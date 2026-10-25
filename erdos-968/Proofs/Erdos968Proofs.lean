module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib
public import PrimeNumberTheoremAnd.Consequences
public import Erdos968PrimeGapsC

@[expose] public section

namespace Set

open Filter
open scoped Topology

@[inline]
noncomputable abbrev partialDensity {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    (S : Set α) (A : Set α := Set.univ) (b : α) : ℝ :=
  ((S ∩ A) ∩ Set.Iio b).ncard / (A ∩ Set.Iio b).ncard

noncomputable def lowerDensity {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    (S : Set α) (A : Set α := Set.univ) : ℝ :=
  atTop.liminf fun (b : α) ↦ S.partialDensity A b

end Set

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators


/-! ## Prime-ratio comparisons and step classifications -/

open Filter
open scoped BigOperators

namespace Erdos968.AuditPrimeRatios

noncomputable def u (n : ℕ) : ℝ :=
  (n.nth Nat.Prime : ℝ) / (n + 1)

theorem u_pos (n : ℕ) : 0 < u n := by
  unfold u
  exact div_pos (by exact_mod_cast (Nat.prime_nth_prime n).pos) (by positivity)

theorem decrease_iff_cross (n : ℕ) :
    u (n + 1) < u n ↔
      (n + 1) * Nat.nth Nat.Prime (n + 1) < (n + 2) * Nat.nth Nat.Prime n := by
  unfold u
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  simp only [Nat.add_assoc, Nat.mul_comm]

theorem decrease_iff_gap (n : ℕ) :
    u (n + 1) < u n ↔
      (n + 1) * (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n) <
        Nat.nth Nat.Prime n := by
  rw [decrease_iff_cross]
  have hle : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
    (show n ≤ n + 1 by omega)
  have heq := Nat.sub_add_cancel hle
  constructor <;> intro h <;> nlinarith

theorem decrease_iff_real_gap (n : ℕ) :
    u (n + 1) < u n ↔
      (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) < u n := by
  rw [decrease_iff_gap]
  unfold u
  rw [lt_div_iff₀ (by positivity)]
  norm_cast
  simp only [Nat.mul_comm]

theorem consecutive_ne (n : ℕ) : u n ≠ u (n + 1) := by
  intro h
  have heq : (n + 2) * Nat.nth Nat.Prime n =
      (n + 1) * Nat.nth Nat.Prime (n + 1) := by
    unfold u at h
    have hz1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hz2 : ((n + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    have hc := (div_eq_div_iff hz1 hz2).mp h
    norm_cast at hc
    nlinarith [hc]
  have hp := Nat.prime_nth_prime n
  have hq := Nat.prime_nth_prime (n + 1)
  have hdiv : Nat.nth Nat.Prime n ∣ (n + 1) * Nat.nth Nat.Prime (n + 1) := by
    rw [← heq]
    exact dvd_mul_left _ _
  rcases hp.dvd_mul.mp hdiv with hsmall | hnext
  · have hle := Nat.le_of_dvd (show 0 < n + 1 by omega) hsmall
    have := Nat.add_two_le_nth_prime n
    omega
  · have hequal := (Nat.prime_dvd_prime_iff_eq hp hq).mp hnext
    have hlt : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (show n < n + 1 by omega)
    exact (ne_of_lt hlt) hequal

theorem increase_iff_not_decrease (n : ℕ) :
    u n < u (n + 1) ↔ ¬ u (n + 1) < u n := by
  have h := consecutive_ne n
  constructor
  · exact fun hlt => not_lt_of_gt hlt
  · intro hnot
    exact lt_of_le_of_ne (le_of_not_gt hnot) h

theorem finite_count_partition (N : ℕ) :
    letI := Classical.propDecidable
    ((Finset.range N).filter (fun n => u n < u (n + 1))).card +
      ((Finset.range N).filter (fun n => u (n + 1) < u n)).card = N := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range N) (fun n => u (n + 1) < u n)
  simp only [Finset.card_range, ← increase_iff_not_decrease] at h
  omega

theorem finite_density_partition (N : ℕ) (hN : 0 < N) :
    ((({n : ℕ | u n < u (n + 1)} ∩ Set.Iio N).ncard : ℝ) / N) +
      ((({n : ℕ | u (n + 1) < u n} ∩ Set.Iio N).ncard : ℝ) / N) = 1 := by
  classical
  have hi : {n : ℕ | u n < u (n + 1)} ∩ Set.Iio N =
      ↑((Finset.range N).filter (fun n => u n < u (n + 1))) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_range]
    exact and_comm
  have hd : {n : ℕ | u (n + 1) < u n} ∩ Set.Iio N =
      ↑((Finset.range N).filter (fun n => u (n + 1) < u n)) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_range]
    exact and_comm
  rw [hi, hd, Set.ncard_coe_finset, Set.ncard_coe_finset, ← add_div, ← Nat.cast_add]
  rw [finite_count_partition]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hN))

end Erdos968.AuditPrimeRatios


/-! ## Excess mass and prime-gap counts -/

open Finset
open scoped BigOperators

namespace Erdos968.GapTailTransfer

end Erdos968.GapTailTransfer


/-! ## Prime-height density transfer -/

open Filter
open scoped BigOperators

namespace Erdos968.DensityTransfer

open Erdos968.AuditPrimeRatios Erdos968.GapTailTransfer

noncomputable def primeHeight (N : ℕ) : ℝ :=
  (Nat.nth Nat.Prime (N - 1) : ℝ)

noncomputable def primeGap (i : ℕ) : ℝ :=
  ((Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i : ℕ) : ℝ)

noncomputable def primeLogRatio (i : ℕ) : ℝ :=
  u i / Real.log (Nat.nth Nat.Prime i : ℝ)

noncomputable def increaseFraction (N : ℕ) : ℝ :=
  (({i : ℕ | u i < u (i + 1)} ∩ Set.Iio N).ncard : ℝ) / N

theorem log_prime_pos (i : ℕ) :
    0 < Real.log (Nat.nth Nat.Prime i : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (Nat.prime_nth_prime i).one_lt

theorem prefix_prime_le_height {i N : ℕ} (hi : i < N) :
    (Nat.nth Nat.Prime i : ℝ) ≤ primeHeight N := by
  unfold primeHeight
  exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
    (show i ≤ N - 1 by omega)

theorem height_tendsto_atTop : Tendsto primeHeight atTop atTop := by
  have hp : Tendsto (fun i : ℕ => (Nat.nth Nat.Prime i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  exact hp.comp (tendsto_sub_atTop_nat 1)

theorem log_height_tendsto_atTop :
    Tendsto (fun N => Real.log (primeHeight N)) atTop atTop :=
  Real.tendsto_log_atTop.comp height_tendsto_atTop

theorem increaseFraction_nonneg (N : ℕ) : 0 ≤ increaseFraction N := by
  unfold increaseFraction
  positivity

theorem prefix_envelope_from_prime_log_ratio
    (lambda : ℝ) (hlambda : 1 < lambda)
    (hpnt : Tendsto primeLogRatio atTop (nhds 1)) :
    ∀ᶠ N : ℕ in atTop, ∀ i < N, u i ≤ lambda * Real.log (primeHeight N) := by
  classical
  have hpos : 0 < lambda := lt_trans zero_lt_one hlambda
  have hratio : ∀ᶠ i : ℕ in atTop, primeLogRatio i < lambda :=
    hpnt.eventually (eventually_lt_nhds hlambda)
  obtain ⟨I, hI⟩ := eventually_atTop.mp hratio
  have hlarge : Tendsto (fun N => lambda * Real.log (primeHeight N)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hpos log_height_tendsto_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop, ∀ i ∈ Finset.range I,
      u i ≤ lambda * Real.log (primeHeight N) := by
    apply (Finset.eventually_all (Finset.range I)).mpr
    intro i hi
    exact hlarge.eventually (eventually_ge_atTop (u i))
  filter_upwards [hsmall] with N hs i hi
  by_cases hilt : i < I
  · exact hs i (Finset.mem_range.mpr hilt)
  · have hr := hI i (by omega)
    have hu : u i < lambda * Real.log (Nat.nth Nat.Prime i : ℝ) :=
      (div_lt_iff₀ (log_prime_pos i)).mp hr
    have hlog : Real.log (Nat.nth Nat.Prime i : ℝ) ≤ Real.log (primeHeight N) :=
      Real.log_le_log (by exact_mod_cast (Nat.prime_nth_prime i).pos)
        (prefix_prime_le_height hi)
    exact hu.le.trans (mul_le_mul_of_nonneg_left hlog hpos.le)

end Erdos968.DensityTransfer


/-! ## Consecutive prime-gap bound -/

namespace Erdos968.CrossingGap

open Erdos968.DensityTransfer

theorem next_prime_le_twice (i : ℕ) :
    Nat.nth Nat.Prime (i + 1) ≤ 2 * Nat.nth Nat.Prime i := by
  let p : ℕ := Nat.nth Nat.Prime i
  have hp : Nat.Prime p := Nat.prime_nth_prime i
  obtain ⟨q, hqprime, hqlo, hqhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul p (Nat.ne_of_gt hp.pos)
  have hnext : Nat.nth Nat.Prime (i + 1) ≤ q := by
    by_contra hnot
    have hlt : q < Nat.nth Nat.Prime (i + 1) := Nat.lt_of_not_ge hnot
    exact (Nat.le_nth_of_lt_nth_succ hlt hqprime).not_gt hqlo
  exact hnext.trans hqhi

theorem prime_gap_le_left_prime (i : ℕ) :
    primeGap i ≤ (Nat.nth Nat.Prime i : ℝ) := by
  unfold primeGap
  exact_mod_cast (show Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i ≤
      Nat.nth Nat.Prime i by
    have := next_prime_le_twice i
    omega)

end Erdos968.CrossingGap


/-! ## Natural-number lower-density formulas -/

open Filter

namespace Erdos968.LocalBridge

theorem partialDensity_nat_eq (S : Set ℕ) (N : ℕ) :
    S.partialDensity Set.univ N =
      ((S ∩ Set.Iio N).ncard : ℝ) / N := by
  simp [Set.partialDensity]

theorem lowerDensity_nat_eq_liminf (S : Set ℕ) :
    S.lowerDensity =
      atTop.liminf (fun N : ℕ => ((S ∩ Set.Iio N).ncard : ℝ) / N) := by
  simp [Set.lowerDensity, partialDensity_nat_eq]

end Erdos968.LocalBridge


/-! ## Prime number theorem asymptotics -/

open Filter Asymptotics
open scoped Topology

namespace Erdos968.PNTReuse

theorem prime_log_ratio_tendsto :
    Tendsto (fun i : ℕ =>
      (((Nat.nth Nat.Prime i : ℝ) / ((i : ℝ) + 1)) /
        Real.log (Nat.nth Nat.Prime i))) atTop (nhds 1) := by
  have hp : Tendsto (fun i : ℕ => (Nat.nth Nat.Prime i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have h : (fun i : ℕ => (Nat.nth Nat.Prime i : ℝ) /
      Real.log (Nat.nth Nat.Prime i)) ~[atTop]
      (fun i : ℕ => (i : ℝ) + 1) := by
    simpa only [Function.comp_def, Nat.floor_natCast, pi_nth_prime,
      Nat.cast_add, Nat.cast_one] using (pi_alt'.comp_tendsto hp).symm
  have hn : ∀ᶠ i : ℕ in atTop, (i : ℝ) + 1 ≠ 0 :=
    Filter.Eventually.of_forall (fun i => ne_of_gt (by positivity))
  have hl := (Asymptotics.isEquivalent_iff_tendsto_one hn).mp h
  change Tendsto (fun i : ℕ => ((Nat.nth Nat.Prime i : ℝ) /
    Real.log (Nat.nth Nat.Prime i)) / ((i : ℝ) + 1)) atTop (nhds 1) at hl
  simpa only [div_div, mul_comm] using hl

end Erdos968.PNTReuse


/-! ## Large prime gaps and local variation bounds -/

namespace Erdos968.LocalScaleAndConvexStepBridge

open Filter Finset
open scoped BigOperators
open Erdos968.AuditPrimeRatios
open Erdos968.DensityTransfer
open Erdos968.CrossingGap
open Erdos968.LocalBridge

theorem u_succ_mul_add_two_eq (n : ℕ) :
    u (n + 1) * ((n : ℝ) + 2) = u n * ((n : ℝ) + 1) + primeGap n := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hle : n.nth Nat.Prime ≤ (n + 1).nth Nat.Prime :=
    le_of_lt (Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n))
  unfold u primeGap
  push_cast [hle]
  field_simp [hn1, hn2]
  ring

theorem u_succ_sub_u_eq_gap_sub_div (n : ℕ) :
    u (n + 1) - u n = (primeGap n - u n) / ((n : ℝ) + 2) := by
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  apply (eq_div_iff hn2.ne').mpr
  have h := u_succ_mul_add_two_eq n
  linarith

theorem u_sub_u_succ_eq_u_sub_gap_div (n : ℕ) :
    u n - u (n + 1) = (u n - primeGap n) / ((n : ℝ) + 2) := by
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  apply (eq_div_iff hn2.ne').mpr
  have h := u_succ_mul_add_two_eq n
  linarith

theorem u_succ_lt_two_mul_u (n : ℕ) :
    u (n + 1) < 2 * u n := by
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hu : 0 < u n := u_pos n
  have hgap : primeGap n ≤ (n.nth Nat.Prime : ℝ) := prime_gap_le_left_prime n
  have hpn : (n.nth Nat.Prime : ℝ) = u n * ((n : ℝ) + 1) := by
    unfold u
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hn1]
  have h := u_succ_mul_add_two_eq n
  have hmul : u (n + 1) * ((n : ℝ) + 2) < (2 * u n) * ((n : ℝ) + 2) := by
    nlinarith
  exact lt_of_mul_lt_mul_right hmul hn2.le

noncomputable def localStrictGapIndices (C : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter
    (fun i => C * Real.log (Nat.nth Nat.Prime i : ℝ) < primeGap i)

theorem oai_prime_succ_eq_nth_prime (i : ℕ) :
    OAI.LargePrimeGaps.prime (i + 1) = Nat.nth Nat.Prime i ∧
      OAI.LargePrimeGaps.prime (i + 1) = Nat.nth Nat.Prime i := by
  exact ⟨rfl, rfl⟩

theorem oai_prime_gap_succ_eq_primeGap (i : ℕ) :
    (OAI.LargePrimeGaps.prime (i + 1 + 1) : ℝ) -
      (OAI.LargePrimeGaps.prime (i + 1) : ℝ) = primeGap i := by
  have hle : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime (i + 1) :=
    le_of_lt (Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self i))
  unfold OAI.LargePrimeGaps.prime primeGap
  simp only [Nat.add_sub_cancel]
  exact (Nat.cast_sub hle).symm

theorem succ_mem_oai_largeGapIndices_iff_mem_localStrictGapIndices
    (C : ℝ) (N i : ℕ) :
    i + 1 ∈ OAI.LargePrimeGaps.largeGapIndices C N ↔
      i ∈ localStrictGapIndices C N := by
  simp only [OAI.LargePrimeGaps.largeGapIndices, localStrictGapIndices,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  rw [oai_prime_gap_succ_eq_primeGap i, (oai_prime_succ_eq_nth_prime i).1]
  exact ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨⟨by omega, by omega⟩, h.2⟩⟩

theorem oai_largeGapIndices_card_eq_localStrictGapIndices_card
    (C : ℝ) (N : ℕ) :
    (OAI.LargePrimeGaps.largeGapIndices C N).card =
      (localStrictGapIndices C N).card := by
  classical
  refine Finset.card_bij (fun n _ => n - 1) ?_ ?_ ?_
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    exact (succ_mem_oai_largeGapIndices_iff_mem_localStrictGapIndices C N (n - 1)).mp
      (by rwa [hsub])
  · intro a ha b hb hab
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    omega
  · intro i hi
    refine ⟨i + 1,
      (succ_mem_oai_largeGapIndices_iff_mem_localStrictGapIndices C N i).mpr hi,
      rfl⟩

theorem unconditional_localStrictGapIndices_linear_lower_bound
    (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ≤ ((localStrictGapIndices C N).card : ℝ) := by
  obtain ⟨c, hc, N₀, hN₀⟩ := OAI.LargePrimeGaps.main C hC
  refine ⟨c, hc, eventually_atTop.mpr ⟨N₀, fun N hN => ?_⟩⟩
  rw [← oai_largeGapIndices_card_eq_localStrictGapIndices_card C N]
  exact hN₀ N hN

theorem eventually_u_le_mul_log_prime (C : ℝ) (hC : 1 < C) :
    ∀ᶠ i : ℕ in atTop, u i ≤ C * Real.log (Nat.nth Nat.Prime i : ℝ) := by
  have hpnt : Tendsto primeLogRatio atTop (nhds 1) :=
    Erdos968.PNTReuse.prime_log_ratio_tendsto
  have hev : ∀ᶠ i : ℕ in atTop, primeLogRatio i < C :=
    hpnt.eventually (Iio_mem_nhds hC)
  filter_upwards [hev] with i hi
  have hlog : 0 < Real.log (Nat.nth Nat.Prime i : ℝ) := log_prime_pos i
  unfold primeLogRatio at hi
  exact (div_lt_iff₀ hlog).mp hi |>.le

end Erdos968.LocalScaleAndConvexStepBridge


open Filter Finset Asymptotics
open scoped BigOperators Topology

namespace Erdos968.DecreasingDensityAndVariation

open Erdos968.AuditPrimeRatios
open Erdos968.DensityTransfer
open Erdos968.LocalBridge
open Erdos968.LocalScaleAndConvexStepBridge

/-!
## Part 1: Step-Excess / Step-Deficit Calculus, Total Variation Doubling Identities,
and Universal Harmonic Upper Bound
-/

noncomputable def stepExcess (n : ℕ) : ℝ :=
  max (primeGap n - u n) 0

noncomputable def stepDeficit (n : ℕ) : ℝ :=
  max (u n - primeGap n) 0

noncomputable def posVariation (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, max (u (n + 1) - u n) 0

noncomputable def negVariation (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, max (u n - u (n + 1)) 0

noncomputable def totVariation (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, |u (n + 1) - u n|

theorem max_u_succ_sub_u_eq_stepExcess_div (n : ℕ) :
    max (u (n + 1) - u n) 0 = stepExcess n / ((n : ℝ) + 2) := by
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [u_succ_sub_u_eq_gap_sub_div n, stepExcess]
  by_cases h : 0 ≤ primeGap n - u n
  · have hdiv : 0 ≤ (primeGap n - u n) / ((n : ℝ) + 2) := div_nonneg h hn2.le
    rw [max_eq_left hdiv, max_eq_left h]
  · push Not at h
    have hdiv : (primeGap n - u n) / ((n : ℝ) + 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h.le hn2.le
    rw [max_eq_right hdiv, max_eq_right h.le, zero_div]

theorem max_u_sub_u_succ_eq_stepDeficit_div (n : ℕ) :
    max (u n - u (n + 1)) 0 = stepDeficit n / ((n : ℝ) + 2) := by
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [u_sub_u_succ_eq_u_sub_gap_div n, stepDeficit]
  by_cases h : 0 ≤ u n - primeGap n
  · have hdiv : 0 ≤ (u n - primeGap n) / ((n : ℝ) + 2) := div_nonneg h hn2.le
    rw [max_eq_left hdiv, max_eq_left h]
  · push Not at h
    have hdiv : (u n - primeGap n) / ((n : ℝ) + 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h.le hn2.le
    rw [max_eq_right hdiv, max_eq_right h.le, zero_div]

theorem posVariation_sub_negVariation_eq_u_sub_u_zero (N : ℕ) :
    posVariation N - negVariation N = u N - u 0 := by
  unfold posVariation negVariation
  rw [← Finset.sum_sub_distrib]
  have hpoint : ∀ n ∈ Finset.range N,
      max (u (n + 1) - u n) 0 - max (u n - u (n + 1)) 0 = u (n + 1) - u n := by
    intro n _
    by_cases h : u n ≤ u (n + 1)
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h), sub_zero]
    · push Not at h
      rw [max_eq_right (sub_nonpos.mpr h.le), max_eq_left (sub_nonneg.mpr h.le)]
      ring
  rw [Finset.sum_congr rfl hpoint]
  exact Finset.sum_range_sub u N

theorem totVariation_eq_posVariation_add_negVariation (N : ℕ) :
    totVariation N = posVariation N + negVariation N := by
  unfold totVariation posVariation negVariation
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : u n ≤ u (n + 1)
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h),
      max_eq_right (sub_nonpos.mpr h), add_zero]
  · push Not at h
    rw [abs_of_neg (sub_neg.mpr h), max_eq_right (sub_nonpos.mpr h.le),
      max_eq_left (sub_nonneg.mpr h.le)]
    ring

theorem totVariation_eq_two_mul_negVariation_add (N : ℕ) :
    totVariation N = 2 * negVariation N + (u N - u 0) := by
  have h1 := totVariation_eq_posVariation_add_negVariation N
  have h2 := posVariation_sub_negVariation_eq_u_sub_u_zero N
  linarith

theorem stepDeficit_lt_u (n : ℕ) :
    stepDeficit n < u n := by
  unfold stepDeficit
  have hu : 0 < u n := u_pos n
  have hgap : 0 < primeGap n := by
    unfold primeGap
    have hlt : n.nth Nat.Prime < (n + 1).nth Nat.Prime :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
    exact_mod_cast Nat.sub_pos_of_lt hlt
  exact max_lt (by linarith) hu

theorem max_u_sub_u_succ_lt_u_div (n : ℕ) :
    max (u n - u (n + 1)) 0 < u n / ((n : ℝ) + 2) := by
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [max_u_sub_u_succ_eq_stepDeficit_div n]
  exact div_lt_div_of_pos_right (stepDeficit_lt_u n) hn2

theorem totVariation_le_u_sub_u_zero_add_two_mul_weighted_u (N : ℕ) :
    totVariation N ≤ u N - u 0 + 2 * ∑ n ∈ Finset.range N, u n / ((n : ℝ) + 2) := by
  have h1 := totVariation_eq_two_mul_negVariation_add N
  have h2 : negVariation N ≤ ∑ n ∈ Finset.range N, u n / ((n : ℝ) + 2) := by
    unfold negVariation
    exact Finset.sum_le_sum fun n _ => (max_u_sub_u_succ_lt_u_div n).le
  linarith

theorem sum_inv_add_two_le_harmonic (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 2) ≤ (harmonic N : ℝ) := by
  have hharm : (harmonic N : ℝ) = ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) := by
    change ((∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℚ))⁻¹ : ℚ) : ℝ) = _
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hharm]
  refine Finset.sum_le_sum fun n _ => ?_
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le hn1 (by linarith)

theorem totVariation_le_of_prefix_envelope (N : ℕ) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ n < N, u n ≤ B) :
    totVariation N ≤ 2 * B * (2 + Real.log (N : ℝ)) := by
  by_cases hN : N = 0
  · subst hN
    simp [totVariation]
    positivity
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have huN : u N ≤ 2 * B := by
      have hpred : N - 1 < N := Nat.sub_lt hNpos zero_lt_one
      have hlt : u N < 2 * u (N - 1) := by
        have hs : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
        simpa [hs] using u_succ_lt_two_mul_u (N - 1)
      have hle : u (N - 1) ≤ B := hB (N - 1) hpred
      linarith
    have hu0 : 0 < u 0 := u_pos 0
    have hsum : ∑ n ∈ Finset.range N, u n / ((n : ℝ) + 2) ≤
        B * (1 + Real.log (N : ℝ)) := by
      calc
        ∑ n ∈ Finset.range N, u n / ((n : ℝ) + 2) ≤
            ∑ n ∈ Finset.range N, B * ((1 : ℝ) / ((n : ℝ) + 2)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
          rw [← mul_one_div]
          exact mul_le_mul_of_nonneg_right (hB n (Finset.mem_range.mp hn)) (by positivity)
        _ = B * ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 2) := by
          rw [← Finset.mul_sum]
        _ ≤ B * (harmonic N : ℝ) :=
          mul_le_mul_of_nonneg_left (sum_inv_add_two_le_harmonic N) hB0
        _ ≤ B * (1 + Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hB0
    have htot := totVariation_le_u_sub_u_zero_add_two_mul_weighted_u N
    nlinarith

/-!
## Part 2: PNT Logarithm Equivalence, Shifted-Index Ratios, and Unconditional Proof of
`erdos_968.variants.decreasing_steps_pos_lower_density`
-/

noncomputable def decreaseFraction (N : ℕ) : ℝ :=
  (({n : ℕ | u (n + 1) < u n} ∩ Set.Iio N).ncard : ℝ) / N

theorem decreaseFraction_eq_filter (N : ℕ) :
    decreaseFraction N =
      (((Finset.range N).filter (fun i => primeGap i < u i)).card : ℝ) / N := by
  classical
  have hs : {i : ℕ | u (i + 1) < u i} ∩ Set.Iio N =
      ↑((Finset.range N).filter (fun i => primeGap i < u i)) := by
    ext i
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    rw [decrease_iff_real_gap]
    exact and_comm
  unfold decreaseFraction
  rw [hs, Set.ncard_coe_finset]

theorem lowerDensity_decrease_eq_liminf :
    ({n : ℕ | u (n + 1) < u n} : Set ℕ).lowerDensity = atTop.liminf decreaseFraction :=
  lowerDensity_nat_eq_liminf {n : ℕ | u (n + 1) < u n}

theorem log_nth_prime_div_log_tendsto_one :
    Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ))
      atTop (nhds 1) := by
  have h := log_nth_prime_asymp
  rw [Asymptotics.isEquivalent_iff_tendsto_one] at h
  · exact h
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by exact_mod_cast (by omega : n ≠ 1))

theorem u_div_log_tendsto_one :
    Tendsto (fun n : ℕ => u n / Real.log (n : ℝ)) atTop (nhds 1) := by
  have h1 := Erdos968.PNTReuse.prime_log_ratio_tendsto
  have h2 := log_nth_prime_div_log_tendsto_one
  have hmul := h1.mul h2
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n _
  have hlog : Real.log (Nat.nth Nat.Prime n : ℝ) ≠ 0 := (log_prime_pos n).ne'
  unfold u
  field_simp [hlog]

theorem log_nat_div_div_log_tendsto_one (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ => Real.log ((N / k : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (nhds 1) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : ℕ => Real.log (2 * (k : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlogN
  have hlo : Tendsto (fun N : ℕ => 1 - Real.log (2 * (k : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hconst
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (max (2 * k) 2)] with N hN
    have hNk : 2 * k ≤ N := le_trans (le_max_left _ _) hN
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
    have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
    have hdiv_nat : N ≤ (2 * k) * (N / k) := by
      have hmod := Nat.div_add_mod N k
      have hlt : N % k < k := Nat.mod_lt N hk
      have hge1 : 1 ≤ N / k := Nat.div_pos (by omega) hk
      nlinarith
    have hdiv_real : (N : ℝ) / (2 * (k : ℝ)) ≤ ((N / k : ℕ) : ℝ) := by
      rw [div_le_iff₀ h2k_pos]
      have : (N : ℝ) ≤ (2 * (k : ℝ)) * ((N / k : ℕ) : ℝ) := by exact_mod_cast hdiv_nat
      linarith
    have hlog_le : Real.log ((N : ℝ) / (2 * (k : ℝ))) ≤ Real.log ((N / k : ℕ) : ℝ) :=
      Real.log_le_log (div_pos hN_pos h2k_pos) hdiv_real
    rw [Real.log_div hN_pos.ne' h2k_pos.ne'] at hlog_le
    calc
      1 - Real.log (2 * (k : ℝ)) / Real.log (N : ℝ) =
          (Real.log (N : ℝ) - Real.log (2 * (k : ℝ))) / Real.log (N : ℝ) := by
        rw [sub_div, div_self hlog_pos.ne']
      _ ≤ Real.log ((N / k : ℕ) : ℝ) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hlog_le hlog_pos.le
  · filter_upwards [eventually_ge_atTop (max (2 * k) 2)] with N hN
    have hNk : 2 * k ≤ N := le_trans (le_max_left _ _) hN
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    have hge1 : 1 ≤ N / k := Nat.div_pos (by omega) hk
    have hle : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_le_self N k
    have hlog_le : Real.log ((N / k : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hge1) hle
    exact (div_le_one hlog_pos).mpr hlog_le

theorem u_nat_div_div_log_tendsto_one (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ => u (N / k) / Real.log (N : ℝ)) atTop (nhds 1) := by
  have hdiv_atTop : Tendsto (fun N : ℕ => N / k) atTop atTop :=
    Nat.tendsto_div_const_atTop hk.ne'
  have h1 : Tendsto (fun N : ℕ => u (N / k) / Real.log ((N / k : ℕ) : ℝ)) atTop (nhds 1) :=
    u_div_log_tendsto_one.comp hdiv_atTop
  have h2 := log_nat_div_div_log_tendsto_one k hk
  have hmul := h1.mul h2
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop (2 * k)] with N hN
  have hge2 : 2 ≤ N / k := (Nat.le_div_iff_mul_le hk).mpr hN
  have hlog : Real.log ((N / k : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hge2)).ne'
  change (u (N / k) / Real.log ((N / k : ℕ) : ℝ)) *
    (Real.log ((N / k : ℕ) : ℝ) / Real.log (N : ℝ)) = u (N / k) / Real.log (N : ℝ)
  field_simp [hlog]

theorem u_sub_u_nat_div_div_log_tendsto_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ => (u N - u (N / k)) / Real.log (N : ℝ)) atTop (nhds 0) := by
  have h := u_div_log_tendsto_one.sub (u_nat_div_div_log_tendsto_one k hk)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards with N
  ring

theorem eventual_posVariation_block_lower :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ b : ℝ, 0 < b ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      b * Real.log (N : ℝ) ≤ posVariation N - posVariation (N / k) := by
  obtain ⟨c₀, hc₀, hgap⟩ := unconditional_localStrictGapIndices_linear_lower_bound 3 (by norm_num)
  let c : ℝ := min c₀ (1 / 2)
  have hc_pos : 0 < c := lt_min hc₀ (by norm_num)
  obtain ⟨k, hk_gt⟩ := exists_nat_gt (max (2 / c) 2)
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk_gt
    exact_mod_cast this.le
  have hk_pos : 0 < k := by omega
  have hkc : 2 / c < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk_gt
  have h1k_le : (1 : ℝ) / (k : ℝ) ≤ c / 2 := by
    have hk_pos_real : (0 : ℝ) < (k : ℝ) := by positivity
    rw [div_le_div_iff₀ hk_pos_real (by norm_num)]
    have := (div_lt_iff₀ hc_pos).mp hkc
    linarith
  obtain ⟨i₁, hi₁⟩ := eventually_atTop.mp (eventually_u_le_mul_log_prime 2 one_lt_two)
  have hlog_p : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) < Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ) :=
    log_nth_prime_div_log_tendsto_one.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨i₂, hi₂⟩ := eventually_atTop.mp hlog_p
  have hlog_div : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) < Real.log ((N / k : ℕ) : ℝ) / Real.log (N : ℝ) :=
    (log_nat_div_div_log_tendsto_one k hk_pos).eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hlog_div
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hgap
  let i₀ : ℕ := max i₁ (max i₂ 2)
  let N₀ : ℕ := max (max N₁ N₂) (max (k * i₀) (2 * k))
  refine ⟨k, hk2, c / 16, by positivity, N₀, fun N hN => ?_⟩
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNN₂ : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNki₀ : k * i₀ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN2k : 2 * k ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hN2 : 2 ≤ N := by omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  let M : ℕ := N / k
  have hMN : M ≤ N := Nat.div_le_self N k
  have hi₀M : i₀ ≤ M := by
    rw [Nat.le_div_iff_mul_le hk_pos]
    simpa [mul_comm] using hNki₀
  have hM2 : 2 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hi₀M
  have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM2)
  have hlogM_ge : (1 / 2 : ℝ) * Real.log (N : ℝ) ≤ Real.log (M : ℝ) :=
    ((lt_div_iff₀ hlogN_pos).mp (hN₁ N hNN₁)).le
  have hlog_pM_ge : (1 / 2 : ℝ) * Real.log (M : ℝ) ≤ Real.log (Nat.nth Nat.Prime M : ℝ) := by
    have hi₂M : i₂ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hi₀M
    exact ((lt_div_iff₀ hlogM_pos).mp (hi₂ M hi₂M)).le
  classical
  let L : Finset ℕ := (Finset.Ico M N).filter
    (fun i => 3 * Real.log (Nat.nth Nat.Prime i : ℝ) < primeGap i)
  have hsub_union : localStrictGapIndices 3 N ⊆ L ∪ Finset.range M := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiN, hgi⟩
    by_cases hiM : M ≤ i
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hiM, Finset.mem_range.mp hiN⟩, hgi⟩)
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by omega))
  have hcard_nat : (localStrictGapIndices 3 N).card ≤ L.card + M := by
    calc
      (localStrictGapIndices 3 N).card ≤ (L ∪ Finset.range M).card :=
        Finset.card_le_card hsub_union
      _ ≤ L.card + (Finset.range M).card := Finset.card_union_le _ _
      _ = L.card + M := by rw [Finset.card_range]
  have hcard_real : (c / 2) * (N : ℝ) ≤ (L.card : ℝ) := by
    have hcN : c * (N : ℝ) ≤ ((localStrictGapIndices 3 N).card : ℝ) := by
      have hc_le : c ≤ c₀ := min_le_left _ _
      exact (mul_le_mul_of_nonneg_right hc_le hN_pos.le).trans (hN₂ N hNN₂)
    have hM_le : (M : ℝ) ≤ (N : ℝ) / (k : ℝ) := by
      have hk_pos_real : (0 : ℝ) < (k : ℝ) := by positivity
      rw [le_div_iff₀ hk_pos_real]
      exact_mod_cast Nat.div_mul_le_self N k
    have hMk : (M : ℝ) ≤ (c / 2) * (N : ℝ) := by
      calc
        (M : ℝ) ≤ (N : ℝ) / (k : ℝ) := hM_le
        _ = ((1 : ℝ) / (k : ℝ)) * (N : ℝ) := by ring
        _ ≤ (c / 2) * (N : ℝ) := mul_le_mul_of_nonneg_right h1k_le hN_pos.le
    have hcast : ((localStrictGapIndices 3 N).card : ℝ) ≤ (L.card : ℝ) + (M : ℝ) := by
      exact_mod_cast hcard_nat
    linarith
  have hpoint : ∀ i ∈ L,
      Real.log (N : ℝ) / (8 * (N : ℝ)) ≤ max (u (i + 1) - u i) 0 := by
    intro i hiL
    rcases Finset.mem_filter.mp hiL with ⟨hiIco, hgi⟩
    rcases Finset.mem_Ico.mp hiIco with ⟨hiM, hiN⟩
    have hi₁i : i₁ ≤ i := le_trans (le_max_left _ _) (le_trans hi₀M hiM)
    have hui : u i ≤ 2 * Real.log (Nat.nth Nat.Prime i : ℝ) := hi₁ i hi₁i
    have hpi_le : (Nat.nth Nat.Prime M : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by
      exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hiM
    have hlog_pi : Real.log (Nat.nth Nat.Prime M : ℝ) ≤ Real.log (Nat.nth Nat.Prime i : ℝ) :=
      Real.log_le_log (by exact_mod_cast (Nat.prime_nth_prime M).pos) hpi_le
    have hex : (1 / 4 : ℝ) * Real.log (N : ℝ) ≤ stepExcess i := by
      unfold stepExcess
      apply le_max_of_le_left
      linarith
    have hi2_pos : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hi2_le : (i : ℝ) + 2 ≤ 2 * (N : ℝ) := by
      have : i + 2 ≤ 2 * N := by omega
      exact_mod_cast this
    rw [max_u_succ_sub_u_eq_stepExcess_div i]
    calc
      Real.log (N : ℝ) / (8 * (N : ℝ)) =
          ((1 / 4 : ℝ) * Real.log (N : ℝ)) / (2 * (N : ℝ)) := by ring
      _ ≤ ((1 / 4 : ℝ) * Real.log (N : ℝ)) / ((i : ℝ) + 2) :=
        div_le_div_of_nonneg_left (by positivity) hi2_pos hi2_le
      _ ≤ stepExcess i / ((i : ℝ) + 2) :=
        div_le_div_of_nonneg_right hex hi2_pos.le
  have hIco : posVariation N - posVariation M =
      ∑ i ∈ Finset.Ico M N, max (u (i + 1) - u i) 0 := by
    unfold posVariation
    exact (Finset.sum_Ico_eq_sub (fun i => max (u (i + 1) - u i) 0) hMN).symm
  rw [hIco]
  have hsub : L ⊆ Finset.Ico M N := Finset.filter_subset _ _
  calc
    (c / 16) * Real.log (N : ℝ) =
        ((c / 2) * (N : ℝ)) * (Real.log (N : ℝ) / (8 * (N : ℝ))) := by
      field_simp [hN_pos.ne']
      ring
    _ ≤ (L.card : ℝ) * (Real.log (N : ℝ) / (8 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard_real (by positivity)
    _ = ∑ _i ∈ L, (Real.log (N : ℝ) / (8 * (N : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ L, max (u (i + 1) - u i) 0 := Finset.sum_le_sum hpoint
    _ ≤ ∑ i ∈ Finset.Ico M N, max (u (i + 1) - u i) 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => le_max_right _ _)

theorem eventual_negVariation_block_lower :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ b : ℝ, 0 < b ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      b * Real.log (N : ℝ) ≤ negVariation N - negVariation (N / k) := by
  obtain ⟨k, hk2, b, hb, N₀, hN₀⟩ := eventual_posVariation_block_lower
  have hk_pos : 0 < k := by omega
  have hdiff : ∀ᶠ N : ℕ in atTop,
      (u N - u (N / k)) / Real.log (N : ℝ) < b / 2 :=
    (u_sub_u_nat_div_div_log_tendsto_zero k hk_pos).eventually (Iio_mem_nhds (half_pos hb))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hdiff
  refine ⟨k, hk2, b / 2, half_pos hb, max (max N₀ N₁) 2, fun N hN => ?_⟩
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNN₁ : N₁ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hu_diff : u N - u (N / k) ≤ (b / 2) * Real.log (N : ℝ) :=
    ((div_lt_iff₀ hlogN_pos).mp (hN₁ N hNN₁)).le
  have hpos := hN₀ N hNN₀
  have htelN := posVariation_sub_negVariation_eq_u_sub_u_zero N
  have htelM := posVariation_sub_negVariation_eq_u_sub_u_zero (N / k)
  linarith

theorem eventual_linear_decreasing_steps :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      δ * (N : ℝ) ≤ (((Finset.range N).filter (fun i => primeGap i < u i)).card : ℝ) := by
  obtain ⟨k, hk2, b, hb, N₀, hN₀⟩ := eventual_negVariation_block_lower
  have hk_pos : 0 < k := by omega
  have hu_le : ∀ᶠ n : ℕ in atTop, u n / Real.log (n : ℝ) < 2 :=
    u_div_log_tendsto_one.eventually (Iio_mem_nhds one_lt_two)
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp hu_le
  let M₀ : ℕ := max N₀ (max (k * max i₀ 2) (2 * k))
  refine ⟨b / (4 * (k : ℝ)), by positivity, eventually_atTop.mpr ⟨M₀, fun N hN => ?_⟩⟩
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNki₀ : k * max i₀ 2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN2k : 2 * k ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hN2 : 2 ≤ N := by omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := by positivity
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  let M : ℕ := N / k
  have hMN : M ≤ N := Nat.div_le_self N k
  have hi₀M : max i₀ 2 ≤ M := by
    rw [Nat.le_div_iff_mul_le hk_pos]
    simpa [mul_comm] using hNki₀
  have hneg := hN₀ N hNN₀
  have hIco : negVariation N - negVariation M =
      ∑ i ∈ Finset.Ico M N, max (u i - u (i + 1)) 0 := by
    unfold negVariation
    exact (Finset.sum_Ico_eq_sub (fun i => max (u i - u (i + 1)) 0) hMN).symm
  classical
  let D_Ico : Finset ℕ := (Finset.Ico M N).filter (fun i => primeGap i < u i)
  let D_N : Finset ℕ := (Finset.range N).filter (fun i => primeGap i < u i)
  have hsum_eq : ∑ i ∈ Finset.Ico M N, max (u i - u (i + 1)) 0 =
      ∑ i ∈ D_Ico, max (u i - u (i + 1)) 0 := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro i _ hne
    contrapose! hne
    rw [max_u_sub_u_succ_eq_stepDeficit_div i, stepDeficit,
      max_eq_right (sub_nonpos.mpr hne), zero_div]
  have hpoint : ∀ i ∈ D_Ico,
      max (u i - u (i + 1)) 0 ≤ (4 * (k : ℝ) * Real.log (N : ℝ)) / (N : ℝ) := by
    intro i hiD
    rcases Finset.mem_filter.mp hiD with ⟨hiIco, _⟩
    rcases Finset.mem_Ico.mp hiIco with ⟨hiM, hiN⟩
    have hi_i₀ : i₀ ≤ i := le_trans (le_max_left _ _) (le_trans hi₀M hiM)
    have hi2 : 2 ≤ i := le_trans (le_max_right _ _) (le_trans hi₀M hiM)
    have hlogi_pos : 0 < Real.log (i : ℝ) := Real.log_pos (by exact_mod_cast hi2)
    have hui : u i ≤ 2 * Real.log (i : ℝ) :=
      ((div_lt_iff₀ hlogi_pos).mp (hi₀ i hi_i₀)).le
    have hlogi_le : Real.log (i : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hiN.le)
    have hui_N : u i ≤ 2 * Real.log (N : ℝ) := by linarith
    have hdiv_nat : N ≤ (2 * k) * (i + 2) := by
      have hmod := Nat.div_add_mod N k
      have hlt : N % k < k := Nat.mod_lt N hk_pos
      have hiM' : N / k ≤ i := hiM
      nlinarith
    have hdiv_real : (N : ℝ) / (2 * (k : ℝ)) ≤ (i : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (N : ℝ) ≤ (2 * (k : ℝ)) * ((i : ℝ) + 2) := by exact_mod_cast hdiv_nat
      linarith
    calc
      max (u i - u (i + 1)) 0 ≤ u i / ((i : ℝ) + 2) := (max_u_sub_u_succ_lt_u_div i).le
      _ ≤ (2 * Real.log (N : ℝ)) / ((i : ℝ) + 2) :=
        div_le_div_of_nonneg_right hui_N (by positivity)
      _ ≤ (2 * Real.log (N : ℝ)) / ((N : ℝ) / (2 * (k : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdiv_real
      _ = (4 * (k : ℝ) * Real.log (N : ℝ)) / (N : ℝ) := by
        field_simp [hN_pos.ne', hk_pos_real.ne']
        ring
  have hcard_le : (D_Ico.card : ℝ) ≤ (D_N.card : ℝ) := by
    have hsub : D_Ico ⊆ D_N := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiIco, hgi⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hiIco).2, hgi⟩
    exact_mod_cast Finset.card_le_card hsub
  have hchain : b * Real.log (N : ℝ) ≤
      (D_N.card : ℝ) * ((4 * (k : ℝ) * Real.log (N : ℝ)) / (N : ℝ)) := by
    calc
      b * Real.log (N : ℝ) ≤ negVariation N - negVariation M := hneg
      _ = ∑ i ∈ Finset.Ico M N, max (u i - u (i + 1)) 0 := hIco
      _ = ∑ i ∈ D_Ico, max (u i - u (i + 1)) 0 := hsum_eq
      _ ≤ ∑ _i ∈ D_Ico, ((4 * (k : ℝ) * Real.log (N : ℝ)) / (N : ℝ)) :=
        Finset.sum_le_sum hpoint
      _ = (D_Ico.card : ℝ) * ((4 * (k : ℝ) * Real.log (N : ℝ)) / (N : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (D_N.card : ℝ) * ((4 * (k : ℝ) * Real.log (N : ℝ)) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard_le (by positivity)
  have hmul : (b * (N : ℝ)) * Real.log (N : ℝ) ≤
      ((D_N.card : ℝ) * (4 * (k : ℝ))) * Real.log (N : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hchain hN_pos.le
    have h2 : (D_N.card : ℝ) * ((4 * (k : ℝ) * Real.log (N : ℝ)) / (N : ℝ)) * (N : ℝ) =
        ((D_N.card : ℝ) * (4 * (k : ℝ))) * Real.log (N : ℝ) := by
      field_simp [hN_pos.ne']
    linarith
  have hle : b * (N : ℝ) ≤ (D_N.card : ℝ) * (4 * (k : ℝ)) :=
    le_of_mul_le_mul_right hmul hlogN_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

theorem erdos_968_decreasing_steps_pos_lower_density :
    0 < {n : ℕ | u n > u (n + 1)}.lowerDensity := by
  obtain ⟨δ, hδ, hcount⟩ := eventual_linear_decreasing_steps
  have hbound : ∀ᶠ N : ℕ in atTop, δ ≤ decreaseFraction N := by
    filter_upwards [hcount, eventually_gt_atTop 0] with N hc hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [decreaseFraction_eq_filter N]
    exact (le_div_iff₀ hN_pos).mpr hc
  have hhi : atTop.IsBoundedUnder (· ≤ ·) decreaseFraction := by
    apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hp := finite_density_partition N hN
    have hinc : 0 ≤ increaseFraction N := increaseFraction_nonneg N
    unfold decreaseFraction increaseFraction at *
    linarith
  have hconst : Tendsto (fun _ : ℕ => δ) atTop (nhds δ) := tendsto_const_nhds
  have hle : δ ≤ ({n : ℕ | u n > u (n + 1)} : Set ℕ).lowerDensity := by
    change δ ≤ ({n : ℕ | u (n + 1) < u n} : Set ℕ).lowerDensity
    rw [lowerDensity_decrease_eq_liminf]
    calc
      δ = atTop.liminf (fun _ : ℕ => δ) := hconst.liminf_eq.symm
      _ ≤ atTop.liminf decreaseFraction :=
        liminf_le_liminf hbound hconst.isBoundedUnder_ge hhi.isCobounded_ge
  exact lt_of_lt_of_le hδ hle

/-!
## Part 3: Unconditional Proof of Erdős–Prachar Total Variation Theorem
(`erdos_968.variants.sum_abs_diff_isTheta_log_sq`)
-/

theorem totVariation_mono : Monotone totVariation := by
  intro m n hmn
  unfold totVariation
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ => abs_nonneg _)

theorem eventual_dyadic_block_totVariation_lower :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ b : ℝ, 0 < b ∧ ∃ N₀ : ℕ, ∀ M ≥ N₀,
      b * Real.log (M : ℝ) ≤ totVariation M - totVariation (M / k) := by
  obtain ⟨k, hk2, b, hb, N₀, hN₀⟩ := eventual_posVariation_block_lower
  refine ⟨k, hk2, b, hb, N₀, fun M hM => ?_⟩
  have hpos := hN₀ M hM
  have hMN : M / k ≤ M := Nat.div_le_self M k
  have hneg_mono : negVariation (M / k) ≤ negVariation M := by
    unfold negVariation
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
      (fun _ _ _ => le_max_right _ _)
  have htotM := totVariation_eq_posVariation_add_negVariation M
  have htotMk := totVariation_eq_posVariation_add_negVariation (M / k)
  linarith

theorem totVariation_isBigO_log_sq :
    totVariation =O[atTop] (fun N : ℕ => Real.log (N : ℝ) ^ 2) := by
  have hprefix := prefix_envelope_from_prime_log_ratio 2 one_lt_two
    Erdos968.PNTReuse.prime_log_ratio_tendsto
  have hlog_p : ∀ᶠ n : ℕ in atTop,
      Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ) < 2 :=
    log_nth_prime_div_log_tendsto_one.eventually (Iio_mem_nhds one_lt_two)
  rw [Asymptotics.isBigO_iff]
  refine ⟨24, ?_⟩
  filter_upwards [hprefix, (tendsto_sub_atTop_nat 1).eventually hlog_p,
      eventually_ge_atTop 3] with N hp hlp hN3
  have hN1 : 2 ≤ N - 1 := by omega
  have hN_pos : 0 < N := by omega
  have hlogN1_pos : 0 < Real.log ((N - 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hlogN_ge1 : 1 ≤ Real.log (N : ℝ) := by
    have hle : Real.exp 1 ≤ (N : ℝ) := by
      have hlt3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have h3N : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
      linarith
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hle
  have hlog_height : Real.log (primeHeight N) ≤ 2 * Real.log (N : ℝ) := by
    have h1 : Real.log (primeHeight N) ≤ 2 * Real.log ((N - 1 : ℕ) : ℝ) := by
      unfold primeHeight
      exact ((div_lt_iff₀ hlogN1_pos).mp hlp).le
    have h2 : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (Nat.sub_le N 1))
    linarith
  have hB : ∀ n < N, u n ≤ 4 * Real.log (N : ℝ) := by
    intro n hn
    have h1 := hp n hn
    linarith
  have htot := totVariation_le_of_prefix_envelope N (4 * Real.log (N : ℝ))
    (by positivity) hB
  have htot_nonneg : 0 ≤ totVariation N := by
    unfold totVariation
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Real.norm_of_nonneg htot_nonneg, Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith

theorem log_sq_isBigO_totVariation :
    (fun N : ℕ => Real.log (N : ℝ) ^ 2) =O[atTop] totVariation := by
  obtain ⟨k, hk2, b, hb, N₀, hN₀⟩ := eventual_dyadic_block_totVariation_lower
  have hk1 : 1 < k := by omega
  have hk_pos : 0 < k := by omega
  have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk1)
  let j₀ : ℕ := N₀
  let J₀ : ℕ := max (2 * j₀) 4
  rw [Asymptotics.isBigO_iff]
  refine ⟨(64 * Real.log (k : ℝ)) / b, ?_⟩
  filter_upwards [eventually_ge_atTop (k ^ J₀)] with N hN
  have hN_ne : N ≠ 0 := by
    have hpos : 0 < k ^ J₀ := pow_pos hk_pos J₀
    omega
  let J : ℕ := Nat.log k N
  have hJ₀J : J₀ ≤ J := Nat.le_log_of_pow_le hk1 hN
  have hj₀J2 : j₀ ≤ J / 2 := by
    have : 2 * j₀ ≤ J := le_trans (le_max_left _ _) hJ₀J
    omega
  have hJ4 : 4 ≤ J := le_trans (le_max_right _ _) hJ₀J
  have hJ2_le : J / 2 ≤ J := Nat.div_le_self J 2
  have hstep : ∀ j ∈ Finset.Ico (J / 2) J,
      b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ) ≤
        totVariation (k ^ (j + 1)) - totVariation (k ^ j) := by
    intro j hj
    rcases Finset.mem_Ico.mp hj with ⟨hj_lo, _⟩
    have hj₀j : N₀ ≤ k ^ (j + 1) := by
      have h1 : N₀ ≤ j + 1 := by omega
      have h2 : j + 1 ≤ k ^ (j + 1) := le_of_lt (Nat.lt_pow_self hk1)
      omega
    have hdiv : k ^ (j + 1) / k = k ^ j := by
      rw [pow_succ, Nat.mul_div_cancel _ hk_pos]
    have hlow := hN₀ (k ^ (j + 1)) hj₀j
    rw [hdiv] at hlow
    have hlog_pow : Real.log ((k ^ (j + 1) : ℕ) : ℝ) =
        ((j + 1 : ℕ) : ℝ) * Real.log (k : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
    have hj_cast : ((J / 2 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : J / 2 ≤ j + 1)
    have hmul : b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ) ≤
        b * (((j + 1 : ℕ) : ℝ) * Real.log (k : ℝ)) := by
      have h1 : b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ) ≤
          b * Real.log (k : ℝ) * ((j + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hj_cast (mul_pos hb hlogk_pos).le
      linarith
    calc
      b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ) ≤
          b * (((j + 1 : ℕ) : ℝ) * Real.log (k : ℝ)) := hmul
      _ = b * Real.log ((k ^ (j + 1) : ℕ) : ℝ) := by rw [hlog_pow]
      _ ≤ totVariation (k ^ (j + 1)) - totVariation (k ^ j) := hlow
  have htel : ∑ j ∈ Finset.Ico (J / 2) J,
      (totVariation (k ^ (j + 1)) - totVariation (k ^ j)) =
      totVariation (k ^ J) - totVariation (k ^ (J / 2)) := by
    rw [Finset.sum_Ico_eq_sub _ hJ2_le,
      Finset.sum_range_sub (fun j => totVariation (k ^ j)),
      Finset.sum_range_sub (fun j => totVariation (k ^ j))]
    ring
  have hcard : (J / 2 : ℕ) ≤ (Finset.Ico (J / 2) J).card := by
    rw [Nat.card_Ico]
    omega
  have hsum_ge : ((J / 2 : ℕ) : ℝ) * (b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ)) ≤
      totVariation (k ^ J) := by
    have hnonneg : 0 ≤ totVariation (k ^ (J / 2)) := by
      unfold totVariation
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h1 : ((Finset.Ico (J / 2) J).card : ℝ) *
        (b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ)) ≤
        totVariation (k ^ J) - totVariation (k ^ (J / 2)) := by
      rw [← htel, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hstep
    have h2 : ((J / 2 : ℕ) : ℝ) ≤ ((Finset.Ico (J / 2) J).card : ℝ) := by
      exact_mod_cast hcard
    have h3 : ((J / 2 : ℕ) : ℝ) * (b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ)) ≤
        ((Finset.Ico (J / 2) J).card : ℝ) *
          (b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  have hJ_div : (J : ℝ) / 4 ≤ ((J / 2 : ℕ) : ℝ) := by
    have hnat : J ≤ 4 * (J / 2) := by omega
    have hreal : (J : ℝ) ≤ 4 * ((J / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hkJN : totVariation (k ^ J) ≤ totVariation N :=
    totVariation_mono (Nat.pow_log_le_self k hN_ne)
  have hlogN_le : Real.log (N : ℝ) ≤ 2 * (J : ℝ) * Real.log (k : ℝ) := by
    have hlt : N < k ^ (J + 1) := Nat.lt_pow_succ_log_self hk1 N
    have hle : (N : ℝ) ≤ ((k ^ (J + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
    have hlog1 : Real.log (N : ℝ) ≤ Real.log ((k ^ (J + 1) : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hle
    rw [Nat.cast_pow, Real.log_pow] at hlog1
    have hJ1 : ((J + 1 : ℕ) : ℝ) ≤ 2 * (J : ℝ) := by
      have : J + 1 ≤ 2 * J := by omega
      exact_mod_cast this
    nlinarith
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    have : 1 ≤ N := by omega
    exact_mod_cast this)
  have htot_nonneg : 0 ≤ totVariation N := by
    unfold totVariation
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg htot_nonneg]
  have hJ_ge : Real.log (N : ℝ) / (8 * Real.log (k : ℝ)) ≤ ((J / 2 : ℕ) : ℝ) := by
    have : Real.log (N : ℝ) / (8 * Real.log (k : ℝ)) ≤ (J : ℝ) / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact this.trans hJ_div
  have hsq : (Real.log (N : ℝ) / (8 * Real.log (k : ℝ))) ^ 2 * (b * Real.log (k : ℝ)) ≤
      ((J / 2 : ℕ) : ℝ) * (b * Real.log (k : ℝ) * ((J / 2 : ℕ) : ℝ)) := by
    have hpos1 : 0 ≤ Real.log (N : ℝ) / (8 * Real.log (k : ℝ)) := by positivity
    have hsq1 : (Real.log (N : ℝ) / (8 * Real.log (k : ℝ))) ^ 2 ≤
        ((J / 2 : ℕ) : ℝ) ^ 2 := by nlinarith
    have hmul1 := mul_le_mul_of_nonneg_right hsq1 (mul_pos hb hlogk_pos).le
    linarith
  have htot_ge : (Real.log (N : ℝ)) ^ 2 * (b / (64 * Real.log (k : ℝ))) ≤ totVariation N := by
    have hident : (Real.log (N : ℝ)) ^ 2 * (b / (64 * Real.log (k : ℝ))) =
        (Real.log (N : ℝ) / (8 * Real.log (k : ℝ))) ^ 2 * (b * Real.log (k : ℝ)) := by
      field_simp [hlogk_pos.ne']
      ring
    linarith
  have hmul := mul_le_mul_of_nonneg_left htot_ge (show (0 : ℝ) ≤ (64 * Real.log (k : ℝ)) / b by positivity)
  have hcancel : ((64 * Real.log (k : ℝ)) / b) *
      ((Real.log (N : ℝ)) ^ 2 * (b / (64 * Real.log (k : ℝ)))) = (Real.log (N : ℝ)) ^ 2 := by
    field_simp [hb.ne', hlogk_pos.ne']
  linarith

theorem totVariation_isTheta_log_sq :
    totVariation =Θ[atTop] (fun N : ℕ => Real.log (N : ℝ) ^ 2) :=
  Asymptotics.IsBigO.antisymm totVariation_isBigO_log_sq log_sq_isBigO_totVariation

theorem log_primeCountingPrime_sq_isTheta_log_sq :
    (fun x : ℕ => Real.log (Nat.primeCounting' x : ℝ) ^ 2) =Θ[atTop]
      (fun x : ℕ => Real.log (x : ℝ) ^ 2) := by
  apply Asymptotics.IsBigO.antisymm
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop 3] with x hx3
    have hpi_pos : 1 ≤ Nat.primeCounting' x := by
      have hne : Nat.primeCounting' x ≠ 0 :=
        Nat.primeCounting'_eq_zero_iff.not.mpr (by omega)
      omega
    have hpi_le : Nat.primeCounting' x ≤ x := by
      rw [Nat.primeCounting']
      exact Nat.count_le Nat.Prime
    have hlog_nonneg : 0 ≤ Real.log (Nat.primeCounting' x : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpi_pos)
    have hlog_le : Real.log (Nat.primeCounting' x : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by exact_mod_cast hpi_pos) (by exact_mod_cast hpi_le)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith
  · have hlog_p : ∀ᶠ n : ℕ in atTop,
        Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ) < 2 :=
      log_nth_prime_div_log_tendsto_one.eventually (Iio_mem_nhds one_lt_two)
    have hpi_tendsto : Tendsto Nat.primeCounting' atTop atTop :=
      Nat.tendsto_primeCounting'
    rw [Asymptotics.isBigO_iff]
    refine ⟨4, ?_⟩
    filter_upwards [hpi_tendsto.eventually hlog_p,
        hpi_tendsto.eventually (eventually_ge_atTop 2),
        eventually_ge_atTop 2] with x hlp hpi2 hx2
    let N : ℕ := Nat.primeCounting' x
    have hN2 : 2 ≤ N := hpi2
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    have hx_le_pN : x ≤ Nat.nth Nat.Prime N := by
      by_contra hlt
      push Not at hlt
      have hmono : Nat.primeCounting' (Nat.nth Nat.Prime N + 1) ≤ Nat.primeCounting' x :=
        Nat.monotone_primeCounting' hlt
      have hsucc : Nat.primeCounting' (Nat.nth Nat.Prime N + 1) = N + 1 := by
        rw [Nat.primeCounting', Nat.count_succ, if_pos (Nat.prime_nth_prime N),
          ← Nat.primeCounting', Nat.primeCounting'_nth_eq]
      omega
    have hlogx_le : Real.log (x : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have h1 : Real.log (x : ℝ) ≤ Real.log (Nat.nth Nat.Prime N : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hx_le_pN)
      have h2 : Real.log (Nat.nth Nat.Prime N : ℝ) ≤ 2 * Real.log (N : ℝ) :=
        ((div_lt_iff₀ hlogN_pos).mp hlp).le
      linarith
    have hlogx_nonneg : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith

theorem erdos_968_sum_abs_diff_isTheta_log_sq :
    (fun x : ℕ => ∑ n ∈ Finset.Iio (Nat.primeCounting' x), |u (n + 1) - u n|) =Θ[atTop]
      (fun x : ℕ => Real.log (x : ℝ) ^ 2) := by
  have hcomp : (fun x : ℕ => totVariation (Nat.primeCounting' x)) =Θ[atTop]
      (fun x : ℕ => Real.log (Nat.primeCounting' x : ℝ) ^ 2) :=
    totVariation_isTheta_log_sq.comp_tendsto Nat.tendsto_primeCounting'
  have heq : (fun x : ℕ => ∑ n ∈ Finset.Iio (Nat.primeCounting' x), |u (n + 1) - u n|) =
      (fun x : ℕ => totVariation (Nat.primeCounting' x)) := by
    ext x
    simp [totVariation, Nat.Iio_eq_range]
  rw [heq]
  exact hcomp.trans log_primeCountingPrime_sq_isTheta_log_sq

end Erdos968.DecreasingDensityAndVariation
