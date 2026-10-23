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
public import PlbyErdos692

@[expose] public section

/-!
# Divisor-interval densities: periodic counting, the density bridge, and extrema

This module establishes the following results.

1. **Universal Periodic Density Bridge (`hasDensity_periodic`, `isDelta1_delta1`, `isDelta1_unique`):**
   Proves that for all `n, m : ℕ`, `exactlyOneDivisorIn n m` has natural density `delta1 n m : ℝ`
   (`IsDelta₁ n m (delta1 n m : ℝ)`), and that `IsDelta₁ n m δ` uniquely determines `δ`.
2. **Proofs of `erdos_692.parts.i` and `erdos_692.variants.cambie_three`:**
   Combines `isDelta1_delta1` and `isDelta1_unique` with `PlbyErdos692` to prove the exact
   `FormalConjectures` statements `erdos_692_variants_cambie_three_impl` and `erdos_692_parts_i`,
   as well as the `n = 2` non-unimodality witness `not_unimodularOn_delta_two`.
3. **Universal Interval-Step Transitions and Sharp `n^2` Composite Obstruction:**
   - `exactlyOneDivisorIn_succ_eq_diff_of_divisor`, `isDelta1_succ_le_of_divisor`:
     Whenever `m` has a divisor `d₀ ∈ Set.Ioo n m`, `exactlyOneDivisorIn n (m + 1)` removes
     all multiples of `m` from `exactlyOneDivisorIn n m`, forcing `δ n (m + 1) ≤ δ n m`.
   - `exactlyOneDivisorIn_succ_eq_of_two_divisors`, `isDelta1_succ_eq_of_two_divisors`:
     Whenever `m` has two distinct divisors in `Set.Ioo n m`,
     `exactlyOneDivisorIn n (m + 1) = exactlyOneDivisorIn n m` and `δ n (m + 1) = δ n m`.
   - `composite_has_divisor_in_Ioo_of_sq_lt`, `prime_of_strict_step_of_sq_lt`,
     `prime_of_succ_mem_localMaxima_of_sq_lt`, and `no_divisor_in_Ioo_prime_sq`:
     For all `n, m : ℕ` with `4 ≤ m` and `n ^ 2 < m`, every composite `m` has a divisor in
     `Set.Ioo n m`, so `δ n (m + 1) ≤ δ n m` and any strict step or local maximum `m + 1`
     requires `Nat.Prime m`; conversely, for every prime `p`, `m = p ^ 2` is composite with
     no divisor in `Set.Ioo p (p ^ 2)`, showing `n ^ 2 < m` is sharp.
4. **Endpoints of `erdos_692.parts.ii` at `n = 0` and `n = 1`:**
   - `erdos_692_parts_ii_zero` and `unimodularOn_delta_zero`: at `n = 0`, `δ 0` is antitone
     on `Set.Ici 2`, unimodular on `(1, ∞)`, and achieves its unique global maximum `1` at `m = 2`.
   - `isDelta1_one_le_half_of_five_le`, `erdos_692_parts_ii_one_three`, and
     `erdos_692_parts_ii_one_four`: at `n = 1`, the odd-core injection bounds `δ 1 m ≤ 1 / 2`
     for all `m ≥ 5`, so `δ 1` achieves its global maximum `1 / 2` on `(2, ∞)` at `m ∈ {3, 4}`.
-/

section DensityHelper
open Filter
open scoped Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

theorem partialDensity_le_one {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : S.partialDensity A b ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ inter_subset_right

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

namespace HasDensity

@[simp]
theorem empty {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] (A : Set β := Set.univ) :
    Set.HasDensity (∅ : Set β) 0 A := by
  simpa [HasDensity, partialDensity] using tendsto_const_nhds

theorem mono {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β]
    {S T : Set β} {αS αT : ℝ} [(atTop (α := β)).NeBot] (h : S ⊆ T) (hS : S.HasDensity αS)
    (hT : T.HasDensity αT) : αS ≤ αT := by
  rw [HasDensity] at hS hT
  apply le_of_tendsto_of_tendsto hS hT
  filter_upwards [eventually_ge_atTop ⊥] with b hb
  apply div_le_div_of_nonneg_right
  grw [Set.ncard_le_ncard (inter_subset_inter_left _ (inter_subset_inter_left _ h))]
  exact Nat.cast_nonneg _

theorem nonneg {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] [(atTop : Filter β).NeBot]
    {S : Set β} {α : ℝ} (h : S.HasDensity α) : 0 ≤ α :=
  le_of_tendsto_of_tendsto' empty h fun b => by simp [div_nonneg, partialDensity]

end HasDensity
end Set

namespace Nat
open Set Filter
open scoped Topology

theorem ncard_multiples_Iio {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ({m : ℕ | k ∣ m} ∩ Iio n).ncard = (n + k - 1) / k := by
  have hkpos : 0 < k := hk
  have : {m : ℕ | k ∣ m} ∩ Iio n = (fun j => j * k) '' Iio ((n + k - 1) / k) := by
    ext m
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Iio, mem_image]
    constructor
    · rintro ⟨⟨j, rfl⟩, hm⟩
      refine ⟨j, ?_, mul_comm _ _⟩
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hkpos]
      rw [mul_comm k j] at hm
      rw [add_mul]
      omega
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨j, mul_comm _ _⟩, ?_⟩
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hkpos, add_mul] at hj
      omega
  rw [this, ncard_image_of_injective _ (mul_left_injective₀ (by omega)), ncard_Iio, Nat.card_Iio]

theorem hasDensity_multiples {k : ℕ} (hk : 1 ≤ k) : {n : ℕ | k ∣ n}.HasDensity (1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [HasDensity, partialDensity, inter_univ, univ_inter, ncard_Iio, Nat.card_Iio]
  have hlow : ∀ n : ℕ, 1 ≤ n → 1 / (k : ℝ) ≤ (({n : ℕ | k ∣ n} ∩ Iio n).ncard : ℝ) / n := by
    intro n hn
    rw [ncard_multiples_Iio hk hn]
    have h1 : n ≤ k * ((n + k - 1) / k) := by
      have := Nat.lt_mul_div_succ (n + k - 1) (show 0 < k from hk)
      rw [mul_add, mul_one] at this
      omega
    have h2 : (n : ℝ) ≤ k * (((n + k - 1) / k : ℕ) : ℝ) := by exact_mod_cast h1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ hkR hnR]
    linarith
  have hup : ∀ n : ℕ, 1 ≤ n →
      (({n : ℕ | k ∣ n} ∩ Iio n).ncard : ℝ) / n ≤ 1 / (k : ℝ) + 1 / n := by
    intro n hn
    rw [ncard_multiples_Iio hk hn]
    have h1 : k * ((n + k - 1) / k) ≤ n + k - 1 := Nat.mul_div_le _ _
    have h2 : (k : ℝ) * (((n + k - 1) / k : ℕ) : ℝ) ≤ n + k := by
      have : k * ((n + k - 1) / k) ≤ n + k := by omega
      exact_mod_cast this
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_add_div _ _ hkR.ne' hnR.ne', div_le_div_iff₀ hnR (by positivity)]
    nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (eventually_atTop.2 ⟨1, hlow⟩) (eventually_atTop.2 ⟨1, hup⟩)
  simpa using Tendsto.const_add (1 / (k : ℝ)) tendsto_one_div_atTop_nhds_zero_nat
end Nat

end DensityHelper

def UnimodularOn {α β : Type*} [Preorder α] [Preorder β] (f : α → β) (a : α) : Prop :=
  ∃ m > a, MonotoneOn f (Set.Ioc a m) ∧ AntitoneOn f (Set.Ici m)

namespace Erdos692
def exactlyOneDivisorIn (n m : ℕ) : Set ℕ :=
  {x | {d ∈ Set.Ioo n m | d ∣ x}.ncard = 1}

def IsDelta₁ (n m : ℕ) (δ : ℝ) : Prop :=
  (exactlyOneDivisorIn n m).HasDensity δ

def localMaxima (f : ℕ → ℝ) (a : ℕ) : Set ℕ :=
  {m | a < m ∧ f (m - 1) < f m ∧ ∃ b, m ≤ b ∧ (∀ j ∈ Set.Icc m b, f j = f m) ∧ f (b + 1) < f m}
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

open Filter Finset Topology


/-! ## Section 1: Universal Set Equivalence and Periodic Natural Density Bridge -/

/-- Membership in `exactlyOneDivisorIn n m` is equivalent to `numDivisorsIn x n m = 1`. -/
theorem mem_exactlyOneDivisorIn_iff (x n m : ℕ) :
    x ∈ exactlyOneDivisorIn n m ↔ numDivisorsIn x n m = 1 := by
  simp only [exactlyOneDivisorIn, Set.mem_setOf_eq, numDivisorsIn]
  have hset : {d ∈ Set.Ioo n m | d ∣ x} = ↑((Finset.Ioo n m).filter (· ∣ x)) := by
    ext d
    simp [Set.mem_Ioo, Finset.mem_Ioo]
  rw [hset, Set.ncard_coe_finset]

/-- Membership in `exactlyOneDivisorIn n m` is equivalent to having a unique divisor in `(n, m)`. -/
theorem mem_exactlyOneDivisorIn_iff_exists_unique (x n m : ℕ) :
    x ∈ exactlyOneDivisorIn n m ↔ ∃ d, {e ∈ Set.Ioo n m | e ∣ x} = {d} := by
  simp only [exactlyOneDivisorIn, Set.mem_setOf_eq, Set.ncard_eq_one]

/-- The least common multiple of all integers in `(n, m)` is strictly positive for all `n, m`. -/
theorem lcm_Ioo_pos (n m : ℕ) : 0 < (Finset.Ioo n m).lcm id := by
  by_contra h
  have h0 : (Finset.Ioo n m).lcm id = 0 := Nat.eq_zero_of_not_pos h
  rw [Finset.lcm_eq_zero_iff] at h0
  rcases h0 with ⟨d, hd, hd0⟩
  simp only [Finset.mem_Ioo, id_eq] at hd hd0
  omega

/-- Periodicity of a predicate `P` under `+ L` extends to `+ q * L` for all `q : ℕ`. -/
theorem periodic_add_mul {P : ℕ → Prop} {L : ℕ} (hper : ∀ x, P (x + L) ↔ P x) (q x : ℕ) :
    P (q * L + x) ↔ P x := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : (q + 1) * L + x = (q * L + x) + L := by ring
    rw [h1, hper, ih]

/-- Exact block-counting identity on `Finset.range (q * L)` for any `L`-periodic predicate `P`. -/
theorem card_filter_range_mul_period {P : ℕ → Prop} [DecidablePred P] {L : ℕ}
    (hper : ∀ x, P (x + L) ↔ P x) (q : ℕ) :
    ((Finset.range (q * L)).filter P).card = q * ((Finset.range L).filter P).card := by
  simp only [Finset.card_filter]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [periodic_add_mul hper q x]

/-- For an `L`-periodic predicate `P`, the count on `Icc 1 L` equals the count on `range L`. -/
theorem card_filter_Icc_one_eq_range {P : ℕ → Prop} [DecidablePred P] {L : ℕ}
    (hper : ∀ x, P (x + L) ↔ P x) :
    ((Finset.Icc 1 L).filter P).card = ((Finset.range L).filter P).card := by
  simp only [Finset.card_filter]
  have hIcc : Finset.Icc 1 L = (Finset.range L).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro hx
      exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hIcc, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have h1 := Finset.sum_range_succ (fun x => if P x then 1 else 0) L
  have h2 := Finset.sum_range_succ' (fun x => if P x then 1 else 0) L
  have hL0 : (if P L then 1 else 0) = (if P 0 then 1 else 0) := by
    have := hper 0
    simp at this
    simp [this]
  omega

/-- Bridge from `Set.ncard` on `{x | P x} ∩ Set.Iio n` to `Finset.card` on `(range n).filter P`. -/
theorem ncard_setOf_inter_Iio_eq_card_filter_range (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ({x : ℕ | P x} ∩ Set.Iio n).ncard = ((Finset.range n).filter P).card := by
  have hset : {x : ℕ | P x} ∩ Set.Iio n = ↑((Finset.range n).filter P) := by
    ext x
    simp [Set.mem_Iio, Finset.mem_range]
    tauto
  rw [hset, Set.ncard_coe_finset]

/-- Every `L`-periodic predicate on `ℕ` (with `0 < L`) has natural density equal to the
proportion of satisfying residues in `Finset.Icc 1 L`. -/
theorem hasDensity_periodic {P : ℕ → Prop} [DecidablePred P] {L : ℕ} (hL : 0 < L)
    (hper : ∀ x, P (x + L) ↔ P x) :
    Set.HasDensity {x : ℕ | P x} ((((Finset.Icc 1 L).filter P).card : ℝ) / (L : ℝ)) := by
  set c := ((Finset.Icc 1 L).filter P).card
  have hc_eq : ((Finset.range L).filter P).card = c := (card_filter_Icc_one_eq_range hper).symm
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio,
    Nat.card_Iio]
  have hbounds : ∀ n : ℕ, 1 ≤ n →
      (c : ℝ) / (L : ℝ) - (c : ℝ) / (n : ℝ) ≤ (({x : ℕ | P x} ∩ Set.Iio n).ncard : ℝ) / (n : ℝ) ∧
      (({x : ℕ | P x} ∩ Set.Iio n).ncard : ℝ) / (n : ℝ) ≤ (c : ℝ) / (L : ℝ) + (c : ℝ) / (n : ℝ) := by
    intro n hn
    rw [ncard_setOf_inter_Iio_eq_card_filter_range]
    have hle1 : (n / L) * L ≤ n := Nat.div_mul_le_self n L
    have hle2 : n ≤ (n / L + 1) * L := by
      have := Nat.lt_mul_div_succ n hL
      rw [Nat.mul_comm] at this
      omega
    have hcard1 : (n / L) * c ≤ ((Finset.range n).filter P).card := by
      calc (n / L) * c = ((Finset.range ((n / L) * L)).filter P).card := by
            rw [card_filter_range_mul_period hper, hc_eq]
        _ ≤ ((Finset.range n).filter P).card :=
            Finset.card_le_card (Finset.filter_subset_filter P (Finset.range_mono hle1))
    have hcard2 : ((Finset.range n).filter P).card ≤ (n / L + 1) * c := by
      calc ((Finset.range n).filter P).card
          ≤ ((Finset.range ((n / L + 1) * L)).filter P).card :=
            Finset.card_le_card (Finset.filter_subset_filter P (Finset.range_mono hle2))
        _ = (n / L + 1) * c := by
            rw [card_filter_range_mul_period hper, hc_eq]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hle1R : ((n / L : ℕ) : ℝ) * L ≤ n := by exact_mod_cast hle1
    have hle2R : (n : ℝ) ≤ ((n / L : ℕ) + 1) * L := by exact_mod_cast hle2
    have hcard1R : ((n / L : ℕ) : ℝ) * c ≤ (((Finset.range n).filter P).card : ℝ) := by
      exact_mod_cast hcard1
    have hcard2R : (((Finset.range n).filter P).card : ℝ) ≤ ((n / L : ℕ) + 1) * c := by
      exact_mod_cast hcard2
    have hcR : (0 : ℝ) ≤ c := by positivity
    constructor
    · rw [sub_le_iff_le_add, ← add_div, div_le_div_iff₀ hLR hnR]
      nlinarith
    · rw [← sub_le_iff_le_add, ← sub_div, div_le_div_iff₀ hnR hLR]
      nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
    (eventually_atTop.2 ⟨1, fun n hn => (hbounds n hn).1⟩)
    (eventually_atTop.2 ⟨1, fun n hn => (hbounds n hn).2⟩)
  · simpa using Tendsto.const_sub ((c : ℝ) / (L : ℝ)) (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  · simpa using Tendsto.const_add ((c : ℝ) / (L : ℝ)) (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))

/-- For all `n, m : ℕ`, `exactlyOneDivisorIn n m` has natural density `(delta1 n m : ℝ)`. -/
theorem isDelta1_delta1 (n m : ℕ) : IsDelta₁ n m (delta1 n m : ℝ) := by
  unfold IsDelta₁ delta1 countWithOneDivisor
  have hset : exactlyOneDivisorIn n m = {x : ℕ | numDivisorsIn x n m = 1} := by
    ext x
    exact mem_exactlyOneDivisorIn_iff x n m
  rw [hset]
  push_cast
  exact hasDensity_periodic (lcm_Ioo_pos n m) (fun x => by rw [numDivisorsIn_periodic])

/-- Uniqueness of the natural density `IsDelta₁ n m δ`. -/
theorem isDelta1_unique {n m : ℕ} {δ₁ δ₂ : ℝ} (h₁ : IsDelta₁ n m δ₁) (h₂ : IsDelta₁ n m δ₂) :
    δ₁ = δ₂ :=
  tendsto_nhds_unique h₁ h₂

/-- Any density function `δ` satisfying `∀ a b, IsDelta₁ a b (δ a b)` agrees everywhere
with `(delta1 n m : ℝ)`. -/
theorem delta_eq_delta1 {δ : ℕ → ℕ → ℝ} (hδ : ∀ a b, IsDelta₁ a b (δ a b)) (n m : ℕ) :
    δ n m = (delta1 n m : ℝ) :=
  isDelta1_unique (hδ n m) (isDelta1_delta1 n m)

/-- Every density `IsDelta₁ n m δ` lies in `[0, 1]`. -/
theorem isDelta1_mem_Icc {n m : ℕ} {δ : ℝ} (h : IsDelta₁ n m δ) : δ ∈ Set.Icc 0 1 := by
  refine ⟨Set.HasDensity.nonneg h, ?_⟩
  exact le_of_tendsto' h (fun b => Set.partialDensity_le_one (exactlyOneDivisorIn n m) Set.univ b)

/-- Inclusion of `exactlyOneDivisorIn` sets implies the corresponding inequality of densities. -/
theorem isDelta1_le_of_subset {n₁ m₁ n₂ m₂ : ℕ} {δ₁ δ₂ : ℝ}
    (hsub : exactlyOneDivisorIn n₁ m₁ ⊆ exactlyOneDivisorIn n₂ m₂)
    (h₁ : IsDelta₁ n₁ m₁ δ₁) (h₂ : IsDelta₁ n₂ m₂ δ₂) : δ₁ ≤ δ₂ :=
  Set.HasDensity.mono hsub h₁ h₂

/-! ## Section 2: Proofs of `erdos_692.parts.i`, `cambie_three`, and the `n = 2` Counterexample -/

/-- Proof of `erdos_692.variants.cambie_three` in `FormalConjectures`. -/
theorem erdos_692_variants_cambie_three_impl :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      δ 3 7 < δ 3 6 ∧ δ 3 7 < δ 3 8 := by
  intro δ hδ
  rw [delta_eq_delta1 hδ 3 6, delta_eq_delta1 hδ 3 7, delta_eq_delta1 hδ 3 8]
  exact ⟨by exact_mod_cast delta1_3_7_lt_3_6, by exact_mod_cast delta1_3_7_lt_3_8⟩

/-- Exact evaluation `delta1 2 6 = 13 / 30`. -/
theorem delta1_2_6 : delta1 2 6 = 13 / 30 := by
  have hlcm : (Finset.Ioo 2 6).lcm id = 60 := by decide
  have hcnt : countWithOneDivisor 2 6 60 = 26 := by decide
  norm_num [delta1, hlcm, hcnt]

/-- Exact evaluation `delta1 2 7 = 11 / 30`. -/
theorem delta1_2_7 : delta1 2 7 = 11 / 30 := by
  have hlcm : (Finset.Ioo 2 7).lcm id = 60 := by decide
  have hcnt : countWithOneDivisor 2 7 60 = 22 := by decide
  norm_num [delta1, hlcm, hcnt]

/-- Exact evaluation `delta1 2 8 = 13 / 35`. -/
theorem delta1_2_8 : delta1 2 8 = 13 / 35 := by
  have hlcm : (Finset.Ioo 2 8).lcm id = 420 := by decide
  set_option maxRecDepth 1000 in
  have hcnt : countWithOneDivisor 2 8 420 = 156 := by decide
  norm_num [delta1, hlcm, hcnt]

/-- Cambie's `n = 2` non-unimodality inequalities: `δ 2 7 < δ 2 6 ∧ δ 2 7 < δ 2 8`. -/
theorem cambie_two_lt {δ : ℕ → ℕ → ℝ} (hδ : ∀ a b, IsDelta₁ a b (δ a b)) :
    δ 2 7 < δ 2 6 ∧ δ 2 7 < δ 2 8 := by
  rw [delta_eq_delta1 hδ 2 6, delta_eq_delta1 hδ 2 7, delta_eq_delta1 hδ 2 8,
      delta1_2_6, delta1_2_7, delta1_2_8]
  constructor <;> norm_num

/-- Universal lemma: any sequence `f : ℕ → ℝ` with a strict local valley at `k > a + 1`
(`f k < f (k - 1)` and `f k < f (k + 1)`) fails `UnimodularOn f a`. -/
theorem not_unimodularOn_of_strict_valley {f : ℕ → ℝ} {a k : ℕ}
    (hk : a + 1 < k) (hleft : f k < f (k - 1)) (hright : f k < f (k + 1)) :
    ¬ UnimodularOn f a := by
  rintro ⟨M, hM, hmono, hanti⟩
  by_cases hMk : M ≤ k - 1
  · have hle : f (k + 1) ≤ f k :=
      hanti (show k ∈ Set.Ici M by simp; omega) (show k + 1 ∈ Set.Ici M by simp; omega) (by omega)
    linarith
  · have hle : f (k - 1) ≤ f k :=
      hmono (show k - 1 ∈ Set.Ioc a M by simp; omega)
        (show k ∈ Set.Ioc a M by simp; omega) (by omega)
    linarith

/-- Non-unimodality of `δ 2` on `(3, ∞)`. -/
theorem not_unimodularOn_delta_two {δ : ℕ → ℕ → ℝ} (hδ : ∀ a b, IsDelta₁ a b (δ a b)) :
    ¬ UnimodularOn (δ 2) (2 + 1) := by
  obtain ⟨h1, h2⟩ := cambie_two_lt hδ
  exact not_unimodularOn_of_strict_valley (k := 7) (by decide) h1 h2

/-- Non-unimodality of `δ 3` on `(4, ∞)`. -/
theorem not_unimodularOn_delta_three {δ : ℕ → ℕ → ℝ} (hδ : ∀ a b, IsDelta₁ a b (δ a b)) :
    ¬ UnimodularOn (δ 3) (3 + 1) := by
  obtain ⟨h1, h2⟩ := erdos_692_variants_cambie_three_impl δ hδ
  exact not_unimodularOn_of_strict_valley (k := 7) (by decide) h1 h2

/-- Proof of `erdos_692.parts.i` in `FormalConjectures`. -/
theorem erdos_692_parts_i :
    False ↔ ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) → ∀ n, UnimodularOn (δ n) (n + 1) := by
  simp only [false_iff, not_forall]
  exact ⟨fun a b => (delta1 a b : ℝ), isDelta1_delta1, 3, not_unimodularOn_delta_three isDelta1_delta1⟩

/-! ## Section 3: Universal Degenerate & Singleton Interval Identities -/

/-- When `m ≤ n + 1`, the open interval `(n, m)` is empty so `exactlyOneDivisorIn n m = ∅`. -/
theorem exactlyOneDivisorIn_eq_empty_of_le {n m : ℕ} (h : m ≤ n + 1) :
    exactlyOneDivisorIn n m = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_exactlyOneDivisorIn_iff_exists_unique]
  rintro ⟨d, hd⟩
  have hd_mem : d ∈ ({e ∈ Set.Ioo n m | e ∣ x} : Set ℕ) := by rw [hd]; simp
  rcases hd_mem with ⟨⟨h1, h2⟩, _⟩
  omega

/-- For all `n, m : ℕ` with `m ≤ n + 1`, `IsDelta₁ n m 0` holds. -/
theorem isDelta1_zero_of_le {n m : ℕ} (h : m ≤ n + 1) : IsDelta₁ n m 0 := by
  rw [IsDelta₁, exactlyOneDivisorIn_eq_empty_of_le h]
  exact Set.HasDensity.empty

/-- For all `n : ℕ`, `exactlyOneDivisorIn n (n + 2)` is the set of multiples of `n + 1`. -/
theorem exactlyOneDivisorIn_add_two (n : ℕ) :
    exactlyOneDivisorIn n (n + 2) = {x : ℕ | n + 1 ∣ x} := by
  ext x
  rw [mem_exactlyOneDivisorIn_iff_exists_unique]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨d, hd⟩
    have hd_mem : d ∈ ({e ∈ Set.Ioo n (n + 2) | e ∣ x} : Set ℕ) := by rw [hd]; simp
    rcases hd_mem with ⟨⟨h1, h2⟩, hdvd⟩
    have : d = n + 1 := by omega
    rwa [← this]
  · intro hdvd
    refine ⟨n + 1, ?_⟩
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      omega
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, hdvd⟩

/-- Universal singleton-interval density: `IsDelta₁ n (n + 2) (1 / (n + 1))` for all `n : ℕ`. -/
theorem isDelta1_add_two (n : ℕ) : IsDelta₁ n (n + 2) (1 / ((n + 1 : ℕ) : ℝ)) := by
  rw [IsDelta₁, exactlyOneDivisorIn_add_two]
  exact Nat.hasDensity_multiples (by omega)

/-! ## Section 4: Universal Interval-Step Transitions and Sharp `n^2` Composite Obstruction -/

/-- If `¬ (m ∣ x)`, the divisor set of `x` in `(n, m + 1)` equals that in `(n, m)`. -/
theorem divisorSet_eq_of_not_dvd {n m x : ℕ} (hnot : ¬ (m ∣ x)) :
    {e ∈ Set.Ioo n (m + 1) | e ∣ x} = {e ∈ Set.Ioo n m | e ∣ x} := by
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨hne, hem⟩, he_dvd⟩
    refine ⟨⟨hne, ?_⟩, he_dvd⟩
    by_contra hge
    have hem_eq : e = m := by omega
    subst hem_eq
    exact hnot he_dvd
  · rintro ⟨⟨hne, hem⟩, he_dvd⟩
    exact ⟨⟨hne, by omega⟩, he_dvd⟩

/-- If `m` has a divisor `d₀ ∈ Set.Ioo n m`, then no multiple of `m` can belong to
`exactlyOneDivisorIn n (m + 1)`. -/
theorem not_mem_exactlyOneDivisorIn_succ_of_divisor {n m d₀ x : ℕ}
    (hd₀ : d₀ ∈ Set.Ioo n m) (hdvd_m : d₀ ∣ m) (hm_dvd_x : m ∣ x) :
    x ∉ exactlyOneDivisorIn n (m + 1) := by
  rcases hd₀ with ⟨hn_lt, hd₀_lt⟩
  rw [mem_exactlyOneDivisorIn_iff_exists_unique]
  rintro ⟨d, hd⟩
  have hd₀_mem : d₀ ∈ ({e ∈ Set.Ioo n (m + 1) | e ∣ x} : Set ℕ) :=
    ⟨⟨hn_lt, by omega⟩, dvd_trans hdvd_m hm_dvd_x⟩
  have hm_mem : m ∈ ({e ∈ Set.Ioo n (m + 1) | e ∣ x} : Set ℕ) :=
    ⟨⟨by omega, by omega⟩, hm_dvd_x⟩
  rw [hd] at hd₀_mem hm_mem
  simp only [Set.mem_singleton_iff] at hd₀_mem hm_mem
  omega

/-- Universal step-difference identity: whenever `m` has a divisor `d₀ ∈ Set.Ioo n m`,
`exactlyOneDivisorIn n (m + 1) = exactlyOneDivisorIn n m \ {x | m ∣ x}`. -/
theorem exactlyOneDivisorIn_succ_eq_diff_of_divisor {n m d₀ : ℕ}
    (hd₀ : d₀ ∈ Set.Ioo n m) (hdvd_m : d₀ ∣ m) :
    exactlyOneDivisorIn n (m + 1) = exactlyOneDivisorIn n m \ {x : ℕ | m ∣ x} := by
  ext x
  simp only [Set.mem_diff, Set.mem_setOf_eq]
  by_cases hm : m ∣ x
  · simp only [hm, not_true_eq_false, and_false, iff_false]
    exact not_mem_exactlyOneDivisorIn_succ_of_divisor hd₀ hdvd_m hm
  · simp only [hm, not_false_eq_true, and_true]
    simp only [exactlyOneDivisorIn, Set.mem_setOf_eq, divisorSet_eq_of_not_dvd hm]

/-- Universal subset monotonicity: whenever `m` has a divisor `d₀ ∈ Set.Ioo n m`,
`exactlyOneDivisorIn n (m + 1) ⊆ exactlyOneDivisorIn n m`. -/
theorem exactlyOneDivisorIn_succ_subset_of_divisor {n m d₀ : ℕ}
    (hd₀ : d₀ ∈ Set.Ioo n m) (hdvd_m : d₀ ∣ m) :
    exactlyOneDivisorIn n (m + 1) ⊆ exactlyOneDivisorIn n m := by
  rw [exactlyOneDivisorIn_succ_eq_diff_of_divisor hd₀ hdvd_m]
  exact Set.diff_subset

/-- Universal density drop: whenever `m` has a divisor `d₀ ∈ Set.Ioo n m`,
`δ n (m + 1) ≤ δ n m`. -/
theorem isDelta1_succ_le_of_divisor {n m d₀ : ℕ} {δ₁ δ₂ : ℝ}
    (hd₀ : d₀ ∈ Set.Ioo n m) (hdvd_m : d₀ ∣ m)
    (h₁ : IsDelta₁ n m δ₁) (h₂ : IsDelta₁ n (m + 1) δ₂) : δ₂ ≤ δ₁ :=
  isDelta1_le_of_subset (exactlyOneDivisorIn_succ_subset_of_divisor hd₀ hdvd_m) h₂ h₁

/-- Universal composite-invariance theorem: whenever `m` has two distinct divisors
`d₁, d₂ ∈ Set.Ioo n m`, `exactlyOneDivisorIn n (m + 1) = exactlyOneDivisorIn n m`. -/
theorem exactlyOneDivisorIn_succ_eq_of_two_divisors {n m d₁ d₂ : ℕ}
    (hd₁ : d₁ ∈ Set.Ioo n m) (hd₂ : d₂ ∈ Set.Ioo n m) (hne : d₁ ≠ d₂)
    (hdvd₁ : d₁ ∣ m) (hdvd₂ : d₂ ∣ m) :
    exactlyOneDivisorIn n (m + 1) = exactlyOneDivisorIn n m := by
  rw [exactlyOneDivisorIn_succ_eq_diff_of_divisor hd₁ hdvd₁]
  ext x
  simp only [Set.mem_diff, Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro hx hm_dvd_x
  rw [mem_exactlyOneDivisorIn_iff_exists_unique] at hx
  rcases hx with ⟨d, hd⟩
  have h1 : d₁ ∈ ({e ∈ Set.Ioo n m | e ∣ x} : Set ℕ) := ⟨hd₁, dvd_trans hdvd₁ hm_dvd_x⟩
  have h2 : d₂ ∈ ({e ∈ Set.Ioo n m | e ∣ x} : Set ℕ) := ⟨hd₂, dvd_trans hdvd₂ hm_dvd_x⟩
  rw [hd] at h1 h2
  simp only [Set.mem_singleton_iff] at h1 h2
  exact hne (h1.trans h2.symm)

/-- Universal density invariance under adding `m` with two distinct divisors in `Set.Ioo n m`. -/
theorem isDelta1_succ_eq_of_two_divisors {n m d₁ d₂ : ℕ} {δ₁ δ₂ : ℝ}
    (hd₁ : d₁ ∈ Set.Ioo n m) (hd₂ : d₂ ∈ Set.Ioo n m) (hne : d₁ ≠ d₂)
    (hdvd₁ : d₁ ∣ m) (hdvd₂ : d₂ ∣ m)
    (h₁ : IsDelta₁ n m δ₁) (h₂ : IsDelta₁ n (m + 1) δ₂) : δ₁ = δ₂ := by
  rw [IsDelta₁, ← exactlyOneDivisorIn_succ_eq_of_two_divisors hd₁ hd₂ hne hdvd₁ hdvd₂] at h₁
  exact isDelta1_unique h₁ h₂

/-- Necessary condition for `m + 1` to be a local maximum of `δ n`: `m` has no divisor in `(n, m)`. -/
theorem no_divisor_in_Ioo_of_succ_mem_localMaxima {n m : ℕ} {δ : ℕ → ℕ → ℝ}
    (hδ : ∀ a b, IsDelta₁ a b (δ a b))
    (hmax : m + 1 ∈ localMaxima (δ n) (n + 1)) :
    ∀ d ∈ Set.Ioo n m, ¬ (d ∣ m) := by
  intro d hd hdvd
  have hle : δ n (m + 1) ≤ δ n m :=
    isDelta1_succ_le_of_divisor hd hdvd (hδ n m) (hδ n (m + 1))
  have hlt : δ n m < δ n (m + 1) := by
    simpa [localMaxima] using hmax.2.1
  linarith

/-- Every composite integer `m` satisfying `4 ≤ m` and `n ^ 2 < m` has a divisor `q ∈ Set.Ioo n m`. -/
theorem composite_has_divisor_in_Ioo_of_sq_lt {n m : ℕ}
    (hm4 : 4 ≤ m) (hsq : n ^ 2 < m) (hnp : ¬ Nat.Prime m) :
    ∃ q ∈ Set.Ioo n m, q ∣ m := by
  set p := m.minFac
  set q := m / p
  have hm_pos : 0 < m := by omega
  have hm_ne_one : m ≠ 1 := by omega
  have hp_prime : Nat.Prime p := Nat.minFac_prime hm_ne_one
  have hp_ge_two : 2 ≤ p := hp_prime.two_le
  have hp_dvd : p ∣ m := Nat.minFac_dvd m
  have hpq : p * q = m := Nat.mul_div_cancel' hp_dvd
  have hp_sq : p ^ 2 ≤ m := Nat.minFac_sq_le_self hm_pos hnp
  have hp_le_q : p ≤ q := by nlinarith
  have hn_lt_q : n < q := by nlinarith
  have hq_lt_m : q < m := by nlinarith
  refine ⟨q, ⟨hn_lt_q, hq_lt_m⟩, ⟨p, by linarith⟩⟩

/-- For all `n, m : ℕ` with `4 ≤ m` and `n ^ 2 < m`, if `m` is composite then `δ n (m + 1) ≤ δ n m`. -/
theorem delta_succ_le_of_composite_sq_lt {n m : ℕ} {δ : ℕ → ℕ → ℝ}
    (hδ : ∀ a b, IsDelta₁ a b (δ a b))
    (hm4 : 4 ≤ m) (hsq : n ^ 2 < m) (hnp : ¬ Nat.Prime m) :
    δ n (m + 1) ≤ δ n m := by
  obtain ⟨q, hq_mem, hq_dvd⟩ := composite_has_divisor_in_Ioo_of_sq_lt hm4 hsq hnp
  exact isDelta1_succ_le_of_divisor hq_mem hq_dvd (hδ n m) (hδ n (m + 1))

/-- For all `n, m : ℕ` with `4 ≤ m` and `n ^ 2 < m`, any strict increase `δ n m < δ n (m + 1)`
forces `m` to be prime. -/
theorem prime_of_strict_step_of_sq_lt {n m : ℕ} {δ : ℕ → ℕ → ℝ}
    (hδ : ∀ a b, IsDelta₁ a b (δ a b))
    (hm4 : 4 ≤ m) (hsq : n ^ 2 < m) (hlt : δ n m < δ n (m + 1)) :
    Nat.Prime m := by
  by_contra hnp
  have hle := delta_succ_le_of_composite_sq_lt hδ hm4 hsq hnp
  linarith

/-- For all `n, m : ℕ` with `4 ≤ m` and `n ^ 2 < m`, if `m + 1 ∈ localMaxima (δ n) (n + 1)`,
then `m` must be prime. -/
theorem prime_of_succ_mem_localMaxima_of_sq_lt {n m : ℕ} {δ : ℕ → ℕ → ℝ}
    (hδ : ∀ a b, IsDelta₁ a b (δ a b))
    (hm4 : 4 ≤ m) (hsq : n ^ 2 < m)
    (hmax : m + 1 ∈ localMaxima (δ n) (n + 1)) :
    Nat.Prime m := by
  have hlt : δ n m < δ n (m + 1) := by simpa [localMaxima] using hmax.2.1
  exact prime_of_strict_step_of_sq_lt hδ hm4 hsq hlt

/-- Universal negative control (sharpness of `n ^ 2 < m`): for every prime `p`, `p ^ 2` is
composite (`¬ Nat.Prime (p ^ 2)`) yet has no divisor in `Set.Ioo p (p ^ 2)`. -/
theorem no_divisor_in_Ioo_prime_sq {p : ℕ} (hp : Nat.Prime p) :
    ¬ Nat.Prime (p ^ 2) ∧ ∀ d ∈ Set.Ioo p (p ^ 2), ¬ (d ∣ p ^ 2) := by
  refine ⟨by rw [sq]; exact Nat.not_prime_mul hp.ne_one hp.ne_one, ?_⟩
  intro d ⟨hgt, hlt⟩ hdvd
  rw [Nat.dvd_prime_pow hp] at hdvd
  rcases hdvd with ⟨i, hi_le, rfl⟩
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases i
  · simp at hgt
    omega
  · simp at hgt
  · simp at hlt

/-! ## Section 5: Endpoints of `erdos_692.parts.ii` at `n = 0` and `n = 1` -/

/-- For `m ≥ 2`, `x ∈ exactlyOneDivisorIn 0 m` iff `x` has no divisor in `Set.Ioo 1 m`. -/
theorem mem_exactlyOneDivisorIn_zero_iff {m x : ℕ} (hm : 2 ≤ m) :
    x ∈ exactlyOneDivisorIn 0 m ↔ ∀ d ∈ Set.Ioo 1 m, ¬ (d ∣ x) := by
  rw [mem_exactlyOneDivisorIn_iff_exists_unique]
  constructor
  · rintro ⟨d, hd⟩ e ⟨he1, hem⟩ he_dvd
    have h1_mem : 1 ∈ ({k ∈ Set.Ioo 0 m | k ∣ x} : Set ℕ) := ⟨⟨by omega, by omega⟩, one_dvd x⟩
    have he_mem : e ∈ ({k ∈ Set.Ioo 0 m | k ∣ x} : Set ℕ) := ⟨⟨by omega, hem⟩, he_dvd⟩
    rw [hd] at h1_mem he_mem
    simp only [Set.mem_singleton_iff] at h1_mem he_mem
    omega
  · intro hno
    refine ⟨1, ?_⟩
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨he0, hem⟩, he_dvd⟩
      by_contra hne1
      exact hno e ⟨by omega, hem⟩ he_dvd
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, one_dvd x⟩

/-- Antitonicity of `exactlyOneDivisorIn 0 m` for `2 ≤ m₁ ≤ m₂`. -/
theorem exactlyOneDivisorIn_zero_antitone {m₁ m₂ : ℕ} (hm₁ : 2 ≤ m₁) (hle : m₁ ≤ m₂) :
    exactlyOneDivisorIn 0 m₂ ⊆ exactlyOneDivisorIn 0 m₁ := by
  intro x hx
  rw [mem_exactlyOneDivisorIn_zero_iff (by omega)] at hx
  rw [mem_exactlyOneDivisorIn_zero_iff hm₁]
  intro d ⟨hd1, hdm₁⟩
  exact hx d ⟨hd1, by omega⟩

/-- Antitonicity of `δ 0` on `Set.Ici 2`. -/
theorem antitoneOn_delta_zero {δ : ℕ → ℕ → ℝ} (hδ : ∀ a b, IsDelta₁ a b (δ a b)) :
    AntitoneOn (δ 0) (Set.Ici 2) := by
  intro m₁ hm₁ m₂ hm₂ hle
  exact isDelta1_le_of_subset (exactlyOneDivisorIn_zero_antitone hm₁ hle) (hδ 0 m₂) (hδ 0 m₁)

/-- Positive control for `UnimodularOn`: `δ 0` is unimodular on `(0 + 1, ∞)`. -/
theorem unimodularOn_delta_zero {δ : ℕ → ℕ → ℝ} (hδ : ∀ a b, IsDelta₁ a b (δ a b)) :
    UnimodularOn (δ 0) (0 + 1) := by
  refine ⟨2, by decide, ?_, antitoneOn_delta_zero hδ⟩
  intro x hx y hy hle
  have hx2 : x = 2 := by simp only [Set.mem_Ioc] at hx; omega
  have hy2 : y = 2 := by simp only [Set.mem_Ioc] at hy; omega
  rw [hx2, hy2]

/-- Endpoint of `erdos_692.parts.ii` at `n = 0`: `δ 0` achieves its global
maximum on `Set.Ioi (0 + 1)` at `m = 2` (with value `1`). -/
theorem erdos_692_parts_ii_zero :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      IsGreatest (δ 0 '' Set.Ioi (0 + 1)) (δ 0 2) := by
  intro δ hδ
  refine ⟨⟨2, by simp, rfl⟩, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  exact antitoneOn_delta_zero hδ (show 2 ∈ Set.Ici 2 by simp)
    (show m ∈ Set.Ici 2 by simp only [Set.mem_Ioi] at hm; simp; omega)
    (by simp only [Set.mem_Ioi] at hm; omega)

/-- For `m ≥ 5`, no multiple of `4` lies in `exactlyOneDivisorIn 1 m`. -/
theorem not_dvd_four_of_mem_exactlyOneDivisorIn_one {m x : ℕ} (hm : 5 ≤ m)
    (hx : x ∈ exactlyOneDivisorIn 1 m) : ¬ (4 ∣ x) := by
  rw [mem_exactlyOneDivisorIn_iff_exists_unique] at hx
  rcases hx with ⟨d, hd⟩
  intro h4
  have h2 : 2 ∣ x := dvd_trans (by decide : 2 ∣ 4) h4
  have h2_mem : 2 ∈ ({e ∈ Set.Ioo 1 m | e ∣ x} : Set ℕ) := ⟨⟨by omega, by omega⟩, h2⟩
  have h4_mem : 4 ∈ ({e ∈ Set.Ioo 1 m | e ∣ x} : Set ℕ) := ⟨⟨by omega, by omega⟩, h4⟩
  rw [hd] at h2_mem h4_mem
  simp only [Set.mem_singleton_iff] at h2_mem h4_mem
  omega

/-- For `m ≥ 5`, if an odd integer `u` lies in `exactlyOneDivisorIn 1 m`, then `2 * u` does not. -/
theorem not_two_mul_mem_exactlyOneDivisorIn_one {m u : ℕ} (hm : 5 ≤ m)
    (hu : u ∈ exactlyOneDivisorIn 1 m) (hodd : ¬ (2 ∣ u)) :
    2 * u ∉ exactlyOneDivisorIn 1 m := by
  rw [mem_exactlyOneDivisorIn_iff_exists_unique] at hu ⊢
  rcases hu with ⟨d, hd⟩
  rintro ⟨d', hd'⟩
  have hd_mem : d ∈ ({e ∈ Set.Ioo 1 m | e ∣ u} : Set ℕ) := by rw [hd]; simp
  rcases hd_mem with ⟨hd_Ioo, hd_dvd⟩
  have hd_ne_two : d ≠ 2 := by
    rintro rfl
    exact hodd hd_dvd
  have h2_mem : 2 ∈ ({e ∈ Set.Ioo 1 m | e ∣ 2 * u} : Set ℕ) :=
    ⟨⟨by omega, by omega⟩, dvd_mul_right 2 u⟩
  have hd_mem2 : d ∈ ({e ∈ Set.Ioo 1 m | e ∣ 2 * u} : Set ℕ) :=
    ⟨hd_Ioo, dvd_mul_of_dvd_right hd_dvd 2⟩
  rw [hd'] at h2_mem hd_mem2
  simp only [Set.mem_singleton_iff] at h2_mem hd_mem2
  omega

/-- Odd-core injection map `x ↦ (if 2 ∣ x then x / 2 else x) - 1`. -/
def oddCoreMinusOne (x : ℕ) : ℕ :=
  (if 2 ∣ x then x / 2 else x) - 1

/-- For `m ≥ 5`, `oddCoreMinusOne` maps `exactlyOneDivisorIn 1 m ∩ Set.Iio N` into even
integers below `N`. -/
theorem oddCoreMinusOne_MapsTo {m N : ℕ} (hm : 5 ≤ m) :
    ∀ x ∈ exactlyOneDivisorIn 1 m ∩ Set.Iio N,
      oddCoreMinusOne x ∈ {x : ℕ | 2 ∣ x} ∩ Set.Iio N := by
  rintro x ⟨hx, hxN⟩
  have hnot4 : ¬ (4 ∣ x) := not_dvd_four_of_mem_exactlyOneDivisorIn_one hm hx
  simp only [oddCoreMinusOne, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio] at hxN ⊢
  split_ifs with h2 <;> omega

/-- For `m ≥ 5`, `oddCoreMinusOne` is injective on `exactlyOneDivisorIn 1 m`. -/
theorem oddCoreMinusOne_injOn {m : ℕ} (hm : 5 ≤ m) :
    Set.InjOn oddCoreMinusOne (exactlyOneDivisorIn 1 m) := by
  intro x hx y hy hxy
  have hx4 : ¬ (4 ∣ x) := not_dvd_four_of_mem_exactlyOneDivisorIn_one hm hx
  have hy4 : ¬ (4 ∣ y) := not_dvd_four_of_mem_exactlyOneDivisorIn_one hm hy
  simp only [oddCoreMinusOne] at hxy
  split_ifs at hxy with hx2 hy2
  · omega
  · have hxy_eq : x = 2 * y := by omega
    subst hxy_eq
    exfalso
    exact not_two_mul_mem_exactlyOneDivisorIn_one hm hy hy2 hx
  · have hyx_eq : y = 2 * x := by omega
    subst hyx_eq
    exfalso
    exact not_two_mul_mem_exactlyOneDivisorIn_one hm hx hx2 hy
  · omega

/-- Universal upper bound at `n = 1`: for all `m ≥ 5`, `δ 1 m ≤ 1 / 2`. -/
theorem isDelta1_one_le_half_of_five_le {m : ℕ} {δ : ℝ} (hm : 5 ≤ m) (hδ : IsDelta₁ 1 m δ) :
    δ ≤ 1 / 2 := by
  have hmult : Set.HasDensity {x : ℕ | 2 ∣ x} (1 / (2 : ℝ)) := by
    simpa using Nat.hasDensity_multiples (by decide : 1 ≤ 2)
  rw [IsDelta₁, Set.HasDensity] at hδ
  rw [Set.HasDensity] at hmult
  refine le_of_tendsto_of_tendsto' hδ hmult fun N => ?_
  simp only [Set.partialDensity, Set.inter_univ]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hncard : (exactlyOneDivisorIn 1 m ∩ Set.Iio N).ncard ≤
      ({x : ℕ | 2 ∣ x} ∩ Set.Iio N).ncard :=
    Set.ncard_le_ncard_of_injOn oddCoreMinusOne (oddCoreMinusOne_MapsTo hm)
      ((oddCoreMinusOne_injOn hm).mono Set.inter_subset_left)
      ((Set.finite_Iio N).subset Set.inter_subset_right)
  exact_mod_cast hncard

/-- Exact evaluations `delta1 1 3 = 1 / 2`, `delta1 1 4 = 1 / 2`, and `delta1 1 5 = 1 / 3`. -/
theorem delta1_one_small :
    delta1 1 3 = 1 / 2 ∧ delta1 1 4 = 1 / 2 ∧ delta1 1 5 = 1 / 3 := by
  have hlcm3 : (Finset.Ioo 1 3).lcm id = 2 := by decide
  have hcnt3 : countWithOneDivisor 1 3 2 = 1 := by decide
  have hlcm4 : (Finset.Ioo 1 4).lcm id = 6 := by decide
  have hcnt4 : countWithOneDivisor 1 4 6 = 3 := by decide
  have hlcm5 : (Finset.Ioo 1 5).lcm id = 12 := by decide
  have hcnt5 : countWithOneDivisor 1 5 12 = 4 := by decide
  refine ⟨?_, ?_, ?_⟩
  · norm_num [delta1, hlcm3, hcnt3]
  · norm_num [delta1, hlcm4, hcnt4]
  · norm_num [delta1, hlcm5, hcnt5]

/-- Endpoint of `erdos_692.parts.ii` at `n = 1` (witness `m = 3`):
`δ 1` achieves its global maximum `1 / 2` on `Set.Ioi (1 + 1)` at `m = 3`. -/
theorem erdos_692_parts_ii_one_three :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      IsGreatest (δ 1 '' Set.Ioi (1 + 1)) (δ 1 3) := by
  intro δ hδ
  have h3 : δ 1 3 = 1 / 2 := by
    rw [delta_eq_delta1 hδ 1 3, delta1_one_small.1]
    norm_num
  have h4 : δ 1 4 = 1 / 2 := by
    rw [delta_eq_delta1 hδ 1 4, delta1_one_small.2.1]
    norm_num
  refine ⟨⟨3, by simp, rfl⟩, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  simp only [Set.mem_Ioi] at hm
  rw [h3]
  by_cases hm5 : 5 ≤ m
  · exact isDelta1_one_le_half_of_five_le hm5 (hδ 1 m)
  · interval_cases m <;> linarith

/-- Endpoint of `erdos_692.parts.ii` at `n = 1` (witness `m = 4`):
`δ 1` also achieves its global maximum `1 / 2` on `Set.Ioi (1 + 1)` at `m = 4`. -/
theorem erdos_692_parts_ii_one_four :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      IsGreatest (δ 1 '' Set.Ioi (1 + 1)) (δ 1 4) := by
  intro δ hδ
  have h34 : δ 1 4 = δ 1 3 := by
    rw [delta_eq_delta1 hδ 1 4, delta_eq_delta1 hδ 1 3, delta1_one_small.1, delta1_one_small.2.1]
  rw [h34]
  exact erdos_692_parts_ii_one_three δ hδ

/-- Positive and negative controls for `localMaxima` on the two-point plateau `[3, 4]` at `n = 1`:
`3 ∈ localMaxima (δ 1) (1 + 1)` while `4 ∉ localMaxima (δ 1) (1 + 1)`. -/
theorem localMaxima_delta_one_plateau_controls {δ : ℕ → ℕ → ℝ}
    (hδ : ∀ a b, IsDelta₁ a b (δ a b)) :
    3 ∈ localMaxima (δ 1) (1 + 1) ∧ 4 ∉ localMaxima (δ 1) (1 + 1) := by
  have h2 : δ 1 2 = 0 := isDelta1_unique (hδ 1 2) (isDelta1_zero_of_le (by decide))
  have h3 : δ 1 3 = 1 / 2 := by
    rw [delta_eq_delta1 hδ 1 3, delta1_one_small.1]; norm_num
  have h4 : δ 1 4 = 1 / 2 := by
    rw [delta_eq_delta1 hδ 1 4, delta1_one_small.2.1]; norm_num
  have h5 : δ 1 5 = 1 / 3 := by
    rw [delta_eq_delta1 hδ 1 5, delta1_one_small.2.2]; norm_num
  constructor
  · simp only [localMaxima, Set.mem_setOf_eq]
    refine ⟨by decide, by linarith, 4, by decide, ?_, by linarith⟩
    rintro j ⟨hj1, hj2⟩
    interval_cases j <;> linarith
  · simp only [localMaxima, Set.mem_setOf_eq]
    rintro ⟨_, hlt, _⟩
    linarith

end

end Erdos692
