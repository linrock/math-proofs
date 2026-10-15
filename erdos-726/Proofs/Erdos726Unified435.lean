module

/-
Copyright 2026 The Formal Conjectures Authors.
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

/-! ## Adapted construction: second Mertens theorem from PrimeNumberTheoremAnd

The `Mertens` section below is adapted from `PrimeNumberTheoremAnd/IEANTN/Mertens.lean`
at pinned commit `9ecc1b67cdbc36f4fab3ebeb5d6d25512392a078`, with contributions by
Li Xuanji, Giuseppe Sorge, and PrimeNumberTheoremAnd contributors under Apache-2.0.
-/

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

set_option autoImplicit false
set_option relaxedAutoImplicit false


theorem Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl


namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

namespace Mertens

open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log


lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring



theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩



theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem one_eq_o_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log x) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop

theorem sum_mangoldt_div_eq_log' :
    (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! E₁Λ.bounded using 1

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]


theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

theorem sum_log_prime_div_eq_log' : E₁p =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩

theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! sum_log_prime_div_eq_log' using 1

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top

theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    simp
    ring
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      simp
      ring

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp


noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]

theorem sum_prime_div_eq_log_log' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, hC ⟩ := sum_prime_div_eq_log_log
    use C, 2

theorem sum_prime_div_eq_log_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_prime_div_eq_log_log' using 1


end Mertens

noncomputable section
open scoped BigOperators Topology Asymptotics
open Nat Filter Finset

namespace Erdos726

/-- Primes `p ≤ n` (`{p ∈ range (n + 1) | p.Prime}`). -/
def primeRange (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime)

/-- Primes `p ≤ n` whose least residue `n % p` lies in the upper half `(p / 2, p)`. -/
def upperHalfPrimes (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ))

/-- Upper-half prime reciprocal sum `∑_{p ≤ n, p/2 < n % p} 1 / p` (`Erdos726.erdos_726`). -/
def upperHalfPrimeSum (n : ℕ) : ℝ :=
  ∑ p ∈ upperHalfPrimes n, (1 : ℝ) / (p : ℝ)

/-- Full prime reciprocal sum `∑_{p ≤ n} 1 / p` (`Erdos726.erdos_726.variants.mertens_estimate`). -/
def fullPrimeReciprocalSum (n : ℕ) : ℝ :=
  ∑ p ∈ primeRange n, (1 : ℝ) / (p : ℝ)

/-- Identification of `primeRange n` with `(Finset.Ioc 0 n).filter Nat.Prime`. -/
theorem primeRange_eq_Ioc_filter_prime (n : ℕ) :
    primeRange n = (Finset.Ioc 0 n).filter Nat.Prime := by
  ext p
  simp only [primeRange, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.pos, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

/-- Exact Mertens second-theorem decomposition for `fullPrimeReciprocalSum n`. -/
theorem mertens_sum_range_eq (n : ℕ) :
    fullPrimeReciprocalSum n =
      Real.log (Real.log (n : ℝ)) + Mertens.M + Mertens.E₂p (n : ℝ) := by
  unfold fullPrimeReciprocalSum
  rw [primeRange_eq_Ioc_filter_prime]
  simpa only [Nat.floor_natCast] using Mertens.sum_prime_div_eq (n : ℝ)

/-- Unconditional proof of `Erdos726.erdos_726.variants.mertens_estimate`:
`∑_{p ≤ n} 1 / p ~[atTop] log(log n)`. -/
theorem erdos_726_variants_mertens_estimate :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter (fun p ↦ p.Prime), (1 : ℝ) / ((p : ℕ) : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) := by
  apply Asymptotics.IsLittleO.isEquivalent
  have hE : Filter.Tendsto (fun n : ℕ ↦ Mertens.E₂p (n : ℝ)) atTop (nhds 0) :=
    Filter.Tendsto.comp ((Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound')
      tendsto_natCast_atTop_atTop
  have hnum :
      Filter.Tendsto (fun n : ℕ ↦ Mertens.M + Mertens.E₂p (n : ℝ)) atTop (nhds (Mertens.M + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds hE
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Filter.Tendsto.comp Real.tendsto_log_atTop
      (Filter.Tendsto.comp Real.tendsto_log_atTop tendsto_natCast_atTop_atTop)
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (Real.log (Real.log (n : ℝ)))⁻¹) atTop (nhds 0) :=
    Filter.Tendsto.comp tendsto_inv_atTop_zero hlog
  have hdiv :
      Filter.Tendsto
        (fun n : ℕ ↦ (Mertens.M + Mertens.E₂p (n : ℝ)) / Real.log (Real.log (n : ℝ)))
        atTop (nhds 0) := by
    have hmul := Filter.Tendsto.mul hnum hinv
    rw [add_zero, mul_zero] at hmul
    simpa [div_eq_mul_inv] using hmul
  have hev : ∀ᶠ n : ℕ in atTop, Real.log (Real.log (n : ℝ)) = 0 →
      ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter (fun p ↦ p.Prime), (1 : ℝ) / ((p : ℕ) : ℝ)) -
        (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))) n = 0 := by
    filter_upwards [Filter.Tendsto.eventually_gt_atTop hlog 0] with n hn hzero
    linarith
  rw [Asymptotics.isLittleO_iff_tendsto' hev]
  refine hdiv.congr fun n => ?_
  have hm := mertens_sum_range_eq n
  unfold fullPrimeReciprocalSum primeRange at hm
  dsimp
  rw [hm]
  ring

/-- `upperHalfPrimes n` is a subset of `primeRange n`. -/
theorem upperHalfPrimes_subset_primeRange (n : ℕ) :
    upperHalfPrimes n ⊆ primeRange n := by
  intro p hp
  simp only [upperHalfPrimes, primeRange, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- Nonnegativity of `upperHalfPrimeSum n`. -/
theorem upperHalfPrimeSum_nonneg (n : ℕ) :
    0 ≤ upperHalfPrimeSum n := by
  unfold upperHalfPrimeSum
  apply Finset.sum_nonneg
  intro p _
  positivity

/-- Upper bound `upperHalfPrimeSum n ≤ fullPrimeReciprocalSum n`. -/
theorem upperHalfPrimeSum_le_fullPrimeReciprocalSum (n : ℕ) :
    upperHalfPrimeSum n ≤ fullPrimeReciprocalSum n := by
  unfold upperHalfPrimeSum fullPrimeReciprocalSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (upperHalfPrimes_subset_primeRange n)
  intro p _ _
  positivity

end Erdos726

namespace Erdos726

/-! ## Section 1: Real Half-Interval Predicate and Kummer Digit Carry -/

/-- The real-cast upper-half remainder predicate `(p : ℝ) / 2 < ((n % p : ℕ) : ℝ)` from `erdos_726`. -/
def inUpperHalfReal (n p : ℕ) : Prop :=
  (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)

/-- The bottom-digit base-`p` Kummer carry `(2 * n) / p - 2 * (n / p)` of `choose(2n, n)`. -/
def kummerCarry (n p : ℕ) : ℕ :=
  (2 * n) / p - 2 * (n / p)

/-- Exact equivalence between the real-cast half-interval predicate and `p < 2 * (n % p)`. -/
theorem inUpperHalfReal_iff_lt_two_mul_mod :
    ∀ n p : ℕ, inUpperHalfReal n p ↔ p < 2 * (n % p) := by
  intro n p
  unfold inUpperHalfReal
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  rw [← Nat.cast_two, ← Nat.cast_mul, Nat.cast_lt]
  omega

/-- Purely arithmetic characterization of membership in `upperHalfPrimes n`. -/
theorem mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod :
    ∀ n p : ℕ, p ∈ upperHalfPrimes n ↔ p ≤ n ∧ p.Prime ∧ p < 2 * (n % p) := by
  intro n p
  simp only [upperHalfPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  rw [← inUpperHalfReal_iff_lt_two_mul_mod]
  rfl

/-- The bottom-digit Kummer carry `(2 * n) / p - 2 * (n / p)` is bounded above by `1`. -/
theorem kummerCarry_le_one :
    ∀ n p : ℕ, kummerCarry n p ≤ 1 := by
  intro n p
  unfold kummerCarry
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have hdiv := Nat.div_add_mod n p
    have hlt : n % p < p := Nat.mod_lt n hp
    have h2 : 2 * n = 2 * (n % p) + 2 * (n / p) * p := by linarith
    have hq : (2 * n) / p = (2 * (n % p)) / p + 2 * (n / p) := by
      rw [h2, Nat.add_mul_div_right _ _ hp]
    rw [hq, Nat.add_sub_cancel]
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hp]
    omega

/-- For `0 < p`, the bottom-digit Kummer carry equals `1` if and only if `p ≤ 2 * (n % p)`. -/
theorem kummerCarry_eq_one_iff_le_two_mul_mod :
    ∀ n p : ℕ, 0 < p → (kummerCarry n p = 1 ↔ p ≤ 2 * (n % p)) := by
  intro n p hp
  unfold kummerCarry
  have hdiv := Nat.div_add_mod n p
  have hlt : n % p < p := Nat.mod_lt n hp
  have h2 : 2 * n = 2 * (n % p) + 2 * (n / p) * p := by linarith
  have hq : (2 * n) / p = (2 * (n % p)) / p + 2 * (n / p) := by
    rw [h2, Nat.add_mul_div_right _ _ hp]
  rw [hq, Nat.add_sub_cancel]
  constructor
  · intro h1
    have hpos : 0 < (2 * (n % p)) / p := by rw [h1]; exact Nat.zero_lt_one
    exact (Nat.div_pos_iff.mp hpos).2
  · intro hge
    have hge1 : 1 ≤ (2 * (n % p)) / p := Nat.div_pos hge hp
    have hle1 : (2 * (n % p)) / p ≤ 1 := by
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul hp]
      omega
    exact le_antisymm hle1 hge1

/-- For any odd modulus `p`, `inUpperHalfReal n p` holds iff `kummerCarry n p = 1`. -/
theorem odd_inUpperHalfReal_iff_kummerCarry_eq_one :
    ∀ n p : ℕ, p % 2 = 1 → (inUpperHalfReal n p ↔ kummerCarry n p = 1) := by
  intro n p hodd
  have hp : 0 < p := by omega
  rw [inUpperHalfReal_iff_lt_two_mul_mod, kummerCarry_eq_one_iff_le_two_mul_mod n p hp]
  omega

/-! ## Section 2: Parity, Divisibility, Prime-Power, and Quotient-Window Exclusions -/

/-- The even prime `2` never belongs to `upperHalfPrimes n`. -/
theorem two_not_mem_upperHalfPrimes :
    ∀ n : ℕ, 2 ∉ upperHalfPrimes n := by
  intro n h2
  rw [mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod] at h2
  omega

/-- Every prime in `upperHalfPrimes n` is an odd prime at least `3`. -/
theorem odd_of_mem_upperHalfPrimes :
    ∀ n p : ℕ, p ∈ upperHalfPrimes n → p % 2 = 1 ∧ 3 ≤ p := by
  intro n p hp
  rw [mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod] at hp
  rcases hp with ⟨_, hprime, hlt⟩
  have hge2 : 2 ≤ p := hprime.two_le
  have hne2 : p ≠ 2 := by
    rintro rfl
    omega
  have hodd : p % 2 = 1 := hprime.eq_two_or_odd.resolve_left hne2
  exact ⟨hodd, by omega⟩

/-- No prime dividing `n` belongs to `upperHalfPrimes n`. -/
theorem not_mem_upperHalfPrimes_of_dvd :
    ∀ n p : ℕ, p ∣ n → p ∉ upperHalfPrimes n := by
  intro n p hdvd hmem
  rw [mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod] at hmem
  have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
  omega

/-- If a positive prime power `p ^ k` divides `n`, then `p ∉ upperHalfPrimes n`. -/
theorem not_mem_upperHalfPrimes_of_dvd_prime_pow :
    ∀ n p k : ℕ, 1 ≤ k → p ^ k ∣ n → p ∉ upperHalfPrimes n := by
  intro n p k hk hdvd
  have hp_dvd : p ∣ n := dvd_trans (dvd_pow_self p (by omega : k ≠ 0)) hdvd
  exact not_mem_upperHalfPrimes_of_dvd n p hp_dvd

/-- Harmonic quotient-window characterization: `p/2 < n % p` iff `(2 * (n / p) + 1) * p < 2 * n`. -/
theorem inUpperHalfReal_iff_harmonic_quotient_window :
    ∀ n p : ℕ, inUpperHalfReal n p ↔ (2 * (n / p) + 1) * p < 2 * n := by
  intro n p
  rw [inUpperHalfReal_iff_lt_two_mul_mod]
  have hdiv := Nat.div_add_mod n p
  have hmul : (2 * (n / p) + 1) * p = 2 * (p * (n / p)) + p := by ring
  omega

/-- No prime in the top third `[2n/3, n]` (`2 * n ≤ 3 * p`) belongs to `upperHalfPrimes n`. -/
theorem not_mem_upperHalfPrimes_of_two_mul_le_three_mul :
    ∀ n p : ℕ, 2 * n ≤ 3 * p → p ∉ upperHalfPrimes n := by
  intro n p hbound hmem
  have hple : p ≤ n := (mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod n p).mp hmem |>.1
  have hprime : p.Prime := (mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod n p).mp hmem |>.2.1
  have hwin : (2 * (n / p) + 1) * p < 2 * n := by
    rw [← inUpperHalfReal_iff_harmonic_quotient_window]
    exact (inUpperHalfReal_iff_lt_two_mul_mod n p).mpr
      ((mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod n p).mp hmem).2.2
  have hq : 1 ≤ n / p := Nat.div_pos hple hprime.pos
  have hge : 3 * p ≤ (2 * (n / p) + 1) * p := by nlinarith
  omega

/-- Every prime `p` in the middle harmonic window `n < 2 * p` and `3 * p < 2 * n` belongs to `upperHalfPrimes n`. -/
theorem mem_upperHalfPrimes_of_prime_in_middle_interval :
    ∀ n p : ℕ, p.Prime → n < 2 * p → 3 * p < 2 * n → p ∈ upperHalfPrimes n := by
  intro n p hprime hlow hhigh
  rw [mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod]
  refine ⟨by omega, hprime, ?_⟩
  rw [← inUpperHalfReal_iff_lt_two_mul_mod, inUpperHalfReal_iff_harmonic_quotient_window]
  have hq_lt : n / p < 2 := (Nat.div_lt_iff_lt_mul hprime.pos).mpr (by omega)
  have hq_ge : 1 ≤ n / p := Nat.div_pos (by omega) hprime.pos
  have hq_eq : n / p = 1 := by omega
  rw [hq_eq]
  omega

/-! ## Section 3: Mertens Decomposition into Upper-Half, Lower-Half, and Dividing Primes -/

/-- The complement prime set `p ≤ n` where `n % p` lies in the lower half `[0, p / 2]`. -/
def lowerComplementPrimes (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime ∧ ¬((p : ℝ) / 2 < ((n % p : ℕ) : ℝ)))

/-- The lower-half complement prime reciprocal sum. -/
def lowerComplementPrimeSum (n : ℕ) : ℝ :=
  ∑ p ∈ lowerComplementPrimes n, (1 : ℝ) / (p : ℝ)

/-- The set of odd primes `p ≤ n` with strictly positive lower-half remainder `0 < n % p < p / 2`. -/
def strictLowerOddPrimes (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime ∧ p % 2 = 1 ∧ 0 < n % p ∧ 2 * (n % p) < p)

/-- The set of primes `p ≤ n` dividing `n`. -/
def dividingPrimeRange (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime ∧ p ∣ n)

/-- The reciprocal sum over primes `p ≤ n` dividing `n`. -/
def dividingPrimeReciprocalSum (n : ℕ) : ℝ :=
  ∑ p ∈ dividingPrimeRange n, (1 : ℝ) / (p : ℝ)

/-- Exact partition of `primeRange n` into `upperHalfPrimes n` and `lowerComplementPrimes n`. -/
theorem disjoint_upperHalfPrimes_lowerComplementPrimes :
    ∀ n : ℕ, Disjoint (upperHalfPrimes n) (lowerComplementPrimes n) ∧
      upperHalfPrimes n ∪ lowerComplementPrimes n = primeRange n := by
  intro n
  constructor
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [upperHalfPrimes, lowerComplementPrimes, Finset.mem_filter] at hp1 hp2
    exact hp2.2.2 hp1.2.2
  · ext p
    simp only [upperHalfPrimes, lowerComplementPrimes, primeRange,
      Finset.mem_union, Finset.mem_filter]
    tauto

/-- Additive decomposition of `fullPrimeReciprocalSum n` into upper-half and lower-complement sums. -/
theorem upperHalfPrimeSum_add_lowerComplementPrimeSum :
    ∀ n : ℕ, upperHalfPrimeSum n + lowerComplementPrimeSum n = fullPrimeReciprocalSum n := by
  intro n
  have hpart := disjoint_upperHalfPrimes_lowerComplementPrimes n
  unfold upperHalfPrimeSum lowerComplementPrimeSum fullPrimeReciprocalSum
  rw [← hpart.2, Finset.sum_union hpart.1]

/-- Exact identity expressing `upperHalfPrimeSum n - log(log n) / 2` in terms of the
upper-minus-lower discrepancy and the second Mertens constant/error. -/
theorem upperHalfPrimeSum_sub_half_mertens_eq_half_diff :
    ∀ n : ℕ, upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2 =
      (upperHalfPrimeSum n - lowerComplementPrimeSum n + Mertens.M + Mertens.E₂p (n : ℝ)) / 2 := by
  intro n
  have hsum := upperHalfPrimeSum_add_lowerComplementPrimeSum n
  have hmert := mertens_sum_range_eq n
  linarith

/-- Disjointness of `upperHalfPrimes n` from `strictLowerOddPrimes n` and `dividingPrimeRange n`. -/
theorem disjoint_upperHalfPrimes_strictLowerOddPrimes :
    ∀ n : ℕ, Disjoint (upperHalfPrimes n) (strictLowerOddPrimes n) ∧
      Disjoint (upperHalfPrimes n) (dividingPrimeRange n) := by
  intro n
  constructor
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod] at hp1
    simp only [strictLowerOddPrimes, Finset.mem_filter] at hp2
    omega
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod] at hp1
    simp only [dividingPrimeRange, Finset.mem_filter] at hp2
    have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hp2.2.2
    omega

/-- Inclusion of dividing primes in `lowerComplementPrimes n` and the induced reciprocal-sum bound. -/
theorem dividingPrimeRange_subset_lowerComplementPrimes :
    ∀ n : ℕ, dividingPrimeRange n ⊆ lowerComplementPrimes n ∧
      dividingPrimeReciprocalSum n ≤ lowerComplementPrimeSum n := by
  intro n
  have hsub : dividingPrimeRange n ⊆ lowerComplementPrimes n := by
    intro p hp
    simp only [dividingPrimeRange, lowerComplementPrimes, Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, hp.2.1, ?_⟩
    change ¬inUpperHalfReal n p
    rw [inUpperHalfReal_iff_lt_two_mul_mod]
    have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hp.2.2
    omega
  refine ⟨hsub, ?_⟩
  unfold dividingPrimeReciprocalSum lowerComplementPrimeSum
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro p _ _
  positivity

/-! ## Section 4: Residue-Complement Involution `r ↔ p - r` and Modular Period Reflection -/

/-- For an odd modulus `p` and nonzero residue `0 < r < p`, the complement `p - r` lies in the
upper half iff `r` lies in the strict lower half `2 * r < p`. -/
theorem odd_residue_complement_involution :
    ∀ p r : ℕ, p % 2 = 1 → 0 < r → r < p → (p < 2 * (p - r) ↔ 2 * r < p) := by
  intro p r hodd hpos hlt
  omega

/-- Remainder reflection identity `(M - n) % p = p - n % p` when `p ∣ M`, `¬(p ∣ n)`, and `n ≤ M`. -/
theorem mod_sub_of_dvd_of_not_dvd :
    ∀ M n p : ℕ, n ≤ M → p ∣ M → ¬(p ∣ n) → (M - n) % p = p - n % p := by
  intro M n p hle hdvd hndvd
  have hp_pos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · simp only [zero_dvd_iff] at hdvd
      subst hdvd
      have hn0 : n = 0 := Nat.le_zero.mp hle
      subst hn0
      exact absurd (dvd_zero 0) hndvd
    · exact hpos
  have hrem_pos : 0 < n % p := by
    have hne : n % p ≠ 0 := mt Nat.dvd_of_mod_eq_zero hndvd
    omega
  have hrem_lt : n % p < p := Nat.mod_lt n hp_pos
  rcases hdvd with ⟨k, rfl⟩
  have hdiv := Nat.div_add_mod n p
  have hk_gt : n / p < k := by
    by_contra hnot
    have hge : k ≤ n / p := Nat.le_of_not_lt hnot
    have hmul : p * k ≤ p * (n / p) := Nat.mul_le_mul_left p hge
    omega
  have hdecomp : p * k - n = (p - n % p) + (k - 1 - n / p) * p := by
    have h1 : k = (k - 1 - n / p) + (n / p) + 1 := by omega
    calc p * k - n
      _ = p * ((k - 1 - n / p) + (n / p) + 1) - (p * (n / p) + n % p) := by
        rw [← h1, hdiv]
      _ = (p * (n / p) + n % p) + ((p - n % p) + (k - 1 - n / p) * p) - (p * (n / p) + n % p) := by
        congr 1
        have hsub_add : n % p + (p - n % p) = p := Nat.add_sub_of_le (le_of_lt hrem_lt)
        linarith
      _ = (p - n % p) + (k - 1 - n / p) * p := Nat.add_sub_cancel_left _ _
  rw [hdecomp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- Modular period reflection: for an odd modulus `p ∣ M` with `¬(p ∣ n)` and `n ≤ M`,
`M - n` lies in the upper half mod `p` iff `n` does not lie in the upper half mod `p`. -/
theorem odd_inUpperHalfReal_sub_iff_not_inUpperHalfReal :
    ∀ M n p : ℕ, p % 2 = 1 → n ≤ M → p ∣ M → ¬(p ∣ n) →
      (inUpperHalfReal (M - n) p ↔ ¬inUpperHalfReal n p) := by
  intro M n p hodd hle hdvd hndvd
  have hp_pos : 0 < p := by omega
  have hrem_pos : 0 < n % p := by
    have hne : n % p ≠ 0 := mt Nat.dvd_of_mod_eq_zero hndvd
    omega
  have hrem_lt : n % p < p := Nat.mod_lt n hp_pos
  rw [inUpperHalfReal_iff_lt_two_mul_mod, inUpperHalfReal_iff_lt_two_mul_mod]
  rw [mod_sub_of_dvd_of_not_dvd M n p hle hdvd hndvd]
  rw [odd_residue_complement_involution p (n % p) hodd hrem_pos hrem_lt]
  omega

/-- Periodicity of `inUpperHalfReal` under shifts by any multiple `k * p`. -/
theorem inUpperHalfReal_periodic_of_add_mul :
    ∀ n p k : ℕ, inUpperHalfReal (n + k * p) p ↔ inUpperHalfReal n p := by
  intro n p k
  unfold inUpperHalfReal
  rw [Nat.add_mul_mod_self_right]

/-! ## Section 5: Weighted Indicator, Interval Splitting, and Truncated-Support Bounds -/

/-- The weighted prime-residue indicator `(1 / p) * 1_{n mod p ∈ (p/2, p)}`. -/
def upperHalfIndicator (n p : ℕ) : ℝ :=
  if (p : ℝ) / 2 < ((n % p : ℕ) : ℝ) then (1 : ℝ) / (p : ℝ) else 0

/-- Upper-half primes restricted to a half-open interval `[a, b)`. -/
def upperHalfIntervalPrimes (n a b : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ))

/-- Upper-half prime reciprocal sum restricted to `[a, b)`. -/
def upperHalfIntervalSum (n a b : ℕ) : ℝ :=
  ∑ p ∈ upperHalfIntervalPrimes n a b, (1 : ℝ) / (p : ℝ)

/-- Primes in the unconditional middle harmonic window `(n / 2, 2n / 3)`. -/
def middleHarmonicPrimes (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime ∧ n < 2 * p ∧ 3 * p < 2 * n)

/-- Reciprocal sum over primes in the unconditional middle harmonic window `(n / 2, 2n / 3)`. -/
def middleHarmonicPrimeSum (n : ℕ) : ℝ :=
  ∑ p ∈ middleHarmonicPrimes n, (1 : ℝ) / (p : ℝ)

/-- Rewriting `upperHalfPrimeSum n` as the sum of `upperHalfIndicator n p` over `primeRange n`. -/
theorem upperHalfPrimeSum_eq_sum_primeRange_indicator :
    ∀ n : ℕ, upperHalfPrimeSum n = ∑ p ∈ primeRange n, upperHalfIndicator n p := by
  intro n
  unfold upperHalfPrimeSum upperHalfIndicator primeRange upperHalfPrimes
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  tauto

/-- Interval additivity of `upperHalfIntervalSum` across adjacent blocks `[a, b)` and `[b, c)`. -/
theorem upperHalfIntervalSum_split :
    ∀ n a b c : ℕ, a ≤ b → b ≤ c →
      upperHalfIntervalSum n a b + upperHalfIntervalSum n b c = upperHalfIntervalSum n a c := by
  intro n a b c hab hbc
  unfold upperHalfIntervalSum upperHalfIntervalPrimes
  have hdisj : Disjoint
      ((Finset.Ico a b).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)))
      ((Finset.Ico b c).filter (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ))) := by
    exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive a b c)
  rw [← Finset.sum_union hdisj, ← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico hab hbc]

/-- Support truncation identity: because `[2n/3, n]` contains no upper-half primes,
`upperHalfPrimeSum n` equals the interval sum over `[0, (2 * n + 2) / 3)`. -/
theorem upperHalfPrimeSum_eq_interval_below_two_thirds :
    ∀ n : ℕ, upperHalfPrimeSum n = upperHalfIntervalSum n 0 ((2 * n + 2) / 3) := by
  intro n
  unfold upperHalfPrimeSum upperHalfIntervalSum
  congr 1
  ext p
  constructor
  · intro hp
    have hnot : ¬(2 * n ≤ 3 * p) := fun hle =>
      not_mem_upperHalfPrimes_of_two_mul_le_three_mul n p hle hp
    simp only [upperHalfPrimes, upperHalfIntervalPrimes, Finset.mem_filter,
      Finset.mem_range, Finset.mem_Ico] at hp ⊢
    exact ⟨⟨Nat.zero_le p, by omega⟩, hp.2⟩
  · intro hp
    simp only [upperHalfPrimes, upperHalfIntervalPrimes, Finset.mem_filter,
      Finset.mem_range, Finset.mem_Ico, Nat.lt_succ_iff] at hp ⊢
    have hprime : p.Prime := hp.2.1
    have hp2 : 2 ≤ p := hprime.two_le
    exact ⟨by omega, hp.2⟩

/-- Unconditional lower bound: `middleHarmonicPrimes n ⊆ upperHalfPrimes n` and
`middleHarmonicPrimeSum n ≤ upperHalfPrimeSum n`. -/
theorem middleHarmonicPrimeSum_le_upperHalfPrimeSum :
    ∀ n : ℕ, middleHarmonicPrimes n ⊆ upperHalfPrimes n ∧
      middleHarmonicPrimeSum n ≤ upperHalfPrimeSum n := by
  intro n
  have hsub : middleHarmonicPrimes n ⊆ upperHalfPrimes n := by
    intro p hp
    simp only [middleHarmonicPrimes, Finset.mem_filter] at hp
    exact mem_upperHalfPrimes_of_prime_in_middle_interval n p hp.2.1 hp.2.2.1 hp.2.2.2
  refine ⟨hsub, ?_⟩
  unfold middleHarmonicPrimeSum upperHalfPrimeSum
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro p _ _
  positivity


end Erdos726

namespace Erdos726

/-! ## Section 1: Kummer Carry Weighted Sums and Signed Discrepancy -/

/-- The finite set of odd primes `p ≤ n`. -/
def oddPrimeRange (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ ↦ p.Prime ∧ p % 2 = 1)

/-- The weighted Kummer carry term `kummerCarry(n, p) / p`. -/
def kummerCarryTerm (n p : ℕ) : ℝ :=
  (kummerCarry n p : ℝ) / (p : ℝ)

/-- The signed Kummer carry term `(2 * kummerCarry(n, p) - 1) / p` taking values `±1 / p`. -/
def signedKummerCarryTerm (n p : ℕ) : ℝ :=
  (2 * (kummerCarry n p : ℝ) - 1) / (p : ℝ)

/-- Every bottom-digit Kummer carry `kummerCarry n p` is either `0` or `1`. -/
theorem kummerCarry_eq_zero_or_one :
    ∀ n p : ℕ, kummerCarry n p = 0 ∨ kummerCarry n p = 1 := by
  intro n p
  have hle := kummerCarry_le_one n p
  omega

/-- For an odd modulus `p`, `kummerCarry n p = 0` iff `n` does not lie in the upper half mod `p`. -/
theorem odd_kummerCarry_eq_zero_iff_not_inUpperHalfReal :
    ∀ n p : ℕ, p % 2 = 1 → (kummerCarry n p = 0 ↔ ¬inUpperHalfReal n p) := by
  intro n p hodd
  rw [odd_inUpperHalfReal_iff_kummerCarry_eq_one n p hodd]
  have h01 := kummerCarry_eq_zero_or_one n p
  omega

/-- For any odd modulus `p`, the weighted Kummer carry term equals `upperHalfIndicator n p`. -/
theorem odd_kummerCarryTerm_eq_upperHalfIndicator :
    ∀ n p : ℕ, p % 2 = 1 → kummerCarryTerm n p = upperHalfIndicator n p := by
  intro n p hodd
  unfold kummerCarryTerm upperHalfIndicator
  split_ifs with hup
  · have hk1 : kummerCarry n p = 1 :=
      (odd_inUpperHalfReal_iff_kummerCarry_eq_one n p hodd).mp hup
    simp [hk1]
  · have hk0 : kummerCarry n p = 0 :=
      (odd_kummerCarry_eq_zero_iff_not_inUpperHalfReal n p hodd).mpr hup
    simp [hk0]

/-- Every prime in `upperHalfPrimes n` belongs to `oddPrimeRange n`. -/
theorem upperHalfPrimes_subset_oddPrimeRange :
    ∀ n : ℕ, upperHalfPrimes n ⊆ oddPrimeRange n := by
  intro n p hp
  have hodd := (odd_of_mem_upperHalfPrimes n p hp).1
  simp only [upperHalfPrimes, oddPrimeRange, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hodd⟩

/-- Exact representation of `upperHalfPrimeSum n` as the weighted Kummer carry sum over odd primes `p ≤ n`. -/
theorem upperHalfPrimeSum_eq_sum_oddPrimeRange_kummerCarry :
    ∀ n : ℕ, upperHalfPrimeSum n = ∑ p ∈ oddPrimeRange n, kummerCarryTerm n p := by
  intro n
  rw [upperHalfPrimeSum_eq_sum_primeRange_indicator]
  have hsub : oddPrimeRange n ⊆ primeRange n := by
    intro p hp
    simp only [oddPrimeRange, primeRange, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hzero : ∀ p ∈ primeRange n, p ∉ oddPrimeRange n → upperHalfIndicator n p = 0 := by
    intro p hp hnotodd
    unfold upperHalfIndicator
    split_ifs with hup
    · exfalso
      apply hnotodd
      apply upperHalfPrimes_subset_oddPrimeRange n
      simp only [primeRange, upperHalfPrimes, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2, hup⟩
    · rfl
  rw [← Finset.sum_subset hsub hzero]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [oddPrimeRange, Finset.mem_filter] at hp
  exact (odd_kummerCarryTerm_eq_upperHalfIndicator n p hp.2.2).symm

/-- At `p = 2`, the Kummer carry `kummerCarry n 2` equals the parity bit `n % 2`. -/
theorem kummerCarry_two_eq_mod_two :
    ∀ n : ℕ, kummerCarry n 2 = n % 2 := by
  intro n
  unfold kummerCarry
  omega

/-- For `2 ≤ n`, `primeRange n` decomposes into `oddPrimeRange n` and `{2}`. -/
theorem oddPrimeRange_union_two_eq_primeRange :
    ∀ n : ℕ, 2 ≤ n →
      Disjoint (oddPrimeRange n) ({2} : Finset ℕ) ∧
        oddPrimeRange n ∪ ({2} : Finset ℕ) = primeRange n := by
  intro n hn
  constructor
  · rw [Finset.disjoint_singleton_right]
    simp [oddPrimeRange]
  · ext p
    simp only [oddPrimeRange, primeRange, Finset.mem_union, Finset.mem_filter,
      Finset.mem_range, Finset.mem_singleton, Nat.lt_succ_iff]
    constructor
    · rintro (⟨hle, hp, _⟩ | rfl)
      · exact ⟨hle, hp⟩
      · exact ⟨hn, Nat.prime_two⟩
    · rintro ⟨hle, hp⟩
      rcases hp.eq_two_or_odd with rfl | hodd
      · right; rfl
      · left; exact ⟨hle, hp, hodd⟩

/-- Summing `kummerCarryTerm n p` over all primes `p ≤ n` (for `2 ≤ n`) equals
`upperHalfPrimeSum n + (n % 2) / 2`. -/
theorem sum_primeRange_kummerCarry_eq_upperHalfPrimeSum_add_parity :
    ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ primeRange n, kummerCarryTerm n p =
        upperHalfPrimeSum n + ((n % 2 : ℕ) : ℝ) / 2 := by
  intro n hn
  have hpart := oddPrimeRange_union_two_eq_primeRange n hn
  rw [← hpart.2, Finset.sum_union hpart.1, Finset.sum_singleton]
  rw [← upperHalfPrimeSum_eq_sum_oddPrimeRange_kummerCarry]
  unfold kummerCarryTerm
  rw [kummerCarry_two_eq_mod_two]
  norm_num

/-- For `2 ≤ n`, the signed Kummer carry sum over odd primes minus `1 / 2` equals the
upper-minus-lower prime-residue discrepancy `upperHalfPrimeSum n - lowerComplementPrimeSum n`. -/
theorem sum_oddPrimeRange_signedKummerCarry_eq_discrepancy :
    ∀ n : ℕ, 2 ≤ n →
      (∑ p ∈ oddPrimeRange n, signedKummerCarryTerm n p) - 1 / 2 =
        upperHalfPrimeSum n - lowerComplementPrimeSum n := by
  intro n hn
  have hterm : ∀ p ∈ oddPrimeRange n,
      signedKummerCarryTerm n p = 2 * kummerCarryTerm n p - (1 : ℝ) / (p : ℝ) := by
    intro p _
    unfold signedKummerCarryTerm kummerCarryTerm
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← upperHalfPrimeSum_eq_sum_oddPrimeRange_kummerCarry]
  have hpart := oddPrimeRange_union_two_eq_primeRange n hn
  have hfull : fullPrimeReciprocalSum n =
      (∑ p ∈ oddPrimeRange n, (1 : ℝ) / (p : ℝ)) + 1 / 2 := by
    unfold fullPrimeReciprocalSum
    rw [← hpart.2, Finset.sum_union hpart.1, Finset.sum_singleton]
    norm_num
  have hadd := upperHalfPrimeSum_add_lowerComplementPrimeSum n
  linarith

/-! ## Section 2: Harmonic Quotient Window Fibers `U_k(n)`, `L_k(n)`, and `Q_k(n)` -/

/-- The `k`-th quotient fiber `Q_k(n) = {p ≤ n prime | n / p = k}`. -/
def quotientPrimeFiber (n k : ℕ) : Finset ℕ :=
  (primeRange n).filter (fun p : ℕ ↦ n / p = k)

/-- The `k`-th upper harmonic quotient prime window
`U_k(n) = {p ≤ n prime | n < (k + 1) * p ∧ (2 * k + 1) * p < 2 * n}`. -/
def upperQuotientPrimes (n k : ℕ) : Finset ℕ :=
  (primeRange n).filter (fun p : ℕ ↦ n < (k + 1) * p ∧ (2 * k + 1) * p < 2 * n)

/-- The `k`-th lower harmonic quotient prime window
`L_k(n) = {p ≤ n prime | k * p ≤ n ∧ 2 * n ≤ (2 * k + 1) * p}`. -/
def lowerQuotientPrimes (n k : ℕ) : Finset ℕ :=
  (primeRange n).filter (fun p : ℕ ↦ k * p ≤ n ∧ 2 * n ≤ (2 * k + 1) * p)

/-- Reciprocal sum over the `k`-th upper quotient prime window `U_k(n)`. -/
def upperQuotientSum (n k : ℕ) : ℝ :=
  ∑ p ∈ upperQuotientPrimes n k, (1 : ℝ) / (p : ℝ)

/-- Reciprocal sum over the `k`-th lower quotient prime window `L_k(n)`. -/
def lowerQuotientSum (n k : ℕ) : ℝ :=
  ∑ p ∈ lowerQuotientPrimes n k, (1 : ℝ) / (p : ℝ)

/-- Reciprocal sum over the full `k`-th quotient prime fiber `Q_k(n)`. -/
def quotientFiberSum (n k : ℕ) : ℝ :=
  ∑ p ∈ quotientPrimeFiber n k, (1 : ℝ) / (p : ℝ)

/-- Exact arithmetic characterization of the `k`-th upper harmonic quotient window:
for `0 < p`, `n / p = k ∧ p < 2 * (n % p)` iff `n < (k + 1) * p ∧ (2 * k + 1) * p < 2 * n`. -/
theorem div_eq_and_lt_two_mul_mod_iff_upper_window :
    ∀ n p k : ℕ, 0 < p →
      (n / p = k ∧ p < 2 * (n % p) ↔ n < (k + 1) * p ∧ (2 * k + 1) * p < 2 * n) := by
  intro n p k hp
  have hdiv := Nat.div_add_mod n p
  have hlt := Nat.mod_lt n hp
  constructor
  · rintro ⟨rfl, hmod⟩
    have h1 : (n / p + 1) * p = p * (n / p) + p := by ring
    have h2 : (2 * (n / p) + 1) * p = 2 * (p * (n / p)) + p := by ring
    omega
  · rintro ⟨hlow, hhigh⟩
    have hkp : k * p < n := by nlinarith
    have hq_ge : k ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr (le_of_lt hkp)
    have hq_lt : n / p < k + 1 := (Nat.div_lt_iff_lt_mul hp).mpr hlow
    have hq_eq : n / p = k := by omega
    subst hq_eq
    have h2 : (2 * (n / p) + 1) * p = 2 * (p * (n / p)) + p := by ring
    exact ⟨rfl, by omega⟩

/-- Exact arithmetic characterization of the `k`-th lower harmonic quotient window:
for `0 < p`, `n / p = k ∧ 2 * (n % p) ≤ p` iff `k * p ≤ n ∧ 2 * n ≤ (2 * k + 1) * p`. -/
theorem div_eq_and_two_mul_mod_le_iff_lower_window :
    ∀ n p k : ℕ, 0 < p →
      (n / p = k ∧ 2 * (n % p) ≤ p ↔ k * p ≤ n ∧ 2 * n ≤ (2 * k + 1) * p) := by
  intro n p k hp
  have hdiv := Nat.div_add_mod n p
  have hlt := Nat.mod_lt n hp
  constructor
  · rintro ⟨rfl, hmod⟩
    have h1 : (n / p) * p = p * (n / p) := by ring
    have h2 : (2 * (n / p) + 1) * p = 2 * (p * (n / p)) + p := by ring
    omega
  · rintro ⟨hlow, hhigh⟩
    have hk1p : n < (k + 1) * p := by nlinarith
    have hq_ge : k ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr hlow
    have hq_lt : n / p < k + 1 := (Nat.div_lt_iff_lt_mul hp).mpr hk1p
    have hq_eq : n / p = k := by omega
    subst hq_eq
    have h2 : (2 * (n / p) + 1) * p = 2 * (p * (n / p)) + p := by ring
    exact ⟨rfl, by omega⟩

/-- `upperQuotientPrimes n k` is the `n / p = k` fiber of `upperHalfPrimes n`. -/
theorem upperQuotientPrimes_eq_upperHalfPrimes_filter_div :
    ∀ n k : ℕ, upperQuotientPrimes n k = (upperHalfPrimes n).filter (fun p : ℕ ↦ n / p = k) := by
  intro n k
  ext p
  simp only [upperQuotientPrimes, primeRange, upperHalfPrimes, Finset.mem_filter,
    Finset.mem_range, Nat.lt_succ_iff]
  change (p ≤ n ∧ p.Prime) ∧ (n < (k + 1) * p ∧ (2 * k + 1) * p < 2 * n) ↔
    (p ≤ n ∧ p.Prime ∧ inUpperHalfReal n p) ∧ n / p = k
  rw [inUpperHalfReal_iff_lt_two_mul_mod]
  constructor
  · rintro ⟨⟨hle, hp⟩, hwin⟩
    have hd := (div_eq_and_lt_two_mul_mod_iff_upper_window n p k hp.pos).mpr hwin
    exact ⟨⟨hle, hp, hd.2⟩, hd.1⟩
  · rintro ⟨⟨hle, hp, hmod⟩, hdiv⟩
    have hwin := (div_eq_and_lt_two_mul_mod_iff_upper_window n p k hp.pos).mp ⟨hdiv, hmod⟩
    exact ⟨⟨hle, hp⟩, hwin⟩

/-- `lowerQuotientPrimes n k` is the `n / p = k` fiber of `lowerComplementPrimes n`. -/
theorem lowerQuotientPrimes_eq_lowerComplementPrimes_filter_div :
    ∀ n k : ℕ, lowerQuotientPrimes n k =
      (lowerComplementPrimes n).filter (fun p : ℕ ↦ n / p = k) := by
  intro n k
  ext p
  simp only [lowerQuotientPrimes, primeRange, lowerComplementPrimes, Finset.mem_filter,
    Finset.mem_range, Nat.lt_succ_iff]
  change (p ≤ n ∧ p.Prime) ∧ (k * p ≤ n ∧ 2 * n ≤ (2 * k + 1) * p) ↔
    (p ≤ n ∧ p.Prime ∧ ¬inUpperHalfReal n p) ∧ n / p = k
  rw [inUpperHalfReal_iff_lt_two_mul_mod, not_lt]
  constructor
  · rintro ⟨⟨hle, hp⟩, hwin⟩
    have hd := (div_eq_and_two_mul_mod_le_iff_lower_window n p k hp.pos).mpr hwin
    exact ⟨⟨hle, hp, hd.2⟩, hd.1⟩
  · rintro ⟨⟨hle, hp, hmod⟩, hdiv⟩
    have hwin := (div_eq_and_two_mul_mod_le_iff_lower_window n p k hp.pos).mp ⟨hdiv, hmod⟩
    exact ⟨⟨hle, hp⟩, hwin⟩

/-- Each quotient fiber `quotientPrimeFiber n k` partitions into `upperQuotientPrimes n k`
and `lowerQuotientPrimes n k`. -/
theorem disjoint_upperQuotientPrimes_lowerQuotientPrimes :
    ∀ n k : ℕ, Disjoint (upperQuotientPrimes n k) (lowerQuotientPrimes n k) ∧
      upperQuotientPrimes n k ∪ lowerQuotientPrimes n k = quotientPrimeFiber n k := by
  intro n k
  rw [upperQuotientPrimes_eq_upperHalfPrimes_filter_div,
    lowerQuotientPrimes_eq_lowerComplementPrimes_filter_div]
  have hpart := disjoint_upperHalfPrimes_lowerComplementPrimes n
  constructor
  · exact Finset.disjoint_filter_filter hpart.1
  · rw [← Finset.filter_union, hpart.2]
    rfl

/-- Additive decomposition of the `k`-th quotient fiber reciprocal sum. -/
theorem upperQuotientSum_add_lowerQuotientSum :
    ∀ n k : ℕ, upperQuotientSum n k + lowerQuotientSum n k = quotientFiberSum n k := by
  intro n k
  have hpart := disjoint_upperQuotientPrimes_lowerQuotientPrimes n k
  unfold upperQuotientSum lowerQuotientSum quotientFiberSum
  rw [← hpart.2, Finset.sum_union hpart.1]

/-- For `k = 1`, `upperQuotientPrimes n 1` and `upperQuotientSum n 1` coincide with
`middleHarmonicPrimes n` and `middleHarmonicPrimeSum n` on `(n / 2, 2n / 3)`. -/
theorem upperQuotientPrimes_one_eq_middleHarmonicPrimes :
    ∀ n : ℕ, upperQuotientPrimes n 1 = middleHarmonicPrimes n ∧
      upperQuotientSum n 1 = middleHarmonicPrimeSum n := by
  intro n
  have hset : upperQuotientPrimes n 1 = middleHarmonicPrimes n := by
    ext p
    simp only [upperQuotientPrimes, primeRange, middleHarmonicPrimes, Finset.mem_filter,
      Finset.mem_range, Nat.lt_succ_iff]
    ring_nf
    tauto
  refine ⟨hset, ?_⟩
  unfold upperQuotientSum middleHarmonicPrimeSum
  rw [hset]

/-! ## Section 3: Pairwise Disjointness, Cutoff Partition, and Exhaustion at `K ≥ n / 2` -/

/-- The small-prime (large-quotient `n / p ≥ K + 1`) tail of `upperHalfPrimes n`. -/
def upperSmallPrimeTail (n K : ℕ) : Finset ℕ :=
  (upperHalfPrimes n).filter (fun p : ℕ ↦ K + 1 ≤ n / p)

/-- Reciprocal sum over `upperSmallPrimeTail n K`. -/
def upperSmallPrimeTailSum (n K : ℕ) : ℝ :=
  ∑ p ∈ upperSmallPrimeTail n K, (1 : ℝ) / (p : ℝ)

/-- The small-prime (large-quotient `n / p ≥ K + 1`) tail of `lowerComplementPrimes n`. -/
def lowerSmallPrimeTail (n K : ℕ) : Finset ℕ :=
  (lowerComplementPrimes n).filter (fun p : ℕ ↦ K + 1 ≤ n / p)

/-- Reciprocal sum over `lowerSmallPrimeTail n K`. -/
def lowerSmallPrimeTailSum (n K : ℕ) : ℝ :=
  ∑ p ∈ lowerSmallPrimeTail n K, (1 : ℝ) / (p : ℝ)

/-- The upper harmonic quotient windows `upperQuotientPrimes n k` are pairwise disjoint across `k`. -/
theorem pairwiseDisjoint_upperQuotientPrimes :
    ∀ n : ℕ, ∀ s : Set ℕ, s.PairwiseDisjoint (upperQuotientPrimes n) := by
  intro n s k₁ _ k₂ _ hne
  change Disjoint (upperQuotientPrimes n k₁) (upperQuotientPrimes n k₂)
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [upperQuotientPrimes_eq_upperHalfPrimes_filter_div] at hp1 hp2
  simp only [Finset.mem_filter] at hp1 hp2
  exact hne (hp1.2.symm.trans hp2.2)

/-- The lower harmonic quotient windows `lowerQuotientPrimes n k` are pairwise disjoint across `k`. -/
theorem pairwiseDisjoint_lowerQuotientPrimes :
    ∀ n : ℕ, ∀ s : Set ℕ, s.PairwiseDisjoint (lowerQuotientPrimes n) := by
  intro n s k₁ _ k₂ _ hne
  change Disjoint (lowerQuotientPrimes n k₁) (lowerQuotientPrimes n k₂)
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [lowerQuotientPrimes_eq_lowerComplementPrimes_filter_div] at hp1 hp2
  simp only [Finset.mem_filter] at hp1 hp2
  exact hne (hp1.2.symm.trans hp2.2)

/-- For any cutoff `K`, `upperHalfPrimes n` partitions into `upperSmallPrimeTail n K` and
the disjoint union of `upperQuotientPrimes n k` over `k ∈ Icc 1 K`. -/
theorem upperHalfPrimes_cutoff_partition :
    ∀ n K : ℕ,
      Disjoint (upperSmallPrimeTail n K) ((Finset.Icc 1 K).biUnion (upperQuotientPrimes n)) ∧
        upperSmallPrimeTail n K ∪ (Finset.Icc 1 K).biUnion (upperQuotientPrimes n) =
          upperHalfPrimes n := by
  intro n K
  constructor
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [upperSmallPrimeTail, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc] at hp1 hp2
    rcases hp2 with ⟨k, ⟨_, hkK⟩, hpk⟩
    rw [upperQuotientPrimes_eq_upperHalfPrimes_filter_div, Finset.mem_filter] at hpk
    omega
  · ext p
    simp only [upperSmallPrimeTail, Finset.mem_union, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_Icc]
    constructor
    · rintro (⟨hp, _⟩ | ⟨k, _, hpk⟩)
      · exact hp
      · rw [upperQuotientPrimes_eq_upperHalfPrimes_filter_div, Finset.mem_filter] at hpk
        exact hpk.1
    · intro hp
      by_cases hge : K + 1 ≤ n / p
      · left; exact ⟨hp, hge⟩
      · right
        have hmem := (mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod n p).mp hp
        have hq_pos : 1 ≤ n / p := Nat.div_pos hmem.1 hmem.2.1.pos
        refine ⟨n / p, ⟨hq_pos, by omega⟩, ?_⟩
        rw [upperQuotientPrimes_eq_upperHalfPrimes_filter_div, Finset.mem_filter]
        exact ⟨hp, rfl⟩

/-- For any cutoff `K`, `lowerComplementPrimes n` partitions into `lowerSmallPrimeTail n K` and
the disjoint union of `lowerQuotientPrimes n k` over `k ∈ Icc 1 K`. -/
theorem lowerComplementPrimes_cutoff_partition :
    ∀ n K : ℕ,
      Disjoint (lowerSmallPrimeTail n K) ((Finset.Icc 1 K).biUnion (lowerQuotientPrimes n)) ∧
        lowerSmallPrimeTail n K ∪ (Finset.Icc 1 K).biUnion (lowerQuotientPrimes n) =
          lowerComplementPrimes n := by
  intro n K
  constructor
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [lowerSmallPrimeTail, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc] at hp1 hp2
    rcases hp2 with ⟨k, ⟨_, hkK⟩, hpk⟩
    rw [lowerQuotientPrimes_eq_lowerComplementPrimes_filter_div, Finset.mem_filter] at hpk
    omega
  · ext p
    simp only [lowerSmallPrimeTail, Finset.mem_union, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_Icc]
    constructor
    · rintro (⟨hp, _⟩ | ⟨k, _, hpk⟩)
      · exact hp
      · rw [lowerQuotientPrimes_eq_lowerComplementPrimes_filter_div, Finset.mem_filter] at hpk
        exact hpk.1
    · intro hp
      by_cases hge : K + 1 ≤ n / p
      · left; exact ⟨hp, hge⟩
      · right
        have hmem : p ≤ n ∧ p.Prime := by
          simp only [lowerComplementPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hp
          exact ⟨hp.1, hp.2.1⟩
        have hq_pos : 1 ≤ n / p := Nat.div_pos hmem.1 hmem.2.pos
        refine ⟨n / p, ⟨hq_pos, by omega⟩, ?_⟩
        rw [lowerQuotientPrimes_eq_lowerComplementPrimes_filter_div, Finset.mem_filter]
        exact ⟨hp, rfl⟩

/-- Cutoff decomposition of `upperHalfPrimeSum n` into `upperSmallPrimeTailSum n K` plus
the sum over quotient windows `k ∈ Icc 1 K`. -/
theorem upperHalfPrimeSum_cutoff_decomposition :
    ∀ n K : ℕ,
      upperHalfPrimeSum n =
        upperSmallPrimeTailSum n K + ∑ k ∈ Finset.Icc 1 K, upperQuotientSum n k := by
  intro n K
  have hpart := upperHalfPrimes_cutoff_partition n K
  unfold upperHalfPrimeSum upperSmallPrimeTailSum upperQuotientSum
  rw [← hpart.2, Finset.sum_union hpart.1,
    Finset.sum_biUnion (pairwiseDisjoint_upperQuotientPrimes n _)]

/-- Cutoff decomposition of `lowerComplementPrimeSum n` into `lowerSmallPrimeTailSum n K` plus
the sum over quotient windows `k ∈ Icc 1 K`. -/
theorem lowerComplementPrimeSum_cutoff_decomposition :
    ∀ n K : ℕ,
      lowerComplementPrimeSum n =
        lowerSmallPrimeTailSum n K + ∑ k ∈ Finset.Icc 1 K, lowerQuotientSum n k := by
  intro n K
  have hpart := lowerComplementPrimes_cutoff_partition n K
  unfold lowerComplementPrimeSum lowerSmallPrimeTailSum lowerQuotientSum
  rw [← hpart.2, Finset.sum_union hpart.1,
    Finset.sum_biUnion (pairwiseDisjoint_lowerQuotientPrimes n _)]

/-- Whenever `n / 2 ≤ K`, `upperSmallPrimeTail n K` is empty and its reciprocal sum is `0`. -/
theorem upperSmallPrimeTail_eq_empty_of_half_le :
    ∀ n K : ℕ, n / 2 ≤ K →
      upperSmallPrimeTail n K = ∅ ∧ upperSmallPrimeTailSum n K = 0 := by
  intro n K hK
  have hemp : upperSmallPrimeTail n K = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    simp only [upperSmallPrimeTail, Finset.mem_filter] at hp
    have hprime := (mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod n p).mp hp.1 |>.2.1
    have hp2 : 2 ≤ p := hprime.two_le
    have hdiv_le : n / p ≤ n / 2 := Nat.div_le_div_left hp2 (by decide)
    omega
  refine ⟨hemp, ?_⟩
  unfold upperSmallPrimeTailSum
  rw [hemp, Finset.sum_empty]

/-- Whenever `n / 2 ≤ K`, `lowerSmallPrimeTail n K` is empty and its reciprocal sum is `0`. -/
theorem lowerSmallPrimeTail_eq_empty_of_half_le :
    ∀ n K : ℕ, n / 2 ≤ K →
      lowerSmallPrimeTail n K = ∅ ∧ lowerSmallPrimeTailSum n K = 0 := by
  intro n K hK
  have hemp : lowerSmallPrimeTail n K = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    simp only [lowerSmallPrimeTail, lowerComplementPrimes, Finset.mem_filter] at hp
    have hp2 : 2 ≤ p := hp.1.2.1.two_le
    have hdiv_le : n / p ≤ n / 2 := Nat.div_le_div_left hp2 (by decide)
    omega
  refine ⟨hemp, ?_⟩
  unfold lowerSmallPrimeTailSum
  rw [hemp, Finset.sum_empty]

/-- Complete harmonic quotient-window expansion of `upperHalfPrimeSum n` for any `K ≥ n / 2`. -/
theorem upperHalfPrimeSum_eq_sum_quotient_windows_of_half_le :
    ∀ n K : ℕ, n / 2 ≤ K →
      upperHalfPrimeSum n = ∑ k ∈ Finset.Icc 1 K, upperQuotientSum n k := by
  intro n K hK
  rw [upperHalfPrimeSum_cutoff_decomposition n K,
    (upperSmallPrimeTail_eq_empty_of_half_le n K hK).2, zero_add]

/-- Complete harmonic quotient-window expansion of `upperHalfPrimeSum n - lowerComplementPrimeSum n`
for any `K ≥ n / 2`. -/
theorem discrepancy_eq_sum_quotient_windows_of_half_le :
    ∀ n K : ℕ, n / 2 ≤ K →
      upperHalfPrimeSum n - lowerComplementPrimeSum n =
        ∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k) := by
  intro n K hK
  rw [upperHalfPrimeSum_cutoff_decomposition n K,
    lowerComplementPrimeSum_cutoff_decomposition n K,
    (upperSmallPrimeTail_eq_empty_of_half_le n K hK).2,
    (lowerSmallPrimeTail_eq_empty_of_half_le n K hK).2,
    zero_add, zero_add, ← Finset.sum_sub_distrib]

/-! ## Section 4: Bilateral Window Reciprocal Sandwich and Discrepancy Bounds -/

/-- Bilateral reciprocal bounds for `upperQuotientSum n k` in terms of `|U_k(n)|`:
`((2k + 1) / (2n)) |U_k(n)| ≤ upperQuotientSum n k ≤ ((k + 1) / n) |U_k(n)|`. -/
theorem upperQuotientSum_bounds :
    ∀ n k : ℕ, 0 < n →
      ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * ((upperQuotientPrimes n k).card : ℝ) ≤
        upperQuotientSum n k ∧
      upperQuotientSum n k ≤
        (((k : ℝ) + 1) / (n : ℝ)) * ((upperQuotientPrimes n k).card : ℝ) := by
  intro n k hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold upperQuotientSum
  constructor
  · have hlow : ∀ p ∈ upperQuotientPrimes n k,
        (2 * (k : ℝ) + 1) / (2 * (n : ℝ)) ≤ (1 : ℝ) / (p : ℝ) := by
      intro p hp
      simp only [upperQuotientPrimes, primeRange, Finset.mem_filter] at hp
      have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.1.2.pos
      have h2nR : (0 : ℝ) < 2 * (n : ℝ) := by positivity
      rw [div_le_div_iff₀ h2nR hpR]
      have hlt : ((2 * k + 1) * p : ℝ) < (2 * n : ℝ) := by exact_mod_cast hp.2.2
      linarith
    have hsum := Finset.card_nsmul_le_sum (upperQuotientPrimes n k)
      (fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)) ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) hlow
    simpa [nsmul_eq_mul, mul_comm] using hsum
  · have hhigh : ∀ p ∈ upperQuotientPrimes n k,
        (1 : ℝ) / (p : ℝ) ≤ ((k : ℝ) + 1) / (n : ℝ) := by
      intro p hp
      simp only [upperQuotientPrimes, primeRange, Finset.mem_filter] at hp
      have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.1.2.pos
      rw [div_le_div_iff₀ hpR hnR]
      have hlt : (n : ℝ) < ((k + 1) * p : ℝ) := by exact_mod_cast hp.2.1
      linarith
    have hsum := Finset.sum_le_card_nsmul (upperQuotientPrimes n k)
      (fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)) (((k : ℝ) + 1) / (n : ℝ)) hhigh
    simpa [nsmul_eq_mul, mul_comm] using hsum

/-- Bilateral reciprocal bounds for `lowerQuotientSum n k` in terms of `|L_k(n)|`:
`(k / n) |L_k(n)| ≤ lowerQuotientSum n k ≤ ((2k + 1) / (2n)) |L_k(n)|`. -/
theorem lowerQuotientSum_bounds :
    ∀ n k : ℕ, 0 < n →
      ((k : ℝ) / (n : ℝ)) * ((lowerQuotientPrimes n k).card : ℝ) ≤
        lowerQuotientSum n k ∧
      lowerQuotientSum n k ≤
        ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * ((lowerQuotientPrimes n k).card : ℝ) := by
  intro n k hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold lowerQuotientSum
  constructor
  · have hlow : ∀ p ∈ lowerQuotientPrimes n k,
        (k : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (p : ℝ) := by
      intro p hp
      simp only [lowerQuotientPrimes, primeRange, Finset.mem_filter] at hp
      have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.1.2.pos
      rw [div_le_div_iff₀ hnR hpR]
      have hle : (k * p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.2.1
      linarith
    have hsum := Finset.card_nsmul_le_sum (lowerQuotientPrimes n k)
      (fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)) ((k : ℝ) / (n : ℝ)) hlow
    simpa [nsmul_eq_mul, mul_comm] using hsum
  · have hhigh : ∀ p ∈ lowerQuotientPrimes n k,
        (1 : ℝ) / (p : ℝ) ≤ (2 * (k : ℝ) + 1) / (2 * (n : ℝ)) := by
      intro p hp
      simp only [lowerQuotientPrimes, primeRange, Finset.mem_filter] at hp
      have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.1.2.pos
      have h2nR : (0 : ℝ) < 2 * (n : ℝ) := by positivity
      rw [div_le_div_iff₀ hpR h2nR]
      have hle : (2 * n : ℝ) ≤ ((2 * k + 1) * p : ℝ) := by exact_mod_cast hp.2.2
      linarith
    have hsum := Finset.sum_le_card_nsmul (lowerQuotientPrimes n k)
      (fun p : ℕ ↦ (1 : ℝ) / (p : ℝ)) ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) hhigh
    simpa [nsmul_eq_mul, mul_comm] using hsum

/-- Bilateral quotient-window discrepancy sandwich: for `0 < n` and any `k`,
`((2k + 1)/(2n)) (|U_k(n)| - |L_k(n)|) ≤ u_k(n) - ℓ_k(n) ≤ ((k + 1)/n)|U_k(n)| - (k/n)|L_k(n)|`. -/
theorem quotient_window_discrepancy_sandwich :
    ∀ n k : ℕ, 0 < n →
      ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) *
          (((upperQuotientPrimes n k).card : ℝ) - ((lowerQuotientPrimes n k).card : ℝ)) ≤
        upperQuotientSum n k - lowerQuotientSum n k ∧
      upperQuotientSum n k - lowerQuotientSum n k ≤
        (((k : ℝ) + 1) / (n : ℝ)) * ((upperQuotientPrimes n k).card : ℝ) -
          ((k : ℝ) / (n : ℝ)) * ((lowerQuotientPrimes n k).card : ℝ) := by
  intro n k hn
  have hu := upperQuotientSum_bounds n k hn
  have hl := lowerQuotientSum_bounds n k hn
  constructor <;> linarith

/-- Absolute-value triangle bound on each quotient window:
`|upperQuotientSum n k - lowerQuotientSum n k| ≤ quotientFiberSum n k`. -/
theorem abs_quotient_window_discrepancy_le_quotientFiberSum :
    ∀ n k : ℕ, |upperQuotientSum n k - lowerQuotientSum n k| ≤ quotientFiberSum n k := by
  intro n k
  have hu_nonneg : 0 ≤ upperQuotientSum n k := by
    unfold upperQuotientSum
    apply Finset.sum_nonneg
    intro p _; positivity
  have hl_nonneg : 0 ≤ lowerQuotientSum n k := by
    unfold lowerQuotientSum
    apply Finset.sum_nonneg
    intro p _; positivity
  have hadd := upperQuotientSum_add_lowerQuotientSum n k
  rw [abs_le]
  constructor <;> linarith

/-- Cutoff discrepancy bound for `|upperHalfPrimeSum n - log(log n) / 2|` combining the
small-prime tail discrepancy, the sum of quotient-window discrepancies over `k ∈ Icc 1 K`,
and the second Mertens constant/error. -/
theorem abs_upperHalfPrimeSum_sub_half_mertens_le_cutoff :
    ∀ n K : ℕ,
      |upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2| ≤
        (|upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K| +
          (∑ k ∈ Finset.Icc 1 K, |upperQuotientSum n k - lowerQuotientSum n k|) +
          |Mertens.M + Mertens.E₂p (n : ℝ)|) / 2 := by
  intro n K
  rw [upperHalfPrimeSum_sub_half_mertens_eq_half_diff n]
  rw [upperHalfPrimeSum_cutoff_decomposition n K,
    lowerComplementPrimeSum_cutoff_decomposition n K]
  have hsplit :
      upperSmallPrimeTailSum n K + (∑ k ∈ Finset.Icc 1 K, upperQuotientSum n k) -
        (lowerSmallPrimeTailSum n K + (∑ k ∈ Finset.Icc 1 K, lowerQuotientSum n k)) +
        Mertens.M + Mertens.E₂p (n : ℝ) =
      (upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K) +
        (∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k)) +
        (Mertens.M + Mertens.E₂p (n : ℝ)) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsplit, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  have htri1 := abs_add_le
    ((upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K) +
      ∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k))
    (Mertens.M + Mertens.E₂p (n : ℝ))
  have htri2 := abs_add_le
    (upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K)
    (∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k))
  have htri3 := Finset.abs_sum_le_sum_abs
    (fun k : ℕ ↦ upperQuotientSum n k - lowerQuotientSum n k) (Finset.Icc 1 K)
  linarith

/-! ## Section 5: Positive and Negative Falsifying Controls -/

/-- Positive control at `n = 5`: `upperHalfPrimes 5 = {3}` and `upperHalfPrimeSum 5 = 1 / 3`. -/
theorem positive_control_upperHalfPrimeSum_five :
    upperHalfPrimes 5 = {3} ∧ upperHalfPrimeSum 5 = 1 / 3 := by
  have hset : upperHalfPrimes 5 = {3} := by
    ext p
    rw [mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod, Finset.mem_singleton]
    constructor
    · rintro ⟨hle, hp, hmod⟩
      have hp2 : 2 ≤ p := hp.two_le
      interval_cases p <;> omega
    · rintro rfl
      exact ⟨by decide, Nat.prime_three, by decide⟩
  refine ⟨hset, ?_⟩
  unfold upperHalfPrimeSum
  rw [hset, Finset.sum_singleton]
  norm_num

/-- Positive control at `n = 6`: `upperHalfPrimes 6 = ∅` and `upperHalfPrimeSum 6 = 0`
(since `6 % 2 = 0`, `6 % 3 = 0`, and `6 % 5 = 1 < 5 / 2`). -/
theorem positive_control_upperHalfPrimeSum_six :
    upperHalfPrimes 6 = ∅ ∧ upperHalfPrimeSum 6 = 0 := by
  have hset : upperHalfPrimes 6 = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    rw [mem_upperHalfPrimes_iff_prime_and_lt_two_mul_mod] at hp
    rcases hp with ⟨hle, hprime, hmod⟩
    have hp2 : 2 ≤ p := hprime.two_le
    interval_cases p
    · omega
    · omega
    · exact absurd hprime (by decide)
    · omega
    · omega
  refine ⟨hset, ?_⟩
  unfold upperHalfPrimeSum
  rw [hset, Finset.sum_empty]

/-- Negative control at `n = 3`: the unadjusted Kummer carry sum over all primes `p ≤ 3`
differs from `upperHalfPrimeSum 3` by `1 / 2` because `kummerCarry 3 2 = 1` whereas
`2 ∉ upperHalfPrimes 3`. -/
theorem negative_control_unadjusted_kummerCarry_sum_three :
    ∑ p ∈ primeRange 3, kummerCarryTerm 3 p ≠ upperHalfPrimeSum 3 := by
  have hsum := sum_primeRange_kummerCarry_eq_upperHalfPrimeSum_add_parity 3 (by decide)
  intro heq
  linarith


end Erdos726

end
