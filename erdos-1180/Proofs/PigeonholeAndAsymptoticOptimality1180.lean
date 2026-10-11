module

/-
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

public import GlibichukBilinearCover1180

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise
open Filter Finset

namespace Erdos1180

/-!
# Large-Prime Pigeonhole Lower Bounds and Separation from `C ε` for Erdős #1180

This module establishes the large-prime pigeonhole lower bounds on `CAsymptotic ε`
(`inv_le_CAsymptotic` and `natCeil_inv_le_CAsymptotic`), proves the thresholded large-prime
formulation of `erdos_1180.variants.lower_bound` (`erdos_1180_lower_bound_large_primes`),
characterizes the unit-summand regime `CAsymptotic ε = 1 ↔ 1 ≤ ε`, and proves the strict
separation `CAsymptotic (n⁻¹) < C (n⁻¹)` for all `n ≥ 15`.
-/

/-! ## 1. Large-Prime Pigeonhole Power Obstruction -/

theorem natFloor_succ_cast_le_two_mul_rpow {ε : ℝ} {n : ℕ} (hε : 0 ≤ ε) (hn : 1 ≤ n) :
    ((⌊(n : ℝ) ^ ε⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ ε := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε
  have hfl : (⌊(n : ℝ) ^ ε⌋₊ : ℝ) ≤ (n : ℝ) ^ ε := Nat.floor_le (by positivity)
  push_cast
  linarith

theorem natFloor_succ_pow_cast_le_two_pow_mul_rpow {ε : ℝ} {n B : ℕ}
    (hε : 0 ≤ ε) (hn : 1 ≤ n) :
    (((⌊(n : ℝ) ^ ε⌋₊ + 1) ^ B : ℕ) : ℝ) ≤ (2 : ℝ) ^ B * (n : ℝ) ^ ((B : ℝ) * ε) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hstep := natFloor_succ_cast_le_two_mul_rpow hε hn
  calc
    (((⌊(n : ℝ) ^ ε⌋₊ + 1) ^ B : ℕ) : ℝ)
      = ((⌊(n : ℝ) ^ ε⌋₊ + 1 : ℕ) : ℝ) ^ B := by push_cast; rfl
    _ ≤ (2 * (n : ℝ) ^ ε) ^ B := pow_le_pow_left₀ (by positivity) hstep B
    _ = (2 : ℝ) ^ B * ((n : ℝ) ^ ε) ^ B := mul_pow 2 ((n : ℝ) ^ ε) B
    _ = (2 : ℝ) ^ B * ((n : ℝ) ^ ε) ^ (B : ℝ) := by rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ B * (n : ℝ) ^ ((B : ℝ) * ε) := by
        rw [← Real.rpow_mul hn0, mul_comm ε (B : ℝ)]

theorem eventually_natFloor_succ_pow_lt_self_of_mul_lt_one {ε : ℝ} {B : ℕ}
    (hε : 0 ≤ ε) (hlt : (B : ℝ) * ε < 1) :
    ∀ᶠ n : ℕ in atTop, (⌊(n : ℝ) ^ ε⌋₊ + 1) ^ B < n := by
  have hev := mul_rpow_lt_rpow_atTop (C := (2 : ℝ) ^ B) hlt
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hbound := natFloor_succ_pow_cast_le_two_pow_mul_rpow (B := B) hε hn1
  have hrpow1 : (n : ℝ) ^ (1 : ℝ) = (n : ℝ) := Real.rpow_one (n : ℝ)
  have hreal : (((⌊(n : ℝ) ^ ε⌋₊ + 1) ^ B : ℕ) : ℝ) < (n : ℝ) := by
    calc
      (((⌊(n : ℝ) ^ ε⌋₊ + 1) ^ B : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ B * (n : ℝ) ^ ((B : ℝ) * ε) := hbound
      _ < (n : ℝ) ^ (1 : ℝ) := hn
      _ = (n : ℝ) := hrpow1
  exact Nat.cast_lt.mp hreal

theorem exists_threshold_not_cover_of_mul_lt_one {ε : ℝ} {B : ℕ}
    (hε : 0 ≤ ε) (hlt : (B : ℝ) * ε < 1) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∃ a : ZMod p,
      ∀ s : Multiset ℕ, Represents ε p a s → B + 1 ≤ s.card := by
  have hev := eventually_natFloor_succ_pow_lt_self_of_mul_lt_one hε hlt
  rw [eventually_atTop] at hev
  obtain ⟨P, hP⟩ := hev
  refine ⟨P, fun p hpP hp ↦ ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra h_all
  push Not at h_all
  have hcover : ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ B ∧ Represents ε p a s := by
    intro a
    obtain ⟨s, hrep, hlt_card⟩ := h_all a
    exact ⟨s, Nat.le_of_lt_succ hlt_card, hrep⟩
  exact Nat.not_le_of_gt (hP p hpP) (prime_le_natFloor_succ_pow_of_cover hcover)

theorem not_mem_asymptoticBoundSet_of_mul_lt_one {ε : ℝ} {B : ℕ}
    (hε : 0 ≤ ε) (hlt : (B : ℝ) * ε < 1) :
    B ∉ AsymptoticBoundSet ε := by
  rintro ⟨P₁, hP₁⟩
  obtain ⟨P₂, hP₂⟩ := exists_threshold_not_cover_of_mul_lt_one hε hlt
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (max P₁ P₂)
  obtain ⟨a, ha⟩ := hP₂ p ((le_max_right P₁ P₂).trans hp_ge) hp
  obtain ⟨s, hcard, hrep⟩ := hP₁ p ((le_max_left P₁ P₂).trans hp_ge) hp a
  exact Nat.not_le_of_gt (ha s hrep) hcard

/-- Unconditional large-prime pigeonhole lower bound matching the thresholded
`erdos_1180.variants.lower_bound` formulation (PR #6951 in `google-deepmind/formal-conjectures`),
proved with `K = 1 / 2`. -/
theorem erdos_1180_lower_bound_large_primes :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∃ a : ZMod p,
        ∀ s : Multiset ℕ, Represents ε p a s → K * ε⁻¹ ≤ (s.card : ℝ) := by
  refine ⟨1 / 2, by norm_num, fun ε hε0 _ ↦ ?_⟩
  let B : ℕ := ⌊(1 / 2 : ℝ) * ε⁻¹⌋₊
  have hfl : (B : ℝ) ≤ (1 / 2 : ℝ) * ε⁻¹ := Nat.floor_le (by positivity)
  have hlt_fl : (1 / 2 : ℝ) * ε⁻¹ < (B : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmul : (B : ℝ) * ε < 1 := by
    calc
      (B : ℝ) * ε ≤ ((1 / 2 : ℝ) * ε⁻¹) * ε :=
        mul_le_mul_of_nonneg_right hfl hε0.le
      _ = (1 / 2 : ℝ) * (ε⁻¹ * ε) := by ring
      _ = 1 / 2 := by rw [inv_mul_cancel₀ hε0.ne', mul_one]
      _ < 1 := by norm_num
  obtain ⟨P, hP⟩ := exists_threshold_not_cover_of_mul_lt_one hε0.le hmul
  refine ⟨P, fun p hpP hp ↦ ?_⟩
  obtain ⟨a, ha⟩ := hP p hpP hp
  refine ⟨a, fun s hrep ↦ ?_⟩
  have hcard : B + 1 ≤ s.card := ha s hrep
  have hcardR : (B : ℝ) + 1 ≤ (s.card : ℝ) := by exact_mod_cast hcard
  exact hlt_fl.le.trans hcardR

/-! ## 2. Universal Lower Bounds `ε⁻¹ ≤ ⌈ε⁻¹⌉₊ ≤ CAsymptotic ε` and Separation from `C ε` -/

theorem one_le_mul_of_mem_asymptoticBoundSet {ε : ℝ} {B : ℕ}
    (hε : 0 ≤ ε) (hB : B ∈ AsymptoticBoundSet ε) :
    1 ≤ (B : ℝ) * ε := by
  by_contra hlt
  exact not_mem_asymptoticBoundSet_of_mul_lt_one hε (lt_of_not_ge hlt) hB

theorem inv_le_cast_of_mem_asymptoticBoundSet {ε : ℝ} {B : ℕ}
    (hε : 0 < ε) (hB : B ∈ AsymptoticBoundSet ε) :
    ε⁻¹ ≤ (B : ℝ) := by
  have h1 := one_le_mul_of_mem_asymptoticBoundSet hε.le hB
  rw [inv_eq_one_div, div_le_iff₀ hε]
  exact h1

theorem natCeil_inv_le_of_mem_asymptoticBoundSet {ε : ℝ} {B : ℕ}
    (hε : 0 < ε) (hB : B ∈ AsymptoticBoundSet ε) :
    ⌈ε⁻¹⌉₊ ≤ B :=
  Nat.ceil_le.mpr (inv_le_cast_of_mem_asymptoticBoundSet hε hB)

/-- Universal reciprocal lower bound `ε⁻¹ ≤ (CAsymptotic ε : ℝ)` for every `ε > 0`. -/
theorem inv_le_CAsymptotic {ε : ℝ} (hε : 0 < ε) :
    ε⁻¹ ≤ (CAsymptotic ε : ℝ) :=
  inv_le_cast_of_mem_asymptoticBoundSet hε (CAsymptotic_mem_asymptoticBoundSet hε)

/-- Universal discrete ceiling lower bound `⌈ε⁻¹⌉₊ ≤ CAsymptotic ε` for every `ε > 0`. -/
theorem natCeil_inv_le_CAsymptotic {ε : ℝ} (hε : 0 < ε) :
    ⌈ε⁻¹⌉₊ ≤ CAsymptotic ε :=
  natCeil_inv_le_of_mem_asymptoticBoundSet hε (CAsymptotic_mem_asymptoticBoundSet hε)

theorem CAsymptotic_eq_one_iff {ε : ℝ} (hε : 0 < ε) :
    CAsymptotic ε = 1 ↔ 1 ≤ ε := by
  constructor
  · intro h1
    by_contra hlt
    have hinv : (1 : ℝ) < ε⁻¹ := (one_lt_inv₀ hε).mpr (lt_of_not_ge hlt)
    have hle : ε⁻¹ ≤ (CAsymptotic ε : ℝ) := inv_le_CAsymptotic hε
    rw [h1, Nat.cast_one] at hle
    linarith
  · exact CAsymptotic_eq_one_of_one_le

/-- Large-prime asymptotic optimality conjecture (`CAsymptotic ε ≤ ε⁻¹ ^ (1 + o(1))`). -/
def Erdos1180AsymptoticOptimalConjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), (CAsymptotic ε : ℝ) ≤ ε⁻¹ ^ (1 + δ)

theorem one_hundred_twenty_eight_mul_sq_lt_two_pow (n : ℕ) (hn : 15 ≤ n) :
    128 * n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
      calc
        128 * (n + 1) ^ 2 < 2 * (128 * n ^ 2) := by nlinarith
        _ < 2 * 2 ^ n := Nat.mul_lt_mul_of_pos_left ih zero_lt_two
        _ = 2 ^ (n + 1) := by rw [pow_succ']

/-- Strict separation between the large-prime constant `CAsymptotic` and the unthresholded all-prime
constant `C` at unit fractions: for every `n ≥ 15`, `CAsymptotic ((n : ℝ)⁻¹) < C ((n : ℝ)⁻¹)`. -/
theorem CAsymptotic_inv_nat_lt_C_inv_nat {n : ℕ} (hn : 15 ≤ n) :
    CAsymptotic ((n : ℝ)⁻¹) < C ((n : ℝ)⁻¹) := by
  have hnpos : (0 : ℝ) < n := by positivity
  let ε : ℝ := (n : ℝ)⁻¹
  have hε0 : 0 < ε := inv_pos.mpr hnpos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ hn1
  have hinv : ε⁻¹ = (n : ℝ) := inv_inv (n : ℝ)
  have hupper : (CAsymptotic ε : ℝ) ≤ 32 * (n : ℝ) ^ 2 := by
    simpa [hinv] using CAsymptotic_le_thirty_two_mul_inv_sq hε0 hε1
  have hlower : (2 : ℝ) ^ (n : ℝ) ≤ 4 * (C ε : ℝ) := by
    simpa [hinv] using two_rpow_inv_le_four_mul_C hε0
  rw [Real.rpow_natCast] at hlower
  have hpow_lt : ((128 * n ^ 2 : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast one_hundred_twenty_eight_mul_sq_lt_two_pow n hn
  push_cast at hpow_lt
  have hreal : (CAsymptotic ε : ℝ) < (C ε : ℝ) := by linarith
  exact Nat.cast_lt.mp hreal

end Erdos1180
