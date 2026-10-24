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

public import Erdos1122Unified435
public import WirsingWindowAveragingAndLittleODiffRigidity1122
public import ControlledDescentTelescopingAndBoundedJumpRigidity1122

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace Erdos1122

/-!
# Controlled-Descent Logarithmic Ratio Squeeze, Two-Sided Base-`a` Division Trajectories, and Dyadic-Shell Rigidity (Erdős Problem #1122)

This module proves five universal structural results for Erdős Problem #1122:
1. **Base-`a` Division Windows (`divLowerWindow`, `divUpperWindow`, `divWindow`) and Single-Step Two-Sided Bounds**:
   Introduces the lower remainder window `divLowerWindow a m j = [a * (m / a ^ (j + 1)), m / a ^ j)`,
   the ceiling-step upper remainder window `divUpperWindow a m j = [m / a ^ j + 1, a * (m / a ^ (j + 1) + 1))`,
   and the full base-`a` division window `divWindow a m j = [a * (m / a ^ (j + 1)), a * (m / a ^ (j + 1) + 1))`
   of exact length `a`. By pairing the floor quotient `m / a` with the ceiling-step quotient `m / a + 1`,
   both the lower drift `f (m / a) + f a - f m` and the upper drift `f (m + 1) - f (m / a + 1) - f a`
   move upward and are therefore bounded solely by `HasPrefixBoundedDownwardJumps f X D`.
2. **Two-Sided Iterated Base-`a` Division Sandwich and Trajectory Window Disjointness**:
   Establishes the iterated `s`-step lower and upper bounds along `divWindow a m j` (`j ∈ Finset.range s`),
   proves that `divWindow a m j` (`j ∈ Finset.range s`) are pairwise disjoint whenever `1 ≤ m / a ^ s` and
   `2 ≤ a` (`a * (m / a ^ (j₂ + 1) + 1) ≤ a * (m / a ^ (j₁ + 1))` for `j₁ < j₂`), bounds the total
   trajectory descent count by `descentCount f X`, and derives the base-`2` normalized (`m / 2 ^ s = 1`)
   two-sided trajectory squeeze.
3. **Controlled-Descent `Nat.log` Sandwich, Cross-Product Deviation, and Unconditional `o(log X)` Log-Rigidity**:
   Generalizes the `Nat.log` power-additive sandwich, cross-product deviation inequality, and
   logarithmic ratio squeeze from `descentCount f X = 0` to `HasPrefixBoundedDownwardJumps f X D`,
   proving `|f m / log m - f n / log n| ≤ (|f n| + D * descentCount f X) / (k * log m)` and deducing
   unconditional `IsScaledLogOnPos f` whenever `descentCount f X = o(log X)` and `HasBoundedDownwardJumps f D`.
4. **Shifted Division-Window Disjointness and Zero-Descent Trajectory Existence Under `descentCount f X = o(X)`**:
   Proves that for fixed `j < s` (with `a ^ s ≤ m`), the shifted division windows `divWindow a (u * m) j`
   are pairwise disjoint across shifts `u ∈ S`, bounds the number of trajectory-violating shifts in `[1, U]`
   by `s * descentCount f X`, and proves that under `s * descentCount f X < U` there exists a shift
   `u ∈ [1, U]` whose entire `s`-step division trajectory is descent-free, yielding the exact
   zero-descent sandwich `f ((u * m) / a ^ s) - f u + s * f a ≤ f m ≤ f ((u * m) / a ^ s + 1) - f u + s * f a`
   with `u ≤ (u * m) / a ^ s < (u * m) / a ^ s + 1 ≤ a * u`.
5. **Dyadic-Shell Oscillation Rigidity Equivalence and Separation Controls**:
   Introduces `HasBoundedDyadicShellOscillation f C` (`|f q - f u| ≤ C` for `u ≤ q ≤ 2 * u`), proves
   that under `IsCoprimeAdditive f`, `descentCount f X = o(X)`, and `HasBoundedDownwardJumps f D`,
   bounded dyadic-shell oscillation implies `|(k : ℝ) * f b - (Nat.log 2 (b ^ k) : ℝ) * f 2| ≤ C`
   and hence `IsScaledLogOnPos f`, and establishes the exact `iff` characterization
   `IsScaledLogOnPos f ↔ ∃ C : ℝ, HasBoundedDyadicShellOscillation f C`.
-/

/-! ## Section 1: Base-`a` Division Windows and Single-Step Two-Sided Bounds -/

/-- Lower remainder window `[a * (m / a ^ (j + 1)), m / a ^ j)` at division level `j`. -/
def divLowerWindow (a m j : ℕ) : Finset ℕ :=
  Finset.Ico (a * (m / a ^ (j + 1))) (m / a ^ j)

/-- Ceiling-step upper remainder window `[m / a ^ j + 1, a * (m / a ^ (j + 1) + 1))` at division level `j`. -/
def divUpperWindow (a m j : ℕ) : Finset ℕ :=
  Finset.Ico (m / a ^ j + 1) (a * (m / a ^ (j + 1) + 1))

/-- Full base-`a` division window `[a * (m / a ^ (j + 1)), a * (m / a ^ (j + 1) + 1))` of length `a` at level `j`. -/
def divWindow (a m j : ℕ) : Finset ℕ :=
  Finset.Ico (a * (m / a ^ (j + 1))) (a * (m / a ^ (j + 1) + 1))

/-- Quotient step relation `m / a ^ (j + 1) = (m / a ^ j) / a`. -/
theorem div_pow_succ_eq (a m j : ℕ) : m / a ^ (j + 1) = (m / a ^ j) / a := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]

/-- Lower endpoint inequality `a * (m / a ^ (j + 1)) ≤ m / a ^ j`. -/
theorem mul_div_pow_succ_le (a m j : ℕ) : a * (m / a ^ (j + 1)) ≤ m / a ^ j := by
  rw [div_pow_succ_eq]
  exact Nat.mul_div_le (m / a ^ j) a

/-- Upper endpoint strict inequality `m / a ^ j < a * (m / a ^ (j + 1) + 1)` for `1 ≤ a`. -/
theorem div_pow_lt_mul_succ (a m j : ℕ) (ha : 1 ≤ a) :
    m / a ^ j < a * (m / a ^ (j + 1) + 1) := by
  rw [div_pow_succ_eq]
  have h := Nat.div_add_mod (m / a ^ j) a
  have hmod : (m / a ^ j) % a < a := Nat.mod_lt _ (by omega)
  have h2 : a * ((m / a ^ j) / a + 1) = a * ((m / a ^ j) / a) + a := by ring
  omega

/-- `divLowerWindow a m j` is a subset of `divWindow a m j` for `1 ≤ a`. -/
theorem divLowerWindow_subset_divWindow (a m j : ℕ) (ha : 1 ≤ a) :
    divLowerWindow a m j ⊆ divWindow a m j := by
  dsimp [divLowerWindow, divWindow]
  exact Finset.Ico_subset_Ico (le_refl _) (le_of_lt (div_pow_lt_mul_succ a m j ha))

/-- `divUpperWindow a m j` is a subset of `divWindow a m j`. -/
theorem divUpperWindow_subset_divWindow (a m j : ℕ) :
    divUpperWindow a m j ⊆ divWindow a m j := by
  dsimp [divUpperWindow, divWindow]
  have h := mul_div_pow_succ_le a m j
  exact Finset.Ico_subset_Ico (by omega) (le_refl _)

/-- Shift index recurrence `divWindow a m (j + 1) = divWindow a (m / a) j`. -/
theorem divWindow_succ_eq (a m j : ℕ) :
    divWindow a m (j + 1) = divWindow a (m / a) j := by
  dsimp [divWindow]
  have h1 : m / a ^ (j + 1 + 1) = (m / a) / a ^ (j + 1) := by
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
  rw [h1]

/-- **Window-Localized Single Division-Step Lower Bound**:
For any completely additive function `f` with `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`),
base `a ≥ 1`, and `m` with `1 ≤ m / a` and `m ≤ X + 1`:
`f (m / a) + f a - D * ((divLowerWindow a m 0 ∩ descentFinset f X).card : ℝ) ≤ f m`. -/
theorem completely_additive_div_step_window_lower_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m / a) (hX : m ≤ X + 1) :
    f (m / a) + f a - D * ((divLowerWindow a m 0 ∩ descentFinset f X).card : ℝ) ≤ f m := by
  have hprod_ge1 : 1 ≤ a * (m / a) := Nat.mul_pos ha hm
  have hprod_le : a * (m / a) ≤ m := Nat.mul_div_le m a
  have hstep := sub_le_mul_card_Ico_inter_descentFinset hD0 hD hprod_ge1 hprod_le hX
  rw [hmul a ha (m / a) hm] at hstep
  have hwin : divLowerWindow a m 0 = Finset.Ico (a * (m / a)) m := by
    simp [divLowerWindow]
  rw [hwin]
  linarith

/-- **Full-Window Single Division-Step Lower Bound**:
Relaxes `divLowerWindow a m 0` to `divWindow a m 0` in the single-step lower bound. -/
theorem completely_additive_div_step_full_window_lower_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m / a) (hX : m ≤ X + 1) :
    f (m / a) + f a - D * ((divWindow a m 0 ∩ descentFinset f X).card : ℝ) ≤ f m := by
  have hlow := completely_additive_div_step_window_lower_bound hmul hD0 hD ha hm hX
  have hsub : divLowerWindow a m 0 ∩ descentFinset f X ⊆ divWindow a m 0 ∩ descentFinset f X :=
    Finset.inter_subset_inter (divLowerWindow_subset_divWindow a m 0 ha) (Finset.Subset.refl _)
  have hcard : (divLowerWindow a m 0 ∩ descentFinset f X).card ≤
      (divWindow a m 0 ∩ descentFinset f X).card := Finset.card_le_card hsub
  have hmul_le : D * ((divLowerWindow a m 0 ∩ descentFinset f X).card : ℝ) ≤
      D * ((divWindow a m 0 ∩ descentFinset f X).card : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hD0
  linarith

/-- **Window-Localized Ceiling-Step Division Upper Bound on `f (m + 1)`**:
Under `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`), for `1 ≤ a` and `a * (m / a + 1) ≤ X + 1`:
`f (m + 1) - f (m / a + 1) - f a ≤ D * ((divUpperWindow a m 0 ∩ descentFinset f X).card : ℝ)`. -/
theorem completely_additive_div_step_succ_window_upper_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {a m : ℕ} (ha : 1 ≤ a) (hX : a * (m / a + 1) ≤ X + 1) :
    f (m + 1) - f (m / a + 1) - f a ≤
      D * ((divUpperWindow a m 0 ∩ descentFinset f X).card : ℝ) := by
  have hlt : m < a * (m / a + 1) := by
    have h := div_pow_lt_mul_succ a m 0 ha
    simpa using h
  have hstep := sub_le_mul_card_Ico_inter_descentFinset hD0 hD (Nat.succ_pos m) (by omega) hX
  rw [hmul a ha (m / a + 1) (Nat.succ_pos (m / a))] at hstep
  have hwin : divUpperWindow a m 0 = Finset.Ico (m + 1) (a * (m / a + 1)) := by
    simp [divUpperWindow]
  rw [hwin]
  linarith

/-- **Full-Window Ceiling-Step Division Upper Bound on `f m`**:
Under `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`), for `1 ≤ a`, `1 ≤ m`, and
`a * (m / a + 1) ≤ X + 1`:
`f m - f (m / a + 1) - f a ≤ D * ((divWindow a m 0 ∩ descentFinset f X).card : ℝ)`. -/
theorem completely_additive_div_step_full_window_upper_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) (hX : a * (m / a + 1) ≤ X + 1) :
    f m - f (m / a + 1) - f a ≤
      D * ((divWindow a m 0 ∩ descentFinset f X).card : ℝ) := by
  have hlt : m < a * (m / a + 1) := by
    have h := div_pow_lt_mul_succ a m 0 ha
    simpa using h
  have hlow : a * (m / a) ≤ m := Nat.mul_div_le m a
  have hstep := sub_le_mul_card_Ico_inter_descentFinset hD0 hD hm (le_of_lt hlt) hX
  rw [hmul a ha (m / a + 1) (Nat.succ_pos (m / a))] at hstep
  have hwin : divWindow a m 0 = Finset.Ico (a * (m / a)) (a * (m / a + 1)) := by
    simp [divWindow]
  have hsub : Finset.Ico m (a * (m / a + 1)) ∩ descentFinset f X ⊆
      divWindow a m 0 ∩ descentFinset f X := by
    rw [hwin]
    exact Finset.inter_subset_inter (Finset.Ico_subset_Ico hlow (le_refl _)) (Finset.Subset.refl _)
  have hcard : (Finset.Ico m (a * (m / a + 1)) ∩ descentFinset f X).card ≤
      (divWindow a m 0 ∩ descentFinset f X).card := Finset.card_le_card hsub
  have hmul_le : D * ((Finset.Ico m (a * (m / a + 1)) ∩ descentFinset f X).card : ℝ) ≤
      D * ((divWindow a m 0 ∩ descentFinset f X).card : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hD0
  linarith

/-! ## Section 2: Two-Sided Iterated Base-`a` Division Sandwich and Trajectory Window Disjointness -/

/-- **Window-Localized Iterated Division Lower Bound**:
Under `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`), for `1 ≤ a`, `1 ≤ m / a ^ s`, and
`m ≤ X + 1`:
`f (m / a ^ s) + (s : ℝ) * f a - D * (∑ j ∈ Finset.range s, ((divWindow a m j ∩ descentFinset f X).card : ℝ)) ≤ f m`. -/
theorem completely_additive_iterated_div_window_lower_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {a : ℕ} (ha : 1 ≤ a) (s : ℕ) {m : ℕ} (hm : 1 ≤ m / a ^ s) (hX : m ≤ X + 1) :
    f (m / a ^ s) + (s : ℝ) * f a -
      D * (∑ j ∈ Finset.range s, ((divWindow a m j ∩ descentFinset f X).card : ℝ)) ≤ f m := by
  induction s generalizing m with
  | zero => simp
  | succ s ih =>
    have hpow_eq : m / a ^ (s + 1) = (m / a) / a ^ s := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have hm_div : 1 ≤ (m / a) / a ^ s := by rwa [← hpow_eq]
    have hm_a : 1 ≤ m / a := le_trans hm_div (Nat.div_le_self (m / a) (a ^ s))
    have hm_a_le : m / a ≤ X + 1 := le_trans (Nat.div_le_self m a) hX
    have ih_step := ih hm_div hm_a_le
    have h_step := completely_additive_div_step_full_window_lower_bound hmul hD0 hD ha hm_a hX
    have hsum_eq : (∑ j ∈ Finset.range (s + 1), ((divWindow a m j ∩ descentFinset f X).card : ℝ)) =
        (∑ j ∈ Finset.range s, ((divWindow a (m / a) j ∩ descentFinset f X).card : ℝ)) +
        ((divWindow a m 0 ∩ descentFinset f X).card : ℝ) := by
      rw [Finset.sum_range_succ']
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [divWindow_succ_eq]
    rw [hpow_eq, hsum_eq]
    push_cast
    linarith

/-- **Window-Localized Iterated Ceiling-Step Division Upper Bound on `f (m + 1)`**:
Under `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`), for `1 ≤ a`, `s : ℕ`, and
`a * (m / a + 1) ≤ X + 1`:
`f (m + 1) ≤ f (m / a ^ s + 1) + (s : ℝ) * f a + D * (∑ j ∈ Finset.range s, ((divWindow a m j ∩ descentFinset f X).card : ℝ))`. -/
theorem completely_additive_iterated_div_succ_window_upper_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {a : ℕ} (ha : 1 ≤ a) (s : ℕ) {m : ℕ} (hX : a * (m / a + 1) ≤ X + 1) :
    f (m + 1) ≤ f (m / a ^ s + 1) + (s : ℝ) * f a +
      D * (∑ j ∈ Finset.range s, ((divWindow a m j ∩ descentFinset f X).card : ℝ)) := by
  induction s generalizing m with
  | zero => simp
  | succ s ih =>
    have hpow_eq : m / a ^ (s + 1) = (m / a) / a ^ s := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have hX_div : a * ((m / a) / a + 1) ≤ X + 1 := by
      have hdiv_le : (m / a) / a ≤ m / a := Nat.div_le_self (m / a) a
      have hmul_le : a * ((m / a) / a + 1) ≤ a * (m / a + 1) :=
        Nat.mul_le_mul_left a (Nat.add_le_add_right hdiv_le 1)
      exact le_trans hmul_le hX
    have ih_step := ih hX_div
    have h_step := completely_additive_div_step_succ_window_upper_bound hmul hD0 hD ha hX
    have hsub : divUpperWindow a m 0 ∩ descentFinset f X ⊆ divWindow a m 0 ∩ descentFinset f X :=
      Finset.inter_subset_inter (divUpperWindow_subset_divWindow a m 0) (Finset.Subset.refl _)
    have hcard : (divUpperWindow a m 0 ∩ descentFinset f X).card ≤
        (divWindow a m 0 ∩ descentFinset f X).card := Finset.card_le_card hsub
    have hmul_card : D * ((divUpperWindow a m 0 ∩ descentFinset f X).card : ℝ) ≤
        D * ((divWindow a m 0 ∩ descentFinset f X).card : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hD0
    have hsum_eq : (∑ j ∈ Finset.range (s + 1), ((divWindow a m j ∩ descentFinset f X).card : ℝ)) =
        (∑ j ∈ Finset.range s, ((divWindow a (m / a) j ∩ descentFinset f X).card : ℝ)) +
        ((divWindow a m 0 ∩ descentFinset f X).card : ℝ) := by
      rw [Finset.sum_range_succ']
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [divWindow_succ_eq]
    rw [hpow_eq, hsum_eq]
    push_cast
    linarith

/-- **Window-Localized Iterated Division Upper Bound on `f m`**:
Under `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`), for `1 ≤ a`, `1 ≤ s`, `1 ≤ m`, and
`a * (m / a + 1) ≤ X + 1`:
`f m ≤ f (m / a ^ s + 1) + (s : ℝ) * f a + D * (∑ j ∈ Finset.range s, ((divWindow a m j ∩ descentFinset f X).card : ℝ))`. -/
theorem completely_additive_iterated_div_window_upper_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {a s m : ℕ} (ha : 1 ≤ a) (hs : 1 ≤ s) (hm : 1 ≤ m) (hX : a * (m / a + 1) ≤ X + 1) :
    f m ≤ f (m / a ^ s + 1) + (s : ℝ) * f a +
      D * (∑ j ∈ Finset.range s, ((divWindow a m j ∩ descentFinset f X).card : ℝ)) := by
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_comm 1 s']
  have hpow_eq : m / a ^ (s' + 1) = (m / a) / a ^ s' := by
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
  have hX_div : a * ((m / a) / a + 1) ≤ X + 1 := by
    have hdiv_le : (m / a) / a ≤ m / a := Nat.div_le_self (m / a) a
    have hmul_le : a * ((m / a) / a + 1) ≤ a * (m / a + 1) :=
      Nat.mul_le_mul_left a (Nat.add_le_add_right hdiv_le 1)
    exact le_trans hmul_le hX
  have h_tail := completely_additive_iterated_div_succ_window_upper_bound
    hmul hD0 hD ha s' hX_div
  have h_first := completely_additive_div_step_full_window_upper_bound
    hmul hD0 hD ha hm hX
  have hsum_eq : (∑ j ∈ Finset.range (s' + 1), ((divWindow a m j ∩ descentFinset f X).card : ℝ)) =
      (∑ j ∈ Finset.range s', ((divWindow a (m / a) j ∩ descentFinset f X).card : ℝ)) +
      ((divWindow a m 0 ∩ descentFinset f X).card : ℝ) := by
    rw [Finset.sum_range_succ']
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [divWindow_succ_eq]
  rw [hpow_eq, hsum_eq]
  push_cast
  linarith

/-- **Base-`2` Normalized Trajectory Two-Sided Squeeze**:
For any completely additive function `f` with `f 1 = 0` and `HasPrefixBoundedDownwardJumps f X D`
(`0 ≤ D`), if `1 ≤ s`, `2 ^ s ≤ m < 2 ^ (s + 1)`, and `2 * (m / 2 + 1) ≤ X + 1`, then
`m / 2 ^ s = 1` and:
`(s : ℝ) * f 2 - D * (∑ j ∈ Finset.range s, ((divWindow 2 m j ∩ descentFinset f X).card : ℝ)) ≤ f m ∧`
`f m ≤ ((s : ℝ) + 1) * f 2 + D * (∑ j ∈ Finset.range s, ((divWindow 2 m j ∩ descentFinset f X).card : ℝ))`. -/
theorem completely_additive_base_two_normalized_trajectory_bound {f : ℕ → ℝ} (h1 : f 1 = 0)
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {s m : ℕ} (hs : 1 ≤ s) (hlow : 2 ^ s ≤ m) (hhigh : m < 2 ^ (s + 1))
    (hX : 2 * (m / 2 + 1) ≤ X + 1) :
    (s : ℝ) * f 2 -
      D * (∑ j ∈ Finset.range s, ((divWindow 2 m j ∩ descentFinset f X).card : ℝ)) ≤ f m ∧
    f m ≤ ((s : ℝ) + 1) * f 2 +
      D * (∑ j ∈ Finset.range s, ((divWindow 2 m j ∩ descentFinset f X).card : ℝ)) := by
  have hpow_pos : 0 < 2 ^ s := pow_pos (by omega) s
  have hq_ge1 : 1 ≤ m / 2 ^ s := (Nat.le_div_iff_mul_le hpow_pos).mpr (by simpa using hlow)
  have hq_lt2 : m / 2 ^ s < 2 := (Nat.div_lt_iff_lt_mul hpow_pos).mpr (by
    have h2 : 2 * 2 ^ s = 2 ^ (s + 1) := by rw [pow_succ']
    omega)
  have hq_eq1 : m / 2 ^ s = 1 := by omega
  have hm_ge1 : 1 ≤ m := le_trans (by omega : 1 ≤ 2 ^ s) hlow
  have hm_le_X : m ≤ X + 1 := by
    have hlt := div_pow_lt_mul_succ 2 m 0 (by omega)
    simp only [pow_zero, Nat.div_one, zero_add, pow_one] at hlt
    omega
  have hlb := completely_additive_iterated_div_window_lower_bound
    hmul hD0 hD (by omega : 1 ≤ 2) s hq_ge1 hm_le_X
  have hub := completely_additive_iterated_div_window_upper_bound
    hmul hD0 hD (by omega : 1 ≤ 2) hs hm_ge1 hX
  rw [hq_eq1, h1] at hlb
  rw [hq_eq1] at hub
  change f m ≤ f 2 + (s : ℝ) * f 2 +
    D * (∑ j ∈ Finset.range s, ((divWindow 2 m j ∩ descentFinset f X).card : ℝ)) at hub
  refine ⟨by linarith, by linarith⟩

/-! ## Section 3: Controlled-Descent `Nat.log` Sandwich, Cross-Product Deviation, and Unconditional `o(log X)` Log-Rigidity -/

/-- **Controlled-Descent `Nat.log` Sandwich**:
A two-sided `Nat.log` sandwich for power-additive `f` on a prefix where downward jumps are bounded
by `D ≥ 0`, relating `f (m ^ k)` to `f n` up to the descent weight in the surrounding intervals. -/
theorem controlled_descent_power_additive_log_sandwich {f : ℕ → ℝ} {X : ℕ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (hpow : ∀ b : ℕ, 1 ≤ b → ∀ r : ℕ, f (b ^ r) = (r : ℝ) * f b)
    {m n k : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (_hk : 1 ≤ k)
    (hX : n ^ (Nat.log n (m ^ k) + 1) ≤ X + 1) :
    let r := Nat.log n (m ^ k)
    (r : ℝ) * f n - D * ((Finset.Ico (n ^ r) (m ^ k) ∩ descentFinset f X).card : ℝ) ≤ (k : ℝ) * f m ∧
    (k : ℝ) * f m ≤ ((r : ℝ) + 1) * f n +
      D * ((Finset.Ico (m ^ k) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) ∧
    (r : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ) * Real.log (m : ℝ) ∧
    (k : ℝ) * Real.log (m : ℝ) ≤ ((r : ℝ) + 1) * Real.log (n : ℝ) := by
  intro r
  have hmk_pos : 1 ≤ m ^ k := Nat.one_le_pow k m (by omega)
  have hnr_pos : 1 ≤ n ^ r := Nat.one_le_pow r n (by omega)
  have hlow_nat : n ^ r ≤ m ^ k := Nat.pow_log_le_self n (by omega)
  have hup_nat : m ^ k ≤ n ^ (r + 1) :=
    le_of_lt (Nat.lt_pow_succ_log_self (by omega) (m ^ k))
  have hlow_f := sub_le_mul_card_Ico_inter_descentFinset hD0 hD hnr_pos hlow_nat (le_trans hup_nat hX)
  have hup_f := sub_le_mul_card_Ico_inter_descentFinset hD0 hD hmk_pos hup_nat hX
  rw [hpow n (by omega) r, hpow m (by omega) k] at hlow_f
  rw [hpow m (by omega) k, hpow n (by omega) (r + 1), Nat.cast_add, Nat.cast_one] at hup_f
  have hnr_real_pos : (0 : ℝ) < ((n ^ r : ℕ) : ℝ) := by exact_mod_cast hnr_pos
  have hmk_real_pos : (0 : ℝ) < ((m ^ k : ℕ) : ℝ) := by exact_mod_cast hmk_pos
  have hlow_log : Real.log ((n ^ r : ℕ) : ℝ) ≤ Real.log ((m ^ k : ℕ) : ℝ) :=
    Real.log_le_log hnr_real_pos (by exact_mod_cast hlow_nat)
  have hup_log : Real.log ((m ^ k : ℕ) : ℝ) ≤ Real.log ((n ^ (r + 1) : ℕ) : ℝ) :=
    Real.log_le_log hmk_real_pos (by exact_mod_cast hup_nat)
  push_cast at hlow_log hup_log
  rw [Real.log_pow, Real.log_pow] at hlow_log hup_log
  push_cast at hup_log
  exact ⟨by linarith, by linarith, hlow_log, hup_log⟩

/-- **Controlled-Descent Cross-Product Deviation Inequality**:
Under `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`) and power-additivity, if
`n ^ (Nat.log n (m ^ k) + 1) ≤ X + 1`, then
`|(k : ℝ) * (Real.log (n : ℝ) * f m - Real.log (m : ℝ) * f n)| ≤ Real.log (n : ℝ) * (|f n| + D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ))`. -/
theorem controlled_descent_power_additive_cross_product_bound {f : ℕ → ℝ} {X : ℕ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (hpow : ∀ b : ℕ, 1 ≤ b → ∀ r : ℕ, f (b ^ r) = (r : ℝ) * f b)
    {m n k : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hX : n ^ (Nat.log n (m ^ k) + 1) ≤ X + 1) :
    let r := Nat.log n (m ^ k)
    |(k : ℝ) * (Real.log (n : ℝ) * f m - Real.log (m : ℝ) * f n)| ≤
      Real.log (n : ℝ) *
        (|f n| + D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ)) := by
  intro r
  obtain ⟨hlow_f, hup_f, hlow_log, hup_log⟩ :=
    controlled_descent_power_additive_log_sandwich hD0 hD hpow hm hn hk hX
  have hmk_pos : 1 ≤ m ^ k := Nat.one_le_pow k m (by omega)
  have hlow_nat : n ^ r ≤ m ^ k := Nat.pow_log_le_self n (by omega)
  have hup_nat : m ^ k ≤ n ^ (r + 1) :=
    le_of_lt (Nat.lt_pow_succ_log_self (by omega) (m ^ k))
  have hsplit := card_Ico_inter_add_card_Ico_inter hlow_nat hup_nat (descentFinset f X)
  have hlow_card : ((Finset.Ico (n ^ r) (m ^ k) ∩ descentFinset f X).card : ℝ) ≤
      ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) := by
    exact_mod_cast (Nat.le.intro hsplit)
  have hup_card : ((Finset.Ico (m ^ k) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) ≤
      ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) := by
    have hsplit' : (Finset.Ico (m ^ k) (n ^ (r + 1)) ∩ descentFinset f X).card +
        (Finset.Ico (n ^ r) (m ^ k) ∩ descentFinset f X).card =
        (Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card := by
      rw [add_comm]
      exact hsplit
    exact_mod_cast (Nat.le.intro hsplit')
  have hlow_D : D * ((Finset.Ico (n ^ r) (m ^ k) ∩ descentFinset f X).card : ℝ) ≤
      D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) :=
    mul_le_mul_of_nonneg_left hlow_card hD0
  have hup_D : D * ((Finset.Ico (m ^ k) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) ≤
      D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) :=
    mul_le_mul_of_nonneg_left hup_card hD0
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogn_pos : 0 ≤ Real.log (n : ℝ) := le_of_lt (Real.log_pos hn_gt1)
  have hlogn_ne : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn_gt1)
  have hlog_diff : |(k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)| ≤ Real.log (n : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hfn_mul := mul_le_mul_of_nonneg_left hlog_diff (abs_nonneg (f n))
  rw [← abs_mul] at hfn_mul
  rw [abs_le] at hfn_mul
  have hf_diff : |(k : ℝ) * f m - (r : ℝ) * f n| ≤
      |f n| + D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) := by
    have hfn_le : f n ≤ |f n| := le_abs_self (f n)
    have hfn_neg : -|f n| ≤ f n := neg_abs_le (f n)
    rw [abs_le]
    constructor <;> linarith
  rw [abs_le] at hf_diff
  have h1 := mul_le_mul_of_nonneg_left hf_diff.1 hlogn_pos
  have h2 := mul_le_mul_of_nonneg_left hf_diff.2 hlogn_pos
  -- Even sharper: notice that in `(k * f m - r * f n) * log n - f n * (k * log m - r * log n)`,
  -- when `0 ≤ k * log m - r * log n ≤ log n`, the `f n` terms partially cancel!
  have hlog_sub_nonneg : 0 ≤ (k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ) := by linarith
  have hlog_sub_le : (k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ) ≤ Real.log (n : ℝ) := by
    linarith
  have hid : (k : ℝ) * (Real.log (n : ℝ) * f m - Real.log (m : ℝ) * f n) =
      Real.log (n : ℝ) * ((k : ℝ) * f m - (r : ℝ) * f n) -
      f n * ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) := by ring
  have hlow_f' : -D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) ≤
      (k : ℝ) * f m - (r : ℝ) * f n := by linarith
  have hup_f' : (k : ℝ) * f m - (r : ℝ) * f n ≤
      f n + D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ) := by linarith
  have hlow_mul := mul_le_mul_of_nonneg_left hlow_f' hlogn_pos
  have hup_mul := mul_le_mul_of_nonneg_left hup_f' hlogn_pos
  have hfn_abs1 : -(|f n| * Real.log (n : ℝ)) ≤
      f n * ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) := by
    have hneg : -|f n| ≤ f n := neg_abs_le (f n)
    have hm1 := mul_le_mul_of_nonneg_right hneg hlog_sub_nonneg
    have hm2 := mul_le_mul_of_nonneg_left hlog_sub_le (abs_nonneg (f n))
    linarith
  have hfn_abs2 : f n * ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) -
      Real.log (n : ℝ) * f n ≤ |f n| * Real.log (n : ℝ) := by
    have hrem : f n * ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) -
        Real.log (n : ℝ) * f n =
        (-f n) * (Real.log (n : ℝ) - ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ))) := by
      ring
    rw [hrem]
    have hrem_nonneg : 0 ≤ Real.log (n : ℝ) -
        ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) := by linarith
    have hrem_le : Real.log (n : ℝ) -
        ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by linarith
    have hneg_le : -f n ≤ |f n| := neg_le_abs (f n)
    have hm1 := mul_le_mul_of_nonneg_right hneg_le hrem_nonneg
    have hm2 := mul_le_mul_of_nonneg_left hrem_le (abs_nonneg (f n))
    linarith
  have hfn_abs3 : Real.log (n : ℝ) * f n -
      f n * ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) ≤
      |f n| * Real.log (n : ℝ) := by
    have hrem : Real.log (n : ℝ) * f n -
        f n * ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) =
        f n * (Real.log (n : ℝ) - ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ))) := by
      ring
    rw [hrem]
    have hrem_nonneg : 0 ≤ Real.log (n : ℝ) -
        ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) := by linarith
    have hrem_le : Real.log (n : ℝ) -
        ((k : ℝ) * Real.log (m : ℝ) - (r : ℝ) * Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by linarith
    have hpos_le : f n ≤ |f n| := le_abs_self (f n)
    have hm1 := mul_le_mul_of_nonneg_right hpos_le hrem_nonneg
    have hm2 := mul_le_mul_of_nonneg_left hrem_le (abs_nonneg (f n))
    linarith
  rw [hid, abs_le]
  constructor <;> linarith

/-- **Controlled-Descent Quantitative Logarithmic Ratio Squeeze**:
Under `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`) and power-additivity, if
`n ^ (Nat.log n (m ^ k) + 1) ≤ X + 1`, then
`|f m / Real.log (m : ℝ) - f n / Real.log (n : ℝ)| ≤ (|f n| + D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ)) / ((k : ℝ) * Real.log (m : ℝ))`. -/
theorem controlled_descent_power_additive_log_ratio_diff_bound {f : ℕ → ℝ} {X : ℕ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (hpow : ∀ b : ℕ, 1 ≤ b → ∀ r : ℕ, f (b ^ r) = (r : ℝ) * f b)
    {m n : ℕ} (k : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hX : n ^ (Nat.log n (m ^ k) + 1) ≤ X + 1) :
    let r := Nat.log n (m ^ k)
    |f m / Real.log (m : ℝ) - f n / Real.log (n : ℝ)| ≤
      (|f n| + D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ)) /
        ((k : ℝ) * Real.log (m : ℝ)) := by
  intro r
  have hcross := controlled_descent_power_additive_cross_product_bound hD0 hD hpow hm hn hk hX
  have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm_gt1
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hden_pos : 0 < (k : ℝ) * Real.log (m : ℝ) * Real.log (n : ℝ) := by positivity
  have hlogm_ne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlogm_pos
  have hlogn_ne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hlogn_pos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hdiv := div_le_div_of_nonneg_right hcross (le_of_lt hden_pos)
  have hlhs : |(k : ℝ) * (Real.log (n : ℝ) * f m - Real.log (m : ℝ) * f n)| /
      ((k : ℝ) * Real.log (m : ℝ) * Real.log (n : ℝ)) =
      |f m / Real.log (m : ℝ) - f n / Real.log (n : ℝ)| := by
    rw [← abs_of_pos hden_pos, ← abs_div]
    congr 1
    field_simp
  have hrhs : (Real.log (n : ℝ) *
      (|f n| + D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ))) /
      ((k : ℝ) * Real.log (m : ℝ) * Real.log (n : ℝ)) =
      (|f n| + D * ((Finset.Ico (n ^ r) (n ^ (r + 1)) ∩ descentFinset f X).card : ℝ)) /
        ((k : ℝ) * Real.log (m : ℝ)) := by
    field_simp
  linarith

/-- **Global Prefix-Descent Logarithmic Ratio Squeeze**:
Relaxes the window descent count in `controlled_descent_power_additive_log_ratio_diff_bound` to
`descentCount f X`. -/
theorem controlled_descent_log_ratio_diff_le_descentCount {f : ℕ → ℝ} {X : ℕ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (hpow : ∀ b : ℕ, 1 ≤ b → ∀ r : ℕ, f (b ^ r) = (r : ℝ) * f b)
    {m n : ℕ} (k : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hX : n ^ (Nat.log n (m ^ k) + 1) ≤ X + 1) :
    |f m / Real.log (m : ℝ) - f n / Real.log (n : ℝ)| ≤
      (|f n| + D * (descentCount f X : ℝ)) / ((k : ℝ) * Real.log (m : ℝ)) := by
  have hwin := controlled_descent_power_additive_log_ratio_diff_bound hD0 hD hpow k hm hn hk hX
  have hcard : (Finset.Ico (n ^ Nat.log n (m ^ k)) (n ^ (Nat.log n (m ^ k) + 1)) ∩ descentFinset f X).card ≤
      descentCount f X :=
    Finset.card_le_card Finset.inter_subset_right
  have hmul : D * ((Finset.Ico (n ^ Nat.log n (m ^ k)) (n ^ (Nat.log n (m ^ k) + 1)) ∩ descentFinset f X).card : ℝ) ≤
      D * (descentCount f X : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hD0
  have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm_gt1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hden_pos : 0 ≤ (k : ℝ) * Real.log (m : ℝ) := by positivity
  have hnum_le : |f n| + D * ((Finset.Ico (n ^ Nat.log n (m ^ k)) (n ^ (Nat.log n (m ^ k) + 1)) ∩
      descentFinset f X).card : ℝ) ≤ |f n| + D * (descentCount f X : ℝ) := by linarith
  have hdiv := div_le_div_of_nonneg_right hnum_le hden_pos
  exact le_trans hwin hdiv

/-- **Unconditional Sub-Logarithmic Descent Log-Rigidity Theorem**:
If `f : ℕ → ℝ` is coprime-additive, satisfies `HasBoundedDownwardJumps f D`, and its descent count
satisfies `descentCount f X = o(log X)` (together with `descentCount f X = o(X)`), then
`f m = (f 2 / Real.log 2) * Real.log m` for all `m ≥ 1`, and hence `IsScaledLogOnPos f`. -/
theorem sublogarithmic_descentCount_eq_scaled_log_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f) {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    (ho_lin : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    (ho_log : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop]
      (fun X : ℕ => Real.log (X : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by
  have h1 : f 1 = 0 := coprime_additive_one hf
  have hpow : ∀ b : ℕ, 1 ≤ b → ∀ r : ℕ, f (b ^ r) = (r : ℝ) * f b :=
    fun _ hb r => coprime_additive_pow_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho_lin hD hb r
  set Dpos : ℝ := max D 0
  have hDpos0 : 0 ≤ Dpos := le_max_right D 0
  have hDpos : HasBoundedDownwardJumps f Dpos :=
    hasBoundedDownwardJumps_mono hD (le_max_left D 0)
  have hmain : ∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ) := by
    intro m hm
    rcases eq_or_lt_of_le hm with rfl | hm_gt1
    · simp [h1]
    · have hm2 : 2 ≤ m := hm_gt1
      have hlogm_pos : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      set Δ : ℝ := |f m / Real.log (m : ℝ) - f 2 / Real.log (2 : ℝ)|
      have hΔ_zero : Δ = 0 := by
        by_contra hΔ_ne
        have hΔ_pos : 0 < Δ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hΔ_ne)
        set C : ℝ := 2 * (Dpos + 1)
        have hC_pos : 0 < C := by positivity
        set ε : ℝ := Δ / (2 * C)
        have hε_pos : 0 < ε := by positivity
        have hev := ho_log.bound hε_pos
        rw [Filter.eventually_atTop] at hev
        rcases hev with ⟨X₀, hX₀⟩
        obtain ⟨K₀, hK₀⟩ := exists_nat_gt (2 * (|f 2| + 1) / (Δ * Real.log (m : ℝ)))
        set k : ℕ := K₀ + X₀ + 1
        have hk1 : 1 ≤ k := by omega
        set r : ℕ := Nat.log 2 (m ^ k)
        set X : ℕ := 2 ^ (r + 1)
        have hpref : HasPrefixBoundedDownwardJumps f X Dpos :=
          hasPrefixBoundedDownwardJumps_of_hasBoundedDownwardJumps hDpos X
        have hX_bound : 2 ^ (Nat.log 2 (m ^ k) + 1) ≤ X + 1 := by dsimp [X, r]; omega
        have hratio := controlled_descent_log_ratio_diff_le_descentCount
          hDpos0 hpref hpow k hm2 (by omega : 2 ≤ 2) hk1 hX_bound
        change Δ ≤ (|f 2| + Dpos * (descentCount f X : ℝ)) / ((k : ℝ) * Real.log (m : ℝ)) at hratio
        have hmk_lt_X : m ^ k < X := Nat.lt_pow_succ_log_self (by omega) (m ^ k)
        have hk_lt_X : k < X := by
          have hk_lt_2k : k < 2 ^ k := Nat.lt_two_pow_self
          have h2k_le_mk : 2 ^ k ≤ m ^ k := Nat.pow_le_pow_left hm2 k
          omega
        have hX_ge_X0 : X₀ ≤ X := by omega
        have hnorm := hX₀ X hX_ge_X0
        have hX_gt1 : (1 : ℝ) < (X : ℝ) := by
          have h2 : 2 ≤ X := by
            have hpow_ge : 2 ^ 1 ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
            simpa [X] using hpow_ge
          exact_mod_cast (show 1 < X by omega)
        have hlogX_pos : 0 ≤ Real.log (X : ℝ) := le_of_lt (Real.log_pos hX_gt1)
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hlogX_pos] at hnorm
        have hlogX_eq : Real.log (X : ℝ) = ((r : ℝ) + 1) * Real.log (2 : ℝ) := by
          dsimp [X]
          push_cast
          rw [Real.log_pow]
          push_cast
          ring
        have hr_log : (r : ℝ) * Real.log (2 : ℝ) ≤ (k : ℝ) * Real.log (m : ℝ) :=
          (controlled_descent_power_additive_log_sandwich
            hDpos0 hpref hpow hm2 (by omega : 2 ≤ 2) hk1 hX_bound).2.2.1
        have hlog2_le_m : Real.log (2 : ℝ) ≤ Real.log (m : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
        have hk_ge1_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        have hlog2_le_km : Real.log (2 : ℝ) ≤ (k : ℝ) * Real.log (m : ℝ) := by
          calc Real.log (2 : ℝ) = 1 * Real.log (2 : ℝ) := by ring
            _ ≤ (k : ℝ) * Real.log (m : ℝ) := mul_le_mul hk_ge1_real hlog2_le_m
                (le_of_lt hlog2_pos) (by positivity)
        have hlogX_le : Real.log (X : ℝ) ≤ 2 * ((k : ℝ) * Real.log (m : ℝ)) := by
          rw [hlogX_eq]
          linarith
        have hdesc_le : Dpos * (descentCount f X : ℝ) ≤
            ((k : ℝ) * Real.log (m : ℝ)) * (Δ / 2) := by
          have h1 : Dpos * (descentCount f X : ℝ) ≤ Dpos * (ε * Real.log (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hnorm hDpos0
          have h2 : Dpos * (ε * Real.log (X : ℝ)) ≤
              Dpos * (ε * (2 * ((k : ℝ) * Real.log (m : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ hDpos0
            exact mul_le_mul_of_nonneg_left hlogX_le (le_of_lt hε_pos)
          have h3 : Dpos * (ε * (2 * ((k : ℝ) * Real.log (m : ℝ)))) ≤
              C * ε * ((k : ℝ) * Real.log (m : ℝ)) := by
            dsimp [C]
            have hnonneg : 0 ≤ ε * ((k : ℝ) * Real.log (m : ℝ)) := by positivity
            nlinarith
          have h4 : C * ε * ((k : ℝ) * Real.log (m : ℝ)) =
              ((k : ℝ) * Real.log (m : ℝ)) * (Δ / 2) := by
            dsimp [ε]
            field_simp [ne_of_gt hC_pos]
          linarith
        have hden_pos : 0 < (k : ℝ) * Real.log (m : ℝ) := by positivity
        have hmul_ratio : Δ * ((k : ℝ) * Real.log (m : ℝ)) ≤
            |f 2| + Dpos * (descentCount f X : ℝ) :=
          (le_div_iff₀ hden_pos).mp hratio
        have hk_gt : 2 * (|f 2| + 1) / (Δ * Real.log (m : ℝ)) < (k : ℝ) := by
          have hKk : (K₀ : ℝ) < (k : ℝ) := by dsimp [k]; push_cast; linarith
          exact lt_trans hK₀ hKk
        have hΔm_pos : 0 < Δ * Real.log (m : ℝ) := by positivity
        have hf2_lt : |f 2| + 1 < ((k : ℝ) * Real.log (m : ℝ)) * (Δ / 2) := by
          have h := (div_lt_iff₀ hΔm_pos).mp hk_gt
          linarith
        linarith
      have heq_sub : f m / Real.log (m : ℝ) - f 2 / Real.log (2 : ℝ) = 0 :=
        abs_eq_zero.mp hΔ_zero
      have heq_div : f m / Real.log (m : ℝ) = f 2 / Real.log (2 : ℝ) := by linarith
      have hlogm_ne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlogm_pos
      calc f m = (f m / Real.log (m : ℝ)) * Real.log (m : ℝ) := by
            rw [div_mul_cancel₀ (f m) hlogm_ne]
        _ = (f 2 / Real.log (2 : ℝ)) * Real.log (m : ℝ) := by rw [heq_div]
  exact ⟨hmain, ⟨f 2 / Real.log 2, hmain⟩⟩

/-! ## Section 4: Shifted Division-Window Disjointness and Zero-Descent Trajectory Existence Under `descentCount f X = o(X)` -/

/-- Total number of descents across the `s`-step base-`a` division trajectory `divWindow a m 0, ..., divWindow a m (s - 1)`. -/
def trajDescentCount (f : ℕ → ℝ) (X a m s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range s, (divWindow a m j ∩ descentFinset f X).card

/-- **Base-`2` Normalized Trajectory Absolute Deviation Bound**:
For any completely additive function `f` with `f 1 = 0` and `HasPrefixBoundedDownwardJumps f X D`
(`0 ≤ D`), if `1 ≤ s`, `2 ^ s ≤ m < 2 ^ (s + 1)`, and `2 * (m / 2 + 1) ≤ X + 1`, then
`|f m - (s : ℝ) * f 2| ≤ |f 2| + D * (trajDescentCount f X 2 m s : ℝ)`. -/
theorem base_two_normalized_trajectory_abs_defect_bound {f : ℕ → ℝ} (h1 : f 1 = 0)
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {s m : ℕ} (hs : 1 ≤ s) (hlow : 2 ^ s ≤ m) (hhigh : m < 2 ^ (s + 1))
    (hX : 2 * (m / 2 + 1) ≤ X + 1) :
    |f m - (s : ℝ) * f 2| ≤ |f 2| + D * (trajDescentCount f X 2 m s : ℝ) := by
  obtain ⟨hlb, hub⟩ := completely_additive_base_two_normalized_trajectory_bound
    h1 hmul hD0 hD hs hlow hhigh hX
  have hcast : (∑ j ∈ Finset.range s, ((divWindow 2 m j ∩ descentFinset f X).card : ℝ)) =
      (trajDescentCount f X 2 m s : ℝ) := by
    dsimp [trajDescentCount]
    push_cast
    rfl
  rw [hcast] at hlb hub
  have hf2_le : f 2 ≤ |f 2| := le_abs_self (f 2)
  have hf2_nonneg : 0 ≤ |f 2| := abs_nonneg (f 2)
  rw [abs_le]
  constructor <;> linarith

/-- **Trajectory-Sublinear Descent Log-Rigidity Theorem**:
If `IsCoprimeAdditive f`, `descentCount f X = o(X)`, `HasBoundedDownwardJumps f D`, and for every
`b ≥ 2` the base-`2` trajectory descent count along `b ^ k` is `o(k)` as `k → ∞`, then
`f m = (f 2 / Real.log 2) * Real.log m` for all `m ≥ 1`, and hence `IsScaledLogOnPos f`. -/
theorem trajectory_sublinear_descent_eq_scaled_log_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    (htraj : ∀ b : ℕ, 2 ≤ b →
      (fun k : ℕ => (trajDescentCount f (2 * ((b ^ k) / 2 + 1)) 2 (b ^ k) (Nat.log 2 (b ^ k)) : ℝ))
        =o[Filter.atTop] (fun k : ℕ => (k : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by
  have h1 : f 1 = 0 := coprime_additive_one hf
  have hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y :=
    fun x hx y hy => coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD hx hy
  have hpow : ∀ m ≥ 1, ∀ r : ℕ, f (m ^ r) = (r : ℝ) * f m :=
    fun m hm r => coprime_additive_pow_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD hm r
  set Dpos : ℝ := max D 0
  have hDpos0 : 0 ≤ Dpos := le_max_right D 0
  have hDpos : HasBoundedDownwardJumps f Dpos :=
    hasBoundedDownwardJumps_mono hD (le_max_left D 0)
  have hmain : ∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ) := by
    intro b hb
    rcases eq_or_lt_of_le hb with rfl | hb_gt1
    · simp [h1]
    · have hb2 : 2 ≤ b := hb_gt1
      have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      set Δ : ℝ := |Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2|
      have hΔ_zero : Δ = 0 := by
        by_contra hΔ_ne
        have hΔ_pos : 0 < Δ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hΔ_ne)
        set C : ℝ := Real.log (2 : ℝ) * (Dpos + 1)
        have hC_pos : 0 < C := by positivity
        set ε : ℝ := Δ / (2 * C)
        have hε_pos : 0 < ε := by positivity
        have hev := (htraj b hb2).bound hε_pos
        rw [Filter.eventually_atTop] at hev
        rcases hev with ⟨K₁, hK₁⟩
        set A₀ : ℝ := 2 * |f 2| * Real.log (2 : ℝ) + 1
        obtain ⟨K₀, hK₀⟩ := exists_nat_gt (2 * A₀ / Δ)
        set k : ℕ := K₀ + K₁ + 1
        have hk1 : 1 ≤ k := by omega
        set m : ℕ := b ^ k
        set s : ℕ := Nat.log 2 m
        set X : ℕ := 2 * (m / 2 + 1)
        have hm_ge2 : 2 ≤ m := by
          calc 2 = 2 ^ 1 := by ring
            _ ≤ b ^ 1 := Nat.pow_le_pow_left hb2 1
            _ ≤ b ^ k := Nat.pow_le_pow_right (by omega) hk1
        have hs_ge1 : 1 ≤ s := Nat.log_pos (by omega) hm_ge2
        have hlow : 2 ^ s ≤ m := Nat.pow_log_le_self 2 (by omega)
        have hhigh : m < 2 ^ (s + 1) := Nat.lt_pow_succ_log_self (by omega) m
        have hpref : HasPrefixBoundedDownwardJumps f X Dpos :=
          hasPrefixBoundedDownwardJumps_of_hasBoundedDownwardJumps hDpos X
        have htraj_bound := base_two_normalized_trajectory_abs_defect_bound
          h1 hmul hDpos0 hpref hs_ge1 hlow hhigh (by dsimp [X]; omega)
        rw [hpow b (by omega) k] at htraj_bound
        have h2s_pos : 1 ≤ 2 ^ s := Nat.one_le_pow s 2 (by omega)
        have hbk_pos : 1 ≤ m := by omega
        have h2s_real_pos : (0 : ℝ) < ((2 ^ s : ℕ) : ℝ) := by exact_mod_cast h2s_pos
        have hbk_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hbk_pos
        have hlow_log : (s : ℝ) * Real.log (2 : ℝ) ≤ (k : ℝ) * Real.log (b : ℝ) := by
          have h := Real.log_le_log h2s_real_pos
            (show ((2 ^ s : ℕ) : ℝ) ≤ ((b ^ k : ℕ) : ℝ) by exact_mod_cast hlow)
          push_cast at h
          rw [Real.log_pow, Real.log_pow] at h
          exact h
        have hup_log : (k : ℝ) * Real.log (b : ℝ) ≤ ((s : ℝ) + 1) * Real.log (2 : ℝ) := by
          have h := Real.log_le_log hbk_real_pos
            (show ((b ^ k : ℕ) : ℝ) ≤ ((2 ^ (s + 1) : ℕ) : ℝ) by exact_mod_cast (le_of_lt hhigh))
          dsimp [m] at h
          push_cast at h
          rw [Real.log_pow, Real.log_pow] at h
          push_cast at h
          exact h
        have hlog_abs : |(k : ℝ) * Real.log (b : ℝ) - (s : ℝ) * Real.log (2 : ℝ)| ≤
            Real.log (2 : ℝ) := by
          rw [abs_le]
          constructor <;> linarith
        have hf2_mul := mul_le_mul_of_nonneg_left hlog_abs (abs_nonneg (f 2))
        rw [← abs_mul] at hf2_mul
        rw [abs_le] at hf2_mul htraj_bound
        have h1_mul := mul_le_mul_of_nonneg_left htraj_bound.1 (le_of_lt hlog2_pos)
        have h2_mul := mul_le_mul_of_nonneg_left htraj_bound.2 (le_of_lt hlog2_pos)
        have hid : (k : ℝ) * (Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2) =
            Real.log (2 : ℝ) * ((k : ℝ) * f b - (s : ℝ) * f 2) -
            f 2 * ((k : ℝ) * Real.log (b : ℝ) - (s : ℝ) * Real.log (2 : ℝ)) := by ring
        have hcross : |(k : ℝ) * (Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2)| ≤
            A₀ + Real.log (2 : ℝ) * Dpos * (trajDescentCount f X 2 m s : ℝ) := by
          dsimp [A₀]
          rw [hid, abs_le]
          constructor <;> linarith
        have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
        rw [abs_mul, abs_of_pos hk_pos] at hcross
        change (k : ℝ) * Δ ≤ A₀ + Real.log (2 : ℝ) * Dpos * (trajDescentCount f X 2 m s : ℝ) at hcross
        have hnorm := hK₁ k (by omega)
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hnorm
        change (trajDescentCount f X 2 m s : ℝ) ≤ ε * (k : ℝ) at hnorm
        have hdesc_le : Real.log (2 : ℝ) * Dpos * (trajDescentCount f X 2 m s : ℝ) ≤
            (k : ℝ) * (Δ / 2) := by
          have h1 : Real.log (2 : ℝ) * Dpos * (trajDescentCount f X 2 m s : ℝ) ≤
              Real.log (2 : ℝ) * Dpos * (ε * (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hnorm (by positivity)
          have h2 : Real.log (2 : ℝ) * Dpos * (ε * (k : ℝ)) ≤ C * ε * (k : ℝ) := by
            dsimp [C]
            have hnonneg : 0 ≤ Real.log (2 : ℝ) * (ε * (k : ℝ)) := by positivity
            nlinarith
          have h3 : C * ε * (k : ℝ) = (k : ℝ) * (Δ / 2) := by
            dsimp [ε]
            field_simp [ne_of_gt hC_pos]
          linarith
        have hlt_k : 2 * A₀ / Δ < (k : ℝ) := by
          have hKk : (K₀ : ℝ) < (k : ℝ) := by dsimp [k]; push_cast; linarith
          exact lt_trans hK₀ hKk
        have hA0_lt : A₀ < (k : ℝ) * (Δ / 2) := by
          have h := (div_lt_iff₀ hΔ_pos).mp hlt_k
          linarith
        linarith
      have heq_sub : Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2 = 0 :=
        abs_eq_zero.mp hΔ_zero
      have heq_mul : Real.log (2 : ℝ) * f b = f 2 * Real.log (b : ℝ) := by linarith
      calc f b = (Real.log (2 : ℝ) * f b) / Real.log (2 : ℝ) := by
            rw [mul_div_cancel_left₀ (f b) hlog2_ne]
        _ = (f 2 * Real.log (b : ℝ)) / Real.log (2 : ℝ) := by rw [heq_mul]
        _ = (f 2 / Real.log (2 : ℝ)) * Real.log (b : ℝ) := by ring
  exact ⟨hmain, ⟨f 2 / Real.log 2, hmain⟩⟩

/-- For `1 ≤ q ≤ m` and `u₁ < u₂`, `(u₁ * m) / q + 1 ≤ (u₂ * m) / q`. -/
theorem shifted_div_quotient_strict_mono {q m u₁ u₂ : ℕ} (hq : 1 ≤ q) (hm : q ≤ m)
    (hu : u₁ < u₂) :
    (u₁ * m) / q + 1 ≤ (u₂ * m) / q := by
  have hle : u₁ * m + q ≤ u₂ * m := by
    calc u₁ * m + q ≤ u₁ * m + m := Nat.add_le_add_left hm (u₁ * m)
      _ = (u₁ + 1) * m := by ring
      _ ≤ u₂ * m := Nat.mul_le_mul_right m hu
  have hdiv := Nat.div_le_div_right hle (c := q)
  rwa [Nat.add_div_right (u₁ * m) hq] at hdiv

/-- For `1 ≤ a`, `a ^ (j + 1) ≤ m`, and `u₁ < u₂`, the upper endpoint of `divWindow a (u₁ * m) j`
never exceeds the lower endpoint of `divWindow a (u₂ * m) j`. -/
theorem shifted_divWindow_upper_le_lower_of_lt {a m j u₁ u₂ : ℕ} (ha : 1 ≤ a)
    (hm : a ^ (j + 1) ≤ m) (hu : u₁ < u₂) :
    a * ((u₁ * m) / a ^ (j + 1) + 1) ≤ a * ((u₂ * m) / a ^ (j + 1)) := by
  have hq : 1 ≤ a ^ (j + 1) := Nat.one_le_pow (j + 1) a ha
  exact Nat.mul_le_mul_left a (shifted_div_quotient_strict_mono hq hm hu)

/-- **Disjointness of Shifted Division Windows at Level `j`**:
For `1 ≤ a`, `a ^ (j + 1) ≤ m`, and `u₁ ≠ u₂`, `divWindow a (u₁ * m) j` and `divWindow a (u₂ * m) j`
are disjoint. -/
theorem disjoint_shifted_divWindow_of_ne {a m j u₁ u₂ : ℕ} (ha : 1 ≤ a)
    (hm : a ^ (j + 1) ≤ m) (hne : u₁ ≠ u₂) :
    Disjoint (divWindow a (u₁ * m) j) (divWindow a (u₂ * m) j) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hord := shifted_divWindow_upper_le_lower_of_lt ha hm hlt
    change Disjoint (Finset.Ico (a * ((u₁ * m) / a ^ (j + 1))) (a * ((u₁ * m) / a ^ (j + 1) + 1)))
      (Finset.Ico (a * ((u₂ * m) / a ^ (j + 1))) (a * ((u₂ * m) / a ^ (j + 1) + 1)))
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    have h1 := (Finset.mem_Ico.mp hn1).2
    have h2 := (Finset.mem_Ico.mp hn2).1
    omega
  · have hord := shifted_divWindow_upper_le_lower_of_lt ha hm hgt
    change Disjoint (Finset.Ico (a * ((u₁ * m) / a ^ (j + 1))) (a * ((u₁ * m) / a ^ (j + 1) + 1)))
      (Finset.Ico (a * ((u₂ * m) / a ^ (j + 1))) (a * ((u₂ * m) / a ^ (j + 1) + 1)))
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    have h1 := (Finset.mem_Ico.mp hn1).1
    have h2 := (Finset.mem_Ico.mp hn2).2
    omega

/-- **Pairwise Disjointness of Shifted Division Windows**:
For `1 ≤ a`, `a ^ (j + 1) ≤ m`, and any shift set `S : Set ℕ`, `fun u => divWindow a (u * m) j`
is pairwise disjoint on `S`. -/
theorem pairwiseDisjoint_shifted_divWindow {a m j : ℕ} (ha : 1 ≤ a)
    (hm : a ^ (j + 1) ≤ m) (S : Set ℕ) :
    S.PairwiseDisjoint (fun u => divWindow a (u * m) j) :=
  fun _ _ _ _ hne => disjoint_shifted_divWindow_of_ne ha hm hne

/-- **Single-Level Shifted Division-Window Descent Sum Bound**:
For `1 ≤ a`, `a ^ (j + 1) ≤ m`, and any `S : Finset ℕ`:
`∑ u ∈ S, (divWindow a (u * m) j ∩ descentFinset f X).card ≤ descentCount f X`. -/
theorem sum_shifted_divWindow_inter_le_descentCount (f : ℕ → ℝ) (X : ℕ)
    {a m j : ℕ} (ha : 1 ≤ a) (hm : a ^ (j + 1) ≤ m) (S : Finset ℕ) :
    (∑ u ∈ S, (divWindow a (u * m) j ∩ descentFinset f X).card) ≤ descentCount f X := by
  let W' : ℕ → Finset ℕ := fun u => divWindow a (u * m) j ∩ descentFinset f X
  have hdisj : (S : Set ℕ).PairwiseDisjoint W' := by
    intro u₁ hu₁ u₂ hu₂ hne
    exact (pairwiseDisjoint_shifted_divWindow ha hm S hu₁ hu₂ hne).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hsub : S.biUnion W' ⊆ descentFinset f X := by
    intro n hn
    rcases Finset.mem_biUnion.mp hn with ⟨u, _, hnW⟩
    exact (Finset.mem_inter.mp hnW).2
  calc (∑ u ∈ S, (W' u).card)
    _ = (S.biUnion W').card := (Finset.card_biUnion hdisj).symm
    _ ≤ (descentFinset f X).card := Finset.card_le_card hsub
    _ = descentCount f X := rfl

/-- **Shifted Trajectory Total Descent Sum Bound**:
For `1 ≤ a`, `s : ℕ`, `a ^ s ≤ m`, and any `S : Finset ℕ`:
`∑ u ∈ S, trajDescentCount f X a (u * m) s ≤ s * descentCount f X`. -/
theorem sum_shifted_trajDescentCount_le_mul_descentCount (f : ℕ → ℝ) (X : ℕ)
    {a m s : ℕ} (ha : 1 ≤ a) (hm : a ^ s ≤ m) (S : Finset ℕ) :
    (∑ u ∈ S, trajDescentCount f X a (u * m) s) ≤ s * descentCount f X := by
  dsimp [trajDescentCount]
  rw [Finset.sum_comm]
  calc (∑ j ∈ Finset.range s, ∑ u ∈ S, (divWindow a (u * m) j ∩ descentFinset f X).card)
    _ ≤ ∑ _j ∈ Finset.range s, descentCount f X := by
        apply Finset.sum_le_sum
        intro j hj
        have hj_lt : j < s := Finset.mem_range.mp hj
        have hpow : a ^ (j + 1) ≤ a ^ s := Nat.pow_le_pow_right ha (by omega)
        exact sum_shifted_divWindow_inter_le_descentCount f X ha (le_trans hpow hm) S
    _ = s * descentCount f X := by simp

/-- **Existence of a Zero-Descent Shifted Division Trajectory**:
If `1 ≤ a`, `a ^ s ≤ m`, and `s * descentCount f X < U`, then there exists a shift
`u ∈ Finset.Icc 1 U` whose entire `s`-step division trajectory has zero descents in
`descentFinset f X` (`trajDescentCount f X a (u * m) s = 0`). -/
theorem exists_zero_descent_shifted_div_trajectory_of_mul_descentCount_lt (f : ℕ → ℝ) (X : ℕ)
    {a m s U : ℕ} (ha : 1 ≤ a) (hm : a ^ s ≤ m) (hU : s * descentCount f X < U) :
    ∃ u ∈ Finset.Icc 1 U, trajDescentCount f X a (u * m) s = 0 := by
  by_contra hno
  have hge1 : ∀ u ∈ Finset.Icc 1 U, 1 ≤ trajDescentCount f X a (u * m) s := by
    intro u hu
    by_contra hlt1
    exact hno ⟨u, hu, by omega⟩
  have hsum_ge : U ≤ ∑ u ∈ Finset.Icc 1 U, trajDescentCount f X a (u * m) s := by
    calc U = ∑ _u ∈ Finset.Icc 1 U, 1 := by simp
      _ ≤ ∑ u ∈ Finset.Icc 1 U, trajDescentCount f X a (u * m) s := Finset.sum_le_sum hge1
  have hsum_le := sum_shifted_trajDescentCount_le_mul_descentCount f X ha hm (Finset.Icc 1 U)
  omega

/-- **Multiplicative Shell Inclusion for Shifted Top Quotients**:
For `1 ≤ a`, `a ^ s ≤ m < a ^ (s + 1)`, and `1 ≤ u`, the top quotient `(u * m) / a ^ s` and its
successor `(u * m) / a ^ s + 1` lie in the multiplicative shell `[u, a * u]`:
`u ≤ (u * m) / a ^ s ∧ (u * m) / a ^ s + 1 ≤ a * u`. -/
theorem shifted_top_quotient_in_multiplicative_shell {a s m u : ℕ} (ha : 1 ≤ a)
    (hlow : a ^ s ≤ m) (hhigh : m < a ^ (s + 1)) (hu : 1 ≤ u) :
    u ≤ (u * m) / a ^ s ∧ (u * m) / a ^ s + 1 ≤ a * u := by
  have hpow_pos : 0 < a ^ s := pow_pos ha s
  have h1 : u * a ^ s ≤ u * m := Nat.mul_le_mul_left u hlow
  have hq_ge : u ≤ (u * m) / a ^ s := (Nat.le_div_iff_mul_le hpow_pos).mpr h1
  have h2 : u * m < a * u * a ^ s := by
    have hmul_lt : u * m < u * a ^ (s + 1) := Nat.mul_lt_mul_of_pos_left hhigh hu
    have hring : u * a ^ (s + 1) = a * u * a ^ s := by rw [pow_succ]; ring
    omega
  have hq_lt : (u * m) / a ^ s < a * u := (Nat.div_lt_iff_lt_mul hpow_pos).mpr h2
  exact ⟨hq_ge, by omega⟩

/-- **Exact Zero-Descent Shifted Division Sandwich**:
For any completely additive function `f` with `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`),
if `1 ≤ a`, `1 ≤ s`, `a ^ s ≤ m`, `1 ≤ u`, `a * ((u * m) / a + 1) ≤ X + 1`, and
`trajDescentCount f X a (u * m) s = 0`, then:
`f ((u * m) / a ^ s) - f u + (s : ℝ) * f a ≤ f m ∧`
`f m ≤ f ((u * m) / a ^ s + 1) - f u + (s : ℝ) * f a`. -/
theorem zero_descent_shifted_div_sandwich {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {a s m u : ℕ} (ha : 1 ≤ a) (hs : 1 ≤ s) (hlow : a ^ s ≤ m) (hu : 1 ≤ u)
    (hX : a * ((u * m) / a + 1) ≤ X + 1)
    (hzero : trajDescentCount f X a (u * m) s = 0) :
    f ((u * m) / a ^ s) - f u + (s : ℝ) * f a ≤ f m ∧
    f m ≤ f ((u * m) / a ^ s + 1) - f u + (s : ℝ) * f a := by
  have hpow_pos : 0 < a ^ s := pow_pos ha s
  have hm_ge1 : 1 ≤ m := le_trans hpow_pos hlow
  have hum_ge1 : 1 ≤ u * m := Nat.mul_pos hu hm_ge1
  have hq_ge1 : 1 ≤ (u * m) / a ^ s := by
    have h1 : 1 * a ^ s ≤ u * m := by
      calc 1 * a ^ s ≤ u * a ^ s := Nat.mul_le_mul_right (a ^ s) hu
        _ ≤ u * m := Nat.mul_le_mul_left u hlow
    exact (Nat.le_div_iff_mul_le hpow_pos).mpr h1
  have hum_le_X : u * m ≤ X + 1 := by
    have hlt := div_pow_lt_mul_succ a (u * m) 0 ha
    simp only [pow_zero, Nat.div_one, zero_add, pow_one] at hlt
    omega
  have hlb := completely_additive_iterated_div_window_lower_bound
    hmul hD0 hD ha s hq_ge1 hum_le_X
  have hub := completely_additive_iterated_div_window_upper_bound
    hmul hD0 hD ha hs hum_ge1 hX
  have hsum_zero : (∑ j ∈ Finset.range s, ((divWindow a (u * m) j ∩ descentFinset f X).card : ℝ)) = 0 := by
    rw [← Nat.cast_sum]
    exact_mod_cast hzero
  rw [hsum_zero, mul_zero, sub_zero, hmul u hu m hm_ge1] at hlb
  rw [hsum_zero, mul_zero, add_zero, hmul u hu m hm_ge1] at hub
  exact ⟨by linarith, by linarith⟩

/-! ## Section 5: Dyadic-Shell Oscillation Rigidity Equivalence and Separation Controls -/

/-- Bounded oscillation on dyadic shells `[u, 2 * u]`: for all `u ≥ 1` and `u ≤ q ≤ 2 * u`,
`|f q - f u| ≤ C`. -/
def HasBoundedDyadicShellOscillation (f : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u → |f q - f u| ≤ C

/-- **Uniform Base-`2` Power-Defect Bound Under Bounded Dyadic-Shell Oscillation**:
If `IsCoprimeAdditive f`, `descentCount f X = o(X)`, `HasBoundedDownwardJumps f D`, and
`HasBoundedDyadicShellOscillation f C`, then for every `b ≥ 2` and `k ≥ 1`, with
`s = Nat.log 2 (b ^ k)`, `|(k : ℝ) * f b - (s : ℝ) * f 2| ≤ C`. -/
theorem dyadic_shell_oscillation_base_two_pow_defect_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D C : ℝ} (hD : HasBoundedDownwardJumps f D) (hC : HasBoundedDyadicShellOscillation f C)
    {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    let s := Nat.log 2 (b ^ k)
    |(k : ℝ) * f b - (s : ℝ) * f 2| ≤ C := by
  intro s
  have hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y :=
    fun x hx y hy => coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD hx hy
  have hpow : ∀ m ≥ 1, ∀ r : ℕ, f (m ^ r) = (r : ℝ) * f m :=
    fun m hm r => coprime_additive_pow_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD hm r
  set Dpos : ℝ := max D 0
  have hDpos0 : 0 ≤ Dpos := le_max_right D 0
  have hDpos : HasBoundedDownwardJumps f Dpos :=
    hasBoundedDownwardJumps_mono hD (le_max_left D 0)
  set m : ℕ := b ^ k
  have hm_ge2 : 2 ≤ m := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ b ^ 1 := Nat.pow_le_pow_left hb 1
      _ ≤ b ^ k := Nat.pow_le_pow_right (by omega) hk
  have hs_ge1 : 1 ≤ s := by
    dsimp [s]
    exact Nat.log_pos (by omega) hm_ge2
  have hlow : 2 ^ s ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hhigh : m < 2 ^ (s + 1) := Nat.lt_pow_succ_log_self (by omega) m
  set M : ℕ := 2 * m + 2
  have hM_pos : 0 < M := by positivity
  set B : ℝ := 2 * ((s + 1 : ℕ) : ℝ) * (M : ℝ)
  have hB_pos : 0 < B := by positivity
  have hε_pos : (0 : ℝ) < 1 / B := div_pos one_pos hB_pos
  have hev := ho.bound hε_pos
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨X₀, hX₀⟩
  set U : ℕ := X₀ + 1
  set X : ℕ := M * U
  have hX_ge_X0 : X₀ ≤ X := by
    have h1 : U ≤ M * U := Nat.le_mul_of_pos_left U hM_pos
    omega
  have hnorm := hX₀ X hX_ge_X0
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hnorm
  have hlt_U : s * descentCount f X < U := by
    by_contra hge_U
    have hU_le : (U : ℝ) ≤ (s : ℝ) * (descentCount f X : ℝ) := by
      exact_mod_cast (not_lt.mp hge_U)
    have hs_le : (s : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 : (U : ℝ) ≤ ((s + 1 : ℕ) : ℝ) * (descentCount f X : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ (descentCount f X : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2 : ((s + 1 : ℕ) : ℝ) * (descentCount f X : ℝ) ≤
        ((s + 1 : ℕ) : ℝ) * ((1 / B) * (X : ℝ)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    have hX_cast : (X : ℝ) = (M : ℝ) * (U : ℝ) := by dsimp [X]; push_cast; ring
    rw [hX_cast] at h2
    have h3 : ((s + 1 : ℕ) : ℝ) * ((1 / B) * ((M : ℝ) * (U : ℝ))) = (U : ℝ) / 2 := by
      dsimp [B]
      field_simp [ne_of_gt hB_pos]
    have hU_pos : (0 : ℝ) < (U : ℝ) := by positivity
    linarith
  obtain ⟨u, huIcc, hzero⟩ :=
    exists_zero_descent_shifted_div_trajectory_of_mul_descentCount_lt
      f X (by omega : 1 ≤ 2) hlow hlt_U
  rcases Finset.mem_Icc.mp huIcc with ⟨hu1, huU⟩
  have hX_u : 2 * ((u * m) / 2 + 1) ≤ X + 1 := by
    have hdiv : 2 * ((u * m) / 2) ≤ u * m := Nat.mul_div_le (u * m) 2
    have hum_le : u * m ≤ U * m := Nat.mul_le_mul_right m huU
    have hMX : U * m + 2 ≤ M * U := by
      dsimp [M]
      have hU1 : 1 ≤ U := by omega
      nlinarith
    dsimp [X]
    omega
  have hpref : HasPrefixBoundedDownwardJumps f X Dpos :=
    hasPrefixBoundedDownwardJumps_of_hasBoundedDownwardJumps hDpos X
  obtain ⟨hlb, hub⟩ := zero_descent_shifted_div_sandwich
    hmul hDpos0 hpref (by omega : 1 ≤ 2) hs_ge1 hlow hu1 hX_u hzero
  obtain ⟨hq_low, hq_high⟩ := shifted_top_quotient_in_multiplicative_shell
    (by omega : 1 ≤ 2) hlow hhigh hu1
  have hosc1 := hC u hu1 ((u * m) / 2 ^ s) hq_low (by omega)
  have hosc2 := hC u hu1 ((u * m) / 2 ^ s + 1) (by omega) hq_high
  rw [abs_le] at hosc1 hosc2 ⊢
  have hfm : f m = (k : ℝ) * f b := hpow b (by omega) k
  rw [hfm] at hlb hub
  constructor <;> linarith

/-- **Dyadic-Shell Oscillation Rigidity Theorem**:
If `IsCoprimeAdditive f`, `descentCount f X = o(X)`, `HasBoundedDownwardJumps f D`, and
`HasBoundedDyadicShellOscillation f C`, then `f m = (f 2 / Real.log 2) * Real.log m` for all
`m ≥ 1`, and hence `IsScaledLogOnPos f`. -/
theorem dyadic_shell_oscillation_eq_scaled_log_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D C : ℝ} (hD : HasBoundedDownwardJumps f D) (hC : HasBoundedDyadicShellOscillation f C) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by
  have h1 : f 1 = 0 := coprime_additive_one hf
  have hC_nonneg : 0 ≤ C := by
    have h0 := hC 1 (le_refl 1) 1 (le_refl 1) (by omega)
    simpa using h0
  have hmain : ∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ) := by
    intro b hb
    rcases eq_or_lt_of_le hb with rfl | hb_gt1
    · simp [h1]
    · have hb2 : 2 ≤ b := hb_gt1
      have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      set Δ : ℝ := |Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2|
      have hΔ_zero : Δ = 0 := by
        by_contra hΔ_ne
        have hΔ_pos : 0 < Δ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hΔ_ne)
        set B : ℝ := Real.log (2 : ℝ) * C + |f 2| * Real.log (2 : ℝ)
        obtain ⟨K₀, hK₀⟩ := exists_nat_gt (B / Δ)
        set k : ℕ := K₀ + 1
        have hk1 : 1 ≤ k := by omega
        set s : ℕ := Nat.log 2 (b ^ k)
        have hdef := dyadic_shell_oscillation_base_two_pow_defect_bound hf ho hD hC hb2 hk1
        change |(k : ℝ) * f b - (s : ℝ) * f 2| ≤ C at hdef
        have hbk_pos : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
        have h2s_pos : 1 ≤ 2 ^ s := Nat.one_le_pow s 2 (by omega)
        have hbk_real_pos : (0 : ℝ) < ((b ^ k : ℕ) : ℝ) := by exact_mod_cast hbk_pos
        have h2s_real_pos : (0 : ℝ) < ((2 ^ s : ℕ) : ℝ) := by exact_mod_cast h2s_pos
        have hlow_nat : 2 ^ s ≤ b ^ k := Nat.pow_log_le_self 2 (by omega)
        have hup_nat : b ^ k ≤ 2 ^ (s + 1) :=
          le_of_lt (Nat.lt_pow_succ_log_self (by omega) (b ^ k))
        have hlow_log : (s : ℝ) * Real.log (2 : ℝ) ≤ (k : ℝ) * Real.log (b : ℝ) := by
          have h := Real.log_le_log h2s_real_pos
            (show ((2 ^ s : ℕ) : ℝ) ≤ ((b ^ k : ℕ) : ℝ) by exact_mod_cast hlow_nat)
          push_cast at h
          rw [Real.log_pow, Real.log_pow] at h
          exact h
        have hup_log : (k : ℝ) * Real.log (b : ℝ) ≤ ((s : ℝ) + 1) * Real.log (2 : ℝ) := by
          have h := Real.log_le_log hbk_real_pos
            (show ((b ^ k : ℕ) : ℝ) ≤ ((2 ^ (s + 1) : ℕ) : ℝ) by exact_mod_cast hup_nat)
          push_cast at h
          rw [Real.log_pow, Real.log_pow] at h
          push_cast at h
          exact h
        have hlog_abs : |(k : ℝ) * Real.log (b : ℝ) - (s : ℝ) * Real.log (2 : ℝ)| ≤
            Real.log (2 : ℝ) := by
          rw [abs_le]
          constructor <;> linarith
        have hf2_mul := mul_le_mul_of_nonneg_left hlog_abs (abs_nonneg (f 2))
        rw [← abs_mul] at hf2_mul
        rw [abs_le] at hf2_mul hdef
        have h1_mul := mul_le_mul_of_nonneg_left hdef.1 (le_of_lt hlog2_pos)
        have h2_mul := mul_le_mul_of_nonneg_left hdef.2 (le_of_lt hlog2_pos)
        have hid : (k : ℝ) * (Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2) =
            Real.log (2 : ℝ) * ((k : ℝ) * f b - (s : ℝ) * f 2) -
            f 2 * ((k : ℝ) * Real.log (b : ℝ) - (s : ℝ) * Real.log (2 : ℝ)) := by ring
        have hcross : |(k : ℝ) * (Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2)| ≤ B := by
          dsimp [B]
          rw [hid, abs_le]
          constructor <;> linarith
        have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
        rw [abs_mul, abs_of_pos hk_pos] at hcross
        change (k : ℝ) * Δ ≤ B at hcross
        have hlt_k : B / Δ < (k : ℝ) := by
          have hKk : (K₀ : ℝ) < (k : ℝ) := by dsimp [k]; push_cast; linarith
          exact lt_trans hK₀ hKk
        have hgt : B < (k : ℝ) * Δ := (div_lt_iff₀ hΔ_pos).mp hlt_k
        linarith
      have heq_sub : Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2 = 0 :=
        abs_eq_zero.mp hΔ_zero
      have heq_mul : Real.log (2 : ℝ) * f b = f 2 * Real.log (b : ℝ) := by linarith
      calc f b = (Real.log (2 : ℝ) * f b) / Real.log (2 : ℝ) := by
            rw [mul_div_cancel_left₀ (f b) hlog2_ne]
        _ = (f 2 * Real.log (b : ℝ)) / Real.log (2 : ℝ) := by rw [heq_mul]
        _ = (f 2 / Real.log (2 : ℝ)) * Real.log (b : ℝ) := by ring
  exact ⟨hmain, ⟨f 2 / Real.log 2, hmain⟩⟩

/-- **Positive Control**: Every scaled logarithm `f(n) = c * Real.log n` satisfies
`HasBoundedDyadicShellOscillation f (|c| * Real.log 2)`. -/
theorem scaled_log_hasBoundedDyadicShellOscillation (c : ℝ) :
    HasBoundedDyadicShellOscillation (fun n : ℕ => c * Real.log (n : ℝ)) (|c| * Real.log (2 : ℝ)) := by
  intro u hu q huq hq2u
  have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (le_trans hu huq)
  have hlog_low : Real.log (u : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hu_pos (by exact_mod_cast huq)
  have hlog_high : Real.log (q : ℝ) ≤ Real.log (2 : ℝ) + Real.log (u : ℝ) := by
    have h := Real.log_le_log hq_pos (show (q : ℝ) ≤ ((2 * u : ℕ) : ℝ) by exact_mod_cast hq2u)
    push_cast at h
    rwa [Real.log_mul (by norm_num) (ne_of_gt hu_pos)] at h
  have hdiff_nonneg : 0 ≤ Real.log (q : ℝ) - Real.log (u : ℝ) := by linarith
  have hdiff_le : Real.log (q : ℝ) - Real.log (u : ℝ) ≤ Real.log (2 : ℝ) := by linarith
  have hfac : c * Real.log (q : ℝ) - c * Real.log (u : ℝ) =
      c * (Real.log (q : ℝ) - Real.log (u : ℝ)) := by ring
  rw [hfac, abs_mul, abs_of_nonneg hdiff_nonneg]
  exact mul_le_mul_of_nonneg_left hdiff_le (abs_nonneg c)

/-- **Exact Dyadic-Shell Oscillation Characterization of `IsScaledLogOnPos`**:
For any coprime-additive function `f : ℕ → ℝ` with `descentCount f X = o(X)` and
`HasBoundedDownwardJumps f D`, `IsScaledLogOnPos f` holds if and only if `f` has bounded
oscillation across dyadic shells `[u, 2 * u]`. -/
theorem isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D) :
    IsScaledLogOnPos f ↔ ∃ C : ℝ, HasBoundedDyadicShellOscillation f C := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨|c| * Real.log (2 : ℝ), ?_⟩
    intro u hu q huq hq2u
    rw [hc q (le_trans hu huq), hc u hu]
    exact scaled_log_hasBoundedDyadicShellOscillation c u hu q huq hq2u
  · rintro ⟨C, hC⟩
    exact (dyadic_shell_oscillation_eq_scaled_log_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
      hf ho hD hC).2

/-- **Top-Down Conditional Reduction for `Erdos1122Conjecture`**:
If every coprime-additive function `f : ℕ → ℝ` with `descentCount f X = o(X)` satisfies
bounded downward jumps and bounded dyadic-shell oscillation, then `Erdos1122Conjecture` holds. -/
theorem erdos1122_conjecture_of_boundedDownwardJumps_and_dyadicShellOscillation
    (hjump : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ D : ℝ, HasBoundedDownwardJumps f D)
    (hshell : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ C : ℝ, HasBoundedDyadicShellOscillation f C) :
    Erdos1122Conjecture := by
  intro f hf ho
  obtain ⟨D, hD⟩ := hjump f hf ho
  obtain ⟨C, hC⟩ := hshell f hf ho
  exact (dyadic_shell_oscillation_eq_scaled_log_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    hf ho hD hC).2

end Erdos1122

end
