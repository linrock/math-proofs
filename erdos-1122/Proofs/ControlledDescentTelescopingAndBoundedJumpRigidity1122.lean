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
# Controlled-Descent `K`-Window Telescoping and Complete Additivity Under Bounded Downward Jumps (Erdős Problem #1122)

This module proves five universal structural results for Erdős Problem #1122:
1. **Bounded Downward Jumps and Interval / Subinterval Descent-Weighted Drift Bounds**:
   Introduces global (`HasBoundedDownwardJumps f D`) and finite-prefix
   (`HasPrefixBoundedDownwardJumps f X D`) downward-jump predicates `f n - f (n + 1) ≤ D`,
   proves that the global predicate implies the prefix one, and proves the
   interval downward-jump bound
   `f u - f v ≤ D * ((Finset.Ico u v ∩ descentFinset f X).card : ℝ)`
   together with single-subinterval and disjoint two-subinterval downward-jump bounds.
2. **Step-Window Decomposition Absorbing Inter-Window Gaps**:
   Defines `sandwichStepWindow a b k = Finset.Ico (sandwichWLow a b k) (sandwichWLow a b (k + 1))`
   and proves the exact non-monotone step-window identities (`coprime_sandwich_step_defect_pos_decomp`
   and `coprime_sandwich_step_defect_neg_decomp`) showing that the inner sandwich window
   `[sandwichWLow a b k, sandwichWHigh a b k)` and the inter-window gap
   `[sandwichWHigh a b k, sandwichWLow a b (k + 1))` combine into disjoint subintervals of a
   single step window `[sandwichWLow a b k, sandwichWLow a b (k + 1))` without double-counting descents.
3. **The Controlled-Descent `K`-Window Telescoping Inequality**:
   Proves the sharp interval-localized `K`-window telescoping bound and the main
   controlled-descent `K`-window telescoping inequality
   `(K : ℝ) * |f (a * b) - f a - f b| ≤ f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) + 2 * D * (descentCount f X : ℝ)`,
   together with a single scale-bound variant.
4. **The Odd Binary Power Sequence (`oddPowTwoSucc`) and Logarithmic Upper Bounds**:
   Defines `oddPowTwoSucc r = 2 ^ (r + 1) + 1`, proves universal coprimality
   `Nat.Coprime 2 (oddPowTwoSucc r)` and the adjacent-step relation
   `oddPowTwoSucc (r + 1) + 1 = 2 * oddPowTwoSucc r`, and establishes the universal logarithmic
   upper bound `f (oddPowTwoSucc r) ≤ f 3 + (r : ℝ) * (f 2 + D)` under `HasBoundedDownwardJumps f D`.
5. **Complete and Power Additivity Under `descentCount f X = o(X)` and Bounded Downward Jumps**:
   Combines the controlled-descent `K`-window telescoping inequality at `K = 2 ^ r` with the
   `oddPowTwoSucc` logarithmic upper bound to prove the quantitative dyadic defect inequality and
   unconditional complete additivity (`f (a * b) = f a + f b`) and power additivity
   (`f (m ^ k) = k * f m`) whenever `descentCount f X = o(X)` and `HasBoundedDownwardJumps f D`.
-/

/-! ## Section 1: Bounded Downward Jumps and Interval Descent-Weighted Drift Bounds -/

/-- Global bounded downward-jump predicate: `f n - f (n + 1) ≤ D` for all `n ≥ 1`. -/
def HasBoundedDownwardJumps (f : ℕ → ℝ) (D : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → f n - f (n + 1) ≤ D

/-- Finite-prefix bounded downward-jump predicate on `descentFinset f X`. -/
def HasPrefixBoundedDownwardJumps (f : ℕ → ℝ) (X : ℕ) (D : ℝ) : Prop :=
  ∀ n ∈ descentFinset f X, f n - f (n + 1) ≤ D

/-- Global bounded downward jumps imply prefix bounded downward jumps on `[1, X]` for all `X : ℕ`. -/
theorem hasPrefixBoundedDownwardJumps_of_hasBoundedDownwardJumps {f : ℕ → ℝ} {D : ℝ}
    (hD : HasBoundedDownwardJumps f D) (X : ℕ) :
    HasPrefixBoundedDownwardJumps f X D := by
  intro n hn
  have h1 : 1 ≤ n := ((mem_descentFinset_iff f X n).mp hn).1.1
  exact hD n h1

/-- Monotonicity of `HasBoundedDownwardJumps` in the jump bound `D`. -/
theorem hasBoundedDownwardJumps_mono {f : ℕ → ℝ} {D₁ D₂ : ℝ}
    (hD : HasBoundedDownwardJumps f D₁) (hle : D₁ ≤ D₂) :
    HasBoundedDownwardJumps f D₂ :=
  fun n hn => le_trans (hD n hn) hle

/-- Additive splitting of intersection cardinalities over adjacent half-open intervals
`Finset.Ico u v` and `Finset.Ico v w` (`u ≤ v ≤ w`). -/
theorem card_Ico_inter_add_card_Ico_inter {u v w : ℕ} (huv : u ≤ v) (hvw : v ≤ w)
    (A : Finset ℕ) :
    (Finset.Ico u v ∩ A).card + (Finset.Ico v w ∩ A).card = (Finset.Ico u w ∩ A).card := by
  have hdisj : Disjoint (Finset.Ico u v ∩ A) (Finset.Ico v w ∩ A) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    have h1 := (Finset.mem_Ico.mp (Finset.mem_inter.mp hn1).1).2
    have h2 := (Finset.mem_Ico.mp (Finset.mem_inter.mp hn2).1).1
    omega
  have hunion : (Finset.Ico u v ∩ A) ∪ (Finset.Ico v w ∩ A) = Finset.Ico u w ∩ A := by
    rw [← Finset.union_inter_distrib_right, Finset.Ico_union_Ico_eq_Ico huv hvw]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- **Fundamental Interval Downward-Jump Bound**:
If `0 ≤ D` and `HasPrefixBoundedDownwardJumps f X D`, then for every integer interval `[u, v)` with
`1 ≤ u ≤ v ≤ X + 1`, the downward drift `f u - f v` is at most `D` times the number of descents of
`f` in `Finset.Ico u v`. -/
theorem sub_le_mul_card_Ico_inter_descentFinset {f : ℕ → ℝ} {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : HasPrefixBoundedDownwardJumps f X D) {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v)
    (hv : v ≤ X + 1) :
    f u - f v ≤ D * ((Finset.Ico u v ∩ descentFinset f X).card : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
  induction d with
  | zero => simp
  | succ d ih =>
    have ih1 : f u - f (u + d) ≤ D * ((Finset.Ico u (u + d) ∩ descentFinset f X).card : ℝ) :=
      ih (by omega) (by omega)
    have hsplit := card_Ico_inter_add_card_Ico_inter (show u ≤ u + d by omega)
      (show u + d ≤ u + (d + 1) by omega) (descentFinset f X)
    have h1 : u + (d + 1) = u + d + 1 := by omega
    rw [h1] at hsplit ⊢
    have hsingle : Finset.Ico (u + d) (u + d + 1) = {u + d} := Nat.Ico_succ_singleton (u + d)
    rw [hsingle] at hsplit
    by_cases hdesc : f (u + d + 1) < f (u + d)
    · have hmem : u + d ∈ descentFinset f X :=
        (mem_descentFinset_iff f X (u + d)).mpr ⟨⟨by omega, hdesc⟩, by omega⟩
      have hcard1 : ({u + d} ∩ descentFinset f X).card = 1 := by
        rw [Finset.singleton_inter_of_mem hmem, Finset.card_singleton]
      rw [hcard1] at hsplit
      have hcast : ((Finset.Ico u (u + d + 1) ∩ descentFinset f X).card : ℝ) =
          ((Finset.Ico u (u + d) ∩ descentFinset f X).card : ℝ) + 1 := by
        exact_mod_cast hsplit.symm
      have hstep : f (u + d) - f (u + d + 1) ≤ D := hD (u + d) hmem
      rw [hcast]
      linarith
    · have hstep : f (u + d) - f (u + d + 1) ≤ 0 := by linarith
      have hle_card : ((Finset.Ico u (u + d) ∩ descentFinset f X).card : ℝ) ≤
          ((Finset.Ico u (u + d + 1) ∩ descentFinset f X).card : ℝ) := by
        exact_mod_cast (Nat.le.intro hsplit)
      have hmul_le : D * ((Finset.Ico u (u + d) ∩ descentFinset f X).card : ℝ) ≤
          D * ((Finset.Ico u (u + d + 1) ∩ descentFinset f X).card : ℝ) :=
        mul_le_mul_of_nonneg_left hle_card hD0
      linarith

/-- **Prefix Global Downward-Jump Bound**:
Under `0 ≤ D` and `HasPrefixBoundedDownwardJumps f X D`, every pair `1 ≤ u ≤ v ≤ X + 1` satisfies
`f u - f v ≤ D * (descentCount f X : ℝ)`. -/
theorem sub_le_mul_descentCount_of_le {f : ℕ → ℝ} {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : HasPrefixBoundedDownwardJumps f X D) {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v)
    (hv : v ≤ X + 1) :
    f u - f v ≤ D * (descentCount f X : ℝ) := by
  have h1 := sub_le_mul_card_Ico_inter_descentFinset hD0 hD hu huv hv
  have hcard : (Finset.Ico u v ∩ descentFinset f X).card ≤ descentCount f X :=
    Finset.card_le_card Finset.inter_subset_right
  have hmul : D * ((Finset.Ico u v ∩ descentFinset f X).card : ℝ) ≤ D * (descentCount f X : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hD0
  linarith

/-- **Single-Subinterval Downward-Jump Bound**:
For any subinterval `[u₁, v₁) ⊆ [u, v)` with `1 ≤ u` and `v ≤ X + 1`,
`f u₁ - f v₁ ≤ D * ((Finset.Ico u v ∩ descentFinset f X).card : ℝ)`. -/
theorem subinterval_sub_le_mul_card_Ico_inter {f : ℕ → ℝ} {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : HasPrefixBoundedDownwardJumps f X D) {u u₁ v₁ v : ℕ}
    (hu : 1 ≤ u) (hu1 : u ≤ u₁) (h1 : u₁ ≤ v₁) (hv1 : v₁ ≤ v) (hv : v ≤ X + 1) :
    f u₁ - f v₁ ≤ D * ((Finset.Ico u v ∩ descentFinset f X).card : ℝ) := by
  have hsub := sub_le_mul_card_Ico_inter_descentFinset hD0 hD (by omega) h1 (by omega)
  have hsub_fin : Finset.Ico u₁ v₁ ∩ descentFinset f X ⊆ Finset.Ico u v ∩ descentFinset f X := by
    intro n hn
    exact Finset.mem_inter.mpr
      ⟨Finset.Ico_subset_Ico hu1 hv1 (Finset.mem_inter.mp hn).1, (Finset.mem_inter.mp hn).2⟩
  have hcard : (Finset.Ico u₁ v₁ ∩ descentFinset f X).card ≤
      (Finset.Ico u v ∩ descentFinset f X).card :=
    Finset.card_le_card hsub_fin
  have hmul : D * ((Finset.Ico u₁ v₁ ∩ descentFinset f X).card : ℝ) ≤
      D * ((Finset.Ico u v ∩ descentFinset f X).card : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hD0
  linarith

/-- **Disjoint Two-Subinterval Downward-Jump Bound**:
For any two ordered disjoint subintervals `[u₁, v₁)` and `[u₂, v₂)` inside `[u, v)`
(`1 ≤ u ≤ u₁ ≤ v₁ ≤ u₂ ≤ v₂ ≤ v ≤ X + 1`),
`(f u₁ - f v₁) + (f u₂ - f v₂) ≤ D * ((Finset.Ico u v ∩ descentFinset f X).card : ℝ)`. -/
theorem disjoint_subintervals_sub_add_sub_le_mul_card_Ico_inter {f : ℕ → ℝ} {X : ℕ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D) {u u₁ v₁ u₂ v₂ v : ℕ}
    (hu : 1 ≤ u) (hu1 : u ≤ u₁) (h1 : u₁ ≤ v₁) (h12 : v₁ ≤ u₂)
    (h2 : u₂ ≤ v₂) (hv2 : v₂ ≤ v) (hv : v ≤ X + 1) :
    (f u₁ - f v₁) + (f u₂ - f v₂) ≤ D * ((Finset.Ico u v ∩ descentFinset f X).card : ℝ) := by
  have hb1 := subinterval_sub_le_mul_card_Ico_inter hD0 hD hu hu1 h1 (le_refl v₁) (by omega)
  have hb2 := subinterval_sub_le_mul_card_Ico_inter hD0 hD (by omega : 1 ≤ v₁) h12 h2 hv2 hv
  have hsplit := card_Ico_inter_add_card_Ico_inter (show u ≤ v₁ by omega) (show v₁ ≤ v by omega)
    (descentFinset f X)
  have hcast : ((Finset.Ico u v₁ ∩ descentFinset f X).card : ℝ) +
      ((Finset.Ico v₁ v ∩ descentFinset f X).card : ℝ) =
      ((Finset.Ico u v ∩ descentFinset f X).card : ℝ) := by
    exact_mod_cast hsplit
  rw [← hcast]
  linarith

/-! ## Section 2: Step-Window Decomposition Absorbing Inter-Window Gaps -/

/-- Full step window `[sandwichWLow a b k, sandwichWLow a b (k + 1))` of length `a * b ^ 2`,
containing both the inner sandwich window `[sandwichWLow a b k, sandwichWHigh a b k)` and the
inter-window gap `[sandwichWHigh a b k, sandwichWLow a b (k + 1))`. -/
def sandwichStepWindow (a b k : ℕ) : Finset ℕ :=
  Finset.Ico (sandwichWLow a b k) (sandwichWLow a b (k + 1))

/-- Monotonicity of `sandwichWLow a b k` in the shift index `k`. -/
theorem sandwichWLow_mono_right (a b : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    sandwichWLow a b k₁ ≤ sandwichWLow a b k₂ := by
  dsimp [sandwichWLow]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (a * b ^ 2) hk) 1

/-- Monotonicity of `sandwichWHigh a b k` in the shift index `k`. -/
theorem sandwichWHigh_mono_right (a b : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    sandwichWHigh a b k₁ ≤ sandwichWHigh a b k₂ := by
  dsimp [sandwichWHigh]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left (a * b ^ 2) hk) (a * b)) 1

/-- **Exact Positive-Sign Step-Window Decomposition**:
Expresses `f (a * b) - f a - f b` as the full step `f (sandwichWLow a b (k + 1)) - f (sandwichWLow a b k)`
plus the two disjoint inner-step drifts `[sandwichWLow a b k, b * sandwichU a b k)` and
`[sandwichWHigh a b k, sandwichWLow a b (k + 1))` and the outer drift
`[a * b * sandwichU a b k, a * sandwichWHigh a b k)`. -/
theorem coprime_sandwich_step_defect_pos_decomp {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ) :
    f (a * b) - f a - f b =
      (f (sandwichWLow a b (k + 1)) - f (sandwichWLow a b k)) +
      (f (sandwichWLow a b k) - f (b * sandwichU a b k)) +
      (f (sandwichWHigh a b k) - f (sandwichWLow a b (k + 1))) +
      (f (a * b * sandwichU a b k) - f (a * sandwichWHigh a b k)) := by
  obtain ⟨_, h2, h3, h4⟩ := coprime_sandwich_double_decomp hf ha hb k
  linarith

/-- **Exact Negative-Sign Step-Window Decomposition**:
Expresses `-(f (a * b) - f a - f b)` as the full step `f (sandwichWLow a b (k + 1)) - f (sandwichWLow a b k)`
plus the single inner-step drift `[b * sandwichU a b k, sandwichWLow a b (k + 1))` and the outer
drift `[a * sandwichWLow a b k, a * b * sandwichU a b k)`. -/
theorem coprime_sandwich_step_defect_neg_decomp {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ) :
    -(f (a * b) - f a - f b) =
      (f (sandwichWLow a b (k + 1)) - f (sandwichWLow a b k)) +
      (f (b * sandwichU a b k) - f (sandwichWLow a b (k + 1))) +
      (f (a * sandwichWLow a b k) - f (a * b * sandwichU a b k)) := by
  obtain ⟨h1, _, h3, h4⟩ := coprime_sandwich_double_decomp hf ha hb k
  linarith

/-- **Step-Window Controlled-Descent Coprime Sandwich Defect Bound**:
Absorbs the inter-window gap `[sandwichWHigh a b k, sandwichWLow a b (k + 1))` into
`sandwichStepWindow a b k` with zero extra descent penalty:
`|f (a * b) - f a - f b| ≤ (f (sandwichWLow a b (k + 1)) - f (sandwichWLow a b k)) + D * (step_descents + outer_descents)`. -/
theorem controlled_descent_step_window_defect_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {X a b k : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hX_in : sandwichWLow a b (k + 1) ≤ X + 1)
    (hX_out : a * sandwichWHigh a b k ≤ X + 1) :
    |f (a * b) - f a - f b| ≤
      (f (sandwichWLow a b (k + 1)) - f (sandwichWLow a b k)) +
      D * ((sandwichStepWindow a b k ∩ descentFinset f X).card : ℝ) +
      D * ((Finset.Ico (a * sandwichWLow a b k) (a * sandwichWHigh a b k) ∩
        descentFinset f X).card : ℝ) := by
  have hpos_id := coprime_sandwich_step_defect_pos_decomp hf ha hb k
  have hneg_id := coprime_sandwich_step_defect_neg_decomp hf ha hb k
  have hwl_ge1 : 1 ≤ sandwichWLow a b k := by dsimp [sandwichWLow]; omega
  have hwl_le_bu : sandwichWLow a b k ≤ b * sandwichU a b k :=
    sandwichWLow_le_mul_sandwichU ha hb k
  have hbu_le_wh : b * sandwichU a b k ≤ sandwichWHigh a b k :=
    mul_sandwichU_le_sandwichWHigh ha hb k
  have hwh_le_next : sandwichWHigh a b k ≤ sandwichWLow a b (k + 1) :=
    sandwichWHigh_le_sandwichWLow_succ a hb k
  have haw_low : a * sandwichWLow a b k ≤ a * b * sandwichU a b k := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left a hwl_le_bu
  have haw_high : a * b * sandwichU a b k ≤ a * sandwichWHigh a b k := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left a hbu_le_wh
  have hstep_pos := disjoint_subintervals_sub_add_sub_le_mul_card_Ico_inter hD0 hD
    hwl_ge1 (le_refl _) hwl_le_bu hbu_le_wh hwh_le_next (le_refl _) hX_in
  have hstep_neg := subinterval_sub_le_mul_card_Ico_inter hD0 hD
    hwl_ge1 hwl_le_bu (le_trans hbu_le_wh hwh_le_next) (le_refl _) hX_in
  have hout_pos := subinterval_sub_le_mul_card_Ico_inter hD0 hD (by nlinarith) haw_low
    haw_high (le_refl _) hX_out
  have hout_neg := subinterval_sub_le_mul_card_Ico_inter hD0 hD (by nlinarith) (le_refl _)
    haw_low haw_high hX_out
  dsimp [sandwichStepWindow]
  rw [abs_le]
  constructor <;> linarith

/-! ## Section 3: The Controlled-Descent `K`-Window Telescoping Inequality -/

/-- **Sharp Interval-Localized Controlled-Descent `K`-Window Telescoping Inequality**:
For any coprime-additive function `f` with `HasPrefixBoundedDownwardJumps f X D` (`0 ≤ D`),
`(K : ℝ) * |f (a * b) - f a - f b|` is bounded by `f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1)`
plus `D` times the descent counts in `[sandwichWLow a b 1, sandwichWLow a b (K + 1))` and
`[a * sandwichWLow a b 1, a * sandwichWLow a b (K + 1))`. -/
theorem controlled_descent_telescoping_Ico_inter_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {X a b : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (K : ℕ)
    (hX_in : sandwichWLow a b (K + 1) ≤ X + 1)
    (hX_out : ∀ k, 1 ≤ k → k ≤ K → a * sandwichWHigh a b k ≤ X + 1) :
    (K : ℝ) * |f (a * b) - f a - f b| ≤
      f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) +
      D * ((Finset.Ico (sandwichWLow a b 1) (sandwichWLow a b (K + 1)) ∩
        descentFinset f X).card : ℝ) +
      D * ((Finset.Ico (a * sandwichWLow a b 1) (a * sandwichWLow a b (K + 1)) ∩
        descentFinset f X).card : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hle_next : sandwichWLow a b (K + 1) ≤ sandwichWLow a b (K + 2) :=
      sandwichWLow_mono_right a b (by omega)
    have ih1 := ih (le_trans hle_next hX_in) (fun k hk1 hkK => hX_out k hk1 (by omega))
    have hstep := controlled_descent_step_window_defect_bound hf hD0 hD ha hb
      hX_in (hX_out (K + 1) (by omega) (le_refl _))
    have hwh_le_wl : a * sandwichWHigh a b (K + 1) ≤ a * sandwichWLow a b (K + 2) :=
      Nat.mul_le_mul_left a (sandwichWHigh_le_sandwichWLow_succ a hb (K + 1))
    have hout_sub :
        Finset.Ico (a * sandwichWLow a b (K + 1)) (a * sandwichWHigh a b (K + 1)) ∩
          descentFinset f X ⊆
        Finset.Ico (a * sandwichWLow a b (K + 1)) (a * sandwichWLow a b (K + 2)) ∩
          descentFinset f X := by
      intro n hn
      exact Finset.mem_inter.mpr
        ⟨Finset.Ico_subset_Ico (le_refl _) hwh_le_wl (Finset.mem_inter.mp hn).1,
          (Finset.mem_inter.mp hn).2⟩
    have hout_card :
        D * ((Finset.Ico (a * sandwichWLow a b (K + 1)) (a * sandwichWHigh a b (K + 1)) ∩
          descentFinset f X).card : ℝ) ≤
        D * ((Finset.Ico (a * sandwichWLow a b (K + 1)) (a * sandwichWLow a b (K + 2)) ∩
          descentFinset f X).card : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hout_sub) hD0
    have h1_le_K1 : sandwichWLow a b 1 ≤ sandwichWLow a b (K + 1) :=
      sandwichWLow_mono_right a b (by omega)
    have hsplit_in := card_Ico_inter_add_card_Ico_inter h1_le_K1 hle_next (descentFinset f X)
    have hsplit_out := card_Ico_inter_add_card_Ico_inter
      (Nat.mul_le_mul_left a h1_le_K1) (Nat.mul_le_mul_left a hle_next) (descentFinset f X)
    have hcast_in :
        ((Finset.Ico (sandwichWLow a b 1) (sandwichWLow a b (K + 1)) ∩ descentFinset f X).card : ℝ) +
        ((sandwichStepWindow a b (K + 1) ∩ descentFinset f X).card : ℝ) =
        ((Finset.Ico (sandwichWLow a b 1) (sandwichWLow a b (K + 2)) ∩ descentFinset f X).card : ℝ) := by
      dsimp [sandwichStepWindow]
      exact_mod_cast hsplit_in
    have hcast_out :
        ((Finset.Ico (a * sandwichWLow a b 1) (a * sandwichWLow a b (K + 1)) ∩
          descentFinset f X).card : ℝ) +
        ((Finset.Ico (a * sandwichWLow a b (K + 1)) (a * sandwichWLow a b (K + 2)) ∩
          descentFinset f X).card : ℝ) =
        ((Finset.Ico (a * sandwichWLow a b 1) (a * sandwichWLow a b (K + 2)) ∩
          descentFinset f X).card : ℝ) := by
      exact_mod_cast hsplit_out
    push_cast
    rw [← hcast_in, ← hcast_out]
    linarith

/-- **Controlled-Descent `K`-Window Telescoping Inequality**:
For any coprime-additive function `f` whose downward jumps up to `X` satisfy `f n - f (n + 1) ≤ D`
(`0 ≤ D`), all `a, b ≥ 1`, and all `K : ℕ` with `sandwichWLow a b (K + 1) ≤ X + 1` and
`a * sandwichWHigh a b K ≤ X + 1`:
`(K : ℝ) * |f (a * b) - f a - f b| ≤ f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) + 2 * D * (descentCount f X : ℝ)`. -/
theorem controlled_descent_telescoping_additive_defect_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {X a b : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (K : ℕ)
    (hX_in : sandwichWLow a b (K + 1) ≤ X + 1)
    (hX_out : a * sandwichWHigh a b K ≤ X + 1) :
    (K : ℝ) * |f (a * b) - f a - f b| ≤
      f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) +
      2 * D * (descentCount f X : ℝ) := by
  have htele := controlled_descent_telescoping_Ico_inter_bound hf hD0 hD ha hb K hX_in
    (fun k _ hkK =>
      le_trans (Nat.mul_le_mul_left a (sandwichWHigh_mono_right a b hkK)) hX_out)
  have hcard_in : (Finset.Ico (sandwichWLow a b 1) (sandwichWLow a b (K + 1)) ∩
      descentFinset f X).card ≤ descentCount f X :=
    Finset.card_le_card Finset.inter_subset_right
  have hcard_out : (Finset.Ico (a * sandwichWLow a b 1) (a * sandwichWLow a b (K + 1)) ∩
      descentFinset f X).card ≤ descentCount f X :=
    Finset.card_le_card Finset.inter_subset_right
  have hmul_in : D * ((Finset.Ico (sandwichWLow a b 1) (sandwichWLow a b (K + 1)) ∩
      descentFinset f X).card : ℝ) ≤ D * (descentCount f X : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard_in) hD0
  have hmul_out : D * ((Finset.Ico (a * sandwichWLow a b 1) (a * sandwichWLow a b (K + 1)) ∩
      descentFinset f X).card : ℝ) ≤ D * (descentCount f X : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard_out) hD0
  linarith

/-- **Controlled-Descent `K`-Window Telescoping under Single Scale Bound**:
For `a, b ≥ 1`, `a * sandwichWLow a b (K + 1) ≤ X + 1` implies both
`sandwichWLow a b (K + 1) ≤ X + 1` and `a * sandwichWHigh a b K ≤ X + 1`, yielding
`(K : ℝ) * |f (a * b) - f a - f b| ≤ f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) + 2 * D * (descentCount f X : ℝ)`. -/
theorem controlled_descent_telescoping_of_mul_wLow_le {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {X a b : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasBoundedDownwardJumps f D)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (K : ℕ)
    (hX : a * sandwichWLow a b (K + 1) ≤ X + 1) :
    (K : ℝ) * |f (a * b) - f a - f b| ≤
      f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) +
      2 * D * (descentCount f X : ℝ) := by
  have hwl_le_mul : sandwichWLow a b (K + 1) ≤ a * sandwichWLow a b (K + 1) :=
    Nat.le_mul_of_pos_left _ ha
  have hawh_le_mul : a * sandwichWHigh a b K ≤ a * sandwichWLow a b (K + 1) :=
    Nat.mul_le_mul_left a (sandwichWHigh_le_sandwichWLow_succ a hb K)
  exact controlled_descent_telescoping_additive_defect_bound hf hD0
    (hasPrefixBoundedDownwardJumps_of_hasBoundedDownwardJumps hD X) ha hb K
    (le_trans hwl_le_mul hX) (le_trans hawh_le_mul hX)

/-! ## Section 4: The Odd Binary Power Sequence (`oddPowTwoSucc`) and Logarithmic Growth -/

/-- The odd binary power sequence `oddPowTwoSucc r = 2 ^ (r + 1) + 1` (`3, 5, 9, 17, 33, ...`),
which grows singly exponentially (`Θ(2^r)`) while satisfying `oddPowTwoSucc (r + 1) + 1 = 2 * oddPowTwoSucc r`. -/
def oddPowTwoSucc (r : ℕ) : ℕ :=
  2 ^ (r + 1) + 1

/-- Every term of `oddPowTwoSucc` is at least `3`. -/
theorem three_le_oddPowTwoSucc (r : ℕ) : 3 ≤ oddPowTwoSucc r := by
  dsimp [oddPowTwoSucc]
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
  have h2 : 2 ≤ 2 ^ (r + 1) := by rw [pow_succ]; omega
  omega

/-- Universal coprimality with `2`: `Nat.Coprime 2 (oddPowTwoSucc r)` for all `r : ℕ`. -/
theorem coprime_two_oddPowTwoSucc (r : ℕ) : Nat.Coprime 2 (oddPowTwoSucc r) := by
  dsimp [oddPowTwoSucc]
  have h : 2 ^ (r + 1) + 1 = 2 * 2 ^ r + 1 := by ring
  rw [h]
  simp

/-- Consecutive-integer doubling relation: `oddPowTwoSucc (r + 1) + 1 = 2 * oddPowTwoSucc r`. -/
theorem oddPowTwoSucc_succ_add_one (r : ℕ) :
    oddPowTwoSucc (r + 1) + 1 = 2 * oddPowTwoSucc r := by
  dsimp [oddPowTwoSucc]
  ring

/-- **Exact Coprime-Additive Step Identity Along `oddPowTwoSucc`**:
For any coprime-additive function `f : ℕ → ℝ` and all `r : ℕ`,
`f (oddPowTwoSucc (r + 1)) - f (oddPowTwoSucc r) = f 2 + (f (oddPowTwoSucc (r + 1)) - f (oddPowTwoSucc (r + 1) + 1))`. -/
theorem coprime_additive_oddPowTwoSucc_step_eq {f : ℕ → ℝ} (hf : IsCoprimeAdditive f) (r : ℕ) :
    f (oddPowTwoSucc (r + 1)) - f (oddPowTwoSucc r) =
      f 2 + (f (oddPowTwoSucc (r + 1)) - f (oddPowTwoSucc (r + 1) + 1)) := by
  have hpos : 0 < oddPowTwoSucc r := by
    have h3 := three_le_oddPowTwoSucc r
    omega
  have hmul : f (2 * oddPowTwoSucc r) = f 2 + f (oddPowTwoSucc r) :=
    hf 2 (by omega) (oddPowTwoSucc r) hpos (coprime_two_oddPowTwoSucc r)
  rw [← oddPowTwoSucc_succ_add_one r] at hmul
  linarith

/-- **Universal Logarithmic Upper Bound Along `oddPowTwoSucc` Under Bounded Downward Jumps**:
For any coprime-additive function `f : ℕ → ℝ` satisfying `HasBoundedDownwardJumps f D`, and every
`r : ℕ`, `f (oddPowTwoSucc r) ≤ f 3 + (r : ℝ) * (f 2 + D)`. -/
theorem f_oddPowTwoSucc_le_of_hasBoundedDownwardJumps {f : ℕ → ℝ} {D : ℝ}
    (hf : IsCoprimeAdditive f) (hD : HasBoundedDownwardJumps f D) (r : ℕ) :
    f (oddPowTwoSucc r) ≤ f 3 + (r : ℝ) * (f 2 + D) := by
  induction r with
  | zero => simp [oddPowTwoSucc]
  | succ r ih =>
    have hstep_id := coprime_additive_oddPowTwoSucc_step_eq hf r
    have h3 : 3 ≤ oddPowTwoSucc (r + 1) := three_le_oddPowTwoSucc (r + 1)
    have hjump : f (oddPowTwoSucc (r + 1)) - f (oddPowTwoSucc (r + 1) + 1) ≤ D :=
      hD (oddPowTwoSucc (r + 1)) (by omega)
    push_cast
    linarith

/-- **Dyadic Scale Inclusion into `oddPowTwoSucc`**:
For all `a, b ≥ 1` and `r : ℕ`, at `K = 2 ^ r` and `s = r + a ^ 2 * b ^ 2 + 1`,
`a * sandwichWLow a b (2 ^ r + 1) ≤ oddPowTwoSucc (r + a ^ 2 * b ^ 2 + 1)`. -/
theorem mul_sandwichWLow_two_pow_le_oddPowTwoSucc {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (r : ℕ) :
    a * sandwichWLow a b (2 ^ r + 1) ≤ oddPowTwoSucc (r + a ^ 2 * b ^ 2 + 1) := by
  set M : ℕ := a ^ 2 * b ^ 2
  have hM_lt : M < 2 ^ M := Nat.lt_two_pow_self
  have hM_le : M ≤ 2 ^ M := le_of_lt hM_lt
  have ha_le_M : a ≤ M := by
    dsimp [M]
    have hab2 : 1 ≤ a * b ^ 2 := by nlinarith
    calc a = a * 1 := (mul_one a).symm
      _ ≤ a * (a * b ^ 2) := Nat.mul_le_mul_left a hab2
      _ = a ^ 2 * b ^ 2 := by ring
  have ha_le_2M : a ≤ 2 ^ M := le_trans ha_le_M hM_le
  have h2r_pos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
  have h2r1_le : 2 ^ r + 1 ≤ 2 ^ (r + 1) := by rw [pow_succ]; omega
  have hlhs_eq : a * sandwichWLow a b (2 ^ r + 1) = M * (2 ^ r + 1) + a := by
    dsimp [sandwichWLow, M]
    ring
  have hmul_le : M * (2 ^ r + 1) ≤ 2 ^ M * 2 ^ (r + 1) :=
    Nat.mul_le_mul hM_le h2r1_le
  have hpow_eq : 2 ^ (r + M + 1 + 1) = 2 ^ M * 2 ^ (r + 1) + 2 ^ M * 2 ^ (r + 1) := by
    calc 2 ^ (r + M + 1 + 1) = 2 ^ M * 2 ^ (r + 1) * 2 := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
      _ = 2 ^ M * 2 ^ (r + 1) + 2 ^ M * 2 ^ (r + 1) := by ring
  have h2r1_pos : 1 ≤ 2 ^ (r + 1) := Nat.one_le_pow (r + 1) 2 (by omega)
  have ha_le_prod : a ≤ 2 ^ M * 2 ^ (r + 1) := by
    calc a ≤ 2 ^ M * 1 := by omega
      _ ≤ 2 ^ M * 2 ^ (r + 1) := Nat.mul_le_mul_left (2 ^ M) h2r1_pos
  dsimp [oddPowTwoSucc]
  change a * sandwichWLow a b (2 ^ r + 1) ≤ 2 ^ (r + M + 1 + 1) + 1
  omega

/-- **Linear Ratio Bound Between `oddPowTwoSucc` and `2 ^ r`**:
For all `a, b, r : ℕ`, `oddPowTwoSucc (r + a ^ 2 * b ^ 2 + 1) ≤ 2 ^ (a ^ 2 * b ^ 2 + 3) * 2 ^ r`. -/
theorem oddPowTwoSucc_le_two_pow_mul (a b r : ℕ) :
    oddPowTwoSucc (r + a ^ 2 * b ^ 2 + 1) ≤ 2 ^ (a ^ 2 * b ^ 2 + 3) * 2 ^ r := by
  set M : ℕ := a ^ 2 * b ^ 2
  dsimp [oddPowTwoSucc]
  have hexp : r + M + 1 + 1 = r + M + 2 := by omega
  rw [hexp]
  have hpos : 1 ≤ 2 ^ (r + M + 2) := Nat.one_le_pow (r + M + 2) 2 (by omega)
  have heq : 2 ^ (M + 3) * 2 ^ r = 2 ^ (r + M + 2) + 2 ^ (r + M + 2) := by
    calc 2 ^ (M + 3) * 2 ^ r = 2 ^ (r + M + 2) * 2 := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
      _ = 2 ^ (r + M + 2) + 2 ^ (r + M + 2) := by ring
  omega

/-! ## Section 5: Complete Additivity and Iterated Division Under `descentCount f X = o(X)` and Bounded Downward Jumps -/

/-- **Quantitative Dyadic Controlled-Descent Additive Defect Bound**:
For any coprime-additive function `f` with `HasBoundedDownwardJumps f D` (`0 ≤ D`), all `a, b ≥ 1`,
and all `r : ℕ`, at `s = r + a ^ 2 * b ^ 2 + 1` and `X = oddPowTwoSucc s`:
`(2 : ℝ) ^ r * |f (a * b) - f a - f b| ≤ f 3 - f (sandwichWLow a b 1) + (s : ℝ) * (f 2 + D) + 3 * D * (descentCount f X : ℝ)`. -/
theorem dyadic_controlled_descent_additive_defect_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : HasBoundedDownwardJumps f D)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (r : ℕ) :
    let s := r + a ^ 2 * b ^ 2 + 1
    let X := oddPowTwoSucc s
    (2 : ℝ) ^ r * |f (a * b) - f a - f b| ≤
      f 3 - f (sandwichWLow a b 1) + (s : ℝ) * (f 2 + D) +
      3 * D * (descentCount f X : ℝ) := by
  intro s X
  have hmul_le_X : a * sandwichWLow a b (2 ^ r + 1) ≤ X :=
    mul_sandwichWLow_two_pow_le_oddPowTwoSucc ha hb r
  have hwl_le_mul : sandwichWLow a b (2 ^ r + 1) ≤ a * sandwichWLow a b (2 ^ r + 1) :=
    Nat.le_mul_of_pos_left _ ha
  have hwl_le_X : sandwichWLow a b (2 ^ r + 1) ≤ X := le_trans hwl_le_mul hmul_le_X
  have hX_succ : a * sandwichWLow a b (2 ^ r + 1) ≤ X + 1 :=
    le_trans hmul_le_X (Nat.le_succ X)
  have htele := controlled_descent_telescoping_of_mul_wLow_le hf hD0 hD ha hb (2 ^ r) hX_succ
  have hpref : HasPrefixBoundedDownwardJumps f X D :=
    hasPrefixBoundedDownwardJumps_of_hasBoundedDownwardJumps hD X
  have hwl_ge1 : 1 ≤ sandwichWLow a b (2 ^ r + 1) := by dsimp [sandwichWLow]; omega
  have hbridge := sub_le_mul_descentCount_of_le hD0 hpref hwl_ge1 hwl_le_X (by omega)
  have hodd := f_oddPowTwoSucc_le_of_hasBoundedDownwardJumps hf hD s
  change f X ≤ f 3 + (s : ℝ) * (f 2 + D) at hodd
  have hcast : ((2 ^ r : ℕ) : ℝ) = (2 : ℝ) ^ r := by push_cast; rfl
  rw [hcast] at htele
  linarith

/-- **Complete Additivity Under `descentCount f X = o(X)` and Bounded Downward Jumps**:
Every coprime-additive function `f : ℕ → ℝ` whose descent count satisfies `descentCount f X = o(X)`
and whose downward jumps satisfy `HasBoundedDownwardJumps f D` is completely additive on positive
integers: `f (a * b) = f a + f b` for all `a, b ≥ 1`. -/
theorem coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b := by
  set Dpos : ℝ := max D 0
  have hDpos0 : 0 ≤ Dpos := le_max_right D 0
  have hDpos : HasBoundedDownwardJumps f Dpos :=
    hasBoundedDownwardJumps_mono hD (le_max_left D 0)
  set Δ : ℝ := |f (a * b) - f a - f b|
  have hΔ_zero : Δ = 0 := by
    by_contra hΔ_ne
    have hΔ_pos : 0 < Δ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hΔ_ne)
    set M : ℕ := a ^ 2 * b ^ 2
    set B : ℝ := |f 2| + Dpos + 1
    have hB_pos : 0 < B := by positivity
    set A₀ : ℝ := |f 3 - f (sandwichWLow a b 1)| + ((M + 1 : ℕ) : ℝ) * B + 1
    have hA0_pos : 0 < A₀ := by positivity
    set C₃ : ℝ := 3 * (Dpos + 1) * (2 : ℝ) ^ (M + 3)
    have hC3_pos : 0 < C₃ := by positivity
    set ε : ℝ := Δ / (2 * C₃)
    have hε_pos : 0 < ε := by positivity
    have hev := ho.bound hε_pos
    rw [Filter.eventually_atTop] at hev
    rcases hev with ⟨X₀, hX₀⟩
    obtain ⟨K₀, hK₀⟩ := exists_nat_gt (2 * (A₀ + 2 * B) / Δ)
    set m : ℕ := K₀ + X₀ + 1
    set r : ℕ := 2 * m
    set s : ℕ := r + M + 1
    set X : ℕ := oddPowTwoSucc s
    have hdyad := dyadic_controlled_descent_additive_defect_bound hf hDpos0 hDpos ha hb r
    change (2 : ℝ) ^ r * Δ ≤ f 3 - f (sandwichWLow a b 1) + (s : ℝ) * (f 2 + Dpos) +
      3 * Dpos * (descentCount f X : ℝ) at hdyad
    have hX_ge_X0 : X₀ ≤ X := by
      have hs_lt : s < 2 ^ (s + 1) := by
        have h1 : s < 2 ^ s := Nat.lt_two_pow_self
        have h2 : 2 ^ s ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      dsimp [X, oddPowTwoSucc]
      omega
    have hnorm := hX₀ X hX_ge_X0
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hnorm
    have hX_le_nat : X ≤ 2 ^ (M + 3) * 2 ^ r := oddPowTwoSucc_le_two_pow_mul a b r
    have hX_le_real : (X : ℝ) ≤ (2 : ℝ) ^ (M + 3) * (2 : ℝ) ^ r := by
      exact_mod_cast hX_le_nat
    have hdesc_le : 3 * Dpos * (descentCount f X : ℝ) ≤ (2 : ℝ) ^ r * (Δ / 2) := by
      have h1 : 3 * Dpos * (descentCount f X : ℝ) ≤ 3 * Dpos * (ε * (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      have h2 : 3 * Dpos * (ε * (X : ℝ)) ≤
          3 * Dpos * (ε * ((2 : ℝ) ^ (M + 3) * (2 : ℝ) ^ r)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hX_le_real (le_of_lt hε_pos)
      have hDpos_le : Dpos ≤ Dpos + 1 := by linarith
      have h3 : 3 * Dpos * (ε * ((2 : ℝ) ^ (M + 3) * (2 : ℝ) ^ r)) ≤
          C₃ * ε * (2 : ℝ) ^ r := by
        dsimp [C₃]
        have hnonneg : 0 ≤ ε * ((2 : ℝ) ^ (M + 3) * (2 : ℝ) ^ r) := by positivity
        nlinarith
      have h4 : C₃ * ε * (2 : ℝ) ^ r = (2 : ℝ) ^ r * (Δ / 2) := by
        dsimp [ε]
        field_simp [ne_of_gt hC3_pos]
      linarith
    have hf3_le : f 3 - f (sandwichWLow a b 1) ≤ |f 3 - f (sandwichWLow a b 1)| :=
      le_abs_self _
    have hf2_le : f 2 + Dpos ≤ B := by
      dsimp [B]
      linarith [le_abs_self (f 2)]
    have hs_pos : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hs_mul_le : (s : ℝ) * (f 2 + Dpos) ≤ (s : ℝ) * B :=
      mul_le_mul_of_nonneg_left hf2_le hs_pos
    have hs_cast : (s : ℝ) = 2 * (m : ℝ) + ((M + 1 : ℕ) : ℝ) := by
      dsimp [s, r]
      push_cast
      ring
    have hlin_le : f 3 - f (sandwichWLow a b 1) + (s : ℝ) * (f 2 + Dpos) ≤
        A₀ + (m : ℝ) * (2 * B) := by
      dsimp [A₀]
      rw [hs_cast] at hs_mul_le ⊢
      linarith
    have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hA0_mul : A₀ + (m : ℝ) * (2 * B) ≤ (m : ℝ) * (A₀ + 2 * B) := by
      nlinarith
    have hm_gt : 2 * (A₀ + 2 * B) / Δ < (m : ℝ) := by
      have hKm : (K₀ : ℝ) < (m : ℝ) := by
        dsimp [m]
        push_cast
        linarith
      exact lt_trans hK₀ hKm
    have hlt_sq : A₀ + 2 * B < (m : ℝ) * (Δ / 2) := by
      have h := (div_lt_iff₀ hΔ_pos).mp hm_gt
      linarith
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hmul_m : (m : ℝ) * (A₀ + 2 * B) < (m : ℝ) * (m : ℝ) * (Δ / 2) := by
      nlinarith
    have hm_sq_nat : m * m ≤ 2 ^ r := by
      have hm_lt : m < 2 ^ m := Nat.lt_two_pow_self
      calc m * m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul (le_of_lt hm_lt) (le_of_lt hm_lt)
        _ = 2 ^ (m + m) := (pow_add 2 m m).symm
        _ = 2 ^ r := by dsimp [r]; rw [two_mul]
    have hm_sq_real : (m : ℝ) * (m : ℝ) ≤ (2 : ℝ) ^ r := by
      exact_mod_cast hm_sq_nat
    have hsq_le_pow : (m : ℝ) * (m : ℝ) * (Δ / 2) ≤ (2 : ℝ) ^ r * (Δ / 2) :=
      mul_le_mul_of_nonneg_right hm_sq_real (by positivity)
    linarith
  have hsub : f (a * b) - f a - f b = 0 := abs_eq_zero.mp hΔ_zero
  linarith

/-- **Power Additivity Under `descentCount f X = o(X)` and Bounded Downward Jumps**:
Every coprime-additive function `f : ℕ → ℝ` with `descentCount f X = o(X)` and
`HasBoundedDownwardJumps f D` satisfies `f (m ^ k) = (k : ℝ) * f m` for all `m ≥ 1` and `k : ℕ`. -/
theorem coprime_additive_pow_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    f (m ^ k) = (k : ℝ) * f m := by
  induction k with
  | zero => simp [coprime_additive_one hf]
  | succ k ih =>
    have hmk_ge1 : 1 ≤ m ^ k := Nat.one_le_pow k m hm
    rw [pow_succ,
      coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps hf ho hD hmk_ge1 hm,
      ih]
    push_cast
    ring

end Erdos1122

end
