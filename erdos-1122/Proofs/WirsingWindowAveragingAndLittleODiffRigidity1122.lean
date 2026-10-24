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
# Wirsing Window-Averaged Coprime Sandwich Bounds and Unconditional `o(1)`-Difference Log-Rigidity (Erdős Problem #1122)

This module proves four universal structural results for Erdős Problem #1122:
1. **Exact Coprime Sandwich Decomposition Identities (Without Monotonicity)**:
   Proves the exact window step-length formulas
   `b * sandwichU a b k = sandwichWLow a b k + (b - 1)`,
   `a * b * sandwichU a b k = a * sandwichWLow a b k + a * (b - 1)`,
   `sandwichWHigh a b k = sandwichWLow a b k + a * b`,
   and the exact non-monotone additive defect decomposition identities
   `f (a * b) - f a - f b = (f (a * b * sandwichU a b k) - f (a * sandwichWLow a b k)) - (f (b * sandwichU a b k) - f (sandwichWLow a b k))`
   at both the lower and upper sandwich endpoints.
2. **Short-Interval Consecutive-Difference Bounds and Complete Additivity under `f(n+1) - f(n) = o(1)`**:
   Bounds `|f (sandwichWHigh a b k) - f (sandwichWLow a b k)| ≤ (a * b) * ε` and
   `|f (a * b) - f a - f b| ≤ (a + 1) * (b - 1) * ε` in terms of the tail consecutive-step bound
   `∀ n ≥ sandwichWLow a b k, |f (n + 1) - f n| ≤ ε`, proving that every coprime-additive function
   with `f(n + 1) - f(n) = o(1)` is completely additive (`f (a * b) = f a + f b`) and power-additive
   (`f (m ^ k) = k * f m`).
3. **Base-`a` Iterated Division and Unconditional Proof of Erdős's 1946 `o(1)`-Difference Theorem (`Erdos1122LittleODiffProp`)**:
   Establishes the base-`a` single-step and `s`-step division bounds
   `|f m - f (m / a ^ s) - s * f a| ≤ s * (a - 1) * ε`, the strong-induction normalization window
   `N ≤ m / a ^ s < a * N`, the logarithmic cross-product bound for completely additive functions,
   and the unconditional resolution of `Erdos1122LittleODiffProp` (`littleO_diff_eq_scaled_log_unconditional`
   and `erdos1122_littleO_diff_prop_holds`).
4. **Wirsing's Window-Localized Coprime Sandwich Averaging and Disjoint-Window Descent Lower Bounds**:
   Localizes the coprime sandwich defect bound to `sandwichInnerWindow a b k` and `sandwichOuterWindow a b k`,
   proves pairwise disjointness across shifts, establishes general disjoint-window and disjoint
   cross-step descent lower bounds `S.card ≤ descentCount f X`, proves the package-local
   shift-set window-averaging inequality (in the style of Wirsing's averaging argument)
   `((S.card : ℝ) - 2 * (descentCount f X : ℝ)) * |f (a * b) - f a - f b| ≤ ∑ k ∈ S_good, (f (sandwichWHigh a b k) - f (sandwichWLow a b k))`,
   and proves that under `descentCount f X = o(X)` a good sandwich shift exists in `[1, K]` for all
   sufficiently large `K`.
-/

/-! ## Section 1: Exact Coprime Sandwich Step-Length and Decomposition Identities -/

/-- Exact inner step length from `sandwichWLow a b k` to `b * sandwichU a b k`:
`b * sandwichU a b k = sandwichWLow a b k + (b - 1)` for all `b ≥ 1`. -/
theorem mul_sandwichU_eq_sandwichWLow_add (a : ℕ) {b : ℕ} (hb : 1 ≤ b) (k : ℕ) :
    b * sandwichU a b k = sandwichWLow a b k + (b - 1) := by
  dsimp [sandwichU, sandwichWLow]
  zify [hb]
  ring

/-- Exact outer step length from `a * sandwichWLow a b k` to `a * b * sandwichU a b k`:
`a * b * sandwichU a b k = a * sandwichWLow a b k + a * (b - 1)` for all `b ≥ 1`. -/
theorem mul_mul_sandwichU_eq_mul_sandwichWLow_add (a : ℕ) {b : ℕ} (hb : 1 ≤ b) (k : ℕ) :
    a * b * sandwichU a b k = a * sandwichWLow a b k + a * (b - 1) := by
  dsimp [sandwichU, sandwichWLow]
  zify [hb]
  ring

/-- **Exact Non-Monotone Coprime Sandwich Defect Identity (Lower Endpoint)**:
For ANY coprime-additive function `f : ℕ → ℝ` (with no monotonicity assumption), all `a, b ≥ 1`,
and all `k : ℕ`, the additive defect `f (a * b) - f a - f b` equals the difference of the two
bounded-length increments from `a * sandwichWLow a b k` and `sandwichWLow a b k`. -/
theorem coprime_sandwich_exact_defect_low {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ) :
    f (a * b) - f a - f b =
      (f (a * b * sandwichU a b k) - f (a * sandwichWLow a b k)) -
      (f (b * sandwichU a b k) - f (sandwichWLow a b k)) := by
  obtain ⟨h1, _, h3, h4⟩ := coprime_sandwich_double_decomp hf ha hb k
  linarith

/-! ## Section 2: Short-Interval Consecutive-Difference Bounds and `o(1)` Complete Additivity -/

/-- **Universal Short-Interval Telescoping Step Bound**:
If `|f (n + 1) - f n| ≤ ε` for all `n` with `n₀ ≤ n < n₀ + d`, then `|f (n₀ + d) - f n₀| ≤ d * ε`. -/
theorem abs_sub_add_le_of_step_abs_le (f : ℕ → ℝ) (n₀ d : ℕ) {ε : ℝ}
    (hstep : ∀ n, n₀ ≤ n → n < n₀ + d → |f (n + 1) - f n| ≤ ε) :
    |f (n₀ + d) - f n₀| ≤ (d : ℝ) * ε := by
  induction d with
  | zero => simp
  | succ d ih =>
    have ih1 : |f (n₀ + d) - f n₀| ≤ (d : ℝ) * ε :=
      ih (fun n hn1 hn2 => hstep n hn1 (by omega))
    have hlast : |f (n₀ + d + 1) - f (n₀ + d)| ≤ ε :=
      hstep (n₀ + d) (by omega) (by omega)
    have h1 : n₀ + (d + 1) = n₀ + d + 1 := by omega
    rw [h1]
    rw [abs_le] at ih1 hlast ⊢
    push_cast
    constructor <;> linarith

/-- **Quantitative Additive Defect Bound from Tail Consecutive Differences**:
For any coprime-additive function `f : ℕ → ℝ`, `a, b ≥ 1`, and `k : ℕ`, if `|f (n + 1) - f n| ≤ ε`
for all `n ≥ sandwichWLow a b k`, then `|f (a * b) - f a - f b| ≤ (a + 1) * (b - 1) * ε`. -/
theorem additive_defect_le_of_tail_step_abs_le {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ) {ε : ℝ}
    (htail : ∀ n, sandwichWLow a b k ≤ n → |f (n + 1) - f n| ≤ ε) :
    |f (a * b) - f a - f b| ≤ (((a + 1) * (b - 1) : ℕ) : ℝ) * ε := by
  have hdef := coprime_sandwich_exact_defect_low hf ha hb k
  have h1 : |f (b * sandwichU a b k) - f (sandwichWLow a b k)| ≤ ((b - 1 : ℕ) : ℝ) * ε := by
    rw [mul_sandwichU_eq_sandwichWLow_add a hb k]
    exact abs_sub_add_le_of_step_abs_le f (sandwichWLow a b k) (b - 1)
      (fun n hn _ => htail n hn)
  have hwl_le : sandwichWLow a b k ≤ a * sandwichWLow a b k :=
    Nat.le_mul_of_pos_left _ ha
  have h2 : |f (a * b * sandwichU a b k) - f (a * sandwichWLow a b k)| ≤
      ((a * (b - 1) : ℕ) : ℝ) * ε := by
    rw [mul_mul_sandwichU_eq_mul_sandwichWLow_add a hb k]
    exact abs_sub_add_le_of_step_abs_le f (a * sandwichWLow a b k) (a * (b - 1))
      (fun n hn _ => htail n (le_trans hwl_le hn))
  have hcast : (((a + 1) * (b - 1) : ℕ) : ℝ) * ε =
      ((a * (b - 1) : ℕ) : ℝ) * ε + ((b - 1 : ℕ) : ℝ) * ε := by
    have hnat : (a + 1) * (b - 1) = a * (b - 1) + (b - 1) := by ring
    rw [hnat]
    push_cast
    ring
  rw [hdef, hcast]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

/-- **Complete Additivity of Coprime-Additive Functions with `f(n + 1) - f(n) = o(1)`**:
Every coprime-additive function `f : ℕ → ℝ` whose consecutive differences vanish at infinity
satisfies `f (a * b) = f a + f b` for all `a, b ≥ 1` (even when `gcd(a, b) > 1`). -/
theorem coprime_additive_mul_of_isLittleO_diff {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)))
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b := by
  set Δ : ℝ := |f (a * b) - f a - f b|
  have hΔ_zero : Δ = 0 := by
    by_contra hΔ_ne
    have hΔ_pos : 0 < Δ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hΔ_ne)
    set C : ℝ := (((a + 1) * (b - 1) : ℕ) : ℝ) + 1
    have hC_pos : 0 < C := by positivity
    have hε_pos : 0 < Δ / (2 * C) := by positivity
    have hev := ho.bound hε_pos
    rw [Filter.eventually_atTop] at hev
    rcases hev with ⟨N, hN⟩
    have htail : ∀ n, sandwichWLow a b N ≤ n → |f (n + 1) - f n| ≤ Δ / (2 * C) := by
      intro n hn
      have hwl_ge : N ≤ sandwichWLow a b N := by
        dsimp [sandwichWLow]
        have hab2 : 1 ≤ a * b ^ 2 := by nlinarith
        nlinarith
      have hnorm := hN n (le_trans hwl_ge hn)
      simpa using hnorm
    have hbound := additive_defect_le_of_tail_step_abs_le hf ha hb N htail
    change Δ ≤ (((a + 1) * (b - 1) : ℕ) : ℝ) * (Δ / (2 * C)) at hbound
    have hle_C : (((a + 1) * (b - 1) : ℕ) : ℝ) ≤ C := by dsimp [C]; linarith
    have hmul_le : (((a + 1) * (b - 1) : ℕ) : ℝ) * (Δ / (2 * C)) ≤ C * (Δ / (2 * C)) :=
      mul_le_mul_of_nonneg_right hle_C (le_of_lt hε_pos)
    have hC_cancel : C * (Δ / (2 * C)) = Δ / 2 := by
      field_simp [ne_of_gt hC_pos]
    linarith
  have hsub : f (a * b) - f a - f b = 0 := abs_eq_zero.mp hΔ_zero
  linarith

/-- **Power Additivity of Coprime-Additive Functions with `f(n + 1) - f(n) = o(1)`**:
Every coprime-additive function `f : ℕ → ℝ` with `f(n + 1) - f(n) = o(1)` satisfies
`f (m ^ k) = (k : ℝ) * f m` for all `m ≥ 1` and `k : ℕ`. -/
theorem coprime_additive_pow_of_isLittleO_diff {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)))
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    f (m ^ k) = (k : ℝ) * f m := by
  induction k with
  | zero => simp [coprime_additive_one hf]
  | succ k ih =>
    have hmk_ge1 : 1 ≤ m ^ k := Nat.one_le_pow k m hm
    rw [pow_succ, coprime_additive_mul_of_isLittleO_diff hf ho hmk_ge1 hm, ih]
    push_cast
    ring

/-! ## Section 3: Base-`a` Iterated Division and Unconditional `Erdos1122LittleODiffProp` -/

/-- Prefix variation bound: if `f 1 = 0` and `1 ≤ r ≤ M + 1`, then
`|f r| ≤ ∑ n ∈ Finset.Icc 1 M, |f (n + 1) - f n|`. -/
theorem abs_f_le_sum_Icc_abs_diff {f : ℕ → ℝ} (h1 : f 1 = 0) {r M : ℕ}
    (hr : 1 ≤ r) (hrM : r ≤ M + 1) :
    |f r| ≤ ∑ n ∈ Finset.Icc 1 M, |f (n + 1) - f n| := by
  have hr_eq : (r - 1) + 1 = r := by omega
  have hsum := sum_Icc_consecutive_diff f (r - 1)
  rw [hr_eq, h1, sub_zero] at hsum
  rw [← hsum]
  calc |∑ n ∈ Finset.Icc 1 (r - 1), (f (n + 1) - f n)|
    _ ≤ ∑ n ∈ Finset.Icc 1 (r - 1), |f (n + 1) - f n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M, |f (n + 1) - f n| :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (by omega)) (fun _ _ _ => abs_nonneg _)

/-- **Base-`a` Single Division Step Inequality**:
For any completely additive function `f`, base `a ≥ 2`, cutoff `N ≥ 1`, and step bound `ε ≥ 0`
on `[N, ∞)`, every `m` with `N ≤ m / a` satisfies `|f m - f (m / a) - f a| ≤ (a - 1) * ε`. -/
theorem completely_additive_div_step_abs_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {a N : ℕ} (ha : 2 ≤ a) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : ∀ n, N ≤ n → |f (n + 1) - f n| ≤ ε)
    {m : ℕ} (hm : N ≤ m / a) :
    |f m - f (m / a) - f a| ≤ ((a - 1 : ℕ) : ℝ) * ε := by
  have hdiv_ge1 : 1 ≤ m / a := le_trans hN hm
  have hprod_ge : N ≤ a * (m / a) := by nlinarith
  have hmod_lt : m % a < a := Nat.mod_lt m (by omega)
  have hmod_le : m % a ≤ a - 1 := by omega
  have hdecomp : a * (m / a) + m % a = m := Nat.div_add_mod m a
  have hstep := abs_sub_add_le_of_step_abs_le f (a * (m / a)) (m % a)
    (fun n hn _ => htail n (le_trans hprod_ge hn))
  rw [hdecomp, hmul a (by omega) (m / a) hdiv_ge1] at hstep
  have hle_mul : ((m % a : ℕ) : ℝ) * ε ≤ ((a - 1 : ℕ) : ℝ) * ε :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmod_le) hε
  rw [abs_le] at hstep ⊢
  constructor <;> linarith

/-- **Base-`a` Iterated Division Inequality**:
For any completely additive function `f`, base `a ≥ 2`, cutoff `N ≥ 1`, step bound `ε ≥ 0`
on `[N, ∞)`, and `s : ℕ`, every `m` with `N ≤ m / a ^ s` satisfies
`|f m - f (m / a ^ s) - s * f a| ≤ s * (a - 1) * ε`. -/
theorem completely_additive_iterated_div_abs_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {a N : ℕ} (ha : 2 ≤ a) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : ∀ n, N ≤ n → |f (n + 1) - f n| ≤ ε)
    (s : ℕ) {m : ℕ} (hm : N ≤ m / a ^ s) :
    |f m - f (m / a ^ s) - (s : ℝ) * f a| ≤ (s : ℝ) * ((a - 1 : ℕ) : ℝ) * ε := by
  induction s generalizing m with
  | zero => simp
  | succ s ih =>
    have hpow_eq : m / a ^ (s + 1) = (m / a) / a ^ s := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    have hm_div : N ≤ (m / a) / a ^ s := by rwa [← hpow_eq]
    have hm_a : N ≤ m / a := by
      have hle : (m / a) / a ^ s ≤ m / a := Nat.div_le_self (m / a) (a ^ s)
      exact le_trans hm_div hle
    have ih_step := ih hm_div
    have h_step := completely_additive_div_step_abs_le hmul ha hN hε htail hm_a
    rw [hpow_eq]
    rw [abs_le] at ih_step h_step ⊢
    push_cast
    constructor <;> linarith

/-- **Existence of Base-`a` Normalization Exponent**:
For any base `a ≥ 2`, cutoff `N ≥ 1`, and `m ≥ N`, there exists `s : ℕ` such that the quotient
`m / a ^ s` lies in `[N, a * N)` and `a ^ s ≤ m < N * a ^ (s + 1)`. -/
theorem exists_pow_div_in_window {a N : ℕ} (ha : 2 ≤ a) (hN : 1 ≤ N) :
    ∀ m : ℕ, N ≤ m →
      ∃ s : ℕ, N ≤ m / a ^ s ∧ m / a ^ s < a * N ∧ a ^ s ≤ m ∧ m < N * a ^ (s + 1) := by
  intro m
  induction' m using Nat.strong_induction_on with m ih
  intro hm
  by_cases hlt : m < a * N
  · refine ⟨0, ?_, ?_, ?_, ?_⟩
    · simpa using hm
    · simpa using hlt
    · simp; omega
    · simp; nlinarith
  · have hge : a * N ≤ m := by omega
    have hdiv_ge : N ≤ m / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
    have hdiv_lt : m / a < m := Nat.div_lt_self (by omega) ha
    obtain ⟨s, hs1, hs2, _, _⟩ := ih (m / a) hdiv_lt hdiv_ge
    have hpow_eq : (m / a) / a ^ s = m / a ^ (s + 1) := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    rw [hpow_eq] at hs1 hs2
    have hpow_pos : 0 < a ^ (s + 1) := pow_pos (by omega) (s + 1)
    have hle_m : a ^ (s + 1) ≤ m := by
      have h1 : 1 ≤ m / a ^ (s + 1) := le_trans hN hs1
      have h2 : 1 * a ^ (s + 1) ≤ (m / a ^ (s + 1)) * a ^ (s + 1) :=
        Nat.mul_le_mul_right (a ^ (s + 1)) h1
      exact le_trans (by simpa using h2) (Nat.div_mul_le_self m (a ^ (s + 1)))
    have hlt_m : m < N * a ^ (s + 2) := by
      have h3 : m < a * N * a ^ (s + 1) := (Nat.div_lt_iff_lt_mul hpow_pos).mp hs2
      have h4 : a * N * a ^ (s + 1) = N * a ^ (s + 2) := by
        rw [pow_succ]
        ring
      omega
    exact ⟨s + 1, hs1, hs2, hle_m, hlt_m⟩

/-- **Quantitative Cross-Product Logarithmic Squeeze from Tail Consecutive Differences**:
For any completely additive function `f` with `f 1 = 0`, any `a, b ≥ 2`, `N ≥ 1`, `ε ≥ 0` with
`|f (n + 1) - f n| ≤ ε` on `n ≥ N`, and any `k : ℕ` with `N ≤ b ^ k`:
`|(k : ℝ) * (Real.log a * f b - Real.log b * f a)| ≤ C_N + (k : ℝ) * Real.log b * (a - 1) * ε`. -/
theorem completely_additive_log_cross_product_bound {f : ℕ → ℝ} (h1 : f 1 = 0)
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    (hpow : ∀ m ≥ 1, ∀ k : ℕ, f (m ^ k) = (k : ℝ) * f m)
    {a b N k : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hN : 1 ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (htail : ∀ n, N ≤ n → |f (n + 1) - f n| ≤ ε)
    (hbk : N ≤ b ^ k) :
    |(k : ℝ) * (Real.log (a : ℝ) * f b - Real.log (b : ℝ) * f a)| ≤
      (Real.log (a : ℝ) * (∑ n ∈ Finset.Icc 1 (a * N), |f (n + 1) - f n|) +
        |f a| * (Real.log (N : ℝ) + Real.log (a : ℝ))) +
      (k : ℝ) * Real.log (b : ℝ) * ((a - 1 : ℕ) : ℝ) * ε := by
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_pow_div_in_window ha hN (b ^ k) hbk
  have hit := completely_additive_iterated_div_abs_le hmul ha hN hε htail s hs1
  rw [hpow b (by omega) k] at hit
  have hrem_bound : |f (b ^ k / a ^ s)| ≤ ∑ n ∈ Finset.Icc 1 (a * N), |f (n + 1) - f n| :=
    abs_f_le_sum_Icc_abs_diff h1 (le_trans hN hs1) (by omega)
  have has_pos : (0 : ℝ) < ((a ^ s : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by omega : 0 < a) s)
  have hbk_pos : (0 : ℝ) < ((b ^ k : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by omega : 0 < b) k)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs3_real : ((a ^ s : ℕ) : ℝ) ≤ ((b ^ k : ℕ) : ℝ) := by exact_mod_cast hs3
  have hlog_low : (s : ℝ) * Real.log (a : ℝ) ≤ (k : ℝ) * Real.log (b : ℝ) := by
    have h := Real.log_le_log has_pos hs3_real
    push_cast at h
    rw [Real.log_pow, Real.log_pow] at h
    exact h
  have hlog_up : (k : ℝ) * Real.log (b : ℝ) ≤
      Real.log (N : ℝ) + ((s : ℝ) + 1) * Real.log (a : ℝ) := by
    have hle_nat : b ^ k ≤ N * a ^ (s + 1) := le_of_lt hs4
    have hle_real : ((b ^ k : ℕ) : ℝ) ≤ ((N * a ^ (s + 1) : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have h := Real.log_le_log hbk_pos hle_real
    push_cast at h
    rw [Real.log_pow, Real.log_mul (ne_of_gt hN_pos) (by positivity), Real.log_pow] at h
    push_cast at h
    linarith
  have ha_gt1 : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have hloga_pos : 0 ≤ Real.log (a : ℝ) := le_of_lt (Real.log_pos ha_gt1)
  have hf_diff : |(k : ℝ) * f b - (s : ℝ) * f a| ≤
      (∑ n ∈ Finset.Icc 1 (a * N), |f (n + 1) - f n|) +
      (s : ℝ) * ((a - 1 : ℕ) : ℝ) * ε := by
    rw [abs_le] at hit hrem_bound ⊢
    constructor <;> linarith
  rw [abs_le] at hf_diff
  have hloga_l := mul_le_mul_of_nonneg_left hf_diff.1 hloga_pos
  have hloga_r := mul_le_mul_of_nonneg_left hf_diff.2 hloga_pos
  have hs_loga_eps : (Real.log (a : ℝ) * (s : ℝ)) * (((a - 1 : ℕ) : ℝ) * ε) ≤
      ((k : ℝ) * Real.log (b : ℝ)) * (((a - 1 : ℕ) : ℝ) * ε) := by
    apply mul_le_mul_of_nonneg_right
    · linarith
    · positivity
  have hlog_abs : |(k : ℝ) * Real.log (b : ℝ) - (s : ℝ) * Real.log (a : ℝ)| ≤
      Real.log (N : ℝ) + Real.log (a : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hmul_fa := mul_le_mul_of_nonneg_left hlog_abs (abs_nonneg (f a))
  rw [← abs_mul] at hmul_fa
  rw [abs_le] at hmul_fa
  have hid : (k : ℝ) * (Real.log (a : ℝ) * f b - Real.log (b : ℝ) * f a) =
      Real.log (a : ℝ) * ((k : ℝ) * f b - (s : ℝ) * f a) -
      f a * ((k : ℝ) * Real.log (b : ℝ) - (s : ℝ) * Real.log (a : ℝ)) := by ring
  rw [hid, abs_le]
  constructor <;> linarith

/-- **Erdős's 1946 Vanishing Consecutive-Difference Theorem (Unconditional Form)**:
Every coprime-additive function `f : ℕ → ℝ` with `f(n + 1) - f(n) = o(1)` satisfies
`f m = (f 2 / Real.log 2) * Real.log m` for all `m ≥ 1`, and hence `IsScaledLogOnPos f`. -/
theorem littleO_diff_eq_scaled_log_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by
  have h1 : f 1 = 0 := coprime_additive_one hf
  have hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y :=
    fun x hx y hy => coprime_additive_mul_of_isLittleO_diff hf ho hx hy
  have hpow : ∀ m ≥ 1, ∀ k : ℕ, f (m ^ k) = (k : ℝ) * f m :=
    fun m hm k => coprime_additive_pow_of_isLittleO_diff hf ho hm k
  have hmain : ∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ) := by
    intro b hb
    rcases eq_or_lt_of_le hb with rfl | hb_gt1
    · simp [h1]
    · have hb2 : 2 ≤ b := hb_gt1
      have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      have hlogb_pos : 0 < Real.log (b : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < b by omega))
      set Δ : ℝ := |Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2|
      have hΔ_zero : Δ = 0 := by
        by_contra hΔ_ne
        have hΔ_pos : 0 < Δ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hΔ_ne)
        set ε : ℝ := Δ / (2 * Real.log (b : ℝ))
        have hε_pos : 0 < ε := by positivity
        have hev := ho.bound hε_pos
        rw [Filter.eventually_atTop] at hev
        rcases hev with ⟨N₀, hN₀⟩
        set N : ℕ := N₀ + 1
        have hN1 : 1 ≤ N := by omega
        have htail : ∀ n, N ≤ n → |f (n + 1) - f n| ≤ ε := by
          intro n hn
          simpa using hN₀ n (by omega)
        set C : ℝ := Real.log (2 : ℝ) * (∑ n ∈ Finset.Icc 1 (2 * N), |f (n + 1) - f n|) +
          |f 2| * (Real.log (N : ℝ) + Real.log (2 : ℝ))
        obtain ⟨K, hK⟩ := exists_nat_gt (2 * C / Δ)
        set k : ℕ := K + N + 1
        have hbk : N ≤ b ^ k := by
          have hk_lt_2k : k < 2 ^ k := Nat.lt_two_pow_self
          have h2k_le_bk : 2 ^ k ≤ b ^ k := Nat.pow_le_pow_left hb2 k
          omega
        have hcross := completely_additive_log_cross_product_bound h1 hmul hpow
          (le_refl 2) hb2 hN1 (le_of_lt hε_pos) htail hbk
        have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
        rw [abs_mul, abs_of_pos hk_pos] at hcross
        change (k : ℝ) * Δ ≤ C + (k : ℝ) * Real.log (b : ℝ) * ((2 - 1 : ℕ) : ℝ) * ε at hcross
        have hcancel : (k : ℝ) * Real.log (b : ℝ) * ((2 - 1 : ℕ) : ℝ) * ε = (k : ℝ) * (Δ / 2) := by
          dsimp [ε]
          push_cast
          field_simp [ne_of_gt hlogb_pos]
        rw [hcancel] at hcross
        have hlt_k : 2 * C / Δ < (k : ℝ) := by
          have hKN : (K : ℝ) < (k : ℝ) := by
            dsimp [k]
            push_cast
            linarith
          exact lt_trans hK hKN
        have hgt : 2 * C < (k : ℝ) * Δ := (div_lt_iff₀ hΔ_pos).mp hlt_k
        linarith
      have heq_sub : Real.log (2 : ℝ) * f b - Real.log (b : ℝ) * f 2 = 0 :=
        abs_eq_zero.mp hΔ_zero
      have heq_mul : Real.log (2 : ℝ) * f b = f 2 * Real.log (b : ℝ) := by linarith
      calc f b = (Real.log (2 : ℝ) * f b) / Real.log (2 : ℝ) := by
            rw [mul_div_cancel_left₀ (f b) hlog2_ne]
        _ = (f 2 * Real.log (b : ℝ)) / Real.log (2 : ℝ) := by rw [heq_mul]
        _ = (f 2 / Real.log (2 : ℝ)) * Real.log (b : ℝ) := by ring
  exact ⟨hmain, ⟨f 2 / Real.log 2, hmain⟩⟩

/-- **Unconditional Verification of `Erdos1122LittleODiffProp` (Erdős 1946 `o(1)` Baseline)**:
Resolves `Erdos1122LittleODiffProp` unconditionally in Lean 4.35.0-rc2. -/
theorem erdos1122_littleO_diff_prop_holds :
    Erdos1122LittleODiffProp ∧
    ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) →
      IsScaledLogOnPos f := by
  have h : Erdos1122LittleODiffProp := fun _ hf ho =>
    (littleO_diff_eq_scaled_log_unconditional hf ho).2
  exact ⟨h, h⟩

/-! ## Section 4: Package-Local Window-Localized Coprime Sandwich Averaging (Wirsing-Style) -/

/-- Inner coprime sandwich window `[sandwichWLow a b k, sandwichWHigh a b k)` of length `a * b`. -/
def sandwichInnerWindow (a b k : ℕ) : Finset ℕ :=
  Finset.Ico (sandwichWLow a b k) (sandwichWHigh a b k)

/-- Outer coprime sandwich window `[a * sandwichWLow a b k, a * sandwichWHigh a b k)` of length `a^2 * b`. -/
def sandwichOuterWindow (a b k : ℕ) : Finset ℕ :=
  Finset.Ico (a * sandwichWLow a b k) (a * sandwichWHigh a b k)

/-- Local interval monotonicity: if `f n ≤ f (n + 1)` for all `n ∈ Finset.Ico u v`, then `f x ≤ f y`
for all `u ≤ x ≤ y ≤ v`. -/
theorem le_of_no_descent_in_Ico {f : ℕ → ℝ} {u v x y : ℕ}
    (hmono : ∀ n ∈ Finset.Ico u v, f n ≤ f (n + 1))
    (hux : u ≤ x) (hxy : x ≤ y) (hyv : y ≤ v) :
    f x ≤ f y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
  induction d with
  | zero => simp
  | succ d ih =>
    have ih1 : f x ≤ f (x + d) := ih (by omega) (by omega)
    have hmem : x + d ∈ Finset.Ico u v := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hstep : f (x + d) ≤ f (x + d + 1) := hmono (x + d) hmem
    have h1 : x + (d + 1) = x + d + 1 := by omega
    rw [h1]
    exact le_trans ih1 hstep

/-- **Window-Localized Coprime Sandwich Defect Bound**:
If `f` is coprime-additive and has no descents in `sandwichInnerWindow a b k` or
`sandwichOuterWindow a b k`, then `0 ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k)` and
`|f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k)`. -/
theorem local_window_additive_defect_le_sandwich_gap {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ)
    (hin : ∀ n ∈ sandwichInnerWindow a b k, f n ≤ f (n + 1))
    (hout : ∀ n ∈ sandwichOuterWindow a b k, f n ≤ f (n + 1)) :
    0 ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k) ∧
    |f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k) := by
  obtain ⟨h1, h2, h3, h4⟩ := coprime_sandwich_double_decomp hf ha hb k
  have hwl_le_bu : sandwichWLow a b k ≤ b * sandwichU a b k :=
    sandwichWLow_le_mul_sandwichU ha hb k
  have hbu_le_wh : b * sandwichU a b k ≤ sandwichWHigh a b k :=
    mul_sandwichU_le_sandwichWHigh ha hb k
  have haw_low : a * sandwichWLow a b k ≤ a * b * sandwichU a b k := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left a hwl_le_bu
  have haw_high : a * b * sandwichU a b k ≤ a * sandwichWHigh a b k := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left a hbu_le_wh
  have hf_wl_bu : f (sandwichWLow a b k) ≤ f (b * sandwichU a b k) :=
    le_of_no_descent_in_Ico hin (le_refl _) hwl_le_bu hbu_le_wh
  have hf_bu_wh : f (b * sandwichU a b k) ≤ f (sandwichWHigh a b k) :=
    le_of_no_descent_in_Ico hin hwl_le_bu hbu_le_wh (le_refl _)
  have hf_awl_abu : f (a * sandwichWLow a b k) ≤ f (a * b * sandwichU a b k) :=
    le_of_no_descent_in_Ico hout (le_refl _) haw_low haw_high
  have hf_abu_awh : f (a * b * sandwichU a b k) ≤ f (a * sandwichWHigh a b k) :=
    le_of_no_descent_in_Ico hout haw_low haw_high (le_refl _)
  refine ⟨by linarith, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- **Localized Forced Descent Witness in Sandwich Windows**:
Whenever `f (sandwichWHigh a b k) - f (sandwichWLow a b k) < |f (a * b) - f a - f b|`, there exists
a descent `n ∈ descentSet f` inside `sandwichInnerWindow a b k` or `sandwichOuterWindow a b k`. -/
theorem exists_descent_in_sandwich_windows_of_gap_lt_defect {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b k : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hlt : f (sandwichWHigh a b k) - f (sandwichWLow a b k) < |f (a * b) - f a - f b|) :
    (∃ n ∈ sandwichInnerWindow a b k, n ∈ descentSet f) ∨
    (∃ n ∈ sandwichOuterWindow a b k, n ∈ descentSet f) := by
  by_contra hno
  rcases not_or.mp hno with ⟨hno_in, hno_out⟩
  have hin : ∀ n ∈ sandwichInnerWindow a b k, f n ≤ f (n + 1) := by
    intro n hn
    by_contra hgt
    have hn_ge1 : 1 ≤ n := by
      have hmem := (Finset.mem_Ico.mp hn).1
      dsimp [sandwichWLow] at hmem
      omega
    exact hno_in ⟨n, hn, hn_ge1, lt_of_not_ge hgt⟩
  have hout : ∀ n ∈ sandwichOuterWindow a b k, f n ≤ f (n + 1) := by
    intro n hn
    by_contra hgt
    have hn_ge1 : 1 ≤ n := by
      have hmem := (Finset.mem_Ico.mp hn).1
      have hwl_ge1 : 1 ≤ sandwichWLow a b k := by dsimp [sandwichWLow]; omega
      have haw_ge1 : 1 ≤ a * sandwichWLow a b k := Nat.mul_pos ha hwl_ge1
      omega
    exact hno_out ⟨n, hn, hn_ge1, lt_of_not_ge hgt⟩
  have hbound := (local_window_additive_defect_le_sandwich_gap hf ha hb k hin hout).2
  linarith

/-- Strict shift separation: for `1 ≤ b` and `k₁ < k₂`, `sandwichWHigh a b k₁ ≤ sandwichWLow a b k₂`. -/
theorem sandwichWHigh_le_sandwichWLow_of_lt (a : ℕ) {b k₁ k₂ : ℕ} (hb : 1 ≤ b) (hlt : k₁ < k₂) :
    sandwichWHigh a b k₁ ≤ sandwichWLow a b k₂ := by
  have h1 : sandwichWHigh a b k₁ ≤ sandwichWLow a b (k₁ + 1) :=
    sandwichWHigh_le_sandwichWLow_succ a hb k₁
  have h2 : sandwichWLow a b (k₁ + 1) ≤ sandwichWLow a b k₂ := by
    dsimp [sandwichWLow]
    have hk : k₁ + 1 ≤ k₂ := hlt
    exact Nat.add_le_add_right (Nat.mul_le_mul_left (a * b ^ 2) hk) 1
  exact le_trans h1 h2

/-- Inner sandwich windows are disjoint for distinct shift indices `k₁ ≠ k₂`. -/
theorem disjoint_sandwichInnerWindow_of_ne (a : ℕ) {b k₁ k₂ : ℕ} (hb : 1 ≤ b) (hne : k₁ ≠ k₂) :
    Disjoint (sandwichInnerWindow a b k₁) (sandwichInnerWindow a b k₂) := by
  rw [Finset.disjoint_left]
  intro n hn1 hn2
  rcases Finset.mem_Ico.mp hn1 with ⟨h1_low, h1_high⟩
  rcases Finset.mem_Ico.mp hn2 with ⟨h2_low, h2_high⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle := sandwichWHigh_le_sandwichWLow_of_lt a hb hlt
    omega
  · have hle := sandwichWHigh_le_sandwichWLow_of_lt a hb hgt
    omega

/-- Outer sandwich windows are disjoint for distinct shift indices `k₁ ≠ k₂`. -/
theorem disjoint_sandwichOuterWindow_of_ne (a : ℕ) {b k₁ k₂ : ℕ} (hb : 1 ≤ b) (hne : k₁ ≠ k₂) :
    Disjoint (sandwichOuterWindow a b k₁) (sandwichOuterWindow a b k₂) := by
  rw [Finset.disjoint_left]
  intro n hn1 hn2
  rcases Finset.mem_Ico.mp hn1 with ⟨h1_low, h1_high⟩
  rcases Finset.mem_Ico.mp hn2 with ⟨h2_low, h2_high⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle := Nat.mul_le_mul_left a (sandwichWHigh_le_sandwichWLow_of_lt a hb hlt)
    omega
  · have hle := Nat.mul_le_mul_left a (sandwichWHigh_le_sandwichWLow_of_lt a hb hgt)
    omega

/-- The family `sandwichInnerWindow a b` is pairwise disjoint on any shift set `S : Set ℕ`. -/
theorem pairwiseDisjoint_sandwichInnerWindow (a : ℕ) {b : ℕ} (hb : 1 ≤ b) (S : Set ℕ) :
    S.PairwiseDisjoint (sandwichInnerWindow a b) :=
  fun _ _ _ _ hne => disjoint_sandwichInnerWindow_of_ne a hb hne

/-- The family `sandwichOuterWindow a b` is pairwise disjoint on any shift set `S : Set ℕ`. -/
theorem pairwiseDisjoint_sandwichOuterWindow (a : ℕ) {b : ℕ} (hb : 1 ≤ b) (S : Set ℕ) :
    S.PairwiseDisjoint (sandwichOuterWindow a b) :=
  fun _ _ _ _ hne => disjoint_sandwichOuterWindow_of_ne a hb hne

/-- **General Disjoint-Window Descent Counting Lower Bound**:
If `W : ι → Finset ℕ` is pairwise disjoint on `S : Finset ι` and every window `W i` (`i ∈ S`)
contains at least one descent in `descentFinset f X`, then `S.card ≤ descentCount f X`. -/
theorem disjoint_window_descentCount_lower_bound {ι : Type*} [DecidableEq ι]
    (f : ℕ → ℝ) (X : ℕ) (S : Finset ι) (W : ι → Finset ℕ)
    (hdisj : (S : Set ι).PairwiseDisjoint W)
    (hwit : ∀ i ∈ S, ∃ n ∈ W i, n ∈ descentFinset f X) :
    S.card ≤ descentCount f X := by
  let W' : ι → Finset ℕ := fun i => W i ∩ descentFinset f X
  have hdisj' : (S : Set ι).PairwiseDisjoint W' := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono Finset.inter_subset_left Finset.inter_subset_left
  have hcard_ge1 : ∀ i ∈ S, 1 ≤ (W' i).card := by
    intro i hi
    obtain ⟨n, hnW, hnD⟩ := hwit i hi
    exact Finset.card_pos.mpr ⟨n, Finset.mem_inter.mpr ⟨hnW, hnD⟩⟩
  have hsub : S.biUnion W' ⊆ descentFinset f X := by
    intro n hn
    rcases Finset.mem_biUnion.mp hn with ⟨i, _, hnW'⟩
    exact (Finset.mem_inter.mp hnW').2
  calc S.card = ∑ _i ∈ S, 1 := by simp
    _ ≤ ∑ i ∈ S, (W' i).card := Finset.sum_le_sum hcard_ge1
    _ = (S.biUnion W').card := (Finset.card_biUnion hdisj').symm
    _ ≤ (descentFinset f X).card := Finset.card_le_card hsub
    _ = descentCount f X := rfl

/-- **Package-local Shift-Set Violation Bound (Wirsing-style averaging)**:
For any coprime-additive `f`, `a, b ≥ 1`, `X : ℕ`, and any shift set `S : Finset ℕ` with
`∀ k ∈ S, a * sandwichWHigh a b k ≤ X + 1`, if every `k ∈ S` violates the sandwich bound
(`f (sandwichWHigh a b k) - f (sandwichWLow a b k) < |f (a * b) - f a - f b|`), then
`S.card ≤ 2 * descentCount f X`. -/
theorem wirsing_shift_set_violation_card_le_two_mul_descentCount {f : ℕ → ℝ}
    (hf : IsCoprimeAdditive f) {a b X : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (S : Finset ℕ) (hX : ∀ k ∈ S, a * sandwichWHigh a b k ≤ X + 1)
    (hviol : ∀ k ∈ S, f (sandwichWHigh a b k) - f (sandwichWLow a b k) < |f (a * b) - f a - f b|) :
    S.card ≤ 2 * descentCount f X := by
  let S_in := S.filter (fun k => ((sandwichInnerWindow a b k) ∩ descentFinset f X).Nonempty)
  let S_out := S.filter (fun k => ((sandwichOuterWindow a b k) ∩ descentFinset f X).Nonempty)
  have hsub : S ⊆ S_in ∪ S_out := by
    intro k hk
    have hX_k := hX k hk
    have hwh_le : sandwichWHigh a b k ≤ a * sandwichWHigh a b k := Nat.le_mul_of_pos_left _ ha
    rcases exists_descent_in_sandwich_windows_of_gap_lt_defect hf ha hb (hviol k hk) with
      ⟨n, hn_in, hdesc⟩ | ⟨n, hn_out, hdesc⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_filter]
      have hn_lt := (Finset.mem_Ico.mp hn_in).2
      have hn_fin : n ∈ descentFinset f X := (mem_descentFinset_iff f X n).mpr ⟨hdesc, by omega⟩
      exact ⟨hk, ⟨n, Finset.mem_inter.mpr ⟨hn_in, hn_fin⟩⟩⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_filter]
      have hn_lt := (Finset.mem_Ico.mp hn_out).2
      have hn_fin : n ∈ descentFinset f X := (mem_descentFinset_iff f X n).mpr ⟨hdesc, by omega⟩
      exact ⟨hk, ⟨n, Finset.mem_inter.mpr ⟨hn_out, hn_fin⟩⟩⟩
  have hin_le : S_in.card ≤ descentCount f X := by
    apply disjoint_window_descentCount_lower_bound f X S_in (sandwichInnerWindow a b)
      (pairwiseDisjoint_sandwichInnerWindow a hb _)
    intro k hk
    rcases (Finset.mem_filter.mp hk).2 with ⟨n, hn⟩
    exact ⟨n, (Finset.mem_inter.mp hn).1, (Finset.mem_inter.mp hn).2⟩
  have hout_le : S_out.card ≤ descentCount f X := by
    apply disjoint_window_descentCount_lower_bound f X S_out (sandwichOuterWindow a b)
      (pairwiseDisjoint_sandwichOuterWindow a hb _)
    intro k hk
    rcases (Finset.mem_filter.mp hk).2 with ⟨n, hn⟩
    exact ⟨n, (Finset.mem_inter.mp hn).1, (Finset.mem_inter.mp hn).2⟩
  have hunion : S.card ≤ S_in.card + S_out.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le S_in S_out)
  omega

/-- **Package-local Zero-Density Good-Shift Lemma (Wirsing-style window averaging)**:
If `f` is coprime-additive and `descentCount f X = o(X)` as `X → ∞`, then for every `a, b ≥ 1`
and all sufficiently large `K` there exists a shift `k ∈ Finset.Icc 1 K` whose coprime sandwich
gap dominates the additive defect:
`|f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k)`.
The conclusion is the sandwich-gap inequality alone; it does not assert that the sandwich
windows contain no descents. -/
theorem wirsing_zero_density_eventually_exists_good_sandwich_shift {f : ℕ → ℝ}
    (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀,
      ∃ k ∈ Finset.Icc 1 K,
        |f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k) := by
  set M : ℕ := 3 * a ^ 2 * b ^ 2
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have hM_real_pos : (0 : ℝ) < (4 * (M : ℝ)) := by positivity
  have hc_pos : (0 : ℝ) < 1 / (4 * (M : ℝ)) := div_pos one_pos hM_real_pos
  have hev := ho.bound hc_pos
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨X₀, hX₀⟩
  refine ⟨X₀ + 1, fun K hK => ?_⟩
  by_contra hno
  have hviol : ∀ k ∈ Finset.Icc 1 K,
      f (sandwichWHigh a b k) - f (sandwichWLow a b k) < |f (a * b) - f a - f b| := by
    intro k hk
    by_contra hge
    exact hno ⟨k, hk, le_of_not_gt hge⟩
  set X : ℕ := a * sandwichWHigh a b K
  have hX_bound : ∀ k ∈ Finset.Icc 1 K, a * sandwichWHigh a b k ≤ X + 1 := by
    intro k hk
    have hk_le : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hwh_le : sandwichWHigh a b k ≤ sandwichWHigh a b K := by
      dsimp [sandwichWHigh]
      have hmul : a * b ^ 2 * k ≤ a * b ^ 2 * K := Nat.mul_le_mul_left (a * b ^ 2) hk_le
      omega
    have hawh_le : a * sandwichWHigh a b k ≤ X := Nat.mul_le_mul_left a hwh_le
    omega
  have hcard_le := wirsing_shift_set_violation_card_le_two_mul_descentCount hf ha hb
    (Finset.Icc 1 K) hX_bound hviol
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard_le
  have hX_ge_X0 : X₀ ≤ X := by
    have hwh_ge_K : K ≤ sandwichWHigh a b K := by
      dsimp [sandwichWHigh]
      have hab2 : 1 ≤ a * b ^ 2 := by nlinarith
      nlinarith
    have hX_ge_K : K ≤ X := le_trans hwh_ge_K (Nat.le_mul_of_pos_left _ ha)
    omega
  have hnorm := hX₀ X hX_ge_X0
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hnorm
  have hX_le_MK : X ≤ M * K := by
    have hwh_le : sandwichWHigh a b K ≤ 3 * a * b ^ 2 * K := by
      dsimp [sandwichWHigh]
      have hbK : 1 ≤ b * K := by nlinarith
      have hab_le : a * b ≤ a * b ^ 2 * K := by
        calc a * b = (a * b) * 1 := by ring
          _ ≤ (a * b) * (b * K) := Nat.mul_le_mul_left (a * b) hbK
          _ = a * b ^ 2 * K := by ring
      have h1_le : 1 ≤ a * b ^ 2 * K := by nlinarith
      have h3 : 3 * a * b ^ 2 * K = a * b ^ 2 * K + a * b ^ 2 * K + a * b ^ 2 * K := by ring
      omega
    calc X = a * sandwichWHigh a b K := rfl
      _ ≤ a * (3 * a * b ^ 2 * K) := Nat.mul_le_mul_left a hwh_le
      _ = M * K := by dsimp [M]; ring
  have hK_real_le : (K : ℝ) ≤ 2 * (descentCount f X : ℝ) := by exact_mod_cast hcard_le
  have hX_real_le : (X : ℝ) ≤ (M : ℝ) * (K : ℝ) := by exact_mod_cast hX_le_MK
  have h1 : (4 * (M : ℝ)) * (descentCount f X : ℝ) ≤ (X : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hnorm (le_of_lt hM_real_pos)
    calc (4 * (M : ℝ)) * (descentCount f X : ℝ)
      _ ≤ (4 * (M : ℝ)) * (1 / (4 * (M : ℝ)) * (X : ℝ)) := hmul
      _ = (X : ℝ) := by field_simp [ne_of_gt hM_real_pos]
  have h2 : (2 * (M : ℝ)) * (K : ℝ) ≤ (4 * (M : ℝ)) * (descentCount f X : ℝ) := by
    have hM_nonneg : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hK_real_le hM_nonneg
    linarith
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hM_pos_real : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  nlinarith

end Erdos1122

end
