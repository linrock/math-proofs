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

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators


namespace Erdos1122

/-- A function `f : ℕ → ℝ` is coprime-additive (an additive arithmetic function) if
`f (a * b) = f a + f b` whenever `a, b > 0` are coprime, matching the convention in
`FormalConjectures/ErdosProblems/491.lean` and `FormalConjectures/ErdosProblems/897.lean`. -/
def IsCoprimeAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a > 0, ∀ b > 0, a.Coprime b → f (a * b) = f a + f b

/-- The descent set `A = {n ≥ 1 : f (n + 1) < f n}` of an arithmetic function `f : ℕ → ℝ`
in Erdős Problem #1122. -/
def descentSet (f : ℕ → ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ f (n + 1) < f n}

/-- The finite prefix `A ∩ [1, X]` of the descent set as a `Finset ℕ`. -/
def descentFinset (f : ℕ → ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => f (n + 1) < f n)

/-- The counting function `|A ∩ [1, X]|` for the descent set up to `X`. -/
def descentCount (f : ℕ → ℝ) (X : ℕ) : ℕ :=
  (descentFinset f X).card

/-- Predicate that `f(n) = c * log n` for some `c : ℝ` on all positive integers `n ≥ 1`. -/
def IsScaledLogOnPos (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ)

/-- **Erdős Problem #1122 Conjecture**:
If `f : ℕ → ℝ` is coprime-additive and `|A ∩ [1, X]| = o(X)` as `X → ∞`, where
`A = {n ≥ 1 : f(n + 1) < f(n)}`, then `f(n) = c * log n` for some `c ∈ ℝ` on all `n ≥ 1`. -/
def Erdos1122Conjecture : Prop :=
  ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
    (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
    IsScaledLogOnPos f

/-- **Erdős (1946) Monotone Baseline Proposition**:
If `f : ℕ → ℝ` is coprime-additive and its descent set `A` is empty, then `f(n) = c * log n`
for some `c ∈ ℝ` on all `n ≥ 1`. -/
def Erdos1122EmptyDescentProp : Prop :=
  ∀ f : ℕ → ℝ, IsCoprimeAdditive f → descentSet f = ∅ → IsScaledLogOnPos f

/-- **Erdős (1946) Vanishing Consecutive Difference Baseline Proposition**:
If `f : ℕ → ℝ` is coprime-additive and `f(n + 1) - f(n) = o(1)` as `n → ∞`, then
`f(n) = c * log n` for some `c ∈ ℝ` on all `n ≥ 1`. -/
def Erdos1122LittleODiffProp : Prop :=
  ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
    (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) →
    IsScaledLogOnPos f

/-- Every coprime-additive function satisfies `f 1 = 0`. -/
theorem coprime_additive_one {f : ℕ → ℝ} (hf : IsCoprimeAdditive f) : f 1 = 0 := by
  have h1 : f (1 * 1) = f 1 + f 1 := hf 1 zero_lt_one 1 zero_lt_one (Nat.coprime_one_left 1)
  linarith

/-- Membership in `descentFinset f X` is equivalent to membership in `descentSet f` and `n ≤ X`. -/
theorem mem_descentFinset_iff (f : ℕ → ℝ) (X n : ℕ) :
    n ∈ descentFinset f X ↔ n ∈ descentSet f ∧ n ≤ X := by
  simp only [descentFinset, Finset.mem_filter, Finset.mem_Icc, descentSet, Set.mem_setOf_eq]
  tauto

/-- `descentCount f X = 0` if and only if `f n ≤ f (n + 1)` for all `1 ≤ n ≤ X`. -/
theorem descentCount_eq_zero_iff (f : ℕ → ℝ) (X : ℕ) :
    descentCount f X = 0 ↔ ∀ n, 1 ≤ n → n ≤ X → f n ≤ f (n + 1) := by
  simp only [descentCount, Finset.card_eq_zero, descentFinset, Finset.filter_eq_empty_iff,
    Finset.mem_Icc, not_lt, and_imp]

/-- `descentSet f = ∅` if and only if `f n ≤ f (n + 1)` for all `n ≥ 1`. -/
theorem descentSet_eq_empty_iff (f : ℕ → ℝ) :
    descentSet f = ∅ ↔ ∀ n, 1 ≤ n → f n ≤ f (n + 1) := by
  simp only [descentSet, Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_and, not_lt]

/-- `descentSet f = ∅` implies `descentCount f X = 0` for every `X : ℕ`. -/
theorem descentCount_eq_zero_of_descentSet_empty {f : ℕ → ℝ} (hempty : descentSet f = ∅) (X : ℕ) :
    descentCount f X = 0 := by
  rw [descentCount_eq_zero_iff]
  intro n hn1 _
  exact (descentSet_eq_empty_iff f).mp hempty n hn1

/-- Erdős Problem #1122 directly implies the Erdős (1946) empty-descent characterization. -/
theorem erdos1122_conjecture_implies_empty_descent_prop :
    Erdos1122Conjecture → Erdos1122EmptyDescentProp := by
  intro hconj f hf hempty
  apply hconj f hf
  have hzero : (fun X : ℕ => (descentCount f X : ℝ)) = 0 := by
    ext X
    simp [descentCount_eq_zero_of_descentSet_empty hempty X]
  rw [hzero]
  exact Asymptotics.isLittleO_zero _ _

/-- Universal telescoping sum of consecutive differences over `Finset.Icc 1 N`:
`∑_{n=1}^N (f (n + 1) - f n) = f (N + 1) - f 1`. -/
theorem sum_Icc_consecutive_diff (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (f (n + 1) - f n)) = f (N + 1) - f 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

/-! ## Descent-Set Structural Theorems -/

/-!
# Structural Theorems on Descent Sets of Coprime-Additive Functions (Erdős Problem #1122)

This module establishes universal (`∀`) structural results advancing Erdős Problem #1122:
1. Prefix monotonicity: a vanishing descent count on `[1, X]` forces `f` to be nondecreasing on
   `[1, X + 1]`, and an empty descent set forces monotonicity on all positive integers.
2. The **Coprime Cross-Step Identity**
   `f ((a + 1) * b) - f (a * (b + 1)) = (f (a + 1) - f a) - (f (b + 1) - f b)`
   for `a.Coprime (b + 1)` and `(a + 1).Coprime b`.
3. **Arithmetic Progression Descent Replication** along `apN Q a k = Q a^2 (a + 1)^2 k + a`:
   a linear lower bound on the descent count, and unconditional rigidity for finitely-supported
   coprime-additive functions.
4. **Erdős's 1946 monotone log-rigidity theorem** for power-additive functions via the `Nat.log`
   sandwich (`empty_descent_power_additive_eq_scaled_log`).
-/


/-! ## Section 1: Prefix Monotonicity and Telescoping Descent Witnesses -/

/-- If `descentCount f X = 0`, then `f` is monotone on the integer interval `[1, X + 1]`. -/
theorem le_of_descentCount_eq_zero {f : ℕ → ℝ} {X a b : ℕ}
    (h0 : descentCount f X = 0) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ X + 1) :
    f a ≤ f b := by
  rw [descentCount_eq_zero_iff] at h0
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => simp
  | succ k ih =>
    have hk_le : a + k ≤ X + 1 := by omega
    have hstep : f (a + k) ≤ f (a + k + 1) := h0 (a + k) (by omega) (by omega)
    have h1 : a + (k + 1) = a + k + 1 := by omega
    rw [h1]
    exact le_trans (ih (by omega) hk_le) hstep

/-- If `descentSet f = ∅`, then `f` is monotone on `[1, ∞)`: for all `1 ≤ a ≤ b`, `f a ≤ f b`. -/
theorem le_of_descentSet_empty {f : ℕ → ℝ} {a b : ℕ}
    (hempty : descentSet f = ∅) (ha : 1 ≤ a) (hab : a ≤ b) :
    f a ≤ f b :=
  le_of_descentCount_eq_zero (descentCount_eq_zero_of_descentSet_empty hempty b) ha hab (by omega)

/-- If `IsCoprimeAdditive f` and `descentSet f = ∅`, then `0 ≤ f n` for every `n ≥ 1`. -/
theorem nonneg_of_descentSet_empty {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ f n := by
  have h1 : f 1 ≤ f n := le_of_descentSet_empty hempty (le_refl 1) hn
  linarith [coprime_additive_one hf]

/-! ## Section 2: The Coprime Cross-Step Identity -/

/-- **Coprime Cross-Step Identity**:
For any coprime-additive function `f` and positive integers `a, b` with `a.Coprime (b + 1)` and
`(a + 1).Coprime b`, the difference between the two coprime products `(a + 1) * b` and
`a * (b + 1)` equals the difference between the consecutive steps at `a` and `b`:
`f ((a + 1) * b) - f (a * (b + 1)) = (f (a + 1) - f a) - (f (b + 1) - f b)`. -/
theorem coprime_cross_step_diff_eq {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcop1 : a.Coprime (b + 1)) (hcop2 : (a + 1).Coprime b) :
    f ((a + 1) * b) - f (a * (b + 1)) = (f (a + 1) - f a) - (f (b + 1) - f b) := by
  have hprod1 : f (a * (b + 1)) = f a + f (b + 1) :=
    hf a ha (b + 1) (Nat.succ_pos b) hcop1
  have hprod2 : f ((a + 1) * b) = f (a + 1) + f b :=
    hf (a + 1) (Nat.succ_pos a) b hb hcop2
  linarith

/-! ## Section 3: Arithmetic Progression Descent Replication (`apN Q a k`) -/

/-- Auxiliary multiplier `u(Q, a, k) = Q * a * (a + 1)^2 * k + 1` for AP descent replication. -/
def apU (Q a k : ℕ) : ℕ := Q * a * (a + 1) ^ 2 * k + 1

/-- Auxiliary multiplier `v(Q, a, k) = Q * a^2 * (a + 1) * k + 1` for AP descent replication. -/
def apV (Q a k : ℕ) : ℕ := Q * a ^ 2 * (a + 1) * k + 1

/-- Arithmetic progression `n(Q, a, k) = a * u(Q, a, k) = Q * a^2 * (a + 1)^2 * k + a`. -/
def apN (Q a k : ℕ) : ℕ := a * apU Q a k

/-- Exact expansion `apN Q a k = Q * a ^ 2 * (a + 1) ^ 2 * k + a`. -/
theorem apN_eq (Q a k : ℕ) : apN Q a k = Q * a ^ 2 * (a + 1) ^ 2 * k + a := by
  dsimp [apN, apU]
  ring

/-- Fundamental consecutive factorization identity: `apN Q a k + 1 = (a + 1) * apV Q a k`. -/
theorem apN_succ_eq (Q a k : ℕ) : apN Q a k + 1 = (a + 1) * apV Q a k := by
  dsimp [apN, apU, apV]
  ring

/-- `a` is always coprime to `apU Q a k`. -/
theorem coprime_a_apU (Q a k : ℕ) : a.Coprime (apU Q a k) := by
  have h : apU Q a k = a * (Q * (a + 1) ^ 2 * k) + 1 := by dsimp [apU]; ring
  rw [h]
  simp

/-- `Q` is always coprime to `apU Q a k`. -/
theorem coprime_Q_apU (Q a k : ℕ) : Q.Coprime (apU Q a k) := by
  have h : apU Q a k = Q * (a * (a + 1) ^ 2 * k) + 1 := by dsimp [apU]; ring
  rw [h]
  simp

/-- `a + 1` is always coprime to `apV Q a k`. -/
theorem coprime_succ_a_apV (Q a k : ℕ) : (a + 1).Coprime (apV Q a k) := by
  have h : apV Q a k = (a + 1) * (Q * a ^ 2 * k) + 1 := by dsimp [apV]; ring
  rw [h]
  simp

/-- `Q` is always coprime to `apV Q a k`. -/
theorem coprime_Q_apV (Q a k : ℕ) : Q.Coprime (apV Q a k) := by
  have h : apV Q a k = Q * (a ^ 2 * (a + 1) * k) + 1 := by dsimp [apV]; ring
  rw [h]
  simp

/-- **Universal AP Consecutive Jump Decomposition**:
For ANY coprime-additive function `f : ℕ → ℝ` (with no support assumption), any `a ≥ 1`, `Q : ℕ`,
and `k : ℕ`, the consecutive difference at `apN Q a k` decomposes as:
`f (apN Q a k + 1) - f (apN Q a k) = (f (a + 1) - f a) + (f (apV Q a k) - f (apU Q a k))`. -/
theorem ap_consecutive_diff_decomposition {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (Q : ℕ) {a : ℕ} (ha : 1 ≤ a) (k : ℕ) :
    f (apN Q a k + 1) - f (apN Q a k) =
      (f (a + 1) - f a) + (f (apV Q a k) - f (apU Q a k)) := by
  have hu_pos : 0 < apU Q a k := by dsimp [apU]; omega
  have hv_pos : 0 < apV Q a k := by dsimp [apV]; omega
  have h1 : f (apN Q a k) = f a + f (apU Q a k) :=
    hf a ha (apU Q a k) hu_pos (coprime_a_apU Q a k)
  have h2 : f (apN Q a k + 1) = f (a + 1) + f (apV Q a k) := by
    rw [apN_succ_eq]
    exact hf (a + 1) (by omega) (apV Q a k) hv_pos (coprime_succ_a_apV Q a k)
  linarith

/-- **Finitely-Supported AP Descent Replication Theorem**:
If `f` is coprime-additive and vanishes on numbers coprime to `Q`, then every single descent
`a ∈ descentSet f` generates an entire infinite arithmetic progression `apN Q a k ∈ descentSet f`
for all `k : ℕ`. -/
theorem finitely_supported_ap_descent_replication {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {Q a : ℕ} (hsupp : ∀ m > 0, Q.Coprime m → f m = 0)
    (ha : a ∈ descentSet f) (k : ℕ) :
    apN Q a k ∈ descentSet f := by
  rcases ha with ⟨ha1, hlt⟩
  have hu_pos : 0 < apU Q a k := by dsimp [apU]; omega
  have hv_pos : 0 < apV Q a k := by dsimp [apV]; omega
  have hfu : f (apU Q a k) = 0 := hsupp (apU Q a k) hu_pos (coprime_Q_apU Q a k)
  have hfv : f (apV Q a k) = 0 := hsupp (apV Q a k) hv_pos (coprime_Q_apV Q a k)
  have hdiff := ap_consecutive_diff_decomposition hf Q ha1 k
  have hapN_ge1 : 1 ≤ apN Q a k := by
    dsimp [apN]
    exact Nat.mul_pos ha1 hu_pos
  refine ⟨hapN_ge1, ?_⟩
  linarith

/-- **Linear Descent Counting Bound for Finitely-Supported Coprime-Additive Functions**:
If `f` is coprime-additive, vanishes on numbers coprime to `Q ≥ 1`, and has a descent `a ∈ descentSet f`,
then `K ≤ descentCount f (Q * a ^ 2 * (a + 1) ^ 2 * K + a)` for every `K : ℕ`. -/
theorem finitely_supported_descentCount_linear_lower_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {Q a : ℕ} (hQ : 1 ≤ Q) (hsupp : ∀ m > 0, Q.Coprime m → f m = 0)
    (ha : a ∈ descentSet f) (K : ℕ) :
    K ≤ descentCount f (Q * a ^ 2 * (a + 1) ^ 2 * K + a) := by
  have ha1 : 1 ≤ a := ha.1
  have hstep_pos : 0 < Q * a ^ 2 * (a + 1) ^ 2 := by positivity
  have hinj : Function.Injective (fun k : ℕ => apN Q a k) := by
    intro k₁ k₂ heq
    simp only [apN_eq] at heq
    have hmul : Q * a ^ 2 * (a + 1) ^ 2 * k₁ = Q * a ^ 2 * (a + 1) ^ 2 * k₂ := by omega
    exact Nat.eq_of_mul_eq_mul_left hstep_pos hmul
  have hsub : (Finset.range K).image (fun k => apN Q a k) ⊆
      descentFinset f (Q * a ^ 2 * (a + 1) ^ 2 * K + a) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨k, hk_range, rfl⟩
    have hk_le : k ≤ K := le_of_lt (Finset.mem_range.mp hk_range)
    rw [mem_descentFinset_iff]
    refine ⟨finitely_supported_ap_descent_replication hf hsupp ha k, ?_⟩
    rw [apN_eq]
    have hmul_le : Q * a ^ 2 * (a + 1) ^ 2 * k ≤ Q * a ^ 2 * (a + 1) ^ 2 * K :=
      Nat.mul_le_mul_left _ hk_le
    omega
  calc K = (Finset.range K).card := (Finset.card_range K).symm
    _ = ((Finset.range K).image (fun k => apN Q a k)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (descentFinset f (Q * a ^ 2 * (a + 1) ^ 2 * K + a)).card := Finset.card_le_card hsub
    _ = descentCount f (Q * a ^ 2 * (a + 1) ^ 2 * K + a) := rfl

/-- If `f` is coprime-additive, vanishes on numbers coprime to `Q ≥ 1`, and has `descentSet f = ∅`,
then `f n = 0` for all `n ≥ 1` (and hence `IsScaledLogOnPos f` holds with `c = 0`). -/
theorem finitely_supported_eq_zero_of_descentSet_empty {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {Q : ℕ} (hQ : 1 ≤ Q) (hsupp : ∀ m > 0, Q.Coprime m → f m = 0)
    (hempty : descentSet f = ∅) :
    ∀ n : ℕ, 1 ≤ n → f n = 0 := by
  intro n hn
  have hlow : 0 ≤ f n := nonneg_of_descentSet_empty hf hempty hn
  have hcop : Q.Coprime (Q * n + 1) := by
    simp
  have hzero_top : f (Q * n + 1) = 0 := hsupp (Q * n + 1) (by omega) hcop
  have hle_top : n ≤ Q * n + 1 := by nlinarith
  have hup : f n ≤ f (Q * n + 1) := le_of_descentSet_empty hempty hn hle_top
  linarith

/-- **Unconditional Resolution of Erdős Problem #1122 for Finitely-Supported Coprime-Additive Functions**:
If `f : ℕ → ℝ` is coprime-additive, vanishes on integers coprime to `Q ≥ 1`, and satisfies
`descentCount f X = o(X)` as `X → ∞`, then `descentSet f = ∅`, `f n = 0` for all `n ≥ 1`, and
`IsScaledLogOnPos f` holds unconditionally. -/
theorem finitely_supported_erdos1122_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {Q : ℕ} (hQ : 1 ≤ Q) (hsupp : ∀ m > 0, Q.Coprime m → f m = 0)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ))) :
    descentSet f = ∅ ∧ (∀ n : ℕ, 1 ≤ n → f n = 0) ∧ IsScaledLogOnPos f := by
  have hempty : descentSet f = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro a ha
    have ha1 : 1 ≤ a := ha.1
    set S : ℕ := Q * a ^ 2 * (a + 1) ^ 2
    have hS_pos : 0 < S := by
      dsimp [S]
      positivity
    have hS_real_pos : (0 : ℝ) < (2 * (S : ℝ)) := by positivity
    have hc_pos : (0 : ℝ) < 1 / (2 * (S : ℝ)) := div_pos one_pos hS_real_pos
    have hev := ho.bound hc_pos
    rw [Filter.eventually_atTop] at hev
    rcases hev with ⟨X₀, hX₀⟩
    set K : ℕ := X₀ + a + 1
    set X : ℕ := S * K + a
    have hX_ge : X₀ ≤ X := by
      have hSK : K ≤ S * K := Nat.le_mul_of_pos_left K hS_pos
      omega
    have hnorm := hX₀ X hX_ge
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hnorm
    have hK_le : (K : ℝ) ≤ (descentCount f X : ℝ) := by
      exact_mod_cast finitely_supported_descentCount_linear_lower_bound hf hQ hsupp ha K
    have hmul_bound : (2 * (S : ℝ)) * (K : ℝ) ≤ (X : ℝ) := by
      have h1 : (2 * (S : ℝ)) * (descentCount f X : ℝ) ≤ (X : ℝ) := by
        have := mul_le_mul_of_nonneg_left hnorm (le_of_lt hS_real_pos)
        calc (2 * (S : ℝ)) * (descentCount f X : ℝ)
          _ ≤ (2 * (S : ℝ)) * (1 / (2 * (S : ℝ)) * (X : ℝ)) := this
          _ = (X : ℝ) := by field_simp [ne_of_gt hS_real_pos]
      have h2 : (2 * (S : ℝ)) * (K : ℝ) ≤ (2 * (S : ℝ)) * (descentCount f X : ℝ) :=
        mul_le_mul_of_nonneg_left hK_le (le_of_lt hS_real_pos)
      exact le_trans h2 h1
    have hX_lt : X < 2 * S * K := by
      have ha_lt_K : a < K := by omega
      have ha_lt_SK : a < S * K := lt_of_lt_of_le ha_lt_K (Nat.le_mul_of_pos_left K hS_pos)
      have h2SK : 2 * S * K = S * K + S * K := by ring
      omega
    have hX_lt_real : (X : ℝ) < (2 * (S : ℝ)) * (K : ℝ) := by
      exact_mod_cast hX_lt
    linarith
  have hzero : ∀ n : ℕ, 1 ≤ n → f n = 0 :=
    finitely_supported_eq_zero_of_descentSet_empty hf hQ hsupp hempty
  refine ⟨hempty, hzero, ⟨0, fun n hn => by simp [hzero n hn]⟩⟩

/-! ## Section 4: Erdős's 1946 Monotone Log-Rigidity Theorem (via `Nat.log` Sandwich) -/

/-- **Monotone Power-Additive `Nat.log` Sandwich**:
If `descentSet f = ∅` and `f (m ^ k) = k * f m` for all `m ≥ 1, k : ℕ`, then for any `m, n ≥ 2`
and `k ≥ 1`, setting `r = Nat.log n (m ^ k)` yields simultaneous two-sided bounds on `k * f m`
and `k * log m`. -/
theorem monotone_power_additive_log_sandwich {f : ℕ → ℝ}
    (hempty : descentSet f = ∅)
    (hpow : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, f (m ^ k) = (k : ℝ) * f m)
    {m n k : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (_hk : 1 ≤ k) :
    let r := Nat.log n (m ^ k)
    (r : ℝ) * f n ≤ (k : ℝ) * f m ∧
    (k : ℝ) * f m ≤ ((r : ℝ) + 1) * f n ∧
    (r : ℝ) * Real.log (n : ℝ) ≤ (k : ℝ) * Real.log (m : ℝ) ∧
    (k : ℝ) * Real.log (m : ℝ) ≤ ((r : ℝ) + 1) * Real.log (n : ℝ) := by
  intro r
  have hmk_pos : 0 < m ^ k := pow_pos (by omega) k
  have hnr_pos : 1 ≤ n ^ r := Nat.one_le_pow r n (by omega)
  have hlow_nat : n ^ r ≤ m ^ k := Nat.pow_log_le_self n (Nat.pos_iff_ne_zero.mp hmk_pos)
  have hup_nat : m ^ k ≤ n ^ (r + 1) :=
    le_of_lt (Nat.lt_pow_succ_log_self (by omega) (m ^ k))
  have hlow_f : f (n ^ r) ≤ f (m ^ k) := le_of_descentSet_empty hempty hnr_pos hlow_nat
  have hup_f : f (m ^ k) ≤ f (n ^ (r + 1)) := le_of_descentSet_empty hempty hmk_pos hup_nat
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
  exact ⟨hlow_f, hup_f, hlow_log, hup_log⟩

/-- **Cross-Product Deviation Inequality**:
Under `IsCoprimeAdditive f`, `descentSet f = ∅`, and `f (m ^ k) = k * f m`, for all `m, n ≥ 2` and
`k ≥ 1`:
`|(k : ℝ) * (Real.log (n : ℝ) * f m - Real.log (m : ℝ) * f n)| ≤ Real.log (n : ℝ) * f n`. -/
theorem monotone_power_additive_cross_product_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅)
    (hpow : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, f (m ^ k) = (k : ℝ) * f m)
    {m n k : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    |(k : ℝ) * (Real.log (n : ℝ) * f m - Real.log (m : ℝ) * f n)| ≤ Real.log (n : ℝ) * f n := by
  obtain ⟨hlow_f, hup_f, hlow_log, hup_log⟩ :=
    monotone_power_additive_log_sandwich hempty hpow hm hn hk
  have hfn_nonneg : 0 ≤ f n := nonneg_of_descentSet_empty hf hempty (by omega)
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogn_pos : 0 ≤ Real.log (n : ℝ) := le_of_lt (Real.log_pos hn_gt1)
  have h1 : Real.log (n : ℝ) * ((Nat.log n (m ^ k) : ℝ) * f n) ≤
      Real.log (n : ℝ) * ((k : ℝ) * f m) :=
    mul_le_mul_of_nonneg_left hlow_f hlogn_pos
  have h2 : Real.log (n : ℝ) * ((k : ℝ) * f m) ≤
      Real.log (n : ℝ) * (((Nat.log n (m ^ k) : ℝ) + 1) * f n) :=
    mul_le_mul_of_nonneg_left hup_f hlogn_pos
  have h3 : f n * ((Nat.log n (m ^ k) : ℝ) * Real.log (n : ℝ)) ≤
      f n * ((k : ℝ) * Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hlow_log hfn_nonneg
  have h4 : f n * ((k : ℝ) * Real.log (m : ℝ)) ≤
      f n * (((Nat.log n (m ^ k) : ℝ) + 1) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hup_log hfn_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- **Erdős's 1946 Monotone Log-Rigidity Theorem (Power-Additive Form)**:
If `f : ℕ → ℝ` is coprime-additive, has `descentSet f = ∅`, and satisfies `f (m ^ k) = k * f m`
for all `m ≥ 1, k : ℕ`, then `f m = (f 2 / Real.log 2) * Real.log m` for every `m ≥ 1`, and hence
`IsScaledLogOnPos f` holds unconditionally. -/
theorem empty_descent_power_additive_eq_scaled_log {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅)
    (hpow : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, f (m ^ k) = (k : ℝ) * f m) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by
  have hmain : ∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ) := by
    intro m hm
    rcases eq_or_lt_of_le hm with rfl | hm_gt1
    · simp [coprime_additive_one hf]
    · have hm2 : 2 ≤ m := hm_gt1
      have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      set Δ : ℝ := |Real.log (2 : ℝ) * f m - Real.log ((m : ℝ)) * f 2|
      have hΔ_zero : Δ = 0 := by
        by_contra hΔ_ne
        have hΔ_pos : 0 < Δ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hΔ_ne)
        set B : ℝ := Real.log (2 : ℝ) * f 2
        obtain ⟨K, hK⟩ := exists_nat_gt (B / Δ)
        have hk1 : 1 ≤ K + 1 := by omega
        have hbound := monotone_power_additive_cross_product_bound hf hempty hpow hm2 (le_refl 2) hk1
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))] at hbound
        change ((K + 1 : ℕ) : ℝ) * Δ ≤ B at hbound
        have hlt_K : B / Δ < ((K + 1 : ℕ) : ℝ) := by
          calc B / Δ < (K : ℝ) := hK
            _ < (K : ℝ) + 1 := lt_add_one (K : ℝ)
            _ = ((K + 1 : ℕ) : ℝ) := by push_cast; ring
        have hgt : B < ((K + 1 : ℕ) : ℝ) * Δ := (div_lt_iff₀ hΔ_pos).mp hlt_K
        linarith
      have heq_sub : Real.log (2 : ℝ) * f m - Real.log (m : ℝ) * f 2 = 0 :=
        abs_eq_zero.mp hΔ_zero
      have heq_mul : Real.log (2 : ℝ) * f m = f 2 * Real.log (m : ℝ) := by linarith
      calc f m = (Real.log (2 : ℝ) * f m) / Real.log (2 : ℝ) := by
            rw [mul_div_cancel_left₀ (f m) hlog2_ne]
        _ = (f 2 * Real.log (m : ℝ)) / Real.log (2 : ℝ) := by rw [heq_mul]
        _ = (f 2 / Real.log (2 : ℝ)) * Real.log (m : ℝ) := by ring
  exact ⟨hmain, ⟨f 2 / Real.log 2, hmain⟩⟩

/-! ## Coprime Sandwich Complete Additivity and Erdős (1946) Log-Rigidity -/

/-!
# Coprime Sandwich Complete Additivity and Unconditional Erdős (1946) Log-Rigidity (#1122)

This part removes the power-additivity hypothesis `f (m ^ k) = k * f m` used by the preceding
empty-descent log-rigidity result, replacing it with the coprime sandwich argument:
1. **The Coprime Sandwich Construction** (`sandwichU`, `sandwichWLow`, `sandwichWHigh`):
   For all `a, b ≥ 1` and `k ≥ 1`, brackets the product `a * b * (a * b * k + 1)` between two integers
   coprime to `a` (`a * b ^ 2 * k + 1` and `a * b ^ 2 * k + a * b + 1`), simultaneously bounding both
   `f (a * b)` and `f a + f b` inside an interval of width
   `f (sandwichWHigh a b k) - f (sandwichWLow a b k)`.
2. **Finite-Prefix and Telescoping Additive Defect Bounds**:
   Bounds `|f (a * b) - f a - f b|` on a monotone prefix `[1, X + 1]` by the sandwich gap, and
   telescopes `K` consecutive sandwich windows to control `(K : ℝ) * |f (a * b) - f a - f b|`.
3. **The Coprime Doubling Sequence** (`coprimeDoublingSeq`):
   Establishes `4 ^ r * 5 ≤ coprimeDoublingSeq r` alongside `f (coprimeDoublingSeq r) ≤ 2 ^ r * f 5`,
   forcing `(M : ℝ) * |f (a * b) - f a - f b| ≤ f 5` for all `M ≥ 1`.
4. **Complete Additivity and Unconditional Proof of Erdős's 1946 Monotone Theorem**:
   Proves `f (a * b) = f a + f b` and `f (m ^ k) = k * f m` for every coprime-additive function with
   `descentSet f = ∅`, establishing `Erdos1122EmptyDescentProp` unconditionally.
-/


/-! ## Section 5: The Coprime Sandwich Construction -/

/-- Auxiliary multiplier `u(a, b, k) = a * b * k + 1`, simultaneously coprime to `a * b` and `b`. -/
def sandwichU (a b k : ℕ) : ℕ := a * b * k + 1

/-- Lower coprime sandwich endpoint `w_-(a, b, k) = a * b ^ 2 * k + 1`, always coprime to `a`. -/
def sandwichWLow (a b k : ℕ) : ℕ := a * b ^ 2 * k + 1

/-- Upper coprime sandwich endpoint `w_+(a, b, k) = a * b ^ 2 * k + a * b + 1`, always coprime to `a`. -/
def sandwichWHigh (a b k : ℕ) : ℕ := a * b ^ 2 * k + a * b + 1

/-- `a * b` is coprime to `sandwichU a b k` for all `a, b, k : ℕ`. -/
theorem coprime_mul_sandwichU (a b k : ℕ) : (a * b).Coprime (sandwichU a b k) := by
  have h : sandwichU a b k = (a * b) * k + 1 := by dsimp [sandwichU]
  rw [h]
  simp

/-- `b` is coprime to `sandwichU a b k` for all `a, b, k : ℕ`. -/
theorem coprime_right_sandwichU (a b k : ℕ) : b.Coprime (sandwichU a b k) := by
  have h : sandwichU a b k = b * (a * k) + 1 := by dsimp [sandwichU]; ring
  rw [h]
  simp

/-- `a` is coprime to `sandwichWLow a b k` for all `a, b, k : ℕ`. -/
theorem coprime_left_sandwichWLow (a b k : ℕ) : a.Coprime (sandwichWLow a b k) := by
  have h : sandwichWLow a b k = a * (b ^ 2 * k) + 1 := by dsimp [sandwichWLow]; ring
  rw [h]
  simp

/-- `a` is coprime to `sandwichWHigh a b k` for all `a, b, k : ℕ`. -/
theorem coprime_left_sandwichWHigh (a b k : ℕ) : a.Coprime (sandwichWHigh a b k) := by
  have h : sandwichWHigh a b k = a * (b ^ 2 * k + b) + 1 := by dsimp [sandwichWHigh]; ring
  rw [h]
  simp

/-- Lower sandwich ordering: `sandwichWLow a b k ≤ b * sandwichU a b k` whenever `1 ≤ b`. -/
theorem sandwichWLow_le_mul_sandwichU {a b : ℕ} (_ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ) :
    sandwichWLow a b k ≤ b * sandwichU a b k := by
  dsimp [sandwichWLow, sandwichU]
  nlinarith

/-- Upper sandwich ordering: `b * sandwichU a b k ≤ sandwichWHigh a b k` whenever `1 ≤ a`. -/
theorem mul_sandwichU_le_sandwichWHigh {a b : ℕ} (ha : 1 ≤ a) (_hb : 1 ≤ b) (k : ℕ) :
    b * sandwichU a b k ≤ sandwichWHigh a b k := by
  dsimp [sandwichU, sandwichWHigh]
  nlinarith

/-- Non-overlapping window property: `sandwichWHigh a b k ≤ sandwichWLow a b (k + 1)` whenever `1 ≤ b`. -/
theorem sandwichWHigh_le_sandwichWLow_succ (a : ℕ) {b : ℕ} (hb : 1 ≤ b) (k : ℕ) :
    sandwichWHigh a b k ≤ sandwichWLow a b (k + 1) := by
  dsimp [sandwichWHigh, sandwichWLow]
  have hb2 : b ≤ b ^ 2 := by nlinarith
  have hab2 : a * b ≤ a * b ^ 2 := Nat.mul_le_mul_left a hb2
  have hexp : a * b ^ 2 * (k + 1) = a * b ^ 2 * k + a * b ^ 2 := by ring
  omega

/-! ## Section 6: Finite-Prefix and Telescoping Coprime Sandwich Defect Bounds -/

/-- Simultaneous coprime-additivity splitting at the four sandwich evaluation points. -/
theorem coprime_sandwich_double_decomp {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ) :
    f (a * sandwichWLow a b k) = f a + f (sandwichWLow a b k) ∧
    f (a * sandwichWHigh a b k) = f a + f (sandwichWHigh a b k) ∧
    f (b * sandwichU a b k) = f b + f (sandwichU a b k) ∧
    f (a * b * sandwichU a b k) = f (a * b) + f (sandwichU a b k) := by
  have hu_pos : 0 < sandwichU a b k := by dsimp [sandwichU]; omega
  have hwl_pos : 0 < sandwichWLow a b k := by dsimp [sandwichWLow]; omega
  have hwh_pos : 0 < sandwichWHigh a b k := by dsimp [sandwichWHigh]; omega
  have hab_pos : 0 < a * b := Nat.mul_pos ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hf a ha (sandwichWLow a b k) hwl_pos (coprime_left_sandwichWLow a b k)
  · exact hf a ha (sandwichWHigh a b k) hwh_pos (coprime_left_sandwichWHigh a b k)
  · exact hf b hb (sandwichU a b k) hu_pos (coprime_right_sandwichU a b k)
  · exact hf (a * b) hab_pos (sandwichU a b k) hu_pos (coprime_mul_sandwichU a b k)

/-- **Finite-Prefix Coprime Sandwich Defect Bound**:
If `descentCount f X = 0` and `a * sandwichWHigh a b k ≤ X + 1`, then the additive defect
`|f (a * b) - f a - f b|` is bounded by `f (sandwichWHigh a b k) - f (sandwichWLow a b k)`. -/
theorem prefix_additive_defect_le_sandwich_gap {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {X a b : ℕ} (k : ℕ) (h0 : descentCount f X = 0) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hX : a * sandwichWHigh a b k ≤ X + 1) :
    |f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k) := by
  obtain ⟨h1, h2, h3, h4⟩ := coprime_sandwich_double_decomp hf ha hb k
  have hwl_ge1 : 1 ≤ sandwichWLow a b k := by dsimp [sandwichWLow]; omega
  have hwh_le_a_wh : sandwichWHigh a b k ≤ a * sandwichWHigh a b k :=
    Nat.le_mul_of_pos_left _ ha
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
    le_of_descentCount_eq_zero h0 hwl_ge1 hwl_le_bu (by omega)
  have hf_bu_wh : f (b * sandwichU a b k) ≤ f (sandwichWHigh a b k) :=
    le_of_descentCount_eq_zero h0 (by omega) hbu_le_wh (by omega)
  have hf_awl_abu : f (a * sandwichWLow a b k) ≤ f (a * b * sandwichU a b k) :=
    le_of_descentCount_eq_zero h0 (by nlinarith) haw_low (by omega)
  have hf_abu_awh : f (a * b * sandwichU a b k) ≤ f (a * sandwichWHigh a b k) :=
    le_of_descentCount_eq_zero h0 (by nlinarith) haw_high hX
  rw [abs_le]
  constructor <;> linarith

/-- **Global Monotone Coprime Sandwich Defect Bound**:
If `IsCoprimeAdditive f` and `descentSet f = ∅`, then for all `a, b ≥ 1` and `k : ℕ`,
`|f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k)`. -/
theorem monotone_additive_defect_le_sandwich_gap {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ) :
    |f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k) := by
  have h0 : descentCount f (a * sandwichWHigh a b k) = 0 :=
    descentCount_eq_zero_of_descentSet_empty hempty (a * sandwichWHigh a b k)
  exact prefix_additive_defect_le_sandwich_gap hf k h0 ha hb (by omega)

/-- **Telescoping `K`-Window Additive Defect Bound**:
For any coprime-additive `f` with `descentSet f = ∅`, `a, b ≥ 1`, and `K : ℕ`,
`(K : ℝ) * |f (a * b) - f a - f b| ≤ f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1)`. -/
theorem monotone_telescoping_additive_defect_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (K : ℕ) :
    (K : ℝ) * |f (a * b) - f a - f b| ≤
      f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hstep := monotone_additive_defect_le_sandwich_gap hf hempty ha hb (K + 1)
    have hle_next : sandwichWHigh a b (K + 1) ≤ sandwichWLow a b (K + 2) :=
      sandwichWHigh_le_sandwichWLow_succ a hb (K + 1)
    have hwh_ge1 : 1 ≤ sandwichWHigh a b (K + 1) := by dsimp [sandwichWHigh]; omega
    have hf_next : f (sandwichWHigh a b (K + 1)) ≤ f (sandwichWLow a b (K + 2)) :=
      le_of_descentSet_empty hempty hwh_ge1 hle_next
    push_cast
    linarith

/-- Non-negativity of `f (sandwichWLow a b 1)` simplifies the `K`-window bound to
`(K : ℝ) * |f (a * b) - f a - f b| ≤ f (sandwichWLow a b (K + 1))`. -/
theorem monotone_telescoping_additive_defect_le_top {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (K : ℕ) :
    (K : ℝ) * |f (a * b) - f a - f b| ≤ f (sandwichWLow a b (K + 1)) := by
  have htele := monotone_telescoping_additive_defect_bound hf hempty ha hb K
  have hwl1_ge1 : 1 ≤ sandwichWLow a b 1 := by dsimp [sandwichWLow]; omega
  have hnonneg : 0 ≤ f (sandwichWLow a b 1) := nonneg_of_descentSet_empty hf hempty hwl1_ge1
  linarith

/-! ## Section 7: The Coprime Doubling Sequence (`coprimeDoublingSeq`) -/

/-- Sylvester-type coprime doubling sequence `x_0 = 5`, `x_{r+1} = x_r * (x_r - 1)`. -/
def coprimeDoublingSeq : ℕ → ℕ
  | 0 => 5
  | r + 1 => coprimeDoublingSeq r * (coprimeDoublingSeq r - 1)

/-- Every term of `coprimeDoublingSeq` is at least `5`. -/
theorem five_le_coprimeDoublingSeq (r : ℕ) : 5 ≤ coprimeDoublingSeq r := by
  induction r with
  | zero => simp [coprimeDoublingSeq]
  | succ r ih =>
    have h4 : 4 ≤ coprimeDoublingSeq r - 1 := by omega
    simp only [coprimeDoublingSeq]
    nlinarith

/-- Exponential lower bound: `4 ^ r * 5 ≤ coprimeDoublingSeq r` for all `r : ℕ`. -/
theorem four_pow_mul_five_le_coprimeDoublingSeq (r : ℕ) :
    4 ^ r * 5 ≤ coprimeDoublingSeq r := by
  induction r with
  | zero => simp [coprimeDoublingSeq]
  | succ r ih =>
    have h5 : 5 ≤ coprimeDoublingSeq r := five_le_coprimeDoublingSeq r
    have h4 : 4 ≤ coprimeDoublingSeq r - 1 := by omega
    simp only [coprimeDoublingSeq]
    calc 4 ^ (r + 1) * 5 = (4 ^ r * 5) * 4 := by ring
      _ ≤ coprimeDoublingSeq r * (coprimeDoublingSeq r - 1) := Nat.mul_le_mul ih h4

/-- Adjacent factor coprimality: `(coprimeDoublingSeq r).Coprime (coprimeDoublingSeq r - 1)`. -/
theorem coprime_coprimeDoublingSeq_pred (r : ℕ) :
    (coprimeDoublingSeq r).Coprime (coprimeDoublingSeq r - 1) := by
  have h5 : 5 ≤ coprimeDoublingSeq r := five_le_coprimeDoublingSeq r
  have h1 : coprimeDoublingSeq r = (coprimeDoublingSeq r - 1) + 1 := by omega
  rw [h1]
  simp

/-- Sub-doubling growth of any monotone coprime-additive function along `coprimeDoublingSeq`:
`f (coprimeDoublingSeq r) ≤ 2 ^ r * f 5`. -/
theorem monotone_f_coprimeDoublingSeq_le {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) (r : ℕ) :
    f (coprimeDoublingSeq r) ≤ (2 : ℝ) ^ r * f 5 := by
  induction r with
  | zero => simp [coprimeDoublingSeq]
  | succ r ih =>
    have h5 : 5 ≤ coprimeDoublingSeq r := five_le_coprimeDoublingSeq r
    have hpred_ge1 : 1 ≤ coprimeDoublingSeq r - 1 := by omega
    have hpred_le : coprimeDoublingSeq r - 1 ≤ coprimeDoublingSeq r := by omega
    have hadd : f (coprimeDoublingSeq (r + 1)) =
        f (coprimeDoublingSeq r) + f (coprimeDoublingSeq r - 1) := by
      simp only [coprimeDoublingSeq]
      exact hf (coprimeDoublingSeq r) (by omega) (coprimeDoublingSeq r - 1) hpred_ge1
        (coprime_coprimeDoublingSeq_pred r)
    have hmono : f (coprimeDoublingSeq r - 1) ≤ f (coprimeDoublingSeq r) :=
      le_of_descentSet_empty hempty hpred_ge1 hpred_le
    have hpow : (2 : ℝ) ^ (r + 1) * f 5 = 2 * ((2 : ℝ) ^ r * f 5) := by ring
    linarith

/-- Key scaling inclusion: at `r = a * b ^ 2 * M` and `K = M * 2 ^ r`, the upper sandwich endpoint
`sandwichWLow a b (K + 1)` never exceeds `coprimeDoublingSeq r`. -/
theorem sandwichWLow_two_pow_scale_le_coprimeDoublingSeq (a b : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    sandwichWLow a b (M * 2 ^ (a * b ^ 2 * M) + 1) ≤ coprimeDoublingSeq (a * b ^ 2 * M) := by
  set r : ℕ := a * b ^ 2 * M
  have hr_lt : r < 2 ^ r := Nat.lt_two_pow_self
  have hr_le : a * b ^ 2 * M ≤ 2 ^ r := le_of_lt hr_lt
  have hab2_le_r : a * b ^ 2 ≤ a * b ^ 2 * M := Nat.le_mul_of_pos_right _ hM
  have hab2_le : a * b ^ 2 ≤ 2 ^ r := le_trans hab2_le_r hr_le
  have h2_pos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
  have h4_eq : 2 ^ r * 2 ^ r = 4 ^ r := by
    calc 2 ^ r * 2 ^ r = (2 * 2) ^ r := (Nat.mul_pow 2 2 r).symm
      _ = 4 ^ r := by rfl
  have hwl_eq : sandwichWLow a b (M * 2 ^ r + 1) = (a * b ^ 2 * M) * 2 ^ r + a * b ^ 2 + 1 := by
    dsimp [sandwichWLow]
    ring
  have hwl_le_4 : sandwichWLow a b (M * 2 ^ r + 1) ≤ 4 ^ r * 5 := by
    rw [hwl_eq]
    have hmul : (a * b ^ 2 * M) * 2 ^ r ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul_right (2 ^ r) hr_le
    rw [h4_eq] at hmul
    have h2_le_4 : 2 ^ r ≤ 4 ^ r := Nat.pow_le_pow_left (by omega) r
    have h1_le_4 : 1 ≤ 4 ^ r := Nat.one_le_pow r 4 (by omega)
    omega
  exact le_trans hwl_le_4 (four_pow_mul_five_le_coprimeDoublingSeq r)

/-! ## Section 8: Complete Additivity and Unconditional Erdős (1946) Monotone Log-Rigidity -/

/-- **Uniform Archimedean Defect Bound**:
For any coprime-additive function `f` with `descentSet f = ∅`, all `a, b ≥ 1`, and all `M ≥ 1`,
`(M : ℝ) * |f (a * b) - f a - f b| ≤ f 5`. -/
theorem monotone_mul_defect_bound_by_f_five {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {a b M : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : 1 ≤ M) :
    (M : ℝ) * |f (a * b) - f a - f b| ≤ f 5 := by
  set r : ℕ := a * b ^ 2 * M
  set K : ℕ := M * 2 ^ r
  have htele := monotone_telescoping_additive_defect_le_top hf hempty ha hb K
  have hle_seq : sandwichWLow a b (K + 1) ≤ coprimeDoublingSeq r :=
    sandwichWLow_two_pow_scale_le_coprimeDoublingSeq a b hM
  have hwl_ge1 : 1 ≤ sandwichWLow a b (K + 1) := by dsimp [sandwichWLow]; omega
  have hf_le_seq : f (sandwichWLow a b (K + 1)) ≤ f (coprimeDoublingSeq r) :=
    le_of_descentSet_empty hempty hwl_ge1 hle_seq
  have hf_seq_le : f (coprimeDoublingSeq r) ≤ (2 : ℝ) ^ r * f 5 :=
    monotone_f_coprimeDoublingSeq_le hf hempty r
  have hcomb : (K : ℝ) * |f (a * b) - f a - f b| ≤ (2 : ℝ) ^ r * f 5 := by linarith
  have hK_cast : (K : ℝ) = (M : ℝ) * (2 : ℝ) ^ r := by
    dsimp [K]
    push_cast
    ring
  rw [hK_cast] at hcomb
  have h2r_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hcomb2 : (2 : ℝ) ^ r * ((M : ℝ) * |f (a * b) - f a - f b|) ≤ (2 : ℝ) ^ r * f 5 := by
    linarith
  exact le_of_mul_le_mul_left hcomb2 h2r_pos

/-- **Complete Additivity of Monotone Coprime-Additive Functions**:
Every coprime-additive function `f : ℕ → ℝ` with `descentSet f = ∅` is completely additive on
positive integers: `f (a * b) = f a + f b` for all `a, b ≥ 1` (even when `gcd(a, b) > 1`). -/
theorem coprime_additive_mul_of_descentSet_empty {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b := by
  set Δ : ℝ := |f (a * b) - f a - f b|
  have hΔ_zero : Δ = 0 := by
    by_contra hΔ_ne
    have hΔ_pos : 0 < Δ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hΔ_ne)
    obtain ⟨K, hK⟩ := exists_nat_gt (f 5 / Δ)
    have hM1 : 1 ≤ K + 1 := by omega
    have hbound := monotone_mul_defect_bound_by_f_five hf hempty ha hb hM1
    change ((K + 1 : ℕ) : ℝ) * Δ ≤ f 5 at hbound
    have hlt_K : f 5 / Δ < ((K + 1 : ℕ) : ℝ) := by
      calc f 5 / Δ < (K : ℝ) := hK
        _ < (K : ℝ) + 1 := lt_add_one (K : ℝ)
        _ = ((K + 1 : ℕ) : ℝ) := by push_cast; ring
    have hgt : f 5 < ((K + 1 : ℕ) : ℝ) * Δ := (div_lt_iff₀ hΔ_pos).mp hlt_K
    linarith
  have hsub : f (a * b) - f a - f b = 0 := abs_eq_zero.mp hΔ_zero
  linarith

/-- **Power Additivity of Monotone Coprime-Additive Functions**:
Every coprime-additive function `f : ℕ → ℝ` with `descentSet f = ∅` satisfies
`f (m ^ k) = (k : ℝ) * f m` for all `m ≥ 1` and `k : ℕ`. -/
theorem coprime_additive_pow_of_descentSet_empty {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    f (m ^ k) = (k : ℝ) * f m := by
  induction k with
  | zero => simp [coprime_additive_one hf]
  | succ k ih =>
    have hmk_ge1 : 1 ≤ m ^ k := Nat.one_le_pow k m hm
    rw [pow_succ, coprime_additive_mul_of_descentSet_empty hf hempty hmk_ge1 hm, ih]
    push_cast
    ring

/-- **Erdős's 1946 Monotone Log-Rigidity Theorem (Unconditional Form)**:
Every coprime-additive function `f : ℕ → ℝ` with `descentSet f = ∅` satisfies
`f m = (f 2 / Real.log 2) * Real.log m` for all `m ≥ 1`, with no auxiliary power-additivity hypothesis. -/
theorem empty_descent_eq_scaled_log_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f :=
  empty_descent_power_additive_eq_scaled_log hf hempty
    (fun _ hm k => coprime_additive_pow_of_descentSet_empty hf hempty hm k)

/-- **Unconditional Verification of `Erdos1122EmptyDescentProp` (Erdős 1946 Baseline)**:
Resolves `Erdos1122EmptyDescentProp` unconditionally in Lean 4.35.0-rc2. -/
theorem erdos1122_empty_descent_prop_holds :
    Erdos1122EmptyDescentProp ∧
    ∀ f : ℕ → ℝ, IsCoprimeAdditive f → descentSet f = ∅ → IsScaledLogOnPos f := by
  have h : Erdos1122EmptyDescentProp := fun _ hf hempty =>
    (empty_descent_eq_scaled_log_unconditional hf hempty).2
  exact ⟨h, h⟩

end Erdos1122

end
