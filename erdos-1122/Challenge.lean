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
noncomputable section
open Filter
open scoped BigOperators Topology
namespace Erdos1122
/-- Predicate for a coprime-additive arithmetic function `f : ℕ → ℝ` (`f (a * b) = f a + f b` when `gcd(a, b) = 1`). -/
def IsCoprimeAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a > 0, ∀ b > 0, a.Coprime b → f (a * b) = f a + f b
/-- The descent set `A = {n ≥ 1 : f (n + 1) < f n}` in Erdős Problem 1122. -/
def descentSet (f : ℕ → ℝ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ f (n + 1) < f n}
/-- Finite prefix `A ∩ [1, X]` of the descent set. -/
def descentFinset (f : ℕ → ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => f (n + 1) < f n)
/-- Counting function `|A ∩ [1, X]|` for the descent set up to `X`. -/
def descentCount (f : ℕ → ℝ) (X : ℕ) : ℕ :=
  (descentFinset f X).card
/-- Predicate that `f n = c * log n` for some `c : ℝ` on all `n ≥ 1`. -/
def IsScaledLogOnPos (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ)
/-- Erdős Problem 1122 Conjecture (`descentCount f X = o(X) → IsScaledLogOnPos f`). -/
def Erdos1122Conjecture : Prop :=
  ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
    (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
    IsScaledLogOnPos f
/-- Erdős (1946) Monotone Baseline Proposition (`descentSet f = ∅ → IsScaledLogOnPos f`). -/
def Erdos1122EmptyDescentProp : Prop :=
  ∀ f : ℕ → ℝ, IsCoprimeAdditive f → descentSet f = ∅ → IsScaledLogOnPos f
/-- Erdős (1946) Vanishing Consecutive Difference Baseline Proposition (`f(n+1) - f(n) = o(1) → IsScaledLogOnPos f`). -/
def Erdos1122LittleODiffProp : Prop :=
  ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
    (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) →
    IsScaledLogOnPos f
/-- Coprime sandwich multiplier `u(a, b, k) = a * b * k + 1`. -/
def sandwichU (a b k : ℕ) : ℕ := a * b * k + 1
/-- Lower coprime sandwich endpoint `w_-(a, b, k) = a * b ^ 2 * k + 1`. -/
def sandwichWLow (a b k : ℕ) : ℕ := a * b ^ 2 * k + 1
/-- Upper coprime sandwich endpoint `w_+(a, b, k) = a * b ^ 2 * k + a * b + 1`. -/
def sandwichWHigh (a b k : ℕ) : ℕ := a * b ^ 2 * k + a * b + 1
/-- Global bounded downward-jump predicate (`f n - f (n + 1) ≤ D` for all `n ≥ 1`). -/
def HasBoundedDownwardJumps (f : ℕ → ℝ) (D : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → f n - f (n + 1) ≤ D
/-- Finite-prefix bounded downward-jump predicate on `descentFinset f X`. -/
def HasPrefixBoundedDownwardJumps (f : ℕ → ℝ) (X : ℕ) (D : ℝ) : Prop :=
  ∀ n ∈ descentFinset f X, f n - f (n + 1) ≤ D
/-- Base-`a` division window `[a * (m / a ^ (j + 1)), a * (m / a ^ (j + 1) + 1))`. -/
def divWindow (a m j : ℕ) : Finset ℕ :=
  Finset.Ico (a * (m / a ^ (j + 1))) (a * (m / a ^ (j + 1) + 1))
/-- Total number of descents up to `X` along the `s`-step base-`a` division trajectory of `m`. -/
def trajDescentCount (f : ℕ → ℝ) (X a m s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range s, (divWindow a m j ∩ descentFinset f X).card
/-- Uniform oscillation bound `|f q - f u| ≤ C` on every dyadic shell `u ≤ q ≤ 2 * u`. -/
def HasBoundedDyadicShellOscillation (f : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u → |f q - f u| ≤ C

/-- Erdős [Er46]: if `A` is empty, i.e. `f n ≤ f (n + 1)` for all `n ≥ 1`, then `f n = c * log n`. -/
theorem erdos_1122.variants.monotone (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hmono : ∀ n ≥ 1, f n ≤ f (n + 1)) :
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  sorry

/-- Erdős [Er46]: if `f (n + 1) - f n = o(1)`, then `f n = c * log n` for some `c : ℝ`. -/
theorem erdos_1122.variants.sub_tendsto_zero (f : ℕ → ℝ)
    (hf : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (hdiff : Tendsto (fun n ↦ f (n + 1) - f n) atTop (𝓝 0)) :
    ∃ c : ℝ, ∀ n > 0, f n = c * Real.log n := by
  sorry

namespace Core

open Erdos1122

/-- Erdős Problem 1122 directly implies Erdős's 1946 empty-descent characterization. -/
theorem erdos1122_conjecture_implies_empty_descent_prop :
    Erdos1122Conjecture → Erdos1122EmptyDescentProp := by sorry

/-- Coprime cross-step identity `f ((a + 1) * b) - f (a * (b + 1)) = (f (a + 1) - f a) - (f (b + 1) - f b)`. -/
theorem coprime_cross_step_diff_eq {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcop1 : a.Coprime (b + 1)) (hcop2 : (a + 1).Coprime b) :
    f ((a + 1) * b) - f (a * (b + 1)) = (f (a + 1) - f a) - (f (b + 1) - f b) := by sorry

/-- Unconditional resolution of Erdős Problem 1122 for finitely supported coprime-additive functions. -/
theorem finitely_supported_erdos1122_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {Q : ℕ} (hQ : 1 ≤ Q) (hsupp : ∀ m > 0, Q.Coprime m → f m = 0)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ))) :
    descentSet f = ∅ ∧ (∀ n : ℕ, 1 ≤ n → f n = 0) ∧ IsScaledLogOnPos f := by sorry

/-- Every coprime-additive function with empty descent set is completely additive (`f (a * b) = f a + f b`). -/
theorem coprime_additive_mul_of_descentSet_empty {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b := by sorry

/-- Erdős's 1946 monotone logarithmic rigidity theorem with explicit constant `f 2 / Real.log 2`. -/
theorem empty_descent_eq_scaled_log_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (hempty : descentSet f = ∅) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by sorry

/-- Unconditional proof of `Erdos1122EmptyDescentProp`. -/
theorem erdos1122_empty_descent_prop_holds :
    Erdos1122EmptyDescentProp ∧
    ∀ f : ℕ → ℝ, IsCoprimeAdditive f → descentSet f = ∅ → IsScaledLogOnPos f := by sorry

/-- Every coprime-additive function with `f (n + 1) - f n = o(1)` is completely additive (`f (a * b) = f a + f b`). -/
theorem coprime_additive_mul_of_isLittleO_diff {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)))
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b := by sorry

/-- Erdős's 1946 vanishing consecutive-difference logarithmic rigidity theorem with explicit constant `f 2 / Real.log 2`. -/
theorem littleO_diff_eq_scaled_log_unconditional {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by sorry

/-- Unconditional proof of `Erdos1122LittleODiffProp`. -/
theorem erdos1122_littleO_diff_prop_holds :
    Erdos1122LittleODiffProp ∧
    ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun n : ℕ => f (n + 1) - f n) =o[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) →
      IsScaledLogOnPos f := by sorry

/-- Zero-density descent count `descentCount f X = o(X)` implies the eventual existence of a good coprime sandwich shift in `[1, K]`. -/
theorem wirsing_zero_density_eventually_exists_good_sandwich_shift {f : ℕ → ℝ}
    (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀,
      ∃ k ∈ Finset.Icc 1 K,
        |f (a * b) - f a - f b| ≤ f (sandwichWHigh a b k) - f (sandwichWLow a b k) := by sorry

/-- Controlled-descent `K`-window telescoping bound on the additive defect `|f (a * b) - f a - f b|`. -/
theorem controlled_descent_telescoping_additive_defect_bound {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    {X a b : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (K : ℕ)
    (hX_in : sandwichWLow a b (K + 1) ≤ X + 1)
    (hX_out : a * sandwichWHigh a b K ≤ X + 1) :
    (K : ℝ) * |f (a * b) - f a - f b| ≤
      f (sandwichWLow a b (K + 1)) - f (sandwichWLow a b 1) +
      2 * D * (descentCount f X : ℝ) := by sorry

/-- Complete additivity `f (a * b) = f a + f b` under `descentCount f X = o(X)` and `HasBoundedDownwardJumps f D`. -/
theorem coprime_additive_mul_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    f (a * b) = f a + f b := by sorry

/-- Controlled-descent `Nat.log` logarithmic ratio squeeze `|f m / log m - f n / log n| ≤ (|f n| + D * descentCount f X) / (k * log m)`. -/
theorem controlled_descent_log_ratio_diff_le_descentCount {f : ℕ → ℝ} {X : ℕ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    (hpow : ∀ b : ℕ, 1 ≤ b → ∀ r : ℕ, f (b ^ r) = (r : ℝ) * f b)
    {m n : ℕ} (k : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hX : n ^ (Nat.log n (m ^ k) + 1) ≤ X + 1) :
    |f m / Real.log (m : ℝ) - f n / Real.log (n : ℝ)| ≤
      (|f n| + D * (descentCount f X : ℝ)) / ((k : ℝ) * Real.log (m : ℝ)) := by sorry

/-- Unconditional logarithmic rigidity under `descentCount f X = o(log X)` and `HasBoundedDownwardJumps f D`. -/
theorem sublogarithmic_descentCount_eq_scaled_log_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f) {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    (ho_lin : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    (ho_log : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop]
      (fun X : ℕ => Real.log (X : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by sorry

/-- Logarithmic rigidity under sublinear base-`2` trajectory descents and `HasBoundedDownwardJumps f D`. -/
theorem trajectory_sublinear_descent_eq_scaled_log_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    (htraj : ∀ b : ℕ, 2 ≤ b →
      (fun k : ℕ => (trajDescentCount f (2 * ((b ^ k) / 2 + 1)) 2 (b ^ k) (Nat.log 2 (b ^ k)) : ℝ))
        =o[Filter.atTop] (fun k : ℕ => (k : ℝ))) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by sorry

/-- Pigeonhole existence of a zero-descent shifted base-`a` division trajectory when `s * descentCount f X < U`. -/
theorem exists_zero_descent_shifted_div_trajectory_of_mul_descentCount_lt (f : ℕ → ℝ) (X : ℕ)
    {a m s U : ℕ} (ha : 1 ≤ a) (hm : a ^ s ≤ m) (hU : s * descentCount f X < U) :
    ∃ u ∈ Finset.Icc 1 U, trajDescentCount f X a (u * m) s = 0 := by sorry

/-- Exact equivalence `IsScaledLogOnPos f ↔ ∃ C, HasBoundedDyadicShellOscillation f C` under `descentCount f X = o(X)` and `HasBoundedDownwardJumps f D`. -/
theorem isScaledLogOnPos_iff_exists_boundedDyadicShellOscillation_of_isLittleO_descentCount_of_hasBoundedDownwardJumps
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D) :
    IsScaledLogOnPos f ↔ ∃ C : ℝ, HasBoundedDyadicShellOscillation f C := by sorry

/-- Top-down conditional reduction of `Erdos1122Conjecture` to bounded downward jumps and bounded dyadic-shell oscillation. -/
theorem erdos1122_conjecture_of_boundedDownwardJumps_and_dyadicShellOscillation
    (hjump : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ D : ℝ, HasBoundedDownwardJumps f D)
    (hshell : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ C : ℝ, HasBoundedDyadicShellOscillation f C) :
    Erdos1122Conjecture := by sorry

/-- Binary-carry odd/even consecutive step bounds under `HasBoundedDownwardJumps f D`. -/
theorem completely_additive_dyadic_step_bounds_of_hasBoundedDownwardJumps {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {D : ℝ} (hD : HasBoundedDownwardJumps f D) {m : ℕ} (hm : 1 ≤ m) :
    -D ≤ f (2 * m + 1) - f (2 * m) ∧
    f (2 * m + 1) - f (2 * m) ≤ (f (m + 1) - f m) + D ∧
    -D ≤ f (2 * m) - f (2 * m - 1) := by sorry

/-- Dyadic-shell complementary identity `(f q - f u) + (f (2 * u) - f q) = f 2` for completely additive functions. -/
theorem completely_additive_dyadic_shell_complement_eq {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y) {u : ℕ} (hu : 1 ≤ u) (q : ℕ) :
    (f q - f u) + (f (2 * u) - f q) = f 2 := by sorry

/-- Window-localized dyadic-shell oscillation bound `|f q - f u| ≤ |f 2| + D * (Ico u (2 * u) ∩ descentFinset f X).card`. -/
theorem completely_additive_dyadic_shell_window_oscillation_bound {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {X : ℕ} {D : ℝ} (hD0 : 0 ≤ D) (hD : HasPrefixBoundedDownwardJumps f X D)
    {u q : ℕ} (hu : 1 ≤ u) (huq : u ≤ q) (hq2u : q ≤ 2 * u) (hX : 2 * u ≤ X + 1) :
    |f q - f u| ≤ |f 2| + D * ((Finset.Ico u (2 * u) ∩ descentFinset f X).card : ℝ) := by sorry

/-- Iterated binary-halving bit-length defect bound `|f q - s * f 2 - f (q / 2 ^ s)| ≤ s * B`. -/
theorem completely_additive_iterated_binary_halving_defect_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hcarry : ∀ m : ℕ, 1 ≤ m → |f (2 * m + 1) - f 2 - f m| ≤ B)
    (s : ℕ) {q : ℕ} (hq : 1 ≤ q / 2 ^ s) :
    |f q - (s : ℝ) * f 2 - f (q / 2 ^ s)| ≤ (s : ℝ) * B := by sorry

/-- Iterated simultaneous binary-halving difference bound `|(f q - f u) - (f (q / 2 ^ s) - f (u / 2 ^ s))| ≤ 2 * s * B`. -/
theorem completely_additive_iterated_simultaneous_binary_halving_diff_le {f : ℕ → ℝ}
    (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hcarry : ∀ m : ℕ, 1 ≤ m → |f (2 * m + 1) - f 2 - f m| ≤ B)
    (s : ℕ) {u q : ℕ} (hu : 1 ≤ u / 2 ^ s) (hq : 1 ≤ q / 2 ^ s) :
    |(f q - f u) - (f (q / 2 ^ s) - f (u / 2 ^ s))| ≤ 2 * (s : ℝ) * B := by sorry

/-- Multi-shell oscillation bound across `[2 ^ s * u, 2 ^ (s + 1) * u]` from `HasBoundedDyadicShellOscillation f C`. -/
theorem completely_additive_pow_two_shell_oscillation_of_hasBoundedDyadicShellOscillation
    {f : ℕ → ℝ} (hmul : ∀ x ≥ 1, ∀ y ≥ 1, f (x * y) = f x + f y)
    {C : ℝ} (hC : HasBoundedDyadicShellOscillation f C)
    (s : ℕ) {u q : ℕ} (hu : 1 ≤ u) (hlow : 2 ^ s * u ≤ q) (hhigh : q ≤ 2 ^ (s + 1) * u) :
    |f q - f u - (s : ℝ) * f 2| ≤ C ∧ |f q - f u| ≤ C + (s : ℝ) * |f 2| := by sorry

/-- Scaled-logarithm rigidity from bounded sub-shell downward drift across `[u, q]` and `[q, 2 * u]`. -/
theorem isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_subshell_downward_drift
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D M : ℝ} (hD : HasBoundedDownwardJumps f D)
    (hdrift : ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u →
      f u - f q ≤ M ∧ f q - f (2 * u) ≤ M) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by sorry

/-- Scaled-logarithm rigidity from bounded dyadic-shell descent counts. -/
theorem isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_shell_descent_card_le
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D : ℝ} (hD : HasBoundedDownwardJumps f D)
    {K : ℕ} (hcard : ∀ u : ℕ, 1 ≤ u → (Finset.Ico u (2 * u) ∩ descentFinset f (2 * u)).card ≤ K) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by sorry

/-- Scaled-logarithm rigidity from bit-length-zero half-open dyadic shell bounds `u ≤ q < 2 * u`. -/
theorem isScaledLogOnPos_of_isLittleO_descentCount_of_hasBoundedDownwardJumps_of_bitLength_zero_shell_bound
    {f : ℕ → ℝ} (hf : IsCoprimeAdditive f)
    (ho : (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)))
    {D B : ℝ} (hD : HasBoundedDownwardJumps f D)
    (hB : ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q < 2 * u → |f q - f u| ≤ B) :
    (∀ m : ℕ, 1 ≤ m → f m = (f 2 / Real.log 2) * Real.log (m : ℝ)) ∧ IsScaledLogOnPos f := by sorry

/-- Top-down conditional reduction of `Erdos1122Conjecture` via bounded downward jumps and sub-shell downward drift. -/
theorem erdos_1122_of_boundedDownwardJumps_and_subshell_downward_drift
    (hjump : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ D : ℝ, HasBoundedDownwardJumps f D)
    (hdrift : ∀ f : ℕ → ℝ, IsCoprimeAdditive f →
      (fun X : ℕ => (descentCount f X : ℝ)) =o[Filter.atTop] (fun X : ℕ => (X : ℝ)) →
      ∃ M : ℝ, ∀ u : ℕ, 1 ≤ u → ∀ q : ℕ, u ≤ q → q ≤ 2 * u →
        f u - f q ≤ M ∧ f q - f (2 * u) ≤ M) :
    Erdos1122Conjecture := by sorry

end Erdos1122.Core
end
