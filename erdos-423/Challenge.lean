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

/-!
# Erdős Problem 423: Hofstadter Consecutive-Block-Sum Sequence

Let `a(1) = 1`, `a(2) = 2`, and, for `k ≥ 3`, let `a(k)` be the least integer greater than
`a(k-1)` representable as a sum of at least two consecutive earlier terms. Erdős and Graham
asked whether this Hofstadter sequence satisfies `a n = n + o(n)`. The package proves that the
excess `a n - n` is unbounded and that the sequence omits infinitely many positive integers,
adapting the 2026 arguments of Bolan and Tang, and re-proves the nondecreasing-excess variant
(already formalized independently by Anatolii Ohorodnyk in `lean-fc-proofs`).

The proof also builds uniqueness, exact omitted-value counting, global block-sum closure, and
prefix-difference bounds. A completed-square Ramanujan--Nagell obstruction refutes eventual
linear stabilization and yields an explicit iterated excess tower. The final exported section
turns control of that tower into conditional stage-reductions toward the remaining lower-bound, upper-bound,
and main-asymptotic questions.
-/

noncomputable section
open Finset BigOperators Filter Asymptotics

namespace Erdos423

attribute [local instance] Classical.propDecidable

/-- `IsConsecutiveBlockSum a k m` means that `m` equals the sum of at least two
consecutive terms of the sequence `a`, using indices from `{1, ..., k - 1}`. -/
def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

/-- The Hofstadter sequence (OEIS A005243): `a(1) = 1`, `a(2) = 2`, and for `k ≥ 3`,
`a(k)` is the least integer `> a(k-1)` that equals the sum of at least two consecutive terms from
`{a(1), ..., a(k-1)}`. -/
def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

/-- `IsGlobalConsecutiveBlockSum a m` means `m = ∑ l ∈ Finset.Icc i j, a l` for some `1 ≤ i` and `i + 1 ≤ j`. -/
def IsGlobalConsecutiveBlockSum (a : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ m = ∑ l ∈ Finset.Icc i j, a l

/-- Prefix sum `prefixSum a n = ∑ l ∈ Finset.Icc 1 n, a l`. -/
def prefixSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ l ∈ Finset.Icc 1 n, a l

/-- Signed Ramanujan–Nagell discriminant offset
`D(n₀, C, i) = 8 * (P(n₀ - 1) - P(i - 1)) - (2n₀ + 2C - 1)^2` in `ℤ`. -/
def discriminantOffset (a : ℕ → ℕ) (n₀ C i : ℕ) : ℤ :=
  8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1) : ℤ) - (((2 * n₀ + 2 * C - 1) ^ 2 : ℕ) : ℤ)

/-- Prefix-index exponent fiber in a window `[r₀, r₀ + K)`: the finset of exponents
`r ∈ Finset.Ico r₀ (r₀ + K)` for which the completed-square equation
`(2 * v + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) = 2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2`
admits a solution `v : ℕ`. -/
def completedSquareExpFiber (a : ℕ → ℕ) (n₀ C r₀ K i : ℕ) : Finset ℕ :=
  (Finset.Ico r₀ (r₀ + K)).filter (fun r =>
    ∃ v : ℕ, (2 * v + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) =
      2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2)

/-- Quantitative exponent horizon
`r₀(a, n₀, C) = max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀`. -/
def stabilizationExpHorizon (a : ℕ → ℕ) (n₀ C : ℕ) : ℕ :=
  max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀

/-- Quantitative index horizon `n₁(a, n₀, C) = 2 ^ r₀(a, n₀, C) + C` bounding the first
stabilization-breaking index above `n₀`. -/
def stabilizationIndexHorizon (a : ℕ → ℕ) (n₀ C : ℕ) : ℕ :=
  2 ^ (stabilizationExpHorizon a n₀ C) + C

/-- Constructive one-step excess-jump horizon `nextExcessHorizon a n₀ = n₁(a, n₀, a n₀ - n₀)`. -/
def nextExcessHorizon (a : ℕ → ℕ) (n₀ : ℕ) : ℕ :=
  stabilizationIndexHorizon a n₀ (a n₀ - n₀)

/-- Iterated excess-jump tower `iterExcessHorizon a k = (nextExcessHorizon a)^[k] 1`. -/
def iterExcessHorizon (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  (nextExcessHorizon a)^[k] 1

/-- Solved Formal Conjectures variant `erdos_423.variants.nondecreasing` (Bolan and Tang, independently, 2026): the excess sequence `a n - n` of any Hofstadter consecutive-block-sum sequence is nondecreasing for `1 ≤ n ≤ m`. Re-proof of a variant already formalized independently by Anatolii Ohorodnyk (`anatoliiohorodnyk/lean-fc-proofs`); not claimed as a new contribution. -/
theorem erdos_423.variants.nondecreasing : ∀ a : ℕ → ℕ, IsHofstadterSeq a → ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m := by sorry

/-- Solved Formal Conjectures variant `erdos_423.variants.unbounded` (Bolan and Tang, independently, 2026): the excess `a n - n` diverges to infinity (`∀ M, ∀ᶠ n in atTop, M + n ≤ a n`). -/
theorem erdos_423.variants.unbounded : ∀ a : ℕ → ℕ, IsHofstadterSeq a → ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n := by sorry

/-- Solved Formal Conjectures variant `erdos_423.variants.infinite_complement` (Bolan and Tang, independently, 2026): the Hofstadter consecutive-block-sum sequence omits infinitely many positive integers. -/
theorem erdos_423.variants.infinite_complement : ∀ a : ℕ → ℕ, IsHofstadterSeq a → Set.Infinite (Set.range a)ᶜ := by sorry

/-- Existence and uniqueness of the `0`-anchored Hofstadter consecutive-block-sum sequence (`a 0 = 0 ∧ IsHofstadterSeq a`). -/
theorem existsUnique_isHofstadterSeq : ∃! a : ℕ → ℕ, a 0 = 0 ∧ IsHofstadterSeq a := by sorry

/-- Exact omitted-integer counting identity: for every `n ≥ 1`, the number of positive integers in `[1, a n]` omitted by `a([1, n])` equals the excess `a n - n`. -/
theorem IsHofstadterSeq_card_omitted_Icc_eq_sub {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {n : ℕ} (hn : 1 ≤ n) : ((Finset.Icc 1 (a n)) \ ((Finset.Icc 1 n).image a)).card = a n - n := by sorry

/-- Global consecutive-block-sum closure theorem: an integer `m` appears in the Hofstadter sequence at some index `k ≥ 3` if and only if `m` is the sum of at least two consecutive terms of `a`. -/
theorem IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (m : ℕ) : (∃ k : ℕ, 3 ≤ k ∧ a k = m) ↔ IsGlobalConsecutiveBlockSum a m := by sorry

/-- Bolan–Tang convex prefix-difference cardinality bound: whenever `1 ≤ m`, `1 ≤ N`, and `prefixSum a m ≤ a N`, the distinct positive prefix differences on `{0, ..., m}` force `2 * m - 1 ≤ N`. -/
theorem two_mul_sub_one_le_of_prefixSum_le : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N → prefixSum a m ≤ a N → 2 * m - 1 ≤ N := by sorry

/-- Unconditional strict excess jump across power-of-two consecutive block sums: if `1 ≤ i`, `i + 1 ≤ j`, and `∑ l ∈ Finset.Icc i j, a l = 2 ^ r`, then `a i - i < a j - j`. -/
theorem strict_excess_increase_of_blockSum_eq_two_pow : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j r : ℕ), 1 ≤ i → i + 1 ≤ j → ∑ l ∈ Finset.Icc i j, a l = 2 ^ r → a i - i < a j - j := by sorry

/-- Universal algebraic completed-square identity `4 * ((j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀))) + (2 * n₀ + 2 * C - 1) ^ 2 = (2 * j + 2 * C + 1) ^ 2` for `1 ≤ n₀ ≤ j`. -/
theorem completed_square_tail_quadratic_identity : ∀ (n₀ C j : ℕ), 1 ≤ n₀ → n₀ ≤ j → 4 * ((j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀))) + (2 * n₀ + 2 * C - 1) ^ 2 = (2 * j + 2 * C + 1) ^ 2 := by sorry

/-- Completed-square Ramanujan–Nagell discriminant identity for power-of-two block sums across an eventually linear tail `a n = n + C` (`n ≥ n₀ ≥ 1`). -/
theorem exists_completed_square_discriminant_of_two_pow : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r : ℕ), 1 ≤ n₀ → (∀ n : ℕ, n₀ ≤ n → a n = n + C) → max n₀ 3 + C ≤ 2 ^ r → prefixSum a (n₀ - 1) < 2 ^ r → ∃ i j : ℕ, 1 ≤ i ∧ i < n₀ ∧ n₀ ≤ j ∧ (2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) = 2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2 := by sorry

/-- Modulo-8 non-degeneracy of the Ramanujan–Nagell discriminant offset: `discriminantOffset a n₀ C i % 8 = 7` for all `n₀ ≥ 1`. -/
theorem discriminantOffset_emod_eight : ∀ (a : ℕ → ℕ) (n₀ C i : ℕ), 1 ≤ n₀ → discriminantOffset a n₀ C i % 8 = 7 := by sorry

/-- Exact 2-adic difference-of-squares factorization `(v₂ - v₁) * (v₂ + v₁ + 1) = 2 ^ (r₁ + 1) * (2 ^ (r₂ - r₁) - 1)` for two completed-square solutions sharing the same prefix offset. -/
theorem completed_square_collision_factor_eq : ∀ (A B v₁ v₂ r₁ r₂ : ℕ), r₁ ≤ r₂ → v₁ ≤ v₂ → (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B → (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B → (v₂ - v₁) * (v₂ + v₁ + 1) = 2 ^ (r₁ + 1) * (2 ^ (r₂ - r₁) - 1) := by sorry

/-- Exponential lower bound `2 ^ (r₁ + 1) ≤ v₂ + v₁ + 1` and `2 ^ r₁ ≤ v₂` from opposite-parity 2-adic divisibility across a completed-square collision `r₁ < r₂`. -/
theorem two_pow_le_of_completed_square_collision : ∀ (A B v₁ v₂ r₁ r₂ : ℕ), r₁ < r₂ → (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B → (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B → 2 ^ (r₁ + 1) ≤ v₂ + v₁ + 1 ∧ 2 ^ r₁ ≤ v₂ := by sorry

/-- Exponent-doubling gap `2 * r₁ ≤ r₂ + 1` between any two distinct solutions `r₁ < r₂` in the same completed-square prefix fiber once `B ≤ 2 ^ (r₁ + 3)`. -/
theorem two_mul_le_succ_of_completed_square_collision : ∀ (A B v₁ v₂ r₁ r₂ : ℕ), r₁ < r₂ → B ≤ 2 ^ (r₁ + 3) → (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B → (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B → 2 * r₁ ≤ r₂ + 1 := by sorry

/-- Subsingleton fiber bound: on any exponent window `[r₀, r₀ + K)` with `K + 1 ≤ r₀` and `(2 * n₀ + 2 * C - 1) ^ 2 ≤ r₀`, each prefix fiber `completedSquareExpFiber a n₀ C r₀ K i` has cardinality at most `1`. -/
theorem completedSquareExpFiber_card_le_one : ∀ (a : ℕ → ℕ) (n₀ C r₀ K i : ℕ), K + 1 ≤ r₀ → (2 * n₀ + 2 * C - 1) ^ 2 ≤ r₀ → (completedSquareExpFiber a n₀ C r₀ K i).card ≤ 1 := by sorry

/-- Unconditional refutation of eventual linear stabilization: for every `n₀ ≥ 1` and `C : ℕ`, no Hofstadter sequence can satisfy `a n = n + C` for all `n ≥ n₀`. -/
theorem not_eventual_linear_of_isHofstadterSeq : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ), 1 ≤ n₀ → ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C) := by sorry

/-- Quantitative finite-horizon stabilization-breaking bound: for every `n₀ ≥ 1` and `C : ℕ`, there exists `n₁ ∈ [n₀, 2 ^ r₀ + C]` such that `a n₁ ≠ n₁ + C`, where `r₀ = max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀`. -/
theorem exists_stabilization_breaking_index_le : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ), 1 ≤ n₀ → let r₀ := max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀; ∃ n₁ : ℕ, n₀ ≤ n₁ ∧ n₁ ≤ 2 ^ r₀ + C ∧ a n₁ ≠ n₁ + C := by sorry

/-- Strict excess increase at the explicit index horizon `stabilizationIndexHorizon a n₀ C = 2 ^ r₀ + C` whenever `1 ≤ n₀` and `a n₀ - n₀ ≤ C`. -/
theorem strict_excess_increase_at_stabilizationIndexHorizon : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ), 1 ≤ n₀ → a n₀ - n₀ ≤ C → a n₀ - n₀ < a (stabilizationIndexHorizon a n₀ C) - stabilizationIndexHorizon a n₀ C := by sorry

/-- Constructive tail excess guarantee along the iterated excess-jump tower: for every `k : ℕ` and `n ≥ iterExcessHorizon a k`, `k ≤ a n - n` and `k + n ≤ a n`. -/
theorem le_excess_of_iterExcessHorizon_le : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (k n : ℕ), iterExcessHorizon a k ≤ n → k ≤ a n - n ∧ k + n ≤ a n := by sorry

/-- Exact base checkpoint evaluation `iterExcessHorizon a 1 = 16` for every Hofstadter consecutive-block-sum sequence `a`. -/
theorem iterExcessHorizon_one_eq_sixteen : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → iterExcessHorizon a 1 = 16 := by sorry

/-- Single-step exponential upper bound `nextExcessHorizon a n₀ ≤ 2 ^ (5 * (a n₀) ^ 2) + a n₀` in terms of `a n₀` (`1 ≤ n₀`). -/
theorem nextExcessHorizon_le_two_pow_five_mul_sq_add : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ : ℕ), 1 ≤ n₀ → nextExcessHorizon a n₀ ≤ 2 ^ (5 * (a n₀) ^ 2) + a n₀ := by sorry

/-- Conditional stage-interval tower reduction toward `erdos_423.variants.lower_bound` (the tower hypothesis is not discharged here): linear control of `log (log (iterExcessHorizon a (k + 1))) ≤ B * k` across tower checkpoints implies `(fun n => Real.log (Real.log n)) =O[atTop] (fun n => (a n : ℝ) - n)`. -/
theorem erdos_423_variants_lower_bound_of_iterExcessHorizon_log_log_le : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (B : ℝ), 0 ≤ B → (∀ k : ℕ, 1 ≤ k → Real.log (Real.log (iterExcessHorizon a (k + 1) : ℝ)) ≤ B * (k : ℝ)) → (fun n : ℕ => Real.log (Real.log n)) =O[atTop] (fun n : ℕ => (a n : ℝ) - n) := by sorry

/-- Conditional stage-interval tower reduction toward `erdos_423.variants.upper_bound` (the tower hypothesis is not discharged here): power-law control of the excess at `iterExcessHorizon a (k + 1)` in terms of `(iterExcessHorizon a k) ^ (688 / 413 + ε)` implies `(fun n => (a n : ℝ)) =O[atTop] (fun n => (n : ℝ) ^ (688 / 413 + ε))`. -/
theorem erdos_423_variants_upper_bound_of_iterExcessHorizon_rpow_le : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (ε B : ℝ), 0 < ε → 0 ≤ B → (∀ k : ℕ, 1 ≤ k → ((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) ≤ B * (iterExcessHorizon a k : ℝ) ^ ((688 : ℝ) / 413 + ε)) → (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((688 : ℝ) / 413 + ε)) := by sorry

/-- Conditional stage-interval tower reduction toward the open main conjecture `erdos_423` (the tower hypothesis is not discharged here): sublinear checkpoint control `a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) ≤ ε * iterExcessHorizon a k` for `k ≥ K₀(ε)` implies `(fun n => (a n : ℝ) - n) =o[atTop] (fun n => (n : ℝ))`. -/
theorem erdos_423_of_iterExcessHorizon_littleO_bound : ∀ (a : ℕ → ℕ), IsHofstadterSeq a → (∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k → ((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) ≤ ε * (iterExcessHorizon a k : ℝ)) → (fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ)) := by sorry

end Erdos423

end
