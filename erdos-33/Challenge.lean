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

Adaptation notice: Linmiao Xu adapted `AdditiveBasisCondition`,
`erdos_33.variants.one_mem_lowerBounds`, and `erdos_33.variants.vanDoorn` from
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/33.lean`)
and added the Moser weighted-representation bound, the Cilleruelo step-function
lower bounds $5/4 = 1.25$, $63/50 = 1.26$, and $127/100 = 1.27$, the Fibonacci
van Doorn construction, and block-ratio bounds for this standalone Lean 4
benchmark in 2026. This file imports only Mathlib.
-/

public import Mathlib

@[expose] public section

open Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Erdos33

/-- `AdditiveBasisCondition A` states that every natural number $k$ can be written as $a + n^2$
for some $a \in A$ and $n \in \mathbb{N}$. -/
def AdditiveBasisCondition (A : Set ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (n : ℕ) (a : ℕ), a ∈ A ∧ k = a + n ^ 2

/-- Equivalent formulation $n = k^2 + a$ (`IsSquareAdditiveComplement A`). -/
def IsSquareAdditiveComplement (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ a ∈ A, ∃ k : ℕ, n = k ^ 2 + a

/-- Prefix count $|A \cap \{1, \dots, N\}|$. -/
noncomputable def prefixCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/-- Normalized prefix ratio $|A \cap \{1, \dots, N\}| / \sqrt{N}$. -/
noncomputable def normalizedPrefixRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  (prefixCount A N : ℝ) / Real.sqrt (N : ℝ)

/-- Van Doorn block $[B, B + 2M]$. -/
def vanDoornBlock (B M : ℕ) : Set ℕ :=
  {a : ℕ | B ≤ a ∧ a ≤ B + 2 * M}

/-- Recursive start points $B_{j+1} = B_j + M_j^2 + 2 M_j$ with $B_0 = 0$. -/
def vanDoornBlockStart (M : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.rec 0 (fun k acc => acc + (M k) ^ 2 + 2 * M k) j

/-- Union of van Doorn blocks $\bigcup_{j \in \mathbb{N}} [B_j, B_j + 2 M_j]$. -/
def vanDoornUnion (M : ℕ → ℕ) : Set ℕ :=
  ⋃ j : ℕ, vanDoornBlock (vanDoornBlockStart M j) (M j)

/-- Fibonacci block widths $M_j = F_{j+2}$. -/
def fibBlockWidth (j : ℕ) : ℕ := Nat.fib (j + 2)

/-- Solved lower bound $> 1$ (`FormalConjectures` `erdos_33.variants.one_mem_lowerBounds`). -/
theorem erdos_33_variants_one_mem_lowerBounds :
    1 < ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) := by
  sorry

/-- Van Doorn's $2 \varphi^{5/2}$ upper bound (`FormalConjectures` `erdos_33.variants.vanDoorn`). -/
theorem erdos_33_variants_vanDoorn :
    (⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal))) ≤
        ((2 * Real.goldenRatio ^ ((5 : ℝ) / 2) : ℝ) : EReal) := by
  sorry

/-- Strengthened Cilleruelo step-function lower bound $63/50 = 1.26$ on the `erdos_33` infimum. -/
theorem sixty_three_fiftieths_le_iInf_limsup :
    (((63 : ℝ) / 50 : ℝ) : EReal) ≤
      ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
        ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) := by
  sorry

/-- Every square additive complement $A$ achieves $|A \cap [1, N]| / \sqrt{N} \ge 63/50$ for arbitrarily large $N$. -/
theorem exists_ge_sixty_three_fiftieths_normalizedPrefixRatio
    {A : Set ℕ} (hA : IsSquareAdditiveComplement A) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ (63 : ℝ) / 50 ≤ normalizedPrefixRatio A N := by
  sorry

/-- Every van Doorn union with positive block widths $M_j \ge 1$ satisfies `AdditiveBasisCondition`. -/
theorem additiveBasisCondition_vanDoornUnion {M : ℕ → ℕ} (hM : ∀ j : ℕ, 1 ≤ M j) :
    AdditiveBasisCondition (vanDoornUnion M) := by
  sorry

/-- Unconditional main-term Fibonacci block-ratio bound: for all $K \ge 1$,
$2 \sum_{j=0}^K F_{j+2} / \sqrt{B_K} \le 2 \varphi^{5/2}$. -/
theorem two_mul_sum_fibBlockWidth_div_sqrt_start_le {K : ℕ} (hK : 1 ≤ K) :
    (2 * ((∑ j ∈ Finset.range (K + 1), fibBlockWidth j : ℕ) : ℝ)) /
      Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) ≤
        2 * Real.goldenRatio ^ ((5 : ℝ) / 2) := by
  sorry

/-- Strengthened Cilleruelo step-function lower bound $127/100 = 1.27$ on the `erdos_33` infimum (via $R = 500$, $S(500) = 196{,}830$). -/
theorem one_hundred_twenty_seven_over_one_hundred_le_iInf_limsup :
    (((127 : ℝ) / 100 : ℝ) : EReal) ≤
      ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
        ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) := by
  sorry

/-- Every square additive complement $A$ achieves $|A \cap [1, N]| / \sqrt{N} \ge 127/100 = 1.27$ for arbitrarily large $N$. -/
theorem exists_ge_one_hundred_twenty_seven_over_one_hundred_normalizedPrefixRatio
    {A : Set ℕ} (hA : IsSquareAdditiveComplement A) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ (127 : ℝ) / 100 ≤ normalizedPrefixRatio A N := by
  sorry

end Erdos33
