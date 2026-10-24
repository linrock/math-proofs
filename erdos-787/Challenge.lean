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
# Erdős Problem 787

The statement `erdos_787.variants.klarner`, together with the definition of
`Finset.restrictedSumset` used to state it.
-/

open Filter
open scoped Finset

namespace Finset

variable {α : Type*} [Add α] [DecidableEq α]

/--
The restricted sumset of a set $S$, denoted $S \hat{+} S$, is the set
$\lbrace s_1 + s_2 : s_1, s_2 \in S, s_1 \neq s_2 \rbrace$.
-/
def restrictedSumset (S : Finset α) : Finset α :=
  S.offDiag.image (fun p => p.1 + p.2)

end Finset

namespace Erdos787

/-- `g G n` is the largest `m` such that every `n`-element subset `A` of `G` has a
subset `B` with `|B| ≥ m` and `Disjoint B.restrictedSumset A`. -/
noncomputable def g (G : Type*) [Add G] [DecidableEq G] (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset G, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A}

/-- Klarner's lower bound: there exists a positive constant `c` such that eventually
`c * log n ≤ g ℝ n`. -/
theorem variants.klarner :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ (g ℝ n : ℝ) := by
  sorry

end Erdos787
