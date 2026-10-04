module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Erdős research contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The statement is adapted from the pinned Formal Conjectures #546 file.
-/
public import Sudakov546


@[expose] public section

/-! Literal statement check against FormalConjectures/ErdosProblems/546.lean.
`True` is the expansion of its `answer(True)` term. This declaration sits
outside the research namespace and spells out every original quantifier.
It is part of the complete saved-source replay and transitive axiom audit. -/

theorem erdos_546_original_statement : True ↔
    ∃ C > (0 : ℝ), ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
      (∀ v, 0 < G.degree v) →
      G.edgeSet.ncard = m →
      (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ (C * Real.sqrt m) := by
  exact Erdos546.erdos_546

#print axioms erdos_546_original_statement
