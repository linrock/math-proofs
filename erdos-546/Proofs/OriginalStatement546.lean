module

/-
Copyright 2026 The Formal Conjectures Authors.
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

The statement is adapted from the pinned Formal Conjectures #546 file.
-/
public import Sudakov546


@[expose] public section

/-!
# Root-level Formal Conjectures statement for Erdős #546

Proves the literal theorem statement from `FormalConjectures/ErdosProblems/546.lean`
(with `answer(True)` elaborated as `True`) at root scope.
-/

theorem erdos_546_original_statement : True ↔
    ∃ C > (0 : ℝ), ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
      (∀ v, 0 < G.degree v) →
      G.edgeSet.ncard = m →
      (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ (C * Real.sqrt m) := by
  exact Erdos546.erdos_546
