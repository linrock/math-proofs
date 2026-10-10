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
-/

public import RamseyBasics546
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt


@[expose] public section

/-!
The exact Erdős #546 statement from `FormalConjectures/ErdosProblems/546.lean`
(Apache-2.0), recorded as a proposition definition over `SimpleGraph.diagonalGraphRamsey`
with no admitted theorem. The elaborated `answer(True)` is written as `True`.
-/

namespace Erdos546.Challenge

/-- Exact statement of Erdős Problem 546 (`FormalConjectures/ErdosProblems/546.lean`). -/
def statement : Prop :=
  True ↔
    ∃ C > (0 : ℝ), ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
      (∀ v, 0 < G.degree v) →
      G.edgeSet.ncard = m →
      (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ (C * Real.sqrt m)

end Erdos546.Challenge
