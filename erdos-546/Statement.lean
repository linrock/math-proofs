module

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
