module

public import Mathlib

@[expose] public section


/-!
The exact Erdős #1139 statement from `FormalConjectures/ErdosProblems/1139.lean`
(Apache-2.0), recorded as a proposition definition with no admitted theorem.
The elaborated `answer(True)` is written as `True`.
-/

namespace Erdos1139.Challenge

open Filter
open scoped ArithmeticFunction.Omega Topology

/-- Exact statement of Erdős Problem 1139 (`FormalConjectures/ErdosProblems/1139.lean`). -/
def statement : Prop :=
  True ↔
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤

end Erdos1139.Challenge
