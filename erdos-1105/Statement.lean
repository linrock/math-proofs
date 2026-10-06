module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
The exact Erdős #1105 statements (Parts (i) and (ii)), using the Apache-2.0
Formal Conjectures `IsRainbow` and `antiRamseyNum` definitions in
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex`.
These are proposition definitions with no admitted theorem. The elaborated
`answer(True)` is written as `True`.
-/

namespace Erdos1105.Challenge

open SimpleGraph Asymptotics Filter

/-- Exact statement of Erdős #1105, Part (i) (cycles). -/
def statement_i : Prop :=
  True ↔
    ∀ k, 3 ≤ k →
    ((fun n => (antiRamseyNum (cycleGraph k) n : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ)))

/-- Exact statement of Erdős #1105, Part (ii) (paths). -/
def statement_ii : Prop :=
  True ↔
    ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
      (ℓ - 1) * (n - ℓ + 1) + ε)

end Erdos1105.Challenge
