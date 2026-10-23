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

public import CycleRepresentativeExchange
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
The exact Erdős #1105 statements (Parts (i) and (ii)) from
`FormalConjectures/ErdosProblems/1105.lean` (Apache-2.0), using the attributed
Formal Conjectures `SimpleGraph.IsRainbow` and `SimpleGraph.antiRamseyNum`
definitions in `CycleRepresentativeExchange`.
These are proposition definitions with no admitted theorem, stated in the
current upstream form (a plain proposition, without the retired `answer(True)`
wrapper).
-/

namespace Erdos1105.Challenge

open SimpleGraph Asymptotics Filter

/-- Exact statement of Erdős #1105, Part (i) (cycles). -/
def statement_i : Prop :=
  ∀ k, 3 ≤ k →
    ((fun n => (antiRamseyNum (cycleGraph k) n : ℝ) - ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ)))

/-- Exact statement of Erdős #1105, Part (ii) (paths). -/
def statement_ii : Prop :=
  ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n = max ((k - 2).choose 2 + 1) ((ℓ - 1).choose 2 +
      (ℓ - 1) * (n - ℓ + 1) + ε)

end Erdos1105.Challenge
