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
