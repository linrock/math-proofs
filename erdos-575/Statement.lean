module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 OpenAI.
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

public import Erdos575


@[expose] public section

/-!
The exact Erdős #575 statements from `FormalConjectures/ErdosProblems/575.lean`
(Apache-2.0), recorded as proposition definitions over the shared
`CompactnessConjecture.FiniteGraph` type with no admitted theorem.
The elaborated `answer(False)` is written as `False`.
-/

namespace Erdos575.Challenge

open CompactnessConjecture Erdos575 Filter SimpleGraph

/-- Exact cyclic statement of Erdős Problem 575 (`FormalConjectures/ErdosProblems/575.lean`). -/
def statement : Prop :=
  False ↔
    ∀ family : Finset FiniteGraph,
      family.Nonempty → IsCyclicFamily family →
        ContainsBipartiteMember family → IsBipartiteCompactFamily family

/-- Exact unrestricted statement of Erdős Problem 575 (`erdos_575.variants.unrestricted`). -/
def statement_unrestricted : Prop :=
  False ↔
    ∀ family : Finset FiniteGraph,
      family.Nonempty → ContainsBipartiteMember family → IsBipartiteCompactFamily family

end Erdos575.Challenge
