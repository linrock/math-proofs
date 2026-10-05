module

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
