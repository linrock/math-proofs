module

public import Mathlib


@[expose] public section

/-!
The exact Erdős #956 statement from `FormalConjectures/ErdosProblems/956.lean`
(Apache-2.0), recorded as a proposition definition with no admitted theorem.
The elaborated `answer(True)` is written as `True`.
-/

namespace Erdos956.Challenge

open Filter

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Minimum Euclidean distance between the sets $C+x$ and $C+y$. -/
noncomputable def translateDistance (C : Set Plane) (x y : Plane) : ℝ :=
  ⨅ c : C, ⨅ d : C, dist (c.1 + x) (d.1 + y)

/-- A family of pairwise disjoint translates of one nonempty compact convex set. -/
def IsConfiguration (C : Set Plane) (X : Finset Plane) : Prop :=
  C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
    ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint ((· + x) '' C) ((· + y) '' C)

open scoped Classical in
/-- The unordered pairs of distinct centers whose translates have set-distance one. -/
noncomputable def unitPairs (C : Set Plane) (X : Finset Plane) : Finset (Finset Plane) :=
  (X.powersetCard 2).filter fun e =>
    ∃ x y : Plane, x ≠ y ∧ e = {x, y} ∧ translateDistance C x y = 1

/-- The maximum number of unordered unit-distance pairs among $n$ disjoint convex translates. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
    X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m}

/-- Exact statement of Erdős Problem 956 (`FormalConjectures/ErdosProblems/956.lean`). -/
def statement : Prop :=
  True ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < (h n : ℝ)

end Erdos956.Challenge
