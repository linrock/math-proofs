module

public import Mathlib


@[expose] public section

/-!
The exact Erdős #958 statement from `FormalConjectures/ErdosProblems/958.lean`
(Apache-2.0), recorded as a proposition definition with no admitted theorem.
The elaborated `answer(False)` is written as `False`.
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry Finset

namespace Erdos958.Challenge

open Finset EuclideanGeometry

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/-- The multiplicity of the distance `d` determined by `points`, that is, the number of unordered
pairs of distinct points at distance `d` apart. -/
noncomputable def distanceMultiplicity {X : Type*} [MetricSpace X] (points : Finset X) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) / 2

/-- `A` is a set of equidistant points on a line: there are a point `a` and a non-zero direction
`v` such that `A` consists of the points `a + i • v` for `0 ≤ i < #A`. -/
def IsEquidistantOnLine (A : Finset ℝ²) : Prop :=
  ∃ a v : ℝ², v ≠ 0 ∧ (A : Set ℝ²) = {x | ∃ i : ℕ, i < #A ∧ x = a + (i : ℝ) • v}

/-- `A` is a set of equidistant points on a circle: there are a centre `c`, a radius `r > 0`, an
initial angle `θ` and a non-zero angular step `α` such that `A` consists of the points of the
circle of centre `c` and radius `r` at the angles `θ + i * α` for `0 ≤ i < #A`. -/
def IsEquidistantOnCircle (A : Finset ℝ²) : Prop :=
  ∃ (c : ℝ²) (r θ α : ℝ), 0 < r ∧ α ≠ 0 ∧ (A : Set ℝ²) =
    {x | ∃ i : ℕ, i < #A ∧
      x = c + r • (!₂[Real.cos (θ + (i : ℝ) * α), Real.sin (θ + (i : ℝ) * α)])}

/-- Exact statement of Erdős Problem 958 (`FormalConjectures/ErdosProblems/958.lean`). -/
def statement : Prop :=
  False ↔
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ², #A = n →
      ((#(distanceSet A) = n - 1 ∧
            (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
        (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A))

end Erdos958.Challenge
