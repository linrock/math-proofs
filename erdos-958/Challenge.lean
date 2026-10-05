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

Adaptation notice: Linmiao Xu adapted the Erdős 958 definitions and statement
from google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/958.lean`)
and added the explicit Clemen–Dumitrescu–Liu counterexample targets for all
`n ≥ 4`, the universal collinear multiplicity-profile target, and the circular
equidistant existence target for this standalone Lean 4 benchmark in 2026. This
file imports only Mathlib.
-/

public import Mathlib


@[expose] public section

/-!
# Erdős Problem 958: planar point sets with distance multiplicities `{1, ..., n - 1}`

Let $A \subset \mathbb{R}^2$ be a finite point set of size $n$, let
$\{d_1, \dots, d_k\}$ be the set of distinct interpoint distances determined by $A$,
and let $f(d)$ denote the multiplicity of $d$ (the number of unordered pairs from $A$
at distance $d$). Erdős asked whether for all sufficiently large $n$, having
$k = n - 1$ and $\{f(d_1), \dots, f(d_k)\} = \{1, \dots, n - 1\}$ implies that $A$
consists of equidistant points on a line or a circle, and conjectured that the answer
is no.

Clemen, Dumitrescu, and Liu (arXiv:2505.04283, 2025) disproved the classification by
showing that $n - 1$ equidistant points on a sufficiently short circular arc of the
unit circle together with the center $(0, 0)$ determine $n - 1$ distinct distances
with multiplicities $\{1, \dots, n - 1\}$ while neither being equidistant on a line
nor equidistant on a circle.

The five intentional `sorry` placeholders below are matched by proved declarations
in `Solution.lean`; `Solution.lean` does not import this module.
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry Finset

namespace Erdos958.Palomar

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

/-- Elaborated Formal Conjectures `False ↔` form of Erdős Problem 958. -/
theorem erdos_958 : False ↔
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ², #A = n →
      ((#(distanceSet A) = n - 1 ∧
            (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
        (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A)) := by
  sorry

/-- Direct disproof of the Erdős #958 large-`n` classification statement. -/
theorem not_erdos_958 :
    ¬ (∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ², #A = n →
      ((#(distanceSet A) = n - 1 ∧
            (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
        (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A))) := by
  sorry

/-- Clemen–Dumitrescu–Liu theorem (2025): for every `n ≥ 4`, there exists an `n`-point
configuration in `ℝ²` determining `n - 1` distinct distances with multiplicities
`{1, ..., n - 1}` that is neither equidistant on a line nor equidistant on a circle. -/
theorem clemen_dumitrescu_liu (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : Finset ℝ², #A = n ∧
      #(distanceSet A) = n - 1 ∧
      (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1) ∧
      ¬ IsEquidistantOnLine A ∧ ¬ IsEquidistantOnCircle A := by
  sorry

/-- Positive direction for collinear equidistant configurations: every finite set
`A ⊂ ℝ²` with `#A ≥ 2` satisfying `IsEquidistantOnLine A` determines `#A - 1`
distinct distances with multiplicities `{1, ..., #A - 1}`. -/
theorem equidistantOnLine_has_profile (A : Finset ℝ²) (hA : 2 ≤ #A)
    (hline : IsEquidistantOnLine A) :
    #(distanceSet A) = #A - 1 ∧
      (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (#A - 1) := by
  sorry

/-- Existence of circular equidistant configurations with the target profile: for every
`n ≥ 2`, there exists an `n`-point configuration on a circle (`IsEquidistantOnCircle`)
determining `n - 1` distinct distances with multiplicities `{1, ..., n - 1}`. -/
theorem equidistantOnCircle_exists_has_profile (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset ℝ², #A = n ∧
      IsEquidistantOnCircle A ∧
      #(distanceSet A) = n - 1 ∧
      (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1) := by
  sorry

end Erdos958.Palomar
