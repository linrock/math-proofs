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

Adaptation notice: Linmiao Xu adapted the definitions and four theorem statements
from google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/91.lean`).
This file imports only Mathlib.
-/

public import Mathlib

@[expose] public section

/-!
# Erdős Problem 91: small distinct-distance minimizer classifications

Let $d(n)$ denote the minimum number of distinct positive pairwise distances among
$n$-point planar configurations. This benchmark contains the four Formal Conjectures
small-case statements for $n = 3, 4, 6, 7$.
-/

open Finset

namespace Erdos91.Palomar

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The set of positive pairwise Euclidean distances determined by `points`. -/
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/-- The number of distinct positive distances determined by `points`. -/
noncomputable def distinctDistances {X : Type*} [MetricSpace X] (points : Finset X) : ℕ :=
  #(distanceSet points)

/-- The minimum number of distinct positive distances among $n$-point sets in $X$. -/
noncomputable def minimalDistinctDistances (X : Type*) [MetricSpace X] (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}

/-- A planar set $A$ is optimal if $|A| = n$ and it attains `minimalDistinctDistances Plane n`. -/
noncomputable def IsOptimal (A : Finset Plane) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances Plane n

/-- Two finite planar sets are similar if related by a `DilationEquiv`. -/
def DilationEquivSimilar (A B : Finset Plane) : Prop :=
  ∃ f : Plane ≃ᵈ Plane, (f '' (A : Set Plane)) = (B : Set Plane)

/-- Equilateral triangle with unit side length. -/
noncomputable def equiTriangle : Finset Plane :=
  {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]}

/-- Every optimal $n$-point planar configuration is similar to every other. -/
def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset Plane, IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

/-- For $n = 3$, the equilateral triangle is the unique optimal configuration. -/
theorem erdos_91_variants_three : UniqueMinimizer 3 := by sorry

/-- For $n = 4$, there are two nonsimilar optimal configurations. -/
theorem erdos_91_variants_four : ¬ UniqueMinimizer 4 := by sorry

/-- For $n = 6$, there are two nonsimilar optimal configurations. -/
theorem erdos_91_variants_six : ¬ UniqueMinimizer 6 := by sorry

/-- For $n = 7$, there are two nonsimilar optimal configurations. -/
theorem erdos_91_variants_seven : ¬ UniqueMinimizer 7 := by sorry

end Erdos91.Palomar
