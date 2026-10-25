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

public import Mathlib

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
open Filter Finset EuclideanGeometry
namespace EuclideanGeometry
noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2
noncomputable def distinctDistances {X : Type*} [MetricSpace X] (points : Finset X) : ℕ :=
  #(distanceSet points)
noncomputable def minimalDistinctDistances (X : Type*) [MetricSpace X] (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}
end EuclideanGeometry
namespace Erdos661
variable {X : Type*} [MetricSpace X]
noncomputable def crossDistanceSet (A B : Finset X) : Finset ℝ :=
  (A ×ˢ B).image fun p : X × X => dist p.1 p.2
variable (X) in
noncomputable def minimalCrossDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A B : Finset X, #A = n ∧ #B = n ∧ Disjoint A B ∧ #(crossDistanceSet A B) = m}
theorem erdos_661_variants_lenz (n : ℕ) :
    ∃ A B : Finset (EuclideanSpace ℝ (Fin 4)), #A = n ∧ #B = n ∧ Disjoint A B ∧
      ∀ x ∈ A, ∀ y ∈ B, dist x y = 1 := by sorry
end Erdos661
