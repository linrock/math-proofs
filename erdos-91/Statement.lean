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
The exact Erdős #91 definitions and the four target statements from
`FormalConjectures/ErdosProblems/91.lean`, recorded as proposition definitions.
-/

open Finset

namespace Erdos91.Challenge

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def distanceSet {X : Type*} [MetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

noncomputable def distinctDistances {X : Type*} [MetricSpace X] (points : Finset X) : ℕ :=
  #(distanceSet points)

noncomputable def minimalDistinctDistances (X : Type*) [MetricSpace X] (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}

noncomputable def IsOptimal (A : Finset Plane) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances Plane n

def DilationEquivSimilar (A B : Finset Plane) : Prop :=
  ∃ f : Plane ≃ᵈ Plane, (f '' (A : Set Plane)) = (B : Set Plane)

noncomputable def equiTriangle : Finset Plane :=
  {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]}

def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset Plane, IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

def statement_three : Prop := UniqueMinimizer 3
def statement_four : Prop := ¬ UniqueMinimizer 4
def statement_six : Prop := ¬ UniqueMinimizer 6
def statement_seven : Prop := ¬ UniqueMinimizer 7

end Erdos91.Challenge
