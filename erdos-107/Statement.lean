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

namespace Set

protected def Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Filter
open EuclideanGeometry

namespace EuclideanGeometry

def NonTrilinear (A : Set ℝ²) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

def HasConvexNGon (n : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

end EuclideanGeometry

namespace Erdos107.Palomar

def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

def NonemptyCardSetStatement : Prop :=
  ∀ n ≥ 3, (cardSet n).Nonempty

def ErdosSzekeresUpperStatement : Prop :=
  ∀ n ≥ 3, f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

def HappyEndingFourStatement : Prop :=
  ∀ n, 3 ≤ n → n ≤ 4 → f n = 2 ^ (n - 2) + 1

def ErdosSzekeresBoundsLeFiveStatement : Prop :=
  ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

end Erdos107.Palomar
