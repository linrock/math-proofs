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

public import Blueprint107

@[expose] public section

namespace Set

protected def Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

open Filter
open EuclideanGeometry

namespace EuclideanGeometry

def NonTrilinear (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

def ConvexIndep (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

def HasConvexNGon (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

end EuclideanGeometry

namespace Erdos107.Palomar

def cardSet (n : ℕ) := { N | ∀ (pts : Finset (EuclideanSpace ℝ (Fin 2))), pts.card = N →
  EuclideanGeometry.NonTrilinear (pts : Set (EuclideanSpace ℝ (Fin 2))) → EuclideanGeometry.HasConvexNGon n pts }

noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

private lemma cardSet_eq (n : ℕ) : cardSet n = Erdos107.cardSet n := rfl

private lemma f_eq (n : ℕ) : f n = Erdos107.f n := rfl

theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty := by
  intro n hn
  rw [cardSet_eq]
  exact Erdos107.nonempty_cardSet n hn

theorem f_le_erdosSzekeresUpper : ∀ n ≥ 3, f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  intro n hn
  rw [f_eq]
  exact Erdos107.f_le_erdosSzekeresUpper (by omega : 2 ≤ n)

theorem f_eq_conjectured_of_le_four : ∀ n, 3 ≤ n → n ≤ 4 → f n = 2 ^ (n - 2) + 1 := by
  intro n hn3 hn4
  rw [f_eq]
  exact Erdos107.f_eq_conjectured_of_le_four hn3 hn4

theorem ersz_bounds_of_le_five :
    ∀ n, 3 ≤ n → n ≤ 5 → 2 ^ (n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  intro n hn3 hn5
  rw [f_eq]
  exact Erdos107.ersz_bounds_of_le_five hn3 hn5

end Erdos107.Palomar
