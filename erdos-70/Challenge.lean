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

open Cardinal Ordinal
open scoped Cardinal

protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

theorem Set.Triplewise.mono {α : Type*} {r : α → α → α → Prop} {s t : Set α} (h : t ⊆ s)
    (hs : s.Triplewise r) : t.Triplewise r :=
  fun _ hx _ hy _ hz hxy hyz hxz ↦ hs (h hx) (h hy) (h hz) hxy hyz hxz

namespace Erdos70.Palomar

universe u

/-- `OrdinalCardinalRamsey3 α β c` asserts the 3-uniform ordinal Ramsey property `α → (β, c)³₂`. -/
def OrdinalCardinalRamsey3 (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    (∃ s : Set α.ToType, typeLT s = β ∧ s.Triplewise isRed) ∨
    (∃ s : Set α.ToType, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

/-- Unconditional ZFC refutation of `𝔠.ord → (ω₁, 4)³₂`. -/
theorem not_ordinalCardinalRamsey3_continuum_aleph1_four :
    ¬ OrdinalCardinalRamsey3.{0} (𝔠).ord (Cardinal.aleph 1).ord 4 := by
  sorry

/-- Negative resolution of `FormalConjectures` `erdos_70.variants.omega_one` (`answer(False)` elaborated as `False`). -/
theorem erdos_70_omega_one_refuted :
    False ↔
    ∀ᵉ (n : ℕ) (_ : 2 ≤ n),
      OrdinalCardinalRamsey3.{0} (𝔠).ord (Cardinal.aleph 1).ord n := by
  sorry

/-- Positive resolution of `𝔠.ord → (ω, 3)³₂`. -/
theorem ordinalCardinalRamsey3_continuum_omega_three :
    OrdinalCardinalRamsey3.{0} (𝔠).ord ω 3 := by
  sorry

/-- Positive resolution of `FormalConjectures` `erdos_70.variants.omega_three` (`answer(True)` elaborated as `True`). -/
theorem erdos_70_omega_three_solved :
    True ↔ OrdinalCardinalRamsey3.{0} (𝔠).ord ω 3 := by
  sorry

end Erdos70.Palomar
