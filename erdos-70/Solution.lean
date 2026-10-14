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

public import ContinuumTriplePartitions70

@[expose] public section

open Cardinal Ordinal
open scoped Cardinal

namespace Erdos70.Palomar

universe u

def OrdinalCardinalRamsey3 (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    (∃ s : Set α.ToType, typeLT s = β ∧ s.Triplewise isRed) ∨
    (∃ s : Set α.ToType, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

theorem not_ordinalCardinalRamsey3_continuum_aleph1_four :
    ¬ OrdinalCardinalRamsey3.{0} (𝔠).ord (Cardinal.aleph 1).ord 4 :=
  Erdos70.not_ordinalCardinalRamsey3_continuum_aleph1_four

theorem erdos_70_omega_one_refuted :
    False ↔
    ∀ᵉ (n : ℕ) (_ : 2 ≤ n),
      OrdinalCardinalRamsey3.{0} (𝔠).ord (Cardinal.aleph 1).ord n :=
  Erdos70.erdos_70_omega_one_refuted

theorem ordinalCardinalRamsey3_continuum_omega_three :
    OrdinalCardinalRamsey3.{0} (𝔠).ord ω 3 :=
  Erdos70.ordinalCardinalRamsey3_continuum_omega_three

theorem erdos_70_omega_three_solved :
    True ↔ OrdinalCardinalRamsey3.{0} (𝔠).ord ω 3 :=
  Erdos70.erdos_70_omega_three_solved

end Erdos70.Palomar
