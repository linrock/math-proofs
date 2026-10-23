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

open Filter
open scoped Topology
namespace Set
@[inline] noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ := ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop := Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)
end Set
namespace Erdos692
def exactlyOneDivisorIn (n m : ℕ) : Set ℕ := {x | {d ∈ Set.Ioo n m | d ∣ x}.ncard = 1}
def IsDelta₁ (n m : ℕ) (δ : ℝ) : Prop := (exactlyOneDivisorIn n m).HasDensity δ
def CambieThreeStatement : Prop := ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) → δ 3 7 < δ 3 6 ∧ δ 3 7 < δ 3 8
end Erdos692
