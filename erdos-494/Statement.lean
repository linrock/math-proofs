module

/-
Copyright 2025 The Formal Conjectures Authors.
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

namespace Erdos494

noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

end Erdos494

namespace Erdos494.Palomar

def KEqTwoCardNotPowTwoStatement : Prop :=
  ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494.Erdos494Unique 2 card

def KEqThreeCardGtSixStatement : Prop :=
  ∀ card > 6, card ≠ 27 → card ≠ 486 → Erdos494.Erdos494Unique 3 card

end Erdos494.Palomar
