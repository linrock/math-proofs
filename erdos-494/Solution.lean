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

public import SelfridgeStrausSumMultiset494

@[expose] public section

namespace Erdos494.Palomar

theorem erdos_494_variants_k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494.Erdos494Unique 2 card :=
  Erdos494.erdos_494.variants.k_eq_2_card_not_pow_two

theorem erdos_494_variants_k_eq_3_card_gt_6 :
    ∀ card > 6, card ≠ 27 → card ≠ 486 → Erdos494.Erdos494Unique 3 card :=
  Erdos494.erdos_494.variants.k_eq_3_card_gt_6

end Erdos494.Palomar
