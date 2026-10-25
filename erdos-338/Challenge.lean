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

namespace Erdos338

open Filter

/-- `HasOrder A h` means that `A` is a basis of order at most `h`: every sufficiently large
natural number is a sum of at most `h` elements of `A`, with repetition allowed. -/
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = m

/-- `HasRestrictedOrder A t` means that every sufficiently large natural number is a sum of at
most `t` distinct elements of `A`. -/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ t ∧ ∑ x ∈ S, x = m

/-- The order of `A`: the least `h` with `HasOrder A h`, or `⊤` if `A` is not a basis. -/
noncomputable def basisOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (h : ℕ) (_ : HasOrder A h), (h : ℕ∞)

/-- The restricted order of `A`: the least `t` with `HasRestrictedOrder A t`, or `⊤` if no such `t`
exists. -/
noncomputable def restrictedOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : HasRestrictedOrder A t), (t : ℕ∞)

/-- The Hegyvári–Hennecart–Plagne bound: for every `k ≥ 2` there is a basis of order `k` whose
restricted order is $2^{k-2} + k - 1$. -/
theorem erdos_338.variants.hegyvari_hennecart_plagne :
    ∀ k : ℕ, 2 ≤ k → ∃ A : Set ℕ,
      basisOrder A = k ∧ restrictedOrder A = (2 ^ (k - 2) + k - 1 : ℕ) := by
  sorry

end Erdos338
