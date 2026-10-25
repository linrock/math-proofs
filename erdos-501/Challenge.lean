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

open Set MeasureTheory
open scoped ENNReal

namespace Erdos501

/--
**Erdős–Hajnal (1960): arbitrarily large finite independent sets exist.**

For every `n : ℕ` and every family `A : ℝ → Set ℝ` of bounded sets with Lebesgue
outer measure `< 1`, there exists a finite independent set of size at least `n`.
-/
theorem erdos_501.variants.erdosHajnal_finite :
    ∀ (n : ℕ) (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) →
      (∀ x, volume.toOuterMeasure (A x) < 1) →
      ∃ X : Finset ℝ, n ≤ X.card ∧ (X : Set ℝ).Pairwise (fun x y => x ∉ A y) := by
  sorry

end Erdos501
