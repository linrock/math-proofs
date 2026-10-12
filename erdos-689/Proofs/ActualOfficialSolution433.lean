module

/-
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

public import ActualMajorArcFinalCoupling433

@[expose] public section


open Filter Finset
open scoped Topology

namespace Erdos689

/-- The verbatim proposition on the right-hand side of the upstream
formal-conjectures statement for Erdős problem #689. -/
theorem erdos_689_original_statement :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ a : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n,
        2 ≤ ((Finset.Icc 1 n).filter
          fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  exact officialStatement_unconditional

#print axioms Erdos689.officialStatement_unconditional
#print axioms Erdos689.erdos_689_original_statement

end Erdos689
