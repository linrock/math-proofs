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

public import ActualOfficialSolution433

@[expose] public section


/-!
# Erdős #689: proved eventual double covering

The advertised type is written out independently of the challenge. The
canonical original-statement capstone discharges it without mathematical
hypotheses. This module never imports the challenge.
-/

open Filter
open scoped Topology

namespace Erdos689.Palomar

/-- Every sufficiently large initial interval admits one selected residue
class per available prime that covers every target at least twice. -/
theorem eventual_double_cover :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ a : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n,
        2 ≤ ((Finset.Icc 1 n).filter
          fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  exact _root_.Erdos689.erdos_689_original_statement

end Erdos689.Palomar

#print axioms Erdos689.Palomar.eventual_double_cover
