/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adaptation notice: Linmiao Xu adapted the Erdős 973 statement for this
standalone Lean 4.33.1 Challenge in 2026 and added the stronger local target.
-/

import Mathlib

/-!
# Independent statements for Erdős problem 973

`OriginalStatement` reproduces the mathematical statement from
google-deepmind/formal-conjectures at commit
`5d65ac9b140a00051fe2827fb10911beb2201b3b`, file
`FormalConjectures/ErdosProblems/973.lean` (SHA-256
`8096c57f6beda47615d508145f22e2ac26c277a5251d3f45d3cbcad08b4f6712`).
Its attribution is retained above. No upstream proof or local research module
is imported. The stronger target writes its power sum directly using Mathlib.

The two intentional challenge holes are matched by proved declarations in
`Solution.lean`; they are not proof evidence.
-/

noncomputable section

open scoped BigOperators
open Finset Filter

namespace Erdos973.Palomar

/-- One exponential base must work for every order, in the closed exterior. -/
def OriginalStatement : Prop :=
  ∃ C : ℝ, C > 1 ∧
    ∀ n : ℕ, n ≥ 2 → ∃ z : ℕ → ℂ,
      z 1 = 1 ∧
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) ∧
      (∀ k ∈ Icc 2 (n + 1), ‖∑ i ∈ Icc 1 n, z i ^ k‖ < C ^ (-(n : ℝ)))

/-- The exact original all-orders exterior-point statement has answer NO. -/
theorem not_erdos_973 : ¬ OriginalStatement := by
  sorry

/-- At every fixed exponential scale, the strict lower bound is eventually
uniform over all indexed exterior configurations, including repeated points. -/
theorem eventually_exterior_power_sum_strict_lower_bound (C : ℝ) (hC : 1 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Fin n → ℂ, (∀ i, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1), C ^ (-(n : ℝ)) < ‖∑ i : Fin n, z i ^ k‖ := by
  sorry

end Erdos973.Palomar
