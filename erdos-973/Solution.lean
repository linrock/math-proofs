module

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
standalone Lean 4.35.0-rc2 package and added the proved adapters in 2026.
-/

public import ExteriorPowerSums973


@[expose] public section

/-!
# Proved adapters for Erdős problem 973

The original statement is reproduced independently of the proof interface,
with the formal-conjectures attribution retained above. The adapters use the
canonical local proof; neither preprint supplies an assumed analytic input.
This module does not import `Challenge`.
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
  change ¬ _root_.Erdos973.OriginalStatement
  exact _root_.Erdos973.not_erdos_973

/-- At every fixed exponential scale, the strict lower bound is eventually
uniform over all indexed exterior configurations, including repeated points. -/
theorem eventually_exterior_power_sum_strict_lower_bound (C : ℝ) (hC : 1 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Fin n → ℂ, (∀ i, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1), C ^ (-(n : ℝ)) < ‖∑ i : Fin n, z i ^ k‖ := by
  simpa only [_root_.Erdos973.powerSum] using
    _root_.Erdos973.eventually_exterior_power_sum_strict_lower_bound C hC

end Erdos973.Palomar
