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

open Filter Real
open scoped BigOperators Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    (S : Set α) (A : Set α := Set.univ) (b : α) : ℝ :=
  ((S ∩ A) ∩ Set.Iio b).ncard / (A ∩ Set.Iio b).ncard

noncomputable def lowerDensity {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    (S : Set α) (A : Set α := Set.univ) : ℝ :=
  atTop.liminf fun (b : α) ↦ S.partialDensity A b

end Set

namespace Erdos968

/-- `u n` is the normalized `n`th prime `pₙ / (n+1)`. -/
noncomputable def u (n : ℕ) : ℝ :=
  (n.nth Nat.Prime : ℝ) / (n + 1)

/-- Erdős and Prachar proved `∑_{pₙ < x} |u (n+1) - u n| ≍ (log x)^2`. -/
theorem erdos_968.variants.sum_abs_diff_isTheta_log_sq :
    (fun x : ℕ =>
        ∑ n < Nat.primeCounting' x, |u (n + 1) - u n|) =Θ[atTop]
      fun x : ℕ => log x ^ 2 := by
  sorry

/-- Erdős and Prachar proved that the set `{n | u n > u (n+1)}` has positive lower density. -/
theorem erdos_968.variants.decreasing_steps_pos_lower_density :
    0 < {n : ℕ | u n > u (n + 1)}.lowerDensity := by
  sorry

end Erdos968
