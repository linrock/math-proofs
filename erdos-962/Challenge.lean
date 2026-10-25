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
namespace Erdos962
def Erdos962Prop (n k : ℕ) : Prop := ∃ m ≤ n, ∀ i ∈ Set.Icc 1 k, ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ p ∣ (m + i)
noncomputable def k (n : ℕ) : ℕ := open scoped Classical in Nat.findGreatest (fun k => Erdos962Prop n k) n
theorem erdos_962_variants_tao_upper_bound : ∃ ε : ℕ → ℝ, (∀ δ > 0, ∀ᶠ n in atTop, |ε n| < δ) ∧ ∀ᶠ n : ℕ in atTop, (k n : ℝ) ≤ (1 + ε n) * sqrt n := by sorry
end Erdos962
