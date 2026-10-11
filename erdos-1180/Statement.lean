module

/-
Copyright 2026 The Formal Conjectures Authors.
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

open Filter

namespace Erdos1180.Challenge

def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a

noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

def statement_erdos_1180 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s

def statement_glibichuk : Prop :=
  ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 2 ∧ Represents ε p a s

def statement_shparlinski : Prop :=
  ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 3 ∧ Represents ε p a s

def statement_lower_bound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → K * ε⁻¹ ≤ (C ε : ℝ)

def statement_lower_bound_large_primes : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∃ a : ZMod p,
      ∀ s : Multiset ℕ, Represents ε p a s → K * ε⁻¹ ≤ s.card

def statement_optimal_false : Prop :=
  ¬ (∀ δ : ℝ, 0 < δ → ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), (C ε : ℝ) ≤ ε⁻¹ ^ (1 + δ))

end Erdos1180.Challenge
