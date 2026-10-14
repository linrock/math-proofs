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

variable {M : Type*} [AddCommMonoid M]

def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

namespace Nat

def IsPractical (n : ℕ) : Prop :=
  ∀ m, m ≤ n → m ∈ subsetSums n.divisors

end Nat

namespace Erdos18

noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

end Erdos18

namespace Erdos18.Palomar

open Filter

def FactorialIsPracticalStatement : Prop :=
  ∀ n : ℕ, Nat.IsPractical n.factorial

def UpperBoundStatement : Prop :=
  ∀ᶠ n : ℕ in atTop, Erdos18.practicalH (Nat.factorial n) < n

end Erdos18.Palomar
