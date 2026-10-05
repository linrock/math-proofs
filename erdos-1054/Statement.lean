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


/-!
The exact Erdős #1054 statements (Parts (i), (ii), and (iii)) from
`FormalConjectures/ErdosProblems/1054.lean` (Apache-2.0), recorded as
proposition definitions with no admitted theorem. The elaborated
`answer(False)` / `answer(True)` values are written as `False` and `True`.
-/

namespace Set

open Filter
open scoped Topology

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos1054.Challenge

open Finset Filter Asymptotics

/-- Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest
divisors of $m$ for some $k\geq 1$. -/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  if h : ∃ m : ℕ, ∃ k : ℕ, 1 ≤ k ∧
      n = ∑ i ∈ Finset.Iio k, Nat.nth (· ∈ m.divisors) i then
    Nat.find h
  else 0

/-- Exact statement of Erdős #1054, Part (i): is $f(n) = o(n)$? (Answer: `False`.) -/
def statement_i : Prop :=
  False ↔ (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))

/-- Exact statement of Erdős #1054, Part (ii): is $f(n) = o(n)$ for almost all $n$?
(Answer: `False`.) -/
def statement_ii : Prop :=
  False ↔ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    (fun (n : A) ↦ (f ↑n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))

/-- Exact statement of Erdős #1054, Part (iii): is $\limsup f(n)/n = \infty$?
(Answer: `True`.) -/
def statement_iii : Prop :=
  True ↔ ∃ (A : Set ℕ), A.HasDensity 1 ∧
    atTop.limsup (fun n ↦ (f n : EReal) / n) = ⊤

end Erdos1054.Challenge
