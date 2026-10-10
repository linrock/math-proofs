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

/-!
The exact Erdős #261 definitions and solved statements from
`FormalConjectures/ErdosProblems/261.lean` (Apache-2.0), recorded as proposition
definitions with no admitted theorem. The elaborated `answer(True)` is written as `True`.
-/

open scoped BigOperators Cardinal

namespace Erdos261.Challenge

/-- A natural number $n$ is said to have property `Erdos261Prop` if there exist $t \ge 2$
pairwise distinct positive integers $a_1, \ldots, a_t$ such that
$n / 2^n = \sum_{1 \le k \le t} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- A canonical infinite representation of a rational number $x$ by positive integers. The
denominators are strictly increasing so that reorderings are not counted as different
representations. -/
def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

/-- Exact statement of Erdős Problem 261 Part (i) (`FormalConjectures/ErdosProblems/261.lean`). -/
def statement : Prop :=
  True ↔ {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite

/-- Exact statement of `erdos_261.variants.borwein_loring` (`FormalConjectures/ErdosProblems/261.lean`). -/
def statement_borwein_loring : Prop :=
  ∀ (m : ℕ), 0 < m →
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

/-- Exact statement of `erdos_261.variants.borwein_loring_property` (`FormalConjectures/ErdosProblems/261.lean`). -/
def statement_borwein_loring_property : Prop :=
  ∀ (m : ℕ), 2 ≤ m → Erdos261Prop (2 ^ (m + 1) - m - 2)

/-- Exact statement of `erdos_261.variants.le_10000` (`FormalConjectures/ErdosProblems/261.lean`). -/
def statement_le_10000 : Prop :=
  ∀ {n : ℕ}, 0 < n → n ≤ 10000 → Erdos261Prop n

/-- Exact statement of `erdos_261.variants.two_representations` (`FormalConjectures/ErdosProblems/261.lean`). -/
def statement_two_representations : Prop :=
  True ↔ ∃ x : ℚ, 2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}

end Erdos261.Challenge
