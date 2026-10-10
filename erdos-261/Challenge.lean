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

Adaptation notice: Linmiao Xu adapted the Erdős 261 definitions and solved theorem
statements from google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/261.lean`)
and added the $2^m$ infinite-representation theorem (`infinite_rationals_two_pow_reps`),
the Tengely–Ulas–Zygadło (2020) extremal and structural theorems (`max_n_bound`,
`exists_term_le_add_three`, `last_term_gap_dvd`, `borwein_loring_unique`,
`punctured_family_erdos261Prop`), and the arbitrary-length splicing theorem
(`arbitrary_length_rep_of_all_erdos261Prop`) for this standalone Lean 4 benchmark in 2026.
This file imports only Mathlib.
-/

public import Mathlib

@[expose] public section

/-!
# Erdős Problem 261: dyadic weighted representations $n / 2^n = \sum_{k=1}^t a_k / 2^{a_k}$

Erdős Problem 261 studies representations of rationals of the form $\sum a_k / 2^{a_k}$
for strictly increasing positive integers $a_k$, and in particular the Erdős–Graham
Diophantine equation
$$\frac{n}{2^n} = \sum_{k=1}^t \frac{a_k}{2^{a_k}} \quad (t \ge 2,\; 1 \le a_1 < \dots < a_t).$$

This benchmark states all five solved theorems in `FormalConjectures/ErdosProblems/261.lean`
together with seven additional structural and infinite-family theorems from
Tengely, Ulas, and Zygadło (2020):
1. `borwein_loring`: for every $m > 0$ and $n = 2^{m+1} - m - 2$,
   $n / 2^n = \sum_{k \in (n, n+m]} k / 2^k$.
2. `borwein_loring_property`: for every $m \ge 2$, $2^{m+1} - m - 2$ satisfies `Erdos261Prop`.
3. `erdos_261_parts_i`: `True ↔ {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite`.
4. `le_10000`: every positive integer $n \le 10000$ satisfies `Erdos261Prop n`
   (Tengely, Ulas, and Zygadło 2020, Theorem 3.5).
5. `two_representations`: `True ↔ ∃ x : ℚ, 2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}`.
6. `infinite_rationals_two_pow_reps`: for every $m \in \mathbb{N}$, infinitely many rationals $x \in \mathbb{Q}$
   have at least $2^m$ distinct infinite representations `Erdos261InfiniteRepresentation x a`.
7. `max_n_bound`: in any $t$-term representation ($t \ge 2$) of $n / 2^n$,
   $n \le 2^{t+1} - t - 2$ (Tengely, Ulas, and Zygadło 2020, Theorem 2.1(i)).
8. `exists_term_le_add_three`: in any $t$-term representation ($t \ge 2$) of $n / 2^n$ with $n \ge 1$,
   there exists a term $a_k$ satisfying $n + 1 \le a_k \le n + 3$
   (Tengely, Ulas, and Zygadło 2020, Theorem 2.1(ii)).
9. `last_term_gap_dvd`: in any strictly increasing $(t + 2)$-term representation of $n / 2^n$,
   $2^{a_{t+1} - a_t} \mid a_{t+1}$ (Tengely, Ulas, and Zygadło 2020, Theorem 2.1(ii)).
10. `borwein_loring_unique`: for $n = 2^{t+1} - t - 2$ ($t \ge 2$), the contiguous block
    $a_k = n + 1 + k$ is the unique strictly increasing $t$-term representation of $n / 2^n$
    (Tengely, Ulas, and Zygadło 2020, Theorem 2.1(i) equality case).
11. `punctured_family_erdos261Prop`: for every $k \ge 1$, the non-Borwein–Loring integer
    $n_k = (2^{4k + 2} + 1) / 5 - 4k$ satisfies `Erdos261Prop n_k` via the punctured interval
    $(n_k, n_k + 4k + 1] \setminus \{n_k + 4k - 1\}$ (Tengely, Ulas, and Zygadło 2020, Theorem 3.1).
12. `arbitrary_length_rep_of_all_erdos261Prop`: if every positive integer satisfies `Erdos261Prop`
    (Part (ii)), then every $n > 0$ admits representations of arbitrarily large length $t \ge L$.

The twelve intentional `sorry` placeholders below are matched by proved declarations
in `Solution.lean`; `Solution.lean` does not import this module.
-/

open scoped BigOperators Cardinal

namespace Erdos261.Palomar

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

/-- For every positive integer $m$, if $n = 2^{m+1} - m - 2$, then
$$\frac{n}{2^n} = \sum_{n < k \le n + m} \frac{k}{2^k}.$$
This construction is due to Borwein and Loring [BoLo90]. -/
theorem borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
  sorry

/-- The Borwein–Loring construction gives the required property when $m \ge 2$. -/
theorem borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  sorry

/-- Erdős #261 Part (i): infinitely many positive integers $n$ satisfy `Erdos261Prop n`. -/
theorem erdos_261_parts_i : True ↔ {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite := by
  sorry

/-- Tengely, Ulas, and Zygadło [TUZ20] verified that every positive integer $n \le 10000$
has the required property. -/
theorem le_10000 {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    Erdos261Prop n := by
  sorry

/-- There exists a rational $x$ with at least two representations
$x = \sum_{k=1}^\infty a_k / 2^{a_k}$ by strictly increasing positive integers $a_k$. -/
theorem two_representations : True ↔ ∃ x : ℚ,
    2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  sorry

/-- For every $m \in \mathbb{N}$, infinitely many rational numbers $x \in \mathbb{Q}$ have at least $2^m$
distinct infinite representations $x = \sum_{k=1}^\infty a_k / 2^{a_k}$ by strictly increasing positive integers. -/
theorem infinite_rationals_two_pow_reps (m : ℕ) :
    {x : ℚ | (2 ^ m : Cardinal) ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}}.Infinite := by
  sorry

/-- Tengely, Ulas, and Zygadło [TUZ20, Theorem 2.1(i)]: in any $t$-term representation
($t \ge 2$) of $n / 2^n$ by distinct positive integers, $n \le 2^{t+1} - t - 2$. -/
theorem max_n_bound {n t : ℕ} (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hinj : Function.Injective a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    n ≤ 2 ^ (t + 1) - t - 2 := by
  sorry

/-- Tengely, Ulas, and Zygadło [TUZ20, Theorem 2.1(ii)]: in any $t$-term representation
($t \ge 2$) of $n / 2^n$ ($n \ge 1$) by distinct positive integers, at least one term $a_k$
satisfies $n + 1 \le a_k \le n + 3$. -/
theorem exists_term_le_add_three {n t : ℕ} (hn : 1 ≤ n) (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hinj : Function.Injective a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    ∃ k : Fin t, n + 1 ≤ a k ∧ a k ≤ n + 3 := by
  sorry

/-- Tengely, Ulas, and Zygadło [TUZ20, Theorem 2.1(ii)]: in any strictly increasing $(t + 2)$-term
representation of $n / 2^n$ by positive integers, $2^{a_{t+1} - a_t} \mid a_{t+1}$. -/
theorem last_term_gap_dvd {n t : ℕ} (a : Fin (t + 2) → ℕ)
    (hmono : StrictMono a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    2 ^ (a (Fin.last (t + 1)) - a (Fin.castSucc (Fin.last t))) ∣ a (Fin.last (t + 1)) := by
  sorry

/-- Tengely, Ulas, and Zygadło [TUZ20, Theorem 2.1(i)]: for $n = 2^{t+1} - t - 2$ ($t \ge 2$),
the Borwein–Loring block $a_k = n + 1 + k$ is the unique strictly increasing $t$-term
representation of $n / 2^n$. -/
theorem borwein_loring_unique {t : ℕ} (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hmono : StrictMono a) (ha_pos : 1 ≤ a)
    (hsum : (2 ^ (t + 1) - t - 2 : ℕ) / (2 ^ (2 ^ (t + 1) - t - 2) : ℚ) =
      ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    ∀ k : Fin t, a k = (2 ^ (t + 1) - t - 2) + 1 + k.val := by
  sorry

/-- Tengely, Ulas, and Zygadło [TUZ20, Theorem 3.1]: for every $k \ge 1$, the non-Borwein–Loring
integer $n_k = (2^{4k + 2} + 1) / 5 - 4k$ satisfies `Erdos261Prop n_k`. -/
theorem punctured_family_erdos261Prop (k : ℕ) (hk : 1 ≤ k) :
    Erdos261Prop ((2 ^ (4 * k + 2) + 1) / 5 - 4 * k) := by
  sorry

/-- Splicing theorem: if every positive integer satisfies `Erdos261Prop`, then every $n > 0$
admits representations of arbitrarily large length $t \ge L$. -/
theorem arbitrary_length_rep_of_all_erdos261Prop
    (hall : ∀ m : ℕ, 0 < m → Erdos261Prop m) {n : ℕ} (hn : 0 < n) (L : ℕ) :
    ∃ᵉ (t ≥ max 2 L) (a : Fin t → ℕ), a.Injective ∧
      (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ) := by
  sorry

end Erdos261.Palomar
