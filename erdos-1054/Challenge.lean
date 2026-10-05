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

Adaptation notice: Linmiao Xu adapted the Erdős 1054 definitions and statements
from google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1054.lean`)
and added the subtype-restricted limsup, sharp second-moment odd-density lower
bounds, Tao–Kovač small-ratio upper bounds, and two-way aliquot range
equivalence targets for this standalone Lean 4.35.0-rc2 benchmark in 2026. This
file imports only Mathlib.
-/

public import Mathlib

@[expose] public section


/-!
# Erdős Problem 1054: sums of smallest divisors

For a natural number $n$, let $f(n)$ be the minimal integer $m$ such that $n$ is
the sum of the $k$ smallest divisors of $m$ for some $k \ge 1$ (and $f(n) = 0$
when no such $m$ exists). Erdős Problem 1054 asks three questions:
1. **Part (i)**: Is $f(n) = o(n)$? (Answer: **No**.)
2. **Part (ii)**: Is $f(n) = o(n)$ for almost all $n$ (i.e. on some subset of
   natural density $1$)? (Answer: **No**.)
3. **Part (iii)**: Is $\limsup_{n \to \infty} f(n)/n = \infty$? (Answer: **Yes**.)

This Mathlib-only Challenge file reproduces the exact zero-padded `Nat.nth`/`Nat.find`
definition of $f(n)$ and partial-density formulation from
`FormalConjectures/ErdosProblems/1054.lean`, together with 21 theorem targets
organized into four sections:
- **Section 1**: The three original Erdős #1054 questions (`answer_i`, `answer_ii`,
  `answer_iii`, `official_answer_i`, `official_answer_ii`, `official_answer_iii`),
  their strengthenings to every density-one subtype (`limsup_on_every_density_one`)
  and every relative-odd-density-one subtype (`odd_subtype_limsup`), and the two
  unrepresented base cases $f(2) = 0$ and $f(5) = 0$.
- **Section 2**: Sharp quantitative lower-density bounds for odd large-ratio
  witnesses $f(n) > A n$ across all $A \ge 1$ and all sets $S$ omitting only
  density-zero many odd integers (`HasOddDensityOne S`), including the sharp
  second-moment bound $c / [A^3 (1 + \log A)^4]$, its explicit finite-count form,
  the $c_\varepsilon / A^{3+\varepsilon}$ bound for every $\varepsilon > 0$, and
  the logarithm-free bound $c / A^6$.
- **Section 3**: The divisibility-preserving Tao–Kovač small-ratio upper bound
  $\#\{n \le X : 0 < f(n) \le \delta n\} \le C \delta^3 X$ and the resulting
  Goldbach-free strong refutation that $f(n) = o(n)$ along any subset $S \subseteq \mathbb{N}$
  forces $\{n \in S : 0 < f(n)\}$ to have natural density zero.
- **Section 4**: Unconditional small-ratio witnesses ($0 < f(\sigma(n)) \le n$ and
  $\liminf_{f(n)>0} f(n)/n = 0$) and the exact two-way asymptotic density
  equivalence between the cofactor-two divisor-prefix range $\{s(2d) : d \ge 1\}$
  and the classical set of even aliquot values $\{N \text{ even} : \exists m \ge 1,\ N = s(m)\}$.

The 21 intentional `sorry` placeholders below are matched by proved declarations
in `Solution.lean`; `Solution.lean` does not import this module.
-/

open Finset Filter Asymptotics
open scoped Topology

namespace Erdos1054.Palomar

/-- The exact official zero-padded divisor-prefix minimum, including its
zero-modulus endpoint and its zero value when no modulus represents `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  if h : ∃ m : ℕ, ∃ k : ℕ, 1 ≤ k ∧
      n = ∑ i ∈ Finset.Iio k,
        Nat.nth (fun d => d ∈ m.divisors) i then
    Nat.find h
  else 0

/-- The literal natural-number partial-density expression in the official
problem, without simplifying its two intersections with `Set.univ`. -/
def HasDensityOne (S : Set ℕ) : Prop :=
  Tendsto
    (fun b : ℕ =>
      ((((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
        ((Set.univ ∩ Set.Iio b).ncard : ℝ)))
    atTop (𝓝 1)

/-- Only the odd integers missing from `S` have density zero. This exact
Mathlib-only hypothesis places no condition on the even members of `S`. -/
def HasOddDensityOne (S : Set ℕ) : Prop :=
  (fun X : ℕ =>
    (({n : ℕ | n ≤ X ∧ Odd n ∧ n ∉ S}).ncard : ℝ))
    =o[atTop] (fun X : ℕ => (X : ℝ))

/-- Lower asymptotic density, specified using only Mathlib and the actual
closed initial interval. -/
noncomputable def lowerDensity (P : ℕ → Prop) : ℝ :=
  liminf
    (fun X : ℕ =>
      ((({n : ℕ | n ≤ X ∧ P n}).ncard : ℝ) / (X : ℝ)))
    atTop

/-! ## Section 1: Original Erdős #1054 Questions, Subtype Limsup, and Base Exceptions -/

/-- Answer to original question (i): the official function is not `o(n)`. -/
theorem answer_i :
    ¬ (fun n : ℕ => (f n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

/-- Answer to original question (ii): there is no density-one set on whose
actual subtype the official function is `o(n)`. -/
theorem answer_ii :
    ¬ ∃ S : Set ℕ, HasDensityOne S ∧
      (fun n : S => (f (n : ℕ) : ℝ))
        =o[atTop] (fun n : S => ((n : ℕ) : ℝ)) := by
  sorry

/-- Answer to original question (iii): the official extended-real limsup is
infinite, including the official question's redundant density-one witness. -/
theorem answer_iii :
    ∃ S : Set ℕ, HasDensityOne S ∧
      atTop.limsup (fun n : ℕ => (f n : EReal) / n) = ⊤ := by
  sorry

/-- The literal resolved answer shape of the official first question. -/
theorem official_answer_i :
    False ↔ (fun n : ℕ => (f n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

/-- The literal resolved answer shape of the official second question. -/
theorem official_answer_ii :
    False ↔ ∃ S : Set ℕ, HasDensityOne S ∧
      (fun n : S => (f (n : ℕ) : ℝ))
        =o[atTop] (fun n : S => ((n : ℕ) : ℝ)) := by
  sorry

/-- The literal resolved answer shape of the official third question. -/
theorem official_answer_iii :
    True ↔ ∃ S : Set ℕ, HasDensityOne S ∧
      atTop.limsup (fun n : ℕ => (f n : EReal) / n) = ⊤ := by
  sorry

/-- Stronger subtype-restricted form of question (iii): the extended-real
limsup of `f(n)/n` is infinite when restricted to the actual subtype of
*every* density-one set `S`. -/
theorem limsup_on_every_density_one
    (S : Set ℕ) (hS : HasDensityOne S) :
    (atTop : Filter S).limsup
      (fun n : S => (f (n : ℕ) : EReal) / (n : ℕ)) = ⊤ := by
  sorry

/-- The exact original ratio has infinite extended-real limsup on the actual
ordered subtype of surviving odd integers inside any `HasOddDensityOne` set `S`. -/
theorem odd_subtype_limsup
    (S : Set ℕ) (hS : HasOddDensityOne S) :
    (atTop : Filter {n : ℕ // n ∈ S ∧ Odd n}).limsup
      (fun n : {n : ℕ // n ∈ S ∧ Odd n} =>
        (f (n : ℕ) : EReal) / (n : ℕ)) = ⊤ := by
  sorry

/-- The official divisor-prefix minimum is undefined at `2`, returning the
sentinel value `0`. -/
theorem f_undefined_at_2 : f 2 = 0 := by
  sorry

/-- The official divisor-prefix minimum is undefined at `5`, returning the
sentinel value `0`. -/
theorem f_undefined_at_5 : f 5 = 0 := by
  sorry

/-! ## Section 2: Sharp Quantitative Lower-Density Bounds for Large Ratios `f(n) > A n` -/

/-- Sharp second-moment logarithmic endpoint: eliminating the three singleton
variables `R, S, T` via exact tail bounds yields a uniform lower-density bound
`c / (A^3 * (1 + log A)^4)` across all `HasOddDensityOne` sets `S` and all real
thresholds `A ≥ 1`. -/
theorem quantitative_odd_sharp_second_moment_logarithmic_endpoint :
    ∃ c : ℝ, 0 < c ∧
      ∀ S : Set ℕ, HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / (A ^ 3 * (1 + Real.log A) ^ 4) ≤
            lowerDensity
              (fun n : ℕ => n ∈ S ∧ Odd n ∧
                A * (n : ℝ) < (f n : ℝ)) := by
  sorry

/-- The sharp `c / (A^3 * (1 + log A)^4)` second-moment bound with explicit
finite counts and eventual cutoffs. -/
theorem quantitative_odd_sharp_second_moment_logarithmic_endpoint_eventual_count :
    ∃ c : ℝ, 0 < c ∧
      ∀ S : Set ℕ, HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
            (c / (A ^ 3 * (1 + Real.log A) ^ 4)) * (X : ℝ) ≤
              (({n : ℕ | n ≤ X ∧ n ∈ S ∧ Odd n ∧
                A * (n : ℝ) < (f n : ℝ)}).ncard : ℝ) := by
  sorry

/-- Every real exponent strictly larger than three (`3 + ε`) is achieved
uniformly across all `HasOddDensityOne` sets `S` and all `A ≥ 1`. -/
theorem quantitative_odd_almost_full_three_plus_epsilon :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ S : Set ℕ, HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / A ^ (3 + ε : ℝ) ≤
            lowerDensity
              (fun n : ℕ => n ∈ S ∧ Odd n ∧
                A * (n : ℝ) < (f n : ℝ)) := by
  sorry

/-- Logarithm-free `c / A^6` lower-density bound from the linear sifted-density
estimate `δ_E ≥ c₁ / E` and fixed-exponent (`β = 1/2`) divisibility-preserving
second moment. -/
theorem quantitative_odd_pure_power_six :
    ∃ c : ℝ, 0 < c ∧
      ∀ S : Set ℕ, HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / A ^ 6 ≤
            lowerDensity
              (fun n : ℕ => n ∈ S ∧ Odd n ∧
                A * (n : ℝ) < (f n : ℝ)) := by
  sorry

/-! ## Section 3: Tao–Kovač Small-Ratio Upper Bounds and Strong Refutation of `f(n) = o(n)` -/

/-- Divisibility-preserving Tao–Kovač small-ratio counting bound: for every
`δ > 0` and `X`, the number of represented integers `n ≤ X` (`0 < f n`) with
`f(n) ≤ δ * n` is at most `C * δ^3 * X`. -/
theorem small_ratio_count_le_cubic :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ X : ℕ,
      (({n : ℕ | n ≤ X ∧ 0 < f n ∧
        (f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) ≤ C * δ ^ 3 * (X : ℝ) := by
  sorry

/-- Upper asymptotic density of represented integers `n` (`0 < f n`) with
`f(n) ≤ δ * n` is bounded by `C * δ^3` for all `δ > 0`. -/
theorem small_ratio_upper_density_le_cubic :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      limsup
        (fun X : ℕ =>
          (({n : ℕ | n ≤ X ∧ 0 < f n ∧
            (f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) / (X : ℝ)) atTop ≤ C * δ ^ 3 := by
  sorry

/-- Strong refutation of `f(n) = o(n)` (without Goldbach): along *any* subset
`S ⊆ ℕ` on whose subtype `f(n) = o(n)` holds, the represented members of `S`
(`0 < f n`) have natural density zero. -/
theorem littleO_on_subtype_imp_represented_density_zero
    (S : Set ℕ)
    (ho : (fun n : S => (f (n : ℕ) : ℝ))
      =o[atTop] (fun n : S => ((n : ℕ) : ℝ))) :
    Tendsto
      (fun X : ℕ =>
        (({n : ℕ | n ≤ X ∧ n ∈ S ∧ 0 < f n}).ncard : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  sorry

/-! ## Section 4: Small-Ratio Witnesses and Two-Way Aliquot Range Equivalence -/

/-- Every positive divisor sum `σ(n) = ∑ d ∈ n.divisors, d` (`n ≥ 1`) is
represented (`0 < f(σ(n))`) and satisfies `f(σ(n)) ≤ n`. -/
theorem f_sigma_le (n : ℕ) (hn : 1 ≤ n) :
    0 < f (∑ d ∈ n.divisors, d) ∧ f (∑ d ∈ n.divisors, d) ≤ n := by
  sorry

/-- Unconditional zero liminf on represented integers: for every `ε > 0` and
every threshold `B`, there is a represented integer `N ≥ B` (`0 < f N`) with
`f(N) < ε * N`. -/
theorem frequently_represented_small_ratio (ε : ℝ) (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ 0 < f N ∧ (f N : ℝ) < ε * (N : ℝ) := by
  sorry

/-- Exact two-way lower-density equivalence between the cofactor-two divisor-prefix
value range `{s(2d) : d > 0}` and the classical set of even aliquot values
`{N even : ∃ m > 0, N = s(m)}`. -/
theorem cofactor_two_lower_density_eq_even_aliquot :
    lowerDensity (fun N : ℕ => ∃ d : ℕ, 0 < d ∧ N = ∑ q ∈ (2 * d).properDivisors, q) =
      lowerDensity (fun N : ℕ => Even N ∧ ∃ m : ℕ, 0 < m ∧ N = ∑ q ∈ m.properDivisors, q) := by
  sorry

/-- Exact two-way upper-density equivalence between the cofactor-two divisor-prefix
value range `{s(2d) : d > 0}` and the classical set of even aliquot values
`{N even : ∃ m > 0, N = s(m)}`. -/
theorem cofactor_two_upper_density_eq_even_aliquot :
    limsup
        (fun X : ℕ =>
          (({N : ℕ | N ≤ X ∧ ∃ d : ℕ, 0 < d ∧
            N = ∑ q ∈ (2 * d).properDivisors, q}).ncard : ℝ) / (X : ℝ)) atTop =
      limsup
        (fun X : ℕ =>
          (({N : ℕ | N ≤ X ∧ Even N ∧ ∃ m : ℕ, 0 < m ∧
            N = ∑ q ∈ m.properDivisors, q}).ncard : ℝ) / (X : ℝ)) atTop := by
  sorry

end Erdos1054.Palomar
