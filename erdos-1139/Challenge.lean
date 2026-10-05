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
# Erdős Problem 1139: large gaps between almost-primes and mixed square coverings

Let $1 \le u_1 < u_2 < \cdots$ be the sequence of positive integers with at most
two prime factors counted with multiplicity ($\Omega(u_k) \le 2$). Erdős Problem 1139
asks whether
$$\limsup_{k \to \infty} \frac{u_{k+1} - u_k}{\log(k + 1)} = \infty.$$

This Mathlib-only benchmark states seven unconditional structural and analytic
theorems from our formalization:
1. `uniform_maximal_gap`: there exists an explicit constant $c > 1$ such that
   below every sufficiently large height $X$, there is an interval $[N+1, N+y] \subseteq [1, X]$
   of length $y \ge c \log X$ on which every integer satisfies $\Omega(N+h) \ge 3$.
2. `limsup_strictly_gt_one`: the literal Formal Conjectures normalized almost-prime
   gap limsup strictly exceeds $1$, i.e., there exists $A > 1$ such that
   $\limsup_{k \to \infty} \frac{u_{k+1} - u_k}{\log(k + 1)} \ge A > 1$.
3. `cover_crt_interval`: any mixed prime/prime-square double cover on $[1, y]$
   produces an explicit CRT interval $[N+1, N+y]$ with $Q < N \le 2Q$ on which
   every integer satisfies $\Omega(N+h) \ge 3$.
4. `seven_square_crt`: explicit finite witness $N = 40323$,
   modulus $Q = 44100 = 2^2 \cdot 3^2 \cdot 5^2 \cdot 7^2$, for the 7-target
   nested-square double cover.
5. `primorial_log_limit`: unconditional Prime Number Theorem asymptotic
   $\lim_{y \to \infty} \frac{\log(\text{primorial } y)}{y} = 1$
   for the base primorial CRT conductor.
6. `limsup_top_of_sparse`: sublinear logarithmic CRT conductors
   ($\log Q \le \varepsilon y$ for every $\varepsilon > 0$) imply the exact
   Formal Conjectures infinite-limsup statement.
7. `core_classification`: exact four-family classification of deficient targets
   surviving the fixed-parameter squared-prime core ($z_1 = z$, $z_2 = y / z$).

In addition, `Solution.lean` exports the complete conditional proof
`erdos_1139_of_gtz` (deriving the Formal Conjectures statement
from the published Green–Tao–Ziegler von Mangoldt linear-forms asymptotic) and
its reverse implication `prime_ap_of_gtz` (showing that the same hypothesis
implies arbitrary-length prime progressions).

The seven intentional `sorry` placeholders below are matched by proved declarations
in `Solution.lean`; `Solution.lean` does not import this module.
-/

namespace Erdos1139.Palomar

open Finset Filter
open scoped ArithmeticFunction.Omega BigOperators Topology

/-- Selected exponent (2 if squared, 1 otherwise) for a prime in a mixed cover. -/
def selectedPrimeExponent (squared : Finset ℕ) (p : ℕ) : ℕ :=
  if p ∈ squared then 2 else 1

/-- Selected prime-power modulus $p^{\text{selectedPrimeExponent}}$ in the CRT conductor. -/
def selectedPrimePower (squared : Finset ℕ) (p : ℕ) : ℕ :=
  p ^ selectedPrimeExponent squared p

/-- An unrestricted mixed prime/prime-square double cover of $[1, y]$. -/
def UnrestrictedPrimeSquareDoubleCover
    (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  (∀ p ∈ P, p.Prime) ∧ squared ⊆ P ∧
    ∀ h ∈ Finset.Icc 1 y,
      2 ≤ (P.filter fun p => a p ≡ h [MOD p]).card +
        (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card

/-- Existence of mixed prime/prime-square double covers with sublinear logarithmic conductor. -/
def HasSublinearUnrestrictedConductorCovers : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ Y₀ : ℕ,
    ∃ (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ),
      Y₀ ≤ y ∧ UnrestrictedPrimeSquareDoubleCover y P squared a ∧
        Real.log
          ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ)
          ≤ ε * (y : ℝ)

/-- Targets in $[1, y]$ that receive fewer than two total prime/prime-square
residue hits from $(P, \mathrm{squared}, a)$. -/
def deficientTargets (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun h =>
    (P.filter fun p => a p ≡ h [MOD p]).card +
      (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card < 2

/-- Broad prime support of the fixed-parameter core: all primes up to $y / z$. -/
def fixedParameterCorePrimes (y z : ℕ) : Finset ℕ :=
  Nat.primesLE (y / z)

/-- Squared prime support of the fixed-parameter core: primes up to $z$ in the broad support. -/
def fixedParameterCoreSquared (y z : ℕ) : Finset ℕ :=
  Nat.primesLE z ∩ fixedParameterCorePrimes y z

/-- The four target families surviving the fixed-parameter squared-prime core:
the unit $1$, primes, semiprimes $p q$ with $p < z$ and $q > y / z$, and prime
powers $p^e$ ($e \ge 2$) with $z < p \le y / z$. -/
def FixedParameterCoreDeficientType (y z h : ℕ) : Prop :=
  h = 1 ∨ h.Prime ∨
    (∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ p < z ∧ y / z < q ∧ h = p * q) ∨
    (∃ p e : ℕ,
      p.Prime ∧ z < p ∧ p ≤ y / z ∧ 2 ≤ e ∧ h = p ^ e)

/-- Below every sufficiently large height, an interval of length at least
`c * log X`, for one fixed `c > 1`, contains only integers with at least
three prime factors counted with multiplicity. -/
theorem uniform_maximal_gap :
    ∃ c : ℝ, 1 < c ∧
      ∀ᶠ X : ℕ in atTop,
        ∃ N y : ℕ,
          0 < N ∧ N + y ≤ X ∧
          c * Real.log (X : ℝ) ≤ (y : ℝ) ∧
          ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) := by
  sorry

/-- Unconditional strict improvement over coefficient $1$ for the literal
Formal Conjectures normalized almost-prime gap limsup. -/
theorem limsup_strictly_gt_one :
    ∃ A : ℝ, 1 < A ∧
      (A : EReal) ≤
        Filter.atTop.limsup
          (fun k : ℕ =>
            (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
               (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
              Real.log ((k : ℝ) + 1) : EReal)) := by
  sorry

/-- Every unrestricted mixed prime/prime-square double cover forces an interval
$[N+1, N+y]$ with $Q < N \le 2Q$ on which every integer satisfies $\Omega(N+h) \ge 3$. -/
theorem cover_crt_interval
    {y : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : UnrestrictedPrimeSquareDoubleCover y P squared a) :
    ∃ N : ℕ,
      (∏ p ∈ P, selectedPrimePower squared p) < N ∧
      N ≤ 2 * (∏ p ∈ P, selectedPrimePower squared p) ∧
        ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) := by
  sorry

/-- Explicit CRT witness $N = 40323$ with conductor $Q = 44100$ for the 7-target
nested-square cover on $\{2, 3, 5, 7\}$. -/
theorem seven_square_crt :
    7 ^ 2 < 40323 ∧ 40323 ≤ 7 ^ 2 + 44100 ∧
      ∀ p ∈ ({2, 3, 5, 7} : Finset ℕ),
        p ^ 2 ∣ 40323 + (if p = 2 then 1 else if p = 3 then 6 else if p = 5 then 2 else 4) := by
  sorry

/-- By the Prime Number Theorem, the logarithmic primorial conductor satisfies
$\lim_{y \to \infty} \frac{\log(\text{primorial } y)}{y} = 1$. -/
theorem primorial_log_limit :
    Tendsto (fun y : ℕ => Real.log (primorial y : ℝ) / (y : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  sorry

/-- Sublinear logarithmic CRT conductors imply the exact Formal Conjectures
infinite-limsup statement for Erdős Problem 1139. -/
theorem limsup_top_of_sparse
    (hsublinear : HasSublinearUnrestrictedConductorCovers) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ := by
  sorry

/-- Exact four-family classification of deficient targets after the fixed-parameter
squared-prime core. -/
theorem core_classification
    {y z h : ℕ} (parameter_positive : 0 < z)
    (square_threshold : z ≤ y / z) :
    h ∈ deficientTargets y (fixedParameterCorePrimes y z)
      (fixedParameterCoreSquared y z) (fun _ => 0) ↔
      h ∈ Finset.Icc 1 y ∧ FixedParameterCoreDeficientType y z h := by
  sorry

end Erdos1139.Palomar
