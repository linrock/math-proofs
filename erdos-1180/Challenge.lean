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

Adaptation notice: Linmiao Xu adapted `Represents`, `C`, `erdos_1180`,
`erdos_1180.variants.shparlinski`, `erdos_1180.variants.glibichuk`,
`erdos_1180.variants.lower_bound`, and `erdos_1180.variants.optimal` from
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1180.lean`)
and added the thresholded large-prime lower bound (`erdos_1180_variants_lower_bound_large_primes`),
the asymptotic large-prime threshold constant `CAsymptotic`, its sharp pigeonhole
lower bounds (`inv_le_CAsymptotic`, `natCeil_inv_le_CAsymptotic`), its discrete
$8 (\lfloor \varepsilon^{-1} \rfloor_+ + 1)^2$, asymptotic $(8 + \eta)\varepsilon^{-2}$,
uniform $32 \varepsilon^{-2}$, symmetric $8 k^2$, and asymmetric $8 k (k + 1)$
(and $8 k$ for $(2k - 1)\varepsilon > k$, giving $16$ for $\varepsilon > 2/3$) upper bounds, and the strict separation
`CAsymptotic_inv_nat_lt_C_inv_nat` for this standalone Lean 4 benchmark in 2026.
This file imports only Mathlib.
-/

public import Mathlib

@[expose] public section

/-!
# Erdős Problem 1180: representing residues as sums of modular inverses with small denominators

Erdős Problem 1180 asks whether for every $\varepsilon > 0$ there exists a constant $C(\varepsilon)$
such that for every prime $p$, every residue $a \in \mathbb{Z}/p\mathbb{Z}$ is the sum of at most
$C(\varepsilon)$ modular inverses $n^{-1} \pmod p$ with $1 \le n \le p^\varepsilon$ and $\gcd(n, p) = 1$.

The problem was answered affirmatively by Shparlinski (2002), who established an $O(\varepsilon^{-3})$
bound for all sufficiently large primes $p \ge P(\varepsilon)$, and improved to $O(\varepsilon^{-2})$
for all sufficiently large primes by Glibichuk (2006). Because primes $p$ with $p^\varepsilon < 2$
admit only the denominator $n = 1$, the unthresholded all-primes constant `C ε` satisfies
$2^{\varepsilon^{-1}} \le 4 C(\varepsilon)$ (disproving the unthresholded polynomial bound
`Erdos1180OptimalConjecture`), whereas the large-prime threshold constant `CAsymptotic ε`
satisfies the two-sided sandwich
$$\varepsilon^{-1} \le \lceil \varepsilon^{-1} \rceil_+ \le C_{\mathrm{asymp}}(\varepsilon) \le 8\bigl(\lfloor \varepsilon^{-1} \rfloor_+ + 1\bigr)^2 = (8 + o(1))\varepsilon^{-2}.$$

This benchmark states seventeen theorems covering all five declarations in
`FormalConjectures/ErdosProblems/1180.lean` (including both the `C ε` and thresholded large-prime
formulations of `variants.lower_bound`) together with explicit quantitative bounds on `C ε`
and `CAsymptotic ε`:
1. `erdos_1180`: for every $\varepsilon > 0$, there exists $C$ valid for all primes $p$ and residues $a$.
2. `erdos_1180_variants_glibichuk`: Glibichuk's $O(\varepsilon^{-2})$ large-prime bound ($K = 32$).
3. `erdos_1180_variants_shparlinski`: Shparlinski's $O(\varepsilon^{-3})$ large-prime bound.
4. `erdos_1180_variants_lower_bound`: unconditional $\Omega(\varepsilon^{-1})$ lower bound on `C ε`
   (since `sInf ∅ = 0` in $\mathbb{N}$, this also entails nonemptiness of the uniform bound set).
5. `erdos_1180_variants_lower_bound_large_primes`: thresholded large-prime $\Omega(\varepsilon^{-1})$
   pigeonhole lower bound ($K = 1/2$, matching `FormalConjectures` PR #6951).
6. `not_erdos_1180_variants_optimal`: disproof of the unthresholded all-primes optimality statement
   `Erdos1180OptimalConjecture`.
7. `two_rpow_inv_le_four_mul_C`: small-prime exponential lower bound $2^{\varepsilon^{-1}} \le 4 C(\varepsilon)$.
8. `inv_le_CAsymptotic`: sharp large-prime pigeonhole lower bound $\varepsilon^{-1} \le C_{\mathrm{asymp}}(\varepsilon)$.
9. `natCeil_inv_le_CAsymptotic`: discrete ceiling lower bound $\lceil \varepsilon^{-1} \rceil_+ \le C_{\mathrm{asymp}}(\varepsilon)$.
10. `CAsymptotic_le_thirty_two_mul_inv_sq`: explicit Glibichuk bound $C_{\mathrm{asymp}}(\varepsilon) \le 32 \varepsilon^{-2}$ on $(0, 1]$.
11. `CAsymptotic_le_eight_mul_sq_of_one_lt_mul`: parameterized integer bound $C_{\mathrm{asymp}}(\varepsilon) \le 8 k^2$ for $k \varepsilon > 1$.
12. `CAsymptotic_le_eight_mul_succ_of_two_lt_mul`: asymmetric $(k, k + 1)$ prime-block staircase bound
    $C_{\mathrm{asymp}}(\varepsilon) \le 8 k (k + 1)$ whenever $(2k + 1)\varepsilon > 2$.
13. `CAsymptotic_le_eight_mul_of_lt_mul`: asymmetric $(1, k)$ linear staircase bound
    $C_{\mathrm{asymp}}(\varepsilon) \le 8 k$ whenever $(2k - 1)\varepsilon > k$.
14. `CAsymptotic_le_sixteen_of_two_thirds_lt`: sub-32 bound $C_{\mathrm{asymp}}(\varepsilon) \le 16$ for all $\varepsilon > 2/3$.
15. `CAsymptotic_le_eight_mul_floor_inv_add_one_sq`: all-$\varepsilon$ discrete bound
    $C_{\mathrm{asymp}}(\varepsilon) \le 8(\lfloor \varepsilon^{-1} \rfloor_+ + 1)^2$.
16. `eventually_CAsymptotic_le_eight_add_mul_inv_sq`: sharp asymptotic leading-constant bound
    $C_{\mathrm{asymp}}(\varepsilon) \le (8 + \eta)\varepsilon^{-2}$ as $\varepsilon \to 0^+$ for every $\eta > 0$.
17. `CAsymptotic_inv_nat_lt_C_inv_nat`: strict separation $C_{\mathrm{asymp}}(n^{-1}) < C(n^{-1})$ for all $n \ge 15$.

The seventeen intentional `sorry` placeholders below are matched by proved declarations
in `Solution.lean`; `Solution.lean` does not import this module.
-/

open Filter

namespace Erdos1180.Palomar

/-- `Represents ε p a s` says that the multiset `s` of denominators `n` with `1 ≤ n ≤ p^ε` and
`n` coprime to `p` has `∑ n⁻¹ = a` in `ZMod p`. -/
def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a

/-- `C ε` is the least `C` such that, for all primes `p`, every residue modulo `p` is the sum of at
most `C` elements of `{n⁻¹ : 1 ≤ n ≤ p^ε}` (or `0` if no such `C` exists). -/
noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

/-- The set of large-prime summand bounds valid for all sufficiently large primes `p ≥ P`. -/
def AsymptoticBoundSet (ε : ℝ) : Set ℕ :=
  {C | ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

/-- `CAsymptotic ε` is the least summand bound valid for all sufficiently large primes `p`. -/
noncomputable def CAsymptotic (ε : ℝ) : ℕ :=
  sInf (AsymptoticBoundSet ε)

/-- The unthresholded all-primes optimality statement (`erdos_1180.variants.optimal` in `FormalConjectures/ErdosProblems/1180.lean`). -/
def Erdos1180OptimalConjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), (C ε : ℝ) ≤ ε⁻¹ ^ (1 + δ)

/-- Affirmative resolution of `erdos_1180`: for every $\varepsilon > 0$, there exists $C_\varepsilon$
such that for all primes $p$, every residue modulo $p$ is the sum of at most $C_\varepsilon$
inverses $n^{-1} \pmod p$ with $1 \le n \le p^\varepsilon$ and $\gcd(n, p) = 1$. -/
theorem erdos_1180 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s := by
  sorry

/-- Glibichuk's $O(\varepsilon^{-2})$ large-prime theorem (`FormalConjectures` `erdos_1180.variants.glibichuk`). -/
theorem erdos_1180_variants_glibichuk :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 2 ∧ Represents ε p a s := by
  sorry

/-- Shparlinski's $O(\varepsilon^{-3})$ large-prime theorem (`FormalConjectures` `erdos_1180.variants.shparlinski`). -/
theorem erdos_1180_variants_shparlinski :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
        ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 3 ∧ Represents ε p a s := by
  sorry

/-- Unconditional $\Omega(\varepsilon^{-1})$ lower bound on `C ε` (`FormalConjectures` `erdos_1180.variants.lower_bound`). -/
theorem erdos_1180_variants_lower_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → K * ε⁻¹ ≤ (C ε : ℝ) := by
  sorry

/-- Thresholded large-prime $\Omega(\varepsilon^{-1})$ pigeonhole lower bound (`FormalConjectures` PR #6951 `erdos_1180.variants.lower_bound`). -/
theorem erdos_1180_variants_lower_bound_large_primes :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∃ a : ZMod p,
        ∀ s : Multiset ℕ, Represents ε p a s → K * ε⁻¹ ≤ s.card := by
  sorry

/-- Disproof of the unthresholded all-primes optimality conjecture (`FormalConjectures` `erdos_1180.variants.optimal`). -/
theorem not_erdos_1180_variants_optimal :
    ¬ Erdos1180OptimalConjecture := by
  sorry

/-- Exponential small-prime lower bound $2^{\varepsilon^{-1}} \le 4 C(\varepsilon)$ for all $\varepsilon > 0$. -/
theorem two_rpow_inv_le_four_mul_C {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ) ^ (ε⁻¹) ≤ 4 * (C ε : ℝ) := by
  sorry

/-- Universal large-prime pigeonhole reciprocal lower bound $\varepsilon^{-1} \le C_{\mathrm{asymp}}(\varepsilon)$ for all $\varepsilon > 0$. -/
theorem inv_le_CAsymptotic {ε : ℝ} (hε : 0 < ε) :
    ε⁻¹ ≤ (CAsymptotic ε : ℝ) := by
  sorry

/-- Universal discrete ceiling lower bound $\lceil \varepsilon^{-1} \rceil_+ \le C_{\mathrm{asymp}}(\varepsilon)$ for all $\varepsilon > 0$. -/
theorem natCeil_inv_le_CAsymptotic {ε : ℝ} (hε : 0 < ε) :
    ⌈ε⁻¹⌉₊ ≤ CAsymptotic ε := by
  sorry

/-- Explicit Glibichuk bound $C_{\mathrm{asymp}}(\varepsilon) \le 32 \varepsilon^{-2}$ for all $0 < \varepsilon \le 1$. -/
theorem CAsymptotic_le_thirty_two_mul_inv_sq {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (CAsymptotic ε : ℝ) ≤ 32 * ε⁻¹ ^ 2 := by
  sorry

/-- Parameterized integer bound $C_{\mathrm{asymp}}(\varepsilon) \le 8 k^2$ whenever $k \ge 1$ and $k \varepsilon > 1$. -/
theorem CAsymptotic_le_eight_mul_sq_of_one_lt_mul {ε : ℝ} {k : ℕ}
    (hε : 0 < ε) (hk : 1 ≤ k) (hkε : 1 < (k : ℝ) * ε) :
    CAsymptotic ε ≤ 8 * k ^ 2 := by
  sorry

/-- Asymmetric $(k, k + 1)$ staircase bound $C_{\mathrm{asymp}}(\varepsilon) \le 8 k (k + 1)$ whenever $k \ge 1$ and $(2k + 1)\varepsilon > 2$. -/
theorem CAsymptotic_le_eight_mul_succ_of_two_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkε : 2 < (2 * (k : ℝ) + 1) * ε) :
    CAsymptotic ε ≤ 8 * k * (k + 1) := by
  sorry

/-- Asymmetric $(1, k)$ linear staircase bound $C_{\mathrm{asymp}}(\varepsilon) \le 8 k$ whenever $k \ge 1$ and $(2k - 1)\varepsilon > k$. -/
theorem CAsymptotic_le_eight_mul_of_lt_mul {ε : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hkε : (k : ℝ) < (2 * (k : ℝ) - 1) * ε) :
    CAsymptotic ε ≤ 8 * k := by
  sorry

/-- Sub-32 bound $C_{\mathrm{asymp}}(\varepsilon) \le 16$ for all $\varepsilon > 2 / 3$. -/
theorem CAsymptotic_le_sixteen_of_two_thirds_lt {ε : ℝ} (hε : 2 / 3 < ε) :
    CAsymptotic ε ≤ 16 := by
  sorry

/-- Discrete all-$\varepsilon$ Glibichuk bound $C_{\mathrm{asymp}}(\varepsilon) \le 8 (\lfloor \varepsilon^{-1} \rfloor_+ + 1)^2$ for all $\varepsilon > 0$. -/
theorem CAsymptotic_le_eight_mul_floor_inv_add_one_sq {ε : ℝ} (hε : 0 < ε) :
    CAsymptotic ε ≤ 8 * (⌊ε⁻¹⌋₊ + 1) ^ 2 := by
  sorry

/-- Sharp asymptotic $(8 + o(1))\varepsilon^{-2}$ Glibichuk bound: for every $\eta > 0$, eventually as $\varepsilon \to 0^+$, $C_{\mathrm{asymp}}(\varepsilon) \le (8 + \eta)\varepsilon^{-2}$. -/
theorem eventually_CAsymptotic_le_eight_add_mul_inv_sq {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (CAsymptotic ε : ℝ) ≤ (8 + η) * ε⁻¹ ^ 2 := by
  sorry

/-- Strict separation $C_{\mathrm{asymp}}(n^{-1}) < C(n^{-1})$ between the large-prime and all-prime constants for all $n \ge 15$. -/
theorem CAsymptotic_inv_nat_lt_C_inv_nat {n : ℕ} (hn : 15 ≤ n) :
    CAsymptotic ((n : ℝ)⁻¹) < C ((n : ℝ)⁻¹) := by
  sorry

end Erdos1180.Palomar
