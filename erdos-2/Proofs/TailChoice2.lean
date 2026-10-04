module

public import AnalyticTail2
public import MertensUpper2
public import SmoothTail2


@[expose] public section

/-!
# Global parameter selection for the probability sieve

Combines the uniform Mertens Euler-product bound (`finitePrimeProduct_uniform_log_bound`),
the summability of the late-prime cost $C (\log p)^6 / (p - 1)^2$
(`latePrimeCost_summable`), and the uniform smooth reciprocal tail bound
(`uniform_finite_primeFactors_tail`) to choose global constants $C > 0$,
$A \ge 2$, and $M \ge 1$ such that both the $A$-smooth reciprocal sum above $M$
and the late-prime sum above $A$ are strictly less than $1/4$.
-/

open scoped BigOperators

namespace Erdos2.Analytic

noncomputable def deltaHalfFactor (q : ℕ) : ℝ :=
  1 + 2 * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2

noncomputable def latePrimeCost (C : ℝ) (p : ℕ) : ℝ :=
  C * Real.log (p : ℝ) ^ 6 / ((p : ℝ) - 1) ^ 2

theorem deltaHalfFactor_nonneg_and_le (q : ℕ) (hq : q.Prime) :
    0 ≤ deltaHalfFactor q ∧
      deltaHalfFactor q ≤ ((q : ℝ) / ((q : ℝ) - 1)) ^ 6 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  constructor
  · dsimp [deltaHalfFactor]
    have hnum : 0 ≤ 3 * (q : ℝ) - 1 := by linarith
    positivity
  · exact deltaHalfFactor_le_inverseEuler_pow_six (q : ℝ) hq2

theorem latePrimeCost_summable (C : ℝ) : Summable (latePrimeCost C) := by
  have h := (summable_log_pow_div_sub_one_square 6).mul_left C
  change Summable (fun p : ℕ => C * Real.log (p : ℝ) ^ 6 / ((p : ℝ) - 1) ^ 2)
  simpa only [mul_div_assoc] using h

/-- The same global constants control every earlier-prime product, every finite
late-index budget, and every finite initial smooth-modulus budget. -/
theorem uniform_budget_selection :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ, 2 ≤ A ∧ ∃ M : ℕ, 1 ≤ M ∧
      (∀ p : ℕ, 2 ≤ p → ∀ s : Finset ℕ,
        (∀ q ∈ s, q.Prime ∧ q < p) →
          (∏ q ∈ s, deltaHalfFactor q) ≤ C * Real.log (p : ℝ) ^ 6) ∧
      (∀ S : Finset ℕ, (∀ p ∈ S, A < p) →
        (∑ p ∈ S, latePrimeCost C p) < (1 : ℝ) / 4) ∧
      (∀ D : Finset ℕ,
        (∀ d ∈ D, ∀ q ∈ d.primeFactors, q ≤ A) →
        (∀ d ∈ D, M ≤ d) →
          (∑ d ∈ D, 1 / (d : ℝ)) < (1 : ℝ) / 4) := by
  obtain ⟨C, hC, hprod⟩ :=
    finitePrimeProduct_uniform_log_bound deltaHalfFactor deltaHalfFactor_nonneg_and_le
  have hcostNonneg : ∀ p : ℕ, 0 ≤ latePrimeCost C p := by
    intro p
    dsimp [latePrimeCost]
    positivity
  obtain ⟨A, hA, hlate⟩ := uniform_finite_tail_of_summable (latePrimeCost C)
    (latePrimeCost_summable C) hcostNonneg ((1 : ℝ) / 4) (by norm_num) 2
  obtain ⟨M, hM, hinitial⟩ :=
    Erdos2.SmoothTail.uniform_finite_primeFactors_tail A (ε := (1 : ℝ) / 4)
      (by norm_num)
  refine ⟨C, hC, A, hA, M, hM, hprod, ?_, hinitial⟩
  intro S hS
  exact hlate S (fun p hp => (hS p hp).le)

end Erdos2.Analytic
