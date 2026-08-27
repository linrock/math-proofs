import AnalyticScalarCapacity433
import DeficiencyAsymptotic433

/-!
# The two remaining genuine analytic inputs for Erdős problem #689

The complete unconditional asymptotic for the actual initial deficiency
discharges the third hypothesis in the previously audited exact
analytic-to-scalar covering construction.  The resulting theorem assumes
only the genuine lower bound for the actual robust edge set and the genuine
upper bound for all three unrestricted actual coordinate degrees, together
with explicit fixed-support, unit-residue, density, and numerical conditions.

In particular no covering, matching, scalar certificate, deficiency estimate,
uniform prime-number theorem, or extra mathematical axiom is an assumption.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The actual unconditional deficiency asymptotic supplies every positive
eventual upper slack, with exactly the original prime-counting normalization. -/
theorem initial_deficiency_eventual_one_upper
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hodd : 2 ∉ S)
    (hb : ∀ s ∈ S, Nat.Coprime (b s) s)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((deficiency n (initialAssignment S b) : ℕ) : ℝ) /
        ((n : ℝ) / Real.log n) ≤ 1 + ε := by
  have hlimit := initial_deficiency_asymptotic S b hsupport hodd hb
  have hstrict : (1 : ℝ) < 1 + ε := by linarith
  filter_upwards [(tendsto_order.mp hlimit).2 (1 + ε) hstrict] with n hn
  exact le_of_lt hn

/-- A strict exact reserve-plus-greedy margin and the two actual robust-graph
estimates imply the original covering statement; actual deficiency is already
an unconditional theorem, not an additional analytic hypothesis. -/
theorem officialStatement_of_fixed_support_edge_degree_margin
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (τ ell c C : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (hb : ∀ s ∈ S, Nat.Coprime (b s) s)
    (htau : 0 < τ) (hell : 0 < ell)
    (hcutoff : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (hc : 0 < c) (hC : 0 < C)
    (hdensity : 0 < manuscriptRobustDensity S b J)
    (hedges : ∀ᶠ n : ℕ in atTop,
      c * manuscriptRobustDensity S b J * ell * (n : ℝ) ^ 2 /
          (Real.log n) ^ 3 ≤
        ((robustManuscriptEdges S b n J τ ell).card : ℝ))
    (hdegree : ∀ᶠ n : ℕ in atTop,
      actualManuscriptDegreeAtMost S b J n τ ell
        (C * n / (Real.log n) ^ 2))
    (hmargin : 1 < manuscriptReserveDensity S b J +
      (c * manuscriptRobustDensity S b J * ell) / (3 * C)) :
    OfficialStatement := by
  have hodd : 2 ∉ S := by
    intro htwo
    have hlarge := (hsupport 2 htwo).2
    omega
  exact officialStatement_of_fixed_support_analytic_rate_margin
    S b J τ ell c C hsupport htau hell hcutoff hc hC hdensity hedges hdegree
    (initial_deficiency_eventual_one_upper S b
      (fun s hs => (hsupport s hs).1) hodd hb)
    hmargin

/-- Full reduction of the original Erdős covering statement to precisely two
actual analytic graph estimates.  The support primes, unit residues, density,
cutoff, and explicit margin inequalities are fixed concrete data; the only
eventual analytic assumptions are the actual edge lower bound and the upper
bound on all three unrestricted actual coordinate degrees. -/
theorem officialStatement_of_dense_support_edge_and_degree
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (τ ell c C : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (hb : ∀ s ∈ S, Nat.Coprime (b s) s)
    (htau_positive : 0 < τ) (hell : 0 < ell)
    (hcutoff : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (hc : 0 < c) (hC : 0 < C)
    (htsmall : c * ell / (3 * C) < 1)
    (htau : τ < (c * ell / (3 * C)) / 10)
    (hdensity :
      1 - (c * ell / (3 * C)) / 10 < manuscriptRobustDensity S b J)
    (hedges : ∀ᶠ n : ℕ in atTop,
      c * manuscriptRobustDensity S b J * ell * (n : ℝ) ^ 2 /
          (Real.log n) ^ 3 ≤
        ((robustManuscriptEdges S b n J τ ell).card : ℝ))
    (hdegree : ∀ᶠ n : ℕ in atTop,
      actualManuscriptDegreeAtMost S b J n τ ell
        (C * n / (Real.log n) ^ 2)) :
    OfficialStatement := by
  have hodd : 2 ∉ S := by
    intro htwo
    have hlarge := (hsupport 2 htwo).2
    omega
  exact officialStatement_of_dense_support_analytic_rates
    S b J τ ell c C hsupport htau_positive hell hcutoff hc hC
    htsmall htau hdensity hedges hdegree
    (initial_deficiency_eventual_one_upper S b
      (fun s hs => (hsupport s hs).1) hodd hb)

#print axioms Erdos689.initial_deficiency_eventual_one_upper
#print axioms Erdos689.officialStatement_of_fixed_support_edge_degree_margin
#print axioms Erdos689.officialStatement_of_dense_support_edge_and_degree

end Erdos689
