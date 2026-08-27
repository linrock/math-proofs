import DeficiencyTwoInputBridge433
import RobustCrtBridge

/-!
# Global two-input reduction for Erdős problem #689

The earlier two-input bridge still requires a fixed support, concrete strip
parameters, an actual robust-density bound, and a strict numerical margin.
Here all of those parameters are constructed from the two genuinely missing
analytic propositions themselves.  The final theorem has precisely two
mathematical hypotheses: the coefficient-uniform actual three-prime edge
estimate and the unrestricted actual two-form degree estimate.

In particular, no support, matching, covering, prime-density assumption,
deficiency asymptotic, numerical margin, or extra mathematical axiom is
accepted as an additional hypothesis.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The original Erdős covering conjecture follows from exactly its two
remaining global analytic estimates.  All fixed parameters and the
arbitrarily dense actual robust support are constructed unconditionally. -/
theorem officialStatement_of_uniform_edge_and_two_form_degree
    (hedge : UniformRobustManuscriptEdgeLowerBound)
    (hdegree : FixedModulusTwoFormDegreeBound) :
    OfficialStatement := by
  classical
  obtain ⟨c, hc, hedge⟩ := hedge
  obtain ⟨C, hC, hdegree⟩ := hdegree
  let ell : ℝ := min (1 / 40) (3 * C / (20 * c))
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by norm_num) (by positivity)
  have hell_small : ell ≤ (1 / 40 : ℝ) := by
    dsimp [ell]
    exact min_le_left _ _
  have hell_capacity : ell ≤ 3 * C / (20 * c) := by
    dsimp [ell]
    exact min_le_right _ _
  let t : ℝ := c * ell / (3 * C)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have ht_small : t ≤ (1 / 20 : ℝ) := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * C)).2
    calc
      c * ell ≤ c * (3 * C / (20 * c)) :=
        mul_le_mul_of_nonneg_left hell_capacity hc.le
      _ = (1 / 20 : ℝ) * (3 * C) := by
        field_simp [ne_of_gt hc]
  let τ : ℝ := t / 20
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hτ_small : τ < t / 10 := by
    dsimp [τ]
    linarith
  have hstrip : τ + ell < (1 / 10 : ℝ) := by
    dsimp [τ]
    nlinarith
  obtain ⟨J, hJ⟩ := exists_nat_gt (1 / τ)
  have hJτ : (1 : ℝ) < (J : ℝ) * τ :=
    (div_lt_iff₀ hτ).mp hJ
  have hcutoff : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  obtain ⟨S, hS, hS_density⟩ :=
    exists_support_actual_robust_density_gt J (by positivity : (0 : ℝ) < t / 10)
  let b : ℕ → ℕ := fun _ => 1
  have hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s := by
    intro s hs
    exact ⟨(hS s hs).1,
      lt_of_le_of_lt (le_max_right J 3) (hS s hs).2⟩
  have hsupport_strong :
      ∀ s ∈ S, s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0 := by
    intro s hs
    have hlarge : max J 3 < s := (hS s hs).2
    have hthree : 3 < s := lt_of_le_of_lt (le_max_right J 3) hlarge
    refine ⟨(hS s hs).1, hthree,
      lt_of_le_of_lt (le_max_left J 3) hlarge, ?_⟩
    dsimp [b]
    rw [Nat.mod_eq_of_lt (by omega : 1 < s)]
    omega
  have hsupport_sieve :
      ∀ s ∈ S, s.Prime ∧ 3 < s ∧ b s % s ≠ 0 := by
    intro s hs
    exact ⟨(hsupport_strong s hs).1,
      (hsupport_strong s hs).2.1,
      (hsupport_strong s hs).2.2.2⟩
  have hb : ∀ s ∈ S, Nat.Coprime (b s) s := by
    intro s hs
    simp [b]
  have hdensity : 1 - t / 10 < manuscriptRobustDensity S b J := by
    simpa [manuscriptRobustDensity, b] using hS_density
  have hedges := hedge S b J τ ell hsupport_strong hτ hell hstrip
  have hdegrees := hdegree S b τ ell hsupport_sieve hτ hell hstrip
  have hactual_degree : ∀ᶠ n : ℕ in atTop,
      actualManuscriptDegreeAtMost S b J n τ ell
        (C * n / (Real.log n) ^ 2) := by
    filter_upwards [hdegrees] with n hn
    exact hn (robustManuscriptEdges S b n J τ ell)
      (fun e he => (Finset.mem_filter.mp he).2.1)
  apply officialStatement_of_dense_support_edge_and_degree
    S b J τ ell c C hsupport hb hτ hell hcutoff hc hC
  · change t < 1
    linarith
  · change τ < t / 10
    exact hτ_small
  · change 1 - t / 10 < manuscriptRobustDensity S b J
    exact hdensity
  · exact hedges
  · exact hactual_degree

#print axioms Erdos689.officialStatement_of_uniform_edge_and_two_form_degree

end Erdos689
