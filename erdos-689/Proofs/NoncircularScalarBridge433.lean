import ReserveCutoff

/-!
# Noncircular eventual assembly for the actual Erdős #689 manuscript edges

`AnalyticBridge.officialStatement_of_analytic_inputs` assumes eventual
`FiniteConstruction` existence, which `finiteConstruction_iff_covering` proves
equivalent to the original covering statement.  This file removes that
hypothesis completely: its only missing input is explicit scalar inequalities
for the *actual* robust manuscript edge set and the *actual* initial
deficiency/canonical reserve.

The required matching is strictly positive, so an empty-edge/zero-demand
construction cannot be smuggled back into the hypothesis.  Green--Tao edge
transfer, two-form degree transfer, the deficiency upper asymptotic, and their
eventual scalar synthesis remain real, separately identified analytic gaps.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- Genuine nondegenerate scalar data for the fixed, concrete manuscript graph.
No residue assignment, covering witness, postmatching ledger, or abstract
`FiniteConstruction` is part of this hypothesis. -/
structure ActualManuscriptScalarData
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ) (n : ℕ) where
  degree : ℕ
  requiredMatching : ℕ
  degree_positive : 0 < degree
  matching_positive : 0 < requiredMatching
  degree_left : ∀ x : ℕ,
    ((robustManuscriptEdges S b n J τ ell).filter fun e => e.1 = x).card ≤ degree
  degree_right : ∀ y : ℕ,
    ((robustManuscriptEdges S b n J τ ell).filter fun e => e.2.1 = y).card ≤ degree
  degree_label : ∀ z : ℕ,
    ((robustManuscriptEdges S b n J τ ell).filter fun e => e.2.2 = z).card ≤ degree
  enough_edges :
    3 * degree * requiredMatching ≤ (robustManuscriptEdges S b n J τ ell).card
  reserve_surplus :
    deficiency n (initialAssignment S b) ≤
      (canonicalReserve S b n J).card + requiredMatching

/-- The scalar hypothesis really forces an actual manuscript edge; the empty
edge/zero matching witness used in `finiteConstruction_iff_covering` is excluded. -/
theorem actualManuscriptScalarData_edges_nonempty
    {S : Finset ℕ} {b : ℕ → ℕ} {J n : ℕ} {τ ell : ℝ}
    (data : ActualManuscriptScalarData S b J τ ell n) :
    (robustManuscriptEdges S b n J τ ell).Nonempty := by
  apply Finset.card_pos.mp
  have hpositive : 0 < 3 * data.degree * data.requiredMatching := by
    exact Nat.mul_pos (Nat.mul_pos (by decide) data.degree_positive)
      data.matching_positive
  exact hpositive.trans_le data.enough_edges

/-- Every fixed finite support is eventually available in the actual interval;
this is derived rather than hidden inside an assumed construction. -/
theorem eventually_support_primes_available
    (S : Finset ℕ)
    (hsupport : ∀ s ∈ S, s.Prime) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ s ∈ S, s ≤ n := by
  let W : ℕ := ∏ s ∈ S, s
  have hpositive : 0 < W := by
    dsimp [W]
    exact Finset.prod_pos fun s hs => (hsupport s hs).pos
  filter_upwards [Filter.eventually_ge_atTop W] with n hn s hs
  have hdiv : s ∣ W := by
    dsimp [W]
    exact Finset.dvd_prod_of_mem (fun s : ℕ => s) hs
  exact (Nat.le_of_dvd hpositive hdiv).trans hn

/-- A finite actual-edge scalar certificate yields the genuine closed-interval
covering without assuming any `FiniteConstruction` or covering witness. -/
theorem covering_of_actual_manuscript_scalar_data
    {S : Finset ℕ} {b : ℕ → ℕ} {J n : ℕ} {τ ell : ℝ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ s ≤ n)
    (hcutoff : (2 : ℝ) ≤ τ * n)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (data : ActualManuscriptScalarData S b J τ ell n) :
    ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m := by
  exact covering_of_manuscript_scalar_bounds S b τ ell
    hsupport hcutoff hscale data.degree_positive
    data.degree_left data.degree_right data.degree_label
    data.enough_edges data.reserve_surplus

/-- Exact noncircular eventual reduction of the official Erdős statement.
The only asymptotic hypothesis concerns explicit actual-edge scalar data.
The old `hconstruction` assumption, being equivalent to the conclusion,
does not occur. -/
theorem officialStatement_of_eventual_actual_manuscript_scalar_data
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (htau : 0 < τ)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (hscalar : ∀ᶠ n : ℕ in Filter.atTop,
      Nonempty (ActualManuscriptScalarData S b J τ ell n)) :
    OfficialStatement := by
  rw [officialStatement_iff_eventual_coverage]
  have havailable := eventually_support_primes_available S
    (fun s hs => (hsupport s hs).1)
  have hcutoff := eventually_manuscript_edge_lower_cutoff htau
  filter_upwards [hscalar, havailable, hcutoff] with n hdata hn hlarge
  obtain ⟨data⟩ := hdata
  exact covering_of_actual_manuscript_scalar_data
    (fun s hs => ⟨(hsupport s hs).1, (hsupport s hs).2, hn s hs⟩)
    hlarge hscale data

end Erdos689

#print axioms Erdos689.actualManuscriptScalarData_edges_nonempty
#print axioms Erdos689.eventually_support_primes_available
#print axioms Erdos689.covering_of_actual_manuscript_scalar_data
#print axioms Erdos689.officialStatement_of_eventual_actual_manuscript_scalar_data
