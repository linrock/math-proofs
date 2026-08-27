import ManuscriptLocal

/-!
# Automatic robust-edge reserve membership

The canonical matching theorem previously retained a separate hypothesis that
every robust manuscript-edge label belongs to the protected prime reserve.
This file proves that hypothesis from the manuscript's actual strict
archimedean strip and one elementary fixed-parameter inequality.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- A robust prime is coprime to the support product and therefore outside it. -/
theorem robustResidue_prime_not_mem_support {S : Finset ℕ}
    {b : ℕ → ℕ} {J p : ℕ}
    (hprime : p.Prime) (hrobust : robustResidue S b J p) :
    p ∉ S := by
  intro hp
  have hdiv : p ∣ ∏ s ∈ S, s :=
    Finset.dvd_prod_of_mem (fun s : ℕ => s) hp
  exact (hprime.coprime_iff_not_dvd.mp hrobust.1) hdiv

/-- An edge label above τn ≥ 2 cannot be the exceptional prime two. -/
theorem manuscriptEdge_label_ne_two_of_cutoff {S : Finset ℕ}
    {b : ℕ → ℕ} {n : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hedge : manuscriptEdge S b n τ ell e)
    (hlarge : (2 : ℝ) ≤ τ * n) :
    e.2.2 ≠ 2 := by
  obtain ⟨_, _, _, _, _, _, hlower, _, _, _⟩ := hedge
  intro heq
  norm_num [heq] at hlower
  linarith

/-- The fixed parameter inequality (J + 1)τ ≥ 1 bounds every old multiple. -/
theorem manuscriptEdge_label_multiple_cutoff {S : Finset ℕ}
    {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hedge : manuscriptEdge S b n τ ell e)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ) :
    n < (J + 1) * e.2.2 := by
  obtain ⟨_, _, _, _, _, _, hlower, _, _, _⟩ := hedge
  have hfirst : (n : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * (τ * n) := by
    calc
      (n : ℝ) = 1 * n := by ring
      _ ≤ (((J + 1 : ℕ) : ℝ) * τ) * n :=
        mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg n)
      _ = ((J + 1 : ℕ) : ℝ) * (τ * n) := by ring
  have hpositive : (0 : ℝ) < ((J + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ J
  have hsecond := mul_lt_mul_of_pos_left hlower hpositive
  have hreal : (n : ℝ) < (((J + 1) * e.2.2 : ℕ) : ℝ) := by
    simpa using hfirst.trans_lt hsecond
  exact_mod_cast hreal

/-- Every robust manuscript-edge prime automatically belongs to the canonical reserve. -/
theorem robustManuscriptEdge_label_mem_canonicalReserve {S : Finset ℕ}
    {b : ℕ → ℕ} {n J : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hlarge : (2 : ℝ) ≤ τ * n)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (he : e ∈ robustManuscriptEdges S b n J τ ell) :
    e.2.2 ∈ canonicalReserve S b n J := by
  classical
  obtain ⟨hcoordinates, hedge, hrobust⟩ := Finset.mem_filter.mp he
  have hinterval :=
    (Finset.mem_product.mp (Finset.mem_product.mp hcoordinates).2).2
  apply Finset.mem_filter.mpr
  refine ⟨hinterval, hedge.1,
    manuscriptEdge_label_ne_two_of_cutoff hedge hlarge, ?_,
    hrobust, manuscriptEdge_label_multiple_cutoff hedge hscale⟩
  exact robustResidue_prime_not_mem_support hedge.1 hrobust

/-- The actual manuscript covering now needs only support and scalar analytic estimates. -/
theorem covering_of_manuscript_scalar_bounds {n J D k : ℕ}
    (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ s ≤ n)
    (hlarge : (2 : ℝ) ≤ τ * n)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ)
    (hdegree : 0 < D)
    (hx : ∀ x : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.2.2 = z).card ≤ D)
    (hedges : 3 * D * k ≤ (robustManuscriptEdges S b n J τ ell).card)
    (hsurplus : deficiency n (initialAssignment S b) ≤
      (canonicalReserve S b n J).card + k) :
    ∃ final : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m := by
  apply covering_of_manuscript_edges
    S b τ ell hsupport hdegree hx hy hz hedges hsurplus
  intro e he
  exact robustManuscriptEdge_label_mem_canonicalReserve hlarge hscale he

/-- For fixed positive τ, the lower edge cutoff exceeds two for all large n. -/
theorem eventually_manuscript_edge_lower_cutoff {τ : ℝ} (hpositive : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ τ * n := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 : ℝ) / τ)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hdiv : (2 : ℝ) / τ ≤ n := (le_of_lt hN).trans hcast
  have hmul := (div_le_iff₀ hpositive).mp hdiv
  nlinarith

/-- Robust-label membership is eventually automatic for every fixed valid cutoff. -/
theorem eventually_robustManuscriptEdge_labels_mem_reserve
    {S : Finset ℕ} {b : ℕ → ℕ} {J : ℕ} {τ ell : ℝ}
    (hpositive : 0 < τ)
    (hscale : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) * τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ e ∈ robustManuscriptEdges S b n J τ ell,
        e.2.2 ∈ canonicalReserve S b n J := by
  filter_upwards [eventually_manuscript_edge_lower_cutoff hpositive] with n hn
  intro e he
  exact robustManuscriptEdge_label_mem_canonicalReserve hn hscale he

end Erdos689

#print axioms Erdos689.robustResidue_prime_not_mem_support
#print axioms Erdos689.manuscriptEdge_label_ne_two_of_cutoff
#print axioms Erdos689.manuscriptEdge_label_multiple_cutoff
#print axioms Erdos689.robustManuscriptEdge_label_mem_canonicalReserve
#print axioms Erdos689.covering_of_manuscript_scalar_bounds
#print axioms Erdos689.eventually_manuscript_edge_lower_cutoff
#print axioms Erdos689.eventually_robustManuscriptEdge_labels_mem_reserve
