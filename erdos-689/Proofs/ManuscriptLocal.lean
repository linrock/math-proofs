import MatchingAssembly

/-!
# Concrete local obligations for the manuscript hypergraph

The affine edge relation proves the repair congruence directly.  Its right
vertex is even, while an edge with a prime label other than two has an odd left
vertex.  Thus distinct vertex parts can never silently represent the same
target.
-/

open scoped BigOperators

namespace Erdos689

/-- A prime dividing a product of distinct support primes belongs to the support. -/
theorem prime_mem_of_dvd_support_product {S : Finset ℕ} {p : ℕ}
    (hprime : p.Prime) (hsupport : ∀ s ∈ S, s.Prime)
    (hdiv : p ∣ ∏ s ∈ S, s) :
    p ∈ S := by
  obtain ⟨s, hs, hps⟩ :=
    (hprime.prime.dvd_finsetProd_iff (fun s : ℕ => s)).mp hdiv
  have heq := (Nat.prime_dvd_prime_iff_eq hprime (hsupport s hs)).mp hps
  simpa [heq] using hs

/-- An even smooth-times-prime target missed by the support has at most one old hit. -/
theorem initialAssignment_even_smooth_prime_coverage {S : Finset ℕ}
    {b : ℕ → ℕ} {n d q : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdivisor : d ∣ ∏ s ∈ S, s)
    (hprime : q.Prime)
    (hmiss : switchedHits S b (2 * d * q) = 0) :
    coverage n (initialAssignment S b) (2 * d * q) ≤ 1 := by
  have hsubset :
      coveredPrimes n (initialAssignment S b) (2 * d * q) ⊆ {q} := by
    intro p hp
    obtain ⟨_, _, hpprime, hhit⟩ := mem_coveredPrimes_iff.mp hp
    have hpnotwo : p ≠ 2 := by
      intro htwo
      subst p
      simp [initialAssignment, Nat.ModEq, Nat.mul_mod] at hhit
    have hpnotS : p ∉ S := by
      intro hmem
      have haux : p ∈ S.filter (fun s => b s ≡ 2 * d * q [MOD s]) := by
        apply Finset.mem_filter.mpr
        refine ⟨hmem, ?_⟩
        simpa [initialAssignment, hpnotwo, hmem] using hhit
      have hpositive : 0 < switchedHits S b (2 * d * q) := by
        exact Finset.card_pos.mpr ⟨p, haux⟩
      omega
    have hzero : initialAssignment S b p = 0 := by
      simp [initialAssignment, hpnotwo, hpnotS]
    have hpdiv := (zero_class_hit_iff_dvd hzero).mp hhit
    rcases (hpprime.dvd_mul).mp hpdiv with hleft | hpq
    · rcases (hpprime.dvd_mul).mp hleft with hptwo | hpd
      · exact False.elim (hpnotwo
          ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp hptwo))
      · exact False.elim (hpnotS (prime_mem_of_dvd_support_product
          hpprime hsupport (dvd_trans hpd hdivisor)))
    · have heq := (Nat.prime_dvd_prime_iff_eq hpprime hprime).mp hpq
      simp [heq]
  change (coveredPrimes n (initialAssignment S b) (2 * d * q)).card ≤ 1
  simpa using Finset.card_le_card hsubset

/-- Doubling once more introduces no additional possible initial covering prime. -/
theorem initialAssignment_four_smooth_prime_coverage {S : Finset ℕ}
    {b : ℕ → ℕ} {n d q : ℕ}
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdivisor : d ∣ ∏ s ∈ S, s)
    (hprime : q.Prime)
    (hmiss : switchedHits S b (4 * d * q) = 0) :
    coverage n (initialAssignment S b) (4 * d * q) ≤ 1 := by
  have hsubset :
      coveredPrimes n (initialAssignment S b) (4 * d * q) ⊆ {q} := by
    intro p hp
    obtain ⟨_, _, hpprime, hhit⟩ := mem_coveredPrimes_iff.mp hp
    have hpnotwo : p ≠ 2 := by
      intro htwo
      subst p
      simp [initialAssignment, Nat.ModEq, Nat.mul_mod] at hhit
    have hpnotS : p ∉ S := by
      intro hmem
      have haux : p ∈ S.filter (fun s => b s ≡ 4 * d * q [MOD s]) := by
        apply Finset.mem_filter.mpr
        refine ⟨hmem, ?_⟩
        simpa [initialAssignment, hpnotwo, hmem] using hhit
      have hpositive : 0 < switchedHits S b (4 * d * q) := by
        exact Finset.card_pos.mpr ⟨p, haux⟩
      omega
    have hzero : initialAssignment S b p = 0 := by
      simp [initialAssignment, hpnotwo, hpnotS]
    have hpdiv := (zero_class_hit_iff_dvd hzero).mp hhit
    rcases (hpprime.dvd_mul).mp hpdiv with hleft | hpq
    · rcases (hpprime.dvd_mul).mp hleft with hpfour | hpd
      · have hpfactor : p ∣ 2 * 2 := by simpa using hpfour
        rcases (hpprime.dvd_mul).mp hpfactor with hptwo | hptwo
        · exact False.elim (hpnotwo
            ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp hptwo))
        · exact False.elim (hpnotwo
            ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp hptwo))
      · exact False.elim (hpnotS (prime_mem_of_dvd_support_product
          hpprime hsupport (dvd_trans hpd hdivisor)))
    · have heq := (Nat.prime_dvd_prime_iff_eq hpprime hprime).mp hpq
      simp [heq]
  change (coveredPrimes n (initialAssignment S b) (4 * d * q)).card ≤ 1
  simpa using Finset.card_le_card hsubset

/-- The actual left endpoint of every manuscript edge is initially deficient. -/
theorem manuscriptEdge_left_deficient {S : Finset ℕ} {b : ℕ → ℕ}
    {n : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hsupport : ∀ s ∈ S, s.Prime)
    (hedge : manuscriptEdge S b n τ ell e) :
    coverage n (initialAssignment S b) (2 * e.1) < 2 := by
  obtain ⟨_, _, _, _, hmiss, _, _, _,
    ⟨d, q, hdivisor, hprime, hrepr⟩, _⟩ := hedge
  have htarget : 2 * e.1 = 2 * d * q := by
    rw [hrepr]
    ring
  rw [htarget] at hmiss ⊢
  have hcoverage := initialAssignment_even_smooth_prime_coverage
    (n := n) hsupport hdivisor hprime hmiss
  omega

/-- The actual right endpoint of every manuscript edge is initially deficient. -/
theorem manuscriptEdge_right_deficient {S : Finset ℕ} {b : ℕ → ℕ}
    {n : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hsupport : ∀ s ∈ S, s.Prime)
    (hedge : manuscriptEdge S b n τ ell e) :
    coverage n (initialAssignment S b) (2 * e.2.1) < 2 := by
  obtain ⟨_, _, _, _, _, hmiss, _, _, _,
    ⟨d, q, hdivisor, hprime, hrepr⟩⟩ := hedge
  have htarget : 2 * e.2.1 = 4 * d * q := by
    rw [hrepr]
    ring
  rw [htarget] at hmiss ⊢
  have hcoverage := initialAssignment_four_smooth_prime_coverage
    (n := n) hsupport hdivisor hprime hmiss
  omega

/-- The manuscript affine equation directly gives the exact paired congruence. -/
theorem manuscriptEdge_paired_targets {S : Finset ℕ} {b : ℕ → ℕ}
    {n : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hedge : manuscriptEdge S b n τ ell e) :
    2 * e.1 ≡ 2 * e.2.1 [MOD e.2.2] := by
  exact paired_targets_same_residue hedge.2.1

/-- Every manuscript right vertex has an even coefficient by definition. -/
theorem manuscriptEdge_right_even {S : Finset ℕ} {b : ℕ → ℕ}
    {n : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hedge : manuscriptEdge S b n τ ell e) :
    e.2.1 % 2 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨d, q, _, _, hrepr⟩⟩ := hedge
  rw [hrepr, Nat.mul_assoc]
  simp

/-- Every manuscript left vertex is odd when its prime label is not two. -/
theorem manuscriptEdge_left_odd {S : Finset ℕ} {b : ℕ → ℕ}
    {n : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hedge : manuscriptEdge S b n τ ell e)
    (hlabel : e.2.2 ≠ 2) :
    e.1 % 2 = 1 := by
  have hright := manuscriptEdge_right_even hedge
  have hprime := hedge.1
  have hodd := hprime.eq_two_or_odd.resolve_left hlabel
  have hrelation := hedge.2.1
  omega

/-- Odd manuscript left vertices and even right vertices are globally disjoint. -/
theorem manuscriptEdges_cross_disjoint {S : Finset ℕ} {b : ℕ → ℕ}
    {n : ℕ} {τ ell : ℝ} {e f : TripleEdge}
    (he : manuscriptEdge S b n τ ell e)
    (hf : manuscriptEdge S b n τ ell f)
    (hlabel : e.2.2 ≠ 2) :
    e.1 ≠ f.2.1 := by
  have hleft := manuscriptEdge_left_odd he hlabel
  have hright := manuscriptEdge_right_even hf
  intro heq
  omega

/-- A positive manuscript left vertex gives a genuine closed-interval target. -/
theorem manuscriptEdge_left_target_mem {S : Finset ℕ} {b : ℕ → ℕ}
    {n : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hedge : manuscriptEdge S b n τ ell e) (hpositive : 0 < e.1) :
    2 * e.1 ∈ Finset.Icc 1 n := by
  apply Finset.mem_Icc.mpr
  have hbound := hedge.2.2.1
  omega

/-- A positive manuscript right vertex gives a genuine closed-interval target. -/
theorem manuscriptEdge_right_target_mem {S : Finset ℕ} {b : ℕ → ℕ}
    {n : ℕ} {τ ell : ℝ} {e : TripleEdge}
    (hedge : manuscriptEdge S b n τ ell e) (hpositive : 0 < e.2.1) :
    2 * e.2.1 ∈ Finset.Icc 1 n := by
  apply Finset.mem_Icc.mpr
  have hbound := hedge.2.2.2.1
  omega

/-- The actual manuscript edge family closes from scalar estimates and reserve labels. -/
theorem covering_of_manuscript_edges {n J D k : ℕ}
    (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ s ≤ n)
    (hdegree : 0 < D)
    (hx : ∀ x : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ,
      ((robustManuscriptEdges S b n J τ ell).filter fun e => e.2.2 = z).card ≤ D)
    (hedges : 3 * D * k ≤ (robustManuscriptEdges S b n J τ ell).card)
    (hsurplus : deficiency n (initialAssignment S b) ≤
      (canonicalReserve S b n J).card + k)
    (hlabels : ∀ e ∈ robustManuscriptEdges S b n J τ ell,
      e.2.2 ∈ canonicalReserve S b n J) :
    ∃ final : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m := by
  classical
  have hprimes : ∀ s ∈ S, s.Prime := fun s hs => (hsupport s hs).1
  apply covering_of_canonical_matching S b
    (robustManuscriptEdges S b n J τ ell)
    hsupport hdegree hx hy hz hedges hsurplus hlabels
  · intro e he
    have hdata := Finset.mem_filter.mp he
    have hedge := hdata.2.1
    have hcoordinate := (Finset.mem_product.mp hdata.1).1
    have hpositive : 0 < e.1 := by
      have := (Finset.mem_Icc.mp hcoordinate).1
      omega
    exact ⟨manuscriptEdge_left_target_mem hedge hpositive,
      manuscriptEdge_left_deficient hprimes hedge⟩
  · intro e he
    have hdata := Finset.mem_filter.mp he
    have hedge := hdata.2.1
    have hcoordinate :=
      (Finset.mem_product.mp (Finset.mem_product.mp hdata.1).2).1
    have hpositive : 0 < e.2.1 := by
      have := (Finset.mem_Icc.mp hcoordinate).1
      omega
    exact ⟨manuscriptEdge_right_target_mem hedge hpositive,
      manuscriptEdge_right_deficient hprimes hedge⟩
  · intro e he
    exact manuscriptEdge_paired_targets (Finset.mem_filter.mp he).2.1
  · intro e he f hf
    have hfirst := (Finset.mem_filter.mp he).2.1
    have hsecond := (Finset.mem_filter.mp hf).2.1
    have hlabel := (Finset.mem_filter.mp (hlabels e he)).2.2.1
    exact manuscriptEdges_cross_disjoint hfirst hsecond hlabel

end Erdos689

#print axioms Erdos689.prime_mem_of_dvd_support_product
#print axioms Erdos689.initialAssignment_even_smooth_prime_coverage
#print axioms Erdos689.initialAssignment_four_smooth_prime_coverage
#print axioms Erdos689.manuscriptEdge_left_deficient
#print axioms Erdos689.manuscriptEdge_right_deficient
#print axioms Erdos689.manuscriptEdge_paired_targets
#print axioms Erdos689.manuscriptEdge_right_even
#print axioms Erdos689.manuscriptEdge_left_odd
#print axioms Erdos689.manuscriptEdges_cross_disjoint
#print axioms Erdos689.manuscriptEdge_left_target_mem
#print axioms Erdos689.manuscriptEdge_right_target_mem
#print axioms Erdos689.covering_of_manuscript_edges
