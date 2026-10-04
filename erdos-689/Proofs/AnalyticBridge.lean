module

public import Mathlib
public import Structural
public import GreedyMatching
public import Cleanup

@[expose] public section


/-!
# Exact official statement and an honest conditional assembly

The prime number theorem in progressions, qualitative and uniformly aggregated
Green--Tao-type estimates, and the uniform two-form degree estimate are defined
as quantified propositions.  They are not axioms and they are not proved.  The
finite construction carries an actual post-matching assignment and reserve;
the final simultaneous cleanup is proved in `Cleanup`, rather than assumed.
-/

open Filter
open scoped Topology BigOperators

namespace Erdos689

/-- The right-hand proposition of the upstream Erdős #689 formal statement. -/
def OfficialStatement : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
    2 ≤ ((Finset.Icc 1 n).filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card

/-- The prime number theorem in every fixed reduced arithmetic progression. -/
def PrimeNumberTheoremAP : Prop :=
  ∀ (q r : ℕ), 0 < q → Nat.Coprime r q →
    Filter.Tendsto
      (fun n : ℕ =>
        (((Finset.Icc 1 n).filter fun p => p.Prime ∧ p % q = r % q).card : ℝ) /
          ((n : ℝ) / Real.log n))
      Filter.atTop (nhds (1 / (q.totient : ℝ)))

/-- The local nonvanishing condition for the actual three prime affine forms. -/
def admissibleThreeForms (a b M r s t : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ x y : ℕ,
    x ≡ r [MOD M] ∧ y ≡ s [MOD M] ∧
    b * y - a * x ≡ t [MOD M] ∧
    ¬ p ∣ x ∧ ¬ p ∣ y ∧ ¬ p ∣ (b * y - a * x)

/-- The three-prime edge candidates in the manuscript's fixed archimedean strip. -/
noncomputable def primeLinearCandidates (n a b M r s t : ℕ) (τ ell : ℝ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 n).product (Finset.Icc 1 n)).filter fun v =>
    v.1.Prime ∧ v.2.Prime ∧ (b * v.2 - a * v.1).Prime ∧
    v.1 ≡ r [MOD M] ∧ v.2 ≡ s [MOD M] ∧
    b * v.2 - a * v.1 ≡ t [MOD M] ∧
    (n : ℝ) / 10 ≤ (a * v.1 : ℕ) ∧
    (a * v.1 : ℕ) ≤ (n : ℝ) / 5 ∧
    τ * n < (b * v.2 - a * v.1 : ℕ) ∧
    (b * v.2 - a * v.1 : ℕ) ≤ (τ + ell) * n

/-- The precise qualitative ternary prime-linear lower bound still required. -/
def TernaryPrimeLinearLowerBound : Prop :=
  ∀ (a b M r s t : ℕ) (τ ell : ℝ),
    0 < a → 0 < b → 0 < M → 0 < τ → 0 < ell → τ + ell < 1 / 10 →
    admissibleThreeForms a b M r s t →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
        c * (n : ℝ) ^ 2 / (Real.log n) ^ 3 ≤
          ((primeLinearCandidates n a b M r s t τ ell).card : ℝ)

/-- The number of switched auxiliary residue classes hitting a target. -/
def switchedHits (S : Finset ℕ) (b : ℕ → ℕ) (m : ℕ) : ℕ :=
  (S.filter fun s => b s ≡ m [MOD s]).card

/-- The fixed manuscript starting assignment: odd class at two, switched support, zero elsewhere. -/
def initialAssignment (S : Finset ℕ) (b : ℕ → ℕ) (p : ℕ) : ℕ :=
  if p = 2 then 1 else if p ∈ S then b p else 0

/-- Concrete three-partite edge admissibility from the manuscript. -/
def manuscriptEdge (S : Finset ℕ) (b : ℕ → ℕ)
    (n : ℕ) (τ ell : ℝ) (e : TripleEdge) : Prop :=
  let W := ∏ s ∈ S, s
  e.2.2.Prime ∧ e.2.1 = e.1 + e.2.2 ∧
  2 * e.1 ≤ n ∧ 2 * e.2.1 ≤ n ∧
  switchedHits S b (2 * e.1) = 0 ∧ switchedHits S b (2 * e.2.1) = 0 ∧
  τ * n < (e.2.2 : ℝ) ∧ (e.2.2 : ℝ) ≤ (τ + ell) * n ∧
  (∃ d q : ℕ, d ∣ W ∧ q.Prime ∧ e.1 = d * q) ∧
  (∃ d q : ℕ, d ∣ W ∧ q.Prime ∧ e.2.1 = 2 * d * q)

/-- A unit residue is robust when every bounded multiple has two auxiliary hits. -/
def robustResidue (S : Finset ℕ) (b : ℕ → ℕ) (J r : ℕ) : Prop :=
  Nat.Coprime r (∏ s ∈ S, s) ∧
    ∀ j ∈ Finset.Icc 1 J, 2 ≤ switchedHits S b (j * r)

/-- The actual robust zero-class reserve, fixed entirely by the manuscript parameters. -/
noncomputable def canonicalReserve (S : Finset ℕ) (b : ℕ → ℕ)
    (n J : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter fun p =>
    p.Prime ∧ p ≠ 2 ∧ p ∉ S ∧ robustResidue S b J p ∧ n < (J + 1) * p

/-- The complete finite set of robust unit residues, not an asserted density. -/
noncomputable def robustResidues (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range (∏ s ∈ S, s)).filter (robustResidue S b J)

/-- The actual finite manuscript edge set after imposing robust prime labels. -/
noncomputable def robustManuscriptEdges (S : Finset ℕ) (b : ℕ → ℕ)
    (n J : ℕ) (τ ell : ℝ) : Finset TripleEdge := by
  classical
  exact ((Finset.Icc 1 n).product
    ((Finset.Icc 1 n).product (Finset.Icc 1 n))).filter fun e =>
      manuscriptEdge S b n τ ell e ∧ robustResidue S b J e.2.2

/--
The coefficient-summed edge estimate actually required by the parameter order.

The positive constant is chosen before the switched prime set.  Only the
eventual threshold, located inside the parameter quantifiers, may depend on it.
The qualitative `TernaryPrimeLinearLowerBound` alone does not imply this form.
-/
def UniformRobustManuscriptEdgeLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in Filter.atTop,
          c * (((robustResidues S b J).card : ℝ) /
            (((∏ s ∈ S, s).totient : ℕ) : ℝ)) * ell * (n : ℝ) ^ 2 /
              (Real.log n) ^ 3 ≤
            ((robustManuscriptEdges S b n J τ ell).card : ℝ)

/-- The fixed-modulus two-form sieve consequence, with one absolute constant. -/
def FixedModulusTwoFormDegreeBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in Filter.atTop, ∀ E : Finset TripleEdge,
          (∀ e ∈ E, manuscriptEdge S b n τ ell e) →
          (∀ x : ℕ, ((E.filter fun e => e.1 = x).card : ℝ) ≤
            C * n / (Real.log n) ^ 2) ∧
          (∀ y : ℕ, ((E.filter fun e => e.2.1 = y).card : ℝ) ≤
            C * n / (Real.log n) ^ 2) ∧
          (∀ z : ℕ, ((E.filter fun e => e.2.2 = z).card : ℝ) ≤
            C * n / (Real.log n) ^ 2)

/-- An explicit finite ledger together with genuine post-matching residue/reserve data. -/
structure FiniteConstruction (n : ℕ) where
  edges : Finset TripleEdge
  degree : ℕ
  demand : ℕ
  reserve : ℕ
  requiredMatching : ℕ
  remaining : Finset TripleEdge → ℕ
  assignment : Finset TripleEdge → ℕ → ℕ
  available : Finset TripleEdge → Finset ℕ
  degree_pos : 0 < degree
  degree_x : ∀ x : ℕ, (edges.filter fun e => e.1 = x).card ≤ degree
  degree_y : ∀ y : ℕ, (edges.filter fun e => e.2.1 = y).card ≤ degree
  degree_z : ∀ z : ℕ, (edges.filter fun e => e.2.2 = z).card ≤ degree
  edge_lower : 3 * degree * requiredMatching ≤ edges.card
  initial_surplus : demand ≤ reserve + requiredMatching
  matching_reserve : ∀ M : Finset TripleEdge,
    M ⊆ edges → threePartiteMatching M → M.card ≤ reserve
  matching_demand : ∀ M : Finset TripleEdge,
    M ⊆ edges → threePartiteMatching M → 2 * M.card ≤ demand
  remaining_bound : ∀ M : Finset TripleEdge,
    M ⊆ edges → threePartiteMatching M →
      remaining M ≤ demand - 2 * M.card
  reserve_protected : ∀ M : Finset TripleEdge,
    M ⊆ edges → threePartiteMatching M →
      protectedReserve n (assignment M) (available M)
  reserve_card : ∀ M : Finset TripleEdge,
    M ⊆ edges → threePartiteMatching M →
      (available M).card = reserve - M.card
  remaining_exact : ∀ M : Finset TripleEdge,
    M ⊆ edges → threePartiteMatching M →
      remaining M = deficiency n (assignment M)

/-- Every switched-support hit survives when the reserve is disjoint from that support. -/
theorem switchedHits_le_protectedPrimes {n m : ℕ}
    {S R : Finset ℕ} {b : ℕ → ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ s ≤ n)
    (hdisjoint : Disjoint S R) :
    switchedHits S b m ≤
      (protectedPrimes n (initialAssignment S b) R m).card := by
  classical
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hmem, hhit⟩ := Finset.mem_filter.mp hs
  obtain ⟨hprime, hlarge, hbound⟩ := hsupport s hmem
  have htwo : s ≠ 2 := by omega
  apply Finset.mem_filter.mpr
  constructor
  · apply mem_coveredPrimes_iff.mpr
    refine ⟨hprime.one_le, hbound, hprime, ?_⟩
    simpa [initialAssignment, htwo, hmem] using hhit
  · intro hreserve
    exact Finset.disjoint_left.mp hdisjoint hmem hreserve

/-- The canonical robust prime set already satisfies simultaneous reserve protection. -/
theorem initialAssignment_protectedReserve {n J : ℕ}
    {S : Finset ℕ} {b : ℕ → ℕ}
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ s ≤ n) :
    protectedReserve n (initialAssignment S b) (canonicalReserve S b n J) := by
  classical
  have hdisjoint : Disjoint S (canonicalReserve S b n J) := by
    apply Finset.disjoint_left.mpr
    intro s hs hreserve
    have hdata := (Finset.mem_filter.mp hreserve).2
    exact hdata.2.2.1 hs
  intro p hp
  obtain ⟨hinterval, hprime, htwo, hnotS, hrobust, hcutoff⟩ :=
    Finset.mem_filter.mp hp
  have hbound : p ≤ n := (Finset.mem_Icc.mp hinterval).2
  refine ⟨hprime, hbound, ?_, ?_⟩
  · simp [initialAssignment, htwo, hnotS]
  · intro m hm hdiv
    have hsupporthits : robustSupport n p (switchedHits S b) :=
      robust_of_multiple_hits hcutoff (by
        intro j hj hJ
        exact hrobust.2 j (Finset.mem_Icc.mpr ⟨hj, hJ⟩))
    have hmhits := hsupporthits m
      (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 hdiv
    exact hmhits.trans (switchedHits_le_protectedPrimes hsupport hdisjoint)

/-- A concrete greedy matching and exact post-switch ledger are enough for cleanup. -/
theorem covering_of_explicit_matching_ledger {n D k : ℕ}
    (a₀ : ℕ → ℕ) (R : Finset ℕ) (E : Finset TripleEdge)
    (hdegree : 0 < D)
    (hx : ∀ x : ℕ, (E.filter fun e => e.1 = x).card ≤ D)
    (hy : ∀ y : ℕ, (E.filter fun e => e.2.1 = y).card ≤ D)
    (hz : ∀ z : ℕ, (E.filter fun e => e.2.2 = z).card ≤ D)
    (hedges : 3 * D * k ≤ E.card)
    (hsurplus : deficiency n a₀ ≤ R.card + k)
    (hrealize : ∀ M : Finset TripleEdge,
      M ⊆ E → threePartiteMatching M →
        ∃ a : ℕ → ℕ, ∃ available : Finset ℕ,
          protectedReserve n a available ∧
          available.card + M.card = R.card ∧
          deficiency n a + 2 * M.card ≤ deficiency n a₀) :
    ∃ final : ℕ → ℕ,
      ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n final m := by
  obtain ⟨M, hsub, hmatching, hbound⟩ :=
    exists_greedy_matching hx hy hz
  have hmatching_size : k ≤ M.card := by
    apply Nat.le_of_mul_le_mul_left (hedges.trans hbound)
    exact Nat.mul_pos (by norm_num) hdegree
  obtain ⟨a, available, hprotected, havailable, hdrop⟩ :=
    hrealize M hsub hmatching
  apply exists_covering_of_protectedReserve hprotected
  omega

/-- Our coverage definition expands to the exact upstream prime filter. -/
theorem coverage_eq_upstream_filter (n m : ℕ) (a : ℕ → ℕ) :
    coverage n a m =
      ((Finset.Icc 1 n).filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card := by
  rfl

/-- The official target is exactly eventual closed-interval double coverage. -/
theorem officialStatement_iff_eventual_coverage :
    OfficialStatement ↔
      ∀ᶠ n : ℕ in Filter.atTop, ∃ a : ℕ → ℕ,
        ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m := by
  rfl

/-- The official eventual quantifier is equivalent to one common threshold. -/
theorem officialStatement_iff_common_threshold :
    OfficialStatement ↔
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ a : ℕ → ℕ,
        ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m := by
  rw [officialStatement_iff_eventual_coverage]
  exact Filter.eventually_atTop

/-- The degree lower bound forces the greedy matching to reach its required size. -/
theorem matching_reaches_required_size {n : ℕ} (c : FiniteConstruction n)
    {M : Finset TripleEdge} (hbound : c.edges.card ≤ 3 * c.degree * M.card) :
    c.requiredMatching ≤ M.card := by
  have hcombined : 3 * c.degree * c.requiredMatching ≤
      3 * c.degree * M.card := c.edge_lower.trans hbound
  have hpositive : 0 < 3 * c.degree :=
    Nat.mul_pos (by norm_num) c.degree_pos
  exact Nat.le_of_mul_le_mul_left hcombined hpositive

/-- Every explicit finite construction yields the genuine official finite witness. -/
theorem finiteConstruction_yields_covering {n : ℕ} (c : FiniteConstruction n) :
    ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m := by
  obtain ⟨M, hsub, hmatching, hbound⟩ :=
    exists_greedy_matching c.degree_x c.degree_y c.degree_z
  have hrequired : c.requiredMatching ≤ M.card :=
    matching_reaches_required_size c hbound
  have hsurplus : c.demand ≤ c.reserve + M.card := by
    have hinitial := c.initial_surplus
    omega
  have hremaining : c.remaining M ≤ c.reserve - M.card :=
    cleanup_ledger
      (c.matching_reserve M hsub hmatching)
      (c.matching_demand M hsub hmatching)
      (c.remaining_bound M hsub hmatching)
      hsurplus
  have hbudget : deficiency n (c.assignment M) ≤ (c.available M).card := by
    rw [← c.remaining_exact M hsub hmatching, c.reserve_card M hsub hmatching]
    exact hremaining
  exact exists_covering_of_protectedReserve
    (c.reserve_protected M hsub hmatching) hbudget

/--
The remaining construction-existence hypothesis still has full covering strength.

A covering gives degenerate empty-edge/empty-reserve data.  Thus replacing the
old `finish` field genuinely proves cleanup, but does not prove the missing
derivation of nondegenerate manuscript construction data from analytic inputs.
-/
theorem finiteConstruction_iff_covering (n : ℕ) :
    Nonempty (FiniteConstruction n) ↔
      ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n, 2 ≤ coverage n a m := by
  constructor
  · rintro ⟨c⟩
    exact finiteConstruction_yields_covering c
  · rintro ⟨a, hcover⟩
    have hdeficiency : deficiency n a = 0 := by
      unfold deficiency
      apply Finset.sum_eq_zero
      intro m hm
      exact Nat.sub_eq_zero_of_le (hcover m hm)
    refine ⟨{
      edges := ∅
      degree := 1
      demand := 0
      reserve := 0
      requiredMatching := 0
      remaining := fun _ => 0
      assignment := fun _ => a
      available := fun _ => ∅
      degree_pos := by decide
      degree_x := by intro x; simp
      degree_y := by intro y; simp
      degree_z := by intro z; simp
      edge_lower := by simp
      initial_surplus := by simp
      matching_reserve := by
        intro M hM _
        have hzero : M = ∅ := Finset.subset_empty.mp hM
        simp [hzero]
      matching_demand := by
        intro M hM _
        have hzero : M = ∅ := Finset.subset_empty.mp hM
        simp [hzero]
      remaining_bound := by
        intro M _ _
        simp
      reserve_protected := by
        intro M _ _
        simp [protectedReserve]
      reserve_card := by
        intro M hM _
        have hzero : M = ∅ := Finset.subset_empty.mp hM
        simp [hzero]
      remaining_exact := by
        intro M _ _
        simp [hdeficiency]
    }⟩

/-- Eventual construction existence is exactly as strong as the official target. -/
theorem officialStatement_iff_eventual_construction :
    OfficialStatement ↔
      ∀ᶠ n : ℕ in Filter.atTop, Nonempty (FiniteConstruction n) := by
  rw [officialStatement_iff_eventual_coverage]
  constructor
  · intro h
    filter_upwards [h] with n hn
    exact (finiteConstruction_iff_covering n).mpr hn
  · intro h
    filter_upwards [h] with n hn
    exact (finiteConstruction_iff_covering n).mp hn

/-- Eventual finite construction is sufficient for the exact official proposition. -/
theorem officialStatement_of_eventual_construction
    (h : ∀ᶠ n : ℕ in Filter.atTop, Nonempty (FiniteConstruction n)) :
    OfficialStatement := by
  apply officialStatement_iff_eventual_coverage.mpr
  filter_upwards [h] with n hn
  exact finiteConstruction_yields_covering hn.some

/--
Honest conditional assembly: the absolute coefficient-summed edge estimate is
separate from per-pattern positivity, and the missing construction-from-analysis
step remains an explicit hypothesis.  Simultaneous cleanup is already proved.
-/
theorem officialStatement_of_analytic_inputs
    (hpnt : PrimeNumberTheoremAP)
    (hternary : TernaryPrimeLinearLowerBound)
    (huniform : UniformRobustManuscriptEdgeLowerBound)
    (hsieve : FixedModulusTwoFormDegreeBound)
    (hconstruction : PrimeNumberTheoremAP →
      TernaryPrimeLinearLowerBound → UniformRobustManuscriptEdgeLowerBound →
      FixedModulusTwoFormDegreeBound →
        ∀ᶠ n : ℕ in Filter.atTop, Nonempty (FiniteConstruction n)) :
    OfficialStatement := by
  exact officialStatement_of_eventual_construction
    (hconstruction hpnt hternary huniform hsieve)

/-- The conditional result covers the endpoint as well as every smaller target. -/
theorem endpoint_of_finiteConstruction {n : ℕ}
    (hn : 1 ≤ n) (c : FiniteConstruction n) :
    ∃ a : ℕ → ℕ, 2 ≤ coverage n a n := by
  obtain ⟨a, ha⟩ := finiteConstruction_yields_covering c
  exact ⟨a, coverage_includes_right_endpoint hn ha⟩

end Erdos689

#print axioms Erdos689.coverage_eq_upstream_filter
#print axioms Erdos689.switchedHits_le_protectedPrimes
#print axioms Erdos689.initialAssignment_protectedReserve
#print axioms Erdos689.covering_of_explicit_matching_ledger
#print axioms Erdos689.officialStatement_iff_eventual_coverage
#print axioms Erdos689.officialStatement_iff_common_threshold
#print axioms Erdos689.matching_reaches_required_size
#print axioms Erdos689.finiteConstruction_yields_covering
#print axioms Erdos689.finiteConstruction_iff_covering
#print axioms Erdos689.officialStatement_iff_eventual_construction
#print axioms Erdos689.officialStatement_of_eventual_construction
#print axioms Erdos689.officialStatement_of_analytic_inputs
#print axioms Erdos689.endpoint_of_finiteConstruction
