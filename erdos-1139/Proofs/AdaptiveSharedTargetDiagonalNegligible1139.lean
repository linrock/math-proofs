module

public import AdaptiveMixedPairedSingularPositive1139
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section


/-!
# Removing the genuine equal-prime-label diagonal

The published finite-complexity prime-pattern theorem naturally counts the
ENTIRE genuine shared-target integral lattice.  The actual #1139 covering
argument instead needs only pairs whose two prime labels are globally
distinct.  Local residues of those labels must still be allowed to agree.

This file identifies the unrestricted lattice, proves its exact finite
partition into globally distinct labels and equal labels, and bounds the
equal-label diagonal by the ACTUAL signed first-branch candidate box.  The
bound is `N * (2 * (base + 1) * N + 1)`, hence the diagonal is `o(1)` after
the genuine three-dimensional `log(N)^k / N^3` normalization at EVERY fixed
prime-form exponent `k`.  No Green--Tao estimate is assumed.

The resulting asymptotic equivalence removes the globally-distinct-label
restriction from the one remaining published-theorem interface.  It does
not establish the prime-pattern asymptotic itself.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- The true integer physical target of one signed fundamental-strip branch;
its type is NOT divided out in these physical coordinates. -/
def adaptiveMixedSignedSharedTargetPhysicalOffset
    (support : Finset ℕ) (base index label : ℕ) (center : ℤ) : ℤ :=
  (index : ℤ) * (label : ℤ) +
    weightedPrimePatternSignedResidue support base label center

/-- The actual published-theorem shared-target lattice, before removing the
globally equal-label diagonal.  Both signed centers, both genuine prime
patterns, true target equality, and the physical convex domain are retained. -/
noncomputable def adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    Finset ((ℕ × ℤ) × (ℕ × ℤ)) := by
  classical
  let first_centers := adaptiveMixedSignedSearchCenterWindow first.1 N
  let second_centers := adaptiveMixedSignedSearchCenterWindow second.1 N
  let first_candidates := (Finset.Ioc N (2 * N)).product first_centers
  let second_candidates := (Finset.Ioc N (2 * N)).product second_centers
  exact (first_candidates.product second_candidates).filter fun pair =>
    pair.1.2 ∈ weightedPrimePatternEdges
      support scale first first_centers pair.1.1 ∧
    pair.2.2 ∈ weightedPrimePatternEdges
      support scale second second_centers pair.2.1 ∧
    adaptiveMixedSignedSharedTargetPhysicalOffset
      support first.1 firstIndex pair.1.1 pair.1.2 =
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support second.1 secondIndex pair.2.1 pair.2.2 ∧
    (((adaptiveMixedSignedSharedTargetPhysicalOffset
      support first.1 firstIndex pair.1.1 pair.1.2 : ℤ) : ℝ) /
        (N : ℝ),
      ((pair.1.1 : ℝ) / (N : ℝ)),
      ((pair.2.1 : ℝ) / (N : ℝ))) ∈ domain

/-- EXACT source-faithful membership in the unrestricted genuine
shared-target lattice. -/
theorem mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (pair : (ℕ × ℤ) × (ℕ × ℤ)) :
    pair ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N ↔
      pair.1 ∈ (Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow first.1 N) ∧
      pair.2 ∈ (Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow second.1 N) ∧
      pair.1.2 ∈ weightedPrimePatternEdges support scale first
        (adaptiveMixedSignedSearchCenterWindow first.1 N) pair.1.1 ∧
      pair.2.2 ∈ weightedPrimePatternEdges support scale second
        (adaptiveMixedSignedSearchCenterWindow second.1 N) pair.2.1 ∧
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support first.1 firstIndex pair.1.1 pair.1.2 =
        adaptiveMixedSignedSharedTargetPhysicalOffset
          support second.1 secondIndex pair.2.1 pair.2.2 ∧
      (((adaptiveMixedSignedSharedTargetPhysicalOffset
        support first.1 firstIndex pair.1.1 pair.1.2 : ℤ) : ℝ) /
          (N : ℝ),
        ((pair.1.1 : ℝ) / (N : ℝ)),
        ((pair.2.1 : ℝ) / (N : ℝ))) ∈ domain := by
  classical
  simp only [adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations,
    Finset.mem_filter]
  constructor
  · rintro ⟨boxed, rest⟩
    obtain ⟨first_box, second_box⟩ := Finset.mem_product.mp boxed
    exact ⟨first_box, second_box, rest⟩
  · rintro ⟨first_box, second_box, rest⟩
    exact ⟨Finset.mem_product.mpr ⟨first_box, second_box⟩, rest⟩

/-- The ACTUAL globally-equal-prime-label diagonal inside the genuine
shared-target lattice; this is not a local congruence restriction. -/
noncomputable def adaptiveMixedSignedSharedTargetEqualLabelDiagonal
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    Finset ((ℕ × ℤ) × (ℕ × ℤ)) :=
  (adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
    support scale first second firstIndex secondIndex domain N).filter
      fun pair => pair.1.1 = pair.2.1

/-- The existing covering realization set is EXACTLY the unrestricted
prime-pattern lattice with the equal-INTEGER-label diagonal removed. -/
theorem adaptiveMixedSignedSharedTargetPrimeRealizations_eq_filter_ne
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    adaptiveMixedSignedSharedTargetPrimeRealizations
      support scale first second firstIndex secondIndex domain N =
      (adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
        support scale first second firstIndex secondIndex domain N).filter
        fun pair => pair.1.1 ≠ pair.2.1 := by
  classical
  ext pair
  constructor
  · intro selected
    simp only [adaptiveMixedSignedSharedTargetPrimeRealizations,
      Finset.mem_filter] at selected
    obtain ⟨boxed, first_edge, second_edge, different,
      equal_target, in_domain⟩ := selected
    obtain ⟨first_box, second_box⟩ := Finset.mem_product.mp boxed
    apply Finset.mem_filter.mpr
    refine ⟨?_, different⟩
    apply (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N pair).mpr
    exact ⟨first_box, second_box, first_edge, second_edge,
      equal_target, in_domain⟩
  · intro selected
    obtain ⟨unrestricted, different⟩ := Finset.mem_filter.mp selected
    obtain ⟨first_box, second_box, first_edge, second_edge,
      equal_target, in_domain⟩ :=
        (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N pair).mp
            unrestricted
    simp only [adaptiveMixedSignedSharedTargetPrimeRealizations,
      Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨first_box, second_box⟩,
      first_edge, second_edge, different, equal_target, in_domain⟩

/-- Exact finite partition of the actual published shared-target lattice
into genuinely distinct prime labels and the equal-label diagonal. -/
theorem adaptiveMixedSignedSharedTargetUnrestricted_card_eq_add_diagonal
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    (adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N).card =
      (adaptiveMixedSignedSharedTargetPrimeRealizations
        support scale first second firstIndex secondIndex domain N).card +
      (adaptiveMixedSignedSharedTargetEqualLabelDiagonal
        support scale first second firstIndex secondIndex domain N).card := by
  classical
  rw [adaptiveMixedSignedSharedTargetPrimeRealizations_eq_filter_ne]
  unfold adaptiveMixedSignedSharedTargetEqualLabelDiagonal
  have partition := Finset.card_filter_add_card_filter_not
    (s := adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N)
    (fun pair : (ℕ × ℤ) × (ℕ × ℤ) => pair.1.1 ≠ pair.2.1)
  simpa using partition.symm

/-- The genuine equal-label diagonal is EMPTY unless the two distinguished
physical indices are the same: their signed residues lie in the SAME
fundamental interval `[0,P)`. -/
theorem adaptiveMixedSignedSharedTargetEqualLabelDiagonal_indices_eq
    {support : Finset ℕ} {scale firstIndex secondIndex N : ℕ}
    {first second : ℕ × ℕ}
    {domain : Set (ℝ × ℝ × ℝ)}
    {pair : (ℕ × ℤ) × (ℕ × ℤ)}
    (selected : pair ∈ adaptiveMixedSignedSharedTargetEqualLabelDiagonal
      support scale first second firstIndex secondIndex domain N) :
    firstIndex = secondIndex := by
  obtain ⟨unrestricted, same_label⟩ := Finset.mem_filter.mp selected
  obtain ⟨_first_box, _second_box, first_edge, second_edge,
    target_equal, _domain⟩ :=
      (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
        support scale first second firstIndex secondIndex domain N pair).mp
          unrestricted
  have first_certificate := weightedPrimePatternEdges_prime_certificate
    support scale first (adaptiveMixedSignedSearchCenterWindow first.1 N)
      pair.1.1 pair.1.2 first_edge
  have second_certificate := weightedPrimePatternEdges_prime_certificate
    support scale second (adaptiveMixedSignedSearchCenterWindow second.1 N)
      pair.2.1 pair.2.2 second_edge
  have label_positive : (0 : ℤ) < (pair.1.1 : ℤ) := by
    exact_mod_cast first_certificate.1.pos
  have label_cast : (pair.1.1 : ℤ) = (pair.2.1 : ℤ) := by
    exact_mod_cast same_label
  have first_lower := first_certificate.2.2.1
  have first_upper := first_certificate.2.2.2.1
  have second_lower := second_certificate.2.2.1
  have second_upper := second_certificate.2.2.2.1
  unfold adaptiveMixedSignedSharedTargetPhysicalOffset at target_equal
  rw [← label_cast] at target_equal second_upper
  by_contra different
  rcases Nat.lt_or_gt_of_ne different with lower | upper
  · have index_step : (firstIndex : ℤ) + 1 ≤ (secondIndex : ℤ) := by
      exact_mod_cast lower
    have scaled := mul_le_mul_of_nonneg_right index_step label_positive.le
    nlinarith
  · have index_step : (secondIndex : ℤ) + 1 ≤ (firstIndex : ℤ) := by
      exact_mod_cast upper
    have scaled := mul_le_mul_of_nonneg_right index_step label_positive.le
    nlinarith

/-- Distinct distinguished physical indices have NO globally equal-label
shared-target configurations at any finite scale. -/
theorem adaptiveMixedSignedSharedTargetEqualLabelDiagonal_eq_empty_of_indices_ne
    {support : Finset ℕ} {scale firstIndex secondIndex N : ℕ}
    {first second : ℕ × ℕ}
    {domain : Set (ℝ × ℝ × ℝ)}
    (different : firstIndex ≠ secondIndex) :
    adaptiveMixedSignedSharedTargetEqualLabelDiagonal
      support scale first second firstIndex secondIndex domain N = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨pair, selected⟩
  exact different
    (adaptiveMixedSignedSharedTargetEqualLabelDiagonal_indices_eq selected)

/-- EXACT cardinality of the actual signed coarse search window; negative
centers and both genuine endpoints are retained. -/
theorem adaptiveMixedSignedSearchCenterWindow_card
    (base N : ℕ) :
    (adaptiveMixedSignedSearchCenterWindow base N).card =
      2 * (base + 1) * N + 1 := by
  unfold adaptiveMixedSignedSearchCenterWindow
  rw [Int.card_Icc]
  have exact_integer :
      2 * (N : ℤ) + 1 - (-(base : ℤ) * (2 * (N : ℤ))) =
        ((2 * (base + 1) * N + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [exact_integer, Int.toNat_natCast]

/-- EXACT cardinality of the genuine first-branch dyadic-label / signed-
center candidate box. -/
theorem adaptiveMixedSignedFirstBranchCandidateBox_card
    (base N : ℕ) :
    ((Finset.Ioc N (2 * N)).product
      (adaptiveMixedSignedSearchCenterWindow base N)).card =
        N * (2 * (base + 1) * N + 1) := by
  rw [Finset.product_eq_sprod, Finset.card_product,
    adaptiveMixedSignedSearchCenterWindow_card, Nat.card_Ioc]
  congr 1
  omega

/-- Every equal-label shared-target realization injects into its ACTUAL
first-branch `(P,C)` candidate: equality of physical target and label
uniquely determines the other signed center because the true squared
support modulus is nonzero. -/
theorem adaptiveMixedSignedSharedTargetEqualLabelDiagonal_card_le_box
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (adaptiveMixedSignedSharedTargetEqualLabelDiagonal
      support scale first second firstIndex secondIndex domain N).card ≤
        N * (2 * (first.1 + 1) * N + 1) := by
  classical
  rw [← adaptiveMixedSignedFirstBranchCandidateBox_card]
  apply Finset.card_le_card_of_injOn
    (fun pair : (ℕ × ℤ) × (ℕ × ℤ) => pair.1)
  · intro pair selected
    have diagonal := Finset.mem_coe.mp selected
    have unrestricted := (Finset.mem_filter.mp diagonal).1
    apply Finset.mem_coe.mpr
    exact (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N pair).mp
        unrestricted |>.1
  · intro left left_selected right right_selected same_first
    change left.1 = right.1 at same_first
    have left_data := Finset.mem_filter.mp
      (Finset.mem_coe.mp left_selected)
    have right_data := Finset.mem_filter.mp
      (Finset.mem_coe.mp right_selected)
    have left_fields :=
      (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
        support scale first second firstIndex secondIndex domain N left).mp
          left_data.1
    have right_fields :=
      (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
        support scale first second firstIndex secondIndex domain N right).mp
          right_data.1
    have same_second_label : left.2.1 = right.2.1 := by
      calc
        left.2.1 = left.1.1 := left_data.2.symm
        _ = right.1.1 := congrArg Prod.fst same_first
        _ = right.2.1 := right_data.2
    have same_second_target :
        adaptiveMixedSignedSharedTargetPhysicalOffset
          support second.1 secondIndex left.2.1 left.2.2 =
        adaptiveMixedSignedSharedTargetPhysicalOffset
          support second.1 secondIndex right.2.1 right.2.2 := by
      calc
        _ = adaptiveMixedSignedSharedTargetPhysicalOffset
              support first.1 firstIndex left.1.1 left.1.2 :=
                left_fields.2.2.2.2.1.symm
        _ = adaptiveMixedSignedSharedTargetPhysicalOffset
              support first.1 firstIndex right.1.1 right.1.2 := by
                rw [same_first]
        _ = _ := right_fields.2.2.2.2.1
    have modulus_nonzero :
        (adaptiveMixedTypeModulus support : ℤ) ≠ 0 := by
      exact_mod_cast (adaptiveMixedTypeModulus_pos support primes).ne'
    have same_second_center : left.2.2 = right.2.2 := by
      unfold adaptiveMixedSignedSharedTargetPhysicalOffset
        weightedPrimePatternSignedResidue at same_second_target
      have cast_label : (left.2.1 : ℤ) = (right.2.1 : ℤ) := by
        exact_mod_cast same_second_label
      rw [cast_label] at same_second_target
      have scaled :
          (adaptiveMixedTypeModulus support : ℤ) * left.2.2 =
            (adaptiveMixedTypeModulus support : ℤ) * right.2.2 := by
        omega
      exact mul_left_cancel₀ modulus_nonzero scaled
    exact Prod.ext same_first (Prod.ext same_second_label same_second_center)

/-- The true equal-label diagonal has a fixed explicit quadratic bound on
every positive physical scale. -/
theorem adaptiveMixedSignedSharedTargetEqualLabelDiagonal_card_le_quadratic
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) {N : ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (positive : 0 < N) :
    (adaptiveMixedSignedSharedTargetEqualLabelDiagonal
      support scale first second firstIndex secondIndex domain N).card ≤
        (2 * (first.1 + 1) + 1) * N ^ 2 := by
  calc
    _ ≤ N * (2 * (first.1 + 1) * N + 1) :=
      adaptiveMixedSignedSharedTargetEqualLabelDiagonal_card_le_box
        support scale first second firstIndex secondIndex domain N primes
    _ ≤ (2 * (first.1 + 1) + 1) * N ^ 2 := by
      nlinarith

/-- Every fixed logarithmic power is negligible relative to the actual
integer physical scale. -/
theorem adaptiveMixedSignedSharedTarget_log_power_div_scale_tendsto_zero
    (rank : ℕ) :
    Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ rank / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have real_limit := Real.tendsto_pow_log_div_mul_add_atTop
    (1 : ℝ) 0 rank one_ne_zero
  simpa [Function.comp_def] using real_limit.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The ENTIRE omitted genuine equal-label diagonal contributes `o(1)` to
the precise three-coordinate finite-complexity normalization, at EVERY
fixed number of prime forms and for arbitrary signed convex domains. -/
theorem adaptiveMixedSignedSharedTargetEqualLabelDiagonal_normalized_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (rank : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedTargetEqualLabelDiagonal
          support scale first second firstIndex secondIndex domain N).card : ℝ) *
            Real.log (N : ℝ) ^ rank / (N : ℝ) ^ 3)
      atTop (nhds (0 : ℝ)) := by
  let coefficient : ℝ := (2 * (first.1 + 1) + 1 : ℕ)
  have model : Tendsto
      (fun N : ℕ => coefficient *
        (Real.log (N : ℝ) ^ rank / (N : ℝ)))
      atTop (nhds (0 : ℝ)) := by
    convert (adaptiveMixedSignedSharedTarget_log_power_div_scale_tendsto_zero
      rank).const_mul coefficient using 1
    simp
  apply squeeze_zero' ?_ ?_ model
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positive
    have nonnegative_log : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast positive
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positive
    have N_positive : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast positive
    have nonnegative_log : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast positive
    have count_bound :
        ((adaptiveMixedSignedSharedTargetEqualLabelDiagonal
          support scale first second firstIndex secondIndex domain N).card : ℝ) ≤
            coefficient * (N : ℝ) ^ 2 := by
      dsimp [coefficient]
      exact_mod_cast
        adaptiveMixedSignedSharedTargetEqualLabelDiagonal_card_le_quadratic
          support scale first second firstIndex secondIndex domain primes
            (by omega : 0 < N)
    calc
      _ ≤ (coefficient * (N : ℝ) ^ 2) *
          Real.log (N : ℝ) ^ rank / (N : ℝ) ^ 3 := by
            gcongr
      _ = coefficient * (Real.log (N : ℝ) ^ rank / (N : ℝ)) := by
            field_simp

/-- SOURCE-FAITHFUL published-theorem bridge: at every fixed actual
prime-form rank, an asymptotic on the FULL integral shared-target lattice
is EQUIVALENT to the same asymptotic on the globally distinct-label
realizations used in the genuine #1139 covering argument. -/
theorem adaptiveMixedSignedSharedTargetUnrestricted_asymptotic_iff_distinct
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (rank : ℕ) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N).card : ℝ) *
            Real.log (N : ℝ) ^ rank / (N : ℝ) ^ 3)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedTargetPrimeRealizations
          support scale first second firstIndex secondIndex domain N).card : ℝ) *
            Real.log (N : ℝ) ^ rank / (N : ℝ) ^ 3)
      atTop (nhds limit) := by
  have diagonal :=
    adaptiveMixedSignedSharedTargetEqualLabelDiagonal_normalized_tendsto_zero
      support scale first second firstIndex secondIndex domain rank primes
  have decomposition (N : ℕ) :
      ((adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
        support scale first second firstIndex secondIndex domain N).card : ℝ) *
          Real.log (N : ℝ) ^ rank / (N : ℝ) ^ 3 =
        ((adaptiveMixedSignedSharedTargetPrimeRealizations
          support scale first second firstIndex secondIndex domain N).card : ℝ) *
            Real.log (N : ℝ) ^ rank / (N : ℝ) ^ 3 +
        ((adaptiveMixedSignedSharedTargetEqualLabelDiagonal
          support scale first second firstIndex secondIndex domain N).card : ℝ) *
            Real.log (N : ℝ) ^ rank / (N : ℝ) ^ 3 := by
    have counts :
        ((adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N).card : ℝ) =
          ((adaptiveMixedSignedSharedTargetPrimeRealizations
            support scale first second firstIndex secondIndex domain N).card : ℝ) +
          ((adaptiveMixedSignedSharedTargetEqualLabelDiagonal
            support scale first second firstIndex secondIndex domain N).card : ℝ) := by
      exact_mod_cast
        adaptiveMixedSignedSharedTargetUnrestricted_card_eq_add_diagonal
          support scale first second firstIndex secondIndex domain N
    rw [counts]
    ring
  constructor
  · intro full
    have removed := full.sub diagonal
    convert removed using 1
    · funext N
      rw [decomposition N]
      ring
    · simp
  · intro distinct
    have restored := distinct.add diagonal
    convert restored using 1
    · funext N
      exact decomposition N
    · simp

end Erdos1139

