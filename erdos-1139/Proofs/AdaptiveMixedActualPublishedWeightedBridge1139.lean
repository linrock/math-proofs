module

public import AdaptiveMixedActualPrimePowerAsymptotics1139
public import AdaptiveMixedPairedActualLogWeightBounds1139
public import AdaptiveMixedVonMangoldtPrimeCountBridge1139

@[expose] public section


/-!
# Published unrestricted von Mangoldt sums versus literal #1139 prime counts

Finite-complexity linear-forms theorems sum genuine von Mangoldt products
over the ENTIRE physical lattice, not merely over points already known to
have all prime coordinates.  The actual #1139 covering construction instead
uses literal unweighted signed prime-realization counts.

This module identifies the primality-free physical lattices, proves their
all-prime subsets are EXACTLY the existing covering realizations, removes
proper prime powers at the true fixed cutoff `K * N`, and applies the
source-faithful logarithmic normalization.  No Green--Tao asymptotic is
assumed or proved.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- In the genuine signed fundamental strip, every positive active mixed
target quotient is strictly below `(scale + 1) * label`, WITHOUT any
primality hypothesis on the label or the target. -/
theorem adaptiveMixedSignedPhysicalStripTarget_natural_upper
    {support : Finset ℕ} {scale index label : ℕ}
    {outcome : ℕ × ℕ} {center : ℤ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (residue_upper :
      weightedPrimePatternSignedResidue
        support outcome.1 label center < (label : ℤ))
    (form_positive :
      0 < weightedPrimePatternIntegerForm
        support outcome.1 index label center) :
    (weightedPrimePatternIntegerForm
      support outcome.1 index label center).toNat <
        (scale + 1) * label := by
  let form := weightedPrimePatternIntegerForm
    support outcome.1 index label center
  let target := form.toNat
  let target_type := adaptiveMixedActualIndexType support outcome.1 index
  have target_int : (target : ℤ) = form := by
    dsimp [target]
    exact Int.toNat_of_nonneg form_positive.le
  have physical :
      (target_type : ℤ) * (target : ℤ) =
        weightedPrimePatternSignedResidue
          support outcome.1 label center +
            (index : ℤ) * (label : ℤ) := by
    rw [target_int]
    exact scaleAdaptiveSignedPhysicalTarget_eq_residue_add_index
      center primes active
  have type_positive : 0 < target_type :=
    adaptiveMixedActualIndexType_pos_of_active primes active
  have type_target_upper : target_type * target < (index + 1) * label := by
    have upper_integer :
        (target_type : ℤ) * (target : ℤ) <
          ((index + 1) * label : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast upper_integer
  have target_le_type_target : target ≤ target_type * target := by
    have bound := Nat.mul_le_mul_right target type_positive
    simpa using bound
  have index_upper :=
    (adaptiveMixedOutcomeActiveIndex_physical_bounds active).2
  exact (target_le_type_target.trans_lt type_target_upper).trans_le
    (Nat.mul_le_mul_right label (by omega : index + 1 ≤ scale + 1))

/-- The actual primality-free ORIGINAL physical lattice: genuine dyadic
label, signed fundamental residue, positivity of every true active form,
and the exact normalized physical domain. -/
noncomputable def adaptiveMixedSignedOriginalPublishedLattice
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) : Finset (ℕ × ℤ) := by
  classical
  let centers := adaptiveMixedSignedSearchCenterWindow outcome.1 N
  exact ((Finset.Ioc N (2 * N)).product centers).filter fun point =>
    0 ≤ weightedPrimePatternSignedResidue
      support outcome.1 point.1 point.2 ∧
    weightedPrimePatternSignedResidue
      support outcome.1 point.1 point.2 < (point.1 : ℤ) ∧
    (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
      0 < weightedPrimePatternIntegerForm
        support outcome.1 index point.1 point.2) ∧
    (((point.1 : ℝ) / (N : ℝ)),
      ((point.2 : ℝ) / (N : ℝ))) ∈ domain

/-- The ALL-prime subset of the primality-free original physical lattice is
EXACTLY the existing literal signed original prime-realization finset. -/
theorem adaptiveMixedSignedOriginalPublishedLattice_all_prime
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) :
    adaptiveMixedAllPrimePoints
      (adaptiveMixedSignedOriginalPublishedLattice
        support scale outcome domain N)
      (adaptiveMixedActualFormIndices support scale outcome)
      (adaptiveMixedActualSignedPrimeFormValue support outcome.1) =
        adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N := by
  classical
  ext point
  constructor
  · intro selected
    obtain ⟨in_lattice, all_prime⟩ := Finset.mem_filter.mp selected
    obtain ⟨boxed, residue_nonnegative, residue_upper,
      forms_positive, in_domain⟩ := Finset.mem_filter.mp in_lattice
    have center_window := (Finset.mem_product.mp boxed).2
    have label_prime := all_prime none
      (adaptiveMixedActualFormIndices_label_mem support scale outcome)
    have edge :
        point.2 ∈ weightedPrimePatternEdges support scale outcome
          (adaptiveMixedSignedSearchCenterWindow outcome.1 N) point.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨center_window, label_prime,
        residue_nonnegative, residue_upper, ?_⟩
      intro physical active
      refine ⟨forms_positive physical active, ?_⟩
      exact all_prime (some physical)
        ((adaptiveMixedActualFormIndices_target_mem_iff
          support scale physical outcome).mpr active)
    exact Finset.mem_filter.mpr ⟨boxed, edge, in_domain⟩
  · intro selected
    obtain ⟨boxed, edge, in_domain⟩ := Finset.mem_filter.mp selected
    obtain ⟨_center, label_prime, residue_nonnegative,
      residue_upper, forms⟩ := Finset.mem_filter.mp edge
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨boxed, residue_nonnegative, residue_upper,
        fun physical active => (forms physical active).1, in_domain⟩
    · intro index indexed
      cases index with
      | none => exact label_prime
      | some physical =>
          have active :=
            (adaptiveMixedActualFormIndices_target_mem_iff
              support scale physical outcome).mp indexed
          exact (forms physical active).2

/-- Every primality-free original-lattice point lies in the genuine signed
dyadic candidate box. -/
theorem adaptiveMixedSignedOriginalPublishedLattice_boxed
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) :
    adaptiveMixedSignedOriginalPublishedLattice
      support scale outcome domain N ⊆
        (Finset.Ioc N (2 * N)).product
          (adaptiveMixedSignedSearchCenterWindow outcome.1 N) := by
  classical
  intro point selected
  exact (Finset.mem_filter.mp selected).1

/-- Every TRUE prime-form value on the unrestricted original physical lattice
is positive and bounded by the fixed source-faithful cutoff
`2 * (scale + 1) * N`.  No coordinate is assumed prime. -/
theorem adaptiveMixedSignedOriginalPublishedLattice_form_bounded
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (point : ℕ × ℤ)
    (selected : point ∈ adaptiveMixedSignedOriginalPublishedLattice
      support scale outcome domain N)
    (index : Option ℕ)
    (indexed : index ∈ adaptiveMixedActualFormIndices
      support scale outcome) :
    adaptiveMixedActualSignedPrimeFormValue
      support outcome.1 index point ∈
        Finset.Ioc 0 (2 * (scale + 1) * N) := by
  classical
  obtain ⟨boxed, _residue_nonnegative, residue_upper,
    forms_positive, _in_domain⟩ := Finset.mem_filter.mp selected
  obtain ⟨label_lower, label_upper⟩ :=
    Finset.mem_Ioc.mp (Finset.mem_product.mp boxed).1
  apply Finset.mem_Ioc.mpr
  cases index with
  | none =>
      constructor
      · exact lt_of_le_of_lt (Nat.zero_le N) label_lower
      · calc
          point.1 ≤ 2 * N := label_upper
          _ ≤ (2 * (scale + 1)) * N := by
            apply Nat.mul_le_mul_right N
            omega
  | some physical =>
      have active :=
        (adaptiveMixedActualFormIndices_target_mem_iff
          support scale physical outcome).mp indexed
      have form_positive := forms_positive physical active
      have integer_target :
          (((weightedPrimePatternIntegerForm
            support outcome.1 physical point.1 point.2).toNat : ℕ) : ℤ) =
              weightedPrimePatternIntegerForm
                support outcome.1 physical point.1 point.2 :=
        Int.toNat_of_nonneg form_positive.le
      constructor
      · exact_mod_cast (integer_target.symm ▸ form_positive)
      · have upper := adaptiveMixedSignedPhysicalStripTarget_natural_upper
          primes active residue_upper form_positive
        calc
          (weightedPrimePatternIntegerForm
              support outcome.1 physical point.1 point.2).toNat ≤
            (scale + 1) * point.1 := upper.le
          _ ≤ (scale + 1) * (2 * N) :=
            Nat.mul_le_mul_left (scale + 1) label_upper
          _ = (2 * (scale + 1)) * N := by ring

/-- PUBLISHED-THEOREM EXACT ORIGINAL interface: the unrestricted genuine
von Mangoldt product over EVERY signed physical lattice point has a given
asymptotic IFF the EXISTING literal prime-realization count has the exact
required fixed-rank normalization.  Proper prime powers are fully removed
at the true cutoff `2 * (scale + 1) * N`. -/
theorem adaptiveMixedSignedOriginalPublishedVonMangoldt_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedOriginalPublishedLattice
          support scale outcome domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedActualFormIndices support scale outcome)
              (adaptiveMixedActualSignedPrimeFormValue
                support outcome.1) point) / (N : ℝ) ^ 2)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices
              support scale outcome).card + 1) /
            (N : ℝ) ^ 2)
      atTop (nhds limit) := by
  classical
  let points := fun N =>
    adaptiveMixedSignedOriginalPublishedLattice
      support scale outcome domain N
  let forms := adaptiveMixedActualFormIndices support scale outcome
  let value := adaptiveMixedActualSignedPrimeFormValue support outcome.1
  let bad : ℕ → ℝ := fun N =>
    (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
      (points N) forms value,
        adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 2
  have bad_vanishes : Tendsto bad atTop (nhds (0 : ℝ)) := by
    exact adaptiveMixedSignedOriginalPrimePowerExceptions_normalized_tendsto_zero
      support scale outcome (2 * (scale + 1)) (by positivity) primes points
        (adaptiveMixedSignedOriginalPublishedLattice_boxed
          support scale outcome domain)
        (fun N point selected index indexed =>
          adaptiveMixedSignedOriginalPublishedLattice_form_bounded
            support scale outcome domain N primes point selected index indexed)
  have decomposition (N : ℕ) :
      (∑ point ∈ points N,
        adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 2 =
      (∑ point ∈ adaptiveMixedSignedOriginalPrimeRealizations
        support scale outcome domain N,
          adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 2 +
        bad N := by
    have split :=
      adaptiveMixedVonMangoldtSum_eq_prime_sum_add_exceptions
        (points N) forms value
    change
      (∑ point ∈ points N,
        adaptiveMixedVonMangoldtProduct forms value point) =
      (∑ point ∈ adaptiveMixedAllPrimePoints (points N) forms value,
        adaptiveMixedVonMangoldtProduct forms value point) +
      ∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
        (points N) forms value,
          adaptiveMixedVonMangoldtProduct forms value point at split
    rw [adaptiveMixedSignedOriginalPublishedLattice_all_prime] at split
    change _ / (N : ℝ) ^ 2 = _ / (N : ℝ) ^ 2 + _ / (N : ℝ) ^ 2
    rw [split]
    ring
  have prime_weighted_iff :
      Tendsto
        (fun N : ℕ =>
          (∑ point ∈ points N,
            adaptiveMixedVonMangoldtProduct forms value point) /
              (N : ℝ) ^ 2)
        atTop (nhds limit) ↔
      Tendsto
        (fun N : ℕ =>
          (∑ point ∈ adaptiveMixedSignedOriginalPrimeRealizations
            support scale outcome domain N,
              adaptiveMixedVonMangoldtProduct forms value point) /
                (N : ℝ) ^ 2)
        atTop (nhds limit) := by
    constructor
    · intro full
      have removed := full.sub bad_vanishes
      convert removed using 1
      · funext N
        rw [decomposition N]
        ring
      · simp
    · intro prime_only
      have restored := prime_only.add bad_vanishes
      convert restored using 1
      · funext N
        exact decomposition N
      · simp
  exact prime_weighted_iff.trans
    (adaptiveMixedSignedOriginalActualVonMangoldt_asymptotic_iff
      support scale outcome domain limit primes)

/-- The actual primality-free SHARED-LABEL physical lattice: one dyadic
label, two signed original fundamental-strip branches, and the exact
three-coordinate physical domain. -/
noncomputable def adaptiveMixedSignedSharedLabelPublishedLattice
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) : Finset (ℕ × ℤ × ℤ) := by
  classical
  let firstCenters := adaptiveMixedSignedSearchCenterWindow first.1 N
  let secondCenters := adaptiveMixedSignedSearchCenterWindow second.1 N
  exact ((Finset.Ioc N (2 * N)).product
    (firstCenters.product secondCenters)).filter fun point =>
      (point.1, point.2.1) ∈ adaptiveMixedSignedOriginalPublishedLattice
        support scale first Set.univ N ∧
      (point.1, point.2.2) ∈ adaptiveMixedSignedOriginalPublishedLattice
        support scale second Set.univ N ∧
      (((point.1 : ℝ) / (N : ℝ)),
        ((point.2.1 : ℝ) / (N : ℝ)),
        ((point.2.2 : ℝ) / (N : ℝ))) ∈ domain

/-- The all-prime subset of the primality-free three-dimensional shared-label
lattice is EXACTLY the literal existing signed shared-label realization set. -/
theorem adaptiveMixedSignedSharedLabelPublishedLattice_all_prime
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    adaptiveMixedAllPrimePoints
      (adaptiveMixedSignedSharedLabelPublishedLattice
        support scale first second domain N)
      (adaptiveMixedSharedLabelFormIndices support scale first second)
      (adaptiveMixedSharedLabelSignedPrimeFormValue
        support first.1 second.1) =
          adaptiveMixedSignedSharedLabelPrimeRealizations
            support scale first second domain N := by
  classical
  ext point
  constructor
  · intro selected
    obtain ⟨in_lattice, all_prime⟩ := Finset.mem_filter.mp selected
    obtain ⟨boxed, first_lattice, second_lattice, in_domain⟩ :=
      Finset.mem_filter.mp in_lattice
    have first_all_prime :
        (point.1, point.2.1) ∈ adaptiveMixedAllPrimePoints
          (adaptiveMixedSignedOriginalPublishedLattice
            support scale first Set.univ N)
          (adaptiveMixedActualFormIndices support scale first)
          (adaptiveMixedActualSignedPrimeFormValue support first.1) := by
      apply Finset.mem_filter.mpr
      refine ⟨first_lattice, ?_⟩
      intro index indexed
      cases index with
      | none =>
          exact all_prime (Sum.inl none)
            ((adaptiveMixedSharedLabelFormIndices_inl_mem_iff
              support scale first second none).mpr indexed)
      | some physical =>
          exact all_prime (Sum.inl (some physical))
            ((adaptiveMixedSharedLabelFormIndices_inl_mem_iff
              support scale first second (some physical)).mpr indexed)
    have second_all_prime :
        (point.1, point.2.2) ∈ adaptiveMixedAllPrimePoints
          (adaptiveMixedSignedOriginalPublishedLattice
            support scale second Set.univ N)
          (adaptiveMixedActualFormIndices support scale second)
          (adaptiveMixedActualSignedPrimeFormValue support second.1) := by
      apply Finset.mem_filter.mpr
      refine ⟨second_lattice, ?_⟩
      intro index indexed
      cases index with
      | none =>
          exact all_prime (Sum.inl none)
            ((adaptiveMixedSharedLabelFormIndices_inl_mem_iff
              support scale first second none).mpr
                (adaptiveMixedActualFormIndices_label_mem
                  support scale first))
      | some physical =>
          have active :=
            (adaptiveMixedActualFormIndices_target_mem_iff
              support scale physical second).mp indexed
          exact all_prime (Sum.inr physical)
            ((adaptiveMixedSharedLabelFormIndices_inr_mem_iff
              support scale first second physical).mpr active)
    rw [adaptiveMixedSignedOriginalPublishedLattice_all_prime] at first_all_prime
    rw [adaptiveMixedSignedOriginalPublishedLattice_all_prime] at second_all_prime
    simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter, Set.mem_univ, and_true] at first_all_prime second_all_prime
    have first_edge := first_all_prime.2
    have second_edge := second_all_prime.2
    exact Finset.mem_filter.mpr
      ⟨boxed, first_edge, second_edge, in_domain⟩
  · intro selected
    obtain ⟨boxed, first_edge, second_edge, in_domain⟩ :=
      Finset.mem_filter.mp selected
    have first_real :
        (point.1, point.2.1) ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale first Set.univ N := by
      simp only [adaptiveMixedSignedOriginalPrimeRealizations,
        Finset.mem_filter, Set.mem_univ, and_true]
      exact ⟨Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp boxed).1,
          (Finset.mem_product.mp (Finset.mem_product.mp boxed).2).1⟩,
        first_edge⟩
    have second_real :
        (point.1, point.2.2) ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale second Set.univ N := by
      simp only [adaptiveMixedSignedOriginalPrimeRealizations,
        Finset.mem_filter, Set.mem_univ, and_true]
      exact ⟨Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp boxed).1,
          (Finset.mem_product.mp (Finset.mem_product.mp boxed).2).2⟩,
        second_edge⟩
    rw [← adaptiveMixedSignedOriginalPublishedLattice_all_prime] at first_real
    rw [← adaptiveMixedSignedOriginalPublishedLattice_all_prime] at second_real
    obtain ⟨first_lattice, first_prime⟩ := Finset.mem_filter.mp first_real
    obtain ⟨second_lattice, second_prime⟩ := Finset.mem_filter.mp second_real
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_filter.mpr
        ⟨boxed, first_lattice, second_lattice, in_domain⟩
    · intro index indexed
      cases index with
      | inl branch =>
          cases branch with
          | none =>
              exact first_prime none
                ((adaptiveMixedSharedLabelFormIndices_inl_mem_iff
                  support scale first second none).mp indexed)
          | some physical =>
              exact first_prime (some physical)
                ((adaptiveMixedSharedLabelFormIndices_inl_mem_iff
                  support scale first second (some physical)).mp indexed)
      | inr physical =>
          have active :=
            (adaptiveMixedSharedLabelFormIndices_inr_mem_iff
              support scale first second physical).mp indexed
          exact second_prime (some physical)
            ((adaptiveMixedActualFormIndices_target_mem_iff
              support scale physical second).mpr active)

/-- Every unrestricted shared-label physical-lattice point lies in the true
dyadic-label/two-signed-center three-dimensional box. -/
theorem adaptiveMixedSignedSharedLabelPublishedLattice_boxed
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    adaptiveMixedSignedSharedLabelPublishedLattice
      support scale first second domain N ⊆
        (Finset.Ioc N (2 * N)).product
          ((adaptiveMixedSignedSearchCenterWindow first.1 N).product
            (adaptiveMixedSignedSearchCenterWindow second.1 N)) := by
  classical
  intro point selected
  exact (Finset.mem_filter.mp selected).1

/-- All actual deduplicated shared-label form values on the unrestricted
physical lattice satisfy the TRUE fixed cutoff `2*(scale+1)*N`. -/
theorem adaptiveMixedSignedSharedLabelPublishedLattice_form_bounded
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (point : ℕ × ℤ × ℤ)
    (selected : point ∈ adaptiveMixedSignedSharedLabelPublishedLattice
      support scale first second domain N)
    (index : Option ℕ ⊕ ℕ)
    (indexed : index ∈ adaptiveMixedSharedLabelFormIndices
      support scale first second) :
    adaptiveMixedSharedLabelSignedPrimeFormValue
      support first.1 second.1 index point ∈
        Finset.Ioc 0 (2 * (scale + 1) * N) := by
  classical
  obtain ⟨_boxed, first_lattice, second_lattice, _domain⟩ :=
    Finset.mem_filter.mp selected
  cases index with
  | inl branch =>
      have active :=
        (adaptiveMixedSharedLabelFormIndices_inl_mem_iff
          support scale first second branch).mp indexed
      cases branch with
      | none =>
          exact adaptiveMixedSignedOriginalPublishedLattice_form_bounded
            support scale first Set.univ N primes
              (point.1, point.2.1) first_lattice none active
      | some physical =>
          exact adaptiveMixedSignedOriginalPublishedLattice_form_bounded
            support scale first Set.univ N primes
              (point.1, point.2.1) first_lattice (some physical) active
  | inr physical =>
      have active :=
        (adaptiveMixedSharedLabelFormIndices_inr_mem_iff
          support scale first second physical).mp indexed
      exact adaptiveMixedSignedOriginalPublishedLattice_form_bounded
        support scale second Set.univ N primes
          (point.1, point.2.2) second_lattice (some physical)
            ((adaptiveMixedActualFormIndices_target_mem_iff
              support scale physical second).mpr active)

/-- PUBLISHED-THEOREM EXACT SHARED-LABEL interface: the unrestricted genuine
three-dimensional von Mangoldt lattice sum is EQUIVALENT to the EXISTING
literal shared-label prime count, at its exact deduplicated fixed rank. -/
theorem adaptiveMixedSignedSharedLabelPublishedVonMangoldt_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedLabelPublishedLattice
          support scale first second domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedSharedLabelFormIndices support scale first second)
              (adaptiveMixedSharedLabelSignedPrimeFormValue
                support first.1 second.1) point) / (N : ℝ) ^ 3)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedLabelPrimeRealizations
          support scale first second domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices support scale first).card +
              (adaptiveMixedOutcomeActiveIndices
                support scale second).card + 1) / (N : ℝ) ^ 3)
      atTop (nhds limit) := by
  classical
  let points := fun N =>
    adaptiveMixedSignedSharedLabelPublishedLattice
      support scale first second domain N
  let forms := adaptiveMixedSharedLabelFormIndices support scale first second
  let value :=
    adaptiveMixedSharedLabelSignedPrimeFormValue support first.1 second.1
  let bad : ℕ → ℝ := fun N =>
    (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
      (points N) forms value,
        adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 3
  have bad_vanishes : Tendsto bad atTop (nhds (0 : ℝ)) := by
    exact adaptiveMixedSignedSharedLabelPrimePowerExceptions_normalized_tendsto_zero
      support scale first second (2 * (scale + 1)) (by positivity) primes points
        (adaptiveMixedSignedSharedLabelPublishedLattice_boxed
          support scale first second domain)
        (fun N point selected index indexed =>
          adaptiveMixedSignedSharedLabelPublishedLattice_form_bounded
            support scale first second domain N primes point selected
              index indexed)
  have decomposition (N : ℕ) :
      (∑ point ∈ points N,
        adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 3 =
      (∑ point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
        support scale first second domain N,
          adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 3 +
        bad N := by
    have split :=
      adaptiveMixedVonMangoldtSum_eq_prime_sum_add_exceptions
        (points N) forms value
    change
      (∑ point ∈ points N,
        adaptiveMixedVonMangoldtProduct forms value point) =
      (∑ point ∈ adaptiveMixedAllPrimePoints (points N) forms value,
        adaptiveMixedVonMangoldtProduct forms value point) +
      ∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
        (points N) forms value,
          adaptiveMixedVonMangoldtProduct forms value point at split
    rw [adaptiveMixedSignedSharedLabelPublishedLattice_all_prime] at split
    change _ / (N : ℝ) ^ 3 = _ / (N : ℝ) ^ 3 + _ / (N : ℝ) ^ 3
    rw [split]
    ring
  have prime_weighted_iff :
      Tendsto
        (fun N : ℕ =>
          (∑ point ∈ points N,
            adaptiveMixedVonMangoldtProduct forms value point) /
              (N : ℝ) ^ 3)
        atTop (nhds limit) ↔
      Tendsto
        (fun N : ℕ =>
          (∑ point ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
            support scale first second domain N,
              adaptiveMixedVonMangoldtProduct forms value point) /
                (N : ℝ) ^ 3)
        atTop (nhds limit) := by
    constructor
    · intro full
      have removed := full.sub bad_vanishes
      convert removed using 1
      · funext N
        rw [decomposition N]
        ring
      · simp
    · intro prime_only
      have restored := prime_only.add bad_vanishes
      convert restored using 1
      · funext N
        exact decomposition N
      · simp
  exact prime_weighted_iff.trans
    (adaptiveMixedSignedSharedLabelActualVonMangoldt_asymptotic_iff
      support scale first second domain limit primes)

/-- On the TRUE same-type shared physical-target lattice, the two
distinguished reduced prime forms are exactly equal as SIGNED INTEGERS.
Thus the second distinguished prime condition can be removed exactly once. -/
theorem adaptiveMixedSignedSharedTargetPublished_distinguished_forms_eq
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (point : (ℕ × ℤ) × (ℕ × ℤ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active : firstIndex ∈
      adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active : secondIndex ∈
      adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (shared :
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support first.1 firstIndex point.1.1 point.1.2 =
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support second.1 secondIndex point.2.1 point.2.2) :
    weightedPrimePatternIntegerForm
      support first.1 firstIndex point.1.1 point.1.2 =
    weightedPrimePatternIntegerForm
      support second.1 secondIndex point.2.1 point.2.2 := by
  have first_physical := scaleAdaptiveSignedPhysicalTarget_eq_residue_add_index
    point.1.2 primes first_active (label := point.1.1)
  have second_physical := scaleAdaptiveSignedPhysicalTarget_eq_residue_add_index
    point.2.2 primes second_active (label := point.2.1)
  have scaled :
      (adaptiveMixedActualIndexType support first.1 firstIndex : ℤ) *
        weightedPrimePatternIntegerForm
          support first.1 firstIndex point.1.1 point.1.2 =
      (adaptiveMixedActualIndexType support second.1 secondIndex : ℤ) *
        weightedPrimePatternIntegerForm
          support second.1 secondIndex point.2.1 point.2.2 := by
    calc
      _ = weightedPrimePatternSignedResidue
            support first.1 point.1.1 point.1.2 +
          (firstIndex : ℤ) * (point.1.1 : ℤ) := first_physical
      _ = adaptiveMixedSignedSharedTargetPhysicalOffset
            support first.1 firstIndex point.1.1 point.1.2 := by
              unfold adaptiveMixedSignedSharedTargetPhysicalOffset
              ring
      _ = adaptiveMixedSignedSharedTargetPhysicalOffset
            support second.1 secondIndex point.2.1 point.2.2 := shared
      _ = weightedPrimePatternSignedResidue
            support second.1 point.2.1 point.2.2 +
          (secondIndex : ℤ) * (point.2.1 : ℤ) := by
              unfold adaptiveMixedSignedSharedTargetPhysicalOffset
              ring
      _ = _ := second_physical.symm
  rw [← same_type] at scaled
  have type_nonzero :
      (adaptiveMixedActualIndexType support first.1 firstIndex : ℤ) ≠ 0 := by
    exact_mod_cast
      (adaptiveMixedActualIndexType_pos_of_active primes first_active).ne'
  exact mul_left_cancel₀ type_nonzero scaled

/-- The actual primality-free FULL SHARED-TARGET lattice: two independent
dyadic labels, two signed original physical branches, exact physical target
equality, and the true three-dimensional normalized target/label domain.
Globally equal labels are deliberately allowed. -/
noncomputable def adaptiveMixedSignedSharedTargetPublishedLattice
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
      Finset ((ℕ × ℤ) × (ℕ × ℤ)) := by
  classical
  let firstCandidates := (Finset.Ioc N (2 * N)).product
    (adaptiveMixedSignedSearchCenterWindow first.1 N)
  let secondCandidates := (Finset.Ioc N (2 * N)).product
    (adaptiveMixedSignedSearchCenterWindow second.1 N)
  exact (firstCandidates.product secondCandidates).filter fun point =>
    point.1 ∈ adaptiveMixedSignedOriginalPublishedLattice
      support scale first Set.univ N ∧
    point.2 ∈ adaptiveMixedSignedOriginalPublishedLattice
      support scale second Set.univ N ∧
    adaptiveMixedSignedSharedTargetPhysicalOffset
      support first.1 firstIndex point.1.1 point.1.2 =
    adaptiveMixedSignedSharedTargetPhysicalOffset
      support second.1 secondIndex point.2.1 point.2.2 ∧
    (((adaptiveMixedSignedSharedTargetPhysicalOffset
      support first.1 firstIndex point.1.1 point.1.2 : ℤ) : ℝ) /
        (N : ℝ),
      ((point.1.1 : ℝ) / (N : ℝ)),
      ((point.2.1 : ℝ) / (N : ℝ))) ∈ domain

/-- The all-prime subset of the genuine same-type primality-free target
lattice is EXACTLY the existing unrestricted prime-realization set.  The
erased second distinguished form is recovered using BOTH active indices,
the genuine same-type identity, and exact physical-target equality. -/
theorem adaptiveMixedSignedSharedTargetPublishedLattice_all_prime
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active : firstIndex ∈
      adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active : secondIndex ∈
      adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex) :
    adaptiveMixedAllPrimePoints
      (adaptiveMixedSignedSharedTargetPublishedLattice
        support scale first second firstIndex secondIndex domain N)
      (adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex)
      (adaptiveMixedSharedTargetSignedPrimeFormValue
        support first.1 second.1) =
          adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
            support scale first second firstIndex secondIndex domain N := by
  classical
  ext point
  constructor
  · intro selected
    obtain ⟨in_lattice, all_prime⟩ := Finset.mem_filter.mp selected
    obtain ⟨boxed, first_lattice, second_lattice,
      shared, in_domain⟩ := Finset.mem_filter.mp in_lattice
    have first_all_prime :
        point.1 ∈ adaptiveMixedAllPrimePoints
          (adaptiveMixedSignedOriginalPublishedLattice
            support scale first Set.univ N)
          (adaptiveMixedActualFormIndices support scale first)
          (adaptiveMixedActualSignedPrimeFormValue support first.1) := by
      apply Finset.mem_filter.mpr
      refine ⟨first_lattice, ?_⟩
      intro index indexed
      exact all_prime (Sum.inl index)
        ((adaptiveMixedSharedTargetFormIndices_inl_mem_iff
          support scale first second secondIndex index).mpr indexed)
    have second_all_prime :
        point.2 ∈ adaptiveMixedAllPrimePoints
          (adaptiveMixedSignedOriginalPublishedLattice
            support scale second Set.univ N)
          (adaptiveMixedActualFormIndices support scale second)
          (adaptiveMixedActualSignedPrimeFormValue support second.1) := by
      apply Finset.mem_filter.mpr
      refine ⟨second_lattice, ?_⟩
      intro index indexed
      by_cases distinguished : index = some secondIndex
      · subst index
        have first_indexed :=
          (adaptiveMixedActualFormIndices_target_mem_iff
            support scale firstIndex first).mpr first_active
        have first_prime := all_prime (Sum.inl (some firstIndex))
          ((adaptiveMixedSharedTargetFormIndices_inl_mem_iff
            support scale first second secondIndex
              (some firstIndex)).mpr first_indexed)
        have same_forms :=
          adaptiveMixedSignedSharedTargetPublished_distinguished_forms_eq
            point primes first_active second_active same_type shared
        have same_naturals := congrArg Int.toNat same_forms
        change Nat.Prime
          ((weightedPrimePatternIntegerForm
            support second.1 secondIndex point.2.1 point.2.2).toNat)
        change Nat.Prime
          ((weightedPrimePatternIntegerForm
            support first.1 firstIndex point.1.1 point.1.2).toNat) at first_prime
        exact same_naturals ▸ first_prime
      · exact all_prime (Sum.inr index)
          ((adaptiveMixedSharedTargetFormIndices_inr_mem_iff
            support scale first second secondIndex index).mpr
              ⟨distinguished, indexed⟩)
    rw [adaptiveMixedSignedOriginalPublishedLattice_all_prime] at first_all_prime
    rw [adaptiveMixedSignedOriginalPublishedLattice_all_prime] at second_all_prime
    simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter, Set.mem_univ, and_true] at first_all_prime second_all_prime
    apply (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
      support scale first second firstIndex secondIndex domain N point).mpr
    exact ⟨(Finset.mem_product.mp boxed).1,
      (Finset.mem_product.mp boxed).2,
      first_all_prime.2, second_all_prime.2, shared, in_domain⟩
  · intro selected
    obtain ⟨first_boxed, second_boxed, first_edge, second_edge,
      shared, in_domain⟩ :=
        (mem_adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N point).mp
            selected
    have first_real :
        point.1 ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale first Set.univ N := by
      simp only [adaptiveMixedSignedOriginalPrimeRealizations,
        Finset.mem_filter, Set.mem_univ, and_true]
      exact ⟨first_boxed, first_edge⟩
    have second_real :
        point.2 ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale second Set.univ N := by
      simp only [adaptiveMixedSignedOriginalPrimeRealizations,
        Finset.mem_filter, Set.mem_univ, and_true]
      exact ⟨second_boxed, second_edge⟩
    rw [← adaptiveMixedSignedOriginalPublishedLattice_all_prime] at first_real
    rw [← adaptiveMixedSignedOriginalPublishedLattice_all_prime] at second_real
    obtain ⟨first_lattice, first_prime⟩ := Finset.mem_filter.mp first_real
    obtain ⟨second_lattice, second_prime⟩ := Finset.mem_filter.mp second_real
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨first_boxed, second_boxed⟩,
          first_lattice, second_lattice, shared, in_domain⟩
    · intro index indexed
      cases index with
      | inl branch =>
          exact first_prime branch
            ((adaptiveMixedSharedTargetFormIndices_inl_mem_iff
              support scale first second secondIndex branch).mp indexed)
      | inr branch =>
          have active :=
            (adaptiveMixedSharedTargetFormIndices_inr_mem_iff
              support scale first second secondIndex branch).mp indexed
          exact second_prime branch active.2

/- Every true primality-free shared-target point lies in the actual four-
coordinate dyadic-label/signed-center box. -/
theorem adaptiveMixedSignedSharedTargetPublishedLattice_boxed
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    adaptiveMixedSignedSharedTargetPublishedLattice
      support scale first second firstIndex secondIndex domain N ⊆
        ((Finset.Ioc N (2 * N)).product
          (adaptiveMixedSignedSearchCenterWindow first.1 N)).product
        ((Finset.Ioc N (2 * N)).product
          (adaptiveMixedSignedSearchCenterWindow second.1 N)) := by
  classical
  intro point selected
  exact (Finset.mem_filter.mp selected).1

/-- Every primality-free published shared-target point satisfies the exact
genuine physical-target equality, with no restriction on global labels. -/
theorem adaptiveMixedSignedSharedTargetPublishedLattice_shared
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (point : (ℕ × ℤ) × (ℕ × ℤ))
    (selected : point ∈ adaptiveMixedSignedSharedTargetPublishedLattice
      support scale first second firstIndex secondIndex domain N) :
    adaptiveMixedSignedSharedTargetPhysicalOffset
      support first.1 firstIndex point.1.1 point.1.2 =
    adaptiveMixedSignedSharedTargetPhysicalOffset
      support second.1 secondIndex point.2.1 point.2.2 := by
  classical
  exact (Finset.mem_filter.mp selected).2.2.2.1

/-- Every deduplicated true shared-target form on the unrestricted physical
lattice satisfies the automatic source-faithful cutoff
`2 * (scale + 1) * N`, without any primality assumption. -/
theorem adaptiveMixedSignedSharedTargetPublishedLattice_form_bounded
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (point : (ℕ × ℤ) × (ℕ × ℤ))
    (selected : point ∈ adaptiveMixedSignedSharedTargetPublishedLattice
      support scale first second firstIndex secondIndex domain N)
    (index : Option ℕ ⊕ Option ℕ)
    (indexed : index ∈ adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex) :
    adaptiveMixedSharedTargetSignedPrimeFormValue
      support first.1 second.1 index point ∈
        Finset.Ioc 0 (2 * (scale + 1) * N) := by
  classical
  obtain ⟨_boxed, first_lattice, second_lattice, _shared, _domain⟩ :=
    Finset.mem_filter.mp selected
  cases index with
  | inl branch =>
      have active :=
        (adaptiveMixedSharedTargetFormIndices_inl_mem_iff
          support scale first second secondIndex branch).mp indexed
      exact adaptiveMixedSignedOriginalPublishedLattice_form_bounded
        support scale first Set.univ N primes point.1
          first_lattice branch active
  | inr branch =>
      have active :=
        (adaptiveMixedSharedTargetFormIndices_inr_mem_iff
          support scale first second secondIndex branch).mp indexed
      exact adaptiveMixedSignedOriginalPublishedLattice_form_bounded
        support scale second Set.univ N primes point.2
          second_lattice branch active.2

/-- PUBLISHED-THEOREM EXACT FULL SHARED-TARGET interface: the unrestricted
genuine three-dimensional von Mangoldt lattice sum, including globally equal
labels, is EQUIVALENT to the existing literal unrestricted prime-realization
count.  The second distinguished form is deduplicated ONLY after its actual
same-type equality has been established. -/
theorem adaptiveMixedSignedSharedTargetPublishedVonMangoldt_asymptotic_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (limit : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active : firstIndex ∈
      adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active : secondIndex ∈
      adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ adaptiveMixedSignedSharedTargetPublishedLattice
          support scale first second firstIndex secondIndex domain N,
            adaptiveMixedVonMangoldtProduct
              (adaptiveMixedSharedTargetFormIndices
                support scale first second secondIndex)
              (adaptiveMixedSharedTargetSignedPrimeFormValue
                support first.1 second.1) point) / (N : ℝ) ^ 3)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
          support scale first second firstIndex secondIndex domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices support scale first).card +
              (adaptiveMixedOutcomeActiveIndices
                support scale second).card + 1) / (N : ℝ) ^ 3)
      atTop (nhds limit) := by
  classical
  let points := fun N =>
    adaptiveMixedSignedSharedTargetPublishedLattice
      support scale first second firstIndex secondIndex domain N
  let forms := adaptiveMixedSharedTargetFormIndices
    support scale first second secondIndex
  let value :=
    adaptiveMixedSharedTargetSignedPrimeFormValue support first.1 second.1
  let bad : ℕ → ℝ := fun N =>
    (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
      (points N) forms value,
        adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 3
  have bad_vanishes : Tendsto bad atTop (nhds (0 : ℝ)) := by
    exact adaptiveMixedSignedSharedTargetPrimePowerExceptions_normalized_tendsto_zero
      support scale first second firstIndex secondIndex
        (2 * (scale + 1)) (by positivity) primes points
        (adaptiveMixedSignedSharedTargetPublishedLattice_boxed
          support scale first second firstIndex secondIndex domain)
        (fun N point selected =>
          adaptiveMixedSignedSharedTargetPublishedLattice_shared
            support scale first second firstIndex secondIndex domain N
              point selected)
        (fun N point selected index indexed =>
          adaptiveMixedSignedSharedTargetPublishedLattice_form_bounded
            support scale first second firstIndex secondIndex domain N
              primes point selected index indexed)
  have decomposition (N : ℕ) :
      (∑ point ∈ points N,
        adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 3 =
      (∑ point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
        support scale first second firstIndex secondIndex domain N,
          adaptiveMixedVonMangoldtProduct forms value point) / (N : ℝ) ^ 3 +
        bad N := by
    have split :=
      adaptiveMixedVonMangoldtSum_eq_prime_sum_add_exceptions
        (points N) forms value
    change
      (∑ point ∈ points N,
        adaptiveMixedVonMangoldtProduct forms value point) =
      (∑ point ∈ adaptiveMixedAllPrimePoints (points N) forms value,
        adaptiveMixedVonMangoldtProduct forms value point) +
      ∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
        (points N) forms value,
          adaptiveMixedVonMangoldtProduct forms value point at split
    rw [adaptiveMixedSignedSharedTargetPublishedLattice_all_prime
      support scale first second firstIndex secondIndex domain N
        primes first_active second_active same_type] at split
    change _ / (N : ℝ) ^ 3 = _ / (N : ℝ) ^ 3 + _ / (N : ℝ) ^ 3
    rw [split]
    ring
  have prime_weighted_iff :
      Tendsto
        (fun N : ℕ =>
          (∑ point ∈ points N,
            adaptiveMixedVonMangoldtProduct forms value point) /
              (N : ℝ) ^ 3)
        atTop (nhds limit) ↔
      Tendsto
        (fun N : ℕ =>
          (∑ point ∈ adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
            support scale first second firstIndex secondIndex domain N,
              adaptiveMixedVonMangoldtProduct forms value point) /
                (N : ℝ) ^ 3)
        atTop (nhds limit) := by
    constructor
    · intro full
      have removed := full.sub bad_vanishes
      convert removed using 1
      · funext N
        rw [decomposition N]
        ring
      · simp
    · intro prime_only
      have restored := prime_only.add bad_vanishes
      convert restored using 1
      · funext N
        exact decomposition N
      · simp
  exact prime_weighted_iff.trans
    (adaptiveMixedSignedSharedTargetUnrestrictedActualVonMangoldt_asymptotic_iff
      support scale first second firstIndex secondIndex domain limit
        primes second_active)

end Erdos1139

