module

public import ScaleAdaptivePrimeSliceVariance1139
public import ScaleAdaptiveWeightedDegreeLimit1139
public import ScaleAdaptiveGTZSharedTargetMoments1139
public import ScaleAdaptiveConstantBandTargetMoments1139
public import ScaleAdaptiveTruncatedBandFirstMoment1139

@[expose] public section


/-!
# Actual typed targets and constant-band target concentration

For a fixed genuine mixed index `i` of actual type `s`, the constant
absolute-residue band has target mean `s / i`, not an unspecified constant.
In an unclipped target cell `(L*N,U*N]`, the true target density is

    (U-L)/s * N/log N.

The original and shared-target prime counts have coefficients `(U-L)/i` and
`(U-L)*s/i²` after division by the ACTUAL constant-band degree.  Their centered
second moment therefore cancels exactly.  Same-label diagonal and
inverse-degree transfer must be retained; no real-domain witness is treated
as a prime, and no target-moment or covering hypothesis is inserted.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 800000

/-- Exact ordinary PNT at an arbitrary fixed positive RATIONAL scaled cutoff,
including the actual integer rounding.  This is an unconditional consequence
of the previously audited progression prime number theorem. -/
theorem scaleAdaptivePrimeCounting_mul_div_normalized_tendsto
    (numerator denominator : ℕ)
    (numerator_positive : 0 < numerator)
    (denominator_positive : 0 < denominator) :
    Tendsto
      (fun N : ℕ =>
        (Nat.primeCounting (numerator * N / denominator) : ℝ) *
          Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds ((numerator : ℝ) / (denominator : ℝ))) := by
  have identity_top : Tendsto (fun N : ℕ => N) atTop atTop := tendsto_id
  have multiplied_top :
      Tendsto (fun N : ℕ => numerator * N) atTop atTop :=
    Filter.tendsto_atTop_mono
      (fun N => Nat.le_mul_of_pos_left N numerator_positive)
      identity_top
  have cutoff :=
    (primeCounting_fixed_cutoff_normalized_tendsto
      denominator denominator_positive).comp multiplied_top
  have inverse_log_ratio :
      Tendsto
        (fun N : ℕ =>
          Real.log (N : ℝ) /
            Real.log ((numerator * N : ℕ) : ℝ))
        atTop (nhds (1 : ℝ)) := by
    convert (Erdos689.nat_div_log_ratio_tendsto
      numerator numerator_positive).comp multiplied_top using 1
    ext N
    dsimp [Function.comp_def]
    rw [Nat.mul_div_cancel_left N numerator_positive]
  have combined := cutoff.mul
    (inverse_log_ratio.const_mul (numerator : ℝ))
  have target :
      Tendsto
        (fun N : ℕ =>
          ((Nat.primeCounting (numerator * N / denominator) : ℝ) /
            (((numerator * N : ℕ) : ℝ) /
              Real.log ((numerator * N : ℕ) : ℝ))) *
            ((numerator : ℝ) *
              (Real.log (N : ℝ) /
                Real.log ((numerator * N : ℕ) : ℝ))))
        atTop (nhds ((numerator : ℝ) / (denominator : ℝ))) := by
    simpa [Function.comp_def, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using combined
  apply target.congr'
  filter_upwards [eventually_ge_atTop 2] with N large
  have N_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have numerator_nonzero : (numerator : ℝ) ≠ 0 := by
    exact_mod_cast numerator_positive.ne'
  have product_log_nonzero :
      Real.log ((numerator * N : ℕ) : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast Nat.mul_pos numerator_positive (by omega : 0 < N)
    · exact_mod_cast (by
        have := Nat.mul_le_mul_left numerator large
        omega : numerator * N ≠ 1)
  have product_log_nonzero' :
      Real.log ((numerator : ℝ) * (N : ℝ)) ≠ 0 := by
    exact_mod_cast product_log_nonzero
  push_cast
  field_simp [N_nonzero, numerator_nonzero, product_log_nonzero']

/-- The EXACT finite set of type-`s` prime or semiprime targets in an
integer-endpoint target cell.  Its elements are genuine integers `s*q` for
actual primes `q`; no real-geometry witness is included. -/
def scaleAdaptiveTypedPrimeTargetsInIntegerCell
    (targetType targetLower targetUpper N : ℕ) : Finset ℕ :=
  ((Nat.primesLE (targetUpper * N / targetType)) \
    Nat.primesLE (targetLower * N / targetType)).image
      fun prime => targetType * prime

/-- Source-faithful membership in the typed target cell: the target is the
actual integer `s*q`, its quotient is genuinely prime, and it satisfies the
original strict-lower/closed-upper physical target endpoints. -/
theorem mem_scaleAdaptiveTypedPrimeTargetsInIntegerCell
    {targetType targetLower targetUpper N target : ℕ}
    (type_positive : 0 < targetType) :
    target ∈ scaleAdaptiveTypedPrimeTargetsInIntegerCell
      targetType targetLower targetUpper N ↔
      ∃ prime : ℕ, prime.Prime ∧
        targetLower * N < target ∧ target ≤ targetUpper * N ∧
          target = targetType * prime := by
  unfold scaleAdaptiveTypedPrimeTargetsInIntegerCell
  constructor
  · intro selected
    obtain ⟨prime, selected, equal⟩ := Finset.mem_image.mp selected
    obtain ⟨upper, not_lower⟩ := Finset.mem_sdiff.mp selected
    obtain ⟨upper_bound, prime_certificate⟩ := Nat.mem_primesLE.mp upper
    have lower_bound : targetLower * N / targetType < prime := by
      apply Nat.lt_of_not_ge
      intro bounded
      exact not_lower (Nat.mem_primesLE.mpr ⟨bounded, prime_certificate⟩)
    have lower_product :=
      (Nat.div_lt_iff_lt_mul type_positive).mp lower_bound
    have upper_product :=
      (Nat.le_div_iff_mul_le type_positive).mp upper_bound
    refine ⟨prime, prime_certificate, ?_, ?_, equal.symm⟩
    · simpa [equal, Nat.mul_comm] using lower_product
    · simpa [equal, Nat.mul_comm] using upper_product
  · rintro ⟨prime, prime_certificate, lower_bound, upper_bound, equal⟩
    subst target
    apply Finset.mem_image.mpr
    refine ⟨prime, ?_, rfl⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Nat.mem_primesLE.mpr
      refine ⟨?_, prime_certificate⟩
      apply (Nat.le_div_iff_mul_le type_positive).mpr
      simpa [Nat.mul_comm] using upper_bound
    · intro small
      have bounded := (Nat.mem_primesLE.mp small).1
      have strict : targetLower * N / targetType < prime :=
        (Nat.div_lt_iff_lt_mul type_positive).mpr (by
          simpa [Nat.mul_comm] using lower_bound)
      omega

/-- Multiplication by a positive genuine target type is injective, so the
typed-target cell retains its exact prime-counting cardinality. -/
theorem scaleAdaptiveTypedPrimeTargetsInIntegerCell_card
    (targetType targetLower targetUpper N : ℕ)
    (type_positive : 0 < targetType)
    (ordered : targetLower ≤ targetUpper) :
    (scaleAdaptiveTypedPrimeTargetsInIntegerCell
      targetType targetLower targetUpper N).card =
      Nat.primeCounting (targetUpper * N / targetType) -
        Nat.primeCounting (targetLower * N / targetType) := by
  unfold scaleAdaptiveTypedPrimeTargetsInIntegerCell
  rw [Finset.card_image_iff.mpr]
  · rw [Finset.card_sdiff_of_subset]
    · simp only [Nat.primesLE_card_eq_primeCounting]
    · exact Nat.primesLE_mono
        (Nat.div_le_div_right (Nat.mul_le_mul_right N ordered))
  · intro first _ second _ same
    exact Nat.eq_of_mul_eq_mul_left type_positive same

/-- UNCONDITIONAL source-faithful prime-density asymptotic for genuine typed
targets, including the correct physical factor `1/s` and both integer-rounded
endpoints. -/
theorem scaleAdaptiveTypedPrimeTargetsInIntegerCell_normalized_tendsto
    (targetType targetLower targetUpper : ℕ)
    (type_positive : 0 < targetType)
    (lower_positive : 0 < targetLower)
    (ordered : targetLower ≤ targetUpper) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveTypedPrimeTargetsInIntegerCell
          targetType targetLower targetUpper N).card : ℝ) *
          Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds
        (((targetUpper : ℝ) - (targetLower : ℝ)) /
          (targetType : ℝ))) := by
  have upper_positive : 0 < targetUpper :=
    lt_of_lt_of_le lower_positive ordered
  have upper := scaleAdaptivePrimeCounting_mul_div_normalized_tendsto
    targetUpper targetType upper_positive type_positive
  have lower := scaleAdaptivePrimeCounting_mul_div_normalized_tendsto
    targetLower targetType lower_positive type_positive
  have difference := upper.sub lower
  have target :
      Tendsto
        (fun N : ℕ =>
          (Nat.primeCounting (targetUpper * N / targetType) : ℝ) *
              Real.log (N : ℝ) / (N : ℝ) -
            (Nat.primeCounting (targetLower * N / targetType) : ℝ) *
              Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds
          (((targetUpper : ℝ) - (targetLower : ℝ)) /
            (targetType : ℝ))) := by
    convert difference using 1
    ring_nf
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp
    rw [scaleAdaptiveTypedPrimeTargetsInIntegerCell_card
      targetType targetLower targetUpper N type_positive ordered,
      Nat.cast_sub (Nat.monotone_primeCounting
        (Nat.div_le_div_right (Nat.mul_le_mul_right N ordered)))]
    ring_nf

/-- Every genuine retained-index physical target is exactly its ACTUAL type
times a genuine prime affine form.  In particular an actual edge targets a
real prime (`s=1`) or its correctly typed semiprime (`s>1`), not merely an
integer suggested by continuous geometry. -/
theorem scaleAdaptiveGTZIndexedPhysicalTarget_eq_type_mul_prime_form
    {support : Finset ℕ} {scale index N : ℕ}
    {outcome : ℕ × ℕ} {domain : Set (ℝ × ℝ)}
    {pair : ℕ × ℤ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (selected : pair ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N) :
    scaleAdaptiveGTZIndexedPhysicalTarget
      support outcome.1 index pair.1 pair.2 =
        adaptiveMixedActualIndexType support outcome.1 index *
          (weightedPrimePatternIntegerForm
            support outcome.1 index pair.1 pair.2).toNat ∧
      (weightedPrimePatternIntegerForm
        support outcome.1 index pair.1 pair.2).toNat.Prime := by
  classical
  have edge :=
    (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
      support scale outcome domain N pair).mp selected |>.2
  have raw_edge := (Finset.mem_filter.mp edge).1
  have certificate := weightedPrimePatternEdges_prime_certificate
    support scale outcome
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
      pair.1 pair.2 raw_edge
  have form_positive := (certificate.2.2.2.2 index active).2.1
  have form_prime := (certificate.2.2.2.2 index active).2.2
  refine ⟨?_, form_prime⟩
  have index_nonnegative : (0 : ℤ) ≤ index := Int.natCast_nonneg _
  have label_nonnegative : (0 : ℤ) ≤ pair.1 := Int.natCast_nonneg _
  have raw_nonnegative :
      0 ≤ (index : ℤ) * (pair.1 : ℤ) +
        weightedPrimePatternSignedResidue
          support outcome.1 pair.1 pair.2 :=
    add_nonneg (mul_nonneg index_nonnegative label_nonnegative)
      certificate.2.2.1
  have identity := scaleAdaptiveSignedPhysicalTarget_eq_residue_add_index
    (label := pair.1) pair.2 primes active
  have cast_equality :
      ((scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index pair.1 pair.2 : ℕ) : ℤ) =
        ((adaptiveMixedActualIndexType support outcome.1 index *
          (weightedPrimePatternIntegerForm
            support outcome.1 index pair.1 pair.2).toNat : ℕ) : ℤ) := by
    unfold scaleAdaptiveGTZIndexedPhysicalTarget
    rw [Int.toNat_of_nonneg raw_nonnegative]
    push_cast
    rw [Int.toNat_of_nonneg form_positive.le]
    nlinarith
  exact_mod_cast cast_equality

/-- A genuine actual signed prime-pattern edge in the prescribed integer
target interval belongs to the exact corresponding typed-prime target set. -/
theorem scaleAdaptiveGTZIndexedPhysicalTarget_mem_typed_cell
    {support : Finset ℕ} {scale index N targetLower targetUpper : ℕ}
    {outcome : ℕ × ℕ} {domain : Set (ℝ × ℝ)}
    {pair : ℕ × ℤ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (selected : pair ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N)
    (lower : targetLower * N <
      scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index pair.1 pair.2)
    (upper : scaleAdaptiveGTZIndexedPhysicalTarget
      support outcome.1 index pair.1 pair.2 ≤ targetUpper * N) :
    scaleAdaptiveGTZIndexedPhysicalTarget
      support outcome.1 index pair.1 pair.2 ∈
        scaleAdaptiveTypedPrimeTargetsInIntegerCell
          (adaptiveMixedActualIndexType support outcome.1 index)
          targetLower targetUpper N := by
  have type_positive :=
    adaptiveMixedActualIndexType_pos_of_active primes active
  obtain ⟨factorization, prime⟩ :=
    scaleAdaptiveGTZIndexedPhysicalTarget_eq_type_mul_prime_form
      primes active selected
  apply (mem_scaleAdaptiveTypedPrimeTargetsInIntegerCell
    type_positive).mpr
  exact ⟨_, prime, lower, upper, factorization⟩

/-- The normalized physical target of an ACTUAL signed prime-pattern edge is
exactly the genuine affine target in its normalized signed physical domain.
The integer `toNat` is removed using the actual nonnegative fundamental
residue certificate; no real-geometry point is promoted to a prime edge. -/
theorem scaleAdaptiveGTZIndexedPhysicalTarget_normalized_eq
    {support : Finset ℕ} {scale index N : ℕ}
    {outcome : ℕ × ℕ} {domain : Set (ℝ × ℝ)}
    {pair : ℕ × ℤ}
    (selected : pair ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N) :
    ((scaleAdaptiveGTZIndexedPhysicalTarget
      support outcome.1 index pair.1 pair.2 : ℕ) : ℝ) / (N : ℝ) =
      (index : ℝ) * ((pair.1 : ℝ) / (N : ℝ)) +
        ((outcome.1 : ℝ) * ((pair.1 : ℝ) / (N : ℝ)) +
          (adaptiveMixedTypeModulus support : ℝ) *
            ((pair.2 : ℝ) / (N : ℝ))) := by
  classical
  have decoded := selected
  simp only [adaptiveMixedSignedOriginalPrimeRealizations,
    Finset.mem_filter] at decoded
  have certificate := weightedPrimePatternEdges_prime_certificate
    support scale outcome
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
      pair.1 pair.2 decoded.2.1
  have raw_nonnegative :
      0 ≤ (index : ℤ) * (pair.1 : ℤ) +
        weightedPrimePatternSignedResidue
          support outcome.1 pair.1 pair.2 :=
    add_nonneg
      (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      certificate.2.2.1
  have cast_target :
      ((scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index pair.1 pair.2 : ℕ) : ℤ) =
        (index : ℤ) * (pair.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.1 pair.2 := by
    exact Int.toNat_of_nonneg raw_nonnegative
  have real_target := congrArg (fun value : ℤ => (value : ℝ)) cast_target
  unfold weightedPrimePatternSignedResidue at real_target
  push_cast at real_target
  rw [real_target]
  ring_nf

/-- Every actual edge in the target-TRUNCATED signed physical domain maps
into the exact integer type-`s` prime-target cell.  Both strict physical
target bounds come from its actual normalized affine domain. -/
theorem scaleAdaptiveTruncatedBandSignedRealization_mem_typed_targets
    {support : Finset ℕ} {scale index N targetLower targetUpper : ℕ}
    {outcome : ℕ × ℕ} {lower upper : ℝ} {pair : ℕ × ℤ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (selected : pair ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome
        (scaleAdaptiveTruncatedBandSignedDomain
          support outcome.1 index lower upper
            (targetLower : ℝ) (targetUpper : ℝ)) N) :
    scaleAdaptiveGTZIndexedPhysicalTarget
      support outcome.1 index pair.1 pair.2 ∈
        scaleAdaptiveTypedPrimeTargetsInIntegerCell
          (adaptiveMixedActualIndexType support outcome.1 index)
            targetLower targetUpper N := by
  classical
  have decoded := selected
  simp only [adaptiveMixedSignedOriginalPrimeRealizations,
    Finset.mem_filter] at decoded
  have label_bounds :=
    Finset.mem_Ioc.mp (Finset.mem_product.mp decoded.1).1
  have N_positive : 0 < N := by omega
  have N_real : (0 : ℝ) < N := by exact_mod_cast N_positive
  have normalized :=
    scaleAdaptiveGTZIndexedPhysicalTarget_normalized_eq
      (index := index) selected
  have physical := decoded.2.2
  change
    1 < (pair.1 : ℝ) / (N : ℝ) ∧
      (pair.1 : ℝ) / (N : ℝ) < 2 ∧
      lower < (outcome.1 : ℝ) * ((pair.1 : ℝ) / (N : ℝ)) +
        (adaptiveMixedTypeModulus support : ℝ) *
          ((pair.2 : ℝ) / (N : ℝ)) ∧
      (outcome.1 : ℝ) * ((pair.1 : ℝ) / (N : ℝ)) +
        (adaptiveMixedTypeModulus support : ℝ) *
          ((pair.2 : ℝ) / (N : ℝ)) < upper ∧
      (targetLower : ℝ) <
        (index : ℝ) * ((pair.1 : ℝ) / (N : ℝ)) +
          ((outcome.1 : ℝ) * ((pair.1 : ℝ) / (N : ℝ)) +
            (adaptiveMixedTypeModulus support : ℝ) *
              ((pair.2 : ℝ) / (N : ℝ))) ∧
      (index : ℝ) * ((pair.1 : ℝ) / (N : ℝ)) +
          ((outcome.1 : ℝ) * ((pair.1 : ℝ) / (N : ℝ)) +
            (adaptiveMixedTypeModulus support : ℝ) *
              ((pair.2 : ℝ) / (N : ℝ))) <
        (targetUpper : ℝ) at physical
  have lower_real :
      (targetLower : ℝ) * (N : ℝ) <
        (scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index pair.1 pair.2 : ℝ) :=
    (lt_div_iff₀ N_real).mp (normalized ▸ physical.2.2.2.2.1)
  have upper_real :
      (scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index pair.1 pair.2 : ℝ) <
          (targetUpper : ℝ) * (N : ℝ) :=
    (div_lt_iff₀ N_real).mp (normalized ▸ physical.2.2.2.2.2)
  apply scaleAdaptiveGTZIndexedPhysicalTarget_mem_typed_cell
    primes active selected
  · exact_mod_cast lower_real
  · have strict :
        scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index pair.1 pair.2 <
            targetUpper * N := by
        exact_mod_cast upper_real
    exact strict.le

/-- At a fixed actual label and physical index, two signed centers cannot
produce the same physical target: the genuine squared-core modulus is
strictly positive.  This proves that the entire same-label target diagonal
contains exactly ONE edge per realization, rather than a heuristic bound. -/
theorem scaleAdaptiveGTZIndexedTargetFiber_label_injective
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    {first second : ℕ × ℤ}
    (first_selected : first ∈ scaleAdaptiveGTZIndexedTargetFiber
      support scale outcome domain index N target)
    (second_selected : second ∈ scaleAdaptiveGTZIndexedTargetFiber
      support scale outcome domain index N target)
    (same_label : first.1 = second.1) :
    first = second := by
  classical
  obtain ⟨first_original, first_target⟩ :=
    Finset.mem_filter.mp first_selected
  obtain ⟨second_original, second_target⟩ :=
    Finset.mem_filter.mp second_selected
  have first_degree :=
    (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
      support scale outcome domain N first).mp first_original |>.2
  have second_degree :=
    (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
      support scale outcome domain N second).mp second_original |>.2
  have first_certificate := weightedPrimePatternEdges_prime_certificate
    support scale outcome
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
      first.1 first.2 (Finset.mem_filter.mp first_degree).1
  have second_certificate := weightedPrimePatternEdges_prime_certificate
    support scale outcome
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
      second.1 second.2 (Finset.mem_filter.mp second_degree).1
  have index_nonnegative : (0 : ℤ) ≤ index := Int.natCast_nonneg _
  have first_raw_nonnegative :
      0 ≤ (index : ℤ) * (first.1 : ℤ) +
        weightedPrimePatternSignedResidue
          support outcome.1 first.1 first.2 :=
    add_nonneg (mul_nonneg index_nonnegative (Int.natCast_nonneg _))
      first_certificate.2.2.1
  have second_raw_nonnegative :
      0 ≤ (index : ℤ) * (second.1 : ℤ) +
        weightedPrimePatternSignedResidue
          support outcome.1 second.1 second.2 :=
    add_nonneg (mul_nonneg index_nonnegative (Int.natCast_nonneg _))
      second_certificate.2.2.1
  have target_equal :
      scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index first.1 first.2 =
        scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index second.1 second.2 :=
    first_target.trans second_target.symm
  have integer_target_equal :=
    congrArg (fun value : ℕ => (value : ℤ)) target_equal
  unfold scaleAdaptiveGTZIndexedPhysicalTarget at integer_target_equal
  rw [Int.toNat_of_nonneg first_raw_nonnegative,
    Int.toNat_of_nonneg second_raw_nonnegative] at integer_target_equal
  have modulus_nonzero :
      (adaptiveMixedTypeModulus support : ℤ) ≠ 0 := by
    exact_mod_cast (adaptiveMixedTypeModulus_pos support primes).ne'
  have center_scaled :
      (adaptiveMixedTypeModulus support : ℤ) * first.2 =
        (adaptiveMixedTypeModulus support : ℤ) * second.2 := by
    unfold weightedPrimePatternSignedResidue at integer_target_equal
    have labels_cast : (first.1 : ℤ) = (second.1 : ℤ) := by
      exact_mod_cast same_label
    rw [labels_cast] at integer_target_equal
    omega
  have centers := mul_left_cancel₀ modulus_nonzero center_scaled
  exact Prod.ext same_label centers

/-- The exact ordered distinct-edge target-pair fiber.  On an actual
same-index signed target fiber, distinct edges are automatically globally
distinct PRIME LABELS by the preceding injectivity theorem. -/
noncomputable def scaleAdaptiveIndexedTargetDistinctLabelPairs
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ) :
    Finset ((ℕ × ℤ) × (ℕ × ℤ)) :=
  (scaleAdaptiveGTZIndexedTargetFiber
    support scale outcome domain index N target).offDiag

/-- Every actual ordered off-diagonal target pair has genuinely DISTINCT
prime labels; pair inequality is not substituted for label inequality. -/
theorem scaleAdaptiveIndexedTargetDistinctLabelPairs_labels_ne
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    {pair : (ℕ × ℤ) × (ℕ × ℤ)}
    (selected : pair ∈ scaleAdaptiveIndexedTargetDistinctLabelPairs
      support scale outcome domain index N target) :
    pair.1.1 ≠ pair.2.1 := by
  have decoded := Finset.mem_offDiag.mp selected
  intro same
  exact decoded.2.2
    (scaleAdaptiveGTZIndexedTargetFiber_label_injective
      support scale outcome domain index N target primes
        decoded.1 decoded.2.1 same)

/-- EXACT same-label diagonal decomposition for one actual target fiber:
the square of its true prime-edge incidence is the number of ordered
distinct-label pairs PLUS the number of actual edges. -/
theorem scaleAdaptiveGTZIndexedTargetFiber_square_eq_distinct_add_diagonal
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ) :
    (scaleAdaptiveGTZIndexedTargetFiber
      support scale outcome domain index N target).card ^ 2 =
      (scaleAdaptiveIndexedTargetDistinctLabelPairs
        support scale outcome domain index N target).card +
        (scaleAdaptiveGTZIndexedTargetFiber
          support scale outcome domain index N target).card := by
  unfold scaleAdaptiveIndexedTargetDistinctLabelPairs
  rw [Finset.offDiag_card]
  have bounded := Nat.le_mul_self
    (scaleAdaptiveGTZIndexedTargetFiber
      support scale outcome domain index N target).card
  rw [pow_two]
  omega

/-- The complete targetwise actual raw second moment decomposes EXACTLY
into genuine ordered distinct-label energy plus the full same-label first
moment.  There is no missing shot-noise or repeated-center assumption. -/
theorem scaleAdaptiveGTZIndexedTarget_secondMoment_eq_distinct_add_first
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) :
    (∑ target ∈ targets,
      ((scaleAdaptiveGTZIndexedTargetFiber
        support scale outcome domain index N target).card : ℝ) ^ 2) =
      (∑ target ∈ targets,
        ((scaleAdaptiveIndexedTargetDistinctLabelPairs
          support scale outcome domain index N target).card : ℝ)) +
      (∑ target ∈ targets,
        ((scaleAdaptiveGTZIndexedTargetFiber
          support scale outcome domain index N target).card : ℝ)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro target _
  exact_mod_cast
    scaleAdaptiveGTZIndexedTargetFiber_square_eq_distinct_add_diagonal
      support scale outcome domain index N target

/-- Exact number of ACTUAL signed prime edges in the target-truncated
constant-residue band.  The actual label and every active mixed prime form
are required by `adaptiveMixedSignedOriginalPrimeRealizations`. -/
noncomputable def scaleAdaptiveConstantBandTruncatedFirstCount
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index : ℕ) (lower upper : ℝ)
    (targetLower targetUpper N : ℕ) : ℕ :=
  (adaptiveMixedSignedOriginalPrimeRealizations support scale outcome
    (scaleAdaptiveTruncatedBandSignedDomain
      support outcome.1 index lower upper
        (targetLower : ℝ) (targetUpper : ℝ)) N).card

/-- Exact number of ordered ACTUAL distinct-prime-label target coincidences
inside the same unclipped constant-residue physical target window. -/
noncomputable def scaleAdaptiveConstantBandSharedOffDiagonalCount
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index : ℕ) (lower upper : ℝ)
    (targetLower targetUpper N : ℕ) : ℕ :=
  (adaptiveMixedSignedSharedTargetPrimeRealizations
    support scale outcome outcome index index
      (scaleAdaptiveConstantBandSharedTargetDomain
        index index lower upper (targetLower : ℝ) (targetUpper : ℝ)) N).card

/-- EXACT first incidence partition over the actual typed PRIME target set,
not over a padded real interval.  Every target-truncated signed edge maps to
its genuine type times an actual prime, and each target fiber is counted once.
-/
theorem scaleAdaptiveConstantBand_typedTarget_firstMoment_eq
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper N : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome) :
    (∑ target ∈ scaleAdaptiveTypedPrimeTargetsInIntegerCell
        (adaptiveMixedActualIndexType support outcome.1 index)
          targetLower targetUpper N,
      (scaleAdaptiveGTZIndexedTargetFiber
        support scale outcome
          (scaleAdaptiveTruncatedBandSignedDomain
            support outcome.1 index lower upper
              (targetLower : ℝ) (targetUpper : ℝ))
          index N target).card) =
      scaleAdaptiveConstantBandTruncatedFirstCount
        support scale outcome index lower upper
          targetLower targetUpper N := by
  let domain := scaleAdaptiveTruncatedBandSignedDomain
    support outcome.1 index lower upper
      (targetLower : ℝ) (targetUpper : ℝ)
  let realizations := adaptiveMixedSignedOriginalPrimeRealizations
    support scale outcome domain N
  let targets := scaleAdaptiveTypedPrimeTargetsInIntegerCell
    (adaptiveMixedActualIndexType support outcome.1 index)
      targetLower targetUpper N
  have mapped :
      (↑realizations : Set (ℕ × ℤ)).MapsTo
        (fun pair => scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index pair.1 pair.2)
        targets := by
    intro pair selected
    exact scaleAdaptiveTruncatedBandSignedRealization_mem_typed_targets
      primes active selected
  have exact_fibers := Finset.card_eq_sum_card_fiberwise mapped
  change (∑ target ∈ targets,
    (scaleAdaptiveGTZIndexedTargetFiber
      support scale outcome domain index N target).card) =
      realizations.card
  rw [exact_fibers]
  apply Finset.sum_congr rfl
  intro target _selected
  rfl

/-- On the ACTUAL unclipped target cell, a signed shared-target realization
fiber is exactly the ordered off-diagonal of the target-truncated original
fiber.  Distinct ORIGINAL edges imply globally distinct prime labels by
fixed-target injectivity; the signed integer target equality and both genuine
physical residue inequalities are checked in both directions. -/
theorem scaleAdaptiveConstantBand_sharedTargetFiber_eq_offDiag
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper N target : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (index_positive : 0 < index)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    scaleAdaptiveGTZSharedTargetFiber
      support scale outcome outcome index index
        (scaleAdaptiveConstantBandSharedTargetDomain
          index index lower upper (targetLower : ℝ) (targetUpper : ℝ))
        N target =
      scaleAdaptiveIndexedTargetDistinctLabelPairs
        support scale outcome
          (scaleAdaptiveTruncatedBandSignedDomain
            support outcome.1 index lower upper
              (targetLower : ℝ) (targetUpper : ℝ))
          index N target := by
  classical
  ext pair
  constructor
  · intro selected
    obtain ⟨shared, first_target⟩ := Finset.mem_filter.mp selected
    simp only [adaptiveMixedSignedSharedTargetPrimeRealizations,
      Finset.mem_filter] at shared
    obtain ⟨boxed, first_edge, second_edge, distinct,
      same_raw, cell⟩ := shared
    have labels := scaleAdaptiveConstantBandSharedTargetDomain_labels
      index_positive index_positive interior_lower interior_upper
      interior_lower interior_upper cell
    have first_affine :
        (((index : ℤ) * (pair.1.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.1.1 pair.1.2 : ℤ) : ℝ) /
            (N : ℝ) =
          (index : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
            ((outcome.1 : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
              (adaptiveMixedTypeModulus support : ℝ) *
                ((pair.1.2 : ℝ) / (N : ℝ))) := by
      unfold weightedPrimePatternSignedResidue
      push_cast
      ring_nf
    have second_affine :
        (((index : ℤ) * (pair.2.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.2.1 pair.2.2 : ℤ) : ℝ) /
            (N : ℝ) =
          (index : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
            ((outcome.1 : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
              (adaptiveMixedTypeModulus support : ℝ) *
                ((pair.2.2 : ℝ) / (N : ℝ))) := by
      unfold weightedPrimePatternSignedResidue
      push_cast
      ring_nf
    have same_real :
        (((index : ℤ) * (pair.1.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.1.1 pair.1.2 : ℤ) : ℝ) /
            (N : ℝ) =
        (((index : ℤ) * (pair.2.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.2.1 pair.2.2 : ℤ) : ℝ) /
            (N : ℝ) := by
      rw [same_raw]
    have first_original :
        pair.1 ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome
            (scaleAdaptiveTruncatedBandSignedDomain
              support outcome.1 index lower upper
                (targetLower : ℝ) (targetUpper : ℝ)) N := by
      simp only [adaptiveMixedSignedOriginalPrimeRealizations,
        Finset.mem_filter]
      refine ⟨(Finset.mem_product.mp boxed).1, first_edge, ?_⟩
      change
        1 < (pair.1.1 : ℝ) / (N : ℝ) ∧
          (pair.1.1 : ℝ) / (N : ℝ) < 2 ∧
          lower < (outcome.1 : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
            (adaptiveMixedTypeModulus support : ℝ) *
              ((pair.1.2 : ℝ) / (N : ℝ)) ∧
          (outcome.1 : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
            (adaptiveMixedTypeModulus support : ℝ) *
              ((pair.1.2 : ℝ) / (N : ℝ)) < upper ∧
          (targetLower : ℝ) <
            (index : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
              ((outcome.1 : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
                (adaptiveMixedTypeModulus support : ℝ) *
                  ((pair.1.2 : ℝ) / (N : ℝ))) ∧
          (index : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
              ((outcome.1 : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
                (adaptiveMixedTypeModulus support : ℝ) *
                  ((pair.1.2 : ℝ) / (N : ℝ))) < (targetUpper : ℝ)
      refine ⟨labels.1, labels.2.1, ?_, ?_, ?_, ?_⟩
      · linarith [cell.2.2.1, first_affine]
      · linarith [cell.2.2.2.1, first_affine]
      · linarith [cell.1, first_affine]
      · linarith [cell.2.1, first_affine]
    have second_original :
        pair.2 ∈ adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome
            (scaleAdaptiveTruncatedBandSignedDomain
              support outcome.1 index lower upper
                (targetLower : ℝ) (targetUpper : ℝ)) N := by
      simp only [adaptiveMixedSignedOriginalPrimeRealizations,
        Finset.mem_filter]
      refine ⟨(Finset.mem_product.mp boxed).2, second_edge, ?_⟩
      change
        1 < (pair.2.1 : ℝ) / (N : ℝ) ∧
          (pair.2.1 : ℝ) / (N : ℝ) < 2 ∧
          lower < (outcome.1 : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
            (adaptiveMixedTypeModulus support : ℝ) *
              ((pair.2.2 : ℝ) / (N : ℝ)) ∧
          (outcome.1 : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
            (adaptiveMixedTypeModulus support : ℝ) *
              ((pair.2.2 : ℝ) / (N : ℝ)) < upper ∧
          (targetLower : ℝ) <
            (index : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
              ((outcome.1 : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
                (adaptiveMixedTypeModulus support : ℝ) *
                  ((pair.2.2 : ℝ) / (N : ℝ))) ∧
          (index : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
              ((outcome.1 : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
                (adaptiveMixedTypeModulus support : ℝ) *
                  ((pair.2.2 : ℝ) / (N : ℝ))) < (targetUpper : ℝ)
      refine ⟨labels.2.2.1, labels.2.2.2, ?_, ?_, ?_, ?_⟩
      · linarith [cell.2.2.2.2.1, same_real, second_affine]
      · linarith [cell.2.2.2.2.2, same_real, second_affine]
      · linarith [cell.1, same_real, second_affine]
      · linarith [cell.2.1, same_real, second_affine]
    have same_target :
        scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index pair.1.1 pair.1.2 =
        scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index pair.2.1 pair.2.2 := by
      unfold scaleAdaptiveGTZIndexedPhysicalTarget
      rw [same_raw]
    apply Finset.mem_offDiag.mpr
    refine ⟨Finset.mem_filter.mpr ⟨first_original, first_target⟩,
      Finset.mem_filter.mpr ⟨second_original,
        same_target.symm.trans first_target⟩, ?_⟩
    intro equal
    exact distinct (congrArg Prod.fst equal)
  · intro selected
    obtain ⟨first_selected, second_selected, distinct_edges⟩ :=
      Finset.mem_offDiag.mp selected
    obtain ⟨first_original, first_target⟩ :=
      Finset.mem_filter.mp first_selected
    obtain ⟨second_original, second_target⟩ :=
      Finset.mem_filter.mp second_selected
    have first_decoded := first_original
    have second_decoded := second_original
    simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter] at first_decoded second_decoded
    have first_certificate := weightedPrimePatternEdges_prime_certificate
      support scale outcome
        (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
        pair.1.1 pair.1.2 first_decoded.2.1
    have second_certificate := weightedPrimePatternEdges_prime_certificate
      support scale outcome
        (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
        pair.2.1 pair.2.2 second_decoded.2.1
    have first_nonnegative :
        0 ≤ (index : ℤ) * (pair.1.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.1.1 pair.1.2 :=
      add_nonneg
        (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
        first_certificate.2.2.1
    have second_nonnegative :
        0 ≤ (index : ℤ) * (pair.2.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.2.1 pair.2.2 :=
      add_nonneg
        (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
        second_certificate.2.2.1
    have same_target := first_target.trans second_target.symm
    have same_raw := congrArg (fun value : ℕ => (value : ℤ)) same_target
    unfold scaleAdaptiveGTZIndexedPhysicalTarget at same_raw
    rw [Int.toNat_of_nonneg first_nonnegative,
      Int.toNat_of_nonneg second_nonnegative] at same_raw
    have distinct_labels : pair.1.1 ≠ pair.2.1 := by
      intro same_label
      exact distinct_edges
        (scaleAdaptiveGTZIndexedTargetFiber_label_injective
          support scale outcome
            (scaleAdaptiveTruncatedBandSignedDomain
              support outcome.1 index lower upper
                (targetLower : ℝ) (targetUpper : ℝ))
          index N target primes
          (Finset.mem_filter.mpr ⟨first_original, first_target⟩)
          (Finset.mem_filter.mpr ⟨second_original, second_target⟩)
          same_label)
    apply Finset.mem_filter.mpr
    refine ⟨?_, first_target⟩
    simp only [adaptiveMixedSignedSharedTargetPrimeRealizations,
      Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr
        ⟨first_decoded.1, second_decoded.1⟩,
      first_decoded.2.1, second_decoded.2.1, distinct_labels,
      same_raw, ?_⟩
    have first_affine :
        (((index : ℤ) * (pair.1.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.1.1 pair.1.2 : ℤ) : ℝ) /
            (N : ℝ) =
          (index : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
            ((outcome.1 : ℝ) * ((pair.1.1 : ℝ) / (N : ℝ)) +
              (adaptiveMixedTypeModulus support : ℝ) *
                ((pair.1.2 : ℝ) / (N : ℝ))) := by
      unfold weightedPrimePatternSignedResidue
      push_cast
      ring_nf
    have second_affine :
        (((index : ℤ) * (pair.2.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.2.1 pair.2.2 : ℤ) : ℝ) /
            (N : ℝ) =
          (index : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
            ((outcome.1 : ℝ) * ((pair.2.1 : ℝ) / (N : ℝ)) +
              (adaptiveMixedTypeModulus support : ℝ) *
                ((pair.2.2 : ℝ) / (N : ℝ))) := by
      unfold weightedPrimePatternSignedResidue
      push_cast
      ring_nf
    have same_real :
        (((index : ℤ) * (pair.1.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.1.1 pair.1.2 : ℤ) : ℝ) /
            (N : ℝ) =
        (((index : ℤ) * (pair.2.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.2.1 pair.2.2 : ℤ) : ℝ) /
            (N : ℝ) := by
      rw [same_raw]
    have first_cell := first_decoded.2.2
    have second_cell := second_decoded.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [first_cell.2.2.2.2.1, first_affine]
    · linarith [first_cell.2.2.2.2.2, first_affine]
    · linarith [first_cell.2.2.1, first_affine]
    · linarith [first_cell.2.2.2.1, first_affine]
    · linarith [second_cell.2.2.1, same_real, second_affine]
    · linarith [second_cell.2.2.2.1, same_real, second_affine]

/-- EXACT distinct-prime-label second moment over the ACTUAL typed prime
target set.  The shared-target GTZ realization count is neither padded with
integer targets nor replaced by real-domain witnesses. -/
theorem scaleAdaptiveConstantBand_typedTarget_distinctMoment_eq
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper N : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (index_positive : 0 < index)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    (∑ target ∈ scaleAdaptiveTypedPrimeTargetsInIntegerCell
        (adaptiveMixedActualIndexType support outcome.1 index)
          targetLower targetUpper N,
      (scaleAdaptiveIndexedTargetDistinctLabelPairs
        support scale outcome
          (scaleAdaptiveTruncatedBandSignedDomain
            support outcome.1 index lower upper
              (targetLower : ℝ) (targetUpper : ℝ))
          index N target).card) =
      scaleAdaptiveConstantBandSharedOffDiagonalCount
        support scale outcome index lower upper
          targetLower targetUpper N := by
  let originalDomain := scaleAdaptiveTruncatedBandSignedDomain
    support outcome.1 index lower upper
      (targetLower : ℝ) (targetUpper : ℝ)
  let sharedDomain := scaleAdaptiveConstantBandSharedTargetDomain
    index index lower upper (targetLower : ℝ) (targetUpper : ℝ)
  let realizations := adaptiveMixedSignedSharedTargetPrimeRealizations
    support scale outcome outcome index index sharedDomain N
  let targets := scaleAdaptiveTypedPrimeTargetsInIntegerCell
    (adaptiveMixedActualIndexType support outcome.1 index)
      targetLower targetUpper N
  have mapped :
      (↑realizations : Set ((ℕ × ℤ) × (ℕ × ℤ))).MapsTo
        (fun pair => scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index pair.1.1 pair.1.2)
        targets := by
    intro pair selected
    have fiber :
        pair ∈ scaleAdaptiveGTZSharedTargetFiber
          support scale outcome outcome index index sharedDomain N
            (scaleAdaptiveGTZIndexedPhysicalTarget
              support outcome.1 index pair.1.1 pair.1.2) :=
      Finset.mem_filter.mpr ⟨selected, rfl⟩
    rw [scaleAdaptiveConstantBand_sharedTargetFiber_eq_offDiag
      support scale outcome index targetLower targetUpper N
        (scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index pair.1.1 pair.1.2)
        lower upper primes index_positive
          interior_lower interior_upper] at fiber
    have first_original := (Finset.mem_filter.mp
      (Finset.mem_offDiag.mp fiber).1).1
    exact scaleAdaptiveTruncatedBandSignedRealization_mem_typed_targets
      primes active first_original
  have exact_fibers := Finset.card_eq_sum_card_fiberwise mapped
  change
    (∑ target ∈ targets,
      (scaleAdaptiveIndexedTargetDistinctLabelPairs
        support scale outcome originalDomain index N target).card) =
      realizations.card
  rw [exact_fibers]
  apply Finset.sum_congr rfl
  intro target _selected
  rw [← scaleAdaptiveConstantBand_sharedTargetFiber_eq_offDiag
    support scale outcome index targetLower targetUpper N target
      lower upper primes index_positive interior_lower interior_upper]
  rfl

/-- EXACT full second prime-incidence moment on the genuine typed target set.
The actual shared-target count supplies all distinct-label pairs and the
actual truncated original count supplies precisely the same-label diagonal.
-/
theorem scaleAdaptiveConstantBand_typedTarget_secondMoment_eq
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper N : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (index_positive : 0 < index)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    (∑ target ∈ scaleAdaptiveTypedPrimeTargetsInIntegerCell
        (adaptiveMixedActualIndexType support outcome.1 index)
          targetLower targetUpper N,
      ((scaleAdaptiveGTZIndexedTargetFiber
        support scale outcome
          (scaleAdaptiveTruncatedBandSignedDomain
            support outcome.1 index lower upper
              (targetLower : ℝ) (targetUpper : ℝ))
          index N target).card : ℝ) ^ 2) =
      (scaleAdaptiveConstantBandSharedOffDiagonalCount
        support scale outcome index lower upper
          targetLower targetUpper N : ℝ) +
      (scaleAdaptiveConstantBandTruncatedFirstCount
        support scale outcome index lower upper
          targetLower targetUpper N : ℝ) := by
  rw [scaleAdaptiveGTZIndexedTarget_secondMoment_eq_distinct_add_first]
  have distinct := congrArg (fun count : ℕ => (count : ℝ))
    (scaleAdaptiveConstantBand_typedTarget_distinctMoment_eq
      support scale outcome index targetLower targetUpper N lower upper
      primes active index_positive interior_lower interior_upper)
  have first := congrArg (fun count : ℕ => (count : ℝ))
    (scaleAdaptiveConstantBand_typedTarget_firstMoment_eq
      support scale outcome index targetLower targetUpper N lower upper
      primes active)
  push_cast at distinct first
  rw [distinct, first]

/-- Actual target-truncated first count and globally distinct-label shared
target count share ONE positive collision-correct singular constant.  Both
archimedean coefficients retain the true target length, band width, physical
index, type, and squared-core Jacobian.  This uses ONLY the original and
shared-target fields of the explicit signed Green--Tao proposition. -/
theorem scaleAdaptiveConstantBand_first_and_shared_moments_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (index_positive : 0 < index)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (target_nonempty : targetLower < targetUpper)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
        atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          (scaleAdaptiveConstantBandTruncatedFirstCount
            support scale outcome index lower upper
              targetLower targetUpper N : ℝ) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 2)
        atTop (nhds
          (((targetUpper : ℝ) - (targetLower : ℝ)) *
            (upper - lower) /
              ((index : ℝ) * (adaptiveMixedTypeModulus support : ℝ)) *
            singular)) ∧
      Tendsto
        (fun N : ℕ =>
          (scaleAdaptiveConstantBandSharedOffDiagonalCount
            support scale outcome index lower upper
              targetLower targetUpper N : ℝ) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card +
               (adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 3)
        atTop (nhds
          (((targetUpper : ℝ) - (targetLower : ℝ)) *
            ((upper - lower) / (index : ℝ)) *
            ((upper - lower) / (index : ℝ)) *
            (adaptiveMixedActualIndexType support outcome.1 index : ℝ) /
              (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
            singular * singular)) := by
  have target_real_nonempty : (targetLower : ℝ) < (targetUpper : ℝ) := by
    exact_mod_cast target_nonempty
  obtain ⟨singular, positive, converges, first_sum⟩ :=
    scaleAdaptiveTruncatedBandIndexedTarget_firstMoment_of_GTZ
      green_tao support scale outcome index
        lower upper (targetLower : ℝ) (targetUpper : ℝ)
      primes index_positive lower_nonnegative band_nonempty
      upper_bounded target_real_nonempty interior_lower interior_upper
  obtain ⟨first_singular, second_singular,
      first_positive, second_positive,
      first_converges, second_converges, _paired_converges,
      shared_sum⟩ :=
    scaleAdaptiveConstantBandSharedTarget_secondMoment_of_GTZ
      green_tao lower upper (targetLower : ℝ) (targetUpper : ℝ)
      primes active active rfl index_positive index_positive
      lower_nonnegative band_nonempty upper_bounded target_real_nonempty
      interior_lower interior_upper interior_lower interior_upper
      (1 : ℤ) (0 : ℤ) (by ring_nf)
  have first_same := tendsto_nhds_unique converges first_converges
  have second_same := tendsto_nhds_unique converges second_converges
  subst first_singular
  subst second_singular
  refine ⟨singular, positive, converges, ?_, ?_⟩
  · convert first_sum using 1
    ext N
    have exact_count := congrArg (fun count : ℕ => (count : ℝ))
      (scaleAdaptiveGTZIndexedTarget_firstMoment_eq_realizations_card
        support scale outcome
          (scaleAdaptiveTruncatedBandSignedDomain support outcome.1 index
            lower upper (targetLower : ℝ) (targetUpper : ℝ)) index N)
    push_cast at exact_count
    unfold scaleAdaptiveConstantBandTruncatedFirstCount
    rw [exact_count]
  · convert shared_sum using 1
    ext N
    have exact_count := congrArg (fun count : ℕ => (count : ℝ))
      (scaleAdaptiveGTZSharedTarget_secondMoment_eq_realizations_card
        support scale outcome outcome index index
          (scaleAdaptiveConstantBandSharedTargetDomain index index
            lower upper (targetLower : ℝ) (targetUpper : ℝ)) N)
    push_cast at exact_count
    unfold scaleAdaptiveConstantBandSharedOffDiagonalCount
    rw [exact_count]

/-- Dividing both actual raw prime-pattern counts by their TRUE constant-band
degree yields the exact source-faithful target first and distinct-label
second coefficients `H/i` and `H*s/i²`.  No local singular factor, square-core
Jacobian, or band-width factor is discarded. -/
theorem scaleAdaptiveConstantBand_normalized_first_and_shared_tendsto_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (index_positive : 0 < index)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (target_nonempty : targetLower < targetUpper)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
        atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          (scaleAdaptiveConstantBandTruncatedFirstCount
            support scale outcome index lower upper
              targetLower targetUpper N : ℝ) /
            scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds
          (((targetUpper : ℝ) - (targetLower : ℝ)) / (index : ℝ))) ∧
      Tendsto
        (fun N : ℕ =>
          (scaleAdaptiveConstantBandSharedOffDiagonalCount
            support scale outcome index lower upper
              targetLower targetUpper N : ℝ) /
            scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N ^ 2 *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds
          (((targetUpper : ℝ) - (targetLower : ℝ)) *
            (adaptiveMixedActualIndexType support outcome.1 index : ℝ) /
            (index : ℝ) ^ 2)) := by
  obtain ⟨singular, positive, converges, first, shared⟩ :=
    scaleAdaptiveConstantBand_first_and_shared_moments_of_GTZ
      green_tao support scale outcome index targetLower targetUpper
      lower upper primes active index_positive lower_nonnegative
      band_nonempty upper_bounded target_nonempty
      interior_lower interior_upper
  have index_real : (0 : ℝ) < index := by
    exact_mod_cast index_positive
  have modulus_real : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have width_positive : 0 < upper - lower := sub_pos.mpr band_nonempty
  let coefficient :=
    (upper - lower) / (adaptiveMixedTypeModulus support : ℝ) * singular
  have coefficient_nonzero : coefficient ≠ 0 := by
    dsimp [coefficient]
    exact mul_ne_zero
      (div_ne_zero width_positive.ne' modulus_real.ne')
      positive.ne'
  let rank := (adaptiveMixedOutcomeActiveIndices
    support scale outcome).card
  refine ⟨singular, positive, converges, ?_, ?_⟩
  · have divided := first.div_const coefficient
    have target :
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveConstantBandTruncatedFirstCount
              support scale outcome index lower upper
                targetLower targetUpper N : ℝ) *
              Real.log (N : ℝ) ^ (rank + 1) /
                (N : ℝ) ^ 2) / coefficient)
          atTop (nhds
            (((targetUpper : ℝ) - (targetLower : ℝ)) / (index : ℝ))) := by
      convert divided using 1
      dsimp [coefficient]
      field_simp [index_real.ne', modulus_real.ne',
        width_positive.ne', positive.ne']
    apply target.congr'
    filter_upwards [eventually_ge_atTop 2] with N large
    have N_nonzero : (N : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : N ≠ 0)
    have log_nonzero : Real.log (N : ℝ) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · exact_mod_cast (by omega : 0 < N)
      · exact_mod_cast (by omega : N ≠ 1)
    change
      ((scaleAdaptiveConstantBandTruncatedFirstCount
        support scale outcome index lower upper
          targetLower targetUpper N : ℝ) *
        Real.log (N : ℝ) ^ (rank + 1) /
          (N : ℝ) ^ 2) / coefficient =
        (scaleAdaptiveConstantBandTruncatedFirstCount
          support scale outcome index lower upper
            targetLower targetUpper N : ℝ) /
          (coefficient * (N : ℝ) / Real.log (N : ℝ) ^ rank) *
          Real.log (N : ℝ) / (N : ℝ)
    field_simp [N_nonzero, log_nonzero, coefficient_nonzero]
    ring_nf
  · have divided := shared.div_const (coefficient ^ 2)
    have target :
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveConstantBandSharedOffDiagonalCount
              support scale outcome index lower upper
                targetLower targetUpper N : ℝ) *
              Real.log (N : ℝ) ^ (rank + rank + 1) /
                (N : ℝ) ^ 3) / coefficient ^ 2)
          atTop (nhds
            (((targetUpper : ℝ) - (targetLower : ℝ)) *
              (adaptiveMixedActualIndexType support outcome.1 index : ℝ) /
              (index : ℝ) ^ 2)) := by
      convert divided using 1
      dsimp [coefficient]
      field_simp [index_real.ne', modulus_real.ne',
        width_positive.ne', positive.ne']
    apply target.congr'
    filter_upwards [eventually_ge_atTop 2] with N large
    have N_nonzero : (N : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : N ≠ 0)
    have log_nonzero : Real.log (N : ℝ) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · exact_mod_cast (by omega : 0 < N)
      · exact_mod_cast (by omega : N ≠ 1)
    change
      ((scaleAdaptiveConstantBandSharedOffDiagonalCount
        support scale outcome index lower upper
          targetLower targetUpper N : ℝ) *
        Real.log (N : ℝ) ^ (rank + rank + 1) /
          (N : ℝ) ^ 3) / coefficient ^ 2 =
        (scaleAdaptiveConstantBandSharedOffDiagonalCount
          support scale outcome index lower upper
            targetLower targetUpper N : ℝ) /
          (coefficient * (N : ℝ) /
            Real.log (N : ℝ) ^ rank) ^ 2 *
          Real.log (N : ℝ) / (N : ℝ)
    field_simp [N_nonzero, log_nonzero, coefficient_nonzero]
    ring_nf

/-- The true mean on type-`s` targets for one physical index `i` is exactly
`s/i`.  Combining the actual distinct-prime shared-target moment, the actual
target-truncated first moment, and the independently proved typed-target PNT
makes the entire normalized OFF-DIAGONAL centered energy tend to zero.

All three moments are actual prime objects, and the only deep input is the
explicit signed Green--Tao proposition. -/
theorem scaleAdaptiveConstantBand_distinctLabelCenteredEnergy_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (index_positive : 0 < index)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (target_nonempty : targetLower < targetUpper)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
        atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveConstantBandSharedOffDiagonalCount
              support scale outcome index lower upper
                targetLower targetUpper N : ℝ) /
              scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper singular N ^ 2 -
            2 *
              ((adaptiveMixedActualIndexType
                support outcome.1 index : ℝ) / (index : ℝ)) *
              ((scaleAdaptiveConstantBandTruncatedFirstCount
                support scale outcome index lower upper
                  targetLower targetUpper N : ℝ) /
                scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper singular N) +
            ((scaleAdaptiveTypedPrimeTargetsInIntegerCell
              (adaptiveMixedActualIndexType support outcome.1 index)
              targetLower targetUpper N).card : ℝ) *
              ((adaptiveMixedActualIndexType
                support outcome.1 index : ℝ) / (index : ℝ)) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, converges, first, shared⟩ :=
    scaleAdaptiveConstantBand_normalized_first_and_shared_tendsto_of_GTZ
      green_tao support scale outcome index targetLower targetUpper
      lower upper primes active index_positive lower_nonnegative
      band_nonempty upper_bounded target_nonempty
      interior_lower interior_upper
  have type_positive :=
    adaptiveMixedActualIndexType_pos_of_active primes active
  have target_lower_positive : 0 < targetLower := by
    have index_real : (0 : ℝ) < index := by
      exact_mod_cast index_positive
    have upper_positive : 0 < upper :=
      lt_of_le_of_lt lower_nonnegative band_nonempty
    have lower_real : (0 : ℝ) < targetLower := by
      linarith
    exact_mod_cast lower_real
  have typed := scaleAdaptiveTypedPrimeTargetsInIntegerCell_normalized_tendsto
    (adaptiveMixedActualIndexType support outcome.1 index)
      targetLower targetUpper type_positive target_lower_positive
        target_nonempty.le
  let mean : ℝ :=
    (adaptiveMixedActualIndexType support outcome.1 index : ℝ) /
      (index : ℝ)
  have combined :=
    (shared.sub (first.const_mul (2 * mean))).add
      (typed.const_mul (mean ^ 2))
  have index_nonzero : (index : ℝ) ≠ 0 := by
    exact_mod_cast index_positive.ne'
  have type_nonzero :
      (adaptiveMixedActualIndexType support outcome.1 index : ℝ) ≠ 0 := by
    exact_mod_cast type_positive.ne'
  have target :
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveConstantBandSharedOffDiagonalCount
              support scale outcome index lower upper
                targetLower targetUpper N : ℝ) /
              scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper singular N ^ 2 *
                Real.log (N : ℝ) / (N : ℝ)) -
            (2 * mean) *
              ((scaleAdaptiveConstantBandTruncatedFirstCount
                support scale outcome index lower upper
                  targetLower targetUpper N : ℝ) /
                scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper singular N *
                Real.log (N : ℝ) / (N : ℝ)) +
            (mean ^ 2) *
              (((scaleAdaptiveTypedPrimeTargetsInIntegerCell
                (adaptiveMixedActualIndexType support outcome.1 index)
                targetLower targetUpper N).card : ℝ) *
                Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds (0 : ℝ)) := by
    convert combined using 1
    dsimp [mean]
    field_simp [index_nonzero, type_nonzero]
    ring_nf
  refine ⟨singular, positive, converges, ?_⟩
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp [mean]
    ring_nf

/-- Every fixed power of the genuine logarithm is negligible compared with
the actual prime-label scale. -/
theorem scaleAdaptiveConstantBand_log_power_div_scale_tendsto_zero
    (rank : ℕ) :
    Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ rank / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have real_limit := Real.tendsto_pow_log_div_mul_add_atTop
    (1 : ℝ) 0 rank one_ne_zero
  simpa [Function.comp_def] using real_limit.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The reciprocal of the ACTUAL constant-band expected integer degree tends
to zero at every fixed genuine prime-pattern rank. -/
theorem scaleAdaptiveSignedConstantResidueBandExpectedDegree_inv_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (band_nonempty : lower < upper)
    (singular_positive : 0 < singular) :
    Tendsto
      (fun N : ℕ =>
        (scaleAdaptiveSignedConstantResidueBandExpectedDegree
          support scale outcome lower upper singular N)⁻¹)
      atTop (nhds (0 : ℝ)) := by
  have modulus_real : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have width_nonzero : upper - lower ≠ 0 :=
    (sub_pos.mpr band_nonempty).ne'
  have coefficient_nonzero :
      (upper - lower) /
        (adaptiveMixedTypeModulus support : ℝ) * singular ≠ 0 :=
    mul_ne_zero (div_ne_zero width_nonzero modulus_real.ne')
      singular_positive.ne'
  have rank_limit :=
    scaleAdaptiveConstantBand_log_power_div_scale_tendsto_zero
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card
  have divided := rank_limit.div_const
    ((upper - lower) /
      (adaptiveMixedTypeModulus support : ℝ) * singular)
  have target :
      Tendsto
        (fun N : ℕ =>
          (Real.log (N : ℝ) ^
            (adaptiveMixedOutcomeActiveIndices
              support scale outcome).card / (N : ℝ)) /
            ((upper - lower) /
              (adaptiveMixedTypeModulus support : ℝ) * singular))
        atTop (nhds (0 : ℝ)) := by
    simpa using divided
  apply target.congr'
  filter_upwards [eventually_ge_atTop 2] with N large
  have N_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have log_nonzero : Real.log (N : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (by omega : 0 < N)
    · exact_mod_cast (by omega : N ≠ 1)
  unfold scaleAdaptiveSignedConstantResidueBandExpectedDegree
  field_simp [N_nonzero, log_nonzero, coefficient_nonzero]

/-- The genuine same-label target diagonal has asymptotically ZERO normalized
energy after division by the square of the actual full-band expected degree.
Unlike a heuristic deletion of the diagonal, this follows from its exact
one-edge multiplicity, the true truncated first moment, and divergence of
the fixed-rank expected degree. -/
theorem scaleAdaptiveConstantBand_diagonalEnergy_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper : ℕ)
    (lower upper singular : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (band_nonempty : lower < upper)
    (singular_positive : 0 < singular)
    (first :
      Tendsto
        (fun N : ℕ =>
          (scaleAdaptiveConstantBandTruncatedFirstCount
            support scale outcome index lower upper
              targetLower targetUpper N : ℝ) /
            scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds
          (((targetUpper : ℝ) - (targetLower : ℝ)) / (index : ℝ)))) :
    Tendsto
      (fun N : ℕ =>
        (scaleAdaptiveConstantBandTruncatedFirstCount
          support scale outcome index lower upper
            targetLower targetUpper N : ℝ) /
          scaleAdaptiveSignedConstantResidueBandExpectedDegree
            support scale outcome lower upper singular N ^ 2 *
          Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have inverse :=
    scaleAdaptiveSignedConstantResidueBandExpectedDegree_inv_tendsto_zero
      support scale outcome lower upper singular primes
      band_nonempty singular_positive
  have product := first.mul inverse
  have limit :
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveConstantBandTruncatedFirstCount
            support scale outcome index lower upper
              targetLower targetUpper N : ℝ) /
            scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N *
            Real.log (N : ℝ) / (N : ℝ)) *
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N)⁻¹)
        atTop (nhds (0 : ℝ)) := by
    simpa using product
  apply limit.congr'
  exact Filter.Eventually.of_forall fun N => by
    simp only [div_eq_mul_inv]
    ring_nf

/-- The entire compensated targetwise centered energy, including the EXACT
same-label diagonal, tends to zero.  The one positive singular is certified by
the actual collision-aware Euler partial products; both moments and the
independently proved typed-target prime density use this SAME singular.

The expression uses the actual distinct-prime shared-target count plus the
actual one-edge diagonal.  Its identification with a sum of squared
target-fiber loads is a separate finite incidence identity. -/
theorem scaleAdaptiveConstantBand_fullCenteredEnergy_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (index_positive : 0 < index)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (target_nonempty : targetLower < targetUpper)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
        atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          (((scaleAdaptiveConstantBandSharedOffDiagonalCount
                support scale outcome index lower upper
                  targetLower targetUpper N : ℝ) +
              (scaleAdaptiveConstantBandTruncatedFirstCount
                support scale outcome index lower upper
                  targetLower targetUpper N : ℝ)) /
              scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper singular N ^ 2 -
            2 *
              ((adaptiveMixedActualIndexType
                support outcome.1 index : ℝ) / (index : ℝ)) *
              ((scaleAdaptiveConstantBandTruncatedFirstCount
                support scale outcome index lower upper
                  targetLower targetUpper N : ℝ) /
                scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper singular N) +
            ((scaleAdaptiveTypedPrimeTargetsInIntegerCell
              (adaptiveMixedActualIndexType support outcome.1 index)
              targetLower targetUpper N).card : ℝ) *
              ((adaptiveMixedActualIndexType
                support outcome.1 index : ℝ) / (index : ℝ)) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, converges, centered⟩ :=
    scaleAdaptiveConstantBand_distinctLabelCenteredEnergy_tendsto_zero_of_GTZ
      green_tao support scale outcome index targetLower targetUpper
      lower upper primes active index_positive lower_nonnegative
      band_nonempty upper_bounded target_nonempty
      interior_lower interior_upper
  obtain ⟨first_singular, first_positive, first_converges, first, _shared⟩ :=
    scaleAdaptiveConstantBand_normalized_first_and_shared_tendsto_of_GTZ
      green_tao support scale outcome index targetLower targetUpper
      lower upper primes active index_positive lower_nonnegative
      band_nonempty upper_bounded target_nonempty
      interior_lower interior_upper
  have same := tendsto_nhds_unique converges first_converges
  subst first_singular
  have diagonal := scaleAdaptiveConstantBand_diagonalEnergy_tendsto_zero
    support scale outcome index targetLower targetUpper
    lower upper singular primes band_nonempty first_positive first
  have combined := centered.add diagonal
  refine ⟨singular, positive, converges, ?_⟩
  have target :
      Tendsto
        (fun N : ℕ =>
          (((scaleAdaptiveConstantBandSharedOffDiagonalCount
              support scale outcome index lower upper
                targetLower targetUpper N : ℝ) /
              scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper singular N ^ 2 -
            2 *
              ((adaptiveMixedActualIndexType
                support outcome.1 index : ℝ) / (index : ℝ)) *
              ((scaleAdaptiveConstantBandTruncatedFirstCount
                support scale outcome index lower upper
                  targetLower targetUpper N : ℝ) /
                scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper singular N) +
            ((scaleAdaptiveTypedPrimeTargetsInIntegerCell
              (adaptiveMixedActualIndexType support outcome.1 index)
              targetLower targetUpper N).card : ℝ) *
              ((adaptiveMixedActualIndexType
                support outcome.1 index : ℝ) / (index : ℝ)) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ)) +
          ((scaleAdaptiveConstantBandTruncatedFirstCount
            support scale outcome index lower upper
              targetLower targetUpper N : ℝ) /
            scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N ^ 2 *
            Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds (0 : ℝ)) := by
    simpa using combined
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    ring_nf

/-- The genuine target-fiber centered variance has the EXACT actual
distinct-label/diagonal/count expansion, on the true typed prime target set.
This identity is finite and unconditional: no moment or covariance premise
is inserted. -/
theorem scaleAdaptiveConstantBand_typedTarget_centeredVariance_eq
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper N : ℕ) (lower upper singular : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (index_positive : 0 < index)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    (∑ target ∈ scaleAdaptiveTypedPrimeTargetsInIntegerCell
        (adaptiveMixedActualIndexType support outcome.1 index)
          targetLower targetUpper N,
      (((scaleAdaptiveGTZIndexedTargetFiber
          support scale outcome
            (scaleAdaptiveTruncatedBandSignedDomain
              support outcome.1 index lower upper
                (targetLower : ℝ) (targetUpper : ℝ))
          index N target).card : ℝ) /
          scaleAdaptiveSignedConstantResidueBandExpectedDegree
            support scale outcome lower upper singular N -
          (adaptiveMixedActualIndexType
            support outcome.1 index : ℝ) / (index : ℝ)) ^ 2) =
      ((scaleAdaptiveConstantBandSharedOffDiagonalCount
          support scale outcome index lower upper
            targetLower targetUpper N : ℝ) +
        (scaleAdaptiveConstantBandTruncatedFirstCount
          support scale outcome index lower upper
            targetLower targetUpper N : ℝ)) /
          scaleAdaptiveSignedConstantResidueBandExpectedDegree
            support scale outcome lower upper singular N ^ 2 -
        2 * ((adaptiveMixedActualIndexType
          support outcome.1 index : ℝ) / (index : ℝ)) *
          ((scaleAdaptiveConstantBandTruncatedFirstCount
            support scale outcome index lower upper
              targetLower targetUpper N : ℝ) /
            scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N) +
        ((scaleAdaptiveTypedPrimeTargetsInIntegerCell
          (adaptiveMixedActualIndexType support outcome.1 index)
          targetLower targetUpper N).card : ℝ) *
          ((adaptiveMixedActualIndexType
            support outcome.1 index : ℝ) / (index : ℝ)) ^ 2 := by
  classical
  let targets := scaleAdaptiveTypedPrimeTargetsInIntegerCell
    (adaptiveMixedActualIndexType support outcome.1 index)
      targetLower targetUpper N
  let domain := scaleAdaptiveTruncatedBandSignedDomain
    support outcome.1 index lower upper
      (targetLower : ℝ) (targetUpper : ℝ)
  let degree := scaleAdaptiveSignedConstantResidueBandExpectedDegree
    support scale outcome lower upper singular N
  let mean : ℝ :=
    (adaptiveMixedActualIndexType support outcome.1 index : ℝ) /
      (index : ℝ)
  have first := congrArg (fun count : ℕ => (count : ℝ))
    (scaleAdaptiveConstantBand_typedTarget_firstMoment_eq
      support scale outcome index targetLower targetUpper N
        lower upper primes active)
  push_cast at first
  have second := scaleAdaptiveConstantBand_typedTarget_secondMoment_eq
    support scale outcome index targetLower targetUpper N
      lower upper primes active index_positive
        interior_lower interior_upper
  change
    (∑ target ∈ targets,
      (((scaleAdaptiveGTZIndexedTargetFiber
        support scale outcome domain index N target).card : ℝ) /
        degree - mean) ^ 2) = _
  calc
    _ = ∑ target ∈ targets,
        (((scaleAdaptiveGTZIndexedTargetFiber
          support scale outcome domain index N target).card : ℝ) ^ 2 /
          degree ^ 2 - 2 * mean *
            (((scaleAdaptiveGTZIndexedTargetFiber
              support scale outcome domain index N target).card : ℝ) /
                degree) + mean ^ 2) := by
      apply Finset.sum_congr rfl
      intro target _selected
      ring_nf
    _ =
        (∑ target ∈ targets,
          ((scaleAdaptiveGTZIndexedTargetFiber
            support scale outcome domain index N target).card : ℝ) ^ 2) /
            degree ^ 2 -
          2 * mean *
            ((∑ target ∈ targets,
              ((scaleAdaptiveGTZIndexedTargetFiber
                support scale outcome domain index N target).card : ℝ)) /
              degree) + (targets.card : ℝ) * mean ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_div, Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
    _ = _ := by
      rw [second, first]

/-- ACTUAL raw prime-target-fiber centered variance tends to zero, with
its exact true target mean `s/i`, its correct prime-target normalization,
its genuine same-label diagonal, and ONE certified collision-aware Euler
singular shared by all physical moments.

Every summand is the square of the true integer signed prime-pattern target
fiber divided by its actual full-band expected degree.  The targets are
actual `s*q` for genuine primes `q`; the only deep input is the explicit
three-field signed Green--Tao proposition.  The closed upper endpoint can
contribute at most one empty-fiber target and is included honestly. -/
theorem scaleAdaptiveConstantBand_typedTarget_centeredVariance_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome)
    (index_positive : 0 < index)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (target_nonempty : targetLower < targetUpper)
    (interior_lower : (index : ℝ) + upper ≤ (targetLower : ℝ))
    (interior_upper : (targetUpper : ℝ) ≤ 2 * (index : ℝ) + lower) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
        atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          (∑ target ∈ scaleAdaptiveTypedPrimeTargetsInIntegerCell
              (adaptiveMixedActualIndexType support outcome.1 index)
                targetLower targetUpper N,
            (((scaleAdaptiveGTZIndexedTargetFiber
                support scale outcome
                  (scaleAdaptiveTruncatedBandSignedDomain
                    support outcome.1 index lower upper
                      (targetLower : ℝ) (targetUpper : ℝ))
                index N target).card : ℝ) /
                scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper singular N -
                (adaptiveMixedActualIndexType
                  support outcome.1 index : ℝ) / (index : ℝ)) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, converges, centered⟩ :=
    scaleAdaptiveConstantBand_fullCenteredEnergy_tendsto_zero_of_GTZ
      green_tao support scale outcome index targetLower targetUpper
        lower upper primes active index_positive lower_nonnegative
        band_nonempty upper_bounded target_nonempty
          interior_lower interior_upper
  refine ⟨singular, positive, converges, ?_⟩
  apply centered.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp only
    rw [scaleAdaptiveConstantBand_typedTarget_centeredVariance_eq
      support scale outcome index targetLower targetUpper N
        lower upper singular primes active index_positive
          interior_lower interior_upper]


end Erdos1139
