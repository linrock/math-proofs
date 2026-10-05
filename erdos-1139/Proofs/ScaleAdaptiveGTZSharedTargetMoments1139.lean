module

public import AdaptiveSharedTargetActualFactorization1139
public import ScaleAdaptiveGlobalMomentConstruction1139

@[expose] public section


/-!
# Genuine signed indexed-target moments directly from Green--Tao

For a fixed actual mixed outcome and retained physical index `d`, every signed
prime edge has the genuine physical target

    h = dP + (bP+WC),        dP ≤ h < (d+1)P.

The first indexed target moment is EXACTLY the cardinality of the actual signed
original prime-pattern realization set.  For two same-type outcomes/indices,
the genuinely distinct-label shared-target second moment is EXACTLY the
cardinality of the actual signed shared-target realization set.

Applying ONLY the explicit three-field fixed-system
`HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics` gives the corresponding
first and shared-target second asymptotics, with their true convex volumes,
collision-aware singular factors, and physical `s/W²` Jacobian.  No
degree-regularity, variance, covariance, first-moment, or second-moment bound
is postulated.

The remaining step to the original Erdős problem is to pass from these fixed
raw incidence moments, together with independently proved degree regularity,
to the scale-adaptive weighted mixed targetwise variance.  That global passage
is not silently assumed here.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos1139

/-- The TRUE physical target of one genuine signed-center mixed edge and its
distinguished actual physical index. -/
def scaleAdaptiveGTZIndexedPhysicalTarget
    (support : Finset ℕ) (base index label : ℕ) (center : ℤ) : ℕ :=
  ((index : ℤ) * (label : ℤ) +
    weightedPrimePatternSignedResidue
      support base label center).toNat

/-- A finite universal target window for a genuine dyadic prime label and a
fixed retained physical index. -/
def scaleAdaptiveGTZIndexedTargetWindow (index N : ℕ) : Finset ℕ :=
  Finset.range (2 * (index + 1) * N + 1)

/-- Every signed ORIGINAL realization has its genuine distinguished physical
target in the explicit finite moving dyadic target window. -/
theorem scaleAdaptiveGTZIndexedPhysicalTarget_mem_window
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (pair : ℕ × ℤ)
    (selected : pair ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N) :
    scaleAdaptiveGTZIndexedPhysicalTarget
      support outcome.1 index pair.1 pair.2 ∈
        scaleAdaptiveGTZIndexedTargetWindow index N := by
  classical
  simp only [adaptiveMixedSignedOriginalPrimeRealizations,
    Finset.mem_filter] at selected
  obtain ⟨boxed, edge, _physical⟩ := selected
  have label_bound :=
    (Finset.mem_Ioc.mp (Finset.mem_product.mp boxed).1).2
  have certificate := weightedPrimePatternEdges_prime_certificate
    support scale outcome
    (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
    pair.1 pair.2 edge
  have residue_nonnegative := certificate.2.2.1
  have residue_upper := certificate.2.2.2.1
  have label_bound_integer :
      (pair.1 : ℤ) ≤ 2 * (N : ℤ) := by
    exact_mod_cast label_bound
  have index_nonnegative : 0 ≤ (index : ℤ) := Int.natCast_nonneg _
  have label_nonnegative : 0 ≤ (pair.1 : ℤ) := Int.natCast_nonneg _
  have raw_nonnegative :
      0 ≤ (index : ℤ) * (pair.1 : ℤ) +
        weightedPrimePatternSignedResidue
          support outcome.1 pair.1 pair.2 := by
    exact add_nonneg (mul_nonneg index_nonnegative label_nonnegative)
      residue_nonnegative
  have scaled_bound :
      ((index : ℤ) + 1) * (pair.1 : ℤ) ≤
        ((index : ℤ) + 1) * (2 * (N : ℤ)) :=
    mul_le_mul_of_nonneg_left label_bound_integer (by omega)
  have raw_upper :
      (index : ℤ) * (pair.1 : ℤ) +
        weightedPrimePatternSignedResidue
          support outcome.1 pair.1 pair.2 <
          ((2 * (index + 1) * N + 1 : ℕ) : ℤ) := by
    push_cast
    nlinarith
  have cast_target :
      ((scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index pair.1 pair.2 : ℕ) : ℤ) =
        (index : ℤ) * (pair.1 : ℤ) +
          weightedPrimePatternSignedResidue
            support outcome.1 pair.1 pair.2 := by
    exact Int.toNat_of_nonneg raw_nonnegative
  apply Finset.mem_range.mpr
  exact_mod_cast cast_target.symm ▸ raw_upper

/-- The ACTUAL signed first-moment target fiber for one fixed retained index;
all prime labels, all true signed centers, and the convex domain are retained. -/
noncomputable def scaleAdaptiveGTZIndexedTargetFiber
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ) : Finset (ℕ × ℤ) :=
  (adaptiveMixedSignedOriginalPrimeRealizations
    support scale outcome domain N).filter fun pair =>
      scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index pair.1 pair.2 = target

/-- EXACT genuine targetwise FIRST incidence moment.  Summing the true signed
indexed target fibers over their actual dyadic target interval gives the
original signed prime-pattern count, with NO moment hypothesis. -/
theorem scaleAdaptiveGTZIndexedTarget_firstMoment_eq_realizations_card
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
      (scaleAdaptiveGTZIndexedTargetFiber
        support scale outcome domain index N target).card) =
      (adaptiveMixedSignedOriginalPrimeRealizations
        support scale outcome domain N).card := by
  let realizations :=
    adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N
  have mapped :
      (↑realizations : Set (ℕ × ℤ)).MapsTo
        (fun pair => scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index pair.1 pair.2)
        (scaleAdaptiveGTZIndexedTargetWindow index N) := by
    intro pair selected
    exact scaleAdaptiveGTZIndexedPhysicalTarget_mem_window
      support scale outcome domain index N pair selected
  have exact_fibers := Finset.card_eq_sum_card_fiberwise mapped
  change _ = realizations.card
  rw [exact_fibers]
  apply Finset.sum_congr rfl
  intro target _selected
  rfl

/-- The ACTUAL targetwise distinct-label shared-target fiber, retaining the
true signed branch centers, same physical target, and physical convex cell. -/
noncomputable def scaleAdaptiveGTZSharedTargetFiber
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N target : ℕ) :
    Finset ((ℕ × ℤ) × (ℕ × ℤ)) :=
  (adaptiveMixedSignedSharedTargetPrimeRealizations
    support scale first second firstIndex secondIndex domain N).filter
      fun pair =>
        scaleAdaptiveGTZIndexedPhysicalTarget
          support first.1 firstIndex pair.1.1 pair.1.2 = target

/-- Every genuine distinct-label signed shared-target realization has its
actual common physical target inside the first branch's moving dyadic window. -/
theorem scaleAdaptiveGTZSharedPhysicalTarget_mem_window
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ)
    (pair : (ℕ × ℤ) × (ℕ × ℤ))
    (selected : pair ∈ adaptiveMixedSignedSharedTargetPrimeRealizations
      support scale first second firstIndex secondIndex domain N) :
    scaleAdaptiveGTZIndexedPhysicalTarget
      support first.1 firstIndex pair.1.1 pair.1.2 ∈
        scaleAdaptiveGTZIndexedTargetWindow firstIndex N := by
  classical
  simp only [adaptiveMixedSignedSharedTargetPrimeRealizations,
    Finset.mem_filter] at selected
  obtain ⟨boxed, first_edge, _second_edge, _distinct,
    _shared, _domain⟩ := selected
  have first_boxed := (Finset.mem_product.mp boxed).1
  have original : pair.1 ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale first Set.univ N := by
    simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter, Set.mem_univ, and_true]
    exact ⟨first_boxed, first_edge⟩
  exact scaleAdaptiveGTZIndexedPhysicalTarget_mem_window
    support scale first Set.univ firstIndex N pair.1 original

/-- EXACT genuine targetwise SECOND incidence moment.  Summing the actual
distinct-label same-target fibers gives precisely the true signed shared-target
prime-system count; no covariance or moment hypothesis is inserted. -/
theorem scaleAdaptiveGTZSharedTarget_secondMoment_eq_realizations_card
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow firstIndex N,
      (scaleAdaptiveGTZSharedTargetFiber support scale first second
        firstIndex secondIndex domain N target).card) =
      (adaptiveMixedSignedSharedTargetPrimeRealizations
        support scale first second firstIndex secondIndex domain N).card := by
  let realizations :=
    adaptiveMixedSignedSharedTargetPrimeRealizations
      support scale first second firstIndex secondIndex domain N
  have mapped :
      (↑realizations : Set ((ℕ × ℤ) × (ℕ × ℤ))).MapsTo
        (fun pair => scaleAdaptiveGTZIndexedPhysicalTarget
          support first.1 firstIndex pair.1.1 pair.1.2)
        (scaleAdaptiveGTZIndexedTargetWindow firstIndex N) := by
    intro pair selected
    exact scaleAdaptiveGTZSharedPhysicalTarget_mem_window
      support scale first second firstIndex secondIndex
        domain N pair selected
  have exact_fibers := Finset.card_eq_sum_card_fiberwise mapped
  change _ = realizations.card
  rw [exact_fibers]
  apply Finset.sum_congr rfl
  intro target _selected
  rfl

/-- The genuine ACTUAL shared-target Bezout-fiber singular products converge
to the product of the two independently defined actual singular limits. -/
theorem scaleAdaptiveGTZActualSharedTargetSingularProduct_tendsto
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction)
    (firstSingular secondSingular : ℝ)
    (first_converges :
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale first)
          atTop (nhds firstSingular))
    (second_converges :
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale second)
          atTop (nhds secondSingular)) :
    Tendsto
      (fun cutoff : ℕ =>
        ∏ ell ∈ Nat.primesLE cutoff,
          adaptiveMixedActualSharedTargetFiberScalarLocalFactor
            support scale first second firstIndex secondIndex
              multiplier correction ell)
      atTop (nhds (firstSingular * secondSingular)) := by
  have factorization :
      (fun cutoff : ℕ =>
        ∏ ell ∈ Nat.primesLE cutoff,
          adaptiveMixedActualSharedTargetFiberScalarLocalFactor
            support scale first second firstIndex secondIndex
              multiplier correction ell) =
        fun cutoff : ℕ =>
          adaptiveMixedSignedSingularPartialProduct
            support scale first cutoff *
          adaptiveMixedSignedSingularPartialProduct
            support scale second cutoff := by
    funext cutoff
    exact adaptiveMixedActualSharedTargetFiber_finite_singular_product_eq_product
      primes first_active second_active same_type multiplier correction
        compatible (Nat.primesLE cutoff)
          (fun ell selected => Nat.prime_of_mem_primesLE selected)
  rw [factorization]
  exact first_converges.mul second_converges

/-- DIRECT fixed-cell signed targetwise FIRST moment asymptotic from the
explicit Green--Tao input.  Every actual retained rank is allowed, and the
physical convex volume and genuine positive singular factor are retained. -/
theorem scaleAdaptiveGTZIndexedTarget_firstMoment_positive_asymptotic
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support outcome.1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
        atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
            ((scaleAdaptiveGTZIndexedTargetFiber
              support scale outcome domain index N target).card : ℝ)) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 2)
        atTop (nhds ((volume domain).toReal * singular)) := by
  obtain ⟨singular, positive, converges, asymptotic⟩ :=
    scaleAdaptiveSignedOriginalPrimeRealizations_positive_asymptotic
      green_tao support scale outcome domain primes
        convex open_domain nonempty physical
  refine ⟨singular, positive, converges, ?_⟩
  have identical :
      (fun N : ℕ =>
        (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
          ((scaleAdaptiveGTZIndexedTargetFiber
            support scale outcome domain index N target).card : ℝ)) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices
              support scale outcome).card + 1) /
          (N : ℝ) ^ 2) =
      (fun N : ℕ =>
        ((adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices
              support scale outcome).card + 1) /
          (N : ℝ) ^ 2) := by
    funext N
    have exact_fibers := congrArg (fun count : ℕ => (count : ℝ))
      (scaleAdaptiveGTZIndexedTarget_firstMoment_eq_realizations_card
        support scale outcome domain index N)
    push_cast at exact_fibers
    rw [exact_fibers]
  rw [identical]
  exact asymptotic

/-- DIRECT fixed-cell genuine distinct-label shared-target SECOND moment
asymptotic from the explicit Green--Tao input.  It simultaneously identifies
the TRUE actual Bezout-fiber singular series, retains both positive individual
singular limits, the physical three-dimensional domain, the exact `s/W²`
Jacobian, and the deduplicated `r+r'+1` prime-form exponent.

No first moment, shared-target moment, covariance, variance, degree
regularity, or exceptional-label estimate is assumed. -/
theorem scaleAdaptiveGTZSharedTarget_secondMoment_positive_asymptotic
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ)
    (domain : Set (ℝ × ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆ adaptiveMixedSharedTargetPhysicalConvexWindow
      firstIndex secondIndex targetLower targetUpper
        firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper)
    (labels : ∀ point ∈ domain,
      (1 : ℝ) < point.2.1 ∧ point.2.1 < 2 ∧
        (1 : ℝ) < point.2.2 ∧ point.2.2 < 2)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction) :
    ∃ firstSingular secondSingular : ℝ,
      0 < firstSingular ∧ 0 < secondSingular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale first)
          atTop (nhds firstSingular) ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale second)
          atTop (nhds secondSingular) ∧
      Tendsto
        (fun cutoff : ℕ =>
          ∏ ell ∈ Nat.primesLE cutoff,
            adaptiveMixedActualSharedTargetFiberScalarLocalFactor
              support scale first second firstIndex secondIndex
                multiplier correction ell)
        atTop (nhds (firstSingular * secondSingular)) ∧
      Tendsto
        (fun N : ℕ =>
          (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow firstIndex N,
            ((scaleAdaptiveGTZSharedTargetFiber support scale first second
              firstIndex secondIndex domain N target).card : ℝ)) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale first).card +
               (adaptiveMixedOutcomeActiveIndices
                support scale second).card + 1) /
            (N : ℝ) ^ 3)
        atTop (nhds
          ((volume domain).toReal *
            (adaptiveMixedActualIndexType
              support first.1 firstIndex : ℝ) /
            (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
            firstSingular * secondSingular)) := by
  obtain ⟨first_singular, second_singular,
    first_converges, second_converges, asymptotic⟩ :=
    green_tao.shared_target support scale firstIndex secondIndex
      first second targetLower targetUpper
      firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper domain
      primes first_active second_active same_type
      convex open_domain nonempty physical labels
  refine ⟨first_singular, second_singular,
    scaleAdaptiveSignedSingularLimit_pos
      support scale first primes first_singular first_converges,
    scaleAdaptiveSignedSingularLimit_pos
      support scale second primes second_singular second_converges,
    first_converges, second_converges,
    scaleAdaptiveGTZActualSharedTargetSingularProduct_tendsto
      primes first_active second_active same_type
      multiplier correction compatible first_singular second_singular
      first_converges second_converges, ?_⟩
  have identical :
      (fun N : ℕ =>
        (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow firstIndex N,
          ((scaleAdaptiveGTZSharedTargetFiber support scale first second
            firstIndex secondIndex domain N target).card : ℝ)) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices
              support scale first).card +
             (adaptiveMixedOutcomeActiveIndices
              support scale second).card + 1) /
          (N : ℝ) ^ 3) =
      (fun N : ℕ =>
        ((adaptiveMixedSignedSharedTargetPrimeRealizations
          support scale first second firstIndex secondIndex
            domain N).card : ℝ) *
          Real.log (N : ℝ) ^
            ((adaptiveMixedOutcomeActiveIndices
              support scale first).card +
             (adaptiveMixedOutcomeActiveIndices
              support scale second).card + 1) /
          (N : ℝ) ^ 3) := by
    funext N
    have exact_fibers := congrArg (fun count : ℕ => (count : ℝ))
      (scaleAdaptiveGTZSharedTarget_secondMoment_eq_realizations_card
        support scale first second firstIndex secondIndex domain N)
    push_cast at exact_fibers
    rw [exact_fibers]
  rw [identical]
  exact asymptotic

end Erdos1139

