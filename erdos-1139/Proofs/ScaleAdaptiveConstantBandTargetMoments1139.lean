module

public import ScaleAdaptiveGTZSharedTargetMoments1139
public import ScaleAdaptivePrimeSliceVariance1139

@[expose] public section


/-!
# Actual shared-target prime moments on an unclipped constant-residue band

For genuine distinct prime labels `N < p,p' < 2*N`, positive physical
indices `i,j`, and one absolute residue band `u*N < r < v*N`, consider the
true shared-target coordinates `(h,p,p')`.  Inside the strict target window

    max (i+v) (j+v) < h/N < min (2*i+u) (2*j+u),

neither prime-label fiber is clipped by the dyadic shell.  Their exact
archimedean widths are `(v-u)/i` and `(v-u)/j`, so the actual physical
three-dimensional volume is

    (H_+-H_-) * (v-u)^2 / (i*j).

The signed shared-target Green--Tao input therefore has the genuine
`s/W²` Jacobian and the collision-correct product of the individual singular
series.  Dividing by the ACTUAL constant-band first-degree coefficients
`(v-u)*S/W` cancels every singular, band-width, and modulus factor.

All prime realizations below are actual signed-center realization sets and
retain globally distinct labels.  Geometric nonemptiness is never confused
with a prime witness, and the external Green--Tao statement remains an
explicit theorem parameter, not a new axiom.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos1139

/-- The actual unclipped affine shared-target band in physical `(h,p,p')`
coordinates.  Dyadic label bounds are derived from the genuine strict
interior conditions rather than silently imposed as independent boxes. -/
def scaleAdaptiveConstantBandSharedTargetDomain
    (firstIndex secondIndex : ℕ)
    (lower upper targetLower targetUpper : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {point |
    targetLower < point.1 ∧ point.1 < targetUpper ∧
      lower < point.1 - (firstIndex : ℝ) * point.2.1 ∧
      point.1 - (firstIndex : ℝ) * point.2.1 < upper ∧
      lower < point.1 - (secondIndex : ℝ) * point.2.2 ∧
      point.1 - (secondIndex : ℝ) * point.2.2 < upper}

/-- The true shared-target constant-band cell is an OPEN affine domain. -/
theorem scaleAdaptiveConstantBandSharedTargetDomain_isOpen
    (firstIndex secondIndex : ℕ)
    (lower upper targetLower targetUpper : ℝ) :
    IsOpen (scaleAdaptiveConstantBandSharedTargetDomain
      firstIndex secondIndex lower upper targetLower targetUpper) := by
  let firstResidue : (ℝ × ℝ × ℝ) → ℝ := fun point =>
    point.1 - (firstIndex : ℝ) * point.2.1
  let secondResidue : (ℝ × ℝ × ℝ) → ℝ := fun point =>
    point.1 - (secondIndex : ℝ) * point.2.2
  have first_continuous : Continuous firstResidue :=
    continuous_fst.sub
      (continuous_const.mul (continuous_fst.comp continuous_snd))
  have second_continuous : Continuous secondResidue :=
    continuous_fst.sub
      (continuous_const.mul (continuous_snd.comp continuous_snd))
  have equal :
      scaleAdaptiveConstantBandSharedTargetDomain
        firstIndex secondIndex lower upper targetLower targetUpper =
        (fun point : ℝ × ℝ × ℝ => point.1) ⁻¹'
            Set.Ioo targetLower targetUpper ∩
          firstResidue ⁻¹' Set.Ioo lower upper ∩
          secondResidue ⁻¹' Set.Ioo lower upper := by
    ext point
    simp [scaleAdaptiveConstantBandSharedTargetDomain,
      firstResidue, secondResidue]
    tauto
  rw [equal]
  exact ((isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_Ioo.preimage first_continuous)).inter
      (isOpen_Ioo.preimage second_continuous)

/-- The true constant-band shared-target cell is convex: all constraints are
strict AFFINE inequalities in the actual target and two labels. -/
theorem scaleAdaptiveConstantBandSharedTargetDomain_convex
    (firstIndex secondIndex : ℕ)
    (lower upper targetLower targetUpper : ℝ) :
    Convex ℝ (scaleAdaptiveConstantBandSharedTargetDomain
      firstIndex secondIndex lower upper targetLower targetUpper) := by
  intro first first_selected second second_selected a b a_nonnegative
    b_nonnegative sum_one
  have targets := (convex_Ioo (𝕜 := ℝ) targetLower targetUpper)
    ⟨first_selected.1, first_selected.2.1⟩
    ⟨second_selected.1, second_selected.2.1⟩
    a_nonnegative b_nonnegative sum_one
  have first_residues := (convex_Ioo (𝕜 := ℝ) lower upper)
    ⟨first_selected.2.2.1, first_selected.2.2.2.1⟩
    ⟨second_selected.2.2.1, second_selected.2.2.2.1⟩
    a_nonnegative b_nonnegative sum_one
  have second_residues := (convex_Ioo (𝕜 := ℝ) lower upper)
    ⟨first_selected.2.2.2.2.1, first_selected.2.2.2.2.2⟩
    ⟨second_selected.2.2.2.2.1, second_selected.2.2.2.2.2⟩
    a_nonnegative b_nonnegative sum_one
  change
    targetLower < a * first.1 + b * second.1 ∧
      a * first.1 + b * second.1 < targetUpper ∧
      lower < a * first.1 + b * second.1 -
        (firstIndex : ℝ) * (a * first.2.1 + b * second.2.1) ∧
      a * first.1 + b * second.1 -
        (firstIndex : ℝ) * (a * first.2.1 + b * second.2.1) < upper ∧
      lower < a * first.1 + b * second.1 -
        (secondIndex : ℝ) * (a * first.2.2 + b * second.2.2) ∧
      a * first.1 + b * second.1 -
        (secondIndex : ℝ) * (a * first.2.2 + b * second.2.2) < upper
  refine ⟨targets.1, targets.2, ?_, ?_, ?_, ?_⟩
  · calc
      lower < a * (first.1 - (firstIndex : ℝ) * first.2.1) +
          b * (second.1 - (firstIndex : ℝ) * second.2.1) :=
        first_residues.1
      _ = _ := by ring
  · calc
      _ = a * (first.1 - (firstIndex : ℝ) * first.2.1) +
          b * (second.1 - (firstIndex : ℝ) * second.2.1) := by ring
      _ < upper := first_residues.2
  · calc
      lower < a * (first.1 - (secondIndex : ℝ) * first.2.2) +
          b * (second.1 - (secondIndex : ℝ) * second.2.2) :=
        second_residues.1
      _ = _ := by ring
  · calc
      _ = a * (first.1 - (secondIndex : ℝ) * first.2.2) +
          b * (second.1 - (secondIndex : ℝ) * second.2.2) := by ring
      _ < upper := second_residues.2

/-- Every positive-width target cell and positive-width residue band has a
real strict interior for any TWO positive physical indices.  This is only
a real geometric witness, not a claimed simultaneous prime pattern. -/
theorem scaleAdaptiveConstantBandSharedTargetDomain_nonempty
    {firstIndex secondIndex : ℕ}
    {lower upper targetLower targetUpper : ℝ}
    (first_positive : 0 < firstIndex)
    (second_positive : 0 < secondIndex)
    (band_nonempty : lower < upper)
    (target_nonempty : targetLower < targetUpper) :
    (scaleAdaptiveConstantBandSharedTargetDomain
      firstIndex secondIndex lower upper targetLower targetUpper).Nonempty := by
  have first_real : (0 : ℝ) < firstIndex := by
    exact_mod_cast first_positive
  have second_real : (0 : ℝ) < secondIndex := by
    exact_mod_cast second_positive
  let target := (targetLower + targetUpper) / 2
  let residue := (lower + upper) / 2
  refine ⟨(target,
    (target - residue) / (firstIndex : ℝ),
    (target - residue) / (secondIndex : ℝ)), ?_⟩
  have first_cancellation :
      target - (firstIndex : ℝ) *
        ((target - residue) / (firstIndex : ℝ)) = residue := by
    field_simp [first_real.ne']
    ring
  have second_cancellation :
      target - (secondIndex : ℝ) *
        ((target - residue) / (secondIndex : ℝ)) = residue := by
    field_simp [second_real.ne']
    ring
  change targetLower < target ∧ target < targetUpper ∧
    lower < target - (firstIndex : ℝ) *
      ((target - residue) / (firstIndex : ℝ)) ∧
    target - (firstIndex : ℝ) *
      ((target - residue) / (firstIndex : ℝ)) < upper ∧
    lower < target - (secondIndex : ℝ) *
      ((target - residue) / (secondIndex : ℝ)) ∧
    target - (secondIndex : ℝ) *
      ((target - residue) / (secondIndex : ℝ)) < upper
  rw [first_cancellation, second_cancellation]
  dsimp [target, residue]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- On the genuinely UNCLIPPED target interior, both label coordinates
automatically lie in the full actual dyadic shell `(1,2)`. -/
theorem scaleAdaptiveConstantBandSharedTargetDomain_labels
    {firstIndex secondIndex : ℕ}
    {lower upper targetLower targetUpper : ℝ}
    (first_positive : 0 < firstIndex)
    (second_positive : 0 < secondIndex)
    (first_lower : (firstIndex : ℝ) + upper ≤ targetLower)
    (first_upper : targetUpper ≤ 2 * (firstIndex : ℝ) + lower)
    (second_lower : (secondIndex : ℝ) + upper ≤ targetLower)
    (second_upper : targetUpper ≤ 2 * (secondIndex : ℝ) + lower)
    {point : ℝ × ℝ × ℝ}
    (selected : point ∈ scaleAdaptiveConstantBandSharedTargetDomain
      firstIndex secondIndex lower upper targetLower targetUpper) :
    (1 : ℝ) < point.2.1 ∧ point.2.1 < 2 ∧
      (1 : ℝ) < point.2.2 ∧ point.2.2 < 2 := by
  have first_real : (0 : ℝ) < firstIndex := by
    exact_mod_cast first_positive
  have second_real : (0 : ℝ) < secondIndex := by
    exact_mod_cast second_positive
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra failed
    have bounded : point.2.1 ≤ 1 := le_of_not_gt failed
    have multiplied := mul_le_mul_of_nonneg_left bounded first_real.le
    nlinarith [selected.1, selected.2.2.2.1]
  · by_contra failed
    have bounded : (2 : ℝ) ≤ point.2.1 := le_of_not_gt failed
    have multiplied := mul_le_mul_of_nonneg_left bounded first_real.le
    nlinarith [selected.2.1, selected.2.2.1]
  · by_contra failed
    have bounded : point.2.2 ≤ 1 := le_of_not_gt failed
    have multiplied := mul_le_mul_of_nonneg_left bounded second_real.le
    nlinarith [selected.1, selected.2.2.2.2.2]
  · by_contra failed
    have bounded : (2 : ℝ) ≤ point.2.2 := le_of_not_gt failed
    have multiplied := mul_le_mul_of_nonneg_left bounded second_real.le
    nlinarith [selected.2.1, selected.2.2.2.2.1]

/-- The unclipped constant-band domain lies in the ACTUAL signed
shared-target physical strip, not in an artificial independent box. -/
theorem scaleAdaptiveConstantBandSharedTargetDomain_subset_physical
    {firstIndex secondIndex : ℕ}
    {lower upper targetLower targetUpper : ℝ}
    (first_positive : 0 < firstIndex)
    (second_positive : 0 < secondIndex)
    (lower_nonnegative : 0 ≤ lower)
    (upper_bounded : upper ≤ 1)
    (first_lower : (firstIndex : ℝ) + upper ≤ targetLower)
    (first_upper : targetUpper ≤ 2 * (firstIndex : ℝ) + lower)
    (second_lower : (secondIndex : ℝ) + upper ≤ targetLower)
    (second_upper : targetUpper ≤ 2 * (secondIndex : ℝ) + lower) :
    scaleAdaptiveConstantBandSharedTargetDomain
      firstIndex secondIndex lower upper targetLower targetUpper ⊆
        adaptiveMixedSharedTargetPhysicalConvexWindow
          firstIndex secondIndex targetLower targetUpper 1 2 1 2 := by
  intro point selected
  have labels := scaleAdaptiveConstantBandSharedTargetDomain_labels
    first_positive second_positive first_lower first_upper
      second_lower second_upper selected
  refine ⟨selected.1, selected.2.1,
    labels.1, labels.2.1, labels.2.2.1, labels.2.2.2,
    ?_, ?_, ?_, ?_⟩
  · linarith [selected.2.2.1]
  · push_cast
    nlinarith [selected.2.2.2.1, labels.1]
  · linarith [selected.2.2.2.2.1]
  · push_cast
    nlinarith [selected.2.2.2.2.2, labels.2.2.1]

/-- EXACT physical three-dimensional target/label/label volume on an
unclipped cell.  Both true target-dependent prime-label fibers have constant
length `(upper-lower)/index`; the target length is NOT silently dropped. -/
theorem scaleAdaptiveConstantBandSharedTargetDomain_volume
    {firstIndex secondIndex : ℕ}
    {lower upper targetLower targetUpper : ℝ}
    (first_positive : 0 < firstIndex)
    (second_positive : 0 < secondIndex)
    (band_ordered : lower ≤ upper)
    (target_ordered : targetLower ≤ targetUpper) :
    (volume (scaleAdaptiveConstantBandSharedTargetDomain
      firstIndex secondIndex lower upper targetLower targetUpper)).toReal =
        (targetUpper - targetLower) *
          ((upper - lower) / (firstIndex : ℝ)) *
          ((upper - lower) / (secondIndex : ℝ)) := by
  classical
  have first_real : (0 : ℝ) < firstIndex := by
    exact_mod_cast first_positive
  have second_real : (0 : ℝ) < secondIndex := by
    exact_mod_cast second_positive
  have first_width : 0 ≤ (upper - lower) / (firstIndex : ℝ) :=
    div_nonneg (sub_nonneg.mpr band_ordered) first_real.le
  have second_width : 0 ≤ (upper - lower) / (secondIndex : ℝ) :=
    div_nonneg (sub_nonneg.mpr band_ordered) second_real.le
  let domain := scaleAdaptiveConstantBandSharedTargetDomain
    firstIndex secondIndex lower upper targetLower targetUpper
  have measurable : MeasurableSet domain :=
    (scaleAdaptiveConstantBandSharedTargetDomain_isOpen
      firstIndex secondIndex lower upper targetLower targetUpper).measurableSet
  change (volume domain).toReal = _
  rw [MeasureTheory.Measure.volume_eq_prod ℝ (ℝ × ℝ),
    MeasureTheory.Measure.prod_apply measurable]
  have fibers :
      (fun target : ℝ =>
        (volume : Measure (ℝ × ℝ)) (Prod.mk target ⁻¹' domain)) =
        (Set.Ioo targetLower targetUpper).indicator fun _ : ℝ =>
          ENNReal.ofReal ((upper - lower) / (firstIndex : ℝ)) *
            ENNReal.ofReal ((upper - lower) / (secondIndex : ℝ)) := by
    funext target
    by_cases inside : target ∈ Set.Ioo targetLower targetUpper
    · rw [Set.indicator_of_mem inside]
      have fiber_equal :
          (Prod.mk target ⁻¹' domain) =
            Set.Ioo
                ((target - upper) / (firstIndex : ℝ))
                ((target - lower) / (firstIndex : ℝ)) ×ˢ
              Set.Ioo
                ((target - upper) / (secondIndex : ℝ))
                ((target - lower) / (secondIndex : ℝ)) := by
        ext labels
        change
          (targetLower < target ∧ target < targetUpper ∧
            lower < target - (firstIndex : ℝ) * labels.1 ∧
            target - (firstIndex : ℝ) * labels.1 < upper ∧
            lower < target - (secondIndex : ℝ) * labels.2 ∧
            target - (secondIndex : ℝ) * labels.2 < upper) ↔
              (((target - upper) / (firstIndex : ℝ) < labels.1 ∧
                labels.1 < (target - lower) / (firstIndex : ℝ)) ∧
               ((target - upper) / (secondIndex : ℝ) < labels.2 ∧
                labels.2 < (target - lower) / (secondIndex : ℝ)))
        constructor
        · rintro ⟨_, _, first_low, first_high, second_low, second_high⟩
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
          · apply (div_lt_iff₀ first_real).mpr
            linarith
          · apply (lt_div_iff₀ first_real).mpr
            linarith
          · apply (div_lt_iff₀ second_real).mpr
            linarith
          · apply (lt_div_iff₀ second_real).mpr
            linarith
        · rintro ⟨⟨first_low, first_high⟩,
            ⟨second_low, second_high⟩⟩
          have first_low' := (div_lt_iff₀ first_real).mp first_low
          have first_high' := (lt_div_iff₀ first_real).mp first_high
          have second_low' := (div_lt_iff₀ second_real).mp second_low
          have second_high' := (lt_div_iff₀ second_real).mp second_high
          exact ⟨inside.1, inside.2, by linarith, by linarith,
            by linarith, by linarith⟩
      rw [fiber_equal, MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
        MeasureTheory.Measure.prod_prod, Real.volume_Ioo,
        Real.volume_Ioo]
      have first_difference :
          (target - lower) / (firstIndex : ℝ) -
            (target - upper) / (firstIndex : ℝ) =
            (upper - lower) / (firstIndex : ℝ) := by ring
      have second_difference :
          (target - lower) / (secondIndex : ℝ) -
            (target - upper) / (secondIndex : ℝ) =
            (upper - lower) / (secondIndex : ℝ) := by ring
      rw [first_difference, second_difference]
    · rw [Set.indicator_of_notMem inside]
      have empty : (Prod.mk target ⁻¹' domain) = ∅ := by
        ext labels
        constructor
        · intro selected
          have interval : target ∈ Set.Ioo targetLower targetUpper :=
            ⟨selected.1, selected.2.1⟩
          exact (inside interval).elim
        · intro selected
          simp at selected
      rw [empty, measure_empty]
  rw [fibers, lintegral_indicator measurableSet_Ioo,
    MeasureTheory.setLIntegral_const, Real.volume_Ioo]
  norm_num [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr target_ordered),
    ENNReal.toReal_ofReal first_width,
    ENNReal.toReal_ofReal second_width]
  ring

/-- DIRECT actual-prime TARGET-INCIDENCE first moment on the genuine
constant-width signed band.  Its positive coefficient is the EXACT actual
one-label physical width `(upper-lower)/W` times its positive singular
factor; no incidence or first-moment estimate is separately assumed. -/
theorem scaleAdaptiveConstantBandIndexedTarget_firstMoment_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
          atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
            ((scaleAdaptiveGTZIndexedTargetFiber support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper)
              index N target).card : ℝ)) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 2)
        atTop (nhds
          (((upper - lower) /
            (adaptiveMixedTypeModulus support : ℝ)) * singular)) := by
  obtain ⟨singular, positive, converges, asymptotic⟩ :=
    scaleAdaptiveGTZIndexedTarget_firstMoment_positive_asymptotic
      green_tao support scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          support outcome.1 lower upper)
        index primes
        (scaleAdaptiveSignedConstantResidueBand_convex
          support outcome.1 lower upper)
        (scaleAdaptiveSignedConstantResidueBand_isOpen
          support outcome.1 lower upper)
        (scaleAdaptiveSignedConstantResidueBand_nonempty
          support outcome.1 lower upper primes band_nonempty)
        (scaleAdaptiveSignedConstantResidueBand_subset_physical
          support outcome.1 lower upper lower_nonnegative upper_bounded)
  refine ⟨singular, positive, converges, ?_⟩
  rw [scaleAdaptiveSignedConstantResidueBand_volume
    support outcome.1 lower upper primes band_nonempty.le] at asymptotic
  exact asymptotic

/-- DIRECT actual distinct-PRIME-LABEL shared-target SECOND incidence
moment on a genuine UNCLIPPED target interval.  The full main term retains
the exact target length, both moving prime-label fiber widths, the true
same-type `s/W²` Jacobian, and BOTH collision-correct singular factors.

This follows SOLELY from the explicit signed Green--Tao prime-pattern
asymptotic; no targetwise moment, variance, degree, or prime witness is
postulated. -/
theorem scaleAdaptiveConstantBandSharedTarget_secondMoment_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (lower upper targetLower targetUpper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (first_positive : 0 < firstIndex)
    (second_positive : 0 < secondIndex)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (target_nonempty : targetLower < targetUpper)
    (first_lower : (firstIndex : ℝ) + upper ≤ targetLower)
    (first_upper : targetUpper ≤ 2 * (firstIndex : ℝ) + lower)
    (second_lower : (secondIndex : ℝ) + upper ≤ targetLower)
    (second_upper : targetUpper ≤ 2 * (secondIndex : ℝ) + lower)
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
              firstIndex secondIndex
                (scaleAdaptiveConstantBandSharedTargetDomain
                  firstIndex secondIndex lower upper targetLower targetUpper)
              N target).card : ℝ)) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale first).card +
               (adaptiveMixedOutcomeActiveIndices
                support scale second).card + 1) /
            (N : ℝ) ^ 3)
        atTop (nhds
          ((targetUpper - targetLower) *
            ((upper - lower) / (firstIndex : ℝ)) *
            ((upper - lower) / (secondIndex : ℝ)) *
            (adaptiveMixedActualIndexType
              support first.1 firstIndex : ℝ) /
            (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
            firstSingular * secondSingular)) := by
  let domain := scaleAdaptiveConstantBandSharedTargetDomain
    firstIndex secondIndex lower upper targetLower targetUpper
  obtain ⟨firstSingular, secondSingular, first_positive_singular,
    second_positive_singular, first_converges, second_converges,
    shared_converges, asymptotic⟩ :=
    scaleAdaptiveGTZSharedTarget_secondMoment_positive_asymptotic
      green_tao targetLower targetUpper 1 2 1 2 domain primes
      first_active second_active same_type
      (scaleAdaptiveConstantBandSharedTargetDomain_convex
        firstIndex secondIndex lower upper targetLower targetUpper)
      (scaleAdaptiveConstantBandSharedTargetDomain_isOpen
        firstIndex secondIndex lower upper targetLower targetUpper)
      (scaleAdaptiveConstantBandSharedTargetDomain_nonempty
        first_positive second_positive band_nonempty target_nonempty)
      (scaleAdaptiveConstantBandSharedTargetDomain_subset_physical
        first_positive second_positive lower_nonnegative upper_bounded
        first_lower first_upper second_lower second_upper)
      (fun point selected =>
        scaleAdaptiveConstantBandSharedTargetDomain_labels
          first_positive second_positive first_lower first_upper
          second_lower second_upper selected)
      multiplier correction compatible
  refine ⟨firstSingular, secondSingular, first_positive_singular,
    second_positive_singular, first_converges, second_converges,
    shared_converges, ?_⟩
  change Tendsto _ atTop (nhds _) at asymptotic ⊢
  change Tendsto _ atTop
    (nhds ((volume domain).toReal * _ / _ * _ * _)) at asymptotic
  rw [scaleAdaptiveConstantBandSharedTargetDomain_volume
    first_positive second_positive band_nonempty.le target_nonempty.le]
      at asymptotic
  exact asymptotic

/-- EXACT normalized true shared-target main-term cancellation.  Dividing the
physical second coefficient by the TWO actual constant-band first-degree
coefficients eliminates the band width, full `W²` conductor Jacobian, and
BOTH mixed singular factors, retaining precisely `targetLength*s/(i*j)`.

No independence is claimed: this is the genuine coefficient identity after
the separately proved collision-aware prime-pattern singular factorization. -/
theorem scaleAdaptiveConstantBandSharedTarget_normalized_main_term
    {firstIndex secondIndex : ℕ}
    {lower upper targetLower targetUpper firstSingular secondSingular : ℝ}
    {support : Finset ℕ} {type : ℕ}
    (first_positive : 0 < firstIndex)
    (second_positive : 0 < secondIndex)
    (band_nonempty : lower < upper)
    (modulus_positive : 0 < adaptiveMixedTypeModulus support)
    (first_singular_positive : 0 < firstSingular)
    (second_singular_positive : 0 < secondSingular) :
    ((targetUpper - targetLower) *
      ((upper - lower) / (firstIndex : ℝ)) *
      ((upper - lower) / (secondIndex : ℝ)) *
      (type : ℝ) / (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
      firstSingular * secondSingular) /
      (((upper - lower) /
        (adaptiveMixedTypeModulus support : ℝ) * firstSingular) *
       ((upper - lower) /
        (adaptiveMixedTypeModulus support : ℝ) * secondSingular)) =
      (targetUpper - targetLower) * (type : ℝ) /
        ((firstIndex : ℝ) * (secondIndex : ℝ)) := by
  have first_real : (0 : ℝ) < firstIndex := by
    exact_mod_cast first_positive
  have second_real : (0 : ℝ) < secondIndex := by
    exact_mod_cast second_positive
  have modulus_real : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast modulus_positive
  have width_nonzero : upper - lower ≠ 0 :=
    ne_of_gt (sub_pos.mpr band_nonempty)
  field_simp [first_real.ne', second_real.ne', modulus_real.ne',
    width_nonzero, first_singular_positive.ne',
    second_singular_positive.ne']

end Erdos1139
