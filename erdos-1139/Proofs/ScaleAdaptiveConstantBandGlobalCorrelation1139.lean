module

public import ScaleAdaptiveConstantBandDegreeTransfer1139
public import ScaleAdaptiveConstantBandTargetMoments1139

@[expose] public section


/-!
# Actual global target transfer and the remaining off-diagonal obstruction

An actual inverse-degree signed pattern gives each genuine usable prime label
UNIT mass.  The previous degree-transfer theorem normalizes that mass by
`log N / N`; on about `N / log N` true typed prime targets this controls the
MEAN absolute actual/model target error, not its untruncated second moment.

The finite lemmas below keep those scales explicit.  They give exact
homogeneity, honest Markov deletion of bad actual targets, and centered
second-moment transfer on the remaining good targets.  No conversion from
an L1 error to a global L2 error is made without an actual pointwise bound.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1139

/-- Genuine physical-target load when every nonempty ACTUAL prime-label
fiber carries its natural unit pattern mass. -/
noncomputable def scaleAdaptiveSignedUnitActualTargetLoad
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ) : ℝ :=
  scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
    support scale outcome domain index N (fun _ => 1) target

/-- Matching true physical-target model with unit prime-label mass and the
specified label-constant positive expected pattern degree. -/
noncomputable def scaleAdaptiveSignedUnitModelTargetLoad
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ)
    (expected : ℝ) : ℝ :=
  scaleAdaptiveSignedModelDegreeIndexedTargetLoad
    support scale outcome domain index N
      (fun _ => 1) (fun _ => expected) target

/-- Actual inverse-INTEGER-degree physical-target load is exactly homogeneous
in constant prime-label pattern mass.  No degree or analytic premise is used. -/
theorem scaleAdaptiveSignedInverseDegreeIndexedTargetLoad_const_mass
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ)
    (mass : ℝ) :
    scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
      support scale outcome domain index N (fun _ => mass) target =
      mass * scaleAdaptiveSignedUnitActualTargetLoad
        support scale outcome domain index N target := by
  unfold scaleAdaptiveSignedUnitActualTargetLoad
  unfold scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  dsimp
  ring

/-- The true constant-degree model has the identical exact pattern-mass
homogeneity, retaining the actual label-target incidence fibers. -/
theorem scaleAdaptiveSignedModelDegreeIndexedTargetLoad_const_mass
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ)
    (mass expected : ℝ) :
    scaleAdaptiveSignedModelDegreeIndexedTargetLoad
      support scale outcome domain index N
        (fun _ => mass) (fun _ => expected) target =
      mass * scaleAdaptiveSignedUnitModelTargetLoad
        support scale outcome domain index N target expected := by
  unfold scaleAdaptiveSignedUnitModelTargetLoad
  unfold scaleAdaptiveSignedModelDegreeIndexedTargetLoad
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  dsimp
  ring

/-- Exact finite FIRST moment of the unit-mass genuine inverse-degree
distribution: each usable actual prime label contributes exactly one. -/
theorem scaleAdaptiveSignedUnitActualTargetLoad_firstMoment
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
      scaleAdaptiveSignedUnitActualTargetLoad
        support scale outcome domain index N target) =
      ((scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N).card : ℝ) := by
  unfold scaleAdaptiveSignedUnitActualTargetLoad
  rw [scaleAdaptiveSignedInverseDegreeIndexedTarget_firstMoment_eq]
  simp

/-- Bad ACTUAL physical targets for a specified fixed error tolerance; the
ambient targets may be a genuine typed prime cell or any true subwindow. -/
noncomputable def scaleAdaptiveSignedUnitBadTargets
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (expected tolerance : ℝ) : Finset ℕ :=
  targets.filter fun target =>
    tolerance ≤
      |scaleAdaptiveSignedUnitActualTargetLoad
        support scale outcome domain index N target -
       scaleAdaptiveSignedUnitModelTargetLoad
        support scale outcome domain index N target expected|

/-- Exact finite Markov bound for genuine unit-mass actual/model target
loads.  The cardinality is in TRUE targets, not in labels or centers. -/
theorem scaleAdaptiveSignedUnitBadTargets_card_mul_tolerance_le
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (expected tolerance : ℝ) :
    ((scaleAdaptiveSignedUnitBadTargets
      support scale outcome domain index N targets expected tolerance).card : ℝ) *
        tolerance ≤
      ∑ target ∈ targets,
        |scaleAdaptiveSignedUnitActualTargetLoad
          support scale outcome domain index N target -
         scaleAdaptiveSignedUnitModelTargetLoad
          support scale outcome domain index N target expected| := by
  exact weightedPrimePattern_bad_targets_card_mul_threshold_le
    targets
    (scaleAdaptiveSignedUnitActualTargetLoad
      support scale outcome domain index N)
    (fun target => scaleAdaptiveSignedUnitModelTargetLoad
      support scale outcome domain index N target expected)
    tolerance

/-- On the ACTUAL retained good target cell, a true model centered variance
transfers with the sharp elementary error `2 * #good * tolerance²`.  This
does not assert any untruncated actual second-moment bound. -/
theorem scaleAdaptiveSignedGoodTargets_centeredVariance_le_model
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (expected tolerance : ℝ)
    (mean : ℕ → ℝ) :
    let good := targets.filter fun target =>
      |scaleAdaptiveSignedUnitActualTargetLoad
        support scale outcome domain index N target -
       scaleAdaptiveSignedUnitModelTargetLoad
        support scale outcome domain index N target expected| ≤ tolerance
    (∑ target ∈ good,
      (scaleAdaptiveSignedUnitActualTargetLoad
        support scale outcome domain index N target - mean target) ^ 2) ≤
      2 * (∑ target ∈ good,
        (scaleAdaptiveSignedUnitModelTargetLoad
          support scale outcome domain index N target expected -
            mean target) ^ 2) +
        2 * (good.card : ℝ) * tolerance ^ 2 := by
  dsimp
  apply weightedPrimePattern_actual_centered_moment_le_of_model
  intro target selected
  exact (Finset.mem_filter.mp selected).2

/-- Exact relation between the previously proved normalized total variation
and the physically meaningful UNIT-label-mass target error.  Its scale is
`(log N / N) * ∑ₕ |actualₕ-modelₕ|`; there is no hidden target factor. -/
theorem scaleAdaptiveSignedNormalizedActualTargetVariation_eq_weight_mul_unit
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ) (expected : ℝ)
    (large : 2 ≤ N) :
    scaleAdaptiveSignedNormalizedActualTargetVariation
      support scale outcome domain index N expected =
      scaleAdaptivePrimeLabelNormalizedWeight N *
        ∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
          |scaleAdaptiveSignedUnitActualTargetLoad
            support scale outcome domain index N target -
           scaleAdaptiveSignedUnitModelTargetLoad
            support scale outcome domain index N target expected| := by
  unfold scaleAdaptiveSignedNormalizedActualTargetVariation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _
  rw [scaleAdaptiveSignedInverseDegreeIndexedTargetLoad_const_mass
    support scale outcome domain index N target
      (scaleAdaptivePrimeLabelNormalizedWeight N),
    scaleAdaptiveSignedModelDegreeIndexedTargetLoad_const_mass
      support scale outcome domain index N target
        (scaleAdaptivePrimeLabelNormalizedWeight N) expected,
    ← mul_sub, abs_mul,
    abs_of_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)]

/-- Restricting to ANY actual physical subcell can only lower its correctly
normalized absolute target-transfer error. -/
theorem scaleAdaptiveSignedRestrictedUnitError_le_normalizedTargetVariation
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (expected : ℝ)
    (large : 2 ≤ N)
    (supported : targets ⊆ scaleAdaptiveGTZIndexedTargetWindow index N) :
    scaleAdaptivePrimeLabelNormalizedWeight N *
      (∑ target ∈ targets,
        |scaleAdaptiveSignedUnitActualTargetLoad
          support scale outcome domain index N target -
         scaleAdaptiveSignedUnitModelTargetLoad
          support scale outcome domain index N target expected|) ≤
      scaleAdaptiveSignedNormalizedActualTargetVariation
        support scale outcome domain index N expected := by
  rw [scaleAdaptiveSignedNormalizedActualTargetVariation_eq_weight_mul_unit
    support scale outcome domain index N expected large]
  apply mul_le_mul_of_nonneg_left _
    (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact supported
  · intro target _ _
    exact abs_nonneg _

/-- Exact prime-density-normalized bad-target Markov inequality.  The bad
objects are genuine physical targets, and the right-hand side is the
previously proved actual inverse-degree total variation. -/
theorem scaleAdaptiveSignedUnitBadTargets_normalizedMass_mul_tolerance_le
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (expected tolerance : ℝ)
    (large : 2 ≤ N)
    (supported : targets ⊆ scaleAdaptiveGTZIndexedTargetWindow index N) :
    ((scaleAdaptiveSignedUnitBadTargets
      support scale outcome domain index N targets expected tolerance).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N * tolerance ≤
      scaleAdaptiveSignedNormalizedActualTargetVariation
        support scale outcome domain index N expected := by
  have markov := scaleAdaptiveSignedUnitBadTargets_card_mul_tolerance_le
    support scale outcome domain index N targets expected tolerance
  have multiplied := mul_le_mul_of_nonneg_left markov
    (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  calc
    _ = scaleAdaptivePrimeLabelNormalizedWeight N *
      (((scaleAdaptiveSignedUnitBadTargets
        support scale outcome domain index N targets expected tolerance).card : ℝ) *
          tolerance) := by ring
    _ ≤ scaleAdaptivePrimeLabelNormalizedWeight N *
      (∑ target ∈ targets,
        |scaleAdaptiveSignedUnitActualTargetLoad
          support scale outcome domain index N target -
         scaleAdaptiveSignedUnitModelTargetLoad
          support scale outcome domain index N target expected|) :=
      multiplied
    _ ≤ _ :=
      scaleAdaptiveSignedRestrictedUnitError_le_normalizedTargetVariation
        support scale outcome domain index N targets expected large supported

/-- ACTUAL vanishing-density bad physical targets on every fixed genuine
constant-residue band and every actual target subcell.  The sole analytic
input is the source-faithful fixed signed Green--Tao package.  The tolerance
is fixed POSITIVE, the target family is an honest subwindow, and the
conclusion is exactly `#bad * log N / N → 0`; it makes no false global
actual second-moment inference. -/
theorem scaleAdaptiveSignedConstantResidueBand_badTargets_normalizedDensity_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index : ℕ) (lower upper tolerance : ℝ)
    (targets : ℕ → Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (strict : lower < upper)
    (upper_bounded : upper ≤ 1)
    (tolerance_positive : 0 < tolerance)
    (supported : ∀ N : ℕ,
      targets N ⊆ scaleAdaptiveGTZIndexedTargetWindow index N) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedUnitBadTargets
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            index N (targets N)
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N)
            tolerance).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, _full, _usable, _empty, _density, variation⟩ :=
    scaleAdaptiveSignedConstantResidueBand_actualDegreeTransfer_tendsto_of_GTZ
      green_tao support scale outcome index lower upper primes
      lower_nonnegative strict upper_bounded
  refine ⟨singular, positive, ?_⟩
  have divided :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedNormalizedActualTargetVariation
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            index N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N) / tolerance)
        atTop (nhds (0 : ℝ)) := by
    simpa using variation.div_const tolerance
  apply squeeze_zero' _ _ divided
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact mul_nonneg (Nat.cast_nonneg _)
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  · filter_upwards [eventually_ge_atTop 2] with N large
    apply (le_div_iff₀ tolerance_positive).mpr
    exact scaleAdaptiveSignedUnitBadTargets_normalizedMass_mul_tolerance_le
      support scale outcome
      (scaleAdaptiveSignedConstantResidueBand
        support outcome.1 lower upper)
      index N (targets N)
      (scaleAdaptiveSignedConstantResidueBandExpectedDegree
        support scale outcome lower upper singular N)
      tolerance large (supported N)

/-- The true inverse-degree total variation is always nonnegative. -/
theorem scaleAdaptiveSignedNormalizedActualTargetVariation_nonnegative
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ) (expected : ℝ) :
    0 ≤ scaleAdaptiveSignedNormalizedActualTargetVariation
      support scale outcome domain index N expected := by
  unfold scaleAdaptiveSignedNormalizedActualTargetVariation
  exact Finset.sum_nonneg fun _target _ => abs_nonneg _

/-- An explicit vanishing target-transfer tolerance that remains STRICTLY
positive at every positive scale, including scales where the actual/model
variation is exactly zero. -/
noncomputable def scaleAdaptiveSignedAdaptiveTargetTolerance
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ) (expected : ℝ) : ℝ :=
  Real.sqrt
    (scaleAdaptiveSignedNormalizedActualTargetVariation
      support scale outcome domain index N expected + (N : ℝ)⁻¹)

/-- The adaptive square-root tolerance is positive at every relevant true
integer scale; zero total variation therefore causes no bad-set pathology. -/
theorem scaleAdaptiveSignedAdaptiveTargetTolerance_positive
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ) (expected : ℝ)
    (large : 2 ≤ N) :
    0 < scaleAdaptiveSignedAdaptiveTargetTolerance
      support scale outcome domain index N expected := by
  unfold scaleAdaptiveSignedAdaptiveTargetTolerance
  apply Real.sqrt_pos.mpr
  exact add_pos_of_nonneg_of_pos
    (scaleAdaptiveSignedNormalizedActualTargetVariation_nonnegative
      support scale outcome domain index N expected)
    (inv_pos.mpr (by exact_mod_cast (by omega : 0 < N)))

theorem scaleAdaptiveSignedAdaptiveTargetTolerance_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index : ℕ) (expected : ℕ → ℝ)
    (variation : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedNormalizedActualTargetVariation
        support scale outcome domain index N (expected N))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedAdaptiveTargetTolerance
        support scale outcome domain index N (expected N))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveSignedAdaptiveTargetTolerance
  simpa using
    (variation.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))).sqrt

/-- Vanishing-density ACTUAL bad targets with a SINGLE vanishing tolerance,
not merely with a separately chosen fixed positive tolerance.  Every retained
target has actual/model unit-load error tending uniformly to zero, while the
deleted genuine targets have normalized density zero.  Only the signed GTZ
package is assumed. -/
theorem scaleAdaptiveSignedConstantResidueBand_adaptiveBadTargets_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index : ℕ) (lower upper : ℝ)
    (targets : ℕ → Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (strict : lower < upper)
    (upper_bounded : upper ≤ 1)
    (supported : ∀ N : ℕ,
      targets N ⊆ scaleAdaptiveGTZIndexedTargetWindow index N) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedAdaptiveTargetTolerance
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            index N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedUnitBadTargets
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            index N (targets N)
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N)
            (scaleAdaptiveSignedAdaptiveTargetTolerance
              support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper)
              index N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper singular N))).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, _full, _usable, _empty, _density, variation⟩ :=
    scaleAdaptiveSignedConstantResidueBand_actualDegreeTransfer_tendsto_of_GTZ
      green_tao support scale outcome index lower upper primes
      lower_nonnegative strict upper_bounded
  let band := scaleAdaptiveSignedConstantResidueBand
    support outcome.1 lower upper
  let expected : ℕ → ℝ := fun N =>
    scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper singular N
  have variation' :
      Tendsto
        (fun N : ℕ => scaleAdaptiveSignedNormalizedActualTargetVariation
          support scale outcome band index N (expected N))
        atTop (nhds (0 : ℝ)) := by
    simpa [band, expected] using variation
  have tolerance := scaleAdaptiveSignedAdaptiveTargetTolerance_tendsto_zero
    support scale outcome band index expected variation'
  refine ⟨singular, positive, by simpa [band, expected] using tolerance, ?_⟩
  have target :
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedUnitBadTargets
            support scale outcome band index N (targets N) (expected N)
            (scaleAdaptiveSignedAdaptiveTargetTolerance
              support scale outcome band index N (expected N))).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero' _ _ tolerance
    · filter_upwards [eventually_ge_atTop 2] with N large
      exact mul_nonneg (Nat.cast_nonneg _)
        (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
    · filter_upwards [eventually_ge_atTop 2] with N large
      let threshold := scaleAdaptiveSignedAdaptiveTargetTolerance
        support scale outcome band index N (expected N)
      have threshold_positive :=
        scaleAdaptiveSignedAdaptiveTargetTolerance_positive
          support scale outcome band index N (expected N) large
      have markov :=
        scaleAdaptiveSignedUnitBadTargets_normalizedMass_mul_tolerance_le
          support scale outcome band index N (targets N)
          (expected N) threshold large (supported N)
      have variation_nonnegative :=
        scaleAdaptiveSignedNormalizedActualTargetVariation_nonnegative
          support scale outcome band index N (expected N)
      have inverse_nonnegative : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
      have threshold_square :
          threshold ^ 2 =
            scaleAdaptiveSignedNormalizedActualTargetVariation
              support scale outcome band index N (expected N) +
              (N : ℝ)⁻¹ := by
        dsimp [threshold, scaleAdaptiveSignedAdaptiveTargetTolerance]
        exact Real.sq_sqrt (add_nonneg variation_nonnegative inverse_nonnegative)
      apply (mul_le_mul_iff_of_pos_right threshold_positive).mp
      calc
        _ ≤ scaleAdaptiveSignedNormalizedActualTargetVariation
          support scale outcome band index N (expected N) := markov
        _ ≤ threshold ^ 2 := by
          rw [threshold_square]
          exact le_add_of_nonneg_right inverse_nonnegative
        _ = _ := by ring
  simpa [band, expected] using target

/-- The ACTUAL good target cell is the exact complement of the bad
inverse-degree transfer targets within the original genuine target cell. -/
noncomputable def scaleAdaptiveSignedUnitGoodTargets
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (expected tolerance : ℝ) : Finset ℕ :=
  targets \ scaleAdaptiveSignedUnitBadTargets
    support scale outcome domain index N targets expected tolerance

/-- Every retained target has STRICTLY smaller actual/model unit-load error
than the true deletion threshold. -/
theorem scaleAdaptiveSignedUnitGoodTargets_error_lt
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (expected tolerance : ℝ)
    {target : ℕ}
    (selected : target ∈ scaleAdaptiveSignedUnitGoodTargets
      support scale outcome domain index N targets expected tolerance) :
    |scaleAdaptiveSignedUnitActualTargetLoad
      support scale outcome domain index N target -
     scaleAdaptiveSignedUnitModelTargetLoad
      support scale outcome domain index N target expected| < tolerance := by
  have decoded := Finset.mem_sdiff.mp selected
  apply lt_of_not_ge
  intro large
  apply decoded.2
  exact Finset.mem_filter.mpr ⟨decoded.1, large⟩

/-- Honest finite good-target variance transfer at the ORIGINAL prime-density
scale.  Every discarded actual target is retained in the exact bad set; no
global L1-to-L2 conversion or pointwise bound is asserted. -/
theorem scaleAdaptiveSignedUnitGoodTargets_normalizedCenteredVariance_le_model
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (expected tolerance : ℝ)
    (mean : ℕ → ℝ)
    (large : 2 ≤ N) :
    let good := scaleAdaptiveSignedUnitGoodTargets
      support scale outcome domain index N targets expected tolerance
    scaleAdaptivePrimeLabelNormalizedWeight N *
      (∑ target ∈ good,
        (scaleAdaptiveSignedUnitActualTargetLoad
          support scale outcome domain index N target - mean target) ^ 2) ≤
      2 * (scaleAdaptivePrimeLabelNormalizedWeight N *
        (∑ target ∈ targets,
          (scaleAdaptiveSignedUnitModelTargetLoad
            support scale outcome domain index N target expected -
              mean target) ^ 2)) +
        2 * ((targets.card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N) * tolerance ^ 2 := by
  dsimp
  let good := scaleAdaptiveSignedUnitGoodTargets
    support scale outcome domain index N targets expected tolerance
  have weight_nonnegative :=
    scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
  have variance := weightedPrimePattern_actual_centered_moment_le_of_model
    good
    (scaleAdaptiveSignedUnitActualTargetLoad
      support scale outcome domain index N)
    (fun target => scaleAdaptiveSignedUnitModelTargetLoad
      support scale outcome domain index N target expected)
    mean tolerance
    (fun target selected =>
      (scaleAdaptiveSignedUnitGoodTargets_error_lt
        support scale outcome domain index N targets expected tolerance
        selected).le)
  have supported : good ⊆ targets := Finset.sdiff_subset
  have model_subset :
      (∑ target ∈ good,
        (scaleAdaptiveSignedUnitModelTargetLoad
          support scale outcome domain index N target expected -
            mean target) ^ 2) ≤
      ∑ target ∈ targets,
        (scaleAdaptiveSignedUnitModelTargetLoad
          support scale outcome domain index N target expected -
            mean target) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact supported
    · intro target _ _
      exact sq_nonneg _
  have first := mul_le_mul_of_nonneg_left model_subset weight_nonnegative
  have card_le : (good.card : ℝ) ≤ (targets.card : ℝ) := by
    exact_mod_cast Finset.card_le_card supported
  have second := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right card_le weight_nonnegative)
    (sq_nonneg tolerance)
  calc
    _ ≤ scaleAdaptivePrimeLabelNormalizedWeight N *
      (2 * (∑ target ∈ good,
        (scaleAdaptiveSignedUnitModelTargetLoad
          support scale outcome domain index N target expected -
            mean target) ^ 2) +
        2 * (good.card : ℝ) * tolerance ^ 2) :=
      mul_le_mul_of_nonneg_left variance weight_nonnegative
    _ = 2 * (scaleAdaptivePrimeLabelNormalizedWeight N *
      (∑ target ∈ good,
        (scaleAdaptiveSignedUnitModelTargetLoad
          support scale outcome domain index N target expected -
            mean target) ^ 2)) +
        2 * ((good.card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N) * tolerance ^ 2 := by
      ring
    _ ≤ _ := by
      nlinarith

theorem scaleAdaptiveSignedFullDegreeResidual_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (expected : ℕ → ℝ)
    (quadratic : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedFullRelativeDegreeError
        support scale outcome domain N (expected N))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveWeightedDegreeResidual
        (scaleAdaptiveSignedDegreePrimeLabels N)
        (fun label =>
          (scaleAdaptiveSignedDegree
            support scale outcome domain N label : ℝ))
        (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
        (fun _ => expected N))
      atTop (nhds (0 : ℝ)) := by
  have product :=
    scaleAdaptiveSignedDegreePrimeLabels_normalizedWeight_tendsto_one.mul
      quadratic
  have root :
      Tendsto
        (fun N : ℕ => Real.sqrt
          (((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N *
            scaleAdaptiveSignedFullRelativeDegreeError
              support scale outcome domain N (expected N)))
        atTop (nhds (0 : ℝ)) := by
    simpa using product.sqrt
  apply squeeze_zero' _ _ root
  · filter_upwards [eventually_ge_atTop 2] with N large
    apply scaleAdaptiveWeightedDegreeResidual_nonnegative
    intro label _
    exact scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
  · filter_upwards [eventually_ge_atTop 2] with N large
    have cauchy := scaleAdaptiveWeightedDegreeResidual_le_sqrt
      (scaleAdaptiveSignedDegreePrimeLabels N)
      (fun label =>
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ))
      (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
      (fun _ => expected N)
      (fun _label _ =>
        scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
    simpa [scaleAdaptiveSignedFullRelativeDegreeError,
      Finset.sum_const, nsmul_eq_mul] using cauchy

theorem scaleAdaptiveSignedFullDegreeSignedResidual_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (expected : ℕ → ℝ)
    (quadratic : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedFullRelativeDegreeError
        support scale outcome domain N (expected N))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
          scaleAdaptivePrimeLabelNormalizedWeight N *
            ((scaleAdaptiveSignedDegree
              support scale outcome domain N label : ℝ) /
                expected N - 1))
      atTop (nhds (0 : ℝ)) := by
  have residual := scaleAdaptiveSignedFullDegreeResidual_tendsto_zero
    support scale outcome domain expected quadratic
  have absolute :
      Tendsto
        (fun N : ℕ =>
          |∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            scaleAdaptivePrimeLabelNormalizedWeight N *
              ((scaleAdaptiveSignedDegree
                support scale outcome domain N label : ℝ) /
                  expected N - 1)|)
        atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) _ residual
    filter_upwards [eventually_ge_atTop 2] with N large
    calc
      _ ≤ ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
        |scaleAdaptivePrimeLabelNormalizedWeight N *
          ((scaleAdaptiveSignedDegree
            support scale outcome domain N label : ℝ) /
              expected N - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        unfold scaleAdaptiveWeightedDegreeResidual
        apply Finset.sum_congr rfl
        intro label _
        rw [abs_mul, abs_of_nonneg
          (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)]
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr absolute

theorem scaleAdaptiveSignedFullExpectedFirstRatio_tendsto_one
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (expected : ℕ → ℝ)
    (quadratic : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedFullRelativeDegreeError
        support scale outcome domain N (expected N))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N).card : ℝ) /
            expected N * scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (1 : ℝ)) := by
  have signed := scaleAdaptiveSignedFullDegreeSignedResidual_tendsto_zero
    support scale outcome domain expected quadratic
  have combined := signed.add
    scaleAdaptiveSignedDegreePrimeLabels_normalizedWeight_tendsto_one
  have target :
      Tendsto
        (fun N : ℕ =>
          (∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            scaleAdaptivePrimeLabelNormalizedWeight N *
              ((scaleAdaptiveSignedDegree
                support scale outcome domain N label : ℝ) /
                  expected N - 1)) +
          ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (1 : ℝ)) := by
    simpa using combined
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    have degrees :
        ((adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N).card : ℝ) =
          ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            (scaleAdaptiveSignedDegree
              support scale outcome domain N label : ℝ) := by
      exact_mod_cast
        scaleAdaptiveSignedOriginalPrimeRealizations_card_eq_degree_sum
          support scale outcome domain N
    dsimp
    rw [degrees]
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_div]
    ring

/-- The singular constant hidden in an ACTUAL vanishing relative-degree
variance is uniquely the genuine signed prime-pattern Euler-product limit.
This prevents independently obtained target moments and inverse-degree
transfer from silently using incompatible singular constants.  The proof
derives the true first prime-pattern asymptotic from weighted Cauchy and
ordinary PNT, then identifies its coefficient with the original GTZ count. -/
theorem scaleAdaptiveSignedConstantResidueBand_singular_converges_of_fullRelative
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (strict : lower < upper)
    (upper_bounded : upper ≤ 1)
    (singular_positive : 0 < singular)
    (quadratic :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ))) :
    Tendsto (adaptiveMixedSignedSingularPartialProduct support scale outcome)
      atTop (nhds singular) := by
  let band := scaleAdaptiveSignedConstantResidueBand
    support outcome.1 lower upper
  let width :=
    (upper - lower) / (adaptiveMixedTypeModulus support : ℝ)
  let expected : ℕ → ℝ := fun N =>
    scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper singular N
  have quadratic' :
      Tendsto
        (fun N : ℕ => scaleAdaptiveSignedFullRelativeDegreeError
          support scale outcome band N (expected N))
        atTop (nhds (0 : ℝ)) := by
    simpa [band, expected] using quadratic
  have ratio := scaleAdaptiveSignedFullExpectedFirstRatio_tendsto_one
    support scale outcome band expected quadratic'
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have width_positive : 0 < width := by
    dsimp [width]
    exact div_pos (sub_pos.mpr strict) modulus_positive
  have scaled := ratio.const_mul (width * singular)
  have first :
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedOriginalPrimeRealizations
            support scale outcome band N).card : ℝ) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 2)
        atTop (nhds (width * singular)) := by
    have target :
        Tendsto
          (fun N : ℕ =>
            (width * singular) *
              (((adaptiveMixedSignedOriginalPrimeRealizations
                support scale outcome band N).card : ℝ) /
                expected N * scaleAdaptivePrimeLabelNormalizedWeight N))
          atTop (nhds (width * singular)) := by
      simpa using scaled
    apply target.congr'
    filter_upwards [eventually_ge_atTop 2] with N large
    have N_nonzero : (N : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : N ≠ 0)
    have log_nonzero : Real.log (N : ℝ) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · exact_mod_cast (by omega : 0 < N)
      · exact_mod_cast (by omega : N ≠ 1)
    dsimp [expected]
    unfold scaleAdaptiveSignedConstantResidueBandExpectedDegree
      scaleAdaptivePrimeLabelNormalizedWeight
    dsimp [width]
    field_simp [N_nonzero, log_nonzero, modulus_positive.ne',
      (sub_pos.mpr strict).ne', singular_positive.ne']
    ring
  obtain ⟨canonical, _canonical_positive, converges, original⟩ :=
    scaleAdaptiveSignedOriginalPrimeRealizations_positive_asymptotic
      green_tao support scale outcome band primes
        (scaleAdaptiveSignedConstantResidueBand_convex
          support outcome.1 lower upper)
        (scaleAdaptiveSignedConstantResidueBand_isOpen
          support outcome.1 lower upper)
        (scaleAdaptiveSignedConstantResidueBand_nonempty
          support outcome.1 lower upper primes strict)
        (scaleAdaptiveSignedConstantResidueBand_subset_physical
          support outcome.1 lower upper lower_nonnegative upper_bounded)
  have original' :
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedOriginalPrimeRealizations
            support scale outcome band N).card : ℝ) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 2)
        atTop (nhds (width * canonical)) := by
    convert original using 1
    dsimp [band, width]
    rw [scaleAdaptiveSignedConstantResidueBand_volume
      support outcome.1 lower upper primes strict.le]
  have same : width * singular = width * canonical :=
    tendsto_nhds_unique first original'
  have singular_same : singular = canonical :=
    mul_left_cancel₀ width_positive.ne' same
  simpa [singular_same] using converges

/-- The actual inverse-degree constant-band transfer and its singular-product
limit hold for ONE AND THE SAME genuine positive singular constant.  This is
the source-faithful interface needed to join independently derived
target-truncated first and same-type shared-target second moments. -/
theorem scaleAdaptiveSignedConstantResidueBand_canonicalActualTransfer_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (strict : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto (adaptiveMixedSignedSingularPartialProduct support scale outcome)
        atTop (nhds singular) ∧
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedNormalizedActualTargetVariation
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            index N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, full, _usable, _empty, _density, variation⟩ :=
    scaleAdaptiveSignedConstantResidueBand_actualDegreeTransfer_tendsto_of_GTZ
      green_tao support scale outcome index lower upper primes
      lower_nonnegative strict upper_bounded
  refine ⟨singular, positive, ?_, full, variation⟩
  exact scaleAdaptiveSignedConstantResidueBand_singular_converges_of_fullRelative
    green_tao support scale outcome lower upper singular primes
    lower_nonnegative strict upper_bounded positive full

/-- Deterministic asymptotic transfer on the retained good cell: an ACTUAL
model centered-variance estimate, the already proved inverse-degree target
variation, and bounded normalized genuine target mass imply vanishing actual
centered variance AFTER deleting the separately controlled bad targets.
The model variance here is an explicit input to this transfer lemma, not a
claim that it has been proved from GTZ or a global untruncated conclusion. -/
theorem scaleAdaptiveSignedAdaptiveGoodVariance_tendsto_zero_of_model
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index : ℕ)
    (targets : ℕ → Finset ℕ) (expected : ℕ → ℝ)
    (mean : ℕ → ℕ → ℝ) (bound : ℝ)
    (target_mass_bounded : ∀ᶠ N : ℕ in atTop,
      ((targets N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N ≤ bound)
    (variation : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedNormalizedActualTargetVariation
        support scale outcome domain index N (expected N))
      atTop (nhds (0 : ℝ)))
    (model : Tendsto
      (fun N : ℕ =>
        scaleAdaptivePrimeLabelNormalizedWeight N *
          (∑ target ∈ targets N,
            (scaleAdaptiveSignedUnitModelTargetLoad
              support scale outcome domain index N target (expected N) -
                mean N target) ^ 2))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        scaleAdaptivePrimeLabelNormalizedWeight N *
          (∑ target ∈ scaleAdaptiveSignedUnitGoodTargets
            support scale outcome domain index N (targets N) (expected N)
            (scaleAdaptiveSignedAdaptiveTargetTolerance
              support scale outcome domain index N (expected N)),
            (scaleAdaptiveSignedUnitActualTargetLoad
              support scale outcome domain index N target -
                mean N target) ^ 2))
      atTop (nhds (0 : ℝ)) := by
  have tolerance := scaleAdaptiveSignedAdaptiveTargetTolerance_tendsto_zero
    support scale outcome domain index expected variation
  have squared := tolerance.pow 2
  have upper :
      Tendsto
        (fun N : ℕ =>
          2 * (scaleAdaptivePrimeLabelNormalizedWeight N *
            (∑ target ∈ targets N,
              (scaleAdaptiveSignedUnitModelTargetLoad
                support scale outcome domain index N target (expected N) -
                  mean N target) ^ 2)) +
            (2 * bound) *
              (scaleAdaptiveSignedAdaptiveTargetTolerance
                support scale outcome domain index N (expected N)) ^ 2)
        atTop (nhds (0 : ℝ)) := by
    simpa using (model.const_mul (2 : ℝ)).add
      (squared.const_mul (2 * bound))
  apply squeeze_zero' _ _ upper
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact mul_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      (Finset.sum_nonneg fun _target _ => sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 2, target_mass_bounded]
      with N large bounded
    have finite :=
      scaleAdaptiveSignedUnitGoodTargets_normalizedCenteredVariance_le_model
        support scale outcome domain index N (targets N) (expected N)
        (scaleAdaptiveSignedAdaptiveTargetTolerance
          support scale outcome domain index N (expected N))
        (mean N) large
    have error := mul_le_mul_of_nonneg_right bounded
      (sq_nonneg
        (scaleAdaptiveSignedAdaptiveTargetTolerance
          support scale outcome domain index N (expected N)))
    calc
      _ ≤ 2 * (scaleAdaptivePrimeLabelNormalizedWeight N *
        (∑ target ∈ targets N,
          (scaleAdaptiveSignedUnitModelTargetLoad
            support scale outcome domain index N target (expected N) -
              mean N target) ^ 2)) +
        2 * (((targets N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N) *
            (scaleAdaptiveSignedAdaptiveTargetTolerance
              support scale outcome domain index N (expected N)) ^ 2 :=
        finite
      _ ≤ _ := by nlinarith


end Erdos1139
