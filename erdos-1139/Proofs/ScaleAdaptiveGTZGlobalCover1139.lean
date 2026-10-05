module

public import ScaleAdaptiveColoredEulerAmplification1139
public import ScaleAdaptiveDyadicShellGeometry1139
public import ScaleAdaptiveMultiShellActualLoad1139
public import ScaleAdaptiveGlobalGoodLabelIntersection1139
public import ScaleAdaptiveGlobalMomentConstruction1139

@[expose] public section


/-!
# Genuine shared-prime two-color assembly from fixed signed Green--Tao

The low and high mixed-pattern supports differ even at one physical dyadic
prime-label scale.  Their separate density-one usable-label pools therefore
cannot simply be treated as the same pool.  The construction below forms the
ACTUAL intersection, proves that its removed-prime density vanishes, and
retains nonempty true signed-center fibers for EVERY outcome of BOTH full
finite pattern families.

The resulting finite joint options choose exactly one color and one genuine
residue at each actual prime, with the unavoidable factor `1/2` in both
color-aware hit probabilities.  No covering theorem, global deficit bound,
or original Erdős conclusion is asserted without its missing full-target
classification and actual-conductor/cleanup assembly.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1000000

/-- The union of the ACTUAL low-family and high-family rejected prime
labels at one common physical scale.  Both families keep their distinct
square-core support, full outcome space, and canonical singulars. -/
noncomputable def scaleAdaptiveSignedTwoColorRejectedPrimeLabels
    (lowSupport highSupport : Finset ℕ) (scale : ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) : Finset ℕ :=
  scaleAdaptiveSignedCommonRejectedPrimeLabels
    lowSupport scale (adaptiveMixedOutcomeSpace lowSupport scale)
      lower upper lowSingular N ∪
    scaleAdaptiveSignedCommonRejectedPrimeLabels
      highSupport scale (adaptiveMixedOutcomeSpace highSupport scale)
        lower upper highSingular N

/-- ONE genuine prime-label pool usable SIMULTANEOUSLY by all low and
high mixed-pattern outcomes; it contains no duplicate label or color. -/
noncomputable def scaleAdaptiveSignedTwoColorGoodPrimeLabels
    (lowSupport highSupport : Finset ℕ) (scale : ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) : Finset ℕ :=
  scaleAdaptiveSignedDegreePrimeLabels N \
    scaleAdaptiveSignedTwoColorRejectedPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N

/-- Every prime rejected by either color belongs to the SAME true
physical dyadic prime-label shell. -/
theorem scaleAdaptiveSignedTwoColorRejectedPrimeLabels_subset_pool
    (lowSupport highSupport : Finset ℕ) (scale : ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ) (N : ℕ) :
    scaleAdaptiveSignedTwoColorRejectedPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N ⊆
      scaleAdaptiveSignedDegreePrimeLabels N := by
  intro label selected
  rcases Finset.mem_union.mp selected with low | high
  · exact scaleAdaptiveSignedCommonRejectedPrimeLabels_subset_pool
      lowSupport scale (adaptiveMixedOutcomeSpace lowSupport scale)
        lower upper lowSingular N low
  · exact scaleAdaptiveSignedCommonRejectedPrimeLabels_subset_pool
      highSupport scale (adaptiveMixedOutcomeSpace highSupport scale)
        lower upper highSingular N high

/-- A common good actual label belongs to the genuine one-family LOW pool. -/
theorem scaleAdaptiveSignedTwoColorGoodPrimeLabels_mem_low
    {lowSupport highSupport : Finset ℕ} {scale : ℕ}
    {lower upper : ℝ}
    {lowSingular highSingular : (ℕ × ℕ) → ℝ} {N label : ℕ}
    (good : label ∈ scaleAdaptiveSignedTwoColorGoodPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N) :
    label ∈ scaleAdaptiveSignedCommonGoodPrimeLabels
      lowSupport scale (adaptiveMixedOutcomeSpace lowSupport scale)
        lower upper lowSingular N := by
  obtain ⟨in_pool, not_bad⟩ := Finset.mem_sdiff.mp good
  apply Finset.mem_sdiff.mpr
  refine ⟨in_pool, ?_⟩
  intro rejected
  exact not_bad (Finset.mem_union_left _ rejected)

/-- A common good actual label belongs to the genuine one-family HIGH pool. -/
theorem scaleAdaptiveSignedTwoColorGoodPrimeLabels_mem_high
    {lowSupport highSupport : Finset ℕ} {scale : ℕ}
    {lower upper : ℝ}
    {lowSingular highSingular : (ℕ × ℕ) → ℝ} {N label : ℕ}
    (good : label ∈ scaleAdaptiveSignedTwoColorGoodPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N) :
    label ∈ scaleAdaptiveSignedCommonGoodPrimeLabels
      highSupport scale (adaptiveMixedOutcomeSpace highSupport scale)
        lower upper highSingular N := by
  obtain ⟨in_pool, not_bad⟩ := Finset.mem_sdiff.mp good
  apply Finset.mem_sdiff.mpr
  refine ⟨in_pool, ?_⟩
  intro rejected
  exact not_bad (Finset.mem_union_right _ rejected)

/-- Every retained prime has a NONEMPTY actual signed-center fiber for
every LOW outcome, with its own exact integer edge degree. -/
theorem scaleAdaptiveSignedTwoColorGoodPrimeLabels_low_usable
    {lowSupport highSupport : Finset ℕ} {scale : ℕ}
    {lower upper : ℝ}
    {lowSingular highSingular : (ℕ × ℕ) → ℝ} {N label : ℕ}
    (good : label ∈ scaleAdaptiveSignedTwoColorGoodPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N)
    {outcome : ℕ × ℕ}
    (selected : outcome ∈ adaptiveMixedOutcomeSpace lowSupport scale) :
    (scaleAdaptiveSignedDegreeEdges lowSupport scale outcome
      (scaleAdaptiveSignedConstantResidueBand
        lowSupport outcome.1 lower upper) N label).Nonempty := by
  exact scaleAdaptiveSignedCommonGoodPrimeLabels_usable
    lowSupport scale (adaptiveMixedOutcomeSpace lowSupport scale)
      lower upper lowSingular N label
        (scaleAdaptiveSignedTwoColorGoodPrimeLabels_mem_low good) selected

/-- Every retained prime has a NONEMPTY actual signed-center fiber for
every HIGH outcome at the SAME genuine prime label. -/
theorem scaleAdaptiveSignedTwoColorGoodPrimeLabels_high_usable
    {lowSupport highSupport : Finset ℕ} {scale : ℕ}
    {lower upper : ℝ}
    {lowSingular highSingular : (ℕ × ℕ) → ℝ} {N label : ℕ}
    (good : label ∈ scaleAdaptiveSignedTwoColorGoodPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N)
    {outcome : ℕ × ℕ}
    (selected : outcome ∈ adaptiveMixedOutcomeSpace highSupport scale) :
    (scaleAdaptiveSignedDegreeEdges highSupport scale outcome
      (scaleAdaptiveSignedConstantResidueBand
        highSupport outcome.1 lower upper) N label).Nonempty := by
  exact scaleAdaptiveSignedCommonGoodPrimeLabels_usable
    highSupport scale (adaptiveMixedOutcomeSpace highSupport scale)
      lower upper highSingular N label
        (scaleAdaptiveSignedTwoColorGoodPrimeLabels_mem_high good) selected

/-- A finite union of TWO actual prime-label exceptional families of
vanishing genuine prime-normalized density still has density zero. -/
theorem scaleAdaptiveTwoPrimeLabelBadUnions_normalized_tendsto_zero
    (first second : ℕ → Finset ℕ)
    (first_zero : Tendsto
      (fun N : ℕ => ((first N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ)))
    (second_zero : Tendsto
      (fun N : ℕ => ((second N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => (((first N ∪ second N).card : ℕ) : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ)) := by
  have majorant :
      Tendsto
        (fun N : ℕ =>
          ((first N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N +
          ((second N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) := by
    simpa using first_zero.add second_zero
  apply squeeze_zero' ?_ ?_ majorant
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N large
    exact mul_nonneg (Nat.cast_nonneg _)
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N large
    have cardinal :
        (((first N ∪ second N).card : ℕ) : ℝ) ≤
          ((first N).card : ℝ) + ((second N).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (first N) (second N)
    have weighted := mul_le_mul_of_nonneg_right cardinal
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
    nlinarith

/-- The common TWO-color good-prime intersection retains full genuine
prime-label density whenever both individual rejection densities vanish. -/
theorem scaleAdaptiveSignedTwoColorGoodPrimeLabels_normalized_tendsto_one
    (lowSupport highSupport : Finset ℕ) (scale : ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (rejected : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorGoodPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (1 : ℝ)) := by
  have difference :=
    scaleAdaptiveSignedDegreePrimeLabels_normalizedWeight_tendsto_one.sub
      rejected
  have target :
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N -
            ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              lowSupport highSupport scale lower upper
                lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (1 : ℝ)) := by
    simpa using difference
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp only
    unfold scaleAdaptiveSignedTwoColorGoodPrimeLabels
    rw [Finset.card_sdiff_of_subset
      (scaleAdaptiveSignedTwoColorRejectedPrimeLabels_subset_pool
        lowSupport highSupport scale lower upper
          lowSingular highSingular N),
      Nat.cast_sub (Finset.card_le_card
        (scaleAdaptiveSignedTwoColorRejectedPrimeLabels_subset_pool
          lowSupport highSupport scale lower upper
            lowSingular highSingular N))]
    ring

/-- The ACTUAL full mixed-pattern outcome space is nonempty whenever its
square-core support consists of genuine primes. -/
theorem scaleAdaptiveMixedFullOutcomeSpace_nonempty
    (support : Finset ℕ) (scale : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (adaptiveMixedOutcomeSpace support scale).Nonempty := by
  apply Finset.card_pos.mp
  rw [adaptiveMixedOutcomeSpace_card]
  exact Nat.mul_pos
    (adaptiveMixedTypeModulus_pos support primes)
    (adaptiveMixedOutsideModulus_pos support scale)

/-- Sole source-faithful signed Green--Tao supplies ONE actual dyadic
prime-label pool simultaneously usable by ALL low AND high full mixed
outcomes.  The pool has genuine prime-normalized density one, each color
keeps its distinct canonical positive Euler singular, and no extra label
concentration or covering premise is assumed. -/
theorem scaleAdaptiveSignedTwoColorCommonGoodPrimePool_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (lowSupport highSupport : Finset ℕ) (scale : ℕ)
    (lower upper : ℝ)
    (low_primes : ∀ prime ∈ lowSupport, prime.Prime)
    (high_primes : ∀ prime ∈ highSupport, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ lowSingular highSingular : (ℕ × ℕ) → ℝ,
      (∀ outcome : ℕ × ℕ,
        0 < lowSingular outcome ∧
          Tendsto
            (adaptiveMixedSignedSingularPartialProduct
              lowSupport scale outcome)
            atTop (nhds (lowSingular outcome))) ∧
      (∀ outcome : ℕ × ℕ,
        0 < highSingular outcome ∧
          Tendsto
            (adaptiveMixedSignedSingularPartialProduct
              highSupport scale outcome)
            atTop (nhds (highSingular outcome))) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            lowSupport highSupport scale lower upper
              lowSingular highSingular N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorGoodPrimeLabels
            lowSupport highSupport scale lower upper
              lowSingular highSingular N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (1 : ℝ)) ∧
      (∀ N label,
        label ∈ scaleAdaptiveSignedTwoColorGoodPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N →
        (∀ outcome ∈ adaptiveMixedOutcomeSpace lowSupport scale,
          (scaleAdaptiveSignedDegreeEdges lowSupport scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              lowSupport outcome.1 lower upper) N label).Nonempty) ∧
        (∀ outcome ∈ adaptiveMixedOutcomeSpace highSupport scale,
          (scaleAdaptiveSignedDegreeEdges highSupport scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              highSupport outcome.1 lower upper) N label).Nonempty)) := by
  obtain ⟨lowSingular, low_canonical⟩ :=
    scaleAdaptiveBand_common_outcome_singular_exists_of_GTZ
      green_tao lowSupport scale lower upper low_primes
        lower_nonnegative band_nonempty upper_bounded
  obtain ⟨highSingular, high_canonical⟩ :=
    scaleAdaptiveBand_common_outcome_singular_exists_of_GTZ
      green_tao highSupport scale lower upper high_primes
        lower_nonnegative band_nonempty upper_bounded
  have low_quadratic :
      ∀ outcome ∈ adaptiveMixedOutcomeSpace lowSupport scale,
        Tendsto
          (fun N : ℕ =>
            scaleAdaptiveSignedFullRelativeDegreeError
              lowSupport scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  lowSupport outcome.1 lower upper) N
                (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  lowSupport scale outcome lower upper
                    (lowSingular outcome) N))
          atTop (nhds (0 : ℝ)) := by
    intro outcome _selected
    exact scaleAdaptiveSignedOutcome_fullRelativeDegreeError_of_canonical
      green_tao lowSupport scale outcome lower upper
        (lowSingular outcome) low_primes lower_nonnegative
        band_nonempty upper_bounded (low_canonical outcome).2
  have high_quadratic :
      ∀ outcome ∈ adaptiveMixedOutcomeSpace highSupport scale,
        Tendsto
          (fun N : ℕ =>
            scaleAdaptiveSignedFullRelativeDegreeError
              highSupport scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  highSupport outcome.1 lower upper) N
                (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  highSupport scale outcome lower upper
                    (highSingular outcome) N))
          atTop (nhds (0 : ℝ)) := by
    intro outcome _selected
    exact scaleAdaptiveSignedOutcome_fullRelativeDegreeError_of_canonical
      green_tao highSupport scale outcome lower upper
        (highSingular outcome) high_primes lower_nonnegative
        band_nonempty upper_bounded (high_canonical outcome).2
  have low_rejected :=
    scaleAdaptiveSignedCommonRejectedPrimeLabels_normalized_card_tendsto_zero
      lowSupport scale (adaptiveMixedOutcomeSpace lowSupport scale)
        lower upper lowSingular low_quadratic
  have high_rejected :=
    scaleAdaptiveSignedCommonRejectedPrimeLabels_normalized_card_tendsto_zero
      highSupport scale (adaptiveMixedOutcomeSpace highSupport scale)
        lower upper highSingular high_quadratic
  have rejected :
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            lowSupport highSupport scale lower upper
              lowSingular highSingular N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) := by
    exact scaleAdaptiveTwoPrimeLabelBadUnions_normalized_tendsto_zero
      (scaleAdaptiveSignedCommonRejectedPrimeLabels
        lowSupport scale (adaptiveMixedOutcomeSpace lowSupport scale)
          lower upper lowSingular)
      (scaleAdaptiveSignedCommonRejectedPrimeLabels
        highSupport scale (adaptiveMixedOutcomeSpace highSupport scale)
          lower upper highSingular)
      low_rejected high_rejected
  refine ⟨lowSingular, highSingular, low_canonical, high_canonical,
    rejected, ?_, ?_⟩
  · exact scaleAdaptiveSignedTwoColorGoodPrimeLabels_normalized_tendsto_one
      lowSupport highSupport scale lower upper
        lowSingular highSingular rejected
  · intro N label good
    constructor
    · intro outcome selected
      exact scaleAdaptiveSignedTwoColorGoodPrimeLabels_low_usable
        good selected
    · intro outcome selected
      exact scaleAdaptiveSignedTwoColorGoodPrimeLabels_high_usable
        good selected

/-- The actual inverse-INTEGER-degree physical-target incidence removed
by the UNION of both colors' bad labels, for one genuine family outcome.
Unlike a one-support rejection this also charges labels rejected only by
the OTHER support. -/
noncomputable def scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) (targets : Finset ℕ) : ℝ :=
  ∑ target ∈ targets,
    ∑ label ∈ scaleAdaptiveSignedTwoColorRejectedPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N,
      ∑ center ∈ scaleAdaptiveSignedDegreeEdges
        familySupport scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            familySupport outcome.1 lower upper) N label,
        if scaleAdaptiveSignedOutcomePhysicalHit
          familySupport scale outcome label center target then
          weightedPrimePatternActualEdgeWeight
            (scaleAdaptivePrimeLabelNormalizedWeight N)
            (scaleAdaptiveSignedDegreeEdges
              familySupport scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  familySupport outcome.1 lower upper) N label)
        else 0

/-- Every actual deleted prime label contributes at most ONE normalized
edge unit under true inverse-integer-degree sampling, even when its
rejection came exclusively from the opposite color. -/
theorem scaleAdaptiveSignedTwoColorRejectedActualEdgeMass_le
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) (large : 2 ≤ N) :
    (∑ label ∈ scaleAdaptiveSignedTwoColorRejectedPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N,
      ∑ _center ∈ scaleAdaptiveSignedDegreeEdges
        familySupport scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            familySupport outcome.1 lower upper) N label,
        weightedPrimePatternActualEdgeWeight
          (scaleAdaptivePrimeLabelNormalizedWeight N)
          (scaleAdaptiveSignedDegreeEdges
            familySupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                familySupport outcome.1 lower upper) N label)) ≤
      ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
        lowSupport highSupport scale lower upper
          lowSingular highSingular N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N := by
  calc
    _ ≤ ∑ _label ∈ scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N,
          scaleAdaptivePrimeLabelNormalizedWeight N := by
      apply Finset.sum_le_sum
      intro label _selected
      by_cases nonempty :
          (scaleAdaptiveSignedDegreeEdges
            familySupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                familySupport outcome.1 lower upper) N label).Nonempty
      · rw [weightedPrimePattern_actual_edges_total_mass _ _ nonempty]
      · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
        simp [scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large]
    _ = _ := by simp

/-- Opposite-color label rejection loses at most the TRUE fixed physical
rank times the actual bad-prime normalized mass.  The ambient number of
targets never appears as a spurious multiplier. -/
theorem scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence_le
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) (targets : Finset ℕ) (large : 2 ≤ N) :
    scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
      familySupport lowSupport highSupport scale outcome lower upper
        lowSingular highSingular N targets ≤
      (scale : ℝ) *
        (((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N) := by
  unfold scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
  calc
    _ ≤ (scale : ℝ) *
        (∑ label ∈ scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N,
          ∑ _center ∈ scaleAdaptiveSignedDegreeEdges
            familySupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                familySupport outcome.1 lower upper) N label,
            weightedPrimePatternActualEdgeWeight
              (scaleAdaptivePrimeLabelNormalizedWeight N)
              (scaleAdaptiveSignedDegreeEdges
                familySupport scale outcome
                  (scaleAdaptiveSignedConstantResidueBand
                    familySupport outcome.1 lower upper) N label)) := by
      apply scaleAdaptiveRankWeightedTargetIncidence_le
      · intro label _selected center _in_edges
        unfold weightedPrimePatternActualEdgeWeight weightedPrimePatternDegree
        exact div_nonneg
          (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
          (Nat.cast_nonneg _)
      · intro label _selected center _in_edges
        exact (scaleAdaptiveSignedOutcomePhysicalHit_card_le_rank
          familySupport scale outcome label center targets).trans
            (scaleAdaptiveMixedOutcomeActiveIndices_card_le_scale
              familySupport scale outcome)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (scaleAdaptiveSignedTwoColorRejectedActualEdgeMass_le
        familySupport lowSupport highSupport scale outcome lower upper
          lowSingular highSingular N large)
      (Nat.cast_nonneg _)

/-- For EITHER true family, deleting labels rejected by either support
costs asymptotically ZERO actual inverse-degree physical-target incidence,
uniformly over arbitrary moving finite target sets. -/
theorem scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence_tendsto_zero
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (targets : ℕ → Finset ℕ)
    (rejected : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
          familySupport lowSupport highSupport scale outcome lower upper
            lowSingular highSingular N (targets N))
      atTop (nhds (0 : ℝ)) := by
  have majorant :
      Tendsto
        (fun N : ℕ =>
          (scale : ℝ) *
            (((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              lowSupport highSupport scale lower upper
                lowSingular highSingular N).card : ℝ) *
                  scaleAdaptivePrimeLabelNormalizedWeight N))
        atTop (nhds (0 : ℝ)) := by
    simpa using rejected.const_mul (scale : ℝ)
  apply squeeze_zero' ?_ ?_ majorant
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N large
    unfold scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
    apply Finset.sum_nonneg
    intro target _selected
    apply Finset.sum_nonneg
    intro label _selected
    apply Finset.sum_nonneg
    intro center _selected
    split_ifs with hit
    · unfold weightedPrimePatternActualEdgeWeight weightedPrimePatternDegree
      exact div_nonneg
        (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
        (Nat.cast_nonneg _)
    · exact le_refl 0
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N large
    exact scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence_le
      familySupport lowSupport highSupport scale outcome lower upper
        lowSingular highSingular N (targets N) large

/-- Exact finite fair-color LOW miss bound for the actual signed mixed
sampler.  The exponential contains exactly one factor `1/2` and the true
global-family residue marginals, not separately colored prime pools. -/
theorem scaleAdaptiveSignedJointLowMissFraction_le_exp_neg_half_family
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ)
    (low_patterns_nonempty : ∀ label, (lowPatterns label).Nonempty)
    (high_patterns_nonempty : ∀ label, (highPatterns label).Nonempty)
    (low_edges_nonempty : ∀ label pattern,
      pattern ∈ lowPatterns label →
        (lowEdges label pattern).Nonempty)
    (high_edges_nonempty : ∀ label pattern,
      pattern ∈ highPatterns label →
        (highEdges label pattern).Nonempty) :
    let k := scaleAdaptiveSignedJointOptionCount
      R lowPatterns highPatterns lowEdges highEdges
    let color := scaleAdaptiveSignedJointColor
      R lowPatterns highPatterns lowEdges highEdges
    let residue := scaleAdaptiveSignedJointResidue
      R lowTargets highTargets lowSupport highSupport
        lowPatterns highPatterns lowEdges highEdges
    ((scaleAdaptiveColorMissAssignments
      R color residue false target).card : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ) ≤
      Real.exp
        (-((∑ prime : ↥R,
          independentResidueHitFraction R
            (scaleAdaptiveSignedGlobalFamilyResidue
              R lowTargets lowSupport lowPatterns lowEdges)
            target prime) / 2)) := by
  dsimp only
  have positive := scaleAdaptiveSignedJointOptionCount_pos
    R lowPatterns highPatterns lowEdges highEdges
    low_patterns_nonempty high_patterns_nonempty
    low_edges_nonempty high_edges_nonempty
  have miss := scaleAdaptiveColorMissFraction_le_exp_neg_hit_load
    positive R
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges)
      false target
  have hit := scaleAdaptiveSignedJointHitLoad_low_eq_half
    R lowTargets highTargets lowSupport highSupport
      lowPatterns highPatterns lowEdges highEdges target
        low_patterns_nonempty high_patterns_nonempty
        low_edges_nonempty high_edges_nonempty
  unfold weightedActualPatternHitLoad at hit
  rwa [hit] at miss

/-- Exact finite fair-color HIGH miss bound from the SAME one-prime,
one-color, one-residue signed mixed-pattern sampler. -/
theorem scaleAdaptiveSignedJointHighMissFraction_le_exp_neg_half_family
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ)
    (low_patterns_nonempty : ∀ label, (lowPatterns label).Nonempty)
    (high_patterns_nonempty : ∀ label, (highPatterns label).Nonempty)
    (low_edges_nonempty : ∀ label pattern,
      pattern ∈ lowPatterns label →
        (lowEdges label pattern).Nonempty)
    (high_edges_nonempty : ∀ label pattern,
      pattern ∈ highPatterns label →
        (highEdges label pattern).Nonempty) :
    let k := scaleAdaptiveSignedJointOptionCount
      R lowPatterns highPatterns lowEdges highEdges
    let color := scaleAdaptiveSignedJointColor
      R lowPatterns highPatterns lowEdges highEdges
    let residue := scaleAdaptiveSignedJointResidue
      R lowTargets highTargets lowSupport highSupport
        lowPatterns highPatterns lowEdges highEdges
    ((scaleAdaptiveColorMissAssignments
      R color residue true target).card : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ) ≤
      Real.exp
        (-((∑ prime : ↥R,
          independentResidueHitFraction R
            (scaleAdaptiveSignedGlobalFamilyResidue
              R highTargets highSupport highPatterns highEdges)
            target prime) / 2)) := by
  dsimp only
  have positive := scaleAdaptiveSignedJointOptionCount_pos
    R lowPatterns highPatterns lowEdges highEdges
    low_patterns_nonempty high_patterns_nonempty
    low_edges_nonempty high_edges_nonempty
  have miss := scaleAdaptiveColorMissFraction_le_exp_neg_hit_load
    positive R
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges)
      true target
  have hit := scaleAdaptiveSignedJointHitLoad_high_eq_half
    R lowTargets highTargets lowSupport highSupport
      lowPatterns highPatterns lowEdges highEdges target
        low_patterns_nonempty high_patterns_nonempty
        low_edges_nonempty high_edges_nonempty
  unfold weightedActualPatternHitLoad at hit
  rwa [hit] at miss

/-- Sole signed Green--Tao constructs the GENUINE common-prime-pool joint
low/high sampler on every fixed dyadic shell.  Its full low and high outcome
families use one actual label, one color, one signed-center residue, exact
inverse-INTEGER pattern degrees, and the exact fair probability `1/2`.

The retained prime pool has density one; discarding labels bad for EITHER
support loses zero actual physical-target incidence for BOTH families; all
joint finite option counts are positive; and both independent miss
probabilities satisfy the true fair-color exponential bound.  No global
target-classification, cleanup/conductor, or original-conjecture conclusion
is asserted. -/
theorem scaleAdaptiveSignedTwoColorActualJointSampler_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (lowSupport highSupport : Finset ℕ) (scale : ℕ)
    (lower upper : ℝ)
    (lowTargets highTargets : ℕ → Finset ℕ)
    (low_primes : ∀ prime ∈ lowSupport, prime.Prime)
    (high_primes : ∀ prime ∈ highSupport, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ lowSingular highSingular : (ℕ × ℕ) → ℝ,
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            lowSupport highSupport scale lower upper
              lowSingular highSingular N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorGoodPrimeLabels
            lowSupport highSupport scale lower upper
              lowSingular highSingular N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (1 : ℝ)) ∧
      (∀ outcome : ℕ × ℕ,
        Tendsto
          (fun N : ℕ =>
            scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
              lowSupport lowSupport highSupport scale outcome lower upper
                lowSingular highSingular N (lowTargets N))
          atTop (nhds (0 : ℝ)) ∧
        Tendsto
          (fun N : ℕ =>
            scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
              highSupport lowSupport highSupport scale outcome lower upper
                lowSingular highSingular N (highTargets N))
          atTop (nhds (0 : ℝ))) ∧
      ∀ N : ℕ,
        let R := scaleAdaptiveSignedTwoColorGoodPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N
        let lowFamilySupport : ↥R → Finset ℕ := fun _ => lowSupport
        let highFamilySupport : ↥R → Finset ℕ := fun _ => highSupport
        let lowPatterns : ↥R → Finset (ℕ × ℕ) :=
          fun _ => adaptiveMixedOutcomeSpace lowSupport scale
        let highPatterns : ↥R → Finset (ℕ × ℕ) :=
          fun _ => adaptiveMixedOutcomeSpace highSupport scale
        let lowEdges : ↥R → (ℕ × ℕ) → Finset ℤ :=
          fun prime outcome =>
            scaleAdaptiveSignedDegreeEdges lowSupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                lowSupport outcome.1 lower upper) N prime
        let highEdges : ↥R → (ℕ × ℕ) → Finset ℤ :=
          fun prime outcome =>
            scaleAdaptiveSignedDegreeEdges highSupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                highSupport outcome.1 lower upper) N prime
        let k := scaleAdaptiveSignedJointOptionCount
          R lowPatterns highPatterns lowEdges highEdges
        let color := scaleAdaptiveSignedJointColor
          R lowPatterns highPatterns lowEdges highEdges
        let residue := scaleAdaptiveSignedJointResidue
          R (lowTargets N) (highTargets N)
            lowFamilySupport highFamilySupport
              lowPatterns highPatterns lowEdges highEdges
        0 < k ∧
        WeightedActualPatternOptionsSupported
          R (lowTargets N) (highTargets N) color residue ∧
        (∀ target : ℕ,
          weightedActualPatternHitLoad R color residue false target =
            (∑ prime : ↥R,
              independentResidueHitFraction R
                (scaleAdaptiveSignedGlobalFamilyResidue
                  R (lowTargets N) lowFamilySupport lowPatterns lowEdges)
                target prime) / 2) ∧
        (∀ target : ℕ,
          weightedActualPatternHitLoad R color residue true target =
            (∑ prime : ↥R,
              independentResidueHitFraction R
                (scaleAdaptiveSignedGlobalFamilyResidue
                  R (highTargets N) highFamilySupport highPatterns highEdges)
                target prime) / 2) ∧
        (∀ target : ℕ,
          ((scaleAdaptiveColorMissAssignments
            R color residue false target).card : ℝ) /
              (Fintype.card (↥R → Fin k) : ℝ) ≤
            Real.exp
              (-((∑ prime : ↥R,
                independentResidueHitFraction R
                  (scaleAdaptiveSignedGlobalFamilyResidue
                    R (lowTargets N) lowFamilySupport lowPatterns lowEdges)
                  target prime) / 2))) ∧
        (∀ target : ℕ,
          ((scaleAdaptiveColorMissAssignments
            R color residue true target).card : ℝ) /
              (Fintype.card (↥R → Fin k) : ℝ) ≤
            Real.exp
              (-((∑ prime : ↥R,
                independentResidueHitFraction R
                  (scaleAdaptiveSignedGlobalFamilyResidue
                    R (highTargets N) highFamilySupport highPatterns highEdges)
                  target prime) / 2))) := by
  obtain ⟨lowSingular, highSingular,
      _low_canonical, _high_canonical, rejected, retained, usable⟩ :=
    scaleAdaptiveSignedTwoColorCommonGoodPrimePool_of_GTZ
      green_tao lowSupport highSupport scale lower upper
        low_primes high_primes lower_nonnegative
          band_nonempty upper_bounded
  refine ⟨lowSingular, highSingular, rejected, retained, ?_, ?_⟩
  · intro outcome
    exact ⟨scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence_tendsto_zero
      lowSupport lowSupport highSupport scale outcome lower upper
        lowSingular highSingular lowTargets rejected,
      scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence_tendsto_zero
        highSupport lowSupport highSupport scale outcome lower upper
          lowSingular highSingular highTargets rejected⟩
  · intro N
    dsimp only
    let R := scaleAdaptiveSignedTwoColorGoodPrimeLabels
      lowSupport highSupport scale lower upper
        lowSingular highSingular N
    let lowFamilySupport : ↥R → Finset ℕ := fun _ => lowSupport
    let highFamilySupport : ↥R → Finset ℕ := fun _ => highSupport
    let lowPatterns : ↥R → Finset (ℕ × ℕ) :=
      fun _ => adaptiveMixedOutcomeSpace lowSupport scale
    let highPatterns : ↥R → Finset (ℕ × ℕ) :=
      fun _ => adaptiveMixedOutcomeSpace highSupport scale
    let lowEdges : ↥R → (ℕ × ℕ) → Finset ℤ :=
      fun prime outcome =>
        scaleAdaptiveSignedDegreeEdges lowSupport scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            lowSupport outcome.1 lower upper) N prime
    let highEdges : ↥R → (ℕ × ℕ) → Finset ℤ :=
      fun prime outcome =>
        scaleAdaptiveSignedDegreeEdges highSupport scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            highSupport outcome.1 lower upper) N prime
    have low_patterns : ∀ prime : ↥R, (lowPatterns prime).Nonempty := by
      intro prime
      exact scaleAdaptiveMixedFullOutcomeSpace_nonempty
        lowSupport scale low_primes
    have high_patterns : ∀ prime : ↥R, (highPatterns prime).Nonempty := by
      intro prime
      exact scaleAdaptiveMixedFullOutcomeSpace_nonempty
        highSupport scale high_primes
    have low_edges : ∀ prime : ↥R, ∀ outcome,
        outcome ∈ lowPatterns prime →
          (lowEdges prime outcome).Nonempty := by
      intro prime outcome selected
      exact (usable N prime prime.property).1 outcome selected
    have high_edges : ∀ prime : ↥R, ∀ outcome,
        outcome ∈ highPatterns prime →
          (highEdges prime outcome).Nonempty := by
      intro prime outcome selected
      exact (usable N prime prime.property).2 outcome selected
    refine ⟨scaleAdaptiveSignedJointOptionCount_pos
      R lowPatterns highPatterns lowEdges highEdges
        low_patterns high_patterns low_edges high_edges, ?_, ?_, ?_, ?_, ?_⟩
    · exact scaleAdaptiveSignedJointOptions_supported
        R (lowTargets N) (highTargets N)
          lowFamilySupport highFamilySupport
            lowPatterns highPatterns lowEdges highEdges
    · intro target
      exact scaleAdaptiveSignedJointHitLoad_low_eq_half
        R (lowTargets N) (highTargets N)
          lowFamilySupport highFamilySupport
            lowPatterns highPatterns lowEdges highEdges target
              low_patterns high_patterns low_edges high_edges
    · intro target
      exact scaleAdaptiveSignedJointHitLoad_high_eq_half
        R (lowTargets N) (highTargets N)
          lowFamilySupport highFamilySupport
            lowPatterns highPatterns lowEdges highEdges target
              low_patterns high_patterns low_edges high_edges
    · intro target
      exact scaleAdaptiveSignedJointLowMissFraction_le_exp_neg_half_family
        R (lowTargets N) (highTargets N)
          lowFamilySupport highFamilySupport
            lowPatterns highPatterns lowEdges highEdges target
              low_patterns high_patterns low_edges high_edges
    · intro target
      exact scaleAdaptiveSignedJointHighMissFraction_le_exp_neg_half_family
        R (lowTargets N) (highTargets N)
          lowFamilySupport highFamilySupport
            lowPatterns highPatterns lowEdges highEdges target
              low_patterns high_patterns low_edges high_edges


end Erdos1139
