module

public import ScaleAdaptiveConstantBandTypedGlobalAssembly1139
public import ScaleAdaptiveBandPositiveTargetLoad1139

@[expose] public section


/-!
# One genuine good-prime-label pool for every fixed mixed pattern

For fixed square-core support and scale, finitely many actual signed pattern
outcomes must use ONE common dyadic prime-label pool.  Deleting a zero-density
label subset alone does not control the lost model target incidence: an
exceptional label may have abnormally many genuine signed centers.

This file keeps the actual inverse-integer degree, the true expected degree,
the prime-density weight `log N / N`, and the physical hyperedge rank.  The
common good pool removes the union of the genuine per-outcome quadratic
degree-exceptional sets.  All its labels are simultaneously usable, and the
removed actual AND model edge/target incidences tend to zero using the proved
quadratic errors, not mere label density.  The only analytic premise is the
explicit three-field signed Green--Tao--Ziegler proposition.

The outcome family is fixed before `N → ∞`; no uniform-in-rank or global
multiscale covering conclusion is silently inserted.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1000000

/-- The true signed constant-band degree ratio of one actual mixed outcome at
one genuine dyadic prime label.  Its denominator retains the outcome's
collision-aware singular, square-core modulus, and physical rank. -/
noncomputable def scaleAdaptiveSignedOutcomeDegreeRatio
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ) (N label : ℕ) : ℝ :=
  (scaleAdaptiveSignedDegree support scale outcome
    (scaleAdaptiveSignedConstantResidueBand
      support outcome.1 lower upper) N label : ℝ) /
    scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper singular N

/-- Genuine bad prime labels for ONE actual pattern outcome.  The fixed
threshold `1/2` ensures every remaining label has positive integer degree;
the quadratic threshold is the exact finite Chebyshev event. -/
noncomputable def scaleAdaptiveSignedOutcomeBadPrimeLabels
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ) (N : ℕ) : Finset ℕ :=
  (scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
    (1 / 2 : ℝ) ^ 2 ≤
      (scaleAdaptiveSignedOutcomeDegreeRatio
        support scale outcome lower upper singular N label - 1) ^ 2

/-- The actual finite UNION of bad prime labels across all genuine mixed
pattern outcomes, with one canonical singular for each common outcome. -/
noncomputable def scaleAdaptiveSignedCommonRejectedPrimeLabels
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular : (ℕ × ℕ) → ℝ) (N : ℕ) : Finset ℕ :=
  patterns.biUnion fun outcome =>
    scaleAdaptiveSignedOutcomeBadPrimeLabels
      support scale outcome lower upper (singular outcome) N

/-- ONE source-faithful common prime-label pool simultaneously usable by all
actual signed pattern outcomes.  It is a subset of the real dyadic primes,
not an independently resampled pattern-specific label pool. -/
noncomputable def scaleAdaptiveSignedCommonGoodPrimeLabels
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular : (ℕ × ℕ) → ℝ) (N : ℕ) : Finset ℕ :=
  scaleAdaptiveSignedDegreePrimeLabels N \
    scaleAdaptiveSignedCommonRejectedPrimeLabels
      support scale patterns lower upper singular N

/-- Every genuinely rejected label is still a member of the ACTUAL dyadic
prime-label support. -/
theorem scaleAdaptiveSignedCommonRejectedPrimeLabels_subset_pool
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular : (ℕ × ℕ) → ℝ) (N : ℕ) :
    scaleAdaptiveSignedCommonRejectedPrimeLabels
      support scale patterns lower upper singular N ⊆
        scaleAdaptiveSignedDegreePrimeLabels N := by
  intro label selected
  obtain ⟨outcome, _in_family, bad⟩ := Finset.mem_biUnion.mp selected
  exact (Finset.mem_filter.mp bad).1

/-- One common good label has strict relative degree error below `1/2` for
EVERY actual outcome in the fixed mixed pattern family. -/
theorem scaleAdaptiveSignedCommonGoodPrimeLabels_relative_error_lt
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular : (ℕ × ℕ) → ℝ) (N label : ℕ)
    (good : label ∈ scaleAdaptiveSignedCommonGoodPrimeLabels
      support scale patterns lower upper singular N)
    {outcome : ℕ × ℕ} (selected : outcome ∈ patterns) :
    |scaleAdaptiveSignedOutcomeDegreeRatio
      support scale outcome lower upper (singular outcome) N label - 1| <
      (1 / 2 : ℝ) := by
  obtain ⟨in_pool, not_rejected⟩ := Finset.mem_sdiff.mp good
  have not_bad :
      label ∉ scaleAdaptiveSignedOutcomeBadPrimeLabels
        support scale outcome lower upper (singular outcome) N := by
    intro bad
    exact not_rejected (Finset.mem_biUnion.mpr
      ⟨outcome, selected, bad⟩)
  have square_lt :
      (scaleAdaptiveSignedOutcomeDegreeRatio
        support scale outcome lower upper (singular outcome) N label -
          1) ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    by_contra failed
    exact not_bad (Finset.mem_filter.mpr
      ⟨in_pool, le_of_not_gt failed⟩)
  nlinarith [sq_abs
    (scaleAdaptiveSignedOutcomeDegreeRatio
      support scale outcome lower upper (singular outcome) N label - 1),
    abs_nonneg
      (scaleAdaptiveSignedOutcomeDegreeRatio
        support scale outcome lower upper (singular outcome) N label - 1)]

/-- Every common good prime label has a NONEMPTY actual signed prime-pattern
center fiber for every outcome in the family; division by its integer degree
is therefore legitimate simultaneously. -/
theorem scaleAdaptiveSignedCommonGoodPrimeLabels_usable
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular : (ℕ × ℕ) → ℝ) (N label : ℕ)
    (good : label ∈ scaleAdaptiveSignedCommonGoodPrimeLabels
      support scale patterns lower upper singular N)
    {outcome : ℕ × ℕ} (selected : outcome ∈ patterns) :
    (scaleAdaptiveSignedDegreeEdges support scale outcome
      (scaleAdaptiveSignedConstantResidueBand
        support outcome.1 lower upper) N label).Nonempty := by
  have close := scaleAdaptiveSignedCommonGoodPrimeLabels_relative_error_lt
    support scale patterns lower upper singular N label good selected
  apply Finset.card_ne_zero.mp
  intro empty
  have degree_zero :
      scaleAdaptiveSignedDegree support scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          support outcome.1 lower upper) N label = 0 := empty
  unfold scaleAdaptiveSignedOutcomeDegreeRatio at close
  rw [degree_zero] at close
  norm_num at close

/-- The canonical positive Euler singular of a fixed outcome satisfies the
already proved true full-prime-pool quadratic degree error.  Equality of
singulars follows from their ACTUAL partial-product limits. -/
theorem scaleAdaptiveSignedOutcome_fullRelativeDegreeError_of_canonical
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (canonical : Tendsto
      (adaptiveMixedSignedSingularPartialProduct support scale outcome)
      atTop (nhds singular)) :
    Tendsto
      (fun N : ℕ =>
        scaleAdaptiveSignedFullRelativeDegreeError
          support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper) N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N))
      atTop (nhds (0 : ℝ)) := by
  obtain ⟨other, _positive, converges, quadratic, _variation⟩ :=
    scaleAdaptiveSignedConstantResidueBand_canonicalActualTransfer_of_GTZ
      green_tao support scale outcome 0 lower upper primes
        lower_nonnegative band_nonempty upper_bounded
  have same := tendsto_nhds_unique canonical converges
  subst other
  exact quadratic

/-- Exact normalization identity for one actual outcome's full prime-label
quadratic degree error.  The genuine prime weight is not dropped. -/
theorem scaleAdaptiveSignedOutcome_fullRelativeDegreeError_eq
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ) (N : ℕ) :
    scaleAdaptiveSignedFullRelativeDegreeError
      support scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          support outcome.1 lower upper) N
        (scaleAdaptiveSignedConstantResidueBandExpectedDegree
          support scale outcome lower upper singular N) =
      scaleAdaptivePrimeLabelNormalizedWeight N *
        (∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
          (scaleAdaptiveSignedOutcomeDegreeRatio
            support scale outcome lower upper singular N label - 1) ^ 2) := by
  unfold scaleAdaptiveSignedFullRelativeDegreeError
    scaleAdaptiveWeightedDegreeQuadraticError
    scaleAdaptiveSignedOutcomeDegreeRatio
  rw [Finset.mul_sum]

/-- Source-faithful finite Chebyshev for one outcome's actual bad PRIME
labels, using the already proved true weighted degree quadratic error. -/
theorem scaleAdaptiveSignedOutcomeBadPrimeLabels_normalized_card_le
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ) (N : ℕ) (large : 2 ≤ N) :
    ((scaleAdaptiveSignedOutcomeBadPrimeLabels
      support scale outcome lower upper singular N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N ≤
      4 * scaleAdaptiveSignedFullRelativeDegreeError
        support scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            support outcome.1 lower upper) N
          (scaleAdaptiveSignedConstantResidueBandExpectedDegree
            support scale outcome lower upper singular N) := by
  have finite := weightedPrimePattern_exceptional_card_mul_threshold_sq_le
    (scaleAdaptiveSignedDegreePrimeLabels N)
    (scaleAdaptiveSignedOutcomeDegreeRatio
      support scale outcome lower upper singular N)
    (1 / 2 : ℝ)
  change
    ((scaleAdaptiveSignedOutcomeBadPrimeLabels
      support scale outcome lower upper singular N).card : ℝ) *
      (1 / 2 : ℝ) ^ 2 ≤ _ at finite
  have weighted := mul_le_mul_of_nonneg_right finite
    (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  rw [scaleAdaptiveSignedOutcome_fullRelativeDegreeError_eq]
  nlinarith

/-- The actual prime-scale density of one pattern's bad labels tends to zero
directly from its true full-prime-pool quadratic degree estimate. -/
theorem scaleAdaptiveSignedOutcomeBadPrimeLabels_normalized_card_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ)
    (quadratic :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedOutcomeBadPrimeLabels
          support scale outcome lower upper singular N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ)) := by
  have majorant :
      Tendsto
        (fun N : ℕ =>
          4 * scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ)) := by
    simpa using quadratic.const_mul (4 : ℝ)
  apply squeeze_zero' _ _ majorant
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact mul_nonneg (Nat.cast_nonneg _)
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact scaleAdaptiveSignedOutcomeBadPrimeLabels_normalized_card_le
      support scale outcome lower upper singular N large

/-- The finite UNION of genuine outcome-specific bad prime labels has zero
true prime-scale density.  The outcome family is fixed before the limit. -/
theorem scaleAdaptiveSignedCommonRejectedPrimeLabels_normalized_card_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular : (ℕ × ℕ) → ℝ)
    (quadratic : ∀ outcome ∈ patterns,
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper (singular outcome) N))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedCommonRejectedPrimeLabels
          support scale patterns lower upper singular N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ)) := by
  have union := scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
    patterns
    (fun outcome N => scaleAdaptiveSignedOutcomeBadPrimeLabels
      support scale outcome lower upper (singular outcome) N)
    (by
      intro outcome selected
      have limit :=
        scaleAdaptiveSignedOutcomeBadPrimeLabels_normalized_card_tendsto_zero
          support scale outcome lower upper (singular outcome)
            (quadratic outcome selected)
      simpa [scaleAdaptivePrimeLabelNormalizedWeight,
        div_eq_mul_inv, mul_assoc] using limit)
  simpa [scaleAdaptiveSignedCommonRejectedPrimeLabels,
    scaleAdaptivePrimeLabelNormalizedWeight,
    div_eq_mul_inv, mul_assoc] using union

/-- ONE common actual prime-label pool for the entire fixed mixed family has
normalized density ONE; no independent pattern-wise prime pools remain. -/
theorem scaleAdaptiveSignedCommonGoodPrimeLabels_normalized_card_tendsto_one
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular : (ℕ × ℕ) → ℝ)
    (quadratic : ∀ outcome ∈ patterns,
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper (singular outcome) N))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedCommonGoodPrimeLabels
          support scale patterns lower upper singular N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (1 : ℝ)) := by
  have bad :=
    scaleAdaptiveSignedCommonRejectedPrimeLabels_normalized_card_tendsto_zero
      support scale patterns lower upper singular quadratic
  have difference :=
    scaleAdaptiveSignedDegreePrimeLabels_normalizedWeight_tendsto_one.sub bad
  have target :
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N -
            ((scaleAdaptiveSignedCommonRejectedPrimeLabels
              support scale patterns lower upper singular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (1 : ℝ)) := by
    simpa using difference
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp only
    unfold scaleAdaptiveSignedCommonGoodPrimeLabels
    rw [Finset.card_sdiff_of_subset
      (scaleAdaptiveSignedCommonRejectedPrimeLabels_subset_pool
        support scale patterns lower upper singular N),
      Nat.cast_sub (Finset.card_le_card
        (scaleAdaptiveSignedCommonRejectedPrimeLabels_subset_pool
          support scale patterns lower upper singular N))]
    ring_nf

/-- Total ACTUAL inverse-INTEGER-degree pattern edge mass removed by the
common-label intersection, with the true prime-density weight. -/
noncomputable def scaleAdaptiveSignedCommonRejectedActualEdgeMass
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (N : ℕ) : ℝ :=
  ∑ label ∈ scaleAdaptiveSignedCommonRejectedPrimeLabels
      support scale patterns lower upper singular N,
    ∑ _center ∈ scaleAdaptiveSignedDegreeEdges
        support scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            support outcome.1 lower upper) N label,
      weightedPrimePatternActualEdgeWeight
        (scaleAdaptivePrimeLabelNormalizedWeight N)
        (scaleAdaptiveSignedDegreeEdges
          support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper) N label)

/-- Total expected-degree MODEL edge mass removed at the same actual rejected
prime labels.  Unlike actual inverse-degree mass, this retains the true
possibly large degree ratio and cannot be controlled by label density alone.
-/
noncomputable def scaleAdaptiveSignedCommonRejectedModelEdgeMass
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (N : ℕ) : ℝ :=
  ∑ label ∈ scaleAdaptiveSignedCommonRejectedPrimeLabels
      support scale patterns lower upper singular N,
    ∑ _center ∈ scaleAdaptiveSignedDegreeEdges
        support scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            support outcome.1 lower upper) N label,
      scaleAdaptivePrimeLabelNormalizedWeight N /
        scaleAdaptiveSignedConstantResidueBandExpectedDegree
          support scale outcome lower upper (singular outcome) N

/-- Every genuinely nonempty deleted actual prime-label fiber contributes
exactly ONE prime-density weight under inverse-integer-degree sampling;
empty fibers contribute zero. -/
theorem scaleAdaptiveSignedCommonRejectedActualEdgeMass_le
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (N : ℕ) (large : 2 ≤ N) :
    scaleAdaptiveSignedCommonRejectedActualEdgeMass
      support scale patterns outcome lower upper singular N ≤
      ((scaleAdaptiveSignedCommonRejectedPrimeLabels
        support scale patterns lower upper singular N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N := by
  unfold scaleAdaptiveSignedCommonRejectedActualEdgeMass
  calc
    _ ≤ ∑ _label ∈ scaleAdaptiveSignedCommonRejectedPrimeLabels
          support scale patterns lower upper singular N,
            scaleAdaptivePrimeLabelNormalizedWeight N := by
      apply Finset.sum_le_sum
      intro label _selected
      by_cases nonempty :
          (scaleAdaptiveSignedDegreeEdges support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper) N label).Nonempty
      · rw [weightedPrimePattern_actual_edges_total_mass _ _ nonempty]
      · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
        simp [scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large]
    _ = _ := by simp

/-- The deleted MODEL edge mass is controlled by BOTH bad-label density and
the actual outcome's FULL quadratic degree error.  This is the essential
anti-concentration term omitted by a label-density-only argument. -/
theorem scaleAdaptiveSignedCommonRejectedModelEdgeMass_le
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (N : ℕ) (large : 2 ≤ N) :
    scaleAdaptiveSignedCommonRejectedModelEdgeMass
      support scale patterns outcome lower upper singular N ≤
      2 * ((scaleAdaptiveSignedCommonRejectedPrimeLabels
        support scale patterns lower upper singular N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N +
        scaleAdaptiveSignedFullRelativeDegreeError
          support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper) N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper (singular outcome) N) := by
  have finite := weightedPrimePattern_exceptional_model_edge_mass_le
    (scaleAdaptiveSignedDegreePrimeLabels N)
    (scaleAdaptiveSignedCommonRejectedPrimeLabels
      support scale patterns lower upper singular N)
    (fun label => scaleAdaptiveSignedDegreeEdges
      support scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          support outcome.1 lower upper) N label)
    (fun _label => scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper (singular outcome) N)
    (scaleAdaptivePrimeLabelNormalizedWeight N)
    (scaleAdaptiveSignedCommonRejectedPrimeLabels_subset_pool
      support scale patterns lower upper singular N)
    (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  change scaleAdaptiveSignedCommonRejectedModelEdgeMass
    support scale patterns outcome lower upper singular N ≤ _ at finite
  rw [scaleAdaptiveSignedOutcome_fullRelativeDegreeError_eq]
  convert finite using 1
  unfold scaleAdaptiveSignedOutcomeDegreeRatio scaleAdaptiveSignedDegree
  ring

/-- At every genuine large scale the actual full-band expected degree is
strictly positive for a positive canonical singular. -/
theorem scaleAdaptiveSignedConstantResidueBandExpectedDegree_pos_of_large
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ) (N : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (band_nonempty : lower < upper)
    (singular_positive : 0 < singular)
    (large : 2 ≤ N) :
    0 < scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper singular N := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have N_positive : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have log_positive : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  unfold scaleAdaptiveSignedConstantResidueBandExpectedDegree
  exact div_pos
    (mul_pos
      (mul_pos (div_pos (sub_pos.mpr band_nonempty) modulus_positive)
        singular_positive)
      N_positive)
    (pow_pos log_positive _)

/-- The actual inverse-integer-degree edge incidence discarded by the COMMON
good-label intersection has genuinely vanishing prime-normalized mass. -/
theorem scaleAdaptiveSignedCommonRejectedActualEdgeMass_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ)
    (bad : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedCommonRejectedPrimeLabels
          support scale patterns lower upper singular N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedCommonRejectedActualEdgeMass
        support scale patterns outcome lower upper singular N)
      atTop (nhds (0 : ℝ)) := by
  apply squeeze_zero' _ _ bad
  · filter_upwards [eventually_ge_atTop 2] with N large
    unfold scaleAdaptiveSignedCommonRejectedActualEdgeMass
    apply Finset.sum_nonneg
    intro label _selected
    apply Finset.sum_nonneg
    intro center _selected
    unfold weightedPrimePatternActualEdgeWeight weightedPrimePatternDegree
    exact div_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact scaleAdaptiveSignedCommonRejectedActualEdgeMass_le
      support scale patterns outcome lower upper singular N large

/-- The deleted MODEL prime-edge incidence also vanishes.  Its proof retains
BOTH genuine common-bad-label mass and the actual full quadratic degree
error, rather than inferring model incidence from label density. -/
theorem scaleAdaptiveSignedCommonRejectedModelEdgeMass_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (band_nonempty : lower < upper)
    (singular_positive : 0 < singular outcome)
    (bad : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedCommonRejectedPrimeLabels
          support scale patterns lower upper singular N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ)))
    (quadratic :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper (singular outcome) N))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedCommonRejectedModelEdgeMass
        support scale patterns outcome lower upper singular N)
      atTop (nhds (0 : ℝ)) := by
  have majorant := (bad.const_mul (2 : ℝ)).add quadratic
  have target :
      Tendsto
        (fun N : ℕ =>
          2 * ((scaleAdaptiveSignedCommonRejectedPrimeLabels
            support scale patterns lower upper singular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N +
            scaleAdaptiveSignedFullRelativeDegreeError
              support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N
                (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper (singular outcome) N))
        atTop (nhds (0 : ℝ)) := by
    simpa [mul_assoc] using majorant
  apply squeeze_zero' _ _ target
  · filter_upwards [eventually_ge_atTop 2] with N large
    unfold scaleAdaptiveSignedCommonRejectedModelEdgeMass
    apply Finset.sum_nonneg
    intro label _selected
    apply Finset.sum_nonneg
    intro center _selected
    exact div_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      (scaleAdaptiveSignedConstantResidueBandExpectedDegree_pos_of_large
        support scale outcome lower upper (singular outcome) N
        primes band_nonempty singular_positive large).le
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact scaleAdaptiveSignedCommonRejectedModelEdgeMass_le
      support scale patterns outcome lower upper singular N large

/-- The genuine physical target-hit predicate of one ACTUAL signed center:
the target must equal `i*p+r` at one of its true retained mixed indices. -/
noncomputable def scaleAdaptiveSignedOutcomePhysicalHit
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (label : ℕ) (center : ℤ) (target : ℕ) : Bool :=
  decide (∃ index ∈ adaptiveMixedOutcomeActiveIndices
    support scale outcome,
      target = scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index label center)

/-- Every genuine signed prime-pattern edge hits at most its TRUE actual
retained mixed rank, uniformly over every finite physical target set. -/
theorem scaleAdaptiveSignedOutcomePhysicalHit_card_le_rank
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (label : ℕ) (center : ℤ) (targets : Finset ℕ) :
    (targets.filter fun target =>
      scaleAdaptiveSignedOutcomePhysicalHit
        support scale outcome label center target).card ≤
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card := by
  classical
  have subset :
      (targets.filter fun target =>
        scaleAdaptiveSignedOutcomePhysicalHit
          support scale outcome label center target) ⊆
        (adaptiveMixedOutcomeActiveIndices support scale outcome).image
          (fun index => scaleAdaptiveGTZIndexedPhysicalTarget
            support outcome.1 index label center) := by
    intro target selected
    obtain ⟨_in_targets, hits⟩ := Finset.mem_filter.mp selected
    have witness :
        ∃ index ∈ adaptiveMixedOutcomeActiveIndices
          support scale outcome,
            target = scaleAdaptiveGTZIndexedPhysicalTarget
              support outcome.1 index label center := by
      simpa [scaleAdaptiveSignedOutcomePhysicalHit] using hits
    obtain ⟨index, active, equal⟩ := witness
    exact Finset.mem_image.mpr ⟨index, active, equal.symm⟩
  exact (Finset.card_le_card subset).trans Finset.card_image_le

/-- Every actual mixed pattern's physical target rank is at most its genuine
positive-index scale; no ambient target cardinality is substituted. -/
theorem scaleAdaptiveMixedOutcomeActiveIndices_card_le_scale
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) :
    (adaptiveMixedOutcomeActiveIndices support scale outcome).card ≤ scale := by
  have subset :
      adaptiveMixedOutcomeActiveIndices support scale outcome ⊆
        Finset.Icc 1 scale := by
    intro index active
    exact adaptiveMixedOutcomeActiveIndices_subset_physical
      support scale outcome active
  have bound := Finset.card_le_card subset
  simpa using bound

/-- Honest finite rank-weighted target-incidence control.  Arbitrarily many
ambient targets cannot multiply the error: each actual edge contributes to at
most its genuine physical rank. -/
theorem scaleAdaptiveRankWeightedTargetIncidence_le
    {α : Type*} (labels targets : Finset ℕ)
    (edges : ℕ → Finset α) (hits : ℕ → α → ℕ → Bool)
    (weight : ℕ → α → ℝ) (rank : ℕ)
    (nonnegative : ∀ label ∈ labels, ∀ center ∈ edges label,
      0 ≤ weight label center)
    (rank_bound : ∀ label ∈ labels, ∀ center ∈ edges label,
      (targets.filter fun target => hits label center target).card ≤ rank) :
    (∑ target ∈ targets, ∑ label ∈ labels, ∑ center ∈ edges label,
      if hits label center target then weight label center else 0) ≤
      (rank : ℝ) *
        (∑ label ∈ labels, ∑ center ∈ edges label,
          weight label center) := by
  classical
  calc
    _ = ∑ label ∈ labels, ∑ center ∈ edges label,
          (((targets.filter fun target =>
            hits label center target).card : ℕ) : ℝ) *
              weight label center := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro label _selected
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro center _selected
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ label ∈ labels, ∑ center ∈ edges label,
          (rank : ℝ) * weight label center := by
      apply Finset.sum_le_sum
      intro label selected
      apply Finset.sum_le_sum
      intro center in_edges
      apply mul_le_mul_of_nonneg_right _
        (nonnegative label selected center in_edges)
      exact_mod_cast rank_bound label selected center in_edges
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro label _selected
      rw [Finset.mul_sum]

/-- The ACTUAL inverse-integer-degree total physical target incidence removed
with the common bad labels.  Every edge is charged only at its genuine active
mixed target indices. -/
noncomputable def scaleAdaptiveSignedCommonRejectedActualTargetIncidence
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (N : ℕ) (targets : Finset ℕ) : ℝ :=
  ∑ target ∈ targets,
    ∑ label ∈ scaleAdaptiveSignedCommonRejectedPrimeLabels
      support scale patterns lower upper singular N,
      ∑ center ∈ scaleAdaptiveSignedDegreeEdges
        support scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            support outcome.1 lower upper) N label,
        if scaleAdaptiveSignedOutcomePhysicalHit
          support scale outcome label center target then
          weightedPrimePatternActualEdgeWeight
            (scaleAdaptivePrimeLabelNormalizedWeight N)
            (scaleAdaptiveSignedDegreeEdges
              support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label)
        else 0

/-- The parallel true EXPECTED-degree physical target incidence removed at
the same common bad prime labels; its degree ratio is retained explicitly. -/
noncomputable def scaleAdaptiveSignedCommonRejectedModelTargetIncidence
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (N : ℕ) (targets : Finset ℕ) : ℝ :=
  ∑ target ∈ targets,
    ∑ label ∈ scaleAdaptiveSignedCommonRejectedPrimeLabels
      support scale patterns lower upper singular N,
      ∑ center ∈ scaleAdaptiveSignedDegreeEdges
        support scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            support outcome.1 lower upper) N label,
        if scaleAdaptiveSignedOutcomePhysicalHit
          support scale outcome label center target then
          scaleAdaptivePrimeLabelNormalizedWeight N /
            scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper (singular outcome) N
        else 0

/-- Deleted genuine inverse-integer-degree target incidence is at most the
TRUE outcome rank times its deleted actual edge mass. -/
theorem scaleAdaptiveSignedCommonRejectedActualTargetIncidence_le
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (N : ℕ) (targets : Finset ℕ)
    (large : 2 ≤ N) :
    scaleAdaptiveSignedCommonRejectedActualTargetIncidence
      support scale patterns outcome lower upper singular N targets ≤
      ((adaptiveMixedOutcomeActiveIndices
        support scale outcome).card : ℝ) *
        scaleAdaptiveSignedCommonRejectedActualEdgeMass
          support scale patterns outcome lower upper singular N := by
  unfold scaleAdaptiveSignedCommonRejectedActualTargetIncidence
    scaleAdaptiveSignedCommonRejectedActualEdgeMass
  apply scaleAdaptiveRankWeightedTargetIncidence_le
  · intro label _selected center _in_edges
    unfold weightedPrimePatternActualEdgeWeight weightedPrimePatternDegree
    exact div_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      (Nat.cast_nonneg _)
  · intro label _selected center _in_edges
    exact scaleAdaptiveSignedOutcomePhysicalHit_card_le_rank
      support scale outcome label center targets

/-- Deleted genuine expected-degree target incidence is bounded by the TRUE
outcome rank times its degree-sensitive deleted model edge mass. -/
theorem scaleAdaptiveSignedCommonRejectedModelTargetIncidence_le
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (N : ℕ) (targets : Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (band_nonempty : lower < upper)
    (singular_positive : 0 < singular outcome)
    (large : 2 ≤ N) :
    scaleAdaptiveSignedCommonRejectedModelTargetIncidence
      support scale patterns outcome lower upper singular N targets ≤
      ((adaptiveMixedOutcomeActiveIndices
        support scale outcome).card : ℝ) *
        scaleAdaptiveSignedCommonRejectedModelEdgeMass
          support scale patterns outcome lower upper singular N := by
  unfold scaleAdaptiveSignedCommonRejectedModelTargetIncidence
    scaleAdaptiveSignedCommonRejectedModelEdgeMass
  apply scaleAdaptiveRankWeightedTargetIncidence_le
  · intro label _selected center _in_edges
    exact div_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      (scaleAdaptiveSignedConstantResidueBandExpectedDegree_pos_of_large
        support scale outcome lower upper (singular outcome) N
        primes band_nonempty singular_positive large).le
  · intro label _selected center _in_edges
    exact scaleAdaptiveSignedOutcomePhysicalHit_card_le_rank
      support scale outcome label center targets

/-- Removing the common bad labels loses asymptotically ZERO actual
inverse-integer-degree physical target incidence, for arbitrary moving
finite target sets and with the exact active-index rank. -/
theorem scaleAdaptiveSignedCommonRejectedActualTargetIncidence_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (targets : ℕ → Finset ℕ)
    (edges : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedCommonRejectedActualEdgeMass
        support scale patterns outcome lower upper singular N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedCommonRejectedActualTargetIncidence
        support scale patterns outcome lower upper singular N (targets N))
      atTop (nhds (0 : ℝ)) := by
  have majorant :
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedOutcomeActiveIndices
            support scale outcome).card : ℝ) *
            scaleAdaptiveSignedCommonRejectedActualEdgeMass
              support scale patterns outcome lower upper singular N)
        atTop (nhds (0 : ℝ)) := by
    simpa using edges.const_mul
      ((adaptiveMixedOutcomeActiveIndices support scale outcome).card : ℝ)
  apply squeeze_zero' _ _ majorant
  · filter_upwards [eventually_ge_atTop 2] with N large
    unfold scaleAdaptiveSignedCommonRejectedActualTargetIncidence
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
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact scaleAdaptiveSignedCommonRejectedActualTargetIncidence_le
      support scale patterns outcome lower upper singular N (targets N) large

/-- Removing the same common bad labels also loses asymptotically ZERO true
expected-degree MODEL target incidence.  The required degree-sensitive
exceptional-edge estimate and physical rank are both retained. -/
theorem scaleAdaptiveSignedCommonRejectedModelTargetIncidence_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ) (targets : ℕ → Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (band_nonempty : lower < upper)
    (singular_positive : 0 < singular outcome)
    (edges : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedCommonRejectedModelEdgeMass
        support scale patterns outcome lower upper singular N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedCommonRejectedModelTargetIncidence
        support scale patterns outcome lower upper singular N (targets N))
      atTop (nhds (0 : ℝ)) := by
  have majorant :
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedOutcomeActiveIndices
            support scale outcome).card : ℝ) *
            scaleAdaptiveSignedCommonRejectedModelEdgeMass
              support scale patterns outcome lower upper singular N)
        atTop (nhds (0 : ℝ)) := by
    simpa using edges.const_mul
      ((adaptiveMixedOutcomeActiveIndices support scale outcome).card : ℝ)
  apply squeeze_zero' _ _ majorant
  · filter_upwards [eventually_ge_atTop 2] with N large
    unfold scaleAdaptiveSignedCommonRejectedModelTargetIncidence
    apply Finset.sum_nonneg
    intro target _selected
    apply Finset.sum_nonneg
    intro label _selected
    apply Finset.sum_nonneg
    intro center _selected
    split_ifs with hit
    · exact div_nonneg
        (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
        (scaleAdaptiveSignedConstantResidueBandExpectedDegree_pos_of_large
          support scale outcome lower upper (singular outcome) N
          primes band_nonempty singular_positive large).le
    · exact le_refl 0
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact scaleAdaptiveSignedCommonRejectedModelTargetIncidence_le
      support scale patterns outcome lower upper singular N (targets N)
      primes band_nonempty singular_positive large

/-- The genuine full-prime-pool degree residual for one outcome, with the
true prime normalization and expected signed constant-band degree. -/
noncomputable def scaleAdaptiveSignedOutcomeNormalizedDegreeResidual
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ) (N : ℕ) : ℝ :=
  scaleAdaptiveWeightedDegreeResidual
    (scaleAdaptiveSignedDegreePrimeLabels N)
    (fun label =>
      (scaleAdaptiveSignedDegree support scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          support outcome.1 lower upper) N label : ℝ))
    (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
    (fun _ => scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper singular N)

/-- True weighted Cauchy and the ordinary dyadic PNT convert the ACTUAL
quadratic degree error into vanishing normalized linear degree residual. -/
theorem scaleAdaptiveSignedOutcomeNormalizedDegreeResidual_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ)
    (quadratic :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedOutcomeNormalizedDegreeResidual
        support scale outcome lower upper singular N)
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
              support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N
                (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper singular N)))
        atTop (nhds (0 : ℝ)) := by
    simpa using product.sqrt
  apply squeeze_zero' _ _ root
  · filter_upwards [eventually_ge_atTop 2] with N large
    unfold scaleAdaptiveSignedOutcomeNormalizedDegreeResidual
    apply scaleAdaptiveWeightedDegreeResidual_nonnegative
    intro label _selected
    exact scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
  · filter_upwards [eventually_ge_atTop 2] with N large
    have bound := scaleAdaptiveWeightedDegreeResidual_le_sqrt
      (scaleAdaptiveSignedDegreePrimeLabels N)
      (fun label =>
        (scaleAdaptiveSignedDegree support scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            support outcome.1 lower upper) N label : ℝ))
      (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
      (fun _ => scaleAdaptiveSignedConstantResidueBandExpectedDegree
        support scale outcome lower upper singular N)
      (fun _label _selected =>
        scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
    simpa [scaleAdaptiveSignedOutcomeNormalizedDegreeResidual,
      scaleAdaptiveSignedFullRelativeDegreeError,
      Finset.sum_const, nsmul_eq_mul] using bound

/-- The complete physical-target total variation of the TRUE common-label
pattern mixture, with outcome masses, actual inverse-integer signed degrees,
expected signed degrees, genuine active-index hits, and prime normalization.
-/
noncomputable def scaleAdaptiveSignedCommonGoodMixtureTargetVariation
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular mass : (ℕ × ℕ) → ℝ)
    (N : ℕ) (targets : Finset ℕ) : ℝ :=
  scaleAdaptivePrimeLabelNormalizedWeight N *
    ∑ label ∈ scaleAdaptiveSignedCommonGoodPrimeLabels
      support scale patterns lower upper singular N,
      ∑ target ∈ targets,
        |(∑ outcome ∈ patterns,
            ∑ center ∈ scaleAdaptiveSignedDegreeEdges
              support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label,
              if scaleAdaptiveSignedOutcomePhysicalHit
                support scale outcome label center target then
                weightedPrimePatternActualEdgeWeight (mass outcome)
                  (scaleAdaptiveSignedDegreeEdges
                    support scale outcome
                      (scaleAdaptiveSignedConstantResidueBand
                        support outcome.1 lower upper) N label)
              else 0) -
          (∑ outcome ∈ patterns,
            ∑ center ∈ scaleAdaptiveSignedDegreeEdges
              support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label,
              if scaleAdaptiveSignedOutcomePhysicalHit
                support scale outcome label center target then
                mass outcome /
                  scaleAdaptiveSignedConstantResidueBandExpectedDegree
                    support scale outcome lower upper
                      (singular outcome) N
              else 0)|

/-- The full common-label actual/model target-mixture variation is bounded
by the TRUE physical rank times the SUM of actual outcome degree residuals.
The proof applies `weightedPrimePattern_good_label_total_target_error_le`
at each genuine common prime label; it never pays the ambient target count.
-/
theorem scaleAdaptiveSignedCommonGoodMixtureTargetVariation_le_residuals
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular mass : (ℕ × ℕ) → ℝ)
    (N : ℕ) (targets : Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (band_nonempty : lower < upper)
    (singular_positive : ∀ outcome ∈ patterns, 0 < singular outcome)
    (mass_nonnegative : ∀ outcome ∈ patterns, 0 ≤ mass outcome)
    (normalized : ∑ outcome ∈ patterns, mass outcome = 1)
    (large : 2 ≤ N) :
    scaleAdaptiveSignedCommonGoodMixtureTargetVariation
      support scale patterns lower upper singular mass N targets ≤
      (scale : ℝ) *
        ∑ outcome ∈ patterns,
          scaleAdaptiveSignedOutcomeNormalizedDegreeResidual
            support scale outcome lower upper (singular outcome) N := by
  classical
  let good := scaleAdaptiveSignedCommonGoodPrimeLabels
    support scale patterns lower upper singular N
  have weight_nonnegative :=
    scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
  have individual : ∀ label ∈ good,
      (∑ target ∈ targets,
        |(∑ outcome ∈ patterns,
            ∑ center ∈ scaleAdaptiveSignedDegreeEdges
              support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label,
              if scaleAdaptiveSignedOutcomePhysicalHit
                support scale outcome label center target then
                weightedPrimePatternActualEdgeWeight (mass outcome)
                  (scaleAdaptiveSignedDegreeEdges
                    support scale outcome
                      (scaleAdaptiveSignedConstantResidueBand
                        support outcome.1 lower upper) N label)
              else 0) -
          (∑ outcome ∈ patterns,
            ∑ center ∈ scaleAdaptiveSignedDegreeEdges
              support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label,
              if scaleAdaptiveSignedOutcomePhysicalHit
                support scale outcome label center target then
                mass outcome /
                  scaleAdaptiveSignedConstantResidueBandExpectedDegree
                    support scale outcome lower upper
                      (singular outcome) N
              else 0)|) ≤
        (scale : ℝ) *
          ∑ outcome ∈ patterns,
            |scaleAdaptiveSignedOutcomeDegreeRatio
              support scale outcome lower upper
                (singular outcome) N label - 1| := by
    intro label selected
    apply weightedPrimePattern_good_label_total_target_error_le
      patterns targets mass
      (fun outcome => scaleAdaptiveSignedConstantResidueBandExpectedDegree
        support scale outcome lower upper (singular outcome) N)
      (fun outcome => scaleAdaptiveSignedDegreeEdges
        support scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            support outcome.1 lower upper) N label)
      (fun outcome center target => scaleAdaptiveSignedOutcomePhysicalHit
        support scale outcome label center target)
      scale
      (∑ outcome ∈ patterns,
        |scaleAdaptiveSignedOutcomeDegreeRatio
          support scale outcome lower upper
            (singular outcome) N label - 1|)
    · exact mass_nonnegative
    · intro outcome in_family
      exact scaleAdaptiveSignedCommonGoodPrimeLabels_usable
        support scale patterns lower upper singular N label
          selected in_family
    · intro outcome in_family
      exact
        (scaleAdaptiveSignedConstantResidueBandExpectedDegree_pos_of_large
          support scale outcome lower upper (singular outcome) N
          primes band_nonempty (singular_positive outcome in_family)
          large).ne'
    · intro outcome in_family
      change
        |scaleAdaptiveSignedOutcomeDegreeRatio
          support scale outcome lower upper
            (singular outcome) N label - 1| ≤ _
      exact Finset.single_le_sum
        (f := fun other =>
          |scaleAdaptiveSignedOutcomeDegreeRatio
            support scale other lower upper
              (singular other) N label - 1|)
        (fun _outcome _selected => abs_nonneg _) in_family
    · exact normalized
    · intro outcome _in_family center _selected
      exact (scaleAdaptiveSignedOutcomePhysicalHit_card_le_rank
        support scale outcome label center targets).trans
          (scaleAdaptiveMixedOutcomeActiveIndices_card_le_scale
            support scale outcome)
  unfold scaleAdaptiveSignedCommonGoodMixtureTargetVariation
  change
    scaleAdaptivePrimeLabelNormalizedWeight N *
      (∑ label ∈ good, _) ≤ _
  calc
    _ ≤ scaleAdaptivePrimeLabelNormalizedWeight N *
        (∑ label ∈ good,
          (scale : ℝ) *
            ∑ outcome ∈ patterns,
              |scaleAdaptiveSignedOutcomeDegreeRatio
                support scale outcome lower upper
                  (singular outcome) N label - 1|) := by
      apply mul_le_mul_of_nonneg_left _ weight_nonnegative
      apply Finset.sum_le_sum
      intro label selected
      exact individual label selected
    _ = (scale : ℝ) *
        ∑ outcome ∈ patterns,
          ∑ label ∈ good,
            scaleAdaptivePrimeLabelNormalizedWeight N *
              |scaleAdaptiveSignedOutcomeDegreeRatio
                support scale outcome lower upper
                  (singular outcome) N label - 1| := by
      calc
        _ = ∑ label ∈ good,
            ∑ outcome ∈ patterns,
              (scale : ℝ) *
                (scaleAdaptivePrimeLabelNormalizedWeight N *
                  |scaleAdaptiveSignedOutcomeDegreeRatio
                    support scale outcome lower upper
                      (singular outcome) N label - 1|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro label _selected
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro outcome _selected
          ring
        _ = ∑ outcome ∈ patterns,
            ∑ label ∈ good,
              (scale : ℝ) *
                (scaleAdaptivePrimeLabelNormalizedWeight N *
                  |scaleAdaptiveSignedOutcomeDegreeRatio
                    support scale outcome lower upper
                      (singular outcome) N label - 1|) := by
          rw [Finset.sum_comm]
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro outcome _selected
          rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro outcome _in_family
      unfold scaleAdaptiveSignedOutcomeNormalizedDegreeResidual
        scaleAdaptiveWeightedDegreeResidual
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro label selected
        exact (Finset.mem_sdiff.mp selected).1
      · intro label _in_pool _not_good
        exact mul_nonneg weight_nonnegative (abs_nonneg _)

/-- The genuine common-prime-pool finite mixed sampler has vanishing TOTAL
physical-target variation between actual inverse-integer-degree and true
expected-degree edge choices.  Its bound is rank-weighted, not multiplied
by the number of targets. -/
theorem scaleAdaptiveSignedCommonGoodMixtureTargetVariation_tendsto_zero
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (singular mass : (ℕ × ℕ) → ℝ)
    (targets : ℕ → Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (band_nonempty : lower < upper)
    (singular_positive : ∀ outcome ∈ patterns, 0 < singular outcome)
    (mass_nonnegative : ∀ outcome ∈ patterns, 0 ≤ mass outcome)
    (normalized : ∑ outcome ∈ patterns, mass outcome = 1)
    (quadratic : ∀ outcome ∈ patterns,
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper (singular outcome) N))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedCommonGoodMixtureTargetVariation
        support scale patterns lower upper singular mass N (targets N))
      atTop (nhds (0 : ℝ)) := by
  have sum_residual :
      Tendsto
        (fun N : ℕ =>
          ∑ outcome ∈ patterns,
            scaleAdaptiveSignedOutcomeNormalizedDegreeResidual
              support scale outcome lower upper (singular outcome) N)
        atTop (nhds (0 : ℝ)) := by
    have convergence := tendsto_finsetSum patterns (by
      intro outcome selected
      exact scaleAdaptiveSignedOutcomeNormalizedDegreeResidual_tendsto_zero
        support scale outcome lower upper (singular outcome)
          (quadratic outcome selected))
    convert convergence using 1
    simp
  have majorant :
      Tendsto
        (fun N : ℕ =>
          (scale : ℝ) *
            ∑ outcome ∈ patterns,
              scaleAdaptiveSignedOutcomeNormalizedDegreeResidual
                support scale outcome lower upper (singular outcome) N)
        atTop (nhds (0 : ℝ)) := by
    simpa using sum_residual.const_mul (scale : ℝ)
  apply squeeze_zero' _ _ majorant
  · filter_upwards [eventually_ge_atTop 2] with N large
    unfold scaleAdaptiveSignedCommonGoodMixtureTargetVariation
    exact mul_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      (Finset.sum_nonneg fun _label _ =>
        Finset.sum_nonneg fun _target _ => abs_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact scaleAdaptiveSignedCommonGoodMixtureTargetVariation_le_residuals
      support scale patterns lower upper singular mass N (targets N)
      primes band_nonempty singular_positive mass_nonnegative
      normalized large

/-- A single actual common prime-label pool works SIMULTANEOUSLY for every
outcome in a fixed finite signed mixture.  Sole signed GTZ supplies the
canonical shared Euler singulars and their genuine quadratic degree errors.

The retained pool has prime-normalized density one, every retained prime has
positive actual integer degree for every outcome, BOTH deleted actual and
expected-model physical target incidences vanish with their correct rank and
degree weights, and the actual inverse-degree common sampler has vanishing
total physical-target variation from the canonical expected-degree sampler.

The support, scale, and finite outcome family are fixed before the limit;
the target sets may vary freely with the physical scale. -/
theorem scaleAdaptiveSignedCommonGoodPrimePool_actualTransfer_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (patterns : Finset (ℕ × ℕ))
    (lower upper : ℝ) (mass : (ℕ × ℕ) → ℝ)
    (targets : ℕ → Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (mass_nonnegative : ∀ outcome ∈ patterns, 0 ≤ mass outcome)
    (normalized : ∑ outcome ∈ patterns, mass outcome = 1) :
    ∃ singular : (ℕ × ℕ) → ℝ,
      (∀ outcome : ℕ × ℕ,
        0 < singular outcome ∧
          Tendsto
            (adaptiveMixedSignedSingularPartialProduct
              support scale outcome)
            atTop (nhds (singular outcome))) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedCommonRejectedPrimeLabels
            support scale patterns lower upper singular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedCommonGoodPrimeLabels
            support scale patterns lower upper singular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (1 : ℝ)) ∧
      (∀ N label,
        label ∈ scaleAdaptiveSignedCommonGoodPrimeLabels
          support scale patterns lower upper singular N →
          ∀ outcome ∈ patterns,
            (scaleAdaptiveSignedDegreeEdges
              support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label).Nonempty) ∧
      (∀ outcome ∈ patterns,
        Tendsto
          (fun N : ℕ => scaleAdaptiveSignedCommonRejectedActualEdgeMass
            support scale patterns outcome lower upper singular N)
          atTop (nhds (0 : ℝ)) ∧
        Tendsto
          (fun N : ℕ => scaleAdaptiveSignedCommonRejectedModelEdgeMass
            support scale patterns outcome lower upper singular N)
          atTop (nhds (0 : ℝ)) ∧
        Tendsto
          (fun N : ℕ => scaleAdaptiveSignedCommonRejectedActualTargetIncidence
            support scale patterns outcome lower upper singular N (targets N))
          atTop (nhds (0 : ℝ)) ∧
        Tendsto
          (fun N : ℕ => scaleAdaptiveSignedCommonRejectedModelTargetIncidence
            support scale patterns outcome lower upper singular N (targets N))
          atTop (nhds (0 : ℝ))) ∧
      Tendsto
        (fun N : ℕ => scaleAdaptiveSignedCommonGoodMixtureTargetVariation
          support scale patterns lower upper singular mass N (targets N))
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, canonical⟩ :=
    scaleAdaptiveBand_common_outcome_singular_exists_of_GTZ
      green_tao support scale lower upper primes
        lower_nonnegative band_nonempty upper_bounded
  have quadratic : ∀ outcome ∈ patterns,
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N
              (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                support scale outcome lower upper (singular outcome) N))
        atTop (nhds (0 : ℝ)) := by
    intro outcome _selected
    exact scaleAdaptiveSignedOutcome_fullRelativeDegreeError_of_canonical
      green_tao support scale outcome lower upper (singular outcome)
      primes lower_nonnegative band_nonempty upper_bounded
        (canonical outcome).2
  have rejected :=
    scaleAdaptiveSignedCommonRejectedPrimeLabels_normalized_card_tendsto_zero
      support scale patterns lower upper singular quadratic
  have retained :=
    scaleAdaptiveSignedCommonGoodPrimeLabels_normalized_card_tendsto_one
      support scale patterns lower upper singular quadratic
  refine ⟨singular, canonical, rejected, retained, ?_, ?_, ?_⟩
  · intro N label selected outcome in_family
    exact scaleAdaptiveSignedCommonGoodPrimeLabels_usable
      support scale patterns lower upper singular N label
        selected in_family
  · intro outcome in_family
    have actual_edges :=
      scaleAdaptiveSignedCommonRejectedActualEdgeMass_tendsto_zero
        support scale patterns outcome lower upper singular rejected
    have model_edges :=
      scaleAdaptiveSignedCommonRejectedModelEdgeMass_tendsto_zero
        support scale patterns outcome lower upper singular
        primes band_nonempty (canonical outcome).1 rejected
          (quadratic outcome in_family)
    refine ⟨actual_edges, model_edges, ?_, ?_⟩
    · exact scaleAdaptiveSignedCommonRejectedActualTargetIncidence_tendsto_zero
        support scale patterns outcome lower upper singular targets actual_edges
    · exact scaleAdaptiveSignedCommonRejectedModelTargetIncidence_tendsto_zero
        support scale patterns outcome lower upper singular targets
        primes band_nonempty (canonical outcome).1 model_edges
  · exact scaleAdaptiveSignedCommonGoodMixtureTargetVariation_tendsto_zero
      support scale patterns lower upper singular mass targets
      primes band_nonempty (fun outcome _selected => (canonical outcome).1)
      mass_nonnegative normalized quadratic


end Erdos1139
