module

public import ScaleAdaptivePrimeSliceVariance1139
public import ScaleAdaptiveWeightedDegreeLimit1139

@[expose] public section


/-!
# Actual constant-band inverse-degree transfer

On the genuine constant-residue band, the original and shared-label signed
Green--Tao asymptotics imply a vanishing, prime-density-normalized relative
degree variance.  The results below transfer that true degree information to
the ACTUAL nonempty prime-label fibers and their genuine inverse-degree
physical-target loads.  No covering, covariance, concentration, or target
independence hypothesis is inserted.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1139

/-- The natural mass of one genuine dyadic prime label.  With this weight the
total prime-label mass tends to one by the ordinary prime number theorem. -/
noncomputable def scaleAdaptivePrimeLabelNormalizedWeight (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / (N : ℝ)

/-- The true normalized prime-label weight is nonnegative at every relevant
scale. -/
theorem scaleAdaptivePrimeLabelNormalizedWeight_nonnegative
    (N : ℕ) (large : 2 ≤ N) :
    0 ≤ scaleAdaptivePrimeLabelNormalizedWeight N := by
  unfold scaleAdaptivePrimeLabelNormalizedWeight
  have N_positive : (0 : ℝ) < N := by
    exact_mod_cast (by omega : 0 < N)
  have log_nonnegative : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  exact div_nonneg log_nonnegative N_positive.le

/-- Filtering out genuinely empty actual prime-label fibers can only decrease
the nonnegative weighted relative degree error.  This finite comparison is
unconditional and allows an arbitrary label-dependent expected degree. -/
theorem scaleAdaptiveSignedNonemptyDegree_weightedQuadratic_le_full
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) (expected : ℕ → ℝ)
    (large : 2 ≤ N) :
    scaleAdaptiveWeightedDegreeQuadraticError
      (scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N)
      (fun label =>
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ))
      (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
      expected ≤
    scaleAdaptiveWeightedDegreeQuadraticError
      (scaleAdaptiveSignedDegreePrimeLabels N)
      (fun label =>
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ))
      (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
      expected := by
  unfold scaleAdaptiveWeightedDegreeQuadraticError
    scaleAdaptiveSignedNonemptyDegreePrimeLabels
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro label _ _
    exact mul_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      (sq_nonneg _)

/-- Empty actual prime-label fibers each contribute one full unit to the
relative squared degree error, regardless of the expected profile. -/
theorem scaleAdaptiveSignedEmptyDegree_normalizedMass_le_weightedQuadratic
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) (expected : ℕ → ℝ)
    (large : 2 ≤ N) :
    (((scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
        scaleAdaptiveSignedDegree
          support scale outcome domain N label = 0).card : ℝ) *
      scaleAdaptivePrimeLabelNormalizedWeight N ≤
    scaleAdaptiveWeightedDegreeQuadraticError
      (scaleAdaptiveSignedDegreePrimeLabels N)
      (fun label =>
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ))
      (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
      expected := by
  let empty := (scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
    scaleAdaptiveSignedDegree support scale outcome domain N label = 0
  have exact_empty :
      ((empty.card : ℝ) * scaleAdaptivePrimeLabelNormalizedWeight N) =
        scaleAdaptiveWeightedDegreeQuadraticError empty
          (fun label =>
            (scaleAdaptiveSignedDegree
              support scale outcome domain N label : ℝ))
          (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
          expected := by
    calc
      _ = ∑ _label ∈ empty,
        scaleAdaptivePrimeLabelNormalizedWeight N := by simp
      _ = _ := by
        unfold scaleAdaptiveWeightedDegreeQuadraticError
        apply Finset.sum_congr rfl
        intro label selected
        have zero := (Finset.mem_filter.mp selected).2
        simp [zero]
  change (empty.card : ℝ) *
    scaleAdaptivePrimeLabelNormalizedWeight N ≤ _
  rw [exact_empty]
  unfold scaleAdaptiveWeightedDegreeQuadraticError
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro label _ _
    exact mul_nonneg
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      (sq_nonneg _)

/-- The actual full-prime-pool normalized relative quadratic error, with a
scale-dependent but label-constant expected signed degree. -/
noncomputable def scaleAdaptiveSignedFullRelativeDegreeError
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) (expected : ℝ) : ℝ :=
  scaleAdaptiveWeightedDegreeQuadraticError
    (scaleAdaptiveSignedDegreePrimeLabels N)
    (fun label =>
      (scaleAdaptiveSignedDegree
        support scale outcome domain N label : ℝ))
    (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
    (fun _ => expected)

/-- The true quadratic degree error restricted to labels where an actual
inverse-degree pattern distribution is defined. -/
noncomputable def scaleAdaptiveSignedUsableRelativeDegreeError
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) (expected : ℝ) : ℝ :=
  scaleAdaptiveWeightedDegreeQuadraticError
    (scaleAdaptiveSignedNonemptyDegreePrimeLabels
      support scale outcome domain N)
    (fun label =>
      (scaleAdaptiveSignedDegree
        support scale outcome domain N label : ℝ))
    (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
    (fun _ => expected)

/-- Natural prime-density-normalized mass of genuine prime labels with no
actual signed pattern realization. -/
noncomputable def scaleAdaptiveSignedEmptyPrimeLabelMass
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) : ℝ :=
  (((scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
      scaleAdaptiveSignedDegree
        support scale outcome domain N label = 0).card : ℝ) *
    scaleAdaptivePrimeLabelNormalizedWeight N

/-- Natural-scale TOTAL variation on all genuine moving physical targets,
between the actual inverse-INTEGER-degree pattern distribution and its
label-constant expected-degree model. -/
noncomputable def scaleAdaptiveSignedNormalizedActualTargetVariation
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ) (expected : ℝ) : ℝ :=
  ∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
    |scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
        support scale outcome domain index N
          (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N) target -
      scaleAdaptiveSignedModelDegreeIndexedTargetLoad
        support scale outcome domain index N
          (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
          (fun _ => expected) target|

/-- The total normalized mass of actual usable prime labels never exceeds
the total normalized mass of all genuine dyadic prime labels. -/
theorem scaleAdaptiveSignedNonemptyDegree_normalizedMass_le_full
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ)
    (large : 2 ≤ N) :
    (∑ _label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
      support scale outcome domain N,
        scaleAdaptivePrimeLabelNormalizedWeight N) ≤
      ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N := by
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _
    (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- The actual weighted quadratic degree error tends to zero on the FULL
genuine prime-label pool.  This is precisely the weighted Cauchy input, with
the natural prime-density mass, deduced from the source-faithful signed
Green--Tao package and the already audited prime number theorem. -/
theorem scaleAdaptiveSignedConstantResidueBand_fullRelativeDegreeError_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (strict : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedFullRelativeDegreeError
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, relative⟩ :=
    scaleAdaptiveSignedConstantResidueBand_relativeVariance_tendsto_zero_of_GTZ
      green_tao support scale outcome lower upper primes
      lower_nonnegative strict upper_bounded
  refine ⟨singular, positive, ?_⟩
  apply relative.congr'
  exact Eventually.of_forall fun N => by
    unfold scaleAdaptiveSignedFullRelativeDegreeError
      scaleAdaptiveWeightedDegreeQuadraticError
      scaleAdaptivePrimeLabelNormalizedWeight
    dsimp
    rw [← Finset.mul_sum]
    ring

/-- Genuine dyadic prime labels have asymptotic normalized total mass one. -/
theorem scaleAdaptiveSignedDegreePrimeLabels_normalizedWeight_tendsto_one :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (1 : ℝ)) := by
  convert scaleAdaptiveSignedDegreePrimeLabels_normalized_tendsto_one using 1
  ext N
  unfold scaleAdaptivePrimeLabelNormalizedWeight
  ring

theorem scaleAdaptiveSignedUsableAndEmptyLimits_of_fullRelative
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (expected : ℕ → ℝ)
    (full : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedFullRelativeDegreeError
        support scale outcome domain N (expected N))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedUsableRelativeDegreeError
        support scale outcome domain N (expected N))
      atTop (nhds (0 : ℝ)) ∧
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedEmptyPrimeLabelMass
        support scale outcome domain N)
      atTop (nhds (0 : ℝ)) := by
  constructor
  · apply squeeze_zero' _ _ full
    · filter_upwards [eventually_ge_atTop 2] with N large
      unfold scaleAdaptiveSignedUsableRelativeDegreeError
      apply scaleAdaptiveWeightedDegreeQuadraticError_nonnegative
      intro label _
      exact scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
    · filter_upwards [eventually_ge_atTop 2] with N large
      unfold scaleAdaptiveSignedUsableRelativeDegreeError
        scaleAdaptiveSignedFullRelativeDegreeError
      exact scaleAdaptiveSignedNonemptyDegree_weightedQuadratic_le_full
        support scale outcome domain N (fun _ => expected N) large
  · apply squeeze_zero' _ _ full
    · filter_upwards [eventually_ge_atTop 2] with N large
      unfold scaleAdaptiveSignedEmptyPrimeLabelMass
      exact mul_nonneg (by positivity)
        (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
    · filter_upwards [eventually_ge_atTop 2] with N large
      unfold scaleAdaptiveSignedEmptyPrimeLabelMass
        scaleAdaptiveSignedFullRelativeDegreeError
      exact
        scaleAdaptiveSignedEmptyDegree_normalizedMass_le_weightedQuadratic
          support scale outcome domain N (fun _ => expected N) large

theorem scaleAdaptiveSignedUsablePrimeMass_tendsto_one_of_empty
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ))
    (empty : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedEmptyPrimeLabelMass
        support scale outcome domain N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedNonemptyDegreePrimeLabels
          support scale outcome domain N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (1 : ℝ)) := by
  have difference :=
    scaleAdaptiveSignedDegreePrimeLabels_normalizedWeight_tendsto_one.sub empty
  have target :
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N -
            scaleAdaptiveSignedEmptyPrimeLabelMass
              support scale outcome domain N)
        atTop (nhds (1 : ℝ)) := by
    simpa using difference
  apply target.congr'
  exact Eventually.of_forall fun N => by
    have partition := Finset.card_filter_add_card_filter_not
      (s := scaleAdaptiveSignedDegreePrimeLabels N)
      (fun label =>
        scaleAdaptiveSignedDegree support scale outcome domain N label ≠ 0)
    have natural_partition :
        ((scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
          scaleAdaptiveSignedDegree
            support scale outcome domain N label ≠ 0).card +
          ((scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
            scaleAdaptiveSignedDegree
              support scale outcome domain N label = 0).card =
          (scaleAdaptiveSignedDegreePrimeLabels N).card := by
      simpa only [not_not] using partition
    have real_partition :
        ((scaleAdaptiveSignedNonemptyDegreePrimeLabels
            support scale outcome domain N).card : ℝ) +
          (((scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
              scaleAdaptiveSignedDegree
                support scale outcome domain N label = 0).card : ℝ) =
          ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) := by
      unfold scaleAdaptiveSignedNonemptyDegreePrimeLabels
      exact_mod_cast natural_partition
    unfold scaleAdaptiveSignedEmptyPrimeLabelMass
    dsimp
    rw [← real_partition]
    ring

theorem scaleAdaptiveSignedTargetVariation_tendsto_zero_of_usableRelative
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index : ℕ) (expected : ℕ → ℝ)
    (eventually_positive : ∀ᶠ N : ℕ in atTop, 0 < expected N)
    (usable : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedUsableRelativeDegreeError
        support scale outcome domain N (expected N))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedNormalizedActualTargetVariation
        support scale outcome domain index N (expected N))
      atTop (nhds (0 : ℝ)) := by
  have bounded : ∀ᶠ N : ℕ in atTop,
      ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N < 2 :=
    (tendsto_order.1
      scaleAdaptiveSignedDegreePrimeLabels_normalizedWeight_tendsto_one).2
        2 (by norm_num)
  have doubled :
      Tendsto
        (fun N : ℕ =>
          2 * scaleAdaptiveSignedUsableRelativeDegreeError
            support scale outcome domain N (expected N))
        atTop (nhds (0 : ℝ)) := by
    simpa using usable.const_mul (2 : ℝ)
  have product :
      Tendsto
        (fun N : ℕ =>
          (∑ _label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
            support scale outcome domain N,
              scaleAdaptivePrimeLabelNormalizedWeight N) *
            scaleAdaptiveSignedUsableRelativeDegreeError
              support scale outcome domain N (expected N))
        atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero' _ _ doubled
    · filter_upwards [eventually_ge_atTop 2] with N large
      apply mul_nonneg
      · exact Finset.sum_nonneg fun _label _ =>
          scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
      · unfold scaleAdaptiveSignedUsableRelativeDegreeError
        apply scaleAdaptiveWeightedDegreeQuadraticError_nonnegative
        intro label _
        exact scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
    · filter_upwards [eventually_ge_atTop 2, bounded] with N large bound
      apply mul_le_mul_of_nonneg_right
      · exact
          (scaleAdaptiveSignedNonemptyDegree_normalizedMass_le_full
            support scale outcome domain N large).trans bound.le
      · unfold scaleAdaptiveSignedUsableRelativeDegreeError
        apply scaleAdaptiveWeightedDegreeQuadraticError_nonnegative
        intro label _
        exact scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
  have root :
      Tendsto
        (fun N : ℕ =>
          Real.sqrt
            ((∑ _label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
              support scale outcome domain N,
                scaleAdaptivePrimeLabelNormalizedWeight N) *
              scaleAdaptiveSignedUsableRelativeDegreeError
                support scale outcome domain N (expected N)))
        atTop (nhds (0 : ℝ)) := by
    simpa using product.sqrt
  apply squeeze_zero' _ _ root
  · exact Eventually.of_forall fun N => by
      unfold scaleAdaptiveSignedNormalizedActualTargetVariation
      exact Finset.sum_nonneg fun _target _ => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 2, eventually_positive]
      with N large positive
    unfold scaleAdaptiveSignedNormalizedActualTargetVariation
      scaleAdaptiveSignedUsableRelativeDegreeError
    apply scaleAdaptiveSignedInverseDegreeIndexedTarget_totalVariation_le_sqrt
      support scale outcome domain index N
      (fun _ => scaleAdaptivePrimeLabelNormalizedWeight N)
      (fun _ => expected N)
    · intro label _
      exact scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large
    · intro label _
      exact positive.ne'

/-- ACTUAL normalized inverse-degree transfer on every genuine constant
signed residue band, at every fixed pattern rank and every physical target
index.  The same positive singular constant simultaneously gives:

* vanishing true relative quadratic error on the FULL genuine prime pool;
* vanishing true error after discarding empty fibers;
* zero normalized density of empty fibers;
* normalized density ONE of usable actual prime labels; and
* vanishing TOTAL physical-target variation between the genuine
  inverse-INTEGER-degree load and its true expected-degree model.

The sole analytic argument is the explicit fixed-system signed Green--Tao
package; ordinary PNT is already proved by the imported development.
There is no extra moment, concentration, covariance, covering, matching,
prime-target, or geometric assumption.  In particular, this result by
itself does not assert that the physical target loads cover all primes. -/
theorem scaleAdaptiveSignedConstantResidueBand_actualDegreeTransfer_tendsto_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (strict : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : ℝ, 0 < singular ∧
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
          scaleAdaptiveSignedUsableRelativeDegreeError
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper)
            N
            (scaleAdaptiveSignedConstantResidueBandExpectedDegree
              support scale outcome lower upper singular N))
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedEmptyPrimeLabelMass
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper) N)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedNonemptyDegreePrimeLabels
            support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper) N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (1 : ℝ)) ∧
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
  obtain ⟨singular, positive, full⟩ :=
    scaleAdaptiveSignedConstantResidueBand_fullRelativeDegreeError_tendsto_zero_of_GTZ
      green_tao support scale outcome lower upper primes
      lower_nonnegative strict upper_bounded
  let band := scaleAdaptiveSignedConstantResidueBand
    support outcome.1 lower upper
  let expected : ℕ → ℝ := fun N =>
    scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper singular N
  have full' :
      Tendsto
        (fun N : ℕ => scaleAdaptiveSignedFullRelativeDegreeError
          support scale outcome band N (expected N))
        atTop (nhds (0 : ℝ)) := by
    simpa [band, expected] using full
  obtain ⟨usable, empty⟩ :=
    scaleAdaptiveSignedUsableAndEmptyLimits_of_fullRelative
      support scale outcome band expected full'
  have density := scaleAdaptiveSignedUsablePrimeMass_tendsto_one_of_empty
    support scale outcome band empty
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have width_positive :
      0 < (upper - lower) / (adaptiveMixedTypeModulus support : ℝ) :=
    div_pos (sub_pos.mpr strict) modulus_positive
  have expected_positive : ∀ᶠ N : ℕ in atTop, 0 < expected N := by
    filter_upwards [eventually_ge_atTop 2] with N large
    have N_positive : (0 : ℝ) < N := by
      exact_mod_cast (by omega : 0 < N)
    have log_positive : 0 < Real.log (N : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < N)
    dsimp [expected]
    unfold scaleAdaptiveSignedConstantResidueBandExpectedDegree
    exact div_pos (mul_pos (mul_pos width_positive positive) N_positive)
      (pow_pos log_positive _)
  have target :=
    scaleAdaptiveSignedTargetVariation_tendsto_zero_of_usableRelative
      support scale outcome band index expected expected_positive usable
  exact ⟨singular, positive, full,
    by simpa [band, expected] using usable,
    by simpa [band] using empty,
    by simpa [band] using density,
    by simpa [band, expected] using target⟩


end Erdos1139
