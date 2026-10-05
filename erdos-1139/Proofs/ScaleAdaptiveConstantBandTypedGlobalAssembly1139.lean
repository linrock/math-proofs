module

public import ScaleAdaptiveConstantBandGlobalCorrelation1139
public import ScaleAdaptiveConstantBandTargetMoments1139
public import ScaleAdaptiveConstantBandTargetConcentration1139

@[expose] public section


/-!
# Actual typed-target assembly on a signed constant-residue band

The intended cell consists of genuine targets `s*q` for prime `q`, with
strict physical endpoints.  The continuous target-truncated GTZ domains are
OPEN, while the existing prime-counting cells are closed on the right; the
upper endpoint therefore has to be removed explicitly.

Every finite incidence identity below retains actual signed prime labels,
true center fibers, inverse-integer-degree pattern probabilities, the exact
same-label diagonal, and a common canonical singular constant.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1139

/-- Exact genuine prime-label partition of ONE physical signed target fiber.
Every summand uses an actually nonempty prime-pattern degree fiber; no
zero-degree label, nonprime label, or real-domain witness is counted. -/
theorem scaleAdaptiveGTZIndexedTargetFiber_card_eq_usableLabelTargetFibers
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ) :
    (scaleAdaptiveGTZIndexedTargetFiber
      support scale outcome domain index N target).card =
      ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N,
          (scaleAdaptiveSignedIndexedLabelTargetFiber
            support scale outcome domain index N label target).card := by
  classical
  let fiber := scaleAdaptiveGTZIndexedTargetFiber
    support scale outcome domain index N target
  let labels := scaleAdaptiveSignedNonemptyDegreePrimeLabels
    support scale outcome domain N
  have mapped :
      (↑fiber : Set (ℕ × ℤ)).MapsTo
        (fun pair => pair.1) labels := by
    intro pair selected
    have original := (Finset.mem_filter.mp selected).1
    have decoded :=
      (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
        support scale outcome domain N pair).mp original
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨decoded.1,
        scaleAdaptiveSignedDegreeEdges_label_prime
          support scale outcome domain N pair.1 pair.2 decoded.2⟩
    · unfold scaleAdaptiveSignedDegree
      exact Finset.card_ne_zero.mpr ⟨pair.2, decoded.2⟩
  change fiber.card = _
  rw [Finset.card_eq_sum_card_fiberwise mapped]
  apply Finset.sum_congr rfl
  intro label selected
  change
    (fiber.filter fun pair => pair.1 = label).card =
      (scaleAdaptiveSignedIndexedLabelTargetFiber
        support scale outcome domain index N label target).card
  apply Finset.card_bij fun pair _ => pair.2
  · intro pair pair_selected
    obtain ⟨in_fiber, same_label⟩ := Finset.mem_filter.mp pair_selected
    obtain ⟨original, target_equal⟩ := Finset.mem_filter.mp in_fiber
    have edge :=
      (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
        support scale outcome domain N pair).mp original |>.2
    apply Finset.mem_filter.mpr
    constructor
    · simpa [same_label] using edge
    · simpa [same_label] using target_equal
  · intro first first_selected second second_selected same_center
    have first_label := (Finset.mem_filter.mp first_selected).2
    have second_label := (Finset.mem_filter.mp second_selected).2
    exact Prod.ext (first_label.trans second_label.symm) same_center
  · intro center center_selected
    obtain ⟨edge, target_equal⟩ := Finset.mem_filter.mp center_selected
    refine ⟨(label, center), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply
        (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
          support scale outcome domain N (label, center)).mpr
      exact ⟨(Finset.mem_filter.mp
        (Finset.mem_filter.mp selected).1).1, edge⟩
    · exact target_equal

/-- The true unit-mass, expected-degree model is EXACTLY raw signed target
incidence divided by the actual constant expected pattern degree. -/
theorem scaleAdaptiveSignedUnitModelTargetLoad_eq_indexedFiber_div
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ)
    (expected : ℝ) :
    scaleAdaptiveSignedModelDegreeIndexedTargetLoad
      support scale outcome domain index N
        (fun _ => 1) (fun _ => expected) target =
      ((scaleAdaptiveGTZIndexedTargetFiber
        support scale outcome domain index N target).card : ℝ) / expected := by
  unfold scaleAdaptiveSignedModelDegreeIndexedTargetLoad
  dsimp
  simp_rw [one_mul]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast
    scaleAdaptiveGTZIndexedTargetFiber_card_eq_usableLabelTargetFibers
      support scale outcome domain index N target |>.symm

/-- The TRUE target probability contributed by one actual nonempty signed
prime-label fiber: its genuine target-edge multiplicity divided by its
actual positive INTEGER prime-pattern degree. -/
noncomputable def scaleAdaptiveSignedActualLabelTargetProbability
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N label target : ℕ) : ℝ :=
  ((scaleAdaptiveSignedIndexedLabelTargetFiber
    support scale outcome domain index N label target).card : ℝ) /
    (scaleAdaptiveSignedDegree support scale outcome domain N label : ℝ)

/-- The genuine unit-label inverse-degree load is the sum of its exact
actual prime-label target probabilities. -/
theorem scaleAdaptiveSignedActualIndexedTargetLoad_eq_label_probabilities
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N target : ℕ) :
    scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
      support scale outcome domain index N (fun _ => 1) target =
      ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N,
          scaleAdaptiveSignedActualLabelTargetProbability
            support scale outcome domain index N label target := by
  unfold scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
    scaleAdaptiveSignedActualLabelTargetProbability
  simp

/-- Exact same-genuine-prime-label target energy for the actual signed
inverse-integer-degree probability distribution. -/
noncomputable def scaleAdaptiveSignedActualLabelDiagonalEnergy
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) : ℝ :=
  ∑ target ∈ targets,
    ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
      support scale outcome domain N,
        (scaleAdaptiveSignedActualLabelTargetProbability
          support scale outcome domain index N label target) ^ 2

/-- Exact ordered, genuinely DISTINCT-prime-label target correlation for
the actual signed inverse-integer-degree pattern distribution. -/
noncomputable def scaleAdaptiveSignedActualDistinctLabelEnergy
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) : ℝ :=
  ∑ target ∈ targets,
    ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
      support scale outcome domain N,
      ∑ other ∈
        (scaleAdaptiveSignedNonemptyDegreePrimeLabels
          support scale outcome domain N).erase label,
        scaleAdaptiveSignedActualLabelTargetProbability
          support scale outcome domain index N label target *
        scaleAdaptiveSignedActualLabelTargetProbability
          support scale outcome domain index N other target

/-- EXACT targetwise actual inverse-degree second moment: the same-label
diagonal plus every ordered genuinely distinct-prime-label correlation.
No degree regularity, Green--Tao input, or omitted shot noise is assumed. -/
theorem scaleAdaptiveSignedActualTarget_secondMoment_eq_diagonal_add_distinct
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) :
    (∑ target ∈ targets,
      (scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
        support scale outcome domain index N (fun _ => 1) target) ^ 2) =
      scaleAdaptiveSignedActualLabelDiagonalEnergy
        support scale outcome domain index N targets +
      scaleAdaptiveSignedActualDistinctLabelEnergy
        support scale outcome domain index N targets := by
  classical
  unfold scaleAdaptiveSignedActualLabelDiagonalEnergy
    scaleAdaptiveSignedActualDistinctLabelEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro target _
  rw [scaleAdaptiveSignedActualIndexedTargetLoad_eq_label_probabilities,
    pow_two, Finset.sum_mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro label selected
  rw [← Finset.sum_erase_add
    (scaleAdaptiveSignedNonemptyDegreePrimeLabels
      support scale outcome domain N)
    (fun other =>
      scaleAdaptiveSignedActualLabelTargetProbability
        support scale outcome domain index N label target *
      scaleAdaptiveSignedActualLabelTargetProbability
        support scale outcome domain index N other target)
    selected]
  ring

/-- The exact actual distinct-prime-label off-diagonal bound is EQUIVALENT
to the corresponding centered inverse-degree target variance.  This is the
correct one-cell finite correlation premise, with its true same-label
diagonal, first moment, target cardinality, and target mean all retained. -/
theorem scaleAdaptiveSignedActualDistinctLabelEnergy_le_iff_centeredVariance
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (mean variance : ℝ) :
    scaleAdaptiveSignedActualDistinctLabelEnergy
      support scale outcome domain index N targets ≤
        variance - scaleAdaptiveSignedActualLabelDiagonalEnergy
          support scale outcome domain index N targets +
        2 * mean *
          (∑ target ∈ targets,
            scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
              support scale outcome domain index N
                (fun _ => 1) target) -
        (targets.card : ℝ) * mean ^ 2 ↔
      (∑ target ∈ targets,
        (scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
          support scale outcome domain index N
            (fun _ => 1) target - mean) ^ 2) ≤ variance := by
  have second :=
    scaleAdaptiveSignedActualTarget_secondMoment_eq_diagonal_add_distinct
      support scale outcome domain index N targets
  have expansion :
      (∑ target ∈ targets,
        (scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
          support scale outcome domain index N
            (fun _ => 1) target - mean) ^ 2) =
        (∑ target ∈ targets,
          (scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
            support scale outcome domain index N
              (fun _ => 1) target) ^ 2) -
        2 * mean *
          (∑ target ∈ targets,
            scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
              support scale outcome domain index N
                (fun _ => 1) target) +
        (targets.card : ℝ) * mean ^ 2 := by
    calc
      _ = ∑ target ∈ targets,
        ((scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
          support scale outcome domain index N
            (fun _ => 1) target) ^ 2 -
          2 * mean *
            scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
              support scale outcome domain index N
                (fun _ => 1) target + mean ^ 2) := by
        apply Finset.sum_congr rfl
        intro target _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  rw [expansion, second]
  constructor <;> intro bound <;> linarith

/-- The EXACT centered signed-prime-label correlation, retaining both the
true same-label diagonal and ALL genuinely distinct actual prime labels. -/
noncomputable def scaleAdaptiveSignedActualCenteredCorrelation
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (mean : ℝ) : ℝ :=
  scaleAdaptiveSignedActualLabelDiagonalEnergy
    support scale outcome domain index N targets +
  scaleAdaptiveSignedActualDistinctLabelEnergy
    support scale outcome domain index N targets -
  2 * mean *
    (∑ target ∈ targets,
      scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
        support scale outcome domain index N (fun _ => 1) target) +
  (targets.card : ℝ) * mean ^ 2

/-- The true centered actual prime-label correlation is EXACTLY the genuine
inverse-integer-degree targetwise centered variance.  Thus proving a
vanishing good-cell variance proves the corresponding actual signed
off-diagonal premise without discarding or assuming its diagonal. -/
theorem scaleAdaptiveSignedActualCenteredCorrelation_eq_centeredVariance
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (targets : Finset ℕ) (mean : ℝ) :
    scaleAdaptiveSignedActualCenteredCorrelation
      support scale outcome domain index N targets mean =
      ∑ target ∈ targets,
        (scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
          support scale outcome domain index N
            (fun _ => 1) target - mean) ^ 2 := by
  unfold scaleAdaptiveSignedActualCenteredCorrelation
  rw [← scaleAdaptiveSignedActualTarget_secondMoment_eq_diagonal_add_distinct]
  calc
    _ = ∑ target ∈ targets,
      ((scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
        support scale outcome domain index N
          (fun _ => 1) target) ^ 2 -
        2 * mean *
          scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
            support scale outcome domain index N
              (fun _ => 1) target + mean ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro target _
      ring

/-- A single moving target has vanishing density at the genuine dyadic
prime-label scale.  This is the exact cost of removing the incompatible
closed upper endpoint from a genuinely OPEN physical GTZ target domain. -/
theorem scaleAdaptivePrimeLabelNormalizedWeight_tendsto_zero :
    Tendsto scaleAdaptivePrimeLabelNormalizedWeight
      atTop (nhds (0 : ℝ)) := by
  have real_limit := Real.tendsto_pow_log_div_mul_add_atTop
    (1 : ℝ) 0 1 one_ne_zero
  have natural := real_limit.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
    atTop (nhds (0 : ℝ))
  simpa [Function.comp_def] using natural

/-- Removing ONE actual moving integer target preserves every existing
prime-density-normalized cardinality asymptotic.  This is valid whether or
not the endpoint itself is prime or belongs to the source target cell. -/
theorem scaleAdaptiveMovingEndpointErase_normalizedDensity_tendsto
    (targets : ℕ → Finset ℕ) (endpoint : ℕ → ℕ) (density : ℝ)
    (original : Tendsto
      (fun N : ℕ => ((targets N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds density)) :
    Tendsto
      (fun N : ℕ => (((targets N).erase (endpoint N)).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds density) := by
  have difference :
      Tendsto
        (fun N : ℕ =>
          (((targets N).card : ℝ) -
            (((targets N).erase (endpoint N)).card : ℝ)) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero' _ _ scaleAdaptivePrimeLabelNormalizedWeight_tendsto_zero
    · filter_upwards [eventually_ge_atTop 2] with N large
      exact mul_nonneg
        (sub_nonneg.mpr (by exact_mod_cast Finset.card_erase_le))
        (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
    · filter_upwards [eventually_ge_atTop 2] with N large
      have cardinal :
          (targets N).card ≤ ((targets N).erase (endpoint N)).card + 1 := by
        by_cases selected : endpoint N ∈ targets N
        · rw [Finset.card_erase_add_one selected]
        · rw [Finset.erase_eq_of_notMem selected]
          omega
      have real_cardinal :
          ((targets N).card : ℝ) -
            (((targets N).erase (endpoint N)).card : ℝ) ≤ 1 := by
        have cast_cardinal :
            ((targets N).card : ℝ) ≤
              (((targets N).erase (endpoint N)).card : ℝ) + 1 := by
          exact_mod_cast cardinal
        linarith
      calc
        _ ≤ 1 * scaleAdaptivePrimeLabelNormalizedWeight N :=
          mul_le_mul_of_nonneg_right real_cardinal
            (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
        _ = _ := one_mul _
  have combined := original.sub difference
  have target :
      Tendsto
        (fun N : ℕ =>
          ((targets N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N -
            (((targets N).card : ℝ) -
              (((targets N).erase (endpoint N)).card : ℝ)) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds density) := by
    simpa using combined
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp
    ring

/-- Removing the genuine bad inverse-degree targets preserves the FULL
prime-density asymptotic of the source target cell whenever those deleted
targets have independently proved vanishing normalized density. -/
theorem scaleAdaptiveSignedUnitGoodTargets_normalizedDensity_tendsto
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index : ℕ)
    (targets : ℕ → Finset ℕ)
    (expected tolerance : ℕ → ℝ) (density : ℝ)
    (target_density : Tendsto
      (fun N : ℕ => ((targets N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds density))
    (bad_density : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedUnitBadTargets
          support scale outcome domain index N (targets N)
          (expected N) (tolerance N)).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedUnitGoodTargets
          support scale outcome domain index N (targets N)
          (expected N) (tolerance N)).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds density) := by
  have difference := target_density.sub bad_density
  have target :
      Tendsto
        (fun N : ℕ =>
          ((targets N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N -
            ((scaleAdaptiveSignedUnitBadTargets
              support scale outcome domain index N (targets N)
              (expected N) (tolerance N)).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds density) := by
    simpa using difference
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    have subset :
        scaleAdaptiveSignedUnitBadTargets
          support scale outcome domain index N (targets N)
            (expected N) (tolerance N) ⊆ targets N :=
      Finset.filter_subset _ _
    have partition := Finset.card_sdiff_add_card_eq_card subset
    have cast_partition :
        ((scaleAdaptiveSignedUnitGoodTargets
          support scale outcome domain index N (targets N)
            (expected N) (tolerance N)).card : ℝ) +
        ((scaleAdaptiveSignedUnitBadTargets
          support scale outcome domain index N (targets N)
            (expected N) (tolerance N)).card : ℝ) =
          ((targets N).card : ℝ) := by
      exact_mod_cast partition
    dsimp
    rw [← cast_partition]
    ring

/-- The GENUINE OPEN typed-prime target cell.  The continuous signed GTZ
domains have two strict physical target bounds, so the right-closed
prime-counting endpoint must be explicitly erased. -/
def scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
    (targetType targetLower targetUpper N : ℕ) : Finset ℕ :=
  (scaleAdaptiveTypedPrimeTargetsInIntegerCell
    targetType targetLower targetUpper N).erase (targetUpper * N)

/-- Membership in the actual open target cell means a GENUINE target
`s*q` with prime `q` and BOTH correct strict moving integer endpoints. -/
theorem mem_scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
    {targetType targetLower targetUpper N target : ℕ}
    (type_positive : 0 < targetType) :
    target ∈ scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
      targetType targetLower targetUpper N ↔
      ∃ prime : ℕ, prime.Prime ∧
        targetLower * N < target ∧ target < targetUpper * N ∧
          target = targetType * prime := by
  unfold scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
  constructor
  · intro selected
    obtain ⟨different, closed⟩ := Finset.mem_erase.mp selected
    obtain ⟨prime, primality, lower, upper, equal⟩ :=
      (mem_scaleAdaptiveTypedPrimeTargetsInIntegerCell
        type_positive).mp closed
    exact ⟨prime, primality, lower, by omega, equal⟩
  · rintro ⟨prime, primality, lower, upper, equal⟩
    apply Finset.mem_erase.mpr
    constructor
    · omega
    · exact (mem_scaleAdaptiveTypedPrimeTargetsInIntegerCell
        type_positive).mpr ⟨prime, primality, lower, upper.le, equal⟩

/-- The correctly OPEN typed prime target cell has the SAME exact PNT
density `(targetUpper-targetLower)/type` as the closed prime-counting cell.
The single moving endpoint is genuinely negligible and never assumed empty. -/
theorem scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell_normalized_tendsto
    (targetType targetLower targetUpper : ℕ)
    (type_positive : 0 < targetType)
    (lower_positive : 0 < targetLower)
    (ordered : targetLower ≤ targetUpper) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
          targetType targetLower targetUpper N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds
        (((targetUpper : ℝ) - (targetLower : ℝ)) /
          (targetType : ℝ))) := by
  have closed := scaleAdaptiveTypedPrimeTargetsInIntegerCell_normalized_tendsto
    targetType targetLower targetUpper type_positive lower_positive ordered
  have closed' :
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveTypedPrimeTargetsInIntegerCell
            targetType targetLower targetUpper N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds
          (((targetUpper : ℝ) - (targetLower : ℝ)) /
            (targetType : ℝ))) := by
    apply closed.congr'
    exact Filter.Eventually.of_forall fun N => by
      unfold scaleAdaptivePrimeLabelNormalizedWeight
      dsimp
      ring
  exact scaleAdaptiveMovingEndpointErase_normalizedDensity_tendsto
    (fun N => scaleAdaptiveTypedPrimeTargetsInIntegerCell
      targetType targetLower targetUpper N)
    (fun N => targetUpper * N)
    (((targetUpper : ℝ) - (targetLower : ℝ)) / (targetType : ℝ))
    closed'

/-- An open integer target cell inside the genuine dyadic physical-index
window is a real subset of the exact moving finite target window. -/
theorem scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell_subset_window
    (targetType targetLower targetUpper index N : ℕ)
    (type_positive : 0 < targetType)
    (upper_bounded : targetUpper ≤ 2 * (index + 1)) :
    scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
      targetType targetLower targetUpper N ⊆
        scaleAdaptiveGTZIndexedTargetWindow index N := by
  intro target selected
  obtain ⟨_prime, _primality, _lower, upper, _equal⟩ :=
    (mem_scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
      type_positive).mp selected
  have bound := Nat.mul_le_mul_right N upper_bounded
  unfold scaleAdaptiveGTZIndexedTargetWindow
  apply Finset.mem_range.mpr
  omega

/-- At every genuine OPEN physical target, the target fiber in the
target-truncated signed domain is EXACTLY the full constant-band target
fiber.  This equality correctly fails at the deleted right endpoint. -/
theorem scaleAdaptiveConstantBand_truncatedTargetFiber_eq_full_of_open
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (index targetLower targetUpper N target : ℕ)
    (lower upper : ℝ)
    (scale_positive : 0 < N)
    (target_lower : targetLower * N < target)
    (target_upper : target < targetUpper * N) :
    scaleAdaptiveGTZIndexedTargetFiber
      support scale outcome
        (scaleAdaptiveTruncatedBandSignedDomain
          support outcome.1 index lower upper
            (targetLower : ℝ) (targetUpper : ℝ))
      index N target =
    scaleAdaptiveGTZIndexedTargetFiber
      support scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          support outcome.1 lower upper)
      index N target := by
  classical
  ext pair
  constructor
  · intro selected
    obtain ⟨original, target_equal⟩ := Finset.mem_filter.mp selected
    apply Finset.mem_filter.mpr
    refine ⟨?_, target_equal⟩
    simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter] at original ⊢
    refine ⟨original.1, original.2.1, ?_⟩
    exact ⟨original.2.2.1,
      original.2.2.2.1,
      original.2.2.2.2.1,
      original.2.2.2.2.2.1⟩
  · intro selected
    obtain ⟨original, target_equal⟩ := Finset.mem_filter.mp selected
    have normalized := scaleAdaptiveGTZIndexedPhysicalTarget_normalized_eq
      (index := index) original
    rw [target_equal] at normalized
    have scale_real : (0 : ℝ) < N := by
      exact_mod_cast scale_positive
    have lower_real :
        (targetLower : ℝ) < (target : ℝ) / (N : ℝ) := by
      apply (lt_div_iff₀ scale_real).mpr
      exact_mod_cast target_lower
    have upper_real :
        (target : ℝ) / (N : ℝ) < (targetUpper : ℝ) := by
      apply (div_lt_iff₀ scale_real).mpr
      exact_mod_cast target_upper
    apply Finset.mem_filter.mpr
    refine ⟨?_, target_equal⟩
    simp only [adaptiveMixedSignedOriginalPrimeRealizations,
      Finset.mem_filter] at original ⊢
    refine ⟨original.1, original.2.1,
      original.2.2.1, original.2.2.2.1,
      original.2.2.2.2.1, original.2.2.2.2.2, ?_, ?_⟩
    · rw [← normalized]
      exact lower_real
    · rw [← normalized]
      exact upper_real

/-- TRUE model target variance on the genuine OPEN typed-prime cell tends
to zero.  Every model value is the actual FULL-band signed target-fiber
count divided by the real expected degree; the proof identifies it with the
target-TRUNCATED GTZ fiber exactly on this open cell and drops only the
nonnegative extra closed-endpoint contribution.

The singular is certified by the genuine Euler partial products, and the
sole analytic input is the explicit signed Green--Tao proposition. -/
theorem scaleAdaptiveConstantBand_openTypedModelVariance_tendsto_zero_of_GTZ
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
          scaleAdaptivePrimeLabelNormalizedWeight N *
            (∑ target ∈ scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
              (adaptiveMixedActualIndexType support outcome.1 index)
              targetLower targetUpper N,
              (scaleAdaptiveSignedUnitModelTargetLoad
                support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper)
                index N target
                (scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper singular N) -
                (adaptiveMixedActualIndexType
                  support outcome.1 index : ℝ) / (index : ℝ)) ^ 2))
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, converges, full_variance⟩ :=
    scaleAdaptiveConstantBand_typedTarget_centeredVariance_tendsto_zero_of_GTZ
      green_tao support scale outcome index targetLower targetUpper
      lower upper primes active index_positive lower_nonnegative
      band_nonempty upper_bounded target_nonempty
      interior_lower interior_upper
  refine ⟨singular, positive, converges, ?_⟩
  let targetType := adaptiveMixedActualIndexType
    support outcome.1 index
  let band := scaleAdaptiveSignedConstantResidueBand
    support outcome.1 lower upper
  let truncated := scaleAdaptiveTruncatedBandSignedDomain
    support outcome.1 index lower upper
      (targetLower : ℝ) (targetUpper : ℝ)
  let expected : ℕ → ℝ := fun N =>
    scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper singular N
  let mean : ℝ := (targetType : ℝ) / (index : ℝ)
  let closed : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveTypedPrimeTargetsInIntegerCell
      targetType targetLower targetUpper N
  let opened : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
      targetType targetLower targetUpper N
  have closed_variance :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptivePrimeLabelNormalizedWeight N *
            (∑ target ∈ closed N,
              (((scaleAdaptiveGTZIndexedTargetFiber
                support scale outcome truncated
                  index N target).card : ℝ) /
                  expected N - mean) ^ 2))
        atTop (nhds (0 : ℝ)) := by
    apply full_variance.congr'
    exact Filter.Eventually.of_forall fun N => by
      dsimp [targetType, truncated, expected, mean, closed]
      unfold scaleAdaptivePrimeLabelNormalizedWeight
      ring
  have type_positive : 0 < targetType :=
    adaptiveMixedActualIndexType_pos_of_active primes active
  have target :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptivePrimeLabelNormalizedWeight N *
            (∑ value ∈ opened N,
              (scaleAdaptiveSignedUnitModelTargetLoad
                support scale outcome band index N value (expected N) -
                mean) ^ 2))
        atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero' _ _ closed_variance
    · filter_upwards [eventually_ge_atTop 2] with N large
      exact mul_nonneg
        (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
        (Finset.sum_nonneg fun _value _ => sq_nonneg _)
    · filter_upwards [eventually_ge_atTop 2] with N large
      apply mul_le_mul_of_nonneg_left _
        (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
      calc
        _ = ∑ value ∈ opened N,
          (((scaleAdaptiveGTZIndexedTargetFiber
            support scale outcome truncated index N value).card : ℝ) /
              expected N - mean) ^ 2 := by
            apply Finset.sum_congr rfl
            intro value selected
            obtain ⟨_prime, _primality, low, high, _equal⟩ :=
              (mem_scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
                type_positive).mp selected
            have same :=
              scaleAdaptiveConstantBand_truncatedTargetFiber_eq_full_of_open
                support scale outcome index targetLower targetUpper
                  N value lower upper (by omega) low high
            unfold scaleAdaptiveSignedUnitModelTargetLoad
            rw [scaleAdaptiveSignedUnitModelTargetLoad_eq_indexedFiber_div
              support scale outcome band index N value (expected N)]
            rw [← same]
        _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.erase_subset _ _
          · intro value _ _
            exact sq_nonneg _
  simpa [targetType, band, expected, mean, opened] using target

/-- A deterministic, SAME-EXPECTED-DEGREE adaptive deletion transfer.
Whenever the actual normalized target variation tends to zero, one explicit
strictly positive tolerance tends to zero and the true bad physical targets
have normalized density zero.  No independently chosen singular witness is
introduced by this transfer. -/
theorem scaleAdaptiveSignedAdaptiveBadTargets_tendsto_zero_of_variation
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index : ℕ)
    (targets : ℕ → Finset ℕ) (expected : ℕ → ℝ)
    (supported : ∀ N : ℕ,
      targets N ⊆ scaleAdaptiveGTZIndexedTargetWindow index N)
    (variation : Tendsto
      (fun N : ℕ => scaleAdaptiveSignedNormalizedActualTargetVariation
        support scale outcome domain index N (expected N))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ => scaleAdaptiveSignedAdaptiveTargetTolerance
        support scale outcome domain index N (expected N))
      atTop (nhds (0 : ℝ)) ∧
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedUnitBadTargets
          support scale outcome domain index N (targets N) (expected N)
          (scaleAdaptiveSignedAdaptiveTargetTolerance
            support scale outcome domain index N (expected N))).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ)) := by
  have tolerance :
      Tendsto
        (fun N : ℕ => scaleAdaptiveSignedAdaptiveTargetTolerance
          support scale outcome domain index N (expected N))
        atTop (nhds (0 : ℝ)) := by
    unfold scaleAdaptiveSignedAdaptiveTargetTolerance
    simpa using
      (variation.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))).sqrt
  refine ⟨tolerance, ?_⟩
  apply squeeze_zero' _ _ tolerance
  · filter_upwards [eventually_ge_atTop 2] with N large
    exact mul_nonneg (Nat.cast_nonneg _)
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  · filter_upwards [eventually_ge_atTop 2] with N large
    let threshold := scaleAdaptiveSignedAdaptiveTargetTolerance
      support scale outcome domain index N (expected N)
    have threshold_positive :=
      scaleAdaptiveSignedAdaptiveTargetTolerance_positive
        support scale outcome domain index N (expected N) large
    have markov :=
      scaleAdaptiveSignedUnitBadTargets_normalizedMass_mul_tolerance_le
        support scale outcome domain index N (targets N)
        (expected N) threshold large (supported N)
    have variation_nonnegative :=
      scaleAdaptiveSignedNormalizedActualTargetVariation_nonnegative
        support scale outcome domain index N (expected N)
    have inverse_nonnegative : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    have threshold_square :
        threshold ^ 2 =
          scaleAdaptiveSignedNormalizedActualTargetVariation
            support scale outcome domain index N (expected N) +
            (N : ℝ)⁻¹ := by
      dsimp [threshold, scaleAdaptiveSignedAdaptiveTargetTolerance]
      exact Real.sq_sqrt (add_nonneg variation_nonnegative inverse_nonnegative)
    apply (mul_le_mul_iff_of_pos_right threshold_positive).mp
    calc
      _ ≤ scaleAdaptiveSignedNormalizedActualTargetVariation
        support scale outcome domain index N (expected N) := markov
      _ ≤ threshold ^ 2 := by
        rw [threshold_square]
        exact le_add_of_nonneg_right inverse_nonnegative
      _ = _ := by ring

/-- ACTUAL one-cell, genuine distinct-prime-label correlation closure.

For every fixed nonempty signed constant-residue band, genuine mixed outcome,
positive active index, and unclipped OPEN typed-prime target cell, the sole
explicit signed Green--Tao proposition produces ONE canonical singular such
that:

* the actual inverse-degree/model tolerance tends to zero;
* the deleted actual typed targets have density zero;
* the retained targets have the FULL correct typed-prime density;
* their ACTUAL inverse-INTEGER-degree centered target variance tends to zero;
* equivalently, the complete same-label-plus-DISTINCT-prime-label centered
  correlation tends to zero at the true prime-target normalization.

Every target is `s*q` with an actual prime `q`, the true mean is `s/i`, the
GTZ upper endpoint is removed honestly, and no variance, correlation,
concentration, pointwise bound, covering, or matching premise is assumed.
This is a fixed single-type/single-index good-cell theorem, not the original
global Erdős #1139 conclusion. -/
theorem scaleAdaptiveConstantBand_actualTypedGoodCellCorrelation_tendsto_zero_of_GTZ
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
      let targetType := adaptiveMixedActualIndexType
        support outcome.1 index
      let band := scaleAdaptiveSignedConstantResidueBand
        support outcome.1 lower upper
      let targets : ℕ → Finset ℕ := fun N =>
        scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
          targetType targetLower targetUpper N
      let expected : ℕ → ℝ := fun N =>
        scaleAdaptiveSignedConstantResidueBandExpectedDegree
          support scale outcome lower upper singular N
      let tolerance : ℕ → ℝ := fun N =>
        scaleAdaptiveSignedAdaptiveTargetTolerance
          support scale outcome band index N (expected N)
      let good : ℕ → Finset ℕ := fun N =>
        scaleAdaptiveSignedUnitGoodTargets
          support scale outcome band index N (targets N)
            (expected N) (tolerance N)
      let mean : ℝ := (targetType : ℝ) / (index : ℝ)
      let density : ℝ :=
        ((targetUpper : ℝ) - (targetLower : ℝ)) / (targetType : ℝ)
      Tendsto tolerance atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedUnitBadTargets
            support scale outcome band index N (targets N)
              (expected N) (tolerance N)).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ => ((good N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds density) ∧
      Tendsto
        (fun N : ℕ =>
          scaleAdaptivePrimeLabelNormalizedWeight N *
            (∑ target ∈ good N,
              (scaleAdaptiveSignedUnitActualTargetLoad
                support scale outcome band index N target - mean) ^ 2))
        atTop (nhds (0 : ℝ)) ∧
      Tendsto
        (fun N : ℕ =>
          scaleAdaptivePrimeLabelNormalizedWeight N *
            scaleAdaptiveSignedActualCenteredCorrelation
              support scale outcome band index N (good N) mean)
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, singular_positive, singular_converges,
      _full_degree, variation⟩ :=
    scaleAdaptiveSignedConstantResidueBand_canonicalActualTransfer_of_GTZ
      green_tao support scale outcome index lower upper primes
      lower_nonnegative band_nonempty upper_bounded
  obtain ⟨model_singular, _model_positive, model_converges, model_variance⟩ :=
    scaleAdaptiveConstantBand_openTypedModelVariance_tendsto_zero_of_GTZ
      green_tao support scale outcome index targetLower targetUpper
      lower upper primes active index_positive lower_nonnegative
      band_nonempty upper_bounded target_nonempty
      interior_lower interior_upper
  have singular_same :=
    tendsto_nhds_unique singular_converges model_converges
  subst model_singular
  let targetType := adaptiveMixedActualIndexType
    support outcome.1 index
  let band := scaleAdaptiveSignedConstantResidueBand
    support outcome.1 lower upper
  let targets : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
      targetType targetLower targetUpper N
  let expected : ℕ → ℝ := fun N =>
    scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper singular N
  let tolerance : ℕ → ℝ := fun N =>
    scaleAdaptiveSignedAdaptiveTargetTolerance
      support scale outcome band index N (expected N)
  let good : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveSignedUnitGoodTargets
      support scale outcome band index N (targets N)
        (expected N) (tolerance N)
  let mean : ℝ := (targetType : ℝ) / (index : ℝ)
  let density : ℝ :=
    ((targetUpper : ℝ) - (targetLower : ℝ)) / (targetType : ℝ)
  have type_positive : 0 < targetType :=
    adaptiveMixedActualIndexType_pos_of_active primes active
  have lower_positive : 0 < targetLower := by
    have index_real : (0 : ℝ) < index := by
      exact_mod_cast index_positive
    have upper_positive : (0 : ℝ) < upper :=
      lt_of_le_of_lt lower_nonnegative band_nonempty
    have target_real : (0 : ℝ) < targetLower := by
      linarith
    exact_mod_cast target_real
  have physical_upper : targetUpper ≤ 2 * (index + 1) := by
    have lower_bounded : lower ≤ (1 : ℝ) :=
      band_nonempty.le.trans upper_bounded
    have cast_bound :
        (targetUpper : ℝ) ≤ (2 * (index + 1) : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast cast_bound
  have supported : ∀ N : ℕ,
      targets N ⊆ scaleAdaptiveGTZIndexedTargetWindow index N := by
    intro N
    exact scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell_subset_window
      targetType targetLower targetUpper index N type_positive physical_upper
  have variation' :
      Tendsto
        (fun N : ℕ => scaleAdaptiveSignedNormalizedActualTargetVariation
          support scale outcome band index N (expected N))
        atTop (nhds (0 : ℝ)) := by
    simpa [band, expected] using variation
  obtain ⟨tolerance_zero, bad_zero⟩ :=
    scaleAdaptiveSignedAdaptiveBadTargets_tendsto_zero_of_variation
      support scale outcome band index targets expected supported variation'
  have target_density :
      Tendsto
        (fun N : ℕ => ((targets N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds density) := by
    exact scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell_normalized_tendsto
      targetType targetLower targetUpper type_positive lower_positive
      target_nonempty.le
  have good_density :
      Tendsto
        (fun N : ℕ => ((good N).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds density) :=
    scaleAdaptiveSignedUnitGoodTargets_normalizedDensity_tendsto
      support scale outcome band index targets expected tolerance
      density target_density bad_zero
  have target_bounded : ∀ᶠ N : ℕ in atTop,
      ((targets N).card : ℝ) *
        scaleAdaptivePrimeLabelNormalizedWeight N ≤ density + 1 := by
    filter_upwards
      [(tendsto_order.1 target_density).2 (density + 1) (by linarith)]
        with N bounded
    exact bounded.le
  have model :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptivePrimeLabelNormalizedWeight N *
            (∑ target ∈ targets N,
              (scaleAdaptiveSignedUnitModelTargetLoad
                support scale outcome band index N target
                  (expected N) - mean) ^ 2))
        atTop (nhds (0 : ℝ)) := by
    simpa [targetType, band, targets, expected, mean] using model_variance
  have actual_variance :=
    scaleAdaptiveSignedAdaptiveGoodVariance_tendsto_zero_of_model
      support scale outcome band index targets expected
      (fun _N _target => mean) (density + 1)
      target_bounded variation' model
  have actual_variance' :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptivePrimeLabelNormalizedWeight N *
            (∑ target ∈ good N,
              (scaleAdaptiveSignedUnitActualTargetLoad
                support scale outcome band index N target - mean) ^ 2))
        atTop (nhds (0 : ℝ)) := by
    simpa [good, tolerance] using actual_variance
  have correlation :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptivePrimeLabelNormalizedWeight N *
            scaleAdaptiveSignedActualCenteredCorrelation
              support scale outcome band index N (good N) mean)
        atTop (nhds (0 : ℝ)) := by
    apply actual_variance'.congr'
    exact Filter.Eventually.of_forall fun N => by
      dsimp only
      rw [scaleAdaptiveSignedActualCenteredCorrelation_eq_centeredVariance]
      rfl
  exact ⟨singular, singular_positive, singular_converges,
    tolerance_zero, bad_zero, good_density, actual_variance', correlation⟩


end Erdos1139
