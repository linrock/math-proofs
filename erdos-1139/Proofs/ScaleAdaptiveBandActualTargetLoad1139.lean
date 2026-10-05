module

public import ScaleAdaptiveBandPositiveTargetLoad1139
public import ScaleAdaptiveConstantBandTypedGlobalAssembly1139

@[expose] public section


/-!
# Actual inverse-degree load on BOTH adjacent physical target cells

The genuine physical-index shell `m < i < 2*m` is simultaneously unclipped
on the even target cell `(2*m,2*m+1)` and the adjacent odd target cell
`(2*m+1,2*m+2)`.  For each actual signed mixed-prime pattern the existing
Green--Tao bridge proves centered variance for the true INVERSE-INTEGER-
DEGREE sampler after deleting a zero-density set of real prime targets.

This file combines that deletion with finite Chebyshev, takes one finite
union over genuine shared outcomes and physical indices, and obtains the
same strictly positive `F/8` lower bound for actual prime and supported
semiprime target loads on BOTH cells.  Every support, scale, outcome
family, and index set is fixed before the prime-label scale tends to
infinity.  The only analytic theorem parameter is the explicit signed
Green--Tao proposition; no model `μ/D` is substituted for actual `μ/d`.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- The same genuine physical indices are unclipped on BOTH adjacent
normalized target cells.  The parity coordinate is an actual natural
number bounded by one, not an independently shifted target pattern. -/
theorem scaleAdaptiveBandInteriorIndices_unclipped_adjacent
    {m index parity : ℕ} {lower upper : ℝ}
    (lower_nonnegative : 0 ≤ lower)
    (upper_bounded : upper ≤ 1)
    (selected : index ∈ scaleAdaptiveBandInteriorIndices m)
    (parity_bounded : parity ≤ 1) :
    (index : ℝ) + upper ≤ (2 * m + parity : ℕ) ∧
      (2 * m + parity + 1 : ℕ) ≤ 2 * (index : ℝ) + lower := by
  have bounds := scaleAdaptiveBandInteriorIndices_mem selected
  have upper_index : index + 1 ≤ 2 * m + parity := by omega
  have lower_index : 2 * m + parity + 1 ≤ 2 * index := by omega
  have upper_real : (index : ℝ) + 1 ≤ (2 * m + parity : ℕ) := by
    exact_mod_cast upper_index
  have lower_real : (2 * m + parity + 1 : ℕ) ≤ 2 * (index : ℝ) := by
    exact_mod_cast lower_index
  constructor <;> linarith

/-- The ACTUAL one-pattern target load, with genuine prime labels and
inverse-INTEGER-degree weights `1/dθ(p)`.  This is deliberately the full
constant-residue-band sampler, not the expected-degree `1/Dθ` model. -/
noncomputable def scaleAdaptiveBandActualInverseTargetLoad
    (support : Finset ℕ) (scale : ℕ) (lower upper : ℝ)
    (index : ℕ) (outcome : ℕ × ℕ) (N target : ℕ) : ℝ :=
  scaleAdaptiveSignedUnitActualTargetLoad
    support scale outcome
      (scaleAdaptiveSignedConstantResidueBand
        support outcome.1 lower upper)
      index N target

/-- The actual OPEN typed-prime target cell of either physical parity.
Every member is `s*q` for a genuine prime `q`; both moving endpoints are
strict, as required by the signed convex Green--Tao domains. -/
def scaleAdaptiveBandAdjacentTypedTargets
    (targetType m parity N : ℕ) : Finset ℕ :=
  scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
    targetType (2 * m + parity) (2 * m + parity + 1) N

/-- If an actual target variance is known only AFTER deleting a
zero-density target set, then the full target set still has zero-density
half-mean failures.  The proof retains the deleted targets explicitly
instead of treating an untruncated actual second moment as proved. -/
theorem scaleAdaptiveBandLowTargets_normalized_card_tendsto_zero_of_good
    (targets deleted : ℕ → Finset ℕ)
    (load : ℕ → ℕ → ℝ) (mean cutoff : ℝ)
    (gap : cutoff < mean)
    (deleted_density : Tendsto
      (fun N : ℕ =>
        ((deleted N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)))
    (good_energy : Tendsto
      (fun N : ℕ =>
        (∑ target ∈ targets N \ deleted N,
          (load N target - mean) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveBandLowTargets
          (targets N) (load N) cutoff).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  let good : ℕ → Finset ℕ := fun N => targets N \ deleted N
  have good_low := scaleAdaptiveBandLowTargets_normalized_card_tendsto_zero
    good load mean cutoff gap good_energy
  have combined : Tendsto
      (fun N : ℕ =>
        ((deleted N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ) +
          ((scaleAdaptiveBandLowTargets
            (good N) (load N) cutoff).card : ℝ) *
              Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
    simpa using deleted_density.add good_low
  apply squeeze_zero' _ _ combined
  · filter_upwards [eventually_ge_atTop 2] with N large
    have log_nonnegative : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ N by omega)
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) log_nonnegative)
        (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with N large
    have N_positive : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have log_nonnegative : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ N by omega)
    have contained :
        scaleAdaptiveBandLowTargets
          (targets N) (load N) cutoff ⊆
            deleted N ∪
              scaleAdaptiveBandLowTargets
                (good N) (load N) cutoff := by
      intro target selected
      obtain ⟨in_targets, below⟩ := Finset.mem_filter.mp selected
      by_cases removed : target ∈ deleted N
      · exact Finset.mem_union_left _ removed
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_sdiff.mpr ⟨in_targets, removed⟩, below⟩
    have cardinal :
        ((scaleAdaptiveBandLowTargets
          (targets N) (load N) cutoff).card : ℝ) ≤
          ((deleted N).card : ℝ) +
            ((scaleAdaptiveBandLowTargets
              (good N) (load N) cutoff).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card contained).trans
        (Finset.card_union_le _ _)
    have weighted := mul_le_mul_of_nonneg_right cardinal
      (div_nonneg log_nonnegative N_positive.le)
    calc
      ((scaleAdaptiveBandLowTargets
        (targets N) (load N) cutoff).card : ℝ) *
          Real.log (N : ℝ) / (N : ℝ) =
        ((scaleAdaptiveBandLowTargets
          (targets N) (load N) cutoff).card : ℝ) *
            (Real.log (N : ℝ) / (N : ℝ)) := by ring
      _ ≤ (((deleted N).card : ℝ) +
            ((scaleAdaptiveBandLowTargets
              (good N) (load N) cutoff).card : ℝ)) *
              (Real.log (N : ℝ) / (N : ℝ)) := weighted
      _ = _ := by ring

/-- For ONE genuine shared outcome and physical index, the actual
inverse-INTEGER-degree load falls below half its true typed mean on only
`o(N/log N)` genuine OPEN typed-prime targets.  The auxiliary expected
degree appears solely in the proved deletion certificate, never in the
load being bounded. -/
theorem scaleAdaptiveBandActualPatternLowTargets_tendsto_zero_of_GTZ
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
    let targetType := adaptiveMixedActualIndexType
      support outcome.1 index
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveBandLowTargets
          (scaleAdaptiveTypedPrimeTargetsInOpenIntegerCell
            targetType targetLower targetUpper N)
          (scaleAdaptiveBandActualInverseTargetLoad
            support scale lower upper index outcome N)
          ((1 / 2 : ℝ) * ((targetType : ℝ) / (index : ℝ)))).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, _singular_positive, _converges,
      _tolerance_zero, deleted_density, _good_density,
      good_variance, _correlation⟩ :=
    scaleAdaptiveConstantBand_actualTypedGoodCellCorrelation_tendsto_zero_of_GTZ
      green_tao support scale outcome index targetLower targetUpper
        lower upper primes active index_positive lower_nonnegative
        band_nonempty upper_bounded target_nonempty
        interior_lower interior_upper
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
  let removed : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveSignedUnitBadTargets
      support scale outcome band index N (targets N)
        (expected N) (tolerance N)
  let actual : ℕ → ℕ → ℝ := fun N target =>
    scaleAdaptiveBandActualInverseTargetLoad
      support scale lower upper index outcome N target
  let mean : ℝ := (targetType : ℝ) / (index : ℝ)
  have type_positive : 0 < targetType :=
    adaptiveMixedActualIndexType_pos_of_active primes active
  have mean_positive : 0 < mean := by
    have positive_type : (0 : ℝ) < targetType := by
      exact_mod_cast type_positive
    have positive_index : (0 : ℝ) < index := by
      exact_mod_cast index_positive
    exact div_pos positive_type positive_index
  have removed_zero : Tendsto
      (fun N : ℕ =>
        ((removed N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
    convert deleted_density using 1
    ext N
    dsimp [removed, tolerance, expected, targets,
      targetType, band, scaleAdaptivePrimeLabelNormalizedWeight]
    ring
  have actual_good_energy : Tendsto
      (fun N : ℕ =>
        (∑ target ∈ targets N \ removed N,
          (actual N target - mean) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
    convert good_variance using 1
    ext N
    dsimp [removed, tolerance, expected, targets,
      targetType, band, actual, mean,
      scaleAdaptiveBandActualInverseTargetLoad,
      scaleAdaptiveSignedUnitGoodTargets,
      scaleAdaptivePrimeLabelNormalizedWeight]
    ring
  exact scaleAdaptiveBandLowTargets_normalized_card_tendsto_zero_of_good
    targets removed actual mean ((1 / 2 : ℝ) * mean)
      (by linarith) removed_zero actual_good_energy

/-- The complete FINITE shared-outcome/index bad set for genuine PRIME
targets in either adjacent cell has prime-scale density zero.  Each
underlying load uses actual inverse integer pattern degrees. -/
theorem scaleAdaptiveBandActualPrimeBadTargets_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale m parity : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (within_scale : 2 * m ≤ scale + 1)
    (parity_bounded : parity ≤ 1)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveBandPrimeBadTargets support scale m
          (scaleAdaptiveBandAdjacentTypedTargets 1 m parity)
          (scaleAdaptiveBandActualInverseTargetLoad
            support scale lower upper) N).card : ℝ) *
              Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveBandPrimeBadTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro index indexed
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro outcome sample
  have bounds := scaleAdaptiveBandInteriorIndices_mem indexed
  have index_positive : 0 < index := by omega
  have active := scaleAdaptiveBandPrimeSample_index_active
    within_scale indexed sample
  have exact_type := scaleAdaptiveBandPrimeSample_actual_type sample
  have unclipped := scaleAdaptiveBandInteriorIndices_unclipped_adjacent
    lower_nonnegative upper_bounded indexed parity_bounded
  have individual := scaleAdaptiveBandActualPatternLowTargets_tendsto_zero_of_GTZ
    green_tao support scale outcome index
      (2 * m + parity) (2 * m + parity + 1)
      lower upper primes active index_positive lower_nonnegative
        band_nonempty upper_bounded (by omega)
          unclipped.1 unclipped.2
  rw [exact_type] at individual
  simpa [scaleAdaptiveBandAdjacentTypedTargets, one_div] using individual

/-- The complete finite shared-outcome/index bad set for EVERY supported
genuine semiprime type has prime-scale density zero on either adjacent
physical cell.  No independently sampled outcome is inserted. -/
theorem scaleAdaptiveBandActualSemiprimeBadTargets_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    {support : Finset ℕ} {targetType : ℕ}
    (scale m parity : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : targetType ∈ support)
    (within_scale : 2 * m ≤ scale + 1)
    (parity_bounded : parity ≤ 1)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveBandSemiprimeBadTargets
          support targetType scale m
          (scaleAdaptiveBandAdjacentTypedTargets
            targetType m parity)
          (scaleAdaptiveBandActualInverseTargetLoad
            support scale lower upper) N).card : ℝ) *
              Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveBandSemiprimeBadTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro index indexed
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro outcome sample
  have bounds := scaleAdaptiveBandInteriorIndices_mem indexed
  have index_positive : 0 < index := by omega
  have active := scaleAdaptiveBandSemiprimeSample_index_active
    type_supported within_scale indexed sample
  have exact_type := scaleAdaptiveBandSemiprimeSample_actual_type
    type_supported sample
  have unclipped := scaleAdaptiveBandInteriorIndices_unclipped_adjacent
    lower_nonnegative upper_bounded indexed parity_bounded
  have individual := scaleAdaptiveBandActualPatternLowTargets_tendsto_zero_of_GTZ
    green_tao support scale outcome index
      (2 * m + parity) (2 * m + parity + 1)
      lower upper primes active index_positive lower_nonnegative
        band_nonempty upper_bounded (by omega)
          unclipped.1 unclipped.2
  rw [exact_type] at individual
  simpa [scaleAdaptiveBandAdjacentTypedTargets, div_eq_mul_inv] using individual

/-- Genuine prime targets in BOTH adjacent physical cells receive actual
shared-outcome inverse-INTEGER-degree load at least `F/8`, except on a
prime-density-zero finite exceptional union.  The only analytic premise is
the explicit fixed-system signed Green--Tao proposition. -/
theorem scaleAdaptiveBandActualPrime_positive_on_both_cells_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale m parity : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (large : 2 ≤ m)
    (within_scale : 2 * m ≤ scale + 1)
    (parity_bounded : parity ≤ 1)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ bad : ℕ → Finset ℕ,
      Tendsto
        (fun N : ℕ =>
          ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) ∧
      ∀ N target,
        target ∈ scaleAdaptiveBandAdjacentTypedTargets
          1 m parity N →
        target ∉ bad N →
          adaptivePatternEulerFactor support scale / 8 ≤
            scaleAdaptiveBandPrimeOutcomeLoad
              support scale m
                (fun index outcome =>
                  scaleAdaptiveBandActualInverseTargetLoad
                    support scale lower upper index outcome N)
                target := by
  let targets := scaleAdaptiveBandAdjacentTypedTargets 1 m parity
  let actual := scaleAdaptiveBandActualInverseTargetLoad
    support scale lower upper
  let bad := scaleAdaptiveBandPrimeBadTargets
    support scale m targets actual
  refine ⟨bad, ?_, ?_⟩
  · exact scaleAdaptiveBandActualPrimeBadTargets_tendsto_zero_of_GTZ
      green_tao support scale m parity lower upper primes
        within_scale parity_bounded lower_nonnegative
          band_nonempty upper_bounded
  · intro N target selected good
    exact scaleAdaptiveBandPrimeOutcomeLoad_ge_outside_bad
      support scale m N target targets actual primes large selected good

/-- Every genuine supported semiprime type has the SAME actual `F/8`
target-load lower bound in BOTH adjacent physical cells.  Its exact joint
sample marginal `F/s` cancels its true conditional mean `s/i`; every edge
uses the genuine inverse integer degree `1/dθ(p)`. -/
theorem scaleAdaptiveBandActualSemiprime_positive_on_both_cells_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    {support : Finset ℕ} {targetType : ℕ}
    (scale m parity : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : targetType ∈ support)
    (large : 2 ≤ m)
    (within_scale : 2 * m ≤ scale + 1)
    (parity_bounded : parity ≤ 1)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ bad : ℕ → Finset ℕ,
      Tendsto
        (fun N : ℕ =>
          ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) ∧
      ∀ N target,
        target ∈ scaleAdaptiveBandAdjacentTypedTargets
          targetType m parity N →
        target ∉ bad N →
          adaptivePatternEulerFactor support scale / 8 ≤
            scaleAdaptiveBandSemiprimeOutcomeLoad
              support targetType scale m
                (fun index outcome =>
                  scaleAdaptiveBandActualInverseTargetLoad
                    support scale lower upper index outcome N)
                target := by
  let targets := scaleAdaptiveBandAdjacentTypedTargets
    targetType m parity
  let actual := scaleAdaptiveBandActualInverseTargetLoad
    support scale lower upper
  let bad := scaleAdaptiveBandSemiprimeBadTargets
    support targetType scale m targets actual
  refine ⟨bad, ?_, ?_⟩
  · exact scaleAdaptiveBandActualSemiprimeBadTargets_tendsto_zero_of_GTZ
      green_tao scale m parity lower upper primes type_supported
        within_scale parity_bounded lower_nonnegative
          band_nonempty upper_bounded
  · intro N target selected good
    exact scaleAdaptiveBandSemiprimeOutcomeLoad_ge_outside_bad
      scale m N target targets actual primes type_supported
        large selected good

end Erdos1139

