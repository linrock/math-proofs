module

public import ScaleAdaptiveBandIndexAggregation1139
public import ScaleAdaptiveConstantBandTargetConcentration1139

@[expose] public section


/-!
# Positive true-target load from finitely many genuine band patterns

For each fixed support/scale, there are finitely many genuine shared-outcome
patterns and physical indices.  A centered target-energy limit for each
actual prime-pattern fiber removes only `o(N/log N)` typed targets; the
finite UNION of these exceptional sets still has that density.

On every remaining typed target, each normalized actual pattern load is at
least half its true mean.  The exact shared-sample marginals are `F` for
prime targets and `F/s` for semiprime type `s`, while the corresponding
means are `1/i` and `s/i`.  Thus the same positive lower bound `F/8`
holds for both target types over the genuine shell `m<i<2*m`.

All family sizes are FIXED before taking `N→∞`; no uniformity in growing
pattern complexity, independent outcome resampling, prime witness, target
cover, or extra correlation premise is asserted.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- The actual finite low-load target set associated with any specified
true targetwise pattern load. -/
noncomputable def scaleAdaptiveBandLowTargets
    (targets : Finset ℕ) (load : ℕ → ℝ) (cutoff : ℝ) : Finset ℕ :=
  targets.filter fun target => load target < cutoff

/-- Honest finite Chebyshev deletion for arbitrary ACTUAL targetwise loads.
Every low-load target contributes at least the squared positive gap. -/
theorem scaleAdaptiveBandLowTargets_card_mul_sq_le_energy
    (targets : Finset ℕ) (load : ℕ → ℝ) (mean cutoff : ℝ)
    (below : cutoff ≤ mean) :
    ((scaleAdaptiveBandLowTargets targets load cutoff).card : ℝ) *
      (mean - cutoff) ^ 2 ≤
        ∑ target ∈ targets, (load target - mean) ^ 2 := by
  classical
  let bad := scaleAdaptiveBandLowTargets targets load cutoff
  calc
    ((bad.card : ℕ) : ℝ) * (mean - cutoff) ^ 2 =
        ∑ _target ∈ bad, (mean - cutoff) ^ 2 := by simp
    _ ≤ ∑ target ∈ bad, (load target - mean) ^ 2 := by
      apply Finset.sum_le_sum
      intro target selected
      have low := (Finset.mem_filter.mp selected).2
      nlinarith [sq_nonneg (load target - cutoff)]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro target _ _
        exact sq_nonneg _

/-- A genuine normalized centered target-energy limit implies vanishing
prime-scale density of the corresponding low-load ACTUAL targets. -/
theorem scaleAdaptiveBandLowTargets_normalized_card_tendsto_zero
    (targets : ℕ → Finset ℕ) (load : ℕ → ℕ → ℝ)
    (mean cutoff : ℝ) (gap : cutoff < mean)
    (energy : Tendsto
      (fun N : ℕ =>
        (∑ target ∈ targets N, (load N target - mean) ^ 2) *
          Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveBandLowTargets
          (targets N) (load N) cutoff).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have gap_positive : 0 < (mean - cutoff) ^ 2 := sq_pos_of_pos (by linarith)
  have divided :
      Tendsto
        (fun N : ℕ =>
          ((∑ target ∈ targets N, (load N target - mean) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ)) /
            (mean - cutoff) ^ 2)
        atTop (nhds (0 : ℝ)) := by
    simpa using energy.div_const ((mean - cutoff) ^ 2)
  apply squeeze_zero' _ _ divided
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
    have finite := scaleAdaptiveBandLowTargets_card_mul_sq_le_energy
      (targets N) (load N) mean cutoff gap.le
    apply (le_div_iff₀ gap_positive).mpr
    have weighted := mul_le_mul_of_nonneg_right finite
      (div_nonneg log_nonnegative N_positive.le)
    convert weighted using 1 <;> ring

/-- An ACTUAL finite union of finitely many independently verified
prime-scale negligible bad-target sets remains prime-scale negligible.
The family is fixed BEFORE taking the target-scale limit. -/
theorem scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
    {α : Type*} [DecidableEq α]
    (family : Finset α) (bad : α → ℕ → Finset ℕ)
    (negligible : ∀ item ∈ family,
      Tendsto
        (fun N : ℕ =>
          ((bad item N).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((family.biUnion fun item => bad item N).card : ℝ) *
          Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have summed :
      Tendsto
        (fun N : ℕ =>
          ∑ item ∈ family,
            ((bad item N).card : ℝ) *
              Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_finsetSum family negligible
  apply squeeze_zero' _ _ summed
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
    have card_bound :
        ((family.biUnion fun item => bad item N).card : ℝ) ≤
          ∑ item ∈ family, ((bad item N).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le
        (s := family) (t := fun item => bad item N))
    have weighted := mul_le_mul_of_nonneg_right card_bound
      (div_nonneg log_nonnegative N_positive.le)
    calc
      ((family.biUnion fun item => bad item N).card : ℝ) *
          Real.log (N : ℝ) / (N : ℝ) =
        ((family.biUnion fun item => bad item N).card : ℝ) *
          (Real.log (N : ℝ) / (N : ℝ)) := by ring
      _ ≤ (∑ item ∈ family, ((bad item N).card : ℝ)) *
          (Real.log (N : ℝ) / (N : ℝ)) := weighted
      _ = ∑ item ∈ family,
          ((bad item N).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro item _
        ring

/-- Actual one-common-outcome PRIME-target load aggregated over all true
physical indices and their genuine prime-type pattern samples. -/
noncomputable def scaleAdaptiveBandPrimeOutcomeLoad
    (support : Finset ℕ) (scale m : ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℝ) (target : ℕ) : ℝ :=
  ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
    ∑ outcome ∈ adaptiveMixedPrimePatternSamples support scale index,
      load index outcome target /
        ((adaptiveMixedTypeModulus support *
          adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)

/-- Actual one-common-outcome SEMIPRIME-target load aggregated over the SAME
physical-index shell and the genuine joint samples of its supported type. -/
noncomputable def scaleAdaptiveBandSemiprimeOutcomeLoad
    (support : Finset ℕ) (type scale m : ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℝ) (target : ℕ) : ℝ :=
  ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
    ∑ outcome ∈ adaptiveMixedSemiprimePatternSamples
      support type scale index,
      load index outcome target /
        ((adaptiveMixedTypeModulus support *
          adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)

/-- The true finite joint-outcome denominator is positive; division by its
cardinality is never treated as an independent-resampling probability. -/
theorem scaleAdaptiveBandOutcomeDenominator_pos
    (support : Finset ℕ) (scale : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (0 : ℝ) <
      ((adaptiveMixedTypeModulus support *
        adaptiveMixedOutsideModulus support scale : ℕ) : ℝ) := by
  exact_mod_cast Nat.mul_pos
    (adaptiveMixedTypeModulus_pos support primes)
    (adaptiveMixedOutsideModulus_pos support scale)

/-- Every prime-type sample carries its ACTUAL type certificate `s=1`, not
merely a declared external target color. -/
theorem scaleAdaptiveBandPrimeSample_actual_type
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (sample : outcome ∈ adaptiveMixedPrimePatternSamples
      support scale index) :
    adaptiveMixedActualIndexType support outcome.1 index = 1 := by
  have coordinates :
      outcome.1 ∈ adaptiveMixedPrimeTypeCenters support index ∧
        outcome.2 ∈ adaptiveMixedOutsideSurvivors support scale index := by
    simpa [adaptiveMixedPrimePatternSamples, Finset.product_eq_sprod]
      using sample
  have coprime := adaptiveMixedPrimeTypeCenter_actual_coprime coordinates.1
  exact Nat.coprime_iff_gcd_eq_one.mp coprime

/-- Every supported semiprime sample has EXACTLY the claimed genuine gcd
type `s`; no cross-type pattern is included in its target family. -/
theorem scaleAdaptiveBandSemiprimeSample_actual_type
    {support : Finset ℕ} {type scale index : ℕ} {outcome : ℕ × ℕ}
    (type_supported : type ∈ support)
    (sample : outcome ∈ adaptiveMixedSemiprimePatternSamples
      support type scale index) :
    adaptiveMixedActualIndexType support outcome.1 index = type := by
  have coordinates :
      outcome.1 ∈ adaptiveMixedSemiprimeTypeCenters support type index ∧
        outcome.2 ∈ adaptiveMixedOutsideSurvivors support scale index := by
    simpa [adaptiveMixedSemiprimePatternSamples,
      Finset.product_eq_sprod] using sample
  exact adaptiveMixedSemiprimeTypeCenter_actual_gcd_eq_type
    type_supported coordinates.1

/-- The TRUE degree-normalized actual signed prime-pattern TARGET fiber
on the shared physical interior cell `(2*m*N,(2*m+1)*N)`.  One singular
coefficient is attached to each COMMON outcome, not resampled per target. -/
noncomputable def scaleAdaptiveBandActualModelTargetLoad
    (support : Finset ℕ) (scale m : ℕ) (lower upper : ℝ)
    (singular : (ℕ × ℕ) → ℝ)
    (index : ℕ) (outcome : ℕ × ℕ) (N target : ℕ) : ℝ :=
  ((scaleAdaptiveGTZIndexedTargetFiber
    support scale outcome
      (scaleAdaptiveTruncatedBandSignedDomain
        support outcome.1 index lower upper
          (2 * m : ℕ) (2 * m + 1 : ℕ))
      index N target).card : ℝ) /
    scaleAdaptiveSignedConstantResidueBandExpectedDegree
      support scale outcome lower upper (singular outcome) N

/-- The explicit original Green--Tao input supplies ONE positive actual
Euler singular limit for EACH shared outcome, simultaneously for the entire
finite (indeed unrestricted) outcome family.  This coefficient does not
depend on which physical target index of that outcome is later examined. -/
theorem scaleAdaptiveBand_common_outcome_singular_exists_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : (ℕ × ℕ) → ℝ,
      ∀ outcome : ℕ × ℕ,
        0 < singular outcome ∧
          Tendsto
            (adaptiveMixedSignedSingularPartialProduct
              support scale outcome)
            atTop (nhds (singular outcome)) := by
  have individual : ∀ outcome : ℕ × ℕ,
      ∃ value : ℝ, 0 < value ∧
        Tendsto
          (adaptiveMixedSignedSingularPartialProduct
            support scale outcome)
          atTop (nhds value) := by
    intro outcome
    obtain ⟨value, positive, converges, _⟩ :=
      scaleAdaptiveConstantBandIndexedTarget_firstMoment_of_GTZ
        green_tao support scale outcome 0 lower upper primes
          lower_nonnegative band_nonempty upper_bounded
    exact ⟨value, positive, converges⟩
  choose singular positive converges using individual
  exact ⟨singular, fun outcome =>
    ⟨positive outcome, converges outcome⟩⟩

/-- Outside the genuine finite exceptional union, the actual PRIME-target
joint load is at least `F/8`.  The hypothesis is pointwise half-mean only
for the true shared samples; finite Chebyshev produces this hypothesis
from the actual Green--Tao target energy. -/
theorem scaleAdaptiveBandPrimeOutcomeLoad_ge_factor_eighth
    (support : Finset ℕ) (scale m target : ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (large : 2 ≤ m)
    (good : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      ∀ outcome ∈ adaptiveMixedPrimePatternSamples
        support scale index,
          (1 / 2 : ℝ) * (index : ℝ)⁻¹ ≤
            load index outcome target) :
    adaptivePatternEulerFactor support scale / 8 ≤
      scaleAdaptiveBandPrimeOutcomeLoad
        support scale m load target := by
  let denominator : ℝ :=
    ((adaptiveMixedTypeModulus support *
      adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)
  have denominator_positive : 0 < denominator :=
    scaleAdaptiveBandOutcomeDenominator_pos support scale primes
  have profile := scaleAdaptiveBandPrimeIndexProfile_ge_factor_quarter
    support scale m primes large
  unfold scaleAdaptiveBandPrimeOutcomeLoad
  calc
    adaptivePatternEulerFactor support scale / 8 ≤
        (1 / 2 : ℝ) *
          (∑ index ∈ scaleAdaptiveBandInteriorIndices m,
            (((adaptiveMixedPrimePatternSamples
              support scale index).card : ℝ) / denominator) *
              (index : ℝ)⁻¹) := by
      dsimp [denominator]
      linarith
    _ = ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
          ∑ _outcome ∈ adaptiveMixedPrimePatternSamples
            support scale index,
              ((1 / 2 : ℝ) * (index : ℝ)⁻¹) / denominator := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
          ∑ outcome ∈ adaptiveMixedPrimePatternSamples
            support scale index,
              load index outcome target / denominator := by
      apply Finset.sum_le_sum
      intro index selected
      apply Finset.sum_le_sum
      intro outcome sample
      exact (div_le_div_iff_of_pos_right denominator_positive).mpr
        (good index selected outcome sample)

/-- Outside the genuine finite exceptional union, EVERY supported
SEMIPRIME target has the SAME positive lower bound `F/8`.  The actual
type-weight `s/i` cancels the joint sample marginal `F/s`. -/
theorem scaleAdaptiveBandSemiprimeOutcomeLoad_ge_factor_eighth
    {support : Finset ℕ} {type : ℕ}
    (scale m target : ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : type ∈ support)
    (large : 2 ≤ m)
    (good : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      ∀ outcome ∈ adaptiveMixedSemiprimePatternSamples
        support type scale index,
          (1 / 2 : ℝ) * ((type : ℝ) * (index : ℝ)⁻¹) ≤
            load index outcome target) :
    adaptivePatternEulerFactor support scale / 8 ≤
      scaleAdaptiveBandSemiprimeOutcomeLoad
        support type scale m load target := by
  let denominator : ℝ :=
    ((adaptiveMixedTypeModulus support *
      adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)
  have denominator_positive : 0 < denominator :=
    scaleAdaptiveBandOutcomeDenominator_pos support scale primes
  have profile := scaleAdaptiveBandSemiprimeIndexProfile_ge_factor_quarter
    scale m primes type_supported large
  unfold scaleAdaptiveBandSemiprimeOutcomeLoad
  calc
    adaptivePatternEulerFactor support scale / 8 ≤
        (1 / 2 : ℝ) *
          (∑ index ∈ scaleAdaptiveBandInteriorIndices m,
            (((adaptiveMixedSemiprimePatternSamples
              support type scale index).card : ℝ) / denominator) *
              ((type : ℝ) * (index : ℝ)⁻¹)) := by
      dsimp [denominator]
      linarith
    _ = ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
          ∑ _outcome ∈ adaptiveMixedSemiprimePatternSamples
            support type scale index,
              ((1 / 2 : ℝ) *
                ((type : ℝ) * (index : ℝ)⁻¹)) / denominator := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
          ∑ outcome ∈ adaptiveMixedSemiprimePatternSamples
            support type scale index,
              load index outcome target / denominator := by
      apply Finset.sum_le_sum
      intro index selected
      apply Finset.sum_le_sum
      intro outcome sample
      exact (div_le_div_iff_of_pos_right denominator_positive).mpr
        (good index selected outcome sample)

/-- The honest exceptional union over the FINITE shared-outcome PRIME
patterns, retaining the actual target set at every physical scale. -/
noncomputable def scaleAdaptiveBandPrimeBadTargets
    (support : Finset ℕ) (scale m : ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ) (N : ℕ) : Finset ℕ :=
  (scaleAdaptiveBandInteriorIndices m).biUnion fun index =>
    (adaptiveMixedPrimePatternSamples support scale index).biUnion
      fun outcome =>
        scaleAdaptiveBandLowTargets
          (targets N) (load index outcome N)
            ((1 / 2 : ℝ) * (index : ℝ)⁻¹)

/-- The honest exceptional union over all FINITE shared-outcome patterns of
one genuine supported semiprime type. -/
noncomputable def scaleAdaptiveBandSemiprimeBadTargets
    (support : Finset ℕ) (type scale m : ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ) (N : ℕ) : Finset ℕ :=
  (scaleAdaptiveBandInteriorIndices m).biUnion fun index =>
    (adaptiveMixedSemiprimePatternSamples
      support type scale index).biUnion fun outcome =>
        scaleAdaptiveBandLowTargets
          (targets N) (load index outcome N)
            ((1 / 2 : ℝ) * ((type : ℝ) * (index : ℝ)⁻¹))

/-- Finitely many GENUINE prime-pattern centered target-energy limits imply
one joint exceptional set of prime-scale density zero.  Pattern complexity
and family size are fixed before `N → ∞`. -/
theorem scaleAdaptiveBandPrimeBadTargets_normalized_card_tendsto_zero
    (support : Finset ℕ) (scale m : ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ)
    (energy : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      ∀ outcome ∈ adaptiveMixedPrimePatternSamples support scale index,
        Tendsto
          (fun N : ℕ =>
            (∑ target ∈ targets N,
              (load index outcome N target - (index : ℝ)⁻¹) ^ 2) *
                Real.log (N : ℝ) / (N : ℝ))
          atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveBandPrimeBadTargets
          support scale m targets load N).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveBandPrimeBadTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro index selected
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro outcome sample
  have bounds := scaleAdaptiveBandInteriorIndices_mem selected
  have index_positive : (0 : ℝ) < index := by
    exact_mod_cast (show 0 < index by omega)
  have positive : (0 : ℝ) < (index : ℝ)⁻¹ := by
    exact inv_pos.mpr index_positive
  apply scaleAdaptiveBandLowTargets_normalized_card_tendsto_zero
    (targets := targets) (load := load index outcome)
      (mean := (index : ℝ)⁻¹)
      (cutoff := (1 / 2 : ℝ) * (index : ℝ)⁻¹)
  · linarith
  · exact energy index selected outcome sample

/-- Finitely many GENUINE type-`s` pattern centered target-energy limits
likewise give one joint exceptional set of prime-scale density zero. -/
theorem scaleAdaptiveBandSemiprimeBadTargets_normalized_card_tendsto_zero
    {support : Finset ℕ} {type : ℕ} (scale m : ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ)
    (type_positive : 0 < type)
    (energy : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      ∀ outcome ∈ adaptiveMixedSemiprimePatternSamples
        support type scale index,
        Tendsto
          (fun N : ℕ =>
            (∑ target ∈ targets N,
              (load index outcome N target -
                ((type : ℝ) * (index : ℝ)⁻¹)) ^ 2) *
                  Real.log (N : ℝ) / (N : ℝ))
          atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveBandSemiprimeBadTargets
          support type scale m targets load N).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveBandSemiprimeBadTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro index selected
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro outcome sample
  have bounds := scaleAdaptiveBandInteriorIndices_mem selected
  have index_positive : (0 : ℝ) < index := by
    exact_mod_cast (show 0 < index by omega)
  have positive : (0 : ℝ) < (type : ℝ) * (index : ℝ)⁻¹ := by
    have cast_type : (0 : ℝ) < type := by
      exact_mod_cast type_positive
    exact mul_pos cast_type (inv_pos.mpr index_positive)
  apply scaleAdaptiveBandLowTargets_normalized_card_tendsto_zero
    (targets := targets) (load := load index outcome)
      (mean := (type : ℝ) * (index : ℝ)⁻¹)
      (cutoff := (1 / 2 : ℝ) *
        ((type : ℝ) * (index : ℝ)⁻¹))
  · linarith
  · exact energy index selected outcome sample

/-- Every genuine prime target outside the exact joint exceptional set has
TRUE shared-outcome aggregate load at least `F/8`. -/
theorem scaleAdaptiveBandPrimeOutcomeLoad_ge_outside_bad
    (support : Finset ℕ) (scale m N target : ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (large : 2 ≤ m)
    (selected : target ∈ targets N)
    (good : target ∉ scaleAdaptiveBandPrimeBadTargets
      support scale m targets load N) :
    adaptivePatternEulerFactor support scale / 8 ≤
      scaleAdaptiveBandPrimeOutcomeLoad
        support scale m (fun index outcome => load index outcome N)
          target := by
  apply scaleAdaptiveBandPrimeOutcomeLoad_ge_factor_eighth
    support scale m target _ primes large
  intro index indexed outcome sample
  apply le_of_not_gt
  intro low
  apply good
  apply Finset.mem_biUnion.mpr
  refine ⟨index, indexed, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨outcome, sample, ?_⟩
  exact Finset.mem_filter.mpr ⟨selected, low⟩

/-- Every genuine supported semiprime target outside the exact joint
exceptional set has the SAME TRUE shared-outcome aggregate load `F/8`. -/
theorem scaleAdaptiveBandSemiprimeOutcomeLoad_ge_outside_bad
    {support : Finset ℕ} {type : ℕ}
    (scale m N target : ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : type ∈ support)
    (large : 2 ≤ m)
    (selected : target ∈ targets N)
    (good : target ∉ scaleAdaptiveBandSemiprimeBadTargets
      support type scale m targets load N) :
    adaptivePatternEulerFactor support scale / 8 ≤
      scaleAdaptiveBandSemiprimeOutcomeLoad
        support type scale m (fun index outcome => load index outcome N)
          target := by
  apply scaleAdaptiveBandSemiprimeOutcomeLoad_ge_factor_eighth
    scale m target _ primes type_supported large
  intro index indexed outcome sample
  apply le_of_not_gt
  intro low
  apply good
  apply Finset.mem_biUnion.mpr
  refine ⟨index, indexed, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨outcome, sample, ?_⟩
  exact Finset.mem_filter.mpr ⟨selected, low⟩

/-- Exact finite-family bridge: genuine per-pattern centered energy gives
positive shared-outcome PRIME load on all but `o(N/log N)` actual targets.
This lemma is purely combinatorial; the specialized Green--Tao capstone
below supplies its energies from ACTUAL prime fibers. -/
theorem scaleAdaptiveBandPrime_positive_on_density_one_of_energies
    (support : Finset ℕ) (scale m : ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (large : 2 ≤ m)
    (energy : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      ∀ outcome ∈ adaptiveMixedPrimePatternSamples support scale index,
        Tendsto
          (fun N : ℕ =>
            (∑ target ∈ targets N,
              (load index outcome N target - (index : ℝ)⁻¹) ^ 2) *
                Real.log (N : ℝ) / (N : ℝ))
          atTop (nhds (0 : ℝ))) :
    ∃ bad : ℕ → Finset ℕ,
      Tendsto
        (fun N : ℕ =>
          ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) ∧
      ∀ N target, target ∈ targets N → target ∉ bad N →
        adaptivePatternEulerFactor support scale / 8 ≤
          scaleAdaptiveBandPrimeOutcomeLoad
            support scale m
              (fun index outcome => load index outcome N) target := by
  refine ⟨scaleAdaptiveBandPrimeBadTargets
    support scale m targets load, ?_, ?_⟩
  · exact scaleAdaptiveBandPrimeBadTargets_normalized_card_tendsto_zero
      support scale m targets load energy
  · intro N target selected good
    exact scaleAdaptiveBandPrimeOutcomeLoad_ge_outside_bad
      support scale m N target targets load primes large selected good

/-- Exact finite-family bridge for EVERY genuine supported SEMIPRIME type;
its positive density-one load is independent of the actual type. -/
theorem scaleAdaptiveBandSemiprime_positive_on_density_one_of_energies
    {support : Finset ℕ} {type : ℕ} (scale m : ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : type ∈ support)
    (large : 2 ≤ m)
    (energy : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      ∀ outcome ∈ adaptiveMixedSemiprimePatternSamples
        support type scale index,
        Tendsto
          (fun N : ℕ =>
            (∑ target ∈ targets N,
              (load index outcome N target -
                ((type : ℝ) * (index : ℝ)⁻¹)) ^ 2) *
                  Real.log (N : ℝ) / (N : ℝ))
          atTop (nhds (0 : ℝ))) :
    ∃ bad : ℕ → Finset ℕ,
      Tendsto
        (fun N : ℕ =>
          ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) ∧
      ∀ N target, target ∈ targets N → target ∉ bad N →
        adaptivePatternEulerFactor support scale / 8 ≤
          scaleAdaptiveBandSemiprimeOutcomeLoad
            support type scale m
              (fun index outcome => load index outcome N) target := by
  refine ⟨scaleAdaptiveBandSemiprimeBadTargets
    support type scale m targets load, ?_, ?_⟩
  · exact scaleAdaptiveBandSemiprimeBadTargets_normalized_card_tendsto_zero
      scale m targets load (primes type type_supported).pos energy
  · intro N target selected good
    exact scaleAdaptiveBandSemiprimeOutcomeLoad_ge_outside_bad
      scale m N target targets load primes type_supported large selected good

/-- DIRECT genuine PRIME-target positive-load theorem from the explicit
signed Green--Tao input.  One certified Euler singular is shared by every
physical index of each common outcome, every fiber is an actual signed
prime-pattern realization, and only `o(N/log N)` TRUE prime targets are
discarded.  There is NO extra moment, correlation, covering, or prime-witness
assumption. -/
theorem scaleAdaptiveBandPrime_positive_on_density_one_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale m : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (large : 2 ≤ m)
    (within_scale : 2 * m ≤ scale + 1)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : (ℕ × ℕ) → ℝ,
      (∀ outcome : ℕ × ℕ,
        0 < singular outcome ∧
          Tendsto
            (adaptiveMixedSignedSingularPartialProduct
              support scale outcome)
            atTop (nhds (singular outcome))) ∧
      ∃ bad : ℕ → Finset ℕ,
        Tendsto
          (fun N : ℕ =>
            ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
          atTop (nhds (0 : ℝ)) ∧
        ∀ N target,
          target ∈ scaleAdaptiveTypedPrimeTargetsInIntegerCell
            1 (2 * m) (2 * m + 1) N →
          target ∉ bad N →
            adaptivePatternEulerFactor support scale / 8 ≤
              scaleAdaptiveBandPrimeOutcomeLoad
                support scale m
                  (fun index outcome =>
                    scaleAdaptiveBandActualModelTargetLoad
                      support scale m lower upper singular
                        index outcome N)
                  target := by
  obtain ⟨singular, certified⟩ :=
    scaleAdaptiveBand_common_outcome_singular_exists_of_GTZ
      green_tao support scale lower upper primes
        lower_nonnegative band_nonempty upper_bounded
  refine ⟨singular, certified, ?_⟩
  let targets : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveTypedPrimeTargetsInIntegerCell
      1 (2 * m) (2 * m + 1) N
  let load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ :=
    scaleAdaptiveBandActualModelTargetLoad
      support scale m lower upper singular
  apply scaleAdaptiveBandPrime_positive_on_density_one_of_energies
    support scale m targets load primes large
  intro index indexed outcome sample
  have bounds := scaleAdaptiveBandInteriorIndices_mem indexed
  have index_positive : 0 < index := by omega
  have active := scaleAdaptiveBandPrimeSample_index_active
    within_scale indexed sample
  have exact_type := scaleAdaptiveBandPrimeSample_actual_type sample
  have unclipped := scaleAdaptiveBandInteriorIndices_unclipped
    lower_nonnegative upper_bounded indexed
  obtain ⟨fiber_singular, _positive, converges, energy⟩ :=
    scaleAdaptiveConstantBand_typedTarget_centeredVariance_tendsto_zero_of_GTZ
      green_tao support scale outcome index (2 * m) (2 * m + 1)
        lower upper primes active index_positive lower_nonnegative
        band_nonempty upper_bounded (by omega)
        unclipped.1 unclipped.2
  have same := tendsto_nhds_unique (certified outcome).2 converges
  subst fiber_singular
  rw [exact_type] at energy
  simpa [targets, load, scaleAdaptiveBandActualModelTargetLoad,
    one_div] using energy

/-- DIRECT genuine SEMIPRIME-target positive-load theorem from ONLY the
explicit signed Green--Tao input.  Every supported true type `s` has the
same lower bound `F/8`; its true joint sample marginal `F/s` cancels its
true conditional target mean `s/i`.  The removed targets are actual
`s*q` for primes `q`, with prime-scale density tending to zero. -/
theorem scaleAdaptiveBandSemiprime_positive_on_density_one_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    {support : Finset ℕ} {type : ℕ}
    (scale m : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : type ∈ support)
    (large : 2 ≤ m)
    (within_scale : 2 * m ≤ scale + 1)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : (ℕ × ℕ) → ℝ,
      (∀ outcome : ℕ × ℕ,
        0 < singular outcome ∧
          Tendsto
            (adaptiveMixedSignedSingularPartialProduct
              support scale outcome)
            atTop (nhds (singular outcome))) ∧
      ∃ bad : ℕ → Finset ℕ,
        Tendsto
          (fun N : ℕ =>
            ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
          atTop (nhds (0 : ℝ)) ∧
        ∀ N target,
          target ∈ scaleAdaptiveTypedPrimeTargetsInIntegerCell
            type (2 * m) (2 * m + 1) N →
          target ∉ bad N →
            adaptivePatternEulerFactor support scale / 8 ≤
              scaleAdaptiveBandSemiprimeOutcomeLoad
                support type scale m
                  (fun index outcome =>
                    scaleAdaptiveBandActualModelTargetLoad
                      support scale m lower upper singular
                        index outcome N)
                  target := by
  obtain ⟨singular, certified⟩ :=
    scaleAdaptiveBand_common_outcome_singular_exists_of_GTZ
      green_tao support scale lower upper primes
        lower_nonnegative band_nonempty upper_bounded
  refine ⟨singular, certified, ?_⟩
  let targets : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveTypedPrimeTargetsInIntegerCell
      type (2 * m) (2 * m + 1) N
  let load : ℕ → (ℕ × ℕ) → ℕ → ℕ → ℝ :=
    scaleAdaptiveBandActualModelTargetLoad
      support scale m lower upper singular
  apply scaleAdaptiveBandSemiprime_positive_on_density_one_of_energies
    scale m targets load primes type_supported large
  intro index indexed outcome sample
  have bounds := scaleAdaptiveBandInteriorIndices_mem indexed
  have index_positive : 0 < index := by omega
  have active := scaleAdaptiveBandSemiprimeSample_index_active
    type_supported within_scale indexed sample
  have exact_type := scaleAdaptiveBandSemiprimeSample_actual_type
    type_supported sample
  have unclipped := scaleAdaptiveBandInteriorIndices_unclipped
    lower_nonnegative upper_bounded indexed
  obtain ⟨fiber_singular, _positive, converges, energy⟩ :=
    scaleAdaptiveConstantBand_typedTarget_centeredVariance_tendsto_zero_of_GTZ
      green_tao support scale outcome index (2 * m) (2 * m + 1)
        lower upper primes active index_positive lower_nonnegative
        band_nonempty upper_bounded (by omega)
        unclipped.1 unclipped.2
  have same := tendsto_nhds_unique (certified outcome).2 converges
  subst fiber_singular
  rw [exact_type] at energy
  simpa [targets, load, scaleAdaptiveBandActualModelTargetLoad,
    div_eq_mul_inv] using energy

end Erdos1139

