module

public import ScaleAdaptiveActualPointwiseHitTransfer1139
public import ScaleAdaptiveFinalShellSupportIdentities1139

@[expose] public section


/-!
# Actual type-specific global colored hit profiles

Prime targets use the full low family or the short high family.  A genuine
low semiprime type uses ONLY its own physically eligible shell tail, and a
genuine high type uses the short high family.  All four families retain the
SAME global prime pool, colors, and residues.

Their actual type-specific pattern/cross-prime exceptional sets have zero
original prime-scale density under the single fixed-system Green--Tao input.
The separately charged true physical prefix is not claimed to have zero
density.  No final covering or probabilistic estimate is assumed.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 2200000

/-- The exact LOW bad set for one true target type: genuine prime-pattern
exceptions for s=1, and complete restricted semiprime exceptions on the
target's OWN eligible physical shell tail for every prime s>1. -/
noncomputable def scaleAdaptiveFinalLowTypedBadTargets
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (parameter targetType length : ℕ) : Finset ℕ :=
  if targetType = 1 then
    scaleAdaptiveRestrictedMultiShellPrimeExceptions
      (scaleAdaptiveFinalShellFullExponents parameter)
      configuration.lowSupport
      configuration.lowSupport configuration.highSupport
      configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular length
  else
    scaleAdaptiveRestrictedMultiShellSemiprimeExceptions
      (scaleAdaptiveFinalShellEligibleExponents parameter targetType)
      configuration.lowSupport
      configuration.lowSupport configuration.highSupport
      targetType configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular length

/-- The exact HIGH bad set for one true target type, always using the
genuinely shorter actual physical-shell amplification family. -/
noncomputable def scaleAdaptiveFinalHighTypedBadTargets
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (parameter targetType length : ℕ) : Finset ℕ :=
  if targetType = 1 then
    scaleAdaptiveRestrictedMultiShellPrimeExceptions
      (scaleAdaptiveFinalShellShortExponents parameter)
      configuration.highSupport
      configuration.lowSupport configuration.highSupport
      configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular length
  else
    scaleAdaptiveRestrictedMultiShellSemiprimeExceptions
      (scaleAdaptiveFinalShellShortExponents parameter)
      configuration.highSupport
      configuration.lowSupport configuration.highSupport
      targetType configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular length

/-- Every exact LOW type-specific whole-outcome and cross-prime exception
has zero density at the ORIGINAL target scale, solely from signed GTZ
and the SAME full global configuration's actual rejected-prime limits. -/
theorem scaleAdaptiveFinalLowTypedBadTargets_normalized_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (parameter targetType : ℕ)
    (configuration_exponents :
      configuration.exponents =
        scaleAdaptiveFinalShellFullExponents parameter)
    (configuration_low :
      configuration.lowSupport = scaleAdaptiveFinalShellLowSupport parameter)
    (_configuration_high :
      configuration.highSupport = scaleAdaptiveFinalShellHighSupport parameter)
    (type_valid : targetType = 1 ∨
      targetType.Prime ∧
        targetType ≤ 2 ^ scaleAdaptiveColoredSplitExponent parameter)
    (lower_nonnegative : 0 ≤ configuration.lower)
    (band_nonempty : configuration.lower < configuration.upper)
    (upper_bounded : configuration.upper ≤ 1)
    (rejected : ∀ exponent ∈ configuration.exponents,
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            (configuration.lowSupport exponent)
            (configuration.highSupport exponent)
            (2 ^ exponent) configuration.lower configuration.upper
              (configuration.lowSingular exponent)
              (configuration.highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveFinalLowTypedBadTargets
          configuration parameter targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime := by
    intro exponent _selected prime included
    rw [configuration_low] at included
    exact scaleAdaptiveFinalShellLowSupport_prime parameter exponent included
  by_cases prime_target : targetType = 1
  · subst targetType
    simp only [scaleAdaptiveFinalLowTypedBadTargets]
    apply scaleAdaptiveRestrictedMultiShellPrimeExceptions_tendsto_zero_of_GTZ
      green_tao (scaleAdaptiveFinalShellFullExponents parameter)
      configuration.lowSupport configuration.lowSupport
      configuration.highSupport configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular
    · intro exponent selected
      exact low_primes exponent (configuration_exponents.symm ▸ selected)
    · exact lower_nonnegative
    · exact band_nonempty
    · exact upper_bounded
    · intro exponent selected
      exact rejected exponent (configuration_exponents.symm ▸ selected)
  · obtain ⟨type_prime, below_split⟩ := type_valid.resolve_left prime_target
    simp only [scaleAdaptiveFinalLowTypedBadTargets, if_neg prime_target]
    apply scaleAdaptiveRestrictedMultiShellSemiprimeExceptions_tendsto_zero_of_GTZ
      green_tao (scaleAdaptiveFinalShellEligibleExponents parameter targetType)
      configuration.lowSupport configuration.lowSupport
      configuration.highSupport targetType
      configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular
    · intro exponent selected
      apply low_primes exponent
      rw [configuration_exponents]
      exact scaleAdaptiveFinalShellEligibleExponents_subset_full
        parameter targetType selected
    · intro exponent selected
      rw [configuration_low]
      exact scaleAdaptiveFinalShellEligibleType_mem_lowSupport
        type_prime below_split selected
    · exact lower_nonnegative
    · exact band_nonempty
    · exact upper_bounded
    · intro exponent selected
      apply rejected exponent
      rw [configuration_exponents]
      exact scaleAdaptiveFinalShellEligibleExponents_subset_full
        parameter targetType selected

/-- Every true HIGH type-specific prime/semiprime and cross-prime
exception has zero ORIGINAL density; the exact short exponent family is
a genuine subfamily of the ONE full global configuration. -/
theorem scaleAdaptiveFinalHighTypedBadTargets_normalized_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (parameter targetType : ℕ)
    (parameter_large : 2 ≤ parameter)
    (configuration_exponents :
      configuration.exponents =
        scaleAdaptiveFinalShellFullExponents parameter)
    (_configuration_low :
      configuration.lowSupport = scaleAdaptiveFinalShellLowSupport parameter)
    (configuration_high :
      configuration.highSupport = scaleAdaptiveFinalShellHighSupport parameter)
    (type_valid : targetType = 1 ∨
      targetType.Prime ∧
        2 ^ scaleAdaptiveColoredSplitExponent parameter < targetType ∧
        targetType ≤ 2 ^ scaleAdaptiveColoredFullExponent parameter)
    (lower_nonnegative : 0 ≤ configuration.lower)
    (band_nonempty : configuration.lower < configuration.upper)
    (upper_bounded : configuration.upper ≤ 1)
    (rejected : ∀ exponent ∈ configuration.exponents,
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            (configuration.lowSupport exponent)
            (configuration.highSupport exponent)
            (2 ^ exponent) configuration.lower configuration.upper
              (configuration.lowSingular exponent)
              (configuration.highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveFinalHighTypedBadTargets
          configuration parameter targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime := by
    intro exponent _selected prime included
    rw [configuration_high] at included
    exact scaleAdaptiveFinalShellHighSupport_prime parameter exponent included
  have short_subset :
      scaleAdaptiveFinalShellShortExponents parameter ⊆
        configuration.exponents := by
    rw [configuration_exponents]
    exact scaleAdaptiveFinalShellShortExponents_subset_full parameter_large
  by_cases prime_target : targetType = 1
  · subst targetType
    simp only [scaleAdaptiveFinalHighTypedBadTargets]
    apply scaleAdaptiveRestrictedMultiShellPrimeExceptions_tendsto_zero_of_GTZ
      green_tao (scaleAdaptiveFinalShellShortExponents parameter)
      configuration.highSupport configuration.lowSupport
      configuration.highSupport configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular
    · intro exponent selected
      exact high_primes exponent (short_subset selected)
    · exact lower_nonnegative
    · exact band_nonempty
    · exact upper_bounded
    · intro exponent selected
      exact rejected exponent (short_subset selected)
  · obtain ⟨type_prime, above_split, below_full⟩ :=
      type_valid.resolve_left prime_target
    simp only [scaleAdaptiveFinalHighTypedBadTargets, if_neg prime_target]
    apply scaleAdaptiveRestrictedMultiShellSemiprimeExceptions_tendsto_zero_of_GTZ
      green_tao (scaleAdaptiveFinalShellShortExponents parameter)
      configuration.highSupport configuration.lowSupport
      configuration.highSupport targetType
      configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular
    · intro exponent selected
      exact high_primes exponent (short_subset selected)
    · intro exponent _selected
      rw [configuration_high]
      exact scaleAdaptiveFinalShellHighType_mem_highSupport
        exponent type_prime above_split below_full
    · exact lower_nonnegative
    · exact band_nonempty
    · exact upper_bounded
    · intro exponent selected
      exact rejected exponent (short_subset selected)

/-- Exact actual LOW colored global hit at EVERY true covered target
type.  Type one uses the full low shell; each prime type uses only its OWN
eligible tail.  The entire prime pool, option denominator, color, and
residue stay fixed. -/
theorem scaleAdaptiveFinalLowTypedPointwiseHit_ge_profile
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (parameter targetType length target : ℕ)
    (lowTargets highTargets : Finset ℕ)
    (configuration_exponents :
      configuration.exponents =
        scaleAdaptiveFinalShellFullExponents parameter)
    (configuration_low :
      configuration.lowSupport = scaleAdaptiveFinalShellLowSupport parameter)
    (configuration_high :
      configuration.highSupport = scaleAdaptiveFinalShellHighSupport parameter)
    (type_valid : targetType = 1 ∨
      targetType.Prime ∧
        targetType ≤ 2 ^ scaleAdaptiveColoredSplitExponent parameter)
    (scales_large : ∀ exponent ∈ configuration.exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (typed : target ∈ scaleAdaptiveGlobalTypedTargets targetType length)
    (not_prefix : target ∉
      scaleAdaptiveGlobalTypedTargets targetType
        (length / 2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1)))
    (not_exception : target ∉
      scaleAdaptiveFinalLowTypedBadTargets
        configuration parameter targetType length) :
    (if targetType = 1 then
      scaleAdaptiveDyadicEulerShellMass
        (scaleAdaptiveColoredLowerExponent parameter)
        (scaleAdaptiveColoredFullExponent parameter)
     else
      scaleAdaptiveLowEligibleDyadicEulerShell
        targetType (2 ^ scaleAdaptiveColoredSplitExponent parameter)
        (scaleAdaptiveColoredLowerExponent parameter)
        (scaleAdaptiveColoredFullExponent parameter)) / 32 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        false target := by
  have low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime := by
    intro exponent _selected prime included
    rw [configuration_low] at included
    exact scaleAdaptiveFinalShellLowSupport_prime parameter exponent included
  have high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime := by
    intro exponent _selected prime included
    rw [configuration_high] at included
    exact scaleAdaptiveFinalShellHighSupport_prime parameter exponent included
  have divisor_positive :
      0 < 2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1) := by
    positivity
  by_cases prime_target : targetType = 1
  · subst targetType
    simp only [ite_true]
    rw [← scaleAdaptiveFinalShellLowFullEulerSum_eq parameter]
    have result := scaleAdaptiveActualLowPrimeHit_ge_euler32
      configuration (scaleAdaptiveFinalShellFullExponents parameter)
      (2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1))
      length target lowTargets highTargets
      (by rw [configuration_exponents])
      low_primes high_primes divisor_positive
      (fun exponent selected =>
        scaleAdaptiveFinalShellPhysicalPrefix_factor_le selected)
      (fun exponent selected =>
        scales_large exponent (configuration_exponents.symm ▸ selected))
      typed not_prefix
      (by simpa [scaleAdaptiveFinalLowTypedBadTargets]
        using not_exception)
    simpa only [configuration_low, ite_true] using result
  · obtain ⟨type_prime, below_split⟩ := type_valid.resolve_left prime_target
    simp only [if_neg prime_target]
    rw [← scaleAdaptiveFinalShellLowEligibleEulerSum_eq
      type_prime below_split]
    have eligible_subset :
        scaleAdaptiveFinalShellEligibleExponents parameter targetType ⊆
          configuration.exponents := by
      rw [configuration_exponents]
      exact scaleAdaptiveFinalShellEligibleExponents_subset_full
        parameter targetType
    have result := scaleAdaptiveActualLowSemiprimeHit_ge_euler32
      configuration
      (scaleAdaptiveFinalShellEligibleExponents parameter targetType)
      targetType (2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1))
      length target lowTargets highTargets eligible_subset
      low_primes high_primes
      (by
        intro exponent selected
        rw [configuration_low]
        exact scaleAdaptiveFinalShellEligibleType_mem_lowSupport
          type_prime below_split selected)
      type_prime.pos divisor_positive
      (by
        intro exponent selected
        exact scaleAdaptiveFinalShellPhysicalPrefix_factor_le
          (scaleAdaptiveFinalShellEligibleExponents_subset_full
            parameter targetType selected))
      (fun exponent selected =>
        scales_large exponent (eligible_subset selected))
      typed not_prefix
      (by simpa [scaleAdaptiveFinalLowTypedBadTargets, prime_target]
        using not_exception)
    simpa only [configuration_low] using result

/-- Exact actual HIGH colored global hit at EVERY true covered target
type, including both prime targets and all strictly-above-split semiprime
types.  EVERY target uses the genuine SHORT physical family inside the
SAME unchanged global sampler. -/
theorem scaleAdaptiveFinalHighTypedPointwiseHit_ge_profile
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (parameter targetType length target : ℕ)
    (lowTargets highTargets : Finset ℕ)
    (parameter_large : 2 ≤ parameter)
    (configuration_exponents :
      configuration.exponents =
        scaleAdaptiveFinalShellFullExponents parameter)
    (configuration_low :
      configuration.lowSupport = scaleAdaptiveFinalShellLowSupport parameter)
    (configuration_high :
      configuration.highSupport = scaleAdaptiveFinalShellHighSupport parameter)
    (type_valid : targetType = 1 ∨
      targetType.Prime ∧
        2 ^ scaleAdaptiveColoredSplitExponent parameter < targetType ∧
        targetType ≤ 2 ^ scaleAdaptiveColoredFullExponent parameter)
    (scales_large : ∀ exponent ∈ configuration.exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (typed : target ∈ scaleAdaptiveGlobalTypedTargets targetType length)
    (not_prefix : target ∉
      scaleAdaptiveGlobalTypedTargets targetType
        (length / 2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1)))
    (not_exception : target ∉
      scaleAdaptiveFinalHighTypedBadTargets
        configuration parameter targetType length) :
    scaleAdaptiveHighDyadicEulerShellMass
      (scaleAdaptiveColoredFullExponent parameter)
      (scaleAdaptiveColoredSplitExponent parameter)
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredSplitExponent parameter) / 32 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        true target := by
  have low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime := by
    intro exponent _selected prime included
    rw [configuration_low] at included
    exact scaleAdaptiveFinalShellLowSupport_prime parameter exponent included
  have high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime := by
    intro exponent _selected prime included
    rw [configuration_high] at included
    exact scaleAdaptiveFinalShellHighSupport_prime parameter exponent included
  have divisor_positive :
      0 < 2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1) := by
    positivity
  have short_subset :
      scaleAdaptiveFinalShellShortExponents parameter ⊆
        configuration.exponents := by
    rw [configuration_exponents]
    exact scaleAdaptiveFinalShellShortExponents_subset_full parameter_large
  rw [← scaleAdaptiveFinalShellHighShortEulerSum_eq parameter]
  by_cases prime_target : targetType = 1
  · subst targetType
    have result := scaleAdaptiveActualHighPrimeHit_ge_euler32
      configuration (scaleAdaptiveFinalShellShortExponents parameter)
      (2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1))
      length target lowTargets highTargets short_subset
      low_primes high_primes divisor_positive
      (by
        intro exponent selected
        exact scaleAdaptiveFinalShellPhysicalPrefix_factor_le
          (scaleAdaptiveFinalShellShortExponents_subset_full
            parameter_large selected))
      (fun exponent selected => scales_large exponent
        (short_subset selected))
      typed not_prefix
      (by simpa [scaleAdaptiveFinalHighTypedBadTargets]
        using not_exception)
    simpa only [configuration_high] using result
  · obtain ⟨type_prime, above_split, below_full⟩ :=
      type_valid.resolve_left prime_target
    have result := scaleAdaptiveActualHighSemiprimeHit_ge_euler32
      configuration (scaleAdaptiveFinalShellShortExponents parameter)
      targetType (2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1))
      length target lowTargets highTargets short_subset
      low_primes high_primes
      (by
        intro exponent _selected
        rw [configuration_high]
        exact scaleAdaptiveFinalShellHighType_mem_highSupport
          exponent type_prime above_split below_full)
      type_prime.pos divisor_positive
      (by
        intro exponent selected
        exact scaleAdaptiveFinalShellPhysicalPrefix_factor_le
          (scaleAdaptiveFinalShellShortExponents_subset_full
            parameter_large selected))
      (fun exponent selected => scales_large exponent
        (short_subset selected))
      typed not_prefix
      (by simpa [scaleAdaptiveFinalHighTypedBadTargets, prime_target]
        using not_exception)
    simpa only [configuration_high] using result


end Erdos1139
