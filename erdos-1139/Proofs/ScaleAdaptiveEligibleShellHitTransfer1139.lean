module

public import ScaleAdaptiveGlobalJointHitTransfer1139

@[expose] public section


/-!
# Actual global colored hits from arbitrary eligible physical shell tails

The low type `s` is available only on the actual shells with `s ≤ 2^j`.
The high-family budget can likewise use only its short physical shell range.
Nevertheless all those tails must be compared with the ONE joint sampler on
the FULL common-prime pool, not with independently resampled subconfigurations.

Every true modular shell mass is nonnegative.  Thus exact physical-index
uniqueness and fair color splitting imply that the actual full-pool colored
hit load dominates one half of the restricted inverse-INTEGER-degree load
from ANY genuine exponent subfamily.  This retains true type eligibility,
shell-dependent supports and singulars, and one globally coherent residue.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1400000

/-- Every genuine modular mixed-pattern shell mass is nonnegative,
including zero-degree or zero-outcome edge cases. -/
theorem scaleAdaptiveGlobalJointFamilyShellModularLoad_nonnegative
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (familySupport : ℕ → Finset ℕ)
    (length exponent target : ℕ) :
    0 ≤ scaleAdaptiveGlobalJointFamilyShellModularLoad
      configuration familySupport length exponent target := by
  unfold scaleAdaptiveGlobalJointFamilyShellModularLoad
  apply Finset.sum_nonneg
  intro label _selected
  apply Finset.sum_nonneg
  intro outcome _selected
  apply Finset.sum_nonneg
  intro center _selected
  split_ifs with hit
  · exact div_nonneg (by norm_num)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact le_refl _

/-- The actual restricted PRIME load of ANY finite physical-shell
subfamily is bounded by precisely the same subfamily's true modular
mixed-pattern masses, with no change to its global prime pool. -/
theorem scaleAdaptiveRestrictedPrimeSubfamily_le_modularShellSum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ)
    (familySupport : ℕ → Finset ℕ)
    (length target : ℕ) :
    scaleAdaptiveRestrictedMultiShellPrimeActualLoad
      exponents familySupport
        configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length target ≤
      ∑ exponent ∈ exponents,
        scaleAdaptiveGlobalJointFamilyShellModularLoad
          configuration familySupport length exponent target := by
  unfold scaleAdaptiveRestrictedMultiShellPrimeActualLoad
  apply Finset.sum_le_sum
  intro exponent _selected
  unfold scaleAdaptiveBandPrimeOutcomeLoad
  have one_shell := scaleAdaptiveSignedRestrictedSampleShell_le_modularLoad
    (familySupport exponent)
    (configuration.lowSupport exponent)
    (configuration.highSupport exponent)
    (2 ^ exponent) configuration.lower configuration.upper
    (configuration.lowSingular exponent)
    (configuration.highSingular exponent)
    (length / 2 ^ exponent) target
    (scaleAdaptiveBandInteriorIndices
      (scaleAdaptiveMultiShellTargetCell length exponent target))
    (adaptiveMixedPrimePatternSamples
      (familySupport exponent) (2 ^ exponent))
    (adaptiveMixedPrimePatternSamples_subset_outcomes
      (familySupport exponent) (2 ^ exponent))
  rw [adaptiveMixedOutcomeSpace_card] at one_shell
  simpa only [scaleAdaptiveGlobalJointFamilyShellModularLoad,
    scaleAdaptiveGlobalTwoColorGoodShell,
    scaleAdaptiveDyadicPhysicalScale,
    adaptiveMixedOutcomeSpace_card] using one_shell

/-- The actual supported type-`s` restricted SEMIPRIME load of ANY true
eligible shell tail is bounded by that tail's true modular masses. -/
theorem scaleAdaptiveRestrictedSemiprimeSubfamily_le_modularShellSum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ)
    (familySupport : ℕ → Finset ℕ)
    (targetType length target : ℕ) :
    scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
      exponents familySupport
        configuration.lowSupport configuration.highSupport
        targetType configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length target ≤
      ∑ exponent ∈ exponents,
        scaleAdaptiveGlobalJointFamilyShellModularLoad
          configuration familySupport length exponent target := by
  unfold scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
  apply Finset.sum_le_sum
  intro exponent _selected
  unfold scaleAdaptiveBandSemiprimeOutcomeLoad
  have one_shell := scaleAdaptiveSignedRestrictedSampleShell_le_modularLoad
    (familySupport exponent)
    (configuration.lowSupport exponent)
    (configuration.highSupport exponent)
    (2 ^ exponent) configuration.lower configuration.upper
    (configuration.lowSingular exponent)
    (configuration.highSingular exponent)
    (length / 2 ^ exponent) target
    (scaleAdaptiveBandInteriorIndices
      (scaleAdaptiveMultiShellTargetCell length exponent target))
    (adaptiveMixedSemiprimePatternSamples
      (familySupport exponent) targetType (2 ^ exponent))
    (adaptiveMixedSemiprimePatternSamples_subset_outcomes
      (familySupport exponent) targetType (2 ^ exponent))
  rw [adaptiveMixedOutcomeSpace_card] at one_shell
  simpa only [scaleAdaptiveGlobalJointFamilyShellModularLoad,
    scaleAdaptiveGlobalTwoColorGoodShell,
    scaleAdaptiveDyadicPhysicalScale,
    adaptiveMixedOutcomeSpace_card] using one_shell

/-- Enlarging from ANY genuine exponent subfamily to the one full global
configuration can only increase its actual modular target mass. -/
theorem scaleAdaptiveGlobalJointSubfamilyModularSum_le_full
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ)
    (familySupport : ℕ → Finset ℕ)
    (length target : ℕ)
    (subset : exponents ⊆ configuration.exponents) :
    (∑ exponent ∈ exponents,
      scaleAdaptiveGlobalJointFamilyShellModularLoad
        configuration familySupport length exponent target) ≤
      ∑ exponent ∈ configuration.exponents,
        scaleAdaptiveGlobalJointFamilyShellModularLoad
          configuration familySupport length exponent target := by
  apply Finset.sum_le_sum_of_subset_of_nonneg subset
  intro exponent _selected _not_selected
  exact scaleAdaptiveGlobalJointFamilyShellModularLoad_nonnegative
    configuration familySupport length exponent target

/-- Actual LOW colored global hits dominate one half of the genuine
restricted PRIME load from ANY retained physical shell subfamily. -/
theorem scaleAdaptiveGlobalJointLowHitLoad_ge_restrictedPrimeSubfamily
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ)
    (length : ℕ) (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (subset : exponents ⊆ configuration.exponents)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    scaleAdaptiveRestrictedMultiShellPrimeActualLoad
      exponents configuration.lowSupport
        configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length target / 2 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        false target := by
  rw [scaleAdaptiveGlobalJointLowHitLoad_eq_half_modularShellSum
    configuration length lowTargets highTargets target
      low_primes high_primes]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  exact (scaleAdaptiveRestrictedPrimeSubfamily_le_modularShellSum
    configuration exponents configuration.lowSupport length target).trans
      (scaleAdaptiveGlobalJointSubfamilyModularSum_le_full
        configuration exponents configuration.lowSupport
          length target subset)

/-- Actual HIGH colored hits of the SAME global sampler dominate one
half of the genuine restricted PRIME load from ANY physical subfamily. -/
theorem scaleAdaptiveGlobalJointHighHitLoad_ge_restrictedPrimeSubfamily
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ)
    (length : ℕ) (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (subset : exponents ⊆ configuration.exponents)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    scaleAdaptiveRestrictedMultiShellPrimeActualLoad
      exponents configuration.highSupport
        configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length target / 2 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        true target := by
  rw [scaleAdaptiveGlobalJointHighHitLoad_eq_half_modularShellSum
    configuration length lowTargets highTargets target
      low_primes high_primes]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  exact (scaleAdaptiveRestrictedPrimeSubfamily_le_modularShellSum
    configuration exponents configuration.highSupport length target).trans
      (scaleAdaptiveGlobalJointSubfamilyModularSum_le_full
        configuration exponents configuration.highSupport
          length target subset)

/-- The ACTUAL LOW global colored hit load dominates one half of the
genuine type-`s` SEMIPRIME load from its OWN eligible physical shells.
The globally selected prime pool, denominator, colors, and residues do
not change with the target type. -/
theorem scaleAdaptiveGlobalJointLowHitLoad_ge_restrictedSemiprimeSubfamily
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ) (targetType length : ℕ)
    (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (subset : exponents ⊆ configuration.exponents)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
      exponents configuration.lowSupport
        configuration.lowSupport configuration.highSupport
        targetType configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length target / 2 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        false target := by
  rw [scaleAdaptiveGlobalJointLowHitLoad_eq_half_modularShellSum
    configuration length lowTargets highTargets target
      low_primes high_primes]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  exact (scaleAdaptiveRestrictedSemiprimeSubfamily_le_modularShellSum
    configuration exponents configuration.lowSupport
      targetType length target).trans
      (scaleAdaptiveGlobalJointSubfamilyModularSum_le_full
        configuration exponents configuration.lowSupport
          length target subset)

/-- The SAME actual HIGH colored global hit load dominates half the
genuine supported type-`s` SEMIPRIME load from ANY eligible subfamily,
including the short physical-shell family used in its true Euler budget. -/
theorem scaleAdaptiveGlobalJointHighHitLoad_ge_restrictedSemiprimeSubfamily
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ) (targetType length : ℕ)
    (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (subset : exponents ⊆ configuration.exponents)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
      exponents configuration.highSupport
        configuration.lowSupport configuration.highSupport
        targetType configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length target / 2 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        true target := by
  rw [scaleAdaptiveGlobalJointHighHitLoad_eq_half_modularShellSum
    configuration length lowTargets highTargets target
      low_primes high_primes]
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
  exact (scaleAdaptiveRestrictedSemiprimeSubfamily_le_modularShellSum
    configuration exponents configuration.highSupport
      targetType length target).trans
      (scaleAdaptiveGlobalJointSubfamilyModularSum_le_full
        configuration exponents configuration.highSupport
          length target subset)


end Erdos1139
