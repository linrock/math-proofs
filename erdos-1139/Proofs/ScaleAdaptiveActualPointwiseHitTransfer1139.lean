module

public import ScaleAdaptiveEligibleShellHitTransfer1139
public import ScaleAdaptiveGlobalExponentialBudgets1139

@[expose] public section


/-!
# Genuine pointwise global colored hit bounds

The same full-pool joint sampler supplies all four required target families.
For an arbitrary eligible physical-shell subfamily, its actual colored hit
load is at least one half of the true common-pool restricted load, which is
at least one sixteenth of the corresponding genuine Euler mass.  Hence the
pointwise lower bound is exactly `Σ F_j / 32`.

The original typed target, its exact floored physical-prefix deletion, and
all restricted mixed-pattern/cross-prime exceptions are explicit.  The
configuration is never changed or resampled for a target type.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1600000

/-- Outside its OWN exact prime-counting prefix, a true typed target is
above the physical lower boundary of every eligible shell.  This accepts
any positive integer divisor satisfying the true integer factor bound. -/
theorem scaleAdaptiveActualTypedTargetInterior_of_not_typed_prefix
    {targetType length target divisor exponent : ℕ}
    (type_positive : 0 < targetType)
    (typed : target ∈ scaleAdaptiveGlobalTypedTargets targetType length)
    (not_prefix : target ∉
      scaleAdaptiveGlobalTypedTargets targetType (length / divisor))
    (divisor_positive : 0 < divisor)
    (factor_bound : 4 * divisor ≤ 2 ^ exponent) :
    4 * (length / 2 ^ exponent) ≤ target := by
  obtain ⟨prime, prime_is_prime, _bounded, equal⟩ :=
    (mem_scaleAdaptiveGlobalTypedTargets type_positive).mp typed
  subst target
  have above : length / divisor < targetType * prime := by
    by_contra failed
    apply not_prefix
    exact (mem_scaleAdaptiveGlobalTypedTargets type_positive).mpr
      ⟨prime, prime_is_prime, le_of_not_gt failed, rfl⟩
  exact scaleAdaptiveGlobalPhysicalInterior_of_prefix
    divisor_positive factor_bound above

/-- The ACTUAL full-pool LOW colored hit at a prime target dominates one
thirty-second of the genuine low Euler mass on ANY physical subfamily. -/
theorem scaleAdaptiveActualLowPrimeHit_ge_euler32
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ) (divisor length target : ℕ)
    (lowTargets highTargets : Finset ℕ)
    (subset : exponents ⊆ configuration.exponents)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
    (divisor_positive : 0 < divisor)
    (factor_bound : ∀ exponent ∈ exponents,
      4 * divisor ≤ 2 ^ exponent)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (typed : target ∈ scaleAdaptiveGlobalTypedTargets 1 length)
    (not_prefix : target ∉
      scaleAdaptiveGlobalTypedTargets 1 (length / divisor))
    (not_exception : target ∉
      scaleAdaptiveRestrictedMultiShellPrimeExceptions
        exponents configuration.lowSupport
          configuration.lowSupport configuration.highSupport
          configuration.lower configuration.upper
          configuration.lowSingular configuration.highSingular length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (configuration.lowSupport exponent) (2 ^ exponent)) / 32 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        false target := by
  obtain ⟨prime, prime_is_prime, target_high, equal⟩ :=
    (mem_scaleAdaptiveGlobalTypedTargets (by omega : 0 < 1)).mp typed
  have target_prime : target.Prime := by
    simpa [equal] using prime_is_prime
  have bounded : target ≤ length := by simpa [equal] using target_high
  have restricted :=
    scaleAdaptiveRestrictedMultiShellPrimeActualLoad_ge_euler_sum
      exponents configuration.lowSupport
      configuration.lowSupport configuration.highSupport
      configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular length target
      (fun exponent selected => low_primes exponent (subset selected))
      target_prime bounded scales_large
      (fun exponent selected =>
        scaleAdaptiveActualTypedTargetInterior_of_not_typed_prefix
          (by omega : 0 < 1) typed not_prefix divisor_positive
            (factor_bound exponent selected))
      not_exception
  have colored :=
    scaleAdaptiveGlobalJointLowHitLoad_ge_restrictedPrimeSubfamily
      configuration exponents length lowTargets highTargets target
        subset low_primes high_primes
  calc
    _ = ((∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (configuration.lowSupport exponent) (2 ^ exponent)) / 16) / 2 := by
          ring
    _ ≤ scaleAdaptiveRestrictedMultiShellPrimeActualLoad
      exponents configuration.lowSupport
        configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length target / 2 :=
          (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
            restricted
    _ ≤ _ := colored

/-- The SAME actual full-pool HIGH sampler at a prime target dominates
one thirty-second of the TRUE high mass on any short shell subfamily. -/
theorem scaleAdaptiveActualHighPrimeHit_ge_euler32
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ) (divisor length target : ℕ)
    (lowTargets highTargets : Finset ℕ)
    (subset : exponents ⊆ configuration.exponents)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
    (divisor_positive : 0 < divisor)
    (factor_bound : ∀ exponent ∈ exponents,
      4 * divisor ≤ 2 ^ exponent)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (typed : target ∈ scaleAdaptiveGlobalTypedTargets 1 length)
    (not_prefix : target ∉
      scaleAdaptiveGlobalTypedTargets 1 (length / divisor))
    (not_exception : target ∉
      scaleAdaptiveRestrictedMultiShellPrimeExceptions
        exponents configuration.highSupport
          configuration.lowSupport configuration.highSupport
          configuration.lower configuration.upper
          configuration.lowSingular configuration.highSingular length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (configuration.highSupport exponent) (2 ^ exponent)) / 32 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        true target := by
  obtain ⟨prime, prime_is_prime, target_high, equal⟩ :=
    (mem_scaleAdaptiveGlobalTypedTargets (by omega : 0 < 1)).mp typed
  have target_prime : target.Prime := by
    simpa [equal] using prime_is_prime
  have bounded : target ≤ length := by simpa [equal] using target_high
  have restricted :=
    scaleAdaptiveRestrictedMultiShellPrimeActualLoad_ge_euler_sum
      exponents configuration.highSupport
      configuration.lowSupport configuration.highSupport
      configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular length target
      (fun exponent selected => high_primes exponent (subset selected))
      target_prime bounded scales_large
      (fun exponent selected =>
        scaleAdaptiveActualTypedTargetInterior_of_not_typed_prefix
          (by omega : 0 < 1) typed not_prefix divisor_positive
            (factor_bound exponent selected))
      not_exception
  have colored :=
    scaleAdaptiveGlobalJointHighHitLoad_ge_restrictedPrimeSubfamily
      configuration exponents length lowTargets highTargets target
        subset low_primes high_primes
  calc
    _ = ((∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (configuration.highSupport exponent) (2 ^ exponent)) / 16) / 2 := by
          ring
    _ ≤ scaleAdaptiveRestrictedMultiShellPrimeActualLoad
      exponents configuration.highSupport
        configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length target / 2 :=
          (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
            restricted
    _ ≤ _ := colored

/-- At a genuine type-`s` semiprime, the SAME LOW global sampler has
actual hit mass at least `Σ F_j/32` on the target's OWN eligible shells. -/
theorem scaleAdaptiveActualLowSemiprimeHit_ge_euler32
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ) (targetType divisor length target : ℕ)
    (lowTargets highTargets : Finset ℕ)
    (subset : exponents ⊆ configuration.exponents)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ configuration.lowSupport exponent)
    (type_positive : 0 < targetType)
    (divisor_positive : 0 < divisor)
    (factor_bound : ∀ exponent ∈ exponents,
      4 * divisor ≤ 2 ^ exponent)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (typed : target ∈ scaleAdaptiveGlobalTypedTargets targetType length)
    (not_prefix : target ∉
      scaleAdaptiveGlobalTypedTargets targetType (length / divisor))
    (not_exception : target ∉
      scaleAdaptiveRestrictedMultiShellSemiprimeExceptions
        exponents configuration.lowSupport
          configuration.lowSupport configuration.highSupport
          targetType configuration.lower configuration.upper
          configuration.lowSingular configuration.highSingular length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (configuration.lowSupport exponent) (2 ^ exponent)) / 32 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        false target := by
  obtain ⟨prime, prime_is_prime, target_high, equal⟩ :=
    (mem_scaleAdaptiveGlobalTypedTargets type_positive).mp typed
  subst target
  have restricted :=
    scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad_ge_euler_sum
      exponents configuration.lowSupport
      configuration.lowSupport configuration.highSupport
      targetType configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular length prime
      (fun exponent selected => low_primes exponent (subset selected))
      type_supported prime_is_prime type_positive target_high scales_large
      (fun exponent selected =>
        scaleAdaptiveActualTypedTargetInterior_of_not_typed_prefix
          type_positive typed not_prefix divisor_positive
            (factor_bound exponent selected))
      not_exception
  have colored :=
    scaleAdaptiveGlobalJointLowHitLoad_ge_restrictedSemiprimeSubfamily
      configuration exponents targetType length lowTargets highTargets
        (targetType * prime) subset low_primes high_primes
  calc
    _ = ((∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (configuration.lowSupport exponent) (2 ^ exponent)) / 16) / 2 := by
          ring
    _ ≤ scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
      exponents configuration.lowSupport
        configuration.lowSupport configuration.highSupport
        targetType configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length (targetType * prime) / 2 :=
          (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
            restricted
    _ ≤ _ := colored

/-- All genuinely supported HIGH types use the SAME global sampler and
any retained short physical-shell family, obtaining the exact `1/32`. -/
theorem scaleAdaptiveActualHighSemiprimeHit_ge_euler32
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponents : Finset ℕ) (targetType divisor length target : ℕ)
    (lowTargets highTargets : Finset ℕ)
    (subset : exponents ⊆ configuration.exponents)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ configuration.highSupport exponent)
    (type_positive : 0 < targetType)
    (divisor_positive : 0 < divisor)
    (factor_bound : ∀ exponent ∈ exponents,
      4 * divisor ≤ 2 ^ exponent)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (typed : target ∈ scaleAdaptiveGlobalTypedTargets targetType length)
    (not_prefix : target ∉
      scaleAdaptiveGlobalTypedTargets targetType (length / divisor))
    (not_exception : target ∉
      scaleAdaptiveRestrictedMultiShellSemiprimeExceptions
        exponents configuration.highSupport
          configuration.lowSupport configuration.highSupport
          targetType configuration.lower configuration.upper
          configuration.lowSingular configuration.highSingular length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (configuration.highSupport exponent) (2 ^ exponent)) / 32 ≤
      weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        true target := by
  obtain ⟨prime, prime_is_prime, target_high, equal⟩ :=
    (mem_scaleAdaptiveGlobalTypedTargets type_positive).mp typed
  subst target
  have restricted :=
    scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad_ge_euler_sum
      exponents configuration.highSupport
      configuration.lowSupport configuration.highSupport
      targetType configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular length prime
      (fun exponent selected => high_primes exponent (subset selected))
      type_supported prime_is_prime type_positive target_high scales_large
      (fun exponent selected =>
        scaleAdaptiveActualTypedTargetInterior_of_not_typed_prefix
          type_positive typed not_prefix divisor_positive
            (factor_bound exponent selected))
      not_exception
  have colored :=
    scaleAdaptiveGlobalJointHighHitLoad_ge_restrictedSemiprimeSubfamily
      configuration exponents targetType length lowTargets highTargets
        (targetType * prime) subset low_primes high_primes
  calc
    _ = ((∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (configuration.highSupport exponent) (2 ^ exponent)) / 16) / 2 := by
          ring
    _ ≤ scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
      exponents configuration.highSupport
        configuration.lowSupport configuration.highSupport
        targetType configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
        length (targetType * prime) / 2 :=
          (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
            restricted
    _ ≤ _ := colored


end Erdos1139
