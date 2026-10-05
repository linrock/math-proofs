module

public import ScaleAdaptiveGlobalExponentialBudgets1139
public import ScaleAdaptiveGlobalJointOptionAssembly1139
public import ScaleAdaptiveGlobalRestrictedMarginalIdentity1139
public import ScaleAdaptiveRestrictedMultiscaleLoad1139
public import ScaleAdaptiveGlobalJointHitTransfer1139
public import ScaleAdaptiveEligibleShellHitTransfer1139
public import ScaleAdaptiveActualPointwiseHitTransfer1139
public import ScaleAdaptiveActualTypedPointwiseProfiles1139
public import ScaleAdaptiveFinalShellSupportIdentities1139
public import ScaleAdaptiveGlobalTypedTargetClassification1139

@[expose] public section


/-!
# Original-scale transfer for actual joint colored missing-hit budgets

This module converts genuine finite exponential bounds into their exact
`Y/log Y` coefficients.  Prime targets retain coefficient one; semiprime
targets of genuine type `s` retain coefficient `1/s`; all fixed-family
exceptional sets are charged explicitly at the ORIGINAL target scale.

Every support, exponent family, and type family is fixed before `Y → ∞`.
The adaptive parameter limit comes afterward.  No rate uniform in the
Green--Tao pattern complexity and no already-constructed covering is used.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1400000

/-- The actual original-scale normalization is nonnegative once the true
integer endpoint is at least two. -/
theorem scaleAdaptiveActualOriginalWeight_nonnegative
    {length : ℕ} (large : 2 ≤ length) :
    0 ≤ Real.log (length : ℝ) / (length : ℝ) := by
  exact div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ length by omega)))
    (Nat.cast_nonneg _)

/-- A genuine zero-density exception plus an actual target-counting
limit gives the precise original-scale limsup upper coefficient of its
missing-hit exponential sum.  This is a finite analytic transfer lemma,
not a covering or a probabilistic premise. -/
theorem scaleAdaptiveActualExponentialBudget_eventually_le
    (targets exceptions : ℕ → Finset ℕ)
    (load : ℕ → ℕ → ℝ) (cutoff density slack : ℝ)
    (target_density : Tendsto
      (fun length : ℕ =>
        ((targets length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds density))
    (exception_density : Tendsto
      (fun length : ℕ =>
        ((exceptions length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)))
    (nonnegative : ∀ᶠ length : ℕ in atTop,
      ∀ target ∈ targets length, 0 ≤ load length target)
    (good : ∀ᶠ length : ℕ in atTop,
      ∀ target ∈ targets length, target ∉ exceptions length →
        cutoff ≤ load length target)
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ target ∈ targets length,
        Real.exp (-load length target)) *
          Real.log (length : ℝ) / (length : ℝ) ≤
        density * Real.exp (-cutoff) + slack := by
  have majorant :
      Tendsto
        (fun length : ℕ =>
          ((exceptions length).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ) +
          (((targets length).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ)) *
            Real.exp (-cutoff))
        atTop (nhds (density * Real.exp (-cutoff))) := by
    simpa using exception_density.add (target_density.mul_const _)
  have strict := majorant.eventually
    (Iio_mem_nhds (by linarith :
      density * Real.exp (-cutoff) <
        density * Real.exp (-cutoff) + slack))
  filter_upwards [nonnegative, good, strict, eventually_ge_atTop 2]
    with length nonnegative good strict large
  have finite := scaleAdaptiveGlobalExponentialBudget_le_exception_card
    (targets length) (exceptions length) (load length) cutoff
      nonnegative good
  have weighted := mul_le_mul_of_nonneg_right finite
    (scaleAdaptiveActualOriginalWeight_nonnegative large)
  have rearranged :
      (∑ target ∈ targets length,
        Real.exp (-load length target)) *
          Real.log (length : ℝ) / (length : ℝ) ≤
        ((exceptions length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ) +
        (((targets length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ)) *
          Real.exp (-cutoff) := by
    calc
      _ = (∑ target ∈ targets length,
        Real.exp (-load length target)) *
          (Real.log (length : ℝ) / (length : ℝ)) := by ring
      _ ≤ (((exceptions length).card : ℝ) +
        ((targets length).card : ℝ) * Real.exp (-cutoff)) *
          (Real.log (length : ℝ) / (length : ℝ)) := weighted
      _ = _ := by ring
  exact rearranged.trans strict.le

/-- The exact ORIGINAL-scale PNT limit for the finite harmonic weighted
sum of true type-dependent prime-counting factors.  Each `s` keeps its
own positive cutoff and its own actual exponential cutoff. -/
theorem scaleAdaptiveActualTypedPrimeCountingMajorant_tendsto
    (types : Finset ℕ) (cutoff : ℕ → ℝ)
    (type_positive : ∀ targetType ∈ types, 0 < targetType) :
    Tendsto
      (fun length : ℕ =>
        (∑ targetType ∈ types,
          (Nat.primeCounting (length / targetType) : ℝ) *
            Real.exp (-cutoff targetType)) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds
        (∑ targetType ∈ types,
          ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType))) := by
  have typed := scaleAdaptiveGlobalTypedExponentialMajorant_normalized_tendsto
    types cutoff type_positive
  apply typed.congr'
  exact Filter.Eventually.of_forall fun length => by
    dsimp
    have identity :
        (∑ targetType ∈ types,
          ((scaleAdaptiveGlobalTypedTargets targetType length).card : ℝ) *
            Real.exp (-cutoff targetType)) =
        ∑ targetType ∈ types,
          (Nat.primeCounting (length / targetType) : ℝ) *
            Real.exp (-cutoff targetType) := by
      apply Finset.sum_congr rfl
      intro targetType selected
      rw [scaleAdaptiveGlobalTypedTargets_card
        targetType length (type_positive targetType selected)]
    rw [identity]

/-- A FIXED finite family of genuine type-specific exceptional sets has
zero normalized SUM of exception cardinalities, not merely zero density
of its set-theoretic union. -/
theorem scaleAdaptiveActualTypedExceptionCardSum_tendsto_zero
    (types : Finset ℕ) (exceptions : ℕ → ℕ → Finset ℕ)
    (exception_density : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ =>
          ((exceptions targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        (∑ targetType ∈ types,
          ((exceptions targetType length).card : ℝ)) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have summed := tendsto_finsetSum types exception_density
  have target :
      Tendsto
        (fun length : ℕ =>
          ∑ targetType ∈ types,
            ((exceptions targetType length).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)) := by
    convert summed using 1
    simp
  apply target.congr'
  exact Filter.Eventually.of_forall fun length => by
    dsimp
    rw [Finset.sum_mul, Finset.sum_div]

/-- The full true TYPE-DEPENDENT finite-family exponential budget has its
exact harmonic limsup upper coefficient.  Every target family is required
only to be a subset of actual `s*q≤Y`; each type keeps its OWN load cutoff
and its OWN genuine zero-density exception. -/
theorem scaleAdaptiveActualTypedExponentialBudgets_eventually_le
    (types : Finset ℕ)
    (targets exceptions : ℕ → ℕ → Finset ℕ)
    (load : ℕ → ℕ → ℕ → ℝ)
    (cutoff : ℕ → ℝ) (slack : ℝ)
    (type_positive : ∀ targetType ∈ types, 0 < targetType)
    (target_subset : ∀ length targetType,
      targetType ∈ types →
        targets targetType length ⊆
          scaleAdaptiveGlobalTypedTargets targetType length)
    (exception_density : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ =>
          ((exceptions targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)))
    (pointwise : ∀ᶠ length : ℕ in atTop,
      ∀ targetType ∈ types,
        (∀ target ∈ targets targetType length,
          0 ≤ load targetType length target) ∧
        (∀ target ∈ targets targetType length,
          target ∉ exceptions targetType length →
            cutoff targetType ≤ load targetType length target))
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ targetType ∈ types,
        ∑ target ∈ targets targetType length,
          Real.exp (-load targetType length target)) *
            Real.log (length : ℝ) / (length : ℝ) ≤
        (∑ targetType ∈ types,
          ((targetType : ℝ)⁻¹) *
            Real.exp (-cutoff targetType)) + slack := by
  have bad := scaleAdaptiveActualTypedExceptionCardSum_tendsto_zero
    types exceptions exception_density
  have good := scaleAdaptiveActualTypedPrimeCountingMajorant_tendsto
    types cutoff type_positive
  have majorant :
      Tendsto
        (fun length : ℕ =>
          (∑ targetType ∈ types,
            ((exceptions targetType length).card : ℝ)) *
                Real.log (length : ℝ) / (length : ℝ) +
          (∑ targetType ∈ types,
            (Nat.primeCounting (length / targetType) : ℝ) *
              Real.exp (-cutoff targetType)) *
                Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds
          (∑ targetType ∈ types,
            ((targetType : ℝ)⁻¹) *
              Real.exp (-cutoff targetType))) := by
    simpa using bad.add good
  have strict := majorant.eventually
    (Iio_mem_nhds (by linarith :
      (∑ targetType ∈ types,
        ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType)) <
      (∑ targetType ∈ types,
        ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType)) + slack))
  filter_upwards [pointwise, strict, eventually_ge_atTop 2]
    with length actual strict large
  have finite :
      (∑ targetType ∈ types,
        ∑ target ∈ targets targetType length,
          Real.exp (-load targetType length target)) ≤
      (∑ targetType ∈ types,
        ((exceptions targetType length).card : ℝ)) +
      (∑ targetType ∈ types,
        (Nat.primeCounting (length / targetType) : ℝ) *
          Real.exp (-cutoff targetType)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro targetType selected
    obtain ⟨nonnegative, lower⟩ := actual targetType selected
    have one := scaleAdaptiveGlobalExponentialBudget_le_exception_card
      (targets targetType length) (exceptions targetType length)
      (load targetType length) (cutoff targetType) nonnegative lower
    refine one.trans ?_
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    rw [← scaleAdaptiveGlobalTypedTargets_card
      targetType length (type_positive targetType selected)]
    exact_mod_cast Finset.card_le_card
      (target_subset length targetType selected)
  have weighted := mul_le_mul_of_nonneg_right finite
    (scaleAdaptiveActualOriginalWeight_nonnegative large)
  have normalized :
      (∑ targetType ∈ types,
        ∑ target ∈ targets targetType length,
          Real.exp (-load targetType length target)) *
            Real.log (length : ℝ) / (length : ℝ) ≤
      (∑ targetType ∈ types,
        ((exceptions targetType length).card : ℝ)) *
          Real.log (length : ℝ) / (length : ℝ) +
      (∑ targetType ∈ types,
        (Nat.primeCounting (length / targetType) : ℝ) *
          Real.exp (-cutoff targetType)) *
            Real.log (length : ℝ) / (length : ℝ) := by
    calc
      _ = (∑ targetType ∈ types,
        ∑ target ∈ targets targetType length,
          Real.exp (-load targetType length target)) *
            (Real.log (length : ℝ) / (length : ℝ)) := by ring
      _ ≤ ((∑ targetType ∈ types,
          ((exceptions targetType length).card : ℝ)) +
        (∑ targetType ∈ types,
          (Nat.primeCounting (length / targetType) : ℝ) *
            Real.exp (-cutoff targetType))) *
              (Real.log (length : ℝ) / (length : ℝ)) := weighted
      _ = _ := by ring
  exact normalized.trans strict.le

/-- Exact prime-scale limit of a finite SUM of type-dependent exception
cardinalities with arbitrary, genuinely nonzero coefficients.  Physical
prefix cleanup therefore does not get mislabeled as zero-density. -/
theorem scaleAdaptiveActualTypedExceptionCardSum_tendsto
    (types : Finset ℕ) (exceptions : ℕ → ℕ → Finset ℕ)
    (coefficient : ℕ → ℝ)
    (exception_density : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ =>
          ((exceptions targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (coefficient targetType))) :
    Tendsto
      (fun length : ℕ =>
        (∑ targetType ∈ types,
          ((exceptions targetType length).card : ℝ)) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (∑ targetType ∈ types, coefficient targetType)) := by
  have summed := tendsto_finsetSum types exception_density
  apply summed.congr'
  exact Filter.Eventually.of_forall fun length => by
    dsimp
    rw [Finset.sum_mul, Finset.sum_div]

/-- Source-faithful ORIGINAL-scale type-dependent exponential transfer
including genuinely NONZERO physical-prefix exception coefficients.
Both contributions remain INSIDE the actual finite prime-type sum. -/
theorem scaleAdaptiveActualTypedExponentialBudgets_with_exceptions_eventually_le
    (types : Finset ℕ)
    (targets exceptions : ℕ → ℕ → Finset ℕ)
    (load : ℕ → ℕ → ℕ → ℝ)
    (cutoff exceptionCoefficient : ℕ → ℝ) (slack : ℝ)
    (type_positive : ∀ targetType ∈ types, 0 < targetType)
    (target_subset : ∀ length targetType,
      targetType ∈ types →
        targets targetType length ⊆
          scaleAdaptiveGlobalTypedTargets targetType length)
    (exception_density : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ =>
          ((exceptions targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (exceptionCoefficient targetType)))
    (pointwise : ∀ᶠ length : ℕ in atTop,
      ∀ targetType ∈ types,
        (∀ target ∈ targets targetType length,
          0 ≤ load targetType length target) ∧
        (∀ target ∈ targets targetType length,
          target ∉ exceptions targetType length →
            cutoff targetType ≤ load targetType length target))
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ targetType ∈ types,
        ∑ target ∈ targets targetType length,
          Real.exp (-load targetType length target)) *
            Real.log (length : ℝ) / (length : ℝ) ≤
        (∑ targetType ∈ types, exceptionCoefficient targetType) +
        (∑ targetType ∈ types,
          ((targetType : ℝ)⁻¹) *
            Real.exp (-cutoff targetType)) + slack := by
  have bad := scaleAdaptiveActualTypedExceptionCardSum_tendsto
    types exceptions exceptionCoefficient exception_density
  have good := scaleAdaptiveActualTypedPrimeCountingMajorant_tendsto
    types cutoff type_positive
  have majorant :
      Tendsto
        (fun length : ℕ =>
          (∑ targetType ∈ types,
            ((exceptions targetType length).card : ℝ)) *
                Real.log (length : ℝ) / (length : ℝ) +
          (∑ targetType ∈ types,
            (Nat.primeCounting (length / targetType) : ℝ) *
              Real.exp (-cutoff targetType)) *
                Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds
          ((∑ targetType ∈ types, exceptionCoefficient targetType) +
            (∑ targetType ∈ types,
              ((targetType : ℝ)⁻¹) *
                Real.exp (-cutoff targetType)))) := by
    exact bad.add good
  have strict := majorant.eventually
    (Iio_mem_nhds (by linarith :
      (∑ targetType ∈ types, exceptionCoefficient targetType) +
        (∑ targetType ∈ types,
          ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType)) <
      (∑ targetType ∈ types, exceptionCoefficient targetType) +
        (∑ targetType ∈ types,
          ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType)) + slack))
  filter_upwards [pointwise, strict, eventually_ge_atTop 2]
    with length actual strict large
  have finite :
      (∑ targetType ∈ types,
        ∑ target ∈ targets targetType length,
          Real.exp (-load targetType length target)) ≤
      (∑ targetType ∈ types,
        ((exceptions targetType length).card : ℝ)) +
      (∑ targetType ∈ types,
        (Nat.primeCounting (length / targetType) : ℝ) *
          Real.exp (-cutoff targetType)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro targetType selected
    obtain ⟨nonnegative, lower⟩ := actual targetType selected
    have one := scaleAdaptiveGlobalExponentialBudget_le_exception_card
      (targets targetType length) (exceptions targetType length)
      (load targetType length) (cutoff targetType) nonnegative lower
    refine one.trans ?_
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    rw [← scaleAdaptiveGlobalTypedTargets_card
      targetType length (type_positive targetType selected)]
    exact_mod_cast Finset.card_le_card
      (target_subset length targetType selected)
  have weighted := mul_le_mul_of_nonneg_right finite
    (scaleAdaptiveActualOriginalWeight_nonnegative large)
  have normalized :
      (∑ targetType ∈ types,
        ∑ target ∈ targets targetType length,
          Real.exp (-load targetType length target)) *
            Real.log (length : ℝ) / (length : ℝ) ≤
      (∑ targetType ∈ types,
        ((exceptions targetType length).card : ℝ)) *
          Real.log (length : ℝ) / (length : ℝ) +
      (∑ targetType ∈ types,
        (Nat.primeCounting (length / targetType) : ℝ) *
          Real.exp (-cutoff targetType)) *
            Real.log (length : ℝ) / (length : ℝ) := by
    calc
      _ = (∑ targetType ∈ types,
        ∑ target ∈ targets targetType length,
          Real.exp (-load targetType length target)) *
            (Real.log (length : ℝ) / (length : ℝ)) := by ring
      _ ≤ ((∑ targetType ∈ types,
          ((exceptions targetType length).card : ℝ)) +
        (∑ targetType ∈ types,
          (Nat.primeCounting (length / targetType) : ℝ) *
            Real.exp (-cutoff targetType))) *
              (Real.log (length : ℝ) / (length : ℝ)) := weighted
      _ = _ := by ring
  exact normalized.trans strict.le

/-- Exact actual physical-prefix divisor.  Every chosen shell has
exponent STRICTLY larger than `2^n`, so its `4N_j` prefix lies below
`Y / 2^(2^n-1)`. -/
def scaleAdaptiveActualPhysicalPrefixDivisor (parameter : ℕ) : ℕ :=
  2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1)

/-- The actual physical-prefix divisor is always positive. -/
theorem scaleAdaptiveActualPhysicalPrefixDivisor_pos
    (parameter : ℕ) :
    0 < scaleAdaptiveActualPhysicalPrefixDivisor parameter := by
  unfold scaleAdaptiveActualPhysicalPrefixDivisor
  positivity

/-- Every genuine retained physical shell satisfies the EXACT integer
prefix factor inequality; no floor or endpoint is removed. -/
theorem scaleAdaptiveActualPhysicalPrefix_factor_bound
    {parameter exponent : ℕ}
    (selected : scaleAdaptiveColoredLowerExponent parameter < exponent) :
    4 * scaleAdaptiveActualPhysicalPrefixDivisor parameter ≤
      2 ^ exponent := by
  let lower := scaleAdaptiveColoredLowerExponent parameter
  have lower_positive : 0 < lower := by
    dsimp [lower, scaleAdaptiveColoredLowerExponent]
    positivity
  have regroup : 2 + (lower - 1) = lower + 1 := by omega
  calc
    4 * scaleAdaptiveActualPhysicalPrefixDivisor parameter =
        2 ^ (2 : ℕ) * 2 ^ (lower - 1) := by
      unfold scaleAdaptiveActualPhysicalPrefixDivisor
      norm_num [lower]
    _ = 2 ^ (2 + (lower - 1)) := by rw [pow_add]
    _ = 2 ^ (lower + 1) := by rw [regroup]
    _ ≤ 2 ^ exponent := Nat.pow_le_pow_right (by norm_num)
      (by omega)

/-- Outside its exact type-dependent prime prefix, every genuine typed
target is physically interior in EVERY selected shell. -/
theorem scaleAdaptiveActualTypedTarget_interior_of_not_prefix
    {parameter targetType length target : ℕ}
    (targetType_positive : 0 < targetType)
    (typed : target ∈ scaleAdaptiveGlobalTypedTargets targetType length)
    (not_prefix : target ∉ scaleAdaptiveGlobalTypedTargets
      targetType (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter))
    {exponent : ℕ}
    (selected : scaleAdaptiveColoredLowerExponent parameter < exponent) :
    4 * (length / 2 ^ exponent) ≤ target := by
  obtain ⟨prime, prime_is_prime, bounded, equal⟩ :=
    (mem_scaleAdaptiveGlobalTypedTargets targetType_positive).mp typed
  subst target
  have above :
      length / scaleAdaptiveActualPhysicalPrefixDivisor parameter <
        targetType * prime := by
    by_contra failed
    apply not_prefix
    apply (mem_scaleAdaptiveGlobalTypedTargets targetType_positive).mpr
    exact ⟨prime, prime_is_prime, le_of_not_gt failed, rfl⟩
  exact scaleAdaptiveGlobalPhysicalInterior_of_prefix
    (scaleAdaptiveActualPhysicalPrefixDivisor_pos parameter)
    (scaleAdaptiveActualPhysicalPrefix_factor_bound selected)
    above

/-- The exact nonzero prime-scale coefficient of a genuine physical-prefix
exception for type `s` is `1/(s*d_n)`. -/
theorem scaleAdaptiveActualTypedPhysicalPrefix_normalized_tendsto
    (parameter targetType : ℕ)
    (targetType_positive : 0 < targetType) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalTypedTargets targetType
          (length / scaleAdaptiveActualPhysicalPrefixDivisor
            parameter)).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop
        (nhds
          (((targetType *
            scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹)) :=
  scaleAdaptiveGlobalTypedPrefix_normalized_tendsto
    targetType (scaleAdaptiveActualPhysicalPrefixDivisor parameter)
    targetType_positive
    (scaleAdaptiveActualPhysicalPrefixDivisor_pos parameter)

/-- A TRUE NATURAL envelope for all prime and all supported semiprime
physical prefixes.  The type sum deliberately overcounts overlaps; that
is exactly what allows the genuine exceptional union to be bounded
without asserting a nonexistent exact union-density identity. -/
def scaleAdaptiveActualPhysicalPrefixEnvelope
    (parameter length : ℕ) : ℕ :=
  (scaleAdaptiveGlobalTypedTargets 1
    (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter)).card +
  ∑ targetType ∈
    Nat.primesLE (2 ^ scaleAdaptiveColoredFullExponent parameter),
    (scaleAdaptiveGlobalTypedTargets targetType
      (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter)).card

/-- Exact ORIGINAL-scale coefficient of the complete actual natural
prefix envelope.  The first `1/d` is the prime prefix, and every genuine
supported semiprime type contributes its own exact `1/(s*d)`. -/
theorem scaleAdaptiveActualPhysicalPrefixEnvelope_normalized_tendsto
    (parameter : ℕ) :
    Tendsto
      (fun length : ℕ =>
        (scaleAdaptiveActualPhysicalPrefixEnvelope parameter length : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop
        (nhds
          (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
            (1 + adaptivePrimeHarmonicPrefix
              (2 ^ scaleAdaptiveColoredFullExponent parameter)))) := by
  let types := Nat.primesLE
    (2 ^ scaleAdaptiveColoredFullExponent parameter)
  have prime := scaleAdaptiveActualTypedPhysicalPrefix_normalized_tendsto
    parameter 1 (by omega)
  have typed : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ =>
          ((scaleAdaptiveGlobalTypedTargets targetType
            (length / scaleAdaptiveActualPhysicalPrefixDivisor
              parameter)).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
        atTop
          (nhds
            (((targetType *
              scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹)) := by
    intro targetType selected
    exact scaleAdaptiveActualTypedPhysicalPrefix_normalized_tendsto
      parameter targetType (Nat.mem_primesLE.mp selected).2.pos
  have combined := prime.add (tendsto_finsetSum types typed)
  convert combined using 1
  · ext length
    simp only [scaleAdaptiveActualPhysicalPrefixEnvelope, Nat.cast_add,
      Nat.cast_sum]
    dsimp [types]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  · dsimp [types]
    simp [adaptivePrimeHarmonicPrefix, Nat.cast_mul,
      Finset.mul_sum, mul_add]

/-- Genuine supported-prime harmonic mass is monotone in its ACTUAL
integer cutoff; all summands are nonnegative. -/
theorem scaleAdaptiveActualPrimeHarmonicPrefix_mono
    {first second : ℕ} (ordered : first ≤ second) :
    adaptivePrimeHarmonicPrefix first ≤
      adaptivePrimeHarmonicPrefix second := by
  unfold adaptivePrimeHarmonicPrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.primesLE_mono ordered)
  intro targetType _selected _not_selected
  exact inv_nonneg.mpr (Nat.cast_nonneg targetType)

/-- The actual full exponent `n*2^(n²)` is below the genuine lower
exponent at the polynomial parameter `n²+n`.  This permits the already
proved Mertens bound to control ALL supported prime types. -/
theorem scaleAdaptiveActualFullExponent_le_polynomial_lower
    (parameter : ℕ) :
    scaleAdaptiveColoredFullExponent parameter ≤
      scaleAdaptiveColoredLowerExponent (parameter ^ 2 + parameter) := by
  unfold scaleAdaptiveColoredFullExponent
    scaleAdaptiveColoredSplitExponent scaleAdaptiveColoredLowerExponent
  rw [pow_add]
  have bound : parameter ≤ 2 ^ parameter :=
    (parameter.lt_two_pow_self).le
  nlinarith [Nat.mul_le_mul_left (2 ^ (parameter ^ 2)) bound]

/-- The exact physical-prefix divisor already dominates `2^n`; this is
weaker than its true double-exponential size but suffices for polynomial
harmonic-mass decay. -/
theorem scaleAdaptiveActualPhysicalPrefixDivisor_ge_pow
    (parameter : ℕ) :
    2 ^ parameter ≤ scaleAdaptiveActualPhysicalPrefixDivisor parameter := by
  unfold scaleAdaptiveActualPhysicalPrefixDivisor
    scaleAdaptiveColoredLowerExponent
  apply Nat.pow_le_pow_right (by norm_num)
  have strict := parameter.lt_two_pow_self
  omega

/-- ALL supported prime types through the true full cutoff have only
quadratic actual harmonic mass.  The proof uses genuine Mertens and
monotonicity, never the number of available types. -/
theorem scaleAdaptiveActualFullTypeHarmonicMass_le_quadratic
    (parameter : ℕ) :
    adaptivePrimeHarmonicPrefix
      (2 ^ scaleAdaptiveColoredFullExponent parameter) ≤
      ((parameter ^ 2 + parameter : ℕ) : ℝ) * Real.log (2 : ℝ) +
        |Real.log (Real.log (2 : ℝ))| + |Mertens.M| +
          adaptiveMertensHarmonicErrorConstant / Real.log (2 : ℝ) := by
  have cutoff_bound :
      2 ^ scaleAdaptiveColoredFullExponent parameter ≤
        2 ^ scaleAdaptiveColoredLowerExponent
          (parameter ^ 2 + parameter) :=
    Nat.pow_le_pow_right (by norm_num)
      (scaleAdaptiveActualFullExponent_le_polynomial_lower parameter)
  exact (scaleAdaptiveActualPrimeHarmonicPrefix_mono cutoff_bound).trans
    (scaleAdaptiveGlobalEarlyLowTypeHarmonicMass_le_affine
      (parameter ^ 2 + parameter))

/-- The ACTUAL complete prime-plus-all-semiprime physical-prefix
coefficient vanishes with the adaptive parameter.  This closes the real
prefix-cleanup obstruction without falsely calling any fixed-parameter
physical prefix a zero-density exceptional set. -/
theorem scaleAdaptiveActualPhysicalPrefixCoefficient_tendsto_zero :
    Tendsto
      (fun parameter : ℕ =>
        (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
          (1 + adaptivePrimeHarmonicPrefix
            (2 ^ scaleAdaptiveColoredFullExponent parameter))))
      atTop (nhds (0 : ℝ)) := by
  let remainder : ℝ :=
    |Real.log (Real.log (2 : ℝ))| + |Mertens.M| +
      adaptiveMertensHarmonicErrorConstant / Real.log (2 : ℝ)
  let constant : ℝ := max 1 (1 + remainder)
  have constant_positive : 0 < constant :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have model :
      Tendsto
        (fun parameter : ℕ =>
          constant * (((parameter : ℝ) ^ 2 + (parameter : ℝ) + 1) /
            (2 : ℝ) ^ parameter))
        atTop (nhds (0 : ℝ)) := by
    have quadratic := tendsto_pow_const_div_const_pow_of_one_lt
      2 (by norm_num : (1 : ℝ) < 2)
    have linear := tendsto_pow_const_div_const_pow_of_one_lt
      1 (by norm_num : (1 : ℝ) < 2)
    have one := tendsto_pow_const_div_const_pow_of_one_lt
      0 (by norm_num : (1 : ℝ) < 2)
    convert ((quadratic.add linear).add one).const_mul constant using 1
    · funext parameter
      simp only [pow_one, pow_zero]
      ring
    · simp
  apply squeeze_zero' _ _ model
  · exact Filter.Eventually.of_forall fun parameter => by
      have harmonic_nonnegative :
          0 ≤ adaptivePrimeHarmonicPrefix
            (2 ^ scaleAdaptiveColoredFullExponent parameter) := by
        unfold adaptivePrimeHarmonicPrefix
        exact Finset.sum_nonneg fun targetType _ =>
          inv_nonneg.mpr (Nat.cast_nonneg targetType)
      exact mul_nonneg
        (inv_nonneg.mpr (Nat.cast_nonneg _)) (by linarith)
  · exact Filter.Eventually.of_forall fun parameter => by
      have harmonic_nonnegative :
          0 ≤ adaptivePrimeHarmonicPrefix
            (2 ^ scaleAdaptiveColoredFullExponent parameter) := by
        unfold adaptivePrimeHarmonicPrefix
        exact Finset.sum_nonneg fun targetType _ =>
          inv_nonneg.mpr (Nat.cast_nonneg targetType)
      have logarithm_bound : Real.log (2 : ℝ) ≤ 1 := by
        have estimate := Real.log_le_sub_one_of_pos
          (by norm_num : (0 : ℝ) < 2)
        norm_num at estimate ⊢
        exact estimate
      have harmonic := scaleAdaptiveActualFullTypeHarmonicMass_le_quadratic
        parameter
      have parameter_nonnegative : (0 : ℝ) ≤ parameter := Nat.cast_nonneg _
      have polynomial_nonnegative :
          0 ≤ (parameter : ℝ) ^ 2 + (parameter : ℝ) := by positivity
      have polynomial_bound := mul_le_mul_of_nonneg_left
        logarithm_bound polynomial_nonnegative
      have remainder_bound : 1 + remainder ≤ constant :=
        le_max_right _ _
      have constant_bound : (1 : ℝ) ≤ constant := le_max_left _ _
      have harmonic_bound :
          1 + adaptivePrimeHarmonicPrefix
            (2 ^ scaleAdaptiveColoredFullExponent parameter) ≤
            constant * ((parameter : ℝ) ^ 2 + (parameter : ℝ) + 1) := by
        push_cast at harmonic
        dsimp [remainder] at remainder_bound ⊢
        nlinarith [mul_nonneg (sub_nonneg.mpr constant_bound)
          polynomial_nonnegative]
      have divisor_order :
          ((2 ^ parameter : ℕ) : ℝ) ≤
            scaleAdaptiveActualPhysicalPrefixDivisor parameter := by
        exact_mod_cast scaleAdaptiveActualPhysicalPrefixDivisor_ge_pow
          parameter
      have power_positive : (0 : ℝ) < (2 : ℝ) ^ parameter := by positivity
      have inverse_order :
          (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹) ≤
            ((2 : ℝ) ^ parameter)⁻¹ := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat] at divisor_order
        simpa [one_div] using
          one_div_le_one_div_of_le power_positive divisor_order
      have product := mul_le_mul inverse_order harmonic_bound
        (by linarith : 0 ≤ 1 + adaptivePrimeHarmonicPrefix
          (2 ^ scaleAdaptiveColoredFullExponent parameter))
        (by positivity : 0 ≤ ((2 : ℝ) ^ parameter)⁻¹)
      calc
        _ ≤ ((2 : ℝ) ^ parameter)⁻¹ *
          (constant * ((parameter : ℝ) ^ 2 + (parameter : ℝ) + 1)) := product
        _ = _ := by ring

/-- The actual SET of all prime and supported-semiprime physical-prefix
targets.  Different prime types can genuinely overlap, so its cardinality
is bounded above by, not identified with, the natural envelope. -/
def scaleAdaptiveActualPhysicalPrefixTargets
    (parameter length : ℕ) : Finset ℕ :=
  scaleAdaptiveGlobalTypedTargets 1
      (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter) ∪
    (Nat.primesLE
      (2 ^ scaleAdaptiveColoredFullExponent parameter)).biUnion
        fun targetType => scaleAdaptiveGlobalTypedTargets targetType
          (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter)

/-- The REAL union of physical prefixes never has more targets than the
exact natural prime-plus-type envelope.  No disjointness is asserted. -/
theorem scaleAdaptiveActualPhysicalPrefixTargets_card_le_envelope
    (parameter length : ℕ) :
    (scaleAdaptiveActualPhysicalPrefixTargets parameter length).card ≤
      scaleAdaptiveActualPhysicalPrefixEnvelope parameter length := by
  unfold scaleAdaptiveActualPhysicalPrefixTargets
    scaleAdaptiveActualPhysicalPrefixEnvelope
  have union := Finset.card_union_le
    (scaleAdaptiveGlobalTypedTargets 1
      (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter))
    ((Nat.primesLE
      (2 ^ scaleAdaptiveColoredFullExponent parameter)).biUnion
        fun targetType => scaleAdaptiveGlobalTypedTargets targetType
          (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter))
  have types := Finset.card_biUnion_le
    (s := Nat.primesLE
      (2 ^ scaleAdaptiveColoredFullExponent parameter))
    (t := fun targetType => scaleAdaptiveGlobalTypedTargets targetType
      (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter))
  omega

/-- A genuine type prefix belongs to the ACTUAL global physical-prefix
set whenever its prime type is supported by the true full cutoff. -/
theorem scaleAdaptiveActualTypedPrefix_subset_global
    {parameter targetType : ℕ}
    (supported : targetType ∈
      Nat.primesLE (2 ^ scaleAdaptiveColoredFullExponent parameter))
    (length : ℕ) :
    scaleAdaptiveGlobalTypedTargets targetType
      (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter) ⊆
        scaleAdaptiveActualPhysicalPrefixTargets parameter length := by
  intro target selected
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨targetType, supported, selected⟩)

/-- The true prime prefix also belongs to the global physical-prefix set. -/
theorem scaleAdaptiveActualPrimePrefix_subset_global
    (parameter length : ℕ) :
    scaleAdaptiveGlobalTypedTargets 1
      (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter) ⊆
        scaleAdaptiveActualPhysicalPrefixTargets parameter length := by
  exact Finset.subset_union_left

/-- Source-faithful LOW missing-hit coefficient: prime targets and EVERY
actual low type, retaining its own genuine eligible physical shell tail.
The factor `1/32` includes exact fair color splitting and the proved
restricted target-load constant `1/16`. -/
noncomputable def scaleAdaptiveActualLowBudgetCoefficient
    (parameter : ℕ) : ℝ :=
  Real.exp (-(1 / 32 : ℝ) *
    scaleAdaptiveDyadicEulerShellMass
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredFullExponent parameter)) +
  ∑ targetType ∈ Nat.primesLE
    (2 ^ scaleAdaptiveColoredSplitExponent parameter),
    ((targetType : ℝ)⁻¹) *
      Real.exp (-(1 / 32 : ℝ) *
        scaleAdaptiveLowEligibleDyadicEulerShell
          targetType (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          (scaleAdaptiveColoredLowerExponent parameter)
          (scaleAdaptiveColoredFullExponent parameter))

/-- Source-faithful HIGH missing-hit coefficient: every actual prime
target and the COMPLETE true supported high-type harmonic mass. -/
noncomputable def scaleAdaptiveActualHighBudgetCoefficient
    (parameter : ℕ) : ℝ :=
  Real.exp (-(1 / 32 : ℝ) *
    scaleAdaptiveHighDyadicEulerShellMass
      (scaleAdaptiveColoredFullExponent parameter)
      (scaleAdaptiveColoredSplitExponent parameter)
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredSplitExponent parameter)) +
  adaptivePrimeHarmonicInterval
    (2 ^ scaleAdaptiveColoredSplitExponent parameter)
    (2 ^ scaleAdaptiveColoredFullExponent parameter) *
      Real.exp (-(1 / 32 : ℝ) *
        scaleAdaptiveHighDyadicEulerShellMass
          (scaleAdaptiveColoredFullExponent parameter)
          (scaleAdaptiveColoredSplitExponent parameter)
          (scaleAdaptiveColoredLowerExponent parameter)
          (scaleAdaptiveColoredSplitExponent parameter))

/-- Both genuine fair-color-aware original missing-hit coefficients
vanish together, with all low-type eligible tails preserved. -/
theorem scaleAdaptiveActualColoredBudgetCoefficients_tendsto_zero :
    Tendsto
      (fun parameter : ℕ =>
        scaleAdaptiveActualLowBudgetCoefficient parameter +
          scaleAdaptiveActualHighBudgetCoefficient parameter)
      atTop (nhds (0 : ℝ)) := by
  have complete :=
    scaleAdaptiveGlobalCompleteColoredExponentialBudgets_tendsto_zero
      (by norm_num : (0 : ℝ) < 1 / 32)
      (by norm_num : (0 : ℝ) < 1 / 32)
      (by norm_num : (0 : ℝ) < 1 / 32)
      (by norm_num : (0 : ℝ) < 1 / 32)
  apply complete.congr'
  exact Filter.Eventually.of_forall fun parameter => by
    unfold scaleAdaptiveActualLowBudgetCoefficient
      scaleAdaptiveActualHighBudgetCoefficient
    ring

/-- Every individual actual LOW coefficient is nonnegative. -/
theorem scaleAdaptiveActualLowBudgetCoefficient_nonnegative
    (parameter : ℕ) :
    0 ≤ scaleAdaptiveActualLowBudgetCoefficient parameter := by
  unfold scaleAdaptiveActualLowBudgetCoefficient
  apply add_nonneg (Real.exp_pos _).le
  apply Finset.sum_nonneg
  intro targetType _selected
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Real.exp_pos _).le

/-- Every individual actual HIGH coefficient is nonnegative. -/
theorem scaleAdaptiveActualHighBudgetCoefficient_nonnegative
    (parameter : ℕ) :
    0 ≤ scaleAdaptiveActualHighBudgetCoefficient parameter := by
  unfold scaleAdaptiveActualHighBudgetCoefficient
  apply add_nonneg (Real.exp_pos _).le
  apply mul_nonneg _ (Real.exp_pos _).le
  unfold adaptivePrimeHarmonicInterval
  exact Finset.sum_nonneg fun targetType _ =>
    inv_nonneg.mpr (Nat.cast_nonneg targetType)

/-- BOTH actual full-shell cross-support target-loss sets.  Taking the
full exponent family includes every type-specific eligible tail; no
unsupported shell is used to claim a positive semiprime load. -/
noncomputable def scaleAdaptiveActualCrossExceptions
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) : Finset ℕ :=
  scaleAdaptiveRestrictedMultiShellCrossBadTargets
    configuration.exponents configuration.lowSupport
      configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular length ∪
    scaleAdaptiveRestrictedMultiShellCrossBadTargets
      configuration.exponents configuration.highSupport
        configuration.lowSupport configuration.highSupport
          configuration.lower configuration.upper
          configuration.lowSingular configuration.highSingular length

/-- Real cross-support target deletion has zero ORIGINAL prime-scale
density directly from the SAME configuration's actual label-rejection
limits, separately for BOTH genuine mixed-pattern support families. -/
theorem scaleAdaptiveActualCrossExceptions_normalized_tendsto_zero
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
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
        ((scaleAdaptiveActualCrossExceptions
          configuration length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveActualCrossExceptions
  apply scaleAdaptiveGlobalBadUnion_normalized_tendsto_zero
  · exact scaleAdaptiveRestrictedMultiShellCrossBadTargets_tendsto_zero
      configuration.exponents configuration.lowSupport
        configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
          low_primes rejected
  · exact scaleAdaptiveRestrictedMultiShellCrossBadTargets_tendsto_zero
      configuration.exponents configuration.highSupport
        configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper
        configuration.lowSingular configuration.highSingular
          high_primes rejected

/-- The genuine exceptional SET for the final joint interface adds the
actual supported physical prefixes to ALL original deficient-target,
boundary, mixed-pattern, and BOTH true cross-support-loss exceptions.
The intersection retains the exact original closed target interval. -/
noncomputable def scaleAdaptiveActualAugmentedExceptions
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (coreParameter adaptiveParameter length : ℕ) : Finset ℕ :=
  scaleAdaptiveGlobalCompleteTargetExceptions
    length coreParameter configuration.exponents configuration.exponents
      configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper ∪
    (Finset.Icc 1 length ∩
      (scaleAdaptiveActualPhysicalPrefixTargets adaptiveParameter length ∪
        scaleAdaptiveActualCrossExceptions configuration length))

/-- Actual augmented exceptional targets stay in the ORIGINAL interval. -/
theorem scaleAdaptiveActualAugmentedExceptions_subset_interval
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (coreParameter adaptiveParameter length : ℕ) :
    scaleAdaptiveActualAugmentedExceptions
      configuration coreParameter adaptiveParameter length ⊆
        Finset.Icc 1 length := by
  intro target selected
  rcases Finset.mem_union.mp selected with original | physical
  · exact scaleAdaptiveGlobalCompleteTargetExceptions_subset_interval
      length coreParameter configuration.exponents configuration.exponents
        configuration.lowSupport configuration.highSupport
          configuration.lower configuration.upper original
  · exact (Finset.mem_inter.mp physical).1

/-- The enlarged actual exception family contains ALL basic original
deficiency, both-color prime-pattern, and physical-boundary exceptions. -/
theorem scaleAdaptiveActualCompleteExceptions_subset_augmented
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (coreParameter adaptiveParameter length : ℕ) :
    scaleAdaptiveGlobalCompleteTargetExceptions
      length coreParameter configuration.exponents configuration.exponents
        configuration.lowSupport configuration.highSupport
          configuration.lower configuration.upper ⊆
    scaleAdaptiveActualAugmentedExceptions
      configuration coreParameter adaptiveParameter length := by
  exact Finset.subset_union_left

/-- TRUE NATURAL envelope for the augmented exception set; overlapping
families are added only in the envelope, never asserted disjoint. -/
noncomputable def scaleAdaptiveActualAugmentedExceptionEnvelope
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (coreParameter adaptiveParameter length : ℕ) : ℕ :=
  (scaleAdaptiveGlobalCompleteTargetExceptions
    length coreParameter configuration.exponents configuration.exponents
      configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper).card +
    scaleAdaptiveActualPhysicalPrefixEnvelope adaptiveParameter length +
      (scaleAdaptiveActualCrossExceptions configuration length).card

/-- Exact honest cardinal upper bound for the actual augmented union. -/
theorem scaleAdaptiveActualAugmentedExceptions_card_le_envelope
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (coreParameter adaptiveParameter length : ℕ) :
    (scaleAdaptiveActualAugmentedExceptions
      configuration coreParameter adaptiveParameter length).card ≤
      scaleAdaptiveActualAugmentedExceptionEnvelope
        configuration coreParameter adaptiveParameter length := by
  unfold scaleAdaptiveActualAugmentedExceptions
    scaleAdaptiveActualAugmentedExceptionEnvelope
  have union := Finset.card_union_le
    (scaleAdaptiveGlobalCompleteTargetExceptions
      length coreParameter configuration.exponents configuration.exponents
        configuration.lowSupport configuration.highSupport
          configuration.lower configuration.upper)
    (Finset.Icc 1 length ∩
      (scaleAdaptiveActualPhysicalPrefixTargets adaptiveParameter length ∪
        scaleAdaptiveActualCrossExceptions configuration length))
  have restricted := Finset.card_le_card
    (Finset.inter_subset_right :
      Finset.Icc 1 length ∩
        (scaleAdaptiveActualPhysicalPrefixTargets adaptiveParameter length ∪
          scaleAdaptiveActualCrossExceptions configuration length) ⊆
            scaleAdaptiveActualPhysicalPrefixTargets adaptiveParameter length ∪
              scaleAdaptiveActualCrossExceptions configuration length)
  have cross_union := Finset.card_union_le
    (scaleAdaptiveActualPhysicalPrefixTargets adaptiveParameter length)
    (scaleAdaptiveActualCrossExceptions configuration length)
  have physical := scaleAdaptiveActualPhysicalPrefixTargets_card_le_envelope
    adaptiveParameter length
  omega

/-- Exact ORIGINAL-scale coefficient of the TRUE NATURAL augmented
exception envelope: historical small-prime cleanup `1/z` PLUS the actual
prime-and-all-types physical prefix coefficient.  This uses sole signed
Green--Tao for the already proved mixed-pattern exception limit. -/
theorem scaleAdaptiveActualAugmentedExceptionEnvelope_normalized_tendsto_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (coreParameter adaptiveParameter : ℕ)
    (core_positive : 0 < coreParameter)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
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
        atTop (nhds (0 : ℝ)))
    (lower_nonnegative : 0 ≤ configuration.lower)
    (band_nonempty : configuration.lower < configuration.upper)
    (upper_bounded : configuration.upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        (scaleAdaptiveActualAugmentedExceptionEnvelope
          configuration coreParameter adaptiveParameter length : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop
        (nhds
          (((coreParameter : ℝ)⁻¹) +
            (((scaleAdaptiveActualPhysicalPrefixDivisor
              adaptiveParameter : ℕ) : ℝ)⁻¹ *
                (1 + adaptivePrimeHarmonicPrefix
                  (2 ^ scaleAdaptiveColoredFullExponent
                    adaptiveParameter))))) := by
  have original :=
    scaleAdaptiveGlobalCompleteTargetExceptions_normalized_tendsto
      green_tao coreParameter configuration.exponents configuration.exponents
        configuration.lowSupport configuration.highSupport
        configuration.lower configuration.upper core_positive
          low_primes high_primes lower_nonnegative band_nonempty upper_bounded
  have physical := scaleAdaptiveActualPhysicalPrefixEnvelope_normalized_tendsto
    adaptiveParameter
  have cross := scaleAdaptiveActualCrossExceptions_normalized_tendsto_zero
    configuration low_primes high_primes rejected
  convert (original.add physical).add cross using 1
  · ext length
    simp only [scaleAdaptiveActualAugmentedExceptionEnvelope,
      Nat.cast_add]
    ring
  · simp

/-- A finite cover by actual type families bounds a nonnegative target
sum by the SUM of its typewise sums, even when those broad type families
overlap.  No false disjointness of generic `s*q` sets is assumed. -/
theorem scaleAdaptiveActualNonnegativeSum_le_typeCover
    (types targets : Finset ℕ) (families : ℕ → Finset ℕ)
    (weight : ℕ → ℝ)
    (nonnegative : ∀ target : ℕ, 0 ≤ weight target)
    (covered : targets ⊆ types.biUnion families) :
    (∑ target ∈ targets, weight target) ≤
      ∑ targetType ∈ types,
        ∑ target ∈ families targetType, weight target := by
  classical
  have pointwise : ∀ target ∈ targets,
      weight target ≤
        ∑ targetType ∈ types,
          if target ∈ families targetType then weight target else 0 := by
    intro target selected
    obtain ⟨targetType, targetType_selected, belongs⟩ :=
      Finset.mem_biUnion.mp (covered selected)
    have one := Finset.single_le_sum
      (f := fun candidate : ℕ =>
        if target ∈ families candidate then weight target else 0)
      (fun candidate _ => by
        split
        · exact nonnegative target
        · exact le_refl 0)
      targetType_selected
    simpa [belongs] using one
  calc
    _ ≤ ∑ target ∈ targets,
      ∑ targetType ∈ types,
        if target ∈ families targetType then weight target else 0 :=
          Finset.sum_le_sum pointwise
    _ = ∑ targetType ∈ types,
      ∑ target ∈ targets,
        if target ∈ families targetType then weight target else 0 := by
          rw [Finset.sum_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro targetType _selected
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro target belongs
        exact (Finset.mem_filter.mp belongs).2
      · intro target _belongs _outside
        exact nonnegative target

/-- Every ACTUAL low semiprime target is covered by its genuine prime
type family; only types up to the exact closed low cutoff are used. -/
theorem scaleAdaptiveActualLowSemiprimeTargets_subset_typeCover
    {length core cutoff : ℕ} (core_positive : 0 < core) :
    scaleAdaptiveGlobalLowSemiprimeTargets length core cutoff ⊆
      (Nat.primesLE cutoff).biUnion
        fun targetType => scaleAdaptiveGlobalTypedTargets targetType length := by
  intro target selected
  obtain ⟨targetType, prime, type_prime, _small, cutoff_bound,
    prime_prime, _large, bounded, equal⟩ :=
      (mem_scaleAdaptiveGlobalLowSemiprimeTargets core_positive).mp selected
  apply Finset.mem_biUnion.mpr
  refine ⟨targetType, Nat.mem_primesLE.mpr
    ⟨cutoff_bound, type_prime⟩, ?_⟩
  exact (mem_scaleAdaptiveGlobalTypedTargets type_prime.pos).mpr
    ⟨prime, prime_prime, bounded, equal⟩

/-- Every ACTUAL high semiprime target is covered by precisely the genuine
upper support prime types; the lower endpoint is OPEN and the full
endpoint is CLOSED. -/
theorem scaleAdaptiveActualHighSemiprimeTargets_subset_typeCover
    {length core cutoff full : ℕ} (core_positive : 0 < core)
    (core_endpoint : core = full + 1) :
    scaleAdaptiveGlobalHighSemiprimeTargets length core cutoff ⊆
      ((Nat.primesLE full) \ (Nat.primesLE cutoff)).biUnion
        fun targetType => scaleAdaptiveGlobalTypedTargets targetType length := by
  intro target selected
  obtain ⟨targetType, prime, type_prime, strict,
    after_cutoff, prime_prime, _large, bounded, equal⟩ :=
      (mem_scaleAdaptiveGlobalHighSemiprimeTargets core_positive).mp selected
  have at_most : targetType ≤ full := by omega
  have chosen : targetType ∈
      (Nat.primesLE full) \ (Nat.primesLE cutoff) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨at_most, type_prime⟩, ?_⟩
    intro small
    exact (Nat.not_le_of_lt after_cutoff)
      (Nat.mem_primesLE.mp small).1
  exact Finset.mem_biUnion.mpr
    ⟨targetType, chosen,
      (mem_scaleAdaptiveGlobalTypedTargets type_prime.pos).mpr
        ⟨prime, prime_prime, bounded, equal⟩⟩

/-- Adding a true zero-density target set to a physical-prefix family
preserves the prefix's exact NONZERO original prime-scale coefficient,
without asserting disjointness or an exact finite union cardinality. -/
theorem scaleAdaptiveActualZeroBadUnion_normalized_tendsto
    (bad physical : ℕ → Finset ℕ) (coefficient : ℝ)
    (bad_density : Tendsto
      (fun length : ℕ => ((bad length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)))
    (physical_density : Tendsto
      (fun length : ℕ => ((physical length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds coefficient)) :
    Tendsto
      (fun length : ℕ => ((bad length ∪ physical length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds coefficient) := by
  have upper :
      Tendsto
        (fun length : ℕ =>
          (((bad length).card : ℝ) + ((physical length).card : ℝ)) *
            Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds coefficient) := by
    convert bad_density.add physical_density using 1
    · ext length
      ring
    · simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    physical_density upper
  · filter_upwards [eventually_ge_atTop 2] with length large
    have card := Finset.card_le_card
      (Finset.subset_union_right :
        physical length ⊆ bad length ∪ physical length)
    have real_card :
        ((physical length).card : ℝ) ≤
          ((bad length ∪ physical length).card : ℝ) := by
      exact_mod_cast card
    calc
      _ = ((physical length).card : ℝ) *
        (Real.log (length : ℝ) / (length : ℝ)) := by ring
      _ ≤ ((bad length ∪ physical length).card : ℝ) *
        (Real.log (length : ℝ) / (length : ℝ)) :=
          mul_le_mul_of_nonneg_right real_card
            (scaleAdaptiveActualOriginalWeight_nonnegative large)
      _ = _ := by ring
  · filter_upwards [eventually_ge_atTop 2] with length large
    have card := Finset.card_union_le (bad length) (physical length)
    have real_card :
        ((bad length ∪ physical length).card : ℝ) ≤
          ((bad length).card : ℝ) + ((physical length).card : ℝ) := by
      exact_mod_cast card
    calc
      _ = ((bad length ∪ physical length).card : ℝ) *
        (Real.log (length : ℝ) / (length : ℝ)) := by ring
      _ ≤ (((bad length).card : ℝ) + ((physical length).card : ℝ)) *
        (Real.log (length : ℝ) / (length : ℝ)) :=
          mul_le_mul_of_nonneg_right real_card
            (scaleAdaptiveActualOriginalWeight_nonnegative large)
      _ = _ := by ring

/-- Every fixed finite genuine physical shell becomes large enough at the
original target scale; the full exponent family is fixed BEFORE `Y→∞`. -/
theorem scaleAdaptiveActualPhysicalScales_eventually_large
    (exponents : Finset ℕ) :
    ∀ᶠ length : ℕ in atTop,
      ∀ exponent ∈ exponents,
        2 ^ exponent ≤ length / 2 ^ exponent := by
  have each : ∀ exponent ∈ exponents,
      ∀ᶠ length : ℕ in atTop,
        2 ^ exponent ≤ length / 2 ^ exponent := by
    intro exponent _selected
    filter_upwards [eventually_ge_atTop ((2 ^ exponent) * (2 ^ exponent))]
      with length large
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr large
  exact (Filter.eventually_all_finset exponents).mpr each

/-- Original low-colored targets are covered by the genuine type families
`s=1` (prime targets) and actual low prime types.  Overlap is allowed. -/
theorem scaleAdaptiveActualLowTargets_subset_typeCover
    {length core cutoff : ℕ} (core_positive : 0 < core) :
    scaleAdaptiveGlobalLowTargets length core cutoff ⊆
      (insert 1 (Nat.primesLE cutoff)).biUnion
        fun targetType => scaleAdaptiveGlobalTypedTargets targetType length := by
  intro target selected
  rcases Finset.mem_union.mp selected with prime | semiprime
  · obtain ⟨is_prime, _large, bounded⟩ :=
      mem_fixedCoreLargePrimeTargets.mp prime
    apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_insert_self _ _, ?_⟩
    exact (mem_scaleAdaptiveGlobalTypedTargets (by omega)).mpr
      ⟨target, is_prime, by simpa using bounded, by simp⟩
  · have covered := scaleAdaptiveActualLowSemiprimeTargets_subset_typeCover
      core_positive semiprime
    obtain ⟨targetType, selected_type, belongs⟩ :=
      Finset.mem_biUnion.mp covered
    exact Finset.mem_biUnion.mpr
      ⟨targetType, Finset.mem_insert_of_mem selected_type, belongs⟩

/-- Original high-colored targets are covered by type `s=1` and the
genuine OPEN-low/CLOSED-high supported prime-type interval. -/
theorem scaleAdaptiveActualHighTargets_subset_typeCover
    {length core cutoff full : ℕ} (core_positive : 0 < core)
    (core_endpoint : core = full + 1) :
    scaleAdaptiveGlobalHighTargets length core cutoff ⊆
      (insert 1 ((Nat.primesLE full) \ (Nat.primesLE cutoff))).biUnion
        fun targetType => scaleAdaptiveGlobalTypedTargets targetType length := by
  intro target selected
  rcases Finset.mem_union.mp selected with prime | semiprime
  · obtain ⟨is_prime, _large, bounded⟩ :=
      mem_fixedCoreLargePrimeTargets.mp prime
    exact Finset.mem_biUnion.mpr
      ⟨1, Finset.mem_insert_self _ _,
        (mem_scaleAdaptiveGlobalTypedTargets (by omega)).mpr
          ⟨target, is_prime, by simpa using bounded, by simp⟩⟩
  · obtain ⟨targetType, selected_type, belongs⟩ :=
      Finset.mem_biUnion.mp
        (scaleAdaptiveActualHighSemiprimeTargets_subset_typeCover
          core_positive core_endpoint semiprime)
    exact Finset.mem_biUnion.mpr
      ⟨targetType, Finset.mem_insert_of_mem selected_type, belongs⟩

/-- Every finite selected collection of supported prime types, optionally
including the genuine prime-target type `1`, has physical-prefix cost at
most the FULL actual natural-envelope coefficient. -/
theorem scaleAdaptiveActualPhysicalTypeCoefficient_le_global
    (parameter : ℕ) (types : Finset ℕ)
    (supported : types ⊆
      insert 1 (Nat.primesLE
        (2 ^ scaleAdaptiveColoredFullExponent parameter))) :
    (∑ targetType ∈ types,
      (((targetType *
        scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹)) ≤
      (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
        (1 + adaptivePrimeHarmonicPrefix
          (2 ^ scaleAdaptiveColoredFullExponent parameter))) := by
  have one_not_prime :
      1 ∉ Nat.primesLE
        (2 ^ scaleAdaptiveColoredFullExponent parameter) := by
    intro selected
    exact Nat.not_prime_one (Nat.mem_primesLE.mp selected).2
  have majorant := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun targetType : ℕ =>
      (((targetType *
        scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹))
    supported
    (fun targetType _selected _outside =>
      inv_nonneg.mpr (Nat.cast_nonneg _))
  refine majorant.trans_eq ?_
  rw [Finset.sum_insert one_not_prime]
  simp [adaptivePrimeHarmonicPrefix, Nat.cast_mul, Finset.mul_sum,
    mul_add]

/-- CENTRAL fixed-family transfer: genuine ACTUAL target loads with
type-dependent zero-density bad sets and type-dependent physical prefixes
give the true original-scale exponential coefficient.  Broad type families
may overlap; their genuine harmonic weights and all prefix coefficients
are retained separately.  This is analytic finite bookkeeping, not an
additional covering hypothesis. -/
theorem scaleAdaptiveActualCoveredTypedMissBudget_eventually_le
    (parameter : ℕ) (types : Finset ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → ℕ → ℝ)
    (cutoff : ℕ → ℝ)
    (bad : ℕ → ℕ → Finset ℕ)
    (slack : ℝ)
    (type_positive : ∀ targetType ∈ types, 0 < targetType)
    (covered : ∀ length : ℕ,
      targets length ⊆ types.biUnion fun targetType =>
        scaleAdaptiveGlobalTypedTargets targetType length)
    (bad_density : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ => ((bad targetType length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)))
    (nonnegative : ∀ᶠ length : ℕ in atTop,
      ∀ target : ℕ, 0 ≤ load length target)
    (good : ∀ᶠ length : ℕ in atTop,
      ∀ targetType ∈ types,
        ∀ target ∈ scaleAdaptiveGlobalTypedTargets targetType length,
          target ∉ bad targetType length →
          target ∉ scaleAdaptiveGlobalTypedTargets targetType
            (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter) →
            cutoff targetType ≤ load length target)
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ target ∈ targets length,
        Real.exp (-load length target)) *
          Real.log (length : ℝ) / (length : ℝ) ≤
        (∑ targetType ∈ types,
          (((targetType *
            scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹)) +
        (∑ targetType ∈ types,
          ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType)) + slack := by
  let exceptions : ℕ → ℕ → Finset ℕ := fun targetType length =>
    bad targetType length ∪
      scaleAdaptiveGlobalTypedTargets targetType
        (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter)
  have exceptions_density : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ =>
          ((exceptions targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
        atTop
          (nhds
            (((targetType *
              scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹)) := by
    intro targetType selected
    exact scaleAdaptiveActualZeroBadUnion_normalized_tendsto
      (bad targetType)
      (fun length => scaleAdaptiveGlobalTypedTargets targetType
        (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter))
      (((targetType *
        scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹)
      (bad_density targetType selected)
      (scaleAdaptiveActualTypedPhysicalPrefix_normalized_tendsto
        parameter targetType (type_positive targetType selected))
  have pointwise : ∀ᶠ length : ℕ in atTop,
      ∀ targetType ∈ types,
        (∀ target ∈ scaleAdaptiveGlobalTypedTargets targetType length,
          0 ≤ load length target) ∧
        (∀ target ∈ scaleAdaptiveGlobalTypedTargets targetType length,
          target ∉ exceptions targetType length →
            cutoff targetType ≤ load length target) := by
    filter_upwards [nonnegative, good] with length positive lower
    intro targetType selected
    refine ⟨fun target _ => positive target, ?_⟩
    intro target belongs outside
    apply lower targetType selected target belongs
    · intro included
      exact outside (Finset.mem_union_left _ included)
    · intro included
      exact outside (Finset.mem_union_right _ included)
  have majorant :=
    scaleAdaptiveActualTypedExponentialBudgets_with_exceptions_eventually_le
      types (fun targetType length =>
        scaleAdaptiveGlobalTypedTargets targetType length)
      exceptions (fun _ length target => load length target)
      cutoff
      (fun targetType =>
        (((targetType *
          scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹))
      slack type_positive
      (fun _ _ _ => Finset.Subset.rfl)
      exceptions_density pointwise slack_positive
  filter_upwards [majorant, eventually_ge_atTop 2] with length estimate large
  have cover := scaleAdaptiveActualNonnegativeSum_le_typeCover
    types (targets length)
    (fun targetType => scaleAdaptiveGlobalTypedTargets targetType length)
    (fun target => Real.exp (-load length target))
    (fun _ => (Real.exp_pos _).le)
    (covered length)
  have weighted := mul_le_mul_of_nonneg_right cover
    (scaleAdaptiveActualOriginalWeight_nonnegative large)
  calc
    _ = (∑ target ∈ targets length, Real.exp (-load length target)) *
      (Real.log (length : ℝ) / (length : ℝ)) := by ring
    _ ≤ (∑ targetType ∈ types,
      ∑ target ∈ scaleAdaptiveGlobalTypedTargets targetType length,
        Real.exp (-load length target)) *
          (Real.log (length : ℝ) / (length : ℝ)) := weighted
    _ = (∑ targetType ∈ types,
      ∑ target ∈ scaleAdaptiveGlobalTypedTargets targetType length,
        Real.exp (-load length target)) *
          Real.log (length : ℝ) / (length : ℝ) := by ring
    _ ≤ _ := estimate

/-- The finite LOW type family includes true prime targets as type `1`
and every genuine supported low semiprime prime type. -/
def scaleAdaptiveActualLowTargetTypes (parameter : ℕ) : Finset ℕ :=
  insert 1 (Nat.primesLE
    (2 ^ scaleAdaptiveColoredSplitExponent parameter))

/-- The finite HIGH type family retains its OPEN split endpoint and CLOSED
full endpoint, together with prime targets as type `1`. -/
def scaleAdaptiveActualHighTargetTypes (parameter : ℕ) : Finset ℕ :=
  insert 1
    ((Nat.primesLE
      (2 ^ scaleAdaptiveColoredFullExponent parameter)) \
      (Nat.primesLE
        (2 ^ scaleAdaptiveColoredSplitExponent parameter)))

/-- True LOW target load profile, retaining the physical shell tail
specific to EACH genuine semiprime type. -/
noncomputable def scaleAdaptiveActualLowTypeProfile
    (parameter targetType : ℕ) : ℝ :=
  if targetType = 1 then
    scaleAdaptiveDyadicEulerShellMass
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredFullExponent parameter) / 32
  else
    scaleAdaptiveLowEligibleDyadicEulerShell
      targetType (2 ^ scaleAdaptiveColoredSplitExponent parameter)
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredFullExponent parameter) / 32

/-- True HIGH target load profile on its genuine short shell, the same for
prime targets and every actually supported high semiprime type. -/
noncomputable def scaleAdaptiveActualHighTypeProfile
    (parameter _targetType : ℕ) : ℝ :=
  scaleAdaptiveHighDyadicEulerShellMass
    (scaleAdaptiveColoredFullExponent parameter)
    (scaleAdaptiveColoredSplitExponent parameter)
    (scaleAdaptiveColoredLowerExponent parameter)
    (scaleAdaptiveColoredSplitExponent parameter) / 32

/-- Every genuine member of either target-type family is positive. -/
theorem scaleAdaptiveActualLowTargetTypes_positive
    {parameter targetType : ℕ}
    (selected : targetType ∈ scaleAdaptiveActualLowTargetTypes parameter) :
    0 < targetType := by
  rcases Finset.mem_insert.mp selected with prime_target | supported
  · omega
  · exact (Nat.mem_primesLE.mp supported).2.pos

/-- Every genuine HIGH target type, including prime-target type `1`, is
positive. -/
theorem scaleAdaptiveActualHighTargetTypes_positive
    {parameter targetType : ℕ}
    (selected : targetType ∈ scaleAdaptiveActualHighTargetTypes parameter) :
    0 < targetType := by
  rcases Finset.mem_insert.mp selected with prime_target | supported
  · omega
  · exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp supported).1).2.pos

/-- Exact LOW type-weighted missing-hit coefficient: the broad finite
type sum is precisely the already proved prime-plus-eligible-type budget. -/
theorem scaleAdaptiveActualLowTypeProfile_exponential_sum
    (parameter : ℕ) :
    (∑ targetType ∈ scaleAdaptiveActualLowTargetTypes parameter,
      ((targetType : ℝ)⁻¹) *
        Real.exp (-scaleAdaptiveActualLowTypeProfile parameter targetType)) =
      scaleAdaptiveActualLowBudgetCoefficient parameter := by
  have one_not_prime :
      1 ∉ Nat.primesLE
        (2 ^ scaleAdaptiveColoredSplitExponent parameter) := by
    intro selected
    exact Nat.not_prime_one (Nat.mem_primesLE.mp selected).2
  unfold scaleAdaptiveActualLowTargetTypes
    scaleAdaptiveActualLowBudgetCoefficient
  rw [Finset.sum_insert one_not_prime]
  norm_num only [Nat.cast_one]
  have prime_term :
      Real.exp (-scaleAdaptiveActualLowTypeProfile parameter 1) =
      Real.exp (-(1 / 32 : ℝ) *
        scaleAdaptiveDyadicEulerShellMass
          (scaleAdaptiveColoredLowerExponent parameter)
          (scaleAdaptiveColoredFullExponent parameter)) := by
    unfold scaleAdaptiveActualLowTypeProfile
    simp
    ring
  rw [one_mul, prime_term]
  congr 1
  apply Finset.sum_congr rfl
  intro targetType selected
  have not_one := (Nat.mem_primesLE.mp selected).2.ne_one
  unfold scaleAdaptiveActualLowTypeProfile
  rw [if_neg not_one]
  congr 1
  congr 1
  ring

/-- Exact HIGH prime-plus-harmonic-type exponential coefficient; the
actual prime harmonic INTERVAL keeps its open/closed endpoints. -/
theorem scaleAdaptiveActualHighTypeProfile_exponential_sum
    (parameter : ℕ) :
    (∑ targetType ∈ scaleAdaptiveActualHighTargetTypes parameter,
      ((targetType : ℝ)⁻¹) *
        Real.exp (-scaleAdaptiveActualHighTypeProfile parameter targetType)) =
      scaleAdaptiveActualHighBudgetCoefficient parameter := by
  let types :=
    (Nat.primesLE (2 ^ scaleAdaptiveColoredFullExponent parameter)) \
      (Nat.primesLE (2 ^ scaleAdaptiveColoredSplitExponent parameter))
  have one_not_selected : 1 ∉ types := by
    intro selected
    exact Nat.not_prime_one
      (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp selected).1).2
  change
    (∑ targetType ∈ insert 1 types,
      ((targetType : ℝ)⁻¹) *
        Real.exp (-scaleAdaptiveActualHighTypeProfile parameter targetType)) = _
  rw [Finset.sum_insert one_not_selected]
  unfold scaleAdaptiveActualHighBudgetCoefficient
    scaleAdaptiveActualHighTypeProfile
  dsimp [types]
  unfold adaptivePrimeHarmonicInterval
  rw [Finset.sum_mul]
  norm_num only [Nat.cast_one, inv_one, one_mul]
  congr 1
  · congr 1
    ring
  · apply Finset.sum_congr rfl
    intro targetType _selected
    congr 1
    congr 1
    ring

/-- The LOW type family stays inside the full supported prime types when
the genuine split/full exponents have their required order. -/
theorem scaleAdaptiveActualLowTargetTypes_subset_full
    {parameter : ℕ} (large : 2 ≤ parameter) :
    scaleAdaptiveActualLowTargetTypes parameter ⊆
      insert 1 (Nat.primesLE
        (2 ^ scaleAdaptiveColoredFullExponent parameter)) := by
  intro targetType selected
  rcases Finset.mem_insert.mp selected with one | supported
  · exact Finset.mem_insert.mpr (Or.inl one)
  · apply Finset.mem_insert_of_mem
    exact Nat.primesLE_mono
      (Nat.pow_le_pow_right (by norm_num)
        (scaleAdaptiveColoredExponent_order large).2) supported

/-- Every HIGH type already belongs to the full supported family. -/
theorem scaleAdaptiveActualHighTargetTypes_subset_full
    (parameter : ℕ) :
    scaleAdaptiveActualHighTargetTypes parameter ⊆
      insert 1 (Nat.primesLE
        (2 ^ scaleAdaptiveColoredFullExponent parameter)) := by
  intro targetType selected
  rcases Finset.mem_insert.mp selected with one | supported
  · exact Finset.mem_insert.mpr (Or.inl one)
  · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mp supported).1

/-- At a genuine original endpoint `Y≥2`, a prime-scale normalized upper
bound is equivalent to the ACTUAL unnormalized target-budget bound. -/
theorem scaleAdaptiveActualNormalizedBudget_implies_raw
    {length : ℕ} {budget coefficient : ℝ}
    (large : 2 ≤ length)
    (bound : budget * Real.log (length : ℝ) / (length : ℝ) ≤ coefficient) :
    budget ≤ coefficient * ((length : ℝ) / Real.log (length : ℝ)) := by
  have length_positive : (0 : ℝ) < length := by
    exact_mod_cast (by omega : 0 < length)
  have logarithm_positive : 0 < Real.log (length : ℝ) := by
    apply Real.log_pos
    exact_mod_cast large
  have multiplied := (div_le_iff₀ length_positive).mp bound
  have divided := (le_div_iff₀ logarithm_positive).mpr multiplied
  calc
    _ ≤ coefficient * (length : ℝ) / Real.log (length : ℝ) := divided
    _ = _ := by ring

/-- Ready-to-use ORIGINAL, unnormalized finite-type miss-budget transfer.
It converts genuine actual same-pool pointwise profiles and zero-density
bad target sets directly into their harmonic exponential coefficient PLUS
the complete actual supported physical-prefix envelope coefficient. -/
theorem scaleAdaptiveActualCoveredTypedMissBudget_raw_eventually_le
    (parameter : ℕ) (types : Finset ℕ)
    (targets : ℕ → Finset ℕ)
    (load : ℕ → ℕ → ℝ)
    (cutoff : ℕ → ℝ)
    (bad : ℕ → ℕ → Finset ℕ)
    (slack : ℝ)
    (type_positive : ∀ targetType ∈ types, 0 < targetType)
    (type_supported : types ⊆
      insert 1 (Nat.primesLE
        (2 ^ scaleAdaptiveColoredFullExponent parameter)))
    (covered : ∀ length : ℕ,
      targets length ⊆ types.biUnion fun targetType =>
        scaleAdaptiveGlobalTypedTargets targetType length)
    (bad_density : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ => ((bad targetType length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)))
    (nonnegative : ∀ᶠ length : ℕ in atTop,
      ∀ target : ℕ, 0 ≤ load length target)
    (good : ∀ᶠ length : ℕ in atTop,
      ∀ targetType ∈ types,
        ∀ target ∈ scaleAdaptiveGlobalTypedTargets targetType length,
          target ∉ bad targetType length →
          target ∉ scaleAdaptiveGlobalTypedTargets targetType
            (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter) →
            cutoff targetType ≤ load length target)
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ target ∈ targets length,
        Real.exp (-load length target)) ≤
      ((∑ targetType ∈ types,
        ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType)) +
       (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
          (1 + adaptivePrimeHarmonicPrefix
            (2 ^ scaleAdaptiveColoredFullExponent parameter))) + slack) *
          ((length : ℝ) / Real.log (length : ℝ)) := by
  have normalized := scaleAdaptiveActualCoveredTypedMissBudget_eventually_le
    parameter types targets load cutoff bad slack type_positive
      covered bad_density nonnegative good slack_positive
  have physical := scaleAdaptiveActualPhysicalTypeCoefficient_le_global
    parameter types type_supported
  filter_upwards [normalized, eventually_ge_atTop 2]
    with length estimate large
  apply scaleAdaptiveActualNormalizedBudget_implies_raw large
  calc
    _ ≤ (∑ targetType ∈ types,
      (((targetType *
        scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹)) +
      (∑ targetType ∈ types,
        ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType)) + slack := estimate
    _ ≤ (∑ targetType ∈ types,
        ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType)) +
      (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
        (1 + adaptivePrimeHarmonicPrefix
          (2 ^ scaleAdaptiveColoredFullExponent parameter))) + slack := by
      linarith

/-- The ACTUAL color-aware hit load of the ONE global common-prime-pool
sampler, with original low/high target-support arrays. -/
noncomputable def scaleAdaptiveActualGlobalColoredHitLoad
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (core cutoff : ℕ) (wanted : Bool) (length target : ℕ) : ℝ :=
  weightedActualPatternHitLoad
    (scaleAdaptiveGlobalJointPrimePool configuration length)
    (scaleAdaptiveGlobalJointColor configuration length)
    (scaleAdaptiveGlobalJointResidue configuration length
      (scaleAdaptiveGlobalLowTargets length core cutoff)
      (scaleAdaptiveGlobalHighTargets length core cutoff))
    wanted target

/-- Every actual same-pool global colored hit load is nonnegative; its
positive global denominator is proved from the genuine support primes. -/
theorem scaleAdaptiveActualGlobalColoredHitLoad_nonnegative
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (core cutoff : ℕ) (wanted : Bool) (length target : ℕ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    0 ≤ scaleAdaptiveActualGlobalColoredHitLoad
      configuration core cutoff wanted length target := by
  unfold scaleAdaptiveActualGlobalColoredHitLoad
  exact weightedActualPatternHitLoad_nonnegative
    (scaleAdaptiveGlobalJointOptionCount_positive
      configuration length low_primes high_primes)
    _ _ _ _ _

/-- Pure analytic final LOW transfer: once the actual same-pool,
type-dependent profiles have been independently proved, true PNT and the
exact physical-prefix envelope give the complete original-scale low miss
inequality.  Its pointwise premise will be discharged directly from GTZ. -/
theorem scaleAdaptiveActualGlobalLowMissBudget_eventually_le_of_profiles
    (parameter : ℕ)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (bad : ℕ → ℕ → Finset ℕ) (slack : ℝ)
    (large : 2 ≤ parameter)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
    (bad_density : ∀ targetType ∈ scaleAdaptiveActualLowTargetTypes parameter,
      Tendsto
        (fun length : ℕ => ((bad targetType length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)))
    (good : ∀ᶠ length : ℕ in atTop,
      ∀ targetType ∈ scaleAdaptiveActualLowTargetTypes parameter,
        ∀ target ∈ scaleAdaptiveGlobalTypedTargets targetType length,
          target ∉ bad targetType length →
          target ∉ scaleAdaptiveGlobalTypedTargets targetType
            (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter) →
            scaleAdaptiveActualLowTypeProfile parameter targetType ≤
              scaleAdaptiveActualGlobalColoredHitLoad configuration
                (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
                (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                false length target)
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ target ∈ scaleAdaptiveGlobalLowTargets length
        (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
        (2 ^ scaleAdaptiveColoredSplitExponent parameter),
        Real.exp (-scaleAdaptiveActualGlobalColoredHitLoad configuration
          (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
          (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          false length target)) ≤
        (scaleAdaptiveActualLowBudgetCoefficient parameter +
          (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
            (1 + adaptivePrimeHarmonicPrefix
              (2 ^ scaleAdaptiveColoredFullExponent parameter))) + slack) *
              ((length : ℝ) / Real.log (length : ℝ)) := by
  have core_positive : 0 < 2 ^ scaleAdaptiveColoredFullExponent parameter + 1 :=
    Nat.zero_lt_succ _
  have majorant := scaleAdaptiveActualCoveredTypedMissBudget_raw_eventually_le
    parameter (scaleAdaptiveActualLowTargetTypes parameter)
    (fun length => scaleAdaptiveGlobalLowTargets length
      (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
      (2 ^ scaleAdaptiveColoredSplitExponent parameter))
    (scaleAdaptiveActualGlobalColoredHitLoad configuration
      (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
      (2 ^ scaleAdaptiveColoredSplitExponent parameter) false)
    (scaleAdaptiveActualLowTypeProfile parameter)
    bad slack
    (fun _ selected => scaleAdaptiveActualLowTargetTypes_positive selected)
    (scaleAdaptiveActualLowTargetTypes_subset_full large)
    (fun length => scaleAdaptiveActualLowTargets_subset_typeCover core_positive)
    bad_density
    (Filter.Eventually.of_forall fun length target =>
      scaleAdaptiveActualGlobalColoredHitLoad_nonnegative
        configuration _ _ false length target low_primes high_primes)
    good slack_positive
  simpa [scaleAdaptiveActualLowTypeProfile_exponential_sum] using majorant

/-- Exact corresponding HIGH analytic transfer, preserving the genuine
upper-supported type interval and the actual same global sampler. -/
theorem scaleAdaptiveActualGlobalHighMissBudget_eventually_le_of_profiles
    (parameter : ℕ)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (bad : ℕ → ℕ → Finset ℕ) (slack : ℝ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
    (bad_density : ∀ targetType ∈ scaleAdaptiveActualHighTargetTypes parameter,
      Tendsto
        (fun length : ℕ => ((bad targetType length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)))
    (good : ∀ᶠ length : ℕ in atTop,
      ∀ targetType ∈ scaleAdaptiveActualHighTargetTypes parameter,
        ∀ target ∈ scaleAdaptiveGlobalTypedTargets targetType length,
          target ∉ bad targetType length →
          target ∉ scaleAdaptiveGlobalTypedTargets targetType
            (length / scaleAdaptiveActualPhysicalPrefixDivisor parameter) →
            scaleAdaptiveActualHighTypeProfile parameter targetType ≤
              scaleAdaptiveActualGlobalColoredHitLoad configuration
                (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
                (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                true length target)
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ target ∈ scaleAdaptiveGlobalHighTargets length
        (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
        (2 ^ scaleAdaptiveColoredSplitExponent parameter),
        Real.exp (-scaleAdaptiveActualGlobalColoredHitLoad configuration
          (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
          (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          true length target)) ≤
        (scaleAdaptiveActualHighBudgetCoefficient parameter +
          (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
            (1 + adaptivePrimeHarmonicPrefix
              (2 ^ scaleAdaptiveColoredFullExponent parameter))) + slack) *
              ((length : ℝ) / Real.log (length : ℝ)) := by
  have core_positive : 0 < 2 ^ scaleAdaptiveColoredFullExponent parameter + 1 :=
    Nat.zero_lt_succ _
  have majorant := scaleAdaptiveActualCoveredTypedMissBudget_raw_eventually_le
    parameter (scaleAdaptiveActualHighTargetTypes parameter)
    (fun length => scaleAdaptiveGlobalHighTargets length
      (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
      (2 ^ scaleAdaptiveColoredSplitExponent parameter))
    (scaleAdaptiveActualGlobalColoredHitLoad configuration
      (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
      (2 ^ scaleAdaptiveColoredSplitExponent parameter) true)
    (scaleAdaptiveActualHighTypeProfile parameter)
    bad slack
    (fun _ selected => scaleAdaptiveActualHighTargetTypes_positive selected)
    (scaleAdaptiveActualHighTargetTypes_subset_full parameter)
    (fun length => scaleAdaptiveActualHighTargets_subset_typeCover
      core_positive rfl)
    bad_density
    (Filter.Eventually.of_forall fun length target =>
      scaleAdaptiveActualGlobalColoredHitLoad_nonnegative
        configuration _ _ true length target low_primes high_primes)
    good slack_positive
  simpa [scaleAdaptiveActualHighTypeProfile_exponential_sum] using majorant

/-- COMPLETE actual LOW original-target missing-hit budget, directly from
the sole fixed-system signed Green--Tao input and the SAME global
configuration's genuine rejected-prime densities.

Every original prime target and every true low semiprime target uses one
unchanged prime pool, option denominator, color array, and residue array.
Each semiprime type retains its own eligible physical-shell tail.  The
nonzero genuine physical prefix is charged by its true full coefficient. -/
theorem scaleAdaptiveActualGlobalLowMissBudget_eventually_le_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (slack : ℝ)
    (large : 2 ≤ parameter)
    (configuration_exponents :
      configuration.exponents =
        scaleAdaptiveFinalShellFullExponents parameter)
    (configuration_low :
      configuration.lowSupport =
        scaleAdaptiveFinalShellLowSupport parameter)
    (configuration_high :
      configuration.highSupport =
        scaleAdaptiveFinalShellHighSupport parameter)
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
        atTop (nhds (0 : ℝ)))
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ target ∈ scaleAdaptiveGlobalLowTargets length
        (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
        (2 ^ scaleAdaptiveColoredSplitExponent parameter),
        Real.exp (-scaleAdaptiveActualGlobalColoredHitLoad configuration
          (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
          (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          false length target)) ≤
        (scaleAdaptiveActualLowBudgetCoefficient parameter +
          (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
            (1 + adaptivePrimeHarmonicPrefix
              (2 ^ scaleAdaptiveColoredFullExponent parameter))) + slack) *
              ((length : ℝ) / Real.log (length : ℝ)) := by
  have low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime := by
    intro exponent _ prime selected
    rw [configuration_low] at selected
    exact scaleAdaptiveFinalShellLowSupport_prime parameter exponent selected
  have high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime := by
    intro exponent _ prime selected
    rw [configuration_high] at selected
    exact scaleAdaptiveFinalShellHighSupport_prime parameter exponent selected
  have valid : ∀ targetType ∈ scaleAdaptiveActualLowTargetTypes parameter,
      targetType = 1 ∨
        targetType.Prime ∧
          targetType ≤ 2 ^ scaleAdaptiveColoredSplitExponent parameter := by
    intro targetType selected
    rcases Finset.mem_insert.mp selected with one | supported
    · exact Or.inl one
    · obtain ⟨bounded, prime⟩ := Nat.mem_primesLE.mp supported
      exact Or.inr ⟨prime, bounded⟩
  apply scaleAdaptiveActualGlobalLowMissBudget_eventually_le_of_profiles
    parameter configuration
    (fun targetType length =>
      scaleAdaptiveFinalLowTypedBadTargets
        configuration parameter targetType length)
    slack large low_primes high_primes
  · intro targetType selected
    exact scaleAdaptiveFinalLowTypedBadTargets_normalized_tendsto_zero_of_GTZ
      green_tao configuration parameter targetType
        configuration_exponents configuration_low configuration_high
        (valid targetType selected)
          lower_nonnegative band_nonempty upper_bounded rejected
  · filter_upwards [scaleAdaptiveActualPhysicalScales_eventually_large
      configuration.exponents] with length scales
    intro targetType selected target typed not_bad not_physical
    have actual := scaleAdaptiveFinalLowTypedPointwiseHit_ge_profile
      configuration parameter targetType length target
      (scaleAdaptiveGlobalLowTargets length
        (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
        (2 ^ scaleAdaptiveColoredSplitExponent parameter))
      (scaleAdaptiveGlobalHighTargets length
        (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
        (2 ^ scaleAdaptiveColoredSplitExponent parameter))
      configuration_exponents configuration_low configuration_high
        (valid targetType selected) scales typed
        (by
          simpa [scaleAdaptiveActualPhysicalPrefixDivisor]
            using not_physical)
        not_bad
    change scaleAdaptiveActualLowTypeProfile parameter targetType ≤ _
    unfold scaleAdaptiveActualLowTypeProfile
    split <;> rename_i branch
    · simpa [branch, scaleAdaptiveActualGlobalColoredHitLoad] using actual
    · simpa [branch, scaleAdaptiveActualGlobalColoredHitLoad] using actual
  · exact slack_positive

/-- COMPLETE actual HIGH original-target missing-hit budget from the SAME
sole fixed-system GTZ input and the SAME globally coherent prime sampler.
The true upper prime-type interval, exact short-shell factor, fair color
half, all target exceptions, and physical prefix are retained. -/
theorem scaleAdaptiveActualGlobalHighMissBudget_eventually_le_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (slack : ℝ)
    (large : 2 ≤ parameter)
    (configuration_exponents :
      configuration.exponents =
        scaleAdaptiveFinalShellFullExponents parameter)
    (configuration_low :
      configuration.lowSupport =
        scaleAdaptiveFinalShellLowSupport parameter)
    (configuration_high :
      configuration.highSupport =
        scaleAdaptiveFinalShellHighSupport parameter)
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
        atTop (nhds (0 : ℝ)))
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      (∑ target ∈ scaleAdaptiveGlobalHighTargets length
        (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
        (2 ^ scaleAdaptiveColoredSplitExponent parameter),
        Real.exp (-scaleAdaptiveActualGlobalColoredHitLoad configuration
          (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
          (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          true length target)) ≤
        (scaleAdaptiveActualHighBudgetCoefficient parameter +
          (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
            (1 + adaptivePrimeHarmonicPrefix
              (2 ^ scaleAdaptiveColoredFullExponent parameter))) + slack) *
              ((length : ℝ) / Real.log (length : ℝ)) := by
  have low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime := by
    intro exponent _ prime selected
    rw [configuration_low] at selected
    exact scaleAdaptiveFinalShellLowSupport_prime parameter exponent selected
  have high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime := by
    intro exponent _ prime selected
    rw [configuration_high] at selected
    exact scaleAdaptiveFinalShellHighSupport_prime parameter exponent selected
  have valid : ∀ targetType ∈ scaleAdaptiveActualHighTargetTypes parameter,
      targetType = 1 ∨
        targetType.Prime ∧
          2 ^ scaleAdaptiveColoredSplitExponent parameter < targetType ∧
          targetType ≤ 2 ^ scaleAdaptiveColoredFullExponent parameter := by
    intro targetType selected
    rcases Finset.mem_insert.mp selected with one | supported
    · exact Or.inl one
    · obtain ⟨in_full, not_low⟩ := Finset.mem_sdiff.mp supported
      obtain ⟨below_full, prime⟩ := Nat.mem_primesLE.mp in_full
      have above_low :
          2 ^ scaleAdaptiveColoredSplitExponent parameter < targetType := by
        by_contra failed
        exact not_low (Nat.mem_primesLE.mpr
          ⟨Nat.le_of_not_gt failed, prime⟩)
      exact Or.inr ⟨prime, above_low, below_full⟩
  apply scaleAdaptiveActualGlobalHighMissBudget_eventually_le_of_profiles
    parameter configuration
    (fun targetType length =>
      scaleAdaptiveFinalHighTypedBadTargets
        configuration parameter targetType length)
    slack low_primes high_primes
  · intro targetType selected
    exact scaleAdaptiveFinalHighTypedBadTargets_normalized_tendsto_zero_of_GTZ
      green_tao configuration parameter targetType large
        configuration_exponents configuration_low configuration_high
          (valid targetType selected)
          lower_nonnegative band_nonempty upper_bounded rejected
  · filter_upwards [scaleAdaptiveActualPhysicalScales_eventually_large
      configuration.exponents] with length scales
    intro targetType selected target typed not_bad not_physical
    have actual := scaleAdaptiveFinalHighTypedPointwiseHit_ge_profile
      configuration parameter targetType length target
      (scaleAdaptiveGlobalLowTargets length
        (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
        (2 ^ scaleAdaptiveColoredSplitExponent parameter))
      (scaleAdaptiveGlobalHighTargets length
        (2 ^ scaleAdaptiveColoredFullExponent parameter + 1)
        (2 ^ scaleAdaptiveColoredSplitExponent parameter))
      large configuration_exponents configuration_low configuration_high
        (valid targetType selected) scales typed
        (by
          simpa [scaleAdaptiveActualPhysicalPrefixDivisor]
            using not_physical)
        not_bad
    simpa [scaleAdaptiveActualHighTypeProfile,
      scaleAdaptiveActualGlobalColoredHitLoad] using actual
  · exact slack_positive


end Erdos1139
