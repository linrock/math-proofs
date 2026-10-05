module

public import ScaleAdaptiveMultiShellActualLoad1139
public import ScaleAdaptiveGlobalGoodLabelIntersection1139
public import AdaptiveHarmonicShellBounds1139

@[expose] public section


/-!
# Actual colored exponential budgets at the original target scale

Every target here is a genuine prime or a genuine typed semiprime `s*q`.
Its asymptotic cardinality retains the factor `1/s`, its load is the ACTUAL
multiscale inverse-integer-degree signed-pattern load, and exceptional
targets are charged at the original `Y/log Y` normalization.

Physical exponent families and target types are fixed before `Y → ∞`.
Subsequent limits in an adaptive integer parameter are separate iterated
limits; no rank-uniform Green--Tao estimate, real-to-prime inference, or
already-constructed covering is assumed.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1000000

/-- Every actual prime target through the original integer endpoint. -/
def scaleAdaptiveGlobalPrimeTargets (length : ℕ) : Finset ℕ :=
  Nat.primesLE length

/-- Every actual typed target `s*q ≤ Y`, with `q` prime and the exact
integer cutoff `⌊Y/s⌋`; multiplication is not treated as injective unless
the genuine type is positive. -/
def scaleAdaptiveGlobalTypedTargets (targetType length : ℕ) : Finset ℕ :=
  (Nat.primesLE (length / targetType)).image
    fun prime => targetType * prime

/-- Exact source-faithful membership in the original typed target family. -/
theorem mem_scaleAdaptiveGlobalTypedTargets
    {targetType length target : ℕ} (positive : 0 < targetType) :
    target ∈ scaleAdaptiveGlobalTypedTargets targetType length ↔
      ∃ prime : ℕ, prime.Prime ∧ targetType * prime ≤ length ∧
        target = targetType * prime := by
  constructor
  · intro selected
    obtain ⟨prime, bounded, same⟩ := Finset.mem_image.mp selected
    have prime_data := Nat.mem_primesLE.mp bounded
    refine ⟨prime, prime_data.2, ?_, same.symm⟩
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le positive).mp prime_data.1
  · rintro ⟨prime, prime_is_prime, bounded, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨prime, ?_, rfl⟩
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_div_iff_mul_le positive).mpr (by
        simpa [Nat.mul_comm] using bounded), prime_is_prime⟩

/-- The typed target family has EXACTLY the ordinary prime-counting
cardinality at its true type-dependent rounded cutoff. -/
theorem scaleAdaptiveGlobalTypedTargets_card
    (targetType length : ℕ) (positive : 0 < targetType) :
    (scaleAdaptiveGlobalTypedTargets targetType length).card =
      Nat.primeCounting (length / targetType) := by
  unfold scaleAdaptiveGlobalTypedTargets
  rw [Finset.card_image_iff.mpr]
  · exact Nat.primesLE_card_eq_primeCounting _
  · intro first _ second _ same
    exact Nat.eq_of_mul_eq_mul_left positive same

/-- The true ORIGINAL-scale density of typed semiprime targets is `1/s`.
This uses ordinary already-proved PNT, not a target-counting assumption. -/
theorem scaleAdaptiveGlobalTypedTargets_normalized_tendsto
    (targetType : ℕ) (positive : 0 < targetType) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalTypedTargets targetType length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds ((targetType : ℝ)⁻¹)) := by
  have counting := primeCounting_fixed_cutoff_normalized_tendsto
    targetType positive
  apply counting.congr'
  filter_upwards [eventually_ge_atTop 2] with length large
  rw [scaleAdaptiveGlobalTypedTargets_card targetType length positive]
  have length_nonzero : (length : ℝ) ≠ 0 := by
    exact_mod_cast (show length ≠ 0 by omega)
  have log_nonzero : Real.log (length : ℝ) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast large
  field_simp

/-- True prime targets have unit original-scale density. -/
theorem scaleAdaptiveGlobalPrimeTargets_normalized_tendsto_one :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalPrimeTargets length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (1 : ℝ)) := by
  have typed := scaleAdaptiveGlobalTypedTargets_normalized_tendsto
    1 (by omega)
  simpa [scaleAdaptiveGlobalPrimeTargets,
    scaleAdaptiveGlobalTypedTargets] using typed

/-- Every true actual signed unit-mass inverse-INTEGER-degree target load
is nonnegative, even when an outcome has no usable prime labels. -/
theorem scaleAdaptiveBandActualInverseTargetLoad_nonnegative
    (support : Finset ℕ) (scale : ℕ) (lower upper : ℝ)
    (index : ℕ) (outcome : ℕ × ℕ) (N target : ℕ) :
    0 ≤ scaleAdaptiveBandActualInverseTargetLoad
      support scale lower upper index outcome N target := by
  unfold scaleAdaptiveBandActualInverseTargetLoad
    scaleAdaptiveSignedUnitActualTargetLoad
    scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
  apply Finset.sum_nonneg
  intro label _selected
  exact div_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- The aggregated ACTUAL prime-target mixed-pattern load is nonnegative. -/
theorem scaleAdaptiveMultiShellPrimeActualLoad_nonnegative
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper : ℝ) (length target : ℕ) :
    0 ≤ scaleAdaptiveMultiShellPrimeActualLoad
      exponents support lower upper length target := by
  unfold scaleAdaptiveMultiShellPrimeActualLoad
    scaleAdaptiveBandPrimeOutcomeLoad
  apply Finset.sum_nonneg
  intro exponent _selected
  apply Finset.sum_nonneg
  intro index _selected
  apply Finset.sum_nonneg
  intro outcome _selected
  exact div_nonneg
    (scaleAdaptiveBandActualInverseTargetLoad_nonnegative
      (support exponent) (2 ^ exponent) lower upper index outcome
        (length / 2 ^ exponent) target)
    (Nat.cast_nonneg _)

/-- The aggregated ACTUAL typed semiprime mixed-pattern load is nonnegative. -/
theorem scaleAdaptiveMultiShellSemiprimeActualLoad_nonnegative
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ) (length target : ℕ) :
    0 ≤ scaleAdaptiveMultiShellSemiprimeActualLoad
      exponents support targetType lower upper length target := by
  unfold scaleAdaptiveMultiShellSemiprimeActualLoad
    scaleAdaptiveBandSemiprimeOutcomeLoad
  apply Finset.sum_nonneg
  intro exponent _selected
  apply Finset.sum_nonneg
  intro index _selected
  apply Finset.sum_nonneg
  intro outcome _selected
  exact div_nonneg
    (scaleAdaptiveBandActualInverseTargetLoad_nonnegative
      (support exponent) (2 ^ exponent) lower upper index outcome
        (length / 2 ^ exponent) target)
    (Nat.cast_nonneg _)

/-- Exact finite missing-hit bookkeeping for any ACTUAL nonnegative target
load: bad targets cost one each, while good targets have their true
pointwise exponential upper bound.  The bad set need not be a subset of the
target family; only its actual intersection is charged. -/
theorem scaleAdaptiveGlobalExponentialBudget_le_exceptions
    (targets exceptions : Finset ℕ) (load : ℕ → ℝ) (cutoff : ℝ)
    (nonnegative : ∀ target ∈ targets, 0 ≤ load target)
    (good : ∀ target ∈ targets, target ∉ exceptions → cutoff ≤ load target) :
    (∑ target ∈ targets, Real.exp (-load target)) ≤
      (((targets.filter fun target => target ∈ exceptions).card : ℕ) : ℝ) +
        (targets.card : ℝ) * Real.exp (-cutoff) := by
  classical
  have pointwise : ∀ target ∈ targets,
      Real.exp (-load target) ≤
        (if target ∈ exceptions then (1 : ℝ) else 0) +
          Real.exp (-cutoff) := by
    intro target selected
    by_cases exceptional : target ∈ exceptions
    · simp only [exceptional, ↓reduceIte]
      have bounded : Real.exp (-load target) ≤ 1 :=
        (Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (nonnegative target selected))
      linarith [Real.exp_pos (-cutoff)]
    · simp only [exceptional, ↓reduceIte, zero_add]
      exact Real.exp_le_exp.mpr
        (neg_le_neg (good target selected exceptional))
  calc
    _ ≤ ∑ target ∈ targets,
        ((if target ∈ exceptions then (1 : ℝ) else 0) +
          Real.exp (-cutoff)) :=
      Finset.sum_le_sum pointwise
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp
      congr 1

/-- The preceding true finite bound with the full external exception
cardinality, suitable for honest deterministic cleanup. -/
theorem scaleAdaptiveGlobalExponentialBudget_le_exception_card
    (targets exceptions : Finset ℕ) (load : ℕ → ℝ) (cutoff : ℝ)
    (nonnegative : ∀ target ∈ targets, 0 ≤ load target)
    (good : ∀ target ∈ targets, target ∉ exceptions → cutoff ≤ load target) :
    (∑ target ∈ targets, Real.exp (-load target)) ≤
      (exceptions.card : ℝ) +
        (targets.card : ℝ) * Real.exp (-cutoff) := by
  refine (scaleAdaptiveGlobalExponentialBudget_le_exceptions
    targets exceptions load cutoff nonnegative good).trans ?_
  apply add_le_add
  · exact_mod_cast Finset.card_le_card (by
      intro target selected
      exact (Finset.mem_filter.mp selected).2)
  · exact le_refl _

/-- Exact fixed-family PNT limit for TYPE-DEPENDENT exponential cutoffs.
The harmonic coefficient `1/s` stays INSIDE the finite type sum, so a low
type's genuine eligible-shell tail is never replaced by a global minimum. -/
theorem scaleAdaptiveGlobalTypedExponentialMajorant_normalized_tendsto
    (types : Finset ℕ) (cutoff : ℕ → ℝ)
    (positive : ∀ targetType ∈ types, 0 < targetType) :
    Tendsto
      (fun length : ℕ =>
        (∑ targetType ∈ types,
          ((scaleAdaptiveGlobalTypedTargets targetType length).card : ℝ) *
            Real.exp (-cutoff targetType)) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds
        (∑ targetType ∈ types,
          ((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType))) := by
  have each : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ =>
          (((scaleAdaptiveGlobalTypedTargets targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ)) *
              Real.exp (-cutoff targetType))
        atTop (nhds
          (((targetType : ℝ)⁻¹) * Real.exp (-cutoff targetType))) := by
    intro targetType selected
    exact (scaleAdaptiveGlobalTypedTargets_normalized_tendsto
      targetType (positive targetType selected)).mul_const _
  have summed := tendsto_finsetSum types each
  apply summed.congr'
  exact Filter.Eventually.of_forall fun length => by
    dsimp
    rw [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro targetType _selected
    ring

/-- A finite family of actual TYPE-DEPENDENT zero-density exception sets
still costs `o(Y/log Y)` at the ORIGINAL target scale. -/
theorem scaleAdaptiveGlobalTypedExceptionUnion_normalized_tendsto_zero
    (types : Finset ℕ) (exceptions : ℕ → ℕ → Finset ℕ)
    (negligible : ∀ targetType ∈ types,
      Tendsto
        (fun length : ℕ =>
          ((exceptions targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((types.biUnion fun targetType =>
          exceptions targetType length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  exact scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
    types exceptions negligible

/-- Actual targets lying beyond the genuine low physical endpoint of EVERY
chosen shell.  The complement is an explicit original-prefix cleanup set;
interior validity is not inferred from a real normalized picture. -/
def scaleAdaptiveGlobalInteriorTargets
    (targets exponents : Finset ℕ) (length : ℕ) : Finset ℕ :=
  targets.filter fun target =>
    ∀ exponent ∈ exponents, 4 * (length / 2 ^ exponent) ≤ target

/-- The actual common-color prime-target exponential budget.  Its cutoff is
the exact sum of genuine shell Euler factors divided by eight, multiplied
by the ACTUAL color rate; true GTZ target exceptions are charged explicitly.
The prime family can subsequently be restricted to the historical large
prime targets without increasing the budget. -/
theorem scaleAdaptiveGlobalPrimeActualExponentialBudget_le
    (exponents : Finset ℕ) (support : ℕ → Finset ℕ)
    (lower upper rate : ℝ) (length : ℕ)
    (rate_nonnegative : 0 ≤ rate)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent) :
    (∑ target ∈ scaleAdaptiveGlobalInteriorTargets
      (scaleAdaptiveGlobalPrimeTargets length) exponents length,
        Real.exp (-(rate * scaleAdaptiveMultiShellPrimeActualLoad
          exponents support lower upper length target))) ≤
      ((scaleAdaptiveMultiShellPrimeExceptions
        exponents support lower upper length).card : ℝ) +
        ((scaleAdaptiveGlobalPrimeTargets length).card : ℝ) *
          Real.exp (-(rate *
            ((∑ exponent ∈ exponents,
              adaptivePatternEulerFactor (support exponent)
                (2 ^ exponent)) / 8))) := by
  let targets := scaleAdaptiveGlobalInteriorTargets
    (scaleAdaptiveGlobalPrimeTargets length) exponents length
  let exceptions := scaleAdaptiveMultiShellPrimeExceptions
    exponents support lower upper length
  have finite := scaleAdaptiveGlobalExponentialBudget_le_exception_card
    targets exceptions
    (fun target => rate * scaleAdaptiveMultiShellPrimeActualLoad
      exponents support lower upper length target)
    (rate * ((∑ exponent ∈ exponents,
      adaptivePatternEulerFactor (support exponent)
        (2 ^ exponent)) / 8))
    (by
      intro target _selected
      exact mul_nonneg rate_nonnegative
        (scaleAdaptiveMultiShellPrimeActualLoad_nonnegative
          exponents support lower upper length target))
    (by
      intro target selected good
      obtain ⟨prime_selected, interior⟩ := Finset.mem_filter.mp selected
      have prime_data := Nat.mem_primesLE.mp prime_selected
      exact mul_le_mul_of_nonneg_left
        (scaleAdaptiveMultiShellPrimeActualLoad_ge_euler_sum_of_good_target
          exponents support lower upper length target primes
          prime_data.2 prime_data.1 scales_large interior good)
        rate_nonnegative)
  refine finite.trans ?_
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- The actual typed-semiprime exponential budget keeps the genuinely
eligible shell family for THIS type, the true signed `μ/d` target load, and
the exact `π(⌊Y/s⌋)` target cardinality. -/
theorem scaleAdaptiveGlobalTypedActualExponentialBudget_le
    (targetType : ℕ) (exponents : Finset ℕ)
    (support : ℕ → Finset ℕ) (lower upper rate : ℝ) (length : ℕ)
    (type_positive : 0 < targetType)
    (rate_nonnegative : 0 ≤ rate)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ support exponent, prime.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ support exponent)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent) :
    (∑ target ∈ scaleAdaptiveGlobalInteriorTargets
      (scaleAdaptiveGlobalTypedTargets targetType length)
        exponents length,
        Real.exp (-(rate * scaleAdaptiveMultiShellSemiprimeActualLoad
          exponents support targetType lower upper length target))) ≤
      ((scaleAdaptiveMultiShellSemiprimeExceptions
        exponents support targetType lower upper length).card : ℝ) +
        (Nat.primeCounting (length / targetType) : ℝ) *
          Real.exp (-(rate *
            ((∑ exponent ∈ exponents,
              adaptivePatternEulerFactor (support exponent)
                (2 ^ exponent)) / 8))) := by
  let targets := scaleAdaptiveGlobalInteriorTargets
    (scaleAdaptiveGlobalTypedTargets targetType length)
      exponents length
  let exceptions := scaleAdaptiveMultiShellSemiprimeExceptions
    exponents support targetType lower upper length
  have finite := scaleAdaptiveGlobalExponentialBudget_le_exception_card
    targets exceptions
    (fun target => rate * scaleAdaptiveMultiShellSemiprimeActualLoad
      exponents support targetType lower upper length target)
    (rate * ((∑ exponent ∈ exponents,
      adaptivePatternEulerFactor (support exponent)
        (2 ^ exponent)) / 8))
    (by
      intro target _selected
      exact mul_nonneg rate_nonnegative
        (scaleAdaptiveMultiShellSemiprimeActualLoad_nonnegative
          exponents support targetType lower upper length target))
    (by
      intro target selected good
      obtain ⟨typed, interior⟩ := Finset.mem_filter.mp selected
      obtain ⟨prime, prime_is_prime, bounded, equal⟩ :=
        (mem_scaleAdaptiveGlobalTypedTargets type_positive).mp typed
      subst target
      exact mul_le_mul_of_nonneg_left
        (scaleAdaptiveMultiShellSemiprimeActualLoad_ge_euler_sum_of_good_target
          exponents support targetType lower upper length prime primes
          type_supported prime_is_prime type_positive bounded scales_large
            interior good)
        rate_nonnegative)
  refine finite.trans ?_
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [← scaleAdaptiveGlobalTypedTargets_card
    targetType length type_positive]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- The EXACT eligible physical exponent tail of a low semiprime type.
The type is absent from every shorter shell; no full-window lower bound
is attributed to an ineligible target. -/
def scaleAdaptiveGlobalLowEligibleExponents
    (targetType lowerExponent upperExponent : ℕ) : Finset ℕ :=
  (Finset.Ioc lowerExponent upperExponent).filter
    fun exponent => targetType ≤ 2 ^ exponent

/-- The true finite eligible-tail pattern Euler sum is exactly the existing
colored low semiprime Euler shell; BOTH the target's prime condition and
the family cutoff are required. -/
theorem scaleAdaptiveGlobalLowEligibleEulerSum_eq
    (targetType lowerExponent upperExponent familyCutoff : ℕ)
    (type_prime : targetType.Prime)
    (type_cutoff : targetType ≤ familyCutoff) :
    (∑ exponent ∈ scaleAdaptiveGlobalLowEligibleExponents
      targetType lowerExponent upperExponent,
        adaptivePatternEulerFactor
          (adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
          (2 ^ exponent)) =
      scaleAdaptiveLowEligibleDyadicEulerShell
        targetType familyCutoff lowerExponent upperExponent := by
  unfold scaleAdaptiveGlobalLowEligibleExponents
    scaleAdaptiveLowEligibleDyadicEulerShell
  congr 1
  ext exponent
  simp [scaleAdaptiveDyadicLowType_mem_iff, type_prime, type_cutoff]

/-- Every ACTUAL low type receives its own eligible-tail exponential
budget, with the exact prime-counting factor `π(⌊Y/s⌋)` and the exact
target-dependent shell mass. -/
theorem scaleAdaptiveGlobalLowTypedActualExponentialBudget_le
    (targetType lowerExponent upperExponent familyCutoff : ℕ)
    (lower upper rate : ℝ) (length : ℕ)
    (type_prime : targetType.Prime)
    (type_cutoff : targetType ≤ familyCutoff)
    (rate_nonnegative : 0 ≤ rate)
    (scales_large : ∀ exponent ∈ scaleAdaptiveGlobalLowEligibleExponents
      targetType lowerExponent upperExponent,
        2 ^ exponent ≤ length / 2 ^ exponent) :
    let exponents := scaleAdaptiveGlobalLowEligibleExponents
      targetType lowerExponent upperExponent
    let support : ℕ → Finset ℕ := fun exponent =>
      adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff
    (∑ target ∈ scaleAdaptiveGlobalInteriorTargets
      (scaleAdaptiveGlobalTypedTargets targetType length)
        exponents length,
        Real.exp (-(rate * scaleAdaptiveMultiShellSemiprimeActualLoad
          exponents support targetType lower upper length target))) ≤
      ((scaleAdaptiveMultiShellSemiprimeExceptions
        exponents support targetType lower upper length).card : ℝ) +
        (Nat.primeCounting (length / targetType) : ℝ) *
          Real.exp (-(rate *
            (scaleAdaptiveLowEligibleDyadicEulerShell
              targetType familyCutoff lowerExponent upperExponent / 8))) := by
  dsimp only
  rw [← scaleAdaptiveGlobalLowEligibleEulerSum_eq
    targetType lowerExponent upperExponent familyCutoff
      type_prime type_cutoff]
  apply scaleAdaptiveGlobalTypedActualExponentialBudget_le
    targetType
    (scaleAdaptiveGlobalLowEligibleExponents
      targetType lowerExponent upperExponent)
    (fun exponent => adaptiveLowPrimeSupport
      (2 ^ exponent) familyCutoff)
    lower upper rate length type_prime.pos rate_nonnegative
  · intro exponent _selected prime in_support
    exact (mem_adaptiveLowPrimeSupport.mp in_support).1
  · intro exponent selected
    have eligible := (Finset.mem_filter.mp selected).2
    exact mem_adaptiveLowPrimeSupport.mpr
      ⟨type_prime, eligible, type_cutoff⟩
  · exact scales_large

/-- All genuine low-type eligible-tail target exceptions for a FIXED
finite type family remain `o(Y/log Y)`, even though every type has a
different actual physical exponent tail and square-core support. -/
theorem scaleAdaptiveGlobalLowTypedExceptionUnion_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (types : Finset ℕ) (lowerExponent upperExponent familyCutoff : ℕ)
    (lower upper : ℝ)
    (type_primes : ∀ targetType ∈ types, targetType.Prime)
    (type_cutoffs : ∀ targetType ∈ types, targetType ≤ familyCutoff)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    Tendsto
      (fun length : ℕ =>
        ((types.biUnion fun targetType =>
          scaleAdaptiveMultiShellSemiprimeExceptions
            (scaleAdaptiveGlobalLowEligibleExponents
              targetType lowerExponent upperExponent)
            (fun exponent =>
              adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
            targetType lower upper length).card : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  apply scaleAdaptiveGlobalTypedExceptionUnion_normalized_tendsto_zero
  intro targetType selected
  apply scaleAdaptiveMultiShellSemiprimeExceptions_global_tendsto_zero_of_GTZ
    green_tao
    (scaleAdaptiveGlobalLowEligibleExponents
      targetType lowerExponent upperExponent)
    (fun exponent => adaptiveLowPrimeSupport
      (2 ^ exponent) familyCutoff)
    targetType lower upper
  · intro exponent _selected prime in_support
    exact (mem_adaptiveLowPrimeSupport.mp in_support).1
  · intro exponent eligible
    exact mem_adaptiveLowPrimeSupport.mpr
      ⟨type_primes targetType selected,
        (Finset.mem_filter.mp eligible).2,
        type_cutoffs targetType selected⟩
  · exact lower_nonnegative
  · exact band_nonempty
  · exact upper_bounded

/-- Exact actual harmonic type mass of the HIGH colored support. -/
theorem scaleAdaptiveGlobalHighTypeHarmonicMass_eq
    (fullCutoff splitCutoff : ℕ) :
    (∑ targetType ∈ adaptiveHighPrimeSupport fullCutoff splitCutoff,
      ((targetType : ℝ)⁻¹)) =
      adaptivePrimeHarmonicInterval splitCutoff fullCutoff := by
  rfl

/-- The exact log-log width of an integer dyadic type interval is the
ordinary logarithm of its positive EXPONENT ratio.  Both actual integer
prime cutoffs remain powers of two. -/
theorem scaleAdaptiveGlobalDyadicLogLogWidth
    (lowerExponent upperExponent : ℕ)
    (lower_positive : 0 < lowerExponent)
    (upper_positive : 0 < upperExponent) :
    Real.log (Real.log ((2 ^ upperExponent : ℕ) : ℝ)) -
      Real.log (Real.log ((2 ^ lowerExponent : ℕ) : ℝ)) =
        Real.log ((upperExponent : ℝ) / (lowerExponent : ℝ)) := by
  have lower_nonzero : (lowerExponent : ℝ) ≠ 0 := by
    exact_mod_cast lower_positive.ne'
  have upper_nonzero : (upperExponent : ℝ) ≠ 0 := by
    exact_mod_cast upper_positive.ne'
  have logarithm_nonzero : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow, Real.log_pow,
    Real.log_mul upper_nonzero logarithm_nonzero,
    Real.log_mul lower_nonzero logarithm_nonzero,
    Real.log_div upper_nonzero lower_nonzero]
  ring

/-- The explicit actual HIGH type harmonic mass grows by at most
`log n + O(1)`.  The true strict support endpoints and the quantitative
two-endpoint Mertens error are both retained. -/
theorem scaleAdaptiveGlobalHighTypeHarmonicMass_le_log_add_constant
    {n : ℕ} (positive : 0 < n) :
    adaptivePrimeHarmonicInterval
      (2 ^ scaleAdaptiveColoredSplitExponent n)
      (2 ^ scaleAdaptiveColoredFullExponent n) ≤
        Real.log (n : ℝ) +
          2 * adaptiveMertensHarmonicErrorConstant /
            Real.log (2 : ℝ) := by
  let split := scaleAdaptiveColoredSplitExponent n
  let full := scaleAdaptiveColoredFullExponent n
  have split_positive : 0 < split := by
    dsimp [split, scaleAdaptiveColoredSplitExponent]
    positivity
  have full_positive : 0 < full := by
    dsimp [full, scaleAdaptiveColoredFullExponent]
    exact Nat.mul_pos positive split_positive
  have exponent_order : split ≤ full := by
    dsimp [full, scaleAdaptiveColoredFullExponent]
    nlinarith [Nat.zero_le split]
  have lower_large : 2 ≤ 2 ^ split := by
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ split := Nat.pow_le_pow_right (by norm_num)
        (by omega : 1 ≤ split)
  have ordered : 2 ^ split ≤ 2 ^ full :=
    Nat.pow_le_pow_right (by omega) exponent_order
  have error := adaptivePrimeHarmonicInterval_error_abs_le
    lower_large ordered
  have log_order : Real.log (2 : ℝ) ≤
      Real.log ((2 ^ split : ℕ) : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast lower_large
  have log_two_positive := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have remainder_bound :
      2 * adaptiveMertensHarmonicErrorConstant /
          Real.log ((2 ^ split : ℕ) : ℝ) ≤
        2 * adaptiveMertensHarmonicErrorConstant /
          Real.log (2 : ℝ) :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num)
        adaptiveMertensHarmonicErrorConstant_nonnegative)
      log_two_positive log_order
  have ratio : (full : ℝ) / (split : ℝ) = (n : ℝ) := by
    have split_nonzero : (split : ℝ) ≠ 0 := by
      exact_mod_cast split_positive.ne'
    dsimp [split] at split_nonzero
    dsimp [full, split, scaleAdaptiveColoredFullExponent]
    push_cast
    simp [split_nonzero]
  have width := scaleAdaptiveGlobalDyadicLogLogWidth
    split full split_positive full_positive
  rw [ratio] at width
  have signed := (le_abs_self _).trans error
  dsimp [split, full] at signed remainder_bound width ⊢
  linarith

/-- The true HIGH-type harmonic mass, multiplied by its ACTUAL colored
missing-hit exponential, tends to zero.  This is a genuine sum over prime
semiprime types, not the earlier illustrative `log n + 1` proxy. -/
theorem scaleAdaptiveGlobalHighTypeExponentialBudget_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun n : ℕ =>
        adaptivePrimeHarmonicInterval
          (2 ^ scaleAdaptiveColoredSplitExponent n)
          (2 ^ scaleAdaptiveColoredFullExponent n) *
            Real.exp (-rate *
              scaleAdaptiveHighDyadicEulerShellMass
                (scaleAdaptiveColoredFullExponent n)
                (scaleAdaptiveColoredSplitExponent n)
                (scaleAdaptiveColoredLowerExponent n)
                (scaleAdaptiveColoredSplitExponent n)))
      atTop (nhds (0 : ℝ)) := by
  let constant : ℝ :=
    max 1 (2 * adaptiveMertensHarmonicErrorConstant /
      Real.log (2 : ℝ))
  have constant_nonnegative : 0 ≤ constant := by
    dsimp [constant]
    exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have majorant : Tendsto
      (fun n : ℕ =>
        constant * ((Real.log (n : ℝ) + 1) *
          Real.exp (-rate *
            scaleAdaptiveHighDyadicEulerShellMass
              (scaleAdaptiveColoredFullExponent n)
              (scaleAdaptiveColoredSplitExponent n)
              (scaleAdaptiveColoredLowerExponent n)
              (scaleAdaptiveColoredSplitExponent n))))
      atTop (nhds (0 : ℝ)) := by
    simpa using
      (scaleAdaptiveColoredHighHarmonicBudget_tendsto_zero
        positive).const_mul constant
  apply squeeze_zero' _ _ majorant
  · exact Filter.Eventually.of_forall fun n =>
      mul_nonneg
        (adaptivePrimeHarmonicInterval_nonnegative _ _)
        (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop 1] with n large
    have log_nonnegative : 0 ≤ Real.log (n : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast large
    have harmonic := scaleAdaptiveGlobalHighTypeHarmonicMass_le_log_add_constant
      (show 0 < n by omega)
    have one_le : (1 : ℝ) ≤ constant := le_max_left _ _
    have error_le :
        2 * adaptiveMertensHarmonicErrorConstant /
          Real.log (2 : ℝ) ≤ constant := le_max_right _ _
    have mass_bound :
        adaptivePrimeHarmonicInterval
          (2 ^ scaleAdaptiveColoredSplitExponent n)
          (2 ^ scaleAdaptiveColoredFullExponent n) ≤
            constant * (Real.log (n : ℝ) + 1) := by
      calc
        _ ≤ Real.log (n : ℝ) +
          2 * adaptiveMertensHarmonicErrorConstant /
            Real.log (2 : ℝ) := harmonic
        _ ≤ constant * Real.log (n : ℝ) + constant := by
          have scaled := mul_le_mul_of_nonneg_right one_le log_nonnegative
          linarith
        _ = _ := by ring
    have weighted := mul_le_mul_of_nonneg_right mass_bound
      (Real.exp_pos (-rate *
        scaleAdaptiveHighDyadicEulerShellMass
          (scaleAdaptiveColoredFullExponent n)
          (scaleAdaptiveColoredSplitExponent n)
          (scaleAdaptiveColoredLowerExponent n)
          (scaleAdaptiveColoredSplitExponent n))).le
    calc
      _ ≤ (constant * (Real.log (n : ℝ) + 1)) *
        Real.exp (-rate *
          scaleAdaptiveHighDyadicEulerShellMass
            (scaleAdaptiveColoredFullExponent n)
            (scaleAdaptiveColoredSplitExponent n)
            (scaleAdaptiveColoredLowerExponent n)
            (scaleAdaptiveColoredSplitExponent n)) := weighted
      _ = _ := by ring

/-- Exact sufficient condition for an actual target above `Y/d` to lie
beyond the lower physical endpoint of EVERY selected integer-floored shell.
All integer remainders are retained. -/
theorem scaleAdaptiveGlobalPhysicalInterior_of_prefix
    {length target divisor exponent : ℕ}
    (divisor_positive : 0 < divisor)
    (factor_bound : 4 * divisor ≤ 2 ^ exponent)
    (above_prefix : length / divisor < target) :
    4 * (length / 2 ^ exponent) ≤ target := by
  have lower : 4 * (length / 2 ^ exponent) ≤ length / divisor := by
    apply (Nat.le_div_iff_mul_le divisor_positive).mpr
    calc
      4 * (length / 2 ^ exponent) * divisor =
          (length / 2 ^ exponent) * (4 * divisor) := by ring
      _ ≤ (length / 2 ^ exponent) * (2 ^ exponent) :=
        Nat.mul_le_mul_left _ factor_bound
      _ ≤ length := Nat.div_mul_le_self length (2 ^ exponent)
  omega

/-- The actual type-`s` prime-target prefix has leading coefficient
`1/(s*d)` at the ORIGINAL endpoint; this is the exact finite cleanup
charge for deleting the low physical boundary. -/
theorem scaleAdaptiveGlobalTypedPrefix_normalized_tendsto
    (targetType divisor : ℕ)
    (type_positive : 0 < targetType)
    (divisor_positive : 0 < divisor) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalTypedTargets
          targetType (length / divisor)).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (((targetType * divisor : ℕ) : ℝ)⁻¹)) := by
  have counting := primeCounting_fixed_cutoff_normalized_tendsto
    (targetType * divisor) (Nat.mul_pos type_positive divisor_positive)
  apply counting.congr'
  filter_upwards [eventually_ge_atTop 2] with length large
  rw [scaleAdaptiveGlobalTypedTargets_card
    targetType (length / divisor) type_positive,
    Nat.div_div_eq_div_mul]
  have same : divisor * targetType = targetType * divisor := by ring
  rw [same]
  have length_nonzero : (length : ℝ) ≠ 0 := by
    exact_mod_cast (show length ≠ 0 by omega)
  have log_nonzero : Real.log (length : ℝ) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast large
  field_simp

/-- The actual low-family type shells are lower-OPEN and upper-CLOSED.
They run downward from the exact cutoff `2^(2^(n²))` in unit-size
log-log steps, preserving all integer endpoints. -/
def scaleAdaptiveGlobalLowTypeShellLower (parameter index : ℕ) : ℕ :=
  2 ^ (2 ^ (parameter ^ 2 - (index + 1)))

/-- The matching genuine upper endpoint of a low prime-type shell. -/
def scaleAdaptiveGlobalLowTypeShellUpper (parameter index : ℕ) : ℕ :=
  2 ^ (2 ^ (parameter ^ 2 - index))

/-- Every genuine low type shell begins at an integer at least two. -/
theorem scaleAdaptiveGlobalLowTypeShellLower_large
    (parameter index : ℕ) :
    2 ≤ scaleAdaptiveGlobalLowTypeShellLower parameter index := by
  unfold scaleAdaptiveGlobalLowTypeShellLower
  have exponent_positive : 0 < (2 : ℕ) ^
      (parameter ^ 2 - (index + 1)) := by positivity
  calc
    2 = 2 ^ (1 : ℕ) := by norm_num
    _ ≤ 2 ^ (2 ^ (parameter ^ 2 - (index + 1))) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The true low type shell endpoints are always ordered, including the
saturated zero-exponent edge cases beyond the finite index range. -/
theorem scaleAdaptiveGlobalLowTypeShell_order
    (parameter index : ℕ) :
    scaleAdaptiveGlobalLowTypeShellLower parameter index ≤
      scaleAdaptiveGlobalLowTypeShellUpper parameter index := by
  unfold scaleAdaptiveGlobalLowTypeShellLower
    scaleAdaptiveGlobalLowTypeShellUpper
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- Every exact integer low type shell has log-log width at most one.
This is the actual hypothesis required by the uniform two-endpoint
Mertens shell estimate. -/
theorem scaleAdaptiveGlobalLowTypeShell_loglog_width_le_one
    (parameter index : ℕ) :
    Real.log (Real.log
      (scaleAdaptiveGlobalLowTypeShellUpper parameter index : ℝ)) -
      Real.log (Real.log
        (scaleAdaptiveGlobalLowTypeShellLower parameter index : ℝ)) ≤
        1 := by
  let lowerExponent := 2 ^ (parameter ^ 2 - (index + 1))
  let upperExponent := 2 ^ (parameter ^ 2 - index)
  have lower_positive : 0 < lowerExponent := by
    dsimp [lowerExponent]
    positivity
  have upper_positive : 0 < upperExponent := by
    dsimp [upperExponent]
    positivity
  have exponent_difference :
      parameter ^ 2 - index ≤
        (parameter ^ 2 - (index + 1)) + 1 := by omega
  have comparison : upperExponent ≤ 2 * lowerExponent := by
    calc
      upperExponent ≤
          2 ^ ((parameter ^ 2 - (index + 1)) + 1) := by
        dsimp [upperExponent]
        exact Nat.pow_le_pow_right (by norm_num) exponent_difference
      _ = 2 * lowerExponent := by
        dsimp [lowerExponent]
        rw [pow_add]
        ring
  have lower_real_positive : (0 : ℝ) < lowerExponent := by
    exact_mod_cast lower_positive
  have upper_real_positive : (0 : ℝ) < upperExponent := by
    exact_mod_cast upper_positive
  have ratio_positive :
      0 < (upperExponent : ℝ) / (lowerExponent : ℝ) :=
    div_pos upper_real_positive lower_real_positive
  have ratio_le_two :
      (upperExponent : ℝ) / (lowerExponent : ℝ) ≤ 2 := by
    apply (div_le_iff₀ lower_real_positive).mpr
    exact_mod_cast comparison
  have width := scaleAdaptiveGlobalDyadicLogLogWidth
    lowerExponent upperExponent lower_positive upper_positive
  change
    Real.log (Real.log ((2 ^ upperExponent : ℕ) : ℝ)) -
      Real.log (Real.log ((2 ^ lowerExponent : ℕ) : ℝ)) ≤ 1
  rw [width]
  have estimate := Real.log_le_sub_one_of_pos ratio_positive
  linarith

/-- A real low-type shell budget retains BOTH the genuine `1/s` harmonic
weight and the ACTUAL eligible-tail Euler factor at each individual prime.
Any explicit linear-in-shell lower estimate then yields the exact finite
geometric bound; no low-type global minimum is used. -/
theorem scaleAdaptiveGlobalLowTypeShellBudget_le_geometric
    (parameter lowerExponent upperExponent familyCutoff count : ℕ)
    (rate baseline : ℝ) (rate_positive : 0 < rate)
    (tail_lower : ∀ index ∈ Finset.range count,
      ∀ targetType ∈
        (Nat.primesLE
          (scaleAdaptiveGlobalLowTypeShellUpper parameter index)) \
          (Nat.primesLE
            (scaleAdaptiveGlobalLowTypeShellLower parameter index)),
          baseline + (index : ℝ) ≤
            scaleAdaptiveLowEligibleDyadicEulerShell
              targetType familyCutoff lowerExponent upperExponent) :
    (∑ index ∈ Finset.range count,
      ∑ targetType ∈
        (Nat.primesLE
          (scaleAdaptiveGlobalLowTypeShellUpper parameter index)) \
          (Nat.primesLE
            (scaleAdaptiveGlobalLowTypeShellLower parameter index)),
        ((targetType : ℝ)⁻¹) *
          Real.exp (-rate *
            scaleAdaptiveLowEligibleDyadicEulerShell
              targetType familyCutoff lowerExponent upperExponent)) ≤
      (1 + 2 * adaptiveMertensHarmonicErrorConstant /
        Real.log (2 : ℝ)) * Real.exp (-rate * baseline) /
          (1 - Real.exp (-rate)) := by
  have finite := adaptiveActualPrimeUnitShells_weighted_bound
    (baseline := baseline)
    rate_positive
    (scaleAdaptiveGlobalLowTypeShellLower parameter)
    (scaleAdaptiveGlobalLowTypeShellUpper parameter)
    (scaleAdaptiveGlobalLowTypeShellLower_large parameter)
    (scaleAdaptiveGlobalLowTypeShell_order parameter)
    (scaleAdaptiveGlobalLowTypeShell_loglog_width_le_one parameter)
    count
  refine le_trans ?_ finite
  apply Finset.sum_le_sum
  intro index selected
  unfold adaptivePrimeHarmonicInterval
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro targetType in_shell
  apply mul_le_mul_of_nonneg_left _
    (inv_nonneg.mpr (Nat.cast_nonneg targetType))
  apply Real.exp_le_exp.mpr
  nlinarith [tail_lower index selected targetType in_shell]

/-- The genuine eligible low-type shell contains the COMPLETE Euler tail
above any physical exponent that already supports the type.  This turns
actual type eligibility into a quantitative shell-dependent load. -/
theorem scaleAdaptiveGlobalLowEligibleEulerShell_ge_tail
    (targetType familyCutoff lowerExponent midExponent upperExponent : ℕ)
    (type_prime : targetType.Prime)
    (type_cutoff : targetType ≤ familyCutoff)
    (type_eligible : targetType ≤ 2 ^ midExponent)
    (lower_order : lowerExponent ≤ midExponent)
    (_upper_order : midExponent ≤ upperExponent) :
    scaleAdaptiveDyadicEulerShellMass midExponent upperExponent ≤
      scaleAdaptiveLowEligibleDyadicEulerShell
        targetType familyCutoff lowerExponent upperExponent := by
  rw [← scaleAdaptiveGlobalLowEligibleEulerSum_eq
    targetType lowerExponent upperExponent familyCutoff
      type_prime type_cutoff]
  unfold scaleAdaptiveDyadicEulerShellMass
  have rewrite :
      (∑ exponent ∈ scaleAdaptiveGlobalLowEligibleExponents
        targetType lowerExponent upperExponent,
          adaptivePatternEulerFactor
            (adaptiveLowPrimeSupport (2 ^ exponent) familyCutoff)
            (2 ^ exponent)) =
        ∑ exponent ∈ scaleAdaptiveGlobalLowEligibleExponents
          targetType lowerExponent upperExponent,
          scaleAdaptiveDyadicEulerFactor exponent := by
    apply Finset.sum_congr rfl
    intro exponent _selected
    exact scaleAdaptiveLowDyadicPatternEulerFactor_eq
      exponent familyCutoff
  rw [rewrite]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro exponent selected
    have bounds := Finset.mem_Ioc.mp selected
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr
      ⟨lt_of_le_of_lt lower_order bounds.1, bounds.2⟩, ?_⟩
    exact type_eligible.trans
      (Nat.pow_le_pow_right (by norm_num) bounds.1.le)
  · intro exponent _selected _not_selected
    exact (scaleAdaptiveDyadicEulerFactor_pos exponent).le

/-- Exact integer factorization behind a low type shell's eligible tail:
`full = n * 2^(n²-index) * 2^index`.  Consequently its actual physical
log window is `log n + index*log 2`, not a target-uniform constant. -/
theorem scaleAdaptiveGlobalLowTypeShell_log_window
    (parameter index : ℕ)
    (parameter_positive : 0 < parameter)
    (index_bounded : index ≤ parameter ^ 2) :
    Real.log (scaleAdaptiveColoredFullExponent parameter : ℝ) -
      Real.log ((2 ^ (parameter ^ 2 - index) : ℕ) : ℝ) =
        Real.log (parameter : ℝ) +
          (index : ℝ) * Real.log (2 : ℝ) := by
  let middle := 2 ^ (parameter ^ 2 - index)
  have middle_positive : 0 < middle := by
    dsimp [middle]
    positivity
  have factorization :
      scaleAdaptiveColoredFullExponent parameter =
        parameter * middle * 2 ^ index := by
    unfold scaleAdaptiveColoredFullExponent
      scaleAdaptiveColoredSplitExponent
    dsimp [middle]
    have powers :
        (2 : ℕ) ^ (parameter ^ 2) =
          2 ^ (parameter ^ 2 - index) * 2 ^ index := by
      rw [← pow_add, Nat.sub_add_cancel index_bounded]
    rw [powers]
    ring
  have parameter_nonzero : (parameter : ℝ) ≠ 0 := by
    exact_mod_cast parameter_positive.ne'
  have middle_nonzero : (middle : ℝ) ≠ 0 := by
    exact_mod_cast middle_positive.ne'
  have power_nonzero : ((2 : ℝ) ^ index) ≠ 0 := by positivity
  rw [factorization]
  push_cast
  rw [Real.log_mul (mul_ne_zero parameter_nonzero middle_nonzero)
    power_nonzero,
    Real.log_mul parameter_nonzero middle_nonzero,
    Real.log_pow]
  dsimp [middle]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Every genuine low prime type in the `index`th exact log-log shell has
actual eligible-tail Euler load at least a FIXED positive constant times
`log n + index*log 2 - 1`.  The statement is uniform across the whole
finite type family but is proved from actual type membership and true
Mertens tails; no prime-pattern estimate is strengthened. -/
theorem scaleAdaptiveGlobalLowTypeShell_actualEuler_eventually_ge
    : ∀ᶠ parameter : ℕ in atTop,
      ∀ index ∈ Finset.range (parameter ^ 2 - parameter),
        ∀ targetType ∈
          (Nat.primesLE
            (scaleAdaptiveGlobalLowTypeShellUpper parameter index)) \
            (Nat.primesLE
              (scaleAdaptiveGlobalLowTypeShellLower parameter index)),
          (scaleAdaptiveDyadicMertensConstant / 2) *
            (Real.log (parameter : ℝ) +
              (index : ℝ) * Real.log (2 : ℝ) - 1) ≤
            scaleAdaptiveLowEligibleDyadicEulerShell
              targetType (2 ^ scaleAdaptiveColoredSplitExponent parameter)
              (scaleAdaptiveColoredLowerExponent parameter)
              (scaleAdaptiveColoredFullExponent parameter) := by
  obtain ⟨threshold, _positive, shells⟩ :=
    scaleAdaptiveDyadicEulerShellMass_ge_log_ratio
  have lower_large :=
    scaleAdaptiveColoredLowerExponent_tendsto_atTop.eventually
      (eventually_ge_atTop threshold)
  filter_upwards [eventually_ge_atTop (2 : ℕ), lower_large]
    with parameter parameter_large cutoff_large
  intro index selected targetType in_shell
  have index_range := Finset.mem_range.mp selected
  have index_bounded : index ≤ parameter ^ 2 := by omega
  let middle : ℕ := 2 ^ (parameter ^ 2 - index)
  let full := scaleAdaptiveColoredFullExponent parameter
  let lower := scaleAdaptiveColoredLowerExponent parameter
  have type_upper :=
    Nat.mem_primesLE.mp (Finset.mem_sdiff.mp in_shell).1
  have type_prime : targetType.Prime := type_upper.2
  have type_eligible : targetType ≤ 2 ^ middle := by
    exact type_upper.1
  have exponent_lower : parameter ≤ parameter ^ 2 - index := by omega
  have lower_order : lower ≤ middle := by
    dsimp [lower, scaleAdaptiveColoredLowerExponent, middle]
    exact Nat.pow_le_pow_right (by norm_num) exponent_lower
  have middle_le_split :
      middle ≤ scaleAdaptiveColoredSplitExponent parameter := by
    dsimp [middle, scaleAdaptiveColoredSplitExponent]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have split_le_full :
      scaleAdaptiveColoredSplitExponent parameter ≤ full := by
    dsimp [full, scaleAdaptiveColoredFullExponent]
    nlinarith [Nat.zero_le (scaleAdaptiveColoredSplitExponent parameter)]
  have middle_order : middle ≤ full :=
    middle_le_split.trans split_le_full
  have cutoff :
      targetType ≤ 2 ^ scaleAdaptiveColoredSplitExponent parameter :=
    type_eligible.trans
      (Nat.pow_le_pow_right (by norm_num) middle_le_split)
  have tail := scaleAdaptiveGlobalLowEligibleEulerShell_ge_tail
    targetType (2 ^ scaleAdaptiveColoredSplitExponent parameter)
    lower middle full type_prime cutoff type_eligible
      lower_order middle_order
  have analytic := shells middle full
    (cutoff_large.trans lower_order) middle_order
  have full_positive : (0 : ℝ) < full := by
    exact_mod_cast (show 0 < full by
      dsimp [full, scaleAdaptiveColoredFullExponent]
      exact Nat.mul_pos (by omega)
        (by
          unfold scaleAdaptiveColoredSplitExponent
          positivity))
  have successor_order :
      Real.log (full : ℝ) ≤ Real.log ((full + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log full_positive
    exact_mod_cast Nat.le_succ full
  have window := scaleAdaptiveGlobalLowTypeShell_log_window
    parameter index (by omega) index_bounded
  change
    Real.log (full : ℝ) - Real.log (middle : ℝ) =
      Real.log (parameter : ℝ) +
        (index : ℝ) * Real.log (2 : ℝ) at window
  have coefficient_nonnegative :
      0 ≤ scaleAdaptiveDyadicMertensConstant / 2 :=
    (div_pos scaleAdaptiveDyadicMertensConstant_pos (by norm_num)).le
  have window_bound :
      Real.log (parameter : ℝ) +
        (index : ℝ) * Real.log (2 : ℝ) - 1 ≤
      Real.log ((full + 1 : ℕ) : ℝ) -
        (1 + Real.log (middle : ℝ)) := by
    linarith
  exact (mul_le_mul_of_nonneg_left window_bound
    coefficient_nonnegative).trans (analytic.trans tail)

/-- Scaled version of the genuine low-type geometric shell bound.  The
positive scale factor is part of the TRUE eligible Euler load, while the
prime-type harmonic weight stays inside each exact shell. -/
theorem scaleAdaptiveGlobalLowTypeShellBudget_le_geometric_scaled
    (parameter lowerExponent upperExponent familyCutoff count : ℕ)
    (rate coefficient baseline : ℝ)
    (rate_positive : 0 < rate)
    (coefficient_positive : 0 < coefficient)
    (tail_lower : ∀ index ∈ Finset.range count,
      ∀ targetType ∈
        (Nat.primesLE
          (scaleAdaptiveGlobalLowTypeShellUpper parameter index)) \
          (Nat.primesLE
            (scaleAdaptiveGlobalLowTypeShellLower parameter index)),
          coefficient * (baseline + (index : ℝ)) ≤
            scaleAdaptiveLowEligibleDyadicEulerShell
              targetType familyCutoff lowerExponent upperExponent) :
    (∑ index ∈ Finset.range count,
      ∑ targetType ∈
        (Nat.primesLE
          (scaleAdaptiveGlobalLowTypeShellUpper parameter index)) \
          (Nat.primesLE
            (scaleAdaptiveGlobalLowTypeShellLower parameter index)),
        ((targetType : ℝ)⁻¹) *
          Real.exp (-rate *
            scaleAdaptiveLowEligibleDyadicEulerShell
              targetType familyCutoff lowerExponent upperExponent)) ≤
      (1 + 2 * adaptiveMertensHarmonicErrorConstant /
        Real.log (2 : ℝ)) *
          Real.exp (-(rate * coefficient) * baseline) /
            (1 - Real.exp (-(rate * coefficient))) := by
  have effective_positive : 0 < rate * coefficient :=
    mul_pos rate_positive coefficient_positive
  have finite := adaptiveActualPrimeUnitShells_weighted_bound
    (baseline := baseline) effective_positive
    (scaleAdaptiveGlobalLowTypeShellLower parameter)
    (scaleAdaptiveGlobalLowTypeShellUpper parameter)
    (scaleAdaptiveGlobalLowTypeShellLower_large parameter)
    (scaleAdaptiveGlobalLowTypeShell_order parameter)
    (scaleAdaptiveGlobalLowTypeShell_loglog_width_le_one parameter)
    count
  refine le_trans ?_ finite
  apply Finset.sum_le_sum
  intro index selected
  unfold adaptivePrimeHarmonicInterval
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro targetType in_shell
  apply mul_le_mul_of_nonneg_left _
    (inv_nonneg.mpr (Nat.cast_nonneg targetType))
  apply Real.exp_le_exp.mpr
  have actual := tail_lower index selected targetType in_shell
  nlinarith

/-- The fixed positive coefficient converting one true low log-log type
shell into its ACTUAL eligible physical Euler-tail increment. -/
noncomputable def scaleAdaptiveGlobalLowShellIncrement : ℝ :=
  (scaleAdaptiveDyadicMertensConstant / 2) * Real.log (2 : ℝ)

/-- The genuine low-shell increment is strictly positive. -/
theorem scaleAdaptiveGlobalLowShellIncrement_pos :
    0 < scaleAdaptiveGlobalLowShellIncrement := by
  unfold scaleAdaptiveGlobalLowShellIncrement
  exact mul_pos
    (div_pos scaleAdaptiveDyadicMertensConstant_pos (by norm_num))
    (Real.log_pos (by norm_num))

/-- The true baseline from the entire post-split eligible physical tail
diverges: `(log n - 1)/log 2 → ∞`. -/
theorem scaleAdaptiveGlobalLowShellBaseline_tendsto_atTop :
    Tendsto
      (fun parameter : ℕ =>
        (Real.log (parameter : ℝ) - 1) / Real.log (2 : ℝ))
      atTop atTop := by
  have logarithm := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have shifted :
      Tendsto (fun parameter : ℕ =>
        Real.log (parameter : ℝ) - 1)
      atTop atTop := by
    convert Filter.tendsto_atTop_add_const_right
      atTop (-1 : ℝ) logarithm using 1
    ext parameter
    simp
    ring
  have log_positive := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simpa [div_eq_mul_inv] using
    shifted.atTop_mul_const (inv_pos.mpr log_positive)

/-- Source-faithful DECAY of the complete low-type geometric shell sum.
Every summand is a true prime type with exact harmonic weight `1/s` and
its own ACTUAL eligible-tail Euler load.  The number of shells grows with
the adaptive parameter; no uniform target cutoff is substituted. -/
theorem scaleAdaptiveGlobalLowTypeExponentialShellBudget_tendsto_zero
    {rate : ℝ} (rate_positive : 0 < rate) :
    Tendsto
      (fun parameter : ℕ =>
        ∑ index ∈ Finset.range (parameter ^ 2 - parameter),
          ∑ targetType ∈
            (Nat.primesLE
              (scaleAdaptiveGlobalLowTypeShellUpper parameter index)) \
              (Nat.primesLE
                (scaleAdaptiveGlobalLowTypeShellLower parameter index)),
            ((targetType : ℝ)⁻¹) *
              Real.exp (-rate *
                scaleAdaptiveLowEligibleDyadicEulerShell
                  targetType
                    (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                  (scaleAdaptiveColoredLowerExponent parameter)
                  (scaleAdaptiveColoredFullExponent parameter)))
      atTop (nhds (0 : ℝ)) := by
  let increment := scaleAdaptiveGlobalLowShellIncrement
  have increment_positive : 0 < increment :=
    scaleAdaptiveGlobalLowShellIncrement_pos
  have effective_positive : 0 < rate * increment :=
    mul_pos rate_positive increment_positive
  have baseline_growth :=
    scaleAdaptiveGlobalLowShellBaseline_tendsto_atTop.const_mul_atTop
      effective_positive
  have exponential :
      Tendsto
        (fun parameter : ℕ =>
          Real.exp (-(rate * increment) *
            ((Real.log (parameter : ℝ) - 1) / Real.log (2 : ℝ))))
        atTop (nhds (0 : ℝ)) := by
    simpa [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp baseline_growth
  have majorant :
      Tendsto
        (fun parameter : ℕ =>
          (1 + 2 * adaptiveMertensHarmonicErrorConstant /
            Real.log (2 : ℝ)) *
            Real.exp (-(rate * increment) *
              ((Real.log (parameter : ℝ) - 1) /
                Real.log (2 : ℝ))) /
              (1 - Real.exp (-(rate * increment))))
        atTop (nhds (0 : ℝ)) := by
    simpa using
      (exponential.const_mul
        (1 + 2 * adaptiveMertensHarmonicErrorConstant /
          Real.log (2 : ℝ))).div_const
        (1 - Real.exp (-(rate * increment)))
  apply squeeze_zero' _ _ majorant
  · exact Filter.Eventually.of_forall fun parameter => by
      apply Finset.sum_nonneg
      intro index _selected
      apply Finset.sum_nonneg
      intro targetType _selected
      exact mul_nonneg
        (inv_nonneg.mpr (Nat.cast_nonneg targetType))
        (Real.exp_pos _).le
  · filter_upwards
      [scaleAdaptiveGlobalLowTypeShell_actualEuler_eventually_ge]
      with parameter actual
    apply scaleAdaptiveGlobalLowTypeShellBudget_le_geometric_scaled
      parameter
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredFullExponent parameter)
      (2 ^ scaleAdaptiveColoredSplitExponent parameter)
      (parameter ^ 2 - parameter)
      rate increment
      ((Real.log (parameter : ℝ) - 1) / Real.log (2 : ℝ))
      rate_positive increment_positive
    intro index selected targetType in_shell
    have lower := actual index selected targetType in_shell
    have logarithm_nonzero : Real.log (2 : ℝ) ≠ 0 :=
      (Real.log_pos (by norm_num)).ne'
    change
      ((scaleAdaptiveDyadicMertensConstant / 2) * Real.log (2 : ℝ)) *
        ((Real.log (parameter : ℝ) - 1) / Real.log (2 : ℝ) +
          (index : ℝ)) ≤ _
    convert lower using 1
    field_simp
    ring

/-- Exact set-theoretic gluing of adjacent genuine prime intervals. -/
theorem scaleAdaptiveGlobalNestedPrimeDifference_union
    (upper middle lower : ℕ)
    (lower_order : lower ≤ middle)
    (upper_order : middle ≤ upper) :
    ((Nat.primesLE upper) \ (Nat.primesLE middle)) ∪
      ((Nat.primesLE middle) \ (Nat.primesLE lower)) =
        (Nat.primesLE upper) \ (Nat.primesLE lower) := by
  ext prime
  simp only [Finset.mem_union, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro (⟨⟨bounded, prime_is_prime⟩, not_middle⟩ |
      ⟨⟨middle_bounded, prime_is_prime⟩, not_lower⟩)
    · refine ⟨⟨bounded, prime_is_prime⟩, ?_⟩
      intro selected
      exact not_middle
        ⟨selected.1.trans lower_order, selected.2⟩
    · exact ⟨⟨middle_bounded.trans upper_order,
          prime_is_prime⟩, not_lower⟩
  · rintro ⟨⟨bounded, prime_is_prime⟩, not_lower⟩
    by_cases middle_bounded : prime ≤ middle
    · exact Or.inr ⟨⟨middle_bounded, prime_is_prime⟩, not_lower⟩
    · exact Or.inl ⟨⟨bounded, prime_is_prime⟩,
        fun selected => middle_bounded selected.1⟩

/-- Telescoping exact lower-open/upper-closed prime intervals over ANY
antitone integer endpoint chain. -/
theorem scaleAdaptiveGlobalAntitonePrimeIntervals_biUnion
    (endpoint : ℕ → ℕ) (antitone : Antitone endpoint)
    (count : ℕ) :
    (Finset.range count).biUnion
      (fun index =>
        (Nat.primesLE (endpoint index)) \
          (Nat.primesLE (endpoint (index + 1)))) =
      (Nat.primesLE (endpoint 0)) \
        (Nat.primesLE (endpoint count)) := by
  induction count with
  | zero => simp
  | succ count induction =>
      rw [Finset.range_add_one, Finset.biUnion_insert, induction]
      rw [Finset.union_comm]
      exact scaleAdaptiveGlobalNestedPrimeDifference_union
        (endpoint 0) (endpoint count) (endpoint (count + 1))
        (antitone (Nat.le_succ count))
        (antitone (Nat.zero_le count))

/-- The exact descending integer endpoint chain used by the actual low
semiprime type partition. -/
def scaleAdaptiveGlobalLowTypeShellEndpoint
    (parameter index : ℕ) : ℕ :=
  2 ^ (2 ^ (parameter ^ 2 - index))

/-- The genuine low-type integer endpoint chain is antitone. -/
theorem scaleAdaptiveGlobalLowTypeShellEndpoint_antitone
    (parameter : ℕ) :
    Antitone (scaleAdaptiveGlobalLowTypeShellEndpoint parameter) := by
  intro first second ordered
  unfold scaleAdaptiveGlobalLowTypeShellEndpoint
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- The exact finite actual type-shell union is PRECISELY the entire
low-prime support between the tiny early-eligibility cutoff and the split
cutoff.  No supported semiprime type disappears between shells. -/
theorem scaleAdaptiveGlobalLowTypeShells_biUnion
    {parameter : ℕ} (positive : 0 < parameter) :
    (Finset.range (parameter ^ 2 - parameter)).biUnion
      (fun index =>
        (Nat.primesLE
          (scaleAdaptiveGlobalLowTypeShellUpper parameter index)) \
          (Nat.primesLE
            (scaleAdaptiveGlobalLowTypeShellLower parameter index))) =
      (Nat.primesLE (2 ^ scaleAdaptiveColoredSplitExponent parameter)) \
        (Nat.primesLE (2 ^ scaleAdaptiveColoredLowerExponent parameter)) := by
  have partition := scaleAdaptiveGlobalAntitonePrimeIntervals_biUnion
    (scaleAdaptiveGlobalLowTypeShellEndpoint parameter)
    (scaleAdaptiveGlobalLowTypeShellEndpoint_antitone parameter)
    (parameter ^ 2 - parameter)
  have square_order : parameter ≤ parameter ^ 2 := by
    nlinarith [show 1 ≤ parameter by omega]
  have endpoint : parameter ^ 2 - (parameter ^ 2 - parameter) =
      parameter := by omega
  simpa [scaleAdaptiveGlobalLowTypeShellEndpoint,
    scaleAdaptiveGlobalLowTypeShellUpper,
    scaleAdaptiveGlobalLowTypeShellLower,
    scaleAdaptiveColoredSplitExponent,
    scaleAdaptiveColoredLowerExponent,
    endpoint] using partition

/-- Distinct adjacent intervals from an antitone endpoint chain are
genuinely disjoint; each real prime type is counted exactly once. -/
theorem scaleAdaptiveGlobalAntitonePrimeIntervals_pairwiseDisjoint
    (endpoint : ℕ → ℕ) (antitone : Antitone endpoint)
    (count : ℕ) :
    Set.Pairwise (↑(Finset.range count) : Set ℕ)
      (fun first second =>
        Disjoint
          ((Nat.primesLE (endpoint first)) \
            (Nat.primesLE (endpoint (first + 1))))
          ((Nat.primesLE (endpoint second)) \
            (Nat.primesLE (endpoint (second + 1))))) := by
  intro first _first_selected second _second_selected distinct
  classical
  rcases lt_or_gt_of_ne distinct with ordered | ordered
  · apply Finset.disjoint_left.mpr
    intro prime in_first in_second
    obtain ⟨_first_upper, not_first_lower⟩ :=
      Finset.mem_sdiff.mp in_first
    obtain ⟨second_upper, _not_second_lower⟩ :=
      Finset.mem_sdiff.mp in_second
    apply not_first_lower
    apply Nat.mem_primesLE.mpr
    have upper := Nat.mem_primesLE.mp second_upper
    exact ⟨upper.1.trans
      (antitone (show first + 1 ≤ second by omega)), upper.2⟩
  · apply Disjoint.symm
    apply Finset.disjoint_left.mpr
    intro prime in_second in_first
    obtain ⟨_second_upper, not_second_lower⟩ :=
      Finset.mem_sdiff.mp in_second
    obtain ⟨first_upper, _not_first_lower⟩ :=
      Finset.mem_sdiff.mp in_first
    apply not_second_lower
    apply Nat.mem_primesLE.mpr
    have upper := Nat.mem_primesLE.mp first_upper
    exact ⟨upper.1.trans
      (antitone (show second + 1 ≤ first by omega)), upper.2⟩

/-- The true entire LATE low-semiprime support has vanishing harmonic
missing-hit budget.  It is EXACTLY the disjoint union of the growing
actual type-shell family, not an illustrative surrogate sum. -/
theorem scaleAdaptiveGlobalLateLowTypeExponentialBudget_tendsto_zero
    {rate : ℝ} (rate_positive : 0 < rate) :
    Tendsto
      (fun parameter : ℕ =>
        ∑ targetType ∈
          (Nat.primesLE
            (2 ^ scaleAdaptiveColoredSplitExponent parameter)) \
            (Nat.primesLE
              (2 ^ scaleAdaptiveColoredLowerExponent parameter)),
          ((targetType : ℝ)⁻¹) *
            Real.exp (-rate *
              scaleAdaptiveLowEligibleDyadicEulerShell
                targetType
                  (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                (scaleAdaptiveColoredLowerExponent parameter)
                (scaleAdaptiveColoredFullExponent parameter)))
      atTop (nhds (0 : ℝ)) := by
  have shell :=
    scaleAdaptiveGlobalLowTypeExponentialShellBudget_tendsto_zero
      rate_positive
  apply shell.congr'
  filter_upwards [eventually_ge_atTop 1] with parameter positive
  have partition := scaleAdaptiveGlobalLowTypeShells_biUnion
    (show 0 < parameter by omega)
  have disjoint := scaleAdaptiveGlobalAntitonePrimeIntervals_pairwiseDisjoint
    (scaleAdaptiveGlobalLowTypeShellEndpoint parameter)
    (scaleAdaptiveGlobalLowTypeShellEndpoint_antitone parameter)
    (parameter ^ 2 - parameter)
  have actual_disjoint :
      Set.Pairwise
        (↑(Finset.range (parameter ^ 2 - parameter)) : Set ℕ)
        (fun first second =>
          Disjoint
            ((Nat.primesLE
              (scaleAdaptiveGlobalLowTypeShellUpper parameter first)) \
              (Nat.primesLE
                (scaleAdaptiveGlobalLowTypeShellLower parameter first)))
            ((Nat.primesLE
              (scaleAdaptiveGlobalLowTypeShellUpper parameter second)) \
              (Nat.primesLE
                (scaleAdaptiveGlobalLowTypeShellLower parameter second)))) := by
    simpa [scaleAdaptiveGlobalLowTypeShellEndpoint,
      scaleAdaptiveGlobalLowTypeShellUpper,
      scaleAdaptiveGlobalLowTypeShellLower] using disjoint
  rw [← partition]
  rw [Finset.sum_biUnion actual_disjoint]

/-- Enlarging the true physical upper endpoint only increases an actual
dyadic Euler-factor shell; each retained prime-product factor is positive. -/
theorem scaleAdaptiveDyadicEulerShellMass_mono_upper
    (lower first second : ℕ) (ordered : first ≤ second) :
    scaleAdaptiveDyadicEulerShellMass lower first ≤
      scaleAdaptiveDyadicEulerShellMass lower second := by
  unfold scaleAdaptiveDyadicEulerShellMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro exponent selected
    have bounds := Finset.mem_Ioc.mp selected
    exact Finset.mem_Ioc.mpr ⟨bounds.1, bounds.2.trans ordered⟩
  · intro exponent _selected _not_selected
    exact (scaleAdaptiveDyadicEulerFactor_pos exponent).le

/-- Uniform genuine Mertens bound for the EARLY low-prime type support.
Its actual harmonic mass grows only linearly in the adaptive parameter,
even though its integer prime cutoff is `2^(2^n)`. -/
theorem scaleAdaptiveGlobalEarlyLowTypeHarmonicMass_le_affine
    (parameter : ℕ) :
    adaptivePrimeHarmonicPrefix
      (2 ^ scaleAdaptiveColoredLowerExponent parameter) ≤
      (parameter : ℝ) * Real.log (2 : ℝ) +
        |Real.log (Real.log (2 : ℝ))| + |Mertens.M| +
          adaptiveMertensHarmonicErrorConstant /
            Real.log (2 : ℝ) := by
  let exponent := scaleAdaptiveColoredLowerExponent parameter
  let cutoff := 2 ^ exponent
  have exponent_positive : 0 < exponent := by
    dsimp [exponent, scaleAdaptiveColoredLowerExponent]
    positivity
  have cutoff_large : 2 ≤ cutoff := by
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ exponent := Nat.pow_le_pow_right (by norm_num)
        (by omega)
  have cutoff_real_large : (2 : ℝ) ≤ cutoff := by
    exact_mod_cast cutoff_large
  have error := Mertens.E₂p.abs_le cutoff_real_large
  change
    |Mertens.E₂p (cutoff : ℝ)| ≤
      adaptiveMertensHarmonicErrorConstant /
        Real.log (cutoff : ℝ) at error
  have log_two_positive := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have log_order : Real.log (2 : ℝ) ≤ Real.log (cutoff : ℝ) :=
    Real.log_le_log (by norm_num) cutoff_real_large
  have error_bound :
      |Mertens.E₂p (cutoff : ℝ)| ≤
        adaptiveMertensHarmonicErrorConstant / Real.log (2 : ℝ) :=
    error.trans (div_le_div_of_nonneg_left
      adaptiveMertensHarmonicErrorConstant_nonnegative
      log_two_positive log_order)
  have width := scaleAdaptiveGlobalDyadicLogLogWidth
    1 exponent (by omega) exponent_positive
  have exponent_log :
      Real.log (exponent : ℝ) =
        (parameter : ℝ) * Real.log (2 : ℝ) := by
    dsimp [exponent, scaleAdaptiveColoredLowerExponent]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow]
  norm_num only [pow_one, Nat.cast_one, div_one] at width
  change
    Real.log (Real.log (cutoff : ℝ)) -
      Real.log (Real.log (2 : ℝ)) =
        Real.log (exponent : ℝ) at width
  have identity := adaptivePrimeHarmonicPrefix_eq_log_log_add_error cutoff
  have log_bound := le_abs_self (Real.log (Real.log (2 : ℝ)))
  have mertens_bound := le_abs_self Mertens.M
  have signed_error := le_abs_self (Mertens.E₂p (cutoff : ℝ))
  dsimp [exponent, cutoff] at identity error_bound width exponent_log ⊢
  linarith

/-- The entire EARLY low-semiprime support has vanishing true harmonic
exponential budget.  Every type is actually eligible at the first shell,
its complete physical Euler load grows quadratically, and its genuine
prime-harmonic mass grows only linearly. -/
theorem scaleAdaptiveGlobalEarlyLowTypeExponentialBudget_tendsto_zero
    {rate : ℝ} (rate_positive : 0 < rate) :
    Tendsto
      (fun parameter : ℕ =>
        ∑ targetType ∈
          Nat.primesLE
            (2 ^ scaleAdaptiveColoredLowerExponent parameter),
          ((targetType : ℝ)⁻¹) *
            Real.exp (-rate *
              scaleAdaptiveLowEligibleDyadicEulerShell
                targetType
                  (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                (scaleAdaptiveColoredLowerExponent parameter)
                (scaleAdaptiveColoredFullExponent parameter)))
      atTop (nhds (0 : ℝ)) := by
  let coefficient : ℝ :=
    scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 4
  have coefficient_positive : 0 < coefficient := by
    dsimp [coefficient]
    exact div_pos
      (mul_pos scaleAdaptiveDyadicMertensConstant_pos
        (Real.log_pos (by norm_num))) (by norm_num)
  let constant : ℝ :=
    max 1 (|Real.log (Real.log (2 : ℝ))| + |Mertens.M| +
      adaptiveMertensHarmonicErrorConstant / Real.log (2 : ℝ))
  have constant_positive : 0 < constant :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have model :
      Tendsto
        (fun parameter : ℕ =>
          constant * (((parameter : ℝ) + 1) *
            Real.exp (-(rate * coefficient) * (parameter : ℝ))))
        atTop (nhds (0 : ℝ)) := by
    have real := adaptiveDeficit_affine_exp_decay
      (mul_pos rate_positive coefficient_positive)
    simpa using
      (real.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
        constant
  apply squeeze_zero' _ _ model
  · exact Filter.Eventually.of_forall fun parameter => by
      apply Finset.sum_nonneg
      intro targetType _selected
      exact mul_nonneg
        (inv_nonneg.mpr (Nat.cast_nonneg targetType))
        (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (2 : ℕ),
      scaleAdaptiveColoredLowShell_eventually_ge_quadratic]
        with parameter large low_shell
    have orders := scaleAdaptiveColoredExponent_order large
    have full_shell := scaleAdaptiveDyadicEulerShellMass_mono_upper
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredSplitExponent parameter)
      (scaleAdaptiveColoredFullExponent parameter)
      orders.2
    have shell_lower :
        coefficient * (parameter : ℝ) ^ 2 ≤
          scaleAdaptiveDyadicEulerShellMass
            (scaleAdaptiveColoredLowerExponent parameter)
            (scaleAdaptiveColoredFullExponent parameter) := by
      exact low_shell.trans full_shell
    have early_identity :
        (∑ targetType ∈ Nat.primesLE
          (2 ^ scaleAdaptiveColoredLowerExponent parameter),
          ((targetType : ℝ)⁻¹) *
            Real.exp (-rate *
              scaleAdaptiveLowEligibleDyadicEulerShell
                targetType
                  (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                (scaleAdaptiveColoredLowerExponent parameter)
                (scaleAdaptiveColoredFullExponent parameter))) =
          adaptivePrimeHarmonicPrefix
            (2 ^ scaleAdaptiveColoredLowerExponent parameter) *
              Real.exp (-rate *
                scaleAdaptiveDyadicEulerShellMass
                  (scaleAdaptiveColoredLowerExponent parameter)
                  (scaleAdaptiveColoredFullExponent parameter)) := by
      unfold adaptivePrimeHarmonicPrefix
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro targetType selected
      have type_data := Nat.mem_primesLE.mp selected
      have cutoff :
          targetType ≤ 2 ^ scaleAdaptiveColoredSplitExponent parameter :=
        type_data.1.trans
          (Nat.pow_le_pow_right (by norm_num) orders.1)
      rw [scaleAdaptiveLowEligibleDyadicEulerShell_eq
        type_data.2 cutoff type_data.1]
    rw [early_identity]
    have log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
      have estimate := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at estimate ⊢
      exact estimate
    have harmonic := scaleAdaptiveGlobalEarlyLowTypeHarmonicMass_le_affine
      parameter
    have constant_bound :
        |Real.log (Real.log (2 : ℝ))| + |Mertens.M| +
          adaptiveMertensHarmonicErrorConstant /
            Real.log (2 : ℝ) ≤ constant := le_max_right _ _
    have n_nonnegative : (0 : ℝ) ≤ parameter := Nat.cast_nonneg _
    have harmonic_bound :
        adaptivePrimeHarmonicPrefix
          (2 ^ scaleAdaptiveColoredLowerExponent parameter) ≤
            constant * ((parameter : ℝ) + 1) := by
      have linear := mul_le_mul_of_nonneg_left log_two_le_one n_nonnegative
      have one_le_constant : (1 : ℝ) ≤ constant := le_max_left _ _
      have factor := mul_le_mul_of_nonneg_right
        one_le_constant n_nonnegative
      calc
        _ ≤ (parameter : ℝ) * Real.log (2 : ℝ) +
          |Real.log (Real.log (2 : ℝ))| + |Mertens.M| +
          adaptiveMertensHarmonicErrorConstant /
            Real.log (2 : ℝ) := harmonic
        _ ≤ (parameter : ℝ) + constant := by linarith
        _ ≤ constant * (parameter : ℝ) + constant := by nlinarith
        _ = _ := by ring
    have quadratic_ge_linear :
        (parameter : ℝ) ≤ (parameter : ℝ) ^ 2 := by
      have real_large : (1 : ℝ) ≤ parameter := by
        exact_mod_cast (show 1 ≤ parameter by omega)
      nlinarith
    have exponential_bound :
        Real.exp (-rate *
          scaleAdaptiveDyadicEulerShellMass
            (scaleAdaptiveColoredLowerExponent parameter)
            (scaleAdaptiveColoredFullExponent parameter)) ≤
          Real.exp (-(rate * coefficient) * (parameter : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg coefficient_positive.le
        (sub_nonneg.mpr quadratic_ge_linear)]
    have prefix_nonnegative :
        0 ≤ adaptivePrimeHarmonicPrefix
          (2 ^ scaleAdaptiveColoredLowerExponent parameter) := by
      unfold adaptivePrimeHarmonicPrefix
      exact Finset.sum_nonneg
        (fun targetType _ => inv_nonneg.mpr (Nat.cast_nonneg targetType))
    have product := mul_le_mul harmonic_bound exponential_bound
      (Real.exp_pos _).le
      (mul_nonneg constant_positive.le (by positivity))
    calc
      _ ≤ (constant * ((parameter : ℝ) + 1)) *
          Real.exp (-(rate * coefficient) * (parameter : ℝ)) := product
      _ = _ := by ring

/-- The COMPLETE actual LOW semiprime support has vanishing harmonic
exponential budget.  Early and late genuine prime types partition exactly;
late types retain their individual eligible-tail loads, while early types
retain their full quadratic physical load. -/
theorem scaleAdaptiveGlobalFullLowTypeExponentialBudget_tendsto_zero
    {rate : ℝ} (rate_positive : 0 < rate) :
    Tendsto
      (fun parameter : ℕ =>
        ∑ targetType ∈
          Nat.primesLE
            (2 ^ scaleAdaptiveColoredSplitExponent parameter),
          ((targetType : ℝ)⁻¹) *
            Real.exp (-rate *
              scaleAdaptiveLowEligibleDyadicEulerShell
                targetType
                  (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                (scaleAdaptiveColoredLowerExponent parameter)
                (scaleAdaptiveColoredFullExponent parameter)))
      atTop (nhds (0 : ℝ)) := by
  have early :=
    scaleAdaptiveGlobalEarlyLowTypeExponentialBudget_tendsto_zero
      rate_positive
  have late :=
    scaleAdaptiveGlobalLateLowTypeExponentialBudget_tendsto_zero
      rate_positive
  have combined :
      Tendsto
        (fun parameter : ℕ =>
          (∑ targetType ∈ Nat.primesLE
            (2 ^ scaleAdaptiveColoredLowerExponent parameter),
            ((targetType : ℝ)⁻¹) *
              Real.exp (-rate *
                scaleAdaptiveLowEligibleDyadicEulerShell
                  targetType
                    (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                  (scaleAdaptiveColoredLowerExponent parameter)
                  (scaleAdaptiveColoredFullExponent parameter))) +
          (∑ targetType ∈
            (Nat.primesLE
              (2 ^ scaleAdaptiveColoredSplitExponent parameter)) \
              (Nat.primesLE
                (2 ^ scaleAdaptiveColoredLowerExponent parameter)),
            ((targetType : ℝ)⁻¹) *
              Real.exp (-rate *
                scaleAdaptiveLowEligibleDyadicEulerShell
                  targetType
                    (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                  (scaleAdaptiveColoredLowerExponent parameter)
                  (scaleAdaptiveColoredFullExponent parameter))))
        atTop (nhds (0 : ℝ)) := by
    simpa using early.add late
  apply combined.congr'
  filter_upwards [eventually_ge_atTop 2] with parameter large
  have order := (scaleAdaptiveColoredExponent_order large).1
  have inclusion :
      Nat.primesLE (2 ^ scaleAdaptiveColoredLowerExponent parameter) ⊆
        Nat.primesLE (2 ^ scaleAdaptiveColoredSplitExponent parameter) :=
    Nat.primesLE_mono (Nat.pow_le_pow_right (by norm_num) order)
  have decomposition := Finset.sum_sdiff inclusion
    (f := fun targetType : ℕ =>
      ((targetType : ℝ)⁻¹) *
        Real.exp (-rate *
          scaleAdaptiveLowEligibleDyadicEulerShell
            targetType
              (2 ^ scaleAdaptiveColoredSplitExponent parameter)
            (scaleAdaptiveColoredLowerExponent parameter)
            (scaleAdaptiveColoredFullExponent parameter)))
  linarith

/-- BOTH genuine colored semiprime missing-hit coefficients tend to zero
simultaneously.  Low uses the complete actual type-dependent eligible-tail
sum; high uses the complete actual high-support harmonic mass. -/
theorem scaleAdaptiveGlobalTwoColorTypeExponentialBudgets_tendsto_zero
    {lowRate highRate : ℝ}
    (low_positive : 0 < lowRate) (high_positive : 0 < highRate) :
    Tendsto
      (fun parameter : ℕ =>
        (∑ targetType ∈
          Nat.primesLE
            (2 ^ scaleAdaptiveColoredSplitExponent parameter),
          ((targetType : ℝ)⁻¹) *
            Real.exp (-lowRate *
              scaleAdaptiveLowEligibleDyadicEulerShell
                targetType
                  (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                (scaleAdaptiveColoredLowerExponent parameter)
                (scaleAdaptiveColoredFullExponent parameter))) +
        adaptivePrimeHarmonicInterval
          (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          (2 ^ scaleAdaptiveColoredFullExponent parameter) *
            Real.exp (-highRate *
              scaleAdaptiveHighDyadicEulerShellMass
                (scaleAdaptiveColoredFullExponent parameter)
                (scaleAdaptiveColoredSplitExponent parameter)
                (scaleAdaptiveColoredLowerExponent parameter)
                (scaleAdaptiveColoredSplitExponent parameter)))
      atTop (nhds (0 : ℝ)) := by
  simpa using
    (scaleAdaptiveGlobalFullLowTypeExponentialBudget_tendsto_zero
      low_positive).add
      (scaleAdaptiveGlobalHighTypeExponentialBudget_tendsto_zero
        high_positive)

/-- The ACTUAL full low-family physical Euler load diverges fast enough
for every positive colored prime-target missing-hit rate. -/
theorem scaleAdaptiveGlobalLowPrimeExponentialBudget_tendsto_zero
    {rate : ℝ} (rate_positive : 0 < rate) :
    Tendsto
      (fun parameter : ℕ =>
        Real.exp (-rate *
          scaleAdaptiveDyadicEulerShellMass
            (scaleAdaptiveColoredLowerExponent parameter)
            (scaleAdaptiveColoredFullExponent parameter)))
      atTop (nhds (0 : ℝ)) := by
  let coefficient : ℝ :=
    scaleAdaptiveDyadicMertensConstant * Real.log (2 : ℝ) / 4
  have coefficient_positive : 0 < coefficient := by
    unfold coefficient
    exact div_pos
      (mul_pos scaleAdaptiveDyadicMertensConstant_pos
        (Real.log_pos (by norm_num))) (by norm_num)
  have growth :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
      (mul_pos rate_positive coefficient_positive)
  have majorant :
      Tendsto
        (fun parameter : ℕ =>
          Real.exp (-(rate * coefficient) * (parameter : ℝ)))
        atTop (nhds (0 : ℝ)) := by
    simpa [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp growth
  apply squeeze_zero' _ _ majorant
  · exact Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (2 : ℕ),
      scaleAdaptiveColoredLowShell_eventually_ge_quadratic]
      with parameter large short
    have order := (scaleAdaptiveColoredExponent_order large).2
    have complete := scaleAdaptiveDyadicEulerShellMass_mono_upper
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredSplitExponent parameter)
      (scaleAdaptiveColoredFullExponent parameter) order
    have lower :
        coefficient * (parameter : ℝ) ^ 2 ≤
          scaleAdaptiveDyadicEulerShellMass
            (scaleAdaptiveColoredLowerExponent parameter)
            (scaleAdaptiveColoredFullExponent parameter) :=
      short.trans complete
    have real_large : (1 : ℝ) ≤ parameter := by
      exact_mod_cast (show 1 ≤ parameter by omega)
    have square : (parameter : ℝ) ≤ (parameter : ℝ) ^ 2 := by
      nlinarith
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg coefficient_positive.le
      (sub_nonneg.mpr square)]

/-- ALL FOUR source-faithful two-color missing-hit coefficients vanish
simultaneously: actual low prime targets, actual high prime targets,
every low semiprime with its OWN eligible physical tail, and every high
semiprime with its true complete harmonic type mass.  The rates may be
different and can include the exact fair-color factor `1/2` and the
actual target-load constant `1/8`. -/
theorem scaleAdaptiveGlobalCompleteColoredExponentialBudgets_tendsto_zero
    {lowPrimeRate highPrimeRate lowTypeRate highTypeRate : ℝ}
    (low_prime_positive : 0 < lowPrimeRate)
    (high_prime_positive : 0 < highPrimeRate)
    (low_type_positive : 0 < lowTypeRate)
    (high_type_positive : 0 < highTypeRate) :
    Tendsto
      (fun parameter : ℕ =>
        Real.exp (-lowPrimeRate *
          scaleAdaptiveDyadicEulerShellMass
            (scaleAdaptiveColoredLowerExponent parameter)
            (scaleAdaptiveColoredFullExponent parameter)) +
        Real.exp (-highPrimeRate *
          scaleAdaptiveHighDyadicEulerShellMass
            (scaleAdaptiveColoredFullExponent parameter)
            (scaleAdaptiveColoredSplitExponent parameter)
            (scaleAdaptiveColoredLowerExponent parameter)
            (scaleAdaptiveColoredSplitExponent parameter)) +
        (∑ targetType ∈
          Nat.primesLE
            (2 ^ scaleAdaptiveColoredSplitExponent parameter),
          ((targetType : ℝ)⁻¹) *
            Real.exp (-lowTypeRate *
              scaleAdaptiveLowEligibleDyadicEulerShell
                targetType
                  (2 ^ scaleAdaptiveColoredSplitExponent parameter)
                (scaleAdaptiveColoredLowerExponent parameter)
                (scaleAdaptiveColoredFullExponent parameter))) +
        adaptivePrimeHarmonicInterval
          (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          (2 ^ scaleAdaptiveColoredFullExponent parameter) *
            Real.exp (-highTypeRate *
              scaleAdaptiveHighDyadicEulerShellMass
                (scaleAdaptiveColoredFullExponent parameter)
                (scaleAdaptiveColoredSplitExponent parameter)
                (scaleAdaptiveColoredLowerExponent parameter)
                (scaleAdaptiveColoredSplitExponent parameter)))
      atTop (nhds (0 : ℝ)) := by
  simpa using
    (((scaleAdaptiveGlobalLowPrimeExponentialBudget_tendsto_zero
      low_prime_positive).add
        (scaleAdaptiveColoredHighMissingProbability_tendsto_zero
          high_prime_positive)).add
          (scaleAdaptiveGlobalFullLowTypeExponentialBudget_tendsto_zero
            low_type_positive)).add
              (scaleAdaptiveGlobalHighTypeExponentialBudget_tendsto_zero
                high_type_positive)


end Erdos1139
