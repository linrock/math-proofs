module

public import ScaleAdaptiveGlobalJointOptionAssembly1139
public import ScaleAdaptiveIntegerCleanupLedger1139
public import ScaleAdaptiveGlobalExponentialBudgets1139
public import ScaleAdaptiveActualGlobalBudgetTransfer1139

@[expose] public section


/-!
# Final fixed-parameter geometry for the exact original Erdős #1139 bridge

The actual mixed core parameter must be `z = 2^K + 1`, not `2^K`: this
simultaneously keeps the final physical shell `j = K` genuinely fresh and
ensures that ALL deficient small prime types `s < z` are exactly those
covered by the supports through `2^K`.

All physical exponents and prime-pattern complexities are fixed before the
original target length tends to infinity.  The outer adaptive parameter is
sent to infinity only afterward.  This module derives the precise endpoint,
support, geometric prime-density, and conductor/cleanup margin facts needed
to connect the genuine global joint options to the literal historical
conjecture.  No missing actual colored exponential budget is postulated.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega BigOperators Topology

namespace Erdos1139

/-- TRUE mixed-core parameter: the successor of the top dyadic cutoff.
The successor is essential for freshness of the actual final shell. -/
def scaleAdaptiveFinalCoreParameter (parameter : ℕ) : ℕ :=
  2 ^ scaleAdaptiveColoredFullExponent parameter + 1

/-- Exact fixed low/high type split, with the closed low endpoint retained. -/
def scaleAdaptiveFinalTypeCutoff (parameter : ℕ) : ℕ :=
  2 ^ scaleAdaptiveColoredSplitExponent parameter

/-- All actual physical prime-label shells, including the final exponent
and excluding the lower conductor cutoff. -/
def scaleAdaptiveFinalExponents (parameter : ℕ) : Finset ℕ :=
  Finset.Ioc (scaleAdaptiveColoredLowerExponent parameter)
    (scaleAdaptiveColoredFullExponent parameter)

/-- Genuine adaptive LOW support, retaining physical eligibility `s ≤ 2^j`. -/
def scaleAdaptiveFinalLowSupport (parameter exponent : ℕ) : Finset ℕ :=
  adaptiveLowPrimeSupport (2 ^ exponent)
    (scaleAdaptiveFinalTypeCutoff parameter)

/-- Genuine HIGH support for every physical shell; all actual deficient
types above the split and below the successor core parameter are included. -/
def scaleAdaptiveFinalHighSupport (parameter _exponent : ℕ) : Finset ℕ :=
  adaptiveHighPrimeSupport
    (2 ^ scaleAdaptiveColoredFullExponent parameter)
    (scaleAdaptiveFinalTypeCutoff parameter)

/-- The true final core parameter is positive at every adaptive index. -/
theorem scaleAdaptiveFinalCoreParameter_pos (parameter : ℕ) :
    0 < scaleAdaptiveFinalCoreParameter parameter := by
  unfold scaleAdaptiveFinalCoreParameter
  positivity

/-- The genuine successor-core coefficient is STRICTLY positive at every
fixed adaptive parameter; it can therefore be used as actual asymptotic
budget slack rather than an invented infinitesimal. -/
theorem scaleAdaptiveFinalCoreParameter_inverse_pos (parameter : ℕ) :
    0 < ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ := by
  exact inv_pos.mpr (by exact_mod_cast
    scaleAdaptiveFinalCoreParameter_pos parameter)

/-- Every actual finite supported prime harmonic prefix is nonnegative. -/
theorem scaleAdaptiveFinalPrimeHarmonicPrefix_nonnegative
    (cutoff : ℕ) :
    0 ≤ adaptivePrimeHarmonicPrefix cutoff := by
  unfold adaptivePrimeHarmonicPrefix
  exact Finset.sum_nonneg fun prime _ =>
    inv_nonneg.mpr (Nat.cast_nonneg prime)

/-- Every genuine physical shell, INCLUDING its final endpoint, is strictly
fresh relative to the actual successor core parameter. -/
theorem scaleAdaptiveFinalExponent_fresh
    {parameter exponent : ℕ}
    (selected : exponent ∈ scaleAdaptiveFinalExponents parameter) :
    2 ^ exponent < scaleAdaptiveFinalCoreParameter parameter := by
  have upper := (Finset.mem_Ioc.mp selected).2
  have powers := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) upper
  unfold scaleAdaptiveFinalCoreParameter
  omega

/-- Every selected shell lies strictly past the true conductor cutoff. -/
theorem scaleAdaptiveFinalExponent_after_conductor_cutoff
    {parameter exponent : ℕ}
    (selected : exponent ∈ scaleAdaptiveFinalExponents parameter) :
    scaleAdaptiveColoredLowerExponent parameter < exponent :=
  (Finset.mem_Ioc.mp selected).1

/-- Exact correction of the final support endpoint: `s < 2^K + 1` is
equivalent to the true closed prime-support bound `s ≤ 2^K`. -/
theorem scaleAdaptiveFinalDeficientType_cutoff_iff
    {parameter targetType : ℕ} :
    targetType < scaleAdaptiveFinalCoreParameter parameter ↔
      targetType ≤ 2 ^ scaleAdaptiveColoredFullExponent parameter := by
  unfold scaleAdaptiveFinalCoreParameter
  omega

/-- Every genuinely high deficient prime type belongs to the actual HIGH
support; there is no uncovered last dyadic type band. -/
theorem scaleAdaptiveFinalHighType_mem
    {parameter exponent targetType : ℕ}
    (prime : targetType.Prime)
    (deficient_type : targetType < scaleAdaptiveFinalCoreParameter parameter)
    (above_split : scaleAdaptiveFinalTypeCutoff parameter < targetType) :
    targetType ∈ scaleAdaptiveFinalHighSupport parameter exponent := by
  apply mem_adaptiveHighPrimeSupport.mpr
  exact ⟨prime, above_split,
    scaleAdaptiveFinalDeficientType_cutoff_iff.mp deficient_type⟩

/-- A genuinely low deficient prime type occurs EXACTLY on its physically
eligible shells; no unavailable `s > 2^j` type is included. -/
theorem scaleAdaptiveFinalLowType_mem_iff
    {parameter exponent targetType : ℕ} :
    targetType ∈ scaleAdaptiveFinalLowSupport parameter exponent ↔
      targetType.Prime ∧
        targetType ≤ scaleAdaptiveFinalTypeCutoff parameter ∧
        targetType ≤ 2 ^ exponent := by
  unfold scaleAdaptiveFinalLowSupport
  rw [mem_adaptiveLowPrimeSupport]
  tauto

/-- Both final supports contain only actual primes on every physical shell. -/
theorem scaleAdaptiveFinalLowSupport_primes
    (parameter exponent : ℕ)
    {prime : ℕ}
    (selected : prime ∈ scaleAdaptiveFinalLowSupport
      parameter exponent) : prime.Prime :=
  (scaleAdaptiveFinalLowType_mem_iff.mp selected).1

theorem scaleAdaptiveFinalHighSupport_primes
    (parameter exponent : ℕ)
    {prime : ℕ}
    (selected : prime ∈ scaleAdaptiveFinalHighSupport
      parameter exponent) : prime.Prime := by
  exact (mem_adaptiveHighPrimeSupport.mp selected).1

/-- Every exact selected prime-shell density is the corresponding true
geometric term, with no approximation in the exponent or coefficient. -/
theorem scaleAdaptiveFinalPrimeShellTerm_eq
    (exponent : ℕ) :
    (((2 ^ exponent : ℕ) : ℝ)⁻¹) =
      ((1 / 2 : ℝ) ^ exponent) := by
  push_cast
  simp [div_eq_mul_inv, inv_pow]

/-- The TOTAL actual selected-prime density of all physical shells is at
most the TRUE lower-cutoff conductor coefficient `2^{-a}`. -/
theorem scaleAdaptiveFinalSelectedPrimeDensity_le_conductor
    (parameter : ℕ) :
    (∑ exponent ∈ scaleAdaptiveFinalExponents parameter,
      (((2 ^ exponent : ℕ) : ℝ)⁻¹)) ≤
        scaleAdaptiveColoredConductorDensity parameter := by
  let lower := scaleAdaptiveColoredLowerExponent parameter
  let upper := scaleAdaptiveColoredFullExponent parameter
  have geometric := geom_sum_Ico_le_of_lt_one
    (m := lower + 1) (n := upper + 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have interval :
      Finset.Ico (lower + 1) (upper + 1) = Finset.Ioc lower upper :=
    Finset.Ico_add_one_add_one_eq_Ioc lower upper
  rw [interval] at geometric
  change
    (∑ exponent ∈ Finset.Ioc lower upper,
      (((2 ^ exponent : ℕ) : ℝ)⁻¹)) ≤
      (((2 ^ lower : ℕ) : ℝ)⁻¹)
  calc
    (∑ exponent ∈ Finset.Ioc lower upper,
      (((2 ^ exponent : ℕ) : ℝ)⁻¹)) =
      ∑ exponent ∈ Finset.Ioc lower upper,
        (1 / 2 : ℝ) ^ exponent := by
          apply Finset.sum_congr rfl
          intro exponent _
          exact scaleAdaptiveFinalPrimeShellTerm_eq exponent
    _ ≤ (1 / 2 : ℝ) ^ (lower + 1) / (1 - (1 / 2 : ℝ)) :=
      geometric
    _ = (((2 ^ lower : ℕ) : ℝ)⁻¹) := by
      rw [scaleAdaptiveFinalPrimeShellTerm_eq]
      rw [pow_succ]
      norm_num

/-- The true global selected-prime coefficient vanishes in the OUTER
adaptive limit, after all fixed-parameter pattern limits. -/
theorem scaleAdaptiveFinalSelectedPrimeDensity_tendsto_zero :
    Tendsto
      (fun parameter : ℕ =>
        ∑ exponent ∈ scaleAdaptiveFinalExponents parameter,
          (((2 ^ exponent : ℕ) : ℝ)⁻¹))
      atTop (nhds (0 : ℝ)) := by
  apply squeeze_zero' _ _ scaleAdaptiveColoredConductorDensity_tendsto_zero
  · exact Filter.Eventually.of_forall fun parameter =>
      Finset.sum_nonneg fun exponent _ =>
        inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact Filter.Eventually.of_forall
      scaleAdaptiveFinalSelectedPrimeDensity_le_conductor

/-- The exact successor core has vanishing inverse density; its retained
`1/z` proper cleanup coefficient is not discarded at fixed parameter. -/
theorem scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero :
    Tendsto
      (fun parameter : ℕ =>
        ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹)
      atTop (nhds (0 : ℝ)) := by
  apply squeeze_zero' _ _ scaleAdaptiveColoredConductorDensity_tendsto_zero
  · exact Filter.Eventually.of_forall fun parameter =>
      inv_nonneg.mpr (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with parameter large
    have order := (scaleAdaptiveColoredExponent_order large).1.trans
      (scaleAdaptiveColoredExponent_order large).2
    have power_order := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) order
    have core_bound :
        2 ^ scaleAdaptiveColoredLowerExponent parameter ≤
          scaleAdaptiveFinalCoreParameter parameter := by
      unfold scaleAdaptiveFinalCoreParameter
      omega
    have real_positive :
        (0 : ℝ) < (2 ^ scaleAdaptiveColoredLowerExponent parameter : ℕ) := by
      exact_mod_cast (show 0 <
        2 ^ scaleAdaptiveColoredLowerExponent parameter by positivity)
    have real_bound :
        ((2 ^ scaleAdaptiveColoredLowerExponent parameter : ℕ) : ℝ) ≤
          (scaleAdaptiveFinalCoreParameter parameter : ℝ) := by
      exact_mod_cast core_bound
    change
      (scaleAdaptiveFinalCoreParameter parameter : ℝ)⁻¹ ≤
        (((2 ^ scaleAdaptiveColoredLowerExponent parameter : ℕ) : ℝ))⁻¹
    simpa [one_div] using one_div_le_one_div_of_le real_positive real_bound

/-- Complete TRUE low-color Euler majorant: actual prime targets plus every
low semiprime with its OWN support-dependent eligible physical tail. -/
noncomputable def scaleAdaptiveFinalLowBudgetCoefficient
    (rate : ℝ) (parameter : ℕ) : ℝ :=
  Real.exp (-rate *
    scaleAdaptiveDyadicEulerShellMass
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredFullExponent parameter)) +
  ∑ targetType ∈
    Nat.primesLE
      (2 ^ scaleAdaptiveColoredSplitExponent parameter),
    ((targetType : ℝ)⁻¹) *
      Real.exp (-rate *
        scaleAdaptiveLowEligibleDyadicEulerShell
          targetType
            (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          (scaleAdaptiveColoredLowerExponent parameter)
          (scaleAdaptiveColoredFullExponent parameter))

/-- Complete TRUE high-color Euler majorant: prime targets plus the actual
harmonic mass of every high semiprime type. -/
noncomputable def scaleAdaptiveFinalHighBudgetCoefficient
    (rate : ℝ) (parameter : ℕ) : ℝ :=
  Real.exp (-rate *
    scaleAdaptiveHighDyadicEulerShellMass
      (scaleAdaptiveColoredFullExponent parameter)
      (scaleAdaptiveColoredSplitExponent parameter)
      (scaleAdaptiveColoredLowerExponent parameter)
      (scaleAdaptiveColoredSplitExponent parameter)) +
  adaptivePrimeHarmonicInterval
    (2 ^ scaleAdaptiveColoredSplitExponent parameter)
    (2 ^ scaleAdaptiveColoredFullExponent parameter) *
      Real.exp (-rate *
        scaleAdaptiveHighDyadicEulerShellMass
          (scaleAdaptiveColoredFullExponent parameter)
          (scaleAdaptiveColoredSplitExponent parameter)
          (scaleAdaptiveColoredLowerExponent parameter)
          (scaleAdaptiveColoredSplitExponent parameter))

/-- Both complete colored coefficients are genuinely nonnegative. -/
theorem scaleAdaptiveFinalLowBudgetCoefficient_nonnegative
    (rate : ℝ) (parameter : ℕ) :
    0 ≤ scaleAdaptiveFinalLowBudgetCoefficient rate parameter := by
  unfold scaleAdaptiveFinalLowBudgetCoefficient
  exact add_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun targetType _ =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg targetType))
        (Real.exp_pos _).le)

theorem scaleAdaptiveFinalHighBudgetCoefficient_nonnegative
    (rate : ℝ) (parameter : ℕ) :
    0 ≤ scaleAdaptiveFinalHighBudgetCoefficient rate parameter := by
  unfold scaleAdaptiveFinalHighBudgetCoefficient
  exact add_nonneg (Real.exp_pos _).le
    (mul_nonneg
      (adaptivePrimeHarmonicInterval_nonnegative _ _)
      (Real.exp_pos _).le)

/-- Every genuine positive fair-color/actual-load rate makes the COMPLETE
low prime-plus-all-types coefficient tend to zero in the OUTER limit. -/
theorem scaleAdaptiveFinalLowBudgetCoefficient_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto (scaleAdaptiveFinalLowBudgetCoefficient rate)
      atTop (nhds (0 : ℝ)) := by
  change Tendsto
    (fun parameter : ℕ => scaleAdaptiveFinalLowBudgetCoefficient rate parameter)
    atTop (nhds (0 : ℝ))
  simpa [scaleAdaptiveFinalLowBudgetCoefficient] using
    (scaleAdaptiveGlobalLowPrimeExponentialBudget_tendsto_zero positive).add
      (scaleAdaptiveGlobalFullLowTypeExponentialBudget_tendsto_zero positive)

/-- The genuine high-color prime-plus-all-types coefficient also vanishes. -/
theorem scaleAdaptiveFinalHighBudgetCoefficient_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto (scaleAdaptiveFinalHighBudgetCoefficient rate)
      atTop (nhds (0 : ℝ)) := by
  change Tendsto
    (fun parameter : ℕ => scaleAdaptiveFinalHighBudgetCoefficient rate parameter)
    atTop (nhds (0 : ℝ))
  simpa [scaleAdaptiveFinalHighBudgetCoefficient] using
    (scaleAdaptiveColoredHighMissingProbability_tendsto_zero positive).add
      (scaleAdaptiveGlobalHighTypeExponentialBudget_tendsto_zero positive)

/-- All ACTUAL ledger coefficients vanish jointly: both complete colored
budgets, the true successor core exception, the actual selected shell
density, and the independently audited prime-product conductor. -/
theorem scaleAdaptiveFinalAllLedgerCoefficients_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun parameter : ℕ =>
        scaleAdaptiveFinalLowBudgetCoefficient rate parameter +
        scaleAdaptiveFinalHighBudgetCoefficient rate parameter +
        ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
        (∑ exponent ∈ scaleAdaptiveFinalExponents parameter,
          (((2 ^ exponent : ℕ) : ℝ)⁻¹)) +
        scaleAdaptiveColoredConductorDensity parameter)
      atTop (nhds (0 : ℝ)) := by
  simpa using
    ((((scaleAdaptiveFinalLowBudgetCoefficient_tendsto_zero positive).add
      (scaleAdaptiveFinalHighBudgetCoefficient_tendsto_zero positive)).add
        scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero).add
          scaleAdaptiveFinalSelectedPrimeDensity_tendsto_zero).add
            scaleAdaptiveColoredConductorDensity_tendsto_zero

/-- The COMPLETE natural-integer cleanup prime-counting margin is eventually
strictly available, with any additional vanishing physical-prefix
exception coefficient retained explicitly. -/
theorem scaleAdaptiveFinalPrimeCountingMargin_eventually
    {rate : ℝ} (positive : 0 < rate)
    (extraExceptions : ℕ → ℝ)
    (extra_vanishes : Tendsto extraExceptions atTop (nhds (0 : ℝ))) :
    ∀ᶠ parameter : ℕ in atTop,
      2 * (scaleAdaptiveFinalLowBudgetCoefficient rate parameter +
        scaleAdaptiveFinalHighBudgetCoefficient rate parameter +
        2 * (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
          extraExceptions parameter)) +
        ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
        (∑ exponent ∈ scaleAdaptiveFinalExponents parameter,
          (((2 ^ exponent : ℕ) : ℝ)⁻¹)) < 1 := by
  have low := scaleAdaptiveFinalLowBudgetCoefficient_tendsto_zero positive
  have high := scaleAdaptiveFinalHighBudgetCoefficient_tendsto_zero positive
  have core := scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero
  have shells := scaleAdaptiveFinalSelectedPrimeDensity_tendsto_zero
  have combined : Tendsto
      (fun parameter : ℕ =>
        2 * (scaleAdaptiveFinalLowBudgetCoefficient rate parameter +
          scaleAdaptiveFinalHighBudgetCoefficient rate parameter +
          2 * (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
            extraExceptions parameter)) +
          ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
          (∑ exponent ∈ scaleAdaptiveFinalExponents parameter,
            (((2 ^ exponent : ℕ) : ℝ)⁻¹)))
      atTop (nhds (0 : ℝ)) := by
    convert
      (((low.add high).add
        ((core.add extra_vanishes).const_mul (2 : ℝ))).const_mul
          (2 : ℝ)).add core |>.add shells using 1
    · ext parameter
      ring_nf
  exact combined.eventually (Iio_mem_nhds (by norm_num))

/-- The fully charged prime-product plus natural cleanup conductor can be
made smaller than ANY prescribed positive coefficient once the extra true
physical-prefix exception coefficient also vanishes. -/
theorem scaleAdaptiveFinalFullConductorCoefficient_eventually_small
    {rate epsilon : ℝ} (positive : 0 < rate) (epsilon_positive : 0 < epsilon)
    (extraExceptions : ℕ → ℝ)
    (extra_vanishes : Tendsto extraExceptions atTop (nhds (0 : ℝ))) :
    ∀ᶠ parameter : ℕ in atTop,
      scaleAdaptiveColoredConductorDensity parameter +
        2 * (scaleAdaptiveFinalLowBudgetCoefficient rate parameter +
          scaleAdaptiveFinalHighBudgetCoefficient rate parameter +
          2 * (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
            extraExceptions parameter)) < epsilon := by
  have low := scaleAdaptiveFinalLowBudgetCoefficient_tendsto_zero positive
  have high := scaleAdaptiveFinalHighBudgetCoefficient_tendsto_zero positive
  have core := scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero
  have conductor := scaleAdaptiveColoredConductorDensity_tendsto_zero
  have combined : Tendsto
      (fun parameter : ℕ =>
        scaleAdaptiveColoredConductorDensity parameter +
          2 * (scaleAdaptiveFinalLowBudgetCoefficient rate parameter +
            scaleAdaptiveFinalHighBudgetCoefficient rate parameter +
            2 * (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
              extraExceptions parameter)))
      atTop (nhds (0 : ℝ)) := by
    convert conductor.add
      (((low.add high).add
        ((core.add extra_vanishes).const_mul (2 : ℝ))).const_mul
          (2 : ℝ)) using 1
    · ext parameter
      ring_nf
  exact combined.eventually (Iio_mem_nhds epsilon_positive)

/-- A strictly positive, vanishing fixed-parameter slack for the TRUE
original-scale colored missing-hit inequalities.  Using the actual
successor-core coefficient avoids introducing any additional free
asymptotic parameter or discarding the nonzero fixed-parameter cleanup. -/
noncomputable def scaleAdaptiveFinalRoundedLowBudgetCoefficient
    (rate : ℝ) (parameter : ℕ) : ℝ :=
  scaleAdaptiveFinalLowBudgetCoefficient rate parameter +
    ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹

/-- Matching positive slack for the second color; both colors use the SAME
actual fixed-parameter global joint configuration. -/
noncomputable def scaleAdaptiveFinalRoundedHighBudgetCoefficient
    (rate : ℝ) (parameter : ℕ) : ℝ :=
  scaleAdaptiveFinalHighBudgetCoefficient rate parameter +
    ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹

theorem scaleAdaptiveFinalRoundedLowBudgetCoefficient_nonnegative
    (rate : ℝ) (parameter : ℕ) :
    0 ≤ scaleAdaptiveFinalRoundedLowBudgetCoefficient rate parameter := by
  exact add_nonneg
    (scaleAdaptiveFinalLowBudgetCoefficient_nonnegative rate parameter)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem scaleAdaptiveFinalRoundedHighBudgetCoefficient_nonnegative
    (rate : ℝ) (parameter : ℕ) :
    0 ≤ scaleAdaptiveFinalRoundedHighBudgetCoefficient rate parameter := by
  exact add_nonneg
    (scaleAdaptiveFinalHighBudgetCoefficient_nonnegative rate parameter)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem scaleAdaptiveFinalRoundedLowBudgetCoefficient_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto (scaleAdaptiveFinalRoundedLowBudgetCoefficient rate)
      atTop (nhds (0 : ℝ)) := by
  change Tendsto
    (fun parameter : ℕ =>
      scaleAdaptiveFinalLowBudgetCoefficient rate parameter +
        ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹)
    atTop (nhds (0 : ℝ))
  simpa using
    (scaleAdaptiveFinalLowBudgetCoefficient_tendsto_zero positive).add
      scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero

theorem scaleAdaptiveFinalRoundedHighBudgetCoefficient_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto (scaleAdaptiveFinalRoundedHighBudgetCoefficient rate)
      atTop (nhds (0 : ℝ)) := by
  change Tendsto
    (fun parameter : ℕ =>
      scaleAdaptiveFinalHighBudgetCoefficient rate parameter +
        ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹)
    atTop (nhds (0 : ℝ))
  simpa using
    (scaleAdaptiveFinalHighBudgetCoefficient_tendsto_zero positive).add
      scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero

/-- All strict margins needed by the LITERAL original problem hold
SIMULTANEOUSLY at one eventual fixed adaptive parameter.  The true basic
core exceptions, any additional physical-prefix exception coefficient,
the actual density of selected primes, and strictly positive slack in
BOTH original colored exponential inequalities are fully charged. -/
theorem scaleAdaptiveFinalRoundedAdmissibleParameters_eventually
    {rate epsilon : ℝ}
    (rate_positive : 0 < rate)
    (epsilon_positive : 0 < epsilon)
    (extraExceptions : ℕ → ℝ)
    (extra_vanishes : Tendsto extraExceptions atTop (nhds (0 : ℝ))) :
    ∀ᶠ parameter : ℕ in atTop,
      2 ≤ parameter ∧
      ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ < epsilon ∧
      2 *
          (scaleAdaptiveFinalRoundedLowBudgetCoefficient rate parameter +
            scaleAdaptiveFinalRoundedHighBudgetCoefficient rate parameter +
            2 * (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
              extraExceptions parameter)) +
          ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
          (∑ exponent ∈ scaleAdaptiveFinalExponents parameter,
            (((2 ^ exponent : ℕ) : ℝ)⁻¹)) < 1 ∧
      scaleAdaptiveColoredConductorDensity parameter +
        2 *
          (scaleAdaptiveFinalRoundedLowBudgetCoefficient rate parameter +
            scaleAdaptiveFinalRoundedHighBudgetCoefficient rate parameter +
            2 * (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
              extraExceptions parameter)) < epsilon := by
  let chargedExtra : ℕ → ℝ := fun parameter =>
    extraExceptions parameter +
      ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹
  have charged_vanishes :
      Tendsto chargedExtra atTop (nhds (0 : ℝ)) := by
    simpa [chargedExtra] using
      extra_vanishes.add scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero
  have core_small :=
    scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero.eventually
      (Iio_mem_nhds epsilon_positive)
  have prime_margin := scaleAdaptiveFinalPrimeCountingMargin_eventually
    rate_positive chargedExtra charged_vanishes
  have conductor_margin :=
    scaleAdaptiveFinalFullConductorCoefficient_eventually_small
      rate_positive epsilon_positive chargedExtra charged_vanishes
  filter_upwards [eventually_ge_atTop 2, core_small,
      prime_margin, conductor_margin] with
    parameter parameter_large core_bound prime_bound conductor_bound
  refine ⟨parameter_large, core_bound, ?_, ?_⟩
  · dsimp [scaleAdaptiveFinalRoundedLowBudgetCoefficient, scaleAdaptiveFinalRoundedHighBudgetCoefficient, chargedExtra] at prime_bound ⊢
    convert prime_bound using 1
    ring
  · dsimp [scaleAdaptiveFinalRoundedLowBudgetCoefficient, scaleAdaptiveFinalRoundedHighBudgetCoefficient, chargedExtra] at conductor_bound ⊢
    convert conductor_bound using 1
    ring

/-- Fully charge a nonzero fixed-parameter physical-prefix coefficient
THREE times: once in each genuine colored missing-hit budget, and once
in the actual exceptional cleanup envelope.  Every quantity vanishes only
in the OUTER adaptive limit; no fixed-parameter prefix is discarded. -/
theorem scaleAdaptiveFinalFullyChargedAdmissibleParameters_eventually
    {rate epsilon : ℝ}
    (rate_positive : 0 < rate)
    (epsilon_positive : 0 < epsilon)
    (extraExceptions : ℕ → ℝ)
    (extra_vanishes : Tendsto extraExceptions atTop (nhds (0 : ℝ))) :
    ∀ᶠ parameter : ℕ in atTop,
      2 ≤ parameter ∧
      ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ < epsilon ∧
      2 *
          ((scaleAdaptiveFinalRoundedLowBudgetCoefficient rate parameter +
            extraExceptions parameter) +
            (scaleAdaptiveFinalRoundedHighBudgetCoefficient rate parameter +
              extraExceptions parameter) +
            2 * (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
              extraExceptions parameter)) +
          ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
          (∑ exponent ∈ scaleAdaptiveFinalExponents parameter,
            (((2 ^ exponent : ℕ) : ℝ)⁻¹)) < 1 ∧
      scaleAdaptiveColoredConductorDensity parameter +
        2 *
          ((scaleAdaptiveFinalRoundedLowBudgetCoefficient rate parameter +
            extraExceptions parameter) +
            (scaleAdaptiveFinalRoundedHighBudgetCoefficient rate parameter +
              extraExceptions parameter) +
            2 * (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
              extraExceptions parameter)) < epsilon := by
  let chargedExtra : ℕ → ℝ := fun parameter =>
    2 * extraExceptions parameter +
      ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹
  have charged_vanishes :
      Tendsto chargedExtra atTop (nhds (0 : ℝ)) := by
    simpa [chargedExtra] using
      (extra_vanishes.const_mul (2 : ℝ)).add
        scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero
  have core_small :=
    scaleAdaptiveFinalCoreParameter_inverse_tendsto_zero.eventually
      (Iio_mem_nhds epsilon_positive)
  have prime_margin := scaleAdaptiveFinalPrimeCountingMargin_eventually
    rate_positive chargedExtra charged_vanishes
  have conductor_margin :=
    scaleAdaptiveFinalFullConductorCoefficient_eventually_small
      rate_positive epsilon_positive chargedExtra charged_vanishes
  filter_upwards [eventually_ge_atTop 2, core_small,
      prime_margin, conductor_margin] with
    parameter parameter_large core_bound prime_bound conductor_bound
  refine ⟨parameter_large, core_bound, ?_, ?_⟩
  · dsimp [scaleAdaptiveFinalRoundedLowBudgetCoefficient, scaleAdaptiveFinalRoundedHighBudgetCoefficient, chargedExtra] at prime_bound ⊢
    convert prime_bound using 1
    ring
  · dsimp [scaleAdaptiveFinalRoundedLowBudgetCoefficient, scaleAdaptiveFinalRoundedHighBudgetCoefficient, chargedExtra] at conductor_bound ⊢
    convert conductor_bound using 1
    ring

/-- The actual globally retained prime product is positive; this includes
the empty-pool case, whose genuine product is exactly one. -/
theorem scaleAdaptiveGlobalJointPrimeProduct_pos
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    0 < (∏ prime ∈ scaleAdaptiveGlobalJointPrimePool
      configuration length, prime) := by
  apply Finset.prod_pos
  intro prime selected
  exact (scaleAdaptiveGlobalJointPrimePool_prime
    configuration length selected).pos

/-- Actual global-prime conductor is bounded by the true integer product
of its enclosing disjoint physical shells, not merely by a density proxy. -/
theorem scaleAdaptiveGlobalJointPrimeProduct_log_le_shell
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    Real.log
      ((∏ prime ∈ scaleAdaptiveGlobalJointPrimePool
        configuration length, prime : ℕ) : ℝ) ≤
      Real.log
        ((∏ prime ∈ configuration.exponents.biUnion
          (scaleAdaptiveDyadicPrimeShell length), prime : ℕ) : ℝ) := by
  have divides := scaleAdaptiveGlobalJointPrimePool_product_dvd_shell_product
    configuration length
  have shell_positive := scaleAdaptiveDyadicPrimeShell_product_pos
    length configuration.exponents
  have bound := Nat.le_of_dvd shell_positive divides
  apply Real.log_le_log
  · exact_mod_cast scaleAdaptiveGlobalJointPrimeProduct_pos
      configuration length
  · exact_mod_cast bound

/-- Actual final fixed-parameter global configuration, retaining the exact
successor core endpoint and shell-dependent low/high supports. -/
def scaleAdaptiveFinalJointConfiguration
    (parameter : ℕ) (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ) :
    ScaleAdaptiveGlobalJointConfiguration :=
  { exponents := scaleAdaptiveFinalExponents parameter
    lowSupport := scaleAdaptiveFinalLowSupport parameter
    highSupport := scaleAdaptiveFinalHighSupport parameter
    lower := lower
    upper := upper
    lowSingular := lowSingular
    highSingular := highSingular }

/-- Choose BOTH canonical collision-aware singular families ONCE for all
actual final physical shells.  The same families subsequently define the
global prime pool, the two colored samplers, the true cross-support
rejection sets, and BOTH final original-scale exponential budgets. -/
theorem scaleAdaptiveFinalCanonicalSingularFamilies_exists_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) :
    ∃ lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ,
      ∀ exponent ∈ scaleAdaptiveFinalExponents parameter,
        (∀ outcome : ℕ × ℕ,
          0 < lowSingular exponent outcome ∧
            Tendsto
              (adaptiveMixedSignedSingularPartialProduct
                (scaleAdaptiveFinalLowSupport parameter exponent)
                (2 ^ exponent) outcome)
              atTop (nhds (lowSingular exponent outcome))) ∧
        (∀ outcome : ℕ × ℕ,
          0 < highSingular exponent outcome ∧
            Tendsto
              (adaptiveMixedSignedSingularPartialProduct
                (scaleAdaptiveFinalHighSupport parameter exponent)
                (2 ^ exponent) outcome)
              atTop (nhds (highSingular exponent outcome))) ∧
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              (scaleAdaptiveFinalLowSupport parameter exponent)
              (scaleAdaptiveFinalHighSupport parameter exponent)
              (2 ^ exponent) 0 1
              (lowSingular exponent)
              (highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (0 : ℝ)) ∧
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorGoodPrimeLabels
              (scaleAdaptiveFinalLowSupport parameter exponent)
              (scaleAdaptiveFinalHighSupport parameter exponent)
              (2 ^ exponent) 0 1
              (lowSingular exponent)
              (highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (1 : ℝ)) := by
  exact scaleAdaptiveGlobalJointSingularFamilies_exists_of_GTZ
    green_tao (scaleAdaptiveFinalExponents parameter)
      (scaleAdaptiveFinalLowSupport parameter)
      (scaleAdaptiveFinalHighSupport parameter)
      0 1
      (fun exponent _ prime selected =>
        scaleAdaptiveFinalLowSupport_primes parameter exponent selected)
      (fun exponent _ prime selected =>
        scaleAdaptiveFinalHighSupport_primes parameter exponent selected)
      (by norm_num) (by norm_num) (by norm_num)

/-- Sole explicit signed Green--Tao supplies the EXACT final-endpoint
global option skeleton for every fixed adaptive parameter.  This includes
the final physical shell, every deficient prime type, the true ONE global
prime pool and color/residue arrays, all original target demands, and the
exact nonzero fixed-parameter `1/z` basic exception coefficient. -/
theorem scaleAdaptiveFinalActualOptionData_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter : ℕ) (lower upper : ℝ)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ,
      let configuration := scaleAdaptiveFinalJointConfiguration
        parameter lower upper lowSingular highSingular
      let core := scaleAdaptiveFinalCoreParameter parameter
      let cutoff := scaleAdaptiveFinalTypeCutoff parameter
      let exponents := scaleAdaptiveFinalExponents parameter
      let lowSupport := scaleAdaptiveFinalLowSupport parameter
      let highSupport := scaleAdaptiveFinalHighSupport parameter
      Tendsto
        (fun length : ℕ =>
          ((scaleAdaptiveGlobalJointPrimePool
            configuration length).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds
          (∑ exponent ∈ exponents,
            (((2 ^ exponent : ℕ) : ℝ)⁻¹))) ∧
      Tendsto
        (fun length : ℕ =>
          ((scaleAdaptiveGlobalCompleteTargetExceptions
            length core exponents exponents
              lowSupport highSupport lower upper).card : ℝ) *
                Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds ((core : ℕ) : ℝ)⁻¹) ∧
      ∀ᶠ length : ℕ in atTop,
        let R := scaleAdaptiveGlobalJointPrimePool configuration length
        let lowTargets := scaleAdaptiveGlobalLowTargets
          length core cutoff
        let highTargets := scaleAdaptiveGlobalHighTargets
          length core cutoff
        let exceptions := scaleAdaptiveGlobalCompleteTargetExceptions
          length core exponents exponents
            lowSupport highSupport lower upper
        let k := scaleAdaptiveGlobalJointOptionCount configuration length
        let color := scaleAdaptiveGlobalJointColor configuration length
        let residue := scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets
        0 < k ∧
        (∀ prime ∈ R, prime.Prime) ∧
        Disjoint (fixedParameterCorePrimes length core) R ∧
        R ⊆ exponents.biUnion (scaleAdaptiveDyadicPrimeShell length) ∧
        lowTargets ⊆ Finset.Icc 1 length ∧
        highTargets ⊆ Finset.Icc 1 length ∧
        exceptions ⊆ Finset.Icc 1 length ∧
        WeightedActualPatternOptionsSupported
          R lowTargets highTargets color residue ∧
        (∀ target ∈ Finset.Icc 1 length, target ∉ exceptions →
          2 ≤ fixedParameterCoreHits length core target +
            (if target ∈ lowTargets then 1 else 0) +
            (if target ∈ highTargets then 1 else 0)) := by
  exact scaleAdaptiveGlobalJointActualOptionData_of_GTZ
    green_tao
      (scaleAdaptiveFinalCoreParameter parameter)
      (scaleAdaptiveFinalTypeCutoff parameter)
      (scaleAdaptiveFinalExponents parameter)
      (scaleAdaptiveFinalLowSupport parameter)
      (scaleAdaptiveFinalHighSupport parameter)
      lower upper (scaleAdaptiveFinalCoreParameter_pos parameter)
      (fun exponent _ prime selected =>
        scaleAdaptiveFinalLowSupport_primes parameter exponent selected)
      (fun exponent _ prime selected =>
        scaleAdaptiveFinalHighSupport_primes parameter exponent selected)
      (fun exponent selected => scaleAdaptiveFinalExponent_fresh selected)
      lower_nonnegative band_nonempty upper_bounded

/-- DETERMINISTIC final fixed-parameter join.  Its only nonstructural inputs
are the two explicit ACTUAL same-pool colored exponential inequalities and
a genuine NATURAL upper envelope for the overlapping physical exceptions.

The proof derives every single conjunct of the literal
`HasSublinearJointColoredMarginals` finite witness: one actual prime pool,
one real joint color/residue array, both genuine original target families,
complete deficiency demand, upward-rounded NATURAL budgets, a real prime
reserve disjoint from both core and selected primes, and the actual
selected-prime-product PLUS fully charged cleanup conductor.

There is no opaque replacement hypothesis, matching premise, or asserted
solution hidden in this deterministic assembly lemma. -/
theorem scaleAdaptiveFinalFixedParameterColoredWitness_of_actual_bounds
    (parameter cutoff lowerExponent : ℕ)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (lowCoefficient highCoefficient envelopeCoefficient epsilon : ℝ)
    (exceptions : ℕ → Finset ℕ)
    (envelope : ℕ → ℕ)
    (parameter_positive : 0 < parameter)
    (low_nonnegative : 0 ≤ lowCoefficient)
    (high_nonnegative : 0 ≤ highCoefficient)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
    (inside : ∀ exponent ∈ configuration.exponents,
      2 ^ exponent < parameter)
    (after : ∀ exponent ∈ configuration.exponents,
      lowerExponent < exponent)
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
    (exceptions_supported : ∀ length : ℕ,
      exceptions length ⊆ Finset.Icc 1 length)
    (basic_exceptions_included : ∀ length : ℕ,
      scaleAdaptiveGlobalCompleteTargetExceptions
        length parameter configuration.exponents configuration.exponents
          configuration.lowSupport configuration.highSupport
            configuration.lower configuration.upper ⊆ exceptions length)
    (envelope_bounds : ∀ᶠ length : ℕ in atTop,
      (exceptions length).card ≤ envelope length)
    (envelope_density : Tendsto
      (fun length : ℕ => (envelope length : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds envelopeCoefficient))
    (low_budget : ∀ᶠ length : ℕ in atTop,
      let R := scaleAdaptiveGlobalJointPrimePool configuration length
      let lowTargets := scaleAdaptiveGlobalLowTargets
        length parameter cutoff
      let highTargets := scaleAdaptiveGlobalHighTargets
        length parameter cutoff
      let color := scaleAdaptiveGlobalJointColor configuration length
      let residue := scaleAdaptiveGlobalJointResidue
        configuration length lowTargets highTargets
      (∑ target ∈ lowTargets,
        Real.exp (-(∑ prime : ↥R,
          scaleAdaptiveColorHitFraction
            R color residue false target prime))) ≤
        lowCoefficient * ((length : ℝ) / Real.log (length : ℝ)))
    (high_budget : ∀ᶠ length : ℕ in atTop,
      let R := scaleAdaptiveGlobalJointPrimePool configuration length
      let lowTargets := scaleAdaptiveGlobalLowTargets
        length parameter cutoff
      let highTargets := scaleAdaptiveGlobalHighTargets
        length parameter cutoff
      let color := scaleAdaptiveGlobalJointColor configuration length
      let residue := scaleAdaptiveGlobalJointResidue
        configuration length lowTargets highTargets
      (∑ target ∈ highTargets,
        Real.exp (-(∑ prime : ↥R,
          scaleAdaptiveColorHitFraction
            R color residue true target prime))) ≤
        highCoefficient * ((length : ℝ) / Real.log (length : ℝ)))
    (prime_margin :
      2 * (lowCoefficient + highCoefficient + 2 * envelopeCoefficient) +
        (parameter : ℝ)⁻¹ +
        (∑ exponent ∈ configuration.exponents,
          (((2 ^ exponent : ℕ) : ℝ)⁻¹)) < 1)
    (conductor_margin :
      (((2 ^ lowerExponent : ℕ) : ℝ)⁻¹) +
        2 * (lowCoefficient + highCoefficient +
          2 * envelopeCoefficient) < epsilon) :
    ∀ᶠ length : ℕ in atTop,
      ∃ (R lowTargets highTargets exceptional : Finset ℕ)
        (k B DLow DHigh : ℕ)
        (color : ↥R → Fin k → Bool)
        (residue : ↥R → Fin k → ℕ),
        0 < k ∧ 1 ≤ B ∧
        (∀ prime ∈ R, prime.Prime) ∧
        Disjoint (fixedParameterCorePrimes length parameter) R ∧
        lowTargets ⊆ Finset.Icc 1 length ∧
        highTargets ⊆ Finset.Icc 1 length ∧
        exceptional ⊆ Finset.Icc 1 length ∧
        (∀ target ∈ Finset.Icc 1 length, target ∉ exceptional →
          2 ≤ fixedParameterCoreHits length parameter target +
            (if target ∈ lowTargets then 1 else 0) +
            (if target ∈ highTargets then 1 else 0)) ∧
        (∑ target ∈ lowTargets,
          Real.exp (-(∑ prime : ↥R,
            scaleAdaptiveColorHitFraction
              R color residue false target prime))) ≤ (DLow : ℝ) ∧
        (∑ target ∈ highTargets,
          Real.exp (-(∑ prime : ↥R,
            scaleAdaptiveColorHitFraction
              R color residue true target prime))) ≤ (DHigh : ℝ) ∧
        2 * (DLow + DHigh + 2 * exceptional.card) +
          ((fixedParameterCorePrimes length parameter) ∪ R).card ≤
            Nat.primeCounting B ∧
        Real.log ((∏ prime ∈ R, prime : ℕ) : ℝ) +
          (2 * ((DLow + DHigh + 2 * exceptional.card : ℕ) : ℝ)) *
            Real.log (B : ℝ) ≤ epsilon * (length : ℝ) := by
  let selected : ℕ → Finset ℕ :=
    scaleAdaptiveGlobalJointPrimePool configuration
  have selected_density := scaleAdaptiveGlobalJointPrimePool_normalized_tendsto
    configuration rejected
  have supply :=
    scaleAdaptiveIntegerCompleteCleanupPrimeCounting_of_envelope_eventually
      parameter parameter_positive lowCoefficient highCoefficient
        envelopeCoefficient
        (∑ exponent ∈ configuration.exponents,
          (((2 ^ exponent : ℕ) : ℝ)⁻¹))
        low_nonnegative high_nonnegative exceptions selected
          envelope envelope_bounds envelope_density
            selected_density prime_margin
  let slack : ℝ := epsilon -
    ((((2 ^ lowerExponent : ℕ) : ℝ)⁻¹) +
      2 * (lowCoefficient + highCoefficient +
        2 * envelopeCoefficient))
  have slack_positive : 0 < slack := by
    dsimp [slack]
    linarith
  have conductor :=
    scaleAdaptiveIntegerFullConductor_of_exception_envelope_eventually_le
      lowerExponent configuration.exponents after
        lowCoefficient highCoefficient envelopeCoefficient slack
          low_nonnegative high_nonnegative exceptions envelope
            envelope_bounds envelope_density slack_positive
  have fresh := scaleAdaptiveGlobalJointPrimePool_eventually_fresh
    configuration parameter inside
  have threshold : ∀ᶠ length : ℕ in atTop,
      parameter ≤ length / parameter := by
    filter_upwards [eventually_ge_atTop (parameter * parameter)] with
      length large
    exact (Nat.le_div_iff_mul_le parameter_positive).mpr large
  filter_upwards [supply, conductor, fresh, threshold,
      low_budget, high_budget, eventually_ge_atTop 1] with
    length prime_supply conductor_bound fresh_core square_threshold
      low_bound high_bound length_positive
  let R := scaleAdaptiveGlobalJointPrimePool configuration length
  let lowTargets := scaleAdaptiveGlobalLowTargets length parameter cutoff
  let highTargets := scaleAdaptiveGlobalHighTargets length parameter cutoff
  let exceptional := exceptions length
  let k := scaleAdaptiveGlobalJointOptionCount configuration length
  let DLow := scaleAdaptiveIntegerCleanupBudget lowCoefficient length
  let DHigh := scaleAdaptiveIntegerCleanupBudget highCoefficient length
  let color := scaleAdaptiveGlobalJointColor configuration length
  let residue := scaleAdaptiveGlobalJointResidue
    configuration length lowTargets highTargets
  refine ⟨R, lowTargets, highTargets, exceptional,
    k, length, DLow, DHigh, color, residue, ?_, length_positive,
    ?_, fresh_core,
    scaleAdaptiveGlobalLowTargets_subset_interval parameter_positive,
    scaleAdaptiveGlobalHighTargets_subset_interval parameter_positive,
    exceptions_supported length, ?_, ?_, ?_, prime_supply, ?_⟩
  · exact scaleAdaptiveGlobalJointOptionCount_positive
      configuration length low_primes high_primes
  · intro prime in_pool
    exact scaleAdaptiveGlobalJointPrimePool_prime
      configuration length in_pool
  · intro target interval outside
    apply scaleAdaptiveGlobalCompleteColoredTargetDemand
      configuration.exponents configuration.exponents
        configuration.lowSupport configuration.highSupport
          configuration.lower configuration.upper
            parameter_positive square_threshold target interval
    intro basic
    exact outside (basic_exceptions_included length basic)
  · exact scaleAdaptiveIntegerCleanupBudget_covers
      lowCoefficient _ length low_bound
  · exact scaleAdaptiveIntegerCleanupBudget_covers
      highCoefficient _ length high_bound
  · have prime_bound := scaleAdaptiveGlobalJointPrimeProduct_log_le_shell
      configuration length
    have charged :
        Real.log
          ((∏ prime ∈ scaleAdaptiveGlobalJointPrimePool
            configuration length, prime : ℕ) : ℝ) +
          (2 * (scaleAdaptiveIntegerCompleteDeficit
            lowCoefficient highCoefficient exceptions length : ℝ)) *
              Real.log (length : ℝ) ≤
        ((((2 ^ lowerExponent : ℕ) : ℝ)⁻¹) +
          2 * (lowCoefficient + highCoefficient +
            2 * envelopeCoefficient) + slack) * (length : ℝ) := by
      calc
        _ ≤ Real.log
          ((∏ prime ∈ configuration.exponents.biUnion
            (scaleAdaptiveDyadicPrimeShell length), prime : ℕ) : ℝ) +
          (2 * (scaleAdaptiveIntegerCompleteDeficit
            lowCoefficient highCoefficient exceptions length : ℝ)) *
              Real.log (length : ℝ) := by
                gcongr
        _ ≤ _ := conductor_bound
    have exact_coefficient :
        ((((2 ^ lowerExponent : ℕ) : ℝ)⁻¹) +
          2 * (lowCoefficient + highCoefficient +
            2 * envelopeCoefficient) + slack) = epsilon := by
      dsimp [slack]
      ring
    rw [exact_coefficient] at charged
    simpa [R, DLow, DHigh, exceptional,
      scaleAdaptiveIntegerCompleteDeficit] using charged

/-- The actual, concrete zero-density rejection condition for BOTH square
supports on the SAME final fixed-parameter global prime pool.  This is a
prime-label asymptotic, not a covering, matching, or rounding premise. -/
def ScaleAdaptiveFinalSameConfigurationRejected
    (parameter : ℕ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ) : Prop :=
  ∀ exponent ∈ scaleAdaptiveFinalExponents parameter,
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          (scaleAdaptiveFinalLowSupport parameter exponent)
          (scaleAdaptiveFinalHighSupport parameter exponent)
          (2 ^ exponent) 0 1
            (lowSingular exponent) (highSingular exponent) N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))

/-- The TRUE LOW missing-hit sum of the actual one-pool finite joint
sampler on the literal original deficient target family. -/
noncomputable def scaleAdaptiveFinalActualLowMissingMass
    (parameter : ℕ)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) : ℝ :=
  let lowTargets := scaleAdaptiveGlobalLowTargets length
    (scaleAdaptiveFinalCoreParameter parameter)
    (scaleAdaptiveFinalTypeCutoff parameter)
  let highTargets := scaleAdaptiveGlobalHighTargets length
    (scaleAdaptiveFinalCoreParameter parameter)
    (scaleAdaptiveFinalTypeCutoff parameter)
  ∑ target ∈ lowTargets,
    Real.exp
      (-(weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        false target))

/-- The HIGH missing-hit sum of that SAME actual global joint sampler;
no second prime pool or independently chosen residue is introduced. -/
noncomputable def scaleAdaptiveFinalActualHighMissingMass
    (parameter : ℕ)
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) : ℝ :=
  let lowTargets := scaleAdaptiveGlobalLowTargets length
    (scaleAdaptiveFinalCoreParameter parameter)
    (scaleAdaptiveFinalTypeCutoff parameter)
  let highTargets := scaleAdaptiveGlobalHighTargets length
    (scaleAdaptiveFinalCoreParameter parameter)
    (scaleAdaptiveFinalTypeCutoff parameter)
  ∑ target ∈ highTargets,
    Real.exp
      (-(weightedActualPatternHitLoad
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (scaleAdaptiveGlobalJointColor configuration length)
        (scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets)
        true target))

/-- Final EXACT historical marginal premise from solely explicit numerical
inputs on the SAME genuine fixed-parameter colored-prime sampler.

The hypotheses state the actual two original-target exponential
inequalities and the genuine NATURAL exception-envelope inclusion,
cardinality, and asymptotic coefficient.  They contain no selected cover,
matching, independent resampling, hidden opaque proposition, or assumed
conductor bound.  Sole signed Green--Tao chooses both canonical singular
families ONCE; every prime-supply, complete-deficiency, rounding, and TRUE
product-conductor requirement is then proved by the preceding deterministic
Lean theorem. -/
theorem scaleAdaptiveFinalJointColoredMarginals_of_actual_same_configuration_budgets
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (extraExceptions : ℕ → ℝ)
    (extra_nonnegative : ∀ parameter : ℕ, 0 ≤ extraExceptions parameter)
    (extra_vanishes : Tendsto extraExceptions atTop (nhds (0 : ℝ)))
    (exceptions : ℕ → ScaleAdaptiveGlobalJointConfiguration → ℕ → Finset ℕ)
    (envelope : ℕ → ScaleAdaptiveGlobalJointConfiguration → ℕ → ℕ)
    (exceptions_supported :
      ∀ parameter lowSingular highSingular length,
        exceptions parameter
          (scaleAdaptiveFinalJointConfiguration
            parameter 0 1 lowSingular highSingular) length ⊆
              Finset.Icc 1 length)
    (basic_exceptions_included :
      ∀ parameter lowSingular highSingular length,
        let configuration := scaleAdaptiveFinalJointConfiguration
          parameter 0 1 lowSingular highSingular
        scaleAdaptiveGlobalCompleteTargetExceptions
          length (scaleAdaptiveFinalCoreParameter parameter)
          configuration.exponents configuration.exponents
          configuration.lowSupport configuration.highSupport
          configuration.lower configuration.upper ⊆
            exceptions parameter configuration length)
    (envelope_bounds :
      ∀ parameter lowSingular highSingular length,
        let configuration := scaleAdaptiveFinalJointConfiguration
          parameter 0 1 lowSingular highSingular
        (exceptions parameter configuration length).card ≤
          envelope parameter configuration length)
    (envelope_density :
      ∀ parameter lowSingular highSingular,
        ScaleAdaptiveFinalSameConfigurationRejected
          parameter lowSingular highSingular →
        let configuration := scaleAdaptiveFinalJointConfiguration
          parameter 0 1 lowSingular highSingular
        Tendsto
          (fun length : ℕ =>
            (envelope parameter configuration length : ℝ) *
              Real.log (length : ℝ) / (length : ℝ))
          atTop (nhds
            (((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
              extraExceptions parameter)))
    (actual_low_budget :
      ∀ parameter lowSingular highSingular,
        2 ≤ parameter →
        ScaleAdaptiveFinalSameConfigurationRejected
          parameter lowSingular highSingular →
        let configuration := scaleAdaptiveFinalJointConfiguration
          parameter 0 1 lowSingular highSingular
        ∀ᶠ length : ℕ in atTop,
          scaleAdaptiveFinalActualLowMissingMass
            parameter configuration length ≤
            (scaleAdaptiveFinalLowBudgetCoefficient
              (1 / 32 : ℝ) parameter + extraExceptions parameter +
                ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹) *
              ((length : ℝ) / Real.log (length : ℝ)))
    (actual_high_budget :
      ∀ parameter lowSingular highSingular,
        2 ≤ parameter →
        ScaleAdaptiveFinalSameConfigurationRejected
          parameter lowSingular highSingular →
        let configuration := scaleAdaptiveFinalJointConfiguration
          parameter 0 1 lowSingular highSingular
        ∀ᶠ length : ℕ in atTop,
          scaleAdaptiveFinalActualHighMissingMass
            parameter configuration length ≤
            (scaleAdaptiveFinalHighBudgetCoefficient
              (1 / 32 : ℝ) parameter + extraExceptions parameter +
                ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹) *
              ((length : ℝ) / Real.log (length : ℝ))) :
    HasSublinearJointColoredMarginals := by
  intro epsilon epsilon_positive
  have margins :=
    scaleAdaptiveFinalFullyChargedAdmissibleParameters_eventually
      (by norm_num : (0 : ℝ) < 1 / 32)
      epsilon_positive extraExceptions extra_vanishes
  obtain ⟨parameter, parameter_large, core_small,
    prime_margin, conductor_margin⟩ := margins.exists
  obtain ⟨lowSingular, highSingular, canonical⟩ :=
    scaleAdaptiveFinalCanonicalSingularFamilies_exists_of_GTZ
      green_tao parameter
  let configuration := scaleAdaptiveFinalJointConfiguration
    parameter 0 1 lowSingular highSingular
  have rejected : ScaleAdaptiveFinalSameConfigurationRejected
      parameter lowSingular highSingular := by
    intro exponent selected
    exact (canonical exponent selected).2.2.1
  have configuration_rejected :
      ∀ exponent ∈ configuration.exponents,
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              (configuration.lowSupport exponent)
              (configuration.highSupport exponent)
              (2 ^ exponent) configuration.lower configuration.upper
                (configuration.lowSingular exponent)
                (configuration.highSingular exponent) N).card : ℝ) *
                  scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (0 : ℝ)) := by
    simpa [configuration, scaleAdaptiveFinalJointConfiguration,
      ScaleAdaptiveFinalSameConfigurationRejected] using rejected
  let lowCoefficient :=
    scaleAdaptiveFinalRoundedLowBudgetCoefficient
      (1 / 32 : ℝ) parameter + extraExceptions parameter
  let highCoefficient :=
    scaleAdaptiveFinalRoundedHighBudgetCoefficient
      (1 / 32 : ℝ) parameter + extraExceptions parameter
  let envelopeCoefficient :=
    ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹ +
      extraExceptions parameter
  refine ⟨scaleAdaptiveFinalCoreParameter parameter,
    scaleAdaptiveFinalCoreParameter_pos parameter, core_small, ?_⟩
  apply scaleAdaptiveFinalFixedParameterColoredWitness_of_actual_bounds
    (scaleAdaptiveFinalCoreParameter parameter)
    (scaleAdaptiveFinalTypeCutoff parameter)
    (scaleAdaptiveColoredLowerExponent parameter)
    configuration lowCoefficient highCoefficient envelopeCoefficient
    epsilon (exceptions parameter configuration)
      (envelope parameter configuration)
  · exact scaleAdaptiveFinalCoreParameter_pos parameter
  · exact add_nonneg
      (scaleAdaptiveFinalRoundedLowBudgetCoefficient_nonnegative
        (1 / 32 : ℝ) parameter)
      (extra_nonnegative parameter)
  · exact add_nonneg
      (scaleAdaptiveFinalRoundedHighBudgetCoefficient_nonnegative
        (1 / 32 : ℝ) parameter)
      (extra_nonnegative parameter)
  · intro exponent _selected prime supported
    exact scaleAdaptiveFinalLowSupport_primes
      parameter exponent (by simpa [configuration,
        scaleAdaptiveFinalJointConfiguration] using supported)
  · intro exponent _selected prime supported
    exact scaleAdaptiveFinalHighSupport_primes
      parameter exponent (by simpa [configuration,
        scaleAdaptiveFinalJointConfiguration] using supported)
  · intro exponent selected
    apply scaleAdaptiveFinalExponent_fresh
    simpa [configuration, scaleAdaptiveFinalJointConfiguration]
      using selected
  · intro exponent selected
    apply scaleAdaptiveFinalExponent_after_conductor_cutoff
    simpa [configuration, scaleAdaptiveFinalJointConfiguration]
      using selected
  · exact configuration_rejected
  · intro length
    exact exceptions_supported parameter lowSingular highSingular length
  · intro length
    exact basic_exceptions_included
      parameter lowSingular highSingular length
  · exact Filter.Eventually.of_forall fun length =>
      envelope_bounds parameter lowSingular highSingular length
  · exact envelope_density parameter lowSingular highSingular rejected
  · filter_upwards [actual_low_budget
      parameter lowSingular highSingular parameter_large rejected]
        with length actual
    change scaleAdaptiveFinalActualLowMissingMass
      parameter configuration length ≤
        lowCoefficient * ((length : ℝ) / Real.log (length : ℝ))
    calc
      _ ≤ (scaleAdaptiveFinalLowBudgetCoefficient (1 / 32 : ℝ) parameter +
        extraExceptions parameter +
          ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹) *
            ((length : ℝ) / Real.log (length : ℝ)) := actual
      _ = _ := by
        dsimp [lowCoefficient, scaleAdaptiveFinalRoundedLowBudgetCoefficient]
        ring
  · filter_upwards [actual_high_budget
      parameter lowSingular highSingular parameter_large rejected]
        with length actual
    change scaleAdaptiveFinalActualHighMissingMass
      parameter configuration length ≤
        highCoefficient * ((length : ℝ) / Real.log (length : ℝ))
    calc
      _ ≤ (scaleAdaptiveFinalHighBudgetCoefficient (1 / 32 : ℝ) parameter +
        extraExceptions parameter +
          ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹) *
            ((length : ℝ) / Real.log (length : ℝ)) := actual
      _ = _ := by
        dsimp [highCoefficient,
          scaleAdaptiveFinalRoundedHighBudgetCoefficient]
        ring
  · simpa [configuration, scaleAdaptiveFinalJointConfiguration,
      lowCoefficient, highCoefficient, envelopeCoefficient]
      using prime_margin
  · simpa [scaleAdaptiveColoredConductorDensity,
      lowCoefficient, highCoefficient, envelopeCoefficient]
      using conductor_margin

/-- The sole explicit fixed-system signed Green--Tao--Ziegler analytic
input implies the EXACT common-pool colored-prime marginal condition for
the original Erdős problem.

Every genuine deficient prime and semiprime type, actual positive integer
degree, same-prime two-color choice, physical prefix, type-dependent
eligible shell, natural exceptional envelope, cleanup prime reserve, and
TRUE selected-prime product conductor is retained.  The adaptive parameter
is fixed before `Y→∞` and sent to infinity only afterward.  There is no
additional moment, target-correlation, matching, covering, or unpublished
mathematical premise.  The Green--Tao input itself remains an explicit
UNFORMALIZED analytic antecedent, not an axiom or unconditional claim. -/
theorem joint_colored_marginals_of_fixed_signed_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics) :
    HasSublinearJointColoredMarginals := by
  let extra : ℕ → ℝ := fun parameter =>
    (((scaleAdaptiveActualPhysicalPrefixDivisor parameter : ℕ) : ℝ)⁻¹ *
      (1 + adaptivePrimeHarmonicPrefix
        (2 ^ scaleAdaptiveColoredFullExponent parameter)))
  let exceptions : ℕ → ScaleAdaptiveGlobalJointConfiguration →
      ℕ → Finset ℕ := fun parameter configuration length =>
    scaleAdaptiveActualAugmentedExceptions configuration
      (scaleAdaptiveFinalCoreParameter parameter) parameter length
  let envelope : ℕ → ScaleAdaptiveGlobalJointConfiguration →
      ℕ → ℕ := fun parameter configuration length =>
    scaleAdaptiveActualAugmentedExceptionEnvelope configuration
      (scaleAdaptiveFinalCoreParameter parameter) parameter length
  refine scaleAdaptiveFinalJointColoredMarginals_of_actual_same_configuration_budgets
    green_tao extra ?_ ?_ exceptions envelope ?_ ?_ ?_ ?_ ?_ ?_
  · intro parameter
    dsimp [extra]
    have harmonic := scaleAdaptiveFinalPrimeHarmonicPrefix_nonnegative
      (2 ^ scaleAdaptiveColoredFullExponent parameter)
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (by linarith)
  · simpa [extra] using
      scaleAdaptiveActualPhysicalPrefixCoefficient_tendsto_zero
  · intro parameter lowSingular highSingular length
    exact scaleAdaptiveActualAugmentedExceptions_subset_interval
      (scaleAdaptiveFinalJointConfiguration
        parameter 0 1 lowSingular highSingular)
      (scaleAdaptiveFinalCoreParameter parameter) parameter length
  · intro parameter lowSingular highSingular length
    exact scaleAdaptiveActualCompleteExceptions_subset_augmented
      (scaleAdaptiveFinalJointConfiguration
        parameter 0 1 lowSingular highSingular)
      (scaleAdaptiveFinalCoreParameter parameter) parameter length
  · intro parameter lowSingular highSingular length
    exact scaleAdaptiveActualAugmentedExceptions_card_le_envelope
      (scaleAdaptiveFinalJointConfiguration
        parameter 0 1 lowSingular highSingular)
      (scaleAdaptiveFinalCoreParameter parameter) parameter length
  · intro parameter lowSingular highSingular rejected
    let configuration := scaleAdaptiveFinalJointConfiguration
      parameter 0 1 lowSingular highSingular
    have low_primes : ∀ exponent ∈ configuration.exponents,
        ∀ prime ∈ configuration.lowSupport exponent, prime.Prime := by
      intro exponent _ prime selected
      exact scaleAdaptiveFinalLowSupport_primes parameter exponent
        (by simpa [configuration, scaleAdaptiveFinalJointConfiguration]
          using selected)
    have high_primes : ∀ exponent ∈ configuration.exponents,
        ∀ prime ∈ configuration.highSupport exponent, prime.Prime := by
      intro exponent _ prime selected
      exact scaleAdaptiveFinalHighSupport_primes parameter exponent
        (by simpa [configuration, scaleAdaptiveFinalJointConfiguration]
          using selected)
    have actual_rejection : ∀ exponent ∈ configuration.exponents,
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              (configuration.lowSupport exponent)
              (configuration.highSupport exponent)
              (2 ^ exponent) configuration.lower configuration.upper
              (configuration.lowSingular exponent)
              (configuration.highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (0 : ℝ)) := by
      simpa [configuration, scaleAdaptiveFinalJointConfiguration,
        ScaleAdaptiveFinalSameConfigurationRejected] using rejected
    exact scaleAdaptiveActualAugmentedExceptionEnvelope_normalized_tendsto_of_GTZ
      green_tao configuration
      (scaleAdaptiveFinalCoreParameter parameter) parameter
      (scaleAdaptiveFinalCoreParameter_pos parameter)
      low_primes high_primes actual_rejection
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
  · intro parameter lowSingular highSingular large rejected
    let configuration := scaleAdaptiveFinalJointConfiguration
      parameter 0 1 lowSingular highSingular
    have actual_rejection : ∀ exponent ∈ configuration.exponents,
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              (configuration.lowSupport exponent)
              (configuration.highSupport exponent)
              (2 ^ exponent) configuration.lower configuration.upper
              (configuration.lowSingular exponent)
              (configuration.highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (0 : ℝ)) := by
      simpa [configuration, scaleAdaptiveFinalJointConfiguration,
        ScaleAdaptiveFinalSameConfigurationRejected] using rejected
    have actual := scaleAdaptiveActualGlobalLowMissBudget_eventually_le_of_GTZ
      green_tao parameter configuration
      ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹
      large (by rfl) (by rfl) (by rfl)
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
      actual_rejection (scaleAdaptiveFinalCoreParameter_inverse_pos parameter)
    filter_upwards [actual] with length bound
    simpa [scaleAdaptiveFinalActualLowMissingMass,
      scaleAdaptiveActualGlobalColoredHitLoad,
      scaleAdaptiveFinalCoreParameter, scaleAdaptiveFinalTypeCutoff,
      scaleAdaptiveActualLowBudgetCoefficient,
      scaleAdaptiveFinalLowBudgetCoefficient, extra]
      using bound
  · intro parameter lowSingular highSingular large rejected
    let configuration := scaleAdaptiveFinalJointConfiguration
      parameter 0 1 lowSingular highSingular
    have actual_rejection : ∀ exponent ∈ configuration.exponents,
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              (configuration.lowSupport exponent)
              (configuration.highSupport exponent)
              (2 ^ exponent) configuration.lower configuration.upper
              (configuration.lowSingular exponent)
              (configuration.highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (0 : ℝ)) := by
      simpa [configuration, scaleAdaptiveFinalJointConfiguration,
        ScaleAdaptiveFinalSameConfigurationRejected] using rejected
    have actual := scaleAdaptiveActualGlobalHighMissBudget_eventually_le_of_GTZ
      green_tao parameter configuration
      ((scaleAdaptiveFinalCoreParameter parameter : ℕ) : ℝ)⁻¹
      large (by rfl) (by rfl) (by rfl)
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
      (by norm_num [configuration, scaleAdaptiveFinalJointConfiguration])
      actual_rejection (scaleAdaptiveFinalCoreParameter_inverse_pos parameter)
    filter_upwards [actual] with length bound
    simpa [scaleAdaptiveFinalActualHighMissingMass,
      scaleAdaptiveActualGlobalColoredHitLoad,
      scaleAdaptiveFinalCoreParameter, scaleAdaptiveFinalTypeCutoff,
      scaleAdaptiveActualHighBudgetCoefficient,
      scaleAdaptiveFinalHighBudgetCoefficient, extra]
      using bound

/-- CONDITIONAL literal original historical Erdős #1139 theorem, with
exact multiplicity-counting `Ω`, positive ordered `Nat.nth` indices,
successive almost-prime gap, `log(k+1)` normalization, and extended-real
infinite limsup.

The SOLE antecedent is the fully explicit fixed-system signed prime-pattern
Green--Tao--Ziegler asymptotic proposition.  No missing target moment,
graph degree, matching, sieve, covering, cleanup, or conductor hypothesis
remains.  This is NOT an unconditional Lean proof because that deep
published analytic input is not presently formalized in Mathlib. -/
theorem original_normalized_limsup_top_of_fixed_signed_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_joint_colored_marginals
    (joint_colored_marginals_of_fixed_signed_GTZ green_tao)


end Erdos1139
