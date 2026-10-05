module

public import ScaleAdaptiveGlobalExponentialBudgets1139
public import ScaleAdaptiveGlobalTypedTargetClassification1139

@[expose] public section


/-!
# Exact final physical shell and support identities for Erdős #1139

The full global sampler, its shorter high-color shell family, and every
low semiprime type's genuinely eligible shell family must use the same
actual dyadic exponents.  These identities expose their exact inclusions,
true prime supports, physical-prefix cutoff, and source-faithful Euler
masses without importing either active final-assembly module.

Every adaptive parameter remains fixed before the original target-length
limit.  No prime-pattern estimate, rounding premise, or covering theorem
is assumed here.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- The entire genuine global physical prime-shell family. -/
def scaleAdaptiveFinalShellFullExponents (parameter : ℕ) : Finset ℕ :=
  Finset.Ioc (scaleAdaptiveColoredLowerExponent parameter)
    (scaleAdaptiveColoredFullExponent parameter)

/-- The true shorter high-color amplification family. -/
def scaleAdaptiveFinalShellShortExponents (parameter : ℕ) : Finset ℕ :=
  Finset.Ioc (scaleAdaptiveColoredLowerExponent parameter)
    (scaleAdaptiveColoredSplitExponent parameter)

/-- Each low type has its OWN physically eligible exponent subfamily. -/
def scaleAdaptiveFinalShellEligibleExponents
    (parameter targetType : ℕ) : Finset ℕ :=
  scaleAdaptiveGlobalLowEligibleExponents targetType
    (scaleAdaptiveColoredLowerExponent parameter)
    (scaleAdaptiveColoredFullExponent parameter)

/-- The genuine scale-dependent LOW prime support. -/
def scaleAdaptiveFinalShellLowSupport
    (parameter exponent : ℕ) : Finset ℕ :=
  adaptiveLowPrimeSupport (2 ^ exponent)
    (2 ^ scaleAdaptiveColoredSplitExponent parameter)

/-- The genuine fixed complementary HIGH prime support. -/
def scaleAdaptiveFinalShellHighSupport
    (parameter _exponent : ℕ) : Finset ℕ :=
  adaptiveHighPrimeSupport
    (2 ^ scaleAdaptiveColoredFullExponent parameter)
    (2 ^ scaleAdaptiveColoredSplitExponent parameter)

/-- The actual short HIGH family never introduces a new shell or label. -/
theorem scaleAdaptiveFinalShellShortExponents_subset_full
    {parameter : ℕ} (large : 2 ≤ parameter) :
    scaleAdaptiveFinalShellShortExponents parameter ⊆
      scaleAdaptiveFinalShellFullExponents parameter := by
  intro exponent selected
  have bounds := Finset.mem_Ioc.mp selected
  apply Finset.mem_Ioc.mpr
  exact ⟨bounds.1,
    bounds.2.trans (scaleAdaptiveColoredExponent_order large).2⟩

/-- Every actual eligible low-type family is a subfamily of the ONE full
global sampler; ineligible early shells are genuinely absent. -/
theorem scaleAdaptiveFinalShellEligibleExponents_subset_full
    (parameter targetType : ℕ) :
    scaleAdaptiveFinalShellEligibleExponents parameter targetType ⊆
      scaleAdaptiveFinalShellFullExponents parameter := by
  intro exponent selected
  exact (Finset.mem_filter.mp selected).1

/-- Exact type-dependent shell eligibility, preserving both physical
endpoints and the true inequality `s ≤ 2^j`. -/
theorem mem_scaleAdaptiveFinalShellEligibleExponents
    {parameter targetType exponent : ℕ} :
    exponent ∈
        scaleAdaptiveFinalShellEligibleExponents parameter targetType ↔
      scaleAdaptiveColoredLowerExponent parameter < exponent ∧
        exponent ≤ scaleAdaptiveColoredFullExponent parameter ∧
          targetType ≤ 2 ^ exponent := by
  unfold scaleAdaptiveFinalShellEligibleExponents
    scaleAdaptiveGlobalLowEligibleExponents
  simp [Finset.mem_Ioc, and_assoc]

/-- Every LOW support element is a genuine prime. -/
theorem scaleAdaptiveFinalShellLowSupport_prime
    (parameter exponent : ℕ) {prime : ℕ}
    (selected : prime ∈
      scaleAdaptiveFinalShellLowSupport parameter exponent) :
    prime.Prime := by
  exact (mem_adaptiveLowPrimeSupport.mp selected).1

/-- Every HIGH support element is a genuine prime. -/
theorem scaleAdaptiveFinalShellHighSupport_prime
    (parameter exponent : ℕ) {prime : ℕ}
    (selected : prime ∈
      scaleAdaptiveFinalShellHighSupport parameter exponent) :
    prime.Prime := by
  exact (mem_adaptiveHighPrimeSupport.mp selected).1

/-- A genuine low type appears on EVERY shell in its OWN eligible family;
no unsupported late type is inserted into the shorter physical scales. -/
theorem scaleAdaptiveFinalShellEligibleType_mem_lowSupport
    {parameter targetType exponent : ℕ}
    (type_prime : targetType.Prime)
    (below_split : targetType ≤
      2 ^ scaleAdaptiveColoredSplitExponent parameter)
    (eligible : exponent ∈
      scaleAdaptiveFinalShellEligibleExponents parameter targetType) :
    targetType ∈ scaleAdaptiveFinalShellLowSupport parameter exponent := by
  apply mem_adaptiveLowPrimeSupport.mpr
  refine ⟨type_prime, ?_, below_split⟩
  exact (mem_scaleAdaptiveFinalShellEligibleExponents.mp eligible).2.2

/-- Every true high deficient prime type occurs on EVERY high shell,
including the shorter amplification subfamily. -/
theorem scaleAdaptiveFinalShellHighType_mem_highSupport
    {parameter targetType : ℕ} (exponent : ℕ)
    (type_prime : targetType.Prime)
    (above_split :
      2 ^ scaleAdaptiveColoredSplitExponent parameter < targetType)
    (below_full : targetType ≤
      2 ^ scaleAdaptiveColoredFullExponent parameter) :
    targetType ∈
      scaleAdaptiveFinalShellHighSupport parameter exponent := by
  exact mem_adaptiveHighPrimeSupport.mpr
    ⟨type_prime, above_split, below_full⟩

/-- The real fixed-parameter physical prefix is bounded on EVERY selected
shell; it has nonzero fixed-parameter density and cannot be discarded. -/
theorem scaleAdaptiveFinalShellPhysicalPrefix_factor_le
    {parameter exponent : ℕ}
    (selected : exponent ∈
      scaleAdaptiveFinalShellFullExponents parameter) :
    4 * 2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1) ≤
      2 ^ exponent := by
  have lower_positive : 0 < scaleAdaptiveColoredLowerExponent parameter := by
    unfold scaleAdaptiveColoredLowerExponent
    positivity
  have exponent_bound :
      scaleAdaptiveColoredLowerExponent parameter + 1 ≤ exponent := by
    exact (Finset.mem_Ioc.mp selected).1
  calc
    4 * 2 ^ (scaleAdaptiveColoredLowerExponent parameter - 1) =
        2 ^ ((scaleAdaptiveColoredLowerExponent parameter - 1) + 2) := by
          simp [pow_add, Nat.mul_comm]
    _ = 2 ^ (scaleAdaptiveColoredLowerExponent parameter + 1) := by
          congr 1
          omega
    _ ≤ 2 ^ exponent :=
          Nat.pow_le_pow_right (by norm_num) exponent_bound

/-- Exact full-family LOW Euler mass: EVERY actual shell contributes its
true physical factor, even when the low support has already saturated. -/
theorem scaleAdaptiveFinalShellLowFullEulerSum_eq
    (parameter : ℕ) :
    (∑ exponent ∈ scaleAdaptiveFinalShellFullExponents parameter,
      adaptivePatternEulerFactor
        (scaleAdaptiveFinalShellLowSupport parameter exponent)
        (2 ^ exponent)) =
      scaleAdaptiveDyadicEulerShellMass
        (scaleAdaptiveColoredLowerExponent parameter)
        (scaleAdaptiveColoredFullExponent parameter) := by
  unfold scaleAdaptiveFinalShellFullExponents
    scaleAdaptiveFinalShellLowSupport scaleAdaptiveDyadicEulerShellMass
  apply Finset.sum_congr rfl
  intro exponent _selected
  exact scaleAdaptiveLowDyadicPatternEulerFactor_eq
    exponent (2 ^ scaleAdaptiveColoredSplitExponent parameter)

/-- Exact low-type Euler mass on its OWN genuinely eligible shell tail;
the type prime condition and true split cutoff are indispensable. -/
theorem scaleAdaptiveFinalShellLowEligibleEulerSum_eq
    {parameter targetType : ℕ}
    (type_prime : targetType.Prime)
    (below_split : targetType ≤
      2 ^ scaleAdaptiveColoredSplitExponent parameter) :
    (∑ exponent ∈
      scaleAdaptiveFinalShellEligibleExponents parameter targetType,
        adaptivePatternEulerFactor
          (scaleAdaptiveFinalShellLowSupport parameter exponent)
          (2 ^ exponent)) =
      scaleAdaptiveLowEligibleDyadicEulerShell
        targetType (2 ^ scaleAdaptiveColoredSplitExponent parameter)
          (scaleAdaptiveColoredLowerExponent parameter)
          (scaleAdaptiveColoredFullExponent parameter) := by
  exact scaleAdaptiveGlobalLowEligibleEulerSum_eq targetType
    (scaleAdaptiveColoredLowerExponent parameter)
    (scaleAdaptiveColoredFullExponent parameter)
    (2 ^ scaleAdaptiveColoredSplitExponent parameter)
    type_prime below_split

/-- Exact actual high-color Euler mass on its shorter physical shell
subfamily, retaining the genuine full/split support ratio. -/
theorem scaleAdaptiveFinalShellHighShortEulerSum_eq
    (parameter : ℕ) :
    (∑ exponent ∈ scaleAdaptiveFinalShellShortExponents parameter,
      adaptivePatternEulerFactor
        (scaleAdaptiveFinalShellHighSupport parameter exponent)
        (2 ^ exponent)) =
      scaleAdaptiveHighDyadicEulerShellMass
        (scaleAdaptiveColoredFullExponent parameter)
        (scaleAdaptiveColoredSplitExponent parameter)
        (scaleAdaptiveColoredLowerExponent parameter)
        (scaleAdaptiveColoredSplitExponent parameter) := by
  rfl

/-- Exact actual high-color Euler mass on the complete physical shell
family, useful when the genuine high support is retained at all scales. -/
theorem scaleAdaptiveFinalShellHighFullEulerSum_eq
    (parameter : ℕ) :
    (∑ exponent ∈ scaleAdaptiveFinalShellFullExponents parameter,
      adaptivePatternEulerFactor
        (scaleAdaptiveFinalShellHighSupport parameter exponent)
        (2 ^ exponent)) =
      scaleAdaptiveHighDyadicEulerShellMass
        (scaleAdaptiveColoredFullExponent parameter)
        (scaleAdaptiveColoredSplitExponent parameter)
        (scaleAdaptiveColoredLowerExponent parameter)
        (scaleAdaptiveColoredFullExponent parameter) := by
  rfl


end Erdos1139
