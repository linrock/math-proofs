module

public import ScaleAdaptiveGlobalRestrictedMarginalIdentity1139
public import ScaleAdaptiveGlobalJointOptionAssembly1139

@[expose] public section


/-!
# Genuine common-prime restricted multiscale target loads

The true Euler factor of a signed mixed shell may decay as its fixed
complexity increases.  Its common-prime deletion tolerance must therefore be
chosen relative to that PARTICULAR factor and its actual physical rank:

    ε_j = F_j / (16 * 2^j).

For every fixed finite shell family, the resulting whole-outcome deletions
remain `o(Y/log Y)` at the ORIGINAL interval length.  Outside their finite
union, both prime and supported semiprime target loads retain at least
`Σ_j F_j/16` after restricting to the ONE common low/high prime pool at each
genuine dyadic shell.

All complexity parameters are fixed before `Y → ∞`.  No uniform positive
Euler factor, covering theorem, independent resampling, or unproved target
marginal is inserted.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1200000

/-- The true moving physical target window for ONE genuine dyadic shell;
its `2*T*N` upper endpoint dominates the original interval when `T ≤ N`. -/
def scaleAdaptiveRestrictedShellAmbientTargets
    (scale N : ℕ) : Finset ℕ :=
  Finset.range (2 * scale * N + 1)

/-- Every target in the ORIGINAL interval belongs to the actual shell
target window once the genuine dyadic pattern scale is at most its
floored physical prime-label scale. -/
theorem scaleAdaptiveRestrictedShellAmbientTargets_mem
    {length exponent target : ℕ}
    (scale_large : 2 ^ exponent ≤ length / 2 ^ exponent)
    (target_high : target ≤ length) :
    target ∈ scaleAdaptiveRestrictedShellAmbientTargets
      (2 ^ exponent) (length / 2 ^ exponent) := by
  have positive : 0 < (2 : ℕ) ^ exponent := by positivity
  have quotient_positive : 0 < length / 2 ^ exponent :=
    lt_of_lt_of_le positive scale_large
  have remainder_small : length % 2 ^ exponent < 2 ^ exponent :=
    Nat.mod_lt length positive
  have decomposition :
      length = length % 2 ^ exponent +
        2 ^ exponent * (length / 2 ^ exponent) := by
    exact (Nat.mod_add_div length (2 ^ exponent)).symm
  have factor_le :
      2 ^ exponent ≤ 2 ^ exponent * (length / 2 ^ exponent) := by
    exact Nat.le_mul_of_pos_right _ quotient_positive
  unfold scaleAdaptiveRestrictedShellAmbientTargets
  apply Finset.mem_range.mpr
  have regroup :
      2 * 2 ^ exponent * (length / 2 ^ exponent) =
        2 * (2 ^ exponent * (length / 2 ^ exponent)) := by ring
  rw [regroup]
  omega

/-- The HONEST shell-dependent deletion tolerance: one sixteenth of the
actual Euler factor divided by its true physical rank bound. -/
noncomputable def scaleAdaptiveRestrictedShellLossCutoff
    (support : Finset ℕ) (exponent : ℕ) : ℝ :=
  adaptivePatternEulerFactor support (2 ^ exponent) /
    (16 * ((2 ^ exponent : ℕ) : ℝ))

/-- Every genuine finite prime-support shell has strictly positive
cutoff, however small its actual Euler factor may be. -/
theorem scaleAdaptiveRestrictedShellLossCutoff_pos
    (support : Finset ℕ) (exponent : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    0 < scaleAdaptiveRestrictedShellLossCutoff support exponent := by
  unfold scaleAdaptiveRestrictedShellLossCutoff
  exact div_pos
    (scaleAdaptiveBandPatternEulerFactor_pos
      support (2 ^ exponent) primes)
    (mul_pos (by norm_num) (by positivity))

/-- Multiplying the real deletion tolerance by the TRUE physical rank
gives exactly `F_j/16`, with no uniform-in-complexity lower bound. -/
theorem scaleAdaptiveRestrictedShellLossCutoff_mul_rank
    (support : Finset ℕ) (exponent : ℕ) :
    ((2 ^ exponent : ℕ) : ℝ) *
      scaleAdaptiveRestrictedShellLossCutoff support exponent =
        adaptivePatternEulerFactor support (2 ^ exponent) / 16 := by
  unfold scaleAdaptiveRestrictedShellLossCutoff
  have nonzero : ((2 ^ exponent : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- The genuine finite UNION of whole-outcome cross-support deletions,
with the actual per-shell Euler/rank tolerance and ORIGINAL floored scale. -/
noncomputable def scaleAdaptiveRestrictedMultiShellCrossBadTargets
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (length : ℕ) : Finset ℕ :=
  exponents.biUnion fun exponent =>
    scaleAdaptiveSignedCrossRejectedFamilyBadTargets
      (familySupport exponent)
      (lowSupport exponent) (highSupport exponent)
      (2 ^ exponent)
      (adaptiveMixedOutcomeSpace
        (familySupport exponent) (2 ^ exponent))
      lower upper
      (scaleAdaptiveRestrictedShellLossCutoff
        (familySupport exponent) exponent)
      (lowSingular exponent) (highSingular exponent)
      (length / 2 ^ exponent)
      (scaleAdaptiveRestrictedShellAmbientTargets
        (2 ^ exponent) (length / 2 ^ exponent))

/-- The entire genuine multiscale cross-support deletion is
`o(Y/log Y)` at ORIGINAL interval length.  Each tiny Euler-dependent
tolerance is fixed BEFORE its corresponding physical limit. -/
theorem scaleAdaptiveRestrictedMultiShellCrossBadTargets_tendsto_zero
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ familySupport exponent, prime.Prime)
    (rejected : ∀ exponent ∈ exponents,
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            (lowSupport exponent) (highSupport exponent)
            (2 ^ exponent) lower upper
              (lowSingular exponent) (highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveRestrictedMultiShellCrossBadTargets
          exponents familySupport lowSupport highSupport
            lower upper lowSingular highSingular length).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  let bad : ℕ → ℕ → Finset ℕ := fun exponent N =>
    scaleAdaptiveSignedCrossRejectedFamilyBadTargets
      (familySupport exponent)
      (lowSupport exponent) (highSupport exponent)
      (2 ^ exponent)
      (adaptiveMixedOutcomeSpace
        (familySupport exponent) (2 ^ exponent))
      lower upper
      (scaleAdaptiveRestrictedShellLossCutoff
        (familySupport exponent) exponent)
      (lowSingular exponent) (highSingular exponent)
      N (scaleAdaptiveRestrictedShellAmbientTargets (2 ^ exponent) N)
  have individual : ∀ exponent ∈ exponents,
      Tendsto
        (fun N : ℕ =>
          ((bad exponent N).card : ℝ) *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) := by
    intro exponent selected
    exact scaleAdaptiveSignedCrossRejectedFamilyBadTargets_tendsto_zero
      (familySupport exponent)
      (lowSupport exponent) (highSupport exponent)
      (2 ^ exponent)
      (adaptiveMixedOutcomeSpace
        (familySupport exponent) (2 ^ exponent))
      lower upper
      (scaleAdaptiveRestrictedShellLossCutoff
        (familySupport exponent) exponent)
      (lowSingular exponent) (highSingular exponent)
      (scaleAdaptiveRestrictedShellAmbientTargets (2 ^ exponent))
      (scaleAdaptiveRestrictedShellLossCutoff_pos
        (familySupport exponent) exponent (primes exponent selected))
      (rejected exponent selected)
  exact scaleAdaptiveFiniteDyadicBadUnion_global_tendsto_zero
    exponents id bad individual

/-- Complete actual PRIME-target exceptions after common-prime
restriction: old outcome/cell/boundary failures plus true cross-loss
deletions from all fixed physical shells. -/
noncomputable def scaleAdaptiveRestrictedMultiShellPrimeExceptions
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (length : ℕ) : Finset ℕ :=
  scaleAdaptiveMultiShellPrimeExceptions
    exponents familySupport lower upper length ∪
  scaleAdaptiveRestrictedMultiShellCrossBadTargets
    exponents familySupport lowSupport highSupport
      lower upper lowSingular highSingular length

/-- Complete actual supported-SEMIPRIME-target exceptions after the
same genuine common low/high prime-pool restriction. -/
noncomputable def scaleAdaptiveRestrictedMultiShellSemiprimeExceptions
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (length : ℕ) : Finset ℕ :=
  scaleAdaptiveMultiShellSemiprimeExceptions
    exponents familySupport targetType lower upper length ∪
  scaleAdaptiveRestrictedMultiShellCrossBadTargets
    exponents familySupport lowSupport highSupport
      lower upper lowSingular highSingular length

/-- The COMPLETE restricted prime-target exceptional union remains
`o(Y/log Y)` at original length directly from signed Green--Tao and the
actual common-prime rejection densities. -/
theorem scaleAdaptiveRestrictedMultiShellPrimeExceptions_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ familySupport exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (rejected : ∀ exponent ∈ exponents,
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            (lowSupport exponent) (highSupport exponent)
            (2 ^ exponent) lower upper
              (lowSingular exponent) (highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveRestrictedMultiShellPrimeExceptions
          exponents familySupport lowSupport highSupport lower upper
            lowSingular highSingular length).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  exact scaleAdaptiveTwoBadTargetUnions_global_tendsto_zero
    (scaleAdaptiveMultiShellPrimeExceptions
      exponents familySupport lower upper)
    (scaleAdaptiveRestrictedMultiShellCrossBadTargets
      exponents familySupport lowSupport highSupport
        lower upper lowSingular highSingular)
    (scaleAdaptiveMultiShellPrimeExceptions_global_tendsto_zero_of_GTZ
      green_tao exponents familySupport lower upper primes
        lower_nonnegative band_nonempty upper_bounded)
    (scaleAdaptiveRestrictedMultiShellCrossBadTargets_tendsto_zero
      exponents familySupport lowSupport highSupport lower upper
        lowSingular highSingular primes rejected)

/-- The COMPLETE restricted genuine type-`s` semiprime exceptional union
likewise has zero ORIGINAL prime-target density. -/
theorem scaleAdaptiveRestrictedMultiShellSemiprimeExceptions_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ familySupport exponent, prime.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ familySupport exponent)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1)
    (rejected : ∀ exponent ∈ exponents,
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            (lowSupport exponent) (highSupport exponent)
            (2 ^ exponent) lower upper
              (lowSingular exponent) (highSingular exponent) N).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveRestrictedMultiShellSemiprimeExceptions
          exponents familySupport lowSupport highSupport
            targetType lower upper lowSingular highSingular length).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  exact scaleAdaptiveTwoBadTargetUnions_global_tendsto_zero
    (scaleAdaptiveMultiShellSemiprimeExceptions
      exponents familySupport targetType lower upper)
    (scaleAdaptiveRestrictedMultiShellCrossBadTargets
      exponents familySupport lowSupport highSupport
        lower upper lowSingular highSingular)
    (scaleAdaptiveMultiShellSemiprimeExceptions_global_tendsto_zero_of_GTZ
      green_tao exponents familySupport targetType lower upper primes
        type_supported lower_nonnegative band_nonempty upper_bounded)
    (scaleAdaptiveRestrictedMultiShellCrossBadTargets_tendsto_zero
      exponents familySupport lowSupport highSupport lower upper
        lowSingular highSingular primes rejected)

/-- ACTUAL prime-target multiscale load after restriction to the genuine
common low/high label pool of EACH disjoint physical dyadic shell. -/
noncomputable def scaleAdaptiveRestrictedMultiShellPrimeActualLoad
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (length target : ℕ) : ℝ :=
  ∑ exponent ∈ exponents,
    scaleAdaptiveBandPrimeOutcomeLoad
      (familySupport exponent) (2 ^ exponent)
      (scaleAdaptiveMultiShellTargetCell length exponent target)
      (fun index outcome target =>
        scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
          (familySupport exponent)
          (lowSupport exponent) (highSupport exponent)
          (2 ^ exponent) outcome lower upper
          (lowSingular exponent) (highSingular exponent)
          index (length / 2 ^ exponent) target)
      target

/-- ACTUAL type-`s` semiprime-target multiscale load on the SAME genuine
common prime pools, retaining eligibility and inverse integer degrees. -/
noncomputable def scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (length target : ℕ) : ℝ :=
  ∑ exponent ∈ exponents,
    scaleAdaptiveBandSemiprimeOutcomeLoad
      (familySupport exponent) targetType (2 ^ exponent)
      (scaleAdaptiveMultiShellTargetCell length exponent target)
      (fun index outcome target =>
        scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
          (familySupport exponent)
          (lowSupport exponent) (highSupport exponent)
          (2 ^ exponent) outcome lower upper
          (lowSingular exponent) (highSingular exponent)
          index (length / 2 ^ exponent) target)
      target

/-- A genuine PRIME target retains at least ONE SIXTEENTH of the SUM of
its actual shell Euler factors after restriction to the same low/high
prime pool at each true physical shell.  Every target exception is explicit. -/
theorem scaleAdaptiveRestrictedMultiShellPrimeActualLoad_ge_euler_sum
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (length target : ℕ)
    (primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ familySupport exponent, prime.Prime)
    (target_prime : target.Prime)
    (target_high : target ≤ length)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ exponents,
      4 * (length / 2 ^ exponent) ≤ target)
    (not_exception : target ∉
      scaleAdaptiveRestrictedMultiShellPrimeExceptions
        exponents familySupport lowSupport highSupport lower upper
          lowSingular highSingular length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (familySupport exponent) (2 ^ exponent)) / 16 ≤
      scaleAdaptiveRestrictedMultiShellPrimeActualLoad
        exponents familySupport lowSupport highSupport lower upper
          lowSingular highSingular length target := by
  have old_good : target ∉
      scaleAdaptiveMultiShellPrimeExceptions
        exponents familySupport lower upper length := by
    intro bad
    exact not_exception (Finset.mem_union_left _ bad)
  have cross_good : target ∉
      scaleAdaptiveRestrictedMultiShellCrossBadTargets
        exponents familySupport lowSupport highSupport
          lower upper lowSingular highSingular length := by
    intro bad
    exact not_exception (Finset.mem_union_right _ bad)
  have boundary_good : target ∉
      scaleAdaptiveMultiShellBoundaryTargets exponents length := by
    intro bad
    exact old_good (Finset.mem_union_right _ bad)
  have original :=
    scaleAdaptiveMultiShellPrimeActualLoad_ge_euler_sum_of_good_target
      exponents familySupport lower upper length target primes
        target_prime target_high scales_large target_interior old_good
  have preserved :
      scaleAdaptiveMultiShellPrimeActualLoad
        exponents familySupport lower upper length target -
          (∑ exponent ∈ exponents,
            adaptivePatternEulerFactor
              (familySupport exponent) (2 ^ exponent)) / 16 ≤
      scaleAdaptiveRestrictedMultiShellPrimeActualLoad
        exponents familySupport lowSupport highSupport lower upper
          lowSingular highSingular length target := by
    unfold scaleAdaptiveMultiShellPrimeActualLoad
      scaleAdaptiveRestrictedMultiShellPrimeActualLoad
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro exponent selected
    let cell := scaleAdaptiveMultiShellTargetCell
      length exponent target
    let N := length / 2 ^ exponent
    have no_boundary := scaleAdaptiveMultiShell_not_boundary_of_not_mem
      selected target_prime.pos target_high boundary_good
    have physical := scaleAdaptiveMultiShellTargetCell_physical
      length exponent target (scales_large exponent selected)
        (target_interior exponent selected) target_high no_boundary
    have cell_physical : 2 * cell ≤ 2 ^ exponent + 1 :=
      (mem_scaleAdaptiveMultiShellValidCells.mp physical.1).2.2
    have target_ambient := scaleAdaptiveRestrictedShellAmbientTargets_mem
      (scales_large exponent selected) target_high
    have local_cross : target ∉
        scaleAdaptiveSignedCrossRejectedFamilyBadTargets
          (familySupport exponent)
          (lowSupport exponent) (highSupport exponent)
          (2 ^ exponent)
          (adaptiveMixedOutcomeSpace
            (familySupport exponent) (2 ^ exponent))
          lower upper
          (scaleAdaptiveRestrictedShellLossCutoff
            (familySupport exponent) exponent)
          (lowSingular exponent) (highSingular exponent)
          N (scaleAdaptiveRestrictedShellAmbientTargets
            (2 ^ exponent) N) := by
      intro bad
      exact cross_good (Finset.mem_biUnion.mpr
        ⟨exponent, selected, bad⟩)
    have one_shell :=
      scaleAdaptiveBandPrimeOutcomeLoad_restricted_ge_full_sub_cutoff
        (familySupport exponent)
        (lowSupport exponent) (highSupport exponent)
        (2 ^ exponent) cell lower upper
        (scaleAdaptiveRestrictedShellLossCutoff
          (familySupport exponent) exponent)
        (lowSingular exponent) (highSingular exponent)
        N target
        (scaleAdaptiveRestrictedShellAmbientTargets
          (2 ^ exponent) N)
        (primes exponent selected) cell_physical
        (scaleAdaptiveRestrictedShellLossCutoff_pos
          (familySupport exponent) exponent
            (primes exponent selected))
        target_ambient local_cross
    rw [scaleAdaptiveRestrictedShellLossCutoff_mul_rank] at one_shell
    exact one_shell
  linarith

/-- A genuine supported type-`s` SEMIPRIME target retains the SAME
`Σ F_j/16` actual inverse-integer-degree load on all its eligible shells
after restriction to the ONE common low/high prime pool per shell. -/
theorem scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad_ge_euler_sum
    (exponents : Finset ℕ)
    (familySupport lowSupport highSupport : ℕ → Finset ℕ)
    (targetType : ℕ) (lower upper : ℝ)
    (lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ)
    (length prime : ℕ)
    (primes : ∀ exponent ∈ exponents,
      ∀ label ∈ familySupport exponent, label.Prime)
    (type_supported : ∀ exponent ∈ exponents,
      targetType ∈ familySupport exponent)
    (target_prime : prime.Prime)
    (type_positive : 0 < targetType)
    (target_high : targetType * prime ≤ length)
    (scales_large : ∀ exponent ∈ exponents,
      2 ^ exponent ≤ length / 2 ^ exponent)
    (target_interior : ∀ exponent ∈ exponents,
      4 * (length / 2 ^ exponent) ≤ targetType * prime)
    (not_exception : targetType * prime ∉
      scaleAdaptiveRestrictedMultiShellSemiprimeExceptions
        exponents familySupport lowSupport highSupport
          targetType lower upper lowSingular highSingular length) :
    (∑ exponent ∈ exponents,
      adaptivePatternEulerFactor
        (familySupport exponent) (2 ^ exponent)) / 16 ≤
      scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
        exponents familySupport lowSupport highSupport
          targetType lower upper lowSingular highSingular
            length (targetType * prime) := by
  let target := targetType * prime
  have old_good : target ∉
      scaleAdaptiveMultiShellSemiprimeExceptions
        exponents familySupport targetType lower upper length := by
    intro bad
    exact not_exception (Finset.mem_union_left _ bad)
  have cross_good : target ∉
      scaleAdaptiveRestrictedMultiShellCrossBadTargets
        exponents familySupport lowSupport highSupport
          lower upper lowSingular highSingular length := by
    intro bad
    exact not_exception (Finset.mem_union_right _ bad)
  have boundary_good : target ∉
      scaleAdaptiveMultiShellBoundaryTargets exponents length := by
    intro bad
    exact old_good (Finset.mem_union_right _ bad)
  have original :=
    scaleAdaptiveMultiShellSemiprimeActualLoad_ge_euler_sum_of_good_target
      exponents familySupport targetType lower upper length prime
        primes type_supported target_prime type_positive target_high
          scales_large target_interior old_good
  have preserved :
      scaleAdaptiveMultiShellSemiprimeActualLoad
        exponents familySupport targetType lower upper length target -
          (∑ exponent ∈ exponents,
            adaptivePatternEulerFactor
              (familySupport exponent) (2 ^ exponent)) / 16 ≤
      scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
        exponents familySupport lowSupport highSupport targetType
          lower upper lowSingular highSingular length target := by
    unfold scaleAdaptiveMultiShellSemiprimeActualLoad
      scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro exponent selected
    let cell := scaleAdaptiveMultiShellTargetCell
      length exponent target
    let N := length / 2 ^ exponent
    have target_positive : 0 < target := by
      dsimp [target]
      exact Nat.mul_pos type_positive target_prime.pos
    have no_boundary := scaleAdaptiveMultiShell_not_boundary_of_not_mem
      selected target_positive target_high boundary_good
    have physical := scaleAdaptiveMultiShellTargetCell_physical
      length exponent target (scales_large exponent selected)
        (target_interior exponent selected) target_high no_boundary
    have cell_physical : 2 * cell ≤ 2 ^ exponent + 1 :=
      (mem_scaleAdaptiveMultiShellValidCells.mp physical.1).2.2
    have target_ambient := scaleAdaptiveRestrictedShellAmbientTargets_mem
      (scales_large exponent selected) target_high
    have local_cross : target ∉
        scaleAdaptiveSignedCrossRejectedFamilyBadTargets
          (familySupport exponent)
          (lowSupport exponent) (highSupport exponent)
          (2 ^ exponent)
          (adaptiveMixedOutcomeSpace
            (familySupport exponent) (2 ^ exponent))
          lower upper
          (scaleAdaptiveRestrictedShellLossCutoff
            (familySupport exponent) exponent)
          (lowSingular exponent) (highSingular exponent)
          N (scaleAdaptiveRestrictedShellAmbientTargets
            (2 ^ exponent) N) := by
      intro bad
      exact cross_good (Finset.mem_biUnion.mpr
        ⟨exponent, selected, bad⟩)
    have one_shell :=
      scaleAdaptiveBandSemiprimeOutcomeLoad_restricted_ge_full_sub_cutoff
        (familySupport exponent)
        (lowSupport exponent) (highSupport exponent)
        targetType (2 ^ exponent) cell lower upper
        (scaleAdaptiveRestrictedShellLossCutoff
          (familySupport exponent) exponent)
        (lowSingular exponent) (highSingular exponent)
        N target
        (scaleAdaptiveRestrictedShellAmbientTargets
          (2 ^ exponent) N)
        (primes exponent selected)
        (type_supported exponent selected) cell_physical
        (scaleAdaptiveRestrictedShellLossCutoff_pos
          (familySupport exponent) exponent
            (primes exponent selected))
        target_ambient local_cross
    rw [scaleAdaptiveRestrictedShellLossCutoff_mul_rank] at one_shell
    exact one_shell
  linarith


end Erdos1139
