module

public import ScaleAdaptiveRestrictedMultiscaleLoad1139

@[expose] public section


/-!
# Exact transfer from genuine restricted physical loads to global joint hits

The globally assembled sampler makes exactly ONE color/outcome/center choice
at each actual prime label.  Its modular hit probability cannot be compared
with an indexed target-load sum unless repeated physical indices are handled:
for one label, outcome, and signed center, a given target comes from AT MOST
one physical index.

This module proves that uniqueness from the true fundamental-strip residue,
derives its genuine modular congruence, regroups the ACTUAL finite sums over
disjoint dyadic shells, and transfers the restricted inverse-integer-degree
loads into the globally coherent colored sampler.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1800000

/-- An ACTUAL signed-center edge has a nonnegative fundamental-strip
residue; it is never an arbitrary signed affine form. -/
theorem scaleAdaptiveSignedDegreeEdge_residue_nonnegative
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N label : ℕ) (center : ℤ)
    (selected : center ∈ scaleAdaptiveSignedDegreeEdges
      support scale outcome domain N label) :
    0 ≤ weightedPrimePatternSignedResidue
      support outcome.1 label center := by
  classical
  have actual := (Finset.mem_filter.mp selected).1
  exact (weightedPrimePatternEdges_prime_certificate
    support scale outcome
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
        label center actual).2.2.1

/-- Exact NATURAL physical-target decomposition at one actual signed
center.  The signed representative is first certified nonnegative. -/
theorem scaleAdaptiveSignedPhysicalTarget_eq_index_mul_add_residue
    (support : Finset ℕ) (base index label : ℕ) (center : ℤ)
    (residue_nonnegative :
      0 ≤ weightedPrimePatternSignedResidue
        support base label center) :
    scaleAdaptiveGTZIndexedPhysicalTarget
      support base index label center =
      index * label +
        (weightedPrimePatternSignedResidue
          support base label center).toNat := by
  have raw_nonnegative :
      0 ≤ (index : ℤ) * (label : ℤ) +
        weightedPrimePatternSignedResidue
          support base label center := by
    exact add_nonneg
      (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      residue_nonnegative
  have cast_target :
      ((scaleAdaptiveGTZIndexedPhysicalTarget
        support base index label center : ℕ) : ℤ) =
        (index : ℤ) * (label : ℤ) +
          weightedPrimePatternSignedResidue
            support base label center := by
    exact Int.toNat_of_nonneg raw_nonnegative
  have cast_residue :
      (((weightedPrimePatternSignedResidue
        support base label center).toNat : ℕ) : ℤ) =
          weightedPrimePatternSignedResidue
            support base label center := by
    exact Int.toNat_of_nonneg residue_nonnegative
  exact_mod_cast (show
    ((scaleAdaptiveGTZIndexedPhysicalTarget
      support base index label center : ℕ) : ℤ) =
      ((index * label +
        (weightedPrimePatternSignedResidue
          support base label center).toNat : ℕ) : ℤ) by
    rw [cast_target]
    push_cast
    rw [cast_residue])

/-- One actual signed center has INJECTIVE physical targets across its
distinct genuine indices whenever its actual prime label is positive. -/
theorem scaleAdaptiveSignedPhysicalTarget_index_injective
    (support : Finset ℕ) (base label : ℕ) (center : ℤ)
    (label_positive : 0 < label)
    (residue_nonnegative :
      0 ≤ weightedPrimePatternSignedResidue
        support base label center) :
    Function.Injective fun index =>
      scaleAdaptiveGTZIndexedPhysicalTarget
        support base index label center := by
  intro first second same
  change
    scaleAdaptiveGTZIndexedPhysicalTarget
      support base first label center =
    scaleAdaptiveGTZIndexedPhysicalTarget
      support base second label center at same
  rw [scaleAdaptiveSignedPhysicalTarget_eq_index_mul_add_residue
    support base first label center residue_nonnegative,
    scaleAdaptiveSignedPhysicalTarget_eq_index_mul_add_residue
      support base second label center residue_nonnegative] at same
  exact Nat.mul_right_cancel label_positive
    (Nat.add_right_cancel same)

/-- Every genuine indexed physical target belongs to precisely the SAME
modular residue class of its ONE actual signed center and prime label. -/
theorem scaleAdaptiveSignedPhysicalTarget_residue_modEq
    (support : Finset ℕ) (base index label target : ℕ) (center : ℤ)
    (residue_nonnegative :
      0 ≤ weightedPrimePatternSignedResidue
        support base label center)
    (physical : scaleAdaptiveGTZIndexedPhysicalTarget
      support base index label center = target) :
    (weightedPrimePatternSignedResidue
      support base label center).toNat ≡ target [MOD label] := by
  rw [← physical,
    scaleAdaptiveSignedPhysicalTarget_eq_index_mul_add_residue
      support base index label center residue_nonnegative]
  simp [Nat.ModEq, Nat.add_mod]

/-- At a fixed ACTUAL prime label and signed center, one physical target
occurs at most once among ANY finite physical-index family. -/
theorem scaleAdaptiveSignedPhysicalTarget_indexFiber_card_le_one
    (support : Finset ℕ) (base label target : ℕ) (center : ℤ)
    (indices : Finset ℕ)
    (label_positive : 0 < label)
    (residue_nonnegative :
      0 ≤ weightedPrimePatternSignedResidue
        support base label center) :
    (indices.filter fun index =>
      scaleAdaptiveGTZIndexedPhysicalTarget
        support base index label center = target).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro first in_first second in_second
  exact scaleAdaptiveSignedPhysicalTarget_index_injective
    support base label center label_positive residue_nonnegative
      ((Finset.mem_filter.mp in_first).2.trans
        (Finset.mem_filter.mp in_second).2.symm)

/-- A true signed center contributes at most its SINGLE modular-hit mass
across all sampled physical indices.  Outcome sampling can only delete
indices, and the index map is genuinely injective at its prime label. -/
theorem scaleAdaptiveSignedSampleIndexWeight_le_modularWeight
    (support : Finset ℕ) (outcome : ℕ × ℕ)
    (label target : ℕ) (center : ℤ)
    (indices : Finset ℕ) (samples : ℕ → Finset (ℕ × ℕ))
    (weight : ℝ)
    (label_positive : 0 < label)
    (residue_nonnegative :
      0 ≤ weightedPrimePatternSignedResidue
        support outcome.1 label center)
    (weight_nonnegative : 0 ≤ weight) :
    (∑ index ∈ indices,
      if outcome ∈ samples index ∧
          scaleAdaptiveGTZIndexedPhysicalTarget
            support outcome.1 index label center = target
      then weight else 0) ≤
      if (weightedPrimePatternSignedResidue
        support outcome.1 label center).toNat ≡ target [MOD label]
      then weight else 0 := by
  classical
  by_cases congruent :
      (weightedPrimePatternSignedResidue
        support outcome.1 label center).toNat ≡ target [MOD label]
  · rw [if_pos congruent, ← Finset.sum_filter]
    have subset :
        (indices.filter fun index =>
          outcome ∈ samples index ∧
            scaleAdaptiveGTZIndexedPhysicalTarget
              support outcome.1 index label center = target) ⊆
          (indices.filter fun index =>
            scaleAdaptiveGTZIndexedPhysicalTarget
              support outcome.1 index label center = target) := by
      intro index selected
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp selected).1,
          (Finset.mem_filter.mp selected).2.2⟩
    have cardinal := (Finset.card_le_card subset).trans
      (scaleAdaptiveSignedPhysicalTarget_indexFiber_card_le_one
        support outcome.1 label target center indices
          label_positive residue_nonnegative)
    have cardinal_real :
        (((indices.filter fun index =>
          outcome ∈ samples index ∧
            scaleAdaptiveGTZIndexedPhysicalTarget
              support outcome.1 index label center = target).card : ℕ) : ℝ) ≤
          1 := by exact_mod_cast cardinal
    simp only [Finset.sum_const, nsmul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_right cardinal_real weight_nonnegative]
  · rw [if_neg congruent]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro index _selected
    split_ifs with selected
    · exfalso
      exact congruent
        (scaleAdaptiveSignedPhysicalTarget_residue_modEq
          support outcome.1 index label target center
            residue_nonnegative selected.2)
    · rfl

/-- TRUE one-shell physical sample/index load is bounded by its actual
common-label modular mixed-pattern marginal.  Repeated indexed occurrences
are NOT counted: a fixed genuine label/outcome/center has at most one
physical index above any target. -/
theorem scaleAdaptiveSignedRestrictedSampleShell_le_modularLoad
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N target : ℕ)
    (indices : Finset ℕ)
    (samples : ℕ → Finset (ℕ × ℕ))
    (sample_subset : ∀ index,
      samples index ⊆ adaptiveMixedOutcomeSpace familySupport scale) :
    (∑ index ∈ indices,
      ∑ outcome ∈ samples index,
        scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
          familySupport lowSupport highSupport scale outcome lower upper
            lowSingular highSingular index N target /
          ((adaptiveMixedOutcomeSpace
            familySupport scale).card : ℝ)) ≤
      ∑ label ∈ scaleAdaptiveSignedTwoColorGoodPrimeLabels
        lowSupport highSupport scale lower upper
          lowSingular highSingular N,
        ∑ outcome ∈ adaptiveMixedOutcomeSpace familySupport scale,
          ∑ center ∈ scaleAdaptiveSignedDegreeEdges
            familySupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                familySupport outcome.1 lower upper) N label,
            if (weightedPrimePatternSignedResidue
              familySupport outcome.1 label center).toNat ≡
                target [MOD label]
            then 1 /
              (((adaptiveMixedOutcomeSpace
                familySupport scale).card : ℝ) *
               ((scaleAdaptiveSignedDegreeEdges
                 familySupport scale outcome
                   (scaleAdaptiveSignedConstantResidueBand
                     familySupport outcome.1 lower upper) N label).card : ℝ))
            else 0 := by
  classical
  let outcomes := adaptiveMixedOutcomeSpace familySupport scale
  let labels := scaleAdaptiveSignedTwoColorGoodPrimeLabels
    lowSupport highSupport scale lower upper
      lowSingular highSingular N
  let edges : (ℕ × ℕ) → ℕ → Finset ℤ := fun outcome label =>
    scaleAdaptiveSignedDegreeEdges
      familySupport scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          familySupport outcome.1 lower upper) N label
  let weight : (ℕ × ℕ) → ℕ → ℝ := fun outcome label =>
    1 / ((outcomes.card : ℝ) * ((edges outcome label).card : ℝ))
  change
    (∑ index ∈ indices,
      ∑ outcome ∈ samples index,
        scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
          familySupport lowSupport highSupport scale outcome lower upper
            lowSingular highSingular index N target /
          (outcomes.card : ℝ)) ≤
      ∑ label ∈ labels,
        ∑ outcome ∈ outcomes,
          ∑ center ∈ edges outcome label,
            if (weightedPrimePatternSignedResidue
              familySupport outcome.1 label center).toNat ≡
                target [MOD label]
            then weight outcome label else 0
  calc
    _ = ∑ index ∈ indices,
          ∑ outcome ∈ samples index,
            ∑ label ∈ labels,
              ∑ center ∈ edges outcome label,
                if scaleAdaptiveGTZIndexedPhysicalTarget
                  familySupport outcome.1 index label center = target
                then weight outcome label else 0 := by
      apply Finset.sum_congr rfl
      intro index _selected
      apply Finset.sum_congr rfl
      intro outcome _sampled
      unfold scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro label _label_selected
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro center _center_selected
      split_ifs with hit
      · dsimp [weight]
        ring
      · simp
    _ = ∑ index ∈ indices,
          ∑ outcome ∈ outcomes,
            ∑ label ∈ labels,
              ∑ center ∈ edges outcome label,
                if outcome ∈ samples index ∧
                  scaleAdaptiveGTZIndexedPhysicalTarget
                    familySupport outcome.1 index label center = target
                then weight outcome label else 0 := by
      apply Finset.sum_congr rfl
      intro index _selected
      calc
        _ = ∑ outcome ∈ samples index,
              ∑ label ∈ labels,
                ∑ center ∈ edges outcome label,
                  if outcome ∈ samples index ∧
                    scaleAdaptiveGTZIndexedPhysicalTarget
                      familySupport outcome.1 index label center = target
                  then weight outcome label else 0 := by
          apply Finset.sum_congr rfl
          intro outcome sampled
          simp only [sampled, true_and]
        _ = _ := by
          apply Finset.sum_subset (sample_subset index)
          intro outcome _selected not_sampled
          simp [not_sampled]
    _ = ∑ outcome ∈ outcomes,
          ∑ label ∈ labels,
            ∑ center ∈ edges outcome label,
              ∑ index ∈ indices,
                if outcome ∈ samples index ∧
                  scaleAdaptiveGTZIndexedPhysicalTarget
                    familySupport outcome.1 index label center = target
                then weight outcome label else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro outcome _selected
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro label _selected
      rw [Finset.sum_comm]
    _ = ∑ label ∈ labels,
          ∑ outcome ∈ outcomes,
            ∑ center ∈ edges outcome label,
              ∑ index ∈ indices,
                if outcome ∈ samples index ∧
                  scaleAdaptiveGTZIndexedPhysicalTarget
                    familySupport outcome.1 index label center = target
                then weight outcome label else 0 := by
      rw [Finset.sum_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro label label_selected
      have label_prime : label.Prime := by
        exact (Finset.mem_filter.mp
          (Finset.mem_sdiff.mp label_selected).1).2
      apply Finset.sum_le_sum
      intro outcome _outcome_selected
      apply Finset.sum_le_sum
      intro center center_selected
      exact scaleAdaptiveSignedSampleIndexWeight_le_modularWeight
        familySupport outcome label target center indices samples
          (weight outcome label) label_prime.pos
          (scaleAdaptiveSignedDegreeEdge_residue_nonnegative
            familySupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                familySupport outcome.1 lower upper)
              N label center center_selected)
          (div_nonneg (by norm_num)
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

/-- Exact conversion between the actual global prime-label subtype sum
and its honest natural prime-label Finset sum. -/
theorem scaleAdaptiveActualPrimeSubtype_sum_eq
    (labels : Finset ℕ) (mass : ℕ → ℝ) :
    (∑ label : ↥labels, mass label) =
      ∑ label ∈ labels, mass label := by
  classical
  simpa only [Finset.attach_eq_univ] using
    (Finset.sum_attach labels mass)

/-- TRUE uncolored modular mixed-pattern target mass of ONE actual
global good shell, retaining its shell-specific support, outcome family,
physical prime labels, signed centers, and inverse integer degrees. -/
noncomputable def scaleAdaptiveGlobalJointFamilyShellModularLoad
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (familySupport : ℕ → Finset ℕ)
    (length exponent target : ℕ) : ℝ :=
  ∑ label ∈ scaleAdaptiveGlobalTwoColorGoodShell
    configuration length exponent,
    ∑ outcome ∈ adaptiveMixedOutcomeSpace
      (familySupport exponent) (2 ^ exponent),
      ∑ center ∈ scaleAdaptiveSignedDegreeEdges
        (familySupport exponent) (2 ^ exponent) outcome
          (scaleAdaptiveSignedConstantResidueBand
            (familySupport exponent) outcome.1
              configuration.lower configuration.upper)
          (length / 2 ^ exponent) label,
        if (weightedPrimePatternSignedResidue
          (familySupport exponent) outcome.1 label center).toNat ≡
            target [MOD label]
        then 1 /
          (((adaptiveMixedOutcomeSpace
            (familySupport exponent) (2 ^ exponent)).card : ℝ) *
           ((scaleAdaptiveSignedDegreeEdges
             (familySupport exponent) (2 ^ exponent) outcome
               (scaleAdaptiveSignedConstantResidueBand
                 (familySupport exponent) outcome.1
                   configuration.lower configuration.upper)
               (length / 2 ^ exponent) label).card : ℝ))
        else 0

/-- The genuine common-pool restricted MULTISCALE PRIME physical target
load is at most the sum of its true one-label modular pattern masses.
This is the missing finite index-versus-modular coupling. -/
theorem scaleAdaptiveRestrictedMultiShellPrimeActualLoad_le_modularSum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (familySupport : ℕ → Finset ℕ)
    (length target : ℕ) :
    scaleAdaptiveRestrictedMultiShellPrimeActualLoad
      configuration.exponents familySupport
      configuration.lowSupport configuration.highSupport
      configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular
      length target ≤
      ∑ exponent ∈ configuration.exponents,
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

/-- The SAME globally coherent modular shell masses dominate every
genuine type-`s` restricted SEMIPRIME physical target load as well. -/
theorem scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad_le_modularSum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (familySupport : ℕ → Finset ℕ)
    (targetType length target : ℕ) :
    scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
      configuration.exponents familySupport
      configuration.lowSupport configuration.highSupport
      targetType configuration.lower configuration.upper
      configuration.lowSingular configuration.highSingular
      length target ≤
      ∑ exponent ∈ configuration.exponents,
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

/-- The TRUE single-label modular mixed-pattern mass, evaluated at the
canonical unique shell of one globally selected actual prime. -/
noncomputable def scaleAdaptiveGlobalJointFamilyLabelModularLoad
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (familySupport : ℕ → Finset ℕ)
    (length label target : ℕ) : ℝ :=
  let exponent := scaleAdaptiveGlobalJointShellIndex
    configuration length label
  ∑ outcome ∈ adaptiveMixedOutcomeSpace
    (familySupport exponent) (2 ^ exponent),
    ∑ center ∈ scaleAdaptiveSignedDegreeEdges
      (familySupport exponent) (2 ^ exponent) outcome
        (scaleAdaptiveSignedConstantResidueBand
          (familySupport exponent) outcome.1
            configuration.lower configuration.upper)
        (length / 2 ^ exponent) label,
      if (weightedPrimePatternSignedResidue
        (familySupport exponent) outcome.1 label center).toNat ≡
          target [MOD label]
      then 1 /
        (((adaptiveMixedOutcomeSpace
          (familySupport exponent) (2 ^ exponent)).card : ℝ) *
         ((scaleAdaptiveSignedDegreeEdges
           (familySupport exponent) (2 ^ exponent) outcome
             (scaleAdaptiveSignedConstantResidueBand
               (familySupport exponent) outcome.1
                 configuration.lower configuration.upper)
             (length / 2 ^ exponent) label).card : ℝ))
      else 0

/-- On a genuinely selected shell the canonical global label-to-shell
map recovers EXACTLY that shell, so its true modular label masses sum to
the genuine shell modular target mass. -/
theorem scaleAdaptiveGlobalJointFamilyShellModularLoad_eq_label_sum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (familySupport : ℕ → Finset ℕ)
    (length exponent target : ℕ)
    (selected : exponent ∈ configuration.exponents) :
    scaleAdaptiveGlobalJointFamilyShellModularLoad
      configuration familySupport length exponent target =
      ∑ label ∈ scaleAdaptiveGlobalTwoColorGoodShell
        configuration length exponent,
        scaleAdaptiveGlobalJointFamilyLabelModularLoad
          configuration familySupport length label target := by
  unfold scaleAdaptiveGlobalJointFamilyShellModularLoad
  apply Finset.sum_congr rfl
  intro label in_shell
  have recovered := scaleAdaptiveGlobalJointShellIndex_eq_of_mem
    configuration length selected in_shell
  unfold scaleAdaptiveGlobalJointFamilyLabelModularLoad
  rw [recovered]

/-- EXACT regrouping of the ONE actual global prime pool into genuinely
disjoint physical shells.  No prime is duplicated across shell patterns. -/
theorem scaleAdaptiveGlobalJointFamilyLabelModularSum_eq_shell_sum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (familySupport : ℕ → Finset ℕ)
    (length target : ℕ) :
    (∑ label ∈ scaleAdaptiveGlobalJointPrimePool configuration length,
      scaleAdaptiveGlobalJointFamilyLabelModularLoad
        configuration familySupport length label target) =
      ∑ exponent ∈ configuration.exponents,
        scaleAdaptiveGlobalJointFamilyShellModularLoad
          configuration familySupport length exponent target := by
  have disjoint :
      Set.Pairwise
        (↑configuration.exponents : Set ℕ)
        (fun first second =>
          Disjoint
            (scaleAdaptiveGlobalTwoColorGoodShell
              configuration length first)
            (scaleAdaptiveGlobalTwoColorGoodShell
              configuration length second)) := by
    intro first _first second _second different
    exact scaleAdaptiveGlobalTwoColorGoodShell_disjoint
      configuration length different
  unfold scaleAdaptiveGlobalJointPrimePool
  rw [Finset.sum_biUnion disjoint]
  apply Finset.sum_congr rfl
  intro exponent selected
  exact (scaleAdaptiveGlobalJointFamilyShellModularLoad_eq_label_sum
    configuration familySupport length exponent target selected).symm

/-- Exact uncolored LOW-family global modular target load equals the
sum of true disjoint shell modular loads with their differing supports. -/
theorem scaleAdaptiveGlobalJointLowModularLoad_eq_shell_sum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length target : ℕ) :
    (∑ label : ↥(scaleAdaptiveGlobalJointPrimePool
      configuration length),
      ∑ outcome ∈ scaleAdaptiveGlobalJointLowPatterns
        configuration length label,
        ∑ center ∈ scaleAdaptiveGlobalJointLowEdges
          configuration length label outcome,
          if (weightedPrimePatternSignedResidue
            (scaleAdaptiveGlobalJointLowSupport
              configuration length label)
            outcome.1 label center).toNat ≡
              target [MOD (label : ℕ)]
          then 1 /
            (((scaleAdaptiveGlobalJointLowPatterns
              configuration length label).card : ℝ) *
             ((scaleAdaptiveGlobalJointLowEdges
               configuration length label outcome).card : ℝ))
          else 0) =
      ∑ exponent ∈ configuration.exponents,
        scaleAdaptiveGlobalJointFamilyShellModularLoad
          configuration configuration.lowSupport length exponent target := by
  change
    (∑ label : ↥(scaleAdaptiveGlobalJointPrimePool
      configuration length),
      scaleAdaptiveGlobalJointFamilyLabelModularLoad
        configuration configuration.lowSupport length label target) = _
  calc
    _ = ∑ label ∈ scaleAdaptiveGlobalJointPrimePool configuration length,
          scaleAdaptiveGlobalJointFamilyLabelModularLoad
            configuration configuration.lowSupport
              length label target := by
      exact scaleAdaptiveActualPrimeSubtype_sum_eq
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (fun label => scaleAdaptiveGlobalJointFamilyLabelModularLoad
          configuration configuration.lowSupport length label target)
    _ = _ := scaleAdaptiveGlobalJointFamilyLabelModularSum_eq_shell_sum
      configuration configuration.lowSupport length target

/-- Exact uncolored HIGH-family global modular target load on the SAME
actual prime labels, with the genuinely different high supports. -/
theorem scaleAdaptiveGlobalJointHighModularLoad_eq_shell_sum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length target : ℕ) :
    (∑ label : ↥(scaleAdaptiveGlobalJointPrimePool
      configuration length),
      ∑ outcome ∈ scaleAdaptiveGlobalJointHighPatterns
        configuration length label,
        ∑ center ∈ scaleAdaptiveGlobalJointHighEdges
          configuration length label outcome,
          if (weightedPrimePatternSignedResidue
            (scaleAdaptiveGlobalJointHighSupport
              configuration length label)
            outcome.1 label center).toNat ≡
              target [MOD (label : ℕ)]
          then 1 /
            (((scaleAdaptiveGlobalJointHighPatterns
              configuration length label).card : ℝ) *
             ((scaleAdaptiveGlobalJointHighEdges
               configuration length label outcome).card : ℝ))
          else 0) =
      ∑ exponent ∈ configuration.exponents,
        scaleAdaptiveGlobalJointFamilyShellModularLoad
          configuration configuration.highSupport length exponent target := by
  change
    (∑ label : ↥(scaleAdaptiveGlobalJointPrimePool
      configuration length),
      scaleAdaptiveGlobalJointFamilyLabelModularLoad
        configuration configuration.highSupport length label target) = _
  calc
    _ = ∑ label ∈ scaleAdaptiveGlobalJointPrimePool configuration length,
          scaleAdaptiveGlobalJointFamilyLabelModularLoad
            configuration configuration.highSupport
              length label target := by
      exact scaleAdaptiveActualPrimeSubtype_sum_eq
        (scaleAdaptiveGlobalJointPrimePool configuration length)
        (fun label => scaleAdaptiveGlobalJointFamilyLabelModularLoad
          configuration configuration.highSupport length label target)
    _ = _ := scaleAdaptiveGlobalJointFamilyLabelModularSum_eq_shell_sum
      configuration configuration.highSupport length target

/-- EXACT LOW colored hit load of the ONE actual globally assembled joint
sampler: one fair color factor times the sum of true disjoint LOW-shell
modular mixed-pattern marginals. -/
theorem scaleAdaptiveGlobalJointLowHitLoad_eq_half_modularShellSum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    weightedActualPatternHitLoad
      (scaleAdaptiveGlobalJointPrimePool configuration length)
      (scaleAdaptiveGlobalJointColor configuration length)
      (scaleAdaptiveGlobalJointResidue
        configuration length lowTargets highTargets)
      false target =
      (∑ exponent ∈ configuration.exponents,
        scaleAdaptiveGlobalJointFamilyShellModularLoad
          configuration configuration.lowSupport
            length exponent target) / 2 := by
  have exact_marginal :=
    scaleAdaptiveSignedJointLowHitLoad_eq_half_label_outcome_center
      (scaleAdaptiveGlobalJointPrimePool configuration length)
      lowTargets highTargets
      (scaleAdaptiveGlobalJointLowSupport configuration length)
      (scaleAdaptiveGlobalJointHighSupport configuration length)
      (scaleAdaptiveGlobalJointLowPatterns configuration length)
      (scaleAdaptiveGlobalJointHighPatterns configuration length)
      (scaleAdaptiveGlobalJointLowEdges configuration length)
      (scaleAdaptiveGlobalJointHighEdges configuration length)
      target
      (scaleAdaptiveGlobalJointLowPatterns_nonempty
        configuration length low_primes)
      (scaleAdaptiveGlobalJointHighPatterns_nonempty
        configuration length high_primes)
      (fun label outcome selected =>
        scaleAdaptiveGlobalJointLowEdges_nonempty
          configuration length label selected)
      (fun label outcome selected =>
        scaleAdaptiveGlobalJointHighEdges_nonempty
          configuration length label selected)
  unfold scaleAdaptiveGlobalJointColor scaleAdaptiveGlobalJointResidue
    scaleAdaptiveGlobalJointOptionCount
  rw [exact_marginal]
  congr 1
  exact scaleAdaptiveGlobalJointLowModularLoad_eq_shell_sum
    configuration length target

/-- EXACT HIGH colored hit load of the SAME actual global sampler, with
its distinct high supports and precisely the same fair color factor. -/
theorem scaleAdaptiveGlobalJointHighHitLoad_eq_half_modularShellSum
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    weightedActualPatternHitLoad
      (scaleAdaptiveGlobalJointPrimePool configuration length)
      (scaleAdaptiveGlobalJointColor configuration length)
      (scaleAdaptiveGlobalJointResidue
        configuration length lowTargets highTargets)
      true target =
      (∑ exponent ∈ configuration.exponents,
        scaleAdaptiveGlobalJointFamilyShellModularLoad
          configuration configuration.highSupport
            length exponent target) / 2 := by
  have exact_marginal :=
    scaleAdaptiveSignedJointHighHitLoad_eq_half_label_outcome_center
      (scaleAdaptiveGlobalJointPrimePool configuration length)
      lowTargets highTargets
      (scaleAdaptiveGlobalJointLowSupport configuration length)
      (scaleAdaptiveGlobalJointHighSupport configuration length)
      (scaleAdaptiveGlobalJointLowPatterns configuration length)
      (scaleAdaptiveGlobalJointHighPatterns configuration length)
      (scaleAdaptiveGlobalJointLowEdges configuration length)
      (scaleAdaptiveGlobalJointHighEdges configuration length)
      target
      (scaleAdaptiveGlobalJointLowPatterns_nonempty
        configuration length low_primes)
      (scaleAdaptiveGlobalJointHighPatterns_nonempty
        configuration length high_primes)
      (fun label outcome selected =>
        scaleAdaptiveGlobalJointLowEdges_nonempty
          configuration length label selected)
      (fun label outcome selected =>
        scaleAdaptiveGlobalJointHighEdges_nonempty
          configuration length label selected)
  unfold scaleAdaptiveGlobalJointColor scaleAdaptiveGlobalJointResidue
    scaleAdaptiveGlobalJointOptionCount
  rw [exact_marginal]
  congr 1
  exact scaleAdaptiveGlobalJointHighModularLoad_eq_shell_sum
    configuration length target

/-- The ONE actual global sampler's LOW colored hit probability
dominates one half of the genuine restricted multiscale PRIME load. -/
theorem scaleAdaptiveGlobalJointLowHitLoad_ge_restrictedPrime
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    scaleAdaptiveRestrictedMultiShellPrimeActualLoad
      configuration.exponents configuration.lowSupport
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
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
    (scaleAdaptiveRestrictedMultiShellPrimeActualLoad_le_modularSum
      configuration configuration.lowSupport length target)

/-- The SAME actual global sampler's HIGH colored hit probability
dominates one half of its distinct restricted multiscale PRIME load. -/
theorem scaleAdaptiveGlobalJointHighHitLoad_ge_restrictedPrime
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    scaleAdaptiveRestrictedMultiShellPrimeActualLoad
      configuration.exponents configuration.highSupport
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
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
    (scaleAdaptiveRestrictedMultiShellPrimeActualLoad_le_modularSum
      configuration configuration.highSupport length target)

/-- Actual LOW colored global hit probability dominates one half of the
genuine type-`s` restricted multiscale SEMIPRIME load. -/
theorem scaleAdaptiveGlobalJointLowHitLoad_ge_restrictedSemiprime
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (targetType length : ℕ)
    (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
      configuration.exponents configuration.lowSupport
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
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
    (scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad_le_modularSum
      configuration configuration.lowSupport targetType length target)

/-- Actual HIGH colored hit probability of the SAME globally coherent
sampler dominates half its genuine supported-semiprime multiscale load. -/
theorem scaleAdaptiveGlobalJointHighHitLoad_ge_restrictedSemiprime
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (targetType length : ℕ)
    (lowTargets highTargets : Finset ℕ) (target : ℕ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad
      configuration.exponents configuration.highSupport
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
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
    (scaleAdaptiveRestrictedMultiShellSemiprimeActualLoad_le_modularSum
      configuration configuration.highSupport targetType length target)


end Erdos1139
