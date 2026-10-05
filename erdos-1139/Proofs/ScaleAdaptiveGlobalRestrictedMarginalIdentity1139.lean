module

public import ScaleAdaptiveGTZGlobalCover1139

@[expose] public section


/-!
# Exact common-pool-restricted signed mixed-pattern marginals

The genuine global family sampler has one dependent signed-center choice at
every actual prime label.  Its global finite option denominator must not
silently replace the local distribution `1/(#outcomes*d_outcome(p))` by a
uniform distribution over rich residue classes.  This file first proves the
EXACT global-to-local target marginal, with all other label coordinates
cancelled as harmless denominator tags and with the target-supported dummy
residue preserving every actual modular hit.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 1200000

/-- The true global family sampler has EXACTLY the same target-hit
probability at one actual label as its local dependent mixed-pattern
sampler.  Every other actual prime label is merely a denominator tag. -/
theorem scaleAdaptiveSignedGlobalFamilyTarget_probability
    (R targets : Finset ℕ)
    (support : ↥R → Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ) (prime : ↥R)
    (patterns_nonempty : ∀ label, (patterns label).Nonempty)
    (edges_nonempty : ∀ label outcome,
      outcome ∈ patterns label → (edges label outcome).Nonempty) :
    independentResidueHitFraction R
      (scaleAdaptiveSignedGlobalFamilyResidue
        R targets support patterns edges)
      target prime =
      ∑ edge ∈ scaleAdaptiveSignedFamilyTargetEdges
        (support prime) prime target (patterns prime) (edges prime),
        1 / (((patterns prime).card : ℝ) *
          ((edges prime edge.1).card : ℝ)) := by
  classical
  let localEvents : Finset
      (ScaleAdaptiveSignedFamilyChoice (patterns prime) (edges prime)) :=
    Finset.univ.filter fun choice =>
      (weightedPrimePatternSignedResidue
        (support prime)
        (scaleAdaptiveSignedChosenPattern choice).1 prime
        (scaleAdaptiveSignedChosenCenter choice)).toNat ≡
          target [MOD (prime : ℕ)]
  let globalEvents : Finset
      (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges) :=
    Finset.univ.filter fun assignment => assignment prime ∈ localEvents
  let localSize := Fintype.card
    (ScaleAdaptiveSignedFamilyChoice (patterns prime) (edges prime))
  let otherProduct :=
    ∏ other ∈ (Finset.univ.erase prime),
      Fintype.card
        (ScaleAdaptiveSignedFamilyChoice
          (patterns other) (edges other))
  have event_equivalence :
      (independentResidueHitChoices R
        (scaleAdaptiveSignedGlobalFamilyResidue
          R targets support patterns edges)
        target prime).card = globalEvents.card := by
    apply Finset.card_bij fun option _ =>
      (scaleAdaptiveSignedGlobalFamilyEquiv R patterns edges).symm option
    · intro option selected
      have hit := (Finset.mem_filter.mp selected).2
      have raw_hit :
          (weightedPrimePatternSignedResidue
            (support prime)
            (scaleAdaptiveSignedChosenPattern
              (((scaleAdaptiveSignedGlobalFamilyEquiv
                R patterns edges).symm option) prime)).1 prime
            (scaleAdaptiveSignedChosenCenter
              (((scaleAdaptiveSignedGlobalFamilyEquiv
                R patterns edges).symm option) prime))).toNat ≡
              target [MOD (prime : ℕ)] := by
        exact (scaleAdaptiveSignedTargetSupportedResidue_hit_iff
          targets prime
          (weightedPrimePatternSignedResidue
            (support prime)
            (scaleAdaptiveSignedChosenPattern
              (((scaleAdaptiveSignedGlobalFamilyEquiv
                R patterns edges).symm option) prime)).1 prime
            (scaleAdaptiveSignedChosenCenter
              (((scaleAdaptiveSignedGlobalFamilyEquiv
                R patterns edges).symm option) prime))).toNat
          target).mp hit
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, raw_hit⟩⟩
    · intro first _ second _ equal
      exact (scaleAdaptiveSignedGlobalFamilyEquiv
        R patterns edges).symm.injective equal
    · intro assignment selected
      refine ⟨(scaleAdaptiveSignedGlobalFamilyEquiv
        R patterns edges) assignment, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have raw_hit := (Finset.mem_filter.mp
          (Finset.mem_filter.mp selected).2).2
        exact (scaleAdaptiveSignedTargetSupportedResidue_hit_iff
          targets prime
          (weightedPrimePatternSignedResidue
            (support prime)
            (scaleAdaptiveSignedChosenPattern
              (((scaleAdaptiveSignedGlobalFamilyEquiv
                R patterns edges).symm
                ((scaleAdaptiveSignedGlobalFamilyEquiv
                  R patterns edges) assignment)) prime)).1 prime
            (scaleAdaptiveSignedChosenCenter
              (((scaleAdaptiveSignedGlobalFamilyEquiv
                R patterns edges).symm
                ((scaleAdaptiveSignedGlobalFamilyEquiv
                  R patterns edges) assignment)) prime))).toNat
          target).mpr (by simpa using raw_hit)
      · exact (scaleAdaptiveSignedGlobalFamilyEquiv
          R patterns edges).symm_apply_apply assignment
  have global_event_card :
      globalEvents.card = localEvents.card * otherProduct := by
    exact scaleAdaptiveGlobalCoordinateEvent_card
      (fun label : ↥R =>
        ScaleAdaptiveSignedFamilyChoice
          (patterns label) (edges label))
      prime localEvents
  have global_card :
      Fintype.card
        (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges) =
          otherProduct * localSize := by
    rw [Fintype.card_pi]
    exact (Finset.prod_erase_mul Finset.univ
      (fun label : ↥R =>
        Fintype.card (ScaleAdaptiveSignedFamilyChoice
          (patterns label) (edges label)))
      (Finset.mem_univ prime)).symm
  have local_positive : 0 < localSize :=
    scaleAdaptiveSignedFamilyChoice_card_pos
      (patterns prime) (edges prime)
      (patterns_nonempty prime)
      (fun outcome selected => edges_nonempty prime outcome selected)
  have other_positive : 0 < otherProduct := by
    apply Finset.prod_pos
    intro other _selected
    exact scaleAdaptiveSignedFamilyChoice_card_pos
      (patterns other) (edges other)
      (patterns_nonempty other)
      (fun outcome selected => edges_nonempty other outcome selected)
  have local_nonzero : (localSize : ℝ) ≠ 0 := by
    exact_mod_cast local_positive.ne'
  have other_nonzero : (otherProduct : ℝ) ≠ 0 := by
    exact_mod_cast other_positive.ne'
  unfold independentResidueHitFraction
  rw [event_equivalence, global_event_card, global_card]
  push_cast
  calc
    ((localEvents.card : ℝ) * (otherProduct : ℝ)) /
        ((otherProduct : ℝ) * (localSize : ℝ)) =
      (localEvents.card : ℝ) / (localSize : ℝ) := by
      field_simp
    _ = _ := by
      exact scaleAdaptiveSignedFamilyTarget_probability
        (support prime) prime target (patterns prime) (edges prime)
          (patterns_nonempty prime)
          (fun outcome selected =>
            edges_nonempty prime outcome selected)

/-- Rewrite the exact dependent signed-edge marginal as genuine nested
finite sums over its ACTUAL full outcome family and signed-center fibers.
Every term has the true integer degree denominator `#outcomes*dθ(p)`. -/
theorem scaleAdaptiveSignedFamilyTargetEdges_sum_eq_outcome_center
    (support : Finset ℕ) (label target : ℕ)
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ) :
    (∑ edge ∈ scaleAdaptiveSignedFamilyTargetEdges
      support label target patterns edges,
      1 / ((patterns.card : ℝ) * ((edges edge.1).card : ℝ))) =
      ∑ outcome ∈ patterns,
        ∑ center ∈ edges outcome,
          if (weightedPrimePatternSignedResidue
            support outcome.1 label center).toNat ≡
              target [MOD label] then
            1 / ((patterns.card : ℝ) * ((edges outcome).card : ℝ))
          else 0 := by
  classical
  unfold scaleAdaptiveSignedFamilyTargetEdges
  rw [Finset.sum_filter]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [← Finset.sum_attach patterns]
  apply Finset.sum_congr rfl
  intro outcome _selected
  rw [← Finset.sum_attach (edges outcome)]
  apply Finset.sum_congr rfl
  intro center _selected
  rfl

/-- Complete exact global-to-local signed target marginal in the
construction's true `μθ/dθ(p)` nested outcome-center form. -/
theorem scaleAdaptiveSignedGlobalFamilyTarget_probability_eq_outcome_center
    (R targets : Finset ℕ)
    (support : ↥R → Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ) (prime : ↥R)
    (patterns_nonempty : ∀ label, (patterns label).Nonempty)
    (edges_nonempty : ∀ label outcome,
      outcome ∈ patterns label → (edges label outcome).Nonempty) :
    independentResidueHitFraction R
      (scaleAdaptiveSignedGlobalFamilyResidue
        R targets support patterns edges)
      target prime =
      ∑ outcome ∈ patterns prime,
        ∑ center ∈ edges prime outcome,
          if (weightedPrimePatternSignedResidue
            (support prime) outcome.1 prime center).toNat ≡
              target [MOD (prime : ℕ)] then
            1 / (((patterns prime).card : ℝ) *
              ((edges prime outcome).card : ℝ))
          else 0 := by
  rw [scaleAdaptiveSignedGlobalFamilyTarget_probability
    R targets support patterns edges target prime
      patterns_nonempty edges_nonempty]
  exact scaleAdaptiveSignedFamilyTargetEdges_sum_eq_outcome_center
    (support prime) prime target (patterns prime) (edges prime)

/-- Exact WHOLE-POOL family target load on the genuinely retained actual
prime labels.  Every global denominator tag cancels, leaving precisely the
true local `μθ/dθ(p)` signed-center sums, not a proxy distribution. -/
theorem scaleAdaptiveSignedGlobalFamilyTargetLoad_eq_label_outcome_center
    (R targets : Finset ℕ)
    (support : ↥R → Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ)
    (patterns_nonempty : ∀ label, (patterns label).Nonempty)
    (edges_nonempty : ∀ label outcome,
      outcome ∈ patterns label → (edges label outcome).Nonempty) :
    (∑ prime : ↥R,
      independentResidueHitFraction R
        (scaleAdaptiveSignedGlobalFamilyResidue
          R targets support patterns edges)
        target prime) =
      ∑ prime : ↥R,
        ∑ outcome ∈ patterns prime,
          ∑ center ∈ edges prime outcome,
            if (weightedPrimePatternSignedResidue
              (support prime) outcome.1 prime center).toNat ≡
                target [MOD (prime : ℕ)] then
              1 / (((patterns prime).card : ℝ) *
                ((edges prime outcome).card : ℝ))
            else 0 := by
  apply Finset.sum_congr rfl
  intro prime _selected
  exact scaleAdaptiveSignedGlobalFamilyTarget_probability_eq_outcome_center
    R targets support patterns edges target prime
      patterns_nonempty edges_nonempty

/-- Exact LOW colored hit load of the ONE globally coherent signed-center
sampler, as a restricted actual-prime / full-outcome / genuine-center sum.
The fair color factor `1/2` occurs exactly once. -/
theorem scaleAdaptiveSignedJointLowHitLoad_eq_half_label_outcome_center
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ)
    (low_patterns_nonempty : ∀ label, (lowPatterns label).Nonempty)
    (high_patterns_nonempty : ∀ label, (highPatterns label).Nonempty)
    (low_edges_nonempty : ∀ label pattern,
      pattern ∈ lowPatterns label → (lowEdges label pattern).Nonempty)
    (high_edges_nonempty : ∀ label pattern,
      pattern ∈ highPatterns label → (highEdges label pattern).Nonempty) :
    weightedActualPatternHitLoad R
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges)
      false target =
        (∑ prime : ↥R,
          ∑ outcome ∈ lowPatterns prime,
            ∑ center ∈ lowEdges prime outcome,
              if (weightedPrimePatternSignedResidue
                (lowSupport prime) outcome.1 prime center).toNat ≡
                  target [MOD (prime : ℕ)] then
                1 / (((lowPatterns prime).card : ℝ) *
                  ((lowEdges prime outcome).card : ℝ))
              else 0) / 2 := by
  rw [scaleAdaptiveSignedJointHitLoad_low_eq_half
    R lowTargets highTargets lowSupport highSupport
      lowPatterns highPatterns lowEdges highEdges target
        low_patterns_nonempty high_patterns_nonempty
          low_edges_nonempty high_edges_nonempty]
  congr 1
  exact scaleAdaptiveSignedGlobalFamilyTargetLoad_eq_label_outcome_center
    R lowTargets lowSupport lowPatterns lowEdges target
      low_patterns_nonempty low_edges_nonempty

/-- Exact HIGH colored hit load from the SAME shared-prime-pool sampler;
its distinct high support and true inverse integer degrees are retained. -/
theorem scaleAdaptiveSignedJointHighHitLoad_eq_half_label_outcome_center
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ)
    (low_patterns_nonempty : ∀ label, (lowPatterns label).Nonempty)
    (high_patterns_nonempty : ∀ label, (highPatterns label).Nonempty)
    (low_edges_nonempty : ∀ label pattern,
      pattern ∈ lowPatterns label → (lowEdges label pattern).Nonempty)
    (high_edges_nonempty : ∀ label pattern,
      pattern ∈ highPatterns label → (highEdges label pattern).Nonempty) :
    weightedActualPatternHitLoad R
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges)
      true target =
        (∑ prime : ↥R,
          ∑ outcome ∈ highPatterns prime,
            ∑ center ∈ highEdges prime outcome,
              if (weightedPrimePatternSignedResidue
                (highSupport prime) outcome.1 prime center).toNat ≡
                  target [MOD (prime : ℕ)] then
                1 / (((highPatterns prime).card : ℝ) *
                  ((highEdges prime outcome).card : ℝ))
              else 0) / 2 := by
  rw [scaleAdaptiveSignedJointHitLoad_high_eq_half
    R lowTargets highTargets lowSupport highSupport
      lowPatterns highPatterns lowEdges highEdges target
        low_patterns_nonempty high_patterns_nonempty
          low_edges_nonempty high_edges_nonempty]
  congr 1
  exact scaleAdaptiveSignedGlobalFamilyTargetLoad_eq_label_outcome_center
    R highTargets highSupport highPatterns highEdges target
      high_patterns_nonempty high_edges_nonempty

/-- ACTUAL unnormalized inverse-INTEGER-degree target load lost by
restricting one outcome to the common low/high good-prime intersection. -/
noncomputable def scaleAdaptiveSignedCrossRejectedActualTargetLoss
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N target : ℕ) : ℝ :=
  ∑ label ∈ scaleAdaptiveSignedTwoColorRejectedPrimeLabels
    lowSupport highSupport scale lower upper
      lowSingular highSingular N,
    ∑ center ∈ scaleAdaptiveSignedDegreeEdges
      familySupport scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          familySupport outcome.1 lower upper) N label,
      if scaleAdaptiveSignedOutcomePhysicalHit
        familySupport scale outcome label center target then
        1 / ((scaleAdaptiveSignedDegreeEdges
          familySupport scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              familySupport outcome.1 lower upper) N label).card : ℝ)
      else 0

/-- Every true cross-rejected actual target loss is nonnegative. -/
theorem scaleAdaptiveSignedCrossRejectedActualTargetLoss_nonnegative
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N target : ℕ) :
    0 ≤ scaleAdaptiveSignedCrossRejectedActualTargetLoss
      familySupport lowSupport highSupport scale outcome lower upper
        lowSingular highSingular N target := by
  unfold scaleAdaptiveSignedCrossRejectedActualTargetLoss
  apply Finset.sum_nonneg
  intro label _selected
  apply Finset.sum_nonneg
  intro center _selected
  split_ifs with hit
  · exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  · exact le_refl 0

/-- EXACT physical-target normalization of the genuine cross-rejected
inverse-degree losses; no factor equal to the number of ambient targets
is inserted. -/
theorem scaleAdaptiveSignedCrossRejectedActualTargetLoss_sum_eq_incidence
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) (targets : Finset ℕ) :
    scaleAdaptivePrimeLabelNormalizedWeight N *
      (∑ target ∈ targets,
        scaleAdaptiveSignedCrossRejectedActualTargetLoss
          familySupport lowSupport highSupport scale outcome lower upper
            lowSingular highSingular N target) =
      scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
        familySupport lowSupport highSupport scale outcome lower upper
          lowSingular highSingular N targets := by
  unfold scaleAdaptiveSignedCrossRejectedActualTargetLoss
    scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _selected
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _selected
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro center _selected
  split_ifs with hit
  · unfold weightedPrimePatternActualEdgeWeight weightedPrimePatternDegree
    ring
  · simp

/-- The actual moving target set on which common-label restriction loses
at least a fixed positive amount of inverse-INTEGER-degree mass. -/
noncomputable def scaleAdaptiveSignedCrossRejectedBadTargets
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) (targets : Finset ℕ) : Finset ℕ :=
  targets.filter fun target =>
    cutoff ≤ scaleAdaptiveSignedCrossRejectedActualTargetLoss
      familySupport lowSupport highSupport scale outcome lower upper
        lowSingular highSingular N target

/-- Exact finite Markov deletion for the TRUE cross-rejected target losses.
Its normalized bad-target density is bounded by actual physical-target
incidence divided by the positive cutoff. -/
theorem scaleAdaptiveSignedCrossRejectedBadTargets_normalized_le
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) (targets : Finset ℕ)
    (cutoff_positive : 0 < cutoff) (large : 2 ≤ N) :
    ((scaleAdaptiveSignedCrossRejectedBadTargets
      familySupport lowSupport highSupport scale outcome lower upper cutoff
        lowSingular highSingular N targets).card : ℝ) *
          scaleAdaptivePrimeLabelNormalizedWeight N ≤
      scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
        familySupport lowSupport highSupport scale outcome lower upper
          lowSingular highSingular N targets / cutoff := by
  let bad := scaleAdaptiveSignedCrossRejectedBadTargets
    familySupport lowSupport highSupport scale outcome lower upper cutoff
      lowSingular highSingular N targets
  let loss := scaleAdaptiveSignedCrossRejectedActualTargetLoss
    familySupport lowSupport highSupport scale outcome lower upper
      lowSingular highSingular N
  have cardinal :
      cutoff * (bad.card : ℝ) ≤
        ∑ target ∈ targets, loss target := by
    calc
      cutoff * (bad.card : ℝ) =
          ∑ _target ∈ bad, cutoff := by simp [mul_comm]
      _ ≤ ∑ target ∈ bad, loss target := by
        apply Finset.sum_le_sum
        intro target selected
        exact (Finset.mem_filter.mp selected).2
      _ ≤ ∑ target ∈ targets, loss target := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro target _selected _not_bad
          exact scaleAdaptiveSignedCrossRejectedActualTargetLoss_nonnegative
            familySupport lowSupport highSupport scale outcome lower upper
              lowSingular highSingular N target
  have weighted := mul_le_mul_of_nonneg_right cardinal
    (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  have identity :=
    scaleAdaptiveSignedCrossRejectedActualTargetLoss_sum_eq_incidence
      familySupport lowSupport highSupport scale outcome lower upper
        lowSingular highSingular N targets
  apply (le_div_iff₀ cutoff_positive).mpr
  dsimp [bad, loss] at cardinal weighted
  nlinarith

/-- Deleting labels rejected by EITHER color spoils at most a
prime-density-ZERO set of actual moving targets for any fixed positive
loss threshold.  This turns cross-support intersection into an honest
target deletion, rather than assuming every target keeps its old load. -/
theorem scaleAdaptiveSignedCrossRejectedBadTargets_normalized_tendsto_zero
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (targets : ℕ → Finset ℕ)
    (cutoff_positive : 0 < cutoff)
    (rejected : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedCrossRejectedBadTargets
          familySupport lowSupport highSupport scale outcome
            lower upper cutoff lowSingular highSingular
              N (targets N)).card : ℝ) *
                scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ)) := by
  have incidence :=
    scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence_tendsto_zero
      familySupport lowSupport highSupport scale outcome lower upper
        lowSingular highSingular targets rejected
  have majorant :
      Tendsto
        (fun N : ℕ =>
          scaleAdaptiveSignedTwoColorRejectedActualTargetIncidence
            familySupport lowSupport highSupport scale outcome lower upper
              lowSingular highSingular N (targets N) / cutoff)
        atTop (nhds (0 : ℝ)) := by
    simpa using incidence.div_const cutoff
  apply squeeze_zero' ?_ ?_ majorant
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N large
    exact mul_nonneg (Nat.cast_nonneg _)
      (scaleAdaptivePrimeLabelNormalizedWeight_nonnegative N large)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N large
    exact scaleAdaptiveSignedCrossRejectedBadTargets_normalized_le
      familySupport lowSupport highSupport scale outcome lower upper cutoff
        lowSingular highSingular N (targets N) cutoff_positive large

/-- The same common-prime restriction deletion is `o(Y/log Y)` at the
ORIGINAL target length on every fixed genuine dyadic physical shell. -/
theorem scaleAdaptiveSignedCrossRejectedBadTargets_global_tendsto_zero
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale exponent : ℕ) (outcome : ℕ × ℕ)
    (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (targets : ℕ → Finset ℕ)
    (cutoff_positive : 0 < cutoff)
    (rejected : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveSignedCrossRejectedBadTargets
          familySupport lowSupport highSupport scale outcome
            lower upper cutoff lowSingular highSingular
              (length / 2 ^ exponent)
              (targets (length / 2 ^ exponent))).card : ℝ) *
                Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  let bad : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveSignedCrossRejectedBadTargets
      familySupport lowSupport highSupport scale outcome
        lower upper cutoff lowSingular highSingular N (targets N)
  have local_limit :=
    scaleAdaptiveSignedCrossRejectedBadTargets_normalized_tendsto_zero
      familySupport lowSupport highSupport scale outcome lower upper cutoff
        lowSingular highSingular targets cutoff_positive rejected
  have local_density : Tendsto
      (fun N : ℕ =>
        ((bad N).card : ℝ) * Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
    convert local_limit using 1
    ext N
    unfold scaleAdaptivePrimeLabelNormalizedWeight
    ring
  exact scaleAdaptiveDyadicBadTargets_global_tendsto_zero
    exponent bad local_density

/-- Exact conversion of a genuine indexed-target fiber cardinality into
its actual individual signed-center weights.  This remains true even at a
zero-degree label: both sides are then empty and equal to zero. -/
theorem scaleAdaptiveSignedIndexedTargetFiber_inverseCard_eq_center_sum
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N label target : ℕ) :
    ((scaleAdaptiveSignedIndexedLabelTargetFiber
      support scale outcome domain index N label target).card : ℝ) /
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ) =
      ∑ center ∈ scaleAdaptiveSignedDegreeEdges
        support scale outcome domain N label,
        if scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index label center = target then
            1 / ((scaleAdaptiveSignedDegreeEdges
              support scale outcome domain N label).card : ℝ)
        else 0 := by
  classical
  calc
    _ = ∑ _center ∈ scaleAdaptiveSignedIndexedLabelTargetFiber
          support scale outcome domain index N label target,
          1 / (scaleAdaptiveSignedDegree
            support scale outcome domain N label : ℝ) := by
      simp [div_eq_mul_inv]
    _ = _ := by
      unfold scaleAdaptiveSignedIndexedLabelTargetFiber
      rw [Finset.sum_filter]
      rfl

/-- The EXISTING actual inverse-integer-degree indexed target load equals
the sum over the FULL genuine prime-label shell of its true individual
center weights; zero-degree labels contribute an empty sum. -/
theorem scaleAdaptiveBandActualInverseTargetLoad_eq_fullLabelCenter
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper : ℝ) (index N target : ℕ) :
    scaleAdaptiveBandActualInverseTargetLoad
      support scale lower upper index outcome N target =
      ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
        ∑ center ∈ scaleAdaptiveSignedDegreeEdges
          support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper) N label,
          if scaleAdaptiveGTZIndexedPhysicalTarget
            support outcome.1 index label center = target then
              1 / ((scaleAdaptiveSignedDegreeEdges
                support scale outcome
                  (scaleAdaptiveSignedConstantResidueBand
                    support outcome.1 lower upper) N label).card : ℝ)
          else 0 := by
  classical
  let domain := scaleAdaptiveSignedConstantResidueBand
    support outcome.1 lower upper
  unfold scaleAdaptiveBandActualInverseTargetLoad
    scaleAdaptiveSignedUnitActualTargetLoad
    scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
  simp only [one_mul]
  change
    (∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
      support scale outcome domain N,
      ((scaleAdaptiveSignedIndexedLabelTargetFiber
        support scale outcome domain index N label target).card : ℝ) /
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ)) = _
  calc
    _ = ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
          support scale outcome domain N,
          ∑ center ∈ scaleAdaptiveSignedDegreeEdges
            support scale outcome domain N label,
            if scaleAdaptiveGTZIndexedPhysicalTarget
              support outcome.1 index label center = target then
                1 / ((scaleAdaptiveSignedDegreeEdges
                  support scale outcome domain N label).card : ℝ)
            else 0 := by
      apply Finset.sum_congr rfl
      intro label _selected
      exact scaleAdaptiveSignedIndexedTargetFiber_inverseCard_eq_center_sum
        support scale outcome domain index N label target
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro label in_pool not_usable
      have degree_zero :
          scaleAdaptiveSignedDegree
            support scale outcome domain N label = 0 := by
        by_contra nonzero
        exact not_usable (Finset.mem_filter.mpr
          ⟨in_pool, nonzero⟩)
      have empty :
          scaleAdaptiveSignedDegreeEdges
            support scale outcome domain N label = ∅ := by
        exact Finset.card_eq_zero.mp degree_zero
      simp [empty]

/-- Genuine indexed inverse-INTEGER-degree physical-target mass after
restricting to the ONE common actual low/high prime-label pool. -/
noncomputable def scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (index N target : ℕ) : ℝ :=
  ∑ label ∈ scaleAdaptiveSignedTwoColorGoodPrimeLabels
    lowSupport highSupport scale lower upper
      lowSingular highSingular N,
    ∑ center ∈ scaleAdaptiveSignedDegreeEdges
      familySupport scale outcome
        (scaleAdaptiveSignedConstantResidueBand
          familySupport outcome.1 lower upper) N label,
      if scaleAdaptiveGTZIndexedPhysicalTarget
        familySupport outcome.1 index label center = target then
          1 / ((scaleAdaptiveSignedDegreeEdges
            familySupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                familySupport outcome.1 lower upper) N label).card : ℝ)
      else 0

/-- EXACT decomposition of the EXISTING full actual indexed target load
into its retained common-prime-pool mass and true rejected-label indexed
mass.  No asymptotic, degree approximation, or target assumption is used. -/
theorem scaleAdaptiveBandActualInverseTargetLoad_eq_restricted_add_rejected
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (index N target : ℕ) :
    scaleAdaptiveBandActualInverseTargetLoad
      familySupport scale lower upper index outcome N target =
      scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
        familySupport lowSupport highSupport scale outcome lower upper
          lowSingular highSingular index N target +
        ∑ label ∈ scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N,
          ∑ center ∈ scaleAdaptiveSignedDegreeEdges
            familySupport scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                familySupport outcome.1 lower upper) N label,
            if scaleAdaptiveGTZIndexedPhysicalTarget
              familySupport outcome.1 index label center = target then
                1 / ((scaleAdaptiveSignedDegreeEdges
                  familySupport scale outcome
                    (scaleAdaptiveSignedConstantResidueBand
                      familySupport outcome.1 lower upper) N label).card : ℝ)
            else 0 := by
  classical
  rw [scaleAdaptiveBandActualInverseTargetLoad_eq_fullLabelCenter]
  unfold scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
    scaleAdaptiveSignedTwoColorGoodPrimeLabels
  exact (Finset.sum_sdiff
    (scaleAdaptiveSignedTwoColorRejectedPrimeLabels_subset_pool
      lowSupport highSupport scale lower upper
        lowSingular highSingular N)).symm

/-- Every rejected genuine indexed-target center is charged by its ACTUAL
physical-target loss whenever the distinguished index is genuinely active. -/
theorem scaleAdaptiveBandActualInverseTargetLoad_le_restricted_add_crossLoss
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcome : ℕ × ℕ) (lower upper : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (index N target : ℕ)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      familySupport scale outcome) :
    scaleAdaptiveBandActualInverseTargetLoad
      familySupport scale lower upper index outcome N target ≤
      scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
        familySupport lowSupport highSupport scale outcome lower upper
          lowSingular highSingular index N target +
      scaleAdaptiveSignedCrossRejectedActualTargetLoss
        familySupport lowSupport highSupport scale outcome lower upper
          lowSingular highSingular N target := by
  rw [scaleAdaptiveBandActualInverseTargetLoad_eq_restricted_add_rejected
    familySupport lowSupport highSupport scale outcome lower upper
      lowSingular highSingular index N target]
  apply add_le_add (le_refl _)
  unfold scaleAdaptiveSignedCrossRejectedActualTargetLoss
  apply Finset.sum_le_sum
  intro label _selected
  apply Finset.sum_le_sum
  intro center _selected
  split_ifs with indexed physical
  · exact le_refl _
  · exfalso
    apply physical
    simp only [scaleAdaptiveSignedOutcomePhysicalHit, decide_eq_true_eq]
    exact ⟨index, active, indexed.symm⟩
  · exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  · exact le_refl _

/-- One actual finite deletion simultaneously protects the true
inverse-degree load of EVERY outcome in a fixed signed pattern family. -/
noncomputable def scaleAdaptiveSignedCrossRejectedFamilyBadTargets
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcomes : Finset (ℕ × ℕ))
    (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N : ℕ) (targets : Finset ℕ) : Finset ℕ :=
  outcomes.biUnion fun outcome =>
    scaleAdaptiveSignedCrossRejectedBadTargets
      familySupport lowSupport highSupport scale outcome lower upper cutoff
        lowSingular highSingular N targets

/-- Simultaneous finite outcome deletion has zero true prime-target density;
the entire outcome space is fixed BEFORE the physical label scale tends to
infinity. -/
theorem scaleAdaptiveSignedCrossRejectedFamilyBadTargets_tendsto_zero
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcomes : Finset (ℕ × ℕ))
    (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (targets : ℕ → Finset ℕ)
    (cutoff_positive : 0 < cutoff)
    (rejected : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedCrossRejectedFamilyBadTargets
          familySupport lowSupport highSupport scale outcomes
            lower upper cutoff lowSingular highSingular
              N (targets N)).card : ℝ) *
                Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
  unfold scaleAdaptiveSignedCrossRejectedFamilyBadTargets
  apply scaleAdaptiveBandFiniteBadUnion_normalized_card_tendsto_zero
  intro outcome _selected
  have local_limit :=
    scaleAdaptiveSignedCrossRejectedBadTargets_normalized_tendsto_zero
      familySupport lowSupport highSupport scale outcome lower upper cutoff
        lowSingular highSingular targets cutoff_positive rejected
  convert local_limit using 1
  ext N
  unfold scaleAdaptivePrimeLabelNormalizedWeight
  ring

/-- The finite whole-outcome deletion remains `o(Y/log Y)` at the
ORIGINAL interval length on every fixed genuine physical dyadic shell. -/
theorem scaleAdaptiveSignedCrossRejectedFamilyBadTargets_global_tendsto_zero
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale exponent : ℕ) (outcomes : Finset (ℕ × ℕ))
    (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (targets : ℕ → Finset ℕ)
    (cutoff_positive : 0 < cutoff)
    (rejected : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          lowSupport highSupport scale lower upper
            lowSingular highSingular N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveSignedCrossRejectedFamilyBadTargets
          familySupport lowSupport highSupport scale outcomes
            lower upper cutoff lowSingular highSingular
              (length / 2 ^ exponent)
              (targets (length / 2 ^ exponent))).card : ℝ) *
                Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (0 : ℝ)) := by
  exact scaleAdaptiveDyadicBadTargets_global_tendsto_zero exponent
    (fun N => scaleAdaptiveSignedCrossRejectedFamilyBadTargets
      familySupport lowSupport highSupport scale outcomes
        lower upper cutoff lowSingular highSingular N (targets N))
    (scaleAdaptiveSignedCrossRejectedFamilyBadTargets_tendsto_zero
      familySupport lowSupport highSupport scale outcomes
        lower upper cutoff lowSingular highSingular targets
          cutoff_positive rejected)

/-- Outside the ONE whole-outcome deletion, every genuine outcome loses
strictly less than the stipulated fixed inverse-degree target tolerance. -/
theorem scaleAdaptiveSignedCrossRejectedActualTargetLoss_lt_of_not_bad
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale : ℕ) (outcomes : Finset (ℕ × ℕ))
    (outcome : ℕ × ℕ) (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N target : ℕ) (targets : Finset ℕ)
    (selected : outcome ∈ outcomes)
    (target_selected : target ∈ targets)
    (not_bad : target ∉ scaleAdaptiveSignedCrossRejectedFamilyBadTargets
      familySupport lowSupport highSupport scale outcomes
        lower upper cutoff lowSingular highSingular N targets) :
    scaleAdaptiveSignedCrossRejectedActualTargetLoss
      familySupport lowSupport highSupport scale outcome lower upper
        lowSingular highSingular N target < cutoff := by
  by_contra failed
  apply not_bad
  apply Finset.mem_biUnion.mpr
  refine ⟨outcome, selected, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨target_selected, le_of_not_gt failed⟩

/-- Every PRIME sample at a genuine interior physical index belongs to
the SAME actual active mixed-pattern index set. -/
theorem scaleAdaptiveBandPrimeSample_active_of_physical
    {support : Finset ℕ} {scale m index : ℕ} {outcome : ℕ × ℕ}
    (physical : 2 * m ≤ scale + 1)
    (interior : index ∈ scaleAdaptiveBandInteriorIndices m)
    (sample : outcome ∈ adaptiveMixedPrimePatternSamples
      support scale index) :
    index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome := by
  have bounds := scaleAdaptiveBandInteriorIndices_mem interior
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, sample⟩

/-- Every genuinely supported SEMIPRIME sample at a physical interior
index belongs to the SAME actual mixed-pattern active index set. -/
theorem scaleAdaptiveBandSemiprimeSample_active_of_physical
    {support : Finset ℕ} {targetType scale m index : ℕ}
    {outcome : ℕ × ℕ}
    (type_supported : targetType ∈ support)
    (physical : 2 * m ≤ scale + 1)
    (interior : index ∈ scaleAdaptiveBandInteriorIndices m)
    (sample : outcome ∈ adaptiveMixedSemiprimePatternSamples
      support targetType scale index) :
    index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome := by
  have bounds := scaleAdaptiveBandInteriorIndices_mem interior
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨targetType, type_supported, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, sample⟩

/-- A genuinely uniform finite mixed-outcome distribution gives ANY subset
of its actual outcomes averaged mass at most the common nonnegative bound. -/
theorem scaleAdaptiveUniformOutcomeSampleAverage_le_cutoff
    {α : Type*} (outcomes samples : Finset α)
    (mass : α → ℝ) (cutoff : ℝ)
    (nonempty : outcomes.Nonempty)
    (subset : samples ⊆ outcomes)
    (cutoff_nonnegative : 0 ≤ cutoff)
    (bounded : ∀ outcome ∈ samples, mass outcome ≤ cutoff) :
    (∑ outcome ∈ samples,
      mass outcome / (outcomes.card : ℝ)) ≤ cutoff := by
  have denominator_positive : (0 : ℝ) < outcomes.card := by
    exact_mod_cast Finset.card_pos.mpr nonempty
  have sum_bounded :
      (∑ outcome ∈ samples, mass outcome) ≤
        (samples.card : ℝ) * cutoff := by
    calc
      _ ≤ ∑ _outcome ∈ samples, cutoff := by
        apply Finset.sum_le_sum
        intro outcome selected
        exact bounded outcome selected
      _ = _ := by simp [mul_comm]
  have cardinal : (samples.card : ℝ) ≤ (outcomes.card : ℝ) := by
    exact_mod_cast Finset.card_le_card subset
  rw [← Finset.sum_div]
  apply (div_le_iff₀ denominator_positive).mpr
  nlinarith [mul_le_mul_of_nonneg_right cardinal cutoff_nonnegative]

/-- A fixed genuinely active sample shell preserves its EXISTING actual
inverse-degree target load after restriction to the common low/high prime
pool, losing at most `scale*cutoff` outside ONE whole-outcome deletion. -/
theorem scaleAdaptiveSignedSampleShellRestrictedLoad_ge_full_sub_cutoff
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale m : ℕ) (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (samples : ℕ → Finset (ℕ × ℕ))
    (N target : ℕ) (targets : Finset ℕ)
    (primes : ∀ prime ∈ familySupport, prime.Prime)
    (physical : 2 * m ≤ scale + 1)
    (cutoff_positive : 0 < cutoff)
    (sample_subset : ∀ index,
      samples index ⊆ adaptiveMixedOutcomeSpace familySupport scale)
    (sample_active : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      ∀ outcome ∈ samples index,
        index ∈ adaptiveMixedOutcomeActiveIndices
          familySupport scale outcome)
    (target_selected : target ∈ targets)
    (not_bad : target ∉
      scaleAdaptiveSignedCrossRejectedFamilyBadTargets
        familySupport lowSupport highSupport scale
          (adaptiveMixedOutcomeSpace familySupport scale)
          lower upper cutoff lowSingular highSingular N targets) :
    (∑ index ∈ scaleAdaptiveBandInteriorIndices m,
      ∑ outcome ∈ samples index,
        scaleAdaptiveBandActualInverseTargetLoad
          familySupport scale lower upper index outcome N target /
          ((adaptiveMixedTypeModulus familySupport *
            adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ)) -
      (scale : ℝ) * cutoff ≤
      ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
        ∑ outcome ∈ samples index,
          scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
            familySupport lowSupport highSupport scale outcome lower upper
              lowSingular highSingular index N target /
            ((adaptiveMixedTypeModulus familySupport *
              adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ) := by
  have denominator_positive :=
    scaleAdaptiveBandOutcomeDenominator_pos familySupport scale primes
  have pointwise :
      ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
        ∀ outcome ∈ samples index,
          scaleAdaptiveBandActualInverseTargetLoad
            familySupport scale lower upper index outcome N target ≤
            scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
              familySupport lowSupport highSupport scale outcome lower upper
                lowSingular highSingular index N target + cutoff := by
    intro index interior outcome sampled
    have comparison :=
      scaleAdaptiveBandActualInverseTargetLoad_le_restricted_add_crossLoss
        familySupport lowSupport highSupport scale outcome lower upper
          lowSingular highSingular index N target
            (sample_active index interior outcome sampled)
    have loss :=
      scaleAdaptiveSignedCrossRejectedActualTargetLoss_lt_of_not_bad
        familySupport lowSupport highSupport scale
          (adaptiveMixedOutcomeSpace familySupport scale)
          outcome lower upper cutoff lowSingular highSingular
            N target targets
              (sample_subset index sampled) target_selected not_bad
    linarith
  have average : ∀ index,
      (∑ _outcome ∈ samples index,
        cutoff /
          ((adaptiveMixedTypeModulus familySupport *
            adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ)) ≤
        cutoff := by
    intro index
    have bound := scaleAdaptiveUniformOutcomeSampleAverage_le_cutoff
      (adaptiveMixedOutcomeSpace familySupport scale)
      (samples index) (fun _ => cutoff) cutoff
      (scaleAdaptiveMixedFullOutcomeSpace_nonempty
        familySupport scale primes)
      (sample_subset index) cutoff_positive.le
      (fun _outcome _selected => le_refl _)
    simpa only [adaptiveMixedOutcomeSpace_card] using bound
  have shell :
      (∑ index ∈ scaleAdaptiveBandInteriorIndices m,
        ∑ outcome ∈ samples index,
          scaleAdaptiveBandActualInverseTargetLoad
            familySupport scale lower upper index outcome N target /
            ((adaptiveMixedTypeModulus familySupport *
              adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ)) ≤
        (∑ index ∈ scaleAdaptiveBandInteriorIndices m,
          ∑ outcome ∈ samples index,
            scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
              familySupport lowSupport highSupport scale outcome lower upper
                lowSingular highSingular index N target /
              ((adaptiveMixedTypeModulus familySupport *
                adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ)) +
          ((scaleAdaptiveBandInteriorIndices m).card : ℝ) * cutoff := by
    calc
      _ ≤ ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
            ((∑ outcome ∈ samples index,
              scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
                familySupport lowSupport highSupport scale outcome lower upper
                  lowSingular highSingular index N target /
                ((adaptiveMixedTypeModulus familySupport *
                  adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ)) +
                cutoff) := by
        apply Finset.sum_le_sum
        intro index interior
        calc
          _ ≤ ∑ outcome ∈ samples index,
                (scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
                  familySupport lowSupport highSupport scale outcome
                    lower upper lowSingular highSingular index N target /
                  ((adaptiveMixedTypeModulus familySupport *
                    adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ) +
                  cutoff /
                    ((adaptiveMixedTypeModulus familySupport *
                      adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ)) := by
            apply Finset.sum_le_sum
            intro outcome sampled
            have divided :=
              (div_le_div_iff_of_pos_right denominator_positive).mpr
                (pointwise index interior outcome sampled)
            convert divided using 1
            ring
          _ =
              (∑ outcome ∈ samples index,
                scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
                  familySupport lowSupport highSupport scale outcome
                    lower upper lowSingular highSingular index N target /
                  ((adaptiveMixedTypeModulus familySupport *
                    adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ)) +
              ∑ _outcome ∈ samples index,
                cutoff /
                  ((adaptiveMixedTypeModulus familySupport *
                    adaptiveMixedOutsideModulus familySupport scale : ℕ) : ℝ) := by
            rw [Finset.sum_add_distrib]
          _ ≤ _ := add_le_add (le_refl _) (average index)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp [mul_comm]
  have cardinal :
      ((scaleAdaptiveBandInteriorIndices m).card : ℝ) ≤ (scale : ℝ) := by
    rw [scaleAdaptiveBandInteriorIndices_card]
    exact_mod_cast (show m - 1 ≤ scale by omega)
  nlinarith [mul_le_mul_of_nonneg_right cardinal cutoff_positive.le]

/-- The PREVIOUSLY PROVED full actual PRIME-target shell load survives
restriction to ONE common low/high label pool, losing at most the explicit
`scale*cutoff` outside a genuine zero-density whole-outcome target union. -/
theorem scaleAdaptiveBandPrimeOutcomeLoad_restricted_ge_full_sub_cutoff
    (familySupport lowSupport highSupport : Finset ℕ)
    (scale m : ℕ) (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N target : ℕ) (targets : Finset ℕ)
    (primes : ∀ prime ∈ familySupport, prime.Prime)
    (physical : 2 * m ≤ scale + 1)
    (cutoff_positive : 0 < cutoff)
    (target_selected : target ∈ targets)
    (not_bad : target ∉
      scaleAdaptiveSignedCrossRejectedFamilyBadTargets
        familySupport lowSupport highSupport scale
          (adaptiveMixedOutcomeSpace familySupport scale)
          lower upper cutoff lowSingular highSingular N targets) :
    scaleAdaptiveBandPrimeOutcomeLoad
      familySupport scale m
        (fun index outcome => scaleAdaptiveBandActualInverseTargetLoad
          familySupport scale lower upper index outcome N) target -
      (scale : ℝ) * cutoff ≤
    scaleAdaptiveBandPrimeOutcomeLoad
      familySupport scale m
        (fun index outcome target =>
          scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
            familySupport lowSupport highSupport scale outcome lower upper
              lowSingular highSingular index N target) target := by
  unfold scaleAdaptiveBandPrimeOutcomeLoad
  exact scaleAdaptiveSignedSampleShellRestrictedLoad_ge_full_sub_cutoff
    familySupport lowSupport highSupport scale m lower upper cutoff
      lowSingular highSingular
        (adaptiveMixedPrimePatternSamples familySupport scale)
        N target targets primes physical cutoff_positive
        (adaptiveMixedPrimePatternSamples_subset_outcomes
          familySupport scale)
        (fun index interior outcome sampled =>
          scaleAdaptiveBandPrimeSample_active_of_physical
            physical interior sampled)
        target_selected not_bad

/-- The PREVIOUSLY PROVED full actual type-`s` SEMIPRIME-target shell
load survives the SAME common low/high label restriction with precisely
the same explicit `scale*cutoff` loss.  Its supported type is retained. -/
theorem scaleAdaptiveBandSemiprimeOutcomeLoad_restricted_ge_full_sub_cutoff
    (familySupport lowSupport highSupport : Finset ℕ)
    (targetType scale m : ℕ) (lower upper cutoff : ℝ)
    (lowSingular highSingular : (ℕ × ℕ) → ℝ)
    (N target : ℕ) (targets : Finset ℕ)
    (primes : ∀ prime ∈ familySupport, prime.Prime)
    (type_supported : targetType ∈ familySupport)
    (physical : 2 * m ≤ scale + 1)
    (cutoff_positive : 0 < cutoff)
    (target_selected : target ∈ targets)
    (not_bad : target ∉
      scaleAdaptiveSignedCrossRejectedFamilyBadTargets
        familySupport lowSupport highSupport scale
          (adaptiveMixedOutcomeSpace familySupport scale)
          lower upper cutoff lowSingular highSingular N targets) :
    scaleAdaptiveBandSemiprimeOutcomeLoad
      familySupport targetType scale m
        (fun index outcome => scaleAdaptiveBandActualInverseTargetLoad
          familySupport scale lower upper index outcome N) target -
      (scale : ℝ) * cutoff ≤
    scaleAdaptiveBandSemiprimeOutcomeLoad
      familySupport targetType scale m
        (fun index outcome target =>
          scaleAdaptiveSignedTwoColorRestrictedIndexedTargetLoad
            familySupport lowSupport highSupport scale outcome lower upper
              lowSingular highSingular index N target) target := by
  unfold scaleAdaptiveBandSemiprimeOutcomeLoad
  exact scaleAdaptiveSignedSampleShellRestrictedLoad_ge_full_sub_cutoff
    familySupport lowSupport highSupport scale m lower upper cutoff
      lowSingular highSingular
        (adaptiveMixedSemiprimePatternSamples
          familySupport targetType scale)
        N target targets primes physical cutoff_positive
        (adaptiveMixedSemiprimePatternSamples_subset_outcomes
          familySupport targetType scale)
        (fun index interior outcome sampled =>
          scaleAdaptiveBandSemiprimeSample_active_of_physical
            type_supported physical interior sampled)
        target_selected not_bad


end Erdos1139
