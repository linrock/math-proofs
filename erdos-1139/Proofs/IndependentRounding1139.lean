module

public import ConstructionAttack1139
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section


/-!
# Exact independent residue rounding for Erdős problem #1139

The adaptive prime-pattern argument chooses at most one globally coherent
residue for each genuine prime label.  Distinct labels are randomized
independently, so the exact fraction of assignments missing a specified
target is the PRODUCT of their individual miss fractions, and is at most
the exponential of the negative sum of their hit probabilities.

This module proves that finite rounding kernel without a hypergraph
matching theorem or a probabilistic axiom.  Labels are the actual members
of a prime finset; each has finitely many equally weighted residue choices,
which also represent arbitrary rational weights by repetition.  Two disjoint
label colors contribute two genuinely distinct prime hits; a one-hit
semiprime and a two-hit prime retain their exact heterogeneous deficits.

The required high-rank fixed-parameter Green--Tao--Ziegler prime-pattern
estimates are NOT proved or assumed here.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- One complete product-space outcome assigns exactly one residue to each
actual label; outside the selected support its value is harmlessly zero. -/
noncomputable def independentResidueAssignment
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (choice : ↥R → Fin k) (p : ℕ) : ℕ :=
  if membership : p ∈ R then
    residue ⟨p, membership⟩ (choice ⟨p, membership⟩)
  else 0

/-- Evaluation on a genuinely selected label uses its own single chosen
option and no assignment made independently for another target. -/
theorem independentResidueAssignment_apply
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (choice : ↥R → Fin k) (p : ↥R) :
    independentResidueAssignment R residue choice p =
      residue p (choice p) := by
  simp [independentResidueAssignment, p.property]

/-- The actual residue options for one label that hit a given target. -/
def independentResidueHitChoices
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (h : ℕ) (p : ↥R) : Finset (Fin k) :=
  Finset.univ.filter fun j => residue p j ≡ h [MOD (p : ℕ)]

/-- The complementary residue options for the same actual label. -/
def independentResidueMissChoices
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (h : ℕ) (p : ↥R) : Finset (Fin k) :=
  Finset.univ.filter fun j => ¬ residue p j ≡ h [MOD (p : ℕ)]

/-- The finite product-space outcomes in which every selected prime misses
the target under its one coherent chosen residue. -/
def independentResidueMissAssignments
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (h : ℕ) : Finset (↥R → Fin k) :=
  Finset.univ.filter fun choice =>
    ∀ p : ↥R, ¬ residue p (choice p) ≡ h [MOD (p : ℕ)]

/-- The abstract product-space missing event is EXACTLY the event that the
actual, globally coherent chosen residue assignment contributes no fresh
prime hit to the target. -/
theorem independentResidueAssignment_misses_iff
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (choice : ↥R → Fin k) (h : ℕ) :
    typedCoreFreshHits R
      (independentResidueAssignment R residue choice) h = 0 ↔
      choice ∈ independentResidueMissAssignments R residue h := by
  classical
  change
    (R.filter fun p =>
      independentResidueAssignment R residue choice p ≡ h [MOD p]).card = 0 ↔ _
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [independentResidueMissAssignments, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro missing p
    simpa [independentResidueAssignment_apply] using
      (missing p.property)
  · intro missing p selected
    simpa [independentResidueAssignment, selected] using
      (missing (⟨p, selected⟩ : ↥R))

/-- The missing outcomes are exactly the finite Cartesian product of the
individual label-wise missing-option sets. -/
theorem independentResidueMissAssignments_eq_piFinset
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (h : ℕ) :
    independentResidueMissAssignments R residue h =
      Fintype.piFinset (independentResidueMissChoices R residue h) := by
  classical
  ext choice
  simp [independentResidueMissAssignments, independentResidueMissChoices,
    Fintype.mem_piFinset]

/-- Exact integer independence: the number of fully coherent assignments
missing a target is the product of the genuine per-label miss counts. -/
theorem independentResidueMissAssignments_card
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (h : ℕ) :
    (independentResidueMissAssignments R residue h).card =
      ∏ p : ↥R, (independentResidueMissChoices R residue h p).card := by
  rw [independentResidueMissAssignments_eq_piFinset,
    Fintype.card_piFinset]

/-- A label's hitting and missing option counts partition its exact common
finite choice denominator. -/
theorem independentResidueChoices_partition
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (h : ℕ) (p : ↥R) :
    (independentResidueHitChoices R residue h p).card +
      (independentResidueMissChoices R residue h p).card = k := by
  simpa [independentResidueHitChoices, independentResidueMissChoices]
    using (Finset.card_filter_add_card_filter_not
      (s := Finset.univ)
      (fun j : Fin k => residue p j ≡ h [MOD (p : ℕ)]))

/-- The exact rational-in-real hit marginal of one label. -/
noncomputable def independentResidueHitFraction
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (h : ℕ) (p : ↥R) : ℝ :=
  ((independentResidueHitChoices R residue h p).card : ℝ) / (k : ℝ)

/-- For a nonempty choice set, every genuine hit marginal lies in `[0,1]`. -/
theorem independentResidueHitFraction_mem_unitInterval
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (h : ℕ) (p : ↥R) :
    0 ≤ independentResidueHitFraction R residue h p ∧
      independentResidueHitFraction R residue h p ≤ 1 := by
  unfold independentResidueHitFraction
  constructor
  · positivity
  · have kpositive : (0 : ℝ) < k := by exact_mod_cast positive
    apply (div_le_iff₀ kpositive).mpr
    norm_num only [one_mul]
    have bound :
        (independentResidueHitChoices R residue h p).card ≤ k := by
      simpa [independentResidueHitChoices] using
        Finset.card_filter_le (Finset.univ : Finset (Fin k))
          (fun j : Fin k => residue p j ≡ h [MOD (p : ℕ)])
    exact_mod_cast bound

/-- The exact fraction of complete independently sampled coherent
assignments missing a target is the product of one minus every actual
per-prime hit marginal. -/
theorem independentResidueMissFraction_eq_product
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (h : ℕ) :
    ((independentResidueMissAssignments R residue h).card : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ) =
      ∏ p : ↥R, (1 - independentResidueHitFraction R residue h p) := by
  classical
  rw [independentResidueMissAssignments_card, Fintype.card_pi]
  push_cast
  simp only [Fintype.card_fin]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  unfold independentResidueHitFraction
  have partition := independentResidueChoices_partition R residue h p
  have k_nonzero : (k : ℝ) ≠ 0 := by
    exact_mod_cast positive.ne'
  have partition_real :
      ((independentResidueHitChoices R residue h p).card : ℝ) +
        ((independentResidueMissChoices R residue h p).card : ℝ) =
          (k : ℝ) := by
    exact_mod_cast partition
  field_simp [k_nonzero]
  linarith

/-- The finite independent-residue rounding bound: target noncoverage is
at most `exp(-sum of actual hit marginals)`.  This reuses the already
kernel-checked elementary exponential-product lemma from problem #689. -/
theorem independentResidueMissFraction_le_exp_neg_hit_load
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (h : ℕ) :
    ((independentResidueMissAssignments R residue h).card : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ) ≤
      Real.exp (-(∑ p : ↥R,
        independentResidueHitFraction R residue h p)) := by
  rw [independentResidueMissFraction_eq_product positive]
  exact Erdos689.finite_one_sub_product_le_exp_neg_sum
    Finset.univ (independentResidueHitFraction R residue h)
      (fun p _ =>
        independentResidueHitFraction_mem_unitInterval
          positive R residue h p)

/-- Actual fresh-hit counts add across disjoint genuine label colors; a
prime label is never silently counted twice. -/
theorem typedCoreFreshHits_union_of_disjoint
    (low high : Finset ℕ) (b : ℕ → ℕ) (h : ℕ)
    (disjoint : Disjoint low high) :
    typedCoreFreshHits (low ∪ high) b h =
      typedCoreFreshHits low b h + typedCoreFreshHits high b h := by
  unfold typedCoreFreshHits
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter disjoint)]

/-- A colored target misses its designated prime-color hit exactly when its
actual genuine-prime hit count is zero. -/
def independentColorMissingHit
    (R : Finset ℕ) (b : ℕ → ℕ) (h : ℕ) : ℕ :=
  if typedCoreFreshHits R b h = 0 then 1 else 0

/-- Enumerate the entire independent product space as the actual `Fin K`
ensemble accepted by the already verified first-moment/cleanup theorem. -/
noncomputable def independentResidueSamples
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (i : Fin (Fintype.card (↥R → Fin k))) : ℕ → ℕ :=
  independentResidueAssignment R residue
    ((Fintype.equivFin (↥R → Fin k)).symm i)

/-- The actual ensemble contains exactly `k ^ #R` complete assignments. -/
theorem independentResidueSampleCard
    {k : ℕ} (R : Finset ℕ) :
    Fintype.card (↥R → Fin k) = k ^ R.card := by
  classical
  simp

/-- A nonempty local choice set produces a genuinely nonempty ensemble,
including when there are no selected labels. -/
theorem independentResidueSampleCard_pos
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ) :
    0 < Fintype.card (↥R → Fin k) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨fun _ => ⟨0, positive⟩⟩

/-- Exact integer first moment: enumerating COMPLETE coherent assignments
counts the target's one-color missing indicator exactly as many times as
there are product-space outcomes missing that target. -/
theorem independentResidueSamples_missing_sum_eq_card
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (h : ℕ) :
    (∑ i : Fin (Fintype.card (↥R → Fin k)),
      independentColorMissingHit R
        (independentResidueSamples R residue i) h) =
      (independentResidueMissAssignments R residue h).card := by
  classical
  unfold independentResidueSamples
  calc
    _ = ∑ choice : (↥R → Fin k),
        independentColorMissingHit R
          (independentResidueAssignment R residue choice) h :=
      Equiv.sum_comp (Fintype.equivFin (↥R → Fin k)).symm _
    _ = _ := by
      simp_rw [independentColorMissingHit,
        independentResidueAssignment_misses_iff]
      simp

/-- The finite first moment accepted by the cleanup development has the
exact independently rounded exponential noncoverage bound. -/
theorem independentResidueSamples_missing_fraction_le_exp_neg_hit_load
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (h : ℕ) :
    (((∑ i : Fin (Fintype.card (↥R → Fin k)),
      independentColorMissingHit R
        (independentResidueSamples R residue i) h) : ℕ) : ℝ) /
      (Fintype.card (↥R → Fin k) : ℝ) ≤
        Real.exp (-(∑ p : ↥R,
          independentResidueHitFraction R residue h p)) := by
  rw [independentResidueSamples_missing_sum_eq_card]
  exact independentResidueMissFraction_le_exp_neg_hit_load
    positive R residue h

/-- Sum the actual coherent-assignment first moment over any finite target
set; no target-wise inconsistent residue assignment or independence between
targets is introduced. -/
theorem independentResidueSamples_missing_first_moment_le_exp
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (targets : Finset ℕ) :
    (∑ h ∈ targets,
      (((∑ i : Fin (Fintype.card (↥R → Fin k)),
        independentColorMissingHit R
          (independentResidueSamples R residue i) h) : ℕ) : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ)) ≤
      ∑ h ∈ targets, Real.exp (-(∑ p : ↥R,
        independentResidueHitFraction R residue h p)) := by
  apply Finset.sum_le_sum
  intro h _
  exact independentResidueSamples_missing_fraction_le_exp_neg_hit_load
    positive R residue h

/-- A real exponential budget yields the exact NATURAL-NUMBER first-moment
budget required by the pre-existing deterministic alteration theorem. -/
theorem independentResidueSamples_missing_first_moment_le_of_exp_budget
    {k D : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (targets : Finset ℕ)
    (budget :
      (∑ h ∈ targets, Real.exp (-(∑ p : ↥R,
        independentResidueHitFraction R residue h p))) ≤ (D : ℝ)) :
    (∑ h ∈ targets,
      ∑ i : Fin (Fintype.card (↥R → Fin k)),
        independentColorMissingHit R
          (independentResidueSamples R residue i) h) ≤
      Fintype.card (↥R → Fin k) * D := by
  have cardinal_positive :
      (0 : ℝ) < (Fintype.card (↥R → Fin k) : ℝ) := by
    exact_mod_cast independentResidueSampleCard_pos positive R
  have expected :
      (((∑ h ∈ targets,
        ∑ i : Fin (Fintype.card (↥R → Fin k)),
          independentColorMissingHit R
            (independentResidueSamples R residue i) h) : ℕ) : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ) ≤ (D : ℝ) := by
    calc
      _ = ∑ h ∈ targets,
          (((∑ i : Fin (Fintype.card (↥R → Fin k)),
            independentColorMissingHit R
              (independentResidueSamples R residue i) h) : ℕ) : ℝ) /
            (Fintype.card (↥R → Fin k) : ℝ) := by
              push_cast
              rw [Finset.sum_div]
      _ ≤ ∑ h ∈ targets, Real.exp (-(∑ p : ↥R,
          independentResidueHitFraction R residue h p)) :=
            independentResidueSamples_missing_first_moment_le_exp
              positive R residue targets
      _ ≤ (D : ℝ) := budget
  have multiplied := (div_le_iff₀ cardinal_positive).mp expected
  rw [mul_comm] at multiplied
  exact_mod_cast multiplied

/-- The summed exponential bound selects ONE actual globally coherent
residue assignment with at most the advertised number of missed targets.
Low and high colors can therefore be optimized separately and glued along
their disjoint prime supports, with no matching or projection theorem. -/
theorem exists_independentResidueSample_with_missing_targets_le_of_exp_budget
    {k D : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ) (targets : Finset ℕ)
    (budget :
      (∑ h ∈ targets, Real.exp (-(∑ p : ↥R,
        independentResidueHitFraction R residue h p))) ≤ (D : ℝ)) :
    ∃ i : Fin (Fintype.card (↥R → Fin k)),
      (∑ h ∈ targets,
        independentColorMissingHit R
          (independentResidueSamples R residue i) h) ≤ D := by
  classical
  have average :=
    independentResidueSamples_missing_first_moment_le_of_exp_budget
      positive R residue targets budget
  rw [Finset.sum_comm] at average
  have nonempty := independentResidueSampleCard_pos positive R
  by_contra absent
  have pointwise : ∀ i : Fin (Fintype.card (↥R → Fin k)),
      D + 1 ≤ ∑ h ∈ targets,
        independentColorMissingHit R
          (independentResidueSamples R residue i) h := by
    intro i
    have not_small : ¬ (∑ h ∈ targets,
        independentColorMissingHit R
          (independentResidueSamples R residue i) h) ≤ D := by
      intro small
      exact absent ⟨i, small⟩
    omega
  have lower := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => pointwise i)
  have lower' :
      Fintype.card (↥R → Fin k) * (D + 1) ≤
        ∑ i : Fin (Fintype.card (↥R → Fin k)),
          ∑ h ∈ targets,
            independentColorMissingHit R
              (independentResidueSamples R residue i) h := by
    simpa using lower
  rw [Nat.mul_add, Nat.mul_one] at lower'
  omega

/-- A target already carrying one old-core hit (the relevant semiprime
case) needs at most its designated single color's missing-hit indicator. -/
theorem typedCoreMissingHits_le_single_color_miss
    {y z h : ℕ} (R : Finset ℕ) (b : ℕ → ℕ)
    (core_hit : 1 ≤ fixedParameterCoreHits y z h) :
    typedCoreMissingHits y z R b h ≤
      independentColorMissingHit R b h := by
  unfold typedCoreMissingHits independentColorMissingHit
  split_ifs <;> omega

/-- Two disjoint label colors supply two DISTINCT genuine prime hits.  The
exact two-hit deficit of a prime target is at most the sum of its two
independent one-color missing indicators. -/
theorem typedCoreMissingHits_le_two_color_misses
    {y z h : ℕ} (low high : Finset ℕ) (b : ℕ → ℕ)
    (disjoint : Disjoint low high) :
    typedCoreMissingHits y z (low ∪ high) b h ≤
      independentColorMissingHit low b h +
        independentColorMissingHit high b h := by
  unfold typedCoreMissingHits
  rw [typedCoreFreshHits_union_of_disjoint low high b h disjoint]
  unfold independentColorMissingHit
  split_ifs <;> omega


end Erdos1139
