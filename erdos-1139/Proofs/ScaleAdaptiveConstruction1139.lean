module

public import IndependentConstructionBridge1139

@[expose] public section


/-!
# Joint color-and-residue rounding on one actual prime pool

The scale-adaptive candidate need not first partition its prime labels into
low and high colors with a separate concentration argument.  Instead, each
actual prime independently chooses ONE joint `(color, residue)` option.
Both color-missing events still factor across genuine prime labels, even
though their incidences at one label are mutually exclusive.

This module proves the finite product identity, both exponential marginal
bounds, the simultaneous first-moment selection, exact disjoint realized
supports, heterogeneous prime/semiprime deficiency accounting, and fully
charged conductor reduction.  The resulting explicit analytic colored-
marginal premise remains unproved: no Green--Tao--Ziegler estimate or
unconditional solution of Erdős #1139 is asserted.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Options at one genuine label that simultaneously choose the requested
color and a residue hitting the specified target. -/
def scaleAdaptiveColorHitChoices
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) (p : ↥R) : Finset (Fin k) :=
  Finset.univ.filter fun j =>
    color p j = wanted ∧ residue p j ≡ h [MOD (p : ℕ)]

/-- The complementary joint color/residue options at one actual label. -/
def scaleAdaptiveColorMissChoices
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) (p : ↥R) : Finset (Fin k) :=
  Finset.univ.filter fun j =>
    ¬ (color p j = wanted ∧ residue p j ≡ h [MOD (p : ℕ)])

/-- The genuine color-aware rational hit marginal, already incorporating
the probability of choosing that color at this label. -/
noncomputable def scaleAdaptiveColorHitFraction
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) (p : ↥R) : ℝ :=
  ((scaleAdaptiveColorHitChoices R color residue wanted h p).card : ℝ) /
    (k : ℝ)

/-- Complete coherent label outcomes with no hit of the requested color. -/
def scaleAdaptiveColorMissAssignments
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) : Finset (↥R → Fin k) :=
  Finset.univ.filter fun choice =>
    ∀ p : ↥R,
      ¬ (color p (choice p) = wanted ∧
        residue p (choice p) ≡ h [MOD (p : ℕ)])

/-- Exact finite independence for a color-specific miss; low/high
independence AT ONE LABEL is neither required nor falsely assumed. -/
theorem scaleAdaptiveColorMissAssignments_card
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) :
    (scaleAdaptiveColorMissAssignments R color residue wanted h).card =
      ∏ p : ↥R,
        (scaleAdaptiveColorMissChoices R color residue wanted h p).card := by
  classical
  have exact_product :
      scaleAdaptiveColorMissAssignments R color residue wanted h =
        Fintype.piFinset
          (scaleAdaptiveColorMissChoices R color residue wanted h) := by
    ext choice
    simp [scaleAdaptiveColorMissAssignments, scaleAdaptiveColorMissChoices,
      Fintype.mem_piFinset]
  rw [exact_product, Fintype.card_piFinset]

/-- Every joint option belongs to exactly one color-hit/miss alternative. -/
theorem scaleAdaptiveColorChoices_partition
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) (p : ↥R) :
    (scaleAdaptiveColorHitChoices R color residue wanted h p).card +
      (scaleAdaptiveColorMissChoices R color residue wanted h p).card = k := by
  simpa [scaleAdaptiveColorHitChoices, scaleAdaptiveColorMissChoices] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.univ)
      (fun j : Fin k =>
        color p j = wanted ∧ residue p j ≡ h [MOD (p : ℕ)]))

/-- Actual color-aware marginals lie in the genuine probability interval. -/
theorem scaleAdaptiveColorHitFraction_mem_unitInterval
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) (p : ↥R) :
    0 ≤ scaleAdaptiveColorHitFraction R color residue wanted h p ∧
      scaleAdaptiveColorHitFraction R color residue wanted h p ≤ 1 := by
  unfold scaleAdaptiveColorHitFraction
  constructor
  · positivity
  · have k_positive : (0 : ℝ) < k := by exact_mod_cast positive
    apply (div_le_iff₀ k_positive).mpr
    norm_num only [one_mul]
    have bounded :
        (scaleAdaptiveColorHitChoices R color residue wanted h p).card ≤ k := by
      simpa [scaleAdaptiveColorHitChoices] using
        Finset.card_filter_le (Finset.univ : Finset (Fin k))
          (fun j : Fin k =>
            color p j = wanted ∧ residue p j ≡ h [MOD (p : ℕ)])
    exact_mod_cast bounded

/-- Exact joint-color miss fraction: the product is across actual labels,
and each factor already includes the selected color probability. -/
theorem scaleAdaptiveColorMissFraction_eq_product
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) :
    ((scaleAdaptiveColorMissAssignments R color residue wanted h).card : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ) =
      ∏ p : ↥R,
        (1 - scaleAdaptiveColorHitFraction R color residue wanted h p) := by
  classical
  rw [scaleAdaptiveColorMissAssignments_card, Fintype.card_pi]
  push_cast
  simp only [Fintype.card_fin]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  unfold scaleAdaptiveColorHitFraction
  have partition :=
    scaleAdaptiveColorChoices_partition R color residue wanted h p
  have nonzero : (k : ℝ) ≠ 0 := by
    exact_mod_cast positive.ne'
  have partition_real :
      ((scaleAdaptiveColorHitChoices R color residue wanted h p).card : ℝ) +
        ((scaleAdaptiveColorMissChoices R color residue wanted h p).card : ℝ) =
          (k : ℝ) := by
    exact_mod_cast partition
  field_simp [nonzero]
  linarith

/-- The fully joint color/residue missing probability has its exact
exponential bound with no preliminary deterministic coloring. -/
theorem scaleAdaptiveColorMissFraction_le_exp_neg_hit_load
    {k : ℕ} (positive : 0 < k) (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) :
    ((scaleAdaptiveColorMissAssignments R color residue wanted h).card : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ) ≤
      Real.exp (-(∑ p : ↥R,
        scaleAdaptiveColorHitFraction R color residue wanted h p)) := by
  rw [scaleAdaptiveColorMissFraction_eq_product positive]
  exact Erdos689.finite_one_sub_product_le_exp_neg_sum Finset.univ
    (scaleAdaptiveColorHitFraction R color residue wanted h)
    (fun p _ =>
      scaleAdaptiveColorHitFraction_mem_unitInterval
        positive R color residue wanted h p)

/-- The unique realized color of an actually selected prime label. -/
noncomputable def scaleAdaptiveChosenColor
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (choice : ↥R → Fin k) (p : ℕ) : Bool :=
  if membership : p ∈ R then
    color ⟨p, membership⟩ (choice ⟨p, membership⟩)
  else false

/-- Actual realized color support; each label is selected at most once. -/
noncomputable def scaleAdaptiveRealizedSupport
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (choice : ↥R → Fin k) (wanted : Bool) : Finset ℕ :=
  R.filter fun p => scaleAdaptiveChosenColor R color choice p = wanted

/-- The chosen color is exactly the label's own joint option. -/
theorem scaleAdaptiveChosenColor_apply
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (choice : ↥R → Fin k) (p : ↥R) :
    scaleAdaptiveChosenColor R color choice p = color p (choice p) := by
  simp [scaleAdaptiveChosenColor, p.property]

/-- The realized low/high supports are genuinely disjoint: one prime cannot
produce two hits at a prime target by silently receiving two colors. -/
theorem scaleAdaptiveRealizedSupports_disjoint
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (choice : ↥R → Fin k) :
    Disjoint (scaleAdaptiveRealizedSupport R color choice false)
      (scaleAdaptiveRealizedSupport R color choice true) := by
  apply Finset.disjoint_left.mpr
  intro p low high
  have low_color := (Finset.mem_filter.mp low).2
  have high_color := (Finset.mem_filter.mp high).2
  rw [low_color] at high_color
  cases high_color

/-- Every selected prime belongs to exactly one realized color, so the
actual total conductor is charged on the ORIGINAL common pool. -/
theorem scaleAdaptiveRealizedSupports_union
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (choice : ↥R → Fin k) :
    scaleAdaptiveRealizedSupport R color choice false ∪
      scaleAdaptiveRealizedSupport R color choice true = R := by
  classical
  ext p
  by_cases selected : p ∈ R
  · cases value : scaleAdaptiveChosenColor R color choice p <;>
      simp [scaleAdaptiveRealizedSupport, selected, value]
  · simp [scaleAdaptiveRealizedSupport, selected]

/-- A requested color has no actual fresh-prime hit exactly when the ONE
coherent joint outcome belongs to its product-space missing event. -/
theorem scaleAdaptiveRealizedColor_misses_iff
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (choice : ↥R → Fin k) (wanted : Bool) (h : ℕ) :
    typedCoreFreshHits
        (scaleAdaptiveRealizedSupport R color choice wanted)
        (independentResidueAssignment R residue choice) h = 0 ↔
      choice ∈ scaleAdaptiveColorMissAssignments R color residue wanted h := by
  classical
  change
    ((scaleAdaptiveRealizedSupport R color choice wanted).filter
      fun p =>
        independentResidueAssignment R residue choice p ≡ h [MOD p]).card = 0 ↔ _
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [scaleAdaptiveColorMissAssignments, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro missing p simultaneous
    have selected :
        (p : ℕ) ∈ scaleAdaptiveRealizedSupport R color choice wanted := by
      apply Finset.mem_filter.mpr
      exact ⟨p.property, by
        simpa [scaleAdaptiveChosenColor_apply] using simultaneous.1⟩
    exact missing selected (by
      simpa [independentResidueAssignment_apply] using simultaneous.2)
  · intro missing p selected hit
    obtain ⟨membership, wanted_color⟩ := Finset.mem_filter.mp selected
    let label : ↥R := ⟨p, membership⟩
    apply missing label
    refine ⟨?_, ?_⟩
    · simpa [label, scaleAdaptiveChosenColor, membership] using wanted_color
    · simpa [label, independentResidueAssignment, membership] using hit

/-- Enumerate complete JOINT color-and-residue choices as the nonempty
finite ensemble used by the existing alteration argument. -/
noncomputable def scaleAdaptiveSampleChoice
    {k : ℕ} (R : Finset ℕ)
    (i : Fin (Fintype.card (↥R → Fin k))) : ↥R → Fin k :=
  (Fintype.equivFin (↥R → Fin k)).symm i

/-- The globally coherent actual residue attached to one joint outcome. -/
noncomputable def scaleAdaptiveSampleResidue
    {k : ℕ} (R : Finset ℕ)
    (residue : ↥R → Fin k → ℕ)
    (i : Fin (Fintype.card (↥R → Fin k))) : ℕ → ℕ :=
  independentResidueAssignment R residue (scaleAdaptiveSampleChoice R i)

/-- Realized actual prime labels in one color of one complete outcome. -/
noncomputable def scaleAdaptiveSampleSupport
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (i : Fin (Fintype.card (↥R → Fin k)))
    (wanted : Bool) : Finset ℕ :=
  scaleAdaptiveRealizedSupport R color (scaleAdaptiveSampleChoice R i) wanted

/-- The integer first moment of one color-specific missing indicator is
exactly the cardinality of its independent product-space missing event. -/
theorem scaleAdaptiveSamples_missing_sum_eq_card
    {k : ℕ} (R : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool) (h : ℕ) :
    (∑ i : Fin (Fintype.card (↥R → Fin k)),
      independentColorMissingHit
        (scaleAdaptiveSampleSupport R color i wanted)
        (scaleAdaptiveSampleResidue R residue i) h) =
      (scaleAdaptiveColorMissAssignments R color residue wanted h).card := by
  classical
  unfold scaleAdaptiveSampleSupport scaleAdaptiveSampleResidue
    scaleAdaptiveSampleChoice
  calc
    _ = ∑ choice : (↥R → Fin k),
        independentColorMissingHit
          (scaleAdaptiveRealizedSupport R color choice wanted)
          (independentResidueAssignment R residue choice) h :=
      Equiv.sum_comp (Fintype.equivFin (↥R → Fin k)).symm _
    _ = _ := by
      simp_rw [independentColorMissingHit,
        scaleAdaptiveRealizedColor_misses_iff]
      simp

/-- The exact color-aware exponential budget bounds the actual natural-
number missing first moment on the COMMON label pool. -/
theorem scaleAdaptiveSamples_missing_first_moment_le_of_exp_budget
    {k D : ℕ} (positive : 0 < k) (R targets : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (wanted : Bool)
    (budget :
      (∑ h ∈ targets, Real.exp (-(∑ p : ↥R,
        scaleAdaptiveColorHitFraction R color residue wanted h p))) ≤
          (D : ℝ)) :
    (∑ h ∈ targets,
      ∑ i : Fin (Fintype.card (↥R → Fin k)),
        independentColorMissingHit
          (scaleAdaptiveSampleSupport R color i wanted)
          (scaleAdaptiveSampleResidue R residue i) h) ≤
      Fintype.card (↥R → Fin k) * D := by
  have cardinal_positive :
      (0 : ℝ) < (Fintype.card (↥R → Fin k) : ℝ) := by
    exact_mod_cast independentResidueSampleCard_pos positive R
  have expected :
      (((∑ h ∈ targets,
        ∑ i : Fin (Fintype.card (↥R → Fin k)),
          independentColorMissingHit
            (scaleAdaptiveSampleSupport R color i wanted)
            (scaleAdaptiveSampleResidue R residue i) h) : ℕ) : ℝ) /
        (Fintype.card (↥R → Fin k) : ℝ) ≤ (D : ℝ) := by
    calc
      _ = ∑ h ∈ targets,
          (((∑ i : Fin (Fintype.card (↥R → Fin k)),
            independentColorMissingHit
              (scaleAdaptiveSampleSupport R color i wanted)
              (scaleAdaptiveSampleResidue R residue i) h) : ℕ) : ℝ) /
            (Fintype.card (↥R → Fin k) : ℝ) := by
              push_cast
              rw [Finset.sum_div]
      _ ≤ ∑ h ∈ targets, Real.exp (-(∑ p : ↥R,
          scaleAdaptiveColorHitFraction R color residue wanted h p)) := by
            apply Finset.sum_le_sum
            intro h _
            rw [scaleAdaptiveSamples_missing_sum_eq_card]
            exact scaleAdaptiveColorMissFraction_le_exp_neg_hit_load
              positive R color residue wanted h
      _ ≤ (D : ℝ) := budget
  have multiplied := (div_le_iff₀ cardinal_positive).mp expected
  rw [mul_comm] at multiplied
  exact_mod_cast multiplied

/-- Every individual complete outcome has its exact heterogeneous deficit
bounded by its TWO realized disjoint-color missing counts. -/
theorem scaleAdaptiveSample_missing_hit_total_le
    {y z k : ℕ} (R lowTargets highTargets exceptions : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (i : Fin (Fintype.card (↥R → Fin k)))
    (low_supported : lowTargets ⊆ Finset.Icc 1 y)
    (high_supported : highTargets ⊆ Finset.Icc 1 y)
    (exceptions_supported : exceptions ⊆ Finset.Icc 1 y)
    (demand : ∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
      2 ≤ fixedParameterCoreHits y z h +
        (if h ∈ lowTargets then 1 else 0) +
        (if h ∈ highTargets then 1 else 0)) :
    typedCoreMissingHitTotal y z R
        (scaleAdaptiveSampleResidue R residue i) ≤
      2 * exceptions.card +
        (∑ h ∈ lowTargets,
          independentColorMissingHit
            (scaleAdaptiveSampleSupport R color i false)
            (scaleAdaptiveSampleResidue R residue i) h) +
        (∑ h ∈ highTargets,
          independentColorMissingHit
            (scaleAdaptiveSampleSupport R color i true)
            (scaleAdaptiveSampleResidue R residue i) h) := by
  let low := scaleAdaptiveSampleSupport R color i false
  let high := scaleAdaptiveSampleSupport R color i true
  let assignment := scaleAdaptiveSampleResidue R residue i
  have disjoint : Disjoint low high :=
    scaleAdaptiveRealizedSupports_disjoint R color
      (scaleAdaptiveSampleChoice R i)
  have union : low ∪ high = R :=
    scaleAdaptiveRealizedSupports_union R color
      (scaleAdaptiveSampleChoice R i)
  have glued :
      independentTwoColorGluedResidue low assignment assignment = assignment := by
    funext p
    simp [independentTwoColorGluedResidue]
  have estimate := independentTwoColor_missing_hit_total_le
    low high lowTargets highTargets exceptions assignment assignment
    disjoint low_supported high_supported exceptions_supported demand
  rw [union, glued] at estimate
  exact estimate

/-- BOTH color budgets hold in the SAME independent sample ensemble.
Therefore their sum controls the genuine prime-versus-semiprime missing-hit
first moment; no independently chosen outcomes are glued afterwards. -/
theorem scaleAdaptiveSamples_missing_hit_first_moment_le
    {y z k DLow DHigh : ℕ}
    (R lowTargets highTargets exceptions : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (positive : 0 < k)
    (low_supported : lowTargets ⊆ Finset.Icc 1 y)
    (high_supported : highTargets ⊆ Finset.Icc 1 y)
    (exceptions_supported : exceptions ⊆ Finset.Icc 1 y)
    (demand : ∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
      2 ≤ fixedParameterCoreHits y z h +
        (if h ∈ lowTargets then 1 else 0) +
        (if h ∈ highTargets then 1 else 0))
    (low_budget :
      (∑ h ∈ lowTargets, Real.exp (-(∑ p : ↥R,
        scaleAdaptiveColorHitFraction R color residue false h p))) ≤
          (DLow : ℝ))
    (high_budget :
      (∑ h ∈ highTargets, Real.exp (-(∑ p : ↥R,
        scaleAdaptiveColorHitFraction R color residue true h p))) ≤
          (DHigh : ℝ)) :
    (∑ h ∈ Finset.Icc 1 y,
      ∑ i : Fin (Fintype.card (↥R → Fin k)),
        typedCoreMissingHits y z R
          (scaleAdaptiveSampleResidue R residue i) h) ≤
      Fintype.card (↥R → Fin k) *
        (DLow + DHigh + 2 * exceptions.card) := by
  classical
  let K : ℕ := Fintype.card (↥R → Fin k)
  have low_first :=
    scaleAdaptiveSamples_missing_first_moment_le_of_exp_budget
      positive R lowTargets color residue false low_budget
  have high_first :=
    scaleAdaptiveSamples_missing_first_moment_le_of_exp_budget
      positive R highTargets color residue true high_budget
  have low_swapped :
      (∑ i : Fin K, ∑ h ∈ lowTargets,
        independentColorMissingHit
          (scaleAdaptiveSampleSupport R color i false)
          (scaleAdaptiveSampleResidue R residue i) h) ≤ K * DLow := by
    change
      (∑ i : Fin (Fintype.card (↥R → Fin k)), ∑ h ∈ lowTargets,
        independentColorMissingHit
          (scaleAdaptiveSampleSupport R color i false)
          (scaleAdaptiveSampleResidue R residue i) h) ≤
        Fintype.card (↥R → Fin k) * DLow
    rw [Finset.sum_comm]
    exact low_first
  have high_swapped :
      (∑ i : Fin K, ∑ h ∈ highTargets,
        independentColorMissingHit
          (scaleAdaptiveSampleSupport R color i true)
          (scaleAdaptiveSampleResidue R residue i) h) ≤ K * DHigh := by
    change
      (∑ i : Fin (Fintype.card (↥R → Fin k)), ∑ h ∈ highTargets,
        independentColorMissingHit
          (scaleAdaptiveSampleSupport R color i true)
          (scaleAdaptiveSampleResidue R residue i) h) ≤
        Fintype.card (↥R → Fin k) * DHigh
    rw [Finset.sum_comm]
    exact high_first
  rw [← typedCore_missing_hit_first_moment_identity]
  change
    (∑ i : Fin K,
      typedCoreMissingHitTotal y z R
        (scaleAdaptiveSampleResidue R residue i)) ≤
      K * (DLow + DHigh + 2 * exceptions.card)
  calc
    _ ≤ ∑ i : Fin K,
        (2 * exceptions.card +
          (∑ h ∈ lowTargets,
            independentColorMissingHit
              (scaleAdaptiveSampleSupport R color i false)
              (scaleAdaptiveSampleResidue R residue i) h) +
          (∑ h ∈ highTargets,
            independentColorMissingHit
              (scaleAdaptiveSampleSupport R color i true)
              (scaleAdaptiveSampleResidue R residue i) h)) := by
      apply Finset.sum_le_sum
      intro i _
      exact scaleAdaptiveSample_missing_hit_total_le
        R lowTargets highTargets exceptions color residue i
        low_supported high_supported exceptions_supported demand
    _ = K * (2 * exceptions.card) +
        (∑ i : Fin K, ∑ h ∈ lowTargets,
          independentColorMissingHit
            (scaleAdaptiveSampleSupport R color i false)
            (scaleAdaptiveSampleResidue R residue i) h) +
        (∑ i : Fin K, ∑ h ∈ highTargets,
          independentColorMissingHit
            (scaleAdaptiveSampleSupport R color i true)
            (scaleAdaptiveSampleResidue R residue i) h) := by
      simp_rw [Finset.sum_add_distrib]
      simp
    _ ≤ K * (2 * exceptions.card) + K * DLow + K * DHigh := by
      omega
    _ = K * (DLow + DHigh + 2 * exceptions.card) := by ring

/-- ONE jointly sampled actual color/residue assignment simultaneously
controls both color deficits.  Its two realized prime supports are disjoint,
their union is precisely the charged original pool, and prime targets cannot
receive two hits from a duplicated prime. -/
theorem exists_scaleAdaptive_joint_assignment_of_exp_budgets
    {y z k DLow DHigh : ℕ}
    (R lowTargets highTargets exceptions : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (positive : 0 < k)
    (low_supported : lowTargets ⊆ Finset.Icc 1 y)
    (high_supported : highTargets ⊆ Finset.Icc 1 y)
    (exceptions_supported : exceptions ⊆ Finset.Icc 1 y)
    (demand : ∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
      2 ≤ fixedParameterCoreHits y z h +
        (if h ∈ lowTargets then 1 else 0) +
        (if h ∈ highTargets then 1 else 0))
    (low_budget :
      (∑ h ∈ lowTargets, Real.exp (-(∑ p : ↥R,
        scaleAdaptiveColorHitFraction R color residue false h p))) ≤
          (DLow : ℝ))
    (high_budget :
      (∑ h ∈ highTargets, Real.exp (-(∑ p : ↥R,
        scaleAdaptiveColorHitFraction R color residue true h p))) ≤
          (DHigh : ℝ)) :
    ∃ choice : ↥R → Fin k,
      Disjoint (scaleAdaptiveRealizedSupport R color choice false)
        (scaleAdaptiveRealizedSupport R color choice true) ∧
      scaleAdaptiveRealizedSupport R color choice false ∪
        scaleAdaptiveRealizedSupport R color choice true = R ∧
      typedCoreMissingHitTotal y z R
          (independentResidueAssignment R residue choice) ≤
        DLow + DHigh + 2 * exceptions.card := by
  let samples : Fin (Fintype.card (↥R → Fin k)) → ℕ → ℕ :=
    scaleAdaptiveSampleResidue R residue
  have first_moment := scaleAdaptiveSamples_missing_hit_first_moment_le
    R lowTargets highTargets exceptions color residue positive
    low_supported high_supported exceptions_supported demand
    low_budget high_budget
  obtain ⟨i, deficit⟩ :=
    exists_typedCore_assignment_of_missing_hit_first_moment
      samples (independentResidueSampleCard_pos positive R) first_moment
  let choice := scaleAdaptiveSampleChoice R i
  refine ⟨choice,
    scaleAdaptiveRealizedSupports_disjoint R color choice,
    scaleAdaptiveRealizedSupports_union R color choice, ?_⟩
  exact deficit

/-- Exact finite end-to-end construction from a COMMON prime pool with
joint color/residue options.  The original pool is charged ONCE, all
exceptional cleanup slots are charged twice, and no preliminary random
coloring concentration, matching theorem, or hypergraph input is used. -/
theorem scaleAdaptive_complete_cover_of_joint_exp_budgets
    {y z k DLow DHigh B : ℕ}
    (R lowTargets highTargets exceptions : Finset ℕ)
    (color : ↥R → Fin k → Bool)
    (residue : ↥R → Fin k → ℕ)
    (positive : 0 < k)
    (low_supported : lowTargets ⊆ Finset.Icc 1 y)
    (high_supported : highTargets ⊆ Finset.Icc 1 y)
    (exceptions_supported : exceptions ⊆ Finset.Icc 1 y)
    (demand : ∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
      2 ≤ fixedParameterCoreHits y z h +
        (if h ∈ lowTargets then 1 else 0) +
        (if h ∈ highTargets then 1 else 0))
    (low_budget :
      (∑ h ∈ lowTargets, Real.exp (-(∑ p : ↥R,
        scaleAdaptiveColorHitFraction R color residue false h p))) ≤
          (DLow : ℝ))
    (high_budget :
      (∑ h ∈ highTargets, Real.exp (-(∑ p : ↥R,
        scaleAdaptiveColorHitFraction R color residue true h p))) ≤
          (DHigh : ℝ))
    (reserve_primes : ∀ p ∈ R, p.Prime)
    (fresh : Disjoint (fixedParameterCorePrimes y z) R)
    (cleanup_bound_positive : 1 ≤ B)
    (cleanup_supply :
      2 * (DLow + DHigh + 2 * exceptions.card) +
        ((fixedParameterCorePrimes y z) ∪ R).card ≤ Nat.primeCounting B) :
    ∃ (completed squared : Finset ℕ) (assignment : ℕ → ℕ),
      UnrestrictedPrimeSquareDoubleCover y completed squared assignment ∧
      Real.log
        ((∏ p ∈ completed, selectedPrimePower squared p : ℕ) : ℝ) ≤
        Real.log
          ((∏ p ∈ fixedParameterCorePrimes y z,
            selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) +
          Real.log ((∏ p ∈ R, p : ℕ) : ℝ) +
          (2 * ((DLow + DHigh + 2 * exceptions.card : ℕ) : ℝ)) *
            Real.log (B : ℝ) := by
  apply typedCore_complete_cover_of_missing_hit_first_moment
    (D := DLow + DHigh + 2 * exceptions.card)
    (B := B) (scaleAdaptiveSampleResidue R residue)
    (independentResidueSampleCard_pos positive R)
    reserve_primes fresh cleanup_bound_positive cleanup_supply
  exact scaleAdaptiveSamples_missing_hit_first_moment_le
    R lowTargets highTargets exceptions color residue positive
    low_supported high_supported exceptions_supported demand
    low_budget high_budget

/-- The explicit remaining analytic input for JOINT color-and-residue
rounding.  Unlike the prior two-pool premise, it asks for only ONE actual
fresh prime pool and one finite list of mutually exclusive colored residue
options per prime.  Both targetwise budgets incorporate the actual color
probability.  No deterministic pre-coloring, concentration inequality,
small-individual-marginal bound, selected matching, or complete cover occurs
among its hypotheses.

The required fixed-parameter prime-pattern estimates are NOT proved here.
In particular, this proposition must not be mistaken for an unconditional
solution of Erdős #1139. -/
def HasSublinearJointColoredMarginals : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ z : ℕ, 0 < z ∧ (z : ℝ)⁻¹ < ε ∧
      ∀ᶠ y : ℕ in atTop,
        ∃ (R lowTargets highTargets exceptions : Finset ℕ)
          (k B DLow DHigh : ℕ)
          (color : ↥R → Fin k → Bool)
          (residue : ↥R → Fin k → ℕ),
          0 < k ∧ 1 ≤ B ∧
          (∀ p ∈ R, p.Prime) ∧
          Disjoint (fixedParameterCorePrimes y z) R ∧
          lowTargets ⊆ Finset.Icc 1 y ∧
          highTargets ⊆ Finset.Icc 1 y ∧
          exceptions ⊆ Finset.Icc 1 y ∧
          (∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
            2 ≤ fixedParameterCoreHits y z h +
              (if h ∈ lowTargets then 1 else 0) +
              (if h ∈ highTargets then 1 else 0)) ∧
          (∑ h ∈ lowTargets, Real.exp (-(∑ p : ↥R,
            scaleAdaptiveColorHitFraction R color residue false h p))) ≤
              (DLow : ℝ) ∧
          (∑ h ∈ highTargets, Real.exp (-(∑ p : ↥R,
            scaleAdaptiveColorHitFraction R color residue true h p))) ≤
              (DHigh : ℝ) ∧
          2 * (DLow + DHigh + 2 * exceptions.card) +
            ((fixedParameterCorePrimes y z) ∪ R).card ≤
              Nat.primeCounting B ∧
          Real.log ((∏ p ∈ R, p : ℕ) : ℝ) +
            (2 * ((DLow + DHigh + 2 * exceptions.card : ℕ) : ℝ)) *
              Real.log (B : ℝ) ≤ ε * (y : ℝ)

/-- The COMMON-pool colored marginal premise yields the existing exact
coherent first-moment/alteration hypothesis directly.  No concentration
theorem intervenes, and the original prime pool is charged only once. -/
theorem averaged_typed_core_data_of_joint_colored_marginals
    (marginals : HasSublinearJointColoredMarginals) :
    HasSublinearAveragedTypedCoreData := by
  intro ε positive
  obtain ⟨z, z_positive, inverse_small, eventually_data⟩ :=
    marginals ε positive
  refine ⟨z, z_positive, inverse_small, ?_⟩
  filter_upwards [eventually_data] with y data
  obtain ⟨R, lowTargets, highTargets, exceptions, k, B, DLow, DHigh,
    color, residue, options_positive, cleanup_positive, reserve_primes,
    fresh, low_supported, high_supported, exceptions_supported,
    demand, low_budget, high_budget, cleanup_supply, auxiliary_cost⟩ := data
  refine ⟨R, B, DLow + DHigh + 2 * exceptions.card,
    Fintype.card (↥R → Fin k), scaleAdaptiveSampleResidue R residue,
    reserve_primes, fresh, cleanup_positive,
    independentResidueSampleCard_pos options_positive R,
    cleanup_supply, ?_, auxiliary_cost⟩
  exact scaleAdaptiveSamples_missing_hit_first_moment_le
    R lowTargets highTargets exceptions color residue options_positive
    low_supported high_supported exceptions_supported demand
    low_budget high_budget

/-- The exact actual-conductor covering obstruction follows from the single
COMMON-pool joint colored-prime marginal estimate. -/
theorem sublinear_unrestricted_conductors_of_joint_colored_marginals
    (marginals : HasSublinearJointColoredMarginals) :
    HasSublinearUnrestrictedConductorCovers :=
  sublinear_unrestricted_conductors_of_averaged_typed_core_data
    (averaged_typed_core_data_of_joint_colored_marginals marginals)

/-- CONDITIONAL exact historical Erdős #1139 statement from the single
shared-prime-pool colored marginal hypothesis.  The `Nat.nth` predicate,
multiplicity-counting `Ω`, real `log(k+1)` denominator, successor index,
and extended-real infinite limsup are the literal upstream formulation.
The analytic antecedent remains unproved; no full solution is claimed. -/
theorem original_normalized_limsup_top_of_joint_colored_marginals
    (marginals : HasSublinearJointColoredMarginals) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_averaged_typed_core_data
    (averaged_typed_core_data_of_joint_colored_marginals marginals)


end Erdos1139
