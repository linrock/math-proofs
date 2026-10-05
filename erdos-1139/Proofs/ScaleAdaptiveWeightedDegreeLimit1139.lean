module

public import ScaleAdaptiveWeightedGTZTransfer1139
public import ScaleAdaptiveGTZDegreeRegularity1139

@[expose] public section


/-!
# Weighted actual-degree transfer and honest shrinking-slice bookkeeping

The exact inverse-degree covering distribution is controlled by its TRUE
weighted residual `∑ₚ μₚ |d(p)/D(p)-1|`.  Whole-dyadic constant profiles are
provably false, so all results here retain label-dependent expectations or
make the error from a genuinely narrow slice explicit.

The finite Cauchy and slice formulas are unconditional.  They do not assume
degree concentration, an extra variance theorem, target covariance, or a
completed covering.  Their eventual smallness still requires the genuine
moving-profile prime-slice variance input from the signed Green--Tao systems.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- Exact weighted actual relative degree residual on any genuine finite set
of labels.  The expected profile may depend on each individual label. -/
noncomputable def scaleAdaptiveWeightedDegreeResidual
    (labels : Finset ℕ)
    (degree mass expected : ℕ → ℝ) : ℝ :=
  ∑ label ∈ labels,
    mass label * |degree label / expected label - 1|

/-- The matching TRUE weighted label-dependent relative quadratic error. -/
noncomputable def scaleAdaptiveWeightedDegreeQuadraticError
    (labels : Finset ℕ)
    (degree mass expected : ℕ → ℝ) : ℝ :=
  ∑ label ∈ labels,
    mass label * (degree label / expected label - 1) ^ 2

/-- Sharp weighted finite Cauchy: true inverse-degree total variation is
bounded by the genuine total pattern mass times the actual moving-profile
quadratic error.  No constant-width or constant-degree model is inserted. -/
theorem scaleAdaptiveWeightedDegreeResidual_sq_le_mass_mul_quadratic
    (labels : Finset ℕ)
    (degree mass expected : ℕ → ℝ)
    (mass_nonnegative : ∀ label ∈ labels, 0 ≤ mass label) :
    (scaleAdaptiveWeightedDegreeResidual
      labels degree mass expected) ^ 2 ≤
      (∑ label ∈ labels, mass label) *
        scaleAdaptiveWeightedDegreeQuadraticError
          labels degree mass expected := by
  unfold scaleAdaptiveWeightedDegreeResidual
    scaleAdaptiveWeightedDegreeQuadraticError
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul labels
  · exact mass_nonnegative
  · intro label selected
    exact mul_nonneg (mass_nonnegative label selected) (sq_nonneg _)
  · intro label _
    rw [mul_pow, sq_abs]
    ring_nf
    rfl

/-- Square-root form of the exact weighted Cauchy bound.  The label-dependent
profile remains arbitrary; the quadratic error is not assumed to vanish. -/
theorem scaleAdaptiveWeightedDegreeResidual_le_sqrt
    (labels : Finset ℕ)
    (degree mass expected : ℕ → ℝ)
    (mass_nonnegative : ∀ label ∈ labels, 0 ≤ mass label) :
    scaleAdaptiveWeightedDegreeResidual
      labels degree mass expected ≤
        Real.sqrt
          ((∑ label ∈ labels, mass label) *
            scaleAdaptiveWeightedDegreeQuadraticError
              labels degree mass expected) := by
  exact Real.le_sqrt_of_sq_le
    (scaleAdaptiveWeightedDegreeResidual_sq_le_mass_mul_quadratic
      labels degree mass expected mass_nonnegative)

/-- The true weighted residual is nonnegative for every genuine nonnegative
pattern-mass distribution. -/
theorem scaleAdaptiveWeightedDegreeResidual_nonnegative
    (labels : Finset ℕ)
    (degree mass expected : ℕ → ℝ)
    (mass_nonnegative : ∀ label ∈ labels, 0 ≤ mass label) :
    0 ≤ scaleAdaptiveWeightedDegreeResidual
      labels degree mass expected := by
  unfold scaleAdaptiveWeightedDegreeResidual
  exact Finset.sum_nonneg fun label selected =>
    mul_nonneg (mass_nonnegative label selected) (abs_nonneg _)

/-- The true weighted quadratic error is nonnegative. -/
theorem scaleAdaptiveWeightedDegreeQuadraticError_nonnegative
    (labels : Finset ℕ)
    (degree mass expected : ℕ → ℝ)
    (mass_nonnegative : ∀ label ∈ labels, 0 ≤ mass label) :
    0 ≤ scaleAdaptiveWeightedDegreeQuadraticError
      labels degree mass expected := by
  unfold scaleAdaptiveWeightedDegreeQuadraticError
  exact Finset.sum_nonneg fun label selected =>
    mul_nonneg (mass_nonnegative label selected) (sq_nonneg _)

/-- Direct genuine physical-target transfer: ALL targetwise errors of the
actual inverse-integer-degree distribution are at most the exact weighted
Cauchy square root, with the full moving prime-label profile retained. -/
theorem scaleAdaptiveSignedInverseDegreeIndexedTarget_totalVariation_le_sqrt
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (mass expected : ℕ → ℝ)
    (mass_nonnegative : ∀ label ∈
      scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N, 0 ≤ mass label)
    (expected_nonzero : ∀ label ∈
      scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N, expected label ≠ 0) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
      |scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
          support scale outcome domain index N mass target -
        scaleAdaptiveSignedModelDegreeIndexedTargetLoad
          support scale outcome domain index N mass expected target|) ≤
      Real.sqrt
        ((∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
          support scale outcome domain N, mass label) *
          scaleAdaptiveWeightedDegreeQuadraticError
            (scaleAdaptiveSignedNonemptyDegreePrimeLabels
              support scale outcome domain N)
            (fun label =>
              (scaleAdaptiveSignedDegree
                support scale outcome domain N label : ℝ))
            mass expected) := by
  calc
    _ ≤ scaleAdaptiveWeightedDegreeResidual
          (scaleAdaptiveSignedNonemptyDegreePrimeLabels
            support scale outcome domain N)
          (fun label =>
            (scaleAdaptiveSignedDegree
              support scale outcome domain N label : ℝ))
          mass expected :=
      scaleAdaptiveSignedInverseDegreeIndexedTarget_totalVariation_le
        support scale outcome domain index N mass expected
          mass_nonnegative expected_nonzero
    _ ≤ _ :=
      scaleAdaptiveWeightedDegreeResidual_le_sqrt
        (scaleAdaptiveSignedNonemptyDegreePrimeLabels
          support scale outcome domain N)
        (fun label =>
          (scaleAdaptiveSignedDegree
            support scale outcome domain N label : ℝ))
        mass expected mass_nonnegative


end Erdos1139
