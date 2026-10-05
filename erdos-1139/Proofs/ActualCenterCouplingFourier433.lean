module

public import ActualMajorArcGlobalErrorAssembly433
public import ActualMajorArcCenterReduction433
public import ActualMajorArcParityCRT433
public import ActualMajorArcPositivityFinal433

@[expose] public section


/-!
# Exact Fourier reduction of genuine deduplicated major centers

The true major-center expansion uses the canonical ORIGINAL widest anchor,
its complete signed support-switched unit-cell phase, and its genuine
denominator-dependent clipped arc.  This file factors that full smooth
model exactly, isolates the signed exceptional family from the global model,
and computes the interior center integral as its true signed affine lattice
main term minus its retained resonant middle tail.

No positive sign, outside-conductor CRT identity, discarded boundary lift, or
uniform singular-model coupling is asserted without proof.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The full genuinely signed coefficient of one original major anchor.
It retains all three actual switched/unit common-modulus selectors and the
exact shifted effective numerator, normalized by the TRUE common totient. -/
noncomputable def actualCenterCouplingAnchorCoefficient
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d : ℕ) (anchor : ShiftedFareyAnchor) : ℂ :=
  (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
      S b target a d anchor.1,
    actualMajorArcArchimedeanCellPhase
      (actualMajorArcLcmResidueModulus S anchor.1)
      triple.1 triple.2.1 triple.2.2 a d
      (actualMajorArcIntegratedAnchorNumerator S anchor)) *
    (1 / ((actualMajorArcLcmResidueModulus S anchor.1).totient : ℂ)) ^ 3

/-- Pointwise exact factorization of the COMPLETE actual anchor smooth
model: one genuine signed conductor/support coefficient times the original
two-edge, real-strip smooth affine cubic at the translated center. -/
theorem actualCenterCoupling_anchor_smooth_eq_coefficient_mul
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor) (α : ℝ) :
    actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α =
      actualCenterCouplingAnchorCoefficient S b target a d anchor *
        actualMajorArcArchimedeanSmoothCubic a d n τ ell
          (α - shiftedFareyAnchorCenter
            (∏ p ∈ S, p) anchor.1 anchor.2.1 anchor.2.2) := by
  unfold actualMajorArcIntegratedAnchorSmooth
    actualCenterCouplingAnchorCoefficient
  rw [actualMajorArcSingular_admissible_smooth_eq_phase_cubic]

/-- Equivalent exact three-coordinate factorization of the same signed
anchor coefficient.  The true fixed robust label, both switched selectors,
and the full `lcm(q,W)` unit condition remain visible in every factor. -/
theorem actualCenterCoupling_anchor_coefficient_eq_three_unit_sums
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d : ℕ) (anchor : ShiftedFareyAnchor) :
    actualCenterCouplingAnchorCoefficient S b target a d anchor =
      ((∑ label ∈ actualMajorArcSingularLabelResidues
          S target anchor.1,
        GoldbachChain.e
          (((label : ℝ) * actualMajorArcIntegratedAnchorNumerator S anchor) /
            actualMajorArcLcmResidueModulus S anchor.1)) *
      (∑ left ∈ actualMajorArcSingularLeftResidues
          S b a anchor.1,
        GoldbachChain.e
          ((((a : ℝ) * left) *
            actualMajorArcIntegratedAnchorNumerator S anchor) /
              actualMajorArcLcmResidueModulus S anchor.1)) *
      (∑ right ∈ actualMajorArcSingularRightResidues
          S b d anchor.1,
        GoldbachChain.e
          (((((-2 * (d : ℤ) : ℤ) : ℝ) * right) *
            actualMajorArcIntegratedAnchorNumerator S anchor) /
              actualMajorArcLcmResidueModulus S anchor.1))) *
        (1 / ((actualMajorArcLcmResidueModulus S anchor.1).totient : ℂ)) ^ 3 := by
  unfold actualCenterCouplingAnchorCoefficient
  rw [actualMajorArcSingular_admissible_phase_eq_three_unit_sums]

/-- The genuine support-square conductor annihilation transfers to the
actual normalized anchor coefficient itself, without removing any unit
selector, switched mask, support character, or periodic lift. -/
theorem actualCenterCoupling_anchor_coefficient_zero_of_support_square
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff p : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor)
    (hsupport : ∀ q ∈ S, q.Prime)
    (hanchor : anchor ∈ actualShiftedFareyAnchors
      (∏ q ∈ S, q) cutoff)
    (hp : p ∈ S)
    (hsquare : p ^ 2 ∣ anchor.1) :
    ∀ α : ℝ,
      actualCenterCouplingAnchorCoefficient S b target a d anchor *
        actualMajorArcArchimedeanSmoothCubic a d n τ ell
          (α - shiftedFareyAnchorCenter
            (∏ q ∈ S, q) anchor.1 anchor.2.1 anchor.2.2) = 0 := by
  intro α
  rw [← actualCenterCoupling_anchor_smooth_eq_coefficient_mul]
  exact actualMajorArcCenter_actual_anchor_smooth_zero_of_support_square
    S b n target a d cutoff p τ ell α anchor hsupport hanchor hp hsquare

/-- Only the COMPLETE genuine smooth contribution, still indexed by each
actual distinct rational center and its canonical ORIGINAL widest anchor. -/
noncomputable def actualCenterCouplingCanonicalSmoothMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target P Q : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      ∑ center ∈
        (shiftedFareyCenterClasses (∏ p ∈ S, p)
          (actualShiftedFareyAnchors (∏ p ∈ S, p) P)).attach,
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            shiftedFareyCenterRegion (∏ p ∈ S, p) Q
              (actualShiftedFareyAnchors (∏ p ∈ S, p) P) center.val,
          actualMajorArcIntegratedAnchorSmooth
            S b n target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) P Q center) α).re

/-- Every genuinely signed nonunit/incompatible cell, indexed by the SAME
actual distinct centers and canonical original widest anchors. -/
noncomputable def actualCenterCouplingCanonicalExceptionalMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target P Q : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      ∑ center ∈
        (shiftedFareyCenterClasses (∏ p ∈ S, p)
          (actualShiftedFareyAnchors (∏ p ∈ S, p) P)).attach,
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            shiftedFareyCenterRegion (∏ p ∈ S, p) Q
              (actualShiftedFareyAnchors (∏ p ∈ S, p) P) center.val,
          actualMajorArcIntegratedAnchorExceptional
            S b n J target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) P Q center) α).re

/-- Exact global signed decomposition of the actual canonical model into
its COMPLETE smooth mass and its COMPLETE exceptional mass.  No exception
is dropped or inferred to have a favorable sign. -/
theorem actualCenterCoupling_canonical_model_eq_smooth_add_exceptional
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target P Q : ℕ) (τ ell : ℝ) :
    actualMajorArcGlobalCanonicalModelMass
        S b n J target P Q τ ell =
      actualCenterCouplingCanonicalSmoothMass
          S b n target P Q τ ell +
        actualCenterCouplingCanonicalExceptionalMass
          S b n J target P Q τ ell := by
  classical
  unfold actualMajorArcGlobalCanonicalModelMass
    actualCenterCouplingCanonicalSmoothMass
    actualCenterCouplingCanonicalExceptionalMass
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro center hcenter
  let W : ℕ := ∏ p ∈ S, p
  let region : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩
    shiftedFareyCenterRegion W Q
      (actualShiftedFareyAnchors W P) center.val
  let anchor := actualMajorArcGlobalCanonicalWidestAnchor
    W P Q center
  have hsmooth : IntegrableOn
      (actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor)
      region volume :=
    (actualMajorArcIntegratedAnchorSmooth_continuous
      S b n target a d τ ell anchor).integrableOn_Ioc.mono_set
        Set.inter_subset_left
  have hexception : IntegrableOn
      (actualMajorArcIntegratedAnchorExceptional
        S b n J target a d τ ell anchor)
      region volume :=
    (actualMajorArcIntegratedAnchorExceptional_continuous
      S b n J target a d τ ell anchor).integrableOn_Ioc.mono_set
        Set.inter_subset_left
  rw [MeasureTheory.integral_add hsmooth hexception]
  rfl

/-- The TRUE original-denominator radius of a canonical major anchor. -/
noncomputable def actualCenterCouplingAnchorRadius
    (fareyCutoff : ℕ) (anchor : ShiftedFareyAnchor) : ℝ :=
  1 / ((anchor.1 : ℝ) * ((fareyCutoff : ℝ) + 1))

/-- Every genuine positive-denominator, positive-cutoff anchor has radius in
`(0,1/2]`; its symmetric singular integral therefore has a well-defined
complementary signed middle tail. -/
theorem actualCenterCoupling_anchor_radius_bounds
    (fareyCutoff : ℕ) (anchor : ShiftedFareyAnchor)
    (hanchor : 0 < anchor.1)
    (hfarey : 0 < fareyCutoff) :
    0 < actualCenterCouplingAnchorRadius fareyCutoff anchor ∧
      2 * actualCenterCouplingAnchorRadius fareyCutoff anchor ≤ 1 := by
  have hanchorReal : (1 : ℝ) ≤ (anchor.1 : ℝ) := by
    exact_mod_cast hanchor
  have hfareyReal : (1 : ℝ) ≤ (fareyCutoff : ℝ) := by
    exact_mod_cast hfarey
  have hdenominator :
      0 < (anchor.1 : ℝ) * ((fareyCutoff : ℝ) + 1) := by
    positivity
  have htwo :
      (2 : ℝ) ≤ (anchor.1 : ℝ) * ((fareyCutoff : ℝ) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hanchorReal)
      (show 0 ≤ (fareyCutoff : ℝ) + 1 by positivity)]
  constructor
  · unfold actualCenterCouplingAnchorRadius
    positivity
  · unfold actualCenterCouplingAnchorRadius
    calc
      2 * (1 / ((anchor.1 : ℝ) * ((fareyCutoff : ℝ) + 1))) =
          2 / ((anchor.1 : ℝ) * ((fareyCutoff : ℝ) + 1)) := by ring
      _ ≤ 1 := (div_le_one hdenominator).mpr htwo

/-- The complete genuine signed smooth cubic over one UNCLIPPED original
widest anchor equals its exact support/outside coefficient times the TRUE
affine lattice count MINUS its signed resonant middle tail.  The radius uses
the anchor's original denominator, not its common modulus or a duplicate. -/
theorem actualCenterCoupling_anchor_integral_eq_signed_lattice_sub_tail
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d fareyCutoff : ℕ)
    (τ ell : ℝ) (anchor : ShiftedFareyAnchor)
    (hanchor : 0 < anchor.1)
    (hfarey : 0 < fareyCutoff) :
    (∫ α in shiftedFareyAnchorArc
          (∏ p ∈ S, p) fareyCutoff
          anchor.1 anchor.2.1 anchor.2.2,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell anchor α) =
      actualCenterCouplingAnchorCoefficient S b target a d anchor *
        (((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        ∫ β in Set.Icc
            (actualCenterCouplingAnchorRadius fareyCutoff anchor)
            (1 - actualCenterCouplingAnchorRadius fareyCutoff anchor),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β) := by
  let center : ℝ := shiftedFareyAnchorCenter
    (∏ p ∈ S, p) anchor.1 anchor.2.1 anchor.2.2
  let radius : ℝ := actualCenterCouplingAnchorRadius fareyCutoff anchor
  have hradius := actualCenterCoupling_anchor_radius_bounds
    fareyCutoff anchor hanchor hfarey
  change
    (∫ α in Metric.closedBall center radius,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α) =
      actualCenterCouplingAnchorCoefficient S b target a d anchor *
        (((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        ∫ β in Set.Icc radius (1 - radius),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β)
  calc
    (∫ α in Metric.closedBall center radius,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α) =
      ∫ α in Metric.closedBall center radius,
        actualCenterCouplingAnchorCoefficient S b target a d anchor *
          actualMajorArcArchimedeanSmoothCubic a d n τ ell
            (α - center) := by
      apply setIntegral_congr_fun
        Metric.isClosed_closedBall.measurableSet
      intro α hα
      exact actualCenterCoupling_anchor_smooth_eq_coefficient_mul
        S b n target a d τ ell anchor α
    _ = actualCenterCouplingAnchorCoefficient S b target a d anchor *
          (∫ α in Metric.closedBall center radius,
            actualMajorArcArchimedeanSmoothCubic a d n τ ell
              (α - center)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = actualCenterCouplingAnchorCoefficient S b target a d anchor *
          (∫ β in Metric.closedBall (0 : ℝ) radius,
            actualMajorArcArchimedeanSmoothCubic a d n τ ell β) := by
      rw [actualMajorArcBoundary_translated_ball_integral
        (actualMajorArcArchimedeanSmoothCubic a d n τ ell)
        center radius hradius.1.le]
    _ = actualCenterCouplingAnchorCoefficient S b target a d anchor *
          (∫ β in Set.Icc (-radius) radius,
            actualMajorArcArchimedeanSmoothCubic a d n τ ell β) := by
      rw [actualMajorArcBoundary_real_closedBall_eq_Icc]
      simp
    _ = _ := by
      rw [actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
        a d n τ ell radius hradius.1.le hradius.2]

/-- Every ACTUAL distinct interior center, represented by its canonical
ORIGINAL widest anchor, has the exact signed lattice-minus-middle-tail
formula on its true clipped center region.  The containment assumption
explicitly excludes the separate `0/1` periodic-boundary pair. -/
theorem actualCenterCoupling_canonical_interior_integral_eq_lattice_sub_tail
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ)
    (center : ActualMajorArcGlobalCenter
      (∏ p ∈ S, p) cutoff)
    (hfarey : 0 < fareyCutoff)
    (hinterior :
      shiftedFareyAnchorArc (∏ p ∈ S, p) fareyCutoff
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center).1
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center).2.1
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center).2.2 ⊆
        Set.Ioc (0 : ℝ) 1) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
          (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center.val,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center) α) =
      actualCenterCouplingAnchorCoefficient S b target a d
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center) *
        (((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        ∫ β in Set.Icc
            (actualCenterCouplingAnchorRadius fareyCutoff
              (actualMajorArcGlobalCanonicalWidestAnchor
                (∏ p ∈ S, p) cutoff fareyCutoff center))
            (1 - actualCenterCouplingAnchorRadius fareyCutoff
              (actualMajorArcGlobalCanonicalWidestAnchor
                (∏ p ∈ S, p) cutoff fareyCutoff center)),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β) := by
  let W : ℕ := ∏ p ∈ S, p
  let anchor := actualMajorArcGlobalCanonicalWidestAnchor
    W cutoff fareyCutoff center
  have hspec := actualMajorArcGlobalCanonicalWidestAnchor_spec
    W cutoff fareyCutoff center
  have hpositive :=
    (actualShiftedFareyAnchors_denominator_bounds
      W cutoff anchor hspec.1).1
  rw [hspec.2.2, Set.inter_eq_right.mpr hinterior]
  exact actualCenterCoupling_anchor_integral_eq_signed_lattice_sub_tail
    S b n target a d fareyCutoff τ ell anchor hpositive hfarey

/-- The exact original deduplicated prime-major mass differs from its
genuine smooth-only canonical center mass by at most the complete explicit
integrated SW/prime-power budget PLUS the absolute value of the retained
signed exceptional mass.  Every support divisor and every distinct actual
widest center remains in all three quantities. -/
theorem actualCenterCoupling_prime_mass_sub_smooth_le_error_add_exception
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (J target Q : ℕ) (τ ell : ℝ),
          target ∈ robustResidues S b J →
          manuscriptRealLabelLower τ n ≤ manuscriptRealLabelUpper τ ell n →
          manuscriptRealLabelUpper τ ell n ≤ n →
          (∀ a ∈ (∏ p ∈ S, p).divisors,
            n / (2 * a) + 1 ≤ n) →
          (∀ d ∈ (∏ p ∈ S, p).divisors,
            n / (4 * d) + 1 ≤ n) →
          |actualDeduplicatedMajorPrimeMass
              S b n J target (compatibleLogMinorCutoff n) Q τ ell -
            actualCenterCouplingCanonicalSmoothMass
              S b n target (compatibleLogMinorCutoff n) Q τ ell| ≤
            actualMajorArcGlobalCanonicalErrorBudget
              S b c C n target (compatibleLogMinorCutoff n) Q τ ell +
            |actualCenterCouplingCanonicalExceptionalMass
              S b n J target (compatibleLogMinorCutoff n) Q τ ell| := by
  obtain ⟨c, C, hc, hC, hmajor⟩ :=
    actualMajorArcGlobalCanonicalMass_error S b hsupport
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hmajor] with n hn
  intro J target Q τ ell htarget hlower hupper hleft hright
  have hbound := hn J target Q τ ell
    htarget hlower hupper hleft hright
  rw [actualCenterCoupling_canonical_model_eq_smooth_add_exceptional] at hbound
  calc
    |actualDeduplicatedMajorPrimeMass
          S b n J target (compatibleLogMinorCutoff n) Q τ ell -
        actualCenterCouplingCanonicalSmoothMass
          S b n target (compatibleLogMinorCutoff n) Q τ ell| =
      |(actualDeduplicatedMajorPrimeMass
          S b n J target (compatibleLogMinorCutoff n) Q τ ell -
          (actualCenterCouplingCanonicalSmoothMass
              S b n target (compatibleLogMinorCutoff n) Q τ ell +
            actualCenterCouplingCanonicalExceptionalMass
              S b n J target (compatibleLogMinorCutoff n) Q τ ell)) +
        actualCenterCouplingCanonicalExceptionalMass
          S b n J target (compatibleLogMinorCutoff n) Q τ ell| := by
      congr 1
      ring
    _ ≤ |actualDeduplicatedMajorPrimeMass
          S b n J target (compatibleLogMinorCutoff n) Q τ ell -
          (actualCenterCouplingCanonicalSmoothMass
              S b n target (compatibleLogMinorCutoff n) Q τ ell +
            actualCenterCouplingCanonicalExceptionalMass
              S b n J target (compatibleLogMinorCutoff n) Q τ ell)| +
        |actualCenterCouplingCanonicalExceptionalMass
          S b n J target (compatibleLogMinorCutoff n) Q τ ell| :=
      abs_add_le _ _
    _ ≤ actualMajorArcGlobalCanonicalErrorBudget
          S b c C n target (compatibleLogMinorCutoff n) Q τ ell +
        |actualCenterCouplingCanonicalExceptionalMass
          S b n J target (compatibleLogMinorCutoff n) Q τ ell| := by
      gcongr

end Erdos689

