module

public import ActualMajorArcCenterReduction433

@[expose] public section


/-!
# Genuine interior-center geometry and signed singular tails

Distinct original translated Farey regions cannot overlap the genuine
boundary-center regions. Consequently every center strictly between zero
and one has an UNCLIPPED entire original widest Farey ball. Its complete
three-cell smooth integral equals its actual signed support/outside phase
coefficient times the genuine symmetric archimedean integral. The latter is
the exact original edge-bounded affine lattice minus its retained SIGNED
middle tail; no positivity or unsigned-tail deletion is assumed.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Erdos689

/-- Every true shifted rational-center region strictly inside the circle is
already contained in the ORIGINAL half-open Fourier domain. Any crossing
of zero or one would overlap the corresponding genuine boundary-center
region, contradicting actual translated-center disjointness. -/
theorem actualMajorArcInterior_region_subset_original_circle
    (support cutoff fareyCutoff : ℕ) (center : ℝ)
    (hsupport : 0 < support) (hcutoff : 0 < cutoff)
    (hseparation : 2 * (support * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses support
      (actualShiftedFareyAnchors support cutoff))
    (hcenterZero : 0 < center) (hcenterOne : center < 1) :
    shiftedFareyCenterRegion support fareyCutoff
        (actualShiftedFareyAnchors support cutoff) center ⊆
      Set.Ioc (0 : ℝ) 1 := by
  let anchors := actualShiftedFareyAnchors support cutoff
  have hgroups := shiftedFareyCenterRegions_pairwise_disjoint
    support cutoff fareyCutoff anchors hsupport
      (actualShiftedFareyAnchors_denominator_bounds support cutoff)
      hseparation
  have hzeroCenter := actualMajorArcBoundary_zero_center_mem
    support cutoff hsupport hcutoff
  have honeCenter := actualMajorArcBoundary_one_center_mem
    support cutoff hsupport hcutoff
  have hzeroRegion : (0 : ℝ) ∈
      shiftedFareyCenterRegion support fareyCutoff anchors 0 := by
    rw [actualMajorArcBoundary_actual_zero_center_region
      support cutoff fareyCutoff hsupport hcutoff]
    simp
    positivity
  have honeRegion : (1 : ℝ) ∈
      shiftedFareyCenterRegion support fareyCutoff anchors 1 := by
    rw [actualMajorArcBoundary_actual_one_center_region
      support cutoff fareyCutoff hsupport hcutoff]
    simp
    positivity
  intro α hα
  have hdecompose := hα
  simp only [shiftedFareyCenterRegion, Set.mem_iUnion] at hdecompose
  obtain ⟨anchor, hfiltered, hball⟩ := hdecompose
  obtain ⟨hanchor, hanchorCenter⟩ := Finset.mem_filter.mp hfiltered
  constructor
  · by_contra hnot
    have hnonpositive : α ≤ 0 := le_of_not_gt hnot
    have hzeroBall : (0 : ℝ) ∈
        shiftedFareyAnchorArc support fareyCutoff
          anchor.1 anchor.2.1 anchor.2.2 := by
      unfold shiftedFareyAnchorArc at hball ⊢
      rw [hanchorCenter] at hball ⊢
      rw [Metric.mem_closedBall, Real.dist_eq,
        abs_of_neg (by linarith : (0 : ℝ) - center < 0)]
      rw [Metric.mem_closedBall, Real.dist_eq,
        abs_of_neg (by linarith : α - center < 0)] at hball
      linarith
    have hzeroThis : (0 : ℝ) ∈
        shiftedFareyCenterRegion support fareyCutoff anchors center := by
      simp only [shiftedFareyCenterRegion, Set.mem_iUnion]
      exact ⟨anchor, Finset.mem_filter.mpr
        ⟨hanchor, hanchorCenter⟩, hzeroBall⟩
    exact Set.disjoint_left.mp
      (hgroups hcenter hzeroCenter (ne_of_gt hcenterZero))
      hzeroThis hzeroRegion
  · by_contra hnot
    have habove : 1 < α := lt_of_not_ge hnot
    have honeBall : (1 : ℝ) ∈
        shiftedFareyAnchorArc support fareyCutoff
          anchor.1 anchor.2.1 anchor.2.2 := by
      unfold shiftedFareyAnchorArc at hball ⊢
      rw [hanchorCenter] at hball ⊢
      rw [Metric.mem_closedBall, Real.dist_eq,
        abs_of_pos (by linarith : (0 : ℝ) < 1 - center)]
      rw [Metric.mem_closedBall, Real.dist_eq,
        abs_of_pos (by linarith : (0 : ℝ) < α - center)] at hball
      linarith
    have honeThis : (1 : ℝ) ∈
        shiftedFareyCenterRegion support fareyCutoff anchors center := by
      simp only [shiftedFareyCenterRegion, Set.mem_iUnion]
      exact ⟨anchor, Finset.mem_filter.mpr
        ⟨hanchor, hanchorCenter⟩, honeBall⟩
    exact Set.disjoint_left.mp
      (hgroups hcenter honeCenter (ne_of_lt hcenterOne))
      honeThis honeRegion

/-- Exact elimination of Fourier-circle clipping at EVERY genuine interior
distinct shifted center; the complete original region is retained. -/
theorem actualMajorArcInterior_clipped_region_eq_unclipped
    (support cutoff fareyCutoff : ℕ) (center : ℝ)
    (hsupport : 0 < support) (hcutoff : 0 < cutoff)
    (hseparation : 2 * (support * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses support
      (actualShiftedFareyAnchors support cutoff))
    (hcenterZero : 0 < center) (hcenterOne : center < 1) :
    Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion support fareyCutoff
          (actualShiftedFareyAnchors support cutoff) center =
      shiftedFareyCenterRegion support fareyCutoff
        (actualShiftedFareyAnchors support cutoff) center := by
  exact Set.inter_eq_right.mpr
    (actualMajorArcInterior_region_subset_original_circle
      support cutoff fareyCutoff center hsupport hcutoff hseparation
      hcenter hcenterZero hcenterOne)

/-- The COMPLETE genuine signed support/outside three-cell phase at an
actual original anchor, including its TRUE `φ(lcm(q,W))⁻³` density. -/
noncomputable def actualMajorArcInteriorAnchorPhase
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d : ℕ) (anchor : ShiftedFareyAnchor) : ℂ :=
  (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
      S b target a d anchor.1,
    actualMajorArcArchimedeanCellPhase
      (actualMajorArcLcmResidueModulus S anchor.1)
      triple.1 triple.2.1 triple.2.2 a d
      (actualMajorArcIntegratedAnchorNumerator S anchor)) *
    (1 / ((actualMajorArcLcmResidueModulus
      S anchor.1).totient : ℂ)) ^ 3

/-- Pointwise exact factorization of the ENTIRE original admissible smooth
model into its true signed full-unit three-cell phase and the genuine
two-edge archimedean cubic at the ACTUAL real-center offset. -/
theorem actualMajorArcInterior_anchor_smooth_eq_signed_phase
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor) (α : ℝ) :
    actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α =
      actualMajorArcInteriorAnchorPhase S b target a d anchor *
        actualMajorArcArchimedeanSmoothCubic a d n τ ell
          (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
            anchor.1 anchor.2.1 anchor.2.2) := by
  unfold actualMajorArcIntegratedAnchorSmooth
    actualMajorArcInteriorAnchorPhase
  exact actualMajorArcSingular_admissible_smooth_eq_phase_cubic
    S b n target a d anchor.1 τ ell
    (actualMajorArcIntegratedAnchorNumerator S anchor)
    (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
      anchor.1 anchor.2.1 anchor.2.2)

/-- The complete actual admissible smooth integral over an interior
deduplicated center is its genuine SIGNED full-cell phase multiplied by
the symmetric archimedean integral of the ORIGINAL widest-anchor radius.
The original circle intersection is eliminated exactly, not approximately. -/
theorem actualMajorArcInterior_integrated_smooth_eq_signed_symmetric
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell center : ℝ) (anchor : ShiftedFareyAnchor)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses
      (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff))
    (hcenterZero : 0 < center) (hcenterOne : center < 1)
    (hanchor : anchor ∈ actualShiftedFareyAnchors
      (∏ p ∈ S, p) cutoff)
    (_hanchorCenter : shiftedFareyAnchorCenter
      (∏ p ∈ S, p) anchor.1 anchor.2.1 anchor.2.2 = center)
    (hregion : shiftedFareyCenterRegion
      (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center =
      shiftedFareyAnchorArc (∏ p ∈ S, p) fareyCutoff
        anchor.1 anchor.2.1 anchor.2.2) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α) =
      actualMajorArcInteriorAnchorPhase S b target a d anchor *
        (∫ β in Set.Icc
          (-(1 / ((anchor.1 : ℝ) * (fareyCutoff + 1))))
          (1 / ((anchor.1 : ℝ) * (fareyCutoff + 1))),
          actualMajorArcArchimedeanSmoothCubic
            a d n τ ell β) := by
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hdenominator :=
    (actualShiftedFareyAnchors_denominator_bounds
      W cutoff anchor hanchor).1
  have hclipping := actualMajorArcInterior_clipped_region_eq_unclipped
    W cutoff fareyCutoff center hW hcutoff hseparation
      hcenter hcenterZero hcenterOne
  rw [hclipping, hregion]
  simp_rw [actualMajorArcInterior_anchor_smooth_eq_signed_phase]
  rw [MeasureTheory.integral_const_mul]
  unfold shiftedFareyAnchorArc
  rw [actualMajorArcBoundary_translated_ball_integral
    (actualMajorArcArchimedeanSmoothCubic a d n τ ell)
    (shiftedFareyAnchorCenter W anchor.1 anchor.2.1 anchor.2.2)
    (1 / ((anchor.1 : ℝ) * (fareyCutoff + 1))) (by positivity)]
  rw [actualMajorArcBoundary_real_closedBall_eq_Icc]
  simp

/-- Exact original interior-center singular expansion: the signed genuine
three-cell phase multiplies the ACTUAL two-edge affine lattice minus the
retained signed archimedean middle tail at radius `1/(q*(Q+1))`. -/
theorem actualMajorArcInterior_integrated_smooth_eq_lattice_sub_tail
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell center : ℝ) (anchor : ShiftedFareyAnchor)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff) (hfarey : 0 < fareyCutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses
      (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff))
    (hcenterZero : 0 < center) (hcenterOne : center < 1)
    (hanchor : anchor ∈ actualShiftedFareyAnchors
      (∏ p ∈ S, p) cutoff)
    (hanchorCenter : shiftedFareyAnchorCenter
      (∏ p ∈ S, p) anchor.1 anchor.2.1 anchor.2.2 = center)
    (hregion : shiftedFareyCenterRegion
      (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center =
      shiftedFareyAnchorArc (∏ p ∈ S, p) fareyCutoff
        anchor.1 anchor.2.1 anchor.2.2) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α) =
      actualMajorArcInteriorAnchorPhase S b target a d anchor *
        (((ternaryAffineTriples
            (actualMajorArcArchimedeanLeftWindow a n)
            (actualMajorArcArchimedeanCenterWindow d n)
            (actualMajorArcArchimedeanLabelWindow τ ell n)
            a (2 * d)).card : ℂ) -
          ∫ β in Set.Icc
            (1 / ((anchor.1 : ℝ) * (fareyCutoff + 1)))
            (1 - 1 / ((anchor.1 : ℝ) * (fareyCutoff + 1))),
            actualMajorArcArchimedeanSmoothCubic a d n τ ell β) := by
  rw [actualMajorArcInterior_integrated_smooth_eq_signed_symmetric
    S b n target a d cutoff fareyCutoff τ ell center anchor
    hsupport hcutoff hseparation hcenter hcenterZero hcenterOne
    hanchor hanchorCenter hregion]
  congr 1
  apply actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
  · positivity
  · have hdenominator :=
      (actualShiftedFareyAnchors_denominator_bounds
        (∏ p ∈ S, p) cutoff anchor hanchor).1
    have hdenominatorReal : (1 : ℝ) ≤ anchor.1 := by
      exact_mod_cast hdenominator
    have hfareyReal : (1 : ℝ) ≤ fareyCutoff := by
      exact_mod_cast hfarey
    have hproduct :
        (2 : ℝ) ≤ (anchor.1 : ℝ) * (fareyCutoff + 1) := by
      calc
        (2 : ℝ) = 1 * (1 + 1) := by ring
        _ ≤ (anchor.1 : ℝ) * (fareyCutoff + 1) :=
          mul_le_mul hdenominatorReal (by linarith)
            (by positivity) (by positivity)
    calc
      2 * (1 / ((anchor.1 : ℝ) * (fareyCutoff + 1))) =
          2 / ((anchor.1 : ℝ) * (fareyCutoff + 1)) := by ring
      _ ≤ 1 := (div_le_iff₀ (by positivity :
        (0 : ℝ) < (anchor.1 : ℝ) * (fareyCutoff + 1))).mpr
          (by simpa using hproduct)

/-- SHARP signed-phase-sensitive true-arc remainder. The absolute error is
`‖actual signed phase‖ * n/(2*radius)` at its ORIGINAL denominator radius;
it is not multiplied by an artificial raw-anchor or support-character count. -/
theorem actualMajorArcInterior_integrated_smooth_lattice_error_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell center : ℝ) (anchor : ShiftedFareyAnchor)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : 0 < a) (hd : 0 < d)
    (hcutoff : 0 < cutoff) (hfarey : 0 < fareyCutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses
      (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff))
    (hcenterZero : 0 < center) (hcenterOne : center < 1)
    (hanchor : anchor ∈ actualShiftedFareyAnchors
      (∏ p ∈ S, p) cutoff)
    (hanchorCenter : shiftedFareyAnchorCenter
      (∏ p ∈ S, p) anchor.1 anchor.2.1 anchor.2.2 = center)
    (hregion : shiftedFareyCenterRegion
      (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center =
      shiftedFareyAnchorArc (∏ p ∈ S, p) fareyCutoff
        anchor.1 anchor.2.1 anchor.2.2) :
    ‖(∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α) -
      actualMajorArcInteriorAnchorPhase S b target a d anchor *
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ)‖ ≤
      ‖actualMajorArcInteriorAnchorPhase S b target a d anchor‖ *
        ((n : ℝ) /
          (2 * (1 / ((anchor.1 : ℝ) * (fareyCutoff + 1))))) := by
  rw [actualMajorArcInterior_integrated_smooth_eq_signed_symmetric
    S b n target a d cutoff fareyCutoff τ ell center anchor
    hsupport hcutoff hseparation hcenter hcenterZero hcenterOne
    hanchor hanchorCenter hregion]
  let phase := actualMajorArcInteriorAnchorPhase S b target a d anchor
  let radius : ℝ := 1 / ((anchor.1 : ℝ) * (fareyCutoff + 1))
  have hdenominator :=
    (actualShiftedFareyAnchors_denominator_bounds
      (∏ p ∈ S, p) cutoff anchor hanchor).1
  have hradius : 0 < radius := by dsimp [radius]; positivity
  have hhalf : 2 * radius ≤ 1 := by
    have hdenominatorReal : (1 : ℝ) ≤ anchor.1 := by
      exact_mod_cast hdenominator
    have hfareyReal : (1 : ℝ) ≤ fareyCutoff := by
      exact_mod_cast hfarey
    have hproduct : (2 : ℝ) ≤
        (anchor.1 : ℝ) * (fareyCutoff + 1) := by
      calc
        (2 : ℝ) = 1 * (1 + 1) := by ring
        _ ≤ (anchor.1 : ℝ) * (fareyCutoff + 1) :=
          mul_le_mul hdenominatorReal (by linarith)
            (by positivity) (by positivity)
    dsimp [radius]
    calc
      2 * (1 / ((anchor.1 : ℝ) * (fareyCutoff + 1))) =
          2 / ((anchor.1 : ℝ) * (fareyCutoff + 1)) := by ring
      _ ≤ 1 := (div_le_iff₀ (by positivity :
        (0 : ℝ) < (anchor.1 : ℝ) * (fareyCutoff + 1))).mpr
          (by simpa using hproduct)
  have herror := actualMajorArcBoundary_smooth_symmetric_lattice_error_le
    a d n τ ell radius ha hd hradius hhalf
  change ‖phase *
      (∫ β in Set.Icc (-radius) radius,
        actualMajorArcArchimedeanSmoothCubic a d n τ ell β) -
      phase *
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ)‖ ≤
    ‖phase‖ * ((n : ℝ) / (2 * radius))
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left herror (norm_nonneg phase)

#print axioms Erdos689.actualMajorArcInterior_region_subset_original_circle
#print axioms Erdos689.actualMajorArcInterior_clipped_region_eq_unclipped
#print axioms Erdos689.actualMajorArcInterior_anchor_smooth_eq_signed_phase
#print axioms Erdos689.actualMajorArcInterior_integrated_smooth_eq_signed_symmetric
#print axioms Erdos689.actualMajorArcInterior_integrated_smooth_eq_lattice_sub_tail
#print axioms Erdos689.actualMajorArcInterior_integrated_smooth_lattice_error_le

end Erdos689
