import ActualMajorArcPositivityFinal433

/-!
# Exact periodic boundary gluing for the original shifted major arcs

The genuine finite center family contains both real representatives `0` and
`1`. Their intersections with the original fundamental domain `Ioc (0,1]`
are complementary HALF arcs. Summing two full singular integrals would
introduce a nonvanishing spurious principal term. The theorems below prove
the exact periodic gluing identity for the actual prime and smooth cubics.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Every actual integer-frequency finite exponential sum is exactly
one-periodic, including negative affine frequencies. -/
theorem actualMajorArcBoundary_exponential_periodic
    (window : Finset ℕ) (weight : ℕ → ℂ) (frequency : ℤ) :
    Function.Periodic (ternaryExponentialSum window weight frequency) 1 := by
  intro α
  simpa using ternaryExponentialSum_add_int window weight frequency α 1

/-- The original genuine-prime, switched, support-filtered three-window
cubic has period one; no residue or edge condition is discarded. -/
theorem actualMajorArcBoundary_prime_cubic_periodic
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d : ℕ) (τ ell : ℝ) :
    Function.Periodic
      (actualMajorArcPrimeCubic S b n J target a d τ ell) 1 := by
  intro α
  unfold actualMajorArcPrimeCubic
  rw [(actualMajorArcBoundary_exponential_periodic _ _ _) α,
    (actualMajorArcBoundary_exponential_periodic _ _ _) α,
    (actualMajorArcBoundary_exponential_periodic _ _ _) α]

/-- The true two-edge archimedean cubic also has period one at ALL three
genuine frequencies `1`, `a`, and `-2d`. -/
theorem actualMajorArcBoundary_smooth_cubic_periodic
    (a d n : ℕ) (τ ell : ℝ) :
    Function.Periodic
      (actualMajorArcArchimedeanSmoothCubic a d n τ ell) 1 := by
  intro α
  unfold actualMajorArcArchimedeanSmoothCubic
  rw [(actualMajorArcBoundary_exponential_periodic _ _ _) α,
    (actualMajorArcBoundary_exponential_periodic _ _ _) α,
    (actualMajorArcBoundary_exponential_periodic _ _ _) α]

/-- The genuine center-zero closed arc contributes exactly its positive
half inside the original fundamental Fourier interval. -/
theorem actualMajorArcBoundary_zero_clipped_arc
    (radius : ℝ) (hradius : radius < 1) :
    Set.Ioc (0 : ℝ) 1 ∩ Metric.closedBall (0 : ℝ) radius =
      Set.Ioc (0 : ℝ) radius := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Metric.mem_closedBall,
    Real.dist_eq, sub_zero]
  constructor
  · rintro ⟨⟨hx, _⟩, hball⟩
    exact ⟨hx, (abs_of_pos hx).symm ▸ hball⟩
  · rintro ⟨hx, hupper⟩
    refine ⟨⟨hx, le_of_lt (hupper.trans_lt hradius)⟩, ?_⟩
    simpa [abs_of_pos hx] using hupper

/-- The distinct real representative `1` contributes exactly the OTHER
closed half of the same periodic principal arc. -/
theorem actualMajorArcBoundary_one_clipped_arc
    (radius : ℝ) (hradius : radius < 1) :
    Set.Ioc (0 : ℝ) 1 ∩ Metric.closedBall (1 : ℝ) radius =
      Set.Icc (1 - radius) 1 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Metric.mem_closedBall,
    Real.dist_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨_, hx⟩, hball⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hx)] at hball
    constructor <;> linarith
  · rintro ⟨hlower, hupper⟩
    have hpositive : 0 < x := by linarith
    refine ⟨⟨hpositive, hupper⟩, ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
    linarith

/-- Exact periodic recombination of the TWO genuine clipped boundary
centers into ONE complete symmetric principal interval. -/
theorem actualMajorArcBoundary_periodic_half_arcs_eq_symmetric
    (f : ℝ → ℂ) (hf : Continuous f)
    (hperiodic : Function.Periodic f 1)
    (radius : ℝ) (hzero : 0 ≤ radius) (hone : radius < 1) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      Metric.closedBall (0 : ℝ) radius, f α) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      Metric.closedBall (1 : ℝ) radius, f α) =
      ∫ α in Set.Icc (-radius) radius, f α := by
  rw [actualMajorArcBoundary_zero_clipped_arc radius hone,
    actualMajorArcBoundary_one_clipped_arc radius hone,
    integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hzero,
    ← intervalIntegral.integral_of_le (by linarith : 1 - radius ≤ 1),
    ← intervalIntegral.integral_of_le (by linarith : -radius ≤ radius)]
  have htranslate :
      (∫ α in (1 - radius)..1, f α) =
        ∫ α in (-radius)..0, f α := by
    calc
      (∫ α in (1 - radius)..1, f α) =
          ∫ α in (-radius + 1)..(0 + 1), f α := by
            congr 1 <;> ring
      _ = ∫ α in (-radius)..0, f (α + 1) :=
        (intervalIntegral.integral_comp_add_right f 1).symm
      _ = ∫ α in (-radius)..0, f α := by
        apply intervalIntegral.integral_congr
        intro α _
        exact hperiodic α
  rw [htranslate, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- The exact center-zero/center-one identity for the actual ORIGINAL
prime-only manuscript cubic, with every graph selector intact. -/
theorem actualMajorArcBoundary_actual_prime_half_arcs_eq_symmetric
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d : ℕ) (τ ell radius : ℝ)
    (hzero : 0 ≤ radius) (hone : radius < 1) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      Metric.closedBall (0 : ℝ) radius,
      actualMajorArcPrimeCubic S b n J target a d τ ell α) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      Metric.closedBall (1 : ℝ) radius,
      actualMajorArcPrimeCubic S b n J target a d τ ell α) =
    ∫ α in Set.Icc (-radius) radius,
      actualMajorArcPrimeCubic S b n J target a d τ ell α := by
  exact actualMajorArcBoundary_periodic_half_arcs_eq_symmetric
    _ (actualMajorArcPrimeCubic_continuous S b n J target a d τ ell)
    (actualMajorArcBoundary_prime_cubic_periodic S b n J target a d τ ell)
    radius hzero hone

/-- The exact clipped-boundary identity for the real-strip, two-edge
smooth cubic entering the true outside singular series. -/
theorem actualMajorArcBoundary_actual_smooth_half_arcs_eq_symmetric
    (a d n : ℕ) (τ ell radius : ℝ)
    (hzero : 0 ≤ radius) (hone : radius < 1) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      Metric.closedBall (0 : ℝ) radius,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell α) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      Metric.closedBall (1 : ℝ) radius,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell α) =
    ∫ α in Set.Icc (-radius) radius,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell α := by
  apply actualMajorArcBoundary_periodic_half_arcs_eq_symmetric _
    ?_ (actualMajorArcBoundary_smooth_cubic_periodic a d n τ ell)
    radius hzero hone
  unfold actualMajorArcArchimedeanSmoothCubic
    ternaryExponentialSum GoldbachChain.e
  fun_prop

/-- The original reduced Farey family always contains its genuine
denominator-one numerator-zero anchor. -/
theorem actualMajorArcBoundary_goldbach_principal_anchor
    (cutoff : ℕ) (hcutoff : 0 < cutoff) :
    (1, (0 : ℤ)) ∈ GoldbachChain.anchors cutoff := by
  unfold GoldbachChain.anchors
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  · norm_num

/-- Both periodic representatives really occur in the ORIGINAL finite
shifted-anchor family: the center-zero one has periodic lift zero. -/
theorem actualMajorArcBoundary_zero_anchor_mem
    (supportModulus cutoff : ℕ)
    (hsupport : 0 < supportModulus) (hcutoff : 0 < cutoff) :
    (1, (0 : ℤ), (0 : ℤ)) ∈
      actualShiftedFareyAnchors supportModulus cutoff := by
  unfold actualShiftedFareyAnchors
  apply Finset.mem_image.mpr
  refine ⟨(((1, (0 : ℤ)), (0 : ℕ)), (0 : ℤ)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact actualMajorArcBoundary_goldbach_principal_anchor cutoff hcutoff
    · exact Finset.mem_range.mpr hsupport
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · norm_num

/-- The distinct center-one representative uses the actual allowed periodic
lift one; it is not an invented second full principal contribution. -/
theorem actualMajorArcBoundary_one_anchor_mem
    (supportModulus cutoff : ℕ)
    (hsupport : 0 < supportModulus) (hcutoff : 0 < cutoff) :
    (1, (1 : ℤ), (0 : ℤ)) ∈
      actualShiftedFareyAnchors supportModulus cutoff := by
  unfold actualShiftedFareyAnchors
  apply Finset.mem_image.mpr
  refine ⟨(((1, (0 : ℤ)), (0 : ℕ)), (1 : ℤ)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact actualMajorArcBoundary_goldbach_principal_anchor cutoff hcutoff
    · exact Finset.mem_range.mpr hsupport
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · norm_num

/-- Any distinct-center region containing an original denominator-one
anchor is EXACTLY its widest principal ball. No duplicate denominator is
counted twice and no clipping is applied prematurely. -/
theorem actualMajorArcBoundary_center_region_eq_unit_anchor
    (supportModulus fareyCutoff : ℕ)
    (anchors : Finset ShiftedFareyAnchor) (center : ℝ)
    (hpositive : ∀ anchor ∈ anchors, 0 < anchor.1)
    (hunit : ∃ numerator shift : ℤ,
      (1, numerator, shift) ∈ anchors ∧
        shiftedFareyAnchorCenter supportModulus 1 numerator shift = center) :
    shiftedFareyCenterRegion supportModulus fareyCutoff anchors center =
      Metric.closedBall center (1 / ((fareyCutoff : ℝ) + 1)) := by
  obtain ⟨numerator, shift, hmember, hcenter⟩ := hunit
  apply Set.Subset.antisymm
  · intro α hα
    simp only [shiftedFareyCenterRegion, Set.mem_iUnion] at hα
    obtain ⟨anchor, hgroup, hball⟩ := hα
    obtain ⟨hanchor, hanchorCenter⟩ := Finset.mem_filter.mp hgroup
    have hdenominator : (1 : ℝ) ≤ (anchor.1 : ℝ) := by
      exact_mod_cast hpositive anchor hanchor
    have hfarey : (0 : ℝ) < (fareyCutoff : ℝ) + 1 := by positivity
    have hradius :
        1 / ((anchor.1 : ℝ) * (fareyCutoff + 1)) ≤
          1 / ((fareyCutoff : ℝ) + 1) := by
      apply one_div_le_one_div_of_le hfarey
      nlinarith
    unfold shiftedFareyAnchorArc at hball
    rw [hanchorCenter] at hball
    exact (Metric.closedBall_subset_closedBall hradius) hball
  · intro α hα
    simp only [shiftedFareyCenterRegion, Set.mem_iUnion]
    refine ⟨(1, numerator, shift),
      Finset.mem_filter.mpr ⟨hmember, hcenter⟩, ?_⟩
    unfold shiftedFareyAnchorArc
    rw [hcenter]
    simpa using hα

/-- The actual distinct center-zero region has exactly the original
denominator-one Farey width. -/
theorem actualMajorArcBoundary_actual_zero_center_region
    (supportModulus cutoff fareyCutoff : ℕ)
    (hsupport : 0 < supportModulus) (hcutoff : 0 < cutoff) :
    shiftedFareyCenterRegion supportModulus fareyCutoff
      (actualShiftedFareyAnchors supportModulus cutoff) 0 =
        Metric.closedBall (0 : ℝ) (1 / ((fareyCutoff : ℝ) + 1)) := by
  apply actualMajorArcBoundary_center_region_eq_unit_anchor
  · intro anchor hanchor
    exact (actualShiftedFareyAnchors_denominator_bounds
      supportModulus cutoff anchor hanchor).1
  · refine ⟨0, 0,
      actualMajorArcBoundary_zero_anchor_mem
        supportModulus cutoff hsupport hcutoff, ?_⟩
    simp [shiftedFareyAnchorCenter]

/-- The actual distinct center-one region has the SAME genuine width;
pairing this region with the zero region is mandatory. -/
theorem actualMajorArcBoundary_actual_one_center_region
    (supportModulus cutoff fareyCutoff : ℕ)
    (hsupport : 0 < supportModulus) (hcutoff : 0 < cutoff) :
    shiftedFareyCenterRegion supportModulus fareyCutoff
      (actualShiftedFareyAnchors supportModulus cutoff) 1 =
        Metric.closedBall (1 : ℝ) (1 / ((fareyCutoff : ℝ) + 1)) := by
  apply actualMajorArcBoundary_center_region_eq_unit_anchor
  · intro anchor hanchor
    exact (actualShiftedFareyAnchors_denominator_bounds
      supportModulus cutoff anchor hanchor).1
  · refine ⟨1, 0,
      actualMajorArcBoundary_one_anchor_mem
        supportModulus cutoff hsupport hcutoff, ?_⟩
    simp [shiftedFareyAnchorCenter]

/-- The actual deduplicated finite center family really contains zero. -/
theorem actualMajorArcBoundary_zero_center_mem
    (supportModulus cutoff : ℕ)
    (hsupport : 0 < supportModulus) (hcutoff : 0 < cutoff) :
    (0 : ℝ) ∈ shiftedFareyCenterClasses supportModulus
      (actualShiftedFareyAnchors supportModulus cutoff) := by
  apply Finset.mem_image.mpr
  refine ⟨(1, (0 : ℤ), (0 : ℤ)),
    actualMajorArcBoundary_zero_anchor_mem
      supportModulus cutoff hsupport hcutoff, ?_⟩
  simp [shiftedFareyAnchorCenter]

/-- The actual deduplicated finite center family also contains the distinct
real representative one. -/
theorem actualMajorArcBoundary_one_center_mem
    (supportModulus cutoff : ℕ)
    (hsupport : 0 < supportModulus) (hcutoff : 0 < cutoff) :
    (1 : ℝ) ∈ shiftedFareyCenterClasses supportModulus
      (actualShiftedFareyAnchors supportModulus cutoff) := by
  apply Finset.mem_image.mpr
  refine ⟨(1, (1 : ℤ), (0 : ℤ)),
    actualMajorArcBoundary_one_anchor_mem
      supportModulus cutoff hsupport hcutoff, ?_⟩
  simp [shiftedFareyAnchorCenter]

/-- Any negative-center ball intersecting the positive fundamental domain
would already intersect the equally wide center-zero principal ball. -/
theorem actualMajorArcBoundary_negative_ball_subset_zero_ball
    (center radius : ℝ) (hcenter : center < 0) :
    Set.Ioc (0 : ℝ) 1 ∩ Metric.closedBall center radius ⊆
      Metric.closedBall (0 : ℝ) radius := by
  intro α hα
  obtain ⟨⟨hpositive, _⟩, hball⟩ := hα
  rw [Metric.mem_closedBall, Real.dist_eq] at hball ⊢
  rw [abs_of_pos (by linarith : 0 < α - center)] at hball
  rw [sub_zero, abs_of_pos hpositive]
  linarith

/-- Any above-one center ball intersecting the original circle would
already intersect the equally wide center-one principal ball. -/
theorem actualMajorArcBoundary_above_one_ball_subset_one_ball
    (center radius : ℝ) (hcenter : 1 < center) :
    Set.Ioc (0 : ℝ) 1 ∩ Metric.closedBall center radius ⊆
      Metric.closedBall (1 : ℝ) radius := by
  intro α hα
  obtain ⟨⟨_, hupper⟩, hball⟩ := hα
  rw [Metric.mem_closedBall, Real.dist_eq] at hball ⊢
  rw [abs_of_neg (by linarith : α - center < 0)] at hball
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-- Every ACTUAL deduplicated shifted center strictly outside `[0,1]` has
empty clipped major region at the genuine translated-disjointness cutoff.
This removes all spurious exterior anchors before conductor counting. -/
theorem actualMajorArcBoundary_exterior_center_region_empty
    (supportModulus cutoff fareyCutoff : ℕ)
    (center : ℝ)
    (hsupport : 0 < supportModulus)
    (hcutoff : 0 < cutoff)
    (hseparation :
      2 * (supportModulus * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses supportModulus
      (actualShiftedFareyAnchors supportModulus cutoff))
    (hexterior : center < 0 ∨ 1 < center) :
    Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion supportModulus fareyCutoff
        (actualShiftedFareyAnchors supportModulus cutoff) center = ∅ := by
  let anchors := actualShiftedFareyAnchors supportModulus cutoff
  have hgroups := shiftedFareyCenterRegions_pairwise_disjoint
    supportModulus cutoff fareyCutoff anchors hsupport
      (actualShiftedFareyAnchors_denominator_bounds supportModulus cutoff)
      hseparation
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro α hα
  obtain ⟨hcircle, hregion⟩ := hα
  have hanchorRegion := hregion
  simp only [shiftedFareyCenterRegion, Set.mem_iUnion] at hanchorRegion
  obtain ⟨anchor, hfiltered, hball⟩ := hanchorRegion
  obtain ⟨hanchor, heq⟩ := Finset.mem_filter.mp hfiltered
  have hdenominator : (1 : ℝ) ≤ (anchor.1 : ℝ) := by
    exact_mod_cast (actualShiftedFareyAnchors_denominator_bounds
      supportModulus cutoff anchor hanchor).1
  have hfarey : (0 : ℝ) < (fareyCutoff : ℝ) + 1 := by positivity
  have hradius :
      1 / ((anchor.1 : ℝ) * (fareyCutoff + 1)) ≤
        1 / ((fareyCutoff : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hfarey
    nlinarith
  unfold shiftedFareyAnchorArc at hball
  rw [heq] at hball
  rcases hexterior with hnegative | habove
  · have hnear := actualMajorArcBoundary_negative_ball_subset_zero_ball
      center _ hnegative ⟨hcircle, hball⟩
    have hzero : α ∈ shiftedFareyCenterRegion
        supportModulus fareyCutoff anchors 0 := by
      rw [actualMajorArcBoundary_actual_zero_center_region
        supportModulus cutoff fareyCutoff hsupport hcutoff]
      exact (Metric.closedBall_subset_closedBall hradius) hnear
    exact Set.disjoint_left.mp
      (hgroups hcenter
        (actualMajorArcBoundary_zero_center_mem
          supportModulus cutoff hsupport hcutoff)
        (ne_of_lt hnegative)) hregion hzero
  · have hnear := actualMajorArcBoundary_above_one_ball_subset_one_ball
      center _ habove ⟨hcircle, hball⟩
    have hone : α ∈ shiftedFareyCenterRegion
        supportModulus fareyCutoff anchors 1 := by
      rw [actualMajorArcBoundary_actual_one_center_region
        supportModulus cutoff fareyCutoff hsupport hcutoff]
      exact (Metric.closedBall_subset_closedBall hradius) hnear
    exact Set.disjoint_left.mp
      (hgroups hcenter
        (actualMajorArcBoundary_one_center_mem
          supportModulus cutoff hsupport hcutoff)
        (ne_of_gt habove)) hregion hone

/-- The actual two ORIGINAL distinct boundary center regions contribute
exactly ONE symmetric principal-arc smooth integral. This closes the
previously unresolved real `0/1` endpoint gluing step. -/
theorem actualMajorArcBoundary_actual_center_smooth_pair
    (S : Finset ℕ) (cutoff fareyCutoff a d n : ℕ)
    (τ ell : ℝ)
    (hsupport : 0 < ∏ p ∈ S, p)
    (hcutoff : 0 < cutoff)
    (hfarey : 0 < fareyCutoff) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) 0,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell α) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) 1,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell α) =
    ∫ α in Set.Icc
      (-(1 / ((fareyCutoff : ℝ) + 1)))
      (1 / ((fareyCutoff : ℝ) + 1)),
      actualMajorArcArchimedeanSmoothCubic a d n τ ell α := by
  rw [actualMajorArcBoundary_actual_zero_center_region
    (∏ p ∈ S, p) cutoff fareyCutoff hsupport hcutoff,
    actualMajorArcBoundary_actual_one_center_region
      (∏ p ∈ S, p) cutoff fareyCutoff hsupport hcutoff]
  apply actualMajorArcBoundary_actual_smooth_half_arcs_eq_symmetric
  · positivity
  · have hfareyReal : (0 : ℝ) < fareyCutoff := by exact_mod_cast hfarey
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith

/-- The analogous exact principal-boundary recombination holds for the
ORIGINAL prime-only cubic, before any smooth approximation. -/
theorem actualMajorArcBoundary_actual_center_prime_pair
    (S : Finset ℕ) (b : ℕ → ℕ)
    (cutoff fareyCutoff n J target a d : ℕ)
    (τ ell : ℝ)
    (hsupport : 0 < ∏ p ∈ S, p)
    (hcutoff : 0 < cutoff)
    (hfarey : 0 < fareyCutoff) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) 0,
      actualMajorArcPrimeCubic S b n J target a d τ ell α) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) 1,
      actualMajorArcPrimeCubic S b n J target a d τ ell α) =
    ∫ α in Set.Icc
      (-(1 / ((fareyCutoff : ℝ) + 1)))
      (1 / ((fareyCutoff : ℝ) + 1)),
      actualMajorArcPrimeCubic S b n J target a d τ ell α := by
  rw [actualMajorArcBoundary_actual_zero_center_region
    (∏ p ∈ S, p) cutoff fareyCutoff hsupport hcutoff,
    actualMajorArcBoundary_actual_one_center_region
      (∏ p ∈ S, p) cutoff fareyCutoff hsupport hcutoff]
  apply actualMajorArcBoundary_actual_prime_half_arcs_eq_symmetric
  · positivity
  · have hfareyReal : (0 : ℝ) < fareyCutoff := by exact_mod_cast hfarey
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith

/-- The exact real closed-ball endpoints; no positive-radius convention is
silently used when translating an actual distinct-center region. -/
theorem actualMajorArcBoundary_real_closedBall_eq_Icc
    (center radius : ℝ) :
    Metric.closedBall center radius =
      Set.Icc (center - radius) (center + radius) := by
  ext α
  simp only [Metric.mem_closedBall, Real.dist_eq, Set.mem_Icc, abs_le]
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2]
  · intro h
    constructor <;> linarith [h.1, h.2]

/-- An actual un-clipped rational-center arc is EXACTLY its translated
symmetric singular integral, with the genuine original width. -/
theorem actualMajorArcBoundary_translated_ball_integral
    (f : ℝ → ℂ) (center radius : ℝ)
    (hradius : 0 ≤ radius) :
    (∫ α in Metric.closedBall center radius, f (α - center)) =
      ∫ β in Metric.closedBall (0 : ℝ) radius, f β := by
  rw [actualMajorArcBoundary_real_closedBall_eq_Icc,
    actualMajorArcBoundary_real_closedBall_eq_Icc,
    zero_sub, zero_add, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : center - radius ≤ center + radius),
    ← intervalIntegral.integral_of_le (by linarith : -radius ≤ radius)]
  calc
    (∫ α in (center - radius)..(center + radius), f (α - center)) =
        ∫ α in (-radius + center)..(radius + center), f (α - center) := by
          congr 1 <;> ring
    _ = ∫ β in (-radius)..radius, f ((β + center) - center) :=
      (intervalIntegral.integral_comp_add_right
        (fun α => f (α - center)) center).symm
    _ = _ := by simp

/-- A COMPLETE symmetric periodic principal arc is the whole circle
MINUS the exact signed middle tail. In particular the omitted tail is not
discarded or asserted nonnegative. -/
theorem actualMajorArcBoundary_periodic_symmetric_eq_whole_sub_middle
    (f : ℝ → ℂ) (hf : Continuous f)
    (hperiodic : Function.Periodic f 1)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hhalf : 2 * radius ≤ 1) :
    (∫ α in Set.Icc (-radius) radius, f α) =
      (∫ α in (0 : ℝ)..1, f α) -
        ∫ α in Set.Icc radius (1 - radius), f α := by
  rw [integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by linarith : -radius ≤ radius),
    ← intervalIntegral.integral_of_le
      (by linarith : radius ≤ 1 - radius)]
  have htranslated :
      (∫ α in (-radius)..0, f α) =
        ∫ α in (1 - radius)..1, f α := by
    calc
      (∫ α in (-radius)..0, f α) =
          ∫ α in (-radius)..0, f (α + 1) := by
            apply intervalIntegral.integral_congr
            intro α _
            exact (hperiodic α).symm
      _ = ∫ α in (-radius + 1)..(0 + 1), f α :=
        intervalIntegral.integral_comp_add_right f 1
      _ = _ := by congr 1 <;> ring
  have hsymmetric :
      (∫ α in (-radius)..radius, f α) =
        (∫ α in (-radius)..0, f α) +
          ∫ α in (0 : ℝ)..radius, f α :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
  have hfirst :
      (∫ α in (0 : ℝ)..(1 - radius), f α) =
        (∫ α in (0 : ℝ)..radius, f α) +
          ∫ α in radius..(1 - radius), f α :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
  have hfull :
      (∫ α in (0 : ℝ)..1, f α) =
        ((∫ α in (0 : ℝ)..radius, f α) +
          ∫ α in radius..(1 - radius), f α) +
            ∫ α in (1 - radius)..1, f α := by
    rw [← hfirst]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm
  rw [hsymmetric, htranslated, hfull]
  ring

/-- Exact signed singular-integral formula on the REAL symmetric genuine
Farey arc: its main term is the ACTUAL edge-bounded affine lattice count,
and its remainder is precisely the signed three-frequency middle tail. -/
theorem actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
    (a d n : ℕ) (τ ell radius : ℝ)
    (hradius : 0 ≤ radius) (hhalf : 2 * radius ≤ 1) :
    (∫ β in Set.Icc (-radius) radius,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell β) =
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        ∫ β in Set.Icc radius (1 - radius),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β := by
  have hcontinuous :
      Continuous (actualMajorArcArchimedeanSmoothCubic a d n τ ell) := by
    unfold actualMajorArcArchimedeanSmoothCubic
      ternaryExponentialSum GoldbachChain.e
    fun_prop
  rw [actualMajorArcBoundary_periodic_symmetric_eq_whole_sub_middle
    _ hcontinuous
    (actualMajorArcBoundary_smooth_cubic_periodic a d n τ ell)
    radius hradius hhalf,
    actualMajorArcArchimedean_smooth_integral_eq_lattice]

/-- The true symmetric original-arc lattice error is controlled by the
ALREADY-PROVED signed resonant middle-tail bound; all affine resonances,
both edge windows, and the exact real strip survive. -/
theorem actualMajorArcBoundary_smooth_symmetric_lattice_error_le
    (a d n : ℕ) (τ ell radius : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hradius : 0 < radius) (hhalf : 2 * radius ≤ 1) :
    ‖(∫ β in Set.Icc (-radius) radius,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell β) -
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ)‖ ≤
      (n : ℝ) / (2 * radius) := by
  rw [actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
    a d n τ ell radius hradius.le hhalf]
  have hrewrite :
      ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        (∫ β in Set.Icc radius (1 - radius),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β) -
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) =
        -(∫ β in Set.Icc radius (1 - radius),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β) := by ring
  rw [hrewrite, norm_neg]
  exact actualMajorArcTail_smooth_middle_integral_le_scale
    a d n τ ell radius ha hd hradius

/-- The TWO actual original principal center regions, without any duplicate
or exterior center, equal their genuine lattice main term minus the exact
signed middle tail at the ORIGINAL Farey width. -/
theorem actualMajorArcBoundary_actual_center_pair_eq_lattice_sub_middle
    (S : Finset ℕ) (cutoff fareyCutoff a d n : ℕ)
    (τ ell : ℝ)
    (hsupport : 0 < ∏ p ∈ S, p)
    (hcutoff : 0 < cutoff)
    (hfarey : 0 < fareyCutoff) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) 0,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell α) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) 1,
      actualMajorArcArchimedeanSmoothCubic a d n τ ell α) =
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        ∫ β in Set.Icc
          (1 / ((fareyCutoff : ℝ) + 1))
          (1 - 1 / ((fareyCutoff : ℝ) + 1)),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β := by
  rw [actualMajorArcBoundary_actual_center_smooth_pair
    S cutoff fareyCutoff a d n τ ell hsupport hcutoff hfarey]
  apply actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
  · positivity
  · have hreal : (1 : ℝ) ≤ fareyCutoff := by exact_mod_cast hfarey
    calc
      2 * (1 / ((fareyCutoff : ℝ) + 1)) =
          2 / ((fareyCutoff : ℝ) + 1) := by ring
      _ ≤ 1 :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < fareyCutoff + 1)).mpr
          (by nlinarith)

#print axioms Erdos689.actualMajorArcBoundary_exponential_periodic
#print axioms Erdos689.actualMajorArcBoundary_prime_cubic_periodic
#print axioms Erdos689.actualMajorArcBoundary_smooth_cubic_periodic
#print axioms Erdos689.actualMajorArcBoundary_zero_clipped_arc
#print axioms Erdos689.actualMajorArcBoundary_one_clipped_arc
#print axioms Erdos689.actualMajorArcBoundary_periodic_half_arcs_eq_symmetric
#print axioms Erdos689.actualMajorArcBoundary_actual_prime_half_arcs_eq_symmetric
#print axioms Erdos689.actualMajorArcBoundary_actual_smooth_half_arcs_eq_symmetric
#print axioms Erdos689.actualMajorArcBoundary_goldbach_principal_anchor
#print axioms Erdos689.actualMajorArcBoundary_zero_anchor_mem
#print axioms Erdos689.actualMajorArcBoundary_one_anchor_mem
#print axioms Erdos689.actualMajorArcBoundary_center_region_eq_unit_anchor
#print axioms Erdos689.actualMajorArcBoundary_actual_zero_center_region
#print axioms Erdos689.actualMajorArcBoundary_actual_one_center_region
#print axioms Erdos689.actualMajorArcBoundary_zero_center_mem
#print axioms Erdos689.actualMajorArcBoundary_one_center_mem
#print axioms Erdos689.actualMajorArcBoundary_negative_ball_subset_zero_ball
#print axioms Erdos689.actualMajorArcBoundary_above_one_ball_subset_one_ball
#print axioms Erdos689.actualMajorArcBoundary_exterior_center_region_empty
#print axioms Erdos689.actualMajorArcBoundary_actual_center_smooth_pair
#print axioms Erdos689.actualMajorArcBoundary_actual_center_prime_pair
#print axioms Erdos689.actualMajorArcBoundary_real_closedBall_eq_Icc
#print axioms Erdos689.actualMajorArcBoundary_translated_ball_integral
#print axioms Erdos689.actualMajorArcBoundary_periodic_symmetric_eq_whole_sub_middle
#print axioms Erdos689.actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
#print axioms Erdos689.actualMajorArcBoundary_smooth_symmetric_lattice_error_le
#print axioms Erdos689.actualMajorArcBoundary_actual_center_pair_eq_lattice_sub_middle

end Erdos689
