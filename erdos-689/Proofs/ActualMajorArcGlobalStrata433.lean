import ActualMajorArcExceptionClosure433
import ActualMajorArcCenterReindex433
import ActualConductorDedupCompletion433
import ActualCenterCouplingFourier433
import ActualMajorArcInterior433
import ActualMajorArcParityCRT433
import ActualMajorArcSignedTailAssembly433

/-!
# Exact global genuine-major-center conductor strata

The original translated major family has duplicated anchors, exterior
centers, two distinct clipped boundary centers, support-linear conductor
aliases, and vanishing support-square branches. This file partitions
actual REAL centers on the half-open Fourier circle by their UNIQUE
support-coprime original denominator. All finite identities preserve
arbitrary signed weights, so no major contribution is discarded by an
unproved positivity assumption.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The exact original support-free denominator range, including parity. -/
noncomputable def actualMajorArcGlobalStrataDenominators
    (support cutoff : ℕ) : Finset ℕ :=
  (Finset.Icc 1 cutoff).filter fun denominator =>
    Nat.Coprime denominator support

/-- All genuine half-open-circle centers possessing an ORIGINAL
support-coprime anchor, without any duplicate anchor representative. -/
noncomputable def actualMajorArcGlobalStrataSupportFreeCenters
    (support cutoff : ℕ) : Finset ℝ :=
  (actualMajorArcGlobalStrataDenominators support cutoff).biUnion
    (actualMajorArcCenterReindexActualStratum support cutoff)

/-- Distinct original support-free denominators have DISJOINT actual REAL
center strata. This uses exact reduced numerator uniqueness, not counting. -/
theorem actualMajorArcGlobalStrata_support_free_pairwise_disjoint
    (support cutoff : ℕ) (hsupport : 0 < support) :
    ((actualMajorArcGlobalStrataDenominators support cutoff) : Set ℕ).PairwiseDisjoint
        (actualMajorArcCenterReindexActualStratum support cutoff) := by
  intro denominator hdenominator other hother hne
  apply Finset.disjoint_left.mpr
  intro center hcenter hcenter'
  obtain ⟨hinterval, hcoprime⟩ :=
    Finset.mem_filter.mp hdenominator
  obtain ⟨hinterval', hcoprime'⟩ :=
    Finset.mem_filter.mp hother
  obtain ⟨hpositive, _⟩ := Finset.mem_Icc.mp hinterval
  obtain ⟨hpositive', _⟩ := Finset.mem_Icc.mp hinterval'
  unfold actualMajorArcCenterReindexActualStratum at hcenter hcenter'
  obtain ⟨_, _, _, anchor, hanchor, hdenominatorEq, hreal⟩ :=
    Finset.mem_filter.mp hcenter
  obtain ⟨_, _, _, anchor', hanchor', hotherEq, hreal'⟩ :=
    Finset.mem_filter.mp hcenter'
  have hnumerator : Int.gcd anchor.2.1 denominator = 1 := by
    simpa [hdenominatorEq] using
      actualMajorArcCenter_actual_anchor_numerator_coprime
        support cutoff anchor hanchor
  have hnumerator' : Int.gcd anchor'.2.1 other = 1 := by
    simpa [hotherEq] using
      actualMajorArcCenter_actual_anchor_numerator_coprime
        support cutoff anchor' hanchor'
  apply hne
  apply actualMajorArcCenterReduction_support_free_denominator_unique
    support denominator other anchor.2.1 anchor.2.2
      anchor'.2.1 anchor'.2.2
      hsupport hpositive hpositive' hnumerator hnumerator'
        hcoprime hcoprime'
  simpa [hdenominatorEq, hotherEq] using hreal.trans hreal'.symm

/-- Exact membership in the GLOBAL support-free genuine-center family:
an ORIGINAL distinct center belongs iff it lies in `[0,1)` and has a
genuine support-coprime original anchor at its EXACT real value. -/
theorem actualMajorArcGlobalStrata_support_free_mem_iff
    (support cutoff : ℕ) (center : ℝ) :
    center ∈ actualMajorArcGlobalStrataSupportFreeCenters
        support cutoff ↔
      center ∈ shiftedFareyCenterClasses support
          (actualShiftedFareyAnchors support cutoff) ∧
        0 ≤ center ∧ center < 1 ∧
        ∃ anchor ∈ actualShiftedFareyAnchors support cutoff,
          Nat.Coprime anchor.1 support ∧
            shiftedFareyAnchorCenter support
              anchor.1 anchor.2.1 anchor.2.2 = center := by
  classical
  constructor
  · intro hmember
    obtain ⟨denominator, hdenominator, hstratum⟩ :=
      Finset.mem_biUnion.mp hmember
    obtain ⟨_, hcoprime⟩ := Finset.mem_filter.mp hdenominator
    unfold actualMajorArcCenterReindexActualStratum at hstratum
    obtain ⟨hactual, hzero, hone, anchor, hanchor,
      hdenominatorEq, hcenter⟩ := Finset.mem_filter.mp hstratum
    refine ⟨hactual, hzero, hone, anchor, hanchor, ?_, hcenter⟩
    simpa [hdenominatorEq] using hcoprime
  · rintro ⟨hactual, hzero, hone, anchor,
      hanchor, hcoprime, hcenter⟩
    have hbounds := actualShiftedFareyAnchors_denominator_bounds
      support cutoff anchor hanchor
    unfold actualMajorArcGlobalStrataSupportFreeCenters
    apply Finset.mem_biUnion.mpr
    refine ⟨anchor.1, ?_, ?_⟩
    · unfold actualMajorArcGlobalStrataDenominators
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hbounds.1, hbounds.2⟩, hcoprime⟩
    · unfold actualMajorArcCenterReindexActualStratum
      exact Finset.mem_filter.mpr
        ⟨hactual, hzero, hone, anchor, hanchor, rfl, hcenter⟩

/-- Arbitrary-additive-weight global finite reindexing of ALL actual
support-free center strata into reduced numerators and EVERY true support
character, with each genuine REAL center counted exactly once. -/
theorem actualMajorArcGlobalStrata_support_free_sum
    {A : Type*} [AddCommMonoid A]
    (support cutoff : ℕ) (weight : ℝ → A)
    (hsupport : 0 < support) :
    (∑ center ∈ actualMajorArcGlobalStrataSupportFreeCenters
      support cutoff, weight center) =
      ∑ denominator ∈ actualMajorArcGlobalStrataDenominators
          support cutoff,
        ∑ numerator ∈ (Finset.range denominator).filter
            (fun numerator => Nat.gcd numerator denominator = 1),
          ∑ shift ∈ Finset.range support,
            weight (actualMajorArcCenterReindexNormalizedCenter
              support denominator numerator
                (actualMajorArcCenterReindexNegShift support shift)) := by
  classical
  unfold actualMajorArcGlobalStrataSupportFreeCenters
  rw [Finset.sum_biUnion
    (actualMajorArcGlobalStrata_support_free_pairwise_disjoint
      support cutoff hsupport)]
  apply Finset.sum_congr rfl
  intro denominator hdenominator
  obtain ⟨hinterval, hcoprime⟩ :=
    Finset.mem_filter.mp hdenominator
  obtain ⟨hpositive, hcutoff⟩ := Finset.mem_Icc.mp hinterval
  exact actualMajorArcCenterReindex_actual_stratum_sum
    support cutoff denominator weight
      hsupport hpositive hcutoff hcoprime

/-- The exact finite half-open original Fourier-circle center set. -/
noncomputable def actualMajorArcGlobalStrataHalfOpenCenters
    (support cutoff : ℕ) : Finset ℝ :=
  (shiftedFareyCenterClasses support
    (actualShiftedFareyAnchors support cutoff)).filter
      fun center => 0 ≤ center ∧ center < 1

/-- The support-free real-center family is a genuine SUBSET of the
original half-open Fourier-circle center set. -/
theorem actualMajorArcGlobalStrata_support_free_subset_half_open
    (support cutoff : ℕ) :
    actualMajorArcGlobalStrataSupportFreeCenters support cutoff ⊆
      actualMajorArcGlobalStrataHalfOpenCenters support cutoff := by
  intro center hcenter
  obtain ⟨hactual, hzero, hone, _⟩ :=
    (actualMajorArcGlobalStrata_support_free_mem_iff
      support cutoff center).mp hcenter
  exact Finset.mem_filter.mpr ⟨hactual, hzero, hone⟩

/-- EXACT signed weighted global half-open-center partition whenever the
remaining support-square strata have rigorously zero weight. The premise
is pointwise vanishing, never a positivity assumption or discarded term. -/
theorem actualMajorArcGlobalStrata_half_open_weighted_sum
    {A : Type*} [AddCommMonoid A]
    (support cutoff : ℕ) (weight : ℝ → A)
    (hsupport : 0 < support)
    (hvanish : ∀ center ∈ actualMajorArcGlobalStrataHalfOpenCenters
      support cutoff,
      (¬ ∃ anchor ∈ actualShiftedFareyAnchors support cutoff,
        Nat.Coprime anchor.1 support ∧
          shiftedFareyAnchorCenter support
            anchor.1 anchor.2.1 anchor.2.2 = center) →
        weight center = 0) :
    (∑ center ∈ actualMajorArcGlobalStrataHalfOpenCenters
      support cutoff, weight center) =
      ∑ denominator ∈ actualMajorArcGlobalStrataDenominators
          support cutoff,
        ∑ numerator ∈ (Finset.range denominator).filter
            (fun numerator => Nat.gcd numerator denominator = 1),
          ∑ shift ∈ Finset.range support,
            weight (actualMajorArcCenterReindexNormalizedCenter
              support denominator numerator
                (actualMajorArcCenterReindexNegShift support shift)) := by
  calc
    (∑ center ∈ actualMajorArcGlobalStrataHalfOpenCenters
      support cutoff, weight center) =
        ∑ center ∈ actualMajorArcGlobalStrataSupportFreeCenters
          support cutoff, weight center := by
      symm
      apply Finset.sum_subset
        (actualMajorArcGlobalStrata_support_free_subset_half_open
          support cutoff)
      intro center hhalf hnot
      apply hvanish center hhalf
      intro hexists
      apply hnot
      apply (actualMajorArcGlobalStrata_support_free_mem_iff
        support cutoff center).mpr
      obtain ⟨hactual, hzero, hone⟩ := Finset.mem_filter.mp hhalf
      exact ⟨hactual, hzero, hone, hexists⟩
    _ = _ := actualMajorArcGlobalStrata_support_free_sum
      support cutoff weight hsupport

/-- Exact original-circle endpoint gluing for ARBITRARY additive signed
weights: exterior centers vanish, the distinct `0` and `1` centers are
paired once at the half-open representative `0`, and every interior center
retains its original contribution. -/
theorem actualMajorArcGlobalStrata_boundary_paired_sum
    {A : Type*} [AddCommMonoid A]
    (support cutoff : ℕ) (weight : ℝ → A)
    (hsupport : 0 < support) (hcutoff : 0 < cutoff)
    (hexterior : ∀ center ∈ shiftedFareyCenterClasses support
      (actualShiftedFareyAnchors support cutoff),
      (center < 0 ∨ 1 < center) → weight center = 0) :
    (∑ center ∈ shiftedFareyCenterClasses support
      (actualShiftedFareyAnchors support cutoff), weight center) =
      ∑ center ∈ actualMajorArcGlobalStrataHalfOpenCenters
        support cutoff,
        if center = 0 then weight 0 + weight 1 else weight center := by
  classical
  let centers := shiftedFareyCenterClasses support
    (actualShiftedFareyAnchors support cutoff)
  let half := actualMajorArcGlobalStrataHalfOpenCenters support cutoff
  let closed := centers.filter fun center => 0 ≤ center ∧ center ≤ 1
  have hzeroCenter : (0 : ℝ) ∈ centers :=
    actualMajorArcBoundary_zero_center_mem
      support cutoff hsupport hcutoff
  have honeCenter : (1 : ℝ) ∈ centers :=
    actualMajorArcBoundary_one_center_mem
      support cutoff hsupport hcutoff
  have hzeroHalf : (0 : ℝ) ∈ half := by
    exact Finset.mem_filter.mpr ⟨hzeroCenter, by norm_num, by norm_num⟩
  have honeHalf : (1 : ℝ) ∉ half := by
    intro hone
    have hlt := (Finset.mem_filter.mp hone).2.2
    linarith
  have hclosed : closed = insert (1 : ℝ) half := by
    ext center
    constructor
    · intro hmember
      obtain ⟨hactual, hzero, hone⟩ :=
        Finset.mem_filter.mp hmember
      by_cases hequal : center = 1
      · exact Finset.mem_insert.mpr (Or.inl hequal)
      · apply Finset.mem_insert.mpr
        right
        exact Finset.mem_filter.mpr
          ⟨hactual, hzero, lt_of_le_of_ne hone hequal⟩
    · intro hmember
      obtain hequal | hhalf := Finset.mem_insert.mp hmember
      · subst center
        exact Finset.mem_filter.mpr
          ⟨honeCenter, by norm_num, le_rfl⟩
      · obtain ⟨hactual, hzero, hone⟩ :=
          Finset.mem_filter.mp hhalf
        exact Finset.mem_filter.mpr
          ⟨hactual, hzero, hone.le⟩
  have hrestrict :
      (∑ center ∈ centers, weight center) =
        ∑ center ∈ closed, weight center := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro center hactual hnot
    apply hexterior center hactual
    by_cases hzero : 0 ≤ center
    · right
      apply lt_of_not_ge
      intro hone
      apply hnot
      exact Finset.mem_filter.mpr ⟨hactual, hzero, hone⟩
    · left
      exact lt_of_not_ge hzero
  change (∑ center ∈ centers, weight center) =
    ∑ center ∈ half,
      if center = 0 then weight 0 + weight 1 else weight center
  calc
    (∑ center ∈ centers, weight center) =
        ∑ center ∈ closed, weight center := hrestrict
    _ = weight 1 + ∑ center ∈ half, weight center := by
      rw [hclosed, Finset.sum_insert honeHalf]
    _ = ∑ center ∈ half,
        (weight center + if center = 0 then weight 1 else 0) := by
      rw [Finset.sum_add_distrib]
      simp [hzeroHalf, add_comm]
    _ = ∑ center ∈ half,
        if center = 0 then weight 0 + weight 1 else weight center := by
      apply Finset.sum_congr rfl
      intro center hcenter
      split_ifs with hequal
      · subst center
        rfl
      · simp

/-- The EXACT canonical-widest smooth contribution attached to a genuine
original REAL center, extended by zero only outside its ACTUAL finite
center domain. Every true clipped arc and switched-unit cell is retained. -/
noncomputable def actualMajorArcGlobalStrataCanonicalWeight
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ) (center : ℝ) : ℝ :=
  if hcenter : center ∈ shiftedFareyCenterClasses (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) then
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff
            ⟨center, hcenter⟩) α).re
  else 0

/-- Attaching center-membership proofs does not alter the ACTUAL genuine
canonical-widest smooth contribution at any coefficient pair. -/
theorem actualMajorArcGlobalStrata_canonical_attached_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ) :
    (∑ center ∈
      (shiftedFareyCenterClasses (∏ p ∈ S, p)
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff)).attach,
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
          (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center.val,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            (∏ p ∈ S, p) cutoff fareyCutoff center) α).re) =
      ∑ center ∈ shiftedFareyCenterClasses (∏ p ∈ S, p)
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff),
        actualMajorArcGlobalStrataCanonicalWeight
          S b n target a d cutoff fareyCutoff τ ell center := by
  classical
  rw [← Finset.sum_attach
    (shiftedFareyCenterClasses (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff))
    (actualMajorArcGlobalStrataCanonicalWeight
      S b n target a d cutoff fareyCutoff τ ell)]
  apply Finset.sum_congr rfl
  intro center hcenter
  unfold actualMajorArcGlobalStrataCanonicalWeight
  simp [center.property]

/-- Every exterior actual center has ZERO genuine canonical smooth
integral, because its exact original clipped center region is empty. -/
theorem actualMajorArcGlobalStrata_canonical_exterior_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell center : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses
      (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff))
    (hexterior : center < 0 ∨ 1 < center) :
    actualMajorArcGlobalStrataCanonicalWeight
      S b n target a d cutoff fareyCutoff τ ell center = 0 := by
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hempty := actualMajorArcBoundary_exterior_center_region_empty
    (∏ p ∈ S, p) cutoff fareyCutoff center
      hW hcutoff hseparation hcenter hexterior
  unfold actualMajorArcGlobalStrataCanonicalWeight
  simp [hcenter, hempty]

/-- A genuine half-open center with NO original support-free anchor has
zero actual canonical smooth weight. This is the true support-prime-square
cancellation branch, and it holds for EVERY coefficient pair, including
noncoprime pairs. No support-free signed contribution is discarded. -/
theorem actualMajorArcGlobalStrata_canonical_zero_of_no_support_free
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell center : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcenter : center ∈ shiftedFareyCenterClasses
      (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff))
    (hzero : 0 ≤ center) (hone : center ≤ 1)
    (hno : ¬ ∃ anchor ∈ actualShiftedFareyAnchors
      (∏ p ∈ S, p) cutoff,
      Nat.Coprime anchor.1 (∏ p ∈ S, p) ∧
        shiftedFareyAnchorCenter (∏ p ∈ S, p)
          anchor.1 anchor.2.1 anchor.2.2 = center) :
    actualMajorArcGlobalStrataCanonicalWeight
      S b n target a d cutoff fareyCutoff τ ell center = 0 := by
  let attached : ActualMajorArcGlobalCenter
    (∏ p ∈ S, p) cutoff := ⟨center, hcenter⟩
  obtain hvanish | hcoprime :=
    actualConductorDedup_canonical_support_square_or_coprime
      S b n target a d cutoff fareyCutoff τ ell attached
        hsupport hzero hone
  · obtain ⟨_, _, _, hzeroCubic⟩ := hvanish
    unfold actualMajorArcGlobalStrataCanonicalWeight
    simp only [dif_pos hcenter]
    have hpoint : ∀ α : ℝ,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            (∏ p ∈ S, p) cutoff fareyCutoff
              ⟨center, hcenter⟩) α = 0 := hzeroCubic
    simp_rw [hpoint]
    simp
  · exfalso
    apply hno
    let anchor := actualMajorArcGlobalCanonicalWidestAnchor
      (∏ p ∈ S, p) cutoff fareyCutoff attached
    obtain ⟨hanchor, hreal, _⟩ :=
      actualMajorArcGlobalCanonicalWidestAnchor_spec
        (∏ p ∈ S, p) cutoff fareyCutoff attached
    exact ⟨anchor, hanchor, hcoprime, hreal⟩

/-- The paired boundary weight: actual zero- and one-center integrals are
combined ONCE, while every genuine interior center remains unchanged. -/
noncomputable def actualMajorArcGlobalStrataPairedCanonicalWeight
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ) (center : ℝ) : ℝ :=
  if center = 0 then
    actualMajorArcGlobalStrataCanonicalWeight
      S b n target a d cutoff fareyCutoff τ ell 0 +
    actualMajorArcGlobalStrataCanonicalWeight
      S b n target a d cutoff fareyCutoff τ ell 1
  else
    actualMajorArcGlobalStrataCanonicalWeight
      S b n target a d cutoff fareyCutoff τ ell center

/-- COMPLETE exact actual-center partition at EACH original coefficient
pair. Every distinct real center is retained, exterior arcs are proved
empty, the genuine `0/1` clipped principal contributions are paired once,
support-square branches are proved zero, and the remaining true centers
are reindexed by ORIGINAL support-free denominator, reduced numerator, and
all `W` genuine support characters. No `gcd(a,d)=1` is assumed. -/
theorem actualMajorArcGlobalStrata_actual_canonical_center_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1) :
    (∑ center ∈
      (shiftedFareyCenterClasses (∏ p ∈ S, p)
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff)).attach,
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
          (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center.val,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            (∏ p ∈ S, p) cutoff fareyCutoff center) α).re) =
      ∑ denominator ∈ actualMajorArcGlobalStrataDenominators
          (∏ p ∈ S, p) cutoff,
        ∑ numerator ∈ (Finset.range denominator).filter
            (fun numerator => Nat.gcd numerator denominator = 1),
          ∑ shift ∈ Finset.range (∏ p ∈ S, p),
            actualMajorArcGlobalStrataPairedCanonicalWeight
              S b n target a d cutoff fareyCutoff τ ell
              (actualMajorArcCenterReindexNormalizedCenter
                (∏ p ∈ S, p) denominator numerator
                  (actualMajorArcCenterReindexNegShift
                    (∏ p ∈ S, p) shift)) := by
  let W := ∏ p ∈ S, p
  have hW : 0 < W :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  let weight := actualMajorArcGlobalStrataCanonicalWeight
    S b n target a d cutoff fareyCutoff τ ell
  let paired := actualMajorArcGlobalStrataPairedCanonicalWeight
    S b n target a d cutoff fareyCutoff τ ell
  rw [actualMajorArcGlobalStrata_canonical_attached_sum]
  rw [actualMajorArcGlobalStrata_boundary_paired_sum
    W cutoff weight hW hcutoff (fun center hcenter hexterior =>
      actualMajorArcGlobalStrata_canonical_exterior_zero
        S b n target a d cutoff fareyCutoff τ ell center
          hsupport hcutoff hseparation hcenter hexterior)]
  change
    (∑ center ∈ actualMajorArcGlobalStrataHalfOpenCenters W cutoff,
      paired center) = _
  apply actualMajorArcGlobalStrata_half_open_weighted_sum
    W cutoff paired hW
  intro center hcenter hno
  obtain ⟨hactual, hzero, hone⟩ := Finset.mem_filter.mp hcenter
  have hnonzero : center ≠ 0 := by
    intro hequal
    subst center
    apply hno
    refine ⟨(1, (0 : ℤ), (0 : ℤ)),
      actualMajorArcBoundary_zero_anchor_mem
        W cutoff hW hcutoff, ?_, ?_⟩
    · exact Nat.coprime_one_left W
    · simp [shiftedFareyAnchorCenter]
  dsimp only [paired]
  unfold actualMajorArcGlobalStrataPairedCanonicalWeight
  simp only [if_neg hnonzero]
  exact actualMajorArcGlobalStrata_canonical_zero_of_no_support_free
    S b n target a d cutoff fareyCutoff τ ell center
      hsupport hactual hzero hone.le hno

/-- The COMPLETE genuine support-divisor-summed canonical smooth mass is
exactly the global denominator/numerator/support-character partition,
including its paired principal boundary and all noncoprime coefficient
pairs. This is a finite identity on the ORIGINAL center family. -/
theorem actualMajorArcGlobalStrata_actual_pure_smooth_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target cutoff fareyCutoff : ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1) :
    actualMajorArcExceptionCanonicalSmoothMass
        S b n target cutoff fareyCutoff τ ell =
      ∑ a ∈ (∏ p ∈ S, p).divisors,
        ∑ d ∈ (∏ p ∈ S, p).divisors,
          ∑ denominator ∈ actualMajorArcGlobalStrataDenominators
              (∏ p ∈ S, p) cutoff,
            ∑ numerator ∈ (Finset.range denominator).filter
                (fun numerator => Nat.gcd numerator denominator = 1),
              ∑ shift ∈ Finset.range (∏ p ∈ S, p),
                actualMajorArcGlobalStrataPairedCanonicalWeight
                  S b n target a d cutoff fareyCutoff τ ell
                  (actualMajorArcCenterReindexNormalizedCenter
                    (∏ p ∈ S, p) denominator numerator
                      (actualMajorArcCenterReindexNegShift
                        (∏ p ∈ S, p) shift)) := by
  unfold actualMajorArcExceptionCanonicalSmoothMass
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  exact actualMajorArcGlobalStrata_actual_canonical_center_sum
    S b n target a d cutoff fareyCutoff τ ell
      hsupport hcutoff hseparation

#print axioms Erdos689.actualMajorArcGlobalStrata_support_free_pairwise_disjoint
#print axioms Erdos689.actualMajorArcGlobalStrata_support_free_mem_iff
#print axioms Erdos689.actualMajorArcGlobalStrata_support_free_sum
#print axioms Erdos689.actualMajorArcGlobalStrata_support_free_subset_half_open
#print axioms Erdos689.actualMajorArcGlobalStrata_half_open_weighted_sum
#print axioms Erdos689.actualMajorArcGlobalStrata_boundary_paired_sum
#print axioms Erdos689.actualMajorArcGlobalStrata_canonical_attached_sum
#print axioms Erdos689.actualMajorArcGlobalStrata_canonical_exterior_zero
#print axioms Erdos689.actualMajorArcGlobalStrata_canonical_zero_of_no_support_free
#print axioms Erdos689.actualMajorArcGlobalStrata_actual_canonical_center_sum
#print axioms Erdos689.actualMajorArcGlobalStrata_actual_pure_smooth_sum

end Erdos689
