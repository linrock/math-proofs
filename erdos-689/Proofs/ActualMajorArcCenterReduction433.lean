module

public import ActualMajorArcCenterConductor433
public import ActualMajorArcBoundary433

@[expose] public section


/-!
# Exact original shifted-center conductor and widest-anchor reduction

The genuine translated Farey family can contain many equal REAL centers.
Support-linear original denominator factors do not create new centers,
while support-square factors have zero full smooth cubic.  This file keeps
the ORIGINAL finite anchors, their signed reduced numerators, true clipped
center regions, and exact smallest-original-denominator arc geometry.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- At one EXACT REAL shifted center, the reduced numerator of an original
anchor forces its original denominator to divide `W*q'` for ANY other
original representation.  No support-coprime assumption or positivity of
signed numerators is needed. -/
theorem actualMajorArcCenterReduction_same_center_denominator_dvd
    (support denominator denominator' : ℕ)
    (numerator character numerator' character' : ℤ)
    (hsupport : 0 < support)
    (hdenominator : 0 < denominator)
    (hdenominator' : 0 < denominator')
    (hnumerator : Int.gcd numerator denominator = 1)
    (hcenter : shiftedFareyAnchorCenter support
      denominator numerator character =
        shiftedFareyAnchorCenter support
          denominator' numerator' character') :
    denominator ∣ support * denominator' := by
  have hsupportReal : (0 : ℝ) < support := by exact_mod_cast hsupport
  have hdenominatorReal : (0 : ℝ) < denominator := by
    exact_mod_cast hdenominator
  have hdenominator'Real : (0 : ℝ) < denominator' := by
    exact_mod_cast hdenominator'
  have hidentityReal :
      (numerator : ℝ) * support * denominator' -
        (numerator' : ℝ) * support * denominator =
      ((character - character' : ℤ) : ℝ) *
        denominator * denominator' := by
    unfold shiftedFareyAnchorCenter at hcenter
    push_cast
    field_simp at hcenter
    linear_combination hcenter
  have hidentity :
      numerator * (support : ℤ) * (denominator' : ℤ) -
        numerator' * (support : ℤ) * (denominator : ℤ) =
      (character - character') *
        (denominator : ℤ) * (denominator' : ℤ) := by
    exact_mod_cast hidentityReal
  have hdividesProduct :
      (denominator : ℤ) ∣
        numerator * (support : ℤ) * (denominator' : ℤ) := by
    refine ⟨numerator' * (support : ℤ) +
      (character - character') * (denominator' : ℤ), ?_⟩
    linear_combination hidentity
  have hcoprimeNumerator :
      Int.gcd (denominator : ℤ) numerator = 1 := by
    rw [Int.gcd_comm]
    exact hnumerator
  have hdividesSupport :
      (denominator : ℤ) ∣
        (support : ℤ) * (denominator' : ℤ) := by
    apply Int.dvd_of_dvd_mul_left_of_gcd_one
      (a := (denominator : ℤ))
      (b := (support : ℤ) * (denominator' : ℤ))
      (c := numerator) ?_ hcoprimeNumerator
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdividesProduct
  exact Int.natCast_dvd_natCast.mp (by simpa using hdividesSupport)

/-- Any support-coprime ORIGINAL denominator at one real shifted center
divides EVERY other original denominator at that center, including
denominators sharing support primes. -/
theorem actualMajorArcCenterReduction_support_free_denominator_dvd
    (support denominator denominator' : ℕ)
    (numerator character numerator' character' : ℤ)
    (hsupport : 0 < support)
    (hdenominator : 0 < denominator)
    (hdenominator' : 0 < denominator')
    (hnumerator : Int.gcd numerator denominator = 1)
    (hcoprime : Nat.Coprime denominator support)
    (hcenter : shiftedFareyAnchorCenter support
      denominator numerator character =
        shiftedFareyAnchorCenter support
          denominator' numerator' character') :
    denominator ∣ denominator' := by
  exact hcoprime.dvd_of_dvd_mul_left
    (actualMajorArcCenterReduction_same_center_denominator_dvd
      support denominator denominator'
      numerator character numerator' character'
      hsupport hdenominator hdenominator' hnumerator hcenter)

/-- Two genuine reduced support-coprime original denominators represent
the same REAL shifted center if and only if their denominators are equal.
Thus the surviving original conductor is UNIQUE; equal-center support
characters cannot create a second outside denominator. -/
theorem actualMajorArcCenterReduction_support_free_denominator_unique
    (support denominator denominator' : ℕ)
    (numerator character numerator' character' : ℤ)
    (hsupport : 0 < support)
    (hdenominator : 0 < denominator)
    (hdenominator' : 0 < denominator')
    (hnumerator : Int.gcd numerator denominator = 1)
    (hnumerator' : Int.gcd numerator' denominator' = 1)
    (hcoprime : Nat.Coprime denominator support)
    (hcoprime' : Nat.Coprime denominator' support)
    (hcenter : shiftedFareyAnchorCenter support
      denominator numerator character =
        shiftedFareyAnchorCenter support
          denominator' numerator' character') :
    denominator = denominator' := by
  apply Nat.dvd_antisymm
  · exact actualMajorArcCenterReduction_support_free_denominator_dvd
      support denominator denominator'
      numerator character numerator' character'
      hsupport hdenominator hdenominator' hnumerator hcoprime hcenter
  · exact actualMajorArcCenterReduction_support_free_denominator_dvd
      support denominator' denominator
      numerator' character' numerator character
      hsupport hdenominator' hdenominator hnumerator' hcoprime'
      hcenter.symm

/-- At the genuine translated-disjointness cutoff, a nonempty ORIGINAL
clipped center region forces its EXACT real center into `[0,1]`.  Exterior
finite anchors therefore never enter the surviving conductor count. -/
theorem actualMajorArcCenterReduction_nonempty_center_bounds
    (support cutoff fareyCutoff : ℕ) (center : ℝ)
    (hsupport : 0 < support)
    (hcutoff : 0 < cutoff)
    (hseparation : 2 * (support * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses support
      (actualShiftedFareyAnchors support cutoff))
    (hnonempty : (Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion support fareyCutoff
        (actualShiftedFareyAnchors support cutoff) center).Nonempty) :
    0 ≤ center ∧ center ≤ 1 := by
  constructor
  · by_contra hnot
    have hnegative : center < 0 := lt_of_not_ge hnot
    have hempty := actualMajorArcBoundary_exterior_center_region_empty
      support cutoff fareyCutoff center hsupport hcutoff hseparation
      hcenter (Or.inl hnegative)
    rw [hempty] at hnonempty
    exact Set.not_nonempty_empty hnonempty
  · by_contra hnot
    have habove : 1 < center := lt_of_not_ge hnot
    have hempty := actualMajorArcBoundary_exterior_center_region_empty
      support cutoff fareyCutoff center hsupport hcutoff hseparation
      hcenter (Or.inr habove)
    rw [hempty] at hnonempty
    exact Set.not_nonempty_empty hnonempty

/-- An ORIGINAL finite shifted anchor in the actual unit circle has the
complete and exclusive conductor alternatives: either a genuine support
prime square annihilates its ENTIRE actual integrated smooth cubic, or its
same REAL center has an ORIGINAL finite support-coprime anchor with exact
denominator `q/gcd(q,W)`.  No signed center contribution is dropped. -/
theorem actualMajorArcCenterReduction_actual_anchor_dichotomy
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hanchor : anchor ∈ actualShiftedFareyAnchors
      (∏ p ∈ S, p) cutoff)
    (hcenterZero : 0 ≤ shiftedFareyAnchorCenter
      (∏ p ∈ S, p) anchor.1 anchor.2.1 anchor.2.2)
    (hcenterOne : shiftedFareyAnchorCenter
      (∏ p ∈ S, p) anchor.1 anchor.2.1 anchor.2.2 ≤ 1) :
    (∃ p ∈ S, p ^ 2 ∣ anchor.1 ∧
      ∀ α : ℝ, actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α = 0) ∨
      (∃ replacement ∈ actualShiftedFareyAnchors
          (∏ p ∈ S, p) cutoff,
        replacement.1 =
          anchor.1 / Nat.gcd anchor.1 (∏ p ∈ S, p) ∧
        Nat.Coprime replacement.1 (∏ p ∈ S, p) ∧
        shiftedFareyAnchorCenter (∏ p ∈ S, p)
            replacement.1 replacement.2.1 replacement.2.2 =
          shiftedFareyAnchorCenter (∏ p ∈ S, p)
            anchor.1 anchor.2.1 anchor.2.2) := by
  classical
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  by_cases hcoprime : Nat.Coprime
      (anchor.1 / Nat.gcd anchor.1 W) W
  · exact Or.inr
      (actualMajorArcCenter_actual_anchor_support_free_reanchor
        W cutoff anchor hW hanchor hcoprime hcenterZero hcenterOne)
  · have hnot : ¬ ∀ p ∈ S, ¬ p ^ 2 ∣ anchor.1 := by
      intro hnosquares
      exact hcoprime
        ((actualMajorArcCenter_outside_denominator_coprime_iff
          S anchor.1 hsupport).mpr hnosquares)
    push Not at hnot
    obtain ⟨p, hp, hpsquare⟩ := hnot
    refine Or.inl ⟨p, hp, hpsquare, ?_⟩
    intro α
    exact actualMajorArcCenter_actual_anchor_smooth_zero_of_support_square
      S b n target a d cutoff p τ ell α anchor
      hsupport hanchor hp hpsquare

/-- An ORIGINAL support-coprime representative is automatically the WIDEST
anchor of its full deduplicated real-center class.  Its original denominator
divides every competing denominator, so the entire true center region is
EXACTLY its genuine original-denominator Farey ball. -/
theorem actualMajorArcCenterReduction_support_free_anchor_widest
    (support cutoff fareyCutoff : ℕ)
    (anchor : ShiftedFareyAnchor)
    (hsupport : 0 < support)
    (hanchor : anchor ∈ actualShiftedFareyAnchors support cutoff)
    (hcoprime : Nat.Coprime anchor.1 support) :
    shiftedFareyCenterRegion support fareyCutoff
        (actualShiftedFareyAnchors support cutoff)
        (shiftedFareyAnchorCenter support
          anchor.1 anchor.2.1 anchor.2.2) =
      shiftedFareyAnchorArc support fareyCutoff
        anchor.1 anchor.2.1 anchor.2.2 := by
  have hdenominator :=
    (actualShiftedFareyAnchors_denominator_bounds
      support cutoff anchor hanchor).1
  have hnumerator :=
    actualMajorArcCenter_actual_anchor_numerator_coprime
      support cutoff anchor hanchor
  apply Set.Subset.antisymm
  · intro α hα
    simp only [shiftedFareyCenterRegion, Set.mem_iUnion] at hα
    obtain ⟨other, hfiltered, hball⟩ := hα
    obtain ⟨hother, hsame⟩ := Finset.mem_filter.mp hfiltered
    have hotherPositive :=
      (actualShiftedFareyAnchors_denominator_bounds
        support cutoff other hother).1
    have hdivides :=
      actualMajorArcCenterReduction_support_free_denominator_dvd
        support anchor.1 other.1
        anchor.2.1 anchor.2.2 other.2.1 other.2.2
        hsupport hdenominator hotherPositive
        hnumerator hcoprime hsame.symm
    have hdenominatorLe : anchor.1 ≤ other.1 :=
      Nat.le_of_dvd hotherPositive hdivides
    unfold shiftedFareyAnchorArc at hball ⊢
    rw [hsame] at hball
    apply (Metric.closedBall_subset_closedBall ?_) hball
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hdenominatorLe) (by positivity)
  · intro α hα
    simp only [shiftedFareyCenterRegion, Set.mem_iUnion]
    exact ⟨anchor, Finset.mem_filter.mpr ⟨hanchor, rfl⟩, hα⟩

/-- Complete ACTUAL deduplicated-center reduction. Every nonempty clipped
center has a genuine widest original anchor. Either its entire actual smooth
cubic vanishes because a support prime occurs to second order, or the widest
anchor can be chosen support-coprime, with denominator dividing EVERY other
original denominator at the same REAL center. This retains the exact
original clipped region, signed numerators, and all switched/unit cells. -/
theorem actualMajorArcCenterReduction_actual_center_dichotomy
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ) (τ ell center : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1)
    (hcenter : center ∈ shiftedFareyCenterClasses
      (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff))
    (hnonempty : (Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff)
        center).Nonempty) :
    ∃ anchor ∈ actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff,
      shiftedFareyAnchorCenter (∏ p ∈ S, p)
          anchor.1 anchor.2.1 anchor.2.2 = center ∧
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
          (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center =
        shiftedFareyAnchorArc (∏ p ∈ S, p) fareyCutoff
          anchor.1 anchor.2.1 anchor.2.2 ∧
      ((∃ p ∈ S, p ^ 2 ∣ anchor.1 ∧
          ∀ α : ℝ, actualMajorArcIntegratedAnchorSmooth
            S b n target a d τ ell anchor α = 0) ∨
        (Nat.Coprime anchor.1 (∏ p ∈ S, p) ∧
          ∀ other ∈ actualShiftedFareyAnchors
              (∏ p ∈ S, p) cutoff,
            shiftedFareyAnchorCenter (∏ p ∈ S, p)
                other.1 other.2.1 other.2.2 = center →
              anchor.1 ∣ other.1)) := by
  classical
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  obtain ⟨hzero, hone⟩ :=
    actualMajorArcCenterReduction_nonempty_center_bounds
      W cutoff fareyCutoff center hW hcutoff hseparation
      hcenter hnonempty
  obtain ⟨widest, hwidest, hwidestCenter, hwidestRegion⟩ :=
    shiftedFareyCenterRegion_eq_widest_anchor
      W fareyCutoff (actualShiftedFareyAnchors W cutoff)
      center hcenter (fun anchor hanchor =>
        (actualShiftedFareyAnchors_denominator_bounds
          W cutoff anchor hanchor).1)
  have hzeroWidest :
      0 ≤ shiftedFareyAnchorCenter W
        widest.1 widest.2.1 widest.2.2 := by
    rwa [hwidestCenter]
  have honeWidest :
      shiftedFareyAnchorCenter W
        widest.1 widest.2.1 widest.2.2 ≤ 1 := by
    rwa [hwidestCenter]
  rcases actualMajorArcCenterReduction_actual_anchor_dichotomy
      S b n target a d cutoff τ ell widest hsupport hwidest
      hzeroWidest honeWidest with hsquare | hreplacement
  · exact ⟨widest, hwidest, hwidestCenter,
      hwidestRegion, Or.inl hsquare⟩
  · obtain ⟨anchor, hanchor, hdenominator,
      hcoprime, hsame⟩ := hreplacement
    have hanchorCenter : shiftedFareyAnchorCenter W
        anchor.1 anchor.2.1 anchor.2.2 = center :=
      hsame.trans hwidestCenter
    have hanchorRegion :
        shiftedFareyCenterRegion W fareyCutoff
            (actualShiftedFareyAnchors W cutoff) center =
          shiftedFareyAnchorArc W fareyCutoff
            anchor.1 anchor.2.1 anchor.2.2 := by
      rw [← hanchorCenter]
      exact actualMajorArcCenterReduction_support_free_anchor_widest
        W cutoff fareyCutoff anchor hW hanchor hcoprime
    refine ⟨anchor, hanchor, hanchorCenter, hanchorRegion,
      Or.inr ⟨hcoprime, ?_⟩⟩
    intro other hother hotherCenter
    apply actualMajorArcCenterReduction_support_free_denominator_dvd
      W anchor.1 other.1
      anchor.2.1 anchor.2.2 other.2.1 other.2.2 hW
      (actualShiftedFareyAnchors_denominator_bounds
        W cutoff anchor hanchor).1
      (actualShiftedFareyAnchors_denominator_bounds
        W cutoff other hother).1
      (actualMajorArcCenter_actual_anchor_numerator_coprime
        W cutoff anchor hanchor)
      hcoprime
    exact hanchorCenter.trans hotherCenter.symm

#print axioms Erdos689.actualMajorArcCenterReduction_same_center_denominator_dvd
#print axioms Erdos689.actualMajorArcCenterReduction_support_free_denominator_dvd
#print axioms Erdos689.actualMajorArcCenterReduction_support_free_denominator_unique
#print axioms Erdos689.actualMajorArcCenterReduction_nonempty_center_bounds
#print axioms Erdos689.actualMajorArcCenterReduction_actual_anchor_dichotomy
#print axioms Erdos689.actualMajorArcCenterReduction_support_free_anchor_widest
#print axioms Erdos689.actualMajorArcCenterReduction_actual_center_dichotomy

end Erdos689
