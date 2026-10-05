module

public import AdaptiveMixedPairedSingularPositive1139
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

@[expose] public section


/-!
# Genuine bounded Jordan domains for the signed mixed prime systems

The published finite-complexity affine-linear prime theorem is applied to
bounded convex bodies.  The original, shared-label, and shared-target
domains occurring in the #1139 reduction are indeed bounded; each convex
subwindow has finite volume and null boundary.  These geometric applicability
conditions are proved outright, without any prime-pattern counting input.
-/

open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1139

/-- Product Lebesgue measure on the genuine three-coordinate signed cells is
additive Haar measure; Mathlib does not synthesize this nested product
instance automatically. -/
local instance adaptiveMixedSignedThreeVolume_isAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Every genuine signed center in a normalized physical fundamental strip
lies in an explicit bounded interval; negative centers are retained. -/
theorem adaptiveMixedSignedPhysicalCenter_mem_coarse_interval
    (support : Finset ℕ) (base : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    {label center : ℝ}
    (label_nonnegative : 0 ≤ label)
    (label_upper : label ≤ 2)
    (physical_positive :
      0 < (base : ℝ) * label +
        (adaptiveMixedTypeModulus support : ℝ) * center)
    (physical_upper :
      (base : ℝ) * label +
        (adaptiveMixedTypeModulus support : ℝ) * center < label) :
    -(2 * (base : ℝ)) ≤ center ∧ center ≤ 2 := by
  have modulus_one : (1 : ℝ) ≤ adaptiveMixedTypeModulus support := by
    exact_mod_cast (adaptiveMixedTypeModulus_pos support primes)
  have base_nonnegative : (0 : ℝ) ≤ base := Nat.cast_nonneg base
  constructor
  · by_contra not_lower
    have center_small : center < -(2 * (base : ℝ)) :=
      lt_of_not_ge not_lower
    have center_nonpositive : center ≤ 0 := by nlinarith
    have scaled_center :
        (adaptiveMixedTypeModulus support : ℝ) * center ≤ center := by
      simpa using mul_le_mul_of_nonpos_right modulus_one center_nonpositive
    have scaled_base : (base : ℝ) * label ≤ 2 * (base : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left label_upper base_nonnegative]
    linarith
  · by_contra not_upper
    have center_large : 2 < center := lt_of_not_ge not_upper
    have center_nonnegative : 0 ≤ center := by linarith
    have scaled_center :
        center ≤ (adaptiveMixedTypeModulus support : ℝ) * center := by
      simpa using mul_le_mul_of_nonneg_right modulus_one center_nonnegative
    have scaled_base : 0 ≤ (base : ℝ) * label :=
      mul_nonneg base_nonnegative label_nonnegative
    linarith

/-- The TRUE two-coordinate signed original physical domain is bounded.
The enclosure contains negative centers and does not substitute a positive
coordinate box. -/
theorem adaptiveMixedSignedOriginalPhysicalDomain_isBounded
    (support : Finset ℕ) (base : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    IsBounded (adaptiveMixedSignedOriginalPhysicalDomain support base) := by
  refine (Metric.isBounded_Icc
    ((0 : ℝ), -(2 * (base : ℝ))) ((2 : ℝ), (2 : ℝ))).subset ?_
  intro point selected
  change
    1 < point.1 ∧ point.1 < 2 ∧
      0 < (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 ∧
      (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 < point.1
    at selected
  obtain ⟨lower_center, upper_center⟩ :=
    adaptiveMixedSignedPhysicalCenter_mem_coarse_interval support base primes
      (by linarith [selected.1]) selected.2.1.le
      selected.2.2.1 selected.2.2.2
  exact ⟨⟨by linarith [selected.1], lower_center⟩,
    ⟨selected.2.1.le, upper_center⟩⟩

/-- The TRUE three-coordinate common-label physical domain is bounded with
both separately signed centers retained. -/
theorem adaptiveMixedSignedSharedLabelPhysicalDomain_isBounded
    (support : Finset ℕ) (firstBase secondBase : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    IsBounded
      (adaptiveMixedSignedSharedLabelPhysicalDomain
        support firstBase secondBase) := by
  refine (Metric.isBounded_Icc
    ((0 : ℝ), (-(2 * (firstBase : ℝ)), -(2 * (secondBase : ℝ))))
    ((2 : ℝ), ((2 : ℝ), (2 : ℝ)))).subset ?_
  intro point selected
  change
    1 < point.1 ∧ point.1 < 2 ∧
      0 < (firstBase : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2.1 ∧
      (firstBase : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2.1 < point.1 ∧
      0 < (secondBase : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2.2 ∧
      (secondBase : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2.2 < point.1
    at selected
  obtain ⟨first_lower, first_upper⟩ :=
    adaptiveMixedSignedPhysicalCenter_mem_coarse_interval
      support firstBase primes (by linarith [selected.1]) selected.2.1.le
      selected.2.2.1 selected.2.2.2.1
  obtain ⟨second_lower, second_upper⟩ :=
    adaptiveMixedSignedPhysicalCenter_mem_coarse_interval
      support secondBase primes (by linarith [selected.1]) selected.2.1.le
      selected.2.2.2.2.1 selected.2.2.2.2.2
  exact ⟨⟨by linarith [selected.1], ⟨first_lower, second_lower⟩⟩,
    ⟨selected.2.1.le, ⟨first_upper, second_upper⟩⟩⟩

/-- Every actual simultaneous target/label physical convex cell is bounded,
including its genuine moving-strip constraints. -/
theorem adaptiveMixedSharedTargetPhysicalConvexWindow_isBounded
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ) :
    IsBounded
      (adaptiveMixedSharedTargetPhysicalConvexWindow
        firstIndex secondIndex targetLower targetUpper
          firstLabelLower firstLabelUpper
          secondLabelLower secondLabelUpper) := by
  refine (Metric.isBounded_Icc
    (targetLower, (firstLabelLower, secondLabelLower))
    (targetUpper, (firstLabelUpper, secondLabelUpper))).subset ?_
  intro point selected
  exact ⟨⟨selected.1.le, ⟨selected.2.2.1.le, selected.2.2.2.2.1.le⟩⟩,
    ⟨selected.2.1.le,
      ⟨selected.2.2.2.1.le, selected.2.2.2.2.2.1.le⟩⟩⟩

/-- Every original-family signed convex subwindow is an ACTUAL bounded
finite-volume Jordan body: its Lebesgue boundary has measure zero. -/
theorem adaptiveMixedSignedOriginalConvexDomain_geometry
    (support : Finset ℕ) (base : ℕ) (domain : Set (ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (physical : domain ⊆ adaptiveMixedSignedOriginalPhysicalDomain support base) :
    IsBounded domain ∧ volume domain < ⊤ ∧ volume (frontier domain) = 0 := by
  have bounded :=
    (adaptiveMixedSignedOriginalPhysicalDomain_isBounded
      support base primes).subset physical
  exact ⟨bounded, bounded.measure_lt_top,
    convex.addHaar_frontier volume⟩

/-- Every original signed OPEN nonempty convex cell has a strictly positive,
finite REAL volume; neither zero-volume nor infinite-volume cells are being
fed into the prime-pattern asymptotic. -/
theorem adaptiveMixedSignedOriginalConvexDomain_volume_toReal_pos
    (support : Finset ℕ) (base : ℕ) (domain : Set (ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆ adaptiveMixedSignedOriginalPhysicalDomain support base) :
    0 < (volume domain).toReal := by
  obtain ⟨_bounded, finite, _null_boundary⟩ :=
    adaptiveMixedSignedOriginalConvexDomain_geometry
      support base domain primes convex physical
  exact ENNReal.toReal_pos
    (open_domain.measure_pos volume nonempty).ne' finite.ne

/-- Every actual common-label signed convex subwindow is bounded, has finite
Lebesgue measure, and has measure-zero boundary. -/
theorem adaptiveMixedSignedSharedLabelConvexDomain_geometry
    (support : Finset ℕ) (firstBase secondBase : ℕ)
    (domain : Set (ℝ × ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (physical : domain ⊆
      adaptiveMixedSignedSharedLabelPhysicalDomain
        support firstBase secondBase) :
    IsBounded domain ∧ volume domain < ⊤ ∧ volume (frontier domain) = 0 := by
  have bounded :=
    (adaptiveMixedSignedSharedLabelPhysicalDomain_isBounded
      support firstBase secondBase primes).subset physical
  exact ⟨bounded, bounded.measure_lt_top,
    convex.addHaar_frontier volume⟩

/-- Every actual common-label open nonempty signed convex subwindow has
strictly positive finite real volume. -/
theorem adaptiveMixedSignedSharedLabelConvexDomain_volume_toReal_pos
    (support : Finset ℕ) (firstBase secondBase : ℕ)
    (domain : Set (ℝ × ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆
      adaptiveMixedSignedSharedLabelPhysicalDomain
        support firstBase secondBase) :
    0 < (volume domain).toReal := by
  obtain ⟨_bounded, finite, _null_boundary⟩ :=
    adaptiveMixedSignedSharedLabelConvexDomain_geometry
      support firstBase secondBase domain primes convex physical
  exact ENNReal.toReal_pos
    (open_domain.measure_pos volume nonempty).ne' finite.ne

/-- Every actual shared-target signed convex subwindow has all standard
bounded-body and null-boundary hypotheses of the affine prime theorem. -/
theorem adaptiveMixedSignedSharedTargetConvexDomain_geometry
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ)
    (domain : Set (ℝ × ℝ × ℝ))
    (convex : Convex ℝ domain)
    (physical : domain ⊆
      adaptiveMixedSharedTargetPhysicalConvexWindow
        firstIndex secondIndex targetLower targetUpper
          firstLabelLower firstLabelUpper
          secondLabelLower secondLabelUpper) :
    IsBounded domain ∧ volume domain < ⊤ ∧ volume (frontier domain) = 0 := by
  have bounded :=
    (adaptiveMixedSharedTargetPhysicalConvexWindow_isBounded
      firstIndex secondIndex targetLower targetUpper
        firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper).subset physical
  exact ⟨bounded, bounded.measure_lt_top,
    convex.addHaar_frontier volume⟩

/-- Every actual shared-target OPEN nonempty signed convex subwindow has
strictly positive finite real three-dimensional volume. -/
theorem adaptiveMixedSignedSharedTargetConvexDomain_volume_toReal_pos
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ)
    (domain : Set (ℝ × ℝ × ℝ))
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆
      adaptiveMixedSharedTargetPhysicalConvexWindow
        firstIndex secondIndex targetLower targetUpper
          firstLabelLower firstLabelUpper
          secondLabelLower secondLabelUpper) :
    0 < (volume domain).toReal := by
  obtain ⟨_bounded, finite, _null_boundary⟩ :=
    adaptiveMixedSignedSharedTargetConvexDomain_geometry
      firstIndex secondIndex targetLower targetUpper
        firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper domain convex physical
  exact ENNReal.toReal_pos
    (open_domain.measure_pos volume nonempty).ne' finite.ne


end Erdos1139
