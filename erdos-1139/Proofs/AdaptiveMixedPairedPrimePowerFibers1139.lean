module

public import AdaptiveMixedAffinePrimePowerFibers1139

@[expose] public section


/-!
# Genuine three-dimensional mixed-pattern prime-power fibers

The shared-label and shared-target #1139 correlations have actual physical
dimension THREE, although each fixed mixed system can have arbitrarily many
prime forms.  Proper-prime-power removal therefore requires every individual
true signed affine fiber to have size `O(N²)`.

This module retains the actual dyadic label, both signed centers, and the
deduplicated source-faithful shared-label prime-form index set.  It proves
explicit finite fiber bounds on arbitrary restricted physical subsets.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- Equality of a positive natural signed-affine value and its label
determines the signed center whenever its true coefficient is nonzero. -/
theorem adaptiveMixedSignedAffinePositiveFiber_center_eq
    (labelCoefficient centerCoefficient : ℤ)
    (center_nonzero : centerCoefficient ≠ 0)
    (power : ℕ) (power_positive : 0 < power)
    (first second : ℕ × ℤ)
    (first_value :
      (labelCoefficient * (first.1 : ℤ) +
        centerCoefficient * first.2).toNat = power)
    (second_value :
      (labelCoefficient * (second.1 : ℤ) +
        centerCoefficient * second.2).toNat = power)
    (same_label : first.1 = second.1) :
    first.2 = second.2 := by
  have first_positive :
      0 < labelCoefficient * (first.1 : ℤ) +
        centerCoefficient * first.2 := by
    by_contra not_positive
    have zero := Int.toNat_eq_zero.mpr (le_of_not_gt not_positive)
    omega
  have second_positive :
      0 < labelCoefficient * (second.1 : ℤ) +
        centerCoefficient * second.2 := by
    by_contra not_positive
    have zero := Int.toNat_eq_zero.mpr (le_of_not_gt not_positive)
    omega
  have same_integer := congrArg (fun value : ℕ => (value : ℤ))
    (first_value.trans second_value.symm)
  rw [Int.toNat_of_nonneg first_positive.le,
    Int.toNat_of_nonneg second_positive.le, same_label] at same_integer
  exact mul_left_cancel₀ center_nonzero (add_left_cancel same_integer)

/-- Genuine three-coordinate prime-label fiber: fixing the single common
label leaves at most the product of BOTH signed-center window sizes. -/
theorem adaptiveMixedSignedSharedLabel_label_fiber_card_le
    (labels : Finset ℕ) (firstCenters secondCenters : Finset ℤ)
    (power : ℕ) :
    (((labels.product (firstCenters.product secondCenters)).filter
      fun point => point.1 = power).card ≤
        firstCenters.card * secondCenters.card) := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun point : ℕ × ℤ × ℤ => point.2)
  · intro point selected
    have membership := Finset.mem_filter.mp (Finset.mem_coe.mp selected)
    exact Finset.mem_coe.mpr (Finset.mem_product.mp membership.1).2
  · intro first first_selected second second_selected same_centers
    have first_value :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp first_selected)).2
    have second_value :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp second_selected)).2
    exact Prod.ext (first_value.trans second_value.symm) same_centers

/-- A first-branch genuine signed mixed target fiber leaves at most one first
center for each pair `(actual label, second signed center)`. -/
theorem adaptiveMixedSignedSharedLabel_first_target_fiber_card_le
    (labels : Finset ℕ) (firstCenters secondCenters : Finset ℤ)
    (labelCoefficient centerCoefficient : ℤ)
    (center_nonzero : centerCoefficient ≠ 0)
    (power : ℕ) (power_positive : 0 < power) :
    (((labels.product (firstCenters.product secondCenters)).filter
      fun point =>
        (labelCoefficient * (point.1 : ℤ) +
          centerCoefficient * point.2.1).toNat = power).card ≤
            labels.card * secondCenters.card) := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun point : ℕ × ℤ × ℤ => (point.1, point.2.2))
  · intro point selected
    have membership := Finset.mem_filter.mp (Finset.mem_coe.mp selected)
    have boxed := Finset.mem_product.mp membership.1
    exact Finset.mem_coe.mpr
      (Finset.mem_product.mpr
        ⟨boxed.1, (Finset.mem_product.mp boxed.2).2⟩)
  · intro first first_selected second second_selected same_projection
    change (first.1, first.2.2) = (second.1, second.2.2) at same_projection
    have same_label : first.1 = second.1 :=
      congrArg (fun pair : ℕ × ℤ => pair.1) same_projection
    have same_second : first.2.2 = second.2.2 :=
      congrArg (fun pair : ℕ × ℤ => pair.2) same_projection
    have first_value :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp first_selected)).2
    have second_value :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp second_selected)).2
    have same_first := adaptiveMixedSignedAffinePositiveFiber_center_eq
      labelCoefficient centerCoefficient center_nonzero power power_positive
        (first.1, first.2.1) (second.1, second.2.1)
          first_value second_value same_label
    exact Prod.ext same_label (Prod.ext same_first same_second)

/-- A second-branch genuine signed mixed target fiber leaves at most one
second center for each pair `(actual label, first signed center)`. -/
theorem adaptiveMixedSignedSharedLabel_second_target_fiber_card_le
    (labels : Finset ℕ) (firstCenters secondCenters : Finset ℤ)
    (labelCoefficient centerCoefficient : ℤ)
    (center_nonzero : centerCoefficient ≠ 0)
    (power : ℕ) (power_positive : 0 < power) :
    (((labels.product (firstCenters.product secondCenters)).filter
      fun point =>
        (labelCoefficient * (point.1 : ℤ) +
          centerCoefficient * point.2.2).toNat = power).card ≤
            labels.card * firstCenters.card) := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun point : ℕ × ℤ × ℤ => (point.1, point.2.1))
  · intro point selected
    have membership := Finset.mem_filter.mp (Finset.mem_coe.mp selected)
    have boxed := Finset.mem_product.mp membership.1
    exact Finset.mem_coe.mpr
      (Finset.mem_product.mpr
        ⟨boxed.1, (Finset.mem_product.mp boxed.2).1⟩)
  · intro first first_selected second second_selected same_projection
    change (first.1, first.2.1) = (second.1, second.2.1) at same_projection
    have same_label : first.1 = second.1 :=
      congrArg (fun pair : ℕ × ℤ => pair.1) same_projection
    have same_first : first.2.1 = second.2.1 :=
      congrArg (fun pair : ℕ × ℤ => pair.2) same_projection
    have first_value :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp first_selected)).2
    have second_value :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp second_selected)).2
    have same_second := adaptiveMixedSignedAffinePositiveFiber_center_eq
      labelCoefficient centerCoefficient center_nonzero power power_positive
        (first.1, first.2.2) (second.1, second.2.2)
          first_value second_value same_label
    exact Prod.ext same_label (Prod.ext same_first same_second)

/-- Natural evaluation of the EXACT deduplicated shared-label system: one
genuine prime label, every first physical target, and every second physical
target, using TWO genuinely signed center coordinates. -/
def adaptiveMixedSharedLabelSignedPrimeFormValue
    (support : Finset ℕ) (firstBase secondBase : ℕ) :
    Option ℕ ⊕ ℕ → (ℕ × ℤ × ℤ) → ℕ
  | Sum.inl none, point => point.1
  | Sum.inl (some index), point =>
      (weightedPrimePatternIntegerForm
        support firstBase index point.1 point.2.1).toNat
  | Sum.inr index, point =>
      (weightedPrimePatternIntegerForm
        support secondBase index point.1 point.2.2).toNat

/-- EVERY actual deduplicated shared-label prime form has a positive-value
fiber bounded by the EXACT product of the two genuine signed-window sizes.
The point set may have arbitrary physical-domain/residue restrictions. -/
theorem adaptiveMixedSignedSharedLabelActualFormFiber_card_le_windows
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ) (N : ℕ)
    (points : Finset (ℕ × ℤ × ℤ))
    (boxed : points ⊆ (Finset.Ioc N (2 * N)).product
      ((adaptiveMixedSignedSearchCenterWindow first.1 N).product
        (adaptiveMixedSignedSearchCenterWindow second.1 N)))
    (primes : ∀ prime ∈ support, prime.Prime)
    (index : Option ℕ ⊕ ℕ)
    (selected : index ∈ adaptiveMixedSharedLabelFormIndices
      support scale first second)
    (power : ℕ) (power_positive : 0 < power) :
    ((points.filter fun point =>
      adaptiveMixedSharedLabelSignedPrimeFormValue
        support first.1 second.1 index point = power).card ≤
      (2 * (first.1 + 1) * N + 1) *
        (2 * (second.1 + 1) * N + 1)) := by
  classical
  let labels := Finset.Ioc N (2 * N)
  let firstCenters := adaptiveMixedSignedSearchCenterWindow first.1 N
  let secondCenters := adaptiveMixedSignedSearchCenterWindow second.1 N
  have labels_card : labels.card = N := by
    dsimp [labels]
    rw [Nat.card_Ioc]
    omega
  have first_card : firstCenters.card = 2 * (first.1 + 1) * N + 1 :=
    adaptiveMixedSignedSearchCenterWindow_card first.1 N
  have second_card : secondCenters.card = 2 * (second.1 + 1) * N + 1 :=
    adaptiveMixedSignedSearchCenterWindow_card second.1 N
  have labels_le_first : labels.card ≤ firstCenters.card := by
    rw [labels_card, first_card]
    exact (Nat.le_mul_of_pos_left N (by positivity : 0 < 2 * (first.1 + 1))).trans
      (Nat.le_add_right _ _)
  have labels_le_second : labels.card ≤ secondCenters.card := by
    rw [labels_card, second_card]
    exact (Nat.le_mul_of_pos_left N (by positivity : 0 < 2 * (second.1 + 1))).trans
      (Nat.le_add_right _ _)
  have filtered_subset :
      (points.filter fun point =>
        adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1 index point = power) ⊆
      ((labels.product (firstCenters.product secondCenters)).filter
        fun point => adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1 index point = power) := by
    intro point membership
    obtain ⟨in_points, fiber⟩ := Finset.mem_filter.mp membership
    exact Finset.mem_filter.mpr ⟨boxed in_points, fiber⟩
  rw [← first_card, ← second_card]
  refine (Finset.card_le_card filtered_subset).trans ?_
  cases index with
  | inl branch =>
      cases branch with
      | none =>
          exact adaptiveMixedSignedSharedLabel_label_fiber_card_le
            labels firstCenters secondCenters power
      | some physical =>
          have actual :=
            (adaptiveMixedSharedLabelFormIndices_inl_mem_iff
              support scale first second (some physical)).mp selected
          have active :=
            (adaptiveMixedActualFormIndices_target_mem_iff
              support scale physical first).mp actual
          have center_nonzero :
              (adaptiveMixedActualCenterCoefficient
                support first.1 physical : ℤ) ≠ 0 := by
            exact_mod_cast
              (adaptiveMixedActualCenterCoefficient_pos primes active).ne'
          have fiber := adaptiveMixedSignedSharedLabel_first_target_fiber_card_le
            labels firstCenters secondCenters
            (adaptiveMixedActualLabelCoefficient support first.1 physical : ℤ)
            (adaptiveMixedActualCenterCoefficient support first.1 physical : ℤ)
            center_nonzero power power_positive
          exact fiber.trans
            (Nat.mul_le_mul_right secondCenters.card labels_le_first)
  | inr physical =>
      have active :=
        (adaptiveMixedSharedLabelFormIndices_inr_mem_iff
          support scale first second physical).mp selected
      have center_nonzero :
          (adaptiveMixedActualCenterCoefficient
            support second.1 physical : ℤ) ≠ 0 := by
        exact_mod_cast
          (adaptiveMixedActualCenterCoefficient_pos primes active).ne'
      have fiber := adaptiveMixedSignedSharedLabel_second_target_fiber_card_le
        labels firstCenters secondCenters
        (adaptiveMixedActualLabelCoefficient support second.1 physical : ℤ)
        (adaptiveMixedActualCenterCoefficient support second.1 physical : ℤ)
        center_nonzero power power_positive
      calc
        _ ≤ labels.card * firstCenters.card := fiber
        _ ≤ secondCenters.card * firstCenters.card :=
          Nat.mul_le_mul_right firstCenters.card labels_le_second
        _ = firstCenters.card * secondCenters.card := Nat.mul_comm _ _

/-- ACTUAL source-faithful arbitrary-rank shared-label proper-prime-power
cardinality bound, with the true combined form rank and both signed windows. -/
theorem adaptiveMixedSignedSharedLabelPrimePowerExceptions_card_le
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (N cutoff : ℕ) (points : Finset (ℕ × ℤ × ℤ))
    (boxed : points ⊆ (Finset.Ioc N (2 * N)).product
      ((adaptiveMixedSignedSearchCenterWindow first.1 N).product
        (adaptiveMixedSignedSearchCenterWindow second.1 N)))
    (primes : ∀ prime ∈ support, prime.Prime)
    (bounded : ∀ point ∈ points,
      ∀ index ∈ adaptiveMixedSharedLabelFormIndices support scale first second,
        adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1 index point ∈ Finset.Ioc 0 cutoff) :
    (adaptiveMixedVonMangoldtPrimePowerExceptions points
      (adaptiveMixedSharedLabelFormIndices support scale first second)
      (adaptiveMixedSharedLabelSignedPrimeFormValue
        support first.1 second.1)).card ≤
        ((adaptiveMixedOutcomeActiveIndices support scale first).card +
          (adaptiveMixedOutcomeActiveIndices support scale second).card + 1) *
          (Erdos689.ternaryProperPrimePowers cutoff).card *
            ((2 * (first.1 + 1) * N + 1) *
              (2 * (second.1 + 1) * N + 1)) := by
  rw [← adaptiveMixedSharedLabelFormIndices_card]
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_card_le
    points (adaptiveMixedSharedLabelFormIndices support scale first second)
      (adaptiveMixedSharedLabelSignedPrimeFormValue support first.1 second.1)
        cutoff ((2 * (first.1 + 1) * N + 1) *
          (2 * (second.1 + 1) * N + 1)) bounded
  intro index selected power selected_power
  have power_positive :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
  exact adaptiveMixedSignedSharedLabelActualFormFiber_card_le_windows
    support scale first second N points boxed primes
      index selected power power_positive

/-- ACTUAL source-faithful arbitrary-rank shared-label von Mangoldt proper-
prime-power error.  Every geometric fiber hypothesis has been proved for the
genuine signed three-dimensional box. -/
theorem adaptiveMixedSignedSharedLabelPrimePowerExceptions_weight_le
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (N cutoff : ℕ) (points : Finset (ℕ × ℤ × ℤ))
    (boxed : points ⊆ (Finset.Ioc N (2 * N)).product
      ((adaptiveMixedSignedSearchCenterWindow first.1 N).product
        (adaptiveMixedSignedSearchCenterWindow second.1 N)))
    (primes : ∀ prime ∈ support, prime.Prime)
    (bounded : ∀ point ∈ points,
      ∀ index ∈ adaptiveMixedSharedLabelFormIndices support scale first second,
        adaptiveMixedSharedLabelSignedPrimeFormValue
          support first.1 second.1 index point ∈ Finset.Ioc 0 cutoff) :
    (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions points
      (adaptiveMixedSharedLabelFormIndices support scale first second)
      (adaptiveMixedSharedLabelSignedPrimeFormValue support first.1 second.1),
        adaptiveMixedVonMangoldtProduct
          (adaptiveMixedSharedLabelFormIndices support scale first second)
          (adaptiveMixedSharedLabelSignedPrimeFormValue
            support first.1 second.1) point) ≤
      (((adaptiveMixedOutcomeActiveIndices support scale first).card +
          (adaptiveMixedOutcomeActiveIndices
            support scale second).card + 1 : ℕ) : ℝ) *
        ((2 * (first.1 + 1) * N + 1) *
          (2 * (second.1 + 1) * N + 1) : ℕ) *
          (Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1) *
            Real.log (cutoff : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices support scale first).card +
                (adaptiveMixedOutcomeActiveIndices
                  support scale second).card + 1) := by
  rw [← adaptiveMixedSharedLabelFormIndices_card]
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_weight_le
    points (adaptiveMixedSharedLabelFormIndices support scale first second)
      (adaptiveMixedSharedLabelSignedPrimeFormValue support first.1 second.1)
        cutoff ((2 * (first.1 + 1) * N + 1) *
          (2 * (second.1 + 1) * N + 1)) bounded
  intro index selected power selected_power
  have power_positive :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
  exact adaptiveMixedSignedSharedLabelActualFormFiber_card_le_windows
    support scale first second N points boxed primes
      index selected power power_positive

end Erdos1139

