module

public import AdaptiveMixedPairedPrimePowerFibers1139

@[expose] public section


/-!
# Proper-prime-power fibers on the genuine shared-target lattice

The actual shared-target lattice consists of TWO prime labels and TWO signed
centers subject to ONE exact physical-target equation.  Its dimension is
three.  The duplicated distinguished target is counted once in the genuine
form index set, but the two prime labels remain separate forms.

This file proves `O(N²)` fibers DIRECTLY on the entire actual integral
shared-target lattice.  Direct injectivity avoids replacing it by an
unjustified rectangular or positive-center box.  It applies to every
additional physical-domain or lattice restriction.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- At fixed genuine label, the actual physical target is injective in its
SIGNED center because its true squared support modulus is positive. -/
theorem adaptiveMixedSignedSharedTargetPhysicalOffset_center_injective
    (support : Finset ℕ) (primes : ∀ prime ∈ support, prime.Prime)
    (base index label : ℕ) (firstCenter secondCenter : ℤ)
    (same :
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support base index label firstCenter =
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support base index label secondCenter) :
    firstCenter = secondCenter := by
  have modulus_nonzero : (adaptiveMixedTypeModulus support : ℤ) ≠ 0 := by
    exact_mod_cast (adaptiveMixedTypeModulus_pos support primes).ne'
  unfold adaptiveMixedSignedSharedTargetPhysicalOffset
    weightedPrimePatternSignedResidue at same
  have multiples :
      (adaptiveMixedTypeModulus support : ℤ) * firstCenter =
        (adaptiveMixedTypeModulus support : ℤ) * secondCenter := by
    linear_combination same
  exact mul_left_cancel₀ modulus_nonzero multiples

/-- Natural evaluation of the source-faithful shared-target system: BOTH
genuine prime labels and all actual branch targets, with removal of the
repeated distinguished target delegated to the existing audited index set. -/
def adaptiveMixedSharedTargetSignedPrimeFormValue
    (support : Finset ℕ) (firstBase secondBase : ℕ) :
    Option ℕ ⊕ Option ℕ → ((ℕ × ℤ) × (ℕ × ℤ)) → ℕ
  | Sum.inl index, point =>
      adaptiveMixedActualSignedPrimeFormValue support firstBase index point.1
  | Sum.inr index, point =>
      adaptiveMixedActualSignedPrimeFormValue support secondBase index point.2

/-- EVERY actual full-lattice shared-target prime form has a positive-value
fiber of size at most the exact product of the TWO genuine signed-center
window sizes.  The result is on the ENTIRE integral target-equality lattice,
with globally equal labels allowed and arbitrary additional restrictions. -/
theorem adaptiveMixedSignedSharedTargetActualFormFiber_card_le_windows
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex N : ℕ)
    (points : Finset ((ℕ × ℤ) × (ℕ × ℤ)))
    (boxed : points ⊆
      ((Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow first.1 N)).product
      ((Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow second.1 N)))
    (shared : ∀ point ∈ points,
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support first.1 firstIndex point.1.1 point.1.2 =
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support second.1 secondIndex point.2.1 point.2.2)
    (primes : ∀ prime ∈ support, prime.Prime)
    (index : Option ℕ ⊕ Option ℕ)
    (selected : index ∈ adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex)
    (power : ℕ) (power_positive : 0 < power) :
    ((points.filter fun point =>
      adaptiveMixedSharedTargetSignedPrimeFormValue
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
  rw [← first_card, ← second_card]
  cases index with
  | inl branch =>
      cases branch with
      | none =>
          calc
            _ ≤ (firstCenters.product labels).card := by
              apply Finset.card_le_card_of_injOn
                (fun point : (ℕ × ℤ) × (ℕ × ℤ) =>
                  (point.1.2, point.2.1))
              · intro point membership
                have in_points :=
                  (Finset.mem_filter.mp (Finset.mem_coe.mp membership)).1
                have boxes := Finset.mem_product.mp (boxed in_points)
                exact Finset.mem_coe.mpr (Finset.mem_product.mpr
                  ⟨(Finset.mem_product.mp boxes.1).2,
                    (Finset.mem_product.mp boxes.2).1⟩)
              · intro left left_member right right_member same_projection
                change (left.1.2, left.2.1) =
                  (right.1.2, right.2.1) at same_projection
                have first_center : left.1.2 = right.1.2 :=
                  congrArg (fun pair : ℤ × ℕ => pair.1) same_projection
                have second_label : left.2.1 = right.2.1 :=
                  congrArg (fun pair : ℤ × ℕ => pair.2) same_projection
                obtain ⟨left_points, left_value⟩ :=
                  Finset.mem_filter.mp (Finset.mem_coe.mp left_member)
                obtain ⟨right_points, right_value⟩ :=
                  Finset.mem_filter.mp (Finset.mem_coe.mp right_member)
                have first_label : left.1.1 = right.1.1 :=
                  left_value.trans right_value.symm
                have first_pair : left.1 = right.1 :=
                  Prod.ext first_label first_center
                have same_second_target :
                    adaptiveMixedSignedSharedTargetPhysicalOffset
                      support second.1 secondIndex left.2.1 left.2.2 =
                    adaptiveMixedSignedSharedTargetPhysicalOffset
                      support second.1 secondIndex right.2.1 right.2.2 := by
                  calc
                    _ = adaptiveMixedSignedSharedTargetPhysicalOffset
                          support first.1 firstIndex left.1.1 left.1.2 :=
                        (shared left left_points).symm
                    _ = adaptiveMixedSignedSharedTargetPhysicalOffset
                          support first.1 firstIndex right.1.1 right.1.2 := by
                        rw [first_pair]
                    _ = _ := shared right right_points
                rw [second_label] at same_second_target
                have second_center :=
                  adaptiveMixedSignedSharedTargetPhysicalOffset_center_injective
                    support primes second.1 secondIndex right.2.1
                      left.2.2 right.2.2 same_second_target
                exact Prod.ext first_pair (Prod.ext second_label second_center)
            _ = firstCenters.card * labels.card := Finset.card_product _ _
            _ ≤ firstCenters.card * secondCenters.card :=
              Nat.mul_le_mul_left firstCenters.card labels_le_second
      | some physical =>
          have actual :=
            (adaptiveMixedSharedTargetFormIndices_inl_mem_iff
              support scale first second secondIndex (some physical)).mp selected
          have active :=
            (adaptiveMixedActualFormIndices_target_mem_iff
              support scale physical first).mp actual
          have center_nonzero :
              (adaptiveMixedActualCenterCoefficient
                support first.1 physical : ℤ) ≠ 0 := by
            exact_mod_cast
              (adaptiveMixedActualCenterCoefficient_pos primes active).ne'
          calc
            _ ≤ (labels.product labels).card := by
              apply Finset.card_le_card_of_injOn
                (fun point : (ℕ × ℤ) × (ℕ × ℤ) =>
                  (point.1.1, point.2.1))
              · intro point membership
                have in_points :=
                  (Finset.mem_filter.mp (Finset.mem_coe.mp membership)).1
                have boxes := Finset.mem_product.mp (boxed in_points)
                exact Finset.mem_coe.mpr (Finset.mem_product.mpr
                  ⟨(Finset.mem_product.mp boxes.1).1,
                    (Finset.mem_product.mp boxes.2).1⟩)
              · intro left left_member right right_member same_projection
                change (left.1.1, left.2.1) =
                  (right.1.1, right.2.1) at same_projection
                have first_label : left.1.1 = right.1.1 :=
                  congrArg (fun pair : ℕ × ℕ => pair.1) same_projection
                have second_label : left.2.1 = right.2.1 :=
                  congrArg (fun pair : ℕ × ℕ => pair.2) same_projection
                obtain ⟨left_points, left_value⟩ :=
                  Finset.mem_filter.mp (Finset.mem_coe.mp left_member)
                obtain ⟨right_points, right_value⟩ :=
                  Finset.mem_filter.mp (Finset.mem_coe.mp right_member)
                have first_center :=
                  adaptiveMixedSignedAffinePositiveFiber_center_eq
                    (adaptiveMixedActualLabelCoefficient
                      support first.1 physical : ℤ)
                    (adaptiveMixedActualCenterCoefficient
                      support first.1 physical : ℤ)
                    center_nonzero power power_positive left.1 right.1
                      left_value right_value first_label
                have first_pair : left.1 = right.1 :=
                  Prod.ext first_label first_center
                have same_second_target :
                    adaptiveMixedSignedSharedTargetPhysicalOffset
                      support second.1 secondIndex left.2.1 left.2.2 =
                    adaptiveMixedSignedSharedTargetPhysicalOffset
                      support second.1 secondIndex right.2.1 right.2.2 := by
                  calc
                    _ = adaptiveMixedSignedSharedTargetPhysicalOffset
                          support first.1 firstIndex left.1.1 left.1.2 :=
                        (shared left left_points).symm
                    _ = adaptiveMixedSignedSharedTargetPhysicalOffset
                          support first.1 firstIndex right.1.1 right.1.2 := by
                        rw [first_pair]
                    _ = _ := shared right right_points
                rw [second_label] at same_second_target
                have second_center :=
                  adaptiveMixedSignedSharedTargetPhysicalOffset_center_injective
                    support primes second.1 secondIndex right.2.1
                      left.2.2 right.2.2 same_second_target
                exact Prod.ext first_pair (Prod.ext second_label second_center)
            _ = labels.card * labels.card := Finset.card_product _ _
            _ ≤ firstCenters.card * secondCenters.card :=
              Nat.mul_le_mul labels_le_first labels_le_second
  | inr branch =>
      have actual :=
        (adaptiveMixedSharedTargetFormIndices_inr_mem_iff
          support scale first second secondIndex branch).mp selected
      cases branch with
      | none =>
          calc
            _ ≤ (labels.product secondCenters).card := by
              apply Finset.card_le_card_of_injOn
                (fun point : (ℕ × ℤ) × (ℕ × ℤ) =>
                  (point.1.1, point.2.2))
              · intro point membership
                have in_points :=
                  (Finset.mem_filter.mp (Finset.mem_coe.mp membership)).1
                have boxes := Finset.mem_product.mp (boxed in_points)
                exact Finset.mem_coe.mpr (Finset.mem_product.mpr
                  ⟨(Finset.mem_product.mp boxes.1).1,
                    (Finset.mem_product.mp boxes.2).2⟩)
              · intro left left_member right right_member same_projection
                change (left.1.1, left.2.2) =
                  (right.1.1, right.2.2) at same_projection
                have first_label : left.1.1 = right.1.1 := by
                  have projected :=
                    congrArg (fun pair : ℕ × ℤ => pair.1) same_projection
                  exact projected
                have second_center : left.2.2 = right.2.2 := by
                  have projected :=
                    congrArg (fun pair : ℕ × ℤ => pair.2) same_projection
                  exact projected
                obtain ⟨left_points, left_value⟩ :=
                  Finset.mem_filter.mp (Finset.mem_coe.mp left_member)
                obtain ⟨right_points, right_value⟩ :=
                  Finset.mem_filter.mp (Finset.mem_coe.mp right_member)
                have second_label : left.2.1 = right.2.1 :=
                  left_value.trans right_value.symm
                have second_pair : left.2 = right.2 :=
                  Prod.ext second_label second_center
                have same_first_target :
                    adaptiveMixedSignedSharedTargetPhysicalOffset
                      support first.1 firstIndex left.1.1 left.1.2 =
                    adaptiveMixedSignedSharedTargetPhysicalOffset
                      support first.1 firstIndex right.1.1 right.1.2 := by
                  calc
                    _ = adaptiveMixedSignedSharedTargetPhysicalOffset
                          support second.1 secondIndex left.2.1 left.2.2 :=
                        shared left left_points
                    _ = adaptiveMixedSignedSharedTargetPhysicalOffset
                          support second.1 secondIndex right.2.1 right.2.2 := by
                        rw [second_pair]
                    _ = _ := (shared right right_points).symm
                rw [first_label] at same_first_target
                have first_center :=
                  adaptiveMixedSignedSharedTargetPhysicalOffset_center_injective
                    support primes first.1 firstIndex right.1.1
                      left.1.2 right.1.2 same_first_target
                exact Prod.ext (Prod.ext first_label first_center) second_pair
            _ = labels.card * secondCenters.card := Finset.card_product _ _
            _ ≤ firstCenters.card * secondCenters.card :=
              Nat.mul_le_mul_right secondCenters.card labels_le_first
      | some physical =>
          have active :=
            (adaptiveMixedActualFormIndices_target_mem_iff
              support scale physical second).mp actual.2
          have center_nonzero :
              (adaptiveMixedActualCenterCoefficient
                support second.1 physical : ℤ) ≠ 0 := by
            exact_mod_cast
              (adaptiveMixedActualCenterCoefficient_pos primes active).ne'
          calc
            _ ≤ (labels.product labels).card := by
              apply Finset.card_le_card_of_injOn
                (fun point : (ℕ × ℤ) × (ℕ × ℤ) =>
                  (point.1.1, point.2.1))
              · intro point membership
                have in_points :=
                  (Finset.mem_filter.mp (Finset.mem_coe.mp membership)).1
                have boxes := Finset.mem_product.mp (boxed in_points)
                exact Finset.mem_coe.mpr (Finset.mem_product.mpr
                  ⟨(Finset.mem_product.mp boxes.1).1,
                    (Finset.mem_product.mp boxes.2).1⟩)
              · intro left left_member right right_member same_projection
                change (left.1.1, left.2.1) =
                  (right.1.1, right.2.1) at same_projection
                have first_label : left.1.1 = right.1.1 :=
                  congrArg (fun pair : ℕ × ℕ => pair.1) same_projection
                have second_label : left.2.1 = right.2.1 :=
                  congrArg (fun pair : ℕ × ℕ => pair.2) same_projection
                obtain ⟨left_points, left_value⟩ :=
                  Finset.mem_filter.mp (Finset.mem_coe.mp left_member)
                obtain ⟨right_points, right_value⟩ :=
                  Finset.mem_filter.mp (Finset.mem_coe.mp right_member)
                have second_center :=
                  adaptiveMixedSignedAffinePositiveFiber_center_eq
                    (adaptiveMixedActualLabelCoefficient
                      support second.1 physical : ℤ)
                    (adaptiveMixedActualCenterCoefficient
                      support second.1 physical : ℤ)
                    center_nonzero power power_positive left.2 right.2
                      left_value right_value second_label
                have second_pair : left.2 = right.2 :=
                  Prod.ext second_label second_center
                have same_first_target :
                    adaptiveMixedSignedSharedTargetPhysicalOffset
                      support first.1 firstIndex left.1.1 left.1.2 =
                    adaptiveMixedSignedSharedTargetPhysicalOffset
                      support first.1 firstIndex right.1.1 right.1.2 := by
                  calc
                    _ = adaptiveMixedSignedSharedTargetPhysicalOffset
                          support second.1 secondIndex left.2.1 left.2.2 :=
                        shared left left_points
                    _ = adaptiveMixedSignedSharedTargetPhysicalOffset
                          support second.1 secondIndex right.2.1 right.2.2 := by
                        rw [second_pair]
                    _ = _ := (shared right right_points).symm
                rw [first_label] at same_first_target
                have first_center :=
                  adaptiveMixedSignedSharedTargetPhysicalOffset_center_injective
                    support primes first.1 firstIndex right.1.1
                      left.1.2 right.1.2 same_first_target
                exact Prod.ext (Prod.ext first_label first_center) second_pair
            _ = labels.card * labels.card := Finset.card_product _ _
            _ ≤ firstCenters.card * secondCenters.card :=
              Nat.mul_le_mul labels_le_first labels_le_second

/-- Actual full-lattice shared-target proper-prime-power cardinality bound.
The exact rank counts BOTH prime labels and counts the shared distinguished
target ONCE; no individual affine-fiber hypothesis is assumed. -/
theorem adaptiveMixedSignedSharedTargetPrimePowerExceptions_card_le
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex N cutoff : ℕ)
    (points : Finset ((ℕ × ℤ) × (ℕ × ℤ)))
    (boxed : points ⊆
      ((Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow first.1 N)).product
      ((Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow second.1 N)))
    (shared : ∀ point ∈ points,
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support first.1 firstIndex point.1.1 point.1.2 =
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support second.1 secondIndex point.2.1 point.2.2)
    (primes : ∀ prime ∈ support, prime.Prime)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (bounded : ∀ point ∈ points,
      ∀ index ∈ adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex,
          adaptiveMixedSharedTargetSignedPrimeFormValue
            support first.1 second.1 index point ∈ Finset.Ioc 0 cutoff) :
    (adaptiveMixedVonMangoldtPrimePowerExceptions points
      (adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex)
      (adaptiveMixedSharedTargetSignedPrimeFormValue
        support first.1 second.1)).card ≤
        ((adaptiveMixedOutcomeActiveIndices support scale first).card +
          (adaptiveMixedOutcomeActiveIndices support scale second).card + 1) *
          (Erdos689.ternaryProperPrimePowers cutoff).card *
            ((2 * (first.1 + 1) * N + 1) *
              (2 * (second.1 + 1) * N + 1)) := by
  rw [← adaptiveMixedSharedTargetFormIndices_card second_active]
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_card_le
    points (adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex)
      (adaptiveMixedSharedTargetSignedPrimeFormValue support first.1 second.1)
        cutoff ((2 * (first.1 + 1) * N + 1) *
          (2 * (second.1 + 1) * N + 1)) bounded
  intro index selected power selected_power
  have power_positive :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
  exact adaptiveMixedSignedSharedTargetActualFormFiber_card_le_windows
    support scale first second firstIndex secondIndex N points boxed shared primes
      index selected power power_positive

/-- Actual full-lattice shared-target arbitrary-rank von Mangoldt proper-
prime-power error.  The three-dimensional geometry, both signed centers,
both labels, exact target equality, and deduplicated shared target are all
retained; every required quadratic fiber bound has been proved. -/
theorem adaptiveMixedSignedSharedTargetPrimePowerExceptions_weight_le
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex N cutoff : ℕ)
    (points : Finset ((ℕ × ℤ) × (ℕ × ℤ)))
    (boxed : points ⊆
      ((Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow first.1 N)).product
      ((Finset.Ioc N (2 * N)).product
        (adaptiveMixedSignedSearchCenterWindow second.1 N)))
    (shared : ∀ point ∈ points,
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support first.1 firstIndex point.1.1 point.1.2 =
      adaptiveMixedSignedSharedTargetPhysicalOffset
        support second.1 secondIndex point.2.1 point.2.2)
    (primes : ∀ prime ∈ support, prime.Prime)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (bounded : ∀ point ∈ points,
      ∀ index ∈ adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex,
          adaptiveMixedSharedTargetSignedPrimeFormValue
            support first.1 second.1 index point ∈ Finset.Ioc 0 cutoff) :
    (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions points
      (adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex)
      (adaptiveMixedSharedTargetSignedPrimeFormValue
        support first.1 second.1),
        adaptiveMixedVonMangoldtProduct
          (adaptiveMixedSharedTargetFormIndices
            support scale first second secondIndex)
          (adaptiveMixedSharedTargetSignedPrimeFormValue
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
  rw [← adaptiveMixedSharedTargetFormIndices_card second_active]
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_weight_le
    points (adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex)
      (adaptiveMixedSharedTargetSignedPrimeFormValue support first.1 second.1)
        cutoff ((2 * (first.1 + 1) * N + 1) *
          (2 * (second.1 + 1) * N + 1)) bounded
  intro index selected power selected_power
  have power_positive :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
  exact adaptiveMixedSignedSharedTargetActualFormFiber_card_le_windows
    support scale first second firstIndex secondIndex N points boxed shared primes
      index selected power power_positive

end Erdos1139

