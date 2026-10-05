module

public import AdaptiveMixedPrimePowerNegligible1139

@[expose] public section


/-!
# Actual signed affine prime-power fibers for Erdős #1139

The arbitrary-rank prime-power-removal theorem requires an individual
`O(N^(dimension-1))` fiber bound.  This module supplies those bounds in the
ACTUAL signed physical coordinates, retaining the genuine prime-label form,
every retained mixed target, and their true positive center coefficients.

No natural-center substitution, fixed-rank-three assumption, prime-pattern
asymptotic, or nonstandard axiom is used.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- Exact natural evaluation of every actual original-system prime form.
`none` is the indispensable genuine prime label; `some index` is the true
SIGNED integer mixed affine target at its actual physical index. -/
def adaptiveMixedActualSignedPrimeFormValue
    (support : Finset ℕ) (base : ℕ) :
    Option ℕ → (ℕ × ℤ) → ℕ
  | none, point => point.1
  | some index, point =>
      (weightedPrimePatternIntegerForm
        support base index point.1 point.2).toNat

/-- A positive-value fiber of a nonconstant signed affine target has at most
one center for each natural label.  Positivity is essential: integer `toNat`
collapses EVERY nonpositive integer to zero. -/
theorem adaptiveMixedSignedAffinePositiveFiber_card_le_labels
    (labels : Finset ℕ) (centers : Finset ℤ)
    (labelCoefficient centerCoefficient : ℤ)
    (center_nonzero : centerCoefficient ≠ 0)
    (power : ℕ) (power_positive : 0 < power) :
    (((labels.product centers).filter fun point =>
      (labelCoefficient * (point.1 : ℤ) +
        centerCoefficient * point.2).toNat = power).card ≤ labels.card) := by
  classical
  apply Finset.card_le_card_of_injOn (fun point : ℕ × ℤ => point.1)
  · intro point selected
    have membership := Finset.mem_filter.mp (Finset.mem_coe.mp selected)
    exact Finset.mem_coe.mpr (Finset.mem_product.mp membership.1).1
  · intro first first_selected second second_selected same_label
    change first.1 = second.1 at same_label
    obtain ⟨_, first_value⟩ :=
      Finset.mem_filter.mp (Finset.mem_coe.mp first_selected)
    obtain ⟨_, second_value⟩ :=
      Finset.mem_filter.mp (Finset.mem_coe.mp second_selected)
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
    have same_natural := first_value.trans second_value.symm
    have same_integer :=
      congrArg (fun value : ℕ => (value : ℤ)) same_natural
    rw [Int.toNat_of_nonneg first_positive.le,
      Int.toNat_of_nonneg second_positive.le] at same_integer
    rw [same_label] at same_integer
    have same_center_multiple := add_left_cancel same_integer
    exact Prod.ext same_label
      (mul_left_cancel₀ center_nonzero same_center_multiple)

/-- The genuine prime-label fiber has at most one label for each signed
center, with no positivity hypothesis needed. -/
theorem adaptiveMixedSignedLabelFiber_card_le_centers
    (labels : Finset ℕ) (centers : Finset ℤ) (power : ℕ) :
    (((labels.product centers).filter
      fun point => point.1 = power).card ≤ centers.card) := by
  classical
  apply Finset.card_le_card_of_injOn (fun point : ℕ × ℤ => point.2)
  · intro point selected
    have membership := Finset.mem_filter.mp (Finset.mem_coe.mp selected)
    exact Finset.mem_coe.mpr (Finset.mem_product.mp membership.1).2
  · intro first first_selected second second_selected same_center
    have first_value :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp first_selected)).2
    have second_value :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp second_selected)).2
    exact Prod.ext (first_value.trans second_value.symm) same_center

/-- EVERY actual retained signed original-system form has at most the exact
signed-center-window cardinality in any positive-value fiber.  Arbitrary
physical-domain, lattice, and residue restrictions may shrink the box. -/
theorem adaptiveMixedSignedOriginalActualFormFiber_card_le_window
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) (N : ℕ)
    (points : Finset (ℕ × ℤ))
    (boxed : points ⊆ (Finset.Ioc N (2 * N)).product
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N))
    (primes : ∀ prime ∈ support, prime.Prime)
    (index : Option ℕ)
    (selected : index ∈ adaptiveMixedActualFormIndices support scale outcome)
    (power : ℕ) (power_positive : 0 < power) :
    ((points.filter fun point =>
      adaptiveMixedActualSignedPrimeFormValue
        support outcome.1 index point = power).card ≤
      2 * (outcome.1 + 1) * N + 1) := by
  classical
  let labels := Finset.Ioc N (2 * N)
  let centers := adaptiveMixedSignedSearchCenterWindow outcome.1 N
  have labels_card : labels.card = N := by
    dsimp [labels]
    rw [Nat.card_Ioc]
    omega
  have centers_card : centers.card = 2 * (outcome.1 + 1) * N + 1 :=
    adaptiveMixedSignedSearchCenterWindow_card outcome.1 N
  have labels_le_centers : labels.card ≤ centers.card := by
    rw [labels_card, centers_card]
    exact (Nat.le_mul_of_pos_left N (by positivity : 0 < 2 * (outcome.1 + 1))).trans
      (Nat.le_add_right _ _)
  have filtered_subset :
      (points.filter fun point =>
        adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point = power) ⊆
        ((labels.product centers).filter fun point =>
          adaptiveMixedActualSignedPrimeFormValue
            support outcome.1 index point = power) := by
    intro point membership
    obtain ⟨in_points, fiber⟩ := Finset.mem_filter.mp membership
    exact Finset.mem_filter.mpr ⟨boxed in_points, fiber⟩
  rw [← centers_card]
  refine (Finset.card_le_card filtered_subset).trans ?_
  cases index with
  | none =>
      exact adaptiveMixedSignedLabelFiber_card_le_centers labels centers power
  | some physical =>
      have active :
          physical ∈ adaptiveMixedOutcomeActiveIndices support scale outcome :=
        (adaptiveMixedActualFormIndices_target_mem_iff
          support scale physical outcome).mp selected
      have center_positive :=
        adaptiveMixedActualCenterCoefficient_pos primes active
      have center_nonzero :
          (adaptiveMixedActualCenterCoefficient
            support outcome.1 physical : ℤ) ≠ 0 := by
        exact_mod_cast center_positive.ne'
      have fiber_bound :=
        adaptiveMixedSignedAffinePositiveFiber_card_le_labels labels centers
          (adaptiveMixedActualLabelCoefficient
            support outcome.1 physical : ℤ)
          (adaptiveMixedActualCenterCoefficient
            support outcome.1 physical : ℤ)
          center_nonzero power power_positive
      exact fiber_bound.trans labels_le_centers

/-- Source-faithful finite arbitrary-rank proper-prime-power cardinality
bound for the ACTUAL signed original system and arbitrary physical-domain
subsets of its genuine dyadic-label/signed-center box. -/
theorem adaptiveMixedSignedOriginalPrimePowerExceptions_card_le
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (N cutoff : ℕ) (points : Finset (ℕ × ℤ))
    (boxed : points ⊆ (Finset.Ioc N (2 * N)).product
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N))
    (primes : ∀ prime ∈ support, prime.Prime)
    (bounded : ∀ point ∈ points,
      ∀ index ∈ adaptiveMixedActualFormIndices support scale outcome,
        adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point ∈ Finset.Ioc 0 cutoff) :
    (adaptiveMixedVonMangoldtPrimePowerExceptions points
      (adaptiveMixedActualFormIndices support scale outcome)
      (adaptiveMixedActualSignedPrimeFormValue support outcome.1)).card ≤
        ((adaptiveMixedOutcomeActiveIndices
          support scale outcome).card + 1) *
          (Erdos689.ternaryProperPrimePowers cutoff).card *
            (2 * (outcome.1 + 1) * N + 1) := by
  rw [← adaptiveMixedActualFormIndices_card]
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_card_le
    points (adaptiveMixedActualFormIndices support scale outcome)
      (adaptiveMixedActualSignedPrimeFormValue support outcome.1)
        cutoff (2 * (outcome.1 + 1) * N + 1) bounded
  intro index selected power selected_power
  have power_positive :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
  exact adaptiveMixedSignedOriginalActualFormFiber_card_le_window
    support scale outcome N points boxed primes index selected power power_positive

/-- Corresponding ACTUAL signed-original arbitrary-rank von Mangoldt error,
with NO assumed affine-fiber condition left to prove.  Both the exact signed
window and the genuine `active.card + 1` form rank are retained. -/
theorem adaptiveMixedSignedOriginalPrimePowerExceptions_weight_le
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (N cutoff : ℕ) (points : Finset (ℕ × ℤ))
    (boxed : points ⊆ (Finset.Ioc N (2 * N)).product
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N))
    (primes : ∀ prime ∈ support, prime.Prime)
    (bounded : ∀ point ∈ points,
      ∀ index ∈ adaptiveMixedActualFormIndices support scale outcome,
        adaptiveMixedActualSignedPrimeFormValue
          support outcome.1 index point ∈ Finset.Ioc 0 cutoff) :
    (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions points
      (adaptiveMixedActualFormIndices support scale outcome)
      (adaptiveMixedActualSignedPrimeFormValue support outcome.1),
        adaptiveMixedVonMangoldtProduct
          (adaptiveMixedActualFormIndices support scale outcome)
          (adaptiveMixedActualSignedPrimeFormValue support outcome.1) point) ≤
      (((adaptiveMixedOutcomeActiveIndices
          support scale outcome).card + 1 : ℕ) : ℝ) *
        (2 * (outcome.1 + 1) * N + 1 : ℕ) *
          (Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1) *
            Real.log (cutoff : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) := by
  rw [← adaptiveMixedActualFormIndices_card]
  apply adaptiveMixedVonMangoldtPrimePowerExceptions_weight_le
    points (adaptiveMixedActualFormIndices support scale outcome)
      (adaptiveMixedActualSignedPrimeFormValue support outcome.1)
        cutoff (2 * (outcome.1 + 1) * N + 1) bounded
  intro index selected power selected_power
  have power_positive :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp selected_power).1).1
  exact adaptiveMixedSignedOriginalActualFormFiber_card_le_window
    support scale outcome N points boxed primes index selected power power_positive

end Erdos1139

