module

public import AdaptiveSharedLabelFactorization1139

@[expose] public section


/-!
# Exact ACTUAL shared-target Bezout-fiber singular factorization

For two independently sampled same-support, same-type mixed outcomes, the
genuine three-coordinate shared-target selector lives on the integral fiber

    P' = cP + Bt,       C' = C-kP-a't,       a'c = a+Bk.

At EVERY prime, including primes dividing `B`, normalize the two complete
branches by their respective nonzero labels and keep their ONE common nonzero
distinguished prime target `q`:

    (P,C,t)  <->  (q, C/P, C'/P').

Every pair of genuinely admissible normalized centers has nonzero distinguished
values; it reconstructs `P=q/f_d(1,C/P)` and `P'=q/f_e(1,C'/P')`.  The true
integer Bezout certificate supplies existence AND uniqueness of the field
fiber parameter, even when `B=0` in that field.

Consequently the ACTUAL shared-target selector has exactly the already
audited shared-label cardinality and hence the exact collision-aware singular
product.  No covariance bound, analytic prime-count theorem, new axiom, or
solution of Erdős #1139 is claimed.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos1139

/-- The ACTUAL second prime label on the integral shared-target fiber. -/
def adaptiveMixedSharedTargetActualSecondLabel
    (support : Finset ℕ) (firstBase firstIndex ell : ℕ)
    (multiplier : ℤ) (firstLabel parameter : ZMod ell) : ZMod ell :=
  (multiplier : ZMod ell) * firstLabel +
    (adaptiveMixedActualCenterCoefficient
      support firstBase firstIndex : ZMod ell) * parameter

/-- The ACTUAL signed second center on the integral shared-target fiber. -/
def adaptiveMixedSharedTargetActualSecondCenter
    (support : Finset ℕ) (secondBase secondIndex ell : ℕ)
    (correction : ℤ) (firstLabel firstCenter parameter : ZMod ell) : ZMod ell :=
  firstCenter - (correction : ZMod ell) * firstLabel -
    (adaptiveMixedActualLabelCoefficient
      support secondBase secondIndex : ZMod ell) * parameter

/-- Exact membership in the ACTUAL three-variable integral-fiber selector,
including BOTH genuine nonzero labels and every physical target form. -/
theorem mem_adaptiveMixedSharedTargetLocalSelectors
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ) (firstIndex secondIndex : ℕ)
    (multiplier correction : ℤ) [Fact ell.Prime]
    (firstLabel firstCenter parameter : ZMod ell) :
    (firstLabel, firstCenter, parameter) ∈
      adaptiveMixedSharedTargetLocalSelectors support scale ell
        first second firstIndex secondIndex multiplier correction ↔
    firstLabel ≠ 0 ∧
      adaptiveMixedSharedTargetActualSecondLabel
        support first.1 firstIndex ell multiplier firstLabel parameter ≠ 0 ∧
      (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale first,
        adaptiveMixedActualAffineForm support first.1 index ell
          firstLabel firstCenter ≠ 0) ∧
      (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale second,
        adaptiveMixedActualAffineForm support second.1 index ell
          (adaptiveMixedSharedTargetActualSecondLabel
            support first.1 firstIndex ell multiplier firstLabel parameter)
          (adaptiveMixedSharedTargetActualSecondCenter
            support second.1 secondIndex ell correction
              firstLabel firstCenter parameter) ≠ 0) := by
  simp [adaptiveMixedSharedTargetLocalSelectors,
    adaptiveMixedSharedTargetActualSecondLabel,
    adaptiveMixedSharedTargetActualSecondCenter]

/-- Integer compatibility guarantees that the two ACTUAL distinguished
mixed quotient forms agree identically on the true local three-variable fiber. -/
theorem adaptiveMixedSharedTargetActualFiber_distinguished_values_eq
    {support : Finset ℕ} {scale firstIndex secondIndex ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (_primes : ∀ prime ∈ support, prime.Prime)
    (_first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (_second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction)
    (firstLabel firstCenter parameter : ZMod ell) :
    adaptiveMixedActualAffineForm support first.1 firstIndex ell
      firstLabel firstCenter =
    adaptiveMixedActualAffineForm support second.1 secondIndex ell
      (adaptiveMixedSharedTargetActualSecondLabel
        support first.1 firstIndex ell multiplier firstLabel parameter)
      (adaptiveMixedSharedTargetActualSecondCenter
        support second.1 secondIndex ell correction
          firstLabel firstCenter parameter) := by
  have compatible_field :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ZMod ell) *
          (multiplier : ZMod ell) =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ZMod ell) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ZMod ell) *
              (correction : ZMod ell) := by
    have converted :=
      congrArg (fun value : ℤ => (value : ZMod ell)) compatible
    exact_mod_cast converted
  rw [adaptiveMixedActualAffineForm_eq_coefficients,
    adaptiveMixedActualAffineForm_eq_coefficients]
  unfold adaptiveMixedSharedTargetActualSecondLabel
    adaptiveMixedSharedTargetActualSecondCenter
  rw [← adaptiveMixedActualCenterCoefficients_eq_of_same_type same_type]
  linear_combination -firstLabel * compatible_field

/-- A genuine field Bezout identity makes the fiber parameter UNIQUE even at
primes dividing the actual modulus `B`; division by `B` is never used. -/
theorem adaptiveMixedSharedTarget_field_parameter_unique
    {K : Type*} [Field K]
    (secondCoefficient modulus inverse complement : K)
    (bezout : secondCoefficient * inverse + modulus * complement = 1)
    {firstParameter secondParameter : K}
    (same_label : modulus * firstParameter =
      modulus * secondParameter)
    (same_center : secondCoefficient * firstParameter =
      secondCoefficient * secondParameter) :
    firstParameter = secondParameter := by
  calc
    firstParameter =
        (secondCoefficient * inverse + modulus * complement) *
          firstParameter := by rw [bezout, one_mul]
    _ = inverse * (secondCoefficient * firstParameter) +
          complement * (modulus * firstParameter) := by ring
    _ = inverse * (secondCoefficient * secondParameter) +
          complement * (modulus * secondParameter) := by
            rw [same_center, same_label]
    _ = (secondCoefficient * inverse + modulus * complement) *
          secondParameter := by ring
    _ = secondParameter := by rw [bezout, one_mul]

/-- UNIVERSAL exact cardinality of the ACTUAL three-variable shared-target
selector, by its genuine common-target / two-normalized-center bijection.
The same formula works at primes dividing `B`; no local division by `B`, root
independence, outside-residue equality, or local label distinctness is used. -/
theorem adaptiveMixedSharedTargetLocalSelectors_card_unit_centers
    {support : Finset ℕ} {scale firstIndex secondIndex ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction) :
    (adaptiveMixedSharedTargetLocalSelectors support scale ell
      first second firstIndex secondIndex multiplier correction).card =
      (ell - 1) *
        (adaptiveMixedActualUnitLabelCenters
          support scale ell first).card *
        (adaptiveMixedActualUnitLabelCenters
          support scale ell second).card := by
  classical
  let first_coefficient :=
    adaptiveMixedActualLabelCoefficient support first.1 firstIndex
  let second_coefficient :=
    adaptiveMixedActualLabelCoefficient support second.1 secondIndex
  let modulus :=
    adaptiveMixedActualCenterCoefficient support first.1 firstIndex
  have same_modulus : modulus =
      adaptiveMixedActualCenterCoefficient support second.1 secondIndex :=
    adaptiveMixedActualCenterCoefficients_eq_of_same_type same_type
  have coprime : Nat.Coprime second_coefficient modulus := by
    dsimp [second_coefficient, modulus]
    rw [adaptiveMixedActualCenterCoefficients_eq_of_same_type same_type]
    exact adaptiveMixedActualLabelCenterCoefficients_coprime
      primes second_active
  obtain ⟨inverse, complement, bezout⟩ :=
    sharedTargetUnit_integer_bezout second_coefficient modulus coprime
  have compatible_field :
      (second_coefficient : ZMod ell) * (multiplier : ZMod ell) =
        (first_coefficient : ZMod ell) +
          (modulus : ZMod ell) * (correction : ZMod ell) := by
    have converted :=
      congrArg (fun value : ℤ => (value : ZMod ell)) compatible
    simpa [first_coefficient, second_coefficient, modulus] using converted
  have bezout_field :
      (second_coefficient : ZMod ell) * (inverse : ZMod ell) +
        (modulus : ZMod ell) * (complement : ZMod ell) = 1 := by
    have converted :=
      congrArg (fun value : ℤ => (value : ZMod ell)) bezout
    exact_mod_cast converted
  let normalized :=
    (Finset.univ.erase (0 : ZMod ell)).product
      ((adaptiveMixedActualUnitLabelCenters
        support scale ell first).product
       (adaptiveMixedActualUnitLabelCenters
        support scale ell second))
  let second_label (triple : ZMod ell × ZMod ell × ZMod ell) :=
    adaptiveMixedSharedTargetActualSecondLabel
      support first.1 firstIndex ell multiplier triple.1 triple.2.2
  let second_center (triple : ZMod ell × ZMod ell × ZMod ell) :=
    adaptiveMixedSharedTargetActualSecondCenter
      support second.1 secondIndex ell correction
        triple.1 triple.2.1 triple.2.2
  let target (triple : ZMod ell × ZMod ell × ZMod ell) :=
    adaptiveMixedActualAffineForm
      support first.1 firstIndex ell triple.1 triple.2.1
  have bijection :
      (adaptiveMixedSharedTargetLocalSelectors support scale ell
        first second firstIndex secondIndex multiplier correction).card =
          normalized.card := by
    apply Finset.card_bij
      (fun triple _ =>
        (target triple,
          (triple.2.1 / triple.1,
           second_center triple / second_label triple)))
    · intro triple selected
      obtain ⟨first_unit, second_unit, first_forms, second_forms⟩ :=
        (mem_adaptiveMixedSharedTargetLocalSelectors
          support scale ell first second firstIndex secondIndex
            multiplier correction triple.1
              triple.2.1 triple.2.2).mp selected
      have target_unit : target triple ≠ 0 :=
        first_forms firstIndex first_active
      dsimp [normalized]
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_erase.mpr
        ⟨target_unit, Finset.mem_univ _⟩, ?_⟩
      apply Finset.mem_product.mpr
      constructor
      · apply (mem_adaptiveMixedActualUnitLabelCenters
          support scale ell first (triple.2.1 / triple.1)).mpr
        intro index active
        exact (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support first.1 index ell triple.1 triple.2.1 first_unit).mp
            (first_forms index active)
      · apply (mem_adaptiveMixedActualUnitLabelCenters
          support scale ell second
            (second_center triple / second_label triple)).mpr
        intro index active
        exact (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support second.1 index ell
            (second_label triple) (second_center triple) second_unit).mp
              (second_forms index active)
    · intro left left_selected right right_selected equal
      obtain ⟨left_unit, left_other_unit, left_forms, left_other_forms⟩ :=
        (mem_adaptiveMixedSharedTargetLocalSelectors
          support scale ell first second firstIndex secondIndex
            multiplier correction left.1 left.2.1 left.2.2).mp left_selected
      obtain ⟨right_unit, right_other_unit, right_forms, right_other_forms⟩ :=
        (mem_adaptiveMixedSharedTargetLocalSelectors
          support scale ell first second firstIndex secondIndex
            multiplier correction right.1 right.2.1 right.2.2).mp right_selected
      have same_target := congrArg Prod.fst equal
      have same_first_center := congrArg
        (fun triple : ZMod ell × ZMod ell × ZMod ell => triple.2.1) equal
      have same_second_center := congrArg
        (fun triple : ZMod ell × ZMod ell × ZMod ell => triple.2.2) equal
      change target left = target right at same_target
      change left.2.1 / left.1 = right.2.1 / right.1 at same_first_center
      change second_center left / second_label left =
        second_center right / second_label right at same_second_center
      have first_normalized_nonzero :
          adaptiveMixedActualAffineForm support first.1 firstIndex ell 1
            (left.2.1 / left.1) ≠ 0 :=
        (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support first.1 firstIndex ell left.1 left.2.1 left_unit).mp
            (left_forms firstIndex first_active)
      have same_first_label : left.1 = right.1 := by
        have values := same_target
        dsimp [target] at values
        rw [adaptiveMixedActualAffineForm_normalize_label
          support first.1 firstIndex ell
            left.1 left.2.1 left_unit,
          adaptiveMixedActualAffineForm_normalize_label
            support first.1 firstIndex ell
              right.1 right.2.1 right_unit] at values
        rw [← same_first_center] at values
        exact mul_right_cancel₀ first_normalized_nonzero values
      have same_actual_first_center : left.2.1 = right.2.1 := by
        have centers := same_first_center
        rw [← same_first_label] at centers
        exact (div_left_inj' left_unit).mp centers
      have other_values :
          adaptiveMixedActualAffineForm support second.1 secondIndex ell
            (second_label left) (second_center left) =
          adaptiveMixedActualAffineForm support second.1 secondIndex ell
            (second_label right) (second_center right) := by
        rw [← adaptiveMixedSharedTargetActualFiber_distinguished_values_eq
          primes first_active second_active same_type multiplier correction
            compatible left.1 left.2.1 left.2.2,
          ← adaptiveMixedSharedTargetActualFiber_distinguished_values_eq
            primes first_active second_active same_type multiplier correction
              compatible right.1 right.2.1 right.2.2]
        exact same_target
      have second_normalized_nonzero :
          adaptiveMixedActualAffineForm support second.1 secondIndex ell 1
            (second_center left / second_label left) ≠ 0 :=
        (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support second.1 secondIndex ell
            (second_label left) (second_center left) left_other_unit).mp
              (left_other_forms secondIndex second_active)
      have same_other_label : second_label left = second_label right := by
        rw [adaptiveMixedActualAffineForm_normalize_label
          support second.1 secondIndex ell
            (second_label left) (second_center left) left_other_unit,
          adaptiveMixedActualAffineForm_normalize_label
            support second.1 secondIndex ell
              (second_label right) (second_center right)
                right_other_unit] at other_values
        rw [← same_second_center] at other_values
        exact mul_right_cancel₀ second_normalized_nonzero other_values
      have same_actual_other_center :
          second_center left = second_center right := by
        have centers := same_second_center
        rw [← same_other_label] at centers
        exact (div_left_inj' left_other_unit).mp centers
      have same_label_parameter :
          (modulus : ZMod ell) * left.2.2 =
            (modulus : ZMod ell) * right.2.2 := by
        dsimp [second_label,
          adaptiveMixedSharedTargetActualSecondLabel,
          modulus] at same_other_label ⊢
        rw [same_first_label] at same_other_label
        exact add_left_cancel same_other_label
      have same_center_parameter :
          (second_coefficient : ZMod ell) * left.2.2 =
            (second_coefficient : ZMod ell) * right.2.2 := by
        dsimp [second_center,
          adaptiveMixedSharedTargetActualSecondCenter,
          second_coefficient] at same_actual_other_center ⊢
        rw [same_first_label, same_actual_first_center]
          at same_actual_other_center
        linear_combination -same_actual_other_center
      have same_parameter :=
        adaptiveMixedSharedTarget_field_parameter_unique
          (second_coefficient : ZMod ell)
          (modulus : ZMod ell)
          (inverse : ZMod ell) (complement : ZMod ell)
          bezout_field same_label_parameter same_center_parameter
      exact Prod.ext same_first_label
        (Prod.ext same_actual_first_center same_parameter)
    · intro triple selected
      obtain ⟨target_selected, centers_selected⟩ :=
        Finset.mem_product.mp selected
      obtain ⟨first_center_selected, second_center_selected⟩ :=
        Finset.mem_product.mp centers_selected
      have target_unit := (Finset.mem_erase.mp target_selected).1
      have first_normalized_forms :=
        (mem_adaptiveMixedActualUnitLabelCenters
          support scale ell first triple.2.1).mp first_center_selected
      have second_normalized_forms :=
        (mem_adaptiveMixedActualUnitLabelCenters
          support scale ell second triple.2.2).mp second_center_selected
      let first_factor := adaptiveMixedActualAffineForm
        support first.1 firstIndex ell 1 triple.2.1
      let second_factor := adaptiveMixedActualAffineForm
        support second.1 secondIndex ell 1 triple.2.2
      have first_factor_unit : first_factor ≠ 0 :=
        first_normalized_forms firstIndex first_active
      have second_factor_unit : second_factor ≠ 0 :=
        second_normalized_forms secondIndex second_active
      let first_label := triple.1 / first_factor
      let other_label := triple.1 / second_factor
      let first_value := triple.2.1 * first_label
      let other_value := triple.2.2 * other_label
      have first_unit : first_label ≠ 0 :=
        div_ne_zero target_unit first_factor_unit
      have other_unit : other_label ≠ 0 :=
        div_ne_zero target_unit second_factor_unit
      have first_normalized : first_value / first_label = triple.2.1 := by
        dsimp [first_value]
        field_simp
      have other_normalized : other_value / other_label = triple.2.2 := by
        dsimp [other_value]
        field_simp
      have first_forms :
          ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale first,
            adaptiveMixedActualAffineForm support first.1 index ell
              first_label first_value ≠ 0 := by
        intro index active
        apply (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support first.1 index ell first_label first_value first_unit).mpr
        rw [first_normalized]
        exact first_normalized_forms index active
      have other_forms :
          ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale second,
            adaptiveMixedActualAffineForm support second.1 index ell
              other_label other_value ≠ 0 := by
        intro index active
        apply (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support second.1 index ell other_label other_value other_unit).mpr
        rw [other_normalized]
        exact second_normalized_forms index active
      have first_target :
          adaptiveMixedActualAffineForm support first.1 firstIndex ell
            first_label first_value = triple.1 := by
        rw [adaptiveMixedActualAffineForm_normalize_label
          support first.1 firstIndex ell
            first_label first_value first_unit,
          first_normalized]
        exact div_mul_cancel₀ triple.1 first_factor_unit
      have other_target :
          adaptiveMixedActualAffineForm support second.1 secondIndex ell
            other_label other_value = triple.1 := by
        rw [adaptiveMixedActualAffineForm_normalize_label
          support second.1 secondIndex ell
            other_label other_value other_unit,
          other_normalized]
        exact div_mul_cancel₀ triple.1 second_factor_unit
      have shared :
          (first_coefficient : ZMod ell) * first_label +
            (modulus : ZMod ell) * first_value =
          (second_coefficient : ZMod ell) * other_label +
            (modulus : ZMod ell) * other_value := by
        have equal := first_target.trans other_target.symm
        rw [adaptiveMixedActualAffineForm_eq_coefficients,
          adaptiveMixedActualAffineForm_eq_coefficients] at equal
        dsimp [first_coefficient, second_coefficient, modulus]
        simpa [adaptiveMixedActualCenterCoefficients_eq_of_same_type same_type]
          using equal
      obtain ⟨parameter, labels, centers⟩ :=
        adaptiveMixedSharedTarget_field_parameter_of_equal_targets
          (first_coefficient : ZMod ell)
          (second_coefficient : ZMod ell)
          (modulus : ZMod ell)
          (multiplier : ZMod ell) (correction : ZMod ell)
          (inverse : ZMod ell) (complement : ZMod ell)
          first_label first_value other_label other_value
          compatible_field bezout_field shared
      have actual_other_label :
          adaptiveMixedSharedTargetActualSecondLabel
            support first.1 firstIndex ell multiplier
              first_label parameter = other_label := by
        exact labels.symm
      have actual_other_center :
          adaptiveMixedSharedTargetActualSecondCenter
            support second.1 secondIndex ell correction
              first_label first_value parameter = other_value := by
        exact centers.symm
      refine ⟨(first_label, first_value, parameter), ?_, ?_⟩
      · apply (mem_adaptiveMixedSharedTargetLocalSelectors
          support scale ell first second firstIndex secondIndex
            multiplier correction first_label first_value parameter).mpr
        rw [actual_other_label, actual_other_center]
        exact ⟨first_unit, other_unit, first_forms, other_forms⟩
      · apply Prod.ext
        · exact first_target
        · apply Prod.ext
          · exact first_normalized
          · change
              adaptiveMixedSharedTargetActualSecondCenter
                support second.1 secondIndex ell correction
                  first_label first_value parameter /
              adaptiveMixedSharedTargetActualSecondLabel
                support first.1 firstIndex ell multiplier
                  first_label parameter = triple.2.2
            rw [actual_other_center, actual_other_label]
            exact other_normalized
  rw [bijection]
  dsimp [normalized]
  rw [Finset.card_product, Finset.card_product]
  simp
  ring

/-- The TRUE shared-target Bezout selector and the TRUE shared-label selector
have EXACTLY the same cardinality, despite their different actual coordinates. -/
theorem adaptiveMixedSharedTargetLocalSelectors_card_eq_shared_label
    {support : Finset ℕ} {scale firstIndex secondIndex ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction) :
    (adaptiveMixedSharedTargetLocalSelectors support scale ell
      first second firstIndex secondIndex multiplier correction).card =
    (adaptiveMixedSharedLabelLocalSelectors
      support scale ell first second).card := by
  rw [adaptiveMixedSharedTargetLocalSelectors_card_unit_centers
    primes first_active second_active same_type
      multiplier correction compatible,
    adaptiveMixedSharedLabelLocalSelectors_card_unit_centers]

/-- EXACT supported-prime cardinality of the TRUE shared-target Bezout fiber,
including primes where `B=0` locally. -/
theorem adaptiveMixedSharedTargetLocalSelectors_card_supported
    {support : Finset ℕ} {scale firstIndex secondIndex ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction)
    (supported : ell ∈ support) :
    (adaptiveMixedSharedTargetLocalSelectors support scale ell
      first second firstIndex secondIndex multiplier correction).card =
        (ell - 1) * ell * ell := by
  rw [adaptiveMixedSharedTargetLocalSelectors_card_eq_shared_label
    primes first_active second_active same_type
      multiplier correction compatible,
    adaptiveMixedSharedLabelLocalSelectors_card_supported
      primes supported]

/-- EXACT outside-prime cardinality of the TRUE shared-target Bezout fiber,
retaining BOTH actual deduplicated forbidden-root sets independently. -/
theorem adaptiveMixedSharedTargetLocalSelectors_card_outside
    {support : Finset ℕ} {scale firstIndex secondIndex ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction)
    (outside : ell ∉ support) :
    (adaptiveMixedSharedTargetLocalSelectors support scale ell
      first second firstIndex secondIndex multiplier correction).card =
        (ell - 1) *
          (ell - (adaptiveMixedOutcomeLocalForbidden
            support scale ell first).card) *
          (ell - (adaptiveMixedOutcomeLocalForbidden
            support scale ell second).card) := by
  rw [adaptiveMixedSharedTargetLocalSelectors_card_eq_shared_label
    primes first_active second_active same_type
      multiplier correction compatible,
    adaptiveMixedSharedLabelLocalSelectors_card_outside
      primes outside]

/-- The TRUE normalized local factor defined from the cardinality of the
ACTUAL three-variable shared-target Bezout selector itself. -/
noncomputable def adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ) (firstIndex secondIndex : ℕ)
    (multiplier correction : ℤ) [Fact ell.Prime] : ℝ :=
  sharedTargetSharedNormalizedFactor ell
    (adaptiveMixedOutcomeActiveIndices support scale first).card
    (adaptiveMixedOutcomeActiveIndices support scale second).card
    (adaptiveMixedSharedTargetLocalSelectors support scale ell
      first second firstIndex secondIndex multiplier correction).card

/-- Instance-free packaging of the TRUE actual Bezout-fiber selector factor. -/
noncomputable def adaptiveMixedActualSharedTargetFiberScalarLocalFactor
    (support : Finset ℕ) (scale : ℕ)
    (first second : ℕ × ℕ) (firstIndex secondIndex : ℕ)
    (multiplier correction : ℤ) (ell : ℕ) : ℝ :=
  if prime : ell.Prime then
    @adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor
      support scale ell first second firstIndex secondIndex
        multiplier correction ⟨prime⟩
  else 0

/-- EXACT genuine normalized selector equality: the ACTUAL shared-target
fiber factor equals the ACTUAL shared-label selector factor at EVERY prime. -/
theorem adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor_eq_shared_label
    {support : Finset ℕ} {scale firstIndex secondIndex ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction) :
    adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor
      support scale ell first second firstIndex secondIndex
        multiplier correction =
    adaptiveMixedActualSharedLabelNormalizedLocalFactor
      support scale ell first second := by
  unfold adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor
    adaptiveMixedActualSharedLabelNormalizedLocalFactor
  rw [adaptiveMixedSharedTargetLocalSelectors_card_eq_shared_label
    primes first_active second_active same_type
      multiplier correction compatible]

/-- The ACTUAL shared-target Bezout-fiber factor is EXACTLY the product of
the two ACTUAL collision-aware individual normalized local factors. -/
theorem adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor_eq_product
    {support : Finset ℕ} {scale firstIndex secondIndex ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction) :
    adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor
      support scale ell first second firstIndex secondIndex
        multiplier correction =
    adaptiveMixedActualNormalizedLocalFactor support scale ell first *
      adaptiveMixedActualNormalizedLocalFactor support scale ell second := by
  rw [adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor_eq_shared_label
    primes first_active second_active same_type
      multiplier correction compatible,
    adaptiveMixedActualSharedLabelNormalizedLocalFactor_eq_product primes]

/-- The scalar from the TRUE actual Bezout-fiber selector equals the audited
abstract same-type paired scalar.  This closes the precise former formal gap. -/
theorem adaptiveMixedActualSharedTargetFiberScalarLocalFactor_eq_model
    {support : Finset ℕ} {scale firstIndex secondIndex ell : ℕ}
    {first second : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (prime : ell.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction) :
    adaptiveMixedActualSharedTargetFiberScalarLocalFactor
      support scale first second firstIndex secondIndex
        multiplier correction ell =
    adaptiveMixedActualSharedTargetScalarLocalFactor
      support scale first second ell := by
  calc
    _ = adaptiveMixedActualSharedLabelScalarLocalFactor
          support scale first second ell := by
      simp only [adaptiveMixedActualSharedTargetFiberScalarLocalFactor,
        adaptiveMixedActualSharedLabelScalarLocalFactor, dif_pos prime]
      exact @adaptiveMixedActualSharedTargetFiberNormalizedLocalFactor_eq_shared_label
        support scale firstIndex secondIndex ell first second ⟨prime⟩
          primes first_active second_active same_type
          multiplier correction compatible
    _ = _ := adaptiveMixedActualSharedLabelScalarLocalFactor_eq_shared_target
      support scale ell first second primes prime

/-- Full finite Euler-product factorization for factors defined DIRECTLY from
the cardinalities of the ACTUAL shared-target three-variable Bezout selectors. -/
theorem adaptiveMixedActualSharedTargetFiber_finite_singular_product_eq_product
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction)
    (evaluation : Finset ℕ)
    (evaluation_primes : ∀ ell ∈ evaluation, ell.Prime) :
    (∏ ell ∈ evaluation,
      adaptiveMixedActualSharedTargetFiberScalarLocalFactor
        support scale first second firstIndex secondIndex
          multiplier correction ell) =
      (∏ ell ∈ evaluation,
        adaptiveMixedActualScalarLocalFactor support scale ell first) *
      (∏ ell ∈ evaluation,
        adaptiveMixedActualScalarLocalFactor support scale ell second) := by
  calc
    _ = ∏ ell ∈ evaluation,
          adaptiveMixedActualSharedTargetScalarLocalFactor
            support scale first second ell := by
      apply Finset.prod_congr rfl
      intro ell selected
      exact adaptiveMixedActualSharedTargetFiberScalarLocalFactor_eq_model
        primes (evaluation_primes ell selected)
        first_active second_active same_type
          multiplier correction compatible
    _ = _ :=
      adaptiveMixedActualSharedTarget_finite_singular_product_eq_product
        support scale first second evaluation primes evaluation_primes

/-- UNCONDITIONAL evaluation-support-uniform strictly positive floor for
finite products of the TRUE actual Bezout-fiber selector local factors. -/
theorem adaptiveMixedActualSharedTargetFiber_singular_product_uniform_positive
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ evaluation : Finset ℕ,
        (∀ ell ∈ evaluation, ell.Prime) →
          constant ≤ ∏ ell ∈ evaluation,
            adaptiveMixedActualSharedTargetFiberScalarLocalFactor
              support scale first second firstIndex secondIndex
                multiplier correction ell := by
  obtain ⟨constant, positive, lower⟩ :=
    adaptiveMixedActualSharedTarget_singular_product_uniform_positive
      support scale first second primes
  refine ⟨constant, positive, ?_⟩
  intro evaluation evaluation_primes
  calc
    constant ≤ ∏ ell ∈ evaluation,
      adaptiveMixedActualSharedTargetScalarLocalFactor
        support scale first second ell :=
          lower evaluation evaluation_primes
    _ = ∏ ell ∈ evaluation,
      adaptiveMixedActualSharedTargetFiberScalarLocalFactor
        support scale first second firstIndex secondIndex
          multiplier correction ell := by
      apply Finset.prod_congr rfl
      intro ell selected
      exact (adaptiveMixedActualSharedTargetFiberScalarLocalFactor_eq_model
        primes (evaluation_primes ell selected)
        first_active second_active same_type
          multiplier correction compatible).symm

end Erdos1139

