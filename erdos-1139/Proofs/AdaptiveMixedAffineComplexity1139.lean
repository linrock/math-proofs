module

public import AdaptiveMixedPatternDistribution1139

@[expose] public section


/-!
# Genuine finite Cauchy--Schwarz complexity of actual mixed forms

For ONE shared actual mixed-pattern outcome `(b,rho)`, put

    W = (∏ s ∈ S, s)^2,
    t_d = gcd(W,b+d),
    A_d = (b+d)/t_d,
    B_d = W/t_d.

The system consists of the genuine prime-label form `P` together with
the actual integer forms `A_d P + B_d C` at retained PHYSICAL indices
`1 ≤ d ≤ T`.  Distinct indices satisfy the exact integral identity

    t_d t_e (A_d B_e - A_e B_d) = W (d-e).

Thus the actual forms are pairwise nonproportional over the rationals,
including the prime-label form.  Singleton classes give the explicit
standard finite Cauchy--Schwarz complexity bound `rank-1`.

This verifies a structural hypothesis of a potential Green--Tao--Ziegler
application.  It does NOT assert that theorem, uniform quantitative prime
counts, shared-target covariance, or a solution of Erdős #1139.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- The TRUE integer label coefficient of one selected physical target. -/
def adaptiveMixedActualLabelCoefficient
    (support : Finset ℕ) (center index : ℕ) : ℕ :=
  (center + index) / adaptiveMixedActualIndexType support center index

/-- The TRUE integer center coefficient of one selected physical target. -/
def adaptiveMixedActualCenterCoefficient
    (support : Finset ℕ) (center index : ℕ) : ℕ :=
  adaptiveMixedTypeModulus support /
    adaptiveMixedActualIndexType support center index

/-- The new explicit integer coefficients are EXACTLY the coefficients
of the already audited actual finite-field mixed affine form. -/
theorem adaptiveMixedActualAffineForm_eq_coefficients
    (support : Finset ℕ) (center index ell : ℕ)
    (label value : ZMod ell) :
    adaptiveMixedActualAffineForm support center index ell label value =
      (adaptiveMixedActualLabelCoefficient support center index : ZMod ell) *
        label +
      (adaptiveMixedActualCenterCoefficient support center index : ZMod ell) *
        value := by
  rfl

/-- The TRUE type of every actually retained physical index is positive. -/
theorem adaptiveMixedActualIndexType_pos_of_active
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    0 < adaptiveMixedActualIndexType support outcome.1 index := by
  exact Nat.pos_of_dvd_of_pos
    (adaptiveMixedOutcomeActiveIndex_type_dvd_modulus primes active)
    (adaptiveMixedTypeModulus_pos support primes)

/-- Actual physical indices are genuinely positive and at most the
original reciprocal scale. -/
theorem adaptiveMixedOutcomeActiveIndex_physical_bounds
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    1 ≤ index ∧ index ≤ scale := by
  exact Finset.mem_Icc.mp
    (adaptiveMixedOutcomeActiveIndices_subset_physical
      support scale outcome active)

/-- Exact integer recovery of the TRUE unreduced target numerator. -/
theorem adaptiveMixedActualLabelCoefficient_factor
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualIndexType support outcome.1 index *
      adaptiveMixedActualLabelCoefficient support outcome.1 index =
        outcome.1 + index := by
  exact Nat.mul_div_cancel'
    (adaptiveMixedOutcomeActiveIndex_type_dvd_value primes active)

/-- Exact integer recovery of the TRUE squared support modulus. -/
theorem adaptiveMixedActualCenterCoefficient_factor
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualIndexType support outcome.1 index *
      adaptiveMixedActualCenterCoefficient support outcome.1 index =
        adaptiveMixedTypeModulus support := by
  exact Nat.mul_div_cancel'
    (adaptiveMixedOutcomeActiveIndex_type_dvd_modulus primes active)

/-- EVERY retained actual target has strictly positive genuine center
coefficient; consequently it cannot equal a constant or a label multiple. -/
theorem adaptiveMixedActualCenterCoefficient_pos
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    0 < adaptiveMixedActualCenterCoefficient support outcome.1 index := by
  have modulus_positive := adaptiveMixedTypeModulus_pos support primes
  have factor := adaptiveMixedActualCenterCoefficient_factor primes active
  by_contra not_positive
  have zero : adaptiveMixedActualCenterCoefficient
      support outcome.1 index = 0 := by omega
  rw [zero, Nat.mul_zero] at factor
  omega

/-- EVERY retained actual target also has strictly positive genuine label
coefficient; physical index zero is not inserted into the pattern. -/
theorem adaptiveMixedActualLabelCoefficient_pos
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    0 < adaptiveMixedActualLabelCoefficient support outcome.1 index := by
  have index_positive :=
    (adaptiveMixedOutcomeActiveIndex_physical_bounds active).1
  have factor := adaptiveMixedActualLabelCoefficient_factor primes active
  by_contra not_positive
  have zero : adaptiveMixedActualLabelCoefficient
      support outcome.1 index = 0 := by omega
  rw [zero, Nat.mul_zero] at factor
  omega

/-- One exact nonnegative cross-product identity, retaining BOTH genuine
possibly distinct types before forming the signed determinant. -/
theorem adaptiveMixedActualCoefficients_cross_product
    {support : Finset ℕ} {scale first second : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      first ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (second_active :
      second ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualIndexType support outcome.1 first *
      adaptiveMixedActualIndexType support outcome.1 second *
      (adaptiveMixedActualLabelCoefficient support outcome.1 first *
        adaptiveMixedActualCenterCoefficient support outcome.1 second) =
      (outcome.1 + first) * adaptiveMixedTypeModulus support := by
  have first_factor :=
    adaptiveMixedActualLabelCoefficient_factor primes first_active
  have second_factor :=
    adaptiveMixedActualCenterCoefficient_factor primes second_active
  calc
    _ =
      (adaptiveMixedActualIndexType support outcome.1 first *
        adaptiveMixedActualLabelCoefficient support outcome.1 first) *
      (adaptiveMixedActualIndexType support outcome.1 second *
        adaptiveMixedActualCenterCoefficient support outcome.1 second) := by
          ring
    _ = _ := by rw [first_factor, second_factor]

/-- The EXACT signed integral determinant identity.  It retains the true
squared modulus, BOTH actual types, and BOTH unreduced physical indices. -/
theorem adaptiveMixedActualCoefficients_integral_determinant_identity
    {support : Finset ℕ} {scale first second : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      first ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (second_active :
      second ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    (adaptiveMixedActualIndexType support outcome.1 first : ℤ) *
      (adaptiveMixedActualIndexType support outcome.1 second : ℤ) *
      ((adaptiveMixedActualLabelCoefficient
          support outcome.1 first : ℤ) *
        (adaptiveMixedActualCenterCoefficient
          support outcome.1 second : ℤ) -
       (adaptiveMixedActualLabelCoefficient
          support outcome.1 second : ℤ) *
        (adaptiveMixedActualCenterCoefficient
          support outcome.1 first : ℤ)) =
      (adaptiveMixedTypeModulus support : ℤ) *
        ((first : ℤ) - (second : ℤ)) := by
  have forward := congrArg (fun value : ℕ => (value : ℤ))
    (adaptiveMixedActualCoefficients_cross_product
      primes first_active second_active)
  have backward := congrArg (fun value : ℕ => (value : ℤ))
    (adaptiveMixedActualCoefficients_cross_product
      primes second_active first_active)
  push_cast at forward backward ⊢
  nlinarith [forward, backward]

/-- Distinct retained physical indices have NONZERO exact signed
integer determinant, regardless of whether their true mixed types agree. -/
theorem adaptiveMixedActualCoefficients_integral_determinant_ne_zero
    {support : Finset ℕ} {scale first second : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      first ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (second_active :
      second ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (different : first ≠ second) :
    (adaptiveMixedActualLabelCoefficient support outcome.1 first : ℤ) *
      (adaptiveMixedActualCenterCoefficient support outcome.1 second : ℤ) -
    (adaptiveMixedActualLabelCoefficient support outcome.1 second : ℤ) *
      (adaptiveMixedActualCenterCoefficient support outcome.1 first : ℤ) ≠
        0 := by
  intro zero
  have identity :=
    adaptiveMixedActualCoefficients_integral_determinant_identity
      primes first_active second_active
  rw [zero, mul_zero] at identity
  have modulus_nonzero : (adaptiveMixedTypeModulus support : ℤ) ≠ 0 := by
    exact_mod_cast (adaptiveMixedTypeModulus_pos support primes).ne'
  have index_zero : (first : ℤ) - (second : ℤ) = 0 := by
    exact (mul_eq_zero.mp identity.symm).resolve_left modulus_nonzero
  have same : first = second := by
    exact_mod_cast (sub_eq_zero.mp index_zero)
  exact different same

/-- The same exact nondegeneracy holds for the ACTUAL rational coefficient
vectors required by the standard finite-complexity prime-pattern theorem. -/
theorem adaptiveMixedActualCoefficients_rational_determinant_ne_zero
    {support : Finset ℕ} {scale first second : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      first ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (second_active :
      second ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (different : first ≠ second) :
    (adaptiveMixedActualLabelCoefficient support outcome.1 first : ℚ) *
      (adaptiveMixedActualCenterCoefficient support outcome.1 second : ℚ) -
    (adaptiveMixedActualLabelCoefficient support outcome.1 second : ℚ) *
      (adaptiveMixedActualCenterCoefficient support outcome.1 first : ℚ) ≠
        0 := by
  intro zero
  have integer_zero :
      (adaptiveMixedActualLabelCoefficient support outcome.1 first : ℤ) *
        (adaptiveMixedActualCenterCoefficient support outcome.1 second : ℤ) -
      (adaptiveMixedActualLabelCoefficient support outcome.1 second : ℤ) *
        (adaptiveMixedActualCenterCoefficient support outcome.1 first : ℤ) =
          0 := by
    exact_mod_cast zero
  exact adaptiveMixedActualCoefficients_integral_determinant_ne_zero
    primes first_active second_active different integer_zero

/-- Actual system labels: `none` is the genuine prime-label form `P`,
while `some d` is the true mixed target at physical index `d`. -/
def adaptiveMixedActualFormIndices
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) :
      Finset (Option ℕ) :=
  insert none ((adaptiveMixedOutcomeActiveIndices
    support scale outcome).image some)

/-- The actual prime-label form is ALWAYS part of the finite system. -/
theorem adaptiveMixedActualFormIndices_label_mem
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) :
    none ∈ adaptiveMixedActualFormIndices support scale outcome := by
  simp [adaptiveMixedActualFormIndices]

/-- A target-form label occurs IFF its true physical index is actually
retained by the ONE common mixed-pattern outcome. -/
theorem adaptiveMixedActualFormIndices_target_mem_iff
    (support : Finset ℕ) (scale index : ℕ) (outcome : ℕ × ℕ) :
    some index ∈ adaptiveMixedActualFormIndices support scale outcome ↔
      index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome := by
  simp [adaptiveMixedActualFormIndices]

/-- The actual system has EXACTLY one prime-label form plus its genuine
number of retained physical mixed target forms. -/
theorem adaptiveMixedActualFormIndices_card
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) :
    (adaptiveMixedActualFormIndices support scale outcome).card =
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card + 1 := by
  unfold adaptiveMixedActualFormIndices
  rw [Finset.card_insert_of_notMem (by simp)]
  rw [Finset.card_image_iff.mpr
    (fun first _ second _ equal => Option.some.inj equal)]

/-- In particular, the full actual affine system has at most `scale+1`
forms; the extra form is the necessary genuine prime label. -/
theorem adaptiveMixedActualFormIndices_card_le_scale_add_one
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) :
    (adaptiveMixedActualFormIndices support scale outcome).card ≤ scale + 1 := by
  rw [adaptiveMixedActualFormIndices_card]
  exact Nat.add_le_add_right
    (adaptiveMixedOutcomeActiveIndices_card_le_scale
      support scale outcome) 1

/-- The TRUE rational coefficient vector of each actual form, retaining
the prime-label vector `(1,0)` and every unreduced mixed target vector. -/
def adaptiveMixedActualFormVector
    (support : Finset ℕ) (center : ℕ) : Option ℕ → ℚ × ℚ
  | none => (1, 0)
  | some index =>
      ((adaptiveMixedActualLabelCoefficient support center index : ℚ),
       (adaptiveMixedActualCenterCoefficient support center index : ℚ))

/-- Every actual form vector, INCLUDING the prime-label form, is nonzero. -/
theorem adaptiveMixedActualFormVector_ne_zero
    {support : Finset ℕ} {scale : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    {index : Option ℕ}
    (selected : index ∈ adaptiveMixedActualFormIndices
      support scale outcome) :
    adaptiveMixedActualFormVector support outcome.1 index ≠ 0 := by
  cases index with
  | none =>
      intro zero
      have first := congrArg Prod.fst zero
      norm_num [adaptiveMixedActualFormVector] at first
  | some index =>
      have active :=
        (adaptiveMixedActualFormIndices_target_mem_iff
          support scale index outcome).mp selected
      have positive := adaptiveMixedActualCenterCoefficient_pos
        primes active
      intro zero
      have second := congrArg Prod.snd zero
      change (adaptiveMixedActualCenterCoefficient
        support outcome.1 index : ℚ) = 0 at second
      have integer_zero :
          adaptiveMixedActualCenterCoefficient
            support outcome.1 index = 0 := by
        exact_mod_cast second
      omega

/-- No ACTUAL target vector is a rational multiple of the genuine prime
label vector `(1,0)` because its true center coefficient is positive. -/
theorem adaptiveMixedActualTargetVector_not_label_multiple
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    ¬ ∃ coefficient : ℚ,
      adaptiveMixedActualFormVector support outcome.1 (some index) =
        coefficient •
          adaptiveMixedActualFormVector support outcome.1 none := by
  rintro ⟨coefficient, equal⟩
  have second := congrArg Prod.snd equal
  change (adaptiveMixedActualCenterCoefficient
    support outcome.1 index : ℚ) = coefficient * 0 at second
  simp at second
  have zero : adaptiveMixedActualCenterCoefficient
      support outcome.1 index = 0 := by
    exact_mod_cast second
  have positive := adaptiveMixedActualCenterCoefficient_pos primes active
  omega

/-- Conversely, the genuine prime-label vector cannot be a rational
multiple of ANY actual mixed target vector. -/
theorem adaptiveMixedActualLabelVector_not_target_multiple
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    ¬ ∃ coefficient : ℚ,
      adaptiveMixedActualFormVector support outcome.1 none =
        coefficient •
          adaptiveMixedActualFormVector support outcome.1 (some index) := by
  rintro ⟨coefficient, equal⟩
  have first := congrArg Prod.fst equal
  have second := congrArg Prod.snd equal
  change (1 : ℚ) = coefficient *
    (adaptiveMixedActualLabelCoefficient
      support outcome.1 index : ℚ) at first
  change (0 : ℚ) = coefficient *
    (adaptiveMixedActualCenterCoefficient
      support outcome.1 index : ℚ) at second
  have center_nonzero :
      (adaptiveMixedActualCenterCoefficient
        support outcome.1 index : ℚ) ≠ 0 := by
    exact_mod_cast (adaptiveMixedActualCenterCoefficient_pos
      primes active).ne'
  have coefficient_zero : coefficient = 0 :=
    (mul_eq_zero.mp second.symm).resolve_right center_nonzero
  rw [coefficient_zero, zero_mul] at first
  norm_num at first

/-- Distinct genuine retained targets are not rational scalar multiples;
their exact signed two-by-two determinant cannot vanish. -/
theorem adaptiveMixedActualTargetVectors_not_proportional
    {support : Finset ℕ} {scale first second : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      first ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (second_active :
      second ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (different : first ≠ second) :
    ¬ ∃ coefficient : ℚ,
      adaptiveMixedActualFormVector support outcome.1 (some first) =
        coefficient •
          adaptiveMixedActualFormVector support outcome.1 (some second) := by
  rintro ⟨coefficient, equal⟩
  have first_coordinate := congrArg Prod.fst equal
  have second_coordinate := congrArg Prod.snd equal
  change (adaptiveMixedActualLabelCoefficient
    support outcome.1 first : ℚ) = coefficient *
      (adaptiveMixedActualLabelCoefficient
        support outcome.1 second : ℚ) at first_coordinate
  change (adaptiveMixedActualCenterCoefficient
    support outcome.1 first : ℚ) = coefficient *
      (adaptiveMixedActualCenterCoefficient
        support outcome.1 second : ℚ) at second_coordinate
  have zero :
      (adaptiveMixedActualLabelCoefficient
          support outcome.1 first : ℚ) *
        (adaptiveMixedActualCenterCoefficient
          support outcome.1 second : ℚ) -
      (adaptiveMixedActualLabelCoefficient
          support outcome.1 second : ℚ) *
        (adaptiveMixedActualCenterCoefficient
          support outcome.1 first : ℚ) = 0 := by
    rw [first_coordinate, second_coordinate]
    ring
  exact adaptiveMixedActualCoefficients_rational_determinant_ne_zero
    primes first_active second_active different zero

/-- The COMPLETE actual affine system, INCLUDING its prime-label form,
is pairwise nonproportional over the rationals. -/
theorem adaptiveMixedActualFormVectors_pairwise_not_proportional
    {support : Finset ℕ} {scale : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    {first second : Option ℕ}
    (first_selected : first ∈ adaptiveMixedActualFormIndices
      support scale outcome)
    (second_selected : second ∈ adaptiveMixedActualFormIndices
      support scale outcome)
    (different : first ≠ second) :
    ¬ ∃ coefficient : ℚ,
      adaptiveMixedActualFormVector support outcome.1 first =
        coefficient •
          adaptiveMixedActualFormVector support outcome.1 second := by
  cases first with
  | none =>
      cases second with
      | none => exact (different rfl).elim
      | some index =>
          exact adaptiveMixedActualLabelVector_not_target_multiple
            primes
              ((adaptiveMixedActualFormIndices_target_mem_iff
                support scale index outcome).mp second_selected)
  | some index =>
      cases second with
      | none =>
          exact adaptiveMixedActualTargetVector_not_label_multiple
            primes
              ((adaptiveMixedActualFormIndices_target_mem_iff
                support scale index outcome).mp first_selected)
      | some other =>
          apply adaptiveMixedActualTargetVectors_not_proportional
            primes
              ((adaptiveMixedActualFormIndices_target_mem_iff
                support scale index outcome).mp first_selected)
              ((adaptiveMixedActualFormIndices_target_mem_iff
                support scale other outcome).mp second_selected)
          intro equal
          exact different (congrArg some equal)

/-- No actual distinguished form lies in the rational span of ANY other
single actual form: the exact singleton Cauchy--Schwarz condition. -/
theorem adaptiveMixedActualFormVector_not_mem_other_singleton_span
    {support : Finset ℕ} {scale : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    {first second : Option ℕ}
    (first_selected : first ∈ adaptiveMixedActualFormIndices
      support scale outcome)
    (second_selected : second ∈ adaptiveMixedActualFormIndices
      support scale outcome)
    (different : first ≠ second) :
    adaptiveMixedActualFormVector support outcome.1 first ∉
      Submodule.span ℚ
        ({adaptiveMixedActualFormVector support outcome.1 second} :
          Set (ℚ × ℚ)) := by
  intro selected
  obtain ⟨coefficient, equal⟩ := Submodule.mem_span_singleton.mp selected
  exact adaptiveMixedActualFormVectors_pairwise_not_proportional
    primes first_selected second_selected different
      ⟨coefficient, equal.symm⟩

/-- The actual singleton partition for a distinguished form: EVERY other
genuine label/target form receives its OWN class. -/
def adaptiveMixedActualSingletonCSClasses
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (distinguished : Option ℕ) : Finset (Finset (Option ℕ)) :=
  ((adaptiveMixedActualFormIndices support scale outcome).erase distinguished).image
    fun other => {other}

/-- The actual singleton classes cover EXACTLY all other actual forms,
neither dropping the prime-label form nor adding a fictitious target. -/
theorem adaptiveMixedActualSingletonCSClasses_biUnion
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (distinguished : Option ℕ) :
    (adaptiveMixedActualSingletonCSClasses
      support scale outcome distinguished).biUnion id =
        (adaptiveMixedActualFormIndices
          support scale outcome).erase distinguished := by
  classical
  ext index
  simp [adaptiveMixedActualSingletonCSClasses]

/-- The number of singleton classes is EXACTLY the actual mixed target
rank, including when the distinguished form is the prime-label form. -/
theorem adaptiveMixedActualSingletonCSClasses_card
    {support : Finset ℕ} {scale : ℕ} {outcome : ℕ × ℕ}
    {distinguished : Option ℕ}
    (selected : distinguished ∈ adaptiveMixedActualFormIndices
      support scale outcome) :
    (adaptiveMixedActualSingletonCSClasses
      support scale outcome distinguished).card =
        (adaptiveMixedOutcomeActiveIndices
          support scale outcome).card := by
  unfold adaptiveMixedActualSingletonCSClasses
  rw [Finset.card_image_iff.mpr
    (fun first _ second _ equal => Finset.singleton_inj.mp equal),
    Finset.card_erase_of_mem selected,
    adaptiveMixedActualFormIndices_card]
  omega

/-- Every singleton class is genuinely nonempty. -/
theorem adaptiveMixedActualSingletonCSClasses_nonempty
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (distinguished : Option ℕ)
    (block : Finset (Option ℕ))
    (selected : block ∈ adaptiveMixedActualSingletonCSClasses
      support scale outcome distinguished) :
    block.Nonempty := by
  obtain ⟨other, _selected, rfl⟩ := Finset.mem_image.mp selected
  exact Finset.singleton_nonempty other

/-- Distinct genuine singleton classes are pairwise disjoint, so the
displayed witness is a true finite PARTITION rather than merely a cover. -/
theorem adaptiveMixedActualSingletonCSClasses_disjoint
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (distinguished : Option ℕ)
    {first second : Finset (Option ℕ)}
    (first_selected : first ∈ adaptiveMixedActualSingletonCSClasses
      support scale outcome distinguished)
    (second_selected : second ∈ adaptiveMixedActualSingletonCSClasses
      support scale outcome distinguished)
    (different : first ≠ second) :
    Disjoint first second := by
  obtain ⟨first_index, _first_other, rfl⟩ :=
    Finset.mem_image.mp first_selected
  obtain ⟨second_index, _second_other, rfl⟩ :=
    Finset.mem_image.mp second_selected
  have different_indices : first_index ≠ second_index := by
    intro equal
    exact different (congrArg (fun index => ({index} : Finset (Option ℕ))) equal)
  apply Finset.disjoint_left.mpr
  intro index in_first in_second
  exact different_indices
    ((Finset.mem_singleton.mp in_first).symm.trans
      (Finset.mem_singleton.mp in_second))

/-- The distinguished actual rational form lies outside the rational
span of EVERY class of its actual singleton partition. -/
theorem adaptiveMixedActualSingletonCSClasses_avoids_span
    {support : Finset ℕ} {scale : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    {distinguished : Option ℕ}
    (distinguished_selected : distinguished ∈
      adaptiveMixedActualFormIndices support scale outcome)
    {block : Finset (Option ℕ)}
    (selected : block ∈ adaptiveMixedActualSingletonCSClasses
      support scale outcome distinguished) :
    adaptiveMixedActualFormVector support outcome.1 distinguished ∉
      Submodule.span ℚ
        (↑(block.image (adaptiveMixedActualFormVector
          support outcome.1)) : Set (ℚ × ℚ)) := by
  obtain ⟨other, other_selected, rfl⟩ := Finset.mem_image.mp selected
  obtain ⟨different, other_actual⟩ := Finset.mem_erase.mp other_selected
  simpa using
    adaptiveMixedActualFormVector_not_mem_other_singleton_span
      primes distinguished_selected other_actual different.symm

/-- The standard finite Cauchy--Schwarz complexity condition, expressed
directly for the ACTUAL label-plus-mixed-target rational form system.
For each distinguished form the remaining forms are partitioned into at
most `complexity+1` nonempty disjoint classes, none spanning that form. -/
def AdaptiveMixedActualHasCSComplexityAtMost
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (complexity : ℕ) : Prop :=
  ∀ distinguished ∈ adaptiveMixedActualFormIndices
      support scale outcome,
    ∃ classes : Finset (Finset (Option ℕ)),
      classes.card ≤ complexity + 1 ∧
      classes.biUnion id =
        (adaptiveMixedActualFormIndices
          support scale outcome).erase distinguished ∧
      (∀ block ∈ classes, block.Nonempty) ∧
      (∀ first ∈ classes, ∀ second ∈ classes,
        first ≠ second → Disjoint first second) ∧
      (∀ block ∈ classes,
        adaptiveMixedActualFormVector support outcome.1 distinguished ∉
          Submodule.span ℚ
            (↑(block.image (adaptiveMixedActualFormVector
              support outcome.1)) : Set (ℚ × ℚ)))

/-- EXPLICIT actual finite Cauchy--Schwarz complexity certificate:
the genuine prime-label-plus-mixed-target system has complexity at most
`actualTargetRank-1`, using its COMPLETE actual singleton partition. -/
theorem adaptiveMixedActualForms_csComplexity_le_rank_sub_one
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    AdaptiveMixedActualHasCSComplexityAtMost support scale outcome
      ((adaptiveMixedOutcomeActiveIndices
        support scale outcome).card - 1) := by
  intro distinguished selected
  refine ⟨adaptiveMixedActualSingletonCSClasses
    support scale outcome distinguished, ?_, ?_, ?_, ?_, ?_⟩
  · rw [adaptiveMixedActualSingletonCSClasses_card selected]
    omega
  · exact adaptiveMixedActualSingletonCSClasses_biUnion
      support scale outcome distinguished
  · exact adaptiveMixedActualSingletonCSClasses_nonempty
      support scale outcome distinguished
  · intro first first_selected second second_selected different
    exact adaptiveMixedActualSingletonCSClasses_disjoint
      support scale outcome distinguished
      first_selected second_selected different
  · intro block block_selected
    exact adaptiveMixedActualSingletonCSClasses_avoids_span
      primes selected block_selected

/-- Consequently the ACTUAL Cauchy--Schwarz complexity is bounded in
terms of the original physical scale, with no dependence on fake indices. -/
theorem adaptiveMixedActualForms_csComplexity_le_scale
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    AdaptiveMixedActualHasCSComplexityAtMost
      support scale outcome scale := by
  intro distinguished selected
  obtain ⟨classes, cardinal, union, nonempty, disjoint, span⟩ :=
    adaptiveMixedActualForms_csComplexity_le_rank_sub_one
      support scale outcome primes distinguished selected
  refine ⟨classes, ?_, union, nonempty, disjoint, span⟩
  have rank_bounded :=
    adaptiveMixedOutcomeActiveIndices_card_le_scale
      support scale outcome
  omega


end Erdos1139
