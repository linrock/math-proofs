module

public import AdaptiveMixedAffineComplexity1139
public import AdaptiveMixedSingularSeries1139
public import SharedTargetFiberCovolume1139
public import SharedTargetSingularFactorization1139

@[expose] public section


/-!
# Actual paired mixed-pattern local systems

Two independently sampled adaptive outcomes have different genuine squared-core
centers and different outside residues.  Their shared-label correlation uses one
prime-label coordinate and two independent SIGNED center coordinates.  Their
same-type shared-target correlation uses the actual three-coordinate integral
fiber

    P' = c P + B t,       C' = C - k P - a' t,

where `a' c = a + B k` and `gcd(a', B) = 1`.

An adversarial search using the repository-pinned `.venv/bin/python` exhaustively
checked 41,548 actual paired local systems: supports `{2}`, `{3}`, `{2,3}`;
physical scales `3,5,7`; deterministic fixed-stride samples of at most 28 genuine
`(b,rho)` outcomes per case; every retained same-type distinguished pair; and
every field `F_2,F_3,F_5,F_7`.  No paired local obstruction exists.  The reason
is proved below: rescale one complete admissible branch until its nonzero
distinguished target agrees with the other, then use a genuine INTEGRAL Bezout
certificate to lift the pair to the three-coordinate fiber.  This remains true
at primes dividing `B`, and distinct integer prime labels may coincide locally.

Centers in this file are finite-field reductions of SIGNED integer coordinates.
No positive-center box is identified with the actual physical adaptive convex
strip, and no Green--Tao--Ziegler theorem, global moment estimate, or solution
of Erdős #1139 is claimed.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos1139

/-- Exact homogeneity of every ACTUAL mixed quotient affine form, including
supported semiprime types. -/
theorem adaptiveMixedActualAffineForm_scale_both
    (support : Finset ℕ) (center index ell : ℕ)
    (factor label value : ZMod ell) :
    adaptiveMixedActualAffineForm support center index ell
      (factor * label) (factor * value) =
      factor * adaptiveMixedActualAffineForm
        support center index ell label value := by
  unfold adaptiveMixedActualAffineForm
  ring

/-- A genuine retained index has COPRIME actual label and center coefficients;
this is true for both prime targets and every supported semiprime type. -/
theorem adaptiveMixedActualLabelCenterCoefficients_coprime
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    Nat.Coprime
      (adaptiveMixedActualLabelCoefficient support outcome.1 index)
      (adaptiveMixedActualCenterCoefficient support outcome.1 index) := by
  rcases adaptiveMixedOutcomeActiveIndex_type_certificate primes active with
    ⟨typed, coprime, _outside⟩ |
      ⟨selected, _supported, typed, _divides, coprime, _outside⟩
  · simpa [adaptiveMixedActualLabelCoefficient,
      adaptiveMixedActualCenterCoefficient, typed] using coprime.symm
  · simpa [adaptiveMixedActualLabelCoefficient,
      adaptiveMixedActualCenterCoefficient, typed] using coprime.symm

/-- Same TRUE mixed types give the same TRUE reduced squared-core modulus. -/
theorem adaptiveMixedActualCenterCoefficients_eq_of_same_type
    {support : Finset ℕ} {firstCenter secondCenter firstIndex secondIndex : ℕ}
    (same_type :
      adaptiveMixedActualIndexType support firstCenter firstIndex =
        adaptiveMixedActualIndexType support secondCenter secondIndex) :
    adaptiveMixedActualCenterCoefficient support firstCenter firstIndex =
      adaptiveMixedActualCenterCoefficient support secondCenter secondIndex := by
  simp only [adaptiveMixedActualCenterCoefficient, same_type]

/-- The ACTUAL shared-label selector: one genuine prime label, two independent
signed center residues, and every retained physical form of BOTH outcomes. -/
noncomputable def adaptiveMixedSharedLabelLocalSelectors
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ) [Fact ell.Prime] :
    Finset (ZMod ell × ZMod ell × ZMod ell) :=
  Finset.univ.filter fun triple =>
    triple.1 ≠ 0 ∧
      (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale first,
        adaptiveMixedActualAffineForm
          support first.1 index ell triple.1 triple.2.1 ≠ 0) ∧
      (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale second,
        adaptiveMixedActualAffineForm
          support second.1 index ell triple.1 triple.2.2 ≠ 0)

/-- Every two independently sampled ACTUAL mixed outcomes have an admissible
shared-label system at EVERY prime, with one label and distinct center
coordinates.  Outside residues need not agree. -/
theorem adaptiveMixedSharedLabelLocalSelectors_nonempty
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ) [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime) :
    (adaptiveMixedSharedLabelLocalSelectors
      support scale ell first second).Nonempty := by
  obtain ⟨first_label, first_center, first_unit, first_forms⟩ :=
    adaptiveMixedOutcome_all_prime_locally_admissible
      support scale first primes ell
  obtain ⟨second_label, second_center, second_unit, second_forms⟩ :=
    adaptiveMixedOutcome_all_prime_locally_admissible
      support scale second primes ell
  refine ⟨(1, first_center / first_label,
      second_center / second_label), ?_⟩
  simp only [adaptiveMixedSharedLabelLocalSelectors,
    Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨one_ne_zero, ?_, ?_⟩
  · intro index active
    exact (adaptiveMixedActualAffineForm_normalized_nonzero_iff
      support first.1 index ell first_label first_center first_unit).mp
        (first_forms index active)
  · intro index active
    exact (adaptiveMixedActualAffineForm_normalized_nonzero_iff
      support second.1 index ell second_label second_center second_unit).mp
        (second_forms index active)

/-- Field-level surjectivity of the TRUE three-coordinate shared-target
parameterization.  The Bezout identity, not division by `B`, makes this valid
even at primes dividing the reduced squared-core modulus. -/
theorem adaptiveMixedSharedTarget_field_parameter_of_equal_targets
    {K : Type*} [Field K]
    (firstCoefficient secondCoefficient modulus multiplier correction
      inverse complement firstLabel firstCenter secondLabel secondCenter : K)
    (compatible : secondCoefficient * multiplier =
      firstCoefficient + modulus * correction)
    (bezout : secondCoefficient * inverse + modulus * complement = 1)
    (shared : firstCoefficient * firstLabel + modulus * firstCenter =
      secondCoefficient * secondLabel + modulus * secondCenter) :
    ∃ parameter : K,
      secondLabel = multiplier * firstLabel + modulus * parameter ∧
        secondCenter = firstCenter - correction * firstLabel -
          secondCoefficient * parameter := by
  let label_difference := secondLabel - multiplier * firstLabel
  let center_difference := firstCenter - secondCenter - correction * firstLabel
  have mixed : secondCoefficient * label_difference =
      modulus * center_difference := by
    dsimp [label_difference, center_difference]
    linear_combination -shared - firstLabel * compatible
  let parameter := inverse * center_difference + complement * label_difference
  have parameter_label : modulus * parameter = label_difference := by
    dsimp [parameter]
    calc
      _ = inverse * (modulus * center_difference) +
          modulus * complement * label_difference := by ring
      _ = inverse * (secondCoefficient * label_difference) +
          modulus * complement * label_difference := by rw [← mixed]
      _ = (secondCoefficient * inverse + modulus * complement) *
          label_difference := by ring
      _ = label_difference := by rw [bezout, one_mul]
  have parameter_center : secondCoefficient * parameter =
      center_difference := by
    dsimp [parameter]
    calc
      _ = secondCoefficient * inverse * center_difference +
          complement * (secondCoefficient * label_difference) := by ring
      _ = secondCoefficient * inverse * center_difference +
          complement * (modulus * center_difference) := by rw [mixed]
      _ = (secondCoefficient * inverse + modulus * complement) *
          center_difference := by ring
      _ = center_difference := by rw [bezout, one_mul]
  refine ⟨parameter, ?_, ?_⟩
  · dsimp [label_difference] at parameter_label
    linear_combination -parameter_label
  · dsimp [center_difference] at parameter_center
    linear_combination parameter_center

/-- ACTUAL same-type shared-target selector in its three integral-fiber
coordinates.  BOTH genuine prime labels must be nonzero; their local residues
are NOT required to differ.  The two distinguished copies of the shared target
have the same value, so their duplicated nonzero condition does not create a
second distinct prime form. -/
noncomputable def adaptiveMixedSharedTargetLocalSelectors
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (multiplier correction : ℤ) [Fact ell.Prime] :
    Finset (ZMod ell × ZMod ell × ZMod ell) :=
  Finset.univ.filter fun triple =>
    let first_label := triple.1
    let first_center := triple.2.1
    let parameter := triple.2.2
    let modulus : ZMod ell :=
      adaptiveMixedActualCenterCoefficient support first.1 firstIndex
    let second_coefficient : ZMod ell :=
      adaptiveMixedActualLabelCoefficient support second.1 secondIndex
    let second_label :=
      (multiplier : ZMod ell) * first_label + modulus * parameter
    let second_center := first_center -
      (correction : ZMod ell) * first_label -
        second_coefficient * parameter
    first_label ≠ 0 ∧ second_label ≠ 0 ∧
      (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale first,
        adaptiveMixedActualAffineForm
          support first.1 index ell first_label first_center ≠ 0) ∧
      (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale second,
        adaptiveMixedActualAffineForm
          support second.1 index ell second_label second_center ≠ 0)

/-- Two genuine retained targets of the SAME actual type always satisfy the
honest integral shared-target congruence `a' c = a + B k`. -/
theorem adaptiveMixedSharedTarget_integer_compatibility
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (_first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex) :
    ∃ multiplier correction : ℤ,
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction := by
  have same_modulus :=
    adaptiveMixedActualCenterCoefficients_eq_of_same_type same_type
  have coprime :=
    adaptiveMixedActualLabelCenterCoefficients_coprime primes second_active
  rw [← same_modulus] at coprime
  exact sharedTargetUnit_integer_compatibility
    (adaptiveMixedActualLabelCoefficient support first.1 firstIndex)
    (adaptiveMixedActualLabelCoefficient support second.1 secondIndex)
    (adaptiveMixedActualCenterCoefficient support first.1 firstIndex)
    coprime

/-- Every two independently sampled actual outcomes with distinguished
retained targets of the SAME true type have an admissible genuine
THREE-COORDINATE shared-target system at EVERY prime.  This uses the actual
integral parameter fiber even at primes dividing `B`; no equality of outside
residues or local inequality between the two prime labels is imposed. -/
theorem adaptiveMixedSharedTargetLocalSelectors_nonempty
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
    (adaptiveMixedSharedTargetLocalSelectors
      support scale ell first second firstIndex secondIndex
        multiplier correction).Nonempty := by
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
  obtain ⟨first_label, first_center, first_unit, first_forms⟩ :=
    adaptiveMixedOutcome_all_prime_locally_admissible
      support scale first primes ell
  obtain ⟨other_label, other_center, other_unit, other_forms⟩ :=
    adaptiveMixedOutcome_all_prime_locally_admissible
      support scale second primes ell
  let first_target := adaptiveMixedActualAffineForm
    support first.1 firstIndex ell first_label first_center
  let other_target := adaptiveMixedActualAffineForm
    support second.1 secondIndex ell other_label other_center
  have first_target_unit : first_target ≠ 0 :=
    first_forms firstIndex first_active
  have other_target_unit : other_target ≠ 0 :=
    other_forms secondIndex second_active
  let scaling := first_target / other_target
  have scaling_unit : scaling ≠ 0 :=
    div_ne_zero first_target_unit other_target_unit
  let second_label := scaling * other_label
  let second_center := scaling * other_center
  have second_unit : second_label ≠ 0 :=
    mul_ne_zero scaling_unit other_unit
  have second_forms :
      ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale second,
        adaptiveMixedActualAffineForm
          support second.1 index ell second_label second_center ≠ 0 := by
    intro index active
    dsimp [second_label, second_center]
    rw [adaptiveMixedActualAffineForm_scale_both]
    exact mul_ne_zero scaling_unit (other_forms index active)
  have same_target :
      adaptiveMixedActualAffineForm
        support second.1 secondIndex ell second_label second_center =
      adaptiveMixedActualAffineForm
        support first.1 firstIndex ell first_label first_center := by
    change adaptiveMixedActualAffineForm
      support second.1 secondIndex ell
        (scaling * other_label) (scaling * other_center) = first_target
    rw [adaptiveMixedActualAffineForm_scale_both]
    change (first_target / other_target) * other_target = first_target
    exact div_mul_cancel₀ first_target other_target_unit
  have shared :
      (first_coefficient : ZMod ell) * first_label +
        (modulus : ZMod ell) * first_center =
      (second_coefficient : ZMod ell) * second_label +
        (modulus : ZMod ell) * second_center := by
    rw [adaptiveMixedActualAffineForm_eq_coefficients,
      adaptiveMixedActualAffineForm_eq_coefficients] at same_target
    dsimp [first_coefficient, second_coefficient, modulus]
    simpa [adaptiveMixedActualCenterCoefficients_eq_of_same_type same_type]
      using same_target.symm
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
  obtain ⟨parameter, labels, centers⟩ :=
    adaptiveMixedSharedTarget_field_parameter_of_equal_targets
      (first_coefficient : ZMod ell)
      (second_coefficient : ZMod ell)
      (modulus : ZMod ell)
      (multiplier : ZMod ell) (correction : ZMod ell)
      (inverse : ZMod ell) (complement : ZMod ell)
      first_label first_center second_label second_center
      compatible_field bezout_field shared
  refine ⟨(first_label, first_center, parameter), ?_⟩
  simp only [adaptiveMixedSharedTargetLocalSelectors,
    Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp
  change first_label ≠ 0 ∧
    ((multiplier : ZMod ell) * first_label +
      (modulus : ZMod ell) * parameter) ≠ 0 ∧
    (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale first,
      adaptiveMixedActualAffineForm
        support first.1 index ell first_label first_center ≠ 0) ∧
    (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale second,
      adaptiveMixedActualAffineForm support second.1 index ell
        ((multiplier : ZMod ell) * first_label +
          (modulus : ZMod ell) * parameter)
        (first_center - (correction : ZMod ell) * first_label -
          (second_coefficient : ZMod ell) * parameter) ≠ 0)
  rw [← labels, ← centers]
  exact ⟨first_unit, second_unit, first_forms, second_forms⟩

/-- Genuine shared-label form indices: the one first-branch label is retained,
all first physical targets are retained, and all second physical targets are
added WITHOUT duplicating the common prime label. -/
def adaptiveMixedSharedLabelFormIndices
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ) :
    Finset (Option ℕ ⊕ ℕ) :=
  (adaptiveMixedActualFormIndices support scale first).image Sum.inl ∪
    (adaptiveMixedOutcomeActiveIndices support scale second).image Sum.inr

/-- The exact shared-label rational coefficient vectors in the genuine
three signed coordinates `(P,C,C')`. -/
def adaptiveMixedSharedLabelFormVector
    (support : Finset ℕ) (firstCenter secondCenter : ℕ) :
    Option ℕ ⊕ ℕ → ℚ × ℚ × ℚ
  | Sum.inl none => (1, 0, 0)
  | Sum.inl (some index) =>
      ((adaptiveMixedActualLabelCoefficient support firstCenter index : ℚ),
       (adaptiveMixedActualCenterCoefficient support firstCenter index : ℚ), 0)
  | Sum.inr index =>
      ((adaptiveMixedActualLabelCoefficient support secondCenter index : ℚ),
       0, (adaptiveMixedActualCenterCoefficient support secondCenter index : ℚ))

/-- The whole first shared-label branch is its ACTUAL audited
two-coordinate system with one zero third coordinate. -/
theorem adaptiveMixedSharedLabelFormVector_inl
    (support : Finset ℕ) (firstCenter secondCenter : ℕ)
    (index : Option ℕ) :
    adaptiveMixedSharedLabelFormVector
      support firstCenter secondCenter (Sum.inl index) =
      ((adaptiveMixedActualFormVector support firstCenter index).1,
       (adaptiveMixedActualFormVector support firstCenter index).2, 0) := by
  cases index <;> rfl

/-- A first-branch shared-label index is present exactly when the original
first label-or-target form is genuinely present. -/
theorem adaptiveMixedSharedLabelFormIndices_inl_mem_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (index : Option ℕ) :
    Sum.inl index ∈ adaptiveMixedSharedLabelFormIndices
      support scale first second ↔
        index ∈ adaptiveMixedActualFormIndices support scale first := by
  simp [adaptiveMixedSharedLabelFormIndices]

/-- A second-branch shared-label index is present exactly when its true
physical mixed target was retained by the second outcome. -/
theorem adaptiveMixedSharedLabelFormIndices_inr_mem_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (index : ℕ) :
    Sum.inr index ∈ adaptiveMixedSharedLabelFormIndices
      support scale first second ↔
        index ∈ adaptiveMixedOutcomeActiveIndices support scale second := by
  simp [adaptiveMixedSharedLabelFormIndices]

/-- The ACTUAL shared-label system has no proportional rational form pairs.
It includes one shared label and both full genuine mixed target branches. -/
theorem adaptiveMixedSharedLabelFormVectors_pairwise_not_proportional
    {support : Finset ℕ} {scale : ℕ} {first second : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    {left right : Option ℕ ⊕ ℕ}
    (left_selected : left ∈ adaptiveMixedSharedLabelFormIndices
      support scale first second)
    (right_selected : right ∈ adaptiveMixedSharedLabelFormIndices
      support scale first second)
    (different : left ≠ right) :
    ¬ ∃ coefficient : ℚ,
      adaptiveMixedSharedLabelFormVector support first.1 second.1 left =
        coefficient •
          adaptiveMixedSharedLabelFormVector
            support first.1 second.1 right := by
  rintro ⟨coefficient, equal⟩
  have first_coordinate := congrArg Prod.fst equal
  have middle_coordinate := congrArg (fun vector => vector.2.1) equal
  have last_coordinate := congrArg (fun vector => vector.2.2) equal
  cases left with
  | inl left =>
      have left_actual :=
        (adaptiveMixedSharedLabelFormIndices_inl_mem_iff
          support scale first second left).mp left_selected
      cases right with
      | inl right =>
          have right_actual :=
            (adaptiveMixedSharedLabelFormIndices_inl_mem_iff
              support scale first second right).mp right_selected
          apply adaptiveMixedActualFormVectors_pairwise_not_proportional
            primes left_actual right_actual
              (fun same => different (congrArg Sum.inl same))
          refine ⟨coefficient, Prod.ext ?_ ?_⟩
          · simpa [adaptiveMixedSharedLabelFormVector_inl]
              using first_coordinate
          · simpa [adaptiveMixedSharedLabelFormVector_inl]
              using middle_coordinate
      | inr right =>
          have right_active :=
            (adaptiveMixedSharedLabelFormIndices_inr_mem_iff
              support scale first second right).mp right_selected
          have right_center_nonzero :
              (adaptiveMixedActualCenterCoefficient
                support second.1 right : ℚ) ≠ 0 := by
            exact_mod_cast (adaptiveMixedActualCenterCoefficient_pos
              primes right_active).ne'
          have coefficient_zero : coefficient = 0 := by
            have last :
                (0 : ℚ) = coefficient *
                  (adaptiveMixedActualCenterCoefficient
                    support second.1 right : ℚ) := by
              cases left <;>
                simpa only [adaptiveMixedSharedLabelFormVector, Prod.smul_fst,
                  Prod.smul_snd, smul_eq_mul, Prod.fst, Prod.snd]
                    using last_coordinate
            exact (mul_eq_zero.mp last.symm).resolve_right
              right_center_nonzero
          cases left with
          | none =>
              rw [coefficient_zero] at first_coordinate
              norm_num [adaptiveMixedSharedLabelFormVector]
                at first_coordinate
          | some left =>
              have left_active :=
                (adaptiveMixedActualFormIndices_target_mem_iff
                  support scale left first).mp left_actual
              have positive := adaptiveMixedActualCenterCoefficient_pos
                primes left_active
              have zero :
                  (adaptiveMixedActualCenterCoefficient
                    support first.1 left : ℚ) = 0 := by
                simpa [adaptiveMixedSharedLabelFormVector, coefficient_zero]
                  using middle_coordinate
              have integral :
                  adaptiveMixedActualCenterCoefficient
                    support first.1 left = 0 := by
                exact_mod_cast zero
              omega
  | inr left =>
      have left_active :=
        (adaptiveMixedSharedLabelFormIndices_inr_mem_iff
          support scale first second left).mp left_selected
      cases right with
      | inl right =>
          have positive := adaptiveMixedActualCenterCoefficient_pos
            primes left_active
          have zero :
              (adaptiveMixedActualCenterCoefficient
                support second.1 left : ℚ) = 0 := by
            cases right <;>
              simpa [adaptiveMixedSharedLabelFormVector]
                using last_coordinate
          have integral : adaptiveMixedActualCenterCoefficient
              support second.1 left = 0 := by
            exact_mod_cast zero
          omega
      | inr right =>
          have right_active :=
            (adaptiveMixedSharedLabelFormIndices_inr_mem_iff
              support scale first second right).mp right_selected
          apply adaptiveMixedActualTargetVectors_not_proportional
            primes left_active right_active
              (fun same => different (congrArg Sum.inr same))
          refine ⟨coefficient, Prod.ext ?_ ?_⟩
          · simpa [adaptiveMixedSharedLabelFormVector,
              adaptiveMixedActualFormVector] using first_coordinate
          · simpa [adaptiveMixedSharedLabelFormVector,
              adaptiveMixedActualFormVector] using last_coordinate

/-- Genuine shared-target form indices retain BOTH actual prime labels and all
first-branch targets, but erase the repeated second-branch distinguished target.
Consequently the shared prime target is counted EXACTLY ONCE. -/
def adaptiveMixedSharedTargetFormIndices
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (secondIndex : ℕ) : Finset (Option ℕ ⊕ Option ℕ) :=
  (adaptiveMixedActualFormIndices support scale first).image Sum.inl ∪
    ((adaptiveMixedActualFormIndices support scale second).erase
      (some secondIndex)).image Sum.inr

/-- The actual rational three-coordinate vectors on the genuine integral
shared-target fiber `(P,C,t)`, including BOTH real prime-label forms. -/
def adaptiveMixedSharedTargetFormVector
    (support : Finset ℕ) (firstCenter secondCenter firstIndex secondIndex : ℕ)
    (multiplier correction : ℤ) : Option ℕ ⊕ Option ℕ → ℚ × ℚ × ℚ
  | Sum.inl none => (1, 0, 0)
  | Sum.inl (some index) =>
      ((adaptiveMixedActualLabelCoefficient support firstCenter index : ℚ),
       (adaptiveMixedActualCenterCoefficient support firstCenter index : ℚ), 0)
  | Sum.inr none =>
      ((multiplier : ℚ), 0,
        (adaptiveMixedActualCenterCoefficient
          support firstCenter firstIndex : ℚ))
  | Sum.inr (some index) =>
      ((adaptiveMixedActualLabelCoefficient support secondCenter index : ℚ) *
          (multiplier : ℚ) -
        (adaptiveMixedActualCenterCoefficient support secondCenter index : ℚ) *
          (correction : ℚ),
       (adaptiveMixedActualCenterCoefficient support secondCenter index : ℚ),
       (adaptiveMixedActualLabelCoefficient support secondCenter index : ℚ) *
          (adaptiveMixedActualCenterCoefficient
            support firstCenter firstIndex : ℚ) -
        (adaptiveMixedActualCenterCoefficient support secondCenter index : ℚ) *
          (adaptiveMixedActualLabelCoefficient
            support secondCenter secondIndex : ℚ))

/-- First-branch shared-target membership preserves EVERY actual prime label
and retained physical mixed target. -/
theorem adaptiveMixedSharedTargetFormIndices_inl_mem_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (secondIndex : ℕ) (index : Option ℕ) :
    Sum.inl index ∈ adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex ↔
        index ∈ adaptiveMixedActualFormIndices support scale first := by
  simp [adaptiveMixedSharedTargetFormIndices]

/-- Second-branch shared-target membership keeps its genuine prime label and
every retained physical target EXCEPT the already-counted shared target. -/
theorem adaptiveMixedSharedTargetFormIndices_inr_mem_iff
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (secondIndex : ℕ) (index : Option ℕ) :
    Sum.inr index ∈ adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex ↔
        index ≠ some secondIndex ∧
          index ∈ adaptiveMixedActualFormIndices support scale second := by
  simp [adaptiveMixedSharedTargetFormIndices]

/-- First-branch shared-target vectors embed the actual audited
two-coordinate forms with zero fiber-parameter coefficient. -/
theorem adaptiveMixedSharedTargetFormVector_inl
    (support : Finset ℕ)
    (firstCenter secondCenter firstIndex secondIndex : ℕ)
    (multiplier correction : ℤ) (index : Option ℕ) :
    adaptiveMixedSharedTargetFormVector support firstCenter secondCenter
      firstIndex secondIndex multiplier correction (Sum.inl index) =
      ((adaptiveMixedActualFormVector support firstCenter index).1,
       (adaptiveMixedActualFormVector support firstCenter index).2, 0) := by
  cases index <;> rfl

/-- EVERY other second-branch physical target has a genuinely NONZERO
fiber-parameter coefficient.  The only possible duplicate with the first
branch is exactly the erased distinguished shared target. -/
theorem adaptiveMixedSharedTarget_other_parameter_coefficient_ne_zero
    {support : Finset ℕ} {scale firstIndex secondIndex otherIndex : ℕ}
    {first second : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (distinguished_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (other_active :
      otherIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (different : otherIndex ≠ secondIndex) :
    (adaptiveMixedActualLabelCoefficient support second.1 otherIndex : ℚ) *
        (adaptiveMixedActualCenterCoefficient
          support first.1 firstIndex : ℚ) -
      (adaptiveMixedActualCenterCoefficient
        support second.1 otherIndex : ℚ) *
        (adaptiveMixedActualLabelCoefficient
          support second.1 secondIndex : ℚ) ≠ 0 := by
  rw [adaptiveMixedActualCenterCoefficients_eq_of_same_type same_type]
  simpa [mul_comm] using
    adaptiveMixedActualCoefficients_rational_determinant_ne_zero
      primes other_active distinguished_active different

/-- The erased second distinguished form is EXACTLY the first distinguished
form as a rational form on the genuine three-coordinate integral fiber. -/
theorem adaptiveMixedSharedTarget_distinguished_vectors_eq
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
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
            support first.1 firstIndex : ℤ) * correction) :
    adaptiveMixedSharedTargetFormVector support first.1 second.1
      firstIndex secondIndex multiplier correction
        (Sum.inl (some firstIndex)) =
    adaptiveMixedSharedTargetFormVector support first.1 second.1
      firstIndex secondIndex multiplier correction
        (Sum.inr (some secondIndex)) := by
  have compatible_rat :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℚ) * (multiplier : ℚ) =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℚ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℚ) * (correction : ℚ) := by
    exact_mod_cast compatible
  have same_modulus :=
    adaptiveMixedActualCenterCoefficients_eq_of_same_type same_type
  change
    ((adaptiveMixedActualLabelCoefficient support first.1 firstIndex : ℚ),
      (adaptiveMixedActualCenterCoefficient support first.1 firstIndex : ℚ),
      (0 : ℚ)) =
    ((adaptiveMixedActualLabelCoefficient support second.1 secondIndex : ℚ) *
        (multiplier : ℚ) -
      (adaptiveMixedActualCenterCoefficient support second.1 secondIndex : ℚ) *
        (correction : ℚ),
      (adaptiveMixedActualCenterCoefficient support second.1 secondIndex : ℚ),
      (adaptiveMixedActualLabelCoefficient support second.1 secondIndex : ℚ) *
        (adaptiveMixedActualCenterCoefficient support first.1 firstIndex : ℚ) -
      (adaptiveMixedActualCenterCoefficient support second.1 secondIndex : ℚ) *
        (adaptiveMixedActualLabelCoefficient support second.1 secondIndex : ℚ))
  apply Prod.ext
  · change (adaptiveMixedActualLabelCoefficient
      support first.1 firstIndex : ℚ) = _
    rw [← same_modulus]
    linear_combination -compatible_rat
  · apply Prod.ext
    · change
        (adaptiveMixedActualCenterCoefficient
          support first.1 firstIndex : ℚ) =
          (adaptiveMixedActualCenterCoefficient
            support second.1 secondIndex : ℚ)
      exact_mod_cast same_modulus
    · change (0 : ℚ) = _
      rw [← same_modulus]
      ring

/-- The COMPLETE deduplicated same-type shared-target system has finite
complexity: every two DISTINCT genuine rational three-coordinate forms are
nonproportional, including both prime labels and both mixed branches. -/
theorem adaptiveMixedSharedTargetFormVectors_pairwise_not_proportional
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
    {left right : Option ℕ ⊕ Option ℕ}
    (left_selected : left ∈ adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex)
    (right_selected : right ∈ adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex)
    (different : left ≠ right) :
    ¬ ∃ coefficient : ℚ,
      adaptiveMixedSharedTargetFormVector support first.1 second.1
        firstIndex secondIndex multiplier correction left =
          coefficient •
            adaptiveMixedSharedTargetFormVector support first.1 second.1
              firstIndex secondIndex multiplier correction right := by
  rintro ⟨coefficient, equal⟩
  have first_coordinate := congrArg Prod.fst equal
  have middle_coordinate := congrArg (fun vector => vector.2.1) equal
  have last_coordinate := congrArg (fun vector => vector.2.2) equal
  have modulus_nonzero :
      (adaptiveMixedActualCenterCoefficient
        support first.1 firstIndex : ℚ) ≠ 0 := by
    exact_mod_cast (adaptiveMixedActualCenterCoefficient_pos
      primes first_active).ne'
  cases left with
  | inl left =>
      have left_actual :=
        (adaptiveMixedSharedTargetFormIndices_inl_mem_iff
          support scale first second secondIndex left).mp left_selected
      cases right with
      | inl right =>
          have right_actual :=
            (adaptiveMixedSharedTargetFormIndices_inl_mem_iff
              support scale first second secondIndex right).mp right_selected
          apply adaptiveMixedActualFormVectors_pairwise_not_proportional
            primes left_actual right_actual
              (fun same => different (congrArg Sum.inl same))
          refine ⟨coefficient, Prod.ext ?_ ?_⟩
          · simpa [adaptiveMixedSharedTargetFormVector_inl]
              using first_coordinate
          · simpa [adaptiveMixedSharedTargetFormVector_inl]
              using middle_coordinate
      | inr right =>
          obtain ⟨right_distinct, right_actual⟩ :=
            (adaptiveMixedSharedTargetFormIndices_inr_mem_iff
              support scale first second secondIndex right).mp right_selected
          cases left with
          | none =>
              cases right with
              | none =>
                  have last :
                      (0 : ℚ) = coefficient *
                        (adaptiveMixedActualCenterCoefficient
                          support first.1 firstIndex : ℚ) := by
                    simpa only [adaptiveMixedSharedTargetFormVector,
                      Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
                      Prod.fst, Prod.snd] using last_coordinate
                  have coefficient_zero : coefficient = 0 :=
                    (mul_eq_zero.mp last.symm).resolve_right modulus_nonzero
                  rw [coefficient_zero] at first_coordinate
                  norm_num [adaptiveMixedSharedTargetFormVector]
                    at first_coordinate
              | some right =>
                  have right_active :=
                    (adaptiveMixedActualFormIndices_target_mem_iff
                      support scale right second).mp right_actual
                  have right_center_nonzero :
                      (adaptiveMixedActualCenterCoefficient
                        support second.1 right : ℚ) ≠ 0 := by
                    exact_mod_cast
                      (adaptiveMixedActualCenterCoefficient_pos
                        primes right_active).ne'
                  have middle : (0 : ℚ) = coefficient *
                      (adaptiveMixedActualCenterCoefficient
                        support second.1 right : ℚ) := by
                    simpa only [adaptiveMixedSharedTargetFormVector,
                      Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
                      Prod.fst, Prod.snd] using middle_coordinate
                  have coefficient_zero : coefficient = 0 :=
                    (mul_eq_zero.mp middle.symm).resolve_right
                      right_center_nonzero
                  rw [coefficient_zero] at first_coordinate
                  norm_num [adaptiveMixedSharedTargetFormVector]
                    at first_coordinate
          | some left =>
              have left_active :=
                (adaptiveMixedActualFormIndices_target_mem_iff
                  support scale left first).mp left_actual
              have left_center_nonzero :
                  (adaptiveMixedActualCenterCoefficient
                    support first.1 left : ℚ) ≠ 0 := by
                exact_mod_cast
                  (adaptiveMixedActualCenterCoefficient_pos
                    primes left_active).ne'
              cases right with
              | none =>
                  apply left_center_nonzero
                  simpa [adaptiveMixedSharedTargetFormVector]
                    using middle_coordinate
              | some right =>
                  have right_active :=
                    (adaptiveMixedActualFormIndices_target_mem_iff
                      support scale right second).mp right_actual
                  have right_not_distinguished : right ≠ secondIndex := by
                    intro same
                    exact right_distinct (congrArg some same)
                  have right_parameter_nonzero :=
                    adaptiveMixedSharedTarget_other_parameter_coefficient_ne_zero
                      primes second_active right_active same_type
                        right_not_distinguished
                  have last : (0 : ℚ) = coefficient *
                      ((adaptiveMixedActualLabelCoefficient
                          support second.1 right : ℚ) *
                        (adaptiveMixedActualCenterCoefficient
                          support first.1 firstIndex : ℚ) -
                      (adaptiveMixedActualCenterCoefficient
                          support second.1 right : ℚ) *
                        (adaptiveMixedActualLabelCoefficient
                          support second.1 secondIndex : ℚ)) := by
                    simpa only [adaptiveMixedSharedTargetFormVector,
                      Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
                      Prod.fst, Prod.snd] using last_coordinate
                  have coefficient_zero : coefficient = 0 :=
                    (mul_eq_zero.mp last.symm).resolve_right
                      right_parameter_nonzero
                  apply left_center_nonzero
                  simpa [adaptiveMixedSharedTargetFormVector, coefficient_zero]
                    using middle_coordinate
  | inr left =>
      obtain ⟨left_distinct, left_actual⟩ :=
        (adaptiveMixedSharedTargetFormIndices_inr_mem_iff
          support scale first second secondIndex left).mp left_selected
      cases right with
      | inl right =>
          cases left with
          | none =>
              apply modulus_nonzero
              cases right <;>
                simpa [adaptiveMixedSharedTargetFormVector]
                  using last_coordinate
          | some left =>
              have left_active :=
                (adaptiveMixedActualFormIndices_target_mem_iff
                  support scale left second).mp left_actual
              cases right with
              | none =>
                  have nonzero :
                      (adaptiveMixedActualCenterCoefficient
                        support second.1 left : ℚ) ≠ 0 := by
                    exact_mod_cast
                      (adaptiveMixedActualCenterCoefficient_pos
                        primes left_active).ne'
                  apply nonzero
                  simpa [adaptiveMixedSharedTargetFormVector]
                    using middle_coordinate
              | some right =>
                  have left_not_distinguished : left ≠ secondIndex := by
                    intro same
                    exact left_distinct (congrArg some same)
                  have nonzero :=
                    adaptiveMixedSharedTarget_other_parameter_coefficient_ne_zero
                      primes second_active left_active same_type
                        left_not_distinguished
                  apply nonzero
                  simpa [adaptiveMixedSharedTargetFormVector]
                    using last_coordinate
      | inr right =>
          obtain ⟨right_distinct, right_actual⟩ :=
            (adaptiveMixedSharedTargetFormIndices_inr_mem_iff
              support scale first second secondIndex right).mp right_selected
          cases left with
          | none =>
              cases right with
              | none => exact different rfl
              | some right =>
                  have right_active :=
                    (adaptiveMixedActualFormIndices_target_mem_iff
                      support scale right second).mp right_actual
                  have right_center_nonzero :
                      (adaptiveMixedActualCenterCoefficient
                        support second.1 right : ℚ) ≠ 0 := by
                    exact_mod_cast
                      (adaptiveMixedActualCenterCoefficient_pos
                        primes right_active).ne'
                  have middle : (0 : ℚ) = coefficient *
                      (adaptiveMixedActualCenterCoefficient
                        support second.1 right : ℚ) := by
                    simpa only [adaptiveMixedSharedTargetFormVector,
                      Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
                      Prod.fst, Prod.snd] using middle_coordinate
                  have coefficient_zero : coefficient = 0 :=
                    (mul_eq_zero.mp middle.symm).resolve_right
                      right_center_nonzero
                  apply modulus_nonzero
                  simpa [adaptiveMixedSharedTargetFormVector, coefficient_zero]
                    using last_coordinate
          | some left =>
              have left_active :=
                (adaptiveMixedActualFormIndices_target_mem_iff
                  support scale left second).mp left_actual
              cases right with
              | none =>
                  have left_center_nonzero :
                      (adaptiveMixedActualCenterCoefficient
                        support second.1 left : ℚ) ≠ 0 := by
                    exact_mod_cast
                      (adaptiveMixedActualCenterCoefficient_pos
                        primes left_active).ne'
                  apply left_center_nonzero
                  simpa [adaptiveMixedSharedTargetFormVector]
                    using middle_coordinate
              | some right =>
                  have right_active :=
                    (adaptiveMixedActualFormIndices_target_mem_iff
                      support scale right second).mp right_actual
                  have middle :
                      (adaptiveMixedActualCenterCoefficient
                        support second.1 left : ℚ) =
                        coefficient *
                          (adaptiveMixedActualCenterCoefficient
                            support second.1 right : ℚ) := by
                    simpa only [adaptiveMixedSharedTargetFormVector,
                      Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
                      Prod.fst, Prod.snd] using middle_coordinate
                  have last :
                      (adaptiveMixedActualLabelCoefficient
                          support second.1 left : ℚ) *
                        (adaptiveMixedActualCenterCoefficient
                          support first.1 firstIndex : ℚ) -
                      (adaptiveMixedActualCenterCoefficient
                          support second.1 left : ℚ) *
                        (adaptiveMixedActualLabelCoefficient
                          support second.1 secondIndex : ℚ) =
                        coefficient *
                          ((adaptiveMixedActualLabelCoefficient
                              support second.1 right : ℚ) *
                            (adaptiveMixedActualCenterCoefficient
                              support first.1 firstIndex : ℚ) -
                          (adaptiveMixedActualCenterCoefficient
                              support second.1 right : ℚ) *
                            (adaptiveMixedActualLabelCoefficient
                              support second.1 secondIndex : ℚ)) := by
                    simpa only [adaptiveMixedSharedTargetFormVector,
                      Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
                      Prod.fst, Prod.snd] using last_coordinate
                  have label :
                      (adaptiveMixedActualLabelCoefficient
                        support second.1 left : ℚ) =
                      coefficient *
                        (adaptiveMixedActualLabelCoefficient
                          support second.1 right : ℚ) := by
                    apply mul_right_cancel₀ modulus_nonzero
                    linear_combination last +
                      (adaptiveMixedActualLabelCoefficient
                        support second.1 secondIndex : ℚ) * middle
                  apply adaptiveMixedActualTargetVectors_not_proportional
                    primes left_active right_active
                      (fun same => different
                        (congrArg (fun value =>
                          Sum.inr (some value)) same))
                  refine ⟨coefficient, Prod.ext ?_ ?_⟩
                  · exact label
                  · exact middle

/-- The honest standard Cauchy--Schwarz partition condition for arbitrary
ACTUAL rational three-coordinate affine systems. -/
def AdaptiveMixedThreeCoordinateHasCSComplexityAtMost
    {ι : Type*} [DecidableEq ι]
    (forms : Finset ι) (vectors : ι → ℚ × ℚ × ℚ)
    (complexity : ℕ) : Prop :=
  ∀ distinguished ∈ forms,
    ∃ classes : Finset (Finset ι),
      classes.card ≤ complexity + 1 ∧
      classes.biUnion id = forms.erase distinguished ∧
      (∀ block ∈ classes, block.Nonempty) ∧
      (∀ first ∈ classes, ∀ second ∈ classes,
        first ≠ second → Disjoint first second) ∧
      (∀ block ∈ classes,
        vectors distinguished ∉
          Submodule.span ℚ
            (↑(block.image vectors) : Set (ℚ × ℚ × ℚ)))

/-- Pairwise rational nonproportionality gives an EXPLICIT genuine singleton
partition proving finite Cauchy--Schwarz complexity at most `#forms-2`. -/
theorem adaptiveMixedThreeCoordinate_csComplexity_of_pairwise
    {ι : Type*} [DecidableEq ι]
    (forms : Finset ι) (vectors : ι → ℚ × ℚ × ℚ)
    (pairwise : ∀ first ∈ forms, ∀ second ∈ forms,
      first ≠ second →
        ¬ ∃ coefficient : ℚ, vectors first = coefficient • vectors second) :
    AdaptiveMixedThreeCoordinateHasCSComplexityAtMost
      forms vectors (forms.card - 2) := by
  classical
  intro distinguished selected
  let classes : Finset (Finset ι) :=
    (forms.erase distinguished).image fun other => ({other} : Finset ι)
  refine ⟨classes, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [classes]
    rw [Finset.card_image_iff.mpr
      (fun first _ second _ equal => Finset.singleton_inj.mp equal),
      Finset.card_erase_of_mem selected]
    have positive := Finset.card_pos.mpr ⟨distinguished, selected⟩
    omega
  · ext index
    simp [classes]
  · intro block member
    obtain ⟨other, _actual, rfl⟩ := Finset.mem_image.mp member
    exact Finset.singleton_nonempty other
  · intro first first_selected second second_selected different
    obtain ⟨first_index, _first_actual, rfl⟩ :=
      Finset.mem_image.mp first_selected
    obtain ⟨second_index, _second_actual, rfl⟩ :=
      Finset.mem_image.mp second_selected
    have distinct : first_index ≠ second_index := by
      intro same
      exact different (congrArg (fun index => ({index} : Finset ι)) same)
    apply Finset.disjoint_left.mpr
    intro index first_member second_member
    exact distinct
      ((Finset.mem_singleton.mp first_member).symm.trans
        (Finset.mem_singleton.mp second_member))
  · intro block member
    obtain ⟨other, other_member, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨different, other_actual⟩ := Finset.mem_erase.mp other_member
    intro dependent
    have singleton :
        vectors distinguished ∈
          Submodule.span ℚ ({vectors other} : Set (ℚ × ℚ × ℚ)) := by
      simpa using dependent
    obtain ⟨coefficient, equal⟩ :=
      Submodule.mem_span_singleton.mp singleton
    exact pairwise distinguished selected other other_actual different.symm
      ⟨coefficient, equal.symm⟩

/-- EXACT number of distinct shared-label forms: one genuine common prime
label plus both FULL actual retained physical target patterns. -/
theorem adaptiveMixedSharedLabelFormIndices_card
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ) :
    (adaptiveMixedSharedLabelFormIndices
      support scale first second).card =
        (adaptiveMixedOutcomeActiveIndices support scale first).card +
          (adaptiveMixedOutcomeActiveIndices support scale second).card + 1 := by
  have disjoint :
      Disjoint
        ((adaptiveMixedActualFormIndices support scale first).image Sum.inl)
        ((adaptiveMixedOutcomeActiveIndices
          support scale second).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro index first_member second_member
    obtain ⟨first_index, _first, first_equal⟩ :=
      Finset.mem_image.mp first_member
    obtain ⟨second_index, _second, second_equal⟩ :=
      Finset.mem_image.mp second_member
    cases first_equal.trans second_equal.symm
  unfold adaptiveMixedSharedLabelFormIndices
  rw [Finset.card_union_of_disjoint disjoint,
    Finset.card_image_iff.mpr
      (fun first _ second _ equal => Sum.inl.inj equal),
    Finset.card_image_iff.mpr
      (fun first _ second _ equal => Sum.inr.inj equal),
    adaptiveMixedActualFormIndices_card]
  omega

/-- EXACT number of distinct shared-target forms: BOTH actual prime labels,
all branch targets, and the shared distinguished target counted ONCE. -/
theorem adaptiveMixedSharedTargetFormIndices_card
    {support : Finset ℕ} {scale secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second) :
    (adaptiveMixedSharedTargetFormIndices
      support scale first second secondIndex).card =
        (adaptiveMixedOutcomeActiveIndices support scale first).card +
          (adaptiveMixedOutcomeActiveIndices support scale second).card + 1 := by
  have disjoint :
      Disjoint
        ((adaptiveMixedActualFormIndices support scale first).image Sum.inl)
        (((adaptiveMixedActualFormIndices support scale second).erase
          (some secondIndex)).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro index first_member second_member
    obtain ⟨first_index, _first, first_equal⟩ :=
      Finset.mem_image.mp first_member
    obtain ⟨second_index, _second, second_equal⟩ :=
      Finset.mem_image.mp second_member
    cases first_equal.trans second_equal.symm
  have distinguished_member :
      some secondIndex ∈ adaptiveMixedActualFormIndices
        support scale second :=
    (adaptiveMixedActualFormIndices_target_mem_iff
      support scale secondIndex second).mpr second_active
  unfold adaptiveMixedSharedTargetFormIndices
  rw [Finset.card_union_of_disjoint disjoint,
    Finset.card_image_iff.mpr
      (fun first _ second _ equal => Sum.inl.inj equal),
    Finset.card_image_iff.mpr
      (fun first _ second _ equal => Sum.inr.inj equal),
    Finset.card_erase_of_mem distinguished_member,
    adaptiveMixedActualFormIndices_card,
    adaptiveMixedActualFormIndices_card]
  omega

/-- EXPLICIT finite Cauchy--Schwarz certificate for the COMPLETE actual
shared-label three-coordinate prime system, with its one label deduplicated. -/
theorem adaptiveMixedSharedLabelForms_csComplexity_le_combined_rank_sub_one
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    AdaptiveMixedThreeCoordinateHasCSComplexityAtMost
      (adaptiveMixedSharedLabelFormIndices support scale first second)
      (adaptiveMixedSharedLabelFormVector support first.1 second.1)
      ((adaptiveMixedOutcomeActiveIndices support scale first).card +
        (adaptiveMixedOutcomeActiveIndices support scale second).card - 1) := by
  have bound :
      (adaptiveMixedSharedLabelFormIndices
        support scale first second).card - 2 =
          (adaptiveMixedOutcomeActiveIndices support scale first).card +
            (adaptiveMixedOutcomeActiveIndices support scale second).card - 1 := by
    rw [adaptiveMixedSharedLabelFormIndices_card]
    omega
  rw [← bound]
  apply adaptiveMixedThreeCoordinate_csComplexity_of_pairwise
  intro left left_selected right right_selected different
  exact adaptiveMixedSharedLabelFormVectors_pairwise_not_proportional
    primes left_selected right_selected different

/-- EXPLICIT finite Cauchy--Schwarz certificate for the COMPLETE genuine
same-type shared-target THREE-coordinate prime system, with BOTH labels and
exactly ONE distinguished common target. -/
theorem adaptiveMixedSharedTargetForms_csComplexity_le_combined_rank_sub_one
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
    (multiplier correction : ℤ) :
    AdaptiveMixedThreeCoordinateHasCSComplexityAtMost
      (adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex)
      (adaptiveMixedSharedTargetFormVector support first.1 second.1
        firstIndex secondIndex multiplier correction)
      ((adaptiveMixedOutcomeActiveIndices support scale first).card +
        (adaptiveMixedOutcomeActiveIndices support scale second).card - 1) := by
  have bound :
      (adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex).card - 2 =
          (adaptiveMixedOutcomeActiveIndices support scale first).card +
            (adaptiveMixedOutcomeActiveIndices support scale second).card - 1 := by
    rw [adaptiveMixedSharedTargetFormIndices_card second_active]
    omega
  rw [← bound]
  apply adaptiveMixedThreeCoordinate_csComplexity_of_pairwise
  intro left left_selected right right_selected different
  exact adaptiveMixedSharedTargetFormVectors_pairwise_not_proportional
    primes first_active second_active same_type multiplier correction
      left_selected right_selected different

end Erdos1139

