module

public import AdaptiveMixedPatternDistribution1139
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section


/-!
# Exact mixed-pattern shared-target fibers and their true covolume

Two same-type prime-pattern branches share a target when

    q = a P + B C = a' P' + B C'.

If `a'` is a unit modulo the positive modulus `B`, choose integer
coefficients `c,k` with `a' c = a + B k`.  Every genuine integral solution
is uniquely parametrized by

    P' = c P + B t,
    C' = C - k P - a' t.

The ORIGINAL equality is one constraint on four integer coordinates.  The
factor `B²` arises only after passing to the THREE physical coordinates
`(q,P,P')`: they obey the TWO independent congruences

    q ≡ aP (mod B),     P' ≡ cP (mod B).

Their actual integer parameter matrix has determinant `-B²`, and their
periodic finite-residue quotient has cardinality exactly `B²`.

This file proves only exact algebra, finite fibers, and local selectors.
It assumes no global prime-pattern asymptotic and does not solve #1139.
-/

open Finset
open scoped BigOperators Matrix

namespace Erdos1139

/-- The exact integer Bézout certificate for an actual natural coefficient
coprime to its true positive shared-target modulus. -/
theorem sharedTargetUnit_integer_bezout
    (coefficient modulus : ℕ)
    (coprime : Nat.Coprime coefficient modulus) :
    ∃ first second : ℤ,
      (coefficient : ℤ) * first + (modulus : ℤ) * second = 1 := by
  refine ⟨Nat.gcdA coefficient modulus, Nat.gcdB coefficient modulus, ?_⟩
  simpa [coprime] using (Nat.gcd_eq_gcd_ab coefficient modulus).symm

/-- A coprime second-branch coefficient gives genuine INTEGER `c,k` with
`a' c = a + B k`; there is no assumed rational inverse or divided lattice. -/
theorem sharedTargetUnit_integer_compatibility
    (firstCoefficient secondCoefficient modulus : ℕ)
    (coprime : Nat.Coprime secondCoefficient modulus) :
    ∃ multiplier correction : ℤ,
      (secondCoefficient : ℤ) * multiplier =
        (firstCoefficient : ℤ) + (modulus : ℤ) * correction := by
  obtain ⟨inverse, complement, bezout⟩ :=
    sharedTargetUnit_integer_bezout secondCoefficient modulus coprime
  refine ⟨(firstCoefficient : ℤ) * inverse,
    -(firstCoefficient : ℤ) * complement, ?_⟩
  linear_combination (firstCoefficient : ℤ) * bezout

/-- The exact original shared-target equality in its four ACTUAL integer
branch coordinates. -/
def SharedTargetIntegerEquation
    (firstCoefficient secondCoefficient modulus : ℤ)
    (firstLabel firstCenter secondLabel secondCenter : ℤ) : Prop :=
  firstCoefficient * firstLabel + modulus * firstCenter =
    secondCoefficient * secondLabel + modulus * secondCenter

/-- The displayed integer parametrization ALWAYS produces an actual
shared-target solution when its genuine Bézout compatibility is retained. -/
theorem sharedTargetIntegerEquation_of_parameter
    {firstCoefficient secondCoefficient modulus multiplier correction : ℤ}
    (compatible : secondCoefficient * multiplier =
      firstCoefficient + modulus * correction)
    (firstLabel firstCenter parameter : ℤ) :
    SharedTargetIntegerEquation firstCoefficient secondCoefficient modulus
      firstLabel firstCenter
      (multiplier * firstLabel + modulus * parameter)
      (firstCenter - correction * firstLabel -
        secondCoefficient * parameter) := by
  unfold SharedTargetIntegerEquation
  linear_combination -firstLabel * compatible

/-- The exact forced modulus divisibility.  It is the SECOND physical
congruence and follows from both the shared-target equality and a genuine
unit certificate for the second-branch coefficient. -/
theorem sharedTargetIntegerEquation_label_difference_dvd
    {firstCoefficient secondCoefficient modulus multiplier correction : ℤ}
    (compatible : secondCoefficient * multiplier =
      firstCoefficient + modulus * correction)
    (unit_certificate : ∃ inverse complement : ℤ,
      secondCoefficient * inverse + modulus * complement = 1)
    {firstLabel firstCenter secondLabel secondCenter : ℤ}
    (shared : SharedTargetIntegerEquation
      firstCoefficient secondCoefficient modulus
      firstLabel firstCenter secondLabel secondCenter) :
    modulus ∣ secondLabel - multiplier * firstLabel := by
  unfold SharedTargetIntegerEquation at shared
  have multiplied :
      secondCoefficient * (secondLabel - multiplier * firstLabel) =
        modulus *
          (firstCenter - secondCenter - correction * firstLabel) := by
    linear_combination -shared - firstLabel * compatible
  obtain ⟨inverse, complement, bezout⟩ := unit_certificate
  refine ⟨inverse *
      (firstCenter - secondCenter - correction * firstLabel) +
        complement * (secondLabel - multiplier * firstLabel), ?_⟩
  calc
    secondLabel - multiplier * firstLabel =
        (secondCoefficient * inverse + modulus * complement) *
          (secondLabel - multiplier * firstLabel) := by rw [bezout, one_mul]
    _ = inverse *
          (secondCoefficient *
            (secondLabel - multiplier * firstLabel)) +
        modulus *
          (complement * (secondLabel - multiplier * firstLabel)) := by ring
    _ = inverse *
          (modulus *
            (firstCenter - secondCenter - correction * firstLabel)) +
        modulus *
          (complement * (secondLabel - multiplier * firstLabel)) := by
            rw [multiplied]
    _ = modulus *
          (inverse *
            (firstCenter - secondCenter - correction * firstLabel) +
              complement * (secondLabel - multiplier * firstLabel)) := by
            ring

/-- Every actual shared-target solution has the advertised integer fiber
parameter; both branch centers and BOTH genuine coefficients are retained. -/
theorem sharedTargetIntegerEquation_exists_parameter
    {firstCoefficient secondCoefficient modulus multiplier correction : ℤ}
    (nonzero : modulus ≠ 0)
    (compatible : secondCoefficient * multiplier =
      firstCoefficient + modulus * correction)
    (unit_certificate : ∃ inverse complement : ℤ,
      secondCoefficient * inverse + modulus * complement = 1)
    {firstLabel firstCenter secondLabel secondCenter : ℤ}
    (shared : SharedTargetIntegerEquation
      firstCoefficient secondCoefficient modulus
      firstLabel firstCenter secondLabel secondCenter) :
    ∃ parameter : ℤ,
      secondLabel = multiplier * firstLabel + modulus * parameter ∧
        secondCenter = firstCenter - correction * firstLabel -
          secondCoefficient * parameter := by
  obtain ⟨parameter, divisible⟩ :=
    sharedTargetIntegerEquation_label_difference_dvd
      compatible unit_certificate shared
  have second_label :
      secondLabel = multiplier * firstLabel + modulus * parameter := by
    linarith
  refine ⟨parameter, second_label, ?_⟩
  unfold SharedTargetIntegerEquation at shared
  rw [second_label] at shared
  have center_multiple :
      modulus * secondCenter =
        modulus *
          (firstCenter - correction * firstLabel -
            secondCoefficient * parameter) := by
    linear_combination -shared - firstLabel * compatible
  exact mul_left_cancel₀ nonzero center_multiple

/-- EXACT unique integer fiber parameter.  Its uniqueness uses the actual
nonzero modulus; no hidden division by a possibly zero parameter occurs. -/
theorem sharedTargetIntegerEquation_exists_unique_parameter
    {firstCoefficient secondCoefficient modulus multiplier correction : ℤ}
    (nonzero : modulus ≠ 0)
    (compatible : secondCoefficient * multiplier =
      firstCoefficient + modulus * correction)
    (unit_certificate : ∃ inverse complement : ℤ,
      secondCoefficient * inverse + modulus * complement = 1)
    {firstLabel firstCenter secondLabel secondCenter : ℤ}
    (shared : SharedTargetIntegerEquation
      firstCoefficient secondCoefficient modulus
      firstLabel firstCenter secondLabel secondCenter) :
    ∃! parameter : ℤ,
      secondLabel = multiplier * firstLabel + modulus * parameter ∧
        secondCenter = firstCenter - correction * firstLabel -
          secondCoefficient * parameter := by
  obtain ⟨parameter, labels, centers⟩ :=
    sharedTargetIntegerEquation_exists_parameter
      nonzero compatible unit_certificate shared
  refine ⟨parameter, ⟨labels, centers⟩, ?_⟩
  intro other other_data
  apply mul_left_cancel₀ nonzero
  linarith [labels, other_data.1]

/-- Equivalence in BOTH directions: the genuine four-coordinate equality
holds exactly when there is one unique integral shared-target parameter. -/
theorem sharedTargetIntegerEquation_iff_unique_parameter
    {firstCoefficient secondCoefficient modulus multiplier correction : ℤ}
    (nonzero : modulus ≠ 0)
    (compatible : secondCoefficient * multiplier =
      firstCoefficient + modulus * correction)
    (unit_certificate : ∃ inverse complement : ℤ,
      secondCoefficient * inverse + modulus * complement = 1)
    (firstLabel firstCenter secondLabel secondCenter : ℤ) :
    SharedTargetIntegerEquation
      firstCoefficient secondCoefficient modulus
      firstLabel firstCenter secondLabel secondCenter ↔
        ∃! parameter : ℤ,
          secondLabel = multiplier * firstLabel + modulus * parameter ∧
            secondCenter = firstCenter - correction * firstLabel -
              secondCoefficient * parameter := by
  constructor
  · exact sharedTargetIntegerEquation_exists_unique_parameter
      nonzero compatible unit_certificate
  · rintro ⟨parameter, ⟨labels, centers⟩, _⟩
    rw [labels, centers]
    exact sharedTargetIntegerEquation_of_parameter
      compatible firstLabel firstCenter parameter

/-- The actual THREE physical coordinates obey TWO independently derived
modulus constraints: the target/first-label relation and the
first-label/second-label relation. -/
def SharedTargetPhysicalConstraints
    (firstCoefficient modulus multiplier : ℤ)
    (target firstLabel secondLabel : ℤ) : Prop :=
  modulus ∣ target - firstCoefficient * firstLabel ∧
    modulus ∣ secondLabel - multiplier * firstLabel

/-- Both physical congruences are exactly the image of integer parameters
`(P,C,t)`; this statement does not require the modulus to be nonzero. -/
theorem sharedTargetPhysicalConstraints_iff_parameters
    (firstCoefficient modulus multiplier target firstLabel secondLabel : ℤ) :
    SharedTargetPhysicalConstraints firstCoefficient modulus multiplier
      target firstLabel secondLabel ↔
      ∃ firstCenter parameter : ℤ,
        target = firstCoefficient * firstLabel + modulus * firstCenter ∧
          secondLabel = multiplier * firstLabel + modulus * parameter := by
  constructor
  · rintro ⟨⟨firstCenter, first_multiple⟩,
      ⟨parameter, second_multiple⟩⟩
    refine ⟨firstCenter, parameter, ?_, ?_⟩ <;> linarith
  · rintro ⟨firstCenter, parameter, target_eq, second_eq⟩
    constructor
    · refine ⟨firstCenter, ?_⟩
      linarith
    · refine ⟨parameter, ?_⟩
      linarith

/-- Exact equivalence between a physically realizable common target and
its TWO genuine congruence constraints.  The full second branch and its
true coefficient are reconstructed, not discarded. -/
theorem sharedTargetPhysicalConstraints_iff_shared_target
    {firstCoefficient secondCoefficient modulus multiplier correction : ℤ}
    (compatible : secondCoefficient * multiplier =
      firstCoefficient + modulus * correction)
    (unit_certificate : ∃ inverse complement : ℤ,
      secondCoefficient * inverse + modulus * complement = 1)
    (target firstLabel secondLabel : ℤ) :
    SharedTargetPhysicalConstraints firstCoefficient modulus multiplier
      target firstLabel secondLabel ↔
      ∃ firstCenter secondCenter : ℤ,
        target = firstCoefficient * firstLabel + modulus * firstCenter ∧
          target = secondCoefficient * secondLabel + modulus * secondCenter := by
  constructor
  · intro constrained
    obtain ⟨firstCenter, parameter, target_eq, label_eq⟩ :=
      (sharedTargetPhysicalConstraints_iff_parameters
        firstCoefficient modulus multiplier
        target firstLabel secondLabel).mp constrained
    refine ⟨firstCenter,
      firstCenter - correction * firstLabel -
        secondCoefficient * parameter,
      target_eq, ?_⟩
    rw [label_eq, target_eq]
    exact sharedTargetIntegerEquation_of_parameter
      compatible firstLabel firstCenter parameter
  · rintro ⟨firstCenter, secondCenter, first_eq, second_eq⟩
    constructor
    · refine ⟨firstCenter, ?_⟩
      linarith
    · apply sharedTargetIntegerEquation_label_difference_dvd
        (firstCenter := firstCenter) (secondCenter := secondCenter)
        compatible unit_certificate
      unfold SharedTargetIntegerEquation
      linarith

/-- The genuine integral map from `(P,C,t)` to physical coordinates
`(q,P,P')`.  Its two modulus-scaled columns are exactly where `B²` comes
from; it is NOT the determinant of the single four-variable equality. -/
def sharedTargetPhysicalParameterMatrix
    (firstCoefficient modulus multiplier : ℤ) :
      Matrix (Fin 3) (Fin 3) ℤ :=
  !![firstCoefficient, modulus, 0;
     1, 0, 0;
     multiplier, 0, modulus]

/-- Exact physical Jacobian: the true integral parameter matrix has
determinant `-B²`, independently of both branch coefficients. -/
theorem sharedTargetPhysicalParameterMatrix_det
    (firstCoefficient modulus multiplier : ℤ) :
    (sharedTargetPhysicalParameterMatrix
      firstCoefficient modulus multiplier).det = -(modulus ^ 2) := by
  rw [Matrix.det_fin_three]
  simp [sharedTargetPhysicalParameterMatrix]
  ring

/-- Nonzero positive modulus makes the actual physical Jacobian nonzero;
the three genuine physical coordinates do not collapse in dimension. -/
theorem sharedTargetPhysicalParameterMatrix_det_ne_zero
    (firstCoefficient modulus multiplier : ℤ)
    (nonzero : modulus ≠ 0) :
    (sharedTargetPhysicalParameterMatrix
      firstCoefficient modulus multiplier).det ≠ 0 := by
  rw [sharedTargetPhysicalParameterMatrix_det]
  exact neg_ne_zero.mpr (pow_ne_zero _ nonzero)

/-- Every ordered pair of target/second-label congruence errors defines
one genuine physical residue fiber modulo the ACTUAL positive modulus. -/
def sharedTargetPhysicalResidueFiber
    (modulus : ℕ) [NeZero modulus]
    (firstCoefficient multiplier firstError secondError : ZMod modulus) :
      Finset (ZMod modulus × ZMod modulus × ZMod modulus) :=
  Finset.univ.filter fun point =>
    point.1 - firstCoefficient * point.2.1 = firstError ∧
      point.2.2 - multiplier * point.2.1 = secondError

/-- EVERY pair of genuine physical residue errors has exactly `B` lifts:
the first prime-label residue is freely chosen and determines both other
physical coordinates uniquely. -/
theorem sharedTargetPhysicalResidueFiber_card
    (modulus : ℕ) [NeZero modulus]
    (firstCoefficient multiplier firstError secondError : ZMod modulus) :
    (sharedTargetPhysicalResidueFiber modulus firstCoefficient multiplier
      firstError secondError).card = modulus := by
  classical
  let parameterize : ZMod modulus →
      ZMod modulus × ZMod modulus × ZMod modulus :=
    fun firstLabel =>
      (firstError + firstCoefficient * firstLabel,
        firstLabel,
        secondError + multiplier * firstLabel)
  have exact_image :
      sharedTargetPhysicalResidueFiber modulus firstCoefficient multiplier
        firstError secondError =
      (Finset.univ : Finset (ZMod modulus)).image parameterize := by
    ext point
    constructor
    · intro selected
      obtain ⟨_, first_eq, second_eq⟩ := Finset.mem_filter.mp selected
      refine Finset.mem_image.mpr
        ⟨point.2.1, Finset.mem_univ _, ?_⟩
      dsimp [parameterize]
      apply Prod.ext
      · exact (sub_eq_iff_eq_add.mp first_eq).symm
      · apply Prod.ext
        · rfl
        · exact (sub_eq_iff_eq_add.mp second_eq).symm
    · intro selected
      obtain ⟨firstLabel, _, equal⟩ := Finset.mem_image.mp selected
      subst point
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · dsimp [parameterize]
        ring
      · dsimp [parameterize]
        ring
  rw [exact_image, Finset.card_image_of_injective]
  · simp
  · intro first second equal
    exact congrArg (fun point : ZMod modulus × ZMod modulus × ZMod modulus =>
      point.2.1) equal

/-- The TWO independent physical congruence errors form a quotient with
exactly `B²` residue classes, proving the manuscript's index without
mistaking the original four-coordinate equality for two constraints. -/
theorem sharedTargetPhysicalCongruence_quotient_card
    (modulus : ℕ) [NeZero modulus] :
    Fintype.card (ZMod modulus × ZMod modulus) = modulus ^ 2 := by
  simp [Fintype.card_prod, pow_two]

/-- Exact physical fundamental-period identity: the full `B³` physical
residue box is `B²` genuine congruence classes, each with `B` actual
first-label lifts.  This is the honest covolume/index `B²`. -/
theorem sharedTargetPhysicalCongruence_period_index
    (modulus : ℕ) [NeZero modulus]
    (firstCoefficient multiplier firstError secondError : ZMod modulus) :
    Fintype.card (ZMod modulus × ZMod modulus × ZMod modulus) =
      modulus ^ 2 *
        (sharedTargetPhysicalResidueFiber modulus firstCoefficient multiplier
          firstError secondError).card := by
  rw [sharedTargetPhysicalResidueFiber_card]
  simp [Fintype.card_prod, pow_two]
  ring

/-- In the ORIGINAL four branch coordinates modulo `B`, the displayed
shared-target equality is only ONE congruence: the two modulus-scaled
center terms vanish and the remaining label forms must agree. -/
def sharedTargetOriginalResidueSelectors
    (modulus : ℕ) [NeZero modulus]
    (firstCoefficient secondCoefficient : ZMod modulus) :
      Finset (ZMod modulus × ZMod modulus ×
        ZMod modulus × ZMod modulus) :=
  Finset.univ.filter fun point =>
    firstCoefficient * point.1 =
      secondCoefficient * point.2.2.1

/-- For a genuine second-branch unit, its ORIGINAL single congruence is
equivalent to the single forced second-label condition `P' = cP`. -/
theorem sharedTargetOriginalResidueEquation_iff
    {modulus : ℕ} [NeZero modulus]
    {firstCoefficient secondCoefficient multiplier : ZMod modulus}
    (compatible : secondCoefficient * multiplier = firstCoefficient)
    (unit : IsUnit secondCoefficient)
    (firstLabel secondLabel : ZMod modulus) :
    firstCoefficient * firstLabel = secondCoefficient * secondLabel ↔
      secondLabel = multiplier * firstLabel := by
  constructor
  · intro shared
    apply unit.mul_left_cancel
    calc
      secondCoefficient * secondLabel = firstCoefficient * firstLabel :=
        shared.symm
      _ = (secondCoefficient * multiplier) * firstLabel := by rw [compatible]
      _ = secondCoefficient * (multiplier * firstLabel) := by ring
  · intro label_eq
    rw [label_eq, ← compatible]
    ring

/-- Exact ORIGINAL-coordinate selector count: among the `B⁴` possible
residue quadruples there are exactly `B³` solutions.  Thus the displayed
four-variable equation alone has index `B`, NOT `B²`. -/
theorem sharedTargetOriginalResidueSelectors_card
    (modulus : ℕ) [NeZero modulus]
    (firstCoefficient secondCoefficient multiplier : ZMod modulus)
    (compatible : secondCoefficient * multiplier = firstCoefficient)
    (unit : IsUnit secondCoefficient) :
    (sharedTargetOriginalResidueSelectors
      modulus firstCoefficient secondCoefficient).card = modulus ^ 3 := by
  classical
  let parameterize :
      (ZMod modulus × ZMod modulus × ZMod modulus) →
        (ZMod modulus × ZMod modulus ×
          ZMod modulus × ZMod modulus) :=
    fun point =>
      (point.1, point.2.1,
        multiplier * point.1, point.2.2)
  have exact_image :
      sharedTargetOriginalResidueSelectors
        modulus firstCoefficient secondCoefficient =
      (Finset.univ : Finset
        (ZMod modulus × ZMod modulus × ZMod modulus)).image
          parameterize := by
    ext point
    constructor
    · intro selected
      obtain ⟨_, shared⟩ := Finset.mem_filter.mp selected
      have label_eq :=
        (sharedTargetOriginalResidueEquation_iff compatible unit
          point.1 point.2.2.1).mp shared
      refine Finset.mem_image.mpr
        ⟨(point.1, point.2.1, point.2.2.2), Finset.mem_univ _, ?_⟩
      dsimp [parameterize]
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact label_eq.symm
          · rfl
    · intro selected
      obtain ⟨point, _, equal⟩ := Finset.mem_image.mp selected
      rw [← equal]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp [parameterize]
      rw [← compatible]
      ring
  rw [exact_image, Finset.card_image_of_injective]
  · simp [Fintype.card_prod, pow_succ]
    ring
  · intro first second equal
    have first_label := congrArg
      (fun point : ZMod modulus × ZMod modulus ×
        ZMod modulus × ZMod modulus => point.1) equal
    have first_center := congrArg
      (fun point : ZMod modulus × ZMod modulus ×
        ZMod modulus × ZMod modulus => point.2.1) equal
    have second_center := congrArg
      (fun point : ZMod modulus × ZMod modulus ×
        ZMod modulus × ZMod modulus => point.2.2.2) equal
    apply Prod.ext
    · exact first_label
    · exact Prod.ext first_center second_center

/-- Exact original-coordinate period identity: `B⁴ = B * B³`, proving the
single-equation index is precisely `B`.  This must not be confused with the
separately proved `B²` physical-target covolume. -/
theorem sharedTargetOriginalResidue_period_index
    (modulus : ℕ) [NeZero modulus]
    (firstCoefficient secondCoefficient multiplier : ZMod modulus)
    (compatible : secondCoefficient * multiplier = firstCoefficient)
    (unit : IsUnit secondCoefficient) :
    Fintype.card
      (ZMod modulus × ZMod modulus × ZMod modulus × ZMod modulus) =
        modulus *
          (sharedTargetOriginalResidueSelectors
            modulus firstCoefficient secondCoefficient).card := by
  rw [sharedTargetOriginalResidueSelectors_card
    modulus firstCoefficient secondCoefficient multiplier compatible unit]
  simp only [Fintype.card_prod, ZMod.card]
  ring

/-- The three distinguished ACTUAL prime forms on the integer-parametrized
shared-target fiber, reduced in a finite field: first label `P`, target
`aP+BC`, and second label `cP+Bt`. -/
def sharedTargetFiberPrimeTriples
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (firstCoefficient modulus multiplier : field) :
      Finset (field × field × field) :=
  Finset.univ.filter fun point =>
    point.1 ≠ 0 ∧
      firstCoefficient * point.1 + modulus * point.2.1 ≠ 0 ∧
      multiplier * point.1 + modulus * point.2.2 ≠ 0

/-- At a genuine SUPPORT prime dividing `B`, all three distinguished
prime forms are units exactly when the single first prime-label residue
is a unit.  The actual selector cardinality is `(ell-1)ell²`. -/
theorem sharedTargetFiberPrimeTriples_card_of_modulus_zero
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (firstCoefficient multiplier : field)
    (first_unit : firstCoefficient ≠ 0)
    (multiplier_unit : multiplier ≠ 0) :
    (sharedTargetFiberPrimeTriples field
      firstCoefficient 0 multiplier).card =
        (Fintype.card field - 1) * (Fintype.card field) ^ 2 := by
  classical
  have exact_product :
      sharedTargetFiberPrimeTriples field
        firstCoefficient 0 multiplier =
      ((Finset.univ : Finset field).erase 0).product
        ((Finset.univ : Finset field).product Finset.univ) := by
    ext point
    simp [sharedTargetFiberPrimeTriples, first_unit, multiplier_unit]
  rw [exact_product]
  simp [Finset.product_eq_sprod, pow_two]

/-- Concrete genuine prime-field support factor, with the actual field
cardinality `ell`; no surrogate local selector or omitted center is used. -/
theorem sharedTargetSupportPrimeLocalTriples_card
    (ell : ℕ) [Fact ell.Prime]
    (firstCoefficient multiplier : ZMod ell)
    (first_unit : firstCoefficient ≠ 0)
    (multiplier_unit : multiplier ≠ 0) :
    (sharedTargetFiberPrimeTriples (ZMod ell)
      firstCoefficient 0 multiplier).card =
        (ell - 1) * ell ^ 2 := by
  simpa using sharedTargetFiberPrimeTriples_card_of_modulus_zero
    (ZMod ell) firstCoefficient multiplier first_unit multiplier_unit

/-- At a fixed nonzero target residue OUTSIDE the support, the two
branches have independent actual allowed-label sets after deleting their
respective (possibly colliding) forbidden roots. -/
def sharedTargetOutsideConditionalPairs
    (field : Type*) [Fintype field] [DecidableEq field]
    (firstForbidden secondForbidden : Finset field) :
      Finset (field × field) :=
  ((Finset.univ : Finset field) \ firstForbidden).product
    ((Finset.univ : Finset field) \ secondForbidden)

/-- Exact conditional outside-support product factor, retaining the
cardinalities of DISTINCT actual forbidden residues rather than replacing
them by pattern ranks. -/
theorem sharedTargetOutsideConditionalPairs_card
    (field : Type*) [Fintype field] [DecidableEq field]
    (firstForbidden secondForbidden : Finset field) :
    (sharedTargetOutsideConditionalPairs field
      firstForbidden secondForbidden).card =
        (Fintype.card field - firstForbidden.card) *
          (Fintype.card field - secondForbidden.card) := by
  unfold sharedTargetOutsideConditionalPairs
  rw [Finset.product_eq_sprod, Finset.card_product,
    Finset.card_sdiff_of_subset (Finset.subset_univ firstForbidden),
    Finset.card_sdiff_of_subset (Finset.subset_univ secondForbidden)]
  simp

/-- Prime-field version of the genuine shared-target conditional local
factor `(ell - nu)(ell - nu')`. -/
theorem sharedTargetOutsidePrimeConditionalPairs_card
    (ell : ℕ) [Fact ell.Prime]
    (firstForbidden secondForbidden : Finset (ZMod ell)) :
    (sharedTargetOutsideConditionalPairs (ZMod ell)
      firstForbidden secondForbidden).card =
        (ell - firstForbidden.card) *
          (ell - secondForbidden.card) := by
  simpa using sharedTargetOutsideConditionalPairs_card
    (ZMod ell) firstForbidden secondForbidden


end Erdos1139
