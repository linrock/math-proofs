module

public import SharedTargetFiberCovolume1139

@[expose] public section


/-!
# Genuine same-type shared-target local singular factorization

The two prime-pattern branches here share ONE actual prime target and have
the SAME fixed semiprime type and square-core support.  Their actual first
prime-label residues remain separate coordinates.  Distinct integer labels
are permitted to coincide modulo a local prime; deleting the residue
diagonal would give the wrong singular factor.

Outside the support, the forbidden-label-root sets may depend on the
actual nonzero target residue.  The only needed hypothesis is their exact
constant cardinalities; repeated index roots are counted once.  Each
branch's root set must include zero to ensure its prime label is nonzero.

The physical shared-target covolume is `B²` in `(q,P,P')`, as proved by
`SharedTargetFiberCovolume1139`; the original four-coordinate equality
has index only `B`.  No global Green--Tao estimate, targetwise second
moment, or unconditional solution of Erdős #1139 is asserted here.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- The genuine one-pattern support-prime selector: its actual prime label
and distinguished prime target are nonzero, while the center is free. -/
def sharedTargetSupportIndividualSelectors
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (coefficient : field) : Finset (field × field) :=
  Finset.univ.filter fun point =>
    point.1 ≠ 0 ∧ coefficient * point.1 ≠ 0

/-- Every unit support coefficient gives exactly `(ell-1)ell` genuine
individual-pattern label/center selectors. -/
theorem sharedTargetSupportIndividualSelectors_card
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (coefficient : field) (unit : coefficient ≠ 0) :
    (sharedTargetSupportIndividualSelectors field coefficient).card =
      (Fintype.card field - 1) * Fintype.card field := by
  have exact_product :
      sharedTargetSupportIndividualSelectors field coefficient =
        ((Finset.univ : Finset field).erase 0).product Finset.univ := by
    ext point
    simp [sharedTargetSupportIndividualSelectors, unit]
  rw [exact_product]
  simp [Finset.product_eq_sprod]

/-- An actual outside-support one-pattern selector in physical target/label
coordinates.  The forbidden LABEL roots may depend on the actual target
residue; they are a genuine finset and therefore already deduplicated. -/
def sharedTargetOutsideIndividualSelectors
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (forbidden : field → Finset field) : Finset (field × field) :=
  Finset.univ.filter fun point =>
    point.1 ≠ 0 ∧ point.2 ∉ forbidden point.1

/-- If zero is among every actual forbidden-root set, the selected first
branch label really is nonzero; it is not silently omitted from the prime
pattern. -/
theorem sharedTargetOutsideIndividual_label_nonzero
    {field : Type*} [Field field] [Fintype field] [DecidableEq field]
    {forbidden : field → Finset field}
    (zero_forbidden : ∀ target, 0 ∈ forbidden target)
    {point : field × field}
    (selected : point ∈
      sharedTargetOutsideIndividualSelectors field forbidden) :
    point.2 ≠ 0 := by
  intro zero
  obtain ⟨_, _target_nonzero, outside⟩ := Finset.mem_filter.mp selected
  exact outside (zero ▸ zero_forbidden point.1)

/-- Exact fiber above ANY actual nonzero target: one branch has exactly
`ell - nu(q)` genuine label choices, even when index roots collide. -/
theorem sharedTargetOutsideIndividual_target_fiber_card
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (forbidden : field → Finset field)
    (target : field) (nonzero : target ≠ 0) :
    ((sharedTargetOutsideIndividualSelectors field forbidden).filter
      fun point => point.1 = target).card =
        Fintype.card field - (forbidden target).card := by
  let allowed : Finset field := Finset.univ \ forbidden target
  have fiber_card :
      ((sharedTargetOutsideIndividualSelectors field forbidden).filter
        fun point => point.1 = target).card = allowed.card := by
    apply Finset.card_bij fun point _ => point.2
    · intro point selected
      obtain ⟨base, equal⟩ := Finset.mem_filter.mp selected
      obtain ⟨_, _prime_target, outside⟩ := Finset.mem_filter.mp base
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_univ _, equal ▸ outside⟩
    · intro first first_selected second second_selected equal
      have first_target := (Finset.mem_filter.mp first_selected).2
      have second_target := (Finset.mem_filter.mp second_selected).2
      exact Prod.ext (first_target.trans second_target.symm) equal
    · intro label selected
      obtain ⟨_, outside⟩ := Finset.mem_sdiff.mp selected
      refine ⟨(target, label), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, nonzero, outside⟩
  rw [fiber_card]
  unfold allowed
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- Summing the actual target fibers gives the genuine total first-pattern
selector count whenever the DISTINCT forbidden-root cardinality is constant
on nonzero target residues. -/
theorem sharedTargetOutsideIndividualSelectors_card
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (forbidden : field → Finset field) (rootCount : ℕ)
    (uniform : ∀ target : field, target ≠ 0 →
      (forbidden target).card = rootCount) :
    (sharedTargetOutsideIndividualSelectors field forbidden).card =
      (Fintype.card field - 1) *
        (Fintype.card field - rootCount) := by
  let targets : Finset field := Finset.univ.erase 0
  have mapped :
      (↑(sharedTargetOutsideIndividualSelectors field forbidden) :
        Set (field × field)).MapsTo Prod.fst targets := by
    intro point selected
    obtain ⟨_, nonzero, _⟩ := Finset.mem_filter.mp selected
    exact Finset.mem_erase.mpr ⟨nonzero, Finset.mem_univ _⟩
  rw [Finset.card_eq_sum_card_fiberwise mapped]
  calc
    _ = ∑ _target ∈ targets,
          (Fintype.card field - rootCount) := by
      apply Finset.sum_congr rfl
      intro target selected
      have nonzero := (Finset.mem_erase.mp selected).1
      rw [sharedTargetOutsideIndividual_target_fiber_card
        field forbidden target nonzero, uniform target nonzero]
    _ = _ := by
      simp [targets]

/-- The genuine shared-target outside-support selector retains ONE prime
target and TWO separately labeled prime-label coordinates.  Its forbidden
root families may vary independently with the same actual target. -/
def sharedTargetOutsideSharedSelectors
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (firstForbidden secondForbidden : field → Finset field) :
      Finset (field × field × field) :=
  Finset.univ.filter fun point =>
    point.1 ≠ 0 ∧
      point.2.1 ∉ firstForbidden point.1 ∧
      point.2.2 ∉ secondForbidden point.1

/-- Both actual outside-support branch labels are genuinely nonzero when
both root families retain their necessary zero-label obstruction. -/
theorem sharedTargetOutsideShared_labels_nonzero
    {field : Type*} [Field field] [Fintype field] [DecidableEq field]
    {firstForbidden secondForbidden : field → Finset field}
    (first_zero : ∀ target, 0 ∈ firstForbidden target)
    (second_zero : ∀ target, 0 ∈ secondForbidden target)
    {point : field × field × field}
    (selected : point ∈ sharedTargetOutsideSharedSelectors
      field firstForbidden secondForbidden) :
    point.2.1 ≠ 0 ∧ point.2.2 ≠ 0 := by
  obtain ⟨_, _target_nonzero, first_outside, second_outside⟩ :=
    Finset.mem_filter.mp selected
  constructor
  · intro zero
    exact first_outside (zero ▸ first_zero point.1)
  · intro zero
    exact second_outside (zero ▸ second_zero point.1)

/-- At each FIXED actual nonzero target, the two genuine branch label
coordinates form precisely the product of their two allowed-root sets.
This is an exact finite bijection, not an assumed probabilistic
independence assertion. -/
theorem sharedTargetOutsideShared_target_fiber_card
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (firstForbidden secondForbidden : field → Finset field)
    (target : field) (nonzero : target ≠ 0) :
    ((sharedTargetOutsideSharedSelectors
      field firstForbidden secondForbidden).filter
        fun point => point.1 = target).card =
      (sharedTargetOutsideConditionalPairs field
        (firstForbidden target) (secondForbidden target)).card := by
  apply Finset.card_bij fun point _ => point.2
  · intro point selected
    obtain ⟨base, equal⟩ := Finset.mem_filter.mp selected
    obtain ⟨_, _prime_target, first_outside, second_outside⟩ :=
      Finset.mem_filter.mp base
    unfold sharedTargetOutsideConditionalPairs
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_sdiff.mpr
    · exact ⟨Finset.mem_univ _, equal ▸ first_outside⟩
    · exact ⟨Finset.mem_univ _, equal ▸ second_outside⟩
  · intro first first_selected second second_selected equal
    have first_target := (Finset.mem_filter.mp first_selected).2
    have second_target := (Finset.mem_filter.mp second_selected).2
    exact Prod.ext (first_target.trans second_target.symm) equal
  · intro pair selected
    obtain ⟨first_allowed, second_allowed⟩ :=
      Finset.mem_product.mp selected
    obtain ⟨_, first_outside⟩ := Finset.mem_sdiff.mp first_allowed
    obtain ⟨_, second_outside⟩ := Finset.mem_sdiff.mp second_allowed
    refine ⟨(target, pair), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, nonzero, first_outside, second_outside⟩

/-- Exact unrestricted shared-target selector count, including the ONE
shared target form and both independently selected prime-label coordinates.
Roots can depend on the target and collide within each branch; only their
actual distinct cardinalities are assumed constant on nonzero targets. -/
theorem sharedTargetOutsideSharedSelectors_card
    (field : Type*) [Field field] [Fintype field] [DecidableEq field]
    (firstForbidden secondForbidden : field → Finset field)
    (firstRootCount secondRootCount : ℕ)
    (first_uniform : ∀ target : field, target ≠ 0 →
      (firstForbidden target).card = firstRootCount)
    (second_uniform : ∀ target : field, target ≠ 0 →
      (secondForbidden target).card = secondRootCount) :
    (sharedTargetOutsideSharedSelectors
      field firstForbidden secondForbidden).card =
        (Fintype.card field - 1) *
          (Fintype.card field - firstRootCount) *
            (Fintype.card field - secondRootCount) := by
  let targets : Finset field := Finset.univ.erase 0
  have mapped :
      (↑(sharedTargetOutsideSharedSelectors
        field firstForbidden secondForbidden) :
          Set (field × field × field)).MapsTo Prod.fst targets := by
    intro point selected
    obtain ⟨_, nonzero, _⟩ := Finset.mem_filter.mp selected
    exact Finset.mem_erase.mpr ⟨nonzero, Finset.mem_univ _⟩
  rw [Finset.card_eq_sum_card_fiberwise mapped]
  calc
    _ = ∑ _target ∈ targets,
          (Fintype.card field - firstRootCount) *
            (Fintype.card field - secondRootCount) := by
      apply Finset.sum_congr rfl
      intro target selected
      have nonzero := (Finset.mem_erase.mp selected).1
      rw [sharedTargetOutsideShared_target_fiber_card
        field firstForbidden secondForbidden target nonzero,
        sharedTargetOutsideConditionalPairs_card,
        first_uniform target nonzero, second_uniform target nonzero]
    _ = _ := by
      simp [targets, mul_assoc]

/-- The actual prime-local unit density, retained with its exact real
normalization rather than silently treating the shared target as two
independent prime forms. -/
noncomputable def sharedTargetPrimeUnitDensity (prime : ℕ) : ℝ :=
  1 - (prime : ℝ)⁻¹

/-- Genuine prime-local unit density is strictly positive, including the
exceptional prime 2. -/
theorem sharedTargetPrimeUnitDensity_pos
    {prime : ℕ} (prime_valid : prime.Prime) :
    0 < sharedTargetPrimeUnitDensity prime := by
  unfold sharedTargetPrimeUnitDensity
  apply sub_pos.mpr
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast prime_valid.one_lt

/-- Normalize an ACTUAL two-coordinate individual-pattern selector by the
full prime-square residue box and by all `rank + 1` distinct prime forms:
one label and `rank` target forms. -/
noncomputable def sharedTargetIndividualNormalizedFactor
    (prime rank selectorCard : ℕ) : ℝ :=
  (selectorCard : ℝ) / (prime : ℝ) ^ 2 /
    (sharedTargetPrimeUnitDensity prime) ^ (rank + 1)

/-- Normalize an ACTUAL three-coordinate shared-target selector by the
full prime-cube residue box and exactly `r+r'+1` distinct prime forms:
two labels, ONE shared target, and the remaining branch forms. -/
noncomputable def sharedTargetSharedNormalizedFactor
    (prime firstRank secondRank selectorCard : ℕ) : ℝ :=
  (selectorCard : ℝ) / (prime : ℝ) ^ 3 /
    (sharedTargetPrimeUnitDensity prime) ^
      (firstRank + secondRank + 1)

/-- CORE scalar identity for the genuine shared target: whenever individual
selector counts are `(ell-1)x` and `(ell-1)y`, and the actual shared
selector count is `(ell-1)xy`, normalized shared singular density equals
the PRODUCT of the two individual densities.  The crucial missing target
factor is supplied exactly by `(ell-1)/ell = 1-1/ell`. -/
theorem sharedTargetNormalizedFactor_product_of_selector_counts
    {prime : ℕ} (prime_valid : prime.Prime)
    (firstRank secondRank firstChoices secondChoices : ℕ) :
    sharedTargetSharedNormalizedFactor prime firstRank secondRank
      ((prime - 1) * firstChoices * secondChoices) =
      sharedTargetIndividualNormalizedFactor prime firstRank
        ((prime - 1) * firstChoices) *
      sharedTargetIndividualNormalizedFactor prime secondRank
        ((prime - 1) * secondChoices) := by
  have prime_nonzero : (prime : ℝ) ≠ 0 := by
    exact_mod_cast prime_valid.ne_zero
  have density_nonzero : sharedTargetPrimeUnitDensity prime ≠ 0 :=
    (sharedTargetPrimeUnitDensity_pos prime_valid).ne'
  have predecessor : ((prime - 1 : ℕ) : ℝ) = (prime : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub prime_valid.one_le
  unfold sharedTargetSharedNormalizedFactor
    sharedTargetIndividualNormalizedFactor
  push_cast
  rw [predecessor]
  simp only [pow_succ, pow_add]
  unfold sharedTargetPrimeUnitDensity
  field_simp

/-- At a genuine SUPPORTED prime, the normalized shared-target factor of
the actual three-coordinate selector is exactly the product of the two
actual individual-pattern factors, with ranks `r,r'` and ONE common
target prime form counted once. -/
theorem sharedTargetSupportNormalizedFactor_eq_product
    (prime firstRank secondRank : ℕ) [Fact prime.Prime]
    (firstCoefficient secondCoefficient multiplier : ZMod prime)
    (first_unit : firstCoefficient ≠ 0)
    (second_unit : secondCoefficient ≠ 0)
    (multiplier_unit : multiplier ≠ 0) :
    sharedTargetSharedNormalizedFactor prime firstRank secondRank
      (sharedTargetFiberPrimeTriples (ZMod prime)
        firstCoefficient 0 multiplier).card =
      sharedTargetIndividualNormalizedFactor prime firstRank
        (sharedTargetSupportIndividualSelectors
          (ZMod prime) firstCoefficient).card *
      sharedTargetIndividualNormalizedFactor prime secondRank
        (sharedTargetSupportIndividualSelectors
          (ZMod prime) secondCoefficient).card := by
  rw [sharedTargetSupportPrimeLocalTriples_card
    prime firstCoefficient multiplier first_unit multiplier_unit,
    sharedTargetSupportIndividualSelectors_card
      (ZMod prime) firstCoefficient first_unit,
    sharedTargetSupportIndividualSelectors_card
      (ZMod prime) secondCoefficient second_unit]
  simpa [pow_two, mul_assoc] using
    sharedTargetNormalizedFactor_product_of_selector_counts
      (Fact.out : prime.Prime) firstRank secondRank prime prime

/-- At a genuine OUTSIDE prime, arbitrary target-dependent forbidden-root
families give exact normalized singular factorization.  Distinct index
roots are counted once; numerical first and second label residues are NOT
required to differ, because distinct integer primes can coincide locally. -/
theorem sharedTargetOutsideNormalizedFactor_eq_product
    (prime firstRank secondRank firstRootCount secondRootCount : ℕ)
    [Fact prime.Prime]
    (firstForbidden secondForbidden : ZMod prime → Finset (ZMod prime))
    (first_uniform : ∀ target : ZMod prime, target ≠ 0 →
      (firstForbidden target).card = firstRootCount)
    (second_uniform : ∀ target : ZMod prime, target ≠ 0 →
      (secondForbidden target).card = secondRootCount) :
    sharedTargetSharedNormalizedFactor prime firstRank secondRank
      (sharedTargetOutsideSharedSelectors
        (ZMod prime) firstForbidden secondForbidden).card =
      sharedTargetIndividualNormalizedFactor prime firstRank
        (sharedTargetOutsideIndividualSelectors
          (ZMod prime) firstForbidden).card *
      sharedTargetIndividualNormalizedFactor prime secondRank
        (sharedTargetOutsideIndividualSelectors
          (ZMod prime) secondForbidden).card := by
  rw [sharedTargetOutsideSharedSelectors_card
    (ZMod prime) firstForbidden secondForbidden
      firstRootCount secondRootCount first_uniform second_uniform,
    sharedTargetOutsideIndividualSelectors_card
      (ZMod prime) firstForbidden firstRootCount first_uniform,
    sharedTargetOutsideIndividualSelectors_card
      (ZMod prime) secondForbidden secondRootCount second_uniform]
  simpa using sharedTargetNormalizedFactor_product_of_selector_counts
    (Fact.out : prime.Prime) firstRank secondRank
    (prime - firstRootCount) (prime - secondRootCount)

/-- The actual one-pattern local factor, using its full square-box selector
count on supported primes and its genuine deduplicated root count outside
the support. -/
noncomputable def sharedTargetIndividualPatternLocalFactor
    (support : Finset ℕ) (rank : ℕ) (rootCount : ℕ → ℕ)
    (prime : ℕ) : ℝ :=
  if prime ∈ support then
    sharedTargetIndividualNormalizedFactor prime rank
      ((prime - 1) * prime)
  else
    sharedTargetIndividualNormalizedFactor prime rank
      ((prime - 1) * (prime - rootCount prime))

/-- The actual same-support, same-type shared-target local factor, retaining
its three-coordinate selector and the ONE shared target form. -/
noncomputable def sharedTargetPairedPatternLocalFactor
    (support : Finset ℕ) (firstRank secondRank : ℕ)
    (firstRootCount secondRootCount : ℕ → ℕ)
    (prime : ℕ) : ℝ :=
  if prime ∈ support then
    sharedTargetSharedNormalizedFactor prime firstRank secondRank
      ((prime - 1) * prime * prime)
  else
    sharedTargetSharedNormalizedFactor prime firstRank secondRank
      ((prime - 1) *
        (prime - firstRootCount prime) *
        (prime - secondRootCount prime))

/-- EXACT single-prime factorization for the true same-support,
same-semiprime-type shared-target system, including every supported prime,
every outside prime, and all actual root collisions. -/
theorem sharedTargetPatternLocalFactor_eq_product
    {prime : ℕ} (prime_valid : prime.Prime)
    (support : Finset ℕ) (firstRank secondRank : ℕ)
    (firstRootCount secondRootCount : ℕ → ℕ) :
    sharedTargetPairedPatternLocalFactor support firstRank secondRank
      firstRootCount secondRootCount prime =
      sharedTargetIndividualPatternLocalFactor
        support firstRank firstRootCount prime *
      sharedTargetIndividualPatternLocalFactor
        support secondRank secondRootCount prime := by
  unfold sharedTargetPairedPatternLocalFactor
    sharedTargetIndividualPatternLocalFactor
  split_ifs with supported
  · exact sharedTargetNormalizedFactor_product_of_selector_counts
      prime_valid firstRank secondRank prime prime
  · exact sharedTargetNormalizedFactor_product_of_selector_counts
      prime_valid firstRank secondRank
      (prime - firstRootCount prime) (prime - secondRootCount prime)

/-- Full FINITE Euler-product factorization over ANY genuine finite set of
prime places.  Both patterns use the SAME type support and the SAME shared
target type; no cross-support, cross-type, or analytic infinite-product
claim is inserted. -/
theorem sharedTargetFiniteSingularProduct_eq_product
    (localPrimes support : Finset ℕ)
    (prime_valid : ∀ prime ∈ localPrimes, prime.Prime)
    (firstRank secondRank : ℕ)
    (firstRootCount secondRootCount : ℕ → ℕ) :
    (∏ prime ∈ localPrimes,
      sharedTargetPairedPatternLocalFactor support firstRank secondRank
        firstRootCount secondRootCount prime) =
      (∏ prime ∈ localPrimes,
        sharedTargetIndividualPatternLocalFactor
          support firstRank firstRootCount prime) *
      (∏ prime ∈ localPrimes,
        sharedTargetIndividualPatternLocalFactor
          support secondRank secondRootCount prime) := by
  calc
    _ = ∏ prime ∈ localPrimes,
          (sharedTargetIndividualPatternLocalFactor
            support firstRank firstRootCount prime *
           sharedTargetIndividualPatternLocalFactor
            support secondRank secondRootCount prime) := by
      apply Finset.prod_congr rfl
      intro prime selected
      exact sharedTargetPatternLocalFactor_eq_product
        (prime_valid prime selected) support firstRank secondRank
          firstRootCount secondRootCount
    _ = _ := by
      rw [Finset.prod_mul_distrib]

/-- The ACTUAL same-type physical Jacobian in target coordinates `h=sq`.
The previously proved `B²` physical covolume contributes `1/B²`, and
changing from `q` to `h` contributes another `1/s`, yielding `s/W²` when
the genuine square-core modulus satisfies `W=sB`. -/
theorem sharedTargetTypedPhysicalJacobian_eq
    (coreModulus sharedType fiberModulus : ℝ)
    (type_nonzero : sharedType ≠ 0)
    (fiber_nonzero : fiberModulus ≠ 0)
    (actual_factorization : coreModulus = sharedType * fiberModulus) :
    1 / (sharedType * fiberModulus ^ 2) =
      sharedType / coreModulus ^ 2 := by
  rw [actual_factorization]
  field_simp

/-- Exact singular/covolume cancellation on the SAME actual shared-type
fiber.  Both individual singular factors cancel, and the genuine physical
index `B²` converts `W²` to precisely `s²`. -/
theorem sharedTargetSingularCovolumeCancellation
    (coreModulus sharedType fiberModulus
      firstSingular secondSingular : ℝ)
    (fiber_nonzero : fiberModulus ≠ 0)
    (first_nonzero : firstSingular ≠ 0)
    (second_nonzero : secondSingular ≠ 0)
    (actual_factorization : coreModulus = sharedType * fiberModulus) :
    coreModulus ^ 2 / (firstSingular * secondSingular) *
      ((firstSingular * secondSingular) / fiberModulus ^ 2) =
        sharedType ^ 2 := by
  rw [actual_factorization]
  field_simp

/-- The true fixed-label model degree of an actual prime-pattern edge,
including its pattern-dependent singular series, prime label, square-core
modulus, and every target prime logarithm. -/
noncomputable def sharedTargetPatternExpectedDegree
    (singular primeLabel coreModulus primeLog : ℝ) (rank : ℕ) : ℝ :=
  singular * primeLabel / (coreModulus * primeLog ^ rank)

/-- The exact pattern-dependent model edge weight; replacing it by uniform
rich-target sampling is invalid and was disproved by actual prime examples. -/
noncomputable def sharedTargetPatternModelWeight
    (patternWeight singular primeLabel coreModulus primeLog : ℝ)
    (rank : ℕ) : ℝ :=
  patternWeight /
    sharedTargetPatternExpectedDegree
      singular primeLabel coreModulus primeLog rank

/-- EXACT quantitative second-moment coefficient cancellation for a
same-type shared-target pattern pair.  Two genuine pattern-weighted edge
denominators, the product singular series for the `r+r'+1` distinct prime
forms, and the honest target-coordinate Jacobian `s/W²` reduce to

    mu * mu' * s / (P * P' * log Y).

The two integer prime labels remain separate, the shared target is counted
only once, and NO Green--Tao asymptotic or covariance estimate is claimed. -/
theorem sharedTargetPatternWeight_singular_jacobian_cancellation
    (firstWeight secondWeight
      firstSingular secondSingular
      firstLabel secondLabel coreModulus sharedType primeLog : ℝ)
    (firstRank secondRank : ℕ)
    (first_singular_nonzero : firstSingular ≠ 0)
    (second_singular_nonzero : secondSingular ≠ 0)
    (first_label_nonzero : firstLabel ≠ 0)
    (second_label_nonzero : secondLabel ≠ 0)
    (core_nonzero : coreModulus ≠ 0)
    (log_nonzero : primeLog ≠ 0) :
    sharedTargetPatternModelWeight firstWeight
        firstSingular firstLabel coreModulus primeLog firstRank *
      sharedTargetPatternModelWeight secondWeight
        secondSingular secondLabel coreModulus primeLog secondRank *
      ((firstSingular * secondSingular) /
        primeLog ^ (firstRank + secondRank + 1)) *
      (sharedType / coreModulus ^ 2) =
        firstWeight * secondWeight * sharedType /
          (firstLabel * secondLabel * primeLog) := by
  unfold sharedTargetPatternModelWeight sharedTargetPatternExpectedDegree
  simp only [pow_succ, pow_add]
  field_simp


end Erdos1139
