module

public import AdaptiveMixedPatternDistribution1139
public import ArbitraryPrimeRankLocalPatterns1139

@[expose] public section


/-!
# Actual collision-aware mixed-pattern local singular factors

For ONE shared adaptive mixed outcome `(b, rho)`, let `A` be its genuine
physical index pattern and put `W = (∏ s ∈ S, s)^2`.  The actual affine
forms are

    P,   ((b+d)/gcd(W,b+d))*P + (W/gcd(W,b+d))*C,   d ∈ A.

This file counts their genuine two-variable finite-field selectors.  At a
supported prime every target form is automatically a unit for every
nonzero label.  At an unsupported prime the exact cardinality retains the
number of DISTINCT forbidden slopes; no independence or root-distinctness
is assumed.  Above the physical scale those slopes are genuinely distinct.

These are local singular-series inputs.  No Green--Tao--Ziegler
prime-pattern theorem, moving-parameter uniformity, target covariance,
or resolution of Erdős #1139 is asserted.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos1139

/-- The ACTUAL finite-field selector for the genuine prime label and ALL
prime and supported-semiprime forms of ONE common mixed outcome. -/
noncomputable def adaptiveMixedActualLocalSelectors
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime] : Finset (ZMod ell × ZMod ell) :=
  (Finset.univ.product Finset.univ).filter fun pair =>
    pair.1 ≠ 0 ∧
      ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
        adaptiveMixedActualAffineForm
          support outcome.1 index ell pair.1 pair.2 ≠ 0

/-- Exact selector membership includes the prime LABEL and every actual
unreduced physical target form. -/
theorem mem_adaptiveMixedActualLocalSelectors
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime] (label center : ZMod ell) :
    (label, center) ∈
      adaptiveMixedActualLocalSelectors support scale ell outcome ↔
        label ≠ 0 ∧
          ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
            adaptiveMixedActualAffineForm
              support outcome.1 index ell label center ≠ 0 := by
  simp [adaptiveMixedActualLocalSelectors]

/-- At a supported prime, EVERY actual reduced-modulus coefficient is
zero, including semiprime forms of DIFFERENT supported types. -/
theorem adaptiveMixed_supported_reduced_coefficient_eq_zero
    {support : Finset ℕ} {scale index ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    (((adaptiveMixedTypeModulus support /
      adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell)) = 0 := by
  rcases adaptiveMixedOutcomeActiveIndex_type_certificate primes active with
    ⟨typed, _coprime, _outside⟩ |
      ⟨selected, selected_supported, typed, _divides, _coprime, _outside⟩
  · rw [typed]
    simp only [Nat.div_one]
    exact (ZMod.natCast_eq_zero_iff
      (adaptiveMixedTypeModulus support) ell).mpr
        (adaptiveMixedType_dvd_modulus supported)
  · rw [typed]
    exact (ZMod.natCast_eq_zero_iff
      (adaptiveMixedTypeModulus support / selected) ell).mpr
        (adaptiveMixedType_support_dvd_reduced_modulus
          primes selected_supported supported)

/-- At a supported prime EVERY genuine active target form is nonzero
EXACTLY when the prime label is nonzero, independently of the center. -/
theorem adaptiveMixed_supported_affine_nonzero_iff_label_nonzero
    {support : Finset ℕ} {scale index ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (label center : ZMod ell) :
    adaptiveMixedActualAffineForm
      support outcome.1 index ell label center ≠ 0 ↔ label ≠ 0 := by
  have prime_coefficient_nonzero :
      (((outcome.1 + index) /
        adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell) ≠
          0 := by
    have actual := adaptiveMixedOutcome_support_prime_affine_nonzero
      primes supported active
    simpa [adaptiveMixedActualAffineForm] using actual
  unfold adaptiveMixedActualAffineForm
  rw [adaptiveMixed_supported_reduced_coefficient_eq_zero
    primes supported active]
  simp [prime_coefficient_nonzero]

/-- At a supported prime the ENTIRE actual local selector is exactly all
nonzero labels times all unrestricted centers. -/
theorem adaptiveMixedActualLocalSelectors_supported_eq_product
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support) :
    adaptiveMixedActualLocalSelectors support scale ell outcome =
      (Finset.univ.erase (0 : ZMod ell)).product Finset.univ := by
  classical
  ext pair
  rw [mem_adaptiveMixedActualLocalSelectors,
    Finset.product_eq_sprod, Finset.mem_product]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · exact And.left
  · intro nonzero
    refine ⟨nonzero, ?_⟩
    intro index active
    exact (adaptiveMixed_supported_affine_nonzero_iff_label_nonzero
      primes supported active pair.1 pair.2).mpr nonzero

/-- EXACT supported-prime selector cardinality: `ell*(ell-1)`.  There
is NO extra independent target-unit restriction at a squared support prime. -/
theorem adaptiveMixedActualLocalSelectors_card_supported
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support) :
    (adaptiveMixedActualLocalSelectors support scale ell outcome).card =
      (ell - 1) * ell := by
  rw [adaptiveMixedActualLocalSelectors_supported_eq_product
    primes supported, Finset.product_eq_sprod, Finset.card_product]
  simp

/-- The genuine forbidden normalized local center of ONE actual physical
index, retaining its exact true gcd type and unreduced numerator. -/
noncomputable def adaptiveMixedActualIndexLocalRoot
    (support : Finset ℕ) (center index ell : ℕ) [Fact ell.Prime] : ZMod ell :=
  -(((center + index) /
      adaptiveMixedActualIndexType support center index : ℕ) : ZMod ell) /
    (((adaptiveMixedTypeModulus support /
      adaptiveMixedActualIndexType support center index : ℕ) : ZMod ell))

/-- At an unsupported prime, a normalized local center kills its ACTUAL
affine form exactly when it equals that genuine forbidden root. -/
theorem adaptiveMixed_outside_affine_one_zero_iff_root
    {support : Finset ℕ} {scale index ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (center : ZMod ell) :
    adaptiveMixedActualAffineForm
      support outcome.1 index ell 1 center = 0 ↔
        center = adaptiveMixedActualIndexLocalRoot
          support outcome.1 index ell := by
  have nonzero := adaptiveMixedOutcome_outside_reduced_modulus_nonzero
    primes outside active
  unfold adaptiveMixedActualAffineForm adaptiveMixedActualIndexLocalRoot
  simp only [mul_one]
  constructor
  · intro equation
    apply (eq_div_iff nonzero).mpr
    linear_combination equation
  · intro root
    rw [root]
    field_simp
    ring

/-- Actual forbidden-root membership keeps collisions: it is equivalent
to the vanishing of AT LEAST ONE genuine physical target form. -/
theorem mem_adaptiveMixedOutcomeLocalForbidden_iff
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) (center : ZMod ell) :
    center ∈ adaptiveMixedOutcomeLocalForbidden support scale ell outcome ↔
      ∃ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
        adaptiveMixedActualAffineForm
          support outcome.1 index ell 1 center = 0 := by
  constructor
  · intro selected
    obtain ⟨index, active, root⟩ := Finset.mem_image.mp selected
    refine ⟨index, active, ?_⟩
    apply (adaptiveMixed_outside_affine_one_zero_iff_root
      primes outside active center).mpr
    exact root.symm
  · rintro ⟨index, active, zero⟩
    apply Finset.mem_image.mpr
    refine ⟨index, active, ?_⟩
    exact (adaptiveMixed_outside_affine_one_zero_iff_root
      primes outside active center).mp zero |>.symm

/-- Homogeneity is exact: dividing the local center by its nonzero prime
label reduces EVERY actual mixed affine form to the unit-label form. -/
theorem adaptiveMixedActualAffineForm_normalize_label
    (support : Finset ℕ) (center index ell : ℕ) [Fact ell.Prime]
    (label value : ZMod ell) (nonzero : label ≠ 0) :
    adaptiveMixedActualAffineForm support center index ell label value =
      label * adaptiveMixedActualAffineForm
        support center index ell 1 (value / label) := by
  unfold adaptiveMixedActualAffineForm
  field_simp

/-- At a nonzero label, actual affine nonvanishing is exactly normalized
unit-label affine nonvanishing. -/
theorem adaptiveMixedActualAffineForm_normalized_nonzero_iff
    (support : Finset ℕ) (center index ell : ℕ) [Fact ell.Prime]
    (label value : ZMod ell) (nonzero : label ≠ 0) :
    adaptiveMixedActualAffineForm support center index ell label value ≠ 0 ↔
      adaptiveMixedActualAffineForm
        support center index ell 1 (value / label) ≠ 0 := by
  rw [adaptiveMixedActualAffineForm_normalize_label
    support center index ell label value nonzero]
  simp [nonzero]

/-- Outside the supported prime types, the TRUE root of each mixed form
is the simple common slope `-(b+d)/W`, despite its varying gcd type. -/
theorem adaptiveMixed_outside_actual_root_eq_common_slope
    {support : Finset ℕ} {scale index ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualIndexLocalRoot support outcome.1 index ell =
      -((outcome.1 + index : ℕ) : ZMod ell) /
        ((adaptiveMixedTypeModulus support : ℕ) : ZMod ell) := by
  have ell_prime : ell.Prime := Fact.out
  have modulus_nonzero :
      ((adaptiveMixedTypeModulus support : ℕ) : ZMod ell) ≠ 0 := by
    intro zero
    exact adaptiveMixedOutsidePrime_not_dvd_type_modulus
      primes ell_prime outside
      ((ZMod.natCast_eq_zero_iff
        (adaptiveMixedTypeModulus support) ell).mp zero)
  let root := adaptiveMixedActualIndexLocalRoot
    support outcome.1 index ell
  have root_zero :
      adaptiveMixedActualAffineForm
        support outcome.1 index ell 1 root = 0 :=
    (adaptiveMixed_outside_affine_one_zero_iff_root
      primes outside active root).mpr rfl
  have scaled := adaptiveMixedActualAffineForm_scaled
    support outcome.1 index ell 1 root
    (adaptiveMixedOutcomeActiveIndex_type_dvd_value primes active)
    (adaptiveMixedOutcomeActiveIndex_type_dvd_modulus primes active)
  rw [root_zero, mul_zero, mul_one] at scaled
  change root = _
  apply (eq_div_iff modulus_nonzero).mpr
  linear_combination -scaled

/-- Root collisions at an unsupported prime are EXACTLY physical-index
congruences.  No independence or blanket root-distinctness is assumed. -/
theorem adaptiveMixed_outside_actual_roots_eq_iff_index_mod
    {support : Finset ℕ} {scale first second ell : ℕ}
    {outcome : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support)
    (first_active :
      first ∈ adaptiveMixedOutcomeActiveIndices support scale outcome)
    (second_active :
      second ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualIndexLocalRoot support outcome.1 first ell =
      adaptiveMixedActualIndexLocalRoot support outcome.1 second ell ↔
        first % ell = second % ell := by
  have ell_prime : ell.Prime := Fact.out
  have modulus_nonzero :
      ((adaptiveMixedTypeModulus support : ℕ) : ZMod ell) ≠ 0 := by
    intro zero
    exact adaptiveMixedOutsidePrime_not_dvd_type_modulus
      primes ell_prime outside
      ((ZMod.natCast_eq_zero_iff
        (adaptiveMixedTypeModulus support) ell).mp zero)
  rw [adaptiveMixed_outside_actual_root_eq_common_slope
    primes outside first_active,
    adaptiveMixed_outside_actual_root_eq_common_slope
      primes outside second_active]
  constructor
  · intro equal
    have numerator_equal := (div_left_inj' modulus_nonzero).mp equal
    have index_equal : (first : ZMod ell) = (second : ZMod ell) := by
      push_cast at numerator_equal
      linear_combination -numerator_equal
    exact (ZMod.natCast_eq_natCast_iff' first second ell).mp index_equal
  · intro equal
    have index_equal :=
      (ZMod.natCast_eq_natCast_iff' first second ell).mpr equal
    push_cast
    rw [index_equal]

/-- EXACT unsupported-prime selector count, preserving the true number
of DISTINCT affine roots and all collisions among physical indices. -/
theorem adaptiveMixedActualLocalSelectors_card_outside
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) :
    (adaptiveMixedActualLocalSelectors support scale ell outcome).card =
      (ell - 1) *
        (ell -
          (adaptiveMixedOutcomeLocalForbidden
            support scale ell outcome).card) := by
  classical
  let forbidden := adaptiveMixedOutcomeLocalForbidden
    support scale ell outcome
  have bijection :
      (adaptiveMixedActualLocalSelectors support scale ell outcome).card =
        ((Finset.univ.erase (0 : ZMod ell)).product
          (Finset.univ \ forbidden)).card := by
    apply Finset.card_bij
      (fun pair _ => (pair.1, pair.2 / pair.1))
    · intro pair selected
      obtain ⟨label_nonzero, forms⟩ :=
        (mem_adaptiveMixedActualLocalSelectors
          support scale ell outcome pair.1 pair.2).mp selected
      have good : pair.2 / pair.1 ∉ forbidden := by
        intro selected_root
        obtain ⟨index, active, zero⟩ :=
          (mem_adaptiveMixedOutcomeLocalForbidden_iff
            primes outside (pair.2 / pair.1)).mp selected_root
        exact ((adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support outcome.1 index ell pair.1 pair.2 label_nonzero).mp
            (forms index active)) zero
      rw [Finset.product_eq_sprod]
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_erase.mpr
          ⟨label_nonzero, Finset.mem_univ _⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, good⟩⟩
    · intro first first_selected second _second_selected equal
      have same_label := congrArg Prod.fst equal
      have same_normalized := congrArg Prod.snd equal
      change first.1 = second.1 at same_label
      change first.2 / first.1 = second.2 / second.1 at same_normalized
      rw [← same_label] at same_normalized
      have nonzero :=
        (mem_adaptiveMixedActualLocalSelectors
          support scale ell outcome first.1 first.2).mp first_selected |>.1
      exact Prod.ext same_label
        ((div_left_inj' nonzero).mp same_normalized)
    · intro pair selected
      rw [Finset.product_eq_sprod] at selected
      obtain ⟨unit, good⟩ := Finset.mem_product.mp selected
      have nonzero := (Finset.mem_erase.mp unit).1
      have avoids := (Finset.mem_sdiff.mp good).2
      refine ⟨(pair.1, pair.2 * pair.1), ?_, ?_⟩
      · apply (mem_adaptiveMixedActualLocalSelectors
          support scale ell outcome pair.1 (pair.2 * pair.1)).mpr
        refine ⟨nonzero, ?_⟩
        intro index active
        apply (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support outcome.1 index ell pair.1 (pair.2 * pair.1) nonzero).mpr
        have normalized : pair.2 * pair.1 / pair.1 = pair.2 := by
          field_simp
        rw [normalized]
        intro zero
        exact avoids
          ((mem_adaptiveMixedOutcomeLocalForbidden_iff
            primes outside pair.2).mpr ⟨index, active, zero⟩)
      · apply Prod.ext
        · rfl
        · change pair.2 * pair.1 / pair.1 = pair.2
          field_simp
  rw [bijection, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [forbidden]

/-- Above the true physical scale, the distinct forbidden affine roots
are in exact bijection with ALL selected prime and semiprime indices. -/
theorem adaptiveMixedOutcomeLocalForbidden_card_eq_rank_of_large
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) (large : scale < ell) :
    (adaptiveMixedOutcomeLocalForbidden support scale ell outcome).card =
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card := by
  unfold adaptiveMixedOutcomeLocalForbidden
  apply Finset.card_image_iff.mpr
  intro first first_active second second_active equal
  change
    adaptiveMixedActualIndexLocalRoot support outcome.1 first ell =
      adaptiveMixedActualIndexLocalRoot support outcome.1 second ell at equal
  have congruent :=
    (adaptiveMixed_outside_actual_roots_eq_iff_index_mod
      primes outside first_active second_active).mp equal
  have first_bounded :=
    (Finset.mem_Icc.mp
      (adaptiveMixedOutcomeActiveIndices_subset_physical
        support scale outcome first_active)).2
  have second_bounded :=
    (Finset.mem_Icc.mp
      (adaptiveMixedOutcomeActiveIndices_subset_physical
        support scale outcome second_active)).2
  rwa [Nat.mod_eq_of_lt (first_bounded.trans_lt large),
    Nat.mod_eq_of_lt (second_bounded.trans_lt large)] at congruent

/-- EXACT large-prime selector cardinality for the ACTUAL arbitrary-rank
mixed pattern: `(ell-1)*(ell-rank)`, with no discarded affine collisions. -/
theorem adaptiveMixedActualLocalSelectors_card_large
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) (large : scale < ell) :
    (adaptiveMixedActualLocalSelectors support scale ell outcome).card =
      (ell - 1) *
        (ell - (adaptiveMixedOutcomeActiveIndices
          support scale outcome).card) := by
  rw [adaptiveMixedActualLocalSelectors_card_outside primes outside,
    adaptiveMixedOutcomeLocalForbidden_card_eq_rank_of_large
      primes outside large]

/-- The actual normalized Green--Tao local density includes its genuine
prime label and EVERY retained mixed target form. -/
noncomputable def adaptiveMixedActualNormalizedLocalFactor
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime] : ℝ :=
  (((adaptiveMixedActualLocalSelectors support scale ell outcome).card : ℝ) /
    (ell : ℝ) ^ 2) *
      ((ell : ℝ) / ((ell : ℝ) - 1)) ^
        ((adaptiveMixedOutcomeActiveIndices support scale outcome).card + 1)

/-- Instance-free scalar packaging permits an arbitrary finite set of
genuine evaluation primes without dependent typeclass bookkeeping. -/
noncomputable def adaptiveMixedActualScalarLocalFactor
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ) : ℝ :=
  if prime : ell.Prime then
    @adaptiveMixedActualNormalizedLocalFactor
      support scale ell outcome ⟨prime⟩
  else 0

/-- Every actual mixed local selector is NONEMPTY at EVERY prime,
including all outside small-prime affine obstructions. -/
theorem adaptiveMixedActualLocalSelectors_nonempty
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime) :
    (adaptiveMixedActualLocalSelectors support scale ell outcome).Nonempty := by
  obtain ⟨label, center, nonzero, forms⟩ :=
    adaptiveMixedOutcome_all_prime_locally_admissible
      support scale outcome primes ell
  exact ⟨(label, center),
    (mem_adaptiveMixedActualLocalSelectors
      support scale ell outcome label center).mpr
        ⟨nonzero, forms⟩⟩

/-- The number of DISTINCT unsupported-prime roots is genuinely below
the whole local field, even when the scale exceeds the local prime. -/
theorem adaptiveMixedOutcomeLocalForbidden_card_lt_outside
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) :
    (adaptiveMixedOutcomeLocalForbidden support scale ell outcome).card < ell := by
  have positive :
      0 < (adaptiveMixedActualLocalSelectors
        support scale ell outcome).card :=
    Finset.card_pos.mpr
      (adaptiveMixedActualLocalSelectors_nonempty
        support scale ell outcome primes)
  rw [adaptiveMixedActualLocalSelectors_card_outside
    primes outside] at positive
  by_contra not_less
  have zero : ell -
      (adaptiveMixedOutcomeLocalForbidden support scale ell outcome).card = 0 :=
    Nat.sub_eq_zero_of_le (Nat.le_of_not_gt not_less)
  rw [zero, Nat.mul_zero] at positive
  omega

/-- Every GENUINE actual normalized mixed local density is strictly
positive at every prime and for every retained actual rank. -/
theorem adaptiveMixedActualNormalizedLocalFactor_pos
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime) :
    0 < adaptiveMixedActualNormalizedLocalFactor
      support scale ell outcome := by
  have prime : ell.Prime := Fact.out
  have ell_real : (0 : ℝ) < ell := by
    exact_mod_cast prime.pos
  have denominator : (0 : ℝ) < (ell : ℝ) - 1 := by
    have large : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
    linarith
  have count : (0 : ℝ) <
      ((adaptiveMixedActualLocalSelectors support scale ell outcome).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (adaptiveMixedActualLocalSelectors_nonempty
        support scale ell outcome primes)
  unfold adaptiveMixedActualNormalizedLocalFactor
  positivity

/-- Supported square primes have EXACT factor
`(ell/(ell-1))^rank`: they IMPROVE the singular product. -/
theorem adaptiveMixedActualNormalizedLocalFactor_supported
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support) :
    adaptiveMixedActualNormalizedLocalFactor support scale ell outcome =
      ((ell : ℝ) / ((ell : ℝ) - 1)) ^
        (adaptiveMixedOutcomeActiveIndices support scale outcome).card := by
  have prime : ell.Prime := Fact.out
  have ell_nonzero : (ell : ℝ) ≠ 0 := by
    exact_mod_cast prime.ne_zero
  have denominator : (ell : ℝ) - 1 ≠ 0 := by
    have large : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
    linarith
  unfold adaptiveMixedActualNormalizedLocalFactor
  rw [adaptiveMixedActualLocalSelectors_card_supported primes supported]
  push_cast [Nat.cast_sub prime.one_le]
  rw [pow_succ ((ell : ℝ) / ((ell : ℝ) - 1))
    (adaptiveMixedOutcomeActiveIndices support scale outcome).card]
  field_simp

/-- Every supported prime factor is AT LEAST ONE, regardless of its
position relative to the pattern scale or its actual retained rank. -/
theorem adaptiveMixedActualNormalizedLocalFactor_supported_ge_one
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support) :
    (1 : ℝ) ≤ adaptiveMixedActualNormalizedLocalFactor
      support scale ell outcome := by
  rw [adaptiveMixedActualNormalizedLocalFactor_supported primes supported]
  have prime : ell.Prime := Fact.out
  have denominator : (0 : ℝ) < (ell : ℝ) - 1 := by
    have large : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
    linarith
  have base : (1 : ℝ) ≤ (ell : ℝ) / ((ell : ℝ) - 1) := by
    apply (le_div_iff₀ denominator).mpr
    linarith
  exact one_le_pow₀ base

/-- The EXACT unsupported-prime factor retains its number of DISTINCT
roots, rather than incorrectly replacing collisions by the total rank. -/
theorem adaptiveMixedActualNormalizedLocalFactor_outside
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) :
    adaptiveMixedActualNormalizedLocalFactor support scale ell outcome =
      (((ell - (adaptiveMixedOutcomeLocalForbidden
        support scale ell outcome).card : ℕ) : ℝ) / (ell : ℝ)) *
        ((ell : ℝ) / ((ell : ℝ) - 1)) ^
          (adaptiveMixedOutcomeActiveIndices support scale outcome).card := by
  have prime : ell.Prime := Fact.out
  have ell_nonzero : (ell : ℝ) ≠ 0 := by
    exact_mod_cast prime.ne_zero
  have denominator : (ell : ℝ) - 1 ≠ 0 := by
    have large : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
    linarith
  unfold adaptiveMixedActualNormalizedLocalFactor
  rw [adaptiveMixedActualLocalSelectors_card_outside primes outside]
  push_cast [Nat.cast_sub prime.one_le]
  rw [pow_succ ((ell : ℝ) / ((ell : ℝ) - 1))
    (adaptiveMixedOutcomeActiveIndices support scale outcome).card]
  field_simp

/-- At every unsupported prime ABOVE the physical scale, the actual
arbitrary-rank mixed factor is EXACTLY the previously audited genuine
pure-rank normalized local factor. -/
theorem adaptiveMixedActualNormalizedLocalFactor_large_eq_pure
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) (large : scale < ell)
    (rank_large :
      2 ≤ (adaptiveMixedOutcomeActiveIndices support scale outcome).card) :
    adaptiveMixedActualNormalizedLocalFactor support scale ell outcome =
      primeRankNormalizedLocalFactor
        (adaptiveMixedOutcomeActiveIndices support scale outcome).card ell := by
  let rank := (adaptiveMixedOutcomeActiveIndices
    support scale outcome).card
  have rank_bounded :=
    adaptiveMixedOutcomeActiveIndices_card_le_scale
      support scale outcome
  have rank_small : rank < ell := by
    dsimp [rank]
    omega
  unfold adaptiveMixedActualNormalizedLocalFactor
    primeRankNormalizedLocalFactor
  rw [adaptiveMixedActualLocalSelectors_card_large
    primes outside large,
    primeRankLocalPairs_card_large rank_large rank_small]

/-- The genuine large-prime mixed local deficit is quadratic, with the
same rank-dependent inverse-square bound as the audited pure pattern. -/
theorem adaptiveMixedActualNormalizedLocalFactor_large_inverse_square_lower
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) (large : scale < ell)
    (rank_large :
      2 ≤ (adaptiveMixedOutcomeActiveIndices support scale outcome).card) :
    1 - (((((adaptiveMixedOutcomeActiveIndices
      support scale outcome).card - 1 : ℕ) : ℝ) ^ 2) /
        ((ell : ℝ) - 1) ^ 2) ≤
          adaptiveMixedActualNormalizedLocalFactor
            support scale ell outcome := by
  let rank := (adaptiveMixedOutcomeActiveIndices
    support scale outcome).card
  have rank_bounded :=
    adaptiveMixedOutcomeActiveIndices_card_le_scale
      support scale outcome
  have rank_small : rank < ell := by
    dsimp [rank]
    omega
  rw [adaptiveMixedActualNormalizedLocalFactor_large_eq_pure
    primes outside large rank_large]
  exact primeRankNormalizedLocalFactor_large_inverse_square_lower
    rank_large rank_small

/-- Every finite product of ACTUAL mixed local factors is strictly
positive, with no omitted local obstruction or vacuous selector. -/
theorem adaptiveMixedActualNormalizedLocalFactor_finite_product_pos
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (support_primes : ∀ prime ∈ support, prime.Prime)
    (evaluation : Finset ℕ)
    (evaluation_primes : ∀ ell ∈ evaluation, ell.Prime) :
    0 < ∏ ell ∈ evaluation,
      adaptiveMixedActualScalarLocalFactor support scale ell outcome := by
  classical
  apply Finset.prod_pos
  intro ell selected
  have prime := evaluation_primes ell selected
  simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
  exact @adaptiveMixedActualNormalizedLocalFactor_pos
    support scale ell outcome ⟨prime⟩ support_primes

/-- The ENTIRE genuine mixed large-prime tail has the same UNIFORM
rank-dependent positive floor as the pure-rank Euler product.  Supported
primes can occur arbitrarily far out, but their factors are at least one. -/
theorem adaptiveMixedActualNormalizedLocalFactor_tail_product_lower
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (support_primes : ∀ prime ∈ support, prime.Prime)
    (rank_large :
      2 ≤ (adaptiveMixedOutcomeActiveIndices support scale outcome).card)
    (evaluation : Finset ℕ)
    (evaluation_primes : ∀ ell ∈ evaluation, ell.Prime)
    (cutoff : ∀ ell ∈ evaluation,
      max scale
        (2 * ((adaptiveMixedOutcomeActiveIndices
          support scale outcome).card - 1)) + 1 ≤ ell) :
    ((1 / 2 : ℝ) ^
      ((adaptiveMixedOutcomeActiveIndices
        support scale outcome).card - 1)) ≤
      ∏ ell ∈ evaluation,
        adaptiveMixedActualScalarLocalFactor
          support scale ell outcome := by
  classical
  let rank := (adaptiveMixedOutcomeActiveIndices
    support scale outcome).card
  let unsupported := evaluation.filter fun ell => ell ∉ support
  let supported := evaluation.filter fun ell => ell ∈ support
  have split : evaluation = unsupported ∪ supported := by
    ext ell
    constructor
    · intro selected
      by_cases member : ell ∈ support
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨selected, member⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨selected, member⟩)
    · intro selected
      rcases Finset.mem_union.mp selected with outside | inside
      · exact (Finset.mem_filter.mp outside).1
      · exact (Finset.mem_filter.mp inside).1
  have disjoint : Disjoint unsupported supported := by
    apply Finset.disjoint_left.mpr
    intro ell outside inside
    exact (Finset.mem_filter.mp outside).2
      (Finset.mem_filter.mp inside).2
  have pure_tail :
      ((1 / 2 : ℝ) ^ (rank - 1)) ≤
        ∏ ell ∈ unsupported, primeRankScalarLocalFactor rank ell := by
    apply primeRankNormalizedLocalFactor_tail_product_lower
      rank rank_large unsupported
    · intro ell selected
      exact evaluation_primes ell (Finset.mem_filter.mp selected).1
    · intro ell selected
      have bound := cutoff ell (Finset.mem_filter.mp selected).1
      dsimp [rank] at bound ⊢
      omega
  have outside_equal :
      (∏ ell ∈ unsupported, primeRankScalarLocalFactor rank ell) =
        ∏ ell ∈ unsupported,
          adaptiveMixedActualScalarLocalFactor
            support scale ell outcome := by
    apply Finset.prod_congr rfl
    intro ell selected
    obtain ⟨evaluated, outside⟩ := Finset.mem_filter.mp selected
    have prime := evaluation_primes ell evaluated
    have bound := cutoff ell evaluated
    have large : scale < ell := by omega
    simp only [primeRankScalarLocalFactor,
      adaptiveMixedActualScalarLocalFactor, dif_pos prime]
    exact (@adaptiveMixedActualNormalizedLocalFactor_large_eq_pure
      support scale ell outcome ⟨prime⟩
      support_primes outside large rank_large).symm
  have supported_lower :
      (1 : ℝ) ≤ ∏ ell ∈ supported,
        adaptiveMixedActualScalarLocalFactor
          support scale ell outcome := by
    apply Finset.one_le_prod₀
    intro ell selected
    obtain ⟨evaluated, member⟩ := Finset.mem_filter.mp selected
    have prime := evaluation_primes ell evaluated
    simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
    exact @adaptiveMixedActualNormalizedLocalFactor_supported_ge_one
      support scale ell outcome ⟨prime⟩ support_primes member
  have outside_nonnegative :
      0 ≤ ∏ ell ∈ unsupported,
        adaptiveMixedActualScalarLocalFactor
          support scale ell outcome := by
    exact (adaptiveMixedActualNormalizedLocalFactor_finite_product_pos
      support scale outcome support_primes unsupported
        (fun ell selected =>
          evaluation_primes ell (Finset.mem_filter.mp selected).1)).le
  rw [split, Finset.prod_union disjoint]
  calc
    ((1 / 2 : ℝ) ^ (rank - 1)) ≤
        ∏ ell ∈ unsupported, primeRankScalarLocalFactor rank ell := pure_tail
    _ = ∏ ell ∈ unsupported,
        adaptiveMixedActualScalarLocalFactor
          support scale ell outcome := outside_equal
    _ ≤ (∏ ell ∈ unsupported,
        adaptiveMixedActualScalarLocalFactor support scale ell outcome) *
        (∏ ell ∈ supported,
          adaptiveMixedActualScalarLocalFactor support scale ell outcome) := by
      simpa using mul_le_mul_of_nonneg_left supported_lower outside_nonnegative

/-- The finite pattern-dependent exceptional-prime floor clips every
actual local density at one, preventing any arbitrary evaluation support
from reducing its uniform global lower bound. -/
noncomputable def adaptiveMixedActualExceptionalLocalFloor
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) : ℝ :=
  ∏ ell ∈ Nat.primesLE
      (max scale
        (2 * ((adaptiveMixedOutcomeActiveIndices
          support scale outcome).card - 1))),
    min 1 (adaptiveMixedActualScalarLocalFactor
      support scale ell outcome)

/-- The finite exceptional-prime floor of EVERY actual mixed pattern is
strictly positive; this uses genuine all-prime affine admissibility. -/
theorem adaptiveMixedActualExceptionalLocalFloor_pos
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (support_primes : ∀ prime ∈ support, prime.Prime) :
    0 < adaptiveMixedActualExceptionalLocalFloor support scale outcome := by
  unfold adaptiveMixedActualExceptionalLocalFloor
  apply Finset.prod_pos
  intro ell selected
  have prime := Nat.prime_of_mem_primesLE selected
  have factor_positive :
      0 < adaptiveMixedActualScalarLocalFactor
        support scale ell outcome := by
    simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
    exact @adaptiveMixedActualNormalizedLocalFactor_pos
      support scale ell outcome ⟨prime⟩ support_primes
  exact lt_min (by norm_num) factor_positive

/-- FULL collision-aware mixed singular-product lower bound: one explicit
strictly positive PATTERN-dependent constant works for EVERY finite set
of genuine local evaluation primes, regardless of its size or support. -/
theorem adaptiveMixedActualNormalizedLocalFactor_full_support_lower
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (support_primes : ∀ prime ∈ support, prime.Prime)
    (rank_large :
      2 ≤ (adaptiveMixedOutcomeActiveIndices support scale outcome).card)
    (evaluation : Finset ℕ)
    (evaluation_primes : ∀ ell ∈ evaluation, ell.Prime) :
    adaptiveMixedActualExceptionalLocalFloor support scale outcome *
      ((1 / 2 : ℝ) ^
        ((adaptiveMixedOutcomeActiveIndices
          support scale outcome).card - 1)) ≤
        ∏ ell ∈ evaluation,
          adaptiveMixedActualScalarLocalFactor
            support scale ell outcome := by
  classical
  let rank := (adaptiveMixedOutcomeActiveIndices
    support scale outcome).card
  let cutoff := max scale (2 * (rank - 1))
  let initial := evaluation.filter fun ell => ell ≤ cutoff
  let tail := evaluation.filter fun ell => cutoff + 1 ≤ ell
  have split : evaluation = initial ∪ tail := by
    ext ell
    constructor
    · intro selected
      by_cases low : ell ≤ cutoff
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨selected, low⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨selected, by omega⟩)
    · intro selected
      rcases Finset.mem_union.mp selected with low | high
      · exact (Finset.mem_filter.mp low).1
      · exact (Finset.mem_filter.mp high).1
  have disjoint : Disjoint initial tail := by
    apply Finset.disjoint_left.mpr
    intro ell low high
    have low_bound := (Finset.mem_filter.mp low).2
    have high_bound := (Finset.mem_filter.mp high).2
    omega
  have initial_subset : initial ⊆ Nat.primesLE cutoff := by
    intro ell selected
    obtain ⟨evaluated, bounded⟩ := Finset.mem_filter.mp selected
    exact Nat.mem_primesLE.mpr
      ⟨bounded, evaluation_primes ell evaluated⟩
  have initial_lower :
      adaptiveMixedActualExceptionalLocalFloor support scale outcome ≤
        ∏ ell ∈ initial,
          adaptiveMixedActualScalarLocalFactor
            support scale ell outcome := by
    have clipped :
        (∏ ell ∈ Nat.primesLE cutoff,
          min 1 (adaptiveMixedActualScalarLocalFactor
            support scale ell outcome)) ≤
          ∏ ell ∈ initial,
            min 1 (adaptiveMixedActualScalarLocalFactor
              support scale ell outcome) := by
      apply Finset.prod_le_prod_of_subset_of_le_one₀ initial_subset
      · intro ell selected
        have prime := Nat.prime_of_mem_primesLE selected
        have positive :
            0 < adaptiveMixedActualScalarLocalFactor
              support scale ell outcome := by
          simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
          exact @adaptiveMixedActualNormalizedLocalFactor_pos
            support scale ell outcome ⟨prime⟩ support_primes
        exact le_min (by norm_num) positive.le
      · intro ell _selected _missing
        exact min_le_left _ _
    calc
      adaptiveMixedActualExceptionalLocalFloor
          support scale outcome =
        ∏ ell ∈ Nat.primesLE cutoff,
          min 1 (adaptiveMixedActualScalarLocalFactor
            support scale ell outcome) := rfl
      _ ≤ ∏ ell ∈ initial,
          min 1 (adaptiveMixedActualScalarLocalFactor
            support scale ell outcome) := clipped
      _ ≤ ∏ ell ∈ initial,
          adaptiveMixedActualScalarLocalFactor
            support scale ell outcome := by
        apply Finset.prod_le_prod₀
        · intro ell selected
          have evaluated := (Finset.mem_filter.mp selected).1
          have prime := evaluation_primes ell evaluated
          have positive :
              0 < adaptiveMixedActualScalarLocalFactor
                support scale ell outcome := by
            simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
            exact @adaptiveMixedActualNormalizedLocalFactor_pos
              support scale ell outcome ⟨prime⟩ support_primes
          exact le_min (by norm_num) positive.le
        · intro ell _selected
          exact min_le_right _ _
  have tail_lower :
      ((1 / 2 : ℝ) ^ (rank - 1)) ≤
        ∏ ell ∈ tail,
          adaptiveMixedActualScalarLocalFactor
            support scale ell outcome := by
    apply adaptiveMixedActualNormalizedLocalFactor_tail_product_lower
      support scale outcome support_primes rank_large tail
    · intro ell selected
      exact evaluation_primes ell (Finset.mem_filter.mp selected).1
    · intro ell selected
      exact (Finset.mem_filter.mp selected).2
  have initial_nonnegative :
      0 ≤ ∏ ell ∈ initial,
        adaptiveMixedActualScalarLocalFactor
          support scale ell outcome := by
    exact (adaptiveMixedActualNormalizedLocalFactor_finite_product_pos
      support scale outcome support_primes initial
        (fun ell selected =>
          evaluation_primes ell (Finset.mem_filter.mp selected).1)).le
  rw [split, Finset.prod_union disjoint]
  exact mul_le_mul initial_lower tail_lower (by positivity)
    initial_nonnegative

/-- For EVERY fixed actual mixed outcome of genuine rank at least two,
there is ONE strictly positive constant uniformly bounding below ALL
finite products of its ACTUAL normalized local factors over arbitrary
genuine evaluation-prime supports. -/
theorem adaptiveMixedActualNormalizedLocalFactor_uniform_positive
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (support_primes : ∀ prime ∈ support, prime.Prime)
    (rank_large :
      2 ≤ (adaptiveMixedOutcomeActiveIndices support scale outcome).card) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ evaluation : Finset ℕ,
        (∀ ell ∈ evaluation, ell.Prime) →
          constant ≤ ∏ ell ∈ evaluation,
            adaptiveMixedActualScalarLocalFactor
              support scale ell outcome := by
  refine ⟨adaptiveMixedActualExceptionalLocalFloor
    support scale outcome *
      ((1 / 2 : ℝ) ^
        ((adaptiveMixedOutcomeActiveIndices
          support scale outcome).card - 1)), ?_, ?_⟩
  · exact mul_pos
      (adaptiveMixedActualExceptionalLocalFloor_pos
        support scale outcome support_primes)
      (by positivity)
  · intro evaluation evaluation_primes
    exact adaptiveMixedActualNormalizedLocalFactor_full_support_lower
      support scale outcome support_primes rank_large
      evaluation evaluation_primes


end Erdos1139
