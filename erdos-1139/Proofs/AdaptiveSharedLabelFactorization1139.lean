module

public import AdaptiveMixedPairedSingularPositive1139

@[expose] public section


/-!
# Exact ACTUAL shared-label mixed singular factorization

Two independently sampled mixed outcomes share ONE genuine prime-label form,
while retaining two separate signed-center coordinates and every target form.
At a prime `ell`, normalize both center coordinates by the SAME nonzero label.
The exact resulting selector cardinality is

    (ell-1) * ell * ell                         if ell belongs to the support,
    (ell-1) * (ell-r_1) * (ell-r_2)            otherwise,

where each `r_i` counts DISTINCT actual forbidden slopes, not physical indices.
Thus the normalized actual three-coordinate shared-label factor is exactly the
product of the two individual collision-aware mixed factors, including ranks
zero and one and independently sampled outside residues.

No target covariance, global prime-count theorem, new mathematical axiom, or
resolution of Erdős #1139 is claimed.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos1139

/-- The genuine local center choices for ONE actual mixed outcome after its
nonzero prime label has been normalized to one. -/
noncomputable def adaptiveMixedActualUnitLabelCenters
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime] : Finset (ZMod ell) :=
  Finset.univ.filter fun center =>
    ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
      adaptiveMixedActualAffineForm
        support outcome.1 index ell 1 center ≠ 0

/-- Exact normalized-center membership retains EVERY genuine physical mixed
target form of the one common outcome. -/
theorem mem_adaptiveMixedActualUnitLabelCenters
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime] (center : ZMod ell) :
    center ∈ adaptiveMixedActualUnitLabelCenters
      support scale ell outcome ↔
        ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
          adaptiveMixedActualAffineForm
            support outcome.1 index ell 1 center ≠ 0 := by
  simp [adaptiveMixedActualUnitLabelCenters]

/-- At a supported squared-core prime, EVERY normalized center is genuinely
admissible, for all actual mixed target types and all retained ranks. -/
theorem adaptiveMixedActualUnitLabelCenters_supported_eq_univ
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support) :
    adaptiveMixedActualUnitLabelCenters
      support scale ell outcome = Finset.univ := by
  ext center
  simp only [mem_adaptiveMixedActualUnitLabelCenters, Finset.mem_univ,
    iff_true]
  intro index active
  exact (adaptiveMixed_supported_affine_nonzero_iff_label_nonzero
    primes supported active 1 center).mpr one_ne_zero

/-- At an unsupported prime, the genuine normalized center choices are
EXACTLY the complement of the deduplicated actual forbidden affine slopes. -/
theorem adaptiveMixedActualUnitLabelCenters_outside_eq_sdiff
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) :
    adaptiveMixedActualUnitLabelCenters support scale ell outcome =
      Finset.univ \
        adaptiveMixedOutcomeLocalForbidden support scale ell outcome := by
  ext center
  rw [mem_adaptiveMixedActualUnitLabelCenters,
    Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro avoids selected
    obtain ⟨index, active, zero⟩ :=
      (mem_adaptiveMixedOutcomeLocalForbidden_iff
        primes outside center).mp selected
    exact avoids index active zero
  · intro avoids index active zero
    exact avoids ((mem_adaptiveMixedOutcomeLocalForbidden_iff
      primes outside center).mpr ⟨index, active, zero⟩)

/-- EXACT supported-prime normalized-center cardinality. -/
theorem adaptiveMixedActualUnitLabelCenters_card_supported
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support) :
    (adaptiveMixedActualUnitLabelCenters
      support scale ell outcome).card = ell := by
  rw [adaptiveMixedActualUnitLabelCenters_supported_eq_univ
    primes supported]
  simp

/-- EXACT outside-prime normalized-center cardinality, retaining all actual
root collisions of the one shared outcome. -/
theorem adaptiveMixedActualUnitLabelCenters_card_outside
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) :
    (adaptiveMixedActualUnitLabelCenters
      support scale ell outcome).card =
        ell -
          (adaptiveMixedOutcomeLocalForbidden
            support scale ell outcome).card := by
  rw [adaptiveMixedActualUnitLabelCenters_outside_eq_sdiff
    primes outside,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- Exact actual shared-label selector membership retains ONE common nonzero
label, BOTH independently signed centers, and every target form on both sides. -/
theorem mem_adaptiveMixedSharedLabelLocalSelectors
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ) [Fact ell.Prime]
    (label firstCenter secondCenter : ZMod ell) :
    (label, firstCenter, secondCenter) ∈
      adaptiveMixedSharedLabelLocalSelectors
        support scale ell first second ↔
      label ≠ 0 ∧
        (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale first,
          adaptiveMixedActualAffineForm
            support first.1 index ell label firstCenter ≠ 0) ∧
        (∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale second,
          adaptiveMixedActualAffineForm
            support second.1 index ell label secondCenter ≠ 0) := by
  simp [adaptiveMixedSharedLabelLocalSelectors]

/-- Exact bijective shared-label selector cardinality: divide BOTH actual
signed local centers by the SAME common nonzero label. -/
theorem adaptiveMixedSharedLabelLocalSelectors_card_unit_centers
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ) [Fact ell.Prime] :
    (adaptiveMixedSharedLabelLocalSelectors
      support scale ell first second).card =
      (ell - 1) *
        (adaptiveMixedActualUnitLabelCenters
          support scale ell first).card *
        (adaptiveMixedActualUnitLabelCenters
          support scale ell second).card := by
  classical
  let normalized :=
    (Finset.univ.erase (0 : ZMod ell)).product
      ((adaptiveMixedActualUnitLabelCenters
        support scale ell first).product
       (adaptiveMixedActualUnitLabelCenters
        support scale ell second))
  have bijection :
      (adaptiveMixedSharedLabelLocalSelectors
        support scale ell first second).card = normalized.card := by
    apply Finset.card_bij
      (fun triple _ =>
        (triple.1, (triple.2.1 / triple.1, triple.2.2 / triple.1)))
    · intro triple selected
      obtain ⟨nonzero, first_forms, second_forms⟩ :=
        (mem_adaptiveMixedSharedLabelLocalSelectors
          support scale ell first second
            triple.1 triple.2.1 triple.2.2).mp selected
      dsimp [normalized]
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_erase.mpr
        ⟨nonzero, Finset.mem_univ _⟩, ?_⟩
      apply Finset.mem_product.mpr
      constructor
      · apply (mem_adaptiveMixedActualUnitLabelCenters
          support scale ell first (triple.2.1 / triple.1)).mpr
        intro index active
        exact (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support first.1 index ell triple.1 triple.2.1 nonzero).mp
            (first_forms index active)
      · apply (mem_adaptiveMixedActualUnitLabelCenters
          support scale ell second (triple.2.2 / triple.1)).mpr
        intro index active
        exact (adaptiveMixedActualAffineForm_normalized_nonzero_iff
          support second.1 index ell triple.1 triple.2.2 nonzero).mp
            (second_forms index active)
    · intro first_triple first_selected second_triple _second_selected equal
      have same_label := congrArg Prod.fst equal
      have same_first := congrArg
        (fun triple : ZMod ell × ZMod ell × ZMod ell => triple.2.1) equal
      have same_second := congrArg
        (fun triple : ZMod ell × ZMod ell × ZMod ell => triple.2.2) equal
      change first_triple.1 = second_triple.1 at same_label
      change first_triple.2.1 / first_triple.1 =
        second_triple.2.1 / second_triple.1 at same_first
      change first_triple.2.2 / first_triple.1 =
        second_triple.2.2 / second_triple.1 at same_second
      rw [← same_label] at same_first same_second
      have nonzero :=
        (mem_adaptiveMixedSharedLabelLocalSelectors
          support scale ell first second first_triple.1
            first_triple.2.1 first_triple.2.2).mp first_selected |>.1
      apply Prod.ext same_label
      apply Prod.ext
      · exact (div_left_inj' nonzero).mp same_first
      · exact (div_left_inj' nonzero).mp same_second
    · intro triple selected
      obtain ⟨label_selected, centers_selected⟩ :=
        Finset.mem_product.mp selected
      obtain ⟨first_selected, second_selected⟩ :=
        Finset.mem_product.mp centers_selected
      have nonzero := (Finset.mem_erase.mp label_selected).1
      refine ⟨(triple.1, triple.2.1 * triple.1,
        triple.2.2 * triple.1), ?_, ?_⟩
      · apply (mem_adaptiveMixedSharedLabelLocalSelectors
          support scale ell first second triple.1
            (triple.2.1 * triple.1)
            (triple.2.2 * triple.1)).mpr
        refine ⟨nonzero, ?_, ?_⟩
        · intro index active
          apply (adaptiveMixedActualAffineForm_normalized_nonzero_iff
            support first.1 index ell triple.1
              (triple.2.1 * triple.1) nonzero).mpr
          have normalized_first :
              triple.2.1 * triple.1 / triple.1 = triple.2.1 := by
            field_simp
          rw [normalized_first]
          exact (mem_adaptiveMixedActualUnitLabelCenters
            support scale ell first triple.2.1).mp
              first_selected index active
        · intro index active
          apply (adaptiveMixedActualAffineForm_normalized_nonzero_iff
            support second.1 index ell triple.1
              (triple.2.2 * triple.1) nonzero).mpr
          have normalized_second :
              triple.2.2 * triple.1 / triple.1 = triple.2.2 := by
            field_simp
          rw [normalized_second]
          exact (mem_adaptiveMixedActualUnitLabelCenters
            support scale ell second triple.2.2).mp
              second_selected index active
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · change triple.2.1 * triple.1 / triple.1 = triple.2.1
            field_simp
          · change triple.2.2 * triple.1 / triple.1 = triple.2.2
            field_simp
  rw [bijection]
  dsimp [normalized]
  rw [Finset.card_product, Finset.card_product]
  simp
  ring

/-- EXACT actual supported-prime shared-label selector cardinality.  The
common label is counted ONCE and both genuine signed local centers are free. -/
theorem adaptiveMixedSharedLabelLocalSelectors_card_supported
    {support : Finset ℕ} {scale ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support) :
    (adaptiveMixedSharedLabelLocalSelectors
      support scale ell first second).card =
        (ell - 1) * ell * ell := by
  rw [adaptiveMixedSharedLabelLocalSelectors_card_unit_centers,
    adaptiveMixedActualUnitLabelCenters_card_supported primes supported,
    adaptiveMixedActualUnitLabelCenters_card_supported primes supported]

/-- EXACT actual outside-prime shared-label selector cardinality.  Both
independently sampled outcomes keep their own DISTINCT-root counts, with no
root-independence assumption and no equality of their outside residues. -/
theorem adaptiveMixedSharedLabelLocalSelectors_card_outside
    {support : Finset ℕ} {scale ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) :
    (adaptiveMixedSharedLabelLocalSelectors
      support scale ell first second).card =
        (ell - 1) *
          (ell - (adaptiveMixedOutcomeLocalForbidden
            support scale ell first).card) *
          (ell - (adaptiveMixedOutcomeLocalForbidden
            support scale ell second).card) := by
  rw [adaptiveMixedSharedLabelLocalSelectors_card_unit_centers,
    adaptiveMixedActualUnitLabelCenters_card_outside primes outside,
    adaptiveMixedActualUnitLabelCenters_card_outside primes outside]

/-- The TRUE normalized Green--Tao factor of the actual three-coordinate
shared-label selector.  Exactly `r+r'+1` distinct prime forms occur: one
genuine shared label and the full two retained physical target branches. -/
noncomputable def adaptiveMixedActualSharedLabelNormalizedLocalFactor
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ) [Fact ell.Prime] : ℝ :=
  sharedTargetSharedNormalizedFactor ell
    (adaptiveMixedOutcomeActiveIndices support scale first).card
    (adaptiveMixedOutcomeActiveIndices support scale second).card
    (adaptiveMixedSharedLabelLocalSelectors
      support scale ell first second).card

/-- Instance-free actual shared-label scalar packaging for arbitrary finite
genuine evaluation-prime supports. -/
noncomputable def adaptiveMixedActualSharedLabelScalarLocalFactor
    (support : Finset ℕ) (scale : ℕ)
    (first second : ℕ × ℕ) (ell : ℕ) : ℝ :=
  if prime : ell.Prime then
    @adaptiveMixedActualSharedLabelNormalizedLocalFactor
      support scale ell first second ⟨prime⟩
  else 0

/-- The TRUE actual shared-label normalized local selector factor is EXACTLY
the product of the two genuine collision-aware individual mixed factors. -/
theorem adaptiveMixedActualSharedLabelNormalizedLocalFactor_eq_product
    {support : Finset ℕ} {scale ell : ℕ}
    {first second : ℕ × ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime) :
    adaptiveMixedActualSharedLabelNormalizedLocalFactor
      support scale ell first second =
        adaptiveMixedActualNormalizedLocalFactor
          support scale ell first *
        adaptiveMixedActualNormalizedLocalFactor
          support scale ell second := by
  have prime : ell.Prime := Fact.out
  by_cases supported : ell ∈ support
  · unfold adaptiveMixedActualSharedLabelNormalizedLocalFactor
    rw [adaptiveMixedSharedLabelLocalSelectors_card_supported
      primes supported]
    calc
      _ = sharedTargetIndividualNormalizedFactor ell
            (adaptiveMixedOutcomeActiveIndices support scale first).card
              ((ell - 1) * ell) *
          sharedTargetIndividualNormalizedFactor ell
            (adaptiveMixedOutcomeActiveIndices support scale second).card
              ((ell - 1) * ell) :=
        sharedTargetNormalizedFactor_product_of_selector_counts
          prime
          (adaptiveMixedOutcomeActiveIndices support scale first).card
          (adaptiveMixedOutcomeActiveIndices support scale second).card
          ell ell
      _ = _ := by
        rw [adaptiveMixedActualNormalizedLocalFactor_eq_shared_normalization
          support scale ell first,
          adaptiveMixedActualNormalizedLocalFactor_eq_shared_normalization
            support scale ell second,
          adaptiveMixedActualLocalSelectors_card_supported
            primes supported,
          adaptiveMixedActualLocalSelectors_card_supported
            primes supported]
  · unfold adaptiveMixedActualSharedLabelNormalizedLocalFactor
    rw [adaptiveMixedSharedLabelLocalSelectors_card_outside
      primes supported]
    calc
      _ = sharedTargetIndividualNormalizedFactor ell
            (adaptiveMixedOutcomeActiveIndices support scale first).card
              ((ell - 1) *
                (ell - (adaptiveMixedOutcomeLocalForbidden
                  support scale ell first).card)) *
          sharedTargetIndividualNormalizedFactor ell
            (adaptiveMixedOutcomeActiveIndices support scale second).card
              ((ell - 1) *
                (ell - (adaptiveMixedOutcomeLocalForbidden
                  support scale ell second).card)) :=
        sharedTargetNormalizedFactor_product_of_selector_counts
          prime
          (adaptiveMixedOutcomeActiveIndices support scale first).card
          (adaptiveMixedOutcomeActiveIndices support scale second).card
          (ell - (adaptiveMixedOutcomeLocalForbidden
            support scale ell first).card)
          (ell - (adaptiveMixedOutcomeLocalForbidden
            support scale ell second).card)
      _ = _ := by
        rw [adaptiveMixedActualNormalizedLocalFactor_eq_shared_normalization
          support scale ell first,
          adaptiveMixedActualNormalizedLocalFactor_eq_shared_normalization
            support scale ell second,
          adaptiveMixedActualLocalSelectors_card_outside
            primes supported,
          adaptiveMixedActualLocalSelectors_card_outside
            primes supported]

/-- Exact instance-free scalar equality at EVERY prime, including supported
and unsupported primes and all ranks zero and one. -/
theorem adaptiveMixedActualSharedLabelScalarLocalFactor_eq_product
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (prime : ell.Prime) :
    adaptiveMixedActualSharedLabelScalarLocalFactor
      support scale first second ell =
        adaptiveMixedActualScalarLocalFactor support scale ell first *
          adaptiveMixedActualScalarLocalFactor support scale ell second := by
  simp only [adaptiveMixedActualSharedLabelScalarLocalFactor,
    adaptiveMixedActualScalarLocalFactor, dif_pos prime]
  exact @adaptiveMixedActualSharedLabelNormalizedLocalFactor_eq_product
    support scale ell first second ⟨prime⟩ primes

/-- The TRUE actual shared-label and same-type shared-target scalar local
factors agree, despite their different actual three-coordinate selectors. -/
theorem adaptiveMixedActualSharedLabelScalarLocalFactor_eq_shared_target
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (prime : ell.Prime) :
    adaptiveMixedActualSharedLabelScalarLocalFactor
      support scale first second ell =
    adaptiveMixedActualSharedTargetScalarLocalFactor
      support scale first second ell := by
  rw [adaptiveMixedActualSharedLabelScalarLocalFactor_eq_product
    support scale ell first second primes prime,
    adaptiveMixedActualSharedTargetScalarLocalFactor_eq_product
      support scale ell first second primes prime]

/-- FULL exact finite ACTUAL shared-label singular-product factorization,
with the common label counted once and all outside-root collisions retained. -/
theorem adaptiveMixedActualSharedLabel_finite_singular_product_eq_product
    (support : Finset ℕ) (scale : ℕ)
    (first second : ℕ × ℕ) (evaluation : Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (evaluation_primes : ∀ ell ∈ evaluation, ell.Prime) :
    (∏ ell ∈ evaluation,
      adaptiveMixedActualSharedLabelScalarLocalFactor
        support scale first second ell) =
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
      exact adaptiveMixedActualSharedLabelScalarLocalFactor_eq_shared_target
        support scale ell first second primes
          (evaluation_primes ell selected)
    _ = _ :=
      adaptiveMixedActualSharedTarget_finite_singular_product_eq_product
        support scale first second evaluation primes evaluation_primes

/-- UNCONDITIONAL support-independent strictly positive singular-product floor
for the TRUE actual shared-label selector at EVERY pair of retained ranks. -/
theorem adaptiveMixedActualSharedLabel_singular_product_uniform_positive
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ evaluation : Finset ℕ,
        (∀ ell ∈ evaluation, ell.Prime) →
          constant ≤ ∏ ell ∈ evaluation,
            adaptiveMixedActualSharedLabelScalarLocalFactor
              support scale first second ell := by
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
      adaptiveMixedActualSharedLabelScalarLocalFactor
        support scale first second ell := by
      apply Finset.prod_congr rfl
      intro ell selected
      exact (adaptiveMixedActualSharedLabelScalarLocalFactor_eq_shared_target
        support scale ell first second primes
          (evaluation_primes ell selected)).symm

end Erdos1139

