module

public import AdaptiveMixedPublishedGTZCapstone1139
public import AdaptiveMixedSignedDomainGeometry1139
public import AdaptivePrimeProgressionStrength1139

@[expose] public section


/-!
# The #1139 prime-pattern premise implies arbitrarily long prime progressions

The original-field portion of the exact #1139 Green--Tao--Ziegler premise
already has at least the strength of the Green--Tao prime-progression
theorem.  This module decodes an authentic signed positive-volume physical
cell into natural-number prime arithmetic progressions; no artificial
positive-center lattice, zero-volume window, or unproved Euler positivity is
used.

The result is CONDITIONAL on the exact remaining published prime-pattern
proposition.  It does not prove either that proposition or Erdős #1139.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1139

/-- A genuine OPEN convex rectangle strictly inside the actual base-zero
signed fundamental strip.  Its center window shrinks by the TRUE SQUARED
support modulus, rather than silently replacing that modulus by one. -/
def adaptivePrimeProgressionPhysicalDomain
    (support : Finset ℕ) : Set (ℝ × ℝ) :=
  Set.Ioo (1 : ℝ) 2 ×ˢ
    Set.Ioo (0 : ℝ) (1 / (adaptiveMixedTypeModulus support : ℝ))

/-- The concrete source-faithful progression window is convex. -/
theorem adaptivePrimeProgressionPhysicalDomain_convex
    (support : Finset ℕ) :
    Convex ℝ (adaptivePrimeProgressionPhysicalDomain support) := by
  exact (convex_Ioo (1 : ℝ) 2).prod
    (convex_Ioo (0 : ℝ) (1 / (adaptiveMixedTypeModulus support : ℝ)))

/-- The concrete source-faithful progression window is open. -/
theorem adaptivePrimeProgressionPhysicalDomain_isOpen
    (support : Finset ℕ) :
    IsOpen (adaptivePrimeProgressionPhysicalDomain support) := by
  exact isOpen_Ioo.prod isOpen_Ioo

/-- The progression window has an actual interior point at every genuine
prime support; it is not a vacuous or measure-zero specialization. -/
theorem adaptivePrimeProgressionPhysicalDomain_nonempty
    (support : Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (adaptivePrimeProgressionPhysicalDomain support).Nonempty := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have reciprocal_positive :
      (0 : ℝ) < 1 / (adaptiveMixedTypeModulus support : ℝ) :=
    one_div_pos.mpr modulus_positive
  refine ⟨((3 / 2 : ℝ),
    (1 / (adaptiveMixedTypeModulus support : ℝ)) / 2), ?_⟩
  change
    (1 < (3 / 2 : ℝ) ∧ (3 / 2 : ℝ) < 2) ∧
      (0 < (1 / (adaptiveMixedTypeModulus support : ℝ)) / 2 ∧
        (1 / (adaptiveMixedTypeModulus support : ℝ)) / 2 <
          1 / (adaptiveMixedTypeModulus support : ℝ))
  constructor
  · norm_num
  · constructor <;> linarith

/-- Every point of the concrete rectangle belongs to the TRUE signed
fundamental strip with physical base zero. -/
theorem adaptivePrimeProgressionPhysicalDomain_subset_actual
    (support : Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    adaptivePrimeProgressionPhysicalDomain support ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support 0 := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  intro point selected
  obtain ⟨⟨lower, upper⟩, center_positive, center_upper⟩ := selected
  have product_upper :
      point.2 * (adaptiveMixedTypeModulus support : ℝ) < 1 :=
    (lt_div_iff₀ modulus_positive).mp center_upper
  simp only [adaptiveMixedSignedOriginalPhysicalDomain, Set.mem_ofPred_eq,
    Nat.cast_zero, zero_mul, zero_add]
  refine ⟨lower, upper, mul_pos modulus_positive center_positive, ?_⟩
  nlinarith

/-- The exact rectangle has strictly positive finite genuine two-dimensional
Lebesgue volume. -/
theorem adaptivePrimeProgressionPhysicalDomain_volume_pos
    (support : Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    0 < (volume (adaptivePrimeProgressionPhysicalDomain support)).toReal := by
  exact adaptiveMixedSignedOriginalConvexDomain_volume_toReal_pos
    support 0 (adaptivePrimeProgressionPhysicalDomain support) primes
    (adaptivePrimeProgressionPhysicalDomain_convex support)
    (adaptivePrimeProgressionPhysicalDomain_isOpen support)
    (adaptivePrimeProgressionPhysicalDomain_nonempty support primes)
    (adaptivePrimeProgressionPhysicalDomain_subset_actual support primes)

/-- The already-proved canonical positive Euler product turns the original
counting field into genuine prime realizations on ALL sufficiently large
scales in this concrete positive-volume signed window. -/
theorem adaptivePrimeProgressionPhysicalDomain_eventually_nonempty
    (counts : HasFixedSignedMixedPrimeCountingAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (zero_base : outcome.1 = 0) :
    ∀ᶠ N : ℕ in atTop,
      (adaptiveMixedSignedOriginalPrimeRealizations
        support scale outcome
          (adaptivePrimeProgressionPhysicalDomain support) N).Nonempty := by
  apply scaleAdaptiveSignedOriginalPrimeRealizations_eventually_nonempty
    (fixed_signed_GTZ_of_prime_counting_asymptotics counts)
    support scale outcome (adaptivePrimeProgressionPhysicalDomain support)
    primes (adaptivePrimeProgressionPhysicalDomain_convex support)
    (adaptivePrimeProgressionPhysicalDomain_isOpen support)
    (adaptivePrimeProgressionPhysicalDomain_nonempty support primes)
    (by simpa [zero_base] using
      adaptivePrimeProgressionPhysicalDomain_subset_actual support primes)
    (adaptivePrimeProgressionPhysicalDomain_volume_pos support primes)

/-- Every index `1+jW` has EXACTLY prime type one at physical base zero;
the squared support modulus is retained in this gcd calculation. -/
theorem adaptivePrimeProgression_index_type_one
    (support : Finset ℕ) (index : ℕ) :
    adaptiveMixedActualIndexType support 0
      (1 + index * adaptiveMixedTypeModulus support) = 1 := by
  simp [adaptiveMixedActualIndexType]

/-- The true signed integral prime form on the embedded physical-index
progression has EXACTLY the advertised affine arithmetic-progression shape. -/
theorem adaptivePrimeProgression_index_integerForm
    (support : Finset ℕ) (index label : ℕ) (center : ℤ) :
    weightedPrimePatternIntegerForm support 0
        (1 + index * adaptiveMixedTypeModulus support) label center =
      ((1 + index * adaptiveMixedTypeModulus support : ℕ) : ℤ) *
        (label : ℤ) +
        (adaptiveMixedTypeModulus support : ℤ) * center := by
  simp [weightedPrimePatternIntegerForm,
    adaptivePrimeProgression_index_type_one]

/-- Decoding theorem: whenever ONE authentic base-zero outcome retains the
physical progression `1+jW`, the original signed prime-counting premise
produces a genuine natural-number arithmetic progression of prime numbers.
Its strictly positive common difference is the actual `W * primeLabel`. -/
theorem adaptivePrimeProgression_exists_of_actual_active_progression
    (counts : HasFixedSignedMixedPrimeCountingAsymptotics)
    (length : ℕ) (positive : 0 < length)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (zero_base : outcome.1 = 0)
    (active : ∀ index < length,
      1 + index * adaptiveMixedTypeModulus support ∈
        adaptiveMixedOutcomeActiveIndices support scale outcome) :
    ∃ first difference : ℕ, 0 < difference ∧
      ∀ index < length, (first + index * difference).Prime := by
  classical
  obtain ⟨N, realized⟩ :=
    (adaptivePrimeProgressionPhysicalDomain_eventually_nonempty
      counts support scale outcome primes zero_base).exists
  obtain ⟨point, selected⟩ := realized
  obtain ⟨_boxed, edge, _physical⟩ := Finset.mem_filter.mp selected
  obtain ⟨prime_label, _window, _residue_nonnegative,
    _residue_upper, all_forms⟩ :=
      weightedPrimePatternEdges_prime_certificate support scale outcome
        (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
          point.1 point.2 edge
  have first_active : 1 ∈
      adaptiveMixedOutcomeActiveIndices support scale outcome := by
    simpa using active 0 positive
  have first_form_positive := (all_forms 1 first_active).2.1
  have first_form_shape :
      weightedPrimePatternIntegerForm support outcome.1 1
        point.1 point.2 =
          (point.1 : ℤ) +
            (adaptiveMixedTypeModulus support : ℤ) * point.2 := by
    rw [zero_base]
    simpa using adaptivePrimeProgression_index_integerForm
      support 0 point.1 point.2
  let first : ℕ :=
    ((point.1 : ℤ) +
      (adaptiveMixedTypeModulus support : ℤ) * point.2).toNat
  let difference : ℕ := adaptiveMixedTypeModulus support * point.1
  have first_cast :
      (first : ℤ) = (point.1 : ℤ) +
        (adaptiveMixedTypeModulus support : ℤ) * point.2 := by
    dsimp [first]
    apply Int.toNat_of_nonneg
    rw [← first_form_shape]
    exact first_form_positive.le
  refine ⟨first, difference,
    Nat.mul_pos (adaptiveMixedTypeModulus_pos support primes)
      prime_label.pos, ?_⟩
  intro index small
  have retained := active index small
  have certificate := all_forms
    (1 + index * adaptiveMixedTypeModulus support) retained
  have target_shape :
      weightedPrimePatternIntegerForm support outcome.1
        (1 + index * adaptiveMixedTypeModulus support)
          point.1 point.2 =
            ((first + index * difference : ℕ) : ℤ) := by
    rw [zero_base, adaptivePrimeProgression_index_integerForm]
    push_cast
    rw [first_cast]
    dsimp [difference]
    ring
  have target_nat :
      (weightedPrimePatternIntegerForm support outcome.1
        (1 + index * adaptiveMixedTypeModulus support)
          point.1 point.2).toNat = first + index * difference := by
    rw [target_shape]
    exact Int.toNat_natCast _
  rw [← target_nat]
  exact certificate.2.2

/-- The exact original-field #1139 prime-counting premise implies genuine
prime arithmetic progressions of EVERY prescribed finite length.  All
targets come from one actual signed prime realization and all progression
indices are retained by one authentic CRT-coded mixed outcome. -/
theorem adaptivePrimeProgression_of_fixed_signed_prime_counts
    (counts : HasFixedSignedMixedPrimeCountingAsymptotics)
    (length : ℕ) :
    ∃ first difference : ℕ, 0 < difference ∧
      ∀ index < length, (first + index * difference).Prime := by
  by_cases positive : 0 < length
  · obtain ⟨outcome, zero_base, active⟩ :=
      adaptivePrimeProgression_exists_active_index_progression length positive
    exact adaptivePrimeProgression_exists_of_actual_active_progression
      counts length positive (Nat.primesLE length)
      (1 + (length - 1) *
        adaptiveMixedTypeModulus (Nat.primesLE length))
      outcome (fun _ selected => Nat.prime_of_mem_primesLE selected)
      zero_base active
  · have zero : length = 0 := Nat.eq_zero_of_not_pos positive
    refine ⟨2, 1, by norm_num, ?_⟩
    intro index small
    omega

/-- The ONE remaining source-faithful published unrestricted von-Mangoldt
premise for #1139 already implies the full arbitrary-length Green--Tao prime
arithmetic-progression conclusion.  Hence discharging this premise from PNT
or a fixed three-prime result would itself formalize Green--Tao strength. -/
theorem adaptivePrimeProgression_of_published_von_mangoldt
    (published : HasFixedSignedMixedPublishedVonMangoldtAsymptotics)
    (length : ℕ) :
    ∃ first difference : ℕ, 0 < difference ∧
      ∀ index < length, (first + index * difference).Prime := by
  exact adaptivePrimeProgression_of_fixed_signed_prime_counts
    (fixed_signed_prime_counting_asymptotics_of_published_von_mangoldt
      published) length

end Erdos1139

