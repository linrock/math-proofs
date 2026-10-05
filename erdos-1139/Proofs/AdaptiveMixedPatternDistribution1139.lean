module

public import ScaleAdaptiveConstruction1139
public import AdaptiveSupportIdentity1139

@[expose] public section


/-!
# Exact mixed prime/semiprime type probabilities for Erdős #1139

For a finite genuine prime-type support `S`, the proposed adaptive
construction samples a center modulo

    W = (∏ s ∈ S, s) ^ 2.

Prime-type residues are precisely the units modulo `W`.  A residue has
semiprime type `s ∈ S` precisely when it is `s * k`, with `k` coprime to
`W / s`.  The resulting exact probabilities are

    Pr(prime type) = ∏ s ∈ S, (1 - 1 / s),
    Pr(semiprime type s) = Pr(prime type) / s.

These are finite local center-distribution identities.  They do not prove
prime-pattern existence, moving-prime correlations, a full mixed covering,
or the original Erdős conjecture.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- The squarefree product of the actual selected semiprime types. -/
def adaptiveMixedTypeRadical (support : Finset ℕ) : ℕ :=
  ∏ p ∈ support, p

/-- The TRUE square-power center modulus used by the adaptive mixed
prime/semiprime pattern, not the squarefree pure-prime modulus. -/
def adaptiveMixedTypeModulus (support : Finset ℕ) : ℕ :=
  (adaptiveMixedTypeRadical support) ^ 2

/-- Every genuine prime support has a positive actual radical. -/
theorem adaptiveMixedTypeRadical_pos
    (support : Finset ℕ)
    (primes : ∀ p ∈ support, p.Prime) :
    0 < adaptiveMixedTypeRadical support := by
  unfold adaptiveMixedTypeRadical
  exact Finset.prod_pos fun p selected => (primes p selected).pos

/-- The true squared type modulus is always positive. -/
theorem adaptiveMixedTypeModulus_pos
    (support : Finset ℕ)
    (primes : ∀ p ∈ support, p.Prime) :
    0 < adaptiveMixedTypeModulus support := by
  unfold adaptiveMixedTypeModulus
  exact pow_pos (adaptiveMixedTypeRadical_pos support primes) 2

/-- The actual squarefree type radical has exactly its advertised genuine
prime support. -/
theorem adaptiveMixedTypeRadical_primeFactors
    (support : Finset ℕ)
    (primes : ∀ p ∈ support, p.Prime) :
    (adaptiveMixedTypeRadical support).primeFactors = support := by
  unfold adaptiveMixedTypeRadical
  exact Nat.primeFactors_prod primes

/-- Squaring the actual type radical does not add or delete any prime type. -/
theorem adaptiveMixedTypeModulus_primeFactors
    (support : Finset ℕ)
    (primes : ∀ p ∈ support, p.Prime) :
    (adaptiveMixedTypeModulus support).primeFactors = support := by
  unfold adaptiveMixedTypeModulus
  rw [Nat.primeFactors_pow _ (by norm_num : (2 : ℕ) ≠ 0)]
  exact adaptiveMixedTypeRadical_primeFactors support primes

/-- Every supported prime square divides the genuine center modulus. -/
theorem adaptiveMixedType_square_dvd_modulus
    {support : Finset ℕ} {prime : ℕ}
    (selected : prime ∈ support) :
    prime ^ 2 ∣ adaptiveMixedTypeModulus support := by
  have divides : prime ∣ adaptiveMixedTypeRadical support := by
    unfold adaptiveMixedTypeRadical
    exact Finset.dvd_prod_of_mem (fun value : ℕ => value) selected
  obtain ⟨quotient, factorization⟩ := divides
  refine ⟨quotient ^ 2, ?_⟩
  unfold adaptiveMixedTypeModulus
  rw [factorization]
  ring

/-- In particular, each supported type divides the genuine modulus. -/
theorem adaptiveMixedType_dvd_modulus
    {support : Finset ℕ} {prime : ℕ}
    (selected : prime ∈ support) :
    prime ∣ adaptiveMixedTypeModulus support := by
  exact dvd_trans (dvd_pow_self prime (by norm_num : 2 ≠ 0))
    (adaptiveMixedType_square_dvd_modulus selected)

/-- Dividing the actual squared modulus by a supported type leaves another
copy of that same type, the crucial distinction from a squarefree model. -/
theorem adaptiveMixedType_dvd_modulus_div
    {support : Finset ℕ} {prime : ℕ}
    (selected : prime ∈ support) :
    prime ∣ adaptiveMixedTypeModulus support / prime := by
  apply (Nat.dvd_div_iff_mul_dvd
    (adaptiveMixedType_dvd_modulus selected)).mpr
  simpa [pow_two] using adaptiveMixedType_square_dvd_modulus selected

/-- Removing one copy of ANY supported type retains EVERY supported
prime in the reduced mixed-pattern modulus. -/
theorem adaptiveMixedType_support_dvd_reduced_modulus
    {support : Finset ℕ} {selectedPrime otherPrime : ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (selected : selectedPrime ∈ support)
    (other : otherPrime ∈ support) :
    otherPrime ∣ adaptiveMixedTypeModulus support / selectedPrime := by
  by_cases same : otherPrime = selectedPrime
  · subst otherPrime
    exact adaptiveMixedType_dvd_modulus_div selected
  · have selected_dvd := adaptiveMixedType_dvd_modulus selected
    have factorization :
        selectedPrime *
          (adaptiveMixedTypeModulus support / selectedPrime) =
            adaptiveMixedTypeModulus support :=
      Nat.mul_div_cancel' selected_dvd
    have product_dvd :
        otherPrime ∣ selectedPrime *
          (adaptiveMixedTypeModulus support / selectedPrime) := by
      rw [factorization]
      exact adaptiveMixedType_dvd_modulus other
    rcases (primes otherPrime other).dvd_mul.mp product_dvd with
      divides_selected | divides_reduced
    · have equal : selectedPrime = otherPrime :=
        ((primes selectedPrime selected).dvd_iff_eq
          (primes otherPrime other).ne_one).mp divides_selected
      exact (same equal.symm).elim
    · exact divides_reduced

/-- The exact totient drop when one copy of a supported prime is removed
from its square in the true mixed-pattern modulus. -/
theorem adaptiveMixedType_totient_eq_mul_reduced_totient
    {support : Finset ℕ} {prime : ℕ}
    (selected : prime ∈ support) (prime_is_prime : prime.Prime) :
    (adaptiveMixedTypeModulus support).totient =
      prime * (adaptiveMixedTypeModulus support / prime).totient := by
  have divides := adaptiveMixedType_dvd_modulus selected
  have factorization :
      prime * (adaptiveMixedTypeModulus support / prime) =
        adaptiveMixedTypeModulus support := Nat.mul_div_cancel' divides
  calc
    (adaptiveMixedTypeModulus support).totient =
        (prime * (adaptiveMixedTypeModulus support / prime)).totient :=
      congrArg Nat.totient factorization.symm
    _ = prime * (adaptiveMixedTypeModulus support / prime).totient :=
      Nat.totient_mul_of_prime_of_dvd prime_is_prime
        (adaptiveMixedType_dvd_modulus_div selected)

/-- The exact prime-type residues are the actual units of the true squared
center modulus. -/
def adaptiveMixedPrimeTypeResidues (support : Finset ℕ) : Finset ℕ :=
  (Finset.range (adaptiveMixedTypeModulus support)).filter fun residue =>
    (adaptiveMixedTypeModulus support).Coprime residue

/-- The exact semiprime-type residues retain one and only one copy of the
selected type and avoid every remaining supported prime type. -/
def adaptiveMixedSemiprimeTypeResidues
    (support : Finset ℕ) (prime : ℕ) : Finset ℕ :=
  (Finset.range (adaptiveMixedTypeModulus support)).filter fun residue =>
    prime ∣ residue ∧
      (adaptiveMixedTypeModulus support / prime).Coprime (residue / prime)

/-- The exact prime-type residue count is the totient of the TRUE squared
center modulus. -/
theorem adaptiveMixedPrimeTypeResidues_card
    (support : Finset ℕ) :
    (adaptiveMixedPrimeTypeResidues support).card =
      (adaptiveMixedTypeModulus support).totient := by
  exact (Nat.totient_eq_card_coprime
    (adaptiveMixedTypeModulus support)).symm

/-- A genuine semiprime-type residue cannot contain a second copy of its
declared type. -/
theorem adaptiveMixedSemiprimeTypeResidues_not_square_dvd
    {support : Finset ℕ} {prime residue : ℕ}
    (selected : prime ∈ support) (prime_is_prime : prime.Prime)
    (typed : residue ∈ adaptiveMixedSemiprimeTypeResidues support prime) :
    ¬ prime ^ 2 ∣ residue := by
  obtain ⟨_bounded, divisible, coprime⟩ := Finset.mem_filter.mp typed
  have type_coprime : prime.Coprime (residue / prime) :=
    Nat.Coprime.of_dvd_left
      (adaptiveMixedType_dvd_modulus_div selected) coprime
  intro square
  have divides_quotient : prime ∣ residue / prime := by
    apply (Nat.dvd_div_iff_mul_dvd divisible).mpr
    simpa [pow_two] using square
  exact prime_is_prime.coprime_iff_not_dvd.mp type_coprime divides_quotient

/-- A residue of declared semiprime type `s` is not divisible by ANY
different supported prime type.  This is the true single-type condition,
not merely a valuation-one condition at `s`. -/
theorem adaptiveMixedSemiprimeTypeResidues_no_other_supported_divisor
    {support : Finset ℕ} {selectedPrime otherPrime residue : ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (selected : selectedPrime ∈ support)
    (other : otherPrime ∈ support)
    (different : otherPrime ≠ selectedPrime)
    (typed : residue ∈
      adaptiveMixedSemiprimeTypeResidues support selectedPrime) :
    ¬ otherPrime ∣ residue := by
  obtain ⟨_bounded, divisible, coprime⟩ := Finset.mem_filter.mp typed
  have other_coprime : otherPrime.Coprime (residue / selectedPrime) :=
    Nat.Coprime.of_dvd_left
      (adaptiveMixedType_support_dvd_reduced_modulus
        primes selected other) coprime
  intro divides_residue
  have factorization : selectedPrime * (residue / selectedPrime) = residue :=
    Nat.mul_div_cancel' divisible
  have divides_product :
      otherPrime ∣ selectedPrime * (residue / selectedPrime) := by
    rw [factorization]
    exact divides_residue
  rcases (primes otherPrime other).dvd_mul.mp divides_product with
    divides_selected | divides_quotient
  · have equal : selectedPrime = otherPrime :=
      ((primes selectedPrime selected).dvd_iff_eq
        (primes otherPrime other).ne_one).mp divides_selected
    exact different equal.symm
  · exact (primes otherPrime other).coprime_iff_not_dvd.mp
      other_coprime divides_quotient

/-- The genuine prime-type and every selected semiprime-type residue
classes are disjoint; one target index cannot have both types. -/
theorem adaptiveMixedPrime_semiprime_type_disjoint
    {support : Finset ℕ} {prime : ℕ}
    (selected : prime ∈ support) (prime_is_prime : prime.Prime) :
    Disjoint (adaptiveMixedPrimeTypeResidues support)
      (adaptiveMixedSemiprimeTypeResidues support prime) := by
  apply Finset.disjoint_left.mpr
  intro residue prime_type semi_type
  have core_coprime := (Finset.mem_filter.mp prime_type).2
  have prime_coprime : prime.Coprime residue :=
    Nat.Coprime.of_dvd_left
      (adaptiveMixedType_dvd_modulus selected) core_coprime
  exact prime_is_prime.coprime_iff_not_dvd.mp prime_coprime
    (Finset.mem_filter.mp semi_type).2.1

/-- Distinct genuine semiprime types have disjoint actual residue classes;
their individually computed probabilities are simultaneously compatible. -/
theorem adaptiveMixedDistinct_semiprime_types_disjoint
    {support : Finset ℕ} {first second : ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_selected : first ∈ support)
    (second_selected : second ∈ support)
    (different : first ≠ second) :
    Disjoint (adaptiveMixedSemiprimeTypeResidues support first)
      (adaptiveMixedSemiprimeTypeResidues support second) := by
  apply Finset.disjoint_left.mpr
  intro residue first_type second_type
  exact adaptiveMixedSemiprimeTypeResidues_no_other_supported_divisor
    primes first_selected second_selected different.symm first_type
    (Finset.mem_filter.mp second_type).2.1

/-- Exact semiprime-type cardinality: division by its selected type gives
a genuine bijection with the units of the reduced center modulus. -/
theorem adaptiveMixedSemiprimeTypeResidues_card
    {support : Finset ℕ} {prime : ℕ}
    (selected : prime ∈ support) (prime_is_prime : prime.Prime) :
    (adaptiveMixedSemiprimeTypeResidues support prime).card =
      (adaptiveMixedTypeModulus support / prime).totient := by
  classical
  let modulus := adaptiveMixedTypeModulus support
  let reduced := modulus / prime
  have positive_prime : 0 < prime := prime_is_prime.pos
  have factorization : prime * reduced = modulus :=
    Nat.mul_div_cancel' (adaptiveMixedType_dvd_modulus selected)
  change
    ((Finset.range modulus).filter fun residue =>
      prime ∣ residue ∧ reduced.Coprime (residue / prime)).card =
        reduced.totient
  rw [Nat.totient_eq_card_coprime]
  apply Finset.card_bij (fun residue _ => residue / prime)
  · intro residue member
    obtain ⟨bounded, divisible, coprime⟩ := Finset.mem_filter.mp member
    have factor : prime * (residue / prime) = residue :=
      Nat.mul_div_cancel' divisible
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, coprime⟩
    apply (Nat.mul_lt_mul_left positive_prime).mp
    rw [factor, factorization]
    exact Finset.mem_range.mp bounded
  · intro first first_member second second_member equal
    have first_divides := (Finset.mem_filter.mp first_member).2.1
    have second_divides := (Finset.mem_filter.mp second_member).2.1
    calc
      first = prime * (first / prime) :=
        (Nat.mul_div_cancel' first_divides).symm
      _ = prime * (second / prime) := by rw [equal]
      _ = second := Nat.mul_div_cancel' second_divides
  · intro quotient member
    obtain ⟨bounded, coprime⟩ := Finset.mem_filter.mp member
    have small : quotient < reduced := Finset.mem_range.mp bounded
    refine ⟨prime * quotient, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, dvd_mul_right prime quotient, ?_⟩
      · rw [← factorization]
        exact (Nat.mul_lt_mul_left positive_prime).mpr small
      · simpa [Nat.mul_div_cancel_left quotient positive_prime] using coprime
    · exact Nat.mul_div_cancel_left quotient positive_prime

/-- The prime-type probability is exactly the actual supported Euler
product, with no heuristic replacement of the true squared modulus. -/
theorem adaptiveMixedPrimeType_probability_eq_eulerProduct
    (support : Finset ℕ) (primes : ∀ prime ∈ support, prime.Prime) :
    ((adaptiveMixedPrimeTypeResidues support).card : ℝ) /
      (adaptiveMixedTypeModulus support : ℝ) =
        adaptivePrimeEulerProduct support := by
  rw [adaptiveMixedPrimeTypeResidues_card]
  have nonzero : (adaptiveMixedTypeModulus support : ℚ) ≠ 0 := by
    exact_mod_cast (adaptiveMixedTypeModulus_pos support primes).ne'
  have rational := Nat.totient_eq_mul_prod_factors
    (adaptiveMixedTypeModulus support)
  rw [adaptiveMixedTypeModulus_primeFactors support primes] at rational
  have rational_ratio :
      ((adaptiveMixedTypeModulus support).totient : ℚ) /
          (adaptiveMixedTypeModulus support : ℚ) =
        ∏ prime ∈ support, (1 - (prime : ℚ)⁻¹) := by
    apply (div_eq_iff nonzero).mpr
    simpa [mul_comm] using rational
  have real := congrArg (fun value : ℚ => (value : ℝ)) rational_ratio
  simpa [adaptivePrimeEulerProduct] using real

/-- Exact mixed-pattern type ratio: each genuine semiprime type has
probability precisely `1 / prime` times the prime-type probability. -/
theorem adaptiveMixedSemiprimeType_probability_eq_eulerProduct_div
    {support : Finset ℕ} {prime : ℕ}
    (primes : ∀ p ∈ support, p.Prime)
    (selected : prime ∈ support) :
    ((adaptiveMixedSemiprimeTypeResidues support prime).card : ℝ) /
      (adaptiveMixedTypeModulus support : ℝ) =
        adaptivePrimeEulerProduct support / (prime : ℝ) := by
  have prime_is_prime := primes prime selected
  rw [adaptiveMixedSemiprimeTypeResidues_card selected prime_is_prime]
  have totient := adaptiveMixedType_totient_eq_mul_reduced_totient
    selected prime_is_prime
  have totient_real :
      ((adaptiveMixedTypeModulus support).totient : ℝ) =
        (prime : ℝ) *
          ((adaptiveMixedTypeModulus support / prime).totient : ℝ) := by
    exact_mod_cast totient
  have factor := adaptiveMixedPrimeType_probability_eq_eulerProduct
    support primes
  rw [adaptiveMixedPrimeTypeResidues_card] at factor
  have prime_nonzero : (prime : ℝ) ≠ 0 := by
    exact_mod_cast prime_is_prime.ne_zero
  rw [← factor, totient_real]
  field_simp

/-- Translation by ANY fixed natural index permutes the complete residue
period of a positive actual modulus; no coprimality of the index is needed. -/
theorem adaptiveMixed_periodic_shift_filter_card
    (modulus shift : ℕ) (positive : 0 < modulus)
    (predicate : ℕ → Prop) [DecidablePred predicate] :
    ((Finset.range modulus).filter fun center =>
      predicate ((center + shift) % modulus)).card =
        ((Finset.range modulus).filter predicate).card := by
  classical
  let _ : NeZero modulus := ⟨positive.ne'⟩
  apply Finset.card_bij (fun center _ => (center + shift) % modulus)
  · intro center selected
    obtain ⟨_bounded, accepted⟩ := Finset.mem_filter.mp selected
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mod_lt _ positive), accepted⟩
  · intro first first_selected second second_selected equal
    have first_bounded :=
      Finset.mem_range.mp (Finset.mem_filter.mp first_selected).1
    have second_bounded :=
      Finset.mem_range.mp (Finset.mem_filter.mp second_selected).1
    have shifted :
        (first : ZMod modulus) + (shift : ZMod modulus) =
          (second : ZMod modulus) + (shift : ZMod modulus) := by
      have casted := congrArg (fun residue : ℕ => (residue : ZMod modulus)) equal
      simpa [ZMod.natCast_mod] using casted
    have cancelled : (first : ZMod modulus) = (second : ZMod modulus) :=
      add_right_cancel shifted
    have values := congrArg ZMod.val cancelled
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt first_bounded,
      Nat.mod_eq_of_lt second_bounded] using values
  · intro value selected
    obtain ⟨bounded, accepted⟩ := Finset.mem_filter.mp selected
    have value_bounded : value < modulus := Finset.mem_range.mp bounded
    let center : ℕ :=
      ((value : ZMod modulus) - (shift : ZMod modulus)).val
    have center_bounded : center < modulus :=
      ZMod.val_lt ((value : ZMod modulus) - (shift : ZMod modulus))
    have center_cast :
        (center : ZMod modulus) =
          (value : ZMod modulus) - (shift : ZMod modulus) :=
      ZMod.natCast_zmod_val
        ((value : ZMod modulus) - (shift : ZMod modulus))
    have shifted :
        ((center + shift : ℕ) : ZMod modulus) =
          (value : ZMod modulus) := by
      push_cast
      rw [center_cast]
      abel
    have exact_residue : (center + shift) % modulus = value := by
      have values := congrArg ZMod.val shifted
      simpa [ZMod.val_add, ZMod.val_natCast, Nat.add_mod,
        Nat.mod_eq_of_lt value_bounded] using values
    refine ⟨center, ?_, exact_residue⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr center_bounded,
      by simpa [exact_residue] using accepted⟩

/-- Prime-type centers at a particular genuine target index, with its full
translation modulo the TRUE squared center modulus. -/
def adaptiveMixedPrimeTypeCenters
    (support : Finset ℕ) (index : ℕ) : Finset ℕ :=
  (Finset.range (adaptiveMixedTypeModulus support)).filter fun center =>
    (adaptiveMixedTypeModulus support).Coprime
      ((center + index) % adaptiveMixedTypeModulus support)

/-- Semiprime-type centers at a particular genuine target index, retaining
exactly one factor of the declared type in the shifted residue. -/
def adaptiveMixedSemiprimeTypeCenters
    (support : Finset ℕ) (prime index : ℕ) : Finset ℕ :=
  (Finset.range (adaptiveMixedTypeModulus support)).filter fun center =>
    let residue := (center + index) % adaptiveMixedTypeModulus support
    prime ∣ residue ∧
      (adaptiveMixedTypeModulus support / prime).Coprime (residue / prime)

/-- EVERY individual index has exactly the same genuine prime-type center
count, independently of its location. -/
theorem adaptiveMixedPrimeTypeCenters_card
    (support : Finset ℕ) (index : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (adaptiveMixedPrimeTypeCenters support index).card =
      (adaptiveMixedTypeModulus support).totient := by
  unfold adaptiveMixedPrimeTypeCenters
  rw [adaptiveMixed_periodic_shift_filter_card
    (adaptiveMixedTypeModulus support) index
    (adaptiveMixedTypeModulus_pos support primes)]
  exact (Nat.totient_eq_card_coprime
    (adaptiveMixedTypeModulus support)).symm

/-- EVERY individual index has the same exact type-`s` center count:
the totient of the actual modulus after deleting ONE factor `s`. -/
theorem adaptiveMixedSemiprimeTypeCenters_card
    {support : Finset ℕ} {prime : ℕ}
    (index : ℕ) (primes : ∀ value ∈ support, value.Prime)
    (selected : prime ∈ support) :
    (adaptiveMixedSemiprimeTypeCenters support prime index).card =
      (adaptiveMixedTypeModulus support / prime).totient := by
  unfold adaptiveMixedSemiprimeTypeCenters
  dsimp only
  rw [adaptiveMixed_periodic_shift_filter_card
    (adaptiveMixedTypeModulus support) index
    (adaptiveMixedTypeModulus_pos support primes)
    (fun residue : ℕ =>
      prime ∣ residue ∧
        (adaptiveMixedTypeModulus support / prime).Coprime
          (residue / prime))]
  exact adaptiveMixedSemiprimeTypeResidues_card selected
    (primes prime selected)

/-- Coprimality with a complete-period representative is exactly the
coprimality needed for the original UNREDUCED integer. -/
theorem adaptiveMixed_coprime_of_mod_coprime
    (modulus value : ℕ)
    (coprime : modulus.Coprime (value % modulus)) :
    modulus.Coprime value := by
  rw [← Nat.mod_add_div value modulus]
  exact (Nat.coprime_add_mul_left_right modulus
    (value % modulus) (value / modulus)).mpr coprime

/-- A selected prime-type center gives a genuine unit coefficient for the
ACTUAL physical value `center + index`, not just its residue. -/
theorem adaptiveMixedPrimeTypeCenter_actual_coprime
    {support : Finset ℕ} {center index : ℕ}
    (selected : center ∈ adaptiveMixedPrimeTypeCenters support index) :
    (adaptiveMixedTypeModulus support).Coprime (center + index) := by
  exact adaptiveMixed_coprime_of_mod_coprime
    (adaptiveMixedTypeModulus support) (center + index)
    (Finset.mem_filter.mp selected).2

/-- A selected semiprime-type center makes the ACTUAL physical value
divisible by its genuine declared type, even across the period boundary. -/
theorem adaptiveMixedSemiprimeTypeCenter_actual_divides
    {support : Finset ℕ} {prime center index : ℕ}
    (supported : prime ∈ support)
    (selected : center ∈
      adaptiveMixedSemiprimeTypeCenters support prime index) :
    prime ∣ center + index := by
  obtain ⟨_bounded, typed⟩ := Finset.mem_filter.mp selected
  dsimp only at typed
  have residue_divides := typed.1
  have modulus_divides := adaptiveMixedType_dvd_modulus supported
  have period_divides :
      prime ∣ adaptiveMixedTypeModulus support *
        ((center + index) / adaptiveMixedTypeModulus support) :=
    dvd_mul_of_dvd_left modulus_divides _
  have total := dvd_add residue_divides period_divides
  rwa [Nat.mod_add_div] at total

/-- Exact physical quotient after crossing the squared-core period.  This
retains the actual numerator `center + index` used by the affine forms. -/
theorem adaptiveMixedSemiprimeTypeCenter_actual_quotient
    {support : Finset ℕ} {prime center index : ℕ}
    (supported : prime ∈ support) :
    (center + index) / prime =
      ((center + index) % adaptiveMixedTypeModulus support) / prime +
        (adaptiveMixedTypeModulus support / prime) *
          ((center + index) / adaptiveMixedTypeModulus support) := by
  have modulus_divides := adaptiveMixedType_dvd_modulus supported
  have period_divides :
      prime ∣ adaptiveMixedTypeModulus support *
        ((center + index) / adaptiveMixedTypeModulus support) :=
    dvd_mul_of_dvd_left modulus_divides _
  calc
    (center + index) / prime =
        (((center + index) % adaptiveMixedTypeModulus support) +
          adaptiveMixedTypeModulus support *
            ((center + index) / adaptiveMixedTypeModulus support)) / prime := by
      rw [Nat.mod_add_div]
    _ = ((center + index) % adaptiveMixedTypeModulus support) / prime +
        (adaptiveMixedTypeModulus support *
          ((center + index) / adaptiveMixedTypeModulus support)) / prime :=
      Nat.add_div_of_dvd_left period_divides
    _ = _ := by
      congr 1
      calc
        (adaptiveMixedTypeModulus support *
          ((center + index) / adaptiveMixedTypeModulus support)) / prime =
            (((center + index) / adaptiveMixedTypeModulus support) *
              adaptiveMixedTypeModulus support) / prime := by
                rw [Nat.mul_comm]
        _ = ((center + index) / adaptiveMixedTypeModulus support) *
              (adaptiveMixedTypeModulus support / prime) :=
                Nat.mul_div_assoc _ modulus_divides
        _ = _ := by rw [Nat.mul_comm]

/-- A selected semiprime center has its TRUE physical quotient coprime to
the entire reduced squared modulus, including every other supported type. -/
theorem adaptiveMixedSemiprimeTypeCenter_actual_quotient_coprime
    {support : Finset ℕ} {prime center index : ℕ}
    (supported : prime ∈ support)
    (selected : center ∈
      adaptiveMixedSemiprimeTypeCenters support prime index) :
    (adaptiveMixedTypeModulus support / prime).Coprime
      ((center + index) / prime) := by
  obtain ⟨_bounded, typed⟩ := Finset.mem_filter.mp selected
  dsimp only at typed
  rw [adaptiveMixedSemiprimeTypeCenter_actual_quotient supported]
  exact (Nat.coprime_add_mul_left_right
    (adaptiveMixedTypeModulus support / prime)
    (((center + index) % adaptiveMixedTypeModulus support) / prime)
    ((center + index) / adaptiveMixedTypeModulus support)).mpr typed.2

/-- The actual physical semiprime type is EXACTLY the gcd with the true
squared support modulus; no second supported factor survives. -/
theorem adaptiveMixedSemiprimeTypeCenter_actual_gcd_eq_type
    {support : Finset ℕ} {prime center index : ℕ}
    (supported : prime ∈ support)
    (selected : center ∈
      adaptiveMixedSemiprimeTypeCenters support prime index) :
    Nat.gcd (adaptiveMixedTypeModulus support) (center + index) = prime := by
  have modulus_factor :
      prime * (adaptiveMixedTypeModulus support / prime) =
        adaptiveMixedTypeModulus support :=
    Nat.mul_div_cancel' (adaptiveMixedType_dvd_modulus supported)
  have value_factor : prime * ((center + index) / prime) = center + index :=
    Nat.mul_div_cancel'
      (adaptiveMixedSemiprimeTypeCenter_actual_divides supported selected)
  have coprime :=
    adaptiveMixedSemiprimeTypeCenter_actual_quotient_coprime
      supported selected
  calc
    Nat.gcd (adaptiveMixedTypeModulus support) (center + index) =
        Nat.gcd
          (prime * (adaptiveMixedTypeModulus support / prime))
          (prime * ((center + index) / prime)) := by
      rw [modulus_factor, value_factor]
    _ = prime * Nat.gcd
          (adaptiveMixedTypeModulus support / prime)
          ((center + index) / prime) :=
      Nat.gcd_mul_left prime _ _
    _ = prime := by rw [Nat.coprime_iff_gcd_eq_one.mp coprime, Nat.mul_one]

/-- The exact omitted-prime support at the current reciprocal scale. -/
def adaptiveMixedOutsidePrimeSupport
    (support : Finset ℕ) (scale : ℕ) : Finset ℕ :=
  (Nat.primesLE scale) \ support

/-- Every genuinely omitted local prime remains prime. -/
theorem adaptiveMixedOutsidePrimeSupport_prime
    (support : Finset ℕ) (scale : ℕ) :
    ∀ prime ∈ adaptiveMixedOutsidePrimeSupport support scale, prime.Prime := by
  intro prime selected
  exact Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp selected).1

/-- One CRT-coded independent forbidden-residue vector is represented by a
single residue modulo the squarefree outside-prime radical. -/
def adaptiveMixedOutsideModulus
    (support : Finset ℕ) (scale : ℕ) : ℕ :=
  adaptiveMixedTypeRadical (adaptiveMixedOutsidePrimeSupport support scale)

/-- The omitted-prime CRT period is positive, including empty support. -/
theorem adaptiveMixedOutsideModulus_pos
    (support : Finset ℕ) (scale : ℕ) :
    0 < adaptiveMixedOutsideModulus support scale := by
  unfold adaptiveMixedOutsideModulus
  exact adaptiveMixedTypeRadical_pos
    (adaptiveMixedOutsidePrimeSupport support scale)
    (adaptiveMixedOutsidePrimeSupport_prime support scale)

/-- The outside forbidden-residue vectors that preserve one genuine target
index; the translation retains the exact CRT coding. -/
def adaptiveMixedOutsideSurvivors
    (support : Finset ℕ) (scale index : ℕ) : Finset ℕ :=
  (Finset.range (adaptiveMixedOutsideModulus support scale)).filter
    fun residue =>
      (adaptiveMixedOutsideModulus support scale).Coprime
        ((residue + index) % adaptiveMixedOutsideModulus support scale)

/-- Every index survives exactly the same number of genuine outside-prime
forbidden-residue choices. -/
theorem adaptiveMixedOutsideSurvivors_card
    (support : Finset ℕ) (scale index : ℕ) :
    (adaptiveMixedOutsideSurvivors support scale index).card =
      (adaptiveMixedOutsideModulus support scale).totient := by
  unfold adaptiveMixedOutsideSurvivors
  rw [adaptiveMixed_periodic_shift_filter_card
    (adaptiveMixedOutsideModulus support scale) index
    (adaptiveMixedOutsideModulus_pos support scale)]
  exact (Nat.totient_eq_card_coprime
    (adaptiveMixedOutsideModulus support scale)).symm

/-- The exact outside-survival probability is its complete genuine
prime-by-prime Euler product. -/
theorem adaptiveMixedOutside_probability_eq_eulerProduct
    (support : Finset ℕ) (scale : ℕ) :
    ((adaptiveMixedOutsideModulus support scale).totient : ℝ) /
      (adaptiveMixedOutsideModulus support scale : ℝ) =
        adaptivePrimeEulerProduct
          (adaptiveMixedOutsidePrimeSupport support scale) := by
  have nonzero : (adaptiveMixedOutsideModulus support scale : ℚ) ≠ 0 := by
    exact_mod_cast (adaptiveMixedOutsideModulus_pos support scale).ne'
  have support_prime := adaptiveMixedOutsidePrimeSupport_prime support scale
  have radical_support :
      (adaptiveMixedOutsideModulus support scale).primeFactors =
        adaptiveMixedOutsidePrimeSupport support scale := by
    exact adaptiveMixedTypeRadical_primeFactors
      (adaptiveMixedOutsidePrimeSupport support scale) support_prime
  have rational := Nat.totient_eq_mul_prod_factors
    (adaptiveMixedOutsideModulus support scale)
  rw [radical_support] at rational
  have rational_ratio :
      ((adaptiveMixedOutsideModulus support scale).totient : ℚ) /
          (adaptiveMixedOutsideModulus support scale : ℚ) =
        ∏ prime ∈ adaptiveMixedOutsidePrimeSupport support scale,
          (1 - (prime : ℚ)⁻¹) := by
    apply (div_eq_iff nonzero).mpr
    simpa [mul_comm] using rational
  have real := congrArg (fun value : ℚ => (value : ℝ)) rational_ratio
  simpa [adaptivePrimeEulerProduct] using real

/-- The complete finite joint sample space supporting prime type at one
index: a genuine squared-core center AND its independent CRT-coded
outside-prime forbidden-residue vector. -/
def adaptiveMixedPrimePatternSamples
    (support : Finset ℕ) (scale index : ℕ) : Finset (ℕ × ℕ) :=
  (adaptiveMixedPrimeTypeCenters support index).product
    (adaptiveMixedOutsideSurvivors support scale index)

/-- The corresponding complete finite joint samples of genuine semiprime
type `prime`. -/
def adaptiveMixedSemiprimePatternSamples
    (support : Finset ℕ) (prime scale index : ℕ) : Finset (ℕ × ℕ) :=
  (adaptiveMixedSemiprimeTypeCenters support prime index).product
    (adaptiveMixedOutsideSurvivors support scale index)

/-- Exact prime-pattern joint count, independently of the actual index. -/
theorem adaptiveMixedPrimePatternSamples_card
    (support : Finset ℕ) (scale index : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (adaptiveMixedPrimePatternSamples support scale index).card =
      (adaptiveMixedTypeModulus support).totient *
        (adaptiveMixedOutsideModulus support scale).totient := by
  unfold adaptiveMixedPrimePatternSamples
  rw [Finset.product_eq_sprod, Finset.card_product,
    adaptiveMixedPrimeTypeCenters_card support index primes,
    adaptiveMixedOutsideSurvivors_card]

/-- Exact semiprime-pattern joint count, independently of the actual index. -/
theorem adaptiveMixedSemiprimePatternSamples_card
    {support : Finset ℕ} {prime : ℕ}
    (scale index : ℕ) (primes : ∀ value ∈ support, value.Prime)
    (selected : prime ∈ support) :
    (adaptiveMixedSemiprimePatternSamples support prime scale index).card =
      (adaptiveMixedTypeModulus support / prime).totient *
        (adaptiveMixedOutsideModulus support scale).totient := by
  unfold adaptiveMixedSemiprimePatternSamples
  rw [Finset.product_eq_sprod, Finset.card_product,
    adaptiveMixedSemiprimeTypeCenters_card index primes selected,
    adaptiveMixedOutsideSurvivors_card]

/-- EXACT Proposition-7 prime-type marginal at EVERY genuine target
index, including both the squared type support and all omitted local
primes through the current reciprocal scale. -/
theorem adaptiveMixedPrimePattern_probability_eq_factor
    (support : Finset ℕ) (scale index : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    ((adaptiveMixedPrimePatternSamples support scale index).card : ℝ) /
      ((adaptiveMixedTypeModulus support *
        adaptiveMixedOutsideModulus support scale : ℕ) : ℝ) =
        adaptivePatternEulerFactor support scale := by
  rw [adaptiveMixedPrimePatternSamples_card support scale index primes]
  push_cast
  have core := adaptiveMixedPrimeType_probability_eq_eulerProduct support primes
  rw [adaptiveMixedPrimeTypeResidues_card] at core
  have outside := adaptiveMixedOutside_probability_eq_eulerProduct support scale
  have core_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have outside_positive : (0 : ℝ) < adaptiveMixedOutsideModulus support scale := by
    exact_mod_cast adaptiveMixedOutsideModulus_pos support scale
  calc
    ((adaptiveMixedTypeModulus support).totient : ℝ) *
          ((adaptiveMixedOutsideModulus support scale).totient : ℝ) /
        ((adaptiveMixedTypeModulus support : ℝ) *
          (adaptiveMixedOutsideModulus support scale : ℝ)) =
      (((adaptiveMixedTypeModulus support).totient : ℝ) /
        (adaptiveMixedTypeModulus support : ℝ)) *
      (((adaptiveMixedOutsideModulus support scale).totient : ℝ) /
        (adaptiveMixedOutsideModulus support scale : ℝ)) := by
          field_simp
    _ = adaptivePrimeEulerProduct support *
          adaptivePrimeEulerProduct
            (adaptiveMixedOutsidePrimeSupport support scale) := by
          rw [core, outside]
    _ = adaptivePatternEulerFactor support scale := by
          rfl

/-- EXACT Proposition-7 semiprime-type marginal at EVERY genuine target
index: the full prime-type factor divided by its actual selected type. -/
theorem adaptiveMixedSemiprimePattern_probability_eq_factor_div
    {support : Finset ℕ} {prime : ℕ}
    (scale index : ℕ) (primes : ∀ value ∈ support, value.Prime)
    (selected : prime ∈ support) :
    ((adaptiveMixedSemiprimePatternSamples support prime scale index).card : ℝ) /
      ((adaptiveMixedTypeModulus support *
        adaptiveMixedOutsideModulus support scale : ℕ) : ℝ) =
        adaptivePatternEulerFactor support scale / (prime : ℝ) := by
  rw [adaptiveMixedSemiprimePatternSamples_card scale index primes selected]
  push_cast
  have core := adaptiveMixedSemiprimeType_probability_eq_eulerProduct_div
    primes selected
  rw [adaptiveMixedSemiprimeTypeResidues_card selected
    (primes prime selected)] at core
  have outside := adaptiveMixedOutside_probability_eq_eulerProduct support scale
  have core_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have outside_positive : (0 : ℝ) < adaptiveMixedOutsideModulus support scale := by
    exact_mod_cast adaptiveMixedOutsideModulus_pos support scale
  calc
    ((adaptiveMixedTypeModulus support / prime).totient : ℝ) *
          ((adaptiveMixedOutsideModulus support scale).totient : ℝ) /
        ((adaptiveMixedTypeModulus support : ℝ) *
          (adaptiveMixedOutsideModulus support scale : ℝ)) =
      (((adaptiveMixedTypeModulus support / prime).totient : ℝ) /
        (adaptiveMixedTypeModulus support : ℝ)) *
      (((adaptiveMixedOutsideModulus support scale).totient : ℝ) /
        (adaptiveMixedOutsideModulus support scale : ℝ)) := by
          field_simp
    _ = (adaptivePrimeEulerProduct support / (prime : ℝ)) *
          adaptivePrimeEulerProduct
            (adaptiveMixedOutsidePrimeSupport support scale) := by
          rw [core, outside]
    _ = adaptivePatternEulerFactor support scale / (prime : ℝ) := by
          unfold adaptivePatternEulerFactor adaptiveMixedOutsidePrimeSupport
          ring

/-- ONE actual outcome contains a common squared-core center and a common
CRT-coded outside forbidden-residue vector.  The same outcome determines
EVERY prime and semiprime index simultaneously. -/
def adaptiveMixedOutcomeSpace
    (support : Finset ℕ) (scale : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (adaptiveMixedTypeModulus support)).product
    (Finset.range (adaptiveMixedOutsideModulus support scale))

/-- Exact cardinality of the SINGLE common mixed-pattern outcome space. -/
theorem adaptiveMixedOutcomeSpace_card
    (support : Finset ℕ) (scale : ℕ) :
    (adaptiveMixedOutcomeSpace support scale).card =
      adaptiveMixedTypeModulus support *
        adaptiveMixedOutsideModulus support scale := by
  unfold adaptiveMixedOutcomeSpace
  rw [Finset.product_eq_sprod, Finset.card_product]
  simp

/-- Prime outcomes at ANY index are restrictions of the same common
pattern-outcome space, not separately resampled distributions. -/
theorem adaptiveMixedPrimePatternSamples_subset_outcomes
    (support : Finset ℕ) (scale index : ℕ) :
    adaptiveMixedPrimePatternSamples support scale index ⊆
      adaptiveMixedOutcomeSpace support scale := by
  intro outcome member
  simp only [adaptiveMixedPrimePatternSamples, adaptiveMixedOutcomeSpace,
    Finset.product_eq_sprod, Finset.mem_product,
    adaptiveMixedPrimeTypeCenters, adaptiveMixedOutsideSurvivors,
    Finset.mem_filter] at member ⊢
  exact ⟨member.1.1, member.2.1⟩

/-- Semiprime outcomes at ANY index and supported type live in the SAME
common pattern-outcome space as all prime outcomes. -/
theorem adaptiveMixedSemiprimePatternSamples_subset_outcomes
    (support : Finset ℕ) (prime scale index : ℕ) :
    adaptiveMixedSemiprimePatternSamples support prime scale index ⊆
      adaptiveMixedOutcomeSpace support scale := by
  intro outcome member
  simp only [adaptiveMixedSemiprimePatternSamples, adaptiveMixedOutcomeSpace,
    Finset.product_eq_sprod, Finset.mem_product,
    adaptiveMixedSemiprimeTypeCenters, adaptiveMixedOutsideSurvivors,
    Finset.mem_filter] at member ⊢
  exact ⟨member.1.1, member.2.1⟩

/-- The actual prime-type physical indices retained by ONE common outcome;
the original manuscript indices are `1,...,scale`, not `0,...,scale-1`. -/
def adaptiveMixedOutcomePrimeIndices
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) : Finset ℕ :=
  (Finset.Icc 1 scale).filter fun index =>
    outcome ∈ adaptiveMixedPrimePatternSamples support scale index

/-- The actual semiprime-type physical indices retained by the SAME
common outcome. -/
def adaptiveMixedOutcomeSemiprimeIndices
    (support : Finset ℕ) (prime scale : ℕ)
    (outcome : ℕ × ℕ) : Finset ℕ :=
  (Finset.Icc 1 scale).filter fun index =>
    outcome ∈ adaptiveMixedSemiprimePatternSamples support prime scale index

/-- Every prime or supported semiprime index retained by ONE shared
actual mixed-pattern outcome.  Duplicate type descriptions are discarded. -/
def adaptiveMixedOutcomeActiveIndices
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) : Finset ℕ :=
  adaptiveMixedOutcomePrimeIndices support scale outcome ∪
    support.biUnion fun selected =>
      adaptiveMixedOutcomeSemiprimeIndices support selected scale outcome

/-- The TRUE type of an actual physical index is its gcd with the squared
support modulus, evaluated on the unreduced integer `center + index`. -/
def adaptiveMixedActualIndexType
    (support : Finset ℕ) (center index : ℕ) : ℕ :=
  Nat.gcd (adaptiveMixedTypeModulus support) (center + index)

/-- The actual integral affine target form, retaining both the unreduced
physical numerator and its true gcd type. -/
def adaptiveMixedActualAffineForm
    (support : Finset ℕ) (center index ell : ℕ)
    (label value : ZMod ell) : ZMod ell :=
  (((center + index) /
      adaptiveMixedActualIndexType support center index : ℕ) : ZMod ell) * label +
    (((adaptiveMixedTypeModulus support /
      adaptiveMixedActualIndexType support center index : ℕ) : ZMod ell)) * value

/-- The complete mixed active pattern uses ONLY true manuscript indices
`1,...,scale`; index zero is never silently inserted. -/
theorem adaptiveMixedOutcomeActiveIndices_subset_physical
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) :
    adaptiveMixedOutcomeActiveIndices support scale outcome ⊆
      Finset.Icc 1 scale := by
  intro index selected
  rcases Finset.mem_union.mp selected with prime | semiprime
  · exact (Finset.mem_filter.mp prime).1
  · obtain ⟨_type, _supported, typed⟩ := Finset.mem_biUnion.mp semiprime
    exact (Finset.mem_filter.mp typed).1

/-- Even allowing ALL simultaneously supported types, an actual shared
mixed outcome contains at most its true number of physical indices. -/
theorem adaptiveMixedOutcomeActiveIndices_card_le_scale
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) :
    (adaptiveMixedOutcomeActiveIndices support scale outcome).card ≤ scale := by
  calc
    (adaptiveMixedOutcomeActiveIndices support scale outcome).card ≤
        (Finset.Icc 1 scale).card :=
      Finset.card_le_card
        (adaptiveMixedOutcomeActiveIndices_subset_physical support scale outcome)
    _ = scale := by simp

/-- EVERY retained physical index of ONE shared actual outcome comes with
its TRUE unreduced type certificate and the SAME outside residue `rho`. -/
theorem adaptiveMixedOutcomeActiveIndex_type_certificate
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (_primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    (adaptiveMixedActualIndexType support outcome.1 index = 1 ∧
       (adaptiveMixedTypeModulus support).Coprime (outcome.1 + index) ∧
       outcome.2 ∈ adaptiveMixedOutsideSurvivors support scale index) ∨
    ∃ selected ∈ support,
      adaptiveMixedActualIndexType support outcome.1 index = selected ∧
      selected ∣ outcome.1 + index ∧
      (adaptiveMixedTypeModulus support / selected).Coprime
        ((outcome.1 + index) / selected) ∧
      outcome.2 ∈ adaptiveMixedOutsideSurvivors support scale index := by
  rcases Finset.mem_union.mp active with prime | semiprime
  · have sample := (Finset.mem_filter.mp prime).2
    have coordinates :
        outcome.1 ∈ adaptiveMixedPrimeTypeCenters support index ∧
          outcome.2 ∈ adaptiveMixedOutsideSurvivors support scale index := by
      simpa [adaptiveMixedPrimePatternSamples, Finset.product_eq_sprod] using sample
    have coprime := adaptiveMixedPrimeTypeCenter_actual_coprime coordinates.1
    exact Or.inl
      ⟨Nat.coprime_iff_gcd_eq_one.mp coprime, coprime, coordinates.2⟩
  · obtain ⟨selected, supported, typed⟩ := Finset.mem_biUnion.mp semiprime
    have sample := (Finset.mem_filter.mp typed).2
    have coordinates :
        outcome.1 ∈ adaptiveMixedSemiprimeTypeCenters support selected index ∧
          outcome.2 ∈ adaptiveMixedOutsideSurvivors support scale index := by
      simpa [adaptiveMixedSemiprimePatternSamples, Finset.product_eq_sprod]
        using sample
    exact Or.inr
      ⟨selected, supported,
        adaptiveMixedSemiprimeTypeCenter_actual_gcd_eq_type
          supported coordinates.1,
        adaptiveMixedSemiprimeTypeCenter_actual_divides supported coordinates.1,
        adaptiveMixedSemiprimeTypeCenter_actual_quotient_coprime
          supported coordinates.1,
        coordinates.2⟩

/-- The true type of every retained mixed index divides its genuine
unreduced physical target numerator. -/
theorem adaptiveMixedOutcomeActiveIndex_type_dvd_value
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualIndexType support outcome.1 index ∣ outcome.1 + index := by
  rcases adaptiveMixedOutcomeActiveIndex_type_certificate primes active with
    ⟨typed, _coprime, _outside⟩ |
      ⟨_selected, _supported, typed, divides, _coprime, _outside⟩
  · simp [typed]
  · simpa [typed] using divides

/-- The true type of every retained mixed index divides the true squared
support modulus. -/
theorem adaptiveMixedOutcomeActiveIndex_type_dvd_modulus
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualIndexType support outcome.1 index ∣
      adaptiveMixedTypeModulus support := by
  rcases adaptiveMixedOutcomeActiveIndex_type_certificate primes active with
    ⟨typed, _coprime, _outside⟩ |
      ⟨selected, supported, typed, _divides, _coprime, _outside⟩
  · simp [typed]
  · simpa [typed] using adaptiveMixedType_dvd_modulus supported

/-- Every active index survives the SAME outside-prime residue vector of
its one shared mixed-pattern outcome. -/
theorem adaptiveMixedOutcomeActiveIndex_outside_survives
    {support : Finset ℕ} {scale index : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    outcome.2 ∈ adaptiveMixedOutsideSurvivors support scale index := by
  rcases adaptiveMixedOutcomeActiveIndex_type_certificate primes active with
    ⟨_typed, _coprime, outside⟩ |
      ⟨_selected, _supported, _typed, _divides, _coprime, outside⟩
  · exact outside
  · exact outside

/-- No prime outside the selected genuine support can divide the true
squared support modulus. -/
theorem adaptiveMixedOutsidePrime_not_dvd_type_modulus
    {support : Finset ℕ} {ell : ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (ell_prime : ell.Prime) (outside : ell ∉ support) :
    ¬ ell ∣ adaptiveMixedTypeModulus support := by
  intro divides
  have member : ell ∈ (adaptiveMixedTypeModulus support).primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero
      (adaptiveMixedTypeModulus_pos support primes).ne').mpr
        ⟨ell_prime, divides⟩
  rw [adaptiveMixedTypeModulus_primeFactors support primes] at member
  exact outside member

/-- At every omitted small prime, surviving the ONE common outside residue
really excludes its forbidden actual index residue. -/
theorem adaptiveMixedOutsideSurvivor_small_prime_not_dvd
    {support : Finset ℕ} {scale index residue ell : ℕ}
    (ell_prime : ell.Prime) (small : ell ≤ scale) (outside : ell ∉ support)
    (survives : residue ∈ adaptiveMixedOutsideSurvivors support scale index) :
    ¬ ell ∣ residue + index := by
  have omitted : ell ∈ adaptiveMixedOutsidePrimeSupport support scale :=
    Finset.mem_sdiff.mpr
      ⟨Nat.mem_primesLE.mpr ⟨small, ell_prime⟩, outside⟩
  have divides_modulus : ell ∣ adaptiveMixedOutsideModulus support scale := by
    unfold adaptiveMixedOutsideModulus adaptiveMixedTypeRadical
    exact Finset.dvd_prod_of_mem (fun prime : ℕ => prime) omitted
  have residue_coprime := (Finset.mem_filter.mp survives).2
  have actual_coprime := adaptiveMixed_coprime_of_mod_coprime
    (adaptiveMixedOutsideModulus support scale) (residue + index)
    residue_coprime
  exact ell_prime.coprime_iff_not_dvd.mp
    (Nat.Coprime.of_dvd_left divides_modulus actual_coprime)

/-- At a supported prime, EVERY selected actual mixed affine form is
already nonzero at the common local choice `(label, center) = (1, 0)`. -/
theorem adaptiveMixedOutcome_support_prime_affine_nonzero
    {support : Finset ℕ} {scale index ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (supported : ell ∈ support)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualAffineForm support outcome.1 index ell 1 0 ≠ 0 := by
  rcases adaptiveMixedOutcomeActiveIndex_type_certificate primes active with
    ⟨typed, coprime, _outside⟩ |
      ⟨selected, selected_supported, typed, _divides, coprime, _outside⟩
  · have local_coprime : ell.Coprime (outcome.1 + index) :=
      Nat.Coprime.of_dvd_left
        (adaptiveMixedType_dvd_modulus supported) coprime
    intro zero
    have cast_zero : ((outcome.1 + index : ℕ) : ZMod ell) = 0 := by
      simpa [adaptiveMixedActualAffineForm, typed] using zero
    exact (primes ell supported).coprime_iff_not_dvd.mp local_coprime
      ((ZMod.natCast_eq_zero_iff (outcome.1 + index) ell).mp cast_zero)
  · have local_coprime : ell.Coprime ((outcome.1 + index) / selected) :=
      Nat.Coprime.of_dvd_left
        (adaptiveMixedType_support_dvd_reduced_modulus
          primes selected_supported supported) coprime
    intro zero
    have cast_zero :
        (((outcome.1 + index) / selected : ℕ) : ZMod ell) = 0 := by
      simpa [adaptiveMixedActualAffineForm, typed] using zero
    exact (primes ell supported).coprime_iff_not_dvd.mp local_coprime
      ((ZMod.natCast_eq_zero_iff
        ((outcome.1 + index) / selected) ell).mp cast_zero)

/-- The canonical local center at an omitted prime uses the SAME actual
outside residue as every index of the shared mixed-pattern outcome. -/
def adaptiveMixedOutsideLocalCenter
    (support : Finset ℕ) (center residue ell : ℕ) [Fact ell.Prime] : ZMod ell :=
  ((residue : ZMod ell) - (center : ZMod ell)) *
    ((adaptiveMixedTypeModulus support : ℕ) : ZMod ell)⁻¹

/-- Multiplying the omitted-prime center by the genuine squared support
modulus gives exactly the common shift `rho - center`. -/
theorem adaptiveMixedOutsideLocalCenter_mul
    {support : Finset ℕ} {center residue ell : ℕ} [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) :
    ((adaptiveMixedTypeModulus support : ℕ) : ZMod ell) *
      adaptiveMixedOutsideLocalCenter support center residue ell =
        (residue : ZMod ell) - (center : ZMod ell) := by
  have prime : ell.Prime := Fact.out
  have modulus_nonzero :
      ((adaptiveMixedTypeModulus support : ℕ) : ZMod ell) ≠ 0 := by
    intro zero
    exact adaptiveMixedOutsidePrime_not_dvd_type_modulus
      primes prime outside
      ((ZMod.natCast_eq_zero_iff
        (adaptiveMixedTypeModulus support) ell).mp zero)
  unfold adaptiveMixedOutsideLocalCenter
  field_simp

/-- Exact integer-factorization identity for the ACTUAL mixed affine form;
both coefficients use true unreduced physical numerators. -/
theorem adaptiveMixedActualAffineForm_scaled
    (support : Finset ℕ) (center index ell : ℕ)
    (label value : ZMod ell)
    (value_divides : adaptiveMixedActualIndexType support center index ∣
      center + index)
    (modulus_divides : adaptiveMixedActualIndexType support center index ∣
      adaptiveMixedTypeModulus support) :
    ((adaptiveMixedActualIndexType support center index : ℕ) : ZMod ell) *
      adaptiveMixedActualAffineForm support center index ell label value =
        ((center + index : ℕ) : ZMod ell) * label +
          ((adaptiveMixedTypeModulus support : ℕ) : ZMod ell) * value := by
  have value_factor := congrArg (fun number : ℕ => (number : ZMod ell))
    (Nat.mul_div_cancel' value_divides)
  have modulus_factor := congrArg (fun number : ℕ => (number : ZMod ell))
    (Nat.mul_div_cancel' modulus_divides)
  push_cast at value_factor modulus_factor
  unfold adaptiveMixedActualAffineForm
  push_cast
  rw [← value_factor, ← modulus_factor]
  ring

/-- At EVERY omitted prime below the physical scale, ONE common local
center makes EVERY selected actual mixed affine target nonzero. -/
theorem adaptiveMixedOutcome_outside_small_prime_affine_nonzero
    {support : Finset ℕ} {scale index ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support) (small : ell ≤ scale)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    adaptiveMixedActualAffineForm support outcome.1 index ell 1
      (adaptiveMixedOutsideLocalCenter support outcome.1 outcome.2 ell) ≠ 0 := by
  have prime : ell.Prime := Fact.out
  have survives := adaptiveMixedOutcomeActiveIndex_outside_survives
    primes active
  have not_divides := adaptiveMixedOutsideSurvivor_small_prime_not_dvd
    prime small outside survives
  have scaled := adaptiveMixedActualAffineForm_scaled
    support outcome.1 index ell 1
    (adaptiveMixedOutsideLocalCenter support outcome.1 outcome.2 ell)
    (adaptiveMixedOutcomeActiveIndex_type_dvd_value primes active)
    (adaptiveMixedOutcomeActiveIndex_type_dvd_modulus primes active)
  have right_side :
      ((outcome.1 + index : ℕ) : ZMod ell) * 1 +
        ((adaptiveMixedTypeModulus support : ℕ) : ZMod ell) *
          adaptiveMixedOutsideLocalCenter support outcome.1 outcome.2 ell =
            ((outcome.2 + index : ℕ) : ZMod ell) := by
    rw [adaptiveMixedOutsideLocalCenter_mul primes outside]
    push_cast
    ring
  rw [right_side] at scaled
  intro zero
  have cast_zero : ((outcome.2 + index : ℕ) : ZMod ell) = 0 := by
    rw [← scaled, zero, mul_zero]
  exact not_divides
    ((ZMod.natCast_eq_zero_iff (outcome.2 + index) ell).mp cast_zero)

/-- Outside the true support, the reduced modulus of EVERY active mixed
type remains a nonzero coefficient in the local finite field. -/
theorem adaptiveMixedOutcome_outside_reduced_modulus_nonzero
    {support : Finset ℕ} {scale index ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome) :
    (((adaptiveMixedTypeModulus support /
      adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell)) ≠
        0 := by
  have prime : ell.Prime := Fact.out
  have reduced_divides :
      adaptiveMixedTypeModulus support /
          adaptiveMixedActualIndexType support outcome.1 index ∣
        adaptiveMixedTypeModulus support :=
    Nat.div_dvd_of_dvd
      (adaptiveMixedOutcomeActiveIndex_type_dvd_modulus primes active)
  intro zero
  have divides_reduced :=
    (ZMod.natCast_eq_zero_iff
      (adaptiveMixedTypeModulus support /
        adaptiveMixedActualIndexType support outcome.1 index) ell).mp zero
  exact adaptiveMixedOutsidePrime_not_dvd_type_modulus
    primes prime outside (dvd_trans divides_reduced reduced_divides)

/-- The genuine forbidden local centers for the ACTUAL mixed affine forms
of ONE common outcome, with each index using its own true type. -/
noncomputable def adaptiveMixedOutcomeLocalForbidden
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime] : Finset (ZMod ell) :=
  (adaptiveMixedOutcomeActiveIndices support scale outcome).image
    fun index : ℕ =>
      -(((outcome.1 + index) /
          adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell) /
        (((adaptiveMixedTypeModulus support /
          adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell))

/-- Above the actual physical scale, the union of ALL prime and supported
semiprime forms forbids fewer centers than the local finite field contains. -/
theorem adaptiveMixedOutcomeLocalForbidden_card_lt_large
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime] (large : scale < ell) :
    (adaptiveMixedOutcomeLocalForbidden support scale ell outcome).card < ell := by
  calc
    (adaptiveMixedOutcomeLocalForbidden support scale ell outcome).card ≤
        (adaptiveMixedOutcomeActiveIndices support scale outcome).card := by
      unfold adaptiveMixedOutcomeLocalForbidden
      exact Finset.card_image_le
    _ ≤ scale :=
      adaptiveMixedOutcomeActiveIndices_card_le_scale support scale outcome
    _ < ell := large

/-- EVERY actual shared mixed prime/semiprime outcome is locally
admissible at EVERY prime.  The same one outcome supplies all true physical
indices, all unreduced affine coefficients, and all outside-prime pruning. -/
theorem adaptiveMixedOutcome_all_prime_locally_admissible
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (ell : ℕ) [Fact ell.Prime] :
    ∃ label value : ZMod ell, label ≠ 0 ∧
      ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
        adaptiveMixedActualAffineForm support outcome.1 index ell label value ≠ 0 := by
  classical
  by_cases supported : ell ∈ support
  · exact ⟨1, 0, one_ne_zero,
      fun index active =>
        adaptiveMixedOutcome_support_prime_affine_nonzero
          primes supported active⟩
  · by_cases small : ell ≤ scale
    · exact
        ⟨1, adaptiveMixedOutsideLocalCenter
          support outcome.1 outcome.2 ell,
          one_ne_zero, fun index active =>
            adaptiveMixedOutcome_outside_small_prime_affine_nonzero
              primes supported small active⟩
    · have large : scale < ell := Nat.lt_of_not_ge small
      let forbidden := adaptiveMixedOutcomeLocalForbidden
        support scale ell outcome
      have cardinal :
          forbidden.card < (Finset.univ : Finset (ZMod ell)).card := by
        simpa [forbidden] using
          adaptiveMixedOutcomeLocalForbidden_card_lt_large
            (support := support) (outcome := outcome) large
      obtain ⟨value, selected⟩ :=
        Finset.sdiff_nonempty_of_card_lt_card cardinal
      have outside : value ∉ forbidden := (Finset.mem_sdiff.mp selected).2
      refine ⟨1, value, one_ne_zero, ?_⟩
      intro index active zero
      have coefficient_nonzero :=
        adaptiveMixedOutcome_outside_reduced_modulus_nonzero
          primes supported active
      have equation :
          (((outcome.1 + index) /
            adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell) +
          (((adaptiveMixedTypeModulus support /
            adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell)) *
              value = 0 := by
        unfold adaptiveMixedActualAffineForm at zero
        simpa only [one_mul, mul_one] using zero
      have root :
          value =
            -(((outcome.1 + index) /
              adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell) /
            (((adaptiveMixedTypeModulus support /
              adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ZMod ell)) := by
        apply (eq_div_iff coefficient_nonzero).mpr
        rw [mul_comm]
        exact eq_neg_of_add_eq_zero_right equation
      apply outside
      change value ∈ adaptiveMixedOutcomeLocalForbidden
        support scale ell outcome
      apply Finset.mem_image.mpr
      exact ⟨index, active, root.symm⟩

/-- Generic exact transpose between one common outcome distribution and
its actual physical-index incidence. -/
theorem adaptiveMixed_common_outcome_incidence_transpose
    (outcomes : Finset (ℕ × ℕ)) (indices : Finset ℕ)
    (samples : ℕ → Finset (ℕ × ℕ))
    (contained : ∀ index ∈ indices, samples index ⊆ outcomes) :
    (∑ outcome ∈ outcomes,
      (indices.filter fun index => outcome ∈ samples index).card) =
        ∑ index ∈ indices, (samples index).card := by
  classical
  calc
    (∑ outcome ∈ outcomes,
      (indices.filter fun index => outcome ∈ samples index).card) =
        ∑ outcome ∈ outcomes, ∑ index ∈ indices,
          if outcome ∈ samples index then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro outcome _selected
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ index ∈ indices, ∑ outcome ∈ outcomes,
          if outcome ∈ samples index then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ index ∈ indices, (samples index).card := by
      apply Finset.sum_congr rfl
      intro index selected
      have exact_filter :
          outcomes.filter (fun outcome => outcome ∈ samples index) =
            samples index := by
        ext outcome
        simp only [Finset.mem_filter]
        exact ⟨And.right,
          fun member => ⟨contained index selected member, member⟩⟩
      calc
        (∑ outcome ∈ outcomes,
          if outcome ∈ samples index then 1 else 0) =
            (outcomes.filter
              (fun outcome => outcome ∈ samples index)).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = (samples index).card := congrArg Finset.card exact_filter

/-- Exact prime-index incidence over the SINGLE common outcome space and
the true physical indices `1,...,scale`. -/
theorem adaptiveMixedOutcomePrimeIndices_total_incidence
    (support : Finset ℕ) (scale : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (∑ outcome ∈ adaptiveMixedOutcomeSpace support scale,
      (adaptiveMixedOutcomePrimeIndices support scale outcome).card) =
        scale * (adaptiveMixedTypeModulus support).totient *
          (adaptiveMixedOutsideModulus support scale).totient := by
  unfold adaptiveMixedOutcomePrimeIndices
  rw [adaptiveMixed_common_outcome_incidence_transpose
    (adaptiveMixedOutcomeSpace support scale) (Finset.Icc 1 scale)
    (adaptiveMixedPrimePatternSamples support scale)
    (fun index _selected =>
      adaptiveMixedPrimePatternSamples_subset_outcomes support scale index)]
  simp [adaptiveMixedPrimePatternSamples_card support scale _ primes,
    Nat.mul_assoc]

/-- Exact semiprime-index incidence of EACH type over the SAME common
outcome distribution and true physical indices `1,...,scale`. -/
theorem adaptiveMixedOutcomeSemiprimeIndices_total_incidence
    {support : Finset ℕ} {prime : ℕ}
    (scale : ℕ) (primes : ∀ value ∈ support, value.Prime)
    (selected : prime ∈ support) :
    (∑ outcome ∈ adaptiveMixedOutcomeSpace support scale,
      (adaptiveMixedOutcomeSemiprimeIndices support prime scale outcome).card) =
        scale * (adaptiveMixedTypeModulus support / prime).totient *
          (adaptiveMixedOutsideModulus support scale).totient := by
  unfold adaptiveMixedOutcomeSemiprimeIndices
  rw [adaptiveMixed_common_outcome_incidence_transpose
    (adaptiveMixedOutcomeSpace support scale) (Finset.Icc 1 scale)
    (adaptiveMixedSemiprimePatternSamples support prime scale)
    (fun index _selected =>
      adaptiveMixedSemiprimePatternSamples_subset_outcomes
        support prime scale index)]
  simp [adaptiveMixedSemiprimePatternSamples_card
    scale _ primes selected, Nat.mul_assoc]

/-- The entire exact expected NUMBER of prime-type indices is the genuine
scale times its full adaptive Euler factor. -/
theorem adaptiveMixedPrimePattern_expected_count
    (support : Finset ℕ) (scale : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (∑ index ∈ Finset.Icc 1 scale,
      ((adaptiveMixedPrimePatternSamples support scale index).card : ℝ) /
        ((adaptiveMixedTypeModulus support *
          adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)) =
      (scale : ℝ) * adaptivePatternEulerFactor support scale := by
  calc
    _ = ∑ _index ∈ Finset.Icc 1 scale,
          adaptivePatternEulerFactor support scale := by
      apply Finset.sum_congr rfl
      intro index _selected
      exact adaptiveMixedPrimePattern_probability_eq_factor
        support scale index primes
    _ = _ := by simp

/-- The entire exact expected NUMBER of genuine semiprime indices of type
`s` is the scale times the full adaptive Euler factor divided by `s`. -/
theorem adaptiveMixedSemiprimePattern_expected_count
    {support : Finset ℕ} {prime : ℕ}
    (scale : ℕ) (primes : ∀ value ∈ support, value.Prime)
    (selected : prime ∈ support) :
    (∑ index ∈ Finset.Icc 1 scale,
      ((adaptiveMixedSemiprimePatternSamples support prime scale index).card : ℝ) /
        ((adaptiveMixedTypeModulus support *
          adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)) =
      (scale : ℝ) *
        (adaptivePatternEulerFactor support scale / (prime : ℝ)) := by
  calc
    _ = ∑ _index ∈ Finset.Icc 1 scale,
          adaptivePatternEulerFactor support scale / (prime : ℝ) := by
      apply Finset.sum_congr rfl
      intro index _selected
      exact adaptiveMixedSemiprimePattern_probability_eq_factor_div
        scale index primes selected
    _ = _ := by simp


end Erdos1139
