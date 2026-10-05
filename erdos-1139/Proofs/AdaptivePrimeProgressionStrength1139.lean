module

public import AdaptiveMixedPublishedGTZCapstone1139
public import AdaptiveMixedSignedDomainGeometry1139
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section


/-!
# The exact remaining #1139 analytic hypothesis contains prime progressions

The actual signed mixed-pattern systems have genuinely unbounded analytic
strength.  This module constructs an admissible arithmetic progression of
physical target indices inside one authentic mixed outcome, using an exact
finite Chinese-remainder choice of all omitted-prime residues.  Consequently
the remaining published prime-pattern hypothesis implies prime arithmetic
progressions of every prescribed finite length.

This is an obstruction to replacing the remaining hypothesis by the already
formalized prime number theorem or the #689 three-prime theorem; it does not
prove the Green--Tao theorem or the original #1139 conjecture outright.
-/

open Filter Finset Set
open scoped BigOperators Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos1139

/-- Fewer than `q` forbidden translates cannot occupy all residue classes
modulo a genuine prime `q`.  The offsets are completely arbitrary and may
collide locally. -/
theorem adaptivePrimeProgression_exists_local_avoiding_residue
    (q length : ℕ) (prime : q.Prime) (short : length < q)
    (offset : ℕ → ℕ) :
    ∃ residue : ℕ, residue < q ∧
      ∀ index < length, ¬q ∣ residue + offset index := by
  classical
  let _ : NeZero q := ⟨prime.ne_zero⟩
  let forbidden : Finset (ZMod q) :=
    (Finset.range length).image fun index => -(offset index : ZMod q)
  have bound : forbidden.card ≤ length := by
    simpa [forbidden] using
      (Finset.card_image_le (s := Finset.range length)
        (f := fun index => -(offset index : ZMod q)))
  obtain ⟨allowed, avoids⟩ : ∃ value : ZMod q, value ∉ forbidden := by
    by_contra none
    push Not at none
    have full : forbidden = Finset.univ :=
      Finset.eq_univ_of_forall none
    have impossible : q ≤ length := by
      simpa [full] using bound
    omega
  refine ⟨allowed.val, ZMod.val_lt allowed, ?_⟩
  intro index small divides
  have zero : (((allowed.val + offset index : ℕ) : ZMod q)) = 0 := by
    obtain ⟨factor, equality⟩ := divides
    rw [equality]
    simp
  have equality : allowed = -(offset index : ZMod q) := by
    have sum_zero : allowed + (offset index : ZMod q) = 0 := by
      simpa using zero
    linear_combination sum_zero
  apply avoids
  exact Finset.mem_image.mpr
    ⟨index, Finset.mem_range.mpr small, equality.symm⟩

/-- A single exact CRT residue simultaneously avoids every prescribed offset
at every prime in a finite family, provided all those primes exceed the
number of offsets.  The representative is strictly below its true radical. -/
theorem adaptivePrimeProgression_exists_simultaneous_avoiding_residue
    (primes : Finset ℕ) (length : ℕ) (offset : ℕ → ℕ)
    (prime : ∀ q ∈ primes, q.Prime)
    (large : ∀ q ∈ primes, length < q) :
    ∃ residue : ℕ, residue < ∏ q ∈ primes, q ∧
      ∀ index < length,
        (∏ q ∈ primes, q).Coprime (residue + offset index) := by
  classical
  let localResidue : ℕ → ℕ := fun q =>
    if selected : q ∈ primes then
      (adaptivePrimeProgression_exists_local_avoiding_residue
        q length (prime q selected) (large q selected) offset).choose
    else 0
  have local_avoids (q : ℕ) (selected : q ∈ primes)
      (index : ℕ) (small : index < length) :
      ¬q ∣ localResidue q + offset index := by
    simp only [localResidue, dif_pos selected]
    exact (adaptivePrimeProgression_exists_local_avoiding_residue
      q length (prime q selected) (large q selected) offset).choose_spec.2
        index small
  have nonzero : ∀ q ∈ primes, q ≠ 0 :=
    fun q selected => (prime q selected).ne_zero
  have pairwise : Set.Pairwise (↑primes : Set ℕ)
      (fun p q : ℕ => Nat.Coprime p q) := by
    intro first first_selected second second_selected distinct
    exact (Nat.coprime_primes
      (prime first first_selected) (prime second second_selected)).mpr distinct
  let witness := Nat.chineseRemainderOfFinset localResidue
    (fun q : ℕ => q) primes nonzero pairwise
  refine ⟨witness, Nat.chineseRemainderOfFinset_lt_prod
    localResidue (fun q : ℕ => q) nonzero pairwise, ?_⟩
  intro index small
  apply Nat.Coprime.prod_left
  intro q selected
  apply (prime q selected).coprime_iff_not_dvd.mpr
  intro divides
  have congruent :
      ((witness : ℕ) + offset index) ≡
        (localResidue q + offset index) [MOD q] :=
    (witness.property q selected).add (Nat.ModEq.rfl)
  have local_divides : q ∣ localResidue q + offset index :=
    Nat.modEq_zero_iff_dvd.mp
      (congruent.symm.trans (Nat.modEq_zero_iff_dvd.mpr divides))
  exact local_avoids q selected index small local_divides

/-- Every prescribed finite progression occurs among the TRUE active physical
indices of one common genuine mixed outcome.  All small primes are absorbed
into the actual squared type modulus; every omitted prime is then larger than
the progression length and a single CRT residue avoids its forbidden classes.
The first outcome coordinate is exactly zero, so all progression indices have
genuine prime type rather than a silently altered semiprime type. -/
theorem adaptivePrimeProgression_exists_active_index_progression
    (length : ℕ) (_positive : 0 < length) :
    ∃ outcome : ℕ × ℕ, outcome.1 = 0 ∧
      ∀ index < length,
        1 + index * adaptiveMixedTypeModulus (Nat.primesLE length) ∈
          adaptiveMixedOutcomeActiveIndices
            (Nat.primesLE length)
            (1 + (length - 1) *
              adaptiveMixedTypeModulus (Nat.primesLE length))
            outcome := by
  classical
  let support : Finset ℕ := Nat.primesLE length
  let modulus : ℕ := adaptiveMixedTypeModulus support
  let scale : ℕ := 1 + (length - 1) * modulus
  let outside : Finset ℕ := adaptiveMixedOutsidePrimeSupport support scale
  have support_prime : ∀ prime ∈ support, prime.Prime := by
    intro prime selected
    exact Nat.prime_of_mem_primesLE selected
  have modulus_positive : 0 < modulus :=
    adaptiveMixedTypeModulus_pos support support_prime
  have outside_prime : ∀ prime ∈ outside, prime.Prime :=
    adaptiveMixedOutsidePrimeSupport_prime support scale
  have outside_large : ∀ prime ∈ outside, length < prime := by
    intro prime selected
    have excluded : prime ∉ Nat.primesLE length :=
      (Finset.mem_sdiff.mp selected).2
    by_contra not_large
    have bounded : prime ≤ length := Nat.le_of_not_gt not_large
    exact excluded (Nat.mem_primesLE.mpr
      ⟨bounded, outside_prime prime selected⟩)
  obtain ⟨residue, bounded, survives⟩ :=
    adaptivePrimeProgression_exists_simultaneous_avoiding_residue
      outside length (fun index => 1 + index * modulus)
      outside_prime outside_large
  have outside_modulus :
      adaptiveMixedOutsideModulus support scale = ∏ prime ∈ outside, prime := by
    rfl
  refine ⟨(0, residue), rfl, ?_⟩
  intro index small
  change 1 + index * modulus ∈
    adaptiveMixedOutcomeActiveIndices support scale (0, residue)
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor
    · omega
    · have index_bound : index ≤ length - 1 := Nat.le_pred_of_lt small
      exact Nat.add_le_add_left (Nat.mul_le_mul_right modulus index_bound) 1
  · unfold adaptiveMixedPrimePatternSamples
    apply Finset.mem_product.mpr
    constructor
    · unfold adaptiveMixedPrimeTypeCenters
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr modulus_positive
      · have coprime : modulus.Coprime (1 + index * modulus) := by
          exact (Nat.coprime_add_mul_right_right modulus 1 index).mpr
            (Nat.coprime_one_right modulus)
        change modulus.Coprime ((0 + (1 + index * modulus)) % modulus)
        simpa only [Nat.zero_add] using
          ((ZMod.coprime_mod_iff_coprime (1 + index * modulus) modulus).mpr
            coprime.symm).symm
    · unfold adaptiveMixedOutsideSurvivors
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        rw [outside_modulus]
        exact bounded
      · have coprime :
            (adaptiveMixedOutsideModulus support scale).Coprime
              (residue + (1 + index * modulus)) := by
          rw [outside_modulus]
          exact survives index small
        simpa using
          ((ZMod.coprime_mod_iff_coprime
            (residue + (1 + index * modulus))
            (adaptiveMixedOutsideModulus support scale)).mpr
              coprime.symm).symm

end Erdos1139

