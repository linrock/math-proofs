module

public import ActualMajorArcPositivityLocalFactors433

@[expose] public section


/-!
# Signed prime-denominator rational-center phases

A nonprincipal major center cannot be declared positive: incompatible
residue triples contribute genuinely signed additive-character phases.
For a prime denominator avoiding `2*a*d`, the three genuine unit-residue
phase sums are all `-1`.  Their signed total over all nonzero rational
numerators is therefore `-(p-1)`; adding the principal denominator term
recovers exactly the actual positive finite-field singular factor.

The complete selector-restricted composite-denominator Euler coupling and
integrated major-arc asymptotic are not asserted here.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The genuine additive-character phase sum on unit residue classes
modulo a rational major-arc denominator. -/
noncomputable def actualMajorArcUnitResiduePhase
    (modulus : ℕ) (frequency : ℤ) : ℂ :=
  ∑ r ∈ (Finset.range modulus).filter
      (fun r => Nat.gcd r modulus = 1),
    GoldbachChain.e ((frequency : ℝ) * r / modulus)

/-- A unit-frequency additive-character sum is the exact Möbius value,
by the independently audited Goldbach Ramanujan-sum theorem. -/
theorem actualMajorArcUnitResiduePhase_eq_moebius
    (modulus : ℕ) (frequency : ℤ)
    (hmodulus : 0 < modulus)
    (hunit : Int.gcd frequency modulus = 1) :
    actualMajorArcUnitResiduePhase modulus frequency =
      (ArithmeticFunction.moebius modulus : ℂ) := by
  exact GoldbachChain.MinorArc.ramanujan_sum_coprime
    frequency modulus hmodulus hunit

/-- At a genuine prime denominator, every unit-frequency residue phase is
strictly negative: it equals `-1`, not `+1` or zero. -/
theorem actualMajorArcUnitResiduePhase_prime_eq_neg_one
    (p : ℕ) (frequency : ℤ) (hp : p.Prime)
    (hunit : Int.gcd frequency p = 1) :
    actualMajorArcUnitResiduePhase p frequency = -1 := by
  rw [actualMajorArcUnitResiduePhase_eq_moebius p frequency hp.pos hunit,
    ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- Natural coprimality gives exactly the integer-frequency gcd required
by the genuine rational-center Ramanujan phase theorem. -/
theorem actualMajorArc_natCast_frequency_gcd
    (frequency modulus : ℕ)
    (hunit : Nat.Coprime frequency modulus) :
    Int.gcd (frequency : ℤ) modulus = 1 := by
  simpa [Nat.Coprime] using hunit

/-- Changing the sign of an integral unit frequency preserves its genuine
rational-denominator coprimality. -/
theorem actualMajorArc_neg_natCast_frequency_gcd
    (frequency modulus : ℕ)
    (hunit : Nat.Coprime frequency modulus) :
    Int.gcd (-(frequency : ℤ)) modulus = 1 := by
  simpa using actualMajorArc_natCast_frequency_gcd
    frequency modulus hunit

/-- The actual three independent rational-center phase factors for the
original affine forms `label`, `a*q`, and `-2*d*r`. -/
noncomputable def actualMajorArcGenericPrimeCenterPhase
    (p a d h : ℕ) : ℂ :=
  actualMajorArcUnitResiduePhase p (h : ℤ) *
    actualMajorArcUnitResiduePhase p ((a * h : ℕ) : ℤ) *
    actualMajorArcUnitResiduePhase p (-(2 * d * h : ℕ) : ℤ)

/-- At every unit rational numerator and every prime avoiding `2*a*d`,
the *actual complete three-coordinate phase product* is `-1`.  Incompatible
residue classes are included, not falsely discarded. -/
theorem actualMajorArcGenericPrimeCenterPhase_eq_neg_one
    (p a d h : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (ha : ¬ p ∣ a) (hd : ¬ p ∣ d)
    (hh : Nat.Coprime h p) :
    actualMajorArcGenericPrimeCenterPhase p a d h = -1 := by
  have haunit : Nat.Coprime a p :=
    (hp.coprime_iff_not_dvd.mpr ha).symm
  have hdunit : Nat.Coprime d p :=
    (hp.coprime_iff_not_dvd.mpr hd).symm
  have htwo : Nat.Coprime 2 p := by
    apply Nat.Coprime.symm
    apply (hp.coprime_iff_not_dvd).mpr
    intro hdivide
    exact hpodd
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdivide)
  have hah : Nat.Coprime (a * h) p := haunit.mul_left hh
  have hdh : Nat.Coprime (2 * d * h) p :=
    (htwo.mul_left hdunit).mul_left hh
  unfold actualMajorArcGenericPrimeCenterPhase
  rw [actualMajorArcUnitResiduePhase_prime_eq_neg_one
      p (h : ℤ) hp (actualMajorArc_natCast_frequency_gcd h p hh),
    actualMajorArcUnitResiduePhase_prime_eq_neg_one
      p ((a * h : ℕ) : ℤ) hp
        (actualMajorArc_natCast_frequency_gcd (a * h) p hah),
    actualMajorArcUnitResiduePhase_prime_eq_neg_one
      p (-(2 * d * h : ℕ) : ℤ) hp
        (actualMajorArc_neg_natCast_frequency_gcd (2 * d * h) p hdh)]
  ring

/-- The actual reduced rational numerators modulo a prime are exactly
`p-1` in number. -/
theorem actualMajorArc_prime_unit_numerators_card
    (p : ℕ) (hp : p.Prime) :
    ((Finset.range p).filter (fun h => Nat.gcd h p = 1)).card =
      p - 1 := by
  rw [← Nat.totient_prime hp, Nat.totient_eq_card_coprime]
  congr 1
  ext h
  simp [Nat.Coprime, Nat.gcd_comm]

/-- Summing ALL genuine nonprincipal rational numerators at a generic prime
gives the exact strictly negative center-phase contribution `-(p-1)`. -/
theorem actualMajorArcGenericPrimeCenterPhase_sum
    (p a d : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (ha : ¬ p ∣ a) (hd : ¬ p ∣ d) :
    (∑ h ∈ (Finset.range p).filter
        (fun h => Nat.gcd h p = 1),
      actualMajorArcGenericPrimeCenterPhase p a d h) =
        -((p - 1 : ℕ) : ℂ) := by
  calc
    (∑ h ∈ (Finset.range p).filter
        (fun h => Nat.gcd h p = 1),
      actualMajorArcGenericPrimeCenterPhase p a d h) =
        ∑ _h ∈ (Finset.range p).filter
            (fun h => Nat.gcd h p = 1), (-1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro h hh
      exact actualMajorArcGenericPrimeCenterPhase_eq_neg_one
        p a d h hp hpodd ha hd (Finset.mem_filter.mp hh).2
    _ = -(((Finset.range p).filter
          (fun h => Nat.gcd h p = 1)).card : ℂ) := by
      simp
    _ = -((p - 1 : ℕ) : ℂ) := by
      rw [actualMajorArc_prime_unit_numerators_card p hp]

/-- The exact normalized nonprincipal prime-denominator rational-center
correction is NEGATIVE: `-1/(p-1)^2`. -/
theorem actualMajorArcGenericPrimeCenter_signed_correction
    (p a d : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (ha : ¬ p ∣ a) (hd : ¬ p ∣ d) :
    (∑ h ∈ (Finset.range p).filter
        (fun h => Nat.gcd h p = 1),
      actualMajorArcGenericPrimeCenterPhase p a d h) /
        ((p : ℂ) - 1) ^ 3 =
      -(1 : ℂ) / ((p : ℂ) - 1) ^ 2 := by
  rw [actualMajorArcGenericPrimeCenterPhase_sum p a d hp hpodd ha hd]
  have hpone : (p : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (show (p : ℝ) - 1 ≠ 0 by
      have hreal : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith)
  push_cast [Nat.cast_sub hp.one_le]
  field_simp

/-- Adding the principal rational center to the COMPLETE signed generic
prime-denominator center correction yields exactly the positive local
singular factor `1-1/(p-1)^2`. -/
theorem actualMajorArcGenericPrimeCenter_principal_plus_signed_eq_local_factor
    (p a d : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (ha : ¬ p ∣ a) (hd : ¬ p ∣ d) :
    (1 +
      (∑ h ∈ (Finset.range p).filter
          (fun h => Nat.gcd h p = 1),
        actualMajorArcGenericPrimeCenterPhase p a d h) /
          ((p : ℂ) - 1) ^ 3).re =
      actualMajorArcGenericLocalFactor p := by
  rw [actualMajorArcGenericPrimeCenter_signed_correction
    p a d hp hpodd ha hd]
  have hcast :
      (((-1 / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ)) =
        -(1 : ℂ) / ((p : ℂ) - 1) ^ 2 := by
    push_cast
    rfl
  rw [← hcast]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
  rw [actualMajorArcGenericLocalFactor_eq_one_sub_inverse_square p hp.one_lt]
  ring

/-- Exact local bridge from the SIGNED rational-center character sum to the
ACTUAL three-form finite-field solution density.  This is the prime-level
singular-series coupling, not an assertion of global major-arc positivity. -/
theorem actualMajorArcGenericPrimeCenter_signed_phase_eq_actual_local_density
    (p a d : ℕ) [Fact p.Prime]
    (hp : p.Prime) (hpodd : p ≠ 2)
    (ha : ¬ p ∣ a) (hd : ¬ p ∣ d) :
    (1 +
      (∑ h ∈ (Finset.range p).filter
          (fun h => Nat.gcd h p = 1),
        actualMajorArcGenericPrimeCenterPhase p a d h) /
          ((p : ℂ) - 1) ^ 3).re =
      (((actualMajorArcGenericLocalPrimePairs (ZMod p)
          (a : ZMod p) ((2 : ZMod p) * (d : ZMod p))).card : ℝ) /
            (p : ℝ) ^ 2) *
          ((p : ℝ) / ((p : ℝ) - 1)) ^ 3 := by
  rw [actualMajorArcGenericPrimeCenter_principal_plus_signed_eq_local_factor
    p a d hp hpodd ha hd]
  exact (actualMajorArcGenericLocalPrimePairs_normalized_factor
    p a d hp hpodd ha hd).symm


end Erdos689
