import ActualMajorArcPositivityPhase433

/-!
# Actual signed phases at arbitrary coprime rational denominators

The original three affine prime forms have signed rational-center phases.
At every denominator coprime to `2*a*d`, each of their three unit-residue
character sums is the actual Möbius value.  Summing all reduced numerators
therefore gives `φ(q)*μ(q)^3`, and normalizing by the three prime-residue
densities gives `μ(q)/φ(q)^2`.  Nonsquarefree denominators vanish.

The integrated major-arc approximation and support-dividing denominators
are not asserted in this file.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- Reduced rational numerators modulo an arbitrary positive denominator
are counted exactly by Euler's totient. -/
theorem actualMajorArcComposite_unit_numerators_card
    (modulus : ℕ) :
    ((Finset.range modulus).filter
      (fun h => Nat.gcd h modulus = 1)).card =
        Nat.totient modulus := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext h
  simp [Nat.Coprime, Nat.gcd_comm]

/-- The genuine three-form signed phase at ANY denominator coprime to the
actual original coefficients is the cube of its Möbius value. -/
theorem actualMajorArcCompositeCenterPhase_eq_moebius_cubed
    (modulus a d h : ℕ)
    (hmodulus : 0 < modulus)
    (hcoeff : Nat.Coprime modulus (2 * a * d))
    (hunit : Nat.Coprime h modulus) :
    actualMajorArcGenericPrimeCenterPhase modulus a d h =
      (ArithmeticFunction.moebius modulus : ℂ) ^ 3 := by
  have haunit : Nat.Coprime a modulus := by
    apply hcoeff.symm.coprime_dvd_left
    refine ⟨2 * d, ?_⟩
    ring
  have hdunit : Nat.Coprime (2 * d) modulus := by
    apply hcoeff.symm.coprime_dvd_left
    refine ⟨a, ?_⟩
    ring
  have hah : Nat.Coprime (a * h) modulus := haunit.mul_left hunit
  have hdh : Nat.Coprime (2 * d * h) modulus :=
    hdunit.mul_left hunit
  unfold actualMajorArcGenericPrimeCenterPhase
  rw [actualMajorArcUnitResiduePhase_eq_moebius
      modulus (h : ℤ) hmodulus
        (actualMajorArc_natCast_frequency_gcd h modulus hunit),
    actualMajorArcUnitResiduePhase_eq_moebius
      modulus ((a * h : ℕ) : ℤ) hmodulus
        (actualMajorArc_natCast_frequency_gcd (a * h) modulus hah),
    actualMajorArcUnitResiduePhase_eq_moebius
      modulus (-(2 * d * h : ℕ) : ℤ) hmodulus
        (actualMajorArc_neg_natCast_frequency_gcd
          (2 * d * h) modulus hdh)]
  ring

/-- The COMPLETE sum over all actual reduced rational numerators at an
arbitrary coefficient-coprime denominator, including every signed phase. -/
theorem actualMajorArcCompositeCenterPhase_sum
    (modulus a d : ℕ)
    (hmodulus : 0 < modulus)
    (hcoeff : Nat.Coprime modulus (2 * a * d)) :
    (∑ h ∈ (Finset.range modulus).filter
        (fun h => Nat.gcd h modulus = 1),
      actualMajorArcGenericPrimeCenterPhase modulus a d h) =
        (Nat.totient modulus : ℂ) *
          (ArithmeticFunction.moebius modulus : ℂ) ^ 3 := by
  calc
    (∑ h ∈ (Finset.range modulus).filter
        (fun h => Nat.gcd h modulus = 1),
      actualMajorArcGenericPrimeCenterPhase modulus a d h) =
        ∑ _h ∈ (Finset.range modulus).filter
            (fun h => Nat.gcd h modulus = 1),
          (ArithmeticFunction.moebius modulus : ℂ) ^ 3 := by
      apply Finset.sum_congr rfl
      intro h hh
      exact actualMajorArcCompositeCenterPhase_eq_moebius_cubed
        modulus a d h hmodulus hcoeff (Finset.mem_filter.mp hh).2
    _ = (Nat.totient modulus : ℂ) *
          (ArithmeticFunction.moebius modulus : ℂ) ^ 3 := by
      rw [Finset.sum_const, nsmul_eq_mul,
        actualMajorArcComposite_unit_numerators_card modulus]

/-- Every integer Möbius value is unchanged by cubing: this includes the
zero value at nonsquarefree denominators, not merely the squarefree case. -/
theorem actualMajorArcComposite_moebius_cube
    (modulus : ℕ) :
    (ArithmeticFunction.moebius modulus : ℂ) ^ 3 =
      (ArithmeticFunction.moebius modulus : ℂ) := by
  obtain hzero | hone | hminus :=
    ArithmeticFunction.moebius_eq_or modulus
  · rw [hzero]
    norm_num
  · rw [hone]
    norm_num
  · rw [hminus]
    norm_num

/-- The true normalized signed contribution at ANY coefficient-coprime
rational denominator is `μ(q)/φ(q)^2`, including composite denominators. -/
theorem actualMajorArcCompositeCenter_signed_correction
    (modulus a d : ℕ)
    (hmodulus : 0 < modulus)
    (hcoeff : Nat.Coprime modulus (2 * a * d)) :
    (∑ h ∈ (Finset.range modulus).filter
        (fun h => Nat.gcd h modulus = 1),
      actualMajorArcGenericPrimeCenterPhase modulus a d h) /
        (Nat.totient modulus : ℂ) ^ 3 =
      (ArithmeticFunction.moebius modulus : ℂ) /
        (Nat.totient modulus : ℂ) ^ 2 := by
  rw [actualMajorArcCompositeCenterPhase_sum
    modulus a d hmodulus hcoeff,
    actualMajorArcComposite_moebius_cube modulus]
  have htotient : (Nat.totient modulus : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hmodulus).ne'
  field_simp

/-- Every nonsquarefree denominator has ZERO total signed rational-center
contribution for the genuine original three affine prime forms. -/
theorem actualMajorArcCompositeCenter_signed_correction_zero_of_not_squarefree
    (modulus a d : ℕ)
    (hmodulus : 0 < modulus)
    (hcoeff : Nat.Coprime modulus (2 * a * d))
    (hsquarefree : ¬ Squarefree modulus) :
    (∑ h ∈ (Finset.range modulus).filter
        (fun h => Nat.gcd h modulus = 1),
      actualMajorArcGenericPrimeCenterPhase modulus a d h) /
        (Nat.totient modulus : ℂ) ^ 3 = 0 := by
  rw [actualMajorArcCompositeCenter_signed_correction
    modulus a d hmodulus hcoeff,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsquarefree]
  norm_num

/-- The genuine signed coefficient supplied by all reduced numerator centers
at an arbitrary denominator.  Its values are the Möbius/totient terms
proved directly from the actual three affine phases above. -/
noncomputable def actualMajorArcGenericSignedCoefficient :
    ArithmeticFunction ℝ :=
  ⟨fun modulus =>
    (ArithmeticFunction.moebius modulus : ℝ) /
      (Nat.totient modulus : ℝ) ^ 2, by simp⟩

/-- Convenient exact evaluation of the genuine rational-center
arithmetic coefficient. -/
theorem actualMajorArcGenericSignedCoefficient_apply
    (modulus : ℕ) :
    actualMajorArcGenericSignedCoefficient modulus =
      (ArithmeticFunction.moebius modulus : ℝ) /
        (Nat.totient modulus : ℝ) ^ 2 := rfl

/-- CRT-compatible multiplicativity of the ACTUAL signed three-phase
center coefficient at every pair of coprime rational denominators. -/
theorem actualMajorArcGenericSignedCoefficient_isMultiplicative :
    actualMajorArcGenericSignedCoefficient.IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [actualMajorArcGenericSignedCoefficient_apply]
  · intro left right hcoprime
    simp only [actualMajorArcGenericSignedCoefficient_apply]
    rw [ArithmeticFunction.isMultiplicative_moebius.2 hcoprime,
      Nat.totient_mul hcoprime]
    push_cast
    rw [mul_pow, mul_div_mul_comm]

/-- At a genuine prime denominator the multiplicative center coefficient is
the exact negative local correction `-1/(p-1)^2`. -/
theorem actualMajorArcGenericSignedCoefficient_prime
    (p : ℕ) (hp : p.Prime) :
    actualMajorArcGenericSignedCoefficient p =
      -(1 : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  rw [actualMajorArcGenericSignedCoefficient_apply,
    ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_prime hp]
  push_cast [Nat.cast_sub hp.one_le]
  ring

/-- Exact squarefree CRT/Euler coupling: the sum of ALL genuine signed
coefficients at divisors of a squarefree modulus equals the product of its
actual prime local singular factors. -/
theorem actualMajorArcComposite_divisor_sum_eq_local_factor_product
    (modulus : ℕ) (hsquarefree : Squarefree modulus) :
    (∑ divisor ∈ modulus.divisors,
      actualMajorArcGenericSignedCoefficient divisor) =
        ∏ p ∈ modulus.primeFactors,
          actualMajorArcGenericLocalFactor p := by
  have heuler :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      actualMajorArcGenericSignedCoefficient_isMultiplicative hsquarefree
  rw [← heuler]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [actualMajorArcGenericSignedCoefficient_prime p hpprime,
    actualMajorArcGenericLocalFactor_eq_one_sub_inverse_square
      p hpprime.one_lt]
  ring

/-- The COMPLETE signed rational-center coefficient sum over every divisor
of ANY odd squarefree modulus retains the absolute support-independent
positive lower bound `1/2`. -/
theorem actualMajorArcComposite_divisor_sum_ge_half
    (modulus : ℕ) (hsquarefree : Squarefree modulus)
    (hodd : ¬ 2 ∣ modulus) :
    (1 / 2 : ℝ) ≤
      ∑ divisor ∈ modulus.divisors,
        actualMajorArcGenericSignedCoefficient divisor := by
  rw [actualMajorArcComposite_divisor_sum_eq_local_factor_product
    modulus hsquarefree]
  apply actualMajorArcGenericLocalFactor_product_ge_half
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdivide : p ∣ modulus := (Nat.mem_primeFactors.mp hp).2.1
  have hpnot : p ≠ 2 := by
    intro heq
    apply hodd
    simpa [heq] using hpdivide
  have hptwo := hpprime.two_le
  omega

/-- The Euler product is exactly the sum of the ACTUAL complete signed
three-coordinate rational-center phases at every divisor, not merely an
abstract multiplicative coefficient.  All denominator numerators and all
three genuine prime-residue character sums are present. -/
theorem actualMajorArcComposite_divisor_signed_phase_sum_eq_local_factor_product
    (modulus a d : ℕ)
    (hsquarefree : Squarefree modulus)
    (hcoeff : Nat.Coprime modulus (2 * a * d)) :
    (∑ divisor ∈ modulus.divisors,
      ((∑ h ∈ (Finset.range divisor).filter
          (fun h => Nat.gcd h divisor = 1),
        actualMajorArcGenericPrimeCenterPhase divisor a d h) /
          (Nat.totient divisor : ℂ) ^ 3).re) =
        ∏ p ∈ modulus.primeFactors,
          actualMajorArcGenericLocalFactor p := by
  rw [← actualMajorArcComposite_divisor_sum_eq_local_factor_product
    modulus hsquarefree]
  apply Finset.sum_congr rfl
  intro divisor hdivisor
  have hdivide : divisor ∣ modulus :=
    (Nat.mem_divisors.mp hdivisor).1
  have hpositive : 0 < divisor := by
    have hnonzero : divisor ≠ 0 := by
      intro hzero
      subst divisor
      exact hsquarefree.ne_zero (by simpa using hdivide)
    omega
  have hdivcoeff : Nat.Coprime divisor (2 * a * d) :=
    hcoeff.coprime_dvd_left hdivide
  rw [actualMajorArcCompositeCenter_signed_correction
    divisor a d hpositive hdivcoeff]
  have hcast :
      (((ArithmeticFunction.moebius divisor : ℝ) /
          (Nat.totient divisor : ℝ) ^ 2 : ℝ) : ℂ) =
        (ArithmeticFunction.moebius divisor : ℂ) /
          (Nat.totient divisor : ℂ) ^ 2 := by
    push_cast
    rfl
  rw [← hcast, Complex.ofReal_re,
    actualMajorArcGenericSignedCoefficient_apply]

/-- The COMPLETE signed rational-center sum over every denominator dividing
ANY odd squarefree coefficient-coprime modulus has the absolute positive
lower bound `1/2`.  This is a true composite-denominator CRT/Euler result
for the original three affine forms, with no positivity assumed for an
individual nonprincipal center. -/
theorem actualMajorArcComposite_divisor_signed_phase_sum_ge_half
    (modulus a d : ℕ)
    (hsquarefree : Squarefree modulus)
    (hodd : ¬ 2 ∣ modulus)
    (hcoeff : Nat.Coprime modulus (2 * a * d)) :
    (1 / 2 : ℝ) ≤
      ∑ divisor ∈ modulus.divisors,
        ((∑ h ∈ (Finset.range divisor).filter
            (fun h => Nat.gcd h divisor = 1),
          actualMajorArcGenericPrimeCenterPhase divisor a d h) /
            (Nat.totient divisor : ℂ) ^ 3).re := by
  rw [actualMajorArcComposite_divisor_signed_phase_sum_eq_local_factor_product
    modulus a d hsquarefree hcoeff,
    ← actualMajorArcComposite_divisor_sum_eq_local_factor_product
      modulus hsquarefree]
  exact actualMajorArcComposite_divisor_sum_ge_half
    modulus hsquarefree hodd

#print axioms Erdos689.actualMajorArcComposite_unit_numerators_card
#print axioms Erdos689.actualMajorArcCompositeCenterPhase_eq_moebius_cubed
#print axioms Erdos689.actualMajorArcCompositeCenterPhase_sum
#print axioms Erdos689.actualMajorArcComposite_moebius_cube
#print axioms Erdos689.actualMajorArcCompositeCenter_signed_correction
#print axioms Erdos689.actualMajorArcCompositeCenter_signed_correction_zero_of_not_squarefree
#print axioms Erdos689.actualMajorArcGenericSignedCoefficient_apply
#print axioms Erdos689.actualMajorArcGenericSignedCoefficient_isMultiplicative
#print axioms Erdos689.actualMajorArcGenericSignedCoefficient_prime
#print axioms Erdos689.actualMajorArcComposite_divisor_sum_eq_local_factor_product
#print axioms Erdos689.actualMajorArcComposite_divisor_sum_ge_half
#print axioms Erdos689.actualMajorArcComposite_divisor_signed_phase_sum_eq_local_factor_product
#print axioms Erdos689.actualMajorArcComposite_divisor_signed_phase_sum_ge_half

end Erdos689
