module

public import ActualLeftVertexMajorIntegration433
public import ActualMajorArcPositivityTruncation433

@[expose] public section


/-!
# Cancellation of genuine high-support-conductor rational phases

The positive outside-support rational-center subseries does not control the
full major region: shifted centers can have denominators divisible by higher
powers of switched support primes, and those contributions cannot simply be
discarded.  At a fixed support residue, however, the original label has
frequency one.  Its complete additive-character sum over every lift to a
higher prime-power conductor vanishes exactly.  This module proves that
genuine conductor cancellation, including the support-square and higher
two-power cases.  No full integrated major-arc positivity is asserted.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- Every complete additive-character sum at a nontrivial modulus and a
coprime frequency vanishes exactly, by the audited Goldbach orthogonality
theorem. -/
theorem actualMajorArcConductor_complete_unit_phase_sum_zero
    (modulus frequency : ℕ)
    (hmodulus : 1 < modulus)
    (hunit : Nat.Coprime frequency modulus) :
    (∑ t ∈ Finset.range modulus,
      GoldbachChain.e (((frequency : ℝ) * t) / modulus)) = 0 := by
  have hnot : ¬ modulus ∣ frequency := by
    intro hdivide
    have hgcd : Nat.gcd frequency modulus = modulus :=
      Nat.gcd_eq_right hdivide
    have hcoprime : Nat.gcd frequency modulus = 1 := hunit
    omega
  have hnotint : ¬ (modulus : ℤ) ∣ (frequency : ℤ) := by
    intro hdivide
    exact hnot (Int.natCast_dvd_natCast.mp hdivide)
  simpa [hnotint] using
    (GoldbachChain.MinorArc.char_orthogonality
      (frequency : ℤ) modulus (by omega))

/-- The exact phase at every lift of a fixed support residue separates into
its fixed support phase and the complete higher-conductor character. -/
theorem actualMajorArcConductor_support_lift_phase_factor
    (support lift residue frequency : ℕ)
    (hsupport : 0 < support)
    (hlift : 0 < lift) :
    (∑ t ∈ Finset.range lift,
      GoldbachChain.e
        (((frequency : ℝ) * (residue + support * t)) /
          (support * lift))) =
      GoldbachChain.e
        (((frequency : ℝ) * residue) / (support * lift)) *
        ∑ t ∈ Finset.range lift,
          GoldbachChain.e (((frequency : ℝ) * t) / lift) := by
  have hsreal : (support : ℝ) ≠ 0 := by exact_mod_cast hsupport.ne'
  have hlreal : (lift : ℝ) ≠ 0 := by exact_mod_cast hlift.ne'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [GoldbachChain.e_add]
  congr 1
  field_simp

/-- A fixed genuine support residue has ZERO total signed phase at any
strictly higher conductor with a coprime lifted frequency. -/
theorem actualMajorArcConductor_support_lift_phase_sum_zero
    (support lift residue frequency : ℕ)
    (hsupport : 0 < support)
    (hlift : 1 < lift)
    (hunit : Nat.Coprime frequency lift) :
    (∑ t ∈ Finset.range lift,
      GoldbachChain.e
        (((frequency : ℝ) * (residue + support * t)) /
          (support * lift))) = 0 := by
  rw [actualMajorArcConductor_support_lift_phase_factor
    support lift residue frequency hsupport (by omega),
    actualMajorArcConductor_complete_unit_phase_sum_zero
      lift frequency hlift hunit, mul_zero]

/-- At ANY genuine prime power with exponent at least two, the full sum of
all lifts of a fixed support residue is exactly zero.  This is the actual
missing support-conductor cancellation, not a positivity assumption. -/
theorem actualMajorArcConductor_prime_power_support_phase_sum_zero
    (p exponent residue frequency : ℕ)
    (hp : p.Prime)
    (hexponent : 2 ≤ exponent)
    (hunit : Nat.Coprime frequency p) :
    (∑ t ∈ Finset.range (p ^ (exponent - 1)),
      GoldbachChain.e
        (((frequency : ℝ) * (residue + p * t)) /
          (p ^ exponent))) = 0 := by
  have hpositive : 0 < exponent - 1 := by omega
  have hlift : 1 < p ^ (exponent - 1) :=
    one_lt_pow₀ hp.one_lt (by omega)
  have hunitpower : Nat.Coprime frequency (p ^ (exponent - 1)) :=
    hunit.pow_right _
  have hpower : p * p ^ (exponent - 1) = p ^ exponent := by
    conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ exponent)]
    rw [pow_succ]
    ring
  have hpowerReal :
      (p : ℝ) * ((p ^ (exponent - 1) : ℕ) : ℝ) =
        (p : ℝ) ^ exponent := by
    exact_mod_cast hpower
  simpa only [hpowerReal] using
    actualMajorArcConductor_support_lift_phase_sum_zero
      p (p ^ (exponent - 1)) residue frequency
        hp.pos hlift hunitpower

/-- In particular, every genuine support-square rational denominator has
zero label-cell phase after its COMPLETE set of fixed-residue lifts. -/
theorem actualMajorArcConductor_prime_square_support_phase_sum_zero
    (p residue frequency : ℕ)
    (hp : p.Prime)
    (hunit : Nat.Coprime frequency p) :
    (∑ t ∈ Finset.range p,
      GoldbachChain.e
        (((frequency : ℝ) * (residue + p * t)) /
          (p ^ 2))) = 0 := by
  simpa using
    actualMajorArcConductor_prime_power_support_phase_sum_zero
      p 2 residue frequency hp (by norm_num) hunit

/-- The same genuine conductor cancellation removes EVERY higher two-power
center; only the parity conductor itself can contribute a local factor. -/
theorem actualMajorArcConductor_two_power_phase_sum_zero
    (exponent residue frequency : ℕ)
    (hexponent : 2 ≤ exponent)
    (hodd : Nat.Coprime frequency 2) :
    (∑ t ∈ Finset.range (2 ^ (exponent - 1)),
      GoldbachChain.e
        (((frequency : ℝ) * (residue + 2 * t)) /
          (2 ^ exponent))) = 0 :=
  actualMajorArcConductor_prime_power_support_phase_sum_zero
    2 exponent residue frequency Nat.prime_two hexponent hodd


end Erdos689
