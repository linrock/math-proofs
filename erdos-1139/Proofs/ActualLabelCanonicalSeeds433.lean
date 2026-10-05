module

public import ActualLabelSummedCoefficient433

@[expose] public section


/-!
# Canonical seeds and assumption-free actual fixed-label coefficient sums

Every support divisor is odd.  Coprime support divisors `a,d` therefore make
`a` invertible modulo `2*d`.  The canonical finite-ring inverse constructs
the exact nonnegative seed for every coefficient pair, eliminating the last
seed-family hypothesis from the actual selector-cardinality cancellation.
-/

open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- A divisor of a support of odd primes is itself coprime to two. -/
theorem oddSupportDivisor_coprime_two
    (S : Finset ℕ) (a : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p) :
    Nat.Coprime a 2 := by
  have hsupportOdd : Nat.Coprime 2 (∏ p ∈ S, p) := by
    apply Nat.Coprime.prod_right
    intro p hp
    exact (Nat.coprime_primes Nat.prime_two (hsupport p hp).1).mpr
      (by have h := (hsupport p hp).2; omega)
  exact (hsupportOdd.coprime_dvd_right ha).symm

/-- The genuine left coefficient of any coprime support-divisor pair is
invertible modulo the entire doubled right coefficient. -/
theorem coprimeSupportDivisors_coprime_doubled
    (S : Finset ℕ) (a d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d) :
    Nat.Coprime a (2 * d) := by
  exact (Nat.coprime_mul_iff_right).mpr
    ⟨oddSupportDivisor_coprime_two S a hsupport ha, hcoprime⟩

/-- The canonical natural first seed is the genuine finite-ring inverse
solution of `a*q₀ = -z (mod 2*d)`. -/
noncomputable def actualLabelCanonicalSeedQ (z a d : ℕ) : ℕ :=
  ((-(z : ZMod (2 * d))) * (a : ZMod (2 * d))⁻¹).val

/-- The corresponding second seed is the exact natural quotient. -/
noncomputable def actualLabelCanonicalSeedR (z a d : ℕ) : ℕ :=
  (a * actualLabelCanonicalSeedQ z a d + z) / (2 * d)

/-- Finite-ring inversion supplies the exact natural seed, including its
canonical first-coordinate bound, without assuming an existing graph edge. -/
theorem actualLabelCanonicalSeeds_spec
    (z a d : ℕ) (hd : 0 < d)
    (hcoprime : Nat.Coprime a (2 * d)) :
    actualLabelCanonicalSeedQ z a d < 2 * d ∧
      2 * d * actualLabelCanonicalSeedR z a d =
        a * actualLabelCanonicalSeedQ z a d + z := by
  let _ : NeZero (2 * d) := ⟨by omega⟩
  have hcanonical :
      ((actualLabelCanonicalSeedQ z a d : ℕ) : ZMod (2 * d)) =
        (-(z : ZMod (2 * d))) * (a : ZMod (2 * d))⁻¹ := by
    exact ZMod.natCast_zmod_val _
  have hzero :
      ((a * actualLabelCanonicalSeedQ z a d + z : ℕ) :
        ZMod (2 * d)) = 0 := by
    push_cast
    rw [hcanonical]
    have hinverse := ZMod.coe_mul_inv_eq_one a hcoprime
    calc
      (a : ZMod (2 * d)) *
          (-(z : ZMod (2 * d)) * (a : ZMod (2 * d))⁻¹) +
          (z : ZMod (2 * d)) =
        -(z : ZMod (2 * d)) *
          ((a : ZMod (2 * d)) * (a : ZMod (2 * d))⁻¹) +
          (z : ZMod (2 * d)) := by ring
      _ = 0 := by rw [hinverse]; ring
  have hdivisor :
      2 * d ∣ a * actualLabelCanonicalSeedQ z a d + z :=
    (ZMod.natCast_eq_zero_iff
      (a * actualLabelCanonicalSeedQ z a d + z) (2 * d)).mp hzero
  constructor
  · exact ZMod.val_lt _
  · exact Nat.mul_div_cancel' hdivisor

/-- Every genuine coprime support-divisor pair has its canonical exact seed;
the pair need not correspond to an already known edge or prime solution. -/
theorem coprimeSupportDivisors_actualLabelCanonicalSeeds
    (S : Finset ℕ) (z a d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d) :
    actualLabelCanonicalSeedQ z a d < 2 * d ∧
      2 * d * actualLabelCanonicalSeedR z a d =
        a * actualLabelCanonicalSeedQ z a d + z := by
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  exact actualLabelCanonicalSeeds_spec z a d
    (Nat.pos_of_dvd_of_pos hd hW)
    (coprimeSupportDivisors_coprime_doubled S a d hsupport ha hcoprime)

/-- The full sum of *actual* unit-refined selected coefficient cardinalities,
using canonical finite-ring seeds, equals the exact three-state support Euler
product.  No seed or local-cardinality hypothesis is assumed. -/
theorem actualFixedLabelCanonicalSummedSelectorCoefficient_eq_product
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    actualFixedLabelSummedSelectorCoefficient S b z
      (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z) =
        ∏ p ∈ S,
          normalizedSwitchedFactor p
            (decide ((2 : ZMod p) * (z : ZMod p) = (b p : ZMod p) ∨
              (2 : ZMod p) * (-(z : ZMod p)) = (b p : ZMod p))) := by
  apply actualFixedLabelSummedSelectorCoefficient_eq_product
    S b z (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z)
    hsupport hz hb
  intro a ha d hd hcoprime
  exact (coprimeSupportDivisors_actualLabelCanonicalSeeds
    S z a d hsupport (Nat.mem_divisors.mp ha).1
      (Nat.mem_divisors.mp hd).1 hcoprime).2

/-- The actual selected double-divisor coefficient sum is at most one,
uniformly in the switched support, with no seed-family assumption. -/
theorem actualFixedLabelCanonicalSummedSelectorCoefficient_le_one
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    actualFixedLabelSummedSelectorCoefficient S b z
      (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z) ≤ 1 := by
  apply actualFixedLabelSummedSelectorCoefficient_le_one
    S b z (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z)
    hsupport hz hb
  intro a ha d hd hcoprime
  exact (coprimeSupportDivisors_actualLabelCanonicalSeeds
    S z a d hsupport (Nat.mem_divisors.mp ha).1
      (Nat.mem_divisors.mp hd).1 hcoprime).2

/-- Canonical actual selector cardinalities also retain the absolute
universal one-half lower bound, with no auxiliary seed assumptions. -/
theorem actualFixedLabelCanonicalSummedSelectorCoefficient_ge_half
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    (1 / 2 : ℝ) ≤ actualFixedLabelSummedSelectorCoefficient S b z
      (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z) := by
  apply actualFixedLabelSummedSelectorCoefficient_ge_half
    S b z (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z)
    hsupport hz hb
  intro a ha d hd hcoprime
  exact (coprimeSupportDivisors_actualLabelCanonicalSeeds
    S z a d hsupport (Nat.mem_divisors.mp ha).1
      (Nat.mem_divisors.mp hd).1 hcoprime).2

/-- Purely algebraic `605/12` rescaling of the genuine canonical normalized
selector sum.  It is not the actual Selberg leading constant: the even
excluded modulus `2*W` contributes a further reciprocal-totient factor four. -/
theorem actualFixedLabelCanonicalSummedSelectorCoefficient_selberg_leading_le
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    (605 / 12 : ℝ) * actualFixedLabelSummedSelectorCoefficient S b z
      (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z) ≤
        605 / 12 := by
  have hsum := actualFixedLabelCanonicalSummedSelectorCoefficient_le_one
    S b z hsupport hz hb
  nlinarith

/-- Genuine globally defined canonical seed functions exist simultaneously
for every coprime support-divisor pair.  Their normalized actual selector
sum is at most one, and its purely algebraic `605/12` rescaling has the
corresponding bound; this rescaling is not an actual graph-degree constant. -/
theorem exists_actualLabelCanonicalSeeds_and_uniform_selector_bound
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    ∃ q₀ r₀ : ℕ → ℕ → ℕ,
      (∀ a ∈ (∏ p ∈ S, p).divisors,
        ∀ d ∈ (∏ p ∈ S, p).divisors,
          Nat.Coprime a d →
            q₀ a d < 2 * d ∧ 2 * d * r₀ a d = a * q₀ a d + z) ∧
      actualFixedLabelSummedSelectorCoefficient S b z q₀ r₀ ≤ 1 ∧
      (605 / 12 : ℝ) *
        actualFixedLabelSummedSelectorCoefficient S b z q₀ r₀ ≤
          605 / 12 := by
  refine ⟨actualLabelCanonicalSeedQ z, actualLabelCanonicalSeedR z,
    ?_, actualFixedLabelCanonicalSummedSelectorCoefficient_le_one
      S b z hsupport hz hb,
    actualFixedLabelCanonicalSummedSelectorCoefficient_selberg_leading_le
      S b z hsupport hz hb⟩
  intro a ha d hd hcoprime
  exact coprimeSupportDivisors_actualLabelCanonicalSeeds
    S z a d hsupport (Nat.mem_divisors.mp ha).1
      (Nat.mem_divisors.mp hd).1 hcoprime


end Erdos689
