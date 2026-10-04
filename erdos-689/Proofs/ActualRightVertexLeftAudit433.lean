module

public import ActualRightVertexReduction433

@[expose] public section


/-!
# Safe moving-determinant infrastructure for actual fixed-left vertices

A fixed-left manuscript vertex has the form `x = a*r`, where `a` divides
the switched support product and `r` is prime.  Unlike a fixed right vertex,
`r` need not exceed the sieve cutoff: the genuine exceptional case `r = 3`
cannot simply be discarded.  Excluding the fixed base modulus `6*W`, and
then one genuine moving outside prime, handles every branch without an
unproved exceptional-prime selector assumption.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- An actual prime strictly outside the entire fixed support modulus
exists unconditionally; it can be used when the determinant prime already
divides `6*W`. -/
theorem actualLeftAuxiliaryPrime_exists (S : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ 6 * (∏ p ∈ S, p) < q := by
  obtain ⟨q, hqbound, hqprime⟩ :=
    Nat.exists_infinite_primes (6 * (∏ p ∈ S, p) + 1)
  exact ⟨q, hqprime, by omega⟩

/-- The canonical fixed auxiliary outside prime, chosen once per support. -/
noncomputable def actualLeftAuxiliaryPrime (S : Finset ℕ) : ℕ :=
  Classical.choose (actualLeftAuxiliaryPrime_exists S)

/-- The canonical auxiliary number is genuinely prime and strictly larger
than the full excluded modulus `6*W`. -/
theorem actualLeftAuxiliaryPrime_prime_and_gt
    (S : Finset ℕ) :
    (actualLeftAuxiliaryPrime S).Prime ∧
      6 * (∏ p ∈ S, p) < actualLeftAuxiliaryPrime S :=
  Classical.choose_spec (actualLeftAuxiliaryPrime_exists S)

/-- If the determinant prime is already in the fixed excluded modulus,
use the fixed auxiliary outside prime; otherwise exclude the determinant
prime itself. -/
noncomputable def actualLeftMovingExcludedPrime
    (S : Finset ℕ) (r : ℕ) : ℕ :=
  if r ∣ 6 * (∏ p ∈ S, p) then actualLeftAuxiliaryPrime S else r

/-- The actually chosen moving excluded number is always prime, coprime to
the true fixed modulus, and at least five, including the determinant-three
and support-prime branches. -/
theorem actualLeftMovingExcludedPrime_prime_coprime_ge_five
    (S : Finset ℕ) (r : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hr : r.Prime) :
    (actualLeftMovingExcludedPrime S r).Prime ∧
      Nat.Coprime (actualLeftMovingExcludedPrime S r)
        (6 * (∏ p ∈ S, p)) ∧
      5 ≤ actualLeftMovingExcludedPrime S r := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hM : 0 < 6 * W := by positivity
  by_cases hinside : r ∣ 6 * W
  · have haux := actualLeftAuxiliaryPrime_prime_and_gt S
    have hinside' : r ∣ 6 * (∏ p ∈ S, p) := hinside
    change (actualLeftMovingExcludedPrime S r).Prime ∧
      Nat.Coprime (actualLeftMovingExcludedPrime S r) (6 * W) ∧
        5 ≤ actualLeftMovingExcludedPrime S r
    unfold actualLeftMovingExcludedPrime
    simp only [hinside', ↓reduceIte]
    refine ⟨haux.1, ?_, by omega⟩
    apply (haux.1.coprime_iff_not_dvd).mpr
    exact Nat.not_dvd_of_pos_of_lt hM haux.2
  · change (actualLeftMovingExcludedPrime S r).Prime ∧
      Nat.Coprime (actualLeftMovingExcludedPrime S r) (6 * W) ∧
        5 ≤ actualLeftMovingExcludedPrime S r
    have hinside' : ¬ r ∣ 6 * (∏ p ∈ S, p) := hinside
    unfold actualLeftMovingExcludedPrime
    simp only [hinside', ↓reduceIte]
    refine ⟨hr, (hr.coprime_iff_not_dvd).mpr hinside, ?_⟩
    have hrnot2 : r ≠ 2 := by
      intro heq
      apply hinside
      rw [heq]
      exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) W
    have hrnot3 : r ≠ 3 := by
      intro heq
      apply hinside
      rw [heq]
      exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) W
    have hrnot4 : r ≠ 4 := by
      intro heq
      subst r
      norm_num at hr
    have htwo := hr.two_le
    omega

/-- Any genuine sieve prime coprime to the chosen moving modulus avoids the
ENTIRE actual fixed-left determinant `a*r`; this includes `r=3`, every
support-prime branch, and every moving external prime branch. -/
theorem actualLeftMovingExcludedPrime_avoids_determinant
    (S : Finset ℕ) (a r p : ℕ)
    (ha : a ∣ ∏ s ∈ S, s)
    (hp : p.Prime)
    (hcoprime : Nat.Coprime p
      ((6 * (∏ s ∈ S, s)) * actualLeftMovingExcludedPrime S r)) :
    ¬ p ∣ a * r := by
  let W : ℕ := ∏ s ∈ S, s
  let q := actualLeftMovingExcludedPrime S r
  have hpnot : ¬ p ∣ (6 * W) * q :=
    (hp.coprime_iff_not_dvd.mp hcoprime)
  intro hdivisor
  rcases (hp.dvd_mul).mp hdivisor with hcoefficient | hremaining
  · apply hpnot
    have hpW : p ∣ W := dvd_trans hcoefficient ha
    have hpM : p ∣ 6 * W := dvd_mul_of_dvd_right hpW 6
    exact dvd_mul_of_dvd_left hpM q
  · by_cases hinside : r ∣ 6 * W
    · apply hpnot
      have hpM : p ∣ 6 * W := dvd_trans hremaining hinside
      exact dvd_mul_of_dvd_left hpM q
    · have hq : q = r := by
        change (if r ∣ 6 * W then actualLeftAuxiliaryPrime S else r) = r
        exact if_neg hinside
      apply hpnot
      rw [hq]
      exact dvd_mul_of_dvd_right hremaining (6 * W)

/-- The genuinely enlarged fixed support modulus has exactly twice the
original support totient; no exceptional-prime local density is omitted. -/
theorem actualLeftSupport_totient_six_mul
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    (6 * (∏ p ∈ S, p)).totient =
      2 * (∏ p ∈ S, p).totient := by
  let W : ℕ := ∏ p ∈ S, p
  have hthree : Nat.Coprime 3 (2 * W) := by
    apply ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr
    intro hdivisor
    rcases ((by norm_num : Nat.Prime 3).dvd_mul).mp hdivisor with
      htwo | hsupportdivisor
    · norm_num at htwo
    · have hmember := prime_mem_of_dvd_support_product
        (by norm_num : Nat.Prime 3)
        (fun p hp => (hsupport p hp).1) hsupportdivisor
      exact (by omega : ¬ 3 < 3) (hsupport 3 hmember).2
  have htwo := actualOddSupport_totient_two_mul S hsupport
  change (6 * W).totient = 2 * W.totient
  calc
    (6 * W).totient = (3 * (2 * W)).totient := by
      congr 1
      ring
    _ = (3 : ℕ).totient * (2 * W).totient := Nat.totient_mul hthree
    _ = 2 * W.totient := by
      rw [Nat.totient_prime (by norm_num), htwo]

#print axioms Erdos689.actualLeftAuxiliaryPrime_exists
#print axioms Erdos689.actualLeftAuxiliaryPrime_prime_and_gt
#print axioms Erdos689.actualLeftMovingExcludedPrime_prime_coprime_ge_five
#print axioms Erdos689.actualLeftMovingExcludedPrime_avoids_determinant
#print axioms Erdos689.actualLeftSupport_totient_six_mul

end Erdos689
