module

public import ActualRightVertexLeftAudit433

@[expose] public section


/-!
# Canonical moving fixed-left sieve and its genuine uniform leading constant

The excluded base modulus is `6*W`, and the moving outside prime is the
actual determinant prime unless that prime already divides the base.  This
canonically handles the genuine determinant-three case without a hidden
exceptional-prime selector hypothesis.  Its sharp edge-normalized main
constant is `1815/4`, uniformly in every moving determinant prime.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The actual canonical moving fixed-left sieve family at the true natural
block cutoff. -/
noncomputable def actualLeftCanonicalMovingSievePrimes
    (S : Finset ℕ) (n r : ℕ) : Finset ℕ :=
  (Nat.primesLE (selbergSquareRootBlockCutoff n ^ 2)).filter fun p =>
    Nat.Coprime p
      ((6 * (∏ s ∈ S, s)) * actualLeftMovingExcludedPrime S r)

/-- Membership is exactly primality, the actual block cutoff, and
coprimality to the complete fixed-times-moving excluded modulus. -/
theorem mem_actualLeftCanonicalMovingSievePrimes_iff
    (S : Finset ℕ) (n r p : ℕ) :
    p ∈ actualLeftCanonicalMovingSievePrimes S n r ↔
      p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧ p.Prime ∧
        Nat.Coprime p
          ((6 * (∏ s ∈ S, s)) * actualLeftMovingExcludedPrime S r) := by
  simp [actualLeftCanonicalMovingSievePrimes,
    Nat.mem_primesLE, and_assoc]

/-- Every actual moving-sieve member is genuinely prime. -/
theorem actualLeftCanonicalMovingSievePrimes_prime
    (S : Finset ℕ) (n r p : ℕ)
    (hp : p ∈ actualLeftCanonicalMovingSievePrimes S n r) :
    p.Prime :=
  ((mem_actualLeftCanonicalMovingSievePrimes_iff S n r p).mp hp).2.1

/-- The genuine moving-sieve product avoids the ENTIRE actual excluded
base-times-moving modulus. -/
theorem actualLeftCanonicalMovingSievePrimes_product_coprime
    (S : Finset ℕ) (n r : ℕ) :
    Nat.Coprime
      (∏ p ∈ actualLeftCanonicalMovingSievePrimes S n r, p)
      ((6 * (∏ s ∈ S, s)) * actualLeftMovingExcludedPrime S r) := by
  apply Nat.Coprime.prod_left
  intro p hp
  exact ((mem_actualLeftCanonicalMovingSievePrimes_iff S n r p).mp hp).2.2

/-- Every genuine moving sieve prime is strictly greater than two because
the fixed base modulus contains the factor six. -/
theorem actualLeftCanonicalMovingSievePrimes_gt_two
    (S : Finset ℕ) (n r p : ℕ)
    (hp : p ∈ actualLeftCanonicalMovingSievePrimes S n r) :
    2 < p := by
  have hprime := actualLeftCanonicalMovingSievePrimes_prime S n r p hp
  have hcoprime :=
    ((mem_actualLeftCanonicalMovingSievePrimes_iff S n r p).mp hp).2.2
  have hnot : p ≠ 2 := by
    intro heq
    subst p
    apply (Nat.prime_two.coprime_iff_not_dvd.mp hcoprime)
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6)
        (∏ s ∈ S, s)) (actualLeftMovingExcludedPrime S r)
  have htwo := hprime.two_le
  omega

/-- Exact prime-divisor characterization for the genuinely constructed
moving sieve product; no family existence premise is assumed. -/
theorem actualLeftCanonicalMovingSievePrimes_dvd_product_iff
    (S : Finset ℕ) (n r p : ℕ) (hp : p.Prime) :
    (p ∣ ∏ q ∈ actualLeftCanonicalMovingSievePrimes S n r, q) ↔
      p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧
        Nat.Coprime p
          ((6 * (∏ s ∈ S, s)) * actualLeftMovingExcludedPrime S r) := by
  constructor
  · intro hdivisor
    obtain ⟨q, hq, hpq⟩ :=
      (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hdivisor
    have hqprime := actualLeftCanonicalMovingSievePrimes_prime S n r q hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
    subst q
    have hmember :=
      (mem_actualLeftCanonicalMovingSievePrimes_iff S n r p).mp hq
    exact ⟨hmember.1, hmember.2.2⟩
  · rintro ⟨hcutoff, hcoprime⟩
    apply Finset.dvd_prod_of_mem (fun q : ℕ => q)
    exact (mem_actualLeftCanonicalMovingSievePrimes_iff S n r p).mpr
      ⟨hcutoff, hp, hcoprime⟩

/-- Every actual canonical sieve prime avoids the complete genuine
fixed-left determinant `a*r`, even when the determinant prime is three
or lies in the switched support. -/
theorem actualLeftCanonicalMovingSievePrimes_avoid_determinant
    (S : Finset ℕ) (n r a p : ℕ)
    (ha : a ∣ ∏ s ∈ S, s)
    (hp : p ∈ actualLeftCanonicalMovingSievePrimes S n r) :
    ¬ p ∣ a * r := by
  exact actualLeftMovingExcludedPrime_avoids_determinant
    S a r p ha
      (actualLeftCanonicalMovingSievePrimes_prime S n r p hp)
      ((mem_actualLeftCanonicalMovingSievePrimes_iff S n r p).mp hp).2.2

/-- The actual fixed-left graph endpoint and complete `6*W` totient
normalization produce the exact universal moving-determinant main constant
`1815/4`; the estimate holds simultaneously for every actual prime `r`. -/
theorem actualLeftMoving_fixedModulus_main_term_eventually_le
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ r : ℕ, r.Prime →
        (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
          (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2 *
            twoRootSelbergDenominator
              ((6 * (∏ p ∈ S, p)) * actualLeftMovingExcludedPrime S r)
              (selbergSquareRootBlockCutoff n ^ 2)) ≤
          (1815 / 4 : ℝ) *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hWreal : (0 : ℝ) < W := by exact_mod_cast hW
  have hphi : 0 < W.totient := Nat.totient_pos.mpr hW
  have hphireal : (0 : ℝ) < W.totient := by exact_mod_cast hphi
  have hM : 2 ∣ 6 * W :=
    dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) W
  have hMtwo : 2 ≤ 6 * W := by omega
  have htotient := actualLeftSupport_totient_six_mul S hsupport
  filter_upwards
    [twoRootSelbergDenominator_fifth_root_eventually_inv_le_explicit
      (6 * W) hM hMtwo] with n hdenominator
  intro r hr
  have hchosen := actualLeftMovingExcludedPrime_prime_coprime_ge_five
    S r (fun p hp => (hsupport p hp).1) hr
  have hreciprocal := hdenominator
    (actualLeftMovingExcludedPrime S r)
      hchosen.1 hchosen.2.1 hchosen.2.2
  change (6 * W).totient = 2 * W.totient at htotient
  rw [htotient] at hreciprocal
  have hnonnegative :
      (0 : ℝ) ≤
        (n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2) := by
    positivity
  change
    (n : ℝ) * (W.totient : ℝ) ^ 2 /
      (4 * (W : ℝ) ^ 2 *
        twoRootSelbergDenominator
          ((6 * W) * actualLeftMovingExcludedPrime S r)
          (selbergSquareRootBlockCutoff n ^ 2)) ≤ _
  calc
    (n : ℝ) * (W.totient : ℝ) ^ 2 /
      (4 * (W : ℝ) ^ 2 *
        twoRootSelbergDenominator
          ((6 * W) * actualLeftMovingExcludedPrime S r)
          (selbergSquareRootBlockCutoff n ^ 2)) =
      ((n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2)) *
        (twoRootSelbergDenominator
          ((6 * W) * actualLeftMovingExcludedPrime S r)
          (selbergSquareRootBlockCutoff n ^ 2))⁻¹ := by
        rw [div_mul_eq_div_mul_one_div, one_div]
    _ ≤ ((n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2)) *
          ((605 / 3 : ℝ) *
            ((((6 * W : ℕ) : ℝ) / ((2 * W.totient : ℕ) : ℝ)) ^ 2) /
              (Real.log (n : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hreciprocal hnonnegative
    _ = (1815 / 4 : ℝ) *
          ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
      push_cast
      field_simp
      ring


end Erdos689
