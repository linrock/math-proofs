module

public import ActualLabelFixedModulus433

@[expose] public section


/-!
# Canonical actual sieve primes for all moving fixed-label graph fibers

The actual sieve set is the finite set of primes at most the natural
fifth-root block cutoff and coprime to the fixed even support modulus.
Every manuscript label above a fixed positive linear cutoff eventually
exceeds both this sieve cutoff and the fixed support product.  Thus its
actual coprime fixed-label graph fibers satisfy the uniform `122*n/log² n`
bound with no assumed sieve set, determinant exclusion, or prime pattern.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The genuine canonical fixed-modulus Selberg prime family. -/
def actualCanonicalLabelSievePrimes (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Nat.primesLE (selbergSquareRootBlockCutoff n ^ 2)).filter fun p =>
    Nat.Coprime p (2 * (∏ q ∈ S, q))

/-- Membership in the actual canonical sieve is exactly primality, the
genuine cutoff, and coprimality to the actual even support modulus. -/
theorem mem_actualCanonicalLabelSievePrimes_iff
    (S : Finset ℕ) (n p : ℕ) :
    p ∈ actualCanonicalLabelSievePrimes S n ↔
      p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧
        p.Prime ∧ Nat.Coprime p (2 * (∏ q ∈ S, q)) := by
  simp [actualCanonicalLabelSievePrimes, Nat.mem_primesLE, and_assoc]

/-- Every canonical sieve prime is genuinely prime. -/
theorem actualCanonicalLabelSievePrimes_prime
    (S : Finset ℕ) (n p : ℕ)
    (hp : p ∈ actualCanonicalLabelSievePrimes S n) :
    p.Prime :=
  ((mem_actualCanonicalLabelSievePrimes_iff S n p).mp hp).2.1

/-- The actual sieve product is coprime to the entire fixed excluded
modulus, not merely to the support alone. -/
theorem actualCanonicalLabelSievePrimes_product_coprime
    (S : Finset ℕ) (n : ℕ) :
    Nat.Coprime (∏ p ∈ actualCanonicalLabelSievePrimes S n, p)
      (2 * (∏ p ∈ S, p)) := by
  apply Nat.Coprime.prod_left
  intro p hp
  exact ((mem_actualCanonicalLabelSievePrimes_iff S n p).mp hp).2.2

/-- The excluded even modulus removes the singular sieve prime two. -/
theorem actualCanonicalLabelSievePrimes_gt_two
    (S : Finset ℕ) (n p : ℕ)
    (hp : p ∈ actualCanonicalLabelSievePrimes S n) :
    2 < p := by
  have hpprime := actualCanonicalLabelSievePrimes_prime S n p hp
  have hpcoprime :=
    ((mem_actualCanonicalLabelSievePrimes_iff S n p).mp hp).2.2
  have hpnot : p ≠ 2 := by
    intro heq
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpcoprime)
      (dvd_mul_right 2 (∏ p ∈ S, p))
  have hpbound := hpprime.two_le
  omega

/-- Exact prime-divisor characterization for the actual canonical sieve
product; no unproved existence or selected-prime family is assumed. -/
theorem actualCanonicalLabelSievePrimes_dvd_product_iff
    (S : Finset ℕ) (n p : ℕ) (hp : p.Prime) :
    (p ∣ ∏ q ∈ actualCanonicalLabelSievePrimes S n, q) ↔
      p ≤ selbergSquareRootBlockCutoff n ^ 2 ∧
        Nat.Coprime p (2 * (∏ q ∈ S, q)) := by
  constructor
  · intro hdivisor
    obtain ⟨q, hq, hpq⟩ :=
      (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hdivisor
    have hqprime := actualCanonicalLabelSievePrimes_prime S n q hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
    subst q
    have hmember := (mem_actualCanonicalLabelSievePrimes_iff S n p).mp hq
    exact ⟨hmember.1, hmember.2.2⟩
  · rintro ⟨hcutoff, hcoprime⟩
    apply Finset.dvd_prod_of_mem (fun q : ℕ => q)
    exact (mem_actualCanonicalLabelSievePrimes_iff S n p).mpr
      ⟨hcutoff, hp, hcoprime⟩

/-- The exact natural block-sieve cutoff has square at most the original
endpoint.  This elementary bound suffices to separate it from every fixed
positive linear manuscript label cutoff. -/
theorem actualCanonicalLabelSieveCutoff_sq_le_endpoint (n : ℕ) :
    (selbergSquareRootBlockCutoff n ^ 2) ^ 2 ≤ n := by
  let r := selbergFifthRootCutoff n
  have hcutoff : selbergSquareRootBlockCutoff n ^ 2 ≤ r :=
    selbergSquareRootBlockCutoff_sq_le n
  have hroot : r ^ 5 ≤ n := selbergFifthRootCutoff_pow_five_le n
  by_cases hzero : r = 0
  · have hblock : selbergSquareRootBlockCutoff n ^ 2 = 0 := by omega
    simp [hblock]
  · have hone : 1 ≤ r := by omega
    calc
      (selbergSquareRootBlockCutoff n ^ 2) ^ 2 ≤ r ^ 2 := by gcongr
      _ ≤ r ^ 5 := Nat.pow_le_pow_right hone (by norm_num)
      _ ≤ n := hroot

/-- Every genuine canonical sieve cutoff is eventually smaller than every
fixed positive linear edge-label threshold, with no asymptotic assumption. -/
theorem actualCanonicalLabelSieveCutoff_lt_linear_eventually
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) < τ * n := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 : ℝ) / τ ^ 2)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with n hn hn1
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn1
  have hthreshold : (1 : ℝ) / τ ^ 2 < n := by
    exact lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hscaled : (1 : ℝ) < τ ^ 2 * n := by
    have := (div_lt_iff₀ (sq_pos_of_pos hτ)).mp hthreshold
    nlinarith
  have hsquare : (n : ℝ) < (τ * (n : ℝ)) ^ 2 := by
    have hproduct := mul_lt_mul_of_pos_right hscaled hnreal
    nlinarith
  have hcutoff :
      (((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ)) ^ 2 ≤ n := by
    exact_mod_cast actualCanonicalLabelSieveCutoff_sq_le_endpoint n
  have hnonnegative :
      (0 : ℝ) ≤ ((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) := by
    positivity
  exact (sq_lt_sq₀ hnonnegative
    (mul_nonneg hτ.le (Nat.cast_nonneg n))).mp
      (hcutoff.trans_lt hsquare)

/-- The fixed support product also eventually lies strictly below every
genuine positive linear manuscript label threshold. -/
theorem actualSupportProduct_lt_linear_eventually
    (S : Finset ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (((∏ p ∈ S, p) : ℕ) : ℝ) < τ * n := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((((∏ p ∈ S, p) : ℕ) : ℝ) / τ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hthreshold :
      ((((∏ p ∈ S, p) : ℕ) : ℝ) / τ) < n :=
    lt_of_lt_of_le hN (by exact_mod_cast hn)
  simpa [mul_comm] using (div_lt_iff₀ hτ).mp hthreshold

/-- Fully unconditional fixed-label analytic estimate for the *actual*
edge-bounded manuscript graph fibers over every coprime support-divisor
pair: the universal constant is `122`, and every prime label above the
original positive linear cutoff is handled simultaneously.  There is no
assumed sieve-prime family, support/determinant exclusion, prime-pattern
estimate, or Selberg remainder estimate. -/
theorem actualFixedLabel_canonical_sieve_fiber_sum_eventually_le
    (S : Finset ℕ) (b : ℕ → ℕ) (τ : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ z : ℕ, z.Prime → τ * n < (z : ℝ) →
        (∑ c ∈ actualCanonicalLabelCoefficientPairs S,
          ((edgeBoundedLabelFiberSwitchedPrimeParameters
            S b n z c.1 c.2).card : ℝ)) ≤
          (122 : ℝ) *
            ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  filter_upwards
    [actualFixedLabel_fixedModulus_fiber_sum_eventually_le S b hsupport hb,
      actualCanonicalLabelSieveCutoff_lt_linear_eventually τ hτ,
      actualSupportProduct_lt_linear_eventually S τ hτ] with
      n hbound hcutoff hsupportBound
  intro z hzprime hzlower
  let P := actualCanonicalLabelSievePrimes S n
  have hzsupport : ∀ p ∈ S, ¬ p ∣ z := by
    intro p hp hpz
    have hpprime := (hsupport p hp).1
    have heq : p = z :=
      (Nat.prime_dvd_prime_iff_eq hpprime hzprime).mp hpz
    have hpW : p ∣ ∏ q ∈ S, q :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    have hWpositive : 0 < ∏ q ∈ S, q :=
      Finset.prod_pos fun q hq => (hsupport q hq).1.pos
    have hpbound : p ≤ ∏ q ∈ S, q :=
      Nat.le_of_dvd hWpositive hpW
    have hpboundreal : (p : ℝ) ≤ ((∏ q ∈ S, q) : ℕ) := by
      exact_mod_cast hpbound
    have hzreal : (z : ℝ) = p := by rw [heq]
    linarith
  have havoidz : ∀ p ∈ P, ¬ p ∣ z := by
    intro p hp hpz
    have hpprime := actualCanonicalLabelSievePrimes_prime S n p hp
    have heq : p = z :=
      (Nat.prime_dvd_prime_iff_eq hpprime hzprime).mp hpz
    have hpbound :=
      ((mem_actualCanonicalLabelSievePrimes_iff S n p).mp hp).1
    have hpboundreal :
        (p : ℝ) ≤ ((selbergSquareRootBlockCutoff n ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hpbound
    have hzreal : (z : ℝ) = p := by rw [heq]
    linarith
  exact hbound z P hzsupport
    (fun p hp => actualCanonicalLabelSievePrimes_prime S n p hp)
    (fun p hp => actualCanonicalLabelSievePrimes_gt_two S n p hp)
    havoidz (actualCanonicalLabelSievePrimes_product_coprime S n)
    (fun p hp => actualCanonicalLabelSievePrimes_dvd_product_iff S n p hp)


end Erdos689
