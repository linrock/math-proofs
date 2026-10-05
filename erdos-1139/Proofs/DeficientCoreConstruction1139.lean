module

public import Reuse689Sparse1139

@[expose] public section


/-!
# Genuine fixed-parameter squared-prime core for Erdős problem #1139

The original proposed argument starts with the actual conductor

  `∏_{p ≤ y / z} p · ∏_{p ≤ z} p`,

assigning zero residue to every selected prime and paying the second exponent
for every selected prime at most `z`.  This module establishes precise
structural facts about the *literal* deficiency finset of that mixed core.
No Green--Tao prime-pattern estimate, matching theorem, or complete #1139
solution is assumed.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Genuine initial broad-prime support, including exactly all primes up to
the integer cutoff `y / z`. -/
def fixedParameterCorePrimes (y z : ℕ) : Finset ℕ :=
  Nat.primesLE (y / z)

/-- Genuine square-exponent support: small primes up to `z` that actually
belong to the broad support.  The intersection makes all edge cases valid. -/
def fixedParameterCoreSquared (y z : ℕ) : Finset ℕ :=
  Nat.primesLE z ∩ fixedParameterCorePrimes y z

/-- Every actual initial broad modulus is prime. -/
theorem fixedParameterCorePrimes_prime
    (y z p : ℕ) (hp : p ∈ fixedParameterCorePrimes y z) : p.Prime :=
  Nat.prime_of_mem_primesLE hp

/-- Every genuine selected square prime is also selected broadly. -/
theorem fixedParameterCoreSquared_subset
    (y z : ℕ) :
    fixedParameterCoreSquared y z ⊆ fixedParameterCorePrimes y z := by
  intro p hp
  exact (Finset.mem_inter.mp hp).2

/-- Every genuine mixed conductor factors into the product of all selected
primes times one additional factor for every selected square prime. -/
theorem selectedPrimePower_product_eq_broad_mul_squared
    (P squared : Finset ℕ) (support : squared ⊆ P) :
    (∏ p ∈ P, selectedPrimePower squared p) =
      (∏ p ∈ P, p) * ∏ p ∈ squared, p := by
  classical
  calc
    (∏ p ∈ P, selectedPrimePower squared p) =
        ∏ p ∈ P, p * (if p ∈ squared then p else 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases selected : p ∈ squared
      · simp [selectedPrimePower, selectedPrimeExponent, selected, pow_two]
      · simp [selectedPrimePower, selectedPrimeExponent, selected]
    _ = (∏ p ∈ P, p) * ∏ p ∈ P ∩ squared, p := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem]
    _ = (∏ p ∈ P, p) * ∏ p ∈ squared, p := by
      rw [Finset.inter_eq_right.mpr support]

/-- Once the small-prime threshold lies below the broad cutoff, the exact
initial conductor is precisely `primorial (y / z) * primorial z`. -/
theorem fixedParameterCore_actual_conductor
    {y z : ℕ} (threshold : z ≤ y / z) :
    (∏ p ∈ fixedParameterCorePrimes y z,
      selectedPrimePower (fixedParameterCoreSquared y z) p) =
        primorial (y / z) * primorial z := by
  have squares : fixedParameterCoreSquared y z = Nat.primesLE z := by
    unfold fixedParameterCoreSquared fixedParameterCorePrimes
    exact Finset.inter_eq_left.mpr (Nat.primesLE_mono threshold)
  rw [selectedPrimePower_product_eq_broad_mul_squared
    _ _ (fixedParameterCoreSquared_subset y z), squares]
  simp [fixedParameterCorePrimes, primorial_eq_prod_primesLE]

/-- Exact old broad hits are the distinct prime divisors below the actual
core cutoff; positivity rules out the misleading prime factors of zero. -/
theorem fixedParameterCore_zero_broad_hits_eq_small_prime_factors
    {y z h : ℕ} (positive : 0 < h) :
    ((fixedParameterCorePrimes y z).filter
      fun p => (0 : ℕ) ≡ h [MOD p]) =
      h.primeFactors.filter (fun p => p ≤ y / z) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hcore, hhit⟩ := Finset.mem_filter.mp hp
    have hprime := fixedParameterCorePrimes_prime y z p hcore
    have hdivides := Nat.modEq_zero_iff_dvd.mp hhit.symm
    have hfactor : p ∈ h.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hprime, hdivides, positive.ne'⟩
    exact Finset.mem_filter.mpr
      ⟨hfactor, Nat.le_of_mem_primesLE hcore⟩
  · intro hp
    obtain ⟨hfactor, hbound⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hfactor
    have hdivides := Nat.dvd_of_mem_primeFactors hfactor
    apply Finset.mem_filter.mpr
    refine ⟨(Nat.mem_primesLE.mpr ⟨hbound, hprime⟩), ?_⟩
    exact (Nat.modEq_zero_iff_dvd.mpr hdivides).symm

/-- Every genuinely deficient initial target has at most one distinct prime
factor at or below the broad cutoff. -/
theorem deficient_fixedParameterCore_small_prime_factors_card_le_one
    {y z h : ℕ}
    (deficient :
      h ∈ deficientTargets y (fixedParameterCorePrimes y z)
        (fixedParameterCoreSquared y z) (fun _ => 0)) :
    (h.primeFactors.filter (fun p => p ≤ y / z)).card ≤ 1 := by
  obtain ⟨hinterval, hdeficiency⟩ := Finset.mem_filter.mp deficient
  have hpositive : 0 < h := by
    have := (Finset.mem_Icc.mp hinterval).1
    omega
  rw [fixedParameterCore_zero_broad_hits_eq_small_prime_factors hpositive]
    at hdeficiency
  omega

/-- A deficient initial target cannot be divisible by the genuine square of
any selected small prime: that prime would supply both its broad and its
nested square hit. -/
theorem deficient_fixedParameterCore_not_dvd_selected_square
    {y z h p : ℕ}
    (deficient :
      h ∈ deficientTargets y (fixedParameterCorePrimes y z)
        (fixedParameterCoreSquared y z) (fun _ => 0))
    (selected : p ∈ fixedParameterCoreSquared y z) :
    ¬ p ^ 2 ∣ h := by
  intro square_divides
  obtain ⟨_hinterval, hdeficiency⟩ := Finset.mem_filter.mp deficient
  change
    ((fixedParameterCorePrimes y z).filter
      fun q => (0 : ℕ) ≡ h [MOD q]).card +
      ((fixedParameterCoreSquared y z).filter
        fun q => (0 : ℕ) ≡ h [MOD q ^ 2]).card < 2 at hdeficiency
  have broad_divides : p ∣ h :=
    dvd_trans (by simp [pow_two]) square_divides
  have broad_hit :
      p ∈ (fixedParameterCorePrimes y z).filter
        fun q => (0 : ℕ) ≡ h [MOD q] := by
    apply Finset.mem_filter.mpr
    refine ⟨fixedParameterCoreSquared_subset y z selected, ?_⟩
    exact (Nat.modEq_zero_iff_dvd.mpr broad_divides).symm
  have square_hit :
      p ∈ (fixedParameterCoreSquared y z).filter
        fun q => (0 : ℕ) ≡ h [MOD q ^ 2] := by
    apply Finset.mem_filter.mpr
    exact ⟨selected, (Nat.modEq_zero_iff_dvd.mpr square_divides).symm⟩
  have broad_positive := Finset.card_pos.mpr ⟨p, broad_hit⟩
  have square_positive := Finset.card_pos.mpr ⟨p, square_hit⟩
  omega

/-- Any divisor above the literal broad cutoff leaves a cofactor strictly
below the fixed parameter `z`; this uses the actual closed endpoint and
integer division, without an asymptotic approximation. -/
theorem large_core_divisor_cofactor_lt_parameter
    {y z h q : ℕ} (parameter_positive : 0 < z)
    (endpoint : h ≤ y) (large : y / z < q) (divides : q ∣ h) :
    h / q < z := by
  have product_bound : q * (h / q) ≤ y := by
    rw [Nat.mul_div_cancel' divides]
    exact endpoint
  by_contra not_small
  have large_cofactor : z ≤ h / q := by omega
  have interval_too_short : y < q * z :=
    (Nat.div_lt_iff_lt_mul parameter_positive).mp large
  have product_too_large : q * z ≤ q * (h / q) :=
    Nat.mul_le_mul_left q large_cofactor
  omega

/-- Two distinct prime divisors below the genuine broad cutoff cannot occur
at an initially deficient target. -/
theorem deficient_fixedParameterCore_small_prime_divisors_equal
    {y z h p q : ℕ}
    (deficient :
      h ∈ deficientTargets y (fixedParameterCorePrimes y z)
        (fixedParameterCoreSquared y z) (fun _ => 0))
    (pprime : p.Prime) (qprime : q.Prime)
    (pbound : p ≤ y / z) (qbound : q ≤ y / z)
    (pdivides : p ∣ h) (qdivides : q ∣ h) :
    p = q := by
  have hpositive : 0 < h := by
    have hinterval := (Finset.mem_filter.mp deficient).1
    have hnonzero := (Finset.mem_Icc.mp hinterval).1
    omega
  have hp : p ∈ h.primeFactors.filter (fun r => r ≤ y / z) :=
    Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨pprime, pdivides, hpositive.ne'⟩,
        pbound⟩
  have hq : q ∈ h.primeFactors.filter (fun r => r ≤ y / z) :=
    Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨qprime, qdivides, hpositive.ne'⟩,
        qbound⟩
  exact Finset.card_le_one.mp
    (deficient_fixedParameterCore_small_prime_factors_card_le_one deficient)
      p hp q hq

/-- EXACT classification of the main large-prime portion of the manuscript's
initial deficiency.  If a genuinely deficient target has a prime divisor
above `y / z`, then the target is either that prime itself or that prime
times one genuinely smaller prime `p < z`.  Prime-square and composite
cofactors are excluded using the paid nested-square classes. -/
theorem deficient_fixedParameterCore_large_prime_classification
    {y z h q : ℕ}
    (parameter_positive : 0 < z)
    (square_threshold : z ≤ y / z)
    (deficient :
      h ∈ deficientTargets y (fixedParameterCorePrimes y z)
        (fixedParameterCoreSquared y z) (fun _ => 0))
    (_qprime : q.Prime) (qlarge : y / z < q) (qdivides : q ∣ h) :
    h = q ∨ ∃ p : ℕ, p.Prime ∧ p < z ∧ h = p * q := by
  have hinterval := (Finset.mem_filter.mp deficient).1
  have hpositive : 0 < h := by
    have := (Finset.mem_Icc.mp hinterval).1
    omega
  have hendpoint := (Finset.mem_Icc.mp hinterval).2
  let r : ℕ := h / q
  have rsmall : r < z :=
    large_core_divisor_cofactor_lt_parameter
      parameter_positive hendpoint qlarge qdivides
  have factorization : q * r = h := Nat.mul_div_cancel' qdivides
  have rpositive : 0 < r := by
    by_contra hnot
    have hzero : r = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero_target : h = 0 := by
      simpa [hzero] using factorization.symm
    exact hpositive.ne' hzero_target
  by_cases rone : r = 1
  · left
    simpa [rone] using factorization.symm
  · have rtwo : 2 ≤ r := by omega
    have rprime : r.Prime := by
      by_contra not_prime
      obtain ⟨left, right, left_lt, right_lt, factors⟩ :=
        (Nat.not_prime_iff_exists_mul_eq rtwo).mp not_prime
      have left_large : 1 < left := by
        by_contra hnot
        have hle : left ≤ 1 := by omega
        interval_cases left <;> simp_all
      have right_large : 1 < right := by
        by_contra hnot
        have hle : right ≤ 1 := by omega
        interval_cases right <;> simp_all
      obtain ⟨p, pprime, pdivleft⟩ :=
        Nat.exists_prime_and_dvd (by omega : left ≠ 1)
      obtain ⟨s, sprime, sdivright⟩ :=
        Nat.exists_prime_and_dvd (by omega : right ≠ 1)
      have psmall : p < z := by
        have ple : p ≤ left := Nat.le_of_dvd (by omega) pdivleft
        omega
      have ssmall : s < z := by
        have sle : s ≤ right := Nat.le_of_dvd (by omega) sdivright
        omega
      have pbound : p ≤ y / z := (Nat.le_of_lt psmall).trans square_threshold
      have sbound : s ≤ y / z := (Nat.le_of_lt ssmall).trans square_threshold
      have pair_divides_r : p * s ∣ r := by
        rw [← factors]
        exact mul_dvd_mul pdivleft sdivright
      have rdivides : r ∣ h := by
        refine ⟨q, ?_⟩
        simpa [Nat.mul_comm] using factorization.symm
      have pdivides : p ∣ h :=
        dvd_trans (dvd_trans (dvd_mul_right p s) pair_divides_r) rdivides
      have sdivides : s ∣ h :=
        dvd_trans (dvd_trans (dvd_mul_left s p) pair_divides_r) rdivides
      have equal : p = s :=
        deficient_fixedParameterCore_small_prime_divisors_equal
          deficient pprime sprime pbound sbound pdivides sdivides
      subst s
      have selected : p ∈ fixedParameterCoreSquared y z := by
        apply Finset.mem_inter.mpr
        refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_lt psmall), pprime⟩, ?_⟩
        exact Nat.mem_primesLE.mpr ⟨pbound, pprime⟩
      apply deficient_fixedParameterCore_not_dvd_selected_square
        deficient selected
      rw [pow_two]
      exact dvd_trans pair_divides_r rdivides
    right
    refine ⟨r, rprime, rsmall, ?_⟩
    simpa [Nat.mul_comm] using factorization.symm


end Erdos1139
