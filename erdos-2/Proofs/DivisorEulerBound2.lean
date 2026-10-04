module

public import NaturalDivisorModel2
public import EulerMoment2
public import AnalyticTail2


@[expose] public section

/-!
# Euler-product bound for the divisor-pair LCM sum

Bounds the double divisor sum
$$\sum_{m \mid Q} \sum_{e \mid Q} \frac{2^{\omega(\operatorname{lcm}(m, e))}}{\operatorname{lcm}(m, e)}$$
by the product over primes $q \mid Q$ of $1 + 2(3q - 1)/(q - 1)^2$, and hence by
$\prod_{q \mid Q} (q / (q - 1))^6$.
-/

namespace Erdos2.DivisorEuler

open scoped BigOperators

theorem divisor_pair_sum_le_product (Q : ℕ) (hQ : Q ≠ 0) :
    (∑ m ∈ Q.divisors, ∑ e ∈ Q.divisors,
      (2 : ℝ) ^ (Nat.lcm m e).primeFactors.card / (Nat.lcm m e : ℝ)) ≤
      ∏ q ∈ Q.primeFactors, Erdos2.EulerMoment.factorBound (q : ℝ) := by
  classical
  calc
    _ = Erdos2.EulerMoment.doubleVectorSum
        (fun q : Erdos2.DivisorModel.PrimeIndex Q => (q : ℝ))
        (fun q => Q.factorization (q : ℕ)) := by
      rw [Erdos2.DivisorModel.double_divisor_sum_eq_vector Q hQ]
      simp only [Erdos2.EulerMoment.doubleVectorSum, Erdos2.EulerMoment.pairWeight]
      apply Finset.sum_congr
      · ext a
        simp
      · intro a ha
        apply Finset.sum_congr
        · ext b
          simp
        · intro b hb
          apply Finset.prod_congr
          · ext p
            simp
          · intro p hp
            rfl
    _ ≤ ∏ q : Erdos2.DivisorModel.PrimeIndex Q,
        Erdos2.EulerMoment.factorBound (q : ℝ) :=
      Erdos2.EulerMoment.doubleVectorSum_le _ _ (by
        intro q
        exact_mod_cast (Nat.prime_of_mem_primeFactors q.property).two_le)
    _ = ∏ q ∈ Q.primeFactors, Erdos2.EulerMoment.factorBound (q : ℝ) := by
      exact Finset.prod_coe_sort Q.primeFactors
        (fun q : ℕ => Erdos2.EulerMoment.factorBound (q : ℝ))

theorem divisor_pair_sum_le_inverseEuler_pow_six (Q : ℕ) (hQ : Q ≠ 0) :
    (∑ m ∈ Q.divisors, ∑ e ∈ Q.divisors,
      (2 : ℝ) ^ (Nat.lcm m e).primeFactors.card / (Nat.lcm m e : ℝ)) ≤
      (∏ q ∈ Q.primeFactors, (q : ℝ) / ((q : ℝ) - 1)) ^ 6 := by
  calc
    _ ≤ ∏ q ∈ Q.primeFactors, Erdos2.EulerMoment.factorBound (q : ℝ) :=
      divisor_pair_sum_le_product Q hQ
    _ ≤ _ := by
      simpa only [Erdos2.EulerMoment.factorBound] using
        Erdos2.Analytic.deltaHalfProduct_le_inverseEuler_pow_six
          Q.primeFactors Q.primeFactors (Finset.Subset.refl _)
          (fun q hq => Nat.prime_of_mem_primeFactors hq)

end Erdos2.DivisorEuler
