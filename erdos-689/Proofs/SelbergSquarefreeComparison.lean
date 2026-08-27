import Mathlib
import SelbergSquarefree
import SelbergDenominator
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergBounds

/-!
# Comparing the genuine two-root squarefree denominator to the divisor kernel

For every excluded even modulus, the completely multiplicative majorant
`2 ^ Ω(n) / n` dominates `τ(n) / n`.  Its prime-power fibers are controlled by
the exact Selberg local factor `2 / (p - 2)`.  The imported finite
factorization identities are from the separately pinned, Apache-2.0
`PrimeNumberTheoremAnd` sieve development.
-/

open Finset
open scoped ArithmeticFunction.Omega

namespace Erdos689

/-- The completely multiplicative positive extension of the two-root density. -/
noncomputable def twoRootDivisorMajorant : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
    (2 : ℝ) ^ ArithmeticFunction.cardFactors n / (n : ℝ), by simp⟩

/-- Off zero, the majorant is exactly `2 ^ Ω(n) / n`. -/
theorem twoRootDivisorMajorant_apply {n : ℕ} (hn : n ≠ 0) :
    twoRootDivisorMajorant n =
      (2 : ℝ) ^ ArithmeticFunction.cardFactors n / (n : ℝ) := by
  simp [twoRootDivisorMajorant, hn]

/-- The divisor majorant is nonnegative even at the arithmetic-function zero. -/
theorem twoRootDivisorMajorant_nonneg (n : ℕ) :
    0 ≤ twoRootDivisorMajorant n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [twoRootDivisorMajorant_apply hn]
    positivity

/-- Exact complete multiplicativity, including inputs equal to zero. -/
theorem twoRootDivisorMajorant_completelyMultiplicative :
    Sieve.CompletelyMultiplicative twoRootDivisorMajorant := by
  constructor
  · simp [twoRootDivisorMajorant]
  · intro a b
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp [twoRootDivisorMajorant, ha, hb, Nat.mul_ne_zero ha hb,
      ArithmeticFunction.cardFactors_mul ha hb, pow_add, Nat.cast_mul]
    ring

/-- The local value at every prime is exactly `2 / p`. -/
theorem twoRootDivisorMajorant_prime {p : ℕ} (hp : p.Prime) :
    twoRootDivisorMajorant p = (2 : ℝ) / p := by
  simp [twoRootDivisorMajorant, hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]

/-- The elementary prime-exponent divisor count is at most its binary bound. -/
theorem divisor_exponent_succ_le_two_pow (k : ℕ) :
    k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      omega

/-- The genuine divisor multiplicity never exceeds `2 ^ Ω(n)`. -/
theorem card_divisors_le_two_pow_cardFactors {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤ 2 ^ ArithmeticFunction.cardFactors n := by
  rw [Nat.card_divisors hn, ArithmeticFunction.cardFactors_eq_sum_factorization]
  change (∏ p ∈ n.primeFactors, (n.factorization p + 1)) ≤
    2 ^ (∑ p ∈ n.primeFactors, n.factorization p)
  rw [← Finset.prod_pow_eq_pow_sum]
  gcongr with p hp
  exact divisor_exponent_succ_le_two_pow (n.factorization p)

/-- The exact divisor-sum kernel is termwise dominated by the completely
multiplicative two-root majorant. -/
theorem divisor_weight_le_twoRootDivisorMajorant {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card : ℝ) / n ≤ twoRootDivisorMajorant n := by
  rw [twoRootDivisorMajorant_apply hn]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast card_divisors_le_two_pow_cardFactors hn
  · exact_mod_cast Nat.zero_le n

/-- Every prime admitted by an even excluded modulus has local density less
than one. -/
theorem twoRootDivisorMajorant_prime_lt_one {M p : ℕ}
    (hM : 2 ∣ M) (hp : p.Prime) (hpM : Nat.Coprime p M) :
    twoRootDivisorMajorant p < 1 := by
  rw [twoRootDivisorMajorant_prime hp]
  have hp2 : Nat.Coprime p 2 := Nat.Coprime.coprime_dvd_right hM hpM
  have hpne : p ≠ 2 := by
    intro heq
    subst p
    norm_num at hp2
  have hpgreater : 2 < p := by
    have hple := hp.two_le
    omega
  apply (div_lt_one (by exact_mod_cast hp.pos)).mpr
  exact_mod_cast hpgreater

/-- On an admitted squarefree integer, the completely multiplicative density
and geometric prime-power factors reproduce the *exact* two-root Selberg
weight. -/
theorem twoRootSelbergWeight_eq_geometric_majorant {M d : ℕ}
    (hM : 2 ∣ M) (hdsquare : Squarefree d) (hdM : Nat.Coprime d M) :
    twoRootSelbergWeight d =
      twoRootDivisorMajorant d *
        ∏ p ∈ d.primeFactors,
          1 / (1 - twoRootDivisorMajorant p) := by
  have hmajorant := twoRootDivisorMajorant_completelyMultiplicative
  have hdproduct : twoRootDivisorMajorant d =
      ∏ p ∈ d.primeFactors, twoRootDivisorMajorant p := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdsquare]
    exact hmajorant.isMultiplicative.map_prod_of_subset_primeFactors
      _ _ (Finset.Subset.refl _)
  rw [hdproduct, ← Finset.prod_mul_distrib]
  unfold twoRootSelbergWeight
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hpM : Nat.Coprime p M := Nat.Coprime.coprime_dvd_left hpd hdM
  have hplt := twoRootDivisorMajorant_prime_lt_one hM hpprime hpM
  rw [twoRootDivisorMajorant_prime hpprime] at hplt ⊢
  have hpzero : (p : ℝ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
  have hpdiff : (p : ℝ) - 2 ≠ 0 := by
    have hppos : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    intro heq
    have hptwo : (p : ℝ) = 2 := by linarith
    rw [hptwo] at hplt
    norm_num at hplt
  field_simp [hpzero, hpdiff]

/-- Every entire finite prime-power fiber of a squarefree radical is bounded by
its single exact two-root squarefree weight. -/
theorem twoRootSelbergWeight_ge_prime_power_fiber {M d : ℕ} (z : ℕ)
    (hM : 2 ∣ M) (hz : z ≠ 0)
    (hdsquare : Squarefree d) (hdM : Nat.Coprime d M) :
    (∑ m ∈ (d ^ z).divisors.filter (fun m => d ∣ m),
      twoRootDivisorMajorant m) ≤ twoRootSelbergWeight d := by
  rw [← Sieve.prod_factors_sum_pow_compMult z hz
    twoRootDivisorMajorant twoRootDivisorMajorant_completelyMultiplicative
    d hdsquare]
  rw [twoRootSelbergWeight_eq_geometric_majorant hM hdsquare hdM]
  apply Sieve.prod_factors_one_div_compMult_ge z twoRootDivisorMajorant
    twoRootDivisorMajorant_completelyMultiplicative
    twoRootDivisorMajorant_nonneg d hdsquare
  intro p hp hpd
  exact twoRootDivisorMajorant_prime_lt_one hM hp
    (Nat.Coprime.coprime_dvd_left hpd hdM)

/-- Distinct squarefree radicals have disjoint complete prime-power fibers. -/
theorem squarefree_radical_power_fibers_pairwise_disjoint
    (T : Finset ℕ) (z : ℕ) (hz : z ≠ 0)
    (hT : ∀ d ∈ T, Squarefree d) :
    (T : Set ℕ).PairwiseDisjoint
      (fun d => (d ^ z).divisors.filter (fun m => d ∣ m)) := by
  intro d hd e he hde
  apply Finset.disjoint_left.mpr
  intro m hmd hme
  obtain ⟨hmddiv, hdm⟩ := Finset.mem_filter.mp hmd
  obtain ⟨hmediv, hem⟩ := Finset.mem_filter.mp hme
  have hmpowd : m ∣ d ^ z := (Nat.mem_divisors.mp hmddiv).1
  have hmpowe : m ∣ e ^ z := (Nat.mem_divisors.mp hmediv).1
  have hde' : d ∣ e :=
    (Squarefree.dvd_pow_iff_dvd (hT d hd) hz).mp (hdm.trans hmpowe)
  have hed' : e ∣ d :=
    (Squarefree.dvd_pow_iff_dvd (hT e he) hz).mp (hem.trans hmpowd)
  exact hde (Nat.dvd_antisymm hde' hed')

/-- Every positive coprime integer below the cutoff belongs to the fiber of
its genuine squarefree radical, and that radical lies below the same cutoff. -/
theorem coprime_parameters_subset_squarefree_radical_fibers
    (M z : ℕ) :
    ((Finset.Icc 1 z).filter (fun m => Nat.Coprime m M)) ⊆
      (((Finset.Icc 1 z).filter
        (fun d => Squarefree d ∧ Nat.Coprime d M)).biUnion
          (fun d => (d ^ z).divisors.filter (fun m => d ∣ m))) := by
  intro m hm
  obtain ⟨hminterval, hmM⟩ := Finset.mem_filter.mp hm
  obtain ⟨hmpos, hmz⟩ := Finset.mem_Icc.mp hminterval
  have hmne : m ≠ 0 := by omega
  let d : ℕ := ∏ p ∈ m.primeFactors, p
  have hdpos : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  have hdsquare : Squarefree d := by
    dsimp [d]
    exact Sieve.prodDistinctPrimes_squarefree m.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hdm : d ∣ m := by
    dsimp [d]
    exact Nat.prod_primeFactors_dvd m
  have hdz : d ≤ z := (Nat.le_of_dvd hmpos hdm).trans hmz
  have hdM : Nat.Coprime d M := Nat.Coprime.coprime_dvd_left hdm hmM
  have hmpowself : m ∣ d ^ m := by
    simpa [d] using Nat.dvd_prod_primeFactors_pow_self hmne
  have hmpowz : m ∣ d ^ z := hmpowself.trans (pow_dvd_pow d hmz)
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hdpos, hdz⟩, hdsquare, hdM⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
    ⟨hmpowz, pow_ne_zero _ (Nat.ne_of_gt hdpos)⟩, hdm⟩

/-- The actual squarefree two-root Selberg denominator dominates the entire
coprime divisor-sum kernel at the *same* cutoff, not merely an Euler product
with an enlarged squarefree support. -/
theorem divisor_sum_le_twoRootSelbergDenominator (M z : ℕ)
    (hM : 2 ∣ M) :
    (∑ m ∈ (Finset.Icc 1 z).filter (fun m => Nat.Coprime m M),
      (m.divisors.card : ℝ) / m) ≤ twoRootSelbergDenominator M z := by
  classical
  by_cases hz : z = 0
  · simp [hz, twoRootSelbergDenominator]
  let T := (Finset.Icc 1 z).filter
    (fun d => Squarefree d ∧ Nat.Coprime d M)
  have hTsquare : ∀ d ∈ T, Squarefree d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2.1
  have hdisjoint := squarefree_radical_power_fibers_pairwise_disjoint
    T z hz hTsquare
  calc
    (∑ m ∈ (Finset.Icc 1 z).filter (fun m => Nat.Coprime m M),
      (m.divisors.card : ℝ) / m) ≤
        ∑ m ∈ (Finset.Icc 1 z).filter (fun m => Nat.Coprime m M),
          twoRootDivisorMajorant m := by
            apply Finset.sum_le_sum
            intro m hm
            have hmpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
            exact divisor_weight_le_twoRootDivisorMajorant (by omega)
    _ ≤ ∑ d ∈ T, ∑ m ∈ (d ^ z).divisors.filter (fun m => d ∣ m),
          twoRootDivisorMajorant m := by
            rw [← Finset.sum_biUnion hdisjoint]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact coprime_parameters_subset_squarefree_radical_fibers M z
            · intro m hm hnot
              exact twoRootDivisorMajorant_nonneg m
    _ ≤ ∑ d ∈ T, twoRootSelbergWeight d := by
            apply Finset.sum_le_sum
            intro d hd
            obtain ⟨hdinterval, hdsquare, hdM⟩ := Finset.mem_filter.mp hd
            exact twoRootSelbergWeight_ge_prime_power_fiber z hM hz
              hdsquare hdM
    _ = twoRootSelbergDenominator M z := rfl

/-- Full coprime dimension-two logarithmic mechanism for the *actual*
squarefree two-root Selberg denominator, for every even excluded modulus. -/
theorem coprime_harmonic_sq_le_twoRootSelbergDenominator (L M : ℕ)
    (hM : 2 ∣ M) :
    (∑ a ∈ (Finset.Icc 1 L).filter (fun a => Nat.Coprime a M),
      (a : ℝ)⁻¹) ^ 2 ≤ twoRootSelbergDenominator M (L ^ 2) := by
  exact (coprime_harmonic_sq_le_divisor_sum L M).trans
    (divisor_sum_le_twoRootSelbergDenominator M (L ^ 2) hM)

#print axioms Erdos689.twoRootDivisorMajorant_apply
#print axioms Erdos689.twoRootDivisorMajorant_nonneg
#print axioms Erdos689.twoRootDivisorMajorant_completelyMultiplicative
#print axioms Erdos689.twoRootDivisorMajorant_prime
#print axioms Erdos689.divisor_exponent_succ_le_two_pow
#print axioms Erdos689.card_divisors_le_two_pow_cardFactors
#print axioms Erdos689.divisor_weight_le_twoRootDivisorMajorant
#print axioms Erdos689.twoRootDivisorMajorant_prime_lt_one
#print axioms Erdos689.twoRootSelbergWeight_eq_geometric_majorant
#print axioms Erdos689.twoRootSelbergWeight_ge_prime_power_fiber
#print axioms Erdos689.squarefree_radical_power_fibers_pairwise_disjoint
#print axioms Erdos689.coprime_parameters_subset_squarefree_radical_fibers
#print axioms Erdos689.divisor_sum_le_twoRootSelbergDenominator
#print axioms Erdos689.coprime_harmonic_sq_le_twoRootSelbergDenominator

end Erdos689
