module

public import Mathlib

@[expose] public section


/-!
# A genuine dimension-two coprime divisor-sum lower bound

The optimized Selberg sieve still requires a dimension-two denominator lower
bound.  This file proves its square-harmonic combinatorial core for every fixed
excluded modulus: every ordered pair of admissible factors injects into the
appropriate divisor antidiagonal of its product.  No squarefreeness,
independence, or fixed-modulus asymptotic is assumed.
-/

open Finset

namespace Erdos689

/-- Distinct product values have disjoint divisor antidiagonals. -/
theorem divisor_antidiagonals_pairwise_disjoint (U : Finset ℕ) :
    (U : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
  intro m hm n hn hmn
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hy' := (Nat.mem_divisorsAntidiagonal.mp hy).1
  exact hmn (hx'.symm.trans hy')

/-- An integer has exactly as many ordered factor pairs as positive divisors. -/
theorem card_divisors_antidiagonal_eq (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- Two bounded coprime-to-`M` factors produce an admissible bounded product. -/
theorem coprime_product_parameters_subset_antidiagonals (L M : ℕ) :
    (((Finset.Icc 1 L).filter fun a => Nat.Coprime a M).product
      ((Finset.Icc 1 L).filter fun a => Nat.Coprime a M)) ⊆
        (((Finset.Icc 1 (L ^ 2)).filter fun m => Nat.Coprime m M).biUnion
          Nat.divisorsAntidiagonal) := by
  intro x hx
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
  obtain ⟨haI, haM⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbI, hbM⟩ := Finset.mem_filter.mp hb
  obtain ⟨ha1, haL⟩ := Finset.mem_Icc.mp haI
  obtain ⟨hb1, hbL⟩ := Finset.mem_Icc.mp hbI
  have habpos : 0 < x.1 * x.2 := Nat.mul_pos (by omega) (by omega)
  apply Finset.mem_biUnion.mpr
  refine ⟨x.1 * x.2, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, haM.mul_left hbM⟩
    simpa [pow_two] using Nat.mul_le_mul haL hbL
  · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by omega⟩

/--
The square of the harmonic sum coprime to `M` is bounded by the genuine
coprime divisor sum through the squared cutoff.  This is the dimension-two
lower-bound mechanism missing from a dimension-one harmonic sieve.
-/
theorem coprime_harmonic_sq_le_divisor_sum (L M : ℕ) :
    (∑ a ∈ (Finset.Icc 1 L).filter (fun a => Nat.Coprime a M),
      (a : ℝ)⁻¹) ^ 2 ≤
      ∑ m ∈ (Finset.Icc 1 (L ^ 2)).filter (fun m => Nat.Coprime m M),
        (m.divisors.card : ℝ) / m := by
  classical
  let T := (Finset.Icc 1 L).filter fun a => Nat.Coprime a M
  let U := (Finset.Icc 1 (L ^ 2)).filter fun m => Nat.Coprime m M
  change (∑ a ∈ T, (a : ℝ)⁻¹) ^ 2 ≤
    ∑ m ∈ U, (m.divisors.card : ℝ) / m
  calc
    (∑ a ∈ T, (a : ℝ)⁻¹) ^ 2 =
        ∑ x ∈ T.product T, ((x.1 * x.2 : ℕ) : ℝ)⁻¹ := by
          rw [pow_two, Finset.sum_mul_sum]
          rw [← Finset.sum_product' T T
            (fun a b : ℕ => (a : ℝ)⁻¹ * (b : ℝ)⁻¹)]
          apply Finset.sum_congr rfl
          intro x hx
          simp [Nat.cast_mul, mul_comm]
    _ ≤ ∑ x ∈ U.biUnion Nat.divisorsAntidiagonal,
        ((x.1 * x.2 : ℕ) : ℝ)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact coprime_product_parameters_subset_antidiagonals L M
          · intro x hx hnot
            positivity
    _ = ∑ m ∈ U, (m.divisors.card : ℝ) / m := by
          rw [Finset.sum_biUnion (divisor_antidiagonals_pairwise_disjoint U)]
          apply Finset.sum_congr rfl
          intro m hm
          calc
            (∑ x ∈ m.divisorsAntidiagonal,
              ((x.1 * x.2 : ℕ) : ℝ)⁻¹) =
                ∑ _x ∈ m.divisorsAntidiagonal, (m : ℝ)⁻¹ := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
            _ = (m.divisors.card : ℝ) / m := by
                  simp [card_divisors_antidiagonal_eq, div_eq_mul_inv]

/-- With no excluded modulus, the genuine divisor denominator grows quadratically in log. -/
theorem log_sq_le_divisor_sum (L : ℕ) :
    (Real.log (L + 1 : ℝ)) ^ 2 ≤
      ∑ m ∈ Finset.Icc 1 (L ^ 2), (m.divisors.card : ℝ) / m := by
  have hlog : Real.log (L + 1 : ℝ) ≤
      ∑ a ∈ Finset.Icc 1 L, (a : ℝ)⁻¹ := by
    calc
      Real.log (L + 1 : ℝ) ≤ (harmonic L : ℝ) := by
        simpa using log_add_one_le_harmonic L
      _ = ∑ a ∈ Finset.Icc 1 L, (a : ℝ)⁻¹ := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
  have hnonneg : 0 ≤ Real.log (L + 1 : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.le_add_left 1 L
  have hsquare := pow_le_pow_left₀ hnonneg hlog 2
  have hdivisor := coprime_harmonic_sq_le_divisor_sum L 1
  have hdivisor' :
      (∑ a ∈ Finset.Icc 1 L, (a : ℝ)⁻¹) ^ 2 ≤
        ∑ m ∈ Finset.Icc 1 (L ^ 2), (m.divisors.card : ℝ) / m := by
    simpa [Nat.Coprime] using hdivisor
  exact hsquare.trans hdivisor'

#print axioms Erdos689.divisor_antidiagonals_pairwise_disjoint
#print axioms Erdos689.card_divisors_antidiagonal_eq
#print axioms Erdos689.coprime_product_parameters_subset_antidiagonals
#print axioms Erdos689.coprime_harmonic_sq_le_divisor_sum
#print axioms Erdos689.log_sq_le_divisor_sum

end Erdos689
