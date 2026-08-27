import Mathlib
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.Selberg

/-!
# The actual finite Selberg inequality for two prime forms

Mathlib supplies the abstract upper-bound-sieve and diagonalization machinery.
The separately pinned, Apache-2.0 `PrimeNumberTheoremAnd` source already proves
the optimized finite Selberg inequality, including its explicit `3 ^ ω(d)`
remainder.  This file transports that theorem to genuine parameter fibers of
the product of two functions, without assuming that the product is injective.
In particular, negative affine slopes can be translated to a positive parameter
interval and represented by natural subtraction; the general theorem does not
restrict either form to positive slope.

The dimension-two denominator lower bound, affine residue counts, and the
eventual prime-pair degree estimate are deliberately not claimed here.
-/

open Finset
open scoped ArithmeticFunction.omega

namespace Erdos689

/-- The exact product sifted when both affine prime forms are tested. -/
def twoAffineProduct (u₁ v₁ u₂ v₂ t : ℕ) : ℕ :=
  (u₁ * t + v₁) * (u₂ * t + v₂)

/-- Grouping by product fibers preserves every parameter, including collisions. -/
theorem siftedSum_eq_parameter_card
    (s : SelbergSieve) (I : Finset ℕ) (F : ℕ → ℕ)
    (hsupport : s.support = I.image F)
    (hweights : ∀ x ∈ s.support,
      s.weights x = ((I.filter fun t => F t = x).card : ℝ)) :
    BoundingSieve.siftedSum (s := s.toBoundingSieve) =
      ((I.filter fun t => Nat.Coprime s.prodPrimes (F t)).card : ℝ) := by
  classical
  unfold BoundingSieve.siftedSum
  rw [hsupport]
  calc
    (∑ x ∈ I.image F,
      if Nat.Coprime s.prodPrimes x then s.weights x else 0) =
        ∑ x ∈ (I.image F).filter (Nat.Coprime s.prodPrimes),
          ((I.filter fun t => F t = x).card : ℝ) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro x hx
            split_ifs with h
            · exact hweights x (hsupport.symm ▸ hx)
            · rfl
    _ = ((∑ x ∈ (I.image F).filter (Nat.Coprime s.prodPrimes),
          (I.filter fun t => F t = x).card : ℕ) : ℝ) := by
            norm_cast
    _ = ((I.filter fun t => Nat.Coprime s.prodPrimes (F t)).card : ℝ) := by
            rw [Finset.sum_card_fiberwise_eq_card_filter]
            apply congrArg (fun T : Finset ℕ => (T.card : ℝ))
            ext t
            simp only [Finset.mem_filter]
            constructor
            · intro h
              exact ⟨h.1, h.2.2⟩
            · intro h
              exact ⟨h.1, ⟨Finset.mem_image_of_mem F h.1, h.2⟩⟩

/-- Optimized Selberg bound for any actual parameter product or signed-form encoding. -/
theorem parameter_sifted_card_le_selberg
    (s : SelbergSieve) (I : Finset ℕ) (F : ℕ → ℕ)
    (hsupport : s.support = I.image F)
    (hweights : ∀ x ∈ s.support,
      s.weights x = ((I.filter fun t => F t = x).card : ℝ)) :
    ((I.filter fun t => Nat.Coprime s.prodPrimes (F t)).card : ℝ) ≤
      s.totalMass / s.selbergBoundingSum +
        ∑ d ∈ s.prodPrimes.divisors,
          if (d : ℝ) ≤ s.level then
            (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
              |BoundingSieve.rem (s := s.toBoundingSieve) d|
          else 0 := by
  rw [← siftedSum_eq_parameter_card s I F hsupport hweights]
  exact SelbergSieve.selberg_bound_simple s

/-- Optimized finite Selberg bound for the actual product of two affine forms. -/
theorem two_affine_sifted_card_le_selberg
    (s : SelbergSieve) (I : Finset ℕ) (u₁ v₁ u₂ v₂ : ℕ)
    (hsupport : s.support = I.image (twoAffineProduct u₁ v₁ u₂ v₂))
    (hweights : ∀ x ∈ s.support,
      s.weights x =
        ((I.filter fun t => twoAffineProduct u₁ v₁ u₂ v₂ t = x).card : ℝ)) :
    ((I.filter fun t =>
      Nat.Coprime s.prodPrimes (twoAffineProduct u₁ v₁ u₂ v₂ t)).card : ℝ) ≤
      s.totalMass / s.selbergBoundingSum +
        ∑ d ∈ s.prodPrimes.divisors,
          if (d : ℝ) ≤ s.level then
            (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
              |BoundingSieve.rem (s := s.toBoundingSieve) d|
          else 0 :=
  parameter_sifted_card_le_selberg s I _ hsupport hweights

/-- Two primes larger than every sieve prime are automatically sifted. -/
theorem large_prime_pair_card_le_parameter_sifted
    (s : SelbergSieve) (I : Finset ℕ) (f g : ℕ → ℕ) (z : ℕ)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ s.prodPrimes → p ≤ z) :
    ((I.filter fun t =>
      (f t).Prime ∧ (g t).Prime ∧ z < f t ∧ z < g t).card : ℝ) ≤
      ((I.filter fun t => Nat.Coprime s.prodPrimes (f t * g t)).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (by
    intro t ht
    obtain ⟨hI, hf, hg, hzf, hzg⟩ := Finset.mem_filter.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨hI, Nat.Coprime.mul_right ?_ ?_⟩
    · rw [Nat.coprime_comm, hf.coprime_iff_not_dvd]
      intro hdiv
      exact Nat.not_lt_of_ge (hsmall (f t) hf hdiv) hzf
    · rw [Nat.coprime_comm, hg.coprime_iff_not_dvd]
      intro hdiv
      exact Nat.not_lt_of_ge (hsmall (g t) hg hdiv) hzg)

/-- The actual large-prime-pair count satisfies the optimized finite sieve bound. -/
theorem large_prime_pair_card_le_selberg
    (s : SelbergSieve) (I : Finset ℕ) (f g : ℕ → ℕ) (z : ℕ)
    (hsupport : s.support = I.image (fun t => f t * g t))
    (hweights : ∀ x ∈ s.support,
      s.weights x = ((I.filter fun t => f t * g t = x).card : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ s.prodPrimes → p ≤ z) :
    ((I.filter fun t =>
      (f t).Prime ∧ (g t).Prime ∧ z < f t ∧ z < g t).card : ℝ) ≤
      s.totalMass / s.selbergBoundingSum +
        ∑ d ∈ s.prodPrimes.divisors,
          if (d : ℝ) ≤ s.level then
            (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
              |BoundingSieve.rem (s := s.toBoundingSieve) d|
          else 0 :=
  (large_prime_pair_card_le_parameter_sifted s I f g z hsmall).trans
    (parameter_sifted_card_le_selberg s I (fun t => f t * g t) hsupport hweights)

/-- The optimized denominator is genuinely positive, never a vacuous zero. -/
theorem two_affine_selberg_denominator_pos (s : SelbergSieve) :
    0 < s.selbergBoundingSum :=
  SelbergSieve.selbergBoundingSum_pos s

/-- Every optimized Selberg weight has the exact absolute bound one. -/
theorem two_affine_selberg_weight_abs_le (s : SelbergSieve) (d : ℕ) :
    |s.selbergWeights d| ≤ (1 : ℝ) :=
  SelbergSieve.selberg_bound_weights s d

#print axioms SelbergSieve.selberg_bound_simple
#print axioms SelbergSieve.selbergBoundingSum_pos
#print axioms SelbergSieve.selberg_bound_weights
#print axioms Erdos689.siftedSum_eq_parameter_card
#print axioms Erdos689.parameter_sifted_card_le_selberg
#print axioms Erdos689.two_affine_sifted_card_le_selberg
#print axioms Erdos689.large_prime_pair_card_le_parameter_sifted
#print axioms Erdos689.large_prime_pair_card_le_selberg
#print axioms Erdos689.two_affine_selberg_denominator_pos
#print axioms Erdos689.two_affine_selberg_weight_abs_le

end Erdos689
