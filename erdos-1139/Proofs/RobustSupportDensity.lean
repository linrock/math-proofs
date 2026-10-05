module

public import Mathlib

@[expose] public section


open Filter Finset
open scoped Topology BigOperators

namespace Erdos689

/-- Deleting every prime at most an arbitrary fixed cutoff does not make the
prime-reciprocal series summable. -/
theorem prime_reciprocal_tail_not_summable (J : ℕ) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ J < p then (1 : ℝ) / p else 0) := by
  let f : ℕ → ℝ := {p : ℕ | p.Prime}.indicator (fun p => (1 : ℝ) / p)
  have htail : ¬ Summable ({p : ℕ | p ≤ J}ᶜ.indicator f) := by
    intro h
    have hsub : Summable (f ∘ Subtype.val : {p : ℕ // p ∈ {p : ℕ | p ≤ J}ᶜ} → ℝ) :=
      summable_subtype_iff_indicator.mpr h
    exact not_summable_one_div_on_primes
      ((Set.finite_le_nat J).summable_compl_iff.mp hsub)
  intro h
  apply htail
  convert h using 1
  funext p
  by_cases hp : p.Prime <;> by_cases hJ : J < p <;>
    simp [f, hp, hJ, not_le]

/-- The finite initial sums of the prime-reciprocal tail diverge to infinity. -/
theorem prime_reciprocal_tail_partial_sums_tendsto (J : ℕ) :
    Tendsto (fun n : ℕ => ∑ p ∈ range n,
      if p.Prime ∧ J < p then (1 : ℝ) / p else 0) atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg ?_).mp
  · exact prime_reciprocal_tail_not_summable J
  · intro p
    split <;> positivity

/-- Prime supports above any prescribed cutoff have arbitrarily large
reciprocal sums.  This is unconditional and needs no Mertens estimate. -/
theorem exists_prime_support_reciprocal_sum_gt (J : ℕ) (C : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ J < p) ∧
      C < ∑ p ∈ S, (1 : ℝ) / p := by
  obtain ⟨n, hn⟩ := (tendsto_atTop_atTop.mp
    (prime_reciprocal_tail_partial_sums_tendsto J)) (C + 1)
  refine ⟨(range n).filter (fun p => p.Prime ∧ J < p), ?_, ?_⟩
  · intro p hp
    exact (mem_filter.mp hp).2
  · have hsum := hn n (le_refl n)
    simp only [sum_filter] at *
    linarith

/-- Replacing the prime denominator `p` by `p - 1` only increases every
summand of a prime-support reciprocal sum. -/
theorem prime_support_reciprocal_le_shifted (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, (1 : ℝ) / p) ≤ ∑ p ∈ S, 1 / ((p : ℝ) - 1) := by
  apply sum_le_sum
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- The elementary product-to-exponential estimate for an arbitrary finite
family of factors in `[0,1]`. -/
theorem finite_one_sub_product_le_exp_neg_sum {ι : Type*} (S : Finset ι)
    (a : ι → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i ∧ a i ≤ 1) :
    ∏ i ∈ S, (1 - a i) ≤ Real.exp (-(∑ i ∈ S, a i)) := by
  rw [← sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact sub_nonneg.mpr (ha i hi).2
  · intro i _
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-a i)

/-- The precise product in the robust-support union bound is at most the
exponential of its negative shifted reciprocal sum. -/
theorem prime_support_product_le_exp_neg_shifted_sum (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))) ≤
      Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) := by
  apply finite_one_sub_product_le_exp_neg_sum
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
  constructor
  · exact div_nonneg (by norm_num) (by linarith)
  · apply (div_le_iff₀ (by linarith)).mpr
    linarith

/-- On prime supports above `3`, the second shifted reciprocal sum is bounded
by twice the first shifted reciprocal sum. -/
theorem prime_support_second_shift_sum_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, 3 < p) :
    (∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 2)) ≤
      2 * ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) := by
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro p hp
  have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (hS p hp)
  calc
    (1 : ℝ) / ((p : ℝ) - 2) ≤ 2 / ((p : ℝ) - 1) := by
      apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      linarith
    _ = 2 * (1 / ((p : ℝ) - 1)) := by ring

/-- The exact elementary error majorant arising from the robust-support
union bound tends to zero, for every fixed number of switching offsets. -/
theorem robust_support_exponential_error_tendsto (J : ℕ) :
    Tendsto (fun x : ℝ => (J : ℝ) * Real.exp (-x) * (1 + 2 * x))
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h1 : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h : Tendsto
      (fun x : ℝ => (J : ℝ) * (Real.exp (-x) + 2 * (x * Real.exp (-x))))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (h0.add (tendsto_const_nhds.mul h1))
  convert h using 1
  funext x
  ring

/-- For every fixed `J` and every positive error tolerance, there is a finite
prime support strictly above `max J 3` whose exact robust-support union-bound
majorant is smaller than the tolerance.  In particular, the auxiliary support
can make robust density arbitrarily close to one without invoking Mertens. -/
theorem exists_prime_support_robust_majorant_lt (J : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ max J 3 < p) ∧
      (J : ℝ) * (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))) *
        (1 + ∑ p ∈ S, 1 / ((p : ℝ) - 2)) < ε := by
  have hevent : ∀ᶠ x : ℝ in atTop,
      (J : ℝ) * Real.exp (-x) * (1 + 2 * x) < ε :=
    (robust_support_exponential_error_tendsto J).eventually (gt_mem_nhds hε)
  obtain ⟨X, hX⟩ := eventually_atTop.mp hevent
  obtain ⟨S, hS, hlarge⟩ := exists_prime_support_reciprocal_sum_gt (max J 3) X
  refine ⟨S, hS, ?_⟩
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hthree : ∀ p ∈ S, 3 < p := by
    intro p hp
    exact lt_of_le_of_lt (le_max_right J 3) (hS p hp).2
  have hshift : X ≤ ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) :=
    le_trans hlarge.le (prime_support_reciprocal_le_shifted S hprime)
  have hprod := prime_support_product_le_exp_neg_shifted_sum S hprime
  have hsum := prime_support_second_shift_sum_le S hthree
  have htail : 0 ≤ 1 + ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 2) := by
    apply add_nonneg (by norm_num)
    apply sum_nonneg
    intro p hp
    have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast hthree p hp
    exact div_nonneg (by norm_num) (by linarith)
  calc
    (J : ℝ) * (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1))) *
        (1 + ∑ p ∈ S, 1 / ((p : ℝ) - 2))
      ≤ (J : ℝ) * Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) *
        (1 + ∑ p ∈ S, 1 / ((p : ℝ) - 2)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg J)) htail
    _ ≤ (J : ℝ) * Real.exp (-(∑ p ∈ S, 1 / ((p : ℝ) - 1))) *
        (1 + 2 * ∑ p ∈ S, 1 / ((p : ℝ) - 1)) := by
          have hplus : (1 + ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 2)) ≤
              1 + 2 * ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) := by
            linarith
          apply mul_le_mul_of_nonneg_left hplus
          positivity
    _ < ε := hX _ hshift

end Erdos689

