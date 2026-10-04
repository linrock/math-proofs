module

public import Mathlib


@[expose] public section

/-!
# Prime-exponent coordinate model for divisors of $Q$

Constructs the equivalence `choicesEquivDivisors Q` between divisors of a
nonzero natural number $Q$ and bounded prime-exponent vectors `Choices Q`,
rewriting the double divisor sum over $\operatorname{lcm}(d, e)$ as a sum over
coordinatewise maxima of exponent vectors.
-/

namespace Erdos2.DivisorModel

open scoped BigOperators

abbrev PrimeIndex (Q : ℕ) := Q.primeFactors

abbrev Choices (Q : ℕ) := ∀ p : PrimeIndex Q, Fin (Q.factorization (p : ℕ) + 1)

noncomputable def exponentVector (Q : ℕ) (v : Choices Q) : ℕ →₀ ℕ := by
  classical
  exact Finsupp.onFinset Q.primeFactors
    (fun p => if hp : p ∈ Q.primeFactors then (v ⟨p, hp⟩ : ℕ) else 0)
    (by
      intro p hp
      by_contra h
      simp [h] at hp)

@[simp] theorem exponentVector_apply_inside (Q : ℕ) (v : Choices Q)
    {p : ℕ} (hp : p ∈ Q.primeFactors) :
    exponentVector Q v p = (v ⟨p, hp⟩ : ℕ) := by
  classical
  simp only [exponentVector, Finsupp.onFinset_apply, hp, ↓reduceDIte]

@[simp] theorem exponentVector_apply_outside (Q : ℕ) (v : Choices Q)
    {p : ℕ} (hp : p ∉ Q.primeFactors) : exponentVector Q v p = 0 := by
  classical
  simp only [exponentVector, Finsupp.onFinset_apply, hp, ↓reduceDIte]

theorem exponentVector_le (Q : ℕ) (v : Choices Q) :
    exponentVector Q v ≤ Q.factorization := by
  classical
  intro p
  by_cases hp : p ∈ Q.primeFactors
  · rw [exponentVector_apply_inside Q v hp]
    exact Nat.le_of_lt_succ (v ⟨p, hp⟩).isLt
  · rw [exponentVector_apply_outside Q v hp]
    exact Nat.zero_le _

noncomputable def divisorValue (Q : ℕ) (v : Choices Q) : ℕ :=
  (exponentVector Q v).prod (fun p k => p ^ k)

theorem divisorValue_dvd (Q : ℕ) (v : Choices Q) : divisorValue Q v ∣ Q := by
  exact Nat.prod_pow_dvd_of_le_factorization (exponentVector_le Q v)

theorem divisorValue_ne_zero (Q : ℕ) (hQ : Q ≠ 0) (v : Choices Q) :
    divisorValue Q v ≠ 0 :=
  ne_zero_of_dvd_ne_zero hQ (divisorValue_dvd Q v)

theorem divisorValue_factorization (Q : ℕ) (v : Choices Q) :
    (divisorValue Q v).factorization = exponentVector Q v := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization (exponentVector_le Q v)

noncomputable def toDivisor (Q : ℕ) (hQ : Q ≠ 0) (v : Choices Q) : Q.divisors :=
  ⟨divisorValue Q v, Nat.mem_divisors.mpr ⟨divisorValue_dvd Q v, hQ⟩⟩

theorem divisor_factorization_le (Q : ℕ) (hQ : Q ≠ 0) (d : Q.divisors) :
    d.val.factorization ≤ Q.factorization := by
  have hdvd := Nat.dvd_of_mem_divisors d.property
  exact (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hQ hdvd) hQ).mpr hdvd

noncomputable def toChoices (Q : ℕ) (hQ : Q ≠ 0) (d : Q.divisors) : Choices Q :=
  fun p => ⟨d.val.factorization (p : ℕ),
    Nat.lt_succ_of_le (divisor_factorization_le Q hQ d (p : ℕ))⟩

theorem exponentVector_toChoices (Q : ℕ) (hQ : Q ≠ 0) (d : Q.divisors) :
    exponentVector Q (toChoices Q hQ d) = d.val.factorization := by
  classical
  ext p
  by_cases hp : p ∈ Q.primeFactors
  · rw [exponentVector_apply_inside Q _ hp]
    rfl
  · rw [exponentVector_apply_outside Q _ hp]
    have hz : Q.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    symm
    exact Nat.eq_zero_of_le_zero (hz ▸ divisor_factorization_le Q hQ d p)

noncomputable def choicesEquivDivisors (Q : ℕ) (hQ : Q ≠ 0) :
    Choices Q ≃ Q.divisors where
  toFun := toDivisor Q hQ
  invFun := toChoices Q hQ
  left_inv v := by
    funext p
    apply Fin.ext
    change (divisorValue Q v).factorization (p : ℕ) = (v p : ℕ)
    rw [divisorValue_factorization, exponentVector_apply_inside Q v p.property]
  right_inv d := by
    apply Subtype.ext
    change divisorValue Q (toChoices Q hQ d) = d.val
    unfold divisorValue
    rw [exponentVector_toChoices]
    exact Nat.prod_factorization_pow_eq_self
      (ne_zero_of_dvd_ne_zero hQ (Nat.dvd_of_mem_divisors d.property))

theorem divisorValue_eq_prod (Q : ℕ) (v : Choices Q) :
    divisorValue Q v = ∏ p : PrimeIndex Q, (p : ℕ) ^ (v p : ℕ) := by
  classical
  unfold divisorValue
  rw [(exponentVector Q v).prod_of_support_subset
    (Finsupp.support_mono (exponentVector_le Q v)) (fun p k => p ^ k)
    (by intro p hp; simp)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p hp
  rw [exponentVector_apply_inside Q v p.property]
  rfl

noncomputable def maxChoices (Q : ℕ) (a b : Choices Q) : Choices Q :=
  fun p => ⟨max (a p : ℕ) (b p : ℕ), max_lt_iff.mpr ⟨(a p).isLt, (b p).isLt⟩⟩

theorem lcm_divisorValue_eq (Q : ℕ) (hQ : Q ≠ 0) (a b : Choices Q) :
    Nat.lcm (divisorValue Q a) (divisorValue Q b) = divisorValue Q (maxChoices Q a b) := by
  classical
  apply Nat.eq_of_factorization_eq'
    (Nat.lcm_ne_zero (divisorValue_ne_zero Q hQ a) (divisorValue_ne_zero Q hQ b))
    (divisorValue_ne_zero Q hQ _)
  rw [Nat.factorization_lcm (divisorValue_ne_zero Q hQ a) (divisorValue_ne_zero Q hQ b),
    divisorValue_factorization, divisorValue_factorization, divisorValue_factorization]
  ext p
  by_cases hp : p ∈ Q.primeFactors
  · simp only [Finsupp.sup_apply, exponentVector_apply_inside Q _ hp, maxChoices]
  · simp only [Finsupp.sup_apply, exponentVector_apply_outside Q _ hp, max_self]

theorem two_pow_card_primeFactors_eq_prod (Q : ℕ) (v : Choices Q) :
    (2 : ℝ) ^ (divisorValue Q v).primeFactors.card =
      ∏ p : PrimeIndex Q, if (v p : ℕ) = 0 then (1 : ℝ) else 2 := by
  classical
  rw [← Nat.support_factorization, divisorValue_factorization]
  have heq : (exponentVector Q v).prod
      (fun _ k => if k = 0 then (1 : ℝ) else 2) =
      (2 : ℝ) ^ (exponentVector Q v).support.card := by
    calc
      _ = ∏ p ∈ (exponentVector Q v).support, (2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp' := Finsupp.mem_support_iff.mp hp
        simp only [hp', ↓reduceIte]
      _ = _ := by rw [Finset.prod_const]
  rw [← heq]
  rw [(exponentVector Q v).prod_of_support_subset
    (Finsupp.support_mono (exponentVector_le Q v))
    (fun _ k => if k = 0 then (1 : ℝ) else 2) (by intro p hp; simp)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p hp
  rw [exponentVector_apply_inside Q v p.property]
  rfl

theorem primeFactorWeight_divisorValue_eq (Q : ℕ) (v : Choices Q) :
    (2 : ℝ) ^ (divisorValue Q v).primeFactors.card / (divisorValue Q v : ℝ) =
      ∏ p : PrimeIndex Q, if (v p : ℕ) = 0 then (1 : ℝ)
        else 2 / (p : ℝ) ^ (v p : ℕ) := by
  classical
  rw [two_pow_card_primeFactors_eq_prod, divisorValue_eq_prod]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hv : (v p : ℕ) = 0 <;> simp [hv]

theorem lcm_weight_divisorValue_eq (Q : ℕ) (hQ : Q ≠ 0) (a b : Choices Q) :
    (2 : ℝ) ^ (Nat.lcm (divisorValue Q a) (divisorValue Q b)).primeFactors.card /
      (Nat.lcm (divisorValue Q a) (divisorValue Q b) : ℝ) =
      ∏ p : PrimeIndex Q, if max (a p : ℕ) (b p : ℕ) = 0 then (1 : ℝ)
        else 2 / (p : ℝ) ^ max (a p : ℕ) (b p : ℕ) := by
  rw [lcm_divisorValue_eq Q hQ a b, primeFactorWeight_divisorValue_eq]
  rfl

theorem sum_divisors_eq_sum_choices {A : Type*} [AddCommMonoid A]
    (Q : ℕ) (hQ : Q ≠ 0) (f : ℕ → A) :
    (∑ d ∈ Q.divisors, f d) = ∑ a : Choices Q, f (divisorValue Q a) := by
  classical
  rw [← Finset.sum_coe_sort]
  symm
  exact Fintype.sum_equiv (choicesEquivDivisors Q hQ)
    (fun a => f (divisorValue Q a)) (fun d => f d.val) (fun a => rfl)

/-- Exact transfer of the natural-divisor double sum to all bounded prime
exponent vectors. Arbitrary prime powers and divisor one are retained. -/
theorem double_divisor_sum_eq_vector (Q : ℕ) (hQ : Q ≠ 0) :
    (∑ d ∈ Q.divisors, ∑ e ∈ Q.divisors,
      (2 : ℝ) ^ (Nat.lcm d e).primeFactors.card / (Nat.lcm d e : ℝ)) =
    ∑ a : Choices Q, ∑ b : Choices Q,
      ∏ p : PrimeIndex Q, if max (a p : ℕ) (b p : ℕ) = 0 then (1 : ℝ)
        else 2 / (p : ℝ) ^ max (a p : ℕ) (b p : ℕ) := by
  classical
  calc
    _ = ∑ a : Choices Q, ∑ b : Choices Q,
        (2 : ℝ) ^ (Nat.lcm (divisorValue Q a) (divisorValue Q b)).primeFactors.card /
          (Nat.lcm (divisorValue Q a) (divisorValue Q b) : ℝ) := by
      rw [sum_divisors_eq_sum_choices Q hQ]
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_divisors_eq_sum_choices Q hQ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact lcm_weight_divisorValue_eq Q hQ a b

end Erdos2.DivisorModel
