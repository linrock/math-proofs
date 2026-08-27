import Mathlib

/-!
# Uniform switched-prime local factors

The manuscript's coefficient-summed singular series is uniform in the switched
prime set because its normalized local factors are bounded below by a single
positive telescoping product.  These finite-product arguments do not assume a
prime-pattern theorem or assert an asymptotic edge count.
-/

open scoped BigOperators

namespace Erdos689

/-- The complete consecutive comparison product telescopes exactly. -/
theorem shifted_inverse_square_product (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 - 1 / ((i + 2 : ℕ) : ℝ) ^ 2)) =
      ((n + 2 : ℕ) : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    have h₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h₂ : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h₃ : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    field_simp
    ring

/-- Every consecutive comparison product has the same positive absolute bound. -/
theorem shifted_inverse_square_product_lower (n : ℕ) :
    (1 / 2 : ℝ) ≤
      ∏ i ∈ Finset.range n, (1 - 1 / ((i + 2 : ℕ) : ℝ) ^ 2) := by
  rw [shifted_inverse_square_product]
  have hpositive : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
  apply (le_div_iff₀ hpositive).mpr
  push_cast
  linarith

/-- The inverse-square comparison factors are nonnegative on their true domain. -/
theorem inverse_square_factor_nonnegative {j : ℕ} (hj : 2 ≤ j) :
    (0 : ℝ) ≤ 1 - 1 / (j : ℝ) ^ 2 := by
  have hreal : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hpositive : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hpositive).mpr
  nlinarith

/-- Deleting arbitrary comparison factors cannot lower the universal half bound. -/
theorem finite_inverse_square_product_lower (T : Finset ℕ)
    (hlarge : ∀ j ∈ T, 2 ≤ j) :
    (1 / 2 : ℝ) ≤ ∏ j ∈ T, (1 - 1 / (j : ℝ) ^ 2) := by
  let N := T.sup id + 1
  have hsubset : T ⊆ Finset.Ico 2 N := by
    intro j hj
    apply Finset.mem_Ico.mpr
    refine ⟨hlarge j hj, ?_⟩
    have hsup : j ≤ T.sup id := Finset.le_sup (f := id) hj
    dsimp [N]
    omega
  have hfull : (1 / 2 : ℝ) ≤
      ∏ j ∈ Finset.Ico 2 N, (1 - 1 / (j : ℝ) ^ 2) := by
    rw [Finset.prod_Ico_eq_prod_range]
    simpa [Nat.add_comm] using shifted_inverse_square_product_lower (N - 2)
  apply hfull.trans
  apply Finset.prod_le_prod_of_subset_of_le_one hsubset
  · intro j hj
    exact inverse_square_factor_nonnegative (Finset.mem_Ico.mp hj).1
  · intro j _ _
    exact sub_le_self _ (by positivity)

/-- Every switched prime is uniquely represented by its positive half-index. -/
theorem switched_prime_half_index {p : ℕ}
    (hprime : p.Prime) (hlarge : 3 < p) :
    p = 2 * (p / 2) + 1 ∧ 2 ≤ p / 2 := by
  have hodd := hprime.eq_two_or_odd.resolve_left (by omega)
  have hdivision := Nat.mod_add_div p 2
  omega

/-- The manuscript's worst switched factor dominates its telescoping comparison. -/
theorem switched_local_factor_dominates_half_index {p : ℕ}
    (hprime : p.Prime) (hlarge : 3 < p) :
    1 - 1 / ((p / 2 : ℕ) : ℝ) ^ 2 ≤
      1 - 3 / ((p : ℝ) - 1) ^ 2 := by
  obtain ⟨hidentity, hindex⟩ := switched_prime_half_index hprime hlarge
  have hreal : (p : ℝ) - 1 = 2 * ((p / 2 : ℕ) : ℝ) := by
    have hcast : (p : ℝ) = 2 * ((p / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hidentity
    linarith
  rw [hreal]
  have hpositive : (0 : ℝ) < ((p / 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < p / 2)
  field_simp
  nlinarith

/-- The switched-set Euler product has an absolute, parameter-independent half bound. -/
theorem switched_prime_euler_product_lower (S : Finset ℕ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s) :
    (1 / 2 : ℝ) ≤
      ∏ s ∈ S, (1 - 3 / ((s : ℝ) - 1) ^ 2) := by
  classical
  let T := S.image fun s => s / 2
  have hindices : ∀ j ∈ T, 2 ≤ j := by
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
    exact (switched_prime_half_index (hsupport s hs).1 (hsupport s hs).2).2
  have hinjective : Set.InjOn (fun s : ℕ => s / 2) ↑S := by
    intro p hp q hq heq
    change p / 2 = q / 2 at heq
    have hpleft := (switched_prime_half_index
      (hsupport p hp).1 (hsupport p hp).2).1
    have hqleft := (switched_prime_half_index
      (hsupport q hq).1 (hsupport q hq).2).1
    omega
  have hcomparison :
      (∏ s ∈ S, (1 - 1 / ((s / 2 : ℕ) : ℝ) ^ 2)) ≤
        ∏ s ∈ S, (1 - 3 / ((s : ℝ) - 1) ^ 2) := by
    apply Finset.prod_le_prod
    · intro s hs
      exact inverse_square_factor_nonnegative
        (switched_prime_half_index (hsupport s hs).1 (hsupport s hs).2).2
    · intro s hs
      exact switched_local_factor_dominates_half_index
        (hsupport s hs).1 (hsupport s hs).2
  calc
    (1 / 2 : ℝ) ≤ ∏ j ∈ T, (1 - 1 / (j : ℝ) ^ 2) :=
      finite_inverse_square_product_lower T hindices
    _ = ∏ s ∈ S, (1 - 1 / ((s / 2 : ℕ) : ℝ) ^ 2) :=
      Finset.prod_image hinjective
    _ ≤ ∏ s ∈ S, (1 - 3 / ((s : ℝ) - 1) ^ 2) := hcomparison

/-- The exceptional switched-prime kernel has the exact advertised normalization. -/
theorem exceptional_switched_kernel_identity {s : ℝ}
    (hzero : s ≠ 0) (hone : s ≠ 1) :
    s * (s - 2 - 1 / s) / (s - 1) ^ 2 =
      1 - 2 / (s - 1) ^ 2 := by
  field_simp
  ring

/-- The generic switched-prime kernel has the exact advertised normalization. -/
theorem generic_switched_kernel_identity {s : ℝ}
    (hzero : s ≠ 0) (hone : s ≠ 1) :
    s * (s - 2 - 2 / s) / (s - 1) ^ 2 =
      1 - 3 / (s - 1) ^ 2 := by
  field_simp
  ring

/-- The two possible coefficient-summed normalized switched local factors. -/
noncomputable def normalizedSwitchedFactor (s : ℕ) (exceptional : Bool) : ℝ :=
  if exceptional then
    1 - 2 / ((s : ℝ) - 1) ^ 2
  else
    1 - 3 / ((s : ℝ) - 1) ^ 2

/-- The generic factor is the pointwise minimum, independently of the selector. -/
theorem normalized_switched_factor_lower (s : ℕ) (exceptional : Bool) :
    1 - 3 / ((s : ℝ) - 1) ^ 2 ≤
      normalizedSwitchedFactor s exceptional := by
  cases exceptional with
  | false => simp [normalizedSwitchedFactor]
  | true =>
    change 1 - 3 / ((s : ℝ) - 1) ^ 2 ≤
      1 - 2 / ((s : ℝ) - 1) ^ 2
    have hnonnegative : (0 : ℝ) ≤ 1 / ((s : ℝ) - 1) ^ 2 := by positivity
    calc
      1 - 3 / ((s : ℝ) - 1) ^ 2 =
          1 - 3 * (1 / ((s : ℝ) - 1) ^ 2) := by ring
      _ ≤ 1 - 2 * (1 / ((s : ℝ) - 1) ^ 2) := by nlinarith
      _ = 1 - 2 / ((s : ℝ) - 1) ^ 2 := by ring

/-- Every switched local factor is bounded above by one. -/
theorem normalized_switched_factor_upper (s : ℕ) (exceptional : Bool) :
    normalizedSwitchedFactor s exceptional ≤ 1 := by
  cases exceptional <;> simp [normalizedSwitchedFactor]
  all_goals positivity

/-- Every coefficient-summed selector product has one uniform absolute bound. -/
theorem normalized_switched_selector_product_lower (S : Finset ℕ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (exceptional : ℕ → Bool) :
    (1 / 2 : ℝ) ≤
      ∏ s ∈ S, normalizedSwitchedFactor s (exceptional s) := by
  apply (switched_prime_euler_product_lower S hsupport).trans
  apply Finset.prod_le_prod
  · intro s hs
    have hcomparison := switched_local_factor_dominates_half_index
      (hsupport s hs).1 (hsupport s hs).2
    exact (inverse_square_factor_nonnegative
      (switched_prime_half_index (hsupport s hs).1 (hsupport s hs).2).2).trans
      hcomparison
  · intro s _
    exact normalized_switched_factor_lower s (exceptional s)

/-- Summing over any robust-residue subset preserves the same uniform constant. -/
theorem robust_selector_normalized_sum_lower {ι : Type*}
    (R : Finset ι) (S : Finset ℕ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (exceptional : ι → ℕ → Bool) :
    (R.card : ℝ) / 2 ≤
      ∑ r ∈ R, ∏ s ∈ S, normalizedSwitchedFactor s (exceptional r s) := by
  calc
    (R.card : ℝ) / 2 = ∑ _r ∈ R, (1 / 2 : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ r ∈ R, ∏ s ∈ S, normalizedSwitchedFactor s (exceptional r s) := by
      apply Finset.sum_le_sum
      intro r _
      exact normalized_switched_selector_product_lower S hsupport (exceptional r)

/-- The full switched local-factor sum is at least half its robust unit density. -/
theorem robust_selector_coefficient_sum_lower {ι : Type*}
    (R : Finset ι) (S : Finset ℕ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (exceptional : ι → ℕ → Bool) :
    ((R.card : ℝ) / (∏ s ∈ S, ((s : ℝ) - 1))) / 2 ≤
      ∑ r ∈ R, ∏ s ∈ S,
        normalizedSwitchedFactor s (exceptional r s) / ((s : ℝ) - 1) := by
  have hdenominator : (0 : ℝ) < ∏ s ∈ S, ((s : ℝ) - 1) := by
    apply Finset.prod_pos
    intro s hs
    have hlarge : (3 : ℝ) < s := by exact_mod_cast (hsupport s hs).2
    linarith
  have hsum := robust_selector_normalized_sum_lower R S hsupport exceptional
  calc
    ((R.card : ℝ) / (∏ s ∈ S, ((s : ℝ) - 1))) / 2 =
        ((R.card : ℝ) / 2) / (∏ s ∈ S, ((s : ℝ) - 1)) := by ring
    _ ≤ (∑ r ∈ R, ∏ s ∈ S, normalizedSwitchedFactor s (exceptional r s)) /
        (∏ s ∈ S, ((s : ℝ) - 1)) :=
      (div_le_div_iff_of_pos_right hdenominator).mpr hsum
    _ = ∑ r ∈ R, ∏ s ∈ S,
        normalizedSwitchedFactor s (exceptional r s) / ((s : ℝ) - 1) := by
      simp_rw [Finset.prod_div_distrib]
      rw [Finset.sum_div]

/-- Distinct prime support factors give exactly the manuscript's totient denominator. -/
theorem prime_support_totient_product (S : Finset ℕ)
    (hsupport : ∀ s ∈ S, s.Prime) :
    (∏ s ∈ S, s).totient = ∏ s ∈ S, (s - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p T hnotmem ih =>
    have hp : p.Prime := hsupport p (by simp)
    have hrest : ∀ s ∈ T, s.Prime := by
      intro s hs
      exact hsupport s (by simp [hs])
    have hnotdiv : ¬ p ∣ ∏ s ∈ T, s := by
      intro hdiv
      obtain ⟨s, hs, hdvd⟩ :=
        (hp.prime.dvd_finsetProd_iff (fun s : ℕ => s)).mp hdiv
      have heq := (Nat.prime_dvd_prime_iff_eq hp (hrest s hs)).mp hdvd
      exact hnotmem (by simpa [heq] using hs)
    have hcoprime : p.Coprime (∏ s ∈ T, s) :=
      hp.coprime_iff_not_dvd.mpr hnotdiv
    rw [Finset.prod_insert hnotmem, Nat.totient_mul hcoprime,
      Nat.totient_prime hp, Finset.prod_insert hnotmem, ih hrest]

/-- The real local denominators reproduce the exact integer totient, not a proxy. -/
theorem prime_support_totient_real_product (S : Finset ℕ)
    (hsupport : ∀ s ∈ S, s.Prime) :
    (((∏ s ∈ S, s).totient : ℕ) : ℝ) =
      ∏ s ∈ S, ((s : ℝ) - 1) := by
  rw [prime_support_totient_product S hsupport]
  push_cast
  apply Finset.prod_congr rfl
  intro s hs
  simpa using Nat.cast_sub (R := ℝ) (hsupport s hs).one_le

/-- The coefficient-summed robust selector is at least half the actual density. -/
theorem robust_selector_totient_density_lower {ι : Type*}
    (R : Finset ι) (S : Finset ℕ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s)
    (exceptional : ι → ℕ → Bool) :
    ((R.card : ℝ) /
      (((∏ s ∈ S, s).totient : ℕ) : ℝ)) / 2 ≤
      ∑ r ∈ R, ∏ s ∈ S,
        normalizedSwitchedFactor s (exceptional r s) / ((s : ℝ) - 1) := by
  rw [prime_support_totient_real_product S (fun s hs => (hsupport s hs).1)]
  exact robust_selector_coefficient_sum_lower R S hsupport exceptional

end Erdos689

#print axioms Erdos689.shifted_inverse_square_product
#print axioms Erdos689.shifted_inverse_square_product_lower
#print axioms Erdos689.inverse_square_factor_nonnegative
#print axioms Erdos689.finite_inverse_square_product_lower
#print axioms Erdos689.switched_prime_half_index
#print axioms Erdos689.switched_local_factor_dominates_half_index
#print axioms Erdos689.switched_prime_euler_product_lower
#print axioms Erdos689.exceptional_switched_kernel_identity
#print axioms Erdos689.generic_switched_kernel_identity
#print axioms Erdos689.normalized_switched_factor_lower
#print axioms Erdos689.normalized_switched_factor_upper
#print axioms Erdos689.normalized_switched_selector_product_lower
#print axioms Erdos689.robust_selector_normalized_sum_lower
#print axioms Erdos689.robust_selector_coefficient_sum_lower
#print axioms Erdos689.prime_support_totient_product
#print axioms Erdos689.prime_support_totient_real_product
#print axioms Erdos689.robust_selector_totient_density_lower
