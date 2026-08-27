import Mathlib

/-!
# Exact initial-deficiency coefficient normalization for Erdős problem #689

For every fixed finite support of integers greater than one, the smooth-core
coefficient in the manuscript's initial-deficiency calculation is exactly one:

`(∑' k, 2⁻¹ ^ (k + 1)) * ∏ s ∈ S,
  ((s - 2) / (s - 1) + ∑' e, s⁻¹ ^ (e + 1)) = 1`.

The shifted-series identities additionally give exact exponential tails for
each independent prime-power coordinate. These results normalize the formal
coefficient; they do not assert the still-missing interchange with the
initial-deficiency prime asymptotic.
-/

open scoped BigOperators

namespace Erdos689

/-- The positive dyadic powers have total mass one. -/
theorem dyadic_deficiency_coefficient_tsum :
    (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ (k + 1)) = 1 := by
  calc
    (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ (k + 1)) =
        (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ k) * ((2 : ℝ)⁻¹) := by
          simp_rw [pow_succ]
          exact tsum_mul_right
    _ = 1 := by rw [tsum_geometric_of_lt_one (by positivity) (by norm_num)]; norm_num

/-- The strictly positive powers of `s⁻¹` sum to `1 / (s - 1)`. -/
theorem smooth_prime_power_coefficient_tsum (s : ℕ) (hs : 1 < s) :
    (∑' e : ℕ, ((s : ℝ)⁻¹) ^ (e + 1)) = ((s : ℝ) - 1)⁻¹ := by
  have hs_real : (1 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs_pos : (0 : ℝ) < (s : ℝ) := lt_trans (by norm_num) hs_real
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
  have hs_sub_ne : (s : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hs_real)
  calc
    (∑' e : ℕ, ((s : ℝ)⁻¹) ^ (e + 1)) =
        (∑' e : ℕ, ((s : ℝ)⁻¹) ^ e) * (s : ℝ)⁻¹ := by
          simp_rw [pow_succ]
          exact tsum_mul_right
    _ = (1 - (s : ℝ)⁻¹)⁻¹ * (s : ℝ)⁻¹ := by
          rw [tsum_geometric_of_lt_one (by positivity) ((inv_lt_one₀ hs_pos).mpr hs_real)]
    _ = ((s : ℝ) - 1)⁻¹ := by
          field_simp

/-- Every single switched-prime coefficient selector is exactly normalized. -/
theorem deficiency_local_selector_eq_one (s : ℕ) (hs : 1 < s) :
    ((s : ℝ) - 2) / ((s : ℝ) - 1) +
      (∑' e : ℕ, ((s : ℝ)⁻¹) ^ (e + 1)) = 1 := by
  have hs_real : (1 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs_sub_ne : (s : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hs_real)
  rw [smooth_prime_power_coefficient_tsum s hs]
  field_simp
  ring

/-- The complete finite switched-prime selector product is exactly one. -/
theorem deficiency_selector_product_eq_one (S : Finset ℕ)
    (hS : ∀ s ∈ S, 1 < s) :
    (∏ s ∈ S, (((s : ℝ) - 2) / ((s : ℝ) - 1) +
      ∑' e : ℕ, ((s : ℝ)⁻¹) ^ (e + 1))) = 1 := by
  exact Finset.prod_eq_one fun s hs ↦ deficiency_local_selector_eq_one s (hS s hs)

/-- The exact smooth-core coefficient in the initial-demand expansion is one. -/
theorem initial_deficiency_coefficient_eq_one (S : Finset ℕ)
    (hS : ∀ s ∈ S, 1 < s) :
    (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ (k + 1)) *
      (∏ s ∈ S, (((s : ℝ) - 2) / ((s : ℝ) - 1) +
        ∑' e : ℕ, ((s : ℝ)⁻¹) ^ (e + 1))) = 1 := by
  rw [dyadic_deficiency_coefficient_tsum, deficiency_selector_product_eq_one S hS]
  norm_num

/-- A shifted prime-power coordinate has an exact geometric tail. -/
theorem smooth_prime_power_coefficient_tail (s : ℕ) (hs : 1 < s) (E : ℕ) :
    (∑' e : ℕ, ((s : ℝ)⁻¹) ^ (e + E + 1)) =
      ((s : ℝ)⁻¹) ^ E / ((s : ℝ) - 1) := by
  calc
    (∑' e : ℕ, ((s : ℝ)⁻¹) ^ (e + E + 1)) =
        (∑' e : ℕ, ((s : ℝ)⁻¹) ^ (e + 1)) * ((s : ℝ)⁻¹) ^ E := by
          rw [← tsum_mul_right]
          congr 1
          funext e
          rw [← pow_add]
          congr 1
          omega
    _ = ((s : ℝ) - 1)⁻¹ * ((s : ℝ)⁻¹) ^ E := by
          rw [smooth_prime_power_coefficient_tsum s hs]
    _ = ((s : ℝ)⁻¹) ^ E / ((s : ℝ) - 1) := by
          simp [div_eq_mul_inv, mul_comm]

/-- The positive dyadic coefficient tail is exactly `2⁻ᴱ`. -/
theorem dyadic_deficiency_coefficient_tail (E : ℕ) :
    (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ (k + E + 1)) = ((2 : ℝ)⁻¹) ^ E := by
  convert smooth_prime_power_coefficient_tail 2 (by norm_num) E using 1 <;> norm_num

#print axioms dyadic_deficiency_coefficient_tsum
#print axioms smooth_prime_power_coefficient_tsum
#print axioms deficiency_local_selector_eq_one
#print axioms deficiency_selector_product_eq_one
#print axioms initial_deficiency_coefficient_eq_one
#print axioms smooth_prime_power_coefficient_tail
#print axioms dyadic_deficiency_coefficient_tail

end Erdos689
