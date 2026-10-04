module

public import Mathlib


@[expose] public section

/-!
# Prime-power geometric coefficient bounds for rectangle pairs

Factors the double sum over `K × Fin γ` and bounds the prime-power geometric
sum $\sum_{j=0}^{\gamma-1} q^{-(j+1)}$ by $1 / (q - 1)$ for $q \ge 2$.
-/

namespace Erdos2.Rectangles

open Finset

theorem ordered_pair_sum_factor {K L : Type*} [Fintype K] [Fintype L]
    (c : L → ℝ) (H : K → K → ℝ) :
    (∑ i : K × L, ∑ j : K × L, c i.2 * c j.2 * H i.1 j.1) =
      (∑ l, c l) ^ 2 * ∑ k, ∑ k', H k k' := by
  classical
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ k : K, ∑ k' : K, ∑ l : L, ∑ l' : L,
      c l * c l' * H k k' := by
        apply sum_congr rfl
        intro k hk
        exact sum_comm
    _ = ∑ k : K, ∑ k' : K, (∑ l : L, c l) ^ 2 * H k k' := by
        apply sum_congr rfl
        intro k hk
        apply sum_congr rfl
        intro k' hk'
        simp_rw [← sum_mul]
        rw [← Fintype.sum_mul_sum, ← pow_two]
    _ = _ := by
      simp_rw [← mul_sum]

theorem positive_geometric_sum_nonneg {q : ℝ} (hq : 0 ≤ q) (γ : ℕ) :
    0 ≤ ∑ j : Fin γ, 1 / q ^ (j.val + 1) := by
  exact sum_nonneg fun j hj => div_nonneg (by norm_num) (pow_nonneg hq _)

theorem positive_geometric_sum_le {q : ℝ} (hq : 2 ≤ q) (γ : ℕ) :
    (∑ j : Fin γ, 1 / q ^ (j.val + 1)) ≤ 1 / (q - 1) := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).mpr (by linarith)
  have hsum : (∑ j ∈ range γ, (q⁻¹) ^ j) ≤ 1 / (1 - q⁻¹) := by
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := γ) hr0 hr1
  rw [Fin.sum_univ_eq_sum_range (fun j => 1 / q ^ (j + 1))]
  simp_rw [one_div, ← inv_pow, pow_succ']
  rw [← mul_sum]
  have h := mul_le_mul_of_nonneg_left hsum hr0
  have heq : q⁻¹ * (1 / (1 - q⁻¹)) = 1 / (q - 1) := by field_simp
  rw [heq] at h
  simpa only [one_div] using h

/-- The complete finite coefficient cost of the divisor/exponent rectangle family. -/
theorem geometric_pair_sum_le {K : Type*} [Fintype K] {q C : ℝ}
    (hq : 2 ≤ q) (γ : ℕ) (H : K → K → ℝ)
    (hH : ∀ k k', 0 ≤ H k k')
    (hC : (∑ k, ∑ k', H k k') ≤ C) :
    (∑ i : K × Fin γ, ∑ j : K × Fin γ,
      (1 / q ^ (i.2.val + 1)) * (1 / q ^ (j.2.val + 1)) * H i.1 j.1) ≤
        C / (q - 1) ^ 2 := by
  have hs0 := positive_geometric_sum_nonneg (by linarith : 0 ≤ q) γ
  have hs := positive_geometric_sum_le hq γ
  have hs_sq := (sq_le_sq₀ hs0 (hs0.trans hs)).mpr hs
  have htotal0 : 0 ≤ ∑ k, ∑ k', H k k' :=
    sum_nonneg fun k hk => sum_nonneg fun k' hk' => hH k k'
  rw [ordered_pair_sum_factor (fun j : Fin γ => 1 / q ^ (j.val + 1)) H]
  calc
    _ ≤ (1 / (q - 1)) ^ 2 * C :=
      mul_le_mul hs_sq hC htotal0 (sq_nonneg _)
    _ = _ := by
      rw [div_pow, one_pow]
      ring

end Erdos2.Rectangles
