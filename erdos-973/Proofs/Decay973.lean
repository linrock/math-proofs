module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


@[expose] public section

/-!
# Exponential decay dominates the fixed polynomial losses

These purely numerical estimates supply the eventual inequalities used when
the original power sums are assumed bounded by `C^(-n)` for a fixed `C > 1`.
-/

open scoped Topology
open Filter

namespace Erdos973.Decay

theorem delta_pos (C : ℝ) (hC : 1 < C) : 0 < Real.log C / 4 := by
  exact div_pos (Real.log_pos hC) (by norm_num)

theorem rpow_neg_nat_eq_inv_pow (C : ℝ) (n : ℕ) :
    C ^ (-(n : ℝ)) = (C⁻¹) ^ n := by
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

theorem tendsto_shifted_pow_mul_geometric (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (k : ℕ) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ k * r ^ n) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one k hr.le hr1).comp
    (tendsto_add_atTop_nat 1)).div_const r
  convert ht using 1
  · funext n
    simp [Nat.cast_add, Nat.cast_one, pow_succ, ← mul_assoc, ne_of_gt hr]
  · simp

theorem separation_geometric_identity (C : ℝ) (n : ℕ) :
    Real.exp ((2 * (n : ℝ)) * (Real.log C / 4)) * C ^ (-(n : ℝ)) =
      (Real.exp (2 * (Real.log C / 4)) * C⁻¹) ^ n := by
  rw [rpow_neg_nat_eq_inv_pow, mul_pow,
    show (2 * (n : ℝ)) * (Real.log C / 4) = (n : ℝ) * (2 * (Real.log C / 4)) by ring,
    Real.exp_nat_mul]

theorem separation_ratio_lt_one (C : ℝ) (hC : 1 < C) :
    Real.exp (2 * (Real.log C / 4)) * C⁻¹ < 1 := by
  have hC0 : 0 < C := lt_trans zero_lt_one hC
  rw [← div_eq_mul_inv, div_lt_one hC0]
  calc
    Real.exp (2 * (Real.log C / 4)) < Real.exp (Real.log C) :=
      Real.exp_lt_exp.mpr (by linarith [Real.log_pos hC])
    _ = C := Real.exp_log hC0

theorem eventually_numeric_conditions (C : ℝ) (hC : 1 < C) (K : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ C ^ (-(n : ℝ)) ≤ 1 ∧
      (Real.log C / 4) * Real.exp ((2 * (n : ℝ)) * (Real.log C / 4)) *
        ((n + 1 : ℝ) * ((n : ℝ) * C ^ (-(n : ℝ)))) < 1 ∧
      C ^ (-(n : ℝ)) * (2 : ℝ) ^ (K - 1) *
        (n + 1 : ℝ) ^ (2 * K - 1) < η := by
  have hC0 : 0 < C := lt_trans zero_lt_one hC
  let r : ℝ := C⁻¹
  let q : ℝ := Real.exp (2 * (Real.log C / 4)) * C⁻¹
  have hr : 0 < r := inv_pos.mpr hC0
  have hr1 : r < 1 := (inv_lt_one₀ hC0).2 hC
  have hq : 0 < q := mul_pos (Real.exp_pos _) (inv_pos.mpr hC0)
  have hq1 : q < 1 := separation_ratio_lt_one C hC
  have hδ : 0 < Real.log C / 4 := delta_pos C hC
  have htsep : Tendsto (fun n : ℕ => (Real.log C / 4) * ((n + 1 : ℝ) ^ 2 * q ^ n))
      atTop (𝓝 0) := by
    simpa using (tendsto_shifted_pow_mul_geometric q hq hq1 2).const_mul (Real.log C / 4)
  have htmom : Tendsto (fun n : ℕ => (2 : ℝ) ^ (K - 1) *
      ((n + 1 : ℝ) ^ (2 * K - 1) * r ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_shifted_pow_mul_geometric r hr hr1 (2 * K - 1)).const_mul
      ((2 : ℝ) ^ (K - 1))
  have hesep := htsep.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hemom := htmom.eventually (gt_mem_nhds hη)
  filter_upwards [eventually_gt_atTop 0, hesep, hemom] with n hn hs hm
  refine ⟨hn, ?_, ?_, ?_⟩
  · rw [rpow_neg_nat_eq_inv_pow]
    exact pow_le_one₀ hr.le hr1.le
  · apply lt_of_le_of_lt ?_ hs
    have hpoly : (n : ℝ) * (n + 1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hid := separation_geometric_identity C n
    change _ = q ^ n at hid
    calc
      (Real.log C / 4) * Real.exp ((2 * (n : ℝ)) * (Real.log C / 4)) *
          ((n + 1 : ℝ) * ((n : ℝ) * C ^ (-(n : ℝ)))) =
          (Real.log C / 4) * ((n : ℝ) * (n + 1 : ℝ)) * q ^ n := by rw [← hid]; ring
      _ ≤ (Real.log C / 4) * ((n + 1 : ℝ) ^ 2 * q ^ n) := by
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hδ.le)
          (pow_nonneg hq.le n)).trans_eq (by ring)
  · simpa only [rpow_neg_nat_eq_inv_pow, r, mul_comm, mul_left_comm, mul_assoc] using hm

end Erdos973.Decay
