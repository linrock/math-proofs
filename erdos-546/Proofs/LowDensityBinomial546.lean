module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic


@[expose] public section

/-!
# The binomial estimate for Sudakov's low-density pair argument

The effective factorial lower bound already proved in Mathlib gives the
usual `(e*n/r)^r` estimate, including explicit treatment of `r = 0`.
-/

namespace Erdos546

theorem choose_le_exp_mul_div_pow (n r : ℕ) (hr : 0 < r) :
    (n.choose r : ℝ) ≤ (Real.exp 1 * n / r) ^ r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hroot : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * r) := by
    apply Real.one_le_sqrt.mpr
    have hpi := Real.pi_gt_three
    have hprod : 3 * (r : ℝ) ≤ Real.pi * r :=
      mul_le_mul_of_nonneg_right (by linarith) hrR.le
    nlinarith
  have hfactorial : ((r : ℝ) / Real.exp 1) ^ r ≤ (r.factorial : ℝ) := by
    calc
      ((r : ℝ) / Real.exp 1) ^ r = 1 * ((r : ℝ) / Real.exp 1) ^ r := by ring
      _ ≤ Real.sqrt (2 * Real.pi * r) * ((r : ℝ) / Real.exp 1) ^ r :=
        mul_le_mul_of_nonneg_right hroot (by positivity)
      _ ≤ (r.factorial : ℝ) := Stirling.le_factorial_stirling r
  have hden : (0 : ℝ) < ((r : ℝ) / Real.exp 1) ^ r := by positivity
  calc
    (n.choose r : ℝ) ≤ (n : ℝ) ^ r / (r.factorial : ℝ) := Nat.choose_le_pow_div r n
    _ ≤ (n : ℝ) ^ r / (((r : ℝ) / Real.exp 1) ^ r) :=
      div_le_div_of_nonneg_left (by positivity) hden hfactorial
    _ = (Real.exp 1 * n / r) ^ r := by
      rw [← div_pow]
      congr 1
      field_simp [hrR.ne']

/-- The scaled form used in the mask pigeonhole and the red pair recurrence. -/
theorem choose_mul_pow_le_one (n r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hscale : Real.exp 1 * n * ε ≤ r) :
    (n.choose r : ℝ) * ε ^ r ≤ 1 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hratio : Real.exp 1 * n / r * ε ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hrR).mpr
    simpa using hscale
  calc
    (n.choose r : ℝ) * ε ^ r ≤ (Real.exp 1 * n / r) ^ r * ε ^ r :=
      mul_le_mul_of_nonneg_right (choose_le_exp_mul_div_pow n r hrpos) (by positivity)
    _ = (Real.exp 1 * n / r * ε) ^ r := (mul_pow _ _ _).symm
    _ ≤ 1 ^ r := pow_le_pow_left₀ (by positivity) hratio r
    _ = 1 := by simp

/-- A convenient rational slack: the paper's coefficient `3` exceeds `e`. -/
theorem choose_mul_pow_le_one_of_three_mul (n r : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hscale : 3 * ε * n ≤ r) :
    (n.choose r : ℝ) * ε ^ r ≤ 1 := by
  apply choose_mul_pow_le_one n r ε hε
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_right he (show 0 ≤ ε * n by positivity)
  nlinarith

end Erdos546
