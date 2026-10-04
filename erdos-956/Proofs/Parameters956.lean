module

public import Mathlib


@[expose] public section

/-!
# Rational grid parameters and spacing inequalities for Erdős #956

Defines the scale parameters `W(k) = 1 / (10k)`, `a(k) = W(k) / k`,
`b(k) = a(k)^2 / 2`, and `η(k) = W(k)^4`, and proves the strict separation
bounds `W^3 / 2 < a`, `η < b`, and `k^2 b < 1`.
-/

namespace Erdos956.Parameters

noncomputable def W (k : ℕ) : ℝ := (1 / 10 : ℝ) / k
noncomputable def a (k : ℕ) : ℝ := W k / k
noncomputable def b (k : ℕ) : ℝ := (a k) ^ 2 / 2
noncomputable def eta (k : ℕ) : ℝ := (W k) ^ 4

/-- Signed parameter set `{i * a k : -k ≤ i ≤ k}` for the signed parabolic cap. -/
noncomputable def signedT (k : ℕ) : Finset ℝ :=
  (Finset.Icc (-(k : ℤ)) (k : ℤ)).image (fun i : ℤ => (i : ℝ) * a k)

theorem k_real_pos (k : ℕ) (hk : 1 ≤ k) : (0 : ℝ) < k := by
  exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hk)

theorem k_real_ne_zero (k : ℕ) (hk : 1 ≤ k) : (k : ℝ) ≠ 0 :=
  ne_of_gt (k_real_pos k hk)

theorem W_formula (k : ℕ) (_hk : 1 ≤ k) :
    W k = 1 / (10 * (k : ℝ)) := by
  unfold W
  ring

theorem a_formula (k : ℕ) (hk : 1 ≤ k) :
    a k = 1 / (10 * (k : ℝ) ^ 2) := by
  rw [a, W_formula k hk]
  ring

theorem b_formula (k : ℕ) (hk : 1 ≤ k) :
    b k = 1 / (200 * (k : ℝ) ^ 4) := by
  rw [b, a_formula k hk]
  ring

theorem eta_formula (k : ℕ) (hk : 1 ≤ k) :
    eta k = 1 / (10000 * (k : ℝ) ^ 4) := by
  rw [eta, W_formula k hk]
  ring

theorem W_pos (k : ℕ) (hk : 1 ≤ k) : 0 < W k := by
  rw [W_formula k hk]
  positivity

theorem W_le_one (k : ℕ) (hk : 1 ≤ k) : W k ≤ 1 := by
  rw [W_formula k hk]
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 10 * k := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

theorem a_pos (k : ℕ) (hk : 1 ≤ k) : 0 < a k := by
  rw [a_formula k hk]
  positivity

theorem b_pos (k : ℕ) (hk : 1 ≤ k) : 0 < b k := by
  rw [b_formula k hk]
  positivity

theorem eta_pos (k : ℕ) (hk : 1 ≤ k) : 0 < eta k := by
  rw [eta_formula k hk]
  positivity

theorem cap_width_lt_a (k : ℕ) (hk : 1 ≤ k) :
    (W k) ^ 3 / 2 < a k := by
  rw [W_formula k hk, a_formula k hk]
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := k_real_pos k hk
  have hden : (0 : ℝ) < 2000 * k ^ 3 := by positivity
  have hden2 : (0 : ℝ) < 10 * k ^ 2 := by positivity
  have hleft : (1 / (10 * (k : ℝ))) ^ 3 / 2 =
      1 / (2000 * (k : ℝ) ^ 3) := by
    field_simp [k_real_ne_zero k hk]; ring
  rw [hleft]
  apply (one_div_lt_one_div hden hden2).2
  nlinarith [sq_nonneg (k - 1)]

theorem eta_lt_b (k : ℕ) (hk : 1 ≤ k) : eta k < b k := by
  rw [eta_formula k hk, b_formula k hk]
  have hkp : (0 : ℝ) < k := k_real_pos k hk
  have hden : (0 : ℝ) < 10000 * k ^ 4 := by positivity
  have hden2 : (0 : ℝ) < 200 * k ^ 4 := by positivity
  apply (one_div_lt_one_div hden hden2).2
  nlinarith [pow_pos hkp 4]

theorem grid_height_lt_one (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ 2 * b k < 1 := by
  rw [b_formula k hk]
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := k_real_pos k hk
  have hrewrite : (k : ℝ) ^ 2 * (1 / (200 * k ^ 4)) =
      1 / (200 * k ^ 2) := by
    field_simp [ne_of_gt hkp]
  rw [hrewrite]
  have hden : (0 : ℝ) < 200 * k ^ 2 := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem mem_signedT_range (k : ℕ) (hk : 1 ≤ k) {t : ℝ} (ht : t ∈ signedT k) :
    -W k ≤ t ∧ t ≤ W k := by
  rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
  rcases Finset.mem_Icc.mp hi with ⟨hlow, hhigh⟩
  have hilow : -(k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hlow
  have hihigh : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hhigh
  have ha := (a_pos k hk).le
  have hW : (k : ℝ) * a k = W k := by
    rw [a]
    field_simp [k_real_ne_zero k hk]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hilow ha
    linarith
  · have hmul := mul_le_mul_of_nonneg_right hihigh ha
    linarith

theorem int_step_mem_signedT (k : ℕ) (i : ℤ)
    (hlow : -(k : ℤ) ≤ i) (hhigh : i ≤ (k : ℤ)) :
    (i : ℝ) * a k ∈ signedT k := by
  unfold signedT
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_Icc.mpr ⟨hlow, hhigh⟩, rfl⟩

end Erdos956.Parameters
