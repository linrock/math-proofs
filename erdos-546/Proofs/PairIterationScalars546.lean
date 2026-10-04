module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic


@[expose] public section

/-!
# Potential-function inequalities for the amplification schedule

Establishes the finite stopping lemma and the geometric potential drop for
reservoir sizes across amplification steps.
-/

namespace Erdos546

/-- Any property that advances along a strictly increasing natural schedule
reaches a prescribed finite stopping parameter. -/
theorem exists_terminal_parameter (A : ℕ) (P : ℕ → Prop) (next : ℕ → ℕ)
    (hstart : P 3)
    (hnext : ∀ a, 3 ≤ a → a < next a)
    (hstep : ∀ a, 3 ≤ a → a < A → P a → P (next a)) :
    ∃ a, 3 ≤ a ∧ A ≤ a ∧ P a := by
  have hmain : ∀ d a, A - a = d → 3 ≤ a → P a →
      ∃ b, 3 ≤ b ∧ A ≤ b ∧ P b := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a hd ha hp
      by_cases hAa : A ≤ a
      · exact ⟨a, ha, hAa, hp⟩
      · have haA : a < A := by omega
        have hab := hnext a ha
        have hb : 3 ≤ next a := by omega
        have hdiff : A - next a < d := by omega
        exact ih (A - next a) hdiff (next a) rfl hb (hstep a ha haA hp)
  exact hmain (A - 3) 3 rfl (by omega) hstart

/-- The remaining reciprocal budget pays for one amplification step.
The multiplicative loss is at most `2^(-L*s/a)`. -/
theorem reservoir_potential_drop (B L s a b : ℝ)
    (hL : 0 ≤ L) (hs : 0 ≤ s) (ha : 0 < a)
    (hstep : (4 / 3 : ℝ) * a ≤ b) :
    (2 : ℝ) ^ (B * s + 4 * L * s / b) ≤
      2 ^ (B * s + 4 * L * s / a) * 2 ^ (-L * s / a) := by
  have hden : (0 : ℝ) < (4 / 3 : ℝ) * a := mul_pos (by norm_num) ha
  have hinv : 1 / b ≤ (3 / 4 : ℝ) * (1 / a) := by
    calc
      1 / b ≤ 1 / ((4 / 3 : ℝ) * a) :=
        one_div_le_one_div_of_le hden hstep
      _ = (3 / 4 : ℝ) * (1 / a) := by field_simp
  have hmul := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ 4 * L * s from mul_nonneg (mul_nonneg (by norm_num) hL) hs)
  have hexp : B * s + 4 * L * s / b ≤
      (B * s + 4 * L * s / a) + (-L * s / a) := by
    simp only [div_eq_mul_inv] at hmul ⊢
    nlinarith
  calc
    (2 : ℝ) ^ (B * s + 4 * L * s / b) ≤
        2 ^ ((B * s + 4 * L * s / a) + (-L * s / a)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = _ := Real.rpow_add (by norm_num) _ _

/-- A reservoir satisfying the potential is large enough to apply a step
whose prerequisite is `2^(B*s/a)`, for parameters at least one. -/
theorem reservoir_threshold_of_potential (B L s a : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hs : 0 ≤ s) (ha : 1 ≤ a) :
    (2 : ℝ) ^ (B * s / a) ≤ 2 ^ (B * s + 4 * L * s / a) := by
  have hbase : B * s / a ≤ B * s := div_le_self (mul_nonneg hB hs) ha
  have hrest : 0 ≤ 4 * L * s / a := by positivity
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem reservoir_initial_potential (B L s : ℝ) :
    (2 : ℝ) ^ ((B + 4 * L / 3) * s) = 2 ^ (B * s + 4 * L * s / 3) := by
  congr 1
  ring

end Erdos546
