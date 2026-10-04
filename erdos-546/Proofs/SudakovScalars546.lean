module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic


@[expose] public section

/-!
# Scalar inequalities for Sudakov's sparse Ramsey argument

Establishes the real and natural-number inequalities used across the greedy
embedding, sparse-cut extraction, and amplification schedule.
-/

namespace Erdos546

theorem nat_two_pow_ge_succ (r : ℕ) : r + 1 ≤ 2 ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [pow_succ]
    omega

theorem half_pow_budget (r : ℕ) :
    ((r : ℝ) + 1) * (1 / 2 : ℝ) ^ r ≤ 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ r := pow_nonneg (by norm_num) r
    simp only [Nat.cast_succ, pow_succ]
    nlinarith

theorem small_pow_budget (ε : ℝ) (hε : 0 ≤ ε) (hhalf : ε ≤ 1 / 2) (r : ℕ) :
    ((r : ℝ) + 1) * ε ^ r ≤ 1 := by
  calc
    ((r : ℝ) + 1) * ε ^ r ≤ ((r : ℝ) + 1) * (1 / 2 : ℝ) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε hhalf r) (by positivity)
    _ ≤ 1 := half_pow_budget r

/-- The unused degree budget supplies enough candidates to avoid every bad set. -/
theorem embedding_power_margin (ε : ℝ) (hε : 0 ≤ ε) (hhalf : ε ≤ 1 / 2)
    (D r : ℕ) (hr : r ≤ D) :
    ε ^ D ≤ ε ^ (D - r) - (r : ℝ) * ε ^ D := by
  have hbudget := small_pow_budget ε hε hhalf r
  have hnonneg : 0 ≤ ε ^ (D - r) := pow_nonneg hε _
  have hmul := mul_le_mul_of_nonneg_left hbudget hnonneg
  have hpower : ε ^ D = ε ^ (D - r) * ε ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  rw [hpower]
  nlinarith

theorem embedding_candidate_budget (ε q n : ℝ) (hε : 0 ≤ ε)
    (hhalf : ε ≤ 1 / 2) (hq : 0 ≤ q) (D r : ℕ) (hr : r ≤ D)
    (hn : n ≤ ε ^ D * q) :
    n ≤ (ε ^ (D - r) - (r : ℝ) * ε ^ D) * q := by
  exact hn.trans (mul_le_mul_of_nonneg_right
    (embedding_power_margin ε hε hhalf D r hr) hq)

/-- Strict rounding slack: a real candidate bound above `n-1` suffices. -/
theorem embedding_candidate_budget_rounded (ε q qstar n : ℝ)
    (hε : 0 ≤ ε) (hhalf : ε ≤ 1 / 2) (hqstar : 0 ≤ qstar)
    (hround : qstar - 1 < q) (D r : ℕ) (hr : r ≤ D)
    (hn : n ≤ ε ^ D * qstar) (hpow : 0 < ε ^ (D - r)) :
    n - 1 < ε ^ (D - r) * q - (r : ℝ) * ε ^ D * qstar := by
  have hεone : ε ≤ 1 := by linarith
  have hleone : ε ^ (D - r) ≤ 1 := pow_le_one₀ hε hεone
  have hmargin := embedding_candidate_budget ε qstar n hε hhalf hqstar D r hr hn
  have hstrict := mul_lt_mul_of_pos_left hround hpow
  nlinarith

theorem embedding_candidate_budget_rounded_general (ε q qstar n : ℝ)
    (hε : 0 < ε) (hhalf : ε ≤ 1 / 2) (hqstar : 0 ≤ qstar) (hq : 0 ≤ q)
    (hround : qstar - 1 < q) (D b r : ℕ) (hdegree : b + r ≤ D)
    (hn : n ≤ ε ^ D * qstar) :
    n - 1 < ε ^ b * q - (r : ℝ) * ε ^ D * qstar := by
  have hr : r ≤ D := by omega
  have hb : b ≤ D - r := by omega
  have hεone : ε ≤ 1 := by linarith
  have h := embedding_candidate_budget_rounded ε q qstar n hε.le hhalf
    hqstar hround D r hr hn (pow_pos hε _)
  have hp := pow_le_pow_of_le_one hε.le hεone hb
  have hmul := mul_le_mul_of_nonneg_right hp hq
  linarith

theorem nat_sparse_loss_bound_index (k : ℕ) :
    8 * (k + 3) ^ 2 ≤ 9 * 2 ^ (k + 3) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpoly : (k + 4) ^ 2 ≤ 2 * (k + 3) ^ 2 := by
      exact_mod_cast (show ((k : ℝ) + 4) ^ 2 ≤ 2 * ((k : ℝ) + 3) ^ 2 by
        nlinarith [sq_nonneg (k : ℝ), show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
    calc
      8 * (k + 1 + 3) ^ 2 = 8 * (k + 4) ^ 2 := by congr 2
      _ ≤ 16 * (k + 3) ^ 2 := by nlinarith
      _ ≤ 18 * 2 ^ (k + 3) := by nlinarith
      _ = 9 * 2 ^ (k + 1 + 3) := by
        rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
        ring

theorem nat_sparse_loss_bound (a : ℕ) (ha : 3 ≤ a) :
    8 * a ^ 2 ≤ 9 * 2 ^ a := by
  have h := nat_sparse_loss_bound_index (a - 3)
  simpa [Nat.sub_add_cancel ha] using h

theorem nat_cube_growth_step (a : ℕ) (ha : 2 ≤ a) :
    (a + 1) ^ 3 ≤ 4 * a ^ 3 := by
  have hsq : 2 * a ≤ a * a := Nat.mul_le_mul_right a ha
  have hcube : 2 * (a * a) ≤ a * (a * a) := Nat.mul_le_mul_right (a * a) ha
  nlinarith

theorem nat_amplification_growth_index (k : ℕ) :
    64 * (k + 3) ^ 3 ≤ 27 * 2 ^ (2 * (k + 3)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpoly := nat_cube_growth_step (k + 3) (by omega)
    calc
      64 * (k + 1 + 3) ^ 3 = 64 * (k + 3 + 1) ^ 3 := by congr 2
      _ ≤ 256 * (k + 3) ^ 3 := by nlinarith
      _ ≤ 108 * 2 ^ (2 * (k + 3)) := by nlinarith
      _ = 27 * 2 ^ (2 * (k + 1 + 3)) := by
        rw [show 2 * (k + 1 + 3) = 2 * (k + 3) + 2 by omega, pow_add]
        norm_num
        ring

theorem nat_amplification_growth (a : ℕ) (ha : 3 ≤ a) :
    64 * a ^ 3 ≤ 27 * 2 ^ (2 * a) := by
  have h := nat_amplification_growth_index (a - 3)
  simpa [Nat.sub_add_cancel ha] using h

theorem integer_amplification_growth (a : ℕ) (ha : 3 ≤ a) :
    ((4 / 3 : ℝ) * a) ^ 3 ≤ (2 : ℝ) ^ (2 * a) := by
  have h : (64 : ℝ) * (a : ℝ) ^ 3 ≤ 27 * (2 : ℝ) ^ (2 * a) := by
    exact_mod_cast nat_amplification_growth a ha
  nlinarith

/-- An integer geometric schedule removes cube roots and iteration rounding. -/
def nextAmplificationParameter546 (a : ℕ) : ℕ := (4 * a + 2) / 3

theorem nextAmplificationParameter546_ge (a : ℕ) :
    (4 / 3 : ℝ) * a ≤ nextAmplificationParameter546 a := by
  have h : 4 * a ≤ 3 * ((4 * a + 2) / 3) := by omega
  have hreal : (4 : ℝ) * a ≤ 3 * (nextAmplificationParameter546 a : ℝ) := by
    exact_mod_cast h
  linarith

theorem nat_cube_growth_two_step (a : ℕ) (ha : 4 ≤ a) :
    (a + 2) ^ 3 ≤ 4 * a ^ 3 := by
  have hsq : 4 * a ≤ a * a := Nat.mul_le_mul_right a ha
  have hcube : 4 * (a * a) ≤ a * (a * a) := Nat.mul_le_mul_right (a * a) ha
  nlinarith

theorem nat_rounded_amplification_growth_index (k : ℕ) :
    nextAmplificationParameter546 (k + 3) ^ 3 ≤ 2 ^ (2 * (k + 3)) := by
  induction k with
  | zero => norm_num [nextAmplificationParameter546]
  | succ k ih =>
    have hbase : 4 ≤ nextAmplificationParameter546 (k + 3) := by
      dsimp [nextAmplificationParameter546]
      omega
    have hnext : nextAmplificationParameter546 (k + 1 + 3) ≤
        nextAmplificationParameter546 (k + 3) + 2 := by
      dsimp [nextAmplificationParameter546]
      omega
    have hpoly := nat_cube_growth_two_step _ hbase
    calc
      nextAmplificationParameter546 (k + 1 + 3) ^ 3 ≤
          (nextAmplificationParameter546 (k + 3) + 2) ^ 3 :=
        Nat.pow_le_pow_left hnext 3
      _ ≤ 4 * nextAmplificationParameter546 (k + 3) ^ 3 := hpoly
      _ ≤ 4 * 2 ^ (2 * (k + 3)) := Nat.mul_le_mul_left 4 ih
      _ = 2 ^ (2 * (k + 1 + 3)) := by
        rw [show 2 * (k + 1 + 3) = 2 * (k + 3) + 2 by omega, pow_add]
        norm_num
        ring

theorem nat_rounded_amplification_growth (a : ℕ) (ha : 3 ≤ a) :
    nextAmplificationParameter546 a ^ 3 ≤ 2 ^ (2 * a) := by
  have h := nat_rounded_amplification_growth_index (a - 3)
  simpa [Nat.sub_add_cancel ha] using h

theorem geometric_reciprocal_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 3 : ℝ) * (3 / 4 : ℝ) ^ i) =
      (4 / 3 : ℝ) * (1 - (3 / 4 : ℝ) ^ n) := by
  have h := geom_sum_mul_neg (3 / 4 : ℝ) n
  rw [← Finset.mul_sum]
  nlinarith

theorem geometric_reciprocal_budget (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 3 : ℝ) * (3 / 4 : ℝ) ^ i) ≤ 4 / 3 := by
  rw [geometric_reciprocal_sum]
  have h : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ n := pow_nonneg (by norm_num) n
  nlinarith

theorem reciprocal_growth_control (a : ℕ → ℝ) (hpos : ∀ i, 0 < a i)
    (hstart : 3 ≤ a 0) (hstep : ∀ i, (4 / 3 : ℝ) * a i ≤ a (i + 1))
    (i : ℕ) :
    1 / a i ≤ (1 / 3 : ℝ) * (3 / 4 : ℝ) ^ i := by
  induction i with
  | zero =>
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hstart
  | succ i ih =>
    have hden : (0 : ℝ) < (4 / 3 : ℝ) * a i := mul_pos (by norm_num) (hpos i)
    calc
      1 / a (i + 1) ≤ 1 / ((4 / 3 : ℝ) * a i) :=
        one_div_le_one_div_of_le hden (hstep i)
      _ = (3 / 4 : ℝ) * (1 / a i) := by field_simp
      _ ≤ (3 / 4 : ℝ) * ((1 / 3 : ℝ) * (3 / 4 : ℝ) ^ i) := by
        exact mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1 / 3 : ℝ) * (3 / 4 : ℝ) ^ (i + 1) := by rw [pow_succ]; ring

theorem finite_reciprocal_budget (a : ℕ → ℝ) (hpos : ∀ i, 0 < a i)
    (hstart : 3 ≤ a 0) (hstep : ∀ i, (4 / 3 : ℝ) * a i ≤ a (i + 1))
    (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / a i) ≤ 4 / 3 := by
  calc
    (∑ i ∈ Finset.range n, 1 / a i) ≤
        ∑ i ∈ Finset.range n, (1 / 3 : ℝ) * (3 / 4 : ℝ) ^ i := by
      exact Finset.sum_le_sum fun i _ => reciprocal_growth_control a hpos hstart hstep i
    _ ≤ 4 / 3 := geometric_reciprocal_budget n

end Erdos546
