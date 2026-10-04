module

public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic


@[expose] public section

/-! Successor scalar proofs; predecessor source is kept unchanged while queued. -/

namespace Erdos546

/-- The finite remaining reciprocal budget supplies the reservoir invariant. -/
theorem finite_reciprocal_budget_tail (a : ℕ → ℝ) (hpos : ∀ i, 0 < a i)
    (hstart : 3 ≤ a 0) (hstep : ∀ i, (4 / 3 : ℝ) * a i ≤ a (i + 1))
    (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / a i) ≤ 4 / 3 - 4 * (1 / a n) := by
  induction n with
  | zero =>
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hstart
    simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  | succ n ih =>
    have hden : (0 : ℝ) < (4 / 3 : ℝ) * a n := mul_pos (by norm_num) (hpos n)
    have hnext : 1 / a (n + 1) ≤ (3 / 4 : ℝ) * (1 / a n) := by
      calc
        1 / a (n + 1) ≤ 1 / ((4 / 3 : ℝ) * a n) :=
          one_div_le_one_div_of_le hden (hstep n)
        _ = (3 / 4 : ℝ) * (1 / a n) := by field_simp
    rw [Finset.sum_range_succ]
    linarith

/-- The final integer parameter is half the natural binary logarithm. -/
def finalAmplificationParameter546 (m : ℕ) : ℕ := Nat.log2 m / 2

theorem finalAmplificationParameter546_lower (m : ℕ) (hm : m ≠ 0) :
    2 ^ (2 * finalAmplificationParameter546 m) ≤ m := by
  have hlog : 2 ^ Nat.log2 m ≤ m := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hm
  have hexp : 2 * finalAmplificationParameter546 m ≤ Nat.log2 m := by
    dsimp [finalAmplificationParameter546]
    omega
  exact (Nat.pow_le_pow_right (by omega : 0 < 2) hexp).trans hlog

theorem finalAmplificationParameter546_upper (m : ℕ) :
    m < 4 * 2 ^ (2 * finalAmplificationParameter546 m) := by
  have hlog : m < 2 ^ (Nat.log2 m + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by omega : 1 < 2) m
  have hexp : Nat.log2 m + 1 ≤ 2 * finalAmplificationParameter546 m + 2 := by
    dsimp [finalAmplificationParameter546]
    omega
  calc
    m < 2 ^ (Nat.log2 m + 1) := hlog
    _ ≤ 2 ^ (2 * finalAmplificationParameter546 m + 2) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hexp
    _ = 4 * 2 ^ (2 * finalAmplificationParameter546 m) := by
      rw [pow_add]
      norm_num
      ring

theorem finalAmplificationParameter546_ge_three (m : ℕ) (hm : 64 ≤ m) :
    3 ≤ finalAmplificationParameter546 m := by
  have hmzero : m ≠ 0 := by omega
  have hlog : 6 ≤ Nat.log2 m := by
    rw [Nat.log2_eq_log_two]
    apply (Nat.le_log_iff_pow_le (by omega : 1 < 2) hmzero).2
    norm_num
    exact hm
  dsimp [finalAmplificationParameter546]
  omega

theorem finalAmplificationParameter546_sqrt_lower (m : ℕ) (hm : m ≠ 0) :
    (2 : ℝ) ^ finalAmplificationParameter546 m ≤ Real.sqrt m := by
  have hpower : (2 : ℝ) ^ (2 * finalAmplificationParameter546 m) ≤ m := by
    exact_mod_cast finalAmplificationParameter546_lower m hm
  apply Real.le_sqrt_of_sq_le
  rw [← pow_mul, Nat.mul_comm (finalAmplificationParameter546 m) 2]
  exact hpower

theorem finalAmplificationParameter546_clique_size (m : ℕ) (hm : 64 ≤ m) :
    (2 : ℝ) ^ (2 * finalAmplificationParameter546 m) * Real.sqrt m ≥ 2 * m := by
  have hupper : (m : ℝ) < 4 * (2 : ℝ) ^ (2 * finalAmplificationParameter546 m) := by
    exact_mod_cast finalAmplificationParameter546_upper m
  have hsqrt : (8 : ℝ) ≤ Real.sqrt m := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hm
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * finalAmplificationParameter546 m) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsqrt hpow
  nlinarith

end Erdos546

#print axioms Erdos546.finite_reciprocal_budget_tail
#print axioms Erdos546.finalAmplificationParameter546_lower
#print axioms Erdos546.finalAmplificationParameter546_upper
#print axioms Erdos546.finalAmplificationParameter546_ge_three
#print axioms Erdos546.finalAmplificationParameter546_sqrt_lower
#print axioms Erdos546.finalAmplificationParameter546_clique_size
