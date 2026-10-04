module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic


@[expose] public section

/-!
Coarse amplification exponent budgets. The hypotheses expose the checked
natural-log and degree-deletion inequalities, so this module imports only
Mathlib and can be checked independently of the graph machinery.
-/

namespace Erdos546

theorem nat_ceil_le_two_mul_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    (Nat.ceil x : ℝ) ≤ 2 * x := by
  have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
  linarith

/-- The two natural ceiling estimates lose a factor of four in `u`. -/
theorem rounded_sparse_parameter_bound (a : ℕ) (s t u : ℝ)
    (ht : t ≤ 2 * (2 : ℝ) ^ (2 * a) * s)
    (hu : u ≤ 2 * t / (2 : ℝ) ^ (3 * a)) :
    u ≤ 4 * s / (2 : ℝ) ^ a := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ (2 * a) := by positivity
  have hp3 : (0 : ℝ) < (2 : ℝ) ^ (3 * a) := by positivity
  have hu' := (le_div_iff₀ hp3).mp hu
  have hsplit : (2 : ℝ) ^ (3 * a) = (2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ a := by
    rw [show 3 * a = 2 * a + a by omega, pow_add]
  rw [hsplit] at hu'
  apply (le_div_iff₀ hp).2
  apply (mul_le_mul_iff_left₀ hp2).mp
  nlinarith only [ht, hu']

theorem amplification_epsilon_bound (a : ℕ) (ha : 1 ≤ a) :
    0 < 1 / (2 : ℝ) ^ (3 * a) ∧ 1 / (2 : ℝ) ^ (3 * a) ≤ 1 / 8 := by
  have hN : 8 ≤ 2 ^ (3 * a) := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * a) := Nat.pow_le_pow_right (by omega) (by omega)
  have hR : (8 : ℝ) ≤ (2 : ℝ) ^ (3 * a) := by exact_mod_cast hN
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hR⟩

theorem amplification_sparse_scale_ge_one (a : ℕ) (s : ℝ)
    (hs : (2 : ℝ) ^ a ≤ s) :
    1 ≤ (1 / (2 : ℝ) ^ (3 * a)) * ((2 : ℝ) ^ (2 * a) * s) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hsplit : (2 : ℝ) ^ (3 * a) = (2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ a := by
    rw [show 3 * a = 2 * a + a by omega, pow_add]
  have he : (1 / (2 : ℝ) ^ (3 * a)) * ((2 : ℝ) ^ (2 * a) * s) =
      s / (2 : ℝ) ^ a := by
    rw [hsplit]
    field_simp
  rw [he]
  apply (le_div_iff₀ hp).2
  simpa using hs

theorem nat_twice_size_log_threshold_bound (m A : ℕ)
    (hm : m < 4 * 2 ^ (2 * A)) :
    2 * m < 2 ^ (2 * A + 3) := by
  calc
    2 * m < 2 * (4 * 2 ^ (2 * A)) := Nat.mul_lt_mul_of_pos_left hm (by omega)
    _ = 2 ^ (2 * A + 3) := by rw [pow_add]; norm_num; ring

/-- The complete-graph Ramsey input fits the amplification exponent budget. -/
theorem ramsey_vertex_exponent_bound (m a A : ℕ)
    (ha : 3 ≤ a) (haA : a ≤ A)
    (hupper : (2 : ℝ) * m < (2 : ℝ) ^ (2 * A + 3))
    (hquad : (8 : ℝ) * (A : ℝ) ^ 2 ≤ 9 * (2 : ℝ) ^ A)
    (hsqrt : (2 : ℝ) ^ A ≤ Real.sqrt m) :
    (2 : ℝ) * m ≤ Real.rpow 2 (4 * Real.sqrt m / a) := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hA : (3 : ℝ) ≤ A := by exact_mod_cast (show 3 ≤ A by omega)
  have haA' : (a : ℝ) ≤ A := by exact_mod_cast haA
  have hs : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hfirst := mul_le_mul_of_nonneg_right haA'
    (show (0 : ℝ) ≤ 2 * (A : ℝ) + 3 by positivity)
  have hsecond : (A : ℝ) * (2 * A + 3) ≤ 3 * (A : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((A : ℝ) - 3)]
  have hp := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 9)
  have hexponent : ((2 * A + 3 : ℕ) : ℝ) ≤ 4 * Real.sqrt m / a := by
    apply (le_div_iff₀ hapos).2
    push_cast
    nlinarith
  calc
    (2 : ℝ) * m ≤ (2 : ℝ) ^ (2 * A + 3) := hupper.le
    _ = Real.rpow 2 ((2 * A + 3 : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
    _ ≤ Real.rpow 2 (4 * Real.sqrt m / a) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

theorem nat_extraction_ratio_bound (a D : ℕ) (hD : D + 1 ≤ 2 ^ D) :
    2 * (D + 1) * 2 ^ ((3 * a + 3) * D) ≤ 2 ^ (1 + (3 * a + 4) * D) := by
  calc
    2 * (D + 1) * 2 ^ ((3 * a + 3) * D) ≤
        2 * 2 ^ D * 2 ^ ((3 * a + 3) * D) := by gcongr
    _ = 2 ^ (1 + (3 * a + 4) * D) := by
      rw [show 1 + (3 * a + 4) * D = 1 + D + (3 * a + 3) * D by ring]
      rw [pow_add, pow_add]
      norm_num

theorem extraction_inverse_exact (a D : ℕ) :
    ((1 / (2 : ℝ) ^ (3 * a)) / 8) ^ D *
        (2 * (D + 1 : ℝ) * (2 : ℝ) ^ ((3 * a + 3) * D)) =
      2 * (D + 1 : ℝ) := by
  have he : (1 / (2 : ℝ) ^ (3 * a)) / 8 = 1 / (2 : ℝ) ^ (3 * a + 3) := by
    norm_num [pow_add, div_div]
    ring
  rw [he, one_div_pow, ← pow_mul]
  field_simp

theorem extraction_depth_bound (a : ℕ) :
    1 / (2 : ℝ) ^ (3 * a + 2) ≤ (1 / (2 : ℝ) ^ (3 * a)) / 2 := by
  rw [pow_add]
  norm_num
  have hp : (0 : ℝ) < (2 : ℝ) ^ (3 * a) := by positivity
  field_simp; nlinarith [hp]

theorem amplification_target_prefactor_bound (a : ℕ) (s : ℝ)
    (ha : 3 ≤ a) (hquad : (8 : ℝ) * (a : ℝ) ^ 2 ≤ 9 * s) :
    2 * (a : ℝ) + 1 ≤ 3 * s / a := by
  have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := by linarith
  apply (le_div_iff₀ hapos).2
  nlinarith [sq_nonneg ((a : ℝ) - 3)]

/-- The two cleanings and depth `3a+2` cost at most `50 sqrt(m)/a`. -/
theorem sparse_extraction_exponent_bound (a D : ℕ) (s : ℝ)
    (ha : 3 ≤ a)
    (hquad : (8 : ℝ) * (a : ℝ) ^ 2 ≤ 9 * s)
    (hdegree : (a : ℝ) ^ 3 * D ≤ 2 * s) :
    ((3 * a + 2 : ℕ) : ℝ) * (2 + (3 * (a : ℝ) + 4) * D) + 1 ≤
      50 * s / a := by
  have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℝ) < a := by linarith
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hcoeff : 9 * (a : ℝ) ^ 2 + 18 * a + 8 ≤ 16 * (a : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - 3)]
  have hmul := mul_le_mul_of_nonneg_right hcoeff hD
  have hmul' := mul_le_mul_of_nonneg_left hmul hapos.le
  have hsmall : (a : ℝ) * (6 * a + 5) ≤ 18 * s := by nlinarith
  apply (le_div_iff₀ hapos).2
  push_cast
  nlinarith

/-- After two ceiling losses, the rounded low-density exponent is bounded. -/
theorem low_density_rounding_loss_bound (a : ℕ) (s u : ℝ)
    (ha : 3 ≤ a) (hu : 0 ≤ u)
    (hquad : (8 : ℝ) * (a : ℝ) ^ 2 ≤ 9 * (2 : ℝ) ^ a)
    (hupper : u ≤ 4 * s / (2 : ℝ) ^ a) :
    60 * a * u ≤ 270 * s / a := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hp : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hu' := (le_div_iff₀ hp).mp hupper
  have hquad' := mul_le_mul_of_nonneg_right hquad hu
  apply (le_div_iff₀ hapos).2
  nlinarith

end Erdos546

#print axioms Erdos546.nat_twice_size_log_threshold_bound
#print axioms Erdos546.nat_ceil_le_two_mul_of_one_le
#print axioms Erdos546.rounded_sparse_parameter_bound
#print axioms Erdos546.amplification_epsilon_bound
#print axioms Erdos546.amplification_sparse_scale_ge_one
#print axioms Erdos546.ramsey_vertex_exponent_bound
#print axioms Erdos546.nat_extraction_ratio_bound
#print axioms Erdos546.extraction_inverse_exact
#print axioms Erdos546.extraction_depth_bound
#print axioms Erdos546.amplification_target_prefactor_bound
#print axioms Erdos546.sparse_extraction_exponent_bound
#print axioms Erdos546.low_density_rounding_loss_bound
