module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring


@[expose] public section

/-!
# A finite higher-moment obstruction in a compact right half-plane

The proof uses the polynomial test `v * (1 - a*v)^m`.  For suitably small
positive `a` this tends to zero uniformly on the stated region, whereas its
linear coefficient is one and all remaining coefficients have degree at
least two.  No analytic compactness theorem is needed for this lemma.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Erdos973.MomentObstruction

theorem exists_uniform_contraction (L : ℝ) (hL : 1 ≤ L) :
    ∃ a q : ℝ, 0 < a ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ v : ℂ, (1 / 2 : ℝ) ≤ v.re → ‖v‖ ≤ L → ‖1 - (a : ℂ) * v‖ ≤ q := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  let a : ℝ := 1 / (2 * L ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha_le : a ≤ 1 / 2 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * L ^ 2)).2
    nlinarith
  have haa : a ^ 2 * L ^ 2 = a / 2 := by
    dsimp [a]
    field_simp
  refine ⟨a, 1 - a / 4, ha, by linarith, by linarith, ?_⟩
  intro v hvre hvnorm
  have hsq : ‖v‖ ^ 2 ≤ L ^ 2 := by nlinarith [norm_nonneg v]
  have hid : ‖1 - (a : ℂ) * v‖ ^ 2 = 1 - 2 * a * v.re + a ^ 2 * ‖v‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.mul_im]
    ring
  have hprod := mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
  have hreal := mul_le_mul_of_nonneg_left hvre ha.le
  have hbound : ‖1 - (a : ℂ) * v‖ ^ 2 ≤ 1 - a / 2 := by nlinarith
  have hq : 0 ≤ 1 - a / 4 := by linarith
  nlinarith [norm_nonneg (1 - (a : ℂ) * v), sq_nonneg a]

theorem test_polynomial_expansion (a v : ℂ) (m : ℕ) :
    v * (1 - a * v) ^ m = v +
      ∑ j ∈ range m, ((-a) ^ (j + 1) * (m.choose (j + 1) : ℂ)) * v ^ (j + 2) := by
  have hbase : 1 - a * v = (-a * v) + 1 := by ring
  rw [hbase, add_pow, mul_sum, sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [mul_pow]
  rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
  ring

theorem norm_average_le {n : ℕ} (hn : 0 < n) (w : Fin n → ℂ) (B : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ B) : ‖(∑ i, w i) / (n : ℂ)‖ ≤ B := by
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).2
  calc
    ‖∑ i, w i‖ ≤ ∑ i, ‖w i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, B := sum_le_sum fun i _ => hw i
    _ = B * (n : ℝ) := by simp [mul_comm]

theorem re_average_ge {n : ℕ} (hn : 0 < n) (w : Fin n → ℂ)
    (hw : ∀ i, (1 / 2 : ℝ) ≤ (w i).re) :
    (1 / 2 : ℝ) ≤ ((∑ i, w i) / (n : ℂ)).re := by
  rw [Complex.div_natCast_re, Complex.re_sum]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).2
  calc
    (1 / 2 : ℝ) * (n : ℝ) = ∑ _i : Fin n, (1 / 2 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ i, (w i).re := sum_le_sum fun i _ => hw i

theorem test_average_expansion {n : ℕ} (v : Fin n → ℂ) (a : ℂ) (m : ℕ) :
    (∑ i, v i * (1 - a * v i) ^ m) / (n : ℂ) =
      (∑ i, v i) / (n : ℂ) +
      ∑ j ∈ range m, ((-a) ^ (j + 1) * (m.choose (j + 1) : ℂ)) *
        ((∑ i, v i ^ (j + 2)) / (n : ℂ)) := by
  simp_rw [test_polynomial_expansion]
  rw [sum_add_distrib, sum_comm, add_div]
  congr 1
  rw [sum_div]
  apply sum_congr rfl
  intro j hj
  rw [← mul_sum, mul_div_assoc]

/-- A bounded subset of `Re v ≥ 1/2` cannot have all its higher normalized
moments arbitrarily small.  Both the finite cutoff and the positive threshold
depend only on the radius bound `L`, not on the number of points. -/
theorem finite_moment_obstruction (L : ℝ) (hL : 1 ≤ L) :
    ∃ K : ℕ, 2 ≤ K ∧ ∃ η : ℝ, 0 < η ∧
      ∀ (n : ℕ), 0 < n → ∀ (v : Fin n → ℂ),
        (∀ i, (1 / 2 : ℝ) ≤ (v i).re) →
        (∀ i, ‖v i‖ ≤ L) →
        ∃ k : ℕ, 2 ≤ k ∧ k ≤ K ∧ η ≤ ‖(∑ i, v i ^ k) / (n : ℂ)‖ := by
  obtain ⟨a, q, ha, hq0, hq1, hcontract⟩ := exists_uniform_contraction L hL
  have ht : Tendsto (fun m : ℕ => L * q ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1))
  have he : ∀ᶠ m : ℕ in atTop, L * q ^ m < (1 / 4 : ℝ) :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨m, hm, hm1⟩ := (he.and (eventually_ge_atTop 1)).exists
  let c : ℕ → ℂ := fun j => (-(a : ℂ)) ^ (j + 1) * (m.choose (j + 1) : ℂ)
  let B : ℝ := ∑ j ∈ range m, ‖c j‖
  have hB : 0 ≤ B := sum_nonneg fun j _ => norm_nonneg (c j)
  let η : ℝ := 1 / (4 * (B + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hBη : B * η < (1 / 4 : ℝ) := by
    calc
      B * η = B / (4 * (B + 1)) := by dsimp [η]; ring
      _ < 1 / 4 := (div_lt_iff₀ (by positivity)).2 (by nlinarith)
  refine ⟨m + 1, by omega, η, hη, ?_⟩
  intro n hn v hvre hvnorm
  by_contra h
  push Not at h
  have hT : ‖(∑ i, v i * (1 - (a : ℂ) * v i) ^ m) / (n : ℂ)‖ < (1 / 4 : ℝ) := by
    apply lt_of_le_of_lt (norm_average_le hn _ (L * q ^ m) ?_) hm
    intro i
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hvnorm i) (pow_le_pow_left₀ (norm_nonneg _) (hcontract _ (hvre i) (hvnorm i)) _)
      (pow_nonneg (norm_nonneg _) _) (by linarith)
  have hR : ‖∑ j ∈ range m, c j * ((∑ i, v i ^ (j + 2)) / (n : ℂ))‖ < (1 / 4 : ℝ) := by
    apply lt_of_le_of_lt ?_ hBη
    calc
      ‖∑ j ∈ range m, c j * ((∑ i, v i ^ (j + 2)) / (n : ℂ))‖ ≤
          ∑ j ∈ range m, ‖c j * ((∑ i, v i ^ (j + 2)) / (n : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range m, ‖c j‖ * η := by
        apply sum_le_sum
        intro j hj
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (h (j + 2) (by omega) (by have := mem_range.mp hj; omega)).le
      _ = B * η := by rw [← sum_mul]
  have hexp := test_average_expansion v (a : ℂ) m
  change _ = _ + ∑ j ∈ range m, c j * ((∑ i, v i ^ (j + 2)) / (n : ℂ)) at hexp
  have hM : ‖(∑ i, v i) / (n : ℂ)‖ < (1 / 2 : ℝ) := by
    have hid := eq_sub_iff_add_eq.mpr hexp.symm
    rw [hid]
    exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith)
  have hreal := re_average_ge hn v hvre
  have hnorm := Complex.re_le_norm ((∑ i, v i) / (n : ℂ))
  linarith

end Erdos973.MomentObstruction
