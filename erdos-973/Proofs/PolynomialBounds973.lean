import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial estimates for the exterior power-sum problem

These estimates use the coefficient and boundary norms explicitly.  In particular,
no residual lower bound or unproved analytic input is assumed.
-/

open scoped BigOperators
open Polynomial Complex Set MeasureTheory

namespace Erdos973

theorem norm_coeff_le_of_circle_bound (p : ℂ[X]) {S : ℝ}
    (hS : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ S) (k : ℕ) :
    ‖p.coeff k‖ ≤ S := by
  let : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  rw [← p.fourierCoeff_toAddCircle_natCast k, fourierCoeff]
  have h : ∀ a : AddCircle (2 * Real.pi),
      ‖fourier (-(k : ℤ)) a • p.toAddCircle a‖ ≤ S := by
    intro a
    simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    simpa [Polynomial.toAddCircle, Polynomial.aeval_continuousMap_apply] using
      hS (a.toCircle : ℂ) (Circle.norm_coe _)
  simpa using norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle) (Filter.Eventually.of_forall h)

theorem exists_circle_max (p : ℂ[X]) :
    ∃ τ : ℂ, ‖τ‖ = 1 ∧ ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ ‖p.eval τ‖ := by
  obtain ⟨τ, hτ, hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    (show (Metric.sphere (0 : ℂ) 1).Nonempty from ⟨1, by simp⟩)
    p.continuous.norm.continuousOn
  refine ⟨τ, by simpa using hτ, ?_⟩
  intro w hw
  exact hmax (by simpa using hw)

theorem exists_circle_max_ne_zero (p : ℂ[X]) (hp : p.coeff 0 = 1) :
    ∃ τ : ℂ, ‖τ‖ = 1 ∧ p.eval τ ≠ 0 ∧
      (∀ w : ℂ, ‖w‖ = 1 → ‖p.eval w‖ ≤ ‖p.eval τ‖) ∧
      (∀ k : ℕ, ‖p.coeff k‖ ≤ ‖p.eval τ‖) := by
  obtain ⟨τ, hτ, hmax⟩ := exists_circle_max p
  have hcoeff := norm_coeff_le_of_circle_bound p hmax
  refine ⟨τ, hτ, ?_, hmax, hcoeff⟩
  intro hz
  have := hcoeff 0
  norm_num [hp, hz] at this

theorem norm_eval_le_of_coeff_bound (p : ℂ[X]) {n : ℕ} {B : ℝ}
    (hn : p.natDegree ≤ n) (hB : ∀ k : ℕ, ‖p.coeff k‖ ≤ B)
    {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖p.eval w‖ ≤ (n + 1 : ℝ) * B := by
  rw [p.eval_eq_sum_range' (show p.natDegree < n + 1 by omega) w]
  calc
    ‖∑ i ∈ Finset.range (n + 1), p.coeff i * w ^ i‖ ≤
        ∑ i ∈ Finset.range (n + 1), ‖p.coeff i * w ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1), B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hw) (norm_nonneg _)).trans
        (by simpa using hB i)
    _ = (n + 1 : ℝ) * B := by simp

theorem norm_taylor_one_coeff_le (p : ℂ[X]) {n : ℕ} {B : ℝ}
    (hn : p.natDegree ≤ n) (hB : ∀ k : ℕ, ‖p.coeff k‖ ≤ B) (k : ℕ) :
    ‖(Polynomial.taylor 1 p).coeff k‖ ≤ B * (n + 1 : ℝ) ^ (k + 1) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply, Polynomial.sum_def,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, one_pow, mul_one]
  calc
    ‖∑ i ∈ p.support, (i.choose k : ℂ) * p.coeff i‖ ≤
        ∑ i ∈ p.support, ‖(i.choose k : ℂ) * p.coeff i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ p.support, (n + 1 : ℝ) ^ k * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := (Polynomial.le_natDegree_of_mem_supp i hi).trans hn
      have hc : (i.choose k : ℝ) ≤ (n + 1 : ℝ) ^ k := by
        exact_mod_cast (Nat.choose_le_pow i k).trans
          (Nat.pow_le_pow_left (by omega : i ≤ n + 1) k)
      simpa only [norm_mul, Complex.norm_natCast] using
        mul_le_mul hc (hB i) (norm_nonneg _) (by positivity : 0 ≤ (n + 1 : ℝ) ^ k)
    _ ≤ (n + 1 : ℝ) * ((n + 1 : ℝ) ^ k * B) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hc : p.support.card ≤ n + 1 := by
        simpa using Finset.card_le_card
          (show p.support ⊆ Finset.range (n + 1) from fun i hi =>
            Finset.mem_range.mpr (lt_of_le_of_lt
              ((Polynomial.le_natDegree_of_mem_supp i hi).trans hn) (Nat.lt_succ_self n)))
      exact_mod_cast hc
    _ = B * (n + 1 : ℝ) ^ (k + 1) := by ring

end Erdos973
