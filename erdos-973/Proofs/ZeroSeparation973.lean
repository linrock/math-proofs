import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring

/-!
# A zero-separation estimate for approximate polynomial exponentials

This module proves an elementary integrating-factor estimate.  It is one
analytic ingredient in the exterior-power-sum argument for Erdős problem 973;
it does not by itself prove the complete conjecture's negation.
-/

namespace Erdos973

open Polynomial Set

theorem integrating_factor_hasDerivAt (G : Polynomial ℂ) (mu w : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (mu * (1 - z)) * G.eval z)
      (Complex.exp (mu * (1 - w)) *
        (G.derivative - Polynomial.C mu * G).eval w) w := by
  convert (((hasDerivAt_id w).const_sub 1).const_mul mu).cexp.mul
    (G.hasDerivAt w) using 1 <;> try rfl
  simp only [id_eq, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- A root in the closed unit disk cannot be too close to a point normalized
to value one when the constant-coefficient differential residual is small. -/
theorem zero_separation_estimate {G : Polynomial ℂ} {mu beta : ℂ} {B epsilon : ℝ}
    (hG1 : G.eval 1 = 1) (hbeta : ‖beta‖ ≤ 1) (hroot : G.eval beta = 0)
    (hmu : ‖mu‖ ≤ B)
    (hE : ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖(G.derivative - Polynomial.C mu * G).eval w‖ ≤ epsilon) :
    1 ≤ ‖1 - beta‖ * Real.exp (B * ‖1 - beta‖) * epsilon := by
  have hB : 0 ≤ B := (norm_nonneg mu).trans hmu
  have hseg : segment ℝ beta (1 : ℂ) ⊆ Metric.closedBall (0 : ℂ) 1 :=
    (convex_closedBall (0 : ℂ) 1).segment_subset
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hbeta) (by simp)
  have hbound : ∀ w ∈ segment ℝ beta (1 : ℂ),
      ‖Complex.exp (mu * (1 - w)) *
        (G.derivative - Polynomial.C mu * G).eval w‖ ≤
      Real.exp (B * ‖1 - beta‖) * epsilon := by
    intro w hw
    have hwunit : ‖w‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hseg hw
    have hdist : ‖1 - w‖ ≤ ‖1 - beta‖ := by
      have hw' : w ∈ segment ℝ (1 : ℂ) beta := by
        simpa only [segment_symm] using hw
      simpa only [norm_sub_rev] using norm_sub_le_of_mem_segment hw'
    have hexp : ‖Complex.exp (mu * (1 - w))‖ ≤
        Real.exp (B * ‖1 - beta‖) := by
      apply (Complex.norm_exp_le_exp_norm _).trans
      apply Real.exp_le_exp.mpr
      rw [norm_mul]
      exact mul_le_mul hmu hdist (norm_nonneg _) hB
    rw [norm_mul]
    exact mul_le_mul hexp (hE w hwunit) (norm_nonneg _) (Real.exp_nonneg _)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w (_ : w ∈ segment ℝ beta (1 : ℂ)) =>
      (integrating_factor_hasDerivAt G mu w).hasDerivWithinAt)
    hbound (convex_segment beta (1 : ℂ))
    (left_mem_segment ℝ beta (1 : ℂ)) (right_mem_segment ℝ beta (1 : ℂ))
  simpa only [hG1, hroot, sub_self, mul_zero, zero_mul, Complex.exp_zero, mul_one,
    sub_zero, norm_one, mul_assoc, mul_comm, mul_left_comm] using h

/-- A finite sufficient condition for strict separation.  Applications can
take `B = 2 * n` and an exponentially small residual bound. -/
theorem zero_separation_of_small_residual
    {G : Polynomial ℂ} {mu beta : ℂ} {B epsilon delta : ℝ}
    (hG1 : G.eval 1 = 1) (hbeta : ‖beta‖ ≤ 1) (hroot : G.eval beta = 0)
    (hmu : ‖mu‖ ≤ B)
    (hE : ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖(G.derivative - Polynomial.C mu * G).eval w‖ ≤ epsilon)
    (hsmall : delta * Real.exp (B * delta) * epsilon < 1) :
    delta < ‖1 - beta‖ := by
  by_contra! hdist
  have hB : 0 ≤ B := (norm_nonneg mu).trans hmu
  have hepsilon : 0 ≤ epsilon := (norm_nonneg _).trans (hE 0 (by simp))
  have hdelta : 0 ≤ delta := (norm_nonneg _).trans hdist
  have hmono : ‖1 - beta‖ * Real.exp (B * ‖1 - beta‖) * epsilon ≤
      delta * Real.exp (B * delta) * epsilon := by
    apply mul_le_mul_of_nonneg_right _ hepsilon
    exact mul_le_mul hdist
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdist hB))
      (Real.exp_nonneg _) hdelta
  exact (not_le_of_gt hsmall)
    ((zero_separation_estimate hG1 hbeta hroot hmu hE).trans hmono)

end Erdos973
