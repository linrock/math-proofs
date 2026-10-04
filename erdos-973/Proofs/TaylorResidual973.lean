module

public import PolynomialBounds973
public import NewtonBridge973


@[expose] public section

/-! Polynomial bounds after moving the normalization point to the origin. -/

open Polynomial

namespace Erdos973

theorem derivative_taylor_one (G : ℂ[X]) :
    (taylor 1 G).derivative = taylor 1 G.derivative := by
  simp [taylor_apply, Polynomial.derivative_comp]

theorem residual_taylor_one_eq (G : ℂ[X]) (mu : ℂ) (hG : G.eval 1 = 1) :
    residual (taylor 1 G) = taylor 1 (G.derivative - C mu * G) -
      C ((G.derivative - C mu * G).eval 1) * taylor 1 G := by
  rw [residual, derivative_taylor_one]
  simp only [taylor_apply, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, zero_add, Polynomial.eval_sub, Polynomial.eval_mul,
    hG, mul_one, map_sub]
  ring

theorem taylor_residual_coeff_bound (G : ℂ[X]) (mu : ℂ) {n : ℕ} {eps : ℝ}
    (hn : G.natDegree ≤ n) (hG : G.eval 1 = 1)
    (hcoeff : ∀ j : ℕ, ‖G.coeff j‖ ≤ 1)
    (hE : ∀ j : ℕ, ‖(G.derivative - C mu * G).coeff j‖ ≤ eps) (k : ℕ) :
    ‖(residual (taylor 1 G)).coeff k‖ ≤ 2 * eps * (n + 1 : ℝ) ^ (k + 2) := by
  let E := G.derivative - C mu * G
  have heps : 0 ≤ eps := (norm_nonneg _).trans (hE 0)
  have hEn : E.natDegree ≤ n := (differential_residual_natDegree_le G mu).trans hn
  have htE := norm_taylor_one_coeff_le E hEn hE k
  have htG := norm_taylor_one_coeff_le G hn hcoeff k
  have hE1 := norm_eval_le_of_coeff_bound E hEn hE (w := 1) (by simp)
  rw [residual_taylor_one_eq G mu hG, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  calc
    ‖(taylor 1 E).coeff k - E.eval 1 * (taylor 1 G).coeff k‖ ≤
        ‖(taylor 1 E).coeff k‖ + ‖E.eval 1‖ * ‖(taylor 1 G).coeff k‖ := by
      simpa only [norm_mul] using norm_sub_le ((taylor 1 E).coeff k)
        (E.eval 1 * (taylor 1 G).coeff k)
    _ ≤ eps * (n + 1 : ℝ) ^ (k + 1) +
        ((n + 1 : ℝ) * eps) * (n + 1 : ℝ) ^ (k + 1) := by
      gcongr
      simpa using htG
    _ = (eps * (n + 1 : ℝ) ^ (k + 1)) * (1 + (n + 1 : ℝ)) := by ring
    _ ≤ (eps * (n + 1 : ℝ) ^ (k + 1)) * (2 * (n + 1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    _ = 2 * eps * (n + 1 : ℝ) ^ (k + 2) := by ring

end Erdos973
