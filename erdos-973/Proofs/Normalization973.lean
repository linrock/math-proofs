import NewtonBridge973
import PolynomialBounds973

/-!
# Boundary normalization for Erdős problem 973

Rotation to a maximum-modulus point and division by its nonzero value preserve
the root domain while controlling every coefficient of the polynomial and its
differential residual.  The estimates here are finite and algebraic once the
maximum point has been supplied.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace Erdos973

/-- Rotate and divide by the value at the chosen boundary point. -/
def boundaryNormalization (P : ℂ[X]) (tau : ℂ) : ℂ[X] :=
  C (P.eval tau)⁻¹ * P.comp (C tau * X)

/-- The constant coefficient in the rotated differential equation. -/
def normalizedMu (P : ℂ[X]) (tau : ℂ) : ℂ :=
  tau * P.derivative.eval 0

@[simp] theorem boundaryNormalization_eval (P : ℂ[X]) (tau w : ℂ) :
    (boundaryNormalization P tau).eval w = (P.eval tau)⁻¹ * P.eval (tau * w) := by
  simp [boundaryNormalization]

@[simp] theorem boundaryNormalization_eval_one (P : ℂ[X]) (tau : ℂ)
    (hval : P.eval tau ≠ 0) : (boundaryNormalization P tau).eval 1 = 1 := by
  simp [hval]

@[simp] theorem boundaryNormalization_coeff (P : ℂ[X]) (tau : ℂ) (k : ℕ) :
    (boundaryNormalization P tau).coeff k = (P.eval tau)⁻¹ * (P.coeff k * tau ^ k) := by
  simp [boundaryNormalization]

theorem boundaryNormalization_natDegree_le (P : ℂ[X]) (tau : ℂ) :
    (boundaryNormalization P tau).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk]

theorem boundaryNormalization_coeff_norm_le_one (P : ℂ[X]) (tau : ℂ)
    (htau : ‖tau‖ = 1) (hval : P.eval tau ≠ 0)
    (hcoeff : ∀ k : ℕ, ‖P.coeff k‖ ≤ ‖P.eval tau‖) (k : ℕ) :
    ‖(boundaryNormalization P tau).coeff k‖ ≤ 1 := by
  have hnorm : 0 < ‖P.eval tau‖ := norm_pos_iff.mpr hval
  have h := (div_le_one₀ hnorm).mpr (hcoeff k)
  simpa [norm_mul, norm_inv, norm_pow, htau, div_eq_mul_inv, mul_comm] using h

theorem boundaryNormalization_residual (P : ℂ[X]) (tau : ℂ) :
    (boundaryNormalization P tau).derivative -
        C (normalizedMu P tau) * boundaryNormalization P tau =
      C (tau * (P.eval tau)⁻¹) * (residual P).comp (C tau * X) := by
  simp only [boundaryNormalization, normalizedMu, residual, Polynomial.derivative_C_mul,
    Polynomial.derivative_comp, Polynomial.derivative_X, mul_one,
    Polynomial.sub_comp, Polynomial.C_mul_comp, map_mul]
  ring

theorem boundaryNormalization_residual_coeff (P : ℂ[X]) (tau : ℂ) (k : ℕ) :
    ((boundaryNormalization P tau).derivative -
        C (normalizedMu P tau) * boundaryNormalization P tau).coeff k =
      (tau * (P.eval tau)⁻¹) * ((residual P).coeff k * tau ^ k) := by
  rw [boundaryNormalization_residual, Polynomial.coeff_C_mul,
    Polynomial.comp_C_mul_X_coeff]

theorem boundaryNormalization_residual_coeff_norm_le
    {ι : Type*} (s : Finset ι) (z : ι → ℂ) (n : ℕ) (M : ℝ) (tau : ℂ)
    (hs : s.card ≤ n) (hM0 : 0 ≤ M)
    (hM : ∀ k ∈ Finset.Icc 2 (n + 1), ‖powerSum s z k‖ ≤ M)
    (htau : ‖tau‖ = 1) (hval : (rootPolynomial s z).eval tau ≠ 0)
    (hcoeff : ∀ k : ℕ, ‖(rootPolynomial s z).coeff k‖ ≤
      ‖(rootPolynomial s z).eval tau‖) (k : ℕ) :
    ‖((boundaryNormalization (rootPolynomial s z) tau).derivative -
      C (normalizedMu (rootPolynomial s z) tau) *
        boundaryNormalization (rootPolynomial s z) tau).coeff k‖ ≤ (n : ℝ) * M := by
  rw [boundaryNormalization_residual_coeff]
  simp only [norm_mul, norm_inv, norm_pow, htau, one_pow, one_mul, mul_one]
  by_cases hk : k ≤ n
  · have hb := residual_rootPolynomial_coeff_norm_le_of_bound s z n k M
      ‖(rootPolynomial s z).eval tau‖ hM0 hM (fun j _ => hcoeff j) hk
    calc
      ‖(rootPolynomial s z).eval tau‖⁻¹ * ‖(residual (rootPolynomial s z)).coeff k‖ ≤
          ‖(rootPolynomial s z).eval tau‖⁻¹ *
            ((n : ℝ) * M * ‖(rootPolynomial s z).eval tau‖) := by gcongr
      _ = (n : ℝ) * M := by
        have hnorm : ‖(rootPolynomial s z).eval tau‖ ≠ 0 := norm_ne_zero_iff.mpr hval
        field_simp
  · have hd : (residual (rootPolynomial s z)).natDegree < k :=
      lt_of_le_of_lt ((residual_natDegree_le _).trans
        ((rootPolynomial_natDegree_le s z).trans hs)) (by omega)
    simp only [Polynomial.coeff_eq_zero_of_natDegree_lt hd, norm_zero, mul_zero]
    positivity

theorem normalizedMu_rootPolynomial_norm_le
    {ι : Type*} (s : Finset ι) (z : ι → ℂ) (n : ℕ) (M : ℝ) (tau : ℂ)
    (hs : s.card ≤ n) (hM0 : 0 ≤ M)
    (hM : ∀ k ∈ Finset.Icc 2 (n + 1), ‖powerSum s z k‖ ≤ M)
    (htau : ‖tau‖ = 1) :
    ‖normalizedMu (rootPolynomial s z) tau‖ ≤ (n : ℝ) * (1 + M) := by
  have h := powerSum_one_norm_le s z n M hs hM0 hM
  simpa [normalizedMu, norm_mul, htau, mul_add] using h

theorem normalized_root_norm_le_one {tau z : ℂ}
    (htau : ‖tau‖ = 1) (hz : 1 ≤ ‖z‖) : ‖(tau * z)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_mul, htau, one_mul]
  exact inv_le_one_of_one_le₀ hz

theorem boundaryNormalization_eval_reciprocal_root
    {ι : Type*} (s : Finset ι) (z : ι → ℂ) (tau : ℂ) (i : ι)
    (hi : i ∈ s) (htz : tau * z i ≠ 0) :
    (boundaryNormalization (rootPolynomial s z) tau).eval ((tau * z i)⁻¹) = 0 := by
  rw [boundaryNormalization_eval]
  apply mul_eq_zero_of_right
  simp only [rootPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hi
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [show z i * (tau * (tau * z i)⁻¹) = (tau * z i) * (tau * z i)⁻¹ by ring,
    mul_inv_cancel₀ htz, sub_self]

/-- Every root-generated polynomial has a boundary normalization with unit
value at one and a coefficient bound of one. -/
theorem exists_boundaryNormalization {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ∃ tau : ℂ, ‖tau‖ = 1 ∧ (rootPolynomial s z).eval tau ≠ 0 ∧
      (boundaryNormalization (rootPolynomial s z) tau).eval 1 = 1 ∧
      (∀ k : ℕ, ‖(rootPolynomial s z).coeff k‖ ≤
        ‖(rootPolynomial s z).eval tau‖) ∧
      (∀ k : ℕ, ‖(boundaryNormalization (rootPolynomial s z) tau).coeff k‖ ≤ 1) := by
  obtain ⟨tau, htau, hval, _, hcoeff⟩ :=
    exists_circle_max_ne_zero (rootPolynomial s z) (rootPolynomial_coeff_zero s z)
  exact ⟨tau, htau, hval, boundaryNormalization_eval_one _ _ hval, hcoeff,
    boundaryNormalization_coeff_norm_le_one _ _ htau hval hcoeff⟩

end Erdos973
