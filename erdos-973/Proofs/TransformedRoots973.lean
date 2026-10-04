module

public import NewtonBridge973
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Tactic.FieldSimp


@[expose] public section

/-!
# Reciprocal roots at a nonvanishing boundary point

These are exact algebraic and geometric identities.  They do not assume the
analytic residual lower bound claimed in either preprint for problem 973.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace Erdos973

variable {ι : Type*}

/-- The reciprocal map sends the closed unit disk, away from `1`, to the
closed half-plane with real part at least `1/2`. -/
theorem reciprocal_one_sub_re_ge_half (beta : ℂ)
    (hbeta : ‖beta‖ ≤ 1) (hbeta1 : beta ≠ 1) :
    (1 / 2 : ℝ) ≤ ((1 - beta)⁻¹).re := by
  have hnz : 1 - beta ≠ 0 := sub_ne_zero.mpr hbeta1.symm
  have hpos : 0 < Complex.normSq (1 - beta) := Complex.normSq_pos.mpr hnz
  have hsq : Complex.normSq beta ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg beta]
  rw [Complex.inv_re]
  apply (le_div_iff₀ hpos).mpr
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im] at hsq ⊢
  nlinarith

/-- A root separation estimate becomes an upper bound for the reciprocal root. -/
theorem reciprocal_one_sub_norm_le (beta : ℂ) (delta : ℝ)
    (hdelta : 0 < delta) (hsep : delta ≤ ‖1 - beta‖) :
    ‖(1 - beta)⁻¹‖ ≤ delta⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hdelta hsep

theorem reciprocal_scalar_relation (a : ℂ) (ha : a ≠ 0)
    (ha1 : 1 - a ≠ 0) :
    (1 - a) * (1 - a⁻¹)⁻¹ = -a := by
  have hi : 1 - a⁻¹ ≠ 0 := by
    intro h
    apply ha1
    have hh : a⁻¹ = 1 := by linear_combination -h
    have hh' := congrArg (fun x : ℂ => x * a) hh
    exact sub_eq_zero.mpr (by simpa [ha] using hh')
  have ha1' : a - 1 ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp ha1).symm
  field_simp [ha, hi, ha1']
  ring

theorem shifted_linear_factor (a : ℂ) (ha : a ≠ 0)
    (ha1 : 1 - a ≠ 0) :
    (1 - C a * (X + 1) : ℂ[X]) =
      C (1 - a) * (1 - C (-(1 - a⁻¹)⁻¹) * X) := by
  have hs := congrArg (C : ℂ →+* ℂ[X]) (reciprocal_scalar_relation a ha ha1)
  simp only [map_mul, map_neg] at hs
  calc
    (1 - C a * (X + 1) : ℂ[X]) = C (1 - a) + (-C a) * X := by
      simp only [map_sub, map_one]
      ring
    _ = _ := by rw [← hs]; simp only [map_neg]; ring

/-- Scaling and shifting the original polynomial factors through the reciprocal
roots; the scalar is exactly the value at the normalization point. -/
theorem rootPolynomial_comp_scale_shift
    (s : Finset ι) (z : ι → ℂ) (tau : ℂ)
    (hnz : ∀ i ∈ s, tau * z i ≠ 0)
    (hvalue : (rootPolynomial s z).eval tau ≠ 0) :
    (rootPolynomial s z).comp (C tau * (X + 1)) =
      C ((rootPolynomial s z).eval tau) *
        rootPolynomial s (fun i => -(1 - (tau * z i)⁻¹)⁻¹) := by
  have hvalue' : (∏ i ∈ s, (1 - tau * z i)) ≠ 0 := by
    simpa only [rootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      mul_comm (z _) tau] using hvalue
  have hfactor (i : ι) (hi : i ∈ s) :
      (1 - C (z i) * X : ℂ[X]).comp (C tau * (X + 1)) =
        C (1 - tau * z i) * (1 - C (-(1 - (tau * z i)⁻¹)⁻¹) * X) := by
    have hsub := (Finset.prod_ne_zero_iff.mp hvalue') i hi
    convert shifted_linear_factor (tau * z i) (hnz i hi) hsub using 1
    simp only [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.X_comp, map_mul]
    ring
  rw [rootPolynomial, Polynomial.prod_comp]
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib]
  simp only [rootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [mul_comm tau]

/-- Taylor expansion at `1` of the boundary-normalized polynomial has constant
coefficient `1` and roots represented by `(1-beta_i)⁻¹`. -/
theorem normalized_taylor_rootPolynomial
    (s : Finset ι) (z : ι → ℂ) (tau : ℂ)
    (hnz : ∀ i ∈ s, tau * z i ≠ 0)
    (hvalue : (rootPolynomial s z).eval tau ≠ 0) :
    Polynomial.taylor 1
      (C ((rootPolynomial s z).eval tau)⁻¹ *
        (rootPolynomial s z).comp (C tau * X)) =
      rootPolynomial s (fun i => -(1 - (tau * z i)⁻¹)⁻¹) := by
  rw [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.comp_assoc]
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, C_1]
  rw [rootPolynomial_comp_scale_shift s z tau hnz hvalue]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hvalue, map_one, one_mul]

end Erdos973
