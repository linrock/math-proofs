import Normalization973
import TransformedRoots973
import ZeroSeparation973
import TaylorResidual973
import HigherMoments973
import MomentObstruction973
import Statement973
import Decay973

/-!
# Exterior power sums: assembly of the qualitative argument

This development follows the residual-polynomial method of Tan, Wang, Huang,
and Chen (arXiv:2608.02043v3), with fixed-degree polynomial tests and coarse
coefficient estimates.  The qualitative negative answer was previously claimed
by Luo, Yang, and Zhu (arXiv:2607.22017).  Neither paper is assumed as an axiom.
The sharper square-root asymptotic estimate is not a target of this proof.
-/

open scoped BigOperators
open Polynomial Finset Filter

namespace Erdos973

/-- A finite reduction from small exterior power sums to bounded reciprocal
points whose higher moments are all controlled by the same small error. -/
theorem exterior_moment_reduction {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, 1 ≤ ‖z i‖) (M delta : ℝ) (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hM : ∀ k ∈ Icc 2 (n + 1), ‖powerSum univ z k‖ ≤ M)
    (hdelta : 0 < delta)
    (hsmall : delta * Real.exp ((2 * (n : ℝ)) * delta) *
      ((n + 1 : ℝ) * ((n : ℝ) * M)) < 1) :
    ∃ v : Fin n → ℂ,
      (∀ i, (1 / 2 : ℝ) ≤ (v i).re) ∧
      (∀ i, ‖v i‖ ≤ max 1 delta⁻¹) ∧
      ∀ K k : ℕ, 2 ≤ k → k ≤ K →
        ‖(∑ i, v i ^ k) / (n : ℂ)‖ ≤
          M * (2 : ℝ) ^ (K - 1) * (n + 1 : ℝ) ^ (2 * K - 1) := by
  obtain ⟨tau, htau, hval, hG1, hPcoeff, hGcoeff⟩ := exists_boundaryNormalization univ z
  let P := rootPolynomial univ z
  let G := boundaryNormalization P tau
  let mu := normalizedMu P tau
  let beta : Fin n → ℂ := fun i => (tau * z i)⁻¹
  let v : Fin n → ℂ := fun i => (1 - beta i)⁻¹
  have htz : ∀ i, tau * z i ≠ 0 := by
    intro i
    apply norm_ne_zero_iff.mp
    rw [norm_mul, htau, one_mul]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hz i))
  have hGdegree : G.natDegree ≤ n := by
    exact (boundaryNormalization_natDegree_le P tau).trans
      (by simpa [P] using rootPolynomial_natDegree_le univ z)
  have hEcoeff : ∀ k, ‖(G.derivative - C mu * G).coeff k‖ ≤ (n : ℝ) * M := by
    intro k
    exact boundaryNormalization_residual_coeff_norm_le univ z n M tau
      (by simp) hM0 hM htau hval hPcoeff k
  have hmu : ‖mu‖ ≤ 2 * (n : ℝ) := by
    apply (normalizedMu_rootPolynomial_norm_le univ z n M tau
      (by simp) hM0 hM htau).trans
    nlinarith [mul_le_mul_of_nonneg_left hM1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hEeval : ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖(G.derivative - C mu * G).eval w‖ ≤ (n + 1 : ℝ) * ((n : ℝ) * M) := by
    intro w hw
    exact norm_eval_le_of_coeff_bound _
      ((differential_residual_natDegree_le G mu).trans hGdegree) hEcoeff hw
  have hbeta : ∀ i, ‖beta i‖ ≤ 1 := fun i => normalized_root_norm_le_one htau (hz i)
  have hroot : ∀ i, G.eval (beta i) = 0 := by
    intro i
    exact boundaryNormalization_eval_reciprocal_root univ z tau i (mem_univ i) (htz i)
  have hsep : ∀ i, delta < ‖1 - beta i‖ := by
    intro i
    exact zero_separation_of_small_residual hG1 (hbeta i) (hroot i) hmu hEeval hsmall
  have hbeta1 : ∀ i, beta i ≠ 1 := by
    intro i hi
    have h := hsep i
    simp only [hi, sub_self, norm_zero] at h
    linarith
  have hTaylor : taylor 1 G = rootPolynomial univ (fun i => -v i) := by
    simpa only [G, P, v, beta, boundaryNormalization] using
      normalized_taylor_rootPolynomial univ z tau (fun i _ => htz i) hval
  have hc : ∀ j : ℕ, ‖(rootPolynomial univ (fun i => -v i)).coeff j‖ ≤
      (n + 1 : ℝ) ^ (j + 1) := by
    intro j
    rw [← hTaylor]
    simpa using norm_taylor_one_coeff_le G hGdegree hGcoeff j
  have hr : ∀ j : ℕ, ‖(residual (rootPolynomial univ (fun i => -v i))).coeff j‖ ≤
      2 * ((n : ℝ) * M) * (n + 1 : ℝ) ^ (j + 2) := by
    intro j
    rw [← hTaylor]
    exact taylor_residual_coeff_bound G mu hGdegree hG1 hGcoeff hEcoeff j
  refine ⟨v, (fun i => reciprocal_one_sub_re_ge_half (beta i) (hbeta i) (hbeta1 i)), ?_, ?_⟩
  · intro i
    exact (reciprocal_one_sub_norm_le (beta i) delta hdelta (hsep i).le).trans (le_max_right _ _)
  · intro K k hk hkK
    simpa only [mul_div_cancel_left₀ M (Nat.cast_ne_zero.mpr hn.ne')] using
      HigherMoments.normalized_powerSum_norm_le_uniform_of_neg_roots hn v
        (n + 1 : ℝ) ((n : ℝ) * M) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
        (by positivity) hc hr K k hk hkK

/-- Uniformly over all exterior configurations, every fixed exponential scale
is eventually strictly below at least one of the powers `2,...,n+1`. -/
theorem eventually_exterior_power_sum_strict_lower_bound (C : ℝ) (hC : 1 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Fin n → ℂ, (∀ i, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1), C ^ (-(n : ℝ)) < ‖powerSum univ z k‖ := by
  let delta := Real.log C / 4
  have hdelta : 0 < delta := Decay.delta_pos C hC
  obtain ⟨K, _, eta, heta, hobstruction⟩ :=
    MomentObstruction.finite_moment_obstruction (max 1 delta⁻¹) (le_max_left _ _)
  filter_upwards [Decay.eventually_numeric_conditions C hC K eta heta] with n hn
  rcases hn with ⟨hn, hM1, hsep, hsmall⟩
  intro z hz
  by_contra h
  push Not at h
  have hM0 : 0 ≤ C ^ (-(n : ℝ)) := Real.rpow_nonneg (by linarith) _
  obtain ⟨v, hvre, hvnorm, hvsmall⟩ :=
    exterior_moment_reduction hn z hz (C ^ (-(n : ℝ))) delta hM0 hM1 h hdelta hsep
  obtain ⟨k, hk, hkK, hlarge⟩ := hobstruction n hn v hvre hvnorm
  exact (not_lt_of_ge hlarge) ((hvsmall K k hk hkK).trans_lt hsmall)

theorem eventually_exterior_power_sum_lower_bound (C : ℝ) (hC : 1 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Fin n → ℂ, (∀ i, 1 ≤ ‖z i‖) →
      ∃ k ∈ Icc 2 (n + 1), C ^ (-(n : ℝ)) ≤ ‖powerSum univ z k‖ := by
  filter_upwards [eventually_exterior_power_sum_strict_lower_bound C hC] with n hn
  intro z hz
  obtain ⟨k, hk, hbound⟩ := hn z hz
  exact ⟨k, hk, hbound.le⟩

/-- The exact original all-orders exterior-point statement is false. -/
theorem not_erdos_973 : ¬ OriginalStatement :=
  not_original_of_eventual_lower_bound eventually_exterior_power_sum_lower_bound

/-- The negative answer in the equivalence format of the upstream statement. -/
theorem erdos_973_false : False ↔ OriginalStatement := by
  simp only [false_iff]
  exact not_erdos_973

end Erdos973
