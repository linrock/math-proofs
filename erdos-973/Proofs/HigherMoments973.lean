module

public import NewtonBridge973


@[expose] public section

/-!
# Coefficient bounds imply bounds for higher Newton sums

The finite projected Newton recurrence has a geometric majorant in the power
index. Its estimates retain the residual error and the exact averaging factor
`1 / n`; for each fixed power, the loss in the coefficient scale is polynomial.
-/

open scoped BigOperators
open Finset

namespace Erdos973.HigherMoments

theorem two_add_sum_reverse_powers (m : ℕ) :
    (2 : ℝ) + ∑ j ∈ range m, (2 : ℝ) ^ (m - j) = 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [← add_assoc, ih, pow_succ]
    ring

/-- A geometric majorant for the projected Newton recurrence. -/
theorem norm_le_of_projected_recurrence
    (p c r : ℕ → ℂ) (D ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hc : ∀ j : ℕ, ‖c j‖ ≤ D ^ (j + 1))
    (hr : ∀ j : ℕ, ‖r j‖ ≤ 2 * ε * D ^ (j + 2))
    (hrec : ∀ m : ℕ, p (m + 2) = -r (m + 1) -
      ∑ j ∈ range m, c (j + 1) * p (m + 1 - j)) :
    ∀ k : ℕ, 2 ≤ k → ‖p k‖ ≤ ε * (2 : ℝ) ^ (k - 1) * D ^ (2 * k - 1) := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rcases k with _ | (_ | m)
    · omega
    · omega
    change ‖p (m + 2)‖ ≤ ε * (2 : ℝ) ^ (m + 1) * D ^ (2 * m + 3)
    have hnorm : ‖p (m + 2)‖ ≤ ‖r (m + 1)‖ +
        ∑ j ∈ range m, ‖c (j + 1)‖ * ‖p (m + 1 - j)‖ := by
      rw [hrec]
      calc
        ‖-r (m + 1) - ∑ j ∈ range m, c (j + 1) * p (m + 1 - j)‖ ≤
            ‖-r (m + 1)‖ + ‖∑ j ∈ range m, c (j + 1) * p (m + 1 - j)‖ := norm_sub_le _ _
        _ ≤ ‖r (m + 1)‖ + ∑ j ∈ range m, ‖c (j + 1)‖ * ‖p (m + 1 - j)‖ := by
          simp only [norm_neg]
          apply add_le_add (le_refl _)
          simpa only [norm_mul] using
            (norm_sum_le (range m) (fun j => c (j + 1) * p (m + 1 - j)))
    have hres : ‖r (m + 1)‖ ≤ 2 * ε * D ^ (2 * m + 3) := by
      exact (hr _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hD (by omega : m + 1 + 2 ≤ 2 * m + 3)) (by positivity))
    have hterms : ∀ j ∈ range m,
        ‖c (j + 1)‖ * ‖p (m + 1 - j)‖ ≤
          ε * (2 : ℝ) ^ (m - j) * D ^ (2 * m + 3) := by
      intro j hj
      have hjm := mem_range.mp hj
      have hp := ih (m + 1 - j) (by omega) (by omega)
      rw [show (m + 1 - j) - 1 = m - j by omega] at hp
      have hpow : D ^ (j + 2) * D ^ (2 * (m + 1 - j) - 1) ≤
          D ^ (2 * m + 3) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hD (by omega)
      calc
        ‖c (j + 1)‖ * ‖p (m + 1 - j)‖ ≤
            D ^ (j + 2) * (ε * (2 : ℝ) ^ (m - j) *
              D ^ (2 * (m + 1 - j) - 1)) :=
          mul_le_mul (hc (j + 1)) hp (norm_nonneg _) (pow_nonneg hD0 _)
        _ = ε * (2 : ℝ) ^ (m - j) *
            (D ^ (j + 2) * D ^ (2 * (m + 1 - j) - 1)) := by ring
        _ ≤ ε * (2 : ℝ) ^ (m - j) * D ^ (2 * m + 3) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    calc
      ‖p (m + 2)‖ ≤ ‖r (m + 1)‖ +
          ∑ j ∈ range m, ‖c (j + 1)‖ * ‖p (m + 1 - j)‖ := hnorm
      _ ≤ 2 * ε * D ^ (2 * m + 3) +
          ∑ j ∈ range m, ε * (2 : ℝ) ^ (m - j) * D ^ (2 * m + 3) :=
        add_le_add hres (sum_le_sum hterms)
      _ = ε * ((2 : ℝ) + ∑ j ∈ range m, (2 : ℝ) ^ (m - j)) * D ^ (2 * m + 3) := by
        simp only [← sum_mul, ← mul_sum]
        ring
      _ = ε * (2 : ℝ) ^ (m + 1) * D ^ (2 * m + 3) := by
        rw [two_add_sum_reverse_powers]

/-- The recurrence estimate instantiated at the actual finite root polynomial. -/
theorem powerSum_norm_le_of_coeff_bounds {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (D ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hc : ∀ j : ℕ, ‖(rootPolynomial s z).coeff j‖ ≤ D ^ (j + 1))
    (hr : ∀ j : ℕ, ‖(residual (rootPolynomial s z)).coeff j‖ ≤ 2 * ε * D ^ (j + 2))
    (k : ℕ) (hk : 2 ≤ k) :
    ‖powerSum s z k‖ ≤ ε * (2 : ℝ) ^ (k - 1) * D ^ (2 * k - 1) := by
  exact norm_le_of_projected_recurrence (powerSum s z)
    (fun j => (rootPolynomial s z).coeff j)
    (fun j => (residual (rootPolynomial s z)).coeff j)
    D ε hD hε hc hr (powerSum_eq_residual_recurrence s z) k hk

/-- A single bound for all powers in any fixed finite window. -/
theorem powerSum_norm_le_uniform {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (D ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hc : ∀ j : ℕ, ‖(rootPolynomial s z).coeff j‖ ≤ D ^ (j + 1))
    (hr : ∀ j : ℕ, ‖(residual (rootPolynomial s z)).coeff j‖ ≤ 2 * ε * D ^ (j + 2))
    (K k : ℕ) (hk : 2 ≤ k) (hkK : k ≤ K) :
    ‖powerSum s z k‖ ≤ ε * (2 : ℝ) ^ (K - 1) * D ^ (2 * K - 1) := by
  apply (powerSum_norm_le_of_coeff_bounds s z D ε hD hε hc hr k hk).trans
  have ht : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ (K - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact mul_le_mul (mul_le_mul_of_nonneg_left ht hε)
    (pow_le_pow_right₀ hD (by omega)) (by positivity) (by positivity)

/-- Normalize the power sum while retaining the exact factor `1 / n`. -/
theorem normalized_powerSum_norm_le_uniform {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (D ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hc : ∀ j : ℕ, ‖(rootPolynomial univ z).coeff j‖ ≤ D ^ (j + 1))
    (hr : ∀ j : ℕ, ‖(residual (rootPolynomial univ z)).coeff j‖ ≤ 2 * ε * D ^ (j + 2))
    (K k : ℕ) (hk : 2 ≤ k) (hkK : k ≤ K) :
    ‖(∑ i, z i ^ k) / (n : ℂ)‖ ≤
      (ε / (n : ℝ)) * (2 : ℝ) ^ (K - 1) * D ^ (2 * K - 1) := by
  have h := powerSum_norm_le_uniform univ z D ε hD hε hc hr K k hk hkK
  rw [norm_div, Complex.norm_natCast]
  calc
    ‖∑ i, z i ^ k‖ / (n : ℝ) ≤
        (ε * (2 : ℝ) ^ (K - 1) * D ^ (2 * K - 1)) / (n : ℝ) :=
      div_le_div_of_nonneg_right h (Nat.cast_pos.mpr hn).le
    _ = (ε / (n : ℝ)) * (2 : ℝ) ^ (K - 1) * D ^ (2 * K - 1) := by ring

/-- Changing every point to its negative changes a power sum only by a unit. -/
theorem norm_sum_neg_pow_div_eq {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (k : ℕ) (w : ℂ) :
    ‖(∑ i ∈ s, (-z i) ^ k) / w‖ = ‖(∑ i ∈ s, z i ^ k) / w‖ := by
  have hs : (∑ i ∈ s, (-z i) ^ k) = (-1 : ℂ) ^ k * (∑ i ∈ s, z i ^ k) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    exact neg_pow (z i) k
  rw [hs, mul_div_assoc, norm_mul, norm_pow]
  simp

/-- The version directly suited to a Taylor polynomial `∏ i, (1 + v i * X)`. -/
theorem normalized_powerSum_norm_le_uniform_of_neg_roots {n : ℕ} (hn : 0 < n)
    (v : Fin n → ℂ) (D ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hc : ∀ j : ℕ, ‖(rootPolynomial univ (fun i => -v i)).coeff j‖ ≤ D ^ (j + 1))
    (hr : ∀ j : ℕ, ‖(residual (rootPolynomial univ (fun i => -v i))).coeff j‖ ≤
      2 * ε * D ^ (j + 2))
    (K k : ℕ) (hk : 2 ≤ k) (hkK : k ≤ K) :
    ‖(∑ i, v i ^ k) / (n : ℂ)‖ ≤
      (ε / (n : ℝ)) * (2 : ℝ) ^ (K - 1) * D ^ (2 * K - 1) := by
  simpa only [norm_sum_neg_pow_div_eq] using
    normalized_powerSum_norm_le_uniform hn (fun i => -v i) D ε hD hε hc hr K k hk hkK

end Erdos973.HigherMoments
