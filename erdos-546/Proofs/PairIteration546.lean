module

public import PairIterationScalars546


@[expose] public section

/-!
# Finite reservoir-budget iteration

Iterates a single-step amplification map along the geometric schedule
$a \mapsto \operatorname{next}(a)$ while tracking the clique growth and
reservoir potential drop until the terminal scale $A$ is reached.
-/

namespace Erdos546

theorem amplification_iteration {State : Type*}
    (valid : State → Prop) (clique reservoir : State → ℝ)
    (A : ℕ) (B L s : ℝ) (next : ℕ → ℕ)
    (hA : 3 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hnext : ∀ a, 3 ≤ a → a < next a)
    (hgrowth : ∀ a, 3 ≤ a → (4 / 3 : ℝ) * a ≤ next a)
    (hcube : ∀ a, 3 ≤ a → (next a : ℝ) ^ 3 ≤ (2 : ℝ) ^ (2 * a))
    (initial : State) (hinitial : valid initial)
    (hinitial_clique : (3 : ℝ) ^ 3 * s ≤ clique initial)
    (hinitial_reservoir : (2 : ℝ) ^ ((B + 4 * L / 3) * s) ≤ reservoir initial)
    (hamp : ∀ (a : ℕ) (σ : State), 3 ≤ a → a ≤ A → valid σ →
      (a : ℝ) ^ 3 * s ≤ clique σ →
      (2 : ℝ) ^ (B * s / a) ≤ reservoir σ →
      ∃ τ, valid τ ∧ (2 : ℝ) ^ (2 * a) * s ≤ clique τ ∧
        reservoir σ * (2 : ℝ) ^ (-L * s / a) ≤ reservoir τ) :
    ∃ τ, valid τ ∧ (2 : ℝ) ^ (2 * A) * s ≤ clique τ := by
  let P : ℕ → Prop := fun a => ∃ σ, valid σ ∧
    (a : ℝ) ^ 3 * s ≤ clique σ ∧
    (2 : ℝ) ^ (B * s + 4 * L * s / a) ≤ reservoir σ
  have hstart : P 3 := by
    refine ⟨initial, hinitial, hinitial_clique, ?_⟩
    norm_num only [Nat.cast_ofNat]
    rw [← reservoir_initial_potential B L s]
    exact hinitial_reservoir
  have hstep : ∀ a, 3 ≤ a → a < A → P a → P (next a) := by
    intro a ha haA hp
    rcases hp with ⟨σ, hv, hc, hr⟩
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    have ha0 : (0 : ℝ) < a := by linarith
    have hready : (2 : ℝ) ^ (B * s / a) ≤ reservoir σ :=
      (reservoir_threshold_of_potential B L s (a : ℝ) hB hL hs ha1).trans hr
    obtain ⟨τ, hτ, hτc, hτr⟩ := hamp a σ ha haA.le hv hc hready
    refine ⟨τ, hτ, (mul_le_mul_of_nonneg_right (hcube a ha) hs).trans hτc, ?_⟩
    calc
      (2 : ℝ) ^ (B * s + 4 * L * s / next a) ≤
          2 ^ (B * s + 4 * L * s / a) * 2 ^ (-L * s / a) :=
        reservoir_potential_drop B L s (a : ℝ) (next a : ℝ) hL hs ha0 (hgrowth a ha)
      _ ≤ reservoir σ * (2 : ℝ) ^ (-L * s / a) :=
        mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg (by norm_num) _)
      _ ≤ reservoir τ := hτr
  obtain ⟨a, ha, hAa, σ, hv, hc, hr⟩ := exists_terminal_parameter A P next hstart hnext hstep
  have hcast : (A : ℝ) ≤ a := by exact_mod_cast hAa
  have hcubeA : (A : ℝ) ^ 3 ≤ (a : ℝ) ^ 3 := by
    gcongr
  have hcliqueA : (A : ℝ) ^ 3 * s ≤ clique σ :=
    (mul_le_mul_of_nonneg_right hcubeA hs).trans hc
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast (show 1 ≤ A by omega)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hrest : 0 ≤ 4 * L * s / a := by positivity
  have hexp : B * s / A ≤ B * s + 4 * L * s / a :=
    (div_le_self (mul_nonneg hB hs) hA1).trans (by linarith)
  have hreadyA : (2 : ℝ) ^ (B * s / A) ≤ reservoir σ :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans hr
  obtain ⟨τ, hτ, hτc, _⟩ := hamp A σ hA le_rfl hv hcliqueA hreadyA
  exact ⟨τ, hτ, hτc⟩

end Erdos546
