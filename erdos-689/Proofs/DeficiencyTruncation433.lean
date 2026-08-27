import DeficiencySmooth433
import DeficiencyCoefficients

/-!
# Rectangular smooth-core truncations for Erdős problem #689

Every finite even smooth-core/residue family is already known to inject into
the actual initial-deficiency ledger and has its exact fixed-progression prime
density. The normalized dyadic/smooth coefficient is one. This module proves
that the diagonal finite rectangular truncations converge to that exact value,
and that realizing those rectangles as admissible finite families suffices for
the genuine asymptotic lower bound. No infinite-tail interchange, uniform PNT,
or exceptional-target upper estimate is required for this one-sided result.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The finite dyadic coefficient with positive exponents up to `E`. -/
noncomputable def truncatedDyadicDeficiencyCoefficient (E : ℕ) : ℝ :=
  ∑ k ∈ Finset.range E, ((2 : ℝ)⁻¹) ^ (k + 1)

/-- One switched-prime selector truncated at positive exponent `E`. -/
noncomputable def truncatedSmoothDeficiencySelector (s E : ℕ) : ℝ :=
  ((s : ℝ) - 2) / ((s : ℝ) - 1) +
    ∑ e ∈ Finset.range E, ((s : ℝ)⁻¹) ^ (e + 1)

/-- The diagonal finite rectangle in the dyadic and switched-prime exponent
coordinates. -/
noncomputable def truncatedInitialDeficiencyCoefficient
    (S : Finset ℕ) (E : ℕ) : ℝ :=
  truncatedDyadicDeficiencyCoefficient E *
    ∏ s ∈ S, truncatedSmoothDeficiencySelector s E

/-- The finite positive dyadic shells converge to their exact mass one. -/
theorem truncated_dyadic_deficiency_coefficient_tendsto :
    Tendsto truncatedDyadicDeficiencyCoefficient atTop (nhds 1) := by
  have hbase : Summable (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hshift : Summable (fun k : ℕ => ((2 : ℝ)⁻¹) ^ (k + 1)) := by
    simpa [pow_succ] using hbase.mul_right ((2 : ℝ)⁻¹)
  have hlimit := hshift.hasSum.tendsto_sum_nat
  rw [dyadic_deficiency_coefficient_tsum] at hlimit
  exact hlimit

/-- Each finite switched-prime selector converges to its exact normalized
value one. -/
theorem truncated_smooth_deficiency_selector_tendsto (s : ℕ) (hs : 1 < s) :
    Tendsto (truncatedSmoothDeficiencySelector s) atTop (nhds 1) := by
  have hsreal : (1 : ℝ) < s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hbase : Summable (fun e : ℕ => ((s : ℝ)⁻¹) ^ e) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ hspos).mpr hsreal)
  have hshift : Summable (fun e : ℕ => ((s : ℝ)⁻¹) ^ (e + 1)) := by
    simpa [pow_succ] using hbase.mul_right ((s : ℝ)⁻¹)
  have hlimit := hshift.hasSum.tendsto_sum_nat
  rw [smooth_prime_power_coefficient_tsum s hs] at hlimit
  have hselector :
      Tendsto (fun E : ℕ => ((s : ℝ) - 2) / ((s : ℝ) - 1) +
        ∑ e ∈ Finset.range E, ((s : ℝ)⁻¹) ^ (e + 1)) atTop
        (nhds (((s : ℝ) - 2) / ((s : ℝ) - 1) + ((s : ℝ) - 1)⁻¹)) :=
    tendsto_const_nhds.add hlimit
  have hone : ((s : ℝ) - 2) / ((s : ℝ) - 1) + ((s : ℝ) - 1)⁻¹ = 1 := by
    have hnormalized := deficiency_local_selector_eq_one s hs
    rw [smooth_prime_power_coefficient_tsum s hs] at hnormalized
    exact hnormalized
  rw [hone] at hselector
  exact hselector

/-- The complete finite diagonal rectangle converges to the exact full
smooth-core coefficient one. -/
theorem truncated_initial_deficiency_coefficient_tendsto (S : Finset ℕ)
    (hS : ∀ s ∈ S, 1 < s) :
    Tendsto (truncatedInitialDeficiencyCoefficient S) atTop (nhds 1) := by
  have hproduct := tendsto_finsetProd S fun s hs =>
    truncated_smooth_deficiency_selector_tendsto s (hS s hs)
  have hcombined := truncated_dyadic_deficiency_coefficient_tendsto.mul hproduct
  change Tendsto
    (fun E => truncatedDyadicDeficiencyCoefficient E *
      ∏ s ∈ S, truncatedSmoothDeficiencySelector s E) atTop (nhds 1)
  simpa using hcombined

/-- Every positive accuracy is attained by a *finite* dyadic/smooth exponent
rectangle. -/
theorem exists_truncated_initial_deficiency_coefficient_gt (S : Finset ℕ)
    (hS : ∀ s ∈ S, 1 < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : ℕ, 1 - ε < truncatedInitialDeficiencyCoefficient S E := by
  have hevent : ∀ᶠ E : ℕ in atTop,
      1 - ε < truncatedInitialDeficiencyCoefficient S E :=
    (tendsto_order.mp (truncated_initial_deficiency_coefficient_tendsto S hS)).1
      (1 - ε) (by linarith)
  obtain ⟨E, hE⟩ := eventually_atTop.mp hevent
  exact ⟨E, hE E (le_refl E)⟩

/-- Arbitrarily weight-complete admissible *finite* smooth-core families give
the genuine one-sided initial-deficiency asymptotic. -/
theorem initial_deficiency_eventual_one_lower_of_finite_family_approximation
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (happrox : ∀ δ : ℝ, 0 < δ →
      ∃ F : Finset (ℕ × ℕ),
        (∀ v ∈ F, admissibleSmoothDeficiencyCore S b v) ∧
          1 - δ < ∑ v ∈ F,
            (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) * ((v.1 : ℝ)⁻¹))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (deficiency n (initialAssignment S b) : ℝ) /
        ((n : ℝ) / Real.log n) := by
  obtain ⟨F, hfamily, hweight⟩ := happrox (ε / 2) (by linarith)
  have hfinite := initial_deficiency_eventual_lower_bound_of_finite_smooth_family
    S b F hsupport hfamily (ε / 2) (by linarith)
  filter_upwards [hfinite] with n hn
  linarith

/-- Precise reduction of the actual initial-deficiency liminf to the sole
remaining finite combinatorial rectangle-realization identity. -/
theorem initial_deficiency_eventual_one_lower_of_rectangular_realization
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hrectangle : ∀ E : ℕ, ∃ F : Finset (ℕ × ℕ),
      (∀ v ∈ F, admissibleSmoothDeficiencyCore S b v) ∧
        (∑ v ∈ F,
          (1 / (((∏ s ∈ S, s).totient : ℕ) : ℝ)) * ((v.1 : ℝ)⁻¹)) =
          truncatedInitialDeficiencyCoefficient S E)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ (deficiency n (initialAssignment S b) : ℝ) /
        ((n : ℝ) / Real.log n) := by
  apply initial_deficiency_eventual_one_lower_of_finite_family_approximation
    S b hsupport _ ε hε
  intro δ hδ
  obtain ⟨E, hE⟩ := exists_truncated_initial_deficiency_coefficient_gt S
    (fun s hs => (hsupport s hs).one_lt) hδ
  obtain ⟨F, hfamily, hweight⟩ := hrectangle E
  exact ⟨F, hfamily, hweight.symm ▸ hE⟩

#print axioms truncated_dyadic_deficiency_coefficient_tendsto
#print axioms truncated_smooth_deficiency_selector_tendsto
#print axioms truncated_initial_deficiency_coefficient_tendsto
#print axioms exists_truncated_initial_deficiency_coefficient_gt
#print axioms initial_deficiency_eventual_one_lower_of_finite_family_approximation
#print axioms initial_deficiency_eventual_one_lower_of_rectangular_realization

end Erdos689
