module

public import FullCoreClassification1139
public import GoalRootPNTLimsup433

@[expose] public section


/-!
# Exact fixed-parameter initial-conductor asymptotics for Erdős #1139

The genuine mixed zero-residue core has exact conductor

  `primorial (y / z) * primorial z`.

Using the already audited prime number theorem and exact natural-division
scaling, this module proves that, for every fixed positive `z`, its actual
logarithmic conductor divided by the covered length converges to `1 / z`.
These coefficients themselves tend to zero as `z` tends to infinity.

Thus the initial core and its exact four-family deficiency classification are
both fully kernel-checked.  The still-unproved ingredient for the complete
Erdős #1139 conjecture is a simultaneous, sublinear-cost covering of those
typed deficient targets; no prime-pattern or hypergraph theorem is assumed.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- The broad prime support up to the exact integer cutoff `y / z` has
logarithmic conductor asymptotic to `y / z`, normalized by the original
covered length rather than by the rounded cutoff. -/
theorem fixedParameterCore_broad_log_ratio_tendsto
    (z : ℕ) (positive : 0 < z) :
    Tendsto
      (fun y : ℕ =>
        Real.log (primorial (y / z) : ℝ) / (y : ℝ))
      atTop (𝓝 ((z : ℝ)⁻¹)) := by
  have cutoff_at_top : Tendsto (fun y : ℕ => y / z) atTop atTop :=
    Nat.tendsto_div_const_atTop positive.ne'
  have cutoff_pnt :=
    original_primorial_log_div_length_tendsto_one.comp cutoff_at_top
  have cutoff_scale := Erdos689.nat_div_cast_ratio_tendsto z positive
  have product := cutoff_pnt.mul cutoff_scale
  convert product using 1
  · funext y
    by_cases cutoff_zero : y / z = 0
    · simp [cutoff_zero]
    · have cutoff_ne : ((y / z : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast cutoff_zero
      have y_nat_ne : y ≠ 0 := by
        intro y_zero
        apply cutoff_zero
        simp [y_zero]
      have y_ne : (y : ℝ) ≠ 0 := by
        exact_mod_cast y_nat_ne
      simp [Function.comp_apply]
      field_simp [cutoff_ne, y_ne]
  · simp

/-- The exact genuine mixed core, including the separately paid squared-small
prime support, has limiting logarithmic cost `1 / z` per covered integer. -/
theorem fixedParameterCore_actual_log_ratio_tendsto
    (z : ℕ) (positive : 0 < z) :
    Tendsto
      (fun y : ℕ =>
        Real.log
          ((∏ p ∈ fixedParameterCorePrimes y z,
            selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) /
          (y : ℝ))
      atTop (𝓝 ((z : ℝ)⁻¹)) := by
  have broad := fixedParameterCore_broad_log_ratio_tendsto z positive
  have fixed_square :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log (primorial z : ℝ))
  have combined := broad.add fixed_square
  have threshold : ∀ᶠ y : ℕ in atTop, z ≤ y / z :=
    (Nat.tendsto_div_const_atTop positive.ne').eventually
      (eventually_ge_atTop z)
  have combined_limit :
      Tendsto
        (fun y : ℕ =>
          Real.log (primorial (y / z) : ℝ) / (y : ℝ) +
            Real.log (primorial z : ℝ) / (y : ℝ))
        atTop (𝓝 ((z : ℝ)⁻¹)) := by
    simpa using combined
  apply combined_limit.congr'
  filter_upwards [threshold] with y hy
  rw [fixedParameterCore_actual_conductor hy]
  push_cast
  have broad_positive : (primorial (y / z) : ℝ) ≠ 0 := by
    exact_mod_cast primorial_ne_zero (y / z)
  have square_positive : (primorial z : ℝ) ≠ 0 := by
    exact_mod_cast primorial_ne_zero z
  rw [Real.log_mul broad_positive square_positive]
  ring

/-- The fixed-parameter leading coefficients really tend to zero; the
parameter is sent to infinity only AFTER each fixed-parameter limit. -/
theorem fixedParameterCore_coefficient_tendsto_zero :
    Tendsto (fun z : ℕ => (z : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Every prescribed positive logarithmic-cost density is eventually achieved
by the genuine initial fixed-parameter core, including its exact square
exponents.  The core remains PARTIAL: covering its four precisely classified
deficient target families with negligible extra cost is the outstanding
analytic prime-pattern/matching obstruction. -/
theorem exists_fixedParameterCore_eventually_sublinear_cost
    (ε : ℝ) (positive : 0 < ε) :
    ∃ z : ℕ, 0 < z ∧
      ∀ᶠ y : ℕ in atTop,
        z ≤ y / z ∧
        Real.log
          ((∏ p ∈ fixedParameterCorePrimes y z,
            selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ)
          < ε * (y : ℝ) := by
  have eventually_small :=
    (tendsto_order.mp fixedParameterCore_coefficient_tendsto_zero).2
      ε positive
  have exists_parameter :
      ∀ᶠ z : ℕ in atTop, 0 < z ∧ (z : ℝ)⁻¹ < ε :=
    (eventually_gt_atTop 0).and eventually_small
  obtain ⟨z, hz, hcoefficient⟩ := exists_parameter.exists
  have ratio := fixedParameterCore_actual_log_ratio_tendsto z hz
  have eventually_ratio :=
    (tendsto_order.mp ratio).2 ε hcoefficient
  have eventually_threshold : ∀ᶠ y : ℕ in atTop, z ≤ y / z :=
    (Nat.tendsto_div_const_atTop hz.ne').eventually
      (eventually_ge_atTop z)
  refine ⟨z, hz, ?_⟩
  filter_upwards [eventually_threshold, eventually_ratio,
      eventually_gt_atTop 0] with y hthreshold hratio hy
  refine ⟨hthreshold, ?_⟩
  have hyreal : (0 : ℝ) < y := by exact_mod_cast hy
  exact (div_lt_iff₀ hyreal).mp hratio


end Erdos1139
