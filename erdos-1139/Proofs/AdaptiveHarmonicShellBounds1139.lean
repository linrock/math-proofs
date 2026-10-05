module

public import AdaptiveMertens1139
public import ScaleAdaptiveParameterDecay1139
public import Mathlib.Algebra.Order.Field.GeomSum

@[expose] public section


/-!
# Genuine prime-harmonic shells and the adaptive low-type exponential budget

The adaptive rounding manuscript groups actual prime semiprime types into
unit-width LOG-LOG shells.  An ordinary full harmonic bound loses the proof;
one needs a shell-uniform bound from the genuine second Mertens theorem,
followed by a geometric exponential sum.

This file keeps the real finite prime supports, both open/closed endpoints,
the true quantitative signed Mertens errors, and every fixed positive rate.
It proves only harmonic bookkeeping, not the missing GTZ prime-pattern
first/shared-label/shared-target estimates.
-/

open Finset Filter
open scoped Topology

namespace Erdos1139

/-- The actual explicit constant in the already proved second-Mertens
signed error bound. -/
noncomputable def adaptiveMertensHarmonicErrorConstant : ℝ :=
  Real.log 4 + 6 + Mertens.E₁

/-- The genuine Mertens harmonic constant is nonnegative. -/
theorem adaptiveMertensHarmonicErrorConstant_nonnegative :
    0 ≤ adaptiveMertensHarmonicErrorConstant := by
  unfold adaptiveMertensHarmonicErrorConstant
  have log_nonnegative : 0 ≤ Real.log (4 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have series_nonnegative := Mertens.E₁.nonneg
  linarith

/-- Quantitative TWO-ENDPOINT second-Mertens error for the actual
lower-OPEN/upper-CLOSED prime-type interval; the bound is uniform in
the upper endpoint and retains the genuine lower cutoff. -/
theorem adaptivePrimeHarmonicInterval_error_abs_le
    {lower upper : ℕ} (lower_large : 2 ≤ lower)
    (ordered : lower ≤ upper) :
    |adaptivePrimeHarmonicInterval lower upper -
      (Real.log (Real.log (upper : ℝ)) -
        Real.log (Real.log (lower : ℝ)))| ≤
      2 * adaptiveMertensHarmonicErrorConstant /
        Real.log (lower : ℝ) := by
  have lower_real : (2 : ℝ) ≤ lower := by exact_mod_cast lower_large
  have upper_real : (2 : ℝ) ≤ upper := by
    exact_mod_cast (lower_large.trans ordered)
  have lower_positive : (0 : ℝ) < lower := by linarith
  have lower_log_positive : 0 < Real.log (lower : ℝ) :=
    Real.log_pos (by linarith)
  have upper_log_positive : 0 < Real.log (upper : ℝ) :=
    Real.log_pos (by linarith)
  have upper_order : (lower : ℝ) ≤ upper := by exact_mod_cast ordered
  have log_order :
      Real.log (lower : ℝ) ≤ Real.log (upper : ℝ) :=
    Real.log_le_log lower_positive upper_order
  have lower_error :
      |Mertens.E₂p (lower : ℝ)| ≤
        adaptiveMertensHarmonicErrorConstant /
          Real.log (lower : ℝ) := by
    simpa [adaptiveMertensHarmonicErrorConstant] using
      Mertens.E₂p.abs_le lower_real
  have upper_error :
      |Mertens.E₂p (upper : ℝ)| ≤
        adaptiveMertensHarmonicErrorConstant /
          Real.log (lower : ℝ) := by
    calc
      |Mertens.E₂p (upper : ℝ)| ≤
          adaptiveMertensHarmonicErrorConstant /
            Real.log (upper : ℝ) := by
              simpa [adaptiveMertensHarmonicErrorConstant] using
                Mertens.E₂p.abs_le upper_real
      _ ≤ adaptiveMertensHarmonicErrorConstant /
            Real.log (lower : ℝ) :=
        div_le_div_of_nonneg_left
          adaptiveMertensHarmonicErrorConstant_nonnegative
          lower_log_positive log_order
  calc
    |adaptivePrimeHarmonicInterval lower upper -
      (Real.log (Real.log (upper : ℝ)) -
        Real.log (Real.log (lower : ℝ)))| =
      |Mertens.E₂p (upper : ℝ) - Mertens.E₂p (lower : ℝ)| := by
        rw [adaptivePrimeHarmonicInterval_eq_log_ratio_add_errors ordered]
        congr 1
        ring
    _ ≤ |Mertens.E₂p (upper : ℝ)| +
          |Mertens.E₂p (lower : ℝ)| := abs_sub _ _
    _ ≤ adaptiveMertensHarmonicErrorConstant / Real.log (lower : ℝ) +
          adaptiveMertensHarmonicErrorConstant / Real.log (lower : ℝ) :=
      add_le_add upper_error lower_error
    _ = 2 * adaptiveMertensHarmonicErrorConstant /
          Real.log (lower : ℝ) := by ring

/-- Every genuine prime-harmonic unit LOG-LOG shell has one uniform
bounded mass, regardless of its position or upper integer endpoint. -/
theorem adaptivePrimeHarmonicUnitShell_uniform_bound
    {lower upper : ℕ} (lower_large : 2 ≤ lower)
    (ordered : lower ≤ upper)
    (unit_width :
      Real.log (Real.log (upper : ℝ)) -
        Real.log (Real.log (lower : ℝ)) ≤ 1) :
    adaptivePrimeHarmonicInterval lower upper ≤
      1 + 2 * adaptiveMertensHarmonicErrorConstant /
        Real.log (2 : ℝ) := by
  have error := adaptivePrimeHarmonicInterval_error_abs_le
    lower_large ordered
  have log_two_positive : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have lower_real : (2 : ℝ) ≤ lower := by exact_mod_cast lower_large
  have log_order : Real.log (2 : ℝ) ≤ Real.log (lower : ℝ) :=
    Real.log_le_log (by norm_num) lower_real
  have endpoint_bound :
      2 * adaptiveMertensHarmonicErrorConstant /
          Real.log (lower : ℝ) ≤
        2 * adaptiveMertensHarmonicErrorConstant /
          Real.log (2 : ℝ) :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num)
        adaptiveMertensHarmonicErrorConstant_nonnegative)
      log_two_positive log_order
  have signed := (le_abs_self _).trans error
  linarith

/-- Every actual lower-open/upper-closed prime harmonic interval is
nonnegative. -/
theorem adaptivePrimeHarmonicInterval_nonnegative
    (lower upper : ℕ) :
    0 ≤ adaptivePrimeHarmonicInterval lower upper := by
  unfold adaptivePrimeHarmonicInterval
  exact Finset.sum_nonneg
    (fun prime _ => inv_nonneg.mpr (Nat.cast_nonneg prime))

/-- The true finite geometric series for every fixed positive exponential
rate is bounded uniformly in its number of shells. -/
theorem adaptiveExpGeometricShellSum_le
    {rate : ℝ} (positive : 0 < rate) (count : ℕ) :
    (∑ index ∈ Finset.range count,
      (Real.exp (-rate)) ^ index) ≤
        1 / (1 - Real.exp (-rate)) := by
  have ratio_nonnegative : 0 ≤ Real.exp (-rate) :=
    (Real.exp_pos _).le
  have ratio_lt_one : Real.exp (-rate) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have bound := geom_sum_Ico_le_of_lt_one
    (m := 0) (n := count) ratio_nonnegative ratio_lt_one
  simpa only [Nat.Ico_zero_eq_range, pow_zero] using bound

/-- Uniformly bounded genuine log-log shell masses have the required
DECAYING weighted budget O(exp(-rate*baseline)), with no factor equal
to the number of prime types or shell count. -/
theorem adaptiveWeightedPrimeShells_le_geometric
    {rate baseline bound : ℝ} (positive : 0 < rate)
    (bound_nonnegative : 0 ≤ bound)
    (mass : ℕ → ℝ)
    (_mass_nonnegative : ∀ index, 0 ≤ mass index)
    (mass_bounded : ∀ index, mass index ≤ bound)
    (count : ℕ) :
    (∑ index ∈ Finset.range count,
      mass index *
        Real.exp (-rate * (baseline + (index : ℝ)))) ≤
      bound * Real.exp (-rate * baseline) /
        (1 - Real.exp (-rate)) := by
  have term_bound :
      ∀ index : ℕ,
        mass index * Real.exp (-rate * (baseline + (index : ℝ))) ≤
          bound * Real.exp (-rate * baseline) *
            (Real.exp (-rate)) ^ index := by
    intro index
    have exponent :
        -rate * (baseline + (index : ℝ)) =
          -rate * baseline + (index : ℝ) * (-rate) := by ring
    rw [exponent, Real.exp_add, Real.exp_nat_mul]
    have factor_nonnegative :
        0 ≤ Real.exp (-rate * baseline) *
          (Real.exp (-rate)) ^ index :=
      mul_nonneg (Real.exp_pos _).le (pow_nonneg (Real.exp_pos _).le _)
    nlinarith [mul_nonneg
      (sub_nonneg.mpr (mass_bounded index)) factor_nonnegative]
  calc
    (∑ index ∈ Finset.range count,
      mass index *
        Real.exp (-rate * (baseline + (index : ℝ)))) ≤
        ∑ index ∈ Finset.range count,
          bound * Real.exp (-rate * baseline) *
            (Real.exp (-rate)) ^ index :=
      Finset.sum_le_sum (fun index _ => term_bound index)
    _ = bound * Real.exp (-rate * baseline) *
          ∑ index ∈ Finset.range count,
            (Real.exp (-rate)) ^ index := by
      rw [Finset.mul_sum]
    _ ≤ bound * Real.exp (-rate * baseline) *
          (1 / (1 - Real.exp (-rate))) :=
      mul_le_mul_of_nonneg_left
        (adaptiveExpGeometricShellSum_le positive count)
        (mul_nonneg bound_nonnegative (Real.exp_pos _).le)
    _ = bound * Real.exp (-rate * baseline) /
          (1 - Real.exp (-rate)) := by ring

/-- Applying the previous theorem to ACTUAL prime-type unit log-log
shells proves precisely the missing shell-uniform geometric bound. -/
theorem adaptiveActualPrimeUnitShells_weighted_bound
    {rate baseline : ℝ} (positive : 0 < rate)
    (lower upper : ℕ → ℕ)
    (lower_large : ∀ index, 2 ≤ lower index)
    (ordered : ∀ index, lower index ≤ upper index)
    (unit_width : ∀ index,
      Real.log (Real.log (upper index : ℝ)) -
        Real.log (Real.log (lower index : ℝ)) ≤ 1)
    (count : ℕ) :
    (∑ index ∈ Finset.range count,
      adaptivePrimeHarmonicInterval (lower index) (upper index) *
        Real.exp (-rate * (baseline + (index : ℝ)))) ≤
      (1 + 2 * adaptiveMertensHarmonicErrorConstant /
        Real.log (2 : ℝ)) * Real.exp (-rate * baseline) /
          (1 - Real.exp (-rate)) := by
  apply adaptiveWeightedPrimeShells_le_geometric positive
    (by
      have log_two_positive : 0 < Real.log (2 : ℝ) :=
        Real.log_pos (by norm_num)
      have correction_nonnegative :
          0 ≤ 2 * adaptiveMertensHarmonicErrorConstant /
            Real.log (2 : ℝ) :=
        div_nonneg
          (mul_nonneg (by norm_num)
            adaptiveMertensHarmonicErrorConstant_nonnegative)
          log_two_positive.le
      linarith)
    (fun index => adaptivePrimeHarmonicInterval
      (lower index) (upper index))
    (fun index => adaptivePrimeHarmonicInterval_nonnegative
      (lower index) (upper index))
    (fun index => adaptivePrimeHarmonicUnitShell_uniform_bound
      (lower_large index) (ordered index) (unit_width index))

/-- The actual geometrically weighted unit-shell majorant tends to zero
at the genuine adaptive baseline U=log(x), for every fixed rate. -/
theorem adaptiveActualPrimeUnitShell_majorant_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun x : ℝ =>
        (1 + 2 * adaptiveMertensHarmonicErrorConstant /
          Real.log (2 : ℝ)) *
            Real.exp (-rate * adaptiveDeficitU x) /
              (1 - Real.exp (-rate)))
      atTop (𝓝 0) := by
  have scaled :=
    (tendsto_const_nhds
      (x := 1 + 2 * adaptiveMertensHarmonicErrorConstant /
        Real.log (2 : ℝ))).mul
      (adaptiveDeficit_low_boundary_tendsto_zero positive)
  simpa using scaled.div_const (1 - Real.exp (-rate))


end Erdos1139
