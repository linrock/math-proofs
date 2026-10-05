module

public import ActualPrimeCorrelationBridge1139
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section


/-!
# Vanishing genuine scale-adaptive conductor and low/high deficit bounds

Use the positive square-root coordinate `x = sqrt(log(log z))`.  The actual
parameters in the independently rounded proposal become

    J = x²,   W = x² - x,   U = log x,   c = 1/x.

The conductor coefficient is `exp(-exp x)`.  The low-type harmonic bound
has terms `exp(-κ U)` and `(x+1) exp(-κ W)`.  The high-type bound is
`(U+1) exp(-κ c (W-U))`.  All four tend to zero for every fixed `κ > 0`.

These are real parameter-limit theorems, not Green--Tao prime-pattern
estimates, targetwise correlation bounds, or a proof of Erdős #1139.
-/

open Filter
open scoped Topology

namespace Erdos1139

/-- The square-root-coordinate version of `J=log(log z)`. -/
def adaptiveDeficitJ (x : ℝ) : ℝ := x ^ 2

/-- Exact `W=J-sqrt(J)` in the positive square-root coordinate. -/
def adaptiveDeficitW (x : ℝ) : ℝ := x ^ 2 - x

/-- Exact `U=(1/2)log J=log x` in the positive square-root coordinate. -/
noncomputable def adaptiveDeficitU (x : ℝ) : ℝ := Real.log x

/-- Exact `c=1/sqrt(J)` in the positive square-root coordinate. -/
noncomputable def adaptiveDeficitC (x : ℝ) : ℝ := x⁻¹

theorem adaptiveDeficitW_eq_sub_sqrt
    {x : ℝ} (nonnegative : 0 ≤ x) :
    adaptiveDeficitW x =
      adaptiveDeficitJ x - Real.sqrt (adaptiveDeficitJ x) := by
  simp [adaptiveDeficitW, adaptiveDeficitJ,
    Real.sqrt_sq_eq_abs, abs_of_nonneg nonnegative]

theorem adaptiveDeficitU_eq_half_log_J
    {x : ℝ} (_positive : 0 < x) :
    adaptiveDeficitU x =
      (1 / 2 : ℝ) * Real.log (adaptiveDeficitJ x) := by
  unfold adaptiveDeficitU adaptiveDeficitJ
  rw [Real.log_pow]
  ring

theorem adaptiveDeficitC_eq_inv_sqrt
    {x : ℝ} (nonnegative : 0 ≤ x) :
    adaptiveDeficitC x = (Real.sqrt (adaptiveDeficitJ x))⁻¹ := by
  simp [adaptiveDeficitC, adaptiveDeficitJ,
    Real.sqrt_sq_eq_abs, abs_of_nonneg nonnegative]

/-- Any fixed positive exponential rate dominates an affine prefactor. -/
theorem adaptiveDeficit_affine_exp_decay
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto (fun x : ℝ => (x + 1) * Real.exp (-rate * x))
      atTop (𝓝 0) := by
  have linear :
      Tendsto (fun x : ℝ => x * Real.exp (-rate * x))
        atTop (𝓝 0) := by
    simpa using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (1 : ℝ) rate positive
  have exponential :
      Tendsto (fun x : ℝ => Real.exp (-rate * x))
        atTop (𝓝 0) := by
    simpa using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (0 : ℝ) rate positive
  simpa [add_mul] using linear.add exponential

/-- The actual full allowed-prime conductor density vanishes. -/
theorem adaptiveDeficit_conductor_tendsto_zero :
    Tendsto (fun x : ℝ => Real.exp (-Real.exp x))
      atTop (𝓝 0) := by
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_exp_atTop

/-- The true low-family boundary contribution is `exp(-κ log x)` and
vanishes for EVERY fixed positive color-aware constant `κ`. -/
theorem adaptiveDeficit_low_boundary_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto (fun x : ℝ => Real.exp (-rate * adaptiveDeficitU x))
      atTop (𝓝 0) := by
  have growth :
      Tendsto (fun x : ℝ => rate * Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop positive
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp growth using 1
  ext x
  simp [adaptiveDeficitU, neg_mul]

/-- For all sufficiently large true parameters, the low-type early-shell
term is bounded by an ordinary exponentially decaying affine function. -/
theorem adaptiveDeficit_low_shell_eventual_bound
    {rate : ℝ} (positive : 0 < rate) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ (x + 1) * Real.exp (-rate * adaptiveDeficitW x) ∧
        (x + 1) * Real.exp (-rate * adaptiveDeficitW x) ≤
          (x + 1) * Real.exp (-rate * x) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x large
  have nonnegative : 0 ≤ x + 1 := by linarith
  have window : x ≤ adaptiveDeficitW x := by
    unfold adaptiveDeficitW
    nlinarith [mul_nonneg (sub_nonneg.mpr large) (by linarith : 0 ≤ x)]
  refine ⟨mul_nonneg nonnegative (Real.exp_pos _).le, ?_⟩
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) nonnegative
  nlinarith [mul_nonneg positive.le
    (sub_nonneg.mpr window)]

/-- The complete low-type early-shell bound tends to zero. -/
theorem adaptiveDeficit_low_shell_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun x : ℝ => (x + 1) * Real.exp (-rate * adaptiveDeficitW x))
      atTop (𝓝 0) := by
  have bounds := adaptiveDeficit_low_shell_eventual_bound positive
  exact squeeze_zero' (bounds.mono fun _ h => h.1)
    (bounds.mono fun _ h => h.2)
    (adaptiveDeficit_affine_exp_decay positive)

/-- At every sufficiently large real square-root parameter, the exact high
load `c(W-U)` is at least `x/2`; no bounded-load fixed-family estimate is
substituted for this genuinely diverging scale-adaptive load. -/
theorem adaptiveDeficit_high_load_eventually_ge_half
    : ∀ᶠ x : ℝ in atTop,
      x / 2 ≤ adaptiveDeficitC x *
        (adaptiveDeficitW x - adaptiveDeficitU x) := by
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x large
  have positive : 0 < x := by linarith
  have logarithm : Real.log x ≤ x - 1 :=
    Real.log_le_sub_one_of_pos positive
  unfold adaptiveDeficitC adaptiveDeficitW adaptiveDeficitU
  calc
    x / 2 ≤ (x ^ 2 - x - Real.log x) / x := by
      apply (le_div_iff₀ positive).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr large)
        (by linarith : 0 ≤ x)]
    _ = x⁻¹ * (x ^ 2 - x - Real.log x) := by
      rw [div_eq_mul_inv]
      ring

/-- The genuinely scale-adaptive high-type error is squeezed below a
vanishing affine-exponential majorant. -/
theorem adaptiveDeficit_high_shell_eventual_bound
    {rate : ℝ} (positive : 0 < rate) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ (adaptiveDeficitU x + 1) *
        Real.exp (-rate * adaptiveDeficitC x *
          (adaptiveDeficitW x - adaptiveDeficitU x)) ∧
      (adaptiveDeficitU x + 1) *
        Real.exp (-rate * adaptiveDeficitC x *
          (adaptiveDeficitW x - adaptiveDeficitU x)) ≤
        (x + 1) * Real.exp (-(rate / 2) * x) := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    adaptiveDeficit_high_load_eventually_ge_half] with x large load
  have x_positive : 0 < x := by linarith
  have log_nonnegative : 0 ≤ Real.log x :=
    (Real.log_nonneg (by linarith : 1 ≤ x))
  have log_upper : Real.log x ≤ x :=
    (Real.log_le_sub_one_of_pos x_positive).trans (by linarith)
  have low_nonnegative : 0 ≤ adaptiveDeficitU x + 1 := by
    unfold adaptiveDeficitU
    linarith
  refine ⟨mul_nonneg low_nonnegative (Real.exp_pos _).le, ?_⟩
  apply mul_le_mul
    (show adaptiveDeficitU x + 1 ≤ x + 1 by
      unfold adaptiveDeficitU
      linarith)
    (Real.exp_le_exp.mpr ?_)
    (Real.exp_pos _).le
    (by linarith)
  nlinarith

/-- The high-type harmonic mass grows only logarithmically, whereas the
ACTUAL scale-adaptive target load grows at least linearly in `sqrt J`. -/
theorem adaptiveDeficit_high_shell_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun x : ℝ =>
        (adaptiveDeficitU x + 1) *
          Real.exp (-rate * adaptiveDeficitC x *
            (adaptiveDeficitW x - adaptiveDeficitU x)))
      atTop (𝓝 0) := by
  have bounds := adaptiveDeficit_high_shell_eventual_bound positive
  exact squeeze_zero' (bounds.mono fun _ h => h.1)
    (bounds.mono fun _ h => h.2)
    (adaptiveDeficit_affine_exp_decay (by positivity : 0 < rate / 2))

/-- All four genuine scale-adaptive conductor and low/high cleanup
coefficients vanish SIMULTANEOUSLY. Prime-pattern realization and the
analytic moment estimates needed to instantiate this bound remain open. -/
theorem adaptiveDeficit_full_parameter_bound_tendsto_zero
    {rate : ℝ} (positive : 0 < rate) :
    Tendsto
      (fun x : ℝ =>
        Real.exp (-Real.exp x) +
          Real.exp (-rate * adaptiveDeficitU x) +
          (x + 1) * Real.exp (-rate * adaptiveDeficitW x) +
          (adaptiveDeficitU x + 1) *
            Real.exp (-rate * adaptiveDeficitC x *
              (adaptiveDeficitW x - adaptiveDeficitU x)))
      atTop (𝓝 0) := by
  simpa using (((adaptiveDeficit_conductor_tendsto_zero.add
    (adaptiveDeficit_low_boundary_tendsto_zero positive)).add
      (adaptiveDeficit_low_shell_tendsto_zero positive)).add
        (adaptiveDeficit_high_shell_tendsto_zero positive))


end Erdos1139
