module

public import AdaptiveSupportIdentity1139
public import PrimeNumberTheoremAnd.IEANTN.Mertens

@[expose] public section


/-!
# The actual second and third Mertens inputs for the adaptive #1139 strategy

The exact Lean 4.33.1 source closure already proves both the second and third
Mertens theorems. This module translates them to the ACTUAL finite prime
supports and Euler factors of the scale-adaptive mixed-pattern construction.

Consequently prime reciprocal asymptotics and the quantitative adaptive
Euler-product law are not additional mathematical hypotheses. The genuinely
missing signed-domain Green--Tao--Ziegler first/shared-label/shared-target
prime-pattern estimates remain unproved.
-/

open Finset Filter
open scoped Topology

namespace Erdos1139

/-- The genuine adaptive prime-prefix support is exactly the CLOSED support
used by the already kernel-proved second and third Mertens theorems. -/
theorem adaptiveMertens_prime_support_eq_closed (cutoff : ℕ) :
    Nat.primesLE cutoff = (Finset.Ioc 0 cutoff).filter Nat.Prime := by
  ext prime
  simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨bounded, is_prime⟩
    exact ⟨⟨is_prime.pos, bounded⟩, is_prime⟩
  · rintro ⟨⟨_, bounded⟩, is_prime⟩
    exact ⟨bounded, is_prime⟩

/-- The actual prime-type harmonic mass through an integer cutoff. -/
noncomputable def adaptivePrimeHarmonicPrefix (cutoff : ℕ) : ℝ :=
  ∑ prime ∈ Nat.primesLE cutoff, (prime : ℝ)⁻¹

/-- EXACT second-Mertens identity for the actual supported prime types,
including the true Meissel--Mertens constant and its full signed error. -/
theorem adaptivePrimeHarmonicPrefix_eq_log_log_add_error (cutoff : ℕ) :
    adaptivePrimeHarmonicPrefix cutoff =
      Real.log (Real.log (cutoff : ℝ)) +
        Mertens.M + Mertens.E₂p (cutoff : ℝ) := by
  unfold adaptivePrimeHarmonicPrefix
  rw [adaptiveMertens_prime_support_eq_closed]
  simpa only [Nat.floor_natCast, one_div] using
    Mertens.sum_prime_div_eq (cutoff : ℝ)

/-- EXACT third-Mertens formula for the precise Euler product already used
by the genuine mixed-pattern distribution. -/
theorem adaptivePrimeEulerProduct_eq_mertens
    {cutoff : ℕ} (large : 2 ≤ cutoff) :
    adaptivePrimeEulerProduct (Nat.primesLE cutoff) =
      Real.exp (-Real.eulerMascheroniConstant) *
        Real.exp (Mertens.E₃ (cutoff : ℝ)) /
          Real.log (cutoff : ℝ) := by
  have real_large : (1 : ℝ) < cutoff := by exact_mod_cast large
  unfold adaptivePrimeEulerProduct
  rw [adaptiveMertens_prime_support_eq_closed]
  simpa only [Nat.floor_natCast, one_div] using
    Mertens.prod_one_minus_div_prime_eq real_large

/-- The genuine second-Mertens error tends to zero on integer cutoffs. -/
theorem adaptiveMertens_prime_error_tendsto_zero :
    Tendsto (fun cutoff : ℕ => Mertens.E₂p (cutoff : ℝ))
      atTop (𝓝 0) := by
  have real_limit : Tendsto Mertens.E₂p atTop (𝓝 (0 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  exact real_limit.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The genuine third-Mertens error tends to zero on integer cutoffs. -/
theorem adaptiveMertens_euler_error_tendsto_zero :
    Tendsto (fun cutoff : ℕ => Mertens.E₃ (cutoff : ℝ))
      atTop (𝓝 0) := by
  have real_limit : Tendsto Mertens.E₃ atTop (𝓝 (0 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  exact real_limit.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The actual full supported prime harmonic mass has the exact
Meissel--Mertens additive constant, with no assumed analytic input. -/
theorem adaptivePrimeHarmonicPrefix_sub_log_log_tendsto :
    Tendsto
      (fun cutoff : ℕ =>
        adaptivePrimeHarmonicPrefix cutoff -
          Real.log (Real.log (cutoff : ℝ)))
      atTop (𝓝 Mertens.M) := by
  have limit := (tendsto_const_nhds (x := Mertens.M)).add
    adaptiveMertens_prime_error_tendsto_zero
  convert limit using 1
  · ext cutoff
    rw [adaptivePrimeHarmonicPrefix_eq_log_log_add_error]
    ring
  · simp

/-- The exact mixed-pattern Euler factor satisfies the leading constant
used in BOTH adaptive color families. -/
theorem adaptivePrimeEulerProduct_mul_log_tendsto :
    Tendsto
      (fun cutoff : ℕ =>
        adaptivePrimeEulerProduct (Nat.primesLE cutoff) *
          Real.log (cutoff : ℝ))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have exponential := adaptiveMertens_euler_error_tendsto_zero.rexp
  have modeled :=
    (tendsto_const_nhds
      (x := Real.exp (-Real.eulerMascheroniConstant))).mul exponential
  have agreement :
      (fun cutoff : ℕ =>
        adaptivePrimeEulerProduct (Nat.primesLE cutoff) *
          Real.log (cutoff : ℝ)) =ᶠ[atTop]
        (fun cutoff : ℕ =>
          Real.exp (-Real.eulerMascheroniConstant) *
            Real.exp (Mertens.E₃ (cutoff : ℝ))) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with cutoff large
    rw [adaptivePrimeEulerProduct_eq_mertens large]
    have log_nonzero : Real.log (cutoff : ℝ) ≠ 0 := by
      have real_large : (1 : ℝ) < cutoff := by exact_mod_cast large
      exact (Real.log_pos real_large).ne'
    field_simp
  exact (show Tendsto _ atTop
    (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) by
      simpa only [Real.exp_zero, mul_one] using modeled).congr' agreement.symm

/-- Exact prime-type harmonic mass on an actual lower-OPEN, upper-CLOSED
adaptive support interval. -/
noncomputable def adaptivePrimeHarmonicInterval
    (lower upper : ℕ) : ℝ :=
  ∑ prime ∈ (Nat.primesLE upper) \ (Nat.primesLE lower),
    (prime : ℝ)⁻¹

/-- The genuine interval harmonic mass is EXACTLY the difference of its
two closed supported prime-prefix masses. -/
theorem adaptivePrimeHarmonicInterval_eq_prefix_sub
    {lower upper : ℕ} (ordered : lower ≤ upper) :
    adaptivePrimeHarmonicInterval lower upper =
      adaptivePrimeHarmonicPrefix upper -
        adaptivePrimeHarmonicPrefix lower := by
  have inclusion : Nat.primesLE lower ⊆ Nat.primesLE upper :=
    Nat.primesLE_mono ordered
  have split := Finset.sum_sdiff
    (f := fun prime : ℕ => (prime : ℝ)⁻¹) inclusion
  unfold adaptivePrimeHarmonicInterval adaptivePrimeHarmonicPrefix
  linarith

/-- EXACT two-endpoint second-Mertens law on the genuine supported
prime-type interval; both signed endpoint errors are retained. -/
theorem adaptivePrimeHarmonicInterval_eq_log_ratio_add_errors
    {lower upper : ℕ} (ordered : lower ≤ upper) :
    adaptivePrimeHarmonicInterval lower upper =
      Real.log (Real.log (upper : ℝ)) -
        Real.log (Real.log (lower : ℝ)) +
        (Mertens.E₂p (upper : ℝ) - Mertens.E₂p (lower : ℝ)) := by
  rw [adaptivePrimeHarmonicInterval_eq_prefix_sub ordered,
    adaptivePrimeHarmonicPrefix_eq_log_log_add_error,
    adaptivePrimeHarmonicPrefix_eq_log_log_add_error]
  ring

/-- Uniformly along ANY pair of diverging ordered integer cutoffs, the
actual prime-type harmonic interval differs from its genuine log-log
coordinate length by a vanishing signed error. -/
theorem adaptivePrimeHarmonicInterval_error_tendsto_zero
    (lower upper : ℕ → ℕ)
    (lower_growth : Tendsto lower atTop atTop)
    (upper_growth : Tendsto upper atTop atTop)
    (eventual_order : ∀ᶠ n : ℕ in atTop, lower n ≤ upper n) :
    Tendsto
      (fun n : ℕ =>
        adaptivePrimeHarmonicInterval (lower n) (upper n) -
          (Real.log (Real.log (upper n : ℝ)) -
            Real.log (Real.log (lower n : ℝ))))
      atTop (𝓝 0) := by
  have errors := (adaptiveMertens_prime_error_tendsto_zero.comp upper_growth).sub
    (adaptiveMertens_prime_error_tendsto_zero.comp lower_growth)
  have agreement :
      (fun n : ℕ =>
        adaptivePrimeHarmonicInterval (lower n) (upper n) -
          (Real.log (Real.log (upper n : ℝ)) -
            Real.log (Real.log (lower n : ℝ)))) =ᶠ[atTop]
      (fun n : ℕ =>
        Mertens.E₂p (upper n : ℝ) - Mertens.E₂p (lower n : ℝ)) := by
    filter_upwards [eventual_order] with n ordered
    rw [adaptivePrimeHarmonicInterval_eq_log_ratio_add_errors ordered]
    ring
  have error_limit :
      Tendsto
        (fun n : ℕ =>
          Mertens.E₂p (upper n : ℝ) - Mertens.E₂p (lower n : ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using errors
  exact error_limit.congr' agreement.symm


end Erdos1139
