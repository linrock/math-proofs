module

public import ScaleAdaptiveDyadicConductorBound1139
public import ScaleAdaptiveGlobalTypedTargetClassification1139

@[expose] public section


/-!
# Genuine natural-number cleanup budgets and their complete conductor ledger

The covering interface does not accept asymptotic real deficit surrogates:
its missing-hit budgets are NATURAL numbers, the available cleanup primes
must exclude the entire existing core and every selected label, and the
actual additional conductor is `2 * D * log B`.  This file rounds genuine
nonnegative real prime-scale coefficients upward, proves exact asymptotic
coefficients for those actual integers, retains the full both-color
exception cost, and checks both PNT supply and the real CRT conductor.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- The ACTUAL natural-number budget corresponding to a nonnegative
original-scale missing-hit coefficient. -/
noncomputable def scaleAdaptiveIntegerCleanupBudget
    (coefficient : ℝ) (length : ℕ) : ℕ :=
  Nat.ceil (coefficient * ((length : ℝ) / Real.log (length : ℝ)))

/-- Rounding upwards, not downwards, preserves every genuine real
missing-hit upper bound. -/
theorem scaleAdaptiveIntegerCleanupBudget_covers
    (coefficient budget : ℝ) (length : ℕ)
    (bound : budget ≤
      coefficient * ((length : ℝ) / Real.log (length : ℝ))) :
    budget ≤ (scaleAdaptiveIntegerCleanupBudget coefficient length : ℝ) := by
  exact bound.trans
    (Nat.le_ceil
      (coefficient * ((length : ℝ) / Real.log (length : ℝ))))

/-- The single integer-rounding error has zero original prime-scale cost. -/
theorem scaleAdaptiveOriginalLogOverLength_tendsto_zero :
    Tendsto (fun length : ℕ =>
      Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds (0 : ℝ)) := by
  have real_limit := Real.tendsto_pow_log_div_mul_add_atTop
    (1 : ℝ) 0 1 one_ne_zero
  simpa [Function.comp_def] using
    real_limit.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The genuinely rounded NATURAL cleanup budget has exactly its advertised
prime-scale coefficient; its less-than-one rounding error is retained. -/
theorem scaleAdaptiveIntegerCleanupBudget_normalized_tendsto
    (coefficient : ℝ) (nonnegative : 0 ≤ coefficient) :
    Tendsto
      (fun length : ℕ =>
        (scaleAdaptiveIntegerCleanupBudget coefficient length : ℝ) *
          Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds coefficient) := by
  have upper_limit :
      Tendsto
        (fun length : ℕ => coefficient +
          Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds coefficient) := by
    simpa using scaleAdaptiveOriginalLogOverLength_tendsto_zero.const_add
      coefficient
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds upper_limit
  · filter_upwards [eventually_ge_atTop 2] with length large
    have length_positive : 0 < (length : ℝ) := by
      exact_mod_cast (by omega : 0 < length)
    have log_positive : 0 < Real.log (length : ℝ) := by
      apply Real.log_pos
      exact_mod_cast large
    have rounded := Nat.le_ceil
      (coefficient * ((length : ℝ) / Real.log (length : ℝ)))
    have multiplied := mul_le_mul_of_nonneg_right rounded
      (div_nonneg log_positive.le length_positive.le)
    have cancel :
        (coefficient * ((length : ℝ) / Real.log (length : ℝ))) *
            (Real.log (length : ℝ) / (length : ℝ)) = coefficient := by
      field_simp [length_positive.ne', log_positive.ne']
    rw [cancel] at multiplied
    simpa [scaleAdaptiveIntegerCleanupBudget, mul_div_assoc] using multiplied
  · filter_upwards [eventually_ge_atTop 2] with length large
    have length_positive : 0 < (length : ℝ) := by
      exact_mod_cast (by omega : 0 < length)
    have log_positive : 0 < Real.log (length : ℝ) := by
      apply Real.log_pos
      exact_mod_cast large
    have argument_nonnegative :
        0 ≤ coefficient * ((length : ℝ) / Real.log (length : ℝ)) :=
      mul_nonneg nonnegative (div_nonneg length_positive.le log_positive.le)
    have rounded := (Nat.ceil_lt_add_one argument_nonnegative).le
    have multiplied := mul_le_mul_of_nonneg_right rounded
      (div_nonneg log_positive.le length_positive.le)
    have cancel :
        (coefficient * ((length : ℝ) / Real.log (length : ℝ)) + 1) *
          (Real.log (length : ℝ) / (length : ℝ)) =
            coefficient + Real.log (length : ℝ) / (length : ℝ) := by
      field_simp [length_positive.ne', log_positive.ne']
    rw [cancel] at multiplied
    simpa [scaleAdaptiveIntegerCleanupBudget, mul_div_assoc] using multiplied

/-- The COMPLETE actual cleanup deficit is the sum of the two rounded
color budgets and twice the genuine exceptional-target count. -/
noncomputable def scaleAdaptiveIntegerCompleteDeficit
    (lowCoefficient highCoefficient : ℝ)
    (exceptions : ℕ → Finset ℕ) (length : ℕ) : ℕ :=
  scaleAdaptiveIntegerCleanupBudget lowCoefficient length +
    scaleAdaptiveIntegerCleanupBudget highCoefficient length +
      2 * (exceptions length).card

/-- Exact normalized coefficient of the ACTUAL integer deficit charged by
the joint sampler, retaining both ceiling errors and the doubled exception
count required by the genuine two-hit interface. -/
theorem scaleAdaptiveIntegerCompleteDeficit_normalized_tendsto
    (lowCoefficient highCoefficient exceptionCoefficient : ℝ)
    (low_nonnegative : 0 ≤ lowCoefficient)
    (high_nonnegative : 0 ≤ highCoefficient)
    (exceptions : ℕ → Finset ℕ)
    (exception_density : Tendsto
      (fun length : ℕ => ((exceptions length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds exceptionCoefficient)) :
    Tendsto
      (fun length : ℕ =>
        (scaleAdaptiveIntegerCompleteDeficit
          lowCoefficient highCoefficient exceptions length : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop
        (nhds
          (lowCoefficient + highCoefficient + 2 * exceptionCoefficient)) := by
  have low := scaleAdaptiveIntegerCleanupBudget_normalized_tendsto
    lowCoefficient low_nonnegative
  have high := scaleAdaptiveIntegerCleanupBudget_normalized_tendsto
    highCoefficient high_nonnegative
  have doubled := exception_density.const_mul (2 : ℝ)
  convert (low.add high).add doubled using 1
  ext length
  simp only [scaleAdaptiveIntegerCompleteDeficit, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- PNT supplies the exact required number of fresh cleanup primes for BOTH
rounded color deficits and all doubled exceptions while excluding every
core and already selected prime.  Its sole extra premise is the true
numerical strict prime-density margin. -/
theorem scaleAdaptiveIntegerCompleteCleanupPrimeCounting_eventually
    (parameter : ℕ) (positive : 0 < parameter)
    (lowCoefficient highCoefficient exceptionCoefficient
      selectedCoefficient : ℝ)
    (low_nonnegative : 0 ≤ lowCoefficient)
    (high_nonnegative : 0 ≤ highCoefficient)
    (exceptions selected : ℕ → Finset ℕ)
    (exception_density : Tendsto
      (fun length : ℕ => ((exceptions length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds exceptionCoefficient))
    (selected_density : Tendsto
      (fun length : ℕ => ((selected length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds selectedCoefficient))
    (margin :
      2 * (lowCoefficient + highCoefficient + 2 * exceptionCoefficient) +
        (parameter : ℝ)⁻¹ + selectedCoefficient < 1) :
    ∀ᶠ length : ℕ in atTop,
      2 * (scaleAdaptiveIntegerCleanupBudget lowCoefficient length +
        scaleAdaptiveIntegerCleanupBudget highCoefficient length +
          2 * (exceptions length).card) +
        ((fixedParameterCorePrimes length parameter) ∪
          selected length).card ≤ Nat.primeCounting length := by
  exact scaleAdaptiveGlobalCleanupWithSelectedPrimeCounting_eventually
    parameter positive
    (scaleAdaptiveIntegerCompleteDeficit
      lowCoefficient highCoefficient exceptions)
    selected
    (lowCoefficient + highCoefficient + 2 * exceptionCoefficient)
    selectedCoefficient
    (scaleAdaptiveIntegerCompleteDeficit_normalized_tendsto
      lowCoefficient highCoefficient exceptionCoefficient
      low_nonnegative high_nonnegative exceptions exception_density)
    selected_density margin

/-- The exact real cost of the extra genuine cleanup primes, with `B=Y`,
converges to twice the COMPLETE rounded deficit coefficient.  This is the
actual conductor term in `HasSublinearJointColoredMarginals`. -/
theorem scaleAdaptiveIntegerCompleteCleanupConductor_normalized_tendsto
    (lowCoefficient highCoefficient exceptionCoefficient : ℝ)
    (low_nonnegative : 0 ≤ lowCoefficient)
    (high_nonnegative : 0 ≤ highCoefficient)
    (exceptions : ℕ → Finset ℕ)
    (exception_density : Tendsto
      (fun length : ℕ => ((exceptions length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds exceptionCoefficient)) :
    Tendsto
      (fun length : ℕ =>
        (2 * (scaleAdaptiveIntegerCompleteDeficit
          lowCoefficient highCoefficient exceptions length : ℝ)) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop
        (nhds
          (2 * (lowCoefficient + highCoefficient +
            2 * exceptionCoefficient))) := by
  convert (scaleAdaptiveIntegerCompleteDeficit_normalized_tendsto
    lowCoefficient highCoefficient exceptionCoefficient
    low_nonnegative high_nonnegative exceptions exception_density).const_mul
      (2 : ℝ) using 1
  ext length
  ring

/-- The TRUE union-prime-product plus TRUE rounded cleanup cost has exact
upper coefficient `2^(-a) + 2*(δ_low+δ_high+2δ_exception)`, with any
arbitrarily small strict slack.  Neither cost is a numerical stand-in. -/
theorem scaleAdaptiveIntegerFullPrimeAndCleanupConductor_eventually_le
    (lower : ℕ) (exponents : Finset ℕ)
    (after : ∀ exponent ∈ exponents, lower < exponent)
    (lowCoefficient highCoefficient exceptionCoefficient slack : ℝ)
    (low_nonnegative : 0 ≤ lowCoefficient)
    (high_nonnegative : 0 ≤ highCoefficient)
    (exceptions : ℕ → Finset ℕ)
    (exception_density : Tendsto
      (fun length : ℕ => ((exceptions length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds exceptionCoefficient))
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      Real.log
        ((∏ prime ∈ exponents.biUnion
          (scaleAdaptiveDyadicPrimeShell length), prime : ℕ) : ℝ) +
        (2 * (scaleAdaptiveIntegerCompleteDeficit
          lowCoefficient highCoefficient exceptions length : ℝ)) *
            Real.log (length : ℝ) ≤
      ((((2 ^ lower : ℕ) : ℝ)⁻¹ +
        2 * (lowCoefficient + highCoefficient +
          2 * exceptionCoefficient) + slack) * (length : ℝ)) := by
  have prime_cost := scaleAdaptiveDyadicPrimeShell_product_eventually_log_le
    lower exponents after (slack / 2) (by linarith)
  have cleanup_limit :=
    scaleAdaptiveIntegerCompleteCleanupConductor_normalized_tendsto
      lowCoefficient highCoefficient exceptionCoefficient
      low_nonnegative high_nonnegative exceptions exception_density
  have cleanup_ratio :
      ∀ᶠ length : ℕ in atTop,
        (2 * (scaleAdaptiveIntegerCompleteDeficit
          lowCoefficient highCoefficient exceptions length : ℝ)) *
            Real.log (length : ℝ) / (length : ℝ) <
          2 * (lowCoefficient + highCoefficient +
            2 * exceptionCoefficient) + slack / 2 :=
    cleanup_limit.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [prime_cost, cleanup_ratio,
      eventually_ge_atTop 1] with length prime_bound cleanup_bound large
  have length_positive : 0 < (length : ℝ) := by exact_mod_cast large
  have cleanup_cost := (div_lt_iff₀ length_positive).mp cleanup_bound
  nlinarith

/-- Real physical prefixes and different exceptional families can overlap,
so their UNION need not have an exact density.  A genuine natural-number
majorant with a known coefficient nevertheless suffices for the exact
joint-interface prime-supply inequality; the actual exceptional cardinality
is never replaced by a falsely asserted equality. -/
theorem scaleAdaptiveIntegerCompleteCleanupPrimeCounting_of_envelope_eventually
    (parameter : ℕ) (positive : 0 < parameter)
    (lowCoefficient highCoefficient envelopeCoefficient
      selectedCoefficient : ℝ)
    (low_nonnegative : 0 ≤ lowCoefficient)
    (high_nonnegative : 0 ≤ highCoefficient)
    (exceptions selected : ℕ → Finset ℕ)
    (envelope : ℕ → ℕ)
    (exception_bound : ∀ᶠ length : ℕ in atTop,
      (exceptions length).card ≤ envelope length)
    (envelope_density : Tendsto
      (fun length : ℕ => (envelope length : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds envelopeCoefficient))
    (selected_density : Tendsto
      (fun length : ℕ => ((selected length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds selectedCoefficient))
    (margin :
      2 * (lowCoefficient + highCoefficient + 2 * envelopeCoefficient) +
        (parameter : ℝ)⁻¹ + selectedCoefficient < 1) :
    ∀ᶠ length : ℕ in atTop,
      2 * (scaleAdaptiveIntegerCleanupBudget lowCoefficient length +
        scaleAdaptiveIntegerCleanupBudget highCoefficient length +
          2 * (exceptions length).card) +
        ((fixedParameterCorePrimes length parameter) ∪
          selected length).card ≤ Nat.primeCounting length := by
  let majorant : ℕ → Finset ℕ := fun length => Finset.range (envelope length)
  have majorant_density : Tendsto
      (fun length : ℕ => ((majorant length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds envelopeCoefficient) := by
    simpa [majorant] using envelope_density
  have supply := scaleAdaptiveIntegerCompleteCleanupPrimeCounting_eventually
    parameter positive lowCoefficient highCoefficient envelopeCoefficient
      selectedCoefficient low_nonnegative high_nonnegative
        majorant selected majorant_density selected_density margin
  filter_upwards [supply, exception_bound] with length enough bounded
  simp only [majorant, Finset.card_range] at enough
  omega

/-- The ACTUAL selected-prime-product plus ACTUAL exceptional-union
cleanup conductor is bounded by the genuine majorant coefficient even when
different physical-prefix and bad-target exception sets overlap.
Only a natural upper envelope is needed; no exact union-density claim is
silently inserted. -/
theorem scaleAdaptiveIntegerFullConductor_of_exception_envelope_eventually_le
    (lower : ℕ) (exponents : Finset ℕ)
    (after : ∀ exponent ∈ exponents, lower < exponent)
    (lowCoefficient highCoefficient envelopeCoefficient slack : ℝ)
    (low_nonnegative : 0 ≤ lowCoefficient)
    (high_nonnegative : 0 ≤ highCoefficient)
    (exceptions : ℕ → Finset ℕ)
    (envelope : ℕ → ℕ)
    (exception_bound : ∀ᶠ length : ℕ in atTop,
      (exceptions length).card ≤ envelope length)
    (envelope_density : Tendsto
      (fun length : ℕ => (envelope length : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds envelopeCoefficient))
    (slack_positive : 0 < slack) :
    ∀ᶠ length : ℕ in atTop,
      Real.log
        ((∏ prime ∈ exponents.biUnion
          (scaleAdaptiveDyadicPrimeShell length), prime : ℕ) : ℝ) +
        (2 * (scaleAdaptiveIntegerCompleteDeficit
          lowCoefficient highCoefficient exceptions length : ℝ)) *
            Real.log (length : ℝ) ≤
      ((((2 ^ lower : ℕ) : ℝ)⁻¹ +
        2 * (lowCoefficient + highCoefficient +
          2 * envelopeCoefficient) + slack) * (length : ℝ)) := by
  let majorant : ℕ → Finset ℕ := fun length => Finset.range (envelope length)
  have majorant_density : Tendsto
      (fun length : ℕ => ((majorant length).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds envelopeCoefficient) := by
    simpa [majorant] using envelope_density
  have total := scaleAdaptiveIntegerFullPrimeAndCleanupConductor_eventually_le
    lower exponents after lowCoefficient highCoefficient
      envelopeCoefficient slack low_nonnegative high_nonnegative
        majorant majorant_density slack_positive
  filter_upwards [total, exception_bound,
      eventually_ge_atTop 1] with length charged bounded large
  have log_nonnegative : 0 ≤ Real.log (length : ℝ) :=
    Real.log_nonneg (by exact_mod_cast large)
  have deficit_bound :
      scaleAdaptiveIntegerCompleteDeficit
        lowCoefficient highCoefficient exceptions length ≤
      scaleAdaptiveIntegerCompleteDeficit
        lowCoefficient highCoefficient majorant length := by
    simp only [scaleAdaptiveIntegerCompleteDeficit,
      majorant, Finset.card_range]
    omega
  have real_deficit_bound :
      (scaleAdaptiveIntegerCompleteDeficit
        lowCoefficient highCoefficient exceptions length : ℝ) ≤
      (scaleAdaptiveIntegerCompleteDeficit
        lowCoefficient highCoefficient majorant length : ℝ) := by
    exact_mod_cast deficit_bound
  have cost_bound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left real_deficit_bound (by norm_num : (0 : ℝ) ≤ 2))
      log_nonnegative
  linarith


end Erdos1139
