module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Erdos726Unified435
public import LogDensityTrapezoidalDefectDecomposition726

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Topology Asymptotics
open Nat Filter Finset

namespace Erdos726

/-! ## Section 1: Floor-Quotient Multiplication Inequalities & Logarithm Difference Bounds -/

/-- Euclidean division upper bound: for all `n K : ℕ`,
`n = (K + 1) * (n / (K + 1)) + n % (K + 1) < (K + 1) * (n / (K + 1)) + (K + 1)`. -/
theorem lt_succ_mul_div_succ_add_succ :
    ∀ n K : ℕ, n < (K + 1) * (n / (K + 1)) + (K + 1) := by
  intro n K
  have hdiv := Nat.div_add_mod n (K + 1)
  have hmod : n % (K + 1) < K + 1 := Nat.mod_lt n (by omega)
  omega

/-- General floor-quotient multiplication inequality: for any divisor `d ≥ 1` with `d ≤ n / d`,
`n ≤ (n / d) * (d + 1)`. -/
theorem le_div_mul_succ_of_le_div :
    ∀ n d : ℕ, 1 ≤ d → d ≤ n / d → n ≤ (n / d) * (d + 1) := by
  intro n d hd hle
  have hdiv := Nat.div_add_mod n d
  have hmod : n % d < d := Nat.mod_lt n (by omega)
  have h1 : d * (n / d) + d ≤ d * (n / d) + n / d := Nat.add_le_add_left hle _
  have h2 : d * (n / d) + n / d = (n / d) * (d + 1) := by ring
  omega

/-- **Floor-Quotient Multiplication Inequality:**
Whenever `K + 1 ≤ n / (K + 1)`, `n ≤ (n / (K + 1)) * (K + 2)` since
`n = (K + 1) * (n / (K + 1)) + n % (K + 1) < (K + 1) * (n / (K + 1)) + (K + 1) ≤ (n / (K + 1)) * (K + 2)`. -/
theorem le_div_succ_mul_add_two_of_succ_le_div :
    ∀ n K : ℕ, K + 1 ≤ n / (K + 1) → n ≤ (n / (K + 1)) * (K + 2) := by
  intro n K hK
  have hlt := lt_succ_mul_div_succ_add_succ n K
  have h1 : (K + 1) * (n / (K + 1)) + (K + 1) ≤ (K + 1) * (n / (K + 1)) + n / (K + 1) :=
    Nat.add_le_add_left hK _
  have h2 : (K + 1) * (n / (K + 1)) + n / (K + 1) = (n / (K + 1)) * (K + 2) := by ring
  omega

/-- Bilateral multiplicative sandwich for `n` in terms of `n / (K + 1)` whenever `K + 1 ≤ n / (K + 1)`:
`(n / (K + 1)) * (K + 1) ≤ n ≤ (n / (K + 1)) * (K + 2)`. -/
theorem div_succ_mul_succ_le_and_le_div_succ_mul_add_two :
    ∀ n K : ℕ, K + 1 ≤ n / (K + 1) →
      (n / (K + 1)) * (K + 1) ≤ n ∧ n ≤ (n / (K + 1)) * (K + 2) := by
  intro n K hK
  refine ⟨?_, le_div_succ_mul_add_two_of_succ_le_div n K hK⟩
  rw [Nat.mul_comm]
  exact Nat.mul_div_le n (K + 1)

/-- Universal threshold extremizer at `n = (K + 1) * (K + 1) + K`:
`n / (K + 1) = K + 1`, `n % (K + 1) = K`, and `(n / (K + 1)) * (K + 2) = n + 1`, showing that
`le_div_succ_mul_add_two_of_succ_le_div` is sharp to within `1` for every `K : ℕ`. -/
theorem threshold_extremizer_div_succ_mul_add_two :
    ∀ K : ℕ,
      ((K + 1) * (K + 1) + K) / (K + 1) = K + 1 ∧
        ((K + 1) * (K + 1) + K) % (K + 1) = K ∧
        (((K + 1) * (K + 1) + K) / (K + 1)) * (K + 2) = ((K + 1) * (K + 1) + K) + 1 := by
  intro K
  have hlt : K < K + 1 := by omega
  have hdiv : ((K + 1) * (K + 1) + K) / (K + 1) = K + 1 := by
    rw [Nat.add_comm ((K + 1) * (K + 1)) K, Nat.add_mul_div_left K (K + 1) (by omega),
      Nat.div_eq_of_lt hlt, zero_add]
  have hmod : ((K + 1) * (K + 1) + K) % (K + 1) = K := by
    rw [Nat.add_comm ((K + 1) * (K + 1)) K, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  refine ⟨hdiv, hmod, ?_⟩
  rw [hdiv]
  ring

/-- Upper bound on `Real.log (n : ℝ)` from `n ≤ (n / (K + 1)) * (K + 2)` when `K + 1 ≤ n / (K + 1)`:
`Real.log (n : ℝ) ≤ Real.log ((n / (K + 1) : ℕ) : ℝ) + Real.log ((K : ℝ) + 2)`. -/
theorem real_log_le_log_div_succ_add_log_add_two :
    ∀ n K : ℕ, K + 1 ≤ n / (K + 1) →
      Real.log (n : ℝ) ≤ Real.log ((n / (K + 1) : ℕ) : ℝ) + Real.log ((K : ℝ) + 2) := by
  intro n K hK
  have hq_pos : 0 < n / (K + 1) := by omega
  have hn_pos : 0 < n := by
    have hle := Nat.div_le_self n (K + 1)
    omega
  have hmul_nat : n ≤ (n / (K + 1)) * (K + 2) :=
    le_div_succ_mul_add_two_of_succ_le_div n K hK
  have hmul_r : (n : ℝ) ≤ ((n / (K + 1) : ℕ) : ℝ) * ((K : ℝ) + 2) := by
    exact_mod_cast hmul_nat
  have hq_r_pos : (0 : ℝ) < ((n / (K + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr hq_pos
  have hk2_pos : (0 : ℝ) < (K : ℝ) + 2 := by positivity
  have hn_r_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hlog_le : Real.log (n : ℝ) ≤ Real.log (((n / (K + 1) : ℕ) : ℝ) * ((K : ℝ) + 2)) :=
    Real.log_le_log hn_r_pos hmul_r
  rw [Real.log_mul (ne_of_gt hq_r_pos) (ne_of_gt hk2_pos)] at hlog_le
  exact hlog_le

/-- **Logarithm Difference Bound:**
Whenever `K + 1 ≤ n / (K + 1)`,
`Real.log (n : ℝ) - Real.log ((n / (K + 1) : ℕ) : ℝ) ≤ Real.log ((K : ℝ) + 2)`. -/
theorem real_log_sub_log_div_succ_le_log_add_two :
    ∀ n K : ℕ, K + 1 ≤ n / (K + 1) →
      Real.log (n : ℝ) - Real.log ((n / (K + 1) : ℕ) : ℝ) ≤ Real.log ((K : ℝ) + 2) := by
  intro n K hK
  have h := real_log_le_log_div_succ_add_log_add_two n K hK
  linarith

/-- Bilateral logarithm difference sandwich whenever `K + 1 ≤ n / (K + 1)`:
`Real.log ((K : ℝ) + 1) ≤ Real.log (n : ℝ) - Real.log ((n / (K + 1) : ℕ) : ℝ) ≤ Real.log ((K : ℝ) + 2)`. -/
theorem real_log_sub_log_div_succ_sandwich :
    ∀ n K : ℕ, K + 1 ≤ n / (K + 1) →
      Real.log ((K : ℝ) + 1) ≤ Real.log (n : ℝ) - Real.log ((n / (K + 1) : ℕ) : ℝ) ∧
        Real.log (n : ℝ) - Real.log ((n / (K + 1) : ℕ) : ℝ) ≤ Real.log ((K : ℝ) + 2) := by
  intro n K hK
  refine ⟨?_, real_log_sub_log_div_succ_le_log_add_two n K hK⟩
  have hq_pos : 0 < n / (K + 1) := by omega
  have hmul_nat : (n / (K + 1)) * (K + 1) ≤ n :=
    (div_succ_mul_succ_le_and_le_div_succ_mul_add_two n K hK).1
  have hmul_r : ((n / (K + 1) : ℕ) : ℝ) * ((K : ℝ) + 1) ≤ (n : ℝ) := by
    exact_mod_cast hmul_nat
  have hq_r_pos : (0 : ℝ) < ((n / (K + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr hq_pos
  have hk1_pos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hprod_pos : (0 : ℝ) < ((n / (K + 1) : ℕ) : ℝ) * ((K : ℝ) + 1) :=
    mul_pos hq_r_pos hk1_pos
  have hlog_le : Real.log (((n / (K + 1) : ℕ) : ℝ) * ((K : ℝ) + 1)) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hprod_pos hmul_r
  rw [Real.log_mul (ne_of_gt hq_r_pos) (ne_of_gt hk1_pos)] at hlog_le
  linarith

/-- **Telescoped Reciprocal-Logarithm Difference Bound:**
Whenever `2 ≤ n / (K + 1)` and `K + 1 ≤ n / (K + 1)`,
`1 / Real.log ((n / (K + 1) : ℕ) : ℝ) - 1 / Real.log (n : ℝ) ≤ Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ))`. -/
theorem inv_log_div_succ_sub_inv_log_le :
    ∀ n K : ℕ, 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      1 / Real.log ((n / (K + 1) : ℕ) : ℝ) - 1 / Real.log (n : ℝ) ≤
        Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) := by
  intro n K h2 hK
  have hn2 : 2 ≤ n := le_trans h2 (Nat.div_le_self n (K + 1))
  have hsub := invLog_sub_eq_log_diff_div_mul (n / (K + 1)) n h2 hn2
  unfold invLog at hsub
  rw [hsub]
  have hlog_q : 0 < Real.log ((n / (K + 1) : ℕ) : ℝ) :=
    (real_log_pos_and_invLog_pos_of_two_le (n / (K + 1)) h2).1
  have hlog_n : 0 < Real.log (n : ℝ) :=
    (real_log_pos_and_invLog_pos_of_two_le n hn2).1
  have hdenom : 0 < Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ) :=
    mul_pos hlog_q hlog_n
  exact div_le_div_of_nonneg_right
    (real_log_sub_log_div_succ_le_log_add_two n K hK) (le_of_lt hdenom)

/-- Restatement of `inv_log_div_succ_sub_inv_log_le` in terms of `invLog`. -/
theorem invLog_div_succ_sub_invLog_le_log_add_two_div :
    ∀ n K : ℕ, 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      invLog (n / (K + 1)) - invLog n ≤
        Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) :=
  inv_log_div_succ_sub_inv_log_le

/-- Bilateral sandwich for the telescoped reciprocal-logarithm difference whenever
`2 ≤ n / (K + 1)` and `K + 1 ≤ n / (K + 1)`. -/
theorem inv_log_div_succ_sub_inv_log_sandwich :
    ∀ n K : ℕ, 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      Real.log ((K : ℝ) + 1) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) ≤
        1 / Real.log ((n / (K + 1) : ℕ) : ℝ) - 1 / Real.log (n : ℝ) ∧
      1 / Real.log ((n / (K + 1) : ℕ) : ℝ) - 1 / Real.log (n : ℝ) ≤
        Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) := by
  intro n K h2 hK
  refine ⟨?_, inv_log_div_succ_sub_inv_log_le n K h2 hK⟩
  have hn2 : 2 ≤ n := le_trans h2 (Nat.div_le_self n (K + 1))
  have hsub := invLog_sub_eq_log_diff_div_mul (n / (K + 1)) n h2 hn2
  unfold invLog at hsub
  rw [hsub]
  have hlog_q : 0 < Real.log ((n / (K + 1) : ℕ) : ℝ) :=
    (real_log_pos_and_invLog_pos_of_two_le (n / (K + 1)) h2).1
  have hlog_n : 0 < Real.log (n : ℝ) :=
    (real_log_pos_and_invLog_pos_of_two_le n hn2).1
  have hdenom : 0 < Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ) :=
    mul_pos hlog_q hlog_n
  exact div_le_div_of_nonneg_right
    (real_log_sub_log_div_succ_sandwich n K hK).1 (le_of_lt hdenom)

/-- Cumulative reciprocal-logarithm second-difference bound across `1 ≤ k ≤ K`:
`∑_{k=1}^K |approxSecondDiff invLog n k| ≤ Real.log (K + 2) / (Real.log ⌊n/(K + 1)⌋ * Real.log n)`. -/
theorem sum_abs_invLog_secondDiff_le_log_add_two_div :
    ∀ n K : ℕ, 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      ∑ k ∈ Finset.Icc 1 K, |approxSecondDiff invLog n k| ≤
        Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) := by
  intro n K h2 hK
  exact le_trans (sum_abs_invLog_secondDiff_le n K h2)
    (inv_log_div_succ_sub_inv_log_le n K h2 hK)

/-! ## Section 2: Quantitative Bounds on the Cumulative Trapezoidal Defect & Large-Prime Reciprocal Sums -/

/-- **Cumulative Logarithmic-Density Trapezoidal Defect Bound in Terms of `log(K + 2)`:**
Whenever `2 ≤ n / (K + 1)` and `K + 1 ≤ n / (K + 1)`,
`∑_{k=1}^K |approxTrapezoidalDefect (fun m => m / log m) n k / n| ≤ (K(K + 2) / n) / log ⌊n/(K + 1)⌋ + log(K + 2) / (log ⌊n/(K + 1)⌋ * log n)`. -/
theorem sum_abs_logDensity_trapezoidalDefect_div_le_log_add_two :
    ∀ n K : ℕ, 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      ∑ k ∈ Finset.Icc 1 K,
        |approxTrapezoidalDefect (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) n k / (n : ℝ)| ≤
        ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
          Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) := by
  intro n K h2 hK
  have htrap := sum_abs_logDensity_trapezoidalDefect_div_le n K h2
  have hinv := inv_log_div_succ_sub_inv_log_le n K h2 hK
  linarith

/-- Quantitative bound on the cumulative midpoint prime-count window approximation
`|∑_{k=1}^K midpointWindowApprox n k|` in terms of `Real.log ((K : ℝ) + 2)`. -/
theorem abs_sum_midpointWindowApprox_le_log_add_two :
    ∀ (n K : ℕ) (δ : ℝ),
      0 ≤ δ → 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      (∀ m : ℕ, m ≤ n →
        |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ * (m : ℝ)) →
      |∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k| ≤
        ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
          Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by
  intro n K δ hδ h2 hK hR
  have hmid := abs_sum_midpointWindowApprox_le_logDensity_floor_and_invLog n K δ hδ h2 hR
  have hinv := inv_log_div_succ_sub_inv_log_le n K h2 hK
  unfold invLog at hmid
  linarith

/-- **Quantitative Bound on the Large-Prime Signed Window Reciprocal Discrepancy:**
For all `n K : ℕ` and `δ ≥ 0` with `2 ≤ n / (K + 1)` and `K + 1 ≤ n / (K + 1)`, the signed
large-prime reciprocal sum discrepancy across `1 ≤ k ≤ K` (`n / (K + 1) < p ≤ n`) is bounded by
`(K(K + 2) / n) / log ⌊n/(K + 1)⌋ + log(K + 2) / (log ⌊n/(K + 1)⌋ * log n) + 4 K δ + (π(n) - π(⌊n/(K + 1)⌋)) / n`. -/
theorem abs_sum_largePrime_window_discrepancy_le_log_add_two :
    ∀ (n K : ℕ) (δ : ℝ),
      0 ≤ δ → 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      (∀ m : ℕ, m ≤ n →
        |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ * (m : ℝ)) →
      |∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k)| ≤
        ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
          Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ) := by
  intro n K δ hδ h2 hK hR
  have hn : 1 ≤ n := by
    have hle := Nat.div_le_self n (K + 1)
    omega
  have hwin := abs_sum_window_discrepancy_le_abs_sum_midpoint_add_primeCount n K hn
  have hmid := abs_sum_midpointWindowApprox_le_log_add_two n K δ hδ h2 hK hR
  have htwo :
      ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) +
        ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) =
      ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ) := by ring
  linarith

/-- Exact identity relating the large-prime upper reciprocal sum `∑_{k=1}^K upperQuotientSum n k`
and half the total large-prime reciprocal sum `(∑_{k=1}^K quotientFiberSum n k) / 2` to half
the signed window discrepancy. -/
theorem sum_upperQuotientSum_sub_half_fiberSum_eq_half_window_discrepancy :
    ∀ n K : ℕ,
      (∑ k ∈ Finset.Icc 1 K, upperQuotientSum n k) -
        (∑ k ∈ Finset.Icc 1 K, quotientFiberSum n k) / 2 =
        (∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k)) / 2 := by
  intro n K
  have hfiber :
      ∑ k ∈ Finset.Icc 1 K, quotientFiberSum n k =
        (∑ k ∈ Finset.Icc 1 K, upperQuotientSum n k) +
          ∑ k ∈ Finset.Icc 1 K, lowerQuotientSum n k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => (upperQuotientSum_add_lowerQuotientSum n k).symm
  rw [hfiber, Finset.sum_sub_distrib]
  ring

/-- **Quantitative Bound on the Large-Prime Upper Reciprocal Sum:**
Bounds the deviation of `∑_{k=1}^K upperQuotientSum n k` from half the large-prime reciprocal sum
`(∑_{k=1}^K quotientFiberSum n k) / 2` using the `log(K + 2)` telescoped reciprocal-logarithm bound. -/
theorem abs_sum_upperQuotientSum_sub_half_fiberSum_le_log_add_two :
    ∀ (n K : ℕ) (δ : ℝ),
      0 ≤ δ → 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      (∀ m : ℕ, m ≤ n →
        |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ * (m : ℝ)) →
      |(∑ k ∈ Finset.Icc 1 K, upperQuotientSum n k) -
        (∑ k ∈ Finset.Icc 1 K, quotientFiberSum n k) / 2| ≤
        (((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
          Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ)) / 2 := by
  intro n K δ hδ h2 hK hR
  rw [sum_upperQuotientSum_sub_half_fiberSum_eq_half_window_discrepancy n K,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right
    (abs_sum_largePrime_window_discrepancy_le_log_add_two n K δ hδ h2 hK hR) (by norm_num)

/-- Quantitative master discrepancy bound for `|upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2|`
in terms of the small-prime tail discrepancy `|upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K|`
and the `log(K + 2)` large-prime window majorant. -/
theorem abs_upperHalfPrimeSum_sub_half_mertens_le_tail_and_log_add_two :
    ∀ (n K : ℕ) (δ : ℝ),
      0 ≤ δ → 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) →
      (∀ m : ℕ, m ≤ n →
        |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ * (m : ℝ)) →
      |upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2| ≤
        (|upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K| +
          ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
          Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ) +
          |Mertens.M + Mertens.E₂p (n : ℝ)|) / 2 := by
  intro n K δ hδ h2 hK hR
  rw [upperHalfPrimeSum_sub_half_mertens_eq_half_diff n]
  rw [upperHalfPrimeSum_cutoff_decomposition n K,
    lowerComplementPrimeSum_cutoff_decomposition n K]
  have hsplit :
      upperSmallPrimeTailSum n K + (∑ k ∈ Finset.Icc 1 K, upperQuotientSum n k) -
        (lowerSmallPrimeTailSum n K + (∑ k ∈ Finset.Icc 1 K, lowerQuotientSum n k)) +
        Mertens.M + Mertens.E₂p (n : ℝ) =
      (upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K) +
        (∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k)) +
        (Mertens.M + Mertens.E₂p (n : ℝ)) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsplit, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  have htri1 := abs_add_le
    ((upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K) +
      ∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k))
    (Mertens.M + Mertens.E₂p (n : ℝ))
  have htri2 := abs_add_le
    (upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K)
    (∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k))
  have hwin := abs_sum_largePrime_window_discrepancy_le_log_add_two n K δ hδ h2 hK hR
  linarith

/-- Quantitative master discrepancy bound combining modular period reflection on the small-prime
tail `p ≤ n / (K + 1)` with the `log(K + 2)` telescoped reciprocal-logarithm bound. -/
theorem abs_upperHalfPrimeSum_sub_half_mertens_le_reflection_and_log_add_two :
    ∀ (n K M : ℕ) (δ : ℝ),
      0 ≤ δ → 2 ≤ n / (K + 1) → K + 1 ≤ n / (K + 1) → n ≤ M →
      (∀ p ∈ oddPrimeRange (n / (K + 1)), p ∣ M) →
      (∀ m : ℕ, m ≤ n →
        |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ * (m : ℝ)) →
      |upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2| ≤
        (|upperBoundedPrimeSum (n / (K + 1)) n - upperBoundedPrimeSum (n / (K + 1)) (M - n)| +
          dividingOddBoundedSum (n / (K + 1)) n + 1 / 2 +
          ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
          Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ) +
          |Mertens.M + Mertens.E₂p (n : ℝ)|) / 2 := by
  intro n K M δ hδ h2 hK hle hM hR
  have hmaster := abs_upperHalfPrimeSum_sub_half_mertens_le_logDensity_master
    n K M δ hδ h2 hle hM hR
  have hinv := inv_log_div_succ_sub_inv_log_le n K h2 hK
  unfold invLog at hmaster
  linarith

/-! ## Conditional asymptotic reductions toward the main conjecture -/

/-- Concrete majorant for the large-prime signed window discrepancy over `1 ≤ k ≤ K` produced by
`abs_sum_largePrime_window_discrepancy_le_log_add_two`. -/
def largePrimeWindowMajorant (n K : ℕ) (δ : ℝ) : ℝ :=
  ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
    Real.log ((K : ℝ) + 2) / (Real.log ((n / (K + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) +
    4 * (K : ℝ) * δ +
    ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ)

/-- Definitional identification of `upperHalfPrimeSum` with the exact prime-reciprocal sum in
`FormalConjectures/ErdosProblems/726.lean` (`Erdos726.erdos_726`). -/
theorem upperHalfPrimeSum_eq_formalConjectures_sum :
    upperHalfPrimeSum =
      (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
          (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / ((2 : ℕ) : ℝ) < ((n % p : ℕ) : ℝ)),
        (1 : ℝ) / (p : ℝ)) :=
  rfl

/-- Unconditional asymptotic vanishing of the normalized Mertens constant and error term
`(Mertens.M + Mertens.E₂p (n : ℝ)) / Real.log (Real.log (n : ℝ)) → 0` as `n → ∞`, derived from
`Mertens.E₂p.bound'`. -/
theorem mertens_error_div_log_log_tendsto_zero :
    Filter.Tendsto (fun n : ℕ ↦ (Mertens.M + Mertens.E₂p (n : ℝ)) / Real.log (Real.log (n : ℝ)))
      atTop (nhds 0) := by
  have hE : Filter.Tendsto (fun n : ℕ ↦ Mertens.E₂p (n : ℝ)) atTop (nhds 0) :=
    Filter.Tendsto.comp ((Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound')
      tendsto_natCast_atTop_atTop
  have hnum :
      Filter.Tendsto (fun n : ℕ ↦ Mertens.M + Mertens.E₂p (n : ℝ)) atTop (nhds (Mertens.M + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds hE
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Filter.Tendsto.comp Real.tendsto_log_atTop
      (Filter.Tendsto.comp Real.tendsto_log_atTop tendsto_natCast_atTop_atTop)
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (Real.log (Real.log (n : ℝ)))⁻¹) atTop (nhds 0) :=
    Filter.Tendsto.comp tendsto_inv_atTop_zero hlog
  have hmul := Filter.Tendsto.mul hnum hinv
  rw [mul_zero] at hmul
  simpa [div_eq_mul_inv] using hmul

/-- Exact equivalence between the `Erdos726.erdos_726` asymptotic relation and convergence to zero
of `(upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2) / Real.log (Real.log (n : ℝ))`. -/
theorem erdos_726_asymptotic_iff_sub_div_log_log_tendsto_zero :
    ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / ((2 : ℕ) : ℝ) < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔
    Filter.Tendsto
      (fun n : ℕ ↦ (upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0) := by
  change (upperHalfPrimeSum ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔ _
  constructor
  · intro heq
    have htd := heq.isLittleO.tendsto_div_nhds_zero
    have hhalf := Filter.Tendsto.const_mul (1 / 2 : ℝ) htd
    rw [mul_zero] at hhalf
    refine hhalf.congr fun n => ?_
    dsimp
    ring
  · intro h
    apply Asymptotics.IsLittleO.isEquivalent
    have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
      Filter.Tendsto.comp Real.tendsto_log_atTop
        (Filter.Tendsto.comp Real.tendsto_log_atTop tendsto_natCast_atTop_atTop)
    have hev : ∀ᶠ n : ℕ in atTop, Real.log (Real.log (n : ℝ)) / 2 = 0 →
        (upperHalfPrimeSum - fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) n = 0 := by
      filter_upwards [Filter.Tendsto.eventually_gt_atTop hlog 0] with n hn hzero
      linarith
    rw [Asymptotics.isLittleO_iff_tendsto' hev]
    have h2 := Filter.Tendsto.const_mul (2 : ℝ) h
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    dsimp
    ring

/-- Unconditional reduction of `Erdos726.erdos_726` via Mertens' second theorem: the upper-half
prime reciprocal sum is asymptotic to `log(log n) / 2` if and only if the upper-minus-lower
discrepancy `(upperHalfPrimeSum n - lowerComplementPrimeSum n) / log(log n)` tends to `0`. -/
theorem erdos_726_asymptotic_iff_discrepancy_tendsto_zero :
    ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / ((2 : ℕ) : ℝ) < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔
    Filter.Tendsto
      (fun n : ℕ ↦ (upperHalfPrimeSum n - lowerComplementPrimeSum n) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0) := by
  rw [erdos_726_asymptotic_iff_sub_div_log_log_tendsto_zero]
  constructor
  · intro hsub
    have h2 := Filter.Tendsto.const_mul (2 : ℝ) hsub
    rw [mul_zero] at h2
    have hdiff := Filter.Tendsto.sub h2 mertens_error_div_log_log_tendsto_zero
    rw [sub_zero] at hdiff
    refine hdiff.congr fun n => ?_
    rw [upperHalfPrimeSum_sub_half_mertens_eq_half_diff n]
    ring
  · intro hdisc
    have hsum := Filter.Tendsto.add hdisc mertens_error_div_log_log_tendsto_zero
    rw [add_zero] at hsum
    have hhalf := Filter.Tendsto.const_mul (1 / 2 : ℝ) hsum
    rw [mul_zero] at hhalf
    refine hhalf.congr fun n => ?_
    rw [upperHalfPrimeSum_sub_half_mertens_eq_half_diff n]
    ring

/-- Little-`o` formulation of `erdos_726_asymptotic_iff_discrepancy_tendsto_zero`:
`Erdos726.erdos_726` holds iff
`(fun n ↦ upperHalfPrimeSum n - lowerComplementPrimeSum n) =o[atTop] (fun n ↦ Real.log (Real.log (n : ℝ)))`. -/
theorem erdos_726_asymptotic_iff_discrepancy_isLittleO :
    ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / ((2 : ℕ) : ℝ) < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔
    (fun n : ℕ ↦ upperHalfPrimeSum n - lowerComplementPrimeSum n)
      =o[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) := by
  rw [erdos_726_asymptotic_iff_discrepancy_tendsto_zero]
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Filter.Tendsto.comp Real.tendsto_log_atTop
      (Filter.Tendsto.comp Real.tendsto_log_atTop tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ n : ℕ in atTop, Real.log (Real.log (n : ℝ)) = 0 →
      upperHalfPrimeSum n - lowerComplementPrimeSum n = 0 := by
    filter_upwards [Filter.Tendsto.eventually_gt_atTop hlog 0] with n hn hzero
    linarith
  exact (Asymptotics.isLittleO_iff_tendsto' hev).symm

/-- Exact additive decomposition of the full discrepancy `upperHalfPrimeSum n - lowerComplementPrimeSum n`
into the small-prime tail discrepancy `upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K`
and the large-prime window discrepancy `∑_{k=1}^K (upperQuotientSum n k - lowerQuotientSum n k)`. -/
theorem discrepancy_eq_smallPrimeTail_add_window_sum :
    ∀ n K : ℕ,
      upperHalfPrimeSum n - lowerComplementPrimeSum n =
        (upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K) +
          ∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k) := by
  intro n K
  rw [upperHalfPrimeSum_cutoff_decomposition n K,
    lowerComplementPrimeSum_cutoff_decomposition n K, Finset.sum_sub_distrib]
  ring

/-- Conditional asymptotic equivalence reducing `Erdos726.erdos_726` to `o(log log n)` small-prime
tail discrepancy whenever the large-prime window discrepancy over `1 ≤ k ≤ K n` is `o(log log n)`. -/
theorem erdos_726_asymptotic_iff_smallPrimeTail_of_window_tendsto (K : ℕ → ℕ)
    (hwin : Filter.Tendsto
      (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 (K n), (upperQuotientSum n k - lowerQuotientSum n k)) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0)) :
    ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / ((2 : ℕ) : ℝ) < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔
    Filter.Tendsto
      (fun n : ℕ ↦ (upperSmallPrimeTailSum n (K n) - lowerSmallPrimeTailSum n (K n)) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0) := by
  rw [erdos_726_asymptotic_iff_discrepancy_tendsto_zero]
  constructor
  · intro hdisc
    have hsub := Filter.Tendsto.sub hdisc hwin
    rw [sub_zero] at hsub
    refine hsub.congr fun n => ?_
    rw [discrepancy_eq_smallPrimeTail_add_window_sum n (K n)]
    ring
  · intro htail
    have hadd := Filter.Tendsto.add htail hwin
    rw [add_zero] at hadd
    refine hadd.congr fun n => ?_
    rw [discrepancy_eq_smallPrimeTail_add_window_sum n (K n)]
    ring

/-- Squeeze theorem showing that the normalized large-prime window discrepancy
`(∑_{k=1}^{K n} (upperQuotientSum n k - lowerQuotientSum n k)) / log(log n)` tends to `0` whenever
`largePrimeWindowMajorant n (K n) (δ n) / log(log n) → 0`. -/
theorem largePrime_window_discrepancy_tendsto_zero_of_log_add_two_bounds
    (K : ℕ → ℕ) (δ : ℕ → ℝ) (N₀ : ℕ)
    (hδ : ∀ n ≥ N₀, 0 ≤ δ n)
    (h2 : ∀ n ≥ N₀, 2 ≤ n / (K n + 1))
    (hK : ∀ n ≥ N₀, K n + 1 ≤ n / (K n + 1))
    (hR : ∀ n ≥ N₀, ∀ m ≤ n,
      |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ n * (m : ℝ))
    (hmaj : Filter.Tendsto
      (fun n : ℕ ↦ largePrimeWindowMajorant n (K n) (δ n) / Real.log (Real.log (n : ℝ)))
      atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 (K n), (upperQuotientSum n k - lowerQuotientSum n k)) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Filter.Tendsto.comp Real.tendsto_log_atTop
      (Filter.Tendsto.comp Real.tendsto_log_atTop tendsto_natCast_atTop_atTop)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop N₀, Filter.Tendsto.eventually_gt_atTop hlog 0] with n hn hlog_pos
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog_pos]
  have hbound := abs_sum_largePrime_window_discrepancy_le_log_add_two
    n (K n) (δ n) (hδ n hn) (h2 n hn) (hK n hn) (hR n hn)
  exact div_le_div_of_nonneg_right hbound (le_of_lt hlog_pos)

/-- **Conditional Asymptotic Equivalence Theorem for `Erdos726.erdos_726`:**
Under the quantitative `log(K n + 2)` large-prime window majorant derived from
`(n / (K n + 1)) * (K n + 2) ≥ n`, the `Erdos726.erdos_726` asymptotic relation is equivalent
(`↔`) to `o(log log n)` small-prime tail discrepancy
`(upperSmallPrimeTailSum n (K n) - lowerSmallPrimeTailSum n (K n)) / log(log n) → 0`. -/
theorem erdos_726_iff_smallPrimeTail_of_log_add_two_bounds
    (K : ℕ → ℕ) (δ : ℕ → ℝ) (N₀ : ℕ)
    (hδ : ∀ n ≥ N₀, 0 ≤ δ n)
    (h2 : ∀ n ≥ N₀, 2 ≤ n / (K n + 1))
    (hK : ∀ n ≥ N₀, K n + 1 ≤ n / (K n + 1))
    (hR : ∀ n ≥ N₀, ∀ m ≤ n,
      |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ n * (m : ℝ))
    (hmaj : Filter.Tendsto
      (fun n : ℕ ↦ largePrimeWindowMajorant n (K n) (δ n) / Real.log (Real.log (n : ℝ)))
      atTop (nhds 0)) :
    ((fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / ((2 : ℕ) : ℝ) < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2)) ↔
    Filter.Tendsto
      (fun n : ℕ ↦ (upperSmallPrimeTailSum n (K n) - lowerSmallPrimeTailSum n (K n)) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0) :=
  erdos_726_asymptotic_iff_smallPrimeTail_of_window_tendsto K
    (largePrime_window_discrepancy_tendsto_zero_of_log_add_two_bounds K δ N₀ hδ h2 hK hR hmaj)

/-- **Top-Down Conditional Reduction to `Erdos726.erdos_726` via Small-Prime Tail Discrepancy:**
Directly reduces the FormalConjectures asymptotic target for Erdős Problem #726 to `o(log log n)`
small-prime tail discrepancy and the `log(K n + 2)` large-prime window majorant. -/
theorem erdos_726_of_smallPrimeTail_and_log_add_two_bounds
    (K : ℕ → ℕ) (δ : ℕ → ℝ) (N₀ : ℕ)
    (hδ : ∀ n ≥ N₀, 0 ≤ δ n)
    (h2 : ∀ n ≥ N₀, 2 ≤ n / (K n + 1))
    (hK : ∀ n ≥ N₀, K n + 1 ≤ n / (K n + 1))
    (hR : ∀ n ≥ N₀, ∀ m ≤ n,
      |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ n * (m : ℝ))
    (hmaj : Filter.Tendsto
      (fun n : ℕ ↦ largePrimeWindowMajorant n (K n) (δ n) / Real.log (Real.log (n : ℝ)))
      atTop (nhds 0))
    (htail : Filter.Tendsto
      (fun n : ℕ ↦ (upperSmallPrimeTailSum n (K n) - lowerSmallPrimeTailSum n (K n)) /
        Real.log (Real.log (n : ℝ))) atTop (nhds 0)) :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / ((2 : ℕ) : ℝ) < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) :=
  (erdos_726_iff_smallPrimeTail_of_log_add_two_bounds K δ N₀ hδ h2 hK hR hmaj).mpr htail

/-- Top-down conditional reduction to `Erdos726.erdos_726` combining modular period reflection
`M n` on `oddPrimeRange (n / (K n + 1))` with the `log(K n + 2)` large-prime window majorant. -/
theorem erdos_726_of_modular_reflection_and_log_add_two_bounds
    (K M : ℕ → ℕ) (δ : ℕ → ℝ) (N₀ : ℕ)
    (hδ : ∀ n ≥ N₀, 0 ≤ δ n)
    (h2 : ∀ n ≥ N₀, 2 ≤ n / (K n + 1))
    (hK : ∀ n ≥ N₀, K n + 1 ≤ n / (K n + 1))
    (hle : ∀ n ≥ N₀, n ≤ M n)
    (hM : ∀ n ≥ N₀, ∀ p ∈ oddPrimeRange (n / (K n + 1)), p ∣ M n)
    (hR : ∀ n ≥ N₀, ∀ m ≤ n,
      |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ n * (m : ℝ))
    (hmaj : Filter.Tendsto
      (fun n : ℕ ↦ largePrimeWindowMajorant n (K n) (δ n) / Real.log (Real.log (n : ℝ)))
      atTop (nhds 0))
    (hrefl : Filter.Tendsto
      (fun n : ℕ ↦
        (|upperBoundedPrimeSum (n / (K n + 1)) n -
            upperBoundedPrimeSum (n / (K n + 1)) (M n - n)| +
          dividingOddBoundedSum (n / (K n + 1)) n + 1 / 2) /
          Real.log (Real.log (n : ℝ)))
      atTop (nhds 0)) :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / ((2 : ℕ) : ℝ) < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) := by
  apply erdos_726_of_smallPrimeTail_and_log_add_two_bounds K δ N₀ hδ h2 hK hR hmaj
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Filter.Tendsto.comp Real.tendsto_log_atTop
      (Filter.Tendsto.comp Real.tendsto_log_atTop tendsto_natCast_atTop_atTop)
  refine squeeze_zero_norm' ?_ hrefl
  filter_upwards [eventually_ge_atTop N₀, Filter.Tendsto.eventually_gt_atTop hlog 0] with n hn hlog_pos
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog_pos]
  have htail := abs_smallPrimeTail_discrepancy_le_of_modular_reflection
    n (K n) (M n) (h2 n hn) (hle n hn) (hM n hn)
  exact div_le_div_of_nonneg_right htail (le_of_lt hlog_pos)

/-! ## Section 4: Positive and Negative Falsifying Controls -/

/-- Positive sharpness control at `n = 11`, `K = 2`: `K + 1 = 3 ≤ 11 / 3 = 3`,
`(11 / 3) * 3 = 9 ≤ 11 < 12 = (11 / 3) * (2 + 2)`, attaining the `(n / (K + 1)) * (K + 2) = n + 1`
threshold extremizer. -/
theorem positive_control_div_succ_mul_add_two_eleven_two :
    2 + 1 ≤ 11 / (2 + 1) ∧
      (11 / (2 + 1)) * (2 + 1) = 9 ∧
      (11 / (2 + 1)) * (2 + 2) = 12 ∧
      11 ≤ (11 / (2 + 1)) * (2 + 2) := by
  decide

/-- Universal negative control for `K ≥ 3`: at `n = 3 * K + 2`, the hypothesis `K + 1 ≤ n / (K + 1)`
fails (`(3 * K + 2) / (K + 1) = 2 < K + 1`) and the floor-quotient multiplication inequality
reverses strictly (`((3 * K + 2) / (K + 1)) * (K + 2) = 2 * K + 4 < 3 * K + 2`). -/
theorem negative_control_subthreshold_div_succ_mul_add_two_lt :
    ∀ K : ℕ, 3 ≤ K →
      (3 * K + 2) / (K + 1) = 2 ∧
        ((3 * K + 2) / (K + 1)) * (K + 2) < 3 * K + 2 := by
  intro K hK
  have h1 : 3 * K + 2 = K + 2 * (K + 1) := by ring
  have hlt : K < K + 1 := by omega
  have hdiv : (3 * K + 2) / (K + 1) = 2 := by
    rw [h1, Nat.add_mul_div_right K 2 (by omega), Nat.div_eq_of_lt hlt, zero_add]
  refine ⟨hdiv, ?_⟩
  rw [hdiv]
  omega

/-- Concrete negative control at `n = 11`, `K = 3` (`n / (K + 1) = 2 < 4 = K + 1`): omitting
`K + 1 ≤ n / (K + 1)` falsifies the multiplication inequality, the logarithm difference bound
`Real.log n - Real.log (n / (K + 1)) ≤ Real.log (K + 2)`, and the reciprocal-logarithm bound
`1 / Real.log (n / (K + 1)) - 1 / Real.log n ≤ Real.log (K + 2) / (Real.log (n / (K + 1)) * Real.log n)`. -/
theorem negative_control_inv_log_bound_fails_without_succ_le_div :
    11 / (3 + 1) = 2 ∧
      (11 / (3 + 1)) * (3 + 2) < 11 ∧
      Real.log ((3 : ℝ) + 2) <
        Real.log ((11 : ℕ) : ℝ) - Real.log ((11 / (3 + 1) : ℕ) : ℝ) ∧
      Real.log ((3 : ℝ) + 2) / (Real.log ((11 / (3 + 1) : ℕ) : ℝ) * Real.log ((11 : ℕ) : ℝ)) <
        1 / Real.log ((11 / (3 + 1) : ℕ) : ℝ) - 1 / Real.log ((11 : ℕ) : ℝ) := by
  have hdiv : 11 / (3 + 1) = 2 := by decide
  have hmul : (11 / (3 + 1)) * (3 + 2) < 11 := by decide
  have hlog_lt : Real.log (10 : ℝ) < Real.log (11 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have h10 : Real.log (10 : ℝ) = Real.log (2 : ℝ) + Real.log (5 : ℝ) := by
    have h10_eq : (10 : ℝ) = 2 * 5 := by norm_num
    rw [h10_eq, Real.log_mul (by norm_num) (by norm_num)]
  have hlog_diff :
      Real.log ((3 : ℝ) + 2) < Real.log ((11 : ℕ) : ℝ) - Real.log ((11 / (3 + 1) : ℕ) : ℝ) := by
    rw [hdiv]
    norm_num
    linarith
  refine ⟨hdiv, hmul, hlog_diff, ?_⟩
  have hsub := invLog_sub_eq_log_diff_div_mul (11 / (3 + 1)) 11 (by decide) (by decide)
  unfold invLog at hsub
  rw [hsub]
  have hlog2 : 0 < Real.log ((11 / (3 + 1) : ℕ) : ℝ) :=
    (real_log_pos_and_invLog_pos_of_two_le (11 / (3 + 1)) (by decide)).1
  have hlog11 : 0 < Real.log ((11 : ℕ) : ℝ) :=
    (real_log_pos_and_invLog_pos_of_two_le 11 (by decide)).1
  exact div_lt_div_of_pos_right hlog_diff (mul_pos hlog2 hlog11)


end Erdos726

end
