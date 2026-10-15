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
public import SmallPrimeTailReflectionDiscrepancy726

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

/-! ## Section 1: Exact `primeCount` Representations of `windowCountDiscrepancy` and `quotientPrimeFiber` -/

/-- The exact `primeCount` second difference `2 π(⌊(2n - 1)/(2k + 1)⌋) - π(⌊n/(k + 1)⌋) - π(⌊n/k⌋)`. -/
def primeCountSecondDiff (n k : ℕ) : ℝ :=
  2 * (primeCount ((2 * n - 1) / (2 * k + 1)) : ℝ) -
    (primeCount (n / (k + 1)) : ℝ) - (primeCount (n / k) : ℝ)

/-- Odd-weighted endpoint prime count `(2k - 1) π(⌊n / k⌋)` for the Abel telescoping identity. -/
def oddWeightedPrimeCount (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) - 1) * (primeCount (n / k) : ℝ)

/-- Left-endpoint normalized prime-count defect
`(2k + 1) π(⌊(2n - 1)/(2k + 1)⌋) - 2k π(⌊n / k⌋)`. -/
def leftNormalizedPrimeDefect (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * (primeCount ((2 * n - 1) / (2 * k + 1)) : ℝ) -
    2 * (k : ℝ) * (primeCount (n / k) : ℝ)

/-- Right-endpoint normalized prime-count defect
`(2k + 1) π(⌊(2n - 1)/(2k + 1)⌋) - 2(k + 1) π(⌊n / (k + 1)⌋)`. -/
def rightNormalizedPrimeDefect (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * (primeCount ((2 * n - 1) / (2 * k + 1)) : ℝ) -
    2 * ((k : ℝ) + 1) * (primeCount (n / (k + 1)) : ℝ)

/-- Trapezoidal (symmetric-endpoint) normalized prime-count second difference
`(2k + 1) π(⌊(2n - 1)/(2k + 1)⌋) - (k + 1) π(⌊n / (k + 1)⌋) - k π(⌊n / k⌋)`. -/
def trapezoidalPrimeDefect (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * (primeCount ((2 * n - 1) / (2 * k + 1)) : ℝ) -
    ((k : ℝ) + 1) * (primeCount (n / (k + 1)) : ℝ) -
    (k : ℝ) * (primeCount (n / k) : ℝ)

/-- Cumulative unweighted prime-count discrepancy `∑_{j=1}^K (|U_j(n)| - |L_j(n)|)`. -/
def cumulativeCountDiscrepancy (n K : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 K, windowCountDiscrepancy n j

/-- Prime-counting remainder `(primeCount m : ℝ) - M m` relative to an approximating main term `M`. -/
def pntRemainder (M : ℕ → ℝ) (m : ℕ) : ℝ :=
  (primeCount m : ℝ) - M m

/-- Second difference `2 M(⌊(2n - 1)/(2k + 1)⌋) - M(⌊n / (k + 1)⌋) - M(⌊n / k⌋)` of an arbitrary
real-valued arithmetic function `M`. -/
def approxSecondDiff (M : ℕ → ℝ) (n k : ℕ) : ℝ :=
  2 * M ((2 * n - 1) / (2 * k + 1)) - M (n / (k + 1)) - M (n / k)

/-- Left-endpoint normalized defect `(2k + 1) M(⌊(2n - 1)/(2k + 1)⌋) - 2k M(⌊n / k⌋)` of `M`. -/
def approxLeftDefect (M : ℕ → ℝ) (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * M ((2 * n - 1) / (2 * k + 1)) - 2 * (k : ℝ) * M (n / k)

/-- Trapezoidal normalized defect
`(2k + 1) M(⌊(2n - 1)/(2k + 1)⌋) - (k + 1) M(⌊n / (k + 1)⌋) - k M(⌊n / k⌋)` of `M`. -/
def approxTrapezoidalDefect (M : ℕ → ℝ) (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * M ((2 * n - 1) / (2 * k + 1)) -
    ((k : ℝ) + 1) * M (n / (k + 1)) - (k : ℝ) * M (n / k)

/-- Ordered cutoff chain `n / (k + 1) ≤ (2n - 1) / (2k + 1) ≤ n / k` for `1 ≤ n` and `1 ≤ k`. -/
theorem div_succ_le_mid_and_mid_le_div :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      n / (k + 1) ≤ (2 * n - 1) / (2 * k + 1) ∧ (2 * n - 1) / (2 * k + 1) ≤ n / k := by
  intro n k _ hk
  constructor
  · rcases Nat.eq_zero_or_pos (n / (k + 1)) with hzero | hpos
    · rw [hzero]; exact Nat.zero_le _
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)]
      have hmul : (n / (k + 1)) * (k + 1) ≤ n := Nat.div_mul_le_self n (k + 1)
      have hstep : (n / (k + 1)) * (2 * k + 1) + 1 ≤ 2 * ((n / (k + 1)) * (k + 1)) := by nlinarith
      omega
  · rw [Nat.le_div_iff_mul_le (by omega : 0 < k)]
    have hmul : ((2 * n - 1) / (2 * k + 1)) * (2 * k + 1) ≤ 2 * n - 1 :=
      Nat.div_mul_le_self (2 * n - 1) (2 * k + 1)
    have hle2n : ((2 * n - 1) / (2 * k + 1)) * (2 * k + 1) ≤ 2 * n :=
      le_trans hmul (Nat.sub_le (2 * n) 1)
    nlinarith

/-- Monotonicity of `primeCount` across the `k`-th window cutoffs
`primeCount (n / (k + 1)) ≤ primeCount ((2n - 1) / (2k + 1)) ≤ primeCount (n / k)`. -/
theorem primeCount_div_succ_le_mid_and_mid_le_div :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      primeCount (n / (k + 1)) ≤ primeCount ((2 * n - 1) / (2 * k + 1)) ∧
        primeCount ((2 * n - 1) / (2 * k + 1)) ≤ primeCount (n / k) := by
  intro n k hn hk
  have hcut := div_succ_le_mid_and_mid_le_div n k hn hk
  exact ⟨(primeRange_mono _ _ hcut.1).2, (primeRange_mono _ _ hcut.2).2⟩

/-- Real-cast `primeCount` formula for `|U_k(n)|`:
`((upperQuotientPrimes n k).card : ℝ) = (primeCount ((2n - 1)/(2k + 1)) : ℝ) - (primeCount (n/(k + 1)) : ℝ)`. -/
theorem upperQuotientPrimes_card_cast_eq_primeCount_sub :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ((upperQuotientPrimes n k).card : ℝ) =
        (primeCount ((2 * n - 1) / (2 * k + 1)) : ℝ) - (primeCount (n / (k + 1)) : ℝ) := by
  intro n k hn hk
  rw [upperQuotientPrimes_card_eq_primeCount_sub n k hn hk]
  have hle := (primeCount_div_succ_le_mid_and_mid_le_div n k hn hk).1
  exact Nat.cast_sub hle

/-- Real-cast `primeCount` formula for `|L_k(n)|`:
`((lowerQuotientPrimes n k).card : ℝ) = (primeCount (n / k) : ℝ) - (primeCount ((2n - 1)/(2k + 1)) : ℝ)`. -/
theorem lowerQuotientPrimes_card_cast_eq_primeCount_sub :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ((lowerQuotientPrimes n k).card : ℝ) =
        (primeCount (n / k) : ℝ) - (primeCount ((2 * n - 1) / (2 * k + 1)) : ℝ) := by
  intro n k hn hk
  rw [lowerQuotientPrimes_card_eq_primeCount_sub n k hn hk]
  have hle := (primeCount_div_succ_le_mid_and_mid_le_div n k hn hk).2
  exact Nat.cast_sub hle

/-- Exact `primeCount` first-difference formula for `|Q_k(n)|`:
`(quotientPrimeFiber n k).card = primeCount (n / k) - primeCount (n / (k + 1))` and its real cast. -/
theorem quotientPrimeFiber_card_eq_primeCount_sub :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (quotientPrimeFiber n k).card = primeCount (n / k) - primeCount (n / (k + 1)) ∧
        ((quotientPrimeFiber n k).card : ℝ) =
          (primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ) := by
  intro n k hn hk
  have hle := primeCount_div_succ_le_mid_and_mid_le_div n k hn hk
  have hnat : (quotientPrimeFiber n k).card = primeCount (n / k) - primeCount (n / (k + 1)) := by
    rw [quotientPrimeFiber_card_eq_add,
      upperQuotientPrimes_card_eq_primeCount_sub n k hn hk,
      lowerQuotientPrimes_card_eq_primeCount_sub n k hn hk]
    have h1 := hle.1
    have h2 := hle.2
    omega
  refine ⟨hnat, ?_⟩
  rw [hnat, Nat.cast_sub (le_trans hle.1 hle.2)]

/-- Exact `primeCount` second-difference representation of `windowCountDiscrepancy n k`:
`|U_k(n)| - |L_k(n)| = 2 π(⌊(2n - 1)/(2k + 1)⌋) - π(⌊n/(k + 1)⌋) - π(⌊n/k⌋)`. -/
theorem windowCountDiscrepancy_eq_primeCountSecondDiff :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      windowCountDiscrepancy n k = primeCountSecondDiff n k := by
  intro n k hn hk
  unfold windowCountDiscrepancy primeCountSecondDiff
  rw [upperQuotientPrimes_card_cast_eq_primeCount_sub n k hn hk,
    lowerQuotientPrimes_card_cast_eq_primeCount_sub n k hn hk]
  ring

/-- Representation of `windowCountDiscrepancy n k` in terms of `|U_k(n)|`, `|L_k(n)|`, and `|Q_k(n)|`:
`|U_k(n)| - |L_k(n)| = 2 |U_k(n)| - |Q_k(n)| = |Q_k(n)| - 2 |L_k(n)|`. -/
theorem windowCountDiscrepancy_eq_fiber_forms :
    ∀ n k : ℕ,
      windowCountDiscrepancy n k =
        2 * ((upperQuotientPrimes n k).card : ℝ) - ((quotientPrimeFiber n k).card : ℝ) ∧
      windowCountDiscrepancy n k =
        ((quotientPrimeFiber n k).card : ℝ) - 2 * ((lowerQuotientPrimes n k).card : ℝ) := by
  intro n k
  have hcard :
      ((quotientPrimeFiber n k).card : ℝ) =
        ((upperQuotientPrimes n k).card : ℝ) + ((lowerQuotientPrimes n k).card : ℝ) := by
    exact_mod_cast quotientPrimeFiber_card_eq_add n k
  unfold windowCountDiscrepancy
  rw [hcard]
  constructor <;> ring

/-- Exact representation of `midpointWindowApprox n k` via `primeCountSecondDiff n k`. -/
theorem midpointWindowApprox_eq_primeCountSecondDiff :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      midpointWindowApprox n k =
        ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * primeCountSecondDiff n k := by
  intro n k hn hk
  unfold midpointWindowApprox
  rw [windowCountDiscrepancy_eq_primeCountSecondDiff n k hn hk]

/-! ## Section 2: Normalized Prime-Count Defects and Pointwise Abel Transformation Identities -/

/-- Evaluation of `oddWeightedPrimeCount` at `k = 1` and `k = K + 1`. -/
theorem oddWeightedPrimeCount_one_and_succ :
    ∀ n K : ℕ,
      oddWeightedPrimeCount n 1 = (primeCount n : ℝ) ∧
        oddWeightedPrimeCount n (K + 1) =
          (2 * (K : ℝ) + 1) * (primeCount (n / (K + 1)) : ℝ) := by
  intro n K
  unfold oddWeightedPrimeCount
  constructor
  · simp
    ring
  · push_cast
    ring

/-- The trapezoidal normalized prime-count defect is the arithmetic mean of the left and right
normalized prime-count defects. -/
theorem trapezoidalPrimeDefect_eq_avg_left_right :
    ∀ n k : ℕ,
      2 * trapezoidalPrimeDefect n k =
        leftNormalizedPrimeDefect n k + rightNormalizedPrimeDefect n k ∧
      rightNormalizedPrimeDefect n k - leftNormalizedPrimeDefect n k =
        2 * (k : ℝ) * (primeCount (n / k) : ℝ) -
          2 * ((k : ℝ) + 1) * (primeCount (n / (k + 1)) : ℝ) := by
  intro n k
  unfold trapezoidalPrimeDefect leftNormalizedPrimeDefect rightNormalizedPrimeDefect
  constructor <;> ring

/-- Pointwise left-endpoint Abel transformation identity:
`(2k + 1) primeCountSecondDiff n k = 2 * leftNormalizedPrimeDefect n k - (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k)`. -/
theorem pointwise_abel_left_identity :
    ∀ n k : ℕ,
      (2 * (k : ℝ) + 1) * primeCountSecondDiff n k =
        2 * leftNormalizedPrimeDefect n k -
          (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k) := by
  intro n k
  unfold primeCountSecondDiff leftNormalizedPrimeDefect oddWeightedPrimeCount
  push_cast
  ring

/-- Pointwise trapezoidal Abel transformation identity:
`(2k + 1) primeCountSecondDiff n k = 2 * trapezoidalPrimeDefect n k - (π(⌊n / k⌋) - π(⌊n / (k + 1)⌋))`. -/
theorem pointwise_abel_trapezoidal_identity :
    ∀ n k : ℕ,
      (2 * (k : ℝ) + 1) * primeCountSecondDiff n k =
        2 * trapezoidalPrimeDefect n k -
          ((primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ)) := by
  intro n k
  unfold primeCountSecondDiff trapezoidalPrimeDefect
  ring

/-- Exact identification of `trapezoidalPrimeDefect n k` with `(k + 1)|U_k(n)| - k|L_k(n)|`,
the upper endpoint weight of `quotient_window_discrepancy_sandwich`. -/
theorem trapezoidalPrimeDefect_eq_upper_lower_card :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      trapezoidalPrimeDefect n k =
        ((k : ℝ) + 1) * ((upperQuotientPrimes n k).card : ℝ) -
          (k : ℝ) * ((lowerQuotientPrimes n k).card : ℝ) := by
  intro n k hn hk
  rw [upperQuotientPrimes_card_cast_eq_primeCount_sub n k hn hk,
    lowerQuotientPrimes_card_cast_eq_primeCount_sub n k hn hk]
  unfold trapezoidalPrimeDefect
  ring

/-- Pointwise relation between `midpointWindowApprox n k`, the quadrature fiber bound
`|Q_k(n)| / (2n)`, and `trapezoidalPrimeDefect n k / n`. -/
theorem midpointWindowApprox_add_fiber_div_eq_trapezoidal :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      midpointWindowApprox n k + ((quotientPrimeFiber n k).card : ℝ) / (2 * (n : ℝ)) =
        trapezoidalPrimeDefect n k / (n : ℝ) := by
  intro n k hn hk
  rw [midpointWindowApprox_eq_primeCountSecondDiff n k hn hk,
    (quotientPrimeFiber_card_eq_primeCount_sub n k hn hk).2]
  have htrap := pointwise_abel_trapezoidal_identity n k
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply mul_right_cancel₀ (show (2 * (n : ℝ)) ≠ 0 by positivity)
  calc ((((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * primeCountSecondDiff n k +
          ((primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ)) / (2 * (n : ℝ))) *
        (2 * (n : ℝ)))
    _ = (2 * (k : ℝ) + 1) * primeCountSecondDiff n k +
          ((primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ)) := by
      field_simp [hn0]
    _ = 2 * trapezoidalPrimeDefect n k := by linarith
    _ = (trapezoidalPrimeDefect n k / (n : ℝ)) * (2 * (n : ℝ)) := by
      field_simp [hn0]

/-- Bilateral window discrepancy sandwich expressed directly via `midpointWindowApprox n k`
and `trapezoidalPrimeDefect n k / n`. -/
theorem window_discrepancy_sandwich_midpoint_trapezoidal :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      midpointWindowApprox n k ≤ upperQuotientSum n k - lowerQuotientSum n k ∧
        upperQuotientSum n k - lowerQuotientSum n k ≤ trapezoidalPrimeDefect n k / (n : ℝ) := by
  intro n k hn hk
  have hdef := window_midpoint_quadrature_defect_bounds n k (by omega)
  have htrap := midpointWindowApprox_add_fiber_div_eq_trapezoidal n k hn hk
  constructor <;> linarith

/-! ## Section 3: Cumulative Summation-by-Parts (Abel Transformation) Identities Across `1 ≤ k ≤ K` -/

/-- Forward telescoping sum identity on `Finset.Icc 1 K`:
`∑_{k=1}^K (f (k + 1) - f k) = f (K + 1) - f 1`. -/
theorem sum_Icc_succ_sub_eq :
    ∀ (f : ℕ → ℝ) (K : ℕ),
      ∑ k ∈ Finset.Icc 1 K, (f (k + 1) - f k) = f (K + 1) - f 1 := by
  intro f K
  induction K with
  | zero =>
    simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih]
    ring

/-- Backward telescoping sum identity on `Finset.Icc 1 K`:
`∑_{k=1}^K (f k - f (k + 1)) = f 1 - f (K + 1)`. -/
theorem sum_Icc_sub_succ_eq :
    ∀ (f : ℕ → ℝ) (K : ℕ),
      ∑ k ∈ Finset.Icc 1 K, (f k - f (k + 1)) = f 1 - f (K + 1) := by
  intro f K
  have h := sum_Icc_succ_sub_eq (fun k : ℕ ↦ -f k) K
  have hcongr :
      ∑ k ∈ Finset.Icc 1 K, (f k - f (k + 1)) =
        ∑ k ∈ Finset.Icc 1 K, (-f (k + 1) - -f k) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hcongr, h]
  ring

/-- Telescoping sum of odd-weighted prime counts across `k ∈ Icc 1 K`:
`∑_{k=1}^K (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k) = (2K + 1) π(⌊n/(K + 1)⌋) - π(n)`. -/
theorem sum_Icc_oddWeightedPrimeCount_diff :
    ∀ n K : ℕ,
      ∑ k ∈ Finset.Icc 1 K, (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k) =
        (2 * (K : ℝ) + 1) * (primeCount (n / (K + 1)) : ℝ) - (primeCount n : ℝ) := by
  intro n K
  rw [sum_Icc_succ_sub_eq (oddWeightedPrimeCount n) K]
  have heval := oddWeightedPrimeCount_one_and_succ n K
  rw [heval.1, heval.2]

/-- Telescoping sum of endpoint `primeCount` differences across `k ∈ Icc 1 K`:
`∑_{k=1}^K (π(⌊n / k⌋) - π(⌊n / (k + 1)⌋)) = π(n) - π(⌊n / (K + 1)⌋)`. -/
theorem sum_Icc_primeCount_div_diff :
    ∀ n K : ℕ,
      ∑ k ∈ Finset.Icc 1 K, ((primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ)) =
        (primeCount n : ℝ) - (primeCount (n / (K + 1)) : ℝ) := by
  intro n K
  have h := sum_Icc_sub_succ_eq (fun k : ℕ ↦ (primeCount (n / k) : ℝ)) K
  simpa using h

/-- Unweighted cumulative prime-count discrepancy identity in terms of `primeCount` evaluations
at `n / k` and `(2n - 1) / (2k + 1)`:
`∑_{k=1}^K (|U_k(n)| - |L_k(n)|) = 2 ∑_{k=1}^K (π(⌊(2n - 1)/(2k + 1)⌋) - π(⌊n/k⌋)) + (π(n) - π(⌊n/(K + 1)⌋))`. -/
theorem cumulativeCountDiscrepancy_eq_primeCount_sum :
    ∀ n K : ℕ, 1 ≤ n →
      cumulativeCountDiscrepancy n K =
        2 * (∑ k ∈ Finset.Icc 1 K,
              ((primeCount ((2 * n - 1) / (2 * k + 1)) : ℝ) - (primeCount (n / k) : ℝ))) +
          ((primeCount n : ℝ) - (primeCount (n / (K + 1)) : ℝ)) := by
  intro n K hn
  unfold cumulativeCountDiscrepancy
  have hcongr :
      ∑ k ∈ Finset.Icc 1 K, windowCountDiscrepancy n k =
        ∑ k ∈ Finset.Icc 1 K,
          (2 * ((primeCount ((2 * n - 1) / (2 * k + 1)) : ℝ) - (primeCount (n / k) : ℝ)) +
            ((primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [windowCountDiscrepancy_eq_primeCountSecondDiff n k hn hk1]
    unfold primeCountSecondDiff
    ring
  rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, sum_Icc_primeCount_div_diff]

/-- **Abel Transformation Identity I (Normalized Left-Defect & Boundary Form):**
For `1 ≤ n` and any cutoff `K`,
`∑_{k=1}^K ((2k + 1) / (2n)) (|U_k(n)| - |L_k(n)|)` equals
`∑_{k=1}^K (((2k + 1) π(⌊(2n - 1)/(2k + 1)⌋) - 2k π(⌊n/k⌋)) / n) + (π(n) - (2K + 1) π(⌊n/(K + 1)⌋)) / (2n)`. -/
theorem sum_midpointWindowApprox_eq_left_abel :
    ∀ n K : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k =
        (∑ k ∈ Finset.Icc 1 K, leftNormalizedPrimeDefect n k / (n : ℝ)) +
          ((primeCount n : ℝ) - (2 * (K : ℝ) + 1) * (primeCount (n / (K + 1)) : ℝ)) /
            (2 * (n : ℝ)) := by
  intro n K hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcongr :
      ∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k =
        ∑ k ∈ Finset.Icc 1 K,
          (leftNormalizedPrimeDefect n k / (n : ℝ) -
            (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k) / (2 * (n : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [midpointWindowApprox_eq_primeCountSecondDiff n k hn hk1]
    have hpt := pointwise_abel_left_identity n k
    apply mul_right_cancel₀ (show (2 * (n : ℝ)) ≠ 0 by positivity)
    calc (((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * primeCountSecondDiff n k) * (2 * (n : ℝ))
      _ = (2 * (k : ℝ) + 1) * primeCountSecondDiff n k := by field_simp [hn0]
      _ = 2 * leftNormalizedPrimeDefect n k -
            (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k) := hpt
      _ = (leftNormalizedPrimeDefect n k / (n : ℝ) -
            (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k) / (2 * (n : ℝ))) *
            (2 * (n : ℝ)) := by field_simp [hn0]
  have hdiv :
      ∑ k ∈ Finset.Icc 1 K,
        (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k) / (2 * (n : ℝ)) =
      (∑ k ∈ Finset.Icc 1 K, (oddWeightedPrimeCount n (k + 1) - oddWeightedPrimeCount n k)) /
        (2 * (n : ℝ)) := (Finset.sum_div _ _ _).symm
  rw [hcongr, Finset.sum_sub_distrib, hdiv, sum_Icc_oddWeightedPrimeCount_diff]
  ring

/-- **Abel Transformation Identity II (Trapezoidal Second-Difference & Quadrature-Defect Form):**
For `1 ≤ n` and any cutoff `K`,
`∑_{k=1}^K ((2k + 1) / (2n)) (|U_k(n)| - |L_k(n)|)` equals
`∑_{k=1}^K (trapezoidalPrimeDefect n k / n) - (π(n) - π(⌊n/(K + 1)⌋)) / (2n)`. -/
theorem sum_midpointWindowApprox_eq_trapezoidal_abel :
    ∀ n K : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k =
        (∑ k ∈ Finset.Icc 1 K, trapezoidalPrimeDefect n k / (n : ℝ)) -
          ((primeCount n : ℝ) - (primeCount (n / (K + 1)) : ℝ)) / (2 * (n : ℝ)) := by
  intro n K hn
  have hcongr :
      ∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k =
        ∑ k ∈ Finset.Icc 1 K,
          (trapezoidalPrimeDefect n k / (n : ℝ) -
            ((primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ)) / (2 * (n : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hpt := midpointWindowApprox_add_fiber_div_eq_trapezoidal n k hn hk1
    rw [(quotientPrimeFiber_card_eq_primeCount_sub n k hn hk1).2] at hpt
    linarith
  have hdiv :
      ∑ k ∈ Finset.Icc 1 K,
        ((primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ)) / (2 * (n : ℝ)) =
      (∑ k ∈ Finset.Icc 1 K, ((primeCount (n / k) : ℝ) - (primeCount (n / (k + 1)) : ℝ))) /
        (2 * (n : ℝ)) := (Finset.sum_div _ _ _).symm
  rw [hcongr, Finset.sum_sub_distrib, hdiv, sum_Icc_primeCount_div_diff]

/-- Step-weight summation by parts on `Finset.Icc 1 K` for an arbitrary sequence `d : ℕ → ℝ`:
`∑_{k=1}^K (2k + 1) d(k) = (2K + 3) (∑_{j=1}^K d(j)) - 2 ∑_{k=1}^K (∑_{j=1}^k d(j))`. -/
theorem sum_Icc_odd_weight_abel :
    ∀ (d : ℕ → ℝ) (K : ℕ),
      ∑ k ∈ Finset.Icc 1 K, (2 * (k : ℝ) + 1) * d k =
        (2 * (K : ℝ) + 3) * (∑ j ∈ Finset.Icc 1 K, d j) -
          2 * ∑ k ∈ Finset.Icc 1 K, (∑ j ∈ Finset.Icc 1 k, d j) := by
  intro d K
  induction K with
  | zero =>
    simp
  | succ K ih =>
    have h1 : 1 ≤ K + 1 := by omega
    rw [Finset.sum_Icc_succ_top h1, ih]
    rw [Finset.sum_Icc_succ_top h1 (f := fun k : ℕ ↦ ∑ j ∈ Finset.Icc 1 k, d j)]
    rw [Finset.sum_Icc_succ_top h1 (f := d)]
    push_cast
    ring

/-- **Abel Transformation Identity III (Step-Weight Partial-Sum Form):**
For any `n` and `K`, `∑_{k=1}^K midpointWindowApprox n k` equals
`((2K + 3) / (2n)) cumulativeCountDiscrepancy n K - (1 / n) ∑_{k=1}^K cumulativeCountDiscrepancy n k`. -/
theorem sum_midpointWindowApprox_eq_partial_sum_abel :
    ∀ n K : ℕ,
      ∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k =
        ((2 * (K : ℝ) + 3) / (2 * (n : ℝ))) * cumulativeCountDiscrepancy n K -
          (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 K, cumulativeCountDiscrepancy n k := by
  intro n K
  have hcongr :
      ∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k =
        (1 / (2 * (n : ℝ))) * ∑ k ∈ Finset.Icc 1 K, (2 * (k : ℝ) + 1) * windowCountDiscrepancy n k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold midpointWindowApprox
    ring
  rw [hcongr, sum_Icc_odd_weight_abel (windowCountDiscrepancy n) K]
  unfold cumulativeCountDiscrepancy
  ring

/-- Cumulative quotient-window discrepancy sandwich between the midpoint Abel sum and the
trapezoidal normalized prime-count sum. -/
theorem sum_window_discrepancy_sandwich_trapezoidal_abel :
    ∀ n K : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k ≤
        ∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k) ∧
      ∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k) ≤
        ∑ k ∈ Finset.Icc 1 K, trapezoidalPrimeDefect n k / (n : ℝ) := by
  intro n K hn
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    exact (window_discrepancy_sandwich_midpoint_trapezoidal n k hn (Finset.mem_Icc.mp hk).1).1
  · apply Finset.sum_le_sum
    intro k hk
    exact (window_discrepancy_sandwich_midpoint_trapezoidal n k hn (Finset.mem_Icc.mp hk).1).2

/-! ## Section 4: Variation Bounds under Prime-Number-Theorem Remainder Estimates -/

/-- Additive decomposition of `primeCountSecondDiff`, `leftNormalizedPrimeDefect`, and
`trapezoidalPrimeDefect` into main-term and `pntRemainder` components for any approximation `M`. -/
theorem primeCount_defects_eq_approx_add_remainder :
    ∀ (M : ℕ → ℝ) (n k : ℕ),
      primeCountSecondDiff n k =
        approxSecondDiff M n k + approxSecondDiff (pntRemainder M) n k ∧
      leftNormalizedPrimeDefect n k =
        approxLeftDefect M n k + approxLeftDefect (pntRemainder M) n k ∧
      trapezoidalPrimeDefect n k =
        approxTrapezoidalDefect M n k + approxTrapezoidalDefect (pntRemainder M) n k := by
  intro M n k
  unfold primeCountSecondDiff leftNormalizedPrimeDefect trapezoidalPrimeDefect
    approxSecondDiff approxLeftDefect approxTrapezoidalDefect pntRemainder
  refine ⟨by ring, by ring, by ring⟩

/-- Exact closed form for the cumulative odd-weight sum `∑_{k=1}^K (2k + 1) = K(K + 2)`. -/
theorem sum_Icc_two_mul_add_one_eq :
    ∀ K : ℕ, ∑ k ∈ Finset.Icc 1 K, (2 * (k : ℝ) + 1) = (K : ℝ) * ((K : ℝ) + 2) := by
  intro K
  induction K with
  | zero =>
    simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih]
    push_cast
    ring

/-- Pointwise bound on `|approxSecondDiff R n k|` under a uniform remainder bound `|R m| ≤ ε`
for `m ≤ n`. -/
theorem abs_approxSecondDiff_le_of_uniform_bound :
    ∀ (R : ℕ → ℝ) (n k : ℕ) (ε : ℝ), 1 ≤ k →
      (∀ m : ℕ, m ≤ n → |R m| ≤ ε) →
      |approxSecondDiff R n k| ≤ 4 * ε := by
  intro R n k ε hk hR
  have hmid_le : (2 * n - 1) / (2 * k + 1) ≤ n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < 2 * k + 1)]
    have h2 : 2 * n ≤ (2 * k + 1) * n := Nat.mul_le_mul_right n (by omega : 2 ≤ 2 * k + 1)
    omega
  have h1 : |R ((2 * n - 1) / (2 * k + 1))| ≤ ε := hR _ hmid_le
  have h2 : |R (n / (k + 1))| ≤ ε := hR _ (Nat.div_le_self n (k + 1))
  have h3 : |R (n / k)| ≤ ε := hR _ (Nat.div_le_self n k)
  unfold approxSecondDiff
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith

/-- Cumulative variation bound on `midpointWindowApprox` under a uniform PNT remainder estimate
`|pntRemainder M m| ≤ ε` for all `m ≤ n`:
`∑_{k=1}^K |midpointWindowApprox n k - ((2k + 1)/(2n)) approxSecondDiff M n k| ≤ (2 K(K + 2) / n) ε`. -/
theorem sum_abs_midpoint_pnt_variation_le_of_uniform_remainder :
    ∀ (M : ℕ → ℝ) (n K : ℕ) (ε : ℝ), 1 ≤ n →
      (∀ m : ℕ, m ≤ n → |pntRemainder M m| ≤ ε) →
      ∑ k ∈ Finset.Icc 1 K,
        |midpointWindowApprox n k - ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * approxSecondDiff M n k| ≤
        (2 * (K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * ε := by
  intro M n K ε hn hR
  have hle :
      ∑ k ∈ Finset.Icc 1 K,
        |midpointWindowApprox n k - ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * approxSecondDiff M n k| ≤
      ∑ k ∈ Finset.Icc 1 K, ((2 * (k : ℝ) + 1) * (2 * ε / (n : ℝ))) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [midpointWindowApprox_eq_primeCountSecondDiff n k hn hk1,
      (primeCount_defects_eq_approx_add_remainder M n k).1]
    have hdiff :
        ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) *
            (approxSecondDiff M n k + approxSecondDiff (pntRemainder M) n k) -
          ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * approxSecondDiff M n k =
        ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * approxSecondDiff (pntRemainder M) n k := by ring
    rw [hdiff, abs_mul]
    have hw_pos : 0 ≤ (2 * (k : ℝ) + 1) / (2 * (n : ℝ)) := by positivity
    rw [abs_of_nonneg hw_pos]
    have hrem := abs_approxSecondDiff_le_of_uniform_bound (pntRemainder M) n k ε hk1 hR
    have hmul := mul_le_mul_of_nonneg_left hrem hw_pos
    have halg :
        ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * (4 * ε) =
          (2 * (k : ℝ) + 1) * (2 * ε / (n : ℝ)) := by ring
    linarith
  rw [← Finset.sum_mul, sum_Icc_two_mul_add_one_eq] at hle
  have halg :
      (K : ℝ) * ((K : ℝ) + 2) * (2 * ε / (n : ℝ)) =
        (2 * (K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * ε := by ring
  linarith

/-- Euclidean division scale-cancellation bounds for the three window cutoffs:
`(2k + 1) ⌊(2n - 1)/(2k + 1)⌋ ≤ 2n`, `(k + 1) ⌊n/(k + 1)⌋ ≤ n`, and `k ⌊n/k⌋ ≤ n`. -/
theorem window_cutoff_mul_le_bounds :
    ∀ n k : ℕ,
      (2 * (k : ℝ) + 1) * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ) ≤ 2 * (n : ℝ) ∧
        ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) ≤ (n : ℝ) ∧
        (k : ℝ) * ((n / k : ℕ) : ℝ) ≤ (n : ℝ) := by
  intro n k
  have h1 : (2 * k + 1) * ((2 * n - 1) / (2 * k + 1)) ≤ 2 * n := by
    rw [Nat.mul_comm]
    exact le_trans (Nat.div_mul_le_self (2 * n - 1) (2 * k + 1)) (Nat.sub_le (2 * n) 1)
  have h2 : (k + 1) * (n / (k + 1)) ≤ n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self n (k + 1)
  have h3 : k * (n / k) ≤ n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self n k
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- Pointwise scale-cancellation bound for `approxLeftDefect R n k` and `approxTrapezoidalDefect R n k`
under a relative PNT remainder bound `|R m| ≤ δ * m` for `m ≤ n`: the growing weights `2k + 1`,
`k + 1`, and `k` cancel against `⌊(2n - 1)/(2k + 1)⌋`, `⌊n/(k + 1)⌋`, and `⌊n/k⌋` to yield
a `k`-independent bound `4 * δ * n`. -/
theorem abs_approxDefects_le_of_linear_scale_bound :
    ∀ (R : ℕ → ℝ) (n k : ℕ) (δ : ℝ), 1 ≤ k → 0 ≤ δ →
      (∀ m : ℕ, m ≤ n → |R m| ≤ δ * (m : ℝ)) →
      |approxLeftDefect R n k| ≤ 4 * δ * (n : ℝ) ∧
        |approxTrapezoidalDefect R n k| ≤ 4 * δ * (n : ℝ) := by
  intro R n k δ hk hδ hR
  have hmid_le : (2 * n - 1) / (2 * k + 1) ≤ n := by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < 2 * k + 1)]
    have h2 : 2 * n ≤ (2 * k + 1) * n := Nat.mul_le_mul_right n (by omega : 2 ≤ 2 * k + 1)
    omega
  have hcut := window_cutoff_mul_le_bounds n k
  have hR_mid : |R ((2 * n - 1) / (2 * k + 1))| ≤ δ * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ) :=
    hR _ hmid_le
  have hR_succ : |R (n / (k + 1))| ≤ δ * ((n / (k + 1) : ℕ) : ℝ) :=
    hR _ (Nat.div_le_self n (k + 1))
  have hR_div : |R (n / k)| ≤ δ * ((n / k : ℕ) : ℝ) :=
    hR _ (Nat.div_le_self n k)
  have hb_mid : (2 * (k : ℝ) + 1) * |R ((2 * n - 1) / (2 * k + 1))| ≤ 2 * δ * (n : ℝ) := by
    calc (2 * (k : ℝ) + 1) * |R ((2 * n - 1) / (2 * k + 1))|
      _ ≤ (2 * (k : ℝ) + 1) * (δ * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hR_mid (by positivity)
      _ = δ * ((2 * (k : ℝ) + 1) * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ)) := by ring
      _ ≤ δ * (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left hcut.1 hδ
      _ = 2 * δ * (n : ℝ) := by ring
  have hb_succ : ((k : ℝ) + 1) * |R (n / (k + 1))| ≤ δ * (n : ℝ) := by
    calc ((k : ℝ) + 1) * |R (n / (k + 1))|
      _ ≤ ((k : ℝ) + 1) * (δ * ((n / (k + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hR_succ (by positivity)
      _ = δ * (((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ)) := by ring
      _ ≤ δ * (n : ℝ) := mul_le_mul_of_nonneg_left hcut.2.1 hδ
  have hb_div : (k : ℝ) * |R (n / k)| ≤ δ * (n : ℝ) := by
    calc (k : ℝ) * |R (n / k)|
      _ ≤ (k : ℝ) * (δ * ((n / k : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hR_div (by positivity)
      _ = δ * ((k : ℝ) * ((n / k : ℕ) : ℝ)) := by ring
      _ ≤ δ * (n : ℝ) := mul_le_mul_of_nonneg_left hcut.2.2 hδ
  have h1 := le_abs_self (R ((2 * n - 1) / (2 * k + 1)))
  have h1n := neg_le_abs (R ((2 * n - 1) / (2 * k + 1)))
  have h2 := le_abs_self (R (n / (k + 1)))
  have h2n := neg_le_abs (R (n / (k + 1)))
  have h3 := le_abs_self (R (n / k))
  have h3n := neg_le_abs (R (n / k))
  have hm1 : (2 * (k : ℝ) + 1) * R ((2 * n - 1) / (2 * k + 1)) ≤ 2 * δ * (n : ℝ) := by
    nlinarith
  have hm1n : -(2 * δ * (n : ℝ)) ≤ (2 * (k : ℝ) + 1) * R ((2 * n - 1) / (2 * k + 1)) := by
    nlinarith
  have hm2 : ((k : ℝ) + 1) * R (n / (k + 1)) ≤ δ * (n : ℝ) := by nlinarith
  have hm2n : -(δ * (n : ℝ)) ≤ ((k : ℝ) + 1) * R (n / (k + 1)) := by nlinarith
  have hm3 : (k : ℝ) * R (n / k) ≤ δ * (n : ℝ) := by nlinarith
  have hm3n : -(δ * (n : ℝ)) ≤ (k : ℝ) * R (n / k) := by nlinarith
  unfold approxLeftDefect approxTrapezoidalDefect
  constructor
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

/-- Cumulative variation bound on the normalized left-defect and trapezoidal Abel sums under a
scale-proportional PNT remainder estimate `|pntRemainder M m| ≤ δ * m`: the `n`-dependence cancels
completely, bounding the cumulative remainder variation across `1 ≤ k ≤ K` by `4 K δ`. -/
theorem sum_abs_abel_pnt_variation_le_of_linear_scale_remainder :
    ∀ (M : ℕ → ℝ) (n K : ℕ) (δ : ℝ), 1 ≤ n → 0 ≤ δ →
      (∀ m : ℕ, m ≤ n → |pntRemainder M m| ≤ δ * (m : ℝ)) →
      ∑ k ∈ Finset.Icc 1 K,
        |(leftNormalizedPrimeDefect n k - approxLeftDefect M n k) / (n : ℝ)| ≤
          4 * (K : ℝ) * δ ∧
      ∑ k ∈ Finset.Icc 1 K,
        |(trapezoidalPrimeDefect n k - approxTrapezoidalDefect M n k) / (n : ℝ)| ≤
          4 * (K : ℝ) * δ := by
  intro M n K δ hn hδ hR
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcard : ((Finset.Icc 1 K).card : ℝ) = (K : ℝ) := by
    rw [Nat.card_Icc]
    simp
  constructor
  · calc ∑ k ∈ Finset.Icc 1 K,
          |(leftNormalizedPrimeDefect n k - approxLeftDefect M n k) / (n : ℝ)|
      _ ≤ ∑ _k ∈ Finset.Icc 1 K, (4 * δ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hdecomp := (primeCount_defects_eq_approx_add_remainder M n k).2.1
        have hsub : leftNormalizedPrimeDefect n k - approxLeftDefect M n k =
            approxLeftDefect (pntRemainder M) n k := by linarith
        rw [hsub, abs_div, abs_of_pos hn_pos, div_le_iff₀ hn_pos]
        exact (abs_approxDefects_le_of_linear_scale_bound (pntRemainder M) n k δ hk1 hδ hR).1
      _ = 4 * (K : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
  · calc ∑ k ∈ Finset.Icc 1 K,
          |(trapezoidalPrimeDefect n k - approxTrapezoidalDefect M n k) / (n : ℝ)|
      _ ≤ ∑ _k ∈ Finset.Icc 1 K, (4 * δ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hdecomp := (primeCount_defects_eq_approx_add_remainder M n k).2.2
        have hsub : trapezoidalPrimeDefect n k - approxTrapezoidalDefect M n k =
            approxTrapezoidalDefect (pntRemainder M) n k := by linarith
        rw [hsub, abs_div, abs_of_pos hn_pos, div_le_iff₀ hn_pos]
        exact (abs_approxDefects_le_of_linear_scale_bound (pntRemainder M) n k δ hk1 hδ hR).2
      _ = 4 * (K : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring

/-- Bound on `|∑_{k=1}^K midpointWindowApprox n k|` via the trapezoidal Abel main-term sum
`∑_{k=1}^K |approxTrapezoidalDefect M n k / n|`, the linear-scale PNT remainder variation `4 K δ`,
and the prime-count quadrature defect `(π(n) - π(⌊n/(K + 1)⌋)) / (2n)`. -/
theorem abs_sum_midpointWindowApprox_le_trapezoidal_approx_and_pnt :
    ∀ (M : ℕ → ℝ) (n K : ℕ) (δ : ℝ), 1 ≤ n → 0 ≤ δ →
      (∀ m : ℕ, m ≤ n → |pntRemainder M m| ≤ δ * (m : ℝ)) →
      |∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k| ≤
        (∑ k ∈ Finset.Icc 1 K, |approxTrapezoidalDefect M n k / (n : ℝ)|) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by
  intro M n K δ hn hδ hR
  rw [sum_midpointWindowApprox_eq_trapezoidal_abel n K hn]
  have hpi_le : primeCount (n / (K + 1)) ≤ primeCount n :=
    (primeRange_mono _ _ (Nat.div_le_self n (K + 1))).2
  have hcast_sub :
      (primeCount n : ℝ) - (primeCount (n / (K + 1)) : ℝ) =
        ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) :=
    (Nat.cast_sub hpi_le).symm
  rw [hcast_sub]
  have hq_nonneg :
      0 ≤ ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by positivity
  have htri1 := abs_sub
    (∑ k ∈ Finset.Icc 1 K, trapezoidalPrimeDefect n k / (n : ℝ))
    (((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)))
  rw [abs_of_nonneg hq_nonneg] at htri1
  have hsum_abs := Finset.abs_sum_le_sum_abs
    (fun k : ℕ ↦ trapezoidalPrimeDefect n k / (n : ℝ)) (Finset.Icc 1 K)
  have hterm_split :
      ∑ k ∈ Finset.Icc 1 K, |trapezoidalPrimeDefect n k / (n : ℝ)| ≤
        (∑ k ∈ Finset.Icc 1 K, |approxTrapezoidalDefect M n k / (n : ℝ)|) +
          ∑ k ∈ Finset.Icc 1 K,
            |(trapezoidalPrimeDefect n k - approxTrapezoidalDefect M n k) / (n : ℝ)| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k _
    have hrew :
        trapezoidalPrimeDefect n k / (n : ℝ) =
          approxTrapezoidalDefect M n k / (n : ℝ) +
            (trapezoidalPrimeDefect n k - approxTrapezoidalDefect M n k) / (n : ℝ) := by ring
    rw [hrew]
    exact abs_add_le _ _
  have hpnt := (sum_abs_abel_pnt_variation_le_of_linear_scale_remainder M n K δ hn hδ hR).2
  linarith

/-- Cumulative signed window discrepancy bound: the signed sum
`|∑_{k=1}^K (upperQuotientSum n k - lowerQuotientSum n k)|` is bounded by
`|∑_{k=1}^K midpointWindowApprox n k| + (π(n) - π(⌊n/(K + 1)⌋)) / (2n)`. -/
theorem abs_sum_window_discrepancy_le_abs_sum_midpoint_add_primeCount :
    ∀ n K : ℕ, 1 ≤ n →
      |∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k)| ≤
        |∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k| +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by
  intro n K hn
  have hdef := sum_window_midpoint_quadrature_defect_bounds n K (by omega)
  have hmid := le_abs_self (∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k)
  have hmid_neg := neg_le_abs (∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k)
  rw [abs_le]
  constructor <;> linarith

/-- Master asymptotic discrepancy bound for `|upperHalfPrimeSum n - log(log n) / 2|` combining
modular period reflection on the small-prime tail, the trapezoidal Abel summation-by-parts
identity on the `K` harmonic quotient windows, and the scale-proportional PNT remainder bound. -/
theorem abs_upperHalfPrimeSum_sub_half_mertens_le_abel_and_pnt_remainder :
    ∀ (M_approx : ℕ → ℝ) (n K M : ℕ) (δ : ℝ),
      1 ≤ n → 0 ≤ δ → 2 ≤ n / (K + 1) → n ≤ M →
      (∀ p ∈ oddPrimeRange (n / (K + 1)), p ∣ M) →
      (∀ m : ℕ, m ≤ n → |pntRemainder M_approx m| ≤ δ * (m : ℝ)) →
      |upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2| ≤
        (|upperBoundedPrimeSum (n / (K + 1)) n - upperBoundedPrimeSum (n / (K + 1)) (M - n)| +
          dividingOddBoundedSum (n / (K + 1)) n + 1 / 2 +
          (∑ k ∈ Finset.Icc 1 K, |approxTrapezoidalDefect M_approx n k / (n : ℝ)|) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ) +
          |Mertens.M + Mertens.E₂p (n : ℝ)|) / 2 := by
  intro M_approx n K M δ hn hδ hB hle hM hR
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
  have hrefl := abs_smallPrimeTail_discrepancy_le_of_modular_reflection n K M hB hle hM
  have hwin := abs_sum_window_discrepancy_le_abs_sum_midpoint_add_primeCount n K hn
  have hmid := abs_sum_midpointWindowApprox_le_trapezoidal_approx_and_pnt M_approx n K δ hn hδ hR
  have htwo :
      ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) +
        ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) =
      ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ) := by ring
  linarith

/-! ## Section 5: Positive and Negative Falsifying Controls -/

/-- Concrete prime-counting evaluations at `m ∈ {1, 2, 3, 6}`:
`primeCount 1 = 0`, `primeCount 2 = 1`, `primeCount 3 = 2`, and `primeCount 6 = 3`. -/
theorem primeCount_small_evaluations :
    primeCount 1 = 0 ∧ primeCount 2 = 1 ∧ primeCount 3 = 2 ∧ primeCount 6 = 3 := by
  decide

/-- Positive control at `n = 6`, `K = 2`: verifies the exact values of `primeCountSecondDiff`,
`leftNormalizedPrimeDefect`, `trapezoidalPrimeDefect`, and `∑_{k=1}^2 midpointWindowApprox 6 k`. -/
theorem positive_control_abel_identities_six_two :
    primeCountSecondDiff 6 1 = -1 ∧
      primeCountSecondDiff 6 2 = -1 ∧
      leftNormalizedPrimeDefect 6 1 = 0 ∧
      trapezoidalPrimeDefect 6 1 = -1 ∧
      ∑ k ∈ Finset.Icc 1 2, midpointWindowApprox 6 k = -2 / 3 := by
  have hpi := primeCount_small_evaluations
  have h1 : primeCountSecondDiff 6 1 = -1 := by
    unfold primeCountSecondDiff
    norm_num [hpi.2.2.1, hpi.2.2.2]
  have h2 : primeCountSecondDiff 6 2 = -1 := by
    unfold primeCountSecondDiff
    norm_num [hpi.2.1, hpi.2.2.1]
  have h3 : leftNormalizedPrimeDefect 6 1 = 0 := by
    unfold leftNormalizedPrimeDefect
    norm_num [hpi.2.2.1, hpi.2.2.2]
  have h4 : trapezoidalPrimeDefect 6 1 = -1 := by
    unfold trapezoidalPrimeDefect
    norm_num [hpi.2.2.1, hpi.2.2.2]
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [Finset.sum_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self, Finset.sum_singleton]
  rw [midpointWindowApprox_eq_primeCountSecondDiff 6 1 (by decide) (by decide),
    midpointWindowApprox_eq_primeCountSecondDiff 6 2 (by decide) (by decide), h1, h2]
  norm_num

/-- Negative control at `n = 6`, `K = 1`: omitting the Abel boundary term
`((primeCount 6 : ℝ) - 3 * (primeCount 3 : ℝ)) / 12 = -1 / 4` falsifies the left-defect Abel
identity (`midpointWindowApprox 6 1 = -1 / 4 ≠ 0 = leftNormalizedPrimeDefect 6 1 / 6`). -/
theorem negative_control_abel_boundary_omission_six_one :
    midpointWindowApprox 6 1 = -1 / 4 ∧
      leftNormalizedPrimeDefect 6 1 / 6 = 0 ∧
      midpointWindowApprox 6 1 ≠ leftNormalizedPrimeDefect 6 1 / 6 := by
  have hctrl := positive_control_abel_identities_six_two
  have hmid : midpointWindowApprox 6 1 = -1 / 4 := by
    rw [midpointWindowApprox_eq_primeCountSecondDiff 6 1 (by decide) (by decide), hctrl.1]
    norm_num
  have hleft : leftNormalizedPrimeDefect 6 1 / 6 = 0 := by
    rw [hctrl.2.2.1]
    norm_num
  refine ⟨hmid, hleft, ?_⟩
  linarith


end Erdos726

end
