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
public import AbelSummationPrimeCountVariation726

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

/-! ## Section 1: Floor-Discretization Defects, Euclidean Remainder Formulas, and Bilateral Bounds -/

/-- Midpoint Euclidean floor deficit `((2n - 1) % (2k + 1)) + 1`, equal to
`2n - (2k + 1) ⌊(2n - 1) / (2k + 1)⌋` for `1 ≤ n`. -/
def midFloorDeficit (n k : ℕ) : ℝ :=
  (((2 * n - 1) % (2 * k + 1) : ℕ) : ℝ) + 1

/-- Right-endpoint Euclidean floor deficit `n % (k + 1)`, equal to
`n - (k + 1) ⌊n / (k + 1)⌋`. -/
def succFloorDeficit (n k : ℕ) : ℝ :=
  ((n % (k + 1) : ℕ) : ℝ)

/-- Left-endpoint Euclidean floor deficit `n % k`, equal to `n - k ⌊n / k⌋`. -/
def divFloorDeficit (n k : ℕ) : ℝ :=
  ((n % k : ℕ) : ℝ)

/-- Floor-discretization trapezoidal defect
`(2k + 1) ⌊(2n - 1) / (2k + 1)⌋ - (k + 1) ⌊n / (k + 1)⌋ - k ⌊n / k⌋`. -/
def floorTrapezoidalDefect (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ) -
    ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) -
    (k : ℝ) * ((n / k : ℕ) : ℝ)

/-- Floor-discretization left-endpoint defect
`(2k + 1) ⌊(2n - 1) / (2k + 1)⌋ - 2k ⌊n / k⌋`. -/
def floorLeftDefect (n k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ) -
    2 * (k : ℝ) * ((n / k : ℕ) : ℝ)

/-- Identification of `floorTrapezoidalDefect` and `floorLeftDefect` with
`approxTrapezoidalDefect` and `approxLeftDefect` applied to `Nat.cast`. -/
theorem floorDefects_eq_approxDefects_cast :
    ∀ n k : ℕ,
      floorTrapezoidalDefect n k = approxTrapezoidalDefect (fun m : ℕ ↦ (m : ℝ)) n k ∧
        floorLeftDefect n k = approxLeftDefect (fun m : ℕ ↦ (m : ℝ)) n k := by
  intro n k
  exact ⟨rfl, rfl⟩

/-- Exact Euclidean division identities linking the scaled window cutoffs to `2n` and `n` via
`midFloorDeficit`, `succFloorDeficit`, and `divFloorDeficit`. -/
theorem window_cutoff_mul_add_deficits_eq :
    ∀ n k : ℕ, 1 ≤ n →
      (2 * (k : ℝ) + 1) * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ) + midFloorDeficit n k =
        2 * (n : ℝ) ∧
      ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) + succFloorDeficit n k = (n : ℝ) ∧
      (k : ℝ) * ((n / k : ℕ) : ℝ) + divFloorDeficit n k = (n : ℝ) := by
  intro n k hn
  have hmid_nat :
      (2 * k + 1) * ((2 * n - 1) / (2 * k + 1)) + ((2 * n - 1) % (2 * k + 1) + 1) = 2 * n := by
    have hdiv := Nat.div_add_mod (2 * n - 1) (2 * k + 1)
    omega
  have hsucc_nat : (k + 1) * (n / (k + 1)) + n % (k + 1) = n :=
    Nat.div_add_mod n (k + 1)
  have hdiv_nat : k * (n / k) + n % k = n :=
    Nat.div_add_mod n k
  unfold midFloorDeficit succFloorDeficit divFloorDeficit
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hmid_nat
  · exact_mod_cast hsucc_nat
  · exact_mod_cast hdiv_nat

/-- Exact range bounds for the three Euclidean floor deficits when `1 ≤ k`:
`1 ≤ midFloorDeficit n k ≤ 2k + 1`, `0 ≤ succFloorDeficit n k ≤ k`, and
`0 ≤ divFloorDeficit n k ≤ k - 1`. -/
theorem floor_deficits_bounds :
    ∀ n k : ℕ, 1 ≤ k →
      (1 ≤ midFloorDeficit n k ∧ midFloorDeficit n k ≤ 2 * (k : ℝ) + 1) ∧
      (0 ≤ succFloorDeficit n k ∧ succFloorDeficit n k ≤ (k : ℝ)) ∧
      (0 ≤ divFloorDeficit n k ∧ divFloorDeficit n k ≤ (k : ℝ) - 1) := by
  intro n k hk
  have hmid_lt : (2 * n - 1) % (2 * k + 1) < 2 * k + 1 :=
    Nat.mod_lt (2 * n - 1) (by omega)
  have hsucc_lt : n % (k + 1) < k + 1 :=
    Nat.mod_lt n (by omega)
  have hdiv_lt : n % k < k :=
    Nat.mod_lt n (by omega)
  have hmid_le : (2 * n - 1) % (2 * k + 1) + 1 ≤ 2 * k + 1 := by omega
  have hsucc_le : n % (k + 1) ≤ k := by omega
  have hdiv_le : n % k + 1 ≤ k := by omega
  have hmid_le_r : (((2 * n - 1) % (2 * k + 1) : ℕ) : ℝ) + 1 ≤ 2 * (k : ℝ) + 1 := by
    exact_mod_cast hmid_le
  have hsucc_le_r : ((n % (k + 1) : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hsucc_le
  have hdiv_le_r : ((n % k : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast hdiv_le
  unfold midFloorDeficit succFloorDeficit divFloorDeficit
  refine ⟨⟨?_, hmid_le_r⟩, ⟨by positivity, hsucc_le_r⟩, ⟨by positivity, by linarith⟩⟩
  have hnonneg : (0 : ℝ) ≤ (((2 * n - 1) % (2 * k + 1) : ℕ) : ℝ) := by positivity
  linarith

/-- Bilateral linear-scale sandwich bounds for the three scaled window cutoffs:
`2n - (2k + 1) ≤ (2k + 1) ⌊(2n - 1)/(2k + 1)⌋ ≤ 2n - 1`,
`n - k ≤ (k + 1) ⌊n/(k + 1)⌋ ≤ n`, and `n - (k - 1) ≤ k ⌊n/k⌋ ≤ n`. -/
theorem window_cutoff_mul_lower_and_upper_bounds :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (2 * (n : ℝ) - (2 * (k : ℝ) + 1) ≤
          (2 * (k : ℝ) + 1) * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ) ∧
        (2 * (k : ℝ) + 1) * (((2 * n - 1) / (2 * k + 1) : ℕ) : ℝ) ≤ 2 * (n : ℝ) - 1) ∧
      ((n : ℝ) - (k : ℝ) ≤ ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) ∧
        ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) ≤ (n : ℝ)) ∧
      ((n : ℝ) - ((k : ℝ) - 1) ≤ (k : ℝ) * ((n / k : ℕ) : ℝ) ∧
        (k : ℝ) * ((n / k : ℕ) : ℝ) ≤ (n : ℝ)) := by
  intro n k hn hk
  have heq := window_cutoff_mul_add_deficits_eq n k hn
  have hb := floor_deficits_bounds n k hk
  refine ⟨⟨by linarith [heq.1, hb.1.2], by linarith [heq.1, hb.1.1]⟩,
    ⟨by linarith [heq.2.1, hb.2.1.2], by linarith [heq.2.1, hb.2.1.1]⟩,
    ⟨by linarith [heq.2.2, hb.2.2.2], by linarith [heq.2.2, hb.2.2.1]⟩⟩

/-- Exact Euclidean remainder formula for the floor-discretization trapezoidal defect:
`floorTrapezoidalDefect n k = (n % (k + 1)) + (n % k) - (((2n - 1) % (2k + 1)) + 1)`. -/
theorem floorTrapezoidalDefect_eq_deficits :
    ∀ n k : ℕ, 1 ≤ n →
      floorTrapezoidalDefect n k =
        succFloorDeficit n k + divFloorDeficit n k - midFloorDeficit n k := by
  intro n k hn
  have heq := window_cutoff_mul_add_deficits_eq n k hn
  unfold floorTrapezoidalDefect
  linarith [heq.1, heq.2.1, heq.2.2]

/-- Exact Euclidean remainder formula for the floor-discretization left-endpoint defect:
`floorLeftDefect n k = 2 (n % k) - (((2n - 1) % (2k + 1)) + 1)`. -/
theorem floorLeftDefect_eq_deficits :
    ∀ n k : ℕ, 1 ≤ n →
      floorLeftDefect n k = 2 * divFloorDeficit n k - midFloorDeficit n k := by
  intro n k hn
  have heq := window_cutoff_mul_add_deficits_eq n k hn
  unfold floorLeftDefect
  linarith [heq.1, heq.2.2]

/-- Sharp bilateral and absolute-value bounds for the floor-discretization trapezoidal defect:
`-(2k + 1) ≤ floorTrapezoidalDefect n k ≤ 2k - 2` and `|floorTrapezoidalDefect n k| ≤ 2k + 1`. -/
theorem floorTrapezoidalDefect_bilateral_and_abs_bounds :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      -(2 * (k : ℝ) + 1) ≤ floorTrapezoidalDefect n k ∧
        floorTrapezoidalDefect n k ≤ 2 * (k : ℝ) - 2 ∧
        |floorTrapezoidalDefect n k| ≤ 2 * (k : ℝ) + 1 := by
  intro n k hn hk
  rw [floorTrapezoidalDefect_eq_deficits n k hn]
  have hb := floor_deficits_bounds n k hk
  have hlow : -(2 * (k : ℝ) + 1) ≤
      succFloorDeficit n k + divFloorDeficit n k - midFloorDeficit n k := by
    linarith [hb.1.2, hb.2.1.1, hb.2.2.1]
  have hhigh : succFloorDeficit n k + divFloorDeficit n k - midFloorDeficit n k ≤
      2 * (k : ℝ) - 2 := by
    linarith [hb.1.1, hb.2.1.2, hb.2.2.2]
  refine ⟨hlow, hhigh, ?_⟩
  rw [abs_le]
  exact ⟨hlow, by linarith⟩

/-- Sharp bilateral and absolute-value bounds for the floor-discretization left-endpoint defect:
`-(2k + 1) ≤ floorLeftDefect n k ≤ 2k - 3` and `|floorLeftDefect n k| ≤ 2k + 1`. -/
theorem floorLeftDefect_bilateral_and_abs_bounds :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      -(2 * (k : ℝ) + 1) ≤ floorLeftDefect n k ∧
        floorLeftDefect n k ≤ 2 * (k : ℝ) - 3 ∧
        |floorLeftDefect n k| ≤ 2 * (k : ℝ) + 1 := by
  intro n k hn hk
  rw [floorLeftDefect_eq_deficits n k hn]
  have hb := floor_deficits_bounds n k hk
  have hlow : -(2 * (k : ℝ) + 1) ≤ 2 * divFloorDeficit n k - midFloorDeficit n k := by
    linarith [hb.1.2, hb.2.2.1]
  have hhigh : 2 * divFloorDeficit n k - midFloorDeficit n k ≤ 2 * (k : ℝ) - 3 := by
    linarith [hb.1.1, hb.2.2.2]
  refine ⟨hlow, hhigh, ?_⟩
  rw [abs_le]
  exact ⟨hlow, by linarith⟩

/-- Cumulative bound on the normalized floor-discretization trapezoidal defect across `1 ≤ k ≤ K`:
`∑_{k=1}^K |floorTrapezoidalDefect n k / n| ≤ K(K + 2) / n`. -/
theorem sum_abs_floorTrapezoidalDefect_div_le :
    ∀ n K : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 K, |floorTrapezoidalDefect n k / (n : ℝ)| ≤
        ((K : ℝ) * ((K : ℝ) + 2)) / (n : ℝ) := by
  intro n K hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  calc ∑ k ∈ Finset.Icc 1 K, |floorTrapezoidalDefect n k / (n : ℝ)|
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ((2 * (k : ℝ) + 1) * (1 / (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [abs_div, abs_of_pos hn_pos, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right
        (floorTrapezoidalDefect_bilateral_and_abs_bounds n k hn hk1).2.2 (by positivity)
    _ = ((K : ℝ) * ((K : ℝ) + 2)) / (n : ℝ) := by
      rw [← Finset.sum_mul, sum_Icc_two_mul_add_one_eq]
      ring

/-- Cumulative bound on the normalized floor-discretization left-endpoint defect across `1 ≤ k ≤ K`:
`∑_{k=1}^K |floorLeftDefect n k / n| ≤ K(K + 2) / n`. -/
theorem sum_abs_floorLeftDefect_div_le :
    ∀ n K : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 K, |floorLeftDefect n k / (n : ℝ)| ≤
        ((K : ℝ) * ((K : ℝ) + 2)) / (n : ℝ) := by
  intro n K hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  calc ∑ k ∈ Finset.Icc 1 K, |floorLeftDefect n k / (n : ℝ)|
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ((2 * (k : ℝ) + 1) * (1 / (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [abs_div, abs_of_pos hn_pos, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right
        (floorLeftDefect_bilateral_and_abs_bounds n k hn hk1).2.2 (by positivity)
    _ = ((K : ℝ) * ((K : ℝ) + 2)) / (n : ℝ) := by
      rw [← Finset.sum_mul, sum_Icc_two_mul_add_one_eq]
      ring

/-! ## Section 2: Exact Decomposition into Floor-Discretization Defect and Weight Differences -/

/-- Factorized arithmetic main term `m ↦ (m : ℝ) * w m` for a density weight `w : ℕ → ℝ`. -/
def scaledWeightMainTerm (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) * w m

/-- Scaled first-difference combination of `w` across the `k`-th window cutoffs:
`(k + 1) ⌊n/(k + 1)⌋ (w ⌊(2n - 1)/(2k + 1)⌋ - w ⌊n/(k + 1)⌋) + k ⌊n/k⌋ (w ⌊(2n - 1)/(2k + 1)⌋ - w ⌊n/k⌋)`. -/
def scaledWeightFirstDiffTerm (w : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) *
      (w ((2 * n - 1) / (2 * k + 1)) - w (n / (k + 1))) +
    (k : ℝ) * ((n / k : ℕ) : ℝ) *
      (w ((2 * n - 1) / (2 * k + 1)) - w (n / k))

/-- Euclidean-remainder coupling defect between the floor deficits and first differences of `w`:
`(n % (k + 1)) (w ⌊n/(k + 1)⌋ - w ⌊(2n - 1)/(2k + 1)⌋) + (n % k) (w ⌊n/k⌋ - w ⌊(2n - 1)/(2k + 1)⌋)`. -/
def remainderCouplingDefect (w : ℕ → ℝ) (n k : ℕ) : ℝ :=
  succFloorDeficit n k * (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) +
    divFloorDeficit n k * (w (n / k) - w ((2 * n - 1) / (2 * k + 1)))

/-- **Decomposition Identity I (Unnormalized):**
`approxTrapezoidalDefect (fun m => m * w m) n k` splits into the floor-discretization defect
weighted by `w ⌊(2n - 1)/(2k + 1)⌋` plus `scaledWeightFirstDiffTerm w n k`. -/
theorem approxTrapezoidalDefect_scaledWeight_eq_floor_add_firstDiff :
    ∀ (w : ℕ → ℝ) (n k : ℕ),
      approxTrapezoidalDefect (scaledWeightMainTerm w) n k =
        floorTrapezoidalDefect n k * w ((2 * n - 1) / (2 * k + 1)) +
          scaledWeightFirstDiffTerm w n k := by
  intro w n k
  unfold approxTrapezoidalDefect scaledWeightMainTerm floorTrapezoidalDefect scaledWeightFirstDiffTerm
  ring

/-- **Decomposition Identity I (Normalized by `n`):**
`approxTrapezoidalDefect (fun m => m * w m) n k / n` equals
`(floorTrapezoidalDefect n k / n) * w ⌊(2n - 1)/(2k + 1)⌋ + scaledWeightFirstDiffTerm w n k / n`. -/
theorem approxTrapezoidalDefect_scaledWeight_div_eq_floor_add_firstDiff :
    ∀ (w : ℕ → ℝ) (n k : ℕ),
      approxTrapezoidalDefect (scaledWeightMainTerm w) n k / (n : ℝ) =
        (floorTrapezoidalDefect n k / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1)) +
          scaledWeightFirstDiffTerm w n k / (n : ℝ) := by
  intro w n k
  rw [approxTrapezoidalDefect_scaledWeight_eq_floor_add_firstDiff]
  ring

/-- Exact relation between `scaledWeightFirstDiffTerm w n k`, the pure second difference
`n * approxSecondDiff w n k`, and `remainderCouplingDefect w n k`. -/
theorem scaledWeightFirstDiffTerm_eq_secondDiff_add_remainderCoupling :
    ∀ (w : ℕ → ℝ) (n k : ℕ), 1 ≤ n →
      scaledWeightFirstDiffTerm w n k =
        (n : ℝ) * approxSecondDiff w n k + remainderCouplingDefect w n k := by
  intro w n k hn
  have heq := window_cutoff_mul_add_deficits_eq n k hn
  have h1 : ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) = (n : ℝ) - succFloorDeficit n k := by
    linarith [heq.2.1]
  have h2 : (k : ℝ) * ((n / k : ℕ) : ℝ) = (n : ℝ) - divFloorDeficit n k := by
    linarith [heq.2.2]
  unfold scaledWeightFirstDiffTerm approxSecondDiff remainderCouplingDefect
  rw [h1, h2]
  ring

/-- **Decomposition Identity II (Unnormalized):**
For `1 ≤ n`, `approxTrapezoidalDefect (fun m => m * w m) n k` decomposes into
`floorTrapezoidalDefect n k * w ⌊(2n - 1)/(2k + 1)⌋ + n * approxSecondDiff w n k + remainderCouplingDefect w n k`. -/
theorem approxTrapezoidalDefect_scaledWeight_eq_floor_add_secondDiff_add_coupling :
    ∀ (w : ℕ → ℝ) (n k : ℕ), 1 ≤ n →
      approxTrapezoidalDefect (scaledWeightMainTerm w) n k =
        floorTrapezoidalDefect n k * w ((2 * n - 1) / (2 * k + 1)) +
          (n : ℝ) * approxSecondDiff w n k +
          remainderCouplingDefect w n k := by
  intro w n k hn
  rw [approxTrapezoidalDefect_scaledWeight_eq_floor_add_firstDiff,
    scaledWeightFirstDiffTerm_eq_secondDiff_add_remainderCoupling w n k hn]
  ring

/-- **Decomposition Identity II (Normalized by `n`):**
For `1 ≤ n`, `approxTrapezoidalDefect (fun m => m * w m) n k / n` separates the
floor-discretization defect `(floorTrapezoidalDefect n k / n) * w ⌊(2n - 1)/(2k + 1)⌋`,
the pure second difference `approxSecondDiff w n k`, and `remainderCouplingDefect w n k / n`. -/
theorem approxTrapezoidalDefect_scaledWeight_div_eq_floor_add_secondDiff_add_coupling :
    ∀ (w : ℕ → ℝ) (n k : ℕ), 1 ≤ n →
      approxTrapezoidalDefect (scaledWeightMainTerm w) n k / (n : ℝ) =
        (floorTrapezoidalDefect n k / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1)) +
          approxSecondDiff w n k +
          remainderCouplingDefect w n k / (n : ℝ) := by
  intro w n k hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [approxTrapezoidalDefect_scaledWeight_eq_floor_add_secondDiff_add_coupling w n k hn]
  field_simp [hn0]

/-- Left-endpoint counterpart decomposition of `approxLeftDefect (scaledWeightMainTerm w) n k`. -/
theorem approxLeftDefect_scaledWeight_eq_floor_add_diff :
    ∀ (w : ℕ → ℝ) (n k : ℕ),
      approxLeftDefect (scaledWeightMainTerm w) n k =
        floorLeftDefect n k * w ((2 * n - 1) / (2 * k + 1)) +
          2 * (k : ℝ) * ((n / k : ℕ) : ℝ) * (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) := by
  intro w n k
  unfold approxLeftDefect scaledWeightMainTerm floorLeftDefect
  ring

/-! ## Section 3: Pointwise and Cumulative Telescoping Bounds for Antitone Weights -/

/-- Sign-cancellation bounds for `approxSecondDiff w n k` when `w` is antitone across the window
cutoffs `w ⌊n/k⌋ ≤ w ⌊(2n - 1)/(2k + 1)⌋ ≤ w ⌊n/(k + 1)⌋`: the two first differences have opposite
signs, bounding `|approxSecondDiff w n k|` by the telescoping first difference
`w ⌊n/(k + 1)⌋ - w ⌊n/k⌋`. -/
theorem approxSecondDiff_bounds_of_antitone_window :
    ∀ (w : ℕ → ℝ) (n k : ℕ),
      w (n / k) ≤ w ((2 * n - 1) / (2 * k + 1)) →
      w ((2 * n - 1) / (2 * k + 1)) ≤ w (n / (k + 1)) →
      -(w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) ≤ approxSecondDiff w n k ∧
        approxSecondDiff w n k ≤ w ((2 * n - 1) / (2 * k + 1)) - w (n / k) ∧
        |approxSecondDiff w n k| ≤ w (n / (k + 1)) - w (n / k) := by
  intro w n k h1 h2
  unfold approxSecondDiff
  refine ⟨by linarith, by linarith, ?_⟩
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Sign-cancellation bounds for `scaledWeightFirstDiffTerm w n k` when `w` is antitone across
the window cutoffs: since `0 ≤ (k + 1) ⌊n/(k + 1)⌋ ≤ n` and `0 ≤ k ⌊n/k⌋ ≤ n`, the opposite-sign
first differences bound `|scaledWeightFirstDiffTerm w n k| ≤ n (w ⌊n/(k + 1)⌋ - w ⌊n/k⌋)`. -/
theorem scaledWeightFirstDiffTerm_bounds_of_antitone_window :
    ∀ (w : ℕ → ℝ) (n k : ℕ),
      w (n / k) ≤ w ((2 * n - 1) / (2 * k + 1)) →
      w ((2 * n - 1) / (2 * k + 1)) ≤ w (n / (k + 1)) →
      -(n : ℝ) * (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) ≤
          scaledWeightFirstDiffTerm w n k ∧
        scaledWeightFirstDiffTerm w n k ≤
          (n : ℝ) * (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) ∧
        |scaledWeightFirstDiffTerm w n k| ≤ (n : ℝ) * (w (n / (k + 1)) - w (n / k)) := by
  intro w n k h1 h2
  have hcut := window_cutoff_mul_le_bounds n k
  have ha1_nonneg : 0 ≤ ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) := by positivity
  have ha0_nonneg : 0 ≤ (k : ℝ) * ((n / k : ℕ) : ℝ) := by positivity
  have hd1_nonneg : 0 ≤ w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1)) := by linarith
  have hd0_nonneg : 0 ≤ w ((2 * n - 1) / (2 * k + 1)) - w (n / k) := by linarith
  have hterm1_le :
      ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) *
        (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) ≤
      (n : ℝ) * (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) :=
    mul_le_mul_of_nonneg_right hcut.2.1 hd1_nonneg
  have hterm1_nonneg :
      0 ≤ ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) *
        (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) :=
    mul_nonneg ha1_nonneg hd1_nonneg
  have hterm0_le :
      (k : ℝ) * ((n / k : ℕ) : ℝ) *
        (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) ≤
      (n : ℝ) * (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) :=
    mul_le_mul_of_nonneg_right hcut.2.2 hd0_nonneg
  have hterm0_nonneg :
      0 ≤ (k : ℝ) * ((n / k : ℕ) : ℝ) *
        (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) :=
    mul_nonneg ha0_nonneg hd0_nonneg
  unfold scaledWeightFirstDiffTerm
  have hlow :
      -(n : ℝ) * (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) ≤
        ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) *
            (w ((2 * n - 1) / (2 * k + 1)) - w (n / (k + 1))) +
          (k : ℝ) * ((n / k : ℕ) : ℝ) *
            (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) := by
    linarith
  have hhigh :
      ((k : ℝ) + 1) * ((n / (k + 1) : ℕ) : ℝ) *
          (w ((2 * n - 1) / (2 * k + 1)) - w (n / (k + 1))) +
        (k : ℝ) * ((n / k : ℕ) : ℝ) *
          (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) ≤
      (n : ℝ) * (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) := by
    linarith
  refine ⟨hlow, hhigh, ?_⟩
  rw [abs_le]
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hsub1 :
      -(n : ℝ) * (w (n / (k + 1)) - w (n / k)) ≤
        -(n : ℝ) * (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) := by
    nlinarith
  have hsub2 :
      (n : ℝ) * (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) ≤
        (n : ℝ) * (w (n / (k + 1)) - w (n / k)) := by
    nlinarith
  exact ⟨by linarith, by linarith⟩

/-- Pointwise bound on `remainderCouplingDefect w n k` for an antitone window:
`|remainderCouplingDefect w n k| ≤ k * (w ⌊n/(k + 1)⌋ - w ⌊n/k⌋)`. -/
theorem abs_remainderCouplingDefect_le_of_antitone_window :
    ∀ (w : ℕ → ℝ) (n k : ℕ), 1 ≤ k →
      w (n / k) ≤ w ((2 * n - 1) / (2 * k + 1)) →
      w ((2 * n - 1) / (2 * k + 1)) ≤ w (n / (k + 1)) →
      |remainderCouplingDefect w n k| ≤ (k : ℝ) * (w (n / (k + 1)) - w (n / k)) := by
  intro w n k hk h1 h2
  have hb := floor_deficits_bounds n k hk
  have hd1_nonneg : 0 ≤ w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1)) := by linarith
  have hd0_nonneg : 0 ≤ w ((2 * n - 1) / (2 * k + 1)) - w (n / k) := by linarith
  have ht1_nonneg :
      0 ≤ succFloorDeficit n k * (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) :=
    mul_nonneg hb.2.1.1 hd1_nonneg
  have ht1_le :
      succFloorDeficit n k * (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) ≤
        (k : ℝ) * (w (n / (k + 1)) - w ((2 * n - 1) / (2 * k + 1))) :=
    mul_le_mul_of_nonneg_right hb.2.1.2 hd1_nonneg
  have ht0_nonneg :
      0 ≤ divFloorDeficit n k * (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) :=
    mul_nonneg hb.2.2.1 hd0_nonneg
  have ht0_le :
      divFloorDeficit n k * (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) ≤
        (k : ℝ) * (w ((2 * n - 1) / (2 * k + 1)) - w (n / k)) :=
    mul_le_mul_of_nonneg_right (by linarith [hb.2.2.2]) hd0_nonneg
  unfold remainderCouplingDefect
  rw [abs_le]
  constructor <;> nlinarith

/-- Pointwise bounds on `|approxTrapezoidalDefect (scaledWeightMainTerm w) n k / n|` from
Decompositions I and II for an antitone nonnegative weight across the `k`-th window. -/
theorem abs_approxTrapezoidalDefect_scaledWeight_div_le_of_antitone_window :
    ∀ (w : ℕ → ℝ) (n k : ℕ), 1 ≤ n → 1 ≤ k →
      0 ≤ w (n / k) →
      w (n / k) ≤ w ((2 * n - 1) / (2 * k + 1)) →
      w ((2 * n - 1) / (2 * k + 1)) ≤ w (n / (k + 1)) →
      |approxTrapezoidalDefect (scaledWeightMainTerm w) n k / (n : ℝ)| ≤
        ((2 * (k : ℝ) + 1) / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1)) +
          (w (n / (k + 1)) - w (n / k)) ∧
      |approxTrapezoidalDefect (scaledWeightMainTerm w) n k / (n : ℝ)| ≤
        |floorTrapezoidalDefect n k / (n : ℝ)| * w ((2 * n - 1) / (2 * k + 1)) +
          |approxSecondDiff w n k| +
          ((k : ℝ) / (n : ℝ)) * (w (n / (k + 1)) - w (n / k)) := by
  intro w n k hn hk hw0 h1 h2
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hw_mid_nonneg : 0 ≤ w ((2 * n - 1) / (2 * k + 1)) := le_trans hw0 h1
  have hfloor := (floorTrapezoidalDefect_bilateral_and_abs_bounds n k hn hk).2.2
  have hfloor_div : |floorTrapezoidalDefect n k / (n : ℝ)| ≤ (2 * (k : ℝ) + 1) / (n : ℝ) := by
    rw [abs_div, abs_of_pos hn_pos]
    exact div_le_div_of_nonneg_right hfloor (by positivity)
  have hfloor_mul :
      |floorTrapezoidalDefect n k / (n : ℝ)| * w ((2 * n - 1) / (2 * k + 1)) ≤
        ((2 * (k : ℝ) + 1) / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1)) :=
    mul_le_mul_of_nonneg_right hfloor_div hw_mid_nonneg
  constructor
  · rw [approxTrapezoidalDefect_scaledWeight_div_eq_floor_add_firstDiff]
    have htri := abs_add_le
      ((floorTrapezoidalDefect n k / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1)))
      (scaledWeightFirstDiffTerm w n k / (n : ℝ))
    have h1_abs :
        |(floorTrapezoidalDefect n k / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1))| =
          |floorTrapezoidalDefect n k / (n : ℝ)| * w ((2 * n - 1) / (2 * k + 1)) := by
      rw [abs_mul, abs_of_nonneg hw_mid_nonneg]
    have h2_abs :
        |scaledWeightFirstDiffTerm w n k / (n : ℝ)| =
          |scaledWeightFirstDiffTerm w n k| / (n : ℝ) := by
      rw [abs_div, abs_of_pos hn_pos]
    have hfirst := (scaledWeightFirstDiffTerm_bounds_of_antitone_window w n k h1 h2).2.2
    have hfirst_div :
        |scaledWeightFirstDiffTerm w n k| / (n : ℝ) ≤ w (n / (k + 1)) - w (n / k) := by
      rw [div_le_iff₀ hn_pos]
      linarith
    linarith
  · rw [approxTrapezoidalDefect_scaledWeight_div_eq_floor_add_secondDiff_add_coupling w n k hn]
    have htri1 := abs_add_le
      ((floorTrapezoidalDefect n k / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1)) +
        approxSecondDiff w n k)
      (remainderCouplingDefect w n k / (n : ℝ))
    have htri2 := abs_add_le
      ((floorTrapezoidalDefect n k / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1)))
      (approxSecondDiff w n k)
    have h1_abs :
        |(floorTrapezoidalDefect n k / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1))| =
          |floorTrapezoidalDefect n k / (n : ℝ)| * w ((2 * n - 1) / (2 * k + 1)) := by
      rw [abs_mul, abs_of_nonneg hw_mid_nonneg]
    have h3_abs :
        |remainderCouplingDefect w n k / (n : ℝ)| =
          |remainderCouplingDefect w n k| / (n : ℝ) := by
      rw [abs_div, abs_of_pos hn_pos]
    have hcoup := abs_remainderCouplingDefect_le_of_antitone_window w n k hk h1 h2
    have hcoup_div :
        |remainderCouplingDefect w n k| / (n : ℝ) ≤
          ((k : ℝ) / (n : ℝ)) * (w (n / (k + 1)) - w (n / k)) := by
      rw [div_le_iff₀ hn_pos]
      have halg :
          ((k : ℝ) / (n : ℝ)) * (w (n / (k + 1)) - w (n / k)) * (n : ℝ) =
            (k : ℝ) * (w (n / (k + 1)) - w (n / k)) := by
        field_simp [ne_of_gt hn_pos]
      linarith
    linarith

/-- Telescoping sum of endpoint weight differences across `k ∈ Finset.Icc 1 K`:
`∑_{k=1}^K (w ⌊n/(k + 1)⌋ - w ⌊n/k⌋) = w ⌊n/(K + 1)⌋ - w n`. -/
theorem sum_Icc_weight_div_succ_sub_div_eq :
    ∀ (w : ℕ → ℝ) (n K : ℕ),
      ∑ k ∈ Finset.Icc 1 K, (w (n / (k + 1)) - w (n / k)) = w (n / (K + 1)) - w n := by
  intro w n K
  have h := sum_Icc_succ_sub_eq (fun k : ℕ ↦ w (n / k)) K
  simpa using h

/-- Cumulative telescoping bound on `∑_{k=1}^K |approxSecondDiff w n k|` across `1 ≤ k ≤ K` for an
antitone weight `w`:
`∑_{k=1}^K |approxSecondDiff w n k| ≤ w ⌊n/(K + 1)⌋ - w n`. -/
theorem sum_abs_approxSecondDiff_le_of_antitone_windows :
    ∀ (w : ℕ → ℝ) (n K : ℕ),
      (∀ k ∈ Finset.Icc 1 K,
        w (n / k) ≤ w ((2 * n - 1) / (2 * k + 1)) ∧
          w ((2 * n - 1) / (2 * k + 1)) ≤ w (n / (k + 1))) →
      ∑ k ∈ Finset.Icc 1 K, |approxSecondDiff w n k| ≤ w (n / (K + 1)) - w n := by
  intro w n K hw
  calc ∑ k ∈ Finset.Icc 1 K, |approxSecondDiff w n k|
    _ ≤ ∑ k ∈ Finset.Icc 1 K, (w (n / (k + 1)) - w (n / k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (approxSecondDiff_bounds_of_antitone_window w n k (hw k hk).1 (hw k hk).2).2.2
    _ = w (n / (K + 1)) - w n := sum_Icc_weight_div_succ_sub_div_eq w n K

/-- Cumulative telescoping bound on `∑_{k=1}^K |remainderCouplingDefect w n k / n|` across
`1 ≤ k ≤ K` for an antitone weight `w`:
`∑_{k=1}^K |remainderCouplingDefect w n k / n| ≤ (K / n) * (w ⌊n/(K + 1)⌋ - w n)`. -/
theorem sum_abs_remainderCouplingDefect_div_le_of_antitone_windows :
    ∀ (w : ℕ → ℝ) (n K : ℕ), 1 ≤ n →
      (∀ k ∈ Finset.Icc 1 K,
        w (n / k) ≤ w ((2 * n - 1) / (2 * k + 1)) ∧
          w ((2 * n - 1) / (2 * k + 1)) ≤ w (n / (k + 1))) →
      ∑ k ∈ Finset.Icc 1 K, |remainderCouplingDefect w n k / (n : ℝ)| ≤
        ((K : ℝ) / (n : ℝ)) * (w (n / (K + 1)) - w n) := by
  intro w n K hn hw
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  calc ∑ k ∈ Finset.Icc 1 K, |remainderCouplingDefect w n k / (n : ℝ)|
    _ ≤ ∑ k ∈ Finset.Icc 1 K, (((K : ℝ) / (n : ℝ)) * (w (n / (k + 1)) - w (n / k))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkK : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
      have hwk := hw k hk
      have hcoup := abs_remainderCouplingDefect_le_of_antitone_window w n k hk1 hwk.1 hwk.2
      have hdiff_nonneg : 0 ≤ w (n / (k + 1)) - w (n / k) := by linarith [hwk.1, hwk.2]
      have hk_le_K :
          (k : ℝ) * (w (n / (k + 1)) - w (n / k)) ≤
            (K : ℝ) * (w (n / (k + 1)) - w (n / k)) :=
        mul_le_mul_of_nonneg_right hkK hdiff_nonneg
      rw [abs_div, abs_of_pos hn_pos, div_le_iff₀ hn_pos]
      have halg :
          ((K : ℝ) / (n : ℝ)) * (w (n / (k + 1)) - w (n / k)) * (n : ℝ) =
            (K : ℝ) * (w (n / (k + 1)) - w (n / k)) := by
        field_simp [ne_of_gt hn_pos]
      linarith
    _ = ((K : ℝ) / (n : ℝ)) * (w (n / (K + 1)) - w n) := by
      rw [← Finset.mul_sum, sum_Icc_weight_div_succ_sub_div_eq]

/-- Master cumulative bound for `∑_{k=1}^K |approxTrapezoidalDefect (scaledWeightMainTerm w) n k / n|`
for any nonnegative antitone weight `w`:
`∑_{k=1}^K |approxTrapezoidalDefect (scaledWeightMainTerm w) n k / n| ≤ (K(K + 2) / n) * w ⌊n/(K + 1)⌋ + (w ⌊n/(K + 1)⌋ - w n)`. -/
theorem sum_abs_approxTrapezoidalDefect_scaledWeight_div_le_of_antitone_windows :
    ∀ (w : ℕ → ℝ) (n K : ℕ), 1 ≤ n →
      (∀ k ∈ Finset.Icc 1 K,
        0 ≤ w (n / k) ∧
          w (n / k) ≤ w ((2 * n - 1) / (2 * k + 1)) ∧
          w ((2 * n - 1) / (2 * k + 1)) ≤ w (n / (k + 1)) ∧
          w ((2 * n - 1) / (2 * k + 1)) ≤ w (n / (K + 1))) →
      ∑ k ∈ Finset.Icc 1 K, |approxTrapezoidalDefect (scaledWeightMainTerm w) n k / (n : ℝ)| ≤
        ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * w (n / (K + 1)) + (w (n / (K + 1)) - w n) := by
  intro w n K hn hw
  calc ∑ k ∈ Finset.Icc 1 K, |approxTrapezoidalDefect (scaledWeightMainTerm w) n k / (n : ℝ)|
    _ ≤ ∑ k ∈ Finset.Icc 1 K,
          ((2 * (k : ℝ) + 1) * (w (n / (K + 1)) / (n : ℝ)) + (w (n / (k + 1)) - w (n / k))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hwk := hw k hk
      have hpt := (abs_approxTrapezoidalDefect_scaledWeight_div_le_of_antitone_window
        w n k hn hk1 hwk.1 hwk.2.1 hwk.2.2.1).1
      have hw_le :
          ((2 * (k : ℝ) + 1) / (n : ℝ)) * w ((2 * n - 1) / (2 * k + 1)) ≤
            ((2 * (k : ℝ) + 1) / (n : ℝ)) * w (n / (K + 1)) :=
        mul_le_mul_of_nonneg_left hwk.2.2.2 (by positivity)
      have halg :
          ((2 * (k : ℝ) + 1) / (n : ℝ)) * w (n / (K + 1)) =
            (2 * (k : ℝ) + 1) * (w (n / (K + 1)) / (n : ℝ)) := by ring
      linarith
    _ = ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * w (n / (K + 1)) + (w (n / (K + 1)) - w n) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_Icc_two_mul_add_one_eq,
        sum_Icc_weight_div_succ_sub_div_eq]
      ring

/-! ## Section 4: Specialization to `m ↦ m / log m` and Reciprocal-Logarithm Second Differences -/

/-- The reciprocal-logarithm weight `m ↦ 1 / log m`. -/
def invLog (m : ℕ) : ℝ :=
  1 / Real.log (m : ℝ)

/-- The logarithmic-density PNT main term `m ↦ m / log m`. -/
def logDensityMainTerm (m : ℕ) : ℝ :=
  (m : ℝ) / Real.log (m : ℝ)

/-- Identification of `logDensityMainTerm` with `scaledWeightMainTerm invLog` and
`fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)`. -/
theorem logDensityMainTerm_eq_scaledWeight_invLog :
    ∀ m : ℕ,
      logDensityMainTerm m = scaledWeightMainTerm invLog m ∧
        logDensityMainTerm = (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) := by
  intro m
  refine ⟨?_, rfl⟩
  unfold logDensityMainTerm scaledWeightMainTerm invLog
  ring

/-- **Exact Decompositions I & II for `approxTrapezoidalDefect (fun m => m / log m) n k / n`:**
Separates the floor-discretization defect
`(2k + 1) ⌊(2n - 1)/(2k + 1)⌋ - (k + 1) ⌊n/(k + 1)⌋ - k ⌊n/k⌋`
from the reciprocal-logarithm first differences (`scaledWeightFirstDiffTerm invLog n k / n`) and
from the reciprocal-logarithm second difference (`approxSecondDiff invLog n k`) plus the
Euclidean-remainder coupling defect (`remainderCouplingDefect invLog n k / n`). -/
theorem approxTrapezoidalDefect_logDensity_div_decompositions :
    ∀ n k : ℕ, 1 ≤ n →
      approxTrapezoidalDefect (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) n k / (n : ℝ) =
        (floorTrapezoidalDefect n k / (n : ℝ)) * invLog ((2 * n - 1) / (2 * k + 1)) +
          scaledWeightFirstDiffTerm invLog n k / (n : ℝ) ∧
      approxTrapezoidalDefect (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) n k / (n : ℝ) =
        (floorTrapezoidalDefect n k / (n : ℝ)) * invLog ((2 * n - 1) / (2 * k + 1)) +
          approxSecondDiff invLog n k +
          remainderCouplingDefect invLog n k / (n : ℝ) := by
  intro n k hn
  have hfun : (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) = scaledWeightMainTerm invLog := by
    funext m
    exact (logDensityMainTerm_eq_scaledWeight_invLog m).1
  rw [hfun]
  exact ⟨approxTrapezoidalDefect_scaledWeight_div_eq_floor_add_firstDiff invLog n k,
    approxTrapezoidalDefect_scaledWeight_div_eq_floor_add_secondDiff_add_coupling invLog n k hn⟩

/-- Positivity of `Real.log (m : ℝ)` and `invLog m` for all `2 ≤ m`. -/
theorem real_log_pos_and_invLog_pos_of_two_le :
    ∀ m : ℕ, 2 ≤ m → 0 < Real.log (m : ℝ) ∧ 0 < invLog m := by
  intro m hm
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  refine ⟨hlog, ?_⟩
  unfold invLog
  positivity

/-- Antitonicity of `invLog` on `[2, ∞)`: for `2 ≤ a ≤ b`, `1 / log b ≤ 1 / log a`. -/
theorem invLog_antitone_of_two_le :
    ∀ a b : ℕ, 2 ≤ a → a ≤ b → invLog b ≤ invLog a := by
  intro a b ha hab
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hab_r : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hlog_a : 0 < Real.log (a : ℝ) := (real_log_pos_and_invLog_pos_of_two_le a ha).1
  have hlog_le : Real.log (a : ℝ) ≤ Real.log (b : ℝ) := Real.log_le_log ha_pos hab_r
  unfold invLog
  exact one_div_le_one_div_of_le hlog_a hlog_le

/-- Exact algebraic representation of reciprocal-logarithm differences:
for `2 ≤ a` and `2 ≤ b`, `1 / log a - 1 / log b = (log b - log a) / (log a * log b)`. -/
theorem invLog_sub_eq_log_diff_div_mul :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      invLog a - invLog b =
        (Real.log (b : ℝ) - Real.log (a : ℝ)) / (Real.log (a : ℝ) * Real.log (b : ℝ)) := by
  intro a b ha hb
  have hla : Real.log (a : ℝ) ≠ 0 := ne_of_gt (real_log_pos_and_invLog_pos_of_two_le a ha).1
  have hlb : Real.log (b : ℝ) ≠ 0 := ne_of_gt (real_log_pos_and_invLog_pos_of_two_le b hb).1
  unfold invLog
  field_simp [hla, hlb]

/-- Complete monotone cutoff chain across `k ∈ Finset.Icc 1 K`:
`n / (K + 1) ≤ n / (k + 1) ≤ (2n - 1) / (2k + 1) ≤ n / k ≤ n`. -/
theorem div_cutoff_chain_of_mem_Icc :
    ∀ n K k : ℕ, 1 ≤ n → k ∈ Finset.Icc 1 K →
      n / (K + 1) ≤ n / (k + 1) ∧
        n / (k + 1) ≤ (2 * n - 1) / (2 * k + 1) ∧
        (2 * n - 1) / (2 * k + 1) ≤ n / k ∧
        n / k ≤ n := by
  intro n K k hn hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
  have hmid := div_succ_le_mid_and_mid_le_div n k hn hk1
  have hK : n / (K + 1) ≤ n / (k + 1) :=
    Nat.div_le_div_left (by omega : k + 1 ≤ K + 1) (by omega : 0 < k + 1)
  exact ⟨hK, hmid.1, hmid.2, Nat.div_le_self n k⟩

/-- Antitone reciprocal-logarithm ordering across the `k`-th window whenever `2 ≤ n / (K + 1)`:
`0 ≤ invLog (n / k) ≤ invLog ((2n - 1)/(2k + 1)) ≤ invLog (n / (k + 1)) ≤ invLog (n / (K + 1))`. -/
theorem invLog_window_ordering_of_two_le_div :
    ∀ n K k : ℕ, k ∈ Finset.Icc 1 K → 2 ≤ n / (K + 1) →
      0 ≤ invLog (n / k) ∧
        invLog (n / k) ≤ invLog ((2 * n - 1) / (2 * k + 1)) ∧
        invLog ((2 * n - 1) / (2 * k + 1)) ≤ invLog (n / (k + 1)) ∧
        invLog ((2 * n - 1) / (2 * k + 1)) ≤ invLog (n / (K + 1)) := by
  intro n K k hk h2
  have hn : 1 ≤ n := by
    have hle : n / (K + 1) ≤ n := Nat.div_le_self n (K + 1)
    omega
  have hchain := div_cutoff_chain_of_mem_Icc n K k hn hk
  have h_succ2 : 2 ≤ n / (k + 1) := le_trans h2 hchain.1
  have h_mid2 : 2 ≤ (2 * n - 1) / (2 * k + 1) := le_trans h_succ2 hchain.2.1
  have h_div2 : 2 ≤ n / k := le_trans h_mid2 hchain.2.2.1
  have hpos : 0 ≤ invLog (n / k) :=
    le_of_lt (real_log_pos_and_invLog_pos_of_two_le (n / k) h_div2).2
  exact ⟨hpos,
    invLog_antitone_of_two_le _ _ h_mid2 hchain.2.2.1,
    invLog_antitone_of_two_le _ _ h_succ2 hchain.2.1,
    invLog_antitone_of_two_le _ _ h2 (le_trans hchain.1 hchain.2.1)⟩

/-- Pointwise bounds on the reciprocal-logarithm second difference, Euclidean-remainder coupling,
and logarithmic-density trapezoidal defect whenever `1 ≤ k` and `2 ≤ n / (k + 1)`. -/
theorem pointwise_logDensity_trapezoidal_and_secondDiff_bounds :
    ∀ n k : ℕ, 1 ≤ k → 2 ≤ n / (k + 1) →
      |approxSecondDiff invLog n k| ≤ invLog (n / (k + 1)) - invLog (n / k) ∧
      |remainderCouplingDefect invLog n k / (n : ℝ)| ≤
        ((k : ℝ) / (n : ℝ)) * (invLog (n / (k + 1)) - invLog (n / k)) ∧
      |approxTrapezoidalDefect (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) n k / (n : ℝ)| ≤
        ((2 * (k : ℝ) + 1) / (n : ℝ)) * invLog ((2 * n - 1) / (2 * k + 1)) +
          (invLog (n / (k + 1)) - invLog (n / k)) := by
  intro n k hk h2
  have hn : 1 ≤ n := by
    have hle : n / (k + 1) ≤ n := Nat.div_le_self n (k + 1)
    omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmem : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  have hord := invLog_window_ordering_of_two_le_div n k k hmem h2
  have hsec := (approxSecondDiff_bounds_of_antitone_window invLog n k hord.2.1 hord.2.2.1).2.2
  have hcoup := abs_remainderCouplingDefect_le_of_antitone_window
    invLog n k hk hord.2.1 hord.2.2.1
  have hcoup_div :
      |remainderCouplingDefect invLog n k / (n : ℝ)| ≤
        ((k : ℝ) / (n : ℝ)) * (invLog (n / (k + 1)) - invLog (n / k)) := by
    rw [abs_div, abs_of_pos hn_pos, div_le_iff₀ hn_pos]
    have halg :
        ((k : ℝ) / (n : ℝ)) * (invLog (n / (k + 1)) - invLog (n / k)) * (n : ℝ) =
          (k : ℝ) * (invLog (n / (k + 1)) - invLog (n / k)) := by
      field_simp [ne_of_gt hn_pos]
    linarith
  have hfun : (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) = scaledWeightMainTerm invLog := by
    funext m
    exact (logDensityMainTerm_eq_scaledWeight_invLog m).1
  rw [hfun]
  have htrap := (abs_approxTrapezoidalDefect_scaledWeight_div_le_of_antitone_window
    invLog n k hn hk hord.1 hord.2.1 hord.2.2.1).1
  exact ⟨hsec, hcoup_div, htrap⟩

/-- Cumulative telescoping bound on the reciprocal-logarithm second differences across `1 ≤ k ≤ K`:
`∑_{k=1}^K |approxSecondDiff invLog n k| ≤ 1 / log ⌊n / (K + 1)⌋ - 1 / log n`. -/
theorem sum_abs_invLog_secondDiff_le :
    ∀ n K : ℕ, 2 ≤ n / (K + 1) →
      ∑ k ∈ Finset.Icc 1 K, |approxSecondDiff invLog n k| ≤
        invLog (n / (K + 1)) - invLog n := by
  intro n K h2
  apply sum_abs_approxSecondDiff_le_of_antitone_windows
  intro k hk
  have hord := invLog_window_ordering_of_two_le_div n K k hk h2
  exact ⟨hord.2.1, hord.2.2.1⟩

/-- **Main theorem:**
For `2 ≤ n / (K + 1)`, the cumulative logarithmic-density main-term trapezoidal defect across
`1 ≤ k ≤ K` satisfies
`∑_{k=1}^K |approxTrapezoidalDefect (fun m => m / log m) n k / n| ≤ (K(K + 2) / n) * (1 / log ⌊n/(K + 1)⌋) + (1 / log ⌊n/(K + 1)⌋ - 1 / log n)`. -/
theorem sum_abs_logDensity_trapezoidalDefect_div_le :
    ∀ n K : ℕ, 2 ≤ n / (K + 1) →
      ∑ k ∈ Finset.Icc 1 K,
        |approxTrapezoidalDefect (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) n k / (n : ℝ)| ≤
        ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * (1 / Real.log ((n / (K + 1) : ℕ) : ℝ)) +
          (1 / Real.log ((n / (K + 1) : ℕ) : ℝ) - 1 / Real.log (n : ℝ)) := by
  intro n K h2
  have hn : 1 ≤ n := by
    have hle : n / (K + 1) ≤ n := Nat.div_le_self n (K + 1)
    omega
  have hfun : (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) = scaledWeightMainTerm invLog := by
    funext m
    exact (logDensityMainTerm_eq_scaledWeight_invLog m).1
  rw [hfun]
  have hsum := sum_abs_approxTrapezoidalDefect_scaledWeight_div_le_of_antitone_windows
    invLog n K hn (fun k hk ↦ invLog_window_ordering_of_two_le_div n K k hk h2)
  simpa [invLog] using hsum

/-- Explicit cumulative bound separating the floor-discretization sum, the reciprocal-logarithm
second-difference sum, and the Euclidean-remainder coupling error across `1 ≤ k ≤ K`. -/
theorem sum_abs_logDensity_trapezoidalDefect_div_le_secondDiff_form :
    ∀ n K : ℕ, 2 ≤ n / (K + 1) →
      ∑ k ∈ Finset.Icc 1 K,
        |approxTrapezoidalDefect (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) n k / (n : ℝ)| ≤
        (∑ k ∈ Finset.Icc 1 K,
          |floorTrapezoidalDefect n k / (n : ℝ)| * invLog ((2 * n - 1) / (2 * k + 1))) +
        (∑ k ∈ Finset.Icc 1 K, |approxSecondDiff invLog n k|) +
        ((K : ℝ) / (n : ℝ)) * (invLog (n / (K + 1)) - invLog n) := by
  intro n K h2
  have hn : 1 ≤ n := by
    have hle : n / (K + 1) ≤ n := Nat.div_le_self n (K + 1)
    omega
  have hfun : (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) = scaledWeightMainTerm invLog := by
    funext m
    exact (logDensityMainTerm_eq_scaledWeight_invLog m).1
  rw [hfun]
  have hstep :
      ∑ k ∈ Finset.Icc 1 K, |approxTrapezoidalDefect (scaledWeightMainTerm invLog) n k / (n : ℝ)| ≤
        ∑ k ∈ Finset.Icc 1 K,
          (|floorTrapezoidalDefect n k / (n : ℝ)| * invLog ((2 * n - 1) / (2 * k + 1)) +
            |approxSecondDiff invLog n k| +
            |remainderCouplingDefect invLog n k / (n : ℝ)|) := by
    apply Finset.sum_le_sum
    intro k hk
    have hord := invLog_window_ordering_of_two_le_div n K k hk h2
    have hw_mid : 0 ≤ invLog ((2 * n - 1) / (2 * k + 1)) := le_trans hord.1 hord.2.1
    rw [approxTrapezoidalDefect_scaledWeight_div_eq_floor_add_secondDiff_add_coupling invLog n k hn]
    have htri1 := abs_add_le
      ((floorTrapezoidalDefect n k / (n : ℝ)) * invLog ((2 * n - 1) / (2 * k + 1)) +
        approxSecondDiff invLog n k)
      (remainderCouplingDefect invLog n k / (n : ℝ))
    have htri2 := abs_add_le
      ((floorTrapezoidalDefect n k / (n : ℝ)) * invLog ((2 * n - 1) / (2 * k + 1)))
      (approxSecondDiff invLog n k)
    rw [abs_mul, abs_of_nonneg hw_mid] at htri2
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hstep
  have hcoup := sum_abs_remainderCouplingDefect_div_le_of_antitone_windows invLog n K hn
    (fun k hk ↦ ⟨(invLog_window_ordering_of_two_le_div n K k hk h2).2.1,
      (invLog_window_ordering_of_two_le_div n K k hk h2).2.2.1⟩)
  linarith

/-- End-to-end bound on `|∑_{k=1}^K midpointWindowApprox n k|` combining the floor-discretization
majorant `(K(K + 2) / n) * invLog ⌊n/(K + 1)⌋`, the telescoped reciprocal-logarithm difference
`invLog ⌊n/(K + 1)⌋ - invLog n`, the scale-proportional PNT remainder variation `4 K δ`, and the
prime-count quadrature defect `(π(n) - π(⌊n/(K + 1)⌋)) / (2n)`. -/
theorem abs_sum_midpointWindowApprox_le_logDensity_floor_and_invLog :
    ∀ (n K : ℕ) (δ : ℝ), 0 ≤ δ → 2 ≤ n / (K + 1) →
      (∀ m : ℕ, m ≤ n →
        |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ * (m : ℝ)) →
      |∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k| ≤
        ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * invLog (n / (K + 1)) +
          (invLog (n / (K + 1)) - invLog n) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by
  intro n K δ hδ h2 hR
  have hn : 1 ≤ n := by
    have hle : n / (K + 1) ≤ n := Nat.div_le_self n (K + 1)
    omega
  have hmid := abs_sum_midpointWindowApprox_le_trapezoidal_approx_and_pnt
    (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) n K δ hn hδ hR
  have htrap := sum_abs_logDensity_trapezoidalDefect_div_le n K h2
  unfold invLog
  linarith

/-- Master asymptotic discrepancy bound for `|upperHalfPrimeSum n - log(log n) / 2|` with the
logarithmic-density main-term trapezoidal defect fully separated and bounded by the
floor-discretization majorant `(K(K + 2) / n) * invLog ⌊n/(K + 1)⌋` and the telescoped
reciprocal-logarithm difference `invLog ⌊n/(K + 1)⌋ - invLog n`. -/
theorem abs_upperHalfPrimeSum_sub_half_mertens_le_logDensity_master :
    ∀ (n K M : ℕ) (δ : ℝ),
      0 ≤ δ → 2 ≤ n / (K + 1) → n ≤ M →
      (∀ p ∈ oddPrimeRange (n / (K + 1)), p ∣ M) →
      (∀ m : ℕ, m ≤ n →
        |pntRemainder (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) m| ≤ δ * (m : ℝ)) →
      |upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2| ≤
        (|upperBoundedPrimeSum (n / (K + 1)) n - upperBoundedPrimeSum (n / (K + 1)) (M - n)| +
          dividingOddBoundedSum (n / (K + 1)) n + 1 / 2 +
          ((K : ℝ) * ((K : ℝ) + 2) / (n : ℝ)) * invLog (n / (K + 1)) +
          (invLog (n / (K + 1)) - invLog n) +
          4 * (K : ℝ) * δ +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (n : ℝ) +
          |Mertens.M + Mertens.E₂p (n : ℝ)|) / 2 := by
  intro n K M δ hδ h2 hle hM hR
  have hn : 1 ≤ n := by
    have hdiv_le : n / (K + 1) ≤ n := Nat.div_le_self n (K + 1)
    omega
  have hmaster := abs_upperHalfPrimeSum_sub_half_mertens_le_abel_and_pnt_remainder
    (fun m : ℕ ↦ (m : ℝ) / Real.log (m : ℝ)) n K M δ hn hδ h2 hle hM hR
  have htrap := sum_abs_logDensity_trapezoidalDefect_div_le n K h2
  unfold invLog
  linarith

/-! ## Section 5: Positive and Negative Falsifying Controls -/

/-- Positive control at `n = 6`, `k = 1` and `k = 2`: verifies exact values of `midFloorDeficit`,
`succFloorDeficit`, `divFloorDeficit`, `floorTrapezoidalDefect`, and `floorLeftDefect`. -/
theorem positive_control_floor_defects_six :
    midFloorDeficit 6 1 = 3 ∧
      succFloorDeficit 6 1 = 0 ∧
      divFloorDeficit 6 1 = 0 ∧
      floorTrapezoidalDefect 6 1 = -3 ∧
      floorLeftDefect 6 1 = -3 ∧
      floorTrapezoidalDefect 6 2 = -2 := by
  unfold midFloorDeficit succFloorDeficit divFloorDeficit floorTrapezoidalDefect floorLeftDefect
  norm_num

/-- Positive sharpness control at `n = 11`, `k = 3`: `floorTrapezoidalDefect 11 3 = 4 = 2 * 3 - 2`,
attaining the upper bound `2k - 2` of `floorTrapezoidalDefect_bilateral_and_abs_bounds` with equality. -/
theorem positive_control_floor_trapezoidal_upper_extremizer_eleven_three :
    floorTrapezoidalDefect 11 3 = 4 ∧
      floorTrapezoidalDefect 11 3 = 2 * (3 : ℝ) - 2 := by
  unfold floorTrapezoidalDefect
  norm_num

/-- Negative control at `n = 6`, `k = 1`: omitting the floor-discretization term
`(floorTrapezoidalDefect 6 1 / 6) * invLog 3 = -invLog 3 / 2` falsifies the naive approximation
`approxTrapezoidalDefect logDensityMainTerm 6 1 / 6 = approxSecondDiff invLog 6 1`. -/
theorem negative_control_logDensity_trapezoidalDefect_not_pure_secondDiff :
    approxTrapezoidalDefect logDensityMainTerm 6 1 / 6 - approxSecondDiff invLog 6 1 =
        -(invLog 3) / 2 ∧
      approxTrapezoidalDefect logDensityMainTerm 6 1 / 6 ≠ approxSecondDiff invLog 6 1 := by
  have hmid : (2 * 6 - 1) / (2 * 1 + 1) = 3 := by decide
  have hdiv : 6 / 1 = 6 := by decide
  have hdiff :
      approxTrapezoidalDefect logDensityMainTerm 6 1 / 6 - approxSecondDiff invLog 6 1 =
        -(invLog 3) / 2 := by
    unfold approxTrapezoidalDefect logDensityMainTerm approxSecondDiff invLog
    rw [hmid, hdiv]
    norm_num
    ring
  refine ⟨hdiff, ?_⟩
  intro heq
  have hpos : 0 < invLog 3 := (real_log_pos_and_invLog_pos_of_two_le 3 (by decide)).2
  linarith


end Erdos726

end
