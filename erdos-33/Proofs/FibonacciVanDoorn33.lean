module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
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

public import SquareComplementBounds33
@[expose] public section
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
noncomputable section
open Filter Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos33.Core

/-- Explicit Fibonacci block-width sequence `M_j = F_{j+2}` (`M_0 = 1, M_1 = 2, M_2 = 3, ...`)
for Wouter van Doorn's recursive shifted-block construction. -/
def fibBlockWidth (j : ℕ) : ℕ := Nat.fib (j + 2)

/-- Every Fibonacci block width `fibBlockWidth j = F_{j+2}` is strictly positive (`≥ 1`). -/
theorem one_le_fibBlockWidth (j : ℕ) : 1 ≤ fibBlockWidth j := by
  unfold fibBlockWidth
  exact Nat.fib_pos.2 (by omega)

/-- Linear growth lower bound `j + 1 ≤ fibBlockWidth j` for all `j : ℕ`. -/
theorem add_one_le_fibBlockWidth (j : ℕ) : j + 1 ≤ fibBlockWidth j := by
  unfold fibBlockWidth
  induction j with
  | zero => simp
  | succ j ih =>
      have hpos : 1 ≤ Nat.fib (j + 1) := Nat.fib_pos.2 (by omega)
      have hrec : Nat.fib (j + 1 + 2) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
      omega

/-- Exact closed-form linear sum identity for `fibBlockWidth`:
`(∑_{j=0}^{K-1} F_{j+2}) + 2 = F_{K+3}`. -/
theorem sum_fibBlockWidth_add_two (K : ℕ) :
    (∑ j ∈ Finset.range K, fibBlockWidth j) + 2 = Nat.fib (K + 3) := by
  induction K with
  | zero => decide
  | succ K ih =>
      rw [Finset.sum_range_succ]
      unfold fibBlockWidth at *
      have hrec : Nat.fib (K + 1 + 3) = Nat.fib (K + 2) + Nat.fib (K + 3) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (@Nat.fib_add_two (K + 2))
      omega

/-- Exact closed-form formula for the `K`-th Fibonacci block horizon `vanDoornBlockStart fibBlockWidth K`:
`vanDoornBlockStart fibBlockWidth K + 5 = F_{K+1} * F_{K+2} + 2 * F_{K+3}`. -/
theorem vanDoornBlockStart_fibBlockWidth_add_five (K : ℕ) :
    vanDoornBlockStart fibBlockWidth K + 5 =
      Nat.fib (K + 1) * Nat.fib (K + 2) + 2 * Nat.fib (K + 3) := by
  induction K with
  | zero => decide
  | succ K ih =>
      simp only [vanDoornBlockStart, fibBlockWidth]
      have hrec1 : Nat.fib (K + 1 + 2) = Nat.fib (K + 1) + Nat.fib (K + 2) := Nat.fib_add_two
      have hrec2 : Nat.fib (K + 1 + 3) = Nat.fib (K + 2) + Nat.fib (K + 3) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (@Nat.fib_add_two (K + 2))
      nlinarith

/-- For all `K ≥ 1`, `vanDoornBlockStart fibBlockWidth K` strictly exceeds `F_{K+1} * F_{K+2}`:
`F_{K+1} * F_{K+2} + 1 ≤ vanDoornBlockStart fibBlockWidth K`. -/
theorem fib_mul_add_one_le_vanDoornBlockStart_fibBlockWidth {K : ℕ} (hK : 1 ≤ K) :
    Nat.fib (K + 1) * Nat.fib (K + 2) + 1 ≤ vanDoornBlockStart fibBlockWidth K := by
  have hstart := vanDoornBlockStart_fibBlockWidth_add_five K
  have hfib : 3 ≤ Nat.fib (K + 3) := by
    have hmono : Nat.fib 4 ≤ Nat.fib (K + 3) := Nat.fib_mono (by omega)
    have h4 : Nat.fib 4 = 3 := by decide
    omega
  omega

/-- Universal cubic growth lower bound `K^3 ≤ 3 * vanDoornBlockStart fibBlockWidth K`. -/
theorem cube_le_three_mul_vanDoornBlockStart_fibBlockWidth (K : ℕ) :
    K ^ 3 ≤ 3 * vanDoornBlockStart fibBlockWidth K := by
  induction K with
  | zero => simp [vanDoornBlockStart]
  | succ K ih =>
      simp only [vanDoornBlockStart]
      have hlin : K + 1 ≤ fibBlockWidth K := add_one_le_fibBlockWidth K
      have hsq : (K + 1) ^ 2 ≤ (fibBlockWidth K) ^ 2 := Nat.pow_le_pow_left hlin 2
      nlinarith

/-- **Subtraction-Free Cassini Discrepancy Sandwich for Fibonacci Numbers**:
for all `n : ℕ`, `F_{n+1}^2 ≤ F_n * F_{n+1} + F_n^2 + 1` and
`F_n * F_{n+1} + F_n^2 ≤ F_{n+1}^2 + 1`. -/
theorem fib_cassini_discrepancy_bounds (n : ℕ) :
    Nat.fib (n + 1) ^ 2 ≤ Nat.fib n * Nat.fib (n + 1) + Nat.fib n ^ 2 + 1 ∧
      Nat.fib n * Nat.fib (n + 1) + Nat.fib n ^ 2 ≤ Nat.fib (n + 1) ^ 2 + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases ih with ⟨ih1, ih2⟩
      have hrec : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      constructor <;> nlinarith [hrec]

/-- Exact fifth-power golden-ratio reduction `c * φ^5 = c * (5 * φ + 3)`. -/
theorem goldenRatio_pow_five_eq (c : ℝ) :
    c * Real.goldenRatio ^ 5 = c * (5 * Real.goldenRatio + 3) := by
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  calc
    c * Real.goldenRatio ^ 5
        = c * (5 * Real.goldenRatio + 3) +
            c * (Real.goldenRatio ^ 3 + Real.goldenRatio ^ 2 + 2 * Real.goldenRatio + 3) *
              (Real.goldenRatio ^ 2 - (Real.goldenRatio + 1)) := by ring
    _ = c * (5 * Real.goldenRatio + 3) := by rw [hsq]; ring

/-- **Golden-Ratio Cassini Polynomial Factorization**:
for any real `u, v`, `((u + 2v)^2 - (5φ + 3)uv)(v + (φ - 1)u) = (4v - (φ - 1)u)(v^2 - uv - u^2)`. -/
theorem goldenRatio_cassini_factorization (u v : ℝ) :
    ((u + 2 * v) ^ 2 - (5 * Real.goldenRatio + 3) * u * v) *
      (v + (Real.goldenRatio - 1) * u) =
        (4 * v - (Real.goldenRatio - 1) * u) * (v ^ 2 - u * v - u ^ 2) := by
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  calc
    ((u + 2 * v) ^ 2 - (5 * Real.goldenRatio + 3) * u * v) *
        (v + (Real.goldenRatio - 1) * u)
      = (4 * v - (Real.goldenRatio - 1) * u) * (v ^ 2 - u * v - u ^ 2) -
          5 * u ^ 2 * v * (Real.goldenRatio ^ 2 - (Real.goldenRatio + 1)) := by ring
    _ = (4 * v - (Real.goldenRatio - 1) * u) * (v ^ 2 - u * v - u ^ 2) := by
      rw [hsq]; ring

/-- For any `u ≥ 0` and `v > 0` satisfying the Cassini discrepancy bound `-1 ≤ v^2 - uv - u^2 ≤ 1`,
`(u + 2v)^2 ≤ φ^5 * (u * v) + 4`. -/
theorem add_two_mul_sq_le_goldenRatio_pow_five_mul_add_four {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 < v)
    (hlo : -1 ≤ v ^ 2 - u * v - u ^ 2)
    (hhi : v ^ 2 - u * v - u ^ 2 ≤ 1) :
    (u + 2 * v) ^ 2 ≤ Real.goldenRatio ^ 5 * (u * v) + 4 := by
  have h1 : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
  have hden : 0 < v + (Real.goldenRatio - 1) * u := by nlinarith
  have hfac := goldenRatio_cassini_factorization u v
  have h5 := goldenRatio_pow_five_eq (u * v)
  have hprod :
      ((u + 2 * v) ^ 2 - (5 * Real.goldenRatio + 3) * u * v) *
        (v + (Real.goldenRatio - 1) * u) ≤
          4 * (v + (Real.goldenRatio - 1) * u) := by
    by_cases hsign : 0 ≤ v ^ 2 - u * v - u ^ 2
    · have hcoef : 4 * v - (Real.goldenRatio - 1) * u ≤ 4 * (v + (Real.goldenRatio - 1) * u) := by
        nlinarith
      nlinarith
    · have hcoef : -(4 * (v + (Real.goldenRatio - 1) * u)) ≤ 4 * v - (Real.goldenRatio - 1) * u := by
        nlinarith
      nlinarith
  nlinarith

/-- Universal Fibonacci-to-golden-ratio square bound:
for all `K : ℕ`, `(F_{K+4} : ℝ)^2 ≤ φ^5 * (F_{K+1} * F_{K+2}) + 4`. -/
theorem fib_add_four_sq_le_goldenRatio_pow_five_mul_add_four (K : ℕ) :
    (Nat.fib (K + 4) : ℝ) ^ 2 ≤
      Real.goldenRatio ^ 5 * ((Nat.fib (K + 1) : ℝ) * (Nat.fib (K + 2) : ℝ)) + 4 := by
  have hu : 0 ≤ (Nat.fib (K + 1) : ℝ) := Nat.cast_nonneg _
  have hv_nat : 1 ≤ Nat.fib (K + 2) := Nat.fib_pos.2 (by omega)
  have hv : 0 < (Nat.fib (K + 2) : ℝ) := Nat.cast_pos.2 hv_nat
  rcases fib_cassini_discrepancy_bounds (K + 1) with ⟨hc1, hc2⟩
  have hc1_real : (Nat.fib (K + 2) : ℝ) ^ 2 ≤
      (Nat.fib (K + 1) : ℝ) * (Nat.fib (K + 2) : ℝ) + (Nat.fib (K + 1) : ℝ) ^ 2 + 1 := by
    exact_mod_cast hc1
  have hc2_real : (Nat.fib (K + 1) : ℝ) * (Nat.fib (K + 2) : ℝ) + (Nat.fib (K + 1) : ℝ) ^ 2 ≤
      (Nat.fib (K + 2) : ℝ) ^ 2 + 1 := by
    exact_mod_cast hc2
  have hrec3 : Nat.fib (K + 3) = Nat.fib (K + 1) + Nat.fib (K + 2) := Nat.fib_add_two
  have hrec4 : Nat.fib (K + 4) = Nat.fib (K + 2) + Nat.fib (K + 3) := Nat.fib_add_two
  have hnat : Nat.fib (K + 4) = Nat.fib (K + 1) + 2 * Nat.fib (K + 2) := by omega
  have hfib4 : (Nat.fib (K + 4) : ℝ) = (Nat.fib (K + 1) : ℝ) + 2 * (Nat.fib (K + 2) : ℝ) := by
    exact_mod_cast hnat
  rw [hfib4]
  exact add_two_mul_sq_le_goldenRatio_pow_five_mul_add_four hu hv (by linarith) (by linarith)

/-- Unconditional square bound on the prefix sum of Fibonacci block widths:
for all `K ≥ 1`, `(∑_{j=0}^K F_{j+2})^2 ≤ φ^5 * vanDoornBlockStart fibBlockWidth K`. -/
theorem sum_fibBlockWidth_sq_le_goldenRatio_pow_five_mul_start {K : ℕ} (hK : 1 ≤ K) :
    ((∑ j ∈ Finset.range (K + 1), fibBlockWidth j : ℕ) : ℝ) ^ 2 ≤
      Real.goldenRatio ^ 5 * (vanDoornBlockStart fibBlockWidth K : ℝ) := by
  have hsum_nat := sum_fibBlockWidth_add_two (K + 1)
  have hsum_real : ((∑ j ∈ Finset.range (K + 1), fibBlockWidth j : ℕ) : ℝ) + 2 =
      (Nat.fib (K + 1 + 3) : ℝ) := by exact_mod_cast hsum_nat
  have hidx : K + 1 + 3 = K + 4 := by omega
  rw [hidx] at hsum_real
  have hfib4_ge : (2 : ℝ) ≤ (Nat.fib (K + 4) : ℝ) := by linarith
  have hsq4 := fib_add_four_sq_le_goldenRatio_pow_five_mul_add_four K
  have hstart_ge :
      ((Nat.fib (K + 1) : ℝ) * (Nat.fib (K + 2) : ℝ)) + 1 ≤
        (vanDoornBlockStart fibBlockWidth K : ℝ) := by
    exact_mod_cast fib_mul_add_one_le_vanDoornBlockStart_fibBlockWidth hK
  have hphi5_pos : 0 < Real.goldenRatio ^ 5 := pow_pos Real.goldenRatio_pos 5
  nlinarith

/-- **Unconditional Main-Term Fibonacci Block-Ratio Bound**:
for all `K ≥ 1`, `2 * (∑_{j=0}^K F_{j+2}) / √(vanDoornBlockStart fibBlockWidth K) ≤ 2 * φ^(5/2)`. -/
theorem two_mul_sum_fibBlockWidth_div_sqrt_start_le {K : ℕ} (hK : 1 ≤ K) :
    (2 * ((∑ j ∈ Finset.range (K + 1), fibBlockWidth j : ℕ) : ℝ)) /
      Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) ≤
        2 * Real.goldenRatio ^ ((5 : ℝ) / 2) := by
  have hB_pos_nat : 1 ≤ vanDoornBlockStart fibBlockWidth K :=
    one_le_vanDoornBlockStart_of_pos one_le_fibBlockWidth hK
  have hB_pos : 0 < (vanDoornBlockStart fibBlockWidth K : ℝ) := Nat.cast_pos.2 hB_pos_nat
  have hsqrt_pos : 0 < Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) :=
    Real.sqrt_pos.2 hB_pos
  rw [div_le_iff₀ hsqrt_pos]
  have hsq_bound := sum_fibBlockWidth_sq_le_goldenRatio_pow_five_mul_start hK
  have hphi_pos : 0 ≤ Real.goldenRatio := le_of_lt Real.goldenRatio_pos
  have hphi5 : (Real.goldenRatio ^ ((5 : ℝ) / 2)) ^ 2 = Real.goldenRatio ^ 5 := by
    rw [← Real.rpow_natCast (Real.goldenRatio ^ ((5 : ℝ) / 2)) 2, ← Real.rpow_mul hphi_pos]
    norm_num
  have hrhs_nonneg : 0 ≤ 2 * Real.goldenRatio ^ ((5 : ℝ) / 2) *
      Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) := by positivity
  have hsq_rhs :
      (2 * Real.goldenRatio ^ ((5 : ℝ) / 2) *
        Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ)) ^ 2 =
          4 * (Real.goldenRatio ^ 5 * (vanDoornBlockStart fibBlockWidth K : ℝ)) := by
    calc
      (2 * Real.goldenRatio ^ ((5 : ℝ) / 2) *
        Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ)) ^ 2
          = 4 * (Real.goldenRatio ^ ((5 : ℝ) / 2)) ^ 2 *
              (Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ)) ^ 2 := by ring
      _ = 4 * (Real.goldenRatio ^ 5 * (vanDoornBlockStart fibBlockWidth K : ℝ)) := by
          rw [hphi5, Real.sq_sqrt (le_of_lt hB_pos)]
          ring
  have hsq_lhs :
      (2 * ((∑ j ∈ Finset.range (K + 1), fibBlockWidth j : ℕ) : ℝ)) ^ 2 ≤
        (2 * Real.goldenRatio ^ ((5 : ℝ) / 2) *
          Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ)) ^ 2 := by
    rw [hsq_rhs]
    linarith
  exact le_of_sq_le_sq hsq_lhs hrhs_nonneg

/-- **Quantitative Fibonacci Block-Scale Ratio Bound with Drift**:
for all `K ≥ 1`,
`(2 * ∑_{j=0}^K F_{j+2} + K) / √(vanDoornBlockStart fibBlockWidth K) ≤ 2 * φ^(5/2) + √(3 / K)`. -/
theorem fibBlockWidth_block_ratio_le_add_sqrt_three_div {K : ℕ} (hK : 1 ≤ K) :
    ((2 * (∑ j ∈ Finset.range (K + 1), fibBlockWidth j) + K : ℕ) : ℝ) /
      Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) ≤
        2 * Real.goldenRatio ^ ((5 : ℝ) / 2) + Real.sqrt (3 / (K : ℝ)) := by
  have hB_pos_nat : 1 ≤ vanDoornBlockStart fibBlockWidth K :=
    one_le_vanDoornBlockStart_of_pos one_le_fibBlockWidth hK
  have hB_pos : 0 < (vanDoornBlockStart fibBlockWidth K : ℝ) := Nat.cast_pos.2 hB_pos_nat
  have hK_pos : 0 < (K : ℝ) := Nat.cast_pos.2 hK
  have hmain := two_mul_sum_fibBlockWidth_div_sqrt_start_le hK
  have hcube : (K : ℝ) ^ 3 ≤ 3 * (vanDoornBlockStart fibBlockWidth K : ℝ) := by
    exact_mod_cast cube_le_three_mul_vanDoornBlockStart_fibBlockWidth K
  have hdrift_sq :
      ((K : ℝ) / Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ)) ^ 2 ≤
        (Real.sqrt (3 / (K : ℝ))) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hB_pos), Real.sq_sqrt (by positivity)]
    rw [div_le_div_iff₀ hB_pos hK_pos]
    nlinarith
  have hdrift :
      (K : ℝ) / Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) ≤
        Real.sqrt (3 / (K : ℝ)) :=
    le_of_sq_le_sq hdrift_sq (Real.sqrt_nonneg _)
  have hsplit :
      ((2 * (∑ j ∈ Finset.range (K + 1), fibBlockWidth j) + K : ℕ) : ℝ) /
        Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) =
          (2 * ((∑ j ∈ Finset.range (K + 1), fibBlockWidth j : ℕ) : ℝ)) /
            Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) +
              (K : ℝ) / Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) := by
    push_cast
    exact add_div _ _ _
  linarith

/-- Whenever `3 / ε^2 < k` and `max k 1 ≤ K` (`ε > 0`), the drift term satisfies `√(3 / K) ≤ ε`. -/
theorem sqrt_three_div_le_of_gt {ε : ℝ} (hε : 0 < ε) {k K : ℕ}
    (hk : 3 / ε ^ 2 < (k : ℝ)) (hK : max k 1 ≤ K) :
    Real.sqrt (3 / (K : ℝ)) ≤ ε := by
  have hK1 : 1 ≤ K := le_trans (le_max_right k 1) hK
  have hkK : k ≤ K := le_trans (le_max_left k 1) hK
  have hK_pos : 0 < (K : ℝ) := Nat.cast_pos.2 hK1
  have h3_lt : 3 / ε ^ 2 < (K : ℝ) := lt_of_lt_of_le hk (Nat.cast_le.2 hkK)
  have h3_le : (3 : ℝ) ≤ (K : ℝ) * ε ^ 2 :=
    le_of_lt ((div_lt_iff₀ (sq_pos_of_pos hε)).1 h3_lt)
  have hdiv_le : 3 / (K : ℝ) ≤ ε ^ 2 := (div_le_iff₀ hK_pos).2 (by linarith)
  calc
    Real.sqrt (3 / (K : ℝ)) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hdiv_le
    _ = ε := Real.sqrt_sq (le_of_lt hε)

/-- Dual `EReal` upper-bound transfer: if `L ≤ ((c + ε : ℝ) : EReal)` holds for every `ε > 0`,
then `L ≤ (c : EReal)`. -/
theorem ereal_le_coe_of_forall_pos_add_le {L : EReal} {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → L ≤ ((c + ε : ℝ) : EReal)) :
    L ≤ (c : EReal) := by
  induction L using EReal.rec with
  | bot => exact bot_le
  | coe y =>
    rw [EReal.coe_le_coe_iff]
    by_contra hlt
    have h2 := h ((y - c) / 2) (by linarith)
    rw [EReal.coe_le_coe_iff] at h2
    linarith
  | top =>
    have h1 : ((c + 1 : ℝ) : EReal) = ⊤ := top_le_iff.1 (h 1 one_pos)
    exact (EReal.coe_ne_top (c + 1) h1).elim

/-- **Complete Unconditional Proof of Wouter van Doorn's Upper Bound (`erdos_33.variants.vanDoorn`)**:
instantiating `iInf_limsup_le_of_vanDoorn_block_ratio_le` with the Fibonacci block-width sequence
`fibBlockWidth j = F_{j+2}` proves that the `erdos_33` infimum is at most `2 * φ^(5/2)`. -/
theorem erdos_33_variants_vanDoorn :
    (⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal))) ≤
        ((2 * Real.goldenRatio ^ ((5 : ℝ) / 2) : ℝ) : EReal) := by
  apply ereal_le_coe_of_forall_pos_add_le
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (3 / ε ^ 2)
  refine iInf_limsup_le_of_vanDoorn_block_ratio_le one_le_fibBlockWidth
    (K₀ := max k 1) (le_max_right k 1) (fun K hK => ?_)
  have hK1 : 1 ≤ K := le_trans (le_max_right k 1) hK
  have h1 := fibBlockWidth_block_ratio_le_add_sqrt_three_div hK1
  have h2 := sqrt_three_div_le_of_gt hε hk hK
  linarith

/-- At `R = 150`, `cillerueloStepSum 150 = 17815`, yielding the ratio `22500 / 17815 ≈ 1.2630 > 63 / 50`. -/
theorem cillerueloStepSum_one_hundred_fifty : cillerueloStepSum 150 = 17815 := by
  norm_num [cillerueloStepSum, cillerueloStepHeight, Finset.sum_range_succ]

/-- Epsilon-free subsequential lower bound `63 / 50 = 1.26 ≤ normalizedPrefixRatio A N`
for arbitrarily large `N ≥ M` (proved via `R = 150`, `S(150) = 17815`). -/
theorem exists_ge_sixty_three_fiftieths_normalizedPrefixRatio
    {A : Set ℕ} (hA : IsSquareAdditiveComplement A) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ (63 : ℝ) / 50 ≤ normalizedPrefixRatio A N := by
  let m : ℕ := max M 3
  have hm3 : 3 ≤ m := le_max_right M 3
  have hm1 : 1 ≤ m := by omega
  have hmM : M ≤ m := le_max_left M 3
  rcases exists_step_horizon_normalizedPrefixRatio_ge hA (R := 150) (by omega) hm1 with
    ⟨r, _, hr_ge⟩
  refine ⟨(cillerueloStepHeight 150 r * m) ^ 2,
    le_trans hmM (step_horizon_ge_base 150 r m), ?_⟩
  rw [cillerueloStepSum_one_hundred_fifty] at hr_ge
  have hm_real : (3 : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hm3
  have hdiv_le : (150 : ℝ) / (m : ℝ) ≤ (150 : ℝ) / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm_real
  linarith

/-- Unconditional `63 / 50 = 1.26 > 127 / 101` lower bound on the `erdos_33` infimum. -/
theorem sixty_three_fiftieths_le_iInf_limsup :
    (((63 : ℝ) / 50 : ℝ) : EReal) ≤
      ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
        ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) := by
  refine le_iInf (fun A => ?_)
  exact coe_le_limsup_ncard_div_sqrt_of_forall_exists_ge
    (exists_ge_sixty_three_fiftieths_normalizedPrefixRatio
      ((isSquareAdditiveComplement_iff_additiveBasisCondition A.1).2 A.2))
