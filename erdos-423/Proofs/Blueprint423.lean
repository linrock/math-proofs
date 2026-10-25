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

public import Erdos423Unified435
public import EventualStabilizationObstructionAndUnbounded423
public import CompletedSquareDiscriminantAndSmallThresholdObstruction423

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open Finset BigOperators Filter Asymptotics

namespace Erdos423

attribute [local instance] Classical.propDecidable

/-!
# Quantitative Excess-Growth Recurrence, Stabilization-Breaking Horizon Bounds, Iterated Tower Thresholds, and Conditional Asymptotic Reductions for Erdős Problem #423 (`Blueprint423`)

This module builds the quantitative excess-growth recurrence and its conditional asymptotic reductions. It
localizes the completed-square fiber obstruction to finite stabilization windows, bounds the first
stabilization-breaking index, defines the iterated excess horizon, and connects checkpoints along
that tower to conditional stage-interval reductions toward the lower-bound, upper-bound, and main-asymptotic statements.
-/

/-!
## Section 1: Finite-Horizon Linear-Shift Block Sums and Completed-Square Fiber Covering
-/

/-- Finite-window linear block-sum congruence: if `a n = n + C` for all `n ∈ [n₀, N]`, then
for any sub-interval `[i, j] ⊆ [n₀, N]`, `∑ l ∈ Finset.Icc i j, a l = ∑ l ∈ Finset.Icc i j, (l + C)`. -/
theorem sum_Icc_eq_of_bounded_linear :
    ∀ (a : ℕ → ℕ) (n₀ C N i j : ℕ),
      (∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) → n₀ ≤ i → j ≤ N →
      ∑ l ∈ Finset.Icc i j, a l = ∑ l ∈ Finset.Icc i j, (l + C) := by
  intro a n₀ C N i j hlin hi hj
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_Icc] at hl
  exact hlin l (by omega) (by omega)

/-- Closed-form block-sum identity on a finite linear window `[n₀, N]`: if `a n = n + C`
for all `n ∈ [n₀, N]` and `n₀ ≤ i ≤ j ≤ N`, then
`2 * ∑ l ∈ Finset.Icc i j, a l = (j - i + 1) * (2 * i + 2 * C + (j - i))`. -/
theorem two_mul_sum_Icc_of_bounded_linear :
    ∀ (a : ℕ → ℕ) (n₀ C N i j : ℕ),
      (∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) → n₀ ≤ i → i ≤ j → j ≤ N →
      2 * ∑ l ∈ Finset.Icc i j, a l = (j - i + 1) * (2 * i + 2 * C + (j - i)) := by
  intro a n₀ C N i j hlin hi hij hj
  rw [sum_Icc_eq_of_bounded_linear a n₀ C N i j hlin hi hj]
  exact two_mul_sum_Icc_add_const i j C hij

/-- Exact quadratic decomposition of `2 * prefixSum a j` on a finite linear window `[n₀, N]`
(`1 ≤ n₀ ≤ j ≤ N`). -/
theorem two_mul_prefixSum_tail_of_bounded_linear :
    ∀ (a : ℕ → ℕ) (n₀ C N j : ℕ),
      (∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) → 1 ≤ n₀ → n₀ ≤ j → j ≤ N →
      2 * prefixSum a j =
        2 * prefixSum a (n₀ - 1) + (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀)) := by
  intro a n₀ C N j hlin hn₀1 hj hjN
  have hadd := prefixSum_add_sum_Icc a (i := n₀ - 1) (j := j) (by omega)
  rw [show n₀ - 1 + 1 = n₀ by omega] at hadd
  have hmul := congrArg (2 * ·) hadd
  have hsum := two_mul_sum_Icc_of_bounded_linear a n₀ C N n₀ j hlin le_rfl hj hjN
  omega

/-- Odd-factor power-of-two exclusion on a finite linear window `[n₀, N]`: if `a n = n + C`
for all `n ∈ [n₀, N]`, then no block `[i, j]` with `1 ≤ i`, `n₀ ≤ i`, `i + 1 ≤ j`, and `j ≤ N`
can sum to `2 ^ r`. -/
theorem tail_blockSum_ne_two_pow_of_bounded_linear :
    ∀ (a : ℕ → ℕ) (n₀ C N i j r : ℕ),
      (∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) → 1 ≤ i → n₀ ≤ i → i + 1 ≤ j → j ≤ N →
      ∑ l ∈ Finset.Icc i j, a l ≠ 2 ^ r := by
  intro a n₀ C N i j r hlin hi1 hin₀ hij hjN
  rw [sum_Icc_eq_of_bounded_linear a n₀ C N i j hlin hin₀ hjN]
  exact linear_blockSum_ne_two_pow i j C r hi1 hij

/-- Finite-horizon prefix-crossing forcing: if `a n = n + C` on `[n₀, N]`, `max n₀ 3 + C ≤ 2 ^ r`,
and `2 ^ r - C ≤ N`, then `a (2 ^ r - C) = 2 ^ r` is witnessed by a consecutive block `[i, j]`
with `1 ≤ i < n₀`, `i + 1 ≤ j < 2 ^ r - C ≤ N`, and `prefixSum a j - prefixSum a (i - 1) = 2 ^ r`. -/
theorem exists_prefix_crossing_rep_of_two_pow_of_bounded_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C N r : ℕ),
      (∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) →
      max n₀ 3 + C ≤ 2 ^ r →
      2 ^ r - C ≤ N →
      ∃ i j : ℕ, 1 ≤ i ∧ i < n₀ ∧ i + 1 ≤ j ∧ j < 2 ^ r - C ∧
        prefixSum a j - prefixSum a (i - 1) = 2 ^ r ∧
        prefixSum a j - prefixSum a (n₀ - 1) ≤ 2 ^ r ∧ 2 ^ r ≤ prefixSum a j := by
  intro a ha n₀ C N r hlin hr hN
  set k := 2 ^ r - C
  have hk_n0 : n₀ ≤ k := by omega
  have hk_3 : 3 ≤ k := by omega
  have hak : a k = 2 ^ r := by
    have h := hlin k hk_n0 hN
    omega
  obtain ⟨⟨i, j, hi1, hij, hjk, hsum⟩, -, -⟩ := ha.2.2 k hk_3
  rw [hak] at hsum
  have hjN : j ≤ N := by omega
  have hin₀ : i < n₀ := by
    by_contra hge
    exact tail_blockSum_ne_two_pow_of_bounded_linear a n₀ C N i j r hlin hi1 (by omega) hij hjN hsum.symm
  have hsub := prefixSum_sub_prefixSum a (i := i - 1) (j := j) (by omega)
  rw [show i - 1 + 1 = i by omega] at hsub
  have hp : prefixSum a j - prefixSum a (i - 1) = 2 ^ r := by omega
  have hint := prefixSum_sub_mem_interval_of_lt a n₀ i j hi1 hin₀
  exact ⟨i, j, hi1, hin₀, hij, by omega, hp, by omega, by omega⟩

/-- Finite-horizon completed-square discriminant identity: if `a n = n + C` on `[n₀, N]` (`1 ≤ n₀`),
`max n₀ 3 + C ≤ 2 ^ r`, `prefixSum a (n₀ - 1) < 2 ^ r`, and `2 ^ r - C ≤ N`, then there exist
`1 ≤ i < n₀` and `n₀ ≤ j < 2 ^ r - C` satisfying
`(2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) = 2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2`. -/
theorem exists_completed_square_discriminant_of_two_pow_of_bounded_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C N r : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) →
      max n₀ 3 + C ≤ 2 ^ r →
      prefixSum a (n₀ - 1) < 2 ^ r →
      2 ^ r - C ≤ N →
      ∃ i j : ℕ, 1 ≤ i ∧ i < n₀ ∧ n₀ ≤ j ∧ j < 2 ^ r - C ∧
        (2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) =
          2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2 := by
  intro a ha n₀ C N r hn₀1 hlin hr hP hN
  obtain ⟨i, j, hi1, hin₀, hij, hjk, hp, -, hle_Pj⟩ :=
    exists_prefix_crossing_rep_of_two_pow_of_bounded_linear a ha n₀ C N r hlin hr hN
  have hjn₀ : n₀ ≤ j := by
    by_contra hlt
    have hPj_le : prefixSum a j ≤ prefixSum a (n₀ - 1) := prefixSum_mono a (by omega)
    omega
  have hjN : j ≤ N := by omega
  have hdecomp := two_mul_prefixSum_tail_of_bounded_linear a n₀ C N j hlin hn₀1 hjn₀ hjN
  have hPi_le_Pn₀ : prefixSum a (i - 1) ≤ prefixSum a (n₀ - 1) := prefixSum_mono a (by omega)
  have hPi_le_Pj : prefixSum a (i - 1) ≤ prefixSum a j := prefixSum_mono a (by omega)
  have hquad : 2 * 2 ^ r =
      2 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) +
        (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀)) := by omega
  refine ⟨i, j, hi1, hin₀, hjn₀, hjk, ?_⟩
  exact completed_square_discriminant_of_two_pow_eq a n₀ C i j r hn₀1 hjn₀ hquad

/-- Finite-horizon exponent-window covering: if `a n = n + C` on `[n₀, N]` (`1 ≤ n₀`),
`max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r_base`, and `2 ^ r - C ≤ N` for all `r ∈ [r_base, r_base + K)`,
then `Finset.Ico r_base (r_base + K)` is covered by the union of
`completedSquareExpFiber a n₀ C r_base K i` over `i ∈ Finset.Ico 1 n₀`. -/
theorem subset_biUnion_completedSquareExpFiber_of_bounded_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C N r_base K : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) →
      max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r_base →
      (∀ r ∈ Finset.Ico r_base (r_base + K), 2 ^ r - C ≤ N) →
      Finset.Ico r_base (r_base + K) ⊆
        (Finset.Ico 1 n₀).biUnion (completedSquareExpFiber a n₀ C r_base K) := by
  intro a ha n₀ C N r_base K hn₀ hlin hr_base hN r hr
  have hr_mem : r ∈ Finset.Ico r_base (r_base + K) := hr
  rw [Finset.mem_Ico] at hr
  have hthresh := threshold_le_two_pow_of_ge_add a n₀ C r (by omega)
  obtain ⟨i, j, hi1, hin₀, -, -, hcs⟩ :=
    exists_completed_square_discriminant_of_two_pow_of_bounded_linear
      a ha n₀ C N r hn₀ hlin hthresh.1 hthresh.2 (hN r hr_mem)
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_Ico.2 ⟨hi1, hin₀⟩, ?_⟩
  unfold completedSquareExpFiber
  rw [Finset.mem_filter]
  refine ⟨hr_mem, j + C, ?_⟩
  rw [show 2 * (j + C) + 1 = 2 * j + 2 * C + 1 by omega]
  exact hcs

/-- Finite-horizon pigeonhole window bound: if `a n = n + C` on `[n₀, N]` (`1 ≤ n₀`),
`max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r_base`, `2 ^ r - C ≤ N` for all `r ∈ [r_base, r_base + K)`,
and each prefix fiber `1 ≤ i < n₀` has cardinality at most `B`, then `K ≤ (n₀ - 1) * B`. -/
theorem window_length_le_mul_of_bounded_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C N r_base K B : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) →
      max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r_base →
      (∀ r ∈ Finset.Ico r_base (r_base + K), 2 ^ r - C ≤ N) →
      (∀ i ∈ Finset.Ico 1 n₀, (completedSquareExpFiber a n₀ C r_base K i).card ≤ B) →
      K ≤ (n₀ - 1) * B := by
  intro a ha n₀ C N r_base K B hn₀ hlin hr_base hN hB
  have hsub := subset_biUnion_completedSquareExpFiber_of_bounded_linear
    a ha n₀ C N r_base K hn₀ hlin hr_base hN
  have hcard1 : (Finset.Ico r_base (r_base + K)).card ≤
      ((Finset.Ico 1 n₀).biUnion (completedSquareExpFiber a n₀ C r_base K)).card :=
    Finset.card_le_card hsub
  have hcard2 : ((Finset.Ico 1 n₀).biUnion (completedSquareExpFiber a n₀ C r_base K)).card ≤
      (Finset.Ico 1 n₀).card * B :=
    Finset.card_biUnion_le_card_mul (Finset.Ico 1 n₀) (completedSquareExpFiber a n₀ C r_base K) B hB
  simp only [Nat.card_Ico] at hcard1 hcard2
  omega

/-- Finite-horizon refutation of linear stabilization from fiber multiplicity bounds: if
`1 ≤ n₀`, `max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r_base`, `2 ^ (r_base + (n₀ - 1) * B) - C ≤ N`,
and every prefix fiber `1 ≤ i < n₀` on `[r_base, r_base + (n₀ - 1) * B + 1)` has size at most `B`,
then `a` cannot satisfy `a n = n + C` across `[n₀, N]`. -/
theorem not_bounded_linear_of_completedSquareExpFiber_card_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C N r_base B : ℕ),
      1 ≤ n₀ →
      max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r_base →
      2 ^ (r_base + (n₀ - 1) * B) - C ≤ N →
      (∀ i ∈ Finset.Ico 1 n₀,
        (completedSquareExpFiber a n₀ C r_base ((n₀ - 1) * B + 1) i).card ≤ B) →
      ¬(∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) := by
  intro a ha n₀ C N r_base B hn₀ hr_base hN hB hlin
  have hN_all : ∀ r ∈ Finset.Ico r_base (r_base + ((n₀ - 1) * B + 1)), 2 ^ r - C ≤ N := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    have hpow : 2 ^ r ≤ 2 ^ (r_base + (n₀ - 1) * B) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    omega
  have hle := window_length_le_mul_of_bounded_linear
    a ha n₀ C N r_base ((n₀ - 1) * B + 1) B hn₀ hlin hr_base hN_all hB
  omega

/-!
## Section 2: Quantitative Stabilization-Breaking Horizon `n₁(n₀, C) ≤ 2 ^ r₀ + C` and Strict Excess Increase
-/

/-- Base exponent threshold `r_base(a, n₀, C) = max (max n₀ 3 + C + P(n₀ - 1)) (max (n₀ + 1) ((2n₀ + 2C - 1)²))`
at which `completedSquareExpFiber` becomes subsingleton on windows of length `n₀`. -/
def baseExpThreshold (a : ℕ → ℕ) (n₀ C : ℕ) : ℕ :=
  max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2))

/-- Quantitative exponent horizon
`r₀(a, n₀, C) = max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀`. -/
def stabilizationExpHorizon (a : ℕ → ℕ) (n₀ C : ℕ) : ℕ :=
  max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀

/-- Quantitative index horizon `n₁(a, n₀, C) = 2 ^ r₀(a, n₀, C) + C` bounding the first
stabilization-breaking index above `n₀`. -/
def stabilizationIndexHorizon (a : ℕ → ℕ) (n₀ C : ℕ) : ℕ :=
  2 ^ (stabilizationExpHorizon a n₀ C) + C

/-- Decomposition of `stabilizationExpHorizon` as `baseExpThreshold a n₀ C + n₀`. -/
theorem stabilizationExpHorizon_eq_base_add :
    ∀ (a : ℕ → ℕ) (n₀ C : ℕ),
      stabilizationExpHorizon a n₀ C = baseExpThreshold a n₀ C + n₀ := by
  intro a n₀ C
  rfl

/-- Tightened finite-horizon non-stabilization theorem: for any `1 ≤ n₀`, `C : ℕ`, and
`N ≥ 2 ^ (baseExpThreshold a n₀ C + (n₀ - 1)) - C`, no Hofstadter sequence `a` can satisfy
`a n = n + C` for all `n ∈ [n₀, N]`. -/
theorem not_bounded_linear_on_baseExpThreshold_window :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C N : ℕ),
      1 ≤ n₀ →
      2 ^ (baseExpThreshold a n₀ C + (n₀ - 1)) - C ≤ N →
      ¬(∀ n : ℕ, n₀ ≤ n → n ≤ N → a n = n + C) := by
  intro a ha n₀ C N hn₀ hN
  set r_base := baseExpThreshold a n₀ C
  have hr1 : max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r_base := le_max_left _ _
  have hr2 : n₀ + 1 ≤ r_base := le_trans (le_max_left _ _) (le_max_right _ _)
  have hr3 : (2 * n₀ + 2 * C - 1) ^ 2 ≤ r_base := le_trans (le_max_right _ _) (le_max_right _ _)
  refine not_bounded_linear_of_completedSquareExpFiber_card_le a ha n₀ C N r_base 1 hn₀ hr1 ?_ ?_
  · simpa using hN
  · intro i _
    exact completedSquareExpFiber_card_le_one a n₀ C r_base ((n₀ - 1) * 1 + 1) i (by omega) hr3

/-- The tightened exponent-window bound `2 ^ (baseExpThreshold a n₀ C + (n₀ - 1)) - C` is bounded
above by `stabilizationIndexHorizon a n₀ C = 2 ^ r₀ + C`. -/
theorem two_pow_baseExpThreshold_sub_le_stabilizationIndexHorizon :
    ∀ (a : ℕ → ℕ) (n₀ C : ℕ),
      2 ^ (baseExpThreshold a n₀ C + (n₀ - 1)) - C ≤ stabilizationIndexHorizon a n₀ C := by
  intro a n₀ C
  have hpow :
      2 ^ (baseExpThreshold a n₀ C + (n₀ - 1)) ≤ 2 ^ (stabilizationExpHorizon a n₀ C) := by
    unfold stabilizationExpHorizon baseExpThreshold
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  exact le_trans (Nat.sub_le _ _) (le_trans hpow (Nat.le_add_right _ _))

/-- For all `n₀, C : ℕ`, `3 ≤ stabilizationExpHorizon a n₀ C`. -/
theorem three_le_stabilizationExpHorizon :
    ∀ (a : ℕ → ℕ) (n₀ C : ℕ), 3 ≤ stabilizationExpHorizon a n₀ C := by
  intro a n₀ C
  unfold stabilizationExpHorizon
  have h1 : 3 ≤ max n₀ 3 + C + prefixSum a (n₀ - 1) := by omega
  have h2 : max n₀ 3 + C + prefixSum a (n₀ - 1) ≤
      max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) :=
    le_max_left _ _
  omega

/-- Strict domination `n₀ + C < stabilizationIndexHorizon a n₀ C` for all `n₀, C : ℕ`. -/
theorem lt_stabilizationIndexHorizon :
    ∀ (a : ℕ → ℕ) (n₀ C : ℕ),
      n₀ + C < stabilizationIndexHorizon a n₀ C := by
  intro a n₀ C
  unfold stabilizationIndexHorizon stabilizationExpHorizon
  set E := max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀
  have hlt : E < 2 ^ E := Nat.lt_two_pow_self
  have hge : n₀ + 1 ≤ max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hE : n₀ + 1 ≤ E := by omega
  calc n₀ + C < E + C := by omega
    _ < 2 ^ E + C := Nat.add_lt_add_right hlt C

/-- For all `n₀, C : ℕ`, `8 ≤ stabilizationIndexHorizon a n₀ C` (and in particular `3 ≤ stabilizationIndexHorizon a n₀ C`). -/
theorem eight_le_stabilizationIndexHorizon :
    ∀ (a : ℕ → ℕ) (n₀ C : ℕ), 8 ≤ stabilizationIndexHorizon a n₀ C := by
  intro a n₀ C
  unfold stabilizationIndexHorizon
  have h3 := three_le_stabilizationExpHorizon a n₀ C
  have hpow : 2 ^ 3 ≤ 2 ^ stabilizationExpHorizon a n₀ C :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h3
  have h8 : (2 : ℕ) ^ 3 = 8 := by decide
  exact le_trans (by omega : 8 ≤ 2 ^ 3) (le_trans hpow (Nat.le_add_right _ _))

/-- For all `n₀, C : ℕ`, `n₀ ≤ stabilizationIndexHorizon a n₀ C`. -/
theorem le_stabilizationIndexHorizon :
    ∀ (a : ℕ → ℕ) (n₀ C : ℕ),
      n₀ ≤ stabilizationIndexHorizon a n₀ C := by
  intro a n₀ C
  have hlt := lt_stabilizationIndexHorizon a n₀ C
  omega

/-- Monotonicity of `stabilizationExpHorizon a n₀ C` in the shift parameter `C`. -/
theorem stabilizationExpHorizon_mono_right :
    ∀ (a : ℕ → ℕ) (n₀ C₁ C₂ : ℕ), C₁ ≤ C₂ →
      stabilizationExpHorizon a n₀ C₁ ≤ stabilizationExpHorizon a n₀ C₂ := by
  intro a n₀ C₁ C₂ hC
  unfold stabilizationExpHorizon
  have hsq : (2 * n₀ + 2 * C₁ - 1) ^ 2 ≤ (2 * n₀ + 2 * C₂ - 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h1 : max n₀ 3 + C₁ + prefixSum a (n₀ - 1) ≤ max n₀ 3 + C₂ + prefixSum a (n₀ - 1) := by omega
  have h2 : max (n₀ + 1) ((2 * n₀ + 2 * C₁ - 1) ^ 2) ≤ max (n₀ + 1) ((2 * n₀ + 2 * C₂ - 1) ^ 2) :=
    max_le_max le_rfl hsq
  have h3 : max (max n₀ 3 + C₁ + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C₁ - 1) ^ 2)) ≤
      max (max n₀ 3 + C₂ + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C₂ - 1) ^ 2)) :=
    max_le_max h1 h2
  omega

/-- Monotonicity of `stabilizationIndexHorizon a n₀ C` in the shift parameter `C`. -/
theorem stabilizationIndexHorizon_mono_right :
    ∀ (a : ℕ → ℕ) (n₀ C₁ C₂ : ℕ), C₁ ≤ C₂ →
      stabilizationIndexHorizon a n₀ C₁ ≤ stabilizationIndexHorizon a n₀ C₂ := by
  intro a n₀ C₁ C₂ hC
  unfold stabilizationIndexHorizon
  have hexp := stabilizationExpHorizon_mono_right a n₀ C₁ C₂ hC
  have hpow : 2 ^ stabilizationExpHorizon a n₀ C₁ ≤ 2 ^ stabilizationExpHorizon a n₀ C₂ :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  exact Nat.add_le_add hpow hC

/-- Unconditional finite-horizon non-stabilization on `[n₀, stabilizationIndexHorizon a n₀ C]`:
for every `1 ≤ n₀` and `C : ℕ`, `a` cannot satisfy `a n = n + C` for all
`n ∈ [n₀, 2 ^ r₀ + C]`. -/
theorem not_bounded_linear_on_stabilizationIndexHorizon :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
      1 ≤ n₀ →
      ¬(∀ n : ℕ, n₀ ≤ n → n ≤ stabilizationIndexHorizon a n₀ C → a n = n + C) := by
  intro a ha n₀ C hn₀
  exact not_bounded_linear_on_baseExpThreshold_window a ha n₀ C (stabilizationIndexHorizon a n₀ C) hn₀
    (two_pow_baseExpThreshold_sub_le_stabilizationIndexHorizon a n₀ C)

/-- Existence of a stabilization-breaking index `n₁ ≤ 2 ^ r₀ + C`: for every `IsHofstadterSeq a`,
`1 ≤ n₀`, and `C : ℕ`, there exists `n₁ ∈ [n₀, 2 ^ r₀ + C]` such that `a n₁ ≠ n₁ + C`, where
`r₀ = max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀`. -/
theorem exists_stabilization_breaking_index_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
      1 ≤ n₀ →
      let r₀ := max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀
      ∃ n₁ : ℕ, n₀ ≤ n₁ ∧ n₁ ≤ 2 ^ r₀ + C ∧ a n₁ ≠ n₁ + C := by
  intro a ha n₀ C hn₀
  dsimp only
  have hnot := not_bounded_linear_on_stabilizationIndexHorizon a ha n₀ C hn₀
  unfold stabilizationIndexHorizon stabilizationExpHorizon at hnot
  by_contra hall
  apply hnot
  intro n hn₀_le hn_le
  by_contra hne
  exact hall ⟨n, hn₀_le, hn_le, hne⟩

/-- Quantitative excess-growth recurrence on `[n₀, stabilizationIndexHorizon a n₀ (a n₀ - n₀)]`:
for every `IsHofstadterSeq a` and `1 ≤ n₀`, there exists `n₁` with
`n₀ < n₁ ≤ stabilizationIndexHorizon a n₀ (a n₀ - n₀)` such that `a n₀ - n₀ < a n₁ - n₁`. -/
theorem exists_strict_excess_increase_on_stabilizationIndexHorizon :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ : ℕ),
      1 ≤ n₀ →
      ∃ n₁ : ℕ, n₀ < n₁ ∧
        n₁ ≤ stabilizationIndexHorizon a n₀ (a n₀ - n₀) ∧
        a n₀ - n₀ < a n₁ - n₁ := by
  intro a ha n₀ hn₀
  set C := a n₀ - n₀
  obtain ⟨n₁, hn₀_le, hn₁_le, hne⟩ := exists_stabilization_breaking_index_le a ha n₀ C hn₀
  have han₀_ge : n₀ ≤ a n₀ := IsHofstadterSeq_le_apply ha n₀ hn₀
  have han₁_ge : n₁ ≤ a n₁ := IsHofstadterSeq_le_apply ha n₁ (by omega)
  have hmono : a n₀ - n₀ ≤ a n₁ - n₁ := erdos_423_variants_nondecreasing a ha n₀ n₁ hn₀ hn₀_le
  have hne_n₀ : n₀ < n₁ := by
    rcases eq_or_lt_of_le hn₀_le with rfl | hlt
    · exfalso
      apply hne
      omega
    · exact hlt
  have hexcess_lt : a n₀ - n₀ < a n₁ - n₁ := by
    rcases eq_or_lt_of_le hmono with heq | hlt
    · exfalso
      apply hne
      omega
    · exact hlt
  exact ⟨n₁, hne_n₀, hn₁_le, hexcess_lt⟩

/-- Quantitative excess-growth theorem with explicit `r₀` bound for any shift parameter
`C ≥ a n₀ - n₀` (including `C = a n₀ - n₀`): on `[n₀, 2 ^ r₀ + C]` where
`r₀ = max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀`,
there exists `n₁ ∈ (n₀, 2 ^ r₀ + C]` where the excess `a n - n` strictly exceeds `a n₀ - n₀`. -/
theorem exists_strict_excess_increase_on_stabilization_window :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
      1 ≤ n₀ → a n₀ - n₀ ≤ C →
      let r₀ := max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀
      ∃ n₁ : ℕ, n₀ < n₁ ∧ n₁ ≤ 2 ^ r₀ + C ∧ a n₀ - n₀ < a n₁ - n₁ := by
  intro a ha n₀ C hn₀ hC
  dsimp only
  obtain ⟨n₁, hn₀_lt, hn₁_le, hlt⟩ :=
    exists_strict_excess_increase_on_stabilizationIndexHorizon a ha n₀ hn₀
  have hmono_hor := stabilizationIndexHorizon_mono_right a n₀ (a n₀ - n₀) C hC
  unfold stabilizationIndexHorizon stabilizationExpHorizon at hmono_hor
  exact ⟨n₁, hn₀_lt, le_trans hn₁_le hmono_hor, hlt⟩

/-- Endpoint excess increase at `2 ^ r₀ + C`: because `a n - n` is nondecreasing, for every
`1 ≤ n₀` and `C ≥ a n₀ - n₀`, the excess at the horizon endpoint `n₁(n₀, C) = 2 ^ r₀ + C`
strictly exceeds `a n₀ - n₀` (`a n₀ - n₀ + 1 ≤ a (2 ^ r₀ + C) - (2 ^ r₀ + C)`). -/
theorem strict_excess_increase_at_stabilizationIndexHorizon :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
      1 ≤ n₀ → a n₀ - n₀ ≤ C →
      a n₀ - n₀ < a (stabilizationIndexHorizon a n₀ C) - stabilizationIndexHorizon a n₀ C := by
  intro a ha n₀ C hn₀ hC
  obtain ⟨n₁, hn₀_lt, hn₁_le, hlt⟩ :=
    exists_strict_excess_increase_on_stabilization_window a ha n₀ C hn₀ hC
  have hmono := erdos_423_variants_nondecreasing a ha n₁ (stabilizationIndexHorizon a n₀ C)
    (by omega) hn₁_le
  omega

/-!
## Section 3: Iterated Excess-Growth Tower (`nextExcessHorizon` and `iterExcessHorizon`)
-/

/-- Constructive one-step excess-jump horizon `nextExcessHorizon a n₀ = n₁(a, n₀, a n₀ - n₀)`. -/
def nextExcessHorizon (a : ℕ → ℕ) (n₀ : ℕ) : ℕ :=
  stabilizationIndexHorizon a n₀ (a n₀ - n₀)

/-- Iterated excess-jump tower `iterExcessHorizon a k = (nextExcessHorizon a)^[k] 1`. -/
def iterExcessHorizon (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  (nextExcessHorizon a)^[k] 1

/-- Base value `iterExcessHorizon a 0 = 1`. -/
@[simp]
theorem iterExcessHorizon_zero (a : ℕ → ℕ) :
    iterExcessHorizon a 0 = 1 := rfl

/-- Step unfolding `iterExcessHorizon a (k + 1) = nextExcessHorizon a (iterExcessHorizon a k)`. -/
theorem iterExcessHorizon_succ (a : ℕ → ℕ) (k : ℕ) :
    iterExcessHorizon a (k + 1) = nextExcessHorizon a (iterExcessHorizon a k) :=
  Function.iterate_succ_apply' (nextExcessHorizon a) k 1

/-- Strict step growth `n₀ < nextExcessHorizon a n₀` for all `n₀ : ℕ`. -/
theorem lt_nextExcessHorizon :
    ∀ (a : ℕ → ℕ) (n₀ : ℕ), n₀ < nextExcessHorizon a n₀ := by
  intro a n₀
  unfold nextExcessHorizon
  have hlt := lt_stabilizationIndexHorizon a n₀ (a n₀ - n₀)
  omega

/-- `iterExcessHorizon a` is strictly increasing on `ℕ`. -/
theorem strictMono_iterExcessHorizon :
    ∀ (a : ℕ → ℕ), StrictMono (iterExcessHorizon a) := by
  intro a
  refine strictMono_nat_of_lt_succ fun k => ?_
  rw [iterExcessHorizon_succ]
  exact lt_nextExcessHorizon a (iterExcessHorizon a k)

/-- Every tower threshold `iterExcessHorizon a k` satisfies `1 ≤ iterExcessHorizon a k`
(and in fact `k + 1 ≤ iterExcessHorizon a k`). -/
theorem add_one_le_iterExcessHorizon :
    ∀ (a : ℕ → ℕ) (k : ℕ), k + 1 ≤ iterExcessHorizon a k := by
  intro a k
  induction k with
  | zero => simp
  | succ m ih =>
    have hlt : iterExcessHorizon a m < iterExcessHorizon a (m + 1) :=
      strictMono_iterExcessHorizon a (Nat.lt_succ_self m)
    omega

/-- Positivity `1 ≤ iterExcessHorizon a k` for all `k : ℕ`. -/
theorem one_le_iterExcessHorizon :
    ∀ (a : ℕ → ℕ) (k : ℕ), 1 ≤ iterExcessHorizon a k := by
  intro a k
  have h := add_one_le_iterExcessHorizon a k
  omega

/-- For all `k ≥ 1`, `8 ≤ iterExcessHorizon a k` (and hence `3 ≤ iterExcessHorizon a k`). -/
theorem eight_le_iterExcessHorizon_of_pos :
    ∀ (a : ℕ → ℕ) (k : ℕ), 1 ≤ k → 8 ≤ iterExcessHorizon a k := by
  intro a k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [iterExcessHorizon_succ]
  unfold nextExcessHorizon
  exact eight_le_stabilizationIndexHorizon a (iterExcessHorizon a m) _

/-- One-step excess growth at `nextExcessHorizon a n₀`: for every `IsHofstadterSeq a` and `1 ≤ n₀`,
`a n₀ - n₀ + 1 ≤ a (nextExcessHorizon a n₀) - nextExcessHorizon a n₀`. -/
theorem strict_excess_increase_at_nextExcessHorizon :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ : ℕ),
      1 ≤ n₀ →
      a n₀ - n₀ + 1 ≤ a (nextExcessHorizon a n₀) - nextExcessHorizon a n₀ := by
  intro a ha n₀ hn₀
  unfold nextExcessHorizon
  have hlt := strict_excess_increase_at_stabilizationIndexHorizon a ha n₀ (a n₀ - n₀) hn₀ le_rfl
  omega

/-- Universal tower excess guarantee: for every `IsHofstadterSeq a` and every `k : ℕ`,
`k ≤ a (iterExcessHorizon a k) - iterExcessHorizon a k`. -/
theorem le_excess_iterExcessHorizon :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (k : ℕ),
      k ≤ a (iterExcessHorizon a k) - iterExcessHorizon a k := by
  intro a ha k
  induction k with
  | zero => omega
  | succ m ih =>
    rw [iterExcessHorizon_succ]
    have hstep := strict_excess_increase_at_nextExcessHorizon a ha
      (iterExcessHorizon a m) (one_le_iterExcessHorizon a m)
    omega

/-- Quantitative tail excess guarantee: for every `IsHofstadterSeq a`, `k : ℕ`, and
`n ≥ iterExcessHorizon a k`, `k ≤ a n - n` and `k + n ≤ a n`. -/
theorem le_excess_of_iterExcessHorizon_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (k n : ℕ),
      iterExcessHorizon a k ≤ n →
      k ≤ a n - n ∧ k + n ≤ a n := by
  intro a ha k n hle
  have hk1 : 1 ≤ iterExcessHorizon a k := one_le_iterExcessHorizon a k
  have hn1 : 1 ≤ n := by omega
  have hbase := le_excess_iterExcessHorizon a ha k
  have hmono := erdos_423_variants_nondecreasing a ha (iterExcessHorizon a k) n hk1 hle
  have han : n ≤ a n := IsHofstadterSeq_le_apply ha n hn1
  exact ⟨by omega, by omega⟩

/-- Quantitative omitted-integer counting bound at tower checkpoints: for every `IsHofstadterSeq a`
and `k : ℕ`, at least `k` positive integers in `Finset.Icc 1 (a (iterExcessHorizon a k))` are
omitted by `a`. -/
theorem omitted_card_ge_at_iterExcessHorizon :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (k : ℕ),
      k ≤ ((Finset.Icc 1 (a (iterExcessHorizon a k))) \
        ((Finset.Icc 1 (iterExcessHorizon a k)).image a)).card := by
  intro a ha k
  rw [IsHofstadterSeq_card_omitted_Icc_eq_sub ha (one_le_iterExcessHorizon a k)]
  exact le_excess_iterExcessHorizon a ha k

/-- Exact evaluation of the first exponent horizon at `(n₀, C) = (1, 0)`:
`stabilizationExpHorizon a 1 0 = 4`. -/
theorem stabilizationExpHorizon_one_zero :
    ∀ (a : ℕ → ℕ), stabilizationExpHorizon a 1 0 = 4 := by
  intro a
  unfold stabilizationExpHorizon
  rw [Nat.sub_self, prefixSum_zero]
  decide

/-- Exact evaluation of the first index horizon at `(n₀, C) = (1, 0)`:
`stabilizationIndexHorizon a 1 0 = 16`. -/
theorem stabilizationIndexHorizon_one_zero :
    ∀ (a : ℕ → ℕ), stabilizationIndexHorizon a 1 0 = 16 := by
  intro a
  unfold stabilizationIndexHorizon
  rw [stabilizationExpHorizon_one_zero]
  decide

/-- Exact evaluation of the first iterated tower checkpoint `iterExcessHorizon a 1 = 16`
for every Hofstadter sequence `a`, with verified excess `a 16 - 16 ≥ 1` (indeed `a 4 - 4 = 1`). -/
theorem iterExcessHorizon_one_eq_sixteen :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → iterExcessHorizon a 1 = 16 := by
  intro a ha
  rw [iterExcessHorizon_succ, iterExcessHorizon_zero]
  unfold nextExcessHorizon
  rw [ha.1, Nat.sub_self, stabilizationIndexHorizon_one_zero]

/-- For any Hofstadter sequence `a` and `n₀ ≥ 1`, `2 * n₀ + 2 * (a n₀ - n₀) - 1 = 2 * a n₀ - 1`. -/
theorem two_mul_add_two_mul_excess_sub_one :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ : ℕ), 1 ≤ n₀ →
      2 * n₀ + 2 * (a n₀ - n₀) - 1 = 2 * a n₀ - 1 := by
  intro a ha n₀ hn₀
  have hle : n₀ ≤ a n₀ := IsHofstadterSeq_le_apply ha n₀ hn₀
  omega

/-- Prefix-sum upper bound `prefixSum a m ≤ m * a n₀` for `m ≤ n₀` (`1 ≤ n₀`). -/
theorem prefixSum_le_mul_term :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m n₀ : ℕ), 1 ≤ n₀ → m ≤ n₀ →
      prefixSum a m ≤ m * a n₀ := by
  intro a ha m n₀ hn₀ hmn₀
  induction m with
  | zero =>
    rw [prefixSum_zero, zero_mul]
  | succ k ih =>
    rw [prefixSum_succ, Nat.succ_mul]
    have hk_le : prefixSum a k ≤ k * a n₀ := ih (by omega)
    have hterm_le : a (k + 1) ≤ a n₀ := IsHofstadterSeq_mono_of_ge_one ha (by omega) hmn₀
    omega

/-- Quadratic upper bound on the exponent horizon at `C = a n₀ - n₀`:
`stabilizationExpHorizon a n₀ (a n₀ - n₀) ≤ 5 * (a n₀) ^ 2` for all `n₀ ≥ 1`. -/
theorem stabilizationExpHorizon_at_excess_le_five_mul_sq :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ : ℕ), 1 ≤ n₀ →
      stabilizationExpHorizon a n₀ (a n₀ - n₀) ≤ 5 * (a n₀) ^ 2 := by
  intro a ha n₀ hn₀
  unfold stabilizationExpHorizon
  set C := a n₀ - n₀
  have hle : n₀ ≤ a n₀ := IsHofstadterSeq_le_apply ha n₀ hn₀
  have hpos : 1 ≤ a n₀ := by omega
  have hP : prefixSum a (n₀ - 1) ≤ (n₀ - 1) * a n₀ :=
    prefixSum_le_mul_term a ha (n₀ - 1) n₀ hn₀ (by omega)
  have hPn₀ : prefixSum a (n₀ - 1) ≤ (a n₀) ^ 2 := by
    calc prefixSum a (n₀ - 1) ≤ (n₀ - 1) * a n₀ := hP
      _ ≤ a n₀ * a n₀ := Nat.mul_le_mul_right (a n₀) (by omega)
      _ = (a n₀) ^ 2 := (sq (a n₀)).symm
  have hsq : (2 * n₀ + 2 * C - 1) ^ 2 ≤ 4 * (a n₀) ^ 2 := by
    calc (2 * n₀ + 2 * C - 1) ^ 2 ≤ (2 * a n₀) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (a n₀) ^ 2 := by ring
  have hmax3 : max n₀ 3 + C ≤ a n₀ + 2 := by omega
  have h1 : max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ 4 * (a n₀) ^ 2 := by
    nlinarith
  have h2 : max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2) ≤ 4 * (a n₀) ^ 2 := by
    refine max_le ?_ hsq
    nlinarith
  have hmax :
      max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) ≤
        4 * (a n₀) ^ 2 :=
    max_le h1 h2
  nlinarith

/-- Single-step exponential upper bound `nextExcessHorizon a n₀ ≤ 2 ^ (5 * (a n₀) ^ 2) + a n₀`
in terms of `a n₀` (`1 ≤ n₀`). -/
theorem nextExcessHorizon_le_two_pow_five_mul_sq_add :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ : ℕ), 1 ≤ n₀ →
      nextExcessHorizon a n₀ ≤ 2 ^ (5 * (a n₀) ^ 2) + a n₀ := by
  intro a ha n₀ hn₀
  unfold nextExcessHorizon stabilizationIndexHorizon
  have hexp := stabilizationExpHorizon_at_excess_le_five_mul_sq a ha n₀ hn₀
  have hpow : 2 ^ stabilizationExpHorizon a n₀ (a n₀ - n₀) ≤ 2 ^ (5 * (a n₀) ^ 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  have hsub : a n₀ - n₀ ≤ a n₀ := Nat.sub_le _ _
  exact Nat.add_le_add hpow hsub

/-- Stepwise doubling bound `a (k + 1) ≤ 2 * a k` for any Hofstadter sequence `a` (`k ≥ 1`). -/
theorem IsHofstadterSeq_succ_le_two_mul :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (k : ℕ), 1 ≤ k →
      a (k + 1) ≤ 2 * a k := by
  intro a ha k hk
  rcases eq_or_lt_of_le hk with rfl | hgt
  · rw [ha.1, ha.2.1]
  · have hstep := IsHofstadterSeq_step_upper_bound ha (k := k + 1) (by omega)
    have hmono : a (k + 1 - 2) ≤ a k := IsHofstadterSeq_mono_of_ge_one ha (by omega) (by omega)
    simp only [show k + 1 - 1 = k by omega] at hstep
    omega

/-- Universal exponential upper bound `a n ≤ 2 ^ (n - 1)` for any Hofstadter sequence `a` (`n ≥ 1`). -/
theorem IsHofstadterSeq_le_two_pow_pred :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n : ℕ), 1 ≤ n →
      a n ≤ 2 ^ (n - 1) := by
  intro a ha n hn
  induction n, hn using Nat.le_induction with
  | base =>
    simp [ha.1]
  | succ k hk ih =>
    have hstep := IsHofstadterSeq_succ_le_two_mul a ha k hk
    have hpow : 2 ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ']
    omega

/-!
## Section 4: Variant Bridges and Conditional Stage-Interval Tower Reductions
-/

/-- Canonical Formal Conjectures declaration `Erdos423.erdos_423.variants.nondecreasing`
(Bolan and Tang, independently, 2026): $a_n - n$ is nondecreasing for $1 \le n \le m$.
This is a re-proof of a variant already registered by an external formalization
(Anatolii Ohorodnyk, lean-fc-proofs); the new results in this package are unboundedness and the
infinite complement. -/
theorem erdos_423.variants.nondecreasing :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m :=
  erdos_423_variants_nondecreasing

/-- Constructive proof of `erdos_423.variants.unbounded` witnessed directly by the explicit
tower threshold `iterExcessHorizon a M` (without non-constructive contradiction). -/
theorem erdos_423_variants_unbounded_of_iterExcessHorizon :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n := by
  intro a ha M
  rw [Filter.eventually_atTop]
  exact ⟨iterExcessHorizon a M, fun n hn => (le_excess_of_iterExcessHorizon_le a ha M n hn).2⟩

/-- Constructive proof of `erdos_423.variants.infinite_complement` via the explicit tower
threshold `iterExcessHorizon a`. -/
theorem erdos_423_variants_infinite_complement_of_iterExcessHorizon :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a → Set.Infinite (Set.range a)ᶜ := by
  intro a ha
  exact IsHofstadterSeq_infinite_compl_of_unbounded ha
    (erdos_423_variants_unbounded_of_iterExcessHorizon a ha)

/-- Exact real-cast excess identity `(a n : ℝ) - (n : ℝ) = ((a n - n : ℕ) : ℝ) ≥ 0` for `n ≥ 1`. -/
theorem real_sub_eq_cast_excess :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n : ℕ), 1 ≤ n →
      (a n : ℝ) - (n : ℝ) = ((a n - n : ℕ) : ℝ) ∧ 0 ≤ (a n : ℝ) - (n : ℝ) := by
  intro a ha n hn
  have hle : n ≤ a n := IsHofstadterSeq_le_apply ha n hn
  have hcast : ((a n - n : ℕ) : ℝ) = (a n : ℝ) - (n : ℝ) := Nat.cast_sub hle
  have hpos : (0 : ℝ) ≤ ((a n - n : ℕ) : ℝ) := Nat.cast_nonneg _
  exact ⟨hcast.symm, by linarith⟩

/-- Universal interval-partition lemma for any strictly increasing sequence `f : ℕ → ℕ`:
every `n ≥ f 1` lies in `[f k, f (k + 1))` for some `k ≥ 1`. -/
theorem exists_mem_Ico_of_strictMono :
    ∀ (f : ℕ → ℕ), StrictMono f → ∀ (n : ℕ), f 1 ≤ n →
      ∃ k : ℕ, 1 ≤ k ∧ f k ≤ n ∧ n < f (k + 1) := by
  intro f hf n hn
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨1, le_rfl, le_rfl, hf (Nat.lt_succ_self 1)⟩
  | succ m _ ih =>
    rcases ih with ⟨k, hk1, hkm, hlt⟩
    have hle_succ : m + 1 ≤ f (k + 1) := by omega
    rcases eq_or_lt_of_le hle_succ with heq | hlt'
    · refine ⟨k + 1, by omega, by omega, ?_⟩
      rw [heq]
      exact hf (Nat.lt_succ_self (k + 1))
    · exact ⟨k, hk1, by omega, hlt'⟩

/-- Stage-interval localization for `iterExcessHorizon a`: every `n ≥ iterExcessHorizon a 1`
belongs to `[iterExcessHorizon a k, iterExcessHorizon a (k + 1))` for some `k ≥ 1` with
`k ≤ a n - n`. -/
theorem exists_iterExcessHorizon_interval_of_ge :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n : ℕ), iterExcessHorizon a 1 ≤ n →
      ∃ k : ℕ, 1 ≤ k ∧ iterExcessHorizon a k ≤ n ∧ n < iterExcessHorizon a (k + 1) ∧
        k ≤ a n - n := by
  intro a ha n hn
  obtain ⟨k, hk1, hlo, hhi⟩ :=
    exists_mem_Ico_of_strictMono (iterExcessHorizon a) (strictMono_iterExcessHorizon a) n hn
  exact ⟨k, hk1, hlo, hhi, (le_excess_of_iterExcessHorizon_le a ha k n hlo).1⟩

/-- Nonnegativity `0 ≤ Real.log (Real.log (n : ℝ))` for all `n ≥ 3`. -/
theorem log_log_nonneg_of_three_le :
    ∀ (n : ℕ), 3 ≤ n → 0 ≤ Real.log (Real.log (n : ℝ)) := by
  intro n hn
  apply Real.log_nonneg
  have hexp : Real.exp 1 ≤ (n : ℝ) := by
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hexp_lt : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    linarith
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) hexp

/-- Monotonicity of `n ↦ Real.log (Real.log (n : ℝ))` for `3 ≤ m ≤ n`. -/
theorem log_log_mono_of_three_le :
    ∀ (m n : ℕ), 3 ≤ m → m ≤ n →
      Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log (n : ℝ)) := by
  intro m n hm hmn
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmn_r : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hexp_lt : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog_m : 1 ≤ Real.log (m : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlog_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by linarith) hmn_r
  exact Real.log_le_log (by linarith) hlog_le

/-- Pointwise-to-asymptotic bridge for `erdos_423.variants.lower_bound`: if for `n ≥ N₀` (`N₀ ≥ 3`)
`Real.log (Real.log (n : ℝ)) ≤ B * ((a n - n : ℕ) : ℝ)` (`0 ≤ B`), then
`(fun n : ℕ => Real.log (Real.log n)) =O[atTop] (fun n : ℕ => (a n : ℝ) - n)`. -/
theorem isBigO_log_log_of_eventually_le_mul_excess :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (B : ℝ) (N₀ : ℕ),
      0 ≤ B → 3 ≤ N₀ →
      (∀ n : ℕ, N₀ ≤ n → Real.log (Real.log (n : ℝ)) ≤ B * ((a n - n : ℕ) : ℝ)) →
      (fun n : ℕ => Real.log (Real.log n)) =O[atTop] (fun n : ℕ => (a n : ℝ) - n) := by
  intro a ha B N₀ hB hN₀ hbound
  refine Asymptotics.IsBigO.of_bound B ?_
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn => ?_⟩
  have hlog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := log_log_nonneg_of_three_le n (by omega)
  obtain ⟨hsub_eq, hsub_nonneg⟩ := real_sub_eq_cast_excess a ha n (by omega)
  rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hsub_nonneg, hsub_eq]
  exact hbound n hn

/-- Quantitative tower reduction for `erdos_423.variants.lower_bound`: if the double-logarithm
of our constructive iterated excess horizon `iterExcessHorizon a (k + 1)` grows at most linearly
in the stage index `k` (`Real.log (Real.log (iterExcessHorizon a (k + 1) : ℝ)) ≤ B * (k : ℝ)`
for all `k ≥ 1`), then `(fun n : ℕ => Real.log (Real.log n)) =O[atTop] (fun n : ℕ => (a n : ℝ) - n)`. -/
theorem erdos_423_variants_lower_bound_of_iterExcessHorizon_log_log_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (B : ℝ),
      0 ≤ B →
      (∀ k : ℕ, 1 ≤ k →
        Real.log (Real.log (iterExcessHorizon a (k + 1) : ℝ)) ≤ B * (k : ℝ)) →
      (fun n : ℕ => Real.log (Real.log n)) =O[atTop] (fun n : ℕ => (a n : ℝ) - n) := by
  intro a ha B hB htower
  have h8 : 8 ≤ iterExcessHorizon a 1 := eight_le_iterExcessHorizon_of_pos a 1 le_rfl
  refine isBigO_log_log_of_eventually_le_mul_excess a ha B (iterExcessHorizon a 1) hB (by omega) ?_
  intro n hn
  obtain ⟨k, hk1, hlo, hhi, hexcess⟩ := exists_iterExcessHorizon_interval_of_ge a ha n hn
  have hn3 : 3 ≤ n := by omega
  have hmono := log_log_mono_of_three_le n (iterExcessHorizon a (k + 1)) hn3 (le_of_lt hhi)
  have hk_le : (k : ℝ) ≤ ((a n - n : ℕ) : ℝ) := by exact_mod_cast hexcess
  have hmul : B * (k : ℝ) ≤ B * ((a n - n : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hk_le hB
  linarith [htower k hk1]

/-- Pointwise-to-asymptotic bridge for `erdos_423.variants.upper_bound`: if for `n ≥ N₀` (`N₀ ≥ 1`)
the excess satisfies `((a n - n : ℕ) : ℝ) ≤ B * (n : ℝ) ^ ((688 : ℝ) / 413 + ε)`, then
`(fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((688 : ℝ) / 413 + ε))`. -/
theorem isBigO_rpow_of_eventually_excess_le_rpow :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (ε B : ℝ) (N₀ : ℕ),
      0 < ε → 0 ≤ B → 1 ≤ N₀ →
      (∀ n : ℕ, N₀ ≤ n → ((a n - n : ℕ) : ℝ) ≤ B * (n : ℝ) ^ ((688 : ℝ) / 413 + ε)) →
      (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((688 : ℝ) / 413 + ε)) := by
  intro a ha ε B N₀ hε hB hN₀ hbound
  refine Asymptotics.IsBigO.of_bound (1 + B) ?_
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hle_an : n ≤ a n := IsHofstadterSeq_le_apply ha n hn1
  have han_eq : (a n : ℝ) = (n : ℝ) + ((a n - n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle_an]
    ring
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hexp_ge_one : (1 : ℝ) ≤ (688 : ℝ) / 413 + ε := by linarith
  have hn_le_rpow : (n : ℝ) ≤ (n : ℝ) ^ ((688 : ℝ) / 413 + ε) := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one (n : ℝ)).symm
      _ ≤ (n : ℝ) ^ ((688 : ℝ) / 413 + ε) := Real.rpow_le_rpow_of_exponent_le hn_ge_one hexp_ge_one
  have han_nonneg : (0 : ℝ) ≤ (a n : ℝ) := Nat.cast_nonneg _
  have hrpow_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ ((688 : ℝ) / 413 + ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hB_le := hbound n hn
  rw [Real.norm_of_nonneg han_nonneg, Real.norm_of_nonneg hrpow_nonneg, han_eq]
  linarith

/-- Quantitative tower reduction for `erdos_423.variants.upper_bound`: if on each tower interval
`[iterExcessHorizon a k, iterExcessHorizon a (k + 1))` (`k ≥ 1`) the excess at the right endpoint
satisfies `((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) ≤
B * (iterExcessHorizon a k : ℝ) ^ ((688 : ℝ) / 413 + ε)`, then by nondecreasingness of `a n - n`
(`erdos_423.variants.nondecreasing`), `(fun n : ℕ => (a n : ℝ)) =O[atTop]
(fun n : ℕ => (n : ℝ) ^ ((688 : ℝ) / 413 + ε))`. -/
theorem erdos_423_variants_upper_bound_of_iterExcessHorizon_rpow_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (ε B : ℝ),
      0 < ε → 0 ≤ B →
      (∀ k : ℕ, 1 ≤ k →
        ((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) ≤
          B * (iterExcessHorizon a k : ℝ) ^ ((688 : ℝ) / 413 + ε)) →
      (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((688 : ℝ) / 413 + ε)) := by
  intro a ha ε B hε hB htower
  have h8 : 8 ≤ iterExcessHorizon a 1 := eight_le_iterExcessHorizon_of_pos a 1 le_rfl
  refine isBigO_rpow_of_eventually_excess_le_rpow a ha ε B (iterExcessHorizon a 1) hε hB (by omega) ?_
  intro n hn
  obtain ⟨k, hk1, hlo, hhi, -⟩ := exists_iterExcessHorizon_interval_of_ge a ha n hn
  have hexcess_le_nat :
      a n - n ≤ a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) :=
    erdos_423.variants.nondecreasing a ha n (iterExcessHorizon a (k + 1)) (by omega) (le_of_lt hhi)
  have hexcess_le :
      ((a n - n : ℕ) : ℝ) ≤
        ((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hexcess_le_nat
  have hlo_r : (iterExcessHorizon a k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
  have hrpow_mono :
      (iterExcessHorizon a k : ℝ) ^ ((688 : ℝ) / 413 + ε) ≤
        (n : ℝ) ^ ((688 : ℝ) / 413 + ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hlo_r (by linarith)
  have hmul :
      B * (iterExcessHorizon a k : ℝ) ^ ((688 : ℝ) / 413 + ε) ≤
        B * (n : ℝ) ^ ((688 : ℝ) / 413 + ε) :=
    mul_le_mul_of_nonneg_left hrpow_mono hB
  linarith [htower k hk1]

/-- Pointwise-to-asymptotic bridge for the open main conjecture `erdos_423`: if for every `ε > 0`
there exists `N₀ ≥ 1` such that `((a n - n : ℕ) : ℝ) ≤ ε * (n : ℝ)` for all `n ≥ N₀`, then
`(fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ))`. -/
theorem isLittleO_excess_of_forall_pos_exists_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → ((a n - n : ℕ) : ℝ) ≤ ε * (n : ℝ)) →
      (fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  intro a ha hex
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  obtain ⟨N₀, hN₀1, hN₀⟩ := hex ε hε
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hsub_eq, hsub_nonneg⟩ := real_sub_eq_cast_excess a ha n (by omega)
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [Real.norm_of_nonneg hsub_nonneg, Real.norm_of_nonneg hn_nonneg, hsub_eq]
  exact hN₀ n hn

/-- Quantitative tower reduction for the open main conjecture `erdos_423`: if for every `ε > 0`
there exists a tower stage `K₀ ≥ 1` such that for all `k ≥ K₀`, the excess at the next tower
checkpoint satisfies
`((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) ≤ ε * (iterExcessHorizon a k : ℝ)`,
then `(fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ))`. -/
theorem erdos_423_of_iterExcessHorizon_littleO_bound :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k →
        ((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) ≤
          ε * (iterExcessHorizon a k : ℝ)) →
      (fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  intro a ha htower
  refine isLittleO_excess_of_forall_pos_exists_le a ha fun ε hε => ?_
  obtain ⟨K₀, hK₀1, hK₀⟩ := htower ε hε
  have hK₀_pos : 1 ≤ iterExcessHorizon a K₀ := one_le_iterExcessHorizon a K₀
  refine ⟨iterExcessHorizon a K₀, hK₀_pos, fun n hn => ?_⟩
  have h1_le_K₀ : iterExcessHorizon a 1 ≤ iterExcessHorizon a K₀ :=
    (strictMono_iterExcessHorizon a).monotone hK₀1
  obtain ⟨k, hk1, hlo, hhi, -⟩ :=
    exists_iterExcessHorizon_interval_of_ge a ha n (le_trans h1_le_K₀ hn)
  have hk_ge_K₀ : K₀ ≤ k := by
    by_contra hlt
    have hle_k : k + 1 ≤ K₀ := by omega
    have hmon : iterExcessHorizon a (k + 1) ≤ iterExcessHorizon a K₀ :=
      (strictMono_iterExcessHorizon a).monotone hle_k
    omega
  have hexcess_le_nat :
      a n - n ≤ a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) :=
    erdos_423.variants.nondecreasing a ha n (iterExcessHorizon a (k + 1)) (by omega) (le_of_lt hhi)
  have hexcess_le :
      ((a n - n : ℕ) : ℝ) ≤
        ((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hexcess_le_nat
  have hlo_r : (iterExcessHorizon a k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
  have hmul : ε * (iterExcessHorizon a k : ℝ) ≤ ε * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hlo_r (le_of_lt hε)
  linarith [hK₀ k hk_ge_K₀]

/-- Implication from the open main conjecture `erdos_423` (`a n - n = o(n)`) to
`erdos_423.variants.upper_bound` (`a n = O(n ^ (688 / 413 + ε))` for every `ε > 0`). -/
theorem erdos_423_implies_variants_upper_bound :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      ((fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ))) →
      ∀ ε > (0 : ℝ), (fun n : ℕ => (a n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ ((688 : ℝ) / 413 + ε)) := by
  intro a ha ho ε hε
  have h1 : ∀ᶠ n : ℕ in atTop, ‖(a n : ℝ) - (n : ℝ)‖ ≤ 1 * ‖(n : ℝ)‖ :=
    ho.bound zero_lt_one
  rw [Filter.eventually_atTop] at h1
  rcases h1 with ⟨N₀, hN₀⟩
  refine isBigO_rpow_of_eventually_excess_le_rpow a ha ε 1 (max N₀ 1) hε zero_le_one (le_max_right _ _) ?_
  intro n hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hsub_eq, hsub_nonneg⟩ := real_sub_eq_cast_excess a ha n hn1
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hbound := hN₀ n hnN₀
  rw [Real.norm_of_nonneg hsub_nonneg, Real.norm_of_nonneg hn_nonneg, hsub_eq] at hbound
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hexp_ge_one : (1 : ℝ) ≤ (688 : ℝ) / 413 + ε := by linarith
  have hn_le_rpow : (n : ℝ) ≤ (n : ℝ) ^ ((688 : ℝ) / 413 + ε) := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one (n : ℝ)).symm
      _ ≤ (n : ℝ) ^ ((688 : ℝ) / 413 + ε) := Real.rpow_le_rpow_of_exponent_le hn_ge_one hexp_ge_one
  linarith

end Erdos423

end
