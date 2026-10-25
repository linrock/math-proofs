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
# Completed-Square Discriminant Identity, Small-Threshold Non-Stabilization (`n₀ ≤ 6`), and Pigeonhole Ramanujan-Nagell Reduction for Erdős Problem #423

This module develops the completed-square discriminant method. It proves a modulo-8 non-degeneracy
identity, gives explicit non-stabilization witnesses for small thresholds, and turns 2-adic collision
factorization into subsingleton prefix-fiber bounds. Those bounds refute eventual linear stabilization
and bridge to unbounded excess and an infinite omitted complement.
-/

/-- Universal algebraic completed-square identity for the tail quadratic factor:
for all `1 ≤ n₀ ≤ j` and `C : ℕ`,
`4 * ((j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀))) + (2 * n₀ + 2 * C - 1) ^ 2 = (2 * j + 2 * C + 1) ^ 2`. -/
theorem completed_square_tail_quadratic_identity :
    ∀ (n₀ C j : ℕ), 1 ≤ n₀ → n₀ ≤ j →
      4 * ((j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀))) + (2 * n₀ + 2 * C - 1) ^ 2 =
        (2 * j + 2 * C + 1) ^ 2 := by
  intro n₀ C j hn₀ hj
  set d := j - n₀
  set u := 2 * n₀ + 2 * C - 1
  have h1 : 2 * n₀ + 2 * C = u + 1 := by omega
  have h2 : 2 * j + 2 * C + 1 = u + 2 * d + 2 := by omega
  rw [h1, h2]
  ring

/-- Completed-square form of the eventual-linear prefix-sum decomposition: if `a n = n + C`
for all `n ≥ n₀` (`1 ≤ n₀ ≤ j`), then
`8 * prefixSum a j + (2 * n₀ + 2 * C - 1) ^ 2 = 8 * prefixSum a (n₀ - 1) + (2 * j + 2 * C + 1) ^ 2`. -/
theorem eight_mul_prefixSum_tail_completed_square :
    ∀ (a : ℕ → ℕ) (n₀ C j : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) → 1 ≤ n₀ → n₀ ≤ j →
      8 * prefixSum a j + (2 * n₀ + 2 * C - 1) ^ 2 =
        8 * prefixSum a (n₀ - 1) + (2 * j + 2 * C + 1) ^ 2 := by
  intro a n₀ C j hlin hn₀ hj
  have hdecomp := two_mul_prefixSum_tail_decomposition a n₀ C j hlin hn₀ hj
  have hcs := completed_square_tail_quadratic_identity n₀ C j hn₀ hj
  omega

/-- General completed-square discriminant identity for any prefix-crossing block sum `m`:
if `1 ≤ n₀ ≤ j` and
`2 * m = 2 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) + (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀))`,
then
`(2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) = 8 * m + (2 * n₀ + 2 * C - 1) ^ 2`. -/
theorem completed_square_discriminant_of_prefix_crossing_eq :
    ∀ (a : ℕ → ℕ) (n₀ C i j m : ℕ),
      1 ≤ n₀ → n₀ ≤ j →
      2 * m =
        2 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) +
          (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀)) →
      (2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) =
        8 * m + (2 * n₀ + 2 * C - 1) ^ 2 := by
  intro a n₀ C i j m hn₀ hj heq
  have hcs := completed_square_tail_quadratic_identity n₀ C j hn₀ hj
  omega

/-- Completed-square discriminant identity for Tang's power-of-two prefix-crossing equation:
if `1 ≤ n₀ ≤ j` and
`2 * 2 ^ r = 2 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) + (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀))`,
then
`(2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) = 2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2`. -/
theorem completed_square_discriminant_of_two_pow_eq :
    ∀ (a : ℕ → ℕ) (n₀ C i j r : ℕ),
      1 ≤ n₀ → n₀ ≤ j →
      2 * 2 ^ r =
        2 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) +
          (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀)) →
      (2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) =
        2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2 := by
  intro a n₀ C i j r hn₀ hj heq
  have h1 := completed_square_discriminant_of_prefix_crossing_eq a n₀ C i j (2 ^ r) hn₀ hj heq
  have hpow : 8 * 2 ^ r = 2 ^ (r + 3) := by ring
  omega

/-- Completed-square lifting of `exists_prefix_crossing_quadratic_eq_of_two_pow`:
under eventual linear stabilization `a n = n + C` (`n ≥ n₀ ≥ 1`), every power of two `2 ^ r`
exceeding `max n₀ 3 + C` and `prefixSum a (n₀ - 1)` satisfies
`(2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) = 2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2`
for some `1 ≤ i < n₀` and `j ≥ n₀`. -/
theorem exists_completed_square_discriminant_of_two_pow :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      max n₀ 3 + C ≤ 2 ^ r →
      prefixSum a (n₀ - 1) < 2 ^ r →
      ∃ i j : ℕ, 1 ≤ i ∧ i < n₀ ∧ n₀ ≤ j ∧
        (2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) =
          2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2 := by
  intro a ha n₀ C r hn₀ hlin hr hP
  obtain ⟨i, j, hi1, hin₀, hjn₀, heq⟩ :=
    exists_prefix_crossing_quadratic_eq_of_two_pow a ha n₀ C r hn₀ hlin hr hP
  refine ⟨i, j, hi1, hin₀, hjn₀, ?_⟩
  exact completed_square_discriminant_of_two_pow_eq a n₀ C i j r hn₀ hjn₀ heq

/-- Every odd square `(2 * k + 1) ^ 2` is congruent to `1` modulo `8`. -/
theorem odd_sq_mod_eight_eq_one :
    ∀ (k : ℕ), (2 * k + 1) ^ 2 % 8 = 1 := by
  intro k
  have hk : k = 2 * (k / 2) + k % 2 := by omega
  have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · have hsq : (2 * k + 1) ^ 2 = 8 * (2 * (k / 2) ^ 2 + (k / 2)) + 1 := by
      calc (2 * k + 1) ^ 2 = (2 * (2 * (k / 2) + 0) + 1) ^ 2 := by rw [← h0, ← hk]
        _ = 8 * (2 * (k / 2) ^ 2 + (k / 2)) + 1 := by ring
    omega
  · have hsq : (2 * k + 1) ^ 2 = 8 * (2 * (k / 2) ^ 2 + 3 * (k / 2) + 1) + 1 := by
      calc (2 * k + 1) ^ 2 = (2 * (2 * (k / 2) + 1) + 1) ^ 2 := by rw [← h1, ← hk]
        _ = 8 * (2 * (k / 2) ^ 2 + 3 * (k / 2) + 1) + 1 := by ring
    omega

/-- No multiple of `8` can equal an odd square `(2 * k + 1) ^ 2`. -/
theorem eight_mul_ne_odd_sq :
    ∀ (x k : ℕ), 8 * x ≠ (2 * k + 1) ^ 2 := by
  intro x k heq
  have hmod := congrArg (· % 8) heq
  have hodd := odd_sq_mod_eight_eq_one k
  omega

/-- Modulo-8 non-degeneracy of the completed-square equation: for all `n₀ ≥ 1`, `C`, and `i`,
`8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) ≠ (2 * n₀ + 2 * C - 1) ^ 2`. -/
theorem eight_mul_prefixSum_sub_ne_tail_odd_sq :
    ∀ (a : ℕ → ℕ) (n₀ C i : ℕ), 1 ≤ n₀ →
      8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) ≠ (2 * n₀ + 2 * C - 1) ^ 2 := by
  intro a n₀ C i hn₀
  have hodd : 2 * n₀ + 2 * C - 1 = 2 * (n₀ + C - 1) + 1 := by omega
  rw [hodd]
  exact eight_mul_ne_odd_sq (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) (n₀ + C - 1)

/-- Signed integer discriminant offset `D = 8 * (P(n₀ - 1) - P(i - 1)) - (2 * n₀ + 2 * C - 1) ^ 2`
appearing in the generalized Ramanujan-Nagell equation `(2 * v + 1) ^ 2 + D = 2 ^ (r + 3)`. -/
def discriminantOffset (a : ℕ → ℕ) (n₀ C i : ℕ) : ℤ :=
  8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1) : ℤ) - (((2 * n₀ + 2 * C - 1) ^ 2 : ℕ) : ℤ)

/-- For every `n₀ ≥ 1`, `C`, and `i`, the signed discriminant offset satisfies
`discriminantOffset a n₀ C i % 8 = 7` (in Euclidean `ℤ` modulo arithmetic). -/
theorem discriminantOffset_emod_eight :
    ∀ (a : ℕ → ℕ) (n₀ C i : ℕ), 1 ≤ n₀ →
      discriminantOffset a n₀ C i % 8 = 7 := by
  intro a n₀ C i hn₀
  unfold discriminantOffset
  have hodd : 2 * n₀ + 2 * C - 1 = 2 * (n₀ + C - 1) + 1 := by omega
  have hmod := odd_sq_mod_eight_eq_one (n₀ + C - 1)
  rw [← hodd] at hmod
  omega

/-- The signed discriminant offset `discriminantOffset a n₀ C i` is never zero for `n₀ ≥ 1`. -/
theorem discriminantOffset_ne_zero :
    ∀ (a : ℕ → ℕ) (n₀ C i : ℕ), 1 ≤ n₀ →
      discriminantOffset a n₀ C i ≠ 0 := by
  intro a n₀ C i hn₀ h0
  have hmod := discriminantOffset_emod_eight a n₀ C i hn₀
  omega

/-- Signed Ramanujan-Nagell form of `exists_completed_square_discriminant_of_two_pow`:
under eventual stabilization `a n = n + C` (`n ≥ n₀ ≥ 1`), every power of two `2 ^ r`
exceeding `max n₀ 3 + C` and `prefixSum a (n₀ - 1)` produces `1 ≤ i < n₀` and `v = j + C ≥ n₀ + C`
satisfying `((2 * v + 1 : ℤ) ^ 2) + discriminantOffset a n₀ C i = (2 : ℤ) ^ (r + 3)`. -/
theorem exists_int_completed_square_of_two_pow :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      max n₀ 3 + C ≤ 2 ^ r →
      prefixSum a (n₀ - 1) < 2 ^ r →
      ∃ i v : ℕ, 1 ≤ i ∧ i < n₀ ∧ n₀ + C ≤ v ∧
        ((2 * v + 1 : ℤ) ^ 2) + discriminantOffset a n₀ C i = (2 : ℤ) ^ (r + 3) := by
  intro a ha n₀ C r hn₀ hlin hr hP
  obtain ⟨i, j, hi1, hin₀, hjn₀, hcs⟩ :=
    exists_completed_square_discriminant_of_two_pow a ha n₀ C r hn₀ hlin hr hP
  refine ⟨i, j + C, hi1, hin₀, by omega, ?_⟩
  unfold discriminantOffset
  have hle : prefixSum a (i - 1) ≤ prefixSum a (n₀ - 1) := prefixSum_mono a (by omega)
  have hcs_z : (((2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) : ℕ) : ℤ) =
      ((2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2 : ℕ) : ℤ) := congrArg Nat.cast hcs
  push_cast [hle] at hcs_z ⊢
  linarith

/-!
## Section 2: Unconditional Non-Stabilization for Small Thresholds (`n₀ ≤ 4` and `n₀ ≤ 6`) via Explicit Inter-Prefix Gap Witnesses
-/

/-- For any Hofstadter sequence `a`, `prefixSum a 1 = 1`. -/
theorem IsHofstadterSeq_prefixSum_one :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → prefixSum a 1 = 1 := by
  intro a ha
  rw [prefixSum_succ, prefixSum_zero, zero_add, ha.1]

/-- For any Hofstadter sequence `a`, `prefixSum a 2 = 3`. -/
theorem IsHofstadterSeq_prefixSum_two :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → prefixSum a 2 = 3 := by
  intro a ha
  rw [prefixSum_succ, IsHofstadterSeq_prefixSum_one a ha, ha.2.1]

/-- For any Hofstadter sequence `a`, `prefixSum a 3 = 6`. -/
theorem IsHofstadterSeq_prefixSum_three :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → prefixSum a 3 = 6 := by
  intro a ha
  rw [prefixSum_succ, IsHofstadterSeq_prefixSum_two a ha, erdos_423_test_a3 a ha]

/-- For any Hofstadter sequence `a`, `prefixSum a 4 = 11`. -/
theorem IsHofstadterSeq_prefixSum_four :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → prefixSum a 4 = 11 := by
  intro a ha
  rw [prefixSum_succ, IsHofstadterSeq_prefixSum_three a ha, erdos_423_test_a4 a ha]

/-- For any Hofstadter sequence `a`, `prefixSum a 5 = 17`. -/
theorem IsHofstadterSeq_prefixSum_five :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → prefixSum a 5 = 17 := by
  intro a ha
  rw [prefixSum_succ, IsHofstadterSeq_prefixSum_four a ha, erdos_423_test_a_five a ha]

/-- Unconditional exclusion of linear stabilization from `n₀ = 2` via the explicit inter-prefix
gap witness `(j, r) = (2, 2)` (`prefixSum a 2 = 3 < 2 ^ 2 = 4 < 5 = prefixSum a 3 - prefixSum a 1`). -/
theorem not_eventual_linear_from_two :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (C : ℕ),
      ¬(∀ n : ℕ, 2 ≤ n → a n = n + C) := by
  intro a ha C hlin
  have ha2 : a 2 = 2 := ha.2.1
  have h2 : a 2 = 2 + C := hlin 2 le_rfl
  have hC : C = 0 := by omega
  have hP1 : prefixSum a 1 = 1 := IsHofstadterSeq_prefixSum_one a ha
  have hP2 := two_mul_prefixSum_tail_decomposition a 2 C 2 hlin (by omega) (by omega)
  have hP3 := two_mul_prefixSum_tail_decomposition a 2 C 3 hlin (by omega) (by omega)
  change 2 * prefixSum a 2 = 2 * prefixSum a 1 + (2 - 2 + 1) * (2 * 2 + 2 * C + (2 - 2)) at hP2
  change 2 * prefixSum a 3 = 2 * prefixSum a 1 + (3 - 2 + 1) * (2 * 2 + 2 * C + (3 - 2)) at hP3
  exact not_eventual_linear_of_inter_prefix_gap_two_pow a ha 2 C 2 2
    (by omega) (by omega) (by change 2 ^ 2 < prefixSum a 3 - prefixSum a 1; omega) hlin

/-- Unconditional exclusion of linear stabilization from `n₀ = 3` via the explicit inter-prefix
gap witness `(j, r) = (5, 4)` (`prefixSum a 5 = 15 < 2 ^ 4 = 16 < 18 = prefixSum a 6 - prefixSum a 2`). -/
theorem not_eventual_linear_from_three :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (C : ℕ),
      ¬(∀ n : ℕ, 3 ≤ n → a n = n + C) := by
  intro a ha C hlin
  have ha3 : a 3 = 3 := erdos_423_test_a3 a ha
  have h3 : a 3 = 3 + C := hlin 3 le_rfl
  have hC : C = 0 := by omega
  have hP2 : prefixSum a 2 = 3 := IsHofstadterSeq_prefixSum_two a ha
  have hP5 := two_mul_prefixSum_tail_decomposition a 3 C 5 hlin (by omega) (by omega)
  have hP6 := two_mul_prefixSum_tail_decomposition a 3 C 6 hlin (by omega) (by omega)
  change 2 * prefixSum a 5 = 2 * prefixSum a 2 + (5 - 3 + 1) * (2 * 3 + 2 * C + (5 - 3)) at hP5
  change 2 * prefixSum a 6 = 2 * prefixSum a 2 + (6 - 3 + 1) * (2 * 3 + 2 * C + (6 - 3)) at hP6
  exact not_eventual_linear_of_inter_prefix_gap_two_pow a ha 3 C 5 4
    (by omega) (by omega) (by change 2 ^ 4 < prefixSum a 6 - prefixSum a 2; omega) hlin

/-- Unconditional exclusion of linear stabilization from `n₀ = 4` via the explicit inter-prefix
gap witness `(j, r) = (10, 6)` (`prefixSum a 10 = 62 < 2 ^ 6 = 64 < 68 = prefixSum a 11 - prefixSum a 3`). -/
theorem not_eventual_linear_from_four :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (C : ℕ),
      ¬(∀ n : ℕ, 4 ≤ n → a n = n + C) := by
  intro a ha C hlin
  have ha4 : a 4 = 5 := erdos_423_test_a4 a ha
  have h4 : a 4 = 4 + C := hlin 4 le_rfl
  have hC : C = 1 := by omega
  have hP3 : prefixSum a 3 = 6 := IsHofstadterSeq_prefixSum_three a ha
  have hP10 := two_mul_prefixSum_tail_decomposition a 4 C 10 hlin (by omega) (by omega)
  have hP11 := two_mul_prefixSum_tail_decomposition a 4 C 11 hlin (by omega) (by omega)
  change 2 * prefixSum a 10 = 2 * prefixSum a 3 + (10 - 4 + 1) * (2 * 4 + 2 * C + (10 - 4)) at hP10
  change 2 * prefixSum a 11 = 2 * prefixSum a 3 + (11 - 4 + 1) * (2 * 4 + 2 * C + (11 - 4)) at hP11
  exact not_eventual_linear_of_inter_prefix_gap_two_pow a ha 4 C 10 6
    (by omega) (by omega) (by change 2 ^ 6 < prefixSum a 11 - prefixSum a 3; omega) hlin

/-- Unconditional exclusion of linear stabilization from `n₀ = 5` via the explicit inter-prefix
gap witness `(j, r) = (21, 8)` (`prefixSum a 21 = 249 < 2 ^ 8 = 256 < 261 = prefixSum a 22 - prefixSum a 4`). -/
theorem not_eventual_linear_from_five :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (C : ℕ),
      ¬(∀ n : ℕ, 5 ≤ n → a n = n + C) := by
  intro a ha C hlin
  have ha5 : a 5 = 6 := erdos_423_test_a_five a ha
  have h5 : a 5 = 5 + C := hlin 5 le_rfl
  have hC : C = 1 := by omega
  have hP4 : prefixSum a 4 = 11 := IsHofstadterSeq_prefixSum_four a ha
  have hP21 := two_mul_prefixSum_tail_decomposition a 5 C 21 hlin (by omega) (by omega)
  have hP22 := two_mul_prefixSum_tail_decomposition a 5 C 22 hlin (by omega) (by omega)
  change 2 * prefixSum a 21 = 2 * prefixSum a 4 + (21 - 5 + 1) * (2 * 5 + 2 * C + (21 - 5)) at hP21
  change 2 * prefixSum a 22 = 2 * prefixSum a 4 + (22 - 5 + 1) * (2 * 5 + 2 * C + (22 - 5)) at hP22
  exact not_eventual_linear_of_inter_prefix_gap_two_pow a ha 5 C 21 8
    (by omega) (by omega) (by change 2 ^ 8 < prefixSum a 22 - prefixSum a 4; omega) hlin

/-- Unconditional exclusion of linear stabilization from `n₀ = 6` via the explicit inter-prefix
gap witness `(j, r) = (61, 11)` (`prefixSum a 61 = 2005 < 2 ^ 11 = 2048 < 2052 = prefixSum a 62 - prefixSum a 5`). -/
theorem not_eventual_linear_from_six :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (C : ℕ),
      ¬(∀ n : ℕ, 6 ≤ n → a n = n + C) := by
  intro a ha C hlin
  have ha6 : a 6 = 8 := erdos_423_test_a_six a ha
  have h6 : a 6 = 6 + C := hlin 6 le_rfl
  have hC : C = 2 := by omega
  have hP5 : prefixSum a 5 = 17 := IsHofstadterSeq_prefixSum_five a ha
  have hP61 := two_mul_prefixSum_tail_decomposition a 6 C 61 hlin (by omega) (by omega)
  have hP62 := two_mul_prefixSum_tail_decomposition a 6 C 62 hlin (by omega) (by omega)
  change 2 * prefixSum a 61 = 2 * prefixSum a 5 + (61 - 6 + 1) * (2 * 6 + 2 * C + (61 - 6)) at hP61
  change 2 * prefixSum a 62 = 2 * prefixSum a 5 + (62 - 6 + 1) * (2 * 6 + 2 * C + (62 - 6)) at hP62
  exact not_eventual_linear_of_inter_prefix_gap_two_pow a ha 6 C 61 11
    (by omega) (by omega) (by change 2 ^ 11 < prefixSum a 62 - prefixSum a 5; omega) hlin

/-- Unconditional non-stabilization for all small thresholds `1 ≤ n₀ ≤ 4` and all shifts `C : ℕ`,
proved via the explicit inter-prefix gap witnesses at `n₀ = 1, 2, 3, 4`. -/
theorem not_eventual_linear_of_le_four :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
      1 ≤ n₀ → n₀ ≤ 4 → ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C) := by
  intro a ha n₀ C hn₀1 hn₀4
  have hcases : n₀ = 1 ∨ n₀ = 2 ∨ n₀ = 3 ∨ n₀ = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact not_eventual_linear_from_one a ha C
  · exact not_eventual_linear_from_two a ha C
  · exact not_eventual_linear_from_three a ha C
  · exact not_eventual_linear_from_four a ha C

/-- Extended unconditional non-stabilization for all thresholds `1 ≤ n₀ ≤ 6` and all shifts `C : ℕ`. -/
theorem not_eventual_linear_of_le_six :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
      1 ≤ n₀ → n₀ ≤ 6 → ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C) := by
  intro a ha n₀ C hn₀1 hn₀6
  have hcases : n₀ ≤ 4 ∨ n₀ = 5 ∨ n₀ = 6 := by omega
  rcases hcases with hle4 | rfl | rfl
  · exact not_eventual_linear_of_le_four a ha n₀ C hn₀1 hle4
  · exact not_eventual_linear_from_five a ha C
  · exact not_eventual_linear_from_six a ha C

/-!
## Section 3: 2-Adic Collision Factorization and Pigeonhole Finite-Solution Reduction over `1 ≤ i < n₀`
-/

/-- Uniqueness of `v` for a fixed exponent `r` in the completed-square equation
`(2 * v + 1) ^ 2 + A = 2 ^ (r + 3) + B`. -/
theorem completed_square_v_eq_of_r_eq :
    ∀ (A B v₁ v₂ r : ℕ),
      (2 * v₁ + 1) ^ 2 + A = 2 ^ (r + 3) + B →
      (2 * v₂ + 1) ^ 2 + A = 2 ^ (r + 3) + B →
      v₁ = v₂ := by
  intro A B v₁ v₂ r h1 h2
  have hsq : (2 * v₁ + 1) ^ 2 = (2 * v₂ + 1) ^ 2 := by omega
  nlinarith

/-- Uniqueness of the exponent `r` for a fixed `v` in `(2 * v + 1) ^ 2 + A = 2 ^ (r + 3) + B`. -/
theorem completed_square_r_eq_of_v_eq :
    ∀ (A B v r₁ r₂ : ℕ),
      (2 * v + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B →
      (2 * v + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B →
      r₁ = r₂ := by
  intro A B v r₁ r₂ h1 h2
  have hpow : 2 ^ (r₁ + 3) = 2 ^ (r₂ + 3) := by omega
  have hinj := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hpow
  omega

/-- Strict monotonicity of `v` with respect to `r` in `(2 * v + 1) ^ 2 + A = 2 ^ (r + 3) + B`. -/
theorem completed_square_v_lt_of_r_lt :
    ∀ (A B v₁ v₂ r₁ r₂ : ℕ),
      r₁ < r₂ →
      (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B →
      (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B →
      v₁ < v₂ := by
  intro A B v₁ v₂ r₁ r₂ hr h1 h2
  have hpow : 2 ^ (r₁ + 3) < 2 ^ (r₂ + 3) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  have hsq : (2 * v₁ + 1) ^ 2 < (2 * v₂ + 1) ^ 2 := by omega
  nlinarith

/-- Exact difference-of-squares collision identity for two solutions `(v₁, r₁)` and `(v₂, r₂)`
(`r₁ ≤ r₂`, `v₁ ≤ v₂`) sharing the same offsets `(A, B)`:
`(v₂ - v₁) * (v₂ + v₁ + 1) = 2 ^ (r₁ + 1) * (2 ^ (r₂ - r₁) - 1)`. -/
theorem completed_square_collision_factor_eq :
    ∀ (A B v₁ v₂ r₁ r₂ : ℕ),
      r₁ ≤ r₂ → v₁ ≤ v₂ →
      (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B →
      (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B →
      (v₂ - v₁) * (v₂ + v₁ + 1) = 2 ^ (r₁ + 1) * (2 ^ (r₂ - r₁) - 1) := by
  intro A B v₁ v₂ r₁ r₂ hr hv h1 h2
  set dv := v₂ - v₁
  set dr := r₂ - r₁
  have hv2 : v₂ = v₁ + dv := by omega
  have hr2 : r₂ + 3 = (r₁ + 1) + dr + 2 := by omega
  have hlhs : 4 * (dv * (v₂ + v₁ + 1)) + (2 * v₁ + 1) ^ 2 = (2 * v₂ + 1) ^ 2 := by
    rw [hv2]
    ring
  have hrhs : 4 * (2 ^ (r₁ + 1) * (2 ^ dr - 1)) + 2 ^ (r₁ + 3) = 2 ^ (r₂ + 3) := by
    have hge : 1 ≤ 2 ^ dr := Nat.one_le_two_pow
    have hsub : 2 ^ dr - 1 + 1 = 2 ^ dr := by omega
    calc 4 * (2 ^ (r₁ + 1) * (2 ^ dr - 1)) + 2 ^ (r₁ + 3)
        = 4 * 2 ^ (r₁ + 1) * (2 ^ dr - 1 + 1) := by
          rw [show r₁ + 3 = (r₁ + 1) + 2 by omega, pow_add]
          ring
      _ = 4 * 2 ^ (r₁ + 1) * 2 ^ dr := by rw [hsub]
      _ = 2 ^ (r₂ + 3) := by rw [hr2, pow_add, pow_add]; ring
  omega

/-- Opposite-parity invariant for the collision factors `v₂ - v₁` and `v₂ + v₁ + 1` (`v₁ ≤ v₂`):
their sum is `2 * v₂ + 1`, which is always odd. -/
theorem completed_square_collision_factors_add_odd :
    ∀ (v₁ v₂ : ℕ), v₁ ≤ v₂ →
      ((v₂ - v₁) + (v₂ + v₁ + 1)) % 2 = 1 := by
  intro v₁ v₂ hv
  omega

/-- Universal 2-adic coprime-factor lemma: if `x` is odd and `x * y = 2 ^ k * z`, then
`2 ^ k` divides `y`, i.e., there exists `q : ℕ` with `y = 2 ^ k * q` and `x * q = z`. -/
theorem exists_eq_two_pow_mul_of_odd_mul_eq :
    ∀ (k x y z : ℕ), x % 2 = 1 → x * y = 2 ^ k * z →
      ∃ q : ℕ, y = 2 ^ k * q ∧ x * q = z := by
  intro k
  induction k with
  | zero =>
    intro x y z _ hxy
    refine ⟨y, by simp, ?_⟩
    simpa using hxy
  | succ m ih =>
    intro x y z hx hxy
    have hy_even : y % 2 = 0 := by
      have h2 : 2 ^ (m + 1) * z = 2 * (2 ^ m * z) := by rw [pow_succ]; ring
      have hmod : (x * y) % 2 = 0 := by rw [hxy, h2]; omega
      rw [Nat.mul_mod, hx] at hmod
      omega
    have hy_div : y = 2 * (y / 2) := by omega
    have hxy2 : x * (y / 2) = 2 ^ m * z := by
      rw [hy_div, pow_succ] at hxy
      linarith
    obtain ⟨q, hq1, hq2⟩ := ih x (y / 2) z hx hxy2
    refine ⟨q, ?_, hq2⟩
    rw [hy_div, hq1, pow_succ]
    ring

/-- If `(x + y) % 2 = 1`, `1 ≤ z`, and `x * y = 2 ^ k * z`, then either `2 ^ k ≤ x` or `2 ^ k ≤ y`. -/
theorem two_pow_le_of_mul_eq_two_pow_mul_of_add_odd :
    ∀ (k x y z : ℕ), (x + y) % 2 = 1 → 1 ≤ z → x * y = 2 ^ k * z →
      2 ^ k ≤ x ∨ 2 ^ k ≤ y := by
  intro k x y z hodd hz hxy
  have hpar : x % 2 = 1 ∨ y % 2 = 1 := by omega
  rcases hpar with hx1 | hy1
  · right
    obtain ⟨q, hq1, hq2⟩ := exists_eq_two_pow_mul_of_odd_mul_eq k x y z hx1 hxy
    rcases q with _ | q
    · simp at hq2; omega
    · rw [hq1]
      exact Nat.le_mul_of_pos_right (2 ^ k) (by omega)
  · left
    obtain ⟨q, hq1, hq2⟩ := exists_eq_two_pow_mul_of_odd_mul_eq k y x z hy1 (by linarith)
    rcases q with _ | q
    · simp at hq2; omega
    · rw [hq1]
      exact Nat.le_mul_of_pos_right (2 ^ k) (by omega)

/-- 2-adic exponential jump for two solutions `(v₁, r₁)` and `(v₂, r₂)` (`r₁ < r₂`) to the
completed-square equation `(2 * v + 1) ^ 2 + A = 2 ^ (r + 3) + B` sharing the same `(A, B)`:
`2 ^ (r₁ + 1) ≤ v₂ + v₁ + 1` and `2 ^ r₁ ≤ v₂`. -/
theorem two_pow_le_of_completed_square_collision :
    ∀ (A B v₁ v₂ r₁ r₂ : ℕ),
      r₁ < r₂ →
      (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B →
      (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B →
      2 ^ (r₁ + 1) ≤ v₂ + v₁ + 1 ∧ 2 ^ r₁ ≤ v₂ := by
  intro A B v₁ v₂ r₁ r₂ hr h1 h2
  have hv : v₁ < v₂ := completed_square_v_lt_of_r_lt A B v₁ v₂ r₁ r₂ hr h1 h2
  have hcol := completed_square_collision_factor_eq A B v₁ v₂ r₁ r₂ (by omega) (by omega) h1 h2
  have hodd := completed_square_collision_factors_add_odd v₁ v₂ (by omega)
  have hz : 1 ≤ 2 ^ (r₂ - r₁) - 1 := by
    have hpow : 2 ^ 1 ≤ 2 ^ (r₂ - r₁) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    omega
  have hdisj := two_pow_le_of_mul_eq_two_pow_mul_of_add_odd
    (r₁ + 1) (v₂ - v₁) (v₂ + v₁ + 1) (2 ^ (r₂ - r₁) - 1) hodd hz hcol
  have hle_sum : 2 ^ (r₁ + 1) ≤ v₂ + v₁ + 1 := by
    rcases hdisj with hleft | hright
    · omega
    · exact hright
  have hpow_succ : 2 ^ (r₁ + 1) = 2 * 2 ^ r₁ := by ring
  omega

/-- Explicit exponent threshold: if `max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r`, then
`max n₀ 3 + C ≤ 2 ^ r` and `prefixSum a (n₀ - 1) < 2 ^ r`. -/
theorem threshold_le_two_pow_of_ge_add :
    ∀ (a : ℕ → ℕ) (n₀ C r : ℕ),
      max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r →
      max n₀ 3 + C ≤ 2 ^ r ∧ prefixSum a (n₀ - 1) < 2 ^ r := by
  intro a n₀ C r hr
  have hlt : r < 2 ^ r := Nat.lt_two_pow_self
  omega

/-- Prefix-index exponent fiber in a window `[r₀, r₀ + K)`: the finset of exponents
`r ∈ Finset.Ico r₀ (r₀ + K)` for which the completed-square equation
`(2 * v + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) = 2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2`
admits a solution `v : ℕ`. -/
def completedSquareExpFiber (a : ℕ → ℕ) (n₀ C r₀ K i : ℕ) : Finset ℕ :=
  (Finset.Ico r₀ (r₀ + K)).filter (fun r =>
    ∃ v : ℕ, (2 * v + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) =
      2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2)

/-- Under eventual stabilization `a n = n + C` (`n ≥ n₀ ≥ 1`), every exponent window
`Finset.Ico r₀ (r₀ + K)` with `r₀ ≥ max n₀ 3 + C + prefixSum a (n₀ - 1)` is covered by the
union of `completedSquareExpFiber a n₀ C r₀ K i` over `i ∈ Finset.Ico 1 n₀`. -/
theorem subset_biUnion_completedSquareExpFiber_of_eventual_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r₀ K : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r₀ →
      Finset.Ico r₀ (r₀ + K) ⊆
        (Finset.Ico 1 n₀).biUnion (completedSquareExpFiber a n₀ C r₀ K) := by
  intro a ha n₀ C r₀ K hn₀ hlin hr₀ r hr
  rw [Finset.mem_Ico] at hr
  have hthresh := threshold_le_two_pow_of_ge_add a n₀ C r (by omega)
  obtain ⟨i, j, hi1, hin₀, -, hcs⟩ :=
    exists_completed_square_discriminant_of_two_pow a ha n₀ C r hn₀ hlin hthresh.1 hthresh.2
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_Ico.2 ⟨hi1, hin₀⟩, ?_⟩
  unfold completedSquareExpFiber
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_Ico.2 hr, j + C, ?_⟩
  rw [show 2 * (j + C) + 1 = 2 * j + 2 * C + 1 by omega]
  exact hcs

/-- Pigeonhole window bound over `1 ≤ i < n₀`: if `a n = n + C` for `n ≥ n₀ ≥ 1`,
`r₀ ≥ max n₀ 3 + C + prefixSum a (n₀ - 1)`, and each prefix index `1 ≤ i < n₀` accounts for
at most `B` exponents in `[r₀, r₀ + K)`, then `K ≤ (n₀ - 1) * B`. -/
theorem window_length_le_mul_of_completedSquareExpFiber_card_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r₀ K B : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r₀ →
      (∀ i ∈ Finset.Ico 1 n₀, (completedSquareExpFiber a n₀ C r₀ K i).card ≤ B) →
      K ≤ (n₀ - 1) * B := by
  intro a ha n₀ C r₀ K B hn₀ hlin hr₀ hB
  have hsub := subset_biUnion_completedSquareExpFiber_of_eventual_linear a ha n₀ C r₀ K hn₀ hlin hr₀
  have hcard1 : (Finset.Ico r₀ (r₀ + K)).card ≤
      ((Finset.Ico 1 n₀).biUnion (completedSquareExpFiber a n₀ C r₀ K)).card :=
    Finset.card_le_card hsub
  have hcard2 : ((Finset.Ico 1 n₀).biUnion (completedSquareExpFiber a n₀ C r₀ K)).card ≤
      (Finset.Ico 1 n₀).card * B :=
    Finset.card_biUnion_le_card_mul (Finset.Ico 1 n₀) (completedSquareExpFiber a n₀ C r₀ K) B hB
  simp only [Nat.card_Ico] at hcard1 hcard2
  omega

/-- Pigeonhole multiplicity forcing over `1 ≤ i < n₀`: under eventual stabilization `a n = n + C`
(`n ≥ n₀ ≥ 1`), in any exponent window `[r₀, r₀ + K)` of length `K > (n₀ - 1) * B` above
`max n₀ 3 + C + prefixSum a (n₀ - 1)`, at least one prefix index `1 ≤ i < n₀` must admit at
least `B + 1` distinct exponent solutions `r`. -/
theorem exists_prefix_index_with_many_completedSquare_solutions :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r₀ K B : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r₀ →
      (n₀ - 1) * B < K →
      ∃ i ∈ Finset.Ico 1 n₀, B + 1 ≤ (completedSquareExpFiber a n₀ C r₀ K i).card := by
  intro a ha n₀ C r₀ K B hn₀ hlin hr₀ hlt
  by_contra hnot
  have hB : ∀ i ∈ Finset.Ico 1 n₀, (completedSquareExpFiber a n₀ C r₀ K i).card ≤ B := by
    intro i hi
    by_contra hgt
    exact hnot ⟨i, hi, by omega⟩
  have hle := window_length_le_mul_of_completedSquareExpFiber_card_le a ha n₀ C r₀ K B hn₀ hlin hr₀ hB
  omega

/-- Finite-fiber pigeonhole refutation criterion: if in some window of length `(n₀ - 1) * B + 1`
starting at `r₀ ≥ max n₀ 3 + C + prefixSum a (n₀ - 1)` every `1 ≤ i < n₀` has at most `B`
solutions in `completedSquareExpFiber`, then `a` cannot stabilize to `n + C` at `n₀`. -/
theorem not_eventual_linear_of_completedSquareExpFiber_card_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r₀ B : ℕ),
      1 ≤ n₀ →
      max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r₀ →
      (∀ i ∈ Finset.Ico 1 n₀,
        (completedSquareExpFiber a n₀ C r₀ ((n₀ - 1) * B + 1) i).card ≤ B) →
      ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C) := by
  intro a ha n₀ C r₀ B hn₀ hr₀ hB hlin
  have hle := window_length_le_mul_of_completedSquareExpFiber_card_le
    a ha n₀ C r₀ ((n₀ - 1) * B + 1) B hn₀ hlin hr₀ hB
  omega

/-- Bridge from the pigeonhole finite-fiber hypothesis on `completedSquareExpFiber` to
`erdos_423.variants.unbounded` and `erdos_423.variants.infinite_complement` via
`unbounded_and_infinite_compl_of_not_eventual_linear`. -/
theorem unbounded_and_infinite_compl_of_completedSquare_fiber_bdd :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ n₀ C : ℕ, 1 ≤ n₀ → ∃ r₀ B : ℕ,
        max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r₀ ∧
        ∀ i ∈ Finset.Ico 1 n₀,
          (completedSquareExpFiber a n₀ C r₀ ((n₀ - 1) * B + 1) i).card ≤ B) →
      (∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n) ∧ Set.Infinite (Set.range a)ᶜ := by
  intro a ha hfib
  apply unbounded_and_infinite_compl_of_not_eventual_linear a ha
  intro n₀ C hn₀
  obtain ⟨r₀, B, hr₀, hB⟩ := hfib n₀ C hn₀
  exact not_eventual_linear_of_completedSquareExpFiber_card_le a ha n₀ C r₀ B hn₀ hr₀ hB

/-- Bridge from the finite-solution obstruction for the generalized Ramanujan-Nagell equation
`((2 * v + 1 : ℤ) ^ 2) + D = (2 : ℤ) ^ (r + 3)` (`D % 8 = 7`) to non-stabilization:
if every `D ≡ 7 (mod 8)` has a finite upper bound `R` on solution exponents `r`, then
no Hofstadter sequence can stabilize to `n + C` at any `n₀ ≥ 1`. -/
theorem not_eventual_linear_of_int_ramanujan_nagell_bdd :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ D : ℤ, D % 8 = 7 → ∃ R : ℕ, ∀ v r : ℕ,
        ((2 * v + 1 : ℤ) ^ 2) + D = (2 : ℤ) ^ (r + 3) → r ≤ R) →
      ∀ (n₀ C : ℕ), 1 ≤ n₀ → ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C) := by
  intro a ha hrn n₀ C hn₀ hlin
  choose R hR using fun (i : ℕ) =>
    hrn (discriminantOffset a n₀ C i) (discriminantOffset_emod_eight a n₀ C i hn₀)
  set r_max := (Finset.Ico 1 n₀).sup R
  set r₀ := max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (r_max + 1)
  have hthresh := threshold_le_two_pow_of_ge_add a n₀ C r₀ (le_max_left _ _)
  obtain ⟨i, v, hi1, hin₀, -, heq⟩ :=
    exists_int_completed_square_of_two_pow a ha n₀ C r₀ hn₀ hlin hthresh.1 hthresh.2
  have hle_Ri : r₀ ≤ R i := hR i v r₀ heq
  have hRi_le : R i ≤ r_max := Finset.le_sup (f := R) (Finset.mem_Ico.2 ⟨hi1, hin₀⟩)
  have hr₀_gt : r_max + 1 ≤ r₀ := le_max_right _ _
  omega

/-- Master reduction connecting the generalized Ramanujan-Nagell finite-solution obstruction
`((2 * v + 1 : ℤ) ^ 2) + D = (2 : ℤ) ^ (r + 3)` (`D % 8 = 7`) directly to
`erdos_423.variants.unbounded` and `erdos_423.variants.infinite_complement` via
`unbounded_and_infinite_compl_of_not_eventual_linear`. -/
theorem unbounded_and_infinite_compl_of_int_ramanujan_nagell_bdd :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ D : ℤ, D % 8 = 7 → ∃ R : ℕ, ∀ v r : ℕ,
        ((2 * v + 1 : ℤ) ^ 2) + D = (2 : ℤ) ^ (r + 3) → r ≤ R) →
      (∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n) ∧ Set.Infinite (Set.range a)ᶜ := by
  intro a ha hrn
  exact unbounded_and_infinite_compl_of_not_eventual_linear a ha
    (not_eventual_linear_of_int_ramanujan_nagell_bdd a ha hrn)

/-- Quadratic exponent-doubling bound for two completed-square solutions `(v₁, r₁)` and `(v₂, r₂)`
with `r₁ < r₂` and `B ≤ 2 ^ (r₁ + 3)`: since `2 ^ r₁ ≤ v₂`, we have
`2 ^ (2 * r₁ + 2) < (2 * v₂ + 1) ^ 2 ≤ 2 ^ (r₂ + 4)`, forcing `2 * r₁ ≤ r₂ + 1`. -/
theorem two_mul_le_succ_of_completed_square_collision :
    ∀ (A B v₁ v₂ r₁ r₂ : ℕ),
      r₁ < r₂ →
      B ≤ 2 ^ (r₁ + 3) →
      (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B →
      (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B →
      2 * r₁ ≤ r₂ + 1 := by
  intro A B v₁ v₂ r₁ r₂ hr hB h1 h2
  have hv2 : 2 ^ r₁ ≤ v₂ :=
    (two_pow_le_of_completed_square_collision A B v₁ v₂ r₁ r₂ hr h1 h2).2
  have hpow_step : 2 ^ (r₁ + 1) = 2 * 2 ^ r₁ := by ring
  have hlt_lin : 2 ^ (r₁ + 1) < 2 * v₂ + 1 := by omega
  have hsq_eq : 2 ^ (2 * r₁ + 2) = (2 ^ (r₁ + 1)) ^ 2 := by
    rw [show 2 * r₁ + 2 = (r₁ + 1) + (r₁ + 1) by omega, pow_add]
    ring
  have hsq_lt : 2 ^ (2 * r₁ + 2) < (2 * v₂ + 1) ^ 2 := by
    rw [hsq_eq]
    exact Nat.pow_lt_pow_left hlt_lin (by decide : 2 ≠ 0)
  have hpow_mono : 2 ^ (r₁ + 3) ≤ 2 ^ (r₂ + 3) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hpow_top : 2 ^ (r₂ + 4) = 2 * 2 ^ (r₂ + 3) := by ring
  have hpow_lt : 2 ^ (2 * r₁ + 2) < 2 ^ (r₂ + 4) := by omega
  by_contra hnot
  have hle_exp : r₂ + 4 ≤ 2 * r₁ + 2 := by omega
  have hpow_ge : 2 ^ (r₂ + 4) ≤ 2 ^ (2 * r₁ + 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle_exp
  omega

/-- Subsingleton property of `completedSquareExpFiber` on any window `[r₀, r₀ + K)` with
`K + 1 ≤ r₀` and `(2 * n₀ + 2 * C - 1) ^ 2 ≤ r₀`: no two distinct exponents in `[r₀, r₀ + K)`
can belong to the same fiber `completedSquareExpFiber a n₀ C r₀ K i`. -/
theorem completedSquareExpFiber_eq_of_mem :
    ∀ (a : ℕ → ℕ) (n₀ C r₀ K i r₁ r₂ : ℕ),
      K + 1 ≤ r₀ →
      (2 * n₀ + 2 * C - 1) ^ 2 ≤ r₀ →
      r₁ ∈ completedSquareExpFiber a n₀ C r₀ K i →
      r₂ ∈ completedSquareExpFiber a n₀ C r₀ K i →
      r₁ = r₂ := by
  intro a n₀ C r₀ K i r₁ r₂ hK hB hr₁ hr₂
  unfold completedSquareExpFiber at hr₁ hr₂
  rw [Finset.mem_filter, Finset.mem_Ico] at hr₁ hr₂
  rcases hr₁ with ⟨⟨hr₁_lo, hr₁_hi⟩, v₁, hv₁⟩
  rcases hr₂ with ⟨⟨hr₂_lo, hr₂_hi⟩, v₂, hv₂⟩
  rcases lt_trichotomy r₁ r₂ with hlt | rfl | hgt
  · exfalso
    have hpow1 : r₁ + 3 < 2 ^ (r₁ + 3) := Nat.lt_two_pow_self
    have hdupl := two_mul_le_succ_of_completed_square_collision
      (8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)))
      ((2 * n₀ + 2 * C - 1) ^ 2) v₁ v₂ r₁ r₂ hlt (by omega) hv₁ hv₂
    omega
  · rfl
  · exfalso
    have hpow2 : r₂ + 3 < 2 ^ (r₂ + 3) := Nat.lt_two_pow_self
    have hdupl := two_mul_le_succ_of_completed_square_collision
      (8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)))
      ((2 * n₀ + 2 * C - 1) ^ 2) v₂ v₁ r₂ r₁ hgt (by omega) hv₂ hv₁
    omega

/-- Uniform cardinality bound `(completedSquareExpFiber a n₀ C r₀ K i).card ≤ 1` for every
prefix index `i` whenever `K + 1 ≤ r₀` and `(2 * n₀ + 2 * C - 1) ^ 2 ≤ r₀`. -/
theorem completedSquareExpFiber_card_le_one :
    ∀ (a : ℕ → ℕ) (n₀ C r₀ K i : ℕ),
      K + 1 ≤ r₀ →
      (2 * n₀ + 2 * C - 1) ^ 2 ≤ r₀ →
      (completedSquareExpFiber a n₀ C r₀ K i).card ≤ 1 := by
  intro a n₀ C r₀ K i hK hB
  exact Finset.card_le_one.2 (fun r₁ hr₁ r₂ hr₂ =>
    completedSquareExpFiber_eq_of_mem a n₀ C r₀ K i r₁ r₂ hK hB hr₁ hr₂)

/-- Unconditional non-stabilization theorem for all thresholds `n₀ ≥ 1` and shifts `C : ℕ`
(Tang [Ta26]): no Hofstadter sequence `a` can satisfy `a n = n + C` for all `n ≥ n₀`. -/
theorem not_eventual_linear_of_isHofstadterSeq :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
      1 ≤ n₀ → ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C) := by
  intro a ha n₀ C hn₀
  set r₀ := max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2))
  have hr₀1 : max n₀ 3 + C + prefixSum a (n₀ - 1) ≤ r₀ := le_max_left _ _
  have hr₀2 : n₀ + 1 ≤ r₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hr₀3 : (2 * n₀ + 2 * C - 1) ^ 2 ≤ r₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine not_eventual_linear_of_completedSquareExpFiber_card_le a ha n₀ C r₀ 1 hn₀ hr₀1 ?_
  intro i _
  exact completedSquareExpFiber_card_le_one a n₀ C r₀ ((n₀ - 1) * 1 + 1) i (by omega) hr₀3

/-- Unconditional resolution of `erdos_423.variants.unbounded` and
`erdos_423.variants.infinite_complement` (Tang, arXiv:2603.09939):
for any Hofstadter sequence `a`, `a n - n` tends to infinity (`∀ M, ∀ᶠ n in atTop, M + n ≤ a n`)
and `(Set.range a)ᶜ` is infinite. -/
theorem erdos_423_variants_unbounded_and_infinite_compl :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n) ∧ Set.Infinite (Set.range a)ᶜ := by
  intro a ha
  exact unbounded_and_infinite_compl_of_not_eventual_linear a ha
    (not_eventual_linear_of_isHofstadterSeq a ha)

/-- Unconditional proof of `erdos_423.variants.unbounded` (`∀ M, ∀ᶠ n in atTop, M + n ≤ a n`). -/
theorem erdos_423_variants_unbounded :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n := by
  intro a ha
  exact (erdos_423_variants_unbounded_and_infinite_compl a ha).1

/-- Unconditional proof of `erdos_423.variants.infinite_complement` (`Set.Infinite (Set.range a)ᶜ`). -/
theorem erdos_423_variants_infinite_complement :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → Set.Infinite (Set.range a)ᶜ := by
  intro a ha
  exact (erdos_423_variants_unbounded_and_infinite_compl a ha).2

/-- Canonical Formal Conjectures declaration `Erdos423.erdos_423.variants.unbounded`
(Bolan and Tang, independently, 2026): $a_n - n \to \infty$. -/
theorem erdos_423.variants.unbounded :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n :=
  erdos_423_variants_unbounded

/-- Canonical Formal Conjectures declaration `Erdos423.erdos_423.variants.infinite_complement`
(Bolan and Tang, independently, 2026): infinitely many positive integers do not occur in the
Hofstadter sequence. -/
theorem erdos_423.variants.infinite_complement :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a → Set.Infinite (Set.range a)ᶜ :=
  erdos_423_variants_infinite_complement

/-!
## Section 4: Explicit Positive and Negative Controls
-/

/-- Positive control 1 (Ramanujan-Nagell `D = 7`): the classical equation
`(2 * v + 1) ^ 2 + 7 = 2 ^ (r + 3)` holds for all five Ramanujan-Nagell pairs
`(v, r) ∈ {(0, 0), (1, 1), (2, 2), (5, 4), (90, 12)}`. -/
theorem ramanujan_nagell_positive_control_D7 :
    ∀ (v r : ℕ),
      (v = 0 ∧ r = 0) ∨ (v = 1 ∧ r = 1) ∨ (v = 2 ∧ r = 2) ∨ (v = 5 ∧ r = 4) ∨ (v = 90 ∧ r = 12) →
      (2 * v + 1) ^ 2 + 7 = 2 ^ (r + 3) := by
  intro v r h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- Negative control 1 (Modulo-8 obstruction when `D = 8 * k`):
no pair `(v, r)` can satisfy `(2 * v + 1) ^ 2 + 8 * k = 2 ^ (r + 3)` because the left-hand side
is congruent to `1 (mod 8)` while `2 ^ (r + 3) ≡ 0 (mod 8)`. -/
theorem completed_square_ne_two_pow_of_eight_mul_offset :
    ∀ (v k r : ℕ), (2 * v + 1) ^ 2 + 8 * k ≠ 2 ^ (r + 3) := by
  intro v k r heq
  have hodd := odd_sq_mod_eight_eq_one v
  have hpow : 2 ^ (r + 3) = 8 * 2 ^ r := by ring
  omega

/-- Positive control 2 (`n₀ = 4, C = 1, r = 5`): before the gap witness `2 ^ 6 = 64` at `n₀ = 4`,
the power of two `2 ^ 5 = 32` is represented by the prefix-crossing completed-square equation
at `(i, j, r) = (1, 7, 5)` (`(2 * 7 + 2 * 1 + 1) ^ 2 + 8 * 6 = 337 = 2 ^ 8 + 9 ^ 2`). -/
theorem completed_square_positive_control_n0_four_r_five :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (2 * 7 + 2 * 1 + 1) ^ 2 + 8 * (prefixSum a (4 - 1) - prefixSum a (1 - 1)) =
        2 ^ (5 + 3) + (2 * 4 + 2 * 1 - 1) ^ 2 := by
  intro a ha
  rw [show 4 - 1 = 3 by decide, show 1 - 1 = 0 by decide,
    IsHofstadterSeq_prefixSum_three a ha, prefixSum_zero]
  norm_num

end Erdos423

end
