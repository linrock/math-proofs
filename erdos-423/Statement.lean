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
public import Blueprint423

@[expose] public section

noncomputable section
open Finset BigOperators Filter Asymptotics

namespace Erdos423.Challenge

open Erdos423

def statement_erdos_423_variants_nondecreasing : Prop :=
  ∀ a : ℕ → ℕ, IsHofstadterSeq a → ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m

def statement_erdos_423_variants_unbounded : Prop :=
  ∀ a : ℕ → ℕ, IsHofstadterSeq a → ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n

def statement_erdos_423_variants_infinite_complement : Prop :=
  ∀ a : ℕ → ℕ, IsHofstadterSeq a → Set.Infinite (Set.range a)ᶜ

def statement_existsUnique_isHofstadterSeq : Prop :=
  ∃! a : ℕ → ℕ, a 0 = 0 ∧ IsHofstadterSeq a

def statement_IsHofstadterSeq_card_omitted_Icc_eq_sub : Prop :=
  ∀ {a : ℕ → ℕ}, IsHofstadterSeq a → ∀ {n : ℕ}, 1 ≤ n →
    ((Finset.Icc 1 (a n)) \ ((Finset.Icc 1 n).image a)).card = a n - n

def statement_IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum : Prop :=
  ∀ {a : ℕ → ℕ}, IsHofstadterSeq a → ∀ (m : ℕ),
    (∃ k : ℕ, 3 ≤ k ∧ a k = m) ↔ IsGlobalConsecutiveBlockSum a m

def statement_two_mul_sub_one_le_of_prefixSum_le : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
    prefixSum a m ≤ a N → 2 * m - 1 ≤ N

def statement_strict_excess_increase_of_blockSum_eq_two_pow : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j r : ℕ),
    1 ≤ i → i + 1 ≤ j → ∑ l ∈ Finset.Icc i j, a l = 2 ^ r → a i - i < a j - j

def statement_completed_square_tail_quadratic_identity : Prop :=
  ∀ (n₀ C j : ℕ), 1 ≤ n₀ → n₀ ≤ j →
    4 * ((j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀))) + (2 * n₀ + 2 * C - 1) ^ 2 =
      (2 * j + 2 * C + 1) ^ 2

def statement_exists_completed_square_discriminant_of_two_pow : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r : ℕ),
    1 ≤ n₀ →
    (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
    max n₀ 3 + C ≤ 2 ^ r →
    prefixSum a (n₀ - 1) < 2 ^ r →
    ∃ i j : ℕ, 1 ≤ i ∧ i < n₀ ∧ n₀ ≤ j ∧
      (2 * j + 2 * C + 1) ^ 2 + 8 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) =
        2 ^ (r + 3) + (2 * n₀ + 2 * C - 1) ^ 2

def statement_discriminantOffset_emod_eight : Prop :=
  ∀ (a : ℕ → ℕ) (n₀ C i : ℕ), 1 ≤ n₀ →
    discriminantOffset a n₀ C i % 8 = 7

def statement_completed_square_collision_factor_eq : Prop :=
  ∀ (A B v₁ v₂ r₁ r₂ : ℕ),
    r₁ ≤ r₂ → v₁ ≤ v₂ →
    (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B →
    (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B →
    (v₂ - v₁) * (v₂ + v₁ + 1) = 2 ^ (r₁ + 1) * (2 ^ (r₂ - r₁) - 1)

def statement_two_pow_le_of_completed_square_collision : Prop :=
  ∀ (A B v₁ v₂ r₁ r₂ : ℕ),
    r₁ < r₂ →
    (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B →
    (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B →
    2 ^ (r₁ + 1) ≤ v₂ + v₁ + 1 ∧ 2 ^ r₁ ≤ v₂

def statement_two_mul_le_succ_of_completed_square_collision : Prop :=
  ∀ (A B v₁ v₂ r₁ r₂ : ℕ),
    r₁ < r₂ →
    B ≤ 2 ^ (r₁ + 3) →
    (2 * v₁ + 1) ^ 2 + A = 2 ^ (r₁ + 3) + B →
    (2 * v₂ + 1) ^ 2 + A = 2 ^ (r₂ + 3) + B →
    2 * r₁ ≤ r₂ + 1

def statement_completedSquareExpFiber_card_le_one : Prop :=
  ∀ (a : ℕ → ℕ) (n₀ C r₀ K i : ℕ),
    K + 1 ≤ r₀ →
    (2 * n₀ + 2 * C - 1) ^ 2 ≤ r₀ →
    (completedSquareExpFiber a n₀ C r₀ K i).card ≤ 1

def statement_not_eventual_linear_of_isHofstadterSeq : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
    1 ≤ n₀ → ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C)

def statement_exists_stabilization_breaking_index_le : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
    1 ≤ n₀ →
    let r₀ := max (max n₀ 3 + C + prefixSum a (n₀ - 1)) (max (n₀ + 1) ((2 * n₀ + 2 * C - 1) ^ 2)) + n₀
    ∃ n₁ : ℕ, n₀ ≤ n₁ ∧ n₁ ≤ 2 ^ r₀ + C ∧ a n₁ ≠ n₁ + C

def statement_strict_excess_increase_at_stabilizationIndexHorizon : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C : ℕ),
    1 ≤ n₀ → a n₀ - n₀ ≤ C →
    a n₀ - n₀ < a (stabilizationIndexHorizon a n₀ C) - stabilizationIndexHorizon a n₀ C

def statement_le_excess_of_iterExcessHorizon_le : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (k n : ℕ),
    iterExcessHorizon a k ≤ n →
    k ≤ a n - n ∧ k + n ≤ a n

def statement_iterExcessHorizon_one_eq_sixteen : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → iterExcessHorizon a 1 = 16

def statement_nextExcessHorizon_le_two_pow_five_mul_sq_add : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ : ℕ), 1 ≤ n₀ →
    nextExcessHorizon a n₀ ≤ 2 ^ (5 * (a n₀) ^ 2) + a n₀

def statement_erdos_423_variants_lower_bound_of_iterExcessHorizon_log_log_le : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (B : ℝ),
    0 ≤ B →
    (∀ k : ℕ, 1 ≤ k →
      Real.log (Real.log (iterExcessHorizon a (k + 1) : ℝ)) ≤ B * (k : ℝ)) →
    (fun n : ℕ => Real.log (Real.log n)) =O[atTop] (fun n : ℕ => (a n : ℝ) - n)

def statement_erdos_423_variants_upper_bound_of_iterExcessHorizon_rpow_le : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (ε B : ℝ),
    0 < ε → 0 ≤ B →
    (∀ k : ℕ, 1 ≤ k →
      ((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) ≤
        B * (iterExcessHorizon a k : ℝ) ^ ((688 : ℝ) / 413 + ε)) →
    (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((688 : ℝ) / 413 + ε))

def statement_erdos_423_of_iterExcessHorizon_littleO_bound : Prop :=
  ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
    (∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k →
      ((a (iterExcessHorizon a (k + 1)) - iterExcessHorizon a (k + 1) : ℕ) : ℝ) ≤
        ε * (iterExcessHorizon a k : ℝ)) →
    (fun n : ℕ => (a n : ℝ) - n) =o[atTop] (fun n : ℕ => (n : ℝ))

end Erdos423.Challenge

end
