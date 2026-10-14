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

public import Erdos886Unified435
public import SixTupleHyperbolicDeterminantsAndDivisorDifferenceGCD886
public import Blueprint886

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos886.Challenge

open Erdos886

/-- The open conjecture `erdos_886` in `FormalConjectures/ErdosProblems/886.lean`. -/
def statement_erdos_886 : Prop :=
  ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K

def statement_erdos_886_variants_rosenfeld_infinite : Prop :=
  Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1 / 4) 16).card}

def statement_erdos_886_variants_rosenfeld_bound : Prop :=
  ∀ C > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      (((Nat.divisors n).filter (fun (d : ℕ) =>
        (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
        (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
        ≤ 1 + C ^ 2

def statement_card_erdos886Divisors_le_one_of_quarter_le : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 1 / 4 ≤ ε → (Erdos886Divisors n ε 1).card ≤ 1

def statement_erdos_886_of_quarter_le : Prop :=
  ∀ (ε : ℝ), 1 / 4 ≤ ε → ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K

def statement_erdos_886_iff_forall_pos_lt_quarter : Prop :=
  (∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K) ↔
      (∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K)

def statement_complementary_divisor_hyperbolic_identity : Prop :=
  ∀ (n d : ℕ), d ∈ Nat.divisors n →
    (d : ℝ) * ((d : ℝ) + (n / d : ℕ) - 2 * (n : ℝ) ^ (1 / 2 : ℝ)) =
      ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2

def statement_complementary_sum_strict_mono_of_ge_sqrt : Prop :=
  ∀ (n d₁ d₂ : ℕ), d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ) → d₁ < d₂ →
    d₁ + n / d₁ < d₂ + n / d₂

def statement_fifth_order_hyperbolic_vandermonde_six_tuple_identity : Prop :=
  ∀ (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n → d₃ ∈ Nat.divisors n →
    d₄ ∈ Nat.divisors n → d₅ ∈ Nat.divisors n → d₆ ∈ Nat.divisors n →
    (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) *
      (((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₃ : ℝ)) * ((d₆ : ℝ) - (d₂ : ℝ)) *
        (((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) *
          (((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
            (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
              ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
          ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
            (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
              ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))))) -
        ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) *
          (((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
            (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
              ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
            (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
              ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))))) -
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) * ((d₅ : ℝ) - (d₁ : ℝ)) *
        (((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₃ : ℝ)) *
          (((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
            (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
              ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) *
            (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
              ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) *
          (((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
            (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
              ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))) -
          ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) *
            (((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
              ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))))))) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
        ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) *
        ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        ((d₄ : ℝ) - (d₁ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₃ : ℝ)) *
        ((d₅ : ℝ) - (d₁ : ℝ)) * ((d₆ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₁ : ℝ))

def statement_six_tuple_product_le_mul_full_vandermonde_of_lt : Prop :=
  ∀ (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n → d₃ ∈ Nat.divisors n →
    d₄ ∈ Nat.divisors n → d₅ ∈ Nat.divisors n → d₆ ∈ Nat.divisors n →
    d₁ < d₂ → d₂ < d₃ → d₃ < d₄ → d₄ < d₅ → d₅ < d₆ →
    d₁ * d₂ * d₃ * d₄ * d₅ * d₆ ≤
      n * (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₅ - d₄) * (d₆ - d₅) *
        (d₃ - d₁) * (d₄ - d₂) * (d₅ - d₃) * (d₆ - d₄) *
        (d₄ - d₁) * (d₅ - d₂) * (d₆ - d₃) *
        (d₅ - d₁) * (d₆ - d₂) * (d₆ - d₁)

def statement_sq_lt_full_vandermonde_of_six_mem_erdos886Divisors : Prop :=
  ∀ (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) (ε C : ℝ),
    d₁ ∈ Erdos886Divisors n ε C → d₂ ∈ Erdos886Divisors n ε C →
    d₃ ∈ Erdos886Divisors n ε C → d₄ ∈ Erdos886Divisors n ε C →
    d₅ ∈ Erdos886Divisors n ε C → d₆ ∈ Erdos886Divisors n ε C →
    d₁ < d₂ → d₂ < d₃ → d₃ < d₄ → d₄ < d₅ → d₅ < d₆ →
    n ^ 2 <
      (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₅ - d₄) * (d₆ - d₅) *
        (d₃ - d₁) * (d₄ - d₂) * (d₅ - d₃) * (d₆ - d₄) *
        (d₄ - d₁) * (d₅ - d₂) * (d₆ - d₃) *
        (d₅ - d₁) * (d₆ - d₂) * (d₆ - d₁)

def statement_gcd_mul_complementary_sum_diff_eq_diff_mul_gcd_sub_lcm_quotient : Prop :=
  ∀ (n d₁ d₂ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ) → d₁ ≤ d₂ →
    Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) =
      (d₂ - d₁) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂)

def statement_complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient : Prop :=
  ∀ (n d₁ d₂ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ) → d₁ ≤ d₂ →
    (d₂ + n / d₂) - (d₁ + n / d₁) =
      ((d₂ - d₁) / Nat.gcd d₁ d₂) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂)

def statement_divisor_diff_eq_gcd_of_complementary_sum_diff_eq_one : Prop :=
  ∀ (n d₁ d₂ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ) → d₁ < d₂ →
    (d₂ + n / d₂) - (d₁ + n / d₁) = 1 →
    d₂ - d₁ = Nat.gcd d₁ d₂

def statement_gcd_complementary_divisors_eq_div_lcm : Prop :=
  ∀ (n d₁ d₂ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    Nat.gcd (n / d₁) (n / d₂) = n / Nat.lcm d₁ d₂

def statement_coprime_cofactor_four_factor_decomposition : Prop :=
  ∀ (n d₁ d₂ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    n = Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂) * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂)

def statement_lcm_complementary_divisors_eq_div_gcd : Prop :=
  ∀ (n d₁ d₂ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    Nat.lcm (n / d₁) (n / d₂) = n / Nat.gcd d₁ d₂

def statement_complementary_sum_diff_eq_coprime_cofactor_diff_mul_gcd_diff : Prop :=
  ∀ (n d₁ d₂ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ) → d₁ ≤ d₂ →
    (d₂ + n / d₂) - (d₁ + n / d₁) =
      (d₂ / Nat.gcd d₁ d₂ - d₁ / Nat.gcd d₁ d₂) *
        (Nat.gcd d₁ d₂ - Nat.gcd (n / d₁) (n / d₂))

def statement_double_oblong_factorization_of_complementary_sum_diff_eq_one : Prop :=
  ∀ (n d₁ d₂ : ℕ),
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ) → d₁ < d₂ →
    (d₂ + n / d₂) - (d₁ + n / d₁) = 1 →
    d₂ / Nat.gcd d₁ d₂ = d₁ / Nat.gcd d₁ d₂ + 1 ∧
    Nat.gcd d₁ d₂ = Nat.gcd (n / d₁) (n / d₂) + 1 ∧
    n / d₁ - n / d₂ = Nat.gcd (n / d₁) (n / d₂) ∧
    n = (Nat.gcd (n / d₁) (n / d₂) + 1) * Nat.gcd (n / d₁) (n / d₂) *
      (d₁ / Nat.gcd d₁ d₂) * (d₁ / Nat.gcd d₁ d₂ + 1)

def statement_finset_lcm_erdos886Divisors_dvd : Prop :=
  ∀ (n : ℕ) (ε C : ℝ), (Erdos886Divisors n ε C).lcm id ∣ n

def statement_two_le_gcd_of_mem_erdos886Divisors_of_lt : Prop :=
  ∀ (n d₁ d₂ : ℕ) (ε C : ℝ),
    d₁ ∈ Erdos886Divisors n ε C → d₂ ∈ Erdos886Divisors n ε C →
    d₁ < d₂ →
    2 ≤ Nat.gcd d₁ d₂

def statement_six_mul_gcd_mul_complementary_gcd_le_of_mem_erdos886Divisors : Prop :=
  ∀ (n d₁ d₂ : ℕ) (ε C : ℝ),
    0 ≤ ε → C ≤ 1 →
    d₁ ∈ Erdos886Divisors n ε C → d₂ ∈ Erdos886Divisors n ε C →
    d₁ < d₂ →
    6 * (Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂)) ≤ n ∧
    2 * Nat.gcd d₁ d₂ ≤ d₁

def statement_padicValNat_coprime_cofactor_four_term_sum : Prop :=
  ∀ (p n d₁ d₂ : ℕ) [Fact p.Prime],
    d₁ ∈ Nat.divisors n → d₂ ∈ Nat.divisors n →
    padicValNat p n =
      padicValNat p (Nat.gcd d₁ d₂) +
      padicValNat p (Nat.gcd (n / d₁) (n / d₂)) +
      padicValNat p (d₁ / Nat.gcd d₁ d₂) +
      padicValNat p (d₂ / Nat.gcd d₁ d₂)

def statement_card_erdos886Divisors_prime_pow_le_one_of_nonneg : Prop :=
  ∀ (p m : ℕ), Nat.Prime p → ∀ (ε : ℝ), 0 ≤ ε →
    (Erdos886Divisors (p ^ m) ε 1).card ≤ 1

def statement_erdos_886_of_eventual_coprime_cofactor_and_complementary_gcd_gap_bound : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ K : ℕ, ∀ᶠ n in Filter.atTop,
        ∀ a ∈ Erdos886Divisors n ε 1, ∀ b ∈ Erdos886Divisors n ε 1, a ≤ b →
          (b / Nat.gcd a b - a / Nat.gcd a b) *
            (Nat.gcd a b - Nat.gcd (n / a) (n / b)) ≤ K) →
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K

end Erdos886.Challenge

end
