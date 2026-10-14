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

namespace Erdos886.Palomar

open Erdos886

/-- Solved Erdős–Rosenfeld variant (`FormalConjectures.ErdosProblems.«886»`, [ErRo97]):
there are infinitely many `n : ℕ` having at least 4 divisors in the open near-square interval
`(n^{1/2}, n^{1/2} + 16 n^{1/4})`, proved unconditionally by exhibiting the explicit degree-8 parametric octic family
`rosenfeldN m = (m+3)(m+4)(m+5)(m+6)(m+8)(m+9)(m+10)(m+11)` with four explicit central divisors
`rosenfeldD1 m < rosenfeldD2 m < rosenfeldD3 m < rosenfeldD4 m`. -/
theorem erdos_886.variants.rosenfeld_infinite :
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1 / 4) 16).card} :=
  Erdos886.erdos_886.variants.rosenfeld_infinite

/-- Solved Erdős–Rosenfeld upper-bound variant (`FormalConjectures.ErdosProblems.«886»`, [ErRo97]):
for every constant `C > 0`, all sufficiently large `n : ℕ` (in fact all `n : ℕ`) have at most
`1 + C^2` divisors in the closed interval `[n^{1/2}, n^{1/2} + C n^{1/4}]`. -/
theorem erdos_886.variants.rosenfeld_bound :
    ∀ C > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      (((Nat.divisors n).filter (fun (d : ℕ) =>
        (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
        (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
        ≤ 1 + C ^ 2 :=
  Erdos886.erdos_886.variants.rosenfeld_bound

/-- Unconditional all-`n` resolution of `Erdos886Divisors n ε 1` in the regime `ε ≥ 1/4`:
for every `n : ℕ` and every `ε ≥ 1/4`, the open interval `(n^{1/2}, n^{1/2} + n^{1/2 - ε})`
contains at most one divisor of `n` (`(Erdos886Divisors n ε 1).card ≤ 1`), because the integer
complementary-divisor sum `d + n / d` is strictly increasing for `d ≥ n^{1/2}` and lies strictly
inside `(2 n^{1/2}, 2 n^{1/2} + 1)`. -/
theorem card_erdos886Divisors_le_one_of_quarter_le (n : ℕ) (ε : ℝ) (hε : 1 / 4 ≤ ε) :
    (Erdos886Divisors n ε 1).card ≤ 1 :=
  Erdos886.card_erdos886Divisors_le_one_of_quarter_le n ε hε

/-- Unconditional eventual boundedness (`K = 1`) for the main `erdos_886` quantifier across the
entire regime `ε ≥ 1/4`: for every `ε ≥ 1/4`, there exists `K : ℕ` (`K = 1`) such that eventually
`(Erdos886Divisors n ε 1).card ≤ K`. -/
theorem erdos_886_of_quarter_le (ε : ℝ) (hε : 1 / 4 ≤ ε) :
    ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K :=
  Erdos886.erdos_886_of_quarter_le ε hε

/-- Exact bidirectional equivalence reducing the open `erdos_886` problem in
`FormalConjectures.ErdosProblems.«886»` to the critical open parameter window `0 < ε < 1/4`. -/
theorem erdos_886_iff_forall_pos_lt_quarter :
    (∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K) ↔
      (∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K) :=
  Erdos886.erdos_886_iff_forall_pos_lt_quarter

/-- Division-free hyperbolic sum identity for any divisor `d ∈ n.divisors`:
`(d : ℝ) * (d + n / d - 2 * n^{1/2}) = (d - n^{1/2})^2`, relating the quadratic excess of `d`
above `n^{1/2}` to the linear excess of the integer complementary-divisor sum `d + n / d` above
`2 n^{1/2}`. -/
theorem complementary_divisor_hyperbolic_identity (n d : ℕ) (hd : d ∈ Nat.divisors n) :
    (d : ℝ) * ((d : ℝ) + (n / d : ℕ) - 2 * (n : ℝ) ^ (1 / 2 : ℝ)) =
      ((d : ℝ) - (n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
  Erdos886.complementary_divisor_hyperbolic_identity n d hd

/-- Strict monotonicity of the integer complementary-divisor sum `d ↦ d + n / d` on divisors
at or above `n^{1/2}`: for any `d₁, d₂ ∈ n.divisors` with `n^{1/2} ≤ d₁ < d₂`,
`d₁ + n / d₁ < d₂ + n / d₂`. -/
theorem complementary_sum_strict_mono_of_ge_sqrt
    (n d₁ d₂ : ℕ) (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂) :
    d₁ + n / d₁ < d₂ + n / d₂ :=
  Erdos886.complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt

/-- Exact unweighted fifth-order hyperbolic Vandermonde determinant identity on any 6-tuple of
divisors `d₁, d₂, d₃, d₄, d₅, d₆ ∈ n.divisors`:
`d₁ * d₂ * d₃ * d₄ * d₅ * d₆ * Δ⁽⁵⁾₁₂₃₄₅₆ = n * V₆(d₁, d₂, d₃, d₄, d₅, d₆)`, where `V₆` is the
15-factor Vandermonde product `∏_{1 ≤ i < j ≤ 6} (d_j - d_i)` and `Δ⁽⁵⁾₁₂₃₄₅₆` is the integer
fifth-order hyperbolic divided-difference combination of the complementary sums `d_i + n / d_i`. -/
theorem fifth_order_hyperbolic_vandermonde_six_tuple_identity
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n) :
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
        ((d₅ : ℝ) - (d₁ : ℝ)) * ((d₆ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₁ : ℝ)) :=
  Erdos886.fifth_order_hyperbolic_vandermonde_six_tuple_identity n d₁ d₂ d₃ d₄ d₅ d₆ hd₁ hd₂ hd₃ hd₄ hd₅ hd₆

/-- Division-free 6-tuple product inequality derived from integer positivity (`Δ⁽⁵⁾₁₂₃₄₅₆ ≥ 1`) of
the fifth-order hyperbolic Vandermonde determinant: for any strictly increasing 6-tuple of divisors
`d₁ < d₂ < d₃ < d₄ < d₅ < d₆` of `n`, `d₁ * d₂ * d₃ * d₄ * d₅ * d₆ ≤ n * V₆(d₁, d₂, d₃, d₄, d₅, d₆)`. -/
theorem six_tuple_product_le_mul_full_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    d₁ * d₂ * d₃ * d₄ * d₅ * d₆ ≤
      n * (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₅ - d₄) * (d₆ - d₅) *
        (d₃ - d₁) * (d₄ - d₂) * (d₅ - d₃) * (d₆ - d₄) *
        (d₄ - d₁) * (d₅ - d₂) * (d₆ - d₃) *
        (d₅ - d₁) * (d₆ - d₂) * (d₆ - d₁) :=
  Erdos886.six_tuple_product_le_mul_full_vandermonde_of_lt n d₁ d₂ d₃ d₄ d₅ d₆ hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56

/-- Universal 6-tuple Vandermonde lower bound on `Erdos886Divisors n ε C`:
for any strictly increasing 6-tuple `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` in `Erdos886Divisors n ε C`,
`n^2 < V₆(d₁, d₂, d₃, d₄, d₅, d₆)`. -/
theorem sq_lt_full_vandermonde_of_six_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε C) (hd₆ : d₆ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    n ^ 2 <
      (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₅ - d₄) * (d₆ - d₅) *
        (d₃ - d₁) * (d₄ - d₂) * (d₅ - d₃) * (d₆ - d₄) *
        (d₄ - d₁) * (d₅ - d₂) * (d₆ - d₃) *
        (d₅ - d₁) * (d₆ - d₂) * (d₆ - d₁) :=
  Erdos886.sq_lt_full_vandermonde_of_six_mem_erdos886Divisors n d₁ d₂ d₃ d₄ d₅ d₆ ε C hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56

/-- Exact GCD / LCM-quotient factorization of the complementary-sum difference for any divisors
`n^{1/2} ≤ d₁ ≤ d₂` of `n`:
`gcd(d₁, d₂) * ((d₂ + n / d₂) - (d₁ + n / d₁)) = (d₂ - d₁) * (gcd(d₁, d₂) - n / lcm(d₁, d₂))`. -/
theorem gcd_mul_complementary_sum_diff_eq_diff_mul_gcd_sub_lcm_quotient (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) =
      (d₂ - d₁) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂) :=
  Erdos886.gcd_mul_complementary_sum_diff_eq_diff_mul_gcd_sub_lcm_quotient n d₁ d₂ hd₁ hd₂ hge hle

/-- Reduced coprime-step factorization of the complementary-sum difference for divisors
`n^{1/2} ≤ d₁ ≤ d₂` of `n`:
`(d₂ + n / d₂) - (d₁ + n / d₁) = ((d₂ - d₁) / gcd(d₁, d₂)) * (gcd(d₁, d₂) - n / lcm(d₁, d₂))`. -/
theorem complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    (d₂ + n / d₂) - (d₁ + n / d₁) =
      ((d₂ - d₁) / Nat.gcd d₁ d₂) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂) :=
  Erdos886.complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient n d₁ d₂ hd₁ hd₂ hge hle

/-- Minimal complementary-sum step forces superparticular GCD equality: whenever
`n^{1/2} ≤ d₁ < d₂` are divisors of `n` with `(d₂ + n / d₂) - (d₁ + n / d₁) = 1`, the divisor gap
equals the greatest common divisor (`d₂ - d₁ = gcd(d₁, d₂)`). -/
theorem divisor_diff_eq_gcd_of_complementary_sum_diff_eq_one (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂)
    (hstep : (d₂ + n / d₂) - (d₁ + n / d₁) = 1) :
    d₂ - d₁ = Nat.gcd d₁ d₂ :=
  Erdos886.divisor_diff_eq_gcd_of_complementary_sum_diff_eq_one n d₁ d₂ hd₁ hd₂ hge hlt hstep

/-- Complementary-divisor GCD/LCM duality: for any two divisors `d₁, d₂ ∈ n.divisors`,
the greatest common divisor of the complementary divisors `n / d₁` and `n / d₂` equals the
LCM quotient `n / lcm(d₁, d₂)` (`gcd(n / d₁, n / d₂) = n / lcm(d₁, d₂)`). -/
theorem gcd_complementary_divisors_eq_div_lcm (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    Nat.gcd (n / d₁) (n / d₂) = n / Nat.lcm d₁ d₂ :=
  Erdos886.gcd_complementary_divisors_eq_div_lcm n d₁ d₂ hd₁ hd₂

/-- Canonical four-factor coprime-cofactor decomposition of `n` for any pair of divisors
`d₁, d₂ ∈ n.divisors`:
`n = gcd(d₁, d₂) * gcd(n / d₁, n / d₂) * (d₁ / gcd(d₁, d₂)) * (d₂ / gcd(d₁, d₂))`. -/
theorem coprime_cofactor_four_factor_decomposition (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    n = Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂) * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) :=
  Erdos886.coprime_cofactor_four_factor_decomposition n d₁ d₂ hd₁ hd₂

/-- Dual complementary-divisor LCM identity: for any two divisors `d₁, d₂ ∈ n.divisors`,
`lcm(n / d₁, n / d₂) = n / gcd(d₁, d₂)`. -/
theorem lcm_complementary_divisors_eq_div_gcd (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    Nat.lcm (n / d₁) (n / d₂) = n / Nat.gcd d₁ d₂ :=
  Erdos886.lcm_complementary_divisors_eq_div_gcd n d₁ d₂ hd₁ hd₂

/-- Exact factorization of the Ruzsa complementary-sum difference into the coprime-cofactor
difference times the GCD-minus-complementary-GCD gap: for `d₁, d₂ ∈ n.divisors` with
`n^{1/2} ≤ d₁ ≤ d₂`,
`(d₂ + n / d₂) - (d₁ + n / d₁) = (d₂ / gcd(d₁, d₂) - d₁ / gcd(d₁, d₂)) * (gcd(d₁, d₂) - gcd(n / d₁, n / d₂))`. -/
theorem complementary_sum_diff_eq_coprime_cofactor_diff_mul_gcd_diff (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    (d₂ + n / d₂) - (d₁ + n / d₁) =
      (d₂ / Nat.gcd d₁ d₂ - d₁ / Nat.gcd d₁ d₂) *
        (Nat.gcd d₁ d₂ - Nat.gcd (n / d₁) (n / d₂)) :=
  Erdos886.complementary_sum_diff_eq_coprime_cofactor_diff_mul_gcd_diff n d₁ d₂ hd₁ hd₂ hge hle

/-- Double-oblong factorization at a minimal Ruzsa complementary-sum step: whenever
`n^{1/2} ≤ d₁ < d₂` are divisors of `n` with `(d₂ + n / d₂) - (d₁ + n / d₁) = 1`, both the
coprime-cofactor gap and the GCD-to-complementary-GCD gap equal `1`, forcing `n` to factor as the
product of two oblong numbers:
`n = (gcd(n / d₁, n / d₂) + 1) * gcd(n / d₁, n / d₂) * (d₁ / gcd(d₁, d₂)) * (d₁ / gcd(d₁, d₂) + 1)`. -/
theorem double_oblong_factorization_of_complementary_sum_diff_eq_one (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂)
    (hstep : (d₂ + n / d₂) - (d₁ + n / d₁) = 1) :
    d₂ / Nat.gcd d₁ d₂ = d₁ / Nat.gcd d₁ d₂ + 1 ∧
    Nat.gcd d₁ d₂ = Nat.gcd (n / d₁) (n / d₂) + 1 ∧
    n / d₁ - n / d₂ = Nat.gcd (n / d₁) (n / d₂) ∧
    n = (Nat.gcd (n / d₁) (n / d₂) + 1) * Nat.gcd (n / d₁) (n / d₂) *
      (d₁ / Nat.gcd d₁ d₂) * (d₁ / Nat.gcd d₁ d₂ + 1) :=
  Erdos886.double_oblong_factorization_of_complementary_sum_diff_eq_one n d₁ d₂ hd₁ hd₂ hge hlt hstep

/-- Finset-level multi-divisor LCM divisibility: for every `n : ℕ` and all `ε, C : ℝ`,
the joint least common multiple `(Erdos886Divisors n ε C).lcm id` divides `n`. -/
theorem finset_lcm_erdos886Divisors_dvd (n : ℕ) (ε C : ℝ) :
    (Erdos886Divisors n ε C).lcm id ∣ n :=
  Erdos886.finset_lcm_erdos886Divisors_dvd n ε C

/-- Pairwise non-coprimality of near-square divisors: any two distinct divisors `d₁ < d₂` in
`Erdos886Divisors n ε C` share a common factor `gcd(d₁, d₂) ≥ 2` (since `1 ≤ n / lcm(d₁, d₂) < gcd(d₁, d₂)`). -/
theorem two_le_gcd_of_mem_erdos886Divisors_of_lt (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    2 ≤ Nat.gcd d₁ d₂ :=
  Erdos886.two_le_gcd_of_mem_erdos886Divisors_of_lt n d₁ d₂ ε C hd₁ hd₂ hlt

/-- GCD product and half-divisor upper bounds for `d₁ < d₂` in `Erdos886Divisors n ε C`
(`0 ≤ ε`, `C ≤ 1`): because `d₁ ∤ d₂` forces `2 ≤ d₁ / gcd(d₁, d₂) < 3 ≤ d₂ / gcd(d₁, d₂)`,
`6 * (gcd(d₁, d₂) * gcd(n / d₁, n / d₂)) ≤ n` and `2 * gcd(d₁, d₂) ≤ d₁`. -/
theorem six_mul_gcd_mul_complementary_gcd_le_of_mem_erdos886Divisors (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hε : 0 ≤ ε) (hC : C ≤ 1)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    6 * (Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂)) ≤ n ∧
    2 * Nat.gcd d₁ d₂ ≤ d₁ :=
  Erdos886.six_mul_gcd_mul_complementary_gcd_le_of_mem_erdos886Divisors n d₁ d₂ ε C hε hC hd₁ hd₂ hlt

/-- Exact four-term `p`-adic valuation decomposition of `n` across any two divisors
`d₁, d₂ ∈ n.divisors`:
`padicValNat p n = padicValNat p (gcd(d₁, d₂)) + padicValNat p (gcd(n / d₁, n / d₂)) + padicValNat p (d₁ / gcd(d₁, d₂)) + padicValNat p (d₂ / gcd(d₁, d₂))`. -/
theorem padicValNat_coprime_cofactor_four_term_sum (p n d₁ d₂ : ℕ) [Fact p.Prime]
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    padicValNat p n =
      padicValNat p (Nat.gcd d₁ d₂) +
      padicValNat p (Nat.gcd (n / d₁) (n / d₂)) +
      padicValNat p (d₁ / Nat.gcd d₁ d₂) +
      padicValNat p (d₂ / Nat.gcd d₁ d₂) :=
  Erdos886.padicValNat_coprime_cofactor_four_term_sum p n d₁ d₂ hd₁ hd₂

/-- Unconditional prime-power resolution across all `ε ≥ 0`: for every prime `p`, every exponent
`m : ℕ`, and every `ε ≥ 0`, `(Erdos886Divisors (p ^ m) ε 1).card ≤ 1`. -/
theorem card_erdos886Divisors_prime_pow_le_one_of_nonneg (p m : ℕ) (hp : Nat.Prime p)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (Erdos886Divisors (p ^ m) ε 1).card ≤ 1 :=
  Erdos886.card_erdos886Divisors_prime_pow_le_one_of_nonneg p m hp ε hε

/-- Top-down conditional reduction of `erdos_886` in `FormalConjectures.ErdosProblems.«886»`
via the coprime-cofactor / complementary-GCD factorization: if for every `0 < ε < 1/4` there exists
`K : ℕ` such that eventually for all `a ≤ b` in `Erdos886Divisors n ε 1`,
`(b / gcd(a, b) - a / gcd(a, b)) * (gcd(a, b) - gcd(n / a, n / b)) ≤ K`, then
`∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K`. -/
theorem erdos_886_of_eventual_coprime_cofactor_and_complementary_gcd_gap_bound
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ K : ℕ, ∀ᶠ n in Filter.atTop,
        ∀ a ∈ Erdos886Divisors n ε 1, ∀ b ∈ Erdos886Divisors n ε 1, a ≤ b →
          (b / Nat.gcd a b - a / Nat.gcd a b) *
            (Nat.gcd a b - Nat.gcd (n / a) (n / b)) ≤ K) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K :=
  Erdos886.erdos_886_of_eventual_coprime_cofactor_and_complementary_gcd_gap_bound hbound

end Erdos886.Palomar

end
