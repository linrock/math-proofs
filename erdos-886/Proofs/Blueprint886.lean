module

/-
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

public import Mathlib
public import Erdos886Unified435
public import SixTupleHyperbolicDeterminantsAndDivisorDifferenceGCD886

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

/-!
# Erdős Problem #886: Coprime Cofactor Decomposition, LCM Divisibility, and Prime-Power Valuation Constraints

This module extends `Erdos886Unified435` and `SixTupleHyperbolicDeterminantsAndDivisorDifferenceGCD886`
with 39 theorems (zero `sorry`, zero `admit`, zero `native_decide`, foundational axioms only):

1. **Coprime Cofactor Factorization & Complementary-Divisor GCD/LCM Duality:**
   - `gcd_mul_div_gcd_left`, `gcd_mul_div_gcd_right`, `coprime_div_gcd_of_mem_divisors`
   - `lcm_eq_mul_div_gcd_right`, `lcm_eq_mul_div_gcd_left`, `lcm_eq_gcd_mul_div_gcd_mul_div_gcd`
   - `complementary_divisor_left_eq_lcm_quotient_mul_coprime_cofactor` and
     `complementary_divisor_right_eq_lcm_quotient_mul_coprime_cofactor`:
     $n / d_1 = (n / \mathrm{lcm}(d_1, d_2)) \cdot (d_2 / \gcd(d_1, d_2))$ and
     $n / d_2 = (n / \mathrm{lcm}(d_1, d_2)) \cdot (d_1 / \gcd(d_1, d_2))$
   - `gcd_complementary_divisors_eq_div_lcm` and `lcm_complementary_divisors_eq_div_gcd`:
     $\gcd(n / d_1, n / d_2) = n / \mathrm{lcm}(d_1, d_2)$ and
     $\mathrm{lcm}(n / d_1, n / d_2) = n / \gcd(d_1, d_2)$
   - `coprime_cofactor_four_factor_decomposition`:
     $$n = \gcd(d_1, d_2) \cdot \gcd(n / d_1, n / d_2) \cdot (d_1 / \gcd(d_1, d_2)) \cdot (d_2 / \gcd(d_1, d_2))$$
   - `div_gcd_sub_div_gcd_eq_sub_div_gcd`,
     `complementary_sum_diff_eq_coprime_cofactor_diff_mul_gcd_diff`,
     `complementary_quotient_diff_eq_coprime_cofactor_diff_mul_complementary_gcd`,
     `complementary_gcd_lt_gcd_of_ge_sqrt`
   - `double_oblong_factorization_of_complementary_sum_diff_eq_one`:
     Every minimal Ruzsa complementary-sum step $(d_2 + n/d_2) - (d_1 + n/d_1) = 1$ forces
     $n = (g' + 1) g' u (u + 1)$ where $g' = \gcd(n/d_1, n/d_2)$ and $u = d_1 / \gcd(d_1, d_2)$.

2. **Multi-Divisor LCM Divisibility (`lcm(d₁, d₂, d₃) ∣ n`) & Pairwise Non-Coprimality:**
   - `three_divisor_lcm_dvd_of_mem_divisors` and `three_divisor_lcm_le_of_mem_divisors`:
     $\mathrm{lcm}(\mathrm{lcm}(d_1, d_2), d_3) \mid n$ and $\mathrm{lcm}(d_1, \mathrm{lcm}(d_2, d_3)) \mid n$
   - `four_divisor_lcm_dvd_of_mem_divisors`
   - `finset_lcm_dvd_of_subset_divisors` and `finset_lcm_erdos886Divisors_dvd`:
     $(\mathrm{Erdos886Divisors}\ n\ \varepsilon\ C).\mathrm{lcm}\ \mathrm{id} \mid n$
   - `two_le_gcd_of_mem_erdos886Divisors_of_lt` and `not_coprime_of_mem_erdos886Divisors_of_ne`:
     For any two distinct $d_1, d_2 \in \mathrm{Erdos886Divisors}\ n\ \varepsilon\ C$,
     $\gcd(d_1, d_2) \ge 2$ and $\neg \mathrm{Coprime}\ d_1\ d_2$.

3. **Prime-Power Valuation (`padicValNat`) & Pairwise-Difference GCD Constraints:**
   - `not_dvd_of_mem_erdos886Divisors_of_lt`:
     For $0 \le \varepsilon$ and $C \le 1$, no divisor in $\mathrm{Erdos886Divisors}\ n\ \varepsilon\ C$
     divides a strictly larger divisor in $\mathrm{Erdos886Divisors}\ n\ \varepsilon\ C$.
   - `two_le_div_gcd_and_three_le_div_gcd_of_mem_erdos886Divisors` and
     `six_mul_gcd_mul_complementary_gcd_le_of_mem_erdos886Divisors`:
     $2 \le d_1 / \gcd(d_1, d_2) < 3 \le d_2 / \gcd(d_1, d_2)$ and
     $6 \gcd(d_1, d_2) \gcd(n/d_1, n/d_2) \le n$.
   - `exists_prime_dvd_common_and_diff_of_mem_erdos886Divisors` and
     `exists_distinct_primes_dvd_coprime_cofactors_of_mem_erdos886Divisors`
   - `pow_dvd_right_and_gcd_of_pow_dvd_left_and_diff`
   - `padicValNat_divisor_add_complementary_eq`,
     `padicValNat_coprime_cofactor_four_term_sum`,
     `padicValNat_coprime_cofactor_eq_zero_or_eq_zero`
   - `card_erdos886Divisors_prime_pow_le_one_of_nonneg`:
     Unconditional proof that $(\mathrm{Erdos886Divisors}\ (p^m)\ \varepsilon\ 1).\mathrm{card} \le 1$
     for every prime $p$, $m \in \mathbb{N}$, and $\varepsilon \ge 0$.

4. **Direct Connections to `FormalConjectures.ErdosProblems.«886»` & Controls:**
   - `erdos_886.variants.rosenfeld_infinite` and `erdos_886.variants.rosenfeld_bound`
   - `erdos_886_iff_forall_pos_lt_quarter`
   - `erdos_886_of_eventual_coprime_cofactor_and_complementary_gcd_gap_bound`
   - `erdos_886_of_eventual_separate_coprime_cofactor_and_gcd_gap_bounds`
   - `positive_control_coprime_cofactor_and_lcm_witnesses_720720_471240_85680`
-/

namespace Erdos886

/-! ## Section 1: Coprime Cofactor Factorization & Complementary-Divisor GCD/LCM Duality -/

/-- Exact left GCD cofactor recovery: `gcd(d₁, d₂) * (d₁ / gcd(d₁, d₂)) = d₁`. -/
theorem gcd_mul_div_gcd_left (d₁ d₂ : ℕ) :
    Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) = d₁ :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left d₁ d₂)

/-- Exact right GCD cofactor recovery: `gcd(d₁, d₂) * (d₂ / gcd(d₁, d₂)) = d₂`. -/
theorem gcd_mul_div_gcd_right (d₁ d₂ : ℕ) :
    Nat.gcd d₁ d₂ * (d₂ / Nat.gcd d₁ d₂) = d₂ :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right d₁ d₂)

/-- For any divisor `d₁ ∈ n.divisors` and any `d₂ : ℕ`, the reduced cofactors
`d₁ / gcd(d₁, d₂)` and `d₂ / gcd(d₁, d₂)` are coprime. -/
theorem coprime_div_gcd_of_mem_divisors (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) :
    Nat.Coprime (d₁ / Nat.gcd d₁ d₂) (d₂ / Nat.gcd d₁ d₂) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left d₂ (Nat.pos_of_mem_divisors hd₁))

/-- Right coprime-cofactor expression for the least common multiple:
`lcm(d₁, d₂) = d₁ * (d₂ / gcd(d₁, d₂))`. -/
theorem lcm_eq_mul_div_gcd_right (d₁ d₂ : ℕ) :
    Nat.lcm d₁ d₂ = d₁ * (d₂ / Nat.gcd d₁ d₂) := by
  rcases eq_or_ne (Nat.gcd d₁ d₂) 0 with h0 | hne
  · rw [(Nat.gcd_eq_zero_iff.mp h0).1, Nat.lcm_zero_left, zero_mul]
  · have hpos : 0 < Nat.gcd d₁ d₂ := Nat.pos_of_ne_zero hne
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc
      Nat.gcd d₁ d₂ * Nat.lcm d₁ d₂ = d₁ * d₂ := Nat.gcd_mul_lcm d₁ d₂
      _ = d₁ * (Nat.gcd d₁ d₂ * (d₂ / Nat.gcd d₁ d₂)) := by rw [gcd_mul_div_gcd_right]
      _ = Nat.gcd d₁ d₂ * (d₁ * (d₂ / Nat.gcd d₁ d₂)) := by ring

/-- Left coprime-cofactor expression for the least common multiple:
`lcm(d₁, d₂) = d₂ * (d₁ / gcd(d₁, d₂))`. -/
theorem lcm_eq_mul_div_gcd_left (d₁ d₂ : ℕ) :
    Nat.lcm d₁ d₂ = d₂ * (d₁ / Nat.gcd d₁ d₂) := by
  rw [Nat.lcm_comm, lcm_eq_mul_div_gcd_right, Nat.gcd_comm]

/-- Three-factor decomposition of the least common multiple into GCD and coprime cofactors:
`lcm(d₁, d₂) = gcd(d₁, d₂) * (d₁ / gcd(d₁, d₂)) * (d₂ / gcd(d₁, d₂))`. -/
theorem lcm_eq_gcd_mul_div_gcd_mul_div_gcd (d₁ d₂ : ℕ) :
    Nat.lcm d₁ d₂ = Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by
  rw [gcd_mul_div_gcd_left, ← lcm_eq_mul_div_gcd_right]

/-- For any two divisors `d₁, d₂ ∈ n.divisors`, the complementary divisor `n / d₁` factors as
`(n / lcm(d₁, d₂)) * (d₂ / gcd(d₁, d₂))`. -/
theorem complementary_divisor_left_eq_lcm_quotient_mul_coprime_cofactor (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    n / d₁ = (n / Nat.lcm d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by
  have hd1_pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  have hlcm_dvd : Nat.lcm d₁ d₂ ∣ n := lcm_dvd_of_mem_divisors n d₁ d₂ hd₁ hd₂
  have hd1_dvd : d₁ ∣ n := (Nat.mem_divisors.mp hd₁).1
  apply Nat.eq_of_mul_eq_mul_left hd1_pos
  calc
    d₁ * (n / d₁) = n := Nat.mul_div_cancel' hd1_dvd
    _ = Nat.lcm d₁ d₂ * (n / Nat.lcm d₁ d₂) := (Nat.mul_div_cancel' hlcm_dvd).symm
    _ = (d₁ * (d₂ / Nat.gcd d₁ d₂)) * (n / Nat.lcm d₁ d₂) := by rw [← lcm_eq_mul_div_gcd_right]
    _ = d₁ * ((n / Nat.lcm d₁ d₂) * (d₂ / Nat.gcd d₁ d₂)) := by ring

/-- For any two divisors `d₁, d₂ ∈ n.divisors`, the complementary divisor `n / d₂` factors as
`(n / lcm(d₁, d₂)) * (d₁ / gcd(d₁, d₂))`. -/
theorem complementary_divisor_right_eq_lcm_quotient_mul_coprime_cofactor (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    n / d₂ = (n / Nat.lcm d₁ d₂) * (d₁ / Nat.gcd d₁ d₂) := by
  rw [Nat.lcm_comm, Nat.gcd_comm]
  exact complementary_divisor_left_eq_lcm_quotient_mul_coprime_cofactor n d₂ d₁ hd₂ hd₁

/-- Complementary-divisor GCD/LCM duality: for any `d₁, d₂ ∈ n.divisors`,
`gcd(n / d₁, n / d₂) = n / lcm(d₁, d₂)`. -/
theorem gcd_complementary_divisors_eq_div_lcm (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    Nat.gcd (n / d₁) (n / d₂) = n / Nat.lcm d₁ d₂ := by
  rw [complementary_divisor_left_eq_lcm_quotient_mul_coprime_cofactor n d₁ d₂ hd₁ hd₂,
    complementary_divisor_right_eq_lcm_quotient_mul_coprime_cofactor n d₁ d₂ hd₁ hd₂,
    Nat.gcd_mul_left, (coprime_div_gcd_of_mem_divisors n d₁ d₂ hd₁).symm.gcd_eq_one, mul_one]

/-- Coprime cofactor four-factor decomposition of `n` for any pair of divisors `d₁, d₂ ∈ n.divisors`:
`n = gcd(d₁, d₂) * gcd(n / d₁, n / d₂) * (d₁ / gcd(d₁, d₂)) * (d₂ / gcd(d₁, d₂))`. -/
theorem coprime_cofactor_four_factor_decomposition (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    n = Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂) * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by
  have hlcm_dvd : Nat.lcm d₁ d₂ ∣ n := lcm_dvd_of_mem_divisors n d₁ d₂ hd₁ hd₂
  rw [gcd_complementary_divisors_eq_div_lcm n d₁ d₂ hd₁ hd₂]
  calc
    n = Nat.lcm d₁ d₂ * (n / Nat.lcm d₁ d₂) := (Nat.mul_div_cancel' hlcm_dvd).symm
    _ = (Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂)) * (n / Nat.lcm d₁ d₂) := by
          rw [← lcm_eq_gcd_mul_div_gcd_mul_div_gcd]
    _ = Nat.gcd d₁ d₂ * (n / Nat.lcm d₁ d₂) * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by ring

/-- Dual complementary-divisor LCM identity: for any `d₁, d₂ ∈ n.divisors`,
`lcm(n / d₁, n / d₂) = n / gcd(d₁, d₂)`. -/
theorem lcm_complementary_divisors_eq_div_gcd (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    Nat.lcm (n / d₁) (n / d₂) = n / Nat.gcd d₁ d₂ := by
  have hd1_pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  have hgcd_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd1_pos
  have hgcd_dvd_n : Nat.gcd d₁ d₂ ∣ n :=
    dvd_trans (Nat.gcd_dvd_left d₁ d₂) (Nat.mem_divisors.mp hd₁).1
  apply Nat.eq_of_mul_eq_mul_left hgcd_pos
  rw [Nat.mul_div_cancel' hgcd_dvd_n,
    complementary_divisor_left_eq_lcm_quotient_mul_coprime_cofactor n d₁ d₂ hd₁ hd₂,
    complementary_divisor_right_eq_lcm_quotient_mul_coprime_cofactor n d₁ d₂ hd₁ hd₂,
    Nat.lcm_mul_left, (coprime_div_gcd_of_mem_divisors n d₁ d₂ hd₁).symm.lcm_eq_mul]
  have h4 := coprime_cofactor_four_factor_decomposition n d₁ d₂ hd₁ hd₂
  rw [gcd_complementary_divisors_eq_div_lcm n d₁ d₂ hd₁ hd₂] at h4
  linarith

/-- The reduced divisor difference `(d₂ - d₁) / gcd(d₁, d₂)` equals the difference of coprime
cofactors `d₂ / gcd(d₁, d₂) - d₁ / gcd(d₁, d₂)`. -/
theorem div_gcd_sub_div_gcd_eq_sub_div_gcd (d₁ d₂ : ℕ) :
    (d₂ - d₁) / Nat.gcd d₁ d₂ = d₂ / Nat.gcd d₁ d₂ - d₁ / Nat.gcd d₁ d₂ := by
  rcases eq_or_ne (Nat.gcd d₁ d₂) 0 with h0 | hne
  · simp [h0]
  · have hpos : 0 < Nat.gcd d₁ d₂ := Nat.pos_of_ne_zero hne
    have hsub : d₂ - d₁ = Nat.gcd d₁ d₂ * (d₂ / Nat.gcd d₁ d₂ - d₁ / Nat.gcd d₁ d₂) := by
      rw [Nat.mul_sub_left_distrib, gcd_mul_div_gcd_right, gcd_mul_div_gcd_left]
    rw [hsub, Nat.mul_div_right _ hpos]

/-- Exact factorization of the complementary-sum difference into the coprime-cofactor difference
times the GCD-minus-complementary-GCD gap:
`(d₂ + n / d₂) - (d₁ + n / d₁) = (d₂ / gcd(d₁, d₂) - d₁ / gcd(d₁, d₂)) * (gcd(d₁, d₂) - gcd(n / d₁, n / d₂))`. -/
theorem complementary_sum_diff_eq_coprime_cofactor_diff_mul_gcd_diff (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    (d₂ + n / d₂) - (d₁ + n / d₁) =
      (d₂ / Nat.gcd d₁ d₂ - d₁ / Nat.gcd d₁ d₂) *
        (Nat.gcd d₁ d₂ - Nat.gcd (n / d₁) (n / d₂)) := by
  rw [complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient n d₁ d₂ hd₁ hd₂ hge hle,
    div_gcd_sub_div_gcd_eq_sub_div_gcd, gcd_complementary_divisors_eq_div_lcm n d₁ d₂ hd₁ hd₂]

/-- Exact factorization of the complementary-quotient drop `n / d₁ - n / d₂` into the
coprime-cofactor difference times the complementary GCD `gcd(n / d₁, n / d₂)`. -/
theorem complementary_quotient_diff_eq_coprime_cofactor_diff_mul_complementary_gcd (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    n / d₁ - n / d₂ =
      (d₂ / Nat.gcd d₁ d₂ - d₁ / Nat.gcd d₁ d₂) * Nat.gcd (n / d₁) (n / d₂) := by
  rw [gcd_complementary_divisors_eq_div_lcm n d₁ d₂ hd₁ hd₂,
    complementary_divisor_left_eq_lcm_quotient_mul_coprime_cofactor n d₁ d₂ hd₁ hd₂,
    complementary_divisor_right_eq_lcm_quotient_mul_coprime_cofactor n d₁ d₂ hd₁ hd₂,
    ← Nat.mul_sub_left_distrib, mul_comm]

/-- For divisors `n^{1/2} ≤ d₁ < d₂` of `n`, the complementary GCD is strictly smaller than
the divisor GCD: `gcd(n / d₁, n / d₂) < gcd(d₁, d₂)`. -/
theorem complementary_gcd_lt_gcd_of_ge_sqrt (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂) :
    Nat.gcd (n / d₁) (n / d₂) < Nat.gcd d₁ d₂ := by
  rw [gcd_complementary_divisors_eq_div_lcm n d₁ d₂ hd₁ hd₂]
  exact lcm_quotient_lt_gcd_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hge hlt

/-- Double-oblong factorization at a minimal Ruzsa step: whenever `n^{1/2} ≤ d₁ < d₂` are divisors
of `n` with `(d₂ + n / d₂) - (d₁ + n / d₁) = 1`, both the coprime-cofactor gap and the
GCD-to-complementary-GCD gap equal `1`, forcing `n` to factor as the product of two oblong numbers:
`n = (gcd(n / d₁, n / d₂) + 1) * gcd(n / d₁, n / d₂) * (d₁ / gcd(d₁, d₂)) * (d₁ / gcd(d₁, d₂) + 1)`. -/
theorem double_oblong_factorization_of_complementary_sum_diff_eq_one (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂)
    (hstep : (d₂ + n / d₂) - (d₁ + n / d₁) = 1) :
    d₂ / Nat.gcd d₁ d₂ = d₁ / Nat.gcd d₁ d₂ + 1 ∧
    Nat.gcd d₁ d₂ = Nat.gcd (n / d₁) (n / d₂) + 1 ∧
    n / d₁ - n / d₂ = Nat.gcd (n / d₁) (n / d₂) ∧
    n = (Nat.gcd (n / d₁) (n / d₂) + 1) * Nat.gcd (n / d₁) (n / d₂) *
      (d₁ / Nat.gcd d₁ d₂) * (d₁ / Nat.gcd d₁ d₂ + 1) := by
  have hprod := complementary_sum_diff_eq_coprime_cofactor_diff_mul_gcd_diff n d₁ d₂ hd₁ hd₂ hge (le_of_lt hlt)
  rw [hstep] at hprod
  have hu_eq1 : d₂ / Nat.gcd d₁ d₂ - d₁ / Nat.gcd d₁ d₂ = 1 :=
    Nat.eq_one_of_mul_eq_one_right hprod.symm
  have hg_eq1 : Nat.gcd d₁ d₂ - Nat.gcd (n / d₁) (n / d₂) = 1 :=
    Nat.eq_one_of_mul_eq_one_left hprod.symm
  have h1 : d₂ / Nat.gcd d₁ d₂ = d₁ / Nat.gcd d₁ d₂ + 1 := by omega
  have h2 : Nat.gcd d₁ d₂ = Nat.gcd (n / d₁) (n / d₂) + 1 := by omega
  have h3 : n / d₁ - n / d₂ = Nat.gcd (n / d₁) (n / d₂) := by
    rw [complementary_quotient_diff_eq_coprime_cofactor_diff_mul_complementary_gcd n d₁ d₂ hd₁ hd₂,
      hu_eq1, one_mul]
  have h4 : n = (Nat.gcd (n / d₁) (n / d₂) + 1) * Nat.gcd (n / d₁) (n / d₂) *
      (d₁ / Nat.gcd d₁ d₂) * (d₁ / Nat.gcd d₁ d₂ + 1) := by
    have hdecomp := coprime_cofactor_four_factor_decomposition n d₁ d₂ hd₁ hd₂
    rw [h1] at hdecomp
    nth_rw 1 [h2] at hdecomp
    exact hdecomp
  exact ⟨h1, h2, h3, h4⟩

/-! ## Section 2: Multi-Divisor LCM Divisibility (`lcm(d₁, d₂, d₃) ∣ n`) & Pairwise Non-Coprimality -/

/-- Three-divisor LCM divisibility: for any three divisors `d₁, d₂, d₃ ∈ n.divisors`,
both `lcm(lcm(d₁, d₂), d₃) ∣ n` and `lcm(d₁, lcm(d₂, d₃)) ∣ n`. -/
theorem three_divisor_lcm_dvd_of_mem_divisors (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n) :
    Nat.lcm (Nat.lcm d₁ d₂) d₃ ∣ n ∧ Nat.lcm d₁ (Nat.lcm d₂ d₃) ∣ n :=
  ⟨Nat.lcm_dvd (lcm_dvd_of_mem_divisors n d₁ d₂ hd₁ hd₂) (Nat.mem_divisors.mp hd₃).1,
   Nat.lcm_dvd (Nat.mem_divisors.mp hd₁).1 (lcm_dvd_of_mem_divisors n d₂ d₃ hd₂ hd₃)⟩

/-- Three-divisor LCM upper bound: for any three divisors `d₁, d₂, d₃ ∈ n.divisors`,
`1 ≤ lcm(lcm(d₁, d₂), d₃)` and `lcm(lcm(d₁, d₂), d₃) ≤ n`. -/
theorem three_divisor_lcm_le_of_mem_divisors (n d₁ d₂ d₃ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n) :
    1 ≤ Nat.lcm (Nat.lcm d₁ d₂) d₃ ∧ Nat.lcm (Nat.lcm d₁ d₂) d₃ ≤ n := by
  have hd1_pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  have hd2_pos : 0 < d₂ := Nat.pos_of_mem_divisors hd₂
  have hd3_pos : 0 < d₃ := Nat.pos_of_mem_divisors hd₃
  have hlcm12_pos : 0 < Nat.lcm d₁ d₂ := Nat.lcm_pos hd1_pos hd2_pos
  have hlcm123_pos : 0 < Nat.lcm (Nat.lcm d₁ d₂) d₃ := Nat.lcm_pos hlcm12_pos hd3_pos
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
  have hdvd := (three_divisor_lcm_dvd_of_mem_divisors n d₁ d₂ d₃ hd₁ hd₂ hd₃).1
  exact ⟨hlcm123_pos, Nat.le_of_dvd hn_pos hdvd⟩

/-- Four-divisor LCM divisibility: for any four divisors `d₁, d₂, d₃, d₄ ∈ n.divisors`,
`lcm(lcm(lcm(d₁, d₂), d₃), d₄) ∣ n`. -/
theorem four_divisor_lcm_dvd_of_mem_divisors (n d₁ d₂ d₃ d₄ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hd₃ : d₃ ∈ Nat.divisors n) (hd₄ : d₄ ∈ Nat.divisors n) :
    Nat.lcm (Nat.lcm (Nat.lcm d₁ d₂) d₃) d₄ ∣ n :=
  Nat.lcm_dvd (three_divisor_lcm_dvd_of_mem_divisors n d₁ d₂ d₃ hd₁ hd₂ hd₃).1
    (Nat.mem_divisors.mp hd₄).1

/-- Finset-level multi-divisor LCM divisibility: for any finite subset `S ⊆ n.divisors`,
`S.lcm id ∣ n`. -/
theorem finset_lcm_dvd_of_subset_divisors (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Nat.divisors n) :
    S.lcm id ∣ n := by
  rw [Finset.lcm_dvd_iff]
  intro d hd
  exact (Nat.mem_divisors.mp (hS hd)).1

/-- The joint LCM of all near-square divisors in `Erdos886Divisors n ε C` divides `n`. -/
theorem finset_lcm_erdos886Divisors_dvd (n : ℕ) (ε C : ℝ) :
    (Erdos886Divisors n ε C).lcm id ∣ n := by
  apply finset_lcm_dvd_of_subset_divisors
  intro d hd
  exact ((mem_erdos886Divisors_iff n d ε C).mp hd).1

/-- Any two distinct divisors `d₁ < d₂` in `Erdos886Divisors n ε C` share a common factor
`gcd(d₁, d₂) ≥ 2`. -/
theorem two_le_gcd_of_mem_erdos886Divisors_of_lt (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    2 ≤ Nat.gcd d₁ d₂ := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hlt_gcd := lcm_quotient_lt_gcd_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt
  have hlcm_dvd := lcm_dvd_of_mem_divisors n d₁ d₂ hm1.1 hm2.1
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm1.1).2
  have hlcm_pos : 0 < Nat.lcm d₁ d₂ :=
    Nat.lcm_pos (Nat.pos_of_mem_divisors hm1.1) (Nat.pos_of_mem_divisors hm2.1)
  have hq_pos : 1 ≤ n / Nat.lcm d₁ d₂ :=
    Nat.div_pos (Nat.le_of_dvd hn_pos hlcm_dvd) hlcm_pos
  omega

/-- No two distinct elements of `Erdos886Divisors n ε C` are coprime. -/
theorem not_coprime_of_mem_erdos886Divisors_of_ne (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hne : d₁ ≠ d₂) :
    ¬ Nat.Coprime d₁ d₂ := by
  intro hcop
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h2 := two_le_gcd_of_mem_erdos886Divisors_of_lt n d₁ d₂ ε C hd₁ hd₂ hlt
    rw [hcop.gcd_eq_one] at h2
    omega
  · have h2 := two_le_gcd_of_mem_erdos886Divisors_of_lt n d₂ d₁ ε C hd₂ hd₁ hgt
    rw [hcop.symm.gcd_eq_one] at h2
    omega

/-! ## Section 3: Prime-Power Valuation (`padicValNat`) & Pairwise-Difference GCD Constraints -/

/-- Anti-chain / non-divisibility property on `Erdos886Divisors n ε C` for `0 ≤ ε` and `C ≤ 1`:
no element `d₁` divides a strictly larger element `d₂` in `Erdos886Divisors n ε C`. -/
theorem not_dvd_of_mem_erdos886Divisors_of_lt (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hε : 0 ≤ ε) (hC : C ≤ 1)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    ¬ (d₁ ∣ d₂) := by
  intro hdvd
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  rcases hdvd with ⟨k, rfl⟩
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hlt
    · simp at hlt
    · omega
  have h2d1_le : 2 * (d₁ : ℝ) ≤ ((d₁ * k : ℕ) : ℝ) := by
    have hnat : 2 * d₁ ≤ d₁ * k := by
      calc 2 * d₁ = d₁ * 2 := mul_comm 2 d₁
      _ ≤ d₁ * k := Nat.mul_le_mul_left d₁ hk2
    exact_mod_cast hnat
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hm1.1).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow_le : (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (1 / 2 - ε) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hmul_le : C * (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      C * (n : ℝ) ^ (1 / 2 - ε) ≤ 1 * (n : ℝ) ^ (1 / 2 - ε) :=
        mul_le_mul_of_nonneg_right hC hpow_nonneg
      _ = (n : ℝ) ^ (1 / 2 - ε) := one_mul _
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := hpow_le
  have hlow1 := hm1.2.1
  have hhigh2 := hm2.2.2
  linarith

/-- Coprime cofactor lower bounds for `d₁ < d₂` in `Erdos886Divisors n ε C` (`0 ≤ ε`, `C ≤ 1`):
`2 ≤ d₁ / gcd(d₁, d₂)`, `3 ≤ d₂ / gcd(d₁, d₂)`, and
`6 ≤ (d₁ / gcd(d₁, d₂)) * (d₂ / gcd(d₁, d₂))`. -/
theorem two_le_div_gcd_and_three_le_div_gcd_of_mem_erdos886Divisors (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hε : 0 ≤ ε) (hC : C ≤ 1)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    2 ≤ d₁ / Nat.gcd d₁ d₂ ∧
    3 ≤ d₂ / Nat.gcd d₁ d₂ ∧
    6 ≤ (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hd1_pos : 0 < d₁ := Nat.pos_of_mem_divisors hm1.1
  have hgcd_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd1_pos
  have hu1_pos : 1 ≤ d₁ / Nat.gcd d₁ d₂ :=
    Nat.div_pos (Nat.le_of_dvd hd1_pos (Nat.gcd_dvd_left d₁ d₂)) hgcd_pos
  have hu1_ne1 : d₁ / Nat.gcd d₁ d₂ ≠ 1 := by
    intro h1
    have hg_eq : Nat.gcd d₁ d₂ = d₁ := by
      have hmul := gcd_mul_div_gcd_left d₁ d₂
      rw [h1, mul_one] at hmul
      exact hmul
    have hdvd : d₁ ∣ d₂ := hg_eq ▸ Nat.gcd_dvd_right d₁ d₂
    exact not_dvd_of_mem_erdos886Divisors_of_lt n d₁ d₂ ε C hε hC hd₁ hd₂ hlt hdvd
  have hu1_ge2 : 2 ≤ d₁ / Nat.gcd d₁ d₂ := by omega
  have hu1_lt_u2 : d₁ / Nat.gcd d₁ d₂ < d₂ / Nat.gcd d₁ d₂ := by
    by_contra hle
    have hmul_le : Nat.gcd d₁ d₂ * (d₂ / Nat.gcd d₁ d₂) ≤ Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) :=
      Nat.mul_le_mul_left (Nat.gcd d₁ d₂) (Nat.le_of_not_lt hle)
    rw [gcd_mul_div_gcd_right, gcd_mul_div_gcd_left] at hmul_le
    omega
  have hu2_ge3 : 3 ≤ d₂ / Nat.gcd d₁ d₂ := by omega
  have hprod_ge6 : 6 ≤ (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by nlinarith
  exact ⟨hu1_ge2, hu2_ge3, hprod_ge6⟩

/-- GCD product and half-divisor upper bounds for `d₁ < d₂` in `Erdos886Divisors n ε C`
(`0 ≤ ε`, `C ≤ 1`): `6 * (gcd(d₁, d₂) * gcd(n / d₁, n / d₂)) ≤ n` and `2 * gcd(d₁, d₂) ≤ d₁`. -/
theorem six_mul_gcd_mul_complementary_gcd_le_of_mem_erdos886Divisors (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hε : 0 ≤ ε) (hC : C ≤ 1)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    6 * (Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂)) ≤ n ∧
    2 * Nat.gcd d₁ d₂ ≤ d₁ := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  obtain ⟨hu1, _, hprod6⟩ :=
    two_le_div_gcd_and_three_le_div_gcd_of_mem_erdos886Divisors n d₁ d₂ ε C hε hC hd₁ hd₂ hlt
  have h4 := coprime_cofactor_four_factor_decomposition n d₁ d₂ hm1.1 hm2.1
  have hle1 : 6 * (Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂)) ≤ n := by
    calc
      6 * (Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂))
        = (Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂)) * 6 := mul_comm _ _
      _ ≤ (Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂)) *
            ((d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂)) :=
          Nat.mul_le_mul_left _ hprod6
      _ = Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂) *
            (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) := by ring
      _ = n := h4.symm
  have hle2 : 2 * Nat.gcd d₁ d₂ ≤ d₁ := by
    calc
      2 * Nat.gcd d₁ d₂ = Nat.gcd d₁ d₂ * 2 := mul_comm _ _
      _ ≤ Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) := Nat.mul_le_mul_left _ hu1
      _ = d₁ := gcd_mul_div_gcd_left d₁ d₂
  exact ⟨hle1, hle2⟩

/-- For any `d₁ < d₂` in `Erdos886Divisors n ε C`, there exists a prime `p` dividing `d₁`, `d₂`,
and `d₂ - d₁`, with `p^2 ∣ d₁ * d₂`. -/
theorem exists_prime_dvd_common_and_diff_of_mem_erdos886Divisors (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ d₁ ∧ p ∣ d₂ ∧ p ∣ (d₂ - d₁) ∧ p ^ 2 ∣ d₁ * d₂ := by
  have h2 := two_le_gcd_of_mem_erdos886Divisors_of_lt n d₁ d₂ ε C hd₁ hd₂ hlt
  have hne1 : Nat.gcd d₁ d₂ ≠ 1 := by omega
  refine ⟨(Nat.gcd d₁ d₂).minFac, Nat.minFac_prime hne1, ?_, ?_, ?_, ?_⟩
  · exact dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left d₁ d₂)
  · exact dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right d₁ d₂)
  · exact Nat.dvd_sub
      (dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right d₁ d₂))
      (dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left d₁ d₂))
  · rw [sq]
    exact mul_dvd_mul
      (dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left d₁ d₂))
      (dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right d₁ d₂))

/-- For any `d₁ < d₂` in `Erdos886Divisors n ε C` (`0 ≤ ε`, `C ≤ 1`), there exist two distinct
primes `p ≠ q` such that `p ∣ (d₁ / gcd(d₁, d₂))`, `q ∣ (d₂ / gcd(d₁, d₂))`,
`p ∣ (n / d₂)`, and `q ∣ (n / d₁)`. -/
theorem exists_distinct_primes_dvd_coprime_cofactors_of_mem_erdos886Divisors
    (n d₁ d₂ : ℕ) (ε C : ℝ) (hε : 0 ≤ ε) (hC : C ≤ 1)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
      p ∣ (d₁ / Nat.gcd d₁ d₂) ∧ q ∣ (d₂ / Nat.gcd d₁ d₂) ∧
      p ∣ (n / d₂) ∧ q ∣ (n / d₁) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  obtain ⟨hu1, hu2, _⟩ :=
    two_le_div_gcd_and_three_le_div_gcd_of_mem_erdos886Divisors n d₁ d₂ ε C hε hC hd₁ hd₂ hlt
  set u₁ := d₁ / Nat.gcd d₁ d₂
  set u₂ := d₂ / Nat.gcd d₁ d₂
  have hp_prime : Nat.Prime u₁.minFac := Nat.minFac_prime (by omega)
  have hq_prime : Nat.Prime u₂.minFac := Nat.minFac_prime (by omega)
  have hp_dvd : u₁.minFac ∣ u₁ := Nat.minFac_dvd u₁
  have hq_dvd : u₂.minFac ∣ u₂ := Nat.minFac_dvd u₂
  have hcop : Nat.Coprime u₁ u₂ := coprime_div_gcd_of_mem_divisors n d₁ d₂ hm1.1
  have hpq_ne : u₁.minFac ≠ u₂.minFac := by
    intro heq
    have hq_dvd_u1 : u₁.minFac ∣ u₂ := heq ▸ hq_dvd
    have hdvd1 : u₁.minFac ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hp_dvd hq_dvd_u1
    exact hp_prime.not_dvd_one hdvd1
  have hp_dvd_nd2 : u₁.minFac ∣ (n / d₂) := by
    rw [complementary_divisor_right_eq_lcm_quotient_mul_coprime_cofactor n d₁ d₂ hm1.1 hm2.1]
    exact dvd_mul_of_dvd_right hp_dvd _
  have hq_dvd_nd1 : u₂.minFac ∣ (n / d₁) := by
    rw [complementary_divisor_left_eq_lcm_quotient_mul_coprime_cofactor n d₁ d₂ hm1.1 hm2.1]
    exact dvd_mul_of_dvd_right hq_dvd _
  exact ⟨u₁.minFac, u₂.minFac, hp_prime, hq_prime, hpq_ne, hp_dvd, hq_dvd, hp_dvd_nd2, hq_dvd_nd1⟩

/-- Prime-power transfer across pairwise differences: for `d₁ ≤ d₂`, if `p^k ∣ d₁` and
`p^k ∣ (d₂ - d₁)`, then `p^k ∣ d₂`, `p^k ∣ gcd(d₁, d₂)`, and `p^(2*k) ∣ d₁ * d₂`. -/
theorem pow_dvd_right_and_gcd_of_pow_dvd_left_and_diff (p k d₁ d₂ : ℕ)
    (hle : d₁ ≤ d₂) (hd1 : p ^ k ∣ d₁) (hdiff : p ^ k ∣ (d₂ - d₁)) :
    p ^ k ∣ d₂ ∧ p ^ k ∣ Nat.gcd d₁ d₂ ∧ p ^ (2 * k) ∣ d₁ * d₂ := by
  have hd2 : p ^ k ∣ d₂ := by
    have h := dvd_add hd1 hdiff
    rwa [Nat.add_sub_of_le hle] at h
  have hgcd : p ^ k ∣ Nat.gcd d₁ d₂ := Nat.dvd_gcd hd1 hd2
  have hprod : p ^ (2 * k) ∣ d₁ * d₂ := by
    rw [two_mul, pow_add]
    exact mul_dvd_mul hd1 hd2
  exact ⟨hd2, hgcd, hprod⟩

/-- For any prime `p` and any divisor `d ∈ n.divisors`,
`padicValNat p d + padicValNat p (n / d) = padicValNat p n`. -/
theorem padicValNat_divisor_add_complementary_eq (p n d : ℕ) [Fact p.Prime]
    (hd : d ∈ Nat.divisors n) :
    padicValNat p d + padicValNat p (n / d) = padicValNat p n := by
  have hd_dvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd).2
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hnd0 : n / d ≠ 0 := by
    intro h0
    have hmul := Nat.mul_div_cancel' hd_dvd
    rw [h0, mul_zero] at hmul
    exact hn0 hmul.symm
  rw [← padicValNat.mul hd0 hnd0, Nat.mul_div_cancel' hd_dvd]

/-- Exact 4-term `p`-adic valuation decomposition of `n` across any two divisors `d₁, d₂ ∈ n.divisors`:
`padicValNat p n = padicValNat p (gcd(d₁, d₂)) + padicValNat p (gcd(n / d₁, n / d₂)) + padicValNat p (d₁ / gcd(d₁, d₂)) + padicValNat p (d₂ / gcd(d₁, d₂))`. -/
theorem padicValNat_coprime_cofactor_four_term_sum (p n d₁ d₂ : ℕ) [Fact p.Prime]
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    padicValNat p n =
      padicValNat p (Nat.gcd d₁ d₂) +
      padicValNat p (Nat.gcd (n / d₁) (n / d₂)) +
      padicValNat p (d₁ / Nat.gcd d₁ d₂) +
      padicValNat p (d₂ / Nat.gcd d₁ d₂) := by
  have h4 := coprime_cofactor_four_factor_decomposition n d₁ d₂ hd₁ hd₂
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd₁).2
  rw [h4] at hn0
  have h123_ne : Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂) * (d₁ / Nat.gcd d₁ d₂) ≠ 0 :=
    left_ne_zero_of_mul hn0
  have hu2_ne : d₂ / Nat.gcd d₁ d₂ ≠ 0 := right_ne_zero_of_mul hn0
  have h12_ne : Nat.gcd d₁ d₂ * Nat.gcd (n / d₁) (n / d₂) ≠ 0 := left_ne_zero_of_mul h123_ne
  have hu1_ne : d₁ / Nat.gcd d₁ d₂ ≠ 0 := right_ne_zero_of_mul h123_ne
  have hg1_ne : Nat.gcd d₁ d₂ ≠ 0 := left_ne_zero_of_mul h12_ne
  have hg2_ne : Nat.gcd (n / d₁) (n / d₂) ≠ 0 := right_ne_zero_of_mul h12_ne
  conv_lhs => rw [h4]
  rw [padicValNat.mul h123_ne hu2_ne, padicValNat.mul h12_ne hu1_ne, padicValNat.mul hg1_ne hg2_ne]

/-- Complementary orthogonality of the coprime cofactor `p`-adic valuations: for every prime `p`
and `d₁ ∈ n.divisors`, at least one of `padicValNat p (d₁ / gcd(d₁, d₂))` or
`padicValNat p (d₂ / gcd(d₁, d₂))` vanishes. -/
theorem padicValNat_coprime_cofactor_eq_zero_or_eq_zero (p n d₁ d₂ : ℕ) [Fact p.Prime]
    (hd₁ : d₁ ∈ Nat.divisors n) :
    padicValNat p (d₁ / Nat.gcd d₁ d₂) = 0 ∨ padicValNat p (d₂ / Nat.gcd d₁ d₂) = 0 := by
  have hcop := coprime_div_gcd_of_mem_divisors n d₁ d₂ hd₁
  by_cases hp1 : p ∣ (d₁ / Nat.gcd d₁ d₂)
  · right
    apply padicValNat.eq_zero_of_not_dvd
    intro hp2
    have hdvd1 : p ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hp1 hp2
    exact (Fact.out : p.Prime).not_dvd_one hdvd1
  · left
    exact padicValNat.eq_zero_of_not_dvd hp1

/-- Unconditional prime-power resolution: for every prime `p`, every exponent `m : ℕ`, and every
`ε ≥ 0`, `(Erdos886Divisors (p ^ m) ε 1).card ≤ 1`. -/
theorem card_erdos886Divisors_prime_pow_le_one_of_nonneg (p m : ℕ) (hp : Nat.Prime p)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (Erdos886Divisors (p ^ m) ε 1).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have hm_a := (mem_erdos886Divisors_iff (p ^ m) a ε 1).mp ha
    have hm_b := (mem_erdos886Divisors_iff (p ^ m) b ε 1).mp hb
    rcases (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp hm_a.1).1 with ⟨i, _, rfl⟩
    rcases (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp hm_b.1).1 with ⟨j, _, rfl⟩
    have hij : i ≤ j := by
      by_contra hji
      have hle : p ^ j ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
      omega
    have hdvd : p ^ i ∣ p ^ j := pow_dvd_pow p hij
    exact False.elim (not_dvd_of_mem_erdos886Divisors_of_lt (p ^ m) (p ^ i) (p ^ j) ε 1 hε le_rfl ha hb hlt hdvd)
  · rfl
  · have hm_a := (mem_erdos886Divisors_iff (p ^ m) a ε 1).mp ha
    have hm_b := (mem_erdos886Divisors_iff (p ^ m) b ε 1).mp hb
    rcases (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp hm_a.1).1 with ⟨i, _, rfl⟩
    rcases (Nat.dvd_prime_pow hp).mp (Nat.mem_divisors.mp hm_b.1).1 with ⟨j, _, rfl⟩
    have hji : j ≤ i := by
      by_contra hij
      have hle : p ^ i ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
      omega
    have hdvd : p ^ j ∣ p ^ i := pow_dvd_pow p hji
    exact False.elim (not_dvd_of_mem_erdos886Divisors_of_lt (p ^ m) (p ^ j) (p ^ i) ε 1 hε le_rfl hb ha hgt hdvd)

/-! ## Section 4: Direct Connections to `FormalConjectures.ErdosProblems.«886»` & Controls -/

/-- Solved variant (`FormalConjectures.ErdosProblems.«886»`, Erdős-Rosenfeld [ErRo97]):
there are infinitely many `n` with at least 4 divisors in `(n^{1/2}, n^{1/2} + 16 n^{1/4})`. -/
theorem erdos_886.variants.rosenfeld_infinite :
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1 / 4) 16).card} :=
  erdos_886_rosenfeld_infinite

/-- Solved variant (`FormalConjectures.ErdosProblems.«886»`, Erdős-Rosenfeld [ErRo97]):
for any `C > 0`, all large `n` have at most `1 + C^2` divisors in `[n^{1/2}, n^{1/2} + C n^{1/4}]`. -/
theorem erdos_886.variants.rosenfeld_bound :
    ∀ C > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      (((Nat.divisors n).filter (fun (d : ℕ) =>
        (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
        (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
        ≤ 1 + C ^ 2 :=
  erdos_886_rosenfeld_bound

/-- Bidirectional equivalence reducing the full `erdos_886` target in
`FormalConjectures.ErdosProblems.«886»` to the open regime `0 < ε < 1/4`
(since `ε ≥ 1/4` holds unconditionally with `K = 1` by `erdos_886_of_quarter_le`). -/
theorem erdos_886_iff_forall_pos_lt_quarter :
    (∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K) ↔
      (∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K) := by
  constructor
  · intro h ε hε _
    exact h ε hε
  · intro h ε hε
    by_cases hq : 1 / 4 ≤ ε
    · exact erdos_886_of_quarter_le ε hq
    · exact h ε hε (lt_of_not_ge hq)

/-- Top-down conditional reduction of `erdos_886` in `FormalConjectures.ErdosProblems.«886»` via
our coprime-cofactor / complementary-GCD factorization
`complementary_sum_diff_eq_coprime_cofactor_diff_mul_gcd_diff`:
if for every `0 < ε < 1/4` there is `K : ℕ` such that eventually for all `a ≤ b` in
`Erdos886Divisors n ε 1`, `(b / gcd(a, b) - a / gcd(a, b)) * (gcd(a, b) - gcd(n / a, n / b)) ≤ K`,
then `∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K`. -/
theorem erdos_886_of_eventual_coprime_cofactor_and_complementary_gcd_gap_bound
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ K : ℕ, ∀ᶠ n in Filter.atTop,
        ∀ a ∈ Erdos886Divisors n ε 1, ∀ b ∈ Erdos886Divisors n ε 1, a ≤ b →
          (b / Nat.gcd a b - a / Nat.gcd a b) *
            (Nat.gcd a b - Nat.gcd (n / a) (n / b)) ≤ K) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K := by
  rw [erdos_886_iff_forall_pos_lt_quarter]
  intro ε hε hq
  rcases hbound ε hε hq with ⟨K, hev⟩
  refine ⟨K + 1, hev.mono (fun n hn => ?_)⟩
  have hreal : ((Erdos886Divisors n ε 1).card : ℝ) ≤ 1 + (K : ℝ) := by
    apply card_nat_finset_le_of_strictMonoOn_image_diff
      (Erdos886Divisors n ε 1) (fun d => d + n / d)
    · intro a ha b hb hlt
      have ha_mem := (mem_erdos886Divisors_iff n a ε 1).mp ha
      have hb_mem := (mem_erdos886Divisors_iff n b ε 1).mp hb
      exact complementary_sum_strict_mono_of_ge_sqrt n a b ha_mem.1 hb_mem.1 (le_of_lt ha_mem.2.1) hlt
    · exact Nat.cast_nonneg K
    · intro a ha b hb
      have ha_mem := (mem_erdos886Divisors_iff n a ε 1).mp ha
      have hb_mem := (mem_erdos886Divisors_iff n b ε 1).mp hb
      rcases le_or_gt a b with hle | hgt
      · have hfact := complementary_sum_diff_eq_coprime_cofactor_diff_mul_gcd_diff n a b
          ha_mem.1 hb_mem.1 (le_of_lt ha_mem.2.1) hle
        have hle_K : (b + n / b) - (a + n / a) ≤ K := by
          rw [hfact]
          exact hn a ha b hb hle
        have hs_le : a + n / a ≤ b + n / b := by
          rcases eq_or_lt_of_le hle with rfl | hlt
          · exact le_rfl
          · exact le_of_lt (complementary_sum_strict_mono_of_ge_sqrt n a b ha_mem.1 hb_mem.1 (le_of_lt ha_mem.2.1) hlt)
        have hcast : (((b + n / b) - (a + n / a) : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hle_K
        rw [Nat.cast_sub hs_le] at hcast
        exact hcast
      · have hs_lt := complementary_sum_strict_mono_of_ge_sqrt n b a hb_mem.1 ha_mem.1 (le_of_lt hb_mem.2.1) hgt
        have hs_ltR : ((b + n / b : ℕ) : ℝ) < ((a + n / a : ℕ) : ℝ) := by exact_mod_cast hs_lt
        have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
        linarith
  have hlt_natR : ((Erdos886Divisors n ε 1).card : ℝ) < ((K + 2 : ℕ) : ℝ) := by
    push_cast; linarith
  have hlt_nat : (Erdos886Divisors n ε 1).card < K + 2 := by exact_mod_cast hlt_natR
  omega

/-- Top-down conditional reduction of `erdos_886` under separate eventual upper bounds `U` on
the coprime-cofactor difference `b / gcd(a, b) - a / gcd(a, b)` and `G` on the
GCD-minus-complementary-GCD gap `gcd(a, b) - gcd(n / a, n / b)` across `Erdos886Divisors n ε 1`. -/
theorem erdos_886_of_eventual_separate_coprime_cofactor_and_gcd_gap_bounds
    (hsep : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ U G : ℕ, ∀ᶠ n in Filter.atTop,
        ∀ a ∈ Erdos886Divisors n ε 1, ∀ b ∈ Erdos886Divisors n ε 1, a ≤ b →
          b / Nat.gcd a b - a / Nat.gcd a b ≤ U ∧
          Nat.gcd a b - Nat.gcd (n / a) (n / b) ≤ G) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K := by
  apply erdos_886_of_eventual_coprime_cofactor_and_complementary_gcd_gap_bound
  intro ε hε hq
  rcases hsep ε hε hq with ⟨U, G, hev⟩
  refine ⟨U * G, hev.mono (fun n hn a ha b hb hle => ?_)⟩
  obtain ⟨hU, hG⟩ := hn a ha b hb hle
  exact Nat.mul_le_mul hU hG

/-- Positive control verifying our coprime cofactor four-factor decomposition, double-oblong
factorization at minimal steps, and multi-divisor LCM divisibility on the canonical pilot
witnesses (`n = 720,720`, `n = 471,240`, `n = 85,680`):
1. At `n = 720,720` (`d₁ = 858, d₂ = 880, d₃ = 910`), `gcd(858, 880) = 22`,
   `gcd(720720 / 858, 720720 / 880) = 21`, `858 / 22 = 39`, `880 / 22 = 40`,
   `720720 = 22 * 21 * 39 * 40`, and `lcm(lcm(858, 880), 910) = 446,160` fails to divide `720,720`?
   Wait: `lcm(858, 880) = 34,320`, and `lcm(34320, 910) = 240,240`, which divides `720,720` (`720720 / 240240 = 3`).
2. At `n = 471,240` (`d₁ = 693, d₂ = 714, d₃ = 748`), `gcd(693, 714) = 21`,
   `gcd(471240 / 693, 471240 / 714) = 20`, `693 / 21 = 33`, `714 / 21 = 34`,
   `471240 = 21 * 20 * 33 * 34`, and `lcm(lcm(693, 714), 748) = 47,124 ∣ 471,240` (`471240 / 47124 = 10`).
3. At `n = 85,680` (`d₁ = 306, d₂ = 315, d₃ = 336`), `gcd(306, 315) = 9`,
   `gcd(85680 / 306, 85680 / 315) = 8`, `306 / 9 = 34`, `315 / 9 = 35`,
   `85680 = 9 * 8 * 34 * 35`, and `lcm(lcm(306, 315), 336) = 85,680 ∣ 85,680`. -/
theorem positive_control_coprime_cofactor_and_lcm_witnesses_720720_471240_85680 :
    (720720 = Nat.gcd 858 880 * Nat.gcd (720720 / 858) (720720 / 880) *
      (858 / Nat.gcd 858 880) * (880 / Nat.gcd 858 880) ∧
      Nat.lcm (Nat.lcm 858 880) 910 = 240240 ∧ 240240 ∣ 720720) ∧
    (471240 = Nat.gcd 693 714 * Nat.gcd (471240 / 693) (471240 / 714) *
      (693 / Nat.gcd 693 714) * (714 / Nat.gcd 693 714) ∧
      Nat.lcm (Nat.lcm 693 714) 748 = 47124 ∧ 47124 ∣ 471240) ∧
    (85680 = Nat.gcd 306 315 * Nat.gcd (85680 / 306) (85680 / 315) *
      (306 / Nat.gcd 306 315) * (315 / Nat.gcd 306 315) ∧
      Nat.lcm (Nat.lcm 306 315) 336 = 85680) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩⟩

end Erdos886

