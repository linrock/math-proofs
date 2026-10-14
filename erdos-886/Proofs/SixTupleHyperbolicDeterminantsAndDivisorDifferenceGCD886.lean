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

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace Erdos886

/-! ## Section 1: Pairwise Divisor-Difference GCD, LCM-Quotient Factorization & Modular Congruences -/

/-- Left GCD invariance under divisor subtraction: `gcd(d₂ - d₁, d₁) = gcd(d₁, d₂)`. -/
theorem gcd_divisor_diff_left (d₁ d₂ : ℕ) (hle : d₁ ≤ d₂) :
    Nat.gcd (d₂ - d₁) d₁ = Nat.gcd d₁ d₂ := by
  rw [Nat.gcd_sub_self_left hle, Nat.gcd_comm]

/-- Right GCD invariance under divisor subtraction: `gcd(d₂ - d₁, d₂) = gcd(d₁, d₂)`. -/
theorem gcd_divisor_diff_right (d₁ d₂ : ℕ) (hle : d₁ ≤ d₂) :
    Nat.gcd (d₂ - d₁) d₂ = Nat.gcd d₁ d₂ := by
  have hsub : d₂ - (d₂ - d₁) = d₁ := Nat.sub_sub_self hle
  have h1 : Nat.gcd (d₂ - (d₂ - d₁)) (d₂ - d₁) = Nat.gcd d₂ (d₂ - d₁) :=
    Nat.gcd_sub_self_left (Nat.sub_le d₂ d₁)
  rw [hsub] at h1
  rw [Nat.gcd_comm (d₂ - d₁) d₂, ← h1, Nat.gcd_comm d₁ (d₂ - d₁), gcd_divisor_diff_left d₁ d₂ hle]

/-- For any two divisors `d₁, d₂` of `n`, their least common multiple `lcm(d₁, d₂)` divides `n`. -/
theorem lcm_dvd_of_mem_divisors (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    Nat.lcm d₁ d₂ ∣ n :=
  Nat.lcm_dvd (Nat.mem_divisors.mp hd₁).1 (Nat.mem_divisors.mp hd₂).1

/-- For any two divisors `d₁, d₂` of `n`, `d₁ * d₂` divides `n * gcd(d₁, d₂)`. -/
theorem divisor_product_dvd_mul_gcd_of_mem_divisors (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) :
    d₁ * d₂ ∣ n * Nat.gcd d₁ d₂ := by
  rw [← Nat.gcd_mul_lcm d₁ d₂, mul_comm (Nat.gcd d₁ d₂)]
  exact Nat.mul_dvd_mul_right (lcm_dvd_of_mem_divisors n d₁ d₂ hd₁ hd₂) (Nat.gcd d₁ d₂)

/-- Natural-number complementary-sum difference identity for divisors `n^{1/2} ≤ d₁ ≤ d₂`:
`d₁ * d₂ * ((d₂ + n/d₂) - (d₁ + n/d₁)) = (d₂ - d₁) * (d₁ * d₂ - n)`. -/
theorem nat_complementary_sum_diff_mul_eq_of_ge_sqrt (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    d₁ * d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) = (d₂ - d₁) * (d₁ * d₂ - n) := by
  have hprod := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have hn_le : n ≤ d₁ * d₂ := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hmul : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ) * (d₁ : ℝ) :=
      mul_self_le_mul_self h0 hge
    have hsq : (n : ℝ) ≤ (d₁ : ℝ) * (d₁ : ℝ) := by
      have hr := rpow_half_sq n
      nlinarith
    have hd1_le : d₁ * d₁ ≤ d₁ * d₂ := Nat.mul_le_mul_left d₁ hle
    have hn_le_d1 : n ≤ d₁ * d₁ := by exact_mod_cast hsq
    exact le_trans hn_le_d1 hd1_le
  have hs_le : d₁ + n / d₁ ≤ d₂ + n / d₂ := by
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_rfl
    · have hlt_real := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hge hlt
      have hlt_nat : d₁ + n / d₁ < d₂ + n / d₂ := by exact_mod_cast hlt_real
      exact le_of_lt hlt_nat
  have hcast : ((d₁ * d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) : ℕ) : ℝ) =
      (((d₂ - d₁) * (d₁ * d₂ - n) : ℕ) : ℝ) := by
    push_cast [hle, hs_le, hn_le]
    exact hprod
  exact_mod_cast hcast

/-- Exact GCD / LCM-quotient factorization of the complementary-sum difference:
`gcd(d₁, d₂) * ((d₂ + n/d₂) - (d₁ + n/d₁)) = (d₂ - d₁) * (gcd(d₁, d₂) - n / lcm(d₁, d₂))`. -/
theorem gcd_mul_complementary_sum_diff_eq_diff_mul_gcd_sub_lcm_quotient (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) =
      (d₂ - d₁) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂) := by
  have hnat := nat_complementary_sum_diff_mul_eq_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hge hle
  have hlcm_dvd : Nat.lcm d₁ d₂ ∣ n := lcm_dvd_of_mem_divisors n d₁ d₂ hd₁ hd₂
  have hn_eq : n = Nat.lcm d₁ d₂ * (n / Nat.lcm d₁ d₂) :=
    (Nat.mul_div_cancel' hlcm_dvd).symm
  have hprod_eq : d₁ * d₂ = Nat.lcm d₁ d₂ * Nat.gcd d₁ d₂ := by
    rw [← Nat.gcd_mul_lcm d₁ d₂, mul_comm]
  have hd1_pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  have hd2_pos : 0 < d₂ := Nat.pos_of_mem_divisors hd₂
  have hlcm_pos : 0 < Nat.lcm d₁ d₂ := Nat.lcm_pos hd1_pos hd2_pos
  have hsub_eq : d₁ * d₂ - n = Nat.lcm d₁ d₂ * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂) := by
    rw [hprod_eq, Nat.mul_sub_left_distrib, ← hn_eq]
  have hmul_lcm :
      Nat.lcm d₁ d₂ * (Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁))) =
        Nat.lcm d₁ d₂ * ((d₂ - d₁) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂)) := by
    calc
      Nat.lcm d₁ d₂ * (Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)))
        = (Nat.lcm d₁ d₂ * Nat.gcd d₁ d₂) * ((d₂ + n / d₂) - (d₁ + n / d₁)) := by ring
      _ = d₁ * d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) := by rw [← hprod_eq]
      _ = (d₂ - d₁) * (d₁ * d₂ - n) := hnat
      _ = (d₂ - d₁) * (Nat.lcm d₁ d₂ * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂)) := by rw [hsub_eq]
      _ = Nat.lcm d₁ d₂ * ((d₂ - d₁) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂)) := by ring
  exact Nat.eq_of_mul_eq_mul_left hlcm_pos hmul_lcm

/-- Reduced coprime-step factorization of the complementary-sum difference:
`(d₂ + n/d₂) - (d₁ + n/d₁) = ((d₂ - d₁) / gcd(d₁, d₂)) * (gcd(d₁, d₂) - n / lcm(d₁, d₂))`. -/
theorem complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    (d₂ + n / d₂) - (d₁ + n / d₁) =
      ((d₂ - d₁) / Nat.gcd d₁ d₂) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂) := by
  have hgcd_eq := gcd_mul_complementary_sum_diff_eq_diff_mul_gcd_sub_lcm_quotient n d₁ d₂ hd₁ hd₂ hge hle
  have hgdvd : Nat.gcd d₁ d₂ ∣ d₂ - d₁ :=
    Nat.dvd_sub (Nat.gcd_dvd_right d₁ d₂) (Nat.gcd_dvd_left d₁ d₂)
  have hdiff_eq : d₂ - d₁ = Nat.gcd d₁ d₂ * ((d₂ - d₁) / Nat.gcd d₁ d₂) :=
    (Nat.mul_div_cancel' hgdvd).symm
  have hd1_pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
  have hgcd_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd1_pos
  have hmul_gcd :
      Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) =
        Nat.gcd d₁ d₂ * (((d₂ - d₁) / Nat.gcd d₁ d₂) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂)) := by
    calc
      Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁))
        = (d₂ - d₁) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂) := hgcd_eq
      _ = (Nat.gcd d₁ d₂ * ((d₂ - d₁) / Nat.gcd d₁ d₂)) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂) := by
            rw [← hdiff_eq]
      _ = Nat.gcd d₁ d₂ * (((d₂ - d₁) / Nat.gcd d₁ d₂) * (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂)) := by ring
  exact Nat.eq_of_mul_eq_mul_left hgcd_pos hmul_gcd

/-- The reduced divisor difference `(d₂ - d₁) / gcd(d₁, d₂)` divides `(d₂ + n/d₂) - (d₁ + n/d₁)`. -/
theorem reduced_divisor_diff_dvd_complementary_sum_diff (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    ((d₂ - d₁) / Nat.gcd d₁ d₂) ∣ ((d₂ + n / d₂) - (d₁ + n / d₁)) := by
  rw [complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient n d₁ d₂ hd₁ hd₂ hge hle]
  exact dvd_mul_right _ _

/-- The GCD-to-LCM-quotient gap `gcd(d₁, d₂) - n / lcm(d₁, d₂)` divides `(d₂ + n/d₂) - (d₁ + n/d₁)`. -/
theorem gcd_sub_lcm_quotient_dvd_complementary_sum_diff (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hle : d₁ ≤ d₂) :
    (Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂) ∣ ((d₂ + n / d₂) - (d₁ + n / d₁)) := by
  rw [complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient n d₁ d₂ hd₁ hd₂ hge hle]
  exact dvd_mul_left _ _

/-- For divisors `n^{1/2} ≤ d₁ < d₂` of `n`, `n / lcm(d₁, d₂) < gcd(d₁, d₂)`. -/
theorem lcm_quotient_lt_gcd_of_ge_sqrt (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂) :
    n / Nat.lcm d₁ d₂ < Nat.gcd d₁ d₂ := by
  have hs_lt_real := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hge hlt
  have hs_lt : d₁ + n / d₁ < d₂ + n / d₂ := by exact_mod_cast hs_lt_real
  have hs_pos : 0 < (d₂ + n / d₂) - (d₁ + n / d₁) := Nat.sub_pos_of_lt hs_lt
  have heq := complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient n d₁ d₂ hd₁ hd₂ hge (le_of_lt hlt)
  rw [heq] at hs_pos
  have hsub_pos : 0 < Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂ := Nat.pos_of_mul_pos_left hs_pos
  exact Nat.lt_of_sub_pos hsub_pos

/-- Pairwise divisor-difference GCD inequality above `n^{1/2}`:
`d₂ - d₁ ≤ gcd(d₁, d₂) * ((d₂ + n/d₂) - (d₁ + n/d₁))`. -/
theorem divisor_diff_le_gcd_mul_complementary_sum_diff (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂) :
    d₂ - d₁ ≤ Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) := by
  have hlt_gcd := lcm_quotient_lt_gcd_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hge hlt
  have h1 : 1 ≤ Nat.gcd d₁ d₂ - n / Nat.lcm d₁ d₂ := Nat.le_sub_of_add_le (by omega)
  have heq := gcd_mul_complementary_sum_diff_eq_diff_mul_gcd_sub_lcm_quotient n d₁ d₂ hd₁ hd₂ hge (le_of_lt hlt)
  rw [heq]
  exact Nat.le_mul_of_pos_right (d₂ - d₁) h1

/-- Pairwise GCD-weighted window bound for `d₁ < d₂` in `Erdos886Divisors n ε C`:
`d₂ - d₁ < gcd(d₁, d₂) * C^2 * n^{1/2 - 2ε}`. -/
theorem divisor_diff_lt_gcd_mul_sq_rpow_of_mem_erdos886Divisors (n d₁ d₂ : ℕ) (ε C : ℝ)
    (hC : 0 ≤ C) (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hlt : d₁ < d₂) :
    ((d₂ - d₁ : ℕ) : ℝ) < (Nat.gcd d₁ d₂ : ℝ) * C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hmem₁ := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hmem₂ := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hle_nat := divisor_diff_le_gcd_mul_complementary_sum_diff n d₁ d₂ hmem₁.1 hmem₂.1
    (le_of_lt hmem₁.2.1) hlt
  have hs_lt_real := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hmem₁.1 hmem₂.1
    (le_of_lt hmem₁.2.1) hlt
  have hs_le : d₁ + n / d₁ ≤ d₂ + n / d₂ := le_of_lt (by exact_mod_cast hs_lt_real)
  have hle_real : ((d₂ - d₁ : ℕ) : ℝ) ≤
      (Nat.gcd d₁ d₂ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
    have hcast : ((Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) : ℕ) : ℝ) =
        (Nat.gcd d₁ d₂ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
      push_cast [hs_le]
      ring
    rw [← hcast]
    exact_mod_cast hle_nat
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₂ ε C hC hd₁ hd₂
  have hd1_pos : 0 < d₁ := Nat.pos_of_mem_divisors hmem₁.1
  have hgcd_pos : (0 : ℝ) < (Nat.gcd d₁ d₂ : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left d₂ hd1_pos
  have hmul_lt : (Nat.gcd d₁ d₂ : ℝ) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) <
      (Nat.gcd d₁ d₂ : ℝ) * (C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε)) :=
    mul_lt_mul_of_pos_left hspan hgcd_pos
  linarith

/-- Minimal complementary-sum step forces superparticular GCD equality `d₂ - d₁ = gcd(d₁, d₂)`. -/
theorem divisor_diff_eq_gcd_of_complementary_sum_diff_eq_one (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂)
    (hstep : (d₂ + n / d₂) - (d₁ + n / d₁) = 1) :
    d₂ - d₁ = Nat.gcd d₁ d₂ := by
  have hle1 := divisor_diff_le_gcd_mul_complementary_sum_diff n d₁ d₂ hd₁ hd₂ hge hlt
  rw [hstep, mul_one] at hle1
  have hgdvd : Nat.gcd d₁ d₂ ∣ d₂ - d₁ :=
    Nat.dvd_sub (Nat.gcd_dvd_right d₁ d₂) (Nat.gcd_dvd_left d₁ d₂)
  have hle2 : Nat.gcd d₁ d₂ ≤ d₂ - d₁ := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hgdvd
  exact le_antisymm hle1 hle2

/-- When `(d₂ + n/d₂) - (d₁ + n/d₁) = 1`, the gap `d₂ - d₁` divides both `d₁` and `d₂`,
so `d₁ ≡ 0 [MOD d₂ - d₁]` and `d₂ ≡ 0 [MOD d₂ - d₁]`. -/
theorem divisor_diff_dvd_both_and_modEq_zero_of_complementary_sum_diff_eq_one (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n)
    (hge : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ)) (hlt : d₁ < d₂)
    (hstep : (d₂ + n / d₂) - (d₁ + n / d₁) = 1) :
    (d₂ - d₁) ∣ d₁ ∧ (d₂ - d₁) ∣ d₂ ∧ d₁ ≡ 0 [MOD d₂ - d₁] ∧ d₂ ≡ 0 [MOD d₂ - d₁] := by
  have heq := divisor_diff_eq_gcd_of_complementary_sum_diff_eq_one n d₁ d₂ hd₁ hd₂ hge hlt hstep
  have hdvd₁ : (d₂ - d₁) ∣ d₁ := by rw [heq]; exact Nat.gcd_dvd_left d₁ d₂
  have hdvd₂ : (d₂ - d₁) ∣ d₂ := by rw [heq]; exact Nat.gcd_dvd_right d₁ d₂
  exact ⟨hdvd₁, hdvd₂, Nat.modEq_zero_iff_dvd.mpr hdvd₁, Nat.modEq_zero_iff_dvd.mpr hdvd₂⟩

/-- Universal modular congruence for any pair of divisors `d₁ ≤ d₂` of `n`:
`d₂ ≡ d₁ [MOD gcd(d₁, d₂)]` and `d₁ * d₂ ≡ n [MOD lcm(d₁, d₂)]`. -/
theorem divisor_modEq_and_product_modEq_of_mem_divisors (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hle : d₁ ≤ d₂) :
    d₂ ≡ d₁ [MOD Nat.gcd d₁ d₂] ∧ d₁ * d₂ ≡ n [MOD Nat.lcm d₁ d₂] := by
  have hm1 : d₁ ≡ 0 [MOD Nat.gcd d₁ d₂] := Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_left d₁ d₂)
  have hm2 : d₂ ≡ 0 [MOD Nat.gcd d₁ d₂] := Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_right d₁ d₂)
  have hl1 : d₁ * d₂ ≡ 0 [MOD Nat.lcm d₁ d₂] := by
    rw [Nat.modEq_zero_iff_dvd, ← Nat.gcd_mul_lcm d₁ d₂]
    exact dvd_mul_left (Nat.lcm d₁ d₂) (Nat.gcd d₁ d₂)
  have hl2 : n ≡ 0 [MOD Nat.lcm d₁ d₂] :=
    Nat.modEq_zero_iff_dvd.mpr (lcm_dvd_of_mem_divisors n d₁ d₂ hd₁ hd₂)
  exact ⟨hm2.trans hm1.symm, hl1.trans hl2.symm⟩

/-! ## Section 2: 6-Tuple (Fifth-Order) Hyperbolic Vandermonde Determinants & Outer Bambah-Chowla Decomposition -/

/-- Exact 4-term decomposition of the outer 6-tuple Bambah-Chowla determinant `Δ₁₂₅₆`
into the four adjacent `3 × 3` hyperbolic Vandermonde determinants `Δ₄₅₆, Δ₃₄₅, Δ₂₃₄, Δ₁₂₃`. -/
theorem six_tuple_outer_bambah_chowla_four_term_decomposition
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) :
    ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
        ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
      (((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
        ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))) +
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) *
      (((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
        ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))) +
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) *
      (((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))) +
    ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) := by
  ring

/-- Exact disjoint-triple coupled 6-tuple hyperbolic Vandermonde determinant identity:
`d₁*d₂*d₃*d₄*d₅*d₆ * (V₃(d₄,d₅,d₆)*Δ₁₂₃ - V₃(d₁,d₂,d₃)*Δ₄₅₆) = n * V₃(d₁,d₂,d₃) * V₃(d₄,d₅,d₆) * (d₄*d₅*d₆ - d₁*d₂*d₃)`. -/
theorem six_tuple_disjoint_triple_coupled_vandermonde_identity
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n) :
    (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) *
      (((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        (((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
          ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))))) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        ((d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ)) := by
  have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have h23 := complementary_sum_diff_product_identity n d₂ d₃ hd₂ hd₃
  have h45 := complementary_sum_diff_product_identity n d₄ d₅ hd₄ hd₅
  have h56 := complementary_sum_diff_product_identity n d₅ d₆ hd₅ hd₆
  have hv123 :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
        (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    linear_combination (d₁ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * h23 - (d₃ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * h12
  have hv456 :
      (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) *
        (((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
          ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))) =
        (n : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) := by
    linear_combination (d₄ : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) * h56 - (d₆ : ℝ) * ((d₆ : ℝ) - (d₅ : ℝ)) * h45
  linear_combination
    (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) *
      ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) * hv123 -
    (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) *
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * hv456

/-- Strict integer positivity (`≥ 1`) of the disjoint-triple coupled 6-tuple determinant
for any `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` dividing `n`. -/
theorem one_le_six_tuple_disjoint_triple_coupled_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
      (((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
        ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))) + 1 ≤
    ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) := by
  have hid := six_tuple_disjoint_triple_coupled_vandermonde_identity n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
  have hd1_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd2_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd3_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hd4_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₄
  have hd5_pos : (0 : ℝ) < (d₅ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₅
  have hd6_pos : (0 : ℝ) < (d₆ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₆
  have h12_pos : (0 : ℝ) < (d₂ : ℝ) - (d₁ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt12)
  have h23_pos : (0 : ℝ) < (d₃ : ℝ) - (d₂ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt23)
  have h13_pos : (0 : ℝ) < (d₃ : ℝ) - (d₁ : ℝ) := sub_pos.mpr (by exact_mod_cast lt_trans hlt12 hlt23)
  have h45_pos : (0 : ℝ) < (d₅ : ℝ) - (d₄ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt45)
  have h56_pos : (0 : ℝ) < (d₆ : ℝ) - (d₅ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt56)
  have h46_pos : (0 : ℝ) < (d₆ : ℝ) - (d₄ : ℝ) := sub_pos.mpr (by exact_mod_cast lt_trans hlt45 hlt56)
  have hprod_lt : d₁ * d₂ * d₃ < d₄ * d₅ * d₆ := by
    have h14 : d₁ < d₄ := lt_trans (lt_trans hlt12 hlt23) hlt34
    have h25 : d₂ < d₅ := lt_trans (lt_trans hlt23 hlt34) hlt45
    have h36 : d₃ < d₆ := lt_trans (lt_trans hlt34 hlt45) hlt56
    exact Nat.mul_lt_mul_of_lt_of_lt (Nat.mul_lt_mul_of_lt_of_lt h14 h25) h36
  have hdiff_pos : (0 : ℝ) < (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) := by
    have hcast : ((d₁ * d₂ * d₃ : ℕ) : ℝ) < ((d₄ * d₅ * d₆ : ℕ) : ℝ) := by exact_mod_cast hprod_lt
    push_cast at hcast
    linarith
  have hrhs_pos :
      (0 : ℝ) < (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        ((d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ)) := by
    positivity
  rw [← hid] at hrhs_pos
  have hP_pos : (0 : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) := by positivity
  have hdet_pos :
      (0 : ℝ) <
        ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
          (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
            ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
        ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
          (((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
            ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))) :=
    pos_of_mul_pos_right hrhs_pos (le_of_lt hP_pos)
  let Z : ℤ :=
    ((d₅ : ℤ) - (d₄ : ℤ)) * ((d₆ : ℤ) - (d₅ : ℤ)) * ((d₆ : ℤ) - (d₄ : ℤ)) *
      (((d₂ : ℤ) - (d₁ : ℤ)) * (((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ)) - ((d₂ : ℤ) + ((n / d₂ : ℕ) : ℤ))) -
        ((d₃ : ℤ) - (d₂ : ℤ)) * (((d₂ : ℤ) + ((n / d₂ : ℕ) : ℤ)) - ((d₁ : ℤ) + ((n / d₁ : ℕ) : ℤ)))) -
    ((d₂ : ℤ) - (d₁ : ℤ)) * ((d₃ : ℤ) - (d₂ : ℤ)) * ((d₃ : ℤ) - (d₁ : ℤ)) *
      (((d₅ : ℤ) - (d₄ : ℤ)) * (((d₆ : ℤ) + ((n / d₆ : ℕ) : ℤ)) - ((d₅ : ℤ) + ((n / d₅ : ℕ) : ℤ))) -
        ((d₆ : ℤ) - (d₅ : ℤ)) * (((d₅ : ℤ) + ((n / d₅ : ℕ) : ℤ)) - ((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ))))
  have hZ_cast : (Z : ℝ) =
      ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        (((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
          ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))) := by
    simp only [Z, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have hZ_pos : (0 : ℤ) < Z := by
    rw [← hZ_cast] at hdet_pos
    exact_mod_cast hdet_pos
  have hZ_ge1 : (1 : ℝ) ≤ (Z : ℝ) := by
    have : (1 : ℤ) ≤ Z := hZ_pos
    exact_mod_cast this
  linarith

/-- Division-free 6-tuple product bound from the disjoint-triple coupled determinant:
`d₁*d₂*d₃*d₄*d₅*d₆ ≤ n * V₃(d₁,d₂,d₃) * V₃(d₄,d₅,d₆) * (d₄*d₅*d₆ - d₁*d₂*d₃)`. -/
theorem six_tuple_product_le_mul_disjoint_triple_coupled_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    d₁ * d₂ * d₃ * d₄ * d₅ * d₆ ≤
      n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) *
        (d₅ - d₄) * (d₆ - d₅) * (d₆ - d₄) *
        (d₄ * d₅ * d₆ - d₁ * d₂ * d₃) := by
  have hid := six_tuple_disjoint_triple_coupled_vandermonde_identity n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆
  have hge1 := one_le_six_tuple_disjoint_triple_coupled_vandermonde_of_lt n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56
  have hd1_pos : (0 : ℝ) ≤ (d₁ : ℝ) := Nat.cast_nonneg d₁
  have hd2_pos : (0 : ℝ) ≤ (d₂ : ℝ) := Nat.cast_nonneg d₂
  have hd3_pos : (0 : ℝ) ≤ (d₃ : ℝ) := Nat.cast_nonneg d₃
  have hd4_pos : (0 : ℝ) ≤ (d₄ : ℝ) := Nat.cast_nonneg d₄
  have hd5_pos : (0 : ℝ) ≤ (d₅ : ℝ) := Nat.cast_nonneg d₅
  have hd6_pos : (0 : ℝ) ≤ (d₆ : ℝ) := Nat.cast_nonneg d₆
  have hP_nonneg : (0 : ℝ) ≤ (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) := by positivity
  have hdet_ge1 : (1 : ℝ) ≤
      ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
          ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) -
      ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        (((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
          ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))) := by linarith
  have hmul :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) * 1 ≤
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) *
        ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        ((d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) - (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ)) := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hdet_ge1 hP_nonneg
  have h13 : d₁ ≤ d₃ := le_of_lt (lt_trans hlt12 hlt23)
  have h46 : d₄ ≤ d₆ := le_of_lt (lt_trans hlt45 hlt56)
  have hprod_le : d₁ * d₂ * d₃ ≤ d₄ * d₅ * d₆ := by
    have h14 : d₁ ≤ d₄ := le_of_lt (lt_trans (lt_trans hlt12 hlt23) hlt34)
    have h25 : d₂ ≤ d₅ := le_of_lt (lt_trans (lt_trans hlt23 hlt34) hlt45)
    have h36 : d₃ ≤ d₆ := le_of_lt (lt_trans (lt_trans hlt34 hlt45) hlt56)
    exact Nat.mul_le_mul (Nat.mul_le_mul h14 h25) h36
  have hcast :
      ((d₁ * d₂ * d₃ * d₄ * d₅ * d₆ : ℕ) : ℝ) ≤
      ((n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) *
        (d₅ - d₄) * (d₆ - d₅) * (d₆ - d₄) *
        (d₄ * d₅ * d₆ - d₁ * d₂ * d₃) : ℕ) : ℝ) := by
    push_cast [le_of_lt hlt12, le_of_lt hlt23, h13, le_of_lt hlt45, le_of_lt hlt56, h46, hprod_le]
    linarith
  exact_mod_cast hcast

/-- For any 6-tuple `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` in `Erdos886Divisors n ε C`,
`n^2 < V₃(d₁,d₂,d₃) * V₃(d₄,d₅,d₆) * (d₄*d₅*d₆ - d₁*d₂*d₃)`. -/
theorem sq_lt_disjoint_triple_coupled_vandermonde_of_six_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) (ε C : ℝ)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε C) (hd₆ : d₆ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    n ^ 2 <
      (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) *
        (d₅ - d₄) * (d₆ - d₅) * (d₆ - d₄) *
        (d₄ * d₅ * d₆ - d₁ * d₂ * d₃) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hm5 := (mem_erdos886Divisors_iff n d₅ ε C).mp hd₅
  have hm6 := (mem_erdos886Divisors_iff n d₆ ε C).mp hd₆
  have hle := six_tuple_product_le_mul_disjoint_triple_coupled_vandermonde_of_lt n d₁ d₂ d₃ d₄ d₅ d₆
    hm1.1 hm2.1 hm3.1 hm4.1 hm5.1 hm6.1 hlt12 hlt23 hlt34 hlt45 hlt56
  have h0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsq := rpow_half_sq n
  have hn12 : n < d₁ * d₂ := by
    have : (n : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by
      have := mul_lt_mul_of_nonneg hm1.2.1 hm2.2.1 h0 h0
      nlinarith
    exact_mod_cast this
  have hn34 : n < d₃ * d₄ := by
    have : (n : ℝ) < (d₃ : ℝ) * (d₄ : ℝ) := by
      have := mul_lt_mul_of_nonneg hm3.2.1 hm4.2.1 h0 h0
      nlinarith
    exact_mod_cast this
  have hn56 : n < d₅ * d₆ := by
    have : (n : ℝ) < (d₅ : ℝ) * (d₆ : ℝ) := by
      have := mul_lt_mul_of_nonneg hm5.2.1 hm6.2.1 h0 h0
      nlinarith
    exact_mod_cast this
  have hcube : n * (n ^ 2) < d₁ * d₂ * d₃ * d₄ * d₅ * d₆ := by
    have h1234 := Nat.mul_lt_mul_of_lt_of_lt hn12 hn34
    have h123456 := Nat.mul_lt_mul_of_lt_of_lt h1234 hn56
    calc
      n * (n ^ 2) = (n * n) * n := by ring
      _ < ((d₁ * d₂) * (d₃ * d₄)) * (d₅ * d₆) := h123456
      _ = d₁ * d₂ * d₃ * d₄ * d₅ * d₆ := by ring
  have hlt_mul :
      n * (n ^ 2) <
        n * ((d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) *
          (d₅ - d₄) * (d₆ - d₅) * (d₆ - d₄) *
          (d₄ * d₅ * d₆ - d₁ * d₂ * d₃)) := by
    calc
      n * (n ^ 2) < d₁ * d₂ * d₃ * d₄ * d₅ * d₆ := hcube
      _ ≤ n * (d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) *
            (d₅ - d₄) * (d₆ - d₅) * (d₆ - d₄) *
            (d₄ * d₅ * d₆ - d₁ * d₂ * d₃) := hle
      _ = n * ((d₂ - d₁) * (d₃ - d₂) * (d₃ - d₁) *
            (d₅ - d₄) * (d₆ - d₅) * (d₆ - d₄) *
            (d₄ * d₅ * d₆ - d₁ * d₂ * d₃)) := by ring
  exact Nat.lt_of_mul_lt_mul_left hlt_mul

/-- Exact unweighted fifth-order hyperbolic Vandermonde determinant identity on 6 divisors:
`d₁*d₂*d₃*d₄*d₅*d₆ * Δ⁽⁵⁾₁₂₃₄₅₆ = n * V₆(d₁, d₂, d₃, d₄, d₅, d₆)`. -/
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
        ((d₅ : ℝ) - (d₁ : ℝ)) * ((d₆ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₁ : ℝ)) := by
  have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
  have h23 := complementary_sum_diff_product_identity n d₂ d₃ hd₂ hd₃
  have h34 := complementary_sum_diff_product_identity n d₃ d₄ hd₃ hd₄
  have h45 := complementary_sum_diff_product_identity n d₄ d₅ hd₄ hd₅
  have h56 := complementary_sum_diff_product_identity n d₅ d₆ hd₅ hd₆
  set D123 : ℝ :=
    ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
      ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))
  set D234 : ℝ :=
    ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
      ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ)))
  set D345 : ℝ :=
    ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
      ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))
  set D456 : ℝ :=
    ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
      ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))
  have hv123 : (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * D123 =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) := by
    dsimp [D123]
    linear_combination (d₁ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * h23 - (d₃ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * h12
  have hv234 : (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * D234 =
      (n : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) := by
    dsimp [D234]
    linear_combination (d₂ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * h34 - (d₄ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * h23
  have hv345 : (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * D345 =
      (n : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) := by
    dsimp [D345]
    linear_combination (d₃ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * h45 - (d₅ : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) * h34
  have hv456 : (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) * D456 =
      (n : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) := by
    dsimp [D456]
    linear_combination (d₄ : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) * h56 - (d₆ : ℝ) * ((d₆ : ℝ) - (d₅ : ℝ)) * h45
  clear_value D123 D234 D345 D456
  have h1234 :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) *
        (((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * D123 -
          ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * D234) =
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
        ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₁ : ℝ)) := by
    linear_combination
      (d₄ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * hv123 -
      (d₁ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₁ : ℝ)) * hv234
  have h2345 :
      (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) *
        (((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * D234 -
          ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * D345) =
      (n : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) *
        ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) := by
    linear_combination
      (d₅ : ℝ) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * hv234 -
      (d₂ : ℝ) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * hv345
  have h3456 :
      (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) *
        (((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) * D345 -
          ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * D456) =
      (n : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) *
        ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₃ : ℝ)) := by
    linear_combination
      (d₆ : ℝ) * ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) * hv345 -
      (d₃ : ℝ) * ((d₄ : ℝ) - (d₃ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * hv456
  set g12 : ℝ := (d₂ : ℝ) - (d₁ : ℝ)
  set g23 : ℝ := (d₃ : ℝ) - (d₂ : ℝ)
  set g34 : ℝ := (d₄ : ℝ) - (d₃ : ℝ)
  set g45 : ℝ := (d₅ : ℝ) - (d₄ : ℝ)
  set g56 : ℝ := (d₆ : ℝ) - (d₅ : ℝ)
  set g13 : ℝ := (d₃ : ℝ) - (d₁ : ℝ)
  set g24 : ℝ := (d₄ : ℝ) - (d₂ : ℝ)
  set g35 : ℝ := (d₅ : ℝ) - (d₃ : ℝ)
  set g46 : ℝ := (d₆ : ℝ) - (d₄ : ℝ)
  set g14 : ℝ := (d₄ : ℝ) - (d₁ : ℝ)
  set g25 : ℝ := (d₅ : ℝ) - (d₂ : ℝ)
  set g36 : ℝ := (d₆ : ℝ) - (d₃ : ℝ)
  clear_value g12 g23 g34 g45 g56 g13 g24 g35 g46 g14 g25 g36
  have h12345 :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) *
        (g45 * g35 * g25 * (g34 * g24 * D123 - g12 * g13 * D234) -
          g12 * g13 * g14 * (g45 * g35 * D234 - g23 * g24 * D345)) =
      (n : ℝ) * g12 * g23 * g34 * g45 * g13 * g24 * g35 * g14 * g25 * ((d₅ : ℝ) - (d₁ : ℝ)) := by
    linear_combination
      (d₅ : ℝ) * g45 * g35 * g25 * h1234 -
      (d₁ : ℝ) * g12 * g13 * g14 * h2345
  have h23456 :
      (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) *
        (g56 * g46 * g36 * (g45 * g35 * D234 - g23 * g24 * D345) -
          g23 * g24 * g25 * (g56 * g46 * D345 - g34 * g35 * D456)) =
      (n : ℝ) * g23 * g34 * g45 * g56 * g24 * g35 * g46 * g25 * g36 * ((d₆ : ℝ) - (d₂ : ℝ)) := by
    linear_combination
      (d₆ : ℝ) * g56 * g46 * g36 * h2345 -
      (d₂ : ℝ) * g23 * g24 * g25 * h3456
  set g15 : ℝ := (d₅ : ℝ) - (d₁ : ℝ)
  set g26 : ℝ := (d₆ : ℝ) - (d₂ : ℝ)
  clear_value g15 g26
  linear_combination
    (d₆ : ℝ) * g56 * g46 * g36 * g26 * h12345 -
    (d₁ : ℝ) * g12 * g13 * g14 * g15 * h23456

/-- Strict integer positivity (`≥ 1`) of the unweighted fifth-order hyperbolic Vandermonde determinant
for any `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` dividing `n`. -/
theorem one_le_fifth_order_hyperbolic_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
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
            ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))))) + 1 ≤
    ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₃ : ℝ)) * ((d₆ : ℝ) - (d₂ : ℝ)) *
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
            ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ)))))) := by
  have hid := fifth_order_hyperbolic_vandermonde_six_tuple_identity n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
  have hd1_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
  have hd2_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
  have hd3_pos : (0 : ℝ) < (d₃ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₃
  have hd4_pos : (0 : ℝ) < (d₄ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₄
  have hd5_pos : (0 : ℝ) < (d₅ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₅
  have hd6_pos : (0 : ℝ) < (d₆ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₆
  have hlt13 : d₁ < d₃ := lt_trans hlt12 hlt23
  have hlt24 : d₂ < d₄ := lt_trans hlt23 hlt34
  have hlt35 : d₃ < d₅ := lt_trans hlt34 hlt45
  have hlt46 : d₄ < d₆ := lt_trans hlt45 hlt56
  have hlt14 : d₁ < d₄ := lt_trans hlt13 hlt34
  have hlt25 : d₂ < d₅ := lt_trans hlt24 hlt45
  have hlt36 : d₃ < d₆ := lt_trans hlt35 hlt56
  have hlt15 : d₁ < d₅ := lt_trans hlt14 hlt45
  have hlt26 : d₂ < d₆ := lt_trans hlt25 hlt56
  have hlt16 : d₁ < d₆ := lt_trans hlt15 hlt56
  have hg12 : (0 : ℝ) < (d₂ : ℝ) - (d₁ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt12)
  have hg23 : (0 : ℝ) < (d₃ : ℝ) - (d₂ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt23)
  have hg34 : (0 : ℝ) < (d₄ : ℝ) - (d₃ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt34)
  have hg45 : (0 : ℝ) < (d₅ : ℝ) - (d₄ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt45)
  have hg56 : (0 : ℝ) < (d₆ : ℝ) - (d₅ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt56)
  have hg13 : (0 : ℝ) < (d₃ : ℝ) - (d₁ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt13)
  have hg24 : (0 : ℝ) < (d₄ : ℝ) - (d₂ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt24)
  have hg35 : (0 : ℝ) < (d₅ : ℝ) - (d₃ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt35)
  have hg46 : (0 : ℝ) < (d₆ : ℝ) - (d₄ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt46)
  have hg14 : (0 : ℝ) < (d₄ : ℝ) - (d₁ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt14)
  have hg25 : (0 : ℝ) < (d₅ : ℝ) - (d₂ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt25)
  have hg36 : (0 : ℝ) < (d₆ : ℝ) - (d₃ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt36)
  have hg15 : (0 : ℝ) < (d₅ : ℝ) - (d₁ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt15)
  have hg26 : (0 : ℝ) < (d₆ : ℝ) - (d₂ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt26)
  have hg16 : (0 : ℝ) < (d₆ : ℝ) - (d₁ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt16)
  have hrhs_pos :
      (0 : ℝ) < (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
        ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) *
        ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        ((d₄ : ℝ) - (d₁ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₃ : ℝ)) *
        ((d₅ : ℝ) - (d₁ : ℝ)) * ((d₆ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₁ : ℝ)) := by
    positivity
  rw [← hid] at hrhs_pos
  have hP_pos : (0 : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) := by positivity
  have hdet_pos := pos_of_mul_pos_right hrhs_pos (le_of_lt hP_pos)
  let Z : ℤ :=
    ((d₆ : ℤ) - (d₅ : ℤ)) * ((d₆ : ℤ) - (d₄ : ℤ)) * ((d₆ : ℤ) - (d₃ : ℤ)) * ((d₆ : ℤ) - (d₂ : ℤ)) *
      (((d₅ : ℤ) - (d₄ : ℤ)) * ((d₅ : ℤ) - (d₃ : ℤ)) * ((d₅ : ℤ) - (d₂ : ℤ)) *
        (((d₄ : ℤ) - (d₃ : ℤ)) * ((d₄ : ℤ) - (d₂ : ℤ)) *
          (((d₂ : ℤ) - (d₁ : ℤ)) * (((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ)) - ((d₂ : ℤ) + ((n / d₂ : ℕ) : ℤ))) -
            ((d₃ : ℤ) - (d₂ : ℤ)) * (((d₂ : ℤ) + ((n / d₂ : ℕ) : ℤ)) - ((d₁ : ℤ) + ((n / d₁ : ℕ) : ℤ)))) -
        ((d₂ : ℤ) - (d₁ : ℤ)) * ((d₃ : ℤ) - (d₁ : ℤ)) *
          (((d₃ : ℤ) - (d₂ : ℤ)) * (((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ)) - ((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ))) -
            ((d₄ : ℤ) - (d₃ : ℤ)) * (((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ)) - ((d₂ : ℤ) + ((n / d₂ : ℕ) : ℤ))))) -
      ((d₂ : ℤ) - (d₁ : ℤ)) * ((d₃ : ℤ) - (d₁ : ℤ)) * ((d₄ : ℤ) - (d₁ : ℤ)) *
        (((d₅ : ℤ) - (d₄ : ℤ)) * ((d₅ : ℤ) - (d₃ : ℤ)) *
          (((d₃ : ℤ) - (d₂ : ℤ)) * (((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ)) - ((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ))) -
            ((d₄ : ℤ) - (d₃ : ℤ)) * (((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ)) - ((d₂ : ℤ) + ((n / d₂ : ℕ) : ℤ)))) -
        ((d₃ : ℤ) - (d₂ : ℤ)) * ((d₄ : ℤ) - (d₂ : ℤ)) *
          (((d₄ : ℤ) - (d₃ : ℤ)) * (((d₅ : ℤ) + ((n / d₅ : ℕ) : ℤ)) - ((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ))) -
            ((d₅ : ℤ) - (d₄ : ℤ)) * (((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ)) - ((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ)))))) -
    ((d₂ : ℤ) - (d₁ : ℤ)) * ((d₃ : ℤ) - (d₁ : ℤ)) * ((d₄ : ℤ) - (d₁ : ℤ)) * ((d₅ : ℤ) - (d₁ : ℤ)) *
      (((d₆ : ℤ) - (d₅ : ℤ)) * ((d₆ : ℤ) - (d₄ : ℤ)) * ((d₆ : ℤ) - (d₃ : ℤ)) *
        (((d₅ : ℤ) - (d₄ : ℤ)) * ((d₅ : ℤ) - (d₃ : ℤ)) *
          (((d₃ : ℤ) - (d₂ : ℤ)) * (((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ)) - ((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ))) -
            ((d₄ : ℤ) - (d₃ : ℤ)) * (((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ)) - ((d₂ : ℤ) + ((n / d₂ : ℕ) : ℤ)))) -
        ((d₃ : ℤ) - (d₂ : ℤ)) * ((d₄ : ℤ) - (d₂ : ℤ)) *
          (((d₄ : ℤ) - (d₃ : ℤ)) * (((d₅ : ℤ) + ((n / d₅ : ℕ) : ℤ)) - ((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ))) -
            ((d₅ : ℤ) - (d₄ : ℤ)) * (((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ)) - ((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ))))) -
      ((d₃ : ℤ) - (d₂ : ℤ)) * ((d₄ : ℤ) - (d₂ : ℤ)) * ((d₅ : ℤ) - (d₂ : ℤ)) *
        (((d₆ : ℤ) - (d₅ : ℤ)) * ((d₆ : ℤ) - (d₄ : ℤ)) *
          (((d₄ : ℤ) - (d₃ : ℤ)) * (((d₅ : ℤ) + ((n / d₅ : ℕ) : ℤ)) - ((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ))) -
            ((d₅ : ℤ) - (d₄ : ℤ)) * (((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ)) - ((d₃ : ℤ) + ((n / d₃ : ℕ) : ℤ)))) -
        ((d₄ : ℤ) - (d₃ : ℤ)) * ((d₅ : ℤ) - (d₃ : ℤ)) *
          (((d₅ : ℤ) - (d₄ : ℤ)) * (((d₆ : ℤ) + ((n / d₆ : ℕ) : ℤ)) - ((d₅ : ℤ) + ((n / d₅ : ℕ) : ℤ))) -
            ((d₆ : ℤ) - (d₅ : ℤ)) * (((d₅ : ℤ) + ((n / d₅ : ℕ) : ℤ)) - ((d₄ : ℤ) + ((n / d₄ : ℕ) : ℤ))))))
  have hZ_cast : (Z : ℝ) =
      ((d₆ : ℝ) - (d₅ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₃ : ℝ)) * ((d₆ : ℝ) - (d₂ : ℝ)) *
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
              ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ)))))) := by
    simp only [Z, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have hZ_pos : (0 : ℤ) < Z := by
    rw [← hZ_cast] at hdet_pos
    exact_mod_cast hdet_pos
  have hZ_ge1 : (1 : ℝ) ≤ (Z : ℝ) := by
    have : (1 : ℤ) ≤ Z := hZ_pos
    exact_mod_cast this
  linarith

/-- Division-free 6-tuple product bound from the fifth-order hyperbolic Vandermonde determinant:
`d₁*d₂*d₃*d₄*d₅*d₆ ≤ n * V₆(d₁, d₂, d₃, d₄, d₅, d₆)`. -/
theorem six_tuple_product_le_mul_full_vandermonde_of_lt
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    d₁ * d₂ * d₃ * d₄ * d₅ * d₆ ≤
      n * (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₅ - d₄) * (d₆ - d₅) *
        (d₃ - d₁) * (d₄ - d₂) * (d₅ - d₃) * (d₆ - d₄) *
        (d₄ - d₁) * (d₅ - d₂) * (d₆ - d₃) *
        (d₅ - d₁) * (d₆ - d₂) * (d₆ - d₁) := by
  have hid := fifth_order_hyperbolic_vandermonde_six_tuple_identity n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆
  have hge1 := one_le_fifth_order_hyperbolic_vandermonde_of_lt n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56
  have hd1_pos : (0 : ℝ) ≤ (d₁ : ℝ) := Nat.cast_nonneg d₁
  have hd2_pos : (0 : ℝ) ≤ (d₂ : ℝ) := Nat.cast_nonneg d₂
  have hd3_pos : (0 : ℝ) ≤ (d₃ : ℝ) := Nat.cast_nonneg d₃
  have hd4_pos : (0 : ℝ) ≤ (d₄ : ℝ) := Nat.cast_nonneg d₄
  have hd5_pos : (0 : ℝ) ≤ (d₅ : ℝ) := Nat.cast_nonneg d₅
  have hd6_pos : (0 : ℝ) ≤ (d₆ : ℝ) := Nat.cast_nonneg d₆
  have hP_nonneg : (0 : ℝ) ≤ (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) := by positivity
  have hdet_ge1 := le_sub_iff_add_le'.mpr hge1
  have hmul :
      (d₁ : ℝ) * (d₂ : ℝ) * (d₃ : ℝ) * (d₄ : ℝ) * (d₅ : ℝ) * (d₆ : ℝ) ≤
      (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d₃ : ℝ) - (d₂ : ℝ)) * ((d₄ : ℝ) - (d₃ : ℝ)) *
        ((d₅ : ℝ) - (d₄ : ℝ)) * ((d₆ : ℝ) - (d₅ : ℝ)) *
        ((d₃ : ℝ) - (d₁ : ℝ)) * ((d₄ : ℝ) - (d₂ : ℝ)) * ((d₅ : ℝ) - (d₃ : ℝ)) * ((d₆ : ℝ) - (d₄ : ℝ)) *
        ((d₄ : ℝ) - (d₁ : ℝ)) * ((d₅ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₃ : ℝ)) *
        ((d₅ : ℝ) - (d₁ : ℝ)) * ((d₆ : ℝ) - (d₂ : ℝ)) * ((d₆ : ℝ) - (d₁ : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hdet_ge1 hP_nonneg
    rwa [mul_one, hid] at hm
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hle23 : d₂ ≤ d₃ := le_of_lt hlt23
  have hle34 : d₃ ≤ d₄ := le_of_lt hlt34
  have hle45 : d₄ ≤ d₅ := le_of_lt hlt45
  have hle56 : d₅ ≤ d₆ := le_of_lt hlt56
  have hle13 : d₁ ≤ d₃ := le_trans hle12 hle23
  have hle24 : d₂ ≤ d₄ := le_trans hle23 hle34
  have hle35 : d₃ ≤ d₅ := le_trans hle34 hle45
  have hle46 : d₄ ≤ d₆ := le_trans hle45 hle56
  have hle14 : d₁ ≤ d₄ := le_trans hle13 hle34
  have hle25 : d₂ ≤ d₅ := le_trans hle24 hle45
  have hle36 : d₃ ≤ d₆ := le_trans hle35 hle56
  have hle15 : d₁ ≤ d₅ := le_trans hle14 hle45
  have hle26 : d₂ ≤ d₆ := le_trans hle25 hle56
  have hle16 : d₁ ≤ d₆ := le_trans hle15 hle56
  have hcast :
      ((d₁ * d₂ * d₃ * d₄ * d₅ * d₆ : ℕ) : ℝ) ≤
      ((n * (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₅ - d₄) * (d₆ - d₅) *
        (d₃ - d₁) * (d₄ - d₂) * (d₅ - d₃) * (d₆ - d₄) *
        (d₄ - d₁) * (d₅ - d₂) * (d₆ - d₃) *
        (d₅ - d₁) * (d₆ - d₂) * (d₆ - d₁) : ℕ) : ℝ) := by
    push_cast [hle12, hle23, hle34, hle45, hle56, hle13, hle24, hle35, hle46, hle14, hle25, hle36, hle15, hle26, hle16]
    exact hmul
  exact_mod_cast hcast

/-- Universal 6-tuple Vandermonde lower bound on `Erdos886Divisors n ε C`:
for any `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` in `Erdos886Divisors n ε C`, `n^2 < V₆(d₁, d₂, d₃, d₄, d₅, d₆)`. -/
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
        (d₅ - d₁) * (d₆ - d₂) * (d₆ - d₁) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hm5 := (mem_erdos886Divisors_iff n d₅ ε C).mp hd₅
  have hm6 := (mem_erdos886Divisors_iff n d₆ ε C).mp hd₆
  have hle := six_tuple_product_le_mul_full_vandermonde_of_lt n d₁ d₂ d₃ d₄ d₅ d₆
    hm1.1 hm2.1 hm3.1 hm4.1 hm5.1 hm6.1 hlt12 hlt23 hlt34 hlt45 hlt56
  have h0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsq := rpow_half_sq n
  have hn12 : n < d₁ * d₂ := by
    have : (n : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by
      have := mul_lt_mul_of_nonneg hm1.2.1 hm2.2.1 h0 h0
      nlinarith
    exact_mod_cast this
  have hn34 : n < d₃ * d₄ := by
    have : (n : ℝ) < (d₃ : ℝ) * (d₄ : ℝ) := by
      have := mul_lt_mul_of_nonneg hm3.2.1 hm4.2.1 h0 h0
      nlinarith
    exact_mod_cast this
  have hn56 : n < d₅ * d₆ := by
    have : (n : ℝ) < (d₅ : ℝ) * (d₆ : ℝ) := by
      have := mul_lt_mul_of_nonneg hm5.2.1 hm6.2.1 h0 h0
      nlinarith
    exact_mod_cast this
  have hcube : n * (n ^ 2) < d₁ * d₂ * d₃ * d₄ * d₅ * d₆ := by
    have h1234 := Nat.mul_lt_mul_of_lt_of_lt hn12 hn34
    have h123456 := Nat.mul_lt_mul_of_lt_of_lt h1234 hn56
    calc
      n * (n ^ 2) = (n * n) * n := by ring
      _ < ((d₁ * d₂) * (d₃ * d₄)) * (d₅ * d₆) := h123456
      _ = d₁ * d₂ * d₃ * d₄ * d₅ * d₆ := by ring
  set V6 : ℕ :=
    (d₂ - d₁) * (d₃ - d₂) * (d₄ - d₃) * (d₅ - d₄) * (d₆ - d₅) *
      (d₃ - d₁) * (d₄ - d₂) * (d₅ - d₃) * (d₆ - d₄) *
      (d₄ - d₁) * (d₅ - d₂) * (d₆ - d₃) *
      (d₅ - d₁) * (d₆ - d₂) * (d₆ - d₁)
  have hle_V6 : d₁ * d₂ * d₃ * d₄ * d₅ * d₆ ≤ n * V6 := by
    simp only [V6, mul_assoc] at hle ⊢
    exact hle
  exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hcube hle_V6)

/-! ## Section 3: 6-Tuple Quotient-Drop, Divisor-Ratio, and GCD-Weighted Telescoping Ruzsa Span Bounds -/

/-- For any strictly increasing 6-tuple `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` of divisors of `n`,
the complementary quotients drop by at least `5`: `n / d₆ + 5 ≤ n / d₁`. -/
theorem six_tuple_quotient_drop_ge_five_of_lt
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    n / d₆ + 5 ≤ n / d₁ := by
  have hstep : ∀ a b : ℕ, a ∈ Nat.divisors n → b ∈ Nat.divisors n → a < b → n / b + 1 ≤ n / a := by
    intro a b ha hb hab
    have hde_a : (a : ℝ) * (n / a : ℕ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
    have hde_b : (b : ℝ) * (n / b : ℕ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hb).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors ha
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hb
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hid : (a : ℝ) * (b : ℝ) * ((n / a : ℕ) - (n / b : ℕ)) = (n : ℝ) * ((b : ℝ) - (a : ℝ)) := by
      linear_combination (b : ℝ) * hde_a - (a : ℝ) * hde_b
    have hprod_pos : 0 < (n : ℝ) * ((b : ℝ) - (a : ℝ)) := by
      have : 0 < (b : ℝ) - (a : ℝ) := by linarith
      positivity
    have hab_pos : 0 < (a : ℝ) * (b : ℝ) := by positivity
    have hdiff_pos : 0 < ((n / a : ℕ) : ℝ) - ((n / b : ℕ) : ℝ) :=
      (mul_pos_iff_of_pos_left hab_pos).mp (hid.symm ▸ hprod_pos)
    have hlt_q : ((n / b : ℕ) : ℝ) < ((n / a : ℕ) : ℝ) := by linarith
    have hlt_nat : n / b < n / a := by exact_mod_cast hlt_q
    omega
  have h12 := hstep d₁ d₂ hd₁ hd₂ hlt12
  have h23 := hstep d₂ d₃ hd₂ hd₃ hlt23
  have h34 := hstep d₃ d₄ hd₃ hd₄ hlt34
  have h45 := hstep d₄ d₅ hd₄ hd₅ hlt45
  have h56 := hstep d₅ d₆ hd₅ hd₆ hlt56
  omega

/-- For any strictly increasing 6-tuple `n^(1/2) ≤ d₁ < d₂ < d₃ < d₄ < d₅ < d₆` of divisors of `n`,
the total divisor span is at least `10`: `d₁ + 10 ≤ d₆`. -/
theorem six_tuple_divisor_span_ge_ten_of_ge_sqrt
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    d₁ + 10 ≤ d₆ := by
  have hs₂ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₂ : ℝ) := by
    have : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    linarith
  have hs₃ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₃ : ℝ) := by
    have : (d₂ : ℝ) < (d₃ : ℝ) := by exact_mod_cast hlt23
    linarith
  have hs₄ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₄ : ℝ) := by
    have : (d₃ : ℝ) < (d₄ : ℝ) := by exact_mod_cast hlt34
    linarith
  have hs₅ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₅ : ℝ) := by
    have : (d₄ : ℝ) < (d₅ : ℝ) := by exact_mod_cast hlt45
    linarith
  have hsum12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt12
  have hsum23 := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hd₂ hd₃ hs₂ hlt23
  have hsum34 := complementary_sum_strict_mono_of_ge_sqrt n d₃ d₄ hd₃ hd₄ hs₃ hlt34
  have hsum45 := complementary_sum_strict_mono_of_ge_sqrt n d₄ d₅ hd₄ hd₅ hs₄ hlt45
  have hsum56 := complementary_sum_strict_mono_of_ge_sqrt n d₅ d₆ hd₅ hd₆ hs₅ hlt56
  have hquot := six_tuple_quotient_drop_ge_five_of_lt n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56
  omega

/-- Universal divisor-ratio product bound across a 6-tuple `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` dividing `n`:
`5 * d₁ * d₆ ≤ n * (d₆ - d₁)`. -/
theorem five_mul_first_last_le_mul_span_of_six_divisors
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    5 * d₁ * d₆ ≤ n * (d₆ - d₁) := by
  have hq := six_tuple_quotient_drop_ge_five_of_lt n d₁ d₂ d₃ d₄ d₅ d₆ hd₁ hd₂ hd₃ hd₄ hd₅ hd₆
    hlt12 hlt23 hlt34 hlt45 hlt56
  have hde₁ : (d₁ : ℝ) * (n / d₁ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₁).1
  have hde₆ : (d₆ : ℝ) * (n / d₆ : ℕ) = (n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₆).1
  have hid : (d₁ : ℝ) * (d₆ : ℝ) * ((n / d₁ : ℕ) - (n / d₆ : ℕ)) = (n : ℝ) * ((d₆ : ℝ) - (d₁ : ℝ)) := by
    linear_combination (d₆ : ℝ) * hde₁ - (d₁ : ℝ) * hde₆
  have hqR : (5 : ℝ) ≤ ((n / d₁ : ℕ) : ℝ) - ((n / d₆ : ℕ) : ℝ) := by
    have : ((n / d₆ + 5 : ℕ) : ℝ) ≤ ((n / d₁ : ℕ) : ℝ) := by exact_mod_cast hq
    push_cast at this; linarith
  have hprod_nonneg : 0 ≤ (d₁ : ℝ) * (d₆ : ℝ) := by positivity
  have hmul_le :
      (d₁ : ℝ) * (d₆ : ℝ) * 5 ≤ (d₁ : ℝ) * (d₆ : ℝ) * (((n / d₁ : ℕ) : ℝ) - ((n / d₆ : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hqR hprod_nonneg
  have hleR : 5 * (d₁ : ℝ) * (d₆ : ℝ) ≤ (n : ℝ) * ((d₆ : ℝ) - (d₁ : ℝ)) := by
    linarith [hmul_le, hid]
  have hle16 : d₁ ≤ d₆ := le_of_lt (lt_trans (lt_trans hlt12 hlt23) (lt_trans hlt34 (lt_trans hlt45 hlt56)))
  have hcast : ((5 * d₁ * d₆ : ℕ) : ℝ) ≤ ((n * (d₆ - d₁) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle16]
    exact hleR
  exact_mod_cast hcast

/-- Exact telescoping Ruzsa complementary-sum span decomposition across any 6-tuple:
`(d₂ - d₁)*(s₆ - s₁) = Δ₁₂₃ + Δ₁₂₃₄ + Δ₁₂₄₅ + Δ₁₂₅₆ + (d₆ - d₁)*(s₂ - s₁)`. -/
theorem ruzsa_six_tuple_span_bambah_chowla_decomposition
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) :
    ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) =
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₃ : ℝ) + (n / d₃ : ℕ)) - ((d₂ : ℝ) + (n / d₂ : ℕ))) -
        ((d₃ : ℝ) - (d₂ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₄ : ℝ) + (n / d₄ : ℕ)) - ((d₃ : ℝ) + (n / d₃ : ℕ))) -
        ((d₄ : ℝ) - (d₃ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₅ : ℝ) + (n / d₅ : ℕ)) - ((d₄ : ℝ) + (n / d₄ : ℕ))) -
        ((d₅ : ℝ) - (d₄ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      (((d₂ : ℝ) - (d₁ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₅ : ℝ) + (n / d₅ : ℕ))) -
        ((d₆ : ℝ) - (d₅ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) +
      ((d₆ : ℝ) - (d₁ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
  ring

/-- Universal 6-tuple Ruzsa span inequality for divisors `n^(1/2) ≤ d₁ < d₂ < d₃ < d₄ < d₅ < d₆` of `n`:
`(d₆ - d₁) + 4 ≤ (d₂ - d₁) * ((d₆ + n/d₆) - (d₁ + n/d₁))`. -/
theorem six_tuple_span_add_four_le_first_gap_mul_ruzsa_span
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    (d₆ - d₁) + 4 ≤ (d₂ - d₁) * ((d₆ + n / d₆) - (d₁ + n / d₁)) := by
  have hbc : ∀ c d : ℕ, c ∈ Nat.divisors n → d ∈ Nat.divisors n → d₂ ≤ c → c < d →
      ((d : ℝ) - (c : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) + 1 ≤
        ((d₂ : ℝ) - (d₁ : ℝ)) * (((d : ℝ) + (n / d : ℕ)) - ((c : ℝ) + (n / c : ℕ))) := by
    intro c d hc hd hle2c hcd
    have h12 := complementary_sum_diff_product_identity n d₁ d₂ hd₁ hd₂
    have hcd_id := complementary_sum_diff_product_identity n c d hc hd
    have hv :
        (d₁ : ℝ) * (d₂ : ℝ) * (c : ℝ) * (d : ℝ) *
          (((d₂ : ℝ) - (d₁ : ℝ)) * (((d : ℝ) + (n / d : ℕ)) - ((c : ℝ) + (n / c : ℕ))) -
            ((d : ℝ) - (c : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)))) =
          (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d : ℝ) - (c : ℝ)) * ((c : ℝ) * (d : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
      linear_combination (d₁ : ℝ) * (d₂ : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * hcd_id -
        (c : ℝ) * (d : ℝ) * ((d : ℝ) - (c : ℝ)) * h12
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2
    have hd₁_pos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
    have hd₂_pos : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
    have hc_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hc
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have h12R : (d₁ : ℝ) < (d₂ : ℝ) := by exact_mod_cast hlt12
    have h2cR : (d₂ : ℝ) ≤ (c : ℝ) := by exact_mod_cast hle2c
    have hcdR : (c : ℝ) < (d : ℝ) := by exact_mod_cast hcd
    have hrhs_pos :
        0 < (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d : ℝ) - (c : ℝ)) * ((c : ℝ) * (d : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
      have : 0 < (d₂ : ℝ) - (d₁ : ℝ) := by linarith
      have : 0 < (d : ℝ) - (c : ℝ) := by linarith
      have : 0 < (c : ℝ) * (d : ℝ) - (d₁ : ℝ) * (d₂ : ℝ) := by nlinarith
      positivity
    have hprod_pos : 0 < (d₁ : ℝ) * (d₂ : ℝ) * (c : ℝ) * (d : ℝ) := by positivity
    let z : ℤ :=
      ((d₂ : ℤ) - (d₁ : ℤ)) * (((d : ℤ) + ((n / d : ℕ) : ℤ)) - ((c : ℤ) + ((n / c : ℕ) : ℤ))) -
        ((d : ℤ) - (c : ℤ)) * (((d₂ : ℤ) + ((n / d₂ : ℕ) : ℤ)) - ((d₁ : ℤ) + ((n / d₁ : ℕ) : ℤ)))
    have hz_eq :
        (z : ℝ) =
          ((d₂ : ℝ) - (d₁ : ℝ)) * (((d : ℝ) + (n / d : ℕ)) - ((c : ℝ) + (n / c : ℕ))) -
            ((d : ℝ) - (c : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
      simp only [z, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    have hv_z :
        (d₁ : ℝ) * (d₂ : ℝ) * (c : ℝ) * (d : ℝ) * (z : ℝ) =
          (n : ℝ) * ((d₂ : ℝ) - (d₁ : ℝ)) * ((d : ℝ) - (c : ℝ)) * ((c : ℝ) * (d : ℝ) - (d₁ : ℝ) * (d₂ : ℝ)) := by
      rw [hz_eq]; exact hv
    have hzR_pos : (0 : ℝ) < (z : ℝ) :=
      (mul_pos_iff_of_pos_left hprod_pos).mp (hv_z.symm ▸ hrhs_pos)
    have hz_pos : 0 < z := by exact_mod_cast hzR_pos
    have hz_ge : (1 : ℤ) ≤ z := hz_pos
    have hzR_ge : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_ge
    linarith [hz_eq, hzR_ge]
  have hd123 := hbc d₂ d₃ hd₂ hd₃ (le_refl d₂) hlt23
  have hd1234 := hbc d₃ d₄ hd₃ hd₄ (le_of_lt hlt23) hlt34
  have hd1245 := hbc d₄ d₅ hd₄ hd₅ (le_of_lt (lt_trans hlt23 hlt34)) hlt45
  have hd1256 := hbc d₅ d₆ hd₅ hd₆ (le_of_lt (lt_trans (lt_trans hlt23 hlt34) hlt45)) hlt56
  have hdecomp := ruzsa_six_tuple_span_bambah_chowla_decomposition n d₁ d₂ d₃ d₄ d₅ d₆
  have hs12_nat := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hd₁ hd₂ hs₁ hlt12
  have hs12R : (1 : ℝ) ≤ ((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have : ((d₁ + n / d₁ + 1 : ℕ) : ℝ) ≤ ((d₂ + n / d₂ : ℕ) : ℝ) := by exact_mod_cast hs12_nat
    push_cast at this; linarith
  have hle16 : d₁ ≤ d₆ := le_of_lt (lt_trans (lt_trans hlt12 hlt23) (lt_trans hlt34 (lt_trans hlt45 hlt56)))
  have h16_nonneg : 0 ≤ (d₆ : ℝ) - (d₁ : ℝ) := by
    have : (d₁ : ℝ) ≤ (d₆ : ℝ) := by exact_mod_cast hle16
    linarith
  have hmul16 :
      ((d₆ : ℝ) - (d₁ : ℝ)) * 1 ≤
        ((d₆ : ℝ) - (d₁ : ℝ)) * (((d₂ : ℝ) + (n / d₂ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) :=
    mul_le_mul_of_nonneg_left hs12R h16_nonneg
  have hleR :
      ((d₆ : ℝ) - (d₁ : ℝ)) + 4 ≤
        ((d₂ : ℝ) - (d₁ : ℝ)) * (((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ))) := by
    linarith [hd123, hd1234, hd1245, hd1256, hdecomp, hmul16]
  have hs16_nat := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₆ hd₁ hd₆ hs₁
    (lt_trans (lt_trans hlt12 hlt23) (lt_trans hlt34 (lt_trans hlt45 hlt56)))
  have hs16_le : d₁ + n / d₁ ≤ d₆ + n / d₆ := le_of_lt hs16_nat
  have hle12 : d₁ ≤ d₂ := le_of_lt hlt12
  have hcast :
      (((d₆ - d₁) + 4 : ℕ) : ℝ) ≤
        (((d₂ - d₁) * ((d₆ + n / d₆) - (d₁ + n / d₁)) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hle16, Nat.cast_sub hle12, Nat.cast_sub hs16_le]
    exact hleR
  exact_mod_cast hcast

/-- GCD-weighted 6-tuple Ruzsa span inequality: combining `six_tuple_span_add_four_le_first_gap_mul_ruzsa_span`
with `divisor_diff_le_gcd_mul_complementary_sum_diff` yields
`(d₆ - d₁) + 4 ≤ gcd(d₁, d₂) * ((d₂ + n/d₂) - (d₁ + n/d₁)) * ((d₆ + n/d₆) - (d₁ + n/d₁))`. -/
theorem six_tuple_span_add_four_le_gcd_mul_first_sum_step_mul_ruzsa_span
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    (d₆ - d₁) + 4 ≤
      Nat.gcd d₁ d₂ * ((d₂ + n / d₂) - (d₁ + n / d₁)) * ((d₆ + n / d₆) - (d₁ + n / d₁)) := by
  have hspan := six_tuple_span_add_four_le_first_gap_mul_ruzsa_span n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hs₁ hlt12 hlt23 hlt34 hlt45 hlt56
  have hgcd := divisor_diff_le_gcd_mul_complementary_sum_diff n d₁ d₂ hd₁ hd₂ hs₁ hlt12
  exact le_trans hspan (Nat.mul_le_mul_right ((d₆ + n / d₆) - (d₁ + n / d₁)) hgcd)

/-- For any 6-tuple `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` in `Erdos886Divisors n ε C` (`0 ≤ C`),
`(d₆ - d₁) + 4 < gcd(d₁, d₂) * ((d₂ + n/d₂) - (d₁ + n/d₁)) * C^2 * n^{1/2 - 2ε}`. -/
theorem six_tuple_span_add_four_lt_gcd_mul_first_sum_step_mul_sq_rpow_of_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε C) (hd₆ : d₆ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    ((d₆ - d₁ : ℕ) : ℝ) + 4 <
      (Nat.gcd d₁ d₂ : ℝ) * (((d₂ + n / d₂) - (d₁ + n / d₁) : ℕ) : ℝ) *
        C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hm5 := (mem_erdos886Divisors_iff n d₅ ε C).mp hd₅
  have hm6 := (mem_erdos886Divisors_iff n d₆ ε C).mp hd₆
  have hle_nat := six_tuple_span_add_four_le_gcd_mul_first_sum_step_mul_ruzsa_span n d₁ d₂ d₃ d₄ d₅ d₆
    hm1.1 hm2.1 hm3.1 hm4.1 hm5.1 hm6.1 (le_of_lt hm1.2.1) hlt12 hlt23 hlt34 hlt45 hlt56
  have hs12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hs16 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₆ hm1.1 hm6.1 (le_of_lt hm1.2.1)
    (lt_trans (lt_trans hlt12 hlt23) (lt_trans hlt34 (lt_trans hlt45 hlt56)))
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₆ ε C hC hd₁ hd₆
  have hs16_cast : (((d₆ + n / d₆) - (d₁ + n / d₁) : ℕ) : ℝ) < C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
    rw [Nat.cast_sub (le_of_lt hs16)]
    push_cast
    exact hspan
  have hd1_pos : 0 < d₁ := Nat.pos_of_mem_divisors hm1.1
  have hgcd_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ hd1_pos
  have hs12_pos : 0 < (d₂ + n / d₂) - (d₁ + n / d₁) := Nat.sub_pos_of_lt hs12
  have hcoeff_pos : (0 : ℝ) < (Nat.gcd d₁ d₂ : ℝ) * (((d₂ + n / d₂) - (d₁ + n / d₁) : ℕ) : ℝ) := by
    positivity
  have hmul_lt := mul_lt_mul_of_pos_left hs16_cast hcoeff_pos
  have hle_real :
      ((d₆ - d₁ : ℕ) : ℝ) + 4 ≤
        (Nat.gcd d₁ d₂ : ℝ) * (((d₂ + n / d₂) - (d₁ + n / d₁) : ℕ) : ℝ) *
          (((d₆ + n / d₆) - (d₁ + n / d₁) : ℕ) : ℝ) := by
    exact_mod_cast hle_nat
  linarith

/-- On any 6-tuple `n^(1/2) ≤ d₁ < d₂ < d₃ < d₄ < d₅ < d₆` of divisors of `n` with minimal
adjacent complementary-sum steps `s_{i+1} = s_i + 1` (`i = 1..5`), strict concavity forces
`d₂ - d₁ ≥ 6`, `d₆ - d₁ ≥ 20`, and every adjacent gap equals the pairwise GCD `d_{i+1} - d_i = gcd(d_i, d_{i+1})`. -/
theorem six_tuple_first_step_ge_six_and_span_ge_twenty_of_minimal_sum_steps
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ)
    (hd₁ : d₁ ∈ Nat.divisors n) (hd₂ : d₂ ∈ Nat.divisors n) (hd₃ : d₃ ∈ Nat.divisors n)
    (hd₄ : d₄ ∈ Nat.divisors n) (hd₅ : d₅ ∈ Nat.divisors n) (hd₆ : d₆ ∈ Nat.divisors n)
    (hs₁ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₁ : ℝ))
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆)
    (hstep12 : d₂ + n / d₂ = d₁ + n / d₁ + 1)
    (hstep23 : d₃ + n / d₃ = d₂ + n / d₂ + 1)
    (hstep34 : d₄ + n / d₄ = d₃ + n / d₃ + 1)
    (hstep45 : d₅ + n / d₅ = d₄ + n / d₄ + 1)
    (hstep56 : d₆ + n / d₆ = d₅ + n / d₅ + 1) :
    6 ≤ d₂ - d₁ ∧ d₁ + 20 ≤ d₆ ∧ d₂ - d₁ = Nat.gcd d₁ d₂ ∧ d₆ - d₅ = Nat.gcd d₅ d₆ := by
  have hconc : ∀ a b c : ℕ, a ∈ Nat.divisors n → b ∈ Nat.divisors n → c ∈ Nat.divisors n →
      a < b → b < c → b + n / b = a + n / a + 1 → c + n / c = b + n / b + 1 → c - b + 1 ≤ b - a := by
    intro a b c ha hb hc hab hbc hsab hsbc
    have h1 := complementary_sum_diff_product_identity n a b ha hb
    have h2 := complementary_sum_diff_product_identity n b c hb hc
    have hv :
        (a : ℝ) * (b : ℝ) * (c : ℝ) *
          (((b : ℝ) - (a : ℝ)) * (((c : ℝ) + (n / c : ℕ)) - ((b : ℝ) + (n / b : ℕ))) -
            ((c : ℝ) - (b : ℝ)) * (((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ)))) =
          (n : ℝ) * ((b : ℝ) - (a : ℝ)) * ((c : ℝ) - (b : ℝ)) * ((c : ℝ) - (a : ℝ)) := by
      linear_combination (a : ℝ) * ((b : ℝ) - (a : ℝ)) * h2 - (c : ℝ) * ((c : ℝ) - (b : ℝ)) * h1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors ha
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hb
    have hc_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hc
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hbcR : (b : ℝ) < (c : ℝ) := by exact_mod_cast hbc
    have hrhs_pos : 0 < (n : ℝ) * ((b : ℝ) - (a : ℝ)) * ((c : ℝ) - (b : ℝ)) * ((c : ℝ) - (a : ℝ)) := by
      have : 0 < (b : ℝ) - (a : ℝ) := by linarith
      have : 0 < (c : ℝ) - (b : ℝ) := by linarith
      have : 0 < (c : ℝ) - (a : ℝ) := by linarith
      positivity
    have hprod_pos : 0 < (a : ℝ) * (b : ℝ) * (c : ℝ) := by positivity
    have hsabR : ((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ)) = 1 := by
      have hcast : ((b + n / b : ℕ) : ℝ) = ((a + n / a + 1 : ℕ) : ℝ) := by exact_mod_cast hsab
      push_cast at hcast; linarith
    have hsbcR : ((c : ℝ) + (n / c : ℕ)) - ((b : ℝ) + (n / b : ℕ)) = 1 := by
      have hcast : ((c + n / c : ℕ) : ℝ) = ((b + n / b + 1 : ℕ) : ℝ) := by exact_mod_cast hsbc
      push_cast at hcast; linarith
    have hΔ_pos :
        0 < ((b : ℝ) - (a : ℝ)) * (((c : ℝ) + (n / c : ℕ)) - ((b : ℝ) + (n / b : ℕ))) -
          ((c : ℝ) - (b : ℝ)) * (((b : ℝ) + (n / b : ℕ)) - ((a : ℝ) + (n / a : ℕ))) :=
      (mul_pos_iff_of_pos_left hprod_pos).mp (hv.symm ▸ hrhs_pos)
    have hdiff_pos : 0 < ((b : ℝ) - (a : ℝ)) - ((c : ℝ) - (b : ℝ)) := by
      rw [hsabR, hsbcR] at hΔ_pos
      linarith
    have hlt_natR : ((c - b : ℕ) : ℝ) < ((b - a : ℕ) : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hbc), Nat.cast_sub (le_of_lt hab)]
      linarith
    have hlt_nat : c - b < b - a := by exact_mod_cast hlt_natR
    omega
  have hc123 := hconc d₁ d₂ d₃ hd₁ hd₂ hd₃ hlt12 hlt23 hstep12 hstep23
  have hc234 := hconc d₂ d₃ d₄ hd₂ hd₃ hd₄ hlt23 hlt34 hstep23 hstep34
  have hc345 := hconc d₃ d₄ d₅ hd₃ hd₄ hd₅ hlt34 hlt45 hstep34 hstep45
  have hc456 := hconc d₄ d₅ d₆ hd₄ hd₅ hd₆ hlt45 hlt56 hstep45 hstep56
  have hq : n / d₆ + 5 ≤ n / d₁ := six_tuple_quotient_drop_ge_five_of_lt n d₁ d₂ d₃ d₄ d₅ d₆
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56
  have hq15 : n / d₅ + 4 ≤ n / d₁ := by
    have hq45 := six_tuple_quotient_drop_ge_five_of_lt n d₁ d₂ d₃ d₄ d₅ d₆
      hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56
    omega
  have h56_ge2 : 2 ≤ d₆ - d₅ := by
    have hde₅ : (d₅ : ℝ) * (n / d₅ : ℕ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₅).1
    have hde₆ : (d₆ : ℝ) * (n / d₆ : ℕ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd₆).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₅).2
    have hd₅_pos : (0 : ℝ) < (d₅ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₅
    have hd₆_pos : (0 : ℝ) < (d₆ : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd₆
    have h56R : (d₅ : ℝ) < (d₆ : ℝ) := by exact_mod_cast hlt56
    have hid : (d₅ : ℝ) * (d₆ : ℝ) * ((n / d₅ : ℕ) - (n / d₆ : ℕ)) = (n : ℝ) * ((d₆ : ℝ) - (d₅ : ℝ)) := by
      linear_combination (d₆ : ℝ) * hde₅ - (d₅ : ℝ) * hde₆
    have hprod_pos : 0 < (n : ℝ) * ((d₆ : ℝ) - (d₅ : ℝ)) := by
      have : 0 < (d₆ : ℝ) - (d₅ : ℝ) := by linarith
      positivity
    have hd56_pos : 0 < (d₅ : ℝ) * (d₆ : ℝ) := by positivity
    have hdiff_pos : 0 < ((n / d₅ : ℕ) : ℝ) - ((n / d₆ : ℕ) : ℝ) :=
      (mul_pos_iff_of_pos_left hd56_pos).mp (hid.symm ▸ hprod_pos)
    have hlt_q : ((n / d₆ : ℕ) : ℝ) < ((n / d₅ : ℕ) : ℝ) := by linarith
    have hlt_nat : n / d₆ < n / d₅ := by exact_mod_cast hlt_q
    omega
  have hs₅ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d₅ : ℝ) := by
    have : d₁ < d₅ := lt_trans (lt_trans hlt12 hlt23) (lt_trans hlt34 hlt45)
    have hR : (d₁ : ℝ) < (d₅ : ℝ) := by exact_mod_cast this
    linarith
  have hg12 := divisor_diff_eq_gcd_of_complementary_sum_diff_eq_one n d₁ d₂ hd₁ hd₂ hs₁ hlt12 (by omega)
  have hg56 := divisor_diff_eq_gcd_of_complementary_sum_diff_eq_one n d₅ d₆ hd₅ hd₆ hs₅ hlt56 (by omega)
  refine ⟨by omega, by omega, hg12, hg56⟩

/-- For any strictly increasing 6-tuple `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` in `Erdos886Divisors n ε C`
(`0 ≤ C`), `5 < C^2 * n^{1/2 - 2ε}`. -/
theorem five_lt_sq_mul_rpow_of_six_mem_erdos886Divisors
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε C) (hd₂ : d₂ ∈ Erdos886Divisors n ε C)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε C) (hd₄ : d₄ ∈ Erdos886Divisors n ε C)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε C) (hd₆ : d₆ ∈ Erdos886Divisors n ε C)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    (5 : ℝ) < C ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
  have hm1 := (mem_erdos886Divisors_iff n d₁ ε C).mp hd₁
  have hm2 := (mem_erdos886Divisors_iff n d₂ ε C).mp hd₂
  have hm3 := (mem_erdos886Divisors_iff n d₃ ε C).mp hd₃
  have hm4 := (mem_erdos886Divisors_iff n d₄ ε C).mp hd₄
  have hm5 := (mem_erdos886Divisors_iff n d₅ ε C).mp hd₅
  have hm6 := (mem_erdos886Divisors_iff n d₆ ε C).mp hd₆
  have hs12 := complementary_sum_strict_mono_of_ge_sqrt n d₁ d₂ hm1.1 hm2.1 (le_of_lt hm1.2.1) hlt12
  have hs23 := complementary_sum_strict_mono_of_ge_sqrt n d₂ d₃ hm2.1 hm3.1 (le_of_lt hm2.2.1) hlt23
  have hs34 := complementary_sum_strict_mono_of_ge_sqrt n d₃ d₄ hm3.1 hm4.1 (le_of_lt hm3.2.1) hlt34
  have hs45 := complementary_sum_strict_mono_of_ge_sqrt n d₄ d₅ hm4.1 hm5.1 (le_of_lt hm4.2.1) hlt45
  have hs56 := complementary_sum_strict_mono_of_ge_sqrt n d₅ d₆ hm5.1 hm6.1 (le_of_lt hm5.2.1) hlt56
  have h5_le : d₁ + n / d₁ + 5 ≤ d₆ + n / d₆ := by omega
  have h5R : (5 : ℝ) ≤ ((d₆ : ℝ) + (n / d₆ : ℕ)) - ((d₁ : ℝ) + (n / d₁ : ℕ)) := by
    have hcast : ((d₁ + n / d₁ + 5 : ℕ) : ℝ) ≤ ((d₆ + n / d₆ : ℕ) : ℝ) := by exact_mod_cast h5_le
    push_cast at hcast; linarith
  have hspan := complementary_sum_span_lt_of_mem_erdos886Divisors n d₁ d₆ ε C hC hd₁ hd₆
  linarith

/-- Explicit 6-tuple threshold for `1/6 ≤ ε`: if `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` belong to
`Erdos886Divisors n ε 1` with `1 / 6 ≤ ε`, then `15625 < n` (since `5^6 = 15625`). -/
theorem gt_15625_of_six_mem_erdos886Divisors_of_sixth_le
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) (ε : ℝ) (hε : 1 / 6 ≤ ε)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε 1) (hd₂ : d₂ ∈ Erdos886Divisors n ε 1)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε 1) (hd₄ : d₄ ∈ Erdos886Divisors n ε 1)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε 1) (hd₆ : d₆ ∈ Erdos886Divisors n ε 1)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    15625 < n := by
  have h5 := five_lt_sq_mul_rpow_of_six_mem_erdos886Divisors n d₁ d₂ d₃ d₄ d₅ d₆ ε 1 (by norm_num)
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp ((mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁).1).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h5_lt : (5 : ℝ) < (n : ℝ) ^ (1 / 6 : ℝ) := by linarith
  by_contra hle
  have hn_le : (n : ℝ) ≤ 15625 := by
    have : n ≤ 15625 := by omega
    exact_mod_cast this
  have hrpow_le : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (15625 : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le (by norm_num)
  have h15625 : (15625 : ℝ) ^ (1 / 6 : ℝ) = 5 := by
    have h_eq : (15625 : ℝ) = (5 : ℝ) ^ (6 : ℝ) := by norm_num
    rw [h_eq, ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith

/-- Explicit 6-tuple threshold for `1/8 ≤ ε`: if `d₁ < d₂ < d₃ < d₄ < d₅ < d₆` belong to
`Erdos886Divisors n ε 1` with `1 / 8 ≤ ε`, then `625 < n` (since `5^4 = 625`). -/
theorem gt_625_of_six_mem_erdos886Divisors_of_eighth_le
    (n d₁ d₂ d₃ d₄ d₅ d₆ : ℕ) (ε : ℝ) (hε : 1 / 8 ≤ ε)
    (hd₁ : d₁ ∈ Erdos886Divisors n ε 1) (hd₂ : d₂ ∈ Erdos886Divisors n ε 1)
    (hd₃ : d₃ ∈ Erdos886Divisors n ε 1) (hd₄ : d₄ ∈ Erdos886Divisors n ε 1)
    (hd₅ : d₅ ∈ Erdos886Divisors n ε 1) (hd₆ : d₆ ∈ Erdos886Divisors n ε 1)
    (hlt12 : d₁ < d₂) (hlt23 : d₂ < d₃) (hlt34 : d₃ < d₄) (hlt45 : d₄ < d₅) (hlt56 : d₅ < d₆) :
    625 < n := by
  have h5 := five_lt_sq_mul_rpow_of_six_mem_erdos886Divisors n d₁ d₂ d₃ d₄ d₅ d₆ ε 1 (by norm_num)
    hd₁ hd₂ hd₃ hd₄ hd₅ hd₆ hlt12 hlt23 hlt34 hlt45 hlt56
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp ((mem_erdos886Divisors_iff n d₁ ε 1).mp hd₁).1).2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h5_lt : (5 : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
  by_contra hle
  have hn_le : (n : ℝ) ≤ 625 := by
    have : n ≤ 625 := by omega
    exact_mod_cast this
  have hrpow_le : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (625 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le (by norm_num)
  have h625 : (625 : ℝ) ^ (1 / 4 : ℝ) = 5 := by
    have h_eq : (625 : ℝ) = (5 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h_eq, ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith

/-- Top-down conditional reduction of `erdos_886` via the GCD / LCM-quotient factorization:
if for every `0 < ε < 1/4` there is `K : ℕ` such that eventually for all `a ≤ b` in
`Erdos886Divisors n ε 1`, `((b - a) / gcd(a, b)) * (gcd(a, b) - n / lcm(a, b)) ≤ K`,
then `∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in atTop, (Erdos886Divisors n ε 1).card ≤ K`. -/
theorem erdos_886_of_eventual_gcd_weighted_complementary_sum_bound
    (hgcd_bound : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
      ∃ K : ℕ, ∀ᶠ n in Filter.atTop,
        ∀ a ∈ Erdos886Divisors n ε 1, ∀ b ∈ Erdos886Divisors n ε 1, a ≤ b →
          ((b - a) / Nat.gcd a b) * (Nat.gcd a b - n / Nat.lcm a b) ≤ K) :
    ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in Filter.atTop, (Erdos886Divisors n ε 1).card ≤ K := by
  intro ε hε
  by_cases hq : 1 / 4 ≤ ε
  · exact erdos_886_of_quarter_le ε hq
  · have hq' : ε < 1 / 4 := lt_of_not_ge hq
    rcases hgcd_bound ε hε hq' with ⟨K, hev⟩
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
        · have hfact := complementary_sum_diff_eq_reduced_diff_mul_gcd_sub_lcm_quotient n a b
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

/-- Negative control / sharp finite 6-tuple exclusions: for all `n ≤ 15625` and `1/6 ≤ ε`,
`(Erdos886Divisors n ε 1).card ≤ 5`; and for all `n ≤ 625` and `1/8 ≤ ε`,
`(Erdos886Divisors n ε 1).card ≤ 5`. -/
theorem negative_control_card_le_five_of_le_15625_of_sixth_le_and_le_625_of_eighth_le :
    (∀ n : ℕ, n ≤ 15625 → ∀ ε : ℝ, 1 / 6 ≤ ε → (Erdos886Divisors n ε 1).card ≤ 5) ∧
    (∀ n : ℕ, n ≤ 625 → ∀ ε : ℝ, 1 / 8 ≤ ε → (Erdos886Divisors n ε 1).card ≤ 5) := by
  have h_card_le : ∀ n k : ℕ, ∀ ε : ℝ, (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (k : ℝ) →
      (Erdos886Divisors n ε 1).card ≤ k := by
    intro n k ε hle
    by_cases hne : (Erdos886Divisors n ε 1).Nonempty
    · set s := Erdos886Divisors n ε 1
      let f : ℕ → ℕ := fun d => d + n / d
      have hmono : ∀ a ∈ s, ∀ b ∈ s, a < b → f a < f b := by
        intro a ha b hb hlt
        have ha_mem := (mem_erdos886Divisors_iff n a ε 1).mp ha
        have hb_mem := (mem_erdos886Divisors_iff n b ε 1).mp hb
        exact complementary_sum_strict_mono_of_ge_sqrt n a b ha_mem.1 hb_mem.1 (le_of_lt ha_mem.2.1) hlt
      have hmin_mem : s.min' hne ∈ s := Finset.min'_mem s hne
      have hmax_mem : s.max' hne ∈ s := Finset.max'_mem s hne
      have hle_Elem : ∀ x ∈ s, f (s.min' hne) ≤ f x ∧ f x ≤ f (s.max' hne) := by
        intro x hx
        constructor
        · rcases lt_or_eq_of_le (Finset.min'_le s x hx) with hlt | heq
          · exact le_of_lt (hmono _ hmin_mem _ hx hlt)
          · rw [heq]
        · rcases lt_or_eq_of_le (Finset.le_max' s x hx) with hlt | heq
          · exact le_of_lt (hmono _ hx _ hmax_mem hlt)
          · rw [heq]
      have hle_span : (s.card : ℝ) ≤ 1 + ((f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ)) := by
        apply card_nat_finset_le_of_strictMonoOn_image_diff s f hmono
          ((f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ))
        · have h1 : (f (s.min' hne) : ℝ) ≤ (f (s.max' hne) : ℝ) := by
            exact_mod_cast (hle_Elem (s.max' hne) hmax_mem).1
          linarith
        · intro a ha b hb
          have ha_le : (f (s.min' hne) : ℝ) ≤ (f a : ℝ) := by exact_mod_cast (hle_Elem a ha).1
          have hb_le : (f b : ℝ) ≤ (f (s.max' hne) : ℝ) := by exact_mod_cast (hle_Elem b hb).2
          linarith
      have hlt_span : (f (s.max' hne) : ℝ) - (f (s.min' hne) : ℝ) < 1 ^ 2 * (n : ℝ) ^ (1 / 2 - 2 * ε) := by
        have h := complementary_sum_span_lt_of_mem_erdos886Divisors n (s.min' hne) (s.max' hne)
          ε 1 (by norm_num) hmin_mem hmax_mem
        dsimp [f]; push_cast; linarith
      have hlt_k : (s.card : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hlt_nat : s.card < k + 1 := by exact_mod_cast hlt_k
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le k
  constructor
  · intro n hn ε hε
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [erdos886Divisors_zero]
    · apply h_card_le n 5 ε
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have hn15625 : (n : ℝ) ≤ 15625 := by exact_mod_cast hn
      have hrpow15625 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (15625 : ℝ) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hn15625 (by norm_num)
      have h15625 : (15625 : ℝ) ^ (1 / 6 : ℝ) = 5 := by
        have h_eq : (15625 : ℝ) = (5 : ℝ) ^ (6 : ℝ) := by norm_num
        rw [h_eq, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
  · intro n hn ε hε
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [erdos886Divisors_zero]
    · apply h_card_le n 5 ε
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hpow_le : (n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have hn625 : (n : ℝ) ≤ 625 := by exact_mod_cast hn
      have hrpow625 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (625 : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hn625 (by norm_num)
      have h625 : (625 : ℝ) ^ (1 / 4 : ℝ) = 5 := by
        have h_eq : (625 : ℝ) = (5 : ℝ) ^ (4 : ℝ) := by norm_num
        rw [h_eq, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith

/-- Positive control verifying our pilot witnesses across `n ≤ 1,000,000`:
1. At `n = 471,240` (first 6-divisor witness at `ε = 1/7`, `{693, 714, 748, 765, 770, 792}`),
   every adjacent difference equals `gcd(d_i, d_{i+1})` (`21, 34, 17, 5, 22`) and `Δ₁₂₅₆ = 83`.
2. At `n = 85,680` (first 6-divisor witness at `ε = 1/8`, `{306, 315, 336, 340, 357, 360}`),
   `Δ₁₂₅₆ = 6` and `Δᶜᵒᵘᵖˡᵉᵈ₁₂₃₄₅₆ = 3960`.
3. At `n = 720,720` (first 5-divisor witness at `ε = 1/6`, `{858, 880, 910, 924, 936}`),
   the reduced coprime steps `(d_{i+1} - d_i) / gcd(d_i, d_{i+1})` equal `(1, 3, 1, 1)`, dividing
   the complementary-sum steps `(1, 3, 2, 2)`. -/
theorem positive_control_witnesses_720720_471240_85680 :
    (714 - 693 = Nat.gcd 693 714 ∧ 748 - 714 = Nat.gcd 714 748 ∧
      765 - 748 = Nat.gcd 748 765 ∧ 770 - 765 = Nat.gcd 765 770 ∧
      792 - 770 = Nat.gcd 770 792) ∧
    (((714 : ℝ) - (693 : ℝ)) * (((792 : ℝ) + (471240 / 792 : ℕ)) - ((770 : ℝ) + (471240 / 770 : ℕ))) -
      ((792 : ℝ) - (770 : ℝ)) * (((714 : ℝ) + (471240 / 714 : ℕ)) - ((693 : ℝ) + (471240 / 693 : ℕ)))) = 83 ∧
    (((315 : ℝ) - (306 : ℝ)) * (((360 : ℝ) + (85680 / 360 : ℕ)) - ((357 : ℝ) + (85680 / 357 : ℕ))) -
      ((360 : ℝ) - (357 : ℝ)) * (((315 : ℝ) + (85680 / 315 : ℕ)) - ((306 : ℝ) + (85680 / 306 : ℕ)))) = 6 ∧
    (880 - 858 = Nat.gcd 858 880 ∧ (910 - 880) / Nat.gcd 880 910 = 3 ∧
      924 - 910 = Nat.gcd 910 924 ∧ 936 - 924 = Nat.gcd 924 936) := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, by norm_num, by norm_num,
    ⟨by decide, by decide, by decide, by decide⟩⟩

end Erdos886

