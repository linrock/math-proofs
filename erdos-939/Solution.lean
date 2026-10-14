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

public import PowerfulSumsAndNitaj939
public import AbcQualityAndCohnRecurrence939
public import Blueprint939

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos939.Palomar

open Nat Erdos939

theorem erdos_939_variants_finite: False ↔ ∀ r ≥ 4, (Erdos939Sums r).Finite :=
  Erdos939.erdos_939_variants_finite

theorem erdos_939_variants_infinite_of_six_le: ∀ r ≥ 6, (Erdos939Sums r).Infinite :=
  Erdos939.erdos_939_variants_infinite_of_six_le

theorem erdos_939_variants_triples: True ↔ {(a, b, c) | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧ (3).Full a ∧ (3).Full b ∧ (3).Full c ∧ a + b = c}.Infinite :=
  Erdos939.erdos_939_variants_triples

theorem erdos_939_variants_examples: ∃ r ≥ 4, (Erdos939Sums r).Nonempty :=
  Erdos939.erdos_939_variants_examples

theorem erdos_939_variants_seven: (Erdos939Sums 7).Nonempty :=
  Erdos939.erdos_939_variants_seven

theorem erdos_939_variants_eight: (Erdos939Sums 8).Nonempty :=
  Erdos939.erdos_939_variants_eight

theorem erdos_939_variants_euler: ¬ (∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
      (∀ s ∈ S, 0 < s) → ¬ (∃ q, ∑ s ∈ S, s ^ k = q ^ k)) :=
  Erdos939.erdos_939_variants_euler

theorem erdos_939_variants_triples_infinite: {(a, b, c) : ℕ × ℕ × ℕ | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧ (3).Full a ∧ (3).Full b ∧ (3).Full c ∧ a + b = c}.Infinite :=
  Erdos939.erdos_939_variants_triples_infinite

theorem cohn_noncube_triples_infinite: {(a, b, c) : ℕ × ℕ × ℕ | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧ (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      (∀ k : ℕ, k ^ 3 ≠ a) ∧ (∀ k : ℕ, k ^ 3 ≠ b) ∧ (∀ k : ℕ, k ^ 3 ≠ c) ∧
      a + b = c}.Infinite :=
  Erdos939.cohn_noncube_triples_infinite

theorem cohn_noncube_generalSums_three_two_infinite: {S : Finset ℕ | S ∈ Erdos939GeneralSums 3 2 ∧
      (∀ k : ℕ, k ^ 3 ≠ ∑ s ∈ S, s) ∧
      ∀ s ∈ S, ∀ k : ℕ, k ^ 3 ≠ s}.Infinite :=
  Erdos939.cohn_noncube_generalSums_three_two_infinite

theorem erdos_939_generalSums_three_two_infinite: (Erdos939GeneralSums 3 2).Infinite :=
  Erdos939.erdos_939_generalSums_three_two_infinite

theorem cambieFiveSet_mem_erdos939Sums_five: cambieFiveSet ∈ Erdos939Sums 5 ∧ ∑ s ∈ cambieFiveSet, s = 3 ^ 7 * 61 ^ 5 :=
  ⟨Erdos939.cambieFiveSet_mem_erdos939Sums_five_and_controls.1, Erdos939.cambieFiveSet_mem_erdos939Sums_five_and_controls.2.1⟩

theorem landerParkinFiveSet_mem_erdos939GeneralSums_five_four: landerParkinFiveSet ∈ Erdos939GeneralSums 5 4 ∧ ∑ s ∈ landerParkinFiveSet, s = 144 ^ 5 :=
  Erdos939.landerParkinFiveSet_mem_erdos939GeneralSums_five_four

theorem r_full_iff_exists_squarefree_cores (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    r.Full n ↔
      ∃ (u : ℕ) (v : ℕ → ℕ),
        (∀ j ∈ Finset.Ico 1 r, Squarefree (v j)) ∧
        (∀ j₁ ∈ Finset.Ico 1 r, ∀ j₂ ∈ Finset.Ico 1 r, j₁ ≠ j₂ → Nat.Coprime (v j₁) (v j₂)) ∧
        u ^ r * ∏ j ∈ Finset.Ico 1 r, (v j) ^ (r + j) = n :=
  Erdos939.r_full_iff_exists_squarefree_cores r n hr hn

theorem rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums {r : ℕ} (hr : 4 ≤ r) {S : Finset ℕ} (hS : S ∈ Erdos939Sums r) :
    rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ≤ (∏ s ∈ S, s) * (∑ s ∈ S, s) ∧
      (∏ s ∈ S, s) * (∑ s ∈ S, s) < (∑ s ∈ S, s) ^ (r - 1) ∧
      rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r < (∑ s ∈ S, s) ^ (r - 1) :=
  Erdos939.rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums hr hS

theorem abc_quality_real_bound_of_mem_erdos939Sums {r : ℕ} (hr : 4 ≤ r) {S : Finset ℕ} (hS : S ∈ Erdos939Sums r) :
    ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) * Real.log (rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) : ℝ) <
      Real.log ((∑ s ∈ S, s : ℕ) : ℝ) :=
  Erdos939.abc_quality_real_bound_of_mem_erdos939Sums hr hS

theorem rad_pow_four_le_and_lt_cube_of_mem_erdos939Sums_four {a b : ℕ} (hmem : ({a, b} : Finset ℕ) ∈ Erdos939Sums 4) :
    rad (a * b * (a + b)) ^ 4 ∣ a * b * (a + b) ∧
    rad (a * b * (a + b)) ^ 4 ≤ a * b * (a + b) ∧
    a * b * (a + b) < (a + b) ^ 3 ∧
    4 * rad (a * b * (a + b)) ^ 4 < (a + b) ^ 3 ∧
    rad (a * b * (a + b)) ^ 4 < (a + b) ^ 3 :=
  Erdos939.rad_pow_four_le_and_lt_cube_of_mem_erdos939Sums_four hmem

theorem walsh_twist_pair_mem_erdos939GeneralSums_three_two {d₁ x₁ d₂ x₂ d₃ x₃ : ℕ}
    (hd₁ : 0 < d₁) (hx₁ : 0 < x₁) (hd₂ : 0 < d₂) (hx₂ : 0 < x₂) (hd₃ : 0 < d₃)
    (hr₁ : rad d₁ ∣ x₁) (hr₂ : rad d₂ ∣ x₂) (hr₃ : rad d₃ ∣ x₃)
    (hcop : Nat.Coprime (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3))
    (hsum : d₁ ^ 2 * x₁ ^ 3 + d₂ ^ 2 * x₂ ^ 3 = d₃ ^ 2 * x₃ ^ 3) :
    ({d₁ ^ 2 * x₁ ^ 3, d₂ ^ 2 * x₂ ^ 3} : Finset ℕ) ∈ Erdos939GeneralSums 3 2 :=
  Erdos939.walsh_twist_pair_mem_erdos939GeneralSums_three_two hd₁ hx₁ hd₂ hx₂ hd₃ hr₁ hr₂ hr₃ hcop hsum

theorem walsh_parametric_cube_scaling_coprime_iff {a b d : ℕ} (hd : 0 < d) (hcop : Nat.Coprime a b) :
    Nat.Coprime (d ^ 3 * a) (d ^ 3 * b) ↔ d = 1 :=
  Erdos939.walsh_parametric_cube_scaling_coprime_iff hd hcop

theorem erdos_939_iff_four_nonempty: (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔ (Erdos939Sums 4).Nonempty :=
  Erdos939.erdos_939_iff_four_nonempty

theorem erdos_939_iff_exists_coprime_four_full_pair: (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
        (4).Full a ∧ (4).Full b ∧ (4).Full (a + b) :=
  Erdos939.erdos_939_iff_exists_coprime_four_full_pair

theorem erdos939Sums_four_finite_of_abc_seven_sixths_bound {K : ℕ} (habc : ∀ x y : ℕ, 0 < x → 0 < y → Nat.Coprime x y →
      (x + y) ^ 6 ≤ K * rad (x * y * (x + y)) ^ 7) :
    (Erdos939Sums 4).Finite :=
  Erdos939.erdos939Sums_four_finite_of_abc_seven_sixths_bound habc

theorem erdos939Sums_five_finite_of_abc_five_fourths_threshold {B : ℕ} (habc : ∀ S ∈ Erdos939Sums 5, B < ∑ s ∈ S, s →
      (∑ s ∈ S, s) ^ 4 ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 5) :
    (Erdos939Sums 5).Finite :=
  Erdos939.erdos939Sums_five_finite_of_abc_five_fourths_threshold habc

theorem not_erdos_939_of_four_full_radical_obstruction (habc : ∀ S ∈ Erdos939Sums 4,
      (∑ s ∈ S, s) ^ 3 ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 4) :
    Erdos939Sums 4 = ∅ ∧ ¬ (∀ r ≥ 4, (Erdos939Sums r).Nonempty) :=
  Erdos939.not_erdos_939_of_four_full_radical_obstruction habc

end Erdos939.Palomar
end
