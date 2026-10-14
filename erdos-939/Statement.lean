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

public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos939.Challenge

def Full (k n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n
@[reducible] def SetCoprime (S : Finset ℕ) : Prop := S.gcd id = 1

def Erdos939Sums (r : ℕ) : Set (Finset ℕ) :=
  {S : Finset ℕ | S.card = r - 2 ∧ SetCoprime S ∧ Full r (∑ s ∈ S, s) ∧
    ∀ s ∈ S, 0 < s ∧ Full r s}

def Erdos939GeneralSums (r k : ℕ) : Set (Finset ℕ) :=
  {S : Finset ℕ | S.card = k ∧ SetCoprime S ∧ Full r (∑ s ∈ S, s) ∧
    ∀ s ∈ S, 0 < s ∧ Full r s}

def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

def cambieFiveSet : Finset ℕ :=
  {2 ^ 8 * 3 ^ 10 * 5 ^ 7, 2 ^ 12 * 23 ^ 6, 11 ^ 5 * 13 ^ 5}

def landerParkinFiveSet : Finset ℕ :=
  {27 ^ 5, 84 ^ 5, 110 ^ 5, 133 ^ 5}

def statement_erdos_939 : Prop :=
  ∀ r ≥ 4, (Erdos939Sums r).Nonempty

def statement_erdos_939_variants_finite : Prop :=
  False ↔ ∀ r ≥ 4, (Erdos939Sums r).Finite

def statement_erdos_939_variants_infinite_of_six_le : Prop :=
  ∀ r ≥ 6, (Erdos939Sums r).Infinite

def statement_erdos_939_variants_triples : Prop :=
  True ↔ {(a, b, c) | SetCoprime {a, b, c} ∧
      0 < a ∧ 0 < b ∧ Full 3 a ∧ Full 3 b ∧ Full 3 c ∧ a + b = c}.Infinite

def statement_erdos_939_variants_examples : Prop :=
  ∃ r ≥ 4, (Erdos939Sums r).Nonempty

def statement_erdos_939_variants_seven : Prop :=
  (Erdos939Sums 7).Nonempty

def statement_erdos_939_variants_eight : Prop :=
  (Erdos939Sums 8).Nonempty

def statement_erdos_939_variants_euler : Prop :=
  ¬ (∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
      (∀ s ∈ S, 0 < s) → ¬ (∃ q, ∑ s ∈ S, s ^ k = q ^ k))

def statement_erdos_939_variants_triples_infinite : Prop :=
  {(a, b, c) : ℕ × ℕ × ℕ | SetCoprime {a, b, c} ∧
      0 < a ∧ 0 < b ∧ Full 3 a ∧ Full 3 b ∧ Full 3 c ∧ a + b = c}.Infinite

def statement_cohn_noncube_triples_infinite : Prop :=
  {(a, b, c) : ℕ × ℕ × ℕ | SetCoprime {a, b, c} ∧
      0 < a ∧ 0 < b ∧ Full 3 a ∧ Full 3 b ∧ Full 3 c ∧
      (∀ k : ℕ, k ^ 3 ≠ a) ∧ (∀ k : ℕ, k ^ 3 ≠ b) ∧ (∀ k : ℕ, k ^ 3 ≠ c) ∧
      a + b = c}.Infinite

def statement_cohn_noncube_generalSums_three_two_infinite : Prop :=
  {S : Finset ℕ | S ∈ Erdos939GeneralSums 3 2 ∧
      (∀ k : ℕ, k ^ 3 ≠ ∑ s ∈ S, s) ∧
      ∀ s ∈ S, ∀ k : ℕ, k ^ 3 ≠ s}.Infinite

def statement_erdos_939_generalSums_three_two_infinite : Prop :=
  (Erdos939GeneralSums 3 2).Infinite

def statement_cambieFiveSet_mem_erdos939Sums_five : Prop :=
  cambieFiveSet ∈ Erdos939Sums 5 ∧ ∑ s ∈ cambieFiveSet, s = 3 ^ 7 * 61 ^ 5

def statement_landerParkinFiveSet_mem_erdos939GeneralSums_five_four : Prop :=
  landerParkinFiveSet ∈ Erdos939GeneralSums 5 4 ∧ ∑ s ∈ landerParkinFiveSet, s = 144 ^ 5

def statement_r_full_iff_exists_squarefree_cores : Prop :=
  ∀ (r n : ℕ), 1 ≤ r → 0 < n →
      (Full r n ↔
        ∃ (u : ℕ) (v : ℕ → ℕ),
          (∀ j ∈ Finset.Ico 1 r, Squarefree (v j)) ∧
          (∀ j₁ ∈ Finset.Ico 1 r, ∀ j₂ ∈ Finset.Ico 1 r, j₁ ≠ j₂ → Nat.Coprime (v j₁) (v j₂)) ∧
          u ^ r * ∏ j ∈ Finset.Ico 1 r, (v j) ^ (r + j) = n)

def statement_rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums : Prop :=
  ∀ {r : ℕ}, 4 ≤ r → ∀ {S : Finset ℕ}, S ∈ Erdos939Sums r →
      rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ≤ (∏ s ∈ S, s) * (∑ s ∈ S, s) ∧
        (∏ s ∈ S, s) * (∑ s ∈ S, s) < (∑ s ∈ S, s) ^ (r - 1) ∧
        rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r < (∑ s ∈ S, s) ^ (r - 1)

def statement_abc_quality_real_bound_of_mem_erdos939Sums : Prop :=
  ∀ {r : ℕ}, 4 ≤ r → ∀ {S : Finset ℕ}, S ∈ Erdos939Sums r →
      ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) * Real.log (rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) : ℝ) <
        Real.log ((∑ s ∈ S, s : ℕ) : ℝ)

def statement_rad_pow_four_le_and_lt_cube_of_mem_erdos939Sums_four : Prop :=
  ∀ {a b : ℕ}, ({a, b} : Finset ℕ) ∈ Erdos939Sums 4 →
      rad (a * b * (a + b)) ^ 4 ∣ a * b * (a + b) ∧
      rad (a * b * (a + b)) ^ 4 ≤ a * b * (a + b) ∧
      a * b * (a + b) < (a + b) ^ 3 ∧
      4 * rad (a * b * (a + b)) ^ 4 < (a + b) ^ 3 ∧
      rad (a * b * (a + b)) ^ 4 < (a + b) ^ 3

def statement_walsh_twist_pair_mem_erdos939GeneralSums_three_two : Prop :=
  ∀ {d₁ x₁ d₂ x₂ d₃ x₃ : ℕ},
      0 < d₁ → 0 < x₁ → 0 < d₂ → 0 < x₂ → 0 < d₃ →
      rad d₁ ∣ x₁ → rad d₂ ∣ x₂ → rad d₃ ∣ x₃ →
      Nat.Coprime (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3) →
      d₁ ^ 2 * x₁ ^ 3 + d₂ ^ 2 * x₂ ^ 3 = d₃ ^ 2 * x₃ ^ 3 →
      ({d₁ ^ 2 * x₁ ^ 3, d₂ ^ 2 * x₂ ^ 3} : Finset ℕ) ∈ Erdos939GeneralSums 3 2

def statement_walsh_parametric_cube_scaling_coprime_iff : Prop :=
  ∀ {a b d : ℕ}, 0 < d → Nat.Coprime a b →
      (Nat.Coprime (d ^ 3 * a) (d ^ 3 * b) ↔ d = 1)

def statement_erdos_939_iff_four_nonempty : Prop :=
  (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔ (Erdos939Sums 4).Nonempty

def statement_erdos_939_iff_exists_coprime_four_full_pair : Prop :=
  (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
        Full 4 a ∧ Full 4 b ∧ Full 4 (a + b)

def statement_erdos939Sums_four_finite_of_abc_seven_sixths_bound : Prop :=
  ∀ {K : ℕ}, (∀ x y : ℕ, 0 < x → 0 < y → Nat.Coprime x y →
      (x + y) ^ 6 ≤ K * rad (x * y * (x + y)) ^ 7) → (Erdos939Sums 4).Finite

def statement_erdos939Sums_five_finite_of_abc_five_fourths_threshold : Prop :=
  ∀ {B : ℕ}, (∀ S ∈ Erdos939Sums 5, B < ∑ s ∈ S, s →
      (∑ s ∈ S, s) ^ 4 ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 5) → (Erdos939Sums 5).Finite

def statement_not_erdos_939_of_four_full_radical_obstruction : Prop :=
  (∀ S ∈ Erdos939Sums 4,
      (∑ s ∈ S, s) ^ 3 ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 4) →
    Erdos939Sums 4 = ∅ ∧ ¬ (∀ r ≥ 4, (Erdos939Sums r).Nonempty)

end Erdos939.Challenge
end
