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

public import FibonacciVanDoorn33

@[expose] public section

open Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Erdos33

noncomputable def AdditiveBasisCondition (A : Set ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (n : ℕ) (a : ℕ), a ∈ A ∧ k = a + n ^ 2

noncomputable def IsSquareAdditiveComplement (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ a ∈ A, ∃ k : ℕ, n = k ^ 2 + a

noncomputable def prefixCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

noncomputable def normalizedPrefixRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  (prefixCount A N : ℝ) / Real.sqrt (N : ℝ)

noncomputable def vanDoornBlock (B M : ℕ) : Set ℕ :=
  {a : ℕ | B ≤ a ∧ a ≤ B + 2 * M}

noncomputable def vanDoornBlockStart (M : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.rec 0 (fun k acc => acc + (M k) ^ 2 + 2 * M k) j

noncomputable def vanDoornUnion (M : ℕ → ℕ) : Set ℕ :=
  ⋃ j : ℕ, vanDoornBlock (vanDoornBlockStart M j) (M j)

noncomputable def fibBlockWidth (j : ℕ) : ℕ := Nat.fib (j + 2)

theorem core_fibBlockWidth_eq (j : ℕ) :
    Erdos33.Core.fibBlockWidth j = fibBlockWidth j := rfl

theorem core_vanDoornBlockStart_eq (M : ℕ → ℕ) (j : ℕ) :
    Erdos33.Core.vanDoornBlockStart M j = vanDoornBlockStart M j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [Erdos33.Core.vanDoornBlockStart, vanDoornBlockStart, ih]

theorem core_vanDoornUnion_eq (M : ℕ → ℕ) :
    Erdos33.Core.vanDoornUnion M = vanDoornUnion M := by
  ext a
  simp [Erdos33.Core.vanDoornUnion, vanDoornUnion, Erdos33.Core.vanDoornBlock,
    vanDoornBlock, core_vanDoornBlockStart_eq]

theorem erdos_33_variants_one_mem_lowerBounds :
    1 < ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) :=
  Erdos33.Core.erdos_33_variants_one_mem_lowerBounds

theorem erdos_33_variants_vanDoorn :
    (⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal))) ≤
        ((2 * Real.goldenRatio ^ ((5 : ℝ) / 2) : ℝ) : EReal) :=
  Erdos33.Core.erdos_33_variants_vanDoorn

theorem sixty_three_fiftieths_le_iInf_limsup :
    (((63 : ℝ) / 50 : ℝ) : EReal) ≤
      ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
        ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) :=
  Erdos33.Core.sixty_three_fiftieths_le_iInf_limsup

theorem exists_ge_sixty_three_fiftieths_normalizedPrefixRatio
    {A : Set ℕ} (hA : IsSquareAdditiveComplement A) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ (63 : ℝ) / 50 ≤ normalizedPrefixRatio A N :=
  Erdos33.Core.exists_ge_sixty_three_fiftieths_normalizedPrefixRatio hA M

theorem additiveBasisCondition_vanDoornUnion {M : ℕ → ℕ} (hM : ∀ j : ℕ, 1 ≤ M j) :
    AdditiveBasisCondition (vanDoornUnion M) := by
  have hcore := Erdos33.Core.additiveBasisCondition_vanDoornUnion hM
  rw [core_vanDoornUnion_eq] at hcore
  exact hcore

theorem two_mul_sum_fibBlockWidth_div_sqrt_start_le {K : ℕ} (hK : 1 ≤ K) :
    (2 * ((∑ j ∈ Finset.range (K + 1), fibBlockWidth j : ℕ) : ℝ)) /
      Real.sqrt (vanDoornBlockStart fibBlockWidth K : ℝ) ≤
        2 * Real.goldenRatio ^ ((5 : ℝ) / 2) := by
  have hcore :
      (2 * ((∑ j ∈ Finset.range (K + 1), Erdos33.Core.fibBlockWidth j : ℕ) : ℝ)) /
        Real.sqrt (Erdos33.Core.vanDoornBlockStart Erdos33.Core.fibBlockWidth K : ℝ) ≤
          2 * Real.goldenRatio ^ ((5 : ℝ) / 2) :=
    Erdos33.Core.two_mul_sum_fibBlockWidth_div_sqrt_start_le hK
  rw [show (∑ j ∈ Finset.range (K + 1), Erdos33.Core.fibBlockWidth j : ℕ) =
        ∑ j ∈ Finset.range (K + 1), fibBlockWidth j by
    exact Finset.sum_congr rfl (fun j _ => core_fibBlockWidth_eq j),
    core_vanDoornBlockStart_eq] at hcore
  exact hcore

theorem one_hundred_twenty_seven_over_one_hundred_le_iInf_limsup :
    (((127 : ℝ) / 100 : ℝ) : EReal) ≤
      ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
        ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) :=
  Erdos33.Core.one_hundred_twenty_seven_over_one_hundred_le_iInf_limsup

theorem exists_ge_one_hundred_twenty_seven_over_one_hundred_normalizedPrefixRatio
    {A : Set ℕ} (hA : IsSquareAdditiveComplement A) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ (127 : ℝ) / 100 ≤ normalizedPrefixRatio A N :=
  Erdos33.Core.exists_ge_one_hundred_twenty_seven_over_one_hundred_normalizedPrefixRatio hA M

end Erdos33
