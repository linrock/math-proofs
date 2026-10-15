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

public import MoserScherkAndFeketeLimit36

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace Erdos36

def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A.product B).filter <| fun (a, b) => a - b = k).card

noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ :=
  iSup <| Overlap A B

noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

noncomputable def MinOverlapQuotient (N : ℕ) : ℝ :=
  (M N : ℝ) / N

theorem liminf_eq_limsup_minOverlapQuotient :
    atTop.liminf MinOverlapQuotient = atTop.limsup MinOverlapQuotient :=
  _root_.Erdos36.Proofs.liminf_eq_limsup_minOverlapQuotient

theorem tendsto_minOverlapQuotient_liminf :
    atTop.Tendsto MinOverlapQuotient (𝓝 (atTop.liminf MinOverlapQuotient)) :=
  _root_.Erdos36.Proofs.tendsto_minOverlapQuotient_liminf

theorem minimum_overlap_variants_lower_erdos_1955 :
    (1 : ℝ) / 4 ≤ atTop.liminf MinOverlapQuotient :=
  _root_.Erdos36.Proofs.minimum_overlap_variants_lower_erdos_1955

theorem minimum_overlap_variants_lower_scherk_1955 :
    1 - (Real.sqrt 2)⁻¹ < atTop.liminf MinOverlapQuotient :=
  _root_.Erdos36.Proofs.minimum_overlap_variants_lower_scherk_1955

theorem minimum_overlap_variants_lower_swierczkowski_1958 :
    (4 - 6 ^ ((1 : ℝ) / 2)) / 5 < atTop.liminf MinOverlapQuotient :=
  _root_.Erdos36.Proofs.minimum_overlap_variants_lower_swierczkowski_1958

theorem moser_sqrt_two_div_four_le_liminf :
    Real.sqrt 2 / 4 ≤ atTop.liminf MinOverlapQuotient :=
  _root_.Erdos36.Proofs.moser_sqrt_two_div_four_le_liminf

theorem minimum_overlap_variants_upper_erdos_1955 :
    atTop.limsup MinOverlapQuotient ≤ (1 : ℝ) / 2 :=
  _root_.Erdos36.Proofs.minimum_overlap_variants_upper_erdos_1955

theorem moser_scherk_combined_le_M (n R : ℕ) :
    12 * R ^ 2 * n ^ 2 + 6 * R ^ 2 * M n +
      6 * (∑ k ∈ Finset.range R,
        (R ^ 2 - (k + 1) ^ 2) * (2 * M n - (2 * n - 1 - k))) ≤
      8 * n ^ 4 + 4 * R * (4 * R ^ 2 - 1) * M n :=
  _root_.Erdos36.Proofs.moser_scherk_combined_le_M n R

theorem exact_values_M :
    M 1 = 1 ∧ M 2 = 1 ∧ M 3 = 2 ∧ M 6 = 3 ∧ M 7 = 3 ∧
      M 8 = 4 ∧ M 9 = 4 ∧ M 12 = 5 ∧ M 14 = 6 ∧ M 15 = 6 :=
  ⟨_root_.Erdos36.Proofs.M_one, _root_.Erdos36.Proofs.M_two, _root_.Erdos36.Proofs.M_three, _root_.Erdos36.Proofs.M_six_eq_three,
   _root_.Erdos36.Proofs.M_seven_eq_three, _root_.Erdos36.Proofs.M_eight_eq_four, _root_.Erdos36.Proofs.M_nine_eq_four,
   _root_.Erdos36.Proofs.M_twelve_eq_five, _root_.Erdos36.Proofs.M_fourteen_eq_six, _root_.Erdos36.Proofs.M_fifteen_eq_six⟩

end Erdos36
