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

public import Erdos836Unified435
public import FourUniformCodimensionOneAvoidingBounds836
public import DegreeThreeVertexReplacementAndNineEdgeBound836

@[expose] public section

noncomputable section
open scoped BigOperators

open Erdos836

variable {V : Type*}

theorem Erdos836.Palomar.erdos_836.parts.i :
    False ↔ ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ((H.biUnion id).card : ℝ) ≤ C * (r : ℝ) ^ 2 :=
  Erdos836.erdos_836_parts_i_proved

theorem Erdos836.Palomar.erdos_836.parts.ii :
    True ↔ ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * (r : ℝ) ≤ ((e ∩ f).card : ℝ) :=
  Erdos836.erdos_836_parts_ii_proved

namespace Erdos836.Palomar

theorem exists_alon_fin_hypergraph {r : ℕ} (hr : 2 ≤ r) :
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
        alonVertexCount r ≤ (activeVertices H).card :=
  Erdos836.exists_alon_fin_hypergraph hr

theorem not_erdos836QuadraticVertexQuestion : ¬ Erdos836QuadraticVertexQuestion :=
  Erdos836.not_erdos836QuadraticVertexQuestion

theorem erdos836LinearIntersectionConjecture_proved :
    Erdos836LinearIntersectionConjecture :=
  Erdos836.erdos836LinearIntersectionConjecture_proved

theorem r_le_two_mul_add_one_of_forall_card_inter_le [DecidableEq V] {r t : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H)
    (ht : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ t) :
    r ≤ 2 * t + 1 :=
  Erdos836.r_le_two_mul_add_one_of_forall_card_inter_le hr hunif hinter hnot2 ht

theorem isTwoColorable_of_four_le_r_of_isLinearHypergraph [DecidableEq V] {r : ℕ}
    (hr : 4 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) :
    IsTwoColorable H :=
  Erdos836.isTwoColorable_of_four_le_r_of_isLinearHypergraph hr hunif hinter hlin

theorem r_le_five_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    r ≤ 5 :=
  Erdos836.r_le_five_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    hr hunif hinter hnot2 hno3

theorem hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting [DecidableEq V]
    {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) :
    HasChromaticNumberThree H ↔ ¬ IsTwoColorable H :=
  Erdos836.hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting hr hunif hinter

theorem three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {v : V} (hv : v ∈ activeVertices H) :
    3 ≤ vertexDegree H v :=
  Erdos836.three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
    hr hunif hinter hnot2 hno hv

theorem two_mul_r_add_one_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    2 * r + 1 ≤ (activeVertices H).card :=
  Erdos836.two_mul_r_add_one_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one
    hr hunif hinter hnot2 hno

theorem four_le_vertexDegree_of_mem_inter_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₁ e₂ : Finset V} (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H) (hne21 : e₂ ≠ e₁)
    (hcard : 2 ≤ (e₁ ∩ e₂).card) {v : V} (hv : v ∈ e₁ ∩ e₂) :
    4 ≤ vertexDegree H v :=
  Erdos836.four_le_vertexDegree_of_mem_inter_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one
    hr hunif hinter hnot2 hno he₁ he₂ hne21 hcard hv

theorem three_mul_card_activeVertices_add_one_le_card_mul_r_of_four_le_r [DecidableEq V] {r : ℕ}
    (hr : 4 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    3 * (activeVertices H).card + 1 ≤ H.card * r :=
  Erdos836.three_mul_card_activeVertices_add_one_le_card_mul_r_of_four_le_r
    hr hunif hinter hnot2 hno

theorem nine_le_card_and_nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hchrom : HasChromaticNumberThree H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    9 ≤ H.card ∧ 9 ≤ (activeVertices H).card ∧
      3 * (activeVertices H).card + 1 ≤ H.card * 4 :=
  Erdos836.nine_le_card_and_nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
    hunif hinter hchrom hno3

theorem card_eq_seven_and_card_activeVertices_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 3 H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H) :
    H.card = 7 ∧ (activeVertices H).card = 7 :=
  ⟨Erdos836.card_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
     hunif hinter hlin hnot2,
   Erdos836.card_activeVertices_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
     hunif hinter hlin hnot2⟩

theorem hasCodimensionOneAvoidingWitness_three : HasCodimensionOneAvoidingWitness 3 :=
  Erdos836.hasCodimensionOneAvoidingWitness_three

end Erdos836.Palomar
end
