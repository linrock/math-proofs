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

public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos836.Challenge

section
variable {V : Type*}

def IsUniform (r : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = r

def IsProperHypergraphColoring (H : Finset (Finset V)) {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

def HypergraphColorable (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperHypergraphColoring H c

def HasHypergraphChromaticNumber (H : Finset (Finset V)) (k : ℕ) : Prop :=
  HypergraphColorable H k ∧ ∀ j < k, ¬ HypergraphColorable H j

def IsIntersecting [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  ∀ e₁ ∈ H, ∀ e₂ ∈ H, (e₁ ∩ e₂).Nonempty

def activeVertices [DecidableEq V] (H : Finset (Finset V)) : Finset V :=
  H.biUnion id

def IsProperColoring (H : Finset (Finset V)) {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

def IsKColorable (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring H c

def IsTwoColorable (H : Finset (Finset V)) : Prop :=
  IsKColorable H 2

def IsThreeColorable (H : Finset (Finset V)) : Prop :=
  IsKColorable H 3

def HasChromaticNumberThree (H : Finset (Finset V)) : Prop :=
  IsThreeColorable H ∧ ¬ IsTwoColorable H

def vertexDegree [DecidableEq V] (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

def HasPairwiseIntersectionAtLeast [DecidableEq V] (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ k ≤ (e₁ ∩ e₂).card

def IsLinearHypergraph [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  ∀ e₁ ∈ H, ∀ e₂ ∈ H, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1

end

def Erdos836QuadraticVertexQuestion : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ), 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H → IsIntersecting H → HasChromaticNumberThree H →
        (activeVertices H).card ≤ C * r ^ 2

def Erdos836LinearIntersectionConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ), 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H → IsIntersecting H → HasChromaticNumberThree H →
        ∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ c * (r : ℝ) ≤ ((e₁ ∩ e₂).card : ℝ)

def HasCodimensionOneAvoidingWitness (r : ℕ) : Prop :=
  ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
    IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
      ¬ HasPairwiseIntersectionAtLeast H (r - 1)

def alonVertexCount (r : ℕ) : ℕ :=
  (2 * r - 2) + Nat.choose (2 * r - 2) (r - 1) / 2

def statement_erdos_836_parts_i : Prop :=
  False ↔ ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H → HasHypergraphChromaticNumber H 3 →
        (H : Set (Finset (Fin n))).Intersecting →
          ((H.biUnion id).card : ℝ) ≤ C * (r : ℝ) ^ 2

def statement_erdos_836_parts_ii : Prop :=
  True ↔ ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H → HasHypergraphChromaticNumber H 3 →
        (H : Set (Finset (Fin n))).Intersecting →
          ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * (r : ℝ) ≤ ((e ∩ f).card : ℝ)

def statement_exists_alon_fin_hypergraph : Prop :=
  ∀ {r : ℕ}, 2 ≤ r →
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
        alonVertexCount r ≤ (activeVertices H).card

def statement_not_erdos836QuadraticVertexQuestion : Prop :=
  ¬ Erdos836QuadraticVertexQuestion

def statement_erdos836LinearIntersectionConjecture_proved : Prop :=
  Erdos836LinearIntersectionConjecture

def statement_r_le_two_mul_add_one_of_forall_card_inter_le : Prop :=
  ∀ {V : Type*} [DecidableEq V] {r t : ℕ},
    2 ≤ r → ∀ {H : Finset (Finset V)}, IsUniform r H → IsIntersecting H →
      ¬ IsTwoColorable H →
      (∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ t) →
        r ≤ 2 * t + 1

def statement_isTwoColorable_of_four_le_r_of_isLinearHypergraph : Prop :=
  ∀ {V : Type*} [DecidableEq V] {r : ℕ},
    4 ≤ r → ∀ {H : Finset (Finset V)}, IsUniform r H → IsIntersecting H →
      IsLinearHypergraph H → IsTwoColorable H

def statement_r_le_five_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable : Prop :=
  ∀ {V : Type*} [DecidableEq V] {r : ℕ},
    2 ≤ r → ∀ {H : Finset (Finset V)}, IsUniform r H → IsIntersecting H →
      ¬ IsTwoColorable H → ¬ HasPairwiseIntersectionAtLeast H 3 → r ≤ 5

def statement_hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting : Prop :=
  ∀ {V : Type*} [DecidableEq V] {r : ℕ},
    2 ≤ r → ∀ {H : Finset (Finset V)}, IsUniform r H → IsIntersecting H →
      (HasChromaticNumberThree H ↔ ¬ IsTwoColorable H)

def statement_three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable : Prop :=
  ∀ {V : Type*} [DecidableEq V] {r : ℕ},
    3 ≤ r → ∀ {H : Finset (Finset V)}, IsUniform r H → IsIntersecting H →
      ¬ IsTwoColorable H → ¬ HasPairwiseIntersectionAtLeast H (r - 1) →
        ∀ {v : V}, v ∈ activeVertices H → 3 ≤ vertexDegree H v

def statement_two_mul_r_add_one_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one : Prop :=
  ∀ {V : Type*} [DecidableEq V] {r : ℕ},
    3 ≤ r → ∀ {H : Finset (Finset V)}, IsUniform r H → IsIntersecting H →
      ¬ IsTwoColorable H → ¬ HasPairwiseIntersectionAtLeast H (r - 1) →
        2 * r + 1 ≤ (activeVertices H).card

def statement_four_le_vertexDegree_of_mem_inter_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one : Prop :=
  ∀ {V : Type*} [DecidableEq V] {r : ℕ},
    2 ≤ r → ∀ {H : Finset (Finset V)}, IsUniform r H → IsIntersecting H →
      ¬ IsTwoColorable H → ¬ HasPairwiseIntersectionAtLeast H (r - 1) →
        ∀ {e₁ e₂ : Finset V}, e₁ ∈ H → e₂ ∈ H → e₂ ≠ e₁ →
          2 ≤ (e₁ ∩ e₂).card → ∀ {v : V}, v ∈ e₁ ∩ e₂ → 4 ≤ vertexDegree H v

def statement_three_mul_card_activeVertices_add_one_le_card_mul_r_of_four_le_r : Prop :=
  ∀ {V : Type*} [DecidableEq V] {r : ℕ},
    4 ≤ r → ∀ {H : Finset (Finset V)}, IsUniform r H → IsIntersecting H →
      ¬ IsTwoColorable H → ¬ HasPairwiseIntersectionAtLeast H (r - 1) →
        3 * (activeVertices H).card + 1 ≤ H.card * r

def statement_nine_le_card_and_nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three : Prop :=
  ∀ {V : Type*} [DecidableEq V] {H : Finset (Finset V)},
    IsUniform 4 H → IsIntersecting H → HasChromaticNumberThree H →
      ¬ HasPairwiseIntersectionAtLeast H 3 →
        9 ≤ H.card ∧ 9 ≤ (activeVertices H).card ∧
          3 * (activeVertices H).card + 1 ≤ H.card * 4

def statement_card_eq_seven_and_card_activeVertices_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable : Prop :=
  ∀ {V : Type*} [DecidableEq V] {H : Finset (Finset V)},
    IsUniform 3 H → IsIntersecting H → IsLinearHypergraph H → ¬ IsTwoColorable H →
      H.card = 7 ∧ (activeVertices H).card = 7

def statement_hasCodimensionOneAvoidingWitness_three : Prop :=
  HasCodimensionOneAvoidingWitness 3

end Erdos836.Challenge
end
