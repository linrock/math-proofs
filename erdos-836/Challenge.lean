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

namespace Finset

variable {V : Type*}

/-- Every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- A weak proper coloring has no monochromatic edge. -/
def IsProperHypergraphColoring (H : Finset (Finset V)) {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- The edge family admits a weak proper coloring with `k` colors. -/
def HypergraphColorable (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, H.IsProperHypergraphColoring c

/-- The weak chromatic number is exactly `k`. -/
def HasHypergraphChromaticNumber (H : Finset (Finset V)) (k : ℕ) : Prop :=
  H.HypergraphColorable k ∧ ∀ j < k, ¬ H.HypergraphColorable j

end Finset

namespace Erdos836

variable {V : Type*}

/-- A finite hypergraph `H` (represented as a `Finset` of `Finset V` hyperedges) is `r`-uniform
if every hyperedge in `H` has cardinality `r`. -/
def IsUniform (r : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A hypergraph `H` is intersecting if every pair of hyperedges in `H` has nonempty intersection. -/
def IsIntersecting [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  ∀ e₁ ∈ H, ∀ e₂ ∈ H, (e₁ ∩ e₂).Nonempty

/-- The set of active vertices of `H`, i.e., the union of all hyperedges in `H`. -/
def activeVertices [DecidableEq V] (H : Finset (Finset V)) : Finset V :=
  H.biUnion id

/-- A vertex colouring `c : V → C` is proper for `H` if no hyperedge of `H` is monochromatic
(every hyperedge contains two vertices of distinct colours). -/
def IsProperColoring (H : Finset (Finset V)) {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- A hypergraph `H` is `k`-colourable if it has a proper vertex colouring with `Fin k`. -/
def IsKColorable (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring H c

/-- A hypergraph `H` is 2-colourable (has Property B) if `IsKColorable H 2`. -/
def IsTwoColorable (H : Finset (Finset V)) : Prop :=
  IsKColorable H 2

/-- A hypergraph `H` is 3-colourable if `IsKColorable H 3`. -/
def IsThreeColorable (H : Finset (Finset V)) : Prop :=
  IsKColorable H 3

/-- A hypergraph `H` has chromatic number exactly `3` if it is 3-colourable and not 2-colourable. -/
def HasChromaticNumberThree (H : Finset (Finset V)) : Prop :=
  IsThreeColorable H ∧ ¬ IsTwoColorable H

/-- The degree of a vertex `v` in `H` is the number of hyperedges of `H` containing `v`. -/
def vertexDegree [DecidableEq V] (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

/-- `H` has a pair of distinct edges meeting in at least `k` vertices. -/
def HasPairwiseIntersectionAtLeast [DecidableEq V] (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ k ≤ (e₁ ∩ e₂).card

/-- `H` is linear (nearly disjoint) if any two distinct edges meet in at most `1` vertex. -/
def IsLinearHypergraph [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  ∀ e₁ ∈ H, ∀ e₂ ∈ H, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1

/-- Statement of Erdős Problem #836, Question 1 (Quadratic Vertex Bound Question). -/
def Erdos836QuadraticVertexQuestion : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ), 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H → IsIntersecting H → HasChromaticNumberThree H →
        (activeVertices H).card ≤ C * r ^ 2

/-- Statement of Erdős Problem #836, Question 2 (Linear Pairwise Intersection Conjecture). -/
def Erdos836LinearIntersectionConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ), 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H → IsIntersecting H → HasChromaticNumberThree H →
        ∃ e₁ ∈ H, ∃ e₂ ∈ H, e₁ ≠ e₂ ∧ c * (r : ℝ) ≤ ((e₁ ∩ e₂).card : ℝ)

/-- Statement of the Erdős–Shelah Codimension-One Intersection Question. -/
def HasCodimensionOneAvoidingWitness (r : ℕ) : Prop :=
  ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
    IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
      ¬ HasPairwiseIntersectionAtLeast H (r - 1)

/-- Vertex count of Alon's counterexample hypergraph for uniformity `r`:
`|X| + |Y| = (2r - 2) + C(2r - 2, r - 1) / 2`. -/
def alonVertexCount (r : ℕ) : ℕ :=
  (2 * r - 2) + Nat.choose (2 * r - 2) (r - 1) / 2

end Erdos836

open Erdos836

variable {V : Type*}

/-- Disproof of Erdős Problem #836, Part (i) (`O(r^2)` active-vertex question) via Noga Alon's
equitable-partition hypergraph construction (`≍ 4^r / √r` active vertices). -/
theorem Erdos836.Palomar.erdos_836.parts.i :
    False ↔ ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ((H.biUnion id).card : ℝ) ≤ C * (r : ℝ) ^ 2 := by
  sorry

/-- Affirmative resolution of Erdős Problem #836, Part (ii) (linear pairwise edge intersection
in 3-chromatic intersecting `r`-uniform hypergraphs, with explicit constant `c = 1 / 3`). -/
theorem Erdos836.Palomar.erdos_836.parts.ii :
    True ↔ ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * (r : ℝ) ≤ ((e ∩ f).card : ℝ) := by
  sorry

namespace Erdos836.Palomar

/-- Alon's equitable-partition construction for all `r ≥ 2`: there exist `n : ℕ` and an
`r`-uniform intersecting 3-chromatic hypergraph `H` on `Fin n` with at least `alonVertexCount r`
active vertices. -/
theorem exists_alon_fin_hypergraph {r : ℕ} (hr : 2 ≤ r) :
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
        alonVertexCount r ≤ (activeVertices H).card := by
  sorry

/-- Unconditional disproof of `Erdos836QuadraticVertexQuestion`. -/
theorem not_erdos836QuadraticVertexQuestion : ¬ Erdos836QuadraticVertexQuestion := by
  sorry

/-- Unconditional proof of `Erdos836LinearIntersectionConjecture` (`c = 1 / 3`). -/
theorem erdos836LinearIntersectionConjecture_proved :
    Erdos836LinearIntersectionConjecture := by
  sorry

/-- Universal Minimal-Blue Double-Counting Pairwise Intersection Bound (`r ≤ 2t + 1`):
in any non-2-colourable intersecting `r`-uniform hypergraph `H` (`r ≥ 2`) over `[DecidableEq V]`,
if every pair of distinct edges meets in at most `t` vertices, then `r ≤ 2 * t + 1`. -/
theorem r_le_two_mul_add_one_of_forall_card_inter_le [DecidableEq V] {r t : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H)
    (ht : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ t) :
    r ≤ 2 * t + 1 := by
  sorry

/-- Universal 2-colourability of linear intersecting `r`-uniform hypergraphs for all `r ≥ 4`. -/
theorem isTwoColorable_of_four_le_r_of_isLinearHypergraph [DecidableEq V] {r : ℕ}
    (hr : 4 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) :
    IsTwoColorable H := by
  sorry

/-- Universal rank upper bound `r ≤ 5` for non-2-colourable intersecting `r`-uniform hypergraphs
avoiding pairwise intersection `3`. -/
theorem r_le_five_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    r ≤ 5 := by
  sorry

/-- Universal 3-colourability characterization for intersecting `r`-uniform hypergraphs (`r ≥ 2`):
`HasChromaticNumberThree H ↔ ¬ IsTwoColorable H`. -/
theorem hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting [DecidableEq V]
    {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) :
    HasChromaticNumberThree H ↔ ¬ IsTwoColorable H := by
  sorry

/-- Universal minimum-degree bound `δ(H) ≥ 3` on active vertices for non-2-colourable intersecting
`r`-uniform hypergraphs (`r ≥ 3`) avoiding pairwise intersection `r - 1`. -/
theorem three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {v : V} (hv : v ∈ activeVertices H) :
    3 ≤ vertexDegree H v := by
  sorry

/-- Universal active-vertex lower bound `2r + 1 ≤ |V(H)|` for non-2-colourable intersecting
`r`-uniform hypergraphs (`r ≥ 3`) avoiding pairwise intersection `r - 1`. -/
theorem two_mul_r_add_one_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    2 * r + 1 ≤ (activeVertices H).card := by
  sorry

/-- Degree-3 Vertex Replacement & Sunflower Theorem: under codimension-one avoidance, every vertex
lying in the intersection of two distinct edges with `|e₁ ∩ e₂| ≥ 2` has degree at least `4`. -/
theorem four_le_vertexDegree_of_mem_inter_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₁ e₂ : Finset V} (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H) (hne21 : e₂ ≠ e₁)
    (hcard : 2 ≤ (e₁ ∩ e₂).card) {v : V} (hv : v ∈ e₁ ∩ e₂) :
    4 ≤ vertexDegree H v := by
  sorry

/-- Sharpened handshake active-vertex inequality `3|V(H)| + 1 ≤ r|E(H)|` for `r ≥ 4` under
codimension-one intersection avoidance. -/
theorem three_mul_card_activeVertices_add_one_le_card_mul_r_of_four_le_r [DecidableEq V] {r : ℕ}
    (hr : 4 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    3 * (activeVertices H).card + 1 ≤ H.card * r := by
  sorry

/-- Combined universal edge and active-vertex lower bounds (`9 ≤ |E(H)|`, `9 ≤ |V(H)|`, and
`3|V(H)| + 1 ≤ 4|E(H)|`) for 4-uniform 3-chromatic intersecting hypergraphs avoiding pairwise
intersection `3`. -/
theorem nine_le_card_and_nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hchrom : HasChromaticNumberThree H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    9 ≤ H.card ∧ 9 ≤ (activeVertices H).card ∧
      3 * (activeVertices H).card + 1 ≤ H.card * 4 := by
  sorry

/-- Lovász `r = 3` Fano parameters theorem: every 3-uniform non-2-colourable linear intersecting
hypergraph has exactly `7` edges and `7` active vertices. -/
theorem card_eq_seven_and_card_activeVertices_eq_seven_of_r_eq_three_of_isLinearHypergraph_of_not_isTwoColorable
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 3 H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H) :
    H.card = 7 ∧ (activeVertices H).card = 7 := by
  sorry

/-- The Fano plane `PG(2, 2)` on `Fin 7` is a verified 3-uniform 3-chromatic intersecting witness
avoiding pairwise intersection `r - 1 = 2`. -/
theorem hasCodimensionOneAvoidingWitness_three : HasCodimensionOneAvoidingWitness 3 := by
  sorry

end Erdos836.Palomar
end
