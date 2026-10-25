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
open scoped BigOperators Topology Classical
open Finset SimpleGraph Asymptotics Filter

namespace SimpleGraph

open Finset

open scoped Classical in
/-- The triangles of `G` containing the edge `uv`, that is, the `3`-cliques of `G` whose vertex
set contains both endpoints of `uv`. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α)
    (uv : Sym2 α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.toFinset ⊆ t)

end SimpleGraph

namespace Erdos600

/-- Let $e(n,r)$ be minimal such that every graph on $n$ vertices with at least $e(n,r)$ edges,
each edge contained in at least one triangle, must have an edge contained in at least
$r$ triangles. -/
def Erdos600Prop (n : ℕ) (e : ℕ) (r : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.edgeFinset.card ≥ e →
  (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) →
  ∃ uv ∈ G.edgeFinset, r ≤ (G.trianglesContaining uv).card

noncomputable def eFunction (n : ℕ) (r : ℕ) : ℕ := sInf {e : ℕ | Erdos600Prop n e r}

/-- A graph `G` is `r`-book-free and triangle-covered if every edge lies in at least `1` and at most `r - 1` triangles. -/
def IsAdmissibleBookFree {α : Type*} [Fintype α] (G : SimpleGraph α) (r : ℕ) : Prop :=
  (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) ∧
    (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r)

/-- The maximum number of edges in an `r`-book-free triangle-covered graph on `Fin n`. -/
noncomputable def maxAdmissibleEdges (n r : ℕ) : ℕ := eFunction n r - 1

/-- The finite set of common neighbors of `u` and `v` in a finite simple graph `G`. -/
noncomputable def commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) : Finset α :=
  G.neighborFinset u ∩ G.neighborFinset v

/-- The sum of triangle multiplicities `(G.trianglesContaining uv).card` over all edges `uv ∈ G.edgeFinset`. -/
noncomputable def edgeTriangleIncidenceSum {α : Type*} [Fintype α]
    (G : SimpleGraph α) : ℕ :=
  ∑ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card

/-- The sum of squared triangle multiplicities `(G.trianglesContaining uv).card ^ 2` over all edges `uv ∈ G.edgeFinset`. -/
noncomputable def edgeTriangleIncidenceSqSum {α : Type*} [Fintype α]
    (G : SimpleGraph α) : ℕ :=
  ∑ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card ^ 2

/-- The vertex carrier of the weighted blow-up of a base type `α` by `w : α → ℕ`. -/
abbrev BlowupVertex {α : Type*} (w : α → ℕ) : Type _ :=
  Σ u : α, Fin (w u)

/-- The weighted vertex-blowup simple graph of `H : SimpleGraph α` with vertex weights `w : α → ℕ`. -/
def weightedBlowupGraph {α : Type*} (H : SimpleGraph α) (w : α → ℕ) :
    SimpleGraph (BlowupVertex w) :=
  H.comap Sigma.fst

instance instDecidableRelWeightedBlowupGraphAdj {α : Type*} (H : SimpleGraph α) (w : α → ℕ)
    [DecidableRel H.Adj] : DecidableRel (weightedBlowupGraph H w).Adj := by
  intro x y
  change Decidable (H.Adj x.1 y.1)
  infer_instance

/-- Total weight of the common neighbors of `u` and `v` in the base graph `H`. -/
noncomputable def commonNeighborWeightSum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) (u v : α) : ℕ :=
  ∑ t ∈ commonNeighborFinset H u v, w t

/-- A weight function `w : α → ℕ` on a base graph `H` is `r`-admissible if for every edge
`H.Adj u v`, the common-neighbor weight sum satisfies `1 ≤ commonNeighborWeightSum H w u v < r`. -/
def IsAdmissibleBlowupWeight {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) (r : ℕ) : Prop :=
  ∀ u v : α, H.Adj u v →
    1 ≤ commonNeighborWeightSum H w u v ∧ commonNeighborWeightSum H w u v < r

/-- Well-defined product of vertex weights across an unordered pair `uv : Sym2 α`. -/
def edgeWeightProd {α : Type*} (w : α → ℕ) : Sym2 α → ℕ :=
  Sym2.lift ⟨fun u v ↦ w u * w v, fun u v ↦ Nat.mul_comm (w u) (w v)⟩

/-- The edge-count quadratic form `∑_{uv ∈ E(H)} w(u) * w(v)` of a weighted vertex blow-up. -/
noncomputable def blowupEdgeQuadraticForm {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) : ℕ :=
  ∑ uv ∈ H.edgeFinset, edgeWeightProd w uv

/-- The residual non-neighbor finset `R(u) = V \ ({u} ∪ N(u))`. -/
noncomputable def nonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset α :=
  (Finset.univ : Finset α) \ insert u (G.neighborFinset u)

/-- Triangles of `G` avoiding vertex `u` (`u ∉ t`). -/
noncomputable def avoidingTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ u ∉ t)

/-- Cross-triangles `(N(u), R(u), R(u))` avoiding `u` with exactly one vertex in `N(u)`. -/
noncomputable def crossTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset (Finset α) :=
  (avoidingTriangles G u).filter (fun t ↦ (t ∩ G.neighborFinset u).card = 1)

/-- Internal residual triangles `(R(u), R(u), R(u))` avoiding `u` with zero vertices in `N(u)`. -/
noncomputable def residualTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset (Finset α) :=
  (avoidingTriangles G u).filter (fun t ↦ (t ∩ G.neighborFinset u).card = 0)

/-- Number `t₁(u)` of `(N(u), R(u), R(u))` cross-triangles avoiding `u`. -/
noncomputable def crossTriangleCount {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : ℕ :=
  (crossTriangles G u).card

/-- Number `t₃(u)` of `(R(u), R(u), R(u))` internal residual triangles avoiding `u`. -/
noncomputable def residualTriangleCount {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : ℕ :=
  (residualTriangles G u).card

/-- The finset of `r`-book ("heavy") edges of `G`, i.e., edges contained in at least `r` triangles. -/
noncomputable def bookHeavyEdgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) : Finset (Sym2 α) :=
  G.edgeFinset.filter (fun uv ↦ r ≤ (G.trianglesContaining uv).card)

/-- Ruzsa and Szemerédi [RuSz78] subquadratic upper bound (`FormalConjectures`
`erdos_600.variants.ruzsa_szemeredi_upper_bound`): for every fixed $r$, $e(n, r) = o(n^2)$. -/
theorem erdos_600.variants.ruzsa_szemeredi_upper_bound :
    ∀ r : ℕ, (fun (n : ℕ) ↦ (eFunction n r : ℝ)) =o[atTop] (fun (n : ℕ) ↦ (n : ℝ)^2) := by
  sorry

/-- Exact characterization of locally linear graphs via triangle coverage and `r = 2` book-freeness. -/
theorem locallyLinear_iff_trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α) :
    G.LocallyLinear ↔
      (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) ∧
        (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < 2) := by
  sorry

/-- Exact Ruzsa–Szemerédi locally linear bridge at `r = 2`: `eFunction n 2 = 3 * ruzsaSzemerediNumberNat n + 1`. -/
theorem eFunction_two_eq (n : ℕ) :
    eFunction n 2 = 3 * ruzsaSzemerediNumberNat n + 1 := by
  sorry

/-- Behrend asymptotic lower bound on `eFunction n r` for all `r ≥ 2`. -/
theorem behrend_asymptotic_lower_bound_eFunction {r : ℕ} (hr : 2 ≤ r) :
    (fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.exp (-4 * Real.sqrt (Real.log n))) =O[atTop]
      (fun n : ℕ ↦ (eFunction n r : ℝ)) := by
  sorry

/-- Sharp `(2r - 1)` triangle-removal cover-charge upper bound for any triangle-free subgraph `H ≤ G`. -/
theorem card_edgeFinset_le_two_mul_sub_one_mul_sub_card {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) (hH : H.CliqueFree 3)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) {r : ℕ}
    (hr : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r) :
    G.edgeFinset.card ≤ (2 * r - 1) * (G.edgeFinset.card - H.edgeFinset.card) := by
  sorry

/-- Exact complete-graph saturation dichotomy for `n ≥ 3`: `eFunction n r = n.choose 2 + 1 ↔ n - 1 ≤ r`. -/
theorem eFunction_eq_choose_two_succ_iff_of_three_le {n r : ℕ} (hn : 3 ≤ n) :
    eFunction n r = n.choose 2 + 1 ↔ n - 1 ≤ r := by
  sorry

/-- Vertex-disjoint union superadditivity of `maxAdmissibleEdges`. -/
theorem maxAdmissibleEdges_superadditive (m n r : ℕ) :
    maxAdmissibleEdges m r + maxAdmissibleEdges n r ≤ maxAdmissibleEdges (m + n) r := by
  sorry

/-- Sharp edge-degree-sum upper bound `deg(u) + deg(v) ≤ |V| + r - 1` in `r`-book-free graphs (`1 ≤ r`). -/
theorem degree_add_degree_le_card_add_sub_one_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r) (hG : IsAdmissibleBookFree G r)
    {u v : α} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ Fintype.card α + r - 1 := by
  sorry

/-- Parity-tightened Ruzsa–Szemerédi triangle packing upper bound `3 * rs(n) ≤ n * ((n - 1) / 2)`. -/
theorem three_mul_ruzsaSzemerediNumberNat_le_mul_div_two (n : ℕ) :
    3 * ruzsaSzemerediNumberNat n ≤ n * ((n - 1) / 2) := by
  sorry

/-- Global Cauchy–Schwarz second-moment triangle-incidence inequality
`9 * |T(G)|^2 ≤ |E(G)| * ∑_{e ∈ E(G)} mult(e)^2`. -/
theorem nine_mul_card_cliqueFinset_sq_le_card_edgeFinset_mul_edgeTriangleIncidenceSqSum
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    9 * (G.cliqueFinset 3).card ^ 2 ≤ G.edgeFinset.card * edgeTriangleIncidenceSqSum G := by
  sorry

/-- Universal Mantel–Turán `r`-book-free edge upper bound `maxAdmissibleEdges n r ≤ (n * (n + r - 1)) / 4`. -/
theorem maxAdmissibleEdges_le_mul_add_sub_one_div_four (n : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    maxAdmissibleEdges n r ≤ (n * (n + r - 1)) / 4 := by
  sorry

/-- Exact triangle multiplicity in a weighted vertex-blowup graph `weightedBlowupGraph H w`. -/
theorem card_trianglesContaining_weightedBlowupGraph_eq_commonNeighborWeightSum
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) {x y : BlowupVertex w}
    (hadj : (weightedBlowupGraph H w).Adj x y) :
    ((weightedBlowupGraph H w).trianglesContaining s(x, y)).card =
      commonNeighborWeightSum H w x.1 y.1 := by
  sorry

/-- Exact characterization of `r`-book-free admissibility for positive-weight vertex blow-ups. -/
theorem isAdmissibleBookFree_weightedBlowupGraph_iff_of_pos
    {α : Type*} [Fintype α] (H : SimpleGraph α) {w : α → ℕ} (r : ℕ)
    (hpos : ∀ u : α, 1 ≤ w u) :
    IsAdmissibleBookFree (weightedBlowupGraph H w) r ↔ IsAdmissibleBlowupWeight H w r := by
  sorry

/-- Exact edge-count quadratic form identity `|E(weightedBlowupGraph H w)| = blowupEdgeQuadraticForm H w`. -/
theorem card_edgeFinset_weightedBlowupGraph_eq_blowupEdgeQuadraticForm
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) :
    (weightedBlowupGraph H w).edgeFinset.card = blowupEdgeQuadraticForm H w := by
  sorry

/-- Uniform `c`-blowup quadratic scaling `c^2 * maxAdmissibleEdges m r ≤ maxAdmissibleEdges (c * m) (c * (r - 1) + 1)`. -/
theorem sq_mul_maxAdmissibleEdges_le_maxAdmissibleEdges_mul
    (m : ℕ) {r c : ℕ} (hc : 1 ≤ c) (hr : 1 ≤ r) :
    c ^ 2 * maxAdmissibleEdges m r ≤ maxAdmissibleEdges (c * m) (c * (r - 1) + 1) := by
  sorry

/-- Locally linear non-neighbor triangle partition identity `4 * t₁(u) + 6 * t₃(u) = ∑_{w ∈ R(u)} deg(w)`. -/
theorem four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_eq_sum_degree
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    4 * crossTriangleCount G u + 6 * residualTriangleCount G u =
      ∑ w ∈ nonNeighborFinset G u, G.degree w := by
  sorry

/-- Heavy-edge triangle-incidence lower bound `|E(G)| + (r - 1) * |bookHeavyEdgeFinset G r| ≤ edgeTriangleIncidenceSum G`. -/
theorem card_edgeFinset_add_sub_one_mul_card_bookHeavyEdgeFinset_le_edgeTriangleIncidenceSum
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) :
    G.edgeFinset.card + (r - 1) * (bookHeavyEdgeFinset G r).card ≤
      edgeTriangleIncidenceSum G := by
  sorry

/-- Subgraph edge-deletion reduction of `erdos_600.parts.ii` (`e(n, r+1) / e(n, r) → 1`) to
eliminating `(r+1)`-books by deleting `o(e(n, r))` edges while preserving triangle coverage. -/
theorem erdos_600_parts_ii_of_forall_exists_deleteEdges_isLittleO
    (d : ℕ → ℕ → ℕ)
    (hdel : ∀ r : ℕ, 2 ≤ r → ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      IsAdmissibleBookFree G (r + 1) →
        ∃ F : Finset (Sym2 (Fin n)), F ⊆ G.edgeFinset ∧ F.card ≤ d r n ∧
          IsAdmissibleBookFree (G.deleteEdges (F : Set (Sym2 (Fin n)))) r)
    (ho : ∀ r : ℕ, 2 ≤ r →
      (fun n : ℕ ↦ (d r n : ℝ)) =o[atTop] (fun n : ℕ ↦ (eFunction n r : ℝ))) :
    ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) / (eFunction n r : ℝ)) atTop (𝓝 1) := by
  sorry

end Erdos600
end
