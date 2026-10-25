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

public import Erdos600Unified435

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace Erdos600

open SimpleGraph Finset

/-!
# Common-Neighbor Triangle Bijection, Induced Link-Graph Handshaking, Vertex-Degree Parity, and Turán Degree-Sum Bounds for Erdős #600

This module develops 51 universally quantified (`∀`) structural theorems advancing Erdős Problem #600
with zero overlap with `Erdos600Unified435.lean`:

1. **Common-Neighbor Finset Bijection for `trianglesContaining` (Theorems 1–16):**
   - Defines `commonNeighborFinset G u v = G.neighborFinset u ∩ G.neighborFinset v`.
   - Establishes membership, symmetry, empty-graph control, endpoint irreflexivity, erased-neighborhood
     inclusions, and the inclusion–exclusion identity
     `(G.neighborFinset u ∪ G.neighborFinset v).card + (commonNeighborFinset G u v).card = G.degree u + G.degree v`.
   - Proves the exact bijection between `commonNeighborFinset G u v` and `G.trianglesContaining s(u, v)`
     for every adjacent pair `G.Adj u v` (`trianglesContaining_eq_image_commonNeighborFinset`,
     `card_trianglesContaining_eq_card_commonNeighborFinset`,
     `nonempty_trianglesContaining_iff_nonempty_commonNeighborFinset`) and characterizes
     `IsAdmissibleBookFree G r` purely in terms of common-neighbor cardinalities
     (`isAdmissibleBookFree_iff_commonNeighborFinset`).

2. **Pointwise Vertex-Degree & Edge-Degree-Sum Bounds in `r`-Book-Free Graphs (Theorems 17–26):**
   - Proves `(G.trianglesContaining s(u, v)).card + 1 ≤ G.degree u` and `2 ≤ G.degree u` for every
     endpoint of an edge in a triangle-covered / admissible graph, yielding the dichotomy
     `G.degree u = 0 ∨ 2 ≤ G.degree u` (`degree_eq_zero_or_two_le_degree_of_isAdmissibleBookFree`).
   - Proves `G.degree u + G.degree v ≤ Fintype.card α + (G.trianglesContaining s(u, v)).card`
     for any edge `G.Adj u v`, deducing the Turán pigeonhole triangle-multiplicity lower bound
     `Fintype.card α + r ≤ G.degree u + G.degree v → r ≤ (G.trianglesContaining s(u, v)).card`
     and the sharp `r`-book-free edge-degree-sum upper bound
     `G.degree u + G.degree v ≤ Fintype.card α + r - 1` (`degree_add_degree_le_card_add_sub_one_of_isAdmissibleBookFree`).

3. **Induced Link-Graph Handshaking, Local Triangle-Cluster Sums, and $r = 2$ Degree Parity (Theorems 27–38):**
   - Defines `vertexTriangleClusterSum G u = ∑ v ∈ G.neighborFinset u, (G.trianglesContaining s(u, v)).card`.
   - Proves that in the induced neighborhood (link) graph `G.induce (G.neighborSet u)`, every neighbor
     `v : G.neighborSet u` has degree `(commonNeighborFinset G u v.1).card`, establishing the exact
     link-graph handshaking identity
     `vertexTriangleClusterSum G u = 2 * (G.induce (G.neighborSet u)).edgeFinset.card`
     and universal evenness `Even (vertexTriangleClusterSum G u)`.
   - Proves the local cluster sandwich bounds
     `G.degree u ≤ vertexTriangleClusterSum G u ≤ (r - 1) * G.degree u` for `IsAdmissibleBookFree G r`.
   - Specializing to `r = 2` (`IsAdmissibleBookFree G 2` / `G.LocallyLinear`), proves that every
     induced link graph is $1$-regular (`induce_neighborSet_isRegularOfDegree_one_of_isAdmissibleBookFree_two`),
     `G.degree u = 2 * (G.induce (G.neighborSet u)).edgeFinset.card`, and every vertex has even degree
     (`even_degree_of_isAdmissibleBookFree_two`, `even_degree_of_locallyLinear`), giving the parity-tightened
     degree bound `G.degree u ≤ 2 * ((Fintype.card α - 1) / 2)` and the universal Ruzsa–Szemerédi
     packing upper bound `3 * ruzsaSzemerediNumberNat n ≤ n * ((n - 1) / 2)`.

4. **Neighborhood Degree-Sum Cauchy–Schwarz & Maximum-Degree Decomposition Bounds (Theorems 39–51):**
   - Proves `G.degree u * G.degree u + ∑ v ∈ G.neighborFinset u, G.degree v ≤ (Fintype.card α + r - 1) * G.degree u`
     for every vertex `u` in an `IsAdmissibleBookFree G r` graph (`1 ≤ r`).
   - Formalizes the exact maximum-degree vertex decomposition bound used in our 8-worker SAT solver:
     partitioning `Finset.univ` into `{u}`, `G.neighborFinset u`, and non-neighbors
     `Finset.univ \ insert u (G.neighborFinset u)` proves
     `2 * G.edgeFinset.card ≤ G.degree u + G.degree u * min (G.degree u) (Fintype.card α + r - 1 - G.degree u) + (Fintype.card α - 1 - G.degree u) * G.degree u`
     whenever `u` attains the maximum degree of `G`.
-/

section NeighborhoodDegreeAndTriangleClusterBounds
open scoped Classical

/-- The finite set of common neighbors of `u` and `v` in a finite simple graph `G`. -/
noncomputable def commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) : Finset α :=
  G.neighborFinset u ∩ G.neighborFinset v

/-- The sum of triangle multiplicities `(G.trianglesContaining s(u, v)).card` over all neighbors `v ∈ G.neighborFinset u`. -/
noncomputable def vertexTriangleClusterSum {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : ℕ :=
  ∑ v ∈ G.neighborFinset u, (G.trianglesContaining s(u, v)).card

theorem mem_commonNeighborFinset_iff {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v w : α) :
    w ∈ commonNeighborFinset G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [commonNeighborFinset, SimpleGraph.mem_neighborFinset]

theorem commonNeighborFinset_symm {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    commonNeighborFinset G u v = commonNeighborFinset G v u := by
  ext w
  simp [mem_commonNeighborFinset_iff, and_comm]

theorem commonNeighborFinset_bot (α : Type*) [Fintype α] (u v : α) :
    commonNeighborFinset (⊥ : SimpleGraph α) u v = ∅ := by
  ext w
  simp [mem_commonNeighborFinset_iff]

theorem notMem_commonNeighborFinset_left {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    u ∉ commonNeighborFinset G u v := by
  simp [mem_commonNeighborFinset_iff]

theorem notMem_commonNeighborFinset_right {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    v ∉ commonNeighborFinset G u v := by
  simp [mem_commonNeighborFinset_iff]

theorem commonNeighborFinset_subset_neighborFinset_left {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    commonNeighborFinset G u v ⊆ G.neighborFinset u :=
  Finset.inter_subset_left

theorem commonNeighborFinset_subset_neighborFinset_right {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    commonNeighborFinset G u v ⊆ G.neighborFinset v :=
  Finset.inter_subset_right

theorem commonNeighborFinset_subset_erase_neighborFinset_left {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    commonNeighborFinset G u v ⊆ (G.neighborFinset u).erase v := by
  intro w hw
  rw [Finset.mem_erase]
  refine ⟨?_, commonNeighborFinset_subset_neighborFinset_left G u v hw⟩
  rintro rfl
  exact notMem_commonNeighborFinset_right G u w hw

theorem commonNeighborFinset_subset_erase_neighborFinset_right {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    commonNeighborFinset G u v ⊆ (G.neighborFinset v).erase u := by
  rw [commonNeighborFinset_symm]
  exact commonNeighborFinset_subset_erase_neighborFinset_left G v u

theorem card_commonNeighborFinset_add_one_le_degree_left {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    (commonNeighborFinset G u v).card + 1 ≤ G.degree u := by
  have hv : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr huv
  have hsub := Finset.card_le_card (commonNeighborFinset_subset_erase_neighborFinset_left G u v)
  have herase : ((G.neighborFinset u).erase v).card + 1 = G.degree u := by
    rw [Finset.card_erase_add_one hv, SimpleGraph.card_neighborFinset_eq_degree]
  omega

theorem card_commonNeighborFinset_add_one_le_degree_right {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    (commonNeighborFinset G u v).card + 1 ≤ G.degree v := by
  rw [commonNeighborFinset_symm]
  exact card_commonNeighborFinset_add_one_le_degree_left G huv.symm

theorem card_union_neighborFinset_add_card_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    (G.neighborFinset u ∪ G.neighborFinset v).card + (commonNeighborFinset G u v).card =
      G.degree u + G.degree v := by
  simpa [commonNeighborFinset, SimpleGraph.card_neighborFinset_eq_degree] using
    Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)

theorem degree_add_degree_le_card_add_card_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u v : α) :
    G.degree u + G.degree v ≤ Fintype.card α + (commonNeighborFinset G u v).card := by
  rw [← card_union_neighborFinset_add_card_commonNeighborFinset G u v]
  have hle : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card α :=
    Finset.card_le_univ _
  omega

theorem insert_mem_trianglesContaining_of_mem_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v w : α} (huv : G.Adj u v)
    (hw : w ∈ commonNeighborFinset G u v) :
    insert w ({u, v} : Finset α) ∈ G.trianglesContaining s(u, v) := by
  rw [mem_commonNeighborFinset_iff] at hw
  rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.is3Clique_iff]
    exact ⟨w, u, v, hw.1.symm, hw.2.symm, huv, rfl⟩
  · rw [Finset.mem_sym2_iff]
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simp

theorem trianglesContaining_eq_image_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    G.trianglesContaining s(u, v) =
      (commonNeighborFinset G u v).image (fun w : α ↦ insert w ({u, v} : Finset α)) := by
  have huv_ne : u ≠ v := G.ne_of_adj huv
  have htwo : ({u, v} : Finset α).card = 2 := Finset.card_pair huv_ne
  ext t
  simp only [Finset.mem_image]
  constructor
  · intro ht
    rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff] at ht
    obtain ⟨hclique, hsym⟩ := ht
    have hu_mem : u ∈ t := Finset.mem_sym2_iff.mp hsym u (Sym2.mem_mk_left u v)
    have hv_mem : v ∈ t := Finset.mem_sym2_iff.mp hsym v (Sym2.mem_mk_right u v)
    have hsub_uv : ({u, v} : Finset α) ⊆ t := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx2
      · exact hu_mem
      · rw [Finset.mem_singleton.mp hx2]
        exact hv_mem
    have hcard_t : t.card = 3 := hclique.card_eq
    have hcard_sdiff : (t \ {u, v}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub_uv, hcard_t, htwo]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard_sdiff
    have hw_mem : w ∈ t \ {u, v} := by rw [hw]; simp
    have hw_t : w ∈ t := (Finset.mem_sdiff.mp hw_mem).1
    have hw_not : w ∉ ({u, v} : Finset α) := (Finset.mem_sdiff.mp hw_mem).2
    have huw_ne : u ≠ w := by rintro rfl; exact hw_not (by simp)
    have hvw_ne : v ≠ w := by rintro rfl; exact hw_not (by simp)
    have huw : G.Adj u w := hclique.isClique hu_mem hw_t huw_ne
    have hvw : G.Adj v w := hclique.isClique hv_mem hw_t hvw_ne
    refine ⟨w, (mem_commonNeighborFinset_iff G u v w).mpr ⟨huw, hvw⟩, ?_⟩
    calc
      insert w ({u, v} : Finset α) = {w} ∪ {u, v} := (Finset.singleton_union w {u, v}).symm
      _ = (t \ {u, v}) ∪ {u, v} := by rw [hw]
      _ = t := Finset.sdiff_union_of_subset hsub_uv
  · rintro ⟨w, hw, rfl⟩
    exact insert_mem_trianglesContaining_of_mem_commonNeighborFinset G huv hw

theorem card_trianglesContaining_eq_card_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    (G.trianglesContaining s(u, v)).card = (commonNeighborFinset G u v).card := by
  rw [trianglesContaining_eq_image_commonNeighborFinset G huv, Finset.card_image_of_injOn]
  intro w₁ hw₁ w₂ _ hw_eq
  dsimp at hw_eq
  rw [Finset.mem_coe, mem_commonNeighborFinset_iff] at hw₁
  have hw₁_not : w₁ ∉ ({u, v} : Finset α) := by
    simp [G.ne_of_adj hw₁.1.symm, G.ne_of_adj hw₁.2.symm]
  have hmem : w₁ ∈ (insert w₂ ({u, v} : Finset α) : Finset α) := by
    rw [← hw_eq]
    exact Finset.mem_insert_self w₁ {u, v}
  rcases Finset.mem_insert.mp hmem with rfl | h2
  · rfl
  · exact (hw₁_not h2).elim

theorem nonempty_trianglesContaining_iff_nonempty_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    (G.trianglesContaining s(u, v)).Nonempty ↔ (commonNeighborFinset G u v).Nonempty := by
  rw [← Finset.card_pos, ← Finset.card_pos,
    card_trianglesContaining_eq_card_commonNeighborFinset G huv]

theorem isAdmissibleBookFree_iff_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) :
    IsAdmissibleBookFree G r ↔
      (∀ u v : α, G.Adj u v → (commonNeighborFinset G u v).Nonempty) ∧
        (∀ u v : α, G.Adj u v → (commonNeighborFinset G u v).card < r) := by
  unfold IsAdmissibleBookFree
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun u v huv ↦ ?_, fun u v huv ↦ ?_⟩
    · rw [← nonempty_trianglesContaining_iff_nonempty_commonNeighborFinset G huv]
      exact h1 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)
    · rw [← card_trianglesContaining_eq_card_commonNeighborFinset G huv]
      exact h2 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)
  · rintro ⟨h1, h2⟩
    refine ⟨fun uv huv ↦ ?_, fun uv huv ↦ ?_⟩
    · induction uv using Sym2.ind with
      | _ u v =>
        have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp huv
        rw [nonempty_trianglesContaining_iff_nonempty_commonNeighborFinset G hadj]
        exact h1 u v hadj
    · induction uv using Sym2.ind with
      | _ u v =>
        have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp huv
        rw [card_trianglesContaining_eq_card_commonNeighborFinset G hadj]
        exact h2 u v hadj

theorem card_trianglesContaining_add_one_le_degree_left {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    (G.trianglesContaining s(u, v)).card + 1 ≤ G.degree u := by
  rw [card_trianglesContaining_eq_card_commonNeighborFinset G huv]
  exact card_commonNeighborFinset_add_one_le_degree_left G huv

theorem card_trianglesContaining_add_one_le_degree_right {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    (G.trianglesContaining s(u, v)).card + 1 ≤ G.degree v := by
  rw [card_trianglesContaining_eq_card_commonNeighborFinset G huv]
  exact card_commonNeighborFinset_add_one_le_degree_right G huv

theorem two_le_degree_of_adj_of_nonempty_trianglesContaining {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v)
    (hne : (G.trianglesContaining s(u, v)).Nonempty) :
    2 ≤ G.degree u := by
  have hpos : 1 ≤ (G.trianglesContaining s(u, v)).card := Finset.card_pos.mpr hne
  have hle := card_trianglesContaining_add_one_le_degree_left G huv
  omega

theorem two_le_degree_of_adj_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r)
    {u v : α} (huv : G.Adj u v) :
    2 ≤ G.degree u :=
  two_le_degree_of_adj_of_nonempty_trianglesContaining G huv
    (hG.1 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv))

theorem degree_eq_zero_or_two_le_degree_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r) (u : α) :
    G.degree u = 0 ∨ 2 ≤ G.degree u := by
  by_cases h0 : G.degree u = 0
  · exact Or.inl h0
  · right
    have hpos : 0 < (G.neighborFinset u).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
    exact two_le_degree_of_adj_of_isAdmissibleBookFree hG huv

theorem degree_add_degree_le_card_add_card_trianglesContaining {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ Fintype.card α + (G.trianglesContaining s(u, v)).card := by
  rw [card_trianglesContaining_eq_card_commonNeighborFinset G huv]
  exact degree_add_degree_le_card_add_card_commonNeighborFinset G u v

theorem le_card_trianglesContaining_of_card_add_le_degree_add_degree {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} {r : ℕ} (huv : G.Adj u v)
    (hdeg : Fintype.card α + r ≤ G.degree u + G.degree v) :
    r ≤ (G.trianglesContaining s(u, v)).card := by
  have hle := degree_add_degree_le_card_add_card_trianglesContaining G huv
  omega

theorem degree_add_degree_lt_card_add_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r)
    {u v : α} (huv : G.Adj u v) :
    G.degree u + G.degree v < Fintype.card α + r := by
  have hle := degree_add_degree_le_card_add_card_trianglesContaining G huv
  have hlt := hG.2 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)
  omega

theorem degree_add_degree_le_card_add_sub_one_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r) (hG : IsAdmissibleBookFree G r)
    {u v : α} (huv : G.Adj u v) :
    G.degree u + G.degree v ≤ Fintype.card α + r - 1 := by
  have hlt := degree_add_degree_lt_card_add_of_isAdmissibleBookFree hG huv
  omega

theorem not_isAdmissibleBookFree_of_adj_of_card_add_le_degree_add_degree
    {α : Type*} [Fintype α] (G : SimpleGraph α) {u v : α} {r : ℕ}
    (huv : G.Adj u v) (hdeg : Fintype.card α + r ≤ G.degree u + G.degree v) :
    ¬ IsAdmissibleBookFree G r := by
  intro hG
  have hlt := degree_add_degree_lt_card_add_of_isAdmissibleBookFree hG huv
  omega

theorem vertexTriangleClusterSum_bot (α : Type*) [Fintype α] (u : α) :
    vertexTriangleClusterSum (⊥ : SimpleGraph α) u = 0 := by
  simp [vertexTriangleClusterSum]

theorem vertexTriangleClusterSum_eq_sum_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    vertexTriangleClusterSum G u =
      ∑ v ∈ G.neighborFinset u, (commonNeighborFinset G u v).card := by
  unfold vertexTriangleClusterSum
  refine Finset.sum_congr rfl (fun v hv ↦ ?_)
  have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
  exact card_trianglesContaining_eq_card_commonNeighborFinset G huv

theorem induce_neighborSet_neighborFinset_map {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) (v : G.neighborSet u) :
    ((G.induce (G.neighborSet u)).neighborFinset v).map (Function.Embedding.subtype _) =
      commonNeighborFinset G u v.1 := by
  ext w
  simp only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
    SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj, SimpleGraph.mem_neighborSet,
    mem_commonNeighborFinset_iff]
  constructor
  · rintro ⟨x, hx, hvx, rfl⟩
    exact ⟨hx, hvx⟩
  · rintro ⟨huw, hvw⟩
    exact ⟨w, huw, hvw, rfl⟩

theorem induce_neighborSet_degree_eq_card_commonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) (v : G.neighborSet u) :
    (G.induce (G.neighborSet u)).degree v = (commonNeighborFinset G u v.1).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← induce_neighborSet_neighborFinset_map G u v, Finset.card_map]

theorem sum_neighborSet_subtype_eq_sum_neighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) (f : α → ℕ) :
    (∑ v : G.neighborSet u, f v.1) = ∑ v ∈ G.neighborFinset u, f v := by
  have heq : G.neighborFinset u =
      (Finset.univ : Finset (G.neighborSet u)).map (Function.Embedding.subtype _) := by
    ext x
    simp [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet]
  rw [heq, Finset.sum_map]
  rfl

theorem sum_neighborFinset_card_commonNeighborFinset_eq_twice_card_induce_edgeFinset
    {α : Type*} [Fintype α] (G : SimpleGraph α) (u : α) :
    ∑ v ∈ G.neighborFinset u, (commonNeighborFinset G u v).card =
      2 * (G.induce (G.neighborSet u)).edgeFinset.card := by
  rw [← sum_neighborSet_subtype_eq_sum_neighborFinset G u
    (fun v ↦ (commonNeighborFinset G u v).card)]
  have hdeg : (∑ v : G.neighborSet u, (commonNeighborFinset G u v.1).card) =
      ∑ v : G.neighborSet u, (G.induce (G.neighborSet u)).degree v := by
    refine Finset.sum_congr rfl (fun v _ ↦ ?_)
    exact (induce_neighborSet_degree_eq_card_commonNeighborFinset G u v).symm
  rw [hdeg, SimpleGraph.sum_degrees_eq_twice_card_edges]

theorem vertexTriangleClusterSum_eq_twice_card_induce_edgeFinset
    {α : Type*} [Fintype α] (G : SimpleGraph α) (u : α) :
    vertexTriangleClusterSum G u =
      2 * (G.induce (G.neighborSet u)).edgeFinset.card := by
  rw [vertexTriangleClusterSum_eq_sum_commonNeighborFinset,
    sum_neighborFinset_card_commonNeighborFinset_eq_twice_card_induce_edgeFinset]

theorem even_vertexTriangleClusterSum {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    Even (vertexTriangleClusterSum G u) := by
  rw [vertexTriangleClusterSum_eq_twice_card_induce_edgeFinset]
  exact even_two_mul _

theorem degree_le_vertexTriangleClusterSum_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r) (u : α) :
    G.degree u ≤ vertexTriangleClusterSum G u := by
  rw [ ← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones]
  unfold vertexTriangleClusterSum
  refine Finset.sum_le_sum (fun v hv ↦ ?_)
  have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
  exact Finset.card_pos.mpr (hG.1 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv))

theorem vertexTriangleClusterSum_le_sub_one_mul_degree_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) (u : α) :
    vertexTriangleClusterSum G u ≤ (r - 1) * G.degree u := by
  have hle : vertexTriangleClusterSum G u ≤ ∑ _v ∈ G.neighborFinset u, (r - 1) := by
    unfold vertexTriangleClusterSum
    refine Finset.sum_le_sum (fun v hv ↦ ?_)
    have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
    have hlt := hG.2 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)
    omega
  simpa [SimpleGraph.card_neighborFinset_eq_degree, Nat.mul_comm] using hle

theorem card_trianglesContaining_eq_one_of_isAdmissibleBookFree_two {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) {uv : Sym2 α}
    (huv : uv ∈ G.edgeFinset) :
    (G.trianglesContaining uv).card = 1 := by
  have hpos : 0 < (G.trianglesContaining uv).card := Finset.card_pos.mpr (hG.1 uv huv)
  have hlt : (G.trianglesContaining uv).card < 2 := hG.2 uv huv
  omega

theorem induce_neighborSet_isRegularOfDegree_one_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    (G.induce (G.neighborSet u)).IsRegularOfDegree 1 := by
  intro v
  rw [induce_neighborSet_degree_eq_card_commonNeighborFinset]
  have huv : G.Adj u v.1 := v.2
  rw [← card_trianglesContaining_eq_card_commonNeighborFinset G huv]
  exact card_trianglesContaining_eq_one_of_isAdmissibleBookFree_two hG
    (SimpleGraph.mem_edgeFinset.mpr huv)

theorem vertexTriangleClusterSum_eq_degree_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    vertexTriangleClusterSum G u = G.degree u := by
  have h1 := degree_le_vertexTriangleClusterSum_of_isAdmissibleBookFree hG u
  have h2 := vertexTriangleClusterSum_le_sub_one_mul_degree_of_isAdmissibleBookFree
    (by omega : 1 ≤ 2) hG u
  omega

theorem degree_eq_twice_card_induce_edgeFinset_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    G.degree u = 2 * (G.induce (G.neighborSet u)).edgeFinset.card := by
  rw [← vertexTriangleClusterSum_eq_degree_of_isAdmissibleBookFree_two hG u,
    vertexTriangleClusterSum_eq_twice_card_induce_edgeFinset]

theorem even_degree_of_isAdmissibleBookFree_two {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    Even (G.degree u) := by
  rw [degree_eq_twice_card_induce_edgeFinset_of_isAdmissibleBookFree_two hG u]
  exact even_two_mul _

theorem even_degree_of_locallyLinear {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : G.LocallyLinear) (u : α) :
    Even (G.degree u) :=
  even_degree_of_isAdmissibleBookFree_two
    ((locallyLinear_iff_trianglesContaining G).mp hG) u

theorem degree_le_two_mul_div_two_of_isAdmissibleBookFree_two {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    G.degree u ≤ 2 * ((Fintype.card α - 1) / 2) := by
  have hlt : G.degree u ≤ Fintype.card α - 1 := by
    have h := G.degree_lt_card_verts u
    omega
  obtain ⟨k, hk⟩ := even_degree_of_isAdmissibleBookFree_two hG u
  omega

theorem card_edgeFinset_le_mul_div_two_of_isAdmissibleBookFree_two {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) :
    G.edgeFinset.card ≤ Fintype.card α * ((Fintype.card α - 1) / 2) := by
  have hsum : ∑ u : α, G.degree u ≤ ∑ _u : α, 2 * ((Fintype.card α - 1) / 2) :=
    Finset.sum_le_sum (fun u _ ↦ degree_le_two_mul_div_two_of_isAdmissibleBookFree_two hG u)
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hsum
  have hmul : Fintype.card α * (2 * ((Fintype.card α - 1) / 2)) =
      2 * (Fintype.card α * ((Fintype.card α - 1) / 2)) := by ring
  omega

theorem maxAdmissibleEdges_two_le_mul_div_two (n : ℕ) :
    maxAdmissibleEdges n 2 ≤ n * ((n - 1) / 2) := by
  obtain ⟨G, hG, hcard⟩ := exists_isAdmissibleBookFree_card_eq_maxAdmissibleEdges n 2
  have hle := card_edgeFinset_le_mul_div_two_of_isAdmissibleBookFree_two hG
  simpa [hcard] using hle

theorem eFunction_two_le_mul_div_two_add_one (n : ℕ) :
    eFunction n 2 ≤ n * ((n - 1) / 2) + 1 := by
  rw [eFunction_eq_maxAdmissibleEdges_add_one]
  exact Nat.add_le_add_right (maxAdmissibleEdges_two_le_mul_div_two n) 1

theorem three_mul_ruzsaSzemerediNumberNat_le_mul_div_two (n : ℕ) :
    3 * ruzsaSzemerediNumberNat n ≤ n * ((n - 1) / 2) := by
  have hle := eFunction_two_le_mul_div_two_add_one n
  have he2 : eFunction n 2 = 3 * ruzsaSzemerediNumberNat n + 1 := eFunction_two_eq n
  omega

theorem two_mul_card_edgeFinset_le_sum_vertexTriangleClusterSum_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r) :
    2 * G.edgeFinset.card ≤ ∑ u : α, vertexTriangleClusterSum G u := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  exact Finset.sum_le_sum (fun u _ ↦ degree_le_vertexTriangleClusterSum_of_isAdmissibleBookFree hG u)

theorem sum_vertexTriangleClusterSum_le_two_mul_sub_one_mul_card_edgeFinset_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) :
    ∑ u : α, vertexTriangleClusterSum G u ≤ 2 * (r - 1) * G.edgeFinset.card := by
  calc
    ∑ u : α, vertexTriangleClusterSum G u
      ≤ ∑ u : α, (r - 1) * G.degree u :=
        Finset.sum_le_sum (fun u _ ↦
          vertexTriangleClusterSum_le_sub_one_mul_degree_of_isAdmissibleBookFree hr hG u)
    _ = (r - 1) * ∑ u : α, G.degree u := by rw [← Finset.mul_sum]
    _ = (r - 1) * (2 * G.edgeFinset.card) := by
      rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    _ = 2 * (r - 1) * G.edgeFinset.card := by ring

theorem sum_vertexTriangleClusterSum_eq_two_mul_card_edgeFinset_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) :
    ∑ u : α, vertexTriangleClusterSum G u = 2 * G.edgeFinset.card := by
  have h1 := two_mul_card_edgeFinset_le_sum_vertexTriangleClusterSum_of_isAdmissibleBookFree hG
  have h2 :=
    sum_vertexTriangleClusterSum_le_two_mul_sub_one_mul_card_edgeFinset_of_isAdmissibleBookFree
      (by omega : 1 ≤ 2) hG
  omega

theorem degree_sq_add_sum_neighborFinset_degree_le_card_mul_degree_add_vertexTriangleClusterSum
    {α : Type*} [Fintype α] (G : SimpleGraph α) (u : α) :
    G.degree u * G.degree u + ∑ v ∈ G.neighborFinset u, G.degree v ≤
      Fintype.card α * G.degree u + vertexTriangleClusterSum G u := by
  have hsum : ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v) ≤
      ∑ v ∈ G.neighborFinset u, (Fintype.card α + (G.trianglesContaining s(u, v)).card) := by
    refine Finset.sum_le_sum (fun v hv ↦ ?_)
    have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
    exact degree_add_degree_le_card_add_card_trianglesContaining G huv
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul, smul_eq_mul,
    Nat.mul_comm (G.degree u) (Fintype.card α)] at hsum
  exact hsum

theorem degree_sq_add_sum_neighborFinset_degree_le_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) (u : α) :
    G.degree u * G.degree u + ∑ v ∈ G.neighborFinset u, G.degree v ≤
      (Fintype.card α + r - 1) * G.degree u := by
  have h1 :=
    degree_sq_add_sum_neighborFinset_degree_le_card_mul_degree_add_vertexTriangleClusterSum G u
  have h2 := vertexTriangleClusterSum_le_sub_one_mul_degree_of_isAdmissibleBookFree hr hG u
  calc
    G.degree u * G.degree u + ∑ v ∈ G.neighborFinset u, G.degree v
      ≤ Fintype.card α * G.degree u + vertexTriangleClusterSum G u := h1
    _ ≤ Fintype.card α * G.degree u + (r - 1) * G.degree u := Nat.add_le_add_left h2 _
    _ = (Fintype.card α + r - 1) * G.degree u := by
      rw [← Nat.add_mul]
      congr 1
      omega

theorem card_sdiff_insert_neighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    ((Finset.univ : Finset α) \ insert u (G.neighborFinset u)).card =
      Fintype.card α - 1 - G.degree u := by
  have hsub : insert u (G.neighborFinset u) ⊆ (Finset.univ : Finset α) := Finset.subset_univ _
  have hu : u ∉ G.neighborFinset u := SimpleGraph.notMem_neighborFinset_self G u
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Finset.card_insert_of_notMem hu,
    SimpleGraph.card_neighborFinset_eq_degree]
  omega

theorem sum_univ_eq_add_sum_neighborFinset_add_sum_nonNeighbors {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) (f : α → ℕ) :
    (∑ x : α, f x) =
      f u + (∑ v ∈ G.neighborFinset u, f v) +
        (∑ w ∈ (Finset.univ : Finset α) \ insert u (G.neighborFinset u), f w) := by
  have hsub : insert u (G.neighborFinset u) ⊆ (Finset.univ : Finset α) := Finset.subset_univ _
  have hu : u ∉ G.neighborFinset u := SimpleGraph.notMem_neighborFinset_self G u
  have h1 := (Finset.sum_sdiff hsub (f := f)).symm
  rw [Finset.sum_insert hu] at h1
  omega

theorem twice_card_edgeFinset_le_of_max_degree_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) (u : α) (hmax : ∀ x : α, G.degree x ≤ G.degree u) :
    2 * G.edgeFinset.card ≤
      G.degree u +
        G.degree u * min (G.degree u) (Fintype.card α + r - 1 - G.degree u) +
        (Fintype.card α - 1 - G.degree u) * G.degree u := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges,
    sum_univ_eq_add_sum_neighborFinset_add_sum_nonNeighbors G u (fun x ↦ G.degree x)]
  have hN : ∑ v ∈ G.neighborFinset u, G.degree v ≤
      G.degree u * min (G.degree u) (Fintype.card α + r - 1 - G.degree u) := by
    calc
      ∑ v ∈ G.neighborFinset u, G.degree v
        ≤ ∑ _v ∈ G.neighborFinset u, min (G.degree u) (Fintype.card α + r - 1 - G.degree u) := by
          refine Finset.sum_le_sum (fun v hv ↦ ?_)
          have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
          have hdeg := degree_add_degree_le_card_add_sub_one_of_isAdmissibleBookFree hr hG huv
          have hm := hmax v
          omega
      _ = G.degree u * min (G.degree u) (Fintype.card α + r - 1 - G.degree u) := by
        rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul]
  have hR : ∑ w ∈ (Finset.univ : Finset α) \ insert u (G.neighborFinset u), G.degree w ≤
      (Fintype.card α - 1 - G.degree u) * G.degree u := by
    calc
      ∑ w ∈ (Finset.univ : Finset α) \ insert u (G.neighborFinset u), G.degree w
        ≤ ∑ _w ∈ (Finset.univ : Finset α) \ insert u (G.neighborFinset u), G.degree u :=
          Finset.sum_le_sum (fun w _ ↦ hmax w)
      _ = (Fintype.card α - 1 - G.degree u) * G.degree u := by
        rw [Finset.sum_const, card_sdiff_insert_neighborFinset, smul_eq_mul]
  omega

end NeighborhoodDegreeAndTriangleClusterBounds

end Erdos600
