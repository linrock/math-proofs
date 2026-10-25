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
public import NeighborhoodDegreeAndTriangleClusterBounds600
public import LinkGraphCycleDeficitAndTriangleCauchySchwarz600
public import WeightedVertexBlowupAndStepDifferenceBounds600

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Topology Classical

namespace Erdos600

open SimpleGraph Finset Filter Asymptotics

/-!
# Non-Neighbor Triangle Partition (`4 * t₁ + 6 * t₃ ≤ |R| * G.degree u`) and `r`-Book Edge-Deletion Subgraphs for Erdős #600
-/

section NonNeighborTrianglePartitionAndBookEdgeDeletion

/-- The residual non-neighbor finset `R(u) = V \ ({u} ∪ N(u))` of vertices neither equal to
nor adjacent to `u`. -/
noncomputable def nonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset α :=
  (Finset.univ : Finset α) \ insert u (G.neighborFinset u)

/-- Triangles of `G` containing vertex `u`. -/
noncomputable def vertexIncidentTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ u ∈ t)

/-- Triangles of `G` avoiding vertex `u` (`u ∉ t`). -/
noncomputable def avoidingTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ u ∉ t)

/-- Cross-triangles `(N(u), R(u), R(u))` avoiding `u` with exactly one vertex in `N(u)`
(and two vertices in `R(u)`). -/
noncomputable def crossTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset (Finset α) :=
  (avoidingTriangles G u).filter (fun t ↦ (t ∩ G.neighborFinset u).card = 1)

/-- Internal residual triangles `(R(u), R(u), R(u))` avoiding `u` with zero vertices in `N(u)`
(and all three vertices in `R(u)`). -/
noncomputable def residualTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset (Finset α) :=
  (avoidingTriangles G u).filter (fun t ↦ (t ∩ G.neighborFinset u).card = 0)

/-- Number `t₀(u)` of triangles containing `u`. -/
noncomputable def vertexIncidentTriangleCount {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : ℕ :=
  (vertexIncidentTriangles G u).card

/-- Number `t₁(u)` of `(N(u), R(u), R(u))` cross-triangles avoiding `u`. -/
noncomputable def crossTriangleCount {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : ℕ :=
  (crossTriangles G u).card

/-- Number `t₃(u)` of `(R(u), R(u), R(u))` internal residual triangles avoiding `u`. -/
noncomputable def residualTriangleCount {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : ℕ :=
  (residualTriangles G u).card

theorem mem_nonNeighborFinset_iff {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u w : α) :
    w ∈ nonNeighborFinset G u ↔ w ≠ u ∧ ¬ G.Adj u w := by
  simp [nonNeighborFinset, SimpleGraph.mem_neighborFinset]

theorem notMem_nonNeighborFinset_self {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    u ∉ nonNeighborFinset G u := by
  simp [mem_nonNeighborFinset_iff]

theorem notMem_nonNeighborFinset_of_adj {α : Type*} [Fintype α]
    (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
    v ∉ nonNeighborFinset G u := by
  rw [mem_nonNeighborFinset_iff]
  intro h
  exact h.2 huv

theorem disjoint_neighborFinset_nonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    Disjoint (G.neighborFinset u) (nonNeighborFinset G u) := by
  rw [Finset.disjoint_left]
  intro x hx hnon
  exact notMem_nonNeighborFinset_of_adj G ((SimpleGraph.mem_neighborFinset G u x).mp hx) hnon

theorem card_nonNeighborFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    (nonNeighborFinset G u).card = Fintype.card α - 1 - G.degree u :=
  card_sdiff_insert_neighborFinset G u

theorem inter_neighborFinset_union_inter_nonNeighborFinset_of_notMem {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (hu : u ∉ t) :
    (t ∩ G.neighborFinset u) ∪ (t ∩ nonNeighborFinset G u) = t := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    mem_nonNeighborFinset_iff]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    have hne : x ≠ u := by rintro rfl; exact hu hx
    by_cases hadj : G.Adj u x
    · exact Or.inl ⟨hx, hadj⟩
    · exact Or.inr ⟨hx, hne, hadj⟩

theorem card_inter_neighborFinset_add_card_inter_nonNeighborFinset_of_notMem
    {α : Type*} [Fintype α] (G : SimpleGraph α) (u : α) {t : Finset α} (hu : u ∉ t) :
    (t ∩ G.neighborFinset u).card + (t ∩ nonNeighborFinset G u).card = t.card := by
  have hdisj : Disjoint (t ∩ G.neighborFinset u) (t ∩ nonNeighborFinset G u) :=
    (disjoint_neighborFinset_nonNeighborFinset G u).mono
      Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_union_of_disjoint hdisj,
    inter_neighborFinset_union_inter_nonNeighborFinset_of_notMem G u hu]

theorem card_inter_neighborFinset_add_card_inter_nonNeighborFinset_of_mem_avoidingTriangles
    {α : Type*} [Fintype α] (G : SimpleGraph α) (u : α) {t : Finset α}
    (ht : t ∈ avoidingTriangles G u) :
    (t ∩ G.neighborFinset u).card + (t ∩ nonNeighborFinset G u).card = 3 := by
  rw [avoidingTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  rw [card_inter_neighborFinset_add_card_inter_nonNeighborFinset_of_notMem G u ht.2,
    ht.1.card_eq]

theorem card_inter_nonNeighborFinset_of_mem_crossTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ crossTriangles G u) :
    (t ∩ nonNeighborFinset G u).card = 2 := by
  rw [crossTriangles, Finset.mem_filter] at ht
  have hsum :=
    card_inter_neighborFinset_add_card_inter_nonNeighborFinset_of_mem_avoidingTriangles G u ht.1
  omega

theorem card_inter_nonNeighborFinset_of_mem_residualTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ residualTriangles G u) :
    (t ∩ nonNeighborFinset G u).card = 3 := by
  rw [residualTriangles, Finset.mem_filter] at ht
  have hsum :=
    card_inter_neighborFinset_add_card_inter_nonNeighborFinset_of_mem_avoidingTriangles G u ht.1
  omega

theorem subset_nonNeighborFinset_of_mem_residualTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ residualTriangles G u) :
    t ⊆ nonNeighborFinset G u := by
  have h0 : t ∩ G.neighborFinset u = ∅ :=
    Finset.card_eq_zero.mp (Finset.mem_filter.mp ht).2
  have hu : u ∉ t := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
  have hunion := inter_neighborFinset_union_inter_nonNeighborFinset_of_notMem G u hu
  rw [h0, Finset.empty_union] at hunion
  rw [← hunion]
  exact Finset.inter_subset_right

theorem inter_neighborFinset_eq_erase_of_mem_vertexIncidentTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ vertexIncidentTriangles G u) :
    t ∩ G.neighborFinset u = t.erase u := by
  rw [vertexIncidentTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  ext x
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  exact ⟨fun ⟨hx, hux⟩ ↦ ⟨G.ne_of_adj hux.symm, hx⟩,
    fun ⟨hne, hx⟩ ↦ ⟨hx, ht.1.isClique ht.2 hx hne.symm⟩⟩

theorem card_inter_neighborFinset_of_mem_vertexIncidentTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ vertexIncidentTriangles G u) :
    (t ∩ G.neighborFinset u).card = 2 := by
  rw [inter_neighborFinset_eq_erase_of_mem_vertexIncidentTriangles G u ht]
  rw [vertexIncidentTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  have hcard : t.card = 3 := ht.1.card_eq
  have herase := Finset.card_erase_add_one ht.2
  omega

theorem inter_nonNeighborFinset_eq_empty_of_mem_vertexIncidentTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ vertexIncidentTriangles G u) :
    t ∩ nonNeighborFinset G u = ∅ := by
  rw [vertexIncidentTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_inter, mem_nonNeighborFinset_iff] at hx
  exact hx.2.2 (ht.1.isClique ht.2 hx.1 hx.2.1.symm)

theorem card_inter_nonNeighborFinset_of_mem_vertexIncidentTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ vertexIncidentTriangles G u) :
    (t ∩ nonNeighborFinset G u).card = 0 := by
  rw [inter_nonNeighborFinset_eq_empty_of_mem_vertexIncidentTriangles G u ht, Finset.card_empty]

theorem edgeDisjointTriangles_of_isAdmissibleBookFree_two {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) :
    G.EdgeDisjointTriangles := by
  rw [edgeDisjointTriangles_iff_forall_trianglesContaining_card_le_one]
  intro uv huv
  have hlt := hG.2 uv huv
  omega

theorem card_inter_neighborFinset_le_one_of_mem_avoidingTriangles_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles)
    (u : α) {t : Finset α} (ht : t ∈ avoidingTriangles G u) :
    (t ∩ G.neighborFinset u).card ≤ 1 := by
  by_contra hgt
  have hlt : 1 < (t ∩ G.neighborFinset u).card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx hy
  rw [avoidingTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  obtain ⟨hclique, hu_not⟩ := ht
  have hadj_xy : G.Adj x y := hclique.isClique hx.1 hy.1 hxy
  have ht_mem : t ∈ G.trianglesContaining s(x, y) := by
    rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨hclique, Finset.mem_sym2_iff.mpr ?_⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> [exact hx.1; exact hy.1]
  have hu_common : u ∈ commonNeighborFinset G x y := by
    rw [mem_commonNeighborFinset_iff]
    exact ⟨hx.2.symm, hy.2.symm⟩
  have hins_mem : insert u ({x, y} : Finset α) ∈ G.trianglesContaining s(x, y) :=
    insert_mem_trianglesContaining_of_mem_commonNeighborFinset G hadj_xy hu_common
  have hne_t : t ≠ insert u ({x, y} : Finset α) := by
    intro heq
    have : u ∈ t := by rw [heq]; exact Finset.mem_insert_self u {x, y}
    exact hu_not this
  have hle1 : (G.trianglesContaining s(x, y)).card ≤ 1 :=
    (edgeDisjointTriangles_iff_forall_trianglesContaining_card_le_one G).mp hed
      s(x, y) (SimpleGraph.mem_edgeFinset.mpr hadj_xy)
  exact hne_t (Finset.card_le_one.mp hle1 t ht_mem (insert u {x, y}) hins_mem)

theorem avoidingTriangles_eq_union_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    avoidingTriangles G u = crossTriangles G u ∪ residualTriangles G u := by
  ext t
  simp only [Finset.mem_union, crossTriangles, residualTriangles, Finset.mem_filter]
  constructor
  · intro ht
    have hle :=
      card_inter_neighborFinset_le_one_of_mem_avoidingTriangles_of_edgeDisjointTriangles hed u ht
    rcases (by omega : (t ∩ G.neighborFinset u).card = 1 ∨ (t ∩ G.neighborFinset u).card = 0) with
      h1 | h0
    · exact Or.inl ⟨ht, h1⟩
    · exact Or.inr ⟨ht, h0⟩
  · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht

theorem disjoint_crossTriangles_residualTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    Disjoint (crossTriangles G u) (residualTriangles G u) := by
  rw [Finset.disjoint_left]
  intro t h1 h0
  rw [crossTriangles, Finset.mem_filter] at h1
  rw [residualTriangles, Finset.mem_filter] at h0
  omega

theorem card_avoidingTriangles_eq_add_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    (avoidingTriangles G u).card = crossTriangleCount G u + residualTriangleCount G u := by
  rw [avoidingTriangles_eq_union_of_edgeDisjointTriangles hed u,
    Finset.card_union_of_disjoint (disjoint_crossTriangles_residualTriangles G u)]
  rfl

theorem card_avoidingTriangles_eq_add_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    (avoidingTriangles G u).card = crossTriangleCount G u + residualTriangleCount G u :=
  card_avoidingTriangles_eq_add_of_edgeDisjointTriangles
    (edgeDisjointTriangles_of_isAdmissibleBookFree_two hG) u

theorem sum_cliqueFinset_eq_add_sum_vertexIncident_avoiding {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) (f : Finset α → ℕ) :
    (∑ t ∈ G.cliqueFinset 3, f t) =
      (∑ t ∈ vertexIncidentTriangles G u, f t) + (∑ t ∈ avoidingTriangles G u, f t) := by
  unfold vertexIncidentTriangles avoidingTriangles
  exact (Finset.sum_filter_add_sum_filter_not (G.cliqueFinset 3) (fun t ↦ u ∈ t) f).symm

theorem card_cliqueFinset_three_eq_add_vertexIncident_avoiding {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    (G.cliqueFinset 3).card = vertexIncidentTriangleCount G u + (avoidingTriangles G u).card := by
  have h := sum_cliqueFinset_eq_add_sum_vertexIncident_avoiding G u (fun _ ↦ 1)
  simpa [vertexIncidentTriangleCount] using h

theorem card_cliqueFinset_three_eq_add_of_edgeDisjointTriangles {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    (G.cliqueFinset 3).card =
      vertexIncidentTriangleCount G u + crossTriangleCount G u + residualTriangleCount G u := by
  rw [card_cliqueFinset_three_eq_add_vertexIncident_avoiding G u,
    card_avoidingTriangles_eq_add_of_edgeDisjointTriangles hed u, Nat.add_assoc]

theorem sum_avoidingTriangles_eq_add_of_edgeDisjointTriangles {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) (f : Finset α → ℕ) :
    (∑ t ∈ avoidingTriangles G u, f t) =
      (∑ t ∈ crossTriangles G u, f t) + (∑ t ∈ residualTriangles G u, f t) := by
  rw [avoidingTriangles_eq_union_of_edgeDisjointTriangles hed u,
    Finset.sum_union (disjoint_crossTriangles_residualTriangles G u)]

theorem sum_card_vertexIncidentTriangles_eq_sum_card_inter {α : Type*} [Fintype α]
    (G : SimpleGraph α) (S : Finset α) :
    (∑ x ∈ S, vertexIncidentTriangleCount G x) =
      ∑ t ∈ G.cliqueFinset 3, (t ∩ S).card := by
  have h1 : ∀ x ∈ S, vertexIncidentTriangleCount G x =
      ∑ t ∈ G.cliqueFinset 3, if x ∈ t then 1 else 0 := by
    intro x _
    rw [vertexIncidentTriangleCount, vertexIncidentTriangles, Finset.card_filter]
  have h2 : ∀ t ∈ G.cliqueFinset 3, (t ∩ S).card =
      ∑ x ∈ S, if x ∈ t then 1 else 0 := by
    intro t _
    have heq : t ∩ S = S.filter (fun x ↦ x ∈ t) := by
      ext x
      simp [and_comm]
    rw [heq, Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, ← Finset.sum_congr rfl h2]

theorem filter_neighborFinset_mem_trianglesContaining_eq_erase {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ vertexIncidentTriangles G u) :
    (G.neighborFinset u).filter (fun v ↦ t ∈ G.trianglesContaining s(u, v)) = t.erase u := by
  rw [vertexIncidentTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  obtain ⟨hclique, hu⟩ := ht
  ext v
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, mem_trianglesContaining_iff,
    SimpleGraph.mem_cliqueFinset_iff, Finset.mem_erase]
  constructor
  · rintro ⟨huv, _, hsym⟩
    refine ⟨G.ne_of_adj huv.symm, ?_⟩
    exact Finset.mem_sym2_iff.mp hsym v (Sym2.mem_mk_right u v)
  · rintro ⟨hne, hv⟩
    have huv : G.Adj u v := hclique.isClique hu hv hne.symm
    refine ⟨huv, hclique, Finset.mem_sym2_iff.mpr ?_⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption

theorem card_filter_neighborFinset_mem_trianglesContaining_of_mem {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (ht : t ∈ vertexIncidentTriangles G u) :
    ((G.neighborFinset u).filter (fun v ↦ t ∈ G.trianglesContaining s(u, v))).card = 2 := by
  rw [filter_neighborFinset_mem_trianglesContaining_eq_erase G u ht]
  rw [vertexIncidentTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  have hcard : t.card = 3 := ht.1.card_eq
  have herase := Finset.card_erase_add_one ht.2
  omega

theorem filter_neighborFinset_mem_trianglesContaining_eq_empty_of_notMem {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) {t : Finset α} (hu : u ∉ t) :
    (G.neighborFinset u).filter (fun v ↦ t ∈ G.trianglesContaining s(u, v)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  rw [Finset.mem_filter, mem_trianglesContaining_iff] at hv
  exact hu (Finset.mem_sym2_iff.mp hv.2.2 u (Sym2.mem_mk_left u v))

theorem vertexTriangleClusterSum_eq_twice_vertexIncidentTriangleCount {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    vertexTriangleClusterSum G u = 2 * vertexIncidentTriangleCount G u := by
  unfold vertexTriangleClusterSum
  have h1 : ∀ v ∈ G.neighborFinset u, (G.trianglesContaining s(u, v)).card =
      ∑ t ∈ G.cliqueFinset 3, if t ∈ G.trianglesContaining s(u, v) then 1 else 0 := by
    intro v _
    have hsub : G.trianglesContaining s(u, v) =
        (G.cliqueFinset 3).filter (fun t ↦ t ∈ G.trianglesContaining s(u, v)) := by
      ext t
      rw [Finset.mem_filter]
      exact ⟨fun ht ↦ ⟨((mem_trianglesContaining_iff G s(u, v) t).mp ht).1, ht⟩, fun h ↦ h.2⟩
    exact (congrArg Finset.card hsub).trans (Finset.card_filter _ _)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ t ∈ G.cliqueFinset 3,
      (∑ v ∈ G.neighborFinset u, if t ∈ G.trianglesContaining s(u, v) then 1 else 0) =
        if u ∈ t then 2 else 0 := by
    intro t ht
    rw [← Finset.card_filter]
    split_ifs with hu
    · exact card_filter_neighborFinset_mem_trianglesContaining_of_mem G u
        (Finset.mem_filter.mpr ⟨ht, hu⟩)
    · rw [filter_neighborFinset_mem_trianglesContaining_eq_empty_of_notMem G u hu,
        Finset.card_empty]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rfl

theorem vertexIncidentTriangleCount_eq_card_induce_edgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) :
    vertexIncidentTriangleCount G u = (G.induce (G.neighborSet u)).edgeFinset.card := by
  have h1 := vertexTriangleClusterSum_eq_twice_vertexIncidentTriangleCount G u
  have h2 := vertexTriangleClusterSum_eq_twice_card_induce_edgeFinset G u
  omega

theorem degree_eq_twice_vertexIncidentTriangleCount_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    G.degree u = 2 * vertexIncidentTriangleCount G u := by
  rw [← vertexTriangleClusterSum_eq_degree_of_isAdmissibleBookFree_two hG u,
    vertexTriangleClusterSum_eq_twice_vertexIncidentTriangleCount]

theorem twice_vertexIncidentTriangleCount_le_degree_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    2 * vertexIncidentTriangleCount G u ≤ G.degree u := by
  rw [← vertexTriangleClusterSum_eq_twice_vertexIncidentTriangleCount,
    ← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones]
  unfold vertexTriangleClusterSum
  refine Finset.sum_le_sum (fun v hv ↦ ?_)
  have huv : s(u, v) ∈ G.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_neighborFinset G u v).mp hv)
  exact (edgeDisjointTriangles_iff_forall_trianglesContaining_card_le_one G).mp hed s(u, v) huv

theorem sum_nonNeighborFinset_vertexIncidentTriangleCount_eq_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    (∑ w ∈ nonNeighborFinset G u, vertexIncidentTriangleCount G w) =
      2 * crossTriangleCount G u + 3 * residualTriangleCount G u := by
  rw [sum_card_vertexIncidentTriangles_eq_sum_card_inter,
    sum_cliqueFinset_eq_add_sum_vertexIncident_avoiding G u,
    sum_avoidingTriangles_eq_add_of_edgeDisjointTriangles hed u]
  have h0 : (∑ t ∈ vertexIncidentTriangles G u, (t ∩ nonNeighborFinset G u).card) = 0 :=
    Finset.sum_eq_zero (fun t ht ↦ card_inter_nonNeighborFinset_of_mem_vertexIncidentTriangles G u ht)
  have h1 : (∑ t ∈ crossTriangles G u, (t ∩ nonNeighborFinset G u).card) =
      2 * crossTriangleCount G u := by
    have hpt : ∀ t ∈ crossTriangles G u, (t ∩ nonNeighborFinset G u).card = 2 :=
      fun t ht ↦ card_inter_nonNeighborFinset_of_mem_crossTriangles G u ht
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rfl
  have h3 : (∑ t ∈ residualTriangles G u, (t ∩ nonNeighborFinset G u).card) =
      3 * residualTriangleCount G u := by
    have hpt : ∀ t ∈ residualTriangles G u, (t ∩ nonNeighborFinset G u).card = 3 :=
      fun t ht ↦ card_inter_nonNeighborFinset_of_mem_residualTriangles G u ht
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rfl
  rw [h0, h1, h3, Nat.zero_add]

theorem sum_neighborFinset_vertexIncidentTriangleCount_eq_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    (∑ v ∈ G.neighborFinset u, vertexIncidentTriangleCount G v) =
      2 * vertexIncidentTriangleCount G u + crossTriangleCount G u := by
  rw [sum_card_vertexIncidentTriangles_eq_sum_card_inter,
    sum_cliqueFinset_eq_add_sum_vertexIncident_avoiding G u,
    sum_avoidingTriangles_eq_add_of_edgeDisjointTriangles hed u]
  have h0 : (∑ t ∈ vertexIncidentTriangles G u, (t ∩ G.neighborFinset u).card) =
      2 * vertexIncidentTriangleCount G u := by
    have hpt : ∀ t ∈ vertexIncidentTriangles G u, (t ∩ G.neighborFinset u).card = 2 :=
      fun t ht ↦ card_inter_neighborFinset_of_mem_vertexIncidentTriangles G u ht
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rfl
  have h1 : (∑ t ∈ crossTriangles G u, (t ∩ G.neighborFinset u).card) =
      crossTriangleCount G u := by
    have hpt : ∀ t ∈ crossTriangles G u, (t ∩ G.neighborFinset u).card = 1 :=
      fun t ht ↦ (Finset.mem_filter.mp ht).2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    rfl
  have h3 : (∑ t ∈ residualTriangles G u, (t ∩ G.neighborFinset u).card) = 0 :=
    Finset.sum_eq_zero (fun t ht ↦ (Finset.mem_filter.mp ht).2)
  rw [h0, h1, h3, Nat.add_zero]

theorem four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_le_sum_degree_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    4 * crossTriangleCount G u + 6 * residualTriangleCount G u ≤
      ∑ w ∈ nonNeighborFinset G u, G.degree w := by
  have hsum := sum_nonNeighborFinset_vertexIncidentTriangleCount_eq_of_edgeDisjointTriangles hed u
  have hle : 2 * (∑ w ∈ nonNeighborFinset G u, vertexIncidentTriangleCount G w) ≤
      ∑ w ∈ nonNeighborFinset G u, G.degree w := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun w _ ↦ twice_vertexIncidentTriangleCount_le_degree_of_edgeDisjointTriangles hed w)
  omega

theorem four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_eq_sum_degree
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    4 * crossTriangleCount G u + 6 * residualTriangleCount G u =
      ∑ w ∈ nonNeighborFinset G u, G.degree w := by
  have hed := edgeDisjointTriangles_of_isAdmissibleBookFree_two hG
  have hdeg : ∀ w ∈ nonNeighborFinset G u, G.degree w = 2 * vertexIncidentTriangleCount G w :=
    fun w _ ↦ degree_eq_twice_vertexIncidentTriangleCount_of_isAdmissibleBookFree_two hG w
  rw [Finset.sum_congr rfl hdeg, ← Finset.mul_sum,
    sum_nonNeighborFinset_vertexIncidentTriangleCount_eq_of_edgeDisjointTriangles hed u]
  ring

theorem four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_le_card_mul_degree
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α)
    (hdeg : ∀ w ∈ nonNeighborFinset G u, G.degree w ≤ G.degree u) :
    4 * crossTriangleCount G u + 6 * residualTriangleCount G u ≤
      (nonNeighborFinset G u).card * G.degree u := by
  rw [four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_eq_sum_degree hG u]
  calc
    ∑ w ∈ nonNeighborFinset G u, G.degree w
      ≤ ∑ _w ∈ nonNeighborFinset G u, G.degree u := Finset.sum_le_sum hdeg
    _ = (nonNeighborFinset G u).card * G.degree u := by
      rw [Finset.sum_const, smul_eq_mul]

theorem four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_le_card_mul_degree_of_locallyLinear
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : G.LocallyLinear) (u : α)
    (hdeg : ∀ w ∈ nonNeighborFinset G u, G.degree w ≤ G.degree u) :
    4 * crossTriangleCount G u + 6 * residualTriangleCount G u ≤
      (nonNeighborFinset G u).card * G.degree u :=
  four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_le_card_mul_degree
    ((locallyLinear_iff_trianglesContaining G).mp hG) u hdeg

theorem four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_le_card_mul_maxDegree
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    4 * crossTriangleCount G u + 6 * residualTriangleCount G u ≤
      (nonNeighborFinset G u).card * G.maxDegree := by
  rw [four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_eq_sum_degree hG u]
  calc
    ∑ w ∈ nonNeighborFinset G u, G.degree w
      ≤ ∑ _w ∈ nonNeighborFinset G u, G.maxDegree :=
        Finset.sum_le_sum (fun w _ ↦ G.degree_le_maxDegree w)
    _ = (nonNeighborFinset G u).card * G.maxDegree := by
      rw [Finset.sum_const, smul_eq_mul]

theorem four_mul_card_avoidingTriangles_le_card_nonNeighborFinset_mul_degree
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α)
    (hdeg : ∀ w ∈ nonNeighborFinset G u, G.degree w ≤ G.degree u) :
    4 * (avoidingTriangles G u).card ≤ (nonNeighborFinset G u).card * G.degree u := by
  have hpart := card_avoidingTriangles_eq_add_of_isAdmissibleBookFree_two hG u
  have hbound :=
    four_mul_crossTriangleCount_add_six_mul_residualTriangleCount_le_card_mul_degree hG u hdeg
  omega

theorem sum_neighborFinset_degree_eq_two_mul_degree_add_two_mul_crossTriangleCount
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    (∑ v ∈ G.neighborFinset u, G.degree v) =
      2 * G.degree u + 2 * crossTriangleCount G u := by
  have hed := edgeDisjointTriangles_of_isAdmissibleBookFree_two hG
  have hdeg : ∀ v ∈ G.neighborFinset u, G.degree v = 2 * vertexIncidentTriangleCount G v :=
    fun v _ ↦ degree_eq_twice_vertexIncidentTriangleCount_of_isAdmissibleBookFree_two hG v
  have hu := degree_eq_twice_vertexIncidentTriangleCount_of_isAdmissibleBookFree_two hG u
  rw [Finset.sum_congr rfl hdeg, ← Finset.mul_sum,
    sum_neighborFinset_vertexIncidentTriangleCount_eq_of_edgeDisjointTriangles hed u]
  omega

theorem two_mul_crossTriangleCount_le_card_nonNeighborFinset_mul_degree
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    2 * crossTriangleCount G u ≤ (nonNeighborFinset G u).card * G.degree u := by
  have h1 := degree_sq_add_sum_neighborFinset_degree_le_of_isAdmissibleBookFree
    (by omega : 1 ≤ 2) hG u
  have h2 := sum_neighborFinset_degree_eq_two_mul_degree_add_two_mul_crossTriangleCount hG u
  have h3 := card_nonNeighborFinset G u
  have hlt : G.degree u < Fintype.card α := G.degree_lt_card_verts u
  have hcard_eq : Fintype.card α + 2 - 1 =
      (nonNeighborFinset G u).card + G.degree u + 2 := by omega
  rw [h2, hcard_eq, Nat.add_mul, Nat.add_mul] at h1
  omega

/-- Cross-triangles `(N(u), R(u), R(u))` containing a specific vertex `w`. -/
noncomputable def vertexCrossTriangles {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u w : α) : Finset (Finset α) :=
  (crossTriangles G u).filter (fun t ↦ w ∈ t)

theorem sum_nonNeighborFinset_card_vertexCrossTriangles_eq_twice_crossTriangleCount
    {α : Type*} [Fintype α] (G : SimpleGraph α) (u : α) :
    (∑ w ∈ nonNeighborFinset G u, (vertexCrossTriangles G u w).card) =
      2 * crossTriangleCount G u := by
  have h1 : ∀ w ∈ nonNeighborFinset G u, (vertexCrossTriangles G u w).card =
      ∑ t ∈ crossTriangles G u, if w ∈ t then 1 else 0 := by
    intro w _
    rw [vertexCrossTriangles, Finset.card_filter]
  have h2 : ∀ t ∈ crossTriangles G u,
      (∑ w ∈ nonNeighborFinset G u, if w ∈ t then 1 else 0) = 2 := by
    intro t ht
    have heq : (nonNeighborFinset G u).filter (fun w ↦ w ∈ t) = t ∩ nonNeighborFinset G u := by
      ext w
      simp [and_comm]
    rw [← Finset.card_filter, heq, card_inter_nonNeighborFinset_of_mem_crossTriangles G u ht]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rfl

theorem inter_neighborFinset_subset_commonNeighborFinset_of_mem_vertexCrossTriangles
    {α : Type*} [Fintype α] (G : SimpleGraph α) {u w : α} (hw : w ∈ nonNeighborFinset G u)
    {t : Finset α} (ht : t ∈ vertexCrossTriangles G u w) :
    t ∩ G.neighborFinset u ⊆ commonNeighborFinset G u w := by
  rw [vertexCrossTriangles, Finset.mem_filter, crossTriangles, Finset.mem_filter,
    avoidingTriangles, Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  intro v hv
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hv
  rw [mem_commonNeighborFinset_iff]
  have hne : w ≠ v := by
    rintro rfl
    exact notMem_nonNeighborFinset_of_adj G hv.2 hw
  exact ⟨hv.2, ht.1.1.1.isClique ht.2 hv.1 hne⟩

theorem card_vertexCrossTriangles_le_card_commonNeighborFinset_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles)
    {u w : α} (hw : w ∈ nonNeighborFinset G u) :
    (vertexCrossTriangles G u w).card ≤ (commonNeighborFinset G u w).card := by
  have hdisj : (vertexCrossTriangles G u w : Set (Finset α)).PairwiseDisjoint
      (fun t ↦ t ∩ G.neighborFinset u) := by
    intro t₁ ht₁ t₂ ht₂ hne
    change Disjoint (t₁ ∩ G.neighborFinset u) (t₂ ∩ G.neighborFinset u)
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hv₁ hv₂
    rw [Finset.mem_coe, vertexCrossTriangles, Finset.mem_filter, crossTriangles,
      Finset.mem_filter, avoidingTriangles, Finset.mem_filter,
      SimpleGraph.mem_cliqueFinset_iff] at ht₁ ht₂
    have hvw : v ≠ w := by
      rintro rfl
      exact notMem_nonNeighborFinset_of_adj G hv₁.2 hw
    have hadj : G.Adj v w := ht₁.1.1.1.isClique hv₁.1 ht₁.2 hvw
    have hm₁ : t₁ ∈ G.trianglesContaining s(v, w) := by
      rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
      refine ⟨ht₁.1.1.1, Finset.mem_sym2_iff.mpr ?_⟩
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> [exact hv₁.1; exact ht₁.2]
    have hm₂ : t₂ ∈ G.trianglesContaining s(v, w) := by
      rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
      refine ⟨ht₂.1.1.1, Finset.mem_sym2_iff.mpr ?_⟩
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> [exact hv₂.1; exact ht₂.2]
    have hle1 : (G.trianglesContaining s(v, w)).card ≤ 1 :=
      (edgeDisjointTriangles_iff_forall_trianglesContaining_card_le_one G).mp hed
        s(v, w) (SimpleGraph.mem_edgeFinset.mpr hadj)
    exact hne (Finset.card_le_one.mp hle1 t₁ hm₁ t₂ hm₂)
  have hcard1 : ∀ t ∈ vertexCrossTriangles G u w, (t ∩ G.neighborFinset u).card = 1 :=
    fun t ht ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
  calc
    (vertexCrossTriangles G u w).card
      = ∑ _t ∈ vertexCrossTriangles G u w, 1 := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    _ = ∑ t ∈ vertexCrossTriangles G u w, (t ∩ G.neighborFinset u).card :=
        (Finset.sum_congr rfl hcard1).symm
    _ = ((vertexCrossTriangles G u w).biUnion (fun t ↦ t ∩ G.neighborFinset u)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (commonNeighborFinset G u w).card := by
        refine Finset.card_le_card ?_
        intro v hv
        rw [Finset.mem_biUnion] at hv
        obtain ⟨t, ht, hv_t⟩ := hv
        exact inter_neighborFinset_subset_commonNeighborFinset_of_mem_vertexCrossTriangles
          G hw ht hv_t

theorem pairwiseDisjoint_offDiag_inter_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (S : Finset α) :
    (G.cliqueFinset 3 : Set (Finset α)).PairwiseDisjoint (fun t ↦ (t ∩ S).offDiag) := by
  intro t₁ ht₁ t₂ ht₂ hne
  change Disjoint ((t₁ ∩ S).offDiag) ((t₂ ∩ S).offDiag)
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  rw [Finset.mem_offDiag, Finset.mem_inter, Finset.mem_inter] at hp₁ hp₂
  rw [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht₁ ht₂
  have hadj : G.Adj p.1 p.2 := ht₁.isClique hp₁.1.1 hp₁.2.1.1 hp₁.2.2
  have hm₁ : t₁ ∈ G.trianglesContaining s(p.1, p.2) := by
    rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨ht₁, Finset.mem_sym2_iff.mpr ?_⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> [exact hp₁.1.1; exact hp₁.2.1.1]
  have hm₂ : t₂ ∈ G.trianglesContaining s(p.1, p.2) := by
    rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨ht₂, Finset.mem_sym2_iff.mpr ?_⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> [exact hp₂.1.1; exact hp₂.2.1.1]
  have hle1 : (G.trianglesContaining s(p.1, p.2)).card ≤ 1 :=
    (edgeDisjointTriangles_iff_forall_trianglesContaining_card_le_one G).mp hed
      s(p.1, p.2) (SimpleGraph.mem_edgeFinset.mpr hadj)
  exact hne (Finset.card_le_one.mp hle1 t₁ hm₁ t₂ hm₂)

theorem sum_card_offDiag_inter_le_offDiag_card_of_edgeDisjointTriangles
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (S : Finset α) :
    (∑ t ∈ G.cliqueFinset 3, (t ∩ S).offDiag.card) ≤ S.offDiag.card := by
  rw [← Finset.card_biUnion (pairwiseDisjoint_offDiag_inter_of_edgeDisjointTriangles hed S)]
  refine Finset.card_le_card ?_
  intro p hp
  rw [Finset.mem_biUnion] at hp
  obtain ⟨t, _, hp_t⟩ := hp
  exact Finset.offDiag_mono Finset.inter_subset_right hp_t

theorem two_mul_crossTriangleCount_add_six_mul_residualTriangleCount_le_offDiag_card
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    2 * crossTriangleCount G u + 6 * residualTriangleCount G u ≤
      (nonNeighborFinset G u).offDiag.card := by
  have hle :=
    sum_card_offDiag_inter_le_offDiag_card_of_edgeDisjointTriangles hed (nonNeighborFinset G u)
  rw [sum_cliqueFinset_eq_add_sum_vertexIncident_avoiding G u,
    sum_avoidingTriangles_eq_add_of_edgeDisjointTriangles hed u] at hle
  have h1 : (∑ t ∈ crossTriangles G u, (t ∩ nonNeighborFinset G u).offDiag.card) =
      2 * crossTriangleCount G u := by
    have hpt : ∀ t ∈ crossTriangles G u, (t ∩ nonNeighborFinset G u).offDiag.card = 2 := by
      intro t ht
      rw [Finset.offDiag_card, card_inter_nonNeighborFinset_of_mem_crossTriangles G u ht]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rfl
  have h3 : (∑ t ∈ residualTriangles G u, (t ∩ nonNeighborFinset G u).offDiag.card) =
      6 * residualTriangleCount G u := by
    have hpt : ∀ t ∈ residualTriangles G u, (t ∩ nonNeighborFinset G u).offDiag.card = 6 := by
      intro t ht
      rw [Finset.offDiag_card, card_inter_nonNeighborFinset_of_mem_residualTriangles G u ht]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rfl
  omega

theorem crossTriangleCount_add_three_mul_residualTriangleCount_le_choose_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hed : G.EdgeDisjointTriangles) (u : α) :
    crossTriangleCount G u + 3 * residualTriangleCount G u ≤
      (nonNeighborFinset G u).card.choose 2 := by
  have hle := two_mul_crossTriangleCount_add_six_mul_residualTriangleCount_le_offDiag_card hed u
  rw [Finset.offDiag_card] at hle
  rw [Nat.choose_two_right]
  have hsub : (nonNeighborFinset G u).card * (nonNeighborFinset G u).card -
      (nonNeighborFinset G u).card =
      (nonNeighborFinset G u).card * ((nonNeighborFinset G u).card - 1) := by
    rw [Nat.mul_sub_one]
  omega

/-! ## `r`-Book Edge-Deletion Subgraphs and Step-Difference Reductions -/

/-- A finite simple graph `G` is `r`-book-free if every edge lies in fewer than `r` triangles. -/
def IsBookFree {α : Type*} [Fintype α] (G : SimpleGraph α) (r : ℕ) : Prop :=
  ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r

/-- The finset of `r`-book ("heavy") edges of `G`, i.e., edges contained in at least `r` triangles. -/
noncomputable def bookHeavyEdgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) : Finset (Sym2 α) :=
  G.edgeFinset.filter (fun uv ↦ r ≤ (G.trianglesContaining uv).card)

/-- The canonical `r`-book edge-deletion subgraph obtained by deleting all edges of triangle
multiplicity `≥ r`. -/
noncomputable def bookEdgeDeletionSubgraph {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) : SimpleGraph α :=
  G.deleteEdges (bookHeavyEdgeFinset G r : Set (Sym2 α))

theorem isAdmissibleBookFree_iff_isBookFree {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) :
    IsAdmissibleBookFree G r ↔
      (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) ∧ IsBookFree G r :=
  Iff.rfl

theorem isBookFree_mono_right {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) (h : IsBookFree G r₁) :
    IsBookFree G r₂ :=
  fun uv huv ↦ Nat.lt_of_lt_of_le (h uv huv) hr

theorem isBookFree_bot (α : Type*) [Fintype α] (r : ℕ) :
    IsBookFree (⊥ : SimpleGraph α) r := by
  intro uv huv
  simp at huv

theorem mem_trianglesContaining_iff_isNClique {α : Type*} [Fintype α]
    (G : SimpleGraph α) (uv : Sym2 α) (t : Finset α) :
    t ∈ G.trianglesContaining uv ↔ G.IsNClique 3 t ∧ uv ∈ t.sym2 := by
  rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]

theorem trianglesContaining_mono {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) (uv : Sym2 α) :
    H.trianglesContaining uv ⊆ G.trianglesContaining uv := by
  intro t ht
  rw [mem_trianglesContaining_iff_isNClique] at ht ⊢
  exact ⟨ht.1.mono hle, ht.2⟩

theorem card_trianglesContaining_mono {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) (uv : Sym2 α) :
    (H.trianglesContaining uv).card ≤ (G.trianglesContaining uv).card :=
  Finset.card_le_card (trianglesContaining_mono hle uv)

theorem isBookFree_anti_graph {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) {r : ℕ} (hG : IsBookFree G r) :
    IsBookFree H r := by
  intro uv huv
  exact Nat.lt_of_le_of_lt (card_trianglesContaining_mono hle uv)
    (hG uv (SimpleGraph.edgeFinset_mono hle huv))

theorem isBookFree_deleteEdges_of_isBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (s : Set (Sym2 α)) (hG : IsBookFree G r) :
    IsBookFree (G.deleteEdges s) r :=
  isBookFree_anti_graph (SimpleGraph.deleteEdges_le s) hG

theorem edgeFinset_deleteEdges_finset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (F : Finset (Sym2 α))
    {inst : Fintype (G.deleteEdges (F : Set (Sym2 α))).edgeSet} :
    @SimpleGraph.edgeFinset _ (G.deleteEdges (F : Set (Sym2 α))) inst = G.edgeFinset \ F := by
  ext uv
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
    Finset.mem_sdiff, Set.mem_diff, Finset.mem_coe]

theorem card_edgeFinset_deleteEdges_of_subset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {F : Finset (Sym2 α)} (hF : F ⊆ G.edgeFinset)
    {inst : Fintype (G.deleteEdges (F : Set (Sym2 α))).edgeSet} :
    (@SimpleGraph.edgeFinset _ (G.deleteEdges (F : Set (Sym2 α))) inst).card =
      G.edgeFinset.card - F.card := by
  rw [edgeFinset_deleteEdges_finset, Finset.card_sdiff_of_subset hF]

theorem card_edgeFinset_deleteEdges_add_card_of_subset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {F : Finset (Sym2 α)} (hF : F ⊆ G.edgeFinset)
    {inst : Fintype (G.deleteEdges (F : Set (Sym2 α))).edgeSet} :
    (@SimpleGraph.edgeFinset _ (G.deleteEdges (F : Set (Sym2 α))) inst).card + F.card =
      G.edgeFinset.card := by
  rw [edgeFinset_deleteEdges_finset, Finset.card_sdiff_add_card_eq_card hF]

theorem edgeFinset_deleteEdges_singleton {α : Type*} [Fintype α]
    (G : SimpleGraph α) (e : Sym2 α)
    {inst : Fintype (G.deleteEdges ({e} : Set (Sym2 α))).edgeSet} :
    @SimpleGraph.edgeFinset _ (G.deleteEdges ({e} : Set (Sym2 α))) inst =
      G.edgeFinset.erase e := by
  ext uv
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
    Finset.mem_erase, Set.mem_diff, Set.mem_singleton_iff, and_comm]

theorem card_edgeFinset_deleteEdges_singleton {α : Type*} [Fintype α]
    (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ G.edgeFinset)
    {inst : Fintype (G.deleteEdges ({e} : Set (Sym2 α))).edgeSet} :
    (@SimpleGraph.edgeFinset _ (G.deleteEdges ({e} : Set (Sym2 α))) inst).card =
      G.edgeFinset.card - 1 := by
  rw [edgeFinset_deleteEdges_singleton, Finset.card_erase_of_mem he]

theorem card_edgeFinset_deleteEdges_singleton_add_one {α : Type*} [Fintype α]
    (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ G.edgeFinset)
    {inst : Fintype (G.deleteEdges ({e} : Set (Sym2 α))).edgeSet} :
    (@SimpleGraph.edgeFinset _ (G.deleteEdges ({e} : Set (Sym2 α))) inst).card + 1 =
      G.edgeFinset.card := by
  rw [edgeFinset_deleteEdges_singleton, Finset.card_erase_add_one he]

theorem isNClique_three_deleteEdges_iff_of_subset_edgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {F : Finset (Sym2 α)} (hF : F ⊆ G.edgeFinset) (t : Finset α) :
    (G.deleteEdges (F : Set (Sym2 α))).IsNClique 3 t ↔
      G.IsNClique 3 t ∧ t ∉ F.biUnion G.trianglesContaining := by
  rw [Finset.mem_biUnion]
  constructor
  · intro ht
    have hG : G.IsNClique 3 t := ht.mono (SimpleGraph.deleteEdges_le _)
    refine ⟨hG, ?_⟩
    rintro ⟨e, heF, he_tri⟩
    rw [mem_trianglesContaining_iff_isNClique] at he_tri
    have hdiag : ¬ e.IsDiag :=
      G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hF heF))
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := Sym2.mk_isDiag_iff.not.mp hdiag
      have hx : x ∈ t := Finset.mem_sym2_iff.mp he_tri.2 x (Sym2.mem_mk_left x y)
      have hy : y ∈ t := Finset.mem_sym2_iff.mp he_tri.2 y (Sym2.mem_mk_right x y)
      have hadj : (G.deleteEdges (F : Set (Sym2 α))).Adj x y := ht.isClique hx hy hxy
      rw [SimpleGraph.deleteEdges_adj, Finset.mem_coe] at hadj
      exact hadj.2 heF
  · rintro ⟨hG, hnot⟩
    rw [SimpleGraph.isNClique_iff] at hG ⊢
    refine ⟨?_, hG.2⟩
    intro x hx y hy hxy
    rw [SimpleGraph.deleteEdges_adj, Finset.mem_coe]
    refine ⟨hG.1 hx hy hxy, ?_⟩
    intro hmemF
    apply hnot
    refine ⟨s(x, y), hmemF, ?_⟩
    rw [mem_trianglesContaining_iff_isNClique, SimpleGraph.isNClique_iff]
    refine ⟨hG, Finset.mem_sym2_iff.mpr ?_⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> [exact hx; exact hy]

theorem cliqueFinset_three_deleteEdges_of_subset_edgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {F : Finset (Sym2 α)} (hF : F ⊆ G.edgeFinset)
    {inst : DecidableRel (G.deleteEdges (F : Set (Sym2 α))).Adj} :
    @SimpleGraph.cliqueFinset _ (G.deleteEdges (F : Set (Sym2 α))) _ _ inst 3 =
      G.cliqueFinset 3 \ F.biUnion G.trianglesContaining := by
  ext t
  rw [Finset.mem_sdiff, SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.mem_cliqueFinset_iff,
    isNClique_three_deleteEdges_iff_of_subset_edgeFinset G hF t]

theorem trianglesContaining_deleteEdges_of_subset_edgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {F : Finset (Sym2 α)} (hF : F ⊆ G.edgeFinset) (uv : Sym2 α) :
    (G.deleteEdges (F : Set (Sym2 α))).trianglesContaining uv =
      G.trianglesContaining uv \ F.biUnion G.trianglesContaining := by
  ext t
  rw [Finset.mem_sdiff, mem_trianglesContaining_iff_isNClique,
    mem_trianglesContaining_iff_isNClique,
    isNClique_three_deleteEdges_iff_of_subset_edgeFinset G hF t]
  tauto

theorem isNClique_three_deleteEdges_singleton_iff_of_mem_edgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ G.edgeFinset) (t : Finset α) :
    (G.deleteEdges ({e} : Set (Sym2 α))).IsNClique 3 t ↔
      G.IsNClique 3 t ∧ t ∉ G.trianglesContaining e := by
  have hsub : ({e} : Finset (Sym2 α)) ⊆ G.edgeFinset := Finset.singleton_subset_iff.mpr he
  have h := isNClique_three_deleteEdges_iff_of_subset_edgeFinset G hsub t
  simpa using h

theorem cliqueFinset_three_deleteEdges_singleton_of_mem_edgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ G.edgeFinset)
    {inst : DecidableRel (G.deleteEdges ({e} : Set (Sym2 α))).Adj} :
    @SimpleGraph.cliqueFinset _ (G.deleteEdges ({e} : Set (Sym2 α))) _ _ inst 3 =
      G.cliqueFinset 3 \ G.trianglesContaining e := by
  ext t
  rw [Finset.mem_sdiff, SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.mem_cliqueFinset_iff,
    isNClique_three_deleteEdges_singleton_iff_of_mem_edgeFinset G he t]

theorem card_cliqueFinset_three_deleteEdges_singleton_add_card {α : Type*} [Fintype α]
    (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ G.edgeFinset)
    {inst : DecidableRel (G.deleteEdges ({e} : Set (Sym2 α))).Adj} :
    (@SimpleGraph.cliqueFinset _ (G.deleteEdges ({e} : Set (Sym2 α))) _ _ inst 3).card +
      (G.trianglesContaining e).card = (G.cliqueFinset 3).card := by
  have hsub : G.trianglesContaining e ⊆ G.cliqueFinset 3 :=
    fun t ht ↦ ((mem_trianglesContaining_iff G e t).mp ht).1
  rw [cliqueFinset_three_deleteEdges_singleton_of_mem_edgeFinset G he,
    Finset.card_sdiff_add_card_eq_card hsub]

theorem edgeTriangleIncidenceSum_deleteEdges_singleton_add_three_mul_card {α : Type*} [Fintype α]
    (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ G.edgeFinset) :
    edgeTriangleIncidenceSum (G.deleteEdges ({e} : Set (Sym2 α))) +
      3 * (G.trianglesContaining e).card = edgeTriangleIncidenceSum G := by
  rw [edgeTriangleIncidenceSum_eq_three_mul_card_cliqueFinset,
    edgeTriangleIncidenceSum_eq_three_mul_card_cliqueFinset G, ← Nat.mul_add,
    card_cliqueFinset_three_deleteEdges_singleton_add_card G he]

theorem isBookFree_deleteEdges_of_bookHeavyEdgeFinset_subset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) {F : Finset (Sym2 α)}
    (hF : bookHeavyEdgeFinset G r ⊆ F) :
    IsBookFree (G.deleteEdges (F : Set (Sym2 α))) r := by
  intro uv huv
  rw [edgeFinset_deleteEdges_finset, Finset.mem_sdiff] at huv
  have hnot_heavy : uv ∉ bookHeavyEdgeFinset G r := fun hm ↦ huv.2 (hF hm)
  have hlt : (G.trianglesContaining uv).card < r := by
    by_contra hge
    exact hnot_heavy (Finset.mem_filter.mpr ⟨huv.1, Nat.le_of_not_lt hge⟩)
  exact Nat.lt_of_le_of_lt (card_trianglesContaining_mono (SimpleGraph.deleteEdges_le _) uv) hlt

theorem isBookFree_bookEdgeDeletionSubgraph {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) :
    IsBookFree (bookEdgeDeletionSubgraph G r) r :=
  isBookFree_deleteEdges_of_bookHeavyEdgeFinset_subset G r Finset.Subset.rfl

theorem card_edgeFinset_bookEdgeDeletionSubgraph_add_card {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ)
    {inst : Fintype (bookEdgeDeletionSubgraph G r).edgeSet} :
    (@SimpleGraph.edgeFinset _ (bookEdgeDeletionSubgraph G r) inst).card +
      (bookHeavyEdgeFinset G r).card = G.edgeFinset.card :=
  card_edgeFinset_deleteEdges_add_card_of_subset G (Finset.filter_subset _ _)

theorem bookHeavyEdgeFinset_deleteEdges_singleton_subset_erase {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) (e : Sym2 α) :
    bookHeavyEdgeFinset (G.deleteEdges ({e} : Set (Sym2 α))) r ⊆
      (bookHeavyEdgeFinset G r).erase e := by
  intro uv huv
  rw [bookHeavyEdgeFinset, Finset.mem_filter, edgeFinset_deleteEdges_singleton,
    Finset.mem_erase] at huv
  rw [Finset.mem_erase, bookHeavyEdgeFinset, Finset.mem_filter]
  refine ⟨huv.1.1, huv.1.2, le_trans huv.2 ?_⟩
  exact card_trianglesContaining_mono (SimpleGraph.deleteEdges_le _) uv

theorem card_bookHeavyEdgeFinset_deleteEdges_singleton_add_one_le {α : Type*} [Fintype α]
    (G : SimpleGraph α) {r : ℕ} {e : Sym2 α} (he : e ∈ bookHeavyEdgeFinset G r) :
    (bookHeavyEdgeFinset (G.deleteEdges ({e} : Set (Sym2 α))) r).card + 1 ≤
      (bookHeavyEdgeFinset G r).card := by
  have hsub := Finset.card_le_card (bookHeavyEdgeFinset_deleteEdges_singleton_subset_erase G r e)
  have herase := Finset.card_erase_add_one he
  omega

theorem mul_card_bookHeavyEdgeFinset_le_edgeTriangleIncidenceSum {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) :
    r * (bookHeavyEdgeFinset G r).card ≤ edgeTriangleIncidenceSum G := by
  calc
    r * (bookHeavyEdgeFinset G r).card
      = ∑ _uv ∈ bookHeavyEdgeFinset G r, r := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ uv ∈ bookHeavyEdgeFinset G r, (G.trianglesContaining uv).card :=
        Finset.sum_le_sum (fun uv huv ↦ (Finset.mem_filter.mp huv).2)
    _ ≤ ∑ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = edgeTriangleIncidenceSum G := rfl

theorem mul_card_bookHeavyEdgeFinset_le_three_mul_card_cliqueFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) :
    r * (bookHeavyEdgeFinset G r).card ≤ 3 * (G.cliqueFinset 3).card := by
  rw [← edgeTriangleIncidenceSum_eq_three_mul_card_cliqueFinset]
  exact mul_card_bookHeavyEdgeFinset_le_edgeTriangleIncidenceSum G r

theorem card_edgeFinset_add_sub_one_mul_card_bookHeavyEdgeFinset_le_edgeTriangleIncidenceSum
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) :
    G.edgeFinset.card + (r - 1) * (bookHeavyEdgeFinset G r).card ≤
      edgeTriangleIncidenceSum G := by
  have h1 : G.edgeFinset.card = ∑ _uv ∈ G.edgeFinset, 1 := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
  have h2 : (r - 1) * (bookHeavyEdgeFinset G r).card =
      ∑ uv ∈ G.edgeFinset, if r ≤ (G.trianglesContaining uv).card then r - 1 else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    rfl
  rw [h1, h2, ← Finset.sum_add_distrib]
  unfold edgeTriangleIncidenceSum
  refine Finset.sum_le_sum (fun uv huv ↦ ?_)
  have hpos : 1 ≤ (G.trianglesContaining uv).card := Finset.card_pos.mpr (htri uv huv)
  split_ifs with hge <;> omega

theorem bookHeavyEdgeFinset_subset_of_isBookFree_deleteEdges {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) {F : Finset (Sym2 α)}
    (hdel : ∀ uv ∈ (G.deleteEdges (F : Set (Sym2 α))).edgeFinset,
      (G.trianglesContaining uv).card < r) :
    bookHeavyEdgeFinset G r ⊆ F := by
  intro uv huv
  rw [bookHeavyEdgeFinset, Finset.mem_filter] at huv
  by_contra hnot
  have hmem : uv ∈ (G.deleteEdges (F : Set (Sym2 α))).edgeFinset := by
    rw [edgeFinset_deleteEdges_finset, Finset.mem_sdiff]
    exact ⟨huv.1, hnot⟩
  have hlt := hdel uv hmem
  omega

theorem stepDiff_le_of_forall_isAdmissibleBookFree_succ_exists_deleteEdges
    (n r d : ℕ)
    (h : ∀ G : SimpleGraph (Fin n), IsAdmissibleBookFree G (r + 1) →
      ∃ F : Finset (Sym2 (Fin n)), F ⊆ G.edgeFinset ∧ F.card ≤ d ∧
        IsAdmissibleBookFree (G.deleteEdges (F : Set (Sym2 (Fin n)))) r) :
    stepDiff n r ≤ d := by
  refine stepDiff_le_of_forall_isAdmissibleBookFree_succ_exists_sub n r d (fun G hG ↦ ?_)
  obtain ⟨F, hF_sub, hF_card, hdel⟩ := h G hG
  refine ⟨G.deleteEdges (F : Set (Sym2 (Fin n))), hdel, ?_⟩
  rw [card_edgeFinset_deleteEdges_of_subset G hF_sub]
  have hle : F.card ≤ G.edgeFinset.card := Finset.card_le_card hF_sub
  omega

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
  intro r hr
  refine tendsto_div_nhds_one_of_book_deletion_isLittleO (d r) (fun n G hG ↦ ?_) (ho r hr)
  obtain ⟨F, hF_sub, hF_card, hadm⟩ := hdel r hr n G hG
  refine ⟨G.deleteEdges (F : Set (Sym2 (Fin n))), hadm, ?_⟩
  rw [card_edgeFinset_deleteEdges_of_subset G hF_sub]
  have hle : F.card ≤ G.edgeFinset.card := Finset.card_le_card hF_sub
  omega

end NonNeighborTrianglePartitionAndBookEdgeDeletion
end Erdos600
