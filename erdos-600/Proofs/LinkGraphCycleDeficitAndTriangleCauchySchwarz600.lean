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

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Topology

namespace Erdos600

open SimpleGraph Finset Filter

/-!
# Second-Order Link-Graph Degree/Deficit Decomposition, Global Triangle-Incidence Cauchy–Schwarz Bounds, Step Differences, and Conditional Reductions for Erdős #600

This module develops 60 universally quantified (`∀`) theorems advancing Erdős Problem #600
with zero overlap with `Erdos600Unified435.lean` and `NeighborhoodDegreeAndTriangleClusterBounds600.lean`:

1. **Second-Order Link-Graph `maxDegree` / `minDegree` Bounds and Cycle/Path Deficit Decomposition for $r = 3, 4$:**
   - Proves general `maxDegree` and `minDegree` transfer bounds and shows that for any `IsAdmissibleBookFree G r`
     graph (`1 ≤ r`), every induced neighborhood (link) graph `G.induce (G.neighborSet u)` satisfies
     `(G.induce (G.neighborSet u)).maxDegree ≤ r - 1` (`induce_neighborSet_maxDegree_le_sub_one_of_isAdmissibleBookFree`),
     `1 ≤ (G.induce (G.neighborSet u)).minDegree` when `Nonempty (G.neighborSet u)`, and
     `(G.induce (G.neighborSet u)).edgeFinset.card ≤ ((r - 1) * G.degree u) / 2`.
   - Specializing to `r = 3` (`IsAdmissibleBookFree G 3`), proves `(G.induce (G.neighborSet u)).maxDegree ≤ 2`,
     every link vertex has degree `1` or `2` (`induce_neighborSet_degree_eq_one_or_two_of_isAdmissibleBookFree_three`),
     and the link degree-1 (path-endpoint) finset `linkDegreeOneFinset G u` satisfies
     `2 * (G.induce (G.neighborSet u)).edgeFinset.card + (linkDegreeOneFinset G u).card = 2 * G.degree u`,
     hence `Even (linkDegreeOneFinset G u).card` (`even_card_linkDegreeOneFinset_of_isAdmissibleBookFree_three`).
   - Specializing to `r = 4` (`IsAdmissibleBookFree G 4`) and general even `r ≥ 2`, proves
     `(G.induce (G.neighborSet u)).maxDegree ≤ 3`, `Even (vertexLinkDeficit G r u) ↔ Even (G.degree u)`,
     and for every odd-degree vertex `Odd (G.degree u)`, `1 ≤ vertexLinkDeficit G r u` and
     `vertexTriangleClusterSum G u ≤ (r - 1) * G.degree u - 1`.

2. **Global Triangle-Incidence Identities, Cauchy–Schwarz Second-Moment Bounds, and Mantel–Turán Edge Bounds:**
   - Defines `edgeTriangleIncidenceSum G` and `edgeTriangleIncidenceSqSum G`.
   - Proves the exact double-counting identities `edgeTriangleIncidenceSum G = 3 * (G.cliqueFinset 3).card`,
     `∑ u : α, vertexTriangleClusterSum G u = 6 * (G.cliqueFinset 3).card`, and
     `∑ u : α, (G.induce (G.neighborSet u)).edgeFinset.card = 3 * (G.cliqueFinset 3).card`.
   - Proves the global and local Cauchy–Schwarz triangle-incidence inequalities
     `(edgeTriangleIncidenceSum G) ^ 2 ≤ G.edgeFinset.card * edgeTriangleIncidenceSqSum G` and
     `9 * (G.cliqueFinset 3).card ^ 2 ≤ G.edgeFinset.card * edgeTriangleIncidenceSqSum G`.
   - Proves the global neighbor-degree double-sum identity
     `∑ u : α, ∑ v ∈ G.neighborFinset u, G.degree v = ∑ u : α, G.degree u ^ 2`, deducing
     `∑ u : α, G.degree u ^ 2 ≤ (Fintype.card α + r - 1) * G.edgeFinset.card` and the universal
     Mantel–Turán book-free edge bound `4 * G.edgeFinset.card ≤ Fintype.card α * (Fintype.card α + r - 1)`
     (`maxAdmissibleEdges n r ≤ (n * (n + r - 1)) / 4`, tight at `(n, r) ∈ {(4, 3), (6, 3), (5, 4), (9, 4)}`).

3. **Step Differences `stepDiff n r = eFunction n (r + 1) - eFunction n r` & Zero-`sorry` Conditional Reductions:**
   - Formalizes `stepDiff n r`, proves exact $r$-book witness existence in any $(r+1)$-admissible graph
     exceeding `maxAdmissibleEdges n r`, establishes Mantel–Turán and parity step-difference lower bounds,
     proves the $(r+1)$-to-$r$ edge-deletion upper bound `stepDiff_le_of_forall_isAdmissibleBookFree_succ_exists_sub`,
     and proves zero-`sorry` conditional reductions to `erdos_600.parts.i` and `erdos_600.parts.ii`.
-/

section LinkGraphCycleDeficitAndTriangleCauchySchwarz
open scoped Classical

/-- The link-degree deficit at vertex `u` relative to the `(r - 1)`-regular link-graph ceiling. -/
noncomputable def vertexLinkDeficit {α : Type*} [Fintype α]
    (G : SimpleGraph α) (r : ℕ) (u : α) : ℕ :=
  ∑ v ∈ G.neighborFinset u, (r - 1 - (G.trianglesContaining s(u, v)).card)

/-- The subset of neighbors `v ∈ G.neighborFinset u` whose edge `s(u, v)` lies in exactly `1` triangle
(equivalently, vertices of degree `1` in the induced link graph `G.induce (G.neighborSet u)`). -/
noncomputable def linkDegreeOneFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) : Finset α :=
  (G.neighborFinset u).filter (fun v ↦ (G.trianglesContaining s(u, v)).card = 1)

/-- The sum of triangle multiplicities `(G.trianglesContaining uv).card` over all edges `uv ∈ G.edgeFinset`. -/
noncomputable def edgeTriangleIncidenceSum {α : Type*} [Fintype α]
    (G : SimpleGraph α) : ℕ :=
  ∑ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card

/-- The sum of squared triangle multiplicities `(G.trianglesContaining uv).card ^ 2` over all edges `uv ∈ G.edgeFinset`. -/
noncomputable def edgeTriangleIncidenceSqSum {α : Type*} [Fintype α]
    (G : SimpleGraph α) : ℕ :=
  ∑ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card ^ 2

/-- The step difference `eFunction n (r + 1) - eFunction n r` appearing in `erdos_600.parts.i` and `erdos_600.parts.ii`. -/
noncomputable def stepDiff (n r : ℕ) : ℕ :=
  eFunction n (r + 1) - eFunction n r

theorem maxDegree_le_of_forall_degree_le {V : Type*} [Fintype V]
    (H : SimpleGraph V) (k : ℕ) (h : ∀ v : V, H.degree v ≤ k) :
    H.maxDegree ≤ k := by
  by_cases hne : Nonempty V
  · obtain ⟨v, hv⟩ := H.exists_maximal_degree_vertex
    rw [hv]
    exact h v
  · haveI : IsEmpty V := not_nonempty_iff.mp hne
    rw [H.maxDegree_of_isEmpty]
    exact Nat.zero_le k

theorem le_minDegree_of_forall_le_degree {V : Type*} [Fintype V] [Nonempty V]
    (H : SimpleGraph V) (k : ℕ) (h : ∀ v : V, k ≤ H.degree v) :
    k ≤ H.minDegree := by
  obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
  rw [hv]
  exact h v

theorem induce_neighborSet_degree_eq_card_trianglesContaining {α : Type*} [Fintype α]
    (G : SimpleGraph α) (u : α) (v : G.neighborSet u) :
    (G.induce (G.neighborSet u)).degree v = (G.trianglesContaining s(u, v.1)).card := by
  rw [induce_neighborSet_degree_eq_card_commonNeighborFinset,
    card_trianglesContaining_eq_card_commonNeighborFinset G v.2]

theorem one_le_induce_neighborSet_degree_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r)
    (u : α) (v : G.neighborSet u) :
    1 ≤ (G.induce (G.neighborSet u)).degree v := by
  rw [induce_neighborSet_degree_eq_card_trianglesContaining]
  exact Finset.card_pos.mpr (hG.1 s(u, v.1) (SimpleGraph.mem_edgeFinset.mpr v.2))

theorem induce_neighborSet_degree_lt_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r)
    (u : α) (v : G.neighborSet u) :
    (G.induce (G.neighborSet u)).degree v < r := by
  rw [induce_neighborSet_degree_eq_card_trianglesContaining]
  exact hG.2 s(u, v.1) (SimpleGraph.mem_edgeFinset.mpr v.2)

theorem induce_neighborSet_degree_le_sub_one_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r) (hG : IsAdmissibleBookFree G r)
    (u : α) (v : G.neighborSet u) :
    (G.induce (G.neighborSet u)).degree v ≤ r - 1 := by
  have hlt := induce_neighborSet_degree_lt_of_isAdmissibleBookFree hG u v
  omega

theorem induce_neighborSet_maxDegree_le_sub_one_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r) (hG : IsAdmissibleBookFree G r) (u : α) :
    (G.induce (G.neighborSet u)).maxDegree ≤ r - 1 :=
  maxDegree_le_of_forall_degree_le (G.induce (G.neighborSet u)) (r - 1)
    (induce_neighborSet_degree_le_sub_one_of_isAdmissibleBookFree hr hG u)

theorem one_le_induce_neighborSet_minDegree_of_isAdmissibleBookFree {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r)
    (u : α) [Nonempty (G.neighborSet u)] :
    1 ≤ (G.induce (G.neighborSet u)).minDegree :=
  le_minDegree_of_forall_le_degree (G.induce (G.neighborSet u)) 1
    (one_le_induce_neighborSet_degree_of_isAdmissibleBookFree hG u)

theorem card_induce_neighborSet_edgeFinset_le_mul_degree_div_two_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) (u : α) :
    (G.induce (G.neighborSet u)).edgeFinset.card ≤ ((r - 1) * G.degree u) / 2 := by
  have h1 := vertexTriangleClusterSum_le_sub_one_mul_degree_of_isAdmissibleBookFree hr hG u
  rw [vertexTriangleClusterSum_eq_twice_card_induce_edgeFinset] at h1
  omega

theorem induce_neighborSet_maxDegree_le_one_of_isAdmissibleBookFree_two {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    (G.induce (G.neighborSet u)).maxDegree ≤ 1 := by
  simpa using
    induce_neighborSet_maxDegree_le_sub_one_of_isAdmissibleBookFree (by omega : 1 ≤ 2) hG u

theorem induce_neighborSet_maxDegree_le_two_of_isAdmissibleBookFree_three {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 3) (u : α) :
    (G.induce (G.neighborSet u)).maxDegree ≤ 2 := by
  simpa using
    induce_neighborSet_maxDegree_le_sub_one_of_isAdmissibleBookFree (by omega : 1 ≤ 3) hG u

theorem induce_neighborSet_maxDegree_le_three_of_isAdmissibleBookFree_four {α : Type*} [Fintype α]
    {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 4) (u : α) :
    (G.induce (G.neighborSet u)).maxDegree ≤ 3 := by
  simpa using
    induce_neighborSet_maxDegree_le_sub_one_of_isAdmissibleBookFree (by omega : 1 ≤ 4) hG u

theorem card_trianglesContaining_eq_one_or_two_of_isAdmissibleBookFree_three
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 3)
    {uv : Sym2 α} (huv : uv ∈ G.edgeFinset) :
    (G.trianglesContaining uv).card = 1 ∨ (G.trianglesContaining uv).card = 2 := by
  have hpos : 1 ≤ (G.trianglesContaining uv).card := Finset.card_pos.mpr (hG.1 uv huv)
  have hlt : (G.trianglesContaining uv).card < 3 := hG.2 uv huv
  omega

theorem induce_neighborSet_degree_eq_one_or_two_of_isAdmissibleBookFree_three
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 3)
    (u : α) (v : G.neighborSet u) :
    (G.induce (G.neighborSet u)).degree v = 1 ∨ (G.induce (G.neighborSet u)).degree v = 2 := by
  rw [induce_neighborSet_degree_eq_card_trianglesContaining]
  exact card_trianglesContaining_eq_one_or_two_of_isAdmissibleBookFree_three hG
    (SimpleGraph.mem_edgeFinset.mpr v.2)

theorem card_induce_neighborSet_edgeFinset_le_degree_of_isAdmissibleBookFree_three
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 3) (u : α) :
    (G.induce (G.neighborSet u)).edgeFinset.card ≤ G.degree u := by
  have h := card_induce_neighborSet_edgeFinset_le_mul_degree_div_two_of_isAdmissibleBookFree
    (by omega : 1 ≤ 3) hG u
  omega

theorem card_trianglesContaining_mem_one_two_three_of_isAdmissibleBookFree_four
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 4)
    {uv : Sym2 α} (huv : uv ∈ G.edgeFinset) :
    (G.trianglesContaining uv).card = 1 ∨
      (G.trianglesContaining uv).card = 2 ∨
      (G.trianglesContaining uv).card = 3 := by
  have hpos : 1 ≤ (G.trianglesContaining uv).card := Finset.card_pos.mpr (hG.1 uv huv)
  have hlt : (G.trianglesContaining uv).card < 4 := hG.2 uv huv
  omega

theorem induce_neighborSet_degree_mem_one_two_three_of_isAdmissibleBookFree_four
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 4)
    (u : α) (v : G.neighborSet u) :
    (G.induce (G.neighborSet u)).degree v = 1 ∨
      (G.induce (G.neighborSet u)).degree v = 2 ∨
      (G.induce (G.neighborSet u)).degree v = 3 := by
  rw [induce_neighborSet_degree_eq_card_trianglesContaining]
  exact card_trianglesContaining_mem_one_two_three_of_isAdmissibleBookFree_four hG
    (SimpleGraph.mem_edgeFinset.mpr v.2)

theorem card_induce_neighborSet_edgeFinset_le_three_mul_degree_div_two_of_isAdmissibleBookFree_four
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 4) (u : α) :
    (G.induce (G.neighborSet u)).edgeFinset.card ≤ (3 * G.degree u) / 2 := by
  simpa using card_induce_neighborSet_edgeFinset_le_mul_degree_div_two_of_isAdmissibleBookFree
    (by omega : 1 ≤ 4) hG u

theorem vertexLinkDeficit_bot (α : Type*) [Fintype α] (r : ℕ) (u : α) :
    vertexLinkDeficit (⊥ : SimpleGraph α) r u = 0 := by
  simp [vertexLinkDeficit]

theorem vertexTriangleClusterSum_add_vertexLinkDeficit_eq_sub_one_mul_degree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) (u : α) :
    vertexTriangleClusterSum G u + vertexLinkDeficit G r u = (r - 1) * G.degree u := by
  unfold vertexTriangleClusterSum vertexLinkDeficit
  rw [← Finset.sum_add_distrib]
  have h1 : ∀ v ∈ G.neighborFinset u,
      (G.trianglesContaining s(u, v)).card + (r - 1 - (G.trianglesContaining s(u, v)).card) = r - 1 := by
    intro v hv
    have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
    have hlt := hG.2 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)
    omega
  rw [Finset.sum_congr rfl h1, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    smul_eq_mul, Nat.mul_comm]

theorem two_mul_card_induce_edgeFinset_add_vertexLinkDeficit_eq
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) (u : α) :
    2 * (G.induce (G.neighborSet u)).edgeFinset.card + vertexLinkDeficit G r u =
      (r - 1) * G.degree u := by
  rw [← vertexTriangleClusterSum_eq_twice_card_induce_edgeFinset,
    vertexTriangleClusterSum_add_vertexLinkDeficit_eq_sub_one_mul_degree hr hG u]

theorem vertexLinkDeficit_two_eq_zero_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) (u : α) :
    vertexLinkDeficit G 2 u = 0 := by
  have h1 := vertexTriangleClusterSum_add_vertexLinkDeficit_eq_sub_one_mul_degree
    (by omega : 1 ≤ 2) hG u
  have h2 := vertexTriangleClusterSum_eq_degree_of_isAdmissibleBookFree_two hG u
  omega

theorem even_vertexLinkDeficit_of_odd_r_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hodd : Odd r) (hG : IsAdmissibleBookFree G r) (u : α) :
    Even (vertexLinkDeficit G r u) := by
  have hident := two_mul_card_induce_edgeFinset_add_vertexLinkDeficit_eq hr hG u
  have hev_rhs : Even ((r - 1) * G.degree u) := by
    rw [Nat.even_mul]
    left
    rcases hodd with ⟨k, rfl⟩
    exact ⟨k, by omega⟩
  rw [← hident, Nat.even_add] at hev_rhs
  exact hev_rhs.mp (even_two_mul _)

theorem even_vertexLinkDeficit_iff_even_degree_of_even_r_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 2 ≤ r)
    (heven : Even r) (hG : IsAdmissibleBookFree G r) (u : α) :
    Even (vertexLinkDeficit G r u) ↔ Even (G.degree u) := by
  have hident := two_mul_card_induce_edgeFinset_add_vertexLinkDeficit_eq (by omega : 1 ≤ r) hG u
  have hnot_ev : ¬ Even (r - 1) := by
    rcases heven with ⟨k, rfl⟩
    rw [Nat.not_even_iff_odd]
    exact ⟨k - 1, by omega⟩
  have hiff :
      Even (2 * (G.induce (G.neighborSet u)).edgeFinset.card + vertexLinkDeficit G r u) ↔
        Even ((r - 1) * G.degree u) := by
    rw [hident]
  rw [Nat.even_add, iff_true_intro (even_two_mul _), true_iff, Nat.even_mul] at hiff
  tauto

theorem one_le_vertexLinkDeficit_of_even_r_of_odd_degree_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 2 ≤ r)
    (heven : Even r) (hG : IsAdmissibleBookFree G r) {u : α}
    (hodd_deg : Odd (G.degree u)) :
    1 ≤ vertexLinkDeficit G r u := by
  by_contra hlt
  have hzero : vertexLinkDeficit G r u = 0 := by omega
  have hev_def : Even (vertexLinkDeficit G r u) := by rw [hzero]; exact Even.zero
  have hev_deg : Even (G.degree u) :=
    (even_vertexLinkDeficit_iff_even_degree_of_even_r_of_isAdmissibleBookFree hr heven hG u).mp
      hev_def
  exact (Nat.not_even_iff_odd.mpr hodd_deg) hev_deg

theorem vertexTriangleClusterSum_le_sub_one_mul_degree_sub_one_of_even_r_of_odd_degree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 2 ≤ r)
    (heven : Even r) (hG : IsAdmissibleBookFree G r) {u : α}
    (hodd_deg : Odd (G.degree u)) :
    vertexTriangleClusterSum G u ≤ (r - 1) * G.degree u - 1 := by
  have hident :=
    vertexTriangleClusterSum_add_vertexLinkDeficit_eq_sub_one_mul_degree (by omega : 1 ≤ r) hG u
  have hpos :=
    one_le_vertexLinkDeficit_of_even_r_of_odd_degree_of_isAdmissibleBookFree hr heven hG hodd_deg
  omega

theorem one_le_vertexLinkDeficit_four_of_odd_degree_of_isAdmissibleBookFree_four
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 4)
    {u : α} (hodd_deg : Odd (G.degree u)) :
    1 ≤ vertexLinkDeficit G 4 u :=
  one_le_vertexLinkDeficit_of_even_r_of_odd_degree_of_isAdmissibleBookFree
    (by omega : 2 ≤ 4) (by decide : Even 4) hG hodd_deg

theorem vertexTriangleClusterSum_le_three_mul_degree_sub_one_of_odd_degree_of_isAdmissibleBookFree_four
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 4)
    {u : α} (hodd_deg : Odd (G.degree u)) :
    vertexTriangleClusterSum G u ≤ 3 * G.degree u - 1 := by
  simpa using
    vertexTriangleClusterSum_le_sub_one_mul_degree_sub_one_of_even_r_of_odd_degree
      (by omega : 2 ≤ 4) (by decide : Even 4) hG hodd_deg

theorem vertexLinkDeficit_three_eq_card_linkDegreeOneFinset_of_isAdmissibleBookFree_three
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 3) (u : α) :
    vertexLinkDeficit G 3 u = (linkDegreeOneFinset G u).card := by
  unfold vertexLinkDeficit linkDegreeOneFinset
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun v hv ↦ ?_)
  have huv : G.Adj u v := (SimpleGraph.mem_neighborFinset G u v).mp hv
  have hpos : 1 ≤ (G.trianglesContaining s(u, v)).card :=
    Finset.card_pos.mpr (hG.1 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv))
  have hlt : (G.trianglesContaining s(u, v)).card < 3 :=
    hG.2 s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)
  by_cases h1 : (G.trianglesContaining s(u, v)).card = 1
  · simp [h1]
  · simp [h1]
    omega

theorem two_mul_card_induce_edgeFinset_add_card_linkDegreeOneFinset_eq_two_mul_degree_of_isAdmissibleBookFree_three
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 3) (u : α) :
    2 * (G.induce (G.neighborSet u)).edgeFinset.card + (linkDegreeOneFinset G u).card =
      2 * G.degree u := by
  rw [← vertexLinkDeficit_three_eq_card_linkDegreeOneFinset_of_isAdmissibleBookFree_three hG u]
  simpa using two_mul_card_induce_edgeFinset_add_vertexLinkDeficit_eq (by omega : 1 ≤ 3) hG u

theorem even_card_linkDegreeOneFinset_of_isAdmissibleBookFree_three
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 3) (u : α) :
    Even (linkDegreeOneFinset G u).card := by
  rw [← vertexLinkDeficit_three_eq_card_linkDegreeOneFinset_of_isAdmissibleBookFree_three hG u]
  exact even_vertexLinkDeficit_of_odd_r_of_isAdmissibleBookFree
    (by omega : 1 ≤ 3) (by decide : Odd 3) hG u

theorem degree_sq_add_sum_neighborFinset_degree_add_vertexLinkDeficit_le
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) (u : α) :
    G.degree u * G.degree u + (∑ v ∈ G.neighborFinset u, G.degree v) +
        vertexLinkDeficit G r u ≤
      (Fintype.card α + r - 1) * G.degree u := by
  have h1 :=
    degree_sq_add_sum_neighborFinset_degree_le_card_mul_degree_add_vertexTriangleClusterSum G u
  have h2 := vertexTriangleClusterSum_add_vertexLinkDeficit_eq_sub_one_mul_degree hr hG u
  have h3 : Fintype.card α * G.degree u + (r - 1) * G.degree u =
      (Fintype.card α + r - 1) * G.degree u := by
    rw [← Nat.add_mul]
    congr 1
    omega
  omega

theorem edgeTriangleIncidenceSum_bot (α : Type*) [Fintype α] :
    edgeTriangleIncidenceSum (⊥ : SimpleGraph α) = 0 := by
  simp [edgeTriangleIncidenceSum]

theorem edgeTriangleIncidenceSqSum_bot (α : Type*) [Fintype α] :
    edgeTriangleIncidenceSqSum (⊥ : SimpleGraph α) = 0 := by
  simp [edgeTriangleIncidenceSqSum]

theorem edgeTriangleIncidenceSum_eq_three_mul_card_cliqueFinset
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    edgeTriangleIncidenceSum G = 3 * (G.cliqueFinset 3).card := by
  unfold edgeTriangleIncidenceSum
  have h1 : ∀ uv ∈ G.edgeFinset,
      (G.trianglesContaining uv).card =
        ∑ t ∈ G.cliqueFinset 3, if t ∈ G.trianglesContaining uv then 1 else 0 := by
    intro uv _
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter]
    have hsub : G.trianglesContaining uv ⊆ G.cliqueFinset 3 := by
      intro t ht
      exact (mem_trianglesContaining_iff G uv t).mp ht |>.1
    rw [Finset.inter_eq_right.mpr hsub]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ t ∈ G.cliqueFinset 3,
      (∑ uv ∈ G.edgeFinset, if t ∈ G.trianglesContaining uv then 1 else 0) = 3 := by
    intro t ht
    rw [← Finset.card_filter]
    exact card_filter_edgeFinset_trianglesContaining_eq_three G ht
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem sum_neighborFinset_eq_two_mul_sum_edgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) (f : Sym2 α → ℕ) :
    (∑ u : α, ∑ v ∈ G.neighborFinset u, f s(u, v)) =
      2 * ∑ uv ∈ G.edgeFinset, f uv := by
  have h1 : ∀ u : α,
      (∑ v ∈ G.neighborFinset u, f s(u, v)) =
        ∑ uv ∈ G.edgeFinset, if u ∈ uv then f uv else 0 := by
    intro u
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun v _ ↦ s(u, v)) ?_ ?_ ?_ ?_
    · intro v hv
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      exact ⟨(SimpleGraph.mem_neighborFinset G u v).mp hv, Sym2.mem_mk_left u v⟩
    · intro v₁ hv₁ v₂ _ heq
      rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exfalso
        exact SimpleGraph.notMem_neighborFinset_self G v₁ hv₁
    · intro uv huv
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at huv
      obtain ⟨h_edge, hu_mem⟩ := huv
      obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.mp hu_mem
      refine ⟨v, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact h_edge
    · intro _ _
      rfl
  rw [Finset.sum_congr rfl (fun u _ ↦ h1 u), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun uv huv ↦ ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  congr 1
  induction uv using Sym2.ind with
  | _ u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp huv
    have hne : u ≠ v := G.ne_of_adj hadj
    have hfilt : (Finset.univ : Finset α).filter (fun x ↦ x ∈ s(u, v)) = {u, v} := by
      ext x
      simp [Sym2.mem_iff]
    rw [hfilt, Finset.card_pair hne]

theorem sum_vertexTriangleClusterSum_eq_two_mul_edgeTriangleIncidenceSum
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (∑ u : α, vertexTriangleClusterSum G u) = 2 * edgeTriangleIncidenceSum G :=
  sum_neighborFinset_eq_two_mul_sum_edgeFinset G (fun uv ↦ (G.trianglesContaining uv).card)

theorem sum_vertexTriangleClusterSum_eq_six_mul_card_cliqueFinset
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (∑ u : α, vertexTriangleClusterSum G u) = 6 * (G.cliqueFinset 3).card := by
  rw [sum_vertexTriangleClusterSum_eq_two_mul_edgeTriangleIncidenceSum,
    edgeTriangleIncidenceSum_eq_three_mul_card_cliqueFinset]
  ring

theorem sum_card_induce_neighborSet_edgeFinset_eq_edgeTriangleIncidenceSum
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (∑ u : α, (G.induce (G.neighborSet u)).edgeFinset.card) = edgeTriangleIncidenceSum G := by
  have h := sum_vertexTriangleClusterSum_eq_two_mul_edgeTriangleIncidenceSum G
  have h2 : (∑ u : α, vertexTriangleClusterSum G u) =
      2 * ∑ u : α, (G.induce (G.neighborSet u)).edgeFinset.card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ ↦ ?_)
    exact vertexTriangleClusterSum_eq_twice_card_induce_edgeFinset G u
  omega

theorem sum_card_induce_neighborSet_edgeFinset_eq_three_mul_card_cliqueFinset
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (∑ u : α, (G.induce (G.neighborSet u)).edgeFinset.card) = 3 * (G.cliqueFinset 3).card := by
  rw [sum_card_induce_neighborSet_edgeFinset_eq_edgeTriangleIncidenceSum,
    edgeTriangleIncidenceSum_eq_three_mul_card_cliqueFinset]

theorem card_edgeFinset_le_edgeTriangleIncidenceSum_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hG : IsAdmissibleBookFree G r) :
    G.edgeFinset.card ≤ edgeTriangleIncidenceSum G := by
  rw [Finset.card_eq_sum_ones]
  unfold edgeTriangleIncidenceSum
  exact Finset.sum_le_sum (fun uv huv ↦ Finset.card_pos.mpr (hG.1 uv huv))

theorem edgeTriangleIncidenceSum_le_sub_one_mul_card_edgeFinset_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) :
    edgeTriangleIncidenceSum G ≤ (r - 1) * G.edgeFinset.card := by
  have hle : edgeTriangleIncidenceSum G ≤ ∑ _uv ∈ G.edgeFinset, (r - 1) := by
    unfold edgeTriangleIncidenceSum
    refine Finset.sum_le_sum (fun uv huv ↦ ?_)
    have hlt := hG.2 uv huv
    omega
  simpa [Finset.sum_const, smul_eq_mul, Nat.mul_comm] using hle

theorem edgeTriangleIncidenceSum_eq_card_edgeFinset_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2) :
    edgeTriangleIncidenceSum G = G.edgeFinset.card := by
  have h1 := card_edgeFinset_le_edgeTriangleIncidenceSum_of_isAdmissibleBookFree hG
  have h2 := edgeTriangleIncidenceSum_le_sub_one_mul_card_edgeFinset_of_isAdmissibleBookFree
    (by omega : 1 ≤ 2) hG
  omega

theorem sum_sq_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ ↦ 1) f
  simpa [Finset.sum_const, smul_eq_mul] using h

theorem edgeTriangleIncidenceSum_sq_le_card_edgeFinset_mul_edgeTriangleIncidenceSqSum
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (edgeTriangleIncidenceSum G) ^ 2 ≤ G.edgeFinset.card * edgeTriangleIncidenceSqSum G :=
  sum_sq_le_card_mul_sum_sq G.edgeFinset (fun uv ↦ (G.trianglesContaining uv).card)

theorem nine_mul_card_cliqueFinset_sq_le_card_edgeFinset_mul_edgeTriangleIncidenceSqSum
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    9 * (G.cliqueFinset 3).card ^ 2 ≤ G.edgeFinset.card * edgeTriangleIncidenceSqSum G := by
  have h := edgeTriangleIncidenceSum_sq_le_card_edgeFinset_mul_edgeTriangleIncidenceSqSum G
  rw [edgeTriangleIncidenceSum_eq_three_mul_card_cliqueFinset] at h
  calc
    9 * (G.cliqueFinset 3).card ^ 2 = (3 * (G.cliqueFinset 3).card) ^ 2 := by ring
    _ ≤ G.edgeFinset.card * edgeTriangleIncidenceSqSum G := h

theorem vertexTriangleClusterSum_sq_le_degree_mul_sum_trianglesContaining_sq
    {α : Type*} [Fintype α] (G : SimpleGraph α) (u : α) :
    (vertexTriangleClusterSum G u) ^ 2 ≤
      G.degree u * ∑ v ∈ G.neighborFinset u, (G.trianglesContaining s(u, v)).card ^ 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact sum_sq_le_card_mul_sum_sq (G.neighborFinset u)
    (fun v ↦ (G.trianglesContaining s(u, v)).card)

theorem four_mul_card_edgeFinset_sq_le_card_mul_sum_degree_sq
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    4 * G.edgeFinset.card ^ 2 ≤ Fintype.card α * ∑ u : α, G.degree u ^ 2 := by
  have h := sum_sq_le_card_mul_sum_sq (Finset.univ : Finset α) (fun u ↦ G.degree u)
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.card_univ] at h
  calc
    4 * G.edgeFinset.card ^ 2 = (2 * G.edgeFinset.card) ^ 2 := by ring
    _ ≤ Fintype.card α * ∑ u : α, G.degree u ^ 2 := h

theorem sum_sum_neighborFinset_degree_eq_sum_degree_sq
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (∑ u : α, ∑ v ∈ G.neighborFinset u, G.degree v) = ∑ u : α, G.degree u ^ 2 := by
  have h1 : (∑ u : α, ∑ v ∈ G.neighborFinset u, G.degree v) =
      ∑ u : α, ∑ v : α, if G.Adj u v then G.degree v else 0 := by
    refine Finset.sum_congr rfl (fun u _ ↦ ?_)
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp [SimpleGraph.mem_neighborFinset]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ ↦ ?_)
  have h2 : (∑ x : α, if G.Adj x v then G.degree v else 0) =
      ∑ _x ∈ G.neighborFinset v, G.degree v := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [h2, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul, sq]

theorem sum_degree_sq_le_card_mul_card_edgeFinset_add_edgeTriangleIncidenceSum
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (∑ u : α, G.degree u ^ 2) ≤
      Fintype.card α * G.edgeFinset.card + edgeTriangleIncidenceSum G := by
  have hsum : ∑ u : α, (G.degree u * G.degree u + ∑ v ∈ G.neighborFinset u, G.degree v) ≤
      ∑ u : α, (Fintype.card α * G.degree u + vertexTriangleClusterSum G u) :=
    Finset.sum_le_sum (fun u _ ↦
      degree_sq_add_sum_neighborFinset_degree_le_card_mul_degree_add_vertexTriangleClusterSum G u)
  have hsq : (∑ u : α, G.degree u * G.degree u) = ∑ u : α, G.degree u ^ 2 :=
    Finset.sum_congr rfl (fun u _ ↦ (sq (G.degree u)).symm)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsq,
    sum_sum_neighborFinset_degree_eq_sum_degree_sq, ← Finset.mul_sum,
    SimpleGraph.sum_degrees_eq_twice_card_edges,
    sum_vertexTriangleClusterSum_eq_two_mul_edgeTriangleIncidenceSum] at hsum
  have hmul : Fintype.card α * (2 * G.edgeFinset.card) =
      2 * (Fintype.card α * G.edgeFinset.card) := by ring
  omega

theorem sum_degree_sq_le_card_add_sub_one_mul_card_edgeFinset_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) :
    (∑ u : α, G.degree u ^ 2) ≤ (Fintype.card α + r - 1) * G.edgeFinset.card := by
  have h1 := sum_degree_sq_le_card_mul_card_edgeFinset_add_edgeTriangleIncidenceSum G
  have h2 := edgeTriangleIncidenceSum_le_sub_one_mul_card_edgeFinset_of_isAdmissibleBookFree hr hG
  have h3 : Fintype.card α * G.edgeFinset.card + (r - 1) * G.edgeFinset.card =
      (Fintype.card α + r - 1) * G.edgeFinset.card := by
    rw [← Nat.add_mul]
    congr 1
    omega
  omega

theorem four_mul_card_edgeFinset_le_card_mul_card_add_sub_one_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) :
    4 * G.edgeFinset.card ≤ Fintype.card α * (Fintype.card α + r - 1) := by
  by_cases h0 : G.edgeFinset.card = 0
  · rw [h0]
    exact Nat.zero_le _
  · have hpos : 0 < G.edgeFinset.card := Nat.pos_of_ne_zero h0
    have hcs := four_mul_card_edgeFinset_sq_le_card_mul_sum_degree_sq G
    have hdeg := sum_degree_sq_le_card_add_sub_one_mul_card_edgeFinset_of_isAdmissibleBookFree hr hG
    have hmul : 4 * G.edgeFinset.card * G.edgeFinset.card ≤
        Fintype.card α * (Fintype.card α + r - 1) * G.edgeFinset.card := by
      calc
        4 * G.edgeFinset.card * G.edgeFinset.card
          = 4 * G.edgeFinset.card ^ 2 := by ring
        _ ≤ Fintype.card α * ∑ u : α, G.degree u ^ 2 := hcs
        _ ≤ Fintype.card α * ((Fintype.card α + r - 1) * G.edgeFinset.card) :=
          Nat.mul_le_mul_left (Fintype.card α) hdeg
        _ = Fintype.card α * (Fintype.card α + r - 1) * G.edgeFinset.card := by ring
    exact Nat.le_of_mul_le_mul_right hmul hpos

theorem card_edgeFinset_le_card_mul_card_add_sub_one_div_four_of_isAdmissibleBookFree
    {α : Type*} [Fintype α] {G : SimpleGraph α} {r : ℕ} (hr : 1 ≤ r)
    (hG : IsAdmissibleBookFree G r) :
    G.edgeFinset.card ≤ (Fintype.card α * (Fintype.card α + r - 1)) / 4 := by
  have h := four_mul_card_edgeFinset_le_card_mul_card_add_sub_one_of_isAdmissibleBookFree hr hG
  omega

theorem maxAdmissibleEdges_le_mul_add_sub_one_div_four (n : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    maxAdmissibleEdges n r ≤ (n * (n + r - 1)) / 4 := by
  obtain ⟨G, hG, hcard⟩ := exists_isAdmissibleBookFree_card_eq_maxAdmissibleEdges n r
  have h := card_edgeFinset_le_card_mul_card_add_sub_one_div_four_of_isAdmissibleBookFree hr hG
  simpa [hcard] using h

theorem eFunction_le_mul_add_sub_one_div_four_add_one (n : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    eFunction n r ≤ (n * (n + r - 1)) / 4 + 1 := by
  rw [eFunction_eq_maxAdmissibleEdges_add_one]
  exact Nat.add_le_add_right (maxAdmissibleEdges_le_mul_add_sub_one_div_four n hr) 1

theorem maxAdmissibleEdges_three_le_mul_add_two_div_four (n : ℕ) :
    maxAdmissibleEdges n 3 ≤ (n * (n + 2)) / 4 := by
  simpa using maxAdmissibleEdges_le_mul_add_sub_one_div_four n (by omega : 1 ≤ 3)

theorem maxAdmissibleEdges_four_le_mul_add_three_div_four (n : ℕ) :
    maxAdmissibleEdges n 4 ≤ (n * (n + 3)) / 4 := by
  simpa using maxAdmissibleEdges_le_mul_add_sub_one_div_four n (by omega : 1 ≤ 4)

theorem stepDiff_eq_maxAdmissibleEdges_sub (n r : ℕ) :
    stepDiff n r = maxAdmissibleEdges n (r + 1) - maxAdmissibleEdges n r := by
  unfold stepDiff
  rw [eFunction_eq_maxAdmissibleEdges_add_one n (r + 1),
    eFunction_eq_maxAdmissibleEdges_add_one n r]
  omega

theorem eFunction_add_stepDiff_eq (n r : ℕ) :
    eFunction n r + stepDiff n r = eFunction n (r + 1) := by
  unfold stepDiff
  have hmono : eFunction n r ≤ eFunction n (r + 1) := eFunction_mono_right (Nat.le_succ r)
  omega

theorem maxAdmissibleEdges_add_stepDiff_eq (n r : ℕ) :
    maxAdmissibleEdges n r + stepDiff n r = maxAdmissibleEdges n (r + 1) := by
  rw [stepDiff_eq_maxAdmissibleEdges_sub]
  have hmono : maxAdmissibleEdges n r ≤ maxAdmissibleEdges n (r + 1) :=
    maxAdmissibleEdges_mono_right (Nat.le_succ r)
  omega

theorem stepDiff_zero (n : ℕ) : stepDiff n 0 = 0 :=
  by
    unfold stepDiff
    rw [eFunction_one, eFunction_zero]

theorem stepDiff_of_lt_three {n : ℕ} (hn : n < 3) (r : ℕ) :
    stepDiff n r = 0 := by
  unfold stepDiff
  rw [eFunction_of_lt_three hn (r + 1), eFunction_of_lt_three hn r]

theorem stepDiff_eq_zero_of_sub_one_le {n r : ℕ} (hn : 3 ≤ n) (hr : n - 1 ≤ r) :
    stepDiff n r = 0 := by
  unfold stepDiff
  rw [eFunction_eq_choose_two_succ_of_sub_one_le hn (by omega),
    eFunction_eq_choose_two_succ_of_sub_one_le hn hr]
  omega

theorem one_le_stepDiff_at_add_two {r : ℕ} (hr : 1 ≤ r) :
    1 ≤ stepDiff (r + 2) r :=
  one_le_eFunction_step_diff_at_add_two hr

theorem stepDiff_four_two : stepDiff 4 2 = 3 :=
  eFunction_four_step_diff

theorem card_edgeFinset_sub_maxAdmissibleEdges_le_stepDiff_of_isAdmissibleBookFree_succ
    {n r : ℕ} {G : SimpleGraph (Fin n)} (hG : IsAdmissibleBookFree G (r + 1)) :
    G.edgeFinset.card - maxAdmissibleEdges n r ≤ stepDiff n r := by
  have hle := card_edgeFinset_le_maxAdmissibleEdges_of_isAdmissibleBookFree hG
  rw [stepDiff_eq_maxAdmissibleEdges_sub]
  omega

theorem card_edgeFinset_sub_mantel_turan_le_stepDiff_of_isAdmissibleBookFree_succ
    {n r : ℕ} (hr : 1 ≤ r) {G : SimpleGraph (Fin n)}
    (hG : IsAdmissibleBookFree G (r + 1)) :
    G.edgeFinset.card - (n * (n + r - 1)) / 4 ≤ stepDiff n r := by
  have h1 := card_edgeFinset_sub_maxAdmissibleEdges_le_stepDiff_of_isAdmissibleBookFree_succ hG
  have h2 := maxAdmissibleEdges_le_mul_add_sub_one_div_four n hr
  omega

theorem card_edgeFinset_sub_parity_bound_le_stepDiff_two_of_isAdmissibleBookFree_three
    {n : ℕ} {G : SimpleGraph (Fin n)} (hG : IsAdmissibleBookFree G 3) :
    G.edgeFinset.card - n * ((n - 1) / 2) ≤ stepDiff n 2 := by
  have h1 := card_edgeFinset_sub_maxAdmissibleEdges_le_stepDiff_of_isAdmissibleBookFree_succ hG
  have h2 := maxAdmissibleEdges_two_le_mul_div_two n
  omega

theorem exists_edge_trianglesContaining_card_eq_of_isAdmissibleBookFree_succ_of_maxAdmissibleEdges_lt
    {n r : ℕ} {G : SimpleGraph (Fin n)} (hG : IsAdmissibleBookFree G (r + 1))
    (hlt : maxAdmissibleEdges n r < G.edgeFinset.card) :
    ∃ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card = r := by
  have hge : eFunction n r ≤ G.edgeFinset.card := by
    have he := eFunction_eq_maxAdmissibleEdges_add_one n r
    omega
  obtain ⟨uv, huv, hr_le⟩ := erdos600Prop_eFunction n r G hge hG.1
  have hlt_succ := hG.2 uv huv
  refine ⟨uv, huv, ?_⟩
  omega

theorem stepDiff_le_of_forall_isAdmissibleBookFree_succ_exists_sub
    (n r d : ℕ)
    (h : ∀ G : SimpleGraph (Fin n), IsAdmissibleBookFree G (r + 1) →
      ∃ H : SimpleGraph (Fin n), IsAdmissibleBookFree H r ∧
        G.edgeFinset.card ≤ H.edgeFinset.card + d) :
    stepDiff n r ≤ d := by
  obtain ⟨G, hG, hcardG⟩ := exists_isAdmissibleBookFree_card_eq_maxAdmissibleEdges n (r + 1)
  obtain ⟨H, hH, hle⟩ := h G hG
  have hcardH := card_edgeFinset_le_maxAdmissibleEdges_of_isAdmissibleBookFree hH
  rw [stepDiff_eq_maxAdmissibleEdges_sub]
  omega

theorem erdos_600_parts_i_of_forall_bound_exists_gadget
    (h : ∀ r : ℕ, 2 ≤ r → ∀ B : ℝ, ∃ k : ℕ, ∀ᶠ n : ℕ in atTop,
      B + ((eFunction n r : ℝ) - (eFunction (n - k) r : ℝ)) ≤ (eFunction k (r + 1) : ℝ) - 1) :
    ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ)) atTop atTop := by
  intro r hr
  exact tendsto_step_diff_atTop_of_forall_bound_exists_gadget (h r hr)

theorem tendsto_div_nhds_one_of_book_deletion_isLittleO {r : ℕ}
    (d : ℕ → ℕ)
    (hdel : ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), IsAdmissibleBookFree G (r + 1) →
      ∃ H : SimpleGraph (Fin n), IsAdmissibleBookFree H r ∧
        G.edgeFinset.card ≤ H.edgeFinset.card + d n)
    (ho : (fun n : ℕ ↦ (d n : ℝ)) =o[atTop] (fun n : ℕ ↦ (eFunction n r : ℝ))) :
    Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) / (eFunction n r : ℝ)) atTop (𝓝 1) := by
  rw [tendsto_div_nhds_one_iff_sub_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ ho
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall (fun n ↦ ?_)⟩
  have hstep : stepDiff n r ≤ d n :=
    stepDiff_le_of_forall_isAdmissibleBookFree_succ_exists_sub n r (d n) (hdel n)
  have hmono : eFunction n r ≤ eFunction n (r + 1) := eFunction_mono_right (Nat.le_succ r)
  have hsub : (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ) = (stepDiff n r : ℝ) := by
    unfold stepDiff
    exact (Nat.cast_sub hmono).symm
  have hnonneg : (0 : ℝ) ≤ (stepDiff n r : ℝ) := Nat.cast_nonneg _
  have hd_nonneg : (0 : ℝ) ≤ (d n : ℝ) := Nat.cast_nonneg _
  rw [hsub, Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hd_nonneg, one_mul]
  exact Nat.cast_le.mpr hstep

theorem erdos_600_parts_ii_of_forall_book_deletion_isLittleO
    (d : ℕ → ℕ → ℕ)
    (hdel : ∀ r : ℕ, 2 ≤ r → ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      IsAdmissibleBookFree G (r + 1) →
        ∃ H : SimpleGraph (Fin n), IsAdmissibleBookFree H r ∧
          G.edgeFinset.card ≤ H.edgeFinset.card + d r n)
    (ho : ∀ r : ℕ, 2 ≤ r →
      (fun n : ℕ ↦ (d r n : ℝ)) =o[atTop] (fun n : ℕ ↦ (eFunction n r : ℝ))) :
    ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) / (eFunction n r : ℝ)) atTop (𝓝 1) := by
  intro r hr
  exact tendsto_div_nhds_one_of_book_deletion_isLittleO (d r) (hdel r hr) (ho r hr)

end LinkGraphCycleDeficitAndTriangleCauchySchwarz

end Erdos600
