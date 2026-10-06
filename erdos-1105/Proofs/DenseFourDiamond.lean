module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

@[expose] public section

/-!
A four-vertex simple graph with at least five of its six possible edges
contains the five-edge diamond as a non-induced subgraph. The missing edge,
if any, is placed between the two degree-two vertices. This is a graph-only
lemma for the `P₅` anti-Ramsey upper bound.
-/

namespace ErdosProblems.AntiRamseyPathFiveDiamond

open SimpleGraph

/-- Choose the two endpoints of a possible missing edge as positions `0,1`.
The remaining two vertices become positions `2,3`. -/
def orientMissing (e : Sym2 (Fin 4)) : Fin 4 → Fin 4 :=
  if e = s(0, 2) then ![0, 2, 1, 3]
  else if e = s(0, 3) then ![0, 3, 1, 2]
  else if e = s(1, 2) then ![1, 2, 0, 3]
  else if e = s(1, 3) then ![1, 3, 0, 2]
  else if e = s(2, 3) then ![2, 3, 0, 1]
  else id

theorem orientMissing_properties (e : Sym2 (Fin 4))
    (he : e ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset) :
    Function.Injective (orientMissing e) ∧
      s(orientMissing e 0, orientMissing e 1) = e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hne : a ≠ b := by
      have hadj : (⊤ : SimpleGraph (Fin 4)).Adj a b := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      exact (top_adj _ _).mp hadj
    fin_cases a <;> fin_cases b <;>
      first
      | exact (hne rfl).elim
      | decide

/-- A graph on four vertices with at least five edges is missing at most one
complete-graph edge. -/
theorem missing_edge_card_le_one (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] (hfive : 5 ≤ G.edgeFinset.card) :
    ((⊤ : SimpleGraph (Fin 4)).edgeFinset \ G.edgeFinset).card ≤ 1 := by
  classical
  have hsubset : G.edgeFinset ⊆ (⊤ : SimpleGraph (Fin 4)).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have hsix : (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 := by decide
  rw [Finset.card_sdiff_of_subset hsubset]
  omega

/-- If one complete-graph edge is absent, every distinct complete-graph edge
must be present under the five-edge hypothesis. -/
theorem other_edge_present (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] (hfive : 5 ≤ G.edgeFinset.card)
    (e₀ e₁ : Sym2 (Fin 4))
    (hmiss : e₀ ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset \ G.edgeFinset)
    (htop : e₁ ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset)
    (hne : e₁ ≠ e₀) : e₁ ∈ G.edgeFinset := by
  classical
  by_contra hnot
  have hmiss₁ : e₁ ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset \ G.edgeFinset :=
    Finset.mem_sdiff.mpr ⟨htop, hnot⟩
  have hpair : ({e₀, e₁} : Finset (Sym2 (Fin 4))) ⊆
      (⊤ : SimpleGraph (Fin 4)).edgeFinset \ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hmiss
    · exact hmiss₁
  have hcardpair : ({e₀, e₁} : Finset (Sym2 (Fin 4))).card = 2 := by
    have hnot : e₀ ∉ ({e₁} : Finset (Sym2 (Fin 4))) := by
      simpa only [Finset.mem_singleton] using (Ne.symm hne)
    rw [Finset.card_insert_of_notMem hnot]
    simp
  have hcard := Finset.card_le_card hpair
  have hmax := missing_edge_card_le_one G hfive
  omega

/-- The five named edges `02,03,12,13,23` are present after orienting the
possible unique missing edge to `01`. -/
theorem dense_four_has_diamond (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] (hfive : 5 ≤ G.edgeFinset.card) :
    ∃ u : Fin 4 → Fin 4, Function.Injective u ∧
      G.Adj (u 0) (u 2) ∧ G.Adj (u 0) (u 3) ∧
      G.Adj (u 1) (u 2) ∧ G.Adj (u 1) (u 3) ∧
      G.Adj (u 2) (u 3) := by
  classical
  let T : Finset (Sym2 (Fin 4)) := (⊤ : SimpleGraph (Fin 4)).edgeFinset
  by_cases hfull : T ⊆ G.edgeFinset
  · have hfull_adj (i j : Fin 4) (hij : i ≠ j) : G.Adj i j := by
      have htop : s(i, j) ∈ T := by
        simpa only [T, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
          ((top_adj i j).mpr hij)
      have hpresent : s(i, j) ∈ G.edgeFinset := hfull htop
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hpresent
    exact ⟨id, fun _ _ h => h,
      hfull_adj 0 2 (by decide), hfull_adj 0 3 (by decide),
      hfull_adj 1 2 (by decide), hfull_adj 1 3 (by decide),
      hfull_adj 2 3 (by decide)⟩
  · obtain ⟨e, heT, heNot⟩ := Finset.not_subset.mp hfull
    have hmiss : e ∈ T \ G.edgeFinset := Finset.mem_sdiff.mpr ⟨heT, heNot⟩
    let u : Fin 4 → Fin 4 := orientMissing e
    obtain ⟨hu, hmissing⟩ := orientMissing_properties e heT
    have hadj (i j : Fin 4) (hij : i ≠ j)
        (hnot : s(i, j) ≠ s((0 : Fin 4), (1 : Fin 4))) :
        G.Adj (u i) (u j) := by
      have htop : s(u i, u j) ∈ T := by
        simpa only [T, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
          ((top_adj (u i) (u j)).mpr (hu.ne hij))
      have hne : s(u i, u j) ≠ e := by
        intro heq
        have hmap : Sym2.map u s(i, j) =
            Sym2.map u s((0 : Fin 4), (1 : Fin 4)) := by
          simp only [Sym2.map_mk]
          rw [hmissing]
          exact heq
        exact hnot ((Sym2.map.injective hu) hmap)
      have hpresent := other_edge_present G hfive e s(u i, u j) hmiss htop hne
      simpa only [G.mem_edgeFinset, G.mem_edgeSet] using hpresent
    exact ⟨u, hu,
      hadj 0 2 (by decide) (by decide),
      hadj 0 3 (by decide) (by decide),
      hadj 1 2 (by decide) (by decide),
      hadj 1 3 (by decide) (by decide),
      hadj 2 3 (by decide) (by decide)⟩

end ErdosProblems.AntiRamseyPathFiveDiamond
