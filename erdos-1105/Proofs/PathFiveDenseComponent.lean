module

public import PathFiveComponentArithmetic
public import PathFiveFiniteBound

@[expose] public section

/-!
A graph-only dense-component consequence of the connected `P₅` extremal
bound. A later module may extract a named diamond copy from this component.
-/

namespace ErdosProblems.AntiRamseyPathFiveComponents

open SimpleGraph

/-- A `P₅`-free graph on at least five vertices with more edges than vertices
has a four-vertex connected component with at least five edges. -/
theorem exists_dense_four_component {n : ℕ} (_hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : (pathGraph 5).Free G) (hmore : n < G.edgeFinset.card) :
    ∃ C : G.ConnectedComponent,
      Fintype.card C.supp = 4 ∧ 5 ≤ Nat.card C.toSimpleGraph.edgeSet := by
  classical
  by_contra hnone
  have hfour : ∀ C : G.ConnectedComponent,
      Fintype.card C.supp = 4 → Nat.card C.toSimpleGraph.edgeSet ≤ 4 := by
    intro C hm
    by_contra hle
    have hfive : 5 ≤ Nat.card C.toSimpleGraph.edgeSet := by omega
    exact hnone ⟨C, hm, hfive⟩
  have hlarge : ∀ C : G.ConnectedComponent,
      5 ≤ Fintype.card C.supp →
      Nat.card C.toSimpleGraph.edgeSet ≤ Fintype.card C.supp := by
    intro C hm
    have hcopy : C.toSimpleGraph ⊑ G := by
      refine ⟨{ toHom := C.toSimpleGraph_hom, injective' := ?_ }⟩
      intro u v huv
      exact Subtype.coe_injective huv
    have hfreeC : (pathGraph 5).Free C.toSimpleGraph := by
      intro hpath
      exact hfree (hpath.trans hcopy)
    have hcardSupp : Fintype.card C = Fintype.card C.supp :=
      Fintype.card_congr (Equiv.refl _)
    have hmC : 5 ≤ Fintype.card C := by
      rw [hcardSupp]
      exact hm
    have hcard : Nat.card C.toSimpleGraph.edgeSet = C.toSimpleGraph.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card]
      exact C.toSimpleGraph.card_edgeSet
    rw [hcard]
    have hbound := ErdosProblems.AntiRamseyPathFiveExtremal.connected_path_five_free_edge_le_finite
      C.toSimpleGraph hmC C.connected_toSimpleGraph hfreeC
    rw [hcardSupp] at hbound
    exact hbound
  have hbound := edge_le_vertex_of_component_bounds G hlarge hfour
  have hbound' : G.edgeFinset.card ≤ n := by simpa using hbound
  omega

end ErdosProblems.AntiRamseyPathFiveComponents
