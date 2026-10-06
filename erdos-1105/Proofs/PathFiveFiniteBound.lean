module

public import PathFiveP4Bound
public import PathFourFreeStarGeneric

@[expose] public section

/-!
The connected `P₅`-free extremal bound on any finite vertex carrier. This
version can be applied to the vertex subtype of a connected component.
-/

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- A connected `P₅`-free graph on at least five vertices has at most one
edge per vertex. -/
theorem connected_path_five_free_edge_le_finite {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 5 ≤ Fintype.card V)
    (hconn : G.Connected) (hfree : (pathGraph 5).Free G) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  by_cases hfour : (pathGraph 4).Free G
  · exact ErdosProblems.AntiRamseyPathFourFree.connected_path_four_free_edge_le_finite
      G hn hconn hfour
  · have hcopy : (pathGraph 4) ⊑ G := not_free.mp hfour
    obtain ⟨f⟩ := hcopy
    have hbase : ([0, 1, 2, 3] : List (Fin 4)).Nodup := by decide
    have hpath : [f (0 : Fin 4), f (1 : Fin 4), f (2 : Fin 4), f (3 : Fin 4)].Nodup := by
      simpa using (List.Nodup.map f.injective hbase)
    have hab : G.Adj (f (0 : Fin 4)) (f (1 : Fin 4)) :=
      f.toHom.map_adj ((pathGraph_adj).2 (Or.inl (by decide)))
    have hbc : G.Adj (f (1 : Fin 4)) (f (2 : Fin 4)) :=
      f.toHom.map_adj ((pathGraph_adj).2 (Or.inl (by decide)))
    have hcd : G.Adj (f (2 : Fin 4)) (f (3 : Fin 4)) :=
      f.toHom.map_adj ((pathGraph_adj).2 (Or.inl (by decide)))
    exact p4_connected_p5_free_edges_le_card G hn hfree hconn
      (f (0 : Fin 4)) (f (1 : Fin 4)) (f (2 : Fin 4)) (f (3 : Fin 4))
      hpath hab hbc hcd

end ErdosProblems.AntiRamseyPathFiveExtremal
