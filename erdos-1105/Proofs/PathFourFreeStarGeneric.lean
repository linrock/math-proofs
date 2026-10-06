module

public import PathFourFreeStar
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

/-!
Finite-vertex transport of the connected `P₄`-free star edge count from
`PathFourFreeStar` along `SimpleGraph.overFinIso`.
-/

namespace ErdosProblems.AntiRamseyPathFourFree

open SimpleGraph

/-- The exact no-`P₄` star edge count for any finite vertex carrier. This is
the form usable for a connected component represented as a subtype. -/
theorem connected_path_four_free_edge_count_finite {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 4 ≤ Fintype.card V) (hconn : G.Connected)
    (hfree : (pathGraph 4).Free G) :
    G.edgeFinset.card + 1 = Fintype.card V := by
  classical
  let H : SimpleGraph (Fin (Fintype.card V)) := G.overFin rfl
  let e : G ≃g H := G.overFinIso rfl
  have hconnH : H.Connected := e.connected_iff.mp hconn
  have hfreeH : (pathGraph 4).Free H := (free_congr_right e).mp hfree
  have hcount : H.edgeFinset.card + 1 = Fintype.card V :=
    connected_path_four_free_edge_count hn H hconnH hfreeH
  have hcard : G.edgeFinset.card = H.edgeFinset.card := e.card_edgeFinset_eq
  omega

/-- The component-count interface used by the connected `P₅` argument. -/
theorem connected_path_four_free_edge_le_finite {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 5 ≤ Fintype.card V) (hconn : G.Connected)
    (hfree : (pathGraph 4).Free G) :
    G.edgeFinset.card ≤ Fintype.card V := by
  have h := connected_path_four_free_edge_count_finite G (by omega : 4 ≤ Fintype.card V)
    hconn hfree
  omega

end ErdosProblems.AntiRamseyPathFourFree
