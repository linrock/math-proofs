module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
Graph-cut lemmas for bridges crossed by a trail in the residual component
decomposition.
-/

universe u

open SimpleGraph

namespace ErdosProblems.PathUpperReduction

/-- A bridge used by a trail separates the endpoints of that trail. -/
theorem bridge_on_trail_separates_endpoints
    {V : Type u} (G : SimpleGraph V) {a b : V}
    (p : G.Walk a b) (hp : p.IsTrail) {e : Sym2 V}
    (he : e ∈ p.edges) (hbridge : G.IsBridge e) :
    ¬ (G.deleteEdges {e}).Reachable a b := by
  classical
  cases e with
  | h x y =>
    have hxy : ¬ (G.deleteEdges {s(x, y)}).Reachable x y :=
      SimpleGraph.isBridge_iff.mp hbridge
    intro hab
    by_cases hay : (G.deleteEdges {s(x, y)}).Reachable a y
    · have hax : ¬ (G.deleteEdges {s(x, y)}).Reachable a x := by
        intro hax
        exact hxy (hax.symm.trans hay)
      have hbx : ¬ (G.deleteEdges {s(x, y)}).Reachable b x := by
        intro hbx
        exact hxy (hbx.symm.trans (hab.symm.trans hay))
      have hswap : s(y, x) = s(x, y) := Sym2.eq_swap
      have hax' : ¬ (G.deleteEdges {s(y, x)}).Reachable a x := by
        simpa only [hswap] using hax
      have hbx' : ¬ (G.deleteEdges {s(y, x)}).Reachable b x := by
        simpa only [hswap] using hbx
      have hnot : s(y, x) ∉ p.edges :=
        hp.not_mem_edges_of_not_reachable (x := y) (y := x) hax' hbx'
      exact hnot (by simpa only [hswap] using he)
    · have hby : ¬ (G.deleteEdges {s(x, y)}).Reachable b y := by
        intro hby
        exact hay (hab.trans hby)
      exact hp.not_mem_edges_of_not_reachable hay hby he

/-- If deleting original bridges disconnects two vertices of a connected graph,
one of those original bridges already disconnects the same two vertices. -/
theorem exists_crossed_bridge_cut
    {V : Type u} (R : SimpleGraph V) (hR : R.Connected)
    (S : Set (Sym2 V)) (hbridges : ∀ e ∈ S, R.IsBridge e) {a b : V}
    (hab : ¬ (R.deleteEdges S).Reachable a b) :
    ∃ e ∈ S, ¬ (R.deleteEdges {e}).Reachable a b := by
  obtain ⟨p, hp⟩ := hR.exists_isPath a b
  obtain ⟨e, heS, hep⟩ := p.exists_mem_edges_of_not_reachable_deleteEdges hab
  exact ⟨e, heS, bridge_on_trail_separates_endpoints R p hp.isTrail hep (hbridges e heS)⟩

end ErdosProblems.PathUpperReduction
