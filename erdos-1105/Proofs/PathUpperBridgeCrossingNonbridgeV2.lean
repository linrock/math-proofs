module

public import PathUpperBridgeCutTransferV2

@[expose] public section

/-!
A connected retained graph transfers an original
bridge cut into a supergraph. An actual additional edge across that original
cut prevents the original pair from being a bridge in the supergraph.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

universe w

/-- A distinct actual supergraph edge across the original bridge cut makes
the retained original pair nonbridge. No finite carrier or current/supergraph
bridge, deletion equivalence, alternate walk or extra connectivity premise
is assumed. -/
theorem not_isBridge_of_crossing_extra_edge
    {V : Type w} (R D Q : SimpleGraph V) {u v a b : V}
    (hR : R.Connected) (hRb : R.Adj u v)
    (hbR : R.IsBridge s(u, v))
    (hD : D.Connected) (hDb : D.Adj u v)
    (hrespect : ∀ {x y : V}, D.Adj x y →
      s(x, y) ≠ s(u, v) →
      (R.deleteEdges {s(u, v)}).Reachable x y)
    (hDQ : D ≤ Q) (habQ : Q.Adj a b)
    (hne : s(a, b) ≠ s(u, v))
    (hcross : ¬ (R.deleteEdges {s(u, v)}).Reachable a b) :
    ¬ Q.IsBridge s(u, v) := by
  intro hbQ
  have hQ : Q.Connected := SimpleGraph.Connected.mono hDQ hD
  have hQb : Q.Adj u v := hDQ hDb
  have hrespectQ : ∀ {x y : V}, D.Adj x y →
      s(x, y) ≠ s(u, v) →
      (Q.deleteEdges {s(u, v)}).Reachable x y := by
    intro x y hxy hxyne
    have hadj : (Q.deleteEdges {s(u, v)}).Adj x y :=
      SimpleGraph.deleteEdges_adj.mpr
        ⟨hDQ hxy, by simpa only [Set.mem_singleton_iff] using hxyne⟩
    exact hadj.reachable
  have hcutR := bridge_cut_component_transfer R D hR hRb hbR hD hDb hrespect
  have hcutQ := bridge_cut_component_transfer Q D hQ hQb hbQ hD hDb hrespectQ
  have hsurviving : (Q.deleteEdges {s(u, v)}).Adj a b :=
    SimpleGraph.deleteEdges_adj.mpr
      ⟨habQ, by simpa only [Set.mem_singleton_iff] using hne⟩
  exact hcross ((hcutR a b).mp ((hcutQ a b).mpr hsurviving.reachable))

end ErdosProblems.PathUpperReduction
