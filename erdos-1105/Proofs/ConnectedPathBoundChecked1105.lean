module

public import GraphCoreBound1105
public import UniformConeStructure1105
public import ConnectedPathScalarChecked1105

@[expose] public section

/-!
Apply the cycle count to the SAME cone of the actual connected path-free
graph. This ordinary edge bound is not an anti-Ramsey color bound and supplies
no equality classification or induction hypothesis. The imported graph cap
retains every long cycle exclusion and actual deletion-connectedness.
-/

noncomputable section
namespace ErdosProblems.PathUpperReduction.ConnectedPathBoundChecked1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.UniformCone1105 (cone)
open ErdosProblems.PathUpperReduction.CoreEndpointBound1105 (extremalCount)

theorem connected_path_free_edge_bound {n k : ℕ} (G : SimpleGraph (Fin n))
    (hk : 5 ≤ k) (hkn : k ≤ n) (hG : G.Connected)
    (hfree : (pathGraph k).Free G) :
    Nat.card G.edgeSet ≤ max (extremalCount n (k - 1) 1)
      (extremalCount n (k - 1) ((k - 2) / 2)) := by
  classical
  have hc := UniformConeStructure1105.finite_connected_path_free_cone
    G hk hkn hG hfree
  have hN : Fintype.card (Option (Fin n)) = n + 1 := by simp
  have hbound := GraphCoreBound1105.long_cycle_free_edge_bound
    (cone G) (K := k + 1) (by omega) (by simpa only [hN] using Nat.add_le_add_right hkn 1)
    hc.2.2.1 (by
      intro z
      exact hc.2.1 z)
  rw [hN] at hbound
  have hcount : Nat.card (cone G).edgeSet = Nat.card G.edgeSet + n := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using hc.2.2.2
  rw [hcount, Nat.add_comm (Nat.card G.edgeSet) n] at hbound
  exact (ConnectedPathScalarChecked1105.cone_endpoint_bound_iff n k
    (Nat.card G.edgeSet) hk hkn).mp hbound

end ErdosProblems.PathUpperReduction.ConnectedPathBoundChecked1105
