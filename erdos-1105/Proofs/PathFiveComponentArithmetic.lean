module

public import PathFiveComponentSums
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
An exact numerical reduction from component edge bounds to the global edge
bound. This module does not use `P₅`-freeness; that enters in the successor.
-/

namespace ErdosProblems.AntiRamseyPathFiveComponents

open SimpleGraph

/-- A component on at most three vertices has at most one edge per vertex. -/
theorem small_component_edge_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : Fintype.card V ≤ 3) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  have hchoose := G.card_edgeFinset_le_card_choose_two
  have hlimit : (Fintype.card V).choose 2 ≤ Fintype.card V := by
    interval_cases hcard : Fintype.card V <;> norm_num at *
  exact hchoose.trans hlimit

/-- If all components with at least five vertices and all four-vertex
components satisfy `edges ≤ vertices`, so does the whole graph. -/
theorem edge_le_vertex_of_component_bounds {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlarge : ∀ C : G.ConnectedComponent,
      5 ≤ Fintype.card C.supp →
      Nat.card C.toSimpleGraph.edgeSet ≤ Fintype.card C.supp)
    (hfour : ∀ C : G.ConnectedComponent,
      Fintype.card C.supp = 4 → Nat.card C.toSimpleGraph.edgeSet ≤ 4) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  rw [edge_card_eq_sum_component_edge_card G,
    vertex_card_eq_sum_component_card G]
  apply Finset.sum_le_sum
  intro C _
  by_cases h5 : 5 ≤ Fintype.card C.supp
  · exact hlarge C h5
  by_cases h4 : Fintype.card C.supp = 4
  · simpa [h4] using hfour C h4
  have hsmall : Fintype.card C.supp ≤ 3 := by omega
  have hcardSupp : Fintype.card C = Fintype.card C.supp :=
    Fintype.card_congr (Equiv.refl _)
  have hsmallC : Fintype.card C ≤ 3 := by
    rw [hcardSupp]
    exact hsmall
  have hcard : Nat.card C.toSimpleGraph.edgeSet = C.toSimpleGraph.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact C.toSimpleGraph.card_edgeSet
  rw [hcard]
  rw [← hcardSupp]
  exact small_component_edge_le_card C.toSimpleGraph hsmallC

end ErdosProblems.AntiRamseyPathFiveComponents
