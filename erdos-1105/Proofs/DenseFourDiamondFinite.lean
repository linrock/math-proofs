module

public import DenseFourDiamond
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section

/-!
Transport the six-edge finite diamond fact through a graph isomorphism,
then through a connected-component inclusion. This is the form needed by a
selected representative graph on `Fin n`.
-/

namespace ErdosProblems.AntiRamseyPathFiveDiamond

open SimpleGraph

/-- Any four-vertex finite graph with at least five edges has an injective
five-edge diamond, regardless of its carrier type. -/
theorem dense_four_has_diamond_finite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : Fintype.card V = 4) (hfive : 5 ≤ G.edgeFinset.card) :
    ∃ u : Fin 4 → V, Function.Injective u ∧
      G.Adj (u 0) (u 2) ∧ G.Adj (u 0) (u 3) ∧
      G.Adj (u 1) (u 2) ∧ G.Adj (u 1) (u 3) ∧
      G.Adj (u 2) (u 3) := by
  classical
  let H : SimpleGraph (Fin 4) := G.overFin hfour
  let e : G ≃g H := G.overFinIso hfour
  have hH : 5 ≤ H.edgeFinset.card := by
    have hcard : G.edgeFinset.card = H.edgeFinset.card := e.card_edgeFinset_eq
    omega
  obtain ⟨w, hw, h02, h03, h12, h13, h23⟩ := dense_four_has_diamond H hH
  let u : Fin 4 → V := fun i => e.symm (w i)
  have hu : Function.Injective u := e.symm.injective.comp hw
  refine ⟨u, hu, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | exact e.symm.map_adj_iff.mpr h02
    | exact e.symm.map_adj_iff.mpr h03
    | exact e.symm.map_adj_iff.mpr h12
    | exact e.symm.map_adj_iff.mpr h13
    | exact e.symm.map_adj_iff.mpr h23

/-- The five diamond adjacencies of a dense four-vertex component also hold
in its parent graph. -/
theorem dense_component_has_diamond {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : G.ConnectedComponent)
    (hfour : Fintype.card C.supp = 4)
    (hfive : 5 ≤ Nat.card C.toSimpleGraph.edgeSet) :
    ∃ u : Fin 4 → Fin n, Function.Injective u ∧
      G.Adj (u 0) (u 2) ∧ G.Adj (u 0) (u 3) ∧
      G.Adj (u 1) (u 2) ∧ G.Adj (u 1) (u 3) ∧
      G.Adj (u 2) (u 3) := by
  classical
  have hcardSupp : Fintype.card C = Fintype.card C.supp :=
    Fintype.card_congr (Equiv.refl _)
  have hfourC : Fintype.card C = 4 := hcardSupp.trans hfour
  have hcard : Nat.card C.toSimpleGraph.edgeSet = C.toSimpleGraph.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact C.toSimpleGraph.card_edgeSet
  have hfive' : 5 ≤ C.toSimpleGraph.edgeFinset.card := by omega
  obtain ⟨w, hw, h02, h03, h12, h13, h23⟩ :=
    dense_four_has_diamond_finite C.toSimpleGraph hfourC hfive'
  let u : Fin 4 → Fin n := fun i => (w i).val
  have hu : Function.Injective u := Subtype.val_injective.comp hw
  refine ⟨u, hu, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | exact C.toSimpleGraph_hom.map_adj h02
    | exact C.toSimpleGraph_hom.map_adj h03
    | exact C.toSimpleGraph_hom.map_adj h12
    | exact C.toSimpleGraph_hom.map_adj h13
    | exact C.toSimpleGraph_hom.map_adj h23

end ErdosProblems.AntiRamseyPathFiveDiamond
