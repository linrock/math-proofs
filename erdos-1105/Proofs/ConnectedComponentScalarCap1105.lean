module

public import ConnectedPathBoundChecked1105
public import PathLemmaFourEnvelopeV2
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
Actual finite connected-head adapter for the original middle-component caller. The path copy supplies the lower carrier cardinality; the carrier-size equality
case uses the complete-graph edge bound. Otherwise a faithful graph isomorphism
transports the SAME graph to the checked Fin-carrier connected path bound.
-/

noncomputable section
namespace ErdosProblems.PathUpperReduction.ComponentScalarCap1105

open SimpleGraph
open ErdosProblems.PathLemmaFourEnvelope (scalarCap h)
open ErdosProblems.PathUpperReduction.CoreEndpointBound1105 (extremalCount)

theorem connected_component_scalar_cap {V : Type*} [Finite V]
    (a : ℕ) (ha : 4 ≤ a) (G : SimpleGraph V)
    (f : (pathGraph a).Copy G)
    (hfree : (pathGraph (a + 1)).Free G) (hconn : G.Connected) :
    Nat.card G.edgeSet ≤ scalarCap a (Nat.card V) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hav : a ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (fun x : Fin a => f x) f.injective
  by_cases hva : Fintype.card V = a
  · have hb : Nat.card G.edgeSet ≤ (Fintype.card V).choose 2 := by
      simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
        G.card_edgeFinset_le_card_choose_two
    simpa only [Nat.card_eq_fintype_card, scalarCap, ite_eq_left hva.le] using hb
  · have hn : a + 1 ≤ Fintype.card V := by omega
    have hnotle : ¬Fintype.card V ≤ a := by omega
    let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e.symm
    let i : H ≃g G := SimpleGraph.Iso.comap e.symm G
    have hc : H.Connected := i.connected_iff.mpr hconn
    have hf : (pathGraph (a + 1)).Free H :=
      (SimpleGraph.free_congr_right i).mpr hfree
    have hb :=
      ConnectedPathBoundChecked1105.connected_path_free_edge_bound
        H (by omega) hn hc hf
    have he : Nat.card H.edgeSet = Nat.card G.edgeSet :=
      Nat.card_congr i.mapEdgeSet
    rw [he] at hb
    have hm1 : a + 1 - 1 = a := by omega
    have hm2 : a + 1 - 2 = a - 1 := by omega
    simpa only [Nat.card_eq_fintype_card, scalarCap, ite_eq_right hnotle,
      h, extremalCount, hm1, hm2] using hb

end ErdosProblems.PathUpperReduction.ComponentScalarCap1105
