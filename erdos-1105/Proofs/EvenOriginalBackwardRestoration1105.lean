module

public import EvenActualSuffixClassification1105
public import EvenOriginalOneVertexRestoration1105
public import CoreSizeUpper1105
public import Fin13BridgeEqualityCombined

@[expose] public section

/-!
Restore the SAME actual graph along its complete exact
core-deletion certificate. The last d outsiders are classified internally;
the universal cone apex supplies the genuine anchor at every restored head. The full-host caller derives the complete certificate, core clique and apex
membership from actual greatest-core identity and tight ORIGINAL edge count. It assumes neither a favorable deletion order nor an enlarged classification.

Core threshold `d` is distinct from the first threshold `d + 1`;
`SecondCoreCount1105` supplies the transition between the two thresholds.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenOriginalBackwardRestoration1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.CoreSizeUpper1105
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenActualSuffixClassification1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- A genuine universal apex belongs to the actual greatest d-core when that
core has more than d vertices. This needs only cone(M) <= G at the caller;
it does not identify the saturated G with its original cone. -/
theorem universal_apex_mem_actual_core (G : SimpleGraph V) (d : ℕ)
    (S : Finset V) (a : V) (hcore : degreeCore G d = S)
    (hlarge : d < S.card) (hall : ∀ z, z ≠ a → G.Adj z a) : a ∈ S := by
  classical
  by_contra ha
  have hgood : GoodCore G d S := by
    rw [← hcore]
    exact degree_core_good G d
  have hneighbors : ∀ z ∈ S, G.Adj a z := by
    intro z hz
    have hza : z ≠ a := by
      intro h
      exact ha (h ▸ hz)
    exact (hall z hza).symm
  have hinsert : GoodCore G d (insert a S) :=
    insert_good_of_all_neighbors G d S hgood hlarge a hneighbors
  have hsubset := good_subset_core G d (insert a S) hinsert
  have hacore : a ∈ degreeCore G d := hsubset (Finset.mem_insert_self a S)
  exact ha (hcore ▸ hacore)

/-- Classify every actual carrier with at least d outsiders by backward
induction on its COMPLETE certificate. Base cardinality, base contacts and
every restored classification are derived, not supplied. The universal
apex remains in the same contact set throughout the induction. -/
theorem classify_complete_deletion_with_apex (G : SimpleGraph V) (d : ℕ)
    (S T : Finset V) (a : V) (hd : 2 ≤ d)
    (hcertificate : ExactCoreDeletion G d S T)
    (hScard : S.card = d + 3) (hclique : G.IsClique (S : Set V))
    (haS : a ∈ S) (hall : ∀ z, z ≠ a → G.Adj z a)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (houtside : d ≤ (T \ S).card) :
    ∃ C : Finset V, C ⊆ S ∧ C.card = d ∧ a ∈ C ∧
      ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)) := by
  classical
  revert houtside
  induction hcertificate with
  | stop =>
      intro houtside
      simp only [Finset.sdiff_self, Finset.card_empty] at houtside
      omega
  | delete T x hx hxS hdegree tail ih =>
      intro houtside
      have hcurrent : ExactCoreDeletion G d S T :=
        ExactCoreDeletion.delete T x hx hxS hdegree tail
      by_cases hlast : (T \ S).card = d
      · obtain ⟨C, hCS, hCcard, hAdj⟩ :=
          actual_suffix_classification G d S T hd hcurrent hScard hclique hlast hfree
        have hpositive : 0 < (T \ S).card := by rw [hlast]; omega
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hpositive
        obtain ⟨hzT, hzS⟩ := Finset.mem_sdiff.mp hz
        have hza : z ≠ a := by
          intro h
          exact hzS (h.symm ▸ haS)
        have hST : S ⊆ T := certificate_core_subset hcurrent
        have hrel := (hAdj z hzT a (hST haS)).mp (hall z hza)
        have haC : a ∈ C := by
          rcases hrel.2 with hSS | hSC | hCS'
          · exact False.elim (hzS hSS.1)
          · exact hSC.2
          · exact False.elim (hCS'.1 haS)
        exact ⟨C, hCS, hCcard, haC, hAdj⟩
      · have hxOutside : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
        have hcount : ((T.erase x) \ S).card = (T \ S).card - 1 := by
          rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem hxOutside]
        have htailOutside : d ≤ ((T.erase x) \ S).card := by
          rw [hcount]
          omega
        obtain ⟨C, hCS, hCcard, haC, hOld⟩ := ih htailOutside
        have hSTail : S ⊆ T.erase x := certificate_core_subset tail
        have hxTail : x ∉ T.erase x := by
          intro h
          exact (Finset.mem_erase.mp h).1 rfl
        have hxa : G.Adj x a := by
          apply hall x
          intro h
          exact hxS (h.symm ▸ haS)
        have hnewDegree : withinDegree G (insert x (T.erase x)) x = d := by
          rw [Finset.insert_erase hx]
          exact hdegree
        have hRestored :=
          EvenOriginalOneVertexRestoration1105.restore_old_join_one_vertex
            G d S C (T.erase x) x a hd hSTail hScard hCS hCcard
            htailOutside hxTail haC hxa hnewDegree hfree hOld
        rw [Finset.insert_erase hx] at hRestored
        exact ⟨C, hCS, hCcard, haC, hRestored⟩

/-- Actual full-host structural endpoint. The supplied data are the actual
greatest core, its forced size, ORIGINAL tight edge count, ambient cycle
freedom and genuine universal apex. Complete deletion, core clique, last
block, contact set and all restorations are derived internally. -/
theorem classify_tight_actual_core_with_apex (G : SimpleGraph V) (d : ℕ)
    (S : Finset V) (a : V) (hd : 2 ≤ d)
    (hcore : degreeCore G d = S) (hScard : S.card = d + 3)
    (htight : Nat.card G.edgeSet =
      S.card.choose 2 + d * (Nat.card V - S.card))
    (houtside : d ≤ Nat.card V - S.card)
    (hall : ∀ z, z ≠ a → G.Adj z a)
    (hfree : (cycleGraph (2 * d + 3)).Free G) :
    ∃ C : Finset V, C ⊆ S ∧ C.card = d ∧ a ∈ C ∧
      ∀ u v, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)) := by
  classical
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  have hcertificate : ExactCoreDeletion G d S Finset.univ :=
    exact_core_deletion_of_tight_nonempty_core G d S hcore hSnonempty htight
  have hOutsideCard : ((Finset.univ : Finset V) \ S).card = Nat.card V - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hEdgesCard : (withinEdges G Finset.univ).card = Nat.card G.edgeSet := by
    have hEdges : withinEdges G Finset.univ = G.edgeFinset := by
      ext e
      simp [withinEdges]
    rw [hEdges, Nat.card_eq_fintype_card, G.card_edgeSet]
  have hLedger := certificate_edge_ledger hcertificate
  rw [hEdgesCard, hOutsideCard] at hLedger
  have hCoreEdges : (withinEdges G S).card = S.card.choose 2 := by
    rw [htight] at hLedger
    omega
  have hInducedCard : (G.induce (S : Set V)).edgeFinset.card =
      (Fintype.card (S : Set V)).choose 2 := by
    have hcardS : Fintype.card (S : Set V) = S.card :=
      Fintype.card_of_finset' (p := (S : Set V)) S (fun _ => Iff.rfl)
    rw [hcardS, ← hCoreEdges]
    have hlift := EvenInducedCarrier1105.withinEdges_lift_card G S S (Finset.Subset.refl S)
    rw [EvenInducedCarrier1105.liftSupport_self] at hlift
    refine Eq.trans ?_ hlift
    unfold withinEdges
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.subset_univ, and_true, mem_edgeFinset]
  have hInducedTop : G.induce (S : Set V) = ⊤ := by
    apply SimpleGraph.edgeFinset_inj.mp
    apply Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    exact hInducedCard.ge
  have hClique : G.IsClique (S : Set V) := by
    intro u hu v hv huv
    have hSubtypeNe : (⟨u, hu⟩ : (S : Set V)) ≠ ⟨v, hv⟩ := by
      intro h
      exact huv (congrArg (fun z : (S : Set V) => z.val) h)
    have hAdj : (G.induce (S : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
      rw [hInducedTop]
      exact hSubtypeNe
    exact hAdj
  have haS : a ∈ S := universal_apex_mem_actual_core G d S a hcore
    (by rw [hScard]; omega) hall
  have hOutsideFinset : d ≤ ((Finset.univ : Finset V) \ S).card := by
    rw [hOutsideCard]
    exact houtside
  obtain ⟨C, hCS, hCcard, haC, hAdj⟩ :=
    classify_complete_deletion_with_apex G d S Finset.univ a hd hcertificate
      hScard hClique haS hall hfree hOutsideFinset
  refine ⟨C, hCS, hCcard, haC, ?_⟩
  intro u v
  exact hAdj u (Finset.mem_univ u) v (Finset.mem_univ v)

end ErdosProblems.PathUpperReduction.EvenOriginalBackwardRestoration1105
