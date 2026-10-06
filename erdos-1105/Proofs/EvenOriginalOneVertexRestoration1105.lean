module

public import EvenRestorationSupport1105
public import EvenFiniteCarrierAdapter1105
public import EvenInducedCarrier1105
public import EvenRestorationLedger1105

@[expose] public section

/-!
Compose the internally selected actual neighbor support,
the actual unordered restoration ledger, the induced-carrier transports and
the generic finite contact classifier. The old join is an induction premise;
no favorable new support, contact set, count or classification is supplied.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.EvenOriginalOneVertexRestoration1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenFiniteCarrierAdapter1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- Restore one actual vertex into the SAME ambient original graph. The old
classified carrier is legitimate induction data. The actual new degree,
anchor and ambient cycle freedom derive the enlarged block classification. -/
theorem restore_old_join_one_vertex (G : SimpleGraph V) (d : ℕ)
    (S C T : Finset V) (x a : V) (hd : 2 ≤ d)
    (hST : S ⊆ T) (hScard : S.card = d + 3)
    (hCS : C ⊆ S) (hCcard : C.card = d)
    (houtside : d ≤ (T \ S).card) (hx : x ∉ T)
    (ha : a ∈ C) (hxa : G.Adj x a)
    (hdegree : withinDegree G (insert x T) x = d)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (hOldAdj : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C))) :
    ∀ u ∈ insert x T, ∀ v ∈ insert x T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)) := by
  classical
  obtain ⟨L, hLO, hLcard, _hOutsideCapture, hCapture, hWcard, hWdegree⟩ :=
    EvenRestorationSupport1105.exists_actual_restoration_support
      G d S T x a hd hST hScard houtside hx (hCS ha) hxa hdegree
  let W : Finset V := insert x (S ∪ L)
  let H : SimpleGraph (W : Set V) := G.induce (W : Set V)
  let S' := EvenInducedCarrier1105.liftSupport W S
  let C' := EvenInducedCarrier1105.liftSupport W C
  have hLT : L ⊆ T := fun y hy => (Finset.mem_sdiff.mp (hLO hy)).1
  have hSW : S ⊆ W := by
    intro y hy
    exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl hy))
  have hCW : C ⊆ W := hCS.trans hSW
  have hxW : x ∈ W := Finset.mem_insert_self _ _
  let x' : (W : Set V) := ⟨x, hxW⟩
  have hmemS (u : (W : Set V)) : u ∈ S' ↔ u.val ∈ S := by
    exact EvenInducedCarrier1105.mem_liftSupport W S u
  have hmemC (u : (W : Set V)) : u ∈ C' ↔ u.val ∈ C := by
    exact EvenInducedCarrier1105.mem_liftSupport W C u
  have hN : Fintype.card (W : Set V) = 2 * d + 3 := by
    exact (EvenInducedCarrier1105.induced_carrier_card W).trans hWcard
  have hS'card : S'.card = d + 3 := by
    exact (EvenInducedCarrier1105.liftSupport_card W S hSW).trans hScard
  have hC'card : C'.card = d := by
    exact (EvenInducedCarrier1105.liftSupport_card W C hCW).trans hCcard
  have hOldClique : G.IsClique (S : Set V) := by
    intro u hu v hv huv
    exact (hOldAdj u (hST hu) v (hST hv)).mpr ⟨huv, Or.inl ⟨hu, hv⟩⟩
  have hClique : H.IsClique (S' : Set (W : Set V)) :=
    EvenInducedCarrier1105.clique_lift G W S hOldClique
  have hFree : (cycleGraph (2 * d + 3)).Free H :=
    EvenInducedCarrier1105.cycle_free_induce G W (2 * d + 3) hfree
  have hOutDegree : ∀ u : (W : Set V), u ∉ S' → d ≤ H.degree u := by
    intro u huS'
    have huS : u.val ∉ S := fun hu => huS' ((hmemS u).mpr hu)
    change d ≤ (G.induce (W : Set V)).degree u
    rw [EvenInducedCarrier1105.degree_induce_eq_withinDegree G W u]
    by_cases hux : u.val = x
    · rw [hux]
      exact hWdegree.ge
    · have huL : u.val ∈ L := by
        have huW : u.val ∈ insert x (S ∪ L) := u.property
        rcases Finset.mem_insert.mp huW with hux' | huSL
        · exact False.elim (hux hux')
        · rcases Finset.mem_union.mp huSL with huS' | huL
          · exact False.elim (huS huS')
          · exact huL
      have hCN : C ⊆ W.filter (fun c => G.Adj u.val c) := by
        intro c hc
        have hcS : c ∈ S := hCS hc
        have huc : u.val ≠ c := by
          intro h
          apply huS
          rw [h]
          exact hcS
        exact Finset.mem_filter.mpr ⟨hCW hc,
          (hOldAdj u.val (hLT huL) c (hST hcS)).mpr
            ⟨huc, Or.inr (Or.inl ⟨huS, hc⟩)⟩⟩
      change d ≤ (W.filter (fun c => G.Adj u.val c)).card
      rw [← hCcard]
      exact Finset.card_le_card hCN
  have hActualLedger := EvenRestorationLedger1105.restoration_edge_ledgers
    G d S C T L x hd hST hScard hCS hCcard hOldAdj hx hLO hLcard hWdegree
  have hLedger : d * d ≤ (coreCrossEdges H S' Finset.univ).card +
      (withinEdges H (Finset.univ \ S')).card := by
    have hTransport := EvenInducedCarrier1105.suffix_ledger_induce G W S hSW
    change (coreCrossEdges H S' Finset.univ).card +
      (withinEdges H (Finset.univ \ S')).card =
      (coreCrossEdges G S W).card + (withinEdges G (W \ S)).card at hTransport
    rw [hTransport]
    exact hActualLedger.2.ge
  have hsdiffEq : @SDiff.sdiff (Finset (W : Set V))
      (@Finset.instSDiff (W : Set V) (Classical.decEq _)) Finset.univ S' =
      Finset.univ \ S' := by
    ext z; simp only [Finset.mem_sdiff]
  rw [← hsdiffEq] at hLedger
  obtain ⟨hDcard, _hDS, _hThree, _hOutsideCard, hAdj⟩ :=
    actual_finite_contact_rigidity (by omega : 1 ≤ d) H hN S'
      hS'card hClique hOutDegree hFree hLedger
  have hLpos : 0 < L.card := by rw [hLcard]; omega
  obtain ⟨z, hzL⟩ := Finset.card_pos.mp hLpos
  have hzS : z ∉ S := (Finset.mem_sdiff.mp (hLO hzL)).2
  have hzW : z ∈ W := Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inr hzL))
  have hCD : C' ⊆ actualContacts H S' := by
    intro c hc
    have hcC : c.val ∈ C := (hmemC c).mp hc
    have hcS : c.val ∈ S := hCS hcC
    have hzc : z ≠ c.val := by
      intro h
      apply hzS
      rw [h]
      exact hcS
    apply (EvenInducedCarrier1105.actualContacts_lift_iff G W S c).mpr
    refine ⟨hcS, z, hzW, hzS, ?_⟩
    exact (hOldAdj z (hLT hzL) c.val (hST hcS)).mpr
      ⟨hzc, Or.inr (Or.inl ⟨hzS, hcC⟩)⟩
  have hDEq : actualContacts H S' = C' := by
    apply (Finset.eq_of_subset_of_card_le hCD ?_).symm
    rw [hDcard, hC'card]
  rw [hDEq] at hAdj
  have hxS' : x' ∉ S' := fun h => hx (hST ((hmemS x').mp h))
  have hxC' : x' ∉ C' := fun h => hx (hST (hCS ((hmemC x').mp h)))
  have hNewAdj (v : V) (hvT : v ∈ T) : G.Adj x v ↔ v ∈ C := by
    constructor
    · intro hxv
      have hvW : v ∈ W := hCapture v (Finset.mem_insert_of_mem hvT) hxv
      let v' : (W : Set V) := ⟨v, hvW⟩
      have hSmall : H.Adj x' v' := by change G.Adj x v; exact hxv
      have h := (hAdj x' v').mp hSmall
      rcases h.2 with hSS | hXC | hVC
      · exact False.elim (hxS' hSS.1)
      · exact (hmemC v').mp hXC.2
      · exact False.elim (hxC' hVC.2)
    · intro hvC
      let v' : (W : Set V) := ⟨v, hCW hvC⟩
      have hxv' : x' ≠ v' := by
        intro h
        have hval : x = v := congrArg (fun u : (W : Set V) => u.val) h
        apply hx
        rw [hval]
        exact hvT
      have hSmall : H.Adj x' v' := (hAdj x' v').mpr
        ⟨hxv', Or.inr (Or.inl ⟨hxS', (hmemC v').mpr hvC⟩)⟩
      exact hSmall
  have hxS : x ∉ S := fun h => hx (hST h)
  have hxC : x ∉ C := fun h => hx (hST (hCS h))
  intro u hu v hv
  rcases Finset.mem_insert.mp hu with hux | huT
  · subst u
    rcases Finset.mem_insert.mp hv with hvx | hvT
    · subst v
      simp
    · have hxv : x ≠ v := by rintro rfl; exact hx hvT
      simpa only [ne_eq, hxS, hxC, hxv, not_false_eq_true, false_and, true_and,
        and_false, or_false, false_or] using hNewAdj v hvT
  · rcases Finset.mem_insert.mp hv with hvx | hvT
    · subst v
      have hux : u ≠ x := by rintro rfl; exact hx huT
      have huxAdj : G.Adj u x ↔ u ∈ C := by
        constructor
        · intro h
          exact (hNewAdj u huT).mp h.symm
        · intro h
          exact ((hNewAdj u huT).mpr h).symm
      simpa only [ne_eq, hxS, hxC, hux, not_false_eq_true, and_false, true_and,
        or_false, false_or] using huxAdj
    · exact hOldAdj u huT v hvT

end ErdosProblems.PathUpperReduction.EvenOriginalOneVertexRestoration1105
