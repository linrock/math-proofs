module

public import PathUpperOriginalResidualStage
public import PathUpperBridgeComponentCountV2
public import PathFiveComponentSums

@[expose] public section

/-!
Residual piece stage caller. Stage palette/actual bridges and
count are derived from the SAME original r/U/W/whole X. Retained supports are
the ACTUAL deleted graph components, including isolates. No desired count,
partition, rainbow/splice or family-closure premise is supplied.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- Actual original induced graph after literal original bridge-owner cuts. -/
def OriginalResidualRetainedGraph
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (X : Set (Fin n)) (B : Finset (Sym2 X)) : SimpleGraph X :=
  ((selectedGraph χ r).induce X).deleteEdges (B : Set (Sym2 X))

/-- Literal host support of an ACTUAL component on the unchanged subtype X. -/
def originalResidualHostPiece
    {X : Set (Fin n)} {D : SimpleGraph X} (C : D.ConnectedComponent) : Set (Fin n) :=
  Subtype.val '' C.supp

/-- Derive actual support partition, connectivity, positive sizes and total size.
The generic vertex sum is reused from PathFiveComponentSums, not reproved. -/
theorem original_residual_actual_component_piece_facts
    (X : Set (Fin n)) (D : SimpleGraph X) :
    letI : DecidablePred (fun v : Fin n => v ∈ X) := Classical.decPred _
    letI : DecidableRel D.Adj := Classical.decRel _
    (∀ C : D.ConnectedComponent, originalResidualHostPiece C ⊆ X) ∧
    (∀ C : D.ConnectedComponent, (originalResidualHostPiece C).Nonempty) ∧
    (Pairwise fun C E : D.ConnectedComponent =>
      Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E)) ∧
    (⋃ C : D.ConnectedComponent, originalResidualHostPiece C) = X ∧
    (∀ C : D.ConnectedComponent, C.toSimpleGraph.Connected) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card C.supp) ∧
    (∑ C : D.ConnectedComponent, Nat.card C.supp) = Nat.card X ∧
    (∀ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C) = Nat.card C.supp) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card (originalResidualHostPiece C)) ∧
    (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) = Nat.card X := by
  classical
  let : DecidablePred (fun v : Fin n => v ∈ X) := Classical.decPred _
  let : DecidableRel D.Adj := Classical.decRel _
  have hpositive : ∀ C : D.ConnectedComponent, 0 < Nat.card C.supp := by
    intro C
    obtain ⟨w, hw⟩ := C.nonempty_supp
    let : Nonempty C.supp := ⟨⟨w, hw⟩⟩
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hsum : (∑ C : D.ConnectedComponent, Nat.card C.supp) = Nat.card X := by
    have h := ErdosProblems.AntiRamseyPathFiveComponents.vertex_card_eq_sum_component_card D
    simpa only [← Nat.card_eq_fintype_card] using h.symm
  have hhost : ∀ C : D.ConnectedComponent,
      Nat.card (originalResidualHostPiece C) = Nat.card C.supp := by
    intro C
    exact Nat.card_image_of_injective Subtype.val_injective C.supp
  refine ⟨?_, ?_, ?_, ?_, ?_, hpositive, hsum, hhost, ?_, ?_⟩
  · intro C v hv
    obtain ⟨w, _hw, rfl⟩ := hv
    exact w.property
  · intro C
    obtain ⟨w, hw⟩ := C.nonempty_supp
    exact ⟨w.val, w, hw, rfl⟩
  · intro C E hCE
    apply Set.disjoint_left.mpr
    intro v hvC hvE
    obtain ⟨c, hc, hcv⟩ := hvC
    obtain ⟨e, he, hev⟩ := hvE
    have hce : c = e := Subtype.ext (hcv.trans hev.symm)
    exact (Set.disjoint_left.mp (D.pairwise_disjoint_supp_connectedComponent hCE))
      hc (hce.symm ▸ he)
  · ext v
    constructor
    · intro hv
      obtain ⟨C, hvC⟩ := Set.mem_iUnion.mp hv
      obtain ⟨w, _hw, rfl⟩ := hvC
      exact w.property
    · intro hv
      let w : X := ⟨v, hv⟩
      apply Set.mem_iUnion.mpr
      refine ⟨D.connectedComponentMk w, w, ?_, rfl⟩
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  · intro C
    exact C.connected_toSimpleGraph
  · intro C
    rw [hhost C]
    exact hpositive C
  · calc
      (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
          ∑ C : D.ConnectedComponent, Nat.card C.supp := by
        apply Finset.sum_congr rfl
        intro C _
        exact hhost C
      _ = Nat.card X := hsum

/-- One actual stage returns its original palette/bridges and ACTUAL retained
pieces, with exact count, positive sizes and unchanged whole-component total. -/
theorem exists_original_residual_actual_retained_pieces
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    ∃ (A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)))
      (B : Finset (Sym2 (componentSupport χ r x))),
    let D := OriginalResidualRetainedGraph χ r (componentSupport χ r x) B
    letI : DecidablePred (fun v : Fin n => v ∈ componentSupport χ r x) := Classical.decPred _
    letI : DecidableRel D.Adj := Classical.decRel _
    B.card = A.card ∧
    (B : Set (Sym2 (componentSupport χ r x))) =
      OriginalResidualColorDeletion χ r U (componentSupport χ r x)
        (A : Set (EligibleInteriorColor χ U (componentSupport χ r x))) ∧
    (B : Set (Sym2 (componentSupport χ r x))) ⊆
      ((selectedGraph χ r).induce (componentSupport χ r x)).edgeSet ∧
    (∀ b ∈ B, ((selectedGraph χ r).induce (componentSupport χ r x)).IsBridge b) ∧
    (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
      c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) → c ∈ A) ∧
    (∀ (f : HostEdge n), EdgeInside (componentSupport χ r x) f.val → χ f ∉ U →
      ∀ z w : componentSupport χ r x, f.val = s(z.val, w.val) →
      ¬ D.Reachable z w →
      ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x), ⟨χ f, hc⟩ ∈ A) ∧
    (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
      u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
      χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x),
        ⟨χ e, hc⟩ ∈ A) ∧
    ((commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B.Nonempty) ∧
    (¬ (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B = ∅) ∧
    (EligibleResidualOutgoing χ U W (componentSupport χ r x) → B.Nonempty) ∧
    Nat.card D.ConnectedComponent = B.card + 1 ∧
    Nat.card D.ConnectedComponent = A.card + 1 ∧
    (∀ C : D.ConnectedComponent, originalResidualHostPiece C ⊆ componentSupport χ r x) ∧
    (∀ C : D.ConnectedComponent, (originalResidualHostPiece C).Nonempty) ∧
    (Pairwise fun C E : D.ConnectedComponent =>
      Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E)) ∧
    (⋃ C : D.ConnectedComponent, originalResidualHostPiece C) = componentSupport χ r x ∧
    (∀ C : D.ConnectedComponent, C.toSimpleGraph.Connected) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card C.supp) ∧
    (∑ C : D.ConnectedComponent, Nat.card C.supp) =
      Nat.card (componentSupport χ r x) ∧
    (∀ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C) = Nat.card C.supp) ∧
    (∀ C : D.ConnectedComponent, 0 < Nat.card (originalResidualHostPiece C)) ∧
    (∑ C : D.ConnectedComponent, Nat.card (originalResidualHostPiece C)) =
      Nat.card (componentSupport χ r x) := by
  classical
  let X := componentSupport χ r x
  let R := (selectedGraph χ r).induce X
  obtain ⟨hR, A, B, hBA, hBset, hBedges, hBbridges, hseed, hcover, hout, hne, hempty, houtne⟩ :=
    exists_original_residual_stage_bridge_edges χ r U W hpartition x hcomponent hmax
  let D := OriginalResidualRetainedGraph χ r X B
  let : DecidablePred (fun v : Fin n => v ∈ X) := Classical.decPred _
  let : DecidableRel D.Adj := Classical.decRel _
  have hcountB : Nat.card D.ConnectedComponent = B.card + 1 :=
    connected_component_count_delete_original_bridges R hR B hBedges hBbridges
  have hcountA : Nat.card D.ConnectedComponent = A.card + 1 := by
    rw [hcountB, hBA]
  obtain ⟨hsubset, hnonempty, hdisjoint, hwhole, hconnected, hpositive, hsum,
      hhost, hhostpositive, hhostsum⟩ :=
    original_residual_actual_component_piece_facts X D
  exact ⟨A, B, hBA, hBset, hBedges, hBbridges, hseed, hcover, hout,
    hne, hempty, houtne, hcountB, hcountA, hsubset, hnonempty, hdisjoint,
    hwhole, hconnected, hpositive, hsum, hhost, hhostpositive, hhostsum⟩

theorem original_owner_of_selected_edge
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (e : HostEdge n) (he : e.val ∈ (selectedGraph χ r).edgeSet) :
    e = r.edge (χ e) := by
  rw [selectedGraph_edgeSet] at he
  obtain ⟨c, hc⟩ := he
  have howner : e = r.edge c := Subtype.ext hc.symm
  have hcolor : χ e = c := (congrArg χ howner).trans (r.color_eq c)
  rw [hcolor]
  exact howner

/-- Every literal original retained edge avoids U and ALL stage cut colors.
The exact B-to-original-slot equality is derived by the public stage caller. -/
theorem original_retained_edge_color_outside_removed_and_cut
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (X : Set (Fin n)) (hXW : X ⊆ W)
    (A : Finset (EligibleInteriorColor χ U X)) (B : Finset (Sym2 X))
    (hBset : (B : Set (Sym2 X)) = OriginalResidualColorDeletion χ r U X (A : Set _))
    (u v : X) (huv : (OriginalResidualRetainedGraph χ r X B).Adj u v)
    (e : HostEdge n) (hval : e.val = s(u.val, v.val)) :
    χ e ∉ U ∧ χ e ∉ A.image (fun c => c.val) := by
  classical
  have hdeleted := SimpleGraph.deleteEdges_adj.mp huv
  have he : e.val ∈ (selectedGraph χ r).edgeSet := by
    rw [hval]
    exact hdeleted.1
  have howner := original_owner_of_selected_edge χ r e he
  have hu : u.val ∈ (r.edge (χ e)).val := by
    rw [← howner, hval]
    exact Sym2.mem_mk_left _ _
  refine ⟨selected_slot_color_not_removed_of_endpoint_in_remaining
    χ r U W hpartition (χ e) u.val hu (hXW u.property), ?_⟩
  intro hcolor
  obtain ⟨c, hcA, hce⟩ := Finset.mem_image.mp hcolor
  have hmap : Sym2.map (fun z : X => z.val) s(u, v) = (r.edge c.val).val := by
    rw [Sym2.map_mk, ← hval, hce, ← howner]
  have hBmem : s(u, v) ∈ (B : Set (Sym2 X)) := by
    rw [hBset]
    exact ⟨c, hcA, hmap⟩
  exact hdeleted.2 hBmem

/-- Every selected original later edge wholly outside the WHOLE X avoids U
and ALL stage A colors. A owners remain wholly in X, not just in two paths. -/
theorem original_later_selected_edge_color_outside_removed_and_cut
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)))
    (e : HostEdge n) (he : e.val ∈ (selectedGraph χ r).edgeSet)
    (hlater : EdgeInside (W \ componentSupport χ r x) e.val) :
    χ e ∉ U ∧ χ e ∉ A.image (fun c => c.val) := by
  classical
  let X := componentSupport χ r x
  have howner := original_owner_of_selected_edge χ r e he
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.val
  have hu : u ∈ e.val := by
    rw [← huv]
    exact Sym2.mem_mk_left _ _
  have huW : u ∈ W := (hlater u hu).1
  have huNotX : u ∉ X := (hlater u hu).2
  have huOwner : u ∈ (r.edge (χ e)).val := by rw [← howner]; exact hu
  refine ⟨selected_slot_color_not_removed_of_endpoint_in_remaining
    χ r U W hpartition (χ e) u huOwner huW, ?_⟩
  intro hcolor
  obtain ⟨c, _hcA, hce⟩ := Finset.mem_image.mp hcolor
  have hinside := selected_edge_inside_of_eligibleInterior_color
    χ r U W hpartition x hcomponent hmax c.val c.property
  have huSlot : u ∈ (r.edge c.val).val := by
    rw [hce, ← howner]
    exact hu
  exact huNotX (hinside u huSlot)

end ErdosProblems.PathUpperReduction
