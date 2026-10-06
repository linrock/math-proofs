module

public import PathUpperEligibleOriginalClosure
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
Actual residual stage palette SOURCE assembly, including the empty full-common
branch. Original chi, full r, U/W and the actual whole component are unchanged.
Deletion uses literal ORIGINAL r slots. No desired palette, bridge, closure,
rank, connected arbitrary-choice or component-count premise is supplied.
The generic finite bridge-deletion component-count identity is documented
separately, not assumed by this module.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Zero deletion of a connected actual graph leaves exactly one component,
including the singleton/empty eligible-palette stage. -/
theorem connected_component_count_delete_empty
    {V : Type*} (G : SimpleGraph V) (hG : G.Connected) :
    Nat.card (G.deleteEdges (∅ : Set (Sym2 V))).ConnectedComponent = 1 := by
  rw [deleteEdges_empty]
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨hG.preconnected.subsingleton_connectedComponent,
      Nonempty.map G.connectedComponentMk hG.nonempty⟩

/-- Literal ORIGINAL r-slot deletion on the actual subtype carrier. -/
def OriginalResidualColorDeletion
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (X : Set (Fin n))
    (A : Set (EligibleInteriorColor χ U X)) : Set (Sym2 X) :=
  {b | ∃ c ∈ A, Sym2.map (fun z : X => z.val) b = (r.edge c.val).val}

/-- A selected original slot meeting W cannot have a removed color. -/
theorem selected_slot_color_not_removed_of_endpoint_in_remaining
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (c : Fin q) (v : Fin n) (hv : v ∈ (r.edge c).val) (hvW : v ∈ W) :
    c ∉ U := by
  intro hc
  exact (hpartition.removed_outside c hc v hv) hvW

/-- Actual-stage palette, allowing zero cuts. FULL-common colors are retained;
ALL eligible original inside crossing colors and ALL outgoing colors are
covered by A, with removed U colors allowed only at the outgoing boundary. -/
theorem exists_original_residual_stage_palette
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    ((selectedGraph χ r).induce (componentSupport χ r x)).Connected ∧
    ∃ A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)),
      (∀ c : EligibleInteriorColor χ U (componentSupport χ r x),
        c.val ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) → c ∈ A) ∧
      (∀ c ∈ A, ∀ a b : componentSupport χ r x,
        (r.edge c.val).val = s(a.val, b.val) →
        ((selectedGraph χ r).induce (componentSupport χ r x)).IsBridge s(a, b)) ∧
      (∀ (f : HostEdge n), EdgeInside (componentSupport χ r x) f.val → χ f ∉ U →
        ∀ z w : componentSupport χ r x, f.val = s(z.val, w.val) →
        ¬ (((selectedGraph χ r).induce (componentSupport χ r x)).deleteEdges
          (OriginalResidualColorDeletion χ r U (componentSupport χ r x)
            (A : Set (EligibleInteriorColor χ U (componentSupport χ r x))))).Reachable z w →
        ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x), ⟨χ f, hc⟩ ∈ A) ∧
      (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
        u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
        χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x),
          ⟨χ e, hc⟩ ∈ A) ∧
      ((commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → A.Nonempty) ∧
      (¬ (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → A = ∅) ∧
      (EligibleResidualOutgoing χ U W (componentSupport χ r x) → A.Nonempty) := by
  classical
  let X := componentSupport χ r x
  let C := EligibleInteriorColor χ U X
  let R := (selectedGraph χ r).induce X
  obtain ⟨s₀, hslots, hgraph, hconn, _howners⟩ :=
    exists_connected_eligible_interior_choice χ r U W hpartition x hcomponent hmax
  have hRconn : R.Connected := by
    change ((selectedGraph χ r).induce X).Connected
    rw [← hgraph]
    exact hconn
  have hdelete : ∀ A : Finset C,
      EligibleInteriorColorDeletion χ U X s₀ (A : Set C) =
        OriginalResidualColorDeletion χ r U X (A : Set C) := by
    intro A
    ext e
    change
      (∃ c ∈ (A : Set C), ∃ a b : X,
        (s₀.edge c).val = s(a.val, b.val) ∧ e = s(a, b)) ↔
      ∃ c ∈ (A : Set C),
        Sym2.map (fun z : X => z.val) e = (r.edge c.val).val
    constructor
    · rintro ⟨c, hc, a, b, hslot, rfl⟩
      refine ⟨c, hc, ?_⟩
      rw [Sym2.map_mk, ← hslots c]
      exact hslot.symm
    · rintro ⟨c, hc, hmap⟩
      obtain ⟨a, b⟩ := e
      have hslot : (s₀.edge c).val = s(a.val, b.val) := by
        rw [hslots c]
        simpa only [Sym2.map_mk] using hmap.symm
      exact ⟨c, hc, a, b, hslot, rfl⟩
  obtain ⟨A, hseed, hbridges, hcover, hne, hempty⟩ :
      ∃ A : Finset C,
        (∀ c : C, c.val ∈ commonEligibleInteriorColors χ U X → c ∈ A) ∧
        (∀ c ∈ A, ∀ a b : X, (r.edge c.val).val = s(a.val, b.val) → R.IsBridge s(a, b)) ∧
        (∀ (f : HostEdge n), EdgeInside X f.val → χ f ∉ U →
          ∀ z w : X, f.val = s(z.val, w.val) →
          ¬ (R.deleteEdges (OriginalResidualColorDeletion χ r U X (A : Set C))).Reachable z w →
          ∃ hc : χ f ∈ eligibleInteriorColors χ U X, ⟨χ f, hc⟩ ∈ A) ∧
        ((commonEligibleInteriorColors χ U X).Nonempty → A.Nonempty) ∧
        (¬ (commonEligibleInteriorColors χ U X).Nonempty → A = ∅) := by
    by_cases hfull : (commonEligibleInteriorColors χ U X).Nonempty
    · obtain ⟨_hfamily, A, hseed, hne, hbridges, hcover⟩ :=
        exists_original_residual_eligible_bridge_closure_with_full_common_seed
          χ r U W hpartition x hcomponent s₀ hconn hfull
      refine ⟨A, hseed, ?_, ?_, fun _ => hne, ?_⟩
      · intro c hc a b hslot
        have hs : (s₀.edge c).val = s(a.val, b.val) := by
          rw [hslots c]
          exact hslot
        have hb := hbridges c hc a b hs
        change ((eligibleInteriorSelectedGraph χ U X s₀).induce X).IsBridge s(a, b) at hb
        rw [hgraph] at hb
        exact hb
      · intro f hf hcolor z w hfv hcross
        apply hcover f hf hcolor z w hfv
        change ¬ (((eligibleInteriorSelectedGraph χ U X s₀).induce X).deleteEdges _).Reachable z w
        rw [hgraph, hdelete A]
        exact hcross
      · intro hnone
        exact False.elim (hnone hfull)
    · refine ⟨∅, ?_, ?_, ?_, ?_, fun _ => rfl⟩
      · intro c hc
        exact False.elim (hfull ⟨c.val, hc⟩)
      · intro c hc
        exact False.elim (Finset.notMem_empty c hc)
      · intro f hf hcolor z w hfv hcross
        have hD : OriginalResidualColorDeletion χ r U X (↑(∅ : Finset C)) = ∅ := by
          ext e
          simp [OriginalResidualColorDeletion]
        have hcross' : ¬ R.Reachable z w := by
          simpa only [hD, deleteEdges_empty] using hcross
        exact False.elim (hcross' (hRconn z w))
      · intro hfull'
        exact False.elim (hfull hfull')
  refine ⟨hRconn, A, hseed, hbridges, hcover, ?_, hne, hempty, ?_⟩
  · intro e u y he hu hyW hy
    by_cases hcolor : χ e ∈ U
    · exact Or.inl hcolor
    · have hcFull := eligible_cross_edge_color_mem_commonEligibleInteriorColors
        χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor
      have hcI : χ e ∈ eligibleInteriorColors χ U X := (Finset.mem_filter.mp hcFull).1
      exact Or.inr ⟨hcI, hseed ⟨χ e, hcI⟩ hcFull⟩
  · intro hout
    exact hne (commonEligibleInteriorColors_nonempty_of_eligibleOutgoing
      χ r U W hpartition x hcomponent hmax hout)

/-- Finite actual ORIGINAL bridge-owner set with exact edge/color count.
The exact retained-component count is a separate generic finite graph input;
it is not smuggled into this palette/bridge theorem. -/
theorem exists_original_residual_stage_bridge_edges
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    ((selectedGraph χ r).induce (componentSupport χ r x)).Connected ∧
    ∃ (A : Finset (EligibleInteriorColor χ U (componentSupport χ r x)))
      (B : Finset (Sym2 (componentSupport χ r x))),
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
        ¬ (((selectedGraph χ r).induce (componentSupport χ r x)).deleteEdges (B : Set _)).Reachable z w →
        ∃ hc : χ f ∈ eligibleInteriorColors χ U (componentSupport χ r x), ⟨χ f, hc⟩ ∈ A) ∧
      (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
        u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
        χ e ∈ U ∨ ∃ hc : χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x),
          ⟨χ e, hc⟩ ∈ A) ∧
      ((commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B.Nonempty) ∧
      (¬ (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty → B = ∅) ∧
      (EligibleResidualOutgoing χ U W (componentSupport χ r x) → B.Nonempty) := by
  classical
  let X := componentSupport χ r x
  let C := EligibleInteriorColor χ U X
  let R := (selectedGraph χ r).induce X
  obtain ⟨hRconn, A, hseed, hbridges, hcover, hout, hne, hempty, houtne⟩ :=
    exists_original_residual_stage_palette χ r U W hpartition x hcomponent hmax
  have howners : ∀ c : C, ∃ b : Sym2 X,
      Sym2.map (fun z : X => z.val) b = (r.edge c.val).val := by
    intro c
    have hi := selected_edge_inside_of_eligibleInterior_color
      χ r U W hpartition x hcomponent hmax c.val c.property
    obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective ((r.edge c.val).val)
    have ha : a ∈ X := hi a (by rw [← hab]; exact Sym2.mem_mk_left a b)
    have hb : b ∈ X := hi b (by rw [← hab]; exact Sym2.mem_mk_right a b)
    refine ⟨s((⟨a, ha⟩ : X), (⟨b, hb⟩ : X)), ?_⟩
    change s(a, b) = (r.edge c.val).val at hab
    simpa only [Sym2.map_mk] using hab
  choose owner howner using howners
  have hinj : Function.Injective owner := by
    intro c d hcd
    have hval : (r.edge c.val).val = (r.edge d.val).val := by
      rw [← howner c, ← howner d, hcd]
    have hedge : r.edge c.val = r.edge d.val := Subtype.ext hval
    exact Subtype.ext ((r.color_eq c.val).symm.trans
      ((congrArg χ hedge).trans (r.color_eq d.val)))
  let B : Finset (Sym2 X) := A.image owner
  have hBcard : B.card = A.card := Finset.card_image_of_injective A hinj
  have hBmem : ∀ e : Sym2 X, e ∈ B ↔
      ∃ c ∈ A, Sym2.map (fun z : X => z.val) e = (r.edge c.val).val := by
    intro e
    constructor
    · intro he
      obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp he
      exact ⟨c, hc, hce ▸ howner c⟩
    · rintro ⟨c, hc, hmap⟩
      have hce : owner c = e :=
        Sym2.map.injective (f := fun z : X => z.val) Subtype.val_injective
          ((howner c).trans hmap.symm)
      exact Finset.mem_image.mpr ⟨c, hc, hce⟩
  have hBcoe : (B : Set (Sym2 X)) = OriginalResidualColorDeletion χ r U X (A : Set C) := by
    ext e
    exact hBmem e
  have hBsubset : (B : Set (Sym2 X)) ⊆ R.edgeSet := by
    intro e he
    obtain ⟨a, b⟩ := e
    obtain ⟨c, _hc, hmap⟩ := (hBmem s(a, b)).mp he
    have hslot : (r.edge c.val).val = s(a.val, b.val) := by
      simpa only [Sym2.map_mk] using hmap.symm
    have hselected : s(a.val, b.val) ∈ (selectedGraph χ r).edgeSet := by
      rw [selectedGraph_edgeSet]
      exact ⟨c.val, hslot⟩
    exact hselected
  have hBbridges : ∀ e ∈ B, R.IsBridge e := by
    intro e he
    obtain ⟨a, b⟩ := e
    obtain ⟨c, hc, hmap⟩ := (hBmem s(a, b)).mp he
    have hslot : (r.edge c.val).val = s(a.val, b.val) := by
      simpa only [Sym2.map_mk] using hmap.symm
    exact hbridges c hc a b hslot
  have hBne : A.Nonempty → B.Nonempty := by
    rintro ⟨c, hc⟩
    exact ⟨owner c, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  refine ⟨hRconn, A, B, hBcard, hBcoe, hBsubset, hBbridges, hseed, ?_, hout, ?_, ?_, ?_⟩
  · intro f hf hcolor z w hfv hcross
    apply hcover f hf hcolor z w hfv
    rw [← hBcoe]
    exact hcross
  · intro hfull
    exact hBne (hne hfull)
  · intro hnone
    change A.image owner = ∅
    rw [hempty hnone]
    exact Finset.image_empty owner
  · intro hout'
    exact hBne (houtne hout')

end ErdosProblems.PathUpperReduction
