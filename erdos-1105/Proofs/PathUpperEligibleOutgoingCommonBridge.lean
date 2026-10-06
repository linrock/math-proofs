module

public import PathUpperEligibleInteriorChoice
public import CycleComponentHamiltonianNonbridgeV3

@[expose] public section

/-!
for the outgoing/common bridge palette of an ORIGINAL
eligible residual stage. Every relative replacement is shown admissible
before its residual size comparison. A common nonempty seed is derived only
from an ACTUAL eligible outgoing witness. No incomplete residual host is
replaced by a complete host, and no colored inside-crossing closure is asserted.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Every admissible original-prefix choice inherits the literal U/W partition. -/
theorem OriginalResidualChoice.slotPartition
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {r : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)}
    (t : OriginalResidualChoice χ r U W)
    (hpartition : ResidualSlotPartition χ r U W) :
    ResidualSlotPartition χ t.choice U W where
  removed_outside := by
    intro c hc
    rw [t.prefix_eq c hc]
    exact hpartition.removed_outside c hc
  eligible_inside := t.eligible_inside

/-- Relative residual replacements still fix the SAME original prefix slots. -/
def OriginalResidualChoice.compose
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {r : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)}
    (t : OriginalResidualChoice χ r U W)
    (s : OriginalResidualChoice χ t.choice U W) :
    OriginalResidualChoice χ r U W where
  choice := s.choice
  prefix_eq := by
    intro c hc
    exact (s.prefix_eq c hc).trans (t.prefix_eq c hc)
  eligible_inside := s.eligible_inside

/-- An admissible SAME-X extension inherits the SIZE comparison over the exact
relative original-prefix family. No unrestricted global maximum is inferred. -/
theorem OriginalResidualChoice.sizeMaximum_of_componentSupport_eq
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {r : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)}
    (t : OriginalResidualChoice χ r U W) (x : Fin n)
    (hmax : ResidualLexMaximum χ r U W x)
    (hsupport : componentSupport χ t.choice x = componentSupport χ r x) :
    ∀ (s : OriginalResidualChoice χ t.choice U W) (z : Fin n), z ∈ W →
      (componentSupport χ s.choice z).ncard ≤
        (componentSupport χ t.choice x).ncard := by
  intro s z hz
  have hle := hmax.1 (t.compose s) z hz
  rw [hsupport]
  exact hle

/-- An ORIGINAL eligible X-to-(W∖X) edge has its selected color on a literal
bridge inside the SAME actual component, under just the residual SIZE maximum. -/
theorem eligible_cross_edge_color_is_component_bridge
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hsize : ∀ (t : OriginalResidualChoice χ r U W) (z : Fin n), z ∈ W →
      (componentSupport χ t.choice z).ncard ≤
        (componentSupport χ r x).ncard)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : u ∈ componentSupport χ r x) (hyW : y ∈ W)
    (hy : y ∉ componentSupport χ r x) (hcolor : χ e ∉ U) :
    ∃ a b : Fin n,
      (r.edge (χ e)).val = s(a, b) ∧
      a ∈ componentSupport χ r x ∧ b ∈ componentSupport χ r x ∧
      (selectedGraph χ r).IsBridge s(a, b) := by
  classical
  have hxW : x ∈ W := hcomponent
    ((mem_componentSupport χ r x x).mpr (SimpleGraph.Reachable.refl x))
  have heW : EdgeInside W e.val := by
    rw [he]
    intro v hv
    rcases Sym2.mem_iff.mp hv with hva | hvy
    · rw [hva]
      exact hcomponent hu
    · rw [hvy]
      exact hyW
  let t : OriginalResidualChoice χ r U W :=
    originalResidualReplace χ r U W hpartition e hcolor heW
  have hureach : (selectedGraph χ r).Reachable x u :=
    (mem_componentSupport χ r x u).mp hu
  have hynot : ¬ (selectedGraph χ r).Reachable x y := by
    intro hreach
    exact hy ((mem_componentSupport χ r x y).mpr hreach)
  have hcuts : ∃ v, (selectedGraph χ r).Reachable x v ∧
      ¬ ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v := by
    by_contra h
    push Not at h
    have hlt := replacement_grows_component χ r e x u y he hureach hynot h
    have hle := hsize t x hxW
    exact (Nat.not_lt_of_ge hle) hlt
  obtain ⟨v, hv, hnot⟩ := hcuts
  obtain ⟨a, b, hab, ha, hb⟩ :=
    edge_endpoints_reachable_of_delete_disconnects
      (selectedGraph χ r) (r.edge (χ e)).val hv hnot
  have hbridge : (selectedGraph χ r).IsBridge (r.edge (χ e)).val := by
    by_contra hnb
    exact hnot (reachable_deleteEdge_of_not_bridge
      (selectedGraph χ r) (r.edge (χ e)).val hnb hv)
  exact ⟨a, b, hab, (mem_componentSupport χ r x a).mpr ha,
    (mem_componentSupport χ r x b).mpr hb, hab ▸ hbridge⟩

/-- Every eligible outgoing original color belongs to the ENTIRE eligible
inside palette; neither properness nor nonempty I is used as a witness. -/
theorem eligible_cross_edge_color_mem_eligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : u ∈ componentSupport χ r x) (hyW : y ∈ W)
    (hy : y ∉ componentSupport χ r x) (hcolor : χ e ∉ U) :
    χ e ∈ eligibleInteriorColors χ U (componentSupport χ r x) := by
  obtain ⟨a, b, hab, ha, hb, _hbridge⟩ :=
    eligible_cross_edge_color_is_component_bridge
      χ r U W hpartition x hcomponent hmax.1 e u y he hu hyW hy hcolor
  have hinside : EdgeInside (componentSupport χ r x) (r.edge (χ e)).val := by
    rw [hab]
    intro v hv
    rcases Sym2.mem_iff.mp hv with hva | hvb
    · rw [hva]
      exact ha
    · rw [hvb]
      exact hb
  exact (mem_eligibleInteriorColors χ U (componentSupport χ r x) (χ e)).mpr
    ⟨hcolor, r.edge (χ e), hinside, r.color_eq (χ e)⟩

/-- Literal ORIGINAL eligible colors whose supplied owner is an actual induced bridge. -/
def eligibleInteriorBridgeColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X) : Set (Fin q) :=
  {c | ∃ (hc : c ∈ eligibleInteriorColors χ U X) (a b : X),
    (s.edge ⟨c, hc⟩).val = s(a.val, b.val) ∧
    χ (s.edge ⟨c, hc⟩) = c ∧
    ((eligibleInteriorSelectedGraph χ U X s).induce X).Adj a b ∧
    ((eligibleInteriorSelectedGraph χ U X s).induce X).IsBridge s(a, b)}

/-- Every eligible outgoing ORIGINAL color is an induced bridge color in EVERY
SUPPLIED CONNECTED ENTIRE eligible-I choice on the SAME actual whole X. -/
theorem eligible_cross_edge_color_mem_bridgeColors_of_connected_choice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : u ∈ componentSupport χ r x) (hyW : y ∈ W)
    (hy : y ∉ componentSupport χ r x) (hcolor : χ e ∉ U)
    (s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x))
    (hconn : ((eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
      (componentSupport χ r x)).Connected) :
    χ e ∈ eligibleInteriorBridgeColors χ U (componentSupport χ r x) s := by
  let X := componentSupport χ r x
  have hc : χ e ∈ eligibleInteriorColors χ U X :=
    eligible_cross_edge_color_mem_eligibleInteriorColors
      χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor
  obtain ⟨t, hslots, _hothers, hsupport⟩ :=
    connected_eligible_choice_has_anchored_residual_extension
      χ r U W hpartition x hcomponent s hconn
  have hpartitionT := t.slotPartition hpartition
  have hcomponentT : componentSupport χ t.choice x ⊆ W := by
    rw [hsupport]
    exact hcomponent
  have huT : u ∈ componentSupport χ t.choice x := by
    rw [hsupport]
    exact hu
  have hyT : y ∉ componentSupport χ t.choice x := by
    rw [hsupport]
    exact hy
  have hsizeT := t.sizeMaximum_of_componentSupport_eq x hmax hsupport
  obtain ⟨a, b, hab, ha, hb, hbridge⟩ :=
    eligible_cross_edge_color_is_component_bridge χ t.choice U W
      hpartitionT x hcomponentT hsizeT e u y he huT hyW hyT hcolor
  have haX : a ∈ X := by rw [hsupport] at ha; exact ha
  have hbX : b ∈ X := by rw [hsupport] at hb; exact hb
  have hliteral : (s.edge ⟨χ e, hc⟩).val = s(a, b) := by
    rw [← hslots ⟨χ e, hc⟩]
    exact hab
  have hfulladj : (selectedGraph χ t.choice).Adj a b := by
    have hmem : s(a, b) ∈ (selectedGraph χ t.choice).edgeSet := by
      rw [selectedGraph_edgeSet]
      exact ⟨χ e, hab⟩
    exact hmem
  have hle : eligibleInteriorSelectedGraph χ U X s ≤ selectedGraph χ t.choice := by
    intro z w hzw
    change s(z, w) ∈ Set.range
      (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val) ∧
        z ≠ w at hzw
    obtain ⟨c, hslot⟩ := hzw.1
    have hmem : s(z, w) ∈ (selectedGraph χ t.choice).edgeSet := by
      rw [selectedGraph_edgeSet]
      refine ⟨c.val, ?_⟩
      change (t.choice.edge c.val).val = s(z, w)
      rw [hslots c]
      exact hslot
    exact hmem
  have hinterioradj : (eligibleInteriorSelectedGraph χ U X s).Adj a b := by
    change s(a, b) ∈ Set.range
      (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val) ∧
        a ≠ b
    exact ⟨⟨⟨χ e, hc⟩, hliteral⟩, hfulladj.ne⟩
  have hinteriorbridge : (eligibleInteriorSelectedGraph χ U X s).IsBridge s(a, b) :=
    SimpleGraph.IsBridge.anti hle hbridge
  let aX : X := ⟨a, haX⟩
  let bX : X := ⟨b, hbX⟩
  have hinducedbridge :
      ((eligibleInteriorSelectedGraph χ U X s).induce X).IsBridge s(aX, bX) :=
    ErdosProblems.AntiRamseyCycleComponentHamiltonianNonbridge.isBridge_comap_of_injective
      (eligibleInteriorSelectedGraph χ U X s) (fun z : X => z.val)
      Subtype.val_injective hinteriorbridge
  exact ⟨hc, aX, bX, hliteral, s.color_eq ⟨χ e, hc⟩,
    hinterioradj, hinducedbridge⟩

/-- Full intersection over EVERY CURRENT CONNECTED entire eligible choice. -/
noncomputable def commonEligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n)) :
    Finset (Fin q) := by
  classical
  exact (eligibleInteriorColors χ U X).filter (fun c =>
    ∀ s : EligibleInteriorRepresentativeChoice χ U X,
      ((eligibleInteriorSelectedGraph χ U X s).induce X).Connected →
        c ∈ eligibleInteriorBridgeColors χ U X s)

/-- One ACTUAL eligible outgoing witness; properness alone does not imply it. -/
def EligibleResidualOutgoing
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q))
    (W X : Set (Fin n)) : Prop :=
  ∃ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) ∧
    u ∈ X ∧ y ∈ W ∧ y ∉ X ∧ χ e ∉ U

/-- All eligible outgoing original colors lie in the FULL common bridge intersection. -/
theorem eligible_cross_edge_color_mem_commonEligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : u ∈ componentSupport χ r x) (hyW : y ∈ W)
    (hy : y ∉ componentSupport χ r x) (hcolor : χ e ∉ U) :
    χ e ∈ commonEligibleInteriorColors χ U (componentSupport χ r x) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨eligible_cross_edge_color_mem_eligibleInteriorColors
    χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor, ?_⟩
  intro s hs
  exact eligible_cross_edge_color_mem_bridgeColors_of_connected_choice
    χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor s hs

/-- An actual eligible outgoing edge supplies a nonempty FULL common seed. -/
theorem commonEligibleInteriorColors_nonempty_of_eligibleOutgoing
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (hout : EligibleResidualOutgoing χ U W (componentSupport χ r x)) :
    (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty := by
  obtain ⟨e, u, y, he, hu, hyW, hy, hcolor⟩ := hout
  exact ⟨χ e, eligible_cross_edge_color_mem_commonEligibleInteriorColors
    χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor⟩

/-- Residual outgoing package: derive one connected ENTIRE eligible choice;
cover every eligible outgoing color in the full common seed; keep the exact
empty-outgoing branch and singleton/empty-I control explicit. -/
theorem eligible_residual_outgoing_common_bridge_package
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    (∃ s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x),
      ((eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
        (componentSupport χ r x)).Connected) ∧
    (∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
      u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
      χ e ∉ U →
      χ e ∈ commonEligibleInteriorColors χ U (componentSupport χ r x)) ∧
    (EligibleResidualOutgoing χ U W (componentSupport χ r x) →
      (commonEligibleInteriorColors χ U (componentSupport χ r x)).Nonempty) ∧
    (¬ EligibleResidualOutgoing χ U W (componentSupport χ r x) →
      ∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
        u ∈ componentSupport χ r x → y ∈ W → y ∉ componentSupport χ r x →
        χ e ∈ U) ∧
    (eligibleInteriorColors χ U (componentSupport χ r x) = ∅ →
      ¬ EligibleResidualOutgoing χ U W (componentSupport χ r x)) := by
  classical
  obtain ⟨s, _hslots, _hgraph, hs, _howners⟩ :=
    exists_connected_eligible_interior_choice χ r U W hpartition x hcomponent hmax
  refine ⟨⟨s, hs⟩, ?_, ?_, ?_, ?_⟩
  · intro e u y he hu hyW hy hcolor
    exact eligible_cross_edge_color_mem_commonEligibleInteriorColors
      χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor
  · exact commonEligibleInteriorColors_nonempty_of_eligibleOutgoing
      χ r U W hpartition x hcomponent hmax
  · intro hnone e u y he hu hyW hy
    by_contra hcolor
    exact hnone ⟨e, u, y, he, hu, hyW, hy, hcolor⟩
  · intro hempty hout
    obtain ⟨e, u, y, he, hu, hyW, hy, hcolor⟩ := hout
    have hc := eligible_cross_edge_color_mem_eligibleInteriorColors
      χ r U W hpartition x hcomponent hmax e u y he hu hyW hy hcolor
    rw [hempty] at hc
    exact Finset.notMem_empty (χ e) hc

end ErdosProblems.PathUpperReduction
