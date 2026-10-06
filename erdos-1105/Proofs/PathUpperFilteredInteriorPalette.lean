module

public import PathUpperLexInternalPaletteV2

@[expose] public section

/-!
for the first palette-filtered residual exchange. All colors and selected slots are from the original complete-host coloring. The prefix is frozen by its removed-color set, and eligible selected edges
must stay wholly in the remaining vertex set. No complete residual host,
interior-palette saturation, bridge conclusion or connected full choice is
assumed. The residual lexicographic maximum is an explicit conditional input.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Original selected slots of removed colors are outside the remaining
vertices; every other original selected slot is wholly inside them. -/
structure ResidualSlotPartition
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) : Prop where
  removed_outside : ∀ c ∈ U, EdgeInside Wᶜ (r.edge c).val
  eligible_inside : ∀ c, c ∉ U → EdgeInside W (r.edge c).val

/-- A full original-color choice with the removed prefix slots frozen.
Only eligible slots may change, and their endpoints remain in `W`. -/
structure OriginalResidualChoice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) where
  choice : RepresentativeChoice χ
  prefix_eq : ∀ c ∈ U, choice.edge c = r.edge c
  eligible_inside : ∀ c, c ∉ U → EdgeInside W (choice.edge c).val

/-- Size maximum, then internal-edge maximum, over exactly the choices
preserving this original prefix and the remaining-vertex boundary. -/
def ResidualLexMaximum
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n)) (x : Fin n) : Prop :=
  (∀ (s : OriginalResidualChoice χ r U W) (z : Fin n), z ∈ W →
    (componentSupport χ s.choice z).ncard ≤
      (componentSupport χ r x).ncard) ∧
  ∀ (s : OriginalResidualChoice χ r U W) (z : Fin n), z ∈ W →
    (componentSupport χ s.choice z).ncard =
      (componentSupport χ r x).ncard →
    (internalSelectedEdges χ s.choice (componentSupport χ s.choice z)).card ≤
      (internalSelectedEdges χ r (componentSupport χ r x)).card

/-- A literal eligible replacement preserves every frozen original slot
and the whole remaining-vertex boundary. -/
def originalResidualReplace
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (e : HostEdge n) (hcolor : χ e ∉ U) (hinside : EdgeInside W e.val) :
    OriginalResidualChoice χ r U W where
  choice := r.replace e
  prefix_eq := by
    intro c hc
    have hne : c ≠ χ e := by
      intro heq
      exact hcolor (heq ▸ hc)
    exact r.replace_edge_other e hne
  eligible_inside := by
    intro c hc
    by_cases heq : c = χ e
    · rw [heq, r.replace_edge_same e]
      exact hinside
    · rw [r.replace_edge_other e heq]
      exact hpartition.eligible_inside c hc

/-- Every eligible original color appearing wholly inside this WHOLE
original component has its literal original selected slot inside the same
component. This is the first input for an entire eligible interior choice. -/
theorem eligible_inside_color_selected_inside_of_residualLexMaximum
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (e : HostEdge n) (hcolor : χ e ∉ U)
    (he : EdgeInside (componentSupport χ r x) e.val) :
    EdgeInside (componentSupport χ r x) (r.edge (χ e)).val := by
  by_contra hnot
  have hx : x ∈ W := hcomponent
    ((mem_componentSupport χ r x x).mpr (SimpleGraph.Reachable.refl x))
  have heW : EdgeInside W e.val := by
    intro v hv
    exact hcomponent (he v hv)
  let s : OriginalResidualChoice χ r U W :=
    originalResidualReplace χ r U W hpartition e hcolor heW
  have hretain : ∀ v, (selectedGraph χ r).Reachable x v →
      ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v := by
    intro v hv
    by_contra hdisconnect
    obtain ⟨a, b, hab, ha, hb⟩ :=
      edge_endpoints_reachable_of_delete_disconnects
        (selectedGraph χ r) (r.edge (χ e)).val hv hdisconnect
    apply hnot
    rw [hab]
    intro w hw
    rcases Sym2.mem_iff.mp hw with hwa | hwb
    · rw [hwa]
      exact (mem_componentSupport χ r x a).mpr ha
    · rw [hwb]
      exact (mem_componentSupport χ r x b).mpr hb
  have hsub : componentSupport χ r x ⊆ componentSupport χ (r.replace e) x := by
    intro v hv
    exact (mem_componentSupport χ (r.replace e) x v).mpr
      ((hretain v ((mem_componentSupport χ r x v).mp hv)).mono
        (delete_selectedEdge_le_replace χ r e))
  have hsizele : (componentSupport χ (r.replace e) x).ncard ≤
      (componentSupport χ r x).ncard := hmax.1 s x hx
  have hsupport : componentSupport χ (r.replace e) x = componentSupport χ r x :=
    (Set.eq_of_subset_of_ncard_le hsub hsizele).symm
  have hsize : (componentSupport χ s.choice x).ncard =
      (componentSupport χ r x).ncard := congrArg Set.ncard hsupport
  have htie := hmax.2 s x hx hsize
  have hsupportS : componentSupport χ s.choice x = componentSupport χ r x := hsupport
  rw [hsupportS] at htie
  have hcard := internalSelectedEdges_card_replace_of_old_not_inside
    χ r (componentSupport χ r x) e he hnot
  have hlt : (internalSelectedEdges χ r (componentSupport χ r x)).card <
      (internalSelectedEdges χ (r.replace e) (componentSupport χ r x)).card := by
    rw [hcard]
    exact Nat.lt_succ_self _
  exact (Nat.not_lt_of_ge htie) hlt

end ErdosProblems.PathUpperReduction
