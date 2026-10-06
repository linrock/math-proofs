module

public import CycleNewChoiceExchange
public import PathUpperExchange
public import Mathlib.Tactic

@[expose] public section

/-! conditional Claim3 palette exclusion for arbitrary original χ/r. -/

namespace ErdosProblems.AntiRamseyCycleCrossComponentPaletteExclusion

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A same-original-color guarded replacement contains both whole old
components if deleting its actual selected same-color edge preserves old
reachability. The old edge is not assumed to lie in either component. -/
theorem replacement_contains_component_union
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : HostEdge n) (hc : χ e ∈ newColorUnion χ)
    (A B : (selectedGraph χ r).ConnectedComponent) (u v : Fin n)
    (hu : u ∈ A.supp) (hv : v ∈ B.supp) (he : e.val = s(u, v))
    (hdelete : ∀ a b : Fin n, (selectedGraph χ r).Reachable a b →
      ((selectedGraph χ r).deleteEdges
        {(r.edge (⟨χ e, hc⟩ : newColorUnion χ)).val}).Reachable a b) :
    A.supp ∪ B.supp ⊆
      ((selectedGraph χ (r.replace e hc)).connectedComponentMk u).supp := by
  classical
  let G' : SimpleGraph (Fin n) := selectedGraph χ (r.replace e hc)
  have hle := delete_selectedEdge_le_replace χ r e hc
  have hretained : ∀ a b : Fin n, (selectedGraph χ r).Reachable a b →
      G'.Reachable a b := by
    intro a b hab
    exact SimpleGraph.Reachable.mono hle (hdelete a b hab)
  have hnew : G'.Adj u v := by
    have hmem := replacedEdge_mem χ r e hc
    rw [he] at hmem
    exact hmem
  intro x hx
  rcases hx with hx | hx
  · have hux : G'.Reachable u x :=
      hretained u x (A.reachable_of_mem_supp hu hx)
    exact (SimpleGraph.ConnectedComponent.eq.mpr hux).symm
  · have hvx : G'.Reachable v x :=
      hretained v x (B.reachable_of_mem_supp hv hx)
    exact (SimpleGraph.ConnectedComponent.eq.mpr (hnew.reachable.trans hvx)).symm

/-- The containing exchanged component has at least the sum of the two
disjoint whole old component orders. No endpoint of the deleted edge is
localized to A or B. -/
theorem replacement_component_card_ge_sum
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : HostEdge n) (hc : χ e ∈ newColorUnion χ)
    (A B : (selectedGraph χ r).ConnectedComponent)
    (hAB : Disjoint A.supp B.supp) (u v : Fin n)
    (hu : u ∈ A.supp) (hv : v ∈ B.supp) (he : e.val = s(u, v))
    (hdelete : ∀ a b : Fin n, (selectedGraph χ r).Reachable a b →
      ((selectedGraph χ r).deleteEdges
        {(r.edge (⟨χ e, hc⟩ : newColorUnion χ)).val}).Reachable a b) :
    A.supp.ncard + B.supp.ncard ≤
      ((selectedGraph χ (r.replace e hc)).connectedComponentMk u).supp.ncard := by
  have hsub := replacement_contains_component_union χ r e hc A B u v hu hv he hdelete
  calc
    A.supp.ncard + B.supp.ncard = (A.supp ∪ B.supp).ncard :=
      (Set.ncard_union_eq hAB (Set.toFinite _) (Set.toFinite _)).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- Conditional original-host cross colors lie outside the complete selected
NEW palette. The upper-order assumption quantifies over every valid choice
for the SAME original coloring; a bound on only r would not suffice. -/
theorem cross_edge_color_not_new_union_of_retained_reachability
    {k : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hdelete : ∀ c : newColorUnion χ, ∀ a b : Fin n,
      (selectedGraph χ r).Reachable a b →
      ((selectedGraph χ r).deleteEdges {(r.edge c).val}).Reachable a b)
    (hupper : ∀ r' : NewChoice χ, ∀ D : (selectedGraph χ r').ConnectedComponent,
      D.supp.ncard ≤ k - 1)
    (A B : (selectedGraph χ r).ConnectedComponent)
    (hAB : Disjoint A.supp B.supp)
    (hlarge : k + 1 ≤ A.supp.ncard + B.supp.ncard)
    (u v : Fin n) (hu : u ∈ A.supp) (hv : v ∈ B.supp)
    (e : HostEdge n) (he : e.val = s(u, v)) :
    χ e ∉ newColorUnion χ := by
  intro hc
  have hlower := replacement_component_card_ge_sum χ r e hc A B hAB u v hu hv he
    (hdelete (⟨χ e, hc⟩ : newColorUnion χ))
  have hsmall := hupper (r.replace e hc)
    ((selectedGraph χ (r.replace e hc)).connectedComponentMk u)
  omega

/-- The checked generic nonbridge-deletion API supplies the preceding
reachability premise. Downstream Hamiltonicity-to-nonbridge is a separate
obligation; it is not silently assumed proved here. -/
theorem cross_edge_color_not_new_union_of_nonbridge
    {k : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnb : ∀ c : newColorUnion χ,
      ¬ (selectedGraph χ r).IsBridge (r.edge c).val)
    (hupper : ∀ r' : NewChoice χ, ∀ D : (selectedGraph χ r').ConnectedComponent,
      D.supp.ncard ≤ k - 1)
    (A B : (selectedGraph χ r).ConnectedComponent)
    (hAB : Disjoint A.supp B.supp)
    (hlarge : k + 1 ≤ A.supp.ncard + B.supp.ncard)
    (u v : Fin n) (hu : u ∈ A.supp) (hv : v ∈ B.supp)
    (e : HostEdge n) (he : e.val = s(u, v)) :
    χ e ∉ newColorUnion χ := by
  apply cross_edge_color_not_new_union_of_retained_reachability χ r ?_
    hupper A B hAB hlarge u v hu hv e he
  intro c a b hab
  exact ErdosProblems.PathUpperReduction.reachable_deleteEdge_of_not_bridge
    (selectedGraph χ r) (r.edge c).val (hnb c) hab

end ErdosProblems.AntiRamseyCycleCrossComponentPaletteExclusion
