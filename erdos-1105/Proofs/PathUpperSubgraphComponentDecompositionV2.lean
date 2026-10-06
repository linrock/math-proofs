module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Image
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

/-!
Generic component refinement for an actual spanning
subgraph H ≤ G. The graph, component correspondence, supports, cardinalities
and cuts are not supplied as desired conclusions. This file introduces no
colors, bridges, finite-carrier assumptions or nonempty-carrier assumptions.
-/

namespace ErdosProblems.PathUpperSubgraphComponentDecomposition

open SimpleGraph

universe u

variable {V : Type u} {G H : SimpleGraph V}

/-- An H-walk cannot leave an actual original G-component when H ≤ G.
This specializes the physical Mathlib `walk_toSimpleGraph` recursion by
coercing each actual H adjacency through the supplied subgraph inequality. -/
def originalComponentRestrictedWalk
    (hHG : H ≤ G) (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) (p : H.Walk u v) :
    (H.induce C.supp).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hu (hHG h)
    have h' : (H.induce C.supp).Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (originalComponentRestrictedWalk hHG C hw hv p)

/-- Exact actual reachability reflection for H restricted to an original
G-component. Both directions include reflexive walks at isolated vertices. -/
theorem reachable_induce_original_component_iff
    (hHG : H ≤ G) (C : G.ConnectedComponent) (u v : C.supp) :
    (H.induce C.supp).Reachable u v ↔ H.Reachable u.val v.val := by
  constructor
  · intro h
    exact h.map (SimpleGraph.Embedding.induce (G := H) C.supp).toHom
  · rintro ⟨p⟩
    exact ⟨originalComponentRestrictedWalk hHG C u.property v.property p⟩

/-- Inclusion of each actual locally induced H-component into host H.
The target is the quotient of actual host reachability, not a proposed
partition type or a chosen list of desired supports. -/
def originalComponentRefinementMap (G H : SimpleGraph V) :
    (Σ C : G.ConnectedComponent, (H.induce C.supp).ConnectedComponent) →
      H.ConnectedComponent :=
  fun P => P.2.map (SimpleGraph.Embedding.induce (G := H) P.1.supp).toHom

/-- The mapped host component has exactly the lifted actual local support;
no support equality is assumed. -/
theorem original_component_refinement_map_supp
    (hHG : H ≤ G) (C : G.ConnectedComponent)
    (c : (H.induce C.supp).ConnectedComponent) :
    (originalComponentRefinementMap G H ⟨C, c⟩).supp =
      (Subtype.val '' c.supp : Set V) := by
  refine c.ind ?_
  intro u
  change (H.connectedComponentMk u.val).supp =
    (Subtype.val '' ((H.induce C.supp).connectedComponentMk u).supp : Set V)
  ext v
  constructor
  · intro hv
    have hr : H.Reachable v u.val := ConnectedComponent.exact hv
    have hvC : v ∈ C.supp :=
      (ConnectedComponent.sound (hr.mono hHG)).trans u.property
    refine ⟨⟨v, hvC⟩, ?_, rfl⟩
    exact ConnectedComponent.sound
      ((reachable_induce_original_component_iff hHG C ⟨v, hvC⟩ u).mpr hr)
  · rintro ⟨w, hw, rfl⟩
    have hr : (H.induce C.supp).Reachable w u := ConnectedComponent.exact hw
    exact ConnectedComponent.sound
      ((reachable_induce_original_component_iff hHG C w u).mp hr)

/-- Actual host H-components correspond bijectively to the dependent family
of actual H-components inside original G-components. This derives the
correspondence from H ≤ G, including empty carriers and isolated vertices. -/
theorem original_component_refinement_map_bijective
    (hHG : H ≤ G) : Function.Bijective (originalComponentRefinementMap G H) := by
  constructor
  · rintro ⟨C, c⟩ ⟨E, d⟩ h
    have hCE : C = E := by
      obtain ⟨u, hu⟩ := c.nonempty_supp
      have huHost : u.val ∈ (originalComponentRefinementMap G H ⟨C, c⟩).supp := by
        rw [original_component_refinement_map_supp hHG C c]
        exact ⟨u, hu, rfl⟩
      have huOther : u.val ∈ (originalComponentRefinementMap G H ⟨E, d⟩).supp := by
        rw [← h]
        exact huHost
      rw [original_component_refinement_map_supp hHG E d] at huOther
      obtain ⟨v, _hv, hvu⟩ := huOther
      have huE : u.val ∈ E.supp := hvu ▸ v.property
      exact ConnectedComponent.eq_of_common_vertex u.property huE
    cases hCE
    have hsupport := congrArg (fun K : H.ConnectedComponent => K.supp) h
    rw [original_component_refinement_map_supp hHG C c,
      original_component_refinement_map_supp hHG C d] at hsupport
    have hcd : c = d :=
      ConnectedComponent.supp_injective
        (Subtype.val_injective.image_injective hsupport)
    cases hcd
    rfl
  · intro K
    obtain ⟨v, rfl⟩ := K.exists_rep
    refine ⟨⟨G.connectedComponentMk v,
      (H.induce (G.connectedComponentMk v).supp).connectedComponentMk ⟨v, rfl⟩⟩, ?_⟩
    rfl

/-- The actual derived component correspondence, oriented local-to-host so
that its support formula is the original subtype lifting. -/
noncomputable def originalComponentRefinementEquiv
    (hHG : H ≤ G) :
    (Σ C : G.ConnectedComponent, (H.induce C.supp).ConnectedComponent) ≃
      H.ConnectedComponent :=
  Equiv.ofBijective (originalComponentRefinementMap G H)
    (original_component_refinement_map_bijective hHG)

theorem original_component_refinement_equiv_supp
    (hHG : H ≤ G) (C : G.ConnectedComponent)
    (c : (H.induce C.supp).ConnectedComponent) :
    (originalComponentRefinementEquiv hHG ⟨C, c⟩).supp =
      (Subtype.val '' c.supp : Set V) := by
  exact original_component_refinement_map_supp hHG C c

end ErdosProblems.PathUpperSubgraphComponentDecomposition
