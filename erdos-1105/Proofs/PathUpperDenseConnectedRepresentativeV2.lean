module

public import PathUpperExchange
public import PathUpperMaxChoice
public import PathUpperRainbowBridge
public import DenseDisconnectedBridgeBoundV2

@[expose] public section

/-! Connectedness of a globally largest representative component above the disconnected bridge threshold. -/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- A globally largest component among all full same-color representatives
is the whole selected graph above the disconnected actual-bridge threshold. -/
theorem selectedGraph_connected_of_global_maximum_and_dense
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hmax : GloballyLargestComponent χ r x)
    (hdense : (n - 2).choose 2 + 2 ≤ q) :
    (selectedGraph χ r).Connected := by
  classical
  by_contra hdis
  have hyexists : ∃ y : Fin n, ¬ (selectedGraph χ r).Reachable x y := by
    by_contra! h
    exact hdis ((SimpleGraph.connected_iff_exists_forall_reachable (selectedGraph χ r)).mpr ⟨x, h⟩)
  obtain ⟨y, hy⟩ := hyexists
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hy (SimpleGraph.Reachable.refl x)
  let e : HostEdge n :=
    ⟨s(x, y), (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin n))).mpr
      ((top_adj x y).mpr hxy)⟩
  obtain ⟨a, b, howner, _, _, hbridge⟩ :=
    cross_edge_color_is_component_bridge χ r x hmax e x y rfl
      (SimpleGraph.Reachable.refl x) hy
  have hselected : (r.edge (χ e)).val ∈ (selectedGraph χ r).edgeSet := by
    rw [selectedGraph_edgeSet χ r]
    exact ⟨χ e, rfl⟩
  rw [howner] at hselected
  have hGdense : (n - 2).choose 2 + 2 ≤ (selectedGraph χ r).edgeFinset.card := by
    rw [selectedGraph_card_edgeFinset χ r]
    exact hdense
  have hGdenseCanonical := hGdense
  have hInstances : selectedGraph_edgeSet_fintype χ r =
      (selectedGraph χ r).fintypeEdgeSet := Subsingleton.elim _ _
  rw [hInstances] at hGdenseCanonical
  exact ErdosProblems.PathUpperDenseDisconnectedBridgeBound.actual_edge_not_bridge_of_dense_disconnected
      (selectedGraph χ r) hdis hGdenseCanonical s(a, b) hselected hbridge

/-- Surjectivity and a nonempty host supply a connected full representative
at the same original-palette density threshold. -/
theorem exists_connected_representative_of_dense_palette
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (hn : 0 < n)
    (hdense : (n - 2).choose 2 + 2 ≤ q) :
    ∃ r : RepresentativeChoice χ, (selectedGraph χ r).Connected := by
  obtain ⟨r, x, hmax⟩ := exists_globallyLargestComponent χ hχ hn
  exact ⟨r, selectedGraph_connected_of_global_maximum_and_dense χ r x hmax hdense⟩

end ErdosProblems.PathUpperReduction
