module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section

/-!
The first edge-exchange step in Yuan's connected-representative argument.
Each used color has exactly one chosen complete-graph edge. Replacing that edge
with another edge of the same color preserves the representative property.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

abbrev HostEdge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet

/-- A choice of one host edge for each used color. -/
structure RepresentativeChoice (χ : TopEdgeLabeling (Fin n) (Fin q)) where
  edge : Fin q → HostEdge n
  color_eq : ∀ c, χ (edge c) = c

/-- The spanning graph consisting of the chosen edges. -/
def selectedGraph (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Set.range fun c : Fin q => (r.edge c).val)

theorem RepresentativeChoice.edge_injective {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) : Function.Injective r.edge := by
  intro a b hab
  calc
    a = χ (r.edge a) := (r.color_eq a).symm
    _ = χ (r.edge b) := by rw [hab]
    _ = b := r.color_eq b

theorem selectedGraph_edgeSet (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) :
    (selectedGraph χ r).edgeSet = Set.range (fun c : Fin q => (r.edge c).val) := by
  rw [selectedGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c, rfl⟩, (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
      (r.edge c).property⟩

/-- Replace the selected edge of color `χ e` by the host edge `e`. -/
def RepresentativeChoice.replace {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) (e : HostEdge n) : RepresentativeChoice χ where
  edge := fun c => if c = χ e then e else r.edge c
  color_eq := by
    intro c
    by_cases h : c = χ e
    · simp [h]
    · simp [h, r.color_eq]

theorem RepresentativeChoice.replace_edge_same {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) (e : HostEdge n) :
    (r.replace e).edge (χ e) = e := by
  simp [RepresentativeChoice.replace]

theorem RepresentativeChoice.replace_edge_other {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) (e : HostEdge n) {c : Fin q} (hc : c ≠ χ e) :
    (r.replace e).edge c = r.edge c := by
  simp [RepresentativeChoice.replace, hc]

/-- The replacement graph retains every old edge except the selected edge of the same color. -/
theorem delete_selectedEdge_le_replace (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (e : HostEdge n) :
    (selectedGraph χ r).deleteEdges {(r.edge (χ e)).val} ≤
      selectedGraph χ (r.replace e) := by
  intro u v huv
  have hL : (selectedGraph χ r).Adj u v := (SimpleGraph.deleteEdges_adj.mp huv).1
  have hneq : s(u, v) ≠ (r.edge (χ e)).val := by
    simpa using (SimpleGraph.deleteEdges_adj.mp huv).2
  have hmem : s(u, v) ∈ Set.range (fun c : Fin q => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact hL
  obtain ⟨c, hc⟩ := hmem
  have hother : c ≠ χ e := by
    intro h
    subst c
    exact hneq hc.symm
  have hnew : s(u, v) ∈ (selectedGraph χ (r.replace e)).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, by simpa [r.replace_edge_other e hother] using hc⟩
  exact hnew

/-- The replacement graph includes the new host edge. -/
theorem replacedEdge_mem (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (e : HostEdge n) :
    e.val ∈ (selectedGraph χ (r.replace e)).edgeSet := by
  rw [selectedGraph_edgeSet]
  exact ⟨χ e, by simp [r.replace_edge_same e]⟩

/-- If removing a selected edge leaves the old component connected, inserting a
cross-component edge produces a strictly larger component. -/
theorem component_grows_of_retained_reachability
    (L L' : SimpleGraph (Fin n)) (old : Sym2 (Fin n)) (x u y : Fin n)
    (hle : L.deleteEdges {old} ≤ L') (huy : L'.Adj u y)
    (hu : L.Reachable x u)
    (hy : ¬ L.Reachable x y)
    (hretain : ∀ v, L.Reachable x v → (L.deleteEdges {old}).Reachable x v) :
    (L.connectedComponentMk x).supp.ncard <
      (L'.connectedComponentMk x).supp.ncard := by
  have hsub : (L.connectedComponentMk x).supp ⊆
      (L'.connectedComponentMk x).supp := by
    intro v hv
    have hv' : L.Reachable x v := SimpleGraph.ConnectedComponent.eq.mp hv.symm
    exact SimpleGraph.ConnectedComponent.eq.mpr
      ((hretain v hv').mono hle) |>.symm
  have hynot : y ∉ (L.connectedComponentMk x).supp := by
    intro h
    exact hy (SimpleGraph.ConnectedComponent.eq.mp h.symm)
  have hynew : y ∈ (L'.connectedComponentMk x).supp := by
    have hxu : L'.Reachable x u := (hretain u hu).mono hle
    exact (SimpleGraph.ConnectedComponent.eq.mpr (hxu.trans huy.reachable)).symm
  exact Set.ncard_lt_ncard (hsub.ssubset_of_mem_notMem hynew hynot)
    (Set.toFinite _)

/-- A chosen component is globally largest if no component of any same-color
representative choice has more vertices. This is the explicit extremal choice
used by Yuan before the cut-edge argument. -/
def GloballyLargestComponent (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n) : Prop :=
  ∀ r' : RepresentativeChoice χ, ∀ z : Fin n,
    ((selectedGraph χ r').connectedComponentMk z).supp.ncard ≤
      ((selectedGraph χ r).connectedComponentMk x).supp.ncard

/-- Applied to an edge exchange, the abstract component-growth lemma. -/
theorem replacement_grows_component (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (e : HostEdge n) (x u y : Fin n)
    (he : e.val = s(u, y))
    (hu : (selectedGraph χ r).Reachable x u)
    (hy : ¬ (selectedGraph χ r).Reachable x y)
    (hretain : ∀ v, (selectedGraph χ r).Reachable x v →
      ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v) :
    ((selectedGraph χ r).connectedComponentMk x).supp.ncard <
      ((selectedGraph χ (r.replace e)).connectedComponentMk x).supp.ncard := by
  apply component_grows_of_retained_reachability
    (selectedGraph χ r) (selectedGraph χ (r.replace e))
    (r.edge (χ e)).val x u y (delete_selectedEdge_le_replace χ r e) ?_
    hu hy hretain
  have hmem := replacedEdge_mem χ r e
  rw [he] at hmem
  exact hmem

/-- Removing an edge that is not a bridge preserves every old reachability
relation, even when the whole graph has several components. -/
theorem reachable_deleteEdge_of_not_bridge (L : SimpleGraph (Fin n))
    (old : Sym2 (Fin n)) (hnb : ¬ L.IsBridge old)
    {u v : Fin n} (huv : L.Reachable u v) :
    (L.deleteEdges {old}).Reachable u v := by
  let D := L.deleteEdges {old}
  have hstep : ∀ a b : Fin n, L.Adj a b → D.Reachable a b := by
    intro a b hab
    by_cases he : s(a, b) = old
    · have hnb' : ¬ L.IsBridge s(a, b) := by simpa [he] using hnb
      by_contra hnotreach
      have hnotreach' : ¬ (L.deleteEdges {s(a, b)}).Reachable a b := by
        simpa [D, he] using hnotreach
      exact hnb' (SimpleGraph.isBridge_iff.mpr hnotreach')
    · exact (SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa using he⟩).reachable
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab p ih => exact (hstep _ _ hab).trans ih

/-- If deleting one edge separates two previously reachable vertices, both
endpoints of that edge lie in their original connected component. -/
theorem edge_endpoints_reachable_of_delete_disconnects (L : SimpleGraph (Fin n))
    (old : Sym2 (Fin n)) {x v : Fin n}
    (hv : L.Reachable x v)
    (hnot : ¬ (L.deleteEdges {old}).Reachable x v) :
    ∃ a b : Fin n, old = s(a, b) ∧ L.Reachable x a ∧ L.Reachable x b := by
  obtain ⟨a, b⟩ := old
  obtain ⟨p⟩ := hv
  have he : s(a, b) ∈ p.edges :=
    p.mem_edges_of_not_reachable_deleteEdges hnot
  refine ⟨a, b, rfl, ?_, ?_⟩
  · exact ⟨p.takeUntil a (p.fst_mem_support_of_mem_edges he)⟩
  · exact ⟨p.takeUntil b (p.snd_mem_support_of_mem_edges he)⟩

/-- In a globally maximal representative, replacing a cross-component host
edge cannot leave the old component connected. Equivalently, the selected edge
of that color cuts the largest component; the stronger `IsBridge` formulation
requires identifying the selected edge inside the induced component. -/
theorem selected_edge_cuts_largest_component (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hmax : GloballyLargestComponent χ r x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : (selectedGraph χ r).Reachable x u)
    (hy : ¬ (selectedGraph χ r).Reachable x y) :
    ∃ v, (selectedGraph χ r).Reachable x v ∧
      ¬ ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v := by
  by_contra h
  push Not at h
  have hlt := replacement_grows_component χ r e x u y he hu hy h
  exact (Nat.not_lt_of_ge (hmax (r.replace e) x)) hlt

/-- Yuan's maximal-component color confinement: a host edge leaving a
globally largest component has the color of a selected bridge edge *inside*
that component. `IsBridge` uses Mathlib's deletion/reachability definition. -/
theorem cross_edge_color_is_component_bridge
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hmax : GloballyLargestComponent χ r x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : (selectedGraph χ r).Reachable x u)
    (hy : ¬ (selectedGraph χ r).Reachable x y) :
    ∃ a b : Fin n,
      (r.edge (χ e)).val = s(a, b) ∧
      a ∈ (selectedGraph χ r).connectedComponentMk x ∧
      b ∈ (selectedGraph χ r).connectedComponentMk x ∧
      (selectedGraph χ r).IsBridge s(a, b) := by
  let L := selectedGraph χ r
  let old := (r.edge (χ e)).val
  obtain ⟨v, hv, hnot⟩ :=
    selected_edge_cuts_largest_component χ r x hmax e u y he hu hy
  obtain ⟨a, b, hab, hxa, hxb⟩ :=
    edge_endpoints_reachable_of_delete_disconnects L old hv hnot
  have hbridge : L.IsBridge old := by
    by_contra hnb
    exact hnot (reachable_deleteEdge_of_not_bridge L old hnb hv)
  exact ⟨a, b, hab,
    (SimpleGraph.ConnectedComponent.eq.mpr hxa).symm,
    (SimpleGraph.ConnectedComponent.eq.mpr hxb).symm,
    hab ▸ hbridge⟩

end ErdosProblems.PathUpperReduction
