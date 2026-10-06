module

public import PathUpperMaxChoice
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
for the internal-color saturation step in Yuan's path proof. The secondary maximum is over internal selected edges of every component with
the globally maximal vertex count. No connected representative is asserted.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

def componentSupport (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n) : Set (Fin n) :=
  ((selectedGraph χ r).connectedComponentMk x).supp

/-- Both endpoints of an unordered edge lie in the specified vertex set. -/
def EdgeInside (X : Set (Fin n)) (f : Sym2 (Fin n)) : Prop :=
  ∀ v ∈ f, v ∈ X

/-- Actual unordered selected host edges wholly inside `X`, counted once. -/
noncomputable def internalSelectedEdges (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact (Finset.univ.image (fun c : Fin q => (r.edge c).val)).filter (EdgeInside X)

theorem mem_componentSupport (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x v : Fin n) :
    v ∈ componentSupport χ r x ↔ (selectedGraph χ r).Reachable x v := by
  change (selectedGraph χ r).connectedComponentMk v =
      (selectedGraph χ r).connectedComponentMk x ↔ _
  exact SimpleGraph.ConnectedComponent.eq.trans SimpleGraph.reachable_comm

theorem mem_internalSelectedEdges (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n)) (f : Sym2 (Fin n)) :
    f ∈ internalSelectedEdges χ r X ↔
      f ∈ (selectedGraph χ r).edgeSet ∧ EdgeInside X f := by
  classical
  rw [selectedGraph_edgeSet χ r]
  simp [internalSelectedEdges]

/-- Maximum component vertex count, then maximum internal edge count among
all components of all same-color choices with that vertex count. -/
def LexLargestComponent (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n) : Prop :=
  GloballyLargestComponent χ r x ∧
    ∀ (r' : RepresentativeChoice χ) (z : Fin n),
      (componentSupport χ r' z).ncard = (componentSupport χ r x).ncard →
      (internalSelectedEdges χ r' (componentSupport χ r' z)).card ≤
        (internalSelectedEdges χ r (componentSupport χ r x)).card

/-- Global vertex maximality makes the retained component's vertex set exact. -/
theorem componentSupport_replace_of_old_not_inside
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hmax : GloballyLargestComponent χ r x) (e : HostEdge n)
    (hnot : ¬ EdgeInside (componentSupport χ r x) (r.edge (χ e)).val) :
    componentSupport χ (r.replace e) x = componentSupport χ r x := by
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
  exact (Set.eq_of_subset_of_ncard_le hsub (hmax (r.replace e) x)).symm

/-- If the old selected same-color edge is noninternal, replacing it by an
interior host edge inserts exactly that literal edge into the internal set. -/
theorem internalSelectedEdges_replace_of_old_not_inside
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n)) (e : HostEdge n)
    (he : EdgeInside X e.val)
    (hnot : ¬ EdgeInside X (r.edge (χ e)).val) :
    internalSelectedEdges χ (r.replace e) X =
      insert e.val (internalSelectedEdges χ r X) := by
  classical
  ext f
  constructor
  · intro hf
    obtain ⟨hselected, hfinside⟩ :=
      (mem_internalSelectedEdges χ (r.replace e) X f).mp hf
    rw [selectedGraph_edgeSet] at hselected
    obtain ⟨c, hc⟩ := hselected
    change ((r.replace e).edge c).val = f at hc
    by_cases hcolor : c = χ e
    · have hfe : f = e.val := by
        rw [hcolor, r.replace_edge_same e] at hc
        exact hc.symm
      exact Finset.mem_insert.mpr (Or.inl hfe)
    · have hold : (r.edge c).val = f := by
        simpa only [r.replace_edge_other e hcolor] using hc
      apply Finset.mem_insert_of_mem
      apply (mem_internalSelectedEdges χ r X f).mpr
      refine ⟨?_, hfinside⟩
      rw [selectedGraph_edgeSet]
      exact ⟨c, hold⟩
  · intro hf
    rcases Finset.mem_insert.mp hf with hfe | hf
    · subst f
      exact (mem_internalSelectedEdges χ (r.replace e) X e.val).mpr
        ⟨replacedEdge_mem χ r e, he⟩
    · obtain ⟨hselected, hfinside⟩ := (mem_internalSelectedEdges χ r X f).mp hf
      rw [selectedGraph_edgeSet] at hselected
      obtain ⟨c, hc⟩ := hselected
      change (r.edge c).val = f at hc
      have hcolor : c ≠ χ e := by
        intro hcγ
        subst c
        apply hnot
        rw [hc]
        exact hfinside
      apply (mem_internalSelectedEdges χ (r.replace e) X f).mpr
      refine ⟨?_, hfinside⟩
      rw [selectedGraph_edgeSet]
      refine ⟨c, ?_⟩
      simpa only [r.replace_edge_other e hcolor] using hc

/-- The insertion above is fresh, since the full original-color choice is
injective and the old edge of this original color is noninternal. -/
theorem internalSelectedEdges_card_replace_of_old_not_inside
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (X : Set (Fin n)) (e : HostEdge n)
    (he : EdgeInside X e.val)
    (hnot : ¬ EdgeInside X (r.edge (χ e)).val) :
    (internalSelectedEdges χ (r.replace e) X).card =
      (internalSelectedEdges χ r X).card + 1 := by
  classical
  have hnew : e.val ∉ internalSelectedEdges χ r X := by
    intro hmem
    have hselected := ((mem_internalSelectedEdges χ r X e.val).mp hmem).1
    rw [selectedGraph_edgeSet] at hselected
    obtain ⟨c, hc⟩ := hselected
    change (r.edge c).val = e.val at hc
    have hedge : r.edge c = e := Subtype.ext hc
    have hcolor : c = χ e := by
      calc
        c = χ (r.edge c) := (r.color_eq c).symm
        _ = χ e := congrArg χ hedge
    subst c
    apply hnot
    rw [hc]
    exact he
  rw [internalSelectedEdges_replace_of_old_not_inside χ r X e he hnot,
    Finset.card_insert_of_notMem hnew]

/-- Every original host color used inside the lexicographically chosen
component is selected on an edge wholly inside that same component. -/
theorem interior_color_selected_inside_of_lexLargestComponent
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hlex : LexLargestComponent χ r x)
    (e : HostEdge n) (he : EdgeInside (componentSupport χ r x) e.val) :
    EdgeInside (componentSupport χ r x) (r.edge (χ e)).val := by
  by_contra hnot
  have hsupport := componentSupport_replace_of_old_not_inside χ r x hlex.1 e hnot
  have hsize : (componentSupport χ (r.replace e) x).ncard =
      (componentSupport χ r x).ncard := congrArg Set.ncard hsupport
  have htie := hlex.2 (r.replace e) x hsize
  rw [hsupport] at htie
  have hcard := internalSelectedEdges_card_replace_of_old_not_inside
    χ r (componentSupport χ r x) e he hnot
  have hlt : (internalSelectedEdges χ r (componentSupport χ r x)).card <
      (internalSelectedEdges χ (r.replace e) (componentSupport χ r x)).card := by
    rw [hcard]
    exact Nat.lt_succ_self _
  exact (Nat.not_lt_of_ge htie) hlt

set_option linter.style.haveILetI false in
/-- Finite same-color choices supply both maxima. Surjectivity and `0<n`
are only used to produce an initial choice and a component vertex. -/
theorem exists_lexLargestComponent (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (hn : 0 < n) :
    ∃ (r : RepresentativeChoice χ) (x : Fin n), LexLargestComponent χ r x := by
  classical
  obtain ⟨r₀, x₀, hsize⟩ := exists_globallyLargestComponent χ hχ hn
  letI : Fintype (HostEdge n) :=
    SimpleGraph.fintypeEdgeSet (⊤ : SimpleGraph (Fin n))
  have hinj : Function.Injective (fun r : RepresentativeChoice χ => r.edge) := by
    intro r s h
    cases r with
    | mk re rp =>
      cases s with
      | mk se sp =>
        cases h
        rfl
  letI : Finite (RepresentativeChoice χ) := Finite.of_injective _ hinj
  letI : Fintype (RepresentativeChoice χ × Fin n) := Fintype.ofFinite _
  let S : Finset (RepresentativeChoice χ × Fin n) :=
    Finset.univ.filter (fun p => (componentSupport χ p.1 p.2).ncard =
      (componentSupport χ r₀ x₀).ncard)
  have hS : S.Nonempty := by
    refine ⟨(r₀, x₀), ?_⟩
    simp [S]
  obtain ⟨⟨r, x⟩, hr, hmax⟩ := Finset.exists_max_image S
    (fun p => (internalSelectedEdges χ p.1 (componentSupport χ p.1 p.2)).card) hS
  have hchosen : (componentSupport χ r x).ncard =
      (componentSupport χ r₀ x₀).ncard := (Finset.mem_filter.mp hr).2
  refine ⟨r, x, ?_, ?_⟩
  · intro r' z
    change (componentSupport χ r' z).ncard ≤ (componentSupport χ r x).ncard
    rw [hchosen]
    exact hsize r' z
  · intro r' z heq
    apply hmax (r', z)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.trans hchosen⟩

end ErdosProblems.PathUpperReduction
