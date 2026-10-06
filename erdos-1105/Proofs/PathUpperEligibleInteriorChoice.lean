module

public import PathUpperFilteredInteriorPalette

@[expose] public section

/-!
Eligible interior palette and representative-choice extension on a residual
component.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Original colors outside U occurring on literal host edges inside X. -/
noncomputable def eligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n)) :
    Finset (Fin q) := by
  classical
  exact Finset.univ.filter (fun c =>
    c ∉ U ∧ ∃ e : HostEdge n, EdgeInside X e.val ∧ χ e = c)

theorem mem_eligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q))
    (X : Set (Fin n)) (c : Fin q) :
    c ∈ eligibleInteriorColors χ U X ↔
      c ∉ U ∧ ∃ e : HostEdge n, EdgeInside X e.val ∧ χ e = c := by
  classical
  simp [eligibleInteriorColors]

/-- A literal original inside host edge for every ENTIRE eligible color. -/
structure EligibleInteriorRepresentativeChoice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n)) where
  edge : {c : Fin q // c ∈ eligibleInteriorColors χ U X} → HostEdge n
  color_eq : ∀ c, χ (edge c) = c.val
  inside : ∀ c, EdgeInside X (edge c).val

def eligibleInteriorSelectedGraph
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (U : Set (Fin q)) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    (Set.range fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val)

/-- Every actual selected internal slot has eligible original color;
removed slots avoid W and cannot meet the whole X contained in W. -/
theorem selected_internal_color_mem_eligibleInteriorColors
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (c : Fin q) (hinside : EdgeInside (componentSupport χ r x) (r.edge c).val) :
    c ∈ eligibleInteriorColors χ U (componentSupport χ r x) := by
  have hnot : c ∉ U := by
    intro hc
    obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective ((r.edge c).val)
    have ha : a ∈ (r.edge c).val := by
      rw [← hab]
      exact Sym2.mem_mk_left a b
    exact (hpartition.removed_outside c hc a ha) (hcomponent (hinside a ha))
  exact (mem_eligibleInteriorColors χ U (componentSupport χ r x) c).mpr
    ⟨hnot, r.edge c, hinside, r.color_eq c⟩

/-- Every original eligible inside color retains its actual original owner
inside the SAME whole component by the public residual exchange theorem. -/
theorem selected_edge_inside_of_eligibleInterior_color
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x)
    (c : Fin q) (hc : c ∈ eligibleInteriorColors χ U (componentSupport χ r x)) :
    EdgeInside (componentSupport χ r x) (r.edge c).val := by
  obtain ⟨hnot, e, he, hcolor⟩ :=
    (mem_eligibleInteriorColors χ U (componentSupport χ r x) c).mp hc
  have hecolor : χ e ∉ U := by simpa only [hcolor] using hnot
  simpa only [hcolor] using
    eligible_inside_color_selected_inside_of_residualLexMaximum
      χ r U W hpartition x hcomponent hmax e hecolor he

/-- The actual original slots supply a connected choice of the ENTIRE
eligible palette, with exact original induced graph and owner coverage. -/
theorem exists_connected_eligible_interior_choice
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (hmax : ResidualLexMaximum χ r U W x) :
    ∃ s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x),
      (∀ c : {c : Fin q // c ∈ eligibleInteriorColors χ U (componentSupport χ r x)},
        s.edge c = r.edge c.val) ∧
      (eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
          (componentSupport χ r x) =
        (selectedGraph χ r).induce (componentSupport χ r x) ∧
      ((eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
        (componentSupport χ r x)).Connected ∧
      ∀ c : Fin q,
        c ∈ eligibleInteriorColors χ U (componentSupport χ r x) ↔
          EdgeInside (componentSupport χ r x) (r.edge c).val := by
  let X := componentSupport χ r x
  let s : EligibleInteriorRepresentativeChoice χ U X :=
    { edge := fun c => r.edge c.val
      color_eq := fun c => r.color_eq c.val
      inside := fun c => selected_edge_inside_of_eligibleInterior_color
        χ r U W hpartition x hcomponent hmax c.val c.property }
  have hgraph : (eligibleInteriorSelectedGraph χ U X s).induce X =
      (selectedGraph χ r).induce X := by
    ext a b
    change
      (s(a.val, b.val) ∈ Set.range
        (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} =>
          (r.edge c.val).val) ∧ a.val ≠ b.val) ↔
      (s(a.val, b.val) ∈ Set.range (fun c : Fin q => (r.edge c).val) ∧
        a.val ≠ b.val)
    constructor
    · rintro ⟨⟨c, hc⟩, hne⟩
      exact ⟨⟨c.val, hc⟩, hne⟩
    · rintro ⟨⟨c, hc⟩, hne⟩
      have hval : (r.edge c).val = s(a.val, b.val) := hc
      have hinside : EdgeInside X (r.edge c).val := by
        rw [hval]
        intro z hz
        rcases Sym2.mem_iff.mp hz with hza | hzb
        · rw [hza]
          exact a.property
        · rw [hzb]
          exact b.property
      have hcolor : c ∈ eligibleInteriorColors χ U X :=
        selected_internal_color_mem_eligibleInteriorColors
          χ r U W hpartition x hcomponent c hinside
      exact ⟨⟨⟨c, hcolor⟩, hc⟩, hne⟩
  have hconn : ((selectedGraph χ r).induce X).Connected :=
    ((selectedGraph χ r).connectedComponentMk x).connected_toSimpleGraph
  refine ⟨s, ?_, hgraph, ?_, ?_⟩
  · intro c
    rfl
  · rw [hgraph]
    exact hconn
  · intro c
    exact ⟨selected_edge_inside_of_eligibleInterior_color
        χ r U W hpartition x hcomponent hmax c,
      selected_internal_color_mem_eligibleInteriorColors
        χ r U W hpartition x hcomponent c⟩

/-- Replace ALL eligible palette slots and keep EVERY other original slot. -/
noncomputable def EligibleInteriorRepresentativeChoice.extend
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {U : Set (Fin q)} {X : Set (Fin n)}
    (s : EligibleInteriorRepresentativeChoice χ U X) (r : RepresentativeChoice χ) :
    RepresentativeChoice χ := by
  classical
  refine
    { edge := fun c => if hc : c ∈ eligibleInteriorColors χ U X then
        s.edge ⟨c, hc⟩ else r.edge c
      color_eq := ?_ }
  intro c
  by_cases hc : c ∈ eligibleInteriorColors χ U X
  · simp [hc, s.color_eq]
  · simp [hc, r.color_eq]

theorem EligibleInteriorRepresentativeChoice.extend_edge_eligible
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {U : Set (Fin q)} {X : Set (Fin n)}
    (s : EligibleInteriorRepresentativeChoice χ U X) (r : RepresentativeChoice χ)
    (c : {c : Fin q // c ∈ eligibleInteriorColors χ U X}) :
    (s.extend r).edge c.val = s.edge c := by
  classical
  simp [EligibleInteriorRepresentativeChoice.extend, c.property]

theorem EligibleInteriorRepresentativeChoice.extend_edge_noneligible
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {U : Set (Fin q)} {X : Set (Fin n)}
    (s : EligibleInteriorRepresentativeChoice χ U X) (r : RepresentativeChoice χ)
    {c : Fin q} (hc : c ∉ eligibleInteriorColors χ U X) :
    (s.extend r).edge c = r.edge c := by
  classical
  simp [EligibleInteriorRepresentativeChoice.extend, hc]

/-- Every valid entire eligible choice extends inside the exact original
U-prefix/W family BEFORE any extremal/connectedness application. -/
noncomputable def EligibleInteriorRepresentativeChoice.asOriginalResidualChoice
    {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x)) :
    OriginalResidualChoice χ r U W where
  choice := s.extend r
  prefix_eq := by
    intro c hc
    have hnot : c ∉ eligibleInteriorColors χ U (componentSupport χ r x) := by
      intro hmem
      exact ((mem_eligibleInteriorColors χ U (componentSupport χ r x) c).mp hmem).1 hc
    exact s.extend_edge_noneligible r hnot
  eligible_inside := by
    intro c hc
    by_cases hmem : c ∈ eligibleInteriorColors χ U (componentSupport χ r x)
    · rw [s.extend_edge_eligible r ⟨c, hmem⟩]
      intro v hv
      exact hcomponent (s.inside ⟨c, hmem⟩ v hv)
    · rw [s.extend_edge_noneligible r hmem]
      exact hpartition.eligible_inside c hc

theorem selected_edge_outside_of_noneligibleInterior_color
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (c : Fin q) (hc : c ∉ eligibleInteriorColors χ U (componentSupport χ r x)) :
    EdgeInside (componentSupport χ r x)ᶜ (r.edge c).val := by
  intro v hv hvX
  obtain ⟨w, hedge⟩ := Sym2.mem_iff_exists.mp hv
  have hselected : (r.edge c).val ∈ (selectedGraph χ r).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, rfl⟩
  have hadj : (selectedGraph χ r).Adj v w := by
    rw [hedge] at hselected
    exact hselected
  have hwX : w ∈ componentSupport χ r x :=
    ((selectedGraph χ r).connectedComponentMk x).mem_supp_of_adj_mem_supp hvX hadj
  have hinside : EdgeInside (componentSupport χ r x) (r.edge c).val := by
    rw [hedge]
    intro z hz
    rcases Sym2.mem_iff.mp hz with hza | hzb
    · rw [hza]
      exact hvX
    · rw [hzb]
      exact hwX
  exact hc (selected_internal_color_mem_eligibleInteriorColors
    χ r U W hpartition x hcomponent c hinside)

theorem eligibleInteriorSelectedGraph_le_extend
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (X : Set (Fin n))
    (s : EligibleInteriorRepresentativeChoice χ U X) :
    eligibleInteriorSelectedGraph χ U X s ≤ selectedGraph χ (s.extend r) := by
  intro a b hab
  change s(a, b) ∈ Set.range
    (fun c : {c : Fin q // c ∈ eligibleInteriorColors χ U X} => (s.edge c).val) ∧
      a ≠ b at hab
  obtain ⟨c, hc⟩ := hab.1
  have hnew : s(a, b) ∈ (selectedGraph χ (s.extend r)).edgeSet := by
    rw [selectedGraph_edgeSet]
    refine ⟨c.val, ?_⟩
    simpa only [s.extend_edge_eligible r c] using hc
  exact hnew

/-- A SUPPLIED CONNECTED entire eligible choice extends in the exact
original residual family with literal palette/other slots and SAME whole X. -/
theorem connected_eligible_choice_has_anchored_residual_extension
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (U : Set (Fin q)) (W : Set (Fin n))
    (hpartition : ResidualSlotPartition χ r U W)
    (x : Fin n) (hcomponent : componentSupport χ r x ⊆ W)
    (s : EligibleInteriorRepresentativeChoice χ U (componentSupport χ r x))
    (hconn : ((eligibleInteriorSelectedGraph χ U (componentSupport χ r x) s).induce
      (componentSupport χ r x)).Connected) :
    ∃ t : OriginalResidualChoice χ r U W,
      (∀ c : {c : Fin q // c ∈ eligibleInteriorColors χ U (componentSupport χ r x)},
        t.choice.edge c.val = s.edge c) ∧
      (∀ c : Fin q, c ∉ eligibleInteriorColors χ U (componentSupport χ r x) →
        t.choice.edge c = r.edge c) ∧
      componentSupport χ t.choice x = componentSupport χ r x := by
  let X := componentSupport χ r x
  let G' := selectedGraph χ (s.extend r)
  have hx : x ∈ X := (mem_componentSupport χ r x x).mpr (SimpleGraph.Reachable.refl x)
  have hclosed : ∀ a b, a ∈ X → G'.Adj a b → b ∈ X := by
    intro a b ha hab
    have hmem : s(a, b) ∈ (selectedGraph χ (s.extend r)).edgeSet := hab
    rw [selectedGraph_edgeSet] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hval : ((s.extend r).edge c).val = s(a, b) := hc
    by_cases hcolor : c ∈ eligibleInteriorColors χ U X
    · have hinside : EdgeInside X ((s.extend r).edge c).val := by
        rw [s.extend_edge_eligible r ⟨c, hcolor⟩]
        exact s.inside ⟨c, hcolor⟩
      apply hinside b
      rw [hval]
      exact Sym2.mem_mk_right a b
    · have hedge : (s.extend r).edge c = r.edge c := s.extend_edge_noneligible r hcolor
      have hout := selected_edge_outside_of_noneligibleInterior_color
        χ r U W hpartition x hcomponent c hcolor
      have hold : (r.edge c).val = s(a, b) := by
        rw [← hedge]
        exact hval
      have hnot : a ∉ X := hout a (by rw [hold]; exact Sym2.mem_mk_left a b)
      exact False.elim (hnot ha)
  have hwalk : ∀ a b (p : G'.Walk a b), a ∈ X → b ∈ X := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | cons hab p ih => exact fun ha => ih (hclosed _ _ ha hab)
  let φ : ((eligibleInteriorSelectedGraph χ U X s).induce X) →g G' :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        exact (eligibleInteriorSelectedGraph_le_extend χ r U X s) hab }
  have hsupport : componentSupport χ (s.extend r) x = X := by
    ext v
    constructor
    · intro hv
      obtain ⟨p⟩ := (mem_componentSupport χ (s.extend r) x v).mp hv
      exact hwalk x v p hx
    · intro hv
      obtain ⟨p⟩ := hconn (⟨x, hx⟩ : X) (⟨v, hv⟩ : X)
      exact (mem_componentSupport χ (s.extend r) x v).mpr (p.map φ).reachable
  refine ⟨s.asOriginalResidualChoice r U W hpartition x hcomponent, ?_, ?_, hsupport⟩
  · exact s.extend_edge_eligible r
  · intro c hc
    exact s.extend_edge_noneligible r hc

end ErdosProblems.PathUpperReduction
