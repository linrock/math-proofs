module

public import CycleNewRepresentative
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section

/-!
An arbitrary choice of one complete-host edge for each color new at some
vertex, and the first guarded edge-exchange semantics. This candidate does
not assert component growth or Choi's weak-block structural conclusion.
-/

namespace ErdosProblems.AntiRamseyCycleNewChoiceExchange

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative

variable {n : ℕ} {C : Type*} [DecidableEq C]

abbrev HostEdge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet

/-- One chosen host edge for each color in the realized union of NEW sets. -/
structure NewChoice (χ : TopEdgeLabeling (Fin n) C) where
  edge : newColorUnion χ → HostEdge n
  color_eq : ∀ c : newColorUnion χ, χ (edge c) = c.val

noncomputable def canonicalChoice (χ : TopEdgeLabeling (Fin n) C) : NewChoice χ where
  edge := chosenNewEdge χ
  color_eq := chosenNewEdge_color χ

/-- The spanning graph consisting precisely of a choice's host edges. -/
noncomputable def selectedGraph (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    (Set.range fun c : newColorUnion χ => (r.edge c).val)

theorem NewChoice.edge_injective {χ : TopEdgeLabeling (Fin n) C}
    (r : NewChoice χ) : Function.Injective r.edge := by
  intro a b hab
  apply Subtype.ext
  calc
    a.val = χ (r.edge a) := (r.color_eq a).symm
    _ = χ (r.edge b) := by rw [hab]
    _ = b.val := r.color_eq b

theorem choice_edge_not_diag (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (c : newColorUnion χ) :
    ¬ ((r.edge c).val : Sym2 (Fin n)).IsDiag :=
  (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
    (r.edge c).property

/-- The selected graph has no edge outside the choice's range. -/
theorem selectedGraph_edgeSet (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) :
    (selectedGraph χ r).edgeSet =
      Set.range (fun c : newColorUnion χ => (r.edge c).val) := by
  rw [selectedGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c, rfl⟩, choice_edge_not_diag χ r c⟩

/-- Exchange exactly the selected edge of the input edge's NEW-union color.
The membership guard creates the necessary subtype index. -/
def NewChoice.replace {χ : TopEdgeLabeling (Fin n) C}
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) : NewChoice χ :=
  let ce : newColorUnion χ := ⟨χ e, he⟩
  { edge := fun c => if c = ce then e else r.edge c
    color_eq := by
      intro c
      by_cases hc : c = ce
      · subst c
        simp [ce]
      · simpa [hc] using r.color_eq c }

theorem NewChoice.replace_edge_same {χ : TopEdgeLabeling (Fin n) C}
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) :
    (r.replace e he).edge (⟨χ e, he⟩ : newColorUnion χ) = e := by
  simp [NewChoice.replace]

theorem NewChoice.replace_edge_other {χ : TopEdgeLabeling (Fin n) C}
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) {c : newColorUnion χ}
    (hc : c ≠ (⟨χ e, he⟩ : newColorUnion χ)) :
    (r.replace e he).edge c = r.edge c := by
  simp [NewChoice.replace, hc]

/-- Removing the replaced selected edge leaves a subgraph of the exchanged
choice graph. This does not assert that removal preserves reachability. -/
theorem delete_selectedEdge_le_replace
    (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) :
    (selectedGraph χ r).deleteEdges
      {(r.edge (⟨χ e, he⟩ : newColorUnion χ)).val} ≤
      selectedGraph χ (r.replace e he) := by
  let ce : newColorUnion χ := ⟨χ e, he⟩
  change (selectedGraph χ r).deleteEdges {(r.edge ce).val} ≤
    selectedGraph χ (r.replace e he)
  intro u v huv
  have hL : (selectedGraph χ r).Adj u v :=
    (SimpleGraph.deleteEdges_adj.mp huv).1
  have hneq : s(u, v) ≠ (r.edge ce).val := by
    simpa using (SimpleGraph.deleteEdges_adj.mp huv).2
  have hmem : s(u, v) ∈
      Set.range (fun c : newColorUnion χ => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact hL
  obtain ⟨c, hc⟩ := hmem
  have hother : c ≠ ce := by
    intro h
    apply hneq
    calc
      s(u, v) = (r.edge c).val := hc.symm
      _ = (r.edge ce).val := by rw [h]
  have hnew : s(u, v) ∈ (selectedGraph χ (r.replace e he)).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, by simpa only [r.replace_edge_other e he hother] using hc⟩
  exact hnew

/-- The input host edge belongs to the graph after the guarded exchange. -/
theorem replacedEdge_mem
    (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) :
    e.val ∈ (selectedGraph χ (r.replace e he)).edgeSet := by
  rw [selectedGraph_edgeSet]
  refine ⟨⟨χ e, he⟩, ?_⟩
  simp only [r.replace_edge_same e he]

/-- Restrict the complete-host labeling to an arbitrary NEW choice graph. -/
def restrictedColor (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) : (selectedGraph χ r).edgeSet → C :=
  fun e => χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩

/-- A valid choice selects at most one edge of each NEW-union color. -/
theorem restrictedColor_injective (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) : Function.Injective (restrictedColor χ r) := by
  intro e₁ e₂ heq
  have he₁ : e₁.val ∈
      Set.range (fun c : newColorUnion χ => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e₁.property
  have he₂ : e₂.val ∈
      Set.range (fun c : newColorUnion χ => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e₂.property
  obtain ⟨c₁, hc₁⟩ := he₁
  obtain ⟨c₂, hc₂⟩ := he₂
  have hcolor₁ : restrictedColor χ r e₁ = c₁.val := by
    have hval : e₁.val = (r.edge c₁).val := hc₁.symm
    simpa [restrictedColor, hval] using r.color_eq c₁
  have hcolor₂ : restrictedColor χ r e₂ = c₂.val := by
    have hval : e₂.val = (r.edge c₂).val := hc₂.symm
    simpa [restrictedColor, hval] using r.color_eq c₂
  have hcolors : c₁.val = c₂.val :=
    hcolor₁.symm.trans (heq.trans hcolor₂)
  have hc : c₁ = c₂ := Subtype.ext hcolors
  apply Subtype.ext
  calc
    e₁.val = (r.edge c₁).val := hc₁.symm
    _ = (r.edge c₂).val := by rw [hc]
    _ = e₂.val := hc₂

/-- Every Copy in every NEW choice graph is a literal rainbow host Copy. -/
theorem copy_in_selectedGraph_isRainbow
    {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (f : H.Copy (selectedGraph χ r)) :
    IsRainbow ((Copy.ofLE (selectedGraph χ r)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom χ := by
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ r)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f
  change Function.Injective (EdgeLabeling.pullback χ g.toHom)
  have hcolors (e : H.edgeSet) :
      EdgeLabeling.pullback χ g.toHom e =
        restrictedColor χ r (f.mapEdgeSet e) := by
    have hval : (g.toHom.mapEdgeSet e).val =
        (f.mapEdgeSet e).val := by
      simp [g, Copy.comp, Copy.ofLE, Hom.mapEdgeSet]
      rfl
    exact congrArg χ (Subtype.ext hval)
  intro e₁ e₂ hcolorsEq
  apply f.mapEdgeSet.injective
  exact restrictedColor_injective χ r
    ((hcolors e₁).symm.trans (hcolorsEq.trans (hcolors e₂)))

/-- The literal no-rainbow host premise makes every valid choice graph free. -/
theorem selectedGraph_free {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    H.Free (selectedGraph χ r) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact hno _ (copy_in_selectedGraph_isRainbow χ r f)

/-- Guarded replacement retains other edges, inserts the given edge, and
preserves ordinary `H.Free` under the literal host no-rainbow premise. -/
theorem replace_semantics {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    (selectedGraph χ r).deleteEdges
        {(r.edge (⟨χ e, he⟩ : newColorUnion χ)).val} ≤
        selectedGraph χ (r.replace e he) ∧
    e.val ∈ (selectedGraph χ (r.replace e he)).edgeSet ∧
    H.Free (selectedGraph χ (r.replace e he)) := by
  exact ⟨delete_selectedEdge_le_replace χ r e he,
    replacedEdge_mem χ r e he,
    selectedGraph_free H χ (r.replace e he) hno⟩

end ErdosProblems.AntiRamseyCycleNewChoiceExchange
