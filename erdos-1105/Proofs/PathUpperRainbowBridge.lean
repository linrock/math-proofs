module

public import PathUpperExchange
public import Mathlib.Combinatorics.SimpleGraph.Copy

@[expose] public section

/-!
Every representative choice has distinct colors on its selected edges, so a
path copy in a representative graph is a rainbow host-graph path copy. This
permits a globally maximal representative choice in the upper argument.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- The complete-graph coloring restricted to a chosen representative. -/
def selectedColor (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : (selectedGraph χ r).edgeSet → Fin q :=
  fun e => χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩

theorem selectedColor_injective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : Function.Injective (selectedColor χ r) := by
  intro e₁ e₂ heq
  have he₁ : e₁.val ∈ Set.range (fun c : Fin q => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e₁.property
  have he₂ : e₂.val ∈ Set.range (fun c : Fin q => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e₂.property
  obtain ⟨c₁, hc₁⟩ := he₁
  obtain ⟨c₂, hc₂⟩ := he₂
  have hcolor₁ : selectedColor χ r e₁ = c₁ := by
    have hval : e₁.val = (r.edge c₁).val := hc₁.symm
    simpa [selectedColor, hval] using r.color_eq c₁
  have hcolor₂ : selectedColor χ r e₂ = c₂ := by
    have hval : e₂.val = (r.edge c₂).val := hc₂.symm
    simpa [selectedColor, hval] using r.color_eq c₂
  have hcolors : c₁ = c₂ := hcolor₁.symm.trans (heq.trans hcolor₂)
  apply Subtype.ext
  calc
    e₁.val = (r.edge c₁).val := hc₁.symm
    _ = (r.edge c₂).val := by rw [hcolors]
    _ = e₂.val := hc₂

theorem selectedColor_surjective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : Function.Surjective (selectedColor χ r) := by
  intro c
  have hselected : (r.edge c).val ∈ (selectedGraph χ r).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, rfl⟩
  refine ⟨⟨(r.edge c).val, hselected⟩, ?_⟩
  simpa [selectedColor] using r.color_eq c

noncomputable instance selectedGraph_edgeSet_fintype
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    Fintype (selectedGraph χ r).edgeSet := Fintype.ofFinite _

/-- Every representative choice has exactly one edge per palette color. -/
theorem selectedGraph_card_edgeFinset (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : (selectedGraph χ r).edgeFinset.card = q := by
  classical
  rw [SimpleGraph.edgeFinset_card]
  let equiv : (selectedGraph χ r).edgeSet ≃ Fin q :=
    Equiv.ofBijective (selectedColor χ r)
      ⟨selectedColor_injective χ r, selectedColor_surjective χ r⟩
  simpa using Fintype.card_congr equiv

/-- Any copy in a chosen representative graph becomes a rainbow copy of the
same graph in the complete host graph. -/
theorem copy_in_selectedGraph_isRainbow {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (f : H.Copy (selectedGraph χ r)) :
    IsRainbow ((Copy.ofLE (selectedGraph χ r)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom χ := by
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ r) (⊤ : SimpleGraph (Fin n)) le_top).comp f
  change Function.Injective (EdgeLabeling.pullback χ g.toHom)
  have hcolors (e : H.edgeSet) :
      EdgeLabeling.pullback χ g.toHom e = selectedColor χ r (f.mapEdgeSet e) := by
    have hval : (g.toHom.mapEdgeSet e).val = (f.mapEdgeSet e).val := by
      simp [g, Copy.comp, Copy.ofLE, Hom.mapEdgeSet]
      rfl
    exact congrArg χ (Subtype.ext hval)
  intro e₁ e₂ hcolorsEq
  apply f.mapEdgeSet.injective
  exact selectedColor_injective χ r
    ((hcolors e₁).symm.trans (hcolorsEq.trans (hcolors e₂)))

/-- No rainbow host copy implies every representative choice is `H.Free`. -/
theorem selectedGraph_free {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f.toHom χ) :
    H.Free (selectedGraph χ r) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact hno _ (copy_in_selectedGraph_isRainbow χ r f)

end ErdosProblems.PathUpperReduction
