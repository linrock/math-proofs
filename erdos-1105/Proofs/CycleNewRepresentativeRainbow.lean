module

public import CycleNewRepresentative
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

/-!
The NEW-color representing graph selects one host edge per color in the
union of Choi's vertex-NEW palettes. Its selected edges have pairwise
distinct host colors; a Copy inside it is therefore a rainbow host Copy.
This semantic transfer uses no surjectivity or high-NEW count premise.
-/

namespace ErdosProblems.AntiRamseyCycleNewRepresentativeRainbow

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Restrict a complete-graph edge coloring to the selected NEW graph. -/
def restrictedNewColor (χ : TopEdgeLabeling (Fin n) C) :
    (newColorRepresentative χ).edgeSet → C :=
  fun e => χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩

/-- Every selected NEW-color edge has a distinct host label. -/
theorem restrictedNewColor_injective (χ : TopEdgeLabeling (Fin n) C) :
    Function.Injective (restrictedNewColor χ) := by
  intro e₁ e₂ heq
  have he₁ : e₁.val ∈
      Set.range (fun c : newColorUnion χ => (chosenNewEdge χ c).val) := by
    rw [← newColorRepresentative_edgeSet χ]
    exact e₁.property
  have he₂ : e₂.val ∈
      Set.range (fun c : newColorUnion χ => (chosenNewEdge χ c).val) := by
    rw [← newColorRepresentative_edgeSet χ]
    exact e₂.property
  obtain ⟨c₁, hc₁⟩ := he₁
  obtain ⟨c₂, hc₂⟩ := he₂
  have hcolor₁ : restrictedNewColor χ e₁ = c₁.val := by
    have hval : e₁.val = (chosenNewEdge χ c₁).val := hc₁.symm
    simpa [restrictedNewColor, hval] using chosenNewEdge_color χ c₁
  have hcolor₂ : restrictedNewColor χ e₂ = c₂.val := by
    have hval : e₂.val = (chosenNewEdge χ c₂).val := hc₂.symm
    simpa [restrictedNewColor, hval] using chosenNewEdge_color χ c₂
  have hcolors : c₁.val = c₂.val :=
    hcolor₁.symm.trans (heq.trans hcolor₂)
  have hc : c₁ = c₂ := Subtype.ext hcolors
  apply Subtype.ext
  calc
    e₁.val = (chosenNewEdge χ c₁).val := hc₁.symm
    _ = (chosenNewEdge χ c₂).val := by rw [hc]
    _ = e₂.val := hc₂

/-- A graph Copy in the selected NEW graph becomes a rainbow Copy in the
complete host, via its inclusion into `⊤`. -/
theorem copy_in_newColorRepresentative_isRainbow
    {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) C)
    (f : H.Copy (newColorRepresentative χ)) :
    IsRainbow ((Copy.ofLE (newColorRepresentative χ)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom χ := by
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (newColorRepresentative χ)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f
  change Function.Injective (EdgeLabeling.pullback χ g.toHom)
  have hcolors (e : H.edgeSet) :
      EdgeLabeling.pullback χ g.toHom e =
        restrictedNewColor χ (f.mapEdgeSet e) := by
    have hval : (g.toHom.mapEdgeSet e).val =
        (f.mapEdgeSet e).val := by
      simp [g, Copy.comp, Copy.ofLE, Hom.mapEdgeSet]
      rfl
    exact congrArg χ (Subtype.ext hval)
  intro e₁ e₂ hcolorsEq
  apply f.mapEdgeSet.injective
  exact restrictedNewColor_injective χ
    ((hcolors e₁).symm.trans (hcolorsEq.trans (hcolors e₂)))

/-- A no-rainbow host coloring forces its NEW-color representative to
contain no ordinary Copy of the same forbidden graph. -/
theorem newColorRepresentative_free {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ) :
    H.Free (newColorRepresentative χ) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact hno _ (copy_in_newColorRepresentative_isRainbow χ f)

/-- The literal Formal Conjectures no-rainbow-`cycleGraph k` premise
implies that the selected NEW graph is `cycleGraph k.Free`. -/
theorem newColorRepresentative_cycleGraph_free (k : ℕ)
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ) :
    (cycleGraph k).Free (newColorRepresentative χ) :=
  newColorRepresentative_free (cycleGraph k) χ hno

end ErdosProblems.AntiRamseyCycleNewRepresentativeRainbow
