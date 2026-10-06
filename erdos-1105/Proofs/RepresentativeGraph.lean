module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Copy

@[expose] public section

/-!
One-edge-per-color representative graphs for a surjective coloring of a complete graph.
This reduction connects anti-Ramsey colorings to ordinary extremal graph bounds.
-/

namespace ErdosProblems.AntiRamseyRepresentative

open SimpleGraph

variable {n q : ℕ}

/-- The edge chosen for color `k` by a right inverse to a surjective coloring. -/
noncomputable def chosenEdge (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) : (⊤ : SimpleGraph (Fin n)).edgeSet :=
  Function.surjInv hχ k

theorem chosenEdge_color (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) : χ (chosenEdge χ hχ k) = k :=
  Function.surjInv_eq hχ k

/-- A graph on all `n` vertices containing exactly one chosen edge for each color. -/
noncomputable def representativeGraph (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Set.range fun k : Fin q => (chosenEdge χ hχ k).val)

theorem chosenEdge_not_diag (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) :
    ¬ ((chosenEdge χ hχ k).val : Sym2 (Fin n)).IsDiag :=
  (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet (chosenEdge χ hχ k).property

theorem representativeGraph_edgeSet (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) :
    (representativeGraph χ hχ).edgeSet =
      Set.range (fun k : Fin q => (chosenEdge χ hχ k).val) := by
  rw [representativeGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, rfl⟩, chosenEdge_not_diag χ hχ k⟩

noncomputable instance representativeGraph_edgeSet_fintype
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ) :
    Fintype (representativeGraph χ hχ).edgeSet := Fintype.ofFinite _

/-- The chosen edge as an edge of the representative graph. -/
noncomputable def chosenRepresentativeEdge (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) : (representativeGraph χ hχ).edgeSet :=
  ⟨(chosenEdge χ hχ k).val, by
    rw [representativeGraph_edgeSet]
    exact ⟨k, rfl⟩⟩

theorem chosenRepresentativeEdge_color (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) :
    χ ⟨(chosenRepresentativeEdge χ hχ k).val,
      by exact (chosenEdge χ hχ k).property⟩ = k := by
  exact chosenEdge_color χ hχ k

/-- Restriction of the complete coloring to the representative graph. -/
def restrictedColor (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) : (representativeGraph χ hχ).edgeSet → Fin q :=
  fun e => χ ⟨e.val, by
    exact SimpleGraph.edgeSet_mono le_top e.property⟩

/-- Distinct edges of the representative graph have distinct colors. -/
theorem restrictedColor_injective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) :
    Function.Injective (restrictedColor χ hχ) := by
  intro e₁ e₂ heq
  have he₁ : e₁.val ∈ Set.range (fun k : Fin q => (chosenEdge χ hχ k).val) := by
    rw [← representativeGraph_edgeSet χ hχ]
    exact e₁.property
  have he₂ : e₂.val ∈ Set.range (fun k : Fin q => (chosenEdge χ hχ k).val) := by
    rw [← representativeGraph_edgeSet χ hχ]
    exact e₂.property
  obtain ⟨k₁, hk₁⟩ := he₁
  obtain ⟨k₂, hk₂⟩ := he₂
  have hc₁ : restrictedColor χ hχ e₁ = k₁ := by
    have hval : e₁.val = (chosenEdge χ hχ k₁).val := hk₁.symm
    simpa [restrictedColor, hval] using chosenEdge_color χ hχ k₁
  have hc₂ : restrictedColor χ hχ e₂ = k₂ := by
    have hval : e₂.val = (chosenEdge χ hχ k₂).val := hk₂.symm
    simpa [restrictedColor, hval] using chosenEdge_color χ hχ k₂
  have hk : k₁ = k₂ := hc₁.symm.trans (heq.trans hc₂)
  apply Subtype.ext
  calc
    e₁.val = (chosenEdge χ hχ k₁).val := hk₁.symm
    _ = (chosenEdge χ hχ k₂).val := by rw [hk]
    _ = e₂.val := hk₂

/-- Every color occurs once on the representative graph. -/
theorem restrictedColor_surjective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) :
    Function.Surjective (restrictedColor χ hχ) := by
  intro k
  refine ⟨chosenRepresentativeEdge χ hχ k, ?_⟩
  simpa [restrictedColor] using chosenRepresentativeEdge_color χ hχ k

/-- The representative graph has exactly `q` edges. -/
theorem representativeGraph_card_edgeFinset (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) :
    (representativeGraph χ hχ).edgeFinset.card = q := by
  classical
  rw [SimpleGraph.edgeFinset_card]
  let e : (representativeGraph χ hχ).edgeSet ≃ Fin q :=
    Equiv.ofBijective (restrictedColor χ hχ)
      ⟨restrictedColor_injective χ hχ, restrictedColor_surjective χ hχ⟩
  simpa using Fintype.card_congr e

/-- A copy in the representative graph becomes a rainbow copy in the complete graph. -/
theorem copy_in_representativeGraph_isRainbow {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (f : H.Copy (representativeGraph χ hχ)) :
    IsRainbow ((Copy.ofLE (representativeGraph χ hχ)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom χ := by
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (representativeGraph χ hχ) (⊤ : SimpleGraph (Fin n)) le_top).comp f
  change Function.Injective (EdgeLabeling.pullback χ g.toHom)
  have hcolors (e : H.edgeSet) :
      EdgeLabeling.pullback χ g.toHom e = restrictedColor χ hχ (f.mapEdgeSet e) := by
    have hval : (g.toHom.mapEdgeSet e).val = (f.mapEdgeSet e).val := by
      simp [g, Copy.comp, Copy.ofLE, Hom.mapEdgeSet]
      rfl
    exact congrArg χ (Subtype.ext hval)
  intro e₁ e₂ hcolorsEq
  apply f.mapEdgeSet.injective
  exact restrictedColor_injective χ hχ
    ((hcolors e₁).symm.trans (hcolorsEq.trans (hcolors e₂)))

/-- A coloring with no rainbow `H` forces its representative graph to be `H`-free. -/
theorem representativeGraph_free {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f.toHom χ) :
    H.Free (representativeGraph χ hχ) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact hno _ (copy_in_representativeGraph_isRainbow χ hχ f)

end ErdosProblems.AntiRamseyRepresentative
