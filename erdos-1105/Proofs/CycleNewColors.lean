module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
The finite color-count identity after deleting one vertex of a complete graph.
This formalizes the definition of `NEWχ(v)` used in Choi's Chapter 3 cycle
induction: incident colors absent from edges spanned by the other vertices.
It is bookkeeping only; no structural upper bound is assumed or proved here.
-/

namespace ErdosProblems.AntiRamseyCycleNewColors

open SimpleGraph

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Colors realized on all edges of the complete graph. -/
def usedColors (χ : TopEdgeLabeling (Fin n) C) : Finset C :=
  Finset.univ.image χ

/-- Colors realized on edges whose endpoints both avoid `v`. -/
def colorsAfterDeleting (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Finset C :=
  (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin n)).edgeSet =>
    v ∉ e.val)).image χ

/-- Colors realized on edges incident to `v`. -/
def incidentColors (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Finset C :=
  (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin n)).edgeSet =>
    v ∈ e.val)).image χ

/-- Choi's `NEWχ(v)`: incident colors that are absent after deleting `v`. -/
def newColors (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Finset C :=
  incidentColors χ v \ colorsAfterDeleting χ v

/-- Every realized color occurs either on an edge avoiding `v` or one
incident to `v`. This union may overlap when a color appears on both. -/
theorem usedColors_eq_deleted_union_incident
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n) :
    usedColors χ = colorsAfterDeleting χ v ∪ incidentColors χ v := by
  let f : (⊤ : SimpleGraph (Fin n)).edgeSet → C := χ
  change (Finset.univ : Finset ((⊤ : SimpleGraph (Fin n)).edgeSet)).image f =
    (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin n)).edgeSet =>
      v ∉ e.val)).image f ∪
    (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin n)).edgeSet =>
      v ∈ e.val)).image f
  rw [← Finset.image_union]
  congr 1
  ext e
  by_cases hv : v ∈ e.val <;> simp [hv]

/-- Exact color-count recurrence for deleting any vertex of a finite
complete graph, including cases where colors are reused on both sides. -/
theorem usedColors_card_delete_add_new
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n) :
    (usedColors χ).card = (colorsAfterDeleting χ v).card + (newColors χ v).card := by
  have hcard := Finset.card_sdiff_add_card (incidentColors χ v)
    (colorsAfterDeleting χ v)
  calc
    (usedColors χ).card = (colorsAfterDeleting χ v ∪ incidentColors χ v).card := by
      rw [usedColors_eq_deleted_union_incident]
    _ = (incidentColors χ v ∪ colorsAfterDeleting χ v).card := by
      rw [Finset.union_comm]
    _ = (newColors χ v).card + (colorsAfterDeleting χ v).card := by
      simpa only [newColors] using hcard.symm
    _ = (colorsAfterDeleting χ v).card + (newColors χ v).card := by
      omega

/-- When the current Formal Conjectures coloring uses every `Fin q` color,
the left side of the recurrence is exactly `q`. -/
theorem surjective_color_count_delete_add_new {q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (v : Fin n) :
    q = (colorsAfterDeleting χ v).card + (newColors χ v).card := by
  have hused : usedColors χ = Finset.univ := by
    simpa only [usedColors] using Finset.image_univ_of_surjective hχ
  simpa [hused] using usedColors_card_delete_add_new χ v

/-- A complete graph with at least two vertices has a realized edge color.
This records a nonempty instance of the recurrence. -/
theorem usedColors_nonempty_of_two_le (χ : TopEdgeLabeling (Fin n) C)
    (hn : 2 ≤ n) : (usedColors χ).Nonempty := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    simp [a, b] at hval
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨s(a, b), (SimpleGraph.mem_edgeSet ⊤).mpr ((SimpleGraph.top_adj a b).mpr hab)⟩
  exact ⟨χ e, by
    unfold usedColors
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩

end ErdosProblems.AntiRamseyCycleNewColors
