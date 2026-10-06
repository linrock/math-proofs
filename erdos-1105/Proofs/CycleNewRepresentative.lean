module

public import CycleNewColors
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
One selected edge for each color that disappears after deleting some vertex.
This is the representing graph needed before Choi's weak-anticyclic component
argument. The result has no rainbow-cycle or surjectivity hypothesis.
-/

namespace ErdosProblems.AntiRamseyCycleNewRepresentative

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The union of all color sets new at a vertex. -/
def newColorUnion (χ : TopEdgeLabeling (Fin n) C) : Finset C :=
  Finset.univ.biUnion (newColors χ)

theorem mem_newColorUnion_of_mem (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) {c : C} (hc : c ∈ newColors χ v) :
    c ∈ newColorUnion χ := by
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hc⟩

theorem newColor_occurs (χ : TopEdgeLabeling (Fin n) C)
    {c : C} (hc : c ∈ newColorUnion χ) :
    ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet, χ e = c := by
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hc
  have hv' : c ∈ incidentColors χ v \ colorsAfterDeleting χ v := hv
  have hinc : c ∈ incidentColors χ v := (Finset.mem_sdiff.mp hv').1
  unfold incidentColors at hinc
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hinc
  exact ⟨e, he⟩

/-- Any occurrence of a color new at v must be incident to v. -/
theorem newColor_every_edge_incident (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) {c : C} (hc : c ∈ newColors χ v)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (he : χ e = c) :
    v ∈ e.val := by
  have hc' : c ∈ incidentColors χ v \ colorsAfterDeleting χ v := hc
  have hnot : c ∉ colorsAfterDeleting χ v := (Finset.mem_sdiff.mp hc').2
  by_contra hv
  have hdel : c ∈ colorsAfterDeleting χ v := by
    unfold colorsAfterDeleting
    exact Finset.mem_image.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, he⟩
  exact hnot hdel

/-- If a color is new at two distinct vertices, it can occur only on
their common edge. The two NEW sets therefore have a consistent selection. -/
theorem shared_newColor_unique_edge (χ : TopEdgeLabeling (Fin n) C)
    (v w : Fin n) (hvw : v ≠ w) {c : C}
    (hv : c ∈ newColors χ v) (hw : c ∈ newColors χ w)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (he : χ e = c) :
    e.val = s(v, w) := by
  exact (Sym2.mem_and_mem_iff hvw).mp
    ⟨newColor_every_edge_incident χ v hv e he,
      newColor_every_edge_incident χ w hw e he⟩

/-- A color new at two endpoints cannot be new at a third vertex. -/
theorem shared_newColor_only_endpoints (χ : TopEdgeLabeling (Fin n) C)
    (v w u : Fin n) (hvw : v ≠ w) {c : C}
    (hv : c ∈ newColors χ v) (hw : c ∈ newColors χ w)
    (hu : c ∈ newColors χ u) :
    u = v ∨ u = w := by
  obtain ⟨e, he⟩ :=
    newColor_occurs χ (mem_newColorUnion_of_mem χ v hv)
  have hpair := shared_newColor_unique_edge χ v w hvw hv hw e he
  have hinc := newColor_every_edge_incident χ u hu e he
  rw [hpair] at hinc
  simpa only [Sym2.mem_iff] using hinc

/-- Choose one host edge for a color that is new at some vertex. -/
noncomputable def chosenNewEdge (χ : TopEdgeLabeling (Fin n) C)
    (c : newColorUnion χ) : (⊤ : SimpleGraph (Fin n)).edgeSet :=
  Classical.choose (newColor_occurs χ c.property)

theorem chosenNewEdge_color (χ : TopEdgeLabeling (Fin n) C)
    (c : newColorUnion χ) : χ (chosenNewEdge χ c) = c.val :=
  Classical.choose_spec (newColor_occurs χ c.property)

theorem chosenNewEdge_injective (χ : TopEdgeLabeling (Fin n) C) :
    Function.Injective (fun c : newColorUnion χ => (chosenNewEdge χ c).val) := by
  intro a b hab
  have hedge : chosenNewEdge χ a = chosenNewEdge χ b := Subtype.ext hab
  have hcolor : a.val = b.val := by
    calc
      a.val = χ (chosenNewEdge χ a) := (chosenNewEdge_color χ a).symm
      _ = χ (chosenNewEdge χ b) := by rw [hedge]
      _ = b.val := chosenNewEdge_color χ b
  exact Subtype.ext hcolor

/-- The spanning graph with exactly the selected NEW-color edges. -/
noncomputable def newColorRepresentative
    (χ : TopEdgeLabeling (Fin n) C) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    (Set.range fun c : newColorUnion χ => (chosenNewEdge χ c).val)

/-- The selected graph is finite at every vertex, including empty cases. -/
noncomputable instance newColorRepresentative_neighborSet_fintype
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n) :
    Fintype ((newColorRepresentative χ).neighborSet v) := Fintype.ofFinite _

theorem chosenNewEdge_not_diag (χ : TopEdgeLabeling (Fin n) C)
    (c : newColorUnion χ) :
    ¬ ((chosenNewEdge χ c).val : Sym2 (Fin n)).IsDiag :=
  (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
    (chosenNewEdge χ c).property

/-- The graph has no other edges besides its one choice per NEW color. -/
theorem newColorRepresentative_edgeSet (χ : TopEdgeLabeling (Fin n) C) :
    (newColorRepresentative χ).edgeSet =
      Set.range (fun c : newColorUnion χ => (chosenNewEdge χ c).val) := by
  rw [newColorRepresentative, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c, rfl⟩, chosenNewEdge_not_diag χ c⟩

theorem chosenNewEdge_mem_representative (χ : TopEdgeLabeling (Fin n) C)
    (c : newColorUnion χ) :
    (chosenNewEdge χ c).val ∈ (newColorRepresentative χ).edgeSet := by
  rw [newColorRepresentative_edgeSet]
  exact ⟨c, rfl⟩

def liftNewColor (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) : newColorUnion χ :=
  ⟨c.val, mem_newColorUnion_of_mem χ v c.property⟩

/-- Send a color new at v to its selected incident edge. -/
noncomputable def newColorIncidenceEdge (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) :
    (newColorRepresentative χ).incidenceSet v := by
  let d : newColorUnion χ := liftNewColor χ v c
  refine ⟨(chosenNewEdge χ d).val, ?_⟩
  change (chosenNewEdge χ d).val ∈ (newColorRepresentative χ).edgeSet ∧
    v ∈ (chosenNewEdge χ d).val
  exact ⟨chosenNewEdge_mem_representative χ d,
    newColor_every_edge_incident χ v c.property
      (chosenNewEdge χ d) (by simpa [d, liftNewColor] using chosenNewEdge_color χ d)⟩

theorem newColorIncidenceEdge_injective (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Function.Injective (newColorIncidenceEdge χ v) := by
  intro a b hab
  have hval := congrArg Subtype.val hab
  change (chosenNewEdge χ (liftNewColor χ v a)).val =
    (chosenNewEdge χ (liftNewColor χ v b)).val at hval
  have hedge : chosenNewEdge χ (liftNewColor χ v a) =
      chosenNewEdge χ (liftNewColor χ v b) := Subtype.ext hval
  apply Subtype.ext
  calc
    a.val = χ (chosenNewEdge χ (liftNewColor χ v a)) := by
      simpa [liftNewColor] using (chosenNewEdge_color χ (liftNewColor χ v a)).symm
    _ = χ (chosenNewEdge χ (liftNewColor χ v b)) := by rw [hedge]
    _ = b.val := by
      simpa [liftNewColor] using chosenNewEdge_color χ (liftNewColor χ v b)

/-- Every NEW color at v provides a distinct edge incident to v in the
NEW-color representing graph. No no-rainbow or surjectivity premise is needed. -/
theorem newColorRepresentative_degree_ge_newColors
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n) :
    (newColors χ v).card ≤ (newColorRepresentative χ).degree v := by
  classical
  have hcard : Fintype.card (newColors χ v) ≤
      Fintype.card ((newColorRepresentative χ).incidenceSet v) :=
    Fintype.card_le_of_injective (newColorIncidenceEdge χ v)
      (newColorIncidenceEdge_injective χ v)
  simpa only [Fintype.card_coe, SimpleGraph.card_incidenceSet_eq_degree] using hcard

end ErdosProblems.AntiRamseyCycleNewRepresentative
