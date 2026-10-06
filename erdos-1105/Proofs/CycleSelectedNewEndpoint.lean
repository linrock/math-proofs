module

public import CycleNewRepresentative

@[expose] public section

/-!
For every edge selected by the NEW-color representative, its host label
is NEW at one endpoint. A disjoint host edge cannot repeat that label.
These statements are elementary color semantics needed in Choi's cycle
splices; they use no no-rainbow, high-NEW, or surjectivity hypothesis.
-/

namespace ErdosProblems.AntiRamseyCycleSelectedNewEndpoint

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Every edge of the checked NEW representative has a label NEW at
one of its endpoints, even if that label is NEW at both endpoints. -/
theorem selected_edge_color_new_at_endpoint
    (χ : TopEdgeLabeling (Fin n) C)
    (e : (newColorRepresentative χ).edgeSet) :
    ∃ v : Fin n, v ∈ e.val ∧
      χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ ∈
        newColors χ v := by
  have he : e.val ∈
      Set.range (fun d : newColorUnion χ => (chosenNewEdge χ d).val) := by
    rw [← newColorRepresentative_edgeSet χ]
    exact e.property
  obtain ⟨d, hd⟩ := he
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp d.property
  let eTop : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩
  have htop : eTop = chosenNewEdge χ d :=
    Subtype.ext hd.symm
  have hcolor : χ eTop = d.val := by
    rw [htop]
    exact chosenNewEdge_color χ d
  have hinc : v ∈ e.val := by
    have h := newColor_every_edge_incident χ v hv
      (chosenNewEdge χ d) (chosenNewEdge_color χ d)
    simpa only [hd] using h
  refine ⟨v, hinc, ?_⟩
  change χ eTop ∈ newColors χ v
  simpa only [hcolor] using hv

/-- A host edge disjoint from both endpoints of a selected edge has
a different color from the selected edge. -/
theorem selected_edge_color_ne_of_disjoint
    (χ : TopEdgeLabeling (Fin n) C)
    (e : (newColorRepresentative χ).edgeSet)
    (f : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (hdisj : ∀ v : Fin n, v ∈ e.val → v ∉ f.val) :
    χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ ≠ χ f := by
  obtain ⟨v, hve, hnew⟩ :=
    selected_edge_color_new_at_endpoint χ e
  intro heq
  have hvf := newColor_every_edge_incident χ v hnew f heq.symm
  exact (hdisj v hve) hvf

end ErdosProblems.AntiRamseyCycleSelectedNewEndpoint
