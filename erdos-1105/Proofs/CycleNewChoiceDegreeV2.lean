module

public import CycleNewChoiceExchange
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
Every valid choice of one host edge for each realized NEW color preserves
the per-vertex NEW-to-selected-degree inequality. This is a graph incidence
lemma only; it assumes no rainbow-cycle avoidance or Choi component structure.
-/

namespace ErdosProblems.AntiRamseyCycleNewChoiceDegree

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

def liftNewColor (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) : newColorUnion χ :=
  ⟨c.val, mem_newColorUnion_of_mem χ v c.property⟩

noncomputable instance selectedGraph_neighborSet_fintype
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ) (v : Fin n) :
    Fintype ((selectedGraph χ r).neighborSet v) := Fintype.ofFinite _

/-- A NEW color at `v` selects an edge of its color incident to `v`,
for every valid choice, including a guarded replacement choice. -/
noncomputable def newChoiceIncidenceEdge (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) :
    (selectedGraph χ r).incidenceSet v := by
  let d : newColorUnion χ := liftNewColor χ v c
  refine ⟨(r.edge d).val, ?_⟩
  change (r.edge d).val ∈ (selectedGraph χ r).edgeSet ∧
    v ∈ (r.edge d).val
  have hselected : (r.edge d).val ∈ (selectedGraph χ r).edgeSet := by
    rw [selectedGraph_edgeSet χ r]
    exact ⟨d, rfl⟩
  have hcolor : χ (r.edge d) = c.val := by
    simpa [d, liftNewColor] using r.color_eq d
  exact ⟨hselected,
    newColor_every_edge_incident χ v c.property (r.edge d) hcolor⟩

/-- Different colors NEW at one vertex select different incident edges. -/
theorem newChoiceIncidenceEdge_injective (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) :
    Function.Injective (newChoiceIncidenceEdge χ r v) := by
  intro a b hab
  have hval := congrArg Subtype.val hab
  change (r.edge (liftNewColor χ v a)).val =
    (r.edge (liftNewColor χ v b)).val at hval
  have hedge : r.edge (liftNewColor χ v a) =
      r.edge (liftNewColor χ v b) := Subtype.ext hval
  have hidx : liftNewColor χ v a = liftNewColor χ v b :=
    NewChoice.edge_injective r hedge
  exact Subtype.ext (congrArg (fun d : newColorUnion χ => d.val) hidx)

/-- The selected degree dominates the deleted-vertex NEW palette at every
vertex for every valid arbitrary-color NEW choice. -/
theorem newChoice_degree_ge_newColors (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) :
    (newColors χ v).card ≤ (selectedGraph χ r).degree v := by
  have hcard : Fintype.card (newColors χ v) ≤
      Fintype.card ((selectedGraph χ r).incidenceSet v) :=
    Fintype.card_le_of_injective (newChoiceIncidenceEdge χ r v)
      (newChoiceIncidenceEdge_injective χ r v)
  simpa only [Fintype.card_coe, SimpleGraph.card_incidenceSet_eq_degree]
    using hcard

end ErdosProblems.AntiRamseyCycleNewChoiceDegree
