module

public import CycleNewChoiceDegreeV2
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
The fixed-choice outside NEW-edge pigeonhole proof, adapted to every valid
NewChoice using the arbitrary-choice incidence map. The color is NEW at the
inside endpoint. This is an auxiliary graph/color incidence statement.
-/

namespace ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree

variable {n : ℕ} {C : Type*} [DecidableEq C]

noncomputable def newChoiceColorNeighbor (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) : Fin n :=
  ((selectedGraph χ r).incidenceSetEquivNeighborSet v
    (newChoiceIncidenceEdge χ r v c)).val

theorem newChoiceColorNeighbor_adj (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) :
    (selectedGraph χ r).Adj v (newChoiceColorNeighbor χ r v c) := by
  have hw : newChoiceColorNeighbor χ r v c ∈
      (selectedGraph χ r).neighborSet v :=
    ((selectedGraph χ r).incidenceSetEquivNeighborSet v
      (newChoiceIncidenceEdge χ r v c)).property
  exact ((selectedGraph χ r).mem_neighborSet v _).mp hw

theorem newChoiceColorNeighbor_injective (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) :
    Function.Injective (newChoiceColorNeighbor χ r v) := by
  intro a b hab
  have he :
      (selectedGraph χ r).incidenceSetEquivNeighborSet v
          (newChoiceIncidenceEdge χ r v a) =
      (selectedGraph χ r).incidenceSetEquivNeighborSet v
          (newChoiceIncidenceEdge χ r v b) := Subtype.ext hab
  have hinc : newChoiceIncidenceEdge χ r v a =
      newChoiceIncidenceEdge χ r v b :=
    ((selectedGraph χ r).incidenceSetEquivNeighborSet v).injective he
  exact newChoiceIncidenceEdge_injective χ r v hinc

theorem newChoiceIncidenceEdge_eq_pair (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) :
    (newChoiceIncidenceEdge χ r v c).val =
      s(v, newChoiceColorNeighbor χ r v c) := by
  have h :=
    ((selectedGraph χ r).incidenceSetEquivNeighborSet v).symm_apply_apply
      (newChoiceIncidenceEdge χ r v c)
  have hval := congrArg Subtype.val h
  change s(v, newChoiceColorNeighbor χ r v c) =
    (newChoiceIncidenceEdge χ r v c).val at hval
  exact hval.symm

theorem newChoiceIncidenceEdge_color (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) :
    χ ⟨(newChoiceIncidenceEdge χ r v c).val,
      SimpleGraph.edgeSet_mono le_top (newChoiceIncidenceEdge χ r v c).property.1⟩ =
      c.val := by
  let d : newColorUnion χ :=
    ⟨c.val, mem_newColorUnion_of_mem χ v c.property⟩
  have hval : (newChoiceIncidenceEdge χ r v c).val = (r.edge d).val := rfl
  have htop :
      (⟨(newChoiceIncidenceEdge χ r v c).val,
        SimpleGraph.edgeSet_mono le_top
          (newChoiceIncidenceEdge χ r v c).property.1⟩ :
        (⊤ : SimpleGraph (Fin n)).edgeSet) = r.edge d := Subtype.ext hval
  rw [htop]
  exact r.color_eq d

theorem exists_newChoiceColorNeighbor_outside
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ) (v : Fin n)
    (P : Finset (Fin n))
    (hsmall : ((selectedGraph χ r).neighborFinset v ∩ P).card <
      (newColors χ v).card) :
    ∃ c : newColors χ v, newChoiceColorNeighbor χ r v c ∉ P := by
  classical
  by_contra h
  push Not at h
  let f : newColors χ v →
      ((selectedGraph χ r).neighborFinset v ∩ P : Finset (Fin n)) := fun c =>
    ⟨newChoiceColorNeighbor χ r v c, Finset.mem_inter.mpr
      ⟨((selectedGraph χ r).mem_neighborFinset v _).mpr
          (newChoiceColorNeighbor_adj χ r v c), h c⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hval : (f a).val = (f b).val := congrArg Subtype.val hab
    change newChoiceColorNeighbor χ r v a = newChoiceColorNeighbor χ r v b at hval
    exact newChoiceColorNeighbor_injective χ r v hval
  have hcard : (newColors χ v).card ≤
      ((selectedGraph χ r).neighborFinset v ∩ P).card :=
    Finset.card_le_card_of_injective hinj
  omega

/-- The color of the selected edge leaving P is NEW at v, the inside
endpoint used in the choice-uniform rotating-path argument. -/
theorem exists_selected_newColor_edge_outside
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ) (v : Fin n)
    (P : Finset (Fin n))
    (hsmall : ((selectedGraph χ r).neighborFinset v ∩ P).card <
      (newColors χ v).card) :
    ∃ w : Fin n, ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
      w ∉ P ∧ (selectedGraph χ r).Adj v w ∧
      e.val = s(v, w) ∧ χ e ∈ newColors χ v := by
  obtain ⟨c, hc⟩ := exists_newChoiceColorNeighbor_outside χ r v P hsmall
  let w : Fin n := newChoiceColorNeighbor χ r v c
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨(newChoiceIncidenceEdge χ r v c).val,
      SimpleGraph.edgeSet_mono le_top (newChoiceIncidenceEdge χ r v c).property.1⟩
  refine ⟨w, e, hc, newChoiceColorNeighbor_adj χ r v c,
    newChoiceIncidenceEdge_eq_pair χ r v c, ?_⟩
  have hcolor : χ e = c.val := newChoiceIncidenceEdge_color χ r v c
  simpa only [hcolor] using c.property

end ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness
