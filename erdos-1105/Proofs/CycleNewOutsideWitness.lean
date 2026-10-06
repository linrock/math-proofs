module

public import CycleNewRepresentative
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
If the number of selected neighbors of v inside a finite vertex set is
smaller than the number of colors NEW at v, one selected NEW(v) edge leaves
that set. This is a color-oriented path-extension interface, with no path,
rainbow-cycle, high-NEW, or surjectivity hypothesis.
-/

namespace ErdosProblems.AntiRamseyCycleNewOutsideWitness

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The other endpoint of the selected edge indexed by a NEW color at `v`. -/
noncomputable def newColorNeighbor (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) : Fin n :=
  ((newColorRepresentative χ).incidenceSetEquivNeighborSet v
    (newColorIncidenceEdge χ v c)).val

theorem newColorNeighbor_adj (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) :
    (newColorRepresentative χ).Adj v (newColorNeighbor χ v c) := by
  have hw : newColorNeighbor χ v c ∈
      (newColorRepresentative χ).neighborSet v :=
    ((newColorRepresentative χ).incidenceSetEquivNeighborSet v
      (newColorIncidenceEdge χ v c)).property
  exact ((newColorRepresentative χ).mem_neighborSet v _).mp hw

theorem newColorNeighbor_injective (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Function.Injective (newColorNeighbor χ v) := by
  intro a b hab
  have he :
      (newColorRepresentative χ).incidenceSetEquivNeighborSet v
          (newColorIncidenceEdge χ v a) =
      (newColorRepresentative χ).incidenceSetEquivNeighborSet v
          (newColorIncidenceEdge χ v b) := Subtype.ext hab
  have hinc : newColorIncidenceEdge χ v a =
      newColorIncidenceEdge χ v b :=
    ((newColorRepresentative χ).incidenceSetEquivNeighborSet v).injective he
  exact newColorIncidenceEdge_injective χ v hinc

theorem newColorIncidenceEdge_eq_pair (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) :
    (newColorIncidenceEdge χ v c).val =
      s(v, newColorNeighbor χ v c) := by
  have h :=
    ((newColorRepresentative χ).incidenceSetEquivNeighborSet v).symm_apply_apply
      (newColorIncidenceEdge χ v c)
  have hval := congrArg Subtype.val h
  change s(v, newColorNeighbor χ v c) =
    (newColorIncidenceEdge χ v c).val at hval
  exact hval.symm

theorem newColorIncidenceEdge_color (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) :
    χ ⟨(newColorIncidenceEdge χ v c).val,
      SimpleGraph.edgeSet_mono le_top (newColorIncidenceEdge χ v c).property.1⟩ =
      c.val := by
  let d : newColorUnion χ :=
    ⟨c.val, mem_newColorUnion_of_mem χ v c.property⟩
  have hval : (newColorIncidenceEdge χ v c).val =
      (chosenNewEdge χ d).val := rfl
  have htop :
      (⟨(newColorIncidenceEdge χ v c).val,
        SimpleGraph.edgeSet_mono le_top
          (newColorIncidenceEdge χ v c).property.1⟩ :
        (⊤ : SimpleGraph (Fin n)).edgeSet) = chosenNewEdge χ d :=
    Subtype.ext hval
  rw [htop]
  exact chosenNewEdge_color χ d

/-- Finite pigeonhole: one indexed NEW(v) color selects a neighbor
outside `P` whenever its internal selected degree is too small. -/
theorem exists_newColorNeighbor_outside
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n)
    (P : Finset (Fin n))
    (hsmall : ((newColorRepresentative χ).neighborFinset v ∩ P).card <
      (newColors χ v).card) :
    ∃ c : newColors χ v, newColorNeighbor χ v c ∉ P := by
  classical
  by_contra h
  push Not at h
  let f : newColors χ v →
      ((newColorRepresentative χ).neighborFinset v ∩ P : Finset (Fin n)) := fun c =>
    ⟨newColorNeighbor χ v c, Finset.mem_inter.mpr
      ⟨((newColorRepresentative χ).mem_neighborFinset v _).mpr
          (newColorNeighbor_adj χ v c), h c⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hval : (f a).val = (f b).val := congrArg Subtype.val hab
    change newColorNeighbor χ v a = newColorNeighbor χ v b at hval
    exact newColorNeighbor_injective χ v hval
  have hcard : (newColors χ v).card ≤
      ((newColorRepresentative χ).neighborFinset v ∩ P).card :=
    Finset.card_le_card_of_injective hinj
  omega

/-- The witness is a selected edge `v-w` whose host label is NEW at the
endpoint `v` inside the finite set. This is the inward orientation used
when extending a selected tail path. -/
theorem exists_selected_newColor_edge_outside
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n)
    (P : Finset (Fin n))
    (hsmall : ((newColorRepresentative χ).neighborFinset v ∩ P).card <
      (newColors χ v).card) :
    ∃ w : Fin n, ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
      w ∉ P ∧ (newColorRepresentative χ).Adj v w ∧
      e.val = s(v, w) ∧ χ e ∈ newColors χ v := by
  obtain ⟨c, hc⟩ := exists_newColorNeighbor_outside χ v P hsmall
  let w : Fin n := newColorNeighbor χ v c
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨(newColorIncidenceEdge χ v c).val,
      SimpleGraph.edgeSet_mono le_top (newColorIncidenceEdge χ v c).property.1⟩
  refine ⟨w, e, hc, newColorNeighbor_adj χ v c,
    newColorIncidenceEdge_eq_pair χ v c, ?_⟩
  have hcolor : χ e = c.val := newColorIncidenceEdge_color χ v c
  simpa only [hcolor] using c.property

end ErdosProblems.AntiRamseyCycleNewOutsideWitness
