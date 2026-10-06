module

public import CycleNewChoiceOutsideWitnessV2
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! For the second NEW edge in Choi Claim 1 Case B. It constructs no rainbow cycle Copy. -/

namespace ErdosProblems.AntiRamseyCycleClaimOneSecondNewWitness

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- If every host spoke from `u` to a selected cycle has color `α`, a
different color NEW at `u` selects an edge `u-w` with `w` outside the cycle. -/
theorem exists_second_new_selected_edge_outside {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (α : C)
    (hnewu : 2 ≤ (newColors χ u).card)
    (hcommon : ∀ (i : Fin (m + 1))
        (e : (⊤ : SimpleGraph (Fin n)).edgeSet),
      e.val = s(u, cyc.toHom i) → χ e = α) :
    ∃ δ : C, δ ∈ newColors χ u ∧ δ ≠ α ∧
      ∃ w : Fin n, ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
        (selectedGraph χ r).Adj u w ∧ w ≠ u ∧
        w ∉ Set.range cyc.toHom ∧ e.val = s(u, w) ∧ χ e = δ := by
  obtain ⟨δ, hδ, hδα⟩ :=
    Finset.exists_mem_ne (Nat.lt_of_succ_le hnewu) α
  let d : newColors χ u := ⟨δ, hδ⟩
  let w : Fin n := newChoiceColorNeighbor χ r u d
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨(newChoiceIncidenceEdge χ r u d).val,
      SimpleGraph.edgeSet_mono le_top
        (newChoiceIncidenceEdge χ r u d).property.1⟩
  have hadj : (selectedGraph χ r).Adj u w :=
    newChoiceColorNeighbor_adj χ r u d
  have hpair : e.val = s(u, w) :=
    newChoiceIncidenceEdge_eq_pair χ r u d
  have hcolor : χ e = δ := newChoiceIncidenceEdge_color χ r u d
  have hwu : w ≠ u := ((selectedGraph χ r).ne_of_adj hadj).symm
  refine ⟨δ, hδ, hδα, w, e, hadj, hwu, ?_, hpair, hcolor⟩
  rintro ⟨i, hi⟩
  have hepair : e.val = s(u, cyc.toHom i) := by
    simpa only [← hi] using hpair
  exact hδα (hcolor.symm.trans (hcommon i e hepair))

end ErdosProblems.AntiRamseyCycleClaimOneSecondNewWitness
