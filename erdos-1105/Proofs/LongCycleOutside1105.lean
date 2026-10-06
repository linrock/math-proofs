module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fintype.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
This supplies the longer-cycle exclusion needed by the actual-cycle contact
argument. No favorable contact, supplied path,
extra cycle-cap oracle or added edge occurs in the final statement.
-/

namespace ErdosProblems.PathUpperReduction.LongCycleOutside1105

open SimpleGraph

/-- A simple cycle has exactly its length many distinct actual vertices. -/
theorem support_finset_card_of_cycle {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) :
    C.support.toFinset.card = C.length := by
  classical
  have hsame : C.support.toFinset = C.support.tail.toFinset := by
    calc
      C.support.toFinset = (a :: C.support.tail).toFinset :=
        congrArg List.toFinset C.cons_tail_support.symm
      _ = insert a C.support.tail.toFinset := by rw [List.toFinset_cons]
      _ = C.support.tail.toFinset :=
        Finset.insert_eq_of_mem (List.mem_toFinset.mpr
          (C.end_mem_tail_support hC.not_nil))
  rw [hsame, List.toFinset_card_of_nodup hC.support_nodup]
  simp only [List.length_tail, SimpleGraph.Walk.length_support, Nat.add_sub_cancel]

/-- Any actual vertex outside a cycle in the original connected graph forces
an actual path with one more vertex than that cycle. -/
theorem path_copy_of_cycle_with_outside_vertex {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (z : V) (hz : z ∉ C.support) : pathGraph (C.length + 1) ⊑ G := by
  classical
  let O : Set V := {w | w ∉ C.support}
  have hzO : z ∈ O := hz
  have haO : a ∉ O := fun ha => ha C.start_mem_support
  obtain ⟨p⟩ := hconn z a
  obtain ⟨b, _, hbOutside, hbNotOutside⟩ := p.exists_boundary_dart O hzO haO
  have hbCycle : b.snd ∈ C.support := by
    by_contra hb
    exact hbNotOutside hb
  let rot := C.rotate b.snd hbCycle
  have hrot : rot.IsCycle := hC.rotate hbCycle
  have hbDrop : b.fst ∉ rot.dropLast.support := by
    intro hb
    rw [rot.support_dropLast hrot.not_nil] at hb
    have hbRot := List.mem_of_mem_dropLast hb
    exact hbOutside ((C.mem_support_rotate_iff b.snd hbCycle).mp hbRot)
  let q := SimpleGraph.Walk.cons b.adj rot.dropLast
  have hq : q.IsPath := hrot.isPath_dropLast.cons hbDrop
  have hdrop : rot.dropLast.length + 1 = C.length := by
    calc
      rot.dropLast.length + 1 = rot.length :=
        SimpleGraph.Walk.length_dropLast_add_one hrot.not_nil
      _ = C.length := SimpleGraph.Walk.length_rotate C b.snd hbCycle
  have hlength : q.length + 1 = C.length + 1 := by
    change (rot.dropLast.length + 1) + 1 = C.length + 1
    omega
  have hcopy : (pathGraph (q.length + 1)).Copy G := hq.pathGraphCopy
  rw [hlength] at hcopy
  exact ⟨hcopy⟩

/-- Original host surplus and path freedom exclude an actual cycle on one
fewer vertices than the forbidden path. No separate cycle cap is assumed. -/
theorem no_cycle_of_order_one_below_forbidden_path {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (d : ℕ)
    (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) : C.length ≠ 2 * d + 1 := by
  classical
  intro hlength
  have hsmall : C.support.toFinset.card < (Finset.univ : Finset V).card := by
    rw [support_finset_card_of_cycle G C hC, Finset.card_univ]
    omega
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hzOutside : z ∉ C.support := by
    intro hzC
    exact hz (List.mem_toFinset.mpr hzC)
  have hcopy := path_copy_of_cycle_with_outside_vertex G hconn C hC z hzOutside
  have heq : C.length + 1 = 2 * d + 2 := by omega
  rw [heq] at hcopy
  exact hfree hcopy

end ErdosProblems.PathUpperReduction.LongCycleOutside1105
