module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
This is the outside-independence step of the actual-cycle cover construction. It derives a contact of a whole outside component and a distinct outside
neighbor of that contact. It does not assume that either endpoint of the
given outside edge itself meets the cycle.
-/

namespace ErdosProblems.PathUpperReduction.ActualCycleOutside1105

open SimpleGraph

/-- An edge outside an actual cycle in a connected graph yields an actual path
on two more vertices than the cycle.  The attachment and both fresh outside
vertices are derived from the original graph. -/
theorem path_copy_of_outside_edge {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (x y : V) (hx : x ∉ C.support) (hy : y ∉ C.support)
    (hxy : G.Adj x y) : pathGraph (C.length + 2) ⊑ G := by
  classical
  let O : Set V := {z | z ∉ C.support}
  let H := G.induce O
  let xo : O := ⟨x, hx⟩
  let U : Set V := {z | ∃ hz : z ∈ O, H.Reachable xo ⟨z, hz⟩}
  have hxU : x ∈ U := ⟨hx, SimpleGraph.Reachable.rfl⟩
  have haU : a ∉ U := by
    rintro ⟨haO, _⟩
    exact haO C.start_mem_support
  obtain ⟨p⟩ := hconn x a
  obtain ⟨b, _, hbU, hbNotU⟩ := p.exists_boundary_dart U hxU haU
  obtain ⟨hzO, hzReach⟩ := hbU
  have hbCycle : b.snd ∈ C.support := by
    by_contra hbOutside
    have hbH : H.Adj ⟨b.fst, hzO⟩ ⟨b.snd, hbOutside⟩ := b.adj
    exact hbNotU ⟨hbOutside, hzReach.trans hbH.reachable⟩
  have hOutsideNeighbor : ∃ w : V, w ∉ C.support ∧ G.Adj b.fst w := by
    by_cases hzx : b.fst = x
    · refine ⟨y, hy, ?_⟩
      simpa only [hzx] using hxy
    · obtain ⟨q⟩ := hzReach.symm
      have hEndpoints : (⟨b.fst, hzO⟩ : O) ≠ xo := by
        intro h
        exact hzx (congrArg Subtype.val h)
      have hqNotNil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_ne hEndpoints
      exact ⟨q.snd.val, q.snd.property, q.adj_snd hqNotNil⟩
  obtain ⟨w, hwOutside, hzw⟩ := hOutsideNeighbor
  let rot := C.rotate b.snd hbCycle
  have hrot : rot.IsCycle := hC.rotate hbCycle
  have hzDrop : b.fst ∉ rot.dropLast.support := by
    intro hz
    rw [rot.support_dropLast hrot.not_nil] at hz
    have hzRot := List.mem_of_mem_dropLast hz
    exact hzO ((C.mem_support_rotate_iff b.snd hbCycle).mp hzRot)
  have hwDrop : w ∉ rot.dropLast.support := by
    intro hw
    rw [rot.support_dropLast hrot.not_nil] at hw
    have hwRot := List.mem_of_mem_dropLast hw
    exact hwOutside ((C.mem_support_rotate_iff b.snd hbCycle).mp hwRot)
  let q1 := SimpleGraph.Walk.cons b.adj rot.dropLast
  have hq1 : q1.IsPath := hrot.isPath_dropLast.cons hzDrop
  have hwQ1 : w ∉ q1.support := by
    intro hw
    change w ∈ b.fst :: rot.dropLast.support at hw
    rcases List.mem_cons.mp hw with hwz | hwRot
    · exact hzw.ne' hwz
    · exact hwDrop hwRot
  let q2 := SimpleGraph.Walk.cons hzw.symm q1
  have hq2 : q2.IsPath := hq1.cons hwQ1
  have hdrop : rot.dropLast.length + 1 = C.length := by
    calc
      rot.dropLast.length + 1 = rot.length :=
        SimpleGraph.Walk.length_dropLast_add_one hrot.not_nil
      _ = C.length := SimpleGraph.Walk.length_rotate C b.snd hbCycle
  have hlength : q2.length + 1 = C.length + 2 := by
    change (rot.dropLast.length + 1 + 1) + 1 = C.length + 2
    omega
  have hcopy : SimpleGraph.Copy (pathGraph (q2.length + 1)) G := hq2.pathGraphCopy
  rw [hlength] at hcopy
  exact ⟨hcopy⟩

/-- The vertices outside an actual `2*d`-cycle are independent when the original
connected graph excludes `P_(2*d+2)`.  This does not require a supplied outside
component, favorable attachment, minimum-degree or alternating-half premise. -/
theorem outside_independent_of_actual_cycle {V : Type*} (G : SimpleGraph V)
    (hconn : G.Connected) (d : ℕ) (hfree : (pathGraph (2 * d + 2)).Free G)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hLength : C.length = 2 * d) :
    ∀ x y : V, x ∉ C.support → y ∉ C.support → ¬G.Adj x y := by
  intro x y hx hy hxy
  have hcopy := path_copy_of_outside_edge G hconn C hC x y hx hy hxy
  rw [hLength] at hcopy
  exact hfree hcopy

end ErdosProblems.PathUpperReduction.ActualCycleOutside1105
