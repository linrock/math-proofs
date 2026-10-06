module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
The cycle-tail
simplification follows current Mathlib Paths.lean:582, reducing the dependent
getVert endpoint before tail_cons/isPath_copy. The redundant omega after the
already reflexive length simplification is removed.
-/

namespace ErdosProblems.PathUpperReduction.CycleInsertion1105

open SimpleGraph

theorem cycle_of_fresh_endpoint_contact {V : Type*} (G : SimpleGraph V)
    {u v : V} (P : G.Walk u v) (hP : P.IsPath) (z : V)
    (hLength : 1 ≤ P.length) (hz : z ∉ P.support)
    (hzu : G.Adj z u) (hvz : G.Adj v z) :
    (SimpleGraph.Walk.cons hzu (P.concat hvz)).IsCycle ∧
      (SimpleGraph.Walk.cons hzu (P.concat hvz)).length = P.length + 2 := by
  classical
  constructor
  · apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.tail_cons,
        SimpleGraph.Walk.isPath_copy]
      exact hP.concat hz hvz
    · simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]
      omega
  · simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]

theorem cycle_of_dropLast_and_fresh_contact {V : Type*} (G : SimpleGraph V)
    {u : V} (C : G.Walk u u) (hC : C.IsCycle) (z : V)
    (hz : z ∉ C.support) (hzu : G.Adj z u) (hvz : G.Adj C.penultimate z) :
    (SimpleGraph.Walk.cons hzu (C.dropLast.concat hvz)).IsCycle ∧
      (SimpleGraph.Walk.cons hzu (C.dropLast.concat hvz)).length = C.length + 1 := by
  classical
  have hzDrop : z ∉ C.dropLast.support := by
    intro hz'
    rw [C.support_dropLast hC.not_nil] at hz'
    exact hz (List.mem_of_mem_dropLast hz')
  have hdrop : C.dropLast.length + 1 = C.length :=
    SimpleGraph.Walk.length_dropLast_add_one hC.not_nil
  have hthree : 3 ≤ C.length := hC.three_le_length
  have hpositive : 1 ≤ C.dropLast.length := by omega
  obtain ⟨hnew, hnewLength⟩ := cycle_of_fresh_endpoint_contact G C.dropLast
    hC.isPath_dropLast z hpositive hzDrop hzu hvz
  refine ⟨hnew, ?_⟩
  calc
    (SimpleGraph.Walk.cons hzu (C.dropLast.concat hvz)).length =
        C.dropLast.length + 2 := hnewLength
    _ = C.length + 1 := by omega

end ErdosProblems.PathUpperReduction.CycleInsertion1105
