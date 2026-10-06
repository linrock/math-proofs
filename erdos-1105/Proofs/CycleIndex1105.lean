module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
The actual walk itself supplies the finite cycle enumeration. Indices are
0,...,C.length-1; the repeated final vertex is represented by index zero. These helpers derive injectivity, the full actual support and cyclic-next
adjacency without any supplied embedding, favorable rotation or copy.
-/

namespace ErdosProblems.PathUpperReduction.CycleIndex1105

open SimpleGraph

/-- Before its repeated closing vertex, an actual simple cycle enumerates
distinct original vertices. -/
theorem cycle_getVert_injective {V : Type*} (G : SimpleGraph V) {a : V}
    (C : G.Walk a a) (hC : C.IsCycle) :
    Function.Injective (fun i : Fin C.length => C.getVert i.val) := by
  intro i j hij
  have hiBound := i.isLt
  have hjBound := j.isLt
  apply Fin.ext
  exact hC.getVert_injOn'
    (show i.val ≤ C.length - 1 from by omega)
    (show j.val ≤ C.length - 1 from by omega) hij

/-- The finite enumeration contains every actual cycle vertex, including the
start vertex, and introduces no vertex outside its original support. -/
theorem cycle_getVert_range {V : Type*} (G : SimpleGraph V) {a : V}
    (C : G.Walk a a) (hC : C.IsCycle) :
    Set.range (fun i : Fin C.length => C.getVert i.val) = {v | v ∈ C.support} := by
  have hpositive : 0 < C.length := by
    have hthree := hC.three_le_length
    omega
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact C.getVert_mem_support i.val
  · intro hv
    obtain ⟨j, hjv, hjLength⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
    by_cases hj : j < C.length
    · exact ⟨⟨j, hj⟩, hjv⟩
    · have hjLast : j = C.length := by omega
      refine ⟨⟨0, hpositive⟩, ?_⟩
      change C.getVert 0 = v
      rw [C.getVert_zero]
      rw [hjLast, C.getVert_length] at hjv
      exact hjv

/-- Cyclic successor indices of an actual closed walk give original adjacent
vertices.  The last index wraps to zero by the actual endpoint equality. -/
theorem closed_walk_getVert_cyclic_adj {V : Type*} (G : SimpleGraph V) {a : V}
    (C : G.Walk a a) (i : Fin C.length) :
    G.Adj (C.getVert i.val) (C.getVert ((i.val + 1) % C.length)) := by
  have hiBound := i.isLt
  have hadj := C.adj_getVert_succ hiBound
  by_cases hi : i.val + 1 < C.length
  · rw [Nat.mod_eq_of_lt hi]
    exact hadj
  · have hiLast : i.val + 1 = C.length := by omega
    rw [hiLast, C.getVert_length] at hadj
    rw [hiLast, Nat.mod_self, C.getVert_zero]
    exact hadj

end ErdosProblems.PathUpperReduction.CycleIndex1105
