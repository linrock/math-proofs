module

public import CycleIndex1105
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

/-!
Constructs an injective `SimpleGraph.Copy (cycleGraph C.length) G` from a
simple cycle walk `C` using the `getVert` enumeration from `CycleIndex1105`.
-/

namespace ErdosProblems.PathUpperReduction.CycleCopy1105

open SimpleGraph

/-- Every actual simple cycle gives an injective actual cycle-graph copy with
exactly its original support, without a supplied copy or enumeration. -/
theorem exists_cycle_copy_with_exact_support {V : Type*} (G : SimpleGraph V)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) :
    ∃ c : SimpleGraph.Copy (cycleGraph C.length) G,
      (∀ i : Fin C.length, c i = C.getVert i.val) ∧
      Set.range c = {v | v ∈ C.support} := by
  have hthree : 3 ≤ C.length := hC.three_le_length
  let : NeZero C.length := ⟨by omega⟩
  have hone : (1 : Fin C.length).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hmap : ∀ i j : Fin C.length, (cycleGraph C.length).Adj i j →
      G.Adj (C.getVert i.val) (C.getVert j.val) := by
    intro i j hij
    rcases SimpleGraph.cycleGraph_adj'.mp hij with hijDiff | hjiDiff
    · have hdiff : i - j = (1 : Fin C.length) := by
        apply Fin.ext
        rw [hone]
        exact hijDiff
      have hi : i = j + 1 := sub_eq_iff_eq_add'.mp hdiff
      rw [hi, Fin.val_add, hone]
      exact (CycleIndex1105.closed_walk_getVert_cyclic_adj G C j).symm
    · have hdiff : j - i = (1 : Fin C.length) := by
        apply Fin.ext
        rw [hone]
        exact hjiDiff
      have hj : j = i + 1 := sub_eq_iff_eq_add'.mp hdiff
      rw [hj, Fin.val_add, hone]
      exact CycleIndex1105.closed_walk_getVert_cyclic_adj G C i
  let f : (cycleGraph C.length) →g G :=
    { toFun := fun i => C.getVert i.val
      map_rel' := fun {i j} hij => hmap i j hij }
  let c : SimpleGraph.Copy (cycleGraph C.length) G :=
    f.toCopy (CycleIndex1105.cycle_getVert_injective G C hC)
  refine ⟨c, ?_, ?_⟩
  · intro i
    rfl
  · change Set.range (fun i : Fin C.length => C.getVert i.val) = {v | v ∈ C.support}
    exact CycleIndex1105.cycle_getVert_range G C hC

end ErdosProblems.PathUpperReduction.CycleCopy1105
