module

public import CycleBlockMap
public import Mathlib.Combinatorics.SimpleGraph.Copy

@[expose] public section

/-!
The first `n / m` consecutive blocks are full. Their vertices are indexed by
`Fin (n / m) × Fin m`, giving a canonical injection into `Fin n` and a
complete-graph copy for each individual block.
-/

namespace ErdosProblems.AntiRamseyCycleBlockCount

open SimpleGraph

/-- Vertex `i` of complete block `b`, indexed in the host `Fin n`. -/
def fullBlockVertex (m n : ℕ) (_hm : 0 < m)
    (b : Fin (n / m)) (i : Fin m) : Fin n := by
  have hb : (b.val + 1) * m ≤ (n / m) * m :=
    Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr b.isLt)
  have hb' : m + m * b.val ≤ (n / m) * m := by
    calc
      m + m * b.val = (b.val + 1) * m := by ring
      _ ≤ (n / m) * m := hb
  have hq : (n / m) * m ≤ n := Nat.div_mul_le_self n m
  exact ⟨i.val + m * b.val,
    lt_of_lt_of_le (Nat.add_lt_add_right i.isLt (m * b.val)) (hb'.trans hq)⟩

@[simp] theorem fullBlockVertex_val (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (i : Fin m) :
    (fullBlockVertex m n hm b i).val = i.val + m * b.val := rfl

/-- Every indexed full-block vertex maps back to its block under division. -/
theorem fullBlockVertex_block (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (i : Fin m) :
    consecutiveBlockMap m n (fullBlockVertex m n hm b i) =
      Fin.castLE (Nat.le_succ _) b := by
  apply Fin.ext
  simp only [consecutiveBlockMap_val, Fin.val_castLE, fullBlockVertex_val]
  rw [Nat.add_mul_div_left _ _ hm]
  simp [Nat.div_eq_of_lt i.isLt]

/-- The full-block coordinate pair is recoverable from its host vertex. -/
theorem fullBlockVertex_injective (m n : ℕ) (hm : 0 < m) :
    Function.Injective (fun p : Fin (n / m) × Fin m =>
      fullBlockVertex m n hm p.1 p.2) := by
  intro p q hpq
  have hb : p.1 = q.1 := by
    have hπ := congrArg (consecutiveBlockMap m n) hpq
    rw [fullBlockVertex_block, fullBlockVertex_block] at hπ
    exact Fin.castLE_injective (Nat.le_succ _) hπ
  have hi : p.2 = q.2 := by
    have hval := congrArg Fin.val hpq
    simp only [fullBlockVertex_val] at hval
    rw [hb] at hval
    exact Fin.ext (Nat.add_right_cancel hval)
  exact Prod.ext hb hi

/-- The full block `b` forms a copy of `K_m` in the host `K_n`. -/
def fullBlockCopy (m n : ℕ) (hm : 0 < m) (b : Fin (n / m)) :
    (⊤ : SimpleGraph (Fin m)).Copy (⊤ : SimpleGraph (Fin n)) := by
  let f : Fin m ↪ Fin n :=
    ⟨fullBlockVertex m n hm b, by
      intro i j h
      have hval := congrArg Fin.val h
      simp only [fullBlockVertex_val] at hval
      exact Fin.ext (Nat.add_right_cancel hval)⟩
  exact (SimpleGraph.Embedding.completeGraph f).toCopy

@[simp] theorem fullBlockCopy_apply (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (i : Fin m) :
    fullBlockCopy m n hm b i = fullBlockVertex m n hm b i := rfl

end ErdosProblems.AntiRamseyCycleBlockCount
