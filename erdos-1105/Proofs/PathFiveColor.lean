module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
For the five-vertex path lower bound, color each edge incident to vertex zero by
its other endpoint. All edges among the remaining vertices receive color zero.
-/

namespace ErdosProblems.AntiRamseyPathFive

open SimpleGraph

/-- Yuan's star construction at `k = 5`, with `n` colors on `K_n`. -/
def starColor (n : ℕ) [NeZero n] : TopEdgeLabeling (Fin n) (Fin n) :=
  EdgeLabeling.mk
    (fun a b _ => if a = 0 ∨ b = 0 then max a b else 0)
    (by intro a b _; simp [or_comm, max_comm])

@[simp] theorem starColor_get {n : ℕ} [NeZero n] (a b : Fin n)
    (hab : (⊤ : SimpleGraph (Fin n)).Adj a b) :
    (starColor n).get a b hab = if a = 0 ∨ b = 0 then max a b else 0 := by
  rfl

/-- An edge away from the distinguished vertex has color zero. -/
theorem starColor_get_nonincident {n : ℕ} [NeZero n] (a b : Fin n)
    (hab : (⊤ : SimpleGraph (Fin n)).Adj a b)
    (ha : a ≠ 0) (hb : b ≠ 0) : (starColor n).get a b hab = 0 := by
  simp [starColor_get, ha, hb]

/-- Every label appears: nonzero label `i` occurs on `{0,i}`, and label zero
occurs on `{1,2}`. -/
theorem starColor_surjective (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    Function.Surjective (starColor n) := by
  intro i
  by_cases hi : i = (0 : Fin n)
  · subst i
    let a : Fin n := ⟨1, by omega⟩
    let b : Fin n := ⟨2, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [a, b] at hv
    have ha : a ≠ (0 : Fin n) := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [a] at hv
    have hb : b ≠ (0 : Fin n) := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [b] at hv
    refine ⟨⟨s(a, b), ((⊤ : SimpleGraph (Fin n)).mem_edgeSet).2
      ((top_adj a b).2 hab)⟩, ?_⟩
    exact starColor_get_nonincident a b ((top_adj a b).2 hab) ha hb
  · refine ⟨⟨s((0 : Fin n), i), ((⊤ : SimpleGraph (Fin n)).mem_edgeSet).2
      ((top_adj 0 i).2 (Ne.symm hi))⟩, ?_⟩
    change (starColor n).get 0 i ((top_adj 0 i).2 (Ne.symm hi)) = i
    rw [starColor_get]
    simp

end ErdosProblems.AntiRamseyPathFive
