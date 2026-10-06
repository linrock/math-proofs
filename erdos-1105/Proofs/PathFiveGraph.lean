module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

namespace ErdosProblems.AntiRamseyPathFive

open SimpleGraph

/-- The index `i : Fin 4` names the corresponding consecutive edge of `P₅`. -/
theorem path_five_adj_succ (i : Fin 4) :
    (pathGraph 5).Adj (Fin.castSucc i) (Fin.succ i) := by
  rw [pathGraph_adj]
  left
  simp

/-- The `i`th edge of the path `P₅`. -/
def pathFiveEdge (i : Fin 4) : (pathGraph 5).edgeSet :=
  ⟨s(Fin.castSucc i, Fin.succ i), path_five_adj_succ i⟩

theorem pathFiveEdge_injective : Function.Injective pathFiveEdge := by
  decide

/-- Among the four edges of a copied five-vertex path, at least two avoid any given vertex.
The indices `i, j : Fin 4` specify the edges from `Fin.castSucc i` to `Fin.succ i`. -/
theorem path_five_copy_two_edges_avoid_vertex {n : ℕ}
    (f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n))) (a : Fin n) :
    ∃ i j : Fin 4, i ≠ j ∧
      f (Fin.castSucc i) ≠ a ∧ f (Fin.succ i) ≠ a ∧
      f (Fin.castSucc j) ≠ a ∧ f (Fin.succ j) ≠ a := by
  by_cases h₀ : a = f (0 : Fin 5)
  · refine ⟨1, 2, by decide, ?_, ?_, ?_, ?_⟩
    · simpa [h₀] using f.injective.ne (show (1 : Fin 5) ≠ 0 by decide)
    · simpa [h₀] using f.injective.ne (show (2 : Fin 5) ≠ 0 by decide)
    · simpa [h₀] using f.injective.ne (show (2 : Fin 5) ≠ 0 by decide)
    · simpa [h₀] using f.injective.ne (show (3 : Fin 5) ≠ 0 by decide)
  by_cases h₁ : a = f (1 : Fin 5)
  · refine ⟨2, 3, by decide, ?_, ?_, ?_, ?_⟩
    · simpa [h₁] using f.injective.ne (show (2 : Fin 5) ≠ 1 by decide)
    · simpa [h₁] using f.injective.ne (show (3 : Fin 5) ≠ 1 by decide)
    · simpa [h₁] using f.injective.ne (show (3 : Fin 5) ≠ 1 by decide)
    · simpa [h₁] using f.injective.ne (show (4 : Fin 5) ≠ 1 by decide)
  by_cases h₂ : a = f (2 : Fin 5)
  · refine ⟨0, 3, by decide, ?_, ?_, ?_, ?_⟩
    · simpa [h₂] using f.injective.ne (show (0 : Fin 5) ≠ 2 by decide)
    · simpa [h₂] using f.injective.ne (show (1 : Fin 5) ≠ 2 by decide)
    · simpa [h₂] using f.injective.ne (show (3 : Fin 5) ≠ 2 by decide)
    · simpa [h₂] using f.injective.ne (show (4 : Fin 5) ≠ 2 by decide)
  by_cases h₃ : a = f (3 : Fin 5)
  · refine ⟨0, 1, by decide, ?_, ?_, ?_, ?_⟩
    · simpa [h₃] using f.injective.ne (show (0 : Fin 5) ≠ 3 by decide)
    · simpa [h₃] using f.injective.ne (show (1 : Fin 5) ≠ 3 by decide)
    · simpa [h₃] using f.injective.ne (show (1 : Fin 5) ≠ 3 by decide)
    · simpa [h₃] using f.injective.ne (show (2 : Fin 5) ≠ 3 by decide)
  refine ⟨0, 1, by decide, ?_, ?_, ?_, ?_⟩
  · simpa using Ne.symm h₀
  · simpa using Ne.symm h₁
  · simpa using Ne.symm h₁
  · simpa using Ne.symm h₂

end ErdosProblems.AntiRamseyPathFive
