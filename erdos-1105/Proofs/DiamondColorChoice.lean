module

public import Mathlib

@[expose] public section

namespace ErdosProblems.AntiRamseyPathFiveUpper

/-- Four Hamiltonian paths in a diamond, rooted at a degree-two vertex.
Values at indices 1, 2, 3 index their three edges among the five
diamond edges ac, ad, bc, bd, cd (numbered 0, 1, 2, 3, 4). -/
def diamondPathEdgeIndex (r : Fin 4) (i : Fin 4) : Fin 5 :=
  if r = 0 then
    if i = 1 then 0 else if i = 2 then 2 else 3
  else if r = 1 then
    if i = 1 then 1 else if i = 2 then 3 else 2
  else if r = 2 then
    if i = 1 then 0 else if i = 2 then 4 else 3
  else
    if i = 1 then 1 else if i = 2 then 4 else 2

/-- Color of the four consecutive edges of a five-vertex path formed by
attaching a new vertex to a rooted Hamiltonian path in the diamond. -/
def extendedPathColors {C : Type*} (d : Fin 5 → C) (x : C)
    (r : Fin 4) (i : Fin 4) : C :=
  if i = 0 then x else d (diamondPathEdgeIndex r i)

/-- The rooted diamond has a Hamiltonian path avoiding any one extra edge
color, provided its five edge colors are distinct. -/
theorem diamond_color_choice {C : Type*} (d : Fin 5 → C) (hd : Function.Injective d)
    (x : C) :
    ∃ r : Fin 4, Function.Injective (extendedPathColors d x r) := by
  by_cases h₀ : x = d 0
  · refine ⟨1, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]
  by_cases h₁ : x = d 1
  · refine ⟨0, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]
  by_cases h₂ : x = d 2
  · refine ⟨2, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]
  by_cases h₃ : x = d 3
  · refine ⟨3, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]
  refine ⟨0, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]

end ErdosProblems.AntiRamseyPathFiveUpper
