module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import DiamondColorChoice

@[expose] public section

namespace ErdosProblems.AntiRamseyPathFiveUpper

open SimpleGraph

/-- The five diamond edges ac, ad, bc, bd, cd, where an injective map
u names v, a, b, c, d at indices 0, 1, 2, 3, 4. -/
def diamondEdgeColors {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin 5 → Fin n)
    (hu : Function.Injective u) : Fin 5 → C :=
  fun i =>
    if i = 0 then χ.get (u 1) (u 3) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 1 then χ.get (u 1) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 2 then χ.get (u 2) (u 3) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 3 then χ.get (u 2) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))
    else χ.get (u 3) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))

/-- Vertex orders v-a-c-b-d, v-a-d-b-c, v-a-c-d-b, v-a-d-c-b. -/
def diamondPathVertexIndex (r : Fin 4) (i : Fin 5) : Fin 5 :=
  if r = 0 then
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 3 else if i = 3 then 2 else 4
  else if r = 1 then
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 4 else if i = 3 then 2 else 3
  else if r = 2 then
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 3 else if i = 3 then 4 else 2
  else
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 4 else if i = 3 then 3 else 2

theorem diamondPathVertexIndex_injective (r : Fin 4) :
    Function.Injective (diamondPathVertexIndex r) := by
  fin_cases r <;> decide

theorem path_five_adj_succ (i : Fin 4) :
    (pathGraph 5).Adj (Fin.castSucc i) (Fin.succ i) := by
  rw [pathGraph_adj]
  left
  simp

def pathFiveEdge (i : Fin 4) : (pathGraph 5).edgeSet :=
  ⟨s(Fin.castSucc i, Fin.succ i), path_five_adj_succ i⟩

theorem pathFiveEdge_surjective : Function.Surjective pathFiveEdge := by
  intro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    change (pathGraph 5).Adj a b at he
    fin_cases a <;> fin_cases b <;>
      first
      | exact ⟨0, Subtype.ext (by rfl)⟩
      | exact ⟨0, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨1, Subtype.ext (by rfl)⟩
      | exact ⟨1, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨2, Subtype.ext (by rfl)⟩
      | exact ⟨2, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨3, Subtype.ext (by rfl)⟩
      | exact ⟨3, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact False.elim (by simp [pathGraph_adj] at he)

/-- Five distinct vertices whose five diamond edges have five distinct
colors force a rainbow five-vertex path, regardless of the remaining
edge colors. The missing diamond edge a-b is never used. -/
theorem rainbow_path_five_of_rainbow_diamond {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin 5 → Fin n)
    (hu : Function.Injective u)
    (hd : Function.Injective (diamondEdgeColors χ u hu)) :
    ∃ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  let x := χ.get (u 0) (u 1) ((top_adj _ _).mpr (hu.ne (by decide)))
  obtain ⟨r, hr⟩ := diamond_color_choice (diamondEdgeColors χ u hu) hd x
  let w : Fin 5 → Fin n := u ∘ diamondPathVertexIndex r
  have hw : Function.Injective w := hu.comp (diamondPathVertexIndex_injective r)
  let φ : (pathGraph 5) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨w, by
      intro i j hij
      exact (top_adj _ _).mpr (hw.ne ((pathGraph 5).ne_of_adj hij))⟩
  let f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hw⟩
  have hcol (i : Fin 4) :
      (EdgeLabeling.pullback χ f.toHom) (pathFiveEdge i) =
        extendedPathColors (diamondEdgeColors χ u hu) x r i := by
    fin_cases r <;> fin_cases i <;>
      simp [pathFiveEdge, f, φ, w, x, diamondPathVertexIndex,
        extendedPathColors, diamondPathEdgeIndex, diamondEdgeColors,
        EdgeLabeling.get, Hom.mapEdgeSet, Sym2.map_mk, Sym2.eq_swap]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  obtain ⟨i, rfl⟩ := pathFiveEdge_surjective e₁
  obtain ⟨j, rfl⟩ := pathFiveEdge_surjective e₂
  have hij : extendedPathColors (diamondEdgeColors χ u hu) x r i =
      extendedPathColors (diamondEdgeColors χ u hu) x r j := by
    simpa only [hcol] using heq
  exact congrArg pathFiveEdge (hr hij)

end ErdosProblems.AntiRamseyPathFiveUpper
