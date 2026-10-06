module

public import PathSixColorChoice
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
Seven distinctly colored edges on six named vertices form a rooted diamond
and two pendant edges. The color of the remaining outside-to-outside host edge
is arbitrary. A finite color choice constructs a rainbow Formal Conjectures
`pathGraph 6` copy.
-/

namespace ErdosProblems.AntiRamseyPathSixTransfer

open SimpleGraph
open ErdosProblems.AntiRamseyPathFiveUpper

def pathSixSevenColors {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin 6 → Fin n)
    (hu : Function.Injective u) : Fin 7 → C :=
  fun i =>
    if i = 0 then χ.get (u 2) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 1 then χ.get (u 2) (u 5) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 2 then χ.get (u 3) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 3 then χ.get (u 3) (u 5) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 4 then χ.get (u 4) (u 5) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 5 then χ.get (u 0) (u 2) ((top_adj _ _).mpr (hu.ne (by decide)))
    else χ.get (u 1) (u 2) ((top_adj _ _).mpr (hu.ne (by decide)))

/-- `true` chooses the first outside vertex as the pendant vertex, and
`false` chooses the second. The other vertex starts the six-vertex path. -/
def pathSixOrderIndex (s : Bool) (r : Fin 4) (i : Fin 6) : Fin 6 :=
  if i = 0 then (if s then 1 else 0)
  else if i = 1 then (if s then 0 else 1)
  else if i = 2 then 2
  else if r = 0 then
    if i = 3 then 4 else if i = 4 then 3 else 5
  else if r = 1 then
    if i = 3 then 5 else if i = 4 then 3 else 4
  else if r = 2 then
    if i = 3 then 4 else if i = 4 then 5 else 3
  else
    if i = 3 then 5 else if i = 4 then 4 else 3

theorem pathSixOrderIndex_injective (s : Bool) (r : Fin 4) :
    Function.Injective (pathSixOrderIndex s r) := by
  cases s <;> fin_cases r <;> decide

theorem pathSix_adj_succ (i : Fin 5) :
    (pathGraph 6).Adj (Fin.castSucc i) (Fin.succ i) := by
  rw [pathGraph_adj]
  left
  simp

def pathSixEdge (i : Fin 5) : (pathGraph 6).edgeSet :=
  ⟨s(Fin.castSucc i, Fin.succ i), pathSix_adj_succ i⟩

theorem pathSixEdge_surjective : Function.Surjective pathSixEdge := by
  intro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    change (pathGraph 6).Adj a b at he
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
      | exact ⟨4, Subtype.ext (by rfl)⟩
      | exact ⟨4, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact False.elim (by simp [pathGraph_adj] at he)

/-- The outside-to-outside edge color is unrestricted. -/
theorem rainbow_path_six_of_seven_colors {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (hd : Function.Injective (pathSixSevenColors χ u hu)) :
    ∃ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let z := χ.get (u 0) (u 1) ((top_adj _ _).mpr (hu.ne (by decide)))
  obtain ⟨s, r, hr⟩ := pathSix_color_choice (pathSixSevenColors χ u hu) hd z
  let w : Fin 6 → Fin n := u ∘ pathSixOrderIndex s r
  have hw : Function.Injective w := hu.comp (pathSixOrderIndex_injective s r)
  let φ : (pathGraph 6) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨w, by
      intro i j hij
      exact (top_adj _ _).mpr (hw.ne ((pathGraph 6).ne_of_adj hij))⟩
  let f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hw⟩
  have hcol (i : Fin 5) :
      (EdgeLabeling.pullback χ f.toHom) (pathSixEdge i) =
        pathSixChosenColors (pathSixSevenColors χ u hu) z s r i := by
    cases s <;> fin_cases r <;> fin_cases i <;>
      simp [pathSixEdge, f, φ, w, z, pathSixOrderIndex,
        pathSixChosenColors, pathSixCompress, pathSixCoreColors,
        pathSixPendantIndex, pathSixSevenColors, extendedPathColors,
        diamondPathEdgeIndex, EdgeLabeling.get, Hom.mapEdgeSet,
        Sym2.map_mk, Sym2.eq_swap]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  obtain ⟨i, rfl⟩ := pathSixEdge_surjective e₁
  obtain ⟨j, rfl⟩ := pathSixEdge_surjective e₂
  have hij : pathSixChosenColors (pathSixSevenColors χ u hu) z s r i =
      pathSixChosenColors (pathSixSevenColors χ u hu) z s r j := by
    simpa only [hcol] using heq
  exact congrArg pathSixEdge (hr hij)

end ErdosProblems.AntiRamseyPathSixTransfer
