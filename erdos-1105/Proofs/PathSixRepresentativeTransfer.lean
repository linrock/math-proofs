module

public import PathSixRainbowCopy
public import PathUpperRainbowBridge

@[expose] public section

/-!
The six-vertex rainbow transfer is applied to an arbitrary one-edge-per-color
representative choice, including a choice with a globally largest component.
The conclusion is a restricted structural exclusion, not the numerical
anti-Ramsey upper bound for all six-vertex paths.
-/

namespace ErdosProblems.AntiRamseyPathSixTransfer

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Six named vertices: a four-vertex core at positions `2..5` is complete,
and both outside vertices at positions `0,1` have selected edges to core
vertex `2`. The proof uses five of the six core edges. -/
structure RepresentativeStarCoreOn {V : Type*}
    (G : SimpleGraph V) (u : Fin 6 → V) : Prop where
  a_b : G.Adj (u 2) (u 3)
  a_c : G.Adj (u 2) (u 4)
  a_d : G.Adj (u 2) (u 5)
  b_c : G.Adj (u 3) (u 4)
  b_d : G.Adj (u 3) (u 5)
  c_d : G.Adj (u 4) (u 5)
  x_a : G.Adj (u 0) (u 2)
  y_a : G.Adj (u 1) (u 2)

def pathSixSevenEdgeIndex (i : Fin 7) : Sym2 (Fin 6) :=
  if i = 0 then s(2, 4)
  else if i = 1 then s(2, 5)
  else if i = 2 then s(3, 4)
  else if i = 3 then s(3, 5)
  else if i = 4 then s(4, 5)
  else if i = 5 then s(0, 2)
  else s(1, 2)

theorem pathSixSevenEdgeIndex_injective :
    Function.Injective pathSixSevenEdgeIndex := by
  decide

def representativeSevenEdge {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u)
    (i : Fin 7) : (selectedGraph χ r).edgeSet :=
  if i = 0 then ⟨s(u 2, u 4), h.a_c⟩
  else if i = 1 then ⟨s(u 2, u 5), h.a_d⟩
  else if i = 2 then ⟨s(u 3, u 4), h.b_c⟩
  else if i = 3 then ⟨s(u 3, u 5), h.b_d⟩
  else if i = 4 then ⟨s(u 4, u 5), h.c_d⟩
  else if i = 5 then ⟨s(u 0, u 2), h.x_a⟩
  else ⟨s(u 1, u 2), h.y_a⟩

theorem representativeSevenEdge_val {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u)
    (i : Fin 7) :
    (representativeSevenEdge χ r u h i).val =
      Sym2.map u (pathSixSevenEdgeIndex i) := by
  fin_cases i <;>
    simp [representativeSevenEdge, pathSixSevenEdgeIndex, Sym2.map_mk]

theorem representativeSevenEdge_injective {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u) :
    Function.Injective (representativeSevenEdge χ r u h) := by
  intro i j he
  apply pathSixSevenEdgeIndex_injective
  apply Sym2.map.injective hu
  calc
    Sym2.map u (pathSixSevenEdgeIndex i) =
        (representativeSevenEdge χ r u h i).val :=
      (representativeSevenEdge_val χ r u h i).symm
    _ = (representativeSevenEdge χ r u h j).val := congrArg Subtype.val he
    _ = Sym2.map u (pathSixSevenEdgeIndex j) :=
      representativeSevenEdge_val χ r u h j

theorem pathSixSevenColors_eq_selectedColor {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u)
    (i : Fin 7) :
    pathSixSevenColors χ u hu i =
      selectedColor χ r (representativeSevenEdge χ r u h i) := by
  fin_cases i <;>
    simp [pathSixSevenColors, representativeSevenEdge, selectedColor,
      EdgeLabeling.get]

/-- A representative containing the selected complete four-vertex core and
two edges from distinct outside vertices to a common core vertex forces a
rainbow `pathGraph 6.Copy ⊤` in the original complete-graph coloring. -/
theorem rainbow_path_six_of_representative_starCore {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u) :
    ∃ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  have hd : Function.Injective (pathSixSevenColors χ u hu) := by
    intro i j he
    apply representativeSevenEdge_injective χ r u hu h
    apply selectedColor_injective χ r
    exact (pathSixSevenColors_eq_selectedColor χ r u hu h i).symm.trans
      (he.trans (pathSixSevenColors_eq_selectedColor χ r u hu h j))
  exact rainbow_path_six_of_seven_colors χ u hu hd

/-- The exact Formal Conjectures no-rainbow-`P₆` premise excludes this
six-vertex structure in *every* one-edge-per-color representative choice. -/
theorem no_representative_starCore_of_no_rainbow_path_six {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ)
    (hno : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (u : Fin 6 → Fin n) (hu : Function.Injective u) :
    ¬ RepresentativeStarCoreOn (selectedGraph χ r) u := by
  intro h
  obtain ⟨f, hf⟩ := rainbow_path_six_of_representative_starCore χ r u hu h
  exact hno f hf

end ErdosProblems.AntiRamseyPathSixTransfer
