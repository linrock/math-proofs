module

public import PathSixOriginalColourEight
public import PathMaxLower
public import PathSixSixConditionalCollapseV2

@[expose] public section

/-! literal Fin6 numerical capstone. -/

namespace ErdosProblems.PathSixNumericalExact

open SimpleGraph
open ErdosProblems.PathSixOriginalColourEight
open ErdosProblems.AntiRamseyPathSixSixConditionalCollapse

/-- Every original surjective coloring of K6 avoiding literal rainbow P6
uses at most seven colors. No owner/graph witness is supplied. -/
theorem palette_le_seven_of_no_rainbow_path_six {q : ℕ}
    (χ : TopEdgeLabeling (Fin 6) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
      ¬ IsRainbow f.toHom χ) : q ≤ 7 := by
  by_contra hq
  exact no_surjective_no_rainbow_path_six_palette_ge_eight (by omega) χ hχ hno

/-- Literal original anti-Ramsey upper at n=k=6, consuming the checked
conditional numerical adapter after deriving its eight-color input. -/
theorem antiRamseyNum_path_six_six_le_seven :
    antiRamseyNum (pathGraph 6) 6 ≤ 7 := by
  apply antiRamseyNum_pathGraph_six_six_le_seven_of_eight_exclusion
  rintro ⟨χ, hχ, hno⟩
  exact no_surjective_no_rainbow_path_six_palette_ge_eight (by decide) χ hχ hno

/-- Literal original equality at n=k=6. The registered maximum lower
construction and its numerical reduction are reused through the adapter. -/
theorem antiRamseyNum_path_six_six_eq_seven :
    antiRamseyNum (pathGraph 6) 6 = 7 := by
  apply antiRamseyNum_pathGraph_six_six_eq_seven_of_eight_exclusion
  rintro ⟨χ, hχ, hno⟩
  exact no_surjective_no_rainbow_path_six_palette_ge_eight (by decide) χ hχ hno

end ErdosProblems.PathSixNumericalExact
