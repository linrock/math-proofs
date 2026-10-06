module

public import PathUpperOriginalLongFamilyInduction
public import PathActualAllShort
public import PathMiddleExtraction1105
public import PathActualMiddle

@[expose] public section

/-!
This is the original proper-first
branch under the genuine FULL smaller-complete-host IH.

This direct composition introduces no equivalent helper,
new graph/cap lemma or desired conclusion premise.

The public theorem supplies no high palette, NoLong, actual component, longest
path or next-order freedom premise. High q is introduced only by contradiction;
the existing long-IH theorem and actual case extraction derive the case data. The FULL IH remains a premise. Connected first support, small orders, induction
bases and the unconditional universal path(ii) theorem are outside this result.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q k : ℕ}

/-- The original palette bound throughout the proper-first branch, under the
FULL smaller-complete-host IH. Every structural path case is derived on the
actual SAME-R family; no favorable component or numerical cap is supplied. -/
theorem OriginalResidualCutFamily.original_color_count_le_formula_of_proper_first_component
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (hk : 8 ≤ k) (hkn : k ≤ n)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n) :
    q ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  classical
  by_contra hbound
  have hhigh : ErdosProblems.PathLemmaFourScalar.pathFormula n k < q := by omega
  have hlong := F.no_long_retained_path_of_proper_first_component
    hproper (by omega) hkn hno hIH hhigh
  rcases F.all_short_or_middle_component_of_no_long hk hlong with
    hshort | ⟨C, a, hlower, hupper, ⟨A⟩, hheadFree⟩
  · have hshortBound := F.original_color_count_le_formula_of_all_short
      hproper (by omega) hkn hshort
    exact (not_lt_of_ge hshortBound) hhigh
  · have hmiddleBound := F.original_color_count_le_formula_of_middle_component
      hproper hk hkn hno C A hheadFree hlower hupper
    omega

end ErdosProblems.PathUpperReduction

