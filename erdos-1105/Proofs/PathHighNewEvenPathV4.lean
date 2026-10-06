module

public import PathHighNewOddCycleForbiddenV4
public import PathHighNewStageTwoV6

@[expose] public section

/-!
Even-path high-NEW assembly combining Stage 1 and Stage 2 on the original coloring.
-/

namespace ErdosProblems.PathHighNew

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Every original NEW-color set has at least ell colors, so the original
complete-host coloring has a rainbow path on 2 * ell + 2 vertices. -/
theorem exists_rainbow_even_path_of_high_new {ell : ℕ}
    (hell : 2 ≤ ell) (hn : 2 * ell + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) C)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card) :
    ∃ p : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
  classical
  by_contra h
  have hnoP :
      ∀ p : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
        ¬ IsRainbow p.toHom χ := by
    intro p hp
    exact h ⟨p, hp⟩
  have hnoC :=
    ErdosProblems.PathHighNewStageOne.no_rainbow_odd_cycle_of_high_new_and_no_even_path
      hell hn χ hnew hnoP
  exact h
    (ErdosProblems.PathHighNewStageTwo.rainbow_even_path_of_high_new_and_no_odd_cycle
      χ hell hn hnew hnoC)

end ErdosProblems.PathHighNew
