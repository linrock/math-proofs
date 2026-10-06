module

public import PathEvenFiniteWindowPropagation
public import PathHighNewOddCycleForbiddenV4
public import PathHighNewStageTwoV6
public import PathSixNumericalExact
public import Mathlib.Tactic

@[expose] public section

/-!
Exact anti-Ramsey upper bound for `P_6` across all host orders `n ≥ 6`,
combining the `Fin 6` base case (`PathSixNumericalExact`), the high-NEW stages,
and finite-window strong induction (`PathEvenFiniteWindowPropagation`).
-/

namespace ErdosProblems.PathSixOriginalAllHostUpper1105

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

theorem pathSixEvenBound_eq (n : ℕ) (hn : 6 ≤ n) :
    max ((2 * 2 : ℕ).choose 2 + 1)
      ((2 - 1 : ℕ).choose 2 + (2 - 1) * (n - 2 + 1) + 2) = n + 1 := by
  have hA : ((2 * 2 : ℕ).choose 2 + 1) = 7 := by decide
  have hB : ((2 - 1 : ℕ).choose 2 + (2 - 1) * (n - 2 + 1) + 2) = n + 1 := by
    simp only [show (2 - 1 : ℕ) = 1 by decide,
      show (1 : ℕ).choose 2 = 0 by decide, zero_add, one_mul]
    omega
  rw [hA, hB]
  exact max_eq_right (by omega)

/-- The original anti-Ramsey P6 upper holds for every n>=6. The finite base,
original high NEW and graph choices are all derived internally. -/
theorem antiRamseyNum_path_six_le (n : ℕ) (hn : 6 ≤ n) :
    antiRamseyNum (pathGraph 6) n ≤ n + 1 := by
  classical
  have hhigh :
      ∀ (m : ℕ), 2 * 2 + 2 ≤ m →
        ∀ (C : Type) [DecidableEq C] (χ : TopEdgeLabeling (Fin m) C),
          (∀ v : Fin m, 2 ≤ (newColors χ v).card) →
          ∃ f : (pathGraph (2 * 2 + 2)).Copy (⊤ : SimpleGraph (Fin m)),
            IsRainbow f.toHom χ := by
    intro m hm C _ χ hnew
    by_contra h
    have hnoP :
        ∀ p : (pathGraph (2 * 2 + 2)).Copy (⊤ : SimpleGraph (Fin m)),
          ¬ IsRainbow p.toHom χ := by
      intro p hp
      exact h ⟨p, hp⟩
    have hnoC :=
      ErdosProblems.PathHighNewStageOne.no_rainbow_odd_cycle_of_high_new_and_no_even_path
        (ell := 2) (by decide) hm χ hnew hnoP
    exact h
      (ErdosProblems.PathHighNewStageTwo.rainbow_even_path_of_high_new_and_no_odd_cycle
        (ell := 2) χ (by decide) hm hnew hnoC)
  have hbases :
      ∀ (m : ℕ), 2 * 2 + 2 ≤ m →
        m ≤ 2 * 2 + 2 + (2 - 1) / 2 →
        antiRamseyNum (pathGraph (2 * 2 + 2)) m ≤
          max ((2 * 2 : ℕ).choose 2 + 1)
            ((2 - 1 : ℕ).choose 2 + (2 - 1) * (m - 2 + 1) + 2) := by
    intro m hm hwindow
    have hm6 : m = 6 := by omega
    subst m
    simpa only [show (2 * 2 + 2 : ℕ) = 6 by decide,
      show ((2 * 2 : ℕ).choose 2 + 1) = 7 by decide,
      show ((2 - 1 : ℕ).choose 2 + (2 - 1) * (6 - 2 + 1) + 2) = 7 by decide,
      max_self] using
      ErdosProblems.PathSixNumericalExact.antiRamseyNum_path_six_six_le_seven
  have hall :=
    ErdosProblems.AntiRamseyEvenPathFiniteWindow.antiRamseyNum_even_path_le_of_high_new_and_window
      2 (by decide) hhigh hbases
  have hwhole := hall n (by omega)
  simpa only [show (2 * 2 + 2 : ℕ) = 6 by decide,
    pathSixEvenBound_eq n hn] using hwhole

end ErdosProblems.PathSixOriginalAllHostUpper1105
