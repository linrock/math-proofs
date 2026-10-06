module

public import PathHighNewOddPath
public import PathSevenSpanningBase
public import CycleDeletionPalette
public import PathMaxLower
public import Mathlib.Tactic

@[expose] public section

/-!
Exact anti-Ramsey formula for `P_7` across all host orders `n ≥ 7`, combining
the `Fin 7` base case (`PathSevenSpanningBase`), the odd high-NEW reduction
(`PathHighNewOddPath`), and strong induction on `n`.
-/

namespace ErdosProblems.PathSevenOriginalAllHostExact1105

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

theorem palette_le_of_smaller_host_bound {m q : ℕ} (hm : 7 ≤ m)
    (hIH : antiRamseyNum (pathGraph 7) m ≤ 2 * m - 2)
    (χ : TopEdgeLabeling (Fin (m + 1)) (Fin q))
    (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 7).Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬ IsRainbow f.toHom χ) : q ≤ 2 * (m + 1) - 2 := by
  classical
  by_contra hnot
  have hlarge : 2 * (m + 1) - 2 < q := by omega
  have hnew : ∀ v : Fin (m + 1), 3 ≤ (newColors χ v).card := by
    intro v
    have hdelete := surjective_color_count_le_antiRamseyNum_add_newColors
      (pathGraph 7) χ hχ hno v
    have hstep : q ≤ (2 * m - 2) + (newColors χ v).card :=
      le_trans hdelete (Nat.add_le_add_right hIH (newColors χ v).card)
    omega
  obtain ⟨f, hf⟩ :=
    ErdosProblems.PathHighNewOdd.exists_rainbow_odd_path_of_high_new
      (ell := 3) (by decide) (by omega) χ hnew
  exact hno f hf

theorem antiRamseyNum_path_seven_le (n : ℕ) :
    7 ≤ n → antiRamseyNum (pathGraph 7) n ≤ 2 * n - 2 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hbase : n = 7
    · subst n
      simpa using ErdosProblems.PathSevenSpanningBase.antiRamseyNum_path_seven_seven_le_twelve
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_add_one_of_ne_zero (by omega)
    have hm : 7 ≤ m := by omega
    have hIH : antiRamseyNum (pathGraph 7) m ≤ 2 * m - 2 :=
      ih m (by omega) hm
    unfold antiRamseyNum
    apply csSup_le'
    rintro q ⟨χ, hχ, hno⟩
    exact palette_le_of_smaller_host_bound hm hIH χ hχ hno

/-- The exact original-host P7 anti-Ramsey number on every n>=7. -/
theorem antiRamseyNum_path_seven_eq (n : ℕ) (hn : 7 ≤ n) :
    antiRamseyNum (pathGraph 7) n = 2 * n - 2 := by
  have hupper := antiRamseyNum_path_seven_le n hn
  have hlower := ErdosProblems.PathSetLower.pathMaxLower 7 n (by decide) hn
  have hOdd : Odd (7 : ℕ) := by decide
  have hc52 : (7 - 2 : ℕ).choose 2 = 10 := by decide
  have hc22 : (((7 - 1 : ℕ) / 2) - 1).choose 2 = 1 := by decide
  simp only [hOdd, ite_true] at hlower
  exact Nat.le_antisymm hupper (by omega)

/-- The literal fixed-k=7 slice of FC1105(ii), retaining all n>=7. -/
theorem path_seven_formal_conjectures_slice (n : ℕ) (hn : 7 ≤ n) :
    let ℓ := (7 - 1 : ℕ) / 2
    let ε := if Odd (7 : ℕ) then 1 else 2
    antiRamseyNum (pathGraph 7) n =
      max ((7 - 2 : ℕ).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  simp only [show Odd (7 : ℕ) by decide, ite_true]
  change antiRamseyNum (pathGraph 7) n =
    max ((5 : ℕ).choose 2 + 1)
      ((2 : ℕ).choose 2 + 2 * (n - 3 + 1) + 1)
  have hA : ((5 : ℕ).choose 2 + 1) = 11 := by decide
  have hB : ((2 : ℕ).choose 2 + 2 * (n - 3 + 1) + 1) = 2 * n - 2 := by
    simp only [show (2 : ℕ).choose 2 = 1 by decide]
    omega
  rw [hA, hB, max_eq_right (show (11 : ℕ) ≤ 2 * n - 2 by omega)]
  exact antiRamseyNum_path_seven_eq n hn

end ErdosProblems.PathSevenOriginalAllHostExact1105
