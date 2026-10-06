module

public import OddPathsUniversalExact1105
public import PathSixOriginalAllHostExact1105
public import LiteralPathEqualityFiniteWindows1105
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Unified Lean 4.35.0-rc2 reduction for Erdős #1105 Part (ii) (`erdos_1105.parts.ii`):
1. Unconditional exact formula for all odd path orders `k ≥ 5` and all `n ≥ k`.
2. Unconditional exact formula for `k = 6` (`P_6`) and all `n ≥ 6`.
3. Exact equivalence reducing the entire universal statement `erdos_1105.parts.ii`
   to the finite base window `2 * ℓ + 2 ≤ n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2` for even
   path orders `k = 2 * ℓ + 2` with `ℓ ≥ 3` (`k ≥ 8`).
-/

namespace ErdosProblems.PathUpperReduction.Erdos1105UniversalPathReduction

open SimpleGraph
open ErdosProblems.PathUpperReduction.OddPathsUniversalExact1105

/-- For any fixed `ℓ ≥ 2` (`k = 2 * ℓ + 2`), if the upper bound holds on the finite
host window `2 * ℓ + 2 ≤ n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2`, then the exact Formal Conjectures
equality holds for every `n ≥ 2 * ℓ + 2`. -/
theorem even_path_exact_of_finite_window (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (hwindow : ∀ n : ℕ, 2 * ℓ + 2 ≤ n → n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2 →
      antiRamseyNum (pathGraph (2 * ℓ + 2)) n ≤
        max ((2 * ℓ).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + 2)) :
    ∀ n : ℕ, 2 * ℓ + 2 ≤ n →
      let k := 2 * ℓ + 2
      let ℓ' := (k - 1) / 2
      let ε := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ℓ' - 1).choose 2 + (ℓ' - 1) * (n - ℓ' + 1) + ε) := by
  intro n hn
  have hhigh : ∀ m : ℕ, 2 * ℓ + 2 ≤ m →
      ∀ (C : Type) [DecidableEq C] (χ : TopEdgeLabeling (Fin m) C),
        (∀ v : Fin m, ℓ ≤ (ErdosProblems.AntiRamseyCycleNewColors.newColors χ v).card) →
        ∃ f : (pathGraph (2 * ℓ + 2)).Copy (⊤ : SimpleGraph (Fin m)),
          IsRainbow f.toHom χ := by
    intro m hm C _ χ hnew
    exact ErdosProblems.PathHighNew.exists_rainbow_even_path_of_high_new hℓ hm χ hnew
  have hupper :=
    ErdosProblems.AntiRamseyEvenPathFiniteWindow.antiRamseyNum_even_path_le_of_high_new_and_window
      ℓ hℓ hhigh hwindow n hn
  have heven : ¬ Odd (2 * ℓ + 2) := by rintro ⟨r, hr⟩; omega
  have hquot : (2 * ℓ + 2 - 1) / 2 = ℓ := by omega
  have hsub : 2 * ℓ + 2 - 2 = 2 * ℓ := by omega
  have hupper' :
      antiRamseyNum (pathGraph (2 * ℓ + 2)) n ≤
        max (((2 * ℓ + 2) - 2).choose 2 + 1)
          ((((2 * ℓ + 2 - 1) / 2) - 1).choose 2 +
            (((2 * ℓ + 2 - 1) / 2) - 1) * (n - ((2 * ℓ + 2 - 1) / 2) + 1) +
              (if Odd (2 * ℓ + 2) then 1 else 2)) := by
    simpa only [hquot, hsub, ite_eq_right heven] using hupper
  have hlower :=
    ErdosProblems.PathSetLower.pathMaxLower (2 * ℓ + 2) n (by omega) hn
  exact Nat.le_antisymm hupper' hlower

/-- The full literal statement of `Erdos1105.erdos_1105.parts.ii` is equivalent to
the finite base window `2 * ℓ + 2 ≤ n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2` for even paths
`P_{2ℓ+2}` with `ℓ ≥ 3` (`k ≥ 8` even). All odd paths `k ≥ 5`, `P_6` (`k = 6`),
all lower bounds, and all even hosts above the window are discharged unconditionally. -/
theorem erdos_1105_parts_ii_iff_even_windows_ge_three :
    (∀ (k n : ℕ), 5 ≤ k → k ≤ n →
      let ℓ := (k - 1) / 2
      let ε := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)) ↔
    (∀ ℓ : ℕ, 3 ≤ ℓ → ∀ n : ℕ,
      2 * ℓ + 2 ≤ n → n ≤ 2 * ℓ + 2 + (ℓ - 1) / 2 →
      antiRamseyNum (pathGraph (2 * ℓ + 2)) n ≤
        max ((2 * ℓ).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + 2)) := by
  rw [ErdosProblems.LiteralPathEqualityFiniteWindows1105.original_path_equality_iff_finite_windows]
  constructor
  · intro h ℓ hℓ n hn hwin
    exact h.2 ℓ (by omega) n hn hwin
  · intro heven3
    refine ⟨?_, ?_⟩
    · intro ℓ hℓ n hn _hwin
      have hodd : Odd (2 * ℓ + 1) := ⟨ℓ, by omega⟩
      have heq := erdos_1105_odd_paths_exact (2 * ℓ + 1) n (by omega) hodd hn
      have hquot : (2 * ℓ + 1 - 1) / 2 = ℓ := by omega
      have hsub : 2 * ℓ + 1 - 2 = 2 * ℓ - 1 := by omega
      dsimp only at heq
      rw [hquot, hsub, ite_eq_left hodd] at heq
      exact le_of_eq heq
    · intro ℓ hℓ n hn hwin
      have hcases : ℓ = 2 ∨ 3 ≤ ℓ := by omega
      rcases hcases with rfl | hℓ3
      · have hn6 : n = 6 := by omega
        subst n
        have heq := ErdosProblems.PathSixOriginalAllHostExact1105.antiRamseyNum_path_six_eq 6 (by decide)
        change antiRamseyNum (pathGraph 6) 6 ≤
          max ((4 : ℕ).choose 2 + 1) ((1 : ℕ).choose 2 + 1 * (6 - 2 + 1) + 2)
        have hmax : max ((4 : ℕ).choose 2 + 1) ((1 : ℕ).choose 2 + 1 * (6 - 2 + 1) + 2) = 7 := by decide
        rw [heq, hmax]
      · exact heven3 ℓ hℓ3 n hn hwin

end ErdosProblems.PathUpperReduction.Erdos1105UniversalPathReduction
