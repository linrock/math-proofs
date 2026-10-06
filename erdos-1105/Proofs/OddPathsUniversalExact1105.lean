module

public import PathFiveExact
public import PathSevenOriginalAllHostExact1105
public import OddUniversalUpper1105
public import PathMaxLower
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Unconditional exact anti-Ramsey formula for all odd paths `P_k` (`k ≥ 5`, `Odd k`)
and all complete hosts `K_n` (`n ≥ k`), matching the literal right-hand side of
Formal Conjectures `Erdos1105.erdos_1105.parts.ii`.
-/

namespace ErdosProblems.PathUpperReduction.OddPathsUniversalExact1105

open SimpleGraph

/-- For every odd `k ≥ 9` and `n ≥ k`, the anti-Ramsey number `AR(n, P_k)` equals
the literal Formal Conjectures formula. -/
theorem antiRamseyNum_odd_path_ge_nine_eq_formula (k n : ℕ)
    (hk : 9 ≤ k) (hodd : Odd k) (hkn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n =
      max ((k - 2).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  dsimp only
  have hupper :=
    OddUniversalUpper1105.antiRamseyNum_odd_path_le_formula k n hk hodd hkn
  have hupper' :
      antiRamseyNum (pathGraph k) n ≤
        max ((k - 2).choose 2 + 1)
          (((k - 1) / 2 - 1).choose 2 +
            ((k - 1) / 2 - 1) * (n - (k - 1) / 2 + 1) +
              (if Odd k then 1 else 2)) := by
    simpa only [ite_eq_left hodd] using hupper
  have hlower :=
    ErdosProblems.PathSetLower.pathMaxLower k n (by omega) hkn
  exact Nat.le_antisymm hupper' hlower

/-- Unconditional exact formula of Erdős #1105 part (ii) for every odd path order
`k ≥ 5` and every complete host size `n ≥ k`. -/
theorem erdos_1105_odd_paths_exact (k n : ℕ)
    (hk : 5 ≤ k) (hodd : Odd k) (hkn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n =
      max ((k - 2).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  have hmod : k % 2 = 1 := Nat.odd_iff.mp hodd
  have hcases : k = 5 ∨ k = 7 ∨ 9 ≤ k := by omega
  rcases hcases with rfl | rfl | hk9
  · exact ErdosProblems.AntiRamseyPathFiveExact.path_five_formal_slice n hkn
  · exact ErdosProblems.PathSevenOriginalAllHostExact1105.path_seven_formal_conjectures_slice n hkn
  · exact antiRamseyNum_odd_path_ge_nine_eq_formula k n hk9 hodd hkn

end ErdosProblems.PathUpperReduction.OddPathsUniversalExact1105
