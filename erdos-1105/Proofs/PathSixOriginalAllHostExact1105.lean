module

public import PathSixOriginalAllHostUpper1105
public import PathMaxLower
public import Mathlib.Tactic

@[expose] public section

/-!
Exact anti-Ramsey number `antiRamseyNum (pathGraph 6) n = n + 1` (and the
matching `max` formula of Part (ii)) for all host orders `n ≥ 6`, combining
`PathSixOriginalAllHostUpper1105` with `PathMaxLower`.
-/

namespace ErdosProblems.PathSixOriginalAllHostExact1105

open SimpleGraph

/-- The exact original-host anti-Ramsey P6 value for every n>=6. -/
theorem antiRamseyNum_path_six_eq (n : ℕ) (hn : 6 ≤ n) :
    antiRamseyNum (pathGraph 6) n = n + 1 := by
  have hupper :=
    ErdosProblems.PathSixOriginalAllHostUpper1105.antiRamseyNum_path_six_le n hn
  have hlower := ErdosProblems.PathSetLower.pathMaxLower 6 n (by decide) hn
  norm_num at hlower
  exact Nat.le_antisymm hupper (by omega)

/-- The literal FC1105(ii) maximum on its full original fixed-k=6 domain. -/
theorem path_six_formal_conjectures_slice (n : ℕ) (hn : 6 ≤ n) :
    let ℓ := (6 - 1 : ℕ) / 2
    let ε := if Odd (6 : ℕ) then 1 else 2
    antiRamseyNum (pathGraph 6) n =
      max ((6 - 2 : ℕ).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) := by
  simp only [show ¬ Odd (6 : ℕ) by decide, ite_false]
  change antiRamseyNum (pathGraph 6) n =
    max ((4 : ℕ).choose 2 + 1)
      ((1 : ℕ).choose 2 + 1 * (n - 2 + 1) + 2)
  have hA : ((4 : ℕ).choose 2 + 1) = 7 := by decide
  have hB : ((1 : ℕ).choose 2 + 1 * (n - 2 + 1) + 2) = n + 1 := by
    simp only [show (1 : ℕ).choose 2 = 0 by decide, zero_add, one_mul]
    omega
  rw [hA, hB, max_eq_right (show (7 : ℕ) ≤ n + 1 by omega)]
  exact antiRamseyNum_path_six_eq n hn

end ErdosProblems.PathSixOriginalAllHostExact1105
