module

public import CycleFullBlockRealLower
public import CycleConditionalUpper
public import TriangleAsymptotic
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section

/-!
Combines the ordered-block lower bound (`CycleFullBlockRealLower`) with the
weak-block upper induction (`CycleConditionalUpper`) and the exact triangle
asymptotic (`TriangleAsymptotic`) to derive the `=O[atTop] 1` cycle formula.
-/

namespace ErdosProblems.AntiRamseyConditionalAsymptotic

open SimpleGraph Asymptotics Filter
open ErdosProblems.AntiRamseyCycleCounted
open ErdosProblems.AntiRamseyConditionalCycleUpper
open ErdosProblems.AntiRamseyTriangle

/-- For any fixed `k ≥ 4` satisfying `HighNewWeakStructure k`, the full-block
lower bound and linear upper bound yield the `=O[atTop] 1` error term. -/
theorem cycle_asymptotic_of_highNewWeakStructure (k : ℕ)
    (hk : 4 ≤ k) (hstructure : HighNewWeakStructure k) :
    ((fun n : ℕ => (antiRamseyNum (cycleGraph k) n : ℝ) -
      ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) := by
  let α : ℝ := ((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)
  have hkreal : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - 1 := by linarith
  have hα : 0 ≤ α := by
    dsimp [α]
    exact add_nonneg (div_nonneg (by linarith) (by norm_num))
      (le_of_lt (one_div_pos.mpr hden))
  let c : ℝ := α * ((k - 1 : ℕ) : ℝ) + 1
  have hc : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg (mul_nonneg hα (Nat.cast_nonneg _)) (by norm_num)
  refine IsBigO.of_bound c ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  have hlow :
      α * (n : ℝ) - α * ((k - 1 : ℕ) : ℝ) - 1 ≤
        (antiRamseyNum (cycleGraph k) n : ℝ) := by
    simpa only [α] using cycle_fullBlock_real_lower k n (by omega : 3 ≤ k) hn
  have hhigh :
      (antiRamseyNum (cycleGraph k) n : ℝ) ≤ α * (n : ℝ) - 1 := by
    simpa only [α, cycleSlope] using
      antiRamseyNum_le_cycle_linear k n hk (by omega : k - 1 ≤ n) hstructure
  have hleft :
      -c ≤ (antiRamseyNum (cycleGraph k) n : ℝ) - α * (n : ℝ) := by
    dsimp [c]
    linarith
  have hright :
      (antiRamseyNum (cycleGraph k) n : ℝ) - α * (n : ℝ) ≤ c := by
    dsimp [c]
    linarith
  have habs := abs_le.mpr ⟨hleft, hright⟩
  simpa only [Real.norm_eq_abs, norm_one, mul_one, α] using habs

/-- Combines the `k = 3` triangle asymptotic with `cycle_asymptotic_of_highNewWeakStructure`
for all `k ≥ 4`. -/
theorem cycle_asymptotic_all_of_highNewWeakStructure
    (hstructure : ∀ k : ℕ, 4 ≤ k → HighNewWeakStructure k) :
    ∀ k, 3 ≤ k →
      ((fun n : ℕ => (antiRamseyNum (cycleGraph k) n : ℝ) -
        ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
        =O[atTop] (fun _ => (1 : ℝ))) := by
  intro k hk
  by_cases h3 : k = 3
  · subst k
    exact triangle_asymptotic_formalConjectures
  · exact cycle_asymptotic_of_highNewWeakStructure k (by omega)
      (hstructure k (by omega))

end ErdosProblems.AntiRamseyConditionalAsymptotic
