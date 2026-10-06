module

public import TriangleExact
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section

/-!
The `k = 3` instance of the cycle asymptotic predicate in Formal Conjectures
Erdős problem 1105. This is a restricted parameter result, derived from the
exact triangle anti-Ramsey number.
-/

namespace ErdosProblems.AntiRamseyTriangle

open SimpleGraph Asymptotics Filter

/-- At `k = 3`, the Formal Conjectures cycle error term is eventually exactly `-1`. -/
theorem triangle_error_eventually_eq_neg_one :
    (fun n : ℕ => (antiRamseyNum (cycleGraph 3) n : ℝ) -
      ((3 - 2 : ℝ) / 2 + 1 / (3 - 1)) * n) =ᶠ[atTop] (fun _ => (-1 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  have hvalue := antiRamseyNum_cycleGraph_three n hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ n))
  have hcoeff : ((3 - 2 : ℝ) / 2 + 1 / (3 - 1)) = 1 := by norm_num
  simp only [hvalue, hcast, hcoeff]
  ring

/-- The `k = 3` instance of the all-cycle `O(1)` claim in `erdos_1105.parts.i`. -/
theorem triangle_asymptotic_formalConjectures :
    ((fun n => (antiRamseyNum (cycleGraph 3) n : ℝ) -
      ((3 - 2 : ℝ) / 2 + 1 / (3 - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) := by
  exact triangle_error_eventually_eq_neg_one.trans_isBigO
    (isBigO_const_one ℝ (-1 : ℝ) atTop)

end ErdosProblems.AntiRamseyTriangle
