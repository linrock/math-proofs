module

public import CycleFourTrianglePartition
public import CycleFourTriangleQuotient
public import CycleConditionalAsymptotic
public import Mathlib.Tactic

@[expose] public section

namespace ErdosProblems.AntiRamseyCycleFourHighNewStructure

open SimpleGraph Asymptotics Filter
open ErdosProblems.AntiRamseyWeakCount
open ErdosProblems.AntiRamseyConditionalCycleUpper
open ErdosProblems.AntiRamseyConditionalAsymptotic
open ErdosProblems.AntiRamseyCycleFourTrianglePartition
open ErdosProblems.AntiRamseyCycleFourTriangleQuotient

/-- Weak-block decomposition theorem `HighNewWeakStructure 4` for `C_4`-free
host colorings in which every vertex has at least two private colors. -/
theorem highNewWeakStructure_four : HighNewWeakStructure 4 := by
  intro n q hn χ hno hnew _hpair
  obtain ⟨t, b, ht, hsize, _, hown, hsum⟩ :=
    selected_triangle_component_partition χ hn hno hnew
  obtain ⟨ψ, hcross, htriangle⟩ :=
    triangle_block_quotient χ hno b ht hsize hown
  refine ⟨t, b, ψ, ht, hcross, htriangle, ?_, ?_, hsum⟩
  · intro i
    rw [hsize i]
    omega
  · intro i
    rw [hsize i]

/-- The `k = 4` specialization of the cycle asymptotic formula. -/
theorem cycle_four_asymptotic_formalConjectures :
    ((fun n : ℕ => (antiRamseyNum (cycleGraph 4) n : ℝ) -
      ((4 - 2 : ℝ) / 2 + 1 / (4 - 1)) * n)
      =O[Filter.atTop] (fun _ => (1 : ℝ))) := by
  exact cycle_asymptotic_of_highNewWeakStructure 4 (by omega)
    highNewWeakStructure_four

end ErdosProblems.AntiRamseyCycleFourHighNewStructure
