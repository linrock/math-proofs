module

public import CycleSelectedComponentOrderV5
public import CycleOriginalCrossComponentConstancyV7
public import CycleOriginalThreeComponentTriangleV5
public import CycleComponentQuotient
public import CycleConditionalUpper
public import CycleFourHighNewStructure
public import CycleConditionalAsymptotic
public import Mathlib.Tactic

@[expose] public section

/-!
Unconditional proof of `HighNewWeakStructure k` for all `k ≥ 4`, the explicit
linear upper bound `antiRamseyNum (cycleGraph k) n ≤ ((k - 2) / 2 + 1 / (k - 1)) * n - 1`
for all `n ≥ k ≥ 3`, and the universal cycle asymptotic `cycle_asymptotic_all`
(Part (i) of Erdős Problem 1105).
-/

namespace ErdosProblems.AntiRamseyCycleOriginalHighNewStructure

open SimpleGraph Asymptotics Filter
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleSelectedComponentOrder
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentConstancy
open ErdosProblems.AntiRamseyCycleOriginalThreeComponentTriangle
open ErdosProblems.AntiRamseyCycleComponentQuotient
open ErdosProblems.AntiRamseyConditionalCycleUpper
open ErdosProblems.AntiRamseyConditionalAsymptotic
open ErdosProblems.AntiRamseyCycleFourHighNewStructure
open ErdosProblems.AntiRamseyTriangle

/-- Unconditional proof of `HighNewWeakStructure k` for every `k ≥ 5` by
combining the selected-component order bound (` ≤ k - 1`), cross-component
monochromaticity, and 3-component rainbow-triangle exclusion. -/
theorem highNewWeakStructure_of_five_le {k : ℕ} (hk : 5 ≤ k) :
    HighNewWeakStructure k := by
  intro n q hn χ hno hnew hpair
  let r : NewChoice χ := canonicalChoice χ
  apply weak_structure_of_component_conditions (selectedGraph χ r) (by omega) χ
  · intro D
    exact selected_component_order_le_original hk χ r hnew hpair hno D
  · intro D E hDE a d ha hd had a' d' ha' hd' had'
    obtain ⟨c, hc⟩ := cross_component_colors_constant hk χ r hnew hpair hno D E hDE
    have hfirst : χ.get a d had = c := hc a d ha hd ⟨s(a, d), had⟩ rfl
    have hsecond : χ.get a' d' had' = c := hc a' d' ha' hd' ⟨s(a', d'), had'⟩ rfl
    exact hfirst.trans hsecond.symm
  · intro a d c had hdc hca hAD hDC hCA
    exact no_three_component_rainbow_triangle hk χ r hnew hpair hno
      a d c had hdc hca hAD hDC hCA

/-- Unconditional weak-block decomposition `HighNewWeakStructure k` for every `k ≥ 4`. -/
theorem highNewWeakStructure_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    HighNewWeakStructure k := by
  by_cases hfour : k = 4
  · subst k
    exact highNewWeakStructure_four
  · exact highNewWeakStructure_of_five_le (by omega)

/-- Unconditional linear upper bound for `antiRamseyNum (cycleGraph k) n` across
all cycle orders `k ≥ 3` and host orders `n ≥ k`. -/
theorem cycle_linear_upper (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≤
      ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n - 1 := by
  by_cases h3 : k = 3
  · subst k
    rw [antiRamseyNum_cycleGraph_three n hn, Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  · have hk4 : 4 ≤ k := by omega
    simpa only [cycleSlope] using
      antiRamseyNum_le_cycle_linear k n hk4 (by omega : k - 1 ≤ n)
        (highNewWeakStructure_of_four_le hk4)

/-- Complete unconditional proof of Part (i) of Erdős Problem 1105 for all `k ≥ 3`. -/
theorem cycle_asymptotic_all :
    ∀ k, 3 ≤ k →
      ((fun n : ℕ => (antiRamseyNum (cycleGraph k) n : ℝ) -
        ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
        =O[atTop] (fun _ => (1 : ℝ))) :=
  cycle_asymptotic_all_of_highNewWeakStructure (fun _ hk => highNewWeakStructure_of_four_le hk)

end ErdosProblems.AntiRamseyCycleOriginalHighNewStructure
