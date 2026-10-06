module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic

@[expose] public section

/-! Exact parity arithmetic for Yuan's second path lower construction. -/

namespace ErdosProblems.PathSetLower

/-- Size of the distinguished set in the second path lower coloring. -/
def fixedSetSize (k : ℕ) : ℕ := (k - 1) / 2 - 1

/-- Number of fresh colors on edges outside the distinguished set. -/
def outsidePaletteSize (k : ℕ) : ℕ := if Odd k then 1 else 2

theorem outsidePaletteSize_pos (k : ℕ) : 0 < outsidePaletteSize k := by
  by_cases ho : Odd k <;> simp [outsidePaletteSize, ho]

theorem outsidePaletteSize_le_two (k : ℕ) : outsidePaletteSize k ≤ 2 := by
  by_cases ho : Odd k <;> simp [outsidePaletteSize, ho]

/-- The path has more outside-only edges than fresh outside colors. -/
theorem fixedSetSize_gap (k : ℕ) (hk : 5 ≤ k) :
    2 * fixedSetSize k + outsidePaletteSize k < k - 1 := by
  by_cases ho : Odd k
  · simp only [outsidePaletteSize, ite_eq_left ho, fixedSetSize]
    obtain ⟨u, hu⟩ := ho
    omega
  · obtain ⟨u, hu⟩ := Nat.not_odd_iff_even.mp ho
    simp only [outsidePaletteSize, ite_eq_right ho, fixedSetSize]
    omega

/-- There are at least three host vertices away from the distinguished set. -/
theorem fixedSetSize_three_outside {k n : ℕ} (hk : 5 ≤ k) (hkn : k ≤ n) :
    fixedSetSize k + 3 ≤ n := by
  have ht : 1 ≤ fixedSetSize k := by
    simp only [fixedSetSize]
    omega
  have hε : 1 ≤ outsidePaletteSize k := outsidePaletteSize_pos k
  have hgap := fixedSetSize_gap k hk
  omega

end ErdosProblems.PathSetLower
