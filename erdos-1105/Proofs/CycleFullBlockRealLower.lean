module

public import CycleFullBlockNumerical

@[expose] public section

/-! Real-valued linear lower bound for `antiRamseyNum (cycleGraph k) n` derived
from the consecutive `(k - 1)`-clique block construction. -/

namespace ErdosProblems.AntiRamseyCycleCounted

open SimpleGraph
open ErdosProblems.AntiRamseyCycle
open ErdosProblems.AntiRamseyCycleBlockCount

/-- For every `n ≥ k ≥ 3`, the anti-Ramsey cycle number is at least its linear
coefficient `((k - 2) / 2 + 1 / (k - 1)) * n` minus the fixed remainder offset
`((k - 2) / 2 + 1 / (k - 1)) * (k - 1) + 1`. -/
theorem cycle_fullBlock_real_lower (k n : ℕ)
    (hk : 3 ≤ k) (hn : k ≤ n) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≥
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) *
          ((k - 1 : ℕ) : ℝ) - 1 := by
  let m : ℕ := k - 1
  let q : ℕ := n / m
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmpos : 0 < m := by omega
  have hmle : m ≤ n := by dsimp [m]; omega
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.div_pos hmle hmpos
  have hqone : 1 ≤ q := hq
  have hformula :
      q * m.choose 2 + (q - 1) =
        q * (m.choose 2 + 1) - 1 := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hnat : q * m.choose 2 + (q - 1) ≤
      antiRamseyNum (cycleGraph k) n := by
    rw [hformula]
    simpa only [m, q] using cycle_fullBlock_antiRamseyNum_lower
      k n hk hn
  have hqcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hqone]
    norm_num
  have hnatreal :
      ((q * m.choose 2 + (q - 1) : ℕ) : ℝ) ≤
        (antiRamseyNum (cycleGraph k) n : ℝ) := by
    exact_mod_cast hnat
  have hreal :
      (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 ≤
        (antiRamseyNum (cycleGraph k) n : ℝ) := by
    calc
      (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 =
          ((q * m.choose 2 + (q - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_mul, hqcast]
        ring
      _ ≤ (antiRamseyNum (cycleGraph k) n : ℝ) := hnatreal
  have hcoeff :
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) =
        (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) := by
    exact cycle_coefficient_eq_block_coefficient k hk
  have harith := full_blocks_real_lower m n hm hmle
  calc
    (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) *
          ((k - 1 : ℕ) : ℝ) - 1 =
      (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (n : ℝ) -
        (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (m : ℝ) - 1 := by
      rw [hcoeff]
    _ ≤ (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 := by
      simpa only [m, q] using harith
    _ ≤ (antiRamseyNum (cycleGraph k) n : ℝ) := hreal

end ErdosProblems.AntiRamseyCycleCounted
