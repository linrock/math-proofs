module

public import Mathlib

@[expose] public section

/-!
The real arithmetic behind the conventional `(k - 1)`-vertex block
construction for the cycle anti-Ramsey lower bound. The palette-counting
argument is separate: this file does not assert that any coloring realizes
the numerical expression below.
-/

namespace ErdosProblems.AntiRamseyCycleBlockCount

/-- A complete block of `m` vertices contributes `m.choose 2 + 1` colors
per `m` vertices at the cycle coefficient. -/
theorem full_block_coefficient (m : ℕ) (hm : 2 ≤ m) :
    (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (m : ℝ) =
      (((m.choose 2 : ℕ) : ℝ) + 1) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  rw [Nat.cast_choose_two ℝ m]
  field_simp [ne_of_gt hmpos]

/-- The full blocks alone have the required cycle slope with a uniform
constant error for fixed `m`; any partial-block colors can only improve this
lower estimate. -/
theorem full_blocks_real_lower (m n : ℕ) (hm : 2 ≤ m) (_hn : m ≤ n) :
    (((n / m : ℕ) : ℝ) * ((m.choose 2 : ℕ) : ℝ) + ((n / m : ℕ) : ℝ) - 1) ≥
      (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (n : ℝ) -
        (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (m : ℝ) - 1 := by
  let q : ℕ := n / m
  let A : ℝ := ((m : ℝ) - 1) / 2 + 1 / (m : ℝ)
  have hmpos : 0 < m := by omega
  have hA : 0 ≤ A := by
    dsimp [A]
    apply add_nonneg
    · apply div_nonneg
      · have hmreal : (1 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (by omega : 1 ≤ m)
        linarith
      · norm_num
    · exact le_of_lt (one_div_pos.mpr (by exact_mod_cast hmpos))
  have hqbound : n ≤ m * q + m := by
    have hmod := Nat.mod_lt n hmpos
    have hdecomp := Nat.mod_add_div n m
    dsimp [q]
    omega
  have hreal : (n : ℝ) ≤ (m : ℝ) * (q : ℝ) + (m : ℝ) := by
    exact_mod_cast hqbound
  have hprod := mul_le_mul_of_nonneg_left hreal hA
  have hcoeff : A * (m : ℝ) = (((m.choose 2 : ℕ) : ℝ) + 1) := by
    dsimp [A]
    exact full_block_coefficient m hm
  have hformula :
      (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 =
        A * (m : ℝ) * (q : ℝ) - 1 := by
    rw [hcoeff]
    ring
  change (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 ≥
    A * (n : ℝ) - A * (m : ℝ) - 1
  rw [hformula]
  nlinarith [hprod]

/-- Substitute `m = k - 1` into the literal real coefficient of
`erdos_1105.parts.i`. -/
theorem cycle_coefficient_eq_block_coefficient (k : ℕ) (hk : 3 ≤ k) :
    (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) =
      ((((k - 1 : ℕ) : ℝ) - 1) / 2 + 1 / ((k - 1 : ℕ) : ℝ)) := by
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [hcast]
  ring

end ErdosProblems.AntiRamseyCycleBlockCount
