module

public import Mathlib

@[expose] public section

namespace ErdosProblems.AntiRamseyWeakCount

open Finset

theorem one_block_arithmetic (m s : ℕ) (hm : 2 ≤ m)
    (hs : 1 ≤ s) (hsm : s ≤ m) :
    ((s.choose 2 : ℕ) : ℝ) + 1 ≤
      (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (s : ℝ) := by
  have hmpos_nat : 0 < m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsm' : (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsm
  have htwo : (2 : ℝ) ≤ (m : ℝ) * (s : ℝ) := by
    calc
      (2 : ℝ) ≤ 2 * (s : ℝ) := by nlinarith
      _ ≤ (m : ℝ) * (s : ℝ) :=
        mul_le_mul_of_nonneg_right hm2 (by positivity)
  have hfactor_nonneg :
      0 ≤ ((m : ℝ) - (s : ℝ)) * ((m : ℝ) * (s : ℝ) - 2) :=
    mul_nonneg (sub_nonneg.mpr hsm') (sub_nonneg.mpr htwo)
  have hchoose : ((s.choose 2 : ℕ) : ℝ) =
      (s : ℝ) * ((s : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ s
  let D : ℝ :=
    (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (s : ℝ) -
      (((s.choose 2 : ℕ) : ℝ) + 1)
  have hfactor : (2 * (m : ℝ)) * D =
      ((m : ℝ) - (s : ℝ)) * ((m : ℝ) * (s : ℝ) - 2) := by
    dsimp [D]
    rw [hchoose]
    field_simp [ne_of_gt hmpos]
    ring
  have hscaled : 0 ≤ (2 * (m : ℝ)) * D := by
    rw [hfactor]
    exact hfactor_nonneg
  have hpositive : (0 : ℝ) < 2 * (m : ℝ) := by positivity
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_right hscaled hpositive
  dsimp [D] at hD
  linarith

/-- Conditional arithmetic step for Choi's weak anticyclic block count.
If `t ≥ 1` and every block size is between `1` and `k - 1`, the finite
internal-edge plus quotient-color count is at most the cycle coefficient
times the total number of vertices minus one. It does not assert that a
rainbow-cycle-free coloring has such a block partition. -/
theorem block_arithmetic_linear_bound (k t n : ℕ) (hk : 3 ≤ k) (ht : 1 ≤ t)
    (s : Fin t → ℕ) (hspos : ∀ i, 1 ≤ s i)
    (hsupper : ∀ i, s i ≤ k - 1)
    (hsum : ∑ i : Fin t, s i = n) :
    (((∑ i : Fin t, (s i).choose 2 : ℕ) : ℕ) : ℝ) + ((t - 1 : ℕ) : ℝ) ≤
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) - 1 := by
  let m : ℕ := k - 1
  let A : ℝ := ((m : ℝ) - 1) / 2 + 1 / (m : ℝ)
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hsum_blocks :
      (∑ i : Fin t, ((((s i).choose 2 : ℕ) : ℝ) + 1)) ≤
        ∑ i : Fin t, A * (s i : ℝ) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin t)))
        (f := fun i => (((s i).choose 2 : ℕ) : ℝ) + 1)
        (g := fun i => A * (s i : ℝ))
        (fun i _ => one_block_arithmetic m (s i) hm (hspos i) (hsupper i)))
  have hleft :
      (((∑ i : Fin t, (s i).choose 2 : ℕ) : ℕ) : ℝ) + (t : ℝ) =
        ∑ i : Fin t, ((((s i).choose 2 : ℕ) : ℝ) + 1) := by
    rw [Finset.sum_add_distrib]
    simp
  have hright : (∑ i : Fin t, A * (s i : ℝ)) = A * (n : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, hsum]
  have hfinite :
      (((∑ i : Fin t, (s i).choose 2 : ℕ) : ℕ) : ℝ) + (t : ℝ) ≤
        A * (n : ℝ) := by
    calc
      _ = ∑ i : Fin t, ((((s i).choose 2 : ℕ) : ℝ) + 1) := hleft
      _ ≤ ∑ i : Fin t, A * (s i : ℝ) := hsum_blocks
      _ = A * (n : ℝ) := hright
  have htcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht]
    norm_num
  have hmcast : (m : ℝ) = (k : ℝ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hcoeff : A = (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) := by
    dsimp [A]
    rw [hmcast]
    ring
  rw [htcast, ← hcoeff]
  linarith

end ErdosProblems.AntiRamseyWeakCount
