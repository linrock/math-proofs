module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.Init
public import Mathlib.Algebra.Group.Int.Even
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Lifted integer matrix parity

candidate for the translation part of Choi Claim 3. It makes no graph, finite cyclic lift, palette, or degree assertion. The codomain is arbitrary; no equality decision procedure on colors is used.
-/

namespace ErdosProblems.AntiRamseyIntegerMatrixParity

variable {C : Type*}

/-- A translation along a diagonal collapses its entries to the second-coordinate zero. -/
theorem diagonal_normal_form
    (M : ℤ → ℤ → C)
    (hminus : ∀ i j, M i j = M (i + 1) (j - 1))
    (i j : ℤ) :
    M i j = M (i + j) 0 := by
  have hg : Function.Periodic (fun x : ℤ => M (i + j - x) x) 1 := by
    intro x
    change M (i + j - (x + 1)) (x + 1) = M (i + j - x) x
    calc
      M (i + j - (x + 1)) (x + 1) =
          M (i + j - (x + 1) + 1) (x + 1 - 1) :=
        hminus (i + j - (x + 1)) (x + 1)
      _ = M (i + j - x) x := by
        congr 1 <;> omega
  have h := hg.int_mul_eq j
  change M (i + j - j * 1) (j * 1) = M (i + j - 0) 0 at h
  calc
    M i j = M (i + j - j * 1) (j * 1) := by
      congr 1 <;> omega
    _ = M (i + j - 0) 0 := h
    _ = M (i + j) 0 := by
      (congr 1; omega)

/-- Composing the two supplied unit translations yields period two in the first coordinate. -/
theorem first_coordinate_period_two
    (M : ℤ → ℤ → C)
    (hminus : ∀ i j, M i j = M (i + 1) (j - 1))
    (hplus : ∀ i j, M i j = M (i + 1) (j + 1)) :
    Function.Periodic (fun i : ℤ => M i 0) 2 := by
  intro i
  change M (i + 2) 0 = M i 0
  calc
    M (i + 2) 0 = M (i + 1 + 1) (0 - 1 + 1) := by
      (congr 1; omega)
    _ = M (i + 1) (0 - 1) := (hplus (i + 1) (0 - 1)).symm
    _ = M i 0 := (hminus i 0).symm

/-- The two unit diagonal translations determine each entry by the parity of the coordinate sum. -/
theorem parity_normal_form
    (M : ℤ → ℤ → C)
    (hminus : ∀ i j, M i j = M (i + 1) (j - 1))
    (hplus : ∀ i j, M i j = M (i + 1) (j + 1))
    (i j : ℤ) :
    M i j = M ((i + j) % 2) 0 := by
  have htwo := first_coordinate_period_two M hminus hplus
  have hrem : i + j - ((i + j) / 2) * 2 = (i + j) % 2 := by
    rw [Int.emod_def, mul_comm 2 ((i + j) / 2)]
  calc
    M i j = M (i + j) 0 := diagonal_normal_form M hminus i j
    _ = M (i + j - ((i + j) / 2) * 2) 0 :=
      (htwo.sub_int_mul_eq (x := i + j) ((i + j) / 2)).symm
    _ = M ((i + j) % 2) 0 := congrArg (fun x : ℤ => M x 0) hrem

/-- Any additional translation with odd coordinate sum makes the matrix constant. -/
theorem constant_of_odd_translation
    (M : ℤ → ℤ → C)
    (hminus : ∀ i j, M i j = M (i + 1) (j - 1))
    (hplus : ∀ i j, M i j = M (i + 1) (j + 1))
    (d e : ℤ)
    (hshift : ∀ i j, M i j = M (i + d) (j + e))
    (hodd : (d + e) % 2 = 1) :
    ∀ i j, M i j = M 0 0 := by
  have hzero_one : M 0 0 = M 1 0 := by
    calc
      M 0 0 = M d e := by
        simpa only [zero_add] using hshift 0 0
      _ = M 1 0 := by
        simpa only [hodd] using parity_normal_form M hminus hplus d e
  intro i j
  have hform := parity_normal_form M hminus hplus i j
  rcases Int.emod_two_eq_zero_or_one (i + j) with hzero | hone
  · simpa only [hzero] using hform
  · have hone_form : M i j = M 1 0 := by
      simpa only [hone] using hform
    exact hone_form.trans hzero_one.symm

/--
Natural coordinate periods and a translation of sum `k - 2` force constancy
whenever at least one of `a`, `b`, `k` is not even.

This stronger statement permits zero natural periods: in the intended positive-period
application, restrict `a,b` to positive naturals. No graph assertion follows from it.
-/
theorem constant_of_not_all_even
    (M : ℤ → ℤ → C)
    (hminus : ∀ i j, M i j = M (i + 1) (j - 1))
    (hplus : ∀ i j, M i j = M (i + 1) (j + 1))
    (a b k : ℕ) (d e : ℤ)
    (ha_period : ∀ i j, M i j = M (i + (a : ℤ)) j)
    (hb_period : ∀ i j, M i j = M i (j + (b : ℤ)))
    (hshift : ∀ i j, M i j = M (i + d) (j + e))
    (hsum : d + e = (k : ℤ) - 2)
    (hodd : ¬Even a ∨ ¬Even b ∨ ¬Even k) :
    ∀ i j, M i j = M 0 0 := by
  rcases hodd with ha | hb | hk
  · have ha_int : ¬Even (a : ℤ) :=
      fun h => ha ((Int.even_coe_nat a).mp h)
    apply constant_of_odd_translation M hminus hplus (a : ℤ) 0
    · intro i j
      simpa only [add_zero] using ha_period i j
    · simpa only [add_zero] using Int.not_even_iff.mp ha_int
  · have hb_int : ¬Even (b : ℤ) :=
      fun h => hb ((Int.even_coe_nat b).mp h)
    apply constant_of_odd_translation M hminus hplus 0 (b : ℤ)
    · intro i j
      simpa only [add_zero] using hb_period i j
    · simpa only [zero_add] using Int.not_even_iff.mp hb_int
  · have hk_int : ¬Even (k : ℤ) :=
      fun h => hk ((Int.even_coe_nat k).mp h)
    have hsum_not_even : ¬Even (d + e) := by
      intro heven
      rw [hsum] at heven
      have hk_iff_two := Int.even_sub.mp heven
      exact hk_int (hk_iff_two.mpr (Int.even_iff.mpr (by rfl)))
    exact constant_of_odd_translation M hminus hplus d e hshift
      (Int.not_even_iff.mp hsum_not_even)

end ErdosProblems.AntiRamseyIntegerMatrixParity
