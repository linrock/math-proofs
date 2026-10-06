module

public import CycleIntegerMatrixParityV2

@[expose] public section

/-!
# Adjacent path-length matrix translations

extraction of the two unit translations from the four translations
supplied by adjacent path lengths and the two directed orientations. No graph, cyclic lift, palette, degree, or unconditional constancy is asserted.
-/

namespace ErdosProblems.AntiRamseyAdjacentMatrixTranslations

variable {C : Type*}

/-- Reverse the first translation, then apply the adjacent forward translation. -/
theorem unit_minus_of_adjacent_translations
    (M : ℤ → ℤ → C) (d e : ℤ)
    (hde : ∀ i j, M i j = M (i + d) (j + e))
    (hnext : ∀ i j, M i j = M (i + (d + 1)) (j + (e - 1))) :
    ∀ i j, M i j = M (i + 1) (j - 1) := by
  intro i j
  calc
    M i j = M (i - d + d) (j - e + e) := by
      congr 1 <;> omega
    _ = M (i - d) (j - e) := (hde (i - d) (j - e)).symm
    _ = M (i - d + (d + 1)) (j - e + (e - 1)) :=
      hnext (i - d) (j - e)
    _ = M (i + 1) (j - 1) := by
      congr 1 <;> omega

/-- Reverse the first reversed-orientation translation, then apply its adjacent one. -/
theorem unit_plus_of_adjacent_reverse_translations
    (M : ℤ → ℤ → C) (d e : ℤ)
    (hde : ∀ i j, M i j = M (i + d) (j + (-e)))
    (hnext : ∀ i j, M i j = M (i + (d + 1)) (j + (-e + 1))) :
    ∀ i j, M i j = M (i + 1) (j + 1) := by
  intro i j
  calc
    M i j = M (i - d + d) (j + e + (-e)) := by
      congr 1 <;> omega
    _ = M (i - d) (j + e) := (hde (i - d) (j + e)).symm
    _ = M (i - d + (d + 1)) (j + e + (-e + 1)) :=
      hnext (i - d) (j + e)
    _ = M (i + 1) (j + 1) := by
      congr 1 <;> omega

/-- Apply the parity normal form to the extracted unit translations. -/
theorem parity_normal_form_of_adjacent_translations
    (M : ℤ → ℤ → C) (d e : ℤ)
    (hde : ∀ i j, M i j = M (i + d) (j + e))
    (hnext : ∀ i j, M i j = M (i + (d + 1)) (j + (e - 1)))
    (hreverse : ∀ i j, M i j = M (i + d) (j + (-e)))
    (hreverse_next : ∀ i j, M i j = M (i + (d + 1)) (j + (-e + 1)))
    (i j : ℤ) :
    M i j = M ((i + j) % 2) 0 := by
  exact ErdosProblems.AntiRamseyIntegerMatrixParity.parity_normal_form M
    (unit_minus_of_adjacent_translations M d e hde hnext)
    (unit_plus_of_adjacent_reverse_translations M d e hreverse hreverse_next)
    i j

/--
Apply the odd-parameter theorem, retaining the first supplied
translation as the additional translation of coordinate sum `k - 2`.
-/
theorem constant_of_not_all_even_of_adjacent_translations
    (M : ℤ → ℤ → C) (d e : ℤ)
    (hde : ∀ i j, M i j = M (i + d) (j + e))
    (hnext : ∀ i j, M i j = M (i + (d + 1)) (j + (e - 1)))
    (hreverse : ∀ i j, M i j = M (i + d) (j + (-e)))
    (hreverse_next : ∀ i j, M i j = M (i + (d + 1)) (j + (-e + 1)))
    (a b k : ℕ)
    (ha_period : ∀ i j, M i j = M (i + (a : ℤ)) j)
    (hb_period : ∀ i j, M i j = M i (j + (b : ℤ)))
    (hsum : d + e = (k : ℤ) - 2)
    (hodd : ¬Even a ∨ ¬Even b ∨ ¬Even k) :
    ∀ i j, M i j = M 0 0 := by
  exact ErdosProblems.AntiRamseyIntegerMatrixParity.constant_of_not_all_even M
    (unit_minus_of_adjacent_translations M d e hde hnext)
    (unit_plus_of_adjacent_reverse_translations M d e hreverse hreverse_next)
    a b k d e ha_period hb_period hde hsum hodd

end ErdosProblems.AntiRamseyAdjacentMatrixTranslations
