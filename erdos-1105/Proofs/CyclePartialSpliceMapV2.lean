module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic

@[expose] public section

/-! the exact graph-only partial-reversal map for Claim2. No splice selection, coloring, cycle Copy or universal bound is asserted. -/

namespace ErdosProblems.AntiRamseyCyclePartialSpliceMap

open SimpleGraph

/-- Fix0 and the exterior; reverse the interval1..a. -/
def partialReverse {m : ℕ} (a i : Fin (m + 3)) : Fin (m + 3) :=
  if h : 1 ≤ i.val ∧ i.val ≤ a.val then
    ⟨a.val + 1 - i.val, by have ha := a.isLt; omega⟩
  else i

theorem partialReverse_val_inside {m : ℕ} (a i : Fin (m + 3))
    (h : 1 ≤ i.val ∧ i.val ≤ a.val) :
    (partialReverse a i).val = a.val + 1 - i.val := by
  unfold partialReverse
  rw [dite_eq_left h]

theorem partialReverse_outside {m : ℕ} (a i : Fin (m + 3))
    (h : ¬ (1 ≤ i.val ∧ i.val ≤ a.val)) : partialReverse a i = i := by
  unfold partialReverse
  exact dite_eq_right h

theorem partialReverse_involutive {m : ℕ} (a : Fin (m + 3)) :
    Function.Involutive (partialReverse a) := by
  intro i
  by_cases h : 1 ≤ i.val ∧ i.val ≤ a.val
  · have hv := partialReverse_val_inside a i h
    have hi : 1 ≤ (partialReverse a i).val ∧
        (partialReverse a i).val ≤ a.val := by omega
    have hh := partialReverse_val_inside a (partialReverse a i) hi
    apply Fin.ext
    rw [hh, hv]
    omega
  · have hi := partialReverse_outside a i h
    rw [hi, hi]

theorem partialReverse_injective {m : ℕ} (a : Fin (m + 3)) :
    Function.Injective (partialReverse a) :=
  (partialReverse_involutive a).injective

theorem partialReverse_zero {m : ℕ} (a : Fin (m + 3)) :
    partialReverse a 0 = 0 := by
  apply partialReverse_outside
  change ¬ (1 ≤ 0 ∧ 0 ≤ a.val)
  omega

theorem partialReverse_one {m : ℕ} (a : Fin (m + 3)) (ha : 2 ≤ a.val) :
    partialReverse a ⟨1, by omega⟩ = a := by
  have h : 1 ≤ (⟨1, by omega⟩ : Fin (m + 3)).val ∧
      (⟨1, by omega⟩ : Fin (m + 3)).val ≤ a.val := by
    change 1 ≤ 1 ∧ 1 ≤ a.val
    omega
  apply Fin.ext
  rw [partialReverse_val_inside a _ h]
  change a.val + 1 - 1 = a.val
  omega

theorem partialReverse_last {m : ℕ} (a : Fin (m + 3)) (ha : a.val ≤ m) :
    partialReverse a (Fin.last (m + 2)) = Fin.last (m + 2) := by
  apply partialReverse_outside
  change ¬ (1 ≤ m + 2 ∧ m + 2 ≤ a.val)
  omega

/-- The two supplied skips are precisely the two new consecutive pairs. -/
theorem partial_splice_ordered_path {V : Type*} {m : ℕ}
    (H : SimpleGraph V) (R : Fin (m + 3) → V)
    (hpath : ∀ x y : Fin (m + 3), x.val + 1 = y.val → H.Adj (R x) (R y))
    (a : Fin (m + 3)) (ha2 : 2 ≤ a.val) (ham : a.val ≤ m)
    (hleft : H.Adj (R 0) (R a))
    (hright : H.Adj (R ⟨1, by omega⟩) (R ⟨a.val + 1, by omega⟩)) :
    ∀ i : Fin (m + 2),
      H.Adj (R (partialReverse a (Fin.castSucc i)))
        (R (partialReverse a (Fin.succ i))) := by
  intro i
  by_cases hzero : i.val = 0
  · have hl : Fin.castSucc i = (0 : Fin (m + 3)) := Fin.ext hzero
    have hr : Fin.succ i = (⟨1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      change i.val + 1 = 1
      omega
    rw [hl, hr, partialReverse_zero, partialReverse_one a ha2]
    exact hleft
  · by_cases hlt : i.val < a.val
    · have hl : 1 ≤ (Fin.castSucc i).val ∧ (Fin.castSucc i).val ≤ a.val := by
        change 1 ≤ i.val ∧ i.val ≤ a.val
        omega
      have hr : 1 ≤ (Fin.succ i).val ∧ (Fin.succ i).val ≤ a.val := by
        change 1 ≤ i.val + 1 ∧ i.val + 1 ≤ a.val
        omega
      apply (hpath _ _ ?_).symm
      rw [partialReverse_val_inside a _ hr, partialReverse_val_inside a _ hl]
      change (a.val + 1 - (i.val + 1)) + 1 = a.val + 1 - i.val
      omega
    · by_cases heq : i.val = a.val
      · have hy : 1 ≤ (Fin.castSucc i).val ∧ (Fin.castSucc i).val ≤ a.val := by
          change 1 ≤ i.val ∧ i.val ≤ a.val
          omega
        have hl : partialReverse a (Fin.castSucc i) = ⟨1, by omega⟩ := by
          apply Fin.ext
          rw [partialReverse_val_inside a _ hy]
          change a.val + 1 - i.val = 1
          omega
        have hn : ¬ (1 ≤ (Fin.succ i).val ∧ (Fin.succ i).val ≤ a.val) := by
          change ¬ (1 ≤ i.val + 1 ∧ i.val + 1 ≤ a.val)
          omega
        have hr : partialReverse a (Fin.succ i) = ⟨a.val + 1, by omega⟩ := by
          rw [partialReverse_outside a _ hn]
          apply Fin.ext
          change i.val + 1 = a.val + 1
          omega
        rw [hl, hr]
        exact hright
      · have hl : ¬ (1 ≤ (Fin.castSucc i).val ∧ (Fin.castSucc i).val ≤ a.val) := by
          change ¬ (1 ≤ i.val ∧ i.val ≤ a.val)
          omega
        have hr : ¬ (1 ≤ (Fin.succ i).val ∧ (Fin.succ i).val ≤ a.val) := by
          change ¬ (1 ≤ i.val + 1 ∧ i.val + 1 ≤ a.val)
          omega
        rw [partialReverse_outside a _ hl, partialReverse_outside a _ hr]
        exact hpath (Fin.castSucc i) (Fin.succ i) rfl

/-- Neither orientation of the omitted first pair occurs in the splice. -/
theorem partial_splice_omits_first_edge {V : Type*} {m : ℕ}
    (R : Fin (m + 3) → V) (hR : Function.Injective R)
    (a : Fin (m + 3)) (ha2 : 2 ≤ a.val) :
    ∀ i : Fin (m + 2),
      s(R (partialReverse a (Fin.castSucc i)), R (partialReverse a (Fin.succ i))) ≠
        s(R 0, R ⟨1, by omega⟩) := by
  intro i heq
  rcases Sym2.eq_iff.mp heq with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · have hc : Fin.castSucc i = 0 :=
      partialReverse_injective a ((hR hl).trans (partialReverse_zero a).symm)
    have hi : i.val = 0 := congrArg Fin.val hc
    have hs : Fin.succ i = (⟨1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      change i.val + 1 = 1
      omega
    have ha : a = (⟨1, by omega⟩ : Fin (m + 3)) := by
      have hcolorless := hR hr
      rw [hs, partialReverse_one a ha2] at hcolorless
      exact hcolorless
    have hav : a.val = 1 := congrArg Fin.val ha
    omega
  · have hs : Fin.succ i = 0 :=
      partialReverse_injective a ((hR hr).trans (partialReverse_zero a).symm)
    have hsv : i.val + 1 = 0 := congrArg Fin.val hs
    omega

end ErdosProblems.AntiRamseyCyclePartialSpliceMap
