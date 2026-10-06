module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Int.Init
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# A same-parity chord path and its literal windows

candidate for the chord/window leg of conditional Choi Claim 3. No palette, cross-component cycle, finite cyclic lift, or laceability is asserted. The numeric construction works for all a; the original even-a caller specializes it.
-/

namespace ErdosProblems.AntiRamseyChordPathWindow

/-- Reverse the prefix before d and fix the suffix starting at d. -/
def chordOrder {a : ℕ} (d : ℕ) (hdad : d + 2 ≤ a) (i : Fin a) : Fin a :=
  if hi : i.val < d then
    ⟨d - 1 - i.val, by omega⟩
  else i

theorem chordOrder_val_inside {a : ℕ} (d : ℕ) (hdad : d + 2 ≤ a)
    (i : Fin a) (hi : i.val < d) :
    (chordOrder d hdad i).val = d - 1 - i.val := by
  unfold chordOrder
  rw [dite_eq_left hi]

theorem chordOrder_outside {a : ℕ} (d : ℕ) (hdad : d + 2 ≤ a)
    (i : Fin a) (hi : ¬i.val < d) :
    chordOrder d hdad i = i := by
  unfold chordOrder
  exact dite_eq_right hi

theorem chordOrder_involutive {a : ℕ} (d : ℕ) (hdad : d + 2 ≤ a) :
    Function.Involutive (chordOrder d hdad) := by
  intro i
  by_cases hi : i.val < d
  · have hv := chordOrder_val_inside d hdad i hi
    have hinside : (chordOrder d hdad i).val < d := by omega
    apply Fin.val_injective
    rw [chordOrder_val_inside d hdad _ hinside, hv]
    omega
  · have hout := chordOrder_outside d hdad i hi
    rw [hout, hout]

theorem chordOrder_injective {a : ℕ} (d : ℕ) (hdad : d + 2 ≤ a) :
    Function.Injective (chordOrder d hdad) :=
  (chordOrder_involutive d hdad).injective

/-- Every consecutive pair is a reversed old edge, the single chord, or a forward old edge. -/
theorem chordOrder_ordered_adj {a : ℕ}
    (G : SimpleGraph (Fin a)) (d : ℕ) (hd2 : 2 ≤ d) (hdad : d + 2 ≤ a)
    (hconsecutive : ∀ x y : Fin a, x.val + 1 = y.val → G.Adj x y)
    (hchord : G.Adj ⟨0, by omega⟩ ⟨d, by omega⟩) :
    ∀ x y : Fin a, x.val + 1 = y.val →
      G.Adj (chordOrder d hdad x) (chordOrder d hdad y) := by
  intro x y hxy
  by_cases hy : y.val < d
  · have hx : x.val < d := by omega
    apply (hconsecutive (chordOrder d hdad y) (chordOrder d hdad x) ?_).symm
    rw [chordOrder_val_inside d hdad y hy, chordOrder_val_inside d hdad x hx]
    omega
  · by_cases hx : x.val < d
    · have hleft : chordOrder d hdad x = (⟨0, by omega⟩ : Fin a) := by
        apply Fin.val_injective
        rw [chordOrder_val_inside d hdad x hx]
        change d - 1 - x.val = 0
        omega
      have hright : chordOrder d hdad y = (⟨d, by omega⟩ : Fin a) := by
        rw [chordOrder_outside d hdad y hy]
        apply Fin.val_injective
        change y.val = d
        omega
      rw [hleft, hright]
      exact hchord
    · rw [chordOrder_outside d hdad x hx, chordOrder_outside d hdad y hy]
      exact hconsecutive x y hxy

/-- Start the window as late as possible subject to retaining the chord position. -/
def windowStart (a d L : ℕ) : ℕ := min (d - 1) (a - L)

theorem windowStart_bounds {a d L : ℕ}
    (hd2 : 2 ≤ d) (hdad : d + 2 ≤ a) (hL2 : 2 ≤ L) (hLa : L ≤ a) :
    windowStart a d L ≤ d - 1 ∧
      d ≤ windowStart a d L + L - 1 ∧ windowStart a d L + L ≤ a := by
  unfold windowStart
  by_cases hmin : d - 1 ≤ a - L
  · rw [Nat.min_eq_left hmin]
    omega
  · rw [Nat.min_eq_right (by omega : a - L ≤ d - 1)]
    omega

/-- The literal affine inclusion i ↦ s+i into the full path positions. -/
def windowIndex {a L : ℕ} (d : ℕ) (hLa : L ≤ a) (i : Fin L) : Fin a :=
  ⟨windowStart a d L + i.val, by
    have hi := i.isLt
    have hs : windowStart a d L ≤ a - L := Nat.min_le_right _ _
    omega⟩

/-- The literal L-vertex window of the chord path. -/
def windowOrder {a L : ℕ} (d : ℕ) (hdad : d + 2 ≤ a) (hLa : L ≤ a) :
    Fin L → Fin a :=
  fun i => chordOrder d hdad (windowIndex d hLa i)

theorem windowOrder_injective {a L : ℕ}
    (d : ℕ) (hdad : d + 2 ≤ a) (hLa : L ≤ a) :
    Function.Injective (windowOrder d hdad hLa) := by
  intro i j hij
  have hpos := chordOrder_injective d hdad hij
  have hval := congrArg Fin.val hpos
  apply Fin.val_injective
  change windowStart a d L + i.val = windowStart a d L + j.val at hval
  omega

theorem windowOrder_ordered_adj {a L : ℕ}
    (G : SimpleGraph (Fin a)) (d : ℕ) (hd2 : 2 ≤ d) (hdad : d + 2 ≤ a)
    (hLa : L ≤ a)
    (hconsecutive : ∀ x y : Fin a, x.val + 1 = y.val → G.Adj x y)
    (hchord : G.Adj ⟨0, by omega⟩ ⟨d, by omega⟩) :
    ∀ x y : Fin L, x.val + 1 = y.val →
      G.Adj (windowOrder d hdad hLa x) (windowOrder d hdad hLa y) := by
  intro x y hxy
  apply chordOrder_ordered_adj G d hd2 hdad hconsecutive hchord
    (windowIndex d hLa x) (windowIndex d hLa y)
  change windowStart a d L + x.val + 1 = windowStart a d L + y.val
  omega

/-- Every allowed window contains the same unordered chord in exactly one step. -/
theorem window_chord_once {a d L : ℕ}
    (hd2 : 2 ≤ d) (hdad : d + 2 ≤ a) (hL2 : 2 ≤ L) (hLa : L ≤ a) :
    ∃! i : Fin (L - 1),
      s(windowOrder d hdad hLa ⟨i.val, by have hi := i.isLt; omega⟩,
        windowOrder d hdad hLa ⟨i.val + 1, by have hi := i.isLt; omega⟩) =
      s((⟨0, by omega⟩ : Fin a), (⟨d, by omega⟩ : Fin a)) := by
  have hbounds := windowStart_bounds hd2 hdad hL2 hLa
  let c : Fin (L - 1) := ⟨d - 1 - windowStart a d L, by omega⟩
  have hc : c.val = d - 1 - windowStart a d L := rfl
  have hleftpos :
      (windowIndex d hLa (⟨c.val, by have hi := c.isLt; omega⟩ : Fin L)).val =
      d - 1 := by
    change windowStart a d L + c.val = d - 1
    rw [hc]
    omega
  have hrightpos :
      (windowIndex d hLa (⟨c.val + 1, by have hi := c.isLt; omega⟩ : Fin L)).val =
      d := by
    change windowStart a d L + (c.val + 1) = d
    rw [hc]
    omega
  have hzero :
      windowOrder d hdad hLa (⟨c.val, by have hi := c.isLt; omega⟩ : Fin L) =
      (⟨0, by omega⟩ : Fin a) := by
    apply Fin.val_injective
    change (chordOrder d hdad (windowIndex d hLa _)).val = 0
    rw [chordOrder_val_inside d hdad _ (by omega), hleftpos]
    omega
  have hdvertex :
      windowOrder d hdad hLa (⟨c.val + 1, by have hi := c.isLt; omega⟩ : Fin L) =
      (⟨d, by omega⟩ : Fin a) := by
    change chordOrder d hdad (windowIndex d hLa _) = _
    rw [chordOrder_outside d hdad _ (by omega)]
    apply Fin.val_injective
    exact hrightpos
  refine ⟨c, ?_, ?_⟩
  · change s(windowOrder d hdad hLa (⟨c.val, by have hi := c.isLt; omega⟩ : Fin L),
        windowOrder d hdad hLa (⟨c.val + 1, by have hi := c.isLt; omega⟩ : Fin L)) =
      s((⟨0, by omega⟩ : Fin a), (⟨d, by omega⟩ : Fin a))
    rw [hzero, hdvertex]
  · intro i hi
    rcases Sym2.eq_iff.mp hi with ⟨hi0, hid⟩ | ⟨hid, hi0⟩
    · have hpos := windowOrder_injective d hdad hLa (hi0.trans hzero.symm)
      have hv := congrArg Fin.val hpos
      apply Fin.val_injective
      exact hv
    · have hpos_left := windowOrder_injective d hdad hLa (hid.trans hdvertex.symm)
      have hpos_right := windowOrder_injective d hdad hLa (hi0.trans hzero.symm)
      have hvleft := congrArg Fin.val hpos_left
      have hvright := congrArg Fin.val hpos_right
      change i.val = c.val + 1 at hvleft
      change i.val + 1 = c.val at hvright
      omega

theorem window_endpoint_values {a d L : ℕ}
    (hd2 : 2 ≤ d) (hdad : d + 2 ≤ a) (hL2 : 2 ≤ L) (hLa : L ≤ a) :
    (windowOrder d hdad hLa (⟨0, by omega⟩ : Fin L)).val =
        d - 1 - windowStart a d L ∧
    (windowOrder d hdad hLa (⟨L - 1, by omega⟩ : Fin L)).val =
        windowStart a d L + L - 1 := by
  have hbounds := windowStart_bounds hd2 hdad hL2 hLa
  constructor
  · change (chordOrder d hdad (windowIndex d hLa _)).val = _
    rw [chordOrder_val_inside d hdad _ (by
      change windowStart a d L + 0 < d
      omega)]
    change d - 1 - (windowStart a d L + 0) = _
    omega
  · change (chordOrder d hdad (windowIndex d hLa _)).val = _
    rw [chordOrder_outside d hdad _ (by
      change ¬windowStart a d L + (L - 1) < d
      omega)]
    change windowStart a d L + (L - 1) = windowStart a d L + L - 1
    omega

/-- A same-parity chord makes the window endpoints differ in parity by L, rather than L−1. -/
theorem window_endpoint_difference_emod_two {a d L : ℕ}
    (hd2 : 2 ≤ d) (hdad : d + 2 ≤ a) (hL2 : 2 ≤ L) (hLa : L ≤ a)
    (hdEven : Even d) :
    (((windowOrder d hdad hLa (⟨L - 1, by omega⟩ : Fin L)).val : ℤ) -
      ((windowOrder d hdad hLa (⟨0, by omega⟩ : Fin L)).val : ℤ)) % 2 =
      (L : ℤ) % 2 := by
  have hbounds := windowStart_bounds hd2 hdad hL2 hLa
  have hvalues := window_endpoint_values hd2 hdad hL2 hLa
  have hdmod := Nat.even_iff.mp hdEven
  rw [hvalues.1, hvalues.2]
  omega

/-- Equivalently, the sum of the endpoint indices has the parity of L. -/
theorem window_endpoint_sum_emod_two {a d L : ℕ}
    (hd2 : 2 ≤ d) (hdad : d + 2 ≤ a) (hL2 : 2 ≤ L) (hLa : L ≤ a)
    (hdEven : Even d) :
    (((windowOrder d hdad hLa (⟨L - 1, by omega⟩ : Fin L)).val : ℤ) +
      ((windowOrder d hdad hLa (⟨0, by omega⟩ : Fin L)).val : ℤ)) % 2 =
      (L : ℤ) % 2 := by
  have hbounds := windowStart_bounds hd2 hdad hL2 hLa
  have hvalues := window_endpoint_values hd2 hdad hL2 hLa
  have hdmod := Nat.even_iff.mp hdEven
  rw [hvalues.1, hvalues.2]
  omega

end ErdosProblems.AntiRamseyChordPathWindow
