module

/-
Copyright 2025-2026 The Formal Conjectures Authors (SimpleGraph.IsRainbow, SimpleGraph.antiRamseyNum).
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# CycleRepresentativeExchange

Private (`NEW`) vertex colors, representative subgraph exchanges, Claim 1 and Claim 2 cycle spoke/chord insertions, and cross-component matrix translations for Erdős Problem 1105.
-/

namespace SimpleGraph

/-- A homomorphism `f : H →g G` is rainbow for an edge labeling `c` of `G` if it maps distinct
edges of `H` to edges of `G` with distinct labels. -/
def IsRainbow {α V K : Type*} {H : SimpleGraph α} {G : SimpleGraph V} (f : H →g G)
    (c : G.EdgeLabeling K) : Prop :=
  Function.Injective (c.pullback f)

/-- The anti-Ramsey number $\mathrm{AR}(n, H)$: the maximum number of colors in an edge coloring of
$K_n$ (that is, a labeling of the edges of $K_n$ using every color) that contains no rainbow copy
of $H$, i.e. no injective homomorphism (copy) of $H$ whose edges all receive different colors. -/
noncomputable def antiRamseyNum {α : Type*} [Fintype α] (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {k | ∃ c : TopEdgeLabeling (Fin n) (Fin k), Function.Surjective c ∧
    ∀ f : H.Copy ⊤, ¬IsRainbow f.toHom c}

end SimpleGraph

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

namespace ErdosProblems.AntiRamseyCycleNewColors

open SimpleGraph

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Colors realized on all edges of the complete graph. -/
def usedColors (χ : TopEdgeLabeling (Fin n) C) : Finset C :=
  Finset.univ.image χ

/-- Colors realized on edges whose endpoints both avoid `v`. -/
def colorsAfterDeleting (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Finset C :=
  (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin n)).edgeSet =>
    v ∉ e.val)).image χ

/-- Colors realized on edges incident to `v`. -/
def incidentColors (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Finset C :=
  (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin n)).edgeSet =>
    v ∈ e.val)).image χ

/-- Choi's `NEWχ(v)`: incident colors that are absent after deleting `v`. -/
def newColors (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Finset C :=
  incidentColors χ v \ colorsAfterDeleting χ v

/-- Every realized color occurs either on an edge avoiding `v` or one
incident to `v`. This union may overlap when a color appears on both. -/
theorem usedColors_eq_deleted_union_incident
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n) :
    usedColors χ = colorsAfterDeleting χ v ∪ incidentColors χ v := by
  let f : (⊤ : SimpleGraph (Fin n)).edgeSet → C := χ
  change (Finset.univ : Finset ((⊤ : SimpleGraph (Fin n)).edgeSet)).image f =
    (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin n)).edgeSet =>
      v ∉ e.val)).image f ∪
    (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin n)).edgeSet =>
      v ∈ e.val)).image f
  rw [← Finset.image_union]
  congr 1
  ext e
  by_cases hv : v ∈ e.val <;> simp [hv]

/-- Exact color-count recurrence for deleting any vertex of a finite
complete graph, including cases where colors are reused on both sides. -/
theorem usedColors_card_delete_add_new
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n) :
    (usedColors χ).card = (colorsAfterDeleting χ v).card + (newColors χ v).card := by
  have hcard := Finset.card_sdiff_add_card (incidentColors χ v)
    (colorsAfterDeleting χ v)
  calc
    (usedColors χ).card = (colorsAfterDeleting χ v ∪ incidentColors χ v).card := by
      rw [usedColors_eq_deleted_union_incident]
    _ = (incidentColors χ v ∪ colorsAfterDeleting χ v).card := by
      rw [Finset.union_comm]
    _ = (newColors χ v).card + (colorsAfterDeleting χ v).card := by
      simpa only [newColors] using hcard.symm
    _ = (colorsAfterDeleting χ v).card + (newColors χ v).card := by
      omega

/-- When the current Formal Conjectures coloring uses every `Fin q` color,
the left side of the recurrence is exactly `q`. -/
theorem surjective_color_count_delete_add_new {q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (v : Fin n) :
    q = (colorsAfterDeleting χ v).card + (newColors χ v).card := by
  have hused : usedColors χ = Finset.univ := by
    simpa only [usedColors] using Finset.image_univ_of_surjective hχ
  simpa [hused] using usedColors_card_delete_add_new χ v

/-- A complete graph with at least two vertices has a realized edge color.
This records a nonempty instance of the recurrence. -/
theorem usedColors_nonempty_of_two_le (χ : TopEdgeLabeling (Fin n) C)
    (hn : 2 ≤ n) : (usedColors χ).Nonempty := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    simp [a, b] at hval
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨s(a, b), (SimpleGraph.mem_edgeSet ⊤).mpr ((SimpleGraph.top_adj a b).mpr hab)⟩
  exact ⟨χ e, by
    unfold usedColors
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩

end ErdosProblems.AntiRamseyCycleNewColors

namespace ErdosProblems.AntiRamseyCycleNewRepresentative

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The union of all color sets new at a vertex. -/
def newColorUnion (χ : TopEdgeLabeling (Fin n) C) : Finset C :=
  Finset.univ.biUnion (newColors χ)

theorem mem_newColorUnion_of_mem (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) {c : C} (hc : c ∈ newColors χ v) :
    c ∈ newColorUnion χ := by
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hc⟩

theorem newColor_occurs (χ : TopEdgeLabeling (Fin n) C)
    {c : C} (hc : c ∈ newColorUnion χ) :
    ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet, χ e = c := by
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hc
  have hv' : c ∈ incidentColors χ v \ colorsAfterDeleting χ v := hv
  have hinc : c ∈ incidentColors χ v := (Finset.mem_sdiff.mp hv').1
  unfold incidentColors at hinc
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hinc
  exact ⟨e, he⟩

/-- Any occurrence of a color new at v must be incident to v. -/
theorem newColor_every_edge_incident (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) {c : C} (hc : c ∈ newColors χ v)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (he : χ e = c) :
    v ∈ e.val := by
  have hc' : c ∈ incidentColors χ v \ colorsAfterDeleting χ v := hc
  have hnot : c ∉ colorsAfterDeleting χ v := (Finset.mem_sdiff.mp hc').2
  by_contra hv
  have hdel : c ∈ colorsAfterDeleting χ v := by
    unfold colorsAfterDeleting
    exact Finset.mem_image.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, he⟩
  exact hnot hdel

/-- If a color is new at two distinct vertices, it can occur only on
their common edge. The two NEW sets therefore have a consistent selection. -/
theorem shared_newColor_unique_edge (χ : TopEdgeLabeling (Fin n) C)
    (v w : Fin n) (hvw : v ≠ w) {c : C}
    (hv : c ∈ newColors χ v) (hw : c ∈ newColors χ w)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) (he : χ e = c) :
    e.val = s(v, w) := by
  exact (Sym2.mem_and_mem_iff hvw).mp
    ⟨newColor_every_edge_incident χ v hv e he,
      newColor_every_edge_incident χ w hw e he⟩

/-- A color new at two endpoints cannot be new at a third vertex. -/
theorem shared_newColor_only_endpoints (χ : TopEdgeLabeling (Fin n) C)
    (v w u : Fin n) (hvw : v ≠ w) {c : C}
    (hv : c ∈ newColors χ v) (hw : c ∈ newColors χ w)
    (hu : c ∈ newColors χ u) :
    u = v ∨ u = w := by
  obtain ⟨e, he⟩ :=
    newColor_occurs χ (mem_newColorUnion_of_mem χ v hv)
  have hpair := shared_newColor_unique_edge χ v w hvw hv hw e he
  have hinc := newColor_every_edge_incident χ u hu e he
  rw [hpair] at hinc
  simpa only [Sym2.mem_iff] using hinc

/-- Choose one host edge for a color that is new at some vertex. -/
noncomputable def chosenNewEdge (χ : TopEdgeLabeling (Fin n) C)
    (c : newColorUnion χ) : (⊤ : SimpleGraph (Fin n)).edgeSet :=
  Classical.choose (newColor_occurs χ c.property)

theorem chosenNewEdge_color (χ : TopEdgeLabeling (Fin n) C)
    (c : newColorUnion χ) : χ (chosenNewEdge χ c) = c.val :=
  Classical.choose_spec (newColor_occurs χ c.property)

theorem chosenNewEdge_injective (χ : TopEdgeLabeling (Fin n) C) :
    Function.Injective (fun c : newColorUnion χ => (chosenNewEdge χ c).val) := by
  intro a b hab
  have hedge : chosenNewEdge χ a = chosenNewEdge χ b := Subtype.ext hab
  have hcolor : a.val = b.val := by
    calc
      a.val = χ (chosenNewEdge χ a) := (chosenNewEdge_color χ a).symm
      _ = χ (chosenNewEdge χ b) := by rw [hedge]
      _ = b.val := chosenNewEdge_color χ b
  exact Subtype.ext hcolor

/-- The spanning graph with exactly the selected NEW-color edges. -/
noncomputable def newColorRepresentative
    (χ : TopEdgeLabeling (Fin n) C) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    (Set.range fun c : newColorUnion χ => (chosenNewEdge χ c).val)

/-- The selected graph is finite at every vertex, including empty cases. -/
noncomputable instance newColorRepresentative_neighborSet_fintype
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n) :
    Fintype ((newColorRepresentative χ).neighborSet v) := Fintype.ofFinite _

theorem chosenNewEdge_not_diag (χ : TopEdgeLabeling (Fin n) C)
    (c : newColorUnion χ) :
    ¬ ((chosenNewEdge χ c).val : Sym2 (Fin n)).IsDiag :=
  (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
    (chosenNewEdge χ c).property

/-- The graph has no other edges besides its one choice per NEW color. -/
theorem newColorRepresentative_edgeSet (χ : TopEdgeLabeling (Fin n) C) :
    (newColorRepresentative χ).edgeSet =
      Set.range (fun c : newColorUnion χ => (chosenNewEdge χ c).val) := by
  rw [newColorRepresentative, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c, rfl⟩, chosenNewEdge_not_diag χ c⟩

theorem chosenNewEdge_mem_representative (χ : TopEdgeLabeling (Fin n) C)
    (c : newColorUnion χ) :
    (chosenNewEdge χ c).val ∈ (newColorRepresentative χ).edgeSet := by
  rw [newColorRepresentative_edgeSet]
  exact ⟨c, rfl⟩

def liftNewColor (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) : newColorUnion χ :=
  ⟨c.val, mem_newColorUnion_of_mem χ v c.property⟩

/-- Send a color new at v to its selected incident edge. -/
noncomputable def newColorIncidenceEdge (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) :
    (newColorRepresentative χ).incidenceSet v := by
  let d : newColorUnion χ := liftNewColor χ v c
  refine ⟨(chosenNewEdge χ d).val, ?_⟩
  change (chosenNewEdge χ d).val ∈ (newColorRepresentative χ).edgeSet ∧
    v ∈ (chosenNewEdge χ d).val
  exact ⟨chosenNewEdge_mem_representative χ d,
    newColor_every_edge_incident χ v c.property
      (chosenNewEdge χ d) (by simpa [d, liftNewColor] using chosenNewEdge_color χ d)⟩

theorem newColorIncidenceEdge_injective (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Function.Injective (newColorIncidenceEdge χ v) := by
  intro a b hab
  have hval := congrArg Subtype.val hab
  change (chosenNewEdge χ (liftNewColor χ v a)).val =
    (chosenNewEdge χ (liftNewColor χ v b)).val at hval
  have hedge : chosenNewEdge χ (liftNewColor χ v a) =
      chosenNewEdge χ (liftNewColor χ v b) := Subtype.ext hval
  apply Subtype.ext
  calc
    a.val = χ (chosenNewEdge χ (liftNewColor χ v a)) := by
      simpa [liftNewColor] using (chosenNewEdge_color χ (liftNewColor χ v a)).symm
    _ = χ (chosenNewEdge χ (liftNewColor χ v b)) := by rw [hedge]
    _ = b.val := by
      simpa [liftNewColor] using chosenNewEdge_color χ (liftNewColor χ v b)

/-- Every NEW color at v provides a distinct edge incident to v in the
NEW-color representing graph. No no-rainbow or surjectivity premise is needed. -/
theorem newColorRepresentative_degree_ge_newColors
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n) :
    (newColors χ v).card ≤ (newColorRepresentative χ).degree v := by
  classical
  have hcard : Fintype.card (newColors χ v) ≤
      Fintype.card ((newColorRepresentative χ).incidenceSet v) :=
    Fintype.card_le_of_injective (newColorIncidenceEdge χ v)
      (newColorIncidenceEdge_injective χ v)
  simpa only [Fintype.card_coe, SimpleGraph.card_incidenceSet_eq_degree] using hcard

end ErdosProblems.AntiRamseyCycleNewRepresentative

namespace ErdosProblems.AntiRamseyCycleNewChoiceExchange

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative

variable {n : ℕ} {C : Type*} [DecidableEq C]

abbrev HostEdge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet

/-- One chosen host edge for each color in the realized union of NEW sets. -/
structure NewChoice (χ : TopEdgeLabeling (Fin n) C) where
  edge : newColorUnion χ → HostEdge n
  color_eq : ∀ c : newColorUnion χ, χ (edge c) = c.val

noncomputable def canonicalChoice (χ : TopEdgeLabeling (Fin n) C) : NewChoice χ where
  edge := chosenNewEdge χ
  color_eq := chosenNewEdge_color χ

/-- The spanning graph consisting precisely of a choice's host edges. -/
noncomputable def selectedGraph (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    (Set.range fun c : newColorUnion χ => (r.edge c).val)

theorem NewChoice.edge_injective {χ : TopEdgeLabeling (Fin n) C}
    (r : NewChoice χ) : Function.Injective r.edge := by
  intro a b hab
  apply Subtype.ext
  calc
    a.val = χ (r.edge a) := (r.color_eq a).symm
    _ = χ (r.edge b) := by rw [hab]
    _ = b.val := r.color_eq b

theorem choice_edge_not_diag (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (c : newColorUnion χ) :
    ¬ ((r.edge c).val : Sym2 (Fin n)).IsDiag :=
  (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
    (r.edge c).property

/-- The selected graph has no edge outside the choice's range. -/
theorem selectedGraph_edgeSet (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) :
    (selectedGraph χ r).edgeSet =
      Set.range (fun c : newColorUnion χ => (r.edge c).val) := by
  rw [selectedGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c, rfl⟩, choice_edge_not_diag χ r c⟩

/-- Exchange exactly the selected edge of the input edge's NEW-union color.
The membership guard creates the necessary subtype index. -/
def NewChoice.replace {χ : TopEdgeLabeling (Fin n) C}
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) : NewChoice χ :=
  let ce : newColorUnion χ := ⟨χ e, he⟩
  { edge := fun c => if c = ce then e else r.edge c
    color_eq := by
      intro c
      by_cases hc : c = ce
      · subst c
        simp [ce]
      · simpa [hc] using r.color_eq c }

theorem NewChoice.replace_edge_same {χ : TopEdgeLabeling (Fin n) C}
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) :
    (r.replace e he).edge (⟨χ e, he⟩ : newColorUnion χ) = e := by
  simp [NewChoice.replace]

theorem NewChoice.replace_edge_other {χ : TopEdgeLabeling (Fin n) C}
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) {c : newColorUnion χ}
    (hc : c ≠ (⟨χ e, he⟩ : newColorUnion χ)) :
    (r.replace e he).edge c = r.edge c := by
  simp [NewChoice.replace, hc]

/-- Removing the replaced selected edge leaves a subgraph of the exchanged
choice graph. -/
theorem delete_selectedEdge_le_replace
    (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) :
    (selectedGraph χ r).deleteEdges
      {(r.edge (⟨χ e, he⟩ : newColorUnion χ)).val} ≤
      selectedGraph χ (r.replace e he) := by
  let ce : newColorUnion χ := ⟨χ e, he⟩
  change (selectedGraph χ r).deleteEdges {(r.edge ce).val} ≤
    selectedGraph χ (r.replace e he)
  intro u v huv
  have hL : (selectedGraph χ r).Adj u v :=
    (SimpleGraph.deleteEdges_adj.mp huv).1
  have hneq : s(u, v) ≠ (r.edge ce).val := by
    simpa using (SimpleGraph.deleteEdges_adj.mp huv).2
  have hmem : s(u, v) ∈
      Set.range (fun c : newColorUnion χ => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact hL
  obtain ⟨c, hc⟩ := hmem
  have hother : c ≠ ce := by
    intro h
    apply hneq
    calc
      s(u, v) = (r.edge c).val := hc.symm
      _ = (r.edge ce).val := by rw [h]
  have hnew : s(u, v) ∈ (selectedGraph χ (r.replace e he)).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, by simpa only [r.replace_edge_other e he hother] using hc⟩
  exact hnew

/-- The input host edge belongs to the graph after the guarded exchange. -/
theorem replacedEdge_mem
    (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ) :
    e.val ∈ (selectedGraph χ (r.replace e he)).edgeSet := by
  rw [selectedGraph_edgeSet]
  refine ⟨⟨χ e, he⟩, ?_⟩
  simp only [r.replace_edge_same e he]

/-- Restrict the complete-host labeling to an arbitrary NEW choice graph. -/
def restrictedColor (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) : (selectedGraph χ r).edgeSet → C :=
  fun e => χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩

/-- A valid choice selects at most one edge of each NEW-union color. -/
theorem restrictedColor_injective (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) : Function.Injective (restrictedColor χ r) := by
  intro e₁ e₂ heq
  have he₁ : e₁.val ∈
      Set.range (fun c : newColorUnion χ => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e₁.property
  have he₂ : e₂.val ∈
      Set.range (fun c : newColorUnion χ => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e₂.property
  obtain ⟨c₁, hc₁⟩ := he₁
  obtain ⟨c₂, hc₂⟩ := he₂
  have hcolor₁ : restrictedColor χ r e₁ = c₁.val := by
    have hval : e₁.val = (r.edge c₁).val := hc₁.symm
    simpa [restrictedColor, hval] using r.color_eq c₁
  have hcolor₂ : restrictedColor χ r e₂ = c₂.val := by
    have hval : e₂.val = (r.edge c₂).val := hc₂.symm
    simpa [restrictedColor, hval] using r.color_eq c₂
  have hcolors : c₁.val = c₂.val :=
    hcolor₁.symm.trans (heq.trans hcolor₂)
  have hc : c₁ = c₂ := Subtype.ext hcolors
  apply Subtype.ext
  calc
    e₁.val = (r.edge c₁).val := hc₁.symm
    _ = (r.edge c₂).val := by rw [hc]
    _ = e₂.val := hc₂

/-- Every Copy in every NEW choice graph is a literal rainbow host Copy. -/
theorem copy_in_selectedGraph_isRainbow
    {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (f : H.Copy (selectedGraph χ r)) :
    IsRainbow ((Copy.ofLE (selectedGraph χ r)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom χ := by
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ r)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f
  change Function.Injective (EdgeLabeling.pullback χ g.toHom)
  have hcolors (e : H.edgeSet) :
      EdgeLabeling.pullback χ g.toHom e =
        restrictedColor χ r (f.mapEdgeSet e) := by
    have hval : (g.toHom.mapEdgeSet e).val =
        (f.mapEdgeSet e).val := by
      simp [g, Copy.comp, Copy.ofLE, Hom.mapEdgeSet]
      rfl
    exact congrArg χ (Subtype.ext hval)
  intro e₁ e₂ hcolorsEq
  apply f.mapEdgeSet.injective
  exact restrictedColor_injective χ r
    ((hcolors e₁).symm.trans (hcolorsEq.trans (hcolors e₂)))

/-- The literal no-rainbow host premise makes every valid choice graph free. -/
theorem selectedGraph_free {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    H.Free (selectedGraph χ r) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact hno _ (copy_in_selectedGraph_isRainbow χ r f)

/-- Guarded replacement retains other edges, inserts the given edge, and
preserves ordinary `H.Free` under the literal host no-rainbow premise. -/
theorem replace_semantics {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (e : HostEdge n)
    (he : χ e ∈ newColorUnion χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    (selectedGraph χ r).deleteEdges
        {(r.edge (⟨χ e, he⟩ : newColorUnion χ)).val} ≤
        selectedGraph χ (r.replace e he) ∧
    e.val ∈ (selectedGraph χ (r.replace e he)).edgeSet ∧
    H.Free (selectedGraph χ (r.replace e he)) := by
  exact ⟨delete_selectedEdge_le_replace χ r e he,
    replacedEdge_mem χ r e he,
    selectedGraph_free H χ (r.replace e he) hno⟩

end ErdosProblems.AntiRamseyCycleNewChoiceExchange

namespace ErdosProblems.AntiRamseyCycleOrderedEdges

open SimpleGraph

theorem cycle_adj_cases {m : ℕ} (_hm : 2 ≤ m)
    {a b : Fin (m + 1)} (hab : (cycleGraph (m + 1)).Adj a b) :
    a.val + 1 = b.val ∨ b.val + 1 = a.val ∨
      (a.val = 0 ∧ b.val = m) ∨
      (b.val = 0 ∧ a.val = m) := by
  rw [cycleGraph_adj'] at hab
  rcases hab with h | h
  · by_cases hle : b ≤ a
    · have hsub : (a - b).val = a.val - b.val := Fin.sub_val_of_le hle
      rw [hsub] at h
      right; left
      omega
    · have hlt : a < b := lt_of_not_ge hle
      have hsub : (a - b).val = m + 1 + a.val - b.val :=
        Fin.coe_sub_iff_lt.mpr hlt
      rw [hsub] at h
      have hb := b.isLt
      right; right; left
      omega
  · by_cases hle : a ≤ b
    · have hsub : (b - a).val = b.val - a.val := Fin.sub_val_of_le hle
      rw [hsub] at h
      left
      omega
    · have hlt : b < a := lt_of_not_ge hle
      have hsub : (b - a).val = m + 1 + b.val - a.val :=
        Fin.coe_sub_iff_lt.mpr hlt
      rw [hsub] at h
      have ha := a.isLt
      right; right; right
      omega

/-- The source edge between the consecutive positions `i` and `i+1`. -/
def sourceStep {m : ℕ} (i : Fin m) : (cycleGraph (m + 1)).edgeSet :=
  ⟨s(Fin.castSucc i, Fin.succ i), by
    apply (SimpleGraph.mem_edgeSet _).mpr
    apply pathGraph_le_cycleGraph
    rw [pathGraph_adj]
    left
    simp only [Fin.val_castSucc, Fin.val_succ]⟩

/-- The source edge from the final position back to zero. -/
def sourceClosing (m : ℕ) (_hm : 2 ≤ m) :
    (cycleGraph (m + 1)).edgeSet :=
  ⟨s((0 : Fin (m + 1)), Fin.last m), by
    apply (SimpleGraph.mem_edgeSet _).mpr
    rw [cycleGraph_adj']
    left
    have hlt : (0 : Fin (m + 1)) < Fin.last m := by
      simp [Fin.lt_def, Fin.val_last]
      omega
    rw [Fin.coe_sub_iff_lt.mpr hlt]
    simp only [Fin.val_zero, Fin.val_last]
    omega⟩

/-- Consecutive source edges have different indices. -/
theorem sourceStep_injective {m : ℕ} :
    Function.Injective (sourceStep (m := m)) := by
  intro i j hij
  have hv := congrArg Subtype.val hij
  change s(Fin.castSucc i, Fin.succ i) =
    s(Fin.castSucc j, Fin.succ j) at hv
  rcases (Sym2.eq_iff.mp hv) with h | h
  · exact Fin.castSucc_injective m h.1
  · have hi := congrArg Fin.val h.1
    have hj := congrArg Fin.val h.2
    simp only [Fin.val_castSucc, Fin.val_succ] at hi hj
    have hii := i.isLt
    have hjj := j.isLt
    omega

/-- The closing edge is not any consecutive edge for cycles of length
at least three. -/
theorem sourceStep_ne_closing {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    sourceStep i ≠ sourceClosing m hm := by
  intro heq
  have hv := congrArg Subtype.val heq
  change s(Fin.castSucc i, Fin.succ i) =
    s((0 : Fin (m + 1)), Fin.last m) at hv
  rcases (Sym2.eq_iff.mp hv) with h | h
  · have h0 := congrArg Fin.val h.1
    have hlast := congrArg Fin.val h.2
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero,
      Fin.val_last] at h0 hlast
    omega
  · have hlast := congrArg Fin.val h.1
    simp only [Fin.val_castSucc, Fin.val_last] at hlast
    have hi := i.isLt
    omega

/-- Every edge of the literal source cycle is a consecutive edge or
its closing edge. No induced-copy assumption is used. -/
theorem sourceEdge_cases {m : ℕ} (hm : 2 ≤ m)
    (e : (cycleGraph (m + 1)).edgeSet) :
    (∃ i : Fin m, e = sourceStep i) ∨ e = sourceClosing m hm := by
  obtain ⟨q, hq⟩ := e
  induction q using Sym2.inductionOn with
  | _ a b =>
    have hab : (cycleGraph (m + 1)).Adj a b :=
      (SimpleGraph.mem_edgeSet _).mp hq
    rcases cycle_adj_cases hm hab with hsucc | hsucc | hclose | hclose
    · have hi : a.val < m := by
        have hb := b.isLt
        omega
      let i : Fin m := ⟨a.val, hi⟩
      have ha : a = Fin.castSucc i := Fin.ext (by rfl)
      have hb : b = Fin.succ i := Fin.ext (by
        simp only [Fin.val_succ, i]
        exact hsucc.symm)
      left
      refine ⟨i, ?_⟩
      apply Subtype.ext
      change s(a, b) = s(Fin.castSucc i, Fin.succ i)
      rw [ha, hb]
    · have hi : b.val < m := by
        have ha := a.isLt
        omega
      let i : Fin m := ⟨b.val, hi⟩
      have hb : b = Fin.castSucc i := Fin.ext (by rfl)
      have ha : a = Fin.succ i := Fin.ext (by
        simp only [Fin.val_succ, i]
        exact hsucc.symm)
      left
      refine ⟨i, ?_⟩
      apply Subtype.ext
      change s(a, b) = s(Fin.castSucc i, Fin.succ i)
      rw [ha, hb]
      exact Sym2.eq_swap
    · have ha : a = (0 : Fin (m + 1)) :=
        Fin.ext (by simpa using hclose.1)
      have hb : b = Fin.last m :=
        Fin.ext (by simpa only [Fin.val_last] using hclose.2)
      right
      apply Subtype.ext
      change s(a, b) = s((0 : Fin (m + 1)), Fin.last m)
      rw [ha, hb]
    · have hb : b = (0 : Fin (m + 1)) :=
        Fin.ext (by simpa using hclose.1)
      have ha : a = Fin.last m :=
        Fin.ext (by simpa only [Fin.val_last] using hclose.2)
      right
      apply Subtype.ext
      change s(a, b) = s((0 : Fin (m + 1)), Fin.last m)
      rw [ha, hb]
      exact Sym2.eq_swap

end ErdosProblems.AntiRamseyCycleOrderedEdges

namespace ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A complete-host spoke to a vertex of a selected cycle, with its required
distinctness derived from the outside-vertex condition. -/
def outsiderEdge {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (i : Fin (m + 1)) : HostEdge n :=
  ⟨s(u, cyc.toHom i), (top_adj _ _).mpr (by
    intro h
    exact hu ⟨i, h.symm⟩)⟩

/-- The fixed-choice selected-endpoint theorem does not apply to an arbitrary
`NewChoice`. This is the needed local analogue, proved directly from the
choice's color equality and the checked vertex-deletion semantics. -/
theorem arbitrary_selected_edge_has_new_endpoint
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : (selectedGraph χ r).edgeSet) :
    ∃ v : Fin n, v ∈ e.val ∧
      restrictedColor χ r e ∈ newColors χ v := by
  have he : e.val ∈
      Set.range (fun d : newColorUnion χ => (r.edge d).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e.property
  obtain ⟨d, hd⟩ := he
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp d.property
  have hval : e.val = (r.edge d).val := hd.symm
  have hcolor : restrictedColor χ r e = d.val := by
    simpa [restrictedColor, hval] using r.color_eq d
  have hinc : v ∈ e.val := by
    rw [hval]
    exact newColor_every_edge_incident χ v hv (r.edge d) (r.color_eq d)
  exact ⟨v, hinc, by simpa only [hcolor] using hv⟩

/-- A complete-host edge disjoint from an arbitrary selected edge cannot
repeat the selected edge's label. -/
theorem arbitrary_selected_edge_ne_disjoint_host_edge
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : (selectedGraph χ r).edgeSet) (f : HostEdge n)
    (hdisj : ∀ v : Fin n, v ∈ e.val → v ∉ f.val) :
    restrictedColor χ r e ≠ χ f := by
  obtain ⟨v, hve, hnew⟩ :=
    arbitrary_selected_edge_has_new_endpoint χ r e
  intro heq
  have hvf := newColor_every_edge_incident χ v hnew f heq.symm
  exact (hdisj v hve) hvf

/-- Insert the outside vertex at position one: the order is
`(v₁,u,v₂,…,vₘ₊₁)`. -/
def firstInsertionMap {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) : Fin ((m + 1) + 1) → Fin n :=
  Fin.insertNth (α := fun _ => Fin n)
    (1 : Fin ((m + 1) + 1)) u cyc.toHom

theorem firstInsertionMap_zero {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    firstInsertionMap cyc u 0 = cyc.toHom 0 := by
  have h : Fin.insertNth (α := fun _ => Fin n)
      (1 : Fin ((m + 1) + 1)) u cyc.toHom
      ((1 : Fin ((m + 1) + 1)).succAbove (0 : Fin (m + 1))) =
        cyc.toHom 0 :=
    Fin.insertNth_apply_succAbove (α := fun _ => Fin n)
      (1 : Fin ((m + 1) + 1)) u cyc.toHom 0
  simpa only [firstInsertionMap, Fin.one_succAbove_zero] using h

theorem firstInsertionMap_one {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    firstInsertionMap cyc u 1 = u := by
  simp only [firstInsertionMap, Fin.insertNth_apply_same]

theorem firstInsertionMap_succ_of_pos {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (j : Fin (m + 1)) (hj : 1 ≤ j.val) :
    firstInsertionMap cyc u (Fin.succ j) = cyc.toHom j := by
  have hone : ((1 : Fin ((m + 1) + 1)) : ℕ) = 1 := by
    have hlt : 1 < (m + 1) + 1 := by omega
    rw [Fin.val_one' ((m + 1) + 1), Nat.mod_eq_of_lt hlt]
  have hlt : (1 : Fin ((m + 1) + 1)) < Fin.succ j := by
    simp only [Fin.lt_def, Fin.val_succ]
    rw [hone]
    omega
  unfold firstInsertionMap
  rw [← Fin.succAbove_of_lt_succ _ _ hlt]
  exact Fin.insertNth_apply_succAbove (α := fun _ => Fin n)
    (1 : Fin ((m + 1) + 1)) u cyc.toHom j

/-- Every host step after the two inserted spokes is exactly a selected
source-cycle step, with the latter index one smaller. -/
theorem firstInsertionMap_step_ge_two {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (i : Fin (m + 1)) (hi : 2 ≤ i.val) :
    ∃ j : Fin m, j.val + 1 = i.val ∧ 1 ≤ j.val ∧
      Sym2.map (firstInsertionMap cyc u) (sourceStep i).val =
        Sym2.map cyc.toHom (sourceStep j).val := by
  let j : Fin m := ⟨i.val - 1, by omega⟩
  have hjEq : j.val + 1 = i.val := by dsimp [j]; omega
  have hj : 1 ≤ j.val := by dsimp [j]; omega
  refine ⟨j, hjEq, hj, ?_⟩
  have hloIndex : Fin.castSucc i = Fin.succ (Fin.castSucc j) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ]
    dsimp [j]
    omega
  have hhiIndex : Fin.succ i = Fin.succ (Fin.succ j) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp [j]
    omega
  have hlo : firstInsertionMap cyc u (Fin.castSucc i) =
      cyc.toHom (Fin.castSucc j) := by
    rw [hloIndex]
    exact firstInsertionMap_succ_of_pos cyc u (Fin.castSucc j)
      (by simpa only [Fin.val_castSucc] using hj)
  have hhi : firstInsertionMap cyc u (Fin.succ i) =
      cyc.toHom (Fin.succ j) := by
    rw [hhiIndex]
    exact firstInsertionMap_succ_of_pos cyc u (Fin.succ j)
      (by simp only [Fin.val_succ]; omega)
  simp only [sourceStep, Sym2.map_mk]
  rw [hlo, hhi]

/-- The closing host edge is precisely the selected source-cycle closing
edge. -/
theorem firstInsertionMap_closing {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    Sym2.map (firstInsertionMap cyc u)
      (sourceClosing (m + 1) (by omega)).val =
    Sym2.map cyc.toHom (sourceClosing m hm).val := by
  have hlastIndex : Fin.last (m + 1) = Fin.succ (Fin.last m) := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_succ]
  have hlast : firstInsertionMap cyc u (Fin.last (m + 1)) =
      cyc.toHom (Fin.last m) := by
    rw [hlastIndex]
    exact firstInsertionMap_succ_of_pos cyc u (Fin.last m)
      (by simp only [Fin.val_last]; omega)
  simp only [sourceClosing, Sym2.map_mk]
  rw [firstInsertionMap_zero, hlast]

theorem firstInsertionMap_first_spoke {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (firstInsertionMap cyc u)
      (sourceStep (0 : Fin (m + 1))).val =
      (outsiderEdge cyc u hu 0).val := by
  change s(firstInsertionMap cyc u 0,
      firstInsertionMap cyc u 1) = s(u, cyc.toHom 0)
  rw [firstInsertionMap_zero, firstInsertionMap_one]
  exact Sym2.eq_swap

theorem firstInsertionMap_second_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (firstInsertionMap cyc u)
      (sourceStep (1 : Fin (m + 1))).val =
      (outsiderEdge cyc u hu 1).val := by
  simp only [sourceStep, outsiderEdge, Sym2.map_mk]
  have honeSmall : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    have hlt : 1 < m + 1 := by omega
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt hlt]
  have honeLarge : ((1 : Fin ((m + 1) + 1)) : ℕ) = 1 := by
    have hlt : 1 < (m + 1) + 1 := by omega
    rw [Fin.val_one' ((m + 1) + 1), Nat.mod_eq_of_lt hlt]
  have hcast : Fin.castSucc (1 : Fin (m + 1)) =
      (1 : Fin ((m + 1) + 1)) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, honeSmall, honeLarge]
  rw [hcast]
  rw [firstInsertionMap_one]
  have hpos : 1 ≤ (1 : Fin (m + 1)).val := by
    rw [honeSmall]
  rw [firstInsertionMap_succ_of_pos cyc u 1 hpos]

theorem firstInsertionMap_injective {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Function.Injective (firstInsertionMap cyc u) := by
  intro a b hab
  let t : Fin ((m + 1) + 1) := 1
  by_cases ha : a = t
  · subst a
    by_cases hb : b = t
    · exact hb.symm
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := t) hb
      subst b
      have hbad : u = cyc.toHom j := by
        simpa only [firstInsertionMap, t, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] using hab
      exact False.elim (hu ⟨j, hbad.symm⟩)
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (y := t) ha
    subst a
    by_cases hb : b = t
    · subst b
      have hbad : cyc.toHom i = u := by
        simpa only [firstInsertionMap, t, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] using hab
      exact False.elim (hu ⟨i, hbad⟩)
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := t) hb
      subst b
      have hij : cyc.toHom i = cyc.toHom j := by
        simpa only [firstInsertionMap, t,
          Fin.insertNth_apply_succAbove] using hab
      rw [cyc.injective hij]

/-- First Choi Claim 1 insertion. The selected cycle has `m+1 ≥ 3`
vertices, so the host cycle has `(m+1)+1` vertices. The only possible
unselected-spoke collision is explicitly excluded by `hbeta`. -/
theorem positive_first_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (hnewFirst : χ (outsiderEdge cyc u hu 0) ∈
      newColors χ (cyc.toHom 0))
    (hbeta : χ (outsiderEdge cyc u hu 1) ≠
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  let p := firstInsertionMap cyc u
  have hp : Function.Injective p :=
    firstInsertionMap_injective cyc u hu
  let φ : (cycleGraph ((m + 1) + 1)) →g
      (⊤ : SimpleGraph (Fin n)) :=
    ⟨p, by
      intro a b hab
      exact (top_adj _ _).mpr
        (hp.ne ((cycleGraph ((m + 1) + 1)).ne_of_adj hab))⟩
  let f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)) := ⟨φ, hp⟩

  have honeSmall : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    have hlt : 1 < m + 1 := by omega
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt hlt]

  let a : (selectedGraph χ r).edgeSet :=
    ⟨s(u, cyc.toHom 0), hattach⟩
  let closing : (selectedGraph χ r).edgeSet :=
    cyc.mapEdgeSet (sourceClosing m hm)
  have hαβ : χ (outsiderEdge cyc u hu 0) ≠
      χ (outsiderEdge cyc u hu 1) := by
    intro heq
    have hinc := newColor_every_edge_incident χ
      (cyc.toHom 0) hnewFirst (outsiderEdge cyc u hu 1) heq.symm
    have hcases : cyc.toHom 0 = u ∨
        cyc.toHom 0 = cyc.toHom 1 := by
      simpa only [outsiderEdge, Sym2.mem_iff] using hinc
    rcases hcases with h | h
    · exact hu ⟨0, h⟩
    · have h01 : (0 : Fin (m + 1)) = 1 := cyc.injective h
      have hval : (0 : ℕ) = 1 := by
        simpa only [Fin.val_zero, honeSmall] using congrArg Fin.val h01
      exact Nat.zero_ne_one hval
  have haColor : χ (outsiderEdge cyc u hu 0) =
      restrictedColor χ r a := by
    simp [outsiderEdge, restrictedColor, a]
  have huSelected (e : (cycleGraph (m + 1)).edgeSet) :
      u ∉ (cyc.mapEdgeSet e).val := by
    intro he
    change u ∈ Sym2.map cyc.toHom e.val at he
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp he
    exact hu ⟨i, hi⟩
  have hαSelected (e : (cycleGraph (m + 1)).edgeSet) :
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet e) := by
    intro heq
    have hae : a = cyc.mapEdgeSet e :=
      restrictedColor_injective χ r (haColor.symm.trans heq)
    have hua : u ∈ a.val := by
      simp [a, Sym2.mem_iff]
    exact huSelected e (hae ▸ hua)
  have hαclosing : χ (outsiderEdge cyc u hu 0) ≠
      restrictedColor χ r closing := hαSelected (sourceClosing m hm)
  have hβAvoid (e : (cycleGraph (m + 1)).edgeSet)
      (hv : cyc.toHom 1 ∉ (cyc.mapEdgeSet e).val) :
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet e) := by
    intro heq
    have hdisj : ∀ v : Fin n, v ∈ (cyc.mapEdgeSet e).val →
        v ∉ (outsiderEdge cyc u hu 1).val := by
      intro v hve hvspoke
      have hcases : v = u ∨ v = cyc.toHom 1 := by
        simpa only [outsiderEdge, Sym2.mem_iff] using hvspoke
      rcases hcases with h | h
      · subst v
        exact huSelected e hve
      · subst v
        exact hv hve
    exact (arbitrary_selected_edge_ne_disjoint_host_edge χ r
      (cyc.mapEdgeSet e) (outsiderEdge cyc u hu 1) hdisj) heq.symm
  have hcycleColors : Function.Injective
      (fun e : (cycleGraph (m + 1)).edgeSet =>
        restrictedColor χ r (cyc.mapEdgeSet e)) :=
    (restrictedColor_injective χ r).comp cyc.mapEdgeSet.injective

  let L := EdgeLabeling.pullback χ f.toHom
  let α : C := χ (outsiderEdge cyc u hu 0)
  let β : C := χ (outsiderEdge cyc u hu 1)
  have hcolor_of_host
      (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : HostEdge n)
      (hval : Sym2.map p e.val = d.val) : L e = χ d := by
    have hedges : f.toHom.mapEdgeSet e = d := by
      apply Subtype.ext
      change Sym2.map p e.val = d.val
      exact hval
    simpa only [L, EdgeLabeling.pullback_apply] using congrArg χ hedges
  have hcolor_of_selected
      (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map p e.val = Sym2.map cyc.toHom d.val) :
      L e = restrictedColor χ r (cyc.mapEdgeSet d) := by
    let selectedHostEdge : HostEdge n :=
      ⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
    have hedges : f.toHom.mapEdgeSet e = selectedHostEdge := by
      apply Subtype.ext
      change Sym2.map p e.val = Sym2.map cyc.toHom d.val
      exact hval
    simpa only [L, EdgeLabeling.pullback_apply, restrictedColor,
      selectedHostEdge] using congrArg χ hedges
  have hstep0 : L (sourceStep (0 : Fin (m + 1))) =
      χ (outsiderEdge cyc u hu 0) :=
    hcolor_of_host _ _ (firstInsertionMap_first_spoke cyc u hu)
  have hstep1 : L (sourceStep (1 : Fin (m + 1))) =
      χ (outsiderEdge cyc u hu 1) :=
    hcolor_of_host _ _ (firstInsertionMap_second_spoke hm cyc u hu)
  have htail (i : Fin (m + 1)) (hi : 2 ≤ i.val) :
      ∃ j : Fin m, j.val + 1 = i.val ∧ 1 ≤ j.val ∧
        L (sourceStep i) =
          restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    obtain ⟨j, hjEq, hj, hval⟩ :=
      firstInsertionMap_step_ge_two cyc u i hi
    exact ⟨j, hjEq, hj, hcolor_of_selected _ _ hval⟩
  have hclose : L (sourceClosing (m + 1) (by omega)) =
      restrictedColor χ r closing :=
    hcolor_of_selected _ _ (firstInsertionMap_closing hm cyc u)

  have hv1NotStep (j : Fin m) (hj : 2 ≤ j.val) :
      cyc.toHom 1 ∉ (cyc.mapEdgeSet (sourceStep j)).val := by
    intro hv
    change cyc.toHom 1 ∈
      Sym2.map cyc.toHom (sourceStep j).val at hv
    obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
    have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
    subst k
    change (1 : Fin (m + 1)) ∈
      s(Fin.castSucc j, Fin.succ j) at hk
    rcases Sym2.mem_iff.mp hk with h | h
    · have hidx : (1 : Fin (m + 1)) = Fin.castSucc j := h
      have hval : (1 : ℕ) = j.val := by
        simpa only [honeSmall, Fin.val_castSucc] using congrArg Fin.val hidx
      omega
    · have hidx : (1 : Fin (m + 1)) = Fin.succ j := h
      have hval : (1 : ℕ) = j.val + 1 := by
        simpa only [honeSmall, Fin.val_succ] using congrArg Fin.val hidx
      omega
  have hv1NotClosing : cyc.toHom 1 ∉ closing.val := by
    intro hv
    change cyc.toHom 1 ∈
      Sym2.map cyc.toHom (sourceClosing m hm).val at hv
    obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
    have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
    subst k
    change (1 : Fin (m + 1)) ∈
      s((0 : Fin (m + 1)), Fin.last m) at hk
    rcases Sym2.mem_iff.mp hk with h | h
    · have hidx : (1 : Fin (m + 1)) = 0 := h
      have hval : (1 : ℕ) = 0 := by
        simpa only [honeSmall, Fin.val_zero] using congrArg Fin.val hidx
      exact Nat.one_ne_zero hval
    · have hidx : (1 : Fin (m + 1)) = Fin.last m := h
      have hval : (1 : ℕ) = m := by
        simpa only [honeSmall, Fin.val_last] using congrArg Fin.val hidx
      omega

  have hβStep (j : Fin m) (hj : 1 ≤ j.val) :
      β ≠ restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    by_cases hj1 : j.val = 1
    · have hjEq : j = (⟨1, by omega⟩ : Fin m) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hj1
      rw [hjEq]
      exact hbeta
    · have hj2 : 2 ≤ j.val := by omega
      exact hβAvoid (sourceStep j) (hv1NotStep j hj2)

  let hostClosing : (cycleGraph ((m + 1) + 1)).edgeSet :=
    sourceClosing (m + 1) (by omega)
  have hClass (e : (cycleGraph ((m + 1) + 1)).edgeSet) :
      (e = sourceStep (0 : Fin (m + 1)) ∧ L e = α) ∨
      (e = sourceStep (1 : Fin (m + 1)) ∧ L e = β) ∨
      (∃ j : Fin m, 1 ≤ j.val ∧
        e = sourceStep (Fin.succ j) ∧
        L e = restrictedColor χ r (cyc.mapEdgeSet (sourceStep j))) ∨
      (e = hostClosing ∧ L e = restrictedColor χ r closing) := by
    rcases sourceEdge_cases (m := m + 1) (by omega) e with
      ⟨i, he⟩ | he
    · subst e
      by_cases hi0 : i = 0
      · subst i
        exact Or.inl ⟨rfl, hstep0⟩
      by_cases hi1 : i = 1
      · subst i
        exact Or.inr (Or.inl ⟨rfl, hstep1⟩)
      have hi : 2 ≤ i.val := by
        have hne0 : i.val ≠ 0 := by
          intro h
          apply hi0
          apply Fin.ext
          simpa only [Fin.val_zero] using h
        have hne1 : i.val ≠ 1 := by
          intro h
          apply hi1
          apply Fin.ext
          simpa only [honeSmall] using h
        omega
      obtain ⟨j, hjEq, hj, hcol⟩ := htail i hi
      have hij : i = Fin.succ j := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      subst i
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, rfl, hcol⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨he, by rw [he]; exact hclose⟩))

  have hβclosing : β ≠ restrictedColor χ r closing :=
    hβAvoid (sourceClosing m hm) hv1NotClosing

  -- Each of the four source-edge classes has a literal original-host color.
  -- The remaining palette proof uses only the eight unordered collisions.
  have hpalette : Function.Injective
      (EdgeLabeling.pullback χ f.toHom) := by
    change Function.Injective L
    intro e₁ e₂ heq
    rcases hClass e₁ with hA₁ | hB₁ | hT₁ | hC₁
    · obtain ⟨hs₁, hc₁⟩ := hA₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · exact hs₁.trans hA₂.1.symm
      · have hcolors : α = β :=
          hc₁.symm.trans (heq.trans hB₂.2)
        exact False.elim (hαβ hcolors)
      · obtain ⟨j, _, _, hc₂⟩ := hT₂
        have hcolors : α =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        exact False.elim (hαSelected (sourceStep j) hcolors)
      · have hcolors : α = restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        exact False.elim (hαclosing hcolors)
    · obtain ⟨hs₁, hc₁⟩ := hB₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α = β :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαβ hcolors)
      · exact hs₁.trans hB₂.1.symm
      · obtain ⟨j, hj, _, hc₂⟩ := hT₂
        have hcolors : β =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        exact False.elim (hβStep j hj hcolors)
      · have hcolors : β = restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        exact False.elim (hβclosing hcolors)
    · obtain ⟨i, hi, hs₁, hc₁⟩ := hT₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαSelected (sourceStep i) hcolors)
      · have hcolors : β =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) :=
          hB₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hβStep i hi hcolors)
      · obtain ⟨j, _, hs₂, hc₂⟩ := hT₂
        have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) =
              restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        have hij : i = j :=
          sourceStep_injective (hcycleColors hcolors)
        subst j
        exact hs₁.trans hs₂.symm
      · have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) =
              restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        have hsource : sourceStep i = sourceClosing m hm :=
          hcycleColors hcolors
        exact False.elim (sourceStep_ne_closing hm i hsource)
    · obtain ⟨hs₁, hc₁⟩ := hC₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α = restrictedColor χ r closing :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαclosing hcolors)
      · have hcolors : β = restrictedColor χ r closing :=
          hB₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hβclosing hcolors)
      · obtain ⟨j, _, _, hc₂⟩ := hT₂
        have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) =
              restrictedColor χ r closing :=
          hc₂.symm.trans (heq.symm.trans hc₁)
        have hsource : sourceStep j = sourceClosing m hm :=
          hcycleColors hcolors
        exact False.elim (sourceStep_ne_closing hm j hsource)
      · exact hs₁.trans hC₂.1.symm

  exact ⟨f, hpalette⟩

end ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion

namespace ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
export ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion (outsiderEdge)

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Repeating a selected outgoing edge color on the first spoke forces
that color to be NEW at the first cycle endpoint, for the same arbitrary
choice `r`. This supplies the NEW premise of the deleted-edge insertion. -/
theorem deleted_edge_color_new_at_first {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hfirstEq : χ (outsiderEdge cyc u hu 0) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m)))) :
    χ (outsiderEdge cyc u hu 0) ∈ newColors χ (cyc.toHom 0) := by
  let e := cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m))
  obtain ⟨v, hve, hnew⟩ :=
    arbitrary_selected_edge_has_new_endpoint χ r e
  have hinc := newColor_every_edge_incident χ v hnew
    (outsiderEdge cyc u hu 0) hfirstEq
  have hcases : v = u ∨ v = cyc.toHom 0 := by
    simpa only [outsiderEdge, Sym2.mem_iff] using hinc
  rcases hcases with hvu | hvzero
  · subst v
    change u ∈ Sym2.map cyc.toHom
      (sourceStep (⟨0, by omega⟩ : Fin m)).val at hve
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hve
    exact False.elim (hu ⟨i, hi⟩)
  · subst v
    simpa only [hfirstEq] using hnew

/-- Insert the outside vertex at position one: the order is
`(v₁,u,v₂,…,vₘ₊₁)`. -/
def deletedInsertionMap {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) : Fin ((m + 1) + 1) → Fin n :=
  Fin.insertNth (α := fun _ => Fin n)
    (1 : Fin ((m + 1) + 1)) u cyc.toHom

theorem deletedInsertionMap_zero {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    deletedInsertionMap cyc u 0 = cyc.toHom 0 := by
  have h : Fin.insertNth (α := fun _ => Fin n)
      (1 : Fin ((m + 1) + 1)) u cyc.toHom
      ((1 : Fin ((m + 1) + 1)).succAbove (0 : Fin (m + 1))) =
        cyc.toHom 0 :=
    Fin.insertNth_apply_succAbove (α := fun _ => Fin n)
      (1 : Fin ((m + 1) + 1)) u cyc.toHom 0
  simpa only [deletedInsertionMap, Fin.one_succAbove_zero] using h

theorem deletedInsertionMap_one {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    deletedInsertionMap cyc u 1 = u := by
  simp only [deletedInsertionMap, Fin.insertNth_apply_same]

theorem deletedInsertionMap_succ_of_pos {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (j : Fin (m + 1)) (hj : 1 ≤ j.val) :
    deletedInsertionMap cyc u (Fin.succ j) = cyc.toHom j := by
  have hone : ((1 : Fin ((m + 1) + 1)) : ℕ) = 1 := by
    have hlt : 1 < (m + 1) + 1 := by omega
    rw [Fin.val_one' ((m + 1) + 1), Nat.mod_eq_of_lt hlt]
  have hlt : (1 : Fin ((m + 1) + 1)) < Fin.succ j := by
    simp only [Fin.lt_def, Fin.val_succ]
    rw [hone]
    omega
  unfold deletedInsertionMap
  rw [← Fin.succAbove_of_lt_succ _ _ hlt]
  exact Fin.insertNth_apply_succAbove (α := fun _ => Fin n)
    (1 : Fin ((m + 1) + 1)) u cyc.toHom j

/-- Every host step after the two inserted spokes is exactly a selected
source-cycle step, with the latter index one smaller. -/
theorem deletedInsertionMap_step_ge_two {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (i : Fin (m + 1)) (hi : 2 ≤ i.val) :
    ∃ j : Fin m, j.val + 1 = i.val ∧ 1 ≤ j.val ∧
      Sym2.map (deletedInsertionMap cyc u) (sourceStep i).val =
        Sym2.map cyc.toHom (sourceStep j).val := by
  let j : Fin m := ⟨i.val - 1, by omega⟩
  have hjEq : j.val + 1 = i.val := by dsimp [j]; omega
  have hj : 1 ≤ j.val := by dsimp [j]; omega
  refine ⟨j, hjEq, hj, ?_⟩
  have hloIndex : Fin.castSucc i = Fin.succ (Fin.castSucc j) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ]
    dsimp [j]
    omega
  have hhiIndex : Fin.succ i = Fin.succ (Fin.succ j) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp [j]
    omega
  have hlo : deletedInsertionMap cyc u (Fin.castSucc i) =
      cyc.toHom (Fin.castSucc j) := by
    rw [hloIndex]
    exact deletedInsertionMap_succ_of_pos cyc u (Fin.castSucc j)
      (by simpa only [Fin.val_castSucc] using hj)
  have hhi : deletedInsertionMap cyc u (Fin.succ i) =
      cyc.toHom (Fin.succ j) := by
    rw [hhiIndex]
    exact deletedInsertionMap_succ_of_pos cyc u (Fin.succ j)
      (by simp only [Fin.val_succ]; omega)
  simp only [sourceStep, Sym2.map_mk]
  rw [hlo, hhi]

/-- The closing host edge is precisely the selected source-cycle closing
edge. -/
theorem deletedInsertionMap_closing {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    Sym2.map (deletedInsertionMap cyc u)
      (sourceClosing (m + 1) (by omega)).val =
    Sym2.map cyc.toHom (sourceClosing m hm).val := by
  have hlastIndex : Fin.last (m + 1) = Fin.succ (Fin.last m) := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_succ]
  have hlast : deletedInsertionMap cyc u (Fin.last (m + 1)) =
      cyc.toHom (Fin.last m) := by
    rw [hlastIndex]
    exact deletedInsertionMap_succ_of_pos cyc u (Fin.last m)
      (by simp only [Fin.val_last]; omega)
  simp only [sourceClosing, Sym2.map_mk]
  rw [deletedInsertionMap_zero, hlast]

theorem deletedInsertionMap_first_spoke {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (deletedInsertionMap cyc u)
      (sourceStep (0 : Fin (m + 1))).val =
      (outsiderEdge cyc u hu 0).val := by
  change s(deletedInsertionMap cyc u 0,
      deletedInsertionMap cyc u 1) = s(u, cyc.toHom 0)
  rw [deletedInsertionMap_zero, deletedInsertionMap_one]
  exact Sym2.eq_swap

theorem deletedInsertionMap_second_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (deletedInsertionMap cyc u)
      (sourceStep (1 : Fin (m + 1))).val =
      (outsiderEdge cyc u hu 1).val := by
  simp only [sourceStep, outsiderEdge, Sym2.map_mk]
  have honeSmall : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    have hlt : 1 < m + 1 := by omega
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt hlt]
  have honeLarge : ((1 : Fin ((m + 1) + 1)) : ℕ) = 1 := by
    have hlt : 1 < (m + 1) + 1 := by omega
    rw [Fin.val_one' ((m + 1) + 1), Nat.mod_eq_of_lt hlt]
  have hcast : Fin.castSucc (1 : Fin (m + 1)) =
      (1 : Fin ((m + 1) + 1)) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, honeSmall, honeLarge]
  rw [hcast]
  rw [deletedInsertionMap_one]
  have hpos : 1 ≤ (1 : Fin (m + 1)).val := by
    rw [honeSmall]
  rw [deletedInsertionMap_succ_of_pos cyc u 1 hpos]

theorem deletedInsertionMap_injective {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Function.Injective (deletedInsertionMap cyc u) := by
  intro a b hab
  let t : Fin ((m + 1) + 1) := 1
  by_cases ha : a = t
  · subst a
    by_cases hb : b = t
    · exact hb.symm
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := t) hb
      subst b
      have hbad : u = cyc.toHom j := by
        simpa only [deletedInsertionMap, t, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] using hab
      exact False.elim (hu ⟨j, hbad.symm⟩)
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (y := t) ha
    subst a
    by_cases hb : b = t
    · subst b
      have hbad : cyc.toHom i = u := by
        simpa only [deletedInsertionMap, t, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] using hab
      exact False.elim (hu ⟨i, hbad⟩)
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := t) hb
      subst b
      have hij : cyc.toHom i = cyc.toHom j := by
        simpa only [deletedInsertionMap, t,
          Fin.insertNth_apply_succAbove] using hab
      rw [cyc.injective hij]

/-- Generalized positive insertion when the first spoke repeats exactly the
selected edge deleted by the insertion. Its selected NEW owner is derived
at the first endpoint; the spoke itself is not assumed selected. -/
theorem positive_deleted_edge_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hfirstEq : χ (outsiderEdge cyc u hu 0) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m))))
    (hbeta : χ (outsiderEdge cyc u hu 1) ≠
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  have hnewFirst : χ (outsiderEdge cyc u hu 0) ∈
      newColors χ (cyc.toHom 0) :=
    deleted_edge_color_new_at_first hm χ r cyc u hu hfirstEq
  let p := deletedInsertionMap cyc u
  have hp : Function.Injective p :=
    deletedInsertionMap_injective cyc u hu
  let φ : (cycleGraph ((m + 1) + 1)) →g
      (⊤ : SimpleGraph (Fin n)) :=
    ⟨p, by
      intro a b hab
      exact (top_adj _ _).mpr
        (hp.ne ((cycleGraph ((m + 1) + 1)).ne_of_adj hab))⟩
  let f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)) := ⟨φ, hp⟩

  have honeSmall : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    have hlt : 1 < m + 1 := by omega
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt hlt]

  let closing : (selectedGraph χ r).edgeSet :=
    cyc.mapEdgeSet (sourceClosing m hm)
  have hαβ : χ (outsiderEdge cyc u hu 0) ≠
      χ (outsiderEdge cyc u hu 1) := by
    intro heq
    have hinc := newColor_every_edge_incident χ
      (cyc.toHom 0) hnewFirst (outsiderEdge cyc u hu 1) heq.symm
    have hcases : cyc.toHom 0 = u ∨
        cyc.toHom 0 = cyc.toHom 1 := by
      simpa only [outsiderEdge, Sym2.mem_iff] using hinc
    rcases hcases with h | h
    · exact hu ⟨0, h⟩
    · have h01 : (0 : Fin (m + 1)) = 1 := cyc.injective h
      have hval : (0 : ℕ) = 1 := by
        simpa only [Fin.val_zero, honeSmall] using congrArg Fin.val h01
      exact Nat.zero_ne_one hval
  have huSelected (e : (cycleGraph (m + 1)).edgeSet) :
      u ∉ (cyc.mapEdgeSet e).val := by
    intro he
    change u ∈ Sym2.map cyc.toHom e.val at he
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp he
    exact hu ⟨i, hi⟩
  have hαRetained (e : (cycleGraph (m + 1)).edgeSet)
      (he : sourceStep (⟨0, by omega⟩ : Fin m) ≠ e) :
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet e) := by
    intro heq
    have hcolors := hfirstEq.symm.trans heq
    have hmaps := restrictedColor_injective χ r hcolors
    exact he (cyc.mapEdgeSet.injective hmaps)
  have hαStep (j : Fin m) (hj : 1 ≤ j.val) :
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    apply hαRetained (sourceStep j)
    intro heq
    have hidx := sourceStep_injective heq
    have hval := congrArg Fin.val hidx
    change 0 = j.val at hval
    omega
  have hαclosing : χ (outsiderEdge cyc u hu 0) ≠
      restrictedColor χ r closing :=
    hαRetained (sourceClosing m hm)
      (sourceStep_ne_closing hm (⟨0, by omega⟩ : Fin m))
  have hβAvoid (e : (cycleGraph (m + 1)).edgeSet)
      (hv : cyc.toHom 1 ∉ (cyc.mapEdgeSet e).val) :
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet e) := by
    intro heq
    have hdisj : ∀ v : Fin n, v ∈ (cyc.mapEdgeSet e).val →
        v ∉ (outsiderEdge cyc u hu 1).val := by
      intro v hve hvspoke
      have hcases : v = u ∨ v = cyc.toHom 1 := by
        simpa only [outsiderEdge, Sym2.mem_iff] using hvspoke
      rcases hcases with h | h
      · subst v
        exact huSelected e hve
      · subst v
        exact hv hve
    exact (arbitrary_selected_edge_ne_disjoint_host_edge χ r
      (cyc.mapEdgeSet e) (outsiderEdge cyc u hu 1) hdisj) heq.symm
  have hcycleColors : Function.Injective
      (fun e : (cycleGraph (m + 1)).edgeSet =>
        restrictedColor χ r (cyc.mapEdgeSet e)) :=
    (restrictedColor_injective χ r).comp cyc.mapEdgeSet.injective

  let L := EdgeLabeling.pullback χ f.toHom
  let α : C := χ (outsiderEdge cyc u hu 0)
  let β : C := χ (outsiderEdge cyc u hu 1)
  have hcolor_of_host
      (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : HostEdge n)
      (hval : Sym2.map p e.val = d.val) : L e = χ d := by
    have hedges : f.toHom.mapEdgeSet e = d := by
      apply Subtype.ext
      change Sym2.map p e.val = d.val
      exact hval
    simpa only [L, EdgeLabeling.pullback_apply] using congrArg χ hedges
  have hcolor_of_selected
      (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map p e.val = Sym2.map cyc.toHom d.val) :
      L e = restrictedColor χ r (cyc.mapEdgeSet d) := by
    let selectedHostEdge : HostEdge n :=
      ⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
    have hedges : f.toHom.mapEdgeSet e = selectedHostEdge := by
      apply Subtype.ext
      change Sym2.map p e.val = Sym2.map cyc.toHom d.val
      exact hval
    simpa only [L, EdgeLabeling.pullback_apply, restrictedColor,
      selectedHostEdge] using congrArg χ hedges
  have hstep0 : L (sourceStep (0 : Fin (m + 1))) =
      χ (outsiderEdge cyc u hu 0) :=
    hcolor_of_host _ _ (deletedInsertionMap_first_spoke cyc u hu)
  have hstep1 : L (sourceStep (1 : Fin (m + 1))) =
      χ (outsiderEdge cyc u hu 1) :=
    hcolor_of_host _ _ (deletedInsertionMap_second_spoke hm cyc u hu)
  have htail (i : Fin (m + 1)) (hi : 2 ≤ i.val) :
      ∃ j : Fin m, j.val + 1 = i.val ∧ 1 ≤ j.val ∧
        L (sourceStep i) =
          restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    obtain ⟨j, hjEq, hj, hval⟩ :=
      deletedInsertionMap_step_ge_two cyc u i hi
    exact ⟨j, hjEq, hj, hcolor_of_selected _ _ hval⟩
  have hclose : L (sourceClosing (m + 1) (by omega)) =
      restrictedColor χ r closing :=
    hcolor_of_selected _ _ (deletedInsertionMap_closing hm cyc u)

  have hv1NotStep (j : Fin m) (hj : 2 ≤ j.val) :
      cyc.toHom 1 ∉ (cyc.mapEdgeSet (sourceStep j)).val := by
    intro hv
    change cyc.toHom 1 ∈
      Sym2.map cyc.toHom (sourceStep j).val at hv
    obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
    have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
    subst k
    change (1 : Fin (m + 1)) ∈
      s(Fin.castSucc j, Fin.succ j) at hk
    rcases Sym2.mem_iff.mp hk with h | h
    · have hidx : (1 : Fin (m + 1)) = Fin.castSucc j := h
      have hval : (1 : ℕ) = j.val := by
        simpa only [honeSmall, Fin.val_castSucc] using congrArg Fin.val hidx
      omega
    · have hidx : (1 : Fin (m + 1)) = Fin.succ j := h
      have hval : (1 : ℕ) = j.val + 1 := by
        simpa only [honeSmall, Fin.val_succ] using congrArg Fin.val hidx
      omega
  have hv1NotClosing : cyc.toHom 1 ∉ closing.val := by
    intro hv
    change cyc.toHom 1 ∈
      Sym2.map cyc.toHom (sourceClosing m hm).val at hv
    obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
    have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
    subst k
    change (1 : Fin (m + 1)) ∈
      s((0 : Fin (m + 1)), Fin.last m) at hk
    rcases Sym2.mem_iff.mp hk with h | h
    · have hidx : (1 : Fin (m + 1)) = 0 := h
      have hval : (1 : ℕ) = 0 := by
        simpa only [honeSmall, Fin.val_zero] using congrArg Fin.val hidx
      exact Nat.one_ne_zero hval
    · have hidx : (1 : Fin (m + 1)) = Fin.last m := h
      have hval : (1 : ℕ) = m := by
        simpa only [honeSmall, Fin.val_last] using congrArg Fin.val hidx
      omega

  have hβStep (j : Fin m) (hj : 1 ≤ j.val) :
      β ≠ restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    by_cases hj1 : j.val = 1
    · have hjEq : j = (⟨1, by omega⟩ : Fin m) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hj1
      rw [hjEq]
      exact hbeta
    · have hj2 : 2 ≤ j.val := by omega
      exact hβAvoid (sourceStep j) (hv1NotStep j hj2)

  let hostClosing : (cycleGraph ((m + 1) + 1)).edgeSet :=
    sourceClosing (m + 1) (by omega)
  have hClass (e : (cycleGraph ((m + 1) + 1)).edgeSet) :
      (e = sourceStep (0 : Fin (m + 1)) ∧ L e = α) ∨
      (e = sourceStep (1 : Fin (m + 1)) ∧ L e = β) ∨
      (∃ j : Fin m, 1 ≤ j.val ∧
        e = sourceStep (Fin.succ j) ∧
        L e = restrictedColor χ r (cyc.mapEdgeSet (sourceStep j))) ∨
      (e = hostClosing ∧ L e = restrictedColor χ r closing) := by
    rcases sourceEdge_cases (m := m + 1) (by omega) e with
      ⟨i, he⟩ | he
    · subst e
      by_cases hi0 : i = 0
      · subst i
        exact Or.inl ⟨rfl, hstep0⟩
      by_cases hi1 : i = 1
      · subst i
        exact Or.inr (Or.inl ⟨rfl, hstep1⟩)
      have hi : 2 ≤ i.val := by
        have hne0 : i.val ≠ 0 := by
          intro h
          apply hi0
          apply Fin.ext
          simpa only [Fin.val_zero] using h
        have hne1 : i.val ≠ 1 := by
          intro h
          apply hi1
          apply Fin.ext
          simpa only [honeSmall] using h
        omega
      obtain ⟨j, hjEq, hj, hcol⟩ := htail i hi
      have hij : i = Fin.succ j := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      subst i
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, rfl, hcol⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨he, by rw [he]; exact hclose⟩))

  have hβclosing : β ≠ restrictedColor χ r closing :=
    hβAvoid (sourceClosing m hm) hv1NotClosing

  -- Each of the four source-edge classes has a literal original-host color.
  -- The remaining palette proof uses only the eight unordered collisions.
  have hpalette : Function.Injective
      (EdgeLabeling.pullback χ f.toHom) := by
    change Function.Injective L
    intro e₁ e₂ heq
    rcases hClass e₁ with hA₁ | hB₁ | hT₁ | hC₁
    · obtain ⟨hs₁, hc₁⟩ := hA₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · exact hs₁.trans hA₂.1.symm
      · have hcolors : α = β :=
          hc₁.symm.trans (heq.trans hB₂.2)
        exact False.elim (hαβ hcolors)
      · obtain ⟨j, hj, _, hc₂⟩ := hT₂
        have hcolors : α =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        exact False.elim (hαStep j hj hcolors)
      · have hcolors : α = restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        exact False.elim (hαclosing hcolors)
    · obtain ⟨hs₁, hc₁⟩ := hB₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α = β :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαβ hcolors)
      · exact hs₁.trans hB₂.1.symm
      · obtain ⟨j, hj, _, hc₂⟩ := hT₂
        have hcolors : β =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        exact False.elim (hβStep j hj hcolors)
      · have hcolors : β = restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        exact False.elim (hβclosing hcolors)
    · obtain ⟨i, hi, hs₁, hc₁⟩ := hT₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαStep i hi hcolors)
      · have hcolors : β =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) :=
          hB₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hβStep i hi hcolors)
      · obtain ⟨j, _, hs₂, hc₂⟩ := hT₂
        have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) =
              restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        have hij : i = j :=
          sourceStep_injective (hcycleColors hcolors)
        subst j
        exact hs₁.trans hs₂.symm
      · have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) =
              restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        have hsource : sourceStep i = sourceClosing m hm :=
          hcycleColors hcolors
        exact False.elim (sourceStep_ne_closing hm i hsource)
    · obtain ⟨hs₁, hc₁⟩ := hC₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α = restrictedColor χ r closing :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαclosing hcolors)
      · have hcolors : β = restrictedColor χ r closing :=
          hB₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hβclosing hcolors)
      · obtain ⟨j, _, _, hc₂⟩ := hT₂
        have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) =
              restrictedColor χ r closing :=
          hc₂.symm.trans (heq.symm.trans hc₁)
        have hsource : sourceStep j = sourceClosing m hm :=
          hcycleColors hcolors
        exact False.elim (sourceStep_ne_closing hm j hsource)
      · exact hs₁.trans hC₂.1.symm

  exact ⟨f, hpalette⟩

/-- Translate the source cycle by an arbitrary cyclic position. The exact
Mathlib `finCycle` permutation is used, and ordinary graph adjacency is
preserved through subtraction in the cyclic group. -/
noncomputable def shiftedCycle {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (a : Fin (m + 1)) :
    (cycleGraph (m + 1)).Copy (selectedGraph χ r) :=
  cyc.comp
    ⟨⟨finCycle a, by
        intro i j hij
        rw [cycleGraph_adj'] at hij ⊢
        simpa only [finCycle_apply, add_sub_add_right_eq_sub] using hij⟩,
      (finCycle a).injective⟩

theorem shiftedCycle_apply {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (a i : Fin (m + 1)) :
    (shiftedCycle cyc a).toHom i = cyc.toHom (i + a) := rfl

theorem shiftedCycle_zero {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) :
    shiftedCycle cyc 0 = cyc := by
  apply DFunLike.ext
  intro i
  change cyc.toHom (i + 0) = cyc.toHom i
  rw [add_zero]

/-- Translating a selected cycle does not change its vertex range. Only
the forward direction is needed for the outside-vertex condition. -/
theorem shifted_outside {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (a : Fin (m + 1)) :
    u ∉ Set.range (shiftedCycle cyc a).toHom := by
  rintro ⟨i, hi⟩
  exact hu ⟨i + a, hi⟩

theorem shifted_outsiderEdge {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (a i : Fin (m + 1)) :
    outsiderEdge (shiftedCycle cyc a) u (shifted_outside cyc u hu a) i =
      outsiderEdge cyc u hu (i + a) := by
  apply Subtype.ext
  rfl

/-- At a cyclic position `a`, the second retained source step is the
first source step of the cycle shifted once further. This statement also
handles the last source position, where cyclic addition wraps to zero. -/
theorem shifted_step_one_eq_next_step_zero {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (a : Fin (m + 1)) :
    (shiftedCycle cyc a).mapEdgeSet
        (sourceStep (⟨1, by omega⟩ : Fin m)) =
      (shiftedCycle cyc (a + 1)).mapEdgeSet
        (sourceStep (⟨0, by omega⟩ : Fin m)) := by
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hcast0 : Fin.castSucc (⟨0, by omega⟩ : Fin m) =
      (0 : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hsucc0 : Fin.succ (⟨0, by omega⟩ : Fin m) =
      (1 : Fin (m + 1)) := by
    apply Fin.ext
    simpa only [Fin.val_succ, Fin.val_mk] using hone.symm
  have hcast1 : Fin.castSucc (⟨1, by omega⟩ : Fin m) =
      (1 : Fin (m + 1)) := by
    apply Fin.ext
    simpa only [Fin.val_castSucc, Fin.val_mk] using hone.symm
  have hsucc1 : Fin.succ (⟨1, by omega⟩ : Fin m) =
      (1 : Fin (m + 1)) + 1 := by
    apply Fin.ext
    rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by omega)]
    rfl
  apply Subtype.ext
  change s(cyc.toHom (Fin.castSucc (⟨1, by omega⟩ : Fin m) + a),
      cyc.toHom (Fin.succ (⟨1, by omega⟩ : Fin m) + a)) =
    s(cyc.toHom (Fin.castSucc (⟨0, by omega⟩ : Fin m) + (a + 1)),
      cyc.toHom (Fin.succ (⟨0, by omega⟩ : Fin m) + (a + 1)))
  rw [hcast1, hsucc1, hcast0, hsucc0]
  simp only [zero_add, add_comm, add_left_comm]

/-- The literal selected outgoing edge color at a cyclic source position.
For the final position this is the selected closing edge color. -/
noncomputable def cycleOutgoingColor {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (a : Fin (m + 1)) : C :=
  restrictedColor χ r ((shiftedCycle cyc a).mapEdgeSet
    (sourceStep (⟨0, by omega⟩ : Fin m)))

theorem cycleOutgoingColor_zero {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) :
    cycleOutgoingColor hm χ r cyc 0 = restrictedColor χ r
      (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m))) := by
  unfold cycleOutgoingColor
  rw [shiftedCycle_zero]

/-- If no literal rainbow host cycle exists, a spoke repeating the selected
outgoing color forces the next spoke to repeat the next outgoing color.
The first spoke is never assumed to be a selected edge. -/
theorem no_rainbow_forces_next_repeat {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ)
    (a : Fin (m + 1))
    (hfirst : χ (outsiderEdge cyc u hu a) =
      cycleOutgoingColor hm χ r cyc a) :
    χ (outsiderEdge cyc u hu (a + 1)) =
      cycleOutgoingColor hm χ r cyc (a + 1) := by
  by_contra hnext
  have hshift := shifted_outside cyc u hu a
  have hfirstEq :
      χ (outsiderEdge (shiftedCycle cyc a) u hshift 0) =
        restrictedColor χ r ((shiftedCycle cyc a).mapEdgeSet
          (sourceStep (⟨0, by omega⟩ : Fin m))) := by
    rw [shifted_outsiderEdge cyc u hu a 0, zero_add]
    exact hfirst
  have hspoke : outsiderEdge (shiftedCycle cyc a) u hshift 1 =
      outsiderEdge cyc u hu (a + 1) := by
    calc
      outsiderEdge (shiftedCycle cyc a) u hshift 1 =
          outsiderEdge cyc u hu (1 + a) :=
        shifted_outsiderEdge cyc u hu a 1
      _ = outsiderEdge cyc u hu (a + 1) :=
        congrArg (outsiderEdge cyc u hu) (add_comm 1 a)
  have hbeta : χ (outsiderEdge (shiftedCycle cyc a) u hshift 1) ≠
      restrictedColor χ r ((shiftedCycle cyc a).mapEdgeSet
        (sourceStep (⟨1, by omega⟩ : Fin m))) := by
    rw [hspoke, shifted_step_one_eq_next_step_zero hm]
    exact hnext
  obtain ⟨f, hf⟩ := positive_deleted_edge_insertion_copy hm χ r
    (shiftedCycle cyc a) u hshift hfirstEq hbeta
  exact hnone f hf

/-- The selected attachment color differs from every selected source-cycle
edge, including the incident first and closing edges. This uses selected
color injection for the same arbitrary `NewChoice`, not only NEW incidence. -/
theorem selected_attachment_color_ne_cycle_color {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (e : (cycleGraph (m + 1)).edgeSet) :
    χ (outsiderEdge cyc u hu 0) ≠
      restrictedColor χ r (cyc.mapEdgeSet e) := by
  let a : (selectedGraph χ r).edgeSet :=
    ⟨s(u, cyc.toHom 0), hattach⟩
  have haColor : χ (outsiderEdge cyc u hu 0) =
      restrictedColor χ r a := by
    simp [outsiderEdge, restrictedColor, a]
  intro heq
  have hae : a = cyc.mapEdgeSet e :=
    restrictedColor_injective χ r (haColor.symm.trans heq)
  have hua : u ∈ a.val := by
    simp [a, Sym2.mem_iff]
  have hue : u ∈ (cyc.mapEdgeSet e).val := hae ▸ hua
  change u ∈ Sym2.map cyc.toHom e.val at hue
  obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hue
  exact hu ⟨i, hi⟩

/-- Choi Claim 1 Case A, the second branch after `beta2=c2`. No inequality
on any later spoke is assumed: each non-rainbow insertion forces the next
repeat, and the final insertion conflicts with the selected attachment.
The inherited NEW-at-first hypothesis is retained although this branch
already derives all later NEW ownership from the repeated selected colors. -/
theorem positive_second_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (_hnewFirst : χ (outsiderEdge cyc u hu 0) ∈
      newColors χ (cyc.toHom 0))
    (hbetaEq : χ (outsiderEdge cyc u hu 1) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  by_contra hnoneExists
  have hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ := by
    intro f hf
    exact hnoneExists ⟨f, hf⟩
  have hbetaOne : χ (outsiderEdge cyc u hu 1) =
      cycleOutgoingColor hm χ r cyc 1 := by
    have hstep := shifted_step_one_eq_next_step_zero hm cyc
      (0 : Fin (m + 1))
    rw [shiftedCycle_zero, zero_add] at hstep
    simpa only [cycleOutgoingColor, ← hstep] using hbetaEq
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hall : ∀ j : ℕ, ∀ hj : j < m,
      χ (outsiderEdge cyc u hu (⟨j + 1, by omega⟩ : Fin (m + 1))) =
        cycleOutgoingColor hm χ r cyc (⟨j + 1, by omega⟩ : Fin (m + 1)) := by
    intro j
    induction j with
    | zero =>
        intro hj
        have heq : (⟨0 + 1, by omega⟩ : Fin (m + 1)) = 1 := by
          apply Fin.ext
          exact hone.symm
        simpa only [heq] using hbetaOne
    | succ j ih =>
        intro hj
        have hjprev : j < m := by omega
        let a : Fin (m + 1) := ⟨j + 1, by omega⟩
        have hthis : χ (outsiderEdge cyc u hu a) =
            cycleOutgoingColor hm χ r cyc a := ih hjprev
        have hnext := no_rainbow_forces_next_repeat hm χ r cyc u hu
          hnone a hthis
        have ha : a + 1 = (⟨j + 1 + 1, by omega⟩ : Fin (m + 1)) := by
          apply Fin.ext
          rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by dsimp [a]; omega)]
        simpa only [ha, Nat.succ_eq_add_one] using hnext
  have hlast := hall (m - 1) (by omega)
  have hlastIndex : (⟨m - 1 + 1, by omega⟩ : Fin (m + 1)) =
      Fin.last m := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  rw [hlastIndex] at hlast
  have hzero := no_rainbow_forces_next_repeat hm χ r cyc u hu
    hnone (Fin.last m) hlast
  have hwrap : (Fin.last m : Fin (m + 1)) + 1 = 0 := by
    simpa only [finRotate_apply] using (finRotate_last (n := m))
  rw [hwrap, cycleOutgoingColor_zero] at hzero
  exact selected_attachment_color_ne_cycle_color χ r cyc u hu hattach
    (sourceStep (⟨0, by omega⟩ : Fin m)) hzero

/-- Complete local Case A of Choi Claim 1. The first selected attachment
color is NEW at the selected cycle endpoint. The imported first insertion
handles the unequal branch, and the second insertion theorem above handles
the equal branch with no further spoke guard. -/
theorem positive_first_endpoint_attachment_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (hnewFirst : χ (outsiderEdge cyc u hu 0) ∈
      newColors χ (cyc.toHom 0)) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  by_cases hbeta : χ (outsiderEdge cyc u hu 1) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))
  · exact positive_second_insertion_copy hm χ r cyc u hu
      hattach hnewFirst hbeta
  · exact positive_first_insertion_copy hm χ r cyc u hu
      hattach hnewFirst hbeta

end ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion

namespace ErdosProblems.AntiRamseyCycleClaimOneOutsideInsertion

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Insert `u` between the first two cycle vertices. The two literal host
spokes are distinct in color and each avoids every retained selected color.
This palette interface reuses the private map; it assumes no NEW orientation.
-/
theorem positive_two_spoke_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hspokes : χ (outsiderEdge cyc u hu 0) ≠
      χ (outsiderEdge cyc u hu 1))
    (hfirstAvoid : ∀ d : (cycleGraph (m + 1)).edgeSet,
      d ≠ sourceStep (⟨0, by omega⟩ : Fin m) →
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet d))
    (hsecondAvoid : ∀ d : (cycleGraph (m + 1)).edgeSet,
      d ≠ sourceStep (⟨0, by omega⟩ : Fin m) →
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet d)) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  let p := deletedInsertionMap cyc u
  have hp : Function.Injective p := deletedInsertionMap_injective cyc u hu
  let φ : (cycleGraph ((m + 1) + 1)) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨p, by
      intro a b hab
      exact (top_adj _ _).mpr
        (hp.ne ((cycleGraph ((m + 1) + 1)).ne_of_adj hab))⟩
  let f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)) := ⟨φ, hp⟩
  let L := EdgeLabeling.pullback χ f.toHom
  let α : C := χ (outsiderEdge cyc u hu 0)
  let β : C := χ (outsiderEdge cyc u hu 1)
  let lifted : (cycleGraph (m + 1)).edgeSet → HostEdge n := fun d =>
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  have hmapHost (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : HostEdge n) (hval : Sym2.map p e.val = d.val) :
      f.mapEdgeSet e = d := by
    apply Subtype.ext
    exact hval
  have hmapSelected (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map p e.val = Sym2.map cyc.toHom d.val) :
      f.mapEdgeSet e = lifted d := by
    apply Subtype.ext
    exact hval
  have hcolorHost (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : HostEdge n) (hmap : f.mapEdgeSet e = d) : L e = χ d := by
    simpa only [L, EdgeLabeling.pullback_apply, SimpleGraph.Copy.mapEdgeSet, Function.Embedding.coeFn_mk] using congrArg χ hmap
  have hcolorSelected (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hmap : f.mapEdgeSet e = lifted d) :
      L e = restrictedColor χ r (cyc.mapEdgeSet d) := by
    simpa only [L, EdgeLabeling.pullback_apply, lifted, restrictedColor, SimpleGraph.Copy.mapEdgeSet, Function.Embedding.coeFn_mk]
      using congrArg χ hmap
  have hstep0 : L (sourceStep (0 : Fin (m + 1))) = α :=
    hcolorHost _ _ (hmapHost _ _ (deletedInsertionMap_first_spoke cyc u hu))
  have hstep1 : L (sourceStep (1 : Fin (m + 1))) = β :=
    hcolorHost _ _ (hmapHost _ _ (deletedInsertionMap_second_spoke hm cyc u hu))
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hClass (e : (cycleGraph ((m + 1) + 1)).edgeSet) :
      (e = sourceStep (0 : Fin (m + 1)) ∧ L e = α) ∨
      (e = sourceStep (1 : Fin (m + 1)) ∧ L e = β) ∨
      ∃ d : (cycleGraph (m + 1)).edgeSet,
        d ≠ sourceStep (⟨0, by omega⟩ : Fin m) ∧
        L e = restrictedColor χ r (cyc.mapEdgeSet d) ∧
        f.mapEdgeSet e = lifted d := by
    rcases sourceEdge_cases (m := m + 1) (by omega) e with ⟨i, he⟩ | he
    · subst e
      by_cases hi0 : i = 0
      · subst i
        exact Or.inl ⟨rfl, hstep0⟩
      by_cases hi1 : i = 1
      · subst i
        exact Or.inr (Or.inl ⟨rfl, hstep1⟩)
      have hi : 2 ≤ i.val := by
        have hne0 : i.val ≠ 0 := by
          intro h
          exact hi0 (Fin.ext h)
        have hne1 : i.val ≠ 1 := by
          intro h
          apply hi1
          apply Fin.ext
          simpa only [hone] using h
        omega
      obtain ⟨j, _, hj, hval⟩ := deletedInsertionMap_step_ge_two cyc u i hi
      have hd : sourceStep j ≠ sourceStep (⟨0, by omega⟩ : Fin m) := by
        intro heq
        have hidx := sourceStep_injective heq
        have hvalj := congrArg Fin.val hidx
        change j.val = 0 at hvalj
        omega
      have hmap := hmapSelected (sourceStep i) (sourceStep j) hval
      exact Or.inr (Or.inr ⟨sourceStep j, hd,
        hcolorSelected _ _ hmap, hmap⟩)
    · subst e
      have hd : sourceClosing m hm ≠
          sourceStep (⟨0, by omega⟩ : Fin m) :=
        (sourceStep_ne_closing hm (⟨0, by omega⟩ : Fin m)).symm
      have hmap := hmapSelected _ _ (deletedInsertionMap_closing hm cyc u)
      exact Or.inr (Or.inr ⟨sourceClosing m hm, hd,
        hcolorSelected _ _ hmap, hmap⟩)
  have hpalette : Function.Injective (EdgeLabeling.pullback χ f.toHom) := by
    change Function.Injective L
    intro e₁ e₂ heq
    rcases hClass e₁ with hA₁ | hB₁ | hR₁
    · rcases hClass e₂ with hA₂ | hB₂ | hR₂
      · exact hA₁.1.trans hA₂.1.symm
      · exact False.elim (hspokes (hA₁.2.symm.trans (heq.trans hB₂.2)))
      · obtain ⟨d, hd, hc, _⟩ := hR₂
        exact False.elim (hfirstAvoid d hd (hA₁.2.symm.trans (heq.trans hc)))
    · rcases hClass e₂ with hA₂ | hB₂ | hR₂
      · exact False.elim (hspokes (hA₂.2.symm.trans (heq.symm.trans hB₁.2)))
      · exact hB₁.1.trans hB₂.1.symm
      · obtain ⟨d, hd, hc, _⟩ := hR₂
        exact False.elim (hsecondAvoid d hd (hB₁.2.symm.trans (heq.trans hc)))
    · obtain ⟨d₁, hd₁, hc₁, hm₁⟩ := hR₁
      rcases hClass e₂ with hA₂ | hB₂ | hR₂
      · exact False.elim (hfirstAvoid d₁ hd₁ (hA₂.2.symm.trans (heq.symm.trans hc₁)))
      · exact False.elim (hsecondAvoid d₁ hd₁ (hB₂.2.symm.trans (heq.symm.trans hc₁)))
      · obtain ⟨d₂, _, hc₂, hm₂⟩ := hR₂
        have hcolors := hc₁.symm.trans (heq.trans hc₂)
        have hd : d₁ = d₂ :=
          cyc.mapEdgeSet.injective (restrictedColor_injective χ r hcolors)
        apply f.mapEdgeSet.injective
        exact hm₁.trans ((congrArg lifted hd).trans hm₂.symm)
  exact ⟨f, hpalette⟩

/-- Initial Case B mismatch insertion. The first spoke is NEW at the outside
vertex, differs from the second spoke, and the second spoke differs from the
only retained selected color it could repeat. No selected attachment is needed.
-/
theorem positive_outside_new_initial_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnewOutside : χ (outsiderEdge cyc u hu 0) ∈ newColors χ u)
    (hspokes : χ (outsiderEdge cyc u hu 0) ≠
      χ (outsiderEdge cyc u hu 1))
    (hbeta : χ (outsiderEdge cyc u hu 1) ≠
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  have huSelected (d : (cycleGraph (m + 1)).edgeSet) :
      u ∉ (cyc.mapEdgeSet d).val := by
    intro he
    change u ∈ Sym2.map cyc.toHom d.val at he
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp he
    exact hu ⟨i, hi⟩
  have hfirstAvoid (d : (cycleGraph (m + 1)).edgeSet)
      (_hd : d ≠ sourceStep (⟨0, by omega⟩ : Fin m)) :
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    intro heq
    let e : HostEdge n :=
      ⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
    have hcolor : χ e = χ (outsiderEdge cyc u hu 0) := heq.symm
    exact huSelected d (newColor_every_edge_incident χ u hnewOutside e hcolor)
  have hbetaAvoid (d : (cycleGraph (m + 1)).edgeSet)
      (hv : cyc.toHom 1 ∉ (cyc.mapEdgeSet d).val) :
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    intro heq
    have hdisj : ∀ v : Fin n, v ∈ (cyc.mapEdgeSet d).val →
        v ∉ (outsiderEdge cyc u hu 1).val := by
      intro v hve hvspoke
      have hcases : v = u ∨ v = cyc.toHom 1 := by
        simpa only [outsiderEdge, Sym2.mem_iff] using hvspoke
      rcases hcases with h | h
      · subst v
        exact huSelected d hve
      · subst v
        exact hv hve
    exact (arbitrary_selected_edge_ne_disjoint_host_edge χ r
      (cyc.mapEdgeSet d) (outsiderEdge cyc u hu 1) hdisj) heq.symm
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hsecondAvoid (d : (cycleGraph (m + 1)).edgeSet)
      (hd : d ≠ sourceStep (⟨0, by omega⟩ : Fin m)) :
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    rcases sourceEdge_cases hm d with ⟨j, hjEq⟩ | hdClosing
    · subst d
      by_cases hj1 : j.val = 1
      · have hidx : j = (⟨1, by omega⟩ : Fin m) := Fin.ext hj1
        simpa only [hidx] using hbeta
      have hj0 : j.val ≠ 0 := by
        intro heq
        exact hd (congrArg sourceStep (Fin.ext heq))
      have hj2 : 2 ≤ j.val := by omega
      apply hbetaAvoid
      intro hv
      change cyc.toHom 1 ∈ Sym2.map cyc.toHom (sourceStep j).val at hv
      obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
      have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
      subst k
      change (1 : Fin (m + 1)) ∈ s(Fin.castSucc j, Fin.succ j) at hk
      rcases Sym2.mem_iff.mp hk with h | h
      · have hval : (1 : ℕ) = j.val := by
          simpa only [hone, Fin.val_castSucc] using congrArg Fin.val h
        omega
      · have hval : (1 : ℕ) = j.val + 1 := by
          simpa only [hone, Fin.val_succ] using congrArg Fin.val h
        omega
    · subst d
      apply hbetaAvoid
      intro hv
      change cyc.toHom 1 ∈
        Sym2.map cyc.toHom (sourceClosing m hm).val at hv
      obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
      have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
      subst k
      change (1 : Fin (m + 1)) ∈ s((0 : Fin (m + 1)), Fin.last m) at hk
      rcases Sym2.mem_iff.mp hk with h | h
      · have hval : (1 : ℕ) = 0 := by
          simpa only [hone, Fin.val_zero] using congrArg Fin.val h
        exact Nat.one_ne_zero hval
      · have hval : (1 : ℕ) = m := by
          simpa only [hone, Fin.val_last] using congrArg Fin.val h
        omega
  exact positive_two_spoke_insertion_copy hm χ r cyc u hu
    hspokes hfirstAvoid hsecondAvoid

/-- At any cyclic position, a first spoke NEW at the outside vertex and a
different next spoke force that next spoke to equal its selected outgoing
color under literal host rainbow-cycle exclusion. This is the first Case B
transition, before the equality-to-omitted-edge recurrence takes over.
-/
theorem no_rainbow_outside_mismatch_forces_next_repeat {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ)
    (a : Fin (m + 1))
    (hnewOutside : χ (outsiderEdge cyc u hu a) ∈ newColors χ u)
    (hspokes : χ (outsiderEdge cyc u hu a) ≠
      χ (outsiderEdge cyc u hu (a + 1))) :
    χ (outsiderEdge cyc u hu (a + 1)) =
      cycleOutgoingColor hm χ r cyc (a + 1) := by
  by_contra hnext
  have hshift := shifted_outside cyc u hu a
  have hspoke : outsiderEdge (shiftedCycle cyc a) u hshift 1 =
      outsiderEdge cyc u hu (a + 1) := by
    calc
      outsiderEdge (shiftedCycle cyc a) u hshift 1 =
          outsiderEdge cyc u hu (1 + a) :=
        shifted_outsiderEdge cyc u hu a 1
      _ = outsiderEdge cyc u hu (a + 1) :=
        congrArg (outsiderEdge cyc u hu) (add_comm 1 a)
  have hnewShift : χ (outsiderEdge (shiftedCycle cyc a) u hshift 0) ∈
      newColors χ u := by
    rw [shifted_outsiderEdge cyc u hu a 0, zero_add]
    exact hnewOutside
  have hspokesShift : χ (outsiderEdge (shiftedCycle cyc a) u hshift 0) ≠
      χ (outsiderEdge (shiftedCycle cyc a) u hshift 1) := by
    rw [hspoke, shifted_outsiderEdge cyc u hu a 0, zero_add]
    exact hspokes
  have hbeta : χ (outsiderEdge (shiftedCycle cyc a) u hshift 1) ≠
      restrictedColor χ r ((shiftedCycle cyc a).mapEdgeSet
        (sourceStep (⟨1, by omega⟩ : Fin m))) := by
    rw [hspoke, shifted_step_one_eq_next_step_zero hm]
    exact hnext
  obtain ⟨f, hf⟩ := positive_outside_new_initial_insertion_copy hm χ r
    (shiftedCycle cyc a) u hshift hnewShift hspokesShift hbeta
  exact hnone f hf

end ErdosProblems.AntiRamseyCycleClaimOneOutsideInsertion

namespace ErdosProblems.AntiRamseyCycleClaimOneCommonSpokes

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion
open ErdosProblems.AntiRamseyCycleClaimOneOutsideInsertion
open scoped Fin.NatCast

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Under literal host rainbow-cycle exclusion, a selected outgoing-color
repeat at any cyclic position propagates to position zero. Natural iteration
uses modular addition on Fin; choosing the value of the additive inverse
reaches zero in at most m successor steps, including the closing-edge wrap. -/
theorem no_rainbow_repeat_forces_zero {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ)
    (a : Fin (m + 1))
    (hfirst : χ (outsiderEdge cyc u hu a) =
      cycleOutgoingColor hm χ r cyc a) :
    χ (outsiderEdge cyc u hu 0) = cycleOutgoingColor hm χ r cyc 0 := by
  have hall : ∀ t : ℕ,
      χ (outsiderEdge cyc u hu (a + (t : Fin (m + 1)))) =
        cycleOutgoingColor hm χ r cyc (a + (t : Fin (m + 1))) := by
    intro t
    induction t with
    | zero =>
        simpa only [Nat.cast_zero, add_zero] using hfirst
    | succ t ih =>
        have hnext := no_rainbow_forces_next_repeat hm χ r cyc u hu
          hnone (a + (t : Fin (m + 1))) ih
        simpa only [Nat.cast_succ, add_assoc] using hnext
  have hzero := hall (-a).val
  simpa only [Fin.cast_val_eq_self, add_neg_cancel] using hzero

/-- Case B common-spoke constancy. If the first outside spoke color is NEW
at u and no literal host rainbow cycle of one greater length exists, every
cycle spoke has that same color. No selected attachment or NEW count is used. -/
theorem no_rainbow_outside_new_spokes_eq {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnewOutside : χ (outsiderEdge cyc u hu 0) ∈ newColors χ u)
    (hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ) :
    ∀ j : Fin (m + 1),
      χ (outsiderEdge cyc u hu j) = χ (outsiderEdge cyc u hu 0) := by
  have hzeroAvoid : χ (outsiderEdge cyc u hu 0) ≠
      cycleOutgoingColor hm χ r cyc 0 := by
    intro heq
    rw [cycleOutgoingColor_zero] at heq
    let d : (cycleGraph (m + 1)).edgeSet :=
      sourceStep (⟨0, by omega⟩ : Fin m)
    let e : HostEdge n :=
      ⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
    have hc : χ e = χ (outsiderEdge cyc u hu 0) := heq.symm
    have hue := newColor_every_edge_incident χ u hnewOutside e hc
    change u ∈ Sym2.map cyc.toHom d.val at hue
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hue
    exact hu ⟨i, hi⟩
  have hadj : ∀ a : Fin (m + 1),
      χ (outsiderEdge cyc u hu a) = χ (outsiderEdge cyc u hu 0) →
      χ (outsiderEdge cyc u hu (a + 1)) =
        χ (outsiderEdge cyc u hu 0) := by
    intro a ha
    by_contra hnext
    have hnew : χ (outsiderEdge cyc u hu a) ∈ newColors χ u := by
      rw [ha]
      exact hnewOutside
    have hspokes : χ (outsiderEdge cyc u hu a) ≠
        χ (outsiderEdge cyc u hu (a + 1)) := by
      intro heq
      exact hnext (heq.symm.trans ha)
    have hrepeat := no_rainbow_outside_mismatch_forces_next_repeat
      hm χ r cyc u hu hnone a hnew hspokes
    have hzero := no_rainbow_repeat_forces_zero hm χ r cyc u hu
      hnone (a + 1) hrepeat
    exact hzeroAvoid hzero
  have hall : ∀ j : ℕ,
      χ (outsiderEdge cyc u hu (j : Fin (m + 1))) =
        χ (outsiderEdge cyc u hu 0) := by
    intro j
    induction j with
    | zero =>
        simp only [Nat.cast_zero]
    | succ j ih =>
        have hnext := hadj (j : Fin (m + 1)) ih
        simpa only [Nat.cast_succ] using hnext
  intro j
  simpa only [Fin.cast_val_eq_self] using hall j.val

end ErdosProblems.AntiRamseyCycleClaimOneCommonSpokes

namespace ErdosProblems.AntiRamseyCycleNewChoiceDegree

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

def liftNewColor (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) : newColorUnion χ :=
  ⟨c.val, mem_newColorUnion_of_mem χ v c.property⟩

noncomputable instance selectedGraph_neighborSet_fintype
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ) (v : Fin n) :
    Fintype ((selectedGraph χ r).neighborSet v) := Fintype.ofFinite _

/-- A NEW color at `v` selects an edge of its color incident to `v`,
for every valid choice, including a guarded replacement choice. -/
noncomputable def newChoiceIncidenceEdge (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) :
    (selectedGraph χ r).incidenceSet v := by
  let d : newColorUnion χ := liftNewColor χ v c
  refine ⟨(r.edge d).val, ?_⟩
  change (r.edge d).val ∈ (selectedGraph χ r).edgeSet ∧
    v ∈ (r.edge d).val
  have hselected : (r.edge d).val ∈ (selectedGraph χ r).edgeSet := by
    rw [selectedGraph_edgeSet χ r]
    exact ⟨d, rfl⟩
  have hcolor : χ (r.edge d) = c.val := by
    simpa [d, liftNewColor] using r.color_eq d
  exact ⟨hselected,
    newColor_every_edge_incident χ v c.property (r.edge d) hcolor⟩

/-- Different colors NEW at one vertex select different incident edges. -/
theorem newChoiceIncidenceEdge_injective (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) :
    Function.Injective (newChoiceIncidenceEdge χ r v) := by
  intro a b hab
  have hval := congrArg Subtype.val hab
  change (r.edge (liftNewColor χ v a)).val =
    (r.edge (liftNewColor χ v b)).val at hval
  have hedge : r.edge (liftNewColor χ v a) =
      r.edge (liftNewColor χ v b) := Subtype.ext hval
  have hidx : liftNewColor χ v a = liftNewColor χ v b :=
    NewChoice.edge_injective r hedge
  exact Subtype.ext (congrArg (fun d : newColorUnion χ => d.val) hidx)

/-- The selected degree dominates the deleted-vertex NEW palette at every
vertex for every valid arbitrary-color NEW choice. -/
theorem newChoice_degree_ge_newColors (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) :
    (newColors χ v).card ≤ (selectedGraph χ r).degree v := by
  have hcard : Fintype.card (newColors χ v) ≤
      Fintype.card ((selectedGraph χ r).incidenceSet v) :=
    Fintype.card_le_of_injective (newChoiceIncidenceEdge χ r v)
      (newChoiceIncidenceEdge_injective χ r v)
  simpa only [Fintype.card_coe, SimpleGraph.card_incidenceSet_eq_degree]
    using hcard

end ErdosProblems.AntiRamseyCycleNewChoiceDegree

namespace ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree

variable {n : ℕ} {C : Type*} [DecidableEq C]

noncomputable def newChoiceColorNeighbor (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) : Fin n :=
  ((selectedGraph χ r).incidenceSetEquivNeighborSet v
    (newChoiceIncidenceEdge χ r v c)).val

theorem newChoiceColorNeighbor_adj (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) :
    (selectedGraph χ r).Adj v (newChoiceColorNeighbor χ r v c) := by
  have hw : newChoiceColorNeighbor χ r v c ∈
      (selectedGraph χ r).neighborSet v :=
    ((selectedGraph χ r).incidenceSetEquivNeighborSet v
      (newChoiceIncidenceEdge χ r v c)).property
  exact ((selectedGraph χ r).mem_neighborSet v _).mp hw

theorem newChoiceColorNeighbor_injective (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) :
    Function.Injective (newChoiceColorNeighbor χ r v) := by
  intro a b hab
  have he :
      (selectedGraph χ r).incidenceSetEquivNeighborSet v
          (newChoiceIncidenceEdge χ r v a) =
      (selectedGraph χ r).incidenceSetEquivNeighborSet v
          (newChoiceIncidenceEdge χ r v b) := Subtype.ext hab
  have hinc : newChoiceIncidenceEdge χ r v a =
      newChoiceIncidenceEdge χ r v b :=
    ((selectedGraph χ r).incidenceSetEquivNeighborSet v).injective he
  exact newChoiceIncidenceEdge_injective χ r v hinc

theorem newChoiceIncidenceEdge_eq_pair (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) :
    (newChoiceIncidenceEdge χ r v c).val =
      s(v, newChoiceColorNeighbor χ r v c) := by
  have h :=
    ((selectedGraph χ r).incidenceSetEquivNeighborSet v).symm_apply_apply
      (newChoiceIncidenceEdge χ r v c)
  have hval := congrArg Subtype.val h
  change s(v, newChoiceColorNeighbor χ r v c) =
    (newChoiceIncidenceEdge χ r v c).val at hval
  exact hval.symm

theorem newChoiceIncidenceEdge_color (χ : TopEdgeLabeling (Fin n) C)
    (r : NewChoice χ) (v : Fin n) (c : newColors χ v) :
    χ ⟨(newChoiceIncidenceEdge χ r v c).val,
      SimpleGraph.edgeSet_mono le_top (newChoiceIncidenceEdge χ r v c).property.1⟩ =
      c.val := by
  let d : newColorUnion χ :=
    ⟨c.val, mem_newColorUnion_of_mem χ v c.property⟩
  have hval : (newChoiceIncidenceEdge χ r v c).val = (r.edge d).val := rfl
  have htop :
      (⟨(newChoiceIncidenceEdge χ r v c).val,
        SimpleGraph.edgeSet_mono le_top
          (newChoiceIncidenceEdge χ r v c).property.1⟩ :
        (⊤ : SimpleGraph (Fin n)).edgeSet) = r.edge d := Subtype.ext hval
  rw [htop]
  exact r.color_eq d

theorem exists_newChoiceColorNeighbor_outside
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ) (v : Fin n)
    (P : Finset (Fin n))
    (hsmall : ((selectedGraph χ r).neighborFinset v ∩ P).card <
      (newColors χ v).card) :
    ∃ c : newColors χ v, newChoiceColorNeighbor χ r v c ∉ P := by
  classical
  by_contra h
  push Not at h
  let f : newColors χ v →
      ((selectedGraph χ r).neighborFinset v ∩ P : Finset (Fin n)) := fun c =>
    ⟨newChoiceColorNeighbor χ r v c, Finset.mem_inter.mpr
      ⟨((selectedGraph χ r).mem_neighborFinset v _).mpr
          (newChoiceColorNeighbor_adj χ r v c), h c⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hval : (f a).val = (f b).val := congrArg Subtype.val hab
    change newChoiceColorNeighbor χ r v a = newChoiceColorNeighbor χ r v b at hval
    exact newChoiceColorNeighbor_injective χ r v hval
  have hcard : (newColors χ v).card ≤
      ((selectedGraph χ r).neighborFinset v ∩ P).card :=
    Finset.card_le_card_of_injective hinj
  omega

/-- The color of the selected edge leaving P is NEW at v, the inside
endpoint used in the choice-uniform rotating-path argument. -/
theorem exists_selected_newColor_edge_outside
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ) (v : Fin n)
    (P : Finset (Fin n))
    (hsmall : ((selectedGraph χ r).neighborFinset v ∩ P).card <
      (newColors χ v).card) :
    ∃ w : Fin n, ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
      w ∉ P ∧ (selectedGraph χ r).Adj v w ∧
      e.val = s(v, w) ∧ χ e ∈ newColors χ v := by
  obtain ⟨c, hc⟩ := exists_newChoiceColorNeighbor_outside χ r v P hsmall
  let w : Fin n := newChoiceColorNeighbor χ r v c
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨(newChoiceIncidenceEdge χ r v c).val,
      SimpleGraph.edgeSet_mono le_top (newChoiceIncidenceEdge χ r v c).property.1⟩
  refine ⟨w, e, hc, newChoiceColorNeighbor_adj χ r v c,
    newChoiceIncidenceEdge_eq_pair χ r v c, ?_⟩
  have hcolor : χ e = c.val := newChoiceIncidenceEdge_color χ r v c
  simpa only [hcolor] using c.property

end ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness

namespace ErdosProblems.AntiRamseyCycleClaimOneSecondNewWitness

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- If every host spoke from `u` to a selected cycle has color `α`, a
different color NEW at `u` selects an edge `u-w` with `w` outside the cycle. -/
theorem exists_second_new_selected_edge_outside {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (α : C)
    (hnewu : 2 ≤ (newColors χ u).card)
    (hcommon : ∀ (i : Fin (m + 1))
        (e : (⊤ : SimpleGraph (Fin n)).edgeSet),
      e.val = s(u, cyc.toHom i) → χ e = α) :
    ∃ δ : C, δ ∈ newColors χ u ∧ δ ≠ α ∧
      ∃ w : Fin n, ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
        (selectedGraph χ r).Adj u w ∧ w ≠ u ∧
        w ∉ Set.range cyc.toHom ∧ e.val = s(u, w) ∧ χ e = δ := by
  obtain ⟨δ, hδ, hδα⟩ :=
    Finset.exists_mem_ne (Nat.lt_of_succ_le hnewu) α
  let d : newColors χ u := ⟨δ, hδ⟩
  let w : Fin n := newChoiceColorNeighbor χ r u d
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨(newChoiceIncidenceEdge χ r u d).val,
      SimpleGraph.edgeSet_mono le_top
        (newChoiceIncidenceEdge χ r u d).property.1⟩
  have hadj : (selectedGraph χ r).Adj u w :=
    newChoiceColorNeighbor_adj χ r u d
  have hpair : e.val = s(u, w) :=
    newChoiceIncidenceEdge_eq_pair χ r u d
  have hcolor : χ e = δ := newChoiceIncidenceEdge_color χ r u d
  have hwu : w ≠ u := ((selectedGraph χ r).ne_of_adj hadj).symm
  refine ⟨δ, hδ, hδα, w, e, hadj, hwu, ?_, hpair, hcolor⟩
  rintro ⟨i, hi⟩
  have hepair : e.val = s(u, cyc.toHom i) := by
    simpa only [← hi] using hpair
  exact hδα (hcolor.symm.trans (hcommon i e hepair))

end ErdosProblems.AntiRamseyCycleClaimOneSecondNewWitness

namespace ErdosProblems.AntiRamseyCycleClaimOneJInsertion

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

def betweenEdge (x y : Fin n) (hxy : x ≠ y) : HostEdge n :=
  ⟨s(x, y), (top_adj _ _).mpr hxy⟩

/-- Retained source order `m-1,0,...,m-2`; the last cycle vertex is omitted. -/
def leftBase (m : ℕ) : Fin m ↪ Fin (m + 1) where
  toFun j := Fin.castSucc ((finRotate m).symm j)
  inj' := (Fin.castSucc_injective m).comp (finRotate m).symm.injective

/-- Retained source order `0,2,...,m`; source vertex one is omitted. -/
def rightBase (m : ℕ) : Fin m ↪ Fin (m + 1) :=
  (Fin.succAboveOrderEmb (1 : Fin (m + 1))).toEmbedding

def retainedPosition {m : ℕ} (hm : 2 ≤ m)
    (i : Fin (m + 2)) : Fin m := ⟨i.val - 2, by omega⟩

def slotMap {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n) (i : Fin (m + 2)) : Fin n :=
  if i.val = 1 then x else if i.val = 2 then y
  else cyc.toHom (ρ (retainedPosition hm i))

theorem slotMap_one {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 1) : slotMap hm cyc ρ x y i = x := by
  simp only [slotMap, ite_eq_left hi]

theorem slotMap_two {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n)
    (i : Fin (m + 2)) (hi1 : i.val ≠ 1) (hi2 : i.val = 2) :
    slotMap hm cyc ρ x y i = y := by
  simp only [slotMap, ite_eq_right hi1, ite_eq_left hi2]

theorem slotMap_other {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n)
    (i : Fin (m + 2)) (hi1 : i.val ≠ 1) (hi2 : i.val ≠ 2) :
    slotMap hm cyc ρ x y i = cyc.toHom (ρ (retainedPosition hm i)) := by
  simp only [slotMap, ite_eq_right hi1, ite_eq_right hi2]

theorem slotMap_injective {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n)
    (hx : x ∉ Set.range cyc.toHom) (hy : y ∉ Set.range cyc.toHom)
    (hxy : x ≠ y) : Function.Injective (slotMap hm cyc ρ x y) := by
  intro a b hab
  by_cases ha1 : a.val = 1
  · by_cases hb1 : b.val = 1
    · exact Fin.ext (ha1.trans hb1.symm)
    by_cases hb2 : b.val = 2
    · rw [slotMap_one hm cyc ρ x y a ha1,
        slotMap_two hm cyc ρ x y b hb1 hb2] at hab
      exact False.elim (hxy hab)
    · rw [slotMap_one hm cyc ρ x y a ha1,
        slotMap_other hm cyc ρ x y b hb1 hb2] at hab
      exact False.elim (hx ⟨ρ (retainedPosition hm b), hab.symm⟩)
  by_cases ha2 : a.val = 2
  · by_cases hb1 : b.val = 1
    · rw [slotMap_two hm cyc ρ x y a ha1 ha2,
        slotMap_one hm cyc ρ x y b hb1] at hab
      exact False.elim (hxy hab.symm)
    by_cases hb2 : b.val = 2
    · exact Fin.ext (ha2.trans hb2.symm)
    · rw [slotMap_two hm cyc ρ x y a ha1 ha2,
        slotMap_other hm cyc ρ x y b hb1 hb2] at hab
      exact False.elim (hy ⟨ρ (retainedPosition hm b), hab.symm⟩)
  by_cases hb1 : b.val = 1
  · rw [slotMap_other hm cyc ρ x y a ha1 ha2,
      slotMap_one hm cyc ρ x y b hb1] at hab
    exact False.elim (hx ⟨ρ (retainedPosition hm a), hab⟩)
  by_cases hb2 : b.val = 2
  · rw [slotMap_other hm cyc ρ x y a ha1 ha2,
      slotMap_two hm cyc ρ x y b hb1 hb2] at hab
    exact False.elim (hy ⟨ρ (retainedPosition hm a), hab⟩)
  rw [slotMap_other hm cyc ρ x y a ha1 ha2,
    slotMap_other hm cyc ρ x y b hb1 hb2] at hab
  have hidx := ρ.injective (cyc.injective hab)
  have hval := congrArg Fin.val hidx
  change a.val - 2 = b.val - 2 at hval
  apply Fin.ext
  omega

theorem leftBase_zero {m : ℕ} (hm : 2 ≤ m) :
    leftBase m (⟨0, by omega⟩ : Fin m) =
      (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
  cases m with
  | zero => omega
  | succ k =>
      apply Fin.ext
      change ((finRotate (k + 1)).symm (0 : Fin (k + 1))).val = (k + 1) - 1
      simp only [finRotate_symm_apply, Fin.coe_sub_one, ite_true,
        Nat.add_sub_cancel]

theorem leftBase_pos {m : ℕ} (hm : 2 ≤ m) (j : Fin m)
    (hj : 1 ≤ j.val) :
    leftBase m j = (⟨j.val - 1, by omega⟩ : Fin (m + 1)) := by
  have hj0 : j ≠ (⟨0, by omega⟩ : Fin m) := by
    intro h
    have hval := congrArg Fin.val h
    change j.val = 0 at hval
    omega
  apply Fin.ext
  change ((finRotate m).symm j).val = j.val - 1
  rw [finRotate_symm_apply, Fin.val_sub_one_of_ne_zero hj0]

theorem rightBase_zero {m : ℕ} (hm : 2 ≤ m) :
    rightBase m (⟨0, by omega⟩ : Fin m) = (0 : Fin (m + 1)) := by
  cases m with
  | zero => omega
  | succ k =>
      change (1 : Fin (k + 2)).succAbove (0 : Fin (k + 1)) = 0
      exact Fin.one_succAbove_zero

theorem rightBase_pos {m : ℕ} (hm : 2 ≤ m) (j : Fin m)
    (hj : 1 ≤ j.val) :
    rightBase m j = (⟨j.val + 1, by omega⟩ : Fin (m + 1)) := by
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hle : (1 : Fin (m + 1)) ≤ Fin.castSucc j := by
    change ((1 : Fin (m + 1)) : ℕ) ≤ (Fin.castSucc j).val
    simpa only [hone, Fin.val_castSucc] using hj
  change (1 : Fin (m + 1)).succAbove j = ⟨j.val + 1, by omega⟩
  exact Fin.succAbove_of_le_castSucc _ _ hle

def jLeftMap {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    Fin (m + 2) → Fin n := slotMap hm cyc (leftBase m) u w

def jRightMap {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    Fin (m + 2) → Fin n := slotMap hm cyc (rightBase m) w u

theorem jLeftMap_zero {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    jLeftMap hm cyc u w 0 = cyc.toHom ⟨m - 1, by omega⟩ := by
  change slotMap hm cyc (leftBase m) u w 0 = _
  rw [slotMap_other hm cyc (leftBase m) u w 0 (by exact Nat.zero_ne_one)
    (by exact Nat.zero_ne_add_one 1)]
  exact congrArg cyc.toHom (leftBase_zero hm)

theorem jRightMap_zero {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    jRightMap hm cyc u w 0 = cyc.toHom 0 := by
  change slotMap hm cyc (rightBase m) w u 0 = _
  rw [slotMap_other hm cyc (rightBase m) w u 0 (by exact Nat.zero_ne_one)
    (by exact Nat.zero_ne_add_one 1)]
  exact congrArg cyc.toHom (rightBase_zero hm)

theorem jLeftMap_one {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 1) : jLeftMap hm cyc u w i = u :=
  slotMap_one hm cyc (leftBase m) u w i hi

theorem jLeftMap_two {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 2) : jLeftMap hm cyc u w i = w :=
  slotMap_two hm cyc (leftBase m) u w i (by omega) hi

theorem jRightMap_one {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 1) : jRightMap hm cyc u w i = w :=
  slotMap_one hm cyc (rightBase m) w u i hi

theorem jRightMap_two {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 2) : jRightMap hm cyc u w i = u :=
  slotMap_two hm cyc (rightBase m) w u i (by omega) hi

theorem jLeftMap_tail {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : 3 ≤ i.val) :
    jLeftMap hm cyc u w i = cyc.toHom ⟨i.val - 3, by omega⟩ := by
  change slotMap hm cyc (leftBase m) u w i = _
  rw [slotMap_other hm cyc (leftBase m) u w i (by omega) (by omega)]
  rw [leftBase_pos hm (retainedPosition hm i) (by dsimp [retainedPosition]; omega)]
  congr 1

theorem jRightMap_tail {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : 3 ≤ i.val) :
    jRightMap hm cyc u w i = cyc.toHom ⟨i.val - 1, by omega⟩ := by
  change slotMap hm cyc (rightBase m) w u i = _
  rw [slotMap_other hm cyc (rightBase m) w u i (by omega) (by omega)]
  rw [rightBase_pos hm (retainedPosition hm i) (by dsimp [retainedPosition]; omega)]
  congr 1
  apply Fin.ext
  dsimp [retainedPosition]
  omega

noncomputable def jLeftCopy {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)) := by
  have hp : Function.Injective (jLeftMap hm cyc u w) :=
    slotMap_injective hm cyc (leftBase m) u w hu hw huw
  exact ⟨⟨jLeftMap hm cyc u w, by
    intro a b hab
    exact (top_adj _ _).mpr (hp.ne ((cycleGraph (m + 2)).ne_of_adj hab))⟩, hp⟩

noncomputable def jRightCopy {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)) := by
  have hp : Function.Injective (jRightMap hm cyc u w) :=
    slotMap_injective hm cyc (rightBase m) w u hw hu huw.symm
  exact ⟨⟨jRightMap hm cyc u w, by
    intro a b hab
    exact (top_adj _ _).mpr (hp.ne ((cycleGraph (m + 2)).ne_of_adj hab))⟩, hp⟩

theorem jLeftMap_step_tail {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 1)) (hi : 3 ≤ i.val) :
    ∃ j : Fin m, j.val + 1 < m ∧
      Sym2.map (jLeftMap hm cyc u w) (sourceStep i).val =
        Sym2.map cyc.toHom (sourceStep j).val := by
  let j : Fin m := ⟨i.val - 3, by omega⟩
  have hj : j.val + 1 < m := by dsimp [j]; omega
  have hlo := jLeftMap_tail hm cyc u w (Fin.castSucc i)
    (by simpa only [Fin.val_castSucc] using hi)
  have hhi := jLeftMap_tail hm cyc u w (Fin.succ i)
    (by simp only [Fin.val_succ]; omega)
  have hloIndex : (⟨(Fin.castSucc i).val - 3, by omega⟩ : Fin (m + 1)) =
      Fin.castSucc j := by
    apply Fin.ext
    rfl
  have hhiIndex : (⟨(Fin.succ i).val - 3, by omega⟩ : Fin (m + 1)) =
      Fin.succ j := by
    apply Fin.ext
    dsimp [j]
    omega
  refine ⟨j, hj, ?_⟩
  simp only [sourceStep, Sym2.map_mk]
  rw [hlo, hhi, hloIndex, hhiIndex]

theorem jRightMap_step_tail {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 1)) (hi : 3 ≤ i.val) :
    ∃ j : Fin m, 2 ≤ j.val ∧
      Sym2.map (jRightMap hm cyc u w) (sourceStep i).val =
        Sym2.map cyc.toHom (sourceStep j).val := by
  let j : Fin m := ⟨i.val - 1, by omega⟩
  have hj : 2 ≤ j.val := by dsimp [j]; omega
  have hlo := jRightMap_tail hm cyc u w (Fin.castSucc i)
    (by simpa only [Fin.val_castSucc] using hi)
  have hhi := jRightMap_tail hm cyc u w (Fin.succ i)
    (by simp only [Fin.val_succ]; omega)
  have hloIndex : (⟨(Fin.castSucc i).val - 1, by omega⟩ : Fin (m + 1)) =
      Fin.castSucc j := by
    apply Fin.ext
    rfl
  have hhiIndex : (⟨(Fin.succ i).val - 1, by omega⟩ : Fin (m + 1)) =
      Fin.succ j := by
    apply Fin.ext
    dsimp [j]
    omega
  refine ⟨j, hj, ?_⟩
  simp only [sourceStep, Sym2.map_mk]
  rw [hlo, hhi, hloIndex, hhiIndex]

theorem jLeftMap_closing {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    Sym2.map (jLeftMap hm cyc u w) (sourceClosing (m + 1) (by omega)).val =
      Sym2.map cyc.toHom (sourceStep (⟨m - 2, by omega⟩ : Fin m)).val := by
  have hlast := jLeftMap_tail hm cyc u w (Fin.last (m + 1))
    (by simp only [Fin.val_last]; omega)
  simp only [sourceClosing, sourceStep, Sym2.map_mk]
  rw [jLeftMap_zero hm cyc u w, hlast]
  have h0 : (⟨m - 1, by omega⟩ : Fin (m + 1)) =
      Fin.succ (⟨m - 2, by omega⟩ : Fin m) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  have hlast0 : (⟨(Fin.last (m + 1)).val - 3, by omega⟩ : Fin (m + 1)) =
      Fin.castSucc (⟨m - 2, by omega⟩ : Fin m) := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_castSucc]
    omega
  rw [h0, hlast0]
  exact Sym2.eq_swap

theorem jRightMap_closing {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    Sym2.map (jRightMap hm cyc u w) (sourceClosing (m + 1) (by omega)).val =
      Sym2.map cyc.toHom (sourceClosing m hm).val := by
  have hlast := jRightMap_tail hm cyc u w (Fin.last (m + 1))
    (by simp only [Fin.val_last]; omega)
  have hlastIndex : (⟨(Fin.last (m + 1)).val - 1, by omega⟩ : Fin (m + 1)) =
      Fin.last m := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  simp only [sourceClosing, Sym2.map_mk]
  rw [jRightMap_zero hm cyc u w, hlast, hlastIndex]

def ThreeEdgeClass {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)))
    (Retained : (cycleGraph (m + 1)).edgeSet → Prop)
    (e₀ e₁ e₂ : (cycleGraph (m + 2)).edgeSet)
    (α β γ : C) (e : (cycleGraph (m + 2)).edgeSet) : Prop :=
  (e = e₀ ∧ EdgeLabeling.pullback χ f.toHom e = α) ∨
  (e = e₁ ∧ EdgeLabeling.pullback χ f.toHom e = β) ∨
  (e = e₂ ∧ EdgeLabeling.pullback χ f.toHom e = γ) ∨
  ∃ d : (cycleGraph (m + 1)).edgeSet,
    Retained d ∧
    EdgeLabeling.pullback χ f.toHom e = restrictedColor χ r (cyc.mapEdgeSet d) ∧
    f.mapEdgeSet e =
      (⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩ : HostEdge n)

/-- Retained edges keep their actual host-edge map equality. -/
theorem three_inserted_palette_isRainbow {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)))
    (Retained : (cycleGraph (m + 1)).edgeSet → Prop)
    (e₀ e₁ e₂ : (cycleGraph (m + 2)).edgeSet)
    (α β γ : C)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hAvoid : ∀ d : (cycleGraph (m + 1)).edgeSet, Retained d →
      α ≠ restrictedColor χ r (cyc.mapEdgeSet d) ∧
      β ≠ restrictedColor χ r (cyc.mapEdgeSet d) ∧
      γ ≠ restrictedColor χ r (cyc.mapEdgeSet d))
    (hClass : ∀ e : (cycleGraph (m + 2)).edgeSet,
      (e = e₀ ∧ EdgeLabeling.pullback χ f.toHom e = α) ∨
      (e = e₁ ∧ EdgeLabeling.pullback χ f.toHom e = β) ∨
      (e = e₂ ∧ EdgeLabeling.pullback χ f.toHom e = γ) ∨
      ∃ d : (cycleGraph (m + 1)).edgeSet,
        Retained d ∧
        EdgeLabeling.pullback χ f.toHom e =
          restrictedColor χ r (cyc.mapEdgeSet d) ∧
        f.mapEdgeSet e =
          (⟨(cyc.mapEdgeSet d).val,
            SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩ :
              HostEdge n)) : IsRainbow f.toHom χ := by
  let L := EdgeLabeling.pullback χ f.toHom
  let lifted : (cycleGraph (m + 1)).edgeSet → HostEdge n := fun d =>
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  change Function.Injective L
  intro a b heq
  rcases hClass a with hA₁ | hB₁ | hC₁ | hR₁
  · rcases hClass b with hA₂ | hB₂ | hC₂ | hR₂
    · exact hA₁.1.trans hA₂.1.symm
    · exact False.elim (hαβ (hA₁.2.symm.trans (heq.trans hB₂.2)))
    · exact False.elim (hαγ (hA₁.2.symm.trans (heq.trans hC₂.2)))
    · obtain ⟨d, hd, hc, _⟩ := hR₂
      exact False.elim ((hAvoid d hd).1 (hA₁.2.symm.trans (heq.trans hc)))
  · rcases hClass b with hA₂ | hB₂ | hC₂ | hR₂
    · exact False.elim (hαβ (hA₂.2.symm.trans (heq.symm.trans hB₁.2)))
    · exact hB₁.1.trans hB₂.1.symm
    · exact False.elim (hβγ (hB₁.2.symm.trans (heq.trans hC₂.2)))
    · obtain ⟨d, hd, hc, _⟩ := hR₂
      exact False.elim ((hAvoid d hd).2.1 (hB₁.2.symm.trans (heq.trans hc)))
  · rcases hClass b with hA₂ | hB₂ | hC₂ | hR₂
    · exact False.elim (hαγ (hA₂.2.symm.trans (heq.symm.trans hC₁.2)))
    · exact False.elim (hβγ (hB₂.2.symm.trans (heq.symm.trans hC₁.2)))
    · exact hC₁.1.trans hC₂.1.symm
    · obtain ⟨d, hd, hc, _⟩ := hR₂
      exact False.elim ((hAvoid d hd).2.2 (hC₁.2.symm.trans (heq.trans hc)))
  · obtain ⟨d₁, hd₁, hc₁, hm₁⟩ := hR₁
    rcases hClass b with hA₂ | hB₂ | hC₂ | hR₂
    · exact False.elim ((hAvoid d₁ hd₁).1 (hA₂.2.symm.trans (heq.symm.trans hc₁)))
    · exact False.elim ((hAvoid d₁ hd₁).2.1 (hB₂.2.symm.trans (heq.symm.trans hc₁)))
    · exact False.elim ((hAvoid d₁ hd₁).2.2 (hC₂.2.symm.trans (heq.symm.trans hc₁)))
    · obtain ⟨d₂, _, hc₂, hm₂⟩ := hR₂
      have hcolors := hc₁.symm.trans (heq.trans hc₂)
      have hd : d₁ = d₂ :=
        cyc.mapEdgeSet.injective (restrictedColor_injective χ r hcolors)
      apply f.mapEdgeSet.injective
      exact hm₁.trans ((congrArg lifted hd).trans hm₂.symm)

def RetainedLeft {m : ℕ} (d : (cycleGraph (m + 1)).edgeSet) : Prop :=
  ∃ j : Fin m, j.val + 1 < m ∧ d = sourceStep j

def RetainedRight {m : ℕ} (hm : 2 ≤ m)
    (d : (cycleGraph (m + 1)).edgeSet) : Prop :=
  (∃ j : Fin m, 2 ≤ j.val ∧ d = sourceStep j) ∨ d = sourceClosing m hm

omit [DecidableEq C] in
theorem copy_color_of_map {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C)
    (f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)))
    (e : (cycleGraph (m + 2)).edgeSet) (d : HostEdge n)
    (hmap : f.mapEdgeSet e = d) :
    EdgeLabeling.pullback χ f.toHom e = χ d := by
  simpa only [EdgeLabeling.pullback_apply, SimpleGraph.Copy.mapEdgeSet,
    Function.Embedding.coeFn_mk]
    using congrArg χ hmap

theorem jLeftMap_first_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (jLeftMap hm cyc u w)
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1))).val =
      (outsiderEdge cyc u hu (⟨m - 1, by omega⟩ : Fin (m + 1))).val := by
  change s(jLeftMap hm cyc u w 0,
    jLeftMap hm cyc u w (Fin.succ (⟨0, by omega⟩ : Fin (m + 1)))) =
      s(u, cyc.toHom ⟨m - 1, by omega⟩)
  rw [jLeftMap_zero hm cyc u w,
    jLeftMap_one hm cyc u w _ rfl]
  exact Sym2.eq_swap

theorem jLeftMap_bridge {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (huw : u ≠ w) :
    Sym2.map (jLeftMap hm cyc u w)
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1))).val =
      (betweenEdge u w huw).val := by
  change s(jLeftMap hm cyc u w (Fin.castSucc (⟨1, by omega⟩ : Fin (m + 1))),
    jLeftMap hm cyc u w (Fin.succ (⟨1, by omega⟩ : Fin (m + 1)))) = s(u, w)
  rw [jLeftMap_one hm cyc u w _ rfl, jLeftMap_two hm cyc u w _ rfl]

theorem jLeftMap_third_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hw : w ∉ Set.range cyc.toHom) :
    Sym2.map (jLeftMap hm cyc u w)
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1))).val =
      (outsiderEdge cyc w hw 0).val := by
  change s(jLeftMap hm cyc u w (Fin.castSucc (⟨2, by omega⟩ : Fin (m + 1))),
    jLeftMap hm cyc u w (Fin.succ (⟨2, by omega⟩ : Fin (m + 1)))) =
      s(w, cyc.toHom 0)
  rw [jLeftMap_two hm cyc u w _ rfl, jLeftMap_tail hm cyc u w _ (by exact le_rfl)]
  rfl

theorem jRightMap_first_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hw : w ∉ Set.range cyc.toHom) :
    Sym2.map (jRightMap hm cyc u w)
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1))).val =
      (outsiderEdge cyc w hw 0).val := by
  change s(jRightMap hm cyc u w 0,
    jRightMap hm cyc u w (Fin.succ (⟨0, by omega⟩ : Fin (m + 1)))) =
      s(w, cyc.toHom 0)
  rw [jRightMap_zero hm cyc u w, jRightMap_one hm cyc u w _ rfl]
  exact Sym2.eq_swap

theorem jRightMap_bridge {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (huw : u ≠ w) :
    Sym2.map (jRightMap hm cyc u w)
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1))).val =
      (betweenEdge u w huw).val := by
  change s(jRightMap hm cyc u w (Fin.castSucc (⟨1, by omega⟩ : Fin (m + 1))),
    jRightMap hm cyc u w (Fin.succ (⟨1, by omega⟩ : Fin (m + 1)))) = s(u, w)
  rw [jRightMap_one hm cyc u w _ rfl, jRightMap_two hm cyc u w _ rfl]
  exact Sym2.eq_swap

theorem jRightMap_third_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (jRightMap hm cyc u w)
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1))).val =
      (outsiderEdge cyc u hu (⟨2, by omega⟩ : Fin (m + 1))).val := by
  change s(jRightMap hm cyc u w (Fin.castSucc (⟨2, by omega⟩ : Fin (m + 1))),
    jRightMap hm cyc u w (Fin.succ (⟨2, by omega⟩ : Fin (m + 1)))) =
      s(u, cyc.toHom ⟨2, by omega⟩)
  rw [jRightMap_two hm cyc u w _ rfl, jRightMap_tail hm cyc u w _ (by exact le_rfl)]
  rfl

theorem jLeft_edge_classes {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) (α : C)
    (hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α)
    (e : (cycleGraph (m + 2)).edgeSet) :
    ThreeEdgeClass χ r cyc (jLeftCopy hm cyc u w hu hw huw) RetainedLeft
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1)))
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1)))
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1)))
      α (χ (betweenEdge u w huw)) (χ (outsiderEdge cyc w hw 0)) e := by
  let f := jLeftCopy hm cyc u w hu hw huw
  let lifted : (cycleGraph (m + 1)).edgeSet → HostEdge n := fun d =>
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  have hmapHost (a : (cycleGraph (m + 2)).edgeSet) (d : HostEdge n)
      (hval : Sym2.map (jLeftMap hm cyc u w) a.val = d.val) :
      f.mapEdgeSet a = d := by
    apply Subtype.ext
    exact hval
  have hmapSelected (a : (cycleGraph (m + 2)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map (jLeftMap hm cyc u w) a.val = Sym2.map cyc.toHom d.val) :
      f.mapEdgeSet a = lifted d := by
    apply Subtype.ext
    exact hval
  have hcolorSelected (a : (cycleGraph (m + 2)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet) (hmap : f.mapEdgeSet a = lifted d) :
      EdgeLabeling.pullback χ f.toHom a =
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    simpa only [lifted, restrictedColor] using copy_color_of_map χ f a (lifted d) hmap
  have h0 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1))) = α := by
    have hc := copy_color_of_map χ f _ _
      (hmapHost _ _ (jLeftMap_first_spoke hm cyc u w hu))
    exact hc.trans (hcommon ⟨m - 1, by omega⟩)
  have h1 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1))) = χ (betweenEdge u w huw) :=
    copy_color_of_map χ f _ _ (hmapHost _ _ (jLeftMap_bridge hm cyc u w huw))
  have h2 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1))) = χ (outsiderEdge cyc w hw 0) :=
    copy_color_of_map χ f _ _ (hmapHost _ _ (jLeftMap_third_spoke hm cyc u w hw))
  unfold ThreeEdgeClass
  rcases sourceEdge_cases (m := m + 1) (by omega) e with ⟨i, he⟩ | he
  · subst e
    by_cases hi0 : i.val = 0
    · have hidx : i = (⟨0, by omega⟩ : Fin (m + 1)) := Fin.ext hi0
      rw [hidx]
      exact Or.inl ⟨rfl, h0⟩
    by_cases hi1 : i.val = 1
    · have hidx : i = (⟨1, by omega⟩ : Fin (m + 1)) := Fin.ext hi1
      rw [hidx]
      exact Or.inr (Or.inl ⟨rfl, h1⟩)
    by_cases hi2 : i.val = 2
    · have hidx : i = (⟨2, by omega⟩ : Fin (m + 1)) := Fin.ext hi2
      rw [hidx]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩))
    have hi : 3 ≤ i.val := by omega
    obtain ⟨j, hj, hval⟩ := jLeftMap_step_tail hm cyc u w i hi
    have hmap := hmapSelected (sourceStep i) (sourceStep j) hval
    exact Or.inr (Or.inr (Or.inr ⟨sourceStep j, ⟨j, hj, rfl⟩,
      hcolorSelected _ _ hmap, hmap⟩))
  · subst e
    let j : Fin m := ⟨m - 2, by omega⟩
    have hj : j.val + 1 < m := by dsimp [j]; omega
    have hmap := hmapSelected _ _ (jLeftMap_closing hm cyc u w)
    exact Or.inr (Or.inr (Or.inr ⟨sourceStep j, ⟨j, hj, rfl⟩,
      hcolorSelected _ _ hmap, hmap⟩))

theorem jRight_edge_classes {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) (α : C)
    (hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α)
    (e : (cycleGraph (m + 2)).edgeSet) :
    ThreeEdgeClass χ r cyc (jRightCopy hm cyc u w hu hw huw) (RetainedRight hm)
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1)))
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1)))
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1)))
      α (χ (betweenEdge u w huw)) (χ (outsiderEdge cyc w hw 0)) e := by
  let f := jRightCopy hm cyc u w hu hw huw
  let lifted : (cycleGraph (m + 1)).edgeSet → HostEdge n := fun d =>
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  have hmapHost (a : (cycleGraph (m + 2)).edgeSet) (d : HostEdge n)
      (hval : Sym2.map (jRightMap hm cyc u w) a.val = d.val) :
      f.mapEdgeSet a = d := by
    apply Subtype.ext
    exact hval
  have hmapSelected (a : (cycleGraph (m + 2)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map (jRightMap hm cyc u w) a.val = Sym2.map cyc.toHom d.val) :
      f.mapEdgeSet a = lifted d := by
    apply Subtype.ext
    exact hval
  have hcolorSelected (a : (cycleGraph (m + 2)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet) (hmap : f.mapEdgeSet a = lifted d) :
      EdgeLabeling.pullback χ f.toHom a =
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    simpa only [lifted, restrictedColor] using copy_color_of_map χ f a (lifted d) hmap
  have h0 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1))) = χ (outsiderEdge cyc w hw 0) :=
    copy_color_of_map χ f _ _ (hmapHost _ _ (jRightMap_first_spoke hm cyc u w hw))
  have h1 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1))) = χ (betweenEdge u w huw) :=
    copy_color_of_map χ f _ _ (hmapHost _ _ (jRightMap_bridge hm cyc u w huw))
  have h2 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1))) = α := by
    have hc := copy_color_of_map χ f _ _
      (hmapHost _ _ (jRightMap_third_spoke hm cyc u w hu))
    exact hc.trans (hcommon ⟨2, by omega⟩)
  unfold ThreeEdgeClass
  rcases sourceEdge_cases (m := m + 1) (by omega) e with ⟨i, he⟩ | he
  · subst e
    by_cases hi0 : i.val = 0
    · have hidx : i = (⟨0, by omega⟩ : Fin (m + 1)) := Fin.ext hi0
      rw [hidx]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, h0⟩))
    by_cases hi1 : i.val = 1
    · have hidx : i = (⟨1, by omega⟩ : Fin (m + 1)) := Fin.ext hi1
      rw [hidx]
      exact Or.inr (Or.inl ⟨rfl, h1⟩)
    by_cases hi2 : i.val = 2
    · have hidx : i = (⟨2, by omega⟩ : Fin (m + 1)) := Fin.ext hi2
      rw [hidx]
      exact Or.inl ⟨rfl, h2⟩
    have hi : 3 ≤ i.val := by omega
    obtain ⟨j, hj, hval⟩ := jRightMap_step_tail hm cyc u w i hi
    have hmap := hmapSelected (sourceStep i) (sourceStep j) hval
    exact Or.inr (Or.inr (Or.inr ⟨sourceStep j, Or.inl ⟨j, hj, rfl⟩,
      hcolorSelected _ _ hmap, hmap⟩))
  · subst e
    have hmap := hmapSelected _ _ (jRightMap_closing hm cyc u w)
    exact Or.inr (Or.inr (Or.inr ⟨sourceClosing m hm, Or.inr rfl,
      hcolorSelected _ _ hmap, hmap⟩))

theorem outside_not_selected_cycle_edge {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (d : (cycleGraph (m + 1)).edgeSet) : u ∉ (cyc.mapEdgeSet d).val := by
  intro he
  change u ∈ Sym2.map cyc.toHom d.val at he
  obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp he
  exact hu ⟨i, hi⟩

theorem new_color_ne_edge_of_not_mem
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin n) (α : C)
    (hαnew : α ∈ newColors χ u) (e : HostEdge n) (hu : u ∉ e.val) : α ≠ χ e := by
  intro heq
  exact hu (newColor_every_edge_incident χ u hαnew e heq.symm)

theorem outside_new_ne_selected_cycle_color {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (α : C) (hαnew : α ∈ newColors χ u)
    (d : (cycleGraph (m + 1)).edgeSet) :
    α ≠ restrictedColor χ r (cyc.mapEdgeSet d) := by
  let e : HostEdge n :=
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  exact new_color_ne_edge_of_not_mem χ u α hαnew e
    (outside_not_selected_cycle_edge χ r cyc u hu d)

theorem outside_not_gamma_edge {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u w : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hw : w ∉ Set.range cyc.toHom) (huw : u ≠ w) :
    u ∉ (outsiderEdge cyc w hw 0).val := by
  intro he
  have hcases : u = w ∨ u = cyc.toHom 0 := by
    simpa only [outsiderEdge, Sym2.mem_iff] using he
  rcases hcases with h | h
  · exact huw h
  · exact hu ⟨0, h.symm⟩

/-- The w-v0 host spoke can repeat a selected consecutive edge color only at
source step zero. This uses the checked arbitrary-choice NEW endpoint lemma. -/
theorem gamma_ne_sourceStep_of_pos {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (w : Fin n) (hw : w ∉ Set.range cyc.toHom) (j : Fin m) (hj : 1 ≤ j.val) :
    χ (outsiderEdge cyc w hw 0) ≠
      restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
  have hv0 : cyc.toHom 0 ∉ (cyc.mapEdgeSet (sourceStep j)).val := by
    intro hv
    change cyc.toHom 0 ∈ Sym2.map cyc.toHom (sourceStep j).val at hv
    obtain ⟨k, hk, hk0⟩ := Sym2.mem_map.mp hv
    have hkey : k = (0 : Fin (m + 1)) := cyc.injective hk0
    subst k
    change (0 : Fin (m + 1)) ∈ s(Fin.castSucc j, Fin.succ j) at hk
    rcases Sym2.mem_iff.mp hk with h | h
    · have hval : (0 : ℕ) = j.val := by
        simpa only [Fin.val_zero, Fin.val_castSucc] using congrArg Fin.val h
      omega
    · have hval : (0 : ℕ) = j.val + 1 := by
        simpa only [Fin.val_zero, Fin.val_succ] using congrArg Fin.val h
      omega
  have hdisj : ∀ v : Fin n, v ∈ (cyc.mapEdgeSet (sourceStep j)).val →
      v ∉ (outsiderEdge cyc w hw 0).val := by
    intro v hve hvgamma
    have hcases : v = w ∨ v = cyc.toHom 0 := by
      simpa only [outsiderEdge, Sym2.mem_iff] using hvgamma
    rcases hcases with h | h
    · subst v
      exact outside_not_selected_cycle_edge χ r cyc w hw (sourceStep j) hve
    · subst v
      exact hv0 hve
  intro heq
  exact (arbitrary_selected_edge_ne_disjoint_host_edge χ r
    (cyc.mapEdgeSet (sourceStep j)) (outsiderEdge cyc w hw 0) hdisj) heq.symm

/-- Positive left J insertion. The extra gamma guard is discharged by a
contradiction in Case B under no rainbow C_(m+2). The bridge is the literal
selected uw edge, whose color is NEW at u and differs from alpha. -/
theorem positive_jLeft_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) (α : C) (hαnew : α ∈ newColors χ u)
    (_hselected : (selectedGraph χ r).Adj u w)
    (hδnew : χ (betweenEdge u w huw) ∈ newColors χ u)
    (hδα : χ (betweenEdge u w huw) ≠ α)
    (hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α)
    (hgamma : χ (outsiderEdge cyc w hw 0) ≠
      restrictedColor χ r (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m)))) :
    IsRainbow (jLeftCopy hm cyc u w hu hw huw).toHom χ := by
  have hαγ : α ≠ χ (outsiderEdge cyc w hw 0) :=
    new_color_ne_edge_of_not_mem χ u α hαnew _
      (outside_not_gamma_edge χ r cyc u w hu hw huw)
  have hδγ : χ (betweenEdge u w huw) ≠ χ (outsiderEdge cyc w hw 0) :=
    new_color_ne_edge_of_not_mem χ u _ hδnew _
      (outside_not_gamma_edge χ r cyc u w hu hw huw)
  apply three_inserted_palette_isRainbow χ r cyc
    (jLeftCopy hm cyc u w hu hw huw) RetainedLeft
    (sourceStep (⟨0, by omega⟩ : Fin (m + 1)))
    (sourceStep (⟨1, by omega⟩ : Fin (m + 1)))
    (sourceStep (⟨2, by omega⟩ : Fin (m + 1)))
    α (χ (betweenEdge u w huw)) (χ (outsiderEdge cyc w hw 0))
    hδα.symm hαγ hδγ
  · intro d hd
    refine ⟨outside_new_ne_selected_cycle_color χ r cyc u hu α hαnew d,
      outside_new_ne_selected_cycle_color χ r cyc u hu _ hδnew d, ?_⟩
    obtain ⟨j, _, hjEq⟩ := hd
    subst d
    by_cases hj0 : j.val = 0
    · have hidx : j = (⟨0, by omega⟩ : Fin m) := Fin.ext hj0
      simpa only [hidx] using hgamma
    · exact gamma_ne_sourceStep_of_pos χ r cyc w hw j (by omega)
  · intro e
    exact jLeft_edge_classes hm χ r cyc u w hu hw huw α hcommon e

/-- Positive right J insertion. It retains only consecutive selected source
steps with index at least two and the original selected closing edge. -/
theorem positive_jRight_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) (α : C) (hαnew : α ∈ newColors χ u)
    (_hselected : (selectedGraph χ r).Adj u w)
    (hδnew : χ (betweenEdge u w huw) ∈ newColors χ u)
    (hδα : χ (betweenEdge u w huw) ≠ α)
    (hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α)
    (hgamma : χ (outsiderEdge cyc w hw 0) ≠
      restrictedColor χ r (cyc.mapEdgeSet (sourceClosing m hm))) :
    IsRainbow (jRightCopy hm cyc u w hu hw huw).toHom χ := by
  have hαγ : α ≠ χ (outsiderEdge cyc w hw 0) :=
    new_color_ne_edge_of_not_mem χ u α hαnew _
      (outside_not_gamma_edge χ r cyc u w hu hw huw)
  have hδγ : χ (betweenEdge u w huw) ≠ χ (outsiderEdge cyc w hw 0) :=
    new_color_ne_edge_of_not_mem χ u _ hδnew _
      (outside_not_gamma_edge χ r cyc u w hu hw huw)
  apply three_inserted_palette_isRainbow χ r cyc
    (jRightCopy hm cyc u w hu hw huw) (RetainedRight hm)
    (sourceStep (⟨2, by omega⟩ : Fin (m + 1)))
    (sourceStep (⟨1, by omega⟩ : Fin (m + 1)))
    (sourceStep (⟨0, by omega⟩ : Fin (m + 1)))
    α (χ (betweenEdge u w huw)) (χ (outsiderEdge cyc w hw 0))
    hδα.symm hαγ hδγ
  · intro d hd
    refine ⟨outside_new_ne_selected_cycle_color χ r cyc u hu α hαnew d,
      outside_new_ne_selected_cycle_color χ r cyc u hu _ hδnew d, ?_⟩
    rcases hd with ⟨j, hj, hjEq⟩ | hjClosing
    · subst d
      exact gamma_ne_sourceStep_of_pos χ r cyc w hw j (by omega)
    · subst d
      exact hgamma
  · intro e
    exact jRight_edge_classes hm χ r cyc u w hu hw huw α hcommon e

end ErdosProblems.AntiRamseyCycleClaimOneJInsertion

namespace ErdosProblems.AntiRamseyCycleClaimOneCaseB

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion
open ErdosProblems.AntiRamseyCycleClaimOneCommonSpokes
open ErdosProblems.AntiRamseyCycleClaimOneSecondNewWitness
open ErdosProblems.AntiRamseyCycleClaimOneJInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Full local Case B positive conclusion. The first literal host spoke is
NEW at its outside endpoint, and at least two colors are NEW there. Neither
selected first attachment nor an initial spoke mismatch is assumed. -/
theorem positive_caseB_outside_new_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnewOutside : χ (outsiderEdge cyc u hu 0) ∈ newColors χ u)
    (hnewu : 2 ≤ (newColors χ u).card) :
    ∃ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  classical
  by_contra hnot
  have hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ := by
    intro f hf
    exact hnot ⟨f, hf⟩
  let α : C := χ (outsiderEdge cyc u hu 0)
  have hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α :=
    no_rainbow_outside_new_spokes_eq hm χ r cyc u hu hnewOutside hnone
  have hcommonHost : ∀ (i : Fin (m + 1)) (e : HostEdge n),
      e.val = s(u, cyc.toHom i) → χ e = α := by
    intro i e hepair
    have he : e = outsiderEdge cyc u hu i := Subtype.ext hepair
    rw [he]
    exact hcommon i
  obtain ⟨δ, hδnew, hδα, w, e, hselected, hwu, hw, hepair, hecolor⟩ :=
    exists_second_new_selected_edge_outside χ r cyc u α hnewu hcommonHost
  have huw : u ≠ w := hwu.symm
  have he : e = betweenEdge u w huw := Subtype.ext hepair
  have hbridge : χ (betweenEdge u w huw) = δ :=
    (congrArg χ he).symm.trans hecolor
  have hbridgeNew : χ (betweenEdge u w huw) ∈ newColors χ u := by
    rw [hbridge]
    exact hδnew
  have hbridgeNe : χ (betweenEdge u w huw) ≠ α := by
    rw [hbridge]
    exact hδα
  have hleft : χ (outsiderEdge cyc w hw 0) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m))) := by
    by_contra hgamma
    exact hnone (jLeftCopy hm cyc u w hu hw huw)
      (positive_jLeft_insertion_copy hm χ r cyc u w hu hw huw α hnewOutside
        hselected hbridgeNew hbridgeNe hcommon hgamma)
  have hright : χ (outsiderEdge cyc w hw 0) =
      restrictedColor χ r (cyc.mapEdgeSet (sourceClosing m hm)) := by
    by_contra hgamma
    exact hnone (jRightCopy hm cyc u w hu hw huw)
      (positive_jRight_insertion_copy hm χ r cyc u w hu hw huw α hnewOutside
        hselected hbridgeNew hbridgeNe hcommon hgamma)
  have hsource : sourceStep (⟨0, by omega⟩ : Fin m) = sourceClosing m hm :=
    cyc.mapEdgeSet.injective
      (restrictedColor_injective χ r (hleft.symm.trans hright))
  exact (sourceStep_ne_closing hm (⟨0, by omega⟩ : Fin m)) hsource

end ErdosProblems.AntiRamseyCycleClaimOneCaseB

namespace ErdosProblems.AntiRamseyCycleClaimOneSelectedAttachment

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion
open ErdosProblems.AntiRamseyCycleClaimOneCaseB

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Local Claim 1 at cycle position zero. Selected attachment alone supplies
a NEW owner at one endpoint; the two positive insertion cases then apply. -/
theorem positive_selected_attachment_copy_zero {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (hnewu : 2 ≤ (newColors χ u).card) :
    ∃ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let e : (selectedGraph χ r).edgeSet := ⟨s(u, cyc.toHom 0), hattach⟩
  have heColor : restrictedColor χ r e = χ (outsiderEdge cyc u hu 0) := by
    rfl
  obtain ⟨v, hve, hnew⟩ := arbitrary_selected_edge_has_new_endpoint χ r e
  have hv : v = u ∨ v = cyc.toHom 0 := by
    change v ∈ s(u, cyc.toHom 0) at hve
    exact Sym2.mem_iff.mp hve
  rcases hv with hv | hv
  · subst v
    have hnewOutside : χ (outsiderEdge cyc u hu 0) ∈ newColors χ u := by
      rw [← heColor]
      exact hnew
    exact positive_caseB_outside_new_copy hm χ r cyc u hu hnewOutside hnewu
  · subst v
    have hnewFirst : χ (outsiderEdge cyc u hu 0) ∈ newColors χ (cyc.toHom 0) := by
      rw [← heColor]
      exact hnew
    exact positive_first_endpoint_attachment_copy hm χ r cyc u hu hattach hnewFirst

/-- The already checked cyclic Copy translation moves an arbitrary selected
attachment endpoint to zero and preserves the outside vertex condition. -/
theorem positive_selected_attachment_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) (a : Fin (m + 1))
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom a))
    (hnewu : 2 ≤ (newColors χ u).card) :
    ∃ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  have hshiftAttach : (selectedGraph χ r).Adj u ((shiftedCycle cyc a).toHom 0) := by
    simpa only [shiftedCycle_apply, zero_add] using hattach
  exact positive_selected_attachment_copy_zero hm χ r (shiftedCycle cyc a) u
    (shifted_outside cyc u hu a) hshiftAttach hnewu

/-- Under literal host no-rainbow exclusion, an outside vertex with at least
two NEW colors has no selected attachment to any vertex of this old cycle. -/
theorem no_rainbow_no_outside_selected_attachment {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnewu : 2 ≤ (newColors χ u).card)
    (hnone : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) (a : Fin (m + 1)) :
    ¬ (selectedGraph χ r).Adj u (cyc.toHom a) := by
  intro hattach
  obtain ⟨f, hf⟩ := positive_selected_attachment_copy hm χ r cyc u hu a hattach hnewu
  exact hnone f hf

end ErdosProblems.AntiRamseyCycleClaimOneSelectedAttachment

namespace ErdosProblems.AntiRamseyCycleClaimOneCycleComponent

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimOneSelectedAttachment

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A selected component containing one vertex of an old selected cycle has
exactly that cycle image, under the original high-NEW and host no-rainbow
conditions. Preconnectedness supplies every other cycle vertex in D. -/
theorem selected_component_support_eq_cycle_range {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hnone : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent)
    (hzeroD : cyc.toHom 0 ∈ D.supp) : D.supp = Set.range cyc.toHom := by
  classical
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  have hclosed : ∀ a b : Fin n, a ∈ Set.range cyc.toHom → G.Adj a b →
      b ∈ Set.range cyc.toHom := by
    rintro a b ⟨i, rfl⟩ hab
    by_contra hb
    exact no_rainbow_no_outside_selected_attachment hm χ r cyc b hb
      (hnew b) hnone i hab.symm
  have hgen : ∀ z : Fin n,
      Relation.ReflTransGen G.Adj (cyc.toHom 0) z → z ∈ Set.range cyc.toHom := by
    intro z hz
    induction hz with
    | refl => exact ⟨0, rfl⟩
    | tail _ hab ih => exact hclosed _ _ ih hab
  have hsubset : D.supp ⊆ Set.range cyc.toHom := by
    intro z hzD
    exact hgen z ((G.reachable_iff_reflTransGen _ _).mp
      (D.reachable_of_mem_supp hzeroD hzD))
  have hsupset : Set.range cyc.toHom ⊆ D.supp := by
    rintro z ⟨i, rfl⟩
    have hreach : G.Reachable (cyc.toHom 0) (cyc.toHom i) :=
      Reachable.map cyc.toHom (cycleGraph_preconnected (n := m + 1) 0 i)
    have hcomp : G.connectedComponentMk (cyc.toHom 0) =
        G.connectedComponentMk (cyc.toHom i) := ConnectedComponent.sound hreach
    exact (D.mem_supp_iff _).mpr
      (hcomp.symm.trans ((D.mem_supp_iff _).mp hzeroD))
  exact Set.Subset.antisymm hsubset hsupset

/-- The exact selected component order is the old cycle order. -/
theorem selected_component_card_eq_cycle_order {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hnone : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent)
    (hzeroD : cyc.toHom 0 ∈ D.supp) : D.supp.ncard = m + 1 := by
  rw [selected_component_support_eq_cycle_range hm χ r cyc hnew hnone D hzeroD]
  simpa only [Nat.card_fin] using Set.ncard_range_of_injective cyc.injective

/-- Exact component-local old-cycle exclusion for the oversized branch.
The same component support appears in its size and cycle-containment inputs. -/
theorem oversized_component_excludes_selected_cycle {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hnone : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) (hlarge : m + 1 < D.supp.ncard) :
    ∀ cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r),
      ¬ (∀ i : Fin (m + 1), cyc.toHom i ∈ D.supp) := by
  intro cyc hinside
  have hcard := selected_component_card_eq_cycle_order hm χ r cyc hnew hnone D
    (hinside 0)
  omega

end ErdosProblems.AntiRamseyCycleClaimOneCycleComponent

namespace ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The arbitrary-choice selected-plus-closing edge palette.
The two orientations are discharged in the concrete path theorem below. -/
def selectedPlusClosingColor {β : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (chain : β → (selectedGraph χ r).edgeSet)
    (closing : HostEdge n) : Option β → C
  | none => χ closing
  | some i => restrictedColor χ r (chain i)

theorem selectedPlusClosingColor_injective {β : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (chain : β → (selectedGraph χ r).edgeSet)
    (hchain : Function.Injective chain) (closing : HostEdge n)
    (hne : ∀ i, restrictedColor χ r (chain i) ≠ χ closing) :
    Function.Injective (selectedPlusClosingColor χ r chain closing) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim (hne j hij.symm)
  | some i =>
      cases j with
      | none => exact False.elim (hne i hij)
      | some j =>
          exact congrArg Option.some
            (hchain (restrictedColor_injective χ r hij))

/-- No induced-copy premise is used. -/
theorem ordered_selected_chain_closes_rainbow
    {t : ℕ} (hs : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (chain : Fin t → (selectedGraph χ r).edgeSet)
    (hchain : ∀ i : Fin t,
      (chain i).val = s(p (Fin.castSucc i), p (Fin.succ i)))
    (closing : HostEdge n)
    (hclosing : closing.val = s(p 0, p (Fin.last t)))
    (hne : ∀ i, restrictedColor χ r (chain i) ≠ χ closing) :
    ∃ f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let φ : (cycleGraph (t + 1)) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨p, by
      intro a b hab
      exact (top_adj _ _).mpr (hp.ne ((cycleGraph (t + 1)).ne_of_adj hab))⟩
  let f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hp⟩
  have hchainInj : Function.Injective chain := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    rw [hchain i, hchain j] at hv
    change Sym2.map p (sourceStep i).val =
      Sym2.map p (sourceStep j).val at hv
    have hsource : sourceStep i = sourceStep j :=
      Subtype.ext (Sym2.map.injective hp hv)
    exact sourceStep_injective hsource
  have hpalette :=
    selectedPlusClosingColor_injective χ r chain hchainInj closing hne
  have hstep (i : Fin t) :
      (EdgeLabeling.pullback χ f.toHom) (sourceStep i) =
        restrictedColor χ r (chain i) := by
    change χ (f.toHom.mapEdgeSet (sourceStep i)) =
      χ ⟨(chain i).val, SimpleGraph.edgeSet_mono le_top (chain i).property⟩
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map p (sourceStep i).val = (chain i).val
    simp only [sourceStep, Sym2.map_mk, hchain]
  have hclose :
      (EdgeLabeling.pullback χ f.toHom) (sourceClosing t hs) =
        χ closing := by
    change χ (f.toHom.mapEdgeSet (sourceClosing t hs)) = χ closing
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map p (sourceClosing t hs).val = closing.val
    simp only [sourceClosing, Sym2.map_mk, hclosing]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  rcases sourceEdge_cases hs e₁ with ⟨i, hi⟩ | hi <;>
    rcases sourceEdge_cases hs e₂ with ⟨j, hj⟩ | hj
  · subst e₁
    subst e₂
    have hsome : (some i : Option (Fin t)) = some j :=
      hpalette (by simpa only [selectedPlusClosingColor, hstep] using heq)
    have hij : i = j := by injection hsome with h
    subst j
    rfl
  · subst e₁
    subst e₂
    have hbad : (some i : Option (Fin t)) = none :=
      hpalette (by simpa only [selectedPlusClosingColor, hstep, hclose] using heq)
    cases hbad
  · subst e₁
    subst e₂
    have hbad : (none : Option (Fin t)) = some j :=
      hpalette (by simpa only [selectedPlusClosingColor, hstep, hclose] using heq)
    cases hbad
  · subst e₁
    subst e₂
    rfl

/-- Selected consecutive edge in an injectively ordered path. -/
noncomputable def selectedPathStep {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (i : Fin (m + 1)) : (selectedGraph χ r).edgeSet :=
  ⟨s(p (Fin.castSucc i), p (Fin.succ i)), hpath i⟩

/-- Positive host insertion with exactly the two inward NEW orientations.
There are m+2 selected path vertices and one outside vertex, hence a
literal host cycle on m+3 vertices. The bound m≥1 is the requested
k≥4 Claim 2 range. No color inequality is assumed in this statement. -/
theorem inward_oriented_path_insertion_rainbow
    {m : ℕ} (_hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (u : Fin n) (hu : u ∉ Set.range p)
    (attachment : (selectedGraph χ r).edgeSet)
    (hattachment : attachment.val = s(u, p 0))
    (hnewFirst : restrictedColor χ r attachment ∈ newColors χ (p 0))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m)))) :
    ∃ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let q : Fin ((m + 2) + 1) → Fin n := Fin.cons u p
  have hq : Function.Injective q := Fin.cons_injective_of_injective hu hp
  let chain : Fin (m + 2) → (selectedGraph χ r).edgeSet :=
    Fin.cons attachment (selectedPathStep χ r p hpath)
  let closing : HostEdge n :=
    ⟨s(u, p (Fin.last (m + 1))), (top_adj _ _).mpr (by
      intro h
      exact hu ⟨Fin.last (m + 1), h.symm⟩)⟩
  have hchain : ∀ i : Fin (m + 2),
      (chain i).val = s(q (Fin.castSucc i), q (Fin.succ i)) := by
    intro i
    cases i using Fin.cases with
    | zero =>
        simpa only [chain, q, Fin.cons_zero, Fin.castSucc_zero,
          Fin.cons_succ] using hattachment
    | succ j =>
        simp only [chain, q, Fin.cons_succ, ← Fin.succ_castSucc,
          selectedPathStep]
  have hclosing : closing.val = s(q 0, q (Fin.last (m + 2))) := by
    simp only [closing, q, Fin.cons_zero, Fin.cons_last]
  have houtsideClosing (i : Fin (m + 2))
      (hi : i ≠ Fin.last (m + 1)) : p i ∉ closing.val := by
    intro hin
    change p i ∈ s(u, p (Fin.last (m + 1))) at hin
    rcases Sym2.mem_iff.mp hin with h | h
    · exact hu ⟨i, h⟩
    · exact hi (hp h)
  have hcastLastNe (i : Fin (m + 1)) :
      Fin.castSucc i ≠ Fin.last (m + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    have hil := i.isLt
    omega
  have hzeroNe : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  have hne : ∀ i, restrictedColor χ r (chain i) ≠ χ closing := by
    intro i
    cases i using Fin.cases with
    | zero =>
        change restrictedColor χ r attachment ≠ χ closing
        intro heq
        have hinc := newColor_every_edge_incident χ (p 0)
          hnewFirst closing heq.symm
        exact houtsideClosing 0 hzeroNe hinc
    | succ j =>
        change restrictedColor χ r (selectedPathStep χ r p hpath j) ≠ χ closing
        by_cases hj : j = Fin.last m
        · subst j
          intro heq
          have hinc := newColor_every_edge_incident χ
            (p (Fin.castSucc (Fin.last m))) hnewLast closing heq.symm
          exact houtsideClosing _ (hcastLastNe (Fin.last m)) hinc
        · have hsuccNe : Fin.succ j ≠ Fin.last (m + 1) := by
            intro h
            apply hj
            apply Fin.ext
            have hv := congrArg Fin.val h
            simp only [Fin.val_succ, Fin.val_last] at hv ⊢
            omega
          apply arbitrary_selected_edge_ne_disjoint_host_edge χ r
            (selectedPathStep χ r p hpath j) closing
          intro v hv
          change v ∈ s(p (Fin.castSucc j), p (Fin.succ j)) at hv
          rcases Sym2.mem_iff.mp hv with h | h
          · rw [h]
            exact houtsideClosing _ (hcastLastNe j)
          · rw [h]
            exact houtsideClosing _ hsuccNe
  exact ordered_selected_chain_closes_rainbow (t := m + 2) (by omega)
    χ r q hq chain hchain closing hclosing hne

/-- Literal no-rainbow host premise forbids that oriented selected configuration.
This does not select or rotate a path. -/
theorem no_inward_oriented_path_insertion
    {m : ℕ} (hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (u : Fin n) (hu : u ∉ Set.range p)
    (attachment : (selectedGraph χ r).edgeSet)
    (hattachment : attachment.val = s(u, p 0))
    (hnewFirst : restrictedColor χ r attachment ∈ newColors χ (p 0))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) : False := by
  obtain ⟨f, hf⟩ := inward_oriented_path_insertion_rainbow hm χ r p hp
    hpath u hu attachment hattachment hnewFirst hnewLast
  exact hno f hf

end ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

namespace ErdosProblems.AntiRamseyCycleClosingColorEquality

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Under literal host no-rainbow, the closing edge of a selected path
whose terminal step is NEW at its inner endpoint has the first step's
color. Interior selected steps are disjoint from closing; the terminal
step is handled by its supplied NEW owner, not by disjointness. -/
theorem no_rainbow_forces_first_closing_color
    {m : ℕ} (hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (q : Fin (m + 2) → Fin n) (hq : Function.Injective q)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)))
    (closing : HostEdge n)
    (hclosing : closing.val = s(q 0, q (Fin.last (m + 1))))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r q hpath (Fin.last m)) ∈
      newColors χ (q (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    χ closing = restrictedColor χ r (selectedPathStep χ r q hpath 0) := by
  by_contra hnot
  let chain : Fin (m + 1) → (selectedGraph χ r).edgeSet :=
    selectedPathStep χ r q hpath
  have houtsideClosing (i : Fin (m + 2))
      (hzero : i ≠ 0) (hlast : i ≠ Fin.last (m + 1)) :
      q i ∉ closing.val := by
    intro hin
    rw [hclosing] at hin
    rcases Sym2.mem_iff.mp hin with h | h
    · exact hzero (hq h)
    · exact hlast (hq h)
  have hcastZeroNe (i : Fin (m + 1)) (hi : i ≠ 0) :
      Fin.castSucc i ≠ (0 : Fin (m + 2)) := by
    intro h
    apply hi
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa only [Fin.val_castSucc, Fin.val_zero] using hv
  have hcastLastNe (i : Fin (m + 1)) :
      Fin.castSucc i ≠ Fin.last (m + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    have hil := i.isLt
    omega
  have hsuccZeroNe (i : Fin (m + 1)) :
      Fin.succ i ≠ (0 : Fin (m + 2)) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  have hne : ∀ i : Fin (m + 1),
      restrictedColor χ r (chain i) ≠ χ closing := by
    intro i
    by_cases hzero : i = 0
    · subst i
      change restrictedColor χ r (selectedPathStep χ r q hpath 0) ≠ χ closing
      intro heq
      exact hnot heq.symm
    by_cases hlast : i = Fin.last m
    · subst i
      change restrictedColor χ r
        (selectedPathStep χ r q hpath (Fin.last m)) ≠ χ closing
      intro heq
      have hinc := newColor_every_edge_incident χ
        (q (Fin.castSucc (Fin.last m))) hnewLast closing heq.symm
      exact houtsideClosing _ (hcastZeroNe _ hzero) (hcastLastNe _) hinc
    have hsuccLastNe : Fin.succ i ≠ Fin.last (m + 1) := by
      intro h
      apply hlast
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hv ⊢
      omega
    apply arbitrary_selected_edge_ne_disjoint_host_edge χ r (chain i) closing
    intro v hv
    change v ∈ s(q (Fin.castSucc i), q (Fin.succ i)) at hv
    rcases Sym2.mem_iff.mp hv with h | h
    · rw [h]
      exact houtsideClosing _ (hcastZeroNe _ hzero) (hcastLastNe _)
    · rw [h]
      exact houtsideClosing _ (hsuccZeroNe _) hsuccLastNe
  obtain ⟨f, hf⟩ :=
    ordered_selected_chain_closes_rainbow (t := m + 1) (by omega)
      χ r q hq chain (fun _ => rfl) closing hclosing hne
  exact hno f hf

end ErdosProblems.AntiRamseyCycleClosingColorEquality

namespace ErdosProblems.AntiRamseyCycleComponentHamiltonianNonbridge

open SimpleGraph

/-- An injective pullback retains a bridge whose endpoints lie in its carrier. -/
theorem isBridge_comap_of_injective {V W : Type*}
    (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f)
    {x y : W} (hbridge : G.IsBridge s(f x, f y)) :
    (G.comap f).IsBridge s(x, y) := by
  rw [SimpleGraph.isBridge_iff] at hbridge ⊢
  intro hreach
  let φ : (G.comap f).deleteEdges {s(x, y)} →g
      G.deleteEdges {s(f x, f y)} :=
    { toFun := f
      map_rel' := by
        intro u v huv
        obtain ⟨hadj, hnot⟩ := SimpleGraph.deleteEdges_adj.mp huv
        refine SimpleGraph.deleteEdges_adj.mpr ⟨hadj, ?_⟩
        intro hmem
        have heq := Set.mem_singleton_iff.mp hmem
        have hpair : s(u, v) = s(x, y) := (Sym2.map.injective hf) heq
        exact hnot (Set.mem_singleton_iff.mpr hpair) }
  exact hbridge (hreach.map φ)

/-- If every whole component has a literal Hamiltonian cycle, no selected
edge is a bridge. No finite ambient carrier or connected ambient graph is assumed. -/
theorem not_isBridge_of_component_hamiltonian_cycles
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hcycles : ∀ D : G.ConnectedComponent,
      ∃ (u : D) (c : D.toSimpleGraph.Walk u u), c.IsHamiltonianCycle)
    {e : Sym2 V} (he : e ∈ G.edgeSet) : ¬ G.IsBridge e := by
  classical
  induction e with
  | h x y =>
    intro hbridge
    have hxy : G.Adj x y := he
    let D : G.ConnectedComponent := G.connectedComponentMk x
    let xD : D := ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
    let yD : D := ⟨y, D.mem_supp_of_adj_mem_supp xD.property hxy⟩
    obtain ⟨u, c, hc⟩ := hcycles D
    let : Finite D := hc.finite
    let : Fintype D := Fintype.ofFinite D
    have hham : D.toSimpleGraph.IsHamiltonian := fun _ => ⟨u, c, hc⟩
    have hlocal : D.toSimpleGraph.IsBridge s(xD, yD) :=
      isBridge_comap_of_injective G (fun z : D => z.val)
        Subtype.val_injective hbridge
    exact hlocal.not_isHamiltonian hham

end ErdosProblems.AntiRamseyCycleComponentHamiltonianNonbridge

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

abbrev HostEdge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet

/-- A choice of one host edge for each used color. -/
structure RepresentativeChoice (χ : TopEdgeLabeling (Fin n) (Fin q)) where
  edge : Fin q → HostEdge n
  color_eq : ∀ c, χ (edge c) = c

/-- The spanning graph consisting of the chosen edges. -/
def selectedGraph (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Set.range fun c : Fin q => (r.edge c).val)

theorem RepresentativeChoice.edge_injective {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) : Function.Injective r.edge := by
  intro a b hab
  calc
    a = χ (r.edge a) := (r.color_eq a).symm
    _ = χ (r.edge b) := by rw [hab]
    _ = b := r.color_eq b

theorem selectedGraph_edgeSet (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) :
    (selectedGraph χ r).edgeSet = Set.range (fun c : Fin q => (r.edge c).val) := by
  rw [selectedGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c, rfl⟩, (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet
      (r.edge c).property⟩

/-- Replace the selected edge of color `χ e` by the host edge `e`. -/
def RepresentativeChoice.replace {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) (e : HostEdge n) : RepresentativeChoice χ where
  edge := fun c => if c = χ e then e else r.edge c
  color_eq := by
    intro c
    by_cases h : c = χ e
    · simp [h]
    · simp [h, r.color_eq]

theorem RepresentativeChoice.replace_edge_same {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) (e : HostEdge n) :
    (r.replace e).edge (χ e) = e := by
  simp [RepresentativeChoice.replace]

theorem RepresentativeChoice.replace_edge_other {χ : TopEdgeLabeling (Fin n) (Fin q)}
    (r : RepresentativeChoice χ) (e : HostEdge n) {c : Fin q} (hc : c ≠ χ e) :
    (r.replace e).edge c = r.edge c := by
  simp [RepresentativeChoice.replace, hc]

/-- The replacement graph retains every old edge except the selected edge of the same color. -/
theorem delete_selectedEdge_le_replace (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (e : HostEdge n) :
    (selectedGraph χ r).deleteEdges {(r.edge (χ e)).val} ≤
      selectedGraph χ (r.replace e) := by
  intro u v huv
  have hL : (selectedGraph χ r).Adj u v := (SimpleGraph.deleteEdges_adj.mp huv).1
  have hneq : s(u, v) ≠ (r.edge (χ e)).val := by
    simpa using (SimpleGraph.deleteEdges_adj.mp huv).2
  have hmem : s(u, v) ∈ Set.range (fun c : Fin q => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact hL
  obtain ⟨c, hc⟩ := hmem
  have hother : c ≠ χ e := by
    intro h
    subst c
    exact hneq hc.symm
  have hnew : s(u, v) ∈ (selectedGraph χ (r.replace e)).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, by simpa [r.replace_edge_other e hother] using hc⟩
  exact hnew

/-- The replacement graph includes the new host edge. -/
theorem replacedEdge_mem (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (e : HostEdge n) :
    e.val ∈ (selectedGraph χ (r.replace e)).edgeSet := by
  rw [selectedGraph_edgeSet]
  exact ⟨χ e, by simp [r.replace_edge_same e]⟩

/-- If removing a selected edge leaves the old component connected, inserting a
cross-component edge produces a strictly larger component. -/
theorem component_grows_of_retained_reachability
    (L L' : SimpleGraph (Fin n)) (old : Sym2 (Fin n)) (x u y : Fin n)
    (hle : L.deleteEdges {old} ≤ L') (huy : L'.Adj u y)
    (hu : L.Reachable x u)
    (hy : ¬ L.Reachable x y)
    (hretain : ∀ v, L.Reachable x v → (L.deleteEdges {old}).Reachable x v) :
    (L.connectedComponentMk x).supp.ncard <
      (L'.connectedComponentMk x).supp.ncard := by
  have hsub : (L.connectedComponentMk x).supp ⊆
      (L'.connectedComponentMk x).supp := by
    intro v hv
    have hv' : L.Reachable x v := SimpleGraph.ConnectedComponent.eq.mp hv.symm
    exact SimpleGraph.ConnectedComponent.eq.mpr
      ((hretain v hv').mono hle) |>.symm
  have hynot : y ∉ (L.connectedComponentMk x).supp := by
    intro h
    exact hy (SimpleGraph.ConnectedComponent.eq.mp h.symm)
  have hynew : y ∈ (L'.connectedComponentMk x).supp := by
    have hxu : L'.Reachable x u := (hretain u hu).mono hle
    exact (SimpleGraph.ConnectedComponent.eq.mpr (hxu.trans huy.reachable)).symm
  exact Set.ncard_lt_ncard (hsub.ssubset_of_mem_notMem hynew hynot)
    (Set.toFinite _)

/-- A chosen component is globally largest if no component of any same-color
representative choice has more vertices. This is the explicit extremal choice
used by Yuan before the cut-edge argument. -/
def GloballyLargestComponent (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n) : Prop :=
  ∀ r' : RepresentativeChoice χ, ∀ z : Fin n,
    ((selectedGraph χ r').connectedComponentMk z).supp.ncard ≤
      ((selectedGraph χ r).connectedComponentMk x).supp.ncard

/-- Applied to an edge exchange, the abstract component-growth lemma. -/
theorem replacement_grows_component (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (e : HostEdge n) (x u y : Fin n)
    (he : e.val = s(u, y))
    (hu : (selectedGraph χ r).Reachable x u)
    (hy : ¬ (selectedGraph χ r).Reachable x y)
    (hretain : ∀ v, (selectedGraph χ r).Reachable x v →
      ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v) :
    ((selectedGraph χ r).connectedComponentMk x).supp.ncard <
      ((selectedGraph χ (r.replace e)).connectedComponentMk x).supp.ncard := by
  apply component_grows_of_retained_reachability
    (selectedGraph χ r) (selectedGraph χ (r.replace e))
    (r.edge (χ e)).val x u y (delete_selectedEdge_le_replace χ r e) ?_
    hu hy hretain
  have hmem := replacedEdge_mem χ r e
  rw [he] at hmem
  exact hmem

/-- Removing an edge that is not a bridge preserves every old reachability
relation, even when the whole graph has several components. -/
theorem reachable_deleteEdge_of_not_bridge (L : SimpleGraph (Fin n))
    (old : Sym2 (Fin n)) (hnb : ¬ L.IsBridge old)
    {u v : Fin n} (huv : L.Reachable u v) :
    (L.deleteEdges {old}).Reachable u v := by
  let D := L.deleteEdges {old}
  have hstep : ∀ a b : Fin n, L.Adj a b → D.Reachable a b := by
    intro a b hab
    by_cases he : s(a, b) = old
    · have hnb' : ¬ L.IsBridge s(a, b) := by simpa [he] using hnb
      by_contra hnotreach
      have hnotreach' : ¬ (L.deleteEdges {s(a, b)}).Reachable a b := by
        simpa [D, he] using hnotreach
      exact hnb' (SimpleGraph.isBridge_iff.mpr hnotreach')
    · exact (SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa using he⟩).reachable
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab p ih => exact (hstep _ _ hab).trans ih

/-- If deleting one edge separates two previously reachable vertices, both
endpoints of that edge lie in their original connected component. -/
theorem edge_endpoints_reachable_of_delete_disconnects (L : SimpleGraph (Fin n))
    (old : Sym2 (Fin n)) {x v : Fin n}
    (hv : L.Reachable x v)
    (hnot : ¬ (L.deleteEdges {old}).Reachable x v) :
    ∃ a b : Fin n, old = s(a, b) ∧ L.Reachable x a ∧ L.Reachable x b := by
  obtain ⟨a, b⟩ := old
  obtain ⟨p⟩ := hv
  have he : s(a, b) ∈ p.edges :=
    p.mem_edges_of_not_reachable_deleteEdges hnot
  refine ⟨a, b, rfl, ?_, ?_⟩
  · exact ⟨p.takeUntil a (p.fst_mem_support_of_mem_edges he)⟩
  · exact ⟨p.takeUntil b (p.snd_mem_support_of_mem_edges he)⟩

/-- In a globally maximal representative, replacing a cross-component host
edge cannot leave the old component connected. Equivalently, the selected edge
of that color cuts the largest component; the stronger `IsBridge` formulation
requires identifying the selected edge inside the induced component. -/
theorem selected_edge_cuts_largest_component (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hmax : GloballyLargestComponent χ r x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : (selectedGraph χ r).Reachable x u)
    (hy : ¬ (selectedGraph χ r).Reachable x y) :
    ∃ v, (selectedGraph χ r).Reachable x v ∧
      ¬ ((selectedGraph χ r).deleteEdges {(r.edge (χ e)).val}).Reachable x v := by
  by_contra h
  push Not at h
  have hlt := replacement_grows_component χ r e x u y he hu hy h
  exact (Nat.not_lt_of_ge (hmax (r.replace e) x)) hlt

/-- Yuan's maximal-component color confinement: a host edge leaving a
globally largest component has the color of a selected bridge edge *inside*
that component. `IsBridge` uses Mathlib's deletion/reachability definition. -/
theorem cross_edge_color_is_component_bridge
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (x : Fin n)
    (hmax : GloballyLargestComponent χ r x)
    (e : HostEdge n) (u y : Fin n) (he : e.val = s(u, y))
    (hu : (selectedGraph χ r).Reachable x u)
    (hy : ¬ (selectedGraph χ r).Reachable x y) :
    ∃ a b : Fin n,
      (r.edge (χ e)).val = s(a, b) ∧
      a ∈ (selectedGraph χ r).connectedComponentMk x ∧
      b ∈ (selectedGraph χ r).connectedComponentMk x ∧
      (selectedGraph χ r).IsBridge s(a, b) := by
  let L := selectedGraph χ r
  let old := (r.edge (χ e)).val
  obtain ⟨v, hv, hnot⟩ :=
    selected_edge_cuts_largest_component χ r x hmax e u y he hu hy
  obtain ⟨a, b, hab, hxa, hxb⟩ :=
    edge_endpoints_reachable_of_delete_disconnects L old hv hnot
  have hbridge : L.IsBridge old := by
    by_contra hnb
    exact hnot (reachable_deleteEdge_of_not_bridge L old hnb hv)
  exact ⟨a, b, hab,
    (SimpleGraph.ConnectedComponent.eq.mpr hxa).symm,
    (SimpleGraph.ConnectedComponent.eq.mpr hxb).symm,
    hab ▸ hbridge⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.AntiRamseyCycleCrossComponentPaletteExclusion

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A same-original-color guarded replacement contains both whole old
components if deleting its actual selected same-color edge preserves old
reachability. The old edge is not assumed to lie in either component. -/
theorem replacement_contains_component_union
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : HostEdge n) (hc : χ e ∈ newColorUnion χ)
    (A B : (selectedGraph χ r).ConnectedComponent) (u v : Fin n)
    (hu : u ∈ A.supp) (hv : v ∈ B.supp) (he : e.val = s(u, v))
    (hdelete : ∀ a b : Fin n, (selectedGraph χ r).Reachable a b →
      ((selectedGraph χ r).deleteEdges
        {(r.edge (⟨χ e, hc⟩ : newColorUnion χ)).val}).Reachable a b) :
    A.supp ∪ B.supp ⊆
      ((selectedGraph χ (r.replace e hc)).connectedComponentMk u).supp := by
  classical
  let G' : SimpleGraph (Fin n) := selectedGraph χ (r.replace e hc)
  have hle := delete_selectedEdge_le_replace χ r e hc
  have hretained : ∀ a b : Fin n, (selectedGraph χ r).Reachable a b →
      G'.Reachable a b := by
    intro a b hab
    exact SimpleGraph.Reachable.mono hle (hdelete a b hab)
  have hnew : G'.Adj u v := by
    have hmem := replacedEdge_mem χ r e hc
    rw [he] at hmem
    exact hmem
  intro x hx
  rcases hx with hx | hx
  · have hux : G'.Reachable u x :=
      hretained u x (A.reachable_of_mem_supp hu hx)
    exact (SimpleGraph.ConnectedComponent.eq.mpr hux).symm
  · have hvx : G'.Reachable v x :=
      hretained v x (B.reachable_of_mem_supp hv hx)
    exact (SimpleGraph.ConnectedComponent.eq.mpr (hnew.reachable.trans hvx)).symm

/-- The containing exchanged component has at least the sum of the two
disjoint whole old component orders. No endpoint of the deleted edge is
localized to A or B. -/
theorem replacement_component_card_ge_sum
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : HostEdge n) (hc : χ e ∈ newColorUnion χ)
    (A B : (selectedGraph χ r).ConnectedComponent)
    (hAB : Disjoint A.supp B.supp) (u v : Fin n)
    (hu : u ∈ A.supp) (hv : v ∈ B.supp) (he : e.val = s(u, v))
    (hdelete : ∀ a b : Fin n, (selectedGraph χ r).Reachable a b →
      ((selectedGraph χ r).deleteEdges
        {(r.edge (⟨χ e, hc⟩ : newColorUnion χ)).val}).Reachable a b) :
    A.supp.ncard + B.supp.ncard ≤
      ((selectedGraph χ (r.replace e hc)).connectedComponentMk u).supp.ncard := by
  have hsub := replacement_contains_component_union χ r e hc A B u v hu hv he hdelete
  calc
    A.supp.ncard + B.supp.ncard = (A.supp ∪ B.supp).ncard :=
      (Set.ncard_union_eq hAB (Set.toFinite _) (Set.toFinite _)).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- Conditional original-host cross colors lie outside the complete selected
NEW palette. The upper-order assumption quantifies over every valid choice
for the SAME original coloring; a bound on only r would not suffice. -/
theorem cross_edge_color_not_new_union_of_retained_reachability
    {k : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hdelete : ∀ c : newColorUnion χ, ∀ a b : Fin n,
      (selectedGraph χ r).Reachable a b →
      ((selectedGraph χ r).deleteEdges {(r.edge c).val}).Reachable a b)
    (hupper : ∀ r' : NewChoice χ, ∀ D : (selectedGraph χ r').ConnectedComponent,
      D.supp.ncard ≤ k - 1)
    (A B : (selectedGraph χ r).ConnectedComponent)
    (hAB : Disjoint A.supp B.supp)
    (hlarge : k + 1 ≤ A.supp.ncard + B.supp.ncard)
    (u v : Fin n) (hu : u ∈ A.supp) (hv : v ∈ B.supp)
    (e : HostEdge n) (he : e.val = s(u, v)) :
    χ e ∉ newColorUnion χ := by
  intro hc
  have hlower := replacement_component_card_ge_sum χ r e hc A B hAB u v hu hv he
    (hdelete (⟨χ e, hc⟩ : newColorUnion χ))
  have hsmall := hupper (r.replace e hc)
    ((selectedGraph χ (r.replace e hc)).connectedComponentMk u)
  omega

/-- The checked generic nonbridge-deletion API supplies the preceding
reachability premise. Downstream Hamiltonicity-to-nonbridge is a separate
obligation; it is not silently assumed proved here. -/
theorem cross_edge_color_not_new_union_of_nonbridge
    {k : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnb : ∀ c : newColorUnion χ,
      ¬ (selectedGraph χ r).IsBridge (r.edge c).val)
    (hupper : ∀ r' : NewChoice χ, ∀ D : (selectedGraph χ r').ConnectedComponent,
      D.supp.ncard ≤ k - 1)
    (A B : (selectedGraph χ r).ConnectedComponent)
    (hAB : Disjoint A.supp B.supp)
    (hlarge : k + 1 ≤ A.supp.ncard + B.supp.ncard)
    (u v : Fin n) (hu : u ∈ A.supp) (hv : v ∈ B.supp)
    (e : HostEdge n) (he : e.val = s(u, v)) :
    χ e ∉ newColorUnion χ := by
  apply cross_edge_color_not_new_union_of_retained_reachability χ r ?_
    hupper A B hAB hlarge u v hu hv e he
  intro c a b hab
  exact ErdosProblems.PathUpperReduction.reachable_deleteEdge_of_not_bridge
    (selectedGraph χ r) (r.edge c).val (hnb c) hab

end ErdosProblems.AntiRamseyCycleCrossComponentPaletteExclusion

namespace ErdosProblems.AntiRamseyCycleHostChainClosing

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges

variable {n : ℕ} {C : Type*}

/-- An arbitrary original-host ordered rainbow chain closes to a literal
rainbow cycle when every chain color differs from the named closing color.
No selected-graph membership or valid NewChoice is assumed. -/
theorem ordered_host_chain_closes_rainbow
    {t : ℕ} (ht : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C)
    (q : Fin (t + 1) → Fin n) (hq : Function.Injective q)
    (chain : Fin t → HostEdge n)
    (hchain : ∀ i : Fin t,
      (chain i).val = s(q (Fin.castSucc i), q (Fin.succ i)))
    (hcolors : Function.Injective (fun i : Fin t => χ (chain i)))
    (closing : HostEdge n)
    (hclosing : closing.val = s(q 0, q (Fin.last t)))
    (hne : ∀ i : Fin t, χ (chain i) ≠ χ closing) :
    ∃ f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let e : Fin (t + 1) ↪ Fin n := ⟨q, hq⟩
  let f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)) :=
    (SimpleGraph.Embedding.completeGraph e).toCopy.comp
      (SimpleGraph.Copy.ofLE (cycleGraph (t + 1))
        (⊤ : SimpleGraph (Fin (t + 1))) le_top)
  have hstep (i : Fin t) :
      (EdgeLabeling.pullback χ f.toHom) (sourceStep i) = χ (chain i) := by
    change χ (f.toHom.mapEdgeSet (sourceStep i)) = χ (chain i)
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map q (sourceStep i).val = (chain i).val
    simp only [sourceStep, Sym2.map_mk, hchain]
  have hclose :
      (EdgeLabeling.pullback χ f.toHom) (sourceClosing t ht) = χ closing := by
    change χ (f.toHom.mapEdgeSet (sourceClosing t ht)) = χ closing
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map q (sourceClosing t ht).val = closing.val
    simp only [sourceClosing, Sym2.map_mk, hclosing]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  rcases sourceEdge_cases ht e₁ with ⟨i, hi⟩ | hi <;>
    rcases sourceEdge_cases ht e₂ with ⟨j, hj⟩ | hj
  · subst e₁
    subst e₂
    have hij : i = j := hcolors (by simpa only [hstep] using heq)
    subst j
    rfl
  · subst e₁
    subst e₂
    exact False.elim (hne i (by simpa only [hstep, hclose] using heq))
  · subst e₁
    subst e₂
    exact False.elim (hne j (by simpa only [hstep, hclose] using heq.symm))
  · subst e₁
    subst e₂
    rfl

end ErdosProblems.AntiRamseyCycleHostChainClosing

namespace ErdosProblems.AntiRamseyTwoSelectedPathsRainbow

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem append_of_lt {α : Type*} {L T : ℕ}
    (A : Fin L → α) (B : Fin T → α) (i : Fin (L + T)) (hi : i.val < L) :
    Fin.append A B i = A ⟨i.val, hi⟩ := by
  have heq : i = Fin.castAdd T (⟨i.val, hi⟩ : Fin L) := Fin.val_injective rfl
  calc
    Fin.append A B i = Fin.append A B (Fin.castAdd T (⟨i.val, hi⟩ : Fin L)) :=
      congrArg (Fin.append A B) heq
    _ = A ⟨i.val, hi⟩ := Fin.append_left A B _

theorem append_of_ge {α : Type*} {L T : ℕ}
    (A : Fin L → α) (B : Fin T → α) (i : Fin (L + T)) (hi : L ≤ i.val) :
    Fin.append A B i = B ⟨i.val - L, by have _h := i.isLt; omega⟩ := by
  have heq : i = Fin.natAdd L (⟨i.val - L, by have h := i.isLt; omega⟩ : Fin T) := by
    apply Fin.val_injective
    change i.val = L + (i.val - L)
    omega
  calc
    Fin.append A B i =
        Fin.append A B (Fin.natAdd L (⟨i.val - L, by have h := i.isLt; omega⟩ : Fin T)) :=
      congrArg (Fin.append A B) heq
    _ = B ⟨i.val - L, by have h := i.isLt; omega⟩ := Fin.append_right A B _

/-- The literal concatenation A followed by B closes to a rainbow host cycle
using the original joining/closing edges and the original χ labeling. -/
theorem two_disjoint_selected_paths_close_rainbow
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    {L T : ℕ} (hL : 2 ≤ L) (hT : 2 ≤ T)
    (A : Fin L → Fin n) (B : Fin T → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hApath : ∀ x y : Fin L, x.val + 1 = y.val →
      (selectedGraph χ r).Adj (A x) (A y))
    (hBpath : ∀ x y : Fin T, x.val + 1 = y.val →
      (selectedGraph χ r).Adj (B x) (B y))
    (between closing : HostEdge n)
    (hbetween : between.val =
      s(A ⟨L - 1, by omega⟩, B ⟨0, by omega⟩))
    (hclosing : closing.val =
      s(A ⟨0, by omega⟩, B ⟨T - 1, by omega⟩))
    (hbetweenOutside : χ between ∉ newColorUnion χ)
    (hclosingOutside : χ closing ∉ newColorUnion χ)
    (hdifferent : χ between ≠ χ closing) :
    ∃ f : (cycleGraph (L + T)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let t : ℕ := L + T - 1
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hcount : t + 1 = L + T := by dsimp [t]; omega
  have happend : Function.Injective (Fin.append A B) :=
    Fin.append_injective_iff.mpr ⟨hA, hB, Set.disjoint_range_iff.mp hdisjoint⟩
  let q : Fin (t + 1) → Fin n :=
    fun i => Fin.append A B ⟨i.val, by have hi := i.isLt; omega⟩
  have hq : Function.Injective q := by
    intro i j hij
    have hpos := happend hij
    apply Fin.val_injective
    exact congrArg (fun i : Fin (L + T) => i.val) hpos
  have hqA (i : Fin (t + 1)) (hi : i.val < L) :
      q i = A ⟨i.val, hi⟩ := by
    exact append_of_lt A B ⟨i.val, by have hi' := i.isLt; omega⟩ hi
  have hqB (i : Fin (t + 1)) (hi : L ≤ i.val) :
      q i = B ⟨i.val - L, by have hi' := i.isLt; omega⟩ := by
    exact append_of_ge A B ⟨i.val, by have hi' := i.isLt; omega⟩ hi
  let chain : Fin t → HostEdge n := fun i =>
    ⟨s(q (Fin.castSucc i), q (Fin.succ i)), by
      apply (SimpleGraph.mem_edgeSet _).mpr
      apply (top_adj _ _).mpr
      intro heq
      have hpos := hq heq
      have hval := congrArg Fin.val hpos
      simp only [Fin.val_castSucc, Fin.val_succ] at hval
      omega⟩
  have hchain (i : Fin t) :
      (chain i).val = s(q (Fin.castSucc i), q (Fin.succ i)) := rfl
  have hchainInj : Function.Injective chain := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    rw [hchain i, hchain j] at hv
    change Sym2.map q (sourceStep i).val = Sym2.map q (sourceStep j).val at hv
    have hsource : sourceStep i = sourceStep j :=
      Subtype.ext (Sym2.map.injective hq hv)
    exact sourceStep_injective hsource

  have hselectedOrBetween (i : Fin t) :
      (chain i).val ∈ (selectedGraph χ r).edgeSet ∨ chain i = between := by
    by_cases hleft : i.val + 1 < L
    · left
      rw [hchain i, hqA (Fin.castSucc i) (by
        change i.val < L
        omega), hqA (Fin.succ i) (by
        change i.val + 1 < L
        exact hleft)]
      apply (SimpleGraph.mem_edgeSet _).mpr
      apply hApath
      change i.val + 1 = i.val + 1
      rfl
    · by_cases hjoin : i.val = L - 1
      · right
        have hleftq : q (Fin.castSucc i) = A ⟨L - 1, by omega⟩ := by
          rw [hqA (Fin.castSucc i) (by change i.val < L; omega)]
          apply congrArg A
          apply Fin.val_injective
          change i.val = L - 1
          exact hjoin
        have hrightq : q (Fin.succ i) = B ⟨0, by omega⟩ := by
          rw [hqB (Fin.succ i) (by change L ≤ i.val + 1; omega)]
          apply congrArg B
          apply Fin.val_injective
          change i.val + 1 - L = 0
          omega
        apply Subtype.ext
        rw [hchain i, hleftq, hrightq, hbetween]
      · left
        have hright : L ≤ i.val := by omega
        rw [hchain i, hqB (Fin.castSucc i) (by
          change L ≤ i.val
          exact hright), hqB (Fin.succ i) (by
          change L ≤ i.val + 1
          omega)]
        apply (SimpleGraph.mem_edgeSet _).mpr
        apply hBpath
        change i.val - L + 1 = i.val + 1 - L
        omega

  have hselectedUnion (e : HostEdge n)
      (he : e.val ∈ (selectedGraph χ r).edgeSet) :
      χ e ∈ newColorUnion χ := by
    rw [selectedGraph_edgeSet χ r] at he
    obtain ⟨c, hc⟩ := he
    have heq : e = r.edge c := Subtype.ext hc.symm
    rw [heq, r.color_eq]
    exact c.property
  have hselectedEq (e₁ e₂ : HostEdge n)
      (he₁ : e₁.val ∈ (selectedGraph χ r).edgeSet)
      (he₂ : e₂.val ∈ (selectedGraph χ r).edgeSet)
      (heq : χ e₁ = χ e₂) : e₁ = e₂ := by
    let s₁ : (selectedGraph χ r).edgeSet := ⟨e₁.val, he₁⟩
    let s₂ : (selectedGraph χ r).edgeSet := ⟨e₂.val, he₂⟩
    have hrestricted : restrictedColor χ r s₁ = restrictedColor χ r s₂ := by
      change χ e₁ = χ e₂
      exact heq
    have hs := restrictedColor_injective χ r hrestricted
    exact Subtype.ext (congrArg (fun e : (selectedGraph χ r).edgeSet => e.val) hs)
  have hcolors : Function.Injective (fun i : Fin t => χ (chain i)) := by
    intro i j heq
    rcases hselectedOrBetween i with hi | hi <;>
      rcases hselectedOrBetween j with hj | hj
    · exact hchainInj (hselectedEq (chain i) (chain j) hi hj heq)
    · have hmem := hselectedUnion (chain i) hi
      have hcolor : χ (chain i) = χ between := heq.trans (congrArg χ hj)
      rw [hcolor] at hmem
      exact False.elim (hbetweenOutside hmem)
    · have hmem := hselectedUnion (chain j) hj
      have hcolor : χ (chain j) = χ between := heq.symm.trans (congrArg χ hi)
      rw [hcolor] at hmem
      exact False.elim (hbetweenOutside hmem)
    · exact hchainInj (hi.trans hj.symm)
  have hne (i : Fin t) : χ (chain i) ≠ χ closing := by
    intro heq
    rcases hselectedOrBetween i with hi | hi
    · have hmem := hselectedUnion (chain i) hi
      rw [heq] at hmem
      exact hclosingOutside hmem
    · exact hdifferent ((congrArg χ hi).symm.trans heq)

  have hqzero : q 0 = A ⟨0, by omega⟩ := by
    exact hqA 0 (by change 0 < L; omega)
  have hqlast : q (Fin.last t) = B ⟨T - 1, by omega⟩ := by
    rw [hqB (Fin.last t) (by change L ≤ t; omega)]
    apply congrArg B
    apply Fin.val_injective
    change t - L = T - 1
    omega
  have hclose : closing.val = s(q 0, q (Fin.last t)) := by
    rw [hqzero, hqlast]
    exact hclosing
  have hresult :=
    ErdosProblems.AntiRamseyCycleHostChainClosing.ordered_host_chain_closes_rainbow
      ht χ q hq chain hchain hcolors closing hclose hne
  exact hcount ▸ hresult

end ErdosProblems.AntiRamseyTwoSelectedPathsRainbow

namespace ErdosProblems.AntiRamseyCycleCyclicCrossMatrixTranslations

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open scoped Fin.CommRing

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The next cyclic index, including the last-to-zero edge. -/
def cyclicSuccessor {a : ℕ} (ha : 0 < a) (x : Fin a) : Fin a :=
  letI : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  x + 1

/-- A cyclic window index in either orientation. -/
def cyclicWindowIndex {a L : ℕ} (ha : 0 < a)
    (i : ℤ) (forward : Bool) (x : Fin L) : Fin a :=
  letI : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  if forward then (i : Fin a) + (x.val : Fin a)
    else (i : Fin a) - (x.val : Fin a)

/-- A literal cyclic window of a given ordered vertex map. -/
def cyclicWindow {a L : ℕ} {α : Type*} (A : Fin a → α)
    (ha : 0 < a) (i : ℤ) (forward : Bool) : Fin L → α :=
  fun x => A (cyclicWindowIndex ha i forward x)

theorem cyclicWindowIndex_injective {a L : ℕ}
    (ha : 0 < a) (hL : L ≤ a) (i : ℤ) (forward : Bool) :
    Function.Injective (cyclicWindowIndex (L := L) ha i forward) := by
  let : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  have hsmall : Function.Injective (fun x : Fin L => (x.val : Fin a)) := by
    intro x y hxy
    apply Fin.val_injective
    have hv := congrArg Fin.val hxy
    rw [Fin.val_natCast, Fin.val_natCast,
      Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt hL),
      Nat.mod_eq_of_lt (lt_of_lt_of_le y.isLt hL)] at hv
    exact hv
  cases forward with
  | false =>
    intro x y hxy
    change (i : Fin a) - (x.val : Fin a) =
      (i : Fin a) - (y.val : Fin a) at hxy
    exact hsmall (sub_right_inj.mp hxy)
  | true =>
    intro x y hxy
    change (i : Fin a) + (x.val : Fin a) =
      (i : Fin a) + (y.val : Fin a) at hxy
    exact hsmall (add_left_cancel hxy)

theorem cyclicWindow_injective {a L : ℕ} {α : Type*}
    (A : Fin a → α) (ha : 0 < a) (hA : Function.Injective A)
    (hL : L ≤ a) (i : ℤ) (forward : Bool) :
    Function.Injective (cyclicWindow (L := L) A ha i forward) :=
  hA.comp (cyclicWindowIndex_injective ha hL i forward)

theorem cyclicWindow_path {a L : ℕ} {α : Type*}
    (G : SimpleGraph α) (A : Fin a → α) (ha : 0 < a)
    (hcycle : ∀ x : Fin a, G.Adj (A x) (A (cyclicSuccessor ha x)))
    (i : ℤ) (forward : Bool) :
    ∀ x y : Fin L, x.val + 1 = y.val →
      G.Adj (cyclicWindow A ha i forward x) (cyclicWindow A ha i forward y) := by
  let : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  intro x y hxy
  have hy : (y.val : Fin a) = (x.val : Fin a) + 1 := by
    rw [← hxy, Nat.cast_add, Nat.cast_one]
  cases forward with
  | false =>
    change G.Adj (A ((i : Fin a) - (x.val : Fin a)))
      (A ((i : Fin a) - (y.val : Fin a)))
    have hindex : (i : Fin a) - (y.val : Fin a) + 1 =
        (i : Fin a) - (x.val : Fin a) := by
      rw [hy]
      abel
    have hs := (hcycle ((i : Fin a) - (y.val : Fin a))).symm
    change G.Adj (A ((i : Fin a) - (y.val : Fin a) + 1))
      (A ((i : Fin a) - (y.val : Fin a))) at hs
    exact hindex ▸ hs
  | true =>
    change G.Adj (A ((i : Fin a) + (x.val : Fin a)))
      (A ((i : Fin a) + (y.val : Fin a)))
    rw [hy, ← add_assoc]
    exact hcycle ((i : Fin a) + (x.val : Fin a))

/-- The actual original complete-host cross edge; disjointness proves it exists. -/
def cyclicCrossEdge {a b : ℕ} (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (x : Fin a) (y : Fin b) : HostEdge n :=
  ⟨s(A x, B y), by
    apply (SimpleGraph.mem_edgeSet _).mpr
    apply (top_adj _ _).mpr
    exact Set.disjoint_range_iff.mp hdisjoint x y⟩

/-- The literal integer lift of the original cross-edge color matrix. -/
def liftedCrossColor {a b : ℕ} (χ : TopEdgeLabeling (Fin n) C)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (ha : 0 < a) (hb : 0 < b)
    (hdisjoint : Disjoint (Set.range A) (Set.range B)) : ℤ → ℤ → C :=
  letI : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  letI : NeZero b := ⟨Nat.ne_zero_of_lt hb⟩
  fun i j => χ (cyclicCrossEdge A B hdisjoint (i : Fin a) (j : Fin b))

omit [DecidableEq C] in
/-- Both exact integer periods of the literal lift. -/
theorem liftedCrossColor_periodic [DecidableEq C] {a b : ℕ} (χ : TopEdgeLabeling (Fin n) C)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (ha : 0 < a) (hb : 0 < b)
    (hdisjoint : Disjoint (Set.range A) (Set.range B)) :
    (∀ i j : ℤ, liftedCrossColor χ A B ha hb hdisjoint (i + a) j =
      liftedCrossColor χ A B ha hb hdisjoint i j) ∧
    (∀ i j : ℤ, liftedCrossColor χ A B ha hb hdisjoint i (j + b) =
      liftedCrossColor χ A B ha hb hdisjoint i j) := by
  let : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  let : NeZero b := ⟨Nat.ne_zero_of_lt hb⟩
  constructor <;> intro i j <;>
    simp only [liftedCrossColor, Int.cast_add, Int.cast_natCast,
      Fin.natCast_self, add_zero]

theorem cyclic_rectangle_cross_colors_eq
    {a b L T : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (ha : 0 < a) (hb : 0 < b)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : ∀ x : Fin a,
      (selectedGraph χ r).Adj (A x) (A (cyclicSuccessor ha x)))
    (hBcycle : ∀ y : Fin b,
      (selectedGraph χ r).Adj (B y) (B (cyclicSuccessor hb y)))
    (hpalette : ∀ x : Fin a, ∀ y : Fin b,
      χ (cyclicCrossEdge A B hdisjoint x y) ∉ newColorUnion χ)
    (hL : 2 ≤ L) (hT : 2 ≤ T) (hLa : L ≤ a) (hTb : T ≤ b)
    (hno : ¬ ∃ f : (cycleGraph (L + T)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ) (i j : ℤ) (forward : Bool) :
    liftedCrossColor χ A B ha hb hdisjoint (i + (L - 1 : ℕ)) j =
      liftedCrossColor χ A B ha hb hdisjoint i
        (j + if forward then ((T - 1 : ℕ) : ℤ) else -((T - 1 : ℕ) : ℤ)) := by
  let : NeZero a := ⟨Nat.ne_zero_of_lt ha⟩
  let : NeZero b := ⟨Nat.ne_zero_of_lt hb⟩
  let AP : Fin L → Fin n := cyclicWindow A ha i true
  let BP : Fin T → Fin n := cyclicWindow B hb j forward
  have hpathsDisjoint : Disjoint (Set.range AP) (Set.range BP) := by
    apply Set.disjoint_range_iff.mpr
    intro x y
    exact Set.disjoint_range_iff.mp hdisjoint
      (cyclicWindowIndex ha i true x) (cyclicWindowIndex hb j forward y)
  let between : HostEdge n := cyclicCrossEdge A B hdisjoint
    ((i + (L - 1 : ℕ) : ℤ) : Fin a) (j : Fin b)
  let closing : HostEdge n := cyclicCrossEdge A B hdisjoint (i : Fin a)
    ((j + if forward then ((T - 1 : ℕ) : ℤ) else -((T - 1 : ℕ) : ℤ) : ℤ) : Fin b)
  have hbetween : between.val =
      s(AP ⟨L - 1, by omega⟩, BP ⟨0, by omega⟩) := by
    change s(A ((i + (L - 1 : ℕ) : ℤ) : Fin a), B (j : Fin b)) =
      s(cyclicWindow A ha i true ⟨L - 1, by omega⟩,
        cyclicWindow B hb j forward ⟨0, by omega⟩)
    cases forward <;>
      simp [cyclicWindow, cyclicWindowIndex]
  have hclosing : closing.val =
      s(AP ⟨0, by omega⟩, BP ⟨T - 1, by omega⟩) := by
    change s(A (i : Fin a),
      B ((j + if forward then ((T - 1 : ℕ) : ℤ) else -((T - 1 : ℕ) : ℤ) : ℤ) : Fin b)) =
      s(cyclicWindow A ha i true ⟨0, by omega⟩,
        cyclicWindow B hb j forward ⟨T - 1, by omega⟩)
    cases forward with
    | false => simp [cyclicWindow, cyclicWindowIndex, sub_eq_add_neg]
    | true => simp [cyclicWindow, cyclicWindowIndex]
  change χ between = χ closing
  by_contra hdifferent
  exact hno
    (ErdosProblems.AntiRamseyTwoSelectedPathsRainbow.two_disjoint_selected_paths_close_rainbow
      χ r hL hT AP BP
      (cyclicWindow_injective A ha hA hLa i true)
      (cyclicWindow_injective B hb hB hTb j forward) hpathsDisjoint
      (cyclicWindow_path (selectedGraph χ r) A ha hAcycle i true)
      (cyclicWindow_path (selectedGraph χ r) B hb hBcycle j forward)
      between closing hbetween hclosing (hpalette _ _) (hpalette _ _) hdifferent)

theorem cyclic_split_translations
    {a b L T : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (ha : 0 < a) (hb : 0 < b)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : ∀ x : Fin a,
      (selectedGraph χ r).Adj (A x) (A (cyclicSuccessor ha x)))
    (hBcycle : ∀ y : Fin b,
      (selectedGraph χ r).Adj (B y) (B (cyclicSuccessor hb y)))
    (hpalette : ∀ x : Fin a, ∀ y : Fin b,
      χ (cyclicCrossEdge A B hdisjoint x y) ∉ newColorUnion χ)
    (hL : 2 ≤ L) (hT : 2 ≤ T) (hLa : L ≤ a) (hTb : T ≤ b)
    (hno : ¬ ∃ f : (cycleGraph (L + T)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ) (i j : ℤ) :
    liftedCrossColor χ A B ha hb hdisjoint i j =
      liftedCrossColor χ A B ha hb hdisjoint
        (i + (L - 1 : ℕ)) (j + (T - 1 : ℕ)) ∧
    liftedCrossColor χ A B ha hb hdisjoint i j =
      liftedCrossColor χ A B ha hb hdisjoint
        (i + (L - 1 : ℕ)) (j - (T - 1 : ℕ)) := by
  have hp := cyclic_rectangle_cross_colors_eq χ r A B ha hb hA hB hdisjoint
    hAcycle hBcycle hpalette hL hT hLa hTb hno i (j + (T - 1 : ℕ)) false
  have hn := cyclic_rectangle_cross_colors_eq χ r A B ha hb hA hB hdisjoint
    hAcycle hBcycle hpalette hL hT hLa hTb hno i (j - (T - 1 : ℕ)) true
  constructor
  · simpa using hp.symm
  · simpa using hn.symm

/-- The four exact adjacent-split translations of the same periodic literal
matrix. No matrix invariance is a premise. -/
theorem cyclic_cross_matrix_has_adjacent_translations
    {k a b : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a ∧ a ≤ k - 1)
    (hb : 3 ≤ b ∧ b ≤ k - 1) (hsum : k + 1 ≤ a + b)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : ∀ x : Fin a,
      (selectedGraph χ r).Adj (A x) (A (cyclicSuccessor (by omega) x)))
    (hBcycle : ∀ y : Fin b,
      (selectedGraph χ r).Adj (B y) (B (cyclicSuccessor (by omega) y)))
    (hpalette : ∀ x : Fin a, ∀ y : Fin b,
      χ (cyclicCrossEdge A B hdisjoint x y) ∉ newColorUnion χ)
    (hno : ¬ ∃ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ) :
    let L : ℕ := max 2 (k - b)
    let d : ℤ := (L : ℤ) - 1
    let e : ℤ := (k : ℤ) - L - 1
    let M : ℤ → ℤ → C := liftedCrossColor χ A B (by omega) (by omega) hdisjoint
    ∀ i j : ℤ,
      M i j = M (i + d) (j + e) ∧
      M i j = M (i + d + 1) (j + e - 1) ∧
      M i j = M (i + d) (j - e) ∧
      M i j = M (i + d + 1) (j - e + 1) := by
  let ha0 : 0 < a := by omega
  let hb0 : 0 < b := by omega
  let L : ℕ := max 2 (k - b)
  let T : ℕ := k - L
  let d : ℤ := (L : ℤ) - 1
  let e : ℤ := (k : ℤ) - L - 1
  let M : ℤ → ℤ → C := liftedCrossColor χ A B ha0 hb0 hdisjoint
  change ∀ i j : ℤ,
    M i j = M (i + d) (j + e) ∧
    M i j = M (i + d + 1) (j + e - 1) ∧
    M i j = M (i + d) (j - e) ∧
    M i j = M (i + d + 1) (j - e + 1)
  have hL : 2 ≤ L := le_max_left _ _
  have hLa : L + 1 ≤ a := by
    have hm : max 2 (k - b) ≤ a - 1 := max_le (by omega) (by omega)
    dsimp only [L]
    omega
  have hLk : L ≤ k - 3 := by
    exact max_le (by omega) (by omega)
  have hLb : k - b ≤ L := le_max_right _ _
  have hT : 3 ≤ T := by dsimp only [T]; omega
  have hTb : T ≤ b := by dsimp only [T]; omega
  have hcount : L + T = k := by dsimp only [T]; omega
  have hcount' : (L + 1) + (T - 1) = k := by omega
  have hno0 : ¬ ∃ f : (cycleGraph (L + T)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by exact hcount.symm ▸ hno
  have hno1 : ¬ ∃ f : (cycleGraph ((L + 1) + (T - 1))).Copy
      (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
    exact hcount'.symm ▸ hno
  have hd0 : ((L - 1 : ℕ) : ℤ) = d := by dsimp only [d]; omega
  have he0 : ((T - 1 : ℕ) : ℤ) = e := by dsimp only [T, e]; omega
  have hd1 : (((L + 1) - 1 : ℕ) : ℤ) = d + 1 := by dsimp only [d]; omega
  have he1 : (((T - 1) - 1 : ℕ) : ℤ) = e - 1 := by dsimp only [T, e]; omega
  intro i j
  have h0 := cyclic_split_translations χ r A B ha0 hb0 hA hB hdisjoint
    hAcycle hBcycle hpalette hL (by omega) (by omega) hTb hno0 i j
  have h1 := cyclic_split_translations (L := L + 1) (T := T - 1)
    χ r A B ha0 hb0 hA hB hdisjoint hAcycle hBcycle hpalette
    (by omega) (by omega) hLa (by omega) hno1 i j
  rw [hd0, he0] at h0
  rw [hd1, he1] at h1
  have hi : i + (d + 1) = i + d + 1 := by omega
  have hjp : j + (e - 1) = j + e - 1 := by omega
  have hjn : j - (e - 1) = j - e + 1 := by omega
  rw [hi, hjp, hjn] at h1
  exact ⟨h0.1, h1.1, h0.2, h1.2⟩

end ErdosProblems.AntiRamseyCycleCyclicCrossMatrixTranslations

namespace ErdosProblems.AntiRamseyCycleNewColors

open SimpleGraph

variable {m : ℕ} {C : Type*} [DecidableEq C]

/-- Pull back a complete-graph coloring while skipping one vertex. -/
def deletedColoring (χ : TopEdgeLabeling (Fin (m + 1)) C)
    (v : Fin (m + 1)) : TopEdgeLabeling (Fin m) C :=
  TopEdgeLabeling.pullback χ v.succAboveEmb

/-- The edges avoiding `v` are exactly the images of the edges of the
complete graph on `Fin m` under the skipped-vertex embedding. -/
theorem avoidingEdges_eq_image (v : Fin (m + 1)) :
    (Finset.univ.filter (fun e : (⊤ : SimpleGraph (Fin (m + 1))).edgeSet =>
      v ∉ e.val)) =
    (Finset.univ : Finset ((⊤ : SimpleGraph (Fin m)).edgeSet)).image
      (SimpleGraph.Embedding.completeGraph v.succAboveEmb).toHom.mapEdgeSet := by
  ext e
  constructor
  · intro he
    have hnot : v ∉ e.val := (Finset.mem_filter.mp he).2
    rcases e with ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | hf a b =>
      have ha : a ≠ v := by
        intro hav
        apply hnot
        rw [← hav]
        exact Sym2.mem_mk_left a b
      have hb : b ≠ v := by
        intro hbv
        apply hnot
        rw [← hbv]
        exact Sym2.mem_mk_right a b
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq ha
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hb
      have hab : a ≠ b := by
        have hadj : (⊤ : SimpleGraph (Fin (m + 1))).Adj a b :=
          (SimpleGraph.mem_edgeSet ⊤).mp hz
        exact (SimpleGraph.top_adj a b).mp hadj
      have hij : i ≠ j := by
        intro h
        apply hab
        calc
          a = v.succAbove i := hi.symm
          _ = v.succAbove j := by rw [h]
          _ = b := hj
      let e' : (⊤ : SimpleGraph (Fin m)).edgeSet :=
        ⟨s(i, j), (SimpleGraph.mem_edgeSet ⊤).mpr
          ((SimpleGraph.top_adj i j).mpr hij)⟩
      apply Finset.mem_image.mpr
      refine ⟨e', Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      change Sym2.map v.succAbove (s(i, j)) = s(a, b)
      simp only [Sym2.map_mk, hi, hj]
  · intro he
    obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change v ∉ Sym2.map v.succAbove e'.val
    induction e'.val using Sym2.inductionOn with
    | hf i j =>
      simp only [Sym2.map_mk, Sym2.mem_iff, not_or]
      exact ⟨Fin.ne_succAbove v i, Fin.ne_succAbove v j⟩

/-- The deletion color set in the recurrence is the realized palette of the
pulled-back complete-graph labeling. -/
theorem colorsAfterDeleting_eq_usedColors_deletedColoring
    (χ : TopEdgeLabeling (Fin (m + 1)) C) (v : Fin (m + 1)) :
    colorsAfterDeleting χ v = usedColors (deletedColoring χ v) := by
  let f : (⊤ : SimpleGraph (Fin (m + 1))).edgeSet → C := χ
  let g : (⊤ : SimpleGraph (Fin m)).edgeSet → C := deletedColoring χ v
  rw [colorsAfterDeleting, avoidingEdges_eq_image]
  change ((Finset.univ : Finset ((⊤ : SimpleGraph (Fin m)).edgeSet)).image
      (SimpleGraph.Embedding.completeGraph v.succAboveEmb).toHom.mapEdgeSet).image f =
    (Finset.univ : Finset ((⊤ : SimpleGraph (Fin m)).edgeSet)).image g
  rw [Finset.image_image]
  rfl

/-- Relabel precisely the colors realized by an edge labeling to a
`Fin p` palette, where `p` is their number. -/
noncomputable def realizedPaletteColoring (ψ : TopEdgeLabeling (Fin m) C) :
    TopEdgeLabeling (Fin m) (Fin (usedColors ψ).card) :=
  fun e => (usedColors ψ).equivFin
    ⟨ψ e, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩

theorem realizedPaletteColoring_surjective (ψ : TopEdgeLabeling (Fin m) C) :
    Function.Surjective (realizedPaletteColoring ψ) := by
  intro i
  let c : usedColors ψ := (usedColors ψ).equivFin.symm i
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp c.property
  refine ⟨e, ?_⟩
  change (usedColors ψ).equivFin ⟨ψ e, _⟩ = i
  rw [← (usedColors ψ).equivFin.apply_symm_apply i]
  apply congrArg (usedColors ψ).equivFin
  apply Subtype.ext
  exact he

/-- Relabeling a restricted coloring by its realized palette preserves
absence of rainbow copies of any graph. -/
theorem noRainbowCopy_realizedPaletteColoring {α : Type*} (H : SimpleGraph α)
    (ψ : TopEdgeLabeling (Fin m) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f.toHom ψ) :
    ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)),
      ¬IsRainbow f.toHom (realizedPaletteColoring ψ) := by
  intro f hr
  apply hno f
  intro e₁ e₂ heq
  apply hr
  change realizedPaletteColoring ψ (f.toHom.mapEdgeSet e₁) =
    realizedPaletteColoring ψ (f.toHom.mapEdgeSet e₂)
  unfold realizedPaletteColoring
  apply congrArg (usedColors ψ).equivFin
  apply Subtype.ext
  exact heq

omit [DecidableEq C] in
/-- A no-rainbow copy on the deletion would compose with the skipped-vertex
embedding to give one in the original complete graph. -/
theorem noRainbowCopy_deletedColoring {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin (m + 1)) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬IsRainbow f.toHom χ) (v : Fin (m + 1)) :
    ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)),
      ¬IsRainbow f.toHom (deletedColoring χ v) := by
  intro f hr
  let g : H.Copy (⊤ : SimpleGraph (Fin (m + 1))) :=
    ((SimpleGraph.Embedding.completeGraph v.succAboveEmb).toCopy).comp f
  apply hno g
  intro e₁ e₂ heq
  apply hr
  have hcolor (e : H.edgeSet) :
      (EdgeLabeling.pullback χ g.toHom) e =
        (EdgeLabeling.pullback (deletedColoring χ v) f.toHom) e := by
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (g : α → Fin (m + 1)) e.val =
      Sym2.map v.succAbove (Sym2.map (f : α → Fin m) e.val)
    rw [Sym2.map_map]
    congr 1
  rw [hcolor e₁, hcolor e₂] at heq
  exact heq

/-- The deletion is an explicit surjective `Fin p` witness with precisely the
number of colors occurring on edges avoiding the removed vertex. -/
theorem deletedPalette_witness {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin (m + 1)) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬IsRainbow f.toHom χ) (v : Fin (m + 1)) :
    ∃ φ : TopEdgeLabeling (Fin m) (Fin (colorsAfterDeleting χ v).card),
      Function.Surjective φ ∧
      ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f.toHom φ := by
  rw [colorsAfterDeleting_eq_usedColors_deletedColoring]
  exact ⟨realizedPaletteColoring (deletedColoring χ v),
    realizedPaletteColoring_surjective (deletedColoring χ v),
    noRainbowCopy_realizedPaletteColoring H (deletedColoring χ v)
      (noRainbowCopy_deletedColoring H χ hno v)⟩

/-- Any no-rainbow complete-graph coloring has at most the Formal Conjectures
anti-Ramsey number many realized colors, without a surjectivity assumption on
its original color type. -/
theorem usedColors_card_le_antiRamseyNum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (ψ : TopEdgeLabeling (Fin m) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f.toHom ψ) :
    (usedColors ψ).card ≤ antiRamseyNum H m := by
  classical
  let A : Set ℕ :=
    {p | ∃ φ : TopEdgeLabeling (Fin m) (Fin p), Function.Surjective φ ∧
      ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f.toHom φ}
  have hbounded : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin m)).edgeSet), ?_⟩
    intro p hp
    obtain ⟨φ, hφ, _⟩ := hp
    simpa using Fintype.card_le_of_surjective φ hφ
  have hmem : (usedColors ψ).card ∈ A :=
    ⟨realizedPaletteColoring ψ, realizedPaletteColoring_surjective ψ,
      noRainbowCopy_realizedPaletteColoring H ψ hno⟩
  change (usedColors ψ).card ≤ sSup A
  exact le_csSup hbounded hmem

/-- Exact deletion colors are bounded by the anti-Ramsey number on one fewer
vertex. This is the low-new-color induction interface for any finite graph. -/
theorem colorsAfterDeleting_card_le_antiRamseyNum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (χ : TopEdgeLabeling (Fin (m + 1)) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬IsRainbow f.toHom χ) (v : Fin (m + 1)) :
    (colorsAfterDeleting χ v).card ≤ antiRamseyNum H m := by
  rw [colorsAfterDeleting_eq_usedColors_deletedColoring]
  exact usedColors_card_le_antiRamseyNum H (deletedColoring χ v)
    (noRainbowCopy_deletedColoring H χ hno v)

/-- The exact new-color recurrence and deletion witness give the numerical
induction inequality. A bound on the new-color term is a separate input. -/
theorem surjective_color_count_le_antiRamseyNum_add_newColors
    {α : Type*} [Fintype α] {q : ℕ}
    (H : SimpleGraph α) (χ : TopEdgeLabeling (Fin (m + 1)) (Fin q))
    (hχ : Function.Surjective χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬IsRainbow f.toHom χ) (v : Fin (m + 1)) :
    q ≤ antiRamseyNum H m + (newColors χ v).card := by
  calc
    q = (colorsAfterDeleting χ v).card + (newColors χ v).card :=
      surjective_color_count_delete_add_new χ hχ v
    _ ≤ antiRamseyNum H m + (newColors χ v).card :=
      Nat.add_le_add_right
        (colorsAfterDeleting_card_le_antiRamseyNum H χ hno v)
        (newColors χ v).card

end ErdosProblems.AntiRamseyCycleNewColors

namespace ErdosProblems.AntiRamseyEvenCheckerboardDegree

open scoped Classical

/-- In an even finite index set, if every graph edge has opposite endpoint
parities, quotient by two injects each neighbor set into `Fin (a / 2)`.
The statement uses arbitrary `G`; its adjacency is decided classically. -/
theorem degree_le_half_of_no_same_parity_edge
    {a : ℕ} (ha : Even a) (G : SimpleGraph (Fin a))
    (hno : ∀ x y : Fin a, G.Adj x y → x.val % 2 ≠ y.val % 2)
    (x : Fin a) : G.degree x ≤ a / 2 := by
  let f : G.neighborSet x → Fin (a / 2) := fun j =>
    ⟨j.val.val / 2, by
      have hjlt : j.val.val < a := j.val.isLt
      have haMod : a % 2 = 0 := Nat.even_iff.mp ha
      omega⟩
  have hinj : Function.Injective f := by
    intro j l h
    have hquot : j.val.val / 2 = l.val.val / 2 := congrArg Fin.val h
    have hjParity : x.val % 2 ≠ j.val.val % 2 := hno x j.val j.property
    have hlParity : x.val % 2 ≠ l.val.val % 2 := hno x l.val l.property
    have hval : j.val.val = l.val.val := by omega
    exact Subtype.ext (Fin.ext hval)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_fin] using hcard

/-- The exact cross-pair degree lower bound rules out opposite-parity-only
edges in both even graphs whose orders are at most `k - 1`, for even `k`.
The output is an actual adjacent same-parity pair in one supplied graph. -/
theorem exists_same_parity_edge_of_cross_degree_sum
    {k a b : ℕ} (hk : 5 ≤ k) (hkEven : Even k)
    (ha : 3 ≤ a) (haEven : Even a) (haUpper : a ≤ k - 1)
    (hb : 3 ≤ b) (hbEven : Even b) (hbUpper : b ≤ k - 1)
    (GA : SimpleGraph (Fin a)) (GB : SimpleGraph (Fin b))
    (hpair : ∀ x : Fin a, ∀ y : Fin b,
      k - 1 ≤ GA.degree x + GB.degree y) :
    (∃ x y : Fin a, GA.Adj x y ∧ x.val % 2 = y.val % 2) ∨
      (∃ x y : Fin b, GB.Adj x y ∧ x.val % 2 = y.val % 2) := by
  by_contra hnone
  have hnoA : ∀ x y : Fin a, GA.Adj x y → x.val % 2 ≠ y.val % 2 := by
    intro x y hxy hpar
    exact hnone (Or.inl ⟨x, y, hxy, hpar⟩)
  have hnoB : ∀ x y : Fin b, GB.Adj x y → x.val % 2 ≠ y.val % 2 := by
    intro x y hxy hpar
    exact hnone (Or.inr ⟨x, y, hxy, hpar⟩)
  let x0 : Fin a := ⟨0, by omega⟩
  let y0 : Fin b := ⟨0, by omega⟩
  have hdegreeA : GA.degree x0 ≤ a / 2 :=
    degree_le_half_of_no_same_parity_edge haEven GA hnoA x0
  have hdegreeB : GB.degree y0 ≤ b / 2 :=
    degree_le_half_of_no_same_parity_edge hbEven GB hnoB y0
  have hkMod : k % 2 = 0 := Nat.even_iff.mp hkEven
  have haMod : a % 2 = 0 := Nat.even_iff.mp haEven
  have hbMod : b % 2 = 0 := Nat.even_iff.mp hbEven
  have haStrict : a ≤ k - 2 := by omega
  have hbStrict : b ≤ k - 2 := by omega
  have hsumUpper : GA.degree x0 + GB.degree y0 ≤ k - 2 := by omega
  have hsumLower := hpair x0 y0
  omega

end ErdosProblems.AntiRamseyEvenCheckerboardDegree

namespace ErdosProblems.AntiRamseyEvenChordRotation

open SimpleGraph

def cyclicRotation {a : ℕ} (x : Fin a) : Fin a → Fin a := fun i => x + i

def chordOffset {a : ℕ} (x y : Fin a) : Fin a := y - x

/-- The literal cyclic rotation sends zero to x and the positive even chord
offset to y, preserves numeric cycleGraph adjacency, and pulls the original
edge back to an actual normalized chord. The explicit zero Fin record keeps
the statement free of an additional NeZero instance assumption. -/
theorem normalized_even_chord_rotation
    {a : ℕ} (ha : 3 ≤ a) (haEven : Even a)
    (G : SimpleGraph (Fin a)) (x y : Fin a)
    (hxy : G.Adj x y) (hparity : x.val % 2 = y.val % 2) :
    Function.Injective (cyclicRotation x) ∧
      cyclicRotation x (⟨0, by omega⟩ : Fin a) = x ∧
      cyclicRotation x (chordOffset x y) = y ∧
      Even (chordOffset x y).val ∧
      2 ≤ (chordOffset x y).val ∧
      (chordOffset x y).val + 2 ≤ a ∧
      (G.comap (cyclicRotation x)).Adj
        (⟨0, by omega⟩ : Fin a) (chordOffset x y) ∧
      (∀ i j : Fin a,
        (cycleGraph a).Adj (cyclicRotation x i) (cyclicRotation x j) ↔
          (cycleGraph a).Adj i j) := by
  let : NeZero a := ⟨by omega⟩
  have hinj : Function.Injective (cyclicRotation x) := add_right_injective x
  have hzero : cyclicRotation x (⟨0, by omega⟩ : Fin a) = x := by
    change x + (0 : Fin a) = x
    exact add_zero x
  have hendpoint : cyclicRotation x (chordOffset x y) = y := by
    change x + (y - x) = y
    exact add_sub_cancel x y
  have hdne : chordOffset x y ≠ (0 : Fin a) := by
    intro hd0
    change y - x = 0 at hd0
    exact hxy.ne (sub_eq_zero.mp hd0).symm
  have hdpos : 0 < (chordOffset x y).val := by
    by_contra hnot
    have hdval : (chordOffset x y).val = 0 := by omega
    have hd0 : chordOffset x y = (0 : Fin a) :=
      Fin.ext (by simpa only [Fin.val_zero] using hdval)
    exact hdne hd0
  have haMod : a % 2 = 0 := Nat.even_iff.mp haEven
  have hdMod : (chordOffset x y).val % 2 = 0 := by
    dsimp only [chordOffset]
    by_cases hle : x ≤ y
    · have hsub : (y - x).val = y.val - x.val := Fin.sub_val_of_le hle
      have hleval : x.val ≤ y.val := hle
      rw [hsub]
      omega
    · have hlt : y < x := lt_of_not_ge hle
      have hltval : y.val < x.val := hlt
      have hsub : (y - x).val = a + y.val - x.val :=
        Fin.coe_sub_iff_lt.mpr hlt
      have hxlt : x.val < a := x.isLt
      rw [hsub]
      omega
  have hdlt : (chordOffset x y).val < a := (chordOffset x y).isLt
  have hdLower : 2 ≤ (chordOffset x y).val := by omega
  have hdUpper : (chordOffset x y).val + 2 ≤ a := by omega
  have hchord : (G.comap (cyclicRotation x)).Adj
      (⟨0, by omega⟩ : Fin a) (chordOffset x y) := by
    rw [SimpleGraph.comap_adj, hzero, hendpoint]
    exact hxy
  have hcycle (i j : Fin a) :
      (cycleGraph a).Adj (cyclicRotation x i) (cyclicRotation x j) ↔
        (cycleGraph a).Adj i j := by
    dsimp only [cyclicRotation]
    rw [cycleGraph_adj', cycleGraph_adj']
    simp only [add_sub_add_left_eq_sub]
  exact ⟨hinj, hzero, hendpoint, Nat.even_iff.mpr hdMod, hdLower, hdUpper,
    hchord, hcycle⟩

end ErdosProblems.AntiRamseyEvenChordRotation

namespace ErdosProblems.AntiRamseyCycleHeadNewDominance

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A NEW deficit at the head of this selected tail would create an
inward NEW attachment and hence a literal rainbow original-host C_(m+3).
No shorter-cycle exclusion, pair sum or component hypothesis is assumed. -/
theorem no_head_new_deficit_of_inward_tail
    {m : ℕ} (hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    (newColors χ (p 0)).card ≤
      ((selectedGraph χ r).neighborFinset (p 0) ∩ Finset.univ.image p).card := by
  classical
  by_contra hnot
  have hsmall :
      ((selectedGraph χ r).neighborFinset (p 0) ∩ Finset.univ.image p).card <
        (newColors χ (p 0)).card := by
    omega
  obtain ⟨u, e, hu, hselected, he, hnew⟩ :=
    ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness.exists_selected_newColor_edge_outside
      χ r (p 0) (Finset.univ.image p) hsmall
  have huRange : u ∉ Set.range p := by
    rintro ⟨i, hi⟩
    exact hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  have heSelected : e.val ∈ (selectedGraph χ r).edgeSet := by
    rw [he]
    exact hselected
  let attachment : (selectedGraph χ r).edgeSet := ⟨e.val, heSelected⟩
  have hattachment : attachment.val = s(u, p 0) := by
    change e.val = s(u, p 0)
    rw [he]
    exact Sym2.eq_swap
  have hcolor : restrictedColor χ r attachment = χ e := rfl
  have hnewFirst : restrictedColor χ r attachment ∈ newColors χ (p 0) := by
    rw [hcolor]
    exact hnew
  obtain ⟨f, hf⟩ :=
    ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion.inward_oriented_path_insertion_rainbow
      hm χ r p hp hpath u huRange attachment hattachment hnewFirst hnewLast
  exact hno f hf

end ErdosProblems.AntiRamseyCycleHeadNewDominance

namespace ErdosProblems.AntiRamseyCycleLiteralSnoc

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Append the named outside NEW edge to the literal selected ordered path.
The value of the terminal selected edge, its original host color and its
inner endpoint are retained for a later suffix alignment. -/
theorem literal_snoc_with_new_terminal
    {t : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (hstep : ∀ i : Fin t,
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (t + 1), p i ∈ D)
    (w : Fin n) (hw : w ∉ Set.range p) (hwD : w ∈ D)
    (e : HostEdge n)
    (hadj : (selectedGraph χ r).Adj (p (Fin.last t)) w)
    (he : e.val = s(p (Fin.last t), w))
    (hnew : χ e ∈ newColors χ (p (Fin.last t))) :
    let R : Fin (t + 2) → Fin n := Fin.snoc p w
    ∃ hRpath : ∀ i : Fin (t + 1),
      (selectedGraph χ r).Adj (R (Fin.castSucc i)) (R (Fin.succ i)),
      Function.Injective R ∧
      (∀ i : Fin (t + 2), R i ∈ D) ∧
      (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
        hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet).val = e.val ∧
      restrictedColor χ r
        (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
          hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) = χ e ∧
      R (Fin.castSucc (Fin.last t)) = p (Fin.last t) ∧
      restrictedColor χ r
        (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
          hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) ∈
        newColors χ (R (Fin.castSucc (Fin.last t))) := by
  classical
  dsimp only
  let R : Fin (t + 2) → Fin n := Fin.snoc p w
  have hR : Function.Injective R := Fin.snoc_injective_of_injective hp hw
  have hRD : ∀ i : Fin (t + 2), R i ∈ D := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [R, Fin.snoc_last] using hwD
    | cast j => simpa only [R, Fin.snoc_castSucc] using hpD j
  have hRpath : ∀ i : Fin (t + 1),
      (selectedGraph χ r).Adj (R (Fin.castSucc i)) (R (Fin.succ i)) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simpa only [R, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using hadj
    | cast j =>
      simpa only [R, Fin.succ_castSucc, Fin.snoc_castSucc] using hstep j
  have hval :
      (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
        hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet).val = e.val := by
    simpa only [R, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using he.symm
  have hcolor : restrictedColor χ r
      (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
        hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) = χ e := by
    change χ ⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
      SimpleGraph.edgeSet_mono
        (show selectedGraph χ r ≤ (⊤ : SimpleGraph (Fin n)) from le_top)
        (hRpath (Fin.last t))⟩ = χ e
    apply congrArg χ
    exact Subtype.ext hval
  have hinner : R (Fin.castSucc (Fin.last t)) = p (Fin.last t) := by
    simp only [R, Fin.snoc_castSucc]
  refine ⟨hRpath, hR, hRD, hval, hcolor, hinner, ?_⟩
  rw [hcolor]
  simpa only [Fin.snoc_castSucc] using hnew

end ErdosProblems.AntiRamseyCycleLiteralSnoc

namespace ErdosProblems.AntiRamseyCycleMaximumPathLocalFree

open SimpleGraph

/-- In a larger connected graph, the image of a maximum-length path cannot
contain a cycle spanning all of its vertices. -/
theorem maximum_path_cycle_free_on_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (u v : V) (p : H.Walk u v) (hp : p.IsPath)
    (hmax : ∀ (a b : V) (w : H.Walk a b),
      w.IsPath → w.length ≤ p.length)
    (hlen : 2 ≤ p.length)
    (hlarge : p.length + 1 < Fintype.card V) :
    (cycleGraph (p.length + 1)).Free
      (H.comap (fun i : Fin (p.length + 1) => p.getVert i.val)) := by
  classical
  let q : Fin (p.length + 1) → V := fun i => p.getVert i.val
  have hq : Function.Injective q := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (by exact Nat.le_of_lt_succ i.isLt)
      (by exact Nat.le_of_lt_succ j.isLt) hij
  have hq_not_surjective : ¬Function.Surjective q := by
    intro hsurj
    have hcard : Fintype.card V ≤ p.length + 1 := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective q hsurj
    exact (Nat.not_le_of_gt hlarge) hcard
  obtain ⟨z, hz⟩ := not_forall.mp hq_not_surjective
  have hzrange : z ∉ Set.range q := hz
  intro hcontained
  obtain ⟨a, c, hc, hclength⟩ :=
    (cycleGraph_isContained_iff (by omega : 2 < p.length + 1)).mp hcontained
  have hham : c.IsHamiltonianCycle :=
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨hc, by simpa only [Fintype.card_fin] using hclength⟩
  let f : H.comap q →g H := SimpleGraph.Hom.comap q H
  have hf : Function.Injective f := by
    change Function.Injective q
    exact hq
  let cc : H.Walk (q a) (q a) := c.map f
  have hcc : cc.IsCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).mpr hc
  have hcclength : cc.length = p.length + 1 := by
    exact (SimpleGraph.Walk.length_map f c).trans hclength
  have hsupport (x : V) : x ∈ cc.support ↔ x ∈ Set.range q := by
    change x ∈ (c.map f).support ↔ x ∈ Set.range q
    rw [SimpleGraph.Walk.support_map]
    constructor
    · intro hx
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
      exact ⟨i, hi⟩
    · rintro ⟨i, rfl⟩
      exact List.mem_map.mpr ⟨i, hham.mem_support i, rfl⟩
  obtain ⟨w⟩ := hconn (q a) z
  obtain ⟨d, _, hdinside, hdoutside⟩ :=
    w.exists_boundary_dart (Set.range q) ⟨a, rfl⟩ hzrange
  have hdmem : d.fst ∈ cc.support := (hsupport d.fst).mpr hdinside
  let rot : H.Walk d.fst d.fst := cc.rotate d.fst hdmem
  have hrot : rot.IsCycle := hcc.rotate hdmem
  have hdnot_dropLast : d.snd ∉ rot.dropLast.support := by
    intro hd
    rw [rot.support_dropLast hrot.not_nil] at hd
    have hdrot : d.snd ∈ rot.support := List.mem_of_mem_dropLast hd
    have hdcc : d.snd ∈ cc.support :=
      (cc.mem_support_rotate_iff d.fst hdmem).mp hdrot
    exact hdoutside ((hsupport d.snd).mp hdcc)
  let longer := SimpleGraph.Walk.cons d.adj.symm rot.dropLast
  have hlonger : longer.IsPath := hrot.isPath_dropLast.cons hdnot_dropLast
  have hlonger_length : longer.length = p.length + 1 := by
    change rot.dropLast.length + 1 = p.length + 1
    calc
      rot.dropLast.length + 1 = rot.length :=
        SimpleGraph.Walk.length_dropLast_add_one hrot.not_nil
      _ = cc.length := SimpleGraph.Walk.length_rotate cc d.fst hdmem
      _ = p.length + 1 := hcclength
  have hbound := hmax _ _ longer hlonger
  rw [hlonger_length] at hbound
  omega

end ErdosProblems.AntiRamseyCycleMaximumPathLocalFree

namespace ErdosProblems.AntiRamseyCycleOmittedSelectedEdgeClosing

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- An omitted selected edge with the closing color makes every edge of the
literal closed ordered path distinct. The cycle has k=t+1>=3 vertices. -/
theorem omitted_selected_edge_closing_rainbow {t : ℕ} (ht : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (q : Fin (t + 1) → Fin n) (hq : Function.Injective q)
    (hpath : ∀ i : Fin t,
      (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)))
    (e0 : (selectedGraph χ r).edgeSet)
    (homit : ∀ i : Fin t,
      s(q (Fin.castSucc i), q (Fin.succ i)) ≠ e0.val)
    (closing : HostEdge n)
    (hclosing : closing.val = s(q 0, q (Fin.last t)))
    (hcolor : χ closing = restrictedColor χ r e0) :
    ∃ f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let chain : Fin t → (selectedGraph χ r).edgeSet :=
    fun i => ⟨s(q (Fin.castSucc i), q (Fin.succ i)), hpath i⟩
  apply ordered_selected_chain_closes_rainbow ht χ r q hq chain
    (fun _ => rfl) closing hclosing
  intro i hsameColor
  exact homit i (congrArg Subtype.val
    (restrictedColor_injective χ r (hsameColor.trans hcolor)))

end ErdosProblems.AntiRamseyCycleOmittedSelectedEdgeClosing

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

namespace ErdosProblems.AntiRamseyCyclePartialSpliceClosing

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCyclePartialSpliceMap
open ErdosProblems.AntiRamseyCycleOmittedSelectedEdgeClosing

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The exact interval reversal omits the first selected edge; its color
therefore closes the reordered path into a rainbow original-host cycle. -/
theorem supplied_skips_and_first_closing_color_rainbow
    {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (R : Fin (m + 3) → Fin n) (hR : Function.Injective R)
    (hpath : ∀ x y : Fin (m + 3), x.val + 1 = y.val →
      (selectedGraph χ r).Adj (R x) (R y))
    (a : Fin (m + 3)) (ha2 : 2 ≤ a.val) (ham : a.val ≤ m)
    (hleft : (selectedGraph χ r).Adj (R 0) (R a))
    (hright : (selectedGraph χ r).Adj
      (R ⟨1, by omega⟩) (R ⟨a.val + 1, by omega⟩))
    (e0 : (selectedGraph χ r).edgeSet)
    (he0 : e0.val = s(R 0, R ⟨1, by omega⟩))
    (closing : HostEdge n)
    (hclosing : closing.val = s(R 0, R (Fin.last (m + 2))))
    (hcolor : χ closing = restrictedColor χ r e0) :
    ∃ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let q : Fin (m + 3) → Fin n := fun i => R (partialReverse a i)
  have hq : Function.Injective q := hR.comp (partialReverse_injective a)
  have hqpath : ∀ i : Fin (m + 2),
      (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)) :=
    partial_splice_ordered_path (selectedGraph χ r) R hpath a ha2 ham hleft hright
  have homit : ∀ i : Fin (m + 2),
      s(q (Fin.castSucc i), q (Fin.succ i)) ≠ e0.val := by
    intro i
    rw [he0]
    exact partial_splice_omits_first_edge R hR a ha2 i
  have hclosingq : closing.val = s(q 0, q (Fin.last (m + 2))) := by
    simpa only [q, partialReverse_zero, partialReverse_last a ham] using hclosing
  exact omitted_selected_edge_closing_rainbow (by omega) χ r q hq hqpath
    e0 homit closing hclosingq hcolor

end ErdosProblems.AntiRamseyCyclePartialSpliceClosing
