module

public import PathUpperSpanningDegreeSlots
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
This is a connected ordinary graph auxiliary on the SAME Fin k, with no coloring
or universal anti-Ramsey conclusion. Its private arithmetic reuses the guarded
choose/Int-cast route from EvenSpanningDegreeSlotNumerical, whose even-order
domain does not cover the present arbitrary k >= 11.
-/

namespace ErdosProblems.PathUpperReduction

theorem degree_slot_cap_lt_spanning_threshold
    (k a : ℕ) (hk : 11 ≤ k) (ha : 1 ≤ a) (haStrict : 2 ≤ a)
    (haBound : 2 * a ≤ k - 2) :
    (k - 1 - a).choose 2 + a * (a + 1) < (k - 2).choose 2 + 2 := by
  let T := (k - 2).choose 2 + 2
  let h := (k - 1 - a).choose 2 + a * (a + 1)
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  have ha1 : a ≤ k - 1 := by omega
  have ha2 : a ≤ k - 2 := by omega
  have h3a : 3 * a ≤ 2 * k := by omega
  have h8 : 8 ≤ 2 * k - 3 * a := by omega
  have hfactor : 1 ≤ 2 * k - 3 * a - 8 := by omega
  have hshiftT : k - 3 + 1 = k - 2 := by omega
  have hshiftH : k - 2 - a + 1 = k - 1 - a := by omega
  have hchooseT :
      (k - 2) * (k - 3) = (k - 2).choose 2 * 2 := by
    simpa only [Nat.choose_one_right, hshiftT] using
      Nat.add_one_mul_choose_eq (k - 3) 1
  have hchooseH :
      (k - 1 - a) * (k - 2 - a) = (k - 1 - a).choose 2 * 2 := by
    simpa only [Nat.choose_one_right, hshiftH] using
      Nat.add_one_mul_choose_eq (k - 2 - a) 1
  have hcastT : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 :=
    Nat.cast_sub hk2
  have hcastTpred : ((k - 3 : ℕ) : ℤ) = (k : ℤ) - 3 :=
    Nat.cast_sub hk3
  have hcastH : ((k - 1 - a : ℕ) : ℤ) = (k : ℤ) - 1 - (a : ℤ) := by
    simp only [Nat.cast_sub ha1, Nat.cast_sub hk1, Nat.cast_one]
  have hcastHpred : ((k - 2 - a : ℕ) : ℤ) = (k : ℤ) - 2 - (a : ℤ) := by
    simp only [Nat.cast_sub ha2, Nat.cast_sub hk2, Nat.cast_ofNat]
  have hcastA : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 :=
    Nat.cast_sub ha
  have hcastFactor :
      ((2 * k - 3 * a - 8 : ℕ) : ℤ) =
        2 * (k : ℤ) - 3 * (a : ℤ) - 8 := by
    simp only [Nat.cast_sub h8, Nat.cast_sub h3a, Nat.cast_mul,
      Nat.cast_ofNat]
  have hcT :
      ((k - 2 : ℕ) : ℤ) * ((k - 3 : ℕ) : ℤ) =
        ((k - 2).choose 2 : ℤ) * 2 := by
    exact_mod_cast hchooseT
  have hcH :
      ((k - 1 - a : ℕ) : ℤ) * ((k - 2 - a : ℕ) : ℤ) =
        ((k - 1 - a).choose 2 : ℤ) * 2 := by
    exact_mod_cast hchooseH
  rw [hcastT, hcastTpred] at hcT
  rw [hcastH, hcastHpred] at hcH
  have hidentityInt :
      2 * (T : ℤ) = 2 * (h : ℤ) +
        (((a - 1) * (2 * k - 3 * a - 8) : ℕ) : ℤ) := by
    dsimp only [T, h]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, hcastA, hcastFactor]
    nlinarith [hcT, hcH]
  have hidentity :
      2 * T = 2 * h + (a - 1) * (2 * k - 3 * a - 8) := by
    exact_mod_cast hidentityInt
  have hgap : 0 < (a - 1) * (2 * k - 3 * a - 8) :=
    Nat.mul_pos (by omega) (by omega)
  change h < T
  omega

/-- A connected dense spanning graph satisfying the missing-pair degree closure
is complete at every order at least11, with minimum degree at least2. -/
theorem connected_spanning_dense_closed_eq_top
    (k : ℕ) (hk : 11 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected) (hmin : ∀ v, 2 ≤ H.degree v)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2)
    (hedges : (k - 2).choose 2 + 2 ≤ H.edgeFinset.card) : H = ⊤ := by
  classical
  by_contra hneTop
  obtain ⟨a, L, ha, haBound, hLcard, hLdeg, hcount⟩ :=
    spanning_degree_slots_and_edge_count k (by omega) H hconn hneTop hclosure
  have hLnonempty : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hLnonempty
  have haStrict : 2 ≤ a := (hmin x).trans (hLdeg x hx)
  have hstrict := degree_slot_cap_lt_spanning_threshold k a hk ha haStrict haBound
  exact (not_lt_of_ge (hedges.trans hcount)) hstrict

end ErdosProblems.PathUpperReduction

