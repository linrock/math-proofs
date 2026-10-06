module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
This is the scalar
endpoint reduction for the actual core-count theorem, with its original
natural subtraction and division. It proves no graph or coloring statement.
-/

namespace ErdosProblems.PathUpperReduction.CoreEndpointBound1105

def extremalCount (N K a : ℕ) : ℕ :=
  (K - a).choose 2 + a * (N - K + a)

theorem extremalCount_cast (N K a : ℕ) (haK : a ≤ K) (hKN : K ≤ N) :
    2 * (extremalCount N K a : ℚ) =
      3 * (a : ℚ) ^ 2 + (2 * (N : ℚ) - 4 * (K : ℚ) + 1) * (a : ℚ) +
        (K : ℚ) ^ 2 - (K : ℚ) := by
  simp only [extremalCount, Nat.cast_add, Nat.cast_mul,
    Nat.cast_choose_two, Nat.cast_sub haK, Nat.cast_sub hKN]
  ring

theorem extremalCount_endpoints (N K a : ℕ) (hK : 5 ≤ K) (hKN : K ≤ N)
    (ha : 2 ≤ a) (hat : a ≤ (K - 1) / 2) :
    extremalCount N K a ≤
      max (extremalCount N K 2) (extremalCount N K ((K - 1) / 2)) := by
  let t : ℕ := (K - 1) / 2
  have ht2 : 2 ≤ t := by dsimp [t]; omega
  have htK : t ≤ K := by dsimp [t]; omega
  have hat' : a ≤ t := hat
  have haK : a ≤ K := le_trans hat' htK
  have h2K : 2 ≤ K := by omega
  by_cases haeq : a = 2
  · subst a
    exact le_max_left _ _
  have hlt : 2 < t := by omega
  have haq : (2 : ℚ) ≤ (a : ℚ) := Nat.cast_le.mpr ha
  have htaq : (a : ℚ) ≤ (t : ℚ) := Nat.cast_le.mpr hat'
  have htq : (2 : ℚ) < (t : ℚ) := Nat.cast_lt.mpr hlt
  have hw₁ : 0 ≤ (t : ℚ) - (a : ℚ) := sub_nonneg.mpr htaq
  have hw₂ : 0 ≤ (a : ℚ) - 2 := sub_nonneg.mpr haq
  have hw : 0 < (t : ℚ) - 2 := sub_pos.mpr htq
  have hpoly₂ := extremalCount_cast N K 2 h2K hKN
  have hpoly_t := extremalCount_cast N K t htK hKN
  have hpoly_a := extremalCount_cast N K a haK hKN
  have hchord :
      ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount N K 2 : ℚ)) +
          ((a : ℚ) - 2) * (2 * (extremalCount N K t : ℚ)) -
          ((t : ℚ) - 2) * (2 * (extremalCount N K a : ℚ)) =
        3 * ((t : ℚ) - 2) * ((a : ℚ) - 2) * ((t : ℚ) - (a : ℚ)) := by
    rw [hpoly₂, hpoly_t, hpoly_a]
    ring
  have hproduct :
      0 ≤ 3 * ((t : ℚ) - 2) * ((a : ℚ) - 2) * ((t : ℚ) - (a : ℚ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hw)) hw₂) hw₁
  have hinterp :
      ((t : ℚ) - 2) * (2 * (extremalCount N K a : ℚ)) ≤
        ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount N K 2 : ℚ)) +
          ((a : ℚ) - 2) * (2 * (extremalCount N K t : ℚ)) := by
    linarith [hchord, hproduct]
  let M : ℕ := max (extremalCount N K 2) (extremalCount N K t)
  have h₂M : (extremalCount N K 2 : ℚ) ≤ (M : ℚ) :=
    Nat.cast_le.mpr (le_max_left _ _)
  have htM : (extremalCount N K t : ℚ) ≤ (M : ℚ) :=
    Nat.cast_le.mpr (le_max_right _ _)
  have h₂M' : 2 * (extremalCount N K 2 : ℚ) ≤ 2 * (M : ℚ) := by linarith
  have htM' : 2 * (extremalCount N K t : ℚ) ≤ 2 * (M : ℚ) := by linarith
  have hweighted :
      ((t : ℚ) - (a : ℚ)) * (2 * (extremalCount N K 2 : ℚ)) +
          ((a : ℚ) - 2) * (2 * (extremalCount N K t : ℚ)) ≤
        ((t : ℚ) - 2) * (2 * (M : ℚ)) := by
    calc
      _ ≤ ((t : ℚ) - (a : ℚ)) * (2 * (M : ℚ)) +
          ((a : ℚ) - 2) * (2 * (M : ℚ)) :=
        add_le_add (mul_le_mul_of_nonneg_left h₂M' hw₁)
          (mul_le_mul_of_nonneg_left htM' hw₂)
      _ = _ := by ring
  have htwice : 2 * (extremalCount N K a : ℚ) ≤ 2 * (M : ℚ) :=
    le_of_mul_le_mul_left (le_trans hinterp hweighted) hw
  have hq : (extremalCount N K a : ℚ) ≤ (M : ℚ) := by linarith
  exact Nat.cast_le.mp hq

theorem emptyCoreCount_le_endpoint (N K : ℕ) (hK : 5 ≤ K) (hKN : K ≤ N) :
    ((K - 1) / 2).choose 2 + ((K - 1) / 2) * (N - (K - 1) / 2) ≤
      extremalCount N K ((K - 1) / 2) := by
  let t : ℕ := (K - 1) / 2
  have htK : t ≤ K := by dsimp [t]; omega
  have htN : t ≤ N := le_trans htK hKN
  have hpoly := extremalCount_cast N K t htK hKN
  have hphi :
      2 * ((t.choose 2 + t * (N - t) : ℕ) : ℚ) =
        (t : ℚ) * ((t : ℚ) - 1) + 2 * (t : ℚ) * ((N : ℚ) - (t : ℚ)) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two, Nat.cast_sub htN]
    ring
  have hparity : K = 2 * t + 1 ∨ K = 2 * t + 2 := by dsimp [t]; omega
  have hq : ((t.choose 2 + t * (N - t) : ℕ) : ℚ) ≤
      (extremalCount N K t : ℚ) := by
    rcases hparity with hodd | heven
    · have hKq : (K : ℚ) = 2 * (t : ℚ) + 1 := by
        rw [hodd]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      rw [hKq] at hpoly
      nlinarith [hphi]
    · have hKq : (K : ℚ) = 2 * (t : ℚ) + 2 := by
        rw [heven]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [hKq] at hpoly
      nlinarith [hphi]
  exact Nat.cast_le.mp hq

end ErdosProblems.PathUpperReduction.CoreEndpointBound1105
