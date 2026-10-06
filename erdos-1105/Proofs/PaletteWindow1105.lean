module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public meta import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

#guard (let m : ℕ := 4; let l : ℕ := 3; let q : ℕ := 9;
  max (m.choose 2 + 1)
    (((m + 1) / 2 - 1).choose 2 +
      ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
      (if Odd m then 1 else 2)) < q ∧
    q ≤ m.choose 2 + l ∧ ¬ (2 * l ≤ m) ∧ q = 6 + l)

#guard (let m : ℕ := 6; let l : ℕ := 2; let q : ℕ := 17;
  max (m.choose 2 + 1)
    (((m + 1) / 2 - 1).choose 2 +
      ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
      (if Odd m then 1 else 2)) < q ∧
    q ≤ m.choose 2 + l ∧ 2 * l ≤ m)

#guard (let m : ℕ := 6; let l : ℕ := 4;
  ((m + 1) / 2 - 1).choose 2 +
      ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
      (if Odd m then 1 else 2) = 19 ∧ m.choose 2 + l = 19)

/-!
For the original-palette S1 window/equality split. The three
preceding Q candidate statements and proof bodies are preserved unchanged.

The original parameters are m = k - 2 and n = m + l. The literal linear
threshold is retained, including its natural subtraction, division, and
parity term. The necessary m = 4 exception is retained: m = 4, l = 3,
q = 9 satisfies both palette premises but not 2*l <= m. The literal caller
records it as k = 6 and q = n + 2. Capacity is still an explicit premise;
no selected-graph capacity or original-color conclusion is proved here.
-/

namespace ErdosProblems.PathUpperReduction.WindowNumerics1105

theorem odd_capacity_le_threshold (a l : ℕ) (ha : 2 ≤ a) (hl : a + 1 ≤ l) :
    (2 * a + 1).choose 2 + l ≤ a.choose 2 + a * (a + l + 1) + 1 := by
  have haq : (2 : ℚ) ≤ (a : ℚ) := Nat.cast_le.mpr ha
  have hlq : (a : ℚ) + 1 ≤ (l : ℚ) := by
    have h : ((a + 1 : ℕ) : ℚ) ≤ (l : ℚ) := Nat.cast_le.mpr hl
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hfactor : 0 ≤ (a : ℚ) - 1 := by linarith
  have hgap : 0 ≤ (l : ℚ) - ((a : ℚ) + 1) := by linarith
  have hmul := mul_nonneg hfactor hgap
  have hsq := mul_nonneg (Nat.cast_nonneg a : (0 : ℚ) ≤ (a : ℚ)) hfactor
  have hidentity :
      2 * (((2 * a + 1).choose 2 + l : ℕ) : ℚ) -
          2 * ((a.choose 2 + a * (a + l + 1) + 1 : ℕ) : ℚ) =
        (a : ℚ) * ((a : ℚ) + 1) - 2 * ((a : ℚ) - 1) * (l : ℚ) - 2 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
      Nat.cast_one, Nat.cast_ofNat]
    ring
  have hcast : (((2 * a + 1).choose 2 + l : ℕ) : ℚ) ≤
      ((a.choose 2 + a * (a + l + 1) + 1 : ℕ) : ℚ) := by
    nlinarith [hidentity, hmul, hsq]
  exact Nat.cast_le.mp hcast

theorem even_capacity_le_threshold (a l : ℕ) (ha : 3 ≤ a) (hl : a + 1 ≤ l) :
    (2 * a).choose 2 + l ≤
      (a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 := by
  have ha1 : 1 ≤ a := by omega
  have haq : (3 : ℚ) ≤ (a : ℚ) := Nat.cast_le.mpr ha
  have hlq : (a : ℚ) + 1 ≤ (l : ℚ) := by
    have h : ((a + 1 : ℕ) : ℚ) ≤ (l : ℚ) := Nat.cast_le.mpr hl
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hfactor : 0 ≤ (a : ℚ) - 2 := by linarith
  have hgap : 0 ≤ (l : ℚ) - ((a : ℚ) + 1) := by linarith
  have hmul := mul_nonneg hfactor hgap
  have hsq := mul_nonneg (Nat.cast_nonneg a : (0 : ℚ) ≤ (a : ℚ))
    (show 0 ≤ (a : ℚ) - 3 by linarith)
  have hidentity :
      2 * (((2 * a).choose 2 + l : ℕ) : ℚ) -
          2 * (((a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 : ℕ) : ℚ) =
        (a : ℚ) * ((a : ℚ) + 1) - 2 * ((a : ℚ) - 2) * (l : ℚ) - 4 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two,
      Nat.cast_sub ha1, Nat.cast_one, Nat.cast_ofNat]
    ring
  have hcast : (((2 * a).choose 2 + l : ℕ) : ℚ) ≤
      (((a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 : ℕ) : ℚ) := by
    nlinarith [hidentity, hmul, hsq]
  exact Nat.cast_le.mp hcast

theorem palette_implies_s1_window (m l q : ℕ) (hm : 5 ≤ m) (_hl : 2 ≤ l)
    (hq : max (m.choose 2 + 1)
      (((m + 1) / 2 - 1).choose 2 +
        ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
        (if Odd m then 1 else 2)) < q)
    (hcapacity : q ≤ m.choose 2 + l) : 2 * l ≤ m := by
  have hBq :
      ((m + 1) / 2 - 1).choose 2 +
        ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
        (if Odd m then 1 else 2) < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  by_contra hwindow
  let a : ℕ := m / 2
  have hparity : m = 2 * a + 1 ∨ m = 2 * a := by dsimp [a]; omega
  rcases hparity with hodd | heven
  · have ha : 2 ≤ a := by omega
    have hl : a + 1 ≤ l := by omega
    have hpred : (m + 1) / 2 - 1 = a := by omega
    have hterm : m + l - (m + 1) / 2 + 1 = a + l + 1 := by omega
    have hmOdd : Odd m := Nat.odd_iff.mpr (by omega)
    have hC : m.choose 2 + l ≤ a.choose 2 + a * (a + l + 1) + 1 := by
      rw [hodd]
      exact odd_capacity_le_threshold a l ha hl
    have hB : a.choose 2 + a * (a + l + 1) + 1 < q := by
      simpa only [hpred, hterm, ite_eq_left hmOdd] using hBq
    omega
  · have ha : 3 ≤ a := by omega
    have hl : a + 1 ≤ l := by omega
    have hpred : (m + 1) / 2 - 1 = a - 1 := by omega
    have hterm : m + l - (m + 1) / 2 + 1 = a + l + 1 := by omega
    have hmNotOdd : ¬ Odd m := Nat.not_odd_iff.mpr (by omega)
    have hC : m.choose 2 + l ≤
        (a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 := by
      rw [heven]
      exact even_capacity_le_threshold a l ha hl
    have hB : (a - 1).choose 2 + (a - 1) * (a + l + 1) + 2 < q := by
      simpa only [hpred, hterm, ite_eq_right hmNotOdd] using hBq
    omega

theorem s1_palette_implies_window_or_full_four (m l q : ℕ)
    (hm : 4 ≤ m) (hl : 2 ≤ l)
    (hq : max (m.choose 2 + 1)
      (((m + 1) / 2 - 1).choose 2 +
        ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
        (if Odd m then 1 else 2)) < q)
    (hcapacity : q ≤ m.choose 2 + l) :
    m.choose 2 + 2 ≤ q ∧ (2 * l ≤ m ∨ (m = 4 ∧ q = 6 + l)) := by
  have hAq : m.choose 2 + 1 < q :=
    lt_of_le_of_lt (le_max_left _ _) hq
  refine ⟨by omega, ?_⟩
  by_cases hfour : m = 4
  · right
    refine ⟨hfour, ?_⟩
    have hBq :
        ((m + 1) / 2 - 1).choose 2 +
          ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
          (if Odd m then 1 else 2) < q :=
      lt_of_le_of_lt (le_max_right _ _) hq
    have hpred : (m + 1) / 2 - 1 = 1 := by omega
    have hterm : m + l - (m + 1) / 2 + 1 = l + 3 := by omega
    have hmNotOdd : ¬ Odd m := Nat.not_odd_iff.mpr (by omega)
    have hchoose1 : (1 : ℕ).choose 2 = 0 := by decide
    have hchoose4 : m.choose 2 = 6 := by rw [hfour]; decide
    rw [hpred, hterm, ite_eq_right hmNotOdd, hchoose1, one_mul, zero_add] at hBq
    rw [hchoose4] at hcapacity
    omega
  · left
    exact palette_implies_s1_window m l q (by omega) hl hq hcapacity

theorem original_palette_implies_window_or_full_four (k n q : ℕ)
    (hk : 6 ≤ k) (hkn : k ≤ n)
    (hq : max ((k - 2).choose 2 + 1)
      (((k - 1) / 2 - 1).choose 2 +
        ((k - 1) / 2 - 1) * (n - (k - 1) / 2 + 1) +
        (if Odd k then 1 else 2)) < q)
    (hcapacity : q ≤ (k - 2).choose 2 + (n - k + 2)) :
    (k - 2).choose 2 + 2 ≤ q ∧
      (2 * (n - k + 2) ≤ k - 2 ∨ (k = 6 ∧ q = n + 2)) := by
  let m : ℕ := k - 2
  let l : ℕ := n - k + 2
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hl : 2 ≤ l := by dsimp [l]; omega
  have hkm : k = m + 2 := by dsimp [m]; omega
  have hn : n = m + l := by dsimp [m, l]; omega
  have hell : (k - 1) / 2 = (m + 1) / 2 := by omega
  have hterm : n - (m + 1) / 2 + 1 = m + l - (m + 1) / 2 + 1 := by omega
  have hparity : Odd k ↔ Odd m := by
    simp only [Nat.odd_iff]
    omega
  have hq' : max (m.choose 2 + 1)
      (((m + 1) / 2 - 1).choose 2 +
        ((m + 1) / 2 - 1) * (m + l - (m + 1) / 2 + 1) +
        (if Odd m then 1 else 2)) < q := by
    simpa only [hell, hterm, hparity] using hq
  have hcapacity' : q ≤ m.choose 2 + l := hcapacity
  obtain ⟨hmargin, hcases⟩ :=
    s1_palette_implies_window_or_full_four m l q hm hl hq' hcapacity'
  refine ⟨hmargin, ?_⟩
  rcases hcases with hwindow | ⟨hfour, hfull⟩
  · exact Or.inl hwindow
  · right
    constructor <;> omega

end ErdosProblems.PathUpperReduction.WindowNumerics1105
