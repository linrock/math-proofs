module

public import PathEvenFiniteWindowPropagation
public import PathHighNewOddPath
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
The public theorem retains the literal
original k,n quantifiers and formula; its right side requires all original
whole-host finite windows, not representative graphs or supplied colorings.
-/

namespace ErdosProblems.PathGeneralFiniteWindowReduction

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

def oddBound (ell n : ℕ) : ℕ :=
  max ((2 * ell - 1).choose 2 + 1)
    ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1)

def oddWindowEnd (ell : ℕ) : ℕ :=
  2 * ell + 1 + (ell - 3) / 2

theorem odd_constant_le_linear (ell m : ℕ) (hell : 2 ≤ ell)
    (hm : oddWindowEnd ell ≤ m) :
    (2 * ell - 1).choose 2 + 1 ≤
      (ell - 1).choose 2 + (ell - 1) * (m - ell + 1) + 1 := by
  have hmell : ell ≤ m := by dsimp [oddWindowEnd] at hm; omega
  have hthreshold : 5 * ell ≤ 2 * m + 2 := by
    dsimp [oddWindowEnd] at hm
    omega
  have hthresholdR : (5 : ℝ) * (ell : ℝ) ≤ 2 * (m : ℝ) + 2 := by
    exact_mod_cast hthreshold
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by
    exact_mod_cast (show 1 ≤ ell by omega)
  have hpredR : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    have hsum : ((ell - 1 : ℕ) : ℝ) + 1 = (ell : ℝ) := by
      exact_mod_cast (show ell - 1 + 1 = ell by omega)
    linarith
  have hmajorR : ((2 * ell - 1 : ℕ) : ℝ) = 2 * (ell : ℝ) - 1 := by
    have hsum : ((2 * ell - 1 : ℕ) : ℝ) + 1 = 2 * (ell : ℝ) := by
      exact_mod_cast (show 2 * ell - 1 + 1 = 2 * ell by omega)
    linarith
  have hsubR : ((m - ell : ℕ) : ℝ) = (m : ℝ) - (ell : ℝ) := by
    have hsum : ((m - ell : ℕ) : ℝ) + (ell : ℝ) = (m : ℝ) := by
      exact_mod_cast (show m - ell + ell = m by omega)
    linarith
  have hproduct : 0 ≤ ((ell : ℝ) - 1) *
      (2 * (m : ℝ) - 5 * (ell : ℝ) + 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hreal :
      (((2 * ell - 1).choose 2 + 1 : ℕ) : ℝ) ≤
        (((ell - 1).choose 2 + (ell - 1) * (m - ell + 1) + 1 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [Nat.cast_choose_two ℝ (2 * ell - 1), Nat.cast_choose_two ℝ (ell - 1)]
    simp only [hpredR, hmajorR, hsubR]
    nlinarith [hproduct]
  exact_mod_cast hreal

theorem odd_bound_succ (ell m : ℕ) (hell : 2 ≤ ell)
    (hm : oddWindowEnd ell ≤ m) :
    oddBound ell (m + 1) = oddBound ell m + (ell - 1) := by
  have hmell : ell ≤ m := by dsimp [oddWindowEnd] at hm; omega
  have hleft := odd_constant_le_linear ell m hell hm
  have hright := odd_constant_le_linear ell (m + 1) hell (by omega)
  have hsub : m + 1 - ell + 1 = (m - ell + 1) + 1 := by omega
  simp only [oddBound, max_eq_right hleft, max_eq_right hright]
  rw [hsub]
  ring

theorem odd_upper_of_window (ell : ℕ) (hell : 2 ≤ ell)
    (hbases : ∀ n : ℕ, 2 * ell + 1 ≤ n → n ≤ oddWindowEnd ell →
      antiRamseyNum (pathGraph (2 * ell + 1)) n ≤ oddBound ell n) :
    ∀ n : ℕ, 2 * ell + 1 ≤ n →
      antiRamseyNum (pathGraph (2 * ell + 1)) n ≤ oddBound ell n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hwindow : n ≤ oddWindowEnd ell
    · exact hbases n hn hwindow
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_add_one_of_ne_zero (by omega)
    have hm : oddWindowEnd ell ≤ m := by omega
    have hmk : 2 * ell + 1 ≤ m := by
      dsimp [oddWindowEnd] at hm
      omega
    have hind : antiRamseyNum (pathGraph (2 * ell + 1)) m ≤ oddBound ell m :=
      ih m (by omega) hmk
    have hjump := odd_bound_succ ell m hell hm
    let S : Set ℕ :=
      {q | ∃ χ : TopEdgeLabeling (Fin (m + 1)) (Fin q),
        Function.Surjective χ ∧
        ∀ f : (pathGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin (m + 1))),
          ¬IsRainbow f.toHom χ}
    have hbounded : BddAbove S := by
      refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin (m + 1))).edgeSet), ?_⟩
      intro q hq
      obtain ⟨χ, hχ, _⟩ := hq
      simpa using Fintype.card_le_of_surjective χ hχ
    change sSup S ≤ oddBound ell (m + 1)
    refine (csSup_le_iff' hbounded).2 ?_
    intro q hq
    obtain ⟨χ, hχ, hno⟩ := hq
    by_contra hnot
    have hlarge : oddBound ell (m + 1) < q := by omega
    have hnew : ∀ v : Fin (m + 1), ell ≤ (newColors χ v).card := by
      intro v
      have hdelete := surjective_color_count_le_antiRamseyNum_add_newColors
        (pathGraph (2 * ell + 1)) χ hχ hno v
      have hstep : q ≤ oddBound ell m + (newColors χ v).card :=
        le_trans hdelete (Nat.add_le_add_right hind (newColors χ v).card)
      rw [hjump] at hlarge
      omega
    obtain ⟨f, hf⟩ :=
      ErdosProblems.PathHighNewOdd.exists_rainbow_odd_path_of_high_new hell hn χ hnew
    exact hno f hf

/-- The literal universal FC1105(ii) upper direction
to every odd and even original whole-host finite window. Its imported positive
original high-NEW theorems are used, not supplied as public hypotheses. -/
theorem original_path_upper_iff_finite_windows :
    (∀ k n : ℕ, 5 ≤ k → k ≤ n →
      let ell := (k - 1) / 2
      let eps := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n ≤
        max ((k - 2).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + eps)) ↔
    ((∀ ell : ℕ, 2 ≤ ell → ∀ n : ℕ,
        2 * ell + 1 ≤ n → n ≤ 2 * ell + 1 + (ell - 3) / 2 →
        antiRamseyNum (pathGraph (2 * ell + 1)) n ≤
          max ((2 * ell - 1).choose 2 + 1)
            ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1)) ∧
      (∀ ell : ℕ, 2 ≤ ell → ∀ n : ℕ,
        2 * ell + 2 ≤ n → n ≤ 2 * ell + 2 + (ell - 1) / 2 →
        antiRamseyNum (pathGraph (2 * ell + 2)) n ≤
          max ((2 * ell).choose 2 + 1)
            ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2))) := by
  classical
  constructor
  · intro hall
    constructor
    · intro ell hell n hn _
      have hodd : Odd (2 * ell + 1) := ⟨ell, by omega⟩
      have hquot : (2 * ell + 1 - 1) / 2 = ell := by omega
      have hsub : 2 * ell + 1 - 2 = 2 * ell - 1 := by omega
      simpa only [hquot, hsub, ite_eq_left hodd] using
        hall (2 * ell + 1) n (by omega) hn
    · intro ell hell n hn _
      have heven : ¬Odd (2 * ell + 2) := by rintro ⟨r, hr⟩; omega
      have hquot : (2 * ell + 2 - 1) / 2 = ell := by omega
      have hsub : 2 * ell + 2 - 2 = 2 * ell := by omega
      simpa only [hquot, hsub, ite_eq_right heven] using
        hall (2 * ell + 2) n (by omega) hn
  · rintro ⟨hoddWindow, hevenWindow⟩ k n hk hn
    let ell := (k - 1) / 2
    have hell : 2 ≤ ell := by dsimp [ell]; omega
    have hrepr : k = 2 * ell + 1 ∨ k = 2 * ell + 2 := by dsimp [ell]; omega
    rcases hrepr with hoddK | hevenK
    · have hupper := odd_upper_of_window ell hell (hoddWindow ell hell) n (by omega)
      have hodd : Odd k := ⟨ell, by omega⟩
      have hsub : k - 2 = 2 * ell - 1 := by omega
      change antiRamseyNum (pathGraph k) n ≤
        max ((k - 2).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) +
            (if Odd k then 1 else 2))
      rw [hsub, ite_eq_left hodd, hoddK]
      exact hupper
    · have hhigh : ∀ m : ℕ, 2 * ell + 2 ≤ m →
          ∀ (C : Type) [DecidableEq C] (χ : TopEdgeLabeling (Fin m) C),
            (∀ v : Fin m, ell ≤ (newColors χ v).card) →
            ∃ f : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin m)),
              IsRainbow f.toHom χ := by
        intro m hm C _ χ hnew
        exact ErdosProblems.PathHighNew.exists_rainbow_even_path_of_high_new
          hell hm χ hnew
      have hupper :=
        ErdosProblems.AntiRamseyEvenPathFiniteWindow.antiRamseyNum_even_path_le_of_high_new_and_window
            ell hell hhigh (hevenWindow ell hell) n (by omega)
      have heven : ¬Odd k := by rintro ⟨r, hr⟩; omega
      have hsub : k - 2 = 2 * ell := by omega
      change antiRamseyNum (pathGraph k) n ≤
        max ((k - 2).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) +
            (if Odd k then 1 else 2))
      rw [hsub, ite_eq_right heven, hevenK]
      exact hupper

end ErdosProblems.PathGeneralFiniteWindowReduction
