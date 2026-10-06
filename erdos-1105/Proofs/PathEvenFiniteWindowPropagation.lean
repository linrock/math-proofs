module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import CycleDeletionPalette
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Conditional finite-window propagation for the even-path upper bound in
FC1105 part ii. The high-NEW implication and every full-host window base
remain explicit mathematical premises.
-/

namespace ErdosProblems.AntiRamseyEvenPathFiniteWindow

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors

def evenBound (ell n : ℕ) : ℕ :=
  max ((2 * ell).choose 2 + 1)
    ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2)

def windowEnd (ell : ℕ) : ℕ :=
  2 * ell + 2 + (ell - 1) / 2

/-- At and above the first integral crossing, the linear branch dominates. -/
theorem constant_le_linear (ell m : ℕ) (hell : 2 ≤ ell)
    (hm : windowEnd ell ≤ m) :
    (2 * ell).choose 2 + 1 ≤
      (ell - 1).choose 2 + (ell - 1) * (m - ell + 1) + 2 := by
  have hmell : ell ≤ m := by
    dsimp [windowEnd] at hm
    omega
  have hthreshold : 5 * ell + 2 ≤ 2 * m := by
    dsimp [windowEnd] at hm
    omega
  have hthresholdR : (5 : ℝ) * (ell : ℝ) + 2 ≤ 2 * (m : ℝ) := by
    exact_mod_cast hthreshold
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by
    exact_mod_cast (show 1 ≤ ell by omega)
  have hpredR : ((ell - 1 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
    have hsum : ((ell - 1 : ℕ) : ℝ) + 1 = (ell : ℝ) := by
      exact_mod_cast (show ell - 1 + 1 = ell by omega)
    linarith
  have hsubR : ((m - ell : ℕ) : ℝ) = (m : ℝ) - (ell : ℝ) := by
    have hsum : ((m - ell : ℕ) : ℝ) + (ell : ℝ) = (m : ℝ) := by
      exact_mod_cast (show m - ell + ell = m by omega)
    linarith
  have hproduct : 0 ≤ ((ell : ℝ) - 1) *
      (2 * (m : ℝ) - 5 * (ell : ℝ) - 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hreal :
      (((2 * ell).choose 2 + 1 : ℕ) : ℝ) ≤
        (((ell - 1).choose 2 + (ell - 1) * (m - ell + 1) + 2 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [Nat.cast_choose_two ℝ (2 * ell), Nat.cast_choose_two ℝ (ell - 1)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, hpredR, hsubR]
    nlinarith [hproduct]
  exact_mod_cast hreal

/-- The increment is proved only after the full base window. -/
theorem bound_succ (ell m : ℕ) (hell : 2 ≤ ell)
    (hm : windowEnd ell ≤ m) :
    evenBound ell (m + 1) = evenBound ell m + (ell - 1) := by
  have hmell : ell ≤ m := by
    dsimp [windowEnd] at hm
    omega
  have hleft := constant_le_linear ell m hell hm
  have hright := constant_le_linear ell (m + 1) hell (by omega)
  have hsub : m + 1 - ell + 1 = (m - ell + 1) + 1 := by omega
  simp only [evenBound, max_eq_right hleft, max_eq_right hright]
  rw [hsub]
  ring

/-- For ell>=2, high ORIGINAL NEW at every vertex plus every full-host base
in the exact finite window implies the original even-path anti-Ramsey upper
on every n>=2*ell+2. The color type in the high-NEW premise is arbitrary;
no finiteness or original surjectivity is supplied. -/
theorem antiRamseyNum_even_path_le_of_high_new_and_window
    (ell : ℕ) (hell : 2 ≤ ell)
    (hhigh : ∀ (n : ℕ), 2 * ell + 2 ≤ n →
      ∀ (C : Type) [DecidableEq C] (χ : TopEdgeLabeling (Fin n) C),
        (∀ v : Fin n, ell ≤ (newColors χ v).card) →
        ∃ f : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
          IsRainbow f.toHom χ)
    (hbases : ∀ (n : ℕ), 2 * ell + 2 ≤ n →
      n ≤ 2 * ell + 2 + (ell - 1) / 2 →
      antiRamseyNum (pathGraph (2 * ell + 2)) n ≤
        max ((2 * ell).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2)) :
    ∀ (n : ℕ), 2 * ell + 2 ≤ n →
      antiRamseyNum (pathGraph (2 * ell + 2)) n ≤
        max ((2 * ell).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    change antiRamseyNum (pathGraph (2 * ell + 2)) n ≤ evenBound ell n
    by_cases hwindow : n ≤ windowEnd ell
    · exact hbases n hn hwindow
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_add_one_of_ne_zero (by omega)
    have hm : windowEnd ell ≤ m := by omega
    have hmk : 2 * ell + 2 ≤ m := by
      dsimp [windowEnd] at hm
      omega
    have hind :
        antiRamseyNum (pathGraph (2 * ell + 2)) m ≤ evenBound ell m :=
      ih m (by omega) hmk
    have hjump := bound_succ ell m hell hm
    let S : Set ℕ :=
      {q | ∃ χ : TopEdgeLabeling (Fin (m + 1)) (Fin q),
        Function.Surjective χ ∧
        ∀ f : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin (m + 1))),
          ¬IsRainbow f.toHom χ}
    have hbounded : BddAbove S := by
      refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin (m + 1))).edgeSet), ?_⟩
      intro q hq
      obtain ⟨χ, hχ, _⟩ := hq
      simpa using Fintype.card_le_of_surjective χ hχ
    change sSup S ≤ evenBound ell (m + 1)
    refine (csSup_le_iff' hbounded).2 ?_
    intro q hq
    obtain ⟨χ, hχ, hno⟩ := hq
    by_contra hnot
    have hlarge : evenBound ell (m + 1) < q := by omega
    have hnew : ∀ v : Fin (m + 1), ell ≤ (newColors χ v).card := by
      intro v
      have hdelete :=
        surjective_color_count_le_antiRamseyNum_add_newColors
          (pathGraph (2 * ell + 2)) χ hχ hno v
      have hstep : q ≤ evenBound ell m + (newColors χ v).card :=
        le_trans hdelete (Nat.add_le_add_right hind (newColors χ v).card)
      rw [hjump] at hlarge
      omega
    obtain ⟨f, hf⟩ := hhigh (m + 1) hn (Fin q) χ hnew
    exact hno f hf

end ErdosProblems.AntiRamseyEvenPathFiniteWindow
