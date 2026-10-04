module

public import MonochromaticPairs546
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt


@[expose] public section

/-!
# Initial monochromatic pair for the amplification schedule

Applies Sudakov's Lemma 2.2 (`exists_monoPair`) at initial scale $a = 3$ to find
a monochromatic pair $(X, Y)$ with $|X| \ge 27 \sqrt{m}$ and
$|Y| \ge 2^{(500 + 1600/3)\sqrt{m}}$ inside any 2-colored complete host of
order at least $2^{2000\sqrt{m}}$.
-/

namespace Erdos546

open SimpleGraph Finset

theorem initial_pair_for_sparse_ramsey {W : Type*} [Fintype W]
    (H : SimpleGraph W) (m : ℕ) (hm : 64 ≤ m)
    (hhost : (2 : ℝ) ^ (2000 * Real.sqrt m) ≤ Fintype.card W) :
    ∃ X Y : Finset W, (MonoPair H X Y ∨ MonoPair Hᶜ X Y) ∧
      (3 : ℝ)^3 * Real.sqrt m ≤ X.card ∧
      (2 : ℝ)^((500 + 4 * (400 : ℝ) / 3) * Real.sqrt m) ≤ Y.card := by
  classical
  let s : ℝ := Real.sqrt m
  let R : ℝ := (2 : ℝ)^((500 + 4 * (400 : ℝ) / 3) * s)
  let k : ℕ := ⌈27 * s⌉₊
  let r : ℕ := ⌈R⌉₊
  have hs : (8 : ℝ) ≤ s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hm
  have hs0 : 0 ≤ s := by linarith
  have hR1 : 1 ≤ R := by
    calc
      (1 : ℝ) = (2 : ℝ)^((0 : ℝ)) := by simp
      _ ≤ R := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  have hkupper : (k : ℝ) < 27 * s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrupper : (r : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  have hrplus : (r : ℝ) + 1 ≤ 3 * R := by linarith
  have hchoose : (((k + k).choose k : ℕ) : ℝ) ≤ (2 : ℝ)^(2 * k) := by
    exact_mod_cast (by simpa [two_mul] using Nat.choose_le_two_pow (k + k) k)
  have hkpow : (2 : ℝ)^(2 * k) ≤ (2 : ℝ)^(54 * s + 2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hthree : (3 : ℝ) ≤ (2 : ℝ)^((2 : ℝ)) := by norm_num
  have hslack : (54 * s + 2) +
      ((500 + 4 * (400 : ℝ) / 3) * s + 2) ≤ 2000 * s := by linarith
  have hthresholdR : (((k + k).choose k * (r + 1) : ℕ) : ℝ) ≤ Fintype.card W := by
    calc
      (((k + k).choose k * (r + 1) : ℕ) : ℝ) ≤ (2 : ℝ)^(2 * k) * (3 * R) := by
        push_cast
        exact mul_le_mul hchoose hrplus (by positivity) (by positivity)
      _ ≤ (2 : ℝ)^(54 * s + 2) * (R * (2 : ℝ)^((2 : ℝ))) := by
        apply mul_le_mul hkpow _ (by positivity) (by positivity)
        nlinarith
      _ = (2 : ℝ)^((54 * s + 2) + ((500 + 4 * (400 : ℝ) / 3) * s + 2)) := by
        dsimp [R]
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
      _ ≤ (2 : ℝ)^(2000 * s) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hslack
      _ ≤ Fintype.card W := hhost
  have hthreshold : (k + k).choose k * (r + 1) ≤ (univ : Finset W).card := by
    exact_mod_cast hthresholdR
  rcases exists_monoPair H k k r univ hthreshold with h | h
  · rcases h with ⟨X, Y, _, _, hp, hX, hY⟩
    refine ⟨X, Y, Or.inl hp, ?_, ?_⟩
    · rw [hX]
      norm_num only [show (3 : ℝ)^3 = 27 by norm_num]
      exact Nat.le_ceil _
    · have hYreal : (r : ℝ) ≤ Y.card := by exact_mod_cast hY
      exact (Nat.le_ceil R).trans hYreal
  · rcases h with ⟨X, Y, _, _, hp, hX, hY⟩
    refine ⟨X, Y, Or.inr hp, ?_, ?_⟩
    · rw [hX]
      norm_num only [show (3 : ℝ)^3 = 27 by norm_num]
      exact Nat.le_ceil _
    · have hYreal : (r : ℝ) ≤ Y.card := by exact_mod_cast hY
      exact (Nat.le_ceil R).trans hYreal

end Erdos546
