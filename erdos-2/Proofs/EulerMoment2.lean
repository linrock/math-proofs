module

public import Mathlib


@[expose] public section

/-!
# Finite Euler-factor bounds for the capped probability sieve

Factorizes the double sum over prime-exponent vectors into single-prime factors
`pairFactor q n` and bounds each prime factor by
`factorBound q = 1 + 2 * (3 * q - 1) / (q - 1) ^ 2`.
-/

namespace Erdos2.EulerMoment

open Finset

/-- Coordinate weight after a factor-two distortion bound. -/
noncomputable def pairWeight (q : ℝ) (a b : ℕ) : ℝ :=
  if max a b = 0 then 1 else 2 / q ^ max a b

/-- The pair factor for exponents from 0 through n, including exponent zero. -/
noncomputable def pairFactor (q : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), pairWeight q a b

/-- The published uniform upper bound for one prime coordinate. -/
noncomputable def factorBound (q : ℝ) : ℝ :=
  1 + 2 * (3 * q - 1) / (q - 1) ^ 2

theorem pairWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (a b : ℕ) :
    0 ≤ pairWeight q a b := by
  unfold pairWeight
  split_ifs <;> positivity

theorem pairFactor_zero (q : ℝ) : pairFactor q 0 = 1 := by
  simp [pairFactor, pairWeight]

theorem new_row (q : ℝ) (n : ℕ) :
    (∑ b ∈ range (n + 1), pairWeight q (n + 1) b) =
      (n + 1 : ℝ) * (2 / q ^ (n + 1)) := by
  calc
    _ = ∑ b ∈ range (n + 1), (2 / q ^ (n + 1)) := by
      apply sum_congr rfl
      intro b hb
      have hb' : b ≤ n + 1 := (mem_range.mp hb).le
      simp [pairWeight, max_eq_left hb']
    _ = _ := by simp

theorem new_column (q : ℝ) (n : ℕ) :
    (∑ a ∈ range (n + 1), pairWeight q a (n + 1)) =
      (n + 1 : ℝ) * (2 / q ^ (n + 1)) := by
  calc
    _ = ∑ a ∈ range (n + 1), (2 / q ^ (n + 1)) := by
      apply sum_congr rfl
      intro a ha
      have ha' : a ≤ n + 1 := (mem_range.mp ha).le
      simp [pairWeight, max_eq_right ha']
    _ = _ := by simp

theorem pairFactor_succ (q : ℝ) (n : ℕ) :
    pairFactor q (n + 1) = pairFactor q n +
      (2 * (n + 1 : ℝ) + 1) * (2 / q ^ (n + 1)) := by
  unfold pairFactor
  have hsplit (a : ℕ) :
      (∑ b ∈ range (n + 1 + 1), pairWeight q a b) =
        (∑ b ∈ range (n + 1), pairWeight q a b) + pairWeight q a (n + 1) :=
    sum_range_succ _ _
  rw [sum_range_succ]
  simp_rw [hsplit]
  rw [sum_add_distrib]
  rw [new_column, new_row]
  simp only [pairWeight, max_self, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceIte]
  ring

/-- Exact finite arithmetic-geometric identity; no infinite summation needed. -/
theorem weighted_geom_identity (r : ℝ) (n : ℕ) :
    (∑ t ∈ range n, (2 * (t : ℝ) + 3) * r ^ (t + 1)) * (1 - r) ^ 2 =
      r * (3 - r) -
        r ^ (n + 1) * ((2 * (n : ℝ) + 3) - (2 * (n : ℝ) + 1) * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    rw [show n + 1 + 1 = (n + 1) + 1 by rfl, pow_succ]
    ring

theorem weighted_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ t ∈ range n, (2 * (t : ℝ) + 3) * r ^ (t + 1)) ≤
      r * (3 - r) / (1 - r) ^ 2 := by
  have hpos : 0 < (1 - r) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
  apply (le_div_iff₀ hpos).mpr
  rw [weighted_geom_identity]
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrem : 0 ≤ (2 * (n : ℝ) + 3) - (2 * (n : ℝ) + 1) * r := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * (n : ℝ) + 1)
      (sub_nonneg.mpr hr1.le)]
  have hp : 0 ≤ r ^ (n + 1) := pow_nonneg hr0 _
  nlinarith [mul_nonneg hp hrem]

theorem pairFactor_eq_weighted (q : ℝ) (n : ℕ) :
    pairFactor q n =
      1 + 2 * ∑ t ∈ range n, (2 * (t : ℝ) + 3) / q ^ (t + 1) := by
  induction n with
  | zero => simp [pairFactor_zero]
  | succ n ih =>
    rw [pairFactor_succ, ih, sum_range_succ]
    ring

theorem pairFactor_le {q : ℝ} (hq : 2 ≤ q) (n : ℕ) :
    pairFactor q n ≤ factorBound q := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).mpr (by linarith)
  have h := weighted_geom_le hr0 hr1 n
  simp only [inv_pow, ← div_eq_mul_inv] at h
  rw [pairFactor_eq_weighted]
  unfold factorBound
  have heq : q⁻¹ * (3 - q⁻¹) / (1 - q⁻¹) ^ 2 =
      (3 * q - 1) / (q - 1) ^ 2 := by
    field_simp
  rw [heq] at h
  simpa only [mul_div_assoc, add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)) 1

/-- A pair of exponent choices at each coordinate. -/
abbrev PairChoices {J : Type*} (γ : J → ℕ) :=
  ∀ j, Fin (γ j + 1) × Fin (γ j + 1)

noncomputable def vectorPairSum {J : Type*} [Fintype J]
    (q : J → ℝ) (γ : J → ℕ) : ℝ := by
  classical
  exact ∑ x : PairChoices γ, ∏ j, pairWeight (q j) (x j).1.val (x j).2.val

theorem vectorPairSum_factorizes {J : Type*} [Fintype J]
    (q : J → ℝ) (γ : J → ℕ) :
    vectorPairSum q γ = ∏ j, pairFactor (q j) (γ j) := by
  classical
  unfold vectorPairSum
  calc
    _ = ∏ j, ∑ p : Fin (γ j + 1) × Fin (γ j + 1),
      pairWeight (q j) p.1.val p.2.val :=
        (Fintype.prod_sum (fun j (p : Fin (γ j + 1) × Fin (γ j + 1)) =>
          pairWeight (q j) p.1.val p.2.val)).symm
    _ = _ := by
      apply prod_congr rfl
      intro j hj
      simp only [Fintype.sum_prod_type]
      rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (γ j + 1),
        pairWeight (q j) a b.val)]
      apply sum_congr rfl
      intro a ha
      rw [Fin.sum_univ_eq_sum_range (fun b => pairWeight (q j) a b)]

theorem vectorPairSum_le {J : Type*} [Fintype J]
    (q : J → ℝ) (γ : J → ℕ) (hq : ∀ j, 2 ≤ q j) :
    vectorPairSum q γ ≤ ∏ j, factorBound (q j) := by
  classical
  rw [vectorPairSum_factorizes]
  apply Finset.prod_le_prod₀
  · intro j hj
    unfold pairFactor
    exact sum_nonneg fun a ha => sum_nonneg fun b hb =>
      pairWeight_nonneg (by linarith [hq j]) a b
  · intro j hj
    exact pairFactor_le (hq j) (γ j)

abbrev ExponentChoices {J : Type*} (γ : J → ℕ) := ∀ j, Fin (γ j + 1)

/-- The separate-vector double sum used by the divisor-pair second moment. -/
noncomputable def doubleVectorSum {J : Type*} [Fintype J]
    (q : J → ℝ) (γ : J → ℕ) : ℝ := by
  classical
  exact ∑ a : ExponentChoices γ, ∑ b : ExponentChoices γ,
    ∏ j, pairWeight (q j) (a j).val (b j).val

theorem doubleVectorSum_eq {J : Type*} [Fintype J]
    (q : J → ℝ) (γ : J → ℕ) : doubleVectorSum q γ = vectorPairSum q γ := by
  classical
  let e := (Equiv.arrowProdEquivProdArrow J (fun j => Fin (γ j + 1))
    (fun j => Fin (γ j + 1))).symm
  unfold doubleVectorSum vectorPairSum
  calc
    _ = ∑ x : ExponentChoices γ × ExponentChoices γ,
      ∏ j, pairWeight (q j) (x.1 j).val (x.2 j).val :=
        (Fintype.sum_prod_type (fun x : ExponentChoices γ × ExponentChoices γ =>
          ∏ j, pairWeight (q j) (x.1 j).val (x.2 j).val)).symm
    _ = _ := Fintype.sum_equiv e
      (fun x => ∏ j, pairWeight (q j) (x.1 j).val (x.2 j).val)
      (fun x => ∏ j, pairWeight (q j) (x j).1.val (x j).2.val)
      (fun x => rfl)

theorem doubleVectorSum_le {J : Type*} [Fintype J]
    (q : J → ℝ) (γ : J → ℕ) (hq : ∀ j, 2 ≤ q j) :
    doubleVectorSum q γ ≤ ∏ j, factorBound (q j) := by
  rw [doubleVectorSum_eq]
  exact vectorPairSum_le q γ hq

end Erdos2.EulerMoment
