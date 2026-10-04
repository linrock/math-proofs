module

public import Mathlib


@[expose] public section

/-!
# Half-cap fiber probability distortion

Defines the BBMST fiber weight update with distortion cap $1/2$ (`badFactor`
and `goodFactor`), proving mass preservation, pointwise factor-two upper
bounds, and the quadratic bound `a * badFactor a ≤ a ^ 2` that drives the
second-moment sieve loss estimate.
-/

namespace Erdos2.Fiber

noncomputable def badFactor (a : ℝ) : ℝ :=
  if a ≤ 1 / 2 then 0 else (2 * a - 1) / a

noncomputable def goodFactor (a : ℝ) : ℝ :=
  if a ≤ 1 / 2 then 1 / (1 - a) else 2

variable {β : Type*} [Fintype β] [DecidableEq β]

noncomputable def fraction (B : Finset β) : ℝ :=
  (B.card : ℝ) / Fintype.card β

noncomputable def updatedWeight (B : Finset β) (w : ℝ) (y : β) : ℝ :=
  w / Fintype.card β *
    (if y ∈ B then badFactor (fraction B) else goodFactor (fraction B))


theorem badFactor_nonneg (a : ℝ) (ha : 0 ≤ a) : 0 ≤ badFactor a := by
  unfold badFactor
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (by linarith) ha

theorem badFactor_le_one (a : ℝ) (ha : a ≤ 1) : badFactor a ≤ 1 := by
  unfold badFactor
  split_ifs with h
  · norm_num
  · apply (div_le_iff₀ (by linarith : 0 < a)).2
    linarith

theorem goodFactor_nonneg (a : ℝ) : 0 ≤ goodFactor a := by
  unfold goodFactor
  split_ifs with h
  · exact div_nonneg (by norm_num) (by linarith)
  · norm_num

theorem goodFactor_le_two (a : ℝ) : goodFactor a ≤ 2 := by
  unfold goodFactor
  split_ifs with h
  · apply (div_le_iff₀ (by linarith : 0 < 1-a)).2
    linarith
  · exact le_rfl

theorem factor_mass_eq_one (a : ℝ) :
    a * badFactor a + (1-a) * goodFactor a = 1 := by
  unfold badFactor goodFactor
  split_ifs with h
  · rw [mul_zero, zero_add, mul_one_div_cancel (by linarith : 1-a ≠ 0)]
  · field_simp [show a ≠ 0 by linarith]
    ring

theorem bad_mass_eq_max (a : ℝ) : a * badFactor a = max 0 (2*a-1) := by
  unfold badFactor
  split_ifs with h
  · rw [mul_zero, max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]
    field_simp [show a ≠ 0 by linarith]

omit [DecidableEq β] in
theorem fraction_nonneg (B : Finset β) : 0 ≤ fraction B := by
  unfold fraction
  positivity

omit [DecidableEq β] in
theorem fraction_le_one (B : Finset β) [Nonempty β] : fraction B ≤ 1 := by
  have hN : (0 : ℝ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hN).2
  simpa using (show (B.card : ℝ) ≤ (Fintype.card β : ℝ) by exact_mod_cast B.card_le_univ)


theorem bad_mass_le_self (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a * badFactor a ≤ a := by
  exact mul_le_of_le_one_right ha (badFactor_le_one a ha1)

theorem bad_mass_le_sq (a : ℝ) : a * badFactor a ≤ a^2 := by
  rw [bad_mass_eq_max, max_le_iff]
  constructor
  · positivity
  · nlinarith [sq_nonneg (a-1)]

theorem updatedWeight_nonneg (B : Finset β) (w : ℝ) (hw : 0 ≤ w) (y : β) :
    0 ≤ updatedWeight B w y := by
  unfold updatedWeight
  apply mul_nonneg (div_nonneg hw (by positivity))
  split_ifs
  · exact badFactor_nonneg _ (fraction_nonneg B)
  · exact goodFactor_nonneg _

theorem updatedWeight_le_two (B : Finset β) [Nonempty β] (w : ℝ) (hw : 0 ≤ w) (y : β) :
    updatedWeight B w y ≤ 2*w/Fintype.card β := by
  unfold updatedWeight
  have hN : (0 : ℝ) ≤ w/Fintype.card β := by positivity
  calc
    _ ≤ w/Fintype.card β * 2 := by
      apply mul_le_mul_of_nonneg_left _ hN
      split_ifs
      · exact (badFactor_le_one _ (fraction_le_one B)).trans (by norm_num)
      · exact goodFactor_le_two _
    _ = _ := by ring

theorem sum_piecewise_factors (B : Finset β) (b g : ℝ) :
    (∑ y : β, if y ∈ B then b else g) =
      (B.card : ℝ)*b + ((Fintype.card β : ℝ)-(B.card : ℝ))*g := by
  rw [Finset.sum_ite]
  simp [Finset.filter_not, Finset.card_univ_sdiff, Nat.cast_sub B.card_le_univ]

theorem sum_bad_updatedWeight_eq (B : Finset β) (w : ℝ) :
    (∑ y ∈ B, updatedWeight B w y) = w * fraction B * badFactor (fraction B) := by
  calc
    _ = ∑ _y ∈ B, w/Fintype.card β*badFactor (fraction B) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp [updatedWeight, hy]
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      unfold fraction
      ring


theorem sum_bad_updatedWeight_le_sq (B : Finset β) (w : ℝ) (hw : 0 ≤ w) :
    (∑ y ∈ B, updatedWeight B w y) ≤ w * (fraction B)^2 := by
  rw [sum_bad_updatedWeight_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (bad_mass_le_sq _) hw

theorem sum_bad_updatedWeight_le_first (B : Finset β) [Nonempty β]
    (w : ℝ) (hw : 0 ≤ w) :
    (∑ y ∈ B, updatedWeight B w y) ≤ w * fraction B := by
  rw [sum_bad_updatedWeight_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (bad_mass_le_self _ (fraction_nonneg B) (fraction_le_one B)) hw

theorem badFactor_le_two (a : ℝ) (ha : a ≤ 1) : badFactor a ≤ 2 :=
  (badFactor_le_one a ha).trans (by norm_num)

theorem sum_updatedWeight_eq (B : Finset β) [Nonempty β] (w : ℝ) :
    (∑ y : β, updatedWeight B w y) = w := by
  have hN : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold updatedWeight
  rw [← Finset.mul_sum, sum_piecewise_factors]
  calc
    _ = w * (fraction B * badFactor (fraction B) +
        (1-fraction B) * goodFactor (fraction B)) := by
      unfold fraction
      field_simp [hN]
    _ = w := by rw [factor_mass_eq_one, mul_one]


theorem preserves_baseEvent_mass {γ : Type*} (X : Finset γ)
    [Nonempty β] (B : γ → Finset β) (w : γ → ℝ) :
    (∑ x ∈ X, ∑ y : β, updatedWeight (B x) (w x) y) = ∑ x ∈ X, w x := by
  simp_rw [sum_updatedWeight_eq]

theorem bad_mass_across_fibers_le_secondMoment {γ : Type*} (X : Finset γ)
    (B : γ → Finset β) (w : γ → ℝ) (hw : ∀ x ∈ X, 0 ≤ w x) :
    (∑ x ∈ X, ∑ y ∈ B x, updatedWeight (B x) (w x) y) ≤
      ∑ x ∈ X, w x * (fraction (B x))^2 := by
  apply Finset.sum_le_sum
  intro x hx
  exact sum_bad_updatedWeight_le_sq (B x) (w x) (hw x hx)

theorem updatedWeight_bad_eq_zero (B : Finset β) (w : ℝ) (y : β)
    (hy : y ∈ B) (ha : fraction B ≤ 1/2) :
    updatedWeight B w y = 0 := by
  simp only [updatedWeight, hy, ↓reduceIte, badFactor, ha, mul_zero]

end Erdos2.Fiber
