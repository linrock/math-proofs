import Geometry956
import Parameters956
import DifferenceBody956
import Padding956
import Extremal956

/-!
# Four-layer signed-grid construction and sharper constants for Erdős #956

Formalizes the four-layer signed parabolic grid (`m = 3q`, `ℓ = 4q^2`, `L = 4`),
proving the exact translate count `N_q = 48q^3 + 16q^2 + 12q + 4` (`N_1 = 80`),
the exact unordered unit-distance edge polynomial
`J_q = 72q^4 + 32q^3 + 24q^2 + 13q + 3` (`J_1 = 144 ≤ h(80)`), the eventual
lower bound `(2 / 5) N^(4 / 3) < h(N)` for `N ≥ 204525328`, and the degree-21
induced-subset tail polynomial certificates.
-/

namespace Erdos956.FourLayer

open scoped Pointwise
open Erdos956.Geometry

/-- Total number of centers in the four-layer signed grid at scale `q`:
`N_q = 4 (3q + 1)(4q^2 + 1) = 48q^3 + 16q^2 + 12q + 4`. -/
def fourLayerSize (q : ℕ) : ℕ := 48 * q ^ 3 + 16 * q ^ 2 + 12 * q + 4

/-- Total number of unordered unit-distance pairs in the four-layer signed grid at scale `q`:
`J_q = 72q^4 + 32q^3 + 24q^2 + 13q + 3`. -/
def fourLayerEdgePoly (q : ℕ) : ℕ := 72 * q ^ 4 + 32 * q ^ 3 + 24 * q ^ 2 + 13 * q + 3

theorem fourLayerSize_one : fourLayerSize 1 = 80 := by decide
theorem fourLayerEdgePoly_one : fourLayerEdgePoly 1 = 144 := by decide
theorem fourLayerSize_two : fourLayerSize 2 = 476 := by decide
theorem fourLayerEdgePoly_two : fourLayerEdgePoly 2 = 1533 := by decide
theorem fourLayerSize_three : fourLayerSize 3 = 1480 := by decide
theorem fourLayerEdgePoly_three : fourLayerEdgePoly 3 = 6954 := by decide

abbrev FourLayerRect (q : ℕ) := Fin (3 * q + 1) × Fin (4 * q ^ 2 + 1)
abbrev FourLayerIndex (q : ℕ) := Fin 4 × FourLayerRect q

theorem fourLayerIndex_card (q : ℕ) :
    Fintype.card (FourLayerIndex q) = fourLayerSize q := by
  simp [FourLayerIndex, FourLayerRect, fourLayerSize, Fintype.card_prod]
  ring

def fourLayerCenter (q : ℕ) (a b η : ℝ) (idx : FourLayerIndex q) : Plane :=
  point (((idx.2.1.val : ℕ) : ℝ) * a)
    (((idx.1.val : ℕ) : ℝ) * (1 + η) + ((idx.2.2.val : ℕ) : ℝ) * b)

@[simp] theorem fourLayerCenter_zero {q : ℕ} (idx : FourLayerIndex q) (a b η : ℝ) :
    (fourLayerCenter q a b η idx) 0 = ((idx.2.1.val : ℕ) : ℝ) * a := by
  simp [fourLayerCenter]

@[simp] theorem fourLayerCenter_one {q : ℕ} (idx : FourLayerIndex q) (a b η : ℝ) :
    (fourLayerCenter q a b η idx) 1 =
      ((idx.1.val : ℕ) : ℝ) * (1 + η) + ((idx.2.2.val : ℕ) : ℝ) * b := by
  simp [fourLayerCenter]

private theorem rect_y_le {q : ℕ} (p : FourLayerRect q) :
    ((p.2.val : ℕ) : ℝ) ≤ ((4 * q ^ 2 : ℕ) : ℝ) := by
  have h : p.2.val ≤ 4 * q ^ 2 := by omega
  exact_mod_cast h

private theorem rect_x_le {q : ℕ} (p : FourLayerRect q) :
    ((p.1.val : ℕ) : ℝ) ≤ ((3 * q : ℕ) : ℝ) := by
  have h : p.1.val ≤ 3 * q := by omega
  exact_mod_cast h

private theorem cross_layer_vertical_gt {q : ℕ} (u v : FourLayerIndex q)
    (huv : u.1.val < v.1.val) (a b η : ℝ) (hb : 0 < b) (hη : 0 ≤ η)
    (hlayer : ((4 * q ^ 2 : ℕ) : ℝ) * b < 1) :
    η < (fourLayerCenter q a b η v) 1 - (fourLayerCenter q a b η u) 1 := by
  have hstep_nat : u.1.val + 1 ≤ v.1.val := by omega
  have hstep_real : ((u.1.val : ℕ) : ℝ) + 1 ≤ ((v.1.val : ℕ) : ℝ) := by
    exact_mod_cast hstep_nat
  have h1η : 0 ≤ 1 + η := by linarith
  have hlayer_mul : (((u.1.val : ℕ) : ℝ) + 1) * (1 + η) ≤
      ((v.1.val : ℕ) : ℝ) * (1 + η) :=
    mul_le_mul_of_nonneg_right hstep_real h1η
  have hub : ((u.2.2.val : ℕ) : ℝ) * b ≤ ((4 * q ^ 2 : ℕ) : ℝ) * b :=
    mul_le_mul_of_nonneg_right (rect_y_le u.2) hb.le
  have hvb : 0 ≤ ((v.2.2.val : ℕ) : ℝ) * b := by positivity
  simp only [fourLayerCenter_one]
  linarith

theorem fourLayerCenter_injective (q : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hlayer : ((4 * q ^ 2 : ℕ) : ℝ) * b < 1) :
    Function.Injective (fourLayerCenter q a b η) := by
  intro u v huv
  have hx : ((u.2.1.val : ℕ) : ℝ) * a = ((v.2.1.val : ℕ) : ℝ) * a := by
    simpa [fourLayerCenter] using congrArg (fun z : Plane => z 0) huv
  have hy : (fourLayerCenter q a b η u) 1 = (fourLayerCenter q a b η v) 1 :=
    congrArg (fun z : Plane => z 1) huv
  have hlayer_eq : u.1 = v.1 := by
    by_contra hne
    have hval_ne : u.1.val ≠ v.1.val := fun he => hne (Fin.ext he)
    rcases lt_or_gt_of_ne hval_ne with hlt | hgt
    · have hgap := cross_layer_vertical_gt u v hlt a b η hb hη hlayer
      linarith
    · have hgap := cross_layer_vertical_gt v u hgt a b η hb hη hlayer
      linarith
  have hpx : u.2.1 = v.2.1 := by
    apply Fin.ext
    exact_mod_cast (mul_right_cancel₀ (ne_of_gt ha) hx)
  have hpy : u.2.2 = v.2.2 := by
    apply Fin.ext
    simp only [fourLayerCenter_one, hlayer_eq] at hy
    have hmul : ((u.2.2.val : ℕ) : ℝ) * b = ((v.2.2.val : ℕ) : ℝ) * b := by linarith
    exact_mod_cast (mul_right_cancel₀ (ne_of_gt hb) hmul)
  exact Prod.ext hlayer_eq (Prod.ext hpx hpy)

noncomputable def fourLayerCenters (q : ℕ) (a b η : ℝ) : Finset Plane :=
  Finset.univ.image (fourLayerCenter q a b η)

theorem fourLayerCenters_card (q : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hlayer : ((4 * q ^ 2 : ℕ) : ℝ) * b < 1) :
    (fourLayerCenters q a b η).card = fourLayerSize q := by
  unfold fourLayerCenters
  rw [Finset.card_image_iff.mpr (fun _ _ _ _ h =>
    fourLayerCenter_injective q a b η ha hb hη hlayer h)]
  simpa using fourLayerIndex_card q

theorem fourLayerCenter_x_bounds {q : ℕ} (idx : FourLayerIndex q)
    (a b η : ℝ) (ha : 0 ≤ a) :
    0 ≤ (fourLayerCenter q a b η idx) 0 ∧
      (fourLayerCenter q a b η idx) 0 ≤ ((3 * q : ℕ) : ℝ) * a := by
  simp only [fourLayerCenter_zero]
  exact ⟨by positivity, mul_le_mul_of_nonneg_right (rect_x_le idx.2) ha⟩

private theorem cast_mul_gap {u v : ℕ} (huv : u ≠ v) (a : ℝ) (ha : 0 < a) :
    a ≤ |(u : ℝ) * a - (v : ℝ) * a| := by
  rcases lt_or_gt_of_ne huv with huv | huv
  · have hnat : u + 1 ≤ v := by omega
    have hreal : (u : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal (le_of_lt ha)
    have hsub : (u : ℝ) * a - (v : ℝ) * a ≤ -a := by nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hnat : v + 1 ≤ u := by omega
    have hreal : (v : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal (le_of_lt ha)
    have hsub : a ≤ (u : ℝ) * a - (v : ℝ) * a := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    exact hsub

theorem fourLayer_pair_difference_outside_box {q : ℕ}
    (u v : FourLayerIndex q) (huv : u ≠ v)
    (a b η W : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hhorizontal : W ^ 3 / 2 < a) (hvertical : η < b)
    (hlayer : ((4 * q ^ 2 : ℕ) : ℝ) * b < 1) :
    W ^ 3 / 2 < |(fourLayerCenter q a b η v - fourLayerCenter q a b η u) 0| ∨
      η < |(fourLayerCenter q a b η v - fourLayerCenter q a b η u) 1| := by
  by_cases hx : u.2.1.val ≠ v.2.1.val
  · left
    simp only [PiLp.sub_apply, fourLayerCenter_zero]
    exact hhorizontal.trans_le (cast_mul_gap hx.symm a ha)
  · have hxsame : u.2.1 = v.2.1 := Fin.ext (not_ne_iff.mp hx)
    right
    by_cases hl : u.1.val ≠ v.1.val
    · rcases lt_or_gt_of_ne hl with hlt | hgt
      · have hgap := cross_layer_vertical_gt u v hlt a b η hb hη hlayer
        simp only [PiLp.sub_apply]
        rw [abs_of_pos (lt_of_le_of_lt hη hgap)]
        exact hgap
      · have hgap := cross_layer_vertical_gt v u hgt a b η hb hη hlayer
        simp only [PiLp.sub_apply]
        have hneg : (fourLayerCenter q a b η v) 1 - (fourLayerCenter q a b η u) 1 =
            -((fourLayerCenter q a b η u) 1 - (fourLayerCenter q a b η v) 1) := by ring
        rw [hneg, abs_neg, abs_of_pos (lt_of_le_of_lt hη hgap)]
        exact hgap
    · have hlsame : u.1 = v.1 := Fin.ext (not_ne_iff.mp hl)
      have hyne : u.2.2.val ≠ v.2.2.val := by
        intro hyeq
        exact huv (Prod.ext hlsame (Prod.ext hxsame (Fin.ext hyeq)))
      simp only [PiLp.sub_apply, fourLayerCenter_one, hlsame]
      have hcancel :
          (((v.1.val : ℕ) : ℝ) * (1 + η) + ((v.2.2.val : ℕ) : ℝ) * b) -
            (((v.1.val : ℕ) : ℝ) * (1 + η) + ((u.2.2.val : ℕ) : ℝ) * b) =
          ((v.2.2.val : ℕ) : ℝ) * b - ((u.2.2.val : ℕ) : ℝ) * b := by ring
      rw [hcancel]
      exact hvertical.trans_le (cast_mul_gap hyne.symm b hb)

theorem fourLayerCenters_diff_not_mem_of_box {q : ℕ}
    (D : Set Plane) (hbox : ∀ z ∈ D, |z 0| ≤ W ^ 3 / 2 ∧ |z 1| ≤ η)
    {x y : Plane} (hx : x ∈ fourLayerCenters q a b η)
    (hy : y ∈ fourLayerCenters q a b η) (hxy : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hhorizontal : W ^ 3 / 2 < a) (hvertical : η < b)
    (hlayer : ((4 * q ^ 2 : ℕ) : ℝ) * b < 1) :
    y - x ∉ D := by
  intro hmem
  have hbound := hbox (y - x) hmem
  rcases Finset.mem_image.mp hx with ⟨u, -, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨v, -, rfl⟩
  have huv : u ≠ v := fun he => hxy (he ▸ rfl)
  rcases fourLayer_pair_difference_outside_box u v huv a b η W
      ha hb hη hhorizontal hvertical hlayer with h | h
  · exact not_lt_of_ge hbound.1 h
  · exact not_lt_of_ge hbound.2 h

/-- Exact evaluation of the four-layer signed-shift sum:
`3 ((3q + 1)(4q^2 + 1) + 2 ∑_{i=0}^{2q-1} (3q - i)(4q^2 + 1 - (i + 1)^2)) = 72q^4 + 32q^3 + 24q^2 + 13q + 3`. -/
theorem fourLayer_sum_polynomial (q : ℕ) :
    3 * ((3 * q + 1) * (4 * q ^ 2 + 1) +
      2 * (∑ i ∈ Finset.range (2 * q), (3 * q - i) * (4 * q ^ 2 + 1 - (i + 1) ^ 2))) =
      72 * q ^ 4 + 32 * q ^ 3 + 24 * q ^ 2 + 13 * q + 3 := by
  have hind : ∀ (m L : ℤ) (K : ℕ),
      12 * (∑ i ∈ Finset.range K, (m - (i : ℤ)) * (L + 1 - ((i : ℤ) + 1) ^ 2)) =
        12 * m * (L + 1) * (K : ℤ)
        - 2 * m * (K : ℤ) * ((K : ℤ) + 1) * (2 * (K : ℤ) + 1)
        - 6 * (L + 1) * (K : ℤ) * ((K : ℤ) - 1)
        + 3 * (K : ℤ) ^ 2 * ((K : ℤ) + 1) ^ 2
        - 2 * (K : ℤ) * ((K : ℤ) + 1) * (2 * (K : ℤ) + 1) := by
    intro m L K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        push_cast
        ring
  have hcast_sum :
      ((∑ i ∈ Finset.range (2 * q), (3 * q - i) * (4 * q ^ 2 + 1 - (i + 1) ^ 2) : ℕ) : ℤ) =
        ∑ i ∈ Finset.range (2 * q),
          ((3 * (q : ℤ)) - (i : ℤ)) * (4 * (q : ℤ) ^ 2 + 1 - ((i : ℤ) + 1) ^ 2) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < 2 * q := Finset.mem_range.mp hi
    have h1 : i ≤ 3 * q := by omega
    have h2 : (i + 1) ^ 2 ≤ 4 * q ^ 2 + 1 := by
      have hle : i + 1 ≤ 2 * q := by omega
      nlinarith
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    push_cast
    ring
  have h12 := hind (3 * (q : ℤ)) (4 * (q : ℤ) ^ 2) (2 * q)
  rw [← hcast_sum] at h12
  have hmain_int :
      2 * ((3 * ((3 * q + 1) * (4 * q ^ 2 + 1) +
        2 * (∑ i ∈ Finset.range (2 * q), (3 * q - i) * (4 * q ^ 2 + 1 - (i + 1) ^ 2))) : ℕ) : ℤ) =
      2 * ((72 * q ^ 4 + 32 * q ^ 3 + 24 * q ^ 2 + 13 * q + 3 : ℕ) : ℤ) := by
    push_cast at h12 ⊢
    linarith
  have hmain_nat :
      2 * (3 * ((3 * q + 1) * (4 * q ^ 2 + 1) +
        2 * (∑ i ∈ Finset.range (2 * q), (3 * q - i) * (4 * q ^ 2 + 1 - (i + 1) ^ 2)))) =
      2 * (72 * q ^ 4 + 32 * q ^ 3 + 24 * q ^ 2 + 13 * q + 3) := by
    exact_mod_cast hmain_int
  omega

abbrev ZeroShiftEdge (q : ℕ) :=
  Fin (3 * q + 1) × Fin (4 * q ^ 2 + 1)

abbrev PosShiftEdge (q : ℕ) :=
  Σ i : Fin (2 * q),
    Fin (3 * q - i.val) × Fin (4 * q ^ 2 + 1 - (i.val + 1) ^ 2)

abbrev LayerPairEdge (q : ℕ) :=
  Sum (ZeroShiftEdge q) (Sum (PosShiftEdge q) (PosShiftEdge q))

abbrev FourLayerEdgeIndex (q : ℕ) :=
  Fin 3 × LayerPairEdge q

theorem fourLayerEdgeIndex_card (q : ℕ) :
    Fintype.card (FourLayerEdgeIndex q) = fourLayerEdgePoly q := by
  have hsum :
      (∑ i : Fin (2 * q), (3 * q - i.val) * (4 * q ^ 2 + 1 - (i.val + 1) ^ 2)) =
        ∑ i ∈ Finset.range (2 * q), (3 * q - i) * (4 * q ^ 2 + 1 - (i + 1) ^ 2) :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => (3 * q - i) * (4 * q ^ 2 + 1 - (i + 1) ^ 2)) (2 * q)
  have hcard : Fintype.card (FourLayerEdgeIndex q) =
      3 * ((3 * q + 1) * (4 * q ^ 2 + 1) +
        2 * (∑ i ∈ Finset.range (2 * q), (3 * q - i) * (4 * q ^ 2 + 1 - (i + 1) ^ 2))) := by
    simp only [FourLayerEdgeIndex, LayerPairEdge, ZeroShiftEdge, PosShiftEdge,
      Fintype.card_prod, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    rw [hsum]
    ring
  rw [hcard, fourLayerEdgePoly]
  exact fourLayer_sum_polynomial q

private theorem posShift_x_lt {q : ℕ} (p : PosShiftEdge q) :
    p.2.1.val < 3 * q + 1 ∧ p.2.1.val + (p.1.val + 1) < 3 * q + 1 := by
  have hi : p.1.val < 2 * q := p.1.isLt
  have hr : p.2.1.val < 3 * q - p.1.val := p.2.1.isLt
  omega

private theorem posShift_y_lt {q : ℕ} (p : PosShiftEdge q) :
    p.2.2.val < 4 * q ^ 2 + 1 ∧
      p.2.2.val + (p.1.val + 1) ^ 2 < 4 * q ^ 2 + 1 := by
  have hi : p.1.val + 1 ≤ 2 * q := by
    have h := p.1.isLt
    omega
  have hsq : (p.1.val + 1) ^ 2 ≤ 4 * q ^ 2 := by nlinarith
  have hs : p.2.2.val < 4 * q ^ 2 + 1 - (p.1.val + 1) ^ 2 := p.2.2.isLt
  omega

def lowerRect {q : ℕ} : LayerPairEdge q → FourLayerRect q
  | .inl rs => rs
  | .inr (.inl p) =>
      (⟨p.2.1.val, (posShift_x_lt p).1⟩,
       ⟨p.2.2.val + (p.1.val + 1) ^ 2, (posShift_y_lt p).2⟩)
  | .inr (.inr p) =>
      (⟨p.2.1.val + (p.1.val + 1), (posShift_x_lt p).2⟩,
       ⟨p.2.2.val + (p.1.val + 1) ^ 2, (posShift_y_lt p).2⟩)

def upperRect {q : ℕ} : LayerPairEdge q → FourLayerRect q
  | .inl rs => rs
  | .inr (.inl p) =>
      (⟨p.2.1.val + (p.1.val + 1), (posShift_x_lt p).2⟩,
       ⟨p.2.2.val, (posShift_y_lt p).1⟩)
  | .inr (.inr p) =>
      (⟨p.2.1.val, (posShift_x_lt p).1⟩,
       ⟨p.2.2.val, (posShift_y_lt p).1⟩)

def layerPairShift {q : ℕ} : LayerPairEdge q → ℤ
  | .inl _ => 0
  | .inr (.inl p) => ((p.1.val + 1 : ℕ) : ℤ)
  | .inr (.inr p) => -((p.1.val + 1 : ℕ) : ℤ)

theorem layerPairShift_bounds {q : ℕ} (lp : LayerPairEdge q) :
    -(3 * q : ℤ) ≤ layerPairShift lp ∧ layerPairShift lp ≤ (3 * q : ℤ) := by
  rcases lp with rs | (p | p)
  · simp [layerPairShift]
  · dsimp [layerPairShift]
    have hi : p.1.val < 2 * q := p.1.isLt
    omega
  · dsimp [layerPairShift]
    have hi : p.1.val < 2 * q := p.1.isLt
    omega

private theorem posShiftEdge_eq_of_coords {q : ℕ} (p p' : PosShiftEdge q)
    (hr : p.2.1.val = p'.2.1.val)
    (hi : p.1.val = p'.1.val)
    (hs : p.2.2.val = p'.2.2.val) : p = p' := by
  rcases p with ⟨i, r, s⟩
  rcases p' with ⟨i', r', s'⟩
  dsimp at hr hi hs
  have hi_eq : i = i' := Fin.ext hi
  subst hi_eq
  exact Sigma.ext rfl (by
    simp only [heq_eq_eq, Prod.mk.injEq]
    exact ⟨Fin.ext hr, Fin.ext hs⟩)

theorem layerPair_rects_injective (q : ℕ) :
    Function.Injective (fun lp : LayerPairEdge q => (lowerRect lp, upperRect lp)) := by
  intro lp1 lp2 h
  have hl : lowerRect lp1 = lowerRect lp2 := congrArg Prod.fst h
  have hu : upperRect lp1 = upperRect lp2 := congrArg Prod.snd h
  have hlx : (lowerRect lp1).1.val = (lowerRect lp2).1.val := congrArg (fun r => r.1.val) hl
  have hux : (upperRect lp1).1.val = (upperRect lp2).1.val := congrArg (fun r => r.1.val) hu
  have huy : (upperRect lp1).2.val = (upperRect lp2).2.val := congrArg (fun r => r.2.val) hu
  rcases lp1 with rs1 | (p1 | p1) <;> rcases lp2 with rs2 | (p2 | p2)
  · exact congrArg Sum.inl hl
  · dsimp [lowerRect, upperRect] at hlx hux; omega
  · dsimp [lowerRect, upperRect] at hlx hux; omega
  · dsimp [lowerRect, upperRect] at hlx hux; omega
  · dsimp [lowerRect, upperRect] at hlx hux huy
    exact congrArg (Sum.inr ∘ Sum.inl)
      (posShiftEdge_eq_of_coords p1 p2 hlx (by omega) huy)
  · dsimp [lowerRect, upperRect] at hlx hux; omega
  · dsimp [lowerRect, upperRect] at hlx hux; omega
  · dsimp [lowerRect, upperRect] at hlx hux; omega
  · dsimp [lowerRect, upperRect] at hlx hux huy
    exact congrArg (Sum.inr ∘ Sum.inr)
      (posShiftEdge_eq_of_coords p1 p2 hux (by omega) huy)

def fourLayerIndexedEdge {q : ℕ} (e : FourLayerEdgeIndex q) :
    FourLayerIndex q × FourLayerIndex q :=
  ((⟨e.1.val, by omega⟩, lowerRect e.2),
   (⟨e.1.val + 1, by omega⟩, upperRect e.2))

theorem fourLayerIndexedEdge_injective (q : ℕ) :
    Function.Injective (@fourLayerIndexedEdge q) := by
  intro e1 e2 h
  have hl : (fourLayerIndexedEdge e1).1 = (fourLayerIndexedEdge e2).1 :=
    congrArg Prod.fst h
  have hu : (fourLayerIndexedEdge e1).2 = (fourLayerIndexedEdge e2).2 :=
    congrArg Prod.snd h
  have hj : e1.1 = e2.1 := by
    apply Fin.ext
    exact congrArg (fun idx : FourLayerIndex q => idx.1.val) hl
  have hlow : lowerRect e1.2 = lowerRect e2.2 := congrArg Prod.snd hl
  have hupp : upperRect e1.2 = upperRect e2.2 := congrArg Prod.snd hu
  have hrects : (lowerRect e1.2, upperRect e1.2) = (lowerRect e2.2, upperRect e2.2) :=
    Prod.ext hlow hupp
  exact Prod.ext hj (layerPair_rects_injective q hrects)

def fourLayerPlaneEdge (q : ℕ) (a b η : ℝ) (e : FourLayerEdgeIndex q) :
    Plane × Plane :=
  (fourLayerCenter q a b η (fourLayerIndexedEdge e).1,
   fourLayerCenter q a b η (fourLayerIndexedEdge e).2)

noncomputable def fourLayerUnorderedEdge (q : ℕ) (a b η : ℝ)
    (e : FourLayerEdgeIndex q) : Finset Plane := by
  classical
  exact {(fourLayerPlaneEdge q a b η e).1, (fourLayerPlaneEdge q a b η e).2}

theorem fourLayerUnorderedEdge_injective (q : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hlayer : ((4 * q ^ 2 : ℕ) : ℝ) * b < 1) :
    Function.Injective (fourLayerUnorderedEdge q a b η) := by
  classical
  intro e1 e2 heq
  have hinj := fourLayerCenter_injective q a b η ha hb hη hlayer
  let u1 := (fourLayerIndexedEdge e1).1
  let u2 := (fourLayerIndexedEdge e1).2
  let v1 := (fourLayerIndexedEdge e2).1
  let v2 := (fourLayerIndexedEdge e2).2
  have hmem1 : fourLayerCenter q a b η u1 ∈
      ({fourLayerCenter q a b η v1, fourLayerCenter q a b η v2} : Finset Plane) := by
    change fourLayerCenter q a b η u1 ∈ fourLayerUnorderedEdge q a b η e2
    rw [← heq]
    exact Finset.mem_insert_self _ _
  have hmem2 : fourLayerCenter q a b η u2 ∈
      ({fourLayerCenter q a b η v1, fourLayerCenter q a b η v2} : Finset Plane) := by
    change fourLayerCenter q a b η u2 ∈ fourLayerUnorderedEdge q a b η e2
    rw [← heq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hu1 : u1 = v1 ∨ u1 = v2 := by
    rcases Finset.mem_insert.mp hmem1 with h | h
    · exact Or.inl (hinj h)
    · exact Or.inr (hinj (Finset.mem_singleton.mp h))
  have hu2 : u2 = v1 ∨ u2 = v2 := by
    rcases Finset.mem_insert.mp hmem2 with h | h
    · exact Or.inl (hinj h)
    · exact Or.inr (hinj (Finset.mem_singleton.mp h))
  have hu1_layer : u1.1.val = e1.1.val := rfl
  have hu2_layer : u2.1.val = e1.1.val + 1 := rfl
  have hv1_layer : v1.1.val = e2.1.val := rfl
  have hv2_layer : v2.1.val = e2.1.val + 1 := rfl
  rcases hu1 with h11 | h12 <;> rcases hu2 with h21 | h22
  · have h1 := congrArg (fun idx : FourLayerIndex q => idx.1.val) h11
    have h2 := congrArg (fun idx : FourLayerIndex q => idx.1.val) h21
    omega
  · exact fourLayerIndexedEdge_injective q (Prod.ext h11 h22)
  · have h1 := congrArg (fun idx : FourLayerIndex q => idx.1.val) h12
    have h2 := congrArg (fun idx : FourLayerIndex q => idx.1.val) h21
    omega
  · have h1 := congrArg (fun idx : FourLayerIndex q => idx.1.val) h12
    have h2 := congrArg (fun idx : FourLayerIndex q => idx.1.val) h22
    omega

noncomputable def fourLayerUnorderedEdges (q : ℕ) (a b η : ℝ) :
    Finset (Finset Plane) := by
  classical
  exact Finset.univ.image (fourLayerUnorderedEdge q a b η)

/-- The four-layer signed grid has `J_q = 72q^4 + 32q^3 + 24q^2 + 13q + 3`
distinct unordered edges. -/
theorem fourLayerUnorderedEdges_card (q : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hlayer : ((4 * q ^ 2 : ℕ) : ℝ) * b < 1) :
    (fourLayerUnorderedEdges q a b η).card = fourLayerEdgePoly q := by
  classical
  unfold fourLayerUnorderedEdges
  rw [Finset.card_image_iff.mpr (fun _ _ _ _ h =>
    fourLayerUnorderedEdge_injective q a b η ha hb hη hlayer h)]
  simpa using fourLayerEdgeIndex_card q

theorem fourLayerPlaneEdge_difference {q : ℕ} (e : FourLayerEdgeIndex q)
    (a b η : ℝ) (hb : b = a ^ 2 / 2) :
    (fourLayerPlaneEdge q a b η e).2 - (fourLayerPlaneEdge q a b η e).1 =
      Geometry.gamma η ((layerPairShift e.2 : ℝ) * a) := by
  rcases e with ⟨j, rs | (p | p)⟩ <;>
  ext coord <;>
  fin_cases coord <;>
  simp [PiLp.sub_apply, fourLayerPlaneEdge, fourLayerIndexedEdge,
    hb, lowerRect, upperRect, layerPairShift] <;>
  ring

noncomputable def signedBody (q : ℕ) : Set Plane :=
  Geometry.D (Parameters.eta (3 * q)) (Parameters.signedT (3 * q))

private theorem scale3q_pos (q : ℕ) (hq : 1 ≤ q) : 1 ≤ 3 * q := by omega

private theorem signedBody_box (q : ℕ) (hq : 1 ≤ q) :
    ∀ z ∈ signedBody q,
      |z 0| ≤ (Parameters.W (3 * q)) ^ 3 / 2 ∧
      |z 1| ≤ Parameters.eta (3 * q) := by
  have hk := scale3q_pos q hq
  have hW0 : 0 ≤ Parameters.W (3 * q) := (Parameters.W_pos (3 * q) hk).le
  have hW1 : Parameters.W (3 * q) ≤ 1 := Parameters.W_le_one (3 * q) hk
  have hT : ∀ t ∈ Parameters.signedT (3 * q),
      -Parameters.W (3 * q) ≤ t ∧ t ≤ Parameters.W (3 * q) :=
    fun _ ht => Parameters.mem_signedT_range (3 * q) hk ht
  exact Geometry.D_abs_box_signed (Parameters.W (3 * q))
    (Parameters.signedT (3 * q)) hW0 hW1 hT

private theorem signedBody_symmetric (q : ℕ) :
    ∀ z ∈ signedBody q, -z ∈ signedBody q := by
  intro z hz
  change -z ∈ Geometry.D (Parameters.eta (3 * q)) (Parameters.signedT (3 * q))
  rw [← Geometry.D_neg_eq (Parameters.eta (3 * q)) (Parameters.signedT (3 * q))]
  exact Set.neg_mem_neg.mpr hz

private theorem fourLayer_height_lt_one (q : ℕ) (hq : 1 ≤ q) :
    ((4 * q ^ 2 : ℕ) : ℝ) * Parameters.b (3 * q) < 1 := by
  have hk := scale3q_pos q hq
  have hb := Parameters.b_pos (3 * q) hk
  have hgrid := Parameters.grid_height_lt_one (3 * q) hk
  have hle_nat : 4 * q ^ 2 ≤ (3 * q) ^ 2 := by nlinarith
  have hle_real : ((4 * q ^ 2 : ℕ) : ℝ) ≤ ((3 * q : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hle_nat
  have hmul := mul_le_mul_of_nonneg_right hle_real hb.le
  linarith

private theorem fourLayer_edge_distance_one (q : ℕ) (hq : 1 ≤ q)
    (e : FourLayerEdgeIndex q) :
    Erdos956.translateSetDistance
      ((1 / 2 : ℝ) • signedBody q)
      (fourLayerPlaneEdge q
        (Parameters.a (3 * q)) (Parameters.b (3 * q))
        (Parameters.eta (3 * q)) e).1
      (fourLayerPlaneEdge q
        (Parameters.a (3 * q)) (Parameters.b (3 * q))
        (Parameters.eta (3 * q)) e).2 = 1 := by
  let k := 3 * q
  let W := Parameters.W k
  let a := Parameters.a k
  let b := Parameters.b k
  let η := Parameters.eta k
  let T := Parameters.signedT k
  let t : ℝ := (layerPairShift e.2 : ℝ) * a
  let edge := fourLayerPlaneEdge q a b η e
  have hk : 1 ≤ k := scale3q_pos q hq
  have hshift := layerPairShift_bounds e.2
  have ht : t ∈ T := Parameters.int_step_mem_signedT k (layerPairShift e.2)
    (by dsimp [k]; omega) (by dsimp [k]; omega)
  have hW0 : 0 ≤ W := (Parameters.W_pos k hk).le
  have hW1 : W ≤ 1 := Parameters.W_le_one k hk
  have hT : ∀ s ∈ T, -W ≤ s ∧ s ≤ W :=
    fun _ hs => Parameters.mem_signedT_range k hk hs
  have hdiff : edge.2 - edge.1 = Geometry.gamma η t :=
    fourLayerPlaneEdge_difference e a b η rfl
  have hp : Geometry.p η t ∈ signedBody q := Geometry.p_mem_D η T t ht
  have hDist : Metric.infDist (Geometry.gamma η t) (signedBody q) = 1 :=
    Geometry.D_unit_distance_signed W T hW0 hW1 hT t ht
  have hclose : dist (Geometry.gamma η t) (Geometry.p η t) = 1 := by
    rw [dist_eq_norm, Geometry.gamma_sub_p, Geometry.normal_norm_one]
  change translateSetDistance ((1 / 2 : ℝ) • signedBody q) edge.1 edge.2 = 1
  exact translateSetDistance_one_of_body (signedBody q)
    (Geometry.D_convex _ _) (signedBody_symmetric q) hp hdiff hDist hclose

private theorem signedHalfBody_interior_nonempty (q : ℕ) (hq : 1 ≤ q) :
    (interior ((1 / 2 : ℝ) • signedBody q)).Nonempty := by
  let k := 3 * q
  let W := Parameters.W k
  let T := Parameters.signedT k
  have hk : 1 ≤ k := scale3q_pos q hq
  have hW : 0 < W := Parameters.W_pos k hk
  have h0 : (0 : ℝ) ∈ T := by
    have h := Parameters.int_step_mem_signedT k 0 (by omega) (by omega)
    simpa [T] using h
  have hWT : W ∈ T := by
    have h := Parameters.int_step_mem_signedT k (k : ℤ) (by omega) (by omega)
    have hka : ((k : ℤ) : ℝ) * Parameters.a k = W := by
      dsimp [W, Parameters.a]
      have hknz : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      push_cast
      field_simp [hknz]
    rwa [hka] at h
  change (interior ((1 / 2 : ℝ) • Geometry.D (W ^ 4) T)).Nonempty
  exact Geometry.half_D_interior_nonempty W T hW h0 hWT

/-- For every scale `q ≥ 1` and every `N ≥ fourLayerSize q`, the padded four-layer
signed-grid construction yields a valid `Specification.Configuration N` with
`fourLayerEdgePoly q = 72q^4 + 32q^3 + 24q^2 + 13q + 3` unordered unit-distance pairs. -/
noncomputable def fourLayerConfiguration (q N : ℕ) (hq : 1 ≤ q)
    (hgrid : fourLayerSize q ≤ N) :
    Specification.Configuration N := by
  classical
  let k := 3 * q
  let a := Parameters.a k
  let b := Parameters.b k
  let η := Parameters.eta k
  let C : Set Plane := (1 / 2 : ℝ) • signedBody q
  let X₀ : Finset Plane := fourLayerCenters q a b η
  let X : Finset Plane := Padding.paddedCenters X₀ (N - X₀.card)
  let E : Finset (Finset Plane) := fourLayerUnorderedEdges q a b η
  have hk : 1 ≤ k := scale3q_pos q hq
  have ha : 0 < a := Parameters.a_pos k hk
  have hb : 0 < b := Parameters.b_pos k hk
  have hη : 0 < η := Parameters.eta_pos k hk
  have hlayer : ((4 * q ^ 2 : ℕ) : ℝ) * b < 1 := fourLayer_height_lt_one q hq
  have hX₀_card : X₀.card = fourLayerSize q :=
    fourLayerCenters_card q a b η ha hb hη.le hlayer
  have hbounds : ∀ x ∈ X₀, 0 ≤ x 0 ∧ x 0 ≤ 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨idx, -, rfl⟩
    have hb0 := fourLayerCenter_x_bounds idx a b η ha.le
    have hka : ((3 * q : ℕ) : ℝ) * a = Parameters.W k := by
      dsimp [a, Parameters.a, k]
      have hknz : (3 * q : ℝ) ≠ 0 := by exact_mod_cast (by omega : 3 * q ≠ 0)
      push_cast
      field_simp [hknz]
    rw [hka] at hb0
    exact ⟨hb0.1, hb0.2.trans (Parameters.W_le_one k hk)⟩
  have hXlow : ∀ x ∈ X₀, 0 ≤ x 0 := fun x hx => (hbounds x hx).1
  have hXhigh : ∀ x ∈ X₀, x 0 ≤ 1 := fun x hx => (hbounds x hx).2
  have hXle : X₀.card ≤ N := by rw [hX₀_card]; exact hgrid
  have hXcard : X.card = N := Padding.paddedCenters_card_exact X₀ hXhigh hXle
  have hDhalf : ∀ z ∈ signedBody q, |z 0| ≤ 1 / 2 := by
    intro z hz
    have hbox := (signedBody_box q hq) z hz
    let W := Parameters.W k
    have hW0 : 0 ≤ W := (Parameters.W_pos k hk).le
    have hW1 : W ≤ 1 := Parameters.W_le_one k hk
    have hW3 : W ^ 3 ≤ 1 := by
      nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hW1),
        mul_nonneg (sq_nonneg W) (sub_nonneg.mpr hW1)]
    dsimp [W, k] at hW3
    linarith [hbox.1]
  have hold_diff : ∀ x ∈ X₀, ∀ y ∈ X₀, x ≠ y → y - x ∉ signedBody q := by
    intro x hx y hy hxy
    exact fourLayerCenters_diff_not_mem_of_box (signedBody q)
      (signedBody_box q hq) hx hy hxy ha hb hη.le
      (Parameters.cap_width_lt_a k hk) (Parameters.eta_lt_b k hk) hlayer
  have hdiff : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → y - x ∉ signedBody q :=
    Padding.padded_differences_excluded (signedBody q) X₀ (N - X₀.card)
      hDhalf hXlow hXhigh hold_diff
  have hCnonempty : C.Nonempty := by
    have h0 : (0 : ℝ) ∈ Parameters.signedT k := by
      have h := Parameters.int_step_mem_signedT k 0 (by omega) (by omega)
      simpa using h
    obtain ⟨z, hz⟩ := Geometry.D_nonempty _ _ ⟨0, h0⟩
    exact ⟨(1 / 2 : ℝ) • z, Set.smul_mem_smul_set hz⟩
  refine {
    C := C
    compact := half_body_isCompact (signedBody q) (Geometry.D_compact _ _)
    convex := half_body_convex (signedBody q) (Geometry.D_convex _ _)
    nonempty := hCnonempty
    interior_nonempty := signedHalfBody_interior_nonempty q hq
    X := X
    cardinality := hXcard
    disjoint := ?_
    edges := E
    edges_good := ?_
  }
  · intro x hx y hy hne
    exact half_body_translates_disjoint_of_diff_not_mem (signedBody q)
      (Geometry.D_convex _ _) (signedBody_symmetric q) (hdiff x hx y hy hne)
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨e, -, rfl⟩
    let p := fourLayerPlaneEdge q a b η e
    have hx0 : p.1 ∈ X₀ := Finset.mem_image.mpr ⟨(fourLayerIndexedEdge e).1, Finset.mem_univ _, rfl⟩
    have hy0 : p.2 ∈ X₀ := Finset.mem_image.mpr ⟨(fourLayerIndexedEdge e).2, Finset.mem_univ _, rfl⟩
    have hne : p.1 ≠ p.2 := by
      intro heq
      have hidx := fourLayerCenter_injective q a b η ha hb hη.le hlayer heq
      have hl := congrArg (fun idx : FourLayerIndex q => idx.1.val) hidx
      dsimp [fourLayerIndexedEdge] at hl
      omega
    refine ⟨p.1, p.2, hne, rfl, Finset.mem_union_left _ hx0,
      Finset.mem_union_left _ hy0, fourLayer_edge_distance_one q hq e⟩

theorem fourLayerConfiguration_edges_card (q N : ℕ) (hq : 1 ≤ q)
    (hgrid : fourLayerSize q ≤ N) :
    (fourLayerConfiguration q N hq hgrid).edges.card = fourLayerEdgePoly q := by
  have hk := scale3q_pos q hq
  exact fourLayerUnorderedEdges_card q
    (Parameters.a (3 * q)) (Parameters.b (3 * q)) (Parameters.eta (3 * q))
    (Parameters.a_pos (3 * q) hk) (Parameters.b_pos (3 * q) hk)
    (Parameters.eta_pos (3 * q) hk).le (fourLayer_height_lt_one q hq)

/-- At every scale `q ≥ 1`, there is an explicit `fourLayerSize q`-translate configuration
with `72q^4 + 32q^3 + 24q^2 + 13q + 3` unordered unit-distance pairs. -/
theorem fourLayer_exact_configuration (q : ℕ) (hq : 1 ≤ q) :
    ∃ config : Specification.Configuration (fourLayerSize q),
      config.edges.card = 72 * q ^ 4 + 32 * q ^ 3 + 24 * q ^ 2 + 13 * q + 3 :=
  ⟨fourLayerConfiguration q (fourLayerSize q) hq (le_refl _),
   fourLayerConfiguration_edges_card q (fourLayerSize q) hq (le_refl _)⟩

/-- The `q = 1` control: 80 disjoint translates with 144 certified unit-distance pairs. -/
theorem fourLayer_q1_configuration :
    ∃ config : Specification.Configuration 80, config.edges.card = 144 := by
  have hgrid : fourLayerSize 1 ≤ 80 := by decide
  refine ⟨fourLayerConfiguration 1 80 (le_refl 1) hgrid, ?_⟩
  rw [fourLayerConfiguration_edges_card 1 80 (le_refl 1) hgrid]
  decide

/-- At every scale `q ≥ 1`, `h(48q^3 + 16q^2 + 12q + 4) ≥ 72q^4 + 32q^3 + 24q^2 + 13q + 3`. -/
theorem h_fourLayer_lower_bound (q : ℕ) (hq : 1 ≤ q) :
    72 * q ^ 4 + 32 * q ^ 3 + 24 * q ^ 2 + 13 * q + 3 ≤
      Extremal.h (48 * q ^ 3 + 16 * q ^ 2 + 12 * q + 4) := by
  let config := fourLayerConfiguration q (fourLayerSize q) hq (le_refl _)
  have hcard := fourLayerConfiguration_edges_card q (fourLayerSize q) hq (le_refl _)
  have hle := Extremal.configuration_edges_le_h config
  rwa [hcard, fourLayerEdgePoly, fourLayerSize] at hle

theorem h_80_ge_144 : 144 ≤ Extremal.h 80 := by
  simpa using h_fourLayer_lower_bound 1 (le_refl 1)

theorem scale_lt_fourLayerSize (q : ℕ) : q < fourLayerSize q := by
  unfold fourLayerSize
  omega

def chosenFourLayerScale (N : ℕ) : ℕ :=
  Nat.findGreatest (fun q => fourLayerSize q ≤ N) N

theorem chosenFourLayerScale_bounds_from_80 (N : ℕ) (hN : 80 ≤ N) :
    1 ≤ chosenFourLayerScale N ∧
      fourLayerSize (chosenFourLayerScale N) ≤ N ∧
      N < fourLayerSize (chosenFourLayerScale N + 1) := by
  let q := chosenFourLayerScale N
  have h80 : fourLayerSize 1 ≤ N := by
    rw [fourLayerSize_one]; exact hN
  have hstart : 1 ≤ N := by omega
  have h1 : 1 ≤ q := by
    dsimp [q, chosenFourLayerScale]
    exact Nat.le_findGreatest hstart h80
  have hq : fourLayerSize q ≤ N := by
    change fourLayerSize (Nat.findGreatest (fun t => fourLayerSize t ≤ N) N) ≤ N
    exact Nat.findGreatest_spec (P := fun t => fourLayerSize t ≤ N) hstart h80
  have hlt : q < N := lt_of_lt_of_le (scale_lt_fourLayerSize q) hq
  have hnext : N < fourLayerSize (q + 1) := by
    have hnot : ¬ fourLayerSize (q + 1) ≤ N := by
      change ¬ fourLayerSize (chosenFourLayerScale N + 1) ≤ N
      apply Nat.findGreatest_is_greatest (P := fun t => fourLayerSize t ≤ N)
      · change chosenFourLayerScale N < chosenFourLayerScale N + 1
        omega
      · omega
    omega
  exact ⟨h1, hq, hnext⟩

/-- For every scale `q = t + 1 ≥ 1`, `(fourLayerSize (q + 1))^4 < (26 * fourLayerEdgePoly q)^3`. -/
theorem fourLayer_26_cube_gt_next_size_fourth (q : ℕ) (hq : 1 ≤ q) :
    (fourLayerSize (q + 1)) ^ 4 < (26 * fourLayerEdgePoly q) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
  let rem : ℕ :=
      205275415552 * t ^ 1
      + 1398053589376 * t ^ 2
      + 4541556246600 * t ^ 3
      + 9188803494848 * t ^ 4
      + 12822333117440 * t ^ 5
      + 12924155190208 * t ^ 6
      + 9577322224640 * t ^ 7
      + 5204678168576 * t ^ 8
      + 2027680622080 * t ^ 9
      + 538071773184 * t ^ 10
      + 87334944768 * t ^ 11
      + 6554898432 * t ^ 12
  have hid :
      (26 * fourLayerEdgePoly (t + 1)) ^ 3 =
        (fourLayerSize (t + 1 + 1)) ^ 4 + 1144971008 + rem := by
    dsimp [fourLayerSize, fourLayerEdgePoly, rem]
    ring
  omega

/-- For every `N ≥ 80`, the padded four-layer signed grid certifies
`(1 / 26) N^(4 / 3) < h(N)`. -/
theorem h_omega_four_thirds_from_80 (N : ℕ) (hN : 80 ≤ N) :
    (1 / 26 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) < (Extremal.h N : ℝ) := by
  obtain ⟨hq1, hgrid, hnext⟩ := chosenFourLayerScale_bounds_from_80 N hN
  let q := chosenFourLayerScale N
  let config := fourLayerConfiguration q N hq1 hgrid
  have hE : config.edges.card = fourLayerEdgePoly q :=
    fourLayerConfiguration_edges_card q N hq1 hgrid
  have hle_h : (fourLayerEdgePoly q : ℝ) ≤ (Extremal.h N : ℝ) := by
    rw [← hE]
    exact_mod_cast Extremal.configuration_edges_le_h config
  have hpow4 : N ^ 4 < (fourLayerSize (q + 1)) ^ 4 := by gcongr
  have h26 := lt_trans hpow4 (fourLayer_26_cube_gt_next_size_fourth q hq1)
  have hR : (N : ℝ) ^ 4 < (26 * (fourLayerEdgePoly q : ℝ)) ^ 3 := by
    exact_mod_cast h26
  have hpow : (((N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3) = (N : ℝ) ^ 4 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N) ((4 : ℝ) / 3) 3]
    norm_num [Real.rpow_natCast]
  have hcube : ((1 / 26 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 <
      ((fourLayerEdgePoly q : ℝ)) ^ 3 := by
    calc
      ((1 / 26 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 =
          (1 / 26 ^ 3 : ℝ) * ((N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 := by ring
      _ = (1 / 26 ^ 3 : ℝ) * (N : ℝ) ^ 4 := by rw [hpow]
      _ < (fourLayerEdgePoly q : ℝ) ^ 3 := by linarith
  have hlt_J : (1 / 26 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) < (fourLayerEdgePoly q : ℝ) := by
    by_contra hnot
    have hle : (fourLayerEdgePoly q : ℝ) ≤ (1 / 26 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) :=
      le_of_not_gt hnot
    have hle3 : ((fourLayerEdgePoly q : ℝ)) ^ 3 ≤
        ((1 / 26 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 := by gcongr
    exact (not_le_of_gt hcube) hle3
  exact lt_of_lt_of_le hlt_J hle_h

theorem next_fourLayerSize_le_49_cube (q : ℕ) (hq : 162 ≤ q) :
    fourLayerSize (q + 1) ≤ 49 * q ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 162 := ⟨q - 162, by omega⟩
  have hid : 49 * (t + 162) ^ 3 =
      fourLayerSize (t + 162 + 1) + (t ^ 3 + 326 * t ^ 2 + 26704 * t + 21952) := by
    unfold fourLayerSize
    ring
  omega

theorem chosenFourLayerScale_bounds (N : ℕ) (hN : fourLayerSize 162 ≤ N) :
    162 ≤ chosenFourLayerScale N ∧
      fourLayerSize (chosenFourLayerScale N) ≤ N ∧
      N < fourLayerSize (chosenFourLayerScale N + 1) := by
  let q := chosenFourLayerScale N
  have hstart : 162 ≤ N := by
    have hlt := scale_lt_fourLayerSize 162
    omega
  have h162 : 162 ≤ q := by
    dsimp [q, chosenFourLayerScale]
    exact Nat.le_findGreatest hstart hN
  have hq : fourLayerSize q ≤ N := by
    change fourLayerSize (Nat.findGreatest (fun t => fourLayerSize t ≤ N) N) ≤ N
    exact Nat.findGreatest_spec (P := fun t => fourLayerSize t ≤ N) hstart hN
  have hlt : q < N := lt_of_lt_of_le (scale_lt_fourLayerSize q) hq
  have hnext : N < fourLayerSize (q + 1) := by
    have hnot : ¬ fourLayerSize (q + 1) ≤ N := by
      change ¬ fourLayerSize (chosenFourLayerScale N + 1) ≤ N
      apply Nat.findGreatest_is_greatest (P := fun t => fourLayerSize t ≤ N)
      · change chosenFourLayerScale N < chosenFourLayerScale N + 1
        omega
      · omega
    omega
  exact ⟨h162, hq, hnext⟩

/-- Pure integer certificate for the sharp `(2/5) N^(4/3)` lower bound from the
four-layer signed grid: for all `N ≥ fourLayerSize 162`, `8 N^4 < 125 J_q^3`. -/
theorem allN_fourLayer_two_fifths_certificate (N : ℕ)
    (hN : fourLayerSize 162 ≤ N) :
    ∃ q : ℕ, 1 ≤ q ∧ fourLayerSize q ≤ N ∧
      8 * N ^ 4 < 125 * (fourLayerEdgePoly q) ^ 3 := by
  obtain ⟨hq162, hgrid, hnext⟩ := chosenFourLayerScale_bounds N hN
  let q := chosenFourLayerScale N
  have hq1 : 1 ≤ q := by omega
  have hcoarse : N < 49 * q ^ 3 :=
    lt_of_lt_of_le hnext (next_fourLayerSize_le_49_cube q hq162)
  have hpow : N ^ 4 < (49 * q ^ 3) ^ 4 := by gcongr
  have hJ : 72 * q ^ 4 < fourLayerEdgePoly q := by
    unfold fourLayerEdgePoly
    omega
  have hJ3 : (72 * q ^ 4) ^ 3 < (fourLayerEdgePoly q) ^ 3 := by gcongr
  refine ⟨q, hq1, hgrid, ?_⟩
  calc
    8 * N ^ 4 < 8 * (49 * q ^ 3) ^ 4 := by omega
    _ = 46118408 * q ^ 12 := by ring
    _ ≤ 46656000 * q ^ 12 :=
      Nat.mul_le_mul_right _ (by norm_num : 46118408 ≤ 46656000)
    _ = 125 * (72 * q ^ 4) ^ 3 := by ring
    _ < 125 * (fourLayerEdgePoly q) ^ 3 := by omega

/-- For every `N ≥ fourLayerSize 162 = 204525328`, the padded four-layer signed-grid
construction certifies `(2/5) N^(4/3) < config.edges.card` (improving the formal
constant from `1/1000` to `2/5`). -/
theorem fourLayer_two_fifths_all_N (N : ℕ) (hN : fourLayerSize 162 ≤ N) :
    ∃ config : Specification.Configuration N,
      (2 / 5 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) < (config.edges.card : ℝ) := by
  obtain ⟨q, hq1, hgrid, hpower⟩ := allN_fourLayer_two_fifths_certificate N hN
  let config := fourLayerConfiguration q N hq1 hgrid
  refine ⟨config, ?_⟩
  have hE : config.edges.card = fourLayerEdgePoly q :=
    fourLayerConfiguration_edges_card q N hq1 hgrid
  rw [hE]
  have hR : 8 * (N : ℝ) ^ 4 < 125 * ((fourLayerEdgePoly q : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast hpower
  have hpow : (((N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3) = (N : ℝ) ^ 4 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N) ((4 : ℝ) / 3) 3]
    norm_num [Real.rpow_natCast]
  have hcube : ((2 / 5 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 <
      (((fourLayerEdgePoly q : ℕ) : ℝ)) ^ 3 := by
    calc
      ((2 / 5 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 =
          (8 / 125 : ℝ) * ((N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 := by ring
      _ = (8 / 125 : ℝ) * (N : ℝ) ^ 4 := by rw [hpow]
      _ < ((fourLayerEdgePoly q : ℕ) : ℝ) ^ 3 := by linarith
  by_contra hnot
  have hle : ((fourLayerEdgePoly q : ℕ) : ℝ) ≤
      (2 / 5 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) := le_of_not_gt hnot
  have hle3 : ((fourLayerEdgePoly q : ℕ) : ℝ) ^ 3 ≤
      ((2 / 5 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 := by gcongr
  exact (not_le_of_gt hcube) hle3

/-- For every `N ≥ fourLayerSize 162`, the extremal function `h(N)` strictly exceeds
`(2/5) N^(4/3)`. -/
theorem h_eventual_two_fifths (N : ℕ) (hN : fourLayerSize 162 ≤ N) :
    (2 / 5 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) < (Extremal.h N : ℝ) := by
  obtain ⟨config, hgt⟩ := fourLayer_two_fifths_all_N N hN
  have hle : (config.edges.card : ℝ) ≤ (Extremal.h N : ℝ) := by
    exact_mod_cast Extremal.configuration_edges_le_h config
  exact lt_of_lt_of_le hgt hle

/-- For every `N ≥ fourLayerSize 162`, `N^(5/4) < h(N)` (answering the highlighted
Erdős–Pach superlinear question with `c = 1/4` directly from the four-layer grid). -/
theorem h_strict_quarter_from_162 (N : ℕ) (hN : fourLayerSize 162 ≤ N) :
    (N : ℝ) ^ ((5 : ℝ) / 4) < (Extremal.h N : ℝ) := by
  obtain ⟨hq162, hgrid, hnext⟩ := chosenFourLayerScale_bounds N hN
  let q := chosenFourLayerScale N
  have hq1 : 1 ≤ q := by omega
  let config := fourLayerConfiguration q N hq1 hgrid
  have hE : config.edges.card = fourLayerEdgePoly q :=
    fourLayerConfiguration_edges_card q N hq1 hgrid
  have hle_h : (fourLayerEdgePoly q : ℝ) ≤ (Extremal.h N : ℝ) := by
    rw [← hE]
    exact_mod_cast Extremal.configuration_edges_le_h config
  have hcoarse : N < 49 * q ^ 3 :=
    lt_of_lt_of_le hnext (next_fourLayerSize_le_49_cube q hq162)
  have hpow5 : N ^ 5 < (49 * q ^ 3) ^ 5 := by gcongr
  have hJ : 72 * q ^ 4 < fourLayerEdgePoly q := by
    unfold fourLayerEdgePoly; omega
  have hJ4 : (72 * q ^ 4) ^ 4 < (fourLayerEdgePoly q) ^ 4 := by gcongr
  have hq15 : 0 < q ^ 15 := by positivity
  have hnum : 49 ^ 5 < 72 ^ 4 * q := by omega
  have hmul : 49 ^ 5 * q ^ 15 < 72 ^ 4 * q * q ^ 15 :=
    Nat.mul_lt_mul_of_pos_right hnum hq15
  have hN5 : N ^ 5 < (fourLayerEdgePoly q) ^ 4 := by
    calc
      N ^ 5 < (49 * q ^ 3) ^ 5 := hpow5
      _ = 49 ^ 5 * q ^ 15 := by ring
      _ < 72 ^ 4 * q * q ^ 15 := hmul
      _ = (72 * q ^ 4) ^ 4 := by ring
      _ < (fourLayerEdgePoly q) ^ 4 := hJ4
  have hR : (N : ℝ) ^ 5 < ((fourLayerEdgePoly q : ℝ)) ^ 4 := by
    exact_mod_cast hN5
  have hroot : ((N : ℝ) ^ ((5 : ℝ) / 4)) ^ 4 = (N : ℝ) ^ 5 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N) ((5 : ℝ) / 4) 4]
    norm_num [Real.rpow_natCast]
  have hlt_J : (N : ℝ) ^ ((5 : ℝ) / 4) < (fourLayerEdgePoly q : ℝ) := by
    by_contra hnot
    have hle : (fourLayerEdgePoly q : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 4) :=
      le_of_not_gt hnot
    have hle4 : ((fourLayerEdgePoly q : ℝ)) ^ 4 ≤
        ((N : ℝ) ^ ((5 : ℝ) / 4)) ^ 4 := by gcongr
    rw [hroot] at hle4
    exact (not_le_of_gt hR) hle4
  exact lt_of_lt_of_le hlt_J hle_h

/-- Affirmative proof of the exact `FormalConjectures.ErdosProblems.956` superlinear statement:
there exists `c > 0` (namely `c = 1/4`) such that `n^(1 + c) < h(n)` for all sufficiently
large `n`. -/
theorem erdos_956_superlinear :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (1 + c) < (Extremal.h n : ℝ) := by
  refine ⟨1 / 4, by norm_num, Filter.eventually_atTop.mpr ⟨fourLayerSize 162, ?_⟩⟩
  intro n hn
  have hexp : (1 : ℝ) + 1 / 4 = 5 / 4 := by norm_num
  rw [hexp]
  exact h_strict_quarter_from_162 n hn

end Erdos956.FourLayer

/-!
## Section 7: Exact Faulhaber & Induced-Subset Tail Polynomial Certificates
-/

namespace Erdos956.PolynomialCertificates

open Erdos956.FourLayer

private theorem twelve_mul_shift_sum_int (m L : ℤ) (K : ℕ) :
    12 * (∑ i ∈ Finset.range K, (m - (i : ℤ)) * (L + 1 - ((i : ℤ) + 1) ^ 2)) =
      12 * m * (L + 1) * (K : ℤ)
      - 2 * m * (K : ℤ) * ((K : ℤ) + 1) * (2 * (K : ℤ) + 1)
      - 6 * (L + 1) * (K : ℤ) * ((K : ℤ) - 1)
      + 3 * (K : ℤ) ^ 2 * ((K : ℤ) + 1) ^ 2
      - 2 * (K : ℤ) * ((K : ℤ) + 1) * (2 * (K : ℤ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- Chojecki's one-sided parabolic edge-count polynomial:
`12 ∑_{i=1}^k (k + 1 - i)(k^2 + 1 - i^2) = 5k^4 + 2k^3 + k^2 + 4k`. -/
theorem oneSided_sum_polynomial (k : ℕ) :
    12 * (∑ i ∈ Finset.range k, (k - i) * (k ^ 2 + 1 - (i + 1) ^ 2)) =
      5 * k ^ 4 + 2 * k ^ 3 + k ^ 2 + 4 * k := by
  have hcast_sum :
      ((∑ i ∈ Finset.range k, (k - i) * (k ^ 2 + 1 - (i + 1) ^ 2) : ℕ) : ℤ) =
        ∑ i ∈ Finset.range k,
          ((k : ℤ) - (i : ℤ)) * ((k : ℤ) ^ 2 + 1 - ((i : ℤ) + 1) ^ 2) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < k := Finset.mem_range.mp hi
    have h1 : i ≤ k := by omega
    have h2 : (i + 1) ^ 2 ≤ k ^ 2 + 1 := by
      have hle : i + 1 ≤ k := by omega
      nlinarith
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    push_cast
    ring
  have h12 := twelve_mul_shift_sum_int (k : ℤ) ((k : ℤ) ^ 2) k
  rw [← hcast_sum] at h12
  have hmain_int :
      ((12 * (∑ i ∈ Finset.range k, (k - i) * (k ^ 2 + 1 - (i + 1) ^ 2)) : ℕ) : ℤ) =
      ((5 * k ^ 4 + 2 * k ^ 3 + k ^ 2 + 4 * k : ℕ) : ℤ) := by
    push_cast at h12 ⊢
    linarith
  exact_mod_cast hmain_int

/-- Full two-layer signed parabolic edge-count polynomial `E(m, m^2)`:
`6 ((m + 1)(m^2 + 1) + 2 ∑_{i=1}^m (m + 1 - i)(m^2 + 1 - i^2)) = 5m^4 + 8m^3 + 7m^2 + 10m + 6`. -/
theorem twoLayer_signed_sum_polynomial (m : ℕ) :
    6 * ((m + 1) * (m ^ 2 + 1) +
      2 * (∑ i ∈ Finset.range m, (m - i) * (m ^ 2 + 1 - (i + 1) ^ 2))) =
      5 * m ^ 4 + 8 * m ^ 3 + 7 * m ^ 2 + 10 * m + 6 := by
  calc
    6 * ((m + 1) * (m ^ 2 + 1) +
        2 * (∑ i ∈ Finset.range m, (m - i) * (m ^ 2 + 1 - (i + 1) ^ 2))) =
      6 * (m + 1) * (m ^ 2 + 1) +
        12 * (∑ i ∈ Finset.range m, (m - i) * (m ^ 2 + 1 - (i + 1) ^ 2)) := by ring
    _ = 6 * (m + 1) * (m ^ 2 + 1) + (5 * m ^ 4 + 2 * m ^ 3 + m ^ 2 + 4 * m) := by
      rw [oneSided_sum_polynomial m]
    _ = 5 * m ^ 4 + 8 * m ^ 3 + 7 * m ^ 2 + 10 * m + 6 := by ring

/-- Exact positivity of the degree-21 sharp induced-subset tail polynomial `P_sharp(q)`
for all `q = t + 51 ≥ 51` (Equation (9a) of `PROOF-STATUS-956.md`). -/
theorem P_sharp_pos_of_ge_51 (t : ℕ) :
    (fourLayerSize (t + 51) + 1) * (fourLayerSize (t + 52)) ^ 3 *
      (fourLayerSize (t + 52) - 1) ^ 3 <
      16 * (fourLayerEdgePoly (t + 52)) ^ 3 * (fourLayerSize (t + 51)) ^ 3 := by
  have hsub : fourLayerSize (t + 52) - 1 =
      48 * (t + 52) ^ 3 + 16 * (t + 52) ^ 2 + 12 * (t + 52) + 3 := rfl
  rw [hsub]
  let rem : ℕ :=
      1804786827514836291446372841618270579264763200 * t ^ 1
      + 622193310722272391561870351239282165496221120 * t ^ 2
      + 109500935741308223973839567557316692117633216 * t ^ 3
      + 12412729820845526749268601586057161526917888 * t ^ 4
      + 1004833637500447497849530323783954617411840 * t ^ 5
      + 61502064956837759789401119163051756453888 * t ^ 6
      + 2947967328907456464172417720042628490240 * t ^ 7
      + 113215747183529621580035207629360332800 * t ^ 8
      + 3536377205575079541510224510315106304 * t ^ 9
      + 90700268128185727596915056183230464 * t ^ 10
      + 1920176884546526443186611139543040 * t ^ 11
      + 33609407917734978455770044694528 * t ^ 12
      + 485475749440663219078233194496 * t ^ 13
      + 5755255062470677725283352576 * t ^ 14
      + 55445879314642450349293568 * t ^ 15
      + 427398208921882309165056 * t ^ 16
      + 2574203989530576420864 * t ^ 17
      + 11675131480652120064 * t ^ 18
      + 37510982456573952 * t ^ 19
      + 76123195047936 * t ^ 20
      + 73383542784 * t ^ 21
  have hid :
      16 * (fourLayerEdgePoly (t + 52)) ^ 3 * (fourLayerSize (t + 51)) ^ 3 =
        (fourLayerSize (t + 51) + 1) * (fourLayerSize (t + 52)) ^ 3 *
          (48 * (t + 52) ^ 3 + 16 * (t + 52) ^ 2 + 12 * (t + 52) + 3) ^ 3 +
          948898466566706391841932598759710145268264000 + rem := by
    dsimp [fourLayerSize, fourLayerEdgePoly, rem]
    ring
  omega

/-- Exact negative control at `q = 50`: `P_sharp(50) < 0`. -/
theorem P_sharp_neg_at_50 :
    16 * (fourLayerEdgePoly 51) ^ 3 * (fourLayerSize 50) ^ 3 <
      (fourLayerSize 50 + 1) * (fourLayerSize 51) ^ 3 * (fourLayerSize 51 - 1) ^ 3 := by
  decide

/-- Exact positivity of the degree-21 two-fifths induced-subset tail polynomial `P_{2,5}(q)`
for all `q = t + 64 ≥ 64` (Equation (8) of `PROOF-STATUS-956.md` for `A = 2, B = 5`). -/
theorem P_two_fifths_pos_of_ge_64 (t : ℕ) :
    8 * (fourLayerSize (t + 64) + 1) * (fourLayerSize (t + 65)) ^ 3 *
      (fourLayerSize (t + 65) - 1) ^ 3 <
      125 * (fourLayerEdgePoly (t + 65)) ^ 3 * (fourLayerSize (t + 64)) ^ 3 := by
  have hsub : fourLayerSize (t + 65) - 1 =
      48 * (t + 65) ^ 3 + 16 * (t + 65) ^ 2 + 12 * (t + 65) + 3 := rfl
  rw [hsub]
  let rem : ℕ :=
      998711151183288381735530469897251345864619581440 * t ^ 1
      + 275561848014416439906879440777131250328349893632 * t ^ 2
      + 38788652765603009547865085502449418955401967168 * t ^ 3
      + 3516105554719299574203950665205701133153964096 * t ^ 4
      + 227593368765221109284286731447504940282197952 * t ^ 5
      + 11137984840457985464129154258270109771380160 * t ^ 6
      + 426854256539907972666842561985908653511936 * t ^ 7
      + 13106792614564922545701463220976765298432 * t ^ 8
      + 327322413490785098044550638232953699840 * t ^ 9
      + 6711964493871770388699274458963647488 * t ^ 10
      + 113606581692270982813620560841488384 * t ^ 11
      + 1589798806737257545761142532661248 * t ^ 12
      + 18359726160516433961884140412928 * t ^ 13
      + 174012001046865942530372386816 * t ^ 14
      + 1340289794195171361984151552 * t ^ 15
      + 8259922221720846147846144 * t ^ 16
      + 39773992892235763286016 * t ^ 17
      + 144221576149674491904 * t ^ 18
      + 370457554476072960 * t ^ 19
      + 601046378348544 * t ^ 20
      + 463233613824 * t ^ 21
  have hid :
      125 * (fourLayerEdgePoly (t + 65)) ^ 3 * (fourLayerSize (t + 64)) ^ 3 =
        8 * (fourLayerSize (t + 64) + 1) * (fourLayerSize (t + 65)) ^ 3 *
          (48 * (t + 65) ^ 3 + 16 * (t + 65) ^ 2 + 12 * (t + 65) + 3) ^ 3 +
          650840016878037311664044756293640233394253889536 + rem := by
    dsimp [fourLayerSize, fourLayerEdgePoly, rem]
    ring
  omega

/-- Exact negative control at `q = 63`: `P_{2,5}(63) < 0`. -/
theorem P_two_fifths_neg_at_63 :
    125 * (fourLayerEdgePoly 64) ^ 3 * (fourLayerSize 63) ^ 3 <
      8 * (fourLayerSize 63 + 1) * (fourLayerSize 64) ^ 3 * (fourLayerSize 64 - 1) ^ 3 := by
  decide

end Erdos956.PolynomialCertificates
