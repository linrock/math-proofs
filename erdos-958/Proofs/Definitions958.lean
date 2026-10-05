module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License") for the
attributed Formal Conjectures definitions, and the MIT License for the
local proof development.
-/

public import Mathlib


@[expose] public section

/-!
# Erdős Problem 958: definitions and the Clemen–Dumitrescu–Liu arc-and-center configuration

This module defines the Euclidean distance counting functions (`distanceSet`,
`distanceMultiplicity`) and geometric predicates (`IsEquidistantOnLine`,
`IsEquidistantOnCircle`) from `FormalConjectures/ErdosProblems/958.lean`, together
with the explicit Clemen–Dumitrescu–Liu configuration `cdlSet n` consisting of the
origin `(0, 0)` and `n - 1` equally spaced points on a short circular arc of the
unit circle at angles `k / n` (`0 ≤ k < n - 1`).
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry Finset

section MetricCounting

variable {X : Type*} [MetricSpace X]

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/-- The multiplicity of the distance `d` determined by `points`, that is, the number of unordered
pairs of distinct points at distance `d` apart. -/
noncomputable def distanceMultiplicity (points : Finset X) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) / 2

end MetricCounting

namespace Erdos958

open Finset EuclideanGeometry

/-- `A` is a set of equidistant points on a line: there are a point `a` and a non-zero direction
`v` such that `A` consists of the points `a + i • v` for `0 ≤ i < #A`. -/
def IsEquidistantOnLine (A : Finset ℝ²) : Prop :=
  ∃ a v : ℝ², v ≠ 0 ∧ (A : Set ℝ²) = {x | ∃ i : ℕ, i < #A ∧ x = a + (i : ℝ) • v}

/-- `A` is a set of equidistant points on a circle: there are a centre `c`, a radius `r > 0`, an
initial angle `θ` and a non-zero angular step `α` such that `A` consists of the points of the
circle of centre `c` and radius `r` at the angles `θ + i * α` for `0 ≤ i < #A`. -/
def IsEquidistantOnCircle (A : Finset ℝ²) : Prop :=
  ∃ (c : ℝ²) (r θ α : ℝ), 0 < r ∧ α ≠ 0 ∧ (A : Set ℝ²) =
    {x | ∃ i : ℕ, i < #A ∧
      x = c + r • (!₂[Real.cos (θ + (i : ℝ) * α), Real.sin (θ + (i : ℝ) * α)])}

/-- The origin `(0, 0)` in `ℝ²`, serving as the circle center in the CDL construction. -/
noncomputable def originPt : ℝ² := !₂[(0 : ℝ), 0]

/-- The `k`-th point on the unit circle at angle `(k : ℝ) / (n : ℝ)`. -/
noncomputable def arcPt (n k : ℕ) : ℝ² :=
  !₂[Real.cos ((k : ℝ) / (n : ℝ)), Real.sin ((k : ℝ) / (n : ℝ))]

/-- The `n - 1` equally spaced points on the short circular arc for `0 ≤ k < n - 1`. -/
noncomputable def arcSet (n : ℕ) : Finset ℝ² :=
  (Finset.range (n - 1)).image (arcPt n)

/-- The Clemen–Dumitrescu–Liu point set of size `n`: the origin together with `n - 1`
equally spaced points on a short arc of the unit circle. -/
noncomputable def cdlSet (n : ℕ) : Finset ℝ² :=
  insert originPt (arcSet n)

/-- The chord length between two unit-circle points separated by `s` angular steps of `1 / n`. -/
noncomputable def chordDist (n s : ℕ) : ℝ :=
  Real.sqrt (2 - 2 * Real.cos ((s : ℝ) / (n : ℝ)))

@[simp]
lemma originPt_zero : originPt 0 = 0 := rfl

@[simp]
lemma originPt_one : originPt 1 = 0 := rfl

@[simp]
lemma arcPt_zero (n k : ℕ) : arcPt n k 0 = Real.cos ((k : ℝ) / (n : ℝ)) := rfl

@[simp]
lemma arcPt_one (n k : ℕ) : arcPt n k 1 = Real.sin ((k : ℝ) / (n : ℝ)) := rfl

/-- Euclidean distance in `ℝ²` expressed via the two coordinates. -/
lemma dist_eq_sqrt_coords (p q : ℝ²) :
    dist p q = Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq]

/-- Every arc point is at distance `1` from the origin. -/
@[simp]
lemma dist_originPt_arcPt (n k : ℕ) : dist originPt (arcPt n k) = 1 := by
  rw [dist_eq_sqrt_coords]
  have hcs : Real.cos ((k : ℝ) / (n : ℝ)) ^ 2 + Real.sin ((k : ℝ) / (n : ℝ)) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq ((k : ℝ) / (n : ℝ))
  have hsq : (originPt 0 - arcPt n k 0) ^ 2 + (originPt 1 - arcPt n k 1) ^ 2 = 1 := by
    simp only [originPt_zero, originPt_one, arcPt_zero, arcPt_one, zero_sub, neg_sq]
    exact hcs
  rw [hsq, Real.sqrt_one]

/-- Every arc point is at distance `1` from the origin (symmetric form). -/
@[simp]
lemma dist_arcPt_originPt (n k : ℕ) : dist (arcPt n k) originPt = 1 := by
  rw [dist_comm, dist_originPt_arcPt]

/-- Trigonometric identity relating squared chord length on the unit circle to `cos (α - β)`. -/
lemma sq_sub_cos_add_sq_sub_sin (α β : ℝ) :
    (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2 =
      2 - 2 * Real.cos (α - β) := by
  have h1 := Real.cos_sq_add_sin_sq α
  have h2 := Real.cos_sq_add_sin_sq β
  rw [Real.cos_sub]
  linear_combination h1 + h2

/-- Relation between `cos` of the signed difference and `Nat.dist`. -/
lemma cos_sub_div_eq_cos_natDist_div (n i j : ℕ) :
    Real.cos ((i : ℝ) / (n : ℝ) - (j : ℝ) / (n : ℝ)) =
      Real.cos ((Nat.dist i j : ℝ) / (n : ℝ)) := by
  rcases le_total i j with hij | hji
  · have hd : (Nat.dist i j : ℝ) = (j : ℝ) - (i : ℝ) := by
      rw [Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij]
    rw [hd, ← Real.cos_neg]
    congr 1; ring
  · have hd : (Nat.dist i j : ℝ) = (i : ℝ) - (j : ℝ) := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji, Nat.cast_sub hji]
    rw [hd, ← sub_div]

/-- Distance between two arc points `arcPt n i` and `arcPt n j` equals `chordDist n (Nat.dist i j)`. -/
lemma dist_arcPt_arcPt (n i j : ℕ) :
    dist (arcPt n i) (arcPt n j) = chordDist n (Nat.dist i j) := by
  rw [dist_eq_sqrt_coords, chordDist]
  simp only [arcPt_zero, arcPt_one]
  rw [sq_sub_cos_add_sq_sub_sin, cos_sub_div_eq_cos_natDist_div]

/-- `1 < π / 3` since `3 < π`. -/
lemma one_lt_pi_div_three : (1 : ℝ) < Real.pi / 3 := by
  linarith [Real.pi_gt_three]

/-- If `s < n`, then `(s : ℝ) / (n : ℝ) ∈ [0, π]`. -/
lemma angle_mem_Icc_zero_pi {n s : ℕ} (hs : s < n) :
    (s : ℝ) / (n : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hs)
  refine ⟨ by positivity, ?_ ⟩
  have h1 : (s : ℝ) / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr (Nat.cast_lt.mpr hs)
  linarith [Real.pi_gt_three]

/-- Strict antitonicity of `s ↦ cos (s / n)` for `s < n`. -/
lemma cos_angle_strictAnti {n s₁ s₂ : ℕ} (h12 : s₁ < s₂) (hs2 : s₂ < n) :
    Real.cos ((s₂ : ℝ) / (n : ℝ)) < Real.cos ((s₁ : ℝ) / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hs2)
  apply Real.strictAntiOn_cos (angle_mem_Icc_zero_pi (lt_trans h12 hs2)) (angle_mem_Icc_zero_pi hs2)
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr h12) hn_pos

/-- For `0 < s < n`, `cos (s / n) < 1`. -/
lemma cos_angle_lt_one {n s : ℕ} (hs0 : 0 < s) (hsn : s < n) :
    Real.cos ((s : ℝ) / (n : ℝ)) < 1 := by
  have h := cos_angle_strictAnti hs0 hsn
  simpa using h

/-- For `s < n` and `0 < n`, `1 / 2 < cos (s / n)`. -/
lemma half_lt_cos_angle {n s : ℕ} (hsn : s < n) :
    (1 / 2 : ℝ) < Real.cos ((s : ℝ) / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hsn)
  have h1 : (s : ℝ) / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr (Nat.cast_lt.mpr hsn)
  have hpi3 : (s : ℝ) / (n : ℝ) < Real.pi / 3 := lt_trans h1 one_lt_pi_div_three
  have hmem_pi3 : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith [Real.pi_gt_three]
  have h := Real.strictAntiOn_cos (angle_mem_Icc_zero_pi hsn) hmem_pi3 hpi3
  rwa [Real.cos_pi_div_three] at h

/-- For `0 < s < n`, `0 < chordDist n s`. -/
lemma chordDist_pos {n s : ℕ} (hs0 : 0 < s) (hsn : s < n) :
    0 < chordDist n s := by
  rw [chordDist]
  apply Real.sqrt_pos.mpr
  linarith [cos_angle_lt_one hs0 hsn]

/-- For `s < n`, `chordDist n s < 1`. -/
lemma chordDist_lt_one {n s : ℕ} (hsn : s < n) :
    chordDist n s < 1 := by
  rw [chordDist, ← Real.sqrt_one]
  apply Real.sqrt_lt_sqrt
  · have hle : Real.cos ((s : ℝ) / (n : ℝ)) ≤ 1 := Real.cos_le_one _
    linarith
  · linarith [half_lt_cos_angle hsn]

/-- Strict monotonicity of `s ↦ chordDist n s` for `s < n`. -/
lemma chordDist_strictMono {n s₁ s₂ : ℕ} (h12 : s₁ < s₂) (hs2 : s₂ < n) :
    chordDist n s₁ < chordDist n s₂ := by
  rw [chordDist, chordDist]
  apply Real.sqrt_lt_sqrt
  · have hle : Real.cos ((s₁ : ℝ) / (n : ℝ)) ≤ 1 := Real.cos_le_one _
    linarith
  · linarith [cos_angle_strictAnti h12 hs2]

/-- Injectivity of `chordDist n` on `{s | s < n}`. -/
lemma chordDist_inj {n s₁ s₂ : ℕ} (hs₁ : s₁ < n) (hs₂ : s₂ < n)
    (heq : chordDist n s₁ = chordDist n s₂) : s₁ = s₂ := by
  rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
  · exact False.elim ((ne_of_lt (chordDist_strictMono hlt hs₂)) heq)
  · rfl
  · exact False.elim ((ne_of_gt (chordDist_strictMono hgt hs₁)) heq)

lemma chordDist_injOn (n : ℕ) : Set.InjOn (chordDist n) {s : ℕ | s < n} := by
  intro s₁ hs₁ s₂ hs₂ heq
  exact chordDist_inj hs₁ hs₂ heq

/-- Injectivity of `arcPt n` on `{k | k < n}`. -/
lemma arcPt_inj {n i j : ℕ} (hi : i < n) (hj : j < n)
    (heq : arcPt n i = arcPt n j) : i = j := by
  have hcos : Real.cos ((i : ℝ) / (n : ℝ)) = Real.cos ((j : ℝ) / (n : ℝ)) :=
    congrArg (fun x : ℝ² => x 0) heq
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact False.elim ((ne_of_gt (cos_angle_strictAnti hlt hj)) hcos)
  · rfl
  · exact False.elim ((ne_of_lt (cos_angle_strictAnti hgt hi)) hcos)

lemma arcPt_injOn (n : ℕ) : Set.InjOn (arcPt n) {k : ℕ | k < n} := by
  intro i hi j hj heq
  exact arcPt_inj hi hj heq

/-- The arc set `arcSet n` has cardinality `n - 1`. -/
@[simp]
lemma card_arcSet (n : ℕ) : #(arcSet n) = n - 1 := by
  rw [arcSet, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj heq
  have hi' : i < n := Nat.lt_of_lt_pred (Finset.mem_range.mp hi)
  have hj' : j < n := Nat.lt_of_lt_pred (Finset.mem_range.mp hj)
  exact arcPt_injOn n hi' hj' heq

/-- The origin `originPt` does not belong to `arcSet n`. -/
lemma originPt_not_mem_arcSet (n : ℕ) : originPt ∉ arcSet n := by
  intro hmem
  rw [arcSet, Finset.mem_image] at hmem
  obtain ⟨k, _, hk⟩ := hmem
  have hd := congrArg (dist originPt) hk
  rw [dist_originPt_arcPt, dist_self] at hd
  norm_num at hd

/-- For `n ≥ 1`, `#(cdlSet n) = n`. -/
@[simp]
lemma card_cdlSet {n : ℕ} (hn : 1 ≤ n) : #(cdlSet n) = n := by
  rw [cdlSet, Finset.card_insert_of_notMem (originPt_not_mem_arcSet n), card_arcSet]
  omega

end Erdos958
