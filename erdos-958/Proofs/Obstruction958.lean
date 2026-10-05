module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License") for the
attributed Formal Conjectures definitions and statement forms, and the MIT
License for the local proof development.
-/

public import Multiplicity958


@[expose] public section

/-!
# Erdős Problem 958: non-collinearity, non-concyclicity, and the main theorem

This module proves that for all `n ≥ 4`, the Clemen–Dumitrescu–Liu configuration
`cdlSet n` satisfies neither `IsEquidistantOnLine` nor `IsEquidistantOnCircle`.
Together with the positive multiplicity-profile theorems for equidistant collinear
configurations (`equidistantOnLine_has_profile`) and short-arc circular equidistant
configurations (`equidistantOnCircle_exists_has_profile`), this establishes both the
explicit all-`n ≥ 4` counterexample theorem `clemen_dumitrescu_liu` and the Formal
Conjectures disproof `erdos_958`.
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Erdos958

open Finset EuclideanGeometry

/-- For `0 < k < n`, `sin (k / n) ≠ 0`. -/
lemma sin_angle_ne_zero {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    Real.sin ((k : ℝ) / (n : ℝ)) ≠ 0 := by
  intro hsin
  have hcs := Real.cos_sq_add_sin_sq ((k : ℝ) / (n : ℝ))
  have hlt := cos_angle_lt_one hk0 hkn
  have hgt := half_lt_cos_angle hkn
  nlinarith

/-- Pointwise coordinate evaluation of `a + t • v` in `ℝ²`. -/
lemma add_smul_apply_zero (a v : ℝ²) (t : ℝ) : (a + t • v) 0 = a 0 + t * v 0 := rfl

lemma add_smul_apply_one (a v : ℝ²) (t : ℝ) : (a + t • v) 1 = a 1 + t * v 1 := rfl

lemma add_smul_vec2_zero (c : ℝ²) (r x y : ℝ) : (c + r • !₂[x, y]) 0 = c 0 + r * x := rfl

lemma add_smul_vec2_one (c : ℝ²) (r x y : ℝ) : (c + r • !₂[x, y]) 1 = c 1 + r * y := rfl

/-- Purely algebraic elimination for three collinear points `(0, 0)`, `(1, 0)`, `(x, y)`. -/
lemma line_obstruction_algebra (a₀ a₁ v₀ v₁ t₀ t₁ t₂ y : ℝ)
    (hp0 : 0 = a₀ + t₀ * v₀)
    (hp1 : 0 = a₁ + t₀ * v₁)
    (h00 : 1 = a₀ + t₁ * v₀)
    (h01 : 0 = a₁ + t₁ * v₁)
    (h11 : y = a₁ + t₂ * v₁) :
    y = 0 := by
  have hdiff0 : (t₁ - t₀) * v₀ = 1 := by linear_combination hp0 - h00
  have hdiff1 : (t₁ - t₀) * v₁ = 0 := by linear_combination hp1 - h01
  have hv1 : v₁ = 0 := by
    calc
      v₁ = ((t₁ - t₀) * v₀) * v₁ := by rw [hdiff0, one_mul]
      _ = v₀ * ((t₁ - t₀) * v₁) := by ring
      _ = 0 := by rw [hdiff1, mul_zero]
  rw [hv1] at hp1 h11
  linarith

/-- Purely algebraic elimination for four concyclic points `(0, 0)`, `(1, 0)`, `(cos β, sin β)`, `(cos 2β, sin 2β)`. -/
lemma circle_obstruction_algebra (c₀ c₁ r cb sb c2b s2b : ℝ)
    (hp : (0 - c₀) ^ 2 + (0 - c₁) ^ 2 = r ^ 2)
    (h0 : (1 - c₀) ^ 2 + (0 - c₁) ^ 2 = r ^ 2)
    (h1 : (cb - c₀) ^ 2 + (sb - c₁) ^ 2 = r ^ 2)
    (h2 : (c2b - c₀) ^ 2 + (s2b - c₁) ^ 2 = r ^ 2)
    (hcs1 : cb ^ 2 + sb ^ 2 = 1)
    (hcs2 : c2b ^ 2 + s2b ^ 2 = 1)
    (hcos2 : c2b = cb ^ 2 - sb ^ 2)
    (hsin2 : s2b = 2 * sb * cb) :
    cb = 1 := by
  linear_combination
    (-1 / 2) * h2 + (-1 / 2) * h0 + cb * h1 + (1 - cb) * hp +
    (1 / 2) * hcs2 + (-cb + c₀) * hcs1 +
    (-c₀) * hcos2 + (-c₁) * hsin2

/-- For `n ≥ 3`, `cdlSet n` is not a set of equidistant points on a line. -/
theorem not_isEquidistantOnLine_cdlSet {n : ℕ} (hn : 3 ≤ n) :
    ¬ IsEquidistantOnLine (cdlSet n) := by
  rintro ⟨a, v, _, hset⟩
  have hmem : ∀ x ∈ cdlSet n, ∃ i : ℕ, i < #(cdlSet n) ∧ x = a + (i : ℝ) • v := by
    intro x hx
    have hx' : x ∈ (cdlSet n : Set ℝ²) := hx
    rw [hset] at hx'
    exact hx'
  obtain ⟨i₀, _, hi₀⟩ := hmem originPt (originPt_mem_cdlSet n)
  obtain ⟨i₁, _, hi₁⟩ := hmem (arcPt n 0) (arcPt_mem_cdlSet (by omega))
  obtain ⟨i₂, _, hi₂⟩ := hmem (arcPt n 1) (arcPt_mem_cdlSet (by omega))
  have hp0 : (0 : ℝ) = a 0 + (i₀ : ℝ) * v 0 := by
    simpa only [originPt_zero, add_smul_apply_zero] using congrArg (fun x : ℝ² => x 0) hi₀
  have hp1 : (0 : ℝ) = a 1 + (i₀ : ℝ) * v 1 := by
    simpa only [originPt_one, add_smul_apply_one] using congrArg (fun x : ℝ² => x 1) hi₀
  have h00 : (1 : ℝ) = a 0 + (i₁ : ℝ) * v 0 := by
    simpa only [arcPt_zero, Nat.cast_zero, zero_div, Real.cos_zero, add_smul_apply_zero] using
      congrArg (fun x : ℝ² => x 0) hi₁
  have h01 : (0 : ℝ) = a 1 + (i₁ : ℝ) * v 1 := by
    simpa only [arcPt_one, Nat.cast_zero, zero_div, Real.sin_zero, add_smul_apply_one] using
      congrArg (fun x : ℝ² => x 1) hi₁
  have h11 : Real.sin (((1 : ℕ) : ℝ) / (n : ℝ)) = a 1 + (i₂ : ℝ) * v 1 := by
    simpa only [arcPt_one, add_smul_apply_one] using congrArg (fun x : ℝ² => x 1) hi₂
  have hsin_zero : Real.sin (((1 : ℕ) : ℝ) / (n : ℝ)) = 0 :=
    line_obstruction_algebra (a 0) (a 1) (v 0) (v 1) (i₀ : ℝ) (i₁ : ℝ) (i₂ : ℝ)
      (Real.sin (((1 : ℕ) : ℝ) / (n : ℝ))) hp0 hp1 h00 h01 h11
  exact sin_angle_ne_zero (by omega : 0 < 1) (by omega : 1 < n) hsin_zero

/-- For `n ≥ 4`, `cdlSet n` is not a set of equidistant points on a circle. -/
theorem not_isEquidistantOnCircle_cdlSet {n : ℕ} (hn : 4 ≤ n) :
    ¬ IsEquidistantOnCircle (cdlSet n) := by
  rintro ⟨c, r, θ, α, _, _, hset⟩
  have hcircle : ∀ x ∈ cdlSet n, (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 = r ^ 2 := by
    intro x hx
    have hx' : x ∈ (cdlSet n : Set ℝ²) := hx
    rw [hset] at hx'
    obtain ⟨i, _, rfl⟩ := hx'
    set φ : ℝ := θ + (i : ℝ) * α
    have hx0 : (c + r • !₂[Real.cos φ, Real.sin φ]) 0 - c 0 = r * Real.cos φ := by
      rw [add_smul_vec2_zero]; ring
    have hx1 : (c + r • !₂[Real.cos φ, Real.sin φ]) 1 - c 1 = r * Real.sin φ := by
      rw [add_smul_vec2_one]; ring
    rw [hx0, hx1]
    linear_combination (r ^ 2) * Real.cos_sq_add_sin_sq φ
  have hp := hcircle originPt (originPt_mem_cdlSet n)
  have h0 := hcircle (arcPt n 0) (arcPt_mem_cdlSet (by omega))
  have h1 := hcircle (arcPt n 1) (arcPt_mem_cdlSet (by omega))
  have h2 := hcircle (arcPt n 2) (arcPt_mem_cdlSet (by omega))
  simp only [originPt_zero, originPt_one, arcPt_zero, arcPt_one, Nat.cast_zero, zero_div,
    Real.cos_zero, Real.sin_zero] at hp h0 h1 h2
  set β : ℝ := ((1 : ℕ) : ℝ) / (n : ℝ) with hβ_def
  have h2β : ((2 : ℕ) : ℝ) / (n : ℝ) = β + β := by
    rw [hβ_def]
    push_cast
    ring
  rw [h2β] at h2
  have hcs1 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
  have hcs2 : Real.cos (β + β) ^ 2 + Real.sin (β + β) ^ 2 = 1 := Real.cos_sq_add_sin_sq (β + β)
  have hcos2 : Real.cos (β + β) = Real.cos β ^ 2 - Real.sin β ^ 2 := by
    rw [Real.cos_add]
    ring
  have hsin2 : Real.sin (β + β) = 2 * Real.sin β * Real.cos β := by
    rw [Real.sin_add]
    ring
  have hcos_eq_one : Real.cos β = 1 :=
    circle_obstruction_algebra (c 0) (c 1) r (Real.cos β) (Real.sin β)
      (Real.cos (β + β)) (Real.sin (β + β)) hp h0 h1 h2 hcs1 hcs2 hcos2 hsin2
  have hcos_lt_one : Real.cos β < 1 := cos_angle_lt_one (by omega : 0 < 1) (by omega : 1 < n)
  linarith

/-- The `i`-th point `a + i • v` of an equidistant collinear progression. -/
noncomputable def linePt (a v : ℝ²) (i : ℕ) : ℝ² :=
  a + (i : ℝ) • v

/-- The distance `s * ‖v‖` between two collinear points separated by `s` steps. -/
noncomputable def lineDist (v : ℝ²) (s : ℕ) : ℝ :=
  (s : ℝ) * ‖v‖

lemma abs_sub_cast_eq_natDist (i j : ℕ) :
    |(i : ℝ) - (j : ℝ)| = (Nat.dist i j : ℝ) := by
  rcases le_total i j with hij | hji
  · have hsub : (i : ℝ) - (j : ℝ) ≤ 0 := sub_nonpos.mpr (Nat.cast_le.mpr hij)
    rw [abs_of_nonpos hsub, neg_sub, Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij]
  · have hsub : 0 ≤ (i : ℝ) - (j : ℝ) := sub_nonneg.mpr (Nat.cast_le.mpr hji)
    rw [abs_of_nonneg hsub, Nat.dist_comm, Nat.dist_eq_sub_of_le hji, Nat.cast_sub hji]

lemma dist_linePt (a v : ℝ²) (i j : ℕ) :
    dist (linePt a v i) (linePt a v j) = lineDist v (Nat.dist i j) := by
  rw [linePt, linePt, lineDist, dist_eq_norm]
  have hsub : (a + (i : ℝ) • v) - (a + (j : ℝ) • v) = ((i : ℝ) - (j : ℝ)) • v := by
    rw [sub_smul]
    abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_sub_cast_eq_natDist]

lemma lineDist_inj {v : ℝ²} (hv : v ≠ 0) {s₁ s₂ : ℕ}
    (h : lineDist v s₁ = lineDist v s₂) : s₁ = s₂ := by
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hcast : (s₁ : ℝ) = (s₂ : ℝ) := mul_right_cancel₀ hnorm h
  exact Nat.cast_injective hcast

lemma eq_image_linePt_of_set_eq {A : Finset ℝ²} {a v : ℝ²}
    (hset : (A : Set ℝ²) = {x | ∃ i : ℕ, i < #A ∧ x = a + (i : ℝ) • v}) :
    A = (Finset.range #A).image (linePt a v) := by
  ext x
  have hiff : x ∈ (A : Set ℝ²) ↔ x ∈ {x | ∃ i : ℕ, i < #A ∧ x = a + (i : ℝ) • v} := by
    rw [hset]
  simp only [mem_coe, Set.mem_ofPred, mem_image, mem_range, linePt] at hiff ⊢
  rw [hiff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

/-- **Positive direction for collinear equidistant configurations**:
Every finite set `A ⊂ ℝ²` with `#A ≥ 2` satisfying `IsEquidistantOnLine A`
determines `#A - 1` distinct distances with multiplicities `{1, ..., #A - 1}`. -/
theorem equidistantOnLine_has_profile (A : Finset ℝ²) (hA : 2 ≤ #A)
    (hline : IsEquidistantOnLine A) :
    #(distanceSet A) = #A - 1 ∧
      (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (#A - 1) := by
  obtain ⟨a, v, hv, hset⟩ := hline
  have hA_eq : A = (Finset.range #A).image (linePt a v) := eq_image_linePt_of_set_eq hset
  have hprof := image_range_has_profile (f := linePt a v) (D := lineDist v) hA
    (dist_linePt a v) (fun _ _ _ _ heq => lineDist_inj hv heq)
  rwa [← hA_eq] at hprof

/-- For `n ≥ 1`, `arcSet (n + 1)` is a set of `n` equidistant points on the unit circle. -/
theorem isEquidistantOnCircle_arcSet (n : ℕ) :
    IsEquidistantOnCircle (arcSet (n + 1)) := by
  refine ⟨0, 1, 0, 1 / ((n + 1 : ℕ) : ℝ), zero_lt_one, one_div_ne_zero (by positivity), ?_⟩
  rw [card_arcSet (n + 1), Nat.add_sub_cancel]
  ext x
  simp only [arcSet, mem_coe, mem_image, mem_range, Nat.add_sub_cancel, Set.mem_ofPred,
    zero_add, one_smul]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hangle : (i : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by ring
    refine ⟨i, hi, ?_⟩
    rw [hangle, arcPt]
  · rintro ⟨i, hi, rfl⟩
    have hangle : (i : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by ring
    refine ⟨i, hi, ?_⟩
    rw [hangle, arcPt]

/-- **Positive direction for short-arc circular equidistant configurations**:
For every `n ≥ 2`, `arcSet (n + 1)` is a configuration of `n` equidistant points on a circle
(`IsEquidistantOnCircle`) that determines `n - 1` distinct distances with multiplicities
`{1, ..., n - 1}`. -/
theorem arcSet_equidistantOnCircle_has_profile (n : ℕ) (hn : 2 ≤ n) :
    #(arcSet (n + 1)) = n ∧
      IsEquidistantOnCircle (arcSet (n + 1)) ∧
      #(distanceSet (arcSet (n + 1))) = n - 1 ∧
      (distanceSet (arcSet (n + 1))).image (distanceMultiplicity (arcSet (n + 1))) =
        Finset.Icc 1 (n - 1) := by
  have harc : arcSet (n + 1) = (Finset.range n).image (arcPt (n + 1)) := by
    simp [arcSet]
  have hprof := image_range_has_profile (f := arcPt (n + 1)) (D := chordDist (n + 1)) hn
    (dist_arcPt_arcPt (n + 1))
    (fun s₁ s₂ hs₁ hs₂ heq => chordDist_inj (by omega) (by omega) heq)
  rw [← harc] at hprof
  exact ⟨by simp, isEquidistantOnCircle_arcSet n, hprof.1, hprof.2⟩

/-- Existential form of the positive circular-arc theorem: for every `n ≥ 2`, there exists
an `n`-point configuration on a circle (`IsEquidistantOnCircle`) with `n - 1` distinct
distances and multiplicities `{1, ..., n - 1}`. -/
theorem equidistantOnCircle_exists_has_profile (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset ℝ², #A = n ∧
      IsEquidistantOnCircle A ∧
      #(distanceSet A) = n - 1 ∧
      (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1) :=
  ⟨arcSet (n + 1), arcSet_equidistantOnCircle_has_profile n hn⟩

/-- **Clemen–Dumitrescu–Liu Theorem (2025)**:
For every `n ≥ 4`, the explicit configuration `cdlSet n` of `n` points in `ℝ²`
determines `n - 1` distinct distances with multiplicities `{1, 2, ..., n - 1}`,
while neither being equidistant on a line nor equidistant on a circle. -/
theorem clemen_dumitrescu_liu (n : ℕ) (hn : 4 ≤ n) :
    #(cdlSet n) = n ∧
      #(distanceSet (cdlSet n)) = n - 1 ∧
      (distanceSet (cdlSet n)).image (distanceMultiplicity (cdlSet n)) = Finset.Icc 1 (n - 1) ∧
      ¬ IsEquidistantOnLine (cdlSet n) ∧
      ¬ IsEquidistantOnCircle (cdlSet n) := by
  refine ⟨card_cdlSet (by omega), card_distanceSet_cdlSet (by omega),
    image_distanceMultiplicity_cdlSet (by omega),
    not_isEquidistantOnLine_cdlSet (by omega),
    not_isEquidistantOnCircle_cdlSet hn⟩

/-- Existential form of the Clemen–Dumitrescu–Liu counterexample for every `n ≥ 4`. -/
theorem exists_counterexample_of_four_le (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : Finset ℝ², #A = n ∧
      #(distanceSet A) = n - 1 ∧
      (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1) ∧
      ¬ IsEquidistantOnLine A ∧ ¬ IsEquidistantOnCircle A :=
  ⟨cdlSet n, clemen_dumitrescu_liu n hn⟩

/-- Direct disproof of the Erdős #958 classification statement. -/
theorem not_erdos_958 :
    ¬ (∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ², #A = n →
      ((#(distanceSet A) = n - 1 ∧
            (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
        (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A))) := by
  rintro ⟨N, hN⟩
  set n : ℕ := max N 4
  have hnN : n ≥ N := le_max_left N 4
  have hn4 : 4 ≤ n := le_max_right N 4
  obtain ⟨hcard, hdist, hmult, hnotLine, hnotCircle⟩ := clemen_dumitrescu_liu n hn4
  rcases hN n hnN (cdlSet n) hcard ⟨hdist, hmult⟩ with hL | hC
  · exact hnotLine hL
  · exact hnotCircle hC

/-- Literal Formal Conjectures statement of Erdős Problem 958 (`FormalConjectures/ErdosProblems/958.lean`),
with `answer(False)` elaborated as `False`. -/
theorem erdos_958 : False ↔
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ², #A = n →
      ((#(distanceSet A) = n - 1 ∧
            (distanceSet A).image (distanceMultiplicity A) = Finset.Icc 1 (n - 1)) →
        (IsEquidistantOnLine A ∨ IsEquidistantOnCircle A)) :=
  ⟨False.elim, not_erdos_958⟩

end Erdos958
