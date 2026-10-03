import Mathlib

/-!
# Erdős Problem #956: Complete Lean 4.35.0-rc2 Formalization

This file provides a self-contained Lean 4.35.0-rc2 formalization of:
1. **Signed Parabolic Cap Geometry (`Erdos956.Geometry`)**:
   Proves the supporting-hyperplane inequality, exact unit distance `Metric.infDist = 1`,
   coordinate box containment `[-W^3/2, W^3/2] × [-W^4, W^4]`, compactness, convexity,
   central symmetry, and nonempty interior for the signed finite convex hull
   `D = conv {±p(t) : t ∈ T}` for any finite parameter set `T ⊆ [-W, W]` (including
   opposite-sign parameters `s, t ∈ [-W, W]`).
2. **Difference-Body & Remote Padding Reductions (`Erdos956`, `Erdos956.Padding`)**:
   Identifies the double-infimum translate set distance `translateSetDistance C x y`
   with `Metric.infDist (y - x) (C - C)` for `C = (1/2) • D`, proves closed-translate
   disjointness from `y - x ∉ D`, and pads configurations with remote translates.
3. **Two-Layer All-`N` Baseline (`Erdos956.Centers`, `Erdos956.Counting`, `Erdos956.Specification`)**:
   Proves `erdos956_full_answer` (`≥ (1/1000) N^(4/3)` for all `N ≥ 30`) and
   `erdos956_strict_superlinear_answer` (`> N^(5/4)` eventually).
4. **Extremal Function Bridge (`Erdos956.Extremal`)**:
   Defines the exact extremal function `h(n) = sSup {m | ...}` and `unitPairs C X` from
   `FormalConjectures.ErdosProblems.956`, proves `BddAbove` via `n.choose 2`, and proves
   both `∀ N ≥ 30, (1/1000) N^(4/3) ≤ h N` and the exact `Filter.atTop` theorem
   `erdos_956_superlinear : ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (1 + c) < (h n : ℝ)`.
5. **Four-Layer Signed-Grid Construction & Polynomial `J_q` (`Erdos956.FourLayer`)**:
   Formalizes the 4-layer signed parabolic grid at scale `q ≥ 1` (`m = 3q`, `ℓ = 4q^2`, `L = 4`),
   proving the exact vertex count `N_q = 48q^3 + 16q^2 + 12q + 4` (`N_1 = 80`), the exact
   unordered unit-distance edge count polynomial `J_q = 72q^4 + 32q^3 + 24q^2 + 13q + 3`
   (`J_1 = 144`), and the improved asymptotic lower bound `h(N) > (2/5) N^(4/3)` for all
   `N ≥ fourLayerSize 162`.
-/

namespace Erdos956.Geometry

open scoped InnerProductSpace
open scoped Pointwise

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

def dot (u v : Plane) : ℝ := u 0 * v 0 + u 1 * v 1

def q (t : ℝ) (z : Plane) : ℝ := t * z 0 + z 1

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := by
  simp [point]

@[simp] theorem point_one (x y : ℝ) : point x y 1 = y := by
  simp [point]

noncomputable def gamma (η t : ℝ) : Plane := point t (1 + η - t ^ 2 / 2)

noncomputable def normal (t : ℝ) : Plane := point (t / Real.sqrt (1 + t ^ 2))
  (1 / Real.sqrt (1 + t ^ 2))

noncomputable def p (η t : ℝ) : Plane := gamma η t - normal t

noncomputable def generators (η : ℝ) (T : Finset ℝ) : Set Plane :=
  (p η '' (T : Set ℝ)) ∪ ((fun s : ℝ => -p η s) '' (T : Set ℝ))

noncomputable def D (η : ℝ) (T : Finset ℝ) : Set Plane := convexHull ℝ (generators η T)

private theorem sqrt_rad_sq (t : ℝ) :
    (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem sqrt_rad_nonneg (t : ℝ) :
    0 ≤ Real.sqrt (1 + t ^ 2) := Real.sqrt_nonneg _

theorem sqrt_rad_ge_one (t : ℝ) :
    1 ≤ Real.sqrt (1 + t ^ 2) := by
  have hsq := sqrt_rad_sq t
  have hn := sqrt_rad_nonneg t
  nlinarith [sq_nonneg t]

theorem sqrt_rad_pos (t : ℝ) :
    0 < Real.sqrt (1 + t ^ 2) := lt_of_lt_of_le (by norm_num) (sqrt_rad_ge_one t)

@[simp] theorem gamma_zero (η t : ℝ) : (gamma η t) 0 = t := by simp [gamma]

@[simp] theorem gamma_one (η t : ℝ) : (gamma η t) 1 = 1 + η - t ^ 2 / 2 := by
  simp [gamma]

@[simp] theorem normal_zero (t : ℝ) :
    (normal t) 0 = t / Real.sqrt (1 + t ^ 2) := by simp [normal]

@[simp] theorem normal_one (t : ℝ) :
    (normal t) 1 = 1 / Real.sqrt (1 + t ^ 2) := by simp [normal]

@[simp] theorem p_zero (η t : ℝ) :
    (p η t) 0 = t - t / Real.sqrt (1 + t ^ 2) := by
  simp [p]

@[simp] theorem p_one (η t : ℝ) :
    (p η t) 1 = 1 + η - t ^ 2 / 2 - 1 / Real.sqrt (1 + t ^ 2) := by
  simp [p]

theorem gamma_sub_p (η t : ℝ) : gamma η t - p η t = normal t := by
  simp [p]

theorem normal_dot_self (t : ℝ) : dot (normal t) (normal t) = 1 := by
  have hr := sqrt_rad_sq t
  have hp := sqrt_rad_pos t
  have hne : Real.sqrt (1 + t ^ 2) ≠ 0 := ne_of_gt hp
  simp only [dot, normal_zero, normal_one]
  field_simp
  nlinarith [hr]

theorem sqrt_rad_le_one_add_half_sq (t : ℝ) :
    Real.sqrt (1 + t ^ 2) ≤ 1 + t ^ 2 / 2 := by
  have hr := sqrt_rad_sq t
  have hpos := sqrt_rad_nonneg t
  nlinarith [sq_nonneg (t ^ 2 / 2)]

theorem reciprocal_error_identity (t : ℝ) :
    1 - 1 / Real.sqrt (1 + t ^ 2) =
      t ^ 2 / (Real.sqrt (1 + t ^ 2) * (Real.sqrt (1 + t ^ 2) + 1)) := by
  have hr := sqrt_rad_sq t
  have hne := ne_of_gt (sqrt_rad_pos t)
  field_simp
  nlinarith [hr]

theorem reciprocal_error_nonneg (t : ℝ) :
    0 ≤ 1 - 1 / Real.sqrt (1 + t ^ 2) := by
  rw [reciprocal_error_identity]
  positivity

theorem reciprocal_error_le_half_sq (t : ℝ) :
    1 - 1 / Real.sqrt (1 + t ^ 2) ≤ t ^ 2 / 2 := by
  let r := Real.sqrt (1 + t ^ 2)
  have hr : 1 ≤ r := sqrt_rad_ge_one t
  have hden : 2 ≤ r * (r + 1) := by nlinarith
  have hdenpos : 0 < r * (r + 1) := by positivity
  rw [reciprocal_error_identity]
  change t ^ 2 / (r * (r + 1)) ≤ t ^ 2 / 2
  apply (div_le_iff₀ hdenpos).2
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hden)]

theorem reciprocal_error_ge_half_sq_sub_quartic (t : ℝ) (ht : t ^ 2 ≤ 1) :
    t ^ 2 / 2 - t ^ 4 / 2 ≤ 1 - 1 / Real.sqrt (1 + t ^ 2) := by
  let r := Real.sqrt (1 + t ^ 2)
  let u := t ^ 2
  have hu0 : 0 ≤ u := sq_nonneg t
  have hu1 : u ≤ 1 := ht
  have hr : r ^ 2 = 1 + u := sqrt_rad_sq t
  have hr1 : 1 ≤ r := sqrt_rad_ge_one t
  have hrmax : r ≤ 1 + u / 2 := sqrt_rad_le_one_add_half_sq t
  have hdenpos : 0 < r * (r + 1) := by positivity
  have haux : (1 - u) * (r - 1 - u / 2) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hden : (1 - u) * (r * (r + 1)) ≤ 2 := by
    nlinarith [sq_nonneg u, haux]
  rw [reciprocal_error_identity]
  have hpow : t ^ 4 = u ^ 2 := by dsimp [u]; ring
  rw [hpow]
  change u / 2 - u ^ 2 / 2 ≤ u / (r * (r + 1))
  apply (le_div_iff₀ hdenpos).2
  nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hden)]

theorem p_x_nonneg (η s : ℝ) (hs : 0 ≤ s) : 0 ≤ (p η s) 0 := by
  rw [p_zero]
  have hδ := reciprocal_error_nonneg s
  have hfactor : s - s / Real.sqrt (1 + s ^ 2) =
      s * (1 - 1 / Real.sqrt (1 + s ^ 2)) := by ring
  rw [hfactor]
  exact mul_nonneg hs hδ

theorem p_x_le_cubic (η s : ℝ) (hs : 0 ≤ s) :
    (p η s) 0 ≤ s ^ 3 / 2 := by
  rw [p_zero]
  have hδ := reciprocal_error_le_half_sq s
  have hfactor : s - s / Real.sqrt (1 + s ^ 2) =
      s * (1 - 1 / Real.sqrt (1 + s ^ 2)) := by ring
  rw [hfactor]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hδ)]

/-- Signed horizontal coordinate bound for `s ∈ [-W, W]`. -/
theorem p_x_signed_bounds (η W s : ℝ) (hW0 : 0 ≤ W)
    (hs_low : -W ≤ s) (hs_high : s ≤ W) :
    -W ^ 3 / 2 ≤ (p η s) 0 ∧ (p η s) 0 ≤ W ^ 3 / 2 := by
  rw [p_zero]
  have hδ0 := reciprocal_error_nonneg s
  have hδ1 := reciprocal_error_le_half_sq s
  have hs2 : s ^ 2 ≤ W ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ W - s) (by linarith : 0 ≤ W + s)]
  have hδW : 1 - 1 / Real.sqrt (1 + s ^ 2) ≤ W ^ 2 / 2 := by linarith
  have hfactor : s - s / Real.sqrt (1 + s ^ 2) =
      s * (1 - 1 / Real.sqrt (1 + s ^ 2)) := by ring
  rw [hfactor]
  constructor
  · nlinarith [mul_nonneg (by linarith : 0 ≤ s + W) hδ0,
      mul_nonneg hW0 (sub_nonneg.mpr hδW)]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ W - s) hδ0,
      mul_nonneg hW0 (sub_nonneg.mpr hδW)]

theorem mul_p_x_nonneg (η t : ℝ) : 0 ≤ t * (p η t) 0 := by
  rw [p_zero]
  have hδ := reciprocal_error_nonneg t
  have hfactor : t * (t - t / Real.sqrt (1 + t ^ 2)) =
      t ^ 2 * (1 - 1 / Real.sqrt (1 + t ^ 2)) := by ring
  rw [hfactor]
  exact mul_nonneg (sq_nonneg t) hδ

theorem p_y_le_eta (η s : ℝ) : (p η s) 1 ≤ η := by
  rw [p_one]
  have hδ := reciprocal_error_le_half_sq s
  linarith

theorem p_y_ge_eta_sub_quartic (η s : ℝ) (hs : s ^ 2 ≤ 1) :
    η - s ^ 4 / 2 ≤ (p η s) 1 := by
  rw [p_one]
  have hδ := reciprocal_error_ge_half_sq_sub_quartic s hs
  linarith

theorem p_y_ge_half_eta_signed (W s : ℝ) (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hs_low : -W ≤ s) (hs_high : s ≤ W) :
    W ^ 4 / 2 ≤ (p (W ^ 4) s) 1 := by
  have hs2 : s ^ 2 ≤ W ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ W - s) (by linarith : 0 ≤ W + s)]
  have hW2 : W ^ 2 ≤ 1 := by nlinarith
  have hs_sq : s ^ 2 ≤ 1 := le_trans hs2 hW2
  have hs4 : s ^ 4 ≤ W ^ 4 := by
    have h2 : (s ^ 2) ^ 2 ≤ (W ^ 2) ^ 2 := by
      nlinarith [sq_nonneg s, sq_nonneg W,
        mul_nonneg (by linarith : 0 ≤ W ^ 2 - s ^ 2) (by positivity : 0 ≤ W ^ 2 + s ^ 2)]
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ ≤ (W ^ 2) ^ 2 := h2
      _ = W ^ 4 := by ring
  have hp := p_y_ge_eta_sub_quartic (W ^ 4) s hs_sq
  linarith

theorem p_y_nonneg_signed (W s : ℝ) (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hs_low : -W ≤ s) (hs_high : s ≤ W) :
    0 ≤ (p (W ^ 4) s) 1 := by
  have h := p_y_ge_half_eta_signed W s hW0 hW1 hs_low hs_high
  have hW4 : 0 ≤ W ^ 4 := by positivity
  linarith

theorem p_y_nonneg (W s : ℝ) (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hs0 : 0 ≤ s) (hsW : s ≤ W) :
    0 ≤ (p (W ^ 4) s) 1 :=
  p_y_nonneg_signed W s hW0 hW1 (by linarith) hsW

private theorem radical_gap_identity (s t : ℝ) :
    (Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + t ^ 2) - (1 + s * t)) *
      (Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + t ^ 2) + (1 + s * t)) =
      (s - t) ^ 2 := by
  have hs := sqrt_rad_sq s
  have ht := sqrt_rad_sq t
  calc
    _ = (Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + t ^ 2)) ^ 2 -
          (1 + s * t) ^ 2 := by ring
    _ = (1 + s ^ 2) * (1 + t ^ 2) - (1 + s * t) ^ 2 := by
      rw [mul_pow, hs, ht]
    _ = (s - t) ^ 2 := by ring

private theorem radical_sum_identity (s t : ℝ) :
    (Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + t ^ 2) - (1 - s * t)) *
      (Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + t ^ 2) + (1 - s * t)) =
      (s + t) ^ 2 := by
  have hs := sqrt_rad_sq s
  have ht := sqrt_rad_sq t
  calc
    _ = (Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + t ^ 2)) ^ 2 -
          (1 - s * t) ^ 2 := by ring
    _ = (1 + s ^ 2) * (1 + t ^ 2) - (1 - s * t) ^ 2 := by
      rw [mul_pow, hs, ht]
    _ = (s + t) ^ 2 := by ring

/-- For ALL real `s, t` (including opposite signs!), `rs * rt + 1 + s * t ≥ 2`,
which yields `0 ≤ rs * rt - (1 + s * t)` and `2 * (rs * rt - (1 + s * t)) ≤ (s - t)^2`. -/
theorem radical_gap_nonneg_bound_signed (s t : ℝ) :
    0 ≤ Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + t ^ 2) - (1 + s * t) ∧
    2 * (Real.sqrt (1 + s ^ 2) * Real.sqrt (1 + t ^ 2) - (1 + s * t)) ≤
      (s - t) ^ 2 := by
  let rs := Real.sqrt (1 + s ^ 2)
  let rt := Real.sqrt (1 + t ^ 2)
  let A := rs * rt
  let B := 1 + s * t
  let C := 1 - s * t
  let Δ := (s - t) ^ 2
  have hrs : 1 ≤ rs := sqrt_rad_ge_one s
  have hrt : 1 ≤ rt := sqrt_rad_ge_one t
  have hA : 1 ≤ A := by nlinarith
  have hsum_id : (A - C) * (A + C) = (s + t) ^ 2 := radical_sum_identity s t
  have hAC : 0 ≤ A - C := by nlinarith [sq_nonneg (s + t)]
  have hsum : 2 ≤ A + B := by
    have hBC : B + C = 2 := by dsimp [B, C]; ring
    linarith
  have hΔ : 0 ≤ Δ := sq_nonneg (s - t)
  have hidentity : (A - B) * (A + B) = Δ := radical_gap_identity s t
  have hgap : 0 ≤ A - B := by nlinarith
  constructor
  · exact hgap
  · nlinarith [mul_nonneg hgap (sub_nonneg.mpr hsum)]

theorem q_p_sub_p_nonneg_signed (η s t : ℝ) :
    0 ≤ q t (p η t - p η s) := by
  let rs := Real.sqrt (1 + s ^ 2)
  let rt := Real.sqrt (1 + t ^ 2)
  let A := rs * rt
  let B := 1 + s * t
  let Δ := (s - t) ^ 2
  have hrs : 1 ≤ rs := sqrt_rad_ge_one s
  have hrsp : 0 < rs := sqrt_rad_pos s
  have hrtp : 0 < rt := sqrt_rad_pos t
  have hgap := (radical_gap_nonneg_bound_signed s t).1
  have hbound := (radical_gap_nonneg_bound_signed s t).2
  have hmul : 0 ≤ rs * (Δ - 2 * (A - B)) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hmul2 : 0 ≤ (rs - 1) * (A - B) := by
    exact mul_nonneg (by linarith) (by linarith)
  have hmain : 2 * (A - B) ≤ rs * Δ := by nlinarith
  have hq : q t (p η t - p η s) = Δ / 2 - (A - B) / rs := by
    have hrt_sq : rt ^ 2 = 1 + t ^ 2 := sqrt_rad_sq t
    have hrt_div : (1 + t ^ 2) / rt = rt := by
      apply (div_eq_iff (ne_of_gt hrtp)).2
      nlinarith [hrt_sq]
    have hA_div : A / rs = rt := by
      change (rs * rt) / rs = rt
      field_simp
    calc
      q t (p η t - p η s) = Δ / 2 - (1 + t ^ 2) / rt + B / rs := by
        simp only [q, PiLp.sub_apply, p_zero, p_one]
        dsimp [Δ, B]
        ring
      _ = Δ / 2 - rt + B / rs := by rw [hrt_div]
      _ = Δ / 2 - (A - B) / rs := by rw [sub_div, hA_div]; ring
  rw [hq]
  have hnum : 0 ≤ rs * Δ - 2 * (A - B) := by linarith
  have hrewrite : Δ / 2 - (A - B) / rs =
      (rs * Δ - 2 * (A - B)) / (2 * rs) := by field_simp
  rw [hrewrite]
  exact div_nonneg hnum (by positivity)

@[simp] theorem q_add (t : ℝ) (x y : Plane) : q t (x + y) = q t x + q t y := by
  simp only [q, PiLp.add_apply]
  ring

@[simp] theorem q_sub (t : ℝ) (x y : Plane) : q t (x - y) = q t x - q t y := by
  simp only [q, PiLp.sub_apply]
  ring

@[simp] theorem q_neg (t : ℝ) (x : Plane) : q t (-x) = -q t x := by
  simp only [q, PiLp.neg_apply]
  ring

/-- Signed negative-generator support inequality for `s, t ∈ [-W, W]`. -/
theorem q_p_add_p_nonneg_signed (W s t : ℝ) (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hs_low : -W ≤ s) (hs_high : s ≤ W)
    (ht_low : -W ≤ t) (ht_high : t ≤ W) :
    0 ≤ q t (p (W ^ 4) t + p (W ^ 4) s) := by
  have htx : 0 ≤ t * (p (W ^ 4) t) 0 := mul_p_x_nonneg (W ^ 4) t
  have hty : 0 ≤ (p (W ^ 4) t) 1 :=
    p_y_nonneg_signed W t hW0 hW1 ht_low ht_high
  have hsx := p_x_signed_bounds (W ^ 4) W s hW0 hs_low hs_high
  have hsy := p_y_ge_half_eta_signed W s hW0 hW1 hs_low hs_high
  have hts_prod : -W ^ 4 / 2 ≤ t * (p (W ^ 4) s) 0 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ W + t) (by linarith [hsx.1] : 0 ≤ W ^ 3 / 2 + (p (W ^ 4) s) 0),
      mul_nonneg (by linarith : 0 ≤ W - t) (by linarith [hsx.2] : 0 ≤ W ^ 3 / 2 - (p (W ^ 4) s) 0)]
  rw [q_add]
  simp only [q]
  linarith

theorem generators_support_signed (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, -W ≤ s ∧ s ≤ W) (t : ℝ) (ht : t ∈ T) :
    ∀ g ∈ generators (W ^ 4) T, q t g ≤ q t (p (W ^ 4) t) := by
  rcases hT t ht with ⟨ht_low, ht_high⟩
  intro g hg
  rcases hg with hg | hg
  · rcases hg with ⟨s, _hsT, rfl⟩
    have h := q_p_sub_p_nonneg_signed (W ^ 4) s t
    rw [q_sub] at h
    linarith
  · rcases hg with ⟨s, hsT, rfl⟩
    rcases hT s hsT with ⟨hs_low, hs_high⟩
    have h := q_p_add_p_nonneg_signed W s t hW0 hW1 hs_low hs_high ht_low ht_high
    rw [q_add] at h
    change q t (-p (W ^ 4) s) ≤ q t (p (W ^ 4) t)
    rw [q_neg]
    linarith

theorem inner_eq_dot (u v : Plane) : ⟪u, v⟫_ℝ = dot u v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dot, dotProduct, Fin.sum_univ_two, mul_comm]

theorem dot_normal_eq_q_div (t : ℝ) (z : Plane) :
    dot z (normal t) = q t z / Real.sqrt (1 + t ^ 2) := by
  simp only [dot, normal_zero, normal_one, q]
  ring

theorem generators_inner_support_signed (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, -W ≤ s ∧ s ≤ W) (t : ℝ) (ht : t ∈ T) :
    ∀ g ∈ generators (W ^ 4) T, ⟪normal t, g - p (W ^ 4) t⟫_ℝ ≤ 0 := by
  intro g hg
  have hq := generators_support_signed W T hW0 hW1 hT t ht g hg
  have hqsub : q t (g - p (W ^ 4) t) ≤ 0 := by rw [q_sub]; linarith
  rw [real_inner_comm, inner_eq_dot, dot_normal_eq_q_div]
  exact div_nonpos_of_nonpos_of_nonneg hqsub (le_of_lt (sqrt_rad_pos t))

theorem D_inner_support_signed (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, -W ≤ s ∧ s ≤ W) (t : ℝ) (ht : t ∈ T) :
    ∀ z ∈ D (W ^ 4) T, ⟪z - p (W ^ 4) t, normal t⟫_ℝ ≤ 0 := by
  have hconv : Convex ℝ {z : Plane | ⟪normal t, z - p (W ^ 4) t⟫_ℝ ≤ 0} := by
    simpa only [Set.preimage, Set.mem_Iic, innerₛₗ_apply_apply,
      inner_sub_right, sub_nonpos] using
      (convex_Iic (𝕜 := ℝ) ⟪normal t, p (W ^ 4) t⟫_ℝ).linear_preimage
        (innerₛₗ ℝ (normal t))
  have hgen : generators (W ^ 4) T ⊆
      {z : Plane | ⟪normal t, z - p (W ^ 4) t⟫_ℝ ≤ 0} := by
    intro g hg
    exact generators_inner_support_signed W T hW0 hW1 hT t ht g hg
  intro z hz
  have hz' := convexHull_min hgen hconv hz
  change ⟪normal t, z - p (W ^ 4) t⟫_ℝ ≤ 0 at hz'
  rwa [real_inner_comm] at hz'

theorem p_mem_D (η : ℝ) (T : Finset ℝ) (t : ℝ) (ht : t ∈ T) :
    p η t ∈ D η T := by
  apply subset_convexHull ℝ (generators η T)
  exact Or.inl ⟨t, ht, rfl⟩

theorem normal_norm_one (t : ℝ) : ‖normal t‖ = 1 := by
  have hs : ‖normal t‖ ^ 2 = dot (normal t) (normal t) := by
    simp [dot, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    ring
  rw [normal_dot_self] at hs
  nlinarith [norm_nonneg (normal t)]

theorem generators_finite (η : ℝ) (T : Finset ℝ) :
    (generators η T).Finite := by
  exact ((T.finite_toSet.image (p η)).union
    (T.finite_toSet.image (fun s : ℝ => -p η s)))

theorem D_compact (η : ℝ) (T : Finset ℝ) : IsCompact (D η T) := by
  exact (generators_finite η T).isCompact_convexHull ℝ

theorem D_convex (η : ℝ) (T : Finset ℝ) : Convex ℝ (D η T) :=
  convex_convexHull ℝ (generators η T)

theorem D_nonempty (η : ℝ) (T : Finset ℝ) (hT : T.Nonempty) :
    (D η T).Nonempty := by
  obtain ⟨t, ht⟩ := hT
  exact ⟨p η t, p_mem_D η T t ht⟩

/-- Full signed parabolic cap unit-distance theorem: for ANY finite set `T ⊆ [-W, W]`,
every `t ∈ T` has `Metric.infDist (gamma (W^4) t) (D (W^4) T) = 1`. -/
theorem D_unit_distance_signed (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, -W ≤ s ∧ s ≤ W) (t : ℝ) (ht : t ∈ T) :
    Metric.infDist (gamma (W ^ 4) t) (D (W ^ 4) T) = 1 := by
  let η := W ^ 4
  let γ := gamma η t
  let contact := p η t
  let ν := normal t
  let body := D η T
  have hp : contact ∈ body := p_mem_D η T t ht
  have hγ : γ = contact + ν := by simp [γ, contact, ν, p]
  have hν : ‖ν‖ = 1 := normal_norm_one t
  have hsupport : ∀ z ∈ body, ⟪z - contact, ν⟫_ℝ ≤ 0 :=
    D_inner_support_signed W T hW0 hW1 hT t ht
  have hlow : 1 ≤ Metric.infDist γ body := by
    apply (Metric.le_infDist ⟨contact, hp⟩).2
    intro z hz
    have hinner : 1 ≤ ⟪γ - z, ν⟫_ℝ := by
      rw [hγ, show contact + ν - z = ν - (z - contact) by abel,
        inner_sub_left, real_inner_self_eq_norm_sq, hν]
      nlinarith [hsupport z hz]
    have hcs := real_inner_le_norm (γ - z) ν
    rw [hν, mul_one] at hcs
    rw [dist_eq_norm]
    exact hinner.trans hcs
  have hupp : Metric.infDist γ body ≤ 1 := by
    calc
      Metric.infDist γ body ≤ dist γ contact := Metric.infDist_le_dist_of_mem hp
      _ = 1 := by rw [dist_eq_norm, hγ, add_sub_cancel_left, hν]
  exact le_antisymm hupp hlow

theorem D_unit_distance (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, 0 ≤ s ∧ s ≤ W) (t : ℝ) (ht : t ∈ T) :
    Metric.infDist (gamma (W ^ 4) t) (D (W ^ 4) T) = 1 :=
  D_unit_distance_signed W T hW0 hW1
    (fun s hs => ⟨by linarith [(hT s hs).1], (hT s hs).2⟩) t ht

theorem generators_neg_eq (η : ℝ) (T : Finset ℝ) :
    -(generators η T) = generators η T := by
  have hneg : ∀ z ∈ generators η T, -z ∈ generators η T := by
    intro z hz
    change z ∈ p η '' (T : Set ℝ) ∪
      (fun s : ℝ => -p η s) '' (T : Set ℝ) at hz
    rcases hz with hz | hz
    · rcases hz with ⟨s, hs, rfl⟩
      exact Or.inr ⟨s, hs, rfl⟩
    · rcases hz with ⟨s, hs, rfl⟩
      simp only [neg_neg]
      exact Or.inl ⟨s, hs, rfl⟩
  apply Set.Subset.antisymm
  · intro z hz
    have hzn : -z ∈ generators η T := (Set.mem_neg).mp hz
    simpa only [neg_neg] using hneg (-z) hzn
  · intro z hz
    exact (Set.mem_neg).2 (hneg z hz)

theorem D_neg_eq (η : ℝ) (T : Finset ℝ) : -(D η T) = D η T := by
  calc
    -(D η T) = convexHull ℝ (-(generators η T)) :=
      (convexHull_neg (𝕜 := ℝ) (generators η T)).symm
    _ = convexHull ℝ (generators η T) := by rw [generators_neg_eq]
    _ = D η T := rfl

def coordinateBox (W : ℝ) : Set Plane :=
  {z | z 0 ∈ Set.Icc (-W ^ 3 / 2) (W ^ 3 / 2)} ∩
  {z | z 1 ∈ Set.Icc (-(W ^ 4)) (W ^ 4)}

theorem coordinateBox_convex (W : ℝ) : Convex ℝ (coordinateBox W) := by
  have hx : Convex ℝ {z : Plane | z 0 ∈ Set.Icc (-W ^ 3 / 2) (W ^ 3 / 2)} := by
    simpa only [Set.preimage, EuclideanSpace.projₗ, PiLp.projₗ_apply] using
      (convex_Icc (𝕜 := ℝ) (-W ^ 3 / 2) (W ^ 3 / 2)).linear_preimage
        (EuclideanSpace.projₗ (0 : Fin 2))
  have hy : Convex ℝ {z : Plane | z 1 ∈ Set.Icc (-(W ^ 4)) (W ^ 4)} := by
    simpa only [Set.preimage, EuclideanSpace.projₗ, PiLp.projₗ_apply] using
      (convex_Icc (𝕜 := ℝ) (-(W ^ 4)) (W ^ 4)).linear_preimage
        (EuclideanSpace.projₗ (1 : Fin 2))
  exact hx.inter hy

theorem generators_subset_coordinateBox_signed (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, -W ≤ s ∧ s ≤ W) :
    generators (W ^ 4) T ⊆ coordinateBox W := by
  have hW4 : 0 ≤ W ^ 4 := by positivity
  intro g hg
  rcases hg with hg | hg
  · rcases hg with ⟨s, hs, rfl⟩
    rcases hT s hs with ⟨hs_low, hs_high⟩
    have hx := p_x_signed_bounds (W ^ 4) W s hW0 hs_low hs_high
    have hy0 := p_y_nonneg_signed W s hW0 hW1 hs_low hs_high
    have hy1 := p_y_le_eta (W ^ 4) s
    change (p (W ^ 4) s) 0 ∈ Set.Icc (-W ^ 3 / 2) (W ^ 3 / 2) ∧
      (p (W ^ 4) s) 1 ∈ Set.Icc (-(W ^ 4)) (W ^ 4)
    simp only [Set.mem_Icc]
    exact ⟨⟨hx.1, hx.2⟩, ⟨by linarith, hy1⟩⟩
  · rcases hg with ⟨s, hs, rfl⟩
    rcases hT s hs with ⟨hs_low, hs_high⟩
    have hx := p_x_signed_bounds (W ^ 4) W s hW0 hs_low hs_high
    have hy0 := p_y_nonneg_signed W s hW0 hW1 hs_low hs_high
    have hy1 := p_y_le_eta (W ^ 4) s
    change (-p (W ^ 4) s) 0 ∈ Set.Icc (-W ^ 3 / 2) (W ^ 3 / 2) ∧
      (-p (W ^ 4) s) 1 ∈ Set.Icc (-(W ^ 4)) (W ^ 4)
    simp only [Set.mem_Icc, PiLp.neg_apply]
    exact ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, ⟨by linarith, by linarith⟩⟩

theorem D_subset_coordinateBox_signed (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, -W ≤ s ∧ s ≤ W) :
    D (W ^ 4) T ⊆ coordinateBox W := by
  exact convexHull_min
    (generators_subset_coordinateBox_signed W T hW0 hW1 hT)
    (coordinateBox_convex W)

theorem D_abs_box_signed (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, -W ≤ s ∧ s ≤ W) :
    ∀ z ∈ D (W ^ 4) T, |z 0| ≤ W ^ 3 / 2 ∧ |z 1| ≤ W ^ 4 := by
  intro z hz
  have hb := D_subset_coordinateBox_signed W T hW0 hW1 hT hz
  change z 0 ∈ Set.Icc (-W ^ 3 / 2) (W ^ 3 / 2) ∧
    z 1 ∈ Set.Icc (-(W ^ 4)) (W ^ 4) at hb
  have hx := Set.mem_Icc.mp hb.1
  have hx' : -(W ^ 3 / 2) ≤ z 0 ∧ z 0 ≤ W ^ 3 / 2 := by
    constructor
    · linarith [hx.1]
    · exact hx.2
  exact ⟨abs_le.mpr hx', abs_le.mpr (Set.mem_Icc.mp hb.2)⟩

theorem D_abs_box (W : ℝ) (T : Finset ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1)
    (hT : ∀ s ∈ T, 0 ≤ s ∧ s ≤ W) :
    ∀ z ∈ D (W ^ 4) T, |z 0| ≤ W ^ 3 / 2 ∧ |z 1| ≤ W ^ 4 :=
  D_abs_box_signed W T hW0 hW1
    (fun s hs => ⟨by linarith [(hT s hs).1], (hT s hs).2⟩)

theorem triangle_interior {S : Set Plane} {η x y : ℝ}
    (hη : 0 < η) (hx : 0 < x)
    (hplus : point 0 η ∈ S) (hminus : point 0 (-η) ∈ S)
    (hX : point x y ∈ S) :
    (interior (convexHull ℝ S)).Nonempty := by
  let f : Fin 2 → Plane := ![point x y - point 0 (-η),
    point 0 η - point 0 (-η)]
  have hli : LinearIndependent ℝ f := by
    refine linearIndependent_fin2.mpr ⟨?_, ?_⟩
    · intro h
      have hc := congrArg (fun z : Plane => z 1) h
      simp [f] at hc
      linarith
    · intro a h
      have hc := congrArg (fun z : Plane => z 0) h
      simp [f] at hc
      linarith
  have hf0 : f 0 ∈ vectorSpan ℝ S := by
    simpa [f, vsub_eq_sub] using vsub_mem_vectorSpan ℝ hX hminus
  have hf1 : f 1 ∈ vectorSpan ℝ S := by
    simpa [f, vsub_eq_sub] using vsub_mem_vectorSpan ℝ hplus hminus
  have hsub : Set.range f ⊆ (vectorSpan ℝ S : Set Plane) := by
    rintro v ⟨i, rfl⟩
    fin_cases i
    · exact hf0
    · exact hf1
  have hspan : Submodule.span ℝ (Set.range f) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hvtop : vectorSpan ℝ S = ⊤ := by
    apply top_unique
    calc
      (⊤ : Submodule ℝ Plane) = Submodule.span ℝ (Set.range f) := hspan.symm
      _ ≤ vectorSpan ℝ S := Submodule.span_le.mpr hsub
  have hstop : affineSpan ℝ S = ⊤ :=
    (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
      ℝ Plane Plane ⟨_, hplus⟩).2 hvtop
  exact interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hstop

theorem p_at_zero (η : ℝ) : p η 0 = point 0 η := by
  ext i
  fin_cases i <;> simp [p_zero, p_one, point]

theorem point_coord_repr (z : Plane) : point (z 0) (z 1) = z := by
  ext i
  fin_cases i <;> simp

theorem p_x_pos (η W : ℝ) (hW : 0 < W) : 0 < (p η W) 0 := by
  rw [p_zero]
  have hδ : 0 < 1 - 1 / Real.sqrt (1 + W ^ 2) := by
    rw [reciprocal_error_identity]
    positivity
  have hfactor : W - W / Real.sqrt (1 + W ^ 2) =
      W * (1 - 1 / Real.sqrt (1 + W ^ 2)) := by ring
  rw [hfactor]
  exact mul_pos hW hδ

theorem D_interior_nonempty (W : ℝ) (T : Finset ℝ)
    (hW : 0 < W) (h0 : (0 : ℝ) ∈ T) (hWT : W ∈ T) :
    (interior (D (W ^ 4) T)).Nonempty := by
  let η := W ^ 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hp0 : point 0 η ∈ generators η T := by
    rw [← p_at_zero η]
    exact Or.inl ⟨0, h0, rfl⟩
  have hm0 : point 0 (-η) ∈ generators η T := by
    have hneg : -p η 0 = point 0 (-η) := by
      rw [p_at_zero]
      ext i
      fin_cases i <;> simp [point]
    rw [← hneg]
    exact Or.inr ⟨0, h0, rfl⟩
  have hpW : p η W ∈ generators η T := Or.inl ⟨W, hWT, rfl⟩
  have hX : point ((p η W) 0) ((p η W) 1) ∈ generators η T := by
    rwa [point_coord_repr]
  exact triangle_interior hη (p_x_pos η W hW) hp0 hm0 hX

theorem half_D_interior_nonempty (W : ℝ) (T : Finset ℝ)
    (hW : 0 < W) (h0 : (0 : ℝ) ∈ T) (hWT : W ∈ T) :
    (interior ((1 / 2 : ℝ) • D (W ^ 4) T)).Nonempty := by
  obtain ⟨z, hz⟩ := D_interior_nonempty W T hW h0 hWT
  rw [interior_smul₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  exact ⟨(1 / 2 : ℝ) • z, Set.smul_mem_smul_set hz⟩

end Erdos956.Geometry

/-!
## Section 2: Rational Grid Parameters (Unsigned and Signed)
-/

namespace Erdos956.Parameters

noncomputable def W (k : ℕ) : ℝ := (1 / 10 : ℝ) / k
noncomputable def a (k : ℕ) : ℝ := W k / k
noncomputable def b (k : ℕ) : ℝ := (a k) ^ 2 / 2
noncomputable def eta (k : ℕ) : ℝ := (W k) ^ 4
noncomputable def T (k : ℕ) : Finset ℝ :=
  (Finset.range (k + 1)).image (fun i : ℕ => (i : ℝ) * a k)

/-- Signed parameter set `{i * a k : -k ≤ i ≤ k}` for the signed parabolic cap. -/
noncomputable def signedT (k : ℕ) : Finset ℝ :=
  (Finset.Icc (-(k : ℤ)) (k : ℤ)).image (fun i : ℤ => (i : ℝ) * a k)

private theorem k_real_pos (k : ℕ) (hk : 1 ≤ k) : (0 : ℝ) < k := by
  exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hk)

private theorem k_real_ne_zero (k : ℕ) (hk : 1 ≤ k) : (k : ℝ) ≠ 0 :=
  ne_of_gt (k_real_pos k hk)

theorem W_formula (k : ℕ) (_hk : 1 ≤ k) :
    W k = 1 / (10 * (k : ℝ)) := by
  unfold W
  ring

theorem a_formula (k : ℕ) (hk : 1 ≤ k) :
    a k = 1 / (10 * (k : ℝ) ^ 2) := by
  rw [a, W_formula k hk]
  ring

theorem b_formula (k : ℕ) (hk : 1 ≤ k) :
    b k = 1 / (200 * (k : ℝ) ^ 4) := by
  rw [b, a_formula k hk]
  ring

theorem eta_formula (k : ℕ) (hk : 1 ≤ k) :
    eta k = 1 / (10000 * (k : ℝ) ^ 4) := by
  rw [eta, W_formula k hk]
  ring

theorem W_pos (k : ℕ) (hk : 1 ≤ k) : 0 < W k := by
  rw [W_formula k hk]
  positivity

theorem W_le_one (k : ℕ) (hk : 1 ≤ k) : W k ≤ 1 := by
  rw [W_formula k hk]
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 10 * k := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

theorem a_pos (k : ℕ) (hk : 1 ≤ k) : 0 < a k := by
  rw [a_formula k hk]
  positivity

theorem b_pos (k : ℕ) (hk : 1 ≤ k) : 0 < b k := by
  rw [b_formula k hk]
  positivity

theorem eta_pos (k : ℕ) (hk : 1 ≤ k) : 0 < eta k := by
  rw [eta_formula k hk]
  positivity

theorem cap_width_lt_a (k : ℕ) (hk : 1 ≤ k) :
    (W k) ^ 3 / 2 < a k := by
  rw [W_formula k hk, a_formula k hk]
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := k_real_pos k hk
  have hden : (0 : ℝ) < 2000 * k ^ 3 := by positivity
  have hden2 : (0 : ℝ) < 10 * k ^ 2 := by positivity
  have hleft : (1 / (10 * (k : ℝ))) ^ 3 / 2 =
      1 / (2000 * (k : ℝ) ^ 3) := by
    field_simp [k_real_ne_zero k hk]; ring
  rw [hleft]
  apply (one_div_lt_one_div hden hden2).2
  nlinarith [sq_nonneg (k - 1)]

theorem eta_lt_b (k : ℕ) (hk : 1 ≤ k) : eta k < b k := by
  rw [eta_formula k hk, b_formula k hk]
  have hkp : (0 : ℝ) < k := k_real_pos k hk
  have hden : (0 : ℝ) < 10000 * k ^ 4 := by positivity
  have hden2 : (0 : ℝ) < 200 * k ^ 4 := by positivity
  apply (one_div_lt_one_div hden hden2).2
  nlinarith [pow_pos hkp 4]

theorem grid_height_lt_one (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ 2 * b k < 1 := by
  rw [b_formula k hk]
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := k_real_pos k hk
  have hrewrite : (k : ℝ) ^ 2 * (1 / (200 * k ^ 4)) =
      1 / (200 * k ^ 2) := by
    field_simp [ne_of_gt hkp]
  rw [hrewrite]
  have hden : (0 : ℝ) < 200 * k ^ 2 := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem mem_T_range (k : ℕ) (hk : 1 ≤ k) {t : ℝ} (ht : t ∈ T k) :
    0 ≤ t ∧ t ≤ W k := by
  rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
  have hi : i ≤ k := by
    have hi' : i < k + 1 := Finset.mem_range.mp hi
    omega
  have hir : (0 : ℝ) ≤ i := by exact_mod_cast (Nat.zero_le i)
  have hirk : (i : ℝ) ≤ k := by exact_mod_cast hi
  have ha := a_pos k hk
  have hW : (k : ℝ) * a k = W k := by
    rw [a]
    field_simp [k_real_ne_zero k hk]
  constructor
  · exact mul_nonneg hir ha.le
  · rw [← hW]
    exact mul_le_mul_of_nonneg_right hirk ha.le

theorem step_mem_T (k i : ℕ) (hi : i ≤ k) : (i : ℝ) * a k ∈ T k := by
  unfold T
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, rfl⟩
  simp only [Finset.mem_range]
  omega

theorem mem_signedT_range (k : ℕ) (hk : 1 ≤ k) {t : ℝ} (ht : t ∈ signedT k) :
    -W k ≤ t ∧ t ≤ W k := by
  rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
  rcases Finset.mem_Icc.mp hi with ⟨hlow, hhigh⟩
  have hilow : -(k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hlow
  have hihigh : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hhigh
  have ha := (a_pos k hk).le
  have hW : (k : ℝ) * a k = W k := by
    rw [a]
    field_simp [k_real_ne_zero k hk]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hilow ha
    linarith
  · have hmul := mul_le_mul_of_nonneg_right hihigh ha
    linarith

theorem int_step_mem_signedT (k : ℕ) (i : ℤ)
    (hlow : -(k : ℤ) ≤ i) (hhigh : i ≤ (k : ℤ)) :
    (i : ℝ) * a k ∈ signedT k := by
  unfold signedT
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_Icc.mpr ⟨hlow, hhigh⟩, rfl⟩

end Erdos956.Parameters

/-!
## Section 3: Difference-Body & Remote Padding Reductions
-/

open scoped Pointwise

namespace Erdos956

/-- The Euclidean minimum distance between two translates of the same set. -/
noncomputable def translateSetDistance {E : Type*} [PseudoMetricSpace E] [AddGroup E]
    (C : Set E) (x y : E) : ℝ :=
  ⨅ c : C, ⨅ d : C, dist (c.1 + x) (d.1 + y)

section Normed

variable {E : Type*} [NormedAddCommGroup E]

private theorem difference_nonempty {C : Set E} (hC : C.Nonempty) : (C - C).Nonempty := by
  obtain ⟨c, hc⟩ := hC
  exact ⟨c - c, Set.sub_mem_sub hc hc⟩

private theorem dist_sub_eq_dist_translate (c d x y : E) :
    dist (y - x) (c - d) = dist (c + x) (d + y) := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : (y - x) - (c - d) = -((c + x) - (d + y)) := by abel
  rw [h, norm_neg]

theorem translateSetDistance_eq_infDist_sub (C : Set E) (hC : C.Nonempty) (x y : E) :
    translateSetDistance C x y = Metric.infDist (y - x) (C - C) := by
  have : Nonempty C := hC.to_subtype
  have hb_inner (c : C) :
      BddBelow (Set.range (fun d : C => dist (c.1 + x) (d.1 + y))) := by
    refine ⟨0, ?_⟩
    rintro z ⟨d, rfl⟩
    exact dist_nonneg
  have hnonneg_inner (c : C) :
      0 ≤ ⨅ d : C, dist (c.1 + x) (d.1 + y) :=
    le_ciInf fun d => dist_nonneg
  have hb_outer :
      BddBelow (Set.range (fun c : C => ⨅ d : C, dist (c.1 + x) (d.1 + y))) := by
    refine ⟨0, ?_⟩
    rintro z ⟨c, rfl⟩
    exact hnonneg_inner c
  apply le_antisymm
  · apply (Metric.le_infDist (difference_nonempty hC)).2
    intro z hz
    rcases Set.mem_sub.mp hz with ⟨c, hc, d, hd, rfl⟩
    have hle : translateSetDistance C x y ≤ dist (c + x) (d + y) := by
      unfold translateSetDistance
      exact (ciInf_le hb_outer (⟨c, hc⟩ : C)).trans
        (ciInf_le (hb_inner (⟨c, hc⟩ : C)) (⟨d, hd⟩ : C))
    rwa [dist_sub_eq_dist_translate]
  · unfold translateSetDistance
    apply le_ciInf
    intro c
    apply le_ciInf
    intro d
    have hm : (c.1 - d.1) ∈ C - C := Set.sub_mem_sub c.2 d.2
    have hle := Metric.infDist_le_dist_of_mem (x := y - x) hm
    rwa [dist_sub_eq_dist_translate] at hle

theorem translates_disjoint_iff_sub_not_mem (C : Set E) (x y : E) :
    Disjoint ((· + x) '' C) ((· + y) '' C) ↔ y - x ∉ C - C := by
  constructor
  · intro h hz
    rcases Set.mem_sub.mp hz with ⟨c, hc, d, hd, heq⟩
    have hxy : c + x = d + y := by
      apply sub_eq_zero.mp
      calc
        (c + x) - (d + y) = (c - d) - (y - x) := by abel
        _ = 0 := sub_eq_zero.mpr heq
    exact (Set.disjoint_left.mp h) ⟨c, hc, rfl⟩ ⟨d, hd, hxy.symm⟩
  · intro h
    apply Set.disjoint_left.mpr
    intro z hz1 hz2
    rcases hz1 with ⟨c, hc, rfl⟩
    rcases hz2 with ⟨d, hd, heq⟩
    apply h
    have hxy : c - d = y - x := by
      apply sub_eq_zero.mp
      calc
        (c - d) - (y - x) = (c + x) - (d + y) := by abel
        _ = 0 := sub_eq_zero.mpr heq.symm
    exact hxy ▸ Set.sub_mem_sub hc hd

end Normed

section HalfBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem half_body_difference_subset (D : Set E) (hconvex : Convex ℝ D)
    (hsymmetric : ∀ z ∈ D, -z ∈ D) :
    ((1 / 2 : ℝ) • D - (1 / 2 : ℝ) • D) ⊆ D := by
  intro z hz
  rcases Set.mem_sub.mp hz with ⟨c, hc, d, hd, rfl⟩
  rcases Set.mem_smul_set.mp hc with ⟨u, hu, rfl⟩
  rcases Set.mem_smul_set.mp hd with ⟨v, hv, rfl⟩
  have hmid : midpoint ℝ u (-v) ∈ D := hconvex.midpoint_mem hu (hsymmetric v hv)
  convert hmid using 1
  simp only [midpoint_eq_smul_add, invOf_eq_inv, one_div, smul_add,
    smul_neg, sub_eq_add_neg]

theorem mem_half_body_difference_of_mem (D : Set E) {p : E}
    (hp : p ∈ D) (hneg : -p ∈ D) :
    p ∈ (1 / 2 : ℝ) • D - (1 / 2 : ℝ) • D := by
  have hmem := Set.sub_mem_sub
    (Set.smul_mem_smul_set (a := (1 / 2 : ℝ)) hp)
    (Set.smul_mem_smul_set (a := (1 / 2 : ℝ)) hneg)
  have h : (1 / 2 : ℝ) • p - (1 / 2 : ℝ) • (-p) = p := by
    rw [smul_neg, sub_neg_eq_add, ← add_smul]
    norm_num
  exact h ▸ hmem

theorem half_body_translates_disjoint_of_diff_not_mem
    (D : Set E) (hconvex : Convex ℝ D) (hsymmetric : ∀ z ∈ D, -z ∈ D)
    {x y : E} (hxy : y - x ∉ D) :
    Disjoint ((· + x) '' ((1 / 2 : ℝ) • D))
      ((· + y) '' ((1 / 2 : ℝ) • D)) := by
  apply (translates_disjoint_iff_sub_not_mem ((1 / 2 : ℝ) • D) x y).2
  exact fun h => hxy ((half_body_difference_subset D hconvex hsymmetric) h)

theorem half_body_isCompact (D : Set E) (hD : IsCompact D) :
    IsCompact ((1 / 2 : ℝ) • D) := hD.smul _

theorem half_body_convex (D : Set E) (hD : Convex ℝ D) :
    Convex ℝ ((1 / 2 : ℝ) • D) := hD.smul _

theorem translateSetDistance_one_of_body
    (D : Set E) (hconvex : Convex ℝ D) (hsymmetric : ∀ z ∈ D, -z ∈ D)
    {p γ x y : E} (hp : p ∈ D) (hγ : y - x = γ)
    (hDist : Metric.infDist γ D = 1) (hclose : dist γ p = 1) :
    translateSetDistance ((1 / 2 : ℝ) • D) x y = 1 := by
  let C : Set E := (1 / 2 : ℝ) • D
  have hpC : ((1 / 2 : ℝ) • p) ∈ C := Set.smul_mem_smul_set hp
  have hC : C.Nonempty := ⟨_, hpC⟩
  have hsubset : C - C ⊆ D := half_body_difference_subset D hconvex hsymmetric
  have hpin : p ∈ C - C := mem_half_body_difference_of_mem D hp (hsymmetric p hp)
  have hlow : 1 ≤ Metric.infDist γ (C - C) := by
    rw [← hDist]
    exact Metric.infDist_le_infDist_of_subset hsubset ⟨p, hpin⟩
  have hupp : Metric.infDist γ (C - C) ≤ 1 := by
    exact (Metric.infDist_le_dist_of_mem hpin).trans_eq hclose
  rw [translateSetDistance_eq_infDist_sub C hC, hγ]
  exact le_antisymm hupp hlow

end HalfBody

end Erdos956

namespace Erdos956.Padding

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := by simp [point]

def remote (j : ℕ) : Plane := point (10 * ((j : ℝ) + 1)) 0

noncomputable def remoteCenters (t : ℕ) : Finset Plane :=
  (Finset.range t).image remote

theorem remote_x_ge_ten (j : ℕ) : 10 ≤ (remote j) 0 := by
  simp only [remote, point_zero]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  nlinarith

theorem remote_injective : Function.Injective remote := by
  intro j l h
  have hx : 10 * ((j : ℝ) + 1) = 10 * ((l : ℝ) + 1) := by
    simpa only [remote, point_zero] using congrArg (fun z : Plane => z 0) h
  have hc : (j : ℝ) = (l : ℝ) := by nlinarith
  exact_mod_cast hc

theorem remoteCenters_card (t : ℕ) : (remoteCenters t).card = t := by
  unfold remoteCenters
  rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => remote_injective h)]
  simp

theorem old_remote_disjoint (X : Finset Plane)
    (hX : ∀ x ∈ X, x 0 ≤ 1) (t : ℕ) :
    Disjoint X (remoteCenters t) := by
  apply Finset.disjoint_left.mpr
  intro x hxX hxR
  rcases Finset.mem_image.mp hxR with ⟨j, _, rfl⟩
  have hx := hX (remote j) hxX
  have hr := remote_x_ge_ten j
  linarith

noncomputable def paddedCenters (X : Finset Plane) (t : ℕ) : Finset Plane :=
  X ∪ remoteCenters t

theorem paddedCenters_card (X : Finset Plane)
    (hX : ∀ x ∈ X, x 0 ≤ 1) (t : ℕ) :
    (paddedCenters X t).card = X.card + t := by
  unfold paddedCenters
  rw [Finset.card_union_of_disjoint (old_remote_disjoint X hX t), remoteCenters_card]

theorem paddedCenters_card_exact (X : Finset Plane)
    (hX : ∀ x ∈ X, x 0 ≤ 1) {N : ℕ} (hXN : X.card ≤ N) :
    (paddedCenters X (N - X.card)).card = N := by
  rw [paddedCenters_card X hX]
  omega

private theorem remote_gap (j l : ℕ) (hjl : j ≠ l) :
    1 / 2 < |(remote l) 0 - (remote j) 0| := by
  have hlt : j < l ∨ l < j := lt_or_gt_of_ne hjl
  rcases hlt with hlt | hlt
  · have hcast : (j : ℝ) + 1 ≤ l := by exact_mod_cast (by omega : j + 1 ≤ l)
    have hval : 10 ≤ (remote l) 0 - (remote j) 0 := by
      simp only [remote, point_zero]
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hcast : (l : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : l + 1 ≤ j)
    have hval : (remote l) 0 - (remote j) 0 ≤ -10 := by
      simp only [remote, point_zero]
      nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem padded_differences_excluded (D : Set Plane) (X : Finset Plane) (t : ℕ)
    (hD : ∀ z ∈ D, |z 0| ≤ 1 / 2)
    (hXlow : ∀ x ∈ X, 0 ≤ x 0)
    (hXhigh : ∀ x ∈ X, x 0 ≤ 1)
    (hold : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → y - x ∉ D) :
    ∀ x ∈ paddedCenters X t, ∀ y ∈ paddedCenters X t,
      x ≠ y → y - x ∉ D := by
  intro x hx y hy hne hz
  have hhalf : |(y - x) 0| ≤ 1 / 2 := hD (y - x) hz
  have hcoord : (y - x) 0 = y 0 - x 0 := by simp
  rw [hcoord] at hhalf
  rcases Finset.mem_union.mp hx with hxX | hxR
  · rcases Finset.mem_union.mp hy with hyX | hyR
    · exact hold x hxX y hyX hne hz
    · rcases Finset.mem_image.mp hyR with ⟨j, _, rfl⟩
      have hxhigh := hXhigh x hxX
      have hyten := remote_x_ge_ten j
      have hgap : 9 ≤ (remote j) 0 - x 0 := by linarith
      have habs : 9 ≤ |(remote j) 0 - x 0| := by
        rw [abs_of_nonneg (by linarith)]
        exact hgap
      linarith
  · rcases Finset.mem_image.mp hxR with ⟨j, _, rfl⟩
    rcases Finset.mem_union.mp hy with hyX | hyR
    · have hylow := hXlow y hyX
      have hyhigh := hXhigh y hyX
      have hxten := remote_x_ge_ten j
      have hgap : y 0 - (remote j) 0 ≤ -9 := by linarith
      have habs : 9 ≤ |y 0 - (remote j) 0| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      linarith
    · rcases Finset.mem_image.mp hyR with ⟨l, _, rfl⟩
      have hneIndex : j ≠ l := fun he => hne (he ▸ rfl)
      have hgap := remote_gap j l hneIndex
      linarith

end Erdos956.Padding

/-!
## Section 4: Two-Layer Center Grids & Bipartite Unordered Counting
-/

namespace Erdos956Centers

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := by simp [point]
@[simp] theorem point_one (x y : ℝ) : point x y 1 = y := by simp [point]

abbrev Rect (k : ℕ) := Fin (k + 1) × Fin (k * k + 1)
abbrev GridIndex (k : ℕ) := Sum (Rect k) (Rect k)

def center (k : ℕ) (a b η : ℝ) : GridIndex k → Plane
  | .inl p => point (((p.1.val : ℕ) : ℝ) * a) (((p.2.val : ℕ) : ℝ) * b)
  | .inr p => point (((p.1.val : ℕ) : ℝ) * a)
      (1 + η + ((p.2.val : ℕ) : ℝ) * b)

theorem grid_index_card (k : ℕ) :
    Fintype.card (GridIndex k) = 2 * (k + 1) * (k * k + 1) := by
  simp [GridIndex, Rect, Fintype.card_sum, Fintype.card_prod]
  ring

private theorem index_le_square (p : Rect k) :
    ((p.2.val : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by
  have h : p.2.val ≤ k * k := by omega
  exact_mod_cast h

theorem cast_mul_gap {u v : ℕ} (huv : u ≠ v) (a : ℝ) (ha : 0 < a) :
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

theorem center_injective (k : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgap : ((k * k : ℕ) : ℝ) * b < 1 + η) :
    Function.Injective (center k a b η) := by
  intro u v huv
  cases u with
  | inl p =>
      cases v with
      | inl q =>
          have hx : ((p.1.val : ℕ) : ℝ) * a = ((q.1.val : ℕ) : ℝ) * a := by
            simpa [center] using congrArg (fun z : Plane => z 0) huv
          have hy : ((p.2.val : ℕ) : ℝ) * b = ((q.2.val : ℕ) : ℝ) * b := by
            simpa [center] using congrArg (fun z : Plane => z 1) huv
          have hpx : p.1 = q.1 := by
            apply Fin.ext
            exact_mod_cast (mul_right_cancel₀ (ne_of_gt ha) hx)
          have hpy : p.2 = q.2 := by
            apply Fin.ext
            exact_mod_cast (mul_right_cancel₀ (ne_of_gt hb) hy)
          exact congrArg Sum.inl (Prod.ext hpx hpy)
      | inr q =>
          have hy : ((p.2.val : ℕ) : ℝ) * b =
              1 + η + ((q.2.val : ℕ) : ℝ) * b := by
            simpa [center] using congrArg (fun z : Plane => z 1) huv
          have hpbound := index_le_square p
          have hpb : ((p.2.val : ℕ) : ℝ) * b ≤ ((k * k : ℕ) : ℝ) * b :=
            mul_le_mul_of_nonneg_right hpbound (le_of_lt hb)
          have hqnonneg : 0 ≤ ((q.2.val : ℕ) : ℝ) * b := by positivity
          exfalso
          linarith
  | inr p =>
      cases v with
      | inl q =>
          have hy : 1 + η + ((p.2.val : ℕ) : ℝ) * b =
              ((q.2.val : ℕ) : ℝ) * b := by
            simpa [center] using congrArg (fun z : Plane => z 1) huv
          have hqbound := index_le_square q
          have hqb : ((q.2.val : ℕ) : ℝ) * b ≤ ((k * k : ℕ) : ℝ) * b :=
            mul_le_mul_of_nonneg_right hqbound (le_of_lt hb)
          have hpnonneg : 0 ≤ ((p.2.val : ℕ) : ℝ) * b := by positivity
          exfalso
          linarith
      | inr q =>
          have hx : ((p.1.val : ℕ) : ℝ) * a = ((q.1.val : ℕ) : ℝ) * a := by
            simpa [center] using congrArg (fun z : Plane => z 0) huv
          have hy : 1 + η + ((p.2.val : ℕ) : ℝ) * b =
              1 + η + ((q.2.val : ℕ) : ℝ) * b := by
            simpa [center] using congrArg (fun z : Plane => z 1) huv
          have hpx : p.1 = q.1 := by
            apply Fin.ext
            exact_mod_cast (mul_right_cancel₀ (ne_of_gt ha) hx)
          have hpy : p.2 = q.2 := by
            apply Fin.ext
            have hmul : ((p.2.val : ℕ) : ℝ) * b =
                ((q.2.val : ℕ) : ℝ) * b := by linarith
            exact_mod_cast (mul_right_cancel₀ (ne_of_gt hb) hmul)
          exact congrArg Sum.inr (Prod.ext hpx hpy)

noncomputable def fullCenters (k : ℕ) (a b η : ℝ) : Finset Plane :=
  Finset.univ.image (center k a b η)

theorem full_centers_card (k : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgap : ((k * k : ℕ) : ℝ) * b < 1 + η) :
    (fullCenters k a b η).card = 2 * (k + 1) * (k * k + 1) := by
  unfold fullCenters
  rw [Finset.card_image_iff.mpr (fun _ _ _ _ h =>
    center_injective k a b η ha hb hgap h)]
  simpa using grid_index_card k

def horizontalIndex (i : GridIndex k) : ℕ :=
  match i with
  | .inl p => p.1.val
  | .inr p => p.1.val

@[simp] theorem center_zero (i : GridIndex k) (a b η : ℝ) :
    (center k a b η i) 0 = ((horizontalIndex i : ℕ) : ℝ) * a := by
  cases i <;> simp [center, horizontalIndex]

private theorem index_le_k (p : Rect k) :
    ((p.1.val : ℕ) : ℝ) ≤ (k : ℝ) := by
  have h : p.1.val ≤ k := by omega
  exact_mod_cast h

theorem center_x_bounds (i : GridIndex k) (a b η : ℝ) (ha : 0 ≤ a) :
    0 ≤ (center k a b η i) 0 ∧
      (center k a b η i) 0 ≤ (k : ℝ) * a := by
  cases i with
  | inl p =>
      simp only [center, point_zero]
      exact ⟨by positivity,
        mul_le_mul_of_nonneg_right (index_le_k p) ha⟩
  | inr p =>
      simp only [center, point_zero]
      exact ⟨by positivity,
        mul_le_mul_of_nonneg_right (index_le_k p) ha⟩

private theorem cross_vertical_gap (p q : Rect k) (b η : ℝ)
    (hb : 0 < b) (hη : 0 ≤ η)
    (hvertical : ((k * k : ℕ) : ℝ) * b < 1) :
    η < |(1 + η + ((q.2.val : ℕ) : ℝ) * b) -
      ((p.2.val : ℕ) : ℝ) * b| := by
  have hpbound := index_le_square p
  have hpb : ((p.2.val : ℕ) : ℝ) * b ≤ ((k * k : ℕ) : ℝ) * b :=
    mul_le_mul_of_nonneg_right hpbound (le_of_lt hb)
  have hqnonneg : 0 ≤ ((q.2.val : ℕ) : ℝ) * b := by positivity
  have hgt : η < (1 + η + ((q.2.val : ℕ) : ℝ) * b) -
      ((p.2.val : ℕ) : ℝ) * b := by linarith
  rw [abs_of_pos (lt_of_le_of_lt hη hgt)]
  exact hgt

theorem pair_difference_outside_box (i j : GridIndex k) (hij : i ≠ j)
    (a b η W : ℝ) (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hhorizontal : W ^ 3 / 2 < a) (hvertical : η < b)
    (hlayer : ((k * k : ℕ) : ℝ) * b < 1) :
    W ^ 3 / 2 < |(center k a b η j - center k a b η i) 0| ∨
      η < |(center k a b η j - center k a b η i) 1| := by
  by_cases hx : horizontalIndex i ≠ horizontalIndex j
  · left
    simp only [PiLp.sub_apply, center_zero]
    exact hhorizontal.trans_le (cast_mul_gap hx.symm a ha)
  · have hxsame : horizontalIndex i = horizontalIndex j := not_ne_iff.mp hx
    right
    cases i with
    | inl p =>
        cases j with
        | inl q =>
            have hpx : p.1 = q.1 := Fin.ext (by simpa [horizontalIndex] using hxsame)
            have hpy : p.2.val ≠ q.2.val := by
              intro hy
              exact hij (congrArg Sum.inl (Prod.ext hpx (Fin.ext hy)))
            simp only [PiLp.sub_apply, center, point_one]
            exact hvertical.trans_le (cast_mul_gap hpy.symm b hb)
        | inr q =>
            simp only [PiLp.sub_apply, center, point_one]
            exact cross_vertical_gap p q b η hb hη hlayer
    | inr p =>
        cases j with
        | inl q =>
            simp only [PiLp.sub_apply, center, point_one]
            have hgap := cross_vertical_gap q p b η hb hη hlayer
            have hneg : (((q.2.val : ℕ) : ℝ) * b -
                (1 + η + ((p.2.val : ℕ) : ℝ) * b)) =
                -((1 + η + ((p.2.val : ℕ) : ℝ) * b) -
                  ((q.2.val : ℕ) : ℝ) * b) := by ring
            rw [hneg, abs_neg]
            exact hgap
        | inr q =>
            have hpx : p.1 = q.1 := Fin.ext (by simpa [horizontalIndex] using hxsame)
            have hpy : p.2.val ≠ q.2.val := by
              intro hy
              exact hij (congrArg Sum.inr (Prod.ext hpx (Fin.ext hy)))
            simp only [PiLp.sub_apply, center, point_one]
            have hgap := cast_mul_gap hpy.symm b hb
            have hcancel :
                (1 + η + ((q.2.val : ℕ) : ℝ) * b) -
                  (1 + η + ((p.2.val : ℕ) : ℝ) * b) =
                ((q.2.val : ℕ) : ℝ) * b - ((p.2.val : ℕ) : ℝ) * b := by ring
            rw [hcancel]
            exact hvertical.trans_le hgap

theorem full_centers_pair_difference_outside_box
    {x y : Plane} (hx : x ∈ fullCenters k a b η)
    (hy : y ∈ fullCenters k a b η) (hxy : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hhorizontal : W ^ 3 / 2 < a) (hvertical : η < b)
    (hlayer : ((k * k : ℕ) : ℝ) * b < 1) :
    W ^ 3 / 2 < |(y - x) 0| ∨ η < |(y - x) 1| := by
  rcases Finset.mem_image.mp hx with ⟨i, -, hix⟩
  rcases Finset.mem_image.mp hy with ⟨j, -, hjy⟩
  have hij : i ≠ j := fun heq => hxy (hix.symm.trans (heq ▸ hjy))
  have hsep := pair_difference_outside_box i j hij a b η W
    ha hb hη hhorizontal hvertical hlayer
  rwa [hix, hjy] at hsep

theorem full_centers_pair_diff_not_mem_of_box
    (D : Set Plane) (hbox : ∀ z ∈ D,
      |z 0| ≤ W ^ 3 / 2 ∧ |z 1| ≤ η)
    {x y : Plane} (hx : x ∈ fullCenters k a b η)
    (hy : y ∈ fullCenters k a b η) (hxy : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 ≤ η)
    (hhorizontal : W ^ 3 / 2 < a) (hvertical : η < b)
    (hlayer : ((k * k : ℕ) : ℝ) * b < 1) :
    y - x ∉ D := by
  intro hmem
  have hbound := hbox (y - x) hmem
  rcases full_centers_pair_difference_outside_box hx hy hxy ha hb hη
      hhorizontal hvertical hlayer with h | h
  · exact not_lt_of_ge hbound.1 h
  · exact not_lt_of_ge hbound.2 h

end Erdos956Centers

namespace Erdos956.Counting

theorem unordered_pair_map_injOn_of_disjoint {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) :
    Set.InjOn (fun p : α × α => ({p.1, p.2} : Finset α)) (A ×ˢ B : Finset (α × α)) := by
  classical
  intro p hp q hq heq
  have hpA : p.1 ∈ A := (Finset.mem_product.mp hp).1
  have hpB : p.2 ∈ B := (Finset.mem_product.mp hp).2
  have hqA : q.1 ∈ A := (Finset.mem_product.mp hq).1
  have hqB : q.2 ∈ B := (Finset.mem_product.mp hq).2
  have hdisj : ∀ x, x ∈ A → x ∈ B → False := Finset.disjoint_left.mp hAB
  have hpair : ({p.1, p.2} : Finset α) = {q.1, q.2} := heq
  have h1 : p.1 = q.1 := by
    have hmem : p.1 ∈ ({q.1, q.2} : Finset α) := by rw [← hpair]; simp
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · have he : p.1 = q.2 := Finset.mem_singleton.mp h
      exact (hdisj p.1 hpA (he ▸ hqB)).elim
  have h2 : p.2 = q.2 := by
    have hmem : p.2 ∈ ({q.1, q.2} : Finset α) := by rw [← hpair]; simp
    rcases Finset.mem_insert.mp hmem with h | h
    · exact (hdisj q.1 hqA (h ▸ hpB)).elim
    · exact Finset.mem_singleton.mp h
  exact Prod.ext h1 h2

theorem ordered_edges_to_unordered {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (E : Finset (α × α))
    (hE : E ⊆ A ×ˢ B) :
    (E.image fun p : α × α => ({p.1, p.2} : Finset α)).card = E.card := by
  classical
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  exact (unordered_pair_map_injOn_of_disjoint A B hAB) (hE hp) (hE hq) heq

end Erdos956.Counting

namespace Erdos956Counting

def gridSize (k : ℕ) : ℕ := 2 * (k + 1) * (k * k + 1)

abbrev Core (m : ℕ) := Fin m × (Fin m × Fin (m * m))

def step (e : Core m) : ℕ := e.1.val + 1
def lowerX (e : Core m) : ℕ := e.2.1.val
def lowerY (m : ℕ) (e : Core m) : ℕ := m * m + e.2.2.val
def upperX (e : Core m) : ℕ := lowerX e + step e
def upperY (m : ℕ) (e : Core m) : ℕ := lowerY m e - (step e) ^ 2

def edgeIndices (m : ℕ) (e : Core m) :
    ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((lowerX e, lowerY m e), (upperX e, upperY m e))

theorem step_le (e : Core m) : step e ≤ m := by
  dsimp [step]
  omega

theorem lowerY_ge_step_sq (e : Core m) : (step e) ^ 2 ≤ lowerY m e := by
  have hi := step_le e
  have hs : (step e) ^ 2 ≤ m * m := by nlinarith
  dsimp [lowerY]
  omega

theorem edgeIndices_admissible (e : Core m) :
    1 ≤ step e ∧ step e ≤ 2 * m ∧
    lowerX e ≤ 2 * m - step e ∧
    (step e) ^ 2 ≤ lowerY m e ∧ lowerY m e ≤ (2 * m) ^ 2 ∧
    upperX e ≤ 2 * m ∧ upperY m e ≤ (2 * m) ^ 2 := by
  have hi := step_le e
  have hr : lowerX e < m := e.2.1.isLt
  have hs : e.2.2.val < m * m := e.2.2.isLt
  have hy := lowerY_ge_step_sq e
  have hxu : upperX e ≤ 2 * m := by dsimp [upperX]; omega
  have hyl : lowerY m e ≤ (2 * m) ^ 2 := by dsimp [lowerY]; nlinarith
  have hyu : upperY m e ≤ (2 * m) ^ 2 := by dsimp [upperY]; omega
  refine ⟨by dsimp [step]; omega, by omega, by dsimp [upperX] at hxu; omega,
    hy, hyl, hxu, hyu⟩

def lowerRect (e : Core m) :
    Fin (2 * m + 1) × Fin ((2 * m) * (2 * m) + 1) :=
  (⟨lowerX e, by
      obtain ⟨_, _, hx, _, _, _, _⟩ := edgeIndices_admissible e
      omega⟩,
   ⟨lowerY m e, by
      obtain ⟨_, _, _, _, hy, _, _⟩ := edgeIndices_admissible e
      have hsq : (2 * m) ^ 2 = (2 * m) * (2 * m) := by ring
      omega⟩)

def upperRect (e : Core m) :
    Fin (2 * m + 1) × Fin ((2 * m) * (2 * m) + 1) :=
  (⟨upperX e, by
      obtain ⟨_, _, _, _, _, hx, _⟩ := edgeIndices_admissible e
      omega⟩,
   ⟨upperY m e, by
      obtain ⟨_, _, _, _, _, _, hy⟩ := edgeIndices_admissible e
      have hsq : (2 * m) ^ 2 = (2 * m) * (2 * m) := by ring
      omega⟩)

theorem edgeIndices_injective (m : ℕ) : Function.Injective (edgeIndices m) := by
  intro e f hef
  have hr : lowerX e = lowerX f :=
    congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) hef
  have hs : lowerY m e = lowerY m f :=
    congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) hef
  have hx : upperX e = upperX f :=
    congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) hef
  have hstep : step e = step f := by dsimp [upperX] at hx; omega
  have hi : e.1 = f.1 := by apply Fin.ext; dsimp [step] at hstep; omega
  have hrr : e.2.1 = f.2.1 := by apply Fin.ext; simpa only [lowerX] using hr
  have hss : e.2.2 = f.2.2 := by apply Fin.ext; dsimp [lowerY] at hs; omega
  exact Prod.ext hi (Prod.ext hrr hss)

theorem core_card (m : ℕ) : Fintype.card (Core m) = m ^ 4 := by
  simp [Core, Fintype.card_prod]
  ring

def indexedEdge (e : Core m) :
    Erdos956Centers.GridIndex (2 * m) × Erdos956Centers.GridIndex (2 * m) :=
  (.inl (lowerRect e), .inr (upperRect e))

theorem indexedEdge_injective (m : ℕ) : Function.Injective (@indexedEdge m) := by
  intro e f hef
  have hl : lowerRect e = lowerRect f := by
    have h := congrArg (fun p : Erdos956Centers.GridIndex (2 * m) ×
        Erdos956Centers.GridIndex (2 * m) => p.1) hef
    simpa only [indexedEdge, Sum.inl.injEq] using h
  have hu : upperRect e = upperRect f := by
    have h := congrArg (fun p : Erdos956Centers.GridIndex (2 * m) ×
        Erdos956Centers.GridIndex (2 * m) => p.2) hef
    simpa only [indexedEdge, Sum.inr.injEq] using h
  apply edgeIndices_injective m
  unfold edgeIndices
  exact Prod.ext
    (Prod.ext (congrArg (fun p => p.1.val) hl)
      (congrArg (fun p => p.2.val) hl))
    (Prod.ext (congrArg (fun p => p.1.val) hu)
      (congrArg (fun p => p.2.val) hu))

def planeEdge (m : ℕ) (a b η : ℝ) (e : Core m) :
    Erdos956Centers.Plane × Erdos956Centers.Plane :=
  (Erdos956Centers.center (2 * m) a b η (indexedEdge e).1,
    Erdos956Centers.center (2 * m) a b η (indexedEdge e).2)

theorem planeEdge_injective (m : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgap : (((2 * m) * (2 * m) : ℕ) : ℝ) * b < 1 + η) :
    Function.Injective (planeEdge m a b η) := by
  intro e f hef
  apply indexedEdge_injective m
  apply Prod.ext
  · exact Erdos956Centers.center_injective (2 * m) a b η ha hb hgap
      (congrArg (fun p : Erdos956Centers.Plane × Erdos956Centers.Plane => p.1) hef)
  · exact Erdos956Centers.center_injective (2 * m) a b η ha hb hgap
      (congrArg (fun p : Erdos956Centers.Plane × Erdos956Centers.Plane => p.2) hef)

theorem planeEdge_image_card (m : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgap : (((2 * m) * (2 * m) : ℕ) : ℝ) * b < 1 + η) :
    (Finset.univ.image (planeEdge m a b η)).card = m ^ 4 := by
  classical
  rw [Finset.card_image_iff.mpr
    (fun _ _ _ _ h => planeEdge_injective m a b η ha hb hgap h)]
  simpa using core_card m

noncomputable def lowerPool (k : ℕ) (a b η : ℝ) :
    Finset Erdos956Centers.Plane :=
  Finset.univ.image (fun p : Erdos956Centers.Rect k =>
    Erdos956Centers.center k a b η (.inl p))

noncomputable def upperPool (k : ℕ) (a b η : ℝ) :
    Finset Erdos956Centers.Plane :=
  Finset.univ.image (fun p : Erdos956Centers.Rect k =>
    Erdos956Centers.center k a b η (.inr p))

theorem pools_disjoint (k : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgap : ((k * k : ℕ) : ℝ) * b < 1 + η) :
    Disjoint (lowerPool k a b η) (upperPool k a b η) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxL hxU
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hxL
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hxU
  have hcenter : Erdos956Centers.center k a b η (.inl p) =
      Erdos956Centers.center k a b η (.inr q) := hp.trans hq.symm
  have htags : (Sum.inl p : Erdos956Centers.GridIndex k) = .inr q :=
    Erdos956Centers.center_injective k a b η ha hb hgap hcenter
  cases htags

theorem lowerPool_subset_fullCenters (k : ℕ) (a b η : ℝ) :
    lowerPool k a b η ⊆ Erdos956Centers.fullCenters k a b η := by
  classical
  intro x hx
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr
    ⟨(Sum.inl p : Erdos956Centers.GridIndex k), Finset.mem_univ _, hp⟩

theorem upperPool_subset_fullCenters (k : ℕ) (a b η : ℝ) :
    upperPool k a b η ⊆ Erdos956Centers.fullCenters k a b η := by
  classical
  intro x hx
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr
    ⟨(Sum.inr p : Erdos956Centers.GridIndex k), Finset.mem_univ _, hp⟩

theorem planeEdge_mem_product (m : ℕ) (a b η : ℝ) (e : Core m) :
    planeEdge m a b η e ∈
      lowerPool (2 * m) a b η ×ˢ upperPool (2 * m) a b η := by
  classical
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_image.mpr ⟨lowerRect e, Finset.mem_univ _, rfl⟩,
    Finset.mem_image.mpr ⟨upperRect e, Finset.mem_univ _, rfl⟩⟩

noncomputable def coreIncidence (m : ℕ) (a b η : ℝ) :
    Finset (Erdos956Centers.Plane × Erdos956Centers.Plane) :=
  Finset.univ.image (planeEdge m a b η)

theorem coreIncidence_subset (m : ℕ) (a b η : ℝ) :
    coreIncidence m a b η ⊆
      lowerPool (2 * m) a b η ×ˢ upperPool (2 * m) a b η := by
  classical
  intro x hx
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
  exact planeEdge_mem_product m a b η e

theorem coreIncidence_card (m : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgap : (((2 * m) * (2 * m) : ℕ) : ℝ) * b < 1 + η) :
    (coreIncidence m a b η).card = m ^ 4 :=
  planeEdge_image_card m a b η ha hb hgap

noncomputable def unorderedCore (m : ℕ) (a b η : ℝ) :
    Finset (Finset Erdos956Centers.Plane) := by
  classical
  exact (coreIncidence m a b η).image
    (fun p : Erdos956Centers.Plane × Erdos956Centers.Plane =>
      ({p.1, p.2} : Finset Erdos956Centers.Plane))

theorem unorderedCore_card (m : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgap : (((2 * m) * (2 * m) : ℕ) : ℝ) * b < 1 + η) :
    (unorderedCore m a b η).card = m ^ 4 := by
  classical
  have hforget := Erdos956.Counting.ordered_edges_to_unordered
    (lowerPool (2 * m) a b η) (upperPool (2 * m) a b η)
    (pools_disjoint (2 * m) a b η ha hb hgap)
    (coreIncidence m a b η) (coreIncidence_subset m a b η)
  simpa [unorderedCore] using
    hforget.trans (coreIncidence_card m a b η ha hb hgap)

theorem unorderedCore_edges_good (m : ℕ) (a b η : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hgap : (((2 * m) * (2 * m) : ℕ) : ℝ) * b < 1 + η)
    (P : Erdos956Centers.Plane → Erdos956Centers.Plane → Prop)
    (hP : ∀ e : Core m, P (planeEdge m a b η e).1
      (planeEdge m a b η e).2)
    {s : Finset Erdos956Centers.Plane} (hs : s ∈ unorderedCore m a b η) :
    ∃ x y : Erdos956Centers.Plane,
      x ∈ Erdos956Centers.fullCenters (2 * m) a b η ∧
      y ∈ Erdos956Centers.fullCenters (2 * m) a b η ∧
      x ≠ y ∧ s = {x, y} ∧ P x y := by
  classical
  unfold unorderedCore at hs
  obtain ⟨p, hp, hps⟩ := Finset.mem_image.mp hs
  unfold coreIncidence at hp
  obtain ⟨e, _, hep⟩ := Finset.mem_image.mp hp
  let x := (planeEdge m a b η e).1
  let y := (planeEdge m a b η e).2
  have hxy : planeEdge m a b η e ∈
      lowerPool (2 * m) a b η ×ˢ upperPool (2 * m) a b η :=
    planeEdge_mem_product m a b η e
  have hx : x ∈ lowerPool (2 * m) a b η := (Finset.mem_product.mp hxy).1
  have hy : y ∈ upperPool (2 * m) a b η := (Finset.mem_product.mp hxy).2
  have hfullx : x ∈ Erdos956Centers.fullCenters (2 * m) a b η :=
    lowerPool_subset_fullCenters (2 * m) a b η hx
  have hfully : y ∈ Erdos956Centers.fullCenters (2 * m) a b η :=
    upperPool_subset_fullCenters (2 * m) a b η hy
  have hne : x ≠ y := by
    intro heq
    exact (Finset.disjoint_left.mp
      (pools_disjoint (2 * m) a b η ha hb hgap)) hx (heq ▸ hy)
  refine ⟨x, y, hfullx, hfully, hne, ?_, hP e⟩
  change ({p.1, p.2} : Finset Erdos956Centers.Plane) = s at hps
  rw [← hep] at hps
  exact hps.symm

theorem edge_difference (m : ℕ) (e : Core m) (a b η : ℝ) :
    b = a ^ 2 / 2 →
    (((upperX e : ℕ) : ℝ) * a - ((lowerX e : ℕ) : ℝ) * a,
      (1 + η + ((upperY m e : ℕ) : ℝ) * b) -
        (((lowerY m e : ℕ) : ℝ) * b)) =
      (((step e : ℕ) : ℝ) * a,
        1 + η - ((((step e : ℕ) : ℝ) * a) ^ 2) / 2) := by
  intro hb
  have hsub := Nat.sub_add_cancel (lowerY_ge_step_sq e)
  have hx : upperX e = lowerX e + step e := rfl
  have hy : upperY m e + (step e) ^ 2 = lowerY m e := by
    simpa [upperY] using hsub
  have hxr : ((upperX e : ℕ) : ℝ) =
      ((lowerX e : ℕ) : ℝ) + ((step e : ℕ) : ℝ) := by
    exact_mod_cast hx
  have hyr : ((upperY m e : ℕ) : ℝ) +
      (((step e : ℕ) : ℝ) ^ 2) = ((lowerY m e : ℕ) : ℝ) := by
    exact_mod_cast hy
  apply Prod.ext
  · rw [hxr]; ring
  · rw [hb, ← hyr]; ring

theorem planeEdge_difference (m : ℕ) (e : Core m) (a b η : ℝ)
    (hb : b = a ^ 2 / 2) :
    ((planeEdge m a b η e).2 0 - (planeEdge m a b η e).1 0,
      (planeEdge m a b η e).2 1 - (planeEdge m a b η e).1 1) =
      (((step e : ℕ) : ℝ) * a,
        1 + η - ((((step e : ℕ) : ℝ) * a) ^ 2) / 2) := by
  simpa [planeEdge, indexedEdge, Erdos956Centers.center, lowerRect, upperRect] using
    edge_difference m e a b η hb

theorem scale_lt_gridSize (m : ℕ) : m < gridSize (2 * m) := by
  calc
    m < 2 * (2 * m + 1) := by omega
    _ = 2 * (2 * m + 1) * 1 := by ring
    _ ≤ gridSize (2 * m) := by
      unfold gridSize
      gcongr
      omega

theorem next_gridSize_le (m : ℕ) (hm : 1 ≤ m) :
    gridSize (2 * (m + 1)) ≤ 170 * m ^ 3 := by
  have hx : 2 * (m + 1) + 1 ≤ 5 * m := by omega
  have h4 : 2 * (m + 1) ≤ 4 * m := by omega
  have hsq : (2 * (m + 1)) * (2 * (m + 1)) ≤ (4 * m) * (4 * m) := by gcongr
  have hm2 : 1 ≤ m * m := by nlinarith
  have hy : (2 * (m + 1)) * (2 * (m + 1)) + 1 ≤ 17 * (m * m) := by nlinarith [hsq]
  calc
    gridSize (2 * (m + 1)) =
        2 * (2 * (m + 1) + 1) * ((2 * (m + 1)) * (2 * (m + 1)) + 1) := rfl
    _ ≤ 2 * (5 * m) * (17 * (m * m)) := by gcongr
    _ = 170 * m ^ 3 := by ring

def chosenScale (N : ℕ) : ℕ :=
  Nat.findGreatest (fun m => gridSize (2 * m) ≤ N) N

theorem chosenScale_bounds (N : ℕ) (hN : 30 ≤ N) :
    1 ≤ chosenScale N ∧ gridSize (2 * chosenScale N) ≤ N ∧
      N < gridSize (2 * (chosenScale N + 1)) := by
  let m := chosenScale N
  have h1 : 1 ≤ m := by
    dsimp [m, chosenScale]
    apply Nat.le_findGreatest (by omega)
    norm_num [gridSize] at hN ⊢
    omega
  have hm : gridSize (2 * m) ≤ N := by
    change gridSize
      (2 * Nat.findGreatest (fun t => gridSize (2 * t) ≤ N) N) ≤ N
    apply Nat.findGreatest_spec (P := fun t => gridSize (2 * t) ≤ N)
      (m := 1) (by omega)
    norm_num [gridSize]
    omega
  have hlt : m < N := lt_of_lt_of_le (scale_lt_gridSize m) hm
  have hnext : N < gridSize (2 * (m + 1)) := by
    have hnot : ¬ gridSize (2 * (m + 1)) ≤ N := by
      change ¬ gridSize (2 * (chosenScale N + 1)) ≤ N
      apply Nat.findGreatest_is_greatest
        (P := fun t => gridSize (2 * t) ≤ N)
      · change chosenScale N < chosenScale N + 1
        omega
      · omega
    omega
  exact ⟨h1, hm, hnext⟩

theorem allN_core_power_certificate (N : ℕ) (hN : 30 ≤ N) :
    ∃ m : ℕ, 1 ≤ m ∧ gridSize (2 * m) ≤ N ∧
      N ^ 4 < 170 ^ 4 * (m ^ 4) ^ 3 := by
  let m := chosenScale N
  obtain ⟨hm, hgrid, hnext⟩ := chosenScale_bounds N hN
  have hcoarse : N < 170 * m ^ 3 :=
    lt_of_lt_of_le hnext (next_gridSize_le m hm)
  have hpow : N ^ 4 < (170 * m ^ 3) ^ 4 := by gcongr
  refine ⟨m, hm, hgrid, ?_⟩
  convert hpow using 1; ring

theorem allN_strict_quarter_certificate (N : ℕ)
    (hN : gridSize (2 * (170 ^ 5 + 1)) ≤ N) :
    ∃ m : ℕ, 1 ≤ m ∧ gridSize (2 * m) ≤ N ∧
      N ^ 5 < (m ^ 4) ^ 4 := by
  have hN30 : 30 ≤ N := by
    norm_num [gridSize] at hN ⊢
    omega
  let m := chosenScale N
  obtain ⟨hm, hgrid, hnext⟩ := chosenScale_bounds N hN30
  have hstart : 170 ^ 5 + 1 ≤ N := by
    have hlt := scale_lt_gridSize (170 ^ 5 + 1)
    omega
  have hmlarge : 170 ^ 5 + 1 ≤ m := by
    dsimp [m, chosenScale]
    exact Nat.le_findGreatest (P := fun t => gridSize (2 * t) ≤ N)
      hstart hN
  have hcoarse : N < 170 * m ^ 3 :=
    lt_of_lt_of_le hnext (next_gridSize_le m hm)
  have hpow : N ^ 5 < (170 * m ^ 3) ^ 5 := by gcongr
  have hmul : 170 ^ 5 * m ^ 15 < m * m ^ 15 := by
    have hlarge : 170 ^ 5 < m := by omega
    gcongr
  refine ⟨m, hm, hgrid, ?_⟩
  calc
    N ^ 5 < (170 * m ^ 3) ^ 5 := hpow
    _ = 170 ^ 5 * m ^ 15 := by ring
    _ < m * m ^ 15 := hmul
    _ = (m ^ 4) ^ 4 := by ring

end Erdos956Counting

namespace Erdos956.Specification

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def translateSetDistance (C : Set Plane) (x y : Plane) : ℝ :=
  ⨅ c : C, ⨅ d : C, dist (c.1 + x) (d.1 + y)

structure Configuration (N : ℕ) where
  C : Set Plane
  compact : IsCompact C
  convex : Convex ℝ C
  nonempty : C.Nonempty
  interior_nonempty : (interior C).Nonempty
  X : Finset Plane
  cardinality : X.card = N
  disjoint : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
    Disjoint ((· + x) '' C) ((· + y) '' C)
  edges : Finset (Finset Plane)
  edges_good : ∀ e ∈ edges, ∃ x y : Plane,
    x ≠ y ∧ e = {x, y} ∧ x ∈ X ∧ y ∈ X ∧
      translateSetDistance C x y = 1

def FullAnswer : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N →
      ∃ config : Configuration N,
        c * (N : ℝ) ^ ((4 : ℝ) / 3) ≤ (config.edges.card : ℝ)

def CubicGrowth {N : ℕ} (config : Configuration N) : Prop :=
  N ^ 4 ≤ 1000000000 * config.edges.card ^ 3

theorem cubic_growth_implies_rpow {N E : ℕ}
    (h : N ^ 4 ≤ 1000000000 * E ^ 3) :
    (1 / 1000 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) ≤ (E : ℝ) := by
  have hR : (N : ℝ) ^ 4 ≤ 1000000000 * (E : ℝ) ^ 3 := by
    exact_mod_cast h
  have hCube : (N : ℝ) ^ 4 ≤ (1000 * (E : ℝ)) ^ 3 := by
    convert hR using 1; ring
  have hpow : ((N : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 = (N : ℝ) ^ 4 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N) ((4 : ℝ) / 3) 3]
    norm_num [Real.rpow_natCast]
  have hroot : (N : ℝ) ^ ((4 : ℝ) / 3) ≤ 1000 * (E : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
    simpa [hpow] using hCube
  nlinarith [hroot]

theorem fullAnswer_of_cubic_growth
    (h : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ config : Configuration N, CubicGrowth config) : FullAnswer := by
  rcases h with ⟨N₀, hN⟩
  refine ⟨1 / 1000, by norm_num, N₀, ?_⟩
  intro N hlarge
  obtain ⟨config, hconfig⟩ := hN N hlarge
  exact ⟨config, cubic_growth_implies_rpow hconfig⟩

end Erdos956.Specification

namespace Erdos956

abbrev Plane := Geometry.Plane

private def scale (m : ℕ) : ℕ := 2 * m

private theorem scale_pos (m : ℕ) (hm : 1 ≤ m) : 1 ≤ scale m := by
  unfold scale
  omega

noncomputable def body (m : ℕ) : Set Plane :=
  Geometry.D (Parameters.eta (scale m)) (Parameters.T (scale m))

noncomputable def initialCenters (m : ℕ) : Finset Plane :=
  Erdos956Centers.fullCenters (scale m)
    (Parameters.a (scale m)) (Parameters.b (scale m))
    (Parameters.eta (scale m))

noncomputable def orderedEdges (m : ℕ) : Finset (Plane × Plane) :=
  Erdos956Counting.coreIncidence m
    (Parameters.a (scale m)) (Parameters.b (scale m))
    (Parameters.eta (scale m))

noncomputable def unorderedEdges (m : ℕ) : Finset (Finset Plane) :=
  Erdos956Counting.unorderedCore m
    (Parameters.a (scale m)) (Parameters.b (scale m))
    (Parameters.eta (scale m))

private theorem parameter_range (m : ℕ) (hm : 1 ≤ m) :
    ∀ t ∈ Parameters.T (scale m),
      0 ≤ t ∧ t ≤ Parameters.W (scale m) := by
  intro t ht
  exact Parameters.mem_T_range (scale m) (scale_pos m hm) ht

private theorem body_box (m : ℕ) (hm : 1 ≤ m) :
    ∀ z ∈ body m,
      |z 0| ≤ (Parameters.W (scale m)) ^ 3 / 2 ∧
      |z 1| ≤ Parameters.eta (scale m) := by
  let W := Parameters.W (scale m)
  let T := Parameters.T (scale m)
  have hW0 : 0 ≤ W := (Parameters.W_pos (scale m) (scale_pos m hm)).le
  have hW1 : W ≤ 1 := Parameters.W_le_one (scale m) (scale_pos m hm)
  have hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ W := parameter_range m hm
  change ∀ z ∈ Geometry.D (W ^ 4) T,
    |z 0| ≤ W ^ 3 / 2 ∧ |z 1| ≤ W ^ 4
  exact Geometry.D_abs_box W T hW0 hW1 hT

private theorem body_symmetric (m : ℕ) :
    ∀ z ∈ body m, -z ∈ body m := by
  intro z hz
  change -z ∈ Geometry.D (Parameters.eta (scale m)) (Parameters.T (scale m))
  rw [← Geometry.D_neg_eq (Parameters.eta (scale m)) (Parameters.T (scale m))]
  exact Set.neg_mem_neg.mpr hz

private theorem layer_gap (m : ℕ) (hm : 1 ≤ m) :
    (((scale m) * (scale m) : ℕ) : ℝ) * Parameters.b (scale m) <
      1 + Parameters.eta (scale m) := by
  have hk := scale_pos m hm
  have hη := Parameters.eta_pos (scale m) hk
  have hvertical := Parameters.grid_height_lt_one (scale m) hk
  have hcast : (((scale m) * (scale m) : ℕ) : ℝ) =
      (scale m : ℝ) ^ 2 := by norm_cast; ring
  rw [hcast]
  linarith

private theorem initial_card (m : ℕ) (hm : 1 ≤ m) :
    (initialCenters m).card = Erdos956Counting.gridSize (scale m) := by
  have hk := scale_pos m hm
  have ha := Parameters.a_pos (scale m) hk
  have hb := Parameters.b_pos (scale m) hk
  simpa only [initialCenters, Erdos956Counting.gridSize] using
    Erdos956Centers.full_centers_card (scale m)
      (Parameters.a (scale m)) (Parameters.b (scale m))
      (Parameters.eta (scale m)) ha hb (layer_gap m hm)

private theorem initial_horizontal_bounds (m : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ initialCenters m, 0 ≤ x 0 ∧ x 0 ≤ 1 := by
  have hk := scale_pos m hm
  have ha := Parameters.a_pos (scale m) hk
  have hW := Parameters.W_le_one (scale m) hk
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
  have hbounds := Erdos956Centers.center_x_bounds i
    (Parameters.a (scale m)) (Parameters.b (scale m))
    (Parameters.eta (scale m)) ha.le
  have hka : (scale m : ℝ) * Parameters.a (scale m) =
      Parameters.W (scale m) := by
    rw [Parameters.a]
    have hknz : (scale m : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : scale m ≠ 0)
    field_simp [hknz]
  rw [hka] at hbounds
  exact ⟨hbounds.1, hbounds.2.trans hW⟩

private theorem initial_differences_excluded (m : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ initialCenters m, ∀ y ∈ initialCenters m,
      x ≠ y → y - x ∉ body m := by
  have hk := scale_pos m hm
  have ha := Parameters.a_pos (scale m) hk
  have hb := Parameters.b_pos (scale m) hk
  have hη := Parameters.eta_pos (scale m) hk
  have hwidth := Parameters.cap_width_lt_a (scale m) hk
  have hheight := Parameters.eta_lt_b (scale m) hk
  have hlayer := Parameters.grid_height_lt_one (scale m) hk
  have hcast : (((scale m) * (scale m) : ℕ) : ℝ) =
      (scale m : ℝ) ^ 2 := by norm_cast; ring
  rw [← hcast] at hlayer
  intro x hx y hy hxy
  exact Erdos956Centers.full_centers_pair_diff_not_mem_of_box
    (body m) (body_box m hm) hx hy hxy ha hb hη.le hwidth hheight hlayer

private theorem body_compact (m : ℕ) : IsCompact (body m) :=
  Geometry.D_compact _ _

private theorem body_convex (m : ℕ) : Convex ℝ (body m) :=
  Geometry.D_convex _ _

private theorem body_nonempty (m : ℕ) : (body m).Nonempty := by
  have hzero : (0 : ℝ) ∈ Parameters.T (scale m) := by
    have h := Parameters.step_mem_T (scale m) 0 (Nat.zero_le _)
    simpa using h
  exact Geometry.D_nonempty _ _ ⟨0, hzero⟩

private theorem scale_edge_distance_one (m : ℕ) (hm : 1 ≤ m)
    (e : Erdos956Counting.Core m) :
    Erdos956.Specification.translateSetDistance
      ((1 / 2 : ℝ) • body m)
      (Erdos956Counting.planeEdge m
        (Parameters.a (scale m)) (Parameters.b (scale m))
        (Parameters.eta (scale m)) e).1
      (Erdos956Counting.planeEdge m
        (Parameters.a (scale m)) (Parameters.b (scale m))
        (Parameters.eta (scale m)) e).2 = 1 := by
  let k := scale m
  let W := Parameters.W k
  let a := Parameters.a k
  let b := Parameters.b k
  let η := Parameters.eta k
  let T := Parameters.T k
  let t : ℝ := (Erdos956Counting.step e : ℝ) * a
  let edge := Erdos956Counting.planeEdge m a b η e
  have hk : 1 ≤ k := scale_pos m hm
  have hstep : Erdos956Counting.step e ≤ k := by
    have hs := Erdos956Counting.step_le e
    dsimp [k, scale]
    omega
  have ht : t ∈ T := Parameters.step_mem_T k _ hstep
  have hW0 : 0 ≤ W := (Parameters.W_pos k hk).le
  have hW1 : W ≤ 1 := Parameters.W_le_one k hk
  have hT : ∀ s ∈ T, 0 ≤ s ∧ s ≤ W := parameter_range m hm
  have hb : b = a ^ 2 / 2 := rfl
  have hcoords := Erdos956Counting.planeEdge_difference m e a b η hb
  have hdiff : edge.2 - edge.1 = Geometry.gamma η t := by
    ext i
    fin_cases i
    · have hx := congrArg Prod.fst hcoords
      simpa [PiLp.sub_apply, Geometry.gamma_zero, t, edge] using hx
    · have hy := congrArg Prod.snd hcoords
      simpa [PiLp.sub_apply, Geometry.gamma_one, t, edge] using hy
  have hp : Geometry.p η t ∈ body m := Geometry.p_mem_D η T t ht
  have hDist : Metric.infDist (Geometry.gamma η t) (body m) = 1 := by
    change Metric.infDist (Geometry.gamma (W ^ 4) t)
      (Geometry.D (W ^ 4) T) = 1
    exact Geometry.D_unit_distance W T hW0 hW1 hT t ht
  have hclose : dist (Geometry.gamma η t) (Geometry.p η t) = 1 := by
    rw [dist_eq_norm, Geometry.gamma_sub_p, Geometry.normal_norm_one]
  change translateSetDistance ((1 / 2 : ℝ) • body m) edge.1 edge.2 = 1
  exact translateSetDistance_one_of_body (body m) (body_convex m)
    (body_symmetric m) hp hdiff hDist hclose

private theorem unordered_edges_card (m : ℕ) (hm : 1 ≤ m) :
    (unorderedEdges m).card = m ^ 4 := by
  have hk := scale_pos m hm
  have ha := Parameters.a_pos (scale m) hk
  have hb := Parameters.b_pos (scale m) hk
  exact Erdos956Counting.unorderedCore_card m _ _ _ ha hb
    (by simpa only [scale] using layer_gap m hm)

private theorem half_body_interior_nonempty (m : ℕ) (hm : 1 ≤ m) :
    (interior ((1 / 2 : ℝ) • body m)).Nonempty := by
  let k := scale m
  let W := Parameters.W k
  let T := Parameters.T k
  have hk : 1 ≤ k := scale_pos m hm
  have hW : 0 < W := Parameters.W_pos k hk
  have h0 : (0 : ℝ) ∈ T := by
    have h := Parameters.step_mem_T k 0 (Nat.zero_le k)
    simpa [T] using h
  have hWT : W ∈ T := by
    have h := Parameters.step_mem_T k k (le_refl k)
    have hka : (k : ℝ) * Parameters.a k = W := by
      dsimp [W, Parameters.a]
      have hknz : (k : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : k ≠ 0)
      field_simp [hknz]
    rw [hka] at h
    exact h
  change (interior ((1 / 2 : ℝ) • Geometry.D (W ^ 4) T)).Nonempty
  exact Geometry.half_D_interior_nonempty W T hW h0 hWT

noncomputable def configuration (m N : ℕ) (hm : 1 ≤ m)
    (hgrid : Erdos956Counting.gridSize (scale m) ≤ N) :
    Specification.Configuration N := by
  classical
  let C : Set Plane := (1 / 2 : ℝ) • body m
  let X : Finset Plane := Padding.paddedCenters (initialCenters m)
    (N - (initialCenters m).card)
  let E : Finset (Finset Plane) := unorderedEdges m
  have hbounds := initial_horizontal_bounds m hm
  have hXlow : ∀ x ∈ initialCenters m, 0 ≤ x 0 :=
    fun x hx => (hbounds x hx).1
  have hXhigh : ∀ x ∈ initialCenters m, x 0 ≤ 1 :=
    fun x hx => (hbounds x hx).2
  have hXle : (initialCenters m).card ≤ N := by
    rw [initial_card m hm]
    exact hgrid
  have hXcard : X.card = N :=
    Padding.paddedCenters_card_exact (initialCenters m) hXhigh hXle
  have hDhalf : ∀ z ∈ body m, |z 0| ≤ 1 / 2 := by
    intro z hz
    have hbox := (body_box m hm) z hz
    let W := Parameters.W (scale m)
    have hW0 : 0 ≤ W := (Parameters.W_pos (scale m) (scale_pos m hm)).le
    have hW1 : W ≤ 1 := Parameters.W_le_one (scale m) (scale_pos m hm)
    have hW3 : W ^ 3 ≤ 1 := by
      nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hW1),
        mul_nonneg (sq_nonneg W) (sub_nonneg.mpr hW1)]
    dsimp [W] at hW3
    linarith [hbox.1]
  have hdiff : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → y - x ∉ body m := by
    exact Padding.padded_differences_excluded (body m) (initialCenters m)
      (N - (initialCenters m).card) hDhalf hXlow hXhigh
      (initial_differences_excluded m hm)
  have hCnonempty : C.Nonempty := by
    obtain ⟨z, hz⟩ := body_nonempty m
    exact ⟨(1 / 2 : ℝ) • z, Set.smul_mem_smul_set hz⟩
  have hk := scale_pos m hm
  have ha := Parameters.a_pos (scale m) hk
  have hb := Parameters.b_pos (scale m) hk
  have hgap :
      (((2 * m) * (2 * m) : ℕ) : ℝ) * Parameters.b (scale m) <
        1 + Parameters.eta (scale m) := by
    simpa only [scale] using layer_gap m hm
  have hP : ∀ e : Erdos956Counting.Core m,
      Specification.translateSetDistance C
        (Erdos956Counting.planeEdge m
          (Parameters.a (scale m)) (Parameters.b (scale m))
          (Parameters.eta (scale m)) e).1
        (Erdos956Counting.planeEdge m
          (Parameters.a (scale m)) (Parameters.b (scale m))
          (Parameters.eta (scale m)) e).2 = 1 := by
    intro e
    simpa only [C, Specification.translateSetDistance,
      Erdos956.translateSetDistance] using scale_edge_distance_one m hm e
  refine {
    C := C
    compact := half_body_isCompact (body m) (body_compact m)
    convex := half_body_convex (body m) (body_convex m)
    nonempty := hCnonempty
    interior_nonempty := half_body_interior_nonempty m hm
    X := X
    cardinality := hXcard
    disjoint := ?_
    edges := E
    edges_good := ?_
  }
  · intro x hx y hy hne
    exact half_body_translates_disjoint_of_diff_not_mem (body m)
      (body_convex m) (body_symmetric m) (hdiff x hx y hy hne)
  · intro s hs
    obtain ⟨x, y, hx, hy, hne, hseq, hunit⟩ :=
      Erdos956Counting.unorderedCore_edges_good m
        (Parameters.a (scale m)) (Parameters.b (scale m))
        (Parameters.eta (scale m)) ha hb hgap
        (fun x y => Specification.translateSetDistance C x y = 1)
        hP hs
    refine ⟨x, y, hne, hseq, ?_, ?_, hunit⟩
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_left _ hy

theorem configuration_edges_card (m N : ℕ) (hm : 1 ≤ m)
    (hgrid : Erdos956Counting.gridSize (scale m) ≤ N) :
    (configuration m N hm hgrid).edges.card = m ^ 4 :=
  unordered_edges_card m hm

theorem cubic_growth_for_all_N :
    ∀ N : ℕ, 30 ≤ N →
      ∃ config : Specification.Configuration N,
        Specification.CubicGrowth config := by
  intro N hN
  obtain ⟨m, hm, hgrid, hpower⟩ :=
    Erdos956Counting.allN_core_power_certificate N hN
  have hgrid' : Erdos956Counting.gridSize (scale m) ≤ N := by
    simpa only [scale] using hgrid
  let config := configuration m N hm hgrid'
  refine ⟨config, ?_⟩
  change N ^ 4 ≤ 1000000000 * config.edges.card ^ 3
  rw [configuration_edges_card m N hm hgrid']
  calc
    N ^ 4 ≤ 170 ^ 4 * (m ^ 4) ^ 3 := hpower.le
    _ ≤ 1000000000 * (m ^ 4) ^ 3 :=
      Nat.mul_le_mul_right _ (by norm_num : 170 ^ 4 ≤ 1000000000)

theorem erdos956_full_answer : Specification.FullAnswer :=
  Specification.fullAnswer_of_cubic_growth
    ⟨30, cubic_growth_for_all_N⟩

theorem erdos956_strict_superlinear_answer :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ config : Specification.Configuration N,
        (N : ℝ) ^ ((5 : ℝ) / 4) < (config.edges.card : ℝ) := by
  refine ⟨Erdos956Counting.gridSize (2 * (170 ^ 5 + 1)), ?_⟩
  intro N hN
  obtain ⟨m, hm, hgrid, hpower⟩ :=
    Erdos956Counting.allN_strict_quarter_certificate N hN
  have hgrid' : Erdos956Counting.gridSize (scale m) ≤ N := by
    simpa only [scale] using hgrid
  let config := configuration m N hm hgrid'
  refine ⟨config, ?_⟩
  have hE : config.edges.card = m ^ 4 :=
    configuration_edges_card m N hm hgrid'
  rw [hE]
  have hR : (N : ℝ) ^ 5 < (((m ^ 4 : ℕ) : ℝ)) ^ 4 := by
    exact_mod_cast hpower
  have hroot : ((N : ℝ) ^ ((5 : ℝ) / 4)) ^ 4 = (N : ℝ) ^ 5 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N) ((5 : ℝ) / 4) 4]
    norm_num [Real.rpow_natCast]
  by_contra hnot
  have hle : (((m ^ 4 : ℕ) : ℝ)) ≤ (N : ℝ) ^ ((5 : ℝ) / 4) :=
    le_of_not_gt hnot
  have hle4 : (((m ^ 4 : ℕ) : ℝ)) ^ 4 ≤
      ((N : ℝ) ^ ((5 : ℝ) / 4)) ^ 4 := by gcongr
  rw [hroot] at hle4
  exact (not_le_of_gt hR) hle4

end Erdos956

/-!
## Section 5: Bridge to the Extremal Function `h(n)` and `FormalConjectures.ErdosProblems.956`
-/

namespace Erdos956.Extremal

open Filter
open scoped Classical

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Minimum Euclidean distance between the sets `C + x` and `C + y`
(matching `FormalConjectures.ErdosProblems.956.translateDistance`). -/
noncomputable def translateDistance (C : Set Plane) (x y : Plane) : ℝ :=
  ⨅ c : C, ⨅ d : C, dist (c.1 + x) (d.1 + y)

/-- A family of pairwise disjoint translates of one nonempty compact convex set
(matching `FormalConjectures.ErdosProblems.956.IsConfiguration`). -/
def IsConfiguration (C : Set Plane) (X : Finset Plane) : Prop :=
  C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
    ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint ((· + x) '' C) ((· + y) '' C)

/-- The unordered pairs of distinct centers whose translates have set-distance one
(matching `FormalConjectures.ErdosProblems.956.unitPairs`). -/
noncomputable def unitPairs (C : Set Plane) (X : Finset Plane) : Finset (Finset Plane) :=
  (X.powersetCard 2).filter fun e =>
    ∃ x y : Plane, x ≠ y ∧ e = {x, y} ∧ translateDistance C x y = 1

/-- The maximum number of unordered unit-distance pairs among `n` disjoint convex translates
(matching `FormalConjectures.ErdosProblems.956.h`). -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
    X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m}

theorem unitPairs_card_le_choose_two (C : Set Plane) (X : Finset Plane) :
    (unitPairs C X).card ≤ X.card.choose 2 := by
  unfold unitPairs
  calc
    ((X.powersetCard 2).filter _).card ≤ (X.powersetCard 2).card :=
      Finset.card_filter_le _ _
    _ = X.card.choose 2 := Finset.card_powersetCard 2 X

theorem attainable_bddAbove (n : ℕ) :
    BddAbove {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
      X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m} := by
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨C, X, hcard, _, rfl⟩
  rw [← hcard]
  exact unitPairs_card_le_choose_two C X

theorem configuration_isConfiguration {n : ℕ} (config : Specification.Configuration n) :
    IsConfiguration config.C config.X :=
  ⟨config.nonempty, config.compact, config.convex, config.disjoint⟩

theorem configuration_edges_subset_unitPairs {n : ℕ} (config : Specification.Configuration n) :
    config.edges ⊆ unitPairs config.C config.X := by
  intro e he
  obtain ⟨x, y, hne, rfl, hx, hy, hdist⟩ := config.edges_good e he
  unfold unitPairs
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  refine ⟨⟨?_, Finset.card_pair hne⟩, ⟨x, y, hne, rfl, hdist⟩⟩
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hx
  · rw [Finset.mem_singleton.mp hz]
    exact hy

theorem configuration_edges_le_h {n : ℕ} (config : Specification.Configuration n) :
    config.edges.card ≤ h n := by
  have hsub : config.edges.card ≤ (unitPairs config.C config.X).card :=
    Finset.card_le_card (configuration_edges_subset_unitPairs config)
  have hmem : (unitPairs config.C config.X).card ∈
      {m : ℕ | ∃ C : Set Plane, ∃ X : Finset Plane,
        X.card = n ∧ IsConfiguration C X ∧ (unitPairs C X).card = m} :=
    ⟨config.C, config.X, config.cardinality, configuration_isConfiguration config, rfl⟩
  exact hsub.trans (le_csSup (attainable_bddAbove n) hmem)

/-- For every `N ≥ 30`, the extremal function `h(N)` is at least `(1/1000) N^(4/3)`. -/
theorem h_lower_bound_all_from_30 (N : ℕ) (hN : 30 ≤ N) :
    (1 / 1000 : ℝ) * (N : ℝ) ^ ((4 : ℝ) / 3) ≤ (h N : ℝ) := by
  obtain ⟨config, hcubic⟩ := Erdos956.cubic_growth_for_all_N N hN
  have hlow := Specification.cubic_growth_implies_rpow hcubic
  have hle : (config.edges.card : ℝ) ≤ (h N : ℝ) := by
    exact_mod_cast configuration_edges_le_h config
  exact hlow.trans hle

/-- Affirmative proof of the exact `FormalConjectures.ErdosProblems.956` superlinear statement:
there exists `c > 0` (namely `c = 1/4`) such that `n^(1 + c) < h(n)` for all sufficiently
large `n`. -/
theorem erdos_956_superlinear :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 + c) < (h n : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := Erdos956.erdos956_strict_superlinear_answer
  refine ⟨1 / 4, by norm_num, Filter.eventually_atTop.mpr ⟨N₀, ?_⟩⟩
  intro n hn
  obtain ⟨config, hgt⟩ := hN₀ n hn
  have hle : (config.edges.card : ℝ) ≤ (h n : ℝ) := by
    exact_mod_cast configuration_edges_le_h config
  have hexp : (1 : ℝ) + 1 / 4 = 5 / 4 := by norm_num
  rw [hexp]
  exact lt_of_lt_of_le hgt hle

end Erdos956.Extremal

/-!
## Section 6: Four-Layer Signed-Grid Construction, Polynomial `J_q`, and `> (2/5) N^(4/3)` Bound
-/

namespace Erdos956.FourLayer

open scoped Pointwise

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := by simp [point]
@[simp] theorem point_one (x y : ℝ) : point x y 1 = y := by simp [point]

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
    exact hhorizontal.trans_le (Erdos956Centers.cast_mul_gap hx.symm a ha)
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
      exact hvertical.trans_le (Erdos956Centers.cast_mul_gap hyne.symm b hb)

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
    Specification.translateSetDistance
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

theorem next_fourLayerSize_le_49_cube (q : ℕ) (hq : 162 ≤ q) :
    fourLayerSize (q + 1) ≤ 49 * q ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 162 := ⟨q - 162, by omega⟩
  have hid : 49 * (t + 162) ^ 3 =
      fourLayerSize (t + 162 + 1) + (t ^ 3 + 326 * t ^ 2 + 26704 * t + 21952) := by
    unfold fourLayerSize
    ring
  omega

def chosenFourLayerScale (N : ℕ) : ℕ :=
  Nat.findGreatest (fun q => fourLayerSize q ≤ N) N

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

/-!
## Section 8: Transitive Axiom Audits
-/

#print axioms Erdos956.Geometry.D_unit_distance_signed
#print axioms Erdos956.Geometry.D_abs_box_signed
#print axioms Erdos956.erdos956_full_answer
#print axioms Erdos956.erdos956_strict_superlinear_answer
#print axioms Erdos956.Extremal.h_lower_bound_all_from_30
#print axioms Erdos956.Extremal.erdos_956_superlinear
#print axioms Erdos956.FourLayer.fourLayer_sum_polynomial
#print axioms Erdos956.FourLayer.fourLayerUnorderedEdges_card
#print axioms Erdos956.FourLayer.fourLayer_exact_configuration
#print axioms Erdos956.FourLayer.fourLayer_q1_configuration
#print axioms Erdos956.FourLayer.h_fourLayer_lower_bound
#print axioms Erdos956.FourLayer.h_80_ge_144
#print axioms Erdos956.FourLayer.fourLayer_two_fifths_all_N
#print axioms Erdos956.FourLayer.h_eventual_two_fifths
#print axioms Erdos956.PolynomialCertificates.oneSided_sum_polynomial
#print axioms Erdos956.PolynomialCertificates.twoLayer_signed_sum_polynomial
#print axioms Erdos956.PolynomialCertificates.P_sharp_pos_of_ge_51
#print axioms Erdos956.PolynomialCertificates.P_sharp_neg_at_50
#print axioms Erdos956.PolynomialCertificates.P_two_fifths_pos_of_ge_64
#print axioms Erdos956.PolynomialCertificates.P_two_fifths_neg_at_63
