module

public import Mathlib


@[expose] public section

/-!
# Signed parabolic cap geometry for Erdős #956

Constructs the centrally symmetric convex polygon `D = conv {±p(t) : t ∈ T}`
from supporting hyperplanes to the parabola `γ(t) = (t, 1 + η - t^2 / 2)` and
proves exact unit point-to-body distance (`D_unit_distance_signed`), coordinate
box containment (`D_abs_box_signed`), compactness, convexity, central symmetry,
and nonempty interior for any finite parameter set `T ⊆ [-W, W]`.
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

theorem sqrt_rad_sq (t : ℝ) :
    (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem sqrt_rad_nonneg (t : ℝ) :
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

theorem radical_gap_identity (s t : ℝ) :
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

theorem radical_sum_identity (s t : ℝ) :
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
