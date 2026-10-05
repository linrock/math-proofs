module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 4000000

namespace GoldbachChain

-- ==== HOISTED shared definitions (single canonical copies) ====
open Finset

/-- `e(x) = exp(2πi x)`, the additive character of the circle. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma e_norm (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

lemma e_pow (α : ℝ) (n : ℕ) : e (n * α) = (e α) ^ n := by
  rw [e, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

lemma e_add (x y : ℝ) : e x * e y = e (x + y) := by
  rw [e, e, e, ← Complex.exp_add]; congr 1; push_cast; ring

lemma e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  rw [e, e, ← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast; ring

lemma geom_exp_bound (z : ℂ) (hz : z ≠ 1) (hz1 : ‖z‖ = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have hzsub : (0 : ℝ) < ‖z - 1‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero_of_ne hz
  rw [geom_sum_eq hz, norm_div]
  gcongr
  calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz1]; norm_num

lemma e_sub_one_norm (α : ℝ) : ‖e α - 1‖ = 2 * |Real.sin (Real.pi * α)| := by
  have harg : e α = Complex.exp ((↑(2 * Real.pi * α) : ℂ) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have hre : (e α).re = Real.cos (2 * Real.pi * α) := by
    rw [harg]; exact Complex.exp_ofReal_mul_I_re _
  have him : (e α).im = Real.sin (2 * Real.pi * α) := by
    rw [harg]; exact Complex.exp_ofReal_mul_I_im _
  have e1 : Real.cos (2 * Real.pi * α) = 2 * Real.cos (Real.pi * α) ^ 2 - 1 := by
    rw [show 2 * Real.pi * α = 2 * (Real.pi * α) by ring]; exact Real.cos_two_mul _
  have e2 : Real.sin (2 * Real.pi * α)
      = 2 * Real.sin (Real.pi * α) * Real.cos (Real.pi * α) := by
    rw [show 2 * Real.pi * α = 2 * (Real.pi * α) by ring]; exact Real.sin_two_mul _
  have hnn : (0 : ℝ) ≤ 2 * |Real.sin (Real.pi * α)| := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (e α - 1)), ← Real.sqrt_sq hnn]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
  rw [e1, e2, mul_pow, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * α)]

lemma exp_sum_le_sin (α : ℝ) (hα : Real.sin (Real.pi * α) ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ 1 / |Real.sin (Real.pi * α)| := by
  have hne : e α ≠ 1 := by
    intro h
    have h0 : ‖e α - 1‖ = 2 * |Real.sin (Real.pi * α)| := e_sub_one_norm α
    rw [h, sub_self, norm_zero] at h0
    have : |Real.sin (Real.pi * α)| = 0 := by linarith [abs_nonneg (Real.sin (Real.pi * α))]
    exact hα (abs_eq_zero.mp this)
  have hsum : ∑ n ∈ Finset.range N, e (n * α) = ∑ n ∈ Finset.range N, (e α) ^ n :=
    Finset.sum_congr rfl (fun n _ => e_pow α n)
  have key : ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ 2 / ‖e α - 1‖ := by
    rw [hsum]; exact geom_exp_bound (e α) hne (e_norm α) N
  rw [e_sub_one_norm α] at key
  have habs : (0 : ℝ) < |Real.sin (Real.pi * α)| := abs_pos.mpr hα
  calc ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ 2 / (2 * |Real.sin (Real.pi * α)|) := key
    _ = 1 / |Real.sin (Real.pi * α)| := by rw [div_mul_eq_div_div]; norm_num

lemma two_dist_le_abs_sin (α : ℝ) : 2 * |α - round α| ≤ |Real.sin (Real.pi * α)| := by
  set m : ℤ := round α with hm
  set r : ℝ := α - (m : ℝ) with hr
  have hrabs : |r| ≤ 1 / 2 := by rw [hr]; exact abs_sub_round α
  have hαsplit : Real.pi * α = Real.pi * r + (m : ℝ) * Real.pi := by
    rw [hr]; ring
  have hsin : Real.sin (Real.pi * α) = (-1) ^ m * Real.sin (Real.pi * r) := by
    rw [hαsplit, Real.sin_add_int_mul_pi]
  have habs1 : |Real.sin (Real.pi * α)| = |Real.sin (Real.pi * r)| := by
    rw [hsin, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hpr : |Real.sin (Real.pi * r)| = Real.sin (Real.pi * |r|) := by
    by_cases hrpos : 0 ≤ r
    · rw [abs_of_nonneg hrpos,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
          (by nlinarith [Real.pi_pos, (abs_le.mp hrabs).2]))]
    · replace hrpos : r < 0 := not_le.mp hrpos
      have hle0 : Real.sin (Real.pi * r) ≤ 0 := by
        have h1 : 0 ≤ Real.sin (Real.pi * (-r)) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
            (by nlinarith [Real.pi_pos, (abs_le.mp hrabs).1])
        rw [show Real.pi * (-r) = -(Real.pi * r) by ring, Real.sin_neg] at h1
        linarith
      rw [abs_of_neg hrpos, abs_of_nonpos hle0,
        show Real.pi * -r = -(Real.pi * r) by ring, Real.sin_neg]
  have hjordan : 2 * |r| ≤ Real.sin (Real.pi * |r|) := by
    have hj := Real.le_sin_mul (x := 2 * |r|) (by positivity) (by nlinarith [hrabs])
    rwa [show Real.pi / 2 * (2 * |r|) = Real.pi * |r| by ring] at hj
  calc 2 * |α - round α| = 2 * |r| := by rw [hr]
    _ ≤ Real.sin (Real.pi * |r|) := hjordan
    _ = |Real.sin (Real.pi * r)| := hpr.symm
    _ = |Real.sin (Real.pi * α)| := habs1.symm

lemma exp_sum_bound (α : ℝ) (hα : Real.sin (Real.pi * α) ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ 1 / (2 * |α - round α|) := by
  have h2 := two_dist_le_abs_sin α
  have hd : (0 : ℝ) < 2 * |α - round α| := by
    rcases (abs_nonneg (α - (round α : ℝ))).lt_or_eq with h | h
    · positivity
    · exfalso; apply hα
      have hz : α - (round α : ℝ) = 0 := abs_eq_zero.mp h.symm
      have hαeq : α = (round α : ℝ) := by linarith
      rw [hαeq, show Real.pi * (round α : ℝ) = (round α : ℝ) * Real.pi by ring,
        Real.sin_int_mul_pi]
  exact le_trans (exp_sum_le_sin α hα N) (one_div_le_one_div_of_le hd h2)

lemma exp_sum_trivial (α : ℝ) (N : ℕ) : ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ N := by
  calc ‖∑ n ∈ Finset.range N, e (n * α)‖
      ≤ ∑ n ∈ Finset.range N, ‖e (n * α)‖ := norm_sum_le _ _
    _ = N := by simp [e_norm]

/-- The capped exponential-sum bound in workhorse-weight form:
    `‖∑_{n<M} e(nβ)‖ ≤ [if β∈ℤ then M else min(M, 1/(2‖β‖))]`. -/
lemma exp_sum_min_bound (β : ℝ) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, e (n * β)‖
      ≤ (if β - round β = 0 then (M : ℝ)
         else min (M : ℝ) (1 / (2 * |β - round β|))) := by
  split
  · exact exp_sum_trivial β M
  · rename_i hne
    apply le_min (exp_sum_trivial β M)
    have hsin : Real.sin (Real.pi * β) ≠ 0 := by
      intro h0
      apply hne
      rw [Real.sin_eq_zero_iff] at h0
      obtain ⟨n, hn⟩ := h0
      have h2 : Real.pi * (n : ℝ) = Real.pi * β := by linear_combination hn
      have hβ : β = (n : ℝ) := (mul_left_cancel₀ Real.pi_ne_zero h2).symm
      rw [hβ, round_intCast]
      ring
    exact exp_sum_bound β hsin M

/-- `e(α) = 1` iff `α` is an integer. -/
lemma e_eq_one_iff (α : ℝ) : e α = 1 ↔ ∃ k : ℤ, α = (k : ℝ) := by
  rw [e, Complex.exp_eq_one_iff]
  have h2πI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [mul_comm ((k : ℤ) : ℂ) (2 * (Real.pi : ℂ) * Complex.I)] at hk
    exact_mod_cast mul_left_cancel₀ h2πI hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

open Filter in
/-- The arithmetic model coefficients for `Λ` mod `q`: `1/φ(q)` on units, `0` off. -/
noncomputable def lambdaModel (q : ℕ) : ℕ → ℂ :=
  fun r => if Nat.gcd r q = 1 then 1 / (Nat.totient q : ℂ) else 0

/-- **The major arcs**: the union of the Farey windows `|α − a/q| ≤ 1/(q(Q+1))` over
    moduli `q ≤ P`. Countable union of closed balls, hence measurable. -/
def MajorArcs (P Q : ℕ) : Set ℝ :=
  ⋃ q ∈ Set.Icc 1 P, ⋃ a : ℤ, Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1)))

/-- The finite set of REDUCED Farey anchors with moduli ≤ P relevant to `(0,1]`. -/
noncomputable def anchors (P : ℕ) : Finset (ℕ × ℤ) :=
  (Finset.Icc 1 P ×ˢ Finset.Icc (-(P : ℤ)) (2 * P)).filter
    (fun pq => Int.gcd pq.2 pq.1 = 1)

noncomputable def minorCsup (N U V P Q : ℕ) : ℝ :=
  2 * Real.log (N + 1) * ((2 * (N : ℝ) / P) * (1 + Real.log U)
      + (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) + U)
  + Real.log (U * V) * ((2 * (N : ℝ) / P) * (1 + Real.log (U * V))
      + (16 * (U * V) + 4 * Q) * (2 + Real.log (2 * Q)))
  + (V : ℝ) * Real.log V
  + Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
      + Real.sqrt 32 * N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt P
      + 64 * N * Real.sqrt (1 + Real.log (2 * Q)) / Real.sqrt U
      + 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (N * Q * (1 + Real.log (2 * Q))))

set_option maxHeartbeats 1000000

/-!
# The Vinogradov minor-arc sup bound for `∑ Λ(n) e(nα)` — the complete chain

**Main theorem** (`MinSum.vinogradov_sup`): for `gcd(a,q) = 1`, `|α − a/q| ≤ 1/q²`,
`q ≥ 2`, `U ≤ N`, `1 ≤ U·V ≤ N`:

  `‖∑_{n≤N} Λ(n) e(nα)‖ ≤ B₁(U,N,q) + B₂(UV,N,q) + V·log V + B₄(U,N,q)`

with every `Bᵢ` fully explicit — the analytic heart of the circle method's minor arcs
for almost-all binary Goldbach (`AlmostAllGoldbachReduction.lean` consumes the variance
bound this sup feeds). Built entirely from Mathlib, self-contained in this file.

The chain, bottom to top (every lemma verified 0 errors / 0 sorries with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

## 1. The min-sum workhorse (Vaughan Lemma 2.2 / IK 13.7)
  • `image_natCast_Ico`, `image_mul_natCast_Ico` — block bijections onto `ZMod q`.
  • `sum_Icc_reflect`, `sum_one_div_le`, `sum_q_div_min_le` — the harmonic core.
  • `dist_round_le` (1-Lipschitz), `dist_round_neg` (even), `dist_int_div_ge` (q∤m separation).
  • `spaced_floor_sign_injOn`, `spaced_min_sum_le` — the δ-spaced counting core
    (`∑ min(V, 1/(2·dist)) ≤ 2V + (2/δ)(1+log(1/δ))`).
  • `block_spaced` — `L ≤ q/2` consecutive `h` make `hα` pairwise `1/(2q)`-spaced.
  • `range_min_sum_le` — **the workhorse, uniform-cap form**:
    `∑_{h∈[M,M+R)} min(V, 1/(2‖hα‖)) ≤ (R/(q/2)+1)(2V + 4q(1+log 2q))`.
  • `dyadic_cap_sum_le` — **the N/h-cap form** via dyadic blocks:
    `∑_{h≤H} min(N/h, 1/(2‖hα‖)) ≤ (log₂H+1)(8N/q + 4qL) + 32HL + 4N`.
  • `cap_symmetric_sum_le` — the symmetric-in-h pure-cap form.

## 2. The exponential-sum chain (self-contained copy of the `MinorArcExpSum.lean` core)
  • `e`, `e_norm`, `e_pow`, `e_add`, `e_conj`; `geom_exp_bound`, `e_sub_one_norm`,
    `exp_sum_le_sin`, `two_dist_le_abs_sin`, `exp_sum_bound`, `exp_sum_trivial`.
  • `exp_sum_min_bound`, `exp_sum_Ico_min_bound`, `exp_sum_Ioc_min_bound` — capped forms.
  • `abel_exp_sum` — monotone weights cost only `2W` (partial summation).

## 3. Type I / Type II
  • `typeI_sum_bound` — `∑_{d≤D} ‖∑_{n<M} e(ndα)‖ ≤ (D/(q/2)+1)(2M + 4qL)`.
  • `typeII_second_moment_le`, `dist_round_neg`, `diff_count_le`, `typeII_h_sum_le`,
    `typeII_second_moment_workhorse`, `typeII_bilinear_sq_le` — the bilinear estimate.

## 4. The Vaughan combine (section `VaughanDecomposition`)
  • `vaughan_identity` (ring form), `vaughan_sum_decomposition` — `∑Λe = S₁−S₂+S₃+S₄`.
  • `sum_Ioc_mul_weight`, `sum_Ioc_mul_weight_eq_sum_sum` — the weighted hyperbola
    unfolding and regrouping (`∑(f∗g)(n)w(n) = ∑_d f(d)∑_{m≤N/d} g(m)w(dm)`).
  • `truncate` + `abs_truncate_moebius_le_one`, `truncate_vonMangoldt_nonneg/le`,
    `abs_truncate_mul_le_log`, `truncate_mul_eq_zero_of_gt`, `sum_vonMangoldt_le`,
    `sum_Ioc_zeta_mul`, `log_natCast_nonneg/monotone`, `cap_succ_le`, `sub_apply'`,
    `tail_conv_nonneg/le_log/eq_zero_of_le`, `moebius_tail_eq_zero_of_le`,
    `abs_moebius_tail_le_one` — the truncated Vaughan pieces with all sup/support facts.
  • `filtered_exp_sum_cap`, `hyperbola_second_moment_expand`, `S4_block_second_moment`
    — the hyperbola problem (varying `m ≤ N/d` ranges), solved.
  • **`S1_bound`, `S2_bound`, `S3_bound`, `S4_bound`** — the four Vaughan pieces,
    each explicitly bounded on the arc.
  • `vinogradov_sup_skeleton`, **`vinogradov_sup`** — the final composition.

Pinned: `leanprover/lean4:v4.31.0` + Mathlib v4.31.0. Companion files:
`MinorArcExpSum.lean` (exp-sum core + Parseval + char orthogonality),
`VaughanIdentity.lean`, `AlmostAllGoldbachReduction.lean`.
-/

namespace MinSum

open Finset

/-- Any `q` consecutive naturals cast onto `ZMod q` bijectively (as a Finset image). -/
lemma image_natCast_Ico (q : ℕ) [NeZero q] (M : ℕ) :
    Finset.image (fun h : ℕ => (h : ZMod q)) (Finset.Ico M (M + q)) = Finset.univ := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hinj : Set.InjOn (fun h : ℕ => (h : ZMod q)) (Finset.Ico M (M + q)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
    have hmod : x ≡ y [MOD q] := (ZMod.natCast_eq_natCast_iff x y q).mp hxy
    have hdvd : (q : ℤ) ∣ (y : ℤ) - x := hmod.dvd
    have hlt : |(y : ℤ) - x| < q := by
      rw [abs_lt]
      constructor <;> [skip; skip] <;> omega
    have : (y : ℤ) - x = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    omega
  have hcard : (Finset.image (fun h : ℕ => (h : ZMod q)) (Finset.Ico M (M + q))).card
      = Finset.univ.card (α := ZMod q) := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Ico]
    simp [ZMod.card q]
  exact Finset.eq_univ_of_card _ hcard

/-- With `gcd(a,q) = 1`, the map `h ↦ h·a` on any `q` consecutive naturals covers `ZMod q`. -/
lemma image_mul_natCast_Ico (q : ℕ) [NeZero q] (a : ℕ) (ha : Nat.Coprime a q) (M : ℕ) :
    Finset.image (fun h : ℕ => (h : ZMod q) * a) (Finset.Ico M (M + q)) = Finset.univ := by
  have h1 : Finset.image (fun h : ℕ => (h : ZMod q) * a) (Finset.Ico M (M + q))
      = Finset.image (fun x : ZMod q => x * a)
          (Finset.image (fun h : ℕ => (h : ZMod q)) (Finset.Ico M (M + q))) := by
    rw [Finset.image_image]; rfl
  rw [h1, image_natCast_Ico q M]
  have hunit : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr ha
  obtain ⟨u, hu⟩ := hunit
  apply Finset.image_univ_of_surjective
  intro x
  refine ⟨x * ↑u⁻¹, ?_⟩
  show x * ↑u⁻¹ * (a : ZMod q) = x
  rw [← hu, mul_assoc, Units.inv_mul, mul_one]

/-- `dist(·,ℤ)` is 1-Lipschitz: `‖x‖ ≤ |x−y| + ‖y‖` (round minimizes over ℤ).
    This is the perturbation step: for `|α − a/q| ≤ 1/q²` it transfers the `‖h·a/q‖`
    block counting to `‖hα‖` at the cost of `h/q² ≤ 1/q` per block. -/
lemma dist_round_le (x y : ℝ) :
    |x - round x| ≤ |x - y| + |y - round y| := by
  calc |x - round x| ≤ |x - round y| := round_le x (round y)
    _ = |(x - y) + (y - round y)| := by ring_nf
    _ ≤ |x - y| + |y - round y| := abs_add_le _ _

/-- A rational `m/q` with `q ∤ m` is at distance `≥ 1/q` from every integer.
    (Feeds the block-spacing fact: `(h₁−h₂)·a/q` is `1/q`-separated from ℤ when
    `q ∤ (h₁−h₂)a`, which the coprime block bijection guarantees.) -/
lemma dist_int_div_ge (m : ℤ) (q : ℕ) (hq : 0 < q) (hnd : ¬ (q : ℤ) ∣ m) :
    1 / (q : ℝ) ≤ |(m : ℝ) / q - round ((m : ℝ) / q)| := by
  set r : ℤ := m - q * round ((m : ℝ) / q) with hr
  have hrne : r ≠ 0 := by
    intro h
    apply hnd
    refine ⟨round ((m : ℝ) / q), ?_⟩
    omega
  have h1 : (1 : ℤ) ≤ |r| := Int.one_le_abs hrne
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have heq : (m : ℝ) / q - round ((m : ℝ) / q) = (r : ℝ) / q := by
    rw [hr]
    push_cast
    field_simp
  rw [heq, abs_div, abs_of_nonneg hqR.le]
  gcongr
  · exact_mod_cast h1

/-- Reflection: `∑_{k=1}^{q-1} f(q-k) = ∑_{k=1}^{q-1} f(k)`. -/
lemma sum_Icc_reflect (q : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (q - 1), f (q - k) = ∑ k ∈ Finset.Icc 1 (q - 1), f k := by
  apply Finset.sum_nbij' (i := fun k => q - k) (j := fun k => q - k)
  · intro k hk; simp only [Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; rfl

/-- Harmonic-sum form: `∑_{k=1}^{n} 1/k ≤ 1 + log n`. -/
lemma sum_one_div_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ 1 + Real.log n := by
  have h1 : ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k = ((harmonic n : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  rw [h1]
  exact harmonic_le_one_add_log n

/-- **The harmonic core of the min-sum workhorse**:
    `∑_{k=1}^{q-1} q / min(k, q-k) ≤ 2q(1 + log q)`. Since `‖k/q‖ = min(k, q-k)/q`,
    this is exactly `∑_{k≠0 mod q} 1/(2‖k/q‖) ≤ 4q(1+log q)`-strength — the per-block
    contribution of the non-exceptional residues. -/
lemma sum_q_div_min_le (q : ℕ) (hq : 1 ≤ q) :
    ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((min k (q - k) : ℕ) : ℝ)
      ≤ 2 * q * (1 + Real.log q) := by
  have hlogq : 0 ≤ Real.log q := by
    rcases Nat.eq_or_lt_of_le hq with h | h
    · rw [← h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h.le)
  have step1 : ∀ k ∈ Finset.Icc 1 (q - 1),
      (q : ℝ) / ((min k (q - k) : ℕ) : ℝ) ≤ (q : ℝ) / k + (q : ℝ) / ((q - k : ℕ) : ℝ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hqk : 1 ≤ q - k := by omega
    have hqk1 : (1 : ℝ) ≤ ((q - k : ℕ) : ℝ) := by exact_mod_cast hqk
    have hposk : (0 : ℝ) < (k : ℝ) := by linarith
    have hposqk : (0 : ℝ) < ((q - k : ℕ) : ℝ) := by linarith
    rcases min_choice k (q - k) with h | h <;> rw [h]
    · have h2 : (0 : ℝ) ≤ (q : ℝ) / ((q - k : ℕ) : ℝ) := by positivity
      linarith
    · have h2 : (0 : ℝ) ≤ (q : ℝ) / (k : ℝ) := by positivity
      linarith
  have hrefl : ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((q - k : ℕ) : ℝ)
      = ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ) :=
    sum_Icc_reflect q (fun k => (q : ℝ) / (k : ℝ))
  have hharm : ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ)
      ≤ (q : ℝ) * (1 + Real.log q) := by
    have h1 : ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ)
        = (q : ℝ) * ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [div_eq_mul_inv, one_div])
    rw [h1]
    have h2 : ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / k ≤ 1 + Real.log (q - 1 : ℕ) :=
      sum_one_div_le (q - 1)
    have h3 : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q := by
      rcases Nat.eq_or_lt_of_le hq with h | h
      · rw [← h]; simp
      · apply Real.log_le_log (by exact_mod_cast Nat.sub_pos_of_lt h)
        have : q - 1 ≤ q := Nat.sub_le q 1
        exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith [h2, h3]
  calc ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((min k (q - k) : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 (q - 1), ((q : ℝ) / k + (q : ℝ) / ((q - k : ℕ) : ℝ)) :=
        Finset.sum_le_sum step1
    _ = ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ)
        + ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((q - k : ℕ) : ℝ) := Finset.sum_add_distrib
    _ = 2 * ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ) := by rw [hrefl]; ring
    _ ≤ 2 * ((q : ℝ) * (1 + Real.log q)) := by linarith [hharm]
    _ = 2 * q * (1 + Real.log q) := by ring

/-- **Spacing injection** (the counting core of the min-sum workhorse / baby large sieve):
    if the points `x i` are pairwise `δ`-spaced mod 1, then the map
    `i ↦ (⌊2·dist(xᵢ,ℤ)/δ⌋, sign of the signed distance)` is injective — i.e. each
    distance-annulus `[kδ/2, (k+1)δ/2)` holds at most one point on each side of ℤ. -/
lemma spaced_floor_sign_injOn {ι : Type*} (s : Finset ι) (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hspace : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |(x i - x j) - round (x i - x j)|) :
    Set.InjOn (fun i =>
      ((⌊2 * |x i - round (x i)| / δ⌋₊, decide (0 ≤ x i - round (x i))) : ℕ × Bool))
      (s : Set ι) := by
  intro i hi j hj hij
  by_contra hne
  have hsp := hspace i hi j hj hne
  set fi : ℝ := x i - round (x i) with hfi
  set fj : ℝ := x j - round (x j) with hfj
  have hk : ⌊2 * |fi| / δ⌋₊ = ⌊2 * |fj| / δ⌋₊ := by
    have := congrArg Prod.fst hij; simpa using this
  have hb : (0 ≤ fi) ↔ (0 ≤ fj) := by
    have := congrArg Prod.snd hij
    simp only [decide_eq_decide] at this
    exact this
  -- floor equality ⇒ ||fi| − |fj|| < δ/2
  have ha0 : 0 ≤ 2 * |fi| / δ := by positivity
  have hb0 : 0 ≤ 2 * |fj| / δ := by positivity
  have habs : |(|fi| - |fj|)| < δ / 2 := by
    have h1 : 2 * |fi| / δ < ⌊2 * |fi| / δ⌋₊ + 1 := Nat.lt_floor_add_one _
    have h2 : (⌊2 * |fj| / δ⌋₊ : ℝ) ≤ 2 * |fj| / δ := Nat.floor_le hb0
    have h3 : 2 * |fj| / δ < ⌊2 * |fj| / δ⌋₊ + 1 := Nat.lt_floor_add_one _
    have h4 : (⌊2 * |fi| / δ⌋₊ : ℝ) ≤ 2 * |fi| / δ := Nat.floor_le ha0
    rw [hk] at h1 h4
    have hd1 : 2 * |fi| / δ - 2 * |fj| / δ < 1 := by linarith
    have hd2 : 2 * |fj| / δ - 2 * |fi| / δ < 1 := by linarith
    have hd1' : 2 * |fi| - 2 * |fj| < δ :=
      (div_lt_one hδ).mp (by rw [sub_div]; linarith [hd1])
    have hd2' : 2 * |fj| - 2 * |fi| < δ :=
      (div_lt_one hδ).mp (by rw [sub_div]; linarith [hd2])
    rw [abs_lt]
    constructor <;> linarith
  -- same sign ⇒ |fi − fj| = ||fi| − |fj|| < δ
  have hsame : |fi - fj| < δ := by
    by_cases hpos : 0 ≤ fi
    · have hpj : 0 ≤ fj := hb.mp hpos
      calc |fi - fj| = |(|fi| - |fj|)| := by rw [abs_of_nonneg hpos, abs_of_nonneg hpj]
        _ < δ / 2 := habs
        _ < δ := by linarith
    · have hneg : fi < 0 := not_le.mp hpos
      have hnj : fj < 0 := by
        by_contra hc
        exact absurd (hb.mpr (not_lt.mp hc)) hpos
      calc |fi - fj| = |(|fi| - |fj|)| := by
            rw [abs_of_neg hneg, abs_of_neg hnj, ← abs_neg]; ring_nf
        _ < δ / 2 := habs
        _ < δ := by linarith
  -- dist(xᵢ−xⱼ, ℤ) ≤ |fi − fj| (round minimizes), contradicting the spacing
  have hmin : |(x i - x j) - round (x i - x j)| ≤ |fi - fj| := by
    have heq : fi - fj = (x i - x j) - ((round (x i) - round (x j) : ℤ) : ℝ) := by
      push_cast; rw [hfi, hfj]; ring
    calc |(x i - x j) - round (x i - x j)|
        ≤ |(x i - x j) - ((round (x i) - round (x j) : ℤ) : ℝ)| :=
          round_le (x i - x j) (round (x i) - round (x j))
      _ = |fi - fj| := by rw [heq]
  linarith

/-- **Spaced-points min-sum bound** (the workhorse's per-block estimate): pairwise
    δ-spaced points contribute at most `2V + (2/δ)(1 + log(1/δ))` to the capped
    reciprocal-distance sum. Combines the spacing injection with the harmonic bound. -/
lemma spaced_min_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (δ V : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hV : 0 ≤ V)
    (hspace : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |(x i - x j) - round (x i - x j)|) :
    ∑ i ∈ s, (if x i - round (x i) = 0 then V
              else min V (1 / (2 * |x i - round (x i)|)))
      ≤ 2 * V + (2 / δ) * (1 + Real.log (1 / δ)) := by
  classical
  set K : ℕ := ⌊1 / δ⌋₊ with hK
  set φ : ι → ℕ × Bool := fun i =>
    (⌊2 * |x i - round (x i)| / δ⌋₊, decide (0 ≤ x i - round (x i))) with hφ
  set W : ℕ × Bool → ℝ := fun p => if p.1 = 0 then V else 1 / (p.1 * δ) with hW
  have hW0 : ∀ p, 0 ≤ W p := by
    intro p
    rw [hW]
    dsimp only
    split
    · exact hV
    · rename_i h
      have hp : (0 : ℝ) < p.1 := by exact_mod_cast Nat.pos_of_ne_zero h
      positivity
  -- termwise: each term is at most W (φ i)
  have hterm : ∀ i ∈ s, (if x i - round (x i) = 0 then V
      else min V (1 / (2 * |x i - round (x i)|))) ≤ W (φ i) := by
    intro i _
    by_cases hf0 : x i - round (x i) = 0
    · rw [if_pos hf0, hW, hφ]
      dsimp only
      rw [hf0]
      simp
    · rw [if_neg hf0]
      by_cases hk : ⌊2 * |x i - round (x i)| / δ⌋₊ = 0
      · have : W (φ i) = V := by rw [hW, hφ]; dsimp only; rw [if_pos hk]
        rw [this]
        exact min_le_left _ _
      · have habs : 0 < |x i - round (x i)| := abs_pos.mpr hf0
        have hkle : (⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ)
            ≤ 2 * |x i - round (x i)| / δ := Nat.floor_le (by positivity)
        have h1 : (⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ) * δ ≤ 2 * |x i - round (x i)| := by
          have := mul_le_mul_of_nonneg_right hkle hδ.le
          rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at this
        have hkpos : (0 : ℝ) < (⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hk
        have h2 : 1 / (2 * |x i - round (x i)|)
            ≤ 1 / ((⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ) * δ) :=
          one_div_le_one_div_of_le (by positivity) h1
        have h3 : W (φ i) = 1 / ((⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ) * δ) := by
          rw [hW, hφ]; dsimp only; rw [if_neg hk]
        rw [h3]
        exact le_trans (min_le_right _ _) h2
  -- image is inside range (K+1) ×ˢ Bool
  have himg : s.image φ ⊆ (Finset.range (K + 1)) ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_range, Nat.lt_succ_iff, hK]
    apply Nat.floor_mono
    have hhalf : |x i - round (x i)| ≤ 1 / 2 := abs_sub_round (x i)
    have : 2 * |x i - round (x i)| ≤ 1 := by linarith
    exact div_le_div_of_nonneg_right this hδ.le
  -- assemble
  calc ∑ i ∈ s, (if x i - round (x i) = 0 then V
        else min V (1 / (2 * |x i - round (x i)|)))
      ≤ ∑ i ∈ s, W (φ i) := Finset.sum_le_sum hterm
    _ = ∑ p ∈ s.image φ, W p := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact spaced_floor_sign_injOn s x δ hδ hspace ha hb hab
    _ ≤ ∑ p ∈ (Finset.range (K + 1)) ×ˢ (Finset.univ : Finset Bool), W p :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun p _ _ => hW0 p)
    _ = ∑ k ∈ Finset.range (K + 1), ∑ b : Bool, W (k, b) := by rw [Finset.sum_product]
    _ = ∑ k ∈ Finset.range (K + 1), 2 * (if k = 0 then V else 1 / (k * δ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Fintype.sum_bool, hW]
        dsimp only
        ring
    _ = 2 * V + 2 * ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * δ) := by
        have hsplit : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
          ext k
          simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [hsplit, Finset.sum_insert (by simp)]
        rw [if_pos rfl]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [if_neg (by omega)]
    _ ≤ 2 * V + (2 / δ) * (1 + Real.log (1 / δ)) := by
        have hδinv : (0 : ℝ) < 1 / δ := by positivity
        have hKle : (K : ℝ) ≤ 1 / δ := by
          rw [hK]; exact Nat.floor_le hδinv.le
        have hK1 : 1 ≤ K := by
          rw [hK]
          apply Nat.le_floor
          rw [Nat.cast_one]
          rw [le_div_iff₀ hδ]
          linarith
        have h1 : ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * δ)
            = (1 / δ) * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_Icc] at hk
          have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
          field_simp
        have h2 := sum_one_div_le K
        have h3 : Real.log K ≤ Real.log (1 / δ) := by
          apply Real.log_le_log (by exact_mod_cast hK1) hKle
        have hlog0 : 0 ≤ Real.log (1 / δ) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ hδ]
          linarith
        rw [h1]
        have h4 : ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k ≤ 1 + Real.log (1 / δ) := by linarith
        have h5 : (1 / δ) * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k
            ≤ (1 / δ) * (1 + Real.log (1 / δ)) := by
          apply mul_le_mul_of_nonneg_left h4 hδinv.le
        have h6 : (2 : ℝ) / δ = 2 * (1 / δ) := by ring
        rw [h6]
        linarith

/-- **Block spacing**: for `gcd(a,q)=1` and `|α − a/q| ≤ 1/q²`, the points `hα` for `h`
    in a run of `L ≤ q/2` consecutive integers are pairwise `1/(2q)`-spaced mod 1.
    (So each such block feeds `spaced_min_sum_le` with `δ = 1/(2q)`.) -/
lemma block_spaced (a q : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M L : ℕ) (hL : 2 * L ≤ q) :
    ∀ i ∈ Finset.Ico M (M + L), ∀ j ∈ Finset.Ico M (M + L), i ≠ j →
      1 / (2 * (q : ℝ)) ≤
        |((i : ℝ) * α - (j : ℝ) * α) - round ((i : ℝ) * α - (j : ℝ) * α)| := by
  intro i hi j hj hij
  simp only [Finset.mem_Ico] at hi hj
  set d : ℤ := (i : ℤ) - j with hd
  have hdne : d ≠ 0 := by rw [hd]; omega
  have hdabs : |d| ≤ (L : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
  -- q ∤ d·a (coprimality + |d| < q)
  have hnd : ¬ (q : ℤ) ∣ d * a := by
    intro hdvd
    have hu : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr ha
    have h0 : ((d * (a : ℤ) : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
    push_cast at h0
    have hd0 : ((d : ℤ) : ZMod q) = 0 := (hu.mul_left_eq_zero).mp h0
    have hqd : (q : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hd0
    have hqle : (q : ℤ) ≤ |d| := Int.le_of_dvd (abs_pos.mpr hdne) ((dvd_abs _ _).mpr hqd)
    have : (q : ℤ) ≤ (L : ℤ) := le_trans hqle hdabs
    omega
  -- the rational point d·a/q is 1/q-separated from ℤ
  have hsep : 1 / (q : ℝ) ≤ |((d * a : ℤ) : ℝ) / q - round (((d * a : ℤ) : ℝ) / q)| :=
    dist_int_div_ge (d * a) q hq hnd
  -- the perturbation |(iα−jα) − d·a/q| = |d|·|α−a/q| ≤ L/q² ≤ 1/(2q)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpert : |((i : ℝ) * α - (j : ℝ) * α) - ((d * a : ℤ) : ℝ) / q| ≤ 1 / (2 * (q : ℝ)) := by
    have h1 : (i : ℝ) * α - (j : ℝ) * α = (d : ℝ) * α := by
      rw [hd]; push_cast; ring
    have h2 : ((d * a : ℤ) : ℝ) / q = (d : ℝ) * ((a : ℝ) / q) := by
      push_cast; ring
    rw [h1, h2, ← mul_sub, abs_mul]
    have h3 : |(d : ℝ)| ≤ (L : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hdabs
    have hL' : (2 : ℝ) * L ≤ q := by exact_mod_cast hL
    calc |(d : ℝ)| * |α - (a : ℝ) / q| ≤ (L : ℝ) * (1 / (q : ℝ) ^ 2) := by
          apply mul_le_mul h3 hα (abs_nonneg _) (by positivity)
      _ ≤ 1 / (2 * (q : ℝ)) := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- combine: dist(iα−jα) ≥ dist(d·a/q) − perturbation ≥ 1/q − 1/(2q) = 1/(2q)
  have hcomb := dist_round_le (((d * a : ℤ) : ℝ) / q) ((i : ℝ) * α - (j : ℝ) * α)
  rw [abs_sub_comm (((d * a : ℤ) : ℝ) / q) ((i : ℝ) * α - (j : ℝ) * α)] at hcomb
  have hq2R : 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 / (2 * (q : ℝ)) := by
    field_simp
    ring
  linarith [hsep, hpert, hcomb, hq2R]

/-- **The min-sum workhorse, uniform-cap form**: for `gcd(a,q) = 1`, `|α − a/q| ≤ 1/q²`,
    `q ≥ 2`, and ANY `R` consecutive integers with a uniform cap `V`,

      `∑_h min(V, 1/(2‖hα‖)) ≤ (R/(q/2) + 1) · (2V + 4q(1 + log 2q))`.

    (Terms with `hα ∈ ℤ` get the `V` cap.) This is the block-summed engine of the
    Type-I/II minor-arc estimates; the classical `N/h`-cap form (Vaughan Lemma 2.2)
    follows by applying this on dyadic `h`-ranges with `V = N/2ᵗ`. -/
lemma range_min_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (V : ℝ) (hV : 0 ≤ V) (M R : ℕ) :
    ∑ h ∈ Finset.Ico M (M + R),
      (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then V
       else min V (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
      ≤ ((R / (q / 2) + 1 : ℕ) : ℝ) * (2 * V + 4 * q * (1 + Real.log (2 * q))) := by
  set L : ℕ := q / 2 with hLdef
  have hL0 : 0 < L := Nat.div_pos hq (by norm_num)
  have h2L : 2 * L ≤ q := by
    have := Nat.div_mul_le_self q 2
    omega
  set T : ℕ := R / L + 1 with hT
  set w : ℕ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then V
     else min V (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hw
  have hw0 : ∀ h, 0 ≤ w h := by
    intro h
    rw [hw]
    dsimp only
    split
    · exact hV
    · exact le_min hV (by positivity)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  -- covering by T blocks of length L
  have hcover : Finset.Ico M (M + R) ⊆
      (Finset.range T).biUnion (fun t => Finset.Ico (M + t * L) (M + t * L + L)) := by
    intro h hh
    simp only [Finset.mem_Ico] at hh
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hh.1
    have hnR : n < R := by omega
    rw [Finset.mem_biUnion]
    refine ⟨n / L, ?_, ?_⟩
    · rw [Finset.mem_range, hT]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hnR.le)
    · obtain ⟨P, hP⟩ : ∃ P, P = n / L * L := ⟨_, rfl⟩
      obtain ⟨m, hm⟩ : ∃ m, m = n % L := ⟨_, rfl⟩
      have h1 : P ≤ n := hP ▸ Nat.div_mul_le_self n L
      have hdm : P + m = n := by rw [hP, hm]; exact Nat.div_add_mod' n L
      have hmod : m < L := hm ▸ Nat.mod_lt n hL0
      rw [Finset.mem_Ico, ← hP]
      omega
  -- blocks are pairwise disjoint
  have hdisj : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint
      (fun t => Finset.Ico (M + t * L) (M + t * L + L)) := by
    intro t₁ _ t₂ _ hne
    apply Finset.disjoint_left.mpr
    intro h h1 h2
    simp only [Finset.mem_Ico] at h1 h2
    obtain ⟨P₁, hP₁⟩ : ∃ P, P = t₁ * L := ⟨_, rfl⟩
    obtain ⟨P₂, hP₂⟩ : ∃ P, P = t₂ * L := ⟨_, rfl⟩
    rw [← hP₁] at h1
    rw [← hP₂] at h2
    rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
    · have h5 : P₁ + L ≤ P₂ := by
        rw [hP₁, hP₂, ← Nat.succ_mul]
        exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
      omega
    · have hlt2 : t₂ < t₁ := lt_of_le_of_ne hge (Ne.symm hne)
      have h5 : P₂ + L ≤ P₁ := by
        rw [hP₁, hP₂, ← Nat.succ_mul]
        exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt2)
      omega
  -- per-block bound via spaced_min_sum_le with δ = 1/(2q)
  have hblock : ∀ t : ℕ, ∑ h ∈ Finset.Ico (M + t * L) (M + t * L + L), w h
      ≤ 2 * V + 4 * (q : ℝ) * (1 + Real.log (2 * q)) := by
    intro t
    have hδpos : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
    have hδ1 : 1 / (2 * (q : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    have hsp := block_spaced a q (by omega) ha α hα (M + t * L) L h2L
    have happ := spaced_min_sum_le (Finset.Ico (M + t * L) (M + t * L + L))
      (fun h : ℕ => (h : ℝ) * α) (1 / (2 * (q : ℝ))) V hδpos hδ1 hV hsp
    have e1 : (2 : ℝ) / (1 / (2 * (q : ℝ))) = 4 * q := by
      field_simp
      ring
    have e2 : (1 : ℝ) / (1 / (2 * (q : ℝ))) = 2 * q := by
      field_simp
    rw [e1, e2] at happ
    exact happ
  -- assemble
  calc ∑ h ∈ Finset.Ico M (M + R), w h
      ≤ ∑ h ∈ (Finset.range T).biUnion
          (fun t => Finset.Ico (M + t * L) (M + t * L + L)), w h :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hw0 h)
    _ = ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (M + t * L) (M + t * L + L), w h :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ _t ∈ Finset.range T, (2 * V + 4 * (q : ℝ) * (1 + Real.log (2 * q))) :=
        Finset.sum_le_sum (fun t _ => hblock t)
    _ = (T : ℝ) * (2 * V + 4 * (q : ℝ) * (1 + Real.log (2 * q))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((R / (q / 2) + 1 : ℕ) : ℝ) * (2 * V + 4 * q * (1 + Real.log (2 * q))) := by
        rw [hT, hLdef]

/-! ### The exponential-sum chain (self-contained copy of the `MinorArcExpSum.lean` core,
    re-verified here so this file stays standalone for the warm-REPL daemon) -/












/-! ### Type I: the workhorse applied to the inner geometric sums -/


/-- Interval form: `‖∑_{d∈[A,B)} e(dβ)‖` obeys the same capped bound with `M = B−A`
    (shift out the unit-modulus prefactor `e(Aβ)`). Type II's inner `d`-sums need this. -/
lemma exp_sum_Ico_min_bound (β : ℝ) (A B : ℕ) :
    ‖∑ d ∈ Finset.Ico A B, e (d * β)‖
      ≤ (if β - round β = 0 then ((B - A : ℕ) : ℝ)
         else min ((B - A : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
  have hshift : ∑ d ∈ Finset.Ico A B, e (d * β)
      = e (A * β) * ∑ k ∈ Finset.range (B - A), e (k * β) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [e_add]
    congr 1
    push_cast
    ring
  rw [hshift, norm_mul, e_norm, one_mul]
  exact exp_sum_min_bound β (B - A)

/-- **The Type I estimate**: the `d`-sum of inner geometric sums over `[1, D]` is
    controlled by the workhorse — for `gcd(a,q)=1`, `|α − a/q| ≤ 1/q²`, `q ≥ 2`:

      `∑_{d=1}^{D} ‖∑_{n<M} e(ndα)‖ ≤ (D/(q/2) + 1)·(2M + 4q(1 + log 2q))`. -/
lemma typeI_sum_bound (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (D M : ℕ) :
    ∑ d ∈ Finset.Ico 1 (1 + D), ‖∑ n ∈ Finset.range M, e (n * ((d : ℝ) * α))‖
      ≤ ((D / (q / 2) + 1 : ℕ) : ℝ) * (2 * M + 4 * q * (1 + Real.log (2 * q))) := by
  have hterm : ∀ d ∈ Finset.Ico 1 (1 + D),
      ‖∑ n ∈ Finset.range M, e (n * ((d : ℝ) * α))‖
      ≤ (if (d : ℝ) * α - round ((d : ℝ) * α) = 0 then ((M : ℕ) : ℝ)
         else min ((M : ℕ) : ℝ) (1 / (2 * |(d : ℝ) * α - round ((d : ℝ) * α)|))) :=
    fun d _ => exp_sum_min_bound ((d : ℝ) * α) M
  calc ∑ d ∈ Finset.Ico 1 (1 + D), ‖∑ n ∈ Finset.range M, e (n * ((d : ℝ) * α))‖
      ≤ ∑ d ∈ Finset.Ico 1 (1 + D),
        (if (d : ℝ) * α - round ((d : ℝ) * α) = 0 then ((M : ℕ) : ℝ)
         else min ((M : ℕ) : ℝ) (1 / (2 * |(d : ℝ) * α - round ((d : ℝ) * α)|))) :=
        Finset.sum_le_sum hterm
    _ ≤ ((D / (q / 2) + 1 : ℕ) : ℝ) * (2 * (M : ℝ) + 4 * q * (1 + Real.log (2 * q))) :=
        range_min_sum_le a q hq ha α hα (M : ℝ) (by positivity) 1 D

/-- dist(·,ℤ) is even: `|(-β) − round(-β)| = |β − round β|` (round minimizes both ways). -/
lemma dist_round_neg (β : ℝ) : |(-β) - round (-β)| = |β - round β| := by
  apply le_antisymm
  · calc |(-β) - round (-β)| ≤ |(-β) - ((-(round β) : ℤ) : ℝ)| := round_le (-β) (-(round β))
      _ = |β - round β| := by push_cast; rw [← abs_neg]; ring_nf
  · calc |β - round β| ≤ |β - ((-(round (-β)) : ℤ) : ℝ)| := round_le β (-(round (-β)))
      _ = |(-β) - round (-β)| := by push_cast; rw [← abs_neg]; ring_nf

/-- **Difference-count bound**: each difference `h = m₁ − m₂` occurs for at most `M`
    pairs, so a nonneg function of the difference sums to at most `M` times its
    `h`-sum over `(-M, M)`. -/
lemma diff_count_le (F : ℤ → ℝ) (hF : ∀ h, 0 ≤ F h) (M : ℕ) :
    ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M, F ((m₁ : ℤ) - m₂)
      ≤ (M : ℝ) * ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), F h := by
  classical
  have h1 : ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M, F ((m₁ : ℤ) - m₂)
      = ∑ p ∈ Finset.range M ×ˢ Finset.range M, F ((p.1 : ℤ) - p.2) := by
    rw [Finset.sum_product]
  rw [h1]
  calc ∑ p ∈ Finset.range M ×ˢ Finset.range M, F ((p.1 : ℤ) - p.2)
      = ∑ h ∈ (Finset.range M ×ˢ Finset.range M).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2),
          ((Finset.range M ×ˢ Finset.range M).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card • F h :=
        Finset.sum_comp _ _
    _ ≤ ∑ h ∈ (Finset.range M ×ˢ Finset.range M).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2),
          (M : ℝ) * F h := by
        apply Finset.sum_le_sum
        intro h _
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (hF h)
        have hcard : ((Finset.range M ×ˢ Finset.range M).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card ≤ (Finset.range M).card := by
          apply Finset.card_le_card_of_injOn (fun p => p.1)
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
            exact hp.1.1
          · intro p hp p' hp' hpp
            rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
            have hpp' : p.1 = p'.1 := hpp
            have e1 := hp.2
            have e2 := hp'.2
            have h2 : (p.2 : ℤ) = (p'.2 : ℤ) := by omega
            exact Prod.ext hpp' (by exact_mod_cast h2)
        rw [Finset.card_range] at hcard
        exact_mod_cast hcard
    _ ≤ ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), (M : ℝ) * F h := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at hh
          obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hh
          rw [Finset.mem_Icc]
          omega
        · intro h _ _
          exact mul_nonneg (by positivity) (hF h)
    _ = (M : ℝ) * ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), F h :=
        (Finset.mul_sum _ _ _).symm

/-- **Discrete second moment** (Type II opening move): the `d`-averaged square of a
    linear exponential sum is bounded by the bilinear difference sums. -/
lemma typeII_second_moment_le (b : ℕ → ℂ) (M : ℕ) (α : ℝ) (s : Finset ℕ) :
    ∑ d ∈ s, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := by
  -- complex identity: ∑_d S_d·conj(S_d) = ∑_{m₁,m₂} b m₁ conj(b m₂) ∑_d e(d(m₁−m₂)α)
  have hid : ∑ d ∈ s, ((∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)) *
        (starRingEnd ℂ) (∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)))
      = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          (b m₁ * (starRingEnd ℂ) (b m₂)) *
            ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
    have hpt : ∀ d ∈ s,
        (∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)) *
          (starRingEnd ℂ) (∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α))
        = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
            (b m₁ * (starRingEnd ℂ) (b m₂)) * e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
      intro d _
      rw [map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro m₁ _
      apply Finset.sum_congr rfl; intro m₂ _
      rw [map_mul, e_conj]
      have h1 : e ((d : ℝ) * (m₁ : ℝ) * α) * e (-((d : ℝ) * (m₂ : ℝ) * α))
          = e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
        rw [e_add]; congr 1; ring
      calc b m₁ * e ((d : ℝ) * (m₁ : ℝ) * α)
            * ((starRingEnd ℂ) (b m₂) * e (-((d : ℝ) * (m₂ : ℝ) * α)))
          = (b m₁ * (starRingEnd ℂ) (b m₂))
            * (e ((d : ℝ) * (m₁ : ℝ) * α) * e (-((d : ℝ) * (m₂ : ℝ) * α))) := by ring
        _ = (b m₁ * (starRingEnd ℂ) (b m₂)) * e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
            rw [h1]
    rw [Finset.sum_congr rfl hpt]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m₁ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m₂ _
    rw [Finset.mul_sum]
  -- take real parts and bound
  have hre : ∑ d ∈ s, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      = (∑ d ∈ s, ((∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)) *
          (starRingEnd ℂ) (∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact (Complex.ofReal_re _).symm
  rw [hre, hid]
  calc (∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        (b m₁ * (starRingEnd ℂ) (b m₂)) * ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))).re
      ≤ ‖∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        (b m₁ * (starRingEnd ℂ) (b m₂)) * ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        Complex.re_le_norm _
    _ ≤ ∑ m₁ ∈ Finset.range M, ‖∑ m₂ ∈ Finset.range M,
        (b m₁ * (starRingEnd ℂ) (b m₂)) * ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        ‖(b m₁ * (starRingEnd ℂ) (b m₂)) * ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        Finset.sum_le_sum (fun m₁ _ => norm_sum_le _ _)
    _ = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := by
        apply Finset.sum_congr rfl; intro m₁ _
        apply Finset.sum_congr rfl; intro m₂ _
        rw [norm_mul, norm_mul, RCLike.norm_conj]

/-- **The Type II h-sum estimate**: the symmetric difference-sum of interval exponential
    sums is one diagonal term plus twice the workhorse. -/
lemma typeII_h_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (A B M : ℕ) :
    ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
        ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖
      ≤ ((B - A : ℕ) : ℝ)
        + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * q) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  set V : ℝ := ((B - A : ℕ) : ℝ) with hV
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  set w : ℤ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then V
     else min V (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hw
  have hw0 : ∀ h, 0 ≤ w h := by
    intro h
    rw [hw]
    dsimp only
    split
    · exact hV0
    · exact le_min hV0 (by positivity)
  have hG : ∀ h : ℤ, ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖ ≤ w h := by
    intro h
    rw [hw]
    exact exp_sum_Ico_min_bound ((h : ℝ) * α) A B
  have hweven : ∀ h : ℤ, w (-h) = w h := by
    intro h
    rw [hw]
    dsimp only
    have hcast : ((-h : ℤ) : ℝ) * α = -((h : ℝ) * α) := by push_cast; ring
    rw [hcast]
    have hd := dist_round_neg ((h : ℝ) * α)
    by_cases h0 : (h : ℝ) * α - round ((h : ℝ) * α) = 0
    · have h0' : -((h : ℝ) * α) - round (-((h : ℝ) * α)) = 0 := by
        have := hd
        rw [abs_eq_zero.mpr h0] at this
        exact abs_eq_zero.mp this
      rw [if_pos h0, if_pos h0']
    · have h0' : ¬ (-((h : ℝ) * α) - round (-((h : ℝ) * α)) = 0) := by
        intro hc
        apply h0
        have := hd
        rw [abs_eq_zero.mpr hc] at this
        exact abs_eq_zero.mp this.symm
      rw [if_neg h0, if_neg h0', hd]
  have hstep1 : ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
        ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖
      ≤ ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), w h :=
    Finset.sum_le_sum (fun h _ => hG h)
  rcases Nat.eq_zero_or_pos M with hM0 | hM1
  · subst hM0
    simp only [Nat.cast_zero, neg_zero, zero_add, zero_sub] at hstep1 ⊢
    rw [show Finset.Icc (1 : ℤ) (-1) = ∅ from Finset.Icc_eq_empty (by omega)] at hstep1 ⊢
    simp only [Finset.sum_empty] at hstep1 ⊢
    positivity
  have hK : (0 : ℤ) ≤ (M : ℤ) - 1 := by omega
  have hsplit : Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1)
      = (Finset.Icc (-(M : ℤ) + 1) (-1)) ∪ insert 0 (Finset.Icc 1 ((M : ℤ) - 1)) := by
    ext h
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert]
    omega
  have hdisj : Disjoint (Finset.Icc (-(M : ℤ) + 1) (-1))
      (insert 0 (Finset.Icc 1 ((M : ℤ) - 1))) := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    simp only [Finset.mem_Icc] at h1
    simp only [Finset.mem_insert, Finset.mem_Icc] at h2
    omega
  have h0notin : (0 : ℤ) ∉ Finset.Icc 1 ((M : ℤ) - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have hrefl : ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) (-1), w h
      = ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h := by
    apply Finset.sum_nbij' (i := fun h => -h) (j := fun h => -h)
    · intro h hh; simp only [Finset.mem_Icc] at *; omega
    · intro h hh; simp only [Finset.mem_Icc] at *; omega
    · intro h _; ring
    · intro h _; ring
    · intro h _
      rw [← hweven h]
  have hw0val : w 0 = V := by
    rw [hw]
    dsimp only
    rw [if_pos (by simp)]
  have hpos : ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h
      ≤ ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * V + 4 * q * (1 + Real.log (2 * q))) := by
    have hreidx : ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h
        = ∑ n ∈ Finset.Ico 1 (1 + (M - 1)),
            (if (n : ℝ) * α - round ((n : ℝ) * α) = 0 then V
             else min V (1 / (2 * |(n : ℝ) * α - round ((n : ℝ) * α)|))) := by
      apply Finset.sum_nbij' (i := fun h : ℤ => h.toNat) (j := fun n : ℕ => (n : ℤ))
      · intro h hh; simp only [Finset.mem_Icc] at hh; simp only [Finset.mem_Ico]; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; simp only [Finset.mem_Icc]; omega
      · intro h hh; simp only [Finset.mem_Icc] at hh; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; omega
      · intro h hh
        simp only [Finset.mem_Icc] at hh
        rw [hw]
        dsimp only
        have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
          have := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ h)
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
        rw [hcast]
    rw [hreidx]
    exact range_min_sum_le a q hq ha α hα V hV0 1 (M - 1)
  calc ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
        ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖
      ≤ ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), w h := hstep1
    _ = ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) (-1), w h
        + (w 0 + ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h) := by
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_insert h0notin]
    _ = V + 2 * ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h := by
        rw [hrefl, hw0val]; ring
    _ ≤ V + 2 * (((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * V + 4 * q * (1 + Real.log (2 * q)))) := by
        have := hpos
        linarith
    _ = ((B - A : ℕ) : ℝ)
        + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))) := by
        rw [hV]; ring

/-- **Abel-summation exponential-sum bound**: a monotone nonneg weight `w ≤ W` costs only
    a factor `2W` over the unweighted capped bound. (Feeds the log-weighted Type I sums
    in the Vaughan combine.) -/
lemma abel_exp_sum (w : ℕ → ℝ) (hw0 : ∀ m, 0 ≤ w m) (hwmono : Monotone w)
    (W : ℝ) (hW : ∀ m, w m ≤ W) (β : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, (w m : ℂ) * e (m * β)‖
      ≤ 2 * W * (if β - round β = 0 then (M : ℝ)
                 else min (M : ℝ) (1 / (2 * |β - round β|))) := by
  have hW0 : 0 ≤ W := le_trans (hw0 0) (hW 0)
  set cap : ℝ := (if β - round β = 0 then (M : ℝ)
                  else min (M : ℝ) (1 / (2 * |β - round β|))) with hcap
  have hcap0 : 0 ≤ cap := by
    rw [hcap]
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  have hZ : ∀ k, k ≤ M → ‖∑ j ∈ Finset.range k, e (j * β)‖ ≤ cap := by
    intro k hk
    have h1 := exp_sum_min_bound β k
    rw [hcap]
    have hkM : ((k : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk
    split
    · rename_i h0
      rw [if_pos h0] at h1
      linarith
    · rename_i h0
      rw [if_neg h0] at h1
      exact le_trans h1 (min_le_min hkM le_rfl)
  rcases Nat.eq_zero_or_pos M with hM0 | hM1
  · subst hM0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have habel : ∑ m ∈ Finset.range M, (w m : ℂ) * e (m * β)
      = (w (M - 1) : ℂ) * ∑ j ∈ Finset.range M, e (j * β)
        - ∑ i ∈ Finset.range (M - 1),
            ((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β) := by
    have := Finset.sum_range_by_parts (f := fun m => ((w m : ℝ) : ℂ))
      (g := fun m => e (m * β)) (n := M)
    simpa only [smul_eq_mul] using this
  rw [habel]
  calc ‖(w (M - 1) : ℂ) * ∑ j ∈ Finset.range M, e (j * β)
        - ∑ i ∈ Finset.range (M - 1),
            ((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β)‖
      ≤ ‖(w (M - 1) : ℂ) * ∑ j ∈ Finset.range M, e (j * β)‖
        + ‖∑ i ∈ Finset.range (M - 1),
            ((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β)‖ :=
        norm_sub_le _ _
    _ ≤ W * cap + ∑ i ∈ Finset.range (M - 1),
          (w (i + 1) - w i) * cap := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real]
          have h1 : |w (M - 1)| ≤ W := by rw [abs_of_nonneg (hw0 _)]; exact hW _
          exact mul_le_mul h1 (hZ M le_rfl) (norm_nonneg _) hW0
        · calc ‖∑ i ∈ Finset.range (M - 1),
                ((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β)‖
              ≤ ∑ i ∈ Finset.range (M - 1),
                ‖((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ i ∈ Finset.range (M - 1), (w (i + 1) - w i) * cap := by
                apply Finset.sum_le_sum
                intro i hi
                simp only [Finset.mem_range] at hi
                rw [norm_mul]
                have hcast : ((w (i + 1) : ℂ) - w i) = ((w (i + 1) - w i : ℝ) : ℂ) := by
                  push_cast; ring
                rw [hcast, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by linarith [hwmono (Nat.le_succ i)] : (0:ℝ) ≤ w (i+1) - w i)]
                apply mul_le_mul_of_nonneg_left _ (by linarith [hwmono (Nat.le_succ i)])
                exact hZ (i + 1) (by omega)
    _ = W * cap + (w (M - 1) - w 0) * cap := by
        congr 1
        rw [← Finset.sum_mul]
        congr 1
        exact Finset.sum_range_sub (fun i => w i) (M - 1)
    _ ≤ W * cap + W * cap := by
        have h4 : w (M - 1) - w 0 ≤ W := by linarith [hW (M - 1), hw0 0]
        have h5 := mul_le_mul_of_nonneg_right h4 hcap0
        linarith
    _ = 2 * W * cap := by ring

/-- (A) The Type II second moment through the workhorse chain. -/
lemma typeII_second_moment_workhorse (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (b : ℕ → ℂ) (Binf : ℝ) (hb : ∀ m, ‖b m‖ ≤ Binf)
    (A B M : ℕ) :
    ∑ d ∈ Finset.Ico A B, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ Binf ^ 2 * (M : ℝ) *
          (((B - A : ℕ) : ℝ)
            + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))) := by
  have hB0 : 0 ≤ Binf := le_trans (norm_nonneg _) (hb 0)
  have h3a := typeII_second_moment_le b M α (Finset.Ico A B)
  have h3b : ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
      ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖
      ≤ Binf ^ 2 * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((((m₁ : ℤ) - m₂) : ℤ) : ℝ) * α))‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m₂ _
    have hsum_eq : ∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))
        = ∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((((m₁ : ℤ) - m₂) : ℤ) : ℝ) * α)) :=
      Finset.sum_congr rfl (fun d _ => congrArg e (by push_cast; ring))
    rw [hsum_eq, pow_two]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (hb m₁) (hb m₂) (norm_nonneg _) hB0
  have h3c := diff_count_le
    (fun h => ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖)
    (fun h => norm_nonneg _) M
  have h3d := typeII_h_sum_le a q hq ha α hα A B M
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hB2 : (0 : ℝ) ≤ Binf ^ 2 := by positivity
  calc ∑ d ∈ Finset.Ico A B, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        h3a
    _ ≤ Binf ^ 2 * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((((m₁ : ℤ) - m₂) : ℤ) : ℝ) * α))‖ := h3b
    _ ≤ Binf ^ 2 * ((M : ℝ) * ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
          ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖) :=
        mul_le_mul_of_nonneg_left h3c hB2
    _ ≤ Binf ^ 2 * ((M : ℝ) * (((B - A : ℕ) : ℝ)
          + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))) := by
        apply mul_le_mul_of_nonneg_left _ hB2
        exact mul_le_mul_of_nonneg_left h3d hM0
    _ = Binf ^ 2 * (M : ℝ) *
        (((B - A : ℕ) : ℝ)
          + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))) := by ring

/-- **THE TYPE II (BILINEAR) ESTIMATE**: squared, with sup-bounded coefficients — for
    `gcd(a,q)=1`, `|α − a/q| ≤ 1/q²`, `q ≥ 2`:

      `‖∑_{d∈[A,B)} c_d ∑_{m<M} b_m e(dmα)‖² ≤ A∞²(B−A) · B∞²M · [workhorse bound]`. -/
lemma typeII_bilinear_sq_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (c b : ℕ → ℂ) (Ainf Binf : ℝ)
    (hc : ∀ d, ‖c d‖ ≤ Ainf) (hb : ∀ m, ‖b m‖ ≤ Binf)
    (A B M : ℕ) :
    ‖∑ d ∈ Finset.Ico A B, c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ Ainf ^ 2 * ((B - A : ℕ) : ℝ) * (Binf ^ 2 * (M : ℝ) *
          (((B - A : ℕ) : ℝ)
            + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))) := by
  have hA0 : 0 ≤ Ainf := le_trans (norm_nonneg _) (hc 0)
  have h1 : ‖∑ d ∈ Finset.Ico A B, c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ Ainf * ∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ := by
    calc ‖∑ d ∈ Finset.Ico A B, c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖
        ≤ ∑ d ∈ Finset.Ico A B, ‖c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ :=
          norm_sum_le _ _
      _ = ∑ d ∈ Finset.Ico A B,
            ‖c d‖ * ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ := by
          apply Finset.sum_congr rfl; intro d _; rw [norm_mul]
      _ ≤ ∑ d ∈ Finset.Ico A B,
            Ainf * ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ :=
          Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_right (hc d) (norm_nonneg _))
      _ = Ainf * ∑ d ∈ Finset.Ico A B,
            ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ :=
          (Finset.mul_sum _ _ _).symm
  have h2 : (∑ d ∈ Finset.Ico A B, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2
      ≤ ((B - A : ℕ) : ℝ) * ∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ico A B)
      (f := fun d => ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖)
    rw [Nat.card_Ico] at hcs
    exact_mod_cast hcs
  have h3 := typeII_second_moment_workhorse a q hq ha α hα b Binf hb A B M
  calc ‖∑ d ∈ Finset.Ico A B, c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ (Ainf * ∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Ainf ^ 2 * (∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2 := by ring
    _ ≤ Ainf ^ 2 * (((B - A : ℕ) : ℝ) * ∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ Ainf ^ 2 * (((B - A : ℕ) : ℝ) * (Binf ^ 2 * (M : ℝ) *
          (((B - A : ℕ) : ℝ)
            + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = Ainf ^ 2 * ((B - A : ℕ) : ℝ) * (Binf ^ 2 * (M : ℝ) *
          (((B - A : ℕ) : ℝ)
            + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))) := by ring

open ArithmeticFunction in
/-- **Weighted hyperbola unfolding** (the convolution → double-sum bridge of the
    Vaughan combine): for any weight `w : ℕ → ℂ`,
    `∑_{n≤N} (f∗g)(n)·w(n) = ∑_{d·m≤N} f(d)g(m)·w(dm)`. Applying this with
    `w n = e(nα)` to the four terms of `Vaughan.vaughan_identity` yields the
    S₁–S₄ decomposition that Type I / Abel / Type II bound. -/
lemma sum_Ioc_mul_weight (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℂ) * w n
      = ∑ x ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun x => x.1 * x.2 ≤ N),
          (f x.1 : ℂ) * (g x.2 : ℂ) * w (x.1 * x.2) := by
  have step1 : ∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℂ) * w n
      = ∑ n ∈ Finset.Ioc 0 N,
          ∑ x ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun x => x.1 * x.2 = n),
            (f x.1 : ℂ) * (g x.2 : ℂ) * w (x.1 * x.2) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hexp : ((f * g) n : ℂ) * w n
        = ∑ x ∈ n.divisorsAntidiagonal, (f x.1 : ℂ) * (g x.2 : ℂ) * w n := by
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rw [Finset.sum_mul]
    rw [hexp, Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_filter] at hx
    rw [hx.2]
  rw [step1]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_product, Finset.mem_Ioc] at hx
  have hpos : 0 < x.1 * x.2 := Nat.mul_pos hx.1.1 hx.2.1
  rw [Finset.sum_ite_eq (Finset.Ioc 0 N) (x.1 * x.2)
    (fun _ => (f x.1 : ℂ) * (g x.2 : ℂ) * w (x.1 * x.2))]
  simp only [Finset.mem_Ioc]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨hpos, h⟩

/-- **The symmetric cap-sum**: `∑_{|h|<M} cap(hα, W) ≤ W + 2((M−1)/(q/2)+1)(2W + 4q(1+log 2q))`
    for any nonneg cap size `W` — the pure-cap form of the Type II h-sum. -/
lemma cap_symmetric_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (W : ℝ) (hW : 0 ≤ W) (M : ℕ) :
    ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
      (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then W
       else min W (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
      ≤ W + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * W + 4 * q * (1 + Real.log (2 * q))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * q) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  set w : ℤ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then W
     else min W (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hw
  have hw0 : ∀ h, 0 ≤ w h := by
    intro h
    rw [hw]
    dsimp only
    split
    · exact hW
    · exact le_min hW (by positivity)
  have hweven : ∀ h : ℤ, w (-h) = w h := by
    intro h
    rw [hw]
    dsimp only
    have hcast : ((-h : ℤ) : ℝ) * α = -((h : ℝ) * α) := by push_cast; ring
    rw [hcast]
    have hd := dist_round_neg ((h : ℝ) * α)
    by_cases h0 : (h : ℝ) * α - round ((h : ℝ) * α) = 0
    · have h0' : -((h : ℝ) * α) - round (-((h : ℝ) * α)) = 0 := by
        have := hd
        rw [abs_eq_zero.mpr h0] at this
        exact abs_eq_zero.mp this
      rw [if_pos h0, if_pos h0']
    · have h0' : ¬ (-((h : ℝ) * α) - round (-((h : ℝ) * α)) = 0) := by
        intro hc
        apply h0
        have := hd
        rw [abs_eq_zero.mpr hc] at this
        exact abs_eq_zero.mp this.symm
      rw [if_neg h0, if_neg h0', hd]
  rcases Nat.eq_zero_or_pos M with hM0 | hM1
  · subst hM0
    simp only [Nat.cast_zero, neg_zero, zero_add, zero_sub]
    rw [show Finset.Icc (1 : ℤ) (-1) = ∅ from Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    have h1 : (0 : ℝ) ≤ 2 * W + 4 * q * (1 + Real.log (2 * q)) := by
      have : (0 : ℝ) ≤ 4 * q * (1 + Real.log (2 * q)) :=
        mul_nonneg (by positivity) (by linarith)
      linarith
    have h2 : (0 : ℝ) ≤ 2 * ((((0 - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
        * (2 * W + 4 * q * (1 + Real.log (2 * q))) := by
      apply mul_nonneg (by positivity) h1
    linarith
  have hsplit : Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1)
      = (Finset.Icc (-(M : ℤ) + 1) (-1)) ∪ insert 0 (Finset.Icc 1 ((M : ℤ) - 1)) := by
    ext h
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert]
    omega
  have hdisj : Disjoint (Finset.Icc (-(M : ℤ) + 1) (-1))
      (insert 0 (Finset.Icc 1 ((M : ℤ) - 1))) := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    simp only [Finset.mem_Icc] at h1
    simp only [Finset.mem_insert, Finset.mem_Icc] at h2
    omega
  have h0notin : (0 : ℤ) ∉ Finset.Icc 1 ((M : ℤ) - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have hrefl : ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) (-1), w h
      = ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h := by
    apply Finset.sum_nbij' (i := fun h => -h) (j := fun h => -h)
    · intro h hh; simp only [Finset.mem_Icc] at *; omega
    · intro h hh; simp only [Finset.mem_Icc] at *; omega
    · intro h _; ring
    · intro h _; ring
    · intro h _
      rw [← hweven h]
  have hw0val : w 0 = W := by
    rw [hw]
    dsimp only
    rw [if_pos (by simp)]
  have hpos : ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h
      ≤ ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * W + 4 * q * (1 + Real.log (2 * q))) := by
    have hreidx : ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h
        = ∑ n ∈ Finset.Ico 1 (1 + (M - 1)),
            (if (n : ℝ) * α - round ((n : ℝ) * α) = 0 then W
             else min W (1 / (2 * |(n : ℝ) * α - round ((n : ℝ) * α)|))) := by
      apply Finset.sum_nbij' (i := fun h : ℤ => h.toNat) (j := fun n : ℕ => (n : ℤ))
      · intro h hh; simp only [Finset.mem_Icc] at hh; simp only [Finset.mem_Ico]; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; simp only [Finset.mem_Icc]; omega
      · intro h hh; simp only [Finset.mem_Icc] at hh; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; omega
      · intro h hh
        simp only [Finset.mem_Icc] at hh
        rw [hw]
        dsimp only
        have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
          have := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ h)
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
        rw [hcast]
    rw [hreidx]
    exact range_min_sum_le a q hq ha α hα W hW 1 (M - 1)
  calc ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), w h
      = ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) (-1), w h
        + (w 0 + ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h) := by
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_insert h0notin]
    _ = W + 2 * ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h := by
        rw [hrefl, hw0val]; ring
    _ ≤ W + 2 * (((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * W + 4 * q * (1 + Real.log (2 * q)))) := by
        linarith [hpos]
    _ = W + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * W + 4 * q * (1 + Real.log (2 * q))) := by ring

/-- **The hyperbola-restricted interval cap**: the doubly-constrained d-sum is still an
    interval, and its cap is uniform in `B − A`. -/
lemma filtered_exp_sum_cap (β : ℝ) (N A B m₁ m₂ : ℕ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N), e (d * β)‖
      ≤ (if β - round β = 0 then ((B - A : ℕ) : ℝ)
         else min ((B - A : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
  have hset : (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N)
      = Finset.Ico A (min B (min (N / m₁) (N / m₂) + 1)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico, lt_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨h1, h2, ?_⟩
      have e1 : d ≤ N / m₁ := Nat.le_div_iff_mul_le hm₁ |>.mpr h3
      have e2 : d ≤ N / m₂ := Nat.le_div_iff_mul_le hm₂ |>.mpr h4
      omega
    · rintro ⟨h1, h2, h3⟩
      have e1 : d ≤ N / m₁ := by omega
      have e2 : d ≤ N / m₂ := by omega
      exact ⟨⟨h1, h2⟩, (Nat.le_div_iff_mul_le hm₁).mp e1, (Nat.le_div_iff_mul_le hm₂).mp e2⟩
  rw [hset]
  have h1 := exp_sum_Ico_min_bound β A (min B (min (N / m₁) (N / m₂) + 1))
  have hsize : ((min B (min (N / m₁) (N / m₂) + 1) - A : ℕ) : ℝ) ≤ ((B - A : ℕ) : ℝ) := by
    have : (min B (min (N / m₁) (N / m₂) + 1) - A : ℕ) ≤ (B - A : ℕ) := by omega
    exact_mod_cast this
  split at h1 <;> rename_i hcase
  · rw [if_pos hcase]
    linarith
  · rw [if_neg hcase]
    exact le_trans h1 (min_le_min hsize le_rfl)

/-- **The hyperbola second-moment expansion** (S₄'s centerpiece): the varying `m`-ranges
    `(V, N/d]` are absorbed into interval-restricted `d`-sums. -/
lemma hyperbola_second_moment_expand (g : ℕ → ℝ) (α : ℝ) (N A B V : ℕ) (hA : 0 < A) :
    ∑ d ∈ Finset.Ico A B,
      ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          |g m₁| * |g m₂| *
            ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := by
  -- extend each inner sum to the fixed range with indicator coefficients
  have hext : ∀ d ∈ Finset.Ico A B,
      ∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)
      = ∑ m ∈ Finset.Ioc V (N / A),
          ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hd0 : 0 < d := lt_of_lt_of_le hA hd.1
    have hstep : ∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)
        = ∑ m ∈ Finset.Ioc V (N / d),
            ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      rw [if_pos (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd0).mp hm.2)]
    rw [hstep]
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Ioc] at hm ⊢
      exact ⟨hm.1, le_trans hm.2 (Nat.div_le_div_left hd.1 hA)⟩
    · intro m hm hnot
      simp only [Finset.mem_Ioc] at hm hnot
      have hgt : N / d < m := by omega
      have hz : ¬ d * m ≤ N := by
        intro hc
        have : m ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr (by rwa [mul_comm] at hc)
        omega
      rw [if_neg hz]
      simp
  -- the complex identity with indicator coefficients
  have hid : ∑ d ∈ Finset.Ico A B,
      ((∑ m ∈ Finset.Ioc V (N / A),
          ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)) *
        (starRingEnd ℂ) (∑ m ∈ Finset.Ioc V (N / A),
          ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)))
      = ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          ((g m₁ * g m₂ : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
    have hpt : ∀ d ∈ Finset.Ico A B,
        (∑ m ∈ Finset.Ioc V (N / A),
            ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)) *
          (starRingEnd ℂ) (∑ m ∈ Finset.Ioc V (N / A),
            ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α))
        = ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
            (if d * m₁ ≤ N ∧ d * m₂ ≤ N then ((g m₁ * g m₂ : ℝ) : ℂ)
              * e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) else 0) := by
      intro d _
      rw [map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro m₁ _
      apply Finset.sum_congr rfl; intro m₂ _
      rw [map_mul, e_conj, Complex.conj_ofReal]
      have h1 : e ((d : ℝ) * (m₁ : ℝ) * α) * e (-((d : ℝ) * (m₂ : ℝ) * α))
          = e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
        rw [e_add]; congr 1; ring
      by_cases hc1 : d * m₁ ≤ N
      · by_cases hc2 : d * m₂ ≤ N
        · rw [if_pos hc1, if_pos hc2, if_pos ⟨hc1, hc2⟩]
          push_cast
          calc (g m₁ : ℂ) * e ((d : ℝ) * (m₁ : ℝ) * α)
                * ((g m₂ : ℂ) * e (-((d : ℝ) * (m₂ : ℝ) * α)))
              = ((g m₁ : ℂ) * g m₂)
                * (e ((d : ℝ) * (m₁ : ℝ) * α) * e (-((d : ℝ) * (m₂ : ℝ) * α))) := by ring
            _ = ((g m₁ : ℂ) * g m₂) * e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by rw [h1]
        · have hcon : ¬ (d * m₁ ≤ N ∧ d * m₂ ≤ N) := fun h => hc2 h.2
          rw [if_pos hc1, if_neg hc2, if_neg hcon]
          push_cast
          ring
      · have hcon : ¬ (d * m₁ ≤ N ∧ d * m₂ ≤ N) := fun h => hc1 h.1
        rw [if_neg hc1, if_neg hcon]
        push_cast
        ring
    rw [Finset.sum_congr rfl hpt]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m₁ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m₂ _
    rw [Finset.mul_sum, Finset.sum_filter]
  -- assemble: real parts + triangle
  have hre : ∑ d ∈ Finset.Ico A B,
      ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      = (∑ d ∈ Finset.Ico A B,
          ((∑ m ∈ Finset.Ioc V (N / A),
              ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)) *
            (starRingEnd ℂ) (∑ m ∈ Finset.Ioc V (N / A),
              ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← hext d hd, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact (Complex.ofReal_re _).symm
  rw [hre, hid]
  calc (∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
        ((g m₁ * g m₂ : ℝ) : ℂ) *
          ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
            e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))).re
      ≤ ‖∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          ((g m₁ * g m₂ : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := Complex.re_le_norm _
    _ ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ‖∑ m₂ ∈ Finset.Ioc V (N / A),
          ((g m₁ * g m₂ : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := norm_sum_le _ _
    _ ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          ‖((g m₁ * g m₂ : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        Finset.sum_le_sum (fun m₁ _ => norm_sum_le _ _)
    _ = ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          |g m₁| * |g m₂| *
            ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := by
        apply Finset.sum_congr rfl; intro m₁ _
        apply Finset.sum_congr rfl; intro m₂ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]

/-- **The S₄-block second moment**: the full hyperbola-restricted second moment through
    the workhorse chain. -/
lemma S4_block_second_moment (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (g : ℕ → ℝ) (G : ℝ) (hg0 : ∀ m, 0 ≤ g m) (hgG : ∀ m, g m ≤ G)
    (N A B V : ℕ) (hA : 0 < A) :
    ∑ d ∈ Finset.Ico A B,
      ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ G ^ 2 * (((N / A : ℕ) : ℝ) + 1) *
          (((B - A : ℕ) : ℝ) + 2 * ((((N / A : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))) := by
  have hG0 : 0 ≤ G := le_trans (hg0 0) (hgG 0)
  set F : ℤ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((B - A : ℕ) : ℝ)
     else min ((B - A : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hF
  have hF0 : ∀ h, 0 ≤ F h := by
    intro h
    rw [hF]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  -- per-pair bound
  have hpair : ∀ m₁ ∈ Finset.Ioc V (N / A), ∀ m₂ ∈ Finset.Ioc V (N / A),
      |g m₁| * |g m₂| *
        ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
          e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖
      ≤ G * G * F ((m₁ : ℤ) - m₂) := by
    intro m₁ hm₁ m₂ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    have hcapF : ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
        e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ ≤ F ((m₁ : ℤ) - m₂) := by
      have h1 := filtered_exp_sum_cap (((m₁ : ℝ) - m₂) * α) N A B m₁ m₂
        (by omega) (by omega)
      have hcast : ((((m₁ : ℤ) - m₂) : ℤ) : ℝ) * α = ((m₁ : ℝ) - m₂) * α := by
        push_cast
        ring
      rw [hF]
      dsimp only
      rw [hcast]
      exact h1
    have hg1 : |g m₁| ≤ G := by rw [abs_of_nonneg (hg0 m₁)]; exact hgG m₁
    have hg2 : |g m₂| ≤ G := by rw [abs_of_nonneg (hg0 m₂)]; exact hgG m₂
    apply mul_le_mul _ hcapF (norm_nonneg _) (by positivity)
    exact mul_le_mul hg1 hg2 (abs_nonneg _) hG0
  -- extend the double sum to squares of ranges
  have hIoc_sub : Finset.Ioc V (N / A) ⊆ Finset.range (N / A + 1) := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    simp only [Finset.mem_range]
    omega
  calc ∑ d ∈ Finset.Ico A B,
      ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          |g m₁| * |g m₂| *
            ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        hyperbola_second_moment_expand g α N A B V hA
    _ ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          G * G * F ((m₁ : ℤ) - m₂) := by
        apply Finset.sum_le_sum
        intro m₁ hm₁
        exact Finset.sum_le_sum (fun m₂ hm₂ => hpair m₁ hm₁ m₂ hm₂)
    _ ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.range (N / A + 1),
          G * G * F ((m₁ : ℤ) - m₂) := by
        apply Finset.sum_le_sum
        intro m₁ _
        apply Finset.sum_le_sum_of_subset_of_nonneg hIoc_sub
        intro m₂ _ _
        positivity
    _ ≤ ∑ m₁ ∈ Finset.range (N / A + 1), ∑ m₂ ∈ Finset.range (N / A + 1),
          G * G * F ((m₁ : ℤ) - m₂) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hIoc_sub
        intro m₁ _ _
        exact Finset.sum_nonneg (fun m₂ _ => by positivity)
    _ = G * G * ∑ m₁ ∈ Finset.range (N / A + 1), ∑ m₂ ∈ Finset.range (N / A + 1),
          F ((m₁ : ℤ) - m₂) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m₁ _
        rw [Finset.mul_sum]
    _ ≤ G * G * (((N / A + 1 : ℕ) : ℝ) *
          ∑ h ∈ Finset.Icc (-(N / A + 1 : ℕ) + 1 : ℤ) ((N / A + 1 : ℕ) - 1 : ℤ), F h) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast diff_count_le F hF0 (N / A + 1)
    _ ≤ G * G * (((N / A + 1 : ℕ) : ℝ) *
          (((B - A : ℕ) : ℝ) + 2 * ((((N / A + 1 - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h5 := cap_symmetric_sum_le a q hq ha α hα ((B - A : ℕ) : ℝ)
          (by positivity) (N / A + 1)
        rw [hF]
        exact_mod_cast h5
    _ = G ^ 2 * (((N / A : ℕ) : ℝ) + 1) *
          (((B - A : ℕ) : ℝ) + 2 * ((((N / A : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))) := by
        rw [Nat.add_sub_cancel]
        push_cast
        ring

/-- **The variance quartic step**: on any interval where `‖S‖ ≤ C`, the fourth moment is
    controlled by `C²` times the second moment. (The per-arc core of
    `∫_𝔪 |S|⁴ ≤ (sup_𝔪|S|)²·∫|S|²`; the arc decomposition supplies the intervals.) -/
lemma quartic_le_sq_mul_sq (S : ℝ → ℂ) (C : ℝ) (a b : ℝ) (hab : a ≤ b)
    (hbound : ∀ α ∈ Set.Icc a b, ‖S α‖ ≤ C)
    (hint2 : IntervalIntegrable (fun α => ‖S α‖ ^ 2) MeasureTheory.volume a b)
    (hint4 : IntervalIntegrable (fun α => ‖S α‖ ^ 4) MeasureTheory.volume a b) :
    ∫ α in a..b, ‖S α‖ ^ 4 ≤ C ^ 2 * ∫ α in a..b, ‖S α‖ ^ 2 := by
  have hC0 : 0 ≤ C := by
    rcases eq_or_lt_of_le hab with h | h
    · -- degenerate interval: both integrals vanish; C ≥ 0 not needed, handle below
      exact le_trans (norm_nonneg (S a)) (hbound a (by constructor <;> simp [h.le]))
    · exact le_trans (norm_nonneg (S a)) (hbound a ⟨le_refl a, hab⟩)
  have hpt : ∀ α ∈ Set.Icc a b, ‖S α‖ ^ 4 ≤ C ^ 2 * ‖S α‖ ^ 2 := by
    intro α hα
    have h1 : ‖S α‖ ≤ C := hbound α hα
    have h2 : ‖S α‖ ^ 2 ≤ C ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) h1
    calc ‖S α‖ ^ 4 = ‖S α‖ ^ 2 * ‖S α‖ ^ 2 := by ring
      _ ≤ C ^ 2 * ‖S α‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
  calc ∫ α in a..b, ‖S α‖ ^ 4
      ≤ ∫ α in a..b, C ^ 2 * ‖S α‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on hab hint4 (hint2.const_mul (C ^ 2))
        exact hpt
    _ = C ^ 2 * ∫ α in a..b, ‖S α‖ ^ 2 := intervalIntegral.integral_const_mul _ _

section VaughanDecomposition

open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Vaughan's identity (self-contained copy of `Vaughan.vaughan_identity` from
    `VaughanIdentity.lean`, re-verified here so this file stays standalone). -/
lemma vaughan_identity (a b : ArithmeticFunction ℝ) :
    Λ = a * ArithmeticFunction.log - a * b * (ζ : ArithmeticFunction ℝ) + b
      + ((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ) := by
  have hlog : (ζ : ArithmeticFunction ℝ) * Λ = ArithmeticFunction.log := zeta_mul_vonMangoldt
  have hμζ : ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)) = 1 :=
    coe_moebius_mul_coe_zeta
  rw [← hlog]
  linear_combination (b - Λ) * hμζ

/-- **The Vaughan sum decomposition**: `∑_{n≤N} Λ(n)·w(n) = S₁ − S₂ + S₃ + S₄`,
    each `Sᵢ` a convolution sum ready for the hyperbola unfolding
    (`sum_Ioc_mul_weight`) and then Type I / Abel / Type II. -/
lemma vaughan_sum_decomposition (a b : ArithmeticFunction ℝ) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * w n
      = (∑ n ∈ Finset.Ioc 0 N, (((a * ArithmeticFunction.log) n : ℝ) : ℂ) * w n)
        - (∑ n ∈ Finset.Ioc 0 N, (((a * b * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * w n)
        + (∑ n ∈ Finset.Ioc 0 N, ((b n : ℝ) : ℂ) * w n)
        + (∑ n ∈ Finset.Ioc 0 N,
            (((((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
              * w n) := by
  have hpt : ∀ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * w n
      = (((a * ArithmeticFunction.log) n : ℝ) : ℂ) * w n
        - (((a * b * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * w n
        + ((b n : ℝ) : ℂ) * w n
        + (((((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ)
            * w n := by
    intro n _
    have h1 : (Λ : ArithmeticFunction ℝ) n
        = (a * ArithmeticFunction.log) n - (a * b * (ζ : ArithmeticFunction ℝ)) n + b n
          + (((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ)) n := by
      conv_lhs => rw [vaughan_identity a b]
      have e1 : (a * ArithmeticFunction.log - a * b * (ζ : ArithmeticFunction ℝ) + b
          + ((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ))
          = ((a * ArithmeticFunction.log + -(a * b * (ζ : ArithmeticFunction ℝ))) + b)
            + ((μ : ArithmeticFunction ℝ) - a) * (Λ - b) * (ζ : ArithmeticFunction ℝ) := by
        ring
      rw [e1, ArithmeticFunction.add_apply, ArithmeticFunction.add_apply,
        ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
      ring
    rw [h1]
    push_cast
    ring
  rw [Finset.sum_congr rfl hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Truncation of an arithmetic function to `n ≤ U` (the Vaughan `a`, `b` pieces). -/
noncomputable def truncate (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by
    split
    · exact f.map_zero
    · rfl⟩

@[simp] lemma truncate_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    truncate f U n = if n ≤ U then f n else 0 := rfl

/-- The truncated Möbius is sup-bounded by 1. -/
lemma abs_truncate_moebius_le_one (U n : ℕ) :
    |truncate (μ : ArithmeticFunction ℝ) U n| ≤ 1 := by
  rw [truncate_apply]
  split
  · have h := abs_moebius_le_one (n := n)
    rw [ArithmeticFunction.intCoe_apply]
    calc |((μ n : ℤ) : ℝ)| = ((|μ n| : ℤ) : ℝ) := by rw [Int.cast_abs]
      _ ≤ 1 := by exact_mod_cast h
  · simp

lemma truncate_vonMangoldt_nonneg (V n : ℕ) : 0 ≤ truncate Λ V n := by
  rw [truncate_apply]
  split
  · exact vonMangoldt_nonneg
  · exact le_refl 0

lemma truncate_vonMangoldt_le (V n : ℕ) : truncate Λ V n ≤ Λ n := by
  rw [truncate_apply]
  split
  · exact le_refl _
  · exact vonMangoldt_nonneg

/-- **The S₂ coefficient bound**: the Vaughan `a·b` coefficients are log-bounded,
    `|(a∗b)(t)| ≤ log t` (via `|μ| ≤ 1`, `0 ≤ Λ_trunc ≤ Λ`, and `∑_{d∣t} Λ(d) = log t`). -/
lemma abs_truncate_mul_le_log (U V t : ℕ) :
    |(truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V) t| ≤ Real.log t := by
  rw [ArithmeticFunction.mul_apply]
  calc |∑ x ∈ t.divisorsAntidiagonal,
        truncate (μ : ArithmeticFunction ℝ) U x.1 * truncate Λ V x.2|
      ≤ ∑ x ∈ t.divisorsAntidiagonal,
        |truncate (μ : ArithmeticFunction ℝ) U x.1 * truncate Λ V x.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ t.divisorsAntidiagonal, Λ x.2 := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul]
        have h1 := abs_truncate_moebius_le_one U x.1
        have h2 : |truncate Λ V x.2| = truncate Λ V x.2 :=
          abs_of_nonneg (truncate_vonMangoldt_nonneg V x.2)
        calc |truncate (μ : ArithmeticFunction ℝ) U x.1| * |truncate Λ V x.2|
            ≤ 1 * |truncate Λ V x.2| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = truncate Λ V x.2 := by rw [one_mul, h2]
          _ ≤ Λ x.2 := truncate_vonMangoldt_le V x.2
    _ = ∑ d ∈ t.divisors, Λ d := Nat.sum_divisorsAntidiagonal' (f := fun _ e => Λ e)
    _ = Real.log t := vonMangoldt_sum

/-- **The regrouping**: `∑_{n≤N} (f∗g)(n)w(n) = ∑_{d≤N} f(d)·∑_{m≤N/d} g(m)w(dm)` —
    each Vaughan piece becomes per-`d` inner sums in exp-sum shape
    (with `w n = e(nα)` the inner sum is `∑_{m≤N/d} g(m)e(m·(dα))`). -/
lemma sum_Ioc_mul_weight_eq_sum_sum (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℂ) * w n
      = ∑ d ∈ Finset.Ioc 0 N, (f d : ℂ) *
          ∑ m ∈ Finset.Ioc 0 (N / d), (g m : ℂ) * w (d * m) := by
  rw [sum_Ioc_mul_weight, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_Ioc] at hd
  have hset : (Finset.Ioc 0 N).filter (fun m => d * m ≤ N) = Finset.Ioc 0 (N / d) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      refine ⟨h1, ?_⟩
      rw [Nat.le_div_iff_mul_le hd.1]
      rwa [mul_comm]
    · rintro ⟨h1, h2⟩
      have h3 : m * d ≤ N := (Nat.le_div_iff_mul_le hd.1).mp h2
      refine ⟨⟨h1, ?_⟩, by rwa [mul_comm] at h3⟩
      calc m ≤ N / d := h2
        _ ≤ N := Nat.div_le_self N d
  calc ∑ m ∈ Finset.Ioc 0 N,
        (if d * m ≤ N then (f d : ℂ) * (g m : ℂ) * w (d * m) else 0)
      = ∑ m ∈ (Finset.Ioc 0 N).filter (fun m => d * m ≤ N),
          (f d : ℂ) * (g m : ℂ) * w (d * m) := (Finset.sum_filter _ _).symm
    _ = ∑ m ∈ Finset.Ioc 0 (N / d), (f d : ℂ) * (g m : ℂ) * w (d * m) := by rw [hset]
    _ = (f d : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / d), (g m : ℂ) * w (d * m) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by ring)

/-- **The dyadic N/h-cap workhorse (Vaughan Lemma 2.2 final form)**. -/
lemma dyadic_cap_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H : ℕ) :
    ∑ h ∈ Finset.Ioc 0 H,
      (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
       else min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
      ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
        + 32 * H * (1 + Real.log (2 * q)) + 4 * N := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 * q) := by
    have : (0 : ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
    linarith
  set L : ℝ := 1 + Real.log (2 * q) with hLdef
  rcases Nat.eq_zero_or_pos H with hH0 | hH1
  · subst hH0
    simp only [Finset.Ioc_self, Finset.sum_empty]
    push_cast
    have h2 : (0 : ℝ) ≤ 4 * q * L := mul_nonneg (by positivity) hL0
    have h4 : (0 : ℝ) ≤ 8 * N / q := by positivity
    have h6 : (0 : ℝ) ≤ ((Nat.log 2 0 : ℝ) + 1) * (8 * N / q + 4 * q * L) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  set T : ℕ := Nat.log 2 H + 1 with hT
  have h2T : (2 : ℕ) ^ T ≤ 2 * H := by
    rw [hT, pow_succ, mul_comm]
    have := Nat.pow_log_le_self 2 (by omega : H ≠ 0)
    omega
  set w : ℕ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
     else min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hw
  set wt : ℕ → ℕ → ℝ := fun t h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / 2 ^ t : ℕ) : ℝ)
     else min ((N / 2 ^ t : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hwt
  have hwt0 : ∀ t h, 0 ≤ wt t h := by
    intro t h
    rw [hwt]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  have hww : ∀ h ∈ Finset.Ioc 0 H, w h ≤ wt (Nat.log 2 h) h := by
    intro h hh
    simp only [Finset.mem_Ioc] at hh
    have hple : 2 ^ Nat.log 2 h ≤ h := Nat.pow_log_le_self 2 (by omega)
    have hdivle : (N / h : ℕ) ≤ N / 2 ^ Nat.log 2 h := Nat.div_le_div_left hple (by positivity)
    have hcast : ((N / h : ℕ) : ℝ) ≤ ((N / 2 ^ Nat.log 2 h : ℕ) : ℝ) := by exact_mod_cast hdivle
    rw [hw, hwt]
    dsimp only
    split
    · exact hcast
    · exact min_le_min hcast le_rfl
  have hsum1 : ∑ h ∈ Finset.Ioc 0 H, w h
      ≤ ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h := by
    have hcover : Finset.Ioc 0 H ⊆
        (Finset.range T).biUnion (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
      intro h hh
      simp only [Finset.mem_Ioc] at hh
      rw [Finset.mem_biUnion]
      refine ⟨Nat.log 2 h, ?_, ?_⟩
      · rw [Finset.mem_range, hT]
        have hlog : Nat.log 2 h ≤ Nat.log 2 H := Nat.log_mono_right hh.2
        omega
      · rw [Finset.mem_Ico]
        constructor
        · exact Nat.pow_log_le_self 2 (by omega)
        · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) h
          rw [pow_succ] at this
          omega
    have hdisj : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint
        (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
      intro t₁ _ t₂ _ hne
      apply Finset.disjoint_left.mpr
      intro h h1 h2
      simp only [Finset.mem_Ico] at h1 h2
      rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
      · have : (2 : ℕ) ^ (t₁ + 1) ≤ 2 ^ t₂ := Nat.pow_le_pow_right (by norm_num) hlt
        rw [pow_succ] at this
        omega
      · have hlt2 : t₂ < t₁ := lt_of_le_of_ne hge (Ne.symm hne)
        have : (2 : ℕ) ^ (t₂ + 1) ≤ 2 ^ t₁ := Nat.pow_le_pow_right (by norm_num) hlt2
        rw [pow_succ] at this
        omega
    calc ∑ h ∈ Finset.Ioc 0 H, w h
        ≤ ∑ h ∈ Finset.Ioc 0 H, wt (Nat.log 2 h) h := Finset.sum_le_sum hww
      _ ≤ ∑ h ∈ (Finset.range T).biUnion (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)),
            wt (Nat.log 2 h) h :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hwt0 _ h)
      _ = ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
            wt (Nat.log 2 h) h := Finset.sum_biUnion hdisj
      _ = ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro h hh
          simp only [Finset.mem_Ico] at hh
          have hlog : Nat.log 2 h = t := by
            apply Nat.log_eq_of_pow_le_of_lt_pow hh.1
            rw [pow_succ]
            omega
          rw [hlog]
  have hblock : ∀ t : ℕ, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h
      ≤ 8 * N / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L := by
    intro t
    have happ := range_min_sum_le a q hq ha α hα ((N / 2 ^ t : ℕ) : ℝ) (by positivity)
      (2 ^ t) (2 ^ t)
    have hq2pos : (0 : ℝ) < ((q / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q / 2)
    have hcast1 : (((2 ^ t) / (q / 2) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ t * (4 / q) + 1 := by
      have h3 : (q : ℝ) ≤ 4 * ((q / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : q ≤ 4 * (q / 2))
      have hinv : 1 / ((q / 2 : ℕ) : ℝ) ≤ 4 / (q : ℝ) := by
        rw [div_le_div_iff₀ hq2pos hqR]
        linarith
      have h1 : (((2 ^ t) / (q / 2) : ℕ) : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) / ((q / 2 : ℕ) : ℝ) :=
        Nat.cast_div_le
      have h5 : ((2 ^ t : ℕ) : ℝ) / ((q / 2 : ℕ) : ℝ)
          = ((2 ^ t : ℕ) : ℝ) * (1 / ((q / 2 : ℕ) : ℝ)) := by ring
      have h6 : ((2 ^ t : ℕ) : ℝ) * (1 / ((q / 2 : ℕ) : ℝ)) ≤ ((2 ^ t : ℕ) : ℝ) * (4 / q) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      have h7 : (((2 ^ t) / (q / 2) + 1 : ℕ) : ℝ) = (((2 ^ t) / (q / 2) : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      have h8 : ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ t := by push_cast; ring
      rw [h7]
      rw [h8] at h5 h6
      rw [h8] at h1
      linarith [h1, h5, h6]
    have hcast2 : ((N / 2 ^ t : ℕ) : ℝ) ≤ (N : ℝ) / (2 : ℝ) ^ t := by
      have h9 := Nat.cast_div_le (m := N) (n := 2 ^ t) (α := ℝ)
      push_cast at h9
      exact h9
    have hnn2 : (0 : ℝ) ≤ 2 * ((N / 2 ^ t : ℕ) : ℝ) + 4 * q * L := by
      have : (0 : ℝ) ≤ 4 * q * L := mul_nonneg (by positivity) hL0
      positivity
    have h2t : ((2 : ℝ) ^ t) ≠ 0 := by positivity
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
    calc ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h
        ≤ (((2 ^ t) / (q / 2) + 1 : ℕ) : ℝ) * (2 * ((N / 2 ^ t : ℕ) : ℝ) + 4 * q * L) := happ
      _ ≤ ((2 : ℝ) ^ t * (4 / q) + 1) * (2 * ((N : ℝ) / (2 : ℝ) ^ t) + 4 * q * L) := by
          apply mul_le_mul hcast1 _ hnn2 (by positivity)
          have h10 : 2 * ((N / 2 ^ t : ℕ) : ℝ) ≤ 2 * ((N : ℝ) / (2 : ℝ) ^ t) := by linarith
          linarith
      _ = 8 * N / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L := by
          field_simp
          ring
  have hgeo1 : ∑ t ∈ Finset.range T, (2 : ℝ) ^ t ≤ (2 : ℝ) ^ T := by
    have heq : ((2 : ℝ) ^ T - 1) / (2 - 1) = (2 : ℝ) ^ T - 1 := by norm_num
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1), heq]
    have : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
    linarith
  have hgeo2 : ∑ t ∈ Finset.range T, (1 / (2 : ℝ)) ^ t ≤ 2 := by
    have heq : ((1 / 2 : ℝ) ^ T - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ T) := by ring
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1), heq]
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ T := by positivity
    linarith
  have hsum2 : ∑ t ∈ Finset.range T,
      (8 * (N : ℝ) / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L)
      ≤ (T : ℝ) * (8 * N / q + 4 * q * L) + 16 * L * (2 : ℝ) ^ T + 4 * N := by
    have hsplit : ∀ t ∈ Finset.range T,
        8 * (N : ℝ) / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L
        = (8 * (N : ℝ) / q + 4 * q * L)
          + (16 * L * (2 : ℝ) ^ t + 2 * N * (1 / (2 : ℝ)) ^ t) := by
      intro t _
      have hp : (1 / (2 : ℝ)) ^ t = 1 / (2 : ℝ) ^ t := by
        rw [div_pow, one_pow]
      rw [hp]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      nsmul_eq_mul]
    have h1 : 16 * L * ∑ t ∈ Finset.range T, (2 : ℝ) ^ t ≤ 16 * L * (2 : ℝ) ^ T :=
      mul_le_mul_of_nonneg_left hgeo1 (by linarith)
    have h2 : 2 * (N : ℝ) * ∑ t ∈ Finset.range T, (1 / (2 : ℝ)) ^ t ≤ 2 * N * 2 :=
      mul_le_mul_of_nonneg_left hgeo2 (by positivity)
    linarith
  have h2TR : (2 : ℝ) ^ T ≤ 2 * H := by exact_mod_cast h2T
  calc ∑ h ∈ Finset.Ioc 0 H, w h
      ≤ ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t), wt t h := hsum1
    _ ≤ ∑ t ∈ Finset.range T,
        (8 * (N : ℝ) / q + 16 * L * (2 : ℝ) ^ t + 2 * N / (2 : ℝ) ^ t + 4 * q * L) :=
        Finset.sum_le_sum (fun t _ => hblock t)
    _ ≤ (T : ℝ) * (8 * N / q + 4 * q * L) + 16 * L * (2 : ℝ) ^ T + 4 * N := hsum2
    _ ≤ (T : ℝ) * (8 * N / q + 4 * q * L) + 16 * L * (2 * H) + 4 * N := by
        have h11 : 16 * L * (2 : ℝ) ^ T ≤ 16 * L * (2 * H) :=
          mul_le_mul_of_nonneg_left h2TR (by linarith)
        linarith
    _ = ((Nat.log 2 H + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
        + 32 * H * (1 + Real.log (2 * q)) + 4 * N := by
        rw [hT, hLdef]
        push_cast
        ring

/-- The S₂ support bound: the convolution of truncations vanishes past `U·V`. -/
lemma truncate_mul_eq_zero_of_gt (f g : ArithmeticFunction ℝ) (U V t : ℕ) (ht : U * V < t) :
    (truncate f U * truncate g V) t = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  by_cases h1 : x.1 ≤ U
  · have h2 : ¬ x.2 ≤ V := by
      intro h2
      have hle : x.1 * x.2 ≤ U * V := Nat.mul_le_mul h1 h2
      obtain ⟨P, hP⟩ : ∃ P, P = x.1 * x.2 := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = U * V := ⟨_, rfl⟩
      rw [← hP] at hle
      rw [← hP] at hx
      rw [← hQ] at hle ht
      omega
    rw [truncate_apply, truncate_apply, if_neg h2, mul_zero]
  · rw [truncate_apply, if_neg h1, zero_mul]

/-- The S₃ trivial bound: `∑_{n≤V} Λ(n) ≤ V·log V`. -/
lemma sum_vonMangoldt_le (V : ℕ) :
    ∑ n ∈ Finset.Ioc 0 V, Λ n ≤ (V : ℝ) * Real.log V := by
  calc ∑ n ∈ Finset.Ioc 0 V, Λ n
      ≤ ∑ _n ∈ Finset.Ioc 0 V, Real.log V := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        calc Λ n ≤ Real.log n := vonMangoldt_le_log
          _ ≤ Real.log V := by
            apply Real.log_le_log (by exact_mod_cast hn.1)
            exact_mod_cast hn.2
    _ = (V : ℝ) * Real.log V := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        norm_num

/-- ζ collapses on positive ranges: `∑_{0<m≤M} ζ(m)·z(m) = ∑_{0<m≤M} z(m)`. -/
lemma sum_Ioc_zeta_mul (z : ℕ → ℂ) (M : ℕ) :
    ∑ m ∈ Finset.Ioc 0 M, (((ζ : ArithmeticFunction ℝ) m : ℝ) : ℂ) * z m
      = ∑ m ∈ Finset.Ioc 0 M, z m := by
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_Ioc] at hm
  have h1 : ((ζ : ArithmeticFunction ℝ) m : ℝ) = 1 := by
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      if_neg (by omega : ¬ m = 0)]
    norm_num
  rw [h1]
  norm_num

/-- The Ioc exp-sum cap: `‖∑_{0<m≤M} e(mβ)‖ ≤ [β∈ℤ ? M : min(M, 1/(2‖β‖))]`. -/
lemma exp_sum_Ioc_min_bound (β : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.Ioc 0 M, e (m * β)‖
      ≤ (if β - round β = 0 then (M : ℝ)
         else min (M : ℝ) (1 / (2 * |β - round β|))) := by
  have hset : Finset.Ioc 0 M = Finset.Ico 1 (M + 1) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset]
  have := exp_sum_Ico_min_bound β 1 (M + 1)
  have hM : (M + 1 - 1 : ℕ) = M := by omega
  rwa [hM] at this

/-- **Near-integer points are large** (tight min-sum keystone): if `hα` is within
    `1/(2q)` of an integer then `2h > q`. Contrapositive: for `0 < h ≤ q/2`,
    `q ∤ ha` forces `‖ha/q‖ ≥ 1/q`, and the `≤ 1/(2q)` perturbation from
    `|α−a/q| ≤ 1/q²` leaves `‖hα‖ ≥ 1/(2q)`. -/
lemma nearint_h_lower (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (h : ℕ) (hh0 : 0 < h) (hhq : 2 * h ≤ q) :
    1 / (2 * (q : ℝ)) ≤ |(h : ℝ) * α - round ((h : ℝ) * α)| := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  -- q ∤ h*a (in ℕ, via coprimality)
  have hnd : ¬ (q : ℤ) ∣ ((h * a : ℕ) : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro hdvd
    have hqh : q ∣ h := (ha.symm).dvd_of_dvd_mul_right hdvd
    exact absurd (Nat.le_of_dvd hh0 hqh) (by omega)
  -- ‖ha/q‖ ≥ 1/q
  have hbase : 1 / (q : ℝ) ≤ |((h * a : ℕ) : ℝ) / q - round (((h * a : ℕ) : ℝ) / q)| :=
    dist_int_div_ge ((h * a : ℕ) : ℤ) q (by omega) hnd
  have hcast : (((h * a : ℕ) : ℝ) / q) = (h : ℝ) * ((a : ℝ) / q) := by
    push_cast
    ring
  rw [hcast] at hbase
  -- perturbation: |h(a/q) − hα| ≤ h/q² ≤ 1/(2q)
  have hpert : |(h : ℝ) * ((a : ℝ) / q) - (h : ℝ) * α| ≤ 1 / (2 * (q : ℝ)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (h:ℝ))]
    rw [abs_sub_comm]
    have h1 : (h : ℝ) * |α - (a : ℝ) / q| ≤ (h : ℝ) * (1 / (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hα (by positivity)
    have h2 : (h : ℝ) * (1 / (q : ℝ) ^ 2) ≤ 1 / (2 * (q : ℝ)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : (2 : ℝ) * h ≤ q := by exact_mod_cast hhq
      nlinarith [hqR]
    linarith
  -- combine via 1-Lipschitz dist: ‖h(a/q)‖ ≤ |h(a/q) − hα| + ‖hα‖
  have hlip := dist_round_le ((h : ℝ) * ((a : ℝ) / q)) ((h : ℝ) * α)
  have hbridge : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) - 1 / (2 * (q : ℝ)) := by
    field_simp
    ring
  linarith [hbase, hpert, hlip, hbridge]

/-- Distance to ℤ is subadditive under subtraction. -/
lemma dist_round_sub_le (x y : ℝ) :
    |(x - y) - round (x - y)| ≤ |x - round x| + |y - round y| := by
  calc |(x - y) - round (x - y)|
      ≤ |(x - y) - ((round x : ℤ) - (round y : ℤ) : ℤ)| :=
        round_le (x - y) ((round x : ℤ) - (round y : ℤ))
    _ = |(x - round x) + (-(y - round y))| := by push_cast; ring_nf
    _ ≤ |x - round x| + |-(y - round y)| := abs_add_le _ _
    _ = |x - round x| + |y - round y| := by rw [abs_neg]

/-- **Resonant points are `q/2`-separated**: two distinct near-integer (`< 1/(4q)`)
    points `h' < h` differ by more than `q/2`, so `⌊2h/q⌋ ≠ ⌊2h'/q⌋`. -/
lemma resonant_spaced (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (h h' : ℕ) (hh'0 : 0 < h') (hlt : h' < h)
    (hres : |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ)))
    (hres' : |(h' : ℝ) * α - round ((h' : ℝ) * α)| < 1 / (4 * (q : ℝ))) :
    q < 2 * (h - h') := by
  by_contra hcon
  push_neg at hcon
  set d : ℕ := h - h' with hd
  have hd0 : 0 < d := by omega
  have hdq : 2 * d ≤ q := hcon
  have hdcast : (d : ℝ) * α = (h : ℝ) * α - (h' : ℝ) * α := by
    rw [hd, Nat.cast_sub hlt.le]
    ring
  have hsub := dist_round_sub_le ((h : ℝ) * α) ((h' : ℝ) * α)
  rw [← hdcast] at hsub
  have hlow := nearint_h_lower a q hq ha α hα d hd0 hdq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hbridge : 1 / (2 * (q : ℝ)) = 1 / (4 * (q : ℝ)) + 1 / (4 * (q : ℝ)) := by
    field_simp
    ring
  linarith [hlow, hsub, hres, hres', hbridge]

/-- **The resonant floor sum has no bare `N`** (the key to killing the spurious `4N`):
    the near-integer `h` (bin `φ h = 2h/q ≥ 1`, `φ` injective by `resonant_spaced`)
    satisfy `⌊N/h⌋ ≤ 2N/(q·φ h)`, so their sum telescopes to `(2N/q)·harmonic`. -/
lemma resonant_floor_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H : ℕ) :
    ∑ h ∈ (Finset.Ioc 0 H).filter
        (fun h : ℕ => |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ))),
        ((N / h : ℕ) : ℝ)
      ≤ (2 * (N : ℝ) / q) * (1 + Real.log H) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  set R := (Finset.Ioc 0 H).filter
      (fun h : ℕ => |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ))) with hR
  set φ : ℕ → ℕ := fun h => 2 * h / q with hφ
  have hφe : ∀ x : ℕ, φ x = 2 * x / q := fun _ => rfl
  -- membership + resonance facts
  have hmem : ∀ h ∈ R, 0 < h ∧ h ≤ H ∧
      |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ)) := by
    intro h hh
    rw [hR, Finset.mem_filter, Finset.mem_Ioc] at hh
    exact ⟨hh.1.1, hh.1.2, hh.2⟩
  have hbig : ∀ h ∈ R, q < 2 * h := by
    intro h hh
    obtain ⟨hh0, _, hres⟩ := hmem h hh
    by_contra hc
    push_neg at hc
    have hlow := nearint_h_lower a q hq ha α hα h hh0 hc
    have : (1 : ℝ) / (2 * q) ≤ 1 / (4 * q) := le_trans hlow hres.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
    linarith
  have hφpos : ∀ h ∈ R, 1 ≤ φ h := by
    intro h hh
    have hh2 := hbig h hh
    rw [hφe]
    exact (Nat.one_le_div_iff (show 0 < q by omega)).mpr (by omega)
  -- φ is injective on R (resonant_spaced ⟹ bins strictly increase)
  have hinj : Set.InjOn φ (R : Set ℕ) := by
    intro h₁ hh₁ h₂ hh₂ hfe
    rcases lt_trichotomy h₁ h₂ with hlt | heq | hgt
    · exfalso
      obtain ⟨hh₁0, _, hr₁⟩ := hmem h₁ (Finset.mem_coe.mp hh₁)
      obtain ⟨_, _, hr₂⟩ := hmem h₂ (Finset.mem_coe.mp hh₂)
      have hsp := resonant_spaced a q hq ha α hα h₂ h₁ hh₁0 hlt hr₂ hr₁
      have hge : 2 * h₁ + q ≤ 2 * h₂ := by omega
      have hk : 2 * h₁ / q + 1 = (2 * h₁ + q) / q :=
        (Nat.add_div_right (2 * h₁) (show 0 < q by omega)).symm
      have hle : (2 * h₁ + q) / q ≤ 2 * h₂ / q := Nat.div_le_div_right hge
      have hbin : φ h₁ < φ h₂ := by rw [hφe, hφe]; omega
      omega
    · exact heq
    · exfalso
      obtain ⟨_, _, hr₁⟩ := hmem h₁ (Finset.mem_coe.mp hh₁)
      obtain ⟨hh₂0, _, hr₂⟩ := hmem h₂ (Finset.mem_coe.mp hh₂)
      have hsp := resonant_spaced a q hq ha α hα h₁ h₂ hh₂0 hgt hr₁ hr₂
      have hge : 2 * h₂ + q ≤ 2 * h₁ := by omega
      have hk : 2 * h₂ / q + 1 = (2 * h₂ + q) / q :=
        (Nat.add_div_right (2 * h₂) (show 0 < q by omega)).symm
      have hle : (2 * h₂ + q) / q ≤ 2 * h₁ / q := Nat.div_le_div_right hge
      have hbin : φ h₂ < φ h₁ := by rw [hφe, hφe]; omega
      omega
  -- termwise: ⌊N/h⌋ ≤ 2N/(q·φ h)
  have hterm : ∀ h ∈ R, ((N / h : ℕ) : ℝ) ≤ (2 * (N : ℝ) / q) * (1 / (φ h : ℝ)) := by
    intro h hh
    obtain ⟨hh0, _, _⟩ := hmem h hh
    have hφ1 := hφpos h hh
    have hφ0 : (0 : ℝ) < (φ h : ℝ) := by exact_mod_cast hφ1
    have hqφ : (q : ℝ) * (φ h : ℝ) ≤ 2 * (h : ℝ) := by
      have := Nat.div_mul_le_self (2 * h) q
      rw [hφe]
      have hcast : ((2 * h / q : ℕ) * q : ℕ) ≤ 2 * h := this
      have : ((2 * h / q : ℕ) : ℝ) * (q : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hcast
      nlinarith [this]
    have hNh : ((N / h : ℕ) : ℝ) ≤ (N : ℝ) / (h : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hh0)]
      have := Nat.div_mul_le_self N h
      have : ((N / h : ℕ) * h : ℕ) ≤ N := this
      exact_mod_cast this
    have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh0
    have hNn : (0:ℝ) ≤ (N:ℝ) := by positivity
    have hbound : (N : ℝ) / (h : ℝ) ≤ (2 * (N : ℝ) / q) * (1 / (φ h : ℝ)) := by
      rw [show (2 * (N : ℝ) / q) * (1 / (φ h : ℝ)) = (2 * (N:ℝ)) / (q * (φ h : ℝ)) from by
        field_simp, div_le_div_iff₀ hhpos (by positivity)]
      nlinarith [hqφ, hNn, hhpos, hqR, hφ0]
    linarith
  calc ∑ h ∈ R, ((N / h : ℕ) : ℝ)
      ≤ ∑ h ∈ R, (2 * (N : ℝ) / q) * (1 / (φ h : ℝ)) := Finset.sum_le_sum hterm
    _ = (2 * (N : ℝ) / q) * ∑ h ∈ R, (1 / (φ h : ℝ)) := by rw [Finset.mul_sum]
    _ = (2 * (N : ℝ) / q) * ∑ b ∈ R.image φ, (1 / (b : ℝ)) := by
        rw [Finset.sum_image (fun x hx y hy => hinj (Finset.mem_coe.mpr hx)
          (Finset.mem_coe.mpr hy))]
    _ ≤ (2 * (N : ℝ) / q) * ∑ b ∈ Finset.Icc 1 H, (1 / (b : ℝ)) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          rw [Finset.mem_image] at hb
          obtain ⟨h, hhR, rfl⟩ := hb
          obtain ⟨hh0, hhH, _⟩ := hmem h hhR
          rw [Finset.mem_Icc]
          refine ⟨hφpos h hhR, ?_⟩
          rw [hφe]
          have hhle : 2 * h / q ≤ h :=
            Nat.div_le_of_le_mul (by nlinarith [hq])
          omega
        · intro b _ _
          positivity
    _ ≤ (2 * (N : ℝ) / q) * (1 + Real.log H) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ b ∈ Finset.Icc 1 H, (1 / (b : ℝ)) ≤ 1 + Real.log H := sum_one_div_le H

/-- **The tight min-sum bound** (replaces `dyadic_cap_sum_le`, NO bare `N`):
    `∑_{h≤H} min(⌊N/h⌋, 1/2‖hα‖) ≤ (2N/q)(1+log H) + (2H/q+1)(4q + 4q(1+log 2q))`.
    Resonant `h` (near-integer) contribute `(2N/q)·harmonic` (via
    `resonant_floor_sum_le`); non-resonant `h` route through `range_min_sum_le`
    with cap `V = 2q` (since `1/2‖hα‖ ≤ 2q` there). -/
lemma min_sum_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (N H : ℕ) :
    ∑ h ∈ Finset.Ioc 0 H,
      (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
       else min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
      ≤ (2 * (N : ℝ) / q) * (1 + Real.log H)
        + ((H / (q / 2) + 1 : ℕ) : ℝ) * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))) := by
  classical
  set res : ℕ → Prop := fun h => |(h : ℝ) * α - round ((h : ℝ) * α)| < 1 / (4 * (q : ℝ))
    with hres
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 H) res]
  apply add_le_add
  · -- resonant half: each term ≤ ⌊N/h⌋
    refine le_trans (Finset.sum_le_sum ?_)
      (resonant_floor_sum_le a q hq ha α hα N H)
    intro h _
    split
    · exact le_refl _
    · exact min_le_left _ _
  · -- non-resonant half: route through range_min_sum_le at V = 2q
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hIoc : Finset.Ioc 0 H = Finset.Ico 1 (1 + H) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    have hrange := range_min_sum_le a q hq ha α hα (2 * (q : ℝ)) (by positivity) 1 H
    rw [show (1 : ℕ) + H = 1 + H from rfl] at hrange
    -- termwise: non-res term ≤ range-term (V = 2q); then superset + Ioc=Ico
    calc ∑ h ∈ (Finset.Ioc 0 H).filter (fun h => ¬ res h),
          (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
           else min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
        ≤ ∑ h ∈ (Finset.Ioc 0 H).filter (fun h => ¬ res h),
            (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then 2 * (q : ℝ)
             else min (2 * (q : ℝ)) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [Finset.mem_filter] at hh
          have hnr : ¬ res h := hh.2
          rw [hres] at hnr
          push_neg at hnr
          -- ‖hα‖ ≥ 1/(4q) > 0 so the `= 0` branch is false; cap ≤ 2q
          have habs : 1 / (4 * (q : ℝ)) ≤ |(h : ℝ) * α - round ((h : ℝ) * α)| := hnr
          have hne : (h : ℝ) * α - round ((h : ℝ) * α) ≠ 0 := by
            intro h0
            rw [h0, abs_zero] at habs
            have : (0:ℝ) < 1 / (4 * (q : ℝ)) := by positivity
            linarith
          rw [if_neg hne, if_neg hne]
          have hcaple : 1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|) ≤ 2 * (q : ℝ) := by
            rw [div_le_iff₀ (by positivity)]
            have habspos : 0 < |(h : ℝ) * α - round ((h : ℝ) * α)| := by
              rw [abs_pos]; exact hne
            rw [div_le_iff₀ (by positivity)] at habs
            nlinarith [habs, hqR]
          calc min ((N / h : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))
              ≤ 1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|) := min_le_right _ _
            _ = min (2 * (q : ℝ)) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)) := by
                rw [min_eq_right hcaple]
      _ ≤ ∑ h ∈ Finset.Ioc 0 H,
            (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then 2 * (q : ℝ)
             else min (2 * (q : ℝ)) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro h _ _
          split
          · positivity
          · exact le_min (by positivity) (by positivity)
      _ = ∑ h ∈ Finset.Ico 1 (1 + H),
            (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then 2 * (q : ℝ)
             else min (2 * (q : ℝ)) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
          rw [hIoc]
      _ ≤ ((H / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))) := hrange


lemma S2_bound (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V
            * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ Real.log (U * V) *
          (((Nat.log 2 (U * V) + 1 : ℕ) : ℝ)
              * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
            + 32 * (U * V) * (1 + Real.log (2 * q)) + 4 * N) := by
  set c : ArithmeticFunction ℝ := truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V with hc
  have hlogUV0 : (0 : ℝ) ≤ Real.log (U * V) := by
    apply Real.log_nonneg
    exact_mod_cast hUV1
  -- regroup + collapse ζ + normalize the e-argument
  have hre : ∑ n ∈ Finset.Ioc 0 N,
      ((c * (ζ : ArithmeticFunction ℝ)) n : ℂ) * e ((n : ℝ) * α)
      = ∑ t ∈ Finset.Ioc 0 N, (c t : ℂ) *
          ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α)) := by
    rw [sum_Ioc_mul_weight_eq_sum_sum c (ζ : ArithmeticFunction ℝ)
      (fun n => e ((n : ℝ) * α)) N]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    rw [sum_Ioc_zeta_mul (fun m => e (((t * m : ℕ) : ℝ) * α)) (N / t)]
    apply Finset.sum_congr rfl
    intro m _
    exact congrArg e (by push_cast; ring)
  rw [hre]
  -- cap the sum over the support
  set cap : ℕ → ℝ := fun t =>
    (if (t : ℝ) * α - round ((t : ℝ) * α) = 0 then ((N / t : ℕ) : ℝ)
     else min ((N / t : ℕ) : ℝ) (1 / (2 * |(t : ℝ) * α - round ((t : ℝ) * α)|))) with hcap
  have hcap0 : ∀ t, 0 ≤ cap t := by
    intro t
    rw [hcap]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  have hterm : ∀ t ∈ Finset.Ioc 0 N,
      ‖(c t : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖
      ≤ (if t ≤ U * V then Real.log (U * V) * cap t else 0) := by
    intro t ht
    simp only [Finset.mem_Ioc] at ht
    by_cases htuv : t ≤ U * V
    · rw [if_pos htuv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |c t| ≤ Real.log (U * V) := by
        calc |c t| ≤ Real.log t := abs_truncate_mul_le_log U V t
          _ ≤ Real.log (U * V) := by
            apply Real.log_le_log (by exact_mod_cast ht.1)
            exact_mod_cast htuv
      have h2 : ‖∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖ ≤ cap t := by
        rw [hcap]
        exact exp_sum_Ioc_min_bound ((t : ℝ) * α) (N / t)
      exact mul_le_mul h1 h2 (norm_nonneg _) hlogUV0
    · rw [if_neg htuv]
      push_neg at htuv
      have hz : c t = 0 := truncate_mul_eq_zero_of_gt _ _ U V t htuv
      rw [hz]
      simp
  calc ‖∑ t ∈ Finset.Ioc 0 N, (c t : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖
      ≤ ∑ t ∈ Finset.Ioc 0 N,
          ‖(c t : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.Ioc 0 N, (if t ≤ U * V then Real.log (U * V) * cap t else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ t ∈ Finset.Ioc 0 (U * V), Real.log (U * V) * cap t := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun t _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hUV⟩, h2⟩
    _ = Real.log (U * V) * ∑ t ∈ Finset.Ioc 0 (U * V), cap t := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (U * V) *
        (((Nat.log 2 (U * V) + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
          + 32 * (U * V) * (1 + Real.log (2 * q)) + 4 * N) := by
        apply mul_le_mul_of_nonneg_left _ hlogUV0
        have := dyadic_cap_sum_le a q hq ha α hα N (U * V)
        rw [hcap]
        push_cast at this ⊢
        exact this

/-- `log` of a natural cast is nonneg (`log 0 = 0`). -/
lemma log_natCast_nonneg (m : ℕ) : 0 ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · rcases Nat.eq_or_lt_of_le h with h1 | h1
    · rw [← h1]; simp
    · exact Real.log_nonneg (by exact_mod_cast h1.le)

/-- `log ∘ (↑·)` is monotone on ℕ. -/
lemma log_natCast_monotone : Monotone (fun m : ℕ => Real.log m) := by
  intro m₁ m₂ h
  rcases Nat.eq_zero_or_pos m₁ with h1 | h1
  · subst h1
    simp only [Nat.cast_zero, Real.log_zero]
    exact log_natCast_nonneg m₂
  · exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast h)

/-- The min-cap grows by at most 1 when the size cap grows by 1. -/
lemma cap_succ_le (β : ℝ) (M : ℕ) :
    (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
     else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|)))
    ≤ (if β - round β = 0 then (M : ℝ)
       else min (M : ℝ) (1 / (2 * |β - round β|))) + 1 := by
  split
  · push_cast; linarith
  · have h1 : min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))
        ≤ min ((M : ℝ) + 1) (1 / (2 * |β - round β|) + 1) := by
      apply min_le_min _ (by linarith)
      push_cast
      linarith
    calc min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))
        ≤ min ((M : ℝ) + 1) (1 / (2 * |β - round β|) + 1) := h1
      _ = min (M : ℝ) (1 / (2 * |β - round β|)) + 1 := by
          rw [← min_add_add_right]

/-- **THE S₁ BOUND**: the log-weighted Vaughan piece. -/
lemma S1_bound (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U N : ℕ) (hU : U ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((truncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ)
          * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          ((((Nat.log 2 U + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
            + 32 * U * (1 + Real.log (2 * q)) + 4 * N) + U) := by
  have hlogN0 : (0 : ℝ) ≤ Real.log (N + 1) := by
    apply Real.log_nonneg
    push_cast
    linarith
  set cap : ℕ → ℝ := fun t =>
    (if (t : ℝ) * α - round ((t : ℝ) * α) = 0 then ((N / t : ℕ) : ℝ)
     else min ((N / t : ℕ) : ℝ) (1 / (2 * |(t : ℝ) * α - round ((t : ℝ) * α)|))) with hcap
  have hcap0 : ∀ t, 0 ≤ cap t := by
    intro t
    rw [hcap]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  -- regroup
  rw [sum_Ioc_mul_weight_eq_sum_sum (truncate (μ : ArithmeticFunction ℝ) U)
    ArithmeticFunction.log (fun n => e ((n : ℝ) * α)) N]
  -- per-d inner bound
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ‖∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) * (cap d + 1) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    set M : ℕ := N / d with hM
    set β : ℝ := (d : ℝ) * α with hβ
    -- normalize the argument and the log
    have hstep1 : ∑ m ∈ Finset.Ioc 0 M, ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)
        = ∑ m ∈ Finset.Ioc 0 M, ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [ArithmeticFunction.log_apply]
      congr 1
      exact congrArg e (by rw [hβ]; push_cast; ring)
    -- extend Ioc 0 M to range (M+1) (the m = 0 term vanishes)
    have hstep2 : ∑ m ∈ Finset.Ioc 0 M, ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β)
        = ∑ m ∈ Finset.range (M + 1), ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        simp only [Finset.mem_range]
        omega
      · intro m hm hnotm
        simp only [Finset.mem_range] at hm
        simp only [Finset.mem_Ioc] at hnotm
        have hm0 : m = 0 := by omega
        subst hm0
        simp
    -- the capped weight agrees with log on the range
    have hstep3 : ∑ m ∈ Finset.range (M + 1), ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β)
        = ∑ m ∈ Finset.range (M + 1),
            ((Real.log ((min m (M + 1) : ℕ) : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_range] at hm
      rw [min_eq_left (by omega : m ≤ M + 1)]
    have habel := abel_exp_sum (fun m => Real.log ((min m (M + 1) : ℕ) : ℝ))
      (fun m => log_natCast_nonneg _)
      (by
        intro x y h
        exact log_natCast_monotone (by omega : min x (M + 1) ≤ min y (M + 1)))
      (Real.log ((M + 1 : ℕ) : ℝ))
      (fun m => by exact log_natCast_monotone (min_le_right m (M + 1)))
      β (M + 1)
    have hlogM : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log (N + 1) := by
      have h1 : (M : ℕ) + 1 ≤ N + 1 := by
        have : M ≤ N := hM ▸ Nat.div_le_self N d
        omega
      have := log_natCast_monotone (show (M + 1 : ℕ) ≤ (N + 1 : ℕ) from h1)
      push_cast at this ⊢
      exact this
    have hcapd : (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
        else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) ≤ cap d + 1 := by
      have h1 := cap_succ_le β M
      have h2 : (if β - round β = 0 then (M : ℝ)
          else min (M : ℝ) (1 / (2 * |β - round β|))) = cap d := by
        rw [hcap, hβ, hM]
      rw [h2] at h1
      exact h1
    have hcapnn : (0 : ℝ) ≤ (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
        else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
      split
      · positivity
      · exact le_min (by positivity) (by positivity)
    calc ‖∑ m ∈ Finset.Ioc 0 M, ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
        = ‖∑ m ∈ Finset.range (M + 1),
            ((Real.log ((min m (M + 1) : ℕ) : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * β)‖ := by
          rw [hstep1, hstep2, hstep3]
      _ ≤ 2 * Real.log ((M + 1 : ℕ) : ℝ)
            * (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
               else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
          have := habel
          push_cast at this ⊢
          exact this
      _ ≤ 2 * Real.log (N + 1) * (cap d + 1) := by
          apply mul_le_mul
          · have : (0:ℝ) ≤ 2 := by norm_num
            nlinarith [hlogM]
          · exact hcapd
          · exact hcapnn
          · positivity
  -- support + assembly
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖(truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ (if d ≤ U then 2 * Real.log (N + 1) * (cap d + 1) else 0) := by
    intro d hd
    by_cases hdU : d ≤ U
    · rw [if_pos hdU, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |truncate (μ : ArithmeticFunction ℝ) U d| *
            ‖∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
              * e (((d * m : ℕ) : ℝ) * α)‖
          ≤ 1 * (2 * Real.log (N + 1) * (cap d + 1)) := by
            apply mul_le_mul (abs_truncate_moebius_le_one U d) (hinner d hd)
              (norm_nonneg _) (by norm_num)
        _ = 2 * Real.log (N + 1) * (cap d + 1) := one_mul _
    · rw [if_neg hdU]
      have hz : truncate (μ : ArithmeticFunction ℝ) U d = 0 := by
        rw [truncate_apply, if_neg hdU]
      rw [hz]
      simp
  calc ‖∑ d ∈ Finset.Ioc 0 N, (truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          ‖(truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
            ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
              * e (((d * m : ℕ) : ℝ) * α)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (if d ≤ U then 2 * Real.log (N + 1) * (cap d + 1) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Ioc 0 U, 2 * Real.log (N + 1) * (cap d + 1) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun t _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hU⟩, h2⟩
    _ = 2 * Real.log (N + 1) * (∑ d ∈ Finset.Ioc 0 U, cap d + U) := by
        have hsplit : ∀ d ∈ Finset.Ioc 0 U,
            2 * Real.log (N + 1) * (cap d + 1)
            = 2 * Real.log (N + 1) * cap d + 2 * Real.log (N + 1) := fun d _ => by ring
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 * Real.log (N + 1) *
        ((((Nat.log 2 U + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
          + 32 * U * (1 + Real.log (2 * q)) + 4 * N) + U) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have hd := dyadic_cap_sum_le a q hq ha α hα N U
        have hsum : ∑ d ∈ Finset.Ioc 0 U, cap d
            ≤ ((Nat.log 2 U + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
              + 32 * U * (1 + Real.log (2 * q)) + 4 * N := by
          calc ∑ d ∈ Finset.Ioc 0 U, cap d
              = ∑ h ∈ Finset.Ioc 0 U,
                  (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
                   else min ((N / h : ℕ) : ℝ)
                     (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
                apply Finset.sum_congr rfl
                intro h _
                rw [hcap]
            _ ≤ _ := hd
        linarith

/-- Pointwise subtraction for arithmetic functions (no `sub_apply` in Mathlib). -/
lemma sub_apply' (f g : ArithmeticFunction ℝ) (n : ℕ) : (f - g) n = f n - g n := by
  have h : f - g = f + -g := sub_eq_add_neg f g
  rw [h, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  ring

/-- The S₄ inner factor `g = (Λ − Λ_{≤V}) ∗ ζ` is nonneg. -/
lemma tail_conv_nonneg (V m : ℕ) :
    0 ≤ ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)) m := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · rw [sub_apply']
    have h1 : truncate Λ V x.1 ≤ Λ x.1 := by
      rw [truncate_apply]
      split
      · exact le_refl _
      · exact vonMangoldt_nonneg
    linarith
  · rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
    split
    · norm_num
    · norm_num

/-- The S₄ inner factor is log-bounded: `g(m) ≤ log m`. -/
lemma tail_conv_le_log (V m : ℕ) :
    ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)) m ≤ Real.log m := by
  rw [ArithmeticFunction.mul_apply]
  calc ∑ x ∈ m.divisorsAntidiagonal, (Λ - truncate Λ V) x.1 * (ζ : ArithmeticFunction ℝ) x.2
      ≤ ∑ x ∈ m.divisorsAntidiagonal, Λ x.1 := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Nat.mem_divisorsAntidiagonal] at hx
        have hz : ((ζ : ArithmeticFunction ℝ) x.2) = 1 := by
          rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
            if_neg (by
              intro hc
              apply hx.2
              rw [← hx.1, hc, mul_zero])]
          norm_num
        rw [hz, mul_one, sub_apply']
        have h1 : 0 ≤ truncate Λ V x.1 := by
          rw [truncate_apply]
          split
          · exact vonMangoldt_nonneg
          · exact le_refl 0
        linarith
    _ = ∑ d ∈ m.divisors, Λ d := Nat.sum_divisorsAntidiagonal (f := fun d _ => Λ d)
    _ = Real.log m := vonMangoldt_sum

/-- The S₄ inner factor vanishes below the truncation: `g(m) = 0` for `m ≤ V`. -/
lemma tail_conv_eq_zero_of_le (V m : ℕ) (hm : m ≤ V) :
    ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)) m = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  have hle : x.1 ≤ V := by
    have h1 : x.1 ∣ m := ⟨x.2, hx.1.symm⟩
    have h2 : x.1 ≤ m := Nat.le_of_dvd (by omega) h1
    omega
  rw [sub_apply', truncate_apply, if_pos hle, sub_self, zero_mul]

/-- The Möbius tail vanishes below the truncation. -/
lemma moebius_tail_eq_zero_of_le (U d : ℕ) (hd : d ≤ U) :
    ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U) d = 0 := by
  rw [sub_apply', truncate_apply, if_pos hd, sub_self]

/-- The Möbius tail is sup-bounded by 1. -/
lemma abs_moebius_tail_le_one (U d : ℕ) :
    |((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U) d| ≤ 1 := by
  rw [sub_apply', truncate_apply]
  split
  · rw [sub_self]
    norm_num
  · rw [sub_zero]
    have h := abs_moebius_le_one (n := d)
    rw [ArithmeticFunction.intCoe_apply]
    calc |((μ d : ℤ) : ℝ)| = ((|μ d| : ℤ) : ℝ) := by rw [Int.cast_abs]
      _ ≤ 1 := by exact_mod_cast h

/-- **Increasing geometric sum**: `∑_{t=t₀}^{T} (√2)^t ≤ 4·(√2)^T`. -/
lemma geom_sqrt2_up (t₀ T : ℕ) :
    ∑ t ∈ Finset.Icc t₀ T, (Real.sqrt 2) ^ t ≤ 4 * (Real.sqrt 2) ^ T := by
  have hr1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) < Real.sqrt 2 := by linarith
  -- ∑_{Icc t₀ T} ≤ ∑_{range (T+1)}
  have hsub : ∑ t ∈ Finset.Icc t₀ T, (Real.sqrt 2) ^ t
      ≤ ∑ t ∈ Finset.range (T + 1), (Real.sqrt 2) ^ t := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      rw [Finset.mem_Icc] at ht
      rw [Finset.mem_range]
      omega
    · intro t _ _
      positivity
  have hgeom : ∑ t ∈ Finset.range (T + 1), (Real.sqrt 2) ^ t
      = ((Real.sqrt 2) ^ (T + 1) - 1) / (Real.sqrt 2 - 1) :=
    geom_sum_eq (by linarith) (T + 1)
  rw [hgeom] at hsub
  refine hsub.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have hpow : (Real.sqrt 2) ^ (T + 1) = Real.sqrt 2 * (Real.sqrt 2) ^ T := by
    rw [pow_succ]; ring
  -- need √2 ≥ 4/3 so that 3√2 - 4 ≥ 0
  have hsqrt2ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (4 / 3 : ℝ) = Real.sqrt ((4/3)^2) from by
      rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    norm_num
  have hpowpos : (0 : ℝ) < (Real.sqrt 2) ^ T := by positivity
  rw [hpow]
  nlinarith [hpowpos, hsqrt2ge,
    mul_nonneg hpowpos.le (show (0:ℝ) ≤ 3 * Real.sqrt 2 - 4 by nlinarith [hsqrt2ge])]

/-- **Decreasing geometric sum**: `∑_{t=t₀}^{T} (√2)⁻ᵗ ≤ 4·(√2)^(-t₀)`
    (stated as `(1/√2)^t`). -/
lemma geom_sqrt2_down (t₀ T : ℕ) :
    ∑ t ∈ Finset.Icc t₀ T, (1 / Real.sqrt 2) ^ t ≤ 4 * (1 / Real.sqrt 2) ^ t₀ := by
  have hr1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) < Real.sqrt 2 := by linarith
  have hlt1 : (1 / Real.sqrt 2) < 1 := by
    rw [div_lt_one hr0]; exact hr1
  have hnn : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  -- shift index: ∑_{t=t₀}^{T} r^t = r^{t₀} ∑_{k=0}^{T-t₀} r^k ≤ r^{t₀} · (1/(1-r))
  by_cases hle : t₀ ≤ T
  · have hIccIco : Finset.Icc t₀ T = Finset.Ico t₀ (T + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hshift : ∑ t ∈ Finset.Icc t₀ T, (1 / Real.sqrt 2) ^ t
        = (1 / Real.sqrt 2) ^ t₀ * ∑ k ∈ Finset.range (T + 1 - t₀), (1 / Real.sqrt 2) ^ k := by
      rw [hIccIco, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
    rw [hshift]
    have hsqrt2ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (4 / 3 : ℝ) = Real.sqrt ((4/3)^2) from by
        rw [Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      norm_num
    have hinvle : 1 / Real.sqrt 2 ≤ 3 / 4 := by
      rw [div_le_div_iff₀ hr0 (by norm_num)]
      linarith
    have hgeomle : ∑ k ∈ Finset.range (T + 1 - t₀), (1 / Real.sqrt 2) ^ k ≤ 4 := by
      have heq := geom_sum_eq (show (1 / Real.sqrt 2) ≠ 1 from ne_of_lt hlt1) (T + 1 - t₀)
      rw [heq]
      -- (r^n - 1)/(r - 1) = (1 - r^n)/(1 - r) ≤ 1/(1-r) ≤ 4
      have hden : (0:ℝ) < 1 - 1 / Real.sqrt 2 := by linarith
      have hrw : ((1 / Real.sqrt 2) ^ (T + 1 - t₀) - 1) / (1 / Real.sqrt 2 - 1)
          = (1 - (1 / Real.sqrt 2) ^ (T + 1 - t₀)) / (1 - 1 / Real.sqrt 2) := by
        rw [div_eq_div_iff (ne_of_lt (by linarith : 1 / Real.sqrt 2 - 1 < 0))
          (ne_of_gt hden)]; ring
      rw [hrw, div_le_iff₀ hden]
      have hp : (0:ℝ) ≤ (1 / Real.sqrt 2) ^ (T + 1 - t₀) := by positivity
      linarith
    calc (1 / Real.sqrt 2) ^ t₀ * ∑ k ∈ Finset.range (T + 1 - t₀), (1 / Real.sqrt 2) ^ k
        ≤ (1 / Real.sqrt 2) ^ t₀ * 4 :=
          mul_le_mul_of_nonneg_left hgeomle (by positivity)
      _ = 4 * (1 / Real.sqrt 2) ^ t₀ := by ring
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- `√(a+b) ≤ √a + √b`. -/
lemma sqrt_add_le' (a b : ℝ) : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : Real.sqrt (a + b) ≤ Real.sqrt (Real.sqrt a ^ 2 + Real.sqrt b ^ 2 + 2 * (Real.sqrt a * Real.sqrt b)) := by
    apply Real.sqrt_le_sqrt
    by_cases ha : 0 ≤ a
    · by_cases hb : 0 ≤ b
      · rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
        nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp hb))]
        rw [Real.sq_sqrt ha]
        simp only [Real.sqrt_zero, mul_zero, add_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true]
        nlinarith [Real.sqrt_nonneg a]
    · have : Real.sqrt a = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp ha))
      rw [this]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_zero,
        add_zero, zero_mul]
      by_cases hb : 0 ≤ b
      · rw [Real.sq_sqrt hb]; nlinarith [Real.sqrt_nonneg b]
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp hb))]; simp; linarith
  refine h.trans (le_of_eq ?_)
  rw [show Real.sqrt a ^ 2 + Real.sqrt b ^ 2 + 2 * (Real.sqrt a * Real.sqrt b)
      = (Real.sqrt a + Real.sqrt b) ^ 2 from by ring,
    Real.sqrt_sq (by positivity)]

/-- `√(a+b+c+d) ≤ √a+√b+√c+√d`. -/
lemma sqrt_add4_le (a b c d : ℝ) :
    Real.sqrt (a + b + c + d) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by
  calc Real.sqrt (a + b + c + d)
      ≤ Real.sqrt (a + b + c) + Real.sqrt d := sqrt_add_le' _ _
    _ ≤ (Real.sqrt (a + b) + Real.sqrt c) + Real.sqrt d := by
        gcongr; exact sqrt_add_le' _ _
    _ ≤ ((Real.sqrt a + Real.sqrt b) + Real.sqrt c) + Real.sqrt d := by
        gcongr; exact sqrt_add_le' _ _
    _ = Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by ring

/-- `√(2^t) = (√2)^t`. -/
lemma sqrt_two_pow (t : ℕ) : Real.sqrt ((2 : ℝ) ^ t) = (Real.sqrt 2) ^ t := by
  rw [show ((2 : ℝ) ^ t) = ((Real.sqrt 2) ^ t) ^ 2 from by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)],
    Real.sqrt_sq (by positivity)]

/-- `(1/√2)^t = √(1/2^t)`. -/
lemma sqrt_two_pow_inv (t : ℕ) : (1 / Real.sqrt 2) ^ t = Real.sqrt (1 / (2 : ℝ) ^ t) := by
  rw [div_pow, one_pow, ← sqrt_two_pow, one_div, ← Real.sqrt_inv, one_div]

/-- `√(c·N²) = √c·N` for `N ≥ 0`, `c ≥ 0`. -/
lemma sqrt_const_mul_sq (c : ℝ) (hc : 0 ≤ c) (N : ℕ) :
    Real.sqrt (c * (N:ℝ)^2) = Real.sqrt c * N := by
  rw [Real.sqrt_mul hc, Real.sqrt_sq (by positivity)]

/-- **The tight dyadic assembly** (Type-II core): sum the per-block second-moment bounds
    across the dyadic range `[t₀, Tmax]` via `√·` splitting and geometric summation.
    Each of the four terms in the per-block bound sums to a geometric series (the `2^t`
    term increasing, the `1/2^t` term decreasing, the `q` and `N²/q` terms constant),
    giving the four-term envelope on the right. This replaces the lossy `S4_bound`
    dyadic assembly (which over-charged the `2^t` cap to `N`). -/
lemma s4_dyadic_assembly (N q V U t₀ Tmax : ℕ) (hq : 2 ≤ q) (hN1 : 1 ≤ N) (hU1 : 1 ≤ U)
    (ht0T : t₀ ≤ Tmax)
    (hUt0 : (U : ℝ) ≤ 2 * (2 : ℝ) ^ t₀)
    (hTmaxN : (2 : ℝ) ^ Tmax ≤ (N : ℝ) / (V + 1))
    (blk : ℕ → ℝ) (hblk0 : ∀ t, 0 ≤ blk t)
    (hbnd : ∀ t ∈ Finset.Icc t₀ Tmax,
        blk t ^ 2 ≤ (Real.log N) ^ 2 *
          (10 * N * (2:ℝ)^t + 32 * N^2 / q + 64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t
            + 36 * N * q * (1 + Real.log (2*q)))) :
    ∑ t ∈ Finset.Icc t₀ Tmax, blk t
      ≤ Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N * ((Tmax - t₀ + 1 : ℕ) : ℝ) / Real.sqrt q
          + 64 * N * Real.sqrt (1 + Real.log (2*q)) / Real.sqrt U
          + 6 * ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (N * q * (1 + Real.log (2*q)))) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hNR : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hUR : (0:ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hlogN0 : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hL0 : (0:ℝ) ≤ 1 + Real.log (2*q) := by
    have : (0:ℝ) ≤ Real.log (2*q) := Real.log_nonneg (by
      have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith)
    linarith
  -- per-block bound
  have hper : ∀ t ∈ Finset.Icc t₀ Tmax,
      blk t ≤ Real.log N * (Real.sqrt (10 * N) * (Real.sqrt 2)^t
        + Real.sqrt (32 * N^2 / q)
        + Real.sqrt (64 * N^2 * (1 + Real.log (2*q))) * (1 / Real.sqrt 2)^t
        + Real.sqrt (36 * N * q * (1 + Real.log (2*q)))) := by
    intro t ht
    have hb := hbnd t ht
    have hsq : blk t ≤ Real.sqrt ((Real.log N) ^ 2 *
        (10 * N * (2:ℝ)^t + 32 * N^2 / q + 64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t
          + 36 * N * q * (1 + Real.log (2*q)))) := by
      rw [← Real.sqrt_sq (hblk0 t)]
      exact Real.sqrt_le_sqrt hb
    refine hsq.trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hlogN0]
    apply mul_le_mul_of_nonneg_left ?_ hlogN0
    have e1 : Real.sqrt (10 * N * (2:ℝ)^t) = Real.sqrt (10 * N) * (Real.sqrt 2)^t := by
      rw [show (10 * (N:ℝ) * (2:ℝ)^t) = (10 * N) * (2:ℝ)^t from by ring,
        Real.sqrt_mul (by positivity), sqrt_two_pow]
    have e3 : Real.sqrt (64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t)
        = Real.sqrt (64 * N^2 * (1 + Real.log (2*q))) * (1 / Real.sqrt 2)^t := by
      rw [show (64 * (N:ℝ)^2 * (1 + Real.log (2*q)) / (2:ℝ)^t)
          = (64 * N^2 * (1 + Real.log (2*q))) * (1 / (2:ℝ)^t) from by ring,
        Real.sqrt_mul (by positivity), ← sqrt_two_pow_inv]
    calc Real.sqrt (10 * N * (2:ℝ)^t + 32 * N^2 / q
          + 64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t + 36 * N * q * (1 + Real.log (2*q)))
        ≤ Real.sqrt (10 * N * (2:ℝ)^t) + Real.sqrt (32 * N^2 / q)
          + Real.sqrt (64 * N^2 * (1 + Real.log (2*q)) / (2:ℝ)^t)
          + Real.sqrt (36 * N * q * (1 + Real.log (2*q))) := sqrt_add4_le _ _ _ _
      _ = Real.sqrt (10 * N) * (Real.sqrt 2)^t + Real.sqrt (32 * N^2 / q)
          + Real.sqrt (64 * N^2 * (1 + Real.log (2*q))) * (1 / Real.sqrt 2)^t
          + Real.sqrt (36 * N * q * (1 + Real.log (2*q))) := by rw [e1, e3]
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left ?_ hlogN0
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]
  have hcard : ((Tmax + 1 - t₀ : ℕ) : ℝ) = ((Tmax - t₀ + 1 : ℕ) : ℝ) := by
    congr 1; omega
  rw [hcard]
  -- P1
  have hP1 : Real.sqrt (10 * N) * (∑ t ∈ Finset.Icc t₀ Tmax, (Real.sqrt 2)^t)
      ≤ 4 * Real.sqrt 10 * N / Real.sqrt (V + 1) := by
    refine (mul_le_mul_of_nonneg_left (geom_sqrt2_up t₀ Tmax) (Real.sqrt_nonneg _)).trans ?_
    rw [← sqrt_two_pow]
    have h2 : Real.sqrt ((2:ℝ)^Tmax) ≤ Real.sqrt ((N:ℝ)/(V+1)) := Real.sqrt_le_sqrt hTmaxN
    have hVpos : (0:ℝ) < (V:ℝ) + 1 := by positivity
    calc Real.sqrt (10 * N) * (4 * Real.sqrt ((2:ℝ)^Tmax))
        ≤ Real.sqrt (10 * N) * (4 * Real.sqrt ((N:ℝ)/(V+1))) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by norm_num))
            (Real.sqrt_nonneg _)
      _ = 4 * Real.sqrt (10 * N * ((N:ℝ)/(V+1))) := by
          rw [show Real.sqrt (10 * N) * (4 * Real.sqrt ((N:ℝ)/(V+1)))
              = 4 * (Real.sqrt (10 * N) * Real.sqrt ((N:ℝ)/(V+1))) from by ring,
            ← Real.sqrt_mul (by positivity)]
      _ = 4 * Real.sqrt 10 * N / Real.sqrt (V + 1) := by
          rw [show (10 * (N:ℝ) * ((N:ℝ)/(V+1))) = (10 * N^2) / (V+1) from by ring,
            Real.sqrt_div (by positivity), sqrt_const_mul_sq 10 (by norm_num) N]
          ring
  -- P3
  have hP3 : Real.sqrt (64 * N^2 * (1 + Real.log (2*q))) * (∑ t ∈ Finset.Icc t₀ Tmax, (1/Real.sqrt 2)^t)
      ≤ 64 * N * Real.sqrt (1 + Real.log (2*q)) / Real.sqrt U := by
    have hs64 : Real.sqrt (64 * N^2 * (1 + Real.log (2*q)))
        = 8 * N * Real.sqrt (1 + Real.log (2*q)) := by
      rw [show (64 * (N:ℝ)^2 * (1 + Real.log (2*q))) = (8 * N)^2 * (1 + Real.log (2*q)) from by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [hs64]
    refine (mul_le_mul_of_nonneg_left (geom_sqrt2_down t₀ Tmax) (by positivity)).trans ?_
    rw [sqrt_two_pow_inv]
    have hkey : Real.sqrt (1 / (2:ℝ)^t₀) ≤ 2 / Real.sqrt U := by
      have hle : (1:ℝ) / (2:ℝ)^t₀ ≤ 4 / U := by
        rw [div_le_div_iff₀ (by positivity) hUR]
        nlinarith [hUt0]
      have h4U : Real.sqrt (4 / U) = 2 / Real.sqrt U := by
        rw [Real.sqrt_div (by norm_num), show Real.sqrt 4 = 2 from by
          rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num)]]
      calc Real.sqrt (1 / (2:ℝ)^t₀) ≤ Real.sqrt (4 / U) := Real.sqrt_le_sqrt hle
        _ = 2 / Real.sqrt U := h4U
    calc 8 * N * Real.sqrt (1 + Real.log (2*q)) * (4 * Real.sqrt (1 / (2:ℝ)^t₀))
        = (32 * N * Real.sqrt (1 + Real.log (2*q))) * Real.sqrt (1 / (2:ℝ)^t₀) := by ring
      _ ≤ (32 * N * Real.sqrt (1 + Real.log (2*q))) * (2 / Real.sqrt U) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 64 * N * Real.sqrt (1 + Real.log (2*q)) / Real.sqrt U := by ring
  -- T2, T4 (equalities)
  have hT2 : ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (32 * N^2 / q)
      = Real.sqrt 32 * N * ((Tmax - t₀ + 1 : ℕ) : ℝ) / Real.sqrt q := by
    rw [show (32 * (N:ℝ)^2 / q) = (32 * N^2) / q from by ring,
      Real.sqrt_div (by positivity), sqrt_const_mul_sq 32 (by norm_num) N]
    ring
  have hT4 : ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (36 * N * q * (1 + Real.log (2*q)))
      = 6 * ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (N * q * (1 + Real.log (2*q))) := by
    rw [show (36 * (N:ℝ) * q * (1 + Real.log (2*q)))
        = 36 * (N * q * (1 + Real.log (2*q))) from by ring,
      Real.sqrt_mul (by norm_num), show Real.sqrt 36 = 6 from by
        rw [show (36:ℝ) = 6^2 from by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  rw [hT2, hT4]
  exact add_le_add (add_le_add (add_le_add hP1 (le_of_eq rfl)) hP3) (le_of_eq rfl)

/-- **Per-block absorption** (Type-II core algebra): the dyadic block second-moment
    envelope `D·(x+1)·(D + 2(y+1)(2D+4qL))` (with `D=2^t`, `x=⌊N/D⌋`, `y=⌊x/⌊q/2⌋⌋`)
    is dominated by the four clean geometric terms consumed by `s4_dyadic_assembly`. -/
lemma s4_block_absorb (D x y q L N : ℝ)
    (hD1 : 1 ≤ D) (hq2 : 2 ≤ q) (hL0 : 0 ≤ L) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hN0 : 0 ≤ N)
    (hDx : D * x ≤ N) (hDN : D ≤ N) (hyx : y ≤ x) (hqy : q * y ≤ 4 * x) :
    D * (x + 1) * (D + 2 * (y + 1) * (2 * D + 4 * q * L))
      ≤ 10 * N * D + 32 * N ^ 2 / q + 64 * N ^ 2 * L / D + 36 * N * q * L := by
  have hD0 : (0:ℝ) ≤ D := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hDpos : (0:ℝ) < D := by linarith
  have hDDx : D * (D * x) ≤ D * N := mul_le_mul_of_nonneg_left hDx hD0
  have hDD : D * D ≤ D * N := mul_le_mul_of_nonneg_left hDN hD0
  have hDy : D * y ≤ N := le_trans (mul_le_mul_of_nonneg_left hyx hD0) hDx
  have hG_ND : 5 * D ^ 2 * x + 5 * D ^ 2 ≤ 10 * N * D := by nlinarith [hDDx, hDD]
  have hG_Nq : 4 * D ^ 2 * x * y + 4 * D ^ 2 * y ≤ 32 * N ^ 2 / q := by
    rw [le_div_iff₀ hq0]
    have e1 : (4 * D ^ 2 * x * y + 4 * D ^ 2 * y) * q
        = 4 * D ^ 2 * x * (q * y) + 4 * D ^ 2 * (q * y) := by ring
    rw [e1]
    have h1 : 4 * D ^ 2 * x * (q * y) ≤ 4 * D ^ 2 * x * (4 * x) :=
      mul_le_mul_of_nonneg_left hqy (by positivity)
    have h2 : 4 * D ^ 2 * (q * y) ≤ 4 * D ^ 2 * (4 * x) :=
      mul_le_mul_of_nonneg_left hqy (by positivity)
    have hDx2 : (D * x) ^ 2 ≤ N ^ 2 := by nlinarith [hDx, mul_nonneg hD0 hx0, hN0]
    have hDxN : D * (D * x) ≤ N ^ 2 := le_trans hDDx (by nlinarith [hDN, hN0])
    nlinarith [h1, h2, hDx2, hDxN, mul_nonneg (mul_nonneg hD0 hD0) hx0, hN0]
  have hG_ND2 : 8 * D * q * L * x * y ≤ 64 * N ^ 2 * L / D := by
    rw [le_div_iff₀ hDpos]
    have e1 : 8 * D * q * L * x * y * D = L * (8 * D ^ 2 * x * (q * y)) := by ring
    rw [e1]
    have h1 : 8 * D ^ 2 * x * (q * y) ≤ 8 * D ^ 2 * x * (4 * x) :=
      mul_le_mul_of_nonneg_left hqy (by positivity)
    have hDx2 : (D * x) ^ 2 ≤ N ^ 2 := by nlinarith [hDx, mul_nonneg hD0 hx0, hN0]
    have h2 : 8 * D ^ 2 * x * (4 * x) ≤ 64 * N ^ 2 := by nlinarith [hDx2]
    have h3 : 8 * D ^ 2 * x * (q * y) ≤ 64 * N ^ 2 := le_trans h1 h2
    calc L * (8 * D ^ 2 * x * (q * y)) ≤ L * (64 * N ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hL0
      _ = 64 * N ^ 2 * L := by ring
  have hG_NqL : 8 * D * q * L * x + 8 * D * q * L * y + 8 * D * q * L
      ≤ 36 * N * q * L := by
    have hqL0 : (0:ℝ) ≤ q * L := mul_nonneg (le_of_lt hq0) hL0
    have t1 : 8 * D * q * L * x = 8 * (q * L) * (D * x) := by ring
    have t2 : 8 * D * q * L * y = 8 * (q * L) * (D * y) := by ring
    have t3 : 8 * D * q * L = 8 * (q * L) * D := by ring
    have b1 : 8 * (q * L) * (D * x) ≤ 8 * (q * L) * N :=
      mul_le_mul_of_nonneg_left hDx (by positivity)
    have b2 : 8 * (q * L) * (D * y) ≤ 8 * (q * L) * N :=
      mul_le_mul_of_nonneg_left hDy (by positivity)
    have b3 : 8 * (q * L) * D ≤ 8 * (q * L) * N :=
      mul_le_mul_of_nonneg_left hDN (by positivity)
    nlinarith [b1, b2, b3, t1, t2, t3, mul_nonneg hqL0 hN0]
  have hEexp : D * (x + 1) * (D + 2 * (y + 1) * (2 * D + 4 * q * L))
      = (5 * D ^ 2 * x + 5 * D ^ 2) + (4 * D ^ 2 * x * y + 4 * D ^ 2 * y)
        + (8 * D * q * L * x * y)
        + (8 * D * q * L * x + 8 * D * q * L * y + 8 * D * q * L) := by ring
  rw [hEexp]
  linarith [hG_ND, hG_Nq, hG_ND2, hG_NqL]

/-- **Per-block `hbnd`** for `s4_dyadic_assembly`: the dyadic-block sum-of-norms squared
    is dominated by the four-term geometric envelope (Cauchy–Schwarz on the block, then
    `S4_block_second_moment`, then `s4_block_absorb`). -/
lemma s4_block_hbnd (a q N V t : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (g : ℕ → ℝ) (G : ℝ)
    (hg0 : ∀ m, 0 ≤ g m) (hgG : ∀ m, g m ≤ G)
    (hN1 : 1 ≤ N) (h2tN : (2:ℕ) ^ t ≤ N) :
    (∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
        ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2
      ≤ G ^ 2 * (10 * N * (2:ℝ) ^ t + 32 * N ^ 2 / q
          + 64 * N ^ 2 * (1 + Real.log (2 * q)) / (2:ℝ) ^ t
          + 36 * N * q * (1 + Real.log (2 * q))) := by
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t))
    (f := fun d => ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖)
  rw [Nat.card_Ico] at hcs
  have hmom := S4_block_second_moment a q hq ha α hα g G hg0 hgG N (2 ^ t) (2 ^ t + 2 ^ t) V
    (by positivity)
  have hcard : ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) = (2:ℝ) ^ t := by
    have h : (2 ^ t + 2 ^ t - 2 ^ t : ℕ) = 2 ^ t := Nat.add_sub_cancel _ _
    rw [h]; push_cast; ring
  have hL0 : (0:ℝ) ≤ 1 + Real.log (2 * q) := by
    have : (0:ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by nlinarith [hq2])
    linarith
  have hx0 : (0:ℝ) ≤ ((N / 2 ^ t : ℕ) : ℝ) := by positivity
  have hy0 : (0:ℝ) ≤ (((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) := by positivity
  have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hD1 : (1:ℝ) ≤ (2:ℝ) ^ t := one_le_pow₀ (by norm_num)
  have hDx : (2:ℝ) ^ t * ((N / 2 ^ t : ℕ) : ℝ) ≤ N := by
    have hnat : (N / 2 ^ t) * 2 ^ t ≤ N := Nat.div_mul_le_self N (2 ^ t)
    calc (2:ℝ) ^ t * ((N / 2 ^ t : ℕ) : ℝ)
        = (((N / 2 ^ t) * 2 ^ t : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (N:ℝ) := by exact_mod_cast hnat
  have hDN : (2:ℝ) ^ t ≤ N := by exact_mod_cast h2tN
  have hyx : (((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) ≤ ((N / 2 ^ t : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_le_self _ _
  have hqy : (q:ℝ) * (((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) ≤ 4 * ((N / 2 ^ t : ℕ) : ℝ) := by
    have h2 : q ≤ 4 * (q / 2) := by omega
    have h1 : ((N / 2 ^ t) / (q / 2)) * (q / 2) ≤ N / 2 ^ t := Nat.div_mul_le_self _ _
    have hnat : q * ((N / 2 ^ t) / (q / 2)) ≤ 4 * (N / 2 ^ t) := by
      calc q * ((N / 2 ^ t) / (q / 2))
          ≤ 4 * (q / 2) * ((N / 2 ^ t) / (q / 2)) := Nat.mul_le_mul_right _ h2
        _ = 4 * (((N / 2 ^ t) / (q / 2)) * (q / 2)) := by ring
        _ ≤ 4 * (N / 2 ^ t) := Nat.mul_le_mul_left _ h1
    exact_mod_cast hnat
  have habs := s4_block_absorb ((2:ℝ) ^ t) ((N / 2 ^ t : ℕ) : ℝ)
    (((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) q (1 + Real.log (2 * q)) N
    hD1 hq2 hL0 hx0 hy0 hN0 hDx hDN hyx hqy
  have hmomeq : G ^ 2 * (((N / 2 ^ t : ℕ) : ℝ) + 1) *
      (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) + 2 * ((((N / 2 ^ t) / (q / 2) + 1 : ℕ) : ℝ))
        * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))
      = G ^ 2 * ((((N / 2 ^ t : ℕ) : ℝ) + 1) * ((2:ℝ) ^ t
          + 2 * ((((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) + 1)
            * (2 * (2:ℝ) ^ t + 4 * q * (1 + Real.log (2 * q))))) := by
    rw [hcard]; push_cast; ring
  calc (∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
          ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2
      ≤ ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) *
          ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
            ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2 := by
        exact_mod_cast hcs
    _ = (2:ℝ) ^ t *
          ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
            ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2 := by
        rw [hcard]
    _ ≤ (2:ℝ) ^ t * (G ^ 2 * ((((N / 2 ^ t : ℕ) : ℝ) + 1) * ((2:ℝ) ^ t
          + 2 * ((((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) + 1)
            * (2 * (2:ℝ) ^ t + 4 * q * (1 + Real.log (2 * q)))))) :=
        mul_le_mul_of_nonneg_left (hmom.trans_eq hmomeq) (by positivity)
    _ = G ^ 2 * ((2:ℝ) ^ t * (((N / 2 ^ t : ℕ) : ℝ) + 1) * ((2:ℝ) ^ t
          + 2 * ((((N / 2 ^ t) / (q / 2) : ℕ) : ℝ) + 1)
            * (2 * (2:ℝ) ^ t + 4 * q * (1 + Real.log (2 * q))))) := by ring
    _ ≤ G ^ 2 * (10 * N * (2:ℝ) ^ t + 32 * N ^ 2 / q
          + 64 * N ^ 2 * (1 + Real.log (2 * q)) / (2:ℝ) ^ t
          + 36 * N * q * (1 + Real.log (2 * q))) :=
        mul_le_mul_of_nonneg_left habs (by positivity)


lemma S4_bound (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
            * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ))) n : ℝ) : ℂ)
          * e ((n : ℝ) * α)‖
      ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) *
          Real.sqrt ((N : ℝ) * (Real.log N ^ 2
            * (((N / 2 ^ Nat.log 2 (U + 1) : ℕ) : ℝ) + 1)
            * ((N : ℝ) + 2 * ((((N / 2 ^ Nat.log 2 (U + 1) : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * N + 4 * q * (1 + Real.log (2 * q)))))) := by
  set c : ArithmeticFunction ℝ :=
    (μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U with hc
  set gAF : ArithmeticFunction ℝ := (Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ) with hgAF
  set ghat : ℕ → ℝ := fun m => if m ≤ N then gAF m else 0 with hghat
  set t₀ : ℕ := Nat.log 2 (U + 1) with ht₀
  set Tmax : ℕ := Nat.log 2 N with hTmax
  set Mom : ℝ := Real.log N ^ 2 * (((N / 2 ^ t₀ : ℕ) : ℝ) + 1)
      * ((N : ℝ) + 2 * ((((N / 2 ^ t₀ : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
        * (2 * N + 4 * q * (1 + Real.log (2 * q)))) with hMom
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 * q) := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have : (0 : ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
    linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · subst hN0
    simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    positivity
  have hMom0 : 0 ≤ Mom := by
    rw [hMom]
    have h1 : (0 : ℝ) ≤ (N : ℝ) + 2 * ((((N / 2 ^ t₀ : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
        * (2 * N + 4 * q * (1 + Real.log (2 * q))) := by
      have h2 : (0 : ℝ) ≤ 2 * N + 4 * q * (1 + Real.log (2 * q)) := by
        have := mul_nonneg (by positivity : (0:ℝ) ≤ 4 * q) hL0
        positivity
      positivity
    positivity
  have hghat0 : ∀ m, 0 ≤ ghat m := by
    intro m
    rw [hghat]
    dsimp only
    split
    · exact tail_conv_nonneg V m
    · exact le_refl 0
  have hghatG : ∀ m, ghat m ≤ Real.log N := by
    intro m
    rw [hghat]
    dsimp only
    split
    · rename_i hm
      calc gAF m ≤ Real.log m := tail_conv_le_log V m
        _ ≤ Real.log N := log_natCast_monotone hm
    · exact log_natCast_nonneg N
  -- regroup and restrict the inner sums
  rw [show c * gAF = c * gAF from rfl,
    sum_Ioc_mul_weight_eq_sum_sum c gAF (fun n => e ((n : ℝ) * α)) N]
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ∑ m ∈ Finset.Ioc 0 (N / d), (gAF m : ℂ) * e (((d * m : ℕ) : ℝ) * α)
      = ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    have step1 : ∑ m ∈ Finset.Ioc 0 (N / d), (gAF m : ℂ) * e (((d * m : ℕ) : ℝ) * α)
        = ∑ m ∈ Finset.Ioc 0 (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      have hmN : m ≤ N := le_trans hm.2 (Nat.div_le_self N d)
      rw [hghat]
      dsimp only
      rw [if_pos hmN]
      congr 1
      exact congrArg e (by push_cast; ring)
    rw [step1]
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Ioc] at hm ⊢
      omega
    · intro m hm hnot
      simp only [Finset.mem_Ioc] at hm hnot
      have hmV : m ≤ V := by omega
      have hz : ghat m = 0 := by
        rw [hghat]
        dsimp only
        split
        · exact tail_conv_eq_zero_of_le V m hmV
        · rfl
      rw [hz]
      simp
  rw [Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])]
  -- support restriction + triangle
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖(c d : ℂ) * ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ (if U < d then
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ else 0) := by
    intro d _
    by_cases hdU : U < d
    · rw [if_pos hdU, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := abs_moebius_tail_le_one U d
      rw [hc]
      calc |(((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U) d)| *
            ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
          ≤ 1 * ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := one_mul _
    · rw [if_neg hdU]
      have hz : c d = 0 := by
        rw [hc]
        exact moebius_tail_eq_zero_of_le U d (by omega)
      rw [hz]
      simp
  calc ‖∑ d ∈ Finset.Ioc 0 N, (c d : ℂ) *
        ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          ‖(c d : ℂ) * ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (if U < d then
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Ioc U N,
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun d _ => rfl)
        ext d
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        omega
    _ ≤ ∑ t ∈ Finset.Icc t₀ Tmax, ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ := by
        have hcover : Finset.Ioc U N ⊆
            (Finset.Icc t₀ Tmax).biUnion (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
          intro d hd
          simp only [Finset.mem_Ioc] at hd
          rw [Finset.mem_biUnion]
          refine ⟨Nat.log 2 d, ?_, ?_⟩
          · rw [Finset.mem_Icc, ht₀, hTmax]
            constructor
            · exact Nat.log_mono_right (by omega)
            · exact Nat.log_mono_right hd.2
          · rw [Finset.mem_Ico]
            constructor
            · exact Nat.pow_log_le_self 2 (by omega)
            · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d
              rw [pow_succ] at this
              omega
        have hdisj : (↑(Finset.Icc t₀ Tmax) : Set ℕ).PairwiseDisjoint
            (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
          intro t₁ _ t₂ _ hne
          apply Finset.disjoint_left.mpr
          intro h h1 h2
          simp only [Finset.mem_Ico] at h1 h2
          rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
          · have : (2 : ℕ) ^ (t₁ + 1) ≤ 2 ^ t₂ := Nat.pow_le_pow_right (by norm_num) hlt
            rw [pow_succ] at this
            omega
          · have hlt2 : t₂ < t₁ := lt_of_le_of_ne hge (Ne.symm hne)
            have : (2 : ℕ) ^ (t₂ + 1) ≤ 2 ^ t₁ := Nat.pow_le_pow_right (by norm_num) hlt2
            rw [pow_succ] at this
            omega
        calc ∑ d ∈ Finset.Ioc U N,
            ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
            ≤ ∑ d ∈ (Finset.Icc t₀ Tmax).biUnion
                (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)),
                ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg hcover (fun d _ _ => norm_nonneg _)
          _ = _ := Finset.sum_biUnion hdisj
    _ ≤ ∑ _t ∈ Finset.Icc t₀ Tmax, Real.sqrt ((N : ℝ) * Mom) := by
        apply Finset.sum_le_sum
        intro t ht
        simp only [Finset.mem_Icc] at ht
        apply Real.le_sqrt_of_sq_le
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t))
          (f := fun d => ‖∑ m ∈ Finset.Ioc V (N / d),
            (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖)
        rw [Nat.card_Ico] at hcs
        have hcard : ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) = ((2 : ℝ) ^ t) := by
          have hnat : (2 ^ t + 2 ^ t - 2 ^ t : ℕ) = 2 ^ t := Nat.add_sub_cancel _ _
          rw [hnat]
          push_cast
          ring
        have hmom := S4_block_second_moment a q hq ha α hα ghat (Real.log N)
          hghat0 hghatG N (2 ^ t) (2 ^ t + 2 ^ t) V (by positivity)
        -- monotone-in-t bounds
        have h2tN : (2 : ℕ) ^ t ≤ N := by
          calc (2 : ℕ) ^ t ≤ 2 ^ Tmax := Nat.pow_le_pow_right (by norm_num) ht.2
            _ ≤ N := by
              rw [hTmax]
              exact Nat.pow_log_le_self 2 (by omega)
        have hdivmono : (N / 2 ^ t : ℕ) ≤ (N / 2 ^ t₀ : ℕ) :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) ht.1) (by positivity)
        have hBA : ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) ≤ (N : ℝ) := by
          rw [hcard]
          exact_mod_cast h2tN
        have hdiv2 : ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            ≤ ((((N / 2 ^ t₀ : ℕ)) / (q / 2) + 1 : ℕ) : ℝ) := by
          have : ((N / 2 ^ t : ℕ)) / (q / 2) ≤ ((N / 2 ^ t₀ : ℕ)) / (q / 2) :=
            Nat.div_le_div_right hdivmono
          exact_mod_cast Nat.add_le_add_right this 1
        have hmono : Real.log N ^ 2 * (((N / 2 ^ t : ℕ) : ℝ) + 1)
            * (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
              + 2 * ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                  + 4 * q * (1 + Real.log (2 * q))))
            ≤ Mom := by
          rw [hMom]
          have hf1 : (((N / 2 ^ t : ℕ) : ℝ) + 1) ≤ (((N / 2 ^ t₀ : ℕ) : ℝ) + 1) := by
            have : ((N / 2 ^ t : ℕ) : ℝ) ≤ ((N / 2 ^ t₀ : ℕ) : ℝ) := by exact_mod_cast hdivmono
            linarith
          have hf2 : (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
              + 2 * ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))
              ≤ ((N : ℝ) + 2 * ((((N / 2 ^ t₀ : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * N + 4 * q * (1 + Real.log (2 * q)))) := by
            have hq4 : (0 : ℝ) ≤ 4 * q * (1 + Real.log (2 * q)) :=
              mul_nonneg (by positivity) hL0
            have hinner2 : 2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                + 4 * q * (1 + Real.log (2 * q))
                ≤ 2 * (N : ℝ) + 4 * q * (1 + Real.log (2 * q)) := by linarith
            have h2a : (0 : ℝ) ≤ 2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                + 4 * q * (1 + Real.log (2 * q)) := by positivity
            have := mul_le_mul hdiv2 hinner2 h2a (by positivity)
            nlinarith [hBA]
          have h0a : (0 : ℝ) ≤ Real.log N ^ 2 := by positivity
          have h0b : (0 : ℝ) ≤ (((N / 2 ^ t : ℕ) : ℝ) + 1) := by positivity
          have h0c : (0 : ℝ) ≤ (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
              + 2 * ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                  + 4 * q * (1 + Real.log (2 * q)))) := by
            have : (0 : ℝ) ≤ 4 * q * (1 + Real.log (2 * q)) :=
              mul_nonneg (by positivity) hL0
            positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hf1 h0a) hf2 h0c (by positivity)
        calc (∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
              ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2
            ≤ ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) *
                ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
                  ‖∑ m ∈ Finset.Ioc V (N / d),
                    (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2 := by
              exact_mod_cast hcs
          _ ≤ ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ) *
                (Real.log N ^ 2 * (((N / 2 ^ t : ℕ) : ℝ) + 1)
                  * (((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                    + 2 * ((((N / 2 ^ t : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                      * (2 * ((2 ^ t + 2 ^ t - 2 ^ t : ℕ) : ℝ)
                        + 4 * q * (1 + Real.log (2 * q))))) :=
              mul_le_mul_of_nonneg_left hmom (by positivity)
          _ ≤ (N : ℝ) * Mom := by
              apply mul_le_mul hBA hmono _ (by positivity)
              have h0a : (0 : ℝ) ≤ Real.log N ^ 2 := by positivity
              have : (0 : ℝ) ≤ 4 * q * (1 + Real.log (2 * q)) :=
                mul_nonneg (by positivity) hL0
              positivity
    _ = ((Finset.Icc t₀ Tmax).card : ℝ) * Real.sqrt ((N : ℝ) * Mom) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt ((N : ℝ) * Mom) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have : (Finset.Icc t₀ Tmax).card ≤ Nat.log 2 N + 1 := by
          rw [Nat.card_Icc, hTmax]
          omega
        exact_mod_cast this

/-- **THE TIGHT S₄ BOUND** (Type-II, large-sieve strength): replaces the vacuous
    `S4_bound` (whose dyadic-boundary over-charge made the innermost factor `≥ N`,
    hence `‖S₄‖ ≥ N·log²N`, weaker than the trivial `ψ(N) ≈ N`) with the four-term
    geometric envelope from `s4_dyadic_assembly`. On a minor arc `P < q ≤ N/P` this is
    `≪ N·log²N/√P`, small enough to close the variance bound. -/
lemma S4_bound_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hU1 : 1 ≤ U) (hN1 : 1 ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
            * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ))) n : ℝ) : ℂ)
          * e ((n : ℝ) * α)‖
      ≤ Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N
              * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ) / Real.sqrt q
          + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
          + 6 * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
              * Real.sqrt (N * q * (1 + Real.log (2 * q)))) := by
  set c : ArithmeticFunction ℝ :=
    (μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U with hc
  set gAF : ArithmeticFunction ℝ := (Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ) with hgAF
  set ghat : ℕ → ℝ := fun m => if m ≤ N then gAF m else 0 with hghat
  set t₀ : ℕ := Nat.log 2 (U + 1) with ht₀
  set Nmax : ℕ := N / (V + 1) with hNmax
  set Tmax : ℕ := Nat.log 2 Nmax with hTmax
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 * q) := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have : (0 : ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
    linarith
  have hN0 : 0 < N := hN1
  have hghat0 : ∀ m, 0 ≤ ghat m := by
    intro m
    rw [hghat]
    dsimp only
    split
    · exact tail_conv_nonneg V m
    · exact le_refl 0
  have hghatG : ∀ m, ghat m ≤ Real.log N := by
    intro m
    rw [hghat]
    dsimp only
    split
    · rename_i hm
      calc gAF m ≤ Real.log m := tail_conv_le_log V m
        _ ≤ Real.log N := log_natCast_monotone hm
    · exact log_natCast_nonneg N
  rw [show c * gAF = c * gAF from rfl,
    sum_Ioc_mul_weight_eq_sum_sum c gAF (fun n => e ((n : ℝ) * α)) N]
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ∑ m ∈ Finset.Ioc 0 (N / d), (gAF m : ℂ) * e (((d * m : ℕ) : ℝ) * α)
      = ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    have step1 : ∑ m ∈ Finset.Ioc 0 (N / d), (gAF m : ℂ) * e (((d * m : ℕ) : ℝ) * α)
        = ∑ m ∈ Finset.Ioc 0 (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      have hmN : m ≤ N := le_trans hm.2 (Nat.div_le_self N d)
      rw [hghat]
      dsimp only
      rw [if_pos hmN]
      congr 1
      exact congrArg e (by push_cast; ring)
    rw [step1]
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Ioc] at hm ⊢
      omega
    · intro m hm hnot
      simp only [Finset.mem_Ioc] at hm hnot
      have hmV : m ≤ V := by omega
      have hz : ghat m = 0 := by
        rw [hghat]
        dsimp only
        split
        · exact tail_conv_eq_zero_of_le V m hmV
        · rfl
      rw [hz]
      simp
  rw [Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])]
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖(c d : ℂ) * ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ (if U < d then
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ else 0) := by
    intro d _
    by_cases hdU : U < d
    · rw [if_pos hdU, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := abs_moebius_tail_le_one U d
      rw [hc]
      calc |(((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U) d)| *
            ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
          ≤ 1 * ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := one_mul _
    · rw [if_neg hdU]
      have hz : c d = 0 := by
        rw [hc]
        exact moebius_tail_eq_zero_of_le U d (by omega)
      rw [hz]
      simp
  calc ‖∑ d ∈ Finset.Ioc 0 N, (c d : ℂ) *
        ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          ‖(c d : ℂ) * ∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (if U < d then
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Ioc U N,
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun d _ => rfl)
        ext d
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        omega
    _ = ∑ d ∈ Finset.Ioc U Nmax,
          ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ := by
        refine (Finset.sum_subset
          (Finset.Ioc_subset_Ioc_right (Nat.div_le_self N (V + 1))) ?_).symm
        intro d hd hnotin
        simp only [Finset.mem_Ioc] at hd hnotin
        have hdNmax : Nmax < d := by
          by_contra hcon
          push_neg at hcon
          exact hnotin ⟨hd.1, hcon⟩
        have hd0 : 0 < d := by omega
        have hNlt : N < d * (V + 1) :=
          (Nat.div_lt_iff_lt_mul (by omega : 0 < V + 1)).mp hdNmax
        have hNdV : N / d ≤ V := by
          have : N / d < V + 1 :=
            (Nat.div_lt_iff_lt_mul hd0).mpr (by rw [Nat.mul_comm]; exact hNlt)
          omega
        have hempty : Finset.Ioc V (N / d) = ∅ := Finset.Ioc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, norm_zero]
    _ ≤ Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N * ((Tmax - t₀ + 1 : ℕ) : ℝ) / Real.sqrt q
          + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
          + 6 * ((Tmax - t₀ + 1 : ℕ) : ℝ) * Real.sqrt (N * q * (1 + Real.log (2 * q)))) := by
        by_cases hcase : t₀ ≤ Tmax
        · have ht0pos : 1 ≤ t₀ := by
            rw [ht₀]
            exact Nat.log_pos (by norm_num) (by omega)
          have hNmaxpos : 0 < Nmax := by
            rcases Nat.eq_zero_or_pos Nmax with h0 | h0
            · exfalso
              have hT0 : Tmax = 0 := by rw [hTmax, h0]; simp
              omega
            · exact h0
          have hUt0 : (U : ℝ) ≤ 2 * (2 : ℝ) ^ t₀ := by
            have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (U + 1)
            rw [← ht₀] at h
            have hUle : U ≤ 2 ^ (t₀ + 1) := by omega
            calc (U : ℝ) ≤ ((2 ^ (t₀ + 1) : ℕ) : ℝ) := by exact_mod_cast hUle
              _ = 2 * (2 : ℝ) ^ t₀ := by push_cast; ring
          have hTmaxN : (2 : ℝ) ^ Tmax ≤ (N : ℝ) / (V + 1) := by
            have h1 : (2 : ℕ) ^ Tmax ≤ Nmax := by
              rw [hTmax]; exact Nat.pow_log_le_self 2 (by omega)
            have hVR : (0 : ℝ) < (V : ℝ) + 1 := by positivity
            rw [le_div_iff₀ hVR]
            have h3 : Nmax * (V + 1) ≤ N := by rw [hNmax]; exact Nat.div_mul_le_self N (V + 1)
            calc (2 : ℝ) ^ Tmax * ((V : ℝ) + 1)
                ≤ (Nmax : ℝ) * ((V : ℝ) + 1) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  calc (2 : ℝ) ^ Tmax = ((2 ^ Tmax : ℕ) : ℝ) := by push_cast; ring
                    _ ≤ (Nmax : ℝ) := by exact_mod_cast h1
              _ = (((Nmax * (V + 1) : ℕ)) : ℝ) := by push_cast; ring
              _ ≤ (N : ℝ) := by exact_mod_cast h3
          have hcover : Finset.Ioc U Nmax ⊆
              (Finset.Icc t₀ Tmax).biUnion (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
            intro d hd
            simp only [Finset.mem_Ioc] at hd
            rw [Finset.mem_biUnion]
            refine ⟨Nat.log 2 d, ?_, ?_⟩
            · rw [Finset.mem_Icc, ht₀, hTmax]
              exact ⟨Nat.log_mono_right (by omega), Nat.log_mono_right hd.2⟩
            · rw [Finset.mem_Ico]
              refine ⟨Nat.pow_log_le_self 2 (by omega), ?_⟩
              have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d
              rw [pow_succ] at this
              omega
          have hdisj : (↑(Finset.Icc t₀ Tmax) : Set ℕ).PairwiseDisjoint
              (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)) := by
            intro t₁ _ t₂ _ hne
            apply Finset.disjoint_left.mpr
            intro h h1 h2
            simp only [Finset.mem_Ico] at h1 h2
            rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
            · have : (2 : ℕ) ^ (t₁ + 1) ≤ 2 ^ t₂ := Nat.pow_le_pow_right (by norm_num) hlt
              rw [pow_succ] at this; omega
            · have hlt2 : t₂ < t₁ := lt_of_le_of_ne hge (Ne.symm hne)
              have : (2 : ℕ) ^ (t₂ + 1) ≤ 2 ^ t₁ := Nat.pow_le_pow_right (by norm_num) hlt2
              rw [pow_succ] at this; omega
          calc ∑ d ∈ Finset.Ioc U Nmax,
                ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖
              ≤ ∑ d ∈ (Finset.Icc t₀ Tmax).biUnion
                  (fun t => Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t)),
                  ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
                Finset.sum_le_sum_of_subset_of_nonneg hcover (fun d _ _ => norm_nonneg _)
            _ = ∑ t ∈ Finset.Icc t₀ Tmax, ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
                  ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ :=
                Finset.sum_biUnion hdisj
            _ ≤ _ :=
                s4_dyadic_assembly N q V U t₀ Tmax hq hN1 hU1 hcase hUt0 hTmaxN
                  (fun t => ∑ d ∈ Finset.Ico (2 ^ t) (2 ^ t + 2 ^ t),
                    ‖∑ m ∈ Finset.Ioc V (N / d), (ghat m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖)
                  (fun t => Finset.sum_nonneg (fun d _ => norm_nonneg _))
                  (fun t ht => by
                    simp only [Finset.mem_Icc] at ht
                    have h2tN : (2 : ℕ) ^ t ≤ N := by
                      calc (2 : ℕ) ^ t ≤ 2 ^ Tmax := Nat.pow_le_pow_right (by norm_num) ht.2
                        _ ≤ Nmax := by rw [hTmax]; exact Nat.pow_log_le_self 2 (by omega)
                        _ ≤ N := Nat.div_le_self N (V + 1)
                    exact s4_block_hbnd a q N V t hq ha α hα ghat (Real.log N)
                      hghat0 hghatG hN1 h2tN)
        · have hle : Nmax ≤ U := by
            by_contra hcon
            push_neg at hcon
            exact hcase (by rw [ht₀, hTmax]; exact Nat.log_mono_right (by omega))
          rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
          apply mul_nonneg (Real.log_nonneg (by exact_mod_cast hN1))
          positivity

/-- **The S₃ bound**: the small Vaughan piece is at most `V·log V`. -/
lemma S3_bound (V N : ℕ) (α : ℝ) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ (V : ℝ) * Real.log V := by
  calc ‖∑ n ∈ Finset.Ioc 0 N, ((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ ∑ n ∈ Finset.Ioc 0 N, ‖((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 N, (if n ≤ V then Λ n else 0) := by
        apply Finset.sum_le_sum
        intro n _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (truncate_vonMangoldt_nonneg V n)]
        have he : ‖e ((n : ℝ) * α)‖ = 1 := by
          rw [e, Complex.norm_exp]
          have : (2 * (Real.pi : ℂ) * Complex.I * (((n : ℝ) * α : ℝ) : ℂ)).re = 0 := by
            simp [Complex.mul_re, Complex.mul_im]
          rw [this, Real.exp_zero]
        rw [he, mul_one, truncate_apply]
    _ ≤ ∑ n ∈ Finset.Ioc 0 V, Λ n := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
          omega
        · intro n _ _
          exact vonMangoldt_nonneg
    _ ≤ (V : ℝ) * Real.log V := sum_vonMangoldt_le V

/-- **THE VINOGRADOV SUP SKELETON**: `‖∑Λ(n)e(nα)‖ ≤ ‖S₁‖ + ‖S₂‖ + ‖S₃‖ + ‖S₄‖`
    for the truncated Vaughan pieces (each `‖Sᵢ‖` separately bounded by
    `S1_bound`/`S2_bound`/`S3_bound`/`S4_bound`). -/
lemma vinogradov_sup_skeleton (U V N : ℕ) (α : ℝ) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ ‖∑ n ∈ Finset.Ioc 0 N,
            (((truncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ)
              * e ((n : ℝ) * α)‖
        + ‖∑ n ∈ Finset.Ioc 0 N,
            (((truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V
                * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
        + ‖∑ n ∈ Finset.Ioc 0 N, ((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
        + ‖∑ n ∈ Finset.Ioc 0 N,
            (((((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
                * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ))) n : ℝ) : ℂ)
              * e ((n : ℝ) * α)‖ := by
  rw [vaughan_sum_decomposition (truncate (μ : ArithmeticFunction ℝ) U) (truncate Λ V)
    (fun n => e ((n : ℝ) * α)) N]
  have hassoc : ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
      * (Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)
      = ((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
      * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ)) := mul_assoc _ _ _
  rw [hassoc]
  set S1 : ℂ := ∑ n ∈ Finset.Ioc 0 N,
      (((truncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ)
        * e ((n : ℝ) * α) with hS1
  set S2 : ℂ := ∑ n ∈ Finset.Ioc 0 N,
      (((truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V
          * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * e ((n : ℝ) * α) with hS2
  set S3 : ℂ := ∑ n ∈ Finset.Ioc 0 N, ((truncate Λ V n : ℝ) : ℂ) * e ((n : ℝ) * α) with hS3
  set S4 : ℂ := ∑ n ∈ Finset.Ioc 0 N,
      (((((μ : ArithmeticFunction ℝ) - truncate (μ : ArithmeticFunction ℝ) U)
          * ((Λ - truncate Λ V) * (ζ : ArithmeticFunction ℝ))) n : ℝ) : ℂ)
        * e ((n : ℝ) * α) with hS4
  calc ‖S1 - S2 + S3 + S4‖
      ≤ ‖S1 - S2 + S3‖ + ‖S4‖ := norm_add_le _ _
    _ ≤ (‖S1 - S2‖ + ‖S3‖) + ‖S4‖ := by
        have := norm_add_le (S1 - S2) S3
        linarith
    _ ≤ ((‖S1‖ + ‖S2‖) + ‖S3‖) + ‖S4‖ := by
        have := norm_sub_le S1 S2
        linarith
    _ = ‖S1‖ + ‖S2‖ + ‖S3‖ + ‖S4‖ := by ring

/-- **THE VINOGRADOV MINOR-ARC SUP BOUND** — explicit, for any truncations `U, V`. -/
theorem vinogradov_sup (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hU : U ≤ N) (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          ((((Nat.log 2 U + 1 : ℕ) : ℝ) * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
            + 32 * U * (1 + Real.log (2 * q)) + 4 * N) + U)
        + Real.log (U * V) *
          (((Nat.log 2 (U * V) + 1 : ℕ) : ℝ)
              * (8 * N / q + 4 * q * (1 + Real.log (2 * q)))
            + 32 * (U * V) * (1 + Real.log (2 * q)) + 4 * N)
        + (V : ℝ) * Real.log V
        + ((Nat.log 2 N + 1 : ℕ) : ℝ) *
          Real.sqrt ((N : ℝ) * (Real.log N ^ 2
            * (((N / 2 ^ Nat.log 2 (U + 1) : ℕ) : ℝ) + 1)
            * ((N : ℝ) + 2 * ((((N / 2 ^ Nat.log 2 (U + 1) : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * N + 4 * q * (1 + Real.log (2 * q)))))) := by
  refine le_trans (vinogradov_sup_skeleton U V N α) ?_
  have h1 := S1_bound a q hq ha α hα U N hU
  have h2 := S2_bound a q hq ha α hα U V N hUV hUV1
  have h3 := S3_bound V N α
  have h4 := S4_bound a q hq ha α hα U V N
  linarith


lemma S2_bound_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V
            * (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ Real.log (U * V) *
          ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
            + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) := by
  set c : ArithmeticFunction ℝ := truncate (μ : ArithmeticFunction ℝ) U * truncate Λ V with hc
  have hlogUV0 : (0 : ℝ) ≤ Real.log (U * V) := by
    apply Real.log_nonneg
    exact_mod_cast hUV1
  -- regroup + collapse ζ + normalize the e-argument
  have hre : ∑ n ∈ Finset.Ioc 0 N,
      ((c * (ζ : ArithmeticFunction ℝ)) n : ℂ) * e ((n : ℝ) * α)
      = ∑ t ∈ Finset.Ioc 0 N, (c t : ℂ) *
          ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α)) := by
    rw [sum_Ioc_mul_weight_eq_sum_sum c (ζ : ArithmeticFunction ℝ)
      (fun n => e ((n : ℝ) * α)) N]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    rw [sum_Ioc_zeta_mul (fun m => e (((t * m : ℕ) : ℝ) * α)) (N / t)]
    apply Finset.sum_congr rfl
    intro m _
    exact congrArg e (by push_cast; ring)
  rw [hre]
  -- cap the sum over the support
  set cap : ℕ → ℝ := fun t =>
    (if (t : ℝ) * α - round ((t : ℝ) * α) = 0 then ((N / t : ℕ) : ℝ)
     else min ((N / t : ℕ) : ℝ) (1 / (2 * |(t : ℝ) * α - round ((t : ℝ) * α)|))) with hcap
  have hcap0 : ∀ t, 0 ≤ cap t := by
    intro t
    rw [hcap]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  have hterm : ∀ t ∈ Finset.Ioc 0 N,
      ‖(c t : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖
      ≤ (if t ≤ U * V then Real.log (U * V) * cap t else 0) := by
    intro t ht
    simp only [Finset.mem_Ioc] at ht
    by_cases htuv : t ≤ U * V
    · rw [if_pos htuv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |c t| ≤ Real.log (U * V) := by
        calc |c t| ≤ Real.log t := abs_truncate_mul_le_log U V t
          _ ≤ Real.log (U * V) := by
            apply Real.log_le_log (by exact_mod_cast ht.1)
            exact_mod_cast htuv
      have h2 : ‖∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖ ≤ cap t := by
        rw [hcap]
        exact exp_sum_Ioc_min_bound ((t : ℝ) * α) (N / t)
      exact mul_le_mul h1 h2 (norm_nonneg _) hlogUV0
    · rw [if_neg htuv]
      push_neg at htuv
      have hz : c t = 0 := truncate_mul_eq_zero_of_gt _ _ U V t htuv
      rw [hz]
      simp
  calc ‖∑ t ∈ Finset.Ioc 0 N, (c t : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖
      ≤ ∑ t ∈ Finset.Ioc 0 N,
          ‖(c t : ℂ) * ∑ m ∈ Finset.Ioc 0 (N / t), e ((m : ℝ) * ((t : ℝ) * α))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.Ioc 0 N, (if t ≤ U * V then Real.log (U * V) * cap t else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ t ∈ Finset.Ioc 0 (U * V), Real.log (U * V) * cap t := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun t _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hUV⟩, h2⟩
    _ = Real.log (U * V) * ∑ t ∈ Finset.Ioc 0 (U * V), cap t := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (U * V) *
        ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
          + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) := by
        apply mul_le_mul_of_nonneg_left _ hlogUV0
        have := min_sum_tight a q hq ha α hα N (U * V)
        rw [hcap]
        push_cast at this ⊢
        exact this

/-- `log` of a natural cast is nonneg (`log 0 = 0`). -/

lemma S1_bound_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U N : ℕ) (hU : U ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 N,
        (((truncate (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) n : ℝ) : ℂ)
          * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          (((2 * (N : ℝ) / q) * (1 + Real.log U)
            + ((U / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U) := by
  have hlogN0 : (0 : ℝ) ≤ Real.log (N + 1) := by
    apply Real.log_nonneg
    push_cast
    linarith
  set cap : ℕ → ℝ := fun t =>
    (if (t : ℝ) * α - round ((t : ℝ) * α) = 0 then ((N / t : ℕ) : ℝ)
     else min ((N / t : ℕ) : ℝ) (1 / (2 * |(t : ℝ) * α - round ((t : ℝ) * α)|))) with hcap
  have hcap0 : ∀ t, 0 ≤ cap t := by
    intro t
    rw [hcap]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  -- regroup
  rw [sum_Ioc_mul_weight_eq_sum_sum (truncate (μ : ArithmeticFunction ℝ) U)
    ArithmeticFunction.log (fun n => e ((n : ℝ) * α)) N]
  -- per-d inner bound
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      ‖∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) * (cap d + 1) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    set M : ℕ := N / d with hM
    set β : ℝ := (d : ℝ) * α with hβ
    -- normalize the argument and the log
    have hstep1 : ∑ m ∈ Finset.Ioc 0 M, ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)
        = ∑ m ∈ Finset.Ioc 0 M, ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [ArithmeticFunction.log_apply]
      congr 1
      exact congrArg e (by rw [hβ]; push_cast; ring)
    -- extend Ioc 0 M to range (M+1) (the m = 0 term vanishes)
    have hstep2 : ∑ m ∈ Finset.Ioc 0 M, ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β)
        = ∑ m ∈ Finset.range (M + 1), ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_Ioc] at hm
        simp only [Finset.mem_range]
        omega
      · intro m hm hnotm
        simp only [Finset.mem_range] at hm
        simp only [Finset.mem_Ioc] at hnotm
        have hm0 : m = 0 := by omega
        subst hm0
        simp
    -- the capped weight agrees with log on the range
    have hstep3 : ∑ m ∈ Finset.range (M + 1), ((Real.log m : ℝ) : ℂ) * e ((m : ℝ) * β)
        = ∑ m ∈ Finset.range (M + 1),
            ((Real.log ((min m (M + 1) : ℕ) : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * β) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_range] at hm
      rw [min_eq_left (by omega : m ≤ M + 1)]
    have habel := abel_exp_sum (fun m => Real.log ((min m (M + 1) : ℕ) : ℝ))
      (fun m => log_natCast_nonneg _)
      (by
        intro x y h
        exact log_natCast_monotone (by omega : min x (M + 1) ≤ min y (M + 1)))
      (Real.log ((M + 1 : ℕ) : ℝ))
      (fun m => by exact log_natCast_monotone (min_le_right m (M + 1)))
      β (M + 1)
    have hlogM : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log (N + 1) := by
      have h1 : (M : ℕ) + 1 ≤ N + 1 := by
        have : M ≤ N := hM ▸ Nat.div_le_self N d
        omega
      have := log_natCast_monotone (show (M + 1 : ℕ) ≤ (N + 1 : ℕ) from h1)
      push_cast at this ⊢
      exact this
    have hcapd : (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
        else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) ≤ cap d + 1 := by
      have h1 := cap_succ_le β M
      have h2 : (if β - round β = 0 then (M : ℝ)
          else min (M : ℝ) (1 / (2 * |β - round β|))) = cap d := by
        rw [hcap, hβ, hM]
      rw [h2] at h1
      exact h1
    have hcapnn : (0 : ℝ) ≤ (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
        else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
      split
      · positivity
      · exact le_min (by positivity) (by positivity)
    calc ‖∑ m ∈ Finset.Ioc 0 M, ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
        = ‖∑ m ∈ Finset.range (M + 1),
            ((Real.log ((min m (M + 1) : ℕ) : ℝ) : ℝ) : ℂ) * e ((m : ℝ) * β)‖ := by
          rw [hstep1, hstep2, hstep3]
      _ ≤ 2 * Real.log ((M + 1 : ℕ) : ℝ)
            * (if β - round β = 0 then ((M + 1 : ℕ) : ℝ)
               else min ((M + 1 : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
          have := habel
          push_cast at this ⊢
          exact this
      _ ≤ 2 * Real.log (N + 1) * (cap d + 1) := by
          apply mul_le_mul
          · have : (0:ℝ) ≤ 2 := by norm_num
            nlinarith [hlogM]
          · exact hcapd
          · exact hcapnn
          · positivity
  -- support + assembly
  have hterm : ∀ d ∈ Finset.Ioc 0 N,
      ‖(truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ (if d ≤ U then 2 * Real.log (N + 1) * (cap d + 1) else 0) := by
    intro d hd
    by_cases hdU : d ≤ U
    · rw [if_pos hdU, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |truncate (μ : ArithmeticFunction ℝ) U d| *
            ‖∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
              * e (((d * m : ℕ) : ℝ) * α)‖
          ≤ 1 * (2 * Real.log (N + 1) * (cap d + 1)) := by
            apply mul_le_mul (abs_truncate_moebius_le_one U d) (hinner d hd)
              (norm_nonneg _) (by norm_num)
        _ = 2 * Real.log (N + 1) * (cap d + 1) := one_mul _
    · rw [if_neg hdU]
      have hz : truncate (μ : ArithmeticFunction ℝ) U d = 0 := by
        rw [truncate_apply, if_neg hdU]
      rw [hz]
      simp
  calc ‖∑ d ∈ Finset.Ioc 0 N, (truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
        ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
          * e (((d * m : ℕ) : ℝ) * α)‖
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          ‖(truncate (μ : ArithmeticFunction ℝ) U d : ℂ) *
            ∑ m ∈ Finset.Ioc 0 (N / d), ((ArithmeticFunction.log m : ℝ) : ℂ)
              * e (((d * m : ℕ) : ℝ) * α)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, (if d ≤ U then 2 * Real.log (N + 1) * (cap d + 1) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ d ∈ Finset.Ioc 0 U, 2 * Real.log (N + 1) * (cap d + 1) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun t _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, le_trans h2 hU⟩, h2⟩
    _ = 2 * Real.log (N + 1) * (∑ d ∈ Finset.Ioc 0 U, cap d + U) := by
        have hsplit : ∀ d ∈ Finset.Ioc 0 U,
            2 * Real.log (N + 1) * (cap d + 1)
            = 2 * Real.log (N + 1) * cap d + 2 * Real.log (N + 1) := fun d _ => by ring
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 * Real.log (N + 1) *
        (((2 * (N : ℝ) / q) * (1 + Real.log U)
          + ((U / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have hd := min_sum_tight a q hq ha α hα N U
        have hsum : ∑ d ∈ Finset.Ioc 0 U, cap d
            ≤ (2 * (N : ℝ) / q) * (1 + Real.log U)
              + ((U / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))) := by
          calc ∑ d ∈ Finset.Ioc 0 U, cap d
              = ∑ h ∈ Finset.Ioc 0 U,
                  (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((N / h : ℕ) : ℝ)
                   else min ((N / h : ℕ) : ℝ)
                     (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) := by
                apply Finset.sum_congr rfl
                intro h _
                rw [hcap]
            _ ≤ _ := hd
        linarith

/-- Pointwise subtraction for arithmetic functions (no `sub_apply` in Mathlib). -/

theorem vinogradov_sup_tight (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hU : U ≤ N) (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          (((2 * (N : ℝ) / q) * (1 + Real.log U)
            + ((U / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U)
        + Real.log (U * V) *
          ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
            + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
        + (V : ℝ) * Real.log V
        + ((Nat.log 2 N + 1 : ℕ) : ℝ) *
          Real.sqrt ((N : ℝ) * (Real.log N ^ 2
            * (((N / 2 ^ Nat.log 2 (U + 1) : ℕ) : ℝ) + 1)
            * ((N : ℝ) + 2 * ((((N / 2 ^ Nat.log 2 (U + 1) : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * N + 4 * q * (1 + Real.log (2 * q)))))) := by
  refine le_trans (vinogradov_sup_skeleton U V N α) ?_
  have h1 := S1_bound_tight a q hq ha α hα U N hU
  have h2 := S2_bound_tight a q hq ha α hα U V N hUV hUV1
  have h3 := S3_bound V N α
  have h4 := S4_bound a q hq ha α hα U V N
  linarith

/-- **THE TIGHT VINOGRADOV SUP BOUND** — with the large-sieve Type-II estimate
    (`S4_bound_tight`). The Type-II term is now the four-term geometric envelope
    `logN·(N/√(V+1) + N·k/√q + N/√U + k·√(Nq))·polylog`, small on minor arcs, rather
    than the vacuous `√(N·Mom) ≳ N·log²N` of `vinogradov_sup_tight`. -/
theorem vinogradov_sup_tight2 (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (U V N : ℕ)
    (hU : U ≤ N) (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ 2 * Real.log (N + 1) *
          (((2 * (N : ℝ) / q) * (1 + Real.log U)
            + ((U / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U)
        + Real.log (U * V) *
          ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
            + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
        + (V : ℝ) * Real.log V
        + Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
            + Real.sqrt 32 * N
                * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ) / Real.sqrt q
            + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
            + 6 * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
                * Real.sqrt (N * q * (1 + Real.log (2 * q)))) := by
  have hN1 : 1 ≤ N := le_trans hUV1 hUV
  have hU1 : 1 ≤ U := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hUV1)
  refine le_trans (vinogradov_sup_skeleton U V N α) ?_
  have h1 := S1_bound_tight a q hq ha α hα U N hU
  have h2 := S2_bound_tight a q hq ha α hα U V N hUV hUV1
  have h3 := S3_bound V N α
  have h4 := S4_bound_tight a q hq ha α hα U V N hU1 hN1
  linarith

end VaughanDecomposition

end MinSum

open MinSum

set_option maxHeartbeats 4000000
/-!
# The minor-arc `minorCsup` asymptotic bound (Phase D — minor smallness)

`minorCsup_bound`: for `U=V=P` with `P^3 <= N` and `P*Q <= N`,
  `minorCsup N P P P Q <= 300 * N * (log N + 2)^3 / sqrt P`.
The `N * polylog / sqrt P` bound that closes the minor L4 smallness once `P = (log N)^B`,
`B >= 8`. Heavy to elaborate (~576s) so kept in its OWN file; imported into
`MinorArcExpSum.lean` as the labeled axiom `minorCsup_bound` (discharged at Phase-F concat;
the `minorCsup` def here is duplicated verbatim, defeq to MinorArcExpSum's).
Pinned leanprover/lean4:v4.31.0.
-/
open Finset
namespace MinorArc


/-- `Nat.log 2 N ≤ 2·log N`. -/
lemma natlog2_le_two_log (N : ℕ) (hN : 2 ≤ N) : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log N := by
  have hself : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hlog : ((Nat.log 2 N : ℝ)) * Real.log 2 ≤ Real.log N := by
    have h1 : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by exact_mod_cast hself)
    rwa [Real.log_pow] at h1
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hk0 : (0:ℝ) ≤ ((Nat.log 2 N : ℕ) : ℝ) := by positivity
  nlinarith [hlog, hlog2, hk0, mul_nonneg hk0 (show (0:ℝ) ≤ Real.log 2 - 1/2 by linarith)]

-- abstract group bounds (over abstract reals — light to elaborate, instantiated below)
lemma csup_g1 (a b c d p q Z L : ℝ)
    (ha : a ≤ L) (ha0 : 0 ≤ a) (hb : b ≤ 2 * Z) (hc : 1 + c ≤ L) (hc0 : 0 ≤ 1 + c)
    (hpq : 16 * p + 4 * q ≤ 20 * Z) (hd : 2 + d ≤ 2 * L) (hd0 : 0 ≤ 2 + d) (hp : p ≤ Z * L)
    (hZ0 : 0 ≤ Z) (hL1 : 1 ≤ L) :
    2 * a * (b * (1 + c) + (16 * p + 4 * q) * (2 + d) + p) ≤ 90 * (Z * L ^ 3) := by
  have hA : b * (1 + c) ≤ 2 * (Z * L) := by
    calc b * (1 + c) ≤ (2 * Z) * L := mul_le_mul hb hc hc0 (by linarith)
      _ = 2 * (Z * L) := by ring
  have hBb : (16 * p + 4 * q) * (2 + d) ≤ 40 * (Z * L) := by
    calc (16 * p + 4 * q) * (2 + d) ≤ (20 * Z) * (2 * L) := mul_le_mul hpq hd hd0 (by linarith)
      _ = 40 * (Z * L) := by ring
  have hin : b * (1 + c) + (16 * p + 4 * q) * (2 + d) + p ≤ 43 * (Z * L) := by
    nlinarith [hA, hBb, hp]
  calc 2 * a * (b * (1 + c) + (16 * p + 4 * q) * (2 + d) + p)
      ≤ 2 * a * (43 * (Z * L)) := by apply mul_le_mul_of_nonneg_left hin (by linarith)
    _ ≤ (2 * L) * (43 * (Z * L)) := by apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 86 * (Z * L ^ 2) := by ring
    _ ≤ 90 * (Z * L ^ 3) := by
        nlinarith [mul_nonneg (mul_nonneg hZ0 (sq_nonneg L)) (show (0:ℝ) ≤ 90 * L - 86 by linarith)]

lemma csup_g2 (b cc d p q Z L : ℝ)
    (hf : cc ≤ 2 * L) (hf0 : 0 ≤ cc) (hb : b ≤ 2 * Z) (hc : 1 + cc ≤ 2 * L) (hc0 : 0 ≤ 1 + cc)
    (hpq : 16 * (p * p) + 4 * q ≤ 20 * Z) (hd : 2 + d ≤ 2 * L) (hd0 : 0 ≤ 2 + d)
    (hZ0 : 0 ≤ Z) (hL1 : 1 ≤ L) :
    cc * (b * (1 + cc) + (16 * (p * p) + 4 * q) * (2 + d)) ≤ 90 * (Z * L ^ 3) := by
  have hA : b * (1 + cc) ≤ 4 * (Z * L) := by
    calc b * (1 + cc) ≤ (2 * Z) * (2 * L) := mul_le_mul hb hc hc0 (by linarith)
      _ = 4 * (Z * L) := by ring
  have hBb : (16 * (p * p) + 4 * q) * (2 + d) ≤ 40 * (Z * L) := by
    calc (16 * (p * p) + 4 * q) * (2 + d) ≤ (20 * Z) * (2 * L) := mul_le_mul hpq hd hd0 (by linarith)
      _ = 40 * (Z * L) := by ring
  have hin : b * (1 + cc) + (16 * (p * p) + 4 * q) * (2 + d) ≤ 44 * (Z * L) := by
    nlinarith [hA, hBb]
  calc cc * (b * (1 + cc) + (16 * (p * p) + 4 * q) * (2 + d))
      ≤ cc * (44 * (Z * L)) := by apply mul_le_mul_of_nonneg_left hin hf0
    _ ≤ (2 * L) * (44 * (Z * L)) := by apply mul_le_mul_of_nonneg_right hf (by positivity)
    _ = 88 * (Z * L ^ 2) := by ring
    _ ≤ 90 * (Z * L ^ 3) := by
        nlinarith [mul_nonneg (mul_nonneg hZ0 (sq_nonneg L)) (show (0:ℝ) ≤ 90 * L - 88 by linarith)]

lemma csup_g4 (a t1 t2 t3 t4 Z L : ℝ)
    (ha : a ≤ L) (ha0 : 0 ≤ a) (h1 : t1 ≤ 16 * Z) (h2 : t2 ≤ 12 * (Z * L))
    (h3 : t3 ≤ 64 * (Z * L)) (h4 : t4 ≤ 12 * (Z * L ^ 2)) (hZ0 : 0 ≤ Z) (hL1 : 1 ≤ L) :
    a * (t1 + t2 + t3 + t4) ≤ 110 * (Z * L ^ 3) := by
  have hin : t1 + t2 + t3 + t4 ≤ 110 * (Z * L ^ 2) := by
    nlinarith [h1, h2, h3, h4, mul_nonneg hZ0 (show (0:ℝ) ≤ L ^ 2 - 1 by nlinarith [hL1]),
      mul_nonneg (mul_nonneg hZ0 (show (0:ℝ) ≤ L by linarith)) (show (0:ℝ) ≤ L - 1 by linarith)]
  calc a * (t1 + t2 + t3 + t4) ≤ a * (110 * (Z * L ^ 2)) := mul_le_mul_of_nonneg_left hin ha0
    _ ≤ L * (110 * (Z * L ^ 2)) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = 110 * (Z * L ^ 3) := by ring

/-- **The minor-arc `Csup` asymptotic**: for `U=V=P` with `P³ ≤ N` and `P·Q ≤ N`,
    `minorCsup ≤ 200·N·(log N + 2)³/√P` — the `N/√P·polylog` bound that closes the minor
    L⁴ smallness once `P = (log N)^B`, `B ≥ 8`. -/
lemma minorCsup_bound (N P Q : ℕ) (hP2 : 2 ≤ P) (hPN : P ^ 3 ≤ N) (hPQ : P * Q ≤ N) :
    minorCsup N P P P Q ≤ 300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P := by
  have hP1 : 1 ≤ P := by omega
  have hPR : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP2
  have hN8 : 8 ≤ N := le_trans (by norm_num : (8:ℕ) ≤ 2^3) (le_trans (Nat.pow_le_pow_left hP2 3) hPN)
  have hNR : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hPcube : (P : ℝ) ≤ (P : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith [hPR]
    calc (P : ℝ) = P * 1 := by ring
      _ ≤ P * P ^ 2 := by apply mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = P ^ 3 := by ring
  have hPNR : (P : ℝ) ≤ (N : ℝ) := le_trans hPcube (by exact_mod_cast hPN)
  have hPQR : (P : ℝ) * Q ≤ N := by exact_mod_cast hPQ
  have hQ0R : (0:ℝ) ≤ (Q:ℝ) := by positivity
  have hQR : (Q : ℝ) ≤ N := by
    nlinarith [hPQR, hPR, hQ0R, mul_nonneg (show (0:ℝ) ≤ (P:ℝ) - 1 by linarith) hQ0R]
  have hsP1 : (1 : ℝ) ≤ Real.sqrt P := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsPpos : (0 : ℝ) < Real.sqrt P := by linarith
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogNP : Real.log P ≤ Real.log N := Real.log_le_log (by linarith) hPNR
  have hlogQN : Real.log Q ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ0
    · simp [hQ0]; positivity
    · exact Real.log_le_log (by exact_mod_cast hQ0) hQR
  have hlog2QN : Real.log (2 * (Q:ℝ)) ≤ Real.log N + 1 := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ0
    · simp [hQ0]; linarith
    · have : Real.log (2 * (Q:ℝ)) = Real.log 2 + Real.log Q := Real.log_mul (by norm_num) (by
        exact_mod_cast hQ0.ne')
      rw [this]
      nlinarith [hlogQN, Real.log_two_lt_d9]
  -- √-helpers (all from P³ ≤ N, PQ ≤ N)
  have hPcubeR : (P : ℝ) ^ 3 ≤ N := by exact_mod_cast hPN
  have hsqrtN : Real.sqrt N ≤ N := by
    have h : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hNR])
    rwa [Real.sqrt_sq (by positivity)] at h
  have hPsP : (P : ℝ) * Real.sqrt P ≤ N := by
    have h : (P : ℝ) * Real.sqrt P = Real.sqrt ((P : ℝ) ^ 3) := by
      rw [show (P : ℝ) ^ 3 = (P : ℝ) ^ 2 * P by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
    rw [h]
    exact le_trans (Real.sqrt_le_sqrt hPcubeR) hsqrtN
  have hP2sP : (P : ℝ) ^ 2 * Real.sqrt P ≤ N := by
    have h : (P : ℝ) ^ 2 * Real.sqrt P = Real.sqrt ((P : ℝ) ^ 5) := by
      rw [show (P : ℝ) ^ 5 = ((P : ℝ) ^ 2) ^ 2 * P by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
    rw [h]
    have hP5 : (P : ℝ) ^ 5 ≤ (N : ℝ) ^ 2 := by
      have h6 : ((P : ℝ) ^ 3) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hPcubeR 2
      nlinarith [h6, mul_nonneg (pow_nonneg (show (0:ℝ) ≤ (P:ℝ) by linarith) 5)
        (show (0:ℝ) ≤ (P:ℝ) - 1 by linarith)]
    calc Real.sqrt ((P : ℝ) ^ 5) ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt hP5
      _ = N := Real.sqrt_sq (by positivity)
  have hsqrtPsq : Real.sqrt P / P = 1 / Real.sqrt P := by
    rw [div_eq_div_iff (ne_of_gt (show (0:ℝ) < (P:ℝ) by linarith)) (ne_of_gt hsPpos), one_mul]
    exact Real.mul_self_sqrt (by linarith)
  have hQsP : (Q : ℝ) * Real.sqrt P ≤ N := by
    have hQle : (Q : ℝ) ≤ N / P := by rw [le_div_iff₀ (by linarith)]; nlinarith [hPQR]
    calc (Q : ℝ) * Real.sqrt P ≤ (N / P) * Real.sqrt P :=
          mul_le_mul_of_nonneg_right hQle (Real.sqrt_nonneg _)
      _ = N * (Real.sqrt P / P) := by ring
      _ = N * (1 / Real.sqrt P) := by rw [hsqrtPsq]
      _ ≤ N * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [div_le_one hsPpos]; exact hsP1
      _ = N := by ring
  -- yardstick facts
  set L : ℝ := Real.log N + 2 with hLdef
  have hL2 : (2 : ℝ) ≤ L := by rw [hLdef]; linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  set Y : ℝ := (N : ℝ) * L ^ 3 / Real.sqrt P with hYdef
  have hYpos : (0 : ℝ) ≤ Y := by rw [hYdef]; positivity
  -- helper: X ≤ c·Y  from  X·√P ≤ c·N·L³
  have hbnd : ∀ (X c : ℝ), 0 ≤ c → X * Real.sqrt P ≤ c * (N * L ^ 3) → X ≤ c * Y := by
    intro X c hc hX
    rw [hYdef, show c * ((N : ℝ) * L ^ 3 / Real.sqrt P) = c * (N * L ^ 3) / Real.sqrt P by ring,
      le_div_iff₀ hsPpos]
    exact hX
  have hlog1P : (1 : ℝ) + Real.log P ≤ L := by rw [hLdef]; linarith [hlogNP]
  have hlogN1 : Real.log (↑N + 1) ≤ L := by
    rw [hLdef]
    have : Real.log (↑N + 1) ≤ Real.log (2 * N) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    nlinarith [this, Real.log_two_lt_d9]
  have hlog2Q_L : (2 : ℝ) + Real.log (2 * (Q : ℝ)) ≤ 2 * L := by rw [hLdef]; linarith [hlog2QN]
  have hlogPP : (1 : ℝ) + Real.log (↑P * ↑P) ≤ 2 * L := by
    rw [Real.log_mul (by positivity) (by positivity)]; rw [hLdef]; linarith [hlogNP]
  have hlogPP2 : Real.log (↑P * ↑P) ≤ 2 * L := by
    rw [Real.log_mul (by positivity) (by positivity)]; rw [hLdef]; linarith [hlogNP]
  have hlogN_L : Real.log N ≤ L := by rw [hLdef]; linarith
  have hlogP_L : Real.log P ≤ L := by rw [hLdef]; linarith [hlogNP]
  have hk_L : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 2 * L := by
    push_cast
    have := natlog2_le_two_log N (by omega)
    rw [hLdef]; linarith
  -- Z := N/√P, Y = Z·L³
  set Z : ℝ := (N : ℝ) / Real.sqrt P with hZdef
  have hZ0 : (0 : ℝ) ≤ Z := by rw [hZdef]; positivity
  have hYZ : Y = Z * L ^ 3 := by rw [hYdef, hZdef]; ring
  have hsPP : Real.sqrt P ≤ P := by
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ (P:ℝ) by linarith), hsP1]
  have hlog2Q_nonneg : (0 : ℝ) ≤ Real.log (2 * (Q : ℝ)) := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ0
    · simp [hQ0]
    · have hq1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ0
      exact Real.log_nonneg (by linarith)
  have h2NP : 2 * (N : ℝ) / P ≤ 2 * Z := by
    rw [hZdef, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) hsPpos hsPP) (by norm_num)
  have hPZ : (P : ℝ) ≤ Z := by rw [hZdef, le_div_iff₀ hsPpos]; exact hPsP
  have hP2Z : (P : ℝ) ^ 2 ≤ Z := by rw [hZdef, le_div_iff₀ hsPpos]; exact hP2sP
  have hQZ : (Q : ℝ) ≤ Z := by rw [hZdef, le_div_iff₀ hsPpos]; exact hQsP
  have hlogP0 : (0 : ℝ) ≤ Real.log P := Real.log_nonneg (by linarith)
  have h2Q0 : (0 : ℝ) ≤ 2 + Real.log (2 * (Q : ℝ)) := by linarith [hlog2Q_nonneg]
  have hLL2 : L ≤ L ^ 2 := by nlinarith [hL1]
  have hZL : Z ≤ Z * L := by nlinarith [hZ0, hL1]
  have hZL2 : Z * L ^ 2 ≤ Y := by
    rw [hYZ]
    have : L ^ 2 ≤ L ^ 3 := by nlinarith [hL1, sq_nonneg L]
    nlinarith [hZ0, this]
  have hZL1 : Z * L ≤ Y := le_trans (by nlinarith [hZ0, hLL2]) hZL2
  -- √(NQL) ≤ Z·L
  have hsqNQL : Real.sqrt ((N : ℝ) * Q * (1 + Real.log (2 * (Q : ℝ)))) ≤ Z * L := by
    have harg : (N : ℝ) * Q * (1 + Real.log (2 * (Q : ℝ))) ≤ (Z * L) ^ 2 := by
      have hNQ : (N : ℝ) * Q ≤ Z ^ 2 := by
        rw [hZdef, div_pow, le_div_iff₀ (by positivity), Real.sq_sqrt (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left hPQR (show (0:ℝ) ≤ (N:ℝ) by positivity)]
      have h1L : (1 : ℝ) + Real.log (2 * (Q : ℝ)) ≤ L ^ 2 := by
        have h1 : (1 : ℝ) + Real.log (2 * (Q : ℝ)) ≤ L := by rw [hLdef]; linarith [hlog2QN]
        linarith [h1, hLL2]
      have hpos1 : (0:ℝ) ≤ 1 + Real.log (2 * (Q:ℝ)) := by linarith [hlog2Q_nonneg]
      calc (N : ℝ) * Q * (1 + Real.log (2 * (Q : ℝ)))
          ≤ Z ^ 2 * L ^ 2 := mul_le_mul hNQ h1L hpos1 (by positivity)
        _ = (Z * L) ^ 2 := by ring
    calc Real.sqrt ((N : ℝ) * Q * (1 + Real.log (2 * (Q : ℝ))))
        ≤ Real.sqrt ((Z * L) ^ 2) := Real.sqrt_le_sqrt harg
      _ = Z * L := Real.sqrt_sq (by positivity)
  -- √(P+1) ≥ √P
  have hsqP1 : (N : ℝ) / Real.sqrt (↑P + 1) ≤ Z := by
    rw [hZdef]
    exact div_le_div_of_nonneg_left (by positivity) hsPpos (Real.sqrt_le_sqrt (by linarith))
  -- √(1+log2Q) ≤ L
  have hsq1L : Real.sqrt (1 + Real.log (2 * (Q : ℝ))) ≤ L := by
    rw [show L = Real.sqrt (L ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    have h1 : (1 : ℝ) + Real.log (2 * (Q : ℝ)) ≤ L := by rw [hLdef]; linarith [hlog2QN]
    linarith [h1, hLL2]
  -- assemble via abstract group lemmas (light instantiations)
  have hlogN10 : (0 : ℝ) ≤ Real.log (↑N + 1) := by
    have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    exact Real.log_nonneg (by linarith)
  have hlogPP0 : (0 : ℝ) ≤ Real.log (↑P * ↑P) := Real.log_nonneg (by nlinarith [hPR])
  have hZL3 : (0 : ℝ) ≤ Z * L ^ 3 := by rw [← hYZ]; exact hYpos
  have hk0 : (0 : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
  have hs10 : Real.sqrt 10 ≤ 4 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs32 : Real.sqrt 32 ≤ 6 := by
    rw [show (6 : ℝ) = Real.sqrt 36 by rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hB1 := csup_g1 (Real.log (↑N + 1)) (2 * ↑N / ↑P) (Real.log ↑P) (Real.log (2 * ↑Q)) ↑P ↑Q Z L
    hlogN1 hlogN10 h2NP hlog1P (by linarith [hlogP0]) (by linarith [hPZ, hQZ]) hlog2Q_L h2Q0
    (le_trans hPZ hZL) hZ0 hL1
  have hB2 := csup_g2 (2 * ↑N / ↑P) (Real.log (↑P * ↑P)) (Real.log (2 * ↑Q)) ↑P ↑Q Z L
    hlogPP2 hlogPP0 h2NP hlogPP (by linarith [hlogPP0]) (by nlinarith [hP2Z, hQZ]) hlog2Q_L h2Q0
    hZ0 hL1
  have hB3 : (↑P : ℝ) * Real.log ↑P ≤ 4 * (Z * L ^ 3) := by
    have h1 : (↑P : ℝ) * Real.log ↑P ≤ Z * L := mul_le_mul hPZ hlogP_L hlogP0 hZ0
    nlinarith [h1, hZ0, hL1,
      mul_nonneg (mul_nonneg hZ0 (show (0:ℝ) ≤ L by linarith)) (show (0:ℝ) ≤ 4 * L ^ 2 - 1 by nlinarith [hL1])]
  have hT1 : 4 * Real.sqrt 10 * ↑N / Real.sqrt (↑P + 1) ≤ 16 * Z := by
    rw [show 4 * Real.sqrt 10 * ↑N / Real.sqrt (↑P + 1)
        = (4 * Real.sqrt 10) * ((N : ℝ) / Real.sqrt (↑P + 1)) by ring]
    calc (4 * Real.sqrt 10) * ((N : ℝ) / Real.sqrt (↑P + 1))
        ≤ (4 * Real.sqrt 10) * Z := mul_le_mul_of_nonneg_left hsqP1 (by positivity)
      _ ≤ 16 * Z := by nlinarith [hs10, hZ0]
  have hT2 : Real.sqrt 32 * ↑N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt ↑P ≤ 12 * (Z * L) := by
    rw [show Real.sqrt 32 * ↑N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt ↑P
        = (Real.sqrt 32 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) * Z by rw [hZdef]; ring]
    calc (Real.sqrt 32 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) * Z ≤ (6 * (2 * L)) * Z := by
          apply mul_le_mul_of_nonneg_right _ hZ0
          calc Real.sqrt 32 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
                nlinarith [hs32, hk0]
            _ ≤ 6 * (2 * L) := by nlinarith [hk_L]
      _ = 12 * (Z * L) := by ring
  have hT3 : 64 * ↑N * Real.sqrt (1 + Real.log (2 * ↑Q)) / Real.sqrt ↑P ≤ 64 * (Z * L) := by
    rw [show 64 * ↑N * Real.sqrt (1 + Real.log (2 * ↑Q)) / Real.sqrt ↑P
        = (64 * Real.sqrt (1 + Real.log (2 * ↑Q))) * Z by rw [hZdef]; ring]
    calc (64 * Real.sqrt (1 + Real.log (2 * ↑Q))) * Z ≤ (64 * L) * Z := by
          apply mul_le_mul_of_nonneg_right _ hZ0; nlinarith [hsq1L]
      _ = 64 * (Z * L) := by ring
  have hT4 : 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (↑N * ↑Q * (1 + Real.log (2 * ↑Q)))
      ≤ 12 * (Z * L ^ 2) := by
    calc 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (↑N * ↑Q * (1 + Real.log (2 * ↑Q)))
        ≤ 6 * (2 * L) * (Z * L) :=
          mul_le_mul (by nlinarith [hk_L]) hsqNQL (Real.sqrt_nonneg _) (by positivity)
      _ = 12 * (Z * L ^ 2) := by ring
  have hB4 := csup_g4 (Real.log ↑N) (4 * Real.sqrt 10 * ↑N / Real.sqrt (↑P + 1))
    (Real.sqrt 32 * ↑N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt ↑P)
    (64 * ↑N * Real.sqrt (1 + Real.log (2 * ↑Q)) / Real.sqrt ↑P)
    (6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (↑N * ↑Q * (1 + Real.log (2 * ↑Q)))) Z L
    hlogN_L hlogN0 hT1 hT2 hT3 hT4 hZ0 hL1
  unfold minorCsup
  rw [show (300 : ℝ) * ↑N * L ^ 3 / Real.sqrt ↑P = 300 * (Z * L ^ 3) by rw [hZdef]; ring]
  refine (add_le_add (add_le_add (add_le_add hB1 hB2) hB3) hB4).trans ?_
  linarith [hZL3]

end MinorArc

set_option maxHeartbeats 1000000

/-!
# Minor-arc exponential-sum bound

The geometric foundation of the circle method's **minor arcs** (the input, alongside
Vaughan's identity, to the Vinogradov bound on `∑ Λ(n) e(nα)` that drives almost-all
binary Goldbach — see `AlmostAllGoldbachReduction.lean`).

Main results:
  • `MinorArc.exp_sum_bound` — `‖∑_{n<N} e(nα)‖ ≤ 1 / (2 · dist(α, ℤ))`  for `α ∉ ℤ`,
    where `e(x) = exp(2πi x)` and `dist(α, ℤ) = |α - round α|`.
  • `MinorArc.char_orthogonality` — `∑_{n<q} e(an/q) = q·[q∣a]`, additive-character
    orthogonality (backbone of Gauss/Ramanujan sums + the major-arc singular series).
  • `MinorArc.integral_e` — `∫₀¹ e(kα) dα = [k=0]`, integral character orthogonality
    (circle-method main-term extractor; seed of the Parseval → large-sieve chain).
  • `MinorArc.parseval` — `∫₀¹ ‖∑_{n<N} aₙ e(nα)‖² dα = ∑_{n<N} ‖aₙ‖²`, the L² mean
    value of an exponential sum (the circle-method variance engine; large-sieve base case).

Proof route (all elementary, Mathlib-only):
  • `geom_exp_bound`   — for unit `z ≠ 1`, `‖∑_{n<N} zⁿ‖ ≤ 2/‖z-1‖`  (geometric sum + triangle).
  • `e_sub_one_norm`   — `‖e(α)-1‖ = 2|sin(πα)|`  (chord length, via `normSq` + double angle).
  • `exp_sum_le_sin`   — combine the two: `‖∑ e(nα)‖ ≤ 1/|sin(πα)|`.
  • `two_dist_le_abs_sin` — Jordan's inequality `2·dist(α,ℤ) ≤ |sin(πα)|`
                            (`Real.le_sin_mul` + `sin_add_int_mul_pi` periodicity).
  • `exp_sum_bound`    — chain them to the `dist` form.

`#print axioms MinorArc.exp_sum_bound` = `[propext, Classical.choice, Quot.sound]` — axiom-free.
Pinned: `leanprover/lean4:v4.31.0` + Mathlib v4.31.0.
-/

namespace MinorArc

open Finset







/-- `e` on an integer is `1`. -/
lemma e_int (a : ℤ) : e ((a : ℝ)) = 1 := (e_eq_one_iff _).mpr ⟨a, rfl⟩

/-- **Additive-character orthogonality**: `∑_{n<q} e(an/q) = q` if `q ∣ a`, else `0`.
    The backbone of Gauss/Ramanujan sums and the major-arc singular series. -/
lemma char_orthogonality (a : ℤ) (q : ℕ) (hq : q ≠ 0) :
    ∑ n ∈ Finset.range q, e ((a : ℝ) * n / q) = if (q : ℤ) ∣ a then (q : ℂ) else 0 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hterm : ∀ n : ℕ, e ((a : ℝ) * n / q) = (e ((a : ℝ) / q)) ^ n := by
    intro n
    rw [← e_pow, show (n : ℝ) * ((a : ℝ) / q) = (a : ℝ) * n / q by ring]
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  have hzq : (e ((a : ℝ) / q)) ^ q = 1 := by
    rw [← e_pow, show (q : ℝ) * ((a : ℝ) / q) = (a : ℝ) by field_simp]
    exact e_int a
  by_cases hdvd : (q : ℤ) ∣ a
  · obtain ⟨k, hk⟩ := hdvd
    have hz : e ((a : ℝ) / q) = 1 := by
      rw [show ((a : ℝ) / q) = (k : ℝ) by rw [hk]; push_cast; field_simp]
      exact e_int k
    rw [if_pos ⟨k, hk⟩]
    simp [hz]
  · have hzne : e ((a : ℝ) / q) ≠ 1 := by
      intro hz
      rw [e_eq_one_iff] at hz
      obtain ⟨k, hk⟩ := hz
      apply hdvd
      refine ⟨k, ?_⟩
      have h1 : (a : ℝ) = (k : ℝ) * (q : ℝ) := by rw [← hk]; field_simp
      have h2 : (a : ℝ) = (q : ℝ) * (k : ℝ) := by rw [h1]; ring
      exact_mod_cast h2
    rw [geom_sum_eq hzne, hzq, sub_self, zero_div, if_neg hdvd]

/-- **Integral character orthogonality**: `∫₀¹ e(kα) dα = 1` if `k = 0`, else `0`.
    The circle-method main-term extractor and the seed of the Parseval/large-sieve chain. -/
lemma integral_e (k : ℤ) :
    ∫ α in (0:ℝ)..1, e ((k : ℝ) * α) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have hcong : ∀ α ∈ Set.uIcc (0:ℝ) 1, e (((0 : ℤ) : ℝ) * α) = 1 := by
      intro α _; simp only [Int.cast_zero, zero_mul]; simp [e]
    rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_const]
    norm_num
  · rw [if_neg hk]
    set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) with hc
    have hcne : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (by exact_mod_cast hk)
    have hexpc : Complex.exp c = 1 := by
      rw [hc, Complex.exp_eq_one_iff]; exact ⟨k, by ring⟩
    have hderiv : ∀ α ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun α : ℝ => Complex.exp (c * ↑α) / c) (e ((k : ℝ) * α)) α := by
      intro α _
      have h1 : HasDerivAt (fun α : ℝ => c * (↑α : ℂ)) c α := by
        simpa using (Complex.ofRealCLM.hasDerivAt).const_mul c
      have h2 : HasDerivAt (fun α : ℝ => Complex.exp (c * ↑α))
          (Complex.exp (c * ↑α) * c) α := h1.cexp
      have h3 := h2.div_const c
      rw [mul_div_assoc, div_self hcne, mul_one] at h3
      have hval : e ((k : ℝ) * α) = Complex.exp (c * ↑α) := by
        rw [e, hc]; push_cast; ring_nf
      rw [hval]; exact h3
    have hcont : IntervalIntegrable (fun α : ℝ => e ((k : ℝ) * α)) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable; unfold e; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
    rw [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, hexpc]
    ring

/-- Orthogonality with natural indices: `∫₀¹ e((m−n)α) dα = [m = n]`. -/
lemma integral_e_nat (m n : ℕ) :
    ∫ α in (0:ℝ)..1, e (((m : ℝ) - n) * α) = if m = n then 1 else 0 := by
  have h := integral_e ((m : ℤ) - n)
  have hcast : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) = (m : ℝ) - n := by push_cast; ring
  rw [hcast] at h
  simpa only [sub_eq_zero, Int.natCast_inj] using h

/-- **Fourier extraction of the representation count**: the `n`-th Fourier coefficient of
    `S(α)²` is the twofold representation sum `R(n) = ∑_{m+k=n} aₘaₖ` — the bridge from
    the circle integral to Goldbach counts. -/
lemma fourier_coeff_sq (a : ℕ → ℂ) (N n : ℕ) :
    ∫ α in (0:ℝ)..1,
        (∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α))
      = ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          a p.1 * a p.2 := by
  have hint : ∀ m k : ℕ, IntervalIntegrable
      (fun α : ℝ => (a m * a k) * e ((((m : ℤ) + k - n : ℤ) : ℝ) * α))
      MeasureTheory.volume 0 1 := by
    intro m k
    apply Continuous.intervalIntegrable; unfold e; fun_prop
  have hint2 : ∀ m : ℕ, IntervalIntegrable
      (fun α : ℝ => ∑ k ∈ Finset.range N,
        (a m * a k) * e ((((m : ℤ) + k - n : ℤ) : ℝ) * α))
      MeasureTheory.volume 0 1 := by
    intro m
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro k _
    unfold e; fun_prop
  have hpt : ∀ α ∈ Set.uIcc (0:ℝ) 1,
      (∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α))
      = ∑ m ∈ Finset.range N, ∑ k ∈ Finset.range N,
          (a m * a k) * e ((((m : ℤ) + k - n : ℤ) : ℝ) * α) := by
    intro α _
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    have harg : (((m : ℤ) + k - n : ℤ) : ℝ) * α
        = (m : ℝ) * α + ((k : ℝ) * α + (-((n : ℝ) * α))) := by
      push_cast; ring
    rw [harg, ← e_add, ← e_add]
    ring
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_finsetSum (fun m _ => hint2 m)]
  have hinner : ∀ m ∈ Finset.range N,
      (∫ α in (0:ℝ)..1, ∑ k ∈ Finset.range N,
        (a m * a k) * e ((((m : ℤ) + k - n : ℤ) : ℝ) * α))
      = ∑ k ∈ Finset.range N, if m + k = n then a m * a k else 0 := by
    intro m _
    rw [intervalIntegral.integral_finsetSum (fun k _ => hint m k)]
    apply Finset.sum_congr rfl; intro k _
    rw [intervalIntegral.integral_const_mul, integral_e ((m : ℤ) + k - n)]
    have hiff : ((m : ℤ) + k - n = 0) ↔ (m + k = n) := by omega
    by_cases h : m + k = n
    · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
    · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_filter, Finset.sum_product]

/-- Parseval, complex pairing form: `∫₀¹ S·conj S = ∑ aₙ·conj aₙ`. -/
lemma parseval_aux (a : ℕ → ℂ) (N : ℕ) :
    ∫ α in (0:ℝ)..1,
        (∑ m ∈ Finset.range N, a m * e (m * α)) *
          (starRingEnd ℂ) (∑ n ∈ Finset.range N, a n * e (n * α))
      = ∑ n ∈ Finset.range N, a n * (starRingEnd ℂ) (a n) := by
  have hint : ∀ m n : ℕ, IntervalIntegrable
      (fun α : ℝ => (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α))
      MeasureTheory.volume 0 1 := by
    intro m n
    apply Continuous.intervalIntegrable; unfold e; fun_prop
  have hint2 : ∀ m : ℕ, IntervalIntegrable
      (fun α : ℝ => ∑ n ∈ Finset.range N,
        (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α))
      MeasureTheory.volume 0 1 := by
    intro m
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro n _
    unfold e; fun_prop
  have hpt : ∀ α ∈ Set.uIcc (0:ℝ) 1,
      (∑ m ∈ Finset.range N, a m * e (m * α)) *
        (starRingEnd ℂ) (∑ n ∈ Finset.range N, a n * e (n * α))
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α) := by
    intro α _
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro n _
    rw [map_mul, e_conj]
    have h1 : e ((m : ℝ) * α) * e (-((n : ℝ) * α)) = e (((m : ℝ) - n) * α) := by
      rw [e_add]; congr 1; ring
    calc a m * e ((m : ℝ) * α) * ((starRingEnd ℂ) (a n) * e (-((n : ℝ) * α)))
        = a m * (starRingEnd ℂ) (a n) * (e ((m : ℝ) * α) * e (-((n : ℝ) * α))) := by ring
      _ = a m * (starRingEnd ℂ) (a n) * e (((m : ℝ) - n) * α) := by rw [h1]
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_finsetSum (fun m _ => hint2 m)]
  have hinner : ∀ m ∈ Finset.range N,
      (∫ α in (0:ℝ)..1, ∑ n ∈ Finset.range N,
        (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α))
      = a m * (starRingEnd ℂ) (a m) := by
    intro m hm
    rw [intervalIntegral.integral_finsetSum (fun n _ => hint m n)]
    have hterm : ∀ n ∈ Finset.range N,
        (∫ α in (0:ℝ)..1, (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α))
        = (a m * (starRingEnd ℂ) (a n)) * (if m = n then 1 else 0) := by
      intro n _
      rw [intervalIntegral.integral_const_mul, integral_e_nat]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_eq_single m
      (fun n _ hne => by rw [if_neg (fun h => hne h.symm), mul_zero])
      (fun hm' => absurd hm hm')]
    rw [if_pos rfl, mul_one]
  exact Finset.sum_congr rfl hinner

/-- **Parseval / the L² mean value of an exponential sum**:
    `∫₀¹ ‖∑_{n<N} aₙ e(nα)‖² dα = ∑_{n<N} ‖aₙ‖²`. The engine of the circle-method
    variance computation and the base case of the large sieve. -/
lemma parseval (a : ℕ → ℂ) (N : ℕ) :
    ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range N, a n * e (n * α)‖ ^ 2
      = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have key := parseval_aux a N
  have hpt : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hL : (∫ α in (0:ℝ)..1,
      (∑ m ∈ Finset.range N, a m * e (m * α)) *
        (starRingEnd ℂ) (∑ n ∈ Finset.range N, a n * e (n * α)))
      = ((∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range N, a n * e (n * α)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro α _
    exact hpt _
  have hR : (∑ n ∈ Finset.range N, a n * (starRingEnd ℂ) (a n))
      = ((∑ n ∈ Finset.range N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun n _ => hpt (a n))
  rw [hL, hR] at key
  exact_mod_cast key







/-- `S(α)²` is itself a trig polynomial, with coefficients the representation sums
    `R(n) = ∑_{m+k=n} aₘaₖ`. -/
lemma sq_expsum_eq (a : ℕ → ℂ) (N : ℕ) (α : ℝ) :
    (∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2
      = ∑ n ∈ Finset.range (2 * N),
          (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) * e ((n : ℝ) * α) := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2)
      (t := Finset.range (2 * N))
      (fun p hp => by
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
        rw [Finset.mem_range]
        omega)]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have harg : (p.1 : ℝ) * α + (p.2 : ℝ) * α = (n : ℝ) * α := by
    rw [← hp.2]; push_cast; ring
  calc a p.1 * e ((p.1 : ℝ) * α) * (a p.2 * e ((p.2 : ℝ) * α))
      = a p.1 * a p.2 * (e ((p.1 : ℝ) * α) * e ((p.2 : ℝ) * α)) := by ring
    _ = a p.1 * a p.2 * e ((n : ℝ) * α) := by rw [e_add, harg]

/-- **The variance identity**: `∑_{n<2N} ‖R(n)‖² = ∫₀¹ ‖S(α)‖⁴ dα` — Parseval applied to
    the trig polynomial `S²`. The bridge between the minor-arc L⁴ bound and the
    sum-over-n variance that `almost_all_goldbach_of_variance` consumes. -/
lemma sum_repCoeff_sq_eq_L4 (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N),
        ‖∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          a p.1 * a p.2‖ ^ 2
      = ∫ α in (0:ℝ)..1, ‖∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)‖ ^ 4 := by
  calc ∑ n ∈ Finset.range (2 * N),
        ‖∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          a p.1 * a p.2‖ ^ 2
      = ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range (2 * N),
          (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) * e ((n : ℝ) * α)‖ ^ 2 :=
        (parseval (fun n => ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter
          (fun p => p.1 + p.2 = n), a p.1 * a p.2) (2 * N)).symm
    _ = ∫ α in (0:ℝ)..1, ‖(∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [sq_expsum_eq]
    _ = ∫ α in (0:ℝ)..1, ‖∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)‖ ^ 4 := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [norm_pow, ← pow_mul]

/-- **Variance = L² error**: for ANY candidate main term `c(n)`, the variance
    `∑_{n<2N} ‖R(n) − c(n)‖²` equals `∫₀¹ ‖S(α)² − C(α)‖² dα` where `C` is the trig
    polynomial with coefficients `c`. Reduces the Goldbach variance hypothesis to an
    L² bound on the circle, which the arc dichotomy then splits. -/
lemma variance_eq_L2_error (a c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      = ∫ α in (0:ℝ)..1,
          ‖(∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2
            - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2 := by
  calc ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      = ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range (2 * N),
          ((∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n) * e ((n : ℝ) * α)‖ ^ 2 :=
        (parseval (fun n => (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter
          (fun p => p.1 + p.2 = n), a p.1 * a p.2) - c n) (2 * N)).symm
    _ = ∫ α in (0:ℝ)..1,
          ‖(∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2
            - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [sq_expsum_eq]
        simp only [sub_mul, Finset.sum_sub_distrib]

open MeasureTheory in
/-- **Circle split**: the L² integral over `(0,1]` splits exactly into the minor-arc set
    and its complement (the major arcs). -/
lemma L2_circle_split (f : ℝ → ℂ) (hf : Continuous f) (m : Set ℝ)
    (hm : MeasurableSet m) (hsub : m ⊆ Set.Ioc (0:ℝ) 1) :
    ∫ α in (0:ℝ)..1, ‖f α‖ ^ 2
      = (∫ α in m, ‖f α‖ ^ 2) + ∫ α in Set.Ioc (0:ℝ) 1 \ m, ‖f α‖ ^ 2 := by
  have hi : IntegrableOn (fun α => ‖f α‖ ^ 2) (Set.Ioc (0:ℝ) 1) volume :=
    (hf.norm.pow 2).integrableOn_Ioc
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← setIntegral_union Set.disjoint_sdiff_right (measurableSet_Ioc.diff hm)
      (hi.mono_set hsub) (hi.mono_set Set.diff_subset),
    Set.union_diff_cancel hsub]

open MeasureTheory in
/-- **Elementary L² triangle bound on a set**: `∫_m ‖f−g‖² ≤ 2∫_m‖f‖² + 2∫_m‖g‖²`. -/
lemma L2_diff_le (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (m : Set ℝ)
    (hm : MeasurableSet m) (hsub : m ⊆ Set.Ioc (0:ℝ) 1) :
    ∫ α in m, ‖f α - g α‖ ^ 2
      ≤ 2 * (∫ α in m, ‖f α‖ ^ 2) + 2 * ∫ α in m, ‖g α‖ ^ 2 := by
  have hif : IntegrableOn (fun α => ‖f α‖ ^ 2) m volume :=
    ((hf.norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hig : IntegrableOn (fun α => ‖g α‖ ^ 2) m volume :=
    ((hg.norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hifg : IntegrableOn (fun α => ‖f α - g α‖ ^ 2) m volume :=
    (((hf.sub hg).norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hpt : ∀ α ∈ m, ‖f α - g α‖ ^ 2 ≤ 2 * ‖f α‖ ^ 2 + 2 * ‖g α‖ ^ 2 := by
    intro α _
    have h1 : ‖f α - g α‖ ≤ ‖f α‖ + ‖g α‖ := norm_sub_le _ _
    have h2 : ‖f α - g α‖ ^ 2 ≤ (‖f α‖ + ‖g α‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖f α‖ - ‖g α‖)]
  have hsum : IntegrableOn (fun α => 2 * ‖f α‖ ^ 2 + 2 * ‖g α‖ ^ 2) m volume := by
    exact (hif.const_mul 2).add (hig.const_mul 2)
  calc ∫ α in m, ‖f α - g α‖ ^ 2
      ≤ ∫ α in m, (2 * ‖f α‖ ^ 2 + 2 * ‖g α‖ ^ 2) :=
        setIntegral_mono_on hifg hsum hm hpt
    _ = 2 * (∫ α in m, ‖f α‖ ^ 2) + 2 * ∫ α in m, ‖g α‖ ^ 2 := by
        rw [integral_add (hif.const_mul 2) (hig.const_mul 2),
          integral_const_mul, integral_const_mul]

open MeasureTheory in
/-- L² mass on any sub-arc set is at most the full-circle L² mass. -/
lemma setL2_le_circle (f : ℝ → ℂ) (hf : Continuous f) (m : Set ℝ)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) :
    ∫ α in m, ‖f α‖ ^ 2 ≤ ∫ α in (0:ℝ)..1, ‖f α‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_mono_set ((hf.norm.pow 2).integrableOn_Ioc)
  · exact Filter.Eventually.of_forall (fun α => sq_nonneg ‖f α‖)
  · exact HasSubset.Subset.eventuallyLE hsub

lemma expsum_continuous (a : ℕ → ℂ) (N : ℕ) :
    Continuous (fun α : ℝ => ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)) := by
  apply continuous_finsetSum
  intro n _
  unfold e
  fun_prop

open MeasureTheory in
/-- General L⁴-on-a-set bound: sup on one factor, Parseval on the other. -/
lemma L4_set_bound (a : ℕ → ℂ) (N : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (Csup : ℝ)
    (hsup : ∀ α ∈ m, ‖∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)‖ ≤ Csup) :
    ∫ α in m, ‖(∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)) ^ 2‖ ^ 2
      ≤ Csup ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  set S := fun α : ℝ => ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α) with hS
  have hcont : Continuous S := expsum_continuous a N
  rcases Set.eq_empty_or_nonempty m with hempty | ⟨α₀, hα₀⟩
  · rw [hempty]
    simp only [Measure.restrict_empty, integral_zero_measure]
    exact mul_nonneg (sq_nonneg Csup) (Finset.sum_nonneg fun n _ => sq_nonneg _)
  have hCnn : 0 ≤ Csup := le_trans (norm_nonneg _) (hsup α₀ hα₀)
  have hint2 : IntegrableOn (fun α => ‖S α‖ ^ 2) m volume :=
    ((hcont.norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hint4 : IntegrableOn (fun α => ‖S α ^ 2‖ ^ 2) m volume := by
    exact (((hcont.pow 2).norm.pow 2).integrableOn_Ioc).mono_set hsub
  calc ∫ α in m, ‖S α ^ 2‖ ^ 2
      ≤ ∫ α in m, Csup ^ 2 * ‖S α‖ ^ 2 := by
        apply setIntegral_mono_on hint4 (hint2.const_mul _) hm
        intro α hα
        rw [norm_pow]
        have hsq : ‖S α‖ ^ 2 ≤ Csup ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hsup α hα) 2
        calc (‖S α‖ ^ 2) ^ 2 = ‖S α‖ ^ 2 * ‖S α‖ ^ 2 := by ring
          _ ≤ Csup ^ 2 * ‖S α‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = Csup ^ 2 * ∫ α in m, ‖S α‖ ^ 2 := by rw [integral_const_mul]
    _ ≤ Csup ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∫ α in m, ‖S α‖ ^ 2 ≤ ∫ α in (0:ℝ)..1, ‖S α‖ ^ 2 :=
              setL2_le_circle S hcont m hsub
          _ = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := parseval a N

open MeasureTheory in
/-- **THE VARIANCE ASSEMBLY**: for any coefficients `a`, main term `c`, and minor set `m`
    with sup bound `Csup`, the full variance is at most the (finished) minor contribution
    plus the major-arc L² integral — the SINGLE remaining analytic input. -/
theorem variance_le_of_arcs (a c : ℕ → ℂ) (N : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (Csup : ℝ)
    (hsup : ∀ α ∈ m, ‖∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)‖ ≤ Csup) :
    ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      ≤ 2 * (Csup ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2)
        + 2 * ∑ n ∈ Finset.range (2 * N), ‖c n‖ ^ 2
        + ∫ α in Set.Ioc (0:ℝ) 1 \ m,
            ‖(∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2
              - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2 := by
  have hScont : Continuous (fun α : ℝ => ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)) :=
    expsum_continuous a N
  have hCcont : Continuous (fun α : ℝ => ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)) :=
    expsum_continuous c (2 * N)
  have hEcont : Continuous (fun α : ℝ =>
      (∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2
        - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)) :=
    (hScont.pow 2).sub hCcont
  rw [variance_eq_L2_error a c N, L2_circle_split _ hEcont m hm hsub]
  have hminor : (∫ α in m,
      ‖(∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2
        - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2)
      ≤ 2 * (Csup ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2)
        + 2 * ∑ n ∈ Finset.range (2 * N), ‖c n‖ ^ 2 := by
    have h1 := L2_diff_le
      (fun α : ℝ =>
        (∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2)
      (fun α : ℝ =>
        ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α))
      (hScont.pow 2) hCcont m hm hsub
    have h2 := L4_set_bound a N m hm hsub Csup hsup
    have h3 : (∫ α in m, ‖∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2)
        ≤ ∑ n ∈ Finset.range (2 * N), ‖c n‖ ^ 2 := by
      calc (∫ α in m, ‖∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2)
          ≤ ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2 :=
            setL2_le_circle _ hCcont m hsub
        _ = ∑ n ∈ Finset.range (2 * N), ‖c n‖ ^ 2 := parseval c (2 * N)
    linarith
  linarith

open MeasureTheory in
/-- **Bessel's inequality on a sub-arc set**: the Fourier coefficients of `f` restricted
    to any measurable `m ⊆ (0,1]` satisfy `∑_{n<M} ‖∫_m f·e(−nα)‖² ≤ ∫_m ‖f‖²`.
    This is the lossless replacement for the crude main-term bound on minor arcs. -/
lemma bessel_minor (f : ℝ → ℂ) (hf : Continuous f) (m : Set ℝ)
    (hm : MeasurableSet m) (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (M : ℕ) :
    ∑ n ∈ Finset.range M, ‖∫ α in m, f α * e (-((n : ℝ) * α))‖ ^ 2
      ≤ ∫ α in m, ‖f α‖ ^ 2 := by
  set c : ℕ → ℂ := fun n => ∫ α in m, f α * e (-((n : ℝ) * α)) with hc
  set T : ℝ → ℂ := fun α => ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α) with hT
  have hTcont : Continuous T := expsum_continuous c M
  have hecont : ∀ n : ℕ, Continuous fun α : ℝ => e (-((n : ℝ) * α)) := by
    intro n
    unfold e
    fun_prop
  -- integrability workhorses on m
  have hInt : ∀ g : ℝ → ℂ, Continuous g → IntegrableOn g m volume := fun g hg =>
    (hg.integrableOn_Ioc).mono_set hsub
  have hIntR : ∀ g : ℝ → ℝ, Continuous g → IntegrableOn g m volume := fun g hg =>
    (hg.integrableOn_Ioc).mono_set hsub
  -- Key 1: ∫_m f·conj T = ∑ c n · conj (c n)
  have hkey1 : (∫ α in m, f α * (starRingEnd ℂ) (T α))
      = ∑ n ∈ Finset.range M, c n * (starRingEnd ℂ) (c n) := by
    have hexp : ∀ α : ℝ, f α * (starRingEnd ℂ) (T α)
        = ∑ n ∈ Finset.range M, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
      intro α
      rw [hT]
      dsimp only
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [map_mul, e_conj]
      ring
    calc (∫ α in m, f α * (starRingEnd ℂ) (T α))
        = ∫ α in m, ∑ n ∈ Finset.range M, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
          apply setIntegral_congr_fun hm
          intro α _
          exact hexp α
      _ = ∑ n ∈ Finset.range M, ∫ α in m, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
          apply integral_finset_sum
          intro n _
          exact (hInt _ ((hf.mul (hecont n)).const_mul _))
      _ = ∑ n ∈ Finset.range M, (starRingEnd ℂ) (c n) * ∫ α in m, f α * e (-((n : ℝ) * α)) := by
          apply Finset.sum_congr rfl
          intro n _
          exact integral_const_mul _ _
      _ = ∑ n ∈ Finset.range M, c n * (starRingEnd ℂ) (c n) := by
          apply Finset.sum_congr rfl
          intro n _
          have hfold : (∫ α in m, f α * e (-((n : ℝ) * α))) = c n := rfl
          rw [hfold]
          ring
  -- Key 2: the expansion of ∫_m ‖f − T‖²
  have hptwise : ∀ α : ℝ, ‖f α - T α‖ ^ 2
      = ‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re + ‖T α‖ ^ 2 := by
    intro α
    have h1 : (‖f α - T α‖ : ℝ) ^ 2 = ((f α - T α) * (starRingEnd ℂ) (f α - T α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h2 : (‖f α‖ : ℝ) ^ 2 = (f α * (starRingEnd ℂ) (f α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h3 : (‖T α‖ : ℝ) ^ 2 = (T α * (starRingEnd ℂ) (T α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hconjswap : (T α * (starRingEnd ℂ) (f α)).re = (f α * (starRingEnd ℂ) (T α)).re := by
      have : T α * (starRingEnd ℂ) (f α) = (starRingEnd ℂ) (f α * (starRingEnd ℂ) (T α)) := by
        rw [map_mul, Complex.conj_conj]
        ring
      rw [this, Complex.conj_re]
    rw [h1, h2, h3]
    have hexpand : (f α - T α) * (starRingEnd ℂ) (f α - T α)
        = f α * (starRingEnd ℂ) (f α) - f α * (starRingEnd ℂ) (T α)
          - T α * (starRingEnd ℂ) (f α) + T α * (starRingEnd ℂ) (T α) := by
      rw [map_sub]
      ring
    rw [hexpand]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hconjswap]
    ring
  have hIfT : IntegrableOn (fun α => (f α * (starRingEnd ℂ) (T α)).re) m volume := by
    apply hIntR
    exact (Complex.continuous_re.comp (hf.mul (Complex.continuous_conj.comp hTcont)))
  have hIf2 : IntegrableOn (fun α => ‖f α‖ ^ 2) m volume := hIntR _ (hf.norm.pow 2)
  have hIT2 : IntegrableOn (fun α => ‖T α‖ ^ 2) m volume := hIntR _ (hTcont.norm.pow 2)
  have hkey2 : (∫ α in m, ‖f α - T α‖ ^ 2)
      = (∫ α in m, ‖f α‖ ^ 2) - 2 * (∫ α in m, f α * (starRingEnd ℂ) (T α)).re
        + ∫ α in m, ‖T α‖ ^ 2 := by
    have hre : (∫ α in m, (f α * (starRingEnd ℂ) (T α)).re)
        = (∫ α in m, f α * (starRingEnd ℂ) (T α)).re := by
      have h := integral_re (hInt (fun α => f α * (starRingEnd ℂ) (T α))
        (hf.mul (Complex.continuous_conj.comp hTcont)))
      simpa [RCLike.re_to_complex] using h
    calc (∫ α in m, ‖f α - T α‖ ^ 2)
        = ∫ α in m, (‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re + ‖T α‖ ^ 2) := by
          apply setIntegral_congr_fun hm
          intro α _
          exact hptwise α
      _ = (∫ α in m, (‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re))
          + ∫ α in m, ‖T α‖ ^ 2 := by
          apply integral_add _ hIT2
          exact hIf2.sub (hIfT.const_mul 2)
      _ = (∫ α in m, ‖f α‖ ^ 2) - (∫ α in m, 2 * (f α * (starRingEnd ℂ) (T α)).re)
          + ∫ α in m, ‖T α‖ ^ 2 := by
          rw [integral_sub hIf2 (hIfT.const_mul 2)]
      _ = (∫ α in m, ‖f α‖ ^ 2) - 2 * (∫ α in m, f α * (starRingEnd ℂ) (T α)).re
          + ∫ α in m, ‖T α‖ ^ 2 := by
          rw [integral_const_mul, hre]
  -- Key 3: ∫_m ‖T‖² ≤ ∑ ‖c n‖²
  have hkey3 : (∫ α in m, ‖T α‖ ^ 2) ≤ ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
    calc (∫ α in m, ‖T α‖ ^ 2) ≤ ∫ α in (0:ℝ)..1, ‖T α‖ ^ 2 :=
          setL2_le_circle T hTcont m hsub
      _ = ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := parseval c M
  -- the cross term is the coefficient mass
  have hcross : (∫ α in m, f α * (starRingEnd ℂ) (T α)).re
      = ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
    rw [hkey1]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  -- combine: 0 ≤ ∫‖f−T‖² = ∫‖f‖² − 2∑‖c‖² + ∫_m‖T‖² ≤ ∫‖f‖² − ∑‖c‖²
  have hnonneg : (0:ℝ) ≤ ∫ α in m, ‖f α - T α‖ ^ 2 := by
    apply integral_nonneg
    intro α
    positivity
  rw [hkey2, hcross] at hnonneg
  linarith [hkey3]

open MeasureTheory in
/-- Splitting a continuous complex integrand over the circle into a sub-arc set and its
    complement. -/
lemma integral_circle_split (g : ℝ → ℂ) (hg : Continuous g) (m : Set ℝ)
    (hm : MeasurableSet m) (hsub : m ⊆ Set.Ioc (0:ℝ) 1) :
    ∫ α in (0:ℝ)..1, g α
      = (∫ α in m, g α) + ∫ α in Set.Ioc (0:ℝ) 1 \ m, g α := by
  have hi : IntegrableOn g (Set.Ioc (0:ℝ) 1) volume := hg.integrableOn_Ioc
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← setIntegral_union Set.disjoint_sdiff_right (measurableSet_Ioc.diff hm)
      (hi.mono_set hsub) (hi.mono_set Set.diff_subset),
    Set.union_diff_cancel hsub]

open MeasureTheory in
/-- **The lossless variance assembly**: the variance against ANY main term `c` is at most
    twice the minor-arc L⁴ integral plus twice the major-arc coefficient error — with NO
    loss on the main term (Bessel replaces the crude full-circle Parseval bound). The
    second sum is exactly the Siegel–Walfisz-grade object. -/
theorem variance_le_bessel (a : ℕ → ℂ) (N : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (c : ℕ → ℂ) :
    ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      ≤ 2 * (∫ α in m, ‖∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)‖ ^ 4)
        + 2 * ∑ n ∈ Finset.range (2 * N),
            ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m,
                (∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α)))
              - c n‖ ^ 2 := by
  set S : ℝ → ℂ := fun α => ∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α) with hS
  have hScont : Continuous S := expsum_continuous a N
  have hS2cont : Continuous (fun α => S α ^ 2) := hScont.pow 2
  have hgcont : ∀ n : ℕ, Continuous (fun α => S α ^ 2 * e (-((n : ℝ) * α))) := by
    intro n
    apply hS2cont.mul
    unfold e
    fun_prop
  -- coefficient split: R(n) = minor coefficient + major coefficient
  have hsplitn : ∀ n : ℕ,
      (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
        a p.1 * a p.2)
      = (∫ α in m, S α ^ 2 * e (-((n : ℝ) * α)))
        + ∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α)) := by
    intro n
    rw [← fourier_coeff_sq a N n]
    exact integral_circle_split _ (hgcont n) m hm hsub
  -- pointwise: ‖x + y − c‖² ≤ 2‖x‖² + 2‖y − c‖²
  have hpt : ∀ n ∈ Finset.range (2 * N),
      ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          a p.1 * a p.2) - c n‖ ^ 2
      ≤ 2 * ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
        + 2 * ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n‖ ^ 2 := by
    intro n _
    rw [hsplitn n]
    set x := ∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))
    set y := (∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n
    have hxy : x + (∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n
        = x + y := by ring
    rw [hxy]
    have htri : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    have hsq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]
  -- sum up and apply Bessel to the minor coefficients
  have hbessel : ∑ n ∈ Finset.range (2 * N),
      ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
      ≤ ∫ α in m, ‖S α‖ ^ 4 := by
    have hb := bessel_minor (fun α => S α ^ 2) hS2cont m hm hsub (2 * N)
    calc ∑ n ∈ Finset.range (2 * N), ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
        ≤ ∫ α in m, ‖S α ^ 2‖ ^ 2 := hb
      _ = ∫ α in m, ‖S α‖ ^ 4 := by
          apply setIntegral_congr_fun hm
          intro α _
          dsimp only
          rw [norm_pow, ← pow_mul]
  calc ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      ≤ ∑ n ∈ Finset.range (2 * N),
          (2 * ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
            + 2 * ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n‖ ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * (∑ n ∈ Finset.range (2 * N),
            ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2)
        + 2 * ∑ n ∈ Finset.range (2 * N),
            ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (∫ α in m, ‖S α‖ ^ 4)
        + 2 * ∑ n ∈ Finset.range (2 * N),
            ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n‖ ^ 2 := by
        have h2 : (0:ℝ) ≤ 2 := by norm_num
        linarith [mul_le_mul_of_nonneg_left hbessel h2]

/-- **Major-arc residue decomposition** — the entry point of the major-arc evaluation:
    at `α = a/q + β`, any weighted exponential sum regroups into the `q` residue classes,
    `∑ g(n)e(nα) = ∑_{r<q} e(ra/q)·∑_{n≡r(q)} g(n)e(nβ)` — reducing the window evaluation
    to AP-restricted sums (the `WeakPNT_AP` shape) twisted by the smooth `e(nβ)`. -/
lemma major_arc_residue_decomp (g : ℕ → ℂ) (N : ℕ) (a : ℤ) (q : ℕ) (hq : 0 < q) (β : ℝ) :
    ∑ n ∈ Finset.range N, g n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))
      = ∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ))
          * ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % q) (t := Finset.range q)
      (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hq))]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨-, hr⟩ := hn
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hn_nat : q * (n / q) + r = n := by
    rw [← hr]
    exact Nat.div_add_mod n q
  have hn_eq : (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) + (r : ℝ) := by
    exact_mod_cast hn_nat.symm
  have key : (n : ℝ) * ((a : ℝ) / (q : ℝ))
      = ((a * (n / q : ℕ) : ℤ) : ℝ) + (r : ℝ) * (a : ℝ) / (q : ℝ) := by
    rw [hn_eq, Int.cast_mul, Int.cast_natCast]
    field_simp
  have hdecomp : (n : ℝ) * ((a : ℝ) / (q : ℝ) + β)
      = ((a * (n / q : ℕ) : ℤ) : ℝ) + ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β) := by
    calc (n : ℝ) * ((a : ℝ) / (q : ℝ) + β)
        = (n : ℝ) * ((a : ℝ) / (q : ℝ)) + (n : ℝ) * β := by ring
      _ = (((a * (n / q : ℕ) : ℤ) : ℝ) + (r : ℝ) * (a : ℝ) / (q : ℝ)) + (n : ℝ) * β := by
          rw [key]
      _ = ((a * (n / q : ℕ) : ℤ) : ℝ) + ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β) := by
          ring
  calc g n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))
      = g n * e (((a * (n / q : ℕ) : ℤ) : ℝ)
          + ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β)) := by rw [hdecomp]
    _ = g n * (e (((a * (n / q : ℕ) : ℤ) : ℝ))
          * e ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β)) := by rw [e_add]
    _ = g n * e ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β) := by
        rw [e_int]
        ring
    _ = g n * (e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * e ((n : ℝ) * β)) := by rw [e_add]
    _ = e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * (g n * e ((n : ℝ) * β)) := by ring

/-- **Abel bound for a twisted sum**: if all partial sums of `a` are `≤ B` in norm, the
    `e(nβ)`-twisted sum is `≤ B(1 + 2πN|β|)` — the summation-by-parts step that converts
    `WeakPNT_AP`-style partial-sum control into major-arc window evaluations, with the
    window factor `N|β| = O(P)` bounded on a Farey arc. -/
lemma abel_twisted_error (a : ℕ → ℂ) (β : ℝ) (N : ℕ) (B : ℝ)
    (hB : ∀ t ≤ N, ‖∑ n ∈ Finset.range t, a n‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, a n * e ((n : ℝ) * β)‖
      ≤ B * (1 + 2 * Real.pi * N * |β|) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Nat.zero_le N))
  have hfac : (0:ℝ) ≤ 2 * Real.pi * N * |β| := by positivity
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg hB0 (by linarith)
  have hstep : ∀ i : ℕ, ‖e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)‖
      ≤ 2 * Real.pi * |β| := by
    intro i
    have hfact : e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)
        = e ((i : ℝ) * β) * (e β - 1) := by
      rw [mul_sub, mul_one, e_add]
      congr 1
      push_cast
      ring
    rw [hfact, norm_mul, e_norm, one_mul, e_sub_one_norm]
    have hsin := Real.abs_sin_le_abs (x := Real.pi * β)
    have hpi : |Real.pi * β| = Real.pi * |β| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
    linarith [hsin, hpi.le, hpi.ge]
  have habel : ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * β)
      = e (((N - 1 : ℕ) : ℝ) * β) * (∑ n ∈ Finset.range N, a n)
        - ∑ i ∈ Finset.range (N - 1),
            (e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j := by
    have h := Finset.sum_range_by_parts (f := fun m : ℕ => e ((m : ℝ) * β)) (g := a) (n := N)
    simp only [smul_eq_mul] at h
    calc ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * β)
        = ∑ n ∈ Finset.range N, e ((n : ℝ) * β) * a n := by
          apply Finset.sum_congr rfl
          intro n _
          ring
      _ = _ := h
  rw [habel]
  calc ‖e (((N - 1 : ℕ) : ℝ) * β) * (∑ n ∈ Finset.range N, a n)
        - ∑ i ∈ Finset.range (N - 1),
            (e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j‖
      ≤ ‖e (((N - 1 : ℕ) : ℝ) * β) * (∑ n ∈ Finset.range N, a n)‖
        + ‖∑ i ∈ Finset.range (N - 1),
            (e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j‖ :=
        norm_sub_le _ _
    _ ≤ B + ((N - 1 : ℕ) : ℝ) * (2 * Real.pi * |β| * B) := by
        apply add_le_add
        · rw [norm_mul, e_norm, one_mul]
          exact hB N le_rfl
        · calc ‖∑ i ∈ Finset.range (N - 1),
              (e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j‖
              ≤ ∑ i ∈ Finset.range (N - 1),
                ‖(e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _i ∈ Finset.range (N - 1), 2 * Real.pi * |β| * B := by
                apply Finset.sum_le_sum
                intro i hi
                rw [norm_mul]
                apply mul_le_mul (hstep i) (hB (i + 1) ?_) (norm_nonneg _) (by positivity)
                rw [Finset.mem_range] at hi
                omega
            _ = ((N - 1 : ℕ) : ℝ) * (2 * Real.pi * |β| * B) := by
                rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ ≤ B * (1 + 2 * Real.pi * N * |β|) := by
        have hle : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast Nat.sub_le N 1
        have hnn : (0:ℝ) ≤ 2 * Real.pi * |β| := by positivity
        nlinarith [hB0, hnn, hle, mul_le_mul_of_nonneg_right hle hnn]

/-- **AP window sum vs smooth model**: if the residue-class partial sums of `g` track the
    linear model `t·κ` within `B` (the `WeakPNT_AP` error shape with `κ = 1/φ(q)`), then
    the twisted window sum tracks `κ·∑e(nβ)` within `B(1 + 2πN|β|)`. With
    `major_arc_residue_decomp` this evaluates `S` on a whole Farey window. -/
lemma ap_twisted_model (g : ℕ → ℂ) (κ : ℂ) (q r N : ℕ) (β : ℝ) (B : ℝ)
    (hB : ∀ t ≤ N, ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n)
        - (t : ℂ) * κ‖ ≤ B) :
    ‖(∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β))
      - κ * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ B * (1 + 2 * Real.pi * N * |β|) := by
  set a : ℕ → ℂ := fun n => (if n % q = r then g n else 0) - κ with ha
  have hpartial : ∀ t : ℕ, ∑ n ∈ Finset.range t, a n
      = (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) - (t : ℂ) * κ := by
    intro t
    rw [ha]
    rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.card_range]
    simp [nsmul_eq_mul]
  have htwist : ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * β)
      = (∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β))
        - κ * ∑ n ∈ Finset.range N, e ((n : ℝ) * β) := by
    rw [ha]
    have hterm : ∀ n : ℕ, ((if n % q = r then g n else 0) - κ) * e ((n : ℝ) * β)
        = (if n % q = r then g n * e ((n : ℝ) * β) else 0) - κ * e ((n : ℝ) * β) := by
      intro n
      by_cases h : n % q = r
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
        ring
    calc ∑ n ∈ Finset.range N, ((if n % q = r then g n else 0) - κ) * e ((n : ℝ) * β)
        = ∑ n ∈ Finset.range N,
            ((if n % q = r then g n * e ((n : ℝ) * β) else 0) - κ * e ((n : ℝ) * β)) := by
          apply Finset.sum_congr rfl
          intro n _
          exact hterm n
      _ = (∑ n ∈ Finset.range N, if n % q = r then g n * e ((n : ℝ) * β) else 0)
          - ∑ n ∈ Finset.range N, κ * e ((n : ℝ) * β) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β))
          - κ * ∑ n ∈ Finset.range N, e ((n : ℝ) * β) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  rw [← htwist]
  apply abel_twisted_error
  intro t ht
  rw [hpartial t]
  exact hB t ht

/-- **Cesàro limit to window bound**: if `(∑_{n<t} c(n))/t → κ`, then for every `ε > 0`
    there is a constant `C` with `‖∑_{n<t} c(n) − tκ‖ ≤ εN + C` for ALL `t ≤ N` — the
    exact `B` that `ap_twisted_model` consumes. Converts `WeakPNT_AP`'s Tendsto into
    per-window control, with the small-`t` range absorbed into `C`. -/
lemma partial_sum_window_bound (c : ℕ → ℂ) (κ : ℂ)
    (h : Filter.Tendsto (fun t : ℕ => (∑ n ∈ Finset.range t, c n) / (t : ℂ))
      Filter.atTop (nhds κ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ t ≤ N,
      ‖(∑ n ∈ Finset.range t, c n) - (t : ℂ) * κ‖ ≤ ε * N + C := by
  have hev : ∀ᶠ t : ℕ in Filter.atTop,
      ‖(∑ n ∈ Finset.range t, c n) / (t : ℂ) - κ‖ < ε := by
    have := Metric.tendsto_nhds.mp h ε hε
    simpa [dist_eq_norm] using this
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨(∑ n ∈ Finset.range T₀, ‖c n‖) + T₀ * ‖κ‖, by positivity, ?_⟩
  intro N t htN
  have hNnn : (0:ℝ) ≤ ε * N := by positivity
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, sub_zero,
      norm_zero]
    positivity
  by_cases hT : T₀ ≤ t
  · have h1 := hT₀ t hT
    have hne : ((t : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfact : (∑ n ∈ Finset.range t, c n) - (t : ℂ) * κ
        = (t : ℂ) * ((∑ n ∈ Finset.range t, c n) / (t : ℂ) - κ) := by
      field_simp
    rw [hfact, norm_mul, Complex.norm_natCast]
    have htN' : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast htN
    calc (t : ℝ) * ‖(∑ n ∈ Finset.range t, c n) / (t : ℂ) - κ‖
        ≤ (t : ℝ) * ε := mul_le_mul_of_nonneg_left h1.le (Nat.cast_nonneg t)
      _ ≤ (N : ℝ) * ε := mul_le_mul_of_nonneg_right htN' hε.le
      _ = ε * N := by ring
      _ ≤ ε * N + ((∑ n ∈ Finset.range T₀, ‖c n‖) + T₀ * ‖κ‖) := by
          have hCnn : (0:ℝ) ≤ (∑ n ∈ Finset.range T₀, ‖c n‖) + T₀ * ‖κ‖ := by positivity
          linarith
  · push_neg at hT
    calc ‖(∑ n ∈ Finset.range t, c n) - (t : ℂ) * κ‖
        ≤ ‖∑ n ∈ Finset.range t, c n‖ + ‖(t : ℂ) * κ‖ := norm_sub_le _ _
      _ ≤ (∑ n ∈ Finset.range t, ‖c n‖) + (t : ℝ) * ‖κ‖ := by
          apply add_le_add (norm_sum_le _ _)
          rw [norm_mul, Complex.norm_natCast]
      _ ≤ (∑ n ∈ Finset.range T₀, ‖c n‖) + (T₀ : ℝ) * ‖κ‖ := by
          apply add_le_add
          · apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [Finset.mem_range] at hx ⊢
              omega
            · intro n _ _
              exact norm_nonneg _
          · apply mul_le_mul_of_nonneg_right _ (norm_nonneg κ)
            exact_mod_cast hT.le
      _ ≤ ε * N + ((∑ n ∈ Finset.range T₀, ‖c n‖) + T₀ * ‖κ‖) := by linarith

/-- **The window evaluation** (route-1 capstone): if each residue class of `g` has Cesàro
    density `κ(r)` (the `WeakPNT_AP` shape for each FIXED `q`), then for every `ε > 0`
    there is `C` such that on EVERY window `a/q + β`,
    `‖S − (∑_r e(ra/q)κ(r))·∑e(nβ)‖ ≤ q(εN+C)(1+2πN|β|)` — with `N|β| = O(P)` bounded on
    a Farey arc, this is `o(N)` per window with NO uniformity in `q`. -/
theorem major_window_eval (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q) (κ : ℕ → ℂ)
    (hκ : ∀ r, r < q → Filter.Tendsto
      (fun t : ℕ => (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) / (t : ℂ))
      Filter.atTop (nhds (κ r)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ a : ℤ, ∀ β : ℝ,
      ‖(∑ n ∈ Finset.range N, g n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
        - (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * κ r)
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ (q : ℝ) * ((ε * N + C) * (1 + 2 * Real.pi * N * |β|)) := by
  classical
  -- per-residue constants from the extractor
  have hres : ∀ r, r < q → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ t ≤ N,
      ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) - (t : ℂ) * κ r‖
        ≤ ε * N + C := by
    intro r hr
    have hconv : (fun t : ℕ => (∑ n ∈ Finset.range t,
          if n % q = r then g n else 0) / (t : ℂ))
        = (fun t : ℕ => (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) / (t : ℂ)) := by
      funext t
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    obtain ⟨C, hC0, hC⟩ := partial_sum_window_bound
      (fun n => if n % q = r then g n else 0) (κ r) (by rw [hconv]; exact hκ r hr) ε hε
    refine ⟨C, hC0, fun N t ht => ?_⟩
    have := hC N t ht
    rwa [Finset.sum_ite, Finset.sum_const_zero, add_zero] at this
  -- a single constant dominating all residues
  set Cf : ℕ → ℝ := fun r => if h : r < q then (hres r h).choose else 0 with hCf
  set Ctot : ℝ := ∑ r ∈ Finset.range q, Cf r with hCtot
  have hCf0 : ∀ r, 0 ≤ Cf r := by
    intro r
    by_cases h : r < q
    · simp only [hCf, dif_pos h]
      exact (hres r h).choose_spec.1
    · simp only [hCf, dif_neg h]
      exact le_refl 0
  have hCtot0 : 0 ≤ Ctot := Finset.sum_nonneg fun r _ => hCf0 r
  have hCfle : ∀ r ∈ Finset.range q, Cf r ≤ Ctot := by
    intro r hr
    exact Finset.single_le_sum (fun i _ => hCf0 i) hr
  refine ⟨Ctot, hCtot0, fun N a β => ?_⟩
  rw [major_arc_residue_decomp g N a q hq β, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hfac : (0:ℝ) ≤ 1 + 2 * Real.pi * N * |β| := by positivity
  calc ‖∑ r ∈ Finset.range q,
        (e ((r : ℝ) * (a : ℝ) / (q : ℝ))
            * ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β)
          - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * κ r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β))‖
      ≤ ∑ r ∈ Finset.range q,
        ‖e ((r : ℝ) * (a : ℝ) / (q : ℝ))
            * ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β)
          - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * κ r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range q, (ε * N + Ctot) * (1 + 2 * Real.pi * N * |β|) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrq : r < q := Finset.mem_range.mp hr
        have hfactor : e ((r : ℝ) * (a : ℝ) / (q : ℝ))
              * ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β)
            - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * κ r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)
            = e ((r : ℝ) * (a : ℝ) / (q : ℝ))
              * ((∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β))
                - κ r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)) := by
          ring
        rw [hfactor, norm_mul, e_norm, one_mul]
        have hB : ∀ t ≤ N,
            ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) - (t : ℂ) * κ r‖
              ≤ ε * N + Ctot := by
          intro t ht
          have h1 := (hres r hrq).choose_spec.2 N t ht
          have h2 : Cf r = (hres r hrq).choose := by
            simp only [hCf, dif_pos hrq]
          have h3 := hCfle r hr
          rw [h2] at h3
          linarith
        exact ap_twisted_model g (κ r) q r N β (ε * N + Ctot) hB
    _ = (q : ℝ) * ((ε * N + Ctot) * (1 + 2 * Real.pi * N * |β|)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]

/-- **Squaring a window estimate**: `‖S−M‖ ≤ E ⟹ ‖S²−M²‖ ≤ E(E+2‖M‖)` — converts the
    window evaluation of `S` into the window evaluation of `S²` that the major
    coefficient `∫_𝔐 S²e(−nα)` consumes. -/
lemma sq_diff_norm_le (S M : ℂ) (E : ℝ) (h : ‖S - M‖ ≤ E) :
    ‖S ^ 2 - M ^ 2‖ ≤ E * (E + 2 * ‖M‖) := by
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) h
  have hfact : S ^ 2 - M ^ 2 = (S - M) * ((S - M) + 2 * M) := by ring
  rw [hfact, norm_mul]
  apply mul_le_mul h _ (norm_nonneg _) hE0
  calc ‖(S - M) + 2 * M‖ ≤ ‖S - M‖ + ‖(2 : ℂ) * M‖ := norm_add_le _ _
    _ ≤ E + 2 * ‖M‖ := by
        rw [norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2]
        linarith

open ArithmeticFunction in
/-- **Ramanujan sum at coprime argument**: `∑_{r<q, gcd(r,q)=1} e(ar/q) = μ(q)` —
    the arithmetic heart of the singular series. Möbius inclusion-exclusion over the
    banked additive-character orthogonality. -/
lemma ramanujan_sum_coprime (a : ℤ) (q : ℕ) (hq : 0 < q) (ha : Int.gcd a q = 1) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)
      = (ArithmeticFunction.moebius q : ℂ) := by
  classical
  have hq' : q ≠ 0 := hq.ne'
  have hind : ∀ n : ℕ, n ≠ 0 →
      (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
    intro n hn
    have h : ((ArithmeticFunction.moebius * ArithmeticFunction.zeta :
        ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    by_cases h1 : n = 1
    · rw [if_pos h1, h1]
      simp
    · rw [if_neg h1]
      rw [if_neg h1] at h
      have : ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℂ) = 0 := by
        rw [h]
        norm_num
      push_cast at this
      exact this
  have hdivset : ∀ r : ℕ, (Nat.gcd r q).divisors = q.divisors.filter (fun d => d ∣ r) := by
    intro r
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hdvd, -⟩
      rw [Nat.dvd_gcd_iff] at hdvd
      exact ⟨⟨hdvd.2, hq'⟩, hdvd.1⟩
    · rintro ⟨⟨hdq, -⟩, hdr⟩
      exact ⟨Nat.dvd_gcd hdr hdq, fun hc => hq' (Nat.gcd_eq_zero_iff.mp hc).2⟩
  have hstep : ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
          * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q) := by
    rw [Finset.sum_filter]
    have hpt : ∀ r ∈ Finset.range q,
        (if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) else 0)
        = ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ)
            * e ((a : ℝ) * r / q) else 0 := by
      intro r _
      have hgpos : Nat.gcd r q ≠ 0 := fun hc => hq' (Nat.gcd_eq_zero_iff.mp hc).2
      calc (if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) else 0)
          = (if Nat.gcd r q = 1 then (1:ℂ) else 0) * e ((a : ℝ) * r / q) := by
            by_cases h : Nat.gcd r q = 1
            · rw [if_pos h, if_pos h, one_mul]
            · rw [if_neg h, if_neg h, zero_mul]
        _ = (∑ d ∈ (Nat.gcd r q).divisors, (ArithmeticFunction.moebius d : ℂ))
              * e ((a : ℝ) * r / q) := by rw [hind _ hgpos]
        _ = ∑ d ∈ q.divisors.filter (fun d => d ∣ r),
              (ArithmeticFunction.moebius d : ℂ) * e ((a : ℝ) * r / q) := by
            rw [hdivset r, Finset.sum_mul]
        _ = ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ)
              * e ((a : ℝ) * r / q) else 0 := by
            rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum, Finset.sum_filter]
  have hinner : ∀ d ∈ q.divisors,
      (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q))
      = if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdq, -⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
    have hm0 : q / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hq hdq) hd0).ne'
    have hqe : d * (q / d) = q := Nat.mul_div_cancel' hdq
    have hreindex : (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q))
        = ∑ s ∈ Finset.range (q / d), e ((a : ℝ) * s / (q / d : ℕ)) := by
      apply Finset.sum_nbij' (fun r => r / d) (fun s => d * s)
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [Finset.mem_range] at hs
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, Dvd.intro s rfl⟩
        have h1 : d * s < d * (q / d) := mul_lt_mul_of_pos_left hs hd0
        rwa [hqe] at h1
      · intro r hr
        simp only [Finset.mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _
        exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        congr 1
        have hcast : ((q : ℝ)) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
          exact_mod_cast hqe.symm
        have hrr : (r : ℝ) = (d : ℝ) * ((r / d : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' hr.2).symm
        have hd0R : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
        have hm0R : ((q / d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
        rw [hcast, hrr]
        field_simp
    rw [hreindex, char_orthogonality a (q / d) hm0]
  rw [hstep]
  have hcongr : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
      * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
        * (if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0) :=
    Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])
  rw [hcongr, Finset.sum_eq_single q]
  · rw [Nat.div_self hq]
    simp
  · intro d hd hne
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdq, -⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
    rw [if_neg, mul_zero]
    intro hdvd
    have hmq : (q / d : ℕ) ∣ q := Nat.div_dvd_of_dvd hdq
    have hgcd : (q / d) ∣ Int.gcd a q := Int.dvd_gcd hdvd (by exact_mod_cast hmq)
    rw [ha] at hgcd
    have hm1 : (q / d : ℕ) = 1 := Nat.dvd_one.mp hgcd
    apply hne
    have hqe : d * (q / d) = q := Nat.mul_div_cancel' hdq
    rw [hm1, mul_one] at hqe
    omega
  · intro hqmem
    exact absurd (Nat.mem_divisors_self q hq') hqmem

/-- **General Ramanujan sum evaluation** (no coprimality hypothesis): the same Möbius
    inclusion–exclusion over character orthogonality that gives `ramanujan_sum_coprime`, but
    stopped *before* the coprime collapse — valid for every `a`. Yields
    `c_q(a) = ∑_{d ∣ q} μ(d)·[ (q/d) ∣ a ]·(q/d)`, the arithmetic engine of the truncated
    singular series `𝔖_P(n) = ∑_{q≤P} μ(q)²c_q(n)/φ(q)²`. -/
lemma ramanujan_sum_divisor (a : ℤ) (q : ℕ) (hq : 0 < q) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
          * (if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  classical
  have hq' : q ≠ 0 := hq.ne'
  have hind : ∀ n : ℕ, n ≠ 0 →
      (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
    intro n hn
    have h : ((ArithmeticFunction.moebius * ArithmeticFunction.zeta :
        ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    by_cases h1 : n = 1
    · rw [if_pos h1, h1]
      simp
    · rw [if_neg h1]
      rw [if_neg h1] at h
      have : ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℂ) = 0 := by
        rw [h]
        norm_num
      push_cast at this
      exact this
  have hdivset : ∀ r : ℕ, (Nat.gcd r q).divisors = q.divisors.filter (fun d => d ∣ r) := by
    intro r
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hdvd, -⟩
      rw [Nat.dvd_gcd_iff] at hdvd
      exact ⟨⟨hdvd.2, hq'⟩, hdvd.1⟩
    · rintro ⟨⟨hdq, -⟩, hdr⟩
      exact ⟨Nat.dvd_gcd hdr hdq, fun hc => hq' (Nat.gcd_eq_zero_iff.mp hc).2⟩
  have hstep : ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
          * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q) := by
    rw [Finset.sum_filter]
    have hpt : ∀ r ∈ Finset.range q,
        (if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) else 0)
        = ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ)
            * e ((a : ℝ) * r / q) else 0 := by
      intro r _
      have hgpos : Nat.gcd r q ≠ 0 := fun hc => hq' (Nat.gcd_eq_zero_iff.mp hc).2
      calc (if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) else 0)
          = (if Nat.gcd r q = 1 then (1:ℂ) else 0) * e ((a : ℝ) * r / q) := by
            by_cases h : Nat.gcd r q = 1
            · rw [if_pos h, if_pos h, one_mul]
            · rw [if_neg h, if_neg h, zero_mul]
        _ = (∑ d ∈ (Nat.gcd r q).divisors, (ArithmeticFunction.moebius d : ℂ))
              * e ((a : ℝ) * r / q) := by rw [hind _ hgpos]
        _ = ∑ d ∈ q.divisors.filter (fun d => d ∣ r),
              (ArithmeticFunction.moebius d : ℂ) * e ((a : ℝ) * r / q) := by
            rw [hdivset r, Finset.sum_mul]
        _ = ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ)
              * e ((a : ℝ) * r / q) else 0 := by
            rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum, Finset.sum_filter]
  have hinner : ∀ d ∈ q.divisors,
      (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q))
      = if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdq, -⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
    have hm0 : q / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hq hdq) hd0).ne'
    have hqe : d * (q / d) = q := Nat.mul_div_cancel' hdq
    have hreindex : (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q))
        = ∑ s ∈ Finset.range (q / d), e ((a : ℝ) * s / (q / d : ℕ)) := by
      apply Finset.sum_nbij' (fun r => r / d) (fun s => d * s)
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [Finset.mem_range] at hs
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, Dvd.intro s rfl⟩
        have h1 : d * s < d * (q / d) := mul_lt_mul_of_pos_left hs hd0
        rwa [hqe] at h1
      · intro r hr
        simp only [Finset.mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _
        exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        congr 1
        have hcast : ((q : ℝ)) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
          exact_mod_cast hqe.symm
        have hrr : (r : ℝ) = (d : ℝ) * ((r / d : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' hr.2).symm
        have hd0R : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
        have hm0R : ((q / d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
        rw [hcast, hrr]
        field_simp
    rw [hreindex, char_orthogonality a (q / d) hm0]
  rw [hstep]
  exact Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])


/-- **The Dirichlet-kernel square's Fourier coefficient is the pair count**:
    `∫₀¹ D_N(α)² e(−nα) dα = #{(i,j) : i,j < N, i+j = n}` — the model's contribution to
    each representation count, in exact form. -/
lemma model_sq_coeff (N n : ℕ) :
    ∫ α in (0:ℝ)..1,
        (∑ m ∈ Finset.range N, e ((m : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α))
      = (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ) := by
  have h := fourier_coeff_sq (fun _ => (1 : ℂ)) N n
  simp only [one_mul] at h
  rw [h]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The tent count**: for `n < N` the number of ordered pairs `i+j = n` inside the
    `N×N` box is exactly `n+1` — the model main term grows linearly on the upper block,
    which is what the reduction's `δ`-lower-bound consumes. -/
lemma pair_count_eq (N n : ℕ) (hn : n < N) :
    ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card = n + 1 := by
  have himg : (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)
      = (Finset.range (n + 1)).image (fun i => (i, n - i)) := by
    ext p
    obtain ⟨p1, p2⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨p1, by omega, rfl, by omega⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro i _ j _ h
  exact (Prod.mk.injEq _ _ _ _).mp h |>.1

/-- Upper slope of the tent: for `N ≤ n ≤ 2N−2` the pair count is `2N−1−n`. -/
lemma pair_count_eq_upper (N n : ℕ) (hn1 : N ≤ n) (hn2 : n ≤ 2 * N - 2) :
    ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card
      = 2 * N - 1 - n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp
  have hN : 2 ≤ N := by omega
  have himg : (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)
      = (Finset.Icc (n - N + 1) (N - 1)).image (fun i => (i, n - i)) := by
    ext p
    obtain ⟨p1, p2⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Finset.mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨p1, ⟨by omega, by omega⟩, rfl, by omega⟩
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i _ j _ h
    exact (Prod.mk.injEq _ _ _ _).mp h |>.1

/-- Beyond the tent: for `n ≥ 2N−1` the pair count vanishes. -/
lemma pair_count_eq_zero (N n : ℕ) (hn : 2 * N - 1 ≤ n) (hN : 0 < N) :
    ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨p1, p2⟩ hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  simp only
  omega

open MeasureTheory in
/-- **Small-set L² bound**: on a measurable `s ⊆ (0,1]` where `‖f‖ ≤ B`, the L² mass is
    at most `vol(s)·B²` — the per-window error estimate: window measure `2/(q(Q+1))`
    times the squared window evaluation. -/
lemma setIntegral_sq_le_measure_mul_sup (f : ℝ → ℂ) (hf : Continuous f) (s : Set ℝ)
    (hs : MeasurableSet s) (hsub : s ⊆ Set.Ioc (0:ℝ) 1) (B : ℝ)
    (hB : ∀ x ∈ s, ‖f x‖ ≤ B) :
    ∫ x in s, ‖f x‖ ^ 2 ≤ (volume s).toReal * B ^ 2 := by
  have hint : IntegrableOn (fun x => ‖f x‖ ^ 2) s volume :=
    ((hf.norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hfin : volume s ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono hsub)
    simp [Real.volume_Ioc]
  calc ∫ x in s, ‖f x‖ ^ 2
      ≤ ∫ _x in s, B ^ 2 := by
        apply setIntegral_mono_on hint (integrableOn_const hfin) hs
        intro x hx
        have h := hB x hx
        have h0 : 0 ≤ ‖f x‖ := norm_nonneg _
        nlinarith
    _ = (volume s).toReal * B ^ 2 := by
        rw [setIntegral_const, smul_eq_mul]
        rfl

/-- A Farey window's measure in usable form: `vol(B̄(c,r)) = 2r`. -/
lemma window_volume (c r : ℝ) (hr : 0 ≤ r) :
    (MeasureTheory.volume (Metric.closedBall c r)).toReal = 2 * r := by
  rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)]

/-- Trivial bound for Ramanujan-type sums: `‖∑_{units} e(ar/q)‖ ≤ φ(q)`. -/
lemma ramanujan_sum_norm_le (a : ℤ) (q : ℕ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)‖
      ≤ (Nat.totient q : ℝ) := by
  calc ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)‖
      ≤ ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), ‖e ((a : ℝ) * r / q)‖ :=
        norm_sum_le _ _
    _ = ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).card := by
        simp [e_norm]
    _ = (Nat.totient q : ℝ) := by
        rw [Nat.totient]
        congr 2
        ext r
        simp [Nat.Coprime, Nat.gcd_comm]

open MeasureTheory in
/-- Two-set L¹ subadditivity for nonneg integrands on subsets of `(0,1]`. -/
lemma setIntegral_union_le (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAsub : A ⊆ Set.Ioc (0:ℝ) 1) (hBsub : B ⊆ Set.Ioc (0:ℝ) 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgnn : ∀ x, 0 ≤ g x) :
    ∫ x in A ∪ B, g x ≤ (∫ x in A, g x) + ∫ x in B, g x := by
  have hint : IntegrableOn g (Set.Ioc (0:ℝ) 1) volume := hg.integrableOn_Ioc
  have hunion : A ∪ (B \ A) = A ∪ B := Set.union_diff_self
  calc ∫ x in A ∪ B, g x
      = ∫ x in A ∪ (B \ A), g x := by rw [hunion]
    _ = (∫ x in A, g x) + ∫ x in B \ A, g x := by
        apply setIntegral_union Set.disjoint_sdiff_right (hB.diff hA)
        · exact hint.mono_set hAsub
        · exact hint.mono_set (le_trans Set.diff_subset hBsub)
    _ ≤ (∫ x in A, g x) + ∫ x in B, g x := by
        have hmono : ∫ x in B \ A, g x ≤ ∫ x in B, g x := by
          apply setIntegral_mono_set (hint.mono_set hBsub)
          · filter_upwards with x using hgnn x
          · exact HasSubset.Subset.eventuallyLE Set.diff_subset
        linarith

open MeasureTheory in
/-- **Finite-union L¹ subadditivity**: the integral of a nonneg integrand over a finite
    union is at most the sum of the per-set integrals — the major-arc integral's split
    over the anchor windows (disjointness not even needed for the ≤ direction). -/
lemma setIntegral_biUnion_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Set ℝ)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) (hsub : ∀ i ∈ s, t i ⊆ Set.Ioc (0:ℝ) 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgnn : ∀ x, 0 ≤ g x) :
    ∫ x in ⋃ i ∈ s, t i, g x ≤ ∑ i ∈ s, ∫ x in t i, g x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hun : (⋃ i ∈ insert a s, t i) = t a ∪ ⋃ i ∈ s, t i := by
      simp [Set.biUnion_insert]
    rw [hun]
    have htm : ∀ i ∈ s, MeasurableSet (t i) := fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hsm : ∀ i ∈ s, t i ⊆ Set.Ioc (0:ℝ) 1 := fun i hi => hsub i (Finset.mem_insert_of_mem hi)
    have hUm : MeasurableSet (⋃ i ∈ s, t i) := by
      apply MeasurableSet.biUnion (Finset.countable_toSet s)
      intro i hi
      exact htm i hi
    have hUsub : (⋃ i ∈ s, t i) ⊆ Set.Ioc (0:ℝ) 1 := by
      apply Set.iUnion₂_subset
      intro i hi
      exact hsm i hi
    calc ∫ x in t a ∪ ⋃ i ∈ s, t i, g x
        ≤ (∫ x in t a, g x) + ∫ x in ⋃ i ∈ s, t i, g x :=
          setIntegral_union_le _ _ (ht a (Finset.mem_insert_self a s)) hUm
            (hsub a (Finset.mem_insert_self a s)) hUsub g hg hgnn
      _ ≤ (∫ x in t a, g x) + ∑ i ∈ s, ∫ x in t i, g x := by
          gcongr
          exact ih htm hsm

section VonMangoldtParseval

open ArithmeticFunction
open scoped ArithmeticFunction

/-- **The Λ-weighted Parseval**: `∫₀¹ ‖∑_{n≤N} Λ(n)e(nα)‖² dα = ∑_{n≤N} Λ(n)²` —
    the variance integral's denominator. -/
lemma parseval_vonMangoldt (N : ℕ) :
    ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 2
      = ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
  have hsub : Finset.Ioc 0 N ⊆ Finset.range (N + 1) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_range]
    omega
  have hzero : ∀ n ∈ Finset.range (N + 1), n ∉ Finset.Ioc 0 N →
      ((Λ n : ℝ) : ℂ) = 0 := by
    intro n hn hnot
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ioc] at hnot
    have hn0 : n = 0 := by omega
    subst hn0
    rw [ArithmeticFunction.map_zero]
    norm_num
  have hsum_eq : ∀ α : ℝ,
      ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)
      = ∑ n ∈ Finset.range (N + 1), ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α) := by
    intro α
    apply Finset.sum_subset hsub
    intro n hn hnot
    rw [hzero n hn hnot, zero_mul]
  calc ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 2
      = ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range (N + 1),
          ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [hsum_eq α]
    _ = ∑ n ∈ Finset.range (N + 1), ‖((Λ n : ℝ) : ℂ)‖ ^ 2 :=
        parseval (fun n => ((Λ n : ℝ) : ℂ)) (N + 1)
    _ = ∑ n ∈ Finset.range (N + 1), Λ n ^ 2 := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    _ = ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
        symm
        apply Finset.sum_subset hsub
        intro n hn hnot
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Ioc] at hnot
        have hn0 : n = 0 := by omega
        subst hn0
        rw [ArithmeticFunction.map_zero]
        norm_num

/-- The second-moment size: `∑_{n≤N} Λ(n)² ≤ N·(log N)²`. -/
lemma sum_vonMangoldt_sq_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 ≤ (N : ℝ) * Real.log N ^ 2 := by
  calc ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2
      ≤ ∑ _n ∈ Finset.Ioc 0 N, Real.log N ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        have h1 : Λ n ≤ Real.log n := vonMangoldt_le_log
        have h2 : Real.log n ≤ Real.log N := by
          apply Real.log_le_log (by exact_mod_cast hn.1)
          exact_mod_cast hn.2
        have h3 : Λ n ≤ Real.log N := le_trans h1 h2
        exact pow_le_pow_left₀ vonMangoldt_nonneg h3 2
    _ = (N : ℝ) * Real.log N ^ 2 := by
        rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

/-- The Λ-exponential sum is continuous in `α`. -/
lemma vonMangoldt_expsum_continuous (N : ℕ) :
    Continuous (fun α : ℝ => ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) := by
  apply continuous_finsetSum
  intro n _
  unfold e
  fun_prop

/-- Any power of the Λ-exponential sum's norm is interval-integrable. -/
lemma vonMangoldt_expsum_pow_integrable (N k : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun α : ℝ => ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ k)
      MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  exact ((vonMangoldt_expsum_continuous N).norm).pow k


open MeasureTheory in
/-- **Minor-arc L⁴ bound**: if the exp sum is ≤ C in sup on a measurable minor-arc set
    `m ⊆ (0,1]`, then `∫_m ‖S‖⁴ ≤ C² · ∑_{n≤N} Λ(n)²` — one factor `‖S‖²` capped by the
    sup, the other integrated out by Parseval. This is Vinogradov's fundamental trick. -/
lemma minor_arc_L4_bound (N : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (C : ℝ)
    (hsup : ∀ α ∈ m, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ C) :
    ∫ α in m, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 4
      ≤ C ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
  set S : ℝ → ℂ := fun α => ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)
    with hS
  have hcont : Continuous S := vonMangoldt_expsum_continuous N
  have hint2 : IntegrableOn (fun α => ‖S α‖ ^ 2) (Set.Ioc (0:ℝ) 1) volume :=
    (hcont.norm.pow 2).integrableOn_Ioc
  have hint2m : IntegrableOn (fun α => ‖S α‖ ^ 2) m volume := hint2.mono_set hsub
  have hint4m : IntegrableOn (fun α => ‖S α‖ ^ 4) m volume :=
    ((hcont.norm.pow 4).integrableOn_Ioc).mono_set hsub
  rcases Set.eq_empty_or_nonempty m with hempty | ⟨α₀, hα₀⟩
  · rw [hempty]
    simp only [Measure.restrict_empty, integral_zero_measure]
    exact mul_nonneg (sq_nonneg C) (Finset.sum_nonneg fun n _ => sq_nonneg _)
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hsup α₀ hα₀)
  -- pointwise: ‖S‖⁴ ≤ C² ‖S‖² on m
  have hpt : ∀ α ∈ m, ‖S α‖ ^ 4 ≤ C ^ 2 * ‖S α‖ ^ 2 := by
    intro α hα
    have hsq : ‖S α‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hsup α hα) 2
    calc ‖S α‖ ^ 4 = ‖S α‖ ^ 2 * ‖S α‖ ^ 2 := by ring
      _ ≤ C ^ 2 * ‖S α‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (by positivity)
  calc ∫ α in m, ‖S α‖ ^ 4
      ≤ ∫ α in m, C ^ 2 * ‖S α‖ ^ 2 :=
        setIntegral_mono_on hint4m (hint2m.const_mul _) hm hpt
    _ = C ^ 2 * ∫ α in m, ‖S α‖ ^ 2 := by rw [integral_const_mul]
    _ ≤ C ^ 2 * ∫ α in Set.Ioc (0:ℝ) 1, ‖S α‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply setIntegral_mono_set hint2
        · filter_upwards with α using by positivity
        · exact HasSubset.Subset.eventuallyLE hsub
    _ = C ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
        rw [← intervalIntegral.integral_of_le zero_le_one, parseval_vonMangoldt N]


open MeasureTheory in
/-- **The complete minor-arc variance piece**: on any minor-arc set where the Λ-exp-sum
    is ≤ Csup in sup, the L² error against ANY trig-polynomial main term is
    `≤ 2·Csup²·∑Λ(n)² + 2·∑‖c(n)‖²`. Composes L2_diff_le + minor_arc_L4_bound +
    setL2_le_circle + parseval; with `vinogradov_sup` as Csup this is the finished
    minor-arc half of the Goldbach variance bound. -/
theorem minor_arc_variance_piece (N M : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (c : ℕ → ℂ) (Csup : ℝ)
    (hsup : ∀ α ∈ m, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ Csup) :
    ∫ α in m, ‖(∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2
        - ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2
      ≤ 2 * (Csup ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2)
        + 2 * ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
  have hS : Continuous (fun α : ℝ => ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) :=
    vonMangoldt_expsum_continuous N
  have hCp : Continuous (fun α : ℝ => ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)) := by
    apply continuous_finsetSum
    intro n _
    unfold e
    fun_prop
  have h1 := L2_diff_le
    (fun α : ℝ =>
      (∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2)
    (fun α : ℝ =>
      ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α))
    (hS.pow 2) hCp m hm hsub
  have h2 : (∫ α in m,
      ‖(∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2)
      ≤ Csup ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
    have hcongr : (∫ α in m,
        ‖(∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2)
        = ∫ α in m, ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 4 := by
      apply setIntegral_congr_fun hm
      intro α _
      dsimp only
      rw [norm_pow, ← pow_mul]
    rw [hcongr]
    exact minor_arc_L4_bound N m hm hsub Csup hsup
  have h3 : (∫ α in m, ‖∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2)
      ≤ ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
    calc (∫ α in m, ‖∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2)
        ≤ ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2 :=
          setL2_le_circle _ hCp m hsub
      _ = ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := parseval c M
  linarith


/-- **Proper prime powers are rare**: the count of `m ≤ n` with `Λ(m) ≠ 0` but `m` not
    prime is at most `√n · (log₂n + 1)` — the elementary input for converting the
    Λ-weighted Goldbach count into the prime-pair count. -/
lemma card_properPrimePow_le (n : ℕ) :
    (((Finset.Ioc 0 n).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0)).card : ℝ)
      ≤ (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) := by
  set s := (Finset.Ioc 0 n).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0) with hs
  have hcard : s.card ≤ (Nat.log 2 n + 1) * (Finset.Ioc 0 (Nat.sqrt n)).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := Nat.minFac)
    · intro m hm
      rw [hs, Finset.mem_filter, Finset.mem_Ioc] at hm
      obtain ⟨⟨hm0, hmn⟩, hnp, hΛ⟩ := hm
      rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ
      obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
      have hp' := hp.nat_prime
      have hmf : (p ^ k).minFac = p := Nat.Prime.pow_minFac hp' hk.ne'
      rw [hmf, Finset.mem_Ioc]
      have hk2 : 2 ≤ k := by
        by_contra hcon
        interval_cases k
        exact hnp (by simpa using hp')
      refine ⟨hp'.pos, ?_⟩
      rw [Nat.le_sqrt]
      calc p * p = p ^ 2 := by ring
        _ ≤ p ^ k := Nat.pow_le_pow_right hp'.pos hk2
        _ ≤ n := hmn
    · intro p _
      have hsubfiber : (s.filter (fun m => m.minFac = p)).card
          ≤ (Finset.Icc 2 (Nat.log 2 n)).card := by
        apply Finset.card_le_card_of_injOn (fun m => Nat.log p m)
        · intro m hm
          simp only [Finset.mem_coe, Finset.mem_filter] at hm
          obtain ⟨hms, hmf⟩ := hm
          rw [hs, Finset.mem_filter, Finset.mem_Ioc] at hms
          obtain ⟨⟨hm0, hmn⟩, hnp, hΛ⟩ := hms
          rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ
          obtain ⟨q, k, hq, hk, rfl⟩ := hΛ
          have hq' := hq.nat_prime
          have hqf : (q ^ k).minFac = q := Nat.Prime.pow_minFac hq' hk.ne'
          have hqp : q = p := by rw [← hqf, hmf]
          subst hqp
          have hk2 : 2 ≤ k := by
            by_contra hcon
            interval_cases k
            exact hnp (by simpa using hq')
          simp only [Finset.mem_coe, Finset.mem_Icc, Nat.log_pow hq'.one_lt]
          refine ⟨hk2, ?_⟩
          have h2k : 2 ^ k ≤ n := le_trans (Nat.pow_le_pow_left hq'.two_le k) hmn
          exact Nat.le_log_of_pow_le (by norm_num) h2k
        · intro m1 hm1 m2 hm2 heq
          simp only [Finset.mem_coe, Finset.mem_filter] at hm1 hm2
          obtain ⟨hms1, hmf1⟩ := hm1
          obtain ⟨hms2, hmf2⟩ := hm2
          rw [hs, Finset.mem_filter] at hms1 hms2
          obtain ⟨-, -, hΛ1⟩ := hms1
          obtain ⟨-, -, hΛ2⟩ := hms2
          rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ1 hΛ2
          obtain ⟨q1, k1, hq1, hk1, rfl⟩ := hΛ1
          obtain ⟨q2, k2, hq2, hk2, rfl⟩ := hΛ2
          have hq1' := hq1.nat_prime
          have hq2' := hq2.nat_prime
          have hf1 : (q1 ^ k1).minFac = q1 := Nat.Prime.pow_minFac hq1' hk1.ne'
          have hf2 : (q2 ^ k2).minFac = q2 := Nat.Prime.pow_minFac hq2' hk2.ne'
          have hq1p : q1 = p := by rw [← hf1, hmf1]
          have hq2p : q2 = p := by rw [← hf2, hmf2]
          subst hq1p
          subst hq2p
          simp only [Nat.log_pow hq1'.one_lt] at heq
          rw [heq]
      calc (s.filter (fun m => m.minFac = p)).card
          ≤ (Finset.Icc 2 (Nat.log 2 n)).card := hsubfiber
        _ ≤ Nat.log 2 n + 1 := by rw [Nat.card_Icc]; omega
  have hIoc : (Finset.Ioc 0 (Nat.sqrt n)).card = Nat.sqrt n := by
    rw [Nat.card_Ioc, Nat.sub_zero]
  rw [hIoc] at hcard
  calc (s.card : ℝ) ≤ ((Nat.log 2 n + 1) * Nat.sqrt n : ℕ) := by exact_mod_cast hcard
    _ = (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) := by push_cast; ring


/-- **The bad-n bound**: if `n` is NOT a sum of two primes, the Λ-weighted representation
    count is supported on pairs containing a proper prime power, hence
    `≤ 2·log²n·√n·(log₂n+1)` — negligible against the main term `≍ n`. -/
lemma badRep_le (N n : ℕ) (hn : 1 ≤ n)
    (hbad : ¬ ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) :
    ∑ pr ∈ (Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n),
        Λ pr.1 * Λ pr.2
      ≤ 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) := by
  classical
  set F := (Finset.range N ×ˢ Finset.range N).filter (fun pr => pr.1 + pr.2 = n) with hF
  set F' := F.filter (fun pr => Λ pr.1 * Λ pr.2 ≠ 0) with hF'
  set PP := (Finset.Ioc 0 n).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0) with hPP
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hmem : ∀ pr ∈ F', pr.1 + pr.2 = n ∧ Λ pr.1 ≠ 0 ∧ Λ pr.2 ≠ 0 := by
    intro pr hpr
    rw [hF', Finset.mem_filter] at hpr
    obtain ⟨hprF, hne⟩ := hpr
    rw [hF, Finset.mem_filter] at hprF
    exact ⟨hprF.2, fun h => hne (by rw [h, zero_mul]),
      fun h => hne (by rw [h, mul_zero])⟩
  have hterm : ∀ pr ∈ F', Λ pr.1 * Λ pr.2 ≤ Real.log n ^ 2 := by
    intro pr hpr
    obtain ⟨hsum, h1, h2⟩ := hmem pr hpr
    have h1le : 2 ≤ pr.1 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1).two_le
    have h2le : 2 ≤ pr.2 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2).two_le
    have hb1 : Λ pr.1 ≤ Real.log n :=
      le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two h1le)
          (by exact_mod_cast Nat.le.intro hsum))
    have hb2 : Λ pr.2 ≤ Real.log n :=
      le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two h2le)
          (by exact_mod_cast Nat.le.intro (by omega : pr.2 + pr.1 = n)))
    calc Λ pr.1 * Λ pr.2 ≤ Real.log n * Real.log n :=
          mul_le_mul hb1 hb2 ArithmeticFunction.vonMangoldt_nonneg hlogn
      _ = Real.log n ^ 2 := (sq (Real.log n)).symm
  have hsplit : ∑ pr ∈ F', Λ pr.1 * Λ pr.2
      = (∑ pr ∈ F'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2)
        + ∑ pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2 :=
    (Finset.sum_filter_add_sum_filter_not F' _ _).symm
  -- the ¬prime-first-coordinate class injects into PP via pr ↦ pr.1
  have hcardA : (F'.filter (fun pr => ¬ pr.1.Prime)).card ≤ PP.card := by
    apply Finset.card_le_card_of_injOn (fun pr => pr.1)
    · intro pr hpr
      simp only [Finset.mem_coe, Finset.mem_filter] at hpr
      obtain ⟨hprF', hnp⟩ := hpr
      obtain ⟨hsum, h1, _⟩ := hmem pr hprF'
      have h1le : 2 ≤ pr.1 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1).two_le
      simp only [Finset.mem_coe, hPP, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, Nat.le.intro hsum⟩, hnp, h1⟩
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
      have hs1 := (hmem p1 hp1.1).1
      have hs2 := (hmem p2 hp2.1).1
      dsimp only at heq
      have : p1.2 = p2.2 := by omega
      exact Prod.ext heq this
  -- the prime-first-coordinate class: second coordinate is a proper prime power
  have hcardB : (F'.filter (fun pr => pr.1.Prime)).card ≤ PP.card := by
    apply Finset.card_le_card_of_injOn (fun pr => pr.2)
    · intro pr hpr
      simp only [Finset.mem_coe, Finset.mem_filter] at hpr
      obtain ⟨hprF', hp1⟩ := hpr
      obtain ⟨hsum, h1, h2⟩ := hmem pr hprF'
      have h2le : 2 ≤ pr.2 := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2).two_le
      have hnp2 : ¬ pr.2.Prime := by
        intro hp2
        exact hbad ⟨pr.1, pr.2, hp1, hp2, hsum.symm⟩
      simp only [Finset.mem_coe, hPP, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, Nat.le.intro (by omega : pr.2 + pr.1 = n)⟩, hnp2, h2⟩
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
      have hs1 := (hmem p1 hp1.1).1
      have hs2 := (hmem p2 hp2.1).1
      dsimp only at heq
      have : p1.1 = p2.1 := by omega
      exact Prod.ext this heq
  have hboundA : ∑ pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2
      ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
    calc ∑ pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2
        ≤ ∑ _pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Real.log n ^ 2 :=
          Finset.sum_le_sum (fun pr hpr => hterm pr (Finset.mem_of_mem_filter pr hpr))
      _ = ((F'.filter (fun pr => ¬ pr.1.Prime)).card : ℝ) * Real.log n ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcardA
  have hboundB : ∑ pr ∈ F'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2
      ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
    calc ∑ pr ∈ F'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2
        ≤ ∑ _pr ∈ F'.filter (fun pr => pr.1.Prime), Real.log n ^ 2 :=
          Finset.sum_le_sum (fun pr hpr => hterm pr (Finset.mem_of_mem_filter pr hpr))
      _ = ((F'.filter (fun pr => pr.1.Prime)).card : ℝ) * Real.log n ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PP.card : ℝ) * Real.log n ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcardB
  have hPPbound := card_properPrimePow_le n
  rw [← hPP] at hPPbound
  calc ∑ pr ∈ F, Λ pr.1 * Λ pr.2
      = ∑ pr ∈ F', Λ pr.1 * Λ pr.2 := (Finset.sum_filter_ne_zero F).symm
    _ = (∑ pr ∈ F'.filter (fun pr => pr.1.Prime), Λ pr.1 * Λ pr.2)
        + ∑ pr ∈ F'.filter (fun pr => ¬ pr.1.Prime), Λ pr.1 * Λ pr.2 := hsplit
    _ ≤ (PP.card : ℝ) * Real.log n ^ 2 + (PP.card : ℝ) * Real.log n ^ 2 :=
        add_le_add hboundB hboundA
    _ = 2 * Real.log n ^ 2 * (PP.card : ℝ) := by ring
    _ ≤ 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) := by
        apply mul_le_mul_of_nonneg_left hPPbound (by positivity)


/-- **Non-unit residue classes carry negligible Λ-mass**: if `gcd(r,q) > 1`, every
    prime in the class `n ≡ r (q)` divides `q` (finitely many, ≤ q+1) and everything
    else is a proper prime power (≤ √t·(log₂t+1)); each term is ≤ log t. Hence the
    class sum is `O(√t · polylog t) = o(t)` — its Cesàro density is 0, completing
    `major_window_eval`'s hypothesis for `g = Λ` off the units. -/
lemma nonunit_class_vonMangoldt_sum_le (q r t : ℕ) (hq : 0 < q) (hd : 1 < Nat.gcd r q) :
    ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
      ≤ ((q : ℝ) + 1) * Real.log t
        + (Nat.sqrt t : ℝ) * (Nat.log 2 t + 1) * Real.log t := by
  classical
  set F := (Finset.range t).filter (fun n => n % q = r) with hF
  have hlogt : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hterm : ∀ n ∈ F, Λ n ≤ Real.log t := by
    intro n hn
    rw [hF, Finset.mem_filter, Finset.mem_range] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simpa using hlogt
    calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log t := Real.log_le_log (by exact_mod_cast hn0)
          (by exact_mod_cast hn.1.le)
  have hΛnn : ∀ n, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  rw [← Finset.sum_filter_add_sum_filter_not F (fun n => n.Prime) Λ]
  have hprime_bound : ∑ n ∈ F.filter (fun n => n.Prime), Λ n ≤ ((q : ℝ) + 1) * Real.log t := by
    have hsub : F.filter (fun n => n.Prime) ⊆ Finset.range (q + 1) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnF, hp⟩ := hn
      rw [hF, Finset.mem_filter] at hnF
      have hgcd : Nat.gcd n q = Nat.gcd r q := by
        rw [Nat.gcd_comm n q, Nat.gcd_rec q n, hnF.2]
      have hdvd : n ∣ q := by
        have h1 : Nat.gcd n q ∣ n := Nat.gcd_dvd_left n q
        have h2 : 1 < Nat.gcd n q := by rw [hgcd]; exact hd
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ h1) with h | h
        · omega
        · rw [← h]
          exact Nat.gcd_dvd_right n q
      rw [Finset.mem_range]
      have := Nat.le_of_dvd hq hdvd
      omega
    calc ∑ n ∈ F.filter (fun n => n.Prime), Λ n
        ≤ ∑ _n ∈ F.filter (fun n => n.Prime), Real.log t :=
          Finset.sum_le_sum (fun n hn => hterm n (Finset.mem_of_mem_filter n hn))
      _ = ((F.filter (fun n => n.Prime)).card : ℝ) * Real.log t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((q : ℝ) + 1) * Real.log t := by
          apply mul_le_mul_of_nonneg_right _ hlogt
          have := Finset.card_le_card hsub
          rw [Finset.card_range] at this
          exact_mod_cast this
  have hpp_bound : ∑ n ∈ F.filter (fun n => ¬ n.Prime), Λ n
      ≤ (Nat.sqrt t : ℝ) * (Nat.log 2 t + 1) * Real.log t := by
    have hdrop : ∑ n ∈ F.filter (fun n => ¬ n.Prime), Λ n
        = ∑ n ∈ (F.filter (fun n => ¬ n.Prime)).filter (fun n => Λ n ≠ 0), Λ n :=
      (Finset.sum_filter_ne_zero _).symm
    rw [hdrop]
    have hsub : (F.filter (fun n => ¬ n.Prime)).filter (fun n => Λ n ≠ 0)
        ⊆ (Finset.Ioc 0 t).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0) := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      obtain ⟨⟨hnF, hnp⟩, hΛ⟩ := hn
      rw [hF, Finset.mem_filter, Finset.mem_range] at hnF
      rw [Finset.mem_filter, Finset.mem_Ioc]
      have h2 : 2 ≤ n := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ).two_le
      exact ⟨⟨by omega, by omega⟩, hnp, hΛ⟩
    calc ∑ n ∈ (F.filter (fun n => ¬ n.Prime)).filter (fun n => Λ n ≠ 0), Λ n
        ≤ ∑ n ∈ (Finset.Ioc 0 t).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0), Λ n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hΛnn n)
      _ ≤ ∑ _n ∈ (Finset.Ioc 0 t).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0), Real.log t := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Ioc] at hn
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · simpa using hlogt
          calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
            _ ≤ Real.log t := Real.log_le_log (by exact_mod_cast hn0)
                (by exact_mod_cast hn.1.2)
      _ = ((((Finset.Ioc 0 t).filter (fun m => ¬ m.Prime ∧ Λ m ≠ 0)).card : ℝ))
            * Real.log t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nat.sqrt t : ℝ) * (Nat.log 2 t + 1) * Real.log t :=
          mul_le_mul_of_nonneg_right (card_properPrimePow_le t) hlogt
  linarith


open Filter Real in
/-- **Non-unit classes have Cesàro density 0** (ℂ-cast form consumed by
    `major_window_eval`): the `O(√t·polylog)` mass bound divided by `t` vanishes. -/
lemma nonunit_class_tendsto_zero (q r : ℕ) (hq : 0 < q) (hd : 1 < Nat.gcd r q) :
    Filter.Tendsto (fun t : ℕ =>
      (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ)) / (t : ℂ))
      Filter.atTop (nhds 0) := by
  set f : ℕ → ℝ := fun t =>
    (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n) / (t : ℝ) with hf
  have hreal : Tendsto f atTop (nhds 0) := by
    set K : ℝ := 8 * ((q : ℝ) + 1) + 136 with hK
    have hg0 : Tendsto (fun t : ℕ => K * (t : ℝ) ^ (-(1/8) : ℝ)) atTop (nhds 0) := by
      have h2 : Tendsto (fun t : ℕ => ((t : ℝ)) ^ (-(1/8) : ℝ)) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
      simpa using h2.const_mul K
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg0
    · apply Eventually.of_forall
      intro t
      apply div_nonneg (Finset.sum_nonneg fun n _ => vonMangoldt_nonneg) (Nat.cast_nonneg t)
    · filter_upwards [eventually_ge_atTop 2] with t ht
      have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two ht
      have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast le_trans (by norm_num : (1:ℕ) ≤ 2) ht
      have hrp1 : (1:ℝ) ≤ (t:ℝ) ^ ((1/8) : ℝ) := Real.one_le_rpow ht1 (by norm_num)
      have hrpnn : (0:ℝ) ≤ (t:ℝ) ^ ((1/8) : ℝ) := by positivity
      -- log t ≤ 8 t^{1/8}
      have hlog8 : Real.log t ≤ 8 * (t:ℝ) ^ ((1/8) : ℝ) := by
        have h := Real.log_le_rpow_div (le_of_lt ht0) (show (0:ℝ) < 1/8 by norm_num)
        have h8 : (t:ℝ) ^ ((1/8) : ℝ) / (1/8) = 8 * (t:ℝ) ^ ((1/8) : ℝ) := by ring
        linarith [h, h8.le, h8.ge]
      have hlognn : (0:ℝ) ≤ Real.log t := Real.log_natCast_nonneg t
      -- Nat.log 2 t + 1 ≤ 17 t^{1/8}
      have hnlog : (Nat.log 2 t : ℝ) + 1 ≤ 17 * (t:ℝ) ^ ((1/8) : ℝ) := by
        have hpow : (2:ℕ) ^ (Nat.log 2 t) ≤ t := Nat.pow_log_le_self 2 (by omega)
        have hlogle : (Nat.log 2 t : ℝ) * Real.log 2 ≤ Real.log t := by
          have hcast : ((2:ℕ) ^ (Nat.log 2 t) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hpow
          have := Real.log_le_log (by positivity) hcast
          rwa [Real.log_pow, Nat.cast_ofNat] at this
        have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hk2 : (Nat.log 2 t : ℝ) ≤ 2 * Real.log t := by
          nlinarith [hlogle, hl2, (by positivity : (0:ℝ) ≤ ((Nat.log 2 t : ℕ) : ℝ))]
        nlinarith [hlog8, hrp1]
      -- Nat.sqrt t ≤ t^{1/2}
      have hsqrt : (Nat.sqrt t : ℝ) ≤ (t:ℝ) ^ ((1/2) : ℝ) := by
        have h1 : (Nat.sqrt t : ℝ) ^ 2 ≤ (t : ℝ) := by
          exact_mod_cast Nat.sqrt_le' t
        have h4 : (Nat.sqrt t : ℝ) ≤ Real.sqrt (t:ℝ) :=
          (Real.le_sqrt (Nat.cast_nonneg _) (le_of_lt ht0)).mpr h1
        rwa [Real.sqrt_eq_rpow] at h4
      -- assemble
      have hsum := nonunit_class_vonMangoldt_sum_le q r t hq hd
      have hnum : (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
          ≤ 8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8) : ℝ) + 136 * (t:ℝ) ^ ((3/4) : ℝ) := by
        have hA : ((q : ℝ) + 1) * Real.log t ≤ 8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8) : ℝ) := by
          have hq1 : (0:ℝ) ≤ (q:ℝ) + 1 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hlog8 hq1]
        have hB : (Nat.sqrt t : ℝ) * (Nat.log 2 t + 1) * Real.log t
            ≤ 136 * (t:ℝ) ^ ((3/4) : ℝ) := by
          have hs1 : (Nat.sqrt t : ℝ) * ((Nat.log 2 t : ℝ) + 1) * Real.log t
              ≤ (t:ℝ) ^ ((1/2) : ℝ) * (17 * (t:ℝ) ^ ((1/8) : ℝ)) * (8 * (t:ℝ) ^ ((1/8) : ℝ)) := by
            apply mul_le_mul
            · apply mul_le_mul hsqrt hnlog (by positivity) (by positivity)
            · exact hlog8
            · exact hlognn
            · positivity
          have hcollect : (t:ℝ) ^ ((1/2) : ℝ) * (17 * (t:ℝ) ^ ((1/8) : ℝ))
                * (8 * (t:ℝ) ^ ((1/8) : ℝ))
              = 136 * ((t:ℝ) ^ ((1/2) : ℝ) * (t:ℝ) ^ ((1/8) : ℝ) * (t:ℝ) ^ ((1/8) : ℝ)) := by
            ring
          have hexp : (t:ℝ) ^ ((1/2) : ℝ) * (t:ℝ) ^ ((1/8) : ℝ) * (t:ℝ) ^ ((1/8) : ℝ)
              = (t:ℝ) ^ ((3/4) : ℝ) := by
            rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
            norm_num
          rw [hcollect, hexp] at hs1
          exact hs1
        linarith
      -- divide by t and compare exponents
      rw [hf]
      have hdiv : (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n) / (t:ℝ)
          ≤ (8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8) : ℝ) + 136 * (t:ℝ) ^ ((3/4) : ℝ)) / (t:ℝ) := by
        gcongr
      have hsplit : (8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8) : ℝ) + 136 * (t:ℝ) ^ ((3/4) : ℝ)) / (t:ℝ)
          = 8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8 - 1) : ℝ) + 136 * (t:ℝ) ^ ((3/4 - 1) : ℝ) := by
        rw [Real.rpow_sub ht0, Real.rpow_sub ht0, Real.rpow_one]
        ring
      have hmono1 : (t:ℝ) ^ ((1/8 - 1) : ℝ) ≤ (t:ℝ) ^ (-(1/8) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      have hmono2 : (t:ℝ) ^ ((3/4 - 1) : ℝ) ≤ (t:ℝ) ^ (-(1/8) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      have hKnn : (0:ℝ) ≤ (t:ℝ) ^ (-(1/8) : ℝ) := by positivity
      calc (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n) / (t:ℝ)
          ≤ 8 * ((q:ℝ) + 1) * (t:ℝ) ^ ((1/8 - 1) : ℝ) + 136 * (t:ℝ) ^ ((3/4 - 1) : ℝ) := by
            rw [← hsplit]
            exact hdiv
        _ ≤ K * (t:ℝ) ^ (-(1/8) : ℝ) := by
            rw [hK]
            have hq1 : (0:ℝ) ≤ 8 * ((q:ℝ) + 1) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hmono1 hq1,
              mul_le_mul_of_nonneg_left hmono2 (show (0:ℝ) ≤ 136 by norm_num)]
  have hcast : (fun t : ℕ =>
      (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ)) / (t : ℂ))
      = fun t => ((f t : ℝ) : ℂ) := by
    funext t
    rw [hf]
    push_cast
    ring
  rw [hcast]
  have hcomp := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hreal
  rw [Complex.ofReal_zero] at hcomp
  exact hcomp



open Filter in
/-- **The von Mangoldt window evaluation**, conditional on EXACTLY the `WeakPNT_AP`
    statement shape (verified in PNT+ for every fixed `q`; hypothesis dischargeable at
    link time). Every Farey window evaluation of `∑Λ(n)e(nα)` against its model, with
    no uniformity in `q`. -/
theorem vonMangoldt_window_eval (q : ℕ) (hq : 0 < q)
    (hAP : ∀ r, r < q → Nat.gcd r q = 1 →
      Filter.Tendsto (fun t : ℕ =>
        (∑ n ∈ Finset.range t, if n % q = r then Λ n else 0) / (t : ℝ))
        Filter.atTop (nhds (1 / (Nat.totient q : ℝ))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ a : ℤ, ∀ β : ℝ,
      ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
        - (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ (q : ℝ) * ((ε * N + C) * (1 + 2 * Real.pi * N * |β|)) := by
  apply major_window_eval (fun n => ((Λ n : ℝ) : ℂ)) q hq (lambdaModel q) _ ε hε
  intro r hr
  by_cases hu : Nat.gcd r q = 1
  · -- unit class: convert WeakPNT_AP's real if-form to the ℂ filter form
    have hAPr := hAP r hr hu
    have hfun : (fun t : ℕ =>
        (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ)) / (t : ℂ))
        = fun t : ℕ =>
          (((∑ n ∈ Finset.range t, if n % q = r then Λ n else 0) / (t : ℝ) : ℝ) : ℂ) := by
      funext t
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      push_cast
      ring
    rw [hfun]
    have hmodel : lambdaModel q r = (((1 / (Nat.totient q : ℝ)) : ℝ) : ℂ) := by
      rw [lambdaModel, if_pos hu]
      push_cast
      ring
    rw [hmodel]
    exact (Complex.continuous_ofReal.tendsto _).comp hAPr
  · -- non-unit class: density zero
    have hd : 1 < Nat.gcd r q := by
      have h0 : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
      omega
    have hmodel : lambdaModel q r = 0 := by
      rw [lambdaModel, if_neg hu]
    rw [hmodel]
    exact nonunit_class_tendsto_zero q r hq hd


open ArithmeticFunction in
/-- **The model coefficient in closed form**: at a reduced fraction `a/q`, the window
    model's coefficient is `μ(q)/φ(q)` — the Hardy–Littlewood singular-series local
    factor. -/
lemma lambdaModel_coeff (a : ℤ) (q : ℕ) (hq : 0 < q) (ha : Int.gcd a q = 1) :
    ∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r
      = (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) := by
  calc ∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r
      = ∑ r ∈ Finset.range q,
          if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) * (1 / (Nat.totient q : ℂ)) else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [lambdaModel]
        by_cases h : Nat.gcd r q = 1
        · rw [if_pos h, if_pos h]
          congr 2
          ring
        · rw [if_neg h, if_neg h, mul_zero]
    _ = ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
          e ((a : ℝ) * r / q) * (1 / (Nat.totient q : ℂ)) := (Finset.sum_filter _ _).symm
    _ = (∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q))
          * (1 / (Nat.totient q : ℂ)) := by rw [Finset.sum_mul]
    _ = (ArithmeticFunction.moebius q : ℂ) * (1 / (Nat.totient q : ℂ)) := by
        rw [ramanujan_sum_coprime a q hq ha]
    _ = (ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ) := by ring


open ArithmeticFunction in
/-- The singular-series local factor has modulus at most 1. -/
lemma moebius_div_totient_norm_le (q : ℕ) (hq : 0 < q) :
    ‖(ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)‖ ≤ 1 := by
  have hφ : 1 ≤ Nat.totient q := (Nat.totient_pos.mpr hq)
  rw [norm_div]
  have h1 : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := q)
    calc ‖(ArithmeticFunction.moebius q : ℂ)‖
        = |(ArithmeticFunction.moebius q : ℝ)| := by
          rw [show ((ArithmeticFunction.moebius q : ℤ) : ℂ)
              = (((ArithmeticFunction.moebius q : ℤ) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 := by exact_mod_cast this
  have h2 : (1:ℝ) ≤ ‖(Nat.totient q : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast hφ
  have h3 : (0:ℝ) < ‖(Nat.totient q : ℂ)‖ := lt_of_lt_of_le one_pos h2
  calc ‖(ArithmeticFunction.moebius q : ℂ)‖ / ‖(Nat.totient q : ℂ)‖
      ≤ 1 / ‖(Nat.totient q : ℂ)‖ := by
        gcongr
    _ ≤ 1 / 1 := by
        apply one_div_le_one_div_of_le one_pos h2
    _ = 1 := by norm_num

open ArithmeticFunction in
/-- Every model coefficient has modulus at most 1. -/
lemma lambdaModel_norm_le (q r : ℕ) (hq : 0 < q) : ‖lambdaModel q r‖ ≤ 1 := by
  rw [lambdaModel]
  by_cases h : Nat.gcd r q = 1
  · rw [if_pos h, norm_div, norm_one, Complex.norm_natCast]
    have hφ : (1:ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq
    rw [div_le_one (by linarith)]
    linarith
  · rw [if_neg h, norm_zero]
    norm_num


/-- Trivial sup bound for the Λ-exponential sum: `‖S(α)‖ ≤ N·log N` everywhere. -/
lemma vonMangoldt_expsum_sup (N : ℕ) (α : ℝ) :
    ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ (N : ℝ) * Real.log N := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
      ≤ ∑ n ∈ Finset.Ioc 0 N, ‖((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc 0 N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Ioc] at hn
        rw [norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast hn.1)
              (by exact_mod_cast hn.2)
    _ = (N : ℝ) * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]

end VonMangoldtParseval

section ArcDecomposition

/-- **Arc decomposition (Dirichlet approximation, reduced form)**: every real `α` has a
    reduced rational anchor `a/q` with `q ≤ Q`, `gcd(a,q) = 1`, and
    `|α − a/q| ≤ 1/(q(Q+1)) ≤ 1/q²` — assigning each point of the circle to a Farey arc.
    The `1/q²` form is exactly the hypothesis of `MinSum.vinogradov_sup`. -/
lemma arc_decomposition (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ q ≤ Q ∧ Int.gcd a q = 1 ∧
      |α - a / q| ≤ 1 / (q * (Q + 1)) ∧ |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQ
  have hqpos : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hbound : |α - (r.num : ℝ) / (r.den : ℝ)| ≤ 1 / (r.den * (Q + 1)) := by
    calc |α - (r.num : ℝ) / (r.den : ℝ)| = |α - (r : ℝ)| := by rw [Rat.cast_def]
      _ ≤ 1 / ((Q + 1) * r.den) := hr
      _ = 1 / (r.den * (Q + 1)) := by ring
  refine ⟨r.num, r.den, r.pos, hden, by simpa [Int.gcd] using r.reduced, hbound, ?_⟩
  refine le_trans hbound ?_
  apply one_div_le_one_div_of_le (by positivity)
  have hle : (r.den : ℝ) ≤ Q := by exact_mod_cast hden
  nlinarith [hqpos]


/-- **Major/minor arc dichotomy**: with cutoffs `P ≤ Q`, every `α` is either in a MAJOR
    arc (anchor denominator `q ≤ P`, tight `1/(q(Q+1))` window) or a MINOR arc
    (`P < q ≤ Q` with `|α − a/q| ≤ 1/q²` — the exact input to `MinSum.vinogradov_sup`,
    whose `2 ≤ q` hypothesis follows from `P < q` when `1 ≤ P`). -/
lemma arc_dichotomy (α : ℝ) (P Q : ℕ) (hP : 0 < P) (hPQ : P ≤ Q) :
    (∃ (a : ℤ) (q : ℕ), 0 < q ∧ q ≤ P ∧ Int.gcd a q = 1 ∧
        |α - a / q| ≤ 1 / (q * (Q + 1)))
    ∨ (∃ (a : ℤ) (q : ℕ), P < q ∧ q ≤ Q ∧ Int.gcd a q = 1 ∧
        |α - a / q| ≤ 1 / (q : ℝ) ^ 2) := by
  obtain ⟨a, q, hq0, hqQ, hgcd, hnear, hsq⟩ :=
    arc_decomposition α Q (lt_of_lt_of_le hP hPQ)
  by_cases hqP : q ≤ P
  · exact Or.inl ⟨a, q, hq0, hqP, hgcd, hnear⟩
  · exact Or.inr ⟨a, q, lt_of_not_ge hqP, hqQ, hgcd, hsq⟩



lemma measurableSet_majorArcs (P Q : ℕ) : MeasurableSet (MajorArcs P Q) := by
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro q _
  apply MeasurableSet.iUnion
  intro a
  exact measurableSet_closedBall

/-- **The canonical minor set works**: every point of `(0,1] \ MajorArcs` has a reduced
    anchor with `P < q ≤ Q` and `|α − a/q| ≤ 1/q²` — `vinogradov_sup`'s hypothesis. -/
lemma minorSet_property (P Q : ℕ) (hP : 0 < P) (hPQ : P ≤ Q) (α : ℝ)
    (hα : α ∈ Set.Ioc (0:ℝ) 1 \ MajorArcs P Q) :
    ∃ (a : ℤ) (q : ℕ), P < q ∧ q ≤ Q ∧ Int.gcd a q = 1 ∧
      |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
  obtain ⟨_, hnot⟩ := hα
  rcases arc_dichotomy α P Q hP hPQ with ⟨a, q, hq0, hqP, _, hnear⟩ | h
  · exfalso
    apply hnot
    refine Set.mem_biUnion ⟨hq0, hqP⟩ ?_
    refine Set.mem_iUnion.mpr ⟨a, ?_⟩
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact hnear
  · exact h

/-- **Minor-arc anchor is a coprime natural**: the Dirichlet anchor `a : ℤ` of a point
    `α ∈ (0,1]` with `|α − a/q| ≤ 1/q²`, `gcd(a,q)=1`, `q ≥ 2` is in fact a positive
    integer, so `a.toNat` is a coprime-to-`q` natural with the same approximation — the
    exact `(a q : ℕ)` input `MinSum.vinogradov_sup_tight2` demands (its bound depends only
    on `q`, `U`, `V`, `N`, never on `a`). -/
lemma minor_anchor_nat (α : ℝ) (a : ℤ) (q : ℕ) (hq2 : 2 ≤ q) (hpos : 0 < α)
    (hgcd : Int.gcd a q = 1) (hsq : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    Nat.Coprime a.toNat q ∧ |α - (a.toNat : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    linarith
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hane : a ≠ 0 := by
    rintro rfl
    simp at hgcd
    omega
  have ha1 : 1 ≤ a := by
    rcases lt_or_ge a 1 with h | h
    · exfalso
      have hcast : (a : ℝ) ≤ -1 := by exact_mod_cast (by omega : a ≤ -1)
      have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
      have habs := abs_le.mp hsq
      have hm := mul_le_mul_of_nonneg_right habs.2 (sq_nonneg (q : ℝ))
      rw [one_div_mul_cancel (show (q : ℝ) ^ 2 ≠ 0 by positivity)] at hm
      have hlhs : (α - (a : ℝ) / q) * (q : ℝ) ^ 2 = α * (q : ℝ) ^ 2 - (a : ℝ) * q := by
        field_simp
      rw [hlhs] at hm
      nlinarith [hm, mul_le_mul_of_nonneg_right hcast (le_of_lt hqR),
        mul_pos hpos (by positivity : (0 : ℝ) < (q : ℝ) ^ 2), hq2R]
    · exact h
  have hcop : Nat.Coprime a.toNat q := by
    have h1 : a.toNat = a.natAbs := by omega
    have h2 : Int.gcd a (q : ℤ) = a.natAbs.gcd q := by simp [Int.gcd]
    unfold Nat.Coprime
    rw [h1]
    omega
  refine ⟨hcop, ?_⟩
  have hcast2 : (a.toNat : ℝ) = (a : ℝ) := by
    have : ((a.toNat : ℤ) : ℝ) = (a : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
    exact_mod_cast this
  rw [hcast2]
  exact hsq

open ArithmeticFunction
open scoped ArithmeticFunction

/-- The explicit RHS of `MinSum.vinogradov_sup_tight2` (the tight minor-arc sup bound),
    packaged as a function of `(q, U, V, N)` — the bound depends on the anchor only through
    its denominator `q`. Written verbatim so the cross-file `vinogradov_sup_tight2` axiom
    below is `rfl`-dischargeable by the real theorem at Phase-F concatenation. -/
noncomputable def tightSupRHS (q U V N : ℕ) : ℝ :=
  2 * Real.log (N + 1) *
      (((2 * (N : ℝ) / q) * (1 + Real.log U)
        + ((U / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))) + U)
    + Real.log (U * V) *
      ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
        + ((U * V / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
    + (V : ℝ) * Real.log V
    + Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
        + Real.sqrt 32 * N
            * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ) / Real.sqrt q
        + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
        + 6 * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
            * Real.sqrt (N * q * (1 + Real.log (2 * q))))


/-- **Minor-arc uniform sup**: given a `Csup` dominating `tightSupRHS q U V N` for every
    minor modulus `P < q ≤ Q` (the envelope bound — the remaining analytic step), the
    exponential sum is `≤ Csup` uniformly on `(0,1] \ MajorArcs P Q`. Combines the arc
    decomposition, the `minor_anchor_nat` bridge, and `vinogradov_sup_tight2`. This is the
    exact `hsup` input to `minor_arc_variance_piece`. -/
lemma minor_sup_uniform (N P Q U V : ℕ) (hP : 0 < P) (hPQ : P ≤ Q)
    (hU : U ≤ N) (hUV : U * V ≤ N) (hUV1 : 1 ≤ U * V) (Csup : ℝ)
    (henv : ∀ q, P < q → q ≤ Q → tightSupRHS q U V N ≤ Csup) :
    ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q,
      ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ Csup := by
  intro α hα
  obtain ⟨a, q, hPq, hqQ, hgcd, hsq⟩ := minorSet_property P Q hP hPQ α hα
  have hq2 : 2 ≤ q := by omega
  have hpos : (0 : ℝ) < α := hα.1.1
  obtain ⟨hcop, hanchor⟩ := minor_anchor_nat α a q hq2 hpos hgcd hsq
  have hb := vinogradov_sup_tight2 a.toNat q hq2 hcop α hanchor U V N hU hUV hUV1
  exact le_trans hb (henv q hPq hqQ)

/-- Envelope helper: the Type-I block factor `(U/⌊q/2⌋+1)·(4q(2+log 2q))` telescopes
    (the `q` cancels the `1/(q/2)`) to `≤ (16U+4Q)(2+log 2Q)`, uniform for `2 ≤ q ≤ Q`. -/
lemma env_natdiv_bound (U q Q : ℕ) (hq2 : 2 ≤ q) (hqQ : q ≤ Q) :
    ((U / (q / 2) + 1 : ℕ) : ℝ) * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))
      ≤ (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) := by
  have hqRle : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqR : (0 : ℝ) < (q : ℝ) := by linarith
  have hQ2 : 2 ≤ Q := le_trans hq2 hqQ
  have hQRle : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have hlogq0 : (0 : ℝ) ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
  have hlogmono : Real.log (2 * (q : ℝ)) ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hnd : ((U / (q / 2) : ℕ) : ℝ) ≤ 4 * (U : ℝ) / q := by
    have h2 : q ≤ 4 * (q / 2) := by omega
    have h1 : (U / (q / 2)) * (q / 2) ≤ U := Nat.div_mul_le_self _ _
    have hnat : q * (U / (q / 2)) ≤ 4 * U := by
      calc q * (U / (q / 2)) ≤ 4 * (q / 2) * (U / (q / 2)) := Nat.mul_le_mul_right _ h2
        _ = 4 * ((U / (q / 2)) * (q / 2)) := by ring
        _ ≤ 4 * U := Nat.mul_le_mul_left _ h1
    rw [le_div_iff₀ hqR]
    calc ((U / (q / 2) : ℕ) : ℝ) * q = ((q * (U / (q / 2)) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((4 * U : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = 4 * U := by push_cast; ring
  have hfac : (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q)))
      = 4 * q * (2 + Real.log (2 * q)) := by ring
  rw [hfac]
  have hcast : ((U / (q / 2) + 1 : ℕ) : ℝ) = ((U / (q / 2) : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hLog2q : (0 : ℝ) ≤ 2 + Real.log (2 * q) := by linarith
  calc (((U / (q / 2) : ℕ) : ℝ) + 1) * (4 * q * (2 + Real.log (2 * q)))
      ≤ (4 * U / q + 1) * (4 * q * (2 + Real.log (2 * q))) := by
        apply mul_le_mul_of_nonneg_right (by linarith [hnd]) (by positivity)
    _ = (16 * U + 4 * q) * (2 + Real.log (2 * q)) := by field_simp; ring
    _ ≤ (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) := by
        apply mul_le_mul (by linarith) (by linarith) hLog2q (by positivity)

/-- **The envelope bound** (`henv` for `minor_sup_uniform`): the tight sup RHS is
    dominated, uniformly for `P < q ≤ Q`, by an explicit `Csup` in `N,U,V,P,Q` — the
    `q`-decreasing terms bounded via `q ≥ P`, the `q`-increasing via `q ≤ Q`, and the
    Type-I block factors telescoped by `env_natdiv_bound`. This discharges the `henv`
    hypothesis of `minor_sup_uniform` for the canonical `Csup`. -/
lemma tightSupRHS_le (N U V P Q q : ℕ)
    (hN1 : 1 ≤ N) (hP1 : 1 ≤ P) (hU1 : 1 ≤ U) (hV1 : 1 ≤ V)
    (hPq : P < q) (hqQ : q ≤ Q) :
    tightSupRHS q U V N ≤
      2 * Real.log (N + 1) * ((2 * (N : ℝ) / P) * (1 + Real.log U)
          + (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) + U)
      + Real.log (U * V) * ((2 * (N : ℝ) / P) * (1 + Real.log (U * V))
          + (16 * (U * V) + 4 * Q) * (2 + Real.log (2 * Q)))
      + (V : ℝ) * Real.log V
      + Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt P
          + 64 * N * Real.sqrt (1 + Real.log (2 * Q)) / Real.sqrt U
          + 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (N * Q * (1 + Real.log (2 * Q)))) := by
  have hq2 : 2 ≤ q := by omega
  have hqRle : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP1
  have hqR : (0 : ℝ) < (q : ℝ) := by linarith
  have hQ2 : 2 ≤ Q := le_trans hq2 hqQ
  have hQRle : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
  have hPqR : (P : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_of_lt hPq
  have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have hUV1 : 1 ≤ U * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlogU0 : (0 : ℝ) ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU1)
  have hlogUV0 : (0 : ℝ) ≤ Real.log (U * V) := Real.log_nonneg (by exact_mod_cast hUV1)
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hlogN10 : (0 : ℝ) ≤ Real.log (↑N + 1) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith)
  have hlogmono : Real.log (2 * (q : ℝ)) ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2q0 : (0 : ℝ) ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hk : ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
      ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
    have h := Nat.log_mono_right (b := 2) (Nat.div_le_self N (V + 1))
    exact_mod_cast (by omega :
      Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 ≤ Nat.log 2 N + 1)
  have h2NqP : (2 * (N : ℝ) / q) ≤ (2 * (N : ℝ) / P) := by
    gcongr
  unfold tightSupRHS
  have hB1 : 2 * Real.log (↑N + 1) *
        (((2 * (N : ℝ) / q) * (1 + Real.log U)
          + ((U / (q / 2) + 1 : ℕ) : ℝ) * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
          + U)
      ≤ 2 * Real.log (↑N + 1) * ((2 * (N : ℝ) / P) * (1 + Real.log U)
          + (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) + U) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith [hlogN10])
    refine add_le_add (add_le_add ?_ (env_natdiv_bound U q Q hq2 hqQ)) (le_refl _)
    exact mul_le_mul_of_nonneg_right h2NqP (by linarith [hlogU0])
  have hB2 : Real.log (↑U * ↑V) *
        ((2 * (N : ℝ) / q) * (1 + Real.log (U * V))
          + ((U * V / (q / 2) + 1 : ℕ) : ℝ) * (2 * (2 * (q : ℝ)) + 4 * q * (1 + Real.log (2 * q))))
      ≤ Real.log (↑U * ↑V) * ((2 * (N : ℝ) / P) * (1 + Real.log (U * V))
          + (16 * (U * V) + 4 * Q) * (2 + Real.log (2 * Q))) := by
    apply mul_le_mul_of_nonneg_left _ hlogUV0
    have henv2 := env_natdiv_bound (U * V) q Q hq2 hqQ
    rw [Nat.cast_mul] at henv2
    refine add_le_add ?_ henv2
    exact mul_le_mul_of_nonneg_right h2NqP (by linarith [hlogUV0])
  have hB4 : Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
        + Real.sqrt 32 * N * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
            / Real.sqrt q
        + 64 * N * Real.sqrt (1 + Real.log (2 * q)) / Real.sqrt U
        + 6 * ((Nat.log 2 (N / (V + 1)) - Nat.log 2 (U + 1) + 1 : ℕ) : ℝ)
            * Real.sqrt (N * q * (1 + Real.log (2 * q))))
      ≤ Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
          + Real.sqrt 32 * N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt P
          + 64 * N * Real.sqrt (1 + Real.log (2 * Q)) / Real.sqrt U
          + 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (N * Q * (1 + Real.log (2 * Q)))) := by
    apply mul_le_mul_of_nonneg_left _ hlogN0
    gcongr <;>
      first
      | exact hk
      | exact hPqR
      | exact hqQR
      | exact hqRle
      | exact Real.sqrt_nonneg _
      | exact Real.sqrt_pos.mpr hPR
      | positivity
      | linarith [hlogmono]
      | linarith [hlog2q0]
  linarith [hB1, hB2, hB4]


/-- **D5 — the minor-arc L⁴ variance bound**: the mean-square of `S(α)² − (model)` over the
    minor arcs `(0,1] \ MajorArcs P Q` is `≤ 2·Csup²·∑Λ(n)² + 2·∑‖c(n)‖²`, with the concrete
    `Csup = minorCsup N U V P Q`. Composes `minor_sup_uniform` (uniform sup via the anchor
    bridge + `vinogradov_sup_tight2`) discharged by `tightSupRHS_le` (envelope) into
    `minor_arc_variance_piece`. The remaining smallness (`Csup²·∑Λ² ≤ εN³` for `U=V~N^{2/5}`,
    `P=(log N)^B`, `Q=N/P`, `B≥20`) is one numeric instantiation at `hvar` closure. -/
lemma minor_variance_bound (N M P Q U V : ℕ) (hP1 : 1 ≤ P) (hPQ : P ≤ Q)
    (hN1 : 1 ≤ N) (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hU : U ≤ N) (hUV : U * V ≤ N) (c : ℕ → ℂ) :
    ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖(∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2
          - ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α)‖ ^ 2
      ≤ 2 * (minorCsup N U V P Q ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2)
        + 2 * ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
  have hUV1 : 1 ≤ U * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsup : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q,
      ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ minorCsup N U V P Q :=
    minor_sup_uniform N P Q U V (by omega) hPQ hU hUV hUV1 (minorCsup N U V P Q)
      (fun q hPq hqQ => tightSupRHS_le N U V P Q q hN1 hP1 hU1 hV1 hPq hqQ)
  exact minor_arc_variance_piece N M (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q)
    (measurableSet_Ioc.diff (measurableSet_majorArcs P Q)) Set.diff_subset c
    (minorCsup N U V P Q) hsup

/-- **D5 minor L⁴, packaged for the variance assembly**: `∫_{minor} ‖S‖⁴ ≤ minorCsup²·∑Λ²`
    with the concrete `minorCsup` — the pure-L⁴ form (no model subtraction) that feeds the
    first term of `variance_le_bessel`. Composes `minor_arc_L4_bound` with the uniform sup. -/
lemma minor_L4_tight (N P Q U V : ℕ) (hP1 : 1 ≤ P) (hPQ : P ≤ Q)
    (hN1 : 1 ≤ N) (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hU : U ≤ N) (hUV : U * V ≤ N) :
    ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ^ 4
      ≤ minorCsup N U V P Q ^ 2 * ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
  have hUV1 : 1 ≤ U * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsup : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q,
      ‖∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ minorCsup N U V P Q :=
    minor_sup_uniform N P Q U V (by omega) hPQ hU hUV hUV1 (minorCsup N U V P Q)
      (fun q hPq hqQ => tightSupRHS_le N U V P Q q hN1 hP1 hU1 hV1 hPq hqQ)
  exact minor_arc_L4_bound N (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q)
    (measurableSet_Ioc.diff (measurableSet_majorArcs P Q)) Set.diff_subset
    (minorCsup N U V P Q) hsup

/-- **D5 minor L⁴ in `range N` form** (the shape `variance_le_bessel` / the major-arc chain
    use): `∫_{minor} ‖(∑_{k<N} Λ(k)e(kα))²‖² ≤ (minorCsup + log N)²·∑_{k<N} Λ(k)²`. Bridges
    `∑_{range N} = ∑_{Ioc 0 N} − Λ(N)e(Nα)` (so the range-sup is `minorCsup + Λ(N) ≤
    minorCsup + log N`), then applies the general `L4_set_bound`. -/
lemma minor_L4_range (N P Q U V : ℕ) (hP1 : 1 ≤ P) (hPQ : P ≤ Q)
    (hN1 : 1 ≤ N) (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hU : U ≤ N) (hUV : U * V ≤ N) :
    ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2
      ≤ (minorCsup N U V P Q + Real.log N) ^ 2 * ∑ n ∈ Finset.range N, Λ n ^ 2 := by
  have hUV1 : 1 ≤ U * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set f : ℝ → ℕ → ℂ := fun α n => ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α) with hf
  have hbridge : ∀ α : ℝ, ∑ n ∈ Finset.range N, f α n
      = (∑ n ∈ Finset.Ioc 0 N, f α n) - f α N := by
    intro α
    have hins : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
    have hf0 : f α 0 = 0 := by
      simp only [hf, ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul]
    have e1 : ∑ n ∈ Finset.Ioc 0 N, f α n = ∑ n ∈ Finset.range (N + 1), f α n := by
      rw [hins, Finset.sum_insert (by simp), hf0, zero_add]
    have e2 : ∑ n ∈ Finset.range (N + 1), f α n = ∑ n ∈ Finset.range N, f α n + f α N :=
      Finset.sum_range_succ (f α) N
    rw [e1, e2]; ring
  have hsup : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q,
      ‖∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖ ≤ minorCsup N U V P Q + Real.log N := by
    intro α hα
    have h1 := minor_sup_uniform N P Q U V (by omega) hPQ hU hUV hUV1 (minorCsup N U V P Q)
      (fun q hPq hqQ => tightSupRHS_le N U V P Q q hN1 hP1 hU1 hV1 hPq hqQ) α hα
    have hfN : ‖f α N‖ ≤ Real.log N := by
      rw [hf, norm_mul, e_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log
    calc ‖∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)‖
        = ‖(∑ n ∈ Finset.Ioc 0 N, f α n) - f α N‖ := by rw [hbridge α]
      _ ≤ ‖∑ n ∈ Finset.Ioc 0 N, f α n‖ + ‖f α N‖ := norm_sub_le _ _
      _ ≤ minorCsup N U V P Q + Real.log N := by
          have := h1
          rw [show (∑ n ∈ Finset.Ioc 0 N, f α n) = ∑ n ∈ Finset.Ioc 0 N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α) from rfl] at *
          linarith [hfN, h1]
  have hL4 := L4_set_bound (fun n => ((Λ n : ℝ) : ℂ)) N (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q)
    (measurableSet_Ioc.diff (measurableSet_majorArcs P Q)) Set.diff_subset
    (minorCsup N U V P Q + Real.log N) hsup
  have hnorm : ∀ n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ ^ 2 = Λ n ^ 2 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2
      ≤ (minorCsup N U V P Q + Real.log N) ^ 2 * ∑ n ∈ Finset.range N, ‖((Λ n : ℝ) : ℂ)‖ ^ 2 :=
        hL4
    _ = (minorCsup N U V P Q + Real.log N) ^ 2 * ∑ n ∈ Finset.range N, Λ n ^ 2 := by
        rw [Finset.sum_congr rfl (fun n _ => hnorm n)]


/-- `∑_{n<N} Λ(n)² ≤ N·(log N)²` (range form, from the banked `sum_vonMangoldt_sq_le`). -/
lemma sum_vonMangoldt_sq_range_le (N : ℕ) :
    ∑ n ∈ Finset.range N, Λ n ^ 2 ≤ (N : ℝ) * Real.log N ^ 2 := by
  calc ∑ n ∈ Finset.range N, Λ n ^ 2
      ≤ ∑ n ∈ Finset.range (N + 1), Λ n ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
        · intro n _ _; exact sq_nonneg _
    _ = ∑ n ∈ Finset.Ioc 0 N, Λ n ^ 2 := by
        rw [show Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) from by
          ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega,
          Finset.sum_insert (by simp)]
        simp [ArithmeticFunction.map_zero]
    _ ≤ (N : ℝ) * Real.log N ^ 2 := sum_vonMangoldt_sq_le N

/-- `minorCsup` is nonnegative (each of its four groups is a product/sum of nonneg factors,
    the logs being `≥ 0` since their arguments are `≥ 1`). -/
lemma minorCsup_nonneg (N P Q : ℕ) (hP2 : 2 ≤ P) (hN1 : 1 ≤ N) (hQ1 : 1 ≤ Q) :
    0 ≤ minorCsup N P P P Q := by
  have hPR : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (show 1 ≤ P by omega)
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlogP : (0 : ℝ) ≤ Real.log P := Real.log_nonneg hPR
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hNR
  have hlogN1 : (0 : ℝ) ≤ Real.log (↑N + 1) := Real.log_nonneg (by linarith)
  have hlogPP : (0 : ℝ) ≤ Real.log (↑P * ↑P) := Real.log_nonneg (by nlinarith [hPR])
  have hlog2Q : (0 : ℝ) ≤ Real.log (2 * ↑Q) := Real.log_nonneg (by linarith)
  unfold minorCsup
  have hb1 : (0 : ℝ) ≤ 2 * Real.log (↑N + 1) *
      ((2 * ↑N / ↑P) * (1 + Real.log ↑P) + (16 * ↑P + 4 * ↑Q) * (2 + Real.log (2 * ↑Q)) + ↑P) := by
    apply mul_nonneg (by linarith)
    apply add_nonneg (add_nonneg (mul_nonneg (by positivity) (by linarith))
      (mul_nonneg (by positivity) (by linarith))) (by positivity)
  have hb2 : (0 : ℝ) ≤ Real.log (↑P * ↑P) *
      ((2 * ↑N / ↑P) * (1 + Real.log (↑P * ↑P))
        + (16 * (↑P * ↑P) + 4 * ↑Q) * (2 + Real.log (2 * ↑Q))) := by
    apply mul_nonneg hlogPP
    apply add_nonneg (mul_nonneg (by positivity) (by linarith))
      (mul_nonneg (by positivity) (by linarith))
  have hb3 : (0 : ℝ) ≤ (↑P : ℝ) * Real.log ↑P := mul_nonneg (by positivity) hlogP
  have hb4 : (0 : ℝ) ≤ Real.log ↑N *
      (4 * Real.sqrt 10 * ↑N / Real.sqrt (↑P + 1)
        + Real.sqrt 32 * ↑N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt ↑P
        + 64 * ↑N * Real.sqrt (1 + Real.log (2 * ↑Q)) / Real.sqrt ↑P
        + 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (↑N * ↑Q * (1 + Real.log (2 * ↑Q)))) := by
    apply mul_nonneg hlogN
    positivity
  linarith [hb1, hb2, hb3, hb4]

/-- **D5 minor L⁴ explicit bound** (combining the banked pieces): with `U=V=P`, `P≥2`,
    `P³≤N`, `P≤Q`, `P·Q≤N`, the minor L⁴ integral is `≤ (300·N·(log N+2)³/√P + log N)²·N·(log N)²`.
    Feeds the minor-arc smallness once `P = (log N)^B`. -/
lemma minor_L4_le_explicit (N P Q : ℕ) (hP2 : 2 ≤ P) (hPN : P ^ 3 ≤ N) (hPQcut : P ≤ Q)
    (hPQ : P * Q ≤ N) (hN1 : 1 ≤ N) (hQ1 : 1 ≤ Q) :
    ∫ α in (Set.Ioc (0 : ℝ) 1 \ MajorArcs P Q),
        ‖(∑ n ∈ Finset.range N, ((Λ n : ℝ) : ℂ) * e ((n : ℝ) * α)) ^ 2‖ ^ 2
      ≤ (300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P + Real.log N) ^ 2
          * ((N : ℝ) * Real.log N ^ 2) := by
  have hP1 : 1 ≤ P := by omega
  have hPleN : P ≤ N := le_trans (Nat.le_self_pow (by norm_num) P) hPN
  have hPP : P * P ≤ N :=
    le_trans (by rw [← pow_two]; exact Nat.pow_le_pow_right hP1 (by norm_num)) hPN
  have hL4 := minor_L4_range N P Q P P hP1 hPQcut hN1 hP1 hP1 hPleN hPP
  have hcsup := minorCsup_bound N P Q hP2 hPN hPQ
  have hcsup0 := minorCsup_nonneg N P Q hP2 hN1 hQ1
  have hsumL := sum_vonMangoldt_sq_range_le N
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hsq0 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, Λ n ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine le_trans hL4 ?_
  apply mul_le_mul _ hsumL hsq0 (by positivity)
  apply pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- **Brick (a): minor-arc smallness limit.** With `P = ⌊(log N)^9⌋₊`, twice the explicit
    minor-L⁴ bound `2·(300 N (logN+2)³/√P + logN)²·N (logN)²` is `≤ ε N³` for all large `N`.
    Route (rpow-free): split into `46080000 N³/L + 4 N L⁴` (L = log N); the first `≤ εN³/2`
    once `L ≥ 92160000/ε`, the second `≤ εN³/2` once `N ≥ 32768/ε` (via `L⁴ ≤ 4096√N ≤ 4096N`,
    the nested-`√` log bound `log N ≤ 8·√√√N`). Feeds the variance assembly's minor term. -/
lemma minor_limit (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 * (300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt (Nat.floor ((Real.log N) ^ 9)) + Real.log N) ^ 2
          * ((N : ℝ) * Real.log N ^ 2) ≤ ε * (N : ℝ) ^ 3 := by
  refine ⟨max 8 (max (Nat.ceil (Real.exp (92160000 / ε))) (Nat.ceil (32768 / ε))), fun N hN => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hNexp : Real.exp (92160000 / ε) ≤ N :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hN32 : (32768 / ε) ≤ N :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hNR : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set L : ℝ := Real.log N with hLdef
  have hL2 : (2 : ℝ) ≤ L := by
    rw [hLdef]
    calc (2 : ℝ) ≤ Real.log 8 := by
          rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
          have h2 : (0.6931 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
          push_cast; linarith
      _ ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hLpos : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hLA0 : (0 : ℝ) ≤ L := le_of_lt hLpos
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hL9pos : (0 : ℝ) < L ^ 9 := by positivity
  have hL9ge2 : (2 : ℝ) ≤ L ^ 9 := by
    have hLL9 : L ≤ L ^ 9 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 9 := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ L) (by norm_num)
    linarith
  have hPR : (L ^ 9 / 2) ≤ (P : ℝ) := by
    have h := Nat.sub_one_lt_floor (L ^ 9)
    rw [← hPdef] at h
    have h2 : L ^ 9 - 1 ≤ (P : ℝ) := le_of_lt h
    linarith
  have hPpos : (0 : ℝ) < (P : ℝ) := by
    have : (0:ℝ) < L ^ 9 / 2 := by positivity
    linarith
  set sP : ℝ := Real.sqrt (P : ℝ) with hsPdef
  have hsPpos : (0 : ℝ) < sP := Real.sqrt_pos.mpr hPpos
  have hsPsq : sP ^ 2 = (P : ℝ) := Real.sq_sqrt (le_of_lt hPpos)
  set A : ℝ := 300 * (N : ℝ) * (L + 2) ^ 3 with hAdef
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hL2p0 : (0:ℝ) ≤ L + 2 := by linarith
  have hL2p : (L + 2) ≤ 2 * L := by linarith
  have hL26 : (L + 2) ^ 6 ≤ 64 * L ^ 6 := by
    calc (L + 2) ^ 6 ≤ (2 * L) ^ 6 := pow_le_pow_left₀ hL2p0 hL2p 6
      _ = 64 * L ^ 6 := by ring
  have hA2val : A ^ 2 = 90000 * (N:ℝ) ^ 2 * (L + 2) ^ 6 := by rw [hAdef]; ring
  have hAsP : (A / sP) ^ 2 = A ^ 2 / (P : ℝ) := by rw [div_pow, hsPsq]
  have hTsq : (A / sP + L) ^ 2 ≤ 2 * (A ^ 2 / (P : ℝ)) + 2 * L ^ 2 := by
    nlinarith [sq_nonneg (A / sP - L), hAsP]
  have hL3pos : (0:ℝ) < L ^ 3 := by positivity
  have hfirst : 2 * (A ^ 2 / (P : ℝ)) ≤ 23040000 * (N:ℝ)^2 / L ^ 3 := by
    rw [show 2 * (A^2/(P:ℝ)) = 2*A^2/(P:ℝ) from by ring, div_le_div_iff₀ hPpos hL3pos, hA2val]
    nlinarith [mul_nonneg (sq_nonneg (N:ℝ)) (show (0:ℝ) ≤ (P:ℝ) - L^9/2 from by linarith [hPR]),
               mul_nonneg (mul_nonneg (sq_nonneg (N:ℝ)) (pow_pos hLpos 3).le)
                          (show (0:ℝ) ≤ 64*L^6 - (L+2)^6 from by linarith [hL26])]
  have hTsq2 : (A / sP + L) ^ 2 ≤ 23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2 := by
    linarith [hTsq, hfirst]
  have hmain : 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
      ≤ 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := by
    have hfac : 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
        ≤ 2 * (23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2) * ((N:ℝ) * L ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left hTsq2 (by norm_num)
    have hexp : 2 * (23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2) * ((N:ℝ) * L ^ 2)
        = 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := by
      field_simp
      ring
    linarith [hfac, hexp.le, hexp.ge]
  have hpart1 : 46080000 * (N:ℝ)^3 / L ≤ ε / 2 * (N:ℝ)^3 := by
    rw [div_le_iff₀ hLpos]
    have hLbig : 92160000 / ε ≤ L := by
      rw [hLdef]
      calc 92160000 / ε ≤ Real.log (Real.exp (92160000 / ε)) := by rw [Real.log_exp]
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) hNexp
    rw [div_le_iff₀ hε] at hLbig
    have hεL : (92160000 : ℝ) ≤ ε * L := by linarith [hLbig]
    nlinarith [mul_nonneg (pow_pos hNpos 3).le (show (0:ℝ) ≤ ε*L - 92160000 from by linarith [hεL])]
  have hpart2 : 4 * (N:ℝ) * L ^ 4 ≤ ε / 2 * (N:ℝ)^3 := by
    set s : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))) with hsdef
    have hLs : L ≤ 8 * s := by
      rw [hLdef, hsdef]
      have e1 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ)))) = Real.log N / 8 := by
        rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _),
            Real.log_sqrt (le_of_lt hNpos)]; ring
      have h4 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))
          ≤ Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [e1] at h4
      linarith [h4, Real.sqrt_nonneg (Real.sqrt (Real.sqrt (N:ℝ)))]
    have hL4 : L ^ 4 ≤ 4096 * (N:ℝ) := by
      have hs4 : s ^ 4 = Real.sqrt (N:ℝ) := by
        rw [hsdef, show (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))^4
              = ((Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))^2)^2 by ring,
            Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _)]
      have hLpow : L ^ 4 ≤ (8 * s) ^ 4 := pow_le_pow_left₀ hLA0 hLs 4
      have hsqrtN : Real.sqrt (N:ℝ) ≤ (N:ℝ) := by
        have hle : Real.sqrt (N:ℝ) ≤ Real.sqrt ((N:ℝ)^2) := Real.sqrt_le_sqrt (by nlinarith [hNR])
        rwa [Real.sqrt_sq (le_of_lt hNpos)] at hle
      calc L ^ 4 ≤ (8 * s) ^ 4 := hLpow
        _ = 4096 * s ^ 4 := by ring
        _ = 4096 * Real.sqrt (N:ℝ) := by rw [hs4]
        _ ≤ 4096 * (N:ℝ) := by linarith [hsqrtN]
    have hεN : (32768 : ℝ) ≤ ε * N := by
      rw [div_le_iff₀ hε] at hN32; linarith [hN32]
    nlinarith [mul_nonneg hNpos.le (show (0:ℝ) ≤ 4096*(N:ℝ) - L^4 from by linarith [hL4]),
               mul_nonneg (sq_nonneg (N:ℝ)) (show (0:ℝ) ≤ ε*(N:ℝ)/2 - 16384 from by linarith [hεN])]
  calc 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
      ≤ 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := hmain
    _ ≤ ε / 2 * (N:ℝ)^3 + ε / 2 * (N:ℝ)^3 := by linarith [hpart1, hpart2]
    _ = ε * (N:ℝ)^3 := by ring

/-- **Farey windows are disjoint**: distinct reduced anchors with moduli `≤ P` have
    disjoint windows once `2P² < Q+1` — the input for splitting the major-arc integral
    into per-window integrals. -/
lemma farey_disjoint (P Q : ℕ) (hPQ : 2 * P ^ 2 < Q + 1) (a a' : ℤ) (q q' : ℕ)
    (hq : 0 < q) (hq' : 0 < q') (hqP : q ≤ P) (hq'P : q' ≤ P)
    (hga : Int.gcd a q = 1) (hga' : Int.gcd a' q' = 1)
    (hne : ¬ (a = a' ∧ q = q')) :
    Disjoint (Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1))))
      (Metric.closedBall ((a' : ℝ) / q') (1 / (q' * (Q + 1)))) := by
  have hP0 : 0 < P := lt_of_lt_of_le hq hqP
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hq'R : (0:ℝ) < q' := by exact_mod_cast hq'
  have hQ1 : (0:ℝ) < (Q:ℝ) + 1 := by positivity
  -- the anchors are distinct rationals: |aq' − a'q| ≥ 1
  have hnum : a * (q' : ℤ) ≠ a' * (q : ℤ) := by
    intro hc
    apply hne
    have hdvd1 : (q : ℤ) ∣ (q' : ℤ) := by
      have h1 : (q : ℤ) ∣ a * q' := ⟨a', by linarith [hc]⟩
      have hco : IsCoprime (q : ℤ) a := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        exact hga
      exact hco.dvd_of_dvd_mul_left h1
    have hdvd2 : (q' : ℤ) ∣ (q : ℤ) := by
      have h1 : (q' : ℤ) ∣ a' * q := ⟨a, by linarith [hc]⟩
      have hco : IsCoprime (q' : ℤ) a' := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        exact hga'
      exact hco.dvd_of_dvd_mul_left h1
    have hqq : (q : ℤ) = q' := Int.dvd_antisymm (by exact_mod_cast Int.natCast_nonneg q)
      (by exact_mod_cast Int.natCast_nonneg q') hdvd1 hdvd2
    have hqq' : q = q' := by exact_mod_cast hqq
    refine ⟨?_, hqq'⟩
    subst hqq'
    have := mul_right_cancel₀ (show (q:ℤ) ≠ 0 by exact_mod_cast hq.ne') hc
    exact this
  have hdist : 1 / ((q:ℝ) * q') ≤ dist ((a : ℝ) / q) ((a' : ℝ) / q') := by
    rw [Real.dist_eq]
    have hval : (a : ℝ) / q - (a' : ℝ) / q' = ((a * q' - a' * q : ℤ) : ℝ) / ((q:ℝ) * q') := by
      push_cast
      field_simp
    rw [hval, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q:ℝ) * q')]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : (1 : ℤ) ≤ |a * q' - a' * q| :=
      Int.one_le_abs (sub_ne_zero_of_ne hnum)
    exact_mod_cast (by exact_mod_cast h1 : (1:ℝ) ≤ |((a * q' - a' * q : ℤ) : ℝ)|)
  apply Metric.closedBall_disjoint_closedBall
  calc 1 / ((q:ℝ) * (Q + 1)) + 1 / ((q':ℝ) * (Q + 1))
      ≤ 1 / ((Q:ℝ) + 1) + 1 / ((Q:ℝ) + 1) := by
        have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
        have hq'1 : (1:ℝ) ≤ (q':ℝ) := by exact_mod_cast hq'
        apply add_le_add
        · apply one_div_le_one_div_of_le hQ1
          nlinarith [hq1, hQ1]
        · apply one_div_le_one_div_of_le hQ1
          nlinarith [hq'1, hQ1]
    _ = 2 / ((Q:ℝ) + 1) := by ring
    _ < 1 / ((P:ℝ) ^ 2) := by
        rw [div_lt_div_iff₀ hQ1 (by positivity)]
        have : (2 * P ^ 2 : ℝ) < (Q:ℝ) + 1 := by exact_mod_cast hPQ
        nlinarith [this]
    _ ≤ 1 / ((q:ℝ) * q') := by
        apply one_div_le_one_div_of_le (by positivity)
        have h1 : (q:ℝ) ≤ P := by exact_mod_cast hqP
        have h2 : (q':ℝ) ≤ P := by exact_mod_cast hq'P
        nlinarith [hqR, hq'R]
    _ ≤ dist ((a : ℝ) / q) ((a' : ℝ) / q') := hdist


/-- **Finite anchor localization**: inside `(0,1]` only anchors with `−q ≤ a ≤ 2q`
    can contribute to the major arcs — the ℤ-union collapses to a finite one, enabling
    the per-window splitting of the major-arc integral. -/
lemma majorArcs_inter_Ioc_subset (P Q : ℕ) (hP : 0 < P) :
    MajorArcs P Q ∩ Set.Ioc (0:ℝ) 1
      ⊆ ⋃ q ∈ Set.Icc 1 P, ⋃ a ∈ Set.Icc (-(q:ℤ)) (2 * q),
          Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1))) := by
  rintro x ⟨hx, hx01⟩
  rw [MajorArcs, Set.mem_iUnion₂] at hx
  obtain ⟨q, hq, hxq⟩ := hx
  rw [Set.mem_iUnion] at hxq
  obtain ⟨a, ha⟩ := hxq
  rw [Metric.mem_closedBall, Real.dist_eq] at ha
  obtain ⟨hq1, hqP⟩ := hq
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hQR : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hrad : 1 / ((q:ℝ) * (Q + 1)) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hx0 : (0:ℝ) < x := hx01.1
  have hx1 : x ≤ 1 := hx01.2
  have hlow : -1 ≤ (a : ℝ) / q := by
    have : (a:ℝ)/q ≥ x - 1/((q:ℝ)*(Q+1)) := by
      have := abs_le.mp ha
      linarith [this.2]
    linarith
  have hhigh : (a : ℝ) / q ≤ 2 := by
    have : (a:ℝ)/q ≤ x + 1/((q:ℝ)*(Q+1)) := by
      have := abs_le.mp ha
      linarith [this.1]
    linarith
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have haZ : -(q:ℤ) ≤ a ∧ a ≤ 2 * q := by
    constructor
    · have : -(q:ℝ) ≤ (a:ℝ) := by
        have := mul_le_mul_of_nonneg_right hlow hqpos.le
        rw [div_mul_cancel₀ _ hqpos.ne'] at this
        linarith
      exact_mod_cast this
    · have : (a:ℝ) ≤ 2 * q := by
        have := mul_le_mul_of_nonneg_right hhigh hqpos.le
        rw [div_mul_cancel₀ _ hqpos.ne'] at this
        linarith
      exact_mod_cast this
  rw [Set.mem_iUnion₂]
  refine ⟨q, ⟨hq1, hqP⟩, ?_⟩
  rw [Set.mem_iUnion₂]
  refine ⟨a, ⟨haZ.1, haZ.2⟩, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  exact ha



/-- **Reduced coverage**: inside `(0,1]` the major arcs are covered by the windows of the
    finitely many REDUCED anchors — an unreduced `a/q` equals a reduced `a'/q'` with
    `q' ∣ q`, whose window is wider. The composition splits over `anchors P` with
    `farey_disjoint` and evaluates each window by `vonMangoldt_window_eval`. -/
lemma majorArcs_subset_reduced (P Q : ℕ) (hP : 0 < P) :
    MajorArcs P Q ∩ Set.Ioc (0:ℝ) 1
      ⊆ ⋃ pq ∈ anchors P,
          Metric.closedBall (((pq.2 : ℤ) : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1))) := by
  rintro x ⟨hx, hx01⟩
  rw [MajorArcs, Set.mem_iUnion₂] at hx
  obtain ⟨q, ⟨hq1, hqP⟩, hxq⟩ := hx
  rw [Set.mem_iUnion] at hxq
  obtain ⟨a, ha⟩ := hxq
  rw [Metric.mem_closedBall, Real.dist_eq] at ha
  -- bounds on a as before
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hQR : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hrad : 1 / ((q:ℝ) * (Q + 1)) ≤ 1 := by
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hx0 : (0:ℝ) < x := hx01.1
  have hx1 : x ≤ 1 := hx01.2
  have habs := abs_le.mp ha
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hlow : -(q:ℝ) ≤ (a:ℝ) := by
    have h1 : -1 ≤ (a:ℝ)/q := by
      have : (a:ℝ)/q ≥ x - 1/((q:ℝ)*(Q+1)) := by linarith [habs.2]
      linarith
    have := mul_le_mul_of_nonneg_right h1 hqpos.le
    rw [div_mul_cancel₀ _ hqpos.ne'] at this
    linarith
  have hhigh : (a:ℝ) ≤ 2*q := by
    have h1 : (a:ℝ)/q ≤ 2 := by
      have : (a:ℝ)/q ≤ x + 1/((q:ℝ)*(Q+1)) := by linarith [habs.1]
      linarith
    have := mul_le_mul_of_nonneg_right h1 hqpos.le
    rw [div_mul_cancel₀ _ hqpos.ne'] at this
    linarith
  -- reduce the fraction
  set g : ℕ := Int.gcd a q with hg
  have hg0 : 0 < g := by
    rw [hg]
    apply Int.gcd_pos_of_ne_zero_right
    exact_mod_cast hq1.trans_lt' Nat.zero_lt_one |>.ne'
  set a' : ℤ := a / g with ha'
  set q' : ℕ := q / g with hq'
  have hgdvd_a : (g : ℤ) ∣ a := by
    rw [hg]
    exact Int.gcd_dvd_left a (q:ℤ)
  have hgdvd_q : g ∣ q := by
    have h := Int.gcd_dvd_right a (q:ℤ)
    rw [← hg] at h
    exact_mod_cast h
  have hq'pos : 0 < q' := Nat.div_pos (Nat.le_of_dvd (by omega) hgdvd_q) hg0
  have hq'le : q' ≤ q := Nat.div_le_self q g
  have haeq : a = g * a' := (Int.mul_ediv_cancel' hgdvd_a).symm
  have hqeq : q = g * q' := (Nat.mul_div_cancel' hgdvd_q).symm
  have hgcd' : Int.gcd a' q' = 1 := by
    rw [ha', hq']
    have h := Int.gcd_div_gcd_div_gcd (i := a) (j := (q:ℤ)) (by
      rw [← hg]
      exact_mod_cast hg0)
    rw [← hg] at h
    convert h using 2
    push_cast
    rfl
  -- same center
  have hcenter : ((a : ℝ)) / q = ((a' : ℝ)) / q' := by
    rw [haeq, hqeq]
    push_cast
    rw [mul_comm ((g:ℝ)) ((a':ℝ)), mul_comm ((g:ℝ)) ((q':ℝ))]
    rw [mul_div_mul_right _ _ (by exact_mod_cast hg0.ne' : ((g:ℝ)) ≠ 0)]
  -- wider radius
  have hradle : 1 / ((q:ℝ) * (Q + 1)) ≤ 1 / ((q':ℝ) * (Q + 1)) := by
    apply one_div_le_one_div_of_le
    · have : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'pos
      nlinarith
    · have h1 : ((q':ℕ):ℝ) ≤ ((q:ℕ):ℝ) := by exact_mod_cast hq'le
      nlinarith
  -- a' bounds
  have hgRpos : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg0
  have ha'low : -(q' : ℤ) ≤ a' := by
    have hR : -((q':ℕ):ℝ) ≤ ((a':ℤ):ℝ) := by
      have h1 : -((q:ℝ)) ≤ (((g:ℤ) * a' : ℤ):ℝ) := by
        rw [← haeq]
        exact hlow
      push_cast at h1
      have h2 : (q:ℝ) = (g:ℝ) * ((q':ℕ):ℝ) := by exact_mod_cast hqeq
      nlinarith
    exact_mod_cast hR
  have ha'high : a' ≤ 2 * q' := by
    have hR : ((a':ℤ):ℝ) ≤ 2 * ((q':ℕ):ℝ) := by
      have h1 : (((g:ℤ) * a' : ℤ):ℝ) ≤ 2 * (q:ℝ) := by
        rw [← haeq]
        exact hhigh
      push_cast at h1
      have h2 : (q:ℝ) = (g:ℝ) * ((q':ℕ):ℝ) := by exact_mod_cast hqeq
      nlinarith
    exact_mod_cast hR
  -- conclude
  rw [Set.mem_iUnion₂]
  refine ⟨(q', a'), ?_, ?_⟩
  · rw [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hq'pos, le_trans hq'le hqP⟩, ?_, ?_⟩, hgcd'⟩
    · calc -(P:ℤ) ≤ -(q':ℤ) := by
            have : (q':ℤ) ≤ P := by exact_mod_cast le_trans hq'le hqP
            omega
        _ ≤ a' := ha'low
    · calc a' ≤ 2 * q' := ha'high
        _ ≤ 2 * P := by
            have : (q':ℤ) ≤ P := by exact_mod_cast le_trans hq'le hqP
            omega
  · rw [Metric.mem_closedBall, Real.dist_eq]
    calc |x - ((a':ℤ):ℝ) / (q':ℕ)| = |x - (a:ℝ)/q| := by rw [hcenter]
      _ ≤ 1 / ((q:ℝ) * (Q + 1)) := ha
      _ ≤ 1 / ((q':ℝ) * (Q + 1)) := hradle

end ArcDecomposition

end MinorArc

open MinorArc

set_option maxHeartbeats 1000000
open scoped ArithmeticFunction



/-- Each anchor window sits inside the major arcs (anchor `q ≤ P`). -/
lemma anchors_subset_majorArcs (P Q : ℕ) :
    (⋃ pq ∈ anchors P,
        Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1))))
      ⊆ MajorArcs P Q := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨pq, hpq, hxmem⟩ := hx
  simp only [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq
  obtain ⟨⟨⟨hq1, hqP⟩, _⟩, _⟩ := hpq
  rw [MajorArcs]
  refine Set.mem_iUnion₂.mpr ⟨pq.1, ⟨hq1, hqP⟩, ?_⟩
  exact Set.mem_iUnion.mpr ⟨pq.2, hxmem⟩

/-- **Major-arc set gluing**: within `(0,1]` the major arcs equal the reduced-anchor
    windows — so `variance_le_bessel`'s major integral (`Ioc \ minor`) is literally
    `major_bessel_error_q`'s anchor-union integral. -/
lemma majorArcs_inter_eq_anchors (P Q : ℕ) (hP : 0 < P) :
    MajorArcs P Q ∩ Set.Ioc (0:ℝ) 1
      = (⋃ pq ∈ anchors P,
          Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1))))
        ∩ Set.Ioc (0:ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨majorArcs_subset_reduced P Q hP hx, hx.2⟩
  · intro x hx
    exact ⟨anchors_subset_majorArcs P Q hx.1, hx.2⟩

/-- **exp beats any power of log** (the analytic core of the major-arc smallness limit):
    for any `c>0`, `k`, `δ>0`, eventually `(log N)^k · exp(-c·(log N)^{1/10}) ≤ δ`.
    Route: with `L = (log N)^{1/10}` (so `log N = L^10`), show `L ≤ exp(sL)`
    (`s = c/(20k+20)`, via `add_one_le_exp` squared), raise to `10k` to get
    `L^{10k} ≤ exp((c/2)L)`, then `exp((c/2)L)·exp(-cL) = exp(-(c/2)L) ≤ δ`. -/
lemma exp_dominates_polylog (c : ℝ) (hc : 0 < c) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (Real.log N) ^ k * Real.exp (-c * (Real.log N) ^ ((1:ℝ)/10)) ≤ δ := by
  set s : ℝ := c / (20 * k + 20) with hsdef
  have hs : 0 < s := by rw [hsdef]; positivity
  have hs2 : 0 < s ^ 2 := by positivity
  have hcne : c ≠ 0 := ne_of_gt hc
  have h10ks : (10 * (k:ℝ)) * s ≤ c / 2 := by
    have hden : (0:ℝ) < 20 * (k:ℝ) + 20 := by positivity
    have key : (10 * (k:ℝ)) * s = (10 * (k:ℝ) * c) / (20 * (k:ℝ) + 20) := by rw [hsdef]; ring
    rw [key, div_le_iff₀ hden]
    have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
    nlinarith [hc, hk0, mul_nonneg hk0 hc.le]
  set D : ℝ := 4 / s ^ 2 + (2 / c) * |Real.log δ| + 1 with hDdef
  have hD4 : 4 / s ^ 2 ≤ D := by
    rw [hDdef]; linarith [mul_nonneg (show (0:ℝ) ≤ 2 / c by positivity) (abs_nonneg (Real.log δ))]
  have hDlog : (2 / c) * |Real.log δ| ≤ D := by
    rw [hDdef]; linarith [show (0:ℝ) ≤ 4 / s ^ 2 by positivity]
  have hD0 : 0 < D := by rw [hDdef]; positivity
  refine ⟨Nat.ceil (Real.exp (D ^ 10)) + 1, fun N hN => ?_⟩
  have hNexp : Real.exp (D ^ 10) ≤ (N:ℝ) := by
    have h1 : (⌈Real.exp (D ^ 10)⌉₊ : ℝ) ≤ (N:ℝ) := by
      have : ⌈Real.exp (D ^ 10)⌉₊ ≤ N := by omega
      exact_mod_cast this
    linarith [Nat.le_ceil (Real.exp (D ^ 10))]
  have hexp1 : (1:ℝ) ≤ Real.exp (D ^ 10) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := le_trans hexp1 hNexp
  have hlogN0 : (0:ℝ) ≤ Real.log N := Real.log_nonneg hN1
  have hlogND : D ^ 10 ≤ Real.log N := by
    calc D ^ 10 = Real.log (Real.exp (D ^ 10)) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) hNexp
  have hlogNpos : (0:ℝ) < Real.log N := lt_of_lt_of_le (by positivity) hlogND
  set L : ℝ := Real.log N ^ ((1:ℝ)/10) with hLdef
  have hL0 : 0 < L := by rw [hLdef]; exact Real.rpow_pos_of_pos hlogNpos _
  have hLpow : L ^ (10 * k) = (Real.log N) ^ k := by
    rw [hLdef, ← Real.rpow_natCast (Real.log N ^ ((1:ℝ)/10)) (10 * k),
        ← Real.rpow_mul hlogN0, ← Real.rpow_natCast (Real.log N) k]
    congr 1; push_cast; ring
  have hLD : D ≤ L := by
    rw [hLdef]
    have hDrw : D = (D ^ 10 : ℝ) ^ ((1:ℝ)/10) := by
      rw [← Real.rpow_natCast D 10, ← Real.rpow_mul hD0.le]; norm_num
    rw [hDrw]
    exact Real.rpow_le_rpow (by positivity) hlogND (by norm_num)
  have hLexp : L ≤ Real.exp (s * L) := by
    have hq := Real.add_one_le_exp (s * L / 2)
    have hsq : Real.exp (s * L) = Real.exp (s * L / 2) * Real.exp (s * L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpos : (0:ℝ) ≤ s * L / 2 + 1 := by positivity
    have hquad : (s * L / 2 + 1) ^ 2 ≤ Real.exp (s * L) := by
      rw [hsq]; nlinarith [mul_le_mul hq hq hpos (Real.exp_pos (s * L / 2)).le]
    have hge : 4 / s ^ 2 ≤ L := le_trans hD4 hLD
    have hs2L : (4:ℝ) ≤ L * s ^ 2 := (div_le_iff₀ hs2).mp hge
    have hLs2 : L ≤ s ^ 2 * L ^ 2 / 4 := by nlinarith [hs2L, hL0]
    nlinarith [hquad, hLs2, mul_nonneg hs.le hL0.le]
  have hLk : L ^ (10 * k) ≤ Real.exp ((10 * (k:ℝ)) * s * L) := by
    calc L ^ (10 * k) ≤ (Real.exp (s * L)) ^ (10 * k) := pow_le_pow_left₀ hL0.le hLexp (10 * k)
      _ = Real.exp ((10 * (k:ℝ)) * (s * L)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ = Real.exp ((10 * (k:ℝ)) * s * L) := by congr 1; ring
  have hexp_neg : Real.exp ((10 * (k:ℝ)) * s * L) * Real.exp (-c * L) ≤ Real.exp (-(c/2) * L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [h10ks, hL0.le]
  have hfin : Real.exp (-(c/2) * L) ≤ δ := by
    rw [← Real.le_log_iff_exp_le hδ]
    have h1 : -(c/2) * L ≤ -(c/2) * D := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ c/2 by positivity) (show (0:ℝ) ≤ L - D by linarith [hLD])]
    have hcancel : |Real.log δ| ≤ (c/2) * D := by
      calc |Real.log δ| = (c/2) * ((2/c) * |Real.log δ|) := by field_simp
        _ ≤ (c/2) * D := mul_le_mul_of_nonneg_left hDlog (by positivity)
    have h2 : -(c/2) * D ≤ Real.log δ := by
      have hneg : -|Real.log δ| ≤ Real.log δ := neg_abs_le _
      linarith [hcancel, hneg]
    linarith
  calc (Real.log N) ^ k * Real.exp (-c * L)
      = L ^ (10 * k) * Real.exp (-c * L) := by rw [hLpow]
    _ ≤ Real.exp ((10 * (k:ℝ)) * s * L) * Real.exp (-c * L) :=
        mul_le_mul_of_nonneg_right hLk (Real.exp_pos _).le
    _ ≤ Real.exp (-(c/2) * L) := hexp_neg
    _ ≤ δ := hfin

section CrossFileInputsMinor



end CrossFileInputsMinor

-- ===== Phase D brick (c): core_variance =====

/-- **Any power of log is eventually beaten by N**: for `K>0`, `k`, eventually
    `K·(log N)^k ≤ N`. (The nat/log bookkeeping for `P = ⌊(log N)^9⌋₊`: gives
    `P³ ≤ N`, `2P³ ≤ N`, etc.) Route: `u = log N`, `N = exp u`; `u ≤ exp(su)`
    (`s=1/(2k+2)`) ⟹ `u^k ≤ exp(u/2)` ⟹ `K u^k ≤ K exp(u/2) ≤ exp u = N`. -/
lemma polylog_le_self (k : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K * (Real.log N) ^ k ≤ (N : ℝ) := by
  set s : ℝ := 1 / (2 * k + 2) with hsdef
  have hs : 0 < s := by rw [hsdef]; positivity
  have hs2 : 0 < s ^ 2 := by positivity
  have hks : (k:ℝ) * s ≤ 1 / 2 := by
    rw [hsdef]
    rw [show (k:ℝ) * (1 / (2 * k + 2)) = (k:ℝ) / (2 * k + 2) from by ring,
        div_le_div_iff₀ (by positivity) (by norm_num)]
    have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
    nlinarith [hk0]
  set D : ℝ := 4 / s ^ 2 + 2 * |Real.log K| + 1 with hDdef
  have hD4 : 4 / s ^ 2 ≤ D := by
    rw [hDdef]; linarith [abs_nonneg (Real.log K)]
  have hDK : 2 * |Real.log K| ≤ D := by
    rw [hDdef]; linarith [show (0:ℝ) ≤ 4 / s ^ 2 by positivity]
  have hD0 : 0 < D := by rw [hDdef]; positivity
  refine ⟨Nat.ceil (Real.exp D) + 1, fun N hN => ?_⟩
  have hNexp : Real.exp D ≤ (N:ℝ) := by
    have h1 : (⌈Real.exp D⌉₊ : ℝ) ≤ (N:ℝ) := by
      have : ⌈Real.exp D⌉₊ ≤ N := by omega
      exact_mod_cast this
    linarith [Nat.le_ceil (Real.exp D)]
  have hexp1 : (1:ℝ) ≤ Real.exp D := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := le_trans hexp1 hNexp
  have hlogND : D ≤ Real.log N := by
    calc D = Real.log (Real.exp D) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) hNexp
  set u : ℝ := Real.log N with hudef
  have hu0 : 0 < u := lt_of_lt_of_le hD0 hlogND
  have huD : D ≤ u := hlogND
  have hNeq : (N:ℝ) = Real.exp u := (Real.exp_log (by linarith)).symm
  -- u ≤ exp(su)
  have hLexp : u ≤ Real.exp (s * u) := by
    have hq := Real.add_one_le_exp (s * u / 2)
    have hsq : Real.exp (s * u) = Real.exp (s * u / 2) * Real.exp (s * u / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpos : (0:ℝ) ≤ s * u / 2 + 1 := by positivity
    have hquad : (s * u / 2 + 1) ^ 2 ≤ Real.exp (s * u) := by
      rw [hsq]; nlinarith [mul_le_mul hq hq hpos (Real.exp_pos (s * u / 2)).le]
    have hge : 4 / s ^ 2 ≤ u := le_trans hD4 huD
    have hs2u : (4:ℝ) ≤ u * s ^ 2 := (div_le_iff₀ hs2).mp hge
    have hus2 : u ≤ s ^ 2 * u ^ 2 / 4 := by nlinarith [hs2u, hu0]
    nlinarith [hquad, hus2, mul_nonneg hs.le hu0.le]
  -- u^k ≤ exp(u/2)
  have huk : u ^ k ≤ Real.exp (u / 2) := by
    calc u ^ k ≤ (Real.exp (s * u)) ^ k := pow_le_pow_left₀ hu0.le hLexp k
      _ = Real.exp ((k:ℝ) * (s * u)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (u / 2) := by
          apply Real.exp_le_exp.mpr; nlinarith [hks, hu0.le]
  -- K ≤ exp(u/2)
  have hKexp : K ≤ Real.exp (u / 2) := by
    rw [← Real.log_le_iff_le_exp hK]
    have hneg : Real.log K ≤ |Real.log K| := le_abs_self _
    linarith [hDK, huD, hneg]
  -- assemble: K u^k ≤ exp(u/2)*exp(u/2) = exp(u) = N
  calc K * u ^ k ≤ Real.exp (u / 2) * Real.exp (u / 2) :=
        mul_le_mul hKexp huk (by positivity) (Real.exp_pos _).le
    _ = Real.exp u := by rw [← Real.exp_add]; congr 1; ring
    _ = (N:ℝ) := hNeq.symm


namespace MajorArcMainTerm

/-- `d/dx e(c·x) = 2πi·c·e(c·x)`. -/
lemma hasDerivAt_e (c x : ℝ) :
    HasDerivAt (fun t : ℝ => e (c * t)) (2 * Real.pi * Complex.I * c * e (c * x)) x := by
  have hr : HasDerivAt (fun t : ℝ => c * t) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have h2 := (hr.ofReal_comp.const_mul (2 * Real.pi * Complex.I : ℂ)).cexp
  have hfe : (fun t : ℝ => e (c * t))
      = (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ((c * t : ℝ) : ℂ))) := by
    funext t; simp only [e]
  rw [hfe]
  have hv : 2 * Real.pi * Complex.I * c * e (c * x)
      = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ((c * x : ℝ) : ℂ))
        * (2 * Real.pi * Complex.I * (c : ℂ)) := by
    simp only [e]; push_cast; ring
  rw [hv]; exact h2

/-- **Character orthogonality**: `∫₀¹ e(m·x) dx = 1` if `m = 0`, else `0`, for `m : ℤ`. The
    backbone of the full-period Dirichlet-kernel value and the major-arc extraction. -/
lemma integral_e_int (m : ℤ) :
    (∫ x in (0:ℝ)..1, e ((m : ℝ) * x)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp only [Int.cast_zero, zero_mul, if_pos rfl, e]
    simp
  · rw [if_neg hm]
    have hc : (2 * Real.pi * Complex.I * (m : ℝ)) ≠ 0 := by
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      have hmr : ((m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by exact_mod_cast hm : (m : ℝ) ≠ 0)
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨⟨by norm_num, by exact_mod_cast hpi⟩, Complex.I_ne_zero⟩, hmr⟩
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun t : ℝ => e ((m : ℝ) * t) / (2 * Real.pi * Complex.I * (m : ℝ)))
          (e ((m : ℝ) * x)) x := by
      intro x _
      have h2 := (hasDerivAt_e (m : ℝ) x).div_const (2 * Real.pi * Complex.I * (m : ℝ))
      have hval : 2 * Real.pi * Complex.I * (m : ℝ) * e ((m : ℝ) * x)
            / (2 * Real.pi * Complex.I * (m : ℝ)) = e ((m : ℝ) * x) := by
        rw [mul_comm (2 * Real.pi * Complex.I * (m : ℝ)) (e ((m : ℝ) * x)),
          mul_div_assoc, div_self hc, mul_one]
      rw [hval] at h2
      exact h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by simp only [e]; fun_prop) 0 1)]
    have he1 : e ((m : ℝ) * 1) = 1 := by
      have harg : (2 * Real.pi * Complex.I : ℂ) * (((m : ℝ) * 1 : ℝ) : ℂ)
          = ((m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      simp only [e]
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I m
    have he0 : e ((m : ℝ) * 0) = 1 := by simp [e]
    rw [he1, he0]; ring


/-- **Full-period Dirichlet-kernel value**: `∫₀¹ (∑_{k<N} e(kβ))² e(−nβ) dβ = r_N(n)`, the
    count `#{(k,k')∈[0,N)²: k+k'=n}`. Termwise orthogonality picks out `k+k'=n`; this is the
    value each major arc localizes. -/
lemma dirichlet_full (N n : ℕ) :
    (∫ β in (0:ℝ)..1, (∑ k ∈ Finset.range N, e ((k:ℝ) * β))^2 * e (-(n:ℝ) * β))
      = (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ) := by
  have key : (fun β : ℝ => (∑ k ∈ Finset.range N, e ((k:ℝ) * β))^2 * e (-(n:ℝ) * β))
      = (fun β : ℝ => ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          e (((((p.1 : ℤ) + (p.2 : ℤ) - (n : ℤ)) : ℤ) : ℝ) * β)) := by
    funext β
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [e_add, e_add]
    congr 1
    push_cast; ring
  rw [key, intervalIntegral.integral_finset_sum
    (fun p _ => Continuous.intervalIntegrable (by simp only [e]; fun_prop) 0 1)]
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.range N ×ˢ Finset.range N) =>
    integral_e_int ((p.1 : ℤ) + (p.2 : ℤ) - (n : ℤ)))]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  congr 1
  refine Finset.filter_congr (fun p _ => ?_)
  constructor <;> intro h <;> omega

/-- **Kernel count**: for `n ≤ X`, the number of ordered pairs `(k,k') ∈ [0,X]²` with
    `k+k'=n` is exactly `n+1` (`k` ranges freely over `0..n`, `k'=n-k` always fits). This is
    `r_{X+1}(n)`, the full-period value `∫₀¹ D_{X+1}(β)² e(−nβ) dβ` of the Dirichlet kernel. -/
lemma kernel_count (X n : ℕ) (hn : n ≤ X) :
    ((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter (fun p => p.1 + p.2 = n)).card
      = n + 1 := by
  rw [← Finset.card_range (n + 1)]
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_range]; omega
  · intro p hp p' hp' heq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp hp'
    have : p.2 = p'.2 := by omega
    exact Prod.ext heq this
  · intro k hk
    rw [Finset.mem_range] at hk
    refine ⟨(k, n - k), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega

/-- **Kernel factor is `≍ X`**: for `n ∈ (X/2, X]`, the (real) kernel count `r_{X+1}(n) = n+1`
    is `≥ X/2`. This is the `r_N(n)` factor of the main term `𝔖_P(n)·r_N(n)`; combined with
    singular-series positivity `𝔖_P(n) ≥ c₀` it gives `hmain`'s lower bound `≥ c₀·X/2`. -/
lemma kernel_real_lb (X n : ℕ) (h1 : X / 2 < n) (h2 : n ≤ X) :
    (X : ℝ) / 2
      ≤ (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
          (fun p => p.1 + p.2 = n)).card : ℝ) := by
  rw [kernel_count X n h2]
  have hXle : X ≤ 2 * n := by omega
  have hXR : (X : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hXle
  push_cast
  linarith

/-- The Ramanujan sum `c_q(n) = ∑_{r<q, gcd(r,q)=1} e(nr/q)` — the arithmetic factor of the
    singular-series local terms `μ(q)²·c_q(n)/φ(q)²`. -/
noncomputable def ramSum (q n : ℕ) : ℂ :=
  ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((n : ℝ) * r / q)

/-- The Ramanujan sum as an explicit **integer**: `c_q(n) = ∑_{d∣q} μ(d)·[ (q/d)∣n ]·(q/d)`.
    Having a ℤ-valued form makes the singular series `𝔖_P(n) = ∑_{q≤P} μ(q)²·c_q(n)/φ(q)²` a
    genuinely real object (no `.re` juggling). -/
def cRam (q n : ℕ) : ℤ :=
  ∑ d ∈ q.divisors, ArithmeticFunction.moebius d * (if q / d ∣ n then ((q / d : ℕ) : ℤ) else 0)

/-- **The Ramanujan sum is real (integer-valued)**: `ramSum q n = (cRam q n : ℂ)`. -/
lemma ramSum_eq_cRam (q n : ℕ) (hq : 0 < q) : ramSum q n = (cRam q n : ℂ) := by
  have h := ramanujan_sum_divisor (n : ℤ) q hq
  rw [ramSum]
  have hlhs : (∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((n : ℝ) * r / q))
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e (((n : ℤ) : ℝ) * r / q) := by
    apply Finset.sum_congr rfl; intro r _; rw [Int.cast_natCast]
  rw [hlhs, h, cRam, Int.cast_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Int.cast_mul, Int.cast_ite, Int.cast_natCast, Int.cast_zero]
  congr 1
  exact if_congr Int.natCast_dvd_natCast rfl rfl

/-- `g_n(m) = [m ∣ n]·m`, a multiplicative arithmetic function; the point is `cRam(·,n) = μ ⋆ g_n`,
    which makes `cRam` multiplicative in `q` for free (Dirichlet-convolution of two multiplicative
    functions). This is the engine of the singular series' Euler product. -/
def gArith (n : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun m => if m ∣ n then (m : ℤ) else 0, by simp⟩

lemma gArith_apply (n m : ℕ) : gArith n m = if m ∣ n then (m : ℤ) else 0 := rfl

/-- `cRam(·,n)` is the Dirichlet convolution `μ ⋆ g_n`. -/
lemma cRam_eq_conv (q n : ℕ) : cRam q n = (ArithmeticFunction.moebius * gArith n) q := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (f := fun d e => (ArithmeticFunction.moebius d) * gArith n e)]
  rw [cRam]
  apply Finset.sum_congr rfl
  intro d _
  rw [gArith_apply]

lemma isMult_gArith (n : ℕ) : (gArith n).IsMultiplicative := by
  refine ⟨by rw [gArith_apply]; simp, ?_⟩
  intro a b hab
  simp only [gArith_apply]
  by_cases ha : a ∣ n <;> by_cases hb : b ∣ n
  · rw [if_pos ha, if_pos hb, if_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hab ha hb)]; push_cast; ring
  · rw [if_pos ha, if_neg hb, if_neg (fun h => hb (dvd_trans (Dvd.intro_left a rfl) h))]; ring
  · rw [if_neg ha, if_pos hb, if_neg (fun h => ha (dvd_trans (Dvd.intro b rfl) h))]; ring
  · rw [if_neg ha, if_neg hb, if_neg (fun h => ha (dvd_trans (Dvd.intro b rfl) h))]; ring

/-- **Ramanujan-sum multiplicativity**: `c_{q₁q₂}(n) = c_{q₁}(n)·c_{q₂}(n)` for coprime `q₁,q₂`.
    Combined with `ramSum_prime` this evaluates `c_q(n)` over the primes and drives the Euler
    product of the singular series. -/
lemma cRam_mul (n q1 q2 : ℕ) (h : Nat.Coprime q1 q2) :
    cRam (q1 * q2) n = cRam q1 n * cRam q2 n := by
  rw [cRam_eq_conv, cRam_eq_conv, cRam_eq_conv]
  exact (ArithmeticFunction.isMultiplicative_moebius.mul (isMult_gArith n)).2 h

/-- **Ramanujan sum at a prime**: `c_p(n) = p−1` if `p ∣ n`, else `−1`. The base case of the
    singular series' Euler product: at `p ∤ n` it is `μ(p) = −1` (via `ramanujan_sum_coprime`,
    since `gcd(n,p)=1`); at `p ∣ n` every `e(nr/p) = 1` so the sum is `φ(p) = p−1`. -/
lemma ramSum_prime (p n : ℕ) (hp : p.Prime) :
    ramSum p n = if p ∣ n then (p - 1 : ℂ) else -1 := by
  by_cases hd : p ∣ n
  · rw [if_pos hd]
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
    obtain ⟨k, hk⟩ := hd
    have hval : ramSum p n
        = ∑ _r ∈ (Finset.range p).filter (fun r => Nat.gcd r p = 1), (1 : ℂ) := by
      rw [ramSum]
      apply Finset.sum_congr rfl
      intro r _
      have hpr : ((n : ℝ) * (r : ℝ) / (p : ℝ)) = ((k * r : ℕ) : ℝ) := by
        rw [hk]; push_cast; field_simp
      rw [hpr]
      simp only [e]
      rw [show (2 * Real.pi * Complex.I * (((k * r : ℕ) : ℝ) : ℂ))
            = ((k * r : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [hval, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((Finset.range p).filter (fun r => Nat.gcd r p = 1)).card = p - 1 := by
      rw [← Nat.totient_prime hp, Nat.totient_eq_card_coprime]
      apply Finset.card_bij (fun r _ => r)
      · intro r hr
        rw [Finset.mem_filter] at hr ⊢
        exact ⟨hr.1, by rw [Nat.Coprime, Nat.gcd_comm]; exact hr.2⟩
      · intro r _ r' _ h; exact h
      · intro r hr
        rw [Finset.mem_filter] at hr
        exact ⟨r, by rw [Finset.mem_filter]; exact ⟨hr.1, by rw [Nat.gcd_comm]; exact hr.2⟩, rfl⟩
    rw [hcard]
    have hp1 : 1 ≤ p := hp.one_lt.le
    push_cast [Nat.cast_sub hp1]
    ring
  · rw [if_neg hd]
    have hcop : Int.gcd (n : ℤ) p = 1 := by
      have hc : Nat.Coprime n p := (hp.coprime_iff_not_dvd.mpr hd).symm
      rw [Int.gcd_natCast_natCast]; exact hc
    have hr := ramanujan_sum_coprime (n : ℤ) p hp.pos hcop
    have hbridge : ramSum p n
        = ∑ r ∈ (Finset.range p).filter (fun r => Nat.gcd r p = 1),
            e ((((n : ℤ) : ℝ)) * r / p) := by
      rw [ramSum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Int.cast_natCast]
    rw [hbridge, hr]
    norm_num [ArithmeticFunction.moebius_apply_prime hp]

/-- **The integer Ramanujan sum at a prime**: `c_p(n) = p−1` if `p∣n`, else `−1`. Follows from
    `ramSum_prime` through `ramSum_eq_cRam` + injectivity of `ℤ ↪ ℂ`. Together with `cRam_mul`
    this gives `c_q(n) = ∏_{p∣q}(…)` for every squarefree `q`. -/
lemma cRam_prime (p n : ℕ) (hp : p.Prime) :
    cRam p n = if p ∣ n then ((p : ℤ) - 1) else -1 := by
  have h1 : (cRam p n : ℂ) = if p ∣ n then ((p : ℂ) - 1) else -1 := by
    rw [← ramSum_eq_cRam p n hp.pos, ramSum_prime p n hp]
  have h2 : ((if p ∣ n then ((p : ℤ) - 1) else -1 : ℤ) : ℂ)
      = if p ∣ n then ((p : ℂ) - 1) else -1 := by
    split <;> push_cast <;> ring
  exact_mod_cast h1.trans h2.symm

/-- `c_1(n) = 1` (the `q=1` term of the singular series). -/
lemma cRam_one (n : ℕ) : cRam 1 n = 1 := by
  simp [cRam, Nat.divisors_one]

/-- **Closed Ramanujan formula (squared)**: for squarefree `q`, `c_q(n)² = φ(gcd(q,n))²`. Since
    `c_q(n) = μ(q/g)·φ(g)` (`g = gcd(q,n)`) and `μ² = 1` on squarefree, the square drops the sign.
    Strong induction peeling `minFac`, via `cRam_mul` (multiplicativity) + `cRam_prime` (base) +
    `gcd(pm,n)=gcd(p,n)gcd(m,n)` (coprime). This is the clean `|c_q(n)| = φ(gcd(q,n))` that makes the
    Ramanujan sum constant on gcd-fibers — the crux of the arithmetic length-capped mean square
    `∑_{n<N} c_q(n)² ≤ e·N·φ(q)` (avoids the `σ(q)²` error of the naive lcm-expansion). -/
lemma cRam_sq_sqfree (q n : ℕ) (hq : Squarefree q) :
    (cRam q n) ^ 2 = (Nat.totient (Nat.gcd q n) : ℤ) ^ 2 := by
  induction q using Nat.strong_induction_on with
  | _ q IH =>
    rcases eq_or_ne q 1 with rfl | hq1
    · simp [cRam_one, Nat.gcd_one_left, Nat.totient_one]
    · have hq0 : q ≠ 0 := hq.ne_zero
      have hpp : (q.minFac).Prime := Nat.minFac_prime hq1
      have hpdvd : q.minFac ∣ q := Nat.minFac_dvd q
      set p := q.minFac with hp
      set m := q / p with hm
      have hpm : p * m = q := Nat.mul_div_cancel' hpdvd
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hpm; omega
        · exact h
      have hmdvd : m ∣ q := ⟨p, by rw [← hpm]; ring⟩
      have hcop : Nat.Coprime p m := by
        rw [hpp.coprime_iff_not_dvd]
        intro hdvd
        have hpp2 : p * p ∣ q := by rw [← hpm]; exact mul_dvd_mul_left p hdvd
        exact hpp.ne_one (Nat.isUnit_iff.mp (hq p hpp2))
      have hmsq : Squarefree m := hq.squarefree_of_dvd hmdvd
      have hmlt : m < q := by rw [← hpm]; exact (Nat.lt_mul_iff_one_lt_left hmpos).mpr hpp.one_lt
      have hIH := IH m hmlt hmsq
      have hgcd : Nat.gcd (p * m) n = Nat.gcd p n * Nat.gcd m n := by
        rw [Nat.gcd_comm (p * m) n, hcop.gcd_mul n, Nat.gcd_comm n p, Nat.gcd_comm n m]
      have hcopg : Nat.Coprime (Nat.gcd p n) (Nat.gcd m n) :=
        (hcop.coprime_dvd_left (Nat.gcd_dvd_left p n)).coprime_dvd_right (Nat.gcd_dvd_left m n)
      rw [← hpm, cRam_mul n p m hcop, mul_pow, hIH, hgcd, Nat.totient_mul hcopg]
      push_cast
      rw [mul_pow]
      congr 1
      rw [cRam_prime p n hpp]
      by_cases hpn : p ∣ n
      · rw [if_pos hpn]
        have hgp : Nat.gcd p n = p := Nat.gcd_eq_left hpn
        rw [hgp, Nat.totient_prime hpp]
        push_cast [Nat.cast_sub hpp.one_le]
        ring
      · rw [if_neg hpn]
        have hgp : Nat.gcd p n = 1 := hpp.coprime_iff_not_dvd.mpr hpn
        rw [hgp, Nat.totient_one]
        norm_num

/-- **Multiples count** (`n=0` excluded ⇒ no `+1`): `#{n∈[1,N) : g∣n} ≤ (N-1)/g` for `g ≥ 1`. The
    gcd-fiber `{n : gcd(q,n)=g} ⊆ {n : g∣n}`, so this bounds each fiber in the arithmetic
    length-capped mean square `∑_{n<N} c_q(n)² = ∑_{g|q} φ(g)²·#{gcd=g} ≤ (N-1)∑ φ(g)²/g`. -/
lemma card_multiples_Ico_le (N g : ℕ) (hg : 1 ≤ g) :
    ((Finset.Ico 1 N).filter (fun n => g ∣ n)).card ≤ (N - 1) / g := by
  have hsub : (Finset.Ico 1 N).filter (fun n => g ∣ n)
      ⊆ (Finset.Ico 1 ((N - 1) / g + 1)).image (fun k => g * k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨hn1, hn2⟩, hgn⟩ := hn
    rw [Finset.mem_image]
    refine ⟨n / g, ?_, Nat.mul_div_cancel' hgn⟩
    rw [Finset.mem_Ico]
    refine ⟨(Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by omega) hgn), ?_⟩
    have hle : n ≤ N - 1 := by omega
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hle)
  calc ((Finset.Ico 1 N).filter (fun n => g ∣ n)).card
      ≤ ((Finset.Ico 1 ((N - 1) / g + 1)).image (fun k => g * k)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.Ico 1 ((N - 1) / g + 1)).card := Finset.card_image_le
    _ = (N - 1) / g := by rw [Nat.card_Ico, Nat.add_sub_cancel]

/-- The **truncated singular series** `𝔖_P(n) = ∑_{1≤q≤P} μ(q)²·c_q(n)/φ(q)²`, real-valued (via
    the integer `cRam`). The `q=1` term is `1`; `q=2` contributes `+1` for even `n`; the Euler
    product `∏_{p∣n}(1+1/(p-1))·∏_{p∤n}(1-1/(p-1)²) ≥ 2·∏_{p≥3}(1-1/(p-1)²)` bounds it below by a
    positive constant for even `n` — the lower bound `hmain` consumes (`𝔖_P(n)·r_N(n) ≥ c₀·X`). -/
noncomputable def singSeries (P n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 P, ((ArithmeticFunction.moebius q : ℝ) ^ 2)
    * (cRam q n : ℝ) / ((Nat.totient q : ℝ) ^ 2)

/-- The singular-series **local term** `T(q) = μ(q)²·c_q(n)/φ(q)²` as an arithmetic function.
    Multiplicative (product of the multiplicative `μ²`, `cRam(·,n)`, `1/φ²`), so its total sum
    factors as an Euler product `∏_p (1+T(p))` — the route to `𝔖(n) ≥ 1.32` for even `n`. -/
noncomputable def Tarith (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => (ArithmeticFunction.moebius q : ℝ) ^ 2 * (cRam q n : ℝ) / (Nat.totient q : ℝ) ^ 2,
    by simp⟩

lemma Tarith_apply (n q : ℕ) :
    Tarith n q = (ArithmeticFunction.moebius q : ℝ) ^ 2 * (cRam q n : ℝ)
      / (Nat.totient q : ℝ) ^ 2 := rfl

lemma isMult_Tarith (n : ℕ) : (Tarith n).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [Tarith_apply, cRam_one, ArithmeticFunction.isMultiplicative_moebius.1]
  · intro a b hab
    simp only [Tarith_apply]
    rw [cRam_mul n a b hab, ArithmeticFunction.isMultiplicative_moebius.2 hab,
      Nat.totient_mul hab]
    push_cast
    ring

/-- **Euler local factor**: `∑'_k T(p^k) = 1 + T(p)` for prime `p` — the sum over prime powers
    collapses to `k=0,1` since `T(p^k)=0` for `k≥2` (`p^k` not squarefree ⇒ `μ(p^k)=0`). This is
    the per-prime factor Mathlib's `eulerProduct_tprod` produces for `𝔖(n) = ∏_p (1+T(p))`. -/
lemma Tarith_local (p n : ℕ) (hp : p.Prime) :
    ∑' k : ℕ, Tarith n (p ^ k) = 1 + Tarith n p := by
  have hsupp : ∀ k ∉ ({0, 1} : Finset ℕ), Tarith n (p ^ k) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    have hk2 : 2 ≤ k := by omega
    rw [Tarith_apply]
    have hμ : ArithmeticFunction.moebius (p ^ k) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      rintro ⟨_, hk1⟩
      omega
    rw [hμ]; simp
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by norm_num), pow_zero, pow_one,
    (isMult_Tarith n).1]

/-- The singular-series local term at a prime: `T(p) = (p−1)/(p−1)² = 1/(p−1)` if `p∣n`, else
    `−1/(p−1)²`. -/
lemma Tarith_prime (p n : ℕ) (hp : p.Prime) :
    Tarith n p = (if p ∣ n then ((p : ℝ) - 1) else -1) / ((p : ℝ) - 1) ^ 2 := by
  have hμ : ((ArithmeticFunction.moebius p : ℝ)) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
  have hφ : ((Nat.totient p : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]; norm_num
  have hc : ((cRam p n : ℝ)) = if p ∣ n then ((p : ℝ) - 1) else -1 := by
    rw [cRam_prime p n hp, Int.cast_ite]; push_cast; norm_num
  rw [Tarith_apply, hμ, hφ, hc, one_mul]

/-- **Euler factor positivity** (for even `n`): `0 < 1 + T(p)` for every prime `p`. At `p=2`
    (`2∣n`) the factor is `2`; at `p≥3` it is `1+1/(p-1) > 0` (if `p∣n`) or `1-1/(p-1)² ≥ 3/4`
    (if `p∤n`). This makes the Euler product `∏_p (1+T(p))` a product of positive factors. -/
lemma one_add_Tarith_pos (p n : ℕ) (hp : p.Prime) (hn : Even n) : 0 < 1 + Tarith n p := by
  rw [Tarith_prime p n hp]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  by_cases hd : p ∣ n
  · rw [if_pos hd]
    have : (0 : ℝ) < ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · rw [if_neg hd]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · exact absurd (h2 ▸ (even_iff_two_dvd.mp hn)) hd
      · have : p ≠ 2 := by rintro rfl; exact hd (even_iff_two_dvd.mp hn)
        have : 3 ≤ p := by
          rcases hp.two_le.lt_or_eq with h | h
          · omega
          · exact absurd h.symm this
        exact_mod_cast this
    have hp1 : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have hsq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hb : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hsq
    have hrw : (-1 : ℝ) / ((p : ℝ) - 1) ^ 2 = -(1 / ((p : ℝ) - 1) ^ 2) := by ring
    rw [hrw]
    linarith [hb]

/-- `K·(log X)³ ≤ √X` eventually — the poly-beats-√ estimate for `hnegl`. Route: `u=log X`,
    `√X=exp(u/2)=(exp(u/8))⁴ ≥ (1+u/8)⁴ ≥ (u/8)⁴ = u⁴/4096 ≥ K u³` once `u ≥ 4096K`. -/
lemma poly3_le_sqrt (K : ℝ) (hK : 0 < K) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → K * Real.log X ^ 3 ≤ Real.sqrt X := by
  refine ⟨Nat.ceil (Real.exp (4096 * K)) + 2, fun X hX => ?_⟩
  have hexp1 : (1 : ℝ) ≤ Real.exp (4096 * K) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
  have hXexp : Real.exp (4096 * K) ≤ (X : ℝ) := by
    have h1 : (⌈Real.exp (4096 * K)⌉₊ : ℝ) ≤ (X : ℝ) := by
      have : ⌈Real.exp (4096 * K)⌉₊ ≤ X := by omega
      exact_mod_cast this
    linarith [Nat.le_ceil (Real.exp (4096 * K))]
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (by linarith) hXexp
  have hu : 4096 * K ≤ Real.log X := by
    rw [← Real.log_exp (4096 * K)]; exact Real.log_le_log (Real.exp_pos _) hXexp
  set u := Real.log X with hudef
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hsqrt : Real.sqrt X = Real.exp (u / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hXpos, hudef]; ring_nf
  rw [hsqrt]
  have hle : 1 + u / 8 ≤ Real.exp (u / 8) := by
    have := Real.add_one_le_exp (u / 8); linarith
  have hpow : (1 + u / 8) ^ 4 ≤ Real.exp (u / 2) := by
    have h4 : (1 + u / 8) ^ 4 ≤ (Real.exp (u / 8)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hle 4
    rwa [← Real.exp_nat_mul, show ((4 : ℕ) : ℝ) * (u / 8) = u / 2 by push_cast; ring] at h4
  have hb1 : (u / 8) ^ 4 ≤ (1 + u / 8) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hb2 : K * u ^ 3 ≤ (u / 8) ^ 4 := by
    have hid : (u / 8) ^ 4 = u ^ 4 / 4096 := by ring
    have hkey : 4096 * K * u ^ 3 ≤ u * u ^ 3 :=
      mul_le_mul_of_nonneg_right hu (pow_nonneg hu0.le 3)
    rw [hid]
    nlinarith [hkey, hu0]
  linarith [hpow, hb1, hb2]

/-- **`hnegl` discharged** (for any `c₀ > 0`): the prime-power negligibility hypothesis of the
    weighted reduction — `2 log²n·√n·(log₂n+1) ≤ c₀·X/2` for `n ∈ (X/2,X]`, `X` large. Bounds
    every factor by its `X`-value, reducing to `K(log X)³ ≤ √X` (`poly3_le_sqrt`). -/
lemma negl_bound (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X → ∀ n : ℕ, X / 2 < n → n ≤ X →
      2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1)) ≤ c₀ * X / 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set CL : ℝ := 1 / Real.log 2 + 1 with hCL
  have hCLpos : 0 < CL := by rw [hCL]; positivity
  obtain ⟨X₀, hX₀⟩ := poly3_le_sqrt (4 * CL / c₀) (by positivity)
  refine ⟨max X₀ 3, fun X hX n hn1 hn2 => ?_⟩
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hX0X : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hn1' : 1 ≤ n := by omega
  have hXR : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
  have hnXR : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hn2
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hnR1
  have hlognX : Real.log n ≤ Real.log X := Real.log_le_log (by linarith) hnXR
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogX1 : 1 ≤ Real.log X := by
    have he3 : Real.exp 1 ≤ (X : ℝ) := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 1) he3
  have hsqrtn : (Nat.sqrt n : ℝ) ≤ Real.sqrt X := by
    have h2 : (Nat.sqrt n : ℝ) ^ 2 ≤ (X : ℝ) := by
      have hh : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
      linarith [hnXR]
    calc (Nat.sqrt n : ℝ) = Real.sqrt ((Nat.sqrt n : ℝ) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt X := Real.sqrt_le_sqrt h2
  have hlog2n : (Nat.log 2 n : ℝ) ≤ Real.log X / Real.log 2 := by
    have h1 : 2 ^ (Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 : ℝ) ^ (Nat.log 2 n)) ≤ (n : ℝ) := by exact_mod_cast h1
    have h3 : Real.log (2 ^ (Nat.log 2 n)) ≤ Real.log n :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    rw [le_div_iff₀ hlog2]
    calc (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := h3
      _ ≤ Real.log X := hlognX
  have hC : (Nat.log 2 n : ℝ) + 1 ≤ CL * Real.log X := by
    have hdiv : Real.log X / Real.log 2 = (1 / Real.log 2) * Real.log X := by ring
    rw [hCL]
    nlinarith [hlog2n, hlogX1, hlog2, hdiv]
  have hsqrtX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hlog2n0 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  have hmid : 2 * Real.log n ^ 2 * ((Nat.sqrt n : ℝ) * (Nat.log 2 n + 1))
      ≤ 2 * CL * Real.log X ^ 3 * Real.sqrt X := by
    have hA : Real.log n ^ 2 ≤ Real.log X ^ 2 := pow_le_pow_left₀ hlogn0 hlognX 2
    have hD : (Nat.sqrt n : ℝ) * (Nat.log 2 n + 1) ≤ Real.sqrt X * (CL * Real.log X) :=
      mul_le_mul hsqrtn hC hlog2n0 hsqrtX0
    have hrhs : 2 * CL * Real.log X ^ 3 * Real.sqrt X
        = 2 * Real.log X ^ 2 * (Real.sqrt X * (CL * Real.log X)) := by ring
    rw [hrhs]
    have h2A : 2 * Real.log n ^ 2 ≤ 2 * Real.log X ^ 2 := by linarith
    apply mul_le_mul h2A hD (by positivity) (by positivity)
  have hsqX : Real.sqrt X * Real.sqrt X = (X : ℝ) := Real.mul_self_sqrt (by linarith)
  have hfin : 2 * CL * Real.log X ^ 3 * Real.sqrt X ≤ c₀ * X / 2 := by
    have hstep : 4 * CL / c₀ * Real.log X ^ 3 ≤ Real.sqrt X := hX₀ X hX0X
    have h4 : 4 * CL * Real.log X ^ 3 ≤ c₀ * Real.sqrt X := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc₀] at hstep
      nlinarith [hstep]
    nlinarith [h4, hsqX, hsqrtX0, mul_le_mul_of_nonneg_right h4 hsqrtX0]
  linarith [hmid, hfin]

/-- Per-prime totient bound `(p-1)² ≥ p^(6/5)` for `p ≥ 3` (from the integer `(p-1)^10 ≥ p^6`
    via `(k+3)³ ≤ (k+2)⁵` squared, bridged with `rpow`). The multiplicative seed for
    `φ(q)² ≥ c·q^(6/5)` (squarefree `q`) ⇒ `∑ 1/φ(q)²` converges ⇒ `Tarith_summable`. -/
lemma prime_factor_rpow (p : ℕ) (hp : 3 ≤ p) :
    (p : ℝ) ^ ((6 : ℝ) / 5) ≤ ((p : ℝ) - 1) ^ 2 := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hint : (p : ℝ) ^ 6 ≤ ((p : ℝ) - 1) ^ 10 := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 3 := ⟨p - 3, by omega⟩
    push_cast
    have hpm : ((k : ℝ) + 3 - 1) = (k : ℝ) + 2 := by ring
    have h5 : ((k : ℝ) + 3) ^ 3 ≤ ((k : ℝ) + 2) ^ 5 := by
      nlinarith [pow_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity) 5,
        pow_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity) 4,
        pow_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity) 3, sq_nonneg (k:ℝ)]
    calc ((k : ℝ) + 3) ^ 6 = (((k : ℝ) + 3) ^ 3) ^ 2 := by ring
      _ ≤ (((k : ℝ) + 2) ^ 5) ^ 2 := by apply pow_le_pow_left₀ (by positivity) h5
      _ = ((k : ℝ) + 2) ^ 10 := by ring
      _ = ((k : ℝ) + 3 - 1) ^ 10 := by rw [hpm]
  have h15 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 6) hint
    (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 5)
  rw [← Real.rpow_natCast (p : ℝ) 6, ← Real.rpow_natCast ((p : ℝ) - 1) 10,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ)),
    ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)] at h15
  norm_num at h15
  exact h15

/-- `q^(6/5) ≤ φ(q)²` for **odd squarefree** `q` (all prime factors ≥ 3, so `prime_factor_rpow`
    applies with multiplicative constant 1). Strong induction peeling the minimal prime factor. -/
lemma odd_sqfree_totient (q : ℕ) (hq : Squarefree q) (hodd : Odd q) :
    (q : ℝ) ^ ((6 : ℝ) / 5) ≤ (Nat.totient q : ℝ) ^ 2 := by
  induction q using Nat.strong_induction_on with
  | _ q IH =>
    rcases eq_or_ne q 1 with rfl | hq1
    · norm_num
    · have hq0 : q ≠ 0 := hq.ne_zero
      have hq2 : 2 ≤ q := by omega
      have hpp : (q.minFac).Prime := Nat.minFac_prime hq1
      have hpdvd : q.minFac ∣ q := Nat.minFac_dvd q
      set p := q.minFac with hp
      set m := q / p with hm
      have hpm : p * m = q := Nat.mul_div_cancel' hpdvd
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hpm; omega
        · exact h
      have hp3 : 3 ≤ p := by
        have hp2 : p ≠ 2 := by
          intro h2
          have h2q : (2 : ℕ) ∣ q := h2 ▸ hpdvd
          exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2q)
        have := hpp.two_le; omega
      have hmdvd : m ∣ q := ⟨p, by rw [← hpm]; ring⟩
      have hcop : Nat.Coprime p m := by
        rw [hpp.coprime_iff_not_dvd]
        intro hdvd
        have hpp2 : p * p ∣ q := by rw [← hpm]; exact mul_dvd_mul_left p hdvd
        exact hpp.ne_one (Nat.isUnit_iff.mp (hq p hpp2))
      have hmsq : Squarefree m := Squarefree.squarefree_of_dvd hmdvd hq
      have hmodd : Odd m := by
        rcases Nat.even_or_odd m with he | ho
        · exfalso
          have hqe : Even q := by rw [← hpm]; exact he.mul_left p
          exact (Nat.not_even_iff_odd.mpr hodd) hqe
        · exact ho
      have hmlt : m < q := by
        rw [← hpm]; exact (Nat.lt_mul_iff_one_lt_left hmpos).mpr hpp.one_lt
      have hIH := IH m hmlt hmsq hmodd
      rw [← hpm, Nat.totient_mul hcop, Nat.totient_prime hpp]
      have hp1 : 1 ≤ p := hpp.one_le
      push_cast [Nat.cast_sub hp1]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      calc (p : ℝ) ^ ((6 : ℝ) / 5) * (m : ℝ) ^ ((6 : ℝ) / 5)
          ≤ ((p : ℝ) - 1) ^ 2 * (Nat.totient m : ℝ) ^ 2 :=
            mul_le_mul (prime_factor_rpow p hp3) hIH (by positivity) (by positivity)
        _ = (((p : ℝ) - 1) * (Nat.totient m : ℝ)) ^ 2 := by ring

/-- `q^(6/5) ≤ 4·φ(q)²` for **all squarefree** `q` (even case `q=2m`, `m` odd squarefree,
    `φ(2m)=φ(m)`, absorbing `2^(6/5) < 4`). The totient lower bound driving `Tarith_summable`. -/
lemma sqfree_totient (q : ℕ) (hq : Squarefree q) :
    (q : ℝ) ^ ((6 : ℝ) / 5) ≤ 4 * (Nat.totient q : ℝ) ^ 2 := by
  rcases Nat.even_or_odd q with he | ho
  · obtain ⟨m, hm⟩ := he
    have hm2 : q = 2 * m := by omega
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm2; exact absurd hm2 hq.ne_zero
      · exact h
    have hmodd : Odd m := by
      rcases Nat.even_or_odd m with hme | hmo
      · exfalso
        obtain ⟨k, hk⟩ := hme
        have : (2 * 2) ∣ q := ⟨k, by omega⟩
        exact (by decide : ¬ IsUnit 2) (hq 2 this)
      · exact hmo
    have hmsq : Squarefree m := hq.squarefree_of_dvd ⟨2, by rw [hm2]; ring⟩
    have hcop : Nat.Coprime 2 m := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h
      exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h)
    have hIH := odd_sqfree_totient m hmsq hmodd
    rw [hm2, Nat.totient_mul hcop, Nat.totient_prime Nat.prime_two]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have h2r : (2 : ℝ) ^ ((6 : ℝ) / 5) ≤ 4 := by
      calc (2 : ℝ) ^ ((6 : ℝ) / 5) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := by norm_num
    have hstep : (2 : ℝ) ^ ((6 : ℝ) / 5) * (m : ℝ) ^ ((6 : ℝ) / 5)
        ≤ 4 * (Nat.totient m : ℝ) ^ 2 :=
      mul_le_mul h2r hIH (by positivity) (by norm_num)
    nlinarith [hstep]
  · have h := odd_sqfree_totient q hq ho
    nlinarith [h, sq_nonneg (Nat.totient q : ℝ)]

/-- **Sharper per-prime totient seed**: `(p-1)² ≥ p^(3/2)` for `p ≥ 5` (constant 1). Squares to the
    integer `(p-1)^4 ≥ p^3` (holds for `p≥4`), bridged with `rpow`. Multiplicative seed for
    `φ(q)² ≥ c·q^(3/2)` (squarefree q, exponent 3/2 > 4/3) ⇒ `∑ 1/φ(q)^(3/2)` converges — the
    Minkowski-route summability the harc truncation needs (crude `p^(6/5)` gives only exponent 6/5
    < 4/3, too weak). Small primes 2,3 are absorbed into `c` separately in `sqfree_totient_strong`. -/
lemma prime_factor_rpow_strong (p : ℕ) (hp : 5 ≤ p) :
    (p : ℝ) ^ ((3 : ℝ) / 2) ≤ ((p : ℝ) - 1) ^ 2 := by
  have hpR : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hint : (p : ℝ) ^ 3 ≤ ((p : ℝ) - 1) ^ 4 := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 5 := ⟨p - 5, by omega⟩
    push_cast
    nlinarith [pow_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity) 4,
      pow_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity) 3,
      pow_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity) 2, sq_nonneg (k:ℝ)]
  have h12 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 3) hint
    (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
  rw [← Real.rpow_natCast (p : ℝ) 3, ← Real.rpow_natCast ((p : ℝ) - 1) 4,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ)),
    ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)] at h12
  norm_num at h12
  exact h12

/-- `q^(3/2) ≤ φ(q)²` for squarefree `q` with **all prime factors ≥ 5** (constant 1). Strong
    induction peeling the minimal prime factor; `prime_factor_rpow_strong` supplies the per-prime step. -/
lemma ge5_totient (q : ℕ) (hq : Squarefree q) (h5 : ∀ p, p.Prime → p ∣ q → 5 ≤ p) :
    (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (Nat.totient q : ℝ) ^ 2 := by
  induction q using Nat.strong_induction_on with
  | _ q IH =>
    rcases eq_or_ne q 1 with rfl | hq1
    · norm_num
    · have hq0 : q ≠ 0 := hq.ne_zero
      have hpp : (q.minFac).Prime := Nat.minFac_prime hq1
      have hpdvd : q.minFac ∣ q := Nat.minFac_dvd q
      set p := q.minFac with hp
      set m := q / p with hm
      have hpm : p * m = q := Nat.mul_div_cancel' hpdvd
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hpm; omega
        · exact h
      have hp5 : 5 ≤ p := h5 p hpp hpdvd
      have hmdvd : m ∣ q := ⟨p, by rw [← hpm]; ring⟩
      have hcop : Nat.Coprime p m := by
        rw [hpp.coprime_iff_not_dvd]
        intro hdvd
        have hpp2 : p * p ∣ q := by rw [← hpm]; exact mul_dvd_mul_left p hdvd
        exact hpp.ne_one (Nat.isUnit_iff.mp (hq p hpp2))
      have hmsq : Squarefree m := hq.squarefree_of_dvd hmdvd
      have hm5 : ∀ r, r.Prime → r ∣ m → 5 ≤ r := fun r hr hrm => h5 r hr (hrm.trans hmdvd)
      have hmlt : m < q := by rw [← hpm]; exact (Nat.lt_mul_iff_one_lt_left hmpos).mpr hpp.one_lt
      have hIH := IH m hmlt hmsq hm5
      rw [← hpm, Nat.totient_mul hcop, Nat.totient_prime hpp]
      have hp1 : 1 ≤ p := hpp.one_le
      push_cast [Nat.cast_sub hp1]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      calc (p : ℝ) ^ ((3 : ℝ) / 2) * (m : ℝ) ^ ((3 : ℝ) / 2)
          ≤ ((p : ℝ) - 1) ^ 2 * (Nat.totient m : ℝ) ^ 2 :=
            mul_le_mul (prime_factor_rpow_strong p hp5) hIH (by positivity) (by positivity)
        _ = (((p : ℝ) - 1) * (Nat.totient m : ℝ)) ^ 2 := by ring

/-- `q^(3/2) ≤ 2·φ(q)²` for **odd squarefree** `q` (constant 2). Peels the possible factor 3
    (which needs its own constant); the rest has all factors ≥5 and feeds `ge5_totient`. -/
lemma odd_totient_strong (q : ℕ) (hq : Squarefree q) (hodd : Odd q) :
    (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (Nat.totient q : ℝ) ^ 2 := by
  have hq0 : q ≠ 0 := hq.ne_zero
  by_cases h3 : 3 ∣ q
  · have h3p : Nat.Prime 3 := by norm_num
    set m := q / 3 with hm
    have hpm : 3 * m = q := Nat.mul_div_cancel' h3
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hpm; omega
      · exact h
    have hmdvd : m ∣ q := ⟨3, by rw [← hpm]; ring⟩
    have hmsq : Squarefree m := hq.squarefree_of_dvd hmdvd
    have hcop : Nat.Coprime 3 m := by
      rw [h3p.coprime_iff_not_dvd]; intro hdvd
      have : (3 * 3) ∣ q := by rw [← hpm]; exact mul_dvd_mul_left 3 hdvd
      exact h3p.ne_one (Nat.isUnit_iff.mp (hq 3 this))
    have hm5 : ∀ r, r.Prime → r ∣ m → 5 ≤ r := by
      intro r hr hrm
      have hrq : r ∣ q := hrm.trans hmdvd
      have hr2 : r ≠ 2 := by
        intro h; rw [h] at hrq
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrq)
      have hr3 : r ≠ 3 := by
        intro h; rw [h] at hrm
        have h31 : (3 : ℕ) ∣ 1 := by
          have := Nat.dvd_gcd (dvd_refl 3) hrm; rwa [hcop] at this
        exact absurd (Nat.le_of_dvd one_pos h31) (by norm_num)
      have hr2le := hr.two_le
      rcases Nat.lt_or_ge r 5 with hlt | hge
      · interval_cases r
        · exact absurd rfl hr2
        · exact absurd rfl hr3
        · exact absurd hr (by norm_num)
      · exact hge
    have hIH := ge5_totient m hmsq hm5
    have ht3 : Nat.totient 3 = 2 := by decide
    rw [← hpm, Nat.totient_mul hcop, ht3]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have h32 : (3 : ℝ) ^ ((3 : ℝ) / 2) ≤ 8 := by
      have h1 : ((3 : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = 27 := by
        rw [← Real.rpow_natCast ((3 : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]; norm_num
      nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) ((3 : ℝ) / 2), h1]
    calc (3 : ℝ) ^ ((3 : ℝ) / 2) * (m : ℝ) ^ ((3 : ℝ) / 2)
        ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) * (Nat.totient m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hIH (by positivity)
      _ ≤ 8 * (Nat.totient m : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h32 (by positivity)
      _ = 2 * (2 * (Nat.totient m : ℝ)) ^ 2 := by ring
  · have h5 : ∀ p, p.Prime → p ∣ q → 5 ≤ p := by
      intro p hp hpq
      have hp2 : p ≠ 2 := by
        intro h; rw [h] at hpq
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpq)
      have hp3 : p ≠ 3 := fun h => h3 (h ▸ hpq)
      have hp2le := hp.two_le
      rcases Nat.lt_or_ge p 5 with hlt | hge
      · interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
        · exact absurd hp (by norm_num)
      · exact hge
    have hg := ge5_totient q hq h5
    nlinarith [hg, sq_nonneg (Nat.totient q : ℝ)]

/-- **Sharper totient bound**: `q^(3/2) ≤ 8·φ(q)²` for all squarefree `q` (exponent 3/2 > 4/3).
    Peels the possible factor 2 (`2^(5/2) ≈ 5.66 ≤ 8`); the odd part feeds `odd_totient_strong`.
    Gives `φ(q) ≥ q^(3/4)/√8`, so `∑ 1/φ(q)^(3/2)` converges — the Minkowski-route summability harc needs. -/
lemma sqfree_totient_strong (q : ℕ) (hq : Squarefree q) :
    (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 8 * (Nat.totient q : ℝ) ^ 2 := by
  rcases Nat.even_or_odd q with he | ho
  · obtain ⟨m, hm⟩ := he
    have hm2 : q = 2 * m := by omega
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm2; exact absurd hm2 hq.ne_zero
      · exact h
    have hmodd : Odd m := by
      rcases Nat.even_or_odd m with hme | hmo
      · exfalso; obtain ⟨k, hk⟩ := hme
        have : (2 * 2) ∣ q := ⟨k, by omega⟩
        exact (by decide : ¬ IsUnit 2) (hq 2 this)
      · exact hmo
    have hmsq : Squarefree m := hq.squarefree_of_dvd ⟨2, by rw [hm2]; ring⟩
    have hcop : Nat.Coprime 2 m := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; intro h
      exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr h)
    have hIH := odd_totient_strong m hmsq hmodd
    rw [hm2, Nat.totient_mul hcop, Nat.totient_two, one_mul]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have h2 : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 := by
      have h1 : ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = 8 := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]; norm_num
      nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) ((3 : ℝ) / 2), h1]
    calc (2 : ℝ) ^ ((3 : ℝ) / 2) * (m : ℝ) ^ ((3 : ℝ) / 2)
        ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) * (2 * (Nat.totient m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hIH (by positivity)
      _ ≤ 8 * (Nat.totient m : ℝ) ^ 2 := by nlinarith [h2, sq_nonneg (Nat.totient m : ℝ)]
  · have := odd_totient_strong q hq ho
    nlinarith [this, sq_nonneg (Nat.totient q : ℝ)]

/-- `|c_q(n)| ≤ σ(n) = ∑_{d∣n} d` (uniform in `q`), for `n ≥ 1`. Triangle inequality on the divisor
    sum + `|μ|≤1`, reindex `d↦q/d`, then `{e∣q : e∣n} ⊆ divisors n`. -/
lemma cRam_abs_le (q n : ℕ) (hn : 1 ≤ n) :
    |cRam q n| ≤ ∑ d ∈ n.divisors, (d : ℤ) := by
  rw [cRam]
  calc |∑ d ∈ q.divisors, ArithmeticFunction.moebius d
          * (if q / d ∣ n then ((q / d : ℕ) : ℤ) else 0)|
      ≤ ∑ d ∈ q.divisors, |ArithmeticFunction.moebius d
          * (if q / d ∣ n then ((q / d : ℕ) : ℤ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ q.divisors, (if q / d ∣ n then ((q / d : ℕ) : ℤ) else 0) := by
        apply Finset.sum_le_sum
        intro d _
        rw [abs_mul]
        have hμ : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
        have hnn : (0 : ℤ) ≤ (if q / d ∣ n then ((q / d : ℕ) : ℤ) else 0) := by
          split <;> positivity
        calc |(ArithmeticFunction.moebius d : ℤ)| * |if q / d ∣ n then ((q / d : ℕ) : ℤ) else 0|
            ≤ 1 * |if q / d ∣ n then ((q / d : ℕ) : ℤ) else 0| :=
              mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
          _ = (if q / d ∣ n then ((q / d : ℕ) : ℤ) else 0) := by rw [one_mul, abs_of_nonneg hnn]
    _ = ∑ d ∈ q.divisors, (if d ∣ n then ((d : ℕ) : ℤ) else 0) :=
        Nat.sum_div_divisors q (fun e => if e ∣ n then ((e : ℕ) : ℤ) else 0)
    _ = ∑ d ∈ q.divisors.filter (fun d => d ∣ n), (d : ℤ) := (Finset.sum_filter _ _).symm
    _ ≤ ∑ d ∈ n.divisors, (d : ℤ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_filter] at hd
          rw [Nat.mem_divisors]
          exact ⟨hd.2, by omega⟩
        · intro d _ _; positivity

/-- **Singular-series convergence** — `∑_q |T(q)| < ∞`, for `n ≥ 1` (FALSE at n=0).
    Comparison `‖T(q)‖ ≤ 4σ(n)/q^(6/5)` (squarefree: `cRam_abs_le` + `sqfree_totient`;
    else `μ²=0`) against the summable `∑ 1/q^(6/5)` (`summable_one_div_nat_rpow`). -/
lemma Tarith_summable (n : ℕ) (hn : 1 ≤ n) : Summable (fun q => ‖Tarith n q‖) := by
  have hσ : (0 : ℝ) ≤ (∑ d ∈ n.divisors, (d : ℝ)) := by positivity
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (f := fun q : ℕ => 4 * (∑ d ∈ n.divisors, (d : ℝ)) * (1 / (q : ℝ) ^ ((6 : ℝ) / 5)))
  · intro q
    rw [Tarith_apply, norm_div, norm_mul]
    have hμsq : ‖(ArithmeticFunction.moebius q : ℝ) ^ 2‖ = (ArithmeticFunction.moebius q : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hφsq : ‖(Nat.totient q : ℝ) ^ 2‖ = (Nat.totient q : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hμsq, hφsq]
    have hcR : ‖(cRam q n : ℝ)‖ ≤ (∑ d ∈ n.divisors, (d : ℝ)) := by
      have heq : ‖(cRam q n : ℝ)‖ = ((|cRam q n| : ℤ) : ℝ) := by
        rw [Real.norm_eq_abs, Int.cast_abs]
      rw [heq]
      calc ((|cRam q n| : ℤ) : ℝ) ≤ ((∑ d ∈ n.divisors, (d : ℤ) : ℤ) : ℝ) := by
            exact_mod_cast cRam_abs_le q n hn
        _ = ∑ d ∈ n.divisors, (d : ℝ) := by push_cast; rfl
    have hcRnn : (0 : ℝ) ≤ ‖(cRam q n : ℝ)‖ := norm_nonneg _
    by_cases hsf : Squarefree q
    · have hμ2 : (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
        have h' : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
        nlinarith [sq_abs (ArithmeticFunction.moebius q : ℝ),
          abs_nonneg (ArithmeticFunction.moebius q : ℝ), h']
      have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) ^ 2 := by
        have : 0 < Nat.totient q := Nat.totient_pos.mpr hsf.ne_zero.bot_lt
        positivity
      have hqpos : (0 : ℝ) < (q : ℝ) ^ ((6 : ℝ) / 5) := by
        have hq0 : 0 < q := hsf.ne_zero.bot_lt
        have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
        positivity
      rw [mul_one_div, div_le_div_iff₀ hφpos hqpos]
      nlinarith [hμ2, hcR, hcRnn, hσ, sqfree_totient q hsf,
        mul_le_mul hcR (sqfree_totient q hsf) hqpos.le hσ,
        mul_nonneg hcRnn hqpos.le]
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp
      positivity
  · apply Summable.mul_left
    exact (Real.summable_one_div_nat_rpow).mpr (by norm_num)

end MajorArcMainTerm
end GoldbachChain
