module

public import SecondMoment1054
public import AliquotEquivalence1054
public import SmallRatioKovac1054

@[expose] public section


/-!
# Sharp second-moment `c / [A^3 (1 + log A)^4]` lower-density bound for Erdős #1054

This module establishes the sharp variable-exponent second-moment lower-density
bound `c / (A ^ 3 * (1 + Real.log A) ^ 4)`:

1. **Singleton tail elimination (`tsum_inv_sq_ge_le`, `tsum_rpow_two_add_beta_ge_le`, `inner_tsum_RST_le`)**:
   In the 7-variable gcd/lcm decomposition `(e, r, s) ↦ (h, u, v, w, R, S, T)` of `U E`,
   for fixed `(h, u, v, w)` the singleton variables `R, S, T` satisfy
   `(E : ℝ) / (h * u * v) ≤ R`, `(v * R : ℝ) / w ≤ S`, and `(u * R : ℝ) / w ≤ T`, while
   `1 / (r * s * lcm(e, r, s)) = h^(-3) * u^(-2) * v^(-2) * w^(-3) * R^(-1) * S^(-2) * T^(-2)`.
   Summing over `S` and `T` first (using `∑_{n ≥ M} n^(-2) ≤ 2 * M^(-θ)` at `θ = (1 + β) / 2`)
   and then over `R` (using `∑_{R ≥ M} R^(-(2 + β)) ≤ 2 * M^(-(1 + β))`) eliminates `R, S, T`
   with an absolute constant factor `8` and leaves only the 4-variable product
   `Sp (2 - β) * Sp ((3 - β) / 2) * Sp ((3 - β) / 2) * Sp (2 - β)`.

2. **Sharp second-moment logarithmic endpoint (`sharp_second_moment_logarithmic_endpoint_odd_in_odd_density_one`)**:
   Choosing `β = 1 - 1 / (2 * (1 + log A))` gives
   `(U E).toReal ≤ 8192 * (1 + log A)^4 * E^(-(2 - 1 / (2 * (1 + log A))))`,
   and optimizing `E asymp A^3 * (1 + log A)^4` yields a uniform
   `c / (A^3 * (1 + log A)^4)` lower density bound for odd represented large-ratio witnesses
   inside any `HasOddDensityOne` set `S`.
-/

open Finset Filter Asymptotics MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Erdos1054.SharpSecondMoment

lemma rpow_neg_two_partial_tail_le (K M : ℕ) (hK : 1 ≤ K) :
    ∑ i ∈ Finset.Ico K M, ((i : ℝ) + 1) ^ (-2 : ℝ) ≤ (K : ℝ) ^ (-1 : ℝ) := by
  rcases Nat.lt_or_ge M K with hMK | hKM
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; positivity
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Icc (K : ℝ) (M : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hK0 hx.1) hxy (by norm_num)
  have hstep := hanti.sum_le_integral_Ico hKM
  have hstep' : ∑ i ∈ Finset.Ico K M, ((i : ℝ) + 1) ^ (-2 : ℝ) ≤
      ∫ x in (K : ℝ)..(M : ℝ), x ^ (-2 : ℝ) := by
    simpa using hstep
  refine le_trans hstep' ?_
  rw [integral_rpow (Or.inr ⟨by norm_num, by
    simp only [Set.uIcc_of_le (by exact_mod_cast hKM : (K : ℝ) ≤ M), Set.mem_Icc, not_and, not_le]
    intro h; linarith [hK0]⟩)]
  have hexp : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [hexp, div_le_iff_of_neg (by norm_num : (-1 : ℝ) < 0)]
  nlinarith [Real.rpow_nonneg hM0.le (-1 : ℝ)]

lemma rpow_neg_two_finset_tail_le (K : ℕ) (hK : 1 ≤ K) (T : Finset ℕ) (hT : ∀ n ∈ T, K < n) :
    ∑ n ∈ T, (n : ℝ) ^ (-2 : ℝ) ≤ (K : ℝ) ^ (-1 : ℝ) := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (t := (Finset.Ico K (T.sup id + 1)).image (· + 1)) (fun n hn => ?_)
    (fun n _ _ => by positivity)) ?_
  · have hn1 : K < n := hT n hn
    have hn2 : n ≤ T.sup id := Finset.le_sup (f := id) hn
    rw [Finset.mem_image]
    exact ⟨n - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · rw [Finset.sum_image (fun a _ b _ h => by omega)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) (rpow_neg_two_partial_tail_le K _ hK)
    rw [Nat.cast_add, Nat.cast_one]

lemma tsum_inv_sq_ge_le {M θ : ℝ} (hM : 0 < M) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∑' n : ℕ, if M ≤ (n : ℝ) then ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) else 0) ≤
      ENNReal.ofReal (2 * M ^ (-θ)) := by
  rcases le_or_gt M 1 with hM1 | hM1
  · have hle_Sp : (∑' n : ℕ, if M ≤ (n : ℝ) then ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) else 0) ≤
        _root_.Represented.Sp 2 := by
      rw [_root_.Represented.Sp]
      refine ENNReal.tsum_le_tsum (fun n => ?_)
      split_ifs <;> simp
    have hSp2 : _root_.Represented.Sp 2 ≤ ENNReal.ofReal 2 := by
      have hne : _root_.Represented.Sp 2 ≠ ⊤ := _root_.Represented.Sp_ne_top (by norm_num)
      rw [← ENNReal.ofReal_toReal hne]
      apply ENNReal.ofReal_le_ofReal
      have hle := _root_.Erdos1054.SecondMoment.Sp_toReal_le (p := 2) (by norm_num) le_rfl
      linarith
    have hMθ : 1 ≤ M ^ (-θ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hM hM1 (by linarith)
    refine hle_Sp.trans (hSp2.trans ?_)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · refine ENNReal.tsum_le_of_sum_range_le (fun N => ?_)
    have hsum_eq : ∑ n ∈ Finset.range N, (if M ≤ (n : ℝ) then ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) else 0)
        = ENNReal.ofReal (∑ n ∈ (Finset.range N).filter (fun n : ℕ => M ≤ (n : ℝ)), (n : ℝ) ^ (-2 : ℝ)) := by
      rw [Finset.sum_filter, ENNReal.ofReal_sum_of_nonneg (fun n _ => by split_ifs <;> positivity)]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero]
    rw [hsum_eq]
    apply ENNReal.ofReal_le_ofReal
    set C : ℕ := ⌈M⌉₊ with hCdef
    have hMC : M ≤ (C : ℝ) := Nat.le_ceil M
    have hC2 : 2 ≤ C := by
      have : (1 : ℝ) < (C : ℝ) := lt_of_lt_of_le hM1 hMC
      exact_mod_cast this
    set K : ℕ := C - 1 with hKdef
    have hK1 : 1 ≤ K := by omega
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    have hfilt : ∀ n ∈ (Finset.range N).filter (fun n : ℕ => M ≤ (n : ℝ)), K < n := by
      intro n hn
      rw [Finset.mem_filter] at hn
      have hCn : C ≤ n := Nat.ceil_le.mpr hn.2
      omega
    have htail := rpow_neg_two_finset_tail_le K hK1 _ hfilt
    have hMK : M / 2 ≤ (K : ℝ) := by
      have hCK : C ≤ 2 * K := by omega
      have hCKR : (C : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast hCK
      linarith
    have hK_le : (K : ℝ) ^ (-1 : ℝ) ≤ 2 * M ^ (-1 : ℝ) := by
      have h1 : (K : ℝ) ^ (-1 : ℝ) ≤ (M / 2) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hMK (by norm_num)
      have h2 : (M / 2) ^ (-1 : ℝ) = 2 * M ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, Real.rpow_neg_one]
        ring
      linarith
    have hM_theta : M ^ (-1 : ℝ) ≤ M ^ (-θ) :=
      Real.rpow_le_rpow_of_exponent_le hM1.le (by linarith)
    linarith

lemma tsum_rpow_two_add_beta_ge_le {M β : ℝ} (hM : 0 < M) (hβ0 : 0 ≤ β) :
    (∑' R : ℕ, if M ≤ (R : ℝ) then ENNReal.ofReal ((R : ℝ) ^ (-(2 + β))) else 0) ≤
      ENNReal.ofReal (2 * M ^ (-(1 + β))) := by
  have hpt : ∀ R : ℕ,
      (if M ≤ (R : ℝ) then ENNReal.ofReal ((R : ℝ) ^ (-(2 + β))) else 0) ≤
        ENNReal.ofReal (M ^ (-β)) * (if M ≤ (R : ℝ) then ENNReal.ofReal ((R : ℝ) ^ (-2 : ℝ)) else 0) := by
    intro R
    split_ifs with hMR
    · have hRpos : 0 < (R : ℝ) := lt_of_lt_of_le hM hMR
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hexp : (R : ℝ) ^ (-(2 + β)) = (R : ℝ) ^ (-β) * (R : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_add hRpos]
        congr 1; ring
      rw [hexp]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos hM hMR (by linarith)
    · simp
  have h1 := tsum_inv_sq_ge_le hM zero_le_one le_rfl
  calc (∑' R : ℕ, if M ≤ (R : ℝ) then ENNReal.ofReal ((R : ℝ) ^ (-(2 + β))) else 0)
      ≤ ∑' R : ℕ, ENNReal.ofReal (M ^ (-β)) *
          (if M ≤ (R : ℝ) then ENNReal.ofReal ((R : ℝ) ^ (-2 : ℝ)) else 0) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (M ^ (-β)) *
          (∑' R : ℕ, if M ≤ (R : ℝ) then ENNReal.ofReal ((R : ℝ) ^ (-2 : ℝ)) else 0) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (M ^ (-β)) * ENNReal.ofReal (2 * M ^ (-1 : ℝ)) := by gcongr
    _ = ENNReal.ofReal (2 * M ^ (-(1 + β))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hexp : M ^ (-β) * M ^ (-1 : ℝ) = M ^ (-(1 + β)) := by
          rw [← Real.rpow_add hM]
          congr 1; ring
        linarith

lemma mul_div_rpow_neg {x y z a : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x * y / z) ^ (-a) = x ^ (-a) * y ^ (-a) * z ^ a := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one z,
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hx.le hy.le,
      ← Real.rpow_mul hz.le,
      show (-1 : ℝ) * -a = a by ring]

lemma div_mul_mul_rpow_neg {E x y z a : ℝ} (hE : 0 < E) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (E / (x * y * z)) ^ (-a) = E ^ (-a) * x ^ a * y ^ a * z ^ a := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one (x * y * z),
      Real.mul_rpow hE.le (by positivity),
      ← Real.rpow_mul (by positivity),
      show (-1 : ℝ) * -a = a by ring,
      Real.mul_rpow (by positivity) hz.le,
      Real.mul_rpow hx.le hy.le]
  ring

lemma tsum4 (f₁ f₂ : ℕ → ℝ≥0∞) :
    (∑' p : ℕ × ℕ × ℕ × ℕ, f₁ p.1 * f₂ p.2.1 * f₂ p.2.2.1 * f₁ p.2.2.2)
      = (∑' a, f₁ a) * ((∑' a, f₂ a) * ((∑' a, f₂ a) * (∑' a, f₁ a))) := by
  have e1 : (∑' p : ℕ × ℕ × ℕ × ℕ, f₁ p.1 * f₂ p.2.1 * f₂ p.2.2.1 * f₁ p.2.2.2)
      = ∑' p : ℕ × (ℕ × ℕ × ℕ), f₁ p.1 * (f₂ p.2.1 * f₂ p.2.2.1 * f₁ p.2.2.2) :=
    tsum_congr (fun p => by ring)
  have e2 : (∑' q : ℕ × ℕ × ℕ, f₂ q.1 * f₂ q.2.1 * f₁ q.2.2)
      = ∑' q : ℕ × (ℕ × ℕ), f₂ q.1 * (f₂ q.2.1 * f₁ q.2.2) :=
    tsum_congr (fun q => by ring)
  rw [e1, _root_.Represented.tsum_mul_prod f₁ (fun q : ℕ × ℕ × ℕ => f₂ q.1 * f₂ q.2.1 * f₁ q.2.2)]
  rw [e2, _root_.Represented.tsum_mul_prod f₂ (fun q : ℕ × ℕ => f₂ q.1 * f₁ q.2)]
  rw [_root_.Represented.tsum_mul_prod f₂ f₁]

noncomputable def b4 (h u v w : ℕ) : ℝ≥0∞ :=
  if 1 ≤ h ∧ 1 ≤ u ∧ 1 ≤ v ∧ 1 ≤ w then
    ENNReal.ofReal ((h : ℝ) ^ (-3 : ℝ) * (u : ℝ) ^ (-2 : ℝ) * (v : ℝ) ^ (-2 : ℝ) * (w : ℝ) ^ (-3 : ℝ))
  else 0

noncomputable def bR (E h u v R : ℕ) : ℝ≥0∞ :=
  if (E : ℝ) / ((h : ℝ) * u * v) ≤ (R : ℝ) then
    ENNReal.ofReal ((R : ℝ) ^ (-1 : ℝ))
  else 0

noncomputable def bS (v w R S : ℕ) : ℝ≥0∞ :=
  if ((v : ℝ) * R) / w ≤ (S : ℝ) then
    ENNReal.ofReal ((S : ℝ) ^ (-2 : ℝ))
  else 0

noncomputable def bT (u w R T : ℕ) : ℝ≥0∞ :=
  if ((u : ℝ) * R) / w ≤ (T : ℝ) then
    ENNReal.ofReal ((T : ℝ) ^ (-2 : ℝ))
  else 0

lemma inner_tsum_RST_le (E : ℕ) (hE : 1 ≤ E) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h u v w : ℕ) :
    b4 h u v w * (∑' rst : ℕ × ℕ × ℕ,
      bR E h u v rst.1 * bS v w rst.1 rst.2.1 * bT u w rst.1 rst.2.2) ≤
      ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β))) *
        (ENNReal.ofReal ((h : ℝ) ^ (-(2 - β))) *
          ENNReal.ofReal ((u : ℝ) ^ (-((3 - β) / 2))) *
          ENNReal.ofReal ((v : ℝ) ^ (-((3 - β) / 2))) *
          ENNReal.ofReal ((w : ℝ) ^ (-(2 - β)))) := by
  classical
  by_cases h4 : 1 ≤ h ∧ 1 ≤ u ∧ 1 ≤ v ∧ 1 ≤ w
  · obtain ⟨hh, hu, hv, hw⟩ := h4
    have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
    have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
    have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
    have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
    have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
    set θ : ℝ := (1 + β) / 2 with hθdef
    have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
    have hθ1 : θ ≤ 1 := by rw [hθdef]; linarith
    have hfactor_RST : (∑' rst : ℕ × ℕ × ℕ,
        bR E h u v rst.1 * bS v w rst.1 rst.2.1 * bT u w rst.1 rst.2.2) =
        ∑' R : ℕ, bR E h u v R * ((∑' S : ℕ, bS v w R S) * (∑' T : ℕ, bT u w R T)) := by
      have e1 : (∑' rst : ℕ × ℕ × ℕ,
          bR E h u v rst.1 * bS v w rst.1 rst.2.1 * bT u w rst.1 rst.2.2) =
          ∑' rst : ℕ × (ℕ × ℕ), bR E h u v rst.1 * (bS v w rst.1 rst.2.1 * bT u w rst.1 rst.2.2) :=
        tsum_congr (fun rst => by ring)
      rw [e1, ENNReal.tsum_prod']
      refine tsum_congr (fun R => ?_)
      dsimp only
      rw [ENNReal.tsum_mul_left, _root_.Represented.tsum_mul_prod (bS v w R) (bT u w R)]
    have hR_step : ∀ R : ℕ,
        bR E h u v R * ((∑' S : ℕ, bS v w R S) * (∑' T : ℕ, bT u w R T)) ≤
          ENNReal.ofReal (4 * (u : ℝ) ^ (-θ) * (v : ℝ) ^ (-θ) * (w : ℝ) ^ (1 + β)) *
            (if (E : ℝ) / ((h : ℝ) * u * v) ≤ (R : ℝ) then
              ENNReal.ofReal ((R : ℝ) ^ (-(2 + β)))
            else 0) := by
      intro R
      simp only [bR]
      split_ifs with hER
      · have hMpos : 0 < (E : ℝ) / ((h : ℝ) * u * v) := by positivity
        have hR0 : 0 < (R : ℝ) := lt_of_lt_of_le hMpos hER
        have hS_le : (∑' S : ℕ, bS v w R S) ≤ ENNReal.ofReal (2 * ((v : ℝ) * R / w) ^ (-θ)) :=
          tsum_inv_sq_ge_le (by positivity) hθ0 hθ1
        have hT_le : (∑' T : ℕ, bT u w R T) ≤ ENNReal.ofReal (2 * ((u : ℝ) * R / w) ^ (-θ)) :=
          tsum_inv_sq_ge_le (by positivity) hθ0 hθ1
        calc ENNReal.ofReal ((R : ℝ) ^ (-1 : ℝ)) * ((∑' S : ℕ, bS v w R S) * (∑' T : ℕ, bT u w R T))
            ≤ ENNReal.ofReal ((R : ℝ) ^ (-1 : ℝ)) *
                (ENNReal.ofReal (2 * ((v : ℝ) * R / w) ^ (-θ)) *
                  ENNReal.ofReal (2 * ((u : ℝ) * R / w) ^ (-θ))) := by gcongr
          _ = ENNReal.ofReal (4 * (u : ℝ) ^ (-θ) * (v : ℝ) ^ (-θ) * (w : ℝ) ^ (1 + β)) *
                ENNReal.ofReal ((R : ℝ) ^ (-(2 + β))) := by
              rw [← ENNReal.ofReal_mul (by positivity),
                  ← ENNReal.ofReal_mul (by positivity),
                  ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [mul_div_rpow_neg hv0 hR0 hw0, mul_div_rpow_neg hu0 hR0 hw0]
              have hw_comb : (w : ℝ) ^ θ * (w : ℝ) ^ θ = (w : ℝ) ^ (1 + β) := by
                rw [← Real.rpow_add hw0]
                congr 1; rw [hθdef]; ring
              have hR_comb : (R : ℝ) ^ (-1 : ℝ) * (R : ℝ) ^ (-θ) * (R : ℝ) ^ (-θ) = (R : ℝ) ^ (-(2 + β)) := by
                rw [← Real.rpow_add hR0, ← Real.rpow_add hR0]
                congr 1; rw [hθdef]; ring
              calc (R : ℝ) ^ (-1 : ℝ) *
                    (2 * ((v : ℝ) ^ (-θ) * (R : ℝ) ^ (-θ) * (w : ℝ) ^ θ) *
                      (2 * ((u : ℝ) ^ (-θ) * (R : ℝ) ^ (-θ) * (w : ℝ) ^ θ)))
                  = 4 * (u : ℝ) ^ (-θ) * (v : ℝ) ^ (-θ) * ((w : ℝ) ^ θ * (w : ℝ) ^ θ) *
                      ((R : ℝ) ^ (-1 : ℝ) * (R : ℝ) ^ (-θ) * (R : ℝ) ^ (-θ)) := by ring
                _ = 4 * (u : ℝ) ^ (-θ) * (v : ℝ) ^ (-θ) * (w : ℝ) ^ (1 + β) * (R : ℝ) ^ (-(2 + β)) := by
                    rw [hw_comb, hR_comb]
      · simp
    have hR_sum : (∑' R : ℕ, bR E h u v R * ((∑' S : ℕ, bS v w R S) * (∑' T : ℕ, bT u w R T))) ≤
        ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β)) * (h : ℝ) ^ (1 + β) *
          (u : ℝ) ^ θ * (v : ℝ) ^ θ * (w : ℝ) ^ (1 + β)) := by
      have hM_le := tsum_rpow_two_add_beta_ge_le (M := (E : ℝ) / ((h : ℝ) * u * v)) (by positivity) hβ0
      calc (∑' R : ℕ, bR E h u v R * ((∑' S : ℕ, bS v w R S) * (∑' T : ℕ, bT u w R T)))
          ≤ ∑' R : ℕ, ENNReal.ofReal (4 * (u : ℝ) ^ (-θ) * (v : ℝ) ^ (-θ) * (w : ℝ) ^ (1 + β)) *
              (if (E : ℝ) / ((h : ℝ) * u * v) ≤ (R : ℝ) then
                ENNReal.ofReal ((R : ℝ) ^ (-(2 + β)))
              else 0) := ENNReal.tsum_le_tsum hR_step
        _ = ENNReal.ofReal (4 * (u : ℝ) ^ (-θ) * (v : ℝ) ^ (-θ) * (w : ℝ) ^ (1 + β)) *
              (∑' R : ℕ, if (E : ℝ) / ((h : ℝ) * u * v) ≤ (R : ℝ) then
                ENNReal.ofReal ((R : ℝ) ^ (-(2 + β)))
              else 0) := ENNReal.tsum_mul_left
        _ ≤ ENNReal.ofReal (4 * (u : ℝ) ^ (-θ) * (v : ℝ) ^ (-θ) * (w : ℝ) ^ (1 + β)) *
              ENNReal.ofReal (2 * ((E : ℝ) / ((h : ℝ) * u * v)) ^ (-(1 + β))) := by gcongr
        _ = ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β)) * (h : ℝ) ^ (1 + β) *
              (u : ℝ) ^ θ * (v : ℝ) ^ θ * (w : ℝ) ^ (1 + β)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [div_mul_mul_rpow_neg hE0 hh0 hu0 hv0]
            have hu_comb : (u : ℝ) ^ (-θ) * (u : ℝ) ^ (1 + β) = (u : ℝ) ^ θ := by
              rw [← Real.rpow_add hu0]; congr 1; rw [hθdef]; ring
            have hv_comb : (v : ℝ) ^ (-θ) * (v : ℝ) ^ (1 + β) = (v : ℝ) ^ θ := by
              rw [← Real.rpow_add hv0]; congr 1; rw [hθdef]; ring
            calc 4 * (u : ℝ) ^ (-θ) * (v : ℝ) ^ (-θ) * (w : ℝ) ^ (1 + β) *
                  (2 * ((E : ℝ) ^ (-(1 + β)) * (h : ℝ) ^ (1 + β) * (u : ℝ) ^ (1 + β) * (v : ℝ) ^ (1 + β)))
                = 8 * (E : ℝ) ^ (-(1 + β)) * (h : ℝ) ^ (1 + β) *
                    ((u : ℝ) ^ (-θ) * (u : ℝ) ^ (1 + β)) *
                    ((v : ℝ) ^ (-θ) * (v : ℝ) ^ (1 + β)) * (w : ℝ) ^ (1 + β) := by ring
              _ = 8 * (E : ℝ) ^ (-(1 + β)) * (h : ℝ) ^ (1 + β) *
                    (u : ℝ) ^ θ * (v : ℝ) ^ θ * (w : ℝ) ^ (1 + β) := by rw [hu_comb, hv_comb]
    rw [hfactor_RST]
    have hb4 : b4 h u v w = ENNReal.ofReal
        ((h : ℝ) ^ (-3 : ℝ) * (u : ℝ) ^ (-2 : ℝ) * (v : ℝ) ^ (-2 : ℝ) * (w : ℝ) ^ (-3 : ℝ)) := by
      simp [b4, hh, hu, hv, hw]
    rw [hb4]
    calc ENNReal.ofReal ((h : ℝ) ^ (-3 : ℝ) * (u : ℝ) ^ (-2 : ℝ) * (v : ℝ) ^ (-2 : ℝ) * (w : ℝ) ^ (-3 : ℝ)) *
          (∑' R : ℕ, bR E h u v R * ((∑' S : ℕ, bS v w R S) * (∑' T : ℕ, bT u w R T)))
        ≤ ENNReal.ofReal ((h : ℝ) ^ (-3 : ℝ) * (u : ℝ) ^ (-2 : ℝ) * (v : ℝ) ^ (-2 : ℝ) * (w : ℝ) ^ (-3 : ℝ)) *
            ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β)) * (h : ℝ) ^ (1 + β) *
              (u : ℝ) ^ θ * (v : ℝ) ^ θ * (w : ℝ) ^ (1 + β)) := by gcongr
      _ = ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β))) *
            (ENNReal.ofReal ((h : ℝ) ^ (-(2 - β))) *
              ENNReal.ofReal ((u : ℝ) ^ (-((3 - β) / 2))) *
              ENNReal.ofReal ((v : ℝ) ^ (-((3 - β) / 2))) *
              ENNReal.ofReal ((w : ℝ) ^ (-(2 - β)))) := by
          repeat rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hh_comb : (h : ℝ) ^ (-3 : ℝ) * (h : ℝ) ^ (1 + β) = (h : ℝ) ^ (-(2 - β)) := by
            rw [← Real.rpow_add hh0]; congr 1; ring
          have hu_comb : (u : ℝ) ^ (-2 : ℝ) * (u : ℝ) ^ θ = (u : ℝ) ^ (-((3 - β) / 2)) := by
            rw [← Real.rpow_add hu0]; congr 1; rw [hθdef]; ring
          have hv_comb : (v : ℝ) ^ (-2 : ℝ) * (v : ℝ) ^ θ = (v : ℝ) ^ (-((3 - β) / 2)) := by
            rw [← Real.rpow_add hv0]; congr 1; rw [hθdef]; ring
          have hw_comb : (w : ℝ) ^ (-3 : ℝ) * (w : ℝ) ^ (1 + β) = (w : ℝ) ^ (-(2 - β)) := by
            rw [← Real.rpow_add hw0]; congr 1; ring
          calc (h : ℝ) ^ (-3 : ℝ) * (u : ℝ) ^ (-2 : ℝ) * (v : ℝ) ^ (-2 : ℝ) * (w : ℝ) ^ (-3 : ℝ) *
                (8 * (E : ℝ) ^ (-(1 + β)) * (h : ℝ) ^ (1 + β) * (u : ℝ) ^ θ * (v : ℝ) ^ θ * (w : ℝ) ^ (1 + β))
              = 8 * (E : ℝ) ^ (-(1 + β)) *
                  (((h : ℝ) ^ (-3 : ℝ) * (h : ℝ) ^ (1 + β)) *
                    ((u : ℝ) ^ (-2 : ℝ) * (u : ℝ) ^ θ) *
                    ((v : ℝ) ^ (-2 : ℝ) * (v : ℝ) ^ θ) *
                    ((w : ℝ) ^ (-3 : ℝ) * (w : ℝ) ^ (1 + β))) := by ring
            _ = 8 * (E : ℝ) ^ (-(1 + β)) *
                  ((h : ℝ) ^ (-(2 - β)) * (u : ℝ) ^ (-((3 - β) / 2)) *
                    (v : ℝ) ^ (-((3 - β) / 2)) * (w : ℝ) ^ (-(2 - β))) := by
                rw [hh_comb, hu_comb, hv_comb, hw_comb]
  · have hb4 : b4 h u v w = 0 := by simp [b4, h4]
    rw [hb4, zero_mul]
    exact bot_le

def equiv43 : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) ≃ ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ where
  toFun x := (x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, x.2.1, x.2.2.1, x.2.2.2)
  invFun d := ((d.1, d.2.1, d.2.2.1, d.2.2.2.1), (d.2.2.2.2.1, d.2.2.2.2.2.1, d.2.2.2.2.2.2))
  left_inv x := by rcases x with ⟨⟨h, u, v, w⟩, ⟨R, S, T⟩⟩; rfl
  right_inv d := by rcases d with ⟨h, u, v, w, R, S, T⟩; rfl

lemma decomp_inv_eq_rpow {e r s h u v w R S T : ℕ}
    (hh : 1 ≤ h) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hT : 1 ≤ T)
    (hsid : r = h * u * w * S) (htid : s = h * v * w * T)
    (hlcm : h * u * v * w * R * S * T = Nat.lcm e (Nat.lcm r s)) :
    (1 : ℝ) / ((r * s * Nat.lcm e (Nat.lcm r s) : ℕ) : ℝ) =
      ((h : ℝ) ^ (-3 : ℝ) * (u : ℝ) ^ (-2 : ℝ) * (v : ℝ) ^ (-2 : ℝ) * (w : ℝ) ^ (-3 : ℝ)) *
        ((R : ℝ) ^ (-1 : ℝ) * (S : ℝ) ^ (-2 : ℝ) * (T : ℝ) ^ (-2 : ℝ)) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hS0 : (0 : ℝ) < S := by exact_mod_cast hS
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hdenom : ((r * s * Nat.lcm e (Nat.lcm r s) : ℕ) : ℝ) =
      (h : ℝ) ^ 3 * (u : ℝ) ^ 2 * (v : ℝ) ^ 2 * (w : ℝ) ^ 3 * (R : ℝ) * (S : ℝ) ^ 2 * (T : ℝ) ^ 2 := by
    have hrR : (r : ℝ) = (h : ℝ) * u * w * S := by exact_mod_cast hsid
    have hsR : (s : ℝ) = (h : ℝ) * v * w * T := by exact_mod_cast htid
    have hlR : (Nat.lcm e (Nat.lcm r s) : ℝ) = (h : ℝ) * u * v * w * R * S * T := by
      exact_mod_cast hlcm.symm
    push_cast
    rw [hrR, hsR, hlR]
    ring
  rw [hdenom]
  have hrpow3 : ∀ x : ℝ, 0 ≤ x → x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx, Real.rpow_ofNat]
  have hrpow2 : ∀ x : ℝ, 0 ≤ x → x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx, Real.rpow_ofNat]
  rw [hrpow3 _ hh0.le, hrpow2 _ hu0.le, hrpow2 _ hv0.le, hrpow3 _ hw0.le,
      Real.rpow_neg_one, hrpow2 _ hS0.le, hrpow2 _ hT0.le]
  ring

theorem U_le_ennreal_beta_sharp (E : ℕ) (hE : 1 ≤ E) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    _root_.Erdos1054.SecondMoment.U E ≤ ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β))) *
      (_root_.Represented.Sp (2 - β) *
        _root_.Represented.Sp ((3 - β) / 2) *
        _root_.Represented.Sp ((3 - β) / 2) *
        _root_.Represented.Sp (2 - β)) := by
  classical
  set g₁ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (-(2 - β))) with hg1
  set g₂ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (-((3 - β) / 2))) with hg2
  have hS1 : (∑' n, g₁ n) = _root_.Represented.Sp (2 - β) := rfl
  have hS2 : (∑' n, g₂ n) = _root_.Represented.Sp ((3 - β) / 2) := rfl
  set b : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℝ≥0∞ := fun d =>
    b4 d.1 d.2.1 d.2.2.1 d.2.2.2.1 *
      (bR E d.1 d.2.1 d.2.2.1 d.2.2.2.2.1 *
        bS d.2.2.1 d.2.2.2.1 d.2.2.2.2.1 d.2.2.2.2.2.1 *
        bT d.2.1 d.2.2.2.1 d.2.2.2.2.1 d.2.2.2.2.2.2) with hb
  set Sset : Set (ℕ × ℕ × ℕ) := {p | E < p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2} with hSset
  set fS : ℕ × ℕ × ℕ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (1 / ((p.2.1 * p.2.2 * Nat.lcm p.1 (Nat.lcm p.2.1 p.2.2) : ℕ) : ℝ))
    with hfS
  have hUeq : _root_.Erdos1054.SecondMoment.U E = ∑' p : Sset, fS p := by
    have h1 : _root_.Erdos1054.SecondMoment.U E = ∑' x : ℕ × ℕ × ℕ, Sset.indicator fS x := by
      rw [_root_.Erdos1054.SecondMoment.U]
      refine tsum_congr (fun p => ?_)
      rw [Set.indicator_apply]
      simp only [hSset, hfS, Set.mem_ofPred_eq]
    rw [h1]; exact (tsum_subtype Sset fS).symm
  set F : Sset → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
    fun p => _root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2 with hF
  have hone : ∀ p : Sset, 1 ≤ p.1.1 ∧ 1 ≤ p.1.2.1 ∧ 1 ≤ p.1.2.2 := by
    rintro p
    have hp := p.2
    simp only [hSset, Set.mem_ofPred_eq] at hp
    omega
  have hFinj : Function.Injective F := by
    intro a c hac
    obtain ⟨har, has, hat⟩ := hone a
    obtain ⟨hcr, hcs, hct⟩ := hone c
    have spa := _root_.Represented.decomp_spec (r := a.1.1) (s := a.1.2.1) (t := a.1.2.2) har has hat
    have spc := _root_.Represented.decomp_spec (r := c.1.1) (s := c.1.2.1) (t := c.1.2.2) hcr hcs hct
    simp only at spa spc
    obtain ⟨_, _, _, _, _, _, _, hra, hsa, hta, _⟩ := spa
    obtain ⟨_, _, _, _, _, _, _, hrc, hsc, htc, _⟩ := spc
    simp only [hF] at hac
    apply Subtype.ext
    apply Prod.ext
    · rw [hra, hrc, hac]
    apply Prod.ext
    · rw [hsa, hsc, hac]
    · rw [hta, htc, hac]
  have hpt : ∀ p : Sset, fS p ≤ b (F p) := by
    rintro p
    have hp := p.2
    simp only [hSset, Set.mem_ofPred_eq] at hp
    obtain ⟨hpE, hps, hpt'⟩ := hp
    have hpe1 : 1 ≤ p.1.1 := by omega
    set d := _root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2 with hd
    have sp := _root_.Represented.decomp_spec (r := p.1.1) (s := p.1.2.1) (t := p.1.2.2)
      hpe1 (by omega) (by omega)
    simp only [← hd] at sp
    obtain ⟨hh, hu, hv, hw, hRR, hSS, hTT, hrid, hsid, htid, hlcm⟩ := sp
    have hh0 : (0 : ℝ) < d.1 := by exact_mod_cast hh
    have hu0 : (0 : ℝ) < d.2.1 := by exact_mod_cast hu
    have hv0 : (0 : ℝ) < d.2.2.1 := by exact_mod_cast hv
    have hw0 : (0 : ℝ) < d.2.2.2.1 := by exact_mod_cast hw
    have hER : (E : ℝ) / ((d.1 : ℝ) * d.2.1 * d.2.2.1) ≤ (d.2.2.2.2.1 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : E ≤ d.2.2.2.2.1 * (d.1 * d.2.1 * d.2.2.1) := by
        calc E ≤ p.1.1 := hpE.le
          _ = d.1 * d.2.1 * d.2.2.1 * d.2.2.2.2.1 := hrid
          _ = d.2.2.2.2.1 * (d.1 * d.2.1 * d.2.2.1) := by ring
      exact_mod_cast h1
    have hvS : ((d.2.2.1 : ℝ) * d.2.2.2.2.1) / d.2.2.2.1 ≤ (d.2.2.2.2.2.1 : ℝ) := by
      rw [div_le_iff₀ hw0]
      have h1 : (d.1 * d.2.1) * (d.2.2.1 * d.2.2.2.2.1) ≤
          (d.1 * d.2.1) * (d.2.2.2.2.2.1 * d.2.2.2.1) := by
        calc (d.1 * d.2.1) * (d.2.2.1 * d.2.2.2.2.1)
            = d.1 * d.2.1 * d.2.2.1 * d.2.2.2.2.1 := by ring
          _ = p.1.1 := hrid.symm
          _ ≤ p.1.2.1 := hps
          _ = d.1 * d.2.1 * d.2.2.2.1 * d.2.2.2.2.2.1 := hsid
          _ = (d.1 * d.2.1) * (d.2.2.2.2.2.1 * d.2.2.2.1) := by ring
      have h2 : d.2.2.1 * d.2.2.2.2.1 ≤ d.2.2.2.2.2.1 * d.2.2.2.1 :=
        Nat.le_of_mul_le_mul_left h1 (by positivity)
      exact_mod_cast h2
    have huT : ((d.2.1 : ℝ) * d.2.2.2.2.1) / d.2.2.2.1 ≤ (d.2.2.2.2.2.2 : ℝ) := by
      rw [div_le_iff₀ hw0]
      have h1 : (d.1 * d.2.2.1) * (d.2.1 * d.2.2.2.2.1) ≤
          (d.1 * d.2.2.1) * (d.2.2.2.2.2.2 * d.2.2.2.1) := by
        calc (d.1 * d.2.2.1) * (d.2.1 * d.2.2.2.2.1)
            = d.1 * d.2.1 * d.2.2.1 * d.2.2.2.2.1 := by ring
          _ = p.1.1 := hrid.symm
          _ ≤ p.1.2.2 := hpt'
          _ = d.1 * d.2.2.1 * d.2.2.2.1 * d.2.2.2.2.2.2 := htid
          _ = (d.1 * d.2.2.1) * (d.2.2.2.2.2.2 * d.2.2.2.1) := by ring
      have h2 : d.2.1 * d.2.2.2.2.1 ≤ d.2.2.2.2.2.2 * d.2.2.2.1 :=
        Nat.le_of_mul_le_mul_left h1 (by positivity)
      exact_mod_cast h2
    have hid := decomp_inv_eq_rpow hh hu hv hw hRR hSS hTT hsid htid hlcm
    refine le_of_eq ?_
    simp only [hfS, hF, hb, ← hd, b4, bR, bS, bT, hh, hu, hv, hw, hER, hvS, huT, and_self, ite_true]
    rw [hid, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [hUeq]
  calc (∑' p : Sset, fS p) ≤ ∑' p : Sset, b (F p) := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' d, b d := ENNReal.tsum_comp_le_tsum_of_injective hFinj b
    _ = ∑' x : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ), b (equiv43 x) := (equiv43.tsum_eq b).symm
    _ = ∑' q : ℕ × ℕ × ℕ × ℕ, ∑' rst : ℕ × ℕ × ℕ, b (equiv43 (q, rst)) := ENNReal.tsum_prod'
    _ = ∑' q : ℕ × ℕ × ℕ × ℕ,
          b4 q.1 q.2.1 q.2.2.1 q.2.2.2 *
            (∑' rst : ℕ × ℕ × ℕ,
              bR E q.1 q.2.1 q.2.2.1 rst.1 *
                bS q.2.2.1 q.2.2.2 rst.1 rst.2.1 *
                bT q.2.1 q.2.2.2 rst.1 rst.2.2) := by
        refine tsum_congr (fun q => ?_)
        rw [← ENNReal.tsum_mul_left]
        rfl
    _ ≤ ∑' q : ℕ × ℕ × ℕ × ℕ,
          ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β))) *
            (g₁ q.1 * g₂ q.2.1 * g₂ q.2.2.1 * g₁ q.2.2.2) :=
        ENNReal.tsum_le_tsum (fun q => inner_tsum_RST_le E hE hβ0 hβ1 q.1 q.2.1 q.2.2.1 q.2.2.2)
    _ = ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β))) *
          (∑' q : ℕ × ℕ × ℕ × ℕ, g₁ q.1 * g₂ q.2.1 * g₂ q.2.2.1 * g₁ q.2.2.2) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (8 * (E : ℝ) ^ (-(1 + β))) *
          (_root_.Represented.Sp (2 - β) *
            _root_.Represented.Sp ((3 - β) / 2) *
            _root_.Represented.Sp ((3 - β) / 2) *
            _root_.Represented.Sp (2 - β)) := by
        rw [tsum4 g₁ g₂, hS1, hS2]
        ring

theorem U_toReal_le_beta_sharp (E : ℕ) (hE : 1 ≤ E) {W : ℝ} (hW : 1 ≤ W) :
    (_root_.Erdos1054.SecondMoment.U E).toReal ≤
      8192 * W ^ 4 * (E : ℝ) ^ (-(2 - 1 / (2 * W))) := by
  have hWpos : 0 < W := by linarith
  set β : ℝ := 1 - 1 / (2 * W) with hβdef
  have h2W : 2 ≤ 2 * W := by linarith
  have hdiv : 1 / (2 * W) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hdiv_pos : 0 < 1 / (2 * W) := by positivity
  have hβ0 : 0 ≤ β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hp1_gt1 : 1 < 2 - β := by linarith
  have hp1_le2 : 2 - β ≤ 2 := by linarith
  have hp2_gt1 : 1 < (3 - β) / 2 := by linarith
  have hp2_le2 : (3 - β) / 2 ≤ 2 := by linarith
  set Cen : ℝ≥0∞ := _root_.Represented.Sp (2 - β)
      * _root_.Represented.Sp ((3 - β) / 2)
      * _root_.Represented.Sp ((3 - β) / 2)
      * _root_.Represented.Sp (2 - β) with hCen
  have hCtop : Cen ≠ ⊤ := by
    rw [hCen]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_) ?_
    · exact _root_.Represented.Sp_ne_top hp1_gt1
    · exact _root_.Represented.Sp_ne_top hp2_gt1
    · exact _root_.Represented.Sp_ne_top hp2_gt1
    · exact _root_.Represented.Sp_ne_top hp1_gt1
  have hchain := U_le_ennreal_beta_sharp E hE hβ0 hβ1.le
  rw [← hCen] at hchain
  have htoReal : (_root_.Erdos1054.SecondMoment.U E).toReal ≤
      8 * (E : ℝ) ^ (-(1 + β)) * Cen.toReal := by
    refine le_trans (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCtop) hchain) ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hSp1 : (_root_.Represented.Sp (2 - β)).toReal ≤ 4 * W := by
    refine le_trans (_root_.Erdos1054.SecondMoment.Sp_toReal_le hp1_gt1 hp1_le2) (le_of_eq ?_)
    rw [hβdef]
    field_simp
    ring
  have hSp2 : (_root_.Represented.Sp ((3 - β) / 2)).toReal ≤ 8 * W := by
    refine le_trans (_root_.Erdos1054.SecondMoment.Sp_toReal_le hp2_gt1 hp2_le2) (le_of_eq ?_)
    rw [hβdef]
    field_simp
    ring
  have hCen_le : Cen.toReal ≤ 1024 * W ^ 4 := by
    rw [hCen]
    repeat rw [ENNReal.toReal_mul]
    have h1 : 0 ≤ (_root_.Represented.Sp (2 - β)).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ (_root_.Represented.Sp ((3 - β) / 2)).toReal := ENNReal.toReal_nonneg
    calc (_root_.Represented.Sp (2 - β)).toReal
          * (_root_.Represented.Sp ((3 - β) / 2)).toReal
          * (_root_.Represented.Sp ((3 - β) / 2)).toReal
          * (_root_.Represented.Sp (2 - β)).toReal
        ≤ (4 * W) * (8 * W) * (8 * W) * (4 * W) := by gcongr
      _ = 1024 * W ^ 4 := by ring
  have hexp : -(1 + β) = -(2 - 1 / (2 * W)) := by rw [hβdef]; ring
  rw [hexp] at htoReal
  calc (_root_.Erdos1054.SecondMoment.U E).toReal
      ≤ 8 * (E : ℝ) ^ (-(2 - 1 / (2 * W))) * Cen.toReal := htoReal
    _ ≤ 8 * (E : ℝ) ^ (-(2 - 1 / (2 * W))) * (1024 * W ^ 4) := by gcongr
    _ = 8192 * W ^ 4 * (E : ℝ) ^ (-(2 - 1 / (2 * W))) := by ring

theorem optimize_second_moment_log_four {c₁ C₀ : ℝ} (hc₁ : 0 < c₁) (_hC₀ : 0 < C₀)
    (P : ℝ → ℕ → Prop)
    (hbound : ∀ A : ℝ, 1 ≤ A → ∀ E : ℕ, 2 ≤ E →
      c₁ / (E : ℝ) - C₀ * A ^ 3 * (1 + Real.log A) ^ 4 * (E : ℝ) ^ (-(2 - 1 / (2 * (1 + Real.log A)))) ≤
        _root_.Represented.lowerDensity (P A)) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 1 ≤ A →
      c / (A ^ 3 * (1 + Real.log A) ^ 4) ≤ _root_.Represented.lowerDensity (P A) := by
  obtain ⟨M, hMlarge⟩ := exists_nat_gt (max 1 (4 * C₀ * Real.exp 6 / c₁))
  have hMone : (1 : ℝ) < M :=
    lt_of_le_of_lt (le_max_left 1 (4 * C₀ * Real.exp 6 / c₁)) hMlarge
  have hMpos : (0 : ℝ) < M := by linarith
  have hMnat : 2 ≤ M := by exact_mod_cast hMone
  have hMchoice : 4 * C₀ * Real.exp 6 ≤ c₁ * (M : ℝ) := by
    have hquot : 4 * C₀ * Real.exp 6 / c₁ < (M : ℝ) :=
      lt_of_le_of_lt (le_max_right 1 (4 * C₀ * Real.exp 6 / c₁)) hMlarge
    have hmul := (div_lt_iff₀ hc₁).mp hquot
    nlinarith
  refine ⟨c₁ / (4 * (M : ℝ) ^ 2), by positivity, ?_⟩
  intro A hA
  have hApos : 0 < A := by linarith
  let W : ℝ := 1 + Real.log A
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hWone : 1 ≤ W := by dsimp [W]; linarith
  have hWpos : 0 < W := by linarith
  let Q : ℝ := A ^ 3 * W ^ 4
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    calc (1 : ℝ) = 1 ^ 3 * 1 ^ 4 := by norm_num
      _ ≤ A ^ 3 * W ^ 4 := by gcongr
  have hQpos : 0 < Q := by linarith
  let B : ℕ := ⌈Q⌉₊
  let E : ℕ := M ^ 2 * B
  have hQB : Q ≤ (B : ℝ) := Nat.le_ceil Q
  have hBtwo : (B : ℝ) ≤ 2 * Q := by
    have hceil : (⌈Q⌉₊ : ℝ) < Q + 1 := Nat.ceil_lt_add_one hQpos.le
    dsimp [B]; linarith
  have hBnat : 1 ≤ B := by
    have : (1 : ℝ) ≤ (B : ℝ) := hQone.trans hQB
    exact_mod_cast this
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hE : 2 ≤ E := by dsimp [E]; nlinarith
  have hEpos : (0 : ℝ) < E := by exact_mod_cast (show 0 < E by omega)
  have hEcast : (E : ℝ) = (M : ℝ) ^ 2 * (B : ℝ) := by simp [E]
  have hEupper : (E : ℝ) ≤ 2 * (M : ℝ) ^ 2 * Q := by
    rw [hEcast]
    calc (M : ℝ) ^ 2 * (B : ℝ) ≤ (M : ℝ) ^ 2 * (2 * Q) := by gcongr
      _ = 2 * (M : ℝ) ^ 2 * Q := by ring
  have hElower : (M : ℝ) ^ 2 * Q ≤ (E : ℝ) := by
    rw [hEcast]; gcongr
  have h2Wpos : 0 < 2 * W := by positivity
  have hinv_le : 1 / (2 * W) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ h2Wpos (by norm_num)]; linarith
  have hM_rpow : ((M : ℝ) ^ 2) ^ (1 / (2 * W)) ≤ (M : ℝ) := by
    calc ((M : ℝ) ^ 2) ^ (1 / (2 * W))
        ≤ ((M : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hMone.le) hinv_le
      _ = (M : ℝ) := by
          rw [← Real.rpow_natCast (M : ℝ) 2, ← Real.rpow_mul hMpos.le]
          norm_num [Real.rpow_one]
  have hB_rpow : (B : ℝ) ^ (1 / (2 * W)) ≤ 2 * Real.exp 6 := by
    have hBlog_le : Real.log (B : ℝ) ≤ Real.log 2 + 3 * Real.log A + 4 * Real.log W := by
      have h1 : Real.log (B : ℝ) ≤ Real.log (2 * Q) :=
        Real.log_le_log hBpos hBtwo
      have h2 : Real.log (2 * Q) = Real.log 2 + 3 * Real.log A + 4 * Real.log W := by
        dsimp [Q]
        rw [Real.log_mul (by norm_num) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_pow, Real.log_pow]
        norm_num
        ring
      linarith
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlogW : Real.log W ≤ W := by
      have := Real.log_le_sub_one_of_pos hWpos; linarith
    have hdiv_le : Real.log (B : ℝ) * (1 / (2 * W)) ≤ Real.log 2 + 6 := by
      rw [mul_one_div, div_le_iff₀ h2Wpos]
      have hlogA_le : Real.log A ≤ W := by dsimp [W]; linarith
      have hlog2_nn : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      nlinarith
    rw [Real.rpow_def_of_pos hBpos]
    calc Real.exp (Real.log (B : ℝ) * (1 / (2 * W)))
        ≤ Real.exp (Real.log 2 + 6) := Real.exp_le_exp.mpr hdiv_le
      _ = 2 * Real.exp 6 := by rw [Real.exp_add, Real.exp_log (by norm_num)]
  have hE_rpow : (E : ℝ) ^ (1 / (2 * W)) ≤ 2 * Real.exp 6 * (M : ℝ) := by
    rw [hEcast, Real.mul_rpow (by positivity) (by positivity)]
    calc ((M : ℝ) ^ 2) ^ (1 / (2 * W)) * (B : ℝ) ^ (1 / (2 * W))
        ≤ (M : ℝ) * (2 * Real.exp 6) := mul_le_mul hM_rpow hB_rpow (by positivity) hMpos.le
      _ = 2 * Real.exp 6 * (M : ℝ) := by ring
  have hrpow_split : (E : ℝ) ^ (-(2 - 1 / (2 * W))) = (E : ℝ) ^ (1 / (2 * W)) / (E : ℝ) ^ 2 := by
    rw [show -(2 - 1 / (2 * W)) = 1 / (2 * W) - 2 by ring,
        Real.rpow_sub hEpos, Real.rpow_two]
  have herror : C₀ * Q * (E : ℝ) ^ (-(2 - 1 / (2 * W))) ≤ c₁ / (2 * (E : ℝ)) := by
    rw [hrpow_split]
    have hrew : C₀ * Q * ((E : ℝ) ^ (1 / (2 * W)) / (E : ℝ) ^ 2) =
        (C₀ * Q * (E : ℝ) ^ (1 / (2 * W))) / (E : ℝ) ^ 2 := by ring
    rw [hrew]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc C₀ * Q * (E : ℝ) ^ (1 / (2 * W)) * (2 * (E : ℝ))
        ≤ C₀ * Q * (2 * Real.exp 6 * (M : ℝ)) * (2 * (E : ℝ)) := by gcongr
      _ = (4 * C₀ * Real.exp 6) * (M : ℝ) * Q * (E : ℝ) := by ring
      _ ≤ (c₁ * (M : ℝ)) * (M : ℝ) * Q * (E : ℝ) := by gcongr
      _ = c₁ * ((M : ℝ) ^ 2 * Q) * (E : ℝ) := by ring
      _ ≤ c₁ * (E : ℝ) * (E : ℝ) := by gcongr
      _ = c₁ * (E : ℝ) ^ 2 := by ring
  have hsurvive : c₁ / (2 * (E : ℝ)) ≤
      c₁ / (E : ℝ) - C₀ * A ^ 3 * (1 + Real.log A) ^ 4 * (E : ℝ) ^ (-(2 - 1 / (2 * (1 + Real.log A)))) := by
    have hdouble : c₁ / (E : ℝ) = 2 * (c₁ / (2 * (E : ℝ))) := by ring
    have heqQ : C₀ * A ^ 3 * (1 + Real.log A) ^ 4 * (E : ℝ) ^ (-(2 - 1 / (2 * (1 + Real.log A)))) =
        C₀ * Q * (E : ℝ) ^ (-(2 - 1 / (2 * W))) := by
      dsimp [Q, W]
      ring
    rw [heqQ]
    linarith
  have hfinal : c₁ / (4 * (M : ℝ) ^ 2) / (A ^ 3 * (1 + Real.log A) ^ 4) ≤ c₁ / (2 * (E : ℝ)) := by
    change c₁ / (4 * (M : ℝ) ^ 2) / Q ≤ c₁ / (2 * (E : ℝ))
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc c₁ * (2 * (E : ℝ))
        ≤ c₁ * (2 * (2 * (M : ℝ) ^ 2 * Q)) := by gcongr
      _ = c₁ * (4 * (M : ℝ) ^ 2 * Q) := by ring
  exact hfinal.trans (hsurvive.trans (hbound A hA E hE))

/-- Uniform two-parameter odd-tail bound with the sharp 4-factor second-moment estimate. -/
theorem explicit_sharp_second_moment_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (A : ℝ), 1 ≤ A → ∀ E : ℕ, 2 ≤ E →
        c₁ / (E : ℝ) -
            8192 * A ^ 3 * (1 + Real.log A) ^ 4 *
              (E : ℝ) ^ (-(2 - 1 / (2 * (1 + Real.log A)))) ≤
          _root_.Represented.lowerDensity
            (fun N : ℕ => Odd N ∧ N ∈ _root_.Represented.R ∧
              A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ)) := by
  obtain ⟨c₁, hc₁pos, hsift⟩ := _root_.Erdos1054.SecondMoment.sift_density_linear_lb
  refine ⟨c₁, hc₁pos, ?_⟩
  intro A hA E hE
  have hE1 : 1 ≤ E := by omega
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hW : 1 ≤ 1 + Real.log A := by linarith
  have hδ : c₁ / (E : ℝ) ≤ _root_.Represented.δ E := hsift E hE
  have hU := U_toReal_le_beta_sharp E hE1 hW
  have hH : ∀ X : ℕ,
      (_root_.Represented.countUpTo (_root_.Represented.Hset A E) X : ℝ) ≤
        (8192 * A ^ 3 * (1 + Real.log A) ^ 4 *
          (E : ℝ) ^ (-(2 - 1 / (2 * (1 + Real.log A))))) * X := by
    intro X
    refine le_trans (_root_.Erdos1054.SecondMoment.large_e_bound_U A hA E hE1 X) ?_
    calc A ^ 3 * (_root_.Erdos1054.SecondMoment.U E).toReal * X
        ≤ A ^ 3 * (8192 * (1 + Real.log A) ^ 4 *
            (E : ℝ) ^ (-(2 - 1 / (2 * (1 + Real.log A))))) * X := by gcongr
      _ = (8192 * A ^ 3 * (1 + Real.log A) ^ 4 *
            (E : ℝ) ^ (-(2 - 1 / (2 * (1 + Real.log A))))) * X := by ring
  have hmain := _root_.Erdos1054.SecondMoment.lowerDensity_odd_gt_of_Hset_bound A
    (8192 * A ^ 3 * (1 + Real.log A) ^ 4 *
      (E : ℝ) ^ (-(2 - 1 / (2 * (1 + Real.log A))))) E hE hH
  linarith

/-- Sharp second-moment logarithmic endpoint: `c / (A^3 * (1 + log A)^4)` lower density
on odd large-ratio witnesses. -/
theorem sharp_second_moment_logarithmic_endpoint_odd :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 1 ≤ A →
        c / (A ^ 3 * (1 + Real.log A) ^ 4) ≤
          _root_.Represented.lowerDensity
            (fun N : ℕ => Odd N ∧ N ∈ _root_.Represented.R ∧
              A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ)) := by
  obtain ⟨c₁, hc₁, hbound⟩ := explicit_sharp_second_moment_bound
  exact optimize_second_moment_log_four hc₁ (by norm_num : (0 : ℝ) < 8192)
    (fun A N => Odd N ∧ N ∈ _root_.Represented.R ∧
      A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ))
    hbound

/-- Sharp second-moment logarithmic endpoint inside any `HasOddDensityOne` set `S`:
`c / (A^3 * (1 + log A)^4)` lower density uniformly for all `S` and `A ≥ 1`. -/
theorem sharp_second_moment_logarithmic_endpoint_odd_in_odd_density_one :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Set ℕ), _root_.Erdos1054.OddTail.HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / (A ^ 3 * (1 + Real.log A) ^ 4) ≤
            _root_.Represented.lowerDensity
              (fun N : ℕ => N ∈ S ∧ Odd N ∧ N ∈ _root_.Represented.R ∧
                A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ)) := by
  obtain ⟨c, hc, hbound⟩ := sharp_second_moment_logarithmic_endpoint_odd
  refine ⟨c, hc, ?_⟩
  intro S hS A hA
  rw [_root_.Erdos1054.OddTail.lower_density_odd_inter_eq S hS
    (fun N : ℕ => N ∈ _root_.Represented.R ∧
      A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ))]
  exact hbound A hA

theorem log_four_isLittleO_rpow (ε : ℝ) (hε : 0 < ε) :
    (fun A : ℝ => (1 + Real.log A) ^ 4)
      =o[atTop] (fun A : ℝ => A ^ ε) := by
  have hlog :
      (fun A : ℝ => (Real.log A) ^ 4)
        =o[atTop] (fun A : ℝ => A ^ ε) := by
    convert (_root_.isLittleO_log_rpow_rpow_atTop (4 : ℝ) hε) using 1
    ext A
    norm_num [Real.rpow_natCast]
  have hbig :
      (fun A : ℝ => (1 + Real.log A) ^ 4)
        =O[atTop] (fun A : ℝ => (Real.log A) ^ 4) := by
    apply Asymptotics.IsBigO.of_bound 16
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with A hA
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    calc
      (1 + Real.log A) ^ 4 ≤ (2 * Real.log A) ^ 4 := by gcongr; linarith
      _ = 16 * (Real.log A) ^ 4 := by ring
  exact hbig.trans_isLittleO hlog

theorem log_four_div_rpow_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun A : ℝ => (1 + Real.log A) ^ 4 / A ^ ε)
      Filter.atTop (nhds 0) :=
  (log_four_isLittleO_rpow ε hε).tendsto_div_nhds_zero

lemma log_four_le_const_mul_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 1 ≤ A →
      (1 + Real.log A) ^ 4 ≤ K * A ^ ε := by
  refine ⟨(1 + 4 / ε) ^ 4, by positivity, fun A hA => ?_⟩
  have hApos : 0 < A := by linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have h1 : 1 ≤ A ^ (ε / 4) := Real.one_le_rpow hA (by positivity)
  have h2 : Real.log A ≤ (4 / ε) * A ^ (ε / 4) := by
    calc Real.log A ≤ A ^ (ε / 4) / (ε / 4) := Real.log_le_rpow_div hApos.le (by positivity)
      _ = (4 / ε) * A ^ (ε / 4) := by ring
  have h3 : 1 + Real.log A ≤ (1 + 4 / ε) * A ^ (ε / 4) := by nlinarith
  calc (1 + Real.log A) ^ 4
      ≤ ((1 + 4 / ε) * A ^ (ε / 4)) ^ 4 := by gcongr
    _ = (1 + 4 / ε) ^ 4 * (A ^ (ε / 4)) ^ 4 := by ring
    _ = (1 + 4 / ε) ^ 4 * A ^ ε := by
        congr 1
        rw [← Real.rpow_natCast (A ^ (ε / 4)) 4, ← Real.rpow_mul hApos.le]
        congr 1; push_cast; ring

/-- For every `ε > 0`, there is a constant `c > 0` such that the lower density of odd
large-ratio witnesses in any `HasOddDensityOne` set `S` is at least `c / A^(3 + ε)`. -/
theorem sharp_second_moment_three_plus_epsilon_odd_in_odd_density_one
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Set ℕ), _root_.Erdos1054.OddTail.HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / A ^ (3 + ε : ℝ) ≤
            _root_.Represented.lowerDensity
              (fun N : ℕ => N ∈ S ∧ Odd N ∧ N ∈ _root_.Represented.R ∧
                A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ)) := by
  obtain ⟨c₀, hc₀, hlog_bound⟩ := sharp_second_moment_logarithmic_endpoint_odd_in_odd_density_one
  obtain ⟨K, hK, hKbound⟩ := log_four_le_const_mul_rpow ε hε
  refine ⟨c₀ / K, by positivity, ?_⟩
  intro S hS A hA
  have hApos : 0 < A := by linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hAeps : 0 < A ^ ε := Real.rpow_pos_of_pos hApos ε
  have hA3eps : A ^ (3 + ε : ℝ) = A ^ 3 * A ^ ε := by
    rw [Real.rpow_add hApos, Real.rpow_ofNat]
  refine le_trans ?_ (hlog_bound S hS A hA)
  rw [hA3eps, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 := hKbound A hA
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ c₀ * A ^ 3)]

end Erdos1054.SharpSecondMoment
