module

public import GoldbachCircleBase
public import GoldbachSW3

@[expose] public section

set_option maxHeartbeats 4000000

namespace GoldbachChain


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


open MinorArc

set_option maxHeartbeats 1000000
open scoped ArithmeticFunction

-- ===== duplicated defs (verbatim from MinorArcExpSum.lean) =====



section CrossFileInputs

/-- Alias of the fully machine-verified `siegel_walfisz_proven` (SiegelWalfiszMaster gate,
    `#print axioms = [propext, Classical.choice, Quot.sound]`). -/
theorem siegel_walfisz (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log X ^ (B : ℝ) →
    ∀ a : ZMod q, IsUnit a →
    |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), if a = ((n : ZMod q)) then Λ n else 0)
      - X / q.totient| ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10)) :=
  siegel_walfisz_proven B hB



end CrossFileInputs

-- ===== Phase-C numerics =====

/-- `x ≤ exp(x/8)` once `256 ≤ x` (via `(x/16+1)² ≥ x²/256 ≥ x`). -/
lemma self_le_exp_eighth {x : ℝ} (hx : 256 ≤ x) : x ≤ Real.exp (x / 8) := by
  have h2 := Real.add_one_le_exp (x/16)
  have h1 : Real.exp (x/8) = Real.exp (x/16) * Real.exp (x/16) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (x/16 + 1) * (x/16 + 1) ≤ Real.exp (x/16) * Real.exp (x/16) := by
    have h4 : (0:ℝ) ≤ x/16 + 1 := by linarith
    exact mul_le_mul h2 h2 h4 (Real.exp_pos _).le
  rw [h1]
  nlinarith [h3, mul_nonneg (show (0:ℝ) ≤ x from by linarith)
    (show (0:ℝ) ≤ x - 256 from by linarith)]

open Finset in
set_option maxHeartbeats 4000000 in
/-- **Rated progression bound, unit residues** (brick C1a): uniformly for
    `q ≤ (log N)^B` and coprime `r < q`, every initial segment `t ≤ N` of the
    progression Λ-sum is within `C·N·exp(−c(log N)^{1/10})` of `t/φ(q)`.
    Route: `siegel_walfisz` at exponent `2B` (the window survives `t ≥ √N`,
    where `log t ≥ (log N)/2`) + √N head/tail split (the head is trivially
    `≤ 4√N·log N`, beaten by the exponential margin). -/
theorem rated_progression_bound (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B : ℝ) →
    ∀ r : ℕ, r < q → Nat.gcd r q = 1 →
    ∀ t : ℕ, t ≤ N →
    ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
      - (t : ℂ) * (1 / (q.totient : ℂ))‖
      ≤ C * N * Real.exp (-c * Real.log N ^ ((1:ℝ)/10)) := by
  obtain ⟨c, C, hc0, hC0, X₀, hSW⟩ := siegel_walfisz (2*B) (by linarith)
  refine ⟨c/2, C + 6, by positivity, by positivity, ?_⟩
  obtain ⟨Λ₂, hΛ₂def⟩ : ∃ x : ℝ, x = 256 + (4*c+1)^(10:ℕ) + 4 := ⟨_, rfl⟩
  have hΛ₂256 : 256 ≤ Λ₂ := by
    rw [hΛ₂def]
    have h1 : (0:ℝ) ≤ (4*c+1)^(10:ℕ) := by positivity
    linarith
  refine ⟨max (⌈Real.exp Λ₂⌉₊ + 2) (⌈(max X₀ 0 + 2)^(2:ℕ)⌉₊ + 2), ?_⟩
  intro N hN₀ q hq0 hqB r hrq hgcd t htN
  haveI : NeZero q := ⟨hq0.ne'⟩
  -- ===== scale facts =====
  have hNexp : ⌈Real.exp Λ₂⌉₊ + 2 ≤ N := le_trans (le_max_left _ _) hN₀
  have hNX₀ : ⌈(max X₀ 0 + 2)^(2:ℕ)⌉₊ + 2 ≤ N := le_trans (le_max_right _ _) hN₀
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have h1 : 1 ≤ N := by omega
    exact_mod_cast h1
  have hNR : Real.exp Λ₂ ≤ (N:ℝ) := by
    have h1 : (⌈Real.exp Λ₂⌉₊ : ℝ) ≤ (N:ℝ) := by
      have h2 : ⌈Real.exp Λ₂⌉₊ ≤ N := by omega
      exact_mod_cast h2
    linarith [Nat.le_ceil (Real.exp Λ₂)]
  have hlogN : Λ₂ ≤ Real.log N := by
    calc Λ₂ = Real.log (Real.exp Λ₂) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) hNR
  have hlogN4 : (4:ℝ) ≤ Real.log N := by linarith
  have hlogN0 : (0:ℝ) < Real.log N := by linarith
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = Real.log N ^ ((1:ℝ)/10) := ⟨_, rfl⟩
  have hL0 : 0 < L := by
    rw [hLdef]
    exact Real.rpow_pos_of_pos hlogN0 _
  have hLpow : L ^ (10:ℕ) = Real.log N := by
    rw [hLdef, ← Real.rpow_natCast (Real.log N ^ ((1:ℝ)/10)) 10,
      ← Real.rpow_mul hlogN0.le]
    norm_num
  have hL256 : 256 ≤ L ^ (10:ℕ) := by rw [hLpow]; linarith
  have hL4c : 4*c + 1 ≤ L := by
    by_contra hcon
    push_neg at hcon
    have h1 : L ^ (10:ℕ) < (4*c+1) ^ (10:ℕ) :=
      pow_lt_pow_left₀ hcon hL0.le (by norm_num)
    have h2 : (0:ℝ) ≤ (4*c+1)^(10:ℕ) := by positivity
    rw [hLpow] at h1
    rw [hΛ₂def] at hlogN
    linarith
  have hL1 : 1 ≤ L := by
    have h1 : (0:ℝ) ≤ 4*c := by positivity
    linarith
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt N := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hN1
  have hsqrtX₀ : max X₀ 0 + 1 ≤ Real.sqrt N := by
    have h1 : ((max X₀ 0 + 2)^(2:ℕ) : ℝ) ≤ (N:ℝ) := by
      have h2 : (⌈(max X₀ 0 + 2)^(2:ℕ)⌉₊ : ℝ) ≤ (N:ℝ) := by
        have h3 : ⌈(max X₀ 0 + 2)^(2:ℕ)⌉₊ ≤ N := by omega
        exact_mod_cast h3
      linarith [Nat.le_ceil ((max X₀ 0 + 2)^(2:ℕ))]
    have h4 : (0:ℝ) ≤ max X₀ 0 + 2 := by
      have h5 := le_max_right X₀ (0:ℝ)
      linarith
    have h6 : max X₀ 0 + 2 ≤ Real.sqrt N := by
      rw [show max X₀ 0 + 2 = Real.sqrt ((max X₀ 0 + 2)^(2:ℕ)) from
        (Real.sqrt_sq h4).symm]
      exact Real.sqrt_le_sqrt h1
    linarith
  have hlogsqrt : Real.log (Real.sqrt N) = Real.log N / 2 :=
    Real.log_sqrt (by positivity)
  have hE0 : (0:ℝ) < Real.exp (-(c/2) * L) := Real.exp_pos _
  have hEbig : 1 ≤ (N:ℝ) * Real.exp (-(c/2) * L) := by
    have h1 : Real.exp ((c/2) * L) ≤ (N:ℝ) := by
      have h2 : (c/2) * L ≤ L ^ (10:ℕ) := by
        have h4 : c/2 ≤ L ^ (9:ℕ) := by
          have h5 : L ≤ L ^ (9:ℕ) := le_self_pow₀ hL1 (by norm_num)
          linarith
        have h3 : (c/2) * L ≤ (L^(9:ℕ)) * L :=
          mul_le_mul_of_nonneg_right h4 hL0.le
        have h6 : (L^(9:ℕ)) * L = L ^ (10:ℕ) := by ring
        linarith
      calc Real.exp ((c/2) * L) ≤ Real.exp (L ^ (10:ℕ)) := Real.exp_le_exp.mpr h2
        _ = (N:ℝ) := by rw [hLpow]; exact Real.exp_log (by linarith)
    calc (1:ℝ) = Real.exp ((c/2) * L) * Real.exp (-(c/2) * L) := by
          rw [← Real.exp_add]
          simp
      _ ≤ (N:ℝ) * Real.exp (-(c/2) * L) :=
          mul_le_mul_of_nonneg_right h1 hE0.le
  -- ===== split at √N =====
  rcases lt_or_ge ((t:ℝ) - 1) (Real.sqrt N) with hhead | htail
  · -- HEAD: trivial bound 4√N·log N
    have hsum_le : ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
        ≤ (t:ℝ) * Real.log N := by
      calc ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n
          ≤ ∑ n ∈ Finset.range t, Λ n := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro n _ _
            exact ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ ∑ _n ∈ Finset.range t, Real.log N := by
            apply Finset.sum_le_sum
            intro n hn
            rcases Nat.eq_zero_or_pos n with rfl | hn0
            · rw [show Λ 0 = 0 from ArithmeticFunction.map_zero]
              linarith
            · calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
                _ ≤ Real.log N := by
                    apply Real.log_le_log (by exact_mod_cast hn0)
                    rw [Finset.mem_range] at hn
                    have h1 : n ≤ N := by omega
                    exact_mod_cast h1
        _ = (t:ℝ) * Real.log N := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    have hsum_nn : (0:ℝ) ≤ ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n :=
      Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
    have hφ1 : (1:ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hcast : ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
        - (t : ℂ) * (1 / (q.totient : ℂ))‖
        = |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
            - (t:ℝ) * (1 / (q.totient : ℝ))| := by
      rw [show (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
          - (t : ℂ) * (1 / (q.totient : ℂ))
          = ((((∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - (t:ℝ) * (1 / (q.totient : ℝ)) : ℝ)) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hcast]
    have htR : (t:ℝ) ≤ Real.sqrt N + 1 := by linarith
    have habs : |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
        - (t:ℝ) * (1 / (q.totient : ℝ))| ≤ 4 * Real.sqrt N * Real.log N := by
      rw [abs_le]
      have h2 : (t:ℝ) ≤ 2 * Real.sqrt N := by linarith [hsqrt1]
      constructor
      · have h1 : (t:ℝ) * (1 / (q.totient : ℝ)) ≤ (t:ℝ) := by
          rw [mul_one_div]
          apply div_le_self (by positivity) hφ1
        nlinarith [hsqrt1, hlogN4]
      · have h3 : (t:ℝ) * Real.log N ≤ 2 * Real.sqrt N * Real.log N :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
        have h4 : (0:ℝ) ≤ (t:ℝ) * (1 / (q.totient : ℝ)) := by positivity
        linarith [hsum_le]
    refine habs.trans ?_
    have hkey : 4 * Real.log N * Real.exp ((c/2) * L) ≤ Real.sqrt N := by
      have h1 : Real.sqrt N = Real.exp (L ^ (10:ℕ) / 2) := by
        rw [hLpow, ← hlogsqrt]
        exact (Real.exp_log (by positivity)).symm
      have h4exp : (4:ℝ) ≤ Real.exp (L ^ (10:ℕ) / 8) := by
        have h2 : (4:ℝ) ≤ L ^ (10:ℕ) / 8 := by linarith
        have h3 := Real.add_one_le_exp (L ^ (10:ℕ) / 8)
        linarith
      have hlogexp : Real.log N ≤ Real.exp (L ^ (10:ℕ) / 8) := by
        rw [← hLpow]
        exact self_le_exp_eighth hL256
      have hcLexp : Real.exp ((c/2) * L) ≤ Real.exp (L ^ (10:ℕ) / 8) := by
        apply Real.exp_le_exp.mpr
        have h6 : L ≤ L ^ (9:ℕ) := le_self_pow₀ hL1 (by norm_num)
        have h5 : (c/2) * L ≤ (L^(9:ℕ)/8) * L := by
          apply mul_le_mul_of_nonneg_right ?_ hL0.le
          linarith [hL4c]
        have h7 : (L^(9:ℕ)/8) * L = L ^ (10:ℕ) / 8 := by ring
        linarith
      calc 4 * Real.log N * Real.exp ((c/2) * L)
          ≤ Real.exp (L ^ (10:ℕ) / 8) * Real.exp (L ^ (10:ℕ) / 8)
            * Real.exp (L ^ (10:ℕ) / 8) := by
            apply mul_le_mul ?_ hcLexp (Real.exp_pos _).le (by positivity)
            exact mul_le_mul h4exp hlogexp (by linarith) (Real.exp_pos _).le
        _ = Real.exp (3 * (L ^ (10:ℕ) / 8)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp (L ^ (10:ℕ) / 2) := by
            apply Real.exp_le_exp.mpr
            have h8 : (0:ℝ) ≤ L ^ (10:ℕ) := by positivity
            linarith
        _ = Real.sqrt N := h1.symm
    have hNsq : Real.sqrt N * Real.sqrt N = (N:ℝ) :=
      Real.mul_self_sqrt (by positivity)
    calc 4 * Real.sqrt N * Real.log N
        = (4 * Real.log N * Real.exp ((c/2) * L)) * Real.sqrt N
          * Real.exp (-(c/2) * L) := by
          rw [show (4 * Real.log N * Real.exp ((c/2) * L)) * Real.sqrt N
              * Real.exp (-(c/2) * L)
              = 4 * Real.log N * Real.sqrt N
                * (Real.exp ((c/2) * L) * Real.exp (-(c/2) * L)) from by ring,
            ← Real.exp_add]
          simp
          ring
      _ ≤ Real.sqrt N * Real.sqrt N * Real.exp (-(c/2) * L) := by
          apply mul_le_mul_of_nonneg_right ?_ hE0.le
          apply mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = (N:ℝ) * Real.exp (-(c/2) * L) := by rw [hNsq]
      _ ≤ (C + 6) * (N:ℝ) * Real.exp (-(c/2) * L) := by
          have h9 : (0:ℝ) ≤ (N:ℝ) * Real.exp (-(c/2) * L) := by positivity
          nlinarith
      _ = (C + 6) * (N:ℝ) * Real.exp (-(c/2) * Real.log N ^ ((1:ℝ)/10)) := by
          rw [hLdef]
  · -- TAIL: siegel_walfisz at X := t − 1
    have ht1 : 1 ≤ t := by
      by_contra hcon
      push_neg at hcon
      have h1 : t = 0 := by omega
      rw [h1] at htail
      simp only [Nat.cast_zero, zero_sub] at htail
      linarith [hsqrt1]
    have hXX₀ : X₀ ≤ (t:ℝ) - 1 := by
      have h1 := le_max_left X₀ (0:ℝ)
      linarith [hsqrtX₀, htail]
    have hlogt : Real.log N / 2 ≤ Real.log ((t:ℝ) - 1) := by
      rw [← hlogsqrt]
      apply Real.log_le_log (by linarith [hsqrt1]) htail
    have hqB2 : (q:ℝ) ≤ Real.log ((t:ℝ) - 1) ^ ((2*B : ℝ)) := by
      have h2 : (Real.log N / 2) ^ ((2*B : ℝ))
          = Real.log N ^ ((2*B:ℝ)) / 2 ^ ((2*B:ℝ)) :=
        Real.div_rpow (by linarith) (by norm_num) _
      have h1 : Real.log N ^ (B:ℝ) ≤ (Real.log N / 2) ^ ((2*B : ℝ)) := by
        rw [h2, le_div_iff₀ (by positivity)]
        have h3 : (2:ℝ) ^ ((2*B:ℝ)) ≤ Real.log N ^ (B:ℝ) := by
          have h31 : (2:ℝ) ^ ((2*B:ℝ)) = ((2:ℝ)^(2:ℕ)) ^ (B:ℝ) := by
            rw [← Real.rpow_natCast (2:ℝ) 2, ← Real.rpow_mul (by norm_num)]
            norm_num
          rw [h31, show ((2:ℝ)^(2:ℕ)) = (4:ℝ) from by norm_num]
          exact Real.rpow_le_rpow (by norm_num) hlogN4 (by linarith)
        have h4 : Real.log N ^ (B:ℝ) * Real.log N ^ (B:ℝ)
            = Real.log N ^ ((2*B:ℝ)) := by
          rw [← Real.rpow_add hlogN0]
          congr 1
          ring
        calc Real.log N ^ (B:ℝ) * 2 ^ ((2*B:ℝ))
            ≤ Real.log N ^ (B:ℝ) * Real.log N ^ (B:ℝ) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = Real.log N ^ ((2*B:ℝ)) := h4
      have h5 : (Real.log N / 2) ^ ((2*B : ℝ)) ≤ Real.log ((t:ℝ) - 1) ^ ((2*B : ℝ)) :=
        Real.rpow_le_rpow (by linarith) hlogt (by linarith)
      linarith [hqB]
    have hunit : IsUnit ((r : ZMod q)) := (ZMod.isUnit_iff_coprime r q).mpr hgcd
    have hSW' := hSW ((t:ℝ) - 1) hXX₀ q hqB2 ((r : ZMod q)) hunit
    have hXdef : ((t:ℝ) - 1) = (((t - 1 : ℕ)):ℝ) := by
      have h1 := Nat.cast_sub ht1 (R := ℝ)
      rw [h1]
      norm_num
    have hfloor : ⌊(t:ℝ) - 1⌋₊ + 1 = t := by
      rw [hXdef, Nat.floor_natCast]
      omega
    rw [hfloor] at hSW'
    have hbridge : (∑ n ∈ Finset.range t,
        if ((r : ZMod q)) = ((n : ZMod q)) then Λ n else 0)
        = ∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      have h1 : (((r : ZMod q)) = ((n : ZMod q))) ↔ (n % q = r) := by
        rw [ZMod.natCast_eq_natCast_iff]
        constructor
        · intro h2
          have h3 : n % q = r % q := (Nat.ModEq.symm h2)
          rwa [Nat.mod_eq_of_lt hrq] at h3
        · intro h2
          have h3 : n % q = r % q := by rw [Nat.mod_eq_of_lt hrq]; exact h2
          exact Nat.ModEq.symm h3
      simp only [h1]
    rw [hbridge] at hSW'
    have hcast : ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
        - (t : ℂ) * (1 / (q.totient : ℂ))‖
        = |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
            - (t:ℝ) * (1 / (q.totient : ℝ))| := by
      rw [show (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), ((Λ n : ℝ) : ℂ))
          - (t : ℂ) * (1 / (q.totient : ℂ))
          = ((((∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - (t:ℝ) * (1 / (q.totient : ℝ)) : ℝ)) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hcast]
    have hφ1 : (1:ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hoffby : |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
        - (t:ℝ) * (1 / (q.totient : ℝ))|
        ≤ |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
            - ((t:ℝ) - 1) / (q.totient : ℝ)| + 1 := by
      have h1 : |((t:ℝ) - 1) / (q.totient : ℝ) - (t:ℝ) * (1 / (q.totient : ℝ))|
          ≤ 1 := by
        have hφ0 : (q.totient : ℝ) ≠ 0 := by linarith
        rw [show ((t:ℝ) - 1) / (q.totient : ℝ) - (t:ℝ) * (1 / (q.totient : ℝ))
            = -(1 / (q.totient : ℝ)) from by field_simp; ring,
          abs_neg, abs_of_pos (by positivity), div_le_one (by linarith)]
        exact hφ1
      calc |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
          - (t:ℝ) * (1 / (q.totient : ℝ))|
          = |((∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - ((t:ℝ) - 1) / (q.totient : ℝ))
            + (((t:ℝ) - 1) / (q.totient : ℝ)
              - (t:ℝ) * (1 / (q.totient : ℝ)))| := by
            congr 1
            ring
        _ ≤ |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - ((t:ℝ) - 1) / (q.totient : ℝ)|
            + |((t:ℝ) - 1) / (q.totient : ℝ) - (t:ℝ) * (1 / (q.totient : ℝ))| :=
            abs_add_le _ _
        _ ≤ |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
              - ((t:ℝ) - 1) / (q.totient : ℝ)| + 1 := by linarith
    have hrate : Real.exp (-c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10))
        ≤ Real.exp (-(c/2) * L) := by
      apply Real.exp_le_exp.mpr
      have h1 : (Real.log N / 2) ^ ((1:ℝ)/10) ≤ Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10) :=
        Real.rpow_le_rpow (by linarith) hlogt (by norm_num)
      have h3 : (Real.log N / 2) ^ ((1:ℝ)/10)
          = Real.log N ^ ((1:ℝ)/10) * ((1:ℝ)/2) ^ ((1:ℝ)/10) := by
        rw [show Real.log N / 2 = Real.log N * ((1:ℝ)/2) from by ring,
          Real.mul_rpow (by linarith) (by norm_num)]
      have h5 : ((1:ℝ)/2) ≤ ((1:ℝ)/2) ^ ((1:ℝ)/10) := by
        nth_rewrite 1 [show ((1:ℝ)/2) = ((1:ℝ)/2) ^ ((1:ℝ)) from
          (Real.rpow_one _).symm]
        apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        norm_num
      have h2 : ((1:ℝ)/2) * Real.log N ^ ((1:ℝ)/10)
          ≤ (Real.log N / 2) ^ ((1:ℝ)/10) := by
        rw [h3]
        calc ((1:ℝ)/2) * Real.log N ^ ((1:ℝ)/10)
            ≤ ((1:ℝ)/2) ^ ((1:ℝ)/10) * Real.log N ^ ((1:ℝ)/10) :=
              mul_le_mul_of_nonneg_right h5 (by positivity)
          _ = Real.log N ^ ((1:ℝ)/10) * ((1:ℝ)/2) ^ ((1:ℝ)/10) := by ring
      have h6 : c * (((1:ℝ)/2) * Real.log N ^ ((1:ℝ)/10))
          ≤ c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10) := by
        apply mul_le_mul_of_nonneg_left ?_ hc0.le
        linarith
      rw [hLdef]
      nlinarith [h6]
    have hfin : C * ((t:ℝ) - 1) * Real.exp (-c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10))
        ≤ C * (N:ℝ) * Real.exp (-(c/2) * L) := by
      have h1 : (t:ℝ) - 1 ≤ (N:ℝ) := by
        have h2 : (t:ℝ) ≤ (N:ℝ) := by exact_mod_cast htN
        linarith
      calc C * ((t:ℝ) - 1) * Real.exp (-c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10))
          ≤ C * ((t:ℝ) - 1) * Real.exp (-(c/2) * L) := by
            apply mul_le_mul_of_nonneg_left hrate ?_
            have h4 : (0:ℝ) ≤ (t:ℝ) - 1 := by linarith [hsqrt1, htail]
            positivity
        _ ≤ C * (N:ℝ) * Real.exp (-(c/2) * L) := by
            apply mul_le_mul_of_nonneg_right ?_ hE0.le
            apply mul_le_mul_of_nonneg_left h1 hC0.le
    calc |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
        - (t:ℝ) * (1 / (q.totient : ℝ))|
        ≤ |(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), Λ n)
            - ((t:ℝ) - 1) / (q.totient : ℝ)| + 1 := hoffby
      _ ≤ C * ((t:ℝ) - 1) * Real.exp (-c * Real.log ((t:ℝ) - 1) ^ ((1:ℝ)/10)) + 1 := by
          linarith [hSW']
      _ ≤ C * (N:ℝ) * Real.exp (-(c/2) * L) + (N:ℝ) * Real.exp (-(c/2) * L) := by
          linarith [hfin, hEbig]
      _ ≤ (C + 6) * (N:ℝ) * Real.exp (-(c/2) * L) := by
          have h9 : (0:ℝ) ≤ (N:ℝ) * Real.exp (-(c/2) * L) := by positivity
          nlinarith
      _ = (C + 6) * (N:ℝ) * Real.exp (-(c/2) * Real.log N ^ ((1:ℝ)/10)) := by
          rw [hLdef]


end GoldbachChain
