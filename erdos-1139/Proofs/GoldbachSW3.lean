module

public import GoldbachSW2
public import PrimeNumberTheoremAnd.MediumPNT
public import PrimeNumberTheoremAnd.PerronFormula

@[expose] public section

set_option maxHeartbeats 4000000

section SWShims

open ArithmeticFunction Complex

/-- Shim 1: `perron_kernel_gtOne` — unfold `VerticalIntegral' = (1/(2πi))•(i•∫)` and cancel `I`. -/
theorem perron_kernel_gtOne (y : ℝ) (hy : 1 < y) (σ : ℝ) (hσ : 0 < σ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        ((y : ℂ) ^ ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))
      = 1 - 1 / (y : ℂ) := by
  have h := Perron.formulaGtOne (x := y) (σ := σ) hy hσ
  unfold VerticalIntegral' VerticalIntegral at h
  rw [smul_smul, smul_eq_mul] at h
  have hI : (1 / (2 * (Real.pi : ℂ) * I)) * I = 1 / (2 * (Real.pi : ℂ)) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [hI] at h
  exact h

/-- Shim 2: `perron_kernel_ltOne` — `VerticalIntegral (f y) σ = 0`, cancel the `I•`. -/
theorem perron_kernel_ltOne (y : ℝ) (hy0 : 0 < y) (hy : y < 1) (σ : ℝ) (hσ : 0 < σ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        ((y : ℂ) ^ ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))
      = 0 := by
  have h := Perron.formulaLtOne (x := y) (σ := σ) hy0 hy hσ
  unfold VerticalIntegral at h
  rw [smul_eq_mul] at h
  rcases mul_eq_zero.mp h with hI | hint
  · exact absurd hI I_ne_zero
  · rw [hint, mul_zero]

/-- Shim 3: `medium_PNT` — the isBigO form of `MediumPNT` made explicit for all `x ≥ 2`,
    with the compact window `[2, X₀]` absorbed into the constant (ψ is monotone, and the
    comparator is bounded below by `2·exp(−c·(log M)^{1/10})` there). -/
theorem medium_PNT : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) - x|
      ≤ C * x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [Filter.eventually_atTop] at hC
  obtain ⟨X₀, hX₀⟩ := hC
  set M : ℝ := max 2 X₀ with hMdef
  have hM2 : (2:ℝ) ≤ M := le_max_left _ _
  have hM0 : (0:ℝ) < M := by linarith
  -- comparator lower bound on [2, M]
  set m : ℝ := 2 * Real.exp (-c * Real.log M ^ ((1:ℝ)/10)) with hmdef
  have hm0 : 0 < m := by positivity
  -- ψ is monotone in x (sum of nonnegatives over a growing range)
  have hpsi_mono : ∀ x : ℝ, x ≤ M →
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) ≤ ∑ n ∈ Finset.range (⌊M⌋₊ + 1), Λ n := by
    intro x hx
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_range] at hk ⊢
      have := Nat.floor_le_floor hx
      omega
    · intro n _ _
      exact vonMangoldt_nonneg
  set K : ℝ := (∑ n ∈ Finset.range (⌊M⌋₊ + 1), Λ n) + M with hKdef
  have hK0 : 0 < K := by
    have h1 : (0:ℝ) ≤ ∑ n ∈ Finset.range (⌊M⌋₊ + 1), Λ n :=
      Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
    linarith
  refine ⟨c, max C 1 + K / m, hc, by positivity, ?_⟩
  intro x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hcomp0 : 0 < x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by positivity
  rcases le_total x M with hxM | hxM
  · -- compact window: |ψ − x| ≤ K and the comparator ≥ m·(x/x)… use m ≤ x·exp(−c logx^{1/10})
    have hψx : |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) - x| ≤ K := by
      have h1 : (0:ℝ) ≤ ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n :=
        Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
      have h2 := hpsi_mono x hxM
      rw [abs_le]
      constructor
      · have : x ≤ M := hxM
        nlinarith
      · nlinarith
    have hcomp_ge : m ≤ x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
      have hlog_le : Real.log x ≤ Real.log M := Real.log_le_log hx0 hxM
      have hlx0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
      have hrpow_le : Real.log x ^ ((1:ℝ)/10) ≤ Real.log M ^ ((1:ℝ)/10) :=
        Real.rpow_le_rpow hlx0 hlog_le (by norm_num)
      have hexp_le : Real.exp (-c * Real.log M ^ ((1:ℝ)/10))
          ≤ Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc m = 2 * Real.exp (-c * Real.log M ^ ((1:ℝ)/10)) := hmdef
        _ ≤ 2 * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
            apply mul_le_mul_of_nonneg_left hexp_le (by norm_num)
        _ ≤ x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
            apply mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    calc |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) - x| ≤ K := hψx
      _ = (K / m) * m := by field_simp
      _ ≤ (K / m) * (x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))) := by
          apply mul_le_mul_of_nonneg_left hcomp_ge (by positivity)
      _ ≤ (max C 1 + K / m) * (x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))) := by
          apply mul_le_mul_of_nonneg_right _ hcomp0.le
          have : (0:ℝ) ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
          linarith
      _ = (max C 1 + K / m) * x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by ring
  · -- asymptotic window: cite the isBigO bound
    have h := hX₀ x (by linarith [le_max_right (2:ℝ) X₀])
    have hψ : ChebyshevPsi x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n :=
      Chebyshev.psi_eq_sum_range x
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    have hxexp : |x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))|
        = x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := abs_of_pos hcomp0
    calc |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) - x|
        = |(ChebyshevPsi x - x)| := by rw [hψ]
      _ ≤ C * |x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))| := by
          have := h
          simpa using this
      _ = C * (x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))) := by rw [hxexp]
      _ ≤ (max C 1 + K / m) * (x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))) := by
          apply mul_le_mul_of_nonneg_right _ hcomp0.le
          have h1 : C ≤ max C 1 := le_max_left _ _
          have h2 : (0:ℝ) ≤ K / m := by positivity
          linarith
      _ = (max C 1 + K / m) * x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by ring

end SWShims

section LandauCount
open Metric

/-- **Landau with the Jensen zero count** (SW brick B1b): the `landau_LFunction`
    package plus `∑ m ≤ 2·log(N(2|t|+7)σ₀/(σ₀−1))` — everything the contour
    `L′/L` bound consumes about one center. -/
theorem landau_LFunction_count (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (σ₀ t : ℝ) (hσ₀ : 1 < σ₀) (hσ₀2 : σ₀ ≤ 2) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ S, ρ ∈ closedBall ((σ₀ : ℂ) + t * Complex.I) (1/5) ∧
        DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ S, m ρ = analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) ∧
      (∀ ρ ∈ closedBall ((σ₀ : ℂ) + t * Complex.I) (1/5),
        DirichletCharacter.LFunction χ ρ = 0 → ρ ∈ S) ∧
      (∀ ρ ∈ S, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ S, (m ρ : ℝ)) ≤ 2 * Real.log ((N : ℝ) * (2 * |t| + 7) * σ₀ / (σ₀ - 1))) ∧
      ∀ z ∈ ball ((σ₀ : ℂ) + t * Complex.I) (1/20), (∀ ρ ∈ S, z ≠ ρ) →
        ‖logDeriv (DirichletCharacter.LFunction χ) z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖
          ≤ 40 * (Real.log ((N : ℝ) * (2 * |t| + 7) * σ₀ / (σ₀ - 1)) + 1) := by
  obtain ⟨S, m, hSz, hm, hcomp, hmpos, hbound⟩ := landau_LFunction N χ hχ σ₀ t hσ₀ hσ₀2
  refine ⟨S, m, hSz, hm, hcomp, hmpos, ?_, hbound⟩
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set c : ℂ := (σ₀ : ℂ) + t * Complex.I with hc
  have hcre : c.re = σ₀ := by rw [hc]; simp
  have hcnorm : ‖c‖ ≤ σ₀ + |t| := by
    rw [hc]
    calc ‖(σ₀:ℂ) + t*Complex.I‖ ≤ ‖(σ₀:ℂ)‖ + ‖(t:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = |σ₀| + |t| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
          simp [Real.norm_eq_abs]
      _ = σ₀ + |t| := by rw [abs_of_pos (by linarith)]
  -- the anchor: f c ≠ 0 with a quantitative lower bound
  have hanchor := LFunction_anchor_quantitative N χ c (by rw [hcre]; exact hσ₀)
  rw [hcre] at hanchor
  have hml0 : (0:ℝ) < (σ₀-1)/σ₀ := by
    apply div_pos <;> linarith
  have hfc0 : DirichletCharacter.LFunction χ c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hanchor
    linarith
  -- the sphere bound at radius 2/5
  have hM1 : (1:ℝ) ≤ (N:ℝ) * (2*|t|+7) := by nlinarith [abs_nonneg t]
  have hfbound : ∀ z ∈ sphere c (2/5),
      ‖DirichletCharacter.LFunction χ z‖ ≤ (N:ℝ) * (2*|t|+7) := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have hzre : (3:ℝ)/5 ≤ z.re := by
      have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      rw [hz] at h1
      have h2 := (abs_le.mp h1).1
      rw [Complex.sub_re, hcre] at h2
      linarith
    have hznorm : ‖z‖ ≤ |t| + 12/5 := by
      calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        _ = ‖c‖ + 2/5 := by rw [hz]
        _ ≤ (σ₀ + |t|) + 2/5 := by linarith [hcnorm]
        _ ≤ |t| + 12/5 := by linarith
    have h3 := LFunction_window_bound N χ hχ (3/5) (|t| + 12/5) (by norm_num)
      (by positivity) z hzre hznorm
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ (N:ℝ) * (2 + (|t| + 12/5)/(3/5)) := h3
      _ ≤ (N:ℝ) * (2*|t|+7) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have h6 : (|t| + 12/5)/((3:ℝ)/5) = (5/3)*|t| + 4 := by ring
          linarith [abs_nonneg t, h6.le, h6.ge]
  -- Jensen
  have hanal : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall c (2/5)) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hjensen := sum_m_le_jensen (DirichletCharacter.LFunction χ) c (1/5) (2/5)
    ((N:ℝ) * (2*|t|+7)) (by norm_num) (by norm_num) hM1 hanal hfc0 hfbound S m hSz hm
  -- massage the bound
  have hlog2 : Real.log ((2:ℝ)/5 / (1/5)) = Real.log 2 := by norm_num
  rw [hlog2] at hjensen
  have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hfcpos : (0:ℝ) < ‖DirichletCharacter.LFunction χ c‖ := by
    have := norm_nonneg (DirichletCharacter.LFunction χ c)
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exact absurd (norm_eq_zero.mp h.symm) hfc0
  have hargpos : (0:ℝ) < (N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1) := by
    apply div_pos (by nlinarith [abs_nonneg t]) (by linarith)
  have hlogmono : Real.log ((N:ℝ) * (2*|t|+7) / ‖DirichletCharacter.LFunction χ c‖)
      ≤ Real.log ((N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hfcpos (by linarith : (0:ℝ) < σ₀-1)]
    have h4 : (σ₀-1)/σ₀ * σ₀ = σ₀ - 1 := by
      field_simp
    have h5 := mul_le_mul_of_nonneg_left hanchor
      (by nlinarith [abs_nonneg t] : (0:ℝ) ≤ (N:ℝ) * (2*|t|+7) * σ₀)
    nlinarith [h5, h4.le, h4.ge, hfcpos, hanchor, hml0]
  have hlogpos : (0:ℝ) ≤ Real.log ((N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith : (0:ℝ) < σ₀-1)]
    nlinarith [abs_nonneg t]
  calc (∑ ρ ∈ S, (m ρ : ℝ))
      ≤ Real.log ((N:ℝ) * (2*|t|+7) / ‖DirichletCharacter.LFunction χ c‖) / Real.log 2 :=
        hjensen
    _ ≤ Real.log ((N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1)) / Real.log 2 := by
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < Real.log 2)
          (by linarith : (0:ℝ) < Real.log 2)]
        nlinarith [hlogmono, hl2]
    _ ≤ 2 * Real.log ((N:ℝ) * (2*|t|+7) * σ₀ / (σ₀-1)) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
        nlinarith [hlogpos, hl2]

end LandauCount

set_option maxHeartbeats 1000000
open DirichletCharacter Complex Metric

section CrossFileInputs



/-- **Contour-to-zero distance** (SW brick B1a): with the final zero-free region's
    `c(ε)`, write `g := c·N^{−ε}/(log(N(4(T+1)+7))+20)` for the height-`T` window gap.
    Every point `s` with `|Im s| ≤ T` and `Re s ≥ 1 − g/2` keeps distance `≥ g/2`
    from every zero of `L(·,χ)` within `‖s − ρ‖ ≤ 1` — the input to the contour
    `L′/L` bound. -/
theorem contour_zero_distance (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ, |s.im| ≤ T →
    1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re →
    ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖s - ρ‖ ≤ 1 →
    c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ ‖s - ρ‖ := by
  obtain ⟨c, hc0, hc⟩ := zero_free_region_final ε hε0
  refine ⟨c, hc0, ?_⟩
  intro N _ χ hχ1 T hT0 s hsim hsre ρ hρz hρnear
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hρform : ((ρ.re : ℝ) : ℂ) + (ρ.im : ℝ) * Complex.I = ρ := Complex.re_add_im ρ
  have hzero' : DirichletCharacter.LFunction χ (((ρ.re : ℝ) : ℂ)
      + (ρ.im : ℝ) * Complex.I) = 0 := by
    rw [hρform]
    exact hρz
  have h1 := hc N χ hχ1 ρ.re ρ.im hzero'
  have him : |ρ.im| ≤ T + 1 := by
    have h2 : |ρ.im - s.im| ≤ ‖ρ - s‖ := by
      have h3 : (ρ - s).im = ρ.im - s.im := by rw [Complex.sub_im]
      rw [← h3]
      exact Complex.abs_im_le_norm _
    have h4 : ‖ρ - s‖ = ‖s - ρ‖ := by
      rw [← norm_neg]
      congr 1
      ring
    have h5 := abs_sub_abs_le_abs_sub ρ.im s.im
    linarith [h2, h4.le, h4.ge, hsim, hρnear, h5]
  obtain ⟨LT, hLTdef⟩ : ∃ x : ℝ, x = Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 := ⟨_, rfl⟩
  obtain ⟨Lρ, hLρdef⟩ : ∃ x : ℝ, x = Real.log ((N:ℝ)*(4*|ρ.im|+7)) + 20 := ⟨_, rfl⟩
  rw [← hLTdef] at hsre ⊢
  rw [← hLρdef] at h1
  have hg0' : (0:ℝ) ≤ |ρ.im| := abs_nonneg _
  have hLρ20 : 20 ≤ Lρ := by
    rw [hLρdef]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|ρ.im|+7)) :=
      Real.log_nonneg (by nlinarith)
    linarith
  have hLT20 : 20 ≤ LT := by
    rw [hLTdef]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) :=
      Real.log_nonneg (by nlinarith)
    linarith
  have hLmono : Lρ ≤ LT := by
    rw [hLρdef, hLTdef]
    have h6 : (N:ℝ)*(4*|ρ.im|+7) ≤ (N:ℝ)*(4*(T+1)+7) := by nlinarith [him, hN1r]
    have h7 := Real.log_le_log (by nlinarith : (0:ℝ) < (N:ℝ)*(4*|ρ.im|+7)) h6
    linarith
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hgap : c * ((N:ℝ))^(-ε) / LT ≤ c * ((N:ℝ))^(-ε) / Lρ := by
    apply div_le_div_of_nonneg_left (by positivity) (by linarith) hLmono
  have hre : s.re - ρ.re ≤ ‖s - ρ‖ := by
    have h8 : (s - ρ).re = s.re - ρ.re := by rw [Complex.sub_re]
    calc s.re - ρ.re = (s - ρ).re := h8.symm
      _ ≤ |(s - ρ).re| := le_abs_self _
      _ ≤ ‖s - ρ‖ := Complex.abs_re_le_norm _
  linarith [h1, hgap, hre, hsre]

set_option maxHeartbeats 2000000 in
/-- **The contour `L′/L` bound** (SW brick B1c): with `c(ε)` from the zero-free
    region and `L_T := log(N(4(T+1)+7))+20`, every `s` in the strip
    `1 − g/2 ≤ Re s ≤ 1 + g`, `|Im s| ≤ T` (`g := c·N^{−ε}/L_T`) has
    `‖L′/L(s,χ)‖ ≤ C(ε)·N^ε·L_T²` — Landau partial fractions at `1+g+i·Im s`,
    every zero at distance `≥ g/2`, at most `2·log` zeros. -/
theorem contour_logDeriv_bound (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 1 ≤ C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ, |s.im| ≤ T →
    1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re →
    s.re ≤ 1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) →
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖
      ≤ C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2 := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := contour_zero_distance ε hε0
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ, x = min c₀ (1/2) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]
    exact lt_min hc₀0 (by norm_num)
  have hc12 : c ≤ 1/2 := by rw [hcdef]; exact min_le_right _ _
  have hcc₀ : c ≤ c₀ := by rw [hcdef]; exact min_le_left _ _
  have hlogc0 : 0 ≤ Real.log (1/c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc0]
    linarith
  obtain ⟨Kc, hKcdef⟩ : ∃ x : ℝ, x = 3 + ε + Real.log (1/c) := ⟨_, rfl⟩
  have hKc3 : 3 ≤ Kc := by rw [hKcdef]; linarith
  obtain ⟨C, hCdef⟩ : ∃ x : ℝ, x = 4*Kc/c + 80*Kc := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    have h1 : (0:ℝ) ≤ 4*Kc/c := by positivity
    linarith [hKc3]
  refine ⟨c, C, hc0, hc12, hC1, ?_⟩
  intro N _ χ hχ1 T hT0 s hsim hsre1 hsre2
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hNe1 : ((N:ℝ))^(-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hNp1 : (1:ℝ) ≤ ((N:ℝ))^ε :=
    Real.one_le_rpow hN1r (by linarith)
  have hNcancel : ((N:ℝ))^(-ε) * ((N:ℝ))^ε = 1 := by
    rw [← Real.rpow_add (by linarith : (0:ℝ) < (N:ℝ))]
    simp
  obtain ⟨LT, hLTdef⟩ : ∃ x : ℝ, x = Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 := ⟨_, rfl⟩
  rw [← hLTdef] at hsre1 hsre2 ⊢
  have hargT1 : (1:ℝ) ≤ (N:ℝ)*(4*(T+1)+7) := by nlinarith
  have hLT20 : 20 ≤ LT := by
    rw [hLTdef]
    have := Real.log_nonneg hargT1
    linarith
  obtain ⟨g, hgdef⟩ : ∃ x : ℝ, x = c * ((N:ℝ))^(-ε) / LT := ⟨_, rfl⟩
  rw [← hgdef] at hsre1 hsre2
  have hg0 : 0 < g := by
    rw [hgdef]
    positivity
  have hg40 : g ≤ 1/40 := by
    rw [hgdef, div_le_iff₀ (by linarith : (0:ℝ) < LT)]
    nlinarith [hNe1, hNe0.le, hc12, hLT20, hc0]
  -- Landau at the center 1+g + i·Im s
  obtain ⟨S, m, hSz, hm, hcomp, hmpos, hcount, hbound⟩ :=
    landau_LFunction_count N χ hχ1 (1+g) s.im (by linarith) (by linarith)
  have hs1g : (1 + g) - 1 = g := by ring
  rw [hs1g] at hcount hbound
  -- s is in the evaluation ball
  have hsc : ‖s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)‖ = |s.re - (1+g)| := by
    have h1 : s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)
        = ((s.re - (1+g) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
      · simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
  have hsc20 : ‖s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)‖ ≤ 3/80 := by
    rw [hsc, abs_le]
    constructor <;> nlinarith [hsre1, hsre2, hg0, hg40]
  have hsball : s ∈ ball (((1+g : ℝ) : ℂ) + s.im * Complex.I) (1/20) := by
    rw [mem_ball, dist_eq_norm]
    calc ‖s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)‖ ≤ 3/80 := hsc20
      _ < 1/20 := by norm_num
  -- every Landau zero keeps distance ≥ g/2
  have hsre1' : 1 - c₀ * ((N:ℝ))^(-ε)
      / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re := by
    rw [← hLTdef]
    have h3 : c * ((N:ℝ))^(-ε) / LT ≤ c₀ * ((N:ℝ))^(-ε) / LT := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < LT) (by linarith : (0:ℝ) < LT)]
      have h4 := mul_le_mul_of_nonneg_right hcc₀ hNe0.le
      nlinarith [h4, hLT20]
    linarith [hsre1, h3, hgdef.le, hgdef.ge]
  have hdist : ∀ ρ ∈ S, g/2 ≤ ‖s - ρ‖ := by
    intro ρ hρ
    obtain ⟨hρball, hρzero⟩ := hSz ρ hρ
    rw [mem_closedBall, dist_eq_norm] at hρball
    have h1 : ‖s - ρ‖ ≤ 1 := by
      have h1b : ‖(((1+g : ℝ) : ℂ) + s.im * Complex.I) - ρ‖ ≤ 1/5 := by
        rw [norm_sub_rev]
        exact hρball
      calc ‖s - ρ‖ = ‖(s - (((1+g : ℝ) : ℂ) + s.im * Complex.I))
            + ((((1+g : ℝ) : ℂ) + s.im * Complex.I) - ρ)‖ := by ring_nf
        _ ≤ ‖s - (((1+g : ℝ) : ℂ) + s.im * Complex.I)‖
            + ‖(((1+g : ℝ) : ℂ) + s.im * Complex.I) - ρ‖ := norm_add_le _ _
        _ ≤ 3/80 + 1/5 := by linarith [hsc20, h1b]
        _ ≤ 1 := by norm_num
    have h2 := hc₀ N χ hχ1 T hT0 s hsim hsre1' ρ hρzero h1
    rw [← hLTdef] at h2
    have h3 : c * ((N:ℝ))^(-ε) / LT ≤ c₀ * ((N:ℝ))^(-ε) / LT := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < LT) (by linarith : (0:ℝ) < LT)]
      have h4 := mul_le_mul_of_nonneg_right hcc₀ hNe0.le
      nlinarith [h4, hLT20]
    rw [hgdef]
    linarith [h2, h3]
  have hzS : ∀ ρ ∈ S, s ≠ ρ := by
    intro ρ hρ heq
    have h5 := hdist ρ hρ
    rw [heq, sub_self, norm_zero] at h5
    linarith [hg0]
  have hb := hbound s hsball hzS
  -- the partial-fraction sum
  have hsum : ‖∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g) := by
    calc ‖∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ ≤ ∑ ρ ∈ S, ‖((m ρ : ℂ)) / (s - ρ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, (m ρ : ℝ) * (2/g) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          have h5 := hdist ρ hρ
          have h6 : (0:ℝ) < ‖s - ρ‖ := by linarith [hg0]
          rw [div_le_iff₀ h6]
          have h7 := mul_le_mul_of_nonneg_left h5
            (by positivity : (0:ℝ) ≤ (m ρ : ℝ) * (2/g))
          have h8 : (m ρ : ℝ) * (2/g) * (g/2) = (m ρ : ℝ) := by
            field_simp
          linarith [h7, h8.le, h8.ge]
      _ = (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g) := by
          rw [← Finset.sum_mul]
  -- the log-argument bound
  have hg1 : (1:ℝ)/g = LT * ((N:ℝ))^ε / c := by
    have h9 : g * (LT * ((N:ℝ))^ε / c) = 1 := by
      rw [hgdef]
      calc c * ((N:ℝ))^(-ε) / LT * (LT * ((N:ℝ))^ε / c)
          = (((N:ℝ))^(-ε) * ((N:ℝ))^ε) * ((c/c) * (LT/LT)) := by ring
        _ = 1 := by
            rw [hNcancel, div_self (ne_of_gt hc0),
              div_self (by linarith : LT ≠ 0)]
            norm_num
    rw [div_eq_iff (ne_of_gt hg0)]
    linarith [h9]
  have hlog1g : Real.log (1/g) ≤ (1+ε)*LT + Real.log (1/c) := by
    rw [hg1]
    have hNlog : Real.log ((N:ℝ)) ≤ LT - 20 := by
      rw [hLTdef]
      have h11 : (N:ℝ) ≤ (N:ℝ)*(4*(T+1)+7) := by nlinarith
      have h12 := Real.log_le_log (by linarith : (0:ℝ) < (N:ℝ)) h11
      linarith
    have hLTlog : Real.log LT ≤ LT - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    calc Real.log (LT * ((N:ℝ))^ε / c)
        = Real.log (LT * ((N:ℝ))^ε) - Real.log c := by
          rw [Real.log_div (by positivity) (ne_of_gt hc0)]
      _ = Real.log LT + ε * Real.log ((N:ℝ)) - Real.log c := by
          rw [Real.log_mul (by linarith : LT ≠ 0) (by positivity),
            Real.log_rpow (by linarith : (0:ℝ) < (N:ℝ))]
      _ ≤ (LT - 1) + ε * (LT - 20) - Real.log c := by
          have h13 := mul_le_mul_of_nonneg_left hNlog (le_of_lt hε0)
          linarith [hLTlog, h13]
      _ ≤ (1+ε)*LT + Real.log (1/c) := by
          have h14 : Real.log (1/c) = - Real.log c := by
            rw [one_div, Real.log_inv]
          nlinarith [hε0, h14.le, h14.ge, hLT20]
  have hA : Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) ≤ Kc * LT := by
    have h15 : (N:ℝ)*(2*|s.im|+7)*(1+g)/g ≤ (2*((N:ℝ)*(4*(T+1)+7))) * (1/g) := by
      rw [div_le_iff₀ hg0]
      have h16 : (2*|s.im|+7)*(1+g) ≤ 2*(4*(T+1)+7) := by
        nlinarith [hsim, hg40, hg0, abs_nonneg s.im, hT0]
      have h17 : (N:ℝ)*(2*|s.im|+7)*(1+g) ≤ 2*((N:ℝ)*(4*(T+1)+7)) := by
        nlinarith [h16, hN1r, abs_nonneg s.im, hg0]
      have h18 : (1:ℝ)/g * g = 1 := by field_simp
      nlinarith [h17, h18, hg0]
    calc Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g)
        ≤ Real.log ((2*((N:ℝ)*(4*(T+1)+7))) * (1/g)) := by
          apply Real.log_le_log _ h15
          apply div_pos _ hg0
          exact mul_pos (mul_pos (by linarith : (0:ℝ) < (N:ℝ))
            (by nlinarith [abs_nonneg s.im] : (0:ℝ) < 2*|s.im|+7))
            (by linarith [hg0] : (0:ℝ) < 1+g)
      _ = Real.log 2 + Real.log ((N:ℝ)*(4*(T+1)+7)) + Real.log (1/g) := by
          rw [Real.log_mul (by nlinarith) (by positivity),
            Real.log_mul (by norm_num) (by nlinarith)]
      _ ≤ 1 + (LT - 20) + ((1+ε)*LT + Real.log (1/c)) := by
          have hlog2le : Real.log 2 ≤ 1 := by
            rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
            apply Real.log_le_log (by norm_num)
            have := Real.exp_one_gt_d9
            linarith
          have h19 : Real.log ((N:ℝ)*(4*(T+1)+7)) = LT - 20 := by
            rw [hLTdef]
            ring
          linarith [hlog2le, h19.le, h19.ge, hlog1g]
      _ ≤ Kc * LT := by
          rw [hKcdef]
          have h20 : Real.log (1/c) * 1 ≤ Real.log (1/c) * LT :=
            mul_le_mul_of_nonneg_left (by linarith) hlogc0
          nlinarith [hLT20, hε0, h20]
  have hA0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hg0]
    have p1 : (7:ℝ) ≤ (2*|s.im|+7) := by linarith [abs_nonneg s.im]
    have p2 : (1:ℝ) ≤ 1+g := by linarith
    have p3 : (7:ℝ) ≤ (N:ℝ)*(2*|s.im|+7) := by nlinarith [hN1r, p1]
    have p4 : (7:ℝ) ≤ (N:ℝ)*(2*|s.im|+7)*(1+g) := by nlinarith [p3, p2]
    linarith [p4, hg40, hg0]
  -- assemble
  have htri : ‖logDeriv (DirichletCharacter.LFunction χ) s‖
      ≤ (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g)
        + 40 * (Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) + 1) := by
    calc ‖logDeriv (DirichletCharacter.LFunction χ) s‖
        = ‖(logDeriv (DirichletCharacter.LFunction χ) s
            - ∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)) + ∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ := by
          congr 1
          ring
      _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s
            - ∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ + ‖∑ ρ ∈ S, ((m ρ : ℂ)) / (s - ρ)‖ :=
          norm_add_le _ _
      _ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g)
            + 40 * (Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) + 1) := by
          linarith [hb, hsum]
  have hsumA : (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g)
      ≤ (4*Kc/c) * ((N:ℝ))^ε * LT^2 := by
    have h21 : (∑ ρ ∈ S, (m ρ : ℝ)) * (2/g)
        ≤ (2 * Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g)) * (2/g) := by
      apply mul_le_mul_of_nonneg_right hcount (by positivity)
    have h22 : (2 * Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g)) * (2/g)
        ≤ (2 * (Kc * LT)) * (2/g) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [hA]
    have h23 : (2 * (Kc * LT)) * (2/g) = 4*Kc*LT*(1/g) := by ring
    have h24 : 4*Kc*LT*(1/g) = (4*Kc/c) * ((N:ℝ))^ε * LT^2 := by
      rw [hg1]
      ring
    linarith [h21, h22, h23.le, h23.ge, h24.le, h24.ge]
  have h40A : 40 * (Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) + 1)
      ≤ 80*Kc * ((N:ℝ))^ε * LT^2 := by
    have h25 : 40 * (Real.log ((N:ℝ)*(2*|s.im|+7)*(1+g)/g) + 1)
        ≤ 40 * (Kc*LT) + 40 := by linarith [hA]
    have h26 : (40:ℝ) ≤ 40 * (Kc*LT) := by nlinarith [hKc3, hLT20]
    have h27 : 80 * (Kc*LT) ≤ 80*Kc*LT^2 := by nlinarith [hKc3, hLT20]
    have h28 : 80*Kc*LT^2 ≤ 80*Kc*LT^2 * ((N:ℝ))^ε := by
      nlinarith [hNp1, hKc3, hLT20]
    have h29 : 80*Kc*LT^2 * ((N:ℝ))^ε = 80*Kc * ((N:ℝ))^ε * LT^2 := by ring
    linarith [h25, h26, h27, h28, h29.le, h29.ge]
  have hCexp : C * ((N:ℝ))^ε * LT^2
      = (4*Kc/c) * ((N:ℝ))^ε * LT^2 + 80*Kc * ((N:ℝ))^ε * LT^2 := by
    rw [hCdef]
    ring
  linarith [htri, hsumA, h40A, hCexp.le, hCexp.ge]

open Finset in
open scoped ArithmeticFunction in
/-- **Character orthogonality for the AP prime-counting sum** (SW brick B5a): for a
    unit residue `a` mod `q`, exactly
    `φ(q)·∑_{n<X, n≡a} Λ(n) = ∑_χ χ(a⁻¹)·∑_{n<X} χ(n)Λ(n)` — the bridge from the
    twisted sums `ψ(X,χ)` to primes in the progression. EXACT identity: terms with
    `gcd(n,q) > 1` vanish on both sides. -/
theorem psi_ap_orthogonality (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (X : ℕ) :
    (q.totient : ℂ) * (∑ n ∈ Finset.range X,
        if a = ((n : ZMod q)) then ((Λ n : ℝ) : ℂ) else 0)
      = ∑ χ : DirichletCharacter ℂ q, (χ a⁻¹) *
          (∑ n ∈ Finset.range X, χ ((n : ZMod q)) * ((Λ n : ℝ) : ℂ)) := by
  symm
  calc ∑ χ : DirichletCharacter ℂ q, (χ a⁻¹) *
      (∑ n ∈ Finset.range X, χ ((n : ZMod q)) * ((Λ n : ℝ) : ℂ))
      = ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.range X,
          (χ a⁻¹ * χ ((n : ZMod q))) * ((Λ n : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = ∑ n ∈ Finset.range X, ∑ χ : DirichletCharacter ℂ q,
          (χ a⁻¹ * χ ((n : ZMod q))) * ((Λ n : ℝ) : ℂ) := Finset.sum_comm
    _ = ∑ n ∈ Finset.range X,
          (if a = ((n : ZMod q)) then (q.totient : ℂ) else 0) * ((Λ n : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [← Finset.sum_mul,
          DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) ha ((n : ZMod q))]
    _ = (q.totient : ℂ) * (∑ n ∈ Finset.range X,
          if a = ((n : ZMod q)) then ((Λ n : ℝ) : ℂ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        split_ifs
        · ring
        · ring

/-- **−L′/L(χ) as the χ·Λ Dirichlet series** (SW Perron input, brick B2a): for `Re s > 1`, the
    negative logarithmic derivative of `LFunction χ` equals `∑_n χ(n)Λ(n) n^{-s}`. Bridges the contour
    `logDeriv` bounds (`contour_logDeriv_bound`, stated for `LFunction χ`) to the Perron integrand
    (the twisted von-Mangoldt series). Mathlib `deriv_LFunction_eq_deriv_LSeries` +
    `LFunction_eq_LSeries` + `LSeries_twist_vonMangoldt_eq`. (`↗` avoided — `open Metric` shadows the
    `scoped[LSeries.notation]` arrow.) -/
lemma neg_logDeriv_LFunction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      = LSeries (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
  exact (LSeries_twist_vonMangoldt_eq χ hs).symm

/-- **`LFunction χ` is entire for `χ ≠ 1`** (SW brick B3 input): no poles inside the contour
    rectangle. Mathlib `differentiable_LFunction`. -/
lemma LFunction_entire {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  differentiable_LFunction hχ

/-- **`LFunction χ` has no zeros on `Re s ≥ 1` for `χ ≠ 1`** (SW brick B3 input): the contour's
    right edge `Re = σ₀ > 1` (and the boundary `Re = 1`) is zero-free, so `L′/L` is holomorphic there.
    Mathlib `LFunction_ne_zero_of_one_le_re`. -/
lemma LFunction_ne_zero_re_ge_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) : DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs


/-- **Perron-integrand reshape** (SW brick W1j): `(−L′/L · X^s)/(s(s+1)) = −L′/L · (X^s/(s(s+1)))`
    under the integral — aligns `smoothed_perron_LFunction`'s form with the `G`-form used by every
    W1 estimate lemma (`mul_div_assoc` under `funext`). -/
lemma perron_integrand_reshape {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X σ : ℝ) :
    (∫ t : ℝ, (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I))
        * (X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = ∫ t : ℝ, (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I))
        * ((X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))) := by
  congr 1
  funext t
  rw [mul_div_assoc]

set_option maxHeartbeats 1000000
open DirichletCharacter Complex Metric MeasureTheory

/-- The smoothed-Perron integrand (duplicated def, identical to DirichletPsiExplicit/Frontier). -/
noncomputable def G' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X : ℝ) : ℂ → ℂ :=
  fun s => (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
    * ((X : ℂ) ^ s / (s * (s + 1)))




/-- **W2d: cpow ratio of positive reals** — `(X:ℂ)^s/(n:ℂ)^s = ((X/n:ℝ):ℂ)^s` for positive real
    `X, n`: reduces the per-`n` summand `X^s·n^{−s}·kernel` to the Perron-kernel shape at
    `y = X/n`. Via `Complex.mul_cpow_ofReal_nonneg` on `X = (X/n)·n`. -/
lemma cpow_ratio (X n : ℝ) (hX : 0 < X) (hn : 0 < n) (s : ℂ) :
    (X : ℂ) ^ s / (n : ℂ) ^ s = (((X / n : ℝ)) : ℂ) ^ s := by
  have hXn : X = (X / n) * n := by field_simp
  have h1 : ((X : ℝ) : ℂ) ^ s = (((X / n : ℝ)) : ℂ) ^ s * ((n : ℝ) : ℂ) ^ s := by
    calc ((X : ℝ) : ℂ) ^ s = ((((X / n : ℝ)) : ℂ) * ((n : ℝ) : ℂ)) ^ s := by
          rw [← Complex.ofReal_mul, ← hXn]
      _ = (((X / n : ℝ)) : ℂ) ^ s * ((n : ℝ) : ℂ) ^ s :=
          Complex.mul_cpow_ofReal_nonneg (by positivity) hn.le s
  have hn0 : ((n : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne')]
    exact Complex.exp_ne_zero _
  rw [h1]
  field_simp

open ArithmeticFunction in
/-- **W2b: the smoothed integrand as a tsum of Perron-kernel summands** — for `Re s > 1`, `X > 0`:
    `G'(s) = ∑'_n χ(n)Λ(n) · (X/n)^s/(s(s+1))` (the `n`-th summand in exactly the
    `perron_kernel_*` shape at `y = X/n`). Via `neg_logDeriv_LFunction_eq` + `tsum_mul_right` +
    per-`n` `cpow_ratio` (`n = 0` term vanishes since `Λ(0) = 0`). -/
lemma G_tsum_form {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X : ℝ) (hX : 0 < X)
    {s : ℂ} (hs : 1 < s.re) :
    G' χ X s = ∑' n : ℕ,
      (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) * ((((X / n : ℝ)) : ℂ) ^ s / (s * (s + 1))) := by
  rw [G', neg_logDeriv_LFunction_eq χ hs, LSeries, ← tsum_mul_right]
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · have hn0 : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne']
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hratio := cpow_ratio X (n:ℝ) hX hnR s
    push_cast at hratio ⊢
    rw [← hratio]
    ring

open ArithmeticFunction in
/-- **W2c: the sum/integral interchange** — `∫_ℝ G'(σ+it) dt = ∑'_n ∫_ℝ h_n(t) dt` for `X>0`, `σ>1`:
    dominated by `Λ(n)(X/n)^σ·(1+t²)⁻¹` (integrable in `t`, summable in `n`). -/
lemma integral_G_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X σ : ℝ)
    (hX : 0 < X) (hσ : 1 < σ) :
    (∫ t : ℝ, G' χ X ((σ:ℂ) + t * I))
      = ∑' n : ℕ, ∫ t : ℝ,
        (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
          * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))) := by
  have hre : ∀ t : ℝ, ((σ:ℂ) + (t:ℂ) * I).re = σ := fun t => by simp
  have hs1 : ∀ t : ℝ, 1 < ((σ:ℂ) + (t:ℂ) * I).re := fun t => by rw [hre]; exact hσ
  set h : ℕ → ℝ → ℂ := fun n t =>
    (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
      * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I) / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)))
    with hdef
  have hden : ∀ t : ℝ, (1:ℝ) + t^2 ≤ ‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖ := by
    intro t
    have e1 : ‖(σ:ℂ) + (t:ℂ) * I‖ = Real.sqrt (σ^2 + t^2) := Complex.norm_add_mul_I σ t
    have e2 : (σ:ℂ) + (t:ℂ) * I + 1 = ((σ + 1 : ℝ) : ℂ) + (t:ℂ) * I := by push_cast; ring
    have e3 : ‖(σ:ℂ) + (t:ℂ) * I + 1‖ = Real.sqrt ((σ+1)^2 + t^2) := by
      rw [e2]; exact Complex.norm_add_mul_I _ _
    rw [e1, e3]
    have h1 : Real.sqrt (σ^2 + t^2) * Real.sqrt (σ^2 + t^2)
        ≤ Real.sqrt (σ^2 + t^2) * Real.sqrt ((σ+1)^2 + t^2) := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt (by positivity)] at h1
    nlinarith [h1, sq_nonneg t]
  have hdenpos : ∀ t : ℝ, (0:ℝ) < ‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖ := by
    intro t
    have := hden t
    nlinarith [sq_nonneg t]
  have hdenne : ∀ t : ℝ, ((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1) ≠ 0 := by
    intro t hzero
    have h2 : ‖((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)‖ = 0 := by rw [hzero, norm_zero]
    rw [norm_mul] at h2
    nlinarith [hdenpos t]
  have hzero0 : h 0 = fun _ => 0 := by
    funext t
    simp [hdef, ArithmeticFunction.map_zero]
  have hnorm : ∀ n : ℕ, 0 < n → ∀ t : ℝ,
      ‖h n t‖ ≤ (vonMangoldt n * (X/n) ^ (σ:ℝ)) * (1 + t^2)⁻¹ := by
    intro n hn t
    have hy0 : (0:ℝ) < X / n := by positivity
    have h1 : ‖(((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)‖ = (X/n) ^ (σ:ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0, hre]
    have h2 : ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖ ≤ vonMangoldt n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      calc ‖χ (n : ZMod N)‖ * vonMangoldt n ≤ 1 * vonMangoldt n :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) vonMangoldt_nonneg
        _ = vonMangoldt n := one_mul _
    have h4 : (0:ℝ) < 1 + t^2 := by positivity
    rw [hdef]
    simp only []
    rw [norm_mul, norm_mul, norm_div, h1]
    have h3 : (1:ℝ) + t^2 ≤ ‖((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)‖ := by
      rw [norm_mul]; exact hden t
    have hΛ : ‖((vonMangoldt n : ℝ) : ℂ)‖ = vonMangoldt n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    calc ‖χ (n : ZMod N)‖ * ‖((vonMangoldt n : ℝ) : ℂ)‖
          * ((X/n) ^ (σ:ℝ) / ‖((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)‖)
        ≤ 1 * vonMangoldt n * ((X/n) ^ (σ:ℝ) / (1 + t^2)) := by
          apply mul_le_mul
          · exact mul_le_mul (DirichletCharacter.norm_le_one χ _) (le_of_eq hΛ)
              (norm_nonneg _) zero_le_one
          · exact div_le_div_of_nonneg_left (by positivity) h4 h3
          · positivity
          · exact mul_nonneg zero_le_one vonMangoldt_nonneg
      _ = (vonMangoldt n * (X/n) ^ (σ:ℝ)) * (1 + t^2)⁻¹ := by
          rw [div_eq_mul_inv]; ring
  have hInt : ∀ n : ℕ, Integrable (h n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hzero0]
      exact integrable_zero _ _ _
    · have hy0 : (0:ℝ) < X / n := by positivity
      have hyC : (((X / n : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
      have hcpow : Continuous (fun t : ℝ => (((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)) := by
        have he : (fun t : ℝ => (((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I))
            = fun t : ℝ => Complex.exp (Complex.log (((X / n : ℝ)) : ℂ) * ((σ:ℂ) + (t:ℂ) * I)) := by
          funext t
          rw [Complex.cpow_def_of_ne_zero hyC]
        rw [he]
        fun_prop
      have hcont : Continuous (h n) := by
        rw [hdef]
        simp only []
        apply Continuous.mul continuous_const
        exact Continuous.div hcpow (by fun_prop) hdenne
      apply Integrable.mono' (g := fun t : ℝ => (vonMangoldt n * (X/n) ^ (σ:ℝ)) * (1 + t^2)⁻¹)
        (integrable_inv_one_add_sq.const_mul _) hcont.aestronglyMeasurable
      exact Filter.Eventually.of_forall (hnorm n hn)
  have hIntNorm : ∀ n : ℕ, 0 < n →
      (∫ t : ℝ, ‖h n t‖) ≤ (vonMangoldt n * (X/n) ^ (σ:ℝ)) * Real.pi := by
    intro n hn
    calc (∫ t : ℝ, ‖h n t‖)
        ≤ ∫ t : ℝ, (vonMangoldt n * (X/n) ^ (σ:ℝ)) * (1 + t^2)⁻¹ := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (integrable_inv_one_add_sq.const_mul _)
            (Filter.Eventually.of_forall (hnorm n hn))
      _ = (vonMangoldt n * (X/n) ^ (σ:ℝ)) * ∫ t : ℝ, (1 + t^2)⁻¹ :=
          integral_const_mul _ _
      _ = (vonMangoldt n * (X/n) ^ (σ:ℝ)) * Real.pi := by
          rw [integral_univ_inv_one_add_sq]
  have hSummable : Summable (fun n : ℕ => ∫ t : ℝ, ‖h n t‖) := by
    have hmaj : Summable (fun n : ℕ =>
        (Real.pi * X ^ (σ:ℝ)) * ‖LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ)) (σ:ℂ) n‖) := by
      apply Summable.mul_left
      apply summable_norm_iff.mpr
      exact LSeriesSummable_vonMangoldt (s := (σ:ℂ)) (by simpa using hσ)
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun t => norm_nonneg _)
      _ hmaj
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hzero0]
      simp
    · have hy0 : (0:ℝ) < X / n := by positivity
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      calc (∫ t : ℝ, ‖h n t‖) ≤ (vonMangoldt n * (X/n) ^ (σ:ℝ)) * Real.pi := hIntNorm n hn
        _ = (Real.pi * X ^ (σ:ℝ)) * (vonMangoldt n / (n:ℝ) ^ (σ:ℝ)) := by
            rw [Real.div_rpow hX.le hnR.le]
            field_simp
        _ = (Real.pi * X ^ (σ:ℝ)) * ‖LSeries.term (fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ)) (σ:ℂ) n‖ := by
            rw [LSeries.norm_term_eq]
            rw [if_neg hn.ne']
            congr 1
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
              Complex.ofReal_re]
  calc (∫ t : ℝ, G' χ X ((σ:ℂ) + t * I))
      = ∫ t : ℝ, ∑' n : ℕ, h n t := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro t
        exact G_tsum_form χ X hX (hs1 t)
    _ = ∑' n : ℕ, ∫ t : ℝ, h n t :=
        (integral_tsum_of_summable_integral_norm hInt hSummable).symm

open Filter Topology in
/-- **W2-y1: the Perron kernel at `y = 1` vanishes** — `(1/2π)·∫ 1^{σ+it}/((σ+it)(σ+it+1)) dt = 0`
    for `σ > 0`: dominated-convergence limit of `perron_kernel_gtOne` along `y_k = 1 + 1/(k+1) ↓ 1`
    (`1 − 1/y_k → 0`; domination `2^σ·(1+t²)⁻¹`-grade uniform for `y ≤ 2`). -/
lemma perron_kernel_one (σ : ℝ) (hσ : 0 < σ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        (((1:ℝ) : ℂ) ^ ((σ : ℂ) + t * I)) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))
      = 0 := by
  -- the kernel and its denominator bounds
  have hre : ∀ t : ℝ, ((σ:ℂ) + (t:ℂ) * I).re = σ := fun t => by simp
  have hden : ∀ t : ℝ, min 1 (σ^2) + t^2 ≤ ‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖ := by
    intro t
    have e1 : ‖(σ:ℂ) + (t:ℂ) * I‖ = Real.sqrt (σ^2 + t^2) := Complex.norm_add_mul_I σ t
    have e2 : (σ:ℂ) + (t:ℂ) * I + 1 = ((σ + 1 : ℝ) : ℂ) + (t:ℂ) * I := by push_cast; ring
    have e3 : ‖(σ:ℂ) + (t:ℂ) * I + 1‖ = Real.sqrt ((σ+1)^2 + t^2) := by
      rw [e2]; exact Complex.norm_add_mul_I _ _
    rw [e1, e3]
    have h1 : Real.sqrt (σ^2 + t^2) * Real.sqrt (σ^2 + t^2)
        ≤ Real.sqrt (σ^2 + t^2) * Real.sqrt ((σ+1)^2 + t^2) := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt (by positivity)] at h1
    have h2 : min 1 (σ^2) ≤ σ^2 := min_le_right _ _
    nlinarith [h1]
  have hm0 : (0:ℝ) < min 1 (σ^2) := lt_min one_pos (pow_pos hσ 2)
  have hdenpos : ∀ t : ℝ, (0:ℝ) < ‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖ := by
    intro t
    have := hden t
    nlinarith [sq_nonneg t]
  -- the y-parameterized integrand family and its uniform bound (1 ≤ y ≤ 2)
  set F : ℕ → ℝ → ℂ := fun k t =>
    (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)
      / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)) with hFdef
  set f : ℝ → ℂ := fun t =>
    (((1:ℝ) : ℂ)) ^ ((σ:ℂ) + (t:ℂ) * I)
      / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)) with hfdef
  have hyk : ∀ k : ℕ, (1:ℝ) < 1 + 1/((k:ℝ)+1) := by
    intro k
    have : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
    linarith
  have hyk2 : ∀ k : ℕ, (1:ℝ) + 1/((k:ℝ)+1) ≤ 2 := by
    intro k
    have h1 : (1:ℝ) ≤ (k:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have : 1/((k:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h1
    linarith
  have hbound : ∀ k : ℕ, ∀ t : ℝ,
      ‖F k t‖ ≤ (2 ^ (σ:ℝ)) * ((min 1 (σ^2) + t^2)⁻¹) := by
    intro k t
    rw [hFdef]
    simp only []
    rw [norm_div, norm_mul]
    have h1 : ‖(((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)‖
        = (1 + 1/((k:ℝ)+1)) ^ (σ:ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hyk k]), hre]
    rw [h1]
    have h2 : (1 + 1/((k:ℝ)+1)) ^ (σ:ℝ) ≤ 2 ^ (σ:ℝ) :=
      Real.rpow_le_rpow (by linarith [hyk k]) (hyk2 k) hσ.le
    have h3 := hden t
    have h4 : (0:ℝ) < min 1 (σ^2) + t^2 := by nlinarith [sq_nonneg t]
    calc (1 + 1/((k:ℝ)+1)) ^ (σ:ℝ) / (‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖)
        ≤ 2 ^ (σ:ℝ) / (min 1 (σ^2) + t^2) := by
          have ha := div_le_div_of_nonneg_right h2 (hdenpos t).le
          have hb : (2:ℝ) ^ (σ:ℝ) / (‖(σ:ℂ) + (t:ℂ) * I‖ * ‖(σ:ℂ) + (t:ℂ) * I + 1‖)
              ≤ 2 ^ (σ:ℝ) / (min 1 (σ^2) + t^2) :=
            div_le_div_of_nonneg_left (by positivity) h4 h3
          linarith
      _ = (2 ^ (σ:ℝ)) * ((min 1 (σ^2) + t^2)⁻¹) := by rw [div_eq_mul_inv]
  -- integrability of the bound
  have hbound_int : Integrable (fun t : ℝ => (2 ^ (σ:ℝ)) * ((min 1 (σ^2) + t^2)⁻¹)) := by
    apply Integrable.const_mul
    apply Integrable.mono' (g := fun t : ℝ => (min 1 (σ^2))⁻¹ * (1 + t^2)⁻¹)
      (integrable_inv_one_add_sq.const_mul _)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.inv₀ (by fun_prop)
      intro t
      nlinarith [sq_nonneg t]
    · apply Filter.Eventually.of_forall
      intro t
      have h4 : (0:ℝ) < min 1 (σ^2) + t^2 := by nlinarith [sq_nonneg t]
      rw [Real.norm_of_nonneg (by positivity)]
      rw [inv_le_iff_one_le_mul₀ h4]
      have hmin1 : min 1 (σ^2) ≤ 1 := min_le_left _ _
      have h5 : (min 1 (σ^2))⁻¹ * (1 + t^2)⁻¹ * (min 1 (σ^2) + t^2)
          = ((min 1 (σ^2) + t^2) / (min 1 (σ^2) * (1 + t^2))) := by
        field_simp
      rw [h5, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg t, hm0]
  -- measurability of each F k
  have hdenne : ∀ t : ℝ, ((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1) ≠ 0 := by
    intro t hzero
    have h2 : ‖((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)‖ = 0 := by rw [hzero, norm_zero]
    rw [norm_mul] at h2
    nlinarith [hdenpos t]
  have hFmeas : ∀ k : ℕ, AEStronglyMeasurable (F k) (volume : Measure ℝ) := by
    intro k
    have hyC : (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by linarith [hyk k])
    have hcont : Continuous (F k) := by
      rw [hFdef]
      simp only []
      apply Continuous.div _ (by fun_prop) hdenne
      have he : (fun t : ℝ => (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I))
          = fun t : ℝ => Complex.exp (Complex.log (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) * ((σ:ℂ) + (t:ℂ) * I)) := by
        funext t
        rw [Complex.cpow_def_of_ne_zero hyC]
      rw [he]
      fun_prop
    exact hcont.aestronglyMeasurable
  -- pointwise convergence F k t → f t
  have hlim : ∀ t : ℝ, Tendsto (fun k : ℕ => F k t) atTop (𝓝 (f t)) := by
    intro t
    have hbase : Tendsto (fun k : ℕ => (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) atTop (𝓝 (((1:ℝ):ℂ))) := by
      apply Tendsto.comp (Complex.continuous_ofReal.tendsto _)
      have h1 : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := h1.const_add 1
      simpa using this
    have hcpowC : ContinuousAt (fun z : ℂ => z ^ ((σ:ℂ) + (t:ℂ) * I)) (((1:ℝ):ℂ)) := by
      apply continuousAt_cpow_const
      norm_num [Complex.mem_slitPlane_iff]
    have hnum : Tendsto (fun k : ℕ => (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I))
        atTop (𝓝 ((((1:ℝ):ℂ)) ^ ((σ:ℂ) + (t:ℂ) * I))) :=
      (hcpowC.tendsto).comp hbase
    rw [hFdef, hfdef]
    simp only []
    exact hnum.div_const _
  -- dominated convergence
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun t : ℝ => (2 ^ (σ:ℝ)) * ((min 1 (σ^2) + t^2)⁻¹)) hFmeas hbound_int
    (fun k => Filter.Eventually.of_forall (hbound k))
    (Filter.Eventually.of_forall hlim)
  -- values from the gtOne axiom
  have h2πne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hvals : ∀ k : ℕ, (∫ t : ℝ, F k t)
      = (2 * (Real.pi : ℂ)) * (1 - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) := by
    intro k
    have hax := perron_kernel_gtOne (1 + 1/((k:ℝ)+1)) (hyk k) σ hσ
    rw [hFdef]
    simp only []
    calc (∫ t : ℝ, (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)
            / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1)))
        = (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
            (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ) ^ ((σ:ℂ) + (t:ℂ) * I)
              / (((σ:ℂ) + (t:ℂ) * I) * ((σ:ℂ) + (t:ℂ) * I + 1))) := by
          rw [← mul_assoc, mul_one_div, div_self h2πne, one_mul]
      _ = (2 * (Real.pi : ℂ)) * (1 - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) := by rw [hax]
  have hvals_lim : Tendsto (fun k : ℕ => (2 * (Real.pi : ℂ)) * (1 - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)))
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun k : ℕ => (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) atTop (𝓝 1) := by
      apply Tendsto.comp (Complex.continuous_ofReal.tendsto _)
      have h1 : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h1.const_add 1
      simpa using h2
    have hinv : Tendsto (fun k : ℕ => 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) atTop (𝓝 1) := by
      have := hbase.inv₀ (by norm_num : (1:ℂ) ≠ 0)
      simpa using this
    have h3 : Tendsto (fun k : ℕ => (1:ℂ) - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (1:ℂ))).sub hinv
      simpa using this
    have h4 := h3.const_mul (2 * (Real.pi : ℂ))
    simpa using h4
  -- conclude
  have hint_f : (∫ t : ℝ, f t) = 0 := by
    apply tendsto_nhds_unique hDCT
    have : (fun k : ℕ => ∫ t : ℝ, F k t)
        = fun k : ℕ => (2 * (Real.pi : ℂ)) * (1 - 1 / (((1 + 1/((k:ℝ)+1) : ℝ)) : ℂ)) := by
      funext k
      exact hvals k
    rw [this]
    exact hvals_lim
  rw [hfdef] at hint_f
  simp only [] at hint_f
  rw [hint_f, mul_zero]

open ArithmeticFunction in
/-- **W2e: per-`n` Perron evaluation** — for `X > 1`, `σ > 0`, every `n`:
    `(1/2π)·∫ χ(n)Λ(n)·(X/n)^{σ+it}/((σ+it)(σ+it+1)) dt
       = χ(n)Λ(n)·(if n ≤ X then 1 − n/X else 0)`.
    Trichotomy `n < X` (`gtOne`), `n = X` (`perron_kernel_one`, both sides `0` via `1−n/X = 0`),
    `n > X` (`ltOne`); `n = 0` degenerates via `Λ(0) = 0`. -/
lemma perron_summand_eval {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X σ : ℝ) (hX : 1 < X) (hσ : 0 < σ) (n : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
          * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
          * (if (n:ℝ) ≤ X then 1 - ((n:ℝ) : ℂ) / ((X:ℝ) : ℂ) else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ArithmeticFunction.map_zero]
  · have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hXne : (X:ℝ) ≠ 0 := by linarith
    -- pull the constant out
    rw [MeasureTheory.integral_const_mul, show
      (1 / (2 * (Real.pi : ℂ))) * ((χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) * ∫ t : ℝ,
        (((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
        (((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      from by ring]
    congr 1
    rcases lt_trichotomy ((n:ℝ)) X with hlt | heq | hgt
    · -- n < X: y = X/n > 1
      have hy : 1 < X / (n:ℝ) := by
        rw [lt_div_iff₀ hnR]
        linarith
      rw [perron_kernel_gtOne (X / (n:ℝ)) hy σ hσ, if_pos hlt.le]
      congr 1
      rw [show ((X / (n:ℝ) : ℝ) : ℂ) = ((X:ℝ):ℂ) / ((n:ℝ):ℂ) from by push_cast; ring]
      rw [one_div_div]
    · -- n = X: y = 1
      have hy1 : (X / (n:ℝ) : ℝ) = 1 := by
        rw [heq]
        field_simp
      rw [hy1, perron_kernel_one σ hσ, if_pos heq.le]
      have hcast : ((n:ℝ) : ℂ) = ((X:ℝ) : ℂ) := by
        exact_mod_cast congrArg Complex.ofReal heq
      rw [hcast, div_self (Complex.ofReal_ne_zero.mpr hXne)]
      ring
    · -- n > X: 0 < y < 1
      have hy0 : (0:ℝ) < X / (n:ℝ) := by positivity
      have hy1 : X / (n:ℝ) < 1 := by
        rw [div_lt_one hnR]
        exact hgt
      rw [perron_kernel_ltOne (X / (n:ℝ)) hy0 hy1 σ hσ, if_neg (by linarith)]


open ArithmeticFunction in
/-- **W2f: THE SMOOTHED-PERRON REPRESENTATION, PROVEN** — the exact statement of the
    `smoothed_perron_LFunction` axiom, now a theorem (modulo the two PNT kernel inputs):
    reshape → interchange (W2c) → per-`n` evaluation (W2e) → tsum collapse to the finite sum. -/
theorem smoothed_perron_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X : ℝ) (hX : 1 < X) (σ : ℝ) (hσ : 1 < σ) :
    ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
          (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I)
              / DirichletCharacter.LFunction χ ((σ : ℂ) + t * I))
            * (X : ℂ) ^ ((σ : ℂ) + t * I)
            / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)) := by
  have hX0 : (0:ℝ) < X := by linarith
  -- reshape to the G'-form and interchange
  have h1 : (∫ t : ℝ, (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I)
          / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I))
        * (X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = ∑' n : ℕ, ∫ t : ℝ,
        (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
          * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))) := by
    rw [perron_integrand_reshape]
    exact integral_G_tsum χ X σ hX0 hσ
  rw [h1, ← tsum_mul_left]
  -- evaluate each summand and collapse
  have h2 : ∀ n : ℕ, (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ,
      (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
        * ((((X / n : ℝ)) : ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))
      = (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
        * (if (n:ℝ) ≤ X then 1 - ((n:ℝ) : ℂ) / ((X:ℝ) : ℂ) else 0) :=
    perron_summand_eval χ X σ hX (by linarith)
  rw [tsum_congr h2]
  -- tsum → finite sum over range(⌊X⌋+1)
  have hvanish : ∀ n ∉ Finset.range (⌊X⌋₊ + 1),
      (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
        * (if (n:ℝ) ≤ X then 1 - ((n:ℝ) : ℂ) / ((X:ℝ) : ℂ) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hnX : X < (n:ℝ) := by
      have h3 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
      have h4 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      push_cast at h4
      linarith
    rw [if_neg (by linarith)]
    ring
  rw [tsum_eq_sum hvanish]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  have hnX : (n:ℝ) ≤ X := by
    have h3 : n ≤ ⌊X⌋₊ := by omega
    have h4 : ((n:ℕ):ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h3
    have h5 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
    linarith
  rw [if_pos hnX]

/-- **Sharp ↔ smoothed bridge** (SW brick B2b): the sharp partial sum equals the smoothed one plus
    the linear-weight correction `(1/X)∑ n·a_n`. Pure algebra (regroup `a_n·(n/X)`); the correction
    is then handled at two scales `X`, `X(1+δ)` to recover the sharp sum with the smoothed rate. -/
lemma sharp_eq_smoothed_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X : ℝ) (M : ℕ) :
    ∑ n ∈ Finset.range M, χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
      = (∑ n ∈ Finset.range M,
          χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
        + (1 / (X : ℂ)) * ∑ n ∈ Finset.range M,
            (n : ℂ) * (χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

/-- **Perron-kernel holomorphy** (SW brick B3 input): the smoothed kernel `X^s/(s(s+1))` is
    holomorphic on `Re s > 0` (`s ≠ 0`, `s+1 ≠ 0`; `X^s` entire for `X > 0`). Combined with the
    zero-free-region holomorphy of `−L′/L` (`LFunction_ne_zero_re_ge_one` / the contour gap), the
    smoothed-Perron integrand is holomorphic in the shift strip, so the B3 rectangle contour picks up
    only the kernel pole at `s = 0` and (for `χ₀`) the `L`-pole at `s = 1`. -/
lemma perron_kernel_differentiableOn (X : ℝ) (hX : 0 < X) :
    DifferentiableOn ℂ (fun s : ℂ => (X : ℂ) ^ s / (s * (s + 1))) {s : ℂ | 0 < s.re} := by
  have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  apply DifferentiableOn.div
  · have hcpow : Differentiable ℂ (fun s : ℂ => (X : ℂ) ^ s) :=
      fun s => (hasStrictDerivAt_const_cpow (Or.inl hXne)).hasDerivAt.differentiableAt
    exact hcpow.differentiableOn
  · fun_prop
  · intro s hs
    simp only [Set.mem_setOf_eq] at hs
    have h1 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
    have h2 : s + 1 ≠ 0 := by
      intro h
      have : s = -1 := by linear_combination h
      rw [this] at hs; norm_num at hs
    exact mul_ne_zero h1 h2

/-- **Smoothed-kernel magnitude** (SW brick B3 input): `‖X^s/(s(s+1))‖ = X^{Re s}/(‖s‖‖s+1‖)`
    for `X > 0`. Via `norm_cpow_eq_rpow_re_of_pos`. -/
lemma perron_kernel_norm (X : ℝ) (hX : 0 < X) (s : ℂ) :
    ‖(X : ℂ) ^ s / (s * (s + 1))‖ = X ^ s.re / (‖s‖ * ‖s + 1‖) := by
  rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hX]

/-- **Smoothed-kernel vertical decay** (SW brick B3 input): `‖X^s/(s(s+1))‖ ≤ X^{Re s}/(Im s)²` off
    the real axis (`‖s‖, ‖s+1‖ ≥ |Im s|`). The `1/t²` decay makes the top/horizontal contour
    integrals `O(X^σ/T)` in the B3 rectangle shift, and the vertical integral absolutely convergent. -/
lemma perron_kernel_decay (X : ℝ) (hX : 0 < X) (s : ℂ) (hs : s.im ≠ 0) :
    ‖(X : ℂ) ^ s / (s * (s + 1))‖ ≤ X ^ s.re / s.im ^ 2 := by
  rw [perron_kernel_norm X hX s]
  have him1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have him2 : |s.im| ≤ ‖s + 1‖ := by
    have h : (s + 1).im = s.im := by simp
    calc |s.im| = |(s + 1).im| := by rw [h]
      _ ≤ ‖s + 1‖ := Complex.abs_im_le_norm _
  have hsq : s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [← sq_abs, sq]
    exact mul_le_mul him1 him2 (abs_nonneg _) (norm_nonneg _)
  have hX0 : (0 : ℝ) ≤ X ^ s.re := Real.rpow_nonneg hX.le _
  have him0 : (0 : ℝ) < s.im ^ 2 := (sq_nonneg s.im).lt_of_ne (Ne.symm (pow_ne_zero 2 hs))
  exact div_le_div_of_nonneg_left hX0 him0 hsq

/-- **Derivative of the entire L-function is entire** (SW brick B3 input): for `χ ≠ 1`,
    `deriv (LFunction χ)` is differentiable everywhere (holomorphic ⇒ analytic ⇒ deriv analytic).
    Via `AnalyticOnNhd.deriv`. -/
lemma deriv_LFunction_differentiable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Differentiable ℂ (deriv (DirichletCharacter.LFunction χ)) := by
  have hana : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
  have hderiv : AnalyticOnNhd ℂ (deriv (DirichletCharacter.LFunction χ)) Set.univ := hana.deriv
  intro s
  exact (hderiv s (Set.mem_univ s)).differentiableAt

/-- **Smoothed-Perron integrand holomorphy** (SW brick B3): the integrand
    `(−L′/L)·X^s/(s(s+1))` is holomorphic on `{Re s > 0 ∧ L(s,χ) ≠ 0}`. So on the zero-free strip
    (`χ ≠ 1`, `Re s > 1−g`) the B3 rectangle encloses no pole and Cauchy
    (`integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real`) gives the vertical-integral shift
    `∫_{(σ)} = ∫_{(σ')}` (horizontal connectors `→0` by `perron_kernel_decay`). -/
lemma smoothed_integrand_differentiableOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (X : ℝ) (hX : 0 < X) :
    DifferentiableOn ℂ
      (fun s : ℂ => (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
        * ((X : ℂ) ^ s / (s * (s + 1))))
      {s : ℂ | 0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0} := by
  have hSsub : {s : ℂ | 0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0} ⊆ {s : ℂ | 0 < s.re} :=
    fun s hs => hs.1
  apply DifferentiableOn.mul
  · apply DifferentiableOn.div
    · exact ((deriv_LFunction_differentiable χ hχ).neg).differentiableOn
    · exact (differentiable_LFunction hχ).differentiableOn
    · intro s hs; exact hs.2
  · exact (perron_kernel_differentiableOn X hX).mono hSsub

/-- **B3 rectangle Cauchy-vanishing**: for a closed rectangle `[z,w]` inside the zero-free strip
    `{Re s > 0 ∧ L(s,χ) ≠ 0}` (`χ ≠ 1`), the smoothed-Perron integrand's boundary integral vanishes
    (Cauchy–Goursat, `integral_boundary_rect_eq_zero_of_differentiableOn` +
    `smoothed_integrand_differentiableOn`). Equating the two vertical sides (as `T → ∞`, the
    horizontal sides `→0` by `perron_kernel_decay`) gives the contour shift `∫_{(σ)} = ∫_{(σ')}`
    for `χ ≠ 1` — the heart of B3. -/
lemma smoothed_integrand_rect_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (X : ℝ) (hX : 0 < X) (z w : ℂ)
    (hrect : Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)
      ⊆ {s : ℂ | 0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0}) :
    (∫ x : ℝ in z.re..w.re,
        (-deriv (DirichletCharacter.LFunction χ) (x + z.im * I) / DirichletCharacter.LFunction χ (x + z.im * I))
          * ((X : ℂ) ^ ((x : ℂ) + z.im * I) / (((x : ℂ) + z.im * I) * ((x : ℂ) + z.im * I + 1))))
      - (∫ x : ℝ in z.re..w.re,
        (-deriv (DirichletCharacter.LFunction χ) (x + w.im * I) / DirichletCharacter.LFunction χ (x + w.im * I))
          * ((X : ℂ) ^ ((x : ℂ) + w.im * I) / (((x : ℂ) + w.im * I) * ((x : ℂ) + w.im * I + 1))))
      + I • (∫ y : ℝ in z.im..w.im,
        (-deriv (DirichletCharacter.LFunction χ) (w.re + y * I) / DirichletCharacter.LFunction χ (w.re + y * I))
          * ((X : ℂ) ^ ((w.re : ℂ) + y * I) / (((w.re : ℂ) + y * I) * ((w.re : ℂ) + y * I + 1))))
      - I • (∫ y : ℝ in z.im..w.im,
        (-deriv (DirichletCharacter.LFunction χ) (z.re + y * I) / DirichletCharacter.LFunction χ (z.re + y * I))
          * ((X : ℂ) ^ ((z.re : ℂ) + y * I) / (((z.re : ℂ) + y * I) * ((z.re : ℂ) + y * I + 1))))
      = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn _ z w
    ((smoothed_integrand_differentiableOn χ hχ X hX).mono hrect)

/-- **Integrand continuity on the vertical line `Re = σ > 1`** (SW brick B3 input): `t ↦ F(σ+it)` is
    continuous (the integrand is holomorphic on `{Re>0 ∧ L≠0}`; the line `Re=σ>1` lies inside it by
    `LFunction_ne_zero_re_ge_one`). Prerequisite for the vertical Perron integral and its `T→∞` limit. -/
lemma integrand_continuous_on_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (X : ℝ) (hX : 0 < X) (σ : ℝ) (hσ : 1 < σ) :
    Continuous (fun t : ℝ =>
      (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + t * I))
        * ((X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)))) := by
  apply (smoothed_integrand_differentiableOn χ hχ X hX).continuousOn.comp_continuous
    (by fun_prop)
  intro t
  refine ⟨?_, ?_⟩
  · simp
    linarith
  · exact LFunction_ne_zero_re_ge_one χ hχ (by simp; linarith)

/-- **`−L′/L` uniformly bounded on the line `Re = σ > 1`** (SW brick B3 input): `‖−L′/L(σ+it,χ)‖ ≤
    ∑_n Λ(n)/n^σ` for all `t` (a constant `B_σ`). Via `neg_logDeriv_LFunction_eq` (= the χ·Λ Dirichlet
    series) + `norm_tsum_le_tsum_norm` + `norm_term_eq` (the term norm depends only on `Re s = σ`).
    With `perron_kernel_decay` (`1/t²`) this makes the vertical integrand integrable on `Re = σ`. -/
lemma neg_logDeriv_bounded_on_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (σ : ℝ) (hσ : 1 < σ) :
    ∃ B : ℝ, ∀ t : ℝ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤ B := by
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n‖, fun t => ?_⟩
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have hs : 1 < ((σ : ℂ) + t * I).re := by rw [hre]; exact hσ
  rw [neg_logDeriv_LFunction_eq χ hs]
  have hsummable : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs)
  calc ‖LSeries (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm hsummable
    _ = ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (σ : ℂ) n‖ := by
        apply tsum_congr; intro n
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hre, Complex.ofReal_re]

open MeasureTheory in
/-- **Vertical-integrand integrability on `Re = σ > 1`** (SW brick B3): the smoothed-Perron integrand
    `t ↦ F(σ+it)` is integrable over `ℝ`. Domination: `‖F‖ = ‖−L′/L‖·‖kernel‖ ≤ B·X^σ/(σ²+t²) ≤
    B·X^σ/(1+t²)` (`neg_logDeriv_bounded_on_line`, `perron_kernel_norm`, `‖s‖‖s+1‖ ≥ σ²+t²` via
    `norm_add_mul_I`, and `σ²≥1`), dominated by the integrable `B·X^σ·(1+t²)⁻¹`
    (`integrable_inv_one_add_sq`). So the vertical Perron integral is a well-defined Bochner integral. -/
lemma integrand_integrable_on_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (X : ℝ) (hX : 0 < X) (σ : ℝ) (hσ : 1 < σ) :
    Integrable (fun t : ℝ =>
      (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + t * I))
        * ((X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1)))) := by
  obtain ⟨B, hB⟩ := neg_logDeriv_bounded_on_line χ σ hσ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hXσ0 : 0 ≤ X ^ σ := Real.rpow_nonneg hX.le _
  refine Integrable.mono' (g := fun t : ℝ => B * X ^ σ * (1 + t ^ 2)⁻¹) ?_
    (integrand_continuous_on_line χ hχ X hX σ hσ).aestronglyMeasurable ?_
  · exact integrable_inv_one_add_sq.const_mul (B * X ^ σ)
  · apply Filter.Eventually.of_forall
    intro t
    have hknorm : ‖(X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1))‖
        = X ^ σ / (‖(σ : ℂ) + t * I‖ * ‖(σ : ℂ) + t * I + 1‖) := by
      rw [perron_kernel_norm X hX]; congr 1; simp
    have hden : σ ^ 2 + t ^ 2 ≤ ‖(σ : ℂ) + ↑t * I‖ * ‖(σ : ℂ) + ↑t * I + 1‖ := by
      have e1 : ‖(σ : ℂ) + ↑t * I‖ = Real.sqrt (σ ^ 2 + t ^ 2) := Complex.norm_add_mul_I σ t
      have e2 : (σ : ℂ) + ↑t * I + 1 = ((σ + 1 : ℝ) : ℂ) + ↑t * I := by push_cast; ring
      have e3 : ‖(σ : ℂ) + ↑t * I + 1‖ = Real.sqrt ((σ + 1) ^ 2 + t ^ 2) := by
        rw [e2]; exact Complex.norm_add_mul_I _ _
      rw [e1, e3]
      have h4 : Real.sqrt (σ ^ 2 + t ^ 2) ≤ Real.sqrt ((σ + 1) ^ 2 + t ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      calc σ ^ 2 + t ^ 2 = Real.sqrt (σ ^ 2 + t ^ 2) * Real.sqrt (σ ^ 2 + t ^ 2) :=
            (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ Real.sqrt (σ ^ 2 + t ^ 2) * Real.sqrt ((σ + 1) ^ 2 + t ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
    have hσ2 : (0 : ℝ) < σ ^ 2 + t ^ 2 := by nlinarith [hσ, sq_nonneg t]
    have hle1 : (1 : ℝ) + t ^ 2 ≤ σ ^ 2 + t ^ 2 := by nlinarith
    calc ‖(-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + ↑t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + ↑t * I))
            * ((X : ℂ) ^ ((σ : ℂ) + ↑t * I) / (((σ : ℂ) + ↑t * I) * ((σ : ℂ) + ↑t * I + 1)))‖
        = ‖(-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + ↑t * I) / DirichletCharacter.LFunction χ ((σ : ℂ) + ↑t * I))‖
            * ‖(X : ℂ) ^ ((σ : ℂ) + ↑t * I) / (((σ : ℂ) + ↑t * I) * ((σ : ℂ) + ↑t * I + 1))‖ := norm_mul _ _
      _ ≤ B * (X ^ σ / (σ ^ 2 + t ^ 2)) := by
          rw [hknorm]
          refine mul_le_mul (hB t) ?_ (by positivity) hB0
          exact div_le_div_of_nonneg_left hXσ0 hσ2 hden
      _ ≤ B * X ^ σ * (1 + t ^ 2)⁻¹ := by
          rw [← mul_div_assoc, ← div_eq_mul_inv]
          exact div_le_div_of_nonneg_left (mul_nonneg hB0 hXσ0) (by positivity) hle1

open MeasureTheory intervalIntegral in
/-- **Horizontal connector bound** (SW brick B3): the top/bottom sides of the B3 rectangle at height
    `T` are `O(X^σ/T²)`: `‖∫_{σ'}^{σ} F(x+iT)‖ ≤ (σ−σ')·M·X^σ/T²`, given a uniform `‖−L′/L‖ ≤ M`
    bound on the segment (from `contour_logDeriv_bound`, `M = C·N^ε·L_T²` polylog). Via
    `perron_kernel_decay` (`‖kernel‖ ≤ X^x/T²`) + `X^x ≤ X^σ` (`X≥1`, `x≤σ`) +
    `norm_integral_le_of_norm_le_const`. Drives the connectors `→0` as `T→∞` (polylog `M`, `1/T²`). -/
lemma horizontal_connector_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X : ℝ) (hX1 : 1 ≤ X) (σ' σ T M : ℝ) (hσ'σ : σ' ≤ σ) (hT : T ≠ 0) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.uIcc σ' σ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I)‖ ≤ M) :
    ‖∫ x : ℝ in σ'..σ,
        (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I))
          * ((X : ℂ) ^ ((x : ℂ) + T * I) / (((x : ℂ) + T * I) * ((x : ℂ) + T * I + 1)))‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hT2 : (0 : ℝ) < T ^ 2 := (sq_nonneg T).lt_of_ne (Ne.symm (pow_ne_zero 2 hT))
  have hkey : ∀ x ∈ Set.uIcc σ' σ,
      ‖(-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I))
          * ((X : ℂ) ^ ((x : ℂ) + T * I) / (((x : ℂ) + T * I) * ((x : ℂ) + T * I + 1)))‖
        ≤ M * X ^ σ / T ^ 2 := by
    intro x hx
    have hxσ : x ≤ σ := (Set.uIcc_of_le hσ'σ ▸ hx : x ∈ Set.Icc σ' σ).2
    have him : ((x : ℂ) + T * I).im = T := by simp
    have hre : ((x : ℂ) + T * I).re = x := by simp
    have hkd := perron_kernel_decay X hX0 ((x : ℂ) + T * I) (by rw [him]; exact hT)
    rw [hre, him] at hkd
    have h3 : X ^ x ≤ X ^ σ := Real.rpow_le_rpow_of_exponent_le hX1 hxσ
    have hdiv : X ^ x / T ^ 2 ≤ X ^ σ / T ^ 2 := by gcongr
    rw [norm_mul]
    calc ‖-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I)‖
            * ‖(X : ℂ) ^ ((x : ℂ) + T * I) / (((x : ℂ) + T * I) * ((x : ℂ) + T * I + 1))‖
        ≤ M * (X ^ x / T ^ 2) := mul_le_mul (hM x hx) hkd (norm_nonneg _) hM0
      _ ≤ M * (X ^ σ / T ^ 2) := mul_le_mul_of_nonneg_left hdiv hM0
      _ = M * X ^ σ / T ^ 2 := by ring
  calc ‖∫ x : ℝ in σ'..σ,
          (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + T * I) / DirichletCharacter.LFunction χ ((x : ℂ) + T * I))
            * ((X : ℂ) ^ ((x : ℂ) + T * I) / (((x : ℂ) + T * I) * ((x : ℂ) + T * I + 1)))‖
      ≤ (M * X ^ σ / T ^ 2) * |σ - σ'| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun x hx => hkey x (Set.uIoc_subset_uIcc hx))
    _ = (σ - σ') * (M * X ^ σ / T ^ 2) := by
        rw [abs_of_nonneg (by linarith)]; ring

open MeasureTheory Filter Topology in
/-- **Truncated → full vertical integral** (SW brick B3): `∫_{-T}^{T} g → ∫_ℝ g` as `T → ∞` for
    integrable `g` — the right/left sides of the B3 rectangle converge to the full vertical Perron
    integrals. Via `tendsto_setIntegral_of_monotone` over `Ioc(-T,T) ↗ univ`. Applied with
    `g = F(σ+·i)` (`integrand_integrable_on_line`) and `g = F(σ'+·i)`, plus the horizontal connectors
    `→0` (`horizontal_connector_bound`), the rectangle identity `smoothed_integrand_rect_zero` yields
    the contour shift `∫_{(σ)} = ∫_{(σ')}` in the limit. -/
lemma vertical_integral_tendsto (g : ℝ → ℂ) (hg : Integrable g) :
    Tendsto (fun T : ℝ => ∫ y in (-T)..T, g y) atTop (𝓝 (∫ y, g y)) := by
  have hunion : (⋃ T : ℝ, Set.Ioc (-T) T) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_univ, iff_true]
    exact ⟨|x| + 1, by have := neg_abs_le x; linarith, by have := le_abs_self x; linarith⟩
  have hmono : Monotone (fun T : ℝ => Set.Ioc (-T) T) := by
    intro a b hab; apply Set.Ioc_subset_Ioc <;> linarith
  have hint : IntegrableOn g (⋃ T : ℝ, Set.Ioc (-T) T) := by rw [hunion]; exact hg.integrableOn
  have key := tendsto_setIntegral_of_monotone (fun T : ℝ => measurableSet_Ioc) hmono hint
  rw [hunion, MeasureTheory.setIntegral_univ] at key
  refine key.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact (intervalIntegral.integral_of_le (by linarith : -T ≤ T)).symm

/-- **Orthogonality character-sum bound** (SW brick B5): `‖∑_χ χ(a)·f(χ)‖ ≤ ∑_χ ‖f(χ)‖` — Dirichlet
    character values have norm ≤ 1 (`norm_le_one`). Applied to `psi_ap_orthogonality` with
    `f χ = ψ(X,χ)`, this reduces the AP prime-count error `φ(q)·∑_{n≡a}Λ − ⋯` to the sum of
    per-character `ψ(X,χ)` bounds (the χ₀ main term `X` + the χ≠1 SW rate), completing the B5 assembly
    skeleton for `siegel_walfisz`. -/
lemma char_sum_norm_le {q : ℕ} [NeZero q] (a : ZMod q) (f : DirichletCharacter ℂ q → ℂ) :
    ‖∑ χ : DirichletCharacter ℂ q, χ a * f χ‖ ≤ ∑ χ : DirichletCharacter ℂ q, ‖f χ‖ := by
  calc ‖∑ χ : DirichletCharacter ℂ q, χ a * f χ‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ a * f χ‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖f χ‖ := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        calc ‖χ a‖ * ‖f χ‖ ≤ 1 * ‖f χ‖ :=
              mul_le_mul_of_nonneg_right (norm_le_one χ a) (norm_nonneg _)
          _ = ‖f χ‖ := one_mul _

/-- **B5 principal-character separation**: `‖∑_χ χ(a)·f(χ)‖ ≤ ‖f(1)‖ + ∑_{χ≠1} ‖f(χ)‖`. Isolates the
    principal character `χ₀=1` (whose `ψ(X,χ₀)` carries the main term `X`) from the nontrivial
    characters (whose `ψ(X,χ)` is `O(SW rate)`). The B5 reduction shape for `siegel_walfisz`:
    `‖φ(q)·(AP count) − X‖ ≤ ‖ψ(X,χ₀)−X‖ + ∑_{χ≠1}‖ψ(X,χ)‖`. -/
lemma char_sum_norm_le_split {q : ℕ} [NeZero q] (a : ZMod q) (f : DirichletCharacter ℂ q → ℂ) :
    ‖∑ χ : DirichletCharacter ℂ q, χ a * f χ‖
      ≤ ‖f 1‖ + ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)), ‖f χ‖ := by
  refine le_trans (char_sum_norm_le a f) ?_
  rw [← Finset.add_sum_erase Finset.univ (fun χ => ‖f χ‖) (Finset.mem_univ 1)]

/-- **B5 reduction** (SW brick B5c): `‖∑_χ χ(a)·f(χ)‖ ≤ ‖f(1)‖ + (#χ − 1)·R` given a uniform bound
    `R` on the nontrivial characters. With `f χ = ψ(X,χ)` and `psi_ap_orthogonality`, this reduces
    the AP prime-count error to the χ₀ main-term error `‖ψ(X,χ₀)−X‖` plus `(φ(q)−1)×` the SW rate —
    dividing by `φ(q)` then gives the `siegel_walfisz` statement shape. -/
lemma char_sum_reduction {q : ℕ} [NeZero q] (a : ZMod q) (R : ℝ) (hR : 0 ≤ R)
    (f : DirichletCharacter ℂ q → ℂ) (hf : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖f χ‖ ≤ R) :
    ‖∑ χ : DirichletCharacter ℂ q, χ a * f χ‖
      ≤ ‖f 1‖ + (Fintype.card (DirichletCharacter ℂ q) - 1 : ℕ) * R := by
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
      = Fintype.card (DirichletCharacter ℂ q) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hbound : ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)), ‖f χ‖
      ≤ (Fintype.card (DirichletCharacter ℂ q) - 1 : ℕ) * R := by
    calc ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)), ‖f χ‖
        ≤ (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card • R :=
          Finset.sum_le_card_nsmul _ _ _ (fun χ hχ => hf χ (Finset.ne_of_mem_erase hχ))
      _ = (Fintype.card (DirichletCharacter ℂ q) - 1 : ℕ) * R := by rw [hcard, nsmul_eq_mul]
  linarith [char_sum_norm_le_split a f, hbound]

open MeasureTheory in
/-- **Truncation tail bound** (SW brick W1a): for integrable `g` with `‖g(t)‖ ≤ C/t²` off `0`,
    `‖∫_ℝ g − ∫_{-T}^{T} g‖ ≤ 2C/T`. The quantitative σ-line truncation error for the B3 finite-T
    rectangle assembly (`g = F(σ+it)`, `C = B_σ·X^σ` via `neg_logDeriv_bounded_on_line` +
    `perron_kernel_decay`) — ties `smoothed_perron_LFunction`'s full vertical integral to the
    truncated one appearing in `smoothed_integrand_rect_zero`. -/
lemma truncation_tail_bound (g : ℝ → ℂ) (hg : Integrable g) (C T : ℝ) (hT : 0 < T)
    (hbound : ∀ t : ℝ, t ≠ 0 → ‖g t‖ ≤ C / t ^ 2) :
    ‖(∫ t, g t) - ∫ t in (-T)..T, g t‖ ≤ 2 * C / T := by
  have hC : 0 ≤ C := by
    have h1 := hbound 1 one_ne_zero
    have h2 : (0:ℝ) ≤ ‖g 1‖ := norm_nonneg _
    have h3 : C / (1:ℝ) ^ 2 = C := by norm_num
    linarith [h3 ▸ h1]
  have tailR : ∀ h : ℝ → ℂ, (∀ x ∈ Set.Ioi T, ‖h x‖ ≤ C / x ^ 2) →
      ‖∫ x in Set.Ioi T, h x‖ ≤ C / T := by
    intro h hh
    have h1 := MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi T)) h
    have hgi : Integrable (fun x : ℝ => C * x ^ (-2:ℝ)) (volume.restrict (Set.Ioi T)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul C
    have h2 : (∫ x in Set.Ioi T, ‖h x‖) ≤ ∫ x in Set.Ioi T, C * x ^ (-2:ℝ) := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => norm_nonneg _
      · exact hgi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := lt_trans hT hx
        have e : x ^ (-2:ℝ) = ((x : ℝ) ^ (2:ℕ))⁻¹ := by
          rw [Real.rpow_neg hx0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [e, ← div_eq_mul_inv]
        exact hh x hx
    have h3 : ∫ x in Set.Ioi T, C * x ^ (-2:ℝ) = C / T := by
      rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT,
        show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring
    linarith
  have hadd := MeasureTheory.integral_add_compl
    (measurableSet_Ioc : MeasurableSet (Set.Ioc (-T) T)) hg
  have hdiff : (∫ t, g t) - (∫ t in Set.Ioc (-T) T, g t) = ∫ t in (Set.Ioc (-T) T)ᶜ, g t := by
    rw [← hadd]; ring
  have hcompl : (Set.Ioc (-T) T)ᶜ = Set.Iic (-T) ∪ Set.Ioi T := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Iic, Set.mem_Ioi]
    push_neg
    constructor
    · intro hx
      by_cases h : -T < x
      · exact Or.inr (hx h)
      · exact Or.inl (by linarith [not_lt.mp h])
    · intro hx h1
      rcases hx with h | h
      · linarith
      · linarith
  have hdisj : Disjoint (Set.Iic (-T)) (Set.Ioi T) := Set.Iic_disjoint_Ioi (by linarith)
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T), hdiff, hcompl,
    MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hg.integrableOn hg.integrableOn]
  have hleft : ‖∫ t in Set.Iic (-T), g t‖ ≤ C / T := by
    rw [← integral_comp_neg_Ioi]
    apply tailR
    intro x hx
    have hx0 : 0 < x := lt_trans hT hx
    have hb := hbound (-x) (by simpa using hx0.ne')
    rwa [show (-x) ^ 2 = x ^ 2 by ring] at hb
  have hright : ‖∫ t in Set.Ioi T, g t‖ ≤ C / T := by
    apply tailR
    intro x hx
    exact hbound x (ne_of_gt (lt_trans hT hx))
  calc ‖(∫ t in Set.Iic (-T), g t) + ∫ t in Set.Ioi T, g t‖
      ≤ ‖∫ t in Set.Iic (-T), g t‖ + ‖∫ t in Set.Ioi T, g t‖ := norm_add_le _ _
    _ ≤ C / T + C / T := add_le_add hleft hright
    _ = 2 * C / T := by ring

open MeasureTheory in
/-- **Shifted-line integral bound** (SW brick W1b): if `‖F(t)‖ ≤ M·Xσ/(σ'²+t²)` on `(-T,T]` with
    `σ' ≥ 3/4`, then `‖∫_{-T}^{T} F‖ ≤ 6·M·Xσ`. -/
lemma shifted_line_integral_bound (F : ℝ → ℂ) (M Xσ σ' T : ℝ)
    (hM : 0 ≤ M) (hXσ : 0 ≤ Xσ) (hσ' : 3/4 ≤ σ') (hT : 0 ≤ T)
    (hpt : ∀ t : ℝ, t ∈ Set.Ioc (-T) T → ‖F t‖ ≤ M * Xσ / (σ' ^ 2 + t ^ 2)) :
    ‖∫ t in (-T)..T, F t‖ ≤ 6 * M * Xσ := by
  have hd1 : ∀ t : ℝ, (0:ℝ) < σ' ^ 2 + t ^ 2 := fun t => by nlinarith [sq_nonneg t]
  have hd2 : ∀ t : ℝ, (0:ℝ) < 1 + t ^ 2 := fun t => by nlinarith [sq_nonneg t]
  have hgcont : Continuous (fun t : ℝ => M * Xσ / (σ' ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun t => (hd1 t).ne')
  have hhcont : Continuous (fun t : ℝ => 16/9 * (M * Xσ) * (1 + t ^ 2)⁻¹) :=
    continuous_const.mul (Continuous.inv₀ (by fun_prop) (fun t => (hd2 t).ne'))
  have step1 := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
    (Filter.Eventually.of_forall hpt) (hgcont.intervalIntegrable (μ := volume) (-T) T)
  have step2 : (∫ t in (-T)..T, M * Xσ / (σ' ^ 2 + t ^ 2))
      ≤ ∫ t in (-T)..T, 16/9 * (M * Xσ) * (1 + t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (hgcont.intervalIntegrable (μ := volume) (-T) T) (hhcont.intervalIntegrable (μ := volume) (-T) T)
    intro t _
    have h9 : 9/16 * (1 + t ^ 2) ≤ σ' ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
    calc M * Xσ / (σ' ^ 2 + t ^ 2) ≤ M * Xσ / (9/16 * (1 + t ^ 2)) :=
          div_le_div_of_nonneg_left (mul_nonneg hM hXσ) (by nlinarith [hd2 t]) h9
      _ = 16/9 * (M * Xσ) * (1 + t ^ 2)⁻¹ := by
          field_simp
  have step3 : (∫ t in (-T)..T, 16/9 * (M * Xσ) * (1 + t ^ 2)⁻¹)
      = 16/9 * (M * Xσ) * ∫ t in (-T)..T, (1 + t ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
  have step4 : (∫ t in (-T)..T, (1 + t ^ 2)⁻¹) ≤ Real.pi := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    calc (∫ t in Set.Ioc (-T) T, (1 + t ^ 2)⁻¹)
        ≤ ∫ t : ℝ, (1 + t ^ 2)⁻¹ := by
          apply MeasureTheory.setIntegral_le_integral integrable_inv_one_add_sq
          exact Filter.Eventually.of_forall (fun t => by positivity)
      _ = Real.pi := integral_univ_inv_one_add_sq
  have h0 : 0 ≤ M * Xσ := mul_nonneg hM hXσ
  have hInn : (0:ℝ) ≤ ∫ t in (-T)..T, (1 + t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t _
    positivity
  have step5 : 16/9 * (M * Xσ) * (∫ t in (-T)..T, (1 + t ^ 2)⁻¹) ≤ 6 * M * Xσ := by
    have hπ : Real.pi < 3.15 := Real.pi_lt_d2
    calc 16/9 * (M * Xσ) * (∫ t in (-T)..T, (1 + t ^ 2)⁻¹)
        ≤ 16/9 * (M * Xσ) * Real.pi := by
          apply mul_le_mul_of_nonneg_left step4 (by positivity)
      _ ≤ 6 * M * Xσ := by nlinarith [Real.pi_pos]
  linarith [step1, step2, step3.le, step3.ge, step5]

/-- **Integrand pointwise bound on a shifted line** (SW brick W1c): given `‖−L′/L(σ'+it)‖ ≤ M`,
    the smoothed integrand satisfies `‖F(σ'+it)‖ ≤ M·X^{σ'}/(σ'²+t²)` — exactly the input to
    `shifted_line_integral_bound`. -/
lemma integrand_pointwise_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X σ' t M : ℝ) (hX : 0 < X) (hσ'0 : 0 < σ') (hM : 0 ≤ M)
    (hLL : ‖-deriv (DirichletCharacter.LFunction χ) ((σ' : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ' : ℂ) + t * I)‖ ≤ M) :
    ‖(-deriv (DirichletCharacter.LFunction χ) ((σ' : ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ' : ℂ) + t * I))
        * ((X : ℂ) ^ ((σ' : ℂ) + t * I) / (((σ' : ℂ) + t * I) * ((σ' : ℂ) + t * I + 1)))‖
      ≤ M * X ^ σ' / (σ' ^ 2 + t ^ 2) := by
  have hknorm : ‖(X : ℂ) ^ ((σ' : ℂ) + t * I) / (((σ' : ℂ) + t * I) * ((σ' : ℂ) + t * I + 1))‖
      = X ^ σ' / (‖(σ' : ℂ) + t * I‖ * ‖(σ' : ℂ) + t * I + 1‖) := by
    rw [perron_kernel_norm X hX]; congr 1; simp
  have hden : σ' ^ 2 + t ^ 2 ≤ ‖(σ' : ℂ) + ↑t * I‖ * ‖(σ' : ℂ) + ↑t * I + 1‖ := by
    have e1 : ‖(σ' : ℂ) + ↑t * I‖ = Real.sqrt (σ' ^ 2 + t ^ 2) := Complex.norm_add_mul_I σ' t
    have e2 : (σ' : ℂ) + ↑t * I + 1 = ((σ' + 1 : ℝ) : ℂ) + ↑t * I := by push_cast; ring
    have e3 : ‖(σ' : ℂ) + ↑t * I + 1‖ = Real.sqrt ((σ' + 1) ^ 2 + t ^ 2) := by
      rw [e2]; exact Complex.norm_add_mul_I _ _
    rw [e1, e3]
    have h4 : Real.sqrt (σ' ^ 2 + t ^ 2) ≤ Real.sqrt ((σ' + 1) ^ 2 + t ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    calc σ' ^ 2 + t ^ 2 = Real.sqrt (σ' ^ 2 + t ^ 2) * Real.sqrt (σ' ^ 2 + t ^ 2) :=
          (Real.mul_self_sqrt (by positivity)).symm
      _ ≤ Real.sqrt (σ' ^ 2 + t ^ 2) * Real.sqrt ((σ' + 1) ^ 2 + t ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _)
  have hσt : (0:ℝ) < σ' ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  rw [norm_mul, hknorm]
  calc ‖-deriv (DirichletCharacter.LFunction χ) ((σ' : ℂ) + ↑t * I) / DirichletCharacter.LFunction χ ((σ' : ℂ) + ↑t * I)‖
        * (X ^ σ' / (‖(σ' : ℂ) + ↑t * I‖ * ‖(σ' : ℂ) + ↑t * I + 1‖))
      ≤ M * (X ^ σ' / (σ' ^ 2 + t ^ 2)) := by
        apply mul_le_mul hLL ?_ (by positivity) hM
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hX.le _) hσt hden
    _ = M * X ^ σ' / (σ' ^ 2 + t ^ 2) := by ring

open MeasureTheory in
/-- **W1 capstone (abstract rectangle assembly)**: given the smoothed-Perron representation
    `S = (1/2π)·∫_ℝ G(σ+it)`, the σ-line truncation error `Ct`, the rectangle identity, connector
    bounds `Cc`, and the shifted-line bound `Cs`, conclude `‖S‖ ≤ (Cs + 2Cc + Ct)/(2π)`. -/
lemma rectangle_assembly (S : ℂ) (G : ℂ → ℂ) (σ' σ T Ct Cc Cs : ℝ)
    (h1 : S = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I))
    (h2 : ‖(∫ t : ℝ, G ((σ : ℂ) + t * Complex.I))
        - ∫ t in (-T)..T, G ((σ : ℂ) + t * Complex.I)‖ ≤ Ct)
    (h3 : (∫ x in σ'..σ, G ((x:ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x in σ'..σ, G ((x:ℂ) + ((T:ℝ) : ℂ) * Complex.I))
        + Complex.I • (∫ y in (-T)..T, G ((σ:ℂ) + (y:ℂ) * Complex.I))
        - Complex.I • (∫ y in (-T)..T, G ((σ':ℂ) + (y:ℂ) * Complex.I)) = 0)
    (h4 : ‖∫ x in σ'..σ, G ((x:ℂ) + ((T:ℝ) : ℂ) * Complex.I)‖ ≤ Cc)
    (h5 : ‖∫ x in σ'..σ, G ((x:ℂ) + ((-T:ℝ) : ℂ) * Complex.I)‖ ≤ Cc)
    (h6 : ‖∫ y in (-T)..T, G ((σ':ℂ) + (y:ℂ) * Complex.I)‖ ≤ Cs) :
    ‖S‖ ≤ (Cs + 2 * Cc + Ct) / (2 * Real.pi) := by
  set Full := ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) with hFull
  set R := ∫ y in (-T)..T, G ((σ:ℂ) + (y:ℂ) * Complex.I) with hRdef
  set L := ∫ y in (-T)..T, G ((σ':ℂ) + (y:ℂ) * Complex.I) with hLdef
  set Btm := ∫ x in σ'..σ, G ((x:ℂ) + ((-T:ℝ) : ℂ) * Complex.I) with hBdef
  set Top := ∫ x in σ'..σ, G ((x:ℂ) + ((T:ℝ) : ℂ) * Complex.I) with hTdef
  rw [smul_eq_mul, smul_eq_mul] at h3
  have h7 : Complex.I * R = Complex.I * L + (Top - Btm) := by linear_combination h3
  have hR : ‖R‖ ≤ Cs + 2 * Cc := by
    have h8 : ‖Complex.I * R‖ = ‖R‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    have h9 : ‖Complex.I * L‖ = ‖L‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    calc ‖R‖ = ‖Complex.I * R‖ := h8.symm
      _ = ‖Complex.I * L + (Top - Btm)‖ := by rw [h7]
      _ ≤ ‖Complex.I * L‖ + ‖Top - Btm‖ := norm_add_le (Complex.I * L) (Top - Btm)
      _ ≤ ‖L‖ + (‖Top‖ + ‖Btm‖) := by
          rw [h9]
          exact add_le_add le_rfl (norm_sub_le Top Btm)
      _ ≤ Cs + (Cc + Cc) := add_le_add h6 (add_le_add h4 h5)
      _ = Cs + 2 * Cc := by ring
  have hfull : ‖Full‖ ≤ Cs + 2 * Cc + Ct := by
    have hsplit : Full = (Full - R) + R := by ring
    calc ‖Full‖ = ‖(Full - R) + R‖ := by rw [← hsplit]
      _ ≤ ‖Full - R‖ + ‖R‖ := norm_add_le (Full - R) R
      _ ≤ Ct + (Cs + 2 * Cc) := add_le_add h2 hR
      _ = Cs + 2 * Cc + Ct := by ring
  have hnrm : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  rw [h1, norm_mul, hnrm]
  calc 1 / (2 * Real.pi) * ‖Full‖ = ‖Full‖ / (2 * Real.pi) := by ring
    _ ≤ (Cs + 2 * Cc + Ct) / (2 * Real.pi) := by gcongr

/-- **Zero-free strip** (SW brick W1d): `L(s,χ) ≠ 0` on the contour strip
    `Re s ≥ 1 − g/2`, `|Im s| ≤ T` — a zero there would contradict its own distance bound
    (`contour_zero_distance` at `ρ = s`: `0 = ‖s−s‖ ≥ g/2 > 0`). Gives the non-vanishing half of
    the `smoothed_integrand_rect_zero` rectangle hypothesis. -/
lemma LFunction_ne_zero_in_strip (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ, |s.im| ≤ T →
    1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re →
    DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := contour_zero_distance ε hε0
  refine ⟨c, hc0, ?_⟩
  intro N _ χ hχ1 T hT0 s hsim hsre hzero
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hkey := hc N χ hχ1 T hT0 s hsim hsre s hzero (by simp)
  have hLT : (0:ℝ) < Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 := by
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) := Real.log_nonneg (by nlinarith)
    linarith
  have hg0 : (0:ℝ) < c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 := by
    have hNe : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  simp only [sub_self, norm_zero] at hkey
  linarith

/-- **Combined contour data** (SW brick W1e): ONE constant `c` under which the strip
    `1 − g/2 ≤ Re s ≤ 1 + g`, `|Im s| ≤ T` (`g = c·N^{−ε}/L_T`) is simultaneously zero-free and
    carries the `‖L′/L‖ ≤ C·N^ε·L_T²` bound. `c := min c₁ c₂` + strip monotonicity (a narrower strip
    inherits both properties). Resolves the two independent existentials for the W1 instantiation. -/
lemma contour_combined (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 1 ≤ C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ, |s.im| ≤ T →
    1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2 ≤ s.re →
    DirichletCharacter.LFunction χ s ≠ 0 ∧
    (s.re ≤ 1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖
        ≤ C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2) := by
  obtain ⟨c₁, hc₁0, hzf⟩ := LFunction_ne_zero_in_strip ε hε0
  obtain ⟨c₂, C, hc₂0, hc₂12, hC1, hLL⟩ := contour_logDeriv_bound ε hε0
  refine ⟨min c₁ c₂, C, lt_min hc₁0 hc₂0, le_trans (min_le_right _ _) hc₂12, hC1, ?_⟩
  intro N _ χ hχ1 T hT0 s hsim hsre
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNe : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hLT : (0:ℝ) < Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 := by
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) := Real.log_nonneg (by nlinarith)
    linarith
  have hfac : (0:ℝ) < ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) := by positivity
  have hmono1 : min c₁ c₂ * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)
      ≤ c₁ * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) := by
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hNe.le) hLT.le
  have hmono2 : min c₁ c₂ * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)
      ≤ c₂ * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) := by
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hNe.le) hLT.le
  constructor
  · exact hzf N χ hχ1 T hT0 s hsim (by linarith)
  · intro hsre2
    exact hLL N χ hχ1 T hT0 s hsim (by linarith) (by linarith)

/-- **`−L′/L` ↔ `logDeriv` norm bridge** (SW brick W1f): `‖−deriv L/L‖ = ‖logDeriv L‖`, so
    `contour_combined`'s `logDeriv` bound transfers to the smoothed-integrand form. -/
lemma neg_logDeriv_norm_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
  rw [logDeriv_apply, neg_div, norm_neg]

/-- **Strip numerics** (SW brick W1g): with `0 < c ≤ 1/2`, `0 < Ne ≤ 1`, `20 ≤ LT`, the gap
    `g = c·Ne/LT` satisfies `0 < g ≤ 1/40`, so `σ' = 1−g/2 ≥ 3/4` (`shifted_line_integral_bound`'s
    hypothesis), `σ = 1+g ∈ (1,2]`, and `σ' ≤ σ`. The arithmetic inputs of the W1 instantiation. -/
lemma strip_numerics (c Ne LT : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1/2)
    (hNe0 : 0 < Ne) (hNe1 : Ne ≤ 1) (hLT : 20 ≤ LT) :
    0 < c * Ne / LT ∧ c * Ne / LT ≤ 1/40 ∧ 3/4 ≤ 1 - c * Ne / LT / 2 ∧
      1 < 1 + c * Ne / LT ∧ 1 - c * Ne / LT / 2 ≤ 1 + c * Ne / LT ∧ 1 + c * Ne / LT ≤ 2 := by
  have hLT0 : (0:ℝ) < LT := by linarith
  have hg0 : 0 < c * Ne / LT := by positivity
  have hgle : c * Ne / LT ≤ 1/40 := by
    rw [div_le_iff₀ hLT0]
    nlinarith
  refine ⟨hg0, hgle, by linarith, by linarith, by linarith, by linarith⟩

/-- **σ-line tail constant** (SW brick W1h): the smoothed integrand on `Re = σ > 1` is dominated by
    `(B·X^σ)/t²` off `t = 0` — the exact `hbound` input of `truncation_tail_bound`. -/
lemma sigma_line_tail_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, t ≠ 0 →
      ‖(-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I))
          * ((X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1)))‖
        ≤ (B * X ^ σ) / t ^ 2 := by
  obtain ⟨B, hB⟩ := neg_logDeriv_bounded_on_line χ σ hσ
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨B, hB0, fun t ht => ?_⟩
  have him : ((σ:ℂ) + t * I).im = t := by simp
  have hre : ((σ:ℂ) + t * I).re = σ := by simp
  have hkd := perron_kernel_decay X hX ((σ:ℂ) + t * I) (by rw [him]; exact ht)
  rw [hre, him] at hkd
  rw [norm_mul]
  calc ‖-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I)‖
        * ‖(X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))‖
      ≤ B * (X ^ σ / t ^ 2) := mul_le_mul (hB t) hkd (norm_nonneg _) hB0
    _ = (B * X ^ σ) / t ^ 2 := by ring

/-- **Strip-point `M`-bound in integrand form** (SW brick W1i): given `contour_combined`'s
    `logDeriv` bound as a hypothesis (fixed constants; `T` = height, `[rlo, rhi]` = Re-range),
    every strip point `x + t·I` (`|t| ≤ T`, `rlo ≤ x ≤ rhi`) has `‖−L′/L(x+t·I)‖ ≤ M`. One
    packaging for BOTH the horizontal connectors (`t = ±T`) and the shifted vertical line
    (`x = σ'`, `t ∈ (−T,T]`). -/
lemma strip_point_M_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (M T rlo rhi : ℝ)
    (hcc : ∀ s : ℂ, |s.im| ≤ T → rlo ≤ s.re → s.re ≤ rhi →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ M)
    (x t : ℝ) (hx1 : rlo ≤ x) (hx2 : x ≤ rhi) (ht : |t| ≤ T) :
    ‖-deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + t * I) / DirichletCharacter.LFunction χ ((x:ℂ) + t * I)‖
      ≤ M := by
  rw [neg_logDeriv_norm_eq]
  apply hcc
  · simpa using ht
  · simpa using hx1
  · simpa using hx2


/-- **Rate-extraction core** (SW brick W1k): `X^{1−g/2} = X·exp(−(g/2)·log X)` for `X > 0` — turns
    the W1 bound's `X^{σ'}` into the exponential-savings form `X·exp(−(g/2)·log X)`, whence the SW
    rate after substituting `g = c·N^{−ε}/L_T` and the `T(X)` choice. -/
lemma rpow_shift_as_exp (X g : ℝ) (hX : 0 < X) :
    X ^ (1 - g / 2 : ℝ) = X * Real.exp (-(g / 2) * Real.log X) := by
  rw [Real.rpow_sub hX, Real.rpow_one, Real.rpow_def_of_pos hX, div_eq_mul_inv, ← Real.exp_neg]
  congr 1
  ring


/-- **W1 instantiation skeleton**: with packaged strip bounds `M`, tail constant `B`, and
    zero-freeness as hypotheses, `‖ψ_smooth(X,χ)‖`-type quantities obey the explicit bound. -/
theorem psi_smooth_bound_skeleton {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (S : ℂ) (X : ℝ) (hX : 1 < X) (σ' σ T M B : ℝ)
    (hσ'34 : 3/4 ≤ σ') (hσ'σ : σ' ≤ σ) (hT : 0 < T) (hM : 0 ≤ M)
    (hrep : S = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G' χ X ((σ : ℂ) + t * I))
    (htail : ‖(∫ t : ℝ, G' χ X ((σ : ℂ) + t * I))
        - ∫ t in (-T)..T, G' χ X ((σ : ℂ) + t * I)‖ ≤ 2 * (B * X ^ σ) / T)
    (hconnT : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2))
    (hconnB : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2))
    (hline : ‖∫ y in (-T)..T, G' χ X ((σ':ℂ) + (y:ℂ) * I)‖ ≤ 6 * M * X ^ σ')
    (hzf : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ‖S‖ ≤ (6 * M * X ^ σ' + 2 * ((σ - σ') * (M * X ^ σ / T ^ 2)) + 2 * (B * X ^ σ) / T)
      / (2 * Real.pi) := by
  have hX0 : (0:ℝ) < X := by linarith
  -- the rectangle: z = σ' − T·I, w = σ + T·I
  have hzre : ((σ' : ℂ) + ((-T : ℝ) : ℂ) * I).re = σ' := by simp
  have hzim : ((σ' : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
  have hwre : ((σ : ℂ) + ((T : ℝ) : ℂ) * I).re = σ := by simp
  have hwim : ((σ : ℂ) + ((T : ℝ) : ℂ) * I).im = T := by simp
  have hrect : Complex.reProdIm (Set.uIcc σ' σ) (Set.uIcc (-T) T)
      ⊆ {s : ℂ | 0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0} := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    obtain ⟨hre, him⟩ := hs
    rw [Set.uIcc_of_le hσ'σ] at hre
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at him
    have h1 : σ' ≤ s.re := hre.1
    have h2 : |s.im| ≤ T := abs_le.mpr ⟨him.1, him.2⟩
    exact ⟨by linarith, hzf s h2 h1⟩
  have h3' := smoothed_integrand_rect_zero χ hχ X hX0
    ((σ' : ℂ) + ((-T : ℝ) : ℂ) * I) ((σ : ℂ) + ((T : ℝ) : ℂ) * I)
    (by rw [hzre, hzim, hwre, hwim]; exact hrect)
  rw [hzre, hzim, hwre, hwim] at h3'
  exact rectangle_assembly S (G' χ X) σ' σ T (2 * (B * X ^ σ) / T)
    ((σ - σ') * (M * X ^ σ / T ^ 2)) (6 * M * X ^ σ') hrep htail h3'
    hconnT hconnB
    hline

set_option maxHeartbeats 1000000
open DirichletCharacter Complex Metric MeasureTheory


















/-- **The χ≠1 smoothed ψ bound** (W1 MAIN): for every nontrivial character, the smoothed sum obeys
    `‖ψ_smooth(X,χ)‖ ≤ (6M·X^{1−g/2} + 2·(3g/2)·M·X^{1+g}/T² + 2B·X^{1+g}/T)/(2π)` with
    `g = c·N^{−ε}/L_T`, `M = C·N^ε·L_T²`. All five skeleton hypotheses discharged. -/
theorem psi_smooth_bound_chi_ne_one (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 1 ≤ C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ X : ℝ, 1 < X → ∀ T : ℝ, 0 < T →
    ∃ B : ℝ, 0 ≤ B ∧
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ (6 * (C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2)
            * X ^ (1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2)
          + 2 * (((1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20))
                - (1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2))
              * ((C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2)
                * X ^ (1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)) / T ^ 2))
          + 2 * (B * X ^ (1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20))) / T)
        / (2 * Real.pi) := by
  obtain ⟨c, C, hc0, hc12, hC1, hcc⟩ := contour_combined ε hε0
  refine ⟨c, C, hc0, hc12, hC1, ?_⟩
  intro N _ χ hχ X hX T hT
  have hX0 : (0:ℝ) < X := by linarith
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hNe1 : ((N:ℝ))^(-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  have hNp1 : (1:ℝ) ≤ ((N:ℝ))^ε := Real.one_le_rpow hN1r (by linarith)
  set LT := Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 with hLTdef
  have hLT20 : (20:ℝ) ≤ LT := by
    rw [hLTdef]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) := Real.log_nonneg (by nlinarith)
    linarith
  obtain ⟨hg0, hg40, hσ'34, hσ1, hσ'σ, hσ2⟩ :=
    strip_numerics c (((N:ℝ))^(-ε)) LT hc0 hc12 hNe0 hNe1 hLT20
  set g := c * ((N:ℝ))^(-ε) / LT with hgdef
  set σ' := 1 - g / 2 with hσ'def
  set σ := 1 + g with hσdef
  set M := C * ((N:ℝ))^ε * LT^2 with hMdef
  have hM0 : (0:ℝ) ≤ M := by rw [hMdef]; positivity
  -- the contour_combined data in strip_point_M_bound's hcc shape
  have hccM : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → s.re ≤ σ →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ M := by
    intro s him hre1 hre2
    exact ((hcc N χ hχ T hT.le s him hre1).2 hre2)
  have hzf : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0 := by
    intro s him hre
    exact (hcc N χ hχ T hT.le s him hre).1
  -- B from the σ-line tail
  obtain ⟨B, hB0, hBt⟩ := sigma_line_tail_bound χ X σ hX0 hσ1
  refine ⟨B, hB0, ?_⟩
  -- the five skeleton hypotheses
  have hrep : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G' χ X ((σ : ℂ) + t * I) := by
    rw [smoothed_perron_LFunction χ X hX σ hσ1, perron_integrand_reshape]
    rfl
  have htail : ‖(∫ t : ℝ, G' χ X ((σ : ℂ) + t * I))
      - ∫ t in (-T)..T, G' χ X ((σ : ℂ) + t * I)‖ ≤ 2 * (B * X ^ σ) / T :=
    truncation_tail_bound _ (integrand_integrable_on_line χ hχ X hX0 σ hσ1)
      (B * X ^ σ) T hT (fun t ht => hBt t ht)
  have hMseg : ∀ tt : ℝ, |tt| ≤ T → ∀ x ∈ Set.uIcc σ' σ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + tt * I) / DirichletCharacter.LFunction χ ((x:ℂ) + tt * I)‖ ≤ M := by
    intro tt httT x hx
    rw [Set.uIcc_of_le hσ'σ] at hx
    exact strip_point_M_bound χ M T σ' σ hccM x tt hx.1 hx.2 httT
  have hconnT : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) :=
    horizontal_connector_bound χ X hX.le σ' σ T M hσ'σ hT.ne' hM0
      (hMseg T (by rw [abs_of_pos hT]))
  have hconnB : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) := by
    have hb := horizontal_connector_bound χ X hX.le σ' σ (-T) M hσ'σ
      (by simpa using hT.ne') hM0 (hMseg (-T) (by rw [abs_neg, abs_of_pos hT]))
    rwa [neg_sq] at hb
  have hline : ‖∫ y in (-T)..T, G' χ X ((σ':ℂ) + (y:ℂ) * I)‖ ≤ 6 * M * X ^ σ' := by
    apply shifted_line_integral_bound _ M (X ^ σ') σ' T hM0 (Real.rpow_nonneg hX0.le _) hσ'34 hT.le
    intro t ht
    have htT : |t| ≤ T := by
      rw [abs_le]
      exact ⟨ht.1.le, ht.2⟩
    exact integrand_pointwise_bound χ X σ' t M hX0 (by linarith) hM0
      (strip_point_M_bound χ M T σ' σ hccM σ' t le_rfl hσ'σ htT)
  exact psi_smooth_bound_skeleton χ hχ _ X hX σ' σ T M B hσ'34 hσ'σ hT hM0
    hrep htail hconnT hconnB hline hzf



open ArithmeticFunction in
/-- **Quantitative −L′/L on the σ-line** (SW brick W2a′): `‖−L′/L(σ+it,χ)‖ ≤ 6/(σ−1)²` for
    `1 < σ ≤ 2` — makes the tail constant `B` explicit (`Λ ≤ log`, `log n ≤ (2/(σ−1))·n^{(σ−1)/2}`,
    `∑ n^{−(σ+1)/2} ≤ (σ+1)/(σ−1)`). -/
lemma neg_logDeriv_quantitative {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    ‖-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I)‖
      ≤ 6 / (σ - 1) ^ 2 := by
  have hre : ((σ:ℂ) + t * I).re = σ := by simp
  have hs : 1 < ((σ:ℂ) + t * I).re := by rw [hre]; exact hσ1
  rw [neg_logDeriv_LFunction_eq χ hs]
  have hsummable : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) ((σ:ℂ) + t * I) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs)
  have hmaj : Summable (fun n : ℕ => (2 / (σ - 1)) * (1 / (n : ℝ) ^ ((σ + 1) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith)).mul_left _
  have hterm : ∀ n : ℕ,
      ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) ((σ:ℂ) + t * I) n‖
        ≤ (2 / (σ - 1)) * (1 / (n : ℝ) ^ ((σ + 1) / 2)) := by
    intro n
    rw [LSeries.norm_term_eq, hre]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [if_pos rfl]
      positivity
    · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      rw [if_neg hn.ne']
      have h1 : ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖ ≤ vonMangoldt n := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg vonMangoldt_nonneg]
        calc ‖χ (n : ZMod N)‖ * vonMangoldt n ≤ 1 * vonMangoldt n :=
              mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) vonMangoldt_nonneg
          _ = vonMangoldt n := one_mul _
      have h2 : vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
      have h3 : Real.log n ≤ (2 / (σ - 1)) * (n:ℝ) ^ ((σ - 1) / 2) := by
        have := Real.log_le_rpow_div hn0.le (by linarith : (0:ℝ) < (σ - 1) / 2)
        calc Real.log n ≤ (n:ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2) := this
          _ = (2 / (σ - 1)) * (n:ℝ) ^ ((σ - 1) / 2) := by
              field_simp
      have h4 : (n:ℝ) ^ ((σ - 1) / 2) / (n:ℝ) ^ σ = 1 / (n:ℝ) ^ ((σ + 1) / 2) := by
        rw [← Real.rpow_sub hn0, one_div, ← Real.rpow_neg hn0.le]
        congr 1
        ring
      calc ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖ / (n : ℝ) ^ σ
          ≤ Real.log n / (n : ℝ) ^ σ := by
            apply div_le_div_of_nonneg_right (le_trans h1 h2) (Real.rpow_pos_of_pos hn0 σ).le
        _ ≤ ((2 / (σ - 1)) * (n:ℝ) ^ ((σ - 1) / 2)) / (n : ℝ) ^ σ := by
            apply div_le_div_of_nonneg_right h3 (Real.rpow_pos_of_pos hn0 σ).le
        _ = (2 / (σ - 1)) * ((n:ℝ) ^ ((σ - 1) / 2) / (n:ℝ) ^ σ) := by ring
        _ = (2 / (σ - 1)) * (1 / (n : ℝ) ^ ((σ + 1) / 2)) := by rw [h4]
  calc ‖LSeries (fun n : ℕ => χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) ((σ:ℂ) + t * I)‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)) ((σ:ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm hsummable
    _ ≤ ∑' n : ℕ, (2 / (σ - 1)) * (1 / (n : ℝ) ^ ((σ + 1) / 2)) :=
        hsummable.tsum_le_tsum hterm hmaj
    _ = (2 / (σ - 1)) * ∑' n : ℕ, 1 / (n : ℝ) ^ ((σ + 1) / 2) := tsum_mul_left
    _ ≤ (2 / (σ - 1)) * (((σ + 1) / 2) / (((σ + 1) / 2) - 1)) := by
        apply mul_le_mul_of_nonneg_left (tsum_one_div_nat_rpow_le _ (by linarith)) (by positivity)
    _ ≤ 6 / (σ - 1) ^ 2 := by
        have hσ1' : (0:ℝ) < σ - 1 := by linarith
        have heq : (2 / (σ - 1)) * (((σ + 1) / 2) / (((σ + 1) / 2) - 1))
            = (2 * (σ + 1)) / (σ - 1) ^ 2 := by
          rw [show ((σ + 1) / 2) - 1 = (σ - 1) / 2 by ring]
          field_simp
        rw [heq]
        gcongr
        linarith


/-- **Quantitative σ-line tail** (SW brick W2a″): the smoothed integrand on `Re = σ ∈ (1,2]` is
    dominated by `((6/(σ−1)²)·X^σ)/t²` — `truncation_tail_bound`'s input with EXPLICIT constant,
    replacing the existential `B` of `sigma_line_tail_bound`. -/
lemma sigma_line_tail_quantitative {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X σ : ℝ) (hX : 0 < X) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    ∀ t : ℝ, t ≠ 0 →
      ‖G' χ X ((σ:ℂ) + t * I)‖ ≤ ((6 / (σ - 1) ^ 2) * X ^ σ) / t ^ 2 := by
  intro t ht
  have him : ((σ:ℂ) + t * I).im = t := by simp
  have hre : ((σ:ℂ) + t * I).re = σ := by simp
  have hkd := perron_kernel_decay X hX ((σ:ℂ) + t * I) (by rw [him]; exact ht)
  rw [hre, him] at hkd
  have hq := neg_logDeriv_quantitative χ σ hσ1 hσ2 t
  have hq0 : (0:ℝ) ≤ 6 / (σ - 1) ^ 2 := by positivity
  rw [G', norm_mul]
  calc ‖-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + t * I) / DirichletCharacter.LFunction χ ((σ:ℂ) + t * I)‖
        * ‖(X:ℂ) ^ ((σ:ℂ) + t * I) / (((σ:ℂ) + t * I) * ((σ:ℂ) + t * I + 1))‖
      ≤ (6 / (σ - 1) ^ 2) * (X ^ σ / t ^ 2) := mul_le_mul hq hkd (norm_nonneg _) hq0
    _ = ((6 / (σ - 1) ^ 2) * X ^ σ) / t ^ 2 := by ring

/-- **The χ≠1 smoothed ψ bound, fully quantitative** (W1 MAIN′): every constant explicit —
    `‖ψ_smooth(X,χ)‖ ≤ (6M·X^{1−g/2} + 3g·M·X^{1+g}/T² + 2·(6/g²)·X^{1+g}/T)/(2π)`. -/
theorem psi_smooth_bound_quantitative (ε : ℝ) (hε0 : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 1 ≤ C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ X : ℝ, 1 < X → ∀ T : ℝ, 0 < T →
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ (6 * (C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2)
            * X ^ (1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2)
          + 2 * (((1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20))
                - (1 - c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20) / 2))
              * ((C * ((N:ℝ))^ε * (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)^2)
                * X ^ (1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)) / T ^ 2))
          + 2 * ((6 / (c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20)) ^ 2)
              * X ^ (1 + c * ((N:ℝ))^(-ε) / (Real.log ((N:ℝ)*(4*(T+1)+7)) + 20))) / T)
        / (2 * Real.pi) := by
  obtain ⟨c, C, hc0, hc12, hC1, hcc⟩ := contour_combined ε hε0
  refine ⟨c, C, hc0, hc12, hC1, ?_⟩
  intro N _ χ hχ X hX T hT
  have hX0 : (0:ℝ) < X := by linarith
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNe0 : (0:ℝ) < ((N:ℝ))^(-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hNe1 : ((N:ℝ))^(-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1r (by linarith)
  set LT := Real.log ((N:ℝ)*(4*(T+1)+7)) + 20 with hLTdef
  have hLT20 : (20:ℝ) ≤ LT := by
    rw [hLTdef]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*(T+1)+7)) := Real.log_nonneg (by nlinarith)
    linarith
  obtain ⟨hg0, hg40, hσ'34, hσ1, hσ'σ, hσ2⟩ :=
    strip_numerics c (((N:ℝ))^(-ε)) LT hc0 hc12 hNe0 hNe1 hLT20
  set g := c * ((N:ℝ))^(-ε) / LT with hgdef
  set σ' := 1 - g / 2 with hσ'def
  set σ := 1 + g with hσdef
  set M := C * ((N:ℝ))^ε * LT^2 with hMdef
  have hM0 : (0:ℝ) ≤ M := by rw [hMdef]; positivity
  have hccM : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → s.re ≤ σ →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ M := by
    intro s him hre1 hre2
    exact ((hcc N χ hχ T hT.le s him hre1).2 hre2)
  have hzf : ∀ s : ℂ, |s.im| ≤ T → σ' ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0 := by
    intro s him hre
    exact (hcc N χ hχ T hT.le s him hre).1
  have hσm1 : σ - 1 = g := by rw [hσdef]; ring
  have hrep : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      χ (n : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
      = (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, G' χ X ((σ : ℂ) + t * I) := by
    rw [smoothed_perron_LFunction χ X hX σ hσ1, perron_integrand_reshape]
    rfl
  have htail : ‖(∫ t : ℝ, G' χ X ((σ : ℂ) + t * I))
      - ∫ t in (-T)..T, G' χ X ((σ : ℂ) + t * I)‖ ≤ 2 * ((6 / g ^ 2) * X ^ σ) / T := by
    have hq := sigma_line_tail_quantitative χ X σ hX0 hσ1 hσ2
    have := truncation_tail_bound _ (integrand_integrable_on_line χ hχ X hX0 σ hσ1)
      ((6 / (σ - 1) ^ 2) * X ^ σ) T hT (fun t ht => hq t ht)
    rwa [hσm1] at this
  have hMseg : ∀ tt : ℝ, |tt| ≤ T → ∀ x ∈ Set.uIcc σ' σ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + tt * I) / DirichletCharacter.LFunction χ ((x:ℂ) + tt * I)‖ ≤ M := by
    intro tt httT x hx
    rw [Set.uIcc_of_le hσ'σ] at hx
    exact strip_point_M_bound χ M T σ' σ hccM x tt hx.1 hx.2 httT
  have hconnT : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) :=
    horizontal_connector_bound χ X hX.le σ' σ T M hσ'σ hT.ne' hM0
      (hMseg T (by rw [abs_of_pos hT]))
  have hconnB : ‖∫ x in σ'..σ, G' χ X ((x:ℂ) + ((-T : ℝ) : ℂ) * I)‖
      ≤ (σ - σ') * (M * X ^ σ / T ^ 2) := by
    have hb := horizontal_connector_bound χ X hX.le σ' σ (-T) M hσ'σ
      (by simpa using hT.ne') hM0 (hMseg (-T) (by rw [abs_neg, abs_of_pos hT]))
    rwa [neg_sq] at hb
  have hline : ‖∫ y in (-T)..T, G' χ X ((σ':ℂ) + (y:ℂ) * I)‖ ≤ 6 * M * X ^ σ' := by
    apply shifted_line_integral_bound _ M (X ^ σ') σ' T hM0 (Real.rpow_nonneg hX0.le _) hσ'34 hT.le
    intro t ht
    have htT : |t| ≤ T := by
      rw [abs_le]
      exact ⟨ht.1.le, ht.2⟩
    exact integrand_pointwise_bound χ X σ' t M hX0 (by linarith) hM0
      (strip_point_M_bound χ M T σ' σ hccM σ' t le_rfl hσ'σ htT)
  exact psi_smooth_bound_skeleton χ hχ _ X hX σ' σ T M (6 / g ^ 2) hσ'34 hσ'σ hT hM0
    hrep htail hconnT hconnB hline hzf

/-- **R1: L_T two-sided bounds at `T = exp u`** — for `u ≥ (4B+23)²` and `1 ≤ Nr ≤ u^{2B}`:
    `u ≤ log(Nr·(4(e^u+1)+7)) + 20 ≤ 2u`. Upper: `log Nr ≤ 2B·log u ≤ 4B·√u` (`log_le_rpow_div`),
    `4e^u+11 ≤ 15e^u`, `log 15 ≤ 3`; lower: the argument dominates `e^u`. -/
lemma LT_bounds_at_exp (B : ℝ) (hB : 1 ≤ B) :
    ∀ u : ℝ, (4*B + 23)^2 ≤ u → ∀ Nr : ℝ, 1 ≤ Nr → Nr ≤ u ^ (2*B : ℝ) →
    u ≤ Real.log (Nr * (4*(Real.exp u + 1) + 7)) + 20 ∧
    Real.log (Nr * (4*(Real.exp u + 1) + 7)) + 20 ≤ 2*u := by
  intro u hu Nr hNr1 hNru
  have hB0 : (0:ℝ) < B := by linarith
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le (by nlinarith) hu
  have hu1 : (1:ℝ) ≤ u := le_trans (by nlinarith) hu
  have hexp0 : (0:ℝ) < Real.exp u := Real.exp_pos u
  have harg0 : (0:ℝ) < Nr * (4*(Real.exp u + 1) + 7) := by positivity
  constructor
  · -- lower: Nr·(4(e^u+1)+7) ≥ e^u
    have h1 : Real.exp u ≤ Nr * (4*(Real.exp u + 1) + 7) := by nlinarith
    have h2 := Real.log_le_log hexp0 h1
    rw [Real.log_exp] at h2
    linarith
  · -- upper
    have hsplit : Real.log (Nr * (4*(Real.exp u + 1) + 7))
        = Real.log Nr + Real.log (4*(Real.exp u + 1) + 7) := by
      rw [Real.log_mul (by linarith) (by positivity)]
    have hlogNr : Real.log Nr ≤ 4 * B * u ^ ((1:ℝ)/2) := by
      have h3 : Real.log Nr ≤ Real.log (u ^ (2*B : ℝ)) := Real.log_le_log (by linarith) hNru
      rw [Real.log_rpow hu0] at h3
      have h4 : Real.log u ≤ u ^ ((1:ℝ)/2) / ((1:ℝ)/2) :=
        Real.log_le_rpow_div hu0.le (by norm_num)
      have h5 : u ^ ((1:ℝ)/2) / ((1:ℝ)/2) = 2 * u ^ ((1:ℝ)/2) := by ring
      rw [h5] at h4
      have hlogu0 : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
      calc Real.log Nr ≤ 2*B * Real.log u := h3
        _ ≤ 2*B * (2 * u ^ ((1:ℝ)/2)) := by
            apply mul_le_mul_of_nonneg_left h4 (by linarith)
        _ = 4 * B * u ^ ((1:ℝ)/2) := by ring
    have hlogT : Real.log (4*(Real.exp u + 1) + 7) ≤ 3 + u := by
      have h6 : 4*(Real.exp u + 1) + 7 ≤ 15 * Real.exp u := by
        nlinarith [Real.one_le_exp (le_of_lt hu0)]
      have h7 := Real.log_le_log (by positivity) h6
      rw [Real.log_mul (by norm_num) hexp0.ne', Real.log_exp] at h7
      have h8 : Real.log 15 ≤ 3 := by
        have h9 : (15:ℝ) ≤ Real.exp 3 := by
          have h10 : (2.7:ℝ) ≤ Real.exp 1 := by
            have := Real.exp_one_gt_d9
            linarith
          calc (15:ℝ) ≤ 2.7^3 := by norm_num
            _ ≤ (Real.exp 1)^3 := pow_le_pow_left₀ (by norm_num) h10 3
            _ = Real.exp 3 := by
                rw [← Real.exp_one_rpow 3]
                norm_num
        calc Real.log 15 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) h9
          _ = 3 := Real.log_exp 3
      linarith
    have hsq : (4*B + 23) ≤ u ^ ((1:ℝ)/2) := by
      have h11 : ((4*B + 23)^2) ^ ((1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) hu (by norm_num)
      rwa [show ((4*B + 23):ℝ)^2 = (4*B+23)*(4*B+23) by ring,
        ← Real.sqrt_eq_rpow, Real.sqrt_mul_self (by linarith)] at h11
    have hsqu : u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) = u := by
      rw [← Real.rpow_add hu0]
      norm_num
    have hsqnn : (0:ℝ) ≤ u ^ ((1:ℝ)/2) := Real.rpow_nonneg hu0.le _
    have hsq1 : (1:ℝ) ≤ u ^ ((1:ℝ)/2) := by nlinarith
    -- 4B√u + 3 + u + 20 ≤ 2u ⟸ 4B√u + 23 ≤ u = √u·√u
    have hmain : 4 * B * u ^ ((1:ℝ)/2) + 23 ≤ u := by
      have h12 : (4*B + 23) * u ^ ((1:ℝ)/2) ≤ u := by
        calc (4*B + 23) * u ^ ((1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) := by
              apply mul_le_mul_of_nonneg_right hsq hsqnn
          _ = u := hsqu
      nlinarith
    rw [hsplit]
    linarith

/-- **R2+R3: the gap–saving balance at `T = exp u`** — with `u ≤ LT ≤ 2u`, `u^{−1/2} ≤ Ne ≤ 1`,
    `0 < c ≤ 1/2`: the exponential saving grows, `(c/2)·u^{1/2} ≤ g·u²` (R2), while the strip stays
    thin enough that `g·u² ≤ u/2` (R3) — so `X^g/T = exp(g·u² − u) ≤ exp(−u/2)`. Here `g = c·Ne/LT`,
    `u² = log X`. -/
lemma rate_g_bounds (c u LT Ne : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1/2)
    (hu1 : 1 ≤ u) (hLTlo : u ≤ LT) (hLThi : LT ≤ 2*u)
    (hNe_lo : u ^ (-(1:ℝ)/2) ≤ Ne) (hNe_hi : Ne ≤ 1) :
    (c/2) * u ^ ((1:ℝ)/2) ≤ (c * Ne / LT) * (u * u) ∧ (c * Ne / LT) * (u * u) ≤ u/2 := by
  have hu0 : (0:ℝ) < u := by linarith
  have hLT0 : (0:ℝ) < LT := by linarith
  have hNe0 : (0:ℝ) < Ne := lt_of_lt_of_le (Real.rpow_pos_of_pos hu0 _) hNe_lo
  have hu2 : u * u = u ^ ((2:ℕ):ℝ) := by
    rw [Real.rpow_natCast]
    ring
  have e1 : u ^ ((1:ℝ)/2) * u = u ^ ((3:ℝ)/2) := by
    nth_rewrite 2 [show u = u ^ (1:ℝ) from (Real.rpow_one u).symm]
    rw [← Real.rpow_add hu0]
    norm_num
  have e2 : u ^ (-(1:ℝ)/2) * (u * u) = u ^ ((3:ℝ)/2) := by
    rw [hu2, ← Real.rpow_add hu0]
    norm_num
  constructor
  · -- R2: (c/2)·u^{1/2} ≤ g·u²
    rw [show (c * Ne / LT) * (u * u) = (c * Ne * (u * u)) / LT from by ring,
        le_div_iff₀ hLT0]
    have h1 : (c/2) * u ^ ((1:ℝ)/2) * LT ≤ (c/2) * u ^ ((1:ℝ)/2) * (2*u) := by
      apply mul_le_mul_of_nonneg_left hLThi (by positivity)
    have h2 : (c/2) * u ^ ((1:ℝ)/2) * (2*u) = c * (u ^ ((1:ℝ)/2) * u) := by ring
    have h3 : u ^ ((3:ℝ)/2) ≤ Ne * (u * u) := by
      calc u ^ ((3:ℝ)/2) = u ^ (-(1:ℝ)/2) * (u * u) := e2.symm
        _ ≤ Ne * (u * u) := by
            apply mul_le_mul_of_nonneg_right hNe_lo (by positivity)
    have h4 : c * (u ^ ((1:ℝ)/2) * u) ≤ c * (Ne * (u * u)) := by
      apply mul_le_mul_of_nonneg_left _ hc0.le
      rw [e1]
      exact h3
    calc (c/2) * u ^ ((1:ℝ)/2) * LT ≤ c * (u ^ ((1:ℝ)/2) * u) := by linarith
      _ ≤ c * (Ne * (u * u)) := h4
      _ = c * Ne * (u * u) := by ring
  · -- R3: g·u² ≤ u/2
    have h5 : c * Ne / LT ≤ c / u := by
      have h5a : c * Ne / LT ≤ c / LT := by
        apply div_le_div_of_nonneg_right _ hLT0.le
        nlinarith
      have h5b : c / LT ≤ c / u := div_le_div_of_nonneg_left hc0.le hu0 hLTlo
      linarith
    have h6 : (c / u) * (u * u) = c * u := by
      field_simp
    calc (c * Ne / LT) * (u * u) ≤ (c / u) * (u * u) := by
          apply mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = c * u := h6
      _ ≤ u/2 := by nlinarith

/-- **R4a: polylog absorption into the exponential saving** — for `u ≥ max((80/c)⁴, 256)`:
    `C·u^{5/2}·e^{−(c/4)√u} + K·u³·e^{−u/2} ≤ (C+K)·e^{−(c/8)√u}`. Via `log a ≤ x−y ⇒
    a·e^{−x} ≤ e^{−y}` + `log u ≤ 4u^{1/4}` (`log_le_rpow_div`). -/
lemma poly_exp_absorption (c C K : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1/2)
    (hC0 : 0 ≤ C) (hK0 : 0 ≤ K) :
    ∀ u : ℝ, max ((80/c)^4) 256 ≤ u →
      C * u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
        + K * u ^ (3:ℝ) * Real.exp (-(u/2))
      ≤ (C + K) * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
  intro u hu
  have hu256 : (256:ℝ) ≤ u := le_trans (le_max_right _ _) hu
  have hu80c : (80/c)^4 ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : (0:ℝ) < u := by linarith
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hs0 : (0:ℝ) < u ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hu0 _
  have hq0 : (0:ℝ) < u ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hu0 _
  -- log u ≤ 4·u^{1/4}
  have hlogu : Real.log u ≤ 4 * u ^ ((1:ℝ)/4) := by
    have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/4)
    calc Real.log u ≤ u ^ ((1:ℝ)/4) / (1/4) := this
      _ = 4 * u ^ ((1:ℝ)/4) := by ring
  -- u^{1/4}·u^{1/4} = u^{1/2}
  have hqq : u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4) = u ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_add hu0]; norm_num
  have hss : u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) = u := by
    rw [← Real.rpow_add hu0]; norm_num
  -- (80/c) ≤ u^{1/4}
  have h80 : 80/c ≤ u ^ ((1:ℝ)/4) := by
    have h1 : ((80/c)^4 : ℝ) ^ ((1:ℝ)/4) ≤ u ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) hu80c (by norm_num)
    rwa [show ((80/c):ℝ)^4 = ((80/c):ℝ)^((4:ℕ):ℝ) from by rw [Real.rpow_natCast],
      ← Real.rpow_mul (by positivity), show ((4:ℕ):ℝ) * ((1:ℝ)/4) = 1 by norm_num,
      Real.rpow_one] at h1
  -- 4 ≤ u^{1/4} (from u ≥ 256)
  have h4q : (4:ℝ) ≤ u ^ ((1:ℝ)/4) := by
    have h1 : ((256:ℝ)) ^ ((1:ℝ)/4) ≤ u ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by norm_num) hu256 (by norm_num)
    rwa [show (256:ℝ) = (4:ℝ)^((4:ℕ):ℝ) from by rw [Real.rpow_natCast]; norm_num,
      ← Real.rpow_mul (by norm_num), show ((4:ℕ):ℝ) * ((1:ℝ)/4) = 1 by norm_num,
      Real.rpow_one] at h1
  -- helper: log a ≤ x − y ⇒ a·e^{−x} ≤ e^{−y}
  have haux : ∀ a x y : ℝ, 0 < a → Real.log a ≤ x - y →
      a * Real.exp (-x) ≤ Real.exp (-y) := by
    intro a x y ha hlog
    have h1 : a ≤ Real.exp (x - y) := (Real.log_le_iff_le_exp ha).mp hlog
    calc a * Real.exp (-x) ≤ Real.exp (x - y) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-y) := by rw [← Real.exp_add]; ring_nf
  -- term 1
  have hterm1 : u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
      ≤ Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
    apply haux _ _ _ (Real.rpow_pos_of_pos hu0 _)
    rw [Real.log_rpow hu0]
    have h1 : (5:ℝ)/2 * Real.log u ≤ 10 * u ^ ((1:ℝ)/4) := by
      have hlogu0 : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
      nlinarith
    have h2 : 10 * u ^ ((1:ℝ)/4) ≤ (c/8) * u ^ ((1:ℝ)/2) := by
      have h3 : (80:ℝ) ≤ c * u ^ ((1:ℝ)/4) := by
        have := mul_le_mul_of_nonneg_left h80 hc0.le
        calc (80:ℝ) = c * (80/c) := by field_simp
          _ ≤ c * u ^ ((1:ℝ)/4) := this
      calc 10 * u ^ ((1:ℝ)/4) = (80 * (u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4))) / (8 * u ^ ((1:ℝ)/4)) := by
            field_simp
            ring
        _ ≤ ((c * u ^ ((1:ℝ)/4)) * (u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4))) / (8 * u ^ ((1:ℝ)/4)) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (c/8) * (u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4)) := by
            field_simp
        _ = (c/8) * u ^ ((1:ℝ)/2) := by rw [hqq]
    have hgoal : (c/4) * u ^ ((1:ℝ)/2) - (c/8) * u ^ ((1:ℝ)/2) = (c/8) * u ^ ((1:ℝ)/2) := by ring
    linarith
  -- term 2
  have hterm2 : u ^ (3:ℝ) * Real.exp (-(u/2))
      ≤ Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
    apply haux _ _ _ (Real.rpow_pos_of_pos hu0 _)
    rw [Real.log_rpow hu0]
    have h1 : (3:ℝ) * Real.log u ≤ 12 * u ^ ((1:ℝ)/4) := by
      have hlogu0 : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
      nlinarith
    -- 12·u^{1/4} ≤ u/4: 12 ≤ (1/4)·u^{3/4} ⟸ u^{3/4} = u^{1/4}·u^{1/2} ≥ 4·16 = 64 ≥ 48
    have h16 : (16:ℝ) ≤ u ^ ((1:ℝ)/2) := by
      have h := mul_le_mul h4q h4q (by norm_num) hq0.le
      rw [hqq] at h
      linarith
    have h2 : 12 * u ^ ((1:ℝ)/4) ≤ u/4 := by
      have h3 : 48 * u ^ ((1:ℝ)/4) ≤ u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) := by
        calc 48 * u ^ ((1:ℝ)/4) ≤ (16 * u ^ ((1:ℝ)/4)) * 4 := by ring_nf; nlinarith [hq0]
          _ ≤ (u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/4)) * u ^ ((1:ℝ)/4) := by
              apply mul_le_mul _ h4q (by norm_num) (by positivity)
              apply mul_le_mul_of_nonneg_right h16 hq0.le
          _ = u ^ ((1:ℝ)/2) * (u ^ ((1:ℝ)/4) * u ^ ((1:ℝ)/4)) := by ring
          _ = u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) := by rw [hqq]
      rw [hss] at h3
      linarith
    -- u/2 − (c/8)√u ≥ u/4: (c/8)√u ≤ √u/16 ≤ u/4
    have h5 : (c/8) * u ^ ((1:ℝ)/2) ≤ u/4 := by
      have h6 : (c/8) * u ^ ((1:ℝ)/2) ≤ (1/16) * u ^ ((1:ℝ)/2) := by
        apply mul_le_mul_of_nonneg_right (by linarith) hs0.le
      have h7 : u ^ ((1:ℝ)/2) ≤ u := by
        calc u ^ ((1:ℝ)/2) = 1 * u ^ ((1:ℝ)/2) := (one_mul _).symm
          _ ≤ u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) := by
              apply mul_le_mul_of_nonneg_right _ hs0.le
              nlinarith [h16]
          _ = u := hss
      linarith
    linarith
  -- assemble
  calc C * u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
        + K * u ^ (3:ℝ) * Real.exp (-(u/2))
      = C * (u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2))))
        + K * (u ^ (3:ℝ) * Real.exp (-(u/2))) := by ring
    _ ≤ C * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) + K * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) :=
        add_le_add (mul_le_mul_of_nonneg_left hterm1 hC0) (mul_le_mul_of_nonneg_left hterm2 hK0)
    _ = (C + K) * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by ring

/-- **R4b-pre: modulus-power bounds at `ε = 1/(4B)`** — for `1 ≤ Nr ≤ u^{2B}`, `u ≥ 1`:
    `Nr^{1/(4B)} ≤ u^{1/2}` and `u^{−1/2} ≤ Nr^{−1/(4B)} ≤ 1` (the `Ne`-window `rate_g_bounds`
    and the `M`-bound need). -/
lemma N_eps_bounds (B : ℝ) (hB : 1 ≤ B) (u Nr : ℝ) (hu1 : 1 ≤ u) (hNr1 : 1 ≤ Nr)
    (hNru : Nr ≤ u ^ (2*B : ℝ)) :
    Nr ^ ((1:ℝ)/(4*B)) ≤ u ^ ((1:ℝ)/2) ∧
    u ^ (-(1:ℝ)/2) ≤ Nr ^ (-((1:ℝ)/(4*B))) ∧ Nr ^ (-((1:ℝ)/(4*B))) ≤ 1 := by
  have hu0 : (0:ℝ) < u := by linarith
  have hNr0 : (0:ℝ) < Nr := by linarith
  have hB0 : (0:ℝ) < B := by linarith
  have hε0 : (0:ℝ) < (1:ℝ)/(4*B) := by positivity
  have hup : Nr ^ ((1:ℝ)/(4*B)) ≤ u ^ ((1:ℝ)/2) := by
    have h1 : Nr ^ ((1:ℝ)/(4*B)) ≤ (u ^ (2*B : ℝ)) ^ ((1:ℝ)/(4*B)) :=
      Real.rpow_le_rpow hNr0.le hNru hε0.le
    rwa [← Real.rpow_mul hu0.le, show (2*B) * ((1:ℝ)/(4*B)) = 1/2 from by
      field_simp
      ring] at h1
  have hpos : (0:ℝ) < Nr ^ ((1:ℝ)/(4*B)) := Real.rpow_pos_of_pos hNr0 _
  refine ⟨hup, ?_, ?_⟩
  · rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hu0.le,
      Real.rpow_neg hNr0.le]
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos hup
  · exact Real.rpow_le_one_of_one_le_of_nonpos hNr1 (neg_nonpos.mpr hε0.le)

set_option maxHeartbeats 4000000 in
open ArithmeticFunction in
/-- **R4b: THE PER-CHARACTER SIEGEL–WALFISZ BOUND** — for every `B ≥ 1` there are `c₂, C₂, X₀ > 0`
    with: for all `X ≥ X₀`, moduli `q ≤ (log X)^B`, and nontrivial `χ mod q`,
    `‖ψ_smooth(X,χ)‖ ≤ C₂·X·exp(−c₂·(log X)^{1/10})`. Instantiates
    `psi_smooth_bound_quantitative` at `ε = 1/(4B)`, `T = exp(√(log X))` and collapses via
    R1 (`LT_bounds_at_exp`), R2/R3 (`rate_g_bounds`), R4b-pre (`N_eps_bounds`),
    `rpow_shift_as_exp`, and R4a (`poly_exp_absorption`). -/
theorem psi_smooth_SW_rate (B : ℝ) (hB : 1 ≤ B) :
    ∃ c₂ C₂ X₀ : ℝ, 0 < c₂ ∧ 0 < C₂ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    (N:ℝ) ≤ Real.log X ^ (B : ℝ) →
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ C₂ * X * Real.exp (-(c₂ * Real.log X ^ ((1:ℝ)/10))) := by
  obtain ⟨c, C, hc0, hc12, hC1, hmain⟩ := psi_smooth_bound_quantitative (1/(4*B)) (by positivity)
  set M₀ := max ((4*B+23)^2) (max ((80/c)^4) 256) with hM₀def
  have hM₀256 : (256:ℝ) ≤ M₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hM₀1 : (1:ℝ) ≤ M₀ := by linarith
  have hM₀0 : (0:ℝ) ≤ M₀ := by linarith
  refine ⟨c/8, 30*C + 48/c^2, Real.exp (M₀^2), by positivity, by positivity, ?_⟩
  intro X hX N _ χ hχ hNB
  -- basic scales
  have hL : M₀^2 ≤ Real.log X := by
    have h1 : Real.log (Real.exp (M₀^2)) ≤ Real.log X :=
      Real.log_le_log (Real.exp_pos _) hX
    rwa [Real.log_exp] at h1
  have hL1 : (1:ℝ) ≤ Real.log X := by nlinarith
  have hL0 : (0:ℝ) < Real.log X := by linarith
  have hX1 : (1:ℝ) < X := by
    have h1 : Real.exp 1 ≤ Real.exp (M₀^2) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 := Real.add_one_le_exp 1
    linarith
  have hX0 : (0:ℝ) < X := by linarith
  set L := Real.log X with hLdef
  set u := L ^ ((1:ℝ)/2) with hudef
  have hu0 : (0:ℝ) < u := Real.rpow_pos_of_pos hL0 _
  have huM : M₀ ≤ u := by
    have h1 : (M₀^2) ^ ((1:ℝ)/2) ≤ L ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) hL (by norm_num)
    rwa [show (M₀:ℝ)^2 = M₀ * M₀ by ring, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul_self hM₀0] at h1
  have hu1 : (1:ℝ) ≤ u := le_trans hM₀1 huM
  have hLuu : u * u = L := by
    rw [hudef, ← Real.rpow_add hL0]
    norm_num
  set T := Real.exp u with hTdef
  have hT0 : (0:ℝ) < T := Real.exp_pos _
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  -- N ≤ u^{2B}
  have hNru : (N:ℝ) ≤ u ^ (2*B : ℝ) := by
    have h1 : L ^ (B:ℝ) = u ^ (2*B : ℝ) := by
      rw [← hLuu, show u * u = u ^ ((2:ℕ):ℝ) from by rw [Real.rpow_natCast]; ring,
        ← Real.rpow_mul hu0.le]
      norm_num
    rwa [h1] at hNB
  -- R1
  obtain ⟨hLTlo, hLThi⟩ := LT_bounds_at_exp B hB u
    (le_trans (le_max_left _ _) huM) (N:ℝ) hN1 hNru
  set LTv := Real.log ((N:ℝ) * (4*(T+1)+7)) + 20 with hLTvdef
  -- R4b-pre
  obtain ⟨hNup, hNe_lo, hNe_hi⟩ := N_eps_bounds B hB u (N:ℝ) hu1 hN1 hNru
  set Ne := (N:ℝ) ^ (-((1:ℝ)/(4*B))) with hNedef
  set g := c * Ne / LTv with hgdef
  have hLT0 : (0:ℝ) < LTv := by linarith
  have hNe0 : (0:ℝ) < Ne := Real.rpow_pos_of_pos (by linarith) _
  have hg0 : (0:ℝ) < g := by rw [hgdef]; positivity
  -- R2/R3
  obtain ⟨hR2, hR3⟩ := rate_g_bounds c u LTv Ne hc0 hc12 hu1 hLTlo hLThi hNe_lo hNe_hi
  set M := C * (N:ℝ) ^ ((1:ℝ)/(4*B)) * LTv^2 with hMdef
  have hM0 : (0:ℝ) ≤ M := by rw [hMdef]; positivity
  -- M ≤ 4C·u^{5/2}
  have hMle : M ≤ 4*C * u ^ ((5:ℝ)/2) := by
    have h1 : LTv^2 ≤ 4 * (u*u) := by nlinarith
    have h2 : (N:ℝ) ^ ((1:ℝ)/(4*B)) * LTv^2 ≤ u ^ ((1:ℝ)/2) * (4*(u*u)) := by
      apply mul_le_mul hNup h1 (by positivity) (by positivity)
    have h3 : u ^ ((1:ℝ)/2) * (4*(u*u)) = 4 * u ^ ((5:ℝ)/2) := by
      rw [show u * u = u ^ ((2:ℕ):ℝ) from by rw [Real.rpow_natCast]; ring,
        show u ^ ((1:ℝ)/2) * (4 * u ^ (((2:ℕ):ℝ))) = 4 * (u ^ ((1:ℝ)/2) * u ^ (((2:ℕ):ℝ))) from by ring,
        ← Real.rpow_add hu0]
      norm_num
    calc M = C * ((N:ℝ) ^ ((1:ℝ)/(4*B)) * LTv^2) := by rw [hMdef]; ring
      _ ≤ C * (u ^ ((1:ℝ)/2) * (4*(u*u))) := by
          apply mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = 4*C * u ^ ((5:ℝ)/2) := by rw [h3]; ring
  -- the main bound
  have hbound := hmain N χ hχ X hX1 T hT0
  -- identify: the main's terms with our abbreviations (they are literally the same after `set`)
  -- term bounds
  have hXg : X ^ (g : ℝ) = Real.exp (g * L) := by
    rw [Real.rpow_def_of_pos hX0, mul_comm]
  have hgL2 : (c/4) * u ^ ((1:ℝ)/2) ≤ (g/2) * L := by
    have := hR2
    rw [← hLuu]
    nlinarith
  have hgLu : g * L ≤ u/2 := by rw [← hLuu]; exact hR3
  -- fold the abbreviations into hbound
  rw [← hLTvdef] at hbound
  rw [← hNedef] at hbound
  rw [← hgdef] at hbound
  rw [← hMdef] at hbound
  -- exponentials
  have hexpX : ∀ a : ℝ, X ^ (1 + a : ℝ) = X * Real.exp (a * L) := by
    intro a
    rw [Real.rpow_add hX0, Real.rpow_one, Real.rpow_def_of_pos hX0, mul_comm L a]
  have hT2 : T^2 = Real.exp (2*u) := by
    rw [hTdef, sq, ← Real.exp_add]
    ring_nf
  -- t1
  have ht1 : 6 * M * X ^ (1 - g/2 : ℝ)
      ≤ 24*C * u ^ ((5:ℝ)/2) * (X * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))) := by
    rw [rpow_shift_as_exp X g hX0]
    have h1 : Real.exp (-(g/2) * L) ≤ Real.exp (-((c/4) * u ^ ((1:ℝ)/2))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hgL2]
    calc 6 * M * (X * Real.exp (-(g/2) * L))
        ≤ 6 * (4*C * u ^ ((5:ℝ)/2)) * (X * Real.exp (-(g/2) * L)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left hMle (by norm_num)
      _ ≤ 6 * (4*C * u ^ ((5:ℝ)/2)) * (X * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left h1 hX0.le
      _ = 24*C * u ^ ((5:ℝ)/2) * (X * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))) := by ring
  have hgle : g ≤ 1/2 := by
    rw [hgdef]
    have h1 : c * Ne ≤ 1/2 := by nlinarith
    have h2 : c * Ne / LTv ≤ c * Ne / 1 := by
      apply div_le_div_of_nonneg_left (by positivity) one_pos (by linarith)
    simpa using le_trans h2 (by linarith)
  have hXgT2 : X ^ (1 + g : ℝ) / T^2 ≤ X * Real.exp (-(u/2)) := by
    rw [hexpX g, hT2, mul_div_assoc, ← Real.exp_sub]
    apply mul_le_mul_of_nonneg_left _ hX0.le
    apply Real.exp_le_exp.mpr
    nlinarith [hgLu, hu0]
  have hXgT : X ^ (1 + g : ℝ) / T ≤ X * Real.exp (-(u/2)) := by
    rw [hexpX g, hTdef, mul_div_assoc, ← Real.exp_sub]
    apply mul_le_mul_of_nonneg_left _ hX0.le
    apply Real.exp_le_exp.mpr
    nlinarith [hgLu, hu0]
  have hu53 : u ^ ((5:ℝ)/2) ≤ u ^ (3:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  -- t2
  have ht2 : 2 * (((1 + g) - (1 - g/2)) * (M * X ^ (1 + g : ℝ) / T^2))
      ≤ 6*C * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by
    have hd : (1 + g) - (1 - g/2) = (3/2)*g := by ring
    rw [hd]
    have h1 : M * X ^ (1 + g : ℝ) / T^2 ≤ (4*C * u ^ (3:ℝ)) * (X * Real.exp (-(u/2))) := by
      rw [mul_div_assoc]
      apply mul_le_mul (le_trans hMle (by nlinarith [Real.rpow_nonneg hu0.le ((5:ℝ)/2)]))
        hXgT2 (by positivity) (by positivity)
    calc 2 * ((3/2)*g * (M * X ^ (1 + g : ℝ) / T^2)) = 3*g * (M * X ^ (1 + g : ℝ) / T^2) := by ring
      _ ≤ 3*(1/2) * ((4*C * u ^ (3:ℝ)) * (X * Real.exp (-(u/2)))) := by
          apply mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
      _ = 6*C * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by ring
  -- 1/g² bound
  have hginv : 6 / g^2 ≤ 6 * ((4/c^2) * u ^ (3:ℝ)) := by
    have h1 : 1/g ≤ (2/c) * u ^ ((3:ℝ)/2) := by
      rw [hgdef]
      have h2 : (1:ℝ)/(c * Ne / LTv) = LTv / (c * Ne) := by
        field_simp
      rw [h2]
      have h3 : c * u ^ (-(1:ℝ)/2) ≤ c * Ne := by
        apply mul_le_mul_of_nonneg_left hNe_lo hc0.le
      have h4 : LTv / (c * Ne) ≤ (2*u) / (c * u ^ (-(1:ℝ)/2)) := by
        have h4a : LTv / (c * Ne) ≤ (2*u) / (c * Ne) :=
          div_le_div_of_nonneg_right hLThi (by positivity)
        have h4b : (2*u) / (c * Ne) ≤ (2*u) / (c * u ^ (-(1:ℝ)/2)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h3
        linarith
      refine le_trans h4 (le_of_eq ?_)
      rw [show u ^ (-(1:ℝ)/2) = (u ^ ((1:ℝ)/2))⁻¹ from by
        rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hu0.le]]
      rw [div_eq_mul_inv, mul_inv, inv_inv]
      rw [show u ^ ((3:ℝ)/2) = u * u ^ ((1:ℝ)/2) from by
        rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hu0, Real.rpow_one]]
      ring
    have h5 : (1/g)^2 ≤ ((2/c) * u ^ ((3:ℝ)/2))^2 := by
      apply pow_le_pow_left₀ (by positivity) h1
    have h6 : ((2/c) * u ^ ((3:ℝ)/2))^2 = (4/c^2) * u ^ (3:ℝ) := by
      rw [mul_pow, div_pow, show (u ^ ((3:ℝ)/2))^2 = u ^ ((3:ℝ)/2) * u ^ ((3:ℝ)/2) by ring,
        ← Real.rpow_add hu0]
      norm_num
    have h7 : (1/g)^2 = 1/g^2 := by
      rw [div_pow, one_pow]
    rw [h7, h6] at h5
    have h8 : 6/g^2 = 6*(1/g^2) := by ring
    rw [h8]
    linarith
  -- t3
  have ht3 : 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T
      ≤ (48/c^2) * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by
    have h1 : 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T
        = 2 * (6 / g^2) * (X ^ (1 + g : ℝ) / T) := by ring
    rw [h1]
    calc 2 * (6 / g^2) * (X ^ (1 + g : ℝ) / T)
        ≤ 2 * (6 * ((4/c^2) * u ^ (3:ℝ))) * (X * Real.exp (-(u/2))) := by
          apply mul_le_mul (by linarith) hXgT (by positivity) (by positivity)
      _ = (48/c^2) * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by ring
  have hR4a := poly_exp_absorption c (24*C) (6*C + 48/c^2) hc0 hc12 (by positivity) (by positivity)
    u (le_trans (le_max_right _ _) huM)
  have hsum : 6 * M * X ^ (1 - g/2 : ℝ)
      + 2 * (((1 + g) - (1 - g/2)) * (M * X ^ (1 + g : ℝ) / T^2))
      + 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T
      ≤ (30*C + 48/c^2) * X * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
    have h2 : X * (24*C * u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
          + (6*C + 48/c^2) * u ^ (3:ℝ) * Real.exp (-(u/2)))
        ≤ X * ((24*C + (6*C + 48/c^2)) * Real.exp (-((c/8) * u ^ ((1:ℝ)/2)))) := by
      apply mul_le_mul_of_nonneg_left hR4a hX0.le
    calc 6 * M * X ^ (1 - g/2 : ℝ)
        + 2 * (((1 + g) - (1 - g/2)) * (M * X ^ (1 + g : ℝ) / T^2))
        + 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T
        ≤ 24*C * u ^ ((5:ℝ)/2) * (X * Real.exp (-((c/4) * u ^ ((1:ℝ)/2))))
          + 6*C * u ^ (3:ℝ) * (X * Real.exp (-(u/2)))
          + (48/c^2) * u ^ (3:ℝ) * (X * Real.exp (-(u/2))) := by
          exact add_le_add (add_le_add ht1 ht2) ht3
      _ = X * (24*C * u ^ ((5:ℝ)/2) * Real.exp (-((c/4) * u ^ ((1:ℝ)/2)))
          + (6*C + 48/c^2) * u ^ (3:ℝ) * Real.exp (-(u/2))) := by ring
      _ ≤ X * ((24*C + (6*C + 48/c^2)) * Real.exp (-((c/8) * u ^ ((1:ℝ)/2)))) := h2
      _ = (30*C + 48/c^2) * X * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by ring
  have hfin : Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) ≤ Real.exp (-(c/8 * L ^ ((1:ℝ)/10))) := by
    apply Real.exp_le_exp.mpr
    have h1 : u ^ ((1:ℝ)/2) = L ^ ((1:ℝ)/4) := by
      rw [hudef, ← Real.rpow_mul hL0.le]
      norm_num
    have h2 : L ^ ((1:ℝ)/10) ≤ L ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    rw [h1]
    nlinarith
  have h2pi : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ (6 * M * X ^ (1 - g/2 : ℝ)
        + 2 * (((1 + g) - (1 - g/2)) * (M * X ^ (1 + g : ℝ) / T^2))
        + 2 * ((6 / g^2) * X ^ (1 + g : ℝ)) / T) / (2 * Real.pi) := hbound
    _ ≤ ((30*C + 48/c^2) * X * Real.exp (-((c/8) * u ^ ((1:ℝ)/2)))) / (2 * Real.pi) := by
        apply div_le_div_of_nonneg_right hsum (by positivity)
    _ ≤ (30*C + 48/c^2) * X * Real.exp (-((c/8) * u ^ ((1:ℝ)/2))) := by
        apply div_le_self (by positivity) h2pi
    _ ≤ (30*C + 48/c^2) * X * Real.exp (-(c/8 * L ^ ((1:ℝ)/10))) := by
        apply mul_le_mul_of_nonneg_left hfin (by positivity)

open scoped Classical in
open ArithmeticFunction in
/-- **W3b-i: per-prime power-mass bound** — for a prime `p` and `X ≥ 2`, the von Mangoldt mass on
    powers of `p` up to `X` is at most `(log X / log 2 + 1)·log p`: there are at most
    `log X / log 2 + 1` exponents `k ≥ 1` with `p^k ≤ X`, each contributing `Λ(p^k) = log p`. -/
lemma vonMangoldt_prime_powers_le (p : ℕ) (hp : p.Prime) (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n),
      vonMangoldt n
    ≤ (Real.log X / Real.log 2 + 1) * Real.log p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : (0:ℝ) ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hlogp : (0:ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  set K : ℕ := ⌊Real.log X / Real.log 2⌋₊ with hKdef
  -- the filter is the image of the exponents k ∈ Icc 1 K under k ↦ p^k
  have hsub : (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n)
      ⊆ (Finset.Icc 1 K).image (fun k => p ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnX, k, hk1, hkn⟩ := hn
    rw [Finset.mem_image]
    refine ⟨k, ?_, hkn⟩
    rw [Finset.mem_Icc]
    refine ⟨hk1, ?_⟩
    -- p^k ≤ X ⇒ 2^k ≤ X ⇒ k·log2 ≤ logX ⇒ k ≤ K
    have h1 : p ^ k ≤ X := by omega
    have h2 : 2 ^ k ≤ X := le_trans (Nat.pow_le_pow_left hp2 k) h1
    have h3 : (k:ℝ) * Real.log 2 ≤ Real.log X := by
      have h4 : ((2:ℕ):ℝ) ^ k ≤ (X:ℝ) := by exact_mod_cast h2
      have h5 := Real.log_le_log (by positivity) h4
      rwa [Real.log_pow, Nat.cast_ofNat] at h5
    apply Nat.le_floor
    rw [le_div_iff₀ hlog2]
    exact h3
  have hnonneg : ∀ n ∈ (Finset.Icc 1 K).image (fun k => p ^ k), 0 ≤ vonMangoldt n :=
    fun n _ => vonMangoldt_nonneg
  calc ∑ n ∈ (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n), vonMangoldt n
      ≤ ∑ n ∈ (Finset.Icc 1 K).image (fun k => p ^ k), vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => vonMangoldt_nonneg)
    _ = ∑ k ∈ Finset.Icc 1 K, vonMangoldt (p ^ k) := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact Nat.pow_right_injective hp2 hab
    _ = ∑ k ∈ Finset.Icc 1 K, Real.log p := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ = (K : ℝ) * Real.log p := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp [nsmul_eq_mul]
    _ ≤ (Real.log X / Real.log 2 + 1) * Real.log p := by
        apply mul_le_mul_of_nonneg_right _ hlogp
        have := Nat.floor_le (by positivity : (0:ℝ) ≤ Real.log X / Real.log 2)
        rw [hKdef]
        linarith

open scoped Classical in
open ArithmeticFunction in
/-- **W3b-ii: the non-unit von Mangoldt mass is polylog** — for `q ≥ 1`, `X ≥ 2`:
    `∑_{n≤X, ¬IsUnit(n mod q)} Λ(n) ≤ (log X/log 2 + 1)·log q`. Prime-power support: each
    contributing `n = p^k` has `p ∣ q`; per-prime mass ≤ `(logX/log2+1)·log p` (W3b-i);
    `∑_{p∣q} log p = log ∏ p ≤ log q`. -/
lemma vonMangoldt_nonunit_sum_le (q : ℕ) [NeZero q] (X : ℕ) (hX : 2 ≤ X) :
    ∑ n ∈ (Finset.range (X+1)).filter (fun n => ¬ IsUnit ((n : ℕ) : ZMod q)), vonMangoldt n
    ≤ (Real.log X / Real.log 2 + 1) * Real.log q := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : (0:ℝ) ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hcoef : (0:ℝ) ≤ Real.log X / Real.log 2 + 1 := by positivity
  -- drop the Λ = 0 terms
  rw [← Finset.sum_filter_ne_zero]
  -- the surviving support embeds in the union of p-power filters, p ∈ q.primeFactors
  set T := ((Finset.range (X+1)).filter (fun n => ¬ IsUnit ((n : ℕ) : ZMod q))).filter
    (fun n => vonMangoldt n ≠ 0) with hTdef
  have hsub : T ⊆ q.primeFactors.biUnion
      (fun p => (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n)) := by
    intro n hn
    rw [hTdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨⟨hnX, hnu⟩, hΛ⟩ := hn
    have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, k, hp, hk, hpk⟩ := hpp
    have hpN : p.Prime := Nat.prime_iff.mpr hp
    -- ¬IsUnit(p^k mod q) ⇒ ¬coprime p q ⇒ p ∣ q
    have hpq : p ∣ q := by
      by_contra hnd
      apply hnu
      rw [ZMod.isUnit_iff_coprime]
      have h1 : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hpN).mpr hnd
      have h2 : Nat.Coprime n q := by
        rw [← hpk]
        exact Nat.Coprime.pow_left k h1
      exact h2
    rw [Finset.mem_biUnion]
    refine ⟨p, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]
      exact ⟨hpN, hpq, hq0⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hnX, k, hk, hpk⟩
  -- distinct primes give disjoint power filters
  have hdisj : ∀ p ∈ q.primeFactors, ∀ p' ∈ q.primeFactors, p ≠ p' →
      Disjoint ((Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n))
        ((Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p' ^ k = n)) := by
    intro p hp p' hp' hne
    rw [Finset.disjoint_left]
    intro n hn hn'
    rw [Finset.mem_filter] at hn hn'
    obtain ⟨-, k, hk1, hkn⟩ := hn
    obtain ⟨-, k', hk1', hkn'⟩ := hn'
    have hpN : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpN' : p'.Prime := (Nat.mem_primeFactors.mp hp').1
    apply hne
    have h1 : p ∣ p' ^ k' := by
      rw [hkn', ← hkn]
      exact dvd_pow_self p (by omega)
    have h2 : p ∣ p' := hpN.dvd_of_dvd_pow h1
    exact (Nat.prime_dvd_prime_iff_eq hpN hpN').mp h2
  calc ∑ n ∈ T, vonMangoldt n
      ≤ ∑ n ∈ q.primeFactors.biUnion
          (fun p => (Finset.range (X+1)).filter (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n)),
          vonMangoldt n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _
        exact vonMangoldt_nonneg
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ (Finset.range (X+1)).filter
          (fun n => ∃ k, 1 ≤ k ∧ p ^ k = n), vonMangoldt n :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ p ∈ q.primeFactors, (Real.log X / Real.log 2 + 1) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact vonMangoldt_prime_powers_le p (Nat.mem_primeFactors.mp hp).1 X hX
    _ = (Real.log X / Real.log 2 + 1) * ∑ p ∈ q.primeFactors, Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ (Real.log X / Real.log 2 + 1) * Real.log q := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        have h1 : ∑ p ∈ q.primeFactors, Real.log p
            = Real.log (∏ p ∈ q.primeFactors, (p:ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos.ne'
        rw [h1]
        have h2 : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
        have h5 : 0 < ∏ p ∈ q.primeFactors, p :=
          Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)
        have h3 : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) h2
        have h4 : (∏ p ∈ q.primeFactors, (p:ℝ)) = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
          push_cast
          rfl
        rw [h4]
        apply Real.log_le_log
        · exact_mod_cast h5
        · exact_mod_cast h3



open scoped Classical in
open ArithmeticFunction in
/-- **W3c: the unit-restricted ψ obeys PNT with a polylog correction** — for every modulus
    `q ≥ 1` and `X ≥ 2`:
    `|∑_{n≤X, IsUnit(n mod q)} Λ(n) − X| ≤ C·X·exp(−c(log X)^{1/10}) + (logX/log2+1)·log q`.
    Split `ψ = unit-part + nonunit-part`; `medium_PNT` for the first, W3b-ii for the second.
    This is `ψ(X,χ₀)` (`MulChar.one_apply` gives the indicator), the χ₀ input to the W5 wiring. -/
theorem psi_unit_sum_bound : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (q : ℕ) [NeZero q], ∀ X : ℝ, 2 ≤ X →
    |(∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) - X|
      ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10))
        + (Real.log X / Real.log 2 + 1) * Real.log q := by
  obtain ⟨c, C, hc, hC, hpnt⟩ := medium_PNT
  refine ⟨c, C, hc, hC, ?_⟩
  intro q _ X hX
  have hX0 : (0:ℝ) < X := by linarith
  have hXn : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hfloor0 : (0:ℝ) < (⌊X⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊X⌋₊)
  have hfloorle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : (0:ℝ) ≤ Real.log q := by
    apply Real.log_nonneg
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  -- ψ = unit + nonunit
  have hsplit : (∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n)
      = (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0)
        + ∑ n ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun n => ¬ IsUnit ((n : ℕ) : ZMod q)),
            vonMangoldt n := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : IsUnit ((n : ℕ) : ZMod q) <;> simp [h]
  set U := ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
    if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0 with hUdef
  set V := ∑ n ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun n => ¬ IsUnit ((n : ℕ) : ZMod q)),
    vonMangoldt n with hVdef
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
  -- V ≤ (log⌊X⌋/log2 + 1)·log q ≤ (logX/log2 + 1)·log q
  have hVle : V ≤ (Real.log X / Real.log 2 + 1) * Real.log q := by
    have h1 := vonMangoldt_nonunit_sum_le q (X := ⌊X⌋₊) hXn
    have h2 : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X := Real.log_le_log hfloor0 hfloorle
    have h3 : (Real.log (⌊X⌋₊ : ℝ) / Real.log 2 + 1) * Real.log q
        ≤ (Real.log X / Real.log 2 + 1) * Real.log q := by
      apply mul_le_mul_of_nonneg_right _ hlogq
      have := div_le_div_of_nonneg_right h2 hlog2.le
      linarith
    exact le_trans h1 h3
  have hpntX := hpnt X hX
  -- |U − X| = |(ψ − X) − V| ≤ |ψ − X| + V
  have habs : |U - X| ≤ |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X| + V := by
    have h4 : U - X = ((∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X) - V := by
      rw [hsplit]
      ring
    rw [h4]
    calc |((∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X) - V|
        ≤ |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X| + |V| := abs_sub _ _
      _ = |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X| + V := by
          rw [abs_of_nonneg hV0]
  calc |U - X| ≤ |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), vonMangoldt n) - X| + V := habs
    _ ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10))
        + (Real.log X / Real.log 2 + 1) * Real.log q := add_le_add hpntX hVle

open ArithmeticFunction in
/-- **W4a: the two-scale identity** — for `0 < X ≤ Y`:
    `Y·S(Y) − X·S(X) = (Y−X)·ψ_c(X) + ∑_{⌊X⌋<n≤⌊Y⌋} χΛ(n)(Y−n)`, where `S` is the smoothed sum
    and `ψ_c` the sharp one. Pure algebra: `Y(1−n/Y) = Y−n`, split `range(⌊Y⌋+1)` at `⌊X⌋+1`. -/
lemma two_scale_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X Y : ℝ)
    (hX : 0 < X) (hXY : X ≤ Y) :
    ((Y:ℝ) : ℂ) * (∑ n ∈ Finset.range (⌊Y⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Y))
      - ((X:ℝ) : ℂ) * (∑ n ∈ Finset.range (⌊X⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
    = (((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * (∑ n ∈ Finset.range (⌊X⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
      + ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)) := by
  have hY0 : (0:ℝ) < Y := lt_of_lt_of_le hX hXY
  have hXC : ((X:ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hYC : ((Y:ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY0.ne'
  have hfloor : ⌊X⌋₊ + 1 ≤ ⌊Y⌋₊ + 1 := by
    have := Nat.floor_le_floor hXY
    omega
  -- per-term unsmoothing
  have hterm : ∀ (Z : ℝ) (hZ : ((Z:ℝ) : ℂ) ≠ 0) (n : ℕ),
      ((Z:ℝ) : ℂ) * (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Z))
      = χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Z:ℝ) : ℂ) - ((n:ℝ) : ℂ)) := by
    intro Z hZ n
    have h1 : ((Z:ℝ) : ℂ) * (1 - ((n:ℝ) : ℂ) / ((Z:ℝ) : ℂ)) = ((Z:ℝ) : ℂ) - ((n:ℝ) : ℂ) := by
      field_simp
    calc ((Z:ℝ) : ℂ) * (χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Z))
        = χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)
            * (((Z:ℝ) : ℂ) * (1 - ((n:ℝ) : ℂ) / ((Z:ℝ) : ℂ))) := by
          push_cast
          ring
      _ = χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Z:ℝ) : ℂ) - ((n:ℝ) : ℂ)) := by
          rw [h1]
  -- unsmooth both scales
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [hterm Y hYC, hterm X hXC]
  -- split the Y-range at ⌊X⌋+1
  have hsplit : ∑ n ∈ Finset.range (⌊Y⌋₊+1),
      χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))
      = (∑ n ∈ Finset.range (⌊X⌋₊+1),
          χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)))
        + ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
          χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hfloor]
  rw [hsplit]
  have hAC : (∑ n ∈ Finset.range (⌊X⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)))
      - (∑ n ∈ Finset.range (⌊X⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((X:ℝ) : ℂ) - ((n:ℝ) : ℂ)))
      = (((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ∑ n ∈ Finset.range (⌊X⌋₊+1),
          χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  linear_combination hAC

open ArithmeticFunction in
/-- **W4b: the boundary window is small** — for `2 ≤ X ≤ Y`:
    `‖∑_{⌊X⌋<n≤⌊Y⌋} χΛ(n)(Y−n)‖ ≤ (Y−X+1)·((Y−X)·log Y)`: each of the ≤ `Y−X+1` terms has
    `Λ(n) ≤ log n ≤ log Y` and `0 ≤ Y−n ≤ Y−X`. -/
lemma boundary_sum_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (X Y : ℝ)
    (hX : 2 ≤ X) (hXY : X ≤ Y) :
    ‖∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))‖
      ≤ (Y - X + 1) * ((Y - X) * Real.log Y) := by
  have hY2 : (2:ℝ) ≤ Y := le_trans hX hXY
  have hYX0 : (0:ℝ) ≤ Y - X := by linarith
  have hlogY : (0:ℝ) ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hfloorle : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_le_floor hXY
  -- per-term bound
  have hterm : ∀ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
      ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))‖
        ≤ (Y - X) * Real.log Y := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hnX : X < (n:ℝ) := by
      have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
      have h2 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      push_cast at h2
      linarith
    have hnY : (n:ℝ) ≤ Y := by
      have h1 : n ≤ ⌊Y⌋₊ := by omega
      have h2 : ((n:ℕ):ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast h1
      have h3 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
      linarith
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by linarith
    rw [norm_mul, norm_mul]
    have h4 : ‖((vonMangoldt n : ℝ) : ℂ)‖ ≤ Real.log Y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      calc vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
        _ ≤ Real.log Y := Real.log_le_log (by linarith) hnY
    have h5 : ‖((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)‖ ≤ Y - X := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      linarith
    calc ‖χ (n : ZMod N)‖ * ‖((vonMangoldt n : ℝ) : ℂ)‖ * ‖((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)‖
        ≤ 1 * Real.log Y * (Y - X) := by
          apply mul_le_mul _ h5 (norm_nonneg _) (by positivity)
          apply mul_le_mul (DirichletCharacter.norm_le_one χ _) h4 (norm_nonneg _) zero_le_one
      _ = (Y - X) * Real.log Y := by ring
  -- count bound
  have hcard : ((Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1)).card : ℝ) ≤ Y - X + 1 := by
    rw [Nat.card_Ico]
    have h1 : (⌊Y⌋₊ + 1) - (⌊X⌋₊ + 1) = ⌊Y⌋₊ - ⌊X⌋₊ := by omega
    rw [h1, Nat.cast_sub hfloorle]
    have h2 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
    have h3 : X - 1 ≤ (⌊X⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one X
      linarith
    linarith
  calc ‖∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
        χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))‖
      ≤ ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
          ‖χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1), (Y - X) * Real.log Y :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1)).card : ℝ) * ((Y - X) * Real.log Y) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y - X + 1) * ((Y - X) * Real.log Y) := by
        apply mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **W4c-i: solve the two-scale identity for the sharp sum** — from
    `Y·SY − X·SX = (Y−X)·ψc + R` with `X < Y` and norm bounds, conclude
    `‖ψc‖ ≤ (Y·BY + X·BX + Bnd)/(Y−X)`. -/
lemma sharp_recovery_norm (ψc SY SX R : ℂ) (X Y BY BX Bnd : ℝ)
    (hX : 0 < X) (hXY : X < Y)
    (hid : ((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX = (((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ψc + R)
    (hSY : ‖SY‖ ≤ BY) (hSX : ‖SX‖ ≤ BX) (hR : ‖R‖ ≤ Bnd) :
    ‖ψc‖ ≤ (Y * BY + X * BX + Bnd) / (Y - X) := by
  have hYX0 : (0:ℝ) < Y - X := by linarith
  have h1 : (((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ψc = ((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX - R := by
    rw [hid]
    ring
  have h2 : ‖(((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ψc‖ = (Y - X) * ‖ψc‖ := by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hYX0]
  have h3 : ‖((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX - R‖ ≤ Y * BY + X * BX + Bnd := by
    have hnY : ‖((Y:ℝ) : ℂ) * SY‖ ≤ Y * BY := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact mul_le_mul_of_nonneg_left hSY (by linarith)
    have hnX : ‖((X:ℝ) : ℂ) * SX‖ ≤ X * BX := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
      exact mul_le_mul_of_nonneg_left hSX hX.le
    calc ‖((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX - R‖
        ≤ ‖((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX‖ + ‖R‖ := norm_sub_le _ _
      _ ≤ (‖((Y:ℝ) : ℂ) * SY‖ + ‖((X:ℝ) : ℂ) * SX‖) + ‖R‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ Y * BY + X * BX + Bnd := by
          have := add_le_add (add_le_add hnY hnX) hR
          linarith
  rw [le_div_iff₀ hYX0]
  calc ‖ψc‖ * (Y - X) = (Y - X) * ‖ψc‖ := by ring
    _ = ‖(((Y:ℝ) : ℂ) - ((X:ℝ) : ℂ)) * ψc‖ := h2.symm
    _ = ‖((Y:ℝ) : ℂ) * SY - ((X:ℝ) : ℂ) * SX - R‖ := by rw [h1]
    _ ≤ Y * BY + X * BX + Bnd := h3

/-- **W4c-ii: polynomial absorption at linear exponent** — `u^m·e^{−a·u} ≤ e^{−(a/2)·u}` for
    `u ≥ max 1 (4m/a)²` (`m·log u ≤ 2m·√u ≤ (a/2)·u`). -/
lemma rpow_exp_absorb (a m : ℝ) (ha : 0 < a) (hm : 0 ≤ m) :
    ∀ u : ℝ, max 1 ((4*m/a)^2) ≤ u →
    u ^ (m : ℝ) * Real.exp (-(a * u)) ≤ Real.exp (-((a/2) * u)) := by
  intro u hu
  have hu1 : (1:ℝ) ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : (0:ℝ) < u := by linarith
  have hum : (4*m/a)^2 ≤ u := le_trans (le_max_right _ _) hu
  have hsq : 4*m/a ≤ u ^ ((1:ℝ)/2) := by
    have h1 : ((4*m/a)^2) ^ ((1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) hum (by norm_num)
    rwa [show ((4*m/a):ℝ)^2 = (4*m/a) * (4*m/a) by ring, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul_self (by positivity)] at h1
  have hss : u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) = u := by
    rw [← Real.rpow_add hu0]
    norm_num
  have hs0 : (0:ℝ) ≤ u ^ ((1:ℝ)/2) := Real.rpow_nonneg hu0.le _
  -- log(u^m) = m·log u ≤ 2m·√u ≤ (a/2)·u
  have hlog : Real.log (u ^ (m:ℝ)) ≤ (a/2) * u := by
    rw [Real.log_rpow hu0]
    have h2 : Real.log u ≤ 2 * u ^ ((1:ℝ)/2) := by
      have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/2)
      calc Real.log u ≤ u ^ ((1:ℝ)/2) / (1/2) := this
        _ = 2 * u ^ ((1:ℝ)/2) := by ring
    have h3 : m * Real.log u ≤ 2*m * u ^ ((1:ℝ)/2) := by nlinarith [Real.log_nonneg hu1]
    have h4 : 2*m * u ^ ((1:ℝ)/2) ≤ (a/2) * u := by
      have h5 : (4*m/a) * u ^ ((1:ℝ)/2) ≤ u ^ ((1:ℝ)/2) * u ^ ((1:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hsq hs0
      rw [hss] at h5
      have h6 : a * ((4*m/a) * u ^ ((1:ℝ)/2)) = 4*m*u ^ ((1:ℝ)/2) := by
        field_simp
      nlinarith [h5, ha]
    linarith
  have h7 : u ^ (m:ℝ) ≤ Real.exp ((a/2) * u) :=
    (Real.log_le_iff_le_exp (Real.rpow_pos_of_pos hu0 _)).mp hlog
  calc u ^ (m:ℝ) * Real.exp (-(a * u))
      ≤ Real.exp ((a/2) * u) * Real.exp (-(a * u)) :=
        mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
    _ = Real.exp (-((a/2) * u)) := by
        rw [← Real.exp_add]
        ring_nf

/-- **W4c-pre: the δ-choice facts** — with `δ = e^{−(a/2)u}` and `u ≥ max 2 (80/a)²`:
    (i) `e^{−au}/δ = δ`; (ii) `u^{10}·δ ≤ e^{−(a/4)u}`; (iii) `2u^{10} ≤ e^{u^{10}}·e^{−(a/4)u}`
    (the standalone-polylog absorption into `X = e^{u^{10}}`). -/
lemma delta_facts (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ u : ℝ, max 2 ((80/a)^2) ≤ u →
    Real.exp (-(a * u)) / Real.exp (-((a/2) * u)) = Real.exp (-((a/2) * u)) ∧
    u ^ (10:ℝ) * Real.exp (-((a/2) * u)) ≤ Real.exp (-((a/4) * u)) ∧
    2 * u ^ (10:ℝ) ≤ Real.exp (u ^ (10:ℝ)) * Real.exp (-((a/4) * u)) := by
  intro u hu
  have hu2 : (2:ℝ) ≤ u := le_trans (le_max_left _ _) hu
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hu0 : (0:ℝ) < u := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- (i) exp division
    rw [← Real.exp_sub]
    congr 1
    ring
  · -- (ii) via rpow_exp_absorb at a' := a/2
    have h1 := rpow_exp_absorb (a/2) 10 (by linarith) (by norm_num) u ?_
    · have h2 : (a/2)/2 = a/4 := by ring
      rw [h2] at h1
      exact h1
    · apply max_le
      · linarith
      · have h3 : (4*10/(a/2)) = 80/a := by
          field_simp
          ring
        rw [h3]
        exact le_trans (le_max_right _ _) hu
  · -- (iii) log route: log 2 + 10·log u ≤ u^{10} − (a/4)u
    have hu10pos : (0:ℝ) < u ^ (10:ℝ) := Real.rpow_pos_of_pos hu0 _
    have hlog : Real.log (2 * u ^ (10:ℝ)) ≤ u ^ (10:ℝ) - (a/4) * u := by
      rw [Real.log_mul (by norm_num) hu10pos.ne', Real.log_rpow hu0]
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9
        linarith
      have h5 : Real.log u ≤ 2 * u ^ ((1:ℝ)/2) := by
        have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/2)
        calc Real.log u ≤ u ^ ((1:ℝ)/2) / (1/2) := this
          _ = 2 * u ^ ((1:ℝ)/2) := by ring
      have h6 : u ^ ((1:ℝ)/2) ≤ u := by
        calc u ^ ((1:ℝ)/2) ≤ u ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
          _ = u := Real.rpow_one u
      have h7 : u ^ (9:ℝ) ≥ 512 := by
        calc (512:ℝ) = 2 ^ (9:ℝ) := by
              rw [show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              norm_num
          _ ≤ u ^ (9:ℝ) := Real.rpow_le_rpow (by norm_num) hu2 (by norm_num)
      have h8 : u ^ (10:ℝ) = u ^ (9:ℝ) * u := by
        rw [show (10:ℝ) = 9 + 1 by norm_num, Real.rpow_add hu0, Real.rpow_one]
      have h9 : (a/4) * u ≤ u := by nlinarith
      have h56 : Real.log u ≤ 2*u := by nlinarith [h5, h6, Real.log_nonneg hu1]
      have hkey : u ^ (9:ℝ) * u ≥ 512 * u := by nlinarith [h7, hu0]
      have hA : u ^ (10:ℝ) ≥ 512 * u := by
        rw [h8]
        linarith
      have hC : Real.log 2 + 10 * Real.log u ≤ 1 + 20 * u := by linarith [h4, h56]
      calc Real.log 2 + 10 * Real.log u ≤ 1 + 20 * u := hC
        _ ≤ 511 * u := by linarith
        _ = 512 * u - u := by ring
        _ ≤ u ^ (10:ℝ) - u := sub_le_sub_right hA u
        _ ≤ u ^ (10:ℝ) - (a/4) * u := sub_le_sub_left h9 _
    have h10 : (0:ℝ) < 2 * u ^ (10:ℝ) := by positivity
    have h11 := (Real.log_le_iff_le_exp h10).mp hlog
    calc 2 * u ^ (10:ℝ) ≤ Real.exp (u ^ (10:ℝ) - (a/4) * u) := h11
      _ = Real.exp (u ^ (10:ℝ)) * Real.exp (-((a/4) * u)) := by
          rw [← Real.exp_add]
          ring_nf


open ArithmeticFunction in
/-- **W4c-MAIN: THE SHARP χ≠1 SIEGEL–WALFISZ BOUND** — for every `B ≥ 1` there are
    `c₅, C₅, X₀ > 0` with: for all `X ≥ X₀`, `q ≤ (log X)^B`, `χ ≠ 1 mod q`:
    `‖ψ(X,χ)‖ = ‖∑_{n≤X} χ(n)Λ(n)‖ ≤ C₅·X·exp(−c₅(log X)^{1/10})`. Two-scale recovery at
    `Y = X(1+δ)`, `δ = e^{−(c₂'/2)(log X)^{1/10}}`, from the smoothed bound at both scales. -/
theorem psi_sharp_SW_rate (B : ℝ) (hB : 1 ≤ B) :
    ∃ c₅ C₅ X₀ : ℝ, 0 < c₅ ∧ 0 < C₅ ∧ ∀ X : ℝ, X₀ ≤ X →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    (N:ℝ) ≤ Real.log X ^ (B : ℝ) →
    ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖
      ≤ C₅ * X * Real.exp (-(c₅ * Real.log X ^ ((1:ℝ)/10))) := by
  obtain ⟨c₂, C₂, X₀', hc₂0, hC₂0, hrate⟩ := psi_smooth_SW_rate B hB
  set a := min c₂ 1 with hadef
  have ha0 : 0 < a := lt_min hc₂0 one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have hac₂ : a ≤ c₂ := min_le_left _ _
  set M := max 2 ((80/a)^2) with hMdef
  have hM2 : (2:ℝ) ≤ M := le_max_left _ _
  have hM0 : (0:ℝ) ≤ M := by linarith
  refine ⟨a/4, 5*C₂ + 3, max X₀' (Real.exp (M^10)), by positivity, by positivity, ?_⟩
  intro X hX N _ χ hχ hNB
  have hXX₀ : X₀' ≤ X := le_trans (le_max_left _ _) hX
  -- scales
  have hLM : M^10 ≤ Real.log X := by
    have h1 : Real.exp (M^10) ≤ X := le_trans (le_max_right _ _) hX
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hM10 : (1024:ℝ) ≤ M^10 := by
    calc (1024:ℝ) = 2^10 := by norm_num
      _ ≤ M^10 := by
          apply pow_le_pow_left₀ (by norm_num) hM2
  have hL1 : (1:ℝ) ≤ Real.log X := by linarith
  have hL0 : (0:ℝ) < Real.log X := by linarith
  have hX2 : (2:ℝ) ≤ X := by
    have h1 : Real.exp (M^10) ≤ X := le_trans (le_max_right _ _) hX
    have h2 : (2:ℝ) ≤ Real.exp (M^10) := by
      have h3 := Real.add_one_le_exp (M^10)
      linarith
    linarith
  have hX1 : (1:ℝ) < X := by linarith
  have hX0 : (0:ℝ) < X := by linarith
  set u := Real.log X ^ ((1:ℝ)/10) with hudef
  have hu0 : (0:ℝ) < u := Real.rpow_pos_of_pos hL0 _
  have huM : M ≤ u := by
    have h1 : (M^10) ^ ((1:ℝ)/10) ≤ (Real.log X) ^ ((1:ℝ)/10) :=
      Real.rpow_le_rpow (by positivity) hLM (by norm_num)
    rwa [show (M:ℝ)^10 = M^((10:ℕ):ℝ) from by rw [Real.rpow_natCast],
      ← Real.rpow_mul hM0, show ((10:ℕ):ℝ) * ((1:ℝ)/10) = 1 by norm_num,
      Real.rpow_one] at h1
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hu10 : u ^ (10:ℝ) = Real.log X := by
    rw [hudef, ← Real.rpow_mul hL0.le]
    norm_num
  -- δ and Y
  set δ := Real.exp (-((a/2) * u)) with hδdef
  have hδ0 : (0:ℝ) < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    rw [hδdef]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  set Y := X * (1 + δ) with hYdef
  have hXY : X < Y := by
    rw [hYdef]
    nlinarith
  have hY2X : Y ≤ 2*X := by
    rw [hYdef]
    nlinarith
  have hYX₀ : X₀' ≤ Y := by linarith
  have hlogXY : Real.log X ≤ Real.log Y := Real.log_le_log hX0 hXY.le
  have hNB_Y : (N:ℝ) ≤ Real.log Y ^ (B : ℝ) := by
    calc (N:ℝ) ≤ Real.log X ^ (B:ℝ) := hNB
      _ ≤ Real.log Y ^ (B:ℝ) := Real.rpow_le_rpow hL0.le hlogXY (by linarith)
  -- smoothed bounds at both scales, weakened to the a-rate at X
  have hrX : Real.exp (-(c₂ * Real.log Y ^ ((1:ℝ)/10))) ≤ Real.exp (-(a * u)) := by
    apply Real.exp_le_exp.mpr
    have h1 : u ≤ Real.log Y ^ ((1:ℝ)/10) :=
      Real.rpow_le_rpow hL0.le hlogXY (by norm_num)
    nlinarith [Real.rpow_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ Y)) ((1:ℝ)/10), hu0]
  have hrXX : Real.exp (-(c₂ * Real.log X ^ ((1:ℝ)/10))) ≤ Real.exp (-(a * u)) := by
    apply Real.exp_le_exp.mpr
    rw [← hudef]
    nlinarith [hu0]
  have hSX := hrate X hXX₀ N χ hχ hNB
  have hSY := hrate Y hYX₀ N χ hχ hNB_Y
  have hSX' : ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X)‖
      ≤ C₂ * X * Real.exp (-(a * u)) := by
    calc ‖_‖ ≤ C₂ * X * Real.exp (-(c₂ * Real.log X ^ ((1:ℝ)/10))) := hSX
      _ ≤ C₂ * X * Real.exp (-(a * u)) := by
          apply mul_le_mul_of_nonneg_left hrXX (by positivity)
  have hSY' : ‖∑ n ∈ Finset.range (⌊Y⌋₊ + 1),
      χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Y)‖
      ≤ C₂ * (2*X) * Real.exp (-(a * u)) := by
    calc ‖_‖ ≤ C₂ * Y * Real.exp (-(c₂ * Real.log Y ^ ((1:ℝ)/10))) := hSY
      _ ≤ C₂ * (2*X) * Real.exp (-(a * u)) := by
          apply mul_le_mul (by nlinarith) hrX (Real.exp_pos _).le (by positivity)
  -- the identity, boundary bound, and recovery
  have hid := two_scale_identity χ X Y hX0 hXY.le
  have hR := boundary_sum_bound χ X Y hX2 hXY.le
  have hrec := sharp_recovery_norm
    (∑ n ∈ Finset.range (⌊X⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ))
    (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / Y))
    (∑ n ∈ Finset.range (⌊X⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℝ) / X))
    (∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1),
      χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ) * (((Y:ℝ) : ℂ) - ((n:ℝ) : ℂ)))
    X Y (C₂ * (2*X) * Real.exp (-(a * u))) (C₂ * X * Real.exp (-(a * u)))
    ((Y - X + 1) * ((Y - X) * Real.log Y))
    hX0 hXY hid hSY' hSX' hR
  -- the δ-facts
  obtain ⟨hdf1, hdf2, hdf3⟩ := delta_facts a ha0 ha1 u (hMdef ▸ huM)
  -- numeric collapse
  have hYX : Y - X = δ * X := by rw [hYdef]; ring
  have hlog2X : Real.log Y ≤ 2 * u ^ (10:ℝ) := by
    have h1 : Real.log Y ≤ Real.log (2*X) := Real.log_le_log (by linarith) hY2X
    have h2 : Real.log (2*X) = Real.log 2 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    rw [hu10]
    linarith [hL1]
  -- numeric collapse of the recovered bound
  set E := Real.exp (-(a * u)) with hEdef
  set F := Real.exp (-((a/4) * u)) with hFdef
  have hE0 : (0:ℝ) < E := Real.exp_pos _
  have hF0 : (0:ℝ) < F := Real.exp_pos _
  have hδF : δ ≤ F := by
    rw [hδdef, hFdef]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hEδ : E / δ = δ := hdf1
  have hu10F : u ^ (10:ℝ) * δ ≤ F := hdf2
  have h2u10 : 2 * u ^ (10:ℝ) ≤ X * F := by
    have h1 : Real.exp (u ^ (10:ℝ)) = X := by
      rw [hu10, Real.exp_log hX0]
    calc 2 * u ^ (10:ℝ) ≤ Real.exp (u ^ (10:ℝ)) * F := hdf3
      _ = X * F := by rw [h1]
  -- the divided pieces
  have hδX0 : (0:ℝ) < δ * X := by positivity
  have hnum1 : Y * (C₂ * (2*X) * E) + X * (C₂ * X * E) ≤ 5 * C₂ * X^2 * E := by
    have h1 : Y * (C₂ * (2*X) * E) ≤ (2*X) * (C₂ * (2*X) * E) := by
      apply mul_le_mul_of_nonneg_right hY2X (by positivity)
    nlinarith [hE0, hX0, hC₂0]
  have hdiv1 : (5 * C₂ * X^2 * E) / (δ * X) = 5 * C₂ * X * δ := by
    rw [show (5 * C₂ * X^2 * E) / (δ * X) = 5 * C₂ * X * (E / δ) from by
      field_simp]
    rw [hEδ]
  have hdiv2 : ((δ * X + 1) * ((δ * X) * Real.log Y)) / (δ * X)
      = (δ * X + 1) * Real.log Y := by
    field_simp
  -- assemble
  have hfinal : (Y * (C₂ * (2*X) * E) + X * (C₂ * X * E)
      + (Y - X + 1) * ((Y - X) * Real.log Y)) / (Y - X)
      ≤ (5*C₂ + 3) * X * F := by
    rw [hYX]
    rw [add_div]
    have hp1 : (Y * (C₂ * (2*X) * E) + X * (C₂ * X * E)) / (δ * X)
        ≤ (5 * C₂ * X^2 * E) / (δ * X) :=
      div_le_div_of_nonneg_right hnum1 hδX0.le
    rw [hdiv1] at hp1
    rw [hdiv2]
    have hp2 : 5 * C₂ * X * δ ≤ 5 * C₂ * X * F := by
      apply mul_le_mul_of_nonneg_left hδF (by positivity)
    have hp3 : (δ * X + 1) * Real.log Y ≤ (δ * X + 1) * (2 * u ^ (10:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hlog2X (by positivity)
    have hp4 : (δ * X + 1) * (2 * u ^ (10:ℝ))
        = (2 * u ^ (10:ℝ) * δ) * X + 2 * u ^ (10:ℝ) := by ring
    have hp5 : (2 * u ^ (10:ℝ) * δ) * X ≤ 2 * F * X := by
      apply mul_le_mul_of_nonneg_right _ hX0.le
      calc 2 * u ^ (10:ℝ) * δ = 2 * (u ^ (10:ℝ) * δ) := by ring
        _ ≤ 2 * F := by linarith [hu10F]
    calc (Y * (C₂ * (2*X) * E) + X * (C₂ * X * E)) / (δ * X)
          + (δ * X + 1) * Real.log Y
        ≤ 5 * C₂ * X * δ + (δ * X + 1) * (2 * u ^ (10:ℝ)) := by
          linarith [hp1, hp3]
      _ ≤ 5 * C₂ * X * F + (2 * F * X + X * F) := by
          rw [hp4]
          have := add_le_add hp5 h2u10
          linarith [hp2, this]
      _ = (5*C₂ + 3) * X * F := by ring
  calc ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1), χ (n : ZMod N) * ((vonMangoldt n : ℝ) : ℂ)‖
      ≤ (Y * (C₂ * (2*X) * E) + X * (C₂ * X * E)
          + (Y - X + 1) * ((Y - X) * Real.log Y)) / (Y - X) := hrec
    _ ≤ (5*C₂ + 3) * X * F := hfinal


set_option maxHeartbeats 4000000 in
open DirichletCharacter Complex ArithmeticFunction Finset in
/-- **W5: SIEGEL–WALFISZ, the statement of the RatedWindow axiom, PROVEN** — orthogonality wiring
    of the χ₀ bound (W3) and the sharp χ≠1 bound (W4) with the character count `φ(q)`. -/
theorem siegel_walfisz_proven (B : ℝ) (hB : 1 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log X ^ (B : ℝ) →
    ∀ a : ZMod q, IsUnit a →
    |(∑ n ∈ Finset.range (⌊X⌋₊ + 1), if a = ((n : ZMod q)) then vonMangoldt n else 0)
      - X / q.totient| ≤ C * X * Real.exp (-c * Real.log X ^ ((1:ℝ)/10)) := by
  obtain ⟨c₃, C₃, hc₃0, hC₃0, hχ₀⟩ := psi_unit_sum_bound
  obtain ⟨c₅, C₅, X₅, hc₅0, hC₅0, hsharp⟩ := psi_sharp_SW_rate B hB
  set c := min (min c₃ (c₅/2)) (1/2) with hcdef
  have hc0 : 0 < c := by
    apply lt_min (lt_min hc₃0 (by linarith)) (by norm_num)
  set M := max 2 (max ((40*B/c₅)^2) (Real.log (60*B))) with hMdef
  have hM2 : (2:ℝ) ≤ M := le_max_left _ _
  refine ⟨c, C₃ + C₅ + 1, by positivity, by positivity,
    max X₅ (Real.exp (M^10)), ?_⟩
  intro X hX q _ hqB a ha
  have hXX₅ : X₅ ≤ X := le_trans (le_max_left _ _) hX
  have hLM : M^10 ≤ Real.log X := by
    have h1 : Real.exp (M^10) ≤ X := le_trans (le_max_right _ _) hX
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hM10 : (1024:ℝ) ≤ M^10 := by
    calc (1024:ℝ) = 2^10 := by norm_num
      _ ≤ M^10 := pow_le_pow_left₀ (by norm_num) hM2 10
  have hL1 : (1:ℝ) ≤ Real.log X := by linarith
  have hL0 : (0:ℝ) < Real.log X := by linarith
  have hX2 : (2:ℝ) ≤ X := by
    have h1 : Real.exp (M^10) ≤ X := le_trans (le_max_right _ _) hX
    have h2 := Real.add_one_le_exp (M^10)
    linarith
  have hX0 : (0:ℝ) < X := by linarith
  set u := Real.log X ^ ((1:ℝ)/10) with hudef
  have hu0 : (0:ℝ) < u := Real.rpow_pos_of_pos hL0 _
  have huM : M ≤ u := by
    have h1 : (M^10) ^ ((1:ℝ)/10) ≤ (Real.log X) ^ ((1:ℝ)/10) :=
      Real.rpow_le_rpow (by positivity) hLM (by norm_num)
    rwa [show (M:ℝ)^10 = M^((10:ℕ):ℝ) from by rw [Real.rpow_natCast],
      ← Real.rpow_mul (by linarith : (0:ℝ) ≤ M),
      show ((10:ℕ):ℝ) * ((1:ℝ)/10) = 1 by norm_num, Real.rpow_one] at h1
  have hu2 : (2:ℝ) ≤ u := le_trans hM2 huM
  have hu10 : u ^ (10:ℝ) = Real.log X := by
    rw [hudef, ← Real.rpow_mul hL0.le]
    norm_num
  -- q and totient facts
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hφ1 : 1 ≤ q.totient := Nat.totient_pos.mpr (by omega)
  have hφq : q.totient ≤ q := Nat.totient_le q
  -- the ℂ-level orthogonality split
  have hAP := psi_ap_orthogonality q a ha (⌊X⌋₊ + 1)
  have ha_inv : IsUnit (a⁻¹ : ZMod q) :=
    IsUnit.of_mul_eq_one a (ZMod.inv_mul_of_unit a ha)
  have hone : (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := MulChar.one_apply ha_inv
  -- ψ₀ as the real unit-restricted sum
  have hψ₀ : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      (1 : DirichletCharacter ℂ q) ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))
      = (((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : IsUnit ((n : ℕ) : ZMod q)
    · rw [MulChar.one_apply h, if_pos h, one_mul]
    · rw [MulChar.map_nonunit _ h, if_neg h, zero_mul, Complex.ofReal_zero]
  -- the real AP-sum bridge
  have hSreal : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
      if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0)
      = (((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if a = ((n : ZMod q)) then vonMangoldt n else 0 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : a = ((n : ZMod q))
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, Complex.ofReal_zero]
  -- split the character sum at χ₀
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    hone, one_mul, hψ₀] at hAP
  -- per-χ≠1 sharp bounds
  have hqB' : (q:ℝ) ≤ Real.log X ^ (B:ℝ) := hqB
  have hsharp' : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))‖
      ≤ C₅ * X * Real.exp (-(c₅ * u)) := by
    intro χ hχ
    have hne := Finset.ne_of_mem_erase hχ
    rw [norm_mul]
    calc ‖χ a⁻¹‖ * ‖∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)‖
        ≤ 1 * (C₅ * X * Real.exp (-(c₅ * u))) := by
          apply mul_le_mul (DirichletCharacter.norm_le_one χ _) _ (norm_nonneg _) zero_le_one
          rw [hudef]
          exact hsharp X hXX₅ q χ hne hqB'
      _ = C₅ * X * Real.exp (-(c₅ * u)) := one_mul _
  -- character count
  have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
      = q.totient - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hsum_erase : ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))‖
      ≤ ((q.totient - 1 : ℕ) : ℝ) * (C₅ * X * Real.exp (-(c₅ * u))) := by
    calc ‖_‖ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
            χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (C₅ * X * Real.exp (-(c₅ * u))) := Finset.sum_le_sum hsharp'
      _ = ((q.totient - 1 : ℕ) : ℝ) * (C₅ * X * Real.exp (-(c₅ * u))) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  -- q ≤ u^{10B} and the character-count absorption
  have hq_u : (q:ℝ) ≤ u ^ (10*B : ℝ) := by
    calc (q:ℝ) ≤ Real.log X ^ (B:ℝ) := hqB
      _ = u ^ (10*B : ℝ) := by
          rw [← hu10, ← Real.rpow_mul (Real.rpow_nonneg hL0.le _)]
  have habsorb : u ^ (10*B : ℝ) * Real.exp (-(c₅ * u)) ≤ Real.exp (-((c₅/2) * u)) := by
    apply rpow_exp_absorb c₅ (10*B) hc₅0 (by linarith) u
    apply max_le (by linarith)
    calc (4*(10*B)/c₅)^2 = (40*B/c₅)^2 := by ring_nf
      _ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
      _ ≤ u := huM
  have hcount : ((q.totient - 1 : ℕ) : ℝ) * (C₅ * X * Real.exp (-(c₅ * u)))
      ≤ C₅ * X * Real.exp (-((c₅/2) * u)) := by
    have h1 : ((q.totient - 1 : ℕ) : ℝ) ≤ (q:ℝ) := by
      have h2 : q.totient - 1 ≤ q := by omega
      exact_mod_cast h2
    calc ((q.totient - 1 : ℕ) : ℝ) * (C₅ * X * Real.exp (-(c₅ * u)))
        ≤ u ^ (10*B : ℝ) * (C₅ * X * Real.exp (-(c₅ * u))) := by
          apply mul_le_mul_of_nonneg_right (le_trans h1 hq_u) (by positivity)
      _ = C₅ * X * (u ^ (10*B : ℝ) * Real.exp (-(c₅ * u))) := by ring
      _ ≤ C₅ * X * Real.exp (-((c₅/2) * u)) := by
          apply mul_le_mul_of_nonneg_left habsorb (by positivity)
  -- the χ₀ deviation with its polylog absorbed
  have hχ₀X := hχ₀ q X hX2
  have hpolylog : (Real.log X / Real.log 2 + 1) * Real.log q ≤ X * Real.exp (-((1:ℝ)/2 * u)) := by
    have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h1 : Real.log X / Real.log 2 + 1 ≤ 3 * u ^ (10:ℝ) := by
      have h2 : Real.log X / Real.log 2 ≤ 2 * Real.log X := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hL0]
      have h3 : (1:ℝ) ≤ u ^ (10:ℝ) := by
        rw [hu10]
        exact hL1
      have h3b : u ^ (10:ℝ) = Real.log X := hu10
      linarith
    have h4 : Real.log q ≤ 20 * B * u := by
      rcases eq_or_lt_of_le hq1 with heq | hgt
      · rw [← heq]
        simp
        positivity
      · have h5 : Real.log q ≤ Real.log (Real.log X ^ (B:ℝ)) :=
          Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)) hqB
        rw [Real.log_rpow hL0, ← hu10, Real.log_rpow hu0] at h5
        have h6 : Real.log u ≤ 2 * u ^ ((1:ℝ)/2) := by
          have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/2)
          calc Real.log u ≤ u ^ ((1:ℝ)/2) / (1/2) := this
            _ = 2 * u ^ ((1:ℝ)/2) := by ring
        have h7 : u ^ ((1:ℝ)/2) ≤ u := by
          calc u ^ ((1:ℝ)/2) ≤ u ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = u := Real.rpow_one u
        calc Real.log q ≤ B * (10 * Real.log u) := h5
          _ ≤ B * (10 * (2 * u)) := by
              apply mul_le_mul_of_nonneg_left _ (by linarith)
              nlinarith [h6, h7]
          _ = 20 * B * u := by ring
    have h8 : (Real.log X / Real.log 2 + 1) * Real.log q ≤ 60 * B * u ^ (11:ℝ) := by
      have h9 : (0:ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have h10 : u ^ (10:ℝ) * u = u ^ (11:ℝ) := by
        rw [show (11:ℝ) = 10 + 1 by norm_num, Real.rpow_add hu0, Real.rpow_one]
      calc (Real.log X / Real.log 2 + 1) * Real.log q
          ≤ (3 * u ^ (10:ℝ)) * (20 * B * u) := by
            apply mul_le_mul h1 h4 h9 (by positivity)
        _ = 60 * B * (u ^ (10:ℝ) * u) := by ring
        _ = 60 * B * u ^ (11:ℝ) := by rw [h10]
    -- 60B·u^{11} ≤ X·e^{−u/2} via the log route
    have hB60 : (0:ℝ) < 60 * B := by linarith
    have hu11pos : (0:ℝ) < u ^ (11:ℝ) := Real.rpow_pos_of_pos hu0 _
    have h11 : Real.log (60 * B * u ^ (11:ℝ)) ≤ Real.log X - (1:ℝ)/2 * u := by
      rw [Real.log_mul hB60.ne' hu11pos.ne', Real.log_rpow hu0]
      have hlogB : Real.log (60 * B) ≤ u :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) huM
      have h6 : Real.log u ≤ 2 * u ^ ((1:ℝ)/2) := by
        have := Real.log_le_rpow_div hu0.le (by norm_num : (0:ℝ) < 1/2)
        calc Real.log u ≤ u ^ ((1:ℝ)/2) / (1/2) := this
          _ = 2 * u ^ ((1:ℝ)/2) := by ring
      have h7 : u ^ ((1:ℝ)/2) ≤ u := by
        calc u ^ ((1:ℝ)/2) ≤ u ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = u := Real.rpow_one u
      have h6b : Real.log u ≤ 2 * u := by linarith
      have h9 : (512:ℝ) ≤ u ^ (9:ℝ) := by
        calc (512:ℝ) = 2 ^ (9:ℝ) := by
              rw [show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              norm_num
          _ ≤ u ^ (9:ℝ) := Real.rpow_le_rpow (by norm_num) hu2 (by norm_num)
      have h10' : u ^ (10:ℝ) = u ^ (9:ℝ) * u := by
        rw [show (10:ℝ) = 9 + 1 by norm_num, Real.rpow_add hu0, Real.rpow_one]
      have h512 : 512 * u ≤ u ^ (10:ℝ) := by
        rw [h10']
        nlinarith [hu0]
      have hLX : u ^ (10:ℝ) = Real.log X := hu10
      linarith
    have h12 : 60 * B * u ^ (11:ℝ) ≤ X * Real.exp (-((1:ℝ)/2 * u)) := by
      have h13 := (Real.log_le_iff_le_exp (mul_pos hB60 hu11pos)).mp h11
      calc 60 * B * u ^ (11:ℝ) ≤ Real.exp (Real.log X - (1:ℝ)/2 * u) := h13
        _ = X * Real.exp (-((1:ℝ)/2 * u)) := by
            rw [show Real.log X - (1:ℝ)/2 * u = Real.log X + -((1:ℝ)/2 * u) by ring,
              Real.exp_add, Real.exp_log hX0]
    exact le_trans h8 h12
  -- χ₀ deviation, complex side
  have hψ₀dev : ‖((((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) : ℝ)) : ℂ) - ((X:ℝ) : ℂ)‖
      ≤ C₃ * X * Real.exp (-(c₃ * u)) + X * Real.exp (-((1:ℝ)/2 * u)) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc |(∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) - X|
        ≤ C₃ * X * Real.exp (-c₃ * Real.log X ^ ((1:ℝ)/10))
          + (Real.log X / Real.log 2 + 1) * Real.log q := hχ₀X
      _ ≤ C₃ * X * Real.exp (-(c₃ * u)) + X * Real.exp (-((1:ℝ)/2 * u)) := by
          apply add_le_add _ hpolylog
          rw [← hudef, neg_mul]
  -- exponent comparisons to the common rate c
  have hec₃ : Real.exp (-(c₃ * u)) ≤ Real.exp (-(c * u)) := by
    apply Real.exp_le_exp.mpr
    have hcc : c ≤ c₃ := le_trans (min_le_left _ _) (min_le_left _ _)
    have := mul_le_mul_of_nonneg_right hcc hu0.le
    linarith
  have hec₅ : Real.exp (-((c₅/2) * u)) ≤ Real.exp (-(c * u)) := by
    apply Real.exp_le_exp.mpr
    have hcc : c ≤ c₅/2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have := mul_le_mul_of_nonneg_right hcc hu0.le
    linarith
  have heh : Real.exp (-((1:ℝ)/2 * u)) ≤ Real.exp (-(c * u)) := by
    apply Real.exp_le_exp.mpr
    have hcc : c ≤ 1/2 := min_le_right _ _
    have := mul_le_mul_of_nonneg_right hcc hu0.le
    linarith
  -- deviation identity from orthogonality
  have hdev : ((q.totient : ℕ) : ℂ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0) - ((X:ℝ) : ℂ)
      = (((((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) : ℝ)) : ℂ) - ((X:ℝ) : ℂ))
        + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
              χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ)) := by
    linear_combination hAP
  -- complex-side master bound
  have hnorm : ‖((q.totient : ℕ) : ℂ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0) - ((X:ℝ) : ℂ)‖
      ≤ (C₃ + C₅ + 1) * (X * Real.exp (-(c * u))) := by
    rw [hdev]
    have hstep : ‖(((((∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if IsUnit ((n : ℕ) : ZMod q) then vonMangoldt n else 0) : ℝ)) : ℂ) - ((X:ℝ) : ℂ))
        + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            χ a⁻¹ * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
              χ ((n : ZMod q)) * ((vonMangoldt n : ℝ) : ℂ))‖
        ≤ (C₃ * X * Real.exp (-(c₃ * u)) + X * Real.exp (-((1:ℝ)/2 * u)))
          + C₅ * X * Real.exp (-((c₅/2) * u)) :=
      le_trans (norm_add_le _ _) (add_le_add hψ₀dev (le_trans hsum_erase hcount))
    have b₁ : C₃ * X * Real.exp (-(c₃ * u)) ≤ C₃ * X * Real.exp (-(c * u)) :=
      mul_le_mul_of_nonneg_left hec₃ (mul_nonneg hC₃0.le hX0.le)
    have b₂ : X * Real.exp (-((1:ℝ)/2 * u)) ≤ X * Real.exp (-(c * u)) :=
      mul_le_mul_of_nonneg_left heh hX0.le
    have b₃ : C₅ * X * Real.exp (-((c₅/2) * u)) ≤ C₅ * X * Real.exp (-(c * u)) :=
      mul_le_mul_of_nonneg_left hec₅ (mul_nonneg hC₅0.le hX0.le)
    have hfold : C₃ * X * Real.exp (-(c * u)) + X * Real.exp (-(c * u))
        + C₅ * X * Real.exp (-(c * u)) = (C₃ + C₅ + 1) * (X * Real.exp (-(c * u))) := by
      ring
    linarith
  -- real bridge
  have hreal : |(q.totient : ℝ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if a = ((n : ZMod q)) then vonMangoldt n else 0) - X|
      ≤ (C₃ + C₅ + 1) * (X * Real.exp (-(c * u))) := by
    have hcast : ((q.totient : ℕ) : ℂ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if a = ((n : ZMod q)) then ((vonMangoldt n : ℝ) : ℂ) else 0) - ((X:ℝ) : ℂ)
        = ((((q.totient : ℝ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
            if a = ((n : ZMod q)) then vonMangoldt n else 0) - X) : ℝ) : ℂ) := by
      rw [hSreal]
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm
  -- divide by φ(q)
  have hφ0 : (0:ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hφ1
  have hφ1' : (1:ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast hφ1
  have hfinal : |(∑ n ∈ Finset.range (⌊X⌋₊ + 1),
        if a = ((n : ZMod q)) then vonMangoldt n else 0) - X / q.totient|
      ≤ (C₃ + C₅ + 1) * (X * Real.exp (-(c * u))) := by
    have hdiv : (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          if a = ((n : ZMod q)) then vonMangoldt n else 0) - X / q.totient
        = ((q.totient : ℝ) * (∑ n ∈ Finset.range (⌊X⌋₊ + 1),
            if a = ((n : ZMod q)) then vonMangoldt n else 0) - X) / q.totient := by
      field_simp
    rw [hdiv, abs_div, abs_of_pos hφ0]
    exact le_trans (div_le_self (abs_nonneg _) hφ1') hreal
  have hassoc : (C₃ + C₅ + 1) * (X * Real.exp (-(c * u)))
      = (C₃ + C₅ + 1) * X * Real.exp (-(c * u)) := by ring
  rw [neg_mul]
  linarith [hfinal, hassoc]

