module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 4000000


set_option maxHeartbeats 1000000
open DirichletCharacter Complex

/-- `LFunctionTrivChar N σ ≠ 0` for real `σ > 1` (it equals `LSeries ↗1 σ`, nonzero on `Re>1`). -/
lemma LFunctionTrivChar_ne_zero_of_one_lt {N : ℕ} [NeZero N] {σ : ℝ} (hσ : 1 < σ) :
    LFunctionTrivChar N (σ : ℂ) ≠ 0 := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [show LFunctionTrivChar N (σ : ℂ) = (1 : DirichletCharacter ℂ N).LFunction (σ : ℂ) from rfl,
    DirichletCharacter.LFunction_eq_LSeries _ hs]
  exact LSeries_ne_zero_of_one_lt_re _ hs

/-- `g = -logDeriv (LFunctionTrivChar₁ N)` is bounded on the real interval `[1,2]` (continuous
    on a compact set). -/
lemma g_bounded (N : ℕ) [NeZero N] : ∃ K : ℝ, ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 →
    ‖-deriv (LFunctionTrivChar₁ N) (σ : ℂ) / LFunctionTrivChar₁ N (σ : ℂ)‖ ≤ K := by
  have hcont := continuousOn_neg_logDeriv_LFunctionTrivChar₁ N
  set S : Set ℂ := (fun σ : ℝ => (σ : ℂ)) '' Set.Icc 1 2 with hS
  have hcompact : IsCompact S := (isCompact_Icc).image (by fun_prop)
  have hsub : S ⊆ {s | s = 1 ∨ LFunctionTrivChar N s ≠ 0} := by
    rintro s ⟨σ, hσ, rfl⟩
    rcases eq_or_lt_of_le hσ.1 with h1 | h1
    · left; rw [← h1]; norm_num
    · exact Or.inr (LFunctionTrivChar_ne_zero_of_one_lt h1)
  obtain ⟨K, hK⟩ := hcompact.exists_bound_of_continuousOn (hcont.mono hsub)
  exact ⟨K, fun σ h1 h2 => hK _ ⟨σ, ⟨h1, h2⟩, rfl⟩⟩

open scoped LSeries.notation ArithmeticFunction in
/-- The identity: for σ>1, `L(χ⁰Λ,σ) = 1/(σ-1) + g(σ)` with `g = -logDeriv(LFunctionTrivChar₁)`. -/
lemma twist_eq_pole_plus_g {N : ℕ} [NeZero N] {σ : ℝ} (hσ : 1 < σ) :
    LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)
      = 1 / ((σ : ℂ) - 1)
        + (-deriv (LFunctionTrivChar₁ N) (σ : ℂ) / LFunctionTrivChar₁ N (σ : ℂ)) := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hσ
  have hs1' : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero_of_ne hs1
  have hLne : LFunctionTrivChar N (σ : ℂ) ≠ 0 := LFunctionTrivChar_ne_zero_of_one_lt hσ
  have htwist : LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)
      = -deriv (LFunctionTrivChar N) (σ : ℂ) / LFunctionTrivChar N (σ : ℂ) := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hs,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs,
      ← DirichletCharacter.LFunction_eq_LSeries _ hs]
  rw [htwist]
  have hup : LFunctionTrivChar₁ N (σ : ℂ) = ((σ : ℂ) - 1) * LFunctionTrivChar N (σ : ℂ) := by
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1]
  have hd : deriv (LFunctionTrivChar₁ N) (σ : ℂ)
      = ((σ : ℂ) - 1) * deriv (LFunctionTrivChar N) (σ : ℂ) + LFunctionTrivChar N (σ : ℂ) :=
    deriv_LFunctionTrivChar₁_apply_of_ne_one N hs1
  rw [hup, hd]; field_simp; ring

open scoped LSeries.notation ArithmeticFunction in
/-- **THE POLE BOUND** (raw input for 1d): `Re L(χ⁰Λ,σ) ≤ 1/(σ-1) + K` for σ ∈ (1,2]. -/
lemma pole_bound (N : ℕ) [NeZero N] : ∃ K : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re ≤ 1 / (σ - 1) + K := by
  obtain ⟨K, hK⟩ := g_bounded N
  refine ⟨K, fun σ hσ1 hσ2 => ?_⟩
  rw [twist_eq_pole_plus_g hσ1, Complex.add_re]
  have h1 : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
      ← Complex.ofReal_div]
    exact Complex.ofReal_re _
  rw [h1]
  have h2 : (-deriv (LFunctionTrivChar₁ N) (σ : ℂ) / LFunctionTrivChar₁ N (σ : ℂ)).re ≤ K :=
    le_trans (Complex.re_le_norm _) (hK σ (le_of_lt hσ1) hσ2)
  linarith

open scoped LSeries.notation ArithmeticFunction in
/-- **THE GROWTH BOUND** (raw input #3, nontrivial χ²): for `ψ = χ² ≠ 1` and fixed γ,
    `Re L(ψΛ, σ+2iγ) ≤ K` on σ ∈ (1,2] — `L(ψ)` entire + nonzero on Re≥1, neg-log-deriv
    bounded on the compact segment. -/
lemma growth_bound_nontriv {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (γ : ℝ) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (LSeries (↗ψ * ↗Λ) ((σ : ℂ) + 2 * γ * I)).re ≤ K := by
  have hcont := continuousOn_neg_logDeriv_LFunction_of_nontriv hψ
  set S : Set ℂ := (fun σ : ℝ => (σ : ℂ) + 2 * γ * I) '' Set.Icc 1 2 with hS
  have hcompact : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hre : ∀ σ : ℝ, ((σ : ℂ) + 2 * γ * I).re = σ := by
    intro σ; simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
  have hsub : S ⊆ {s | LFunction ψ s ≠ 0} := by
    rintro s ⟨σ, hσ, rfl⟩
    simp only [Set.mem_setOf_eq]
    rcases eq_or_lt_of_le hσ.1 with h1 | h1
    · apply DirichletCharacter.LFunction_ne_zero_of_re_eq_one <;>
        first
        | (rw [hre]; linarith)
        | exact Or.inl hψ
    · have hs : 1 < ((σ : ℂ) + 2 * γ * I).re := by rw [hre]; exact h1
      rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
      exact LSeries_ne_zero_of_one_lt_re _ hs
  obtain ⟨K, hK⟩ := hcompact.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨K, fun σ hσ1 hσ2 => ?_⟩
  have hs : 1 < ((σ : ℂ) + 2 * γ * I).re := by rw [hre]; exact hσ1
  have hid : LSeries (↗ψ * ↗Λ) ((σ : ℂ) + 2 * γ * I)
      = -deriv (LFunction ψ) ((σ : ℂ) + 2 * γ * I) / LFunction ψ ((σ : ℂ) + 2 * γ * I) := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hs,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs,
      ← DirichletCharacter.LFunction_eq_LSeries _ hs]
  rw [hid]
  exact le_trans (Complex.re_le_norm _) (hK _ ⟨σ, ⟨le_of_lt hσ1, hσ2⟩, rfl⟩)

open scoped LSeries.notation ArithmeticFunction in
/-- **THE ZERO BOUND (fixed χ, γ)** — the last raw input of the zero-free-region chain:
    a zero `ρ = β + iγ` of `L(·,χ)` pulls the twisted log-derivative down by `1/(σ−β)`.
    Pure compactness — the pole-removed `−L'/L + 1/(s−ρ)` is continuous on the segment
    `[1,2] + iγ` (no zeros there), hence bounded; no Hadamard product needed at fixed γ. -/
lemma zero_bound_fixed {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (γ β : ℝ) (hβ1 : β < 1) (hzero : LFunction χ ((β : ℂ) + γ * I) = 0) :
    ∃ K : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * I)).re ≤ K - 1 / (σ - β) := by
  set ρ : ℂ := (β : ℂ) + γ * I with hρ
  set F : ℂ → ℂ := fun s => -deriv (LFunction χ) s / LFunction χ s + 1 / (s - ρ) with hF
  set Sg : Set ℂ := (fun σ : ℝ => (σ : ℂ) + γ * I) '' Set.Icc 1 2 with hSg
  have hre : ∀ σ : ℝ, ((σ : ℂ) + γ * I).re = σ := by
    intro σ
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
  have hLne : ∀ s ∈ Sg, LFunction χ s ≠ 0 := by
    rintro s ⟨σ, hσ, rfl⟩
    rcases eq_or_lt_of_le hσ.1 with h1 | h1
    · apply DirichletCharacter.LFunction_ne_zero_of_re_eq_one <;>
        first
        | (rw [hre]; linarith)
        | exact Or.inl hχ
    · have hs : 1 < ((σ : ℂ) + γ * I).re := by rw [hre]; exact h1
      rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
      exact LSeries_ne_zero_of_one_lt_re _ hs
  have hsne : ∀ s ∈ Sg, s - ρ ≠ 0 := by
    rintro s ⟨σ, hσ, rfl⟩
    intro hc
    rw [sub_eq_zero] at hc
    have hσβ : σ = β := by
      have := congrArg Complex.re hc
      rw [hre] at this
      rw [hρ] at this
      simpa [Complex.add_re, Complex.mul_re, Complex.mul_im] using this
    linarith [hσ.1]
  have hcont : ContinuousOn F Sg := by
    rw [hF]
    apply ContinuousOn.add
    · exact (continuousOn_neg_logDeriv_LFunction_of_nontriv hχ).mono
        (fun s hs => hLne s hs)
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      exact hsne
  have hcompact : IsCompact Sg := isCompact_Icc.image (by fun_prop)
  obtain ⟨K, hK⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨K, fun σ hσ1 hσ2 => ?_⟩
  have hs : 1 < ((σ : ℂ) + γ * I).re := by rw [hre]; exact hσ1
  have hmem : ((σ : ℂ) + γ * I) ∈ Sg := ⟨σ, ⟨le_of_lt hσ1, hσ2⟩, rfl⟩
  have hid : LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * I)
      = F ((σ : ℂ) + γ * I) - 1 / (((σ : ℂ) + γ * I) - ρ) := by
    rw [hF]
    dsimp only
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hs,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs,
      ← DirichletCharacter.LFunction_eq_LSeries _ hs]
    ring
  rw [hid]
  have hreal : (((σ : ℂ) + γ * I) - ρ) = ((σ - β : ℝ) : ℂ) := by
    rw [hρ]
    push_cast
    ring
  have hre1 : (1 / (((σ : ℂ) + γ * I) - ρ)).re = 1 / (σ - β) := by
    rw [hreal, show (1 : ℂ) / ((σ - β : ℝ) : ℂ) = (((1 / (σ - β) : ℝ)) : ℂ) by
      push_cast; ring]
    exact Complex.ofReal_re _
  rw [Complex.sub_re, hre1]
  have hFK : (F ((σ : ℂ) + γ * I)).re ≤ K :=
    le_trans (Complex.re_le_norm _) (hK _ hmem)
  linarith

open ArithmeticFunction Complex in
open scoped LSeries.notation ArithmeticFunction in
/-- **THE UNIFORM POLE BOUND — first brick of the Siegel–Walfisz uniformity layer**:
    a SINGLE constant works for every modulus, because the trivial-character twisted
    series has nonneg coefficients dominated termwise by the full `−ζ'/ζ` (`N = 1`).
    No Hadamard needed for `A₀`'s uniformity. -/
theorem pole_bound_uniform : ∃ K : ℝ, ∀ (N : ℕ) [NeZero N], ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re ≤ 1 / (σ - 1) + K := by
  obtain ⟨K, hK⟩ := pole_bound 1
  refine ⟨K, fun N _ σ hσ1 hσ2 => ?_⟩
  have hσre : 1 < ((σ : ℂ)).re := by simpa using hσ1
  have hsumΛ : LSeriesSummable (↗Λ) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσre
  have hsumN : LSeriesSummable (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) :=
    DirichletCharacter.LSeriesSummable_mul _ hsumΛ
  have hsum1 : LSeriesSummable (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ) :=
    DirichletCharacter.LSeriesSummable_mul _ hsumΛ
  -- per-term real parts
  have hterm : ∀ (M : ℕ) [NeZero M], ∀ n : ℕ,
      (LSeries.term (↗(1 : DirichletCharacter ℂ M) * ↗Λ) (σ : ℂ) n).re
      = if n = 0 then 0
        else (if IsUnit ((n : ZMod M)) then Λ n / (n : ℝ) ^ σ else 0) := by
    intro M _ n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [if_pos rfl]
      simp [LSeries.term]
    have hne : n ≠ 0 := hn0.ne'
    rw [LSeries.term_of_ne_zero hne, if_neg hne]
    have hpow : ((n : ℂ)) ^ ((σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; rfl,
        Complex.ofReal_cpow (Nat.cast_nonneg n)]
    have happ : (↗(1 : DirichletCharacter ℂ M) * ↗Λ) n
        = (if IsUnit ((n : ZMod M)) then ((Λ n : ℝ) : ℂ) else 0) := by
      show (1 : DirichletCharacter ℂ M) (n : ZMod M) * ((Λ n : ℝ) : ℂ) = _
      by_cases h : IsUnit ((n : ZMod M))
      · simp [MulChar.one_apply, h]
      · simp [MulChar.map_nonunit _ h, h]
    rw [happ]
    by_cases h : IsUnit ((n : ZMod M))
    · rw [if_pos h, if_pos h, hpow]
      rw [show (((Λ n : ℝ)) : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)
          = (((Λ n / (n : ℝ) ^ σ : ℝ)) : ℂ) by push_cast; ring]
      exact Complex.ofReal_re _
    · rw [if_neg h, if_neg h, zero_div]
      simp
  -- compare the real tsums
  have hreN : (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re
      = ∑' n, (LSeries.term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re :=
    ((Complex.hasSum_re hsumN.hasSum).tsum_eq).symm
  have hre1 : (LSeries (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ)).re
      = ∑' n, (LSeries.term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ) n).re :=
    ((Complex.hasSum_re hsum1.hasSum).tsum_eq).symm
  have hcomp : (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re
      ≤ (LSeries (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ)).re := by
    rw [hreN, hre1]
    have hsumNre : Summable (fun n => (LSeries.term (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ) n).re) :=
      (Complex.hasSum_re hsumN.hasSum).summable
    have hsum1re : Summable (fun n => (LSeries.term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ) n).re) :=
      (Complex.hasSum_re hsum1.hasSum).summable
    apply Summable.tsum_mono hsumNre hsum1re
    intro n
    dsimp only
    rw [hterm N n, hterm 1 n]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    rw [if_neg hn0.ne', if_neg hn0.ne']
    have hden : (0:ℝ) < (n : ℝ) ^ σ := by
      apply Real.rpow_pos_of_pos
      exact_mod_cast hn0
    have hΛnn : 0 ≤ Λ n / (n : ℝ) ^ σ :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg hden.le
    have hu1 : IsUnit ((n : ZMod 1)) := isUnit_of_subsingleton _
    rw [if_pos hu1]
    by_cases h : IsUnit ((n : ZMod N))
    · rw [if_pos h]
    · rw [if_neg h]
      exact hΛnn
  calc (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re
      ≤ (LSeries (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ)).re := hcomp
    _ ≤ 1 / (σ - 1) + K := hK σ hσ1 hσ2

open ArithmeticFunction Complex in
open scoped LSeries.notation ArithmeticFunction in
/-- **The uniform trivial twist bound**: for EVERY modulus, character, and height,
    `Re L(χΛ, σ+it) ≤ 1/(σ−1) + K` with ONE constant — termwise `Re ≤ ‖·‖ ≤ Λ(n)/n^σ`.
    The crude-but-uniform input the classical σ = 1 + c/log(q(t+2)) argument quotes
    wherever the Hadamard log-bound is not needed. -/
theorem twist_re_le_uniform : ∃ K : ℝ, ∀ (N : ℕ) [NeZero N],
    ∀ (χ : DirichletCharacter ℂ N), ∀ t σ : ℝ, 1 < σ → σ ≤ 2 →
    (LSeries (↗χ * ↗Λ) ((σ : ℂ) + t * I)).re ≤ 1 / (σ - 1) + K := by
  obtain ⟨K, hK⟩ := pole_bound 1
  refine ⟨K, fun N _ χ t σ hσ1 hσ2 => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : s.re = σ := by
    rw [hs]
    simp
  have hσre : 1 < s.re := by rw [hsre]; exact hσ1
  have hsumΛ : LSeriesSummable (↗Λ) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσre
  have hsumχ : LSeriesSummable (↗χ * ↗Λ) s :=
    DirichletCharacter.LSeriesSummable_mul _ hsumΛ
  have hσre1 : 1 < ((σ : ℂ)).re := by simpa using hσ1
  have hsumΛσ : LSeriesSummable (↗Λ) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hσre1
  have hsum1 : LSeriesSummable (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ) :=
    DirichletCharacter.LSeriesSummable_mul _ hsumΛσ
  -- termwise: Re ≤ ‖·‖ ≤ the N=1 real term
  have hpt : ∀ n : ℕ, (LSeries.term (↗χ * ↗Λ) s n).re
      ≤ (LSeries.term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ) n).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [LSeries.term_zero, LSeries.term_zero]
    have hne : n ≠ 0 := hn0.ne'
    rw [LSeries.term_of_ne_zero hne, LSeries.term_of_ne_zero hne]
    have hnormpow : ‖((n : ℂ)) ^ s‖ = (n : ℝ) ^ σ := by
      rw [Complex.norm_natCast_cpow_of_pos hn0, hsre]
    have hpow1 : ((n : ℂ)) ^ ((σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; rfl,
        Complex.ofReal_cpow (Nat.cast_nonneg n)]
    have h1app : (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) n = ((Λ n : ℝ) : ℂ) := by
      show (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * ((Λ n : ℝ) : ℂ) = _
      have h1 : ((n : ZMod 1)) = 1 := Subsingleton.elim _ _
      rw [h1, MulChar.map_one, one_mul]
    calc (((↗χ * ↗Λ) n) / ((n : ℂ)) ^ s).re
        ≤ ‖(((↗χ * ↗Λ) n) / ((n : ℂ)) ^ s)‖ := Complex.re_le_norm _
      _ = ‖(↗χ * ↗Λ) n‖ / (n : ℝ) ^ σ := by rw [norm_div, hnormpow]
      _ ≤ Λ n / (n : ℝ) ^ σ := by
          apply div_le_div_of_nonneg_right _
            (Real.rpow_pos_of_pos (show (0:ℝ) < (n:ℝ) by exact_mod_cast hn0) σ).le
          show ‖χ (n : ZMod N) * ((Λ n : ℝ) : ℂ)‖ ≤ Λ n
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          calc ‖χ ((n : ZMod N))‖ * Λ n ≤ 1 * Λ n := by
                apply mul_le_mul_of_nonneg_right (χ.norm_le_one _)
                  ArithmeticFunction.vonMangoldt_nonneg
            _ = Λ n := one_mul _
      _ = ((↗(1 : DirichletCharacter ℂ 1) * ↗Λ) n / ((n : ℂ)) ^ ((σ : ℂ))).re := by
          rw [h1app, hpow1]
          rw [show (((Λ n : ℝ)) : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)
              = (((Λ n / (n : ℝ) ^ σ : ℝ)) : ℂ) by push_cast; ring]
          rw [Complex.ofReal_re]
  -- sum up
  have hre1 : (LSeries (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ)).re
      = ∑' n, (LSeries.term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ) n).re :=
    ((Complex.hasSum_re hsum1.hasSum).tsum_eq).symm
  have hreχ : (LSeries (↗χ * ↗Λ) s).re
      = ∑' n, (LSeries.term (↗χ * ↗Λ) s n).re :=
    ((Complex.hasSum_re hsumχ.hasSum).tsum_eq).symm
  calc (LSeries (↗χ * ↗Λ) ((σ : ℂ) + t * I)).re
      = ∑' n, (LSeries.term (↗χ * ↗Λ) s n).re := hreχ
    _ ≤ ∑' n, (LSeries.term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ) n).re := by
        apply Summable.tsum_mono
        · exact (Complex.hasSum_re hsumχ.hasSum).summable
        · exact (Complex.hasSum_re hsum1.hasSum).summable
        · intro n
          exact hpt n
    _ = (LSeries (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) (σ : ℂ)).re := hre1.symm
    _ ≤ 1 / (σ - 1) + K := hK σ hσ1 hσ2

open Finset in
/-- Sum of a Dirichlet character over one period, as a range sum. -/
lemma char_range_period (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∑ j ∈ Finset.range N, χ ((j : ZMod N)) = 0 := by
  have hbij : ∑ j ∈ Finset.range N, χ ((j : ZMod N)) = ∑ a : ZMod N, χ a := by
    apply Finset.sum_nbij' (i := fun j : ℕ => ((j : ZMod N))) (j := fun a : ZMod N => a.val)
    · intro j _
      exact Finset.mem_univ _
    · intro a _
      rw [Finset.mem_range]
      exact ZMod.val_lt a
    · intro j hj
      rw [Finset.mem_range] at hj
      exact ZMod.val_natCast_of_lt hj
    · intro a _
      exact ZMod.natCast_rightInverse a
    · intro j _
      rfl
  rw [hbij]
  exact MulChar.sum_eq_zero_of_ne_one hχ

open Finset in
/-- **Character partial sums are bounded by the modulus** — the seed of the uniform
    polynomial growth bound `|L(s,χ)| ≪ q(1+|s|)` that the Hadamard layer consumes. -/
lemma char_partial_sum_bound (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (x : ℕ) : ‖∑ n ∈ Finset.range x, χ ((n : ZMod N))‖ ≤ N := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- full periods vanish
  have hfull : ∀ k : ℕ, ∑ n ∈ Finset.range (N * k), χ ((n : ZMod N)) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
      have hshift : ∀ j : ℕ, χ (((N * k + j : ℕ) : ZMod N)) = χ ((j : ZMod N)) := by
        intro j
        congr 1
        push_cast
        simp [ZMod.natCast_self]
      rw [Finset.sum_congr rfl (fun j _ => hshift j)]
      exact char_range_period N χ hχ
  -- split off the incomplete period
  have hsplit : ∑ n ∈ Finset.range x, χ ((n : ZMod N))
      = ∑ n ∈ Finset.range (N * (x / N) + x % N), χ ((n : ZMod N)) := by
    rw [Nat.div_add_mod]
  rw [hsplit, Finset.sum_range_add, hfull, zero_add]
  have hshift : ∀ j : ℕ, χ (((N * (x / N) + j : ℕ) : ZMod N)) = χ ((j : ZMod N)) := by
    intro j
    congr 1
    push_cast
    simp [ZMod.natCast_self]
  rw [Finset.sum_congr rfl (fun j _ => hshift j)]
  calc ‖∑ j ∈ Finset.range (x % N), χ ((j : ZMod N))‖
      ≤ ∑ j ∈ Finset.range (x % N), ‖χ ((j : ZMod N))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (x % N), 1 :=
        Finset.sum_le_sum (fun j _ => χ.norm_le_one _)
    _ = ((x % N : ℕ) : ℝ) := by simp
    _ ≤ N := by
        have h := (Nat.mod_lt x hN0).le
        exact_mod_cast h

open intervalIntegral in
/-- **The Abel kernel inequality**: `‖n^{−s} − (n+1)^{−s}‖ ≤ (‖s‖/σ)(n^{−σ} − (n+1)^{−σ})`
    for `σ = Re s > 0` — the summand bound that turns bounded character sums into the
    uniform polynomial growth of `L(s,χ)` by partial summation. -/
lemma cpow_diff_kernel_bound (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hσ : 0 < s.re) :
    ‖((n : ℂ)) ^ (-s) - (((n + 1 : ℕ) : ℂ)) ^ (-s)‖
      ≤ (‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hab : (n:ℝ) ≤ ((n+1 : ℕ):ℝ) := by exact_mod_cast Nat.le_succ n
  have h0notin : (0:ℝ) ∉ Set.uIcc ((n:ℝ)) (((n+1 : ℕ)):ℝ) := by
    rw [Set.uIcc_of_le hab]
    intro h0
    rw [Set.mem_Icc] at h0
    linarith [h0.1]
  -- FTC via integral_cpow at r = −s−1
  have hr : (-s - 1 : ℂ) ≠ -1 := by
    intro h
    apply hs0
    have : -s = 0 := by linear_combination h
    linear_combination -this
  have hint := integral_cpow (a := (n:ℝ)) (b := ((n+1 : ℕ):ℝ)) (r := -s - 1)
    (Or.inr ⟨hr, h0notin⟩)
  have hexp : (-s - 1 : ℂ) + 1 = -s := by ring
  rw [hexp] at hint
  have hFTC : ((n : ℂ)) ^ (-s) - (((n + 1 : ℕ) : ℂ)) ^ (-s)
      = s * ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ((x:ℂ)) ^ (-s - 1) := by
    rw [hint]
    have hcast1 : (((n:ℝ)) : ℂ) = ((n : ℕ) : ℂ) := by push_cast; rfl
    have hcast2 : ((((n+1 : ℕ)):ℝ) : ℂ) = (((n+1) : ℕ) : ℂ) := by push_cast; rfl
    rw [hcast1, hcast2]
    field_simp
    ring
  rw [hFTC, norm_mul]
  -- bound the integral
  have hnorm_int : ‖∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ((x:ℂ)) ^ (-s - 1)‖
      ≤ ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), x ^ (-s.re - 1) := by
    have h1 : ‖∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ((x:ℂ)) ^ (-s - 1)‖
        ≤ ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ‖((x:ℂ)) ^ (-s - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have h2 : ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ‖((x:ℂ)) ^ (-s - 1)‖
        = ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), x ^ (-s.re - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      dsimp only
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      norm_num
    linarith [h1, h2.le, h2.ge]
  have hreal : ∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), x ^ (-s.re - 1)
      = ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) / s.re := by
    have hrne : (-s.re - 1 : ℝ) ≠ -1 := by
      intro h
      have : s.re = 0 := by linarith
      linarith
    have h := integral_rpow (a := (n:ℝ)) (b := ((n+1 : ℕ):ℝ)) (r := -s.re - 1)
      (Or.inr ⟨hrne, h0notin⟩)
    rw [show (-s.re - 1 : ℝ) + 1 = -s.re by ring] at h
    rw [h]
    field_simp
    ring
  rw [hreal] at hnorm_int
  have hσne : s.re ≠ 0 := hσ.ne'
  have hmono : 0 ≤ ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) := by
    have h1 : ((n + 1 : ℕ) : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-s.re) := by
      apply Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)
    linarith
  calc ‖s‖ * ‖∫ x in ((n:ℝ))..(((n+1 : ℕ)):ℝ), ((x:ℂ)) ^ (-s - 1)‖
      ≤ ‖s‖ * (((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) / s.re) :=
        mul_le_mul_of_nonneg_left hnorm_int (norm_nonneg s)
    _ = (‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) := by
        field_simp

open Finset in
/-- **Uniform growth of twisted partial sums** (SW uniformity brick 6): for every
    nontrivial χ mod N and `Re s > 0`,
    `‖∑_{n<x} χ(n)n^{−s}‖ ≤ N(2 + ‖s‖/Re s)` — partial summation of the bounded
    character sums against the Abel kernel. The finite heart of the uniform polynomial
    growth of `L(s,χ)` off `Re s > 1`. -/
lemma char_twisted_partial_bound (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (x : ℕ) :
    ‖∑ n ∈ Finset.range x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s)‖
      ≤ (N : ℝ) * (2 + ‖s‖ / s.re) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hfac : (0:ℝ) ≤ 2 + ‖s‖ / s.re := by positivity
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · -- x = 0 or 1: only the vanishing n = 0 term
    interval_cases x
    · simp
      positivity
    · rw [Finset.sum_range_one]
      rw [show ((0 : ℕ) : ℂ) ^ (-s) = 0 by
        rw [Nat.cast_zero]; exact Complex.zero_cpow (neg_ne_zero.mpr hs0)]
      rw [mul_zero, norm_zero]
      positivity
  -- Abel summation
  have habel := Finset.sum_range_by_parts
    (f := fun n : ℕ => ((n : ℂ)) ^ (-s)) (g := fun n : ℕ => χ ((n : ZMod N))) (n := x)
  simp only [smul_eq_mul] at habel
  have hswap : ∑ n ∈ Finset.range x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s)
      = ∑ n ∈ Finset.range x, ((n : ℂ)) ^ (-s) * χ ((n : ZMod N)) := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hswap, habel]
  set A : ℕ → ℂ := fun t => ∑ j ∈ Finset.range t, χ ((j : ZMod N)) with hA
  have hAbound : ∀ t, ‖A t‖ ≤ N := fun t => char_partial_sum_bound N χ hχ t
  -- step bounds
  have hstep : ∀ i ∈ Finset.range (x - 1),
      ‖(((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖
      ≤ (if i = 0 then (1:ℝ)
         else (‖s‖ / s.re) * ((i : ℝ) ^ (-s.re) - ((i + 1 : ℕ) : ℝ) ^ (-s.re))) * N := by
    intro i _
    rw [norm_mul]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [if_pos rfl]
      apply mul_le_mul _ (hAbound 1) (norm_nonneg _) (by norm_num)
      rw [show ((0 : ℕ) : ℂ) ^ (-s) = 0 by
        rw [Nat.cast_zero]; exact Complex.zero_cpow (neg_ne_zero.mpr hs0)]
      rw [sub_zero]
      rw [show (((0 + 1 : ℕ)) : ℂ) = 1 by norm_num, Complex.one_cpow, norm_one]
    · rw [if_neg hi0.ne']
      apply mul_le_mul _ (hAbound (i + 1)) (norm_nonneg _) ?_
      · rw [← norm_neg]
        rw [show -(((i + 1 : ℕ) : ℂ) ^ (-s) - ((i : ℂ)) ^ (-s))
            = ((i : ℂ)) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s) by ring]
        exact cpow_diff_kernel_bound i hi0 s hσ
      · have := cpow_diff_kernel_bound i hi0 s hσ
        have h0 : (0:ℝ) ≤ ‖((i : ℂ)) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s)‖ := norm_nonneg _
        linarith
  -- telescoping the kernel sums
  have htele : ∑ i ∈ Finset.range (x - 1),
      (if i = 0 then (1:ℝ)
       else (‖s‖ / s.re) * ((i : ℝ) ^ (-s.re) - ((i + 1 : ℕ) : ℝ) ^ (-s.re)))
      ≤ 1 + ‖s‖ / s.re := by
    have hm : 1 ≤ x - 1 := by omega
    rw [show x - 1 = 1 + (x - 2) by omega, Finset.sum_range_add]
    rw [Finset.sum_range_one, if_pos rfl]
    have hrest : ∑ i ∈ Finset.range (x - 2),
        (if 1 + i = 0 then (1:ℝ)
         else (‖s‖ / s.re) * (((1 + i : ℕ) : ℝ) ^ (-s.re) - ((1 + i + 1 : ℕ) : ℝ) ^ (-s.re)))
        ≤ ‖s‖ / s.re := by
      have hcongr : ∀ i ∈ Finset.range (x - 2),
          (if 1 + i = 0 then (1:ℝ)
           else (‖s‖ / s.re) * (((1 + i : ℕ) : ℝ) ^ (-s.re) - ((1 + i + 1 : ℕ) : ℝ) ^ (-s.re)))
          = (‖s‖ / s.re) * (((i + 1 : ℕ) : ℝ) ^ (-s.re) - ((i + 2 : ℕ) : ℝ) ^ (-s.re)) := by
        intro i _
        rw [if_neg (by omega), show 1 + i = i + 1 from by omega]
      rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
      have htel : ∑ i ∈ Finset.range (x - 2),
          (((i + 1 : ℕ) : ℝ) ^ (-s.re) - ((i + 2 : ℕ) : ℝ) ^ (-s.re))
          = ((1 : ℕ) : ℝ) ^ (-s.re) - ((x - 1 : ℕ) : ℝ) ^ (-s.re) := by
        have h := Finset.sum_range_sub' (f := fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (-s.re))
          (n := x - 2)
        calc ∑ i ∈ Finset.range (x - 2),
            (((i + 1 : ℕ) : ℝ) ^ (-s.re) - ((i + 2 : ℕ) : ℝ) ^ (-s.re))
            = ∑ i ∈ Finset.range (x - 2),
              ((((i + 1 : ℕ)) : ℝ) ^ (-s.re) - (((i + 1 + 1 : ℕ)) : ℝ) ^ (-s.re)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [show (i + 2 : ℕ) = i + 1 + 1 from by omega]
          _ = (((0 + 1 : ℕ)) : ℝ) ^ (-s.re) - (((x - 2 + 1 : ℕ)) : ℝ) ^ (-s.re) := h
          _ = ((1 : ℕ) : ℝ) ^ (-s.re) - ((x - 1 : ℕ) : ℝ) ^ (-s.re) := by
              rw [show (0 + 1 : ℕ) = 1 from rfl, show x - 2 + 1 = x - 1 from by omega]
      rw [htel]
      have h1 : ((1 : ℕ) : ℝ) ^ (-s.re) = 1 := by
        norm_num
      have h2 : (0:ℝ) ≤ ((x - 1 : ℕ) : ℝ) ^ (-s.re) := by positivity
      rw [h1]
      have hq : (0:ℝ) ≤ ‖s‖ / s.re := by positivity
      nlinarith [mul_nonneg hq h2]
    exact add_le_add (le_refl (1:ℝ)) hrest
  -- assemble
  calc ‖((x - 1 : ℕ) : ℂ) ^ (-s) * A x
        - ∑ i ∈ Finset.range (x - 1),
            ((((i + 1 : ℕ) : ℂ)) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖
      ≤ ‖((x - 1 : ℕ) : ℂ) ^ (-s) * A x‖
        + ‖∑ i ∈ Finset.range (x - 1),
            ((((i + 1 : ℕ) : ℂ)) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖ := norm_sub_le _ _
    _ ≤ 1 * (N : ℝ)
        + ∑ i ∈ Finset.range (x - 1),
            (if i = 0 then (1:ℝ)
             else (‖s‖ / s.re) * ((i : ℝ) ^ (-s.re) - ((i + 1 : ℕ) : ℝ) ^ (-s.re))) * N := by
        apply add_le_add
        · rw [norm_mul]
          apply mul_le_mul _ (hAbound x) (norm_nonneg _) (by norm_num)
          rw [show ((x - 1 : ℕ) : ℂ) = (((x - 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl]
          rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.sub_pos_of_lt (by omega))]
          simp only [Complex.neg_re]
          apply Real.rpow_le_one_of_one_le_of_nonpos
          · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
          · linarith
        · exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum hstep)
    _ = 1 * (N : ℝ) + (∑ i ∈ Finset.range (x - 1),
            (if i = 0 then (1:ℝ)
             else (‖s‖ / s.re) * ((i : ℝ) ^ (-s.re) - ((i + 1 : ℕ) : ℝ) ^ (-s.re)))) * N := by
        rw [Finset.sum_mul]
    _ ≤ 1 * (N : ℝ) + (1 + ‖s‖ / s.re) * N := by
        have := mul_le_mul_of_nonneg_right htele hNnn
        linarith
    _ = (N : ℝ) * (2 + ‖s‖ / s.re) := by ring

open Finset in
open scoped LSeries.notation in
/-- **Uniform L-series bound** (SW uniformity brick 7): on `Re s > 1`,
    `‖L(s,χ)‖ ≤ N(2 + ‖s‖/Re s)` for every nontrivial χ — the partial-sum bound survives
    the limit. Transfers to `LFunction` on `Re s > 1` via `LFunction_eq_LSeries`. -/
lemma char_LSeries_bound (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    ‖LSeries (↗χ) s‖ ≤ (N : ℝ) * (2 + ‖s‖ / s.re) := by
  have hσ : 0 < s.re := lt_trans one_pos hs
  have hsum : LSeriesSummable (↗χ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    exact χ.norm_le_one _
  have hterm_eq : ∀ n : ℕ, LSeries.term (↗χ) s n = χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [LSeries.term_zero]
      rw [show ((0 : ℕ) : ℂ) ^ (-s) = 0 by
        rw [Nat.cast_zero]
        exact Complex.zero_cpow (neg_ne_zero.mpr (fun h => by simp [h] at hσ))]
      rw [mul_zero]
    · rw [LSeries.term_of_ne_zero hn0.ne']
      rw [Complex.cpow_neg]
      rw [div_eq_mul_inv]
  have htend : Filter.Tendsto (fun x : ℕ => ∑ n ∈ Finset.range x, LSeries.term (↗χ) s n)
      Filter.atTop (nhds (LSeries (↗χ) s)) := hsum.hasSum.tendsto_sum_nat
  have hnorm_tend : Filter.Tendsto
      (fun x : ℕ => ‖∑ n ∈ Finset.range x, LSeries.term (↗χ) s n‖)
      Filter.atTop (nhds ‖LSeries (↗χ) s‖) := htend.norm
  apply le_of_tendsto hnorm_tend
  apply Filter.Eventually.of_forall
  intro x
  have hcongr : ∑ n ∈ Finset.range x, LSeries.term (↗χ) s n
      = ∑ n ∈ Finset.range x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s) :=
    Finset.sum_congr rfl (fun n _ => hterm_eq n)
  rw [hcongr]
  exact char_twisted_partial_bound N χ hχ s hσ x

open Finset in
/-- **The decaying tail bound** (SW uniformity brick 8): for `1 ≤ x < y`,
    `‖∑_{x≤n<y} χ(n)n^{−s}‖ ≤ N·x^{−σ}·(2 + ‖s‖/σ)` — the partial sums are uniformly
    Cauchy on `Re s ≥ σ₀ > 0`; the continuation of `L(s,χ)` to the strip inherits the
    uniform bound. -/
lemma char_twisted_tail_bound (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) (x y : ℕ) (hx : 1 ≤ x) (hxy : x < y) :
    ‖∑ n ∈ Finset.Ico x y, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s)‖
      ≤ (N : ℝ) * ((x : ℝ) ^ (-s.re) * (2 + ‖s‖ / s.re)) := by
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hxR : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hxσ : (0:ℝ) < (x:ℝ) ^ (-s.re) := by positivity
  set A : ℕ → ℂ := fun t => ∑ j ∈ Finset.range t, χ ((j : ZMod N)) with hA
  have hAbound : ∀ t, ‖A t‖ ≤ N := fun t => char_partial_sum_bound N χ hχ t
  have hnormpow : ∀ k : ℕ, 1 ≤ k → ‖((k : ℂ)) ^ (-s)‖ = (k : ℝ) ^ (-s.re) := by
    intro k hk
    rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  have hanti : ∀ k : ℕ, x ≤ k → ((k : ℝ)) ^ (-s.re) ≤ ((x : ℝ)) ^ (-s.re) := by
    intro k hk
    apply Real.rpow_le_rpow_of_nonpos (by linarith) (by exact_mod_cast hk) (by linarith)
  -- Abel on the tail
  have habel := Finset.sum_Ico_by_parts
    (f := fun n : ℕ => ((n : ℂ)) ^ (-s)) (g := fun n : ℕ => χ ((n : ZMod N))) hxy
  simp only [smul_eq_mul] at habel
  have hswap : ∑ n ∈ Finset.Ico x y, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s)
      = ∑ n ∈ Finset.Ico x y, ((n : ℂ)) ^ (-s) * χ ((n : ZMod N)) :=
    Finset.sum_congr rfl (fun n _ => by ring)
  rw [hswap, habel]
  -- the three pieces
  have hp1 : ‖((y - 1 : ℕ) : ℂ) ^ (-s) * A y‖ ≤ (x : ℝ) ^ (-s.re) * N := by
    rw [norm_mul, hnormpow (y - 1) (by omega)]
    apply mul_le_mul (hanti (y - 1) (by omega)) (hAbound y) (norm_nonneg _) hxσ.le
  have hp2 : ‖((x : ℕ) : ℂ) ^ (-s) * A x‖ ≤ (x : ℝ) ^ (-s.re) * N := by
    rw [norm_mul, hnormpow x hx]
    apply mul_le_mul le_rfl (hAbound x) (norm_nonneg _) hxσ.le
  have hp3 : ‖∑ i ∈ Finset.Ico x (y - 1),
      ((((i + 1 : ℕ) : ℂ)) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖
      ≤ (‖s‖ / s.re) * (x : ℝ) ^ (-s.re) * N := by
    calc ‖∑ i ∈ Finset.Ico x (y - 1),
        ((((i + 1 : ℕ) : ℂ)) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖
        ≤ ∑ i ∈ Finset.Ico x (y - 1),
          ‖((((i + 1 : ℕ) : ℂ)) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.Ico x (y - 1),
          ((‖s‖ / s.re) * ((i : ℝ) ^ (-s.re) - ((i + 1 : ℕ) : ℝ) ^ (-s.re))) * N := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Ico] at hi
          rw [norm_mul]
          refine mul_le_mul ?_ (hAbound (i + 1)) (norm_nonneg _) ?_
          · rw [← norm_neg, show -(((((i + 1 : ℕ) : ℂ)) ^ (-s)) - ((i : ℂ)) ^ (-s))
                = ((i : ℂ)) ^ (-s) - (((i + 1 : ℕ) : ℂ)) ^ (-s) by ring]
            exact cpow_diff_kernel_bound i (by omega) s hσ
          · have h := cpow_diff_kernel_bound i (by omega) s hσ
            have h0 : (0:ℝ) ≤ ‖((i : ℂ)) ^ (-s) - (((i + 1 : ℕ) : ℂ)) ^ (-s)‖ :=
              norm_nonneg _
            linarith
      _ = (‖s‖ / s.re) * (∑ i ∈ Finset.Ico x (y - 1),
            ((i : ℝ) ^ (-s.re) - ((i + 1 : ℕ) : ℝ) ^ (-s.re))) * N := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ (‖s‖ / s.re) * (x : ℝ) ^ (-s.re) * N := by
          apply mul_le_mul_of_nonneg_right _ hNnn
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases Nat.lt_or_ge x (y - 1) with hlt | hge
          · have htel : ∑ i ∈ Finset.Ico x (y - 1),
                ((i : ℝ) ^ (-s.re) - ((i + 1 : ℕ) : ℝ) ^ (-s.re))
                = (x : ℝ) ^ (-s.re) - ((y - 1 : ℕ) : ℝ) ^ (-s.re) := by
              rw [Finset.sum_Ico_eq_sum_range]
              have hcongr : ∀ j ∈ Finset.range (y - 1 - x),
                  (((x + j : ℕ) : ℝ) ^ (-s.re) - (((x + j) + 1 : ℕ) : ℝ) ^ (-s.re))
                  = (fun t : ℕ => ((x + t : ℕ) : ℝ) ^ (-s.re)) j
                    - (fun t : ℕ => ((x + t : ℕ) : ℝ) ^ (-s.re)) (j + 1) := by
                intro j _
                rfl
              rw [Finset.sum_congr rfl hcongr, Finset.sum_range_sub']
              rw [show x + 0 = x from by omega, show x + (y - 1 - x) = y - 1 from by omega]
            rw [htel]
            have h2 : (0:ℝ) ≤ ((y - 1 : ℕ) : ℝ) ^ (-s.re) := by positivity
            linarith
          · have hempty : Finset.Ico x (y - 1) = ∅ := Finset.Ico_eq_empty (by omega)
            rw [hempty, Finset.sum_empty]
            positivity
  calc ‖((y - 1 : ℕ) : ℂ) ^ (-s) * A y - ((x : ℕ) : ℂ) ^ (-s) * A x
        - ∑ i ∈ Finset.Ico x (y - 1),
            ((((i + 1 : ℕ) : ℂ)) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖
      ≤ ‖((y - 1 : ℕ) : ℂ) ^ (-s) * A y - ((x : ℕ) : ℂ) ^ (-s) * A x‖
        + ‖∑ i ∈ Finset.Ico x (y - 1),
            ((((i + 1 : ℕ) : ℂ)) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖ := norm_sub_le _ _
    _ ≤ (‖((y - 1 : ℕ) : ℂ) ^ (-s) * A y‖ + ‖((x : ℕ) : ℂ) ^ (-s) * A x‖)
        + ‖∑ i ∈ Finset.Ico x (y - 1),
            ((((i + 1 : ℕ) : ℂ)) ^ (-s) - ((i : ℂ)) ^ (-s)) * A (i + 1)‖ := by
        have := norm_sub_le (((y - 1 : ℕ) : ℂ) ^ (-s) * A y) (((x : ℕ) : ℂ) ^ (-s) * A x)
        linarith
    _ ≤ ((x : ℝ) ^ (-s.re) * N + (x : ℝ) ^ (-s.re) * N)
        + (‖s‖ / s.re) * (x : ℝ) ^ (-s.re) * N := by
        linarith [hp1, hp2, hp3]
    _ = (N : ℝ) * ((x : ℝ) ^ (-s.re) * (2 + ‖s‖ / s.re)) := by ring

open Finset in
/-- The truncated twisted sums are ENTIRE — each term `s ↦ χ(n)·n^{−s}` is
    (for `n ≥ 1`) a constant times `const_cpow` of the entire `−s`. Input to the
    Weierstrass step of the strip continuation. -/
lemma twisted_partial_differentiable (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (x : ℕ) :
    Differentiable ℂ (fun s : ℂ =>
      ∑ n ∈ Finset.Ico 1 x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s)) := by
  apply Differentiable.fun_sum
  intro n hn
  rw [Finset.mem_Ico] at hn
  have hne : ((n : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn.1
  apply Differentiable.const_mul
  exact (differentiable_neg).const_cpow (Or.inl hne)

open Finset in
open scoped LSeries.notation in
/-- The truncations `P_x(s) = ∑_{1≤n<x} χ(n)n^{−s}` converge to `L(s,χ)` on `Re s > 1`
    — step 3 of the strip-identification plan. -/
lemma twisted_partial_tendsto (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (hs : 1 < s.re) :
    Filter.Tendsto (fun x : ℕ =>
        ∑ n ∈ Finset.Ico 1 x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s))
      Filter.atTop (nhds (LSeries (↗χ) s)) := by
  have hσ : 0 < s.re := lt_trans one_pos hs
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hsum : LSeriesSummable (↗χ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    exact χ.norm_le_one _
  have hterm_eq : ∀ n : ℕ, 1 ≤ n →
      LSeries.term (↗χ) s n = χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
  have hbridge : ∀ x : ℕ, ∑ n ∈ Finset.range x, LSeries.term (↗χ) s n
      = ∑ n ∈ Finset.Ico 1 x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s) := by
    intro x
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hx0]
    rw [show ∑ n ∈ Finset.Ico 0 1, LSeries.term (↗χ) s n = 0 by
      rw [Finset.sum_Ico_eq_sum_range]
      simp [LSeries.term_zero]]
    rw [zero_add]
    exact Finset.sum_congr rfl (fun n hn => hterm_eq n (Finset.mem_Ico.mp hn).1)
  have htend := hsum.hasSum.tendsto_sum_nat
  rw [show (fun x : ℕ => ∑ n ∈ Finset.range x, LSeries.term (↗χ) s n)
      = (fun x : ℕ => ∑ n ∈ Finset.Ico 1 x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s)) from
    funext hbridge] at htend
  exact htend

open Finset Filter in
/-- **Uniform Cauchy on strips** (SW uniformity brick 11): the truncations are uniformly
    Cauchy on every `{σ₀ ≤ Re s, ‖s‖ ≤ R}` — the Weierstrass input for the strip
    continuation of `L(s,χ)` with its uniform bound. -/
lemma twisted_partial_uniformCauchy (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (σ₀ R : ℝ) (hσ₀ : 0 < σ₀) (hR : 0 ≤ R) :
    UniformCauchySeqOn (fun x : ℕ => fun s : ℂ =>
        ∑ n ∈ Finset.Ico 1 x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s))
      Filter.atTop {s : ℂ | σ₀ ≤ s.re ∧ ‖s‖ ≤ R} := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  set C : ℝ := (N:ℝ) * (2 + R / σ₀) + 1 with hCdef
  have hC : (0:ℝ) < C := by positivity
  have htend : Filter.Tendsto (fun k : ℕ => C * (k : ℝ) ^ (-σ₀))
      Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun k : ℕ => ((k : ℝ)) ^ (-σ₀)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hσ₀).comp tendsto_natCast_atTop_atTop
    simpa using h2.const_mul C
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hε))
  refine ⟨max K₀ 1, fun m hm n hn s hsmem => ?_⟩
  obtain ⟨hs1, hs2⟩ := hsmem
  have hσ : 0 < s.re := lt_of_lt_of_le hσ₀ hs1
  -- one-sided estimate
  have hside : ∀ a b : ℕ, max K₀ 1 ≤ a → a < b →
      dist (∑ k ∈ Finset.Ico 1 a, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s))
        (∑ k ∈ Finset.Ico 1 b, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s)) < ε := by
    intro a b ha hab
    have ha1 : 1 ≤ a := le_trans (le_max_right _ _) ha
    have haK : K₀ ≤ a := le_trans (le_max_left _ _) ha
    have hsplit : ∑ k ∈ Finset.Ico 1 b, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s)
        = (∑ k ∈ Finset.Ico 1 a, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s))
          + ∑ k ∈ Finset.Ico a b, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s) :=
      (Finset.sum_Ico_consecutive _ ha1 hab.le).symm
    rw [dist_eq_norm, hsplit]
    rw [show (∑ k ∈ Finset.Ico 1 a, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s))
        - ((∑ k ∈ Finset.Ico 1 a, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s))
          + ∑ k ∈ Finset.Ico a b, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s))
        = -(∑ k ∈ Finset.Ico a b, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s)) by ring]
    rw [norm_neg]
    have htail := char_twisted_tail_bound N χ hχ s hσ a b ha1 hab
    have haR : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha1
    have hmono1 : ((a:ℝ)) ^ (-s.re) ≤ ((a:ℝ)) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le haR (by linarith)
    have hmono2 : ‖s‖ / s.re ≤ R / σ₀ := by
      gcongr
    have hbound2 : (N : ℝ) * ((a : ℝ) ^ (-s.re) * (2 + ‖s‖ / s.re))
        ≤ C * (a : ℝ) ^ (-σ₀) := by
      have h1 : (0:ℝ) ≤ (a:ℝ) ^ (-s.re) := by positivity
      have h2 : (0:ℝ) ≤ 2 + ‖s‖ / s.re := by positivity
      have h3 : (a : ℝ) ^ (-s.re) * (2 + ‖s‖ / s.re)
          ≤ (a : ℝ) ^ (-σ₀) * (2 + R / σ₀) := by
        apply mul_le_mul hmono1 (by linarith) h2 (by positivity)
      have h4 : (N:ℝ) * ((a : ℝ) ^ (-s.re) * (2 + ‖s‖ / s.re))
          ≤ (N:ℝ) * ((a : ℝ) ^ (-σ₀) * (2 + R / σ₀)) :=
        mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg N)
      have h5 : (N:ℝ) * ((a : ℝ) ^ (-σ₀) * (2 + R / σ₀))
          ≤ C * (a : ℝ) ^ (-σ₀) := by
        rw [hCdef]
        have h6 : (0:ℝ) ≤ (a:ℝ) ^ (-σ₀) := by positivity
        nlinarith
      linarith
    calc ‖∑ k ∈ Finset.Ico a b, χ ((k : ZMod N)) * ((k : ℂ)) ^ (-s)‖
        ≤ (N : ℝ) * ((a : ℝ) ^ (-s.re) * (2 + ‖s‖ / s.re)) := htail
      _ ≤ C * (a : ℝ) ^ (-σ₀) := hbound2
      _ < ε := hK₀ a haK
  rcases lt_trichotomy m n with h | h | h
  · exact hside m n hm h
  · subst h
    rw [dist_self]
    exact hε
  · rw [dist_comm]
    exact hside n m hn h

open Finset Filter in
open scoped LSeries.notation in
/-- **THE UNIFORM STRIP BOUND** (SW uniformity brick 12 — the free layer's capstone):
    `‖L(s,χ)‖ ≤ N(2 + ‖s‖/Re s)` for every nontrivial χ on ALL of `Re s > 0` — the
    truncations' locally uniform limit is analytic, agrees with `LFunction` past the
    1-line, and the identity theorem carries the uniform bound into the strip. -/
theorem LFunction_strip_bound (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hσ : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (N : ℝ) * (2 + ‖s‖ / s.re) := by
  classical
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := convex_halfSpace_re_gt 0
  set P : ℕ → ℂ → ℂ := fun x z =>
    ∑ n ∈ Finset.Ico 1 x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-z) with hP
  -- pointwise Cauchy → pointwise limit F on U
  have hcau : ∀ z ∈ U, CauchySeq (fun x => P x z) := by
    intro z hz
    have hz' : 0 < z.re := hz
    have huc := twisted_partial_uniformCauchy N χ hχ (z.re) (‖z‖) hz' (norm_nonneg z)
    have hmem : z ∈ {w : ℂ | z.re ≤ w.re ∧ ‖w‖ ≤ ‖z‖} := ⟨le_refl _, le_refl _⟩
    exact huc.cauchySeq hmem
  set F : ℂ → ℂ := fun z => limUnder Filter.atTop (fun x => P x z) with hF
  have hFtend : ∀ z ∈ U, Filter.Tendsto (fun x => P x z) Filter.atTop (nhds (F z)) := by
    intro z hz
    exact (hcau z hz).tendsto_limUnder
  -- locally uniform convergence on U
  have hlocal : TendstoLocallyUniformlyOn P F Filter.atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen]
    intro K hKU hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact tendstoUniformlyOn_empty
    · -- compact K has positive min re and bounded norm
      obtain ⟨z₀, hz₀K, hz₀min⟩ := hK.exists_isMinOn hKne
        (Complex.continuous_re.continuousOn)
      obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
      have hσ₀ : 0 < z₀.re := hKU hz₀K
      have hsub : K ⊆ {w : ℂ | z₀.re ≤ w.re ∧ ‖w‖ ≤ max R 0} := by
        intro w hw
        constructor
        · exact hz₀min hw
        · have := hR hw
          rw [Metric.mem_ball, dist_zero_right] at this
          exact le_trans this.le (le_max_left _ _)
      have huc := twisted_partial_uniformCauchy N χ hχ (z₀.re) (max R 0) hσ₀
        (le_max_right _ _)
      have hucK := huc.mono hsub
      exact hucK.tendstoUniformlyOn_of_tendsto (fun z hz => hFtend z (hKU hz))
  -- F analytic on U
  have hFdiff : DifferentiableOn ℂ F U :=
    hlocal.differentiableOn
      (Filter.Eventually.of_forall (fun x => (twisted_partial_differentiable N χ x).differentiableOn))
      hUopen
  -- F = LFunction on {re > 1}
  have hagree : ∀ z : ℂ, 1 < z.re → F z = DirichletCharacter.LFunction χ z := by
    intro z hz
    have h1 := hFtend z (by simp only [hU, Set.mem_setOf_eq]; linarith)
    have h2 := twisted_partial_tendsto N χ z hz
    have := tendsto_nhds_unique h1 h2
    rw [this, DirichletCharacter.LFunction_eq_LSeries _ hz]
  -- identity theorem
  have hLdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have heq : Set.EqOn F (DirichletCharacter.LFunction χ) U := by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hFdiff.analyticOnNhd hUopen) (hLdiff.analyticOnNhd hUopen)
      hUconv.isPreconnected (show (2 : ℂ) ∈ U by simp [hU])
    have hV : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := by
      apply IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
      simp
    exact Filter.eventuallyEq_of_mem hV (fun z hz => hagree z hz)
  -- transfer the bound
  have hsU : s ∈ U := hσ
  rw [← heq hsU]
  have htends := hFtend s hsU
  apply le_of_tendsto htends.norm
  apply Filter.Eventually.of_forall
  intro x
  -- P x s = range-sum minus the vanishing n=0 term
  have hzero : χ (((0 : ℕ) : ZMod N)) * (((0 : ℕ) : ℂ)) ^ (-s) = 0 := by
    rw [show (((0 : ℕ)) : ℂ) ^ (-s) = 0 by
      rw [Nat.cast_zero]
      exact Complex.zero_cpow (neg_ne_zero.mpr (fun h => by simp [h] at hσ))]
    rw [mul_zero]
  have hbridge : P x s = ∑ n ∈ Finset.range x, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s) := by
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp [hP]
    rw [hP]
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hx0]
    rw [show ∑ n ∈ Finset.Ico (0:ℕ) 1, χ ((n : ZMod N)) * ((n : ℂ)) ^ (-s) = 0 by
      rw [Finset.sum_Ico_eq_sum_range]
      simpa using hzero]
    rw [zero_add]
  rw [hbridge]
  exact char_twisted_partial_bound N χ hχ s hσ x

/-- Constant-form window bound: on `{σ₀ ≤ Re s, ‖s‖ ≤ R}`,
    `‖L(s,χ)‖ ≤ N(2 + R/σ₀)` — the `M` that Borel–Carathéodory consumes. -/
lemma LFunction_window_bound (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (σ₀ R : ℝ) (hσ₀ : 0 < σ₀) (hR : 0 ≤ R) (s : ℂ)
    (hs1 : σ₀ ≤ s.re) (hs2 : ‖s‖ ≤ R) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (N : ℝ) * (2 + R / σ₀) := by
  have hσ : 0 < s.re := lt_of_lt_of_le hσ₀ hs1
  calc ‖DirichletCharacter.LFunction χ s‖
      ≤ (N : ℝ) * (2 + ‖s‖ / s.re) := LFunction_strip_bound N χ hχ s hσ
    _ ≤ (N : ℝ) * (2 + R / σ₀) := by
        gcongr

open Metric in
/-- **Uniform derivative bound** (SW uniformity brick 14): whenever the closed `r`-ball
    around `s` stays in the window `{σ₀ ≤ Re, ‖·‖ ≤ R}`,
    `‖L'(s,χ)‖ ≤ N(2 + R/σ₀)/r` — the Cauchy estimate over the uniform window bound.
    Feeds the 3-4-1 error terms and the Landau assembly. -/
lemma LFunction_deriv_bound (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (σ₀ R r : ℝ) (hσ₀ : 0 < σ₀) (hr : 0 < r) (s : ℂ)
    (h1 : σ₀ + r ≤ s.re) (h2 : ‖s‖ + r ≤ R) :
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ (N : ℝ) * (2 + R / σ₀) / r := by
  have hR0 : (0:ℝ) ≤ R := le_trans (by positivity) h2
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    ((DirichletCharacter.differentiable_LFunction hχ).diffContOnCl)
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have hzre : σ₀ ≤ z.re := by
    have hd : |(z - s).re| ≤ ‖z - s‖ := Complex.abs_re_le_norm _
    have h3 : z.re = s.re + (z - s).re := by
      simp [Complex.sub_re]
    rw [h3]
    have := abs_le.mp (hz ▸ hd)
    linarith
  have hznorm : ‖z‖ ≤ R := by
    calc ‖z‖ = ‖s + (z - s)‖ := by ring_nf
      _ ≤ ‖s‖ + ‖z - s‖ := norm_add_le _ _
      _ = ‖s‖ + r := by rw [hz]
      _ ≤ R := h2
  exact LFunction_window_bound N χ hχ σ₀ R hσ₀ hR0 z hzre hznorm

open Finset in
open scoped LSeries.notation in
/-- **The uniform non-vanishing anchor** (SW uniformity brick 15): for EVERY modulus and
    nontrivial character, `‖L(2,χ)‖ ≥ 2 − π²/6 > 0` — the `f(s₀)` lower bound the Landau
    log-derivative lemma normalizes against. -/
lemma LFunction_two_lower_uniform (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    2 - Real.pi ^ 2 / 6 ≤ ‖DirichletCharacter.LFunction χ 2‖ := by
  have h2re : (1:ℝ) < ((2:ℂ)).re := by norm_num
  rw [DirichletCharacter.LFunction_eq_LSeries _ h2re]
  have hsum : LSeriesSummable (↗χ) 2 := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ h2re
    intro n hn
    exact χ.norm_le_one _
  -- split off the first two terms
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hterm0 : LSeries.term (↗χ) 2 0 = 0 := LSeries.term_zero _ _
  have hterm1 : LSeries.term (↗χ) 2 1 = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    simp
  have hhead : ∑ i ∈ Finset.range 2, LSeries.term (↗χ) 2 i = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hterm0, hterm1, zero_add]
  -- tail norm bound via Basel
  have hbasel : Summable (fun n : ℕ => (1:ℝ) / ((n:ℝ)) ^ 2) := hasSum_zeta_two.summable
  have htails : Summable (fun i : ℕ => (1:ℝ) / (((i + 2 : ℕ)):ℝ) ^ 2) := by
    exact_mod_cast (summable_nat_add_iff 2).mpr hbasel
  have htermbound : ∀ i : ℕ, ‖LSeries.term (↗χ) 2 (i + 2)‖ ≤ (1:ℝ) / (((i + 2 : ℕ)):ℝ) ^ 2 := by
    intro i
    rw [LSeries.term_of_ne_zero (by omega)]
    rw [norm_div]
    have hpow : ‖(((i + 2 : ℕ)) : ℂ) ^ (2 : ℂ)‖ = (((i + 2 : ℕ)):ℝ) ^ 2 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      rw [show ((2:ℂ)).re = (2:ℝ) by norm_num]
      rw [Real.rpow_two]
    rw [hpow]
    have hnum : ‖(↗χ) ((i + 2 : ℕ))‖ ≤ 1 := χ.norm_le_one _
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have htailnorm : ‖∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have hsumtail : Summable (fun i : ℕ => LSeries.term (↗χ) 2 (i + 2)) :=
      (summable_nat_add_iff 2).mpr hsum
    calc ‖∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2)‖
        ≤ ∑' i : ℕ, ‖LSeries.term (↗χ) 2 (i + 2)‖ := norm_tsum_le_tsum_norm hsumtail.norm
      _ ≤ ∑' i : ℕ, (1:ℝ) / (((i + 2 : ℕ)):ℝ) ^ 2 :=
          Summable.tsum_mono hsumtail.norm htails (fun i => htermbound i)
      _ = Real.pi ^ 2 / 6 - 1 := by
          have hfull := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
          have hh : ∑ i ∈ Finset.range 2, (1:ℝ) / ((i:ℝ)) ^ 2 = 1 := by
            rw [Finset.sum_range_succ, Finset.sum_range_one]
            norm_num
          rw [hh, hasSum_zeta_two.tsum_eq] at hfull
          have : ∑' (i : ℕ), (1:ℝ) / ((((i + 2 : ℕ)):ℝ)) ^ 2
              = Real.pi ^ 2 / 6 - 1 := by
            push_cast at hfull ⊢
            linarith
          exact this
  -- reverse triangle
  have hLS : LSeries (↗χ) 2 = 1 + ∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2) := by
    rw [LSeries, ← hsplit, hhead]
  rw [hLS]
  have htri := norm_sub_le (1 + ∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2))
    (∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2))
  have hone : ‖(1 + ∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2))
      - ∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2)‖ = 1 := by
    rw [show (1 + ∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2))
        - ∑' i : ℕ, LSeries.term (↗χ) 2 (i + 2) = 1 by ring]
    norm_num
  rw [hone] at htri
  linarith [htailnorm, htri]

/-- **The normalized log-ratio bound** (SW uniformity brick 16): on the window,
    `log‖L(s,χ)‖ − log‖L(2,χ)‖ ≤ log(N(2+R/σ₀)) − log(2−π²/6)` — exactly the `M` that
    Borel–Carathéodory takes when applied to `log(L(z)/L(2))` in the Landau assembly. -/
lemma LFunction_log_ratio_bound (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (σ₀ R : ℝ) (hσ₀ : 0 < σ₀) (hR : 0 ≤ R) (s : ℂ)
    (hs1 : σ₀ ≤ s.re) (hs2 : ‖s‖ ≤ R) :
    Real.log ‖DirichletCharacter.LFunction χ s‖
      - Real.log ‖DirichletCharacter.LFunction χ 2‖
      ≤ Real.log ((N : ℝ) * (2 + R / σ₀)) - Real.log (2 - Real.pi ^ 2 / 6) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hM : (1:ℝ) ≤ (N : ℝ) * (2 + R / σ₀) := by
    have h2 : (2:ℝ) ≤ 2 + R / σ₀ := by linarith [div_nonneg hR hσ₀.le]
    nlinarith
  have hanchor_pos : (0:ℝ) < 2 - Real.pi ^ 2 / 6 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  -- upper piece
  have hup : Real.log ‖DirichletCharacter.LFunction χ s‖
      ≤ Real.log ((N : ℝ) * (2 + R / σ₀)) := by
    rcases eq_or_lt_of_le (norm_nonneg (DirichletCharacter.LFunction χ s)) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg hM
    · exact Real.log_le_log h0 (LFunction_window_bound N χ hχ σ₀ R hσ₀ hR s hs1 hs2)
  -- lower piece
  have hlow : Real.log (2 - Real.pi ^ 2 / 6)
      ≤ Real.log ‖DirichletCharacter.LFunction χ 2‖ :=
    Real.log_le_log hanchor_pos (LFunction_two_lower_uniform N χ hχ)
  linarith

open Finset in
/-- Log-derivative of a linear factor: `logDeriv (· − ρ) z = 1/(z − ρ)`. -/
lemma logDeriv_sub_const (ρ z : ℂ) (hz : z ≠ ρ) :
    logDeriv (fun w => w - ρ) z = 1 / (z - ρ) := by
  rw [logDeriv_apply]
  rw [deriv_sub_const, deriv_id'']

open Finset in
/-- **The Landau partial-fraction skeleton** (SW uniformity brick 17): if
    `f = g·∏_{ρ∈S}(·−ρ)` with `g(z) ≠ 0` and `z` off the zero set, then
    `f'/f(z) = g'/g(z) + ∑_{ρ∈S} 1/(z−ρ)` — the exact shape Landau's lemma extracts:
    the log-derivative equals the nearby-zero partial fractions plus a BC-bounded rest. -/
lemma logDeriv_factored (g : ℂ → ℂ) (S : Finset ℂ) (z : ℂ)
    (hg : g z ≠ 0) (hz : ∀ ρ ∈ S, z ≠ ρ) (hgd : DifferentiableAt ℂ g z) :
    logDeriv (fun w => g w * ∏ ρ ∈ S, (w - ρ)) z
      = logDeriv g z + ∑ ρ ∈ S, 1 / (z - ρ) := by
  have hfac : ∀ ρ ∈ S, (fun w : ℂ => w - ρ) z ≠ 0 := by
    intro ρ hρ
    exact sub_ne_zero_of_ne (hz ρ hρ)
  have hfacd : ∀ ρ ∈ S, DifferentiableAt ℂ (fun w : ℂ => w - ρ) z := by
    intro ρ _
    exact (differentiable_id.sub_const ρ).differentiableAt
  rw [logDeriv_fun_mul z hg ?_ hgd ?_]
  · congr 1
    rw [show logDeriv (fun w : ℂ => ∏ ρ ∈ S, (w - ρ)) z
        = ∑ ρ ∈ S, logDeriv (fun w : ℂ => w - ρ) z from logDeriv_fun_prod hfac hfacd]
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact logDeriv_sub_const ρ z (hz ρ hρ)
  · rw [Finset.prod_ne_zero_iff]
    intro ρ hρ
    exact sub_ne_zero_of_ne (hz ρ hρ)
  · apply DifferentiableAt.fun_finsetProd
    intro ρ hρ
    exact hfacd ρ hρ

/-- **Log-derivative of the canonical factor** (SW uniformity brick 19):
    `logDeriv (canonicalFactor R w) z = −w̄/(R²−w̄z) − 1/(z−w)` — the per-factor
    contribution in the Landau assembly over `exists_canonicalDecomp`. -/
lemma logDeriv_canonicalFactor (R : ℝ) (w z : ℂ) (hR : (R:ℂ) ≠ 0)
    (hN : (R:ℂ) ^ 2 - (starRingEnd ℂ) w * z ≠ 0) (hD : z ≠ w) :
    logDeriv (Complex.canonicalFactor R w) z
      = (-(starRingEnd ℂ) w) / ((R:ℂ) ^ 2 - (starRingEnd ℂ) w * z) - 1 / (z - w) := by
  rw [Complex.canonicalFactor_def]
  have hDen : (R:ℂ) * (z - w) ≠ 0 := mul_ne_zero hR (sub_ne_zero_of_ne hD)
  have hdifN : DifferentiableAt ℂ (fun y : ℂ => (R:ℂ) ^ 2 - (starRingEnd ℂ) w * y) z := by
    fun_prop
  have hdifD : DifferentiableAt ℂ (fun y : ℂ => (R:ℂ) * (y - w)) z := by
    fun_prop
  rw [logDeriv_fun_div z hN hDen hdifN hdifD]
  congr 1
  · rw [logDeriv_apply]
    have hder : deriv (fun y : ℂ => (R:ℂ) ^ 2 - (starRingEnd ℂ) w * y) z
        = -(starRingEnd ℂ) w := by
      rw [deriv_fun_sub (by fun_prop) (by fun_prop)]
      simp [deriv_const_mul_field]
    rw [hder]
  · have hsplit : logDeriv (fun y : ℂ => (R:ℂ) * (y - w)) z
        = logDeriv (fun y : ℂ => y - w) z := logDeriv_const_mul z (R:ℂ) hR
    rw [hsplit, logDeriv_sub_const w z hD]

open Finset in
open scoped LSeries.notation in
/-- **Anchor on the whole line Re s = 2** (Landau brick L1): `‖L(s,χ)‖ ≥ 2 − π²/6` for
    every modulus, nontrivial character, and s with `Re s = 2` — the normalization lower
    bound at the Landau ball's center `2 + it₀`. -/
lemma LFunction_anchor_re_two (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) (hs : s.re = 2) :
    2 - Real.pi ^ 2 / 6 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have h2re : (1:ℝ) < s.re := by rw [hs]; norm_num
  rw [DirichletCharacter.LFunction_eq_LSeries _ h2re]
  have hsum : LSeriesSummable (↗χ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ h2re
    intro n hn
    exact χ.norm_le_one _
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hterm0 : LSeries.term (↗χ) s 0 = 0 := LSeries.term_zero _ _
  have hterm1 : LSeries.term (↗χ) s 1 = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    simp
  have hhead : ∑ i ∈ Finset.range 2, LSeries.term (↗χ) s i = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hterm0, hterm1, zero_add]
  have hbasel : Summable (fun n : ℕ => (1:ℝ) / ((n:ℝ)) ^ 2) := hasSum_zeta_two.summable
  have htails : Summable (fun i : ℕ => (1:ℝ) / (((i + 2 : ℕ)):ℝ) ^ 2) := by
    exact_mod_cast (summable_nat_add_iff 2).mpr hbasel
  have htermbound : ∀ i : ℕ, ‖LSeries.term (↗χ) s (i + 2)‖ ≤ (1:ℝ) / (((i + 2 : ℕ)):ℝ) ^ 2 := by
    intro i
    rw [LSeries.term_of_ne_zero (by omega)]
    rw [norm_div]
    have hpow : ‖(((i + 2 : ℕ)) : ℂ) ^ s‖ = (((i + 2 : ℕ)):ℝ) ^ 2 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega), hs, Real.rpow_two]
    rw [hpow]
    have hnum : ‖(↗χ) ((i + 2 : ℕ))‖ ≤ 1 := χ.norm_le_one _
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have htailnorm : ‖∑' i : ℕ, LSeries.term (↗χ) s (i + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have hsumtail : Summable (fun i : ℕ => LSeries.term (↗χ) s (i + 2)) :=
      (summable_nat_add_iff 2).mpr hsum
    calc ‖∑' i : ℕ, LSeries.term (↗χ) s (i + 2)‖
        ≤ ∑' i : ℕ, ‖LSeries.term (↗χ) s (i + 2)‖ := norm_tsum_le_tsum_norm hsumtail.norm
      _ ≤ ∑' i : ℕ, (1:ℝ) / (((i + 2 : ℕ)):ℝ) ^ 2 :=
          Summable.tsum_mono hsumtail.norm htails (fun i => htermbound i)
      _ = Real.pi ^ 2 / 6 - 1 := by
          have hfull := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
          have hh : ∑ i ∈ Finset.range 2, (1:ℝ) / ((i:ℝ)) ^ 2 = 1 := by
            rw [Finset.sum_range_succ, Finset.sum_range_one]
            norm_num
          rw [hh, hasSum_zeta_two.tsum_eq] at hfull
          push_cast at hfull ⊢
          linarith
  have hLS : LSeries (↗χ) s = 1 + ∑' i : ℕ, LSeries.term (↗χ) s (i + 2) := by
    rw [LSeries, ← hsplit, hhead]
  rw [hLS]
  have htri := norm_sub_le (1 + ∑' i : ℕ, LSeries.term (↗χ) s (i + 2))
    (∑' i : ℕ, LSeries.term (↗χ) s (i + 2))
  have hone : ‖(1 + ∑' i : ℕ, LSeries.term (↗χ) s (i + 2))
      - ∑' i : ℕ, LSeries.term (↗χ) s (i + 2)‖ = 1 := by
    rw [show (1 + ∑' i : ℕ, LSeries.term (↗χ) s (i + 2))
        - ∑' i : ℕ, LSeries.term (↗χ) s (i + 2) = 1 by ring]
    norm_num
  rw [hone] at htri
  linarith [htailnorm, htri]

open Metric Complex in
/-- **The holomorphic logarithm on a disk** (Landau brick L2): a nonvanishing holomorphic
    function on a ball is `g(c)·exp(h)` for a primitive `h` of `g′/g` with `h(c) = 0`.
    Then `Re h = log‖g‖ − log‖g(c)‖`, which Borel–Carathéodory consumes. -/
lemma exists_exp_eq_of_ne_zero (g : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hne : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ h : ℂ → ℂ, h c = 0 ∧ (∀ z ∈ ball c R, HasDerivAt h (deriv g z / g z) z) ∧
      ∀ z ∈ ball c R, g z = g c * Complex.exp (h z) := by
  by_cases hR : R ≤ 0
  · exact ⟨fun _ => 0, rfl, fun z hz => absurd hz (by simp [ball_eq_empty.mpr hR]),
      fun z hz => absurd hz (by simp [ball_eq_empty.mpr hR])⟩
  push_neg at hR
  have hcball : c ∈ ball c R := mem_ball_self hR
  -- the logarithmic derivative is holomorphic on the ball
  have hganal : AnalyticOnNhd ℂ g (ball c R) := hg.analyticOnNhd isOpen_ball
  have hderivg : DifferentiableOn ℂ (deriv g) (ball c R) :=
    (hganal.deriv).differentiableOn
  have hφ : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) :=
    hderivg.div hg hne
  -- primitive normalized at c
  obtain ⟨h, hc0, hd⟩ := (hφ.isExactOn_ball).with_val_at c 0
  refine ⟨h, hc0, fun z hz => hd z hz, ?_⟩
  -- k := g·exp(−h) has zero derivative on the ball
  set k : ℂ → ℂ := fun z => g z * Complex.exp (-h z) with hk
  have hkderiv : ∀ z ∈ ball c R, HasDerivAt k 0 z := by
    intro z hz
    have h1 : HasDerivAt g (deriv g z) z :=
      ((hg.differentiableAt (isOpen_ball.mem_nhds hz))).hasDerivAt
    have h2 : HasDerivAt (fun w => Complex.exp (-h w))
        (Complex.exp (-h z) * (-(deriv g z / g z))) z := by
      have := ((hd z hz).neg).cexp
      simpa using this
    rw [hk]
    have hgφ : g z * (deriv g z / g z) = deriv g z := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ (hne z hz)
    have h3 := h1.mul h2
    have heq : deriv g z * Complex.exp (-h z)
        + g z * (Complex.exp (-h z) * -(deriv g z / g z)) = 0 := by
      calc deriv g z * Complex.exp (-h z)
            + g z * (Complex.exp (-h z) * -(deriv g z / g z))
          = deriv g z * Complex.exp (-h z)
            - Complex.exp (-h z) * (g z * (deriv g z / g z)) := by ring
        _ = 0 := by rw [hgφ]; ring
    exact heq ▸ h3
  -- constant on the convex ball
  have hconst : ∀ z ∈ ball c R, k z = k c := by
    intro z hz
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) (convex_ball c R)
    · intro x hx
      exact ((hkderiv x hx).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [fderivWithin_of_isOpen isOpen_ball hx]
      exact ((hkderiv x hx).hasFDerivAt).fderiv.trans (by ext; simp)
    · exact hz
    · exact hcball
  intro z hz
  have hkz := hconst z hz
  rw [hk] at hkz
  simp only at hkz
  rw [hc0] at hkz
  simp at hkz
  rw [← hkz, mul_assoc, ← Complex.exp_add]
  simp

open Metric Complex in
/-- **The Landau bound for nonvanishing functions** (brick L3): if `g` is holomorphic and
    nonvanishing on `B(c,R)` with `‖g‖ ≤ Mb` there and `‖g(c)‖ ≥ ml > 0`, then on the
    quarter ball `‖g′/g‖ ≤ 8(log(Mb/ml)+1)/R` — Borel–Carathéodory on the holomorphic
    logarithm, then the Cauchy estimate. -/
lemma logDeriv_bound_of_ne_zero (g : ℂ → ℂ) (c : ℂ) (R Mb ml : ℝ)
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball c R))
    (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hMb : ∀ z ∈ ball c R, ‖g z‖ ≤ Mb) (hml : 0 < ml) (hlow : ml ≤ ‖g c‖)
    (z : ℂ) (hz : z ∈ ball c (R / 4)) :
    ‖deriv g z / g z‖ ≤ 8 * (Real.log (Mb / ml) + 1) / R := by
  obtain ⟨h, hc0, hd, hexp⟩ := exists_exp_eq_of_ne_zero g c R hg hne
  set M : ℝ := Real.log (Mb / ml) + 1 with hM
  have hcball : c ∈ ball c R := mem_ball_self hR
  have hgcpos : 0 < ‖g c‖ := lt_of_lt_of_le hml hlow
  have hMbml : ml ≤ Mb := le_trans hlow (hMb c hcball)
  have hM0 : 0 < M := by
    have : (0:ℝ) ≤ Real.log (Mb / ml) :=
      Real.log_nonneg ((one_le_div hml).mpr hMbml)
    linarith
  -- Re h ≤ M on the ball
  have hre : ∀ w ∈ ball c R, (h w).re ≤ M := by
    intro w hw
    have hnorm : ‖g w‖ = ‖g c‖ * Real.exp ((h w).re) := by
      rw [hexp w hw, norm_mul, Complex.norm_exp]
    have hgwpos : 0 < ‖g w‖ := norm_pos_iff.mpr (hne w hw)
    have hlog : Real.log ‖g w‖ = Real.log ‖g c‖ + (h w).re := by
      rw [hnorm, Real.log_mul hgcpos.ne' (Real.exp_ne_zero _), Real.log_exp]
    have h1 : Real.log ‖g w‖ ≤ Real.log Mb := Real.log_le_log hgwpos (hMb w hw)
    have h2 : Real.log ml ≤ Real.log ‖g c‖ := Real.log_le_log hml hlow
    have h3 : Real.log (Mb / ml) = Real.log Mb - Real.log ml :=
      Real.log_div (by linarith) hml.ne'
    rw [hM]
    linarith
  -- shifted function for center-0 Borel–Carathéodory
  set h₀ : ℂ → ℂ := fun w => h (c + w) with hh₀
  have hmem : ∀ w : ℂ, w ∈ ball (0:ℂ) R → c + w ∈ ball c R := by
    intro w hw
    rw [mem_ball] at hw ⊢
    simpa [dist_eq_norm] using hw
  have hh₀0 : h₀ 0 = 0 := by
    rw [hh₀]
    simpa using hc0
  have hh₀diff : DifferentiableOn ℂ h₀ (ball 0 R) := by
    intro w hw
    exact (((hd (c + w) (hmem w hw)).differentiableAt).comp w
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
  have hh₀re : Set.MapsTo h₀ (ball 0 R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    exact hre (c + w) (hmem w hw)
  -- ‖h‖ ≤ 2M on the half ball
  have hhbound : ∀ w ∈ ball c (R / 2), ‖h w‖ ≤ 2 * M := by
    intro w hw
    have hwc : ‖w - c‖ < R / 2 := by
      rw [mem_ball, dist_eq_norm] at hw
      exact hw
    have hw0 : w - c ∈ ball (0:ℂ) R := by
      rw [mem_ball, dist_zero_right]
      linarith
    have hbc := Complex.borelCaratheodory hM0 hh₀diff hh₀re hR hw0
    have hval : h₀ (w - c) = h w := by
      rw [hh₀]
      simp
    have hzeroterm : ‖h₀ 0‖ = 0 := by
      rw [hh₀0, norm_zero]
    rw [hval, hzeroterm] at hbc
    simp only [zero_mul, zero_div, add_zero] at hbc
    have hden : R / 2 ≤ R - ‖w - c‖ := by linarith
    have hdenpos : (0:ℝ) < R - ‖w - c‖ := by linarith [norm_nonneg (w - c)]
    calc ‖h w‖ ≤ 2 * M * ‖w - c‖ / (R - ‖w - c‖) := hbc
      _ ≤ 2 * M * (R / 2) / (R / 2) := by
          gcongr <;> linarith
      _ = 2 * M := by field_simp
  -- Cauchy estimate on the quarter ball
  have hzc : ‖z - c‖ < R / 4 := by
    rw [mem_ball, dist_eq_norm] at hz
    exact hz
  have hzball : z ∈ ball c R := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have hr4 : (0:ℝ) < R / 4 := by linarith
  have hsub : closedBall z (R / 4) ⊆ ball c R := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_eq_norm]
    calc ‖y - c‖ = ‖(y - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖y - z‖ + ‖z - c‖ := norm_add_le _ _
      _ < R / 4 + R / 4 := by linarith
      _ ≤ R := by linarith
  have hdiffh : DifferentiableOn ℂ h (ball c R) := by
    intro y hy
    exact ((hd y hy).differentiableAt).differentiableWithinAt
  have hdccl : DiffContOnCl ℂ h (ball z (R / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hr4.ne']
    exact hdiffh.mono hsub
  have hsphere : ∀ y ∈ sphere z (R / 4), ‖h y‖ ≤ 2 * M := by
    intro y hy
    rw [mem_sphere_iff_norm] at hy
    apply hhbound
    rw [mem_ball, dist_eq_norm]
    calc ‖y - c‖ = ‖(y - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖y - z‖ + ‖z - c‖ := norm_add_le _ _
      _ < R / 4 + R / 4 := by
          rw [hy]
          linarith
      _ = R / 2 := by ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr4 hdccl hsphere
  have hderiv_eq : deriv h z = deriv g z / g z := (hd z hzball).deriv
  rw [hderiv_eq] at hcauchy
  calc ‖deriv g z / g z‖ ≤ 2 * M / (R / 4) := hcauchy
    _ = 8 * M / R := by
        field_simp
        ring

open Metric Complex Finset in
/-- Log-derivative of a finite product of powered linear factors:
    `logDeriv (∏ (·−ρ)^{m ρ}) z = ∑ m ρ/(z−ρ)`. -/
lemma logDeriv_prod_pow (S : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) (hz : ∀ ρ ∈ S, z ≠ ρ) :
    logDeriv (fun w => ∏ ρ ∈ S, (w - ρ) ^ (m ρ)) z
      = ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ) := by
  have hfac : ∀ ρ ∈ S, (fun w : ℂ => (w - ρ) ^ (m ρ)) z ≠ 0 := by
    intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero_of_ne (hz ρ hρ))
  have hfacd : ∀ ρ ∈ S, DifferentiableAt ℂ (fun w : ℂ => (w - ρ) ^ (m ρ)) z := by
    intro ρ _
    exact ((differentiable_id.sub_const ρ).pow _).differentiableAt
  rw [show logDeriv (fun w : ℂ => ∏ ρ ∈ S, (w - ρ) ^ (m ρ)) z
      = ∑ ρ ∈ S, logDeriv (fun w : ℂ => (w - ρ) ^ (m ρ)) z from
    logDeriv_fun_prod hfac hfacd]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have h1 : logDeriv (fun w : ℂ => (w - ρ) ^ (m ρ)) z
      = (m ρ : ℂ) * logDeriv (fun w : ℂ => w - ρ) z := by
    have := logDeriv_fun_zpow (f := fun w : ℂ => w - ρ) (x := z)
      ((differentiable_id.sub_const ρ).differentiableAt) (m ρ : ℤ)
    simpa using this
  rw [h1, logDeriv_sub_const ρ z (hz ρ hρ)]
  ring

open Metric Complex Finset in
/-- **The conditional Landau lemma** (brick L5): given a factorization
    `f = g·∏(·−ρ)^{m ρ}` on `B(c,R)` with `g` holomorphic nonvanishing, `‖g‖ ≤ Mb`,
    `‖g(c)‖ ≥ ml`, the log-derivative of `f` on the quarter ball is the zero
    partial-fractions plus an `8(log(Mb/ml)+1)/R` remainder. -/
lemma landau_of_factorization (f g : ℂ → ℂ) (c : ℂ) (R Mb ml : ℝ) (S : Finset ℂ)
    (m : ℂ → ℕ) (hR : 0 < R)
    (hfac : ∀ z ∈ ball c R, f z = g z * ∏ ρ ∈ S, (z - ρ) ^ (m ρ))
    (hg : DifferentiableOn ℂ g (ball c R)) (hgne : ∀ z ∈ ball c R, g z ≠ 0)
    (hMb : ∀ z ∈ ball c R, ‖g z‖ ≤ Mb) (hml : 0 < ml) (hlow : ml ≤ ‖g c‖)
    (z : ℂ) (hz : z ∈ ball c (R / 4)) (hzS : ∀ ρ ∈ S, z ≠ ρ) :
    ‖logDeriv f z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖
      ≤ 8 * (Real.log (Mb / ml) + 1) / R := by
  have hzR : z ∈ ball c R := by
    rw [mem_ball] at hz ⊢
    linarith [hz]
  -- logDeriv f = logDeriv g + partial fractions at z
  have hPne : (fun w : ℂ => ∏ ρ ∈ S, (w - ρ) ^ (m ρ)) z ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero_of_ne (hzS ρ hρ))
  have hPd : DifferentiableAt ℂ (fun w : ℂ => ∏ ρ ∈ S, (w - ρ) ^ (m ρ)) z := by
    apply DifferentiableAt.fun_finsetProd
    intro ρ _
    exact ((differentiable_id.sub_const ρ).pow _).differentiableAt
  have hgd : DifferentiableAt ℂ g z :=
    hg.differentiableAt (isOpen_ball.mem_nhds hzR)
  have hlog_eq : logDeriv f z = logDeriv g z + ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ) := by
    have hfeq : f =ᶠ[nhds z] (fun w => g w * ∏ ρ ∈ S, (w - ρ) ^ (m ρ)) := by
      filter_upwards [isOpen_ball.mem_nhds hzR] with w hw
      exact hfac w hw
    rw [logDeriv_apply, Filter.EventuallyEq.deriv_eq hfeq, hfeq.eq_of_nhds,
      ← logDeriv_apply]
    rw [logDeriv_fun_mul z (hgne z hzR) hPne hgd hPd]
    rw [logDeriv_prod_pow S m z hzS]
  rw [hlog_eq]
  rw [show logDeriv g z + ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)
      - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ) = logDeriv g z by ring]
  rw [logDeriv_apply]
  exact logDeriv_bound_of_ne_zero g c R Mb ml hR hg hgne hMb hml hlow z hz

open Metric in
/-- **Finiteness of zeros on a compact sub-ball** (Landau brick L4a): a holomorphic
    function on `B(c,R₁)`, nonzero at the center, has finitely many zeros in
    `closedBall c R` for `R < R₁` — zeros are isolated (else the identity theorem
    contradicts `f(c) ≠ 0`), and a discrete compact set is finite. -/
lemma zeros_finite_of_ne_center (f : ℂ → ℂ) (c : ℂ) (R₁ R : ℝ)
    (hR : 0 < R) (hRR : R < R₁)
    (hf : DifferentiableOn ℂ f (ball c R₁)) (hfc : f c ≠ 0) :
    {z | z ∈ closedBall c R ∧ f z = 0}.Finite := by
  have hanal : AnalyticOnNhd ℂ f (ball c R₁) := hf.analyticOnNhd isOpen_ball
  have hsub : closedBall c R ⊆ ball c R₁ := closedBall_subset_ball hRR
  have hcball : c ∈ ball c R₁ := mem_ball_self (lt_trans hR hRR)
  have hnotloc : ∀ z ∈ ball c R₁, ¬ (∀ᶠ w in nhds z, f w = 0) := by
    intro z hz hev
    have heq : Set.EqOn f 0 (ball c R₁) :=
      hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball c R₁).isPreconnected hz hev
    exact hfc (heq hcball)
  set Z : Set ℂ := {z | z ∈ closedBall c R ∧ f z = 0} with hZ
  -- Z is compact
  have hfcont : ContinuousOn f (closedBall c R) := (hf.mono hsub).continuousOn
  have hZclosed : IsClosed Z := by
    have h1 : Z = closedBall c R ∩ f ⁻¹' {0} := by
      ext w
      simp [hZ, Set.mem_inter_iff]
    rw [h1]
    exact hfcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hZcompact : IsCompact Z :=
    (isCompact_closedBall c R).of_isClosed_subset hZclosed
      (by intro w hw; exact hw.1)
  -- Z is discrete
  have hZdisc : IsDiscrete Z := by
    rw [isDiscrete_iff_nhdsNE]
    intro z hzZ
    obtain ⟨hzball, hz0⟩ := hzZ
    have hzb : z ∈ ball c R₁ := hsub hzball
    rcases (hanal z hzb).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h (hnotloc z hzb)
    · rw [Filter.inf_principal_eq_bot]
      filter_upwards [h] with w hw
      intro hwZ
      exact hw hwZ.2
  exact hZcompact.finite hZdisc

open Metric in
/-- **The global one-zero peel** (Landau brick L4b): if `f` is holomorphic on open `U`
    with `analyticOrderAt f ρ = n` at `ρ ∈ U`, then `f = (·−ρ)^n · g` on ALL of `U`
    with `g` holomorphic on `U` and `g(ρ) ≠ 0` — the local order factorization glued
    with the direct quotient off `ρ`. -/
lemma peel_zero (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (ρ : ℂ) (hρ : ρ ∈ U) (n : ℕ) (hn : analyticOrderAt f ρ = n) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ g ρ ≠ 0 ∧
      ∀ z ∈ U, f z = (z - ρ) ^ n * g z := by
  have hanal : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  obtain ⟨g₀, hg₀anal, hg₀ne, hg₀ev⟩ :=
    ((hanal ρ hρ).analyticOrderAt_eq_natCast).mp hn
  classical
  set g : ℂ → ℂ := fun z => if z = ρ then g₀ ρ else f z / (z - ρ) ^ n with hg
  have hg_near : g =ᶠ[nhds ρ] g₀ := by
    filter_upwards [hg₀ev] with z hz
    by_cases hzρ : z = ρ
    · simp [hg, hzρ]
    · simp only [hg, if_neg hzρ]
      rw [hz, smul_eq_mul]
      field_simp [sub_ne_zero_of_ne hzρ]
  have hgρ : g ρ = g₀ ρ := by
    simp [hg]
  refine ⟨g, ?_, by rw [hgρ]; exact hg₀ne, ?_⟩
  · -- differentiability
    intro z hz
    by_cases hzρ : z = ρ
    · subst hzρ
      exact ((hg₀anal.differentiableAt).congr_of_eventuallyEq hg_near
        ).differentiableWithinAt
    · have hev : g =ᶠ[nhds z] (fun w => f w / (w - ρ) ^ n) := by
        have hopen : IsOpen (U \ {ρ}) := hU.sdiff isClosed_singleton
        filter_upwards [hopen.mem_nhds ⟨hz, by simpa using hzρ⟩] with w hw
        simp only [hg, if_neg (show w ≠ ρ by simpa using hw.2)]
      have hd : DifferentiableAt ℂ (fun w => f w / (w - ρ) ^ n) z := by
        apply DifferentiableAt.div
        · exact hf.differentiableAt (hU.mem_nhds hz)
        · exact ((differentiable_id.sub_const ρ).pow n).differentiableAt
        · exact pow_ne_zero _ (sub_ne_zero_of_ne hzρ)
      exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  · -- factorization
    intro z hz
    by_cases hzρ : z = ρ
    · rw [hzρ]
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · have h0 := hg₀ev.self_of_nhds
        simp only [pow_zero, one_mul] at h0 ⊢
        simp [hg, h0]
      · have hfρ : f ρ = 0 := by
          have := hg₀ev.self_of_nhds
          rw [this]
          simp [zero_pow hn0.ne']
        rw [hfρ, sub_self, zero_pow hn0.ne', zero_mul]
    · simp only [hg, if_neg hzρ]
      field_simp [pow_ne_zero n (sub_ne_zero_of_ne hzρ)]

open Metric in
/-- **The full zero factorization on a compact sub-ball** (Landau brick L4c): a
    holomorphic `f` on `B(c,R₁)`, nonzero at the center, factors on the whole ball as
    `f = g·∏_{ρ∈S}(·−ρ)^{m ρ}` with `S ⊆ closedBall c R` its zeros there, `m ρ ≥ 1`,
    and `g` holomorphic, nonvanishing on `closedBall c R`. Induction on the number of
    zeros with the one-zero peel. -/
lemma exists_zero_factorization (c : ℂ) (R₁ R : ℝ) (hR : 0 < R) (hRR : R < R₁) :
    ∀ (k : ℕ) (f : ℂ → ℂ), DifferentiableOn ℂ f (ball c R₁) → f c ≠ 0 →
    ∀ (hfin : {z | z ∈ closedBall c R ∧ f z = 0}.Finite), hfin.toFinset.card = k →
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ ρ ∈ S, ρ ∈ closedBall c R ∧ f ρ = 0) ∧
      DifferentiableOn ℂ g (ball c R₁) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      (∀ z ∈ ball c R₁, f z = g z * ∏ ρ ∈ S, (z - ρ) ^ (m ρ)) := by
  intro k
  induction k with
  | zero =>
    intro f hf hfc hfin hcard
    refine ⟨∅, fun _ => 0, f, by simp, hf, ?_, by simp⟩
    intro z hz
    intro hz0
    have : z ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hz, hz0⟩
    rw [Finset.card_eq_zero] at hcard
    rw [hcard] at this
    simp at this
  | succ k ih =>
    intro f hf hfc hfin hcard
    -- pick a zero ρ
    have hne : hfin.toFinset.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    obtain ⟨ρ, hρmem⟩ := hne
    rw [Set.Finite.mem_toFinset] at hρmem
    obtain ⟨hρball, hρ0⟩ := hρmem
    have hρball' : ρ ∈ ball c R₁ := closedBall_subset_ball hRR hρball
    have hcball : c ∈ ball c R₁ := mem_ball_self (lt_trans hR hRR)
    -- the order at ρ is a positive natural
    have hanal : AnalyticOnNhd ℂ f (ball c R₁) := hf.analyticOnNhd isOpen_ball
    have hnotloc : ¬ (∀ᶠ w in nhds ρ, f w = 0) := by
      intro hev
      have heq : Set.EqOn f 0 (ball c R₁) :=
        hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_ball c R₁).isPreconnected hρball' hev
      exact hfc (heq hcball)
    have hordtop : analyticOrderAt f ρ ≠ ⊤ := by
      intro htop
      exact hnotloc (analyticOrderAt_eq_top.mp htop)
    set n : ℕ := analyticOrderNatAt f ρ with hn
    have hncast : (n : ℕ∞) = analyticOrderAt f ρ := Nat.cast_analyticOrderNatAt hordtop
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso
        have hoz : analyticOrderAt f ρ = ((0 : ℕ) : ℕ∞) := by
          rw [← hncast, h0]
        rw [Nat.cast_zero, analyticOrderAt_eq_zero] at hoz
        rcases hoz with h | h
        · exact h (hanal ρ hρball')
        · exact h hρ0
      · exact h
    -- peel
    obtain ⟨g₁, hg₁diff, hg₁ρ, hg₁fac⟩ :=
      peel_zero f (ball c R₁) isOpen_ball hf ρ hρball' n hncast.symm
    -- g₁ has one fewer zero
    have hg₁c : g₁ c ≠ 0 := by
      intro h0
      apply hfc
      rw [hg₁fac c hcball, h0, mul_zero]
    have hZeq : {z | z ∈ closedBall c R ∧ g₁ z = 0}
        = {z | z ∈ closedBall c R ∧ f z = 0} \ {ρ} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hwball, hw0⟩
        refine ⟨⟨hwball, ?_⟩, ?_⟩
        · rw [hg₁fac w (closedBall_subset_ball hRR hwball), hw0, mul_zero]
        · intro hwρ
          rw [hwρ] at hw0
          exact hg₁ρ hw0
      · rintro ⟨⟨hwball, hw0⟩, hwρ⟩
        refine ⟨hwball, ?_⟩
        have := hg₁fac w (closedBall_subset_ball hRR hwball)
        rw [this] at hw0
        rcases mul_eq_zero.mp hw0 with h | h
        · exact absurd h (pow_ne_zero _ (sub_ne_zero_of_ne hwρ))
        · exact h
    have hfin₁ : {z | z ∈ closedBall c R ∧ g₁ z = 0}.Finite := by
      rw [hZeq]
      exact hfin.diff
    have hcard₁ : hfin₁.toFinset.card = k := by
      have htf : hfin₁.toFinset = hfin.toFinset.erase ρ := by
        ext w
        simp only [Set.Finite.mem_toFinset, Finset.mem_erase]
        rw [hZeq]
        simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
        tauto
      rw [htf, Finset.card_erase_of_mem (by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hρball, hρ0⟩), hcard]
      omega
    -- induction hypothesis on g₁
    obtain ⟨S₁, m₁, g, hS₁, hgdiff, hgne, hgfac⟩ := ih g₁ hg₁diff hg₁c hfin₁ hcard₁
    -- ρ is not in S₁
    have hρS₁ : ρ ∉ S₁ := by
      intro hmem
      have := (hS₁ ρ hmem).2
      exact hg₁ρ this
    refine ⟨insert ρ S₁, fun x => if x = ρ then n else m₁ x, g, ?_, hgdiff, hgne, ?_⟩
    · intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ₁
      · exact ⟨hρball, hρ0⟩
      · obtain ⟨hσball, hσ0⟩ := hS₁ σ hσ₁
        refine ⟨hσball, ?_⟩
        rw [hg₁fac σ (closedBall_subset_ball hRR hσball), hσ0, mul_zero]
    · intro z hz
      rw [hg₁fac z hz, hgfac z hz, Finset.prod_insert hρS₁]
      dsimp only
      rw [if_pos rfl]
      have hcongr : ∏ σ ∈ S₁, (z - σ) ^ (if σ = ρ then n else m₁ σ)
          = ∏ σ ∈ S₁, (z - σ) ^ (m₁ σ) := by
        apply Finset.prod_congr rfl
        intro σ hσ
        rw [if_neg (by
          intro h
          rw [h] at hσ
          exact hρS₁ hσ)]
      rw [hcongr]
      ring

open Metric in
/-- **Order preservation off the peeled zero** (Landau brick L4d-bridge): if
    `f = (·−ρ)^n·g` near `σ ≠ ρ`, the analytic orders of `f` and `g` at `σ` agree. -/
lemma analyticOrderAt_peel (f g : ℂ → ℂ) (ρ σ : ℂ) (n : ℕ) (hσρ : σ ≠ ρ)
    (hg : AnalyticAt ℂ g σ) (hev : ∀ᶠ z in nhds σ, f z = (z - ρ) ^ n * g z) :
    analyticOrderAt f σ = analyticOrderAt g σ := by
  have hpow : AnalyticAt ℂ (fun z : ℂ => (z - ρ) ^ n) σ :=
    ((analyticAt_id.sub analyticAt_const).pow n)
  have h1 : analyticOrderAt f σ
      = analyticOrderAt (fun z => (z - ρ) ^ n * g z) σ :=
    analyticOrderAt_congr hev
  have h2 : analyticOrderAt (fun z => (z - ρ) ^ n * g z) σ
      = analyticOrderAt (fun z : ℂ => (z - ρ) ^ n) σ + analyticOrderAt g σ := by
    have h := analyticOrderAt_smul (f := fun z : ℂ => (z - ρ) ^ n) (g := g)
      (z₀ := σ) hpow hg
    simp only [smul_eq_mul] at h
    exact h
  have h3 : analyticOrderAt (fun z : ℂ => (z - ρ) ^ n) σ = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    exact pow_ne_zero _ (sub_ne_zero_of_ne hσρ)
  rw [h1, h2, h3, zero_add]

open Metric in
/-- **The full zero factorization on a compact sub-ball** (Landau brick L4c): a
    holomorphic `f` on `B(c,R₁)`, nonzero at the center, factors on the whole ball as
    `f = g·∏_{ρ∈S}(·−ρ)^{m ρ}` with `S ⊆ closedBall c R` its zeros there, `m ρ ≥ 1`,
    and `g` holomorphic, nonvanishing on `closedBall c R`. Induction on the number of
    zeros with the one-zero peel. -/
lemma exists_zero_factorization' (c : ℂ) (R₁ R : ℝ) (hR : 0 < R) (hRR : R < R₁) :
    ∀ (k : ℕ) (f : ℂ → ℂ), DifferentiableOn ℂ f (ball c R₁) → f c ≠ 0 →
    ∀ (hfin : {z | z ∈ closedBall c R ∧ f z = 0}.Finite), hfin.toFinset.card = k →
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ ρ ∈ S, ρ ∈ closedBall c R ∧ f ρ = 0) ∧
      (∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ) ∧
      DifferentiableOn ℂ g (ball c R₁) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      (∀ z ∈ ball c R₁, f z = g z * ∏ ρ ∈ S, (z - ρ) ^ (m ρ)) := by
  intro k
  induction k with
  | zero =>
    intro f hf hfc hfin hcard
    refine ⟨∅, fun _ => 0, f, by simp, by simp, hf, ?_, by simp⟩
    intro z hz
    intro hz0
    have : z ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hz, hz0⟩
    rw [Finset.card_eq_zero] at hcard
    rw [hcard] at this
    simp at this
  | succ k ih =>
    intro f hf hfc hfin hcard
    -- pick a zero ρ
    have hne : hfin.toFinset.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    obtain ⟨ρ, hρmem⟩ := hne
    rw [Set.Finite.mem_toFinset] at hρmem
    obtain ⟨hρball, hρ0⟩ := hρmem
    have hρball' : ρ ∈ ball c R₁ := closedBall_subset_ball hRR hρball
    have hcball : c ∈ ball c R₁ := mem_ball_self (lt_trans hR hRR)
    -- the order at ρ is a positive natural
    have hanal : AnalyticOnNhd ℂ f (ball c R₁) := hf.analyticOnNhd isOpen_ball
    have hnotloc : ¬ (∀ᶠ w in nhds ρ, f w = 0) := by
      intro hev
      have heq : Set.EqOn f 0 (ball c R₁) :=
        hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (convex_ball c R₁).isPreconnected hρball' hev
      exact hfc (heq hcball)
    have hordtop : analyticOrderAt f ρ ≠ ⊤ := by
      intro htop
      exact hnotloc (analyticOrderAt_eq_top.mp htop)
    set n : ℕ := analyticOrderNatAt f ρ with hn
    have hncast : (n : ℕ∞) = analyticOrderAt f ρ := Nat.cast_analyticOrderNatAt hordtop
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso
        have hoz : analyticOrderAt f ρ = ((0 : ℕ) : ℕ∞) := by
          rw [← hncast, h0]
        rw [Nat.cast_zero, analyticOrderAt_eq_zero] at hoz
        rcases hoz with h | h
        · exact h (hanal ρ hρball')
        · exact h hρ0
      · exact h
    -- peel
    obtain ⟨g₁, hg₁diff, hg₁ρ, hg₁fac⟩ :=
      peel_zero f (ball c R₁) isOpen_ball hf ρ hρball' n hncast.symm
    -- g₁ has one fewer zero
    have hg₁c : g₁ c ≠ 0 := by
      intro h0
      apply hfc
      rw [hg₁fac c hcball, h0, mul_zero]
    have hZeq : {z | z ∈ closedBall c R ∧ g₁ z = 0}
        = {z | z ∈ closedBall c R ∧ f z = 0} \ {ρ} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hwball, hw0⟩
        refine ⟨⟨hwball, ?_⟩, ?_⟩
        · rw [hg₁fac w (closedBall_subset_ball hRR hwball), hw0, mul_zero]
        · intro hwρ
          rw [hwρ] at hw0
          exact hg₁ρ hw0
      · rintro ⟨⟨hwball, hw0⟩, hwρ⟩
        refine ⟨hwball, ?_⟩
        have := hg₁fac w (closedBall_subset_ball hRR hwball)
        rw [this] at hw0
        rcases mul_eq_zero.mp hw0 with h | h
        · exact absurd h (pow_ne_zero _ (sub_ne_zero_of_ne hwρ))
        · exact h
    have hfin₁ : {z | z ∈ closedBall c R ∧ g₁ z = 0}.Finite := by
      rw [hZeq]
      exact hfin.diff
    have hcard₁ : hfin₁.toFinset.card = k := by
      have htf : hfin₁.toFinset = hfin.toFinset.erase ρ := by
        ext w
        simp only [Set.Finite.mem_toFinset, Finset.mem_erase]
        rw [hZeq]
        simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
        tauto
      rw [htf, Finset.card_erase_of_mem (by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hρball, hρ0⟩), hcard]
      omega
    -- induction hypothesis on g₁
    obtain ⟨S₁, m₁, g, hS₁, hm₁, hgdiff, hgne, hgfac⟩ := ih g₁ hg₁diff hg₁c hfin₁ hcard₁
    -- ρ is not in S₁
    have hρS₁ : ρ ∉ S₁ := by
      intro hmem
      have := (hS₁ ρ hmem).2
      exact hg₁ρ this
    refine ⟨insert ρ S₁, fun x => if x = ρ then n else m₁ x, g, ?_, ?_, hgdiff, hgne, ?_⟩
    · intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ₁
      · exact ⟨hρball, hρ0⟩
      · obtain ⟨hσball, hσ0⟩ := hS₁ σ hσ₁
        refine ⟨hσball, ?_⟩
        rw [hg₁fac σ (closedBall_subset_ball hRR hσball), hσ0, mul_zero]
    · intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ₁
      · dsimp only
        rw [if_pos rfl, hn]
      · have hσρ : σ ≠ ρ := by
          intro h
          rw [h] at hσ₁
          exact hρS₁ hσ₁
        dsimp only
        rw [if_neg hσρ, hm₁ σ hσ₁]
        have hσball' : σ ∈ ball c R₁ :=
          closedBall_subset_ball hRR (hS₁ σ hσ₁).1
        have hord : analyticOrderAt f σ = analyticOrderAt g₁ σ := by
          apply analyticOrderAt_peel f g₁ ρ σ n hσρ
            ((hg₁diff.analyticOnNhd isOpen_ball) σ hσball')
          filter_upwards [isOpen_ball.mem_nhds hσball'] with w hw
          exact hg₁fac w hw
        rw [analyticOrderNatAt, analyticOrderNatAt, hord]
    · intro z hz
      rw [hg₁fac z hz, hgfac z hz, Finset.prod_insert hρS₁]
      dsimp only
      rw [if_pos rfl]
      have hcongr : ∏ σ ∈ S₁, (z - σ) ^ (if σ = ρ then n else m₁ σ)
          = ∏ σ ∈ S₁, (z - σ) ^ (m₁ σ) := by
        apply Finset.prod_congr rfl
        intro σ hσ
        rw [if_neg (by
          intro h
          rw [h] at hσ
          exact hρS₁ hσ)]
      rw [hcongr]
      ring

open Metric MeromorphicOn in
/-- **The Jensen bridge** (Landau brick L4d): the multiplicity sum of a zero Finset with
    `m ρ = analyticOrderNatAt f ρ` in `closedBall c r` is bounded by
    `log(M/‖f(c)‖)/log(R/r)` — Mathlib's `AnalyticOnNhd.sum_divisor_le` pulled through
    the divisor↔order dictionary. -/
lemma sum_m_le_jensen (f : ℂ → ℂ) (c : ℂ) (r R M : ℝ) (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (h₁f : AnalyticOnNhd ℂ f (closedBall c R)) (h₂f : f c ≠ 0)
    (fbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ ρ ∈ S, ρ ∈ closedBall c r ∧ f ρ = 0)
    (hm : ∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ) :
    (∑ ρ ∈ S, (m ρ : ℝ)) ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  have hrabs : |r| = r := abs_of_pos hr
  have hRabs : |R| = R := abs_of_pos (lt_trans hr hrR)
  have h₁f' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [hRabs]
  have fbound' : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M := by rwa [hRabs]
  have hjensen := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M)
    (by rwa [hrabs]) (by rwa [hrabs, hRabs]) hM h₁f' h₂f fbound'
  -- orders are finite everywhere on the closed ball
  have hordtop : ∀ z ∈ closedBall c R, analyticOrderAt f z ≠ ⊤ := by
    intro z hz htop
    rw [analyticOrderAt_eq_top] at htop
    have heq : Set.EqOn f 0 (closedBall c R) :=
      h₁f.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_closedBall c R).isPreconnected hz htop
    exact h₂f (heq (mem_closedBall_self (by linarith)))
  -- per-point: divisor = m on S
  have hdiv : ∀ ρ ∈ S, MeromorphicOn.divisor f (closedBall c |r|) ρ = (m ρ : ℤ) := by
    intro ρ hρ
    obtain ⟨hρball, hρ0⟩ := hS ρ hρ
    have hρball' : ρ ∈ closedBall c |r| := by rwa [hrabs]
    have h₁f'' : AnalyticOnNhd ℂ f (closedBall c |r|) := by
      apply h₁f.mono
      rw [hrabs]
      gcongr
    rw [h₁f''.divisor_apply hρball']
    have hne : analyticOrderAt f ρ ≠ ⊤ :=
      hordtop ρ (by rw [hrabs] at hρball'; exact closedBall_subset_closedBall hrR.le hρball')
    rw [hm ρ hρ, analyticOrderNatAt]
    lift analyticOrderAt f ρ to ℕ using hne with n hn
    simp
  -- the finsum dominates the Finset sum
  set D := MeromorphicOn.divisor f (closedBall c |r|) with hD
  have hfin : (Function.support (D : ℂ → ℤ)).Finite := by
    have := D.finiteSupport (isCompact_closedBall c |r|)
    exact this
  have hnonneg : ∀ u, 0 ≤ D u := by
    intro u
    by_cases hu : u ∈ closedBall c |r|
    · have h₁f'' : AnalyticOnNhd ℂ f (closedBall c |r|) := by
        apply h₁f.mono
        rw [hrabs]
        gcongr
      rw [h₁f''.divisor_apply hu]
      cases hord : analyticOrderAt f u with
      | top => simp
      | coe n => simp
    · rcases eq_or_ne (D u) 0 with h | h
      · rw [h]
      · exact absurd (D.supportWithinDomain (Function.mem_support.mpr h)) hu
  have hSsub : S ⊆ hfin.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    rw [hdiv ρ hρ]
    obtain ⟨hρball, hρ0⟩ := hS ρ hρ
    -- m ρ ≥ 1 since f ρ = 0
    have hord1 : analyticOrderAt f ρ ≠ 0 := by
      intro h0
      rw [analyticOrderAt_eq_zero] at h0
      rcases h0 with h | h
      · exact h (h₁f ρ (closedBall_subset_closedBall hrR.le hρball))
      · exact h hρ0
    have hne : analyticOrderAt f ρ ≠ ⊤ :=
      hordtop ρ (closedBall_subset_closedBall hrR.le hρball)
    rw [hm ρ hρ, analyticOrderNatAt]
    intro hc
    apply hord1
    have : (analyticOrderAt f ρ).toNat = 0 := by exact_mod_cast hc
    rw [← ENat.coe_toNat hne, this]
    rfl
  have hsum_le : (∑ ρ ∈ S, (m ρ : ℤ)) ≤ ∑ᶠ u, D u := by
    rw [finsum_eq_sum (D : ℂ → ℤ) hfin]
    calc ∑ ρ ∈ S, (m ρ : ℤ) = ∑ ρ ∈ S, D ρ := by
          apply Finset.sum_congr rfl
          intro ρ hρ
          rw [hdiv ρ hρ]
      _ ≤ ∑ u ∈ hfin.toFinset, D u :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun u _ _ => hnonneg u)
  calc (∑ ρ ∈ S, (m ρ : ℝ)) = ((∑ ρ ∈ S, (m ρ : ℤ) : ℤ) : ℝ) := by push_cast; rfl
    _ ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by exact_mod_cast hsum_le
    _ ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by exact_mod_cast hjensen

open Metric in
/-- **The peeled function's bounds** (Landau brick L4e): from `f = g·∏(z−ρ)^{m_ρ}` with
    zeros in `B̄(c,r)`, `‖f‖ ≤ Mb` on `B(c,R₁)`, `‖f(c)‖ ≥ ml`: the anchor
    `‖g(c)‖ ≥ ml/r^K` and, by the maximum principle through the `R₂`-sphere (every
    factor `≥ R₂−r` there), the sup `‖g‖ ≤ Mb/(R₂−r)^K` on `B̄(c,R₂)`, `K = Σ m_ρ`. -/
lemma peeled_g_bounds (f g : ℂ → ℂ) (c : ℂ) (R₁ r R₂ Mb ml : ℝ) (S : Finset ℂ)
    (m : ℂ → ℕ) (hr : 0 < r) (hrR₂ : r < R₂) (hR₂R₁ : R₂ < R₁)
    (hfb : ∀ z ∈ ball c R₁, ‖f z‖ ≤ Mb) (hml : 0 < ml) (hmlc : ml ≤ ‖f c‖)
    (hS : ∀ ρ ∈ S, ρ ∈ closedBall c r ∧ f ρ = 0)
    (hgdiff : DifferentiableOn ℂ g (ball c R₁))
    (hfac : ∀ z ∈ ball c R₁, f z = g z * ∏ ρ ∈ S, (z - ρ) ^ (m ρ)) :
    ml / r ^ (∑ ρ ∈ S, m ρ) ≤ ‖g c‖ ∧
    ∀ z ∈ closedBall c R₂, ‖g z‖ ≤ Mb / (R₂ - r) ^ (∑ ρ ∈ S, m ρ) := by
  set K : ℕ := ∑ ρ ∈ S, m ρ with hK
  have hcball : c ∈ ball c R₁ := mem_ball_self (by linarith)
  have hMb0 : 0 ≤ Mb := le_trans (norm_nonneg _) (hfb c hcball)
  have hfc0 : f c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hmlc
    linarith
  have hnorm_eq : ∀ w ∈ ball c R₁, ‖f w‖ = ‖g w‖ * ∏ ρ ∈ S, ‖w - ρ‖ ^ (m ρ) := by
    intro w hw
    rw [hfac w hw, norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl (fun ρ _ => norm_pow _ _)
  constructor
  · -- anchor
    have hcρ : ∀ ρ ∈ S, c ≠ ρ := by
      intro ρ hρ hc
      exact hfc0 (hc ▸ (hS ρ hρ).2)
    have hprod_pos : (0:ℝ) < ∏ ρ ∈ S, ‖c - ρ‖ ^ (m ρ) :=
      Finset.prod_pos (fun ρ hρ =>
        pow_pos (norm_pos_iff.mpr (sub_ne_zero_of_ne (hcρ ρ hρ))) _)
    have hprod_le : ∏ ρ ∈ S, ‖c - ρ‖ ^ (m ρ) ≤ r ^ K := by
      rw [hK, ← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_le_prod₀
      · intro ρ _
        positivity
      · intro ρ hρ
        apply pow_le_pow_left₀ (norm_nonneg _)
        have := (hS ρ hρ).1
        rwa [mem_closedBall, dist_comm, dist_eq_norm] at this
    have hgc_eq : ‖g c‖ = ‖f c‖ / ∏ ρ ∈ S, ‖c - ρ‖ ^ (m ρ) := by
      rw [hnorm_eq c hcball]
      field_simp
    rw [hgc_eq]
    calc ml / r ^ K ≤ ‖f c‖ / r ^ K := by gcongr
      _ ≤ ‖f c‖ / ∏ ρ ∈ S, ‖c - ρ‖ ^ (m ρ) := by
          gcongr
  · -- sup via the maximum principle
    have hRr : (0:ℝ) < R₂ - r := by linarith
    have hRrK : (0:ℝ) < (R₂ - r) ^ K := by positivity
    have hbdry : ∀ w ∈ sphere c R₂, ‖g w‖ ≤ Mb / (R₂ - r) ^ K := by
      intro w hw
      rw [mem_sphere_iff_norm] at hw
      have hwball : w ∈ ball c R₁ := by
        rw [mem_ball, dist_eq_norm, hw]
        linarith
      have hprod_ge : (R₂ - r) ^ K ≤ ∏ ρ ∈ S, ‖w - ρ‖ ^ (m ρ) := by
        rw [hK, ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_le_prod₀
        · intro ρ _
          exact pow_nonneg hRr.le _
        · intro ρ hρ
          apply pow_le_pow_left₀ hRr.le
          have hρr := (hS ρ hρ).1
          rw [mem_closedBall, dist_comm, dist_eq_norm] at hρr
          calc R₂ - r ≤ ‖w - c‖ - ‖c - ρ‖ := by
                rw [hw]
                linarith
            _ ≤ ‖w - ρ‖ := by
                have h1 := norm_add_le (w - ρ) (ρ - c)
                have h2 : (w - ρ) + (ρ - c) = w - c := by ring
                rw [h2] at h1
                have h3 : ‖ρ - c‖ = ‖c - ρ‖ := by rw [norm_sub_rev]
                linarith
      have h1 : ‖g w‖ * (R₂ - r) ^ K ≤ Mb := by
        calc ‖g w‖ * (R₂ - r) ^ K ≤ ‖g w‖ * ∏ ρ ∈ S, ‖w - ρ‖ ^ (m ρ) := by
              gcongr
          _ = ‖f w‖ := (hnorm_eq w hwball).symm
          _ ≤ Mb := hfb w hwball
      exact (le_div_iff₀ hRrK).mpr h1
    intro z hz
    have hR₂0 : R₂ ≠ 0 := by linarith
    have hdccl : DiffContOnCl ℂ g (ball c R₂) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball c hR₂0]
      exact hgdiff.mono (closedBall_subset_ball hR₂R₁)
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdccl
    · intro w hw
      rw [frontier_ball c hR₂0] at hw
      exact hbdry w hw
    · rw [closure_ball c hR₂0]
      exact hz

open Metric in
/-- **The Landau log-derivative lemma** (brick L6, the unconditional assembly): a
    holomorphic `f` on `B(c,R₁)` with `‖f‖ ≤ Mb`, `‖f(c)‖ ≥ ml > 0`, `2R < R₁` has a
    finite multiset of zeros `(S, m)` in `B̄(c,R)` — with true analytic multiplicities —
    such that on the quarter ball, away from the zeros,
    `‖f′/f(z) − Σ_ρ m_ρ/(z−ρ)‖ ≤ 8(log(Mb/ml)+1)/R`. The peel at `R₂ = 2R` makes the
    peeled function's sup/anchor ratio collapse to `Mb/ml`, so no multiplicity count
    enters the remainder. -/
theorem landau_log_deriv (f : ℂ → ℂ) (c : ℂ) (R₁ R Mb ml : ℝ) (hR : 0 < R)
    (hRR : 2 * R < R₁) (hf : DifferentiableOn ℂ f (ball c R₁))
    (hfb : ∀ z ∈ ball c R₁, ‖f z‖ ≤ Mb) (hml : 0 < ml) (hmlc : ml ≤ ‖f c‖) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ S, ρ ∈ closedBall c R ∧ f ρ = 0) ∧
      (∀ ρ ∈ S, m ρ = analyticOrderNatAt f ρ) ∧
      (∀ ρ ∈ closedBall c R, f ρ = 0 → ρ ∈ S) ∧
      ∀ z ∈ ball c (R / 4), (∀ ρ ∈ S, z ≠ ρ) →
        ‖logDeriv f z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖
          ≤ 8 * (Real.log (Mb / ml) + 1) / R := by
  have hRR₁ : R < R₁ := by linarith
  have hfc0 : f c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hmlc
    linarith
  have hfin := zeros_finite_of_ne_center f c R₁ R hR hRR₁ hf hfc0
  obtain ⟨S, m, g, hSz, hm, hgdiff, hgne, hfac⟩ :=
    exists_zero_factorization' c R₁ R hR hRR₁ hfin.toFinset.card f hf hfc0 hfin rfl
  obtain ⟨hanchor, hsup⟩ :=
    peeled_g_bounds f g c R₁ R (2 * R) Mb ml S m hR (by linarith) hRR
      hfb hml hmlc hSz hgdiff hfac
  set K : ℕ := ∑ ρ ∈ S, m ρ with hK
  have hRK : (0:ℝ) < R ^ K := by positivity
  have h2RR : 2 * R - R = R := by ring
  rw [h2RR] at hsup
  have hcomplete : ∀ ρ₀ ∈ closedBall c R, f ρ₀ = 0 → ρ₀ ∈ S := by
    intro ρ₀ hρ₀ hf0
    by_contra hρS
    have hfaceq := hfac ρ₀ ((closedBall_subset_ball hRR₁) hρ₀)
    rw [hf0] at hfaceq
    have hg0 : g ρ₀ ≠ 0 := hgne ρ₀ hρ₀
    have hprod : ∏ ρ ∈ S, (ρ₀ - ρ) ^ (m ρ) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro ρ hρ
      exact pow_ne_zero _ (sub_ne_zero_of_ne (fun hEq => hρS (hEq ▸ hρ)))
    exact (mul_ne_zero hg0 hprod) hfaceq.symm
  refine ⟨S, m, hSz, hm, hcomplete, ?_⟩
  intro z hz hzS
  have hbound := landau_of_factorization f g c R (Mb / R ^ K) (ml / R ^ K) S m hR
    (fun w hw => hfac w (ball_subset_ball hRR₁.le hw))
    (hgdiff.mono (ball_subset_ball hRR₁.le))
    (fun w hw => hgne w (ball_subset_closedBall hw))
    (fun w hw => hsup w (closedBall_subset_closedBall (by linarith)
      (ball_subset_closedBall hw)))
    (by positivity) hanchor z hz hzS
  have hratio : Mb / R ^ K / (ml / R ^ K) = Mb / ml := by
    field_simp
  rwa [hratio] at hbound

open scoped LSeries.notation ArithmeticFunction ArithmeticFunction.Moebius in
/-- **The uniform Euler–Möbius anchor** (SW instantiation brick U1): for EVERY modulus,
    character, and point with `Re s > 1`,
    `‖L(s,χ)‖ ≥ (∑ 1/n^{Re s})⁻¹` — from `L(s,χ)·L(s,χμ) = 1` and the trivial bound
    `‖L(s,χμ)‖ ≤ ∑ 1/n^{Re s}`. The `ml` the Landau lemma normalizes against, uniform
    in `(N, χ, t)` and depending only on `σ = Re s`. -/
lemma LFunction_anchor_euler (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : 1 < s.re) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ s.re)⁻¹ ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  set S : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ s.re with hSdef
  have hmaj : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s.re) :=
    Real.summable_one_div_nat_rpow.mpr hs
  have hS1 : (1:ℝ) ≤ S := by
    have h1 : 1 / ((1:ℕ) : ℝ) ^ s.re = 1 := by norm_num
    calc (1:ℝ) = 1 / ((1:ℕ) : ℝ) ^ s.re := h1.symm
      _ ≤ S := hmaj.le_tsum 1 (fun i _ => by positivity)
  have hS0 : (0:ℝ) < S := by linarith
  have hμsum : LSeriesSummable (↗χ * ↗μ) s :=
    DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  -- the trivial bound on the inverse series
  have hMle : ‖L (↗χ * ↗μ) s‖ ≤ S := by
    calc ‖L (↗χ * ↗μ) s‖ ≤ ∑' n, ‖LSeries.term (↗χ * ↗μ) s n‖ :=
          norm_tsum_le_tsum_norm hμsum.norm
      _ ≤ S := by
          apply hμsum.norm.tsum_mono hmaj
          intro n
          dsimp only
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · simp [LSeries.term_zero]
            positivity
          · rw [LSeries.term_of_ne_zero hn0.ne']
            rw [norm_div, Complex.norm_natCast_cpow_of_pos hn0]
            apply div_le_div_of_nonneg_right _ (Real.rpow_pos_of_pos
              (show (0:ℝ) < (n:ℝ) by exact_mod_cast hn0) s.re).le
            show ‖χ ((n : ZMod N)) * ((μ n : ℤ) : ℂ)‖ ≤ 1
            rw [norm_mul]
            calc ‖χ ((n : ZMod N))‖ * ‖((μ n : ℤ) : ℂ)‖
                ≤ 1 * 1 := by
                  apply mul_le_mul (χ.norm_le_one _) _ (norm_nonneg _) zero_le_one
                  rw [Complex.norm_intCast]
                  exact_mod_cast ArithmeticFunction.abs_moebius_le_one
              _ = 1 := one_mul 1
  -- assemble
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h1 : (1:ℝ) ≤ ‖L ↗χ s‖ * S := by
    calc (1:ℝ) = ‖L ↗χ s * L (↗χ * ↗μ) s‖ := by rw [hmul, norm_one]
      _ = ‖L ↗χ s‖ * ‖L (↗χ * ↗μ) s‖ := norm_mul _ _
      _ ≤ ‖L ↗χ s‖ * S := by
          apply mul_le_mul_of_nonneg_left hMle (norm_nonneg _)
  rw [inv_eq_one_div, div_le_iff₀ hS0]
  linarith

/-- **The explicit zeta-sum bound** (SW instantiation brick U2):
    `∑ 1/n^σ ≤ σ/(σ−1)` for `σ > 1` — integral comparison against `∫ x^{−σ}`.
    Turns the U1 anchor into the uniform quantitative `ml ≥ (σ−1)/σ`. -/
lemma tsum_one_div_nat_rpow_le (σ : ℝ) (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ σ ≤ σ / (σ - 1) := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ1 : σ - 1 ≠ 0 := by linarith
  have hσ1' : (0:ℝ) < σ - 1 := by linarith
  have hmaj : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) :=
    Real.summable_one_div_nat_rpow.mpr hσ
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  rcases Nat.lt_or_ge N 2 with hN | hN
  · -- N = 0 or 1: sum is 0
    interval_cases N
    · simp
      positivity
    · rw [Finset.sum_range_one, Nat.cast_zero, Real.zero_rpow (by linarith), div_zero]
      positivity
  · -- N ≥ 2: peel n = 0, 1 and integral-compare the rest
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 2) hN]
    have hhead : ∑ i ∈ Finset.Ico (0:ℕ) 2, 1 / (i : ℝ) ^ σ = 1 := by
      rw [Nat.Ico_zero_eq_range]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), div_zero, zero_add]
      norm_num
    have htail : ∑ i ∈ Finset.Ico 2 N, 1 / (i : ℝ) ^ σ ≤ 1 / (σ - 1) := by
      have hshift : ∑ i ∈ Finset.Ico 2 N, 1 / (i : ℝ) ^ σ
          = ∑ i ∈ Finset.Ico 1 (N - 1), (fun x : ℝ => x ^ (-σ)) ((i + 1 : ℕ) : ℝ) := by
        rw [show (2:ℕ) = 1 + 1 by rfl, show N = (N - 1) + 1 by omega]
        rw [← Finset.sum_Ico_add]
        apply Finset.sum_congr rfl
        intro i hi
        simp only
        rw [Real.rpow_neg (Nat.cast_nonneg _), inv_eq_one_div]
        congr 2
        push_cast
        ring
      rw [hshift]
      have hab : (1:ℕ) ≤ N - 1 := by omega
      have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc ((1:ℕ):ℝ) ((N-1:ℕ):ℝ)) := by
        intro x hx y hy hxy
        simp only
        have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos (by exact_mod_cast hx.1)
        have hy0 : (0:ℝ) < y := lt_of_lt_of_le hx0 hxy
        rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hx0 σ)
          (Real.rpow_le_rpow hx0.le hxy hσ0.le)
      have hint := AntitoneOn.sum_le_integral_Ico hab hanti
      apply le_trans hint
      have hN1 : ((1:ℕ):ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hab
      have h0mem : (0:ℝ) ∉ Set.uIcc ((1:ℕ):ℝ) ((N-1:ℕ):ℝ) := by
        rw [Set.uIcc_of_le hN1]
        rintro ⟨h0, -⟩
        norm_num at h0
      rw [integral_rpow (Or.inr ⟨by linarith, h0mem⟩)]
      rw [Nat.cast_one, Real.one_rpow]
      have hpow0 : (0:ℝ) ≤ ((N - 1 : ℕ) : ℝ) ^ (-σ + 1) :=
        Real.rpow_nonneg (by linarith) _
      have heq : (((N - 1 : ℕ) : ℝ) ^ (-σ + 1) - 1) / (-σ + 1)
          = (1 - ((N - 1 : ℕ) : ℝ) ^ (-σ + 1)) / (σ - 1) := by
        rw [show (-σ + 1) = -(σ - 1) by ring, div_neg, ← neg_div]
        congr 1
        ring
      rw [heq]
      gcongr
      linarith
    calc ∑ i ∈ Finset.Ico (0:ℕ) 2, 1 / (i : ℝ) ^ σ + ∑ i ∈ Finset.Ico (2:ℕ) N, 1 / (i : ℝ) ^ σ
        ≤ 1 + 1 / (σ - 1) := by
          rw [hhead]
          linarith [htail]
      _ = σ / (σ - 1) := by
          field_simp
          ring

/-- **The quantitative uniform anchor** (SW instantiation brick U3 = U1 ∘ U2): for EVERY
    modulus, character, and `Re s > 1`, `‖L(s,χ)‖ ≥ (Re s − 1)/Re s` — the explicit `ml`
    the Landau lemma takes at the center `σ₀ + it`, uniform in `(N, χ, t)`. -/
lemma LFunction_anchor_quantitative (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (hs : 1 < s.re) :
    (s.re - 1) / s.re ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hσ1' : (0:ℝ) < s.re - 1 := by linarith
  have hσ0 : (0:ℝ) < s.re := by linarith
  have hmaj : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s.re) :=
    Real.summable_one_div_nat_rpow.mpr hs
  have hS1 : (1:ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
    have h1 : 1 / ((1:ℕ) : ℝ) ^ s.re = 1 := by norm_num
    calc (1:ℝ) = 1 / ((1:ℕ) : ℝ) ^ s.re := h1.symm
      _ ≤ _ := hmaj.le_tsum 1 (fun i _ => by positivity)
  have hS0 : (0:ℝ) < ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by linarith
  calc (s.re - 1) / s.re = (s.re / (s.re - 1))⁻¹ := by
        rw [inv_div]
    _ ≤ (∑' n : ℕ, 1 / (n : ℝ) ^ s.re)⁻¹ :=
        inv_anti₀ hS0 (tsum_one_div_nat_rpow_le s.re hs)
    _ ≤ ‖DirichletCharacter.LFunction χ s‖ := LFunction_anchor_euler N χ s hs

open Metric in
/-- **Landau's lemma for Dirichlet L-functions** (SW brick U4): for every modulus `N`,
    nontrivial `χ`, height `t`, and `σ₀ ∈ (1,2]`, the log-derivative of `L(·,χ)` near
    `c = σ₀ + it` is the partial-fraction sum over the zeros in `B̄(c,1/5)` (true
    multiplicities) up to `40(log(N(2|t|+7)·σ₀/(σ₀−1)) + 1)` — the classical
    `−L′/L = Σ_{nearby ρ} 1/(s−ρ) + O(log(N(2+|t|)) + log(1/(σ₀−1)))`, fully explicit
    and uniform in `(N, χ, t)`. -/
theorem landau_LFunction (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (σ₀ t : ℝ) (hσ₀ : 1 < σ₀) (hσ₀2 : σ₀ ≤ 2) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ S, ρ ∈ closedBall ((σ₀ : ℂ) + t * Complex.I) (1/5) ∧
        DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ S, m ρ = analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) ∧
      (∀ ρ ∈ closedBall ((σ₀ : ℂ) + t * Complex.I) (1/5),
        DirichletCharacter.LFunction χ ρ = 0 → ρ ∈ S) ∧
      (∀ ρ ∈ S, 1 ≤ m ρ) ∧
      ∀ z ∈ ball ((σ₀ : ℂ) + t * Complex.I) (1/20), (∀ ρ ∈ S, z ≠ ρ) →
        ‖logDeriv (DirichletCharacter.LFunction χ) z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖
          ≤ 40 * (Real.log ((N : ℝ) * (2 * |t| + 7) * σ₀ / (σ₀ - 1)) + 1) := by
  set c : ℂ := (σ₀ : ℂ) + t * Complex.I with hc
  have hcre : c.re = σ₀ := by
    rw [hc]
    simp
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set Mb : ℝ := (N : ℝ) * (2 * |t| + 7) with hMb
  set ml : ℝ := (σ₀ - 1) / σ₀ with hml_def
  have hml : 0 < ml := div_pos (by linarith) (by linarith)
  have hmlc : ml ≤ ‖DirichletCharacter.LFunction χ c‖ := by
    have := LFunction_anchor_quantitative N χ c (by rw [hcre]; exact hσ₀)
    rwa [hcre] at this
  have hfb : ∀ z ∈ ball c (1/2), ‖DirichletCharacter.LFunction χ z‖ ≤ Mb := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre : (1/2 : ℝ) ≤ z.re := by
      have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      have h2 : |z.re - c.re| < 1/2 := by
        rw [← Complex.sub_re]
        exact lt_of_le_of_lt h1 hz
      have h3 := (abs_lt.mp h2).1
      rw [hcre] at h3
      linarith
    have hnorm : ‖z‖ ≤ |t| + 5/2 := by
      have hcnorm : ‖c‖ ≤ σ₀ + |t| := by
        calc ‖c‖ ≤ ‖(σ₀ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |σ₀| + |t| := by
              rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
              simp [Real.norm_eq_abs]
          _ = σ₀ + |t| := by rw [abs_of_pos (by linarith)]
      calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        _ ≤ (σ₀ + |t|) + 1/2 := by
            apply add_le_add hcnorm hz.le
        _ ≤ |t| + 5/2 := by linarith
    have hw := LFunction_window_bound N χ hχ (1/2) (|t| + 5/2) (by norm_num)
      (by positivity) z hre hnorm
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ (N : ℝ) * (2 + (|t| + 5/2) / (1/2)) := hw
      _ = Mb := by
          rw [hMb]
          ring
  obtain ⟨S, m, hSz, hm, hcomp, hbound⟩ := landau_log_deriv
    (DirichletCharacter.LFunction χ) c (1/2) (1/5) Mb ml (by norm_num) (by norm_num)
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn) hfb hml hmlc
  have hLne : DirichletCharacter.LFunction χ 2 ≠ 0 := by
    have h2 := LFunction_two_lower_uniform N χ hχ
    intro h0
    rw [h0, norm_zero] at h2
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hmpos : ∀ ρ ∈ S, 1 ≤ m ρ := by
    intro ρ hρ
    have hLρ : DirichletCharacter.LFunction χ ρ = 0 := (hSz ρ hρ).2
    have hAnal : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
      (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
    have hordtop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
      intro htop
      have hev := analyticOrderAt_eq_top.mp htop
      have hanalU : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
        fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
      have hzero := hanalU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ ρ) hev
      exact hLne (hzero (Set.mem_univ 2))
    have hordzero : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
      intro h0
      rcases analyticOrderAt_eq_zero.mp h0 with h | h
      · exact h hAnal
      · exact h hLρ
    rw [hm ρ hρ, analyticOrderNatAt]
    apply Nat.one_le_iff_ne_zero.mpr
    intro h0
    rcases ENat.toNat_eq_zero.mp h0 with h | h
    · exact hordzero h
    · exact hordtop h
  refine ⟨S, m, hSz, hm, hcomp, hmpos, ?_⟩
  intro z hz hzS
  have hz' : z ∈ ball c ((1/5) / 4) := by
    rw [show ((1:ℝ)/5) / 4 = 1/20 by norm_num]
    exact hz
  have hb := hbound z hz' hzS
  have hconst : 8 * (Real.log (Mb / ml) + 1) / (1/5)
      = 40 * (Real.log (Mb / ml) + 1) := by ring
  have hratio : Mb / ml = (N : ℝ) * (2 * |t| + 7) * σ₀ / (σ₀ - 1) := by
    rw [hMb, hml_def]
    field_simp
  rw [hconst, hratio] at hb
  exact hb

open Metric ArithmeticFunction in
open scoped LSeries.notation ArithmeticFunction in
/-- **The UNIFORM zero bound** (SW brick U5 — the A₁ ingredient of 3-4-1 with uniform
    constant): a zero `β + iγ` of `L(·,χ)` with `σ − β ≤ 1/5`, `σ ∈ (1,2]`, forces
    `Re L(χΛ, σ+iγ) ≤ 40(log(N(2|γ|+7)σ/(σ−1)) + 1) − 1/(σ−β)` — Landau's partial
    fractions at the center, all other zero terms dropped by positivity. The constant
    is explicit and uniform in `(N, χ, γ, β)`: THE Hadamard-grade input the classical
    zero-free region needs. -/
theorem zero_bound_uniform (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (β γ : ℝ) (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + γ * Complex.I) = 0)
    (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hnear : σ - β ≤ 1/5) :
    (LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * Complex.I)).re
      ≤ 40 * (Real.log ((N : ℝ) * (2 * |γ| + 7) * σ / (σ - 1)) + 1) - 1 / (σ - β) := by
  set c : ℂ := (σ : ℂ) + γ * Complex.I with hc
  set ρ₀ : ℂ := (β : ℂ) + γ * Complex.I with hρ₀def
  have hcre : c.re = σ := by rw [hc]; simp
  have hρ₀re : ρ₀.re = β := by rw [hρ₀def]; simp
  have hcre1 : 1 < c.re := by rw [hcre]; exact hσ1
  -- every zero has Re < 1 (Mathlib nonvanishing on Re ≥ 1)
  have hzlt : ∀ w : ℂ, DirichletCharacter.LFunction χ w = 0 → w.re < 1 := by
    intro w hw
    by_contra hwre
    push_neg at hwre
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hwre hw
  have hβ1 : β < 1 := by
    have := hzlt ρ₀ hzero
    rwa [hρ₀re] at this
  have hβσ : β < σ := by linarith
  have hσβ0 : (0:ℝ) < σ - β := by linarith
  obtain ⟨S, m, hSz, hm, hcomp, hmpos, hbound⟩ := landau_LFunction N χ hχ σ γ hσ1 hσ2
  have hρ₀ball : ρ₀ ∈ closedBall c (1/5) := by
    rw [mem_closedBall, dist_eq_norm]
    have hdiff : ρ₀ - c = ((β - σ : ℝ) : ℂ) := by
      rw [hρ₀def, hc]
      push_cast
      ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hρ₀S : ρ₀ ∈ S := hcomp ρ₀ hρ₀ball hzero
  have hcz : c ∈ ball c (1/20) := mem_ball_self (by norm_num)
  have hzS : ∀ ρ ∈ S, c ≠ ρ := by
    intro ρ hρ hEq
    have hLρ := (hSz ρ hρ).2
    rw [← hEq] at hLρ
    have := hzlt c hLρ
    rw [hcre] at this
    linarith
  have hb := hbound c hcz hzS
  -- real part of each partial-fraction term is nonneg
  have hreS : ∀ ρ ∈ S, 0 ≤ ((m ρ : ℂ) / (c - ρ)).re := by
    intro ρ hρ
    have hρre : ρ.re < 1 := hzlt ρ (hSz ρ hρ).2
    rw [div_eq_mul_inv, show ((m ρ : ℕ) : ℂ) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.inv_re]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg _ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, hcre]
    linarith
  -- the ρ₀ term alone is ≥ 1/(σ−β)
  have hterm : 1 / (σ - β) ≤ ((m ρ₀ : ℂ) / (c - ρ₀)).re := by
    have hdiff : c - ρ₀ = ((σ - β : ℝ) : ℂ) := by
      rw [hρ₀def, hc]
      push_cast
      ring
    rw [hdiff, show ((m ρ₀ : ℕ) : ℂ) = (((m ρ₀ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_div, Complex.ofReal_re]
    gcongr
    exact_mod_cast hmpos ρ₀ hρ₀S
  -- the sum's real part dominates the single ρ₀ term
  have hsum : 1 / (σ - β) ≤ (∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    rw [Complex.re_sum]
    calc 1 / (σ - β) ≤ ((m ρ₀ : ℂ) / (c - ρ₀)).re := hterm
      _ ≤ ∑ ρ ∈ S, ((m ρ : ℂ) / (c - ρ)).re :=
          Finset.single_le_sum hreS hρ₀S
  have hrediff : -(40 * (Real.log ((N : ℝ) * (2 * |γ| + 7) * σ / (σ - 1)) + 1))
      ≤ (logDeriv (DirichletCharacter.LFunction χ) c
          - ∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    have habs := (Complex.abs_re_le_norm _).trans hb
    linarith [(abs_le.mp habs).1]
  have hident : LSeries (↗χ * ↗Λ) c = - logDeriv (DirichletCharacter.LFunction χ) c := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hcre1,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hcre1,
      ← DirichletCharacter.LFunction_eq_LSeries _ hcre1, neg_div, ← logDeriv_apply]
  rw [hident, Complex.neg_re]
  rw [Complex.sub_re] at hrediff
  linarith [hrediff, hsum]

open Metric ArithmeticFunction in
open scoped LSeries.notation ArithmeticFunction in
/-- **The UNIFORM growth bound** (SW brick U6 — the A₂ ingredient of 3-4-1 with uniform
    constant): for every nontrivial `χ`, `σ ∈ (1,2]`, and height `t`,
    `Re L(χΛ, σ+it) ≤ 40(log(N(2|t|+7)σ/(σ−1)) + 1)` — Landau's partial fractions at
    the center with EVERY zero term dropped by positivity. Uniform in `(N, χ, t)`;
    replaces the compactness-per-`(χ,γ)` bound `growth_bound_nontriv`. -/
theorem growth_bound_uniform (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (t σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    (LSeries (↗χ * ↗Λ) ((σ : ℂ) + t * Complex.I)).re
      ≤ 40 * (Real.log ((N : ℝ) * (2 * |t| + 7) * σ / (σ - 1)) + 1) := by
  set c : ℂ := (σ : ℂ) + t * Complex.I with hc
  have hcre : c.re = σ := by rw [hc]; simp
  have hcre1 : 1 < c.re := by rw [hcre]; exact hσ1
  have hzlt : ∀ w : ℂ, DirichletCharacter.LFunction χ w = 0 → w.re < 1 := by
    intro w hw
    by_contra hwre
    push_neg at hwre
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hwre hw
  obtain ⟨S, m, hSz, hm, hcomp, hmpos, hbound⟩ := landau_LFunction N χ hχ σ t hσ1 hσ2
  have hcz : c ∈ ball c (1/20) := mem_ball_self (by norm_num)
  have hzS : ∀ ρ ∈ S, c ≠ ρ := by
    intro ρ hρ hEq
    have hLρ := (hSz ρ hρ).2
    rw [← hEq] at hLρ
    have := hzlt c hLρ
    rw [hcre] at this
    linarith
  have hb := hbound c hcz hzS
  have hreS : ∀ ρ ∈ S, 0 ≤ ((m ρ : ℂ) / (c - ρ)).re := by
    intro ρ hρ
    have hρre : ρ.re < 1 := hzlt ρ (hSz ρ hρ).2
    rw [div_eq_mul_inv, show ((m ρ : ℕ) : ℂ) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.inv_re]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg _ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, hcre]
    linarith
  have hsum : 0 ≤ (∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg hreS
  have hrediff : -(40 * (Real.log ((N : ℝ) * (2 * |t| + 7) * σ / (σ - 1)) + 1))
      ≤ (logDeriv (DirichletCharacter.LFunction χ) c
          - ∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    have habs := (Complex.abs_re_le_norm _).trans hb
    linarith [(abs_le.mp habs).1]
  have hident : LSeries (↗χ * ↗Λ) c = - logDeriv (DirichletCharacter.LFunction χ) c := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hcre1,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hcre1,
      ← DirichletCharacter.LFunction_eq_LSeries _ hcre1, neg_div, ← logDeriv_apply]
  rw [hident, Complex.neg_re]
  rw [Complex.sub_re] at hrediff
  linarith [hrediff, hsum]

/-! ## The 3-4-1 positivity engine (mirrored from DirichletZeroFreeComposed.lean) -/

/-- The 3-4-1 trigonometric inequality: `3 + 4cosθ + cos2θ = 2(1+cosθ)² ≥ 0`.
    Foundation of the classical de la Vallée-Poussin zero-free region (for ζ and L(s,χ)). -/
lemma three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  rw [h]; nlinarith [sq_nonneg (Real.cos θ + 1)]

/-- Complex 3-4-1: for a unit `w = χ(n)·n^{-it}`, `Re(3 + 4w + w²) = 2(Re w + 1)² ≥ 0`.
    This is the term-by-term positivity feeding the log-derivative combination
    `-Re[ 3·(L'/L)(σ,χ₀) + 4·(L'/L)(σ+it,χ) + (L'/L)(σ+2it,χ²) ]`. -/
lemma three_four_one_complex (w : ℂ) (hw : ‖w‖ = 1) :
    0 ≤ (3 + 4 * w + w ^ 2).re := by
  have h1 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h : (w.re * w.re + w.im * w.im : ℝ) = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]; norm_num
    nlinarith [h]
  have h2 : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    rw [sq, Complex.mul_re]; ring
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.re_ofNat,
    Complex.im_ofNat, Complex.ofReal_im, h2]
  nlinarith [sq_nonneg (w.re + 1), h1]

/-- Termwise 3-4-1 for the Dirichlet log-derivative combination: for a coprime `n`,
    `χ⁰(n)=1`, `w₀ = χ(n)` is a unit and `u = n^{-it}` is a unit, so the bracket
    `3·1 + 4·(w₀·u) + (w₀·u)²` (the `n`-th term of `3(L'/L)(σ,χ⁰)+4(L'/L)(σ+it,χ)+(L'/L)(σ+2it,χ²)`
    up to the positive weight `Λ(n)n^{-σ}`) has nonnegative real part. -/
lemma three_four_one_char (w₀ u : ℂ) (h₀ : ‖w₀‖ = 1) (hu : ‖u‖ = 1) :
    0 ≤ (3 + 4 * (w₀ * u) + (w₀ * u) ^ 2).re := by
  apply three_four_one_complex
  rw [norm_mul, h₀, hu, mul_one]

/-- The weighted term stays nonnegative: multiplying by a nonnegative real weight
    (`Λ(n)·n^{-σ} ≥ 0`) preserves the sign. -/
lemma three_four_one_char_weighted (c : ℝ) (hc : 0 ≤ c) (w₀ u : ℂ) (h₀ : ‖w₀‖ = 1)
    (hu : ‖u‖ = 1) : 0 ≤ c * (3 + 4 * (w₀ * u) + (w₀ * u) ^ 2).re :=
  mul_nonneg hc (three_four_one_char w₀ u h₀ hu)

open Complex in
/-- 1c-i: `n^{it}` (equivalently `n^{-it}`) is a unit for `n ≥ 1` — the imaginary exponent
    contributes no modulus. -/
lemma norm_nat_cpow_I (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp [Complex.mul_re, Complex.mul_im]

open Complex in
/-- 1c-ii (the analytic core): the `n`-th term of the 3-4-1 log-derivative combination has
    nonnegative real part. `c0,c1,c2 = χ⁰(n),χ(n),χ²(n)` obey the dichotomy: all zero off the
    coprime set, else `c0=1, ‖c1‖=1, c2=c1²`. -/
lemma term_combination_re_nonneg (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) (c0 c1 c2 : ℂ)
    (hcase : (c0 = 0 ∧ c1 = 0 ∧ c2 = 0) ∨ (c0 = 1 ∧ ‖c1‖ = 1 ∧ c2 = c1 ^ 2)) :
    0 ≤ (3 * (c0 * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ))
       + 4 * (c1 * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I))
       + (c2 * (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + 2 * t * I))).re := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  rcases hcase with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · subst h0 h1 h2; simp
  · subst h0 h2
    have hd1 : (n : ℂ) ^ ((σ : ℂ) + t * I) = (n : ℂ) ^ (σ : ℂ) * (n : ℂ) ^ ((t : ℂ) * I) := by
      rw [← Complex.cpow_add _ _ hn0]
    have hd2 : (n : ℂ) ^ ((σ : ℂ) + 2 * t * I)
        = (n : ℂ) ^ (σ : ℂ) * ((n : ℂ) ^ ((t : ℂ) * I)) ^ 2 := by
      rw [show (σ : ℂ) + 2 * (t : ℂ) * I = (σ : ℂ) + (t : ℂ) * I + (t : ℂ) * I by ring,
        Complex.cpow_add _ _ hn0, Complex.cpow_add _ _ hn0, sq]
      try ring
    rw [hd1, hd2]
    set P : ℂ := (n : ℂ) ^ (σ : ℂ) with hP
    set U : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hU
    set vm : ℝ := ArithmeticFunction.vonMangoldt n with hvm
    have hUnorm : ‖U‖ = 1 := norm_nat_cpow_I n hn t
    have hUne : U ≠ 0 := by
      intro h; rw [h, norm_zero] at hUnorm; norm_num at hUnorm
    have hPreal : P = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [hP, ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (n:ℝ))]
    have hPpos : (0 : ℝ) < (n : ℝ) ^ σ := by positivity
    have hPne : P ≠ 0 := by rw [hPreal]; exact_mod_cast ne_of_gt hPpos
    have key : 3 * ((1 : ℂ) * (vm : ℂ) / P) + 4 * (c1 * (vm : ℂ) / (P * U))
        + c1 ^ 2 * (vm : ℂ) / (P * U ^ 2)
        = (((vm / (n : ℝ) ^ σ : ℝ)) : ℂ) * (3 + 4 * (c1 * U⁻¹) + (c1 * U⁻¹) ^ 2) := by
      rw [hPreal]; push_cast; field_simp; try ring
    rw [key, Complex.re_ofReal_mul]
    apply mul_nonneg
    · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_of_lt hPpos)
    · exact three_four_one_char c1 U⁻¹ h1 (by rw [norm_inv, hUnorm, inv_one])

/-- 1c-iii (character dichotomy): the triple `(χ⁰(n), χ(n), χ²(n))` obeys the dichotomy
    required by `term_combination_re_nonneg`. -/
lemma char_triple_dichotomy {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) :
    (((1 : DirichletCharacter ℂ N) (n : ZMod N) = 0 ∧ χ (n : ZMod N) = 0
        ∧ (χ ^ 2) (n : ZMod N) = 0)
     ∨ ((1 : DirichletCharacter ℂ N) (n : ZMod N) = 1 ∧ ‖χ (n : ZMod N)‖ = 1
        ∧ (χ ^ 2) (n : ZMod N) = (χ (n : ZMod N)) ^ 2)) := by
  by_cases h : IsUnit (n : ZMod N)
  · right
    refine ⟨MulChar.one_apply h, ?_, MulChar.pow_apply' χ (by norm_num) _⟩
    obtain ⟨u, hu⟩ := h
    rw [← hu]; exact χ.unit_norm_eq_one u
  · exact Or.inl ⟨MulChar.map_nonunit _ h, MulChar.map_nonunit _ h, MulChar.map_nonunit _ h⟩

open ArithmeticFunction Complex in
open scoped LSeries.notation ArithmeticFunction in
/-- 1c (assembled): the log-derivative 3-4-1 combination has nonnegative real part for σ>1. -/
lemma logDeriv_combo_re_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (3 * LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)
       + 4 * LSeries (↗χ * ↗Λ) ((σ : ℂ) + t * I)
       + LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * t * I)).re := by
  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + t * I).re := by simp; linarith
  have hs2 : 1 < ((σ : ℂ) + 2 * t * I).re := by simp; linarith
  have S0 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ N) hs0
  have S1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs1
  have S2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) hs2
  simp only [LSeries]
  have H := ((S0.hasSum.mul_left 3).add (S1.hasSum.mul_left 4)).add S2.hasSum
  rw [← H.tsum_eq, re_tsum H.summable]
  apply tsum_nonneg
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [Pi.mul_apply]
    exact term_combination_re_nonneg n (Nat.one_le_iff_ne_zero.mpr hn) σ t _ _ _
      (char_triple_dichotomy χ n)

/-- 1d (assembly): plug the three raw `L'/L` bounds into the 1c combination `0 ≤ 3A₀+4A₁+A₂`
    (where `A₀ = Re L(χ⁰Λ,σ)`, `A₁ = Re L(χΛ,σ+iγ)`, `A₂ = Re L(χ²Λ,σ+2iγ)`) to get the combined
    bound consumed by `zero_free_region_from_bounds`. Reduces all of 1d to the raw bounds:
    (pole) `A₀ ≤ 1/(σ-1)+K`, (zero) `A₁ ≤ K - 1/(σ-β)`, (growth) `A₂ ≤ K`. -/
lemma combined_bound_from_ingredients (β σ K A₀ A₁ A₂ : ℝ)
    (hcombo : 0 ≤ 3 * A₀ + 4 * A₁ + A₂)
    (hpole : A₀ ≤ 1 / (σ - 1) + K) (hzero : A₁ ≤ K - 1 / (σ - β)) (hgrowth : A₂ ≤ K) :
    1 / (σ - β) ≤ 3 / (4 * (σ - 1)) + 2 * K := by
  have hbridge : 3 / 4 * (1 / (σ - 1)) = 3 / (4 * (σ - 1)) := by
    rw [div_mul_div_comm]; norm_num
  linarith [hcombo, hpole, hzero, hgrowth, hbridge]

open ArithmeticFunction Complex in
open scoped LSeries.notation ArithmeticFunction in
/-- **THE UNIFORM ZERO-FREE REGION** (SW brick U7 — de la Vallée-Poussin with an
    absolute constant): there is one `C` such that EVERY zero `β + iγ` of EVERY
    `L(·,χ)` with `χ` nontrivial non-quadratic satisfies
    `β ≤ 1 − 1/(335(1360+C)(log(N(4|γ|+7)) + 20))` — the classical
    `1 − c/log(N(|γ|+2))` region, fully uniform in `(N, χ, γ)`. Composition: the
    positivity engine + uniform pole (twist_re_le_uniform) + uniform zero (U5) +
    uniform growth (U6) at the single point `σ = 1 + 1/(100M)`, where
    `M = 80(log+20) + 20·max(K_P,1) + 24000` a-priori majorizes the Landau constant
    (via `log M ≤ 2√M ≤ M/160`). -/
theorem dvp_zero_free_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ ^ 2 ≠ 1 → ∀ β γ : ℝ,
      DirichletCharacter.LFunction χ ((β : ℂ) + γ * Complex.I) = 0 →
      β ≤ 1 - 1 / (335 * (1360 + C) * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20)) := by
  obtain ⟨KP, hKP⟩ := twist_re_le_uniform
  set KP' : ℝ := max KP 1 with hKP'def
  have hKP'1 : 1 ≤ KP' := le_max_right _ _
  have hKPle : KP ≤ KP' := le_max_left _ _
  refine ⟨KP', hKP'1, ?_⟩
  intro N _ χ hχ hχ2 β γ hzero
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h47 : (0:ℝ) < 4 * |γ| + 7 := by positivity
  have harg1 : (1:ℝ) ≤ (N : ℝ) * (4 * |γ| + 7) := by nlinarith [abs_nonneg γ]
  have hL₀ : 0 ≤ Real.log ((N : ℝ) * (4 * |γ| + 7)) := Real.log_nonneg harg1
  set M : ℝ := 80 * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20) + 20 * KP' + 24000 with hMdef
  have hM25600 : 25600 ≤ M := by rw [hMdef]; nlinarith
  have hM0 : (0:ℝ) < M := by linarith
  set σ : ℝ := 1 + 1 / (100 * M) with hσdef
  have hinv0 : (0:ℝ) < 1 / (100 * M) := by
    apply div_pos one_pos
    linarith
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ0 : (0:ℝ) < σ := by linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσdef]
    have h1 : 1 / (100 * M) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hσ1' : σ - 1 = 1 / (100 * M) := by rw [hσdef]; ring
  have hβ1 : β < 1 := by
    by_contra hβ'
    push_neg at hβ'
    have hre : (1:ℝ) ≤ ((β : ℂ) + γ * Complex.I).re := by simp; linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre hzero
  have hσβ0 : (0:ℝ) < σ - β := by linarith
  -- log M ≤ 2√M and 80√M ≤ M/2
  set sM : ℝ := M ^ ((1:ℝ)/2) with hsMdef
  have hsM0 : 0 ≤ sM := Real.rpow_nonneg hM0.le _
  have hsq : sM ^ (2:ℕ) = M := by
    rw [hsMdef, ← Real.rpow_natCast (M ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hM0.le]
    norm_num
  have h160 : 160 ≤ sM := by nlinarith [hsq, hM25600, hsM0]
  have hlogM : Real.log M ≤ 2 * sM := by
    have h := Real.log_le_rpow_div hM0.le (show (0:ℝ) < 1/2 by norm_num)
    rw [← hsMdef] at h
    linarith
  have h80s : 80 * sM ≤ M / 2 := by nlinarith [hsq, h160, hsM0]
  -- nonzeroness for log_mul
  have hNne : ((N:ℝ)) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hN1)
  have h47ne : (4 * |γ| + 7 : ℝ) ≠ 0 := ne_of_gt h47
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have hMne : M ≠ 0 := ne_of_gt hM0
  -- the a-priori majorant: K_A ≤ M
  have hKA : 40 * (Real.log ((N : ℝ) * (4 * |γ| + 7) * σ / (σ - 1)) + 1) ≤ M := by
    have hlogσ : Real.log σ ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos hσ0
      have hσ1e : σ - 1 ≤ 1 := by
        rw [hσ1', div_le_one (by linarith)]
        linarith
      linarith
    have hlog100 : Real.log 100 ≤ 18 := by
      have h10 : Real.log 10 ≤ 9 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 10 by norm_num)
        linarith
      have h100 : Real.log 100 = Real.log 10 + Real.log 10 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      linarith
    have hsplit : (N : ℝ) * (4 * |γ| + 7) * σ / (σ - 1)
        = (N : ℝ) * (4 * |γ| + 7) * σ * (100 * M) := by
      rw [hσ1', div_eq_mul_inv, one_div, inv_inv]
    rw [hsplit]
    have hlogprod : Real.log ((N : ℝ) * (4 * |γ| + 7) * σ * (100 * M))
        = Real.log ((N : ℝ) * (4 * |γ| + 7)) + Real.log σ
          + (Real.log 100 + Real.log M) := by
      rw [Real.log_mul (mul_ne_zero (mul_ne_zero hNne h47ne) hσne)
          (by norm_num; exact hMne : (100 * M : ℝ) ≠ 0),
        Real.log_mul (mul_ne_zero hNne h47ne) hσne,
        Real.log_mul (by norm_num : (100:ℝ) ≠ 0) hMne]
    rw [hlogprod]
    have hM40 : 80 * Real.log ((N : ℝ) * (4 * |γ| + 7)) + 1600 ≤ M := by
      rw [hMdef]
      nlinarith
    nlinarith [hlogσ, hlog100, hlogM, h80s]
  -- far case: trivially deep
  rcases le_or_gt (σ - β) (1/5) with hnear | hfar
  swap
  · have hsmall : 1 / (100 * M) ≤ (1:ℝ) / 2560000 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    rw [hσdef] at hfar
    have hβfar : β < (0.81 : ℝ) := by linarith
    have hCbig : (10:ℝ) ≤ 335 * (1360 + KP')
        * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20) := by nlinarith
    have hfrac : 1 / (335 * (1360 + KP') * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20))
        ≤ 1/10 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hCbig
    linarith
  -- main case: the 3-4-1 chain at the single σ
  · have hcombo := logDeriv_combo_re_nonneg χ σ γ hσ1
    have hlin : (3 * LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)
         + 4 * LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * I)
         + LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * γ * I)).re
        = 3 * (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re
          + 4 * (LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * I)).re
          + (LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * γ * I)).re := by
      simp [Complex.add_re, Complex.mul_re]
    rw [hlin] at hcombo
    have hpole : (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (σ : ℂ)).re
        ≤ 1 / (σ - 1) + M := by
      have h := hKP N (1 : DirichletCharacter ℂ N) 0 σ hσ1 hσ2
      have hpt : ((σ : ℂ) + ((0:ℝ) : ℂ) * I) = (σ : ℂ) := by push_cast; ring
      rw [hpt] at h
      have hKPM : KP ≤ M := by
        rw [hMdef]
        nlinarith
      linarith
    have hzb := zero_bound_uniform N χ hχ β γ hzero σ hσ1 hσ2 hnear
    have hKU5 : 40 * (Real.log ((N : ℝ) * (2 * |γ| + 7) * σ / (σ - 1)) + 1)
        ≤ 40 * (Real.log ((N : ℝ) * (4 * |γ| + 7) * σ / (σ - 1)) + 1) := by
      have hle : (N : ℝ) * (2 * |γ| + 7) * σ / (σ - 1)
          ≤ (N : ℝ) * (4 * |γ| + 7) * σ / (σ - 1) := by
        apply div_le_div_of_nonneg_right _ (by rw [hσ1']; exact hinv0.le)
        have h1 : (N:ℝ) * (2 * |γ| + 7) ≤ (N:ℝ) * (4 * |γ| + 7) := by
          nlinarith [abs_nonneg γ]
        exact mul_le_mul_of_nonneg_right h1 hσ0.le
      have hpos : (0:ℝ) < (N : ℝ) * (2 * |γ| + 7) * σ / (σ - 1) := by
        rw [hσ1']
        have h27 : (0:ℝ) < (N:ℝ) * (2 * |γ| + 7) := by nlinarith [abs_nonneg γ]
        have := mul_pos h27 hσ0
        exact div_pos this hinv0
      have := Real.log_le_log hpos hle
      linarith
    have hzero' : (LSeries (↗χ * ↗Λ) ((σ : ℂ) + γ * I)).re ≤ M - 1 / (σ - β) := by
      linarith [hzb, hKA, hKU5]
    have hgb := growth_bound_uniform N (χ ^ 2) hχ2 (2 * γ) σ hσ1 hσ2
    have hpt2 : ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) = ((σ : ℂ) + 2 * (γ : ℂ) * I) := by
      push_cast
      ring
    rw [hpt2] at hgb
    have habs2 : (2:ℝ) * |2 * γ| + 7 = 4 * |γ| + 7 := by
      rw [abs_mul, abs_two]
      ring
    rw [habs2] at hgb
    have hgrowth : (LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * γ * I)).re ≤ M := by
      linarith [hKA]
    have hcb := combined_bound_from_ingredients β σ M _ _ _ hcombo hpole hzero' hgrowth
    have h34 : 3 / (4 * (σ - 1)) = 75 * M := by
      rw [hσ1']
      rw [div_eq_iff (by
        have : (0:ℝ) < 4 * (1 / (100 * M)) := by linarith
        exact ne_of_gt this)]
      field_simp
      ring
    rw [h34] at hcb
    have h77 : 1 / (σ - β) ≤ 77 * M := by linarith
    have hgap : 1 / (77 * M) ≤ σ - β := by
      have h77M0 : (0:ℝ) < 77 * M := by linarith
      rw [div_le_iff₀ h77M0]
      rw [div_le_iff₀ hσβ0] at h77
      nlinarith [h77]
    have hβbound : β ≤ 1 - 1 / (335 * M) := by
      have hstep : β ≤ σ - 1 / (77 * M) := by linarith
      rw [hσdef] at hstep
      have e1 : 1 / (100 * M) - 1 / (77 * M) = - (23 / (7700 * M)) := by
        field_simp
        ring
      have e2 : 1 / (335 * M) ≤ 23 / (7700 * M) := by
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 335 * M)
          (by linarith : (0:ℝ) < 7700 * M)]
        nlinarith
      linarith
    have hMC : 335 * M ≤ 335 * (1360 + KP')
        * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20) := by
      rw [hMdef]
      nlinarith [hL₀, hKP'1]
    have hfinal : 1 / (335 * (1360 + KP') * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20))
        ≤ 1 / (335 * M) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hMC
    linarith

section ConjSymmetry
open Finset Filter Metric Topology

/-- Values of a quadratic character lie in `{−1, 0, 1}` (copy of the SiegelTheorem
    brick, needed here for conjugation symmetry). -/
lemma dvp_real_char_repr {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (a : ZMod q) : χ a = -1 ∨ χ a = 0 ∨ χ a = 1 := by
  by_cases hu : IsUnit a
  · have hsq : χ a * χ a = 1 := by
      have h1 : (χ ^ 2) a = 1 := by
        rw [hχ2]
        exact MulChar.one_apply hu
      rw [pow_two, MulChar.mul_apply] at h1
      exact h1
    have hfactor : (χ a - 1) * (χ a + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfactor with h | h
    · right; right
      exact sub_eq_zero.mp h
    · left
      exact eq_neg_of_add_eq_zero_left h
  · right; left
    exact MulChar.map_nonunit χ hu

/-- Quadratic characters are real-valued: conjugation fixes every value. -/
lemma conj_char_val {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (a : ZMod q) : (starRingEnd ℂ) (χ a) = χ a := by
  rcases dvp_real_char_repr χ hχ2 a with h | h | h <;> rw [h] <;> simp

/-- The antiholomorphic square: if `f` is complex-differentiable at `conj z`, then
    `s ↦ conj (f (conj s))` is complex-differentiable at `z` with the conjugated
    derivative. -/
lemma hasDerivAt_conj_conj {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' ((starRingEnd ℂ) z)) :
    HasDerivAt (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s)))
      ((starRingEnd ℂ) f') z := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  have hct : Tendsto (starRingEnd ℂ) (𝓝 z) (𝓝 ((starRingEnd ℂ) z)) :=
    Complex.continuous_conj.continuousAt
  have h1 := hf.comp_tendsto hct
  simp only [Function.comp_def] at h1
  rw [Asymptotics.isLittleO_iff] at h1 ⊢
  intro c hc
  filter_upwards [h1 hc] with x hx
  have he : (starRingEnd ℂ) (f ((starRingEnd ℂ) x)) - (starRingEnd ℂ) (f ((starRingEnd ℂ) z))
      - (x - z) • (starRingEnd ℂ) f'
      = (starRingEnd ℂ) (f ((starRingEnd ℂ) x) - f ((starRingEnd ℂ) z)
          - ((starRingEnd ℂ) x - (starRingEnd ℂ) z) • f') := by
    simp only [map_sub, map_mul, smul_eq_mul, Complex.conj_conj]
  have hn : ‖(starRingEnd ℂ) x - (starRingEnd ℂ) z‖ = ‖x - z‖ := by
    rw [← map_sub, Complex.norm_conj]
  calc ‖(starRingEnd ℂ) (f ((starRingEnd ℂ) x)) - (starRingEnd ℂ) (f ((starRingEnd ℂ) z))
        - (x - z) • (starRingEnd ℂ) f'‖
      = ‖f ((starRingEnd ℂ) x) - f ((starRingEnd ℂ) z)
          - ((starRingEnd ℂ) x - (starRingEnd ℂ) z) • f'‖ := by
        rw [he, Complex.norm_conj]
    _ ≤ c * ‖(starRingEnd ℂ) x - (starRingEnd ℂ) z‖ := hx
    _ = c * ‖x - z‖ := by rw [hn]

/-- On `Re > 1` the conjugation symmetry holds by the Dirichlet series. -/
lemma LFunction_conj_series {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ2 : χ ^ 2 = 1) {w : ℂ} (hw : 1 < w.re) :
    (starRingEnd ℂ) (DirichletCharacter.LFunction χ ((starRingEnd ℂ) w))
      = DirichletCharacter.LFunction χ w := by
  have hwc : 1 < ((starRingEnd ℂ) w).re := by
    rw [Complex.conj_re]
    exact hw
  rw [DirichletCharacter.LFunction_eq_LSeries _ hwc,
    DirichletCharacter.LFunction_eq_LSeries _ hw]
  have hsum : LSeriesSummable (fun n : ℕ => χ ((n : ZMod N))) ((starRingEnd ℂ) w) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hwc
  have h1 : HasSum (fun n : ℕ => LSeries.term (fun n : ℕ => χ ((n : ZMod N)))
      ((starRingEnd ℂ) w) n)
      (LSeries (fun n : ℕ => χ ((n : ZMod N))) ((starRingEnd ℂ) w)) := hsum.hasSum
  have h2 := h1.star
  simp only [Complex.star_def] at h2
  have h3 : (fun n : ℕ => (starRingEnd ℂ)
      (LSeries.term (fun n : ℕ => χ ((n : ZMod N))) ((starRingEnd ℂ) w) n))
      = fun n : ℕ => LSeries.term (fun n : ℕ => χ ((n : ZMod N))) w n := by
    funext n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [LSeries.term]
    · have hn0 : n ≠ 0 := hpos.ne'
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0,
        map_div₀, conj_char_val χ hχ2]
      congr 1
      have harg : ((n : ℂ)).arg ≠ Real.pi := by
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm
      have hcp := Complex.cpow_conj ((n : ℂ)) w harg
      rw [map_natCast] at hcp
      rw [hcp, Complex.conj_conj]
  rw [h3] at h2
  rw [LSeries]
  exact h2.tsum_eq.symm

/-- **Conjugation symmetry of quadratic L-functions** (SW brick S4a-1): for `χ² = 1`,
    `χ ≠ 1`, `L(χ, conj s) = conj (L(χ, s))` everywhere — the coefficients are real,
    and both sides are entire. -/
theorem LFunction_conj_quadratic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction χ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by
  have hLd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ1
  have hgd : Differentiable ℂ (fun w => (starRingEnd ℂ)
      (DirichletCharacter.LFunction χ ((starRingEnd ℂ) w))) := by
    intro z
    exact (hasDerivAt_conj_conj (hLd ((starRingEnd ℂ) z)).hasDerivAt).differentiableAt
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2:ℂ) ∈ {w : ℂ | 1 < w.re} := by
    simp only [Set.mem_setOf_eq]
    norm_num
  have hseed : (fun w => (starRingEnd ℂ)
      (DirichletCharacter.LFunction χ ((starRingEnd ℂ) w)))
      =ᶠ[𝓝 2] DirichletCharacter.LFunction χ := by
    filter_upwards [hU.mem_nhds h2U] with w hw
    exact LFunction_conj_series χ hχ2 hw
  have heq : Set.EqOn (fun w => (starRingEnd ℂ)
      (DirichletCharacter.LFunction χ ((starRingEnd ℂ) w)))
      (DirichletCharacter.LFunction χ) Set.univ :=
    ((hgd.differentiableOn).analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      ((hLd.differentiableOn).analyticOnNhd isOpen_univ)
      isPreconnected_univ (Set.mem_univ 2) hseed
  have hs := heq (Set.mem_univ s)
  simp only at hs
  calc DirichletCharacter.LFunction χ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) ((starRingEnd ℂ)
          (DirichletCharacter.LFunction χ ((starRingEnd ℂ) s))) := (Complex.conj_conj _).symm
    _ = (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by rw [hs]

/-- **Zeros of quadratic L-functions pair by conjugation** (SW brick S4a-1′). -/
theorem conj_zero_quadratic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) {ρ : ℂ}
    (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ ((starRingEnd ℂ) ρ) = 0 := by
  rw [LFunction_conj_quadratic χ hχ2 hχ1 ρ, hz, map_zero]

end ConjSymmetry

open Metric ArithmeticFunction in
open scoped LSeries.notation ArithmeticFunction in
/-- **The conjugate-pair zero bound at the real point** (SW brick S4a-2): if BOTH
    `β ± iγ` are zeros of `L(·,χ)` (γ ≠ 0) close to the real point `σ`, peeling the
    PAIR from Landau's partial fractions doubles the repulsion:
    `Re L(χΛ, σ) ≤ 40(log(7Nσ/(σ−1)) + 1) − 2(σ−β)/((σ−β)² + γ²)`. -/
theorem zero_pair_bound_uniform (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (β γ : ℝ) (hγ : γ ≠ 0)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + γ * Complex.I) = 0)
    (hzero' : DirichletCharacter.LFunction χ ((β : ℂ) - γ * Complex.I) = 0)
    (σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hnear : (σ - β)^2 + γ^2 ≤ 1/25) :
    (LSeries (↗χ * ↗Λ) ((σ : ℂ))).re
      ≤ 40 * (Real.log ((N : ℝ) * 7 * σ / (σ - 1)) + 1)
        - 2 * (σ - β) / ((σ - β)^2 + γ^2) := by
  set c : ℂ := (σ : ℂ) + (0:ℝ) * Complex.I with hc
  have hceq : c = (σ : ℂ) := by rw [hc]; push_cast; ring
  have hcre : c.re = σ := by rw [hceq]; simp
  set ρ₀ : ℂ := (β : ℂ) + γ * Complex.I with hρ₀def
  set ρ₁ : ℂ := (β : ℂ) - γ * Complex.I with hρ₁def
  have hρ₀re : ρ₀.re = β := by rw [hρ₀def]; simp
  have hρ₁re : ρ₁.re = β := by rw [hρ₁def]; simp
  have hρ₀im : ρ₀.im = γ := by rw [hρ₀def]; simp
  have hρ₁im : ρ₁.im = -γ := by rw [hρ₁def]; simp
  have hzlt : ∀ w : ℂ, DirichletCharacter.LFunction χ w = 0 → w.re < 1 := by
    intro w hw
    by_contra hwre
    push_neg at hwre
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hwre hw
  have hβ1 : β < 1 := by
    have := hzlt ρ₀ hzero
    rwa [hρ₀re] at this
  have hσβ0 : (0:ℝ) < σ - β := by linarith
  have hd0 : (0:ℝ) < (σ - β)^2 + γ^2 := by positivity
  obtain ⟨S, m, hSz, hm, hcomp, hmpos, hbound⟩ := landau_LFunction N χ hχ σ 0 hσ1 hσ2
  -- both members of the pair lie in the Landau ball
  have hball : ∀ d : ℝ, d^2 = γ^2 → ((β : ℂ) + (d:ℝ) * Complex.I) ∈ closedBall c (1/5) := by
    intro d hd
    rw [mem_closedBall, dist_eq_norm]
    have hdiff : ((β : ℂ) + (d:ℝ) * Complex.I) - c
        = ((β - σ : ℝ) : ℂ) + (d:ℝ) * Complex.I := by
      rw [hc]; push_cast; ring
    rw [hdiff, Complex.norm_add_mul_I]
    rw [show (β - σ:ℝ)^2 + d^2 = (σ-β)^2 + γ^2 by rw [hd]; ring]
    calc Real.sqrt ((σ-β)^2 + γ^2) ≤ Real.sqrt (1/25) := Real.sqrt_le_sqrt hnear
      _ = 1/5 := by
          rw [show (1/25:ℝ) = (1/5)^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/5)]
  have hρ₀S : ρ₀ ∈ S := hcomp ρ₀ (by rw [hρ₀def]; exact hball γ rfl) hzero
  have hρ₁S : ρ₁ ∈ S := by
    apply hcomp ρ₁ _ hzero'
    have hρ₁eq : ρ₁ = (β : ℂ) + ((-γ : ℝ):ℂ) * Complex.I := by
      rw [hρ₁def]; push_cast; ring
    rw [hρ₁eq]
    exact hball (-γ) (by ring)
  have hne : ρ₀ ≠ ρ₁ := by
    intro h
    have him := congrArg Complex.im h
    rw [hρ₀im, hρ₁im] at him
    exact hγ (by linarith)
  have hcz : c ∈ ball c (1/20) := mem_ball_self (by norm_num)
  have hzS : ∀ ρ ∈ S, c ≠ ρ := by
    intro ρ hρ hEq
    have hLρ := (hSz ρ hρ).2
    rw [← hEq] at hLρ
    have := hzlt c hLρ
    rw [hcre] at this
    linarith
  have hb := hbound c hcz hzS
  -- real part of each partial-fraction term is nonneg
  have hreS : ∀ ρ ∈ S, 0 ≤ ((m ρ : ℂ) / (c - ρ)).re := by
    intro ρ hρ
    have hρre : ρ.re < 1 := hzlt ρ (hSz ρ hρ).2
    rw [div_eq_mul_inv, show ((m ρ : ℕ) : ℂ) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.inv_re]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg _ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, hcre]
    linarith
  -- each pair term is ≥ (σ−β)/((σ−β)²+γ²)
  have hcim : c.im = 0 := by rw [hceq]; simp
  have hterm : ∀ ρ, ρ ∈ S → ρ.re = β → ρ.im ^ 2 = γ^2 →
      (σ - β) / ((σ - β)^2 + γ^2) ≤ ((m ρ : ℂ) / (c - ρ)).re := by
    intro ρ hρS hρre hρim
    have hre_d : (c - ρ).re = σ - β := by rw [Complex.sub_re, hcre, hρre]
    have him_d : (c - ρ).im = -ρ.im := by rw [Complex.sub_im, hcim]; ring
    have hnsq : Complex.normSq (c - ρ) = (σ - β)^2 + γ^2 := by
      rw [Complex.normSq_apply, hre_d, him_d, show (-ρ.im) * (-ρ.im) = ρ.im ^ 2 by ring,
        hρim]
      ring
    have heq : ((m ρ : ℂ) / (c - ρ)).re
        = (m ρ : ℝ) * ((σ - β) / ((σ - β)^2 + γ^2)) := by
      rw [div_eq_mul_inv, show ((m ρ : ℕ) : ℂ) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_ofReal_mul, Complex.inv_re, hre_d, hnsq]
    rw [heq]
    calc (σ - β) / ((σ - β)^2 + γ^2) = 1 * ((σ - β) / ((σ - β)^2 + γ^2)) := (one_mul _).symm
      _ ≤ (m ρ : ℝ) * ((σ - β) / ((σ - β)^2 + γ^2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hmpos ρ hρS
  -- the sum dominates the pair
  have hsum : 2 * (σ - β) / ((σ - β)^2 + γ^2) ≤ (∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    rw [Complex.re_sum]
    have hsub : ({ρ₀, ρ₁} : Finset ℂ) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact hρ₀S
      · rw [Finset.mem_singleton] at h
        rw [h]; exact hρ₁S
    calc 2 * (σ - β) / ((σ - β)^2 + γ^2)
        = (σ - β) / ((σ - β)^2 + γ^2) + (σ - β) / ((σ - β)^2 + γ^2) := by ring
      _ ≤ ((m ρ₀ : ℂ) / (c - ρ₀)).re + ((m ρ₁ : ℂ) / (c - ρ₁)).re :=
          add_le_add (hterm ρ₀ hρ₀S hρ₀re (by rw [hρ₀im]))
            (hterm ρ₁ hρ₁S hρ₁re (by rw [hρ₁im]; ring))
      _ = ∑ ρ ∈ ({ρ₀, ρ₁} : Finset ℂ), ((m ρ : ℂ) / (c - ρ)).re :=
          (Finset.sum_pair (f := fun ρ => ((m ρ : ℂ) / (c - ρ)).re) hne).symm
      _ ≤ ∑ ρ ∈ S, ((m ρ : ℂ) / (c - ρ)).re :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ => hreS ρ hρ)
  have hrediff : -(40 * (Real.log ((N : ℝ) * (2 * |(0:ℝ)| + 7) * σ / (σ - 1)) + 1))
      ≤ (logDeriv (DirichletCharacter.LFunction χ) c
          - ∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    have habs := (Complex.abs_re_le_norm _).trans hb
    linarith [(abs_le.mp habs).1]
  have hcre1 : 1 < c.re := by rw [hcre]; exact hσ1
  have hident : LSeries (↗χ * ↗Λ) c = - logDeriv (DirichletCharacter.LFunction χ) c := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hcre1,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hcre1,
      ← DirichletCharacter.LFunction_eq_LSeries _ hcre1, neg_div, ← logDeriv_apply]
  have habs0 : (N : ℝ) * (2 * |(0:ℝ)| + 7) * σ / (σ - 1) = (N : ℝ) * 7 * σ / (σ - 1) := by
    norm_num
  rw [habs0] at hrediff
  rw [show ((σ:ℝ) : ℂ) = c from hceq.symm, hident, Complex.neg_re]
  rw [Complex.sub_re] at hrediff
  linarith [hrediff, hsum]

open ArithmeticFunction Complex in
open scoped LSeries.notation ArithmeticFunction in
/-- **The 1-1 positivity combo at the real point** (SW brick S4a-3a): for any `χ`,
    `0 ≤ Re(L(χ⁰Λ, σ) + L(χΛ, σ))` for real `σ > 1` — termwise `Λ(n)(1 + Re χ(n)) ≥ 0`.
    The lower comparison feeding the conjugate-pair repulsion. -/
lemma pair_combo_re_nonneg {N : ℕ} (χ : DirichletCharacter ℂ N) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) ((σ : ℂ))
       + LSeries (↗χ * ↗Λ) ((σ : ℂ))).re := by
  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have S0 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ N) hs0
  have S1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs0
  simp only [LSeries]
  have H := S0.hasSum.add S1.hasSum
  rw [← H.tsum_eq, re_tsum H.summable]
  apply tsum_nonneg
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [Pi.mul_apply]
    by_cases h : IsUnit ((n : ZMod N))
    · have h0 : (1 : DirichletCharacter ℂ N) ((n : ZMod N)) = 1 := MulChar.one_apply h
      have h1 : ‖χ ((n : ZMod N))‖ = 1 := by
        obtain ⟨u, hu⟩ := h
        rw [← hu]
        exact χ.unit_norm_eq_one u
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hPreal : (n : ℂ) ^ ((σ:ℝ) : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast n,
          ← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (n:ℝ))]
      have hPpos : (0:ℝ) < (n:ℝ) ^ σ := by
        have hn1 : (0:ℝ) < (n:ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      have key : ((1 : DirichletCharacter ℂ N) ((n : ZMod N)))
            * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ) ^ ((σ:ℝ) : ℂ)
          + (χ ((n : ZMod N))) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
            / (n:ℂ) ^ ((σ:ℝ) : ℂ)
          = (((ArithmeticFunction.vonMangoldt n / (n:ℝ)^σ : ℝ)) : ℂ)
            * (1 + χ ((n : ZMod N))) := by
        rw [h0, hPreal]
        push_cast
        ring
      rw [key, Complex.re_ofReal_mul]
      apply mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hPpos.le)
      have habs := Complex.abs_re_le_norm (χ ((n : ZMod N)))
      rw [h1] at habs
      have h2 := (abs_le.mp habs).1
      rw [Complex.add_re, Complex.one_re]
      linarith
    · rw [MulChar.map_nonunit _ h, MulChar.map_nonunit _ h]
      simp

open scoped LSeries.notation ArithmeticFunction in
/-- **The quadratic small-height zero-free region** (SW brick S4a-3b): there is an
    absolute `C` such that every zero `β + iγ` (γ ≠ 0) of every quadratic nontrivial
    `L(·,χ)` mod `N` with `|γ| ≤ 1/(C·L₀)` (`L₀ = log(N(4|γ|+7))+20`) satisfies
    `β ≤ 1 − 1/(C·L₀)` — the conjugate-pair Landau repulsion at `σ = 1+2(1−β+|γ|)`,
    with the `log(1/x) ≤ 2/√x` a-priori trick closing the self-reference. -/
theorem quad_pair_gap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ β γ : ℝ, γ ≠ 0 →
      DirichletCharacter.LFunction χ ((β : ℂ) + γ * Complex.I) = 0 →
      |γ| * (C * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20)) ≤ 1 →
      β ≤ 1 - 1 / (C * (Real.log ((N : ℝ) * (4 * |γ| + 7)) + 20)) := by
  obtain ⟨K, hK⟩ := twist_re_le_uniform
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = max K 0 := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK'def]; exact le_max_right _ _
  have hKK' : K ≤ K' := by rw [hK'def]; exact le_max_left _ _
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 2 * (576060 * (K'/20 + 40)) + 40 := ⟨_, rfl⟩
  have hC40 : 40 ≤ C := by
    rw [hCdef]
    nlinarith [hK'0]
  refine ⟨C, by linarith, ?_⟩
  intro N _ χ hχ1 hχ2 β γ hγ hzero hsmall
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg0 : (0:ℝ) < |γ| := abs_pos.mpr hγ
  have harg1 : (1:ℝ) ≤ (N:ℝ) * (4*|γ|+7) := by nlinarith
  have hL0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|γ|+7)) := Real.log_nonneg harg1
  obtain ⟨L₀, hL₀def⟩ : ∃ Lv : ℝ, Lv = Real.log ((N:ℝ)*(4*|γ|+7)) + 20 := ⟨_, rfl⟩
  rw [← hL₀def] at hsmall ⊢
  have hL20 : 20 ≤ L₀ := by rw [hL₀def]; linarith
  have hCL : 800 ≤ C * L₀ := by nlinarith
  have hCL0 : 0 < C * L₀ := by linarith
  have hβ1 : β < 1 := by
    by_contra hβ'
    push_neg at hβ'
    have hre : (1:ℝ) ≤ ((β:ℂ) + γ*Complex.I).re := by
      simp
      linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre hzero
  by_cases hb40 : 1/40 ≤ 1 - β
  · have h1 : 1/(C*L₀) ≤ 1/40 := by
      rw [div_le_div_iff₀ hCL0 (by norm_num : (0:ℝ) < 40)]
      linarith
    linarith
  push_neg at hb40
  have hb0 : (0:ℝ) < 1 - β := by linarith
  have hgC : |γ| ≤ 1/(C*L₀) := by
    rw [le_div_iff₀ hCL0]
    exact hsmall
  have hg800 : |γ| ≤ 1/800 := by
    refine le_trans hgC ?_
    rw [div_le_div_iff₀ hCL0 (by norm_num : (0:ℝ) < 800)]
    linarith
  obtain ⟨σ, hσdef⟩ : ∃ s : ℝ, s = 1 + 2*((1-β) + |γ|) := ⟨_, rfl⟩
  have hx0 : (0:ℝ) < (1-β) + |γ| := by linarith
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith [hb40, hg800]
  have hσβ : σ - β = 3*(1-β) + 2*|γ| := by rw [hσdef]; ring
  have hσ1x : σ - 1 = 2*((1-β)+|γ|) := by rw [hσdef]; ring
  -- the conjugate zero
  have hconjpt : (starRingEnd ℂ) ((β:ℂ) + γ*Complex.I) = (β:ℂ) - γ*Complex.I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hzero' : DirichletCharacter.LFunction χ ((β:ℂ) - γ*Complex.I) = 0 := by
    rw [← hconjpt]
    exact conj_zero_quadratic χ hχ2 hχ1 hzero
  -- the pair repulsion
  have hnear : (σ-β)^2 + γ^2 ≤ 1/25 := by
    have h1 : σ - β ≤ 3/40 + 2/800 := by
      rw [hσβ]
      linarith [hb40, hg800]
    have hu0' : (0:ℝ) < σ - β := by rw [hσβ]; linarith
    have h2 : γ^2 ≤ (1/800)^2 := by
      rw [← sq_abs]
      nlinarith [hg800, hg0.le]
    nlinarith [h1, h2, hu0']
  have hpair := zero_pair_bound_uniform N χ hχ1 β γ hγ hzero hzero' σ hσ1 hσ2 hnear
  -- the lower comparison
  have hcombo := pair_combo_re_nonneg χ σ hσ1
  have hA0 := hK N (1 : DirichletCharacter ℂ N) 0 σ hσ1 hσ2
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hA0
  rw [Complex.add_re] at hcombo
  have hchain : 2*(σ-β)/((σ-β)^2+γ^2)
      ≤ 1/(σ-1) + K' + 40*(Real.log ((N:ℝ)*7*σ/(σ-1))+1) := by
    linarith [hpair, hcombo, hA0, hKK']
  -- lower-bound the repulsion by 8/(15x)
  have hu0 : (0:ℝ) < σ - β := by rw [hσβ]; linarith
  have hgu : 2*|γ| ≤ σ - β := by rw [hσβ]; linarith
  have hu3x : σ - β ≤ 3*((1-β)+|γ|) := by rw [hσβ]; linarith
  have hden0 : (0:ℝ) < (σ-β)^2 + γ^2 := by nlinarith [hu0, sq_nonneg γ]
  have hden : (σ-β)^2 + γ^2 ≤ (5/4)*(σ-β)^2 := by
    have h1 : γ^2 = |γ|^2 := (sq_abs γ).symm
    nlinarith [hgu, hg0.le]
  have hLHS1 : 8/(5*(σ-β)) ≤ 2*(σ-β)/((σ-β)^2+γ^2) := by
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 5*(σ-β)) hden0]
    nlinarith [hden]
  have hLHS2 : 8/(15*((1-β)+|γ|)) ≤ 8/(5*(σ-β)) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8) (by linarith : (0:ℝ) < 5*(σ-β))
    linarith [hu3x]
  have hkey : 1/(30*((1-β)+|γ|)) ≤ K' + 40 + 40*Real.log ((N:ℝ)*7*σ/(σ-1)) := by
    have h1 : 8/(15*((1-β)+|γ|)) - 1/(2*((1-β)+|γ|)) = 1/(30*((1-β)+|γ|)) := by
      field_simp
      ring
    have h2 : 1/(σ-1) = 1/(2*((1-β)+|γ|)) := by rw [hσ1x]
    linarith [hLHS1, hLHS2, hchain, h1.le, h1.ge, h2.le, h2.ge]
  -- bound the log: log(7Nσ/(σ−1)) ≤ log(7N) + log(1/x)
  have hlogb : Real.log ((N:ℝ)*7*σ/(σ-1))
      ≤ Real.log (7*(N:ℝ)) + Real.log (1/((1-β)+|γ|)) := by
    have harg0 : (0:ℝ) < (N:ℝ)*7*σ/(σ-1) := by
      apply div_pos (by nlinarith [hN1, hσ1]) (by linarith)
    have hxx : (1/((1-β)+|γ|)) * (2*((1-β)+|γ|)) = 2 := by
      field_simp
    have hle : (N:ℝ)*7*σ/(σ-1) ≤ 7*(N:ℝ) * (1/((1-β)+|γ|)) := by
      rw [hσ1x, div_le_iff₀ (by linarith : (0:ℝ) < 2*((1-β)+|γ|))]
      nlinarith [hσ2, hN1, hxx, hx0]
    calc Real.log ((N:ℝ)*7*σ/(σ-1))
        ≤ Real.log (7*(N:ℝ) * (1/((1-β)+|γ|))) := Real.log_le_log harg0 hle
      _ = Real.log (7*(N:ℝ)) + Real.log (1/((1-β)+|γ|)) :=
          Real.log_mul (by nlinarith [hN1]) (by positivity)
  -- the √-trick
  have hsqrt : Real.log (1/((1-β)+|γ|)) ≤ 2*(1/((1-β)+|γ|))^((1:ℝ)/2) := by
    have h1 := Real.log_le_rpow_div
      (le_of_lt (by positivity : (0:ℝ) < 1/((1-β)+|γ|)))
      (by norm_num : (0:ℝ) < 1/2)
    calc Real.log (1/((1-β)+|γ|)) ≤ (1/((1-β)+|γ|))^((1:ℝ)/2) / (1/2) := h1
      _ = 2*(1/((1-β)+|γ|))^((1:ℝ)/2) := by ring
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (1/((1-β)+|γ|))^((1:ℝ)/2) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have ht2 : t^2 = 1/((1-β)+|γ|) := by
    rw [htdef, ← Real.rpow_natCast ((1/((1-β)+|γ|))^((1:ℝ)/2)) 2,
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1/((1-β)+|γ|))]
    norm_num
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = K' + 40 + 40*Real.log (7*(N:ℝ)) := ⟨_, rfl⟩
  have hD40 : 40 ≤ D := by
    rw [hDdef]
    have h1 : (0:ℝ) ≤ Real.log (7*(N:ℝ)) := Real.log_nonneg (by nlinarith [hN1])
    linarith [hK'0]
  have hquad : t^2 ≤ 30*D + 2400*t := by
    have h1 : 1/(30*((1-β)+|γ|)) = t^2/30 := by
      rw [ht2, div_div]
      ring
    rw [h1] at hkey
    have h3 : Real.log ((N:ℝ)*7*σ/(σ-1)) ≤ Real.log (7*(N:ℝ)) + 2*t := by
      rw [htdef]
      linarith [hlogb, hsqrt]
    have h4 : K' + 40 + 40*Real.log ((N:ℝ)*7*σ/(σ-1)) ≤ D + 80*t := by
      rw [hDdef]
      linarith [h3]
    linarith [hkey, h4]
  have hres : t^2 ≤ 576060*D := by
    by_cases ht48 : t ≤ 4800
    · have h8 : 2400*t ≤ 11520000 := by linarith
      have h9 : (11520000:ℝ) ≤ 288000*D := by linarith [hD40]
      have h10 : (0:ℝ) ≤ D := by linarith [hD40]
      linarith [hquad, h8, h9, h10]
    · push_neg at ht48
      have h8 : 2400*t ≤ t^2/2 := by nlinarith [ht48, ht0]
      have h10 : (0:ℝ) ≤ D := by linarith [hD40]
      linarith [hquad, h8, h10]
  have hDL : D ≤ (K'/20 + 40)*L₀ := by
    rw [hDdef]
    have h1 : Real.log (7*(N:ℝ)) ≤ L₀ - 20 := by
      rw [hL₀def]
      have h2 : 7*(N:ℝ) ≤ (N:ℝ)*(4*|γ|+7) := by nlinarith [hN1, hg0.le]
      have h3 := Real.log_le_log (by nlinarith [hN1] : (0:ℝ) < 7*(N:ℝ)) h2
      linarith
    have h4 : K' ≤ (K'/20)*L₀ := by nlinarith [hK'0, hL20]
    have hexp : (K'/20 + 40)*L₀ = (K'/20)*L₀ + 40*L₀ := by ring
    linarith [h1, h4, hexp.le, hexp.ge, hL20]
  have hxfinal : t^2 ≤ (C/2)*L₀ := by
    have hCC : 576060*(K'/20+40) = (C-40)/2 := by
      rw [hCdef]
      ring
    have h5 : 576060*D ≤ ((C-40)/2)*L₀ := by
      have h9 : 576060*((K'/20+40)*L₀) = ((C-40)/2)*L₀ := by
        rw [← mul_assoc, hCC]
      have h11 := mul_le_mul_of_nonneg_left hDL (by norm_num : (0:ℝ) ≤ 576060)
      linarith [h11, h9.le, h9.ge]
    have h7 : (C/2)*L₀ = ((C-40)/2)*L₀ + 20*L₀ := by ring
    linarith [hres, h5, h7.le, h7.ge, hL20]
  have hxfinal' : 1/((1-β)+|γ|) ≤ (C/2)*L₀ := by
    rw [← ht2]
    exact hxfinal
  have h6 : 1 ≤ ((C/2)*L₀) * ((1-β)+|γ|) := by
    rw [div_le_iff₀ hx0] at hxfinal'
    linarith [hxfinal']
  have h2CL : 2/(C*L₀) ≤ (1-β)+|γ| := by
    rw [div_le_iff₀ hCL0]
    have h10 : (((C/2)*L₀))*((1-β)+|γ|)*2 = ((1-β)+|γ|)*(C*L₀) := by ring
    linarith [h6, h10.le, h10.ge]
  have hsplit : 2/(C*L₀) - 1/(C*L₀) = 1/(C*L₀) := by
    ring
  linarith [h2CL, hgC, hsplit.le, hsplit.ge]

/-- Derivative of `u ↦ (u:ℂ)^c` at positive real `u`. -/
lemma hasDerivAt_real_cpow_const {u : ℝ} (hu : 0 < u) (c : ℂ) :
    HasDerivAt (fun v : ℝ => ((v:ℂ)) ^ c) (c * ((u:ℂ)) ^ (c - 1)) u := by
  have h1 : HasDerivAt (fun z : ℂ => z ^ c) (c * ((u:ℂ)) ^ (c - 1) * 1) ((u:ℂ)) := by
    apply HasDerivAt.cpow_const (hasDerivAt_id ((u:ℂ)))
    exact Complex.ofReal_mem_slitPlane.mpr hu
  rw [mul_one] at h1
  exact h1.comp_ofReal

/-- Inner MVT step: `‖n^{−s} − u^{−s}‖ ≤ ‖s‖·n^{−σ−1}·(u−n)` on `[n, n+1]`. -/
lemma cpow_diff_bound (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hσ : 0 < s.re)
    {u : ℝ} (hu : u ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1)) :
    ‖((n:ℂ)) ^ (-s) - ((u:ℂ)) ^ (-s)‖ ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * (u - (n:ℝ)) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hderiv : ∀ v ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1),
      HasDerivWithinAt (fun w : ℝ => ((w:ℂ)) ^ (-s))
        ((-s) * ((v:ℂ)) ^ (-s - 1)) (Set.Icc ((n:ℝ)) ((n:ℝ)+1)) v := by
    intro v hv
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hn0 hv.1
    exact (hasDerivAt_real_cpow_const hv0 (-s)).hasDerivWithinAt
  have hbound : ∀ v ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1),
      ‖(-s) * ((v:ℂ)) ^ (-s - 1)‖ ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) := by
    intro v hv
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hn0 hv.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hv0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    have hexp : (-s - 1).re = -s.re - 1 := by simp
    rw [hexp]
    exact Real.rpow_le_rpow_of_nonpos hn0 hv.1 (by linarith)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc _ _) (Set.left_mem_Icc.mpr (by linarith)) hu
  have habs : ‖u - (n:ℝ)‖ = u - (n:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    linarith [hu.1]
  calc ‖((n:ℂ)) ^ (-s) - ((u:ℂ)) ^ (-s)‖
      = ‖((u:ℂ)) ^ (-s) - (((n:ℝ):ℂ)) ^ (-s)‖ := by
        rw [← norm_neg]
        congr 1
        push_cast
        ring
    _ ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * ‖u - (n:ℝ)‖ := hmvt
    _ = ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * (u - (n:ℝ)) := by rw [habs]

/-- **The complex Abel kernel bound** (SW brick S4a-4a): for `n ≥ 1` and `Re s > 0`,
    `‖(s−1)n^{−s} − (n^{1−s} − (n+1)^{1−s})‖ ≤ ‖s−1‖·‖s‖·n^{−Re s − 1}` — the
    summand of the ζ-truncation tail, now at COMPLEX `s`. -/
lemma abel_kernel_bound (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hσ : 0 < s.re) :
    ‖(s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s))‖
      ≤ ‖s - 1‖ * ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  -- h(u) := u^{1−s} + (s−1)·u·n^{−s}; K = h(n+1) − h(n)
  have hderiv : ∀ v ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1),
      HasDerivWithinAt (fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s))
        ((s-1) * (((n:ℂ)) ^ (-s) - ((v:ℂ)) ^ (-s))) (Set.Icc ((n:ℝ)) ((n:ℝ)+1)) v := by
    intro v hv
    have hv0 : (0:ℝ) < v := lt_of_lt_of_le hn0 hv.1
    have h1 := hasDerivAt_real_cpow_const hv0 ((1:ℂ) - s)
    have h2 : HasDerivAt (fun w : ℝ => ((w:ℂ))) 1 v := by
      exact (hasDerivAt_id ((v:ℂ))).comp_ofReal
    have h3 : HasDerivAt (fun w : ℝ => (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s))
        ((s-1) * ((n:ℂ)) ^ (-s)) v := by
      have h4 := (h2.const_mul (s-1)).mul_const (((n:ℂ)) ^ (-s))
      have h5 : (s-1) * 1 * ((n:ℂ)) ^ (-s) = (s-1) * ((n:ℂ)) ^ (-s) := by ring
      rw [h5] at h4
      exact h4
    have h6 := h1.add h3
    have h7 : ((1:ℂ) - s) * ((v:ℂ)) ^ ((1:ℂ) - s - 1) + (s-1) * ((n:ℂ)) ^ (-s)
        = (s-1) * (((n:ℂ)) ^ (-s) - ((v:ℂ)) ^ (-s)) := by
      have h8 : (1:ℂ) - s - 1 = -s := by ring
      rw [h8]
      ring
    rw [h7] at h6
    exact h6.hasDerivWithinAt
  have hbound : ∀ v ∈ Set.Icc ((n:ℝ)) ((n:ℝ)+1),
      ‖(s-1) * (((n:ℂ)) ^ (-s) - ((v:ℂ)) ^ (-s))‖ ≤ ‖s-1‖ * (‖s‖ * ((n:ℝ)) ^ (-s.re - 1)) := by
    intro v hv
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc ‖((n:ℂ)) ^ (-s) - ((v:ℂ)) ^ (-s)‖
        ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * (v - (n:ℝ)) := cpow_diff_bound n hn s hσ hv
      _ ≤ ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hv.2]
      _ = ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) := mul_one _
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc _ _) (Set.left_mem_Icc.mpr (by linarith))
    (Set.right_mem_Icc.mpr (by linarith))
  have hcast : (((n+1 : ℕ):ℂ)) = (((((n:ℝ))+1 : ℝ)):ℂ) := by push_cast; ring
  have hK : (fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s)) ((n:ℝ)+1)
      - (fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s)) ((n:ℝ))
      = (s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s)) := by
    simp only
    rw [hcast]
    push_cast
    ring
  have hnorm1 : ‖((n:ℝ)) + 1 - ((n:ℝ))‖ = 1 := by
    rw [show ((n:ℝ)) + 1 - ((n:ℝ)) = 1 by ring, norm_one]
  calc ‖(s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s))‖
      = ‖(fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s)) ((n:ℝ)+1)
        - (fun w : ℝ => ((w:ℂ)) ^ ((1:ℂ) - s) + (s-1) * ((w:ℂ)) * ((n:ℂ)) ^ (-s)) ((n:ℝ))‖ := by
        rw [hK]
    _ ≤ ‖s-1‖ * (‖s‖ * ((n:ℝ)) ^ (-s.re - 1)) * ‖((n:ℝ)) + 1 - ((n:ℝ))‖ := hmvt
    _ = ‖s - 1‖ * ‖s‖ * ((n:ℝ)) ^ (-s.re - 1) := by
        rw [hnorm1, mul_one, mul_assoc]

section ZetaWindow
open Finset Filter Topology Metric

-- verbatim copies from SiegelTheorem.lean (telescope machinery)
lemma tsum_cpow_telescope (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if n < x then 0 else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))
      = ((x:ℂ)) ^ ((1:ℂ) - s) := by
  have hs1 : (0:ℝ) < s.re - 1 := by linarith
  -- partial sums telescope
  have hpartial : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))
      = ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℂ)
            else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  -- the real telescoping majorant
  have hC0 : (0:ℝ) ≤ ‖s - 1‖ / (s.re - 1) := div_nonneg (norm_nonneg _) hs1.le
  have hgmono : ∀ n : ℕ, 1 ≤ n →
      (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)) ≤ ((n : ℝ)) ^ (-(s.re - 1)) := by
    intro n hn1
    apply Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
      (by push_cast; linarith)
    linarith
  -- majorant partial sums telescope
  have hpartialR : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
          - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
      = (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1))) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self, mul_zero]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  -- summability from the kernel bound at s − 1
  have hsummable : Summable (fun n : ℕ => (if n < x then (0:ℂ)
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => if n < x then 0
      else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
        - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
    · -- majorant summable: nonneg terms with telescoping bounded partials
      apply summable_of_sum_range_le (c := ‖s - 1‖ / (s.re - 1))
      · intro n
        rcases Nat.lt_or_ge n x with h | h
        · rw [if_pos h]
        · rw [if_neg (by omega)]
          apply mul_nonneg hC0
          have := hgmono n (le_trans hx h)
          linarith
      · intro z
        rcases Nat.lt_or_ge z x with hz | hz
        · -- every index n < z ≤ x: all terms vanish
          have hall : ∀ n ∈ range z, (if n < x then (0:ℝ)
              else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
                - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_pos (by omega)]
          rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero]
          exact hC0
        · rw [hpartialR z hz]
          have hx1 : ((x:ℝ)) ^ (-(s.re - 1)) ≤ 1 := by
            apply Real.rpow_le_one_of_one_le_of_nonpos
              (by exact_mod_cast hx)
            linarith
          have hz0 : (0:ℝ) ≤ ((z:ℝ)) ^ (-(s.re - 1)) :=
            Real.rpow_nonneg (Nat.cast_nonneg z) _
          calc (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1)))
              ≤ (‖s - 1‖ / (s.re - 1)) * 1 := by
                apply mul_le_mul_of_nonneg_left _ hC0
                linarith
            _ = ‖s - 1‖ / (s.re - 1) := mul_one _
    · intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_pos h, norm_zero]
      · rw [if_neg (by omega), if_neg (by omega)]
        have hn1 : 1 ≤ n := le_trans hx h
        have hker := cpow_diff_kernel_bound n hn1 (s - 1) (by
          simp only [Complex.sub_re, Complex.one_re]
          linarith)
        have he1 : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) ^ (-(s - 1)) := by
          congr 1
          ring
        have he2 : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s) = (((n + 1 : ℕ):ℂ)) ^ (-(s - 1)) := by
          congr 1
          ring
        rw [he1, he2]
        have hre : (s - 1).re = s.re - 1 := by
          simp [Complex.sub_re]
        rw [hre] at hker
        exact hker
  -- conclude: tsum = limit of partials = x^{1−s}
  have hrange := hsummable.hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun z : ℕ => ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s))
      atTop (nhds (((x:ℂ)) ^ ((1:ℂ) - s))) := by
    have hz0 : Tendsto (fun z : ℕ => ((z:ℂ)) ^ ((1:ℂ) - s)) atTop (nhds 0) := by
      have h1s : ((1:ℂ) - s) ≠ 0 := by
        intro hc
        have := congrArg Complex.re hc
        simp at this
        linarith
      have hbnd : ∀ z : ℕ, ‖((z:ℂ)) ^ ((1:ℂ) - s)‖ ≤ ((z:ℝ)) ^ (1 - s.re) := by
        intro z
        rcases Nat.eq_zero_or_pos z with rfl | hzpos
        · simp only [Nat.cast_zero]
          rw [Complex.zero_cpow h1s, norm_zero,
            Real.zero_rpow (by linarith : (1:ℝ) - s.re ≠ 0)]
        · rw [Complex.norm_natCast_cpow_of_pos hzpos]
          have hre1 : ((1:ℂ) - s).re = 1 - s.re := by simp [Complex.sub_re]
          rw [hre1]
      have hg0 : Tendsto (fun z : ℕ => ((z:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
        have h := tendsto_rpow_neg_atTop (show (0:ℝ) < s.re - 1 by linarith)
        have hcomp := h.comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, neg_sub] using hcomp
      exact squeeze_zero_norm hbnd hg0
    have := (tendsto_const_nhds (x := ((x:ℂ)) ^ ((1:ℂ) - s))).sub hz0
    simpa using this
  have heq : (fun z : ℕ => ∑ n ∈ range z, (if n < x then 0
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      =ᶠ[atTop] (fun z : ℕ => ((x:ℂ)) ^ ((1:ℂ) - s) - ((z:ℂ)) ^ ((1:ℂ) - s)) := by
    filter_upwards [eventually_ge_atTop x] with z hz
    exact hpartial z hz
  have hrange' : Tendsto (fun z : ℕ => ∑ n ∈ range z, (if n < x then 0
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      atTop (nhds (((x:ℂ)) ^ ((1:ℂ) - s))) :=
    (Filter.tendsto_congr' heq).mpr hlim
  exact tendsto_nhds_unique hrange hrange'


lemma tsum_cpow_telescope_summable (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (if n < x then (0:ℂ)
      else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
  have hs1 : (0:ℝ) < s.re - 1 := by linarith
  have hC0 : (0:ℝ) ≤ ‖s - 1‖ / (s.re - 1) := div_nonneg (norm_nonneg _) hs1.le
  have hgmono : ∀ n : ℕ, 1 ≤ n →
      (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)) ≤ ((n : ℝ)) ^ (-(s.re - 1)) := by
    intro n hn1
    apply Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
      (by push_cast; linarith)
    linarith
  have hpartialR : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ range z, (if n < x then 0
        else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
          - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
      = (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1))) := by
    intro z
    induction z with
    | zero =>
      intro h0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        have hall : ∀ n ∈ range (m + 1), (if n < m + 1 then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, sub_self, mul_zero]
      · rw [Finset.sum_range_succ, ihm hge, if_neg (by omega)]
        push_cast
        ring
  apply Summable.of_norm_bounded (g := fun n : ℕ => if n < x then 0
    else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
      - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1))))
  · apply summable_of_sum_range_le (c := ‖s - 1‖ / (s.re - 1))
    · intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h]
      · rw [if_neg (by omega)]
        apply mul_nonneg hC0
        have := hgmono n (le_trans hx h)
        linarith
    · intro z
      rcases Nat.lt_or_ge z x with hz | hz
      · have hall : ∀ n ∈ range z, (if n < x then (0:ℝ)
            else (‖s - 1‖ / (s.re - 1)) * (((n : ℝ)) ^ (-(s.re - 1))
              - (((n + 1 : ℕ)) : ℝ) ^ (-(s.re - 1)))) = 0 := by
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos (by omega)]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero]
        exact hC0
      · rw [hpartialR z hz]
        have hx1 : ((x:ℝ)) ^ (-(s.re - 1)) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos
            (by exact_mod_cast hx)
          linarith
        have hz0 : (0:ℝ) ≤ ((z:ℝ)) ^ (-(s.re - 1)) :=
          Real.rpow_nonneg (Nat.cast_nonneg z) _
        calc (‖s - 1‖ / (s.re - 1)) * (((x : ℝ)) ^ (-(s.re - 1)) - ((z : ℝ)) ^ (-(s.re - 1)))
            ≤ (‖s - 1‖ / (s.re - 1)) * 1 := by
              apply mul_le_mul_of_nonneg_left _ hC0
              linarith
          _ = ‖s - 1‖ / (s.re - 1) := mul_one _
  · intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, norm_zero]
    · rw [if_neg (by omega), if_neg (by omega)]
      have hn1 : 1 ≤ n := le_trans hx h
      have hker := cpow_diff_kernel_bound n hn1 (s - 1) (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith)
      have he1 : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) ^ (-(s - 1)) := by
        congr 1
        ring
      have he2 : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s) = (((n + 1 : ℕ):ℂ)) ^ (-(s - 1)) := by
        congr 1
        ring
      rw [he1, he2]
      have hre : (s - 1).re = s.re - 1 := by
        simp [Complex.sub_re]
      rw [hre] at hker
      exact hker

/-- **The completed-zeta ball bound** (SW brick S4a-4b): one absolute `C₀` with
    `‖(z−1)ζ(z)‖ ≤ C₀·R²` (as `LFunctionTrivChar₁ 1`, pole removed) on every ball
    `‖z‖ < R`, `Re z > 19/20` — via the complex Abel truncation tail. -/
theorem completed_zeta_ball_bound :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, 19/20 < z.re → ‖z‖ < R →
      ‖DirichletCharacter.LFunctionTrivChar₁ 1 z‖ ≤ C₀ * R^2 := by
  have hmaj : Summable (fun k : ℕ => (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20)) := by
    have h1 : Summable (fun n : ℕ => ((n:ℝ)) ^ (-(39:ℝ)/20)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    exact h1.comp_injective (add_left_injective 1)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑' k : ℕ, (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact tsum_nonneg (fun k => Real.rpow_nonneg (by positivity) _)
  refine ⟨1 + 3*S, by linarith, ?_⟩
  intro R hR z hzre hznorm
  obtain ⟨T, hTdef⟩ : ∃ T : ℂ → ℂ, T = fun w => ∑' k : ℕ,
      ((w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
        - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w))) := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = {w : ℂ | 19/20 < w.re} ∩ Metric.ball 0 R := ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hterm : ∀ (k : ℕ) (w : ℂ), w ∈ U →
      ‖(w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
        - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w))‖
        ≤ (R+1)*R * (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20) := by
    intro k w hw
    rw [hUdef] at hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [Set.mem_setOf_eq] at hw1
    rw [Metric.mem_ball, dist_zero_right] at hw2
    have h1 := abel_kernel_bound (k+1) (by omega) w (by linarith)
    have h2 : ‖w - 1‖ ≤ R + 1 := by
      calc ‖w - 1‖ ≤ ‖w‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ ≤ R + 1 := by rw [norm_one]; linarith
    have h3 : (((k+1 : ℕ)):ℝ) ^ (-w.re - 1) ≤ (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
      · linarith
    have h4 := mul_le_mul (mul_le_mul h2 hw2.le (norm_nonneg w) (by linarith)) h3
      (Real.rpow_nonneg (by positivity) _) (by positivity)
    linarith [h1, h4]
  have hTnorm : ∀ w ∈ U, ‖T w‖ ≤ (R+1)*R*S := by
    intro w hw
    have hnsum : Summable (fun k : ℕ => ‖(w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
        - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w))‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hterm k w hw)
        (hmaj.mul_left ((R+1)*R))
    simp only [hTdef]
    calc ‖∑' k : ℕ, ((w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
          - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w)))‖
        ≤ ∑' k : ℕ, ‖(w - 1) * ((((k+1 : ℕ)):ℂ)) ^ (-w)
          - (((((k+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w) - ((((k+1+1 : ℕ)):ℂ)) ^ ((1:ℂ) - w))‖ :=
          norm_tsum_le_tsum_norm hnsum
      _ ≤ ∑' k : ℕ, (R+1)*R * (((k+1 : ℕ)):ℝ) ^ (-(39:ℝ)/20) :=
          hnsum.tsum_le_tsum (fun k => hterm k w hw) (hmaj.mul_left ((R+1)*R))
      _ = (R+1)*R*S := by
          rw [hSdef, tsum_mul_left]
  have hTdiff : DifferentiableOn ℂ T U := by
    rw [hTdef]
    apply differentiableOn_tsum_of_summable_norm (hmaj.mul_left ((R+1)*R)) _ hUopen
      (fun k w hw => hterm k w hw)
    intro k
    apply Differentiable.differentiableOn
    have hb1 : ((((k+1 : ℕ)):ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hb2 : ((((k+1+1 : ℕ)):ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact ((differentiable_id.sub_const 1).mul
        (differentiable_id.neg.const_cpow (Or.inl hb1))).sub
      ((((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow (Or.inl hb1)).sub
        (((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow (Or.inl hb2)))
  have hidentity : ∀ s : ℂ, 1 < s.re →
      DirichletCharacter.LFunctionTrivChar₁ 1 s = 1 + T s := by
    intro s hs1
    have hsne : s ≠ 1 := fun h => by
      rw [h, Complex.one_re] at hs1
      exact lt_irrefl _ hs1
    have hs0 : s ≠ 0 := fun h => by
      rw [h, Complex.zero_re] at hs1
      linarith
    have hL : DirichletCharacter.LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hsne,
        DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hsne,
        Nat.primeFactors_one, Finset.prod_empty, one_mul]
    have hζ := zeta_eq_tsum_one_div_nat_cpow hs1
    have hA : Summable (fun n : ℕ => (1:ℂ)/((n:ℂ))^s) :=
      Complex.summable_one_div_nat_cpow.mpr hs1
    have hB := tsum_cpow_telescope_summable 1 (le_refl 1) hs1
    have hAeq : (fun n : ℕ => (if n < 1 then (0:ℂ) else (s - 1) * ((n:ℂ)) ^ (-s)))
        = fun n : ℕ => (s - 1) * ((1:ℂ)/((n:ℂ))^s) := by
      funext n
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp [Complex.zero_cpow hs0]
      · rw [if_neg (by omega), Complex.cpow_neg, one_div]
    have hAsum : Summable (fun n : ℕ =>
        (if n < 1 then (0:ℂ) else (s - 1) * ((n:ℂ)) ^ (-s))) := by
      rw [hAeq]
      exact hA.mul_left _
    have hGeq : (fun n : ℕ =>
        (if n < 1 then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
        = fun n : ℕ => ((if n < 1 then (0:ℂ) else (s - 1) * ((n:ℂ)) ^ (-s))
          - (if n < 1 then (0:ℂ)
            else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
      funext n
      split_ifs
      · ring
      · ring
    have hGsum : Summable (fun n : ℕ =>
        (if n < 1 then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) := by
      rw [hGeq]
      exact hAsum.sub hB
    have hGtsum : ∑' n : ℕ, (if n < 1 then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n+1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
        = (s - 1) * riemannZeta s - 1 := by
      rw [hGeq, hAsum.tsum_sub hB, tsum_cpow_telescope 1 (le_refl 1) hs1, hAeq,
        tsum_mul_left, ← hζ]
      norm_num
    have hshift := hGsum.tsum_eq_zero_add
    have hTG : T s = ∑' k : ℕ, (if k+1 < 1 then (0:ℂ)
        else ((s - 1) * (((k+1 : ℕ):ℂ)) ^ (-s)
          - ((((k+1 : ℕ):ℂ)) ^ ((1:ℂ) - s) - ((((k+1)+1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) := by
      simp only [hTdef]
      first
      | rfl
      | congr 1
      | (congr 1
         funext k
         split_ifs with h
         · exact absurd h (by omega)
         · rfl)
    rw [hL, hTG]
    rw [if_pos (by omega), zero_add] at hshift
    rw [← hshift, hGtsum]
    ring
  have hUconv : Convex ℝ U := by
    rw [hUdef]
    exact (convex_halfSpace_re_gt _).inter (convex_ball 0 R)
  have hg1diff : Differentiable ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) :=
    DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have h1Tdiff : DifferentiableOn ℂ (fun w => 1 + T w) U :=
    (differentiableOn_const 1).add hTdiff
  have hz₀U : ((3/2 : ℝ) : ℂ) ∈ U := by
    rw [hUdef]
    constructor
    · rw [Set.mem_setOf_eq, Complex.ofReal_re]
      norm_num
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)]
      linarith
  have hVopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz₀V : ((3/2 : ℝ) : ℂ) ∈ {w : ℂ | 1 < w.re} := by
    rw [Set.mem_setOf_eq, Complex.ofReal_re]
    norm_num
  have hseed : (fun w => 1 + T w) =ᶠ[nhds ((3/2 : ℝ) : ℂ)]
      (DirichletCharacter.LFunctionTrivChar₁ 1) := by
    filter_upwards [hVopen.mem_nhds hz₀V] with w hw
    exact (hidentity w hw).symm
  have heq : Set.EqOn (fun w => 1 + T w) (DirichletCharacter.LFunctionTrivChar₁ 1) U :=
    (h1Tdiff.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
      ((hg1diff.differentiableOn).analyticOnNhd hUopen)
      hUconv.isPreconnected hz₀U hseed
  have hzU : z ∈ U := by
    rw [hUdef]
    refine ⟨hzre, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact hznorm
  have hval := (heq hzU).symm
  have hfinal : ‖DirichletCharacter.LFunctionTrivChar₁ 1 z‖ ≤ 1 + (R+1)*R*S := by
    rw [hval]
    calc ‖1 + T z‖ ≤ ‖(1:ℂ)‖ + ‖T z‖ := norm_add_le _ _
      _ ≤ 1 + (R+1)*R*S := by
          rw [norm_one]
          linarith [hTnorm z hzU]
  have h6 : (R+1)*R ≤ 3*R^2 := by nlinarith
  have h7 : (R+1)*R*S ≤ 3*R^2*S := mul_le_mul_of_nonneg_right h6 hS0
  have h8 : (1:ℝ) ≤ R^2 := by nlinarith
  calc ‖DirichletCharacter.LFunctionTrivChar₁ 1 z‖ ≤ 1 + (R+1)*R*S := hfinal
    _ ≤ R^2 + 3*S*R^2 := by nlinarith [h7, h8]
    _ = (1 + 3*S) * R^2 := by ring

end ZetaWindow

section TrivCharHeight
open Metric

/-- Norm of a product over prime factors, each factor of norm ≤ 2, is at most `N`. -/
lemma primeFactors_prod_norm_le (N : ℕ) [NeZero N] (g : ℕ → ℂ)
    (hg : ∀ p ∈ N.primeFactors, ‖g p‖ ≤ 2) :
    ‖∏ p ∈ N.primeFactors, g p‖ ≤ (N:ℝ) := by
  calc ‖∏ p ∈ N.primeFactors, g p‖ ≤ ∏ p ∈ N.primeFactors, ‖g p‖ :=
      (norm_prod _ _).le
    _ ≤ ∏ p ∈ N.primeFactors, (2:ℝ) := by
        apply Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) hg
    _ = (2:ℝ) ^ N.primeFactors.card := by
        rw [Finset.prod_const]
    _ ≤ (N:ℝ) := by
        have h1 : (2:ℕ) ^ N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
        have h2 : ∏ p ∈ N.primeFactors, p ≤ N :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (Nat.prod_primeFactors_dvd N)
        have h3 : (2:ℕ) ^ N.primeFactors.card ≤ N := le_trans h1 h2
        calc (2:ℝ) ^ N.primeFactors.card = (((2:ℕ) ^ N.primeFactors.card : ℕ) : ℝ) := by
              push_cast
              ring
          _ ≤ (N:ℝ) := by exact_mod_cast h3

open scoped LSeries.notation ArithmeticFunction in
/-- **The trivial-character Landau bound at height** (SW brick S4a-4c): one absolute
    `C` with, for every modulus and `σ ∈ (1,2]`, every height `t`,
    `Re L(χ⁰Λ, σ+it) ≤ (σ−1)/((σ−1)²+t²) + C(log(N(|t|+3)/(σ−1)) + 1)` — the DAMPED
    pole: Landau on the completed `(s−1)L(χ⁰,s)` (no pole, fixed radius), every zero
    term dropped by positivity. -/
theorem trivchar_height_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N], ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
      (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) ((σ:ℂ) + t*I)).re
        ≤ (σ-1)/((σ-1)^2 + t^2) + C * (Real.log ((N:ℝ)*(|t|+3)/(σ-1)) + 1) := by
  obtain ⟨C₀, hC₀1, hC₀⟩ := completed_zeta_ball_bound
  have hlogC₀ : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀1
  refine ⟨1000*(Real.log C₀ + 4), by linarith, ?_⟩
  intro N _ σ t hσ1 hσ2
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set c : ℂ := (σ:ℂ) + t*I with hcdef
  have hcre : c.re = σ := by rw [hcdef]; simp
  have hcim : c.im = t := by rw [hcdef]; simp
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hcre
    linarith
  have hcnorm : ‖c‖ ≤ σ + |t| := by
    rw [hcdef]
    calc ‖(σ:ℂ) + t*I‖ ≤ ‖(σ:ℂ)‖ + ‖(t:ℂ)*I‖ := norm_add_le _ _
      _ = |σ| + |t| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
          simp [Real.norm_eq_abs]
      _ = σ + |t| := by rw [abs_of_pos (by linarith)]
  -- the ball bound for the completed function
  have hfb : ∀ z ∈ ball c (1/50),
      ‖DirichletCharacter.LFunctionTrivChar₁ N z‖ ≤ (N:ℝ) * (C₀ * (|t|+3)^2) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hzre : 19/20 < z.re := by
      have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      have h2 : |z.re - c.re| < 1/50 := by
        rw [← Complex.sub_re]
        exact lt_of_le_of_lt h1 hz
      have h3 := (abs_lt.mp h2).1
      rw [hcre] at h3
      linarith
    have hznorm : ‖z‖ < |t| + 3 := by
      calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
        _ < (σ + |t|) + 1/50 := by
            apply add_lt_add_of_le_of_lt hcnorm hz
        _ ≤ |t| + 3 := by linarith
    have hR3 : (2:ℝ) ≤ |t| + 3 := by
      have := abs_nonneg t
      linarith
    have hzeta := hC₀ (|t|+3) hR3 z hzre hznorm
    by_cases hz1 : z = 1
    · -- at the removed pole: the update value is the finite Euler product
      subst hz1
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
      have hprod : ‖∏ p ∈ N.primeFactors, (1 - ((p:ℂ))⁻¹)‖ ≤ (N:ℝ) := by
        apply primeFactors_prod_norm_le
        intro p hp
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        calc ‖1 - ((p:ℂ))⁻¹‖ ≤ ‖(1:ℂ)‖ + ‖((p:ℂ))⁻¹‖ := norm_sub_le _ _
          _ = 1 + ((p:ℝ))⁻¹ := by
              rw [norm_one, norm_inv]
              congr 1
              rw [show ((p:ℂ)) = (((p:ℝ)):ℂ) by push_cast; ring, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos (by linarith)]
          _ ≤ 2 := by
              have : ((p:ℝ))⁻¹ ≤ 1 := by
                rw [inv_le_one_iff₀]
                right
                linarith
              linarith
      have hbig : (1:ℝ) ≤ C₀ * (|t|+3)^2 := by
        have h9 : (9:ℝ) ≤ (|t|+3)^2 := by nlinarith [abs_nonneg t]
        nlinarith [hC₀1]
      calc ‖∏ p ∈ N.primeFactors, (1 - ((p:ℂ))⁻¹)‖ ≤ (N:ℝ) := hprod
        _ ≤ (N:ℝ) * (C₀ * (|t|+3)^2) := by nlinarith [hN1r, hbig]
    · -- away from 1: factor through the level-1 completed function
      have hfactor : DirichletCharacter.LFunctionTrivChar₁ N z
          = (∏ p ∈ N.primeFactors, (1 - ((p:ℂ)) ^ (-z)))
            * DirichletCharacter.LFunctionTrivChar₁ 1 z := by
        rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1,
          DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1,
          DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz1,
          DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz1,
          Nat.primeFactors_one, Finset.prod_empty, one_mul]
        ring
      rw [hfactor, norm_mul]
      have hzre0 : (0:ℝ) < z.re := by linarith
      have hprod : ‖∏ p ∈ N.primeFactors, (1 - ((p:ℂ)) ^ (-z))‖ ≤ (N:ℝ) := by
        apply primeFactors_prod_norm_le
        intro p hp
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hp0 : (0:ℝ) < (p:ℝ) := by linarith
        calc ‖1 - ((p:ℂ)) ^ (-z)‖ ≤ ‖(1:ℂ)‖ + ‖((p:ℂ)) ^ (-z)‖ := norm_sub_le _ _
          _ = 1 + ((p:ℝ)) ^ (-z.re) := by
              rw [norm_one, show ((p:ℂ)) = (((p:ℝ)):ℂ) by push_cast; ring,
                Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
          _ ≤ 2 := by
              have h1 : ((p:ℝ)) ^ (-z.re) ≤ 1 :=
                Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
              linarith
      exact mul_le_mul hprod hzeta (norm_nonneg _) (by linarith)
  -- the anchor
  have hcre1 : 1 < c.re := by
    rw [hcre]
    exact hσ1
  have hLne := LFunction_anchor_quantitative N 1 c hcre1
  rw [hcre] at hLne
  have hLpos : (0:ℝ) < (σ - 1)/σ := by
    apply div_pos <;> linarith
  have hml : (σ-1)^2/2 ≤ ‖DirichletCharacter.LFunctionTrivChar₁ N c‖ := by
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hc1]
    have h1 : σ - 1 ≤ ‖c - 1‖ := by
      calc σ - 1 = (c - 1).re := by rw [Complex.sub_re, hcre, Complex.one_re]
        _ ≤ |(c - 1).re| := le_abs_self _
        _ ≤ ‖c - 1‖ := Complex.abs_re_le_norm _
    have h2 : (σ - 1)/σ ≤ ‖DirichletCharacter.LFunctionTrivChar N c‖ := hLne
    have h3 : (σ-1)/2 ≤ (σ-1)/σ := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith)
      linarith
    calc (σ-1)^2/2 = (σ-1) * ((σ-1)/2) := by ring
      _ ≤ ‖c - 1‖ * ‖DirichletCharacter.LFunctionTrivChar N c‖ := by
          apply mul_le_mul h1 (le_trans h3 h2) (by positivity) (norm_nonneg _)
      _ = ‖(c - 1) * DirichletCharacter.LFunctionTrivChar N c‖ := (norm_mul _ _).symm
  have hml0 : (0:ℝ) < (σ-1)^2/2 := by positivity
  -- Landau on the completed function
  obtain ⟨S, m, hSz, hm, hcomp, hbound⟩ := landau_log_deriv
    (DirichletCharacter.LFunctionTrivChar₁ N) c (1/50) (1/125)
    ((N:ℝ) * (C₀ * (|t|+3)^2)) ((σ-1)^2/2) (by norm_num) (by norm_num)
    ((DirichletCharacter.differentiable_LFunctionTrivChar₁ N).differentiableOn) hfb hml0 hml
  have hfc0 : DirichletCharacter.LFunctionTrivChar₁ N c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hml
    nlinarith [hml0]
  have hzS : ∀ ρ ∈ S, c ≠ ρ := by
    intro ρ hρ h
    rw [h] at hfc0
    exact hfc0 (hSz ρ hρ).2
  have hb := hbound c (mem_ball_self (by norm_num)) hzS
  -- every zero term has nonnegative real part
  have hreS : ∀ ρ ∈ S, 0 ≤ ((m ρ : ℂ) / (c - ρ)).re := by
    intro ρ hρ
    have hρz := (hSz ρ hρ).2
    have hρ1 : ρ ≠ 1 := by
      intro h
      rw [h] at hρz
      exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N hρz
    have hLρ : DirichletCharacter.LFunctionTrivChar N ρ = 0 := by
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ1] at hρz
      rcases mul_eq_zero.mp hρz with h | h
      · exact absurd (sub_eq_zero.mp h) hρ1
      · exact h
    have hρre : ρ.re < 1 := by
      by_contra hre
      push_neg at hre
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re
        (1 : DirichletCharacter ℂ N) (Or.inr hρ1) hre hLρ
    rw [div_eq_mul_inv, show ((m ρ : ℕ) : ℂ) = (((m ρ : ℕ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.inv_re]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg _ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, hcre]
    linarith
  -- the log-derivative identity at the center
  have hLcne : DirichletCharacter.LFunctionTrivChar N c ≠ 0 := by
    intro h
    have h' : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) c = 0 := h
    rw [h', norm_zero] at hLne
    nlinarith [hLpos]
  have hld : logDeriv (DirichletCharacter.LFunctionTrivChar₁ N) c
      = 1/(c-1) + logDeriv (DirichletCharacter.LFunctionTrivChar N) c := by
    rw [logDeriv_apply, logDeriv_apply,
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one N hc1,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hc1]
    have hcne : c - 1 ≠ 0 := sub_ne_zero_of_ne hc1
    field_simp
    ring
  -- the twist identity
  have hident : LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) c
      = - logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) c := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hcre1,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hcre1,
      ← DirichletCharacter.LFunction_eq_LSeries _ hcre1, neg_div, ← logDeriv_apply]
  -- assemble
  have hrediff : -(8 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1) / (1/125))
      ≤ (logDeriv (DirichletCharacter.LFunctionTrivChar₁ N) c
          - ∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    have habs := (Complex.abs_re_le_norm _).trans hb
    linarith [(abs_le.mp habs).1]
  have hsum0 : 0 ≤ (∑ ρ ∈ S, (m ρ : ℂ) / (c - ρ)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg hreS
  have hpole : ((1:ℂ)/(c-1)).re = (σ-1)/((σ-1)^2 + t^2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      hcre, hcim, Complex.one_re, Complex.one_im]
    ring
  -- the log arithmetic
  have hA1 : (3:ℝ) ≤ (N:ℝ)*(|t|+3)/(σ-1) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < σ-1)]
    have := abs_nonneg t
    nlinarith
  have hA0 : (0:ℝ) < (N:ℝ)*(|t|+3)/(σ-1) := by linarith
  have hlogA0 : (1:ℝ) ≤ Real.log ((N:ℝ)*(|t|+3)/(σ-1)) := by
    calc (1:ℝ) ≤ Real.log 3 := by
          rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
          apply Real.log_le_log (Real.exp_pos 1)
          have := Real.exp_one_lt_d9
          linarith
      _ ≤ Real.log ((N:ℝ)*(|t|+3)/(σ-1)) := Real.log_le_log (by norm_num) hA1
  have hMbml : (N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)
      ≤ 2*C₀ * ((N:ℝ)*(|t|+3)/(σ-1))^2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (σ-1)^2/2)]
    have hexp : 2*C₀ * ((N:ℝ)*(|t|+3)/(σ-1))^2 * ((σ-1)^2/2)
        = C₀ * (N:ℝ)^2 * (|t|+3)^2 * (((σ-1)/(σ-1))^2) := by
      field_simp
    rw [hexp, div_self (by linarith : σ-1 ≠ 0)]
    have h10 : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith [hN1r]
    have h11 : (0:ℝ) ≤ C₀ * (|t|+3)^2 := by positivity
    nlinarith [h10, h11]
  have hlogMbml : Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2))
      ≤ Real.log 2 + Real.log C₀ + 2 * Real.log ((N:ℝ)*(|t|+3)/(σ-1)) := by
    calc Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2))
        ≤ Real.log (2*C₀ * ((N:ℝ)*(|t|+3)/(σ-1))^2) := by
          apply Real.log_le_log _ hMbml
          have hN0 : (0:ℝ) < (N:ℝ) := by linarith
          exact div_pos (mul_pos hN0 (by positivity)) (by positivity)
      _ = Real.log (2*C₀) + Real.log (((N:ℝ)*(|t|+3)/(σ-1))^2) := by
          rw [Real.log_mul (by nlinarith [hC₀1]) (by positivity)]
      _ = Real.log 2 + Real.log C₀ + 2 * Real.log ((N:ℝ)*(|t|+3)/(σ-1)) := by
          rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow]
          push_cast
          ring
  -- final chain
  have hcore : (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) c).re
      ≤ ((1:ℂ)/(c-1)).re
        + 1000 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1) := by
    rw [hident]
    have h1 : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) c
        = logDeriv (DirichletCharacter.LFunctionTrivChar₁ N) c - 1/(c-1) := by
      have h2 : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) c
          = logDeriv (DirichletCharacter.LFunctionTrivChar N) c := rfl
      rw [h2, hld]
      ring
    rw [h1, Complex.neg_re, Complex.sub_re]
    have h3 := hrediff
    rw [Complex.sub_re] at h3
    have h4 : 8 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1) / (1/125)
        = 1000 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1) := by
      ring
    rw [h4] at h3
    linarith [hsum0, h3]
  rw [hpole] at hcore
  have hfinal : 1000 * (Real.log ((N:ℝ) * (C₀ * (|t|+3)^2) / ((σ-1)^2/2)) + 1)
      ≤ 1000*(Real.log C₀ + 4) * (Real.log ((N:ℝ)*(|t|+3)/(σ-1)) + 1) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      apply Real.log_le_log (by norm_num)
      have := Real.exp_one_gt_d9
      linarith
    have hL := hlogA0
    nlinarith [hlogMbml, hlogC₀, hL, hlog2]
  linarith [hcore, hfinal]

end TrivCharHeight

section Quad341
open Metric
set_option maxHeartbeats 2000000

open scoped LSeries.notation ArithmeticFunction in
/-- **The quadratic 3-4-1 gap away from the real axis** (SW brick S4a-5): for any
    height-threshold parameter `D ≥ 1` there is `C ≥ 1` with: every zero `β+iγ` of
    every quadratic nontrivial `χ` mod `N` with `1 ≤ |γ|·D·L₀` satisfies
    `β ≤ 1 − 1/(C·L₀)` — the classical de la Vallée-Poussin argument, with the
    trivial-character term DAMPED by the height (`trivchar_height_bound`). -/
theorem quad_341_gap (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ β γ : ℝ,
      DirichletCharacter.LFunction χ ((β:ℂ) + γ*Complex.I) = 0 →
      1 ≤ |γ| * (D * (Real.log ((N:ℝ)*(4*|γ|+7)) + 20)) →
      β ≤ 1 - 1/(C * (Real.log ((N:ℝ)*(4*|γ|+7)) + 20)) := by
  obtain ⟨KP, hKP⟩ := twist_re_le_uniform
  obtain ⟨KP', hKP'def⟩ : ∃ K' : ℝ, K' = max KP 0 := ⟨_, rfl⟩
  have hKP'0 : 0 ≤ KP' := by rw [hKP'def]; exact le_max_right _ _
  have hKPle : KP ≤ KP' := by rw [hKP'def]; exact le_max_left _ _
  obtain ⟨C₄, hC₄1, hC₄⟩ := trivchar_height_bound
  obtain ⟨C₉, hC₉def⟩ : ∃ c : ℝ, c = 3*KP' + 320 + 2*C₄ := ⟨_, rfl⟩
  have hC₉1 : 1 ≤ C₉ := by rw [hC₉def]; linarith
  obtain ⟨W, hWdef⟩ : ∃ w : ℝ, w = 4*D*(6400*C₉^2 + 1600*C₉ + 4) := ⟨_, rfl⟩
  have hW16D : 16*D ≤ W := by rw [hWdef]; nlinarith [hC₉1, hD]
  have hW6400 : 6400*C₉^2 ≤ W := by rw [hWdef]; nlinarith [hC₉1, hD]
  have hW2400 : 2400*C₉ ≤ W := by rw [hWdef]; nlinarith [hC₉1, hD]
  have hW1 : 1 ≤ W := by nlinarith [hW2400, hC₉1]
  have hW0 : (0:ℝ) < W := by linarith
  refine ⟨4*W, by linarith, ?_⟩
  intro N _ χ hχ1 hχ2 β γ hzero hbig
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg0 : (0:ℝ) ≤ |γ| := abs_nonneg γ
  have harg1 : (1:ℝ) ≤ (N:ℝ) * (4*|γ|+7) := by nlinarith
  have hL0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|γ|+7)) := Real.log_nonneg harg1
  obtain ⟨L₀, hL₀def⟩ : ∃ Lv : ℝ, Lv = Real.log ((N:ℝ)*(4*|γ|+7)) + 20 := ⟨_, rfl⟩
  rw [← hL₀def] at hbig ⊢
  have hL20 : 20 ≤ L₀ := by rw [hL₀def]; linarith
  have hCL : 4*W*L₀ ≥ 80 := by nlinarith [hW1, hL20]
  have hCL0 : (0:ℝ) < 4*W*L₀ := by linarith
  -- β < 1
  have hβ1 : β < 1 := by
    by_contra hβ'
    push_neg at hβ'
    have hre : (1:ℝ) ≤ ((β:ℂ) + γ*Complex.I).re := by
      simp
      linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre hzero
  -- the sigma
  obtain ⟨d, hddef⟩ : ∃ x : ℝ, x = 1/(W*L₀) := ⟨_, rfl⟩
  have hd0 : (0:ℝ) < d := by
    rw [hddef]
    positivity
  have hdinv : d * (W*L₀) = 1 := by
    rw [hddef]
    field_simp
  have hd20 : d ≤ 1/400 := by
    rw [hddef]
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 400)]
    nlinarith [hW1, hL20]
  have hσ1 : 1 < 1 + d := by linarith
  have hσ2 : 1 + d ≤ 2 := by linarith
  -- the height is large relative to d: |γ| ≥ 4d
  have hγ4d : 4*d ≤ |γ| := by
    have hDL0 : (0:ℝ) < D * L₀ := by nlinarith [hD, hL20]
    have h1 : 1/(D*L₀) ≤ |γ| := by
      rw [div_le_iff₀ hDL0]
      exact hbig
    have h2 : 16*d = 16/(W*L₀) := by
      rw [hddef]
      ring
    have h3 : (16:ℝ)/(W*L₀) ≤ 1/(D*L₀) := by
      rw [div_le_div_iff₀ (by positivity) hDL0]
      have h3a := mul_le_mul_of_nonneg_right hW16D (by linarith : (0:ℝ) ≤ L₀)
      have h3b : 16*D*L₀ = 16*(D*L₀) := by ring
      have h3c : 1*(W*L₀) = W*L₀ := by ring
      linarith [h3a, h3b.le, h3b.ge, h3c.le, h3c.ge]
    linarith [h1, h2.le, h2.ge, h3, hd0]
  have hγ0 : (0:ℝ) < |γ| := by linarith [hγ4d, hd0]
  -- case: far from 1 already
  by_cases hfar : (1 + d) - β ≤ 1/5
  swap
  · push_neg at hfar
    have h1 : 1/(4*W*L₀) ≤ 1/10 := by
      rw [div_le_div_iff₀ hCL0 (by norm_num : (0:ℝ) < 10)]
      linarith
    linarith [hd20]
  -- the main chain
  have hcombo := logDeriv_combo_re_nonneg χ (1+d) γ hσ1
  rw [hχ2] at hcombo
  have hlin : (3 * LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (((1+d : ℝ) : ℂ))
       + 4 * LSeries (↗χ * ↗Λ) ((((1+d : ℝ)) : ℂ) + γ * I)
       + LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) ((((1+d : ℝ)) : ℂ) + 2 * γ * I)).re
      = 3 * (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (((1+d : ℝ) : ℂ))).re
        + 4 * (LSeries (↗χ * ↗Λ) ((((1+d : ℝ)) : ℂ) + γ * I)).re
        + (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) ((((1+d : ℝ)) : ℂ) + 2 * γ * I)).re := by
    simp [Complex.add_re, Complex.mul_re]
  rw [hlin] at hcombo
  -- A0: the pole bound at t = 0
  have hA0 := hKP N (1 : DirichletCharacter ℂ N) 0 (1+d) hσ1 hσ2
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hA0
  -- A1: the zero repulsion
  have hA1 := zero_bound_uniform N χ hχ1 β γ hzero (1+d) hσ1 hσ2 hfar
  -- A2: the damped trivial-character bound at height 2γ
  have hA2 := hC₄ N (1+d) (2*γ) hσ1 hσ2
  have harg : ((((1+d : ℝ)) : ℂ) + 2 * γ * I) = ((((1+d : ℝ)) : ℂ) + ((2*γ : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [harg] at hcombo
  -- clean σ − 1 = d
  have hs1 : (1 + d) - 1 = d := by ring
  rw [hs1] at hA0 hA1 hA2
  -- damping: d/(d² + (2γ)²) ≤ (1/64)/d
  have hdamp : d/(d^2 + (2*γ)^2) ≤ 1/(64*d) := by
    have h1 : (64:ℝ)*d^2 ≤ (2*γ)^2 := by
      have h2 : (4*d)^2 ≤ γ^2 := by
        have := sq_abs γ
        nlinarith [hγ4d, hd0]
      nlinarith [h2]
    rw [div_le_div_iff₀ (by positivity) (by positivity : (0:ℝ) < 64*d)]
    nlinarith [h1, sq_nonneg d, hd0]
  -- the log bounds
  have hd1 : (1:ℝ) ≤ 1/d := by
    rw [le_div_iff₀ hd0]
    linarith [hd20]
  have hdW : 1/d = W*L₀ := by
    rw [hddef]
    field_simp
  have hlogd : Real.log (1/d) ≤ Real.log W + L₀ := by
    rw [hdW, Real.log_mul (by linarith) (by linarith)]
    have h1 : Real.log L₀ ≤ L₀ - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  -- log(N(2|γ|+7)(1+d)/d) ≤ L₀ + log(1/d)
  have hlog1 : Real.log ((N:ℝ)*(2*|γ|+7)*(1+d)/d) ≤ L₀ + Real.log (1/d) := by
    have h1 : (N:ℝ)*(2*|γ|+7)*(1+d)/d ≤ ((N:ℝ)*(4*|γ|+7)) * (1/d) := by
      rw [div_le_iff₀ hd0]
      have h3 : (2*|γ|+7)*d ≤ 2*|γ| := by
        have h3a : |γ| * d ≤ |γ| * (1/400) := mul_le_mul_of_nonneg_left hd20 hg0
        nlinarith [hγ4d, hd0, hg0, h3a]
      have h5 : (2*|γ|+7)*(1+d) ≤ 4*|γ|+7 := by nlinarith [h3]
      have h2 : (N:ℝ)*((2*|γ|+7)*(1+d)) ≤ (N:ℝ)*(4*|γ|+7) :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      have h4 : (1/d) * d = 1 := by field_simp
      calc (N:ℝ)*(2*|γ|+7)*(1+d) = (N:ℝ)*((2*|γ|+7)*(1+d)) := by ring
        _ ≤ (N:ℝ)*(4*|γ|+7) := h2
        _ = ((N:ℝ)*(4*|γ|+7)) * ((1/d)*d) := by rw [h4, mul_one]
        _ = ((N:ℝ)*(4*|γ|+7)) * (1/d) * d := by ring
    calc Real.log ((N:ℝ)*(2*|γ|+7)*(1+d)/d)
        ≤ Real.log (((N:ℝ)*(4*|γ|+7)) * (1/d)) := by
          apply Real.log_le_log _ h1
          apply div_pos (by nlinarith [hN1r, hg0, hd0]) hd0
      _ = Real.log ((N:ℝ)*(4*|γ|+7)) + Real.log (1/d) := by
          rw [Real.log_mul (by nlinarith [hN1r, hg0]) (by linarith)]
      _ ≤ L₀ + Real.log (1/d) := by
          rw [hL₀def]
          linarith
  -- log(N(|2γ|+3)/d) ≤ L₀ + log(1/d)
  have hlog2 : Real.log ((N:ℝ)*(|2*γ|+3)/d) ≤ L₀ + Real.log (1/d) := by
    have habs2 : |2*γ| = 2*|γ| := by
      rw [abs_mul]
      norm_num
    have h1 : (N:ℝ)*(|2*γ|+3)/d ≤ ((N:ℝ)*(4*|γ|+7)) * (1/d) := by
      rw [habs2, div_le_iff₀ hd0, mul_assoc, mul_comm (1/d) d, ← mul_assoc]
      have h4 : d * (1/d) = 1 := by field_simp
      nlinarith [hN1r, hg0, h4]
    calc Real.log ((N:ℝ)*(|2*γ|+3)/d)
        ≤ Real.log (((N:ℝ)*(4*|γ|+7)) * (1/d)) := by
          apply Real.log_le_log _ h1
          apply div_pos (by nlinarith [hN1r, abs_nonneg (2*γ)]) hd0
      _ = Real.log ((N:ℝ)*(4*|γ|+7)) + Real.log (1/d) := by
          rw [Real.log_mul (by nlinarith [hN1r, hg0]) (by linarith)]
      _ ≤ L₀ + Real.log (1/d) := by
          rw [hL₀def]
          linarith
  -- the √-trick on W
  obtain ⟨sW, hsWdef⟩ : ∃ s : ℝ, s = W^((1:ℝ)/2) := ⟨_, rfl⟩
  have hsW0 : 0 ≤ sW := by rw [hsWdef]; positivity
  have hsW2 : sW^2 = W := by
    rw [hsWdef, ← Real.rpow_natCast (W^((1:ℝ)/2)) 2, ← Real.rpow_mul hW0.le]
    norm_num
  have hlogW : Real.log W ≤ 2*sW := by
    have h1 := Real.log_le_rpow_div hW0.le (by norm_num : (0:ℝ) < 1/2)
    calc Real.log W ≤ W^((1:ℝ)/2)/(1/2) := h1
      _ = 2*W^((1:ℝ)/2) := by ring
      _ = 2*sW := by rw [hsWdef]
  have hsW80 : 80*C₉ ≤ sW := by
    by_contra hcon
    push_neg at hcon
    have h0c : (0:ℝ) ≤ 80*C₉ := by linarith
    have h1 : sW*sW < (80*C₉)*(80*C₉) := mul_lt_mul'' hcon hcon hsW0 hsW0
    have h2 : sW*sW = W := by rw [← pow_two]; exact hsW2
    have h3 : (80*C₉)*(80*C₉) = 6400*C₉^2 := by ring
    linarith [h1, h2.le, h2.ge, h3.le, h3.ge, hW6400]
  -- assemble the extras: C₉·(2L₀ + log(1/d)) ≤ (1/400)·(1/d)
  have hextra : C₉ * (2*L₀ + Real.log (1/d)) ≤ (1/400) * (W*L₀) := by
    have h1 : Real.log (1/d) ≤ 2*sW + L₀ := by linarith [hlogd, hlogW]
    have h2 : C₉ * (2*L₀ + Real.log (1/d)) ≤ C₉*(3*L₀ + 2*sW) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ C₉)
      linarith [h1]
    have h3 : C₉*(3*L₀) ≤ (1/800)*(W*L₀) := by
      have h3a := mul_le_mul_of_nonneg_right hW2400 (by linarith : (0:ℝ) ≤ L₀)
      have h3b : 2400*C₉*L₀ = 800*(C₉*(3*L₀)) := by ring
      have h3c : W*L₀ = 800*((1/800)*(W*L₀)) := by ring
      linarith [h3a, h3b.le, h3b.ge, h3c.le, h3c.ge]
    have h4 : C₉*(2*sW) ≤ (1/800)*(W*L₀) := by
      have h5a := mul_le_mul_of_nonneg_right hsW80 hsW0
      have h5b : sW*sW = W := by rw [← pow_two]; exact hsW2
      have h5 : 2*C₉*sW ≤ W/40 := by linarith [h5a, h5b.le, h5b.ge]
      have h6a := mul_le_mul_of_nonneg_left hL20 (by linarith : (0:ℝ) ≤ W)
      have h6b : W*20 = 800*(W/40) := by ring
      have h6c : W*L₀ = 800*((1/800)*(W*L₀)) := by ring
      linarith [h5, h6a, h6b.le, h6b.ge, h6c.le, h6c.ge]
    linarith [h2, h3, h4]
  -- generalize the three atoms to opaque reals
  obtain ⟨A₀v, hA₀v⟩ : ∃ x : ℝ,
      x = (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ) (((1+d : ℝ) : ℂ))).re := ⟨_, rfl⟩
  obtain ⟨A₁v, hA₁v⟩ : ∃ x : ℝ,
      x = (LSeries (↗χ * ↗Λ) ((((1+d : ℝ)) : ℂ) + γ * I)).re := ⟨_, rfl⟩
  obtain ⟨A₂v, hA₂v⟩ : ∃ x : ℝ,
      x = (LSeries (↗(1 : DirichletCharacter ℂ N) * ↗Λ)
        ((((1+d : ℝ)) : ℂ) + ((2*γ : ℝ) : ℂ) * I)).re := ⟨_, rfl⟩
  rw [← hA₀v, ← hA₁v, ← hA₂v] at hcombo
  rw [← hA₀v] at hA0
  rw [← hA₁v] at hA1
  rw [← hA₂v] at hA2
  -- the master chain
  have hchain : 4/((1+d) - β)
      ≤ 3/d + 1/(64*d) + (3*KP' + 320 + 2*C₄)
        + (160 + C₄) * (L₀ + Real.log (1/d)) := by
    have e1 : 3 * A₀v ≤ 3/d + 3*KP' := by
      have b1 : 3/d = 3*(1/d) := by ring
      linarith only [hA0, hKPle, b1]
    have e2 : 4 * A₁v ≤ 160 * (L₀ + Real.log (1/d)) + 160 - 4/((1+d) - β) := by
      have b2 : 4/((1+d) - β) = 4*(1/((1+d) - β)) := by ring
      linarith only [hA1, hlog1, b2]
    have e3 : A₂v ≤ 1/(64*d) + C₄ * (L₀ + Real.log (1/d)) + C₄ := by
      have h9 := mul_le_mul_of_nonneg_left hlog2 (by linarith : (0:ℝ) ≤ C₄)
      linarith only [hA2, hdamp, h9]
    linarith only [hcombo, e1, e2, e3, hC₄1, hKP'0]
  -- numeric close: 4/((1+d)−β) ≤ (31/10)/d
  have hclose : 4/((1+d) - β) ≤ (31/10)/d := by
    have h1 : (3*KP' + 320 + 2*C₄) + (160 + C₄) * (L₀ + Real.log (1/d))
        ≤ C₉ * (2*L₀ + Real.log (1/d)) := by
      have h2 : (0:ℝ) ≤ Real.log (1/d) := Real.log_nonneg hd1
      rw [hC₉def]
      have hb1 := mul_le_mul_of_nonneg_left hL20
        (by linarith : (0:ℝ) ≤ 3*KP' + 320 + 2*C₄)
      nlinarith [hL20, hKP'0, hC₄1, h2, hb1]
    have h3 : C₉ * (2*L₀ + Real.log (1/d)) ≤ (1/400)*(1/d) := by
      have h3a : (1/400)*(W*L₀) = (1/400)*(1/d) := by rw [hdW]
      linarith [hextra, h3a.le, h3a.ge]
    have h4 : 1/(64*d) = (1/64)*(1/d) := by
      rw [div_eq_mul_inv, mul_inv]
      ring
    have h5 : 3/d = 3*(1/d) := by ring
    have h6 : (31/10)/d = (31/10)*(1/d) := by ring
    have h8 : (0:ℝ) < 1/d := by positivity
    have h9 : 3*(1/d) + (1/64)*(1/d) + (1/400)*(1/d) ≤ (31/10)*(1/d) := by
      have h9a : (0:ℝ) ≤ ((31:ℝ)/10 - 3 - 1/64 - 1/400) * (1/d) := by positivity
      linarith [h9a]
    linarith [hchain, h1, h3, h4.le, h4.ge, h5.le, h5.ge, h6.le, h6.ge, h9]
  -- extract the gap
  have hσβ0 : (0:ℝ) < (1+d) - β := by linarith
  have hgap : (40/31)*d ≤ (1+d) - β := by
    rw [div_le_div_iff₀ hσβ0 hd0] at hclose
    linarith [hclose]
  have hfinal : 1/(4*W*L₀) ≤ 1 - β := by
    have h1 : d/4 ≤ 1 - β := by nlinarith [hgap, hd0]
    have h2 : 1/(4*W*L₀) = d/4 := by
      rw [hddef, div_div]
      congr 1
      ring
    linarith [h2.le, h2.ge, h1]
  linarith [hfinal]

end Quad341

/-- **THE UNIFORM ZERO-FREE REGION FOR QUADRATIC CHARACTERS OFF THE REAL AXIS**
    (SW brick S4a-6): one absolute `C` with: every zero `β + iγ`, `γ ≠ 0`, of every
    quadratic nontrivial `χ` mod `N` satisfies
    `β ≤ 1 − 1/(C(log(N(4|γ|+7)) + 20))` — the conjugate-pair repulsion for small
    `|γ|`, the damped 3-4-1 for the rest. Only REAL zeros (Siegel) remain. -/
theorem dvp_zero_free_uniform_quadratic :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ β γ : ℝ, γ ≠ 0 →
      DirichletCharacter.LFunction χ ((β:ℂ) + γ*Complex.I) = 0 →
      β ≤ 1 - 1/(C * (Real.log ((N:ℝ)*(4*|γ|+7)) + 20)) := by
  obtain ⟨Cp, hCp1, hCp⟩ := quad_pair_gap
  obtain ⟨Cq, hCq1, hCq⟩ := quad_341_gap Cp hCp1
  refine ⟨max Cp Cq, le_trans hCp1 (le_max_left _ _), ?_⟩
  intro N _ χ hχ1 hχ2 β γ hγ hzero
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hg0 : (0:ℝ) ≤ |γ| := abs_nonneg γ
  have harg1 : (1:ℝ) ≤ (N:ℝ) * (4*|γ|+7) := by nlinarith
  have hL0 : (0:ℝ) ≤ Real.log ((N:ℝ)*(4*|γ|+7)) := Real.log_nonneg harg1
  obtain ⟨L₀, hL₀def⟩ : ∃ Lv : ℝ, Lv = Real.log ((N:ℝ)*(4*|γ|+7)) + 20 := ⟨_, rfl⟩
  rw [← hL₀def] at ⊢
  have hL20 : 20 ≤ L₀ := by rw [hL₀def]; linarith
  have hmono : ∀ Cbr : ℝ, 1 ≤ Cbr → Cbr ≤ max Cp Cq →
      1/(max Cp Cq * L₀) ≤ 1/(Cbr * L₀) := by
    intro Cbr hCbr1 hCbrle
    apply div_le_div_of_nonneg_left (by norm_num) (by nlinarith [hL20])
    nlinarith [hL20, hCbr1]
  by_cases hsmall : |γ| * (Cp * L₀) ≤ 1
  · have h1 := hCp N χ hχ1 hχ2 β γ hγ hzero (by rw [hL₀def] at hsmall; exact hsmall)
    rw [← hL₀def] at h1
    have h2 := hmono Cp hCp1 (le_max_left _ _)
    linarith [h1, h2]
  · push_neg at hsmall
    have h1 := hCq N χ hχ1 hχ2 β γ hzero
      (by rw [hL₀def] at hsmall; linarith [hsmall])
    rw [← hL₀def] at h1
    have h2 := hmono Cq hCq1 (le_max_right _ _)
    linarith [h1, h2]

