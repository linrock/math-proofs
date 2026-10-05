module

public import OddTail1054
public import StatementAudit1054
public import CofactorParity1054

@[expose] public section


/-!
# Linear sifted-density lower bound and divisibility-preserving second moment for Erdős #1054

This module establishes two core quantitative ingredients for Erdős Problem 1054:

1. **Linear sifted-density lower bound (`sift_density_linear_lb`)**:
   Using `lcmRange_le_four_pow` (`lcm(1, ..., n) ≤ 4^n`), every reduced numerator
   `Aval e R` for `e ≤ E` divides `e * lcm(1, ..., E - 1)` and is bounded by
   `E^2 * 4^E`. Every prime divisor of the sieve modulus `Q_E` is therefore at
   most `E^2 * 4^E`, upgrading Mertens' lower bound on the sifted density from
   `c₁ / (E * log(2E))` to `c₁ / E`.

2. **Divisibility-preserving second moment (`moment2_le_all`, `large_e_bound_U_all`, `Sp_toReal_le`)**:
   Retaining the divisibility condition `e ∣ m` in the second moment gives
   `#H_{A,E}(X) ≤ A^3 * U(E) * X`.
   - With the fixed exponent `β = 1/2` (`U(E) ≤ C₂ * E^(-3/2)`), choosing
     `E asymp A^6` gives a logarithm-free `c / A^6` lower density bound
     (`pure_power_six_lower_density_odd_in_odd_density_one`).
   - The uniform integral bound `Sp p ≤ 2 / (p - 1)` for `1 < p ≤ 2` supplies the
     Dirichlet-series input for the sharp `c / [A^3 (1 + log A)^4]` bound in
     `SharpSecondMoment1054.lean`.
-/

open Finset Filter Asymptotics MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Erdos1054.SecondMoment
set_option linter.deprecated false


lemma Aval_le_exp (E e : ℕ) (R : Finset ℕ) (hE : 2 ≤ E) (he : e ≤ E) (hR : R ⊆ Finset.Ico 1 e) :
    _root_.Represented.Aval e R ≤ E ^ 2 * 4 ^ E := by
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · simp [_root_.Represented.Aval]
  set Dn : ℕ := _root_.Represented.lcmRange (E - 1) with hDn
  have hE1 : 1 ≤ E - 1 := by omega
  have hDnpos : 0 < Dn := _root_.Represented.lcmRange_pos (E - 1) hE1
  have hrdvd : ∀ r ∈ R, r ∣ Dn := fun r hr => by
    have hmem := hR hr; rw [Finset.mem_Ico] at hmem
    exact _root_.Represented.lcmRange_dvd_of_le (by omega) (by omega)
  set An : ℕ := e * ∑ r ∈ R, Dn / r with hAn
  have hVeq : (e : ℚ) * ∑ r ∈ R, (1 : ℚ) / r = Rat.divInt (An : ℤ) (Dn : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast,
      eq_div_iff (by exact_mod_cast hDnpos.ne' : (Dn : ℚ) ≠ 0), hAn]
    push_cast
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr0 : (r : ℚ) ≠ 0 := by
      have hmem := hR hr; rw [Finset.mem_Ico] at hmem
      exact Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_div (hrdvd r hr) hr0, one_div, inv_mul_eq_div]
  have hAval_le_An : _root_.Represented.Aval e R ≤ An := by
    rcases Nat.eq_zero_or_pos An with hA0 | hApos
    · rw [_root_.Represented.Aval, hVeq, hA0]; simp
    · have hdvd : (_root_.Represented.Aval e R : ℤ) ∣ (An : ℤ) := by
        rw [_root_.Represented.Aval]
        have hnd := Rat.num_dvd (An : ℤ) (b := (Dn : ℤ)) (by exact_mod_cast hDnpos.ne')
        rw [← hVeq] at hnd
        rwa [Int.natAbs_dvd]
      exact Nat.le_of_dvd hApos (by exact_mod_cast hdvd)
  have hAn_le : An ≤ E ^ 2 * 4 ^ E := by
    rw [hAn]
    calc e * ∑ r ∈ R, Dn / r
        ≤ E * (R.card * Dn) := by
          refine Nat.mul_le_mul he ?_
          calc ∑ r ∈ R, Dn / r ≤ ∑ _r ∈ R, Dn := Finset.sum_le_sum (fun r _ => Nat.div_le_self _ _)
            _ = R.card * Dn := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ E * (E * 4 ^ E) := by
          refine Nat.mul_le_mul_left _ (Nat.mul_le_mul ?_ ?_)
          · calc R.card ≤ (Finset.Ico 1 e).card := Finset.card_le_card hR
              _ = e - 1 := by rw [Nat.card_Ico]
              _ ≤ E := by omega
          · calc Dn ≤ 4 ^ (E - 1) := _root_.Represented.lcmRange_le_four_pow (E - 1) hE1
              _ ≤ 4 ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      _ = E ^ 2 * 4 ^ E := by ring
  exact hAval_le_An.trans hAn_le

lemma qER_le_exp (E e : ℕ) (R : Finset ℕ) (hE : 2 ≤ E) (he : e ≤ E) (hR : R ⊆ Finset.Ico 1 e) :
    _root_.Represented.qER e R ≤ E ^ 2 * 4 ^ E := by
  rw [_root_.Represented.qER]
  rcases Nat.eq_zero_or_pos (_root_.Represented.Aval e R) with h0 | hpos
  · rw [h0, Nat.minFac_zero]
    have h4 : 1 ≤ 4 ^ E := Nat.one_le_pow E 4 (by omega)
    nlinarith
  · exact le_trans (Nat.minFac_le hpos) (Aval_le_exp E e R hE he hR)

lemma primeFactors_Qpr_le_exp (E : ℕ) (hE : 2 ≤ E) :
    ∀ p ∈ (_root_.Represented.Qpr E).primeFactors, p ≤ E ^ 2 * 4 ^ E := by
  intro p hp
  obtain ⟨hpp, hpdvd, _⟩ := Nat.mem_primeFactors.1 hp
  rw [_root_.Represented.Qpr] at hpdvd
  obtain ⟨q, hqS, hpq⟩ := hpp.prime.exists_mem_finset_dvd hpdvd
  have hqle : q ≤ E ^ 2 * 4 ^ E := by
    rw [_root_.Represented.S, Finset.mem_insert] at hqS
    rcases hqS with rfl | hqS
    · have h4 : 1 ≤ 4 ^ E := Nat.one_le_pow E 4 (by omega)
      nlinarith
    · simp only [Finset.mem_biUnion, Finset.mem_image] at hqS
      obtain ⟨e, hemem, R, hRmem, rfl⟩ := hqS
      rw [Finset.mem_Icc] at hemem
      rw [Finset.mem_powerset] at hRmem
      exact qER_le_exp E e R hE hemem.2 hRmem
  exact le_trans (Nat.le_of_dvd (_root_.Represented.S_pos E q hqS) hpq) hqle

theorem sift_density_linear_lb :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ E : ℕ, 2 ≤ E →
      c₁ / (E : ℝ) ≤ _root_.Represented.δ E := by
  obtain ⟨c₀, hc₀, hmertens⟩ := _root_.Represented.mertens_third_lower
  refine ⟨c₀ / 7, by positivity, fun E hE => ?_⟩
  have hE2R : (2 : ℝ) ≤ E := by exact_mod_cast hE
  set Y : ℕ := E ^ 2 * 4 ^ E with hYdef
  have hY2 : 2 ≤ Y := by
    rw [hYdef]
    have h4 : 1 ≤ 4 ^ E := Nat.one_le_pow E 4 (by omega)
    nlinarith
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY2
  have hsub : (_root_.Represented.Qpr E).primeFactors ⊆ (Finset.range (Y + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := primeFactors_Qpr_le_exp E hE p hp; omega, (Nat.mem_primeFactors.1 hp).1⟩
  have hmono : ∏ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ (_root_.Represented.Qpr E).primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_sdiff hsub]
    apply mul_le_of_le_one_left
    · apply Finset.prod_nonneg
      intro p hp
      have hpp := (Nat.mem_primeFactors.1 hp).1
      have hp1 : (1 : ℝ) ≤ p := by have := hpp.two_le; exact_mod_cast (show 1 ≤ p by omega)
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith
    · apply Finset.prod_le_one₀
      · intro p hp
        have hpp : p.Prime := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hp).1).2
        have hp1 : (1 : ℝ) ≤ p := by have := hpp.two_le; exact_mod_cast (show 1 ≤ p by omega)
        have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
        linarith
      · intro p hp
        have hpp : p.Prime := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hp).1).2
        have hppos : (0 : ℝ) < p := by have := hpp.pos; exact_mod_cast this
        have : 0 ≤ 1 / (p : ℝ) := by positivity
        linarith
  have hA2 := hmertens Y hY2
  have hlogYpos : 0 < Real.log (2 * (Y : ℝ)) :=
    Real.log_pos (by nlinarith [hYR])
  have hlog : Real.log (2 * (Y : ℝ)) ≤ 7 * (E : ℝ) := by
    have hYlog : Real.log (2 * (Y : ℝ)) = Real.log 2 + 2 * Real.log (E : ℝ) + (E : ℝ) * Real.log 4 := by
      rw [hYdef]
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have hlogE : Real.log (E : ℝ) ≤ (E : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    rw [hYlog]
    nlinarith
  rw [_root_.Represented.delta_eq_prod]
  calc c₀ / 7 / (E : ℝ)
      = c₀ / (7 * (E : ℝ)) := by rw [div_div]
    _ ≤ c₀ / Real.log (2 * (Y : ℝ)) := by
        rw [div_le_div_iff₀ (by linarith) hlogYpos]
        exact mul_le_mul_of_nonneg_left hlog hc₀.le
    _ ≤ ∏ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := hA2
    _ ≤ ∏ p ∈ (_root_.Represented.Qpr E).primeFactors, (1 - 1 / (p : ℝ)) := hmono



/-- General sieve combination lemma: given any upper bound `Hbound` on `#H_{A,E}(X) / X`,
the odd represented large-ratio tail has lower density at least `δ E - Hbound`. -/
theorem lowerDensity_odd_gt_of_Hset_bound (A Hbound : ℝ) (E : ℕ) (hE : 2 ≤ E)
    (hHbound : ∀ X : ℕ, (_root_.Represented.countUpTo (_root_.Represented.Hset A E) X : ℝ) ≤ Hbound * X) :
    _root_.Represented.δ E - Hbound ≤
      _root_.Represented.lowerDensity
        (fun N : ℕ => Odd N ∧ N ∈ _root_.Represented.R ∧
          A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ)) := by
  have hDeep : _root_.Represented.DeepInputs :=
    _root_.Erdos1054.goldbach_of_matching_density
      _root_.Erdos1054.Unconditional.almost_all_binary_goldbach
  have hodd : ∀ N, Nat.Coprime N (_root_.Represented.Qpr E) → Odd N := by
    intro N hN
    rcases Nat.even_or_odd N with he | ho
    · have hgcd : Nat.gcd N (_root_.Represented.Qpr E) = 1 := hN
      have hdvd : (2 : ℕ) ∣ 1 :=
        hgcd ▸ Nat.dvd_gcd he.two_dvd (_root_.Represented.two_dvd_Qpr E hE)
      exact absurd hdvd (by decide)
    · exact ho
  have step0 : _root_.Represented.δ E ≤
      _root_.Represented.lowerDensity (fun N => Nat.Coprime N (_root_.Represented.Qpr E)) :=
    _root_.Represented.sift_lowerDensity E hE
  have step1 : _root_.Represented.δ E ≤
      _root_.Represented.lowerDensity
        (fun N => Nat.Coprime N (_root_.Represented.Qpr E) ∧
          ¬ (Nat.Coprime N (_root_.Represented.Qpr E) ∧
            ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = _root_.Represented.F e d)) :=
    _root_.Represented.lowerDensity_and_not step0 (_root_.Represented.small_e_exclusion E hE)
  have hB1 : _root_.Represented.CountIsLittleO
      (fun N => Nat.Coprime N (_root_.Represented.Qpr E) ∧ N ∉ _root_.Represented.R) :=
    _root_.Represented.CountIsLittleO.mono
      (fun N hN => ⟨hodd N hN.1, hN.2⟩)
      (_root_.Represented.odd_represented hDeep)
  have step2 : _root_.Represented.δ E ≤
      _root_.Represented.lowerDensity
        (fun N => (Nat.Coprime N (_root_.Represented.Qpr E) ∧
            ¬ (Nat.Coprime N (_root_.Represented.Qpr E) ∧
              ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = _root_.Represented.F e d)) ∧
          ¬ (Nat.Coprime N (_root_.Represented.Qpr E) ∧ N ∉ _root_.Represented.R)) :=
    _root_.Represented.lowerDensity_and_not step1 hB1
  have step3 :
      _root_.Represented.δ E - Hbound ≤
        _root_.Represented.lowerDensity
          (fun N => ((Nat.Coprime N (_root_.Represented.Qpr E) ∧
              ¬ (Nat.Coprime N (_root_.Represented.Qpr E) ∧
                ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = _root_.Represented.F e d)) ∧
            ¬ (Nat.Coprime N (_root_.Represented.Qpr E) ∧ N ∉ _root_.Represented.R)) ∧
              ¬ _root_.Represented.Hset A E N) :=
    _root_.Represented.lowerDensity_and_not_le hHbound step2
  have hmono : ∀ N,
      (((Nat.Coprime N (_root_.Represented.Qpr E) ∧
          ¬ (Nat.Coprime N (_root_.Represented.Qpr E) ∧
            ∃ e d, 1 ≤ e ∧ e ≤ E ∧ N = _root_.Represented.F e d)) ∧
        ¬ (Nat.Coprime N (_root_.Represented.Qpr E) ∧ N ∉ _root_.Represented.R)) ∧
          ¬ _root_.Represented.Hset A E N) →
        Odd N ∧ N ∈ _root_.Represented.R ∧
          A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ) := by
    intro N hgood
    obtain ⟨⟨⟨hQc, hnsmall⟩, hnunrep⟩, hnHset⟩ := hgood
    have hNR : N ∈ _root_.Represented.R := by
      by_contra hNR
      exact hnunrep ⟨hQc, hNR⟩
    refine ⟨hodd N hQc, hNR, ?_⟩
    rw [_root_.Erdos1054.OriginalNth.f_eq_supported]
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨e, d, he, hd, hfeq, hNF⟩ := _root_.Represented.f_mem_Fform N hNR
    by_cases heE : e ≤ E
    · exact hnsmall ⟨hQc, e, d, he, heE, hNF⟩
    · rw [not_le] at heE
      refine hnHset ⟨e, d, heE, hd, hNF, ?_⟩
      have hcast : (e : ℝ) * d = (_root_.Represented.f N : ℝ) := by
        rw [← Nat.cast_mul, ← hfeq]
      rw [hcast]
      exact hle
  exact step3.trans (_root_.Represented.lowerDensity_mono hmono)

noncomputable def U (E : ℕ) : ℝ≥0∞ :=
  ∑' t : ℕ × ℕ × ℕ,
    (if E < t.1 ∧ t.1 ≤ t.2.1 ∧ t.1 ≤ t.2.2 then
      ENNReal.ofReal
        (1 / ((t.2.1 * t.2.2 * Nat.lcm t.1 (Nat.lcm t.2.1 t.2.2) : ℕ) : ℝ))
    else 0)

theorem U_le_ennreal_max (E : ℕ) :
    U E ≤ ENNReal.ofReal (((max E 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
      * (_root_.Represented.Sp (3 / 2) * _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3)
          * _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6)) := by
  classical
  set g₁ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (-(3 / 2 : ℝ))) with hg1
  set g₂ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (-(4 / 3 : ℝ))) with hg2
  set g₃ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((n : ℝ) ^ (-(7 / 6 : ℝ))) with hg3
  have hS1 : (∑' n, g₁ n) = _root_.Represented.Sp (3 / 2) := rfl
  have hS2 : (∑' n, g₂ n) = _root_.Represented.Sp (4 / 3) := rfl
  have hS3 : (∑' n, g₃ n) = _root_.Represented.Sp (7 / 6) := rfl
  set b : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℝ≥0∞ := fun d =>
    ENNReal.ofReal (((max E 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
      (g₁ d.1 * g₂ d.2.1 * g₂ d.2.2.1 * g₂ d.2.2.2.1 * g₃ d.2.2.2.2.1
        * g₃ d.2.2.2.2.2.1 * g₃ d.2.2.2.2.2.2) with hb
  set Sset : Set (ℕ × ℕ × ℕ) := {p | E < p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2} with hSset
  set fS : ℕ × ℕ × ℕ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (1 / ((p.2.1 * p.2.2 * Nat.lcm p.1 (Nat.lcm p.2.1 p.2.2) : ℕ) : ℝ))
    with hfS
  have hUeq : U E = ∑' p : Sset, fS p := by
    have h1 : U E = ∑' x : ℕ × ℕ × ℕ, Sset.indicator fS x := by
      rw [U]
      refine tsum_congr (fun p => ?_)
      rw [Set.indicator_apply]
      simp only [hSset, hfS, Set.mem_ofPred_eq]
    rw [h1]; exact (tsum_subtype Sset fS).symm
  set F : Sset → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := fun p => _root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2 with hF
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
    have sp := _root_.Represented.decomp_spec (r := p.1.1) (s := p.1.2.1) (t := p.1.2.2)
      hpe1 (by omega) (by omega)
    simp only at sp
    obtain ⟨hh, hu, hv, hw, hRR, hSS, hTT, hrid, hsid, htid, hlcm⟩ := sp
    have hpw := _root_.Represented.decomp_pointwise (e := p.1.1) (r := p.1.1) (s := p.1.2.1) (t := p.1.2.2)
      (h := (_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).1)
      (u := (_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.1)
      (v := (_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.1)
      (w := (_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.1)
      (R := (_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.1)
      (S := (_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.2.1)
      (T := (_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.2.2)
      hpe1 le_rfl hps hpt' hh hu hv hw hRR hSS hTT hrid hsid htid hlcm
    have he0R : (0 : ℝ) < (p.1.1 : ℝ) := by exact_mod_cast hpe1
    have hE0R : (0 : ℝ) < ((max E 1 : ℕ) : ℝ) := by exact_mod_cast (le_max_right E 1)
    have hEe : ((max E 1 : ℕ) : ℝ) ≤ (p.1.1 : ℝ) := by exact_mod_cast (max_le hpE.le hpe1)
    have hLpos : 0 < Nat.lcm p.1.1 (Nat.lcm p.1.2.1 p.1.2.2) :=
      Nat.pos_of_ne_zero (by
        simp only [ne_eq, Nat.lcm_eq_zero_iff]
        push Not
        omega)
    have hsplit : (1 : ℝ) / ((p.1.2.1 * p.1.2.2 * Nat.lcm p.1.1 (Nat.lcm p.1.2.1 p.1.2.2) : ℕ) : ℝ)
        = (p.1.1 : ℝ) * ((1 : ℝ)
            / ((p.1.1 * p.1.2.1 * p.1.2.2 * Nat.lcm p.1.1 (Nat.lcm p.1.2.1 p.1.2.2) : ℕ) : ℝ)) := by
      have h1 : (0:ℝ) < (p.1.2.1 : ℝ) := by exact_mod_cast (by omega : 0 < p.1.2.1)
      have h2 : (0:ℝ) < (p.1.2.2 : ℝ) := by exact_mod_cast (by omega : 0 < p.1.2.2)
      have h3 : (0:ℝ) < ((Nat.lcm p.1.1 (Nat.lcm p.1.2.1 p.1.2.2) : ℕ) : ℝ) := by
        exact_mod_cast hLpos
      push_cast
      rw [mul_one_div, eq_comm,
        div_eq_div_iff (mul_pos (mul_pos (mul_pos he0R h1) h2) h3).ne'
          (mul_pos (mul_pos h1 h2) h3).ne']
      ring
    have hexp : (p.1.1 : ℝ) * (p.1.1 : ℝ) ^ (-(5 / 2 : ℝ)) = (p.1.1 : ℝ) ^ (-(3 / 2 : ℝ)) := by
      nth_rewrite 1 [show (p.1.1 : ℝ) = (p.1.1 : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add he0R]
      norm_num
    have hmono : (p.1.1 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ((max E 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hE0R hEe (by norm_num)
    have hreal : (1 : ℝ) / ((p.1.2.1 * p.1.2.2 * Nat.lcm p.1.1 (Nat.lcm p.1.2.1 p.1.2.2) : ℕ) : ℝ)
        ≤ ((max E 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
            (((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).1 : ℝ) ^ (-(3 / 2 : ℝ))
              * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.1 : ℝ) ^ (-(4 / 3 : ℝ))
              * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.1 : ℝ) ^ (-(4 / 3 : ℝ))
              * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.1 : ℝ) ^ (-(4 / 3 : ℝ))
              * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.1 : ℝ) ^ (-(7 / 6 : ℝ))
              * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.2.1 : ℝ) ^ (-(7 / 6 : ℝ))
              * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.2.2 : ℝ) ^ (-(7 / 6 : ℝ))) := by
      set prod7 : ℝ := ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).1 : ℝ) ^ (-(3 / 2 : ℝ))
          * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.1 : ℝ) ^ (-(4 / 3 : ℝ))
          * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.1 : ℝ) ^ (-(4 / 3 : ℝ))
          * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.1 : ℝ) ^ (-(4 / 3 : ℝ))
          * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.1 : ℝ) ^ (-(7 / 6 : ℝ))
          * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.2.1 : ℝ) ^ (-(7 / 6 : ℝ))
          * ((_root_.Represented.decomp p.1.1 p.1.2.1 p.1.2.2).2.2.2.2.2.2 : ℝ) ^ (-(7 / 6 : ℝ)) with hprod7
      have hprod70 : 0 ≤ prod7 := by
        rw [hprod7]
        positivity
      calc (1 : ℝ) / ((p.1.2.1 * p.1.2.2 * Nat.lcm p.1.1 (Nat.lcm p.1.2.1 p.1.2.2) : ℕ) : ℝ)
          = (p.1.1 : ℝ) * ((1 : ℝ)
              / ((p.1.1 * p.1.2.1 * p.1.2.2 * Nat.lcm p.1.1 (Nat.lcm p.1.2.1 p.1.2.2) : ℕ) : ℝ)) :=
            hsplit
        _ ≤ (p.1.1 : ℝ) * ((p.1.1 : ℝ) ^ (-(5 / 2 : ℝ)) * prod7) := by
            apply mul_le_mul_of_nonneg_left _ he0R.le
            rw [hprod7]
            exact hpw
        _ = (p.1.1 : ℝ) ^ (-(3 / 2 : ℝ)) * prod7 := by
            rw [← mul_assoc, hexp]
        _ ≤ ((max E 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * prod7 :=
            mul_le_mul_of_nonneg_right hmono hprod70
    simp only [hfS, hF, hb, hg1, hg2, hg3]
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity)]
  rw [hUeq]
  calc (∑' p : Sset, fS p) ≤ ∑' p : Sset, b (F p) := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' d, b d := ENNReal.tsum_comp_le_tsum_of_injective hFinj b
    _ = ENNReal.ofReal (((max E 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
          (∑' d : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ,
            g₁ d.1 * g₂ d.2.1 * g₂ d.2.2.1 * g₂ d.2.2.2.1 * g₃ d.2.2.2.2.1
              * g₃ d.2.2.2.2.2.1 * g₃ d.2.2.2.2.2.2) := by
          simp only [hb]; rw [← ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (((max E 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
          * (_root_.Represented.Sp (3 / 2) * _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3)
              * _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6)) := by
          rw [_root_.Represented.tsum7 g₁ g₂ g₃, hS1, hS2, hS3]; ring

theorem U_le_ennreal (E : ℕ) (hE : 1 ≤ E) :
    U E ≤ ENNReal.ofReal ((E : ℝ) ^ (-(3 / 2 : ℝ)))
      * (_root_.Represented.Sp (3 / 2) * _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3)
          * _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6)) := by
  simpa [Nat.max_eq_left hE] using U_le_ennreal_max E

theorem U_lt_top_all (E : ℕ) : U E < ⊤ := by
  refine lt_of_le_of_lt (U_le_ennreal_max E) ?_
  rw [lt_top_iff_ne_top]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_) ?_) ?_) ?_) ?_
  all_goals exact _root_.Represented.Sp_ne_top (by norm_num)

theorem U_lt_top (E : ℕ) (_hE : 1 ≤ E) : U E < ⊤ :=
  U_lt_top_all E


theorem U_power_saving :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ E : ℕ, 1 ≤ E → (U E).toReal ≤ C₂ * (E : ℝ) ^ (-(3 / 2 : ℝ)) := by
  set Cen : ℝ≥0∞ := _root_.Represented.Sp (3 / 2) * _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3)
      * _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6) with hCen
  have hCtop : Cen ≠ ⊤ := by
    rw [hCen]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_) ?_) ?_) ?_) ?_
    all_goals exact _root_.Represented.Sp_ne_top (by norm_num)
  have hCpos : 0 < Cen := by
    rw [hCen, pos_iff_ne_zero]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
      ?_) ?_) ?_) ?_
    all_goals exact _root_.Represented.Sp_pos.ne'
  refine ⟨Cen.toReal, ENNReal.toReal_pos hCpos.ne' hCtop, fun E hE => ?_⟩
  have hchain := U_le_ennreal E hE
  rw [← hCen] at hchain
  refine le_trans (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCtop) hchain) ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  exact le_of_eq (mul_comm _ _)

lemma sum_sq_eq_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ r ∈ s, a r) ^ 2 = ∑ p ∈ s ×ˢ s, a p.1 * a p.2 := by
  simp only [Finset.sum_product]
  rw [sq, Finset.sum_mul_sum]

theorem moment2_le_all (E Z : ℕ) :
    (∑ p ∈ (Finset.range (Z + 1) ×ˢ Finset.range (Z + 1)).filter
        (fun p => p.2 ∣ p.1 ∧ E < p.2), (_root_.Represented.g p.2 p.1) ^ 2)
      ≤ (Z : ℝ) * (U E).toReal := by
  classical
  set ind : ℕ → ℕ → ℝ := fun r n => if r ∣ n ∧ 1 ≤ n then (1 : ℝ) / r else 0 with hind
  set inde : ℕ → ℕ → ℝ := fun e r => if e ≤ r then (1 : ℝ) else 0 with hinde
  set indd : ℕ → ℕ → ℝ := fun e n => if e ∣ n ∧ 1 ≤ n then (1 : ℝ) else 0 with hindd
  have hg : ∀ e : ℕ, ∀ n ∈ Finset.range (Z + 1), 1 ≤ n →
      _root_.Represented.g e n = ∑ r ∈ Finset.range (Z + 1), inde e r * ind r n := by
    intro e n hn hn1
    rw [Finset.mem_range] at hn
    rw [_root_.Represented.g]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Z + 1)) (fun r => e ≤ r ∧ r ∣ n ∧ 1 ≤ n)]
    have hz : ∑ r ∈ (Finset.range (Z + 1)).filter
        (fun r => ¬(e ≤ r ∧ r ∣ n ∧ 1 ≤ n)), inde e r * ind r n = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [Finset.mem_filter] at hr
      simp only [hinde, hind]
      by_cases h1 : e ≤ r
      · by_cases h2 : r ∣ n ∧ 1 ≤ n
        · exact absurd ⟨h1, h2.1, h2.2⟩ hr.2
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [hz, add_zero]
    have hmatch : (Finset.range (Z + 1)).filter (fun r => e ≤ r ∧ r ∣ n ∧ 1 ≤ n)
        = n.divisors.filter (e ≤ ·) := by
      ext r
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_range]
      constructor
      · rintro ⟨_, her, hdvd, _⟩
        exact ⟨⟨hdvd, by omega⟩, her⟩
      · rintro ⟨⟨hdvd, hn0⟩, her⟩
        exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (by omega) hdvd) hn, her, hdvd, by omega⟩
    rw [hmatch]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_filter, Nat.mem_divisors] at hr
    simp only [hinde, hind]
    rw [if_pos hr.2, if_pos ⟨hr.1.1, by omega⟩, one_mul]
  set R2 := Finset.range (Z + 1) ×ˢ Finset.range (Z + 1) with hR2
  set R3 := Finset.range (Z + 1) ×ˢ Finset.range (Z + 1) ×ˢ Finset.range (Z + 1) with hR3
  have hswap : (∑ p ∈ R2.filter (fun p => p.2 ∣ p.1 ∧ E < p.2), (_root_.Represented.g p.2 p.1) ^ 2)
      ≤ ∑ q ∈ R3, ∑ n ∈ Finset.range (Z + 1),
          (if E < q.1 then (1:ℝ) else 0) * indd q.1 n
            * (inde q.1 q.2.1 * ind q.2.1 n) * (inde q.1 q.2.2 * ind q.2.2 n) := by
    have hpair : ∀ p ∈ R2, (if p.2 ∣ p.1 ∧ E < p.2 then (_root_.Represented.g p.2 p.1) ^ 2 else 0)
        = ∑ rs ∈ Finset.range (Z + 1) ×ˢ Finset.range (Z + 1),
            (if E < p.2 then (1:ℝ) else 0) * indd p.2 p.1
              * (inde p.2 rs.1 * ind rs.1 p.1) * (inde p.2 rs.2 * ind rs.2 p.1) := by
      intro p hp
      rw [hR2, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      by_cases hc : p.2 ∣ p.1 ∧ E < p.2
      · rw [if_pos hc]
        by_cases hn1 : 1 ≤ p.1
        · have hgp := hg p.2 p.1 (Finset.mem_range.mpr hp.1) hn1
          rw [hgp, sum_sq_eq_prod]
          apply Finset.sum_congr rfl
          intro rs _
          rw [if_pos hc.2]
          simp only [hindd]
          rw [if_pos ⟨hc.1, hn1⟩]
          ring
        · have hp10 : p.1 = 0 := by omega
          have hgz : _root_.Represented.g p.2 p.1 = 0 := by
            rw [hp10, _root_.Represented.g]
            simp
          rw [hgz]
          rw [show (0:ℝ) ^ 2 = 0 by ring]
          symm
          apply Finset.sum_eq_zero
          intro rs _
          simp only [hindd]
          rw [hp10, if_neg (by omega : ¬(p.2 ∣ 0 ∧ 1 ≤ 0))]
          ring
      · rw [if_neg hc]
        symm
        apply Finset.sum_eq_zero
        intro rs _
        rcases not_and_or.mp hc with hnd | hnE
        · have h0 : indd p.2 p.1 = 0 := by
            simp only [hindd]
            exact if_neg (fun h => hnd h.1)
          rw [h0]
          ring
        · have h0 : (if E < p.2 then (1:ℝ) else 0) = 0 := if_neg hnE
          rw [h0]
          ring
    refine le_of_eq ?_
    calc (∑ p ∈ R2.filter (fun p => p.2 ∣ p.1 ∧ E < p.2), (_root_.Represented.g p.2 p.1) ^ 2)
        = ∑ p ∈ R2, (if p.2 ∣ p.1 ∧ E < p.2 then (_root_.Represented.g p.2 p.1) ^ 2 else 0) :=
          Finset.sum_filter _ _
      _ = ∑ p ∈ R2, ∑ rs ∈ Finset.range (Z + 1) ×ˢ Finset.range (Z + 1),
            (if E < p.2 then (1:ℝ) else 0) * indd p.2 p.1
              * (inde p.2 rs.1 * ind rs.1 p.1) * (inde p.2 rs.2 * ind rs.2 p.1) :=
          Finset.sum_congr rfl hpair
      _ = ∑ n ∈ Finset.range (Z + 1), ∑ e ∈ Finset.range (Z + 1),
            ∑ rs ∈ Finset.range (Z + 1) ×ˢ Finset.range (Z + 1),
            (if E < e then (1:ℝ) else 0) * indd e n
              * (inde e rs.1 * ind rs.1 n) * (inde e rs.2 * ind rs.2 n) := by
          rw [hR2, Finset.sum_product]
      _ = ∑ e ∈ Finset.range (Z + 1), ∑ n ∈ Finset.range (Z + 1),
            ∑ rs ∈ Finset.range (Z + 1) ×ˢ Finset.range (Z + 1),
            (if E < e then (1:ℝ) else 0) * indd e n
              * (inde e rs.1 * ind rs.1 n) * (inde e rs.2 * ind rs.2 n) :=
          Finset.sum_comm
      _ = ∑ e ∈ Finset.range (Z + 1),
            ∑ rs ∈ Finset.range (Z + 1) ×ˢ Finset.range (Z + 1),
            ∑ n ∈ Finset.range (Z + 1),
            (if E < e then (1:ℝ) else 0) * indd e n
              * (inde e rs.1 * ind rs.1 n) * (inde e rs.2 * ind rs.2 n) := by
          apply Finset.sum_congr rfl
          intro e _
          exact Finset.sum_comm
      _ = ∑ q ∈ R3, ∑ n ∈ Finset.range (Z + 1),
            (if E < q.1 then (1:ℝ) else 0) * indd q.1 n
              * (inde q.1 q.2.1 * ind q.2.1 n) * (inde q.1 q.2.2 * ind q.2.2 n) := by
          rw [hR3, Finset.sum_product]
  refine le_trans hswap ?_
  have hpbound : ∀ q ∈ R3,
      (∑ n ∈ Finset.range (Z + 1),
          (if E < q.1 then (1:ℝ) else 0) * indd q.1 n
            * (inde q.1 q.2.1 * ind q.2.1 n) * (inde q.1 q.2.2 * ind q.2.2 n))
      ≤ (Z : ℝ) * (if E < q.1 ∧ q.1 ≤ q.2.1 ∧ q.1 ≤ q.2.2 then
          (1 : ℝ) / ((q.2.1 * q.2.2 * Nat.lcm q.1 (Nat.lcm q.2.1 q.2.2) : ℕ) : ℝ) else 0) := by
    rintro ⟨e, r, s⟩ _
    by_cases hc : E < e ∧ e ≤ r ∧ e ≤ s
    · have hterm : ∀ n, (if E < e then (1:ℝ) else 0) * indd e n
          * (inde e r * ind r n) * (inde e s * ind s n)
          = if Nat.lcm e (Nat.lcm r s) ∣ n ∧ 1 ≤ n then (1 : ℝ) / (r * s) else 0 := by
        intro n
        simp only [hind, hinde, hindd]
        rw [if_pos hc.1, if_pos hc.2.1, if_pos hc.2.2]
        by_cases hd : Nat.lcm e (Nat.lcm r s) ∣ n ∧ 1 ≤ n
        · have hd' := hd
          rw [Nat.lcm_dvd_iff, Nat.lcm_dvd_iff] at hd'
          rw [if_pos ⟨hd'.1.1, hd.2⟩, if_pos ⟨hd'.1.2.1, hd.2⟩, if_pos ⟨hd'.1.2.2, hd.2⟩,
            if_pos hd]
          ring
        · rw [if_neg hd]
          rw [Nat.lcm_dvd_iff, Nat.lcm_dvd_iff] at hd
          by_cases h1 : e ∣ n ∧ 1 ≤ n
          · by_cases h2 : r ∣ n ∧ 1 ≤ n
            · by_cases h3 : s ∣ n ∧ 1 ≤ n
              · exact absurd ⟨⟨h1.1, h2.1, h3.1⟩, h1.2⟩ hd
              · rw [if_pos h1, if_pos h2, if_neg h3]
                ring
            · rw [if_pos h1, if_neg h2]
              ring
          · rw [if_neg h1]
            ring
      rw [Finset.sum_congr rfl (fun n _ => hterm n)]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rw [if_pos hc]
      set L := Nat.lcm e (Nat.lcm r s) with hL
      have hcount : ((Finset.range (Z + 1)).filter (fun n => L ∣ n ∧ 1 ≤ n)).card ≤ Z / L := by
        rw [← Nat.card_multiples' Z L]
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        obtain ⟨hr', hd', h1'⟩ := hn
        exact ⟨hr', by omega, hd'⟩
      have hcountR : (((Finset.range (Z + 1)).filter (fun n => L ∣ n ∧ 1 ≤ n)).card : ℝ)
          ≤ (Z : ℝ) / (L : ℝ) := by
        have h1 : (((Finset.range (Z + 1)).filter (fun n => L ∣ n ∧ 1 ≤ n)).card : ℝ)
            ≤ ((Z / L : ℕ) : ℝ) := by exact_mod_cast hcount
        exact h1.trans Nat.cast_div_le
      refine le_trans (mul_le_mul_of_nonneg_right hcountR (by positivity)) (le_of_eq ?_)
      push_cast
      ring
    · rw [if_neg hc, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero (fun n _ => ?_))
      rcases not_and_or.mp hc with hnE | hnrs
      · have h0 : (if E < e then (1:ℝ) else 0) = 0 := if_neg hnE
        rw [h0]
        ring
      · rcases not_and_or.mp hnrs with hnr | hns
        · have h0 : inde e r = 0 := by
            simp only [hinde]
            exact if_neg hnr
          rw [h0]
          ring
        · have h0 : inde e s = 0 := by
            simp only [hinde]
            exact if_neg hns
          rw [h0]
          ring
  calc ∑ q ∈ R3, ∑ n ∈ Finset.range (Z + 1),
        (if E < q.1 then (1:ℝ) else 0) * indd q.1 n
          * (inde q.1 q.2.1 * ind q.2.1 n) * (inde q.1 q.2.2 * ind q.2.2 n)
      ≤ ∑ q ∈ R3, (Z : ℝ) * (if E < q.1 ∧ q.1 ≤ q.2.1 ∧ q.1 ≤ q.2.2 then
          (1 : ℝ) / ((q.2.1 * q.2.2 * Nat.lcm q.1 (Nat.lcm q.2.1 q.2.2) : ℕ) : ℝ) else 0) :=
        Finset.sum_le_sum hpbound
    _ = (Z : ℝ) * ∑ q ∈ R3, (if E < q.1 ∧ q.1 ≤ q.2.1 ∧ q.1 ≤ q.2.2 then
          (1 : ℝ) / ((q.2.1 * q.2.2 * Nat.lcm q.1 (Nat.lcm q.2.1 q.2.2) : ℕ) : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ (Z : ℝ) * (U E).toReal := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← ENNReal.toReal_ofReal (Finset.sum_nonneg (fun q _ => by positivity))]
        refine ENNReal.toReal_mono (U_lt_top_all E).ne ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => by positivity)]
        calc ∑ q ∈ R3, ENNReal.ofReal (if E < q.1 ∧ q.1 ≤ q.2.1 ∧ q.1 ≤ q.2.2 then
                (1 : ℝ) / ((q.2.1 * q.2.2 * Nat.lcm q.1 (Nat.lcm q.2.1 q.2.2) : ℕ) : ℝ) else 0)
            = ∑ q ∈ R3, (if E < q.1 ∧ q.1 ≤ q.2.1 ∧ q.1 ≤ q.2.2 then ENNReal.ofReal
                ((1 : ℝ) / ((q.2.1 * q.2.2 * Nat.lcm q.1 (Nat.lcm q.2.1 q.2.2) : ℕ) : ℝ))
                else 0) :=
              Finset.sum_congr rfl (fun q _ => by rw [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero])
          _ ≤ U E := by
              rw [U]
              exact ENNReal.sum_le_tsum R3

theorem moment2_le (E Z : ℕ) (_hE : 1 ≤ E) :
    (∑ p ∈ (Finset.range (Z + 1) ×ˢ Finset.range (Z + 1)).filter
        (fun p => p.2 ∣ p.1 ∧ E < p.2), (_root_.Represented.g p.2 p.1) ^ 2)
      ≤ (Z : ℝ) * (U E).toReal :=
  moment2_le_all E Z

theorem large_e_bound_U_all (A : ℝ) (hA0 : 0 < A) (E X : ℕ) :
    (_root_.Represented.countUpTo (_root_.Represented.Hset A E) X : ℝ) ≤
      A ^ 3 * (U E).toReal * X := by
  classical
  set M := ⌊A * (X : ℝ)⌋₊ with hMdef
  set pairs := (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
    (fun p => p.2 ∣ p.1 ∧ E < p.2 ∧ (1 : ℝ) / A ≤ _root_.Represented.g p.2 p.1) with hpairs
  have hstep1 : (_root_.Represented.countUpTo (_root_.Represented.Hset A E) X : ℝ) ≤ (pairs.card : ℝ) := by
    have hsub : _root_.Represented.setUpTo (_root_.Represented.Hset A E) X ⊆
        ↑(pairs.image (fun p => _root_.Represented.F p.2 (p.1 / p.2))) := by
      rintro N ⟨hNX, e, d, hEe, hd1, hN, hle⟩
      have he1 : 1 ≤ e := by omega
      have hgN : (N : ℝ) = ((e * d : ℕ) : ℝ) * _root_.Represented.g e (e * d) := by
        rw [hN]; exact_mod_cast _root_.Represented.reflection e d he1 hd1
      have hgpos : (1 : ℝ) / A ≤ _root_.Represented.g e (e * d) := by
        have hmpos : (0 : ℝ) < ((e * d : ℕ) : ℝ) := by positivity
        have hgnn : 0 ≤ _root_.Represented.g e (e * d) := by
          rw [_root_.Represented.g]; exact Finset.sum_nonneg (fun r _ => by positivity)
        have hcast : ((e * d : ℕ) : ℝ) ≤ A * N := by exact_mod_cast hle
        rw [hgN] at hcast
        rw [div_le_iff₀ hA0]; nlinarith [hcast, hmpos, hgnn]
      have hmle : e * d ≤ M := by
        rw [hMdef]; apply Nat.le_floor
        calc ((e * d : ℕ) : ℝ) ≤ A * N := by exact_mod_cast hle
          _ ≤ A * X := by
              apply mul_le_mul_of_nonneg_left _ hA0.le; exact_mod_cast hNX
      have hele : e ≤ M := le_trans (Nat.le_mul_of_pos_right e (by omega : 0 < d)) hmle
      rw [Finset.coe_image, Set.mem_image]
      refine ⟨(e * d, e), ?_, ?_⟩
      · rw [Finset.mem_coe, hpairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, dvd_mul_right e d, hEe, hgpos⟩
      · simp only [Nat.mul_div_cancel_left d (by omega : 0 < e)]; exact hN.symm
    calc (_root_.Represented.countUpTo (_root_.Represented.Hset A E) X : ℝ)
        ≤ ((pairs.image (fun p => _root_.Represented.F p.2 (p.1 / p.2))).card : ℝ) := by
          rw [_root_.Represented.countUpTo]
          exact_mod_cast le_trans (Set.ncard_le_ncard hsub (Finset.finite_toSet _))
            (le_of_eq (Set.ncard_coe_finset _))
      _ ≤ (pairs.card : ℝ) := by exact_mod_cast Finset.card_image_le
  have hstep2 : (pairs.card : ℝ) ≤ A ^ 2 * ((M : ℝ) * (U E).toReal) := by
    have hmarkov : (pairs.card : ℝ) ≤ A ^ 2 * ∑ p ∈ pairs, (_root_.Represented.g p.2 p.1) ^ 2 := by
      rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum (fun p hp => ?_)
      rw [hpairs, Finset.mem_filter] at hp
      have h1 : (1 : ℝ) ≤ A * _root_.Represented.g p.2 p.1 := by
        have := (div_le_iff₀ hA0).mp hp.2.2.2; linarith [this]
      calc ((1 : ℕ) : ℝ) = 1 := by norm_num
        _ ≤ (A * _root_.Represented.g p.2 p.1) ^ 2 := one_le_pow₀ h1
        _ = A ^ 2 * (_root_.Represented.g p.2 p.1) ^ 2 := by rw [mul_pow]
    refine le_trans hmarkov (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have henlarge : ∑ p ∈ pairs, (_root_.Represented.g p.2 p.1) ^ 2
        ≤ ∑ p ∈ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
            (fun p => p.2 ∣ p.1 ∧ E < p.2), (_root_.Represented.g p.2 p.1) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [hpairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
      · intro p _ _
        positivity
    exact le_trans henlarge (moment2_le_all E M)
  refine le_trans hstep1 (le_trans hstep2 ?_)
  have hMle : (M : ℝ) ≤ A * X := by rw [hMdef]; exact Nat.floor_le (by positivity)
  have hUnn : (0 : ℝ) ≤ (U E).toReal := ENNReal.toReal_nonneg
  calc A ^ 2 * ((M : ℝ) * (U E).toReal)
      ≤ A ^ 2 * ((A * X) * (U E).toReal) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hMle hUnn
    _ = A ^ 3 * (U E).toReal * X := by ring

theorem large_e_bound_U (A : ℝ) (hA : 1 ≤ A) (E : ℕ) (_hE : 1 ≤ E) (X : ℕ) :
    (_root_.Represented.countUpTo (_root_.Represented.Hset A E) X : ℝ) ≤
      A ^ 3 * (U E).toReal * X :=
  large_e_bound_U_all A (by linarith) E X

theorem large_e_bound_cubed :
    ∃ C₅ : ℝ, 0 < C₅ ∧ ∀ (A : ℝ), 1 ≤ A → ∀ E : ℕ, 1 ≤ E → ∀ X : ℕ,
      (_root_.Represented.countUpTo (_root_.Represented.Hset A E) X : ℝ) ≤
        C₅ * A ^ 3 * (E : ℝ) ^ (-(3 / 2 : ℝ)) * X := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := U_power_saving
  refine ⟨C₂, hC₂pos, fun A hA E hE X => ?_⟩
  refine le_trans (large_e_bound_U A hA E hE X) ?_
  have hU := hC₂ E hE
  calc A ^ 3 * (U E).toReal * X
      ≤ A ^ 3 * (C₂ * (E : ℝ) ^ (-(3 / 2 : ℝ))) * X := by
        gcongr
    _ = C₂ * A ^ 3 * (E : ℝ) ^ (-(3 / 2 : ℝ)) * X := by ring


theorem optimize_power_bound {k : ℕ} {c C : ℝ} (hc : 0 < c) (_hC : 0 < C)
    (P : ℝ → ℕ → Prop)
    (hbound : ∀ A : ℝ, 1 ≤ A → ∀ E : ℕ, 2 ≤ E →
      c / (E : ℝ) - C * A ^ k * (E : ℝ) ^ (-(3 / 2 : ℝ)) ≤
        _root_.Represented.lowerDensity (P A)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ A : ℝ, 1 ≤ A →
      c₀ / A ^ (2 * k) ≤ _root_.Represented.lowerDensity (P A) := by
  obtain ⟨M, hMlarge⟩ := exists_nat_gt (max 1 (2 * C / c))
  have hMone : (1 : ℝ) < M :=
    lt_of_le_of_lt (le_max_left 1 (2 * C / c)) hMlarge
  have hMpos : (0 : ℝ) < M := by linarith
  have hMnat : 2 ≤ M := by exact_mod_cast hMone
  have hMchoice : 2 * C ≤ c * (M : ℝ) := by
    have hquot : 2 * C / c < (M : ℝ) :=
      lt_of_le_of_lt (le_max_right 1 (2 * C / c)) hMlarge
    have hmul := (div_lt_iff₀ hc).mp hquot
    nlinarith
  refine ⟨c / (8 * (M : ℝ) ^ 2), by positivity, ?_⟩
  intro A hA
  have hApos : 0 < A := by linarith
  let B : ℕ := ⌈A ^ k⌉₊
  let T : ℕ := M * B
  let E : ℕ := T ^ 2
  have hAB : A ^ k ≤ (B : ℝ) := Nat.le_ceil (A ^ k)
  have hBtwo : (B : ℝ) ≤ 2 * A ^ k := by
    have hAk1 : 1 ≤ A ^ k := one_le_pow₀ hA
    have hceil : (⌈A ^ k⌉₊ : ℝ) < A ^ k + 1 := Nat.ceil_lt_add_one (by positivity)
    dsimp [B]
    linarith
  have hBnat : 1 ≤ B := by
    have hAk1 : (1 : ℝ) ≤ A ^ k := one_le_pow₀ hA
    have : (1 : ℝ) ≤ (B : ℝ) := hAk1.trans hAB
    exact_mod_cast this
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hTnat : 2 ≤ T := by dsimp [T]; nlinarith
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hE : 2 ≤ E := by dsimp [E]; nlinarith
  have hTcast : (T : ℝ) = (M : ℝ) * (B : ℝ) := by simp [T]
  have hEcast : (E : ℝ) = (T : ℝ) ^ 2 := by simp [E]
  have hrpow : (E : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / (T : ℝ) ^ 3 := by
    rw [hEcast, ← Real.rpow_natCast_mul hTpos.le 2 (-(3 / 2 : ℝ))]
    norm_num [Real.rpow_neg, Real.rpow_natCast, one_div]
  have herror : C * A ^ k * (E : ℝ) ^ (-(3 / 2 : ℝ)) ≤ c / (2 * (E : ℝ)) := by
    rw [hrpow, hEcast]
    have hrewrite : C * A ^ k * (1 / (T : ℝ) ^ 3) = (C * A ^ k) / (T : ℝ) ^ 3 := by ring
    rw [hrewrite]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hBM : A ^ k * (M : ℝ) ≤ (T : ℝ) := by
      rw [hTcast, mul_comm]
      exact mul_le_mul_of_nonneg_left hAB hMpos.le
    calc C * A ^ k * (2 * (T : ℝ) ^ 2)
        = (2 * C) * A ^ k * (T : ℝ) ^ 2 := by ring
      _ ≤ (c * (M : ℝ)) * A ^ k * (T : ℝ) ^ 2 := by gcongr
      _ = c * (A ^ k * (M : ℝ)) * (T : ℝ) ^ 2 := by ring
      _ ≤ c * (T : ℝ) * (T : ℝ) ^ 2 := by gcongr
      _ = c * (T : ℝ) ^ 3 := by ring
  have hsurvive : c / (2 * (E : ℝ)) ≤ c / (E : ℝ) - C * A ^ k * (E : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hdouble : c / (E : ℝ) = 2 * (c / (2 * (E : ℝ))) := by ring
    linarith
  have hEupper : (E : ℝ) ≤ 4 * (M : ℝ) ^ 2 * A ^ (2 * k) := by
    rw [hEcast, hTcast]
    calc ((M : ℝ) * (B : ℝ)) ^ 2
        ≤ ((M : ℝ) * (2 * A ^ k)) ^ 2 := by gcongr
      _ = 4 * (M : ℝ) ^ 2 * (A ^ k) ^ 2 := by ring
      _ = 4 * (M : ℝ) ^ 2 * A ^ (2 * k) := by rw [← pow_mul, mul_comm k 2]
  have hfinal : c / (8 * (M : ℝ) ^ 2) / A ^ (2 * k) ≤ c / (2 * (E : ℝ)) := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc c * (2 * (E : ℝ))
        ≤ c * (2 * (4 * (M : ℝ) ^ 2 * A ^ (2 * k))) := by gcongr
      _ = c * (8 * (M : ℝ) ^ 2 * A ^ (2 * k)) := by ring
  exact hfinal.trans (hsurvive.trans (hbound A hA E hE))


lemma rpow_partial_tail_le_gen (M : ℕ) {p : ℝ} (hp : 1 < p) :
    ∑ i ∈ Finset.Ico 1 M, ((i : ℝ) + 1) ^ (-p) ≤ 1 / (p - 1) := by
  rcases Nat.lt_or_ge M 1 with hM1 | hM1
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have : 0 < p - 1 := by linarith
    positivity
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc ((1 : ℕ) : ℝ) (M : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (by norm_num) hx.1) hxy (by linarith)
  have hstep := hanti.sum_le_integral_Ico hM1
  refine le_trans (by exact_mod_cast hstep) ?_
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by exact_mod_cast hM1 : (1 : ℝ) ≤ M)]
    intro h
    linarith [h.1]⟩)]
  have hneg : -p + 1 < 0 := by linarith
  rw [Real.one_rpow, div_le_iff_of_neg hneg]
  have h1 : 1 / (p - 1) * (-p + 1) = -1 := by
    have : p - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h1]
  have hMnn : 0 ≤ (M : ℝ) ^ (-p + 1) := Real.rpow_nonneg hM0.le (-p + 1)
  linarith

lemma Sp_toReal_le {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    (_root_.Represented.Sp p).toReal ≤ 2 / (p - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hf : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-p) := fun n => Real.rpow_nonneg (by positivity) _
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) := by
    have heq : (fun n : ℕ => (n : ℝ) ^ (-p)) = (fun r : ℕ => 1 / (r : ℝ) ^ p) := by
      funext r; rw [Real.rpow_neg (by positivity), one_div]
    rw [heq]; exact (Real.summable_one_div_nat_rpow).mpr hp1
  have hSp_eq : (_root_.Represented.Sp p).toReal = ∑' n : ℕ, (n : ℝ) ^ (-p) := by
    rw [_root_.Represented.Sp, ← ENNReal.ofReal_tsum_of_nonneg hf hsum,
        ENNReal.toReal_ofReal (tsum_nonneg hf)]
  rw [hSp_eq]
  refine Real.tsum_le_of_sum_le hf (fun s => ?_)
  set M := s.sup id + 1 with hMdef
  have hsub : s ⊆ Finset.range (M + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have : n ≤ s.sup id := Finset.le_sup (f := id) hn
    omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)) ?_
  have hrange : Finset.range (M + 1) = {0, 1} ∪ (Finset.Ico 1 M).image (· + 1) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_Ico]
    constructor
    · intro hn
      rcases n with _ | _ | n
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨n + 1, ⟨by omega, by omega⟩, rfl⟩
    · rintro ((rfl | rfl) | ⟨i, hi, rfl⟩) <;> omega
  have hdisj : Disjoint ({0, 1} : Finset ℕ) ((Finset.Ico 1 M).image (· + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hxim
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_image, Finset.mem_Ico] at hxim
    rcases hx with rfl | rfl <;> obtain ⟨i, hi, hi2⟩ := hxim <;> omega
  rw [hrange, Finset.sum_union hdisj, Finset.sum_pair (by decide : (0:ℕ) ≠ 1),
      Finset.sum_image (fun a _ b _ h => by omega)]
  have h01 : ((0 : ℕ) : ℝ) ^ (-p) + ((1 : ℕ) : ℝ) ^ (-p) = 1 := by
    rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hp0), Nat.cast_one, Real.one_rpow, zero_add]
  rw [h01]
  have htail : ∑ x ∈ Finset.Ico 1 M, ((x + 1 : ℕ) : ℝ) ^ (-p) ≤ 1 / (p - 1) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) (rpow_partial_tail_le_gen M hp1)
    rw [Nat.cast_add, Nat.cast_one]
  have h1le : 1 ≤ 1 / (p - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have htwo : 1 / (p - 1) + 1 / (p - 1) = 2 / (p - 1) := by ring
  linarith

/-- Uniform two-parameter odd-tail bound using the linear sifted density `c₁ / E`
and the fixed-exponent (`β = 1/2`) second-moment error `C * A^3 * E^(-3/2)`. -/
theorem explicit_linear_sieve_second_moment_bound :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (A : ℝ), 1 ≤ A → ∀ E : ℕ, 2 ≤ E →
        c / (E : ℝ) - C * A ^ 3 * (E : ℝ) ^ (-(3 / 2 : ℝ)) ≤
          _root_.Represented.lowerDensity
            (fun N : ℕ => Odd N ∧ N ∈ _root_.Represented.R ∧
              A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ)) := by
  obtain ⟨c₁, hc₁pos, hsift⟩ := sift_density_linear_lb
  obtain ⟨C₅, hC₅pos, hlarge⟩ := large_e_bound_cubed
  refine ⟨c₁, C₅, hc₁pos, hC₅pos, ?_⟩
  intro A hA E hE
  have hE1 : 1 ≤ E := by omega
  have hδ : c₁ / (E : ℝ) ≤ _root_.Represented.δ E := hsift E hE
  have hH : ∀ X : ℕ,
      (_root_.Represented.countUpTo (_root_.Represented.Hset A E) X : ℝ) ≤
        (C₅ * A ^ 3 * (E : ℝ) ^ (-(3 / 2 : ℝ))) * X :=
    hlarge A hA E hE1
  have hmain := lowerDensity_odd_gt_of_Hset_bound A (C₅ * A ^ 3 * (E : ℝ) ^ (-(3 / 2 : ℝ))) E hE hH
  linarith

/-- Logarithm-free `c / A^6` lower-density bound from the fixed-exponent (`β = 1/2`)
second moment and linear sifted-density bound. -/
theorem pure_power_six_lower_density_odd :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : ℝ, 1 ≤ A →
        c / A ^ 6 ≤
          _root_.Represented.lowerDensity
            (fun N : ℕ => Odd N ∧ N ∈ _root_.Represented.R ∧
              A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ)) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hbound⟩ := explicit_linear_sieve_second_moment_bound
  simpa using optimize_power_bound (k := 3) hc₀ hC₀
    (fun A N => Odd N ∧ N ∈ _root_.Represented.R ∧
      A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ))
    hbound

/-- Logarithm-free `c / A^6` lower-density bound inside any `HasOddDensityOne` set `S`. -/
theorem pure_power_six_lower_density_odd_in_odd_density_one :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Set ℕ), _root_.Erdos1054.OddTail.HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / A ^ 6 ≤
            _root_.Represented.lowerDensity
              (fun N : ℕ => N ∈ S ∧ Odd N ∧ N ∈ _root_.Represented.R ∧
                A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ)) := by
  obtain ⟨c, hc, hbound⟩ := pure_power_six_lower_density_odd
  refine ⟨c, hc, ?_⟩
  intro S hS A hA
  rw [_root_.Erdos1054.OddTail.lower_density_odd_inter_eq S hS
    (fun N : ℕ => N ∈ _root_.Represented.R ∧
      A * (N : ℝ) < (_root_.Erdos1054.OriginalNth.f N : ℝ))]
  exact hbound A hA

end Erdos1054.SecondMoment
