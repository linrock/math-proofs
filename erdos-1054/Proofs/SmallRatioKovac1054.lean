module

public import SecondMoment1054

@[expose] public section


/-!
# Tao–Kovač small-ratio upper bound and density-zero refutation of `f(n) = o(n)`

This module formalizes the `E = 0` divisibility-preserving second-moment bound
for Erdős problem #1054 and its consequences for small ratios `f(n) / n ≤ δ`:

1. **Unconditional `E = 0` series bound (`U_zero_le_ennreal`, `U_zero_lt_top`,
   `U_zero_pos`, `moment2_zero_le`)**:
   When `E = 0`, every triple `(e, r, s)` in `U 0` satisfies `1 ≤ e ≤ r, s`, so
   `e^(-3/2) ≤ 1` and `U 0` is bounded by the finite 7-fold product of convergent
   Dirichlet series `Sp(3/2) * Sp(4/3)^3 * Sp(7/6)^3 < ⊤`.

2. **Tao–Kovač small-ratio counting bounds (`small_ratio_count_le_cubic`,
   `small_ratio_count_le_quadratic`)**:
   For any `δ > 0` and `X : ℕ`, every integer `n ≤ X` with `0 < f(n) ≤ δ * n`
   belongs to `H_{δ, 0}(X)`.  Combining the truncation `m = e * d ≤ ⌊δ * X⌋`
   (factor `δ`) with Markov's inequality on `g(e, m) ≥ 1 / δ` in the second
   moment (factor `δ^2`) yields
   `#{n ≤ X : 0 < f(n) ≤ δ * n} ≤ C * δ^3 * X` for all `δ > 0`, and in
   particular `≤ C * δ^2 * X` for `0 < δ ≤ 1`.

3. **Upper-density bound and strong refutation of `f(n) = o(n)`
   (`small_ratio_upper_density_le`,
   `littleO_on_subtype_imp_represented_density_zero`)**:
   The upper asymptotic density of `{n : 0 < f(n) ≤ δ * n}` is at most `C * δ^3`.
   Consequently, for *any* subset `S : Set ℕ` on which `f(n) = o(n)` along `S`,
   the represented members of `S` have natural density zero.
-/

open Finset Filter Asymptotics MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Erdos1054.SmallRatioKovac

/-- When `E = 0`, the 3-parameter gcd/lcm series `U 0` is bounded by the finite
7-fold product of `p`-series `Sp(3/2) * Sp(4/3)^3 * Sp(7/6)^3`. -/
theorem U_zero_le_ennreal :
    _root_.Erdos1054.SecondMoment.U 0 ≤
      _root_.Represented.Sp (3 / 2) * _root_.Represented.Sp (4 / 3) *
        _root_.Represented.Sp (4 / 3) * _root_.Represented.Sp (4 / 3) *
        _root_.Represented.Sp (7 / 6) * _root_.Represented.Sp (7 / 6) *
        _root_.Represented.Sp (7 / 6) := by
  simpa using _root_.Erdos1054.SecondMoment.U_le_ennreal_max 0

/-- The full second-moment constant `U 0` is finite. -/
theorem U_zero_lt_top : _root_.Erdos1054.SecondMoment.U 0 < ⊤ :=
  _root_.Erdos1054.SecondMoment.U_lt_top_all 0

/-- The real value `(U 0).toReal` is strictly positive. -/
theorem U_zero_pos : 0 < (_root_.Erdos1054.SecondMoment.U 0).toReal := by
  refine ENNReal.toReal_pos ?_ U_zero_lt_top.ne
  rw [_root_.Erdos1054.SecondMoment.U]
  refine ne_of_gt (lt_of_lt_of_le ?_
    (ENNReal.le_tsum ((1 : ℕ), (1 : ℕ), (1 : ℕ))))
  norm_num

/-- Unconditional `E = 0` divisibility-preserving second-moment bound over all
pairs `(m, e)` with `m ≤ Z`, `e ∣ m`, and `0 < e`. -/
theorem moment2_zero_le (Z : ℕ) :
    (∑ p ∈ (Finset.range (Z + 1) ×ˢ Finset.range (Z + 1)).filter
        (fun p => p.2 ∣ p.1 ∧ 0 < p.2), (_root_.Represented.g p.2 p.1) ^ 2)
      ≤ (Z : ℝ) * (_root_.Erdos1054.SecondMoment.U 0).toReal :=
  _root_.Erdos1054.SecondMoment.moment2_le_all 0 Z

/-- For any `δ > 0` and `X : ℕ`, the number of integers `n ≤ X` in `H_{δ, 0}` is
at most `(U 0).toReal * δ^3 * X`. -/
theorem Hset_zero_bound_U (δ : ℝ) (hδ : 0 < δ) (X : ℕ) :
    (_root_.Represented.countUpTo (_root_.Represented.Hset δ 0) X : ℝ) ≤
      (_root_.Erdos1054.SecondMoment.U 0).toReal * δ ^ 3 * (X : ℝ) := by
  linarith [_root_.Erdos1054.SecondMoment.large_e_bound_U_all δ hδ 0 X]

/-- Every represented integer `n` with `f(n) ≤ δ * n` belongs to `H_{δ, 0}`. -/
lemma small_ratio_mem_Hset_zero {δ : ℝ} {n : ℕ}
    (hpos : 0 < _root_.Erdos1054.OriginalNth.f n)
    (hle : (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)) :
    _root_.Represented.Hset δ 0 n := by
  have hR : n ∈ _root_.Represented.R :=
    (_root_.Erdos1054.StatementAudit.official_f_pos_iff_represented n).mp hpos
  obtain ⟨e, d, he, hd, hfeq, hNF⟩ := _root_.Represented.f_mem_Fform n hR
  refine ⟨e, d, by omega, hd, hNF, ?_⟩
  have hcast : (e : ℝ) * (d : ℝ) = (_root_.Erdos1054.OriginalNth.f n : ℝ) := by
    rw [_root_.Erdos1054.OriginalNth.f_eq_supported, ← Nat.cast_mul, ← hfeq]
  linarith

/-- Counting bound for `{n ≤ X : 0 < f(n) ≤ δ * n}` in terms of `(U 0).toReal`:
for every `δ > 0` and `X : ℕ`, the count is at most `(U 0).toReal * δ^3 * X`. -/
theorem small_ratio_count_le_U_zero (δ : ℝ) (hδ : 0 < δ) (X : ℕ) :
    (({n : ℕ | n ≤ X ∧ 0 < _root_.Erdos1054.OriginalNth.f n ∧
      (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) ≤
        (_root_.Erdos1054.SecondMoment.U 0).toReal * δ ^ 3 * (X : ℝ) := by
  have hsub :
      {n : ℕ | n ≤ X ∧ 0 < _root_.Erdos1054.OriginalNth.f n ∧
        (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)} ⊆
      _root_.Represented.setUpTo (_root_.Represented.Hset δ 0) X := by
    rintro n ⟨hnX, hpos, hle⟩
    exact ⟨hnX, small_ratio_mem_Hset_zero hpos hle⟩
  have hncard :
      (({n : ℕ | n ≤ X ∧ 0 < _root_.Erdos1054.OriginalNth.f n ∧
        (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) ≤
      (_root_.Represented.countUpTo (_root_.Represented.Hset δ 0) X : ℝ) := by
    rw [_root_.Represented.countUpTo]
    exact_mod_cast Set.ncard_le_ncard hsub (_root_.Represented.setUpTo_finite _ X)
  exact hncard.trans (Hset_zero_bound_U δ hδ X)

/-- **Tao–Kovač small-ratio cubic counting bound**: there is an absolute constant
`C > 0` such that for all `δ > 0` and all `X : ℕ`,
`#{n ≤ X : 0 < f(n) ≤ δ * n} ≤ C * δ^3 * X`. -/
theorem small_ratio_count_le_cubic :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ X : ℕ,
      (({n : ℕ | n ≤ X ∧ 0 < _root_.Erdos1054.OriginalNth.f n ∧
        (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) ≤
          C * δ ^ 3 * (X : ℝ) :=
  ⟨(_root_.Erdos1054.SecondMoment.U 0).toReal, U_zero_pos, small_ratio_count_le_U_zero⟩

/-- **Tao–Kovač small-ratio quadratic counting bound**: there is an absolute
constant `C > 0` such that for all `0 < δ ≤ 1` and all `X : ℕ`,
`#{n ≤ X : 0 < f(n) ≤ δ * n} ≤ C * δ^2 * X`. -/
theorem small_ratio_count_le_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ X : ℕ,
      (({n : ℕ | n ≤ X ∧ 0 < _root_.Erdos1054.OriginalNth.f n ∧
        (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) ≤
          C * δ ^ 2 * (X : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := small_ratio_count_le_cubic
  refine ⟨C, hCpos, fun δ hδ hδ1 X => ?_⟩
  refine (hC δ hδ X).trans ?_
  have hpow : δ ^ 3 ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]
  have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hCpos.le) hX

/-- **Small-ratio upper asymptotic density bound**: there is an absolute constant
`C > 0` such that for every `δ > 0`, the upper asymptotic density of
`{n : 0 < f(n) ≤ δ * n}` is at most `C * δ^3`. -/
theorem small_ratio_upper_density_le :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      limsup (fun X : ℕ =>
        (({n : ℕ | n ≤ X ∧ 0 < _root_.Erdos1054.OriginalNth.f n ∧
          (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) / (X : ℝ)) atTop ≤
        C * δ ^ 3 := by
  obtain ⟨C, hCpos, hC⟩ := small_ratio_count_le_cubic
  refine ⟨C, hCpos, fun δ hδ => ?_⟩
  refine limsup_le_of_le ?_ ?_
  · refine ⟨0, fun a ha => ?_⟩
    rw [eventually_map] at ha
    obtain ⟨X, hX⟩ := ha.exists
    exact le_trans (by positivity) hX
  · filter_upwards [eventually_gt_atTop 0] with X hX
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    rw [div_le_iff₀ hXpos]
    exact hC δ hδ X

/-- **Small-ratio quadratic upper asymptotic density bound**: for `0 < δ ≤ 1`,
the upper asymptotic density of `{n : 0 < f(n) ≤ δ * n}` is at most `C * δ^2`. -/
theorem small_ratio_upper_density_le_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      limsup (fun X : ℕ =>
        (({n : ℕ | n ≤ X ∧ 0 < _root_.Erdos1054.OriginalNth.f n ∧
          (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) / (X : ℝ)) atTop ≤
        C * δ ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := small_ratio_upper_density_le
  refine ⟨C, hCpos, fun δ hδ hδ1 => (hC δ hδ).trans ?_⟩
  have hpow : δ ^ 3 ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]
  exact mul_le_mul_of_nonneg_left hpow hCpos.le

/-- If `f(n) = o(n)` along a subset `S : Set ℕ`, then the represented elements
of `S` satisfy `CountIsLittleO` (count up to `X` is `o(X)`). -/
theorem littleO_on_subtype_imp_represented_countIsLittleO
    (S : Set ℕ)
    (ho : (fun n : S => (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ))
      =o[atTop] (fun n : S => ((n : ℕ) : ℝ))) :
    _root_.Represented.CountIsLittleO
      (fun n : ℕ => n ∈ S ∧ 0 < _root_.Erdos1054.OriginalNth.f n) := by
  classical
  rw [_root_.Represented.CountIsLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  by_cases hS : Nonempty S
  · obtain ⟨C, hCpos, hC⟩ := small_ratio_count_le_cubic
    set δ : ℝ := min 1 (ε / (2 * C)) with hδdef
    have hδpos : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδC : δ ≤ ε / (2 * C) := min_le_right _ _
    have hCδ3 : C * δ ^ 3 ≤ ε / 2 := by
      have hpow : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ]
      have h1 : C * δ ^ 3 ≤ C * δ := mul_le_mul_of_nonneg_left hpow hCpos.le
      have h2 : C * δ ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left hδC hCpos.le
      have h3 : C * (ε / (2 * C)) = ε / 2 := by
        field_simp [hCpos.ne']
      linarith
    have hev := (Asymptotics.isLittleO_iff.mp ho) hδpos
    rw [eventually_atTop] at hev
    obtain ⟨m₀, hm₀⟩ := hev
    set N₀ : ℕ := (m₀ : ℕ) with hN₀def
    set X₀ : ℕ := ⌈2 * ((N₀ : ℝ) + 1) / ε⌉₊ with hX₀def
    rw [eventually_atTop]
    refine ⟨X₀, fun X hX => ?_⟩
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hsplit :
        _root_.Represented.countUpTo
          (fun n : ℕ => n ∈ S ∧ 0 < _root_.Erdos1054.OriginalNth.f n) X ≤
        _root_.Represented.countUpTo (fun n : ℕ => n ≤ N₀) X +
        _root_.Represented.countUpTo
          (fun n : ℕ => 0 < _root_.Erdos1054.OriginalNth.f n ∧
            (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)) X := by
      refine le_trans (_root_.Represented.countUpTo_mono (fun n hn => ?_) X)
        (_root_.Represented.countUpTo_or_le _ _ X)
      by_cases hnN₀ : n ≤ N₀
      · exact Or.inl hnN₀
      · right
        refine ⟨hn.2, ?_⟩
        have hm : m₀ ≤ (⟨n, hn.1⟩ : S) := by
          change N₀ ≤ n
          omega
        have hbound := hm₀ ⟨n, hn.1⟩ hm
        simpa only [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (_root_.Erdos1054.OriginalNth.f n : ℝ)),
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))] using hbound
    have hinit_nat :
        _root_.Represented.countUpTo (fun n : ℕ => n ≤ N₀) X ≤ N₀ + 1 := by
      unfold _root_.Represented.countUpTo _root_.Represented.setUpTo
      calc ({n : ℕ | n ≤ X ∧ n ≤ N₀}).ncard
          ≤ (Set.Iic N₀).ncard :=
            Set.ncard_le_ncard (fun n hn => hn.2) (Set.finite_Iic N₀)
        _ = N₀ + 1 := Set.ncard_Iic_nat N₀
    have hinit :
        (_root_.Represented.countUpTo (fun n : ℕ => n ≤ N₀) X : ℝ) ≤ (ε / 2) * (X : ℝ) := by
      have h1 : (_root_.Represented.countUpTo (fun n : ℕ => n ≤ N₀) X : ℝ) ≤ (N₀ : ℝ) + 1 := by
        exact_mod_cast hinit_nat
      have h2 : 2 * ((N₀ : ℝ) + 1) / ε ≤ (X : ℝ) := by
        calc 2 * ((N₀ : ℝ) + 1) / ε ≤ (X₀ : ℝ) := Nat.le_ceil _
          _ ≤ (X : ℝ) := by exact_mod_cast hX
      have h3 : (N₀ : ℝ) + 1 ≤ (ε / 2) * (X : ℝ) := by
        have := (div_le_iff₀ hε).mp h2
        linarith
      exact h1.trans h3
    have htail :
        (_root_.Represented.countUpTo
          (fun n : ℕ => 0 < _root_.Erdos1054.OriginalNth.f n ∧
            (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)) X : ℝ) ≤
        (ε / 2) * (X : ℝ) := by
      have h1 :
          (_root_.Represented.countUpTo
            (fun n : ℕ => 0 < _root_.Erdos1054.OriginalNth.f n ∧
              (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)) X : ℝ) ≤
          C * δ ^ 3 * (X : ℝ) := by
        simpa only [_root_.Represented.countUpTo, _root_.Represented.setUpTo] using hC δ hδpos X
      exact h1.trans (mul_le_mul_of_nonneg_right hCδ3 (Nat.cast_nonneg X))
    have hsplitR :
        (_root_.Represented.countUpTo
          (fun n : ℕ => n ∈ S ∧ 0 < _root_.Erdos1054.OriginalNth.f n) X : ℝ) ≤
        (_root_.Represented.countUpTo (fun n : ℕ => n ≤ N₀) X : ℝ) +
        (_root_.Represented.countUpTo
          (fun n : ℕ => 0 < _root_.Erdos1054.OriginalNth.f n ∧
            (_root_.Erdos1054.OriginalNth.f n : ℝ) ≤ δ * (n : ℝ)) X : ℝ) := by
      exact_mod_cast hsplit
    linarith
  · rw [not_nonempty_iff] at hS
    rw [eventually_atTop]
    refine ⟨0, fun X _ => ?_⟩
    have hempty :
        _root_.Represented.setUpTo
          (fun n : ℕ => n ∈ S ∧ 0 < _root_.Erdos1054.OriginalNth.f n) X = ∅ := by
      ext n
      simp only [_root_.Represented.setUpTo, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hnS, _⟩
      exact hS.false ⟨n, hnS⟩
    have hzero :
        _root_.Represented.countUpTo
          (fun n : ℕ => n ∈ S ∧ 0 < _root_.Erdos1054.OriginalNth.f n) X = 0 := by
      rw [_root_.Represented.countUpTo, hempty, Set.ncard_empty]
    rw [hzero, Nat.cast_zero, norm_zero]
    positivity

/-- **Strong refutation of `f(n) = o(n)` on any subset**:
for *any* set `S : Set ℕ`, if `f(n) = o(n)` along the subtype `S`, then the
represented members of `S` have natural density zero. -/
theorem littleO_on_subtype_imp_represented_density_zero
    (S : Set ℕ)
    (ho : (fun n : S => (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ))
      =o[atTop] (fun n : S => ((n : ℕ) : ℝ))) :
    Tendsto (fun X : ℕ =>
      (({n : ℕ | n ≤ X ∧ n ∈ S ∧ 0 < _root_.Erdos1054.OriginalNth.f n}).ncard : ℝ) / (X : ℝ))
      atTop (𝓝 0) :=
  (littleO_on_subtype_imp_represented_countIsLittleO S ho).tendsto_div

/-- Alias of `littleO_on_subtype_imp_represented_density_zero`. -/
theorem littleO_represented_density_zero
    (S : Set ℕ)
    (ho : (fun n : S => (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ))
      =o[atTop] (fun n : S => ((n : ℕ) : ℝ))) :
    Tendsto (fun X : ℕ =>
      (({n : ℕ | n ≤ X ∧ n ∈ S ∧ 0 < _root_.Erdos1054.OriginalNth.f n}).ncard : ℝ) / (X : ℝ))
      atTop (𝓝 0) :=
  littleO_on_subtype_imp_represented_density_zero S ho

end Erdos1054.SmallRatioKovac
