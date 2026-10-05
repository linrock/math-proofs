module

public import SharpSecondMoment1054

@[expose] public section


/-!
# Erdős Problem 1054: complete proved endpoints

This module exports the 21 proved theorems declared in `Challenge.lean`,
resolving all three parts of Erdős Problem 1054 (`answer_i`, `answer_ii`,
`answer_iii` and their Formal Conjectures `False ↔` / `True ↔` counterparts
`official_answer_i`, `official_answer_ii`, `official_answer_iii`) together with
the sharp second-moment odd-density lower bound `c / [A^3 (1 + log A)^4]`, the
Tao–Kovač small-ratio upper bound `C * δ^3 * X` and Goldbach-free density-zero
refutation, unconditional zero liminf on represented integers, and the two-way
cofactor-two aliquot range density equivalence. This module never imports
`Challenge.lean`.
-/

open Finset Filter Asymptotics
open scoped Topology

namespace Erdos1054.Palomar

/-- The exact official zero-padded divisor-prefix minimum, including its
zero-modulus endpoint and its zero value when no modulus represents `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  if h : ∃ m : ℕ, ∃ k : ℕ, 1 ≤ k ∧
      n = ∑ i ∈ Finset.Iio k,
        Nat.nth (fun d => d ∈ m.divisors) i then
    Nat.find h
  else 0

/-- The literal natural-number partial-density expression in the official
problem, without simplifying its two intersections with `Set.univ`. -/
def HasDensityOne (S : Set ℕ) : Prop :=
  Tendsto
    (fun b : ℕ =>
      ((((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
        ((Set.univ ∩ Set.Iio b).ncard : ℝ)))
    atTop (𝓝 1)

/-- Only the odd integers missing from `S` have density zero. This exact
Mathlib-only hypothesis places no condition on the even members of `S`. -/
def HasOddDensityOne (S : Set ℕ) : Prop :=
  (fun X : ℕ =>
    (({n : ℕ | n ≤ X ∧ Odd n ∧ n ∉ S}).ncard : ℝ))
    =o[atTop] (fun X : ℕ => (X : ℝ))

/-- Lower asymptotic density, specified using only Mathlib and the actual
closed initial interval; no proof-specific counting definition is trusted. -/
noncomputable def lowerDensity (P : ℕ → Prop) : ℝ :=
  liminf
    (fun X : ℕ =>
      ((({n : ℕ | n ≤ X ∧ P n}).ncard : ℝ) / (X : ℝ)))
    atTop

/-- The local statement-only minimizer is exactly the fully audited official
minimizer at every natural number; no representability hypothesis is needed. -/
private theorem f_eq_original (n : ℕ) :
    f n = _root_.Erdos1054.OriginalNth.f n := by
  simpa only [f] using
    (_root_.Erdos1054.OriginalNth.f_eq_official_formula n).symm

/-- Answer to original question (i): the official function is not `o(n)`. -/
theorem answer_i :
    ¬ (fun n : ℕ => (f n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  simpa only [f_eq_original] using
    _root_.Erdos1054.Unconditional.answer_i

/-- Answer to original question (ii): there is no density-one set on whose
actual subtype the official function is `o(n)`. -/
theorem answer_ii :
    ¬ ∃ S : Set ℕ, HasDensityOne S ∧
      (fun n : S => (f (n : ℕ) : ℝ))
        =o[atTop] (fun n : S => ((n : ℕ) : ℝ)) := by
  rintro ⟨S, hS, hsmall⟩
  apply _root_.Erdos1054.Unconditional.answer_ii_official_density
  refine ⟨S, hS, ?_⟩
  simpa only [f_eq_original] using hsmall

/-- Answer to original question (iii): the official extended-real limsup is
infinite, including the official question's redundant density-one witness. -/
theorem answer_iii :
    ∃ S : Set ℕ, HasDensityOne S ∧
      atTop.limsup (fun n : ℕ => (f n : EReal) / n) = ⊤ := by
  obtain ⟨S, hS, hlimsup⟩ :=
    _root_.Erdos1054.Unconditional.answer_iii_official_density
  refine ⟨S, hS, ?_⟩
  simpa only [f_eq_original] using hlimsup

/-- The literal resolved answer shape of the official first question. -/
theorem official_answer_i :
    False ↔ (fun n : ℕ => (f n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ)) :=
  ⟨False.elim, answer_i⟩

/-- The literal resolved answer shape of the official second question. -/
theorem official_answer_ii :
    False ↔ ∃ S : Set ℕ, HasDensityOne S ∧
      (fun n : S => (f (n : ℕ) : ℝ))
        =o[atTop] (fun n : S => ((n : ℕ) : ℝ)) :=
  ⟨False.elim, answer_ii⟩

/-- The literal resolved answer shape of the official third question. -/
theorem official_answer_iii :
    True ↔ ∃ S : Set ℕ, HasDensityOne S ∧
      atTop.limsup (fun n : ℕ => (f n : EReal) / n) = ⊤ :=
  ⟨fun _ => answer_iii, fun _ => True.intro⟩

/-- Stronger subtype-restricted form of question (iii): the extended-real
limsup of `f(n)/n` is infinite when restricted to the actual subtype of
*every* density-one set `S`. -/
theorem limsup_on_every_density_one
    (S : Set ℕ) (hS : HasDensityOne S) :
    (atTop : Filter S).limsup
      (fun n : S => (f (n : ℕ) : EReal) / (n : ℕ)) = ⊤ := by
  have hSorig : _root_.Erdos1054.HasDensityOne S :=
    (_root_.Erdos1054.hasDensityOne_iff_official_formula S).mpr hS
  simpa only [f_eq_original] using
    _root_.Erdos1054.StatementAudit.limsup_on_every_density_one S hSorig

/-- The exact original ratio has infinite extended-real limsup on the actual
ordered subtype of surviving odd integers inside any `HasOddDensityOne` set `S`. -/
theorem odd_subtype_limsup
    (S : Set ℕ) (hS : HasOddDensityOne S) :
    (atTop : Filter {n : ℕ // n ∈ S ∧ Odd n}).limsup
      (fun n : {n : ℕ // n ∈ S ∧ Odd n} =>
        (f (n : ℕ) : EReal) / (n : ℕ)) = ⊤ := by
  change _root_.Erdos1054.OddTail.HasOddDensityOne S at hS
  simpa only [f_eq_original] using
    _root_.Erdos1054.OddTail.limsup_on_odd_density_one_subtype S hS

/-- The official divisor-prefix minimum is undefined at `2`, returning the
sentinel value `0`. -/
theorem f_undefined_at_2 : f 2 = 0 := by
  rw [f_eq_original]
  exact _root_.Erdos1054.StatementAudit.official_f_undefined_at_two

/-- The official divisor-prefix minimum is undefined at `5`, returning the
sentinel value `0`. -/
theorem f_undefined_at_5 : f 5 = 0 := by
  rw [f_eq_original]
  exact _root_.Erdos1054.StatementAudit.official_f_undefined_at_five

/-! ## Section 2: Sharp Quantitative Lower-Density Bounds for Large Ratios `f(n) > A n` -/

/-- Sharp second-moment logarithmic endpoint: eliminating the three singleton
variables `R, S, T` via exact tail bounds yields a uniform lower-density bound
`c / (A^3 * (1 + log A)^4)` across all `HasOddDensityOne` sets `S` and all real
thresholds `A ≥ 1`. -/
theorem quantitative_odd_sharp_second_moment_logarithmic_endpoint :
    ∃ c : ℝ, 0 < c ∧
      ∀ S : Set ℕ, HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / (A ^ 3 * (1 + Real.log A) ^ 4) ≤
            lowerDensity
              (fun n : ℕ => n ∈ S ∧ Odd n ∧
                A * (n : ℝ) < (f n : ℝ)) := by
  obtain ⟨c, hc, hbound⟩ :=
    _root_.Erdos1054.SharpSecondMoment.sharp_second_moment_logarithmic_endpoint_odd_in_odd_density_one
  refine ⟨c, hc, fun S hS A hA => ?_⟩
  change _root_.Erdos1054.OddTail.HasOddDensityOne S at hS
  refine (hbound S hS A hA).trans (_root_.Represented.lowerDensity_mono fun n hn => ?_)
  exact ⟨hn.1, hn.2.1, by simpa only [f_eq_original] using hn.2.2.2⟩

/-- The sharp `c / (A^3 * (1 + log A)^4)` second-moment bound with explicit
finite counts and eventual cutoffs. -/
theorem quantitative_odd_sharp_second_moment_logarithmic_endpoint_eventual_count :
    ∃ c : ℝ, 0 < c ∧
      ∀ S : Set ℕ, HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
            (c / (A ^ 3 * (1 + Real.log A) ^ 4)) * (X : ℝ) ≤
              (({n : ℕ | n ≤ X ∧ n ∈ S ∧ Odd n ∧
                A * (n : ℝ) < (f n : ℝ)}).ncard : ℝ) := by
  obtain ⟨c₀, hc₀, hbound⟩ :=
    quantitative_odd_sharp_second_moment_logarithmic_endpoint
  refine ⟨c₀ / 2, by positivity, fun S hS A hA => ?_⟩
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  let P : ℕ → Prop := fun n => n ∈ S ∧ Odd n ∧ A * (n : ℝ) < (f n : ℝ)
  have hstrict : (c₀ / 2) / (A ^ 3 * (1 + Real.log A) ^ 4) <
      _root_.Represented.lowerDensity P :=
    (div_lt_div_of_pos_right (by linarith : c₀ / 2 < c₀) (by positivity)).trans_le
      (hbound S hS A hA)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun X : ℕ => (_root_.Represented.countUpTo P X : ℝ) / (X : ℝ)) :=
    ⟨0, Filter.eventually_map.2 (Filter.Eventually.of_forall fun _ => by positivity)⟩
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (eventually_lt_of_lt_liminf hstrict hbdd)
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  exact ((lt_div_iff₀ hXpos).mp (hX₀ X ((le_max_left X₀ 1).trans hX))).le

/-- Every real exponent strictly larger than three (`3 + ε`) is achieved
uniformly across all `HasOddDensityOne` sets `S` and all `A ≥ 1`. -/
theorem quantitative_odd_almost_full_three_plus_epsilon :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ S : Set ℕ, HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / A ^ (3 + ε : ℝ) ≤
            lowerDensity
              (fun n : ℕ => n ∈ S ∧ Odd n ∧
                A * (n : ℝ) < (f n : ℝ)) := by
  intro ε hε
  obtain ⟨c, hc, hbound⟩ :=
    _root_.Erdos1054.SharpSecondMoment.sharp_second_moment_three_plus_epsilon_odd_in_odd_density_one ε hε
  refine ⟨c, hc, fun S hS A hA => ?_⟩
  change _root_.Erdos1054.OddTail.HasOddDensityOne S at hS
  refine (hbound S hS A hA).trans (_root_.Represented.lowerDensity_mono fun n hn => ?_)
  exact ⟨hn.1, hn.2.1, by simpa only [f_eq_original] using hn.2.2.2⟩

/-- Logarithm-free `c / A^6` lower-density bound from the linear sifted-density
estimate `δ_E ≥ c₁ / E` and fixed-exponent (`β = 1/2`) divisibility-preserving
second moment. -/
theorem quantitative_odd_pure_power_six :
    ∃ c : ℝ, 0 < c ∧
      ∀ S : Set ℕ, HasOddDensityOne S →
        ∀ A : ℝ, 1 ≤ A →
          c / A ^ 6 ≤
            lowerDensity
              (fun n : ℕ => n ∈ S ∧ Odd n ∧
                A * (n : ℝ) < (f n : ℝ)) := by
  obtain ⟨c, hc, hbound⟩ :=
    _root_.Erdos1054.SecondMoment.pure_power_six_lower_density_odd_in_odd_density_one
  refine ⟨c, hc, fun S hS A hA => ?_⟩
  change _root_.Erdos1054.OddTail.HasOddDensityOne S at hS
  refine (hbound S hS A hA).trans (_root_.Represented.lowerDensity_mono fun n hn => ?_)
  exact ⟨hn.1, hn.2.1, by simpa only [f_eq_original] using hn.2.2.2⟩

/-! ## Section 3: Tao–Kovač Small-Ratio Upper Bounds and Strong Refutation of `f(n) = o(n)` -/

/-- Divisibility-preserving Tao–Kovač small-ratio counting bound: for every
`δ > 0` and `X`, the number of represented integers `n ≤ X` (`0 < f n`) with
`f(n) ≤ δ * n` is at most `C * δ^3 * X`. -/
theorem small_ratio_count_le_cubic :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ X : ℕ,
      (({n : ℕ | n ≤ X ∧ 0 < f n ∧
        (f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) ≤ C * δ ^ 3 * (X : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := _root_.Erdos1054.SmallRatioKovac.small_ratio_count_le_cubic
  refine ⟨C, hC, fun δ hδ X => ?_⟩
  simpa only [f_eq_original] using hbound δ hδ X

/-- Upper asymptotic density of represented integers `n` (`0 < f n`) with
`f(n) ≤ δ * n` is bounded by `C * δ^3` for all `δ > 0`. -/
theorem small_ratio_upper_density_le_cubic :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      limsup
        (fun X : ℕ =>
          (({n : ℕ | n ≤ X ∧ 0 < f n ∧
            (f n : ℝ) ≤ δ * (n : ℝ)}).ncard : ℝ) / (X : ℝ)) atTop ≤ C * δ ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := _root_.Erdos1054.SmallRatioKovac.small_ratio_upper_density_le
  refine ⟨C, hC, fun δ hδ => ?_⟩
  simpa only [f_eq_original] using hbound δ hδ

/-- Strong refutation of `f(n) = o(n)` (without Goldbach): along *any* subset
`S ⊆ ℕ` on whose subtype `f(n) = o(n)` holds, the represented members of `S`
(`0 < f n`) have natural density zero. -/
theorem littleO_on_subtype_imp_represented_density_zero
    (S : Set ℕ)
    (ho : (fun n : S => (f (n : ℕ) : ℝ))
      =o[atTop] (fun n : S => ((n : ℕ) : ℝ))) :
    Tendsto
      (fun X : ℕ =>
        (({n : ℕ | n ≤ X ∧ n ∈ S ∧ 0 < f n}).ncard : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  have ho' :
      (fun n : S => (_root_.Erdos1054.OriginalNth.f (n : ℕ) : ℝ))
        =o[atTop] (fun n : S => ((n : ℕ) : ℝ)) := by
    simpa only [f_eq_original] using ho
  simpa only [f_eq_original] using
    _root_.Erdos1054.SmallRatioKovac.littleO_on_subtype_imp_represented_density_zero S ho'

/-! ## Section 4: Small-Ratio Witnesses and Two-Way Aliquot Range Equivalence -/

/-- Every positive divisor sum `σ(n) = ∑ d ∈ n.divisors, d` (`n ≥ 1`) is
represented (`0 < f(σ(n))`) and satisfies `f(σ(n)) ≤ n`. -/
theorem f_sigma_le (n : ℕ) (hn : 1 ≤ n) :
    0 < f (∑ d ∈ n.divisors, d) ∧ f (∑ d ∈ n.divisors, d) ≤ n := by
  rw [f_eq_original, ← ArithmeticFunction.sigma_one_apply]
  exact _root_.Erdos1054.AliquotEquivalence.official_f_sigma_le n hn

/-- Unconditional zero liminf on represented integers: for every `ε > 0` and
every threshold `B`, there is a represented integer `N ≥ B` (`0 < f N`) with
`f(N) < ε * N`. -/
theorem frequently_represented_small_ratio (ε : ℝ) (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ 0 < f N ∧ (f N : ℝ) < ε * (N : ℝ) := by
  obtain ⟨N, hBN, hpos, hlt⟩ :=
    _root_.Erdos1054.AliquotEquivalence.frequently_represented_small_ratio ε hε B
  refine ⟨N, hBN, ?_, ?_⟩
  · simpa only [f_eq_original] using hpos
  · simpa only [f_eq_original] using hlt

/-- Exact two-way lower-density equivalence between the cofactor-two divisor-prefix
value range `{s(2d) : d > 0}` and the classical set of even aliquot values
`{N even : ∃ m > 0, N = s(m)}`. -/
theorem cofactor_two_lower_density_eq_even_aliquot :
    lowerDensity (fun N : ℕ => ∃ d : ℕ, 0 < d ∧ N = ∑ q ∈ (2 * d).properDivisors, q) =
      lowerDensity (fun N : ℕ => Even N ∧ ∃ m : ℕ, 0 < m ∧ N = ∑ q ∈ m.properDivisors, q) :=
  _root_.Erdos1054.AliquotEquivalence.cofactorTwo_lowerDensity_eq_evenAliquot

/-- Exact two-way upper-density equivalence between the cofactor-two divisor-prefix
value range `{s(2d) : d > 0}` and the classical set of even aliquot values
`{N even : ∃ m > 0, N = s(m)}`. -/
theorem cofactor_two_upper_density_eq_even_aliquot :
    limsup
        (fun X : ℕ =>
          (({N : ℕ | N ≤ X ∧ ∃ d : ℕ, 0 < d ∧
            N = ∑ q ∈ (2 * d).properDivisors, q}).ncard : ℝ) / (X : ℝ)) atTop =
      limsup
        (fun X : ℕ =>
          (({N : ℕ | N ≤ X ∧ Even N ∧ ∃ m : ℕ, 0 < m ∧
            N = ∑ q ∈ m.properDivisors, q}).ncard : ℝ) / (X : ℝ)) atTop :=
  _root_.Erdos1054.AliquotEquivalence.cofactorTwo_upperDensity_eq_evenAliquot

end Erdos1054.Palomar
