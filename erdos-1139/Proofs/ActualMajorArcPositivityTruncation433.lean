module

public import ActualMajorArcPositivityComposite433

@[expose] public section


/-!
# Sharp truncation of the actual generic rational-center singular series

The genuine signed three-form coefficient is `μ(q)/φ(q)^2`.  It is exactly
the independently audited Goldbach arithmetic coefficient at target `1`, so
its absolute summability follows from the existing proved squarefree-totient
estimate.  Excluding every prime dividing an arbitrary fixed even support
modulus preserves multiplicativity and summability.  The actual sharp
denominator truncations therefore converge to their positive Euler product.

No statement in this file asserts an integrated prime major-arc asymptotic.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos689

/-- At frequency one, the imported integer Ramanujan sum is exactly the
actual Möbius value at every positive or zero denominator. -/
theorem actualMajorArcTruncation_cRam_one_eq_moebius
    (modulus : ℕ) :
    GoldbachChain.MajorArcMainTerm.cRam modulus 1 =
      ArithmeticFunction.moebius modulus := by
  rcases Nat.eq_zero_or_pos modulus with rfl | hmodulus
  · simp [GoldbachChain.MajorArcMainTerm.cRam]
  · have hbridge :
        actualMajorArcUnitResiduePhase modulus (1 : ℤ) =
          GoldbachChain.MajorArcMainTerm.ramSum modulus 1 := by
      unfold actualMajorArcUnitResiduePhase
        GoldbachChain.MajorArcMainTerm.ramSum
      simp
    have hphase := actualMajorArcUnitResiduePhase_eq_moebius
      modulus 1 hmodulus (by simp)
    rw [hbridge,
      GoldbachChain.MajorArcMainTerm.ramSum_eq_cRam
        modulus 1 hmodulus] at hphase
    exact_mod_cast hphase

/-- The actual signed three-prime center coefficient is IDENTICALLY the
already audited Goldbach arithmetic-function value at target one. -/
theorem actualMajorArcTruncation_coefficient_eq_goldbach
    (modulus : ℕ) :
    actualMajorArcGenericSignedCoefficient modulus =
      GoldbachChain.MajorArcMainTerm.Tarith 1 modulus := by
  rw [actualMajorArcGenericSignedCoefficient_apply,
    GoldbachChain.MajorArcMainTerm.Tarith_apply,
    actualMajorArcTruncation_cRam_one_eq_moebius modulus]
  obtain hzero | hone | hminus :=
    ArithmeticFunction.moebius_eq_or modulus
  · rw [hzero]
    norm_num
  · rw [hone]
    norm_num
  · rw [hminus]
    norm_num

/-- Absolute summability of the genuine signed rational-center coefficients;
this is a proved imported totient bound, not an assumed Euler tail. -/
theorem actualMajorArcTruncation_signedCoefficient_norm_summable :
    Summable (fun modulus : ℕ =>
      ‖actualMajorArcGenericSignedCoefficient modulus‖) := by
  simpa only [actualMajorArcTruncation_coefficient_eq_goldbach] using
    GoldbachChain.MajorArcMainTerm.Tarith_summable 1 (by norm_num)

/-- Remove exactly the rational denominators meeting a fixed support and
coefficient modulus; all other coefficients remain the actual signed ones. -/
noncomputable def actualMajorArcRestrictedSignedCoefficient
    (excluded : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun modulus => if Nat.Coprime modulus excluded then
      actualMajorArcGenericSignedCoefficient modulus else 0, by
        simp⟩

/-- Exact pointwise form of the support-restricted genuine center term. -/
theorem actualMajorArcRestrictedSignedCoefficient_apply
    (excluded modulus : ℕ) :
    actualMajorArcRestrictedSignedCoefficient excluded modulus =
      if Nat.Coprime modulus excluded then
        actualMajorArcGenericSignedCoefficient modulus else 0 := rfl

/-- Fixed-support denominator deletion preserves the actual CRT
multiplicativity of the three-prime rational-center coefficient. -/
theorem actualMajorArcRestrictedSignedCoefficient_isMultiplicative
    (excluded : ℕ) :
    (actualMajorArcRestrictedSignedCoefficient excluded).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [actualMajorArcRestrictedSignedCoefficient_apply,
      actualMajorArcGenericSignedCoefficient_apply]
  · intro left right hcoprime
    simp only [actualMajorArcRestrictedSignedCoefficient_apply,
      Nat.coprime_mul_iff_left]
    by_cases hleft : Nat.Coprime left excluded <;>
      by_cases hright : Nat.Coprime right excluded
    · rw [if_pos ⟨hleft, hright⟩, if_pos hleft, if_pos hright]
      exact actualMajorArcGenericSignedCoefficient_isMultiplicative.2
        hcoprime
    · rw [if_neg (by tauto), if_pos hleft, if_neg hright,
        mul_zero]
    · rw [if_neg (by tauto), if_neg hleft, if_pos hright,
        zero_mul]
    · rw [if_neg (by tauto), if_neg hleft, if_neg hright,
        zero_mul]

/-- Arbitrarily many excluded support primes do not obstruct absolute
convergence of the genuine signed rational-center series. -/
theorem actualMajorArcRestrictedSignedCoefficient_norm_summable
    (excluded : ℕ) :
    Summable (fun modulus : ℕ =>
      ‖actualMajorArcRestrictedSignedCoefficient excluded modulus‖) := by
  apply Summable.of_nonneg_of_le
    (fun modulus => norm_nonneg
      (actualMajorArcRestrictedSignedCoefficient excluded modulus))
    _ actualMajorArcTruncation_signedCoefficient_norm_summable
  intro modulus
  rw [actualMajorArcRestrictedSignedCoefficient_apply]
  split <;> simp

/-- All prime powers beyond exponent one have genuinely zero
support-restricted signed rational-center coefficient. -/
theorem actualMajorArcRestrictedSignedCoefficient_prime_power_zero
    (excluded p exponent : ℕ)
    (hp : p.Prime) (hexponent : 2 ≤ exponent) :
    actualMajorArcRestrictedSignedCoefficient excluded
      (p ^ exponent) = 0 := by
  rw [actualMajorArcRestrictedSignedCoefficient_apply]
  split
  · rw [actualMajorArcGenericSignedCoefficient_apply,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
    · norm_num
    · rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      rintro ⟨_, hone⟩
      omega
  · rfl

/-- Exact local Euler sum after excluding any fixed support modulus.  An
excluded prime contributes `1`; any other prime contributes its genuine
signed correction. -/
theorem actualMajorArcRestrictedSignedCoefficient_local
    (excluded p : ℕ) (hp : p.Prime) :
    (∑' exponent : ℕ,
      actualMajorArcRestrictedSignedCoefficient excluded
        (p ^ exponent)) =
      1 + actualMajorArcRestrictedSignedCoefficient excluded p := by
  have hsupport : ∀ exponent ∉ ({0, 1} : Finset ℕ),
      actualMajorArcRestrictedSignedCoefficient excluded
        (p ^ exponent) = 0 := by
    intro exponent hnot
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
    push Not at hnot
    exact actualMajorArcRestrictedSignedCoefficient_prime_power_zero
      excluded p exponent hp (by omega)
  rw [tsum_eq_sum hsupport, Finset.sum_pair (by norm_num),
    pow_zero, pow_one,
    (actualMajorArcRestrictedSignedCoefficient_isMultiplicative excluded).1]

/-- Every support-free prime Euler factor is the exact actual finite-field
three-form factor, while every excluded prime Euler factor is exactly one. -/
theorem actualMajorArcRestrictedSignedCoefficient_prime_factor
    (excluded p : ℕ) (hp : p.Prime) :
    1 + actualMajorArcRestrictedSignedCoefficient excluded p =
      if Nat.Coprime p excluded then
        actualMajorArcGenericLocalFactor p else 1 := by
  rw [actualMajorArcRestrictedSignedCoefficient_apply]
  split
  · rw [actualMajorArcGenericSignedCoefficient_prime p hp,
      actualMajorArcGenericLocalFactor_eq_one_sub_inverse_square
        p hp.one_lt]
    ring
  · ring

/-- EVERY finite Euler product for the actual signed center coefficient,
with any fixed EVEN exclusion modulus, has the same absolute lower bound
`1/2`.  All support-dividing and coefficient-dividing primes are omitted. -/
theorem actualMajorArcRestrictedSignedCoefficient_partial_product_ge_half
    (excluded : ℕ) (heven : 2 ∣ excluded)
    (primes : Finset Nat.Primes) :
    (1 / 2 : ℝ) ≤
      ∏ p ∈ primes,
        (1 + actualMajorArcRestrictedSignedCoefficient excluded
          (p : ℕ)) := by
  classical
  let active : Finset Nat.Primes :=
    primes.filter fun p => Nat.Coprime (p : ℕ) excluded
  let naturalActive : Finset ℕ :=
    active.image fun p : Nat.Primes => (p : ℕ)
  have hrewrite :
      (∏ p ∈ primes,
        (1 + actualMajorArcRestrictedSignedCoefficient excluded
          (p : ℕ))) =
        ∏ p ∈ active, actualMajorArcGenericLocalFactor (p : ℕ) := by
    calc
      (∏ p ∈ primes,
        (1 + actualMajorArcRestrictedSignedCoefficient excluded
          (p : ℕ))) =
          ∏ p ∈ primes, if Nat.Coprime (p : ℕ) excluded then
            actualMajorArcGenericLocalFactor (p : ℕ) else 1 := by
          apply Finset.prod_congr rfl
          intro p hp
          exact actualMajorArcRestrictedSignedCoefficient_prime_factor
            excluded (p : ℕ) p.2
      _ = ∏ p ∈ active,
          actualMajorArcGenericLocalFactor (p : ℕ) := by
          exact (Finset.prod_filter
            (fun p : Nat.Primes => Nat.Coprime (p : ℕ) excluded)
            (fun p : Nat.Primes => actualMajorArcGenericLocalFactor
              (p : ℕ))).symm
  have hnatural :
      (∏ p ∈ active, actualMajorArcGenericLocalFactor (p : ℕ)) =
        ∏ p ∈ naturalActive, actualMajorArcGenericLocalFactor p := by
    dsimp [naturalActive]
    rw [Finset.prod_image]
    intro p hp q hq hequal
    exact Subtype.ext hequal
  rw [hrewrite, hnatural]
  apply actualMajorArcGenericLocalFactor_product_ge_half
  intro p hp
  obtain ⟨q, hq, hequal⟩ := Finset.mem_image.mp hp
  have hqprime := q.2
  have hqcoprime : Nat.Coprime (q : ℕ) excluded :=
    (Finset.mem_filter.mp hq).2
  have hqnot : (q : ℕ) ≠ 2 := by
    intro htwo
    have hcopTwo : Nat.Coprime 2 excluded := by
      simpa [htwo] using hqcoprime
    have hone : excluded.gcd 2 = 1 := hcopTwo.symm
    have htwoDvd : excluded.gcd 2 = 2 := Nat.gcd_eq_right heven
    omega
  have hqtwo := hqprime.two_le
  omega

/-- The complete convergent Euler series of genuine signed rational-center
coefficients, excluding ANY fixed even modulus, is uniformly at least
`1/2`.  Both its convergence and its CRT product are actual proved theorems. -/
theorem actualMajorArcRestrictedSignedCoefficient_tsum_ge_half
    (excluded : ℕ) (heven : 2 ∣ excluded) :
    (1 / 2 : ℝ) ≤
      ∑' modulus : ℕ,
        actualMajorArcRestrictedSignedCoefficient excluded modulus := by
  have hproduct :
      HasProd (fun p : Nat.Primes =>
          1 + actualMajorArcRestrictedSignedCoefficient excluded
            (p : ℕ))
        (∑' modulus : ℕ,
          actualMajorArcRestrictedSignedCoefficient excluded modulus) := by
    have heuler :=
      ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd
        (actualMajorArcRestrictedSignedCoefficient_isMultiplicative excluded)
        (actualMajorArcRestrictedSignedCoefficient_norm_summable excluded)
    have hlocal :
        (fun p : Nat.Primes =>
          ∑' exponent : ℕ,
            actualMajorArcRestrictedSignedCoefficient excluded
              ((p : ℕ) ^ exponent)) =
          (fun p : Nat.Primes =>
            1 + actualMajorArcRestrictedSignedCoefficient excluded
              (p : ℕ)) := by
      funext p
      exact actualMajorArcRestrictedSignedCoefficient_local
        excluded (p : ℕ) p.2
    rwa [hlocal] at heuler
  exact ge_of_tendsto hproduct
    (Filter.Eventually.of_forall fun primes =>
      actualMajorArcRestrictedSignedCoefficient_partial_product_ge_half
        excluded heven primes)

/-- Sharp denominator truncation `1 ≤ q ≤ P` converges to the COMPLETE
actual fixed-support signed Euler series.  This is the true Farey cutoff,
not the easier set of divisors of a primorial. -/
theorem actualMajorArcRestrictedSignedCoefficient_sharp_truncation_tendsto
    (excluded : ℕ) :
    Tendsto
      (fun cutoff : ℕ =>
        ∑ modulus ∈ Finset.Icc 1 cutoff,
          actualMajorArcRestrictedSignedCoefficient excluded modulus)
      atTop
      (nhds (∑' modulus : ℕ,
        actualMajorArcRestrictedSignedCoefficient excluded modulus)) := by
  have hsummable :
      Summable (fun modulus : ℕ =>
        actualMajorArcRestrictedSignedCoefficient excluded modulus) :=
    summable_norm_iff.mp
      (actualMajorArcRestrictedSignedCoefficient_norm_summable excluded)
  have hrange :=
    hsummable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  change Tendsto
    (fun cutoff : ℕ =>
      ∑ modulus ∈ Finset.range (cutoff + 1),
        actualMajorArcRestrictedSignedCoefficient excluded modulus)
    atTop
    (nhds (∑' modulus : ℕ,
      actualMajorArcRestrictedSignedCoefficient excluded modulus)) at hrange
  have hfunctions :
      (fun cutoff : ℕ =>
        ∑ modulus ∈ Finset.range (cutoff + 1),
          actualMajorArcRestrictedSignedCoefficient excluded modulus) =
        (fun cutoff : ℕ =>
          ∑ modulus ∈ Finset.Icc 1 cutoff,
            actualMajorArcRestrictedSignedCoefficient excluded modulus) := by
    funext cutoff
    have hfinset : Finset.range (cutoff + 1) =
        insert 0 (Finset.Icc 1 cutoff) := by
      ext modulus
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hfinset, Finset.sum_insert (by simp)]
    simp
  rw [hfunctions] at hrange
  exact hrange

/-- The ACTUAL sharp denominator cutoff eventually has positive signed
mass at least `1/4`, with the same absolute constant for every fixed even
support exclusion modulus. -/
theorem actualMajorArcRestrictedSignedCoefficient_sharp_truncation_ge_quarter
    (excluded : ℕ) (heven : 2 ∣ excluded) :
    ∀ᶠ cutoff : ℕ in atTop,
      (1 / 4 : ℝ) ≤
        ∑ modulus ∈ Finset.Icc 1 cutoff,
          actualMajorArcRestrictedSignedCoefficient excluded modulus := by
  have hlimit :=
    actualMajorArcRestrictedSignedCoefficient_sharp_truncation_tendsto
      excluded
  have hpositive :
      (1 / 4 : ℝ) <
        ∑' modulus : ℕ,
          actualMajorArcRestrictedSignedCoefficient excluded modulus :=
    lt_of_lt_of_le (by norm_num)
      (actualMajorArcRestrictedSignedCoefficient_tsum_ge_half
        excluded heven)
  filter_upwards [(tendsto_order.1 hlimit).1 _ hpositive]
    with cutoff hcutoff
  exact hcutoff.le

/-- The sharp positive denominator truncation remains valid for the EXACT
fully compatible manuscript cutoff `P(n)=floor(log n)^12`. -/
theorem actualMajorArcRestrictedSignedCoefficient_compatible_cutoff_ge_quarter
    (excluded : ℕ) (heven : 2 ∣ excluded) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) ≤
        ∑ modulus ∈ Finset.Icc 1 (compatibleLogMinorCutoff n),
          actualMajorArcRestrictedSignedCoefficient excluded modulus := by
  exact compatibleLogMinorCutoff_tendsto_atTop.eventually
    (actualMajorArcRestrictedSignedCoefficient_sharp_truncation_ge_quarter
      excluded heven)

/-- The exact genuine sharp-cutoff singular series, written DIRECTLY as the
sum of all actual three-form signed rational-center phases, eventually has
absolute lower bound `1/4`.  Denominators are coprime to both the real
support modulus `W` and the actual affine coefficient product `2*a*d`.
The cutoff is exactly `floor(log n)^12`, and every reduced numerator is
included; no primorial or divisor-complete truncation is substituted. -/
theorem actualMajorArcComposite_sharp_signed_phase_ge_quarter
    (a d supportModulus : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) ≤
        ∑ denominator ∈
            (Finset.Icc 1 (compatibleLogMinorCutoff n)).filter
              (fun denominator =>
                Nat.Coprime denominator
                  (2 * a * d * supportModulus)),
          ((∑ numerator ∈ (Finset.range denominator).filter
              (fun numerator => Nat.gcd numerator denominator = 1),
            actualMajorArcGenericPrimeCenterPhase
              denominator a d numerator) /
                (Nat.totient denominator : ℂ) ^ 3).re := by
  let excluded := 2 * a * d * supportModulus
  have heven : 2 ∣ excluded := by
    refine ⟨a * d * supportModulus, ?_⟩
    dsimp [excluded]
    ring
  have hcutoff :=
    actualMajorArcRestrictedSignedCoefficient_compatible_cutoff_ge_quarter
      excluded heven
  filter_upwards [hcutoff] with n hn
  calc
    (1 / 4 : ℝ) ≤
        ∑ denominator ∈ Finset.Icc 1 (compatibleLogMinorCutoff n),
          actualMajorArcRestrictedSignedCoefficient excluded
            denominator := hn
    _ = ∑ denominator ∈
          (Finset.Icc 1 (compatibleLogMinorCutoff n)).filter
            (fun denominator => Nat.Coprime denominator excluded),
          actualMajorArcGenericSignedCoefficient denominator := by
      simp_rw [actualMajorArcRestrictedSignedCoefficient_apply]
      rw [← Finset.sum_filter]
    _ = ∑ denominator ∈
          (Finset.Icc 1 (compatibleLogMinorCutoff n)).filter
            (fun denominator =>
              Nat.Coprime denominator
                (2 * a * d * supportModulus)),
          ((∑ numerator ∈ (Finset.range denominator).filter
              (fun numerator => Nat.gcd numerator denominator = 1),
            actualMajorArcGenericPrimeCenterPhase
              denominator a d numerator) /
                (Nat.totient denominator : ℂ) ^ 3).re := by
      dsimp [excluded]
      apply Finset.sum_congr rfl
      intro denominator hdenominator
      obtain ⟨hinterval, hcoprime⟩ :=
        Finset.mem_filter.mp hdenominator
      have hpositive : 0 < denominator :=
        (Finset.mem_Icc.mp hinterval).1
      have hcoefficient : Nat.Coprime denominator (2 * a * d) := by
        apply hcoprime.coprime_dvd_right
        exact ⟨supportModulus, rfl⟩
      rw [actualMajorArcCompositeCenter_signed_correction
        denominator a d hpositive hcoefficient]
      have hcast :
          (((ArithmeticFunction.moebius denominator : ℝ) /
              (Nat.totient denominator : ℝ) ^ 2 : ℝ) : ℂ) =
            (ArithmeticFunction.moebius denominator : ℂ) /
              (Nat.totient denominator : ℂ) ^ 2 := by
        push_cast
        rfl
      rw [← hcast, Complex.ofReal_re,
        actualMajorArcGenericSignedCoefficient_apply]


end Erdos689
