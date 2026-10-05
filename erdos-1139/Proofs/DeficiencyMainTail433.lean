module

public import DeficiencyUpper433
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section


/-!
# Uniform prime-stratum tails for the actual initial deficiency

The genuine first-power outside-prime targets have already been identified
with their moving family of even support-smooth cores and reduced residue
classes.  This file bounds those *actual* strata by ordinary prime counts,
keeps their residue multiplicity finite, and applies the fixed-support Rankin
tail to moving large-core families.
-/

open Filter
open scoped BigOperators Topology Nat.Prime

namespace Erdos689

/-- The completely elementary endpoint bound for the actual prime count. -/
theorem primeCounting_le_endpoint (n : ℕ) :
    Nat.primeCounting n ≤ n := by
  calc
    Nat.primeCounting n = (Nat.primesLE n).card :=
      (Nat.primesLE_card_eq_primeCounting n).symm
    _ ≤ (Finset.Icc 1 n).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hple, hpprime⟩ := Nat.mem_primesLE.mp hp
      exact Finset.mem_Icc.mpr ⟨hpprime.one_le, hple⟩
    _ = n := by simp

/-- Every actual reduced progression is a subset of the ordinary prime set
up to its exact natural-division endpoint. -/
theorem smoothDeficiencyPrimeStratum_subset_primesLE
    (S : Finset ℕ) (c r n : ℕ) :
    smoothDeficiencyPrimeStratum S c r n ⊆
      Nat.primesLE (n / c) := by
  intro p hp
  obtain ⟨_, hfilter⟩ := Finset.mem_erase.mp hp
  obtain ⟨hinterval, hprime, _⟩ := Finset.mem_filter.mp hfilter
  exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hinterval).2, hprime⟩

/-- Uniform honest prime-count upper bound for each actual deficiency stratum. -/
theorem smoothDeficiencyPrimeStratum_card_le_primeCounting
    (S : Finset ℕ) (c r n : ℕ) :
    (smoothDeficiencyPrimeStratum S c r n).card ≤
      Nat.primeCounting (n / c) := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact Finset.card_le_card
    (smoothDeficiencyPrimeStratum_subset_primesLE S c r n)

/-- A family of actual core/residue pairs has at most its bounded residue
multiplicity times the ordinary prime sum over its distinct smooth cores. -/
theorem smoothCorePair_prime_sum_le_residue_mul
    (S : Finset ℕ) (G : Finset (ℕ × ℕ)) (W n : ℕ)
    (hresidue : ∀ v ∈ G, v.2 < W) :
    (∑ v ∈ G, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) ≤
      W * ∑ c ∈ G.image Prod.fst, Nat.primeCounting (n / c) := by
  classical
  calc
    (∑ v ∈ G, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) ≤
        ∑ v ∈ G, Nat.primeCounting (n / v.1) := by
          apply Finset.sum_le_sum
          intro v _
          exact smoothDeficiencyPrimeStratum_card_le_primeCounting
            S v.1 v.2 n
    _ ≤ ∑ v ∈ (G.image Prod.fst).product (Finset.range W),
          Nat.primeCounting (n / v.1) := by
          apply Finset.sum_le_sum_of_subset
          intro v hv
          apply Finset.mem_product.mpr
          exact ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩,
            Finset.mem_range.mpr (hresidue v hv)⟩
    _ = ∑ c ∈ G.image Prod.fst,
          ∑ _r ∈ Finset.range W, Nat.primeCounting (n / c) :=
          Finset.sum_product (G.image Prod.fst) (Finset.range W)
            (fun v => Nat.primeCounting (n / v.1))
    _ = W * ∑ c ∈ G.image Prod.fst,
          Nat.primeCounting (n / c) := by
          simp [Finset.mul_sum]

/-- The trivial prime estimate gives an exact reciprocal-core majorant,
including nondivisible natural endpoints. -/
theorem prime_sum_le_endpoint_mass (F : Finset ℕ) (n : ℕ) :
    ((∑ c ∈ F, Nat.primeCounting (n / c)) : ℝ) ≤
      (n : ℝ) * ∑ c ∈ F, (c : ℝ)⁻¹ := by
  calc
    ((∑ c ∈ F, Nat.primeCounting (n / c)) : ℝ) =
        ∑ c ∈ F, (Nat.primeCounting (n / c) : ℝ) := by rfl
    _ ≤ ∑ c ∈ F, ((n / c : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro c _
          exact_mod_cast primeCounting_le_endpoint (n / c)
    _ ≤ ∑ c ∈ F, (n : ℝ) / (c : ℝ) := by
          apply Finset.sum_le_sum
          intro c _
          exact Nat.cast_div_le
    _ = (n : ℝ) * ∑ c ∈ F, (c : ℝ)⁻¹ := by
          simp [div_eq_mul_inv, Finset.mul_sum]

/-- Uniform Rankin majorant for any moving finite family of large fixed-support
smooth cores, with no assumption about arithmetic-progressions distribution. -/
theorem supportSmooth_prime_sum_rankin_tail
    (T F : Finset ℕ) (n : ℕ) {R θ : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθone : θ < 1)
    (hsmooth : ∀ c ∈ F, c ∈ Nat.factoredNumbers T)
    (hlarge : ∀ c ∈ F, R ≤ (c : ℝ)) :
    ((∑ c ∈ F, Nat.primeCounting (n / c)) : ℝ) ≤
      (n : ℝ) * R ^ (-θ) *
        (∏ p ∈ T with p.Prime,
          (1 - (p : ℝ) ^ (-(1 - θ)))⁻¹) := by
  have htail := supportSmooth_reciprocal_rankin_tail_finset
    T F hR hθ hθone hsmooth hlarge
  calc
    ((∑ c ∈ F, Nat.primeCounting (n / c)) : ℝ) ≤
        (n : ℝ) * ∑ c ∈ F, (c : ℝ)⁻¹ :=
      prime_sum_le_endpoint_mass F n
    _ ≤ (n : ℝ) *
          (R ^ (-θ) *
            (∏ p ∈ T with p.Prime,
              (1 - (p : ℝ) ^ (-(1 - θ)))⁻¹)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

/-- Uniform actual-core/residue Rankin bound, retaining the finite residue
multiplicity explicitly and allowing the whole family to depend on `n`. -/
theorem smoothCorePair_prime_sum_rankin_tail
    (S T : Finset ℕ) (G : Finset (ℕ × ℕ)) (W n : ℕ) {R θ : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθone : θ < 1)
    (hresidue : ∀ v ∈ G, v.2 < W)
    (hsmooth : ∀ v ∈ G, v.1 ∈ Nat.factoredNumbers T)
    (hlarge : ∀ v ∈ G, R ≤ (v.1 : ℝ)) :
    ((∑ v ∈ G, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) ≤
      (W : ℝ) * (n : ℝ) * R ^ (-θ) *
        (∏ p ∈ T with p.Prime,
          (1 - (p : ℝ) ^ (-(1 - θ)))⁻¹) := by
  classical
  let cores := G.image Prod.fst
  have hcoresmooth : ∀ c ∈ cores, c ∈ Nat.factoredNumbers T := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact hsmooth v hv
  have hcorelarge : ∀ c ∈ cores, R ≤ (c : ℝ) := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact hlarge v hv
  have hpair := smoothCorePair_prime_sum_le_residue_mul S G W n hresidue
  have hcore := supportSmooth_prime_sum_rankin_tail
    T cores n hR hθ hθone hcoresmooth hcorelarge
  calc
    ((∑ v ∈ G, (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) ≤
        ((W * ∑ c ∈ cores, Nat.primeCounting (n / c) : ℕ) : ℝ) := by
          exact_mod_cast hpair
    _ = (W : ℝ) * ((∑ c ∈ cores, Nat.primeCounting (n / c)) : ℝ) := by
          push_cast
          rfl
    _ ≤ (W : ℝ) *
          ((n : ℝ) * R ^ (-θ) *
            (∏ p ∈ T with p.Prime,
              (1 - (p : ℝ) ^ (-(1 - θ)))⁻¹)) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = _ := by ring

/-- Every moving large-core family of genuine reduced prime strata has zero
density on the actual `n / log n` scale.  The support and residue modulus are
fixed, but both the core family and its individual residues may vary with `n`.
No prime number theorem, arithmetic-progression estimate, or deficiency
asymptotic is assumed. -/
theorem smoothCorePair_large_prime_sum_normalized_tendsto_zero
    (S T : Finset ℕ) (G : ℕ → Finset (ℕ × ℕ)) (W : ℕ)
    (hresidue : ∀ n v, v ∈ G n → v.2 < W)
    (hsmooth : ∀ n v, v ∈ G n → v.1 ∈ Nat.factoredNumbers T)
    (hlarge : ∀ n v, v ∈ G n →
      Real.sqrt (n : ℝ) ≤ (v.1 : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((∑ v ∈ G n,
          (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
            ((n : ℝ) / Real.log n))
      atTop (nhds 0) := by
  let C : ℝ :=
    ∏ p ∈ T with p.Prime,
      (1 - (p : ℝ) ^ (-(1 - (1 / 2 : ℝ))))⁻¹
  have hvanish :=
    (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hupper :
      Tendsto
        (fun n : ℕ =>
          ((W : ℝ) * C) *
            (Real.log (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using hvanish.const_mul ((W : ℝ) * C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnreal : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (by norm_num) hnreal
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
    have hden : 0 < (n : ℝ) / Real.log n := div_pos hnpos hlog
    have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
    have htail := smoothCorePair_prime_sum_rankin_tail
      S T (G n) W n hroot
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
        (hresidue n) (hsmooth n) (hlarge n)
    have hsqrtpower :
        Real.sqrt (n : ℝ) ^ (-(1 / 2 : ℝ)) =
          ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
      norm_num
      rw [Real.rpow_neg (by positivity)]
    calc
      ((∑ v ∈ G n,
          (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
            ((n : ℝ) / Real.log n) ≤
        ((W : ℝ) * (n : ℝ) * Real.sqrt (n : ℝ) ^ (-(1 / 2 : ℝ)) * C) /
            ((n : ℝ) / Real.log n) := by
          apply (div_le_div_iff_of_pos_right hden).mpr
          exact htail
      _ = ((W : ℝ) * C) *
            (Real.log (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)) := by
          rw [hsqrtpower]
          field_simp

/-- Chebyshev's eventual upper bound is uniform over *all* positive cores
below the square-root cutoff: the real quotient `n / c` remains above
`sqrt n`, and its natural floor is exactly natural division. -/
theorem primeCounting_div_uniform_sqrt_chebyshev :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℕ,
      0 < c → (c : ℝ) ≤ Real.sqrt (n : ℝ) →
        (Nat.primeCounting (n / c) : ℝ) ≤
          (2 * (Real.log 4 + 1)) *
            ((n : ℝ) / Real.log n) * (c : ℝ)⁻¹ := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le
      (by norm_num : (0 : ℝ) < 1))
  have hroot_eventually :
      ∀ᶠ n : ℕ in atTop, max A 2 ≤ Real.sqrt (n : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
        (eventually_ge_atTop (max A 2))
  filter_upwards [hroot_eventually] with n hn c hc hcle
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hroot_two : (2 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    (le_max_right A 2).trans hn
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hsquare : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnnonneg
  have hnreal : (1 : ℝ) < (n : ℝ) := by nlinarith
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (by norm_num) hnreal
  have hrootpos : (0 : ℝ) < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 hnpos
  have hquotient :
      Real.sqrt (n : ℝ) ≤ (n : ℝ) / (c : ℝ) := by
    apply (le_div_iff₀ hcpos).mpr
    calc
      Real.sqrt (n : ℝ) * (c : ℝ) ≤
          Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hcle hrootpos.le
      _ = (n : ℝ) := Real.mul_self_sqrt hnnonneg
  have hthreshold : A ≤ (n : ℝ) / (c : ℝ) :=
    ((le_max_left A 2).trans hn).trans hquotient
  have hchebyshev := hA ((n : ℝ) / (c : ℝ)) hthreshold
  rw [Nat.floor_div_eq_div] at hchebyshev
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hlogquotient :
      Real.log (n : ℝ) / 2 ≤ Real.log ((n : ℝ) / (c : ℝ)) := by
    rw [← Real.log_sqrt hnnonneg]
    exact Real.log_le_log hrootpos hquotient
  have hconstant : 0 < Real.log 4 + 1 := by
    have hfour : (0 : ℝ) < Real.log 4 :=
      Real.log_pos (by norm_num)
    linarith
  calc
    (Nat.primeCounting (n / c) : ℝ) ≤
        (Real.log 4 + 1) * ((n : ℝ) / (c : ℝ)) /
          Real.log ((n : ℝ) / (c : ℝ)) := hchebyshev
    _ ≤ (Real.log 4 + 1) * ((n : ℝ) / (c : ℝ)) /
          (Real.log (n : ℝ) / 2) := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg hconstant.le (div_nonneg hnnonneg hcpos.le))
        (by positivity) hlogquotient
    _ = (2 * (Real.log 4 + 1)) *
          ((n : ℝ) / Real.log n) * (c : ℝ)⁻¹ := by
      field_simp

/-- Uniform middle-core tail for the *actual moving prime-progression family*.
For any fixed positive cutoff `R`, every family of genuine fixed-support cores
between `R` and `sqrt n` has normalized mass at most an explicit constant
times `R ^ (-1 / 2)`.  The family and all residue choices may vary with `n`.
This is the missing noncircular Chebyshev--Rankin interchange bound. -/
theorem smoothCorePair_middle_prime_sum_eventually_le
    (S T : Finset ℕ) (G : ℕ → Finset (ℕ × ℕ)) (W : ℕ)
    {R : ℝ} (hR : 0 < R)
    (hresidue : ∀ n v, v ∈ G n → v.2 < W)
    (hsmooth : ∀ n v, v ∈ G n → v.1 ∈ Nat.factoredNumbers T)
    (hlarge : ∀ n v, v ∈ G n → R ≤ (v.1 : ℝ))
    (hsmall : ∀ n v, v ∈ G n → (v.1 : ℝ) ≤ Real.sqrt (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      ((∑ v ∈ G n,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
          ((n : ℝ) / Real.log n) ≤
        (W : ℝ) * (2 * (Real.log 4 + 1)) * R ^ (-(1 / 2 : ℝ)) *
          (∏ p ∈ T with p.Prime,
            (1 - (p : ℝ) ^ (-(1 - (1 / 2 : ℝ))))⁻¹) := by
  classical
  filter_upwards [primeCounting_div_uniform_sqrt_chebyshev,
    eventually_ge_atTop 2] with n hchebyshev hn
  let cores := (G n).image Prod.fst
  have hnreal : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 1 < n)
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (by norm_num) hnreal
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hden : 0 < (n : ℝ) / Real.log n := div_pos hnpos hlog
  have hconstant : 0 < 2 * (Real.log 4 + 1) := by
    have hfour : (0 : ℝ) < Real.log 4 :=
      Real.log_pos (by norm_num)
    nlinarith
  have hcoresmooth : ∀ c ∈ cores, c ∈ Nat.factoredNumbers T := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact hsmooth n v hv
  have hcorelarge : ∀ c ∈ cores, R ≤ (c : ℝ) := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact hlarge n v hv
  have hcoresmall : ∀ c ∈ cores, (c : ℝ) ≤ Real.sqrt (n : ℝ) := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact hsmall n v hv
  have hprime :
      ((∑ c ∈ cores, Nat.primeCounting (n / c)) : ℝ) ≤
        (2 * (Real.log 4 + 1)) *
          ((n : ℝ) / Real.log n) * ∑ c ∈ cores, (c : ℝ)⁻¹ := by
    calc
      ((∑ c ∈ cores, Nat.primeCounting (n / c)) : ℝ) =
          ∑ c ∈ cores, (Nat.primeCounting (n / c) : ℝ) := by rfl
      _ ≤ ∑ c ∈ cores,
          (2 * (Real.log 4 + 1)) *
            ((n : ℝ) / Real.log n) * (c : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro c hc
          exact hchebyshev c
            (Nat.pos_of_ne_zero (hcoresmooth c hc).1)
            (hcoresmall c hc)
      _ = _ := by rw [Finset.mul_sum]
  have htail := supportSmooth_reciprocal_rankin_tail_finset
    T cores hR (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hcoresmooth hcorelarge
  have hpair := smoothCorePair_prime_sum_le_residue_mul
    S (G n) W n (hresidue n)
  have hpairreal :
      ((∑ v ∈ G n,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) ≤
          (W : ℝ) *
            ((∑ c ∈ cores, Nat.primeCounting (n / c)) : ℝ) := by
    exact_mod_cast hpair
  have hcount :
      ((∑ v ∈ G n,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) ≤
        (W : ℝ) * (2 * (Real.log 4 + 1)) *
          ((n : ℝ) / Real.log n) *
            (R ^ (-(1 / 2 : ℝ)) *
              (∏ p ∈ T with p.Prime,
                (1 - (p : ℝ) ^ (-(1 - (1 / 2 : ℝ))))⁻¹)) := by
    calc
      ((∑ v ∈ G n,
        (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) ≤
          (W : ℝ) *
            ((∑ c ∈ cores, Nat.primeCounting (n / c)) : ℝ) := hpairreal
      _ ≤ (W : ℝ) *
          ((2 * (Real.log 4 + 1)) *
            ((n : ℝ) / Real.log n) * ∑ c ∈ cores, (c : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hprime (by positivity)
      _ ≤ (W : ℝ) *
          ((2 * (Real.log 4 + 1)) *
            ((n : ℝ) / Real.log n) *
              (R ^ (-(1 / 2 : ℝ)) *
                (∏ p ∈ T with p.Prime,
                  (1 - (p : ℝ) ^ (-(1 - (1 / 2 : ℝ))))⁻¹))) := by
        apply mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htail
            (mul_nonneg hconstant.le hden.le))
          (by positivity)
      _ = _ := by ring
  calc
    ((∑ v ∈ G n,
      (smoothDeficiencyPrimeStratum S v.1 v.2 n).card) : ℝ) /
        ((n : ℝ) / Real.log n) ≤
      ((W : ℝ) * (2 * (Real.log 4 + 1)) *
        ((n : ℝ) / Real.log n) *
          (R ^ (-(1 / 2 : ℝ)) *
            (∏ p ∈ T with p.Prime,
              (1 - (p : ℝ) ^ (-(1 - (1 / 2 : ℝ))))⁻¹))) /
                ((n : ℝ) / Real.log n) :=
      (div_le_div_iff_of_pos_right hden).mpr hcount
    _ = (W : ℝ) * (2 * (Real.log 4 + 1)) * R ^ (-(1 / 2 : ℝ)) *
          (∏ p ∈ T with p.Prime,
            (1 - (p : ℝ) ^ (-(1 - (1 / 2 : ℝ))))⁻¹) := by
      field_simp


end Erdos689
