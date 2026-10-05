module

public import AdaptiveMixedAffineComplexity1139
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section


/-!
# Removing logarithmic prime weights at every fixed mixed-pattern rank

Published finite-complexity linear-forms theorems are naturally stated for
von-Mangoldt/logarithmic weights.  Once proper prime powers are separately
discarded, every genuine positive affine prime form lies between fixed
positive multiples of the common scale.  Its log weight is therefore
uniformly asymptotic to `log N`.  This module proves the resulting exact
finite-form-family weighted/unweighted asymptotic transfer without assuming
any prime-pattern theorem.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- An exact fixed positive linear window bounds the logarithmic prime
weight between its two genuinely scale-independent logarithmic shifts. -/
theorem adaptiveMixedFixedLinearLogRatio_bounds
    {lower upper : ℝ} {N value : ℕ}
    (lower_positive : 0 < lower)
    (upper_positive : 0 < upper)
    (large : 2 ≤ N)
    (lower_bound : lower * (N : ℝ) ≤ (value : ℝ))
    (upper_bound : (value : ℝ) ≤ upper * (N : ℝ)) :
    1 + Real.log lower / Real.log (N : ℝ) ≤
        Real.log (value : ℝ) / Real.log (N : ℝ) ∧
      Real.log (value : ℝ) / Real.log (N : ℝ) ≤
        1 + Real.log upper / Real.log (N : ℝ) := by
  have N_positive : (0 : ℝ) < N := by
    exact_mod_cast (by omega : 0 < N)
  have N_log_positive : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < N)
  have value_positive : (0 : ℝ) < value :=
    (mul_pos lower_positive N_positive).trans_le lower_bound
  have lower_log := Real.strictMonoOn_log.monotoneOn
    (mul_pos lower_positive N_positive) value_positive lower_bound
  have upper_log := Real.strictMonoOn_log.monotoneOn
    value_positive (mul_pos upper_positive N_positive) upper_bound
  rw [Real.log_mul lower_positive.ne' N_positive.ne'] at lower_log
  rw [Real.log_mul upper_positive.ne' N_positive.ne'] at upper_log
  constructor
  · apply (le_div_iff₀ N_log_positive).mpr
    calc
      (1 + Real.log lower / Real.log (N : ℝ)) * Real.log (N : ℝ) =
          Real.log (N : ℝ) + Real.log lower := by
        field_simp
      _ ≤ Real.log (value : ℝ) := by linarith
  · apply (div_le_iff₀ N_log_positive).mpr
    calc
      Real.log (value : ℝ) ≤
          Real.log (N : ℝ) + Real.log upper := by linarith
      _ = (1 + Real.log upper / Real.log (N : ℝ)) *
          Real.log (N : ℝ) := by
        field_simp

/-- The two fixed-multiple logarithmic correction factors both tend to one;
the bound is uniform over every prime value in the corresponding window. -/
theorem adaptiveMixedFixedLinearLogCorrection_tendsto_one
    (factor : ℝ) :
    Tendsto
      (fun N : ℕ => 1 + Real.log factor / Real.log (N : ℝ))
      atTop (nhds (1 : ℝ)) := by
  have logarithm_top :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have correction :=
    (tendsto_const_nhds (x := Real.log factor)).div_atTop logarithm_top
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).add correction

/-- Every finite fixed family of actual positive linearly bounded prime-form
values has its whole normalized logarithmic product squeezed between the
corresponding fixed endpoint powers. -/
theorem adaptiveMixedFixedLinearLogProduct_bounds
    {ι : Type*} (forms : Finset ι) (value : ι → ℕ)
    {lower upper : ℝ} {N : ℕ}
    (lower_positive : 0 < lower)
    (upper_positive : 0 < upper)
    (large : 2 ≤ N)
    (lower_factor_nonnegative :
      0 ≤ 1 + Real.log lower / Real.log (N : ℝ))
    (bounds : ∀ index ∈ forms,
      lower * (N : ℝ) ≤ (value index : ℝ) ∧
        (value index : ℝ) ≤ upper * (N : ℝ)) :
    (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card ≤
        ∏ index ∈ forms,
          Real.log (value index : ℝ) / Real.log (N : ℝ) ∧
      (∏ index ∈ forms,
          Real.log (value index : ℝ) / Real.log (N : ℝ)) ≤
        (1 + Real.log upper / Real.log (N : ℝ)) ^ forms.card := by
  constructor
  · calc
      (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card =
          ∏ _index ∈ forms,
            (1 + Real.log lower / Real.log (N : ℝ)) := by simp
      _ ≤ ∏ index ∈ forms,
          Real.log (value index : ℝ) / Real.log (N : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro index selected
          exact lower_factor_nonnegative
        · intro index selected
          exact (adaptiveMixedFixedLinearLogRatio_bounds
            lower_positive upper_positive large
            (bounds index selected).1 (bounds index selected).2).1
  · calc
      (∏ index ∈ forms,
          Real.log (value index : ℝ) / Real.log (N : ℝ)) ≤
        ∏ _index ∈ forms,
          (1 + Real.log upper / Real.log (N : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro index selected
          exact lower_factor_nonnegative.trans
            (adaptiveMixedFixedLinearLogRatio_bounds
              lower_positive upper_positive large
              (bounds index selected).1 (bounds index selected).2).1
        · intro index selected
          exact (adaptiveMixedFixedLinearLogRatio_bounds
            lower_positive upper_positive large
            (bounds index selected).1 (bounds index selected).2).2
      _ = (1 + Real.log upper / Real.log (N : ℝ)) ^ forms.card := by simp

/-- The ENTIRE finite genuine prime-pattern family satisfies the same
arbitrary-fixed-rank logarithmic sandwich, with no bound on its cardinality
and no independence assumption between its points. -/
theorem adaptiveMixedFixedLinearLogSum_bounds
    {ι α : Type*} (forms : Finset ι) (points : Finset α)
    (value : ι → α → ℕ) {lower upper : ℝ} {N : ℕ}
    (lower_positive : 0 < lower)
    (upper_positive : 0 < upper)
    (large : 2 ≤ N)
    (lower_factor_nonnegative :
      0 ≤ 1 + Real.log lower / Real.log (N : ℝ))
    (bounds : ∀ point ∈ points, ∀ index ∈ forms,
      lower * (N : ℝ) ≤ (value index point : ℝ) ∧
        (value index point : ℝ) ≤ upper * (N : ℝ)) :
    (points.card : ℝ) *
        (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card ≤
      ∑ point ∈ points,
        ∏ index ∈ forms,
          Real.log (value index point : ℝ) / Real.log (N : ℝ) ∧
    (∑ point ∈ points,
        ∏ index ∈ forms,
          Real.log (value index point : ℝ) / Real.log (N : ℝ)) ≤
      (points.card : ℝ) *
        (1 + Real.log upper / Real.log (N : ℝ)) ^ forms.card := by
  constructor
  · calc
      (points.card : ℝ) *
          (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card =
        ∑ _point ∈ points,
          (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card := by simp
      _ ≤ ∑ point ∈ points,
            ∏ index ∈ forms,
              Real.log (value index point : ℝ) / Real.log (N : ℝ) := by
        apply Finset.sum_le_sum
        intro point selected
        exact (adaptiveMixedFixedLinearLogProduct_bounds forms
          (fun index => value index point)
          lower_positive upper_positive large lower_factor_nonnegative
          (bounds point selected)).1
  · calc
      (∑ point ∈ points,
          ∏ index ∈ forms,
            Real.log (value index point : ℝ) / Real.log (N : ℝ)) ≤
        ∑ _point ∈ points,
          (1 + Real.log upper / Real.log (N : ℝ)) ^ forms.card := by
        apply Finset.sum_le_sum
        intro point selected
        exact (adaptiveMixedFixedLinearLogProduct_bounds forms
          (fun index => value index point)
          lower_positive upper_positive large lower_factor_nonnegative
          (bounds point selected)).2
      _ = (points.card : ℝ) *
          (1 + Real.log upper / Real.log (N : ℝ)) ^ forms.card := by simp

/-- Exact cancellation of the common `log N` denominator in an arbitrary
finite prime-form product. -/
theorem adaptiveMixedFixedLinearLogProduct_normalized_eq
    {ι : Type*} (forms : Finset ι) (value : ι → ℕ) (N : ℕ) :
    (∏ index ∈ forms,
      Real.log (value index : ℝ) / Real.log (N : ℝ)) =
      (∏ index ∈ forms, Real.log (value index : ℝ)) /
        Real.log (N : ℝ) ^ forms.card := by
  rw [Finset.prod_div_distrib]
  simp

/-- The raw logarithmically weighted finite pattern sum equals its
normalized-log-weight sum times the EXACT common `log(N)^rank` factor. -/
theorem adaptiveMixedFixedLinearLogWeightedSum_normalized_identity
    {ι α : Type*} (forms : Finset ι) (points : Finset α)
    (value : ι → α → ℕ) (dimension N : ℕ) (large : 2 ≤ N) :
    (∑ point ∈ points,
      ∏ index ∈ forms, Real.log (value index point : ℝ)) /
        (N : ℝ) ^ dimension =
      (Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension) *
        (∑ point ∈ points,
          ∏ index ∈ forms,
            Real.log (value index point : ℝ) / Real.log (N : ℝ)) := by
  have logarithm_positive : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < N)
  have logarithm_nonzero : Real.log (N : ℝ) ≠ 0 := logarithm_positive.ne'
  simp_rw [adaptiveMixedFixedLinearLogProduct_normalized_eq]
  rw [← Finset.sum_div]
  field_simp [logarithm_nonzero]

/-- The true arbitrary-rank weighted prime-form sum and the corresponding
unweighted count have the SAME scale, up to endpoint powers converging to one.
The moving finite point families may have arbitrary cardinalities. -/
theorem adaptiveMixedFixedLinearLogWeightedSum_eventual_sandwich
    {ι α : Type*} (forms : Finset ι)
    (points : ℕ → Finset α) (value : ι → α → ℕ)
    (lower upper : ℝ) (dimension : ℕ)
    (lower_positive : 0 < lower)
    (upper_positive : 0 < upper)
    (bounds : ∀ᶠ N : ℕ in atTop,
      ∀ point ∈ points N, ∀ index ∈ forms,
        lower * (N : ℝ) ≤ (value index point : ℝ) ∧
          (value index point : ℝ) ≤ upper * (N : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card *
          (((points N).card : ℝ) *
            Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension) ≤
        (∑ point ∈ points N,
          ∏ index ∈ forms,
            Real.log (value index point : ℝ)) / (N : ℝ) ^ dimension ∧
      (∑ point ∈ points N,
          ∏ index ∈ forms,
            Real.log (value index point : ℝ)) / (N : ℝ) ^ dimension ≤
        (1 + Real.log upper / Real.log (N : ℝ)) ^ forms.card *
          (((points N).card : ℝ) *
            Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension) := by
  have lower_eventually :
      ∀ᶠ N : ℕ in atTop,
        0 < 1 + Real.log lower / Real.log (N : ℝ) :=
    (adaptiveMixedFixedLinearLogCorrection_tendsto_one lower).eventually
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 2, lower_eventually, bounds]
    with N large lower_factor_positive linear_bounds
  have scale_nonnegative :
      0 ≤ Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension := by
    apply div_nonneg
    · exact pow_nonneg (Real.log_nonneg (by
        exact_mod_cast (by omega : 1 ≤ N))) _
    · exact pow_nonneg (Nat.cast_nonneg N) _
  obtain ⟨lower_sum, upper_sum⟩ :=
    adaptiveMixedFixedLinearLogSum_bounds forms (points N) value
      lower_positive upper_positive large lower_factor_positive.le
      linear_bounds
  have actual_identity :=
    adaptiveMixedFixedLinearLogWeightedSum_normalized_identity
      forms (points N) value dimension N large
  constructor
  · calc
      (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card *
          (((points N).card : ℝ) *
            Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension) =
        (Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension) *
          (((points N).card : ℝ) *
            (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card) := by ring
      _ ≤ (Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension) *
          (∑ point ∈ points N,
            ∏ index ∈ forms,
              Real.log (value index point : ℝ) / Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left lower_sum scale_nonnegative
      _ = _ := actual_identity.symm
  · calc
      (∑ point ∈ points N,
          ∏ index ∈ forms,
            Real.log (value index point : ℝ)) / (N : ℝ) ^ dimension =
        (Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension) *
          (∑ point ∈ points N,
            ∏ index ∈ forms,
              Real.log (value index point : ℝ) / Real.log (N : ℝ)) :=
        actual_identity
      _ ≤ (Real.log (N : ℝ) ^ forms.card / (N : ℝ) ^ dimension) *
          (((points N).card : ℝ) *
            (1 + Real.log upper / Real.log (N : ℝ)) ^ forms.card) :=
        mul_le_mul_of_nonneg_left upper_sum scale_nonnegative
      _ = _ := by ring

/-- COMPLETE exact arbitrary-fixed-rank logarithmic-weight conversion:
the genuine finite-form weighted prime-pattern asymptotic is equivalent to
the unweighted count with its correct `log(N)^rank` normalization.

Only fixed positive linear bounds on the actual form VALUES are assumed.
The moving point family can grow arbitrarily, there is no independence or
uniform-in-rank hypothesis, and no prime-pattern theorem is postulated. -/
theorem adaptiveMixedFixedLinearLogWeighted_asymptotic_iff
    {ι α : Type*} (forms : Finset ι)
    (points : ℕ → Finset α) (value : ι → α → ℕ)
    (lower upper : ℝ) (dimension : ℕ) (limit : ℝ)
    (lower_positive : 0 < lower)
    (upper_positive : 0 < upper)
    (bounds : ∀ᶠ N : ℕ in atTop,
      ∀ point ∈ points N, ∀ index ∈ forms,
        lower * (N : ℝ) ≤ (value index point : ℝ) ∧
          (value index point : ℝ) ≤ upper * (N : ℝ)) :
    Tendsto
      (fun N : ℕ =>
        (∑ point ∈ points N,
          ∏ index ∈ forms,
            Real.log (value index point : ℝ)) / (N : ℝ) ^ dimension)
      atTop (nhds limit) ↔
    Tendsto
      (fun N : ℕ =>
        ((points N).card : ℝ) * Real.log (N : ℝ) ^ forms.card /
          (N : ℝ) ^ dimension)
      atTop (nhds limit) := by
  let weighted : ℕ → ℝ := fun N =>
    (∑ point ∈ points N,
      ∏ index ∈ forms,
        Real.log (value index point : ℝ)) / (N : ℝ) ^ dimension
  let unweighted : ℕ → ℝ := fun N =>
    ((points N).card : ℝ) * Real.log (N : ℝ) ^ forms.card /
      (N : ℝ) ^ dimension
  let lower_factor : ℕ → ℝ := fun N =>
    (1 + Real.log lower / Real.log (N : ℝ)) ^ forms.card
  let upper_factor : ℕ → ℝ := fun N =>
    (1 + Real.log upper / Real.log (N : ℝ)) ^ forms.card
  have lower_tendsto : Tendsto lower_factor atTop (nhds (1 : ℝ)) := by
    simpa [lower_factor] using
      (adaptiveMixedFixedLinearLogCorrection_tendsto_one lower).pow forms.card
  have upper_tendsto : Tendsto upper_factor atTop (nhds (1 : ℝ)) := by
    simpa [upper_factor] using
      (adaptiveMixedFixedLinearLogCorrection_tendsto_one upper).pow forms.card
  have lower_eventually : ∀ᶠ N : ℕ in atTop, 0 < lower_factor N :=
    lower_tendsto.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have upper_eventually : ∀ᶠ N : ℕ in atTop, 0 < upper_factor N :=
    upper_tendsto.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have sandwich : ∀ᶠ N : ℕ in atTop,
      lower_factor N * unweighted N ≤ weighted N ∧
        weighted N ≤ upper_factor N * unweighted N := by
    simpa [weighted, unweighted, lower_factor, upper_factor] using
      adaptiveMixedFixedLinearLogWeightedSum_eventual_sandwich
        forms points value lower upper dimension
        lower_positive upper_positive bounds
  change Tendsto weighted atTop (nhds limit) ↔
    Tendsto unweighted atTop (nhds limit)
  constructor
  · intro weighted_limit
    have lower_limit :
        Tendsto (fun N : ℕ => weighted N / upper_factor N)
          atTop (nhds limit) := by
      have quotient :
          Tendsto (weighted / upper_factor) atTop (nhds limit) := by
        simpa using weighted_limit.div upper_tendsto (by norm_num)
      exact quotient.congr' (Eventually.of_forall fun _ => rfl)
    have upper_limit :
        Tendsto (fun N : ℕ => weighted N / lower_factor N)
          atTop (nhds limit) := by
      have quotient :
          Tendsto (weighted / lower_factor) atTop (nhds limit) := by
        simpa using weighted_limit.div lower_tendsto (by norm_num)
      exact quotient.congr' (Eventually.of_forall fun _ => rfl)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      lower_limit upper_limit
    · filter_upwards [sandwich, upper_eventually] with N bounded positive
      apply (div_le_iff₀ positive).mpr
      simpa [mul_comm] using bounded.2
    · filter_upwards [sandwich, lower_eventually] with N bounded positive
      apply (le_div_iff₀ positive).mpr
      simpa [mul_comm] using bounded.1
  · intro unweighted_limit
    have lower_limit :
        Tendsto (fun N : ℕ => lower_factor N * unweighted N)
          atTop (nhds limit) := by
      simpa using lower_tendsto.mul unweighted_limit
    have upper_limit :
        Tendsto (fun N : ℕ => upper_factor N * unweighted N)
          atTop (nhds limit) := by
      simpa using upper_tendsto.mul unweighted_limit
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      lower_limit upper_limit
      (sandwich.mono fun _ bounded => bounded.1)
      (sandwich.mono fun _ bounded => bounded.2)


end Erdos1139
