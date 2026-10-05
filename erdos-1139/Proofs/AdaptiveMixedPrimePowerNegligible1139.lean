module

public import AdaptiveSharedTargetDiagonalNegligible1139
public import PrincipalPrimeOnly433

@[expose] public section


/-!
# Proper prime powers in arbitrary-rank genuine mixed prime systems

The published linear-forms theorem is naturally expressed with von Mangoldt
weights.  The actual Erdős #1139 construction instead requires every one of
its genuine prime forms to be prime.  Their rank is fixed when taking the
analytic limit, but it is NOT restricted to three.

This module reuses the independently audited proper-prime-power counting
bound from Erdős #689.  It proves a finite exceptional-set estimate for an
arbitrary finite system of forms on an arbitrary finite point set, together
with the exact signed affine fiber estimates needed for the actual
two-dimensional and three-dimensional #1139 systems.  No prime-pattern
asymptotic, Green--Tao estimate, or nonstandard axiom is assumed.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- The genuine von Mangoldt weight of an arbitrary FINITE fixed-rank prime
form system; this includes its indispensable prime-label forms. -/
noncomputable def adaptiveMixedVonMangoldtProduct
    {ι α : Type*} (forms : Finset ι) (value : ι → α → ℕ)
    (point : α) : ℝ :=
  ∏ index ∈ forms, ArithmeticFunction.vonMangoldt (value index point)

/-- Points with nonzero actual von Mangoldt weight at which at least one
form is a proper prime power rather than a prime. -/
noncomputable def adaptiveMixedVonMangoldtPrimePowerExceptions
    {ι α : Type*} (points : Finset α) (forms : Finset ι)
    (value : ι → α → ℕ) : Finset α := by
  classical
  exact points.filter fun point =>
    adaptiveMixedVonMangoldtProduct forms value point ≠ 0 ∧
      ∃ index ∈ forms, ¬ (value index point).Prime

/-- Every finite-rank genuine von Mangoldt product is nonnegative. -/
theorem adaptiveMixedVonMangoldtProduct_nonneg
    {ι α : Type*} (forms : Finset ι) (value : ι → α → ℕ)
    (point : α) :
    0 ≤ adaptiveMixedVonMangoldtProduct forms value point := by
  unfold adaptiveMixedVonMangoldtProduct
  exact Finset.prod_nonneg fun index _ =>
    ArithmeticFunction.vonMangoldt_nonneg

/-- A nonzero finite-rank product forces EVERY indexed prime form to have
nonzero von Mangoldt weight. -/
theorem adaptiveMixedVonMangoldtProduct_factor_ne_zero
    {ι α : Type*} (forms : Finset ι) (value : ι → α → ℕ)
    (point : α) {index : ι} (selected : index ∈ forms)
    (nonzero : adaptiveMixedVonMangoldtProduct forms value point ≠ 0) :
    ArithmeticFunction.vonMangoldt (value index point) ≠ 0 := by
  classical
  intro zero
  apply nonzero
  unfold adaptiveMixedVonMangoldtProduct
  exact Finset.prod_eq_zero selected zero

/-- Finite arbitrary-rank proper-prime-power covering estimate.  Each actual
form may have a different map, and the points may have arbitrary signed,
archimedean, residue, or lattice restrictions.  The ONLY required geometric
input is a uniform finite fiber bound. -/
theorem adaptiveMixedVonMangoldtPrimePowerExceptions_card_le
    {ι α : Type*} (points : Finset α) (forms : Finset ι)
    (value : ι → α → ℕ) (cutoff fiberBound : ℕ)
    (bounded : ∀ point ∈ points, ∀ index ∈ forms,
      value index point ∈ Finset.Ioc 0 cutoff)
    (fibers : ∀ index ∈ forms,
      ∀ power ∈ Erdos689.ternaryProperPrimePowers cutoff,
        (points.filter fun point => value index point = power).card ≤
          fiberBound) :
    (adaptiveMixedVonMangoldtPrimePowerExceptions
      points forms value).card ≤
        forms.card *
          (Erdos689.ternaryProperPrimePowers cutoff).card * fiberBound := by
  classical
  let powers := Erdos689.ternaryProperPrimePowers cutoff
  let bad (index : ι) := points.filter fun point => value index point ∈ powers
  have per_form (index : ι) (selected : index ∈ forms) :
      (bad index).card ≤ powers.card * fiberBound := by
    have cover :
        bad index ⊆ powers.biUnion
          (fun power => points.filter fun point => value index point = power) := by
      intro point membership
      obtain ⟨in_points, in_powers⟩ := Finset.mem_filter.mp membership
      apply Finset.mem_biUnion.mpr
      exact ⟨value index point, in_powers,
        Finset.mem_filter.mpr ⟨in_points, rfl⟩⟩
    calc
      (bad index).card ≤
          (powers.biUnion
            (fun power => points.filter
              fun point => value index point = power)).card :=
        Finset.card_le_card cover
      _ ≤ ∑ power ∈ powers,
          (points.filter fun point => value index point = power).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _power ∈ powers, fiberBound := by
        exact Finset.sum_le_sum fun power selected_power =>
          fibers index selected power selected_power
      _ = powers.card * fiberBound := by simp
  have cover :
      adaptiveMixedVonMangoldtPrimePowerExceptions points forms value ⊆
        forms.biUnion bad := by
    intro point membership
    obtain ⟨in_points, nonzero, index, selected, not_prime⟩ :=
      Finset.mem_filter.mp membership
    apply Finset.mem_biUnion.mpr
    refine ⟨index, selected, Finset.mem_filter.mpr ⟨in_points, ?_⟩⟩
    exact Finset.mem_filter.mpr
      ⟨bounded point in_points index selected, not_prime,
        adaptiveMixedVonMangoldtProduct_factor_ne_zero
          forms value point selected nonzero⟩
  calc
    (adaptiveMixedVonMangoldtPrimePowerExceptions points forms value).card ≤
        (forms.biUnion bad).card := Finset.card_le_card cover
    _ ≤ ∑ index ∈ forms, (bad index).card := Finset.card_biUnion_le
    _ ≤ ∑ _index ∈ forms, powers.card * fiberBound := by
      exact Finset.sum_le_sum fun index selected => per_form index selected
    _ = forms.card *
          (Erdos689.ternaryProperPrimePowers cutoff).card * fiberBound := by
      simp [powers, mul_assoc]

/-- EXACT finite arbitrary-rank decomposition: the unrestricted genuine
von Mangoldt sum is its all-prime part plus the proper-prime-power error.
All nonprime zero-weight points disappear identically. -/
theorem adaptiveMixedVonMangoldtSum_eq_prime_sum_add_exceptions
    {ι α : Type*} (points : Finset α) (forms : Finset ι)
    (value : ι → α → ℕ) :
    (∑ point ∈ points, adaptiveMixedVonMangoldtProduct forms value point) =
      (∑ point ∈ points.filter
        (fun point => ∀ index ∈ forms, (value index point).Prime),
          adaptiveMixedVonMangoldtProduct forms value point) +
      ∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
        points forms value, adaptiveMixedVonMangoldtProduct forms value point := by
  classical
  let good := fun point : α => ∀ index ∈ forms, (value index point).Prime
  have split := Finset.sum_filter_add_sum_filter_not
    points good (adaptiveMixedVonMangoldtProduct forms value)
  have bad :
      (points.filter fun point => ¬ good point).filter
        (fun point => adaptiveMixedVonMangoldtProduct forms value point ≠ 0) =
          adaptiveMixedVonMangoldtPrimePowerExceptions points forms value := by
    ext point
    simp only [adaptiveMixedVonMangoldtPrimePowerExceptions, Finset.mem_filter]
    constructor
    · rintro ⟨⟨in_points, not_good⟩, nonzero⟩
      refine ⟨in_points, nonzero, ?_⟩
      simp only [good, not_forall] at not_good
      obtain ⟨index, selected, not_prime⟩ := not_good
      exact ⟨index, selected, not_prime⟩
    · rintro ⟨in_points, nonzero, index, selected, not_prime⟩
      exact ⟨⟨in_points, fun all_prime =>
        not_prime (all_prime index selected)⟩, nonzero⟩
  change
    (∑ point ∈ points, adaptiveMixedVonMangoldtProduct forms value point) =
      (∑ point ∈ points.filter good,
        adaptiveMixedVonMangoldtProduct forms value point) +
      ∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions points forms value,
        adaptiveMixedVonMangoldtProduct forms value point
  calc
    (∑ point ∈ points, adaptiveMixedVonMangoldtProduct forms value point) =
        (∑ point ∈ points.filter good,
          adaptiveMixedVonMangoldtProduct forms value point) +
        ∑ point ∈ points.filter (fun point => ¬ good point),
          adaptiveMixedVonMangoldtProduct forms value point := split.symm
    _ = (∑ point ∈ points.filter good,
          adaptiveMixedVonMangoldtProduct forms value point) +
        ∑ point ∈ (points.filter (fun point => ¬ good point)).filter
          (fun point => adaptiveMixedVonMangoldtProduct forms value point ≠ 0),
            adaptiveMixedVonMangoldtProduct forms value point := by
      rw [Finset.sum_filter_ne_zero]
    _ = _ := by rw [bad]

/-- Arbitrary fixed-rank actual von Mangoldt weight on a positive bounded
form box is at most the corresponding power of the logarithmic cutoff. -/
theorem adaptiveMixedVonMangoldtProduct_le_log_pow
    {ι α : Type*} (forms : Finset ι) (value : ι → α → ℕ)
    (point : α) (cutoff : ℕ)
    (bounded : ∀ index ∈ forms,
      value index point ∈ Finset.Ioc 0 cutoff) :
    adaptiveMixedVonMangoldtProduct forms value point ≤
      Real.log (cutoff : ℝ) ^ forms.card := by
  unfold adaptiveMixedVonMangoldtProduct
  calc
    (∏ index ∈ forms, ArithmeticFunction.vonMangoldt (value index point)) ≤
        ∏ _index ∈ forms, Real.log (cutoff : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro index selected
        exact ArithmeticFunction.vonMangoldt_nonneg
      · intro index selected
        obtain ⟨positive, upper⟩ := Finset.mem_Ioc.mp (bounded index selected)
        exact ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log (by exact_mod_cast positive)
            (by exact_mod_cast upper))
    _ = Real.log (cutoff : ℝ) ^ forms.card := by simp

/-- Quantitative arbitrary-rank weighted proper-prime-power error, retaining
the exact finite fiber bound and the audited #689 `sqrt(n)(log₂(n)+1)`
proper-prime-power counting estimate. -/
theorem adaptiveMixedVonMangoldtPrimePowerExceptions_weight_le
    {ι α : Type*} (points : Finset α) (forms : Finset ι)
    (value : ι → α → ℕ) (cutoff fiberBound : ℕ)
    (bounded : ∀ point ∈ points, ∀ index ∈ forms,
      value index point ∈ Finset.Ioc 0 cutoff)
    (fibers : ∀ index ∈ forms,
      ∀ power ∈ Erdos689.ternaryProperPrimePowers cutoff,
        (points.filter fun point => value index point = power).card ≤
          fiberBound) :
    (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions points forms value,
      adaptiveMixedVonMangoldtProduct forms value point) ≤
        (forms.card : ℝ) * (fiberBound : ℝ) *
          (Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1) *
            Real.log (cutoff : ℝ) ^ forms.card := by
  classical
  let exceptions := adaptiveMixedVonMangoldtPrimePowerExceptions
    points forms value
  have log_nonneg : 0 ≤ Real.log (cutoff : ℝ) :=
    Real.log_natCast_nonneg cutoff
  have card_bound :=
    adaptiveMixedVonMangoldtPrimePowerExceptions_card_le
      points forms value cutoff fiberBound bounded fibers
  have real_card_bound :
      (exceptions.card : ℝ) ≤
        (forms.card : ℝ) *
          ((Erdos689.ternaryProperPrimePowers cutoff).card : ℝ) *
            (fiberBound : ℝ) := by
    exact_mod_cast card_bound
  have powers := Erdos689.ternaryProperPrimePowers_card_le cutoff
  calc
    (∑ point ∈ exceptions, adaptiveMixedVonMangoldtProduct forms value point) ≤
        ∑ _point ∈ exceptions, Real.log (cutoff : ℝ) ^ forms.card := by
      apply Finset.sum_le_sum
      intro point selected
      have in_points :=
        (Finset.mem_filter.mp (show point ∈
          adaptiveMixedVonMangoldtPrimePowerExceptions points forms value from
            selected)).1
      exact adaptiveMixedVonMangoldtProduct_le_log_pow
        forms value point cutoff (bounded point in_points)
    _ = (exceptions.card : ℝ) * Real.log (cutoff : ℝ) ^ forms.card := by simp
    _ ≤ ((forms.card : ℝ) *
        ((Erdos689.ternaryProperPrimePowers cutoff).card : ℝ) *
          (fiberBound : ℝ)) * Real.log (cutoff : ℝ) ^ forms.card := by
      gcongr
    _ ≤ ((forms.card : ℝ) *
        ((Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1)) *
          (fiberBound : ℝ)) * Real.log (cutoff : ℝ) ^ forms.card := by
      gcongr
    _ = _ := by ring

/-- At EVERY fixed form rank, the proper-prime-power counting loss times the
full von Mangoldt logarithmic weight is little-o of one linear scale. -/
theorem adaptiveMixedProperPrimePowerScaleError_tendsto_zero (rank : ℕ) :
    Tendsto
      (fun cutoff : ℕ =>
        (Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1) *
          Real.log (cutoff : ℝ) ^ rank / (cutoff : ℝ))
      atTop (nhds 0) := by
  have log_two_positive : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  have logarithms :
      Tendsto
        (fun cutoff : ℕ =>
          Real.log (cutoff : ℝ) ^ (rank + 1) /
            (cutoff : ℝ) ^ (1 / 2 : ℝ))
        atTop (nhds 0) := by
    have real_limit :=
      (isLittleO_log_rpow_rpow_atTop (rank + 1 : ℕ)
        (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero
    have natural_limit :=
      real_limit.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, Real.rpow_natCast] using natural_limit
  have upper_limit :
      Tendsto
        (fun cutoff : ℕ =>
          (2 / Real.log 2) *
            (Real.log (cutoff : ℝ) ^ (rank + 1) /
              (cutoff : ℝ) ^ (1 / 2 : ℝ)))
        atTop (nhds 0) := by
    simpa using logarithms.const_mul (2 / Real.log 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds upper_limit ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with cutoff at_least_two
    positivity
  · filter_upwards [eventually_ge_atTop 2] with cutoff at_least_two
    have positive : (0 : ℝ) < (cutoff : ℝ) := by
      exact_mod_cast (by omega : 0 < cutoff)
    have log_positive : (0 : ℝ) < Real.log (cutoff : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < cutoff))
    have log_monotone : Real.log (2 : ℝ) ≤ Real.log (cutoff : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast at_least_two)
    have natural_log := Real.natLog_le_logb cutoff 2
    simp only [Real.logb, Nat.cast_ofNat] at natural_log
    have one_log : (1 : ℝ) ≤ Real.log (cutoff : ℝ) / Real.log 2 :=
      (le_div_iff₀ log_two_positive).mpr (by simpa using log_monotone)
    have binary_log :
        (Nat.log 2 cutoff : ℝ) + 1 ≤
          2 * (Real.log (cutoff : ℝ) / Real.log 2) := by
      linarith
    have square_root :
        (Nat.sqrt cutoff : ℝ) ≤ (cutoff : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.nat_sqrt_le_real_sqrt
    have root_positive : 0 < (cutoff : ℝ) ^ (1 / 2 : ℝ) := by
      positivity
    have root_square :
        (cutoff : ℝ) ^ (1 / 2 : ℝ) *
          (cutoff : ℝ) ^ (1 / 2 : ℝ) = cutoff := by
      rw [← Real.rpow_add positive]
      norm_num
    have ratio :
        (cutoff : ℝ) ^ (1 / 2 : ℝ) / (cutoff : ℝ) =
          1 / (cutoff : ℝ) ^ (1 / 2 : ℝ) := by
      apply (div_eq_div_iff positive.ne' root_positive.ne').mpr
      simpa using root_square
    calc
      (Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1) *
          Real.log (cutoff : ℝ) ^ rank / (cutoff : ℝ) ≤
        (cutoff : ℝ) ^ (1 / 2 : ℝ) *
          (2 * (Real.log (cutoff : ℝ) / Real.log 2)) *
            Real.log (cutoff : ℝ) ^ rank / (cutoff : ℝ) := by
          gcongr
      _ = (2 / Real.log 2) *
          Real.log (cutoff : ℝ) ^ (rank + 1) *
            ((cutoff : ℝ) ^ (1 / 2 : ℝ) / (cutoff : ℝ)) := by
          rw [pow_succ]
          field_simp
      _ = (2 / Real.log 2) *
          (Real.log (cutoff : ℝ) ^ (rank + 1) /
            (cutoff : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [ratio]
          ring

/-- Arbitrary fixed-rank, arbitrary positive-dimensional proper-prime-power
removal.  An `O(N^(dimension-1))` bound for every actual affine fiber implies
that the complete genuine von Mangoldt proper-prime-power error is
`o(N^dimension)`.  This covers BOTH the two-dimensional single-pattern and
three-dimensional paired/shared-target applications without bounding rank. -/
theorem adaptiveMixedVonMangoldtPrimePowerExceptions_normalized_tendsto_zero
    {ι α : Type*} (forms : Finset ι) (points : ℕ → Finset α)
    (value : ι → ℕ → α → ℕ) (dimension coefficient : ℕ)
    (dimension_positive : 0 < dimension)
    (bounded : ∀ cutoff : ℕ, ∀ point ∈ points cutoff,
      ∀ index ∈ forms, value index cutoff point ∈ Finset.Ioc 0 cutoff)
    (fibers : ∀ cutoff : ℕ, ∀ index ∈ forms,
      ∀ power ∈ Erdos689.ternaryProperPrimePowers cutoff,
        ((points cutoff).filter
          fun point => value index cutoff point = power).card ≤
            coefficient * cutoff ^ (dimension - 1)) :
    Tendsto
      (fun cutoff : ℕ =>
        (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
          (points cutoff) forms (fun index point => value index cutoff point),
            adaptiveMixedVonMangoldtProduct forms
              (fun index point => value index cutoff point) point) /
                (cutoff : ℝ) ^ dimension)
      atTop (nhds 0) := by
  have upper_limit :
      Tendsto
        (fun cutoff : ℕ =>
          ((forms.card : ℝ) * (coefficient : ℝ)) *
            ((Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1) *
              Real.log (cutoff : ℝ) ^ forms.card / (cutoff : ℝ)))
        atTop (nhds 0) := by
    simpa using
      (adaptiveMixedProperPrimePowerScaleError_tendsto_zero forms.card).const_mul
        ((forms.card : ℝ) * (coefficient : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds upper_limit ?_ ?_
  · exact Eventually.of_forall fun cutoff =>
      div_nonneg (Finset.sum_nonneg fun point _ =>
        adaptiveMixedVonMangoldtProduct_nonneg forms
          (fun index point => value index cutoff point) point) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with cutoff at_least_one
    have positive : (0 : ℝ) < (cutoff : ℝ) := by
      exact_mod_cast at_least_one
    have power_positive : (0 : ℝ) < (cutoff : ℝ) ^ dimension := by
      positivity
    have exception_bound :=
      adaptiveMixedVonMangoldtPrimePowerExceptions_weight_le
        (points cutoff) forms (fun index point => value index cutoff point)
        cutoff (coefficient * cutoff ^ (dimension - 1))
        (bounded cutoff) (fibers cutoff)
    calc
      (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
          (points cutoff) forms (fun index point => value index cutoff point),
            adaptiveMixedVonMangoldtProduct forms
              (fun index point => value index cutoff point) point) /
                (cutoff : ℝ) ^ dimension ≤
          ((forms.card : ℝ) *
            ((coefficient * cutoff ^ (dimension - 1) : ℕ) : ℝ) *
              (Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1) *
                Real.log (cutoff : ℝ) ^ forms.card) /
                  (cutoff : ℝ) ^ dimension := by
          exact (div_le_div_iff_of_pos_right power_positive).mpr exception_bound
      _ = ((forms.card : ℝ) * (coefficient : ℝ)) *
            ((Nat.sqrt cutoff : ℝ) * ((Nat.log 2 cutoff : ℝ) + 1) *
              Real.log (cutoff : ℝ) ^ forms.card / (cutoff : ℝ)) := by
          simp only [Nat.cast_mul, Nat.cast_pow]
          have power_identity :
              (cutoff : ℝ) ^ dimension =
                (cutoff : ℝ) ^ (dimension - 1) * (cutoff : ℝ) := by
            rw [← pow_succ]
            congr 1
            omega
          rw [power_identity]
          field_simp

end Erdos1139

