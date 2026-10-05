module

public import AdaptiveMixedPrimePowerNegligible1139
public import AdaptiveMixedLogWeightNormalization1139

@[expose] public section


/-!
# Exact arbitrary-rank von Mangoldt to prime-count transfer

The published finite-complexity linear-forms theorem is naturally expressed
using products of von Mangoldt weights.  The actual #1139 construction uses
unweighted counts of genuinely prime affine values.  This module proves their
equivalence at EVERY FIXED finite form rank, using the already established
proper-prime-power error and the uniform logarithmic-weight sandwich.

The dimension, point family, affine values, and fiber bound remain explicit.
No Green--Tao theorem, arbitrary-rank prime-pattern count, or unconditional
solution of #1139 is asserted.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- The actual simultaneous-prime points inside an arbitrary finite ambient
family.  Every prime-form index is retained, including label coordinates. -/
noncomputable def adaptiveMixedAllPrimePoints
    {ι α : Type*} (points : Finset α) (forms : Finset ι)
    (value : ι → α → ℕ) : Finset α := by
  classical
  exact points.filter fun point => ∀ index ∈ forms, (value index point).Prime

/-- On a genuine all-prime point the actual von Mangoldt product is EXACTLY
the product of the logarithms of the true indexed prime values. -/
theorem adaptiveMixedVonMangoldtProduct_eq_prime_log_product
    {ι α : Type*} (points : Finset α) (forms : Finset ι)
    (value : ι → α → ℕ) {point : α}
    (selected : point ∈ adaptiveMixedAllPrimePoints points forms value) :
    adaptiveMixedVonMangoldtProduct forms value point =
      ∏ index ∈ forms, Real.log (value index point : ℝ) := by
  classical
  have primes : ∀ index ∈ forms, (value index point).Prime :=
    (Finset.mem_filter.mp selected).2
  unfold adaptiveMixedVonMangoldtProduct
  apply Finset.prod_congr rfl
  intro index indexed
  exact ArithmeticFunction.vonMangoldt_apply_prime (primes index indexed)

/-- The unrestricted genuine von Mangoldt sum has EXACTLY the same normalized
asymptotic as its prime-only logarithmically weighted part whenever the true
proper-prime-power fibers have the standard codimension-one bound. -/
theorem adaptiveMixedVonMangoldt_asymptotic_iff_prime_log_sum
    {ι α : Type*} (forms : Finset ι)
    (points : ℕ → Finset α) (value : ι → α → ℕ)
    (dimension coefficient : ℕ) (limit : ℝ)
    (dimension_positive : 0 < dimension)
    (bounded : ∀ cutoff : ℕ, ∀ point ∈ points cutoff,
      ∀ index ∈ forms, value index point ∈ Finset.Ioc 0 cutoff)
    (fibers : ∀ cutoff : ℕ, ∀ index ∈ forms,
      ∀ power ∈ Erdos689.ternaryProperPrimePowers cutoff,
        ((points cutoff).filter
          fun point => value index point = power).card ≤
            coefficient * cutoff ^ (dimension - 1)) :
    Tendsto
      (fun cutoff : ℕ =>
        (∑ point ∈ points cutoff,
          adaptiveMixedVonMangoldtProduct forms value point) /
            (cutoff : ℝ) ^ dimension)
      atTop (nhds limit) ↔
    Tendsto
      (fun cutoff : ℕ =>
        (∑ point ∈ adaptiveMixedAllPrimePoints
          (points cutoff) forms value,
            ∏ index ∈ forms, Real.log (value index point : ℝ)) /
              (cutoff : ℝ) ^ dimension)
      atTop (nhds limit) := by
  classical
  let bad : ℕ → ℝ := fun cutoff =>
    (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
      (points cutoff) forms value,
        adaptiveMixedVonMangoldtProduct forms value point) /
          (cutoff : ℝ) ^ dimension
  have bad_vanishes : Tendsto bad atTop (nhds (0 : ℝ)) := by
    exact adaptiveMixedVonMangoldtPrimePowerExceptions_normalized_tendsto_zero
      forms points (fun index _cutoff point => value index point)
        dimension coefficient dimension_positive bounded fibers
  have decomposition (cutoff : ℕ) :
      (∑ point ∈ points cutoff,
        adaptiveMixedVonMangoldtProduct forms value point) /
          (cutoff : ℝ) ^ dimension =
        (∑ point ∈ adaptiveMixedAllPrimePoints
          (points cutoff) forms value,
            ∏ index ∈ forms, Real.log (value index point : ℝ)) /
              (cutoff : ℝ) ^ dimension + bad cutoff := by
    have prime_sum :
        (∑ point ∈ adaptiveMixedAllPrimePoints
          (points cutoff) forms value,
            adaptiveMixedVonMangoldtProduct forms value point) =
          ∑ point ∈ adaptiveMixedAllPrimePoints
            (points cutoff) forms value,
              ∏ index ∈ forms, Real.log (value index point : ℝ) := by
      apply Finset.sum_congr rfl
      intro point selected
      exact adaptiveMixedVonMangoldtProduct_eq_prime_log_product
        (points cutoff) forms value selected
    have exact_split := adaptiveMixedVonMangoldtSum_eq_prime_sum_add_exceptions
      (points cutoff) forms value
    change
      (∑ point ∈ points cutoff,
        adaptiveMixedVonMangoldtProduct forms value point) /
          (cutoff : ℝ) ^ dimension =
        (∑ point ∈ adaptiveMixedAllPrimePoints
          (points cutoff) forms value,
            ∏ index ∈ forms, Real.log (value index point : ℝ)) /
              (cutoff : ℝ) ^ dimension +
          (∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
            (points cutoff) forms value,
              adaptiveMixedVonMangoldtProduct forms value point) /
                (cutoff : ℝ) ^ dimension
    rw [exact_split]
    change
      ((∑ point ∈ adaptiveMixedAllPrimePoints
        (points cutoff) forms value,
          adaptiveMixedVonMangoldtProduct forms value point) +
        ∑ point ∈ adaptiveMixedVonMangoldtPrimePowerExceptions
          (points cutoff) forms value,
            adaptiveMixedVonMangoldtProduct forms value point) /
              (cutoff : ℝ) ^ dimension = _
    rw [prime_sum]
    ring
  constructor
  · intro full
    have removed := full.sub bad_vanishes
    convert removed using 1
    · funext cutoff
      rw [decomposition cutoff]
      ring
    · simp
  · intro prime_only
    have restored := prime_only.add bad_vanishes
    convert restored using 1
    · funext cutoff
      exact decomposition cutoff
    · simp

/-- COMPLETE source-faithful arbitrary-fixed-rank transfer: the genuine
unrestricted von Mangoldt affine-system asymptotic is EQUIVALENT to its
correctly normalized count of points on which EVERY actual form is prime.

The only side conditions are the explicit standard individual fiber bound
and fixed positive linear bounds for the form values.  Neither a Green--Tao
prime-pattern theorem nor a growing-rank uniformity statement is assumed. -/
theorem adaptiveMixedVonMangoldt_asymptotic_iff_prime_count
    {ι α : Type*} (forms : Finset ι)
    (points : ℕ → Finset α) (value : ι → α → ℕ)
    (dimension coefficient : ℕ) (lower upper limit : ℝ)
    (dimension_positive : 0 < dimension)
    (lower_positive : 0 < lower)
    (upper_positive : 0 < upper)
    (bounded : ∀ cutoff : ℕ, ∀ point ∈ points cutoff,
      ∀ index ∈ forms, value index point ∈ Finset.Ioc 0 cutoff)
    (fibers : ∀ cutoff : ℕ, ∀ index ∈ forms,
      ∀ power ∈ Erdos689.ternaryProperPrimePowers cutoff,
        ((points cutoff).filter
          fun point => value index point = power).card ≤
            coefficient * cutoff ^ (dimension - 1))
    (linear_bounds : ∀ᶠ cutoff : ℕ in atTop,
      ∀ point ∈ points cutoff, ∀ index ∈ forms,
        lower * (cutoff : ℝ) ≤ (value index point : ℝ) ∧
          (value index point : ℝ) ≤ upper * (cutoff : ℝ)) :
    Tendsto
      (fun cutoff : ℕ =>
        (∑ point ∈ points cutoff,
          adaptiveMixedVonMangoldtProduct forms value point) /
            (cutoff : ℝ) ^ dimension)
      atTop (nhds limit) ↔
    Tendsto
      (fun cutoff : ℕ =>
        ((adaptiveMixedAllPrimePoints (points cutoff) forms value).card : ℝ) *
          Real.log (cutoff : ℝ) ^ forms.card /
            (cutoff : ℝ) ^ dimension)
      atTop (nhds limit) := by
  rw [adaptiveMixedVonMangoldt_asymptotic_iff_prime_log_sum
    forms points value dimension coefficient limit
      dimension_positive bounded fibers]
  apply adaptiveMixedFixedLinearLogWeighted_asymptotic_iff
    forms (fun cutoff => adaptiveMixedAllPrimePoints
      (points cutoff) forms value) value lower upper dimension limit
        lower_positive upper_positive
  filter_upwards [linear_bounds] with cutoff bounds point selected index indexed
  exact bounds point (Finset.mem_filter.mp selected).1 index indexed

end Erdos1139

