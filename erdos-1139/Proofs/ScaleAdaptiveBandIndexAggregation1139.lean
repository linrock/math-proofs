module

public import ScaleAdaptiveTruncatedBandFirstMoment1139
public import AdaptiveSupportIdentity1139

@[expose] public section


/-!
# Genuine physical-index aggregation on a constant residue band

On the actual target cell `(2*m,2*m+1)`, every physical index

    m < i < 2*m

has an UNCLIPPED label fiber for every normalized band
`0 ≤ u < v ≤ 1`.  Its target-truncated first coefficient, after division
by the genuine constant-band label degree, is `1/i`.

For supported semiprime type `s`, the exact JOINT sample marginal is
`F/s`, while the conditional target load is `s/i`.  The type cancels:
both prime and semiprime types have the exact aggregate profile

    F * ∑_{m<i<2m} 1/i.

The finite reciprocal sum is at least `1/4` for all `m ≥ 2`.  These are
actual sample-marginal and Green--Tao main-coefficient identities; no
simultaneous prime witness, target cover, or unexplained per-index
activation is asserted.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1139

/-- The exact genuine UNCLIPPED physical-index shell for the target cell
`(2*m,2*m+1)`.  Its endpoints are excluded because the low absolute residue
band genuinely clips there. -/
def scaleAdaptiveBandInteriorIndices (m : ℕ) : Finset ℕ :=
  Finset.Ioo m (2 * m)

/-- The exact size of the physical-index shell; for `m ≥ 1` it equals `m-1`.
In particular, the physical endpoints are never accidentally counted. -/
theorem scaleAdaptiveBandInteriorIndices_card (m : ℕ) :
    (scaleAdaptiveBandInteriorIndices m).card = m - 1 := by
  simp [scaleAdaptiveBandInteriorIndices]
  omega

/-- Every genuine shell index is positive and lies strictly below `2*m`. -/
theorem scaleAdaptiveBandInteriorIndices_mem
    {m index : ℕ}
    (selected : index ∈ scaleAdaptiveBandInteriorIndices m) :
    m < index ∧ index < 2 * m := by
  simpa [scaleAdaptiveBandInteriorIndices] using selected

/-- If the physical pattern scale contains the whole shell, every sampled
index lies in the manuscript's TRUE index interval `1,...,scale`. -/
theorem scaleAdaptiveBandInteriorIndices_subset_physical
    {m scale : ℕ}
    (within_scale : 2 * m ≤ scale + 1) :
    scaleAdaptiveBandInteriorIndices m ⊆ Finset.Icc 1 scale := by
  intro index selected
  have bounds := scaleAdaptiveBandInteriorIndices_mem selected
  simp only [Finset.mem_Icc]
  omega

/-- Every shell index is genuinely UNCLIPPED on the entire normalized target
cell `(2*m,2*m+1)` for any physical constant band in `[0,1]`. -/
theorem scaleAdaptiveBandInteriorIndices_unclipped
    {m index : ℕ} {lower upper : ℝ}
    (lower_nonnegative : 0 ≤ lower)
    (upper_bounded : upper ≤ 1)
    (selected : index ∈ scaleAdaptiveBandInteriorIndices m) :
    (index : ℝ) + upper ≤ (2 * m : ℕ) ∧
      (2 * m + 1 : ℕ) ≤ 2 * (index : ℝ) + lower := by
  have bounds := scaleAdaptiveBandInteriorIndices_mem selected
  have upper_index : index + 1 ≤ 2 * m := by omega
  have lower_index : m + 1 ≤ index := by omega
  have upper_real : (index : ℝ) + 1 ≤ (2 * m : ℕ) := by
    exact_mod_cast upper_index
  have lower_real : (m : ℝ) + 1 ≤ (index : ℝ) := by
    exact_mod_cast lower_index
  constructor
  · linarith
  · push_cast
    nlinarith

/-- Uniform quantitative NONVANISHING of the actual physical-index harmonic
window.  This elementary bound needs no asymptotic and is valid for every
`m ≥ 2`. -/
theorem scaleAdaptiveBandInteriorIndices_reciprocal_sum_ge_quarter
    {m : ℕ} (large : 2 ≤ m) :
    (1 / 4 : ℝ) ≤
      ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
        (index : ℝ)⁻¹ := by
  have m_positive : (0 : ℝ) < m := by
    exact_mod_cast (show 0 < m by omega)
  have pointwise : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      (2 * (m : ℝ))⁻¹ ≤ (index : ℝ)⁻¹ := by
    intro index selected
    have bounds := scaleAdaptiveBandInteriorIndices_mem selected
    have positive : (0 : ℝ) < index := by
      exact_mod_cast (show 0 < index by omega)
    have bounded : (index : ℝ) ≤ 2 * (m : ℝ) := by
      exact_mod_cast (show index ≤ 2 * m by omega)
    simpa [one_div] using one_div_le_one_div_of_le positive bounded
  have aggregate := Finset.sum_le_sum pointwise
  have card := scaleAdaptiveBandInteriorIndices_card m
  have card_real :
      ((scaleAdaptiveBandInteriorIndices m).card : ℝ) =
        (m : ℝ) - 1 := by
    rw [card, Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have sum_constant :
      ∑ _index ∈ scaleAdaptiveBandInteriorIndices m,
        (2 * (m : ℝ))⁻¹ =
          ((m : ℝ) - 1) / (2 * (m : ℝ)) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [card_real]
    rfl
  rw [sum_constant] at aggregate
  have lower : (1 / 4 : ℝ) ≤
      ((m : ℝ) - 1) / (2 * (m : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have cast_large : (2 : ℝ) ≤ m := by exact_mod_cast large
    nlinarith
  exact lower.trans aggregate

/-- Prime-type samples from the shared outcome pool really activate the
corresponding TRUE physical index whenever the index is within scale. -/
theorem scaleAdaptiveBandPrimeSample_index_active
    {support : Finset ℕ} {m scale index : ℕ} {outcome : ℕ × ℕ}
    (within_scale : 2 * m ≤ scale + 1)
    (selected : index ∈ scaleAdaptiveBandInteriorIndices m)
    (sample : outcome ∈ adaptiveMixedPrimePatternSamples
      support scale index) :
    index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome := by
  have physical := scaleAdaptiveBandInteriorIndices_subset_physical
    within_scale selected
  apply Finset.mem_union_left
  simp only [adaptiveMixedOutcomePrimeIndices,
    Finset.mem_filter]
  exact ⟨physical, sample⟩

/-- Semiprime samples of a genuinely supported type activate the same
shared-outcome physical index; outcomes are never sampled independently
for separate indices or target types. -/
theorem scaleAdaptiveBandSemiprimeSample_index_active
    {support : Finset ℕ} {type m scale index : ℕ} {outcome : ℕ × ℕ}
    (type_supported : type ∈ support)
    (within_scale : 2 * m ≤ scale + 1)
    (selected : index ∈ scaleAdaptiveBandInteriorIndices m)
    (sample : outcome ∈ adaptiveMixedSemiprimePatternSamples
      support type scale index) :
    index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome := by
  have physical := scaleAdaptiveBandInteriorIndices_subset_physical
    within_scale selected
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨type, type_supported, ?_⟩
  simp only [adaptiveMixedOutcomeSemiprimeIndices,
    Finset.mem_filter]
  exact ⟨physical, sample⟩

/-- Every genuine adaptive finite local factor is strictly positive on an
actual selected prime support. -/
theorem scaleAdaptiveBandPatternEulerFactor_pos
    (support : Finset ℕ) (scale : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    0 < adaptivePatternEulerFactor support scale := by
  rw [adaptivePatternEulerFactor_eq_union]
  apply adaptivePrimeEulerProduct_pos
  intro prime selected
  rcases Finset.mem_union.mp selected with selected | selected
  · exact primes prime selected
  · exact Nat.prime_of_mem_primesLE selected

/-- EXACT aggregate PRIME-type profile across the genuine physical-index
shell, using the TRUE shared sample-space marginal at every index. -/
theorem scaleAdaptiveBandPrimeIndexProfile_eq_factor_mul_harmonic
    (support : Finset ℕ) (scale m : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    (∑ index ∈ scaleAdaptiveBandInteriorIndices m,
      (((adaptiveMixedPrimePatternSamples
        support scale index).card : ℝ) /
        ((adaptiveMixedTypeModulus support *
          adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)) *
        (index : ℝ)⁻¹) =
      adaptivePatternEulerFactor support scale *
        ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
          (index : ℝ)⁻¹ := by
  simp_rw [adaptiveMixedPrimePattern_probability_eq_factor
    support scale _ primes]
  rw [Finset.mul_sum]

/-- EXACT aggregate SEMIPRIME-type profile.  The true joint sample marginal
`F/s` cancels its true conditional target load `s/i`, giving EXACTLY the
same profile as prime targets; this uses one common outcome space. -/
theorem scaleAdaptiveBandSemiprimeIndexProfile_eq_factor_mul_harmonic
    {support : Finset ℕ} {type : ℕ} (scale m : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : type ∈ support) :
    (∑ index ∈ scaleAdaptiveBandInteriorIndices m,
      (((adaptiveMixedSemiprimePatternSamples
        support type scale index).card : ℝ) /
        ((adaptiveMixedTypeModulus support *
          adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)) *
        ((type : ℝ) * (index : ℝ)⁻¹)) =
      adaptivePatternEulerFactor support scale *
        ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
          (index : ℝ)⁻¹ := by
  have type_positive : (0 : ℝ) < type := by
    exact_mod_cast (primes type type_supported).pos
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _selected
  rw [adaptiveMixedSemiprimePattern_probability_eq_factor_div
    scale index primes type_supported]
  field_simp [type_positive.ne']

/-- Uniform positive PRIME-target profile on EVERY genuine physical shell,
with no unproved prime-pattern or index-activation assumption. -/
theorem scaleAdaptiveBandPrimeIndexProfile_ge_factor_quarter
    (support : Finset ℕ) (scale m : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (large : 2 ≤ m) :
    adaptivePatternEulerFactor support scale / 4 ≤
      ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
        (((adaptiveMixedPrimePatternSamples
          support scale index).card : ℝ) /
          ((adaptiveMixedTypeModulus support *
            adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)) *
          (index : ℝ)⁻¹ := by
  rw [scaleAdaptiveBandPrimeIndexProfile_eq_factor_mul_harmonic
    support scale m primes]
  have positive := scaleAdaptiveBandPatternEulerFactor_pos
    support scale primes
  have harmonic := scaleAdaptiveBandInteriorIndices_reciprocal_sum_ge_quarter
    large
  have multiplied := mul_le_mul_of_nonneg_left harmonic positive.le
  calc
    adaptivePatternEulerFactor support scale / 4 =
        adaptivePatternEulerFactor support scale * (1 / 4 : ℝ) := by ring
    _ ≤ _ := multiplied

/-- Uniform positive SEMIPRIME-target profile for EVERY genuine supported
type.  Crucially the lower bound is independent of the type `s`. -/
theorem scaleAdaptiveBandSemiprimeIndexProfile_ge_factor_quarter
    {support : Finset ℕ} {type : ℕ} (scale m : ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (type_supported : type ∈ support)
    (large : 2 ≤ m) :
    adaptivePatternEulerFactor support scale / 4 ≤
      ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
        (((adaptiveMixedSemiprimePatternSamples
          support type scale index).card : ℝ) /
          ((adaptiveMixedTypeModulus support *
            adaptiveMixedOutsideModulus support scale : ℕ) : ℝ)) *
          ((type : ℝ) * (index : ℝ)⁻¹) := by
  rw [scaleAdaptiveBandSemiprimeIndexProfile_eq_factor_mul_harmonic
    scale m primes type_supported]
  have positive := scaleAdaptiveBandPatternEulerFactor_pos
    support scale primes
  have harmonic := scaleAdaptiveBandInteriorIndices_reciprocal_sum_ge_quarter
    large
  have multiplied := mul_le_mul_of_nonneg_left harmonic positive.le
  calc
    adaptivePatternEulerFactor support scale / 4 =
        adaptivePatternEulerFactor support scale * (1 / 4 : ℝ) := by ring
    _ ≤ _ := multiplied

/-- EXACT single-index normalization of the TRUE target-truncated first
Green--Tao main term by its TRUE constant-band label degree.  All singular,
width, and conductor factors cancel; the remaining physical profile is
`targetLength/index`. -/
theorem scaleAdaptiveTruncatedBand_normalized_first_main_term
    {support : Finset ℕ} {index : ℕ}
    {lower upper targetLower targetUpper singular : ℝ}
    (index_positive : 0 < index)
    (band_nonempty : lower < upper)
    (modulus_positive : 0 < adaptiveMixedTypeModulus support)
    (singular_positive : 0 < singular) :
    ((targetUpper - targetLower) * (upper - lower) /
      ((index : ℝ) * (adaptiveMixedTypeModulus support : ℝ)) * singular) /
      (((upper - lower) /
        (adaptiveMixedTypeModulus support : ℝ)) * singular) =
      (targetUpper - targetLower) / (index : ℝ) := by
  have index_real : (0 : ℝ) < index := by
    exact_mod_cast index_positive
  have modulus_real : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast modulus_positive
  have width_nonzero : upper - lower ≠ 0 :=
    ne_of_gt (sub_pos.mpr band_nonempty)
  field_simp [index_real.ne', modulus_real.ne', width_nonzero,
    singular_positive.ne']

/-- Exact finite index aggregation of the genuine degree-normalized first
Green--Tao MAIN COEFFICIENT, permitting a different actual positive singular
factor at every index.  Pattern singularities cancel separately rather than
being averaged incorrectly. -/
theorem scaleAdaptiveBand_normalized_first_main_terms_sum
    {support : Finset ℕ} {m : ℕ}
    {lower upper targetLower targetUpper : ℝ}
    (singular : ℕ → ℝ)
    (band_nonempty : lower < upper)
    (modulus_positive : 0 < adaptiveMixedTypeModulus support)
    (singular_positive : ∀ index ∈ scaleAdaptiveBandInteriorIndices m,
      0 < singular index) :
    (∑ index ∈ scaleAdaptiveBandInteriorIndices m,
      ((targetUpper - targetLower) * (upper - lower) /
        ((index : ℝ) * (adaptiveMixedTypeModulus support : ℝ)) *
          singular index) /
        (((upper - lower) /
          (adaptiveMixedTypeModulus support : ℝ)) * singular index)) =
      (targetUpper - targetLower) *
        ∑ index ∈ scaleAdaptiveBandInteriorIndices m,
          (index : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index selected
  have bounds := scaleAdaptiveBandInteriorIndices_mem selected
  have exact_term := scaleAdaptiveTruncatedBand_normalized_first_main_term
    (support := support) (lower := lower) (upper := upper)
      (targetLower := targetLower) (targetUpper := targetUpper)
      (singular := singular index)
      (show 0 < index by omega)
      band_nonempty modulus_positive (singular_positive index selected)
  simpa [div_eq_mul_inv] using exact_term

end Erdos1139
