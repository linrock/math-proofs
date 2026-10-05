module

public import ScaleAdaptiveGTZDegreeRegularity1139
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section


/-!
# Actual prime-label slices and signed degree variance

The original and shared-label Green--Tao fields determine the first and
second moments of the ACTUAL signed center fibers.  Prime-label counting is
an independent, already audited consequence of the prime number theorem.

The centered second moment therefore has an exact archimedean limit.  A
constant expected degree is justified precisely on a constant-width physical
fiber, not on the full moving residue strip.  No degree-regularity,
exceptional-label, or concentration hypothesis is introduced here.
-/

open Finset Filter MeasureTheory Set
open scoped BigOperators Topology Interval ENNReal

namespace Erdos1139

set_option maxHeartbeats 800000

/-- The exact actual dyadic prime labels are the difference of the two
ordinary CLOSED prime-counting supports; neither endpoint is discarded. -/
theorem scaleAdaptiveSignedDegreePrimeLabels_eq_prime_support_difference
    (N : ℕ) :
    scaleAdaptiveSignedDegreePrimeLabels N =
      Nat.primesLE (2 * N) \ Nat.primesLE N := by
  ext label
  simp only [scaleAdaptiveSignedDegreePrimeLabels, Finset.mem_filter,
    Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨large, bounded⟩, prime⟩
    exact ⟨⟨bounded, prime⟩,
      fun small => (Nat.not_le_of_gt large) small.1⟩
  · rintro ⟨⟨bounded, prime⟩, not_small⟩
    exact ⟨⟨Nat.lt_of_not_ge fun small =>
      not_small ⟨small, prime⟩, bounded⟩, prime⟩

/-- Exact cardinality of the real dyadic prime-label pool. -/
theorem scaleAdaptiveSignedDegreePrimeLabels_card_eq_primeCounting_sub
    (N : ℕ) :
    (scaleAdaptiveSignedDegreePrimeLabels N).card =
      Nat.primeCounting (2 * N) - Nat.primeCounting N := by
  rw [scaleAdaptiveSignedDegreePrimeLabels_eq_prime_support_difference]
  rw [Finset.card_sdiff_of_subset
    (Nat.primesLE_mono (by omega : N ≤ 2 * N))]
  simp only [Nat.primesLE_card_eq_primeCounting]

/-- Doubling the actual prime-label scale changes its logarithm only by a
lower-order term. -/
theorem scaleAdaptivePrimeLabel_log_double_ratio_tendsto_one :
    Tendsto
      (fun N : ℕ =>
        Real.log ((2 * N : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (nhds (1 : ℝ)) := by
  have log_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have correction :
      Tendsto (fun N : ℕ => Real.log (2 : ℝ) / Real.log (N : ℝ))
        atTop (nhds (0 : ℝ)) :=
    (tendsto_const_nhds (x := Real.log (2 : ℝ))).div_atTop log_top
  have target :
      Tendsto
        (fun N : ℕ =>
          Real.log (2 : ℝ) / Real.log (N : ℝ) + 1)
        atTop (nhds (1 : ℝ)) := by
    simpa using correction.add (tendsto_const_nhds (x := (1 : ℝ)))
  apply target.congr'
  filter_upwards [eventually_ge_atTop 2] with N large
  have N_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have logarithm_nonzero : Real.log (N : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (by omega : 0 < N)
    · exact_mod_cast (by omega : N ≠ 1)
  push_cast
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) N_nonzero]
  field_simp

/-- The already audited ordinary PNT gives the correct doubled-endpoint
coefficient when normalized at the ORIGINAL dyadic scale. -/
theorem scaleAdaptivePrimeCounting_double_normalized_tendsto_two :
    Tendsto
      (fun N : ℕ =>
        (Nat.primeCounting (2 * N) : ℝ) *
          Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (2 : ℝ)) := by
  have identity_top : Tendsto (fun N : ℕ => N) atTop atTop := tendsto_id
  have doubled_top : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    Filter.tendsto_atTop_mono (fun N => by omega) identity_top
  have pnt := primeCounting_normalized_tendsto_one.comp doubled_top
  have inverse_log_ratio :=
    scaleAdaptivePrimeLabel_log_double_ratio_tendsto_one.inv₀ one_ne_zero
  have combined := (pnt.const_mul (2 : ℝ)).mul inverse_log_ratio
  have target :
      Tendsto
        (fun N : ℕ =>
          2 * ((Nat.primeCounting (2 * N) : ℝ) /
            (((2 * N : ℕ) : ℝ) /
              Real.log ((2 * N : ℕ) : ℝ))) *
            (Real.log ((2 * N : ℕ) : ℝ) /
              Real.log (N : ℝ))⁻¹)
        atTop (nhds (2 : ℝ)) := by
    simpa using combined
  apply target.congr'
  filter_upwards [eventually_ge_atTop 2] with N large
  have N_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have log_nonzero : Real.log (N : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (by omega : 0 < N)
    · exact_mod_cast (by omega : N ≠ 1)
  have double_nonzero : ((2 * N : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : 2 * N ≠ 0)
  have double_log_nonzero : Real.log ((2 * N : ℕ) : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (by omega : 0 < 2 * N)
    · exact_mod_cast (by omega : 2 * N ≠ 1)
  have double_log_real_nonzero : Real.log (2 * (N : ℝ)) ≠ 0 := by
    exact_mod_cast double_log_nonzero
  push_cast
  field_simp [N_nonzero, log_nonzero, double_log_real_nonzero]

/-- The genuine prime-label pool has asymptotic density exactly one in its
true normalization `N / log N`; this uses the proved PNT, not a heuristic. -/
theorem scaleAdaptiveSignedDegreePrimeLabels_normalized_tendsto_one :
    Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
          Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (1 : ℝ)) := by
  have ordinary :
      Tendsto
        (fun N : ℕ =>
          (Nat.primeCounting N : ℝ) * Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (1 : ℝ)) := by
    apply primeCounting_normalized_tendsto_one.congr'
    filter_upwards [eventually_ge_atTop 2] with N large
    have N_nonzero : (N : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : N ≠ 0)
    have log_nonzero : Real.log (N : ℝ) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      · exact_mod_cast (by omega : 0 < N)
      · exact_mod_cast (by omega : N ≠ 1)
    field_simp
  have difference :=
    scaleAdaptivePrimeCounting_double_normalized_tendsto_two.sub ordinary
  have target :
      Tendsto
        (fun N : ℕ =>
          (Nat.primeCounting (2 * N) : ℝ) *
              Real.log (N : ℝ) / (N : ℝ) -
            (Nat.primeCounting N : ℝ) *
              Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (1 : ℝ)) := by
    convert difference using 1
    norm_num
  apply target.congr'
  exact Filter.Eventually.of_forall fun N => by
    dsimp
    rw [scaleAdaptiveSignedDegreePrimeLabels_card_eq_primeCounting_sub,
      Nat.cast_sub (Nat.monotone_primeCounting (by omega : N ≤ 2 * N))]
    ring_nf

/-- Both actual signed prime-label degree moments have the SAME genuine
singular constant.  Its uniqueness follows from their common collision-aware
partial Euler products; it is not an independently supplied hypothesis. -/
theorem scaleAdaptiveSignedDegree_first_and_secondMoments_tendsto_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support outcome.1)
    (convex_shared : Convex ℝ
      (scaleAdaptiveSignedSharedLabelDomainLift domain))
    (open_shared : IsOpen
      (scaleAdaptiveSignedSharedLabelDomainLift domain))
    (nonempty_shared :
      (scaleAdaptiveSignedSharedLabelDomainLift domain).Nonempty)
    (physical_shared : scaleAdaptiveSignedSharedLabelDomainLift domain ⊆
      adaptiveMixedSignedSharedLabelPhysicalDomain
        support outcome.1 outcome.1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedOriginalPrimeRealizations
            support scale outcome domain N).card : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card + 1) /
                (N : ℝ) ^ 2)
        atTop (nhds ((volume domain).toReal * singular)) ∧
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedSharedLabelPrimeRealizations
            support scale outcome outcome
              (scaleAdaptiveSignedSharedLabelDomainLift domain) N).card : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card +
                 (adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card + 1) /
                (N : ℝ) ^ 3)
        atTop (nhds
          ((volume (scaleAdaptiveSignedSharedLabelDomainLift domain)).toReal *
            singular ^ 2)) := by
  obtain ⟨singular, positive, singular_converges, first⟩ :=
    scaleAdaptiveSignedOriginalPrimeRealizations_positive_asymptotic
      green_tao support scale outcome domain
      primes convex open_domain nonempty physical
  obtain ⟨first_singular, second_singular,
      first_converges, second_converges, second⟩ :=
    green_tao.shared_label support scale outcome outcome
      (scaleAdaptiveSignedSharedLabelDomainLift domain)
      primes convex_shared open_shared nonempty_shared physical_shared
  have first_same : singular = first_singular :=
    tendsto_nhds_unique singular_converges first_converges
  have second_same : singular = second_singular :=
    tendsto_nhds_unique singular_converges second_converges
  subst first_singular
  subst second_singular
  refine ⟨singular, positive, first, ?_⟩
  simpa [pow_two, mul_assoc] using second

/-- EXACT asymptotic centered degree variance on the actual prime-label pool.
The formula retains the true signed first-fiber and squared-fiber volumes.
For the whole physical wedge these do NOT cancel; for a constant-width
residue band they do.  Only the original/shared-label Green--Tao fields and
the proved ordinary PNT are used. -/
theorem scaleAdaptiveSignedDegree_normalizedCenteredVariance_tendsto_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support outcome.1)
    (convex_shared : Convex ℝ
      (scaleAdaptiveSignedSharedLabelDomainLift domain))
    (open_shared : IsOpen
      (scaleAdaptiveSignedSharedLabelDomainLift domain))
    (nonempty_shared :
      (scaleAdaptiveSignedSharedLabelDomainLift domain).Nonempty)
    (physical_shared : scaleAdaptiveSignedSharedLabelDomainLift domain ⊆
      adaptiveMixedSignedSharedLabelPhysicalDomain
        support outcome.1 outcome.1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          (∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            ((scaleAdaptiveSignedDegree
                support scale outcome domain N label : ℝ) -
              (volume domain).toReal * singular * (N : ℝ) /
                Real.log (N : ℝ) ^
                  (adaptiveMixedOutcomeActiveIndices
                    support scale outcome).card) ^ 2) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card +
               (adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 3)
        atTop (nhds
          (singular ^ 2 *
            ((volume (scaleAdaptiveSignedSharedLabelDomainLift domain)).toReal -
              (volume domain).toReal ^ 2))) := by
  obtain ⟨singular, positive, first, second⟩ :=
    scaleAdaptiveSignedDegree_first_and_secondMoments_tendsto_of_GTZ
      green_tao support scale outcome domain primes convex open_domain
      nonempty physical convex_shared open_shared nonempty_shared physical_shared
  refine ⟨singular, positive, ?_⟩
  let width := (volume domain).toReal
  let rank := (adaptiveMixedOutcomeActiveIndices support scale outcome).card
  have prime_count := scaleAdaptiveSignedDegreePrimeLabels_normalized_tendsto_one
  have middle := first.const_mul (2 * width * singular)
  have last := prime_count.const_mul ((width * singular) ^ 2)
  have combined := (second.sub middle).add last
  have target :
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedSharedLabelPrimeRealizations
              support scale outcome outcome
                (scaleAdaptiveSignedSharedLabelDomainLift domain) N).card : ℝ) *
            Real.log (N : ℝ) ^ (rank + rank + 1) / (N : ℝ) ^ 3 -
          (2 * width * singular) *
            (((adaptiveMixedSignedOriginalPrimeRealizations
              support scale outcome domain N).card : ℝ) *
              Real.log (N : ℝ) ^ (rank + 1) / (N : ℝ) ^ 2) +
          ((width * singular) ^ 2) *
            (((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
              Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds
          (singular ^ 2 *
            ((volume (scaleAdaptiveSignedSharedLabelDomainLift domain)).toReal -
              (volume domain).toReal ^ 2))) := by
    convert combined using 1
    dsimp [width]
    ring_nf
  apply target.congr'
  filter_upwards [eventually_ge_atTop 2] with N large
  have N_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have log_nonzero : Real.log (N : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (by omega : 0 < N)
    · exact_mod_cast (by omega : N ≠ 1)
  dsimp [width, rank]
  rw [scaleAdaptiveSignedDegree_centeredVariance_eq_actual_counts]
  field_simp [N_nonzero, log_nonzero]
  ring_nf

/-- Whenever a genuine signed subwindow has CONSTANT physical center-fiber
width, its squared-fiber volume equals the square of its first volume, and
the exact prime-label centered variance genuinely tends to zero.  This is a
geometric identity, not an analytic degree-concentration hypothesis. -/
theorem scaleAdaptiveSignedDegree_normalizedCenteredVariance_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support outcome.1)
    (convex_shared : Convex ℝ
      (scaleAdaptiveSignedSharedLabelDomainLift domain))
    (open_shared : IsOpen
      (scaleAdaptiveSignedSharedLabelDomainLift domain))
    (nonempty_shared :
      (scaleAdaptiveSignedSharedLabelDomainLift domain).Nonempty)
    (physical_shared : scaleAdaptiveSignedSharedLabelDomainLift domain ⊆
      adaptiveMixedSignedSharedLabelPhysicalDomain
        support outcome.1 outcome.1)
    (constant_fiber_volume :
      (volume (scaleAdaptiveSignedSharedLabelDomainLift domain)).toReal =
        (volume domain).toReal ^ 2) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          (∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            ((scaleAdaptiveSignedDegree
                support scale outcome domain N label : ℝ) -
              (volume domain).toReal * singular * (N : ℝ) /
                Real.log (N : ℝ) ^
                  (adaptiveMixedOutcomeActiveIndices
                    support scale outcome).card) ^ 2) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card +
               (adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 3)
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, variance⟩ :=
    scaleAdaptiveSignedDegree_normalizedCenteredVariance_tendsto_of_GTZ
      green_tao support scale outcome domain primes convex open_domain
      nonempty physical convex_shared open_shared nonempty_shared physical_shared
  refine ⟨singular, positive, ?_⟩
  simpa [constant_fiber_volume] using variance

/-- The genuine constant-ABSOLUTE-residue band in the signed physical
coordinates.  Its center interval translates with the actual label and has
constant width `(upper-lower)/W` for EVERY outcome base.  The restriction
`upper ≤ 1` deliberately discards residues above `N`; it does not by itself
assert that all physical targets remain covered. -/
def scaleAdaptiveSignedConstantResidueBand
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ) : Set (ℝ × ℝ) :=
  {point |
    1 < point.1 ∧ point.1 < 2 ∧
      lower < (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 ∧
      (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 < upper}

/-- The constant-residue band has a genuinely OPEN signed physical domain. -/
theorem scaleAdaptiveSignedConstantResidueBand_isOpen
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ) :
    IsOpen (scaleAdaptiveSignedConstantResidueBand
      support base lower upper) := by
  let residue : (ℝ × ℝ) → ℝ := fun point =>
    (base : ℝ) * point.1 +
      (adaptiveMixedTypeModulus support : ℝ) * point.2
  have residue_continuous : Continuous residue := by
    exact (continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd)
  have equal :
      scaleAdaptiveSignedConstantResidueBand support base lower upper =
        (fun point : ℝ × ℝ => point.1) ⁻¹' Set.Ioo 1 2 ∩
          residue ⁻¹' Set.Ioo lower upper := by
    ext point
    simp [scaleAdaptiveSignedConstantResidueBand, residue]
    tauto
  rw [equal]
  exact (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_Ioo.preimage residue_continuous)

/-- The constant-residue band is convex, despite its necessarily negative
SIGNED centers for positive physical bases. -/
theorem scaleAdaptiveSignedConstantResidueBand_convex
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ) :
    Convex ℝ (scaleAdaptiveSignedConstantResidueBand
      support base lower upper) := by
  intro first first_selected second second_selected a b a_nonnegative
    b_nonnegative sum_one
  change
    1 < a * first.1 + b * second.1 ∧
      a * first.1 + b * second.1 < 2 ∧
      lower <
        (base : ℝ) * (a * first.1 + b * second.1) +
          (adaptiveMixedTypeModulus support : ℝ) *
            (a * first.2 + b * second.2) ∧
      (base : ℝ) * (a * first.1 + b * second.1) +
          (adaptiveMixedTypeModulus support : ℝ) *
            (a * first.2 + b * second.2) < upper
  have coordinates := (convex_Ioo (𝕜 := ℝ) (1 : ℝ) 2)
    ⟨first_selected.1, first_selected.2.1⟩
    ⟨second_selected.1, second_selected.2.1⟩
    a_nonnegative b_nonnegative sum_one
  have residues := (convex_Ioo (𝕜 := ℝ) lower upper)
    ⟨first_selected.2.2.1, first_selected.2.2.2⟩
    ⟨second_selected.2.2.1, second_selected.2.2.2⟩
    a_nonnegative b_nonnegative sum_one
  refine ⟨coordinates.1, coordinates.2, ?_, ?_⟩
  · calc
      lower <
          a * ((base : ℝ) * first.1 +
            (adaptiveMixedTypeModulus support : ℝ) * first.2) +
          b * ((base : ℝ) * second.1 +
            (adaptiveMixedTypeModulus support : ℝ) * second.2) :=
        residues.1
      _ = _ := by ring_nf
  · calc
      _ =
          a * ((base : ℝ) * first.1 +
            (adaptiveMixedTypeModulus support : ℝ) * first.2) +
          b * ((base : ℝ) * second.1 +
            (adaptiveMixedTypeModulus support : ℝ) * second.2) := by ring_nf
      _ < upper := residues.2

/-- Every point of the low constant-residue band satisfies the GENUINE
fundamental-strip inequalities for its actual varying prime label. -/
theorem scaleAdaptiveSignedConstantResidueBand_subset_physical
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ)
    (lower_nonnegative : 0 ≤ lower)
    (upper_bounded : upper ≤ 1) :
    scaleAdaptiveSignedConstantResidueBand support base lower upper ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support base := by
  intro point selected
  refine ⟨selected.1, selected.2.1, ?_, ?_⟩
  · linarith [selected.2.2.1]
  · linarith [selected.1, selected.2.2.2]

/-- The genuine band is exactly the region between its two translated signed
center bounds.  Crucially their difference is CONSTANT, even though each
individual bound moves linearly with the actual prime label. -/
theorem scaleAdaptiveSignedConstantResidueBand_eq_regionBetween
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    scaleAdaptiveSignedConstantResidueBand support base lower upper =
      regionBetween
        (fun label : ℝ =>
          (lower - (base : ℝ) * label) /
            (adaptiveMixedTypeModulus support : ℝ))
        (fun label : ℝ =>
          (upper - (base : ℝ) * label) /
            (adaptiveMixedTypeModulus support : ℝ))
        (Set.Ioo (1 : ℝ) 2) := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  ext point
  change
    (1 < point.1 ∧ point.1 < 2 ∧
      lower < (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 ∧
      (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 < upper) ↔
      (1 < point.1 ∧ point.1 < 2) ∧
        (lower - (base : ℝ) * point.1) /
            (adaptiveMixedTypeModulus support : ℝ) < point.2 ∧
          point.2 <
            (upper - (base : ℝ) * point.1) /
              (adaptiveMixedTypeModulus support : ℝ)
  constructor
  · rintro ⟨large, bounded, lower_bound, upper_bound⟩
    refine ⟨⟨large, bounded⟩, ?_, ?_⟩
    · apply (div_lt_iff₀ modulus_positive).mpr
      nlinarith
    · apply (lt_div_iff₀ modulus_positive).mpr
      nlinarith
  · rintro ⟨⟨large, bounded⟩, lower_bound, upper_bound⟩
    refine ⟨large, bounded, ?_, ?_⟩
    · have inequality := (div_lt_iff₀ modulus_positive).mp lower_bound
      nlinarith
    · have inequality := (lt_div_iff₀ modulus_positive).mp upper_bound
      nlinarith

/-- Exact first-fiber volume of the actual slanted residue band.  The signed
translation by `-base*label/W` contributes no spurious covolume factor. -/
theorem scaleAdaptiveSignedConstantResidueBand_volume
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (ordered : lower ≤ upper) :
    (volume (scaleAdaptiveSignedConstantResidueBand
      support base lower upper)).toReal =
        (upper - lower) / (adaptiveMixedTypeModulus support : ℝ) := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have width_nonnegative :
      0 ≤ (upper - lower) / (adaptiveMixedTypeModulus support : ℝ) :=
    div_nonneg (sub_nonneg.mpr ordered) modulus_positive.le
  rw [scaleAdaptiveSignedConstantResidueBand_eq_regionBetween
    support base lower upper primes]
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [volume_regionBetween_eq_lintegral'
    (by fun_prop) (by fun_prop) measurableSet_Ioo]
  have constant_integrand :
      (fun label : ℝ => ENNReal.ofReal
        (((fun label : ℝ =>
            (upper - (base : ℝ) * label) /
              (adaptiveMixedTypeModulus support : ℝ)) -
          (fun label : ℝ =>
            (lower - (base : ℝ) * label) /
              (adaptiveMixedTypeModulus support : ℝ))) label)) =
        fun _ : ℝ => ENNReal.ofReal
          ((upper - lower) /
            (adaptiveMixedTypeModulus support : ℝ)) := by
    funext label
    congr 1
    dsimp
    ring_nf
  rw [constant_integrand, MeasureTheory.setLIntegral_const,
    Real.volume_Ioo]
  norm_num [ENNReal.toReal_ofReal width_nonnegative]

/-- Every strictly positive-width band really contains a signed physical
point, including arbitrary positive bases with negative centers. -/
theorem scaleAdaptiveSignedConstantResidueBand_nonempty
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (strict : lower < upper) :
    (scaleAdaptiveSignedConstantResidueBand
      support base lower upper).Nonempty := by
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  refine ⟨((3 : ℝ) / 2,
    (((lower + upper) / 2) - (base : ℝ) * ((3 : ℝ) / 2)) /
      (adaptiveMixedTypeModulus support : ℝ)), ?_⟩
  change
    1 < (3 : ℝ) / 2 ∧ (3 : ℝ) / 2 < 2 ∧
      lower < (base : ℝ) * ((3 : ℝ) / 2) +
        (adaptiveMixedTypeModulus support : ℝ) *
          (((lower + upper) / 2 - (base : ℝ) * ((3 : ℝ) / 2)) /
            (adaptiveMixedTypeModulus support : ℝ)) ∧
      (base : ℝ) * ((3 : ℝ) / 2) +
        (adaptiveMixedTypeModulus support : ℝ) *
          (((lower + upper) / 2 - (base : ℝ) * ((3 : ℝ) / 2)) /
            (adaptiveMixedTypeModulus support : ℝ)) < upper
  have cancellation :
      (base : ℝ) * ((3 : ℝ) / 2) +
        (adaptiveMixedTypeModulus support : ℝ) *
          (((lower + upper) / 2 - (base : ℝ) * ((3 : ℝ) / 2)) /
            (adaptiveMixedTypeModulus support : ℝ)) =
        (lower + upper) / 2 := by
    field_simp [modulus_positive.ne']
    ring_nf
  rw [cancellation]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor <;> linarith

/-- Any open signed physical domain has an open actual two-center,
same-label lift. -/
theorem scaleAdaptiveSignedSharedLabelDomainLift_isOpen
    (domain : Set (ℝ × ℝ)) (open_domain : IsOpen domain) :
    IsOpen (scaleAdaptiveSignedSharedLabelDomainLift domain) := by
  let first : (ℝ × ℝ × ℝ) → (ℝ × ℝ) :=
    fun point => (point.1, point.2.1)
  let second : (ℝ × ℝ × ℝ) → (ℝ × ℝ) :=
    fun point => (point.1, point.2.2)
  have first_continuous : Continuous first :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have second_continuous : Continuous second :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have equal :
      scaleAdaptiveSignedSharedLabelDomainLift domain =
        first ⁻¹' domain ∩ second ⁻¹' domain := by
    rfl
  rw [equal]
  exact (open_domain.preimage first_continuous).inter
    (open_domain.preimage second_continuous)

/-- Any convex signed physical domain has a convex actual two-center,
same-label lift. -/
theorem scaleAdaptiveSignedSharedLabelDomainLift_convex
    (domain : Set (ℝ × ℝ)) (convex : Convex ℝ domain) :
    Convex ℝ (scaleAdaptiveSignedSharedLabelDomainLift domain) := by
  intro first first_selected second second_selected a b a_nonnegative
    b_nonnegative sum_one
  constructor
  · exact convex first_selected.1 second_selected.1
      a_nonnegative b_nonnegative sum_one
  · exact convex first_selected.2 second_selected.2
      a_nonnegative b_nonnegative sum_one

/-- Nonemptiness is preserved by taking two actual centers in the same
signed prime-label fiber. -/
theorem scaleAdaptiveSignedSharedLabelDomainLift_nonempty
    (domain : Set (ℝ × ℝ)) (nonempty : domain.Nonempty) :
    (scaleAdaptiveSignedSharedLabelDomainLift domain).Nonempty := by
  obtain ⟨⟨label, center⟩, selected⟩ := nonempty
  exact ⟨(label, center, center), selected, selected⟩

/-- Genuine original-strip containment automatically gives the correct
genuine two-center shared-label physical-strip containment. -/
theorem scaleAdaptiveSignedSharedLabelDomainLift_subset_physical
    (support : Finset ℕ) (base : ℕ) (domain : Set (ℝ × ℝ))
    (physical : domain ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support base) :
    scaleAdaptiveSignedSharedLabelDomainLift domain ⊆
      adaptiveMixedSignedSharedLabelPhysicalDomain support base base := by
  intro point selected
  have first := physical selected.1
  have second := physical selected.2
  exact ⟨first.1, first.2.1, first.2.2.1,
    first.2.2.2, second.2.2.1, second.2.2.2⟩

/-- EXACT squared-fiber volume of the genuine slanted constant-residue band.
Both independent SIGNED center fibers have the same true width, so their
three-dimensional physical volume is precisely the SQUARE of the actual
two-dimensional first-fiber volume. -/
theorem scaleAdaptiveSignedConstantResidueBand_shared_volume
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (ordered : lower ≤ upper) :
    (volume (scaleAdaptiveSignedSharedLabelDomainLift
      (scaleAdaptiveSignedConstantResidueBand
        support base lower upper))).toReal =
      ((upper - lower) / (adaptiveMixedTypeModulus support : ℝ)) ^ 2 := by
  classical
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have width_nonnegative :
      0 ≤ (upper - lower) / (adaptiveMixedTypeModulus support : ℝ) :=
    div_nonneg (sub_nonneg.mpr ordered) modulus_positive.le
  let band := scaleAdaptiveSignedConstantResidueBand
    support base lower upper
  have measurable :
      MeasurableSet (scaleAdaptiveSignedSharedLabelDomainLift band) :=
    (scaleAdaptiveSignedSharedLabelDomainLift_isOpen band
      (scaleAdaptiveSignedConstantResidueBand_isOpen
        support base lower upper)).measurableSet
  change (volume (scaleAdaptiveSignedSharedLabelDomainLift band)).toReal = _
  rw [MeasureTheory.Measure.volume_eq_prod ℝ (ℝ × ℝ),
    MeasureTheory.Measure.prod_apply measurable]
  have fibers :
      (fun label : ℝ =>
        (volume : Measure (ℝ × ℝ))
          (Prod.mk label ⁻¹'
            scaleAdaptiveSignedSharedLabelDomainLift band)) =
        (Set.Ioo (1 : ℝ) 2).indicator fun _ : ℝ =>
          (ENNReal.ofReal
            ((upper - lower) /
              (adaptiveMixedTypeModulus support : ℝ))) ^ 2 := by
    funext label
    by_cases in_interval : label ∈ Set.Ioo (1 : ℝ) 2
    · rw [Set.indicator_of_mem in_interval]
      let left :=
        (lower - (base : ℝ) * label) /
          (adaptiveMixedTypeModulus support : ℝ)
      let right :=
        (upper - (base : ℝ) * label) /
          (adaptiveMixedTypeModulus support : ℝ)
      have fiber_equal :
          (Prod.mk label ⁻¹'
            scaleAdaptiveSignedSharedLabelDomainLift band) =
              (Set.Ioo left right) ×ˢ (Set.Ioo left right) := by
        ext centers
        change
          ((label, centers.1) ∈ band ∧
            (label, centers.2) ∈ band) ↔
              (left < centers.1 ∧ centers.1 < right) ∧
                (left < centers.2 ∧ centers.2 < right)
        dsimp [band]
        rw [scaleAdaptiveSignedConstantResidueBand_eq_regionBetween
          support base lower upper primes]
        change
          ((label ∈ Set.Ioo (1 : ℝ) 2 ∧
              centers.1 ∈ Set.Ioo left right) ∧
            (label ∈ Set.Ioo (1 : ℝ) 2 ∧
              centers.2 ∈ Set.Ioo left right)) ↔ _
        simp [in_interval]
      rw [fiber_equal, MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
        MeasureTheory.Measure.prod_prod, Real.volume_Ioo]
      have difference :
          right - left =
            (upper - lower) /
              (adaptiveMixedTypeModulus support : ℝ) := by
        dsimp [left, right]
        ring_nf
      rw [difference]
      ring_nf
    · rw [Set.indicator_of_notMem in_interval]
      have empty :
          (Prod.mk label ⁻¹'
            scaleAdaptiveSignedSharedLabelDomainLift band) = ∅ := by
        ext centers
        constructor
        · intro selected
          have first : (label, centers.1) ∈ band := selected.1
          have interval : label ∈ Set.Ioo (1 : ℝ) 2 :=
            ⟨first.1, first.2.1⟩
          exact (in_interval interval).elim
        · intro selected
          simp at selected
      rw [empty, measure_empty]
  rw [fibers, lintegral_indicator measurableSet_Ioo,
    MeasureTheory.setLIntegral_const, Real.volume_Ioo]
  norm_num [ENNReal.toReal_pow, ENNReal.toReal_ofReal width_nonnegative]

/-- The exact actual two-center physical volume cancels the square of the
one-center physical volume, for EVERY base and every ordered residue band. -/
theorem scaleAdaptiveSignedConstantResidueBand_volume_factorization
    (support : Finset ℕ) (base : ℕ) (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (ordered : lower ≤ upper) :
    (volume (scaleAdaptiveSignedSharedLabelDomainLift
      (scaleAdaptiveSignedConstantResidueBand
        support base lower upper))).toReal =
      (volume (scaleAdaptiveSignedConstantResidueBand
        support base lower upper)).toReal ^ 2 := by
  rw [scaleAdaptiveSignedConstantResidueBand_shared_volume
    support base lower upper primes ordered,
    scaleAdaptiveSignedConstantResidueBand_volume
      support base lower upper primes ordered]

/-- ACTUAL zero centered degree variance for every rank and every outcome
base on the true signed constant-residue band.  The proof uses ONLY the
explicit fixed-system original/shared-label Green--Tao counts and the
already proved ordinary prime number theorem.  All openness, convexity,
nonemptiness, physical-strip conditions, singular normalization, and the
exact two- versus three-dimensional physical volumes are proved outright;
no degree, covariance, concentration, or geometric premise is assumed.

The band is a strict subfamily of the full physical strip.  In particular,
this theorem alone makes no original almost-prime-covering claim. -/
theorem scaleAdaptiveSignedConstantResidueBand_centeredVariance_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (strict : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          (∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            ((scaleAdaptiveSignedDegree support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label : ℝ) -
              ((upper - lower) /
                (adaptiveMixedTypeModulus support : ℝ)) *
                singular * (N : ℝ) /
                  Real.log (N : ℝ) ^
                    (adaptiveMixedOutcomeActiveIndices
                      support scale outcome).card) ^ 2) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card +
               (adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 3)
        atTop (nhds (0 : ℝ)) := by
  let band := scaleAdaptiveSignedConstantResidueBand
    support outcome.1 lower upper
  have convex := scaleAdaptiveSignedConstantResidueBand_convex
    support outcome.1 lower upper
  have open_domain := scaleAdaptiveSignedConstantResidueBand_isOpen
    support outcome.1 lower upper
  have nonempty := scaleAdaptiveSignedConstantResidueBand_nonempty
    support outcome.1 lower upper primes strict
  have physical := scaleAdaptiveSignedConstantResidueBand_subset_physical
    support outcome.1 lower upper lower_nonnegative upper_bounded
  have factorization := scaleAdaptiveSignedConstantResidueBand_volume_factorization
    support outcome.1 lower upper primes strict.le
  obtain ⟨singular, positive, variance⟩ :=
    scaleAdaptiveSignedDegree_normalizedCenteredVariance_tendsto_zero_of_GTZ
      green_tao support scale outcome band primes convex open_domain
      nonempty physical
      (scaleAdaptiveSignedSharedLabelDomainLift_convex band convex)
      (scaleAdaptiveSignedSharedLabelDomainLift_isOpen band open_domain)
      (scaleAdaptiveSignedSharedLabelDomainLift_nonempty band nonempty)
      (scaleAdaptiveSignedSharedLabelDomainLift_subset_physical
        support outcome.1 band physical)
      factorization
  refine ⟨singular, positive, ?_⟩
  convert variance using 1
  ext N
  rw [scaleAdaptiveSignedConstantResidueBand_volume
    support outcome.1 lower upper primes strict.le]

/-- The natural expected degree on a genuine constant-residue signed band:
actual physical center width times its true positive singular density. -/
noncomputable def scaleAdaptiveSignedConstantResidueBandExpectedDegree
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper singular : ℝ) (N : ℕ) : ℝ :=
  ((upper - lower) /
    (adaptiveMixedTypeModulus support : ℝ)) * singular * (N : ℝ) /
      Real.log (N : ℝ) ^
        (adaptiveMixedOutcomeActiveIndices support scale outcome).card

/-- The precise prime-density-normalized mean-square RELATIVE degree error
on the actual signed constant-residue band tends to zero.  This is the
normalization consumed by the genuine weighted Cauchy--Schwarz transfer,
and it is derived rather than assumed. -/
theorem scaleAdaptiveSignedConstantResidueBand_relativeVariance_tendsto_zero_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (lower upper : ℝ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (strict : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          (∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            ((scaleAdaptiveSignedDegree support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label : ℝ) /
                scaleAdaptiveSignedConstantResidueBandExpectedDegree
                  support scale outcome lower upper singular N - 1) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds (0 : ℝ)) := by
  obtain ⟨singular, positive, centered⟩ :=
    scaleAdaptiveSignedConstantResidueBand_centeredVariance_tendsto_zero_of_GTZ
      green_tao support scale outcome lower upper primes
      lower_nonnegative strict upper_bounded
  refine ⟨singular, positive, ?_⟩
  have modulus_positive : (0 : ℝ) < adaptiveMixedTypeModulus support := by
    exact_mod_cast adaptiveMixedTypeModulus_pos support primes
  have width_positive :
      0 < (upper - lower) / (adaptiveMixedTypeModulus support : ℝ) :=
    div_pos (sub_pos.mpr strict) modulus_positive
  have coefficient_nonzero :
      ((upper - lower) /
        (adaptiveMixedTypeModulus support : ℝ)) * singular ≠ 0 :=
    mul_ne_zero width_positive.ne' positive.ne'
  have divided := centered.div_const
    ((((upper - lower) /
      (adaptiveMixedTypeModulus support : ℝ)) * singular) ^ 2)
  have target :
      Tendsto
        (fun N : ℕ =>
          ((∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            ((scaleAdaptiveSignedDegree support scale outcome
                (scaleAdaptiveSignedConstantResidueBand
                  support outcome.1 lower upper) N label : ℝ) -
              ((upper - lower) /
                (adaptiveMixedTypeModulus support : ℝ)) *
                singular * (N : ℝ) /
                  Real.log (N : ℝ) ^
                    (adaptiveMixedOutcomeActiveIndices
                      support scale outcome).card) ^ 2) *
            Real.log (N : ℝ) ^
              ((adaptiveMixedOutcomeActiveIndices
                support scale outcome).card +
               (adaptiveMixedOutcomeActiveIndices
                support scale outcome).card + 1) /
            (N : ℝ) ^ 3) /
            ((((upper - lower) /
              (adaptiveMixedTypeModulus support : ℝ)) * singular) ^ 2))
        atTop (nhds (0 : ℝ)) := by
    simpa using divided
  apply target.congr'
  filter_upwards [eventually_ge_atTop 2] with N large
  have N_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have log_nonzero : Real.log (N : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (by omega : 0 < N)
    · exact_mod_cast (by omega : N ≠ 1)
  let coefficient : ℝ :=
    ((upper - lower) /
      (adaptiveMixedTypeModulus support : ℝ)) * singular
  let rank := (adaptiveMixedOutcomeActiveIndices
    support scale outcome).card
  have coefficient_nonzero' : coefficient ≠ 0 := coefficient_nonzero
  have term : ∀ degree : ℝ,
      ((degree / (coefficient * (N : ℝ) /
          Real.log (N : ℝ) ^ rank) - 1) ^ 2) *
          Real.log (N : ℝ) / (N : ℝ) =
        (((degree - coefficient * (N : ℝ) /
            Real.log (N : ℝ) ^ rank) ^ 2) *
          Real.log (N : ℝ) ^ (rank + rank + 1) /
          (N : ℝ) ^ 3) / coefficient ^ 2 := by
    intro degree
    field_simp [N_nonzero, log_nonzero, coefficient_nonzero']
    ring_nf
  change
    ((∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
      ((scaleAdaptiveSignedDegree support scale outcome
          (scaleAdaptiveSignedConstantResidueBand
            support outcome.1 lower upper) N label : ℝ) -
        coefficient * (N : ℝ) / Real.log (N : ℝ) ^ rank) ^ 2) *
        Real.log (N : ℝ) ^ (rank + rank + 1) / (N : ℝ) ^ 3) /
          coefficient ^ 2 =
      (∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
        ((scaleAdaptiveSignedDegree support scale outcome
            (scaleAdaptiveSignedConstantResidueBand
              support outcome.1 lower upper) N label : ℝ) /
          (coefficient * (N : ℝ) / Real.log (N : ℝ) ^ rank) - 1) ^ 2) *
        Real.log (N : ℝ) / (N : ℝ)
  calc
    _ = ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
          (((scaleAdaptiveSignedDegree support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N label : ℝ) -
            coefficient * (N : ℝ) /
              Real.log (N : ℝ) ^ rank) ^ 2) *
            Real.log (N : ℝ) ^ (rank + rank + 1) /
              (N : ℝ) ^ 3 / coefficient ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div]
    _ = ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
          (((scaleAdaptiveSignedDegree support scale outcome
              (scaleAdaptiveSignedConstantResidueBand
                support outcome.1 lower upper) N label : ℝ) /
              (coefficient * (N : ℝ) /
                Real.log (N : ℝ) ^ rank) - 1) ^ 2) *
            Real.log (N : ℝ) / (N : ℝ) := by
      apply Finset.sum_congr rfl
      intro label _
      exact (term _).symm
    _ = _ := by
      rw [← Finset.sum_div, ← Finset.sum_mul]


end Erdos1139
