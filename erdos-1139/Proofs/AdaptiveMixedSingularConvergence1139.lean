module

public import ScaleAdaptiveGTZConditionalOriginal1139
public import AdaptiveSharedTargetDiagonalNegligible1139
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section


/-!
# Unconditional convergence of the genuine mixed singular series

The explicit Green--Tao--Ziegler input previously bundled convergence of its
individual collision-aware singular products with the deep prime-pattern
counting asymptotics.  The convergence is elementary: once all supported and
small primes have been passed, every actual local factor is at most one, while
the already proved all-prime positive product floor bounds the monotone tail
away from zero.

This file separates that unconditional Euler-product ingredient from the
still-unformalized simultaneous-prime counting theorem.  It asserts no
unconditional resolution of Erdős #1139.
-/

open Filter Finset MeasureTheory Set
open scoped ArithmeticFunction.Omega BigOperators Topology

namespace Erdos1139

/-- Above its rank, the genuine arbitrary-rank pure local factor is at most
one.  The first-order cancellation is Bernoulli's inequality, not an
assumed Euler-product convergence theorem. -/
theorem primeRankNormalizedLocalFactor_large_le_one
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_large : 2 ≤ rank) (large : rank < ell) :
    primeRankNormalizedLocalFactor rank ell ≤ 1 := by
  have prime : ell.Prime := Fact.out
  have ell_positive : (0 : ℝ) < ell := by exact_mod_cast prime.pos
  have ell_large : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
  have denominator_positive : (0 : ℝ) < (ell : ℝ) - 1 := by linarith
  have inverse_le_one : (1 : ℝ) / ell ≤ 1 := by
    apply (div_le_iff₀ ell_positive).mpr
    linarith
  have rank_cast : (((rank - 1 : ℕ) : ℝ)) = (rank : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ rank)]
    norm_num
  have bernoulli :
      1 - (((rank - 1 : ℕ) : ℝ)) / (ell : ℝ) ≤
        (1 - 1 / (ell : ℝ)) ^ (rank - 1) := by
    have admissible : (-2 : ℝ) ≤ -(1 / (ell : ℝ)) := by linarith
    simpa [div_eq_mul_inv, sub_eq_add_neg, mul_neg] using
      one_add_mul_le_pow admissible (rank - 1)
  have first_le_linear :
      (((ell : ℝ) - rank) / ((ell : ℝ) - 1)) ≤
        1 - (((rank - 1 : ℕ) : ℝ)) / (ell : ℝ) := by
    apply (div_le_iff₀ denominator_positive).mpr
    have identity :
        (1 - (((rank - 1 : ℕ) : ℝ)) / (ell : ℝ)) *
            ((ell : ℝ) - 1) - ((ell : ℝ) - rank) =
          (((rank - 1 : ℕ) : ℝ)) / (ell : ℝ) := by
      rw [rank_cast]
      field_simp
      ring
    have nonnegative :
        0 ≤ (((rank - 1 : ℕ) : ℝ)) / (ell : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) ell_positive.le
    linarith
  have cancellation :
      (1 - 1 / (ell : ℝ)) *
        ((ell : ℝ) / ((ell : ℝ) - 1)) = 1 := by
    field_simp
  rw [primeRankNormalizedLocalFactor_large rank_large large]
  calc
    (((ell : ℝ) - rank) / ((ell : ℝ) - 1)) *
        ((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank - 1) ≤
      (1 - 1 / (ell : ℝ)) ^ (rank - 1) *
        ((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank - 1) := by
      exact mul_le_mul_of_nonneg_right
        (first_le_linear.trans bernoulli) (by positivity)
    _ = ((1 - 1 / (ell : ℝ)) *
      ((ell : ℝ) / ((ell : ℝ) - 1))) ^ (rank - 1) := by
        rw [mul_pow]
    _ = 1 := by rw [cancellation, one_pow]

/-- Once an unsupported prime is above the physical scale, the TRUE mixed
local factor is at most one at EVERY rank, including ranks zero and one. -/
theorem adaptiveMixedActualScalarLocalFactor_large_le_one
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (prime : ell.Prime) (outside : ell ∉ support) (large : scale < ell) :
    adaptiveMixedActualScalarLocalFactor support scale ell outcome ≤ 1 := by
  simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
  by_cases rank_large :
      2 ≤ (adaptiveMixedOutcomeActiveIndices support scale outcome).card
  · rw [@adaptiveMixedActualNormalizedLocalFactor_large_eq_pure
      support scale ell outcome ⟨prime⟩ primes outside large rank_large]
    apply @primeRankNormalizedLocalFactor_large_le_one
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card
        ell ⟨prime⟩ rank_large
    have bounded := adaptiveMixedOutcomeActiveIndices_card_le_scale
      support scale outcome
    omega
  · have small_rank :
        (adaptiveMixedOutcomeActiveIndices support scale outcome).card ≤ 1 := by
      omega
    rw [@adaptiveMixedActualNormalizedLocalFactor_outside_eq_one_of_rank_le_one
      support scale ell outcome ⟨prime⟩ primes outside small_rank]

/-- An explicit fixed cutoff contains both the physical scale and EVERY
supported prime; after this cutoff no exceptional local factor can recur. -/
def adaptiveMixedSignedSingularMonotoneCutoff
    (support : Finset ℕ) (scale : ℕ) : ℕ :=
  max scale (support.sup id)

/-- The genuine collision-aware partial Euler products are eventually
ANTITONE.  No Green--Tao theorem or asymptotic prime-pattern input is used. -/
theorem adaptiveMixedSignedSingularPartialProduct_antitoneOn
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    AntitoneOn (adaptiveMixedSignedSingularPartialProduct support scale outcome)
      (Ici (adaptiveMixedSignedSingularMonotoneCutoff support scale)) := by
  intro lower lower_large upper _upper_large ordered
  unfold adaptiveMixedSignedSingularPartialProduct
  apply Finset.prod_le_prod_of_subset_of_le_one₀
  · intro ell selected
    obtain ⟨bounded, prime⟩ := Nat.mem_primesLE.mp selected
    exact Nat.mem_primesLE.mpr ⟨bounded.trans ordered, prime⟩
  · intro ell selected
    have prime := Nat.prime_of_mem_primesLE selected
    simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
    exact (@adaptiveMixedActualNormalizedLocalFactor_pos
      support scale ell outcome ⟨prime⟩ primes).le
  · intro ell selected missing
    obtain ⟨_bounded, prime⟩ := Nat.mem_primesLE.mp selected
    have lower_lt : lower < ell := by
      by_contra not_large
      exact missing (Nat.mem_primesLE.mpr
        ⟨Nat.le_of_not_gt not_large, prime⟩)
    have scale_lt : scale < ell := by
      have cutoff_le := lower_large
      change adaptiveMixedSignedSingularMonotoneCutoff support scale ≤ lower
        at cutoff_le
      unfold adaptiveMixedSignedSingularMonotoneCutoff at cutoff_le
      omega
    have outside : ell ∉ support := by
      intro supported
      have support_bound : ell ≤ support.sup id := by
        simpa using (Finset.le_sup (f := id) supported)
      have cutoff_le := lower_large
      change adaptiveMixedSignedSingularMonotoneCutoff support scale ≤ lower
        at cutoff_le
      unfold adaptiveMixedSignedSingularMonotoneCutoff at cutoff_le
      omega
    exact adaptiveMixedActualScalarLocalFactor_large_le_one
      primes prime outside scale_lt

/-- Canonical genuine singular value: the infimum of the actual antitone
tail after every exceptional supported and small prime has entered. -/
noncomputable def adaptiveMixedSignedCanonicalSingular
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ) : ℝ :=
  sInf ((adaptiveMixedSignedSingularPartialProduct support scale outcome) ''
    Ici (adaptiveMixedSignedSingularMonotoneCutoff support scale))

/-- EVERY actual collision-aware mixed Euler product converges
UNCONDITIONALLY to its canonical real singular value.  This eliminates an
entire previously bundled part of the explicit Green--Tao input. -/
theorem adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    Tendsto (adaptiveMixedSignedSingularPartialProduct support scale outcome)
      atTop (nhds (adaptiveMixedSignedCanonicalSingular support scale outcome)) := by
  obtain ⟨constant, _positive, lower⟩ :=
    adaptiveMixedActualNormalizedLocalFactor_uniform_positive_all_ranks
      support scale outcome primes
  have bounded : BddBelow
      ((adaptiveMixedSignedSingularPartialProduct support scale outcome) ''
        Ici (adaptiveMixedSignedSingularMonotoneCutoff support scale)) := by
    refine ⟨constant, ?_⟩
    rintro value ⟨cutoff, _large, rfl⟩
    exact lower (Nat.primesLE cutoff)
      (fun ell selected => Nat.prime_of_mem_primesLE selected)
  exact Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (adaptiveMixedSignedSingularPartialProduct_antitoneOn
      support scale outcome primes) bounded

/-- The unconditional canonical singular value is STRICTLY POSITIVE at
every fixed actual rank, outcome, support, and scale. -/
theorem adaptiveMixedSignedCanonicalSingular_pos
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    0 < adaptiveMixedSignedCanonicalSingular support scale outcome := by
  obtain ⟨constant, positive, lower⟩ :=
    adaptiveMixedActualNormalizedLocalFactor_uniform_positive_all_ranks
      support scale outcome primes
  have eventually_lower : ∀ᶠ cutoff : ℕ in atTop,
      constant ≤ adaptiveMixedSignedSingularPartialProduct
        support scale outcome cutoff := by
    exact Eventually.of_forall fun cutoff =>
      lower (Nat.primesLE cutoff)
        (fun ell selected => Nat.prime_of_mem_primesLE selected)
  exact positive.trans_le (ge_of_tendsto
    (adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
      support scale outcome primes) eventually_lower)

/-- The strictly reduced remaining deep analytic input contains ONLY actual
fixed-system simultaneous-prime COUNTING asymptotics.  Every singular constant
is the unconditional, strictly positive, canonically convergent Euler product
proved above; no convergence or local-positivity clause is assumed.  The
shared-target count uses the genuine FULL integral lattice of the published
theorem; deletion of the equal-label diagonal is proved separately. -/
structure HasFixedSignedMixedPrimeCountingAsymptotics : Prop where
  original :
    ∀ (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
      (domain : Set (ℝ × ℝ)),
      (∀ prime ∈ support, prime.Prime) →
      Convex ℝ domain → IsOpen domain → domain.Nonempty →
      domain ⊆ adaptiveMixedSignedOriginalPhysicalDomain
        support outcome.1 →
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedOriginalPrimeRealizations
            support scale outcome domain N).card : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card + 1) /
                (N : ℝ) ^ 2)
        atTop (nhds
          ((volume domain).toReal *
            adaptiveMixedSignedCanonicalSingular support scale outcome))
  shared_label :
    ∀ (support : Finset ℕ) (scale : ℕ)
      (first second : ℕ × ℕ) (domain : Set (ℝ × ℝ × ℝ)),
      (∀ prime ∈ support, prime.Prime) →
      Convex ℝ domain → IsOpen domain → domain.Nonempty →
      domain ⊆ adaptiveMixedSignedSharedLabelPhysicalDomain
        support first.1 second.1 →
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedSharedLabelPrimeRealizations
            support scale first second domain N).card : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale first).card +
                 (adaptiveMixedOutcomeActiveIndices
                  support scale second).card + 1) /
                (N : ℝ) ^ 3)
        atTop (nhds
          ((volume domain).toReal *
            adaptiveMixedSignedCanonicalSingular support scale first *
            adaptiveMixedSignedCanonicalSingular support scale second))
  shared_target :
    ∀ (support : Finset ℕ) (scale firstIndex secondIndex : ℕ)
      (first second : ℕ × ℕ)
      (targetLower targetUpper firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper : ℝ)
      (domain : Set (ℝ × ℝ × ℝ)),
      (∀ prime ∈ support, prime.Prime) →
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first →
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second →
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex →
      Convex ℝ domain → IsOpen domain → domain.Nonempty →
      domain ⊆ adaptiveMixedSharedTargetPhysicalConvexWindow
        firstIndex secondIndex targetLower targetUpper
          firstLabelLower firstLabelUpper
          secondLabelLower secondLabelUpper →
      (∀ point ∈ domain,
        (1 : ℝ) < point.2.1 ∧ point.2.1 < 2 ∧
          (1 : ℝ) < point.2.2 ∧ point.2.2 < 2) →
      Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedSharedTargetUnrestrictedPrimeRealizations
            support scale first second firstIndex secondIndex domain N).card : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale first).card +
                 (adaptiveMixedOutcomeActiveIndices
                  support scale second).card + 1) /
                (N : ℝ) ^ 3)
        atTop (nhds
          ((volume domain).toReal *
            (adaptiveMixedActualIndexType
              support first.1 firstIndex : ℝ) /
            (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
            adaptiveMixedSignedCanonicalSingular support scale first *
            adaptiveMixedSignedCanonicalSingular support scale second))

/-- The earlier bundled Green--Tao input follows from the genuinely smaller
COUNTING-ONLY premise because every singular-product convergence assertion is
now a proved unconditional theorem. -/
theorem fixed_signed_GTZ_of_prime_counting_asymptotics
    (counts : HasFixedSignedMixedPrimeCountingAsymptotics) :
    HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics := by
  refine ⟨?_, ?_, ?_⟩
  · intro support scale outcome domain primes convex is_open nonempty contained
    exact ⟨adaptiveMixedSignedCanonicalSingular support scale outcome,
      adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale outcome primes,
      counts.original support scale outcome domain
        primes convex is_open nonempty contained⟩
  · intro support scale first second domain primes convex is_open nonempty contained
    exact ⟨adaptiveMixedSignedCanonicalSingular support scale first,
      adaptiveMixedSignedCanonicalSingular support scale second,
      adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale first primes,
      adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale second primes,
      counts.shared_label support scale first second domain
        primes convex is_open nonempty contained⟩
  · intro support scale firstIndex secondIndex first second
      targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper domain primes first_active
      second_active same_type convex is_open nonempty contained labels
    refine ⟨adaptiveMixedSignedCanonicalSingular support scale first,
      adaptiveMixedSignedCanonicalSingular support scale second,
      adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale first primes,
      adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale second primes, ?_⟩
    apply (adaptiveMixedSignedSharedTargetUnrestricted_asymptotic_iff_distinct
      support scale first second firstIndex secondIndex domain
      ((adaptiveMixedOutcomeActiveIndices support scale first).card +
       (adaptiveMixedOutcomeActiveIndices support scale second).card + 1)
      ((volume domain).toReal *
        (adaptiveMixedActualIndexType support first.1 firstIndex : ℝ) /
          (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
        adaptiveMixedSignedCanonicalSingular support scale first *
        adaptiveMixedSignedCanonicalSingular support scale second)
      primes).mp
    exact counts.shared_target support scale firstIndex secondIndex first second
      targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper domain primes first_active
      second_active same_type convex is_open nonempty contained labels

/-- Conversely, uniqueness of the now-unconditionally convergent singular
product extracts the three pure counting conclusions from the old bundle. -/
theorem fixed_signed_prime_counting_asymptotics_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics) :
    HasFixedSignedMixedPrimeCountingAsymptotics := by
  refine ⟨?_, ?_, ?_⟩
  · intro support scale outcome domain primes convex is_open nonempty contained
    obtain ⟨singular, convergence, count⟩ :=
      green_tao.original support scale outcome domain
        primes convex is_open nonempty contained
    have identified := tendsto_nhds_unique convergence
      (adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale outcome primes)
    simpa [identified] using count
  · intro support scale first second domain primes convex is_open nonempty contained
    obtain ⟨firstSingular, secondSingular, first_convergence,
      second_convergence, count⟩ :=
        green_tao.shared_label support scale first second domain
          primes convex is_open nonempty contained
    have first_identified := tendsto_nhds_unique first_convergence
      (adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale first primes)
    have second_identified := tendsto_nhds_unique second_convergence
      (adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale second primes)
    simpa [first_identified, second_identified] using count
  · intro support scale firstIndex secondIndex first second
      targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper domain primes first_active
      second_active same_type convex is_open nonempty contained labels
    obtain ⟨firstSingular, secondSingular, first_convergence,
      second_convergence, count⟩ :=
        green_tao.shared_target support scale firstIndex secondIndex first second
          targetLower targetUpper firstLabelLower firstLabelUpper
          secondLabelLower secondLabelUpper domain primes first_active
          second_active same_type convex is_open nonempty contained labels
    have first_identified := tendsto_nhds_unique first_convergence
      (adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale first primes)
    have second_identified := tendsto_nhds_unique second_convergence
      (adaptiveMixedSignedSingularPartialProduct_tendsto_canonical
        support scale second primes)
    apply (adaptiveMixedSignedSharedTargetUnrestricted_asymptotic_iff_distinct
      support scale first second firstIndex secondIndex domain
      ((adaptiveMixedOutcomeActiveIndices support scale first).card +
       (adaptiveMixedOutcomeActiveIndices support scale second).card + 1)
      ((volume domain).toReal *
        (adaptiveMixedActualIndexType support first.1 firstIndex : ℝ) /
          (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
        adaptiveMixedSignedCanonicalSingular support scale first *
        adaptiveMixedSignedCanonicalSingular support scale second)
      primes).mpr
    simpa [first_identified, second_identified] using count

/-- Exact equivalence: the ONLY content left in the earlier Green--Tao bundle
is its three genuine simultaneous-prime counting asymptotics. -/
theorem fixed_signed_GTZ_iff_prime_counting_asymptotics :
    HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics ↔
      HasFixedSignedMixedPrimeCountingAsymptotics :=
  ⟨fixed_signed_prime_counting_asymptotics_of_GTZ,
    fixed_signed_GTZ_of_prime_counting_asymptotics⟩

/-- The EXACT original Erdős #1139 infinite limsup now follows from ONLY the
three fixed-system genuine simultaneous-prime COUNTING asymptotics.  Every
singular-product convergence and positivity ingredient is kernel-proved
unconditionally; the prime-counting premise itself remains unformalized. -/
theorem original_normalized_limsup_top_of_fixed_signed_prime_counts
    (counts : HasFixedSignedMixedPrimeCountingAsymptotics) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_fixed_signed_GTZ
    (fixed_signed_GTZ_of_prime_counting_asymptotics counts)

end Erdos1139

