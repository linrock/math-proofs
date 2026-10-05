module

public import AdaptiveMixedActualPublishedWeightedBridge1139
public import AdaptiveMixedSingularConvergence1139

@[expose] public section


/-!
# Exact published finite-complexity prime-pattern interface for Erdős #1139

The sole external analytic theorem is expressed in its actual published
von-Mangoldt-weighted form: sums are over the ENTIRE primality-free signed
physical lattices, not over preselected prime points.  All genuine affine
forms, all labels, true fixed ranks, signed convex domains, canonical
collision-aware Euler factors, and the actual shared-target Jacobian are
retained.

The published theorem itself is NOT proved here.  This module proves that
its exact three source-faithful fixed-system specializations are logically
equivalent to the previously isolated three simultaneous-prime counting
asymptotics, and derives the exact original Erdős #1139 infinite-limsup
statement from this ONE explicit external mathematical premise.
-/

open Filter Finset MeasureTheory
open scoped ArithmeticFunction.Omega BigOperators Topology ENNReal

namespace Erdos1139

/-- The ONE remaining analytic input, in the genuine published form:
unrestricted von Mangoldt products over the ACTUAL primality-free original,
shared-label, and FULL shared-target integral lattices.  The rank is
arbitrary but fixed BEFORE the physical scale tends to infinity.  Every
Euler factor converges and is strictly positive UNCONDITIONALLY; no singular
convergence or positivity assumption occurs in this proposition. -/
structure HasFixedSignedMixedPublishedVonMangoldtAsymptotics : Prop where
  original :
    ∀ (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
      (domain : Set (ℝ × ℝ)),
      (∀ prime ∈ support, prime.Prime) →
      Convex ℝ domain → IsOpen domain → domain.Nonempty →
      domain ⊆ adaptiveMixedSignedOriginalPhysicalDomain
        support outcome.1 →
      Tendsto
        (fun N : ℕ =>
          (∑ point ∈ adaptiveMixedSignedOriginalPublishedLattice
            support scale outcome domain N,
              adaptiveMixedVonMangoldtProduct
                (adaptiveMixedActualFormIndices support scale outcome)
                (adaptiveMixedActualSignedPrimeFormValue
                  support outcome.1) point) / (N : ℝ) ^ 2)
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
          (∑ point ∈ adaptiveMixedSignedSharedLabelPublishedLattice
            support scale first second domain N,
              adaptiveMixedVonMangoldtProduct
                (adaptiveMixedSharedLabelFormIndices
                  support scale first second)
                (adaptiveMixedSharedLabelSignedPrimeFormValue
                  support first.1 second.1) point) / (N : ℝ) ^ 3)
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
          (∑ point ∈ adaptiveMixedSignedSharedTargetPublishedLattice
            support scale first second firstIndex secondIndex domain N,
              adaptiveMixedVonMangoldtProduct
                (adaptiveMixedSharedTargetFormIndices
                  support scale first second secondIndex)
                (adaptiveMixedSharedTargetSignedPrimeFormValue
                  support first.1 second.1) point) / (N : ℝ) ^ 3)
        atTop (nhds
          ((volume domain).toReal *
            (adaptiveMixedActualIndexType
              support first.1 firstIndex : ℝ) /
            (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
            adaptiveMixedSignedCanonicalSingular support scale first *
            adaptiveMixedSignedCanonicalSingular support scale second))

/-- The exact three published unrestricted von Mangoldt asymptotics imply
the three literal source-faithful fixed-system simultaneous-prime counts.
All proper prime powers, all true affine fibers, logarithmic weights, the
signed geometry, and the globally equal-label diagonal are handled by
separately kernel-proved theorems. -/
theorem fixed_signed_prime_counting_asymptotics_of_published_von_mangoldt
    (published : HasFixedSignedMixedPublishedVonMangoldtAsymptotics) :
    HasFixedSignedMixedPrimeCountingAsymptotics := by
  refine ⟨?_, ?_, ?_⟩
  · intro support scale outcome domain primes convex is_open nonempty contained
    apply (adaptiveMixedSignedOriginalPublishedVonMangoldt_asymptotic_iff
      support scale outcome domain
      ((volume domain).toReal *
        adaptiveMixedSignedCanonicalSingular support scale outcome)
      primes).mp
    exact published.original support scale outcome domain
      primes convex is_open nonempty contained
  · intro support scale first second domain primes convex is_open nonempty contained
    apply (adaptiveMixedSignedSharedLabelPublishedVonMangoldt_asymptotic_iff
      support scale first second domain
      ((volume domain).toReal *
        adaptiveMixedSignedCanonicalSingular support scale first *
        adaptiveMixedSignedCanonicalSingular support scale second)
      primes).mp
    exact published.shared_label support scale first second domain
      primes convex is_open nonempty contained
  · intro support scale firstIndex secondIndex first second
      targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper domain primes first_active
      second_active same_type convex is_open nonempty contained labels
    apply (adaptiveMixedSignedSharedTargetPublishedVonMangoldt_asymptotic_iff
      support scale first second firstIndex secondIndex domain
      ((volume domain).toReal *
        (adaptiveMixedActualIndexType support first.1 firstIndex : ℝ) /
          (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
        adaptiveMixedSignedCanonicalSingular support scale first *
        adaptiveMixedSignedCanonicalSingular support scale second)
      primes first_active second_active same_type).mp
    exact published.shared_target support scale firstIndex secondIndex
      first second targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper domain primes first_active
      second_active same_type convex is_open nonempty contained labels

/-- Conversely, the three exact prime counts imply the corresponding
published unrestricted weighted asymptotics: the prime-power removal and
true logarithmic normalization are genuine equivalences, not merely upper
or lower bounds. -/
theorem fixed_signed_published_von_mangoldt_asymptotics_of_prime_counts
    (counts : HasFixedSignedMixedPrimeCountingAsymptotics) :
    HasFixedSignedMixedPublishedVonMangoldtAsymptotics := by
  refine ⟨?_, ?_, ?_⟩
  · intro support scale outcome domain primes convex is_open nonempty contained
    apply (adaptiveMixedSignedOriginalPublishedVonMangoldt_asymptotic_iff
      support scale outcome domain
      ((volume domain).toReal *
        adaptiveMixedSignedCanonicalSingular support scale outcome)
      primes).mpr
    exact counts.original support scale outcome domain
      primes convex is_open nonempty contained
  · intro support scale first second domain primes convex is_open nonempty contained
    apply (adaptiveMixedSignedSharedLabelPublishedVonMangoldt_asymptotic_iff
      support scale first second domain
      ((volume domain).toReal *
        adaptiveMixedSignedCanonicalSingular support scale first *
        adaptiveMixedSignedCanonicalSingular support scale second)
      primes).mpr
    exact counts.shared_label support scale first second domain
      primes convex is_open nonempty contained
  · intro support scale firstIndex secondIndex first second
      targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper domain primes first_active
      second_active same_type convex is_open nonempty contained labels
    apply (adaptiveMixedSignedSharedTargetPublishedVonMangoldt_asymptotic_iff
      support scale first second firstIndex secondIndex domain
      ((volume domain).toReal *
        (adaptiveMixedActualIndexType support first.1 firstIndex : ℝ) /
          (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
        adaptiveMixedSignedCanonicalSingular support scale first *
        adaptiveMixedSignedCanonicalSingular support scale second)
      primes first_active second_active same_type).mpr
    exact counts.shared_target support scale firstIndex secondIndex
      first second targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper domain primes first_active
      second_active same_type convex is_open nonempty contained labels

/-- The ONE explicit published fixed-system weighted prime-pattern input is
EXACTLY equivalent to the prior genuine three-count analytic proposition.
It is not assumed as an axiom and is not claimed to be proved in Mathlib. -/
theorem fixed_signed_published_von_mangoldt_iff_prime_counts :
    HasFixedSignedMixedPublishedVonMangoldtAsymptotics ↔
      HasFixedSignedMixedPrimeCountingAsymptotics :=
  ⟨fixed_signed_prime_counting_asymptotics_of_published_von_mangoldt,
    fixed_signed_published_von_mangoldt_asymptotics_of_prime_counts⟩

/-- COMPLETE exact original Erdős #1139 conclusion from ONLY the
source-faithful published unrestricted finite-complexity von Mangoldt
linear-forms theorem.  The external theorem remains an explicit proposition
parameter; no custom axiom, prime-count premise, matching hypothesis,
covering premise, singular-convergence clause, or degree bound is hidden. -/
theorem original_normalized_limsup_top_of_published_von_mangoldt
    (published : HasFixedSignedMixedPublishedVonMangoldtAsymptotics) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_fixed_signed_prime_counts
    (fixed_signed_prime_counting_asymptotics_of_published_von_mangoldt
      published)

end Erdos1139

