module

public import TypedCoreRankBarrier1139
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section


/-!
# Exact prime-plus-semiprime incidence barrier for Erdős problem #1139

The fixed zero-residue core leaves every small prime with one missing hit,
every large prime with two missing hits, and every genuinely typed
semiprime `s * q`, with `s < z < q` and `q > y / z`, with one missing hit.
The semiprime families for different `s` are genuinely disjoint.  Their exact
cardinality is

`∑ s ∈ primesLE (z - 1), (π (y / s) - π (y / z))`.

This strengthens the previously verified prime-only incidence coefficient.
It does not assert existence of the required sparse matching.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Large prime partners of one fixed small prime type. -/
def fixedCoreTypedSemiprimePartners (y z s : ℕ) : Finset ℕ :=
  (Nat.primesLE (y / s)).filter fun q => y / z < q

/-- The disjoint dependent sum of the genuinely different small prime types
and their admissible large prime partners. -/
def fixedCoreTypedSemiprimePairs (y z : ℕ) : Finset (Σ _s : ℕ, ℕ) :=
  (Nat.primesLE (z - 1)).sigma fun s =>
    fixedCoreTypedSemiprimePartners y z s

/-- Actual integer targets represented by the genuine typed prime pairs. -/
def fixedCoreTypedSemiprimeTargets (y z : ℕ) : Finset ℕ :=
  (fixedCoreTypedSemiprimePairs y z).image fun pair => pair.1 * pair.2

/-- Membership preserves the actual strict small-type cutoff, strict large
prime cutoff, both primalities, and the original closed interval endpoint. -/
theorem mem_fixedCoreTypedSemiprimePairs
    {y z : ℕ} {pair : Σ _s : ℕ, ℕ} (z_positive : 0 < z) :
    pair ∈ fixedCoreTypedSemiprimePairs y z ↔
      pair.1.Prime ∧ pair.1 < z ∧ pair.2.Prime ∧
        y / z < pair.2 ∧ pair.1 * pair.2 ≤ y := by
  unfold fixedCoreTypedSemiprimePairs fixedCoreTypedSemiprimePartners
  simp only [Finset.mem_sigma, Nat.mem_primesLE, Finset.mem_filter]
  constructor
  · rintro ⟨⟨small_bound, small_prime⟩,
      ⟨⟨partner_bound, partner_prime⟩, large⟩⟩
    refine ⟨small_prime, by omega, partner_prime, large, ?_⟩
    have product := (Nat.le_div_iff_mul_le small_prime.pos).mp partner_bound
    simpa [Nat.mul_comm] using product
  · rintro ⟨small_prime, small, partner_prime, large, product⟩
    refine ⟨⟨by omega, small_prime⟩, ⟨⟨?_, partner_prime⟩, large⟩⟩
    apply (Nat.le_div_iff_mul_le small_prime.pos).mpr
    simpa [Nat.mul_comm] using product

/-- Each fixed type has exactly the difference of the two genuine closed
prime-counting functions, with all integer divisions retained. -/
theorem fixedCoreTypedSemiprimePartners_card
    {y z s : ℕ} (s_prime : s.Prime) (s_le_z : s ≤ z) :
    (fixedCoreTypedSemiprimePartners y z s).card =
      Nat.primeCounting (y / s) - Nat.primeCounting (y / z) := by
  have cutoff_le : y / z ≤ y / s := by
    apply (Nat.le_div_iff_mul_le s_prime.pos).mpr
    calc
      (y / z) * s ≤ (y / z) * z := Nat.mul_le_mul_left _ s_le_z
      _ ≤ y := Nat.div_mul_le_self y z
  have exact_difference : fixedCoreTypedSemiprimePartners y z s =
      Nat.primesLE (y / s) \ Nat.primesLE (y / z) := by
    ext q
    simp only [fixedCoreTypedSemiprimePartners, Finset.mem_filter,
      Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨bounded, prime⟩, large⟩
      exact ⟨⟨bounded, prime⟩, fun small =>
        (Nat.not_le_of_gt large) small.1⟩
    · rintro ⟨⟨bounded, prime⟩, not_small⟩
      refine ⟨⟨bounded, prime⟩, ?_⟩
      apply Nat.lt_of_not_ge
      intro small
      exact not_small ⟨small, prime⟩
  rw [exact_difference, Finset.card_sdiff_of_subset
    (Nat.primesLE_mono cutoff_le)]
  simp only [Nat.primesLE_card_eq_primeCounting]

/-- Ordered small/large prime pairs represent distinct actual semiprime
targets; in particular no different small prime type is counted twice. -/
theorem fixedCoreTypedSemiprimePairs_multiplication_injOn
    {y z : ℕ} (z_positive : 0 < z)
    (square_threshold : z ≤ y / z) :
    Set.InjOn (fun pair : (Σ _s : ℕ, ℕ) => pair.1 * pair.2)
      (fixedCoreTypedSemiprimePairs y z : Set (Σ _s : ℕ, ℕ)) := by
  intro first first_mem second second_mem same_product
  obtain ⟨first_prime, first_small, first_partner_prime,
    first_large, _⟩ :=
      (mem_fixedCoreTypedSemiprimePairs z_positive).mp first_mem
  obtain ⟨second_prime, second_small, second_partner_prime,
    second_large, _⟩ :=
      (mem_fixedCoreTypedSemiprimePairs z_positive).mp second_mem
  change first.1 * first.2 = second.1 * second.2 at same_product
  have first_divides : first.1 ∣ second.1 * second.2 := by
    rw [← same_product]
    exact dvd_mul_right _ _
  have first_equal : first.1 = second.1 := by
    rcases (first_prime.dvd_mul).mp first_divides with divides_small |
      divides_large
    · exact (Nat.prime_dvd_prime_iff_eq first_prime second_prime).mp
        divides_small
    · have impossible :=
        (Nat.prime_dvd_prime_iff_eq first_prime
          second_partner_prime).mp divides_large
      omega
  cases first with
  | mk s q =>
    cases second with
    | mk t r =>
      change s = t at first_equal
      subst t
      change s * q = s * r at same_product
      have partners_equal : q = r :=
        Nat.mul_left_cancel first_prime.pos same_product
      subst r
      rfl

/-- Exact closed-endpoint cardinality of all genuinely distinct typed
semiprime targets. -/
theorem fixedCoreTypedSemiprimeTargets_card
    {y z : ℕ} (z_positive : 0 < z)
    (square_threshold : z ≤ y / z) :
    (fixedCoreTypedSemiprimeTargets y z).card =
      ∑ s ∈ Nat.primesLE (z - 1),
        (Nat.primeCounting (y / s) - Nat.primeCounting (y / z)) := by
  unfold fixedCoreTypedSemiprimeTargets
  rw [(Finset.card_image_iff.mpr
    (fixedCoreTypedSemiprimePairs_multiplication_injOn
      z_positive square_threshold))]
  unfold fixedCoreTypedSemiprimePairs
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro s selected
  have prime := Nat.prime_of_mem_primesLE selected
  have bounded := Nat.le_of_mem_primesLE selected
  apply fixedCoreTypedSemiprimePartners_card prime
  omega

/-- A typed semiprime receives exactly one old broad-prime hit and no
nested-square hit from the actual fixed zero-residue core. -/
theorem fixedParameterCoreHits_typed_semiprime
    {y z s q : ℕ} (square_threshold : z ≤ y / z)
    (s_prime : s.Prime) (q_prime : q.Prime)
    (s_small : s < z) (q_large : y / z < q) :
    fixedParameterCoreHits y z (s * q) = 1 := by
  classical
  have s_bounded : s ≤ y / z := (Nat.le_of_lt s_small).trans square_threshold
  have distinct : s ≠ q := by omega
  have squarefree : Squarefree (s * q) :=
    (Nat.squarefree_mul ((Nat.coprime_primes s_prime q_prime).mpr
      distinct)).mpr ⟨s_prime.squarefree, q_prime.squarefree⟩
  have square_empty :
      ((fixedParameterCoreSquared y z).filter
        fun p => (0 : ℕ) ≡ s * q [MOD p ^ 2]) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p selected congruence
    have prime := fixedParameterCorePrimes_prime y z p
      (fixedParameterCoreSquared_subset y z selected)
    have divides := Nat.modEq_zero_iff_dvd.mp congruence.symm
    exact (Nat.squarefree_iff_prime_squarefree.mp squarefree p prime)
      (by simpa [pow_two] using divides)
  unfold fixedParameterCoreHits
  rw [fixedParameterCore_zero_broad_hits_eq_small_prime_factors
    (Nat.mul_pos s_prime.pos q_prime.pos), square_empty,
    Nat.primeFactors_mul s_prime.ne_zero q_prime.ne_zero,
    s_prime.primeFactors, q_prime.primeFactors]
  have surviving :
      (({s, q} : Finset ℕ).filter fun p => p ≤ y / z) = {s} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨equal | equal, bounded⟩
      · exact equal
      · subst p
        omega
    · intro equal
      subst p
      exact ⟨Or.inl rfl, s_bounded⟩
  simp [surviving]

/-- Membership in the actual target finset retains both distinct prime
factors, their strict type cutoffs, and the genuine interval endpoint. -/
theorem mem_fixedCoreTypedSemiprimeTargets
    {y z h : ℕ} (z_positive : 0 < z) :
    h ∈ fixedCoreTypedSemiprimeTargets y z ↔
      ∃ s q : ℕ, s.Prime ∧ s < z ∧ q.Prime ∧ y / z < q ∧
        s * q ≤ y ∧ h = s * q := by
  unfold fixedCoreTypedSemiprimeTargets
  constructor
  · intro selected
    obtain ⟨pair, pair_selected, equal⟩ := Finset.mem_image.mp selected
    obtain ⟨s_prime, small, q_prime, large, bounded⟩ :=
      (mem_fixedCoreTypedSemiprimePairs z_positive).mp pair_selected
    exact ⟨pair.1, pair.2, s_prime, small, q_prime,
      large, bounded, equal.symm⟩
  · rintro ⟨s, q, s_prime, small, q_prime, large, bounded, equal⟩
    subst h
    apply Finset.mem_image.mpr
    exact ⟨⟨s, q⟩,
      (mem_fixedCoreTypedSemiprimePairs z_positive).mpr
        ⟨s_prime, small, q_prime, large, bounded⟩,
      rfl⟩

/-- Every counted typed semiprime is a genuine positive interval target. -/
theorem fixedCoreTypedSemiprimeTargets_subset_interval
    {y z : ℕ} (z_positive : 0 < z) :
    fixedCoreTypedSemiprimeTargets y z ⊆ Finset.Icc 1 y := by
  intro h selected
  obtain ⟨s, q, s_prime, _small, q_prime, _large,
    bounded, equal⟩ :=
      (mem_fixedCoreTypedSemiprimeTargets z_positive).mp selected
  subst h
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_pos s_prime.pos q_prime.pos).ne', bounded⟩

/-- No prime target is silently double-counted as a typed semiprime target. -/
theorem primes_disjoint_fixedCoreTypedSemiprimeTargets
    {y z : ℕ} (z_positive : 0 < z) :
    Disjoint (Nat.primesLE y) (fixedCoreTypedSemiprimeTargets y z) := by
  apply Finset.disjoint_left.mpr
  intro h prime_target semiprime_target
  obtain ⟨s, q, s_prime, _small, q_prime, _large,
    _bounded, equal⟩ :=
      (mem_fixedCoreTypedSemiprimeTargets z_positive).mp semiprime_target
  have prime := Nat.prime_of_mem_primesLE prime_target
  subst h
  exact Nat.not_prime_mul s_prime.ne_one q_prime.ne_one prime

/-- Every genuinely typed semiprime needs one distinct new prime label. -/
theorem typedCore_typed_semiprime_needs_fresh_hit
    {y z : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (z_positive : 0 < z) (square_threshold : z ≤ y / z)
    (matching : ∀ h ∈ Finset.Icc 1 y,
      FixedParameterCoreDeficientType y z h →
        2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h)
    {h : ℕ} (selected : h ∈ fixedCoreTypedSemiprimeTargets y z) :
    1 ≤ typedCoreFreshHits R b h := by
  obtain ⟨s, q, s_prime, small, q_prime, large,
    bounded, equal⟩ :=
      (mem_fixedCoreTypedSemiprimeTargets z_positive).mp selected
  subst h
  have interval : s * q ∈ Finset.Icc 1 y :=
    Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_pos s_prime.pos q_prime.pos).ne', bounded⟩
  have target_type : FixedParameterCoreDeficientType y z (s * q) :=
    Or.inr (Or.inr (Or.inl
      ⟨s, q, s_prime, q_prime, small, large, rfl⟩))
  have required := matching (s * q) interval target_type
  rw [fixedParameterCoreHits_typed_semiprime
    square_threshold s_prime q_prime small large] at required
  omega

end Erdos1139
