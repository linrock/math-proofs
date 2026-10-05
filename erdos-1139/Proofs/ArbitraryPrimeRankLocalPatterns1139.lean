module

public import Mathlib
public import IndependentConstructionBridge1139
public import AnalyticBridge
public import UniformLocalFactors
public import TypedCoreRankBarrier1139

@[expose] public section


/-!
# Arbitrary-rank genuine NONZERO pure-prime local constellations

For every fixed rank `r ≥ 2`, use the ACTUAL affine prime forms

    p, q + 2 * primorial(r) * j * p,   0 ≤ j < r.

The common primorial multiplier is indispensable: the naive rank-three
family with step `2 * p` is obstructed already modulo three.

At a prime `ell ≤ r`, the entire step vanishes and the actual finite-field
unit-pair selector has `(ell - 1)^2` elements.  At every prime `ell > r`,
the step is a unit, the `r` forbidden center residues are distinct for
every nonzero label, and the genuine selector has exactly
`(ell - 1) * (ell - r)` elements.  Thus EVERY prime has a positive actual
local factor at EVERY fixed rank.  Any actual all-prime constellation
produces a genuine nonzero-residue prime-target collision bucket of rank
at least `r`.

No global Green--Tao--Ziegler estimate, high-rank target marginal, or
solution of Erdős #1139 is assumed or asserted.
-/

open Finset Filter
open scoped BigOperators Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos1139

/-- The primorial-dilated coefficient needed to remove ALL small-prime
local obstructions at the prescribed pure-prime rank. -/
def primeRankConstellationStep (rank : ℕ) : ℕ :=
  2 * primorial rank

/-- The common step is genuinely positive at every rank. -/
theorem primeRankConstellationStep_pos (rank : ℕ) :
    0 < primeRankConstellationStep rank := by
  unfold primeRankConstellationStep
  exact Nat.mul_pos (by norm_num) (primorial_pos rank)

/-- The `rank` actual forbidden center residues at a fixed genuine local
label.  The index `j = 0` correctly includes the center prime itself. -/
noncomputable def primeRankLocalForbidden
    (rank ell : ℕ) [Fact ell.Prime] (label : ZMod ell) : Finset (ZMod ell) :=
  (Finset.range rank).image fun j : ℕ =>
    -((primeRankConstellationStep rank : ZMod ell) *
      (j : ZMod ell) * label)

/-- Exact finite-field center options avoiding every genuine affine prime
form; it is an actual finite selector, not a symbolic density. -/
noncomputable def primeRankLocalGoodCenters
    (rank ell : ℕ) [Fact ell.Prime] (label : ZMod ell) : Finset (ZMod ell) :=
  Finset.univ \ primeRankLocalForbidden rank ell label

/-- The complete ACTUAL finite-field selector for the label prime and
all `rank` center-progressed prime forms. -/
noncomputable def primeRankLocalPairs
    (rank ell : ℕ) [Fact ell.Prime] : Finset (ZMod ell × ZMod ell) :=
  (Finset.univ.product Finset.univ).filter fun v =>
    v.1 ≠ 0 ∧ ∀ j ∈ Finset.range rank,
      v.2 + (primeRankConstellationStep rank : ZMod ell) *
        (j : ZMod ell) * v.1 ≠ 0

/-- Actual forbidden-center membership, retaining the exact affine sign. -/
theorem mem_primeRankLocalForbidden
    (rank ell : ℕ) [Fact ell.Prime] (label center : ZMod ell) :
    center ∈ primeRankLocalForbidden rank ell label ↔
      ∃ j < rank,
        center = -((primeRankConstellationStep rank : ZMod ell) *
          (j : ZMod ell) * label) := by
  simp [primeRankLocalForbidden, eq_comm]

/-- Exact local center admissibility is simultaneous nonvanishing of all
the actual progressed affine prime forms. -/
theorem mem_primeRankLocalGoodCenters
    (rank ell : ℕ) [Fact ell.Prime] (label center : ZMod ell) :
    center ∈ primeRankLocalGoodCenters rank ell label ↔
      ∀ j < rank,
        center + (primeRankConstellationStep rank : ZMod ell) *
          (j : ZMod ell) * label ≠ 0 := by
  simp only [primeRankLocalGoodCenters, Finset.mem_sdiff,
    Finset.mem_univ, true_and, mem_primeRankLocalForbidden]
  push Not
  simp [add_eq_zero_iff_eq_neg]

/-- Exact pair membership in terms of the genuine unit label and its
actual finite-field good-center selector. -/
theorem mem_primeRankLocalPairs
    (rank ell : ℕ) [Fact ell.Prime]
    (label center : ZMod ell) :
    (label, center) ∈ primeRankLocalPairs rank ell ↔
      label ≠ 0 ∧ center ∈ primeRankLocalGoodCenters rank ell label := by
  simp [primeRankLocalPairs, mem_primeRankLocalGoodCenters]

/-- Every local prime at most the rank genuinely divides the primorial
step; this is why all its progressed forms coincide. -/
theorem primeRankConstellationStep_cast_zero_of_small
    {rank ell : ℕ} [Fact ell.Prime] (small : ell ≤ rank) :
    (primeRankConstellationStep rank : ZMod ell) = 0 := by
  have prime : ell.Prime := Fact.out
  apply (ZMod.natCast_eq_zero_iff
    (primeRankConstellationStep rank) ell).mpr
  unfold primeRankConstellationStep
  exact dvd_mul_of_dvd_right (prime.dvd_primorial_iff.mpr small) 2

/-- Above a genuine rank at least two, the complete primorial step is a
unit modulo every local prime. -/
theorem primeRankConstellationStep_cast_ne_zero_of_large
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_large : 2 ≤ rank) (large : rank < ell) :
    (primeRankConstellationStep rank : ZMod ell) ≠ 0 := by
  have prime : ell.Prime := Fact.out
  intro zero
  have divides :=
    (ZMod.natCast_eq_zero_iff
      (primeRankConstellationStep rank) ell).mp zero
  unfold primeRankConstellationStep at divides
  rcases (prime.dvd_mul).mp divides with divides_two | divides_primorial
  · have equal :=
      (Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp divides_two
    omega
  · have bounded := prime.dvd_primorial_iff.mp divides_primorial
    omega

/-- At a small local prime, EVERY genuine affine form has the same
forbidden center residue: exactly zero. -/
theorem primeRankLocalForbidden_small_eq_singleton
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_positive : 0 < rank) (small : ell ≤ rank)
    (label : ZMod ell) :
    primeRankLocalForbidden rank ell label = {0} := by
  have zero := primeRankConstellationStep_cast_zero_of_small small
  ext center
  rw [mem_primeRankLocalForbidden]
  simp only [zero, zero_mul, neg_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨j, _bounded, equal⟩
    exact equal
  · intro equal
    exact ⟨0, rank_positive, equal⟩

/-- At a small local prime, the actual center selector has EXACTLY
`ell - 1` options for every label. -/
theorem primeRankLocalGoodCenters_card_small
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_positive : 0 < rank) (small : ell ≤ rank)
    (label : ZMod ell) :
    (primeRankLocalGoodCenters rank ell label).card = ell - 1 := by
  unfold primeRankLocalGoodCenters
  rw [primeRankLocalForbidden_small_eq_singleton rank_positive small label]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Finset.card_singleton]
  simp

/-- Above the rank, the genuine `rank` forbidden center residues are
PAIRWISE DISTINCT at every nonzero actual local label. -/
theorem primeRankLocalForbidden_card_large
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_large : 2 ≤ rank) (large : rank < ell)
    {label : ZMod ell} (label_nonzero : label ≠ 0) :
    (primeRankLocalForbidden rank ell label).card = rank := by
  classical
  unfold primeRankLocalForbidden
  calc
    ((Finset.range rank).image fun j : ℕ =>
      -((primeRankConstellationStep rank : ZMod ell) *
        (j : ZMod ell) * label)).card =
          (Finset.range rank).card := by
      apply Finset.card_image_iff.mpr
      intro i i_selected j j_selected equal
      have i_bound : i < rank := Finset.mem_range.mp i_selected
      have j_bound : j < rank := Finset.mem_range.mp j_selected
      have step_nonzero :=
        primeRankConstellationStep_cast_ne_zero_of_large rank_large large
      have without_neg := neg_injective equal
      have without_label := mul_right_cancel₀ label_nonzero without_neg
      have without_step := mul_left_cancel₀ step_nonzero without_label
      have modular :=
        (ZMod.natCast_eq_natCast_iff' i j ell).mp without_step
      rw [Nat.mod_eq_of_lt (i_bound.trans large),
        Nat.mod_eq_of_lt (j_bound.trans large)] at modular
      exact modular
    _ = rank := Finset.card_range rank

/-- Above the rank, the actual good-center selector has EXACTLY
`ell - rank` options at every nonzero label. -/
theorem primeRankLocalGoodCenters_card_large
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_large : 2 ≤ rank) (large : rank < ell)
    {label : ZMod ell} (label_nonzero : label ≠ 0) :
    (primeRankLocalGoodCenters rank ell label).card = ell - rank := by
  unfold primeRankLocalGoodCenters
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,
    primeRankLocalForbidden_card_large rank_large large label_nonzero]
  simp

/-- The exact first-coordinate fiber of the ACTUAL pair selector is in
bijection with its genuine local good-center selector. -/
theorem primeRankLocalPairs_fiber_card
    (rank ell : ℕ) [Fact ell.Prime]
    (label : ZMod ell) (label_nonzero : label ≠ 0) :
    ((primeRankLocalPairs rank ell).filter
      fun v => v.1 = label).card =
        (primeRankLocalGoodCenters rank ell label).card := by
  classical
  apply Finset.card_bij (fun v _ => v.2)
  · intro v selected
    obtain ⟨pair, first⟩ := Finset.mem_filter.mp selected
    obtain ⟨_, good⟩ := (mem_primeRankLocalPairs rank ell v.1 v.2).mp pair
    rwa [first] at good
  · intro v selected w selected' equal
    have first := (Finset.mem_filter.mp selected).2
    have first' := (Finset.mem_filter.mp selected').2
    exact Prod.ext (first.trans first'.symm) equal
  · intro center good
    refine ⟨(label, center), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_primeRankLocalPairs rank ell label center).mpr
        ⟨label_nonzero, good⟩, rfl⟩

/-- General exact fiberwise decomposition over all genuine nonzero local
labels. -/
theorem primeRankLocalPairs_card_eq_sum
    (rank ell : ℕ) [Fact ell.Prime] :
    (primeRankLocalPairs rank ell).card =
      ∑ label ∈ (Finset.univ.erase (0 : ZMod ell)),
        (primeRankLocalGoodCenters rank ell label).card := by
  classical
  let pairs := primeRankLocalPairs rank ell
  let units : Finset (ZMod ell) := Finset.univ.erase 0
  have filter_identity :
      pairs.filter (fun v => v.1 ∈ units) = pairs := by
    apply Finset.filter_true_of_mem
    intro v selected
    have nonzero :=
      ((mem_primeRankLocalPairs rank ell v.1 v.2).mp selected).1
    exact Finset.mem_erase.mpr ⟨nonzero, Finset.mem_univ _⟩
  have fibers := Finset.sum_card_fiberwise_eq_card_filter
    pairs units (fun v : ZMod ell × ZMod ell => v.1)
  rw [filter_identity] at fibers
  calc
    pairs.card =
        ∑ label ∈ units, (pairs.filter fun v => v.1 = label).card :=
      fibers.symm
    _ = ∑ label ∈ units,
          (primeRankLocalGoodCenters rank ell label).card := by
      apply Finset.sum_congr rfl
      intro label selected
      exact primeRankLocalPairs_fiber_card rank ell label
        (Finset.mem_erase.mp selected).1

/-- EXACT actual local-pair count at EVERY prime at most the rank:
both the label and the common center are independently nonzero. -/
theorem primeRankLocalPairs_card_small
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_positive : 0 < rank) (small : ell ≤ rank) :
    (primeRankLocalPairs rank ell).card = (ell - 1) ^ 2 := by
  rw [primeRankLocalPairs_card_eq_sum]
  simp_rw [primeRankLocalGoodCenters_card_small rank_positive small]
  simp [pow_two]

/-- EXACT actual local-pair count at EVERY prime above the rank:
the `rank` distinct affine roots leave `ell - rank` genuine centers. -/
theorem primeRankLocalPairs_card_large
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_large : 2 ≤ rank) (large : rank < ell) :
    (primeRankLocalPairs rank ell).card =
      (ell - 1) * (ell - rank) := by
  rw [primeRankLocalPairs_card_eq_sum]
  have fibers :
      (∑ label ∈ (Finset.univ.erase (0 : ZMod ell)),
        (primeRankLocalGoodCenters rank ell label).card) =
        ∑ _label ∈ (Finset.univ.erase (0 : ZMod ell)),
          (ell - rank) := by
    apply Finset.sum_congr rfl
    intro label selected
    exact primeRankLocalGoodCenters_card_large rank_large large
      (Finset.mem_erase.mp selected).1
  rw [fibers]
  simp

/-- The ACTUAL local selector is nonempty at EVERY prime and EVERY fixed
pure-prime rank at least two. -/
theorem primeRankLocalPairs_nonempty
    (rank ell : ℕ) [Fact ell.Prime] (rank_large : 2 ≤ rank) :
    (primeRankLocalPairs rank ell).Nonempty := by
  have prime : ell.Prime := Fact.out
  rw [← Finset.card_pos]
  by_cases small : ell ≤ rank
  · rw [primeRankLocalPairs_card_small (by omega) small]
    exact pow_pos (Nat.sub_pos_of_lt prime.one_lt) _
  · have large : rank < ell := by omega
    rw [primeRankLocalPairs_card_large rank_large large]
    exact Nat.mul_pos (Nat.sub_pos_of_lt prime.one_lt)
      (Nat.sub_pos_of_lt large)

/-- Fully explicit all-prime local admissibility: every prime admits
genuine NONZERO label and center residues for ALL `rank` pure-prime
forms simultaneously. -/
theorem primeRankConstellation_all_prime_locally_admissible
    (rank : ℕ) (rank_large : 2 ≤ rank)
    (ell : ℕ) [Fact ell.Prime] :
    ∃ label center : ZMod ell,
      label ≠ 0 ∧ ∀ j < rank,
        center + (primeRankConstellationStep rank : ZMod ell) *
          (j : ZMod ell) * label ≠ 0 := by
  obtain ⟨⟨label, center⟩, selected⟩ :=
    primeRankLocalPairs_nonempty rank ell rank_large
  obtain ⟨nonzero, good⟩ :=
    (mem_primeRankLocalPairs rank ell label center).mp selected
  exact ⟨label, center, nonzero,
    (mem_primeRankLocalGoodCenters rank ell label center).mp good⟩

/-- Actual normalized local factor for `rank + 1` simultaneous genuine
prime forms and two independent finite-field coordinates. -/
noncomputable def primeRankNormalizedLocalFactor
    (rank ell : ℕ) [Fact ell.Prime] : ℝ :=
  (((primeRankLocalPairs rank ell).card : ℝ) / (ell : ℝ) ^ 2) *
    ((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank + 1)

/-- Instance-free scalar packaging of genuine local factors for products
indexed by an ordinary finite set of prime numbers. -/
noncomputable def primeRankScalarLocalFactor
    (rank ell : ℕ) : ℝ :=
  if prime : ell.Prime then
    @primeRankNormalizedLocalFactor rank ell ⟨prime⟩
  else 0

/-- At every small local prime, the actual normalized factor has the
EXACT positive closed form `(ell / (ell - 1)) ^ (rank - 1)`. -/
theorem primeRankNormalizedLocalFactor_small
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_positive : 0 < rank) (small : ell ≤ rank) :
    primeRankNormalizedLocalFactor rank ell =
      ((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank - 1) := by
  have prime : ell.Prime := Fact.out
  have ell_nonzero : (ell : ℝ) ≠ 0 := by exact_mod_cast prime.ne_zero
  have denominator : (ell : ℝ) - 1 ≠ 0 := by
    have large : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
    linarith
  have exponent : rank + 1 = (rank - 1) + 2 := by omega
  unfold primeRankNormalizedLocalFactor
  rw [primeRankLocalPairs_card_small rank_positive small]
  push_cast [Nat.cast_sub prime.one_le]
  rw [exponent, pow_add]
  have cancellation :
      (((ell : ℝ) - 1) ^ 2 / (ell : ℝ) ^ 2) *
          ((ell : ℝ) / ((ell : ℝ) - 1)) ^ 2 = 1 := by
    field_simp
  calc
    (((ell : ℝ) - 1) ^ 2 / (ell : ℝ) ^ 2) *
        (((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank - 1) *
          ((ell : ℝ) / ((ell : ℝ) - 1)) ^ 2) =
      ((((ell : ℝ) - 1) ^ 2 / (ell : ℝ) ^ 2) *
        ((ell : ℝ) / ((ell : ℝ) - 1)) ^ 2) *
        ((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank - 1) := by ring
    _ = _ := by rw [cancellation, one_mul]

/-- Every small-prime local factor is at least one; the small support
can therefore only IMPROVE any global product lower bound. -/
theorem primeRankNormalizedLocalFactor_small_ge_one
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_positive : 0 < rank) (small : ell ≤ rank) :
    (1 : ℝ) ≤ primeRankNormalizedLocalFactor rank ell := by
  rw [primeRankNormalizedLocalFactor_small rank_positive small]
  have prime : ell.Prime := Fact.out
  have denominator : (0 : ℝ) < (ell : ℝ) - 1 := by
    have large : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
    linarith
  have base : (1 : ℝ) ≤ (ell : ℝ) / ((ell : ℝ) - 1) := by
    apply (le_div_iff₀ denominator).mpr
    linarith
  exact one_le_pow₀ base

/-- Above the rank, the actual normalized local factor is EXACTLY
`((ell-r)/(ell-1)) * (ell/(ell-1))^(r-1)`. -/
theorem primeRankNormalizedLocalFactor_large
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_large : 2 ≤ rank) (large : rank < ell) :
    primeRankNormalizedLocalFactor rank ell =
      (((ell : ℝ) - rank) / ((ell : ℝ) - 1)) *
        ((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank - 1) := by
  have prime : ell.Prime := Fact.out
  have ell_nonzero : (ell : ℝ) ≠ 0 := by exact_mod_cast prime.ne_zero
  have denominator : (ell : ℝ) - 1 ≠ 0 := by
    have big : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
    linarith
  have exponent : rank + 1 = (rank - 1) + 2 := by omega
  unfold primeRankNormalizedLocalFactor
  rw [primeRankLocalPairs_card_large rank_large large]
  push_cast [Nat.cast_sub prime.one_le,
    Nat.cast_sub (Nat.le_of_lt large)]
  rw [exponent, pow_add]
  have cancellation :
      ((((ell : ℝ) - 1) * ((ell : ℝ) - rank) /
        (ell : ℝ) ^ 2) *
          ((ell : ℝ) / ((ell : ℝ) - 1)) ^ 2) =
        ((ell : ℝ) - rank) / ((ell : ℝ) - 1) := by
    field_simp
  calc
    (((ell : ℝ) - 1) * ((ell : ℝ) - rank) / (ell : ℝ) ^ 2) *
      (((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank - 1) *
       ((ell : ℝ) / ((ell : ℝ) - 1)) ^ 2) =
      ((((ell : ℝ) - 1) * ((ell : ℝ) - rank) /
        (ell : ℝ) ^ 2) *
          ((ell : ℝ) / ((ell : ℝ) - 1)) ^ 2) *
        ((ell : ℝ) / ((ell : ℝ) - 1)) ^ (rank - 1) := by ring
    _ = _ := by rw [cancellation]

/-- The arbitrary-rank large-prime factor has a QUADRATIC rather than
linear deficit, uniformly bounded below by
`1 - (rank - 1)^2 / (ell - 1)^2`. -/
theorem primeRankNormalizedLocalFactor_large_inverse_square_lower
    {rank ell : ℕ} [Fact ell.Prime]
    (rank_large : 2 ≤ rank) (large : rank < ell) :
    1 - (((rank - 1 : ℕ) : ℝ) ^ 2 /
      ((ell : ℝ) - 1) ^ 2) ≤
        primeRankNormalizedLocalFactor rank ell := by
  have prime : ell.Prime := Fact.out
  have ell_real : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
  have rank_le : (rank : ℝ) ≤ ell := by
    exact_mod_cast (Nat.le_of_lt large)
  have denominator : (0 : ℝ) < (ell : ℝ) - 1 := by linarith
  have rank_cast : (((rank - 1 : ℕ) : ℝ)) = (rank : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ rank)]
    norm_num
  have base_identity :
      (ell : ℝ) / ((ell : ℝ) - 1) =
        1 + 1 / ((ell : ℝ) - 1) := by
    field_simp
    ring
  have bernoulli :
      1 + (((rank - 1 : ℕ) : ℝ)) *
        (1 / ((ell : ℝ) - 1)) ≤
          (1 + 1 / ((ell : ℝ) - 1)) ^ (rank - 1) := by
    simpa using one_add_mul_le_pow
      (show (-2 : ℝ) ≤ 1 / ((ell : ℝ) - 1) by
        have := (one_div_pos.mpr denominator).le
        linarith)
        (rank - 1)
  have first_nonnegative :
      (0 : ℝ) ≤ ((ell : ℝ) - rank) / ((ell : ℝ) - 1) := by
    exact div_nonneg (by linarith) denominator.le
  rw [primeRankNormalizedLocalFactor_large rank_large large,
    base_identity]
  calc
    1 - (((rank - 1 : ℕ) : ℝ) ^ 2 /
      ((ell : ℝ) - 1) ^ 2) =
        (((ell : ℝ) - rank) / ((ell : ℝ) - 1)) *
          (1 + (((rank - 1 : ℕ) : ℝ)) *
            (1 / ((ell : ℝ) - 1))) := by
      rw [rank_cast]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left bernoulli first_nonnegative

/-- Every actual normalized arbitrary-rank local factor is STRICTLY
positive; hence there is no small-prime or parity obstruction. -/
theorem primeRankNormalizedLocalFactor_pos
    (rank ell : ℕ) [Fact ell.Prime] (rank_large : 2 ≤ rank) :
    0 < primeRankNormalizedLocalFactor rank ell := by
  have prime : ell.Prime := Fact.out
  have pairs_positive : 0 < (primeRankLocalPairs rank ell).card :=
    Finset.card_pos.mpr (primeRankLocalPairs_nonempty rank ell rank_large)
  have real_ell : (0 : ℝ) < ell := by exact_mod_cast prime.pos
  have ell_one : (0 : ℝ) < (ell : ℝ) - 1 := by
    have : (1 : ℝ) < ell := by exact_mod_cast prime.one_lt
    linarith
  unfold primeRankNormalizedLocalFactor
  have real_pairs : (0 : ℝ) <
      ((primeRankLocalPairs rank ell).card : ℝ) := by
    exact_mod_cast pairs_positive
  positivity

/-- Every finite product of the GENUINE arbitrary-rank local factors is
strictly positive; no Euler-product/major-arc coupling is presumed. -/
theorem primeRankNormalizedLocalFactor_finite_product_pos
    (rank : ℕ) (rank_large : 2 ≤ rank)
    (T : Finset ℕ) (primes : ∀ ell ∈ T, ell.Prime) :
    0 < ∏ ell ∈ T, primeRankScalarLocalFactor rank ell := by
  classical
  apply Finset.prod_pos
  intro ell selected
  have prime := primes ell selected
  simp only [primeRankScalarLocalFactor, dif_pos prime]
  exact @primeRankNormalizedLocalFactor_pos rank ell ⟨prime⟩ rank_large

/-- Partitioning indices by their remainder modulo `c` converts the
scaled inverse-square losses into `c` genuinely injective ordinary
inverse-square families.  The resulting bound is UNIFORM in the finite
support; it depends only on the fixed scale `c`. -/
theorem primeRankScaledInverseSquare_support_lower
    (c : ℕ) (positive : 0 < c) (T : Finset ℕ)
    (cutoff : ∀ ell ∈ T, 2 * c + 1 ≤ ell) :
    ((1 / 2 : ℝ) ^ c) ≤
      ∏ ell ∈ T,
        (1 - (c : ℝ) ^ 2 / ((ell : ℝ) - 1) ^ 2) := by
  classical
  let quotient : ℕ → ℕ := fun ell => (ell - 1) / c
  let remainder : ℕ → ℕ := fun ell => (ell - 1) % c
  let scaled : ℕ → ℝ :=
    fun ell => 1 - (c : ℝ) ^ 2 / ((ell : ℝ) - 1) ^ 2
  have quotient_large : ∀ ell ∈ T, 2 ≤ quotient ell := by
    intro ell selected
    apply (Nat.le_div_iff_mul_le positive).mpr
    have bound := cutoff ell selected
    omega
  have pointwise : ∀ ell ∈ T,
      1 - 1 / (quotient ell : ℝ) ^ 2 ≤ scaled ell := by
    intro ell selected
    have ell_bound := cutoff ell selected
    have quotient_bound := quotient_large ell selected
    have denominator : (0 : ℝ) < (ell : ℝ) - 1 := by
      have real_bound : (1 : ℝ) < ell := by
        exact_mod_cast (by omega : 1 < ell)
      linarith
    have quotient_positive : (0 : ℝ) < quotient ell := by
      exact_mod_cast (by omega : 0 < quotient ell)
    have integer_bound : quotient ell * c ≤ ell - 1 :=
      Nat.div_mul_le_self (ell - 1) c
    have real_bound :
        (c : ℝ) * (quotient ell : ℝ) ≤ (ell : ℝ) - 1 := by
      have casted : ((quotient ell * c : ℕ) : ℝ) ≤
          ((ell - 1 : ℕ) : ℝ) := by exact_mod_cast integer_bound
      rw [Nat.cast_sub (by omega : 1 ≤ ell)] at casted
      push_cast at casted
      nlinarith
    have ratio :
        (c : ℝ) / ((ell : ℝ) - 1) ≤
          1 / (quotient ell : ℝ) := by
      apply (div_le_div_iff₀ denominator quotient_positive).mpr
      simpa using real_bound
    have squared := mul_self_le_mul_self
      (show (0 : ℝ) ≤ (c : ℝ) / ((ell : ℝ) - 1) by positivity)
      ratio
    have square_ratio :
        (c : ℝ) ^ 2 / ((ell : ℝ) - 1) ^ 2 ≤
          1 / (quotient ell : ℝ) ^ 2 := by
      simpa [pow_two, div_mul_div_comm] using squared
    dsimp [scaled]
    linarith
  have fiber_lower : ∀ residue ∈ Finset.range c,
      (1 / 2 : ℝ) ≤
        ∏ ell ∈ T.filter (fun ell => remainder ell = residue),
          scaled ell := by
    intro residue _residue_bounded
    let fiber := T.filter fun ell => remainder ell = residue
    have injective :
        Set.InjOn quotient (↑fiber : Set ℕ) := by
      intro i i_selected j j_selected same_quotient
      have i_fiber : i ∈ fiber := Finset.mem_coe.mp i_selected
      have j_fiber : j ∈ fiber := Finset.mem_coe.mp j_selected
      obtain ⟨i_selected', i_remainder⟩ := Finset.mem_filter.mp i_fiber
      obtain ⟨j_selected', j_remainder⟩ := Finset.mem_filter.mp j_fiber
      have same_remainder : remainder i = remainder j :=
        i_remainder.trans j_remainder.symm
      have i_division := Nat.mod_add_div (i - 1) c
      have j_division := Nat.mod_add_div (j - 1) c
      change (i - 1) % c = (j - 1) % c at same_remainder
      change (i - 1) / c = (j - 1) / c at same_quotient
      rw [same_remainder, same_quotient] at i_division
      have i_positive : 1 ≤ i := by
        have := cutoff i i_selected'
        omega
      have j_positive : 1 ≤ j := by
        have := cutoff j j_selected'
        omega
      omega
    have image_large : ∀ k ∈ fiber.image quotient, 2 ≤ k := by
      intro k selected
      obtain ⟨ell, ell_selected, rfl⟩ := Finset.mem_image.mp selected
      exact quotient_large ell (Finset.mem_filter.mp ell_selected).1
    calc
      (1 / 2 : ℝ) ≤
          ∏ k ∈ fiber.image quotient, (1 - 1 / (k : ℝ) ^ 2) :=
        Erdos689.finite_inverse_square_product_lower
          (fiber.image quotient) image_large
      _ = ∏ ell ∈ fiber,
          (1 - 1 / (quotient ell : ℝ) ^ 2) := by
        rw [Finset.prod_image injective]
      _ ≤ ∏ ell ∈ fiber, scaled ell := by
        apply Finset.prod_le_prod₀
        · intro ell selected
          exact Erdos689.inverse_square_factor_nonnegative
            (quotient_large ell (Finset.mem_filter.mp selected).1)
        · intro ell selected
          exact pointwise ell (Finset.mem_filter.mp selected).1
  have maps : ∀ ell ∈ T, remainder ell ∈ Finset.range c := by
    intro ell _selected
    exact Finset.mem_range.mpr (Nat.mod_lt _ positive)
  calc
    ((1 / 2 : ℝ) ^ c) =
        ∏ _residue ∈ Finset.range c, (1 / 2 : ℝ) := by simp
    _ ≤ ∏ residue ∈ Finset.range c,
          ∏ ell ∈ T.filter (fun ell => remainder ell = residue),
            scaled ell := by
      apply Finset.prod_le_prod₀
      · intro residue _selected
        norm_num
      · exact fiber_lower
    _ = ∏ ell ∈ T, scaled ell :=
      Finset.prod_fiberwise_of_maps_to maps scaled
    _ = _ := rfl

/-- The ENTIRE large-prime tail of the actual arbitrary-rank singular
product has a support-independent positive bound `2 ^ (1-r)`. -/
theorem primeRankNormalizedLocalFactor_tail_product_lower
    (rank : ℕ) (rank_large : 2 ≤ rank)
    (T : Finset ℕ) (primes : ∀ ell ∈ T, ell.Prime)
    (cutoff : ∀ ell ∈ T, 2 * (rank - 1) + 1 ≤ ell) :
    ((1 / 2 : ℝ) ^ (rank - 1)) ≤
      ∏ ell ∈ T, primeRankScalarLocalFactor rank ell := by
  have rank_sub_positive : 0 < rank - 1 := by omega
  have inverse_lower :=
    primeRankScaledInverseSquare_support_lower
      (rank - 1) rank_sub_positive T cutoff
  apply inverse_lower.trans
  apply Finset.prod_le_prod₀
  · intro ell selected
    have bound := cutoff ell selected
    have quotient :
        (((rank - 1 : ℕ) : ℝ)) < (ell : ℝ) - 1 := by
      have integer : rank - 1 < ell - 1 := by omega
      have casted : (((rank - 1 : ℕ) : ℝ)) <
          (((ell - 1 : ℕ) : ℝ)) := by exact_mod_cast integer
      rw [Nat.cast_sub (by omega : 1 ≤ ell)] at casted
      simpa using casted
    have denominator : (0 : ℝ) < (ell : ℝ) - 1 := by
      have real_rank : (0 : ℝ) ≤ (((rank - 1 : ℕ) : ℝ)) := by positivity
      exact real_rank.trans_lt quotient
    have ratio :
        (((rank - 1 : ℕ) : ℝ)) ^ 2 ≤ ((ell : ℝ) - 1) ^ 2 := by
      exact (sq_le_sq₀ (by positivity) denominator.le).mpr quotient.le
    apply sub_nonneg.mpr
    apply (div_le_one (sq_pos_of_pos denominator)).mpr
    exact ratio
  · intro ell selected
    have prime := primes ell selected
    have bound := cutoff ell selected
    have large : rank < ell := by omega
    simp only [primeRankScalarLocalFactor, dif_pos prime]
    exact @primeRankNormalizedLocalFactor_large_inverse_square_lower
      rank ell ⟨prime⟩ rank_large large

/-- The rank-dependent finite exceptional-prime floor; clipping at one
ensures that adding or deleting any small prime cannot invalidate a
UNIFORM support-independent lower bound. -/
noncomputable def primeRankExceptionalLocalFloor (rank : ℕ) : ℝ :=
  ∏ ell ∈ Nat.primesLE (2 * (rank - 1)),
    min 1 (primeRankScalarLocalFactor rank ell)

/-- The actual finite exceptional-prime floor is STRICTLY positive at
every fixed pure-prime rank at least two. -/
theorem primeRankExceptionalLocalFloor_pos
    (rank : ℕ) (rank_large : 2 ≤ rank) :
    0 < primeRankExceptionalLocalFloor rank := by
  unfold primeRankExceptionalLocalFloor
  apply Finset.prod_pos
  intro ell selected
  have prime := Nat.prime_of_mem_primesLE selected
  have factor_positive : 0 < primeRankScalarLocalFactor rank ell := by
    simp only [primeRankScalarLocalFactor, dif_pos prime]
    exact @primeRankNormalizedLocalFactor_pos
      rank ell ⟨prime⟩ rank_large
  exact lt_min (by norm_num) factor_positive

/-- FULL GENUINE SUPPORT-INDEPENDENT singular-factor positivity for EVERY
fixed rank: the same explicitly positive rank-dependent constant works
for EVERY finite set of genuine local primes, regardless of its size. -/
theorem primeRankNormalizedLocalFactor_full_support_lower
    (rank : ℕ) (rank_large : 2 ≤ rank)
    (T : Finset ℕ) (primes : ∀ ell ∈ T, ell.Prime) :
    primeRankExceptionalLocalFloor rank *
        ((1 / 2 : ℝ) ^ (rank - 1)) ≤
      ∏ ell ∈ T, primeRankScalarLocalFactor rank ell := by
  classical
  let cutoff := 2 * (rank - 1)
  let initial := T.filter fun ell => ell ≤ cutoff
  let tail := T.filter fun ell => cutoff + 1 ≤ ell
  have split : T = initial ∪ tail := by
    ext ell
    constructor
    · intro selected
      by_cases low : ell ≤ cutoff
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨selected, low⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨selected, by omega⟩)
    · intro selected
      rcases Finset.mem_union.mp selected with low | high
      · exact (Finset.mem_filter.mp low).1
      · exact (Finset.mem_filter.mp high).1
  have disjoint : Disjoint initial tail := by
    apply Finset.disjoint_left.mpr
    intro ell low high
    have low_bound := (Finset.mem_filter.mp low).2
    have high_bound := (Finset.mem_filter.mp high).2
    omega
  have initial_subset : initial ⊆ Nat.primesLE cutoff := by
    intro ell selected
    obtain ⟨in_support, bounded⟩ := Finset.mem_filter.mp selected
    exact Nat.mem_primesLE.mpr ⟨bounded, primes ell in_support⟩
  have initial_lower :
      primeRankExceptionalLocalFloor rank ≤
        ∏ ell ∈ initial, primeRankScalarLocalFactor rank ell := by
    have clipped :
        (∏ ell ∈ Nat.primesLE cutoff,
          min 1 (primeRankScalarLocalFactor rank ell)) ≤
          ∏ ell ∈ initial,
            min 1 (primeRankScalarLocalFactor rank ell) := by
      apply Finset.prod_le_prod_of_subset_of_le_one₀ initial_subset
      · intro ell selected
        have prime := Nat.prime_of_mem_primesLE selected
        have positive : 0 < primeRankScalarLocalFactor rank ell := by
          simp only [primeRankScalarLocalFactor, dif_pos prime]
          exact @primeRankNormalizedLocalFactor_pos
            rank ell ⟨prime⟩ rank_large
        exact le_min (by norm_num) positive.le
      · intro ell _selected _missing
        exact min_le_left _ _
    calc
      primeRankExceptionalLocalFloor rank =
          ∏ ell ∈ Nat.primesLE cutoff,
            min 1 (primeRankScalarLocalFactor rank ell) := rfl
      _ ≤ ∏ ell ∈ initial,
          min 1 (primeRankScalarLocalFactor rank ell) := clipped
      _ ≤ ∏ ell ∈ initial,
          primeRankScalarLocalFactor rank ell := by
        apply Finset.prod_le_prod₀
        · intro ell selected
          have in_support := (Finset.mem_filter.mp selected).1
          have prime := primes ell in_support
          have positive : 0 < primeRankScalarLocalFactor rank ell := by
            simp only [primeRankScalarLocalFactor, dif_pos prime]
            exact @primeRankNormalizedLocalFactor_pos
              rank ell ⟨prime⟩ rank_large
          exact le_min (by norm_num) positive.le
        · intro ell _selected
          exact min_le_right _ _
  have tail_lower :
      ((1 / 2 : ℝ) ^ (rank - 1)) ≤
        ∏ ell ∈ tail, primeRankScalarLocalFactor rank ell := by
    apply primeRankNormalizedLocalFactor_tail_product_lower rank rank_large
    · intro ell selected
      exact primes ell (Finset.mem_filter.mp selected).1
    · intro ell selected
      exact (Finset.mem_filter.mp selected).2
  have initial_nonnegative :
      0 ≤ ∏ ell ∈ initial, primeRankScalarLocalFactor rank ell := by
    apply Finset.prod_nonneg
    intro ell selected
    have prime := primes ell (Finset.mem_filter.mp selected).1
    simp only [primeRankScalarLocalFactor, dif_pos prime]
    exact (@primeRankNormalizedLocalFactor_pos
      rank ell ⟨prime⟩ rank_large).le
  rw [split, Finset.prod_union disjoint]
  exact mul_le_mul initial_lower tail_lower (by positivity)
    initial_nonnegative

/-- For EVERY fixed rank there exists a SINGLE strictly positive constant
bounding below ALL actual finite singular products over genuine primes.
This completely removes the arbitrary-rank local Euler-factor obstruction;
the global analytic prime-constellation and covering marginal remain open. -/
theorem primeRankNormalizedLocalFactor_uniform_positive
    (rank : ℕ) (rank_large : 2 ≤ rank) :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : Finset ℕ, (∀ ell ∈ T, ell.Prime) →
        c ≤ ∏ ell ∈ T, primeRankScalarLocalFactor rank ell := by
  refine ⟨primeRankExceptionalLocalFloor rank *
    ((1 / 2 : ℝ) ^ (rank - 1)), ?_, ?_⟩
  · exact mul_pos (primeRankExceptionalLocalFloor_pos rank rank_large)
      (by positivity)
  · intro T primes
    exact primeRankNormalizedLocalFactor_full_support_lower
      rank rank_large T primes

end Erdos1139
