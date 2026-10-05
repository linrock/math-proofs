module

public import FixedCoreAsymptotic1139

@[expose] public section


/-!
# Exact typed-target matching obstruction for Erdős problem #1139

The genuine fixed-parameter zero-residue core has logarithmic cost
`(1 / z + o_z(1)) * y` and an exactly classified deficient-target set.  Its
remaining targets require differing numbers of new hits: a large prime or
`1` requires two, while a genuinely singly covered typed semiprime requires
only one.

This file proves the sharp finite extension principle for any coherent fresh
prime-residue assignment, preserving the existing nested square classes and
factoring the actual mixed conductor exactly.  It then gives one explicit
fixed-parameter, typed-target matching hypothesis sufficient for the literal
original infinite-limsup conjecture.

The typed prime-pattern/hypergraph matching hypothesis is NOT proved here;
it is precisely the remaining analytic obstruction.  No axiom, placeholder,
or claim of a complete unconditional solution is introduced.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- The exact number of prime and paid nested-square hits supplied by the
literal initial zero-residue core. -/
def fixedParameterCoreHits (y z h : ℕ) : ℕ :=
  ((fixedParameterCorePrimes y z).filter
    fun p => (0 : ℕ) ≡ h [MOD p]).card +
    ((fixedParameterCoreSquared y z).filter
      fun p => (0 : ℕ) ≡ h [MOD p ^ 2]).card

/-- Every fresh label carries ONE globally coherent prime residue; the same
label may hit multiple different deficient targets. -/
def typedCoreFreshHits (R : Finset ℕ) (b : ℕ → ℕ) (h : ℕ) : ℕ :=
  (R.filter fun p => b p ≡ h [MOD p]).card

/-- Coherently glue the old zero-residue assignment and the new prime-label
assignment.  Freshness prevents any residue conflict. -/
def typedCoreGluedResidue (y z : ℕ) (b : ℕ → ℕ) (p : ℕ) : ℕ :=
  if p ∈ fixedParameterCorePrimes y z then 0 else b p

/-- Exact broad-prime hit ledger: disjoint old and fresh prime supports
contribute additively, with no double-counted label. -/
theorem typedCore_broad_hits_add
    {y z h : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (fresh : Disjoint (fixedParameterCorePrimes y z) R) :
    (((fixedParameterCorePrimes y z) ∪ R).filter
      fun p => typedCoreGluedResidue y z b p ≡ h [MOD p]).card =
      ((fixedParameterCorePrimes y z).filter
        fun p => (0 : ℕ) ≡ h [MOD p]).card +
        typedCoreFreshHits R b h := by
  classical
  have split :
      (((fixedParameterCorePrimes y z) ∪ R).filter
        fun p => typedCoreGluedResidue y z b p ≡ h [MOD p]) =
        ((fixedParameterCorePrimes y z).filter
          fun p => (0 : ℕ) ≡ h [MOD p]) ∪
          (R.filter fun p => b p ≡ h [MOD p]) := by
    ext p
    by_cases in_core : p ∈ fixedParameterCorePrimes y z
    · have not_fresh : p ∉ R := Finset.disjoint_left.mp fresh in_core
      simp only [Finset.mem_filter, Finset.mem_union]
      simp [typedCoreGluedResidue, in_core, not_fresh]
    · simp only [Finset.mem_filter, Finset.mem_union]
      simp [typedCoreGluedResidue, in_core]
  rw [split, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter fresh)]
  rfl

/-- All selected nested square classes remain exactly the initial
zero-residue classes; no new label silently acquires a square exponent. -/
theorem typedCore_square_hits_unchanged
    (y z h : ℕ) (b : ℕ → ℕ) :
    ((fixedParameterCoreSquared y z).filter
      fun p => typedCoreGluedResidue y z b p ≡ h [MOD p ^ 2]) =
      ((fixedParameterCoreSquared y z).filter
        fun p => (0 : ℕ) ≡ h [MOD p ^ 2]) := by
  apply Finset.filter_congr
  intro p selected
  have in_core := fixedParameterCoreSquared_subset y z selected
  simp [typedCoreGluedResidue, in_core]

/-- Exact heterogeneous mixed-hit identity: old broad-plus-square hits plus
the genuine new broad-prime hits. -/
theorem typedCore_total_hits_eq
    {y z h : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (fresh : Disjoint (fixedParameterCorePrimes y z) R) :
    (((fixedParameterCorePrimes y z) ∪ R).filter
      fun p => typedCoreGluedResidue y z b p ≡ h [MOD p]).card +
      ((fixedParameterCoreSquared y z).filter
        fun p => typedCoreGluedResidue y z b p ≡ h [MOD p ^ 2]).card =
      fixedParameterCoreHits y z h + typedCoreFreshHits R b h := by
  rw [typedCore_broad_hits_add fresh,
    typedCore_square_hits_unchanged]
  unfold fixedParameterCoreHits
  omega

/-- Sharp finite typed-target matching bridge.  Only ACTUALLY deficient
classified targets need to be repaired, and each target receives precisely
its remaining hit requirement rather than two indiscriminate new labels. -/
theorem typedCore_complete_cover_of_matching
    {y z : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (parameter_positive : 0 < z)
    (square_threshold : z ≤ y / z)
    (reserve_primes : ∀ p ∈ R, p.Prime)
    (fresh : Disjoint (fixedParameterCorePrimes y z) R)
    (matching : ∀ h ∈ Finset.Icc 1 y,
      FixedParameterCoreDeficientType y z h →
        2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h) :
    UnrestrictedPrimeSquareDoubleCover y
      ((fixedParameterCorePrimes y z) ∪ R)
      (fixedParameterCoreSquared y z)
      (typedCoreGluedResidue y z b) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with in_core | in_reserve
    · exact fixedParameterCorePrimes_prime y z p in_core
    · exact reserve_primes p in_reserve
  · intro p hp
    exact Finset.mem_union_left R
      (fixedParameterCoreSquared_subset y z hp)
  · intro h interval
    rw [typedCore_total_hits_eq fresh]
    by_cases deficient :
        h ∈ deficientTargets y (fixedParameterCorePrimes y z)
          (fixedParameterCoreSquared y z) (fun _ => 0)
    · exact matching h interval
        ((fixedParameterCore_deficiency_exact_classification
          parameter_positive square_threshold).mp deficient).2
    · have old_enough : 2 ≤ fixedParameterCoreHits y z h := by
        by_contra not_enough
        apply deficient
        apply Finset.mem_filter.mpr
        exact ⟨interval, by
          change fixedParameterCoreHits y z h < 2
          omega⟩
      omega

/-- Exact multiplicative conductor ledger for every coherent fresh-label
extension; new primes are paid once and old nested squares are preserved. -/
theorem typedCore_actual_conductor_factor
    {y z : ℕ} {R : Finset ℕ}
    (fresh : Disjoint (fixedParameterCorePrimes y z) R) :
    (∏ p ∈ (fixedParameterCorePrimes y z) ∪ R,
      selectedPrimePower (fixedParameterCoreSquared y z) p) =
      (∏ p ∈ fixedParameterCorePrimes y z,
        selectedPrimePower (fixedParameterCoreSquared y z) p) *
        ∏ p ∈ R, p := by
  classical
  rw [Finset.prod_union fresh]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have not_squared : p ∉ fixedParameterCoreSquared y z := by
    intro selected
    exact Finset.disjoint_left.mp fresh
      (fixedParameterCoreSquared_subset y z selected) hp
  simp [selectedPrimePower, selectedPrimeExponent, not_squared]

/-- Substituting the actual fixed-parameter conductor gives the completely
explicit three-factor product, including all selected square exponents. -/
theorem typedCore_actual_conductor_eq_primorials
    {y z : ℕ} {R : Finset ℕ}
    (square_threshold : z ≤ y / z)
    (fresh : Disjoint (fixedParameterCorePrimes y z) R) :
    (∏ p ∈ (fixedParameterCorePrimes y z) ∪ R,
      selectedPrimePower (fixedParameterCoreSquared y z) p) =
      primorial (y / z) * primorial z * ∏ p ∈ R, p := by
  rw [typedCore_actual_conductor_factor fresh,
    fixedParameterCore_actual_conductor square_threshold]

/-- Exact REAL logarithmic cost is the sum of the actual mixed core cost and
the genuine fresh prime product cost. -/
theorem typedCore_actual_log_conductor_add
    {y z : ℕ} {R : Finset ℕ}
    (reserve_primes : ∀ p ∈ R, p.Prime)
    (fresh : Disjoint (fixedParameterCorePrimes y z) R) :
    Real.log
      ((∏ p ∈ (fixedParameterCorePrimes y z) ∪ R,
        selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) =
      Real.log
        ((∏ p ∈ fixedParameterCorePrimes y z,
          selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) +
        Real.log ((∏ p ∈ R, p : ℕ) : ℝ) := by
  rw [typedCore_actual_conductor_factor fresh]
  push_cast
  apply Real.log_mul
  · have positive : 0 <
        ∏ p ∈ fixedParameterCorePrimes y z,
          selectedPrimePower (fixedParameterCoreSquared y z) p := by
      apply Finset.prod_pos
      intro p hp
      exact pow_pos (fixedParameterCorePrimes_prime y z p hp).pos _
    exact_mod_cast positive.ne'
  · have real_positive : (0 : ℝ) < ∏ p ∈ R, (p : ℝ) := by
      apply Finset.prod_pos
      intro p hp
      exact_mod_cast (reserve_primes p hp).pos
    exact real_positive.ne'

/-- The sole remaining analytic input in exact fixed-parameter form.  For
every requested cost density, select a FIXED positive `z` with `1/z` already
smaller than that density, and then, for every sufficiently large `y`, find
fresh distinct genuine prime labels with one coherent residue each that
repair the exact four typed target families at the stated total prime cost.

Importantly this does NOT claim little-oh cost in `y` for each fixed `z`;
the parameter `z` is chosen before taking `y` to infinity. -/
def HasSublinearTypedCoreMatchings : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ z : ℕ, 0 < z ∧ (z : ℝ)⁻¹ < ε ∧
      ∀ᶠ y : ℕ in atTop,
        ∃ (R : Finset ℕ) (b : ℕ → ℕ),
          (∀ p ∈ R, p.Prime) ∧
          Disjoint (fixedParameterCorePrimes y z) R ∧
          (∀ h ∈ Finset.Icc 1 y,
            FixedParameterCoreDeficientType y z h →
              2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h) ∧
          Real.log ((∏ p ∈ R, p : ℕ) : ℝ) ≤ ε * (y : ℝ)

/-- The exact typed-target prime matching hypothesis discharges the entire
actual-conductor sparse-cover obstruction; the old core contribution is
already unconditional by the prime number theorem. -/
theorem sublinear_unrestricted_conductors_of_typed_core_matchings
    (matchings : HasSublinearTypedCoreMatchings) :
    HasSublinearUnrestrictedConductorCovers := by
  intro ε positive Y₀
  let δ : ℝ := ε / 4
  have δpositive : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨z, zpositive, inverse_small, eventual_matching⟩ :=
    matchings δ δpositive
  have core_ratio := fixedParameterCore_actual_log_ratio_tendsto z zpositive
  have ratio_bound : (z : ℝ)⁻¹ < 2 * δ := by linarith
  have eventual_core : ∀ᶠ y : ℕ in atTop,
      Real.log
        ((∏ p ∈ fixedParameterCorePrimes y z,
          selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) /
        (y : ℝ) < 2 * δ :=
    (tendsto_order.mp core_ratio).2 (2 * δ) ratio_bound
  have eventual_threshold : ∀ᶠ y : ℕ in atTop, z ≤ y / z :=
    (Nat.tendsto_div_const_atTop zpositive.ne').eventually
      (eventually_ge_atTop z)
  have all_data : ∀ᶠ y : ℕ in atTop,
      Y₀ ≤ y ∧ 0 < y ∧ z ≤ y / z ∧
      Real.log
        ((∏ p ∈ fixedParameterCorePrimes y z,
          selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) /
        (y : ℝ) < 2 * δ ∧
      (∃ (R : Finset ℕ) (b : ℕ → ℕ),
        (∀ p ∈ R, p.Prime) ∧
        Disjoint (fixedParameterCorePrimes y z) R ∧
        (∀ h ∈ Finset.Icc 1 y,
          FixedParameterCoreDeficientType y z h →
            2 ≤ fixedParameterCoreHits y z h + typedCoreFreshHits R b h) ∧
        Real.log ((∏ p ∈ R, p : ℕ) : ℝ) ≤ δ * (y : ℝ)) := by
    filter_upwards [eventually_ge_atTop Y₀, eventually_gt_atTop 0,
      eventual_threshold, eventual_core, eventual_matching]
        with y large positive_y threshold ratio matching
    exact ⟨large, positive_y, threshold, ratio, matching⟩
  obtain ⟨y, large, positive_y, threshold, ratio,
    R, b, reserve_primes, fresh, matching, reserve_cost⟩ := all_data.exists
  let P := (fixedParameterCorePrimes y z) ∪ R
  let squared := fixedParameterCoreSquared y z
  let residue := typedCoreGluedResidue y z b
  have cover : UnrestrictedPrimeSquareDoubleCover y P squared residue :=
    typedCore_complete_cover_of_matching zpositive threshold
      reserve_primes fresh matching
  refine ⟨y, P, squared, residue, large, cover, ?_⟩
  have yreal : (0 : ℝ) < y := by exact_mod_cast positive_y
  have core_cost :
      Real.log
        ((∏ p ∈ fixedParameterCorePrimes y z,
          selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ)
        < (2 * δ) * (y : ℝ) :=
    (div_lt_iff₀ yreal).mp ratio
  change Real.log
    ((∏ p ∈ (fixedParameterCorePrimes y z) ∪ R,
      selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ)
      ≤ ε * (y : ℝ)
  rw [typedCore_actual_log_conductor_add reserve_primes fresh]
  dsimp [δ] at core_cost reserve_cost
  nlinarith

/-- One exact, honest, explicit remaining analytic matching proposition
implies the literal original historical Erdős #1139 infinite-limsup target.
The proposition is a HYPOTHESIS, not a proved full solution. -/
theorem original_normalized_limsup_top_of_typed_core_matchings
    (matchings : HasSublinearTypedCoreMatchings) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_sublinear_unrestricted_conductors
    (sublinear_unrestricted_conductors_of_typed_core_matchings matchings)


end Erdos1139
