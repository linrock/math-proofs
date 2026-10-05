module

public import TypedCoreMatchingBridge1139

@[expose] public section


/-!
# Coherent residue averaging and deterministic alteration for Erdős #1139

One fixed bundle of several targets generally determines its large prime
label, so matching such bundles to labels by Hall does not itself construct
the required prime patterns. This file uses the opposite quantifier order:
first fix the genuinely distinct prime labels, then average over complete,
globally coherent choices of ONE residue for each label.

The actual one-or-two-hit deficit is averaged target by target. A finite
first-moment argument selects a single deterministic assignment with small
total residual deficit, and the independently proved fresh-prime cleanup
repairs the remaining targets with its exact real logarithmic conductor cost.

There is no fractional hypergraph matching, Kahn input, Hall-expansion
assumption, second-moment assumption, mathematical axiom, or placeholder.
The actual first-moment prime-pattern construction remains an explicit
unproved analytic hypothesis; therefore no unconditional solution of #1139
is claimed.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Exact residual multiplicity of one target after choosing a single
coherent broad residue for every genuinely distinct fresh prime label. -/
def typedCoreMissingHits
    (y z : ℕ) (R : Finset ℕ) (b : ℕ → ℕ) (h : ℕ) : ℕ :=
  2 - (fixedParameterCoreHits y z h + typedCoreFreshHits R b h)

/-- Total actual heterogeneous missing-hit demand, retaining the closed
historical interval and charging a prime target twice when neither hit has
been supplied. -/
def typedCoreMissingHitTotal
    (y z : ℕ) (R : Finset ℕ) (b : ℕ → ℕ) : ℕ :=
  ∑ h ∈ Finset.Icc 1 y, typedCoreMissingHits y z R b h

/-- The literal deficient-target set of the actual partially selected mixed
conductor is precisely the set with positive heterogeneous residual demand. -/
theorem typedCore_deficientTargets_eq_missing_hit_filter
    {y z : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (fresh : Disjoint (fixedParameterCorePrimes y z) R) :
    deficientTargets y
        ((fixedParameterCorePrimes y z) ∪ R)
        (fixedParameterCoreSquared y z)
        (typedCoreGluedResidue y z b) =
      (Finset.Icc 1 y).filter
        fun h => 0 < typedCoreMissingHits y z R b h := by
  classical
  ext h
  simp only [deficientTargets, Finset.mem_filter]
  rw [typedCore_total_hits_eq fresh]
  unfold typedCoreMissingHits
  constructor
  · rintro ⟨interval, deficit⟩
    exact ⟨interval, by omega⟩
  · rintro ⟨interval, deficit⟩
    exact ⟨interval, by omega⟩

/-- Each actual deficient target consumes at least one residual hit; the
total heterogeneous slot deficit therefore bounds the deficient-target count
without replacing its one-hit and two-hit demands by a fictitious uniform
target type. -/
theorem typedCore_deficientTargets_card_le_missing_hit_total
    {y z : ℕ} {R : Finset ℕ} {b : ℕ → ℕ}
    (fresh : Disjoint (fixedParameterCorePrimes y z) R) :
    (deficientTargets y
      ((fixedParameterCorePrimes y z) ∪ R)
      (fixedParameterCoreSquared y z)
      (typedCoreGluedResidue y z b)).card ≤
      typedCoreMissingHitTotal y z R b := by
  classical
  rw [typedCore_deficientTargets_eq_missing_hit_filter fresh]
  unfold typedCoreMissingHitTotal
  calc
    ((Finset.Icc 1 y).filter
      fun h => 0 < typedCoreMissingHits y z R b h).card =
        ∑ h ∈ (Finset.Icc 1 y).filter
          (fun h => 0 < typedCoreMissingHits y z R b h), 1 :=
      Finset.card_eq_sum_ones _
    _ ≤ ∑ h ∈ (Finset.Icc 1 y).filter
          (fun h => 0 < typedCoreMissingHits y z R b h),
            typedCoreMissingHits y z R b h := by
      apply Finset.sum_le_sum
      intro h selected
      exact (Finset.mem_filter.mp selected).2
    _ ≤ ∑ h ∈ Finset.Icc 1 y, typedCoreMissingHits y z R b h := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

/-- Exact finite first-moment identity. The sample variable indexes COMPLETE
residue assignments, so every label has one globally coherent residue in
each sample; no independently chosen residue for each target is allowed. -/
theorem typedCore_missing_hit_first_moment_identity
    (y z k : ℕ) (R : Finset ℕ)
    (samples : Fin k → ℕ → ℕ) :
    (∑ i : Fin k, typedCoreMissingHitTotal y z R (samples i)) =
      ∑ h ∈ Finset.Icc 1 y,
        ∑ i : Fin k, typedCoreMissingHits y z R (samples i) h := by
  classical
  unfold typedCoreMissingHitTotal
  rw [Finset.sum_comm]

/-- Finite averaging chooses one actual complete label-residue assignment
whose total heterogeneous deficit is at most the advertised integer budget.
Only a FIRST-MOMENT bound is required. -/
theorem exists_typedCore_assignment_of_missing_hit_first_moment
    {y z k D : ℕ} {R : Finset ℕ}
    (samples : Fin k → ℕ → ℕ)
    (nonempty : 0 < k)
    (first_moment :
      (∑ h ∈ Finset.Icc 1 y,
        ∑ i : Fin k, typedCoreMissingHits y z R (samples i) h) ≤
          k * D) :
    ∃ i : Fin k, typedCoreMissingHitTotal y z R (samples i) ≤ D := by
  classical
  rw [← typedCore_missing_hit_first_moment_identity] at first_moment
  by_contra absent
  have pointwise : ∀ i : Fin k,
      D + 1 ≤ typedCoreMissingHitTotal y z R (samples i) := by
    intro i
    have not_small : ¬ typedCoreMissingHitTotal y z R (samples i) ≤ D := by
      intro small
      exact absent ⟨i, small⟩
    omega
  have lower :
      (∑ _i : Fin k, (D + 1)) ≤
        ∑ i : Fin k, typedCoreMissingHitTotal y z R (samples i) := by
    exact Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => pointwise i)
  have lower' :
      k * (D + 1) ≤
        ∑ i : Fin k, typedCoreMissingHitTotal y z R (samples i) := by
    simpa using lower
  rw [Nat.mul_add, Nat.mul_one] at lower'
  omega

/-- A coherent finite first-moment estimate plus an ordinary numeric supply of
fresh cleanup primes constructs an ACTUAL complete mixed prime-square cover.
The conductor is the exact old core conductor plus the exact selected-label
logarithm and at most twice the residual-slot budget times the actual cleanup
prime logarithm. No Hall or hypergraph theorem is used. -/
theorem typedCore_complete_cover_of_missing_hit_first_moment
    {y z k D B : ℕ} {R : Finset ℕ}
    (samples : Fin k → ℕ → ℕ)
    (nonempty : 0 < k)
    (reserve_primes : ∀ p ∈ R, p.Prime)
    (fresh : Disjoint (fixedParameterCorePrimes y z) R)
    (cleanup_bound_positive : 1 ≤ B)
    (cleanup_supply :
      2 * D + ((fixedParameterCorePrimes y z) ∪ R).card ≤
        Nat.primeCounting B)
    (first_moment :
      (∑ h ∈ Finset.Icc 1 y,
        ∑ i : Fin k, typedCoreMissingHits y z R (samples i) h) ≤
          k * D) :
    ∃ (completed squared : Finset ℕ) (residue : ℕ → ℕ),
      UnrestrictedPrimeSquareDoubleCover y completed squared residue ∧
      Real.log
        ((∏ p ∈ completed, selectedPrimePower squared p : ℕ) : ℝ) ≤
        Real.log
          ((∏ p ∈ fixedParameterCorePrimes y z,
            selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) +
          Real.log ((∏ p ∈ R, p : ℕ) : ℝ) +
          (2 * (D : ℝ)) * Real.log (B : ℝ) := by
  classical
  obtain ⟨i, deficit⟩ :=
    exists_typedCore_assignment_of_missing_hit_first_moment
      samples nonempty first_moment
  let P := (fixedParameterCorePrimes y z) ∪ R
  let squared := fixedParameterCoreSquared y z
  let assignment := typedCoreGluedResidue y z (samples i)
  have core_primes : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with core | selected
    · exact fixedParameterCorePrimes_prime y z p core
    · exact reserve_primes p selected
  have square_support : squared ⊆ P := by
    intro p hp
    exact Finset.mem_union_left R
      (fixedParameterCoreSquared_subset y z hp)
  have target_budget :
      (deficientTargets y P squared assignment).card ≤ D :=
    (typedCore_deficientTargets_card_le_missing_hit_total fresh).trans deficit
  have actual_supply :
      2 * (deficientTargets y P squared assignment).card + P.card ≤
        Nat.primeCounting B := by
    change 2 * D + P.card ≤ Nat.primeCounting B at cleanup_supply
    omega
  obtain ⟨completed, residue, cover, _support, _cardinality, cost⟩ :=
    complete_partial_core_of_primeCounting
      y P squared assignment B core_primes square_support actual_supply
  refine ⟨completed, squared, residue, cover, ?_⟩
  have log_nonnegative : 0 ≤ Real.log (B : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast cleanup_bound_positive
  have cleanup_cost :
      (2 * ((deficientTargets y P squared assignment).card : ℝ)) *
          Real.log (B : ℝ) ≤
        (2 * (D : ℝ)) * Real.log (B : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ log_nonnegative
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast target_budget) (by positivity)
  calc
    Real.log
        ((∏ p ∈ completed, selectedPrimePower squared p : ℕ) : ℝ) ≤
      Real.log ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ) +
        (2 * ((deficientTargets y P squared assignment).card : ℝ)) *
          Real.log (B : ℝ) := cost
    _ ≤ Real.log
          ((∏ p ∈ fixedParameterCorePrimes y z,
            selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) +
          Real.log ((∏ p ∈ R, p : ℕ) : ℝ) +
          (2 * (D : ℝ)) * Real.log (B : ℝ) := by
      dsimp [P, squared]
      rw [typedCore_actual_log_conductor_add reserve_primes fresh]
      dsimp [P, squared] at cleanup_cost
      linarith

/-- Sole analytic input for the first-moment/alteration route. For each fixed
accuracy, one first fixes the genuine core parameter; for all sufficiently
large interval lengths one then supplies distinct actual prime labels, a
NONEMPTY finite ensemble of complete coherent residue assignments, a
pointwise-summed first-moment bound for the genuine one/two-hit deficit,
sufficient fresh cleanup primes, and the exact selected-plus-cleanup cost.

No fractional matching, Hall expansion, second-moment, or prime-pattern
theorem is hidden in this proposition. Its truth is not established here. -/
def HasSublinearAveragedTypedCoreData : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ z : ℕ, 0 < z ∧ (z : ℝ)⁻¹ < ε ∧
      ∀ᶠ y : ℕ in atTop,
        ∃ (R : Finset ℕ) (B D k : ℕ)
          (samples : Fin k → ℕ → ℕ),
          (∀ p ∈ R, p.Prime) ∧
          Disjoint (fixedParameterCorePrimes y z) R ∧
          1 ≤ B ∧ 0 < k ∧
          2 * D + ((fixedParameterCorePrimes y z) ∪ R).card ≤
            Nat.primeCounting B ∧
          (∑ h ∈ Finset.Icc 1 y,
            ∑ i : Fin k, typedCoreMissingHits y z R (samples i) h) ≤
              k * D ∧
          Real.log ((∏ p ∈ R, p : ℕ) : ℝ) +
            (2 * (D : ℝ)) * Real.log (B : ℝ) ≤ ε * (y : ℝ)

/-- The finite first-moment construction and fully charged deterministic
alteration discharge the exact unrestricted sparse-conductor obstruction.
The fixed-parameter core cost is already an unconditional formal PNT theorem.
No matching/rounding theorem is required in this reduction. -/
theorem sublinear_unrestricted_conductors_of_averaged_typed_core_data
    (averaged : HasSublinearAveragedTypedCoreData) :
    HasSublinearUnrestrictedConductorCovers := by
  intro ε positive Y₀
  let δ : ℝ := ε / 4
  have δpositive : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨z, zpositive, inverse_small, eventual_data⟩ :=
    averaged δ δpositive
  have core_ratio := fixedParameterCore_actual_log_ratio_tendsto z zpositive
  have ratio_bound : (z : ℝ)⁻¹ < 2 * δ := by linarith
  have eventual_core : ∀ᶠ y : ℕ in atTop,
      Real.log
        ((∏ p ∈ fixedParameterCorePrimes y z,
          selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) /
        (y : ℝ) < 2 * δ :=
    (tendsto_order.mp core_ratio).2 (2 * δ) ratio_bound
  have all_data : ∀ᶠ y : ℕ in atTop,
      Y₀ ≤ y ∧ 0 < y ∧
      Real.log
        ((∏ p ∈ fixedParameterCorePrimes y z,
          selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) /
        (y : ℝ) < 2 * δ ∧
      (∃ (R : Finset ℕ) (B D k : ℕ)
        (samples : Fin k → ℕ → ℕ),
        (∀ p ∈ R, p.Prime) ∧
        Disjoint (fixedParameterCorePrimes y z) R ∧
        1 ≤ B ∧ 0 < k ∧
        2 * D + ((fixedParameterCorePrimes y z) ∪ R).card ≤
          Nat.primeCounting B ∧
        (∑ h ∈ Finset.Icc 1 y,
          ∑ i : Fin k, typedCoreMissingHits y z R (samples i) h) ≤
            k * D ∧
        Real.log ((∏ p ∈ R, p : ℕ) : ℝ) +
          (2 * (D : ℝ)) * Real.log (B : ℝ) ≤ δ * (y : ℝ)) := by
    filter_upwards [eventually_ge_atTop Y₀, eventually_gt_atTop 0,
      eventual_core, eventual_data] with y large positive_y ratio data
    exact ⟨large, positive_y, ratio, data⟩
  obtain ⟨y, large, positive_y, ratio,
    R, B, D, k, samples, reserve_primes, fresh, Bpositive,
      nonempty, supply, first_moment, auxiliary_cost⟩ := all_data.exists
  obtain ⟨completed, squared, residue, cover, conductor⟩ :=
    typedCore_complete_cover_of_missing_hit_first_moment
      samples nonempty reserve_primes fresh Bpositive supply first_moment
  refine ⟨y, completed, squared, residue, large, cover, ?_⟩
  have yreal : (0 : ℝ) < y := by exact_mod_cast positive_y
  have core_cost :
      Real.log
        ((∏ p ∈ fixedParameterCorePrimes y z,
          selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) <
          (2 * δ) * (y : ℝ) :=
    (div_lt_iff₀ yreal).mp ratio
  dsimp [δ] at core_cost auxiliary_cost
  nlinarith

/-- Exact original historical infinite-limsup consequence of the sole
explicit coherent first-moment prime-pattern hypothesis. This is a
CONDITIONAL theorem: the requisite finite sample ensembles and quantitative
first-moment estimate have not been proved unconditionally. -/
theorem original_normalized_limsup_top_of_averaged_typed_core_data
    (averaged : HasSublinearAveragedTypedCoreData) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_sublinear_unrestricted_conductors
    (sublinear_unrestricted_conductors_of_averaged_typed_core_data averaged)


end Erdos1139
