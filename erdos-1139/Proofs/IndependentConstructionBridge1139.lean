module

public import IndependentRounding1139

@[expose] public section


/-!
# Disjoint independent prime colors imply genuine mixed covers

The two prime-label colors are rounded SEPARATELY.  Each color's exact
exponential marginal budget selects one globally coherent residue assignment;
disjointness then glues the assignments without reusing a prime label.

Prime targets can demand both colors, semiprime targets can demand just one,
and an explicitly charged exceptional target can demand two cleanup hits.
The output is an ACTUAL prime/squared-prime cover with its full old-core,
selected-label, and reserve-prime logarithmic conductor charge.

No matching theorem, hypergraph axiom, probabilistic axiom, or unproved
analytic theorem is used.  Any asymptotic prime-pattern supply remains an
explicit hypothesis, not an unconditional solution of Erdős problem #1139.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- Glue two globally coherent residue functions on disjoint label colors;
each low label keeps its low assignment and every other label uses high. -/
def independentTwoColorGluedResidue
    (low : Finset ℕ) (lowResidue highResidue : ℕ → ℕ)
    (p : ℕ) : ℕ :=
  if p ∈ low then lowResidue p else highResidue p

/-- Gluing preserves every actual low-color fresh-prime incidence. -/
theorem typedCoreFreshHits_independentTwoColorGlued_low
    (low : Finset ℕ) (lowResidue highResidue : ℕ → ℕ) (h : ℕ) :
    typedCoreFreshHits low
      (independentTwoColorGluedResidue low lowResidue highResidue) h =
        typedCoreFreshHits low lowResidue h := by
  classical
  unfold typedCoreFreshHits
  congr 1
  ext p
  simp only [Finset.mem_filter]
  by_cases selected : p ∈ low
  · simp [independentTwoColorGluedResidue, selected]
  · simp [selected]

/-- Disjointness is essential: gluing also preserves every actual high-color
fresh-prime incidence precisely because no high label belongs to low. -/
theorem typedCoreFreshHits_independentTwoColorGlued_high
    (low high : Finset ℕ) (lowResidue highResidue : ℕ → ℕ)
    (h : ℕ) (disjoint : Disjoint low high) :
    typedCoreFreshHits high
      (independentTwoColorGluedResidue low lowResidue highResidue) h =
        typedCoreFreshHits high highResidue h := by
  classical
  unfold typedCoreFreshHits
  congr 1
  ext p
  simp only [Finset.mem_filter]
  by_cases selected : p ∈ high
  · have outside : p ∉ low := by
      intro also_low
      exact Finset.disjoint_left.mp disjoint also_low selected
    simp [independentTwoColorGluedResidue, selected, outside]
  · simp [selected]

/-- A supported target mask sums exactly over the advertised target set. -/
theorem independentTwoColor_mask_sum_eq
    (interval targets : Finset ℕ) (f : ℕ → ℕ)
    (supported : targets ⊆ interval) :
    (∑ h ∈ interval, if h ∈ targets then f h else 0) =
      ∑ h ∈ targets, f h := by
  classical
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr supported]

/-- The actual heterogeneous slot deficit is bounded by the two separately
rounded color misses, plus two fully charged slots for an exceptional target.
The explicit demand condition allows a prime to demand both colors and a
semiprime with one old-core hit to demand just its designated color. -/
theorem independentTwoColor_missing_hits_le_classified_indicators
    {y z h : ℕ} (low high lowTargets highTargets exceptions : Finset ℕ)
    (lowResidue highResidue : ℕ → ℕ)
    (disjoint : Disjoint low high)
    (demand : h ∉ exceptions →
      2 ≤ fixedParameterCoreHits y z h +
        (if h ∈ lowTargets then 1 else 0) +
        (if h ∈ highTargets then 1 else 0)) :
    typedCoreMissingHits y z (low ∪ high)
      (independentTwoColorGluedResidue low lowResidue highResidue) h ≤
      (if h ∈ exceptions then 2 else 0) +
        (if h ∈ lowTargets then
          independentColorMissingHit low lowResidue h else 0) +
        (if h ∈ highTargets then
          independentColorMissingHit high highResidue h else 0) := by
  classical
  by_cases exceptional : h ∈ exceptions
  · simp [exceptional]
    unfold typedCoreMissingHits
    omega
  · have required := demand exceptional
    unfold typedCoreMissingHits
    rw [typedCoreFreshHits_union_of_disjoint low high _ h disjoint,
      typedCoreFreshHits_independentTwoColorGlued_low,
      typedCoreFreshHits_independentTwoColorGlued_high
        low high lowResidue highResidue h disjoint]
    unfold independentColorMissingHit
    by_cases in_low : h ∈ lowTargets <;>
      by_cases in_high : h ∈ highTargets <;>
      simp [exceptional, in_low, in_high] at required ⊢ <;>
      (try split_ifs) <;> omega

/-- Sum the exact two-color pointwise bound without mistaking prime targets
for one-hit semiprimes or dropping the factor two for exceptional cleanup. -/
theorem independentTwoColor_missing_hit_total_le
    {y z : ℕ} (low high lowTargets highTargets exceptions : Finset ℕ)
    (lowResidue highResidue : ℕ → ℕ)
    (disjoint : Disjoint low high)
    (low_supported : lowTargets ⊆ Finset.Icc 1 y)
    (high_supported : highTargets ⊆ Finset.Icc 1 y)
    (exceptions_supported : exceptions ⊆ Finset.Icc 1 y)
    (demand : ∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
      2 ≤ fixedParameterCoreHits y z h +
        (if h ∈ lowTargets then 1 else 0) +
        (if h ∈ highTargets then 1 else 0)) :
    typedCoreMissingHitTotal y z (low ∪ high)
      (independentTwoColorGluedResidue low lowResidue highResidue) ≤
      2 * exceptions.card +
        (∑ h ∈ lowTargets,
          independentColorMissingHit low lowResidue h) +
        (∑ h ∈ highTargets,
          independentColorMissingHit high highResidue h) := by
  classical
  unfold typedCoreMissingHitTotal
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 y,
        ((if h ∈ exceptions then 2 else 0) +
          (if h ∈ lowTargets then
            independentColorMissingHit low lowResidue h else 0) +
          (if h ∈ highTargets then
            independentColorMissingHit high highResidue h else 0)) := by
      apply Finset.sum_le_sum
      intro h selected
      exact independentTwoColor_missing_hits_le_classified_indicators
        low high lowTargets highTargets exceptions
        lowResidue highResidue disjoint (demand h selected)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        independentTwoColor_mask_sum_eq
          (Finset.Icc 1 y) exceptions (fun _ => 2) exceptions_supported,
        independentTwoColor_mask_sum_eq
          (Finset.Icc 1 y) lowTargets
          (independentColorMissingHit low lowResidue) low_supported,
        independentTwoColor_mask_sum_eq
          (Finset.Icc 1 y) highTargets
          (independentColorMissingHit high highResidue) high_supported]
      simp [Nat.mul_comm]

/-- Two separate finite exponential budgets select one ACTUAL globally
coherent glued residue assignment whose genuine heterogeneous total deficit
is bounded by both budgets and the twice-charged exceptional targets. -/
theorem exists_independentTwoColor_assignment_of_exp_budgets
    {y z kLow kHigh DLow DHigh : ℕ}
    (low high lowTargets highTargets exceptions : Finset ℕ)
    (lowOptions : ↥low → Fin kLow → ℕ)
    (highOptions : ↥high → Fin kHigh → ℕ)
    (low_nonempty : 0 < kLow) (high_nonempty : 0 < kHigh)
    (disjoint : Disjoint low high)
    (low_supported : lowTargets ⊆ Finset.Icc 1 y)
    (high_supported : highTargets ⊆ Finset.Icc 1 y)
    (exceptions_supported : exceptions ⊆ Finset.Icc 1 y)
    (demand : ∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
      2 ≤ fixedParameterCoreHits y z h +
        (if h ∈ lowTargets then 1 else 0) +
        (if h ∈ highTargets then 1 else 0))
    (low_budget :
      (∑ h ∈ lowTargets, Real.exp (-(∑ p : ↥low,
        independentResidueHitFraction low lowOptions h p))) ≤ (DLow : ℝ))
    (high_budget :
      (∑ h ∈ highTargets, Real.exp (-(∑ p : ↥high,
        independentResidueHitFraction high highOptions h p))) ≤ (DHigh : ℝ)) :
    ∃ residue : ℕ → ℕ,
      typedCoreMissingHitTotal y z (low ∪ high) residue ≤
        DLow + DHigh + 2 * exceptions.card := by
  obtain ⟨iLow, low_misses⟩ :=
    exists_independentResidueSample_with_missing_targets_le_of_exp_budget
      low_nonempty low lowOptions lowTargets low_budget
  obtain ⟨iHigh, high_misses⟩ :=
    exists_independentResidueSample_with_missing_targets_le_of_exp_budget
      high_nonempty high highOptions highTargets high_budget
  let lowResidue := independentResidueSamples low lowOptions iLow
  let highResidue := independentResidueSamples high highOptions iHigh
  refine ⟨independentTwoColorGluedResidue low lowResidue highResidue, ?_⟩
  have total := independentTwoColor_missing_hit_total_le
    low high lowTargets highTargets exceptions lowResidue highResidue
      disjoint low_supported high_supported exceptions_supported demand
  change (∑ h ∈ lowTargets,
    independentColorMissingHit low lowResidue h) ≤ DLow at low_misses
  change (∑ h ∈ highTargets,
    independentColorMissingHit high highResidue h) ≤ DHigh at high_misses
  omega

/-- Exact FINITE end-to-end two-color independent rounding and deterministic
alteration: actual distinct prime labels, genuine reserve-prime availability,
all prime-versus-semiprime demand, twice-charged exceptional slots, and the
full real logarithmic conductor ledger.  No hypergraph matching is used. -/
theorem independentTwoColor_complete_cover_of_exp_budgets
    {y z kLow kHigh DLow DHigh B : ℕ}
    (low high lowTargets highTargets exceptions : Finset ℕ)
    (lowOptions : ↥low → Fin kLow → ℕ)
    (highOptions : ↥high → Fin kHigh → ℕ)
    (low_nonempty : 0 < kLow) (high_nonempty : 0 < kHigh)
    (disjoint : Disjoint low high)
    (low_supported : lowTargets ⊆ Finset.Icc 1 y)
    (high_supported : highTargets ⊆ Finset.Icc 1 y)
    (exceptions_supported : exceptions ⊆ Finset.Icc 1 y)
    (demand : ∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
      2 ≤ fixedParameterCoreHits y z h +
        (if h ∈ lowTargets then 1 else 0) +
        (if h ∈ highTargets then 1 else 0))
    (low_budget :
      (∑ h ∈ lowTargets, Real.exp (-(∑ p : ↥low,
        independentResidueHitFraction low lowOptions h p))) ≤ (DLow : ℝ))
    (high_budget :
      (∑ h ∈ highTargets, Real.exp (-(∑ p : ↥high,
        independentResidueHitFraction high highOptions h p))) ≤ (DHigh : ℝ))
    (reserve_primes : ∀ p ∈ low ∪ high, p.Prime)
    (fresh : Disjoint (fixedParameterCorePrimes y z) (low ∪ high))
    (cleanup_bound_positive : 1 ≤ B)
    (cleanup_supply :
      2 * (DLow + DHigh + 2 * exceptions.card) +
        ((fixedParameterCorePrimes y z) ∪ (low ∪ high)).card ≤
          Nat.primeCounting B) :
    ∃ (completed squared : Finset ℕ) (residue : ℕ → ℕ),
      UnrestrictedPrimeSquareDoubleCover y completed squared residue ∧
      Real.log
        ((∏ p ∈ completed, selectedPrimePower squared p : ℕ) : ℝ) ≤
        Real.log
          ((∏ p ∈ fixedParameterCorePrimes y z,
            selectedPrimePower (fixedParameterCoreSquared y z) p : ℕ) : ℝ) +
          Real.log ((∏ p ∈ low ∪ high, p : ℕ) : ℝ) +
          (2 * ((DLow + DHigh + 2 * exceptions.card : ℕ) : ℝ)) *
            Real.log (B : ℝ) := by
  obtain ⟨assignment, deficit⟩ :=
    exists_independentTwoColor_assignment_of_exp_budgets
      low high lowTargets highTargets exceptions lowOptions highOptions
      low_nonempty high_nonempty disjoint low_supported high_supported
      exceptions_supported demand low_budget high_budget
  let samples : Fin 1 → ℕ → ℕ := fun _ => assignment
  apply typedCore_complete_cover_of_missing_hit_first_moment
    (D := DLow + DHigh + 2 * exceptions.card)
    (B := B) samples (by decide) reserve_primes fresh
      cleanup_bound_positive cleanup_supply
  simpa [samples, typedCoreMissingHitTotal] using deficit

/-- The sole explicit analytic input for the scale-adaptive independent
construction.  It asks ONLY for actual finite prime-label option lists,
their independently calculated exponential hit-marginal budgets, the exact
one-versus-two-hit target demand, genuine fresh-prime supply, and the fully
charged sublinear conductor ledger.

It does NOT assume a selected matching, a complete cover, an already
globally coherent residue assignment, a fractional hypergraph theorem, or a
probabilistic rounding result.  Its proposed verification requires the
unformalized fixed-parameter Green--Tao--Ziegler prime-pattern moments.
Thus this proposition itself remains UNPROVED in the local Lean development.
-/
def HasSublinearIndependentTwoColorMarginals : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ z : ℕ, 0 < z ∧ (z : ℝ)⁻¹ < ε ∧
      ∀ᶠ y : ℕ in atTop,
        ∃ (low high lowTargets highTargets exceptions : Finset ℕ)
          (kLow kHigh B DLow DHigh : ℕ)
          (lowOptions : ↥low → Fin kLow → ℕ)
          (highOptions : ↥high → Fin kHigh → ℕ),
          0 < kLow ∧ 0 < kHigh ∧ 1 ≤ B ∧
          Disjoint low high ∧
          (∀ p ∈ low ∪ high, p.Prime) ∧
          Disjoint (fixedParameterCorePrimes y z) (low ∪ high) ∧
          lowTargets ⊆ Finset.Icc 1 y ∧
          highTargets ⊆ Finset.Icc 1 y ∧
          exceptions ⊆ Finset.Icc 1 y ∧
          (∀ h ∈ Finset.Icc 1 y, h ∉ exceptions →
            2 ≤ fixedParameterCoreHits y z h +
              (if h ∈ lowTargets then 1 else 0) +
              (if h ∈ highTargets then 1 else 0)) ∧
          (∑ h ∈ lowTargets, Real.exp (-(∑ p : ↥low,
            independentResidueHitFraction low lowOptions h p))) ≤
              (DLow : ℝ) ∧
          (∑ h ∈ highTargets, Real.exp (-(∑ p : ↥high,
            independentResidueHitFraction high highOptions h p))) ≤
              (DHigh : ℝ) ∧
          2 * (DLow + DHigh + 2 * exceptions.card) +
            ((fixedParameterCorePrimes y z) ∪ (low ∪ high)).card ≤
              Nat.primeCounting B ∧
          Real.log ((∏ p ∈ low ∪ high, p : ℕ) : ℝ) +
            (2 * ((DLow + DHigh + 2 * exceptions.card : ℕ) : ℝ)) *
              Real.log (B : ℝ) ≤ ε * (y : ℝ)

/-- Two separate deterministic independent-rounding selections transform
the NONCIRCULAR analytic marginal-data premise into the exact pre-existing
coherent first-moment/alteration hypothesis, using a singleton ensemble.
No Hall, nibble, Kahn, or hypergraph theorem intervenes. -/
theorem averaged_typed_core_data_of_independent_two_color_marginals
    (marginals : HasSublinearIndependentTwoColorMarginals) :
    HasSublinearAveragedTypedCoreData := by
  intro ε positive
  obtain ⟨z, zpositive, inverse_small, eventual_data⟩ :=
    marginals ε positive
  refine ⟨z, zpositive, inverse_small, ?_⟩
  filter_upwards [eventual_data] with y data
  obtain ⟨low, high, lowTargets, highTargets, exceptions,
    kLow, kHigh, B, DLow, DHigh, lowOptions, highOptions,
    low_nonempty, high_nonempty, cleanup_positive, disjoint,
    reserve_primes, fresh, low_supported, high_supported,
    exceptions_supported, demand, low_budget, high_budget,
    cleanup_supply, auxiliary_cost⟩ := data
  obtain ⟨assignment, deficit⟩ :=
    exists_independentTwoColor_assignment_of_exp_budgets
      low high lowTargets highTargets exceptions lowOptions highOptions
      low_nonempty high_nonempty disjoint low_supported high_supported
      exceptions_supported demand low_budget high_budget
  refine ⟨low ∪ high, B, DLow + DHigh + 2 * exceptions.card, 1,
    (fun _ => assignment), reserve_primes, fresh, cleanup_positive,
    (by decide), cleanup_supply, ?_, auxiliary_cost⟩
  simpa [typedCoreMissingHitTotal] using deficit

/-- The exact unrestricted sublinear-conductor covering obstruction reduces
to the explicit fixed-parameter exponential prime-pattern marginal data. -/
theorem sublinear_unrestricted_conductors_of_independent_two_color_marginals
    (marginals : HasSublinearIndependentTwoColorMarginals) :
    HasSublinearUnrestrictedConductorCovers :=
  sublinear_unrestricted_conductors_of_averaged_typed_core_data
    (averaged_typed_core_data_of_independent_two_color_marginals marginals)

/-- CONDITIONAL exact historical Erdős #1139 theorem: explicit scale-adaptive
actual prime-pattern hit marginals imply the literal infinite normalized
limsup.  The sole antecedent is NOT proved here; it isolates the missing
Green--Tao--Ziegler analytic estimate without a Kahn/matching dependency. -/
theorem original_normalized_limsup_top_of_independent_two_color_marginals
    (marginals : HasSublinearIndependentTwoColorMarginals) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  original_normalized_limsup_top_of_averaged_typed_core_data
    (averaged_typed_core_data_of_independent_two_color_marginals marginals)


end Erdos1139
