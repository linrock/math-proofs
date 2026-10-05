module

public import ActualMajorArcWeightedBridge433
public import ShiftedMajorArcDedup433

@[expose] public section


/-!
# Exact original weighted-pattern assembly over deduplicated major centers

The manuscript quantity is the actual robust-residue, coefficient-summed
three-prime weight. Its shifted major arcs contain duplicate rational centers
and cannot be summed over raw anchor/character indices. Combining the two
independently proved finite bridges gives its exact decomposition into genuine
distinct-center interval integrals plus its genuine prime-only shifted minor.
Every original edge endpoint, support-unit selector, robust residue, and
strict/weak real strip is retained.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The complete genuine original coefficient-summed major mass, indexed by
distinct actual translated rational centers, with no duplicate-anchor
overcount and no discarded prime/support selector. -/
noncomputable def actualDeduplicatedMajorPrimeMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue P Q : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ s ∈ S, s).divisors,
    ∑ d ∈ (∏ s ∈ S, s).divisors,
      ∑ c ∈ shiftedFareyCenterClasses (∏ s ∈ S, s)
          (actualShiftedFareyAnchors (∏ s ∈ S, s) P),
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            shiftedFareyCenterRegion (∏ s ∈ S, s) Q
              (actualShiftedFareyAnchors (∏ s ∈ S, s) P) c,
          actualMajorArcPrimeCubic
            S b n J residue a d τ ell α).re

/-- The complete genuine original coefficient-summed prime-only shifted
minor contribution, retaining all manuscript filters. -/
noncomputable def actualShiftedMinorPrimeMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue P Q : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ s ∈ S, s).divisors,
    ∑ d ∈ (∏ s ∈ S, s).divisors,
      (∫ α in ternaryShiftedMinorArcs (∏ s ∈ S, s) P Q,
        actualMajorArcPrimeCubic
          S b n J residue a d τ ell α).re

/-- Exact equality for the ORIGINAL robust-residue weighted manuscript count,
the whole deduplicated rational-center major mass, and its actual prime-only
shifted minor. No principal-only, unweighted, selector-free, or
coefficient-free substitute occurs anywhere in the equality. -/
theorem manuscriptWeightedResidueCount_eq_actual_deduplicated_major_minor
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue P Q : ℕ) (τ ell : ℝ)
    (hW : 0 < ∏ s ∈ S, s) (hP : 0 < P)
    (hPQ : 2 * ((∏ s ∈ S, s) * P) ^ 2 < Q + 1)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell) :
    manuscriptWeightedResidueCount S b n J τ ell residue =
      actualDeduplicatedMajorPrimeMass S b n J residue P Q τ ell +
        actualShiftedMinorPrimeMass S b n J residue P Q τ ell := by
  rw [manuscriptWeightedResidueCount_eq_actual_shifted_major_minor_sum
    S b n J residue P Q τ ell hτ hell]
  unfold actualDeduplicatedMajorPrimeMass actualShiftedMinorPrimeMass
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  rw [ternaryShiftedMajorRegion_integral_eq_actual_center_sum
    (∏ s ∈ S, s) P Q hW hP hPQ
    (actualMajorArcPrimeCubic S b n J residue a d τ ell)
    (actualMajorArcPrimeCubic_continuous S b n J residue a d τ ell)]
  simp

/-- At every sufficiently large original endpoint, the real manuscript
weighted residue count has its exact center-major/minor decomposition for
the genuinely compatible `P=floor(log n)^12`, `Q=floor(lower(n)/P)`.
The residue and both real strip parameters remain the original ones. -/
theorem manuscriptWeightedResidueCount_actual_center_assembly_eventually
    (S : Finset ℕ) (b : ℕ → ℕ)
    (J residue : ℕ) (τ ell κ : ℝ) (lower : ℕ → ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell)
    (hκ : 0 < κ)
    (hlinear : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      manuscriptWeightedResidueCount S b n J τ ell residue =
        actualDeduplicatedMajorPrimeMass S b n J residue
          (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff lower n) τ ell +
        actualShiftedMinorPrimeMass S b n J residue
          (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff lower n) τ ell := by
  have hW : 0 < ∏ s ∈ S, s :=
    Finset.prod_pos fun s hs => (hsupport s hs).pos
  filter_upwards
    [fullyCompatibleFareyCutoff_merged_disjoint_eventually
      lower κ hκ hlinear (∏ s ∈ S, s),
      (tendsto_atTop.1 compatibleLogMinorCutoff_tendsto_atTop 1)]
      with n hseparation hcutoff
  exact manuscriptWeightedResidueCount_eq_actual_deduplicated_major_minor
    S b n J residue (compatibleLogMinorCutoff n)
      (fullyCompatibleFareyCutoff lower n) τ ell
      hW hcutoff hseparation hτ hell

/-- Any quantitative lower bound for the genuine deduplicated major mass
transfers to the ORIGINAL weighted residue count with exactly the actual
prime-only shifted-minor error. The major positivity remains an explicit
mathematical hypothesis and is not smuggled into the proof. -/
theorem manuscriptWeightedResidueCount_lower_of_deduplicated_major_and_minor
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue P Q : ℕ) (τ ell B E : ℝ)
    (hW : 0 < ∏ s ∈ S, s) (hP : 0 < P)
    (hPQ : 2 * ((∏ s ∈ S, s) * P) ^ 2 < Q + 1)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell)
    (hmajor : B ≤ actualDeduplicatedMajorPrimeMass
      S b n J residue P Q τ ell)
    (hminor : |actualShiftedMinorPrimeMass
      S b n J residue P Q τ ell| ≤ E) :
    B - E ≤ manuscriptWeightedResidueCount S b n J τ ell residue := by
  rw [manuscriptWeightedResidueCount_eq_actual_deduplicated_major_minor
    S b n J residue P Q τ ell hW hP hPQ hτ hell]
  have hnegative := (abs_le.mp hminor).1
  linarith

end Erdos689

