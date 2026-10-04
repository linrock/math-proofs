module

public import ActualMajorArcPrimeMinor433
public import ActualMajorArcCenterAssembly433
public import ActualRightVertexFinalCovering433

@[expose] public section


/-!
# Original Erdős covering reduced to genuine rational-center positivity

All actual coefficient-summed prime-only shifted minors are already `o(n²)`;
the complete genuine shifted major region has an exact disjoint-center
decomposition; and the original right-vertex and prime-label graph degrees
are unconditional. This merged PNT/AP-and-Selberg module identifies the only
remaining analytic hypothesis with positivity of the EXPLICIT deduplicated
rational-center integral and proves the original covering implication from
that hypothesis plus the sole remaining fixed-left graph degree.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- For every fixed genuine support and real positive strip location, the
entire actual shifted-major coefficient integral equals its exact finite
deduplicated-center sum at every sufficiently large original endpoint,
simultaneously for all label residues. -/
theorem actualMajorArcCoefficientMajorIntegral_eq_center_mass_eventually
    (S : Finset ℕ) (b : ℕ → ℕ)
    (J : ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ residue : ℕ,
        actualMajorArcCoefficientMajorIntegral
          S b n J residue τ ell =
        actualDeduplicatedMajorPrimeMass S b n J residue
          (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff
            (fun m => Nat.floor (τ * (m : ℝ))) n)
          τ ell := by
  have hW : 0 < ∏ s ∈ S, s :=
    Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hlinear := actualMajorArc_real_lower_floor_eventually_linear τ hτ
  filter_upwards
    [fullyCompatibleFareyCutoff_merged_disjoint_eventually
      (fun m => Nat.floor (τ * (m : ℝ)))
      (τ / 2) (by positivity) hlinear (∏ s ∈ S, s),
      (tendsto_atTop.1 compatibleLogMinorCutoff_tendsto_atTop 1)]
      with n hseparation hcutoff
  intro residue
  unfold actualMajorArcCoefficientMajorIntegral
    actualDeduplicatedMajorPrimeMass actualMajorArcShiftedMinor
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  rw [ternaryShiftedMajorRegion_integral_eq_actual_center_sum
    (∏ s ∈ S, s) (compatibleLogMinorCutoff n)
    (fullyCompatibleFareyCutoff
      (fun m => Nat.floor (τ * (m : ℝ))) n)
    hW hcutoff hseparation
    (actualMajorArcPrimeCubic S b n J residue a d τ ell)
    (actualMajorArcPrimeCubic_continuous S b n J residue a d τ ell)]
  simp

/-- The sole remaining original prime-pattern analytic input, expressed
directly on the exact FINITE DISJOINT RATIONAL-CENTER sum. Its absolute
constant precedes every support, target, real strip, and robust residue.
No minor-arc, endpoint, selector, coefficient, or overlap input remains. -/
def UniformActualDeduplicatedCenterMajorPositivity : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in atTop,
          ∀ residue ∈ robustResidues S b J,
            c * manuscriptLocalSingularFactor S b residue *
                ell * (n : ℝ) ^ 2 ≤
              actualDeduplicatedMajorPrimeMass S b n J residue
                (compatibleLogMinorCutoff n)
                (fullyCompatibleFareyCutoff
                  (fun m => Nat.floor (τ * (m : ℝ))) n)
                τ ell

/-- The complete shifted-major positivity obligation is EXACTLY equivalent
to positivity of the explicit deduplicated true-center integrals. All
duplicate-anchor, periodic-lift, and coefficient-sum identities are proved;
neither direction infers a sign from a principal arc. -/
theorem uniformActualSummedMajorPositivity_iff_deduplicated_center :
    UniformActualCoefficientSummedMajorArcPositivity ↔
      UniformActualDeduplicatedCenterMajorPositivity := by
  constructor
  · rintro ⟨c, hc, hmajor⟩
    refine ⟨c, hc, ?_⟩
    intro S b J τ ell hsupport hτ hell hstrip
    filter_upwards
      [hmajor S b J τ ell hsupport hτ hell hstrip,
        actualMajorArcCoefficientMajorIntegral_eq_center_mass_eventually
          S b J τ ell (fun s hs => (hsupport s hs).1) hτ]
        with n hpositive hequality
    intro residue hresidue
    rw [← hequality residue]
    exact hpositive residue hresidue
  · rintro ⟨c, hc, hmajor⟩
    refine ⟨c, hc, ?_⟩
    intro S b J τ ell hsupport hτ hell hstrip
    filter_upwards
      [hmajor S b J τ ell hsupport hτ hell hstrip,
        actualMajorArcCoefficientMajorIntegral_eq_center_mass_eventually
          S b J τ ell (fun s hs => (hsupport s hs).1) hτ]
        with n hpositive hequality
    intro residue hresidue
    rw [hequality residue]
    exact hpositive residue hresidue

/-- The exact original covering conclusion now has only TWO precise
remaining hypotheses: positive quadratic mass of the actual finite
deduplicated rational-center integrals, and the genuine fixed-left graph
degree. The full actual prime-only minors, right degree, label degree,
deficiency asymptotic, and matching construction are unconditional. -/
theorem officialStatement_of_actual_center_major_positivity_and_left_degree
    (hmajor : UniformActualDeduplicatedCenterMajorPositivity)
    (hleft : FixedModulusLeftVertexDegreeBound) :
    OfficialStatement := by
  apply officialStatement_of_localized_major_arcs_and_left_vertex_degree
    _ hleft
  exact uniformLocalizedThreePrimeMajorArcLowerBound_of_actual_summed_major_positivity
    (uniformActualSummedMajorPositivity_iff_deduplicated_center.mpr hmajor)

end Erdos689

#print axioms Erdos689.actualMajorArcCoefficientMajorIntegral_eq_center_mass_eventually
#print axioms Erdos689.uniformActualSummedMajorPositivity_iff_deduplicated_center
#print axioms Erdos689.officialStatement_of_actual_center_major_positivity_and_left_degree
