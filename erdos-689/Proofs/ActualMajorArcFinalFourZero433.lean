module

public import ActualMajorArcCenterPhaseBridge433

@[expose] public section


/-!
# Exact vanishing of higher parity-conductor original anchor orbits

Every original denominator divisible by four has zero COMPLETE genuine
selected-unit three-cell phase.  This is transferred first to its actual
signed anchor coefficient, and then to the full reduced-numerator/support-
character ORIGINAL-width smooth orbit.  No raw anchor is discarded by a
sign assumption, and no support-coprime or switched-selector shortcut is
introduced.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- Every individual ORIGINAL reduced-numerator support-shift anchor at a
higher parity conductor has zero complete actual selected-unit coefficient. -/
theorem actualMajorArcFinalFourZero_original_anchor_coefficient_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator numerator shift : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hdenominator : 0 < denominator)
    (hfour : 4 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    actualCenterCouplingAnchorCoefficient S b target a d
      (denominator, (numerator : ℤ), (shift : ℤ)) = 0 := by
  unfold actualCenterCouplingAnchorCoefficient
  have heffective :
      actualMajorArcIntegratedAnchorNumerator S
        (denominator, (numerator : ℤ), (shift : ℤ)) =
      actualMajorArcSingularShiftedNumerator
        S denominator numerator (shift : ℤ) 0 := by
    simp [actualMajorArcIntegratedAnchorNumerator,
      actualMajorArcSingularShiftedNumerator]
  rw [heffective,
    actualMajorArcParity_admissible_phase_zero_of_four_dvd
      S b denominator numerator target a d (shift : ℤ) 0
      hsupport hdenominator hfour hnumerator]
  simp

/-- The ENTIRE genuine original-width rational-anchor smooth orbit is
exactly zero for every denominator divisible by four, including every
reduced numerator, all support-character shifts, all switched/unit cells,
and the original resonant archimedean integral. -/
theorem actualMajorArcFinalFourZero_original_orbit_zero_of_four_dvd
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d denominator fareyCutoff : ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hdenominator : 0 < denominator)
    (hfarey : 0 < fareyCutoff)
    (hfour : 4 ∣ denominator) :
    ternaryMajorArcOriginalAnchorOrbitSmoothMass
      S b n target a d denominator fareyCutoff τ ell = 0 := by
  rw [ternaryMajorArc_original_anchor_orbit_eq_coefficient_lattice_sub_tail
    S b n target a d denominator fareyCutoff τ ell
      hdenominator hfarey]
  have hcoefficients :
      (∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range (∏ p ∈ S, p),
          actualCenterCouplingAnchorCoefficient
            S b target a d
              (denominator, (numerator : ℤ), (shift : ℤ))) = 0 := by
    apply Finset.sum_eq_zero
    intro numerator hnumerator
    apply Finset.sum_eq_zero
    intro shift hshift
    exact actualMajorArcFinalFourZero_original_anchor_coefficient_zero
      S b target a d denominator numerator shift
      hsupport hdenominator hfour (Finset.mem_filter.mp hnumerator).2
  rw [hcoefficients]
  ring

#print axioms Erdos689.actualMajorArcFinalFourZero_original_anchor_coefficient_zero
#print axioms Erdos689.actualMajorArcFinalFourZero_original_orbit_zero_of_four_dvd

end Erdos689
