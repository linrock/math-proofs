module

public import ActualRightVertexMajorUnitOrbit433
public import ActualLeftVertexMajorExceptional433

@[expose] public section


/-!
# Genuine three-cell singular-phase assembly at mixed conductors

The actual switched major-arc model has three independent full-common-modulus
unit selectors, not an unrestricted residue character.  Its complete
admissible triple phase factors exactly into the genuine fixed-label,
fixed-left, and fixed-right phase sums.  Consequently every denominator
containing a squared support prime contributes exactly zero even after ALL
unit filters and both switched selectors are retained.  The complete
support-character shift projects the remaining signed triple phases onto the
original affine congruence.  No deduplicated integrated major-arc positivity
or identification with an outside Euler series is assumed.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- The ORIGINAL fixed robust-label support residue together with the FULL
common-modulus prime-progression unit condition. -/
noncomputable def actualMajorArcSingularLabelResidues
    (S : Finset ℕ) (target denominator : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (actualMajorArcLcmResidueModulus S denominator)).filter
    fun residue => residue % (∏ p ∈ S, p) = target ∧
      Nat.Coprime residue (actualMajorArcLcmResidueModulus S denominator)

/-- The genuine fixed-left common-modulus unit and ORIGINAL switched mask. -/
noncomputable def actualMajorArcSingularLeftResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (a denominator : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (actualMajorArcLcmResidueModulus S denominator)).filter
    fun residue =>
      Nat.Coprime residue (actualMajorArcLcmResidueModulus S denominator) ∧
        switchedHits S b (2 * (a * residue)) = 0

/-- The genuine fixed-right common-modulus unit and ORIGINAL `4*d` mask. -/
noncomputable def actualMajorArcSingularRightResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (d denominator : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (actualMajorArcLcmResidueModulus S denominator)).filter
    fun residue =>
      Nat.Coprime residue (actualMajorArcLcmResidueModulus S denominator) ∧
        switchedHits S b (2 * (2 * d * residue)) = 0

/-- All three ORIGINAL common-modulus unit selectors are independent before
the signed rational-center phase is summed.  Both switched masks and the
fixed robust label residue are retained exactly. -/
theorem actualMajorArcSingular_admissible_triples_eq_selector_product
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ) :
    actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator =
      (actualMajorArcSingularLabelResidues S target denominator).product
        ((actualMajorArcSingularLeftResidues S b a denominator).product
          (actualMajorArcSingularRightResidues S b d denominator)) := by
  classical
  ext triple
  rcases triple with ⟨label, left, right⟩
  constructor
  · intro htriple
    unfold actualMajorArcLcmAdmissibleCellTriples at htriple
    obtain ⟨hall, hconditions⟩ := Finset.mem_filter.mp htriple
    unfold actualMajorArcLcmAllCellTriples at hall
    obtain ⟨hlabelRange, hremaining⟩ := Finset.mem_product.mp hall
    obtain ⟨hleftRange, hrightRange⟩ := Finset.mem_product.mp hremaining
    unfold actualMajorArcLcmAdmissibleCell at hconditions
    obtain ⟨hlabelTarget, hlabelUnit, hleftUnit,
      hrightUnit, hleftMask, hrightMask⟩ := hconditions
    apply Finset.mem_product.mpr
    refine ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr
        ⟨hlabelRange, hlabelTarget, hlabelUnit⟩
    · exact Finset.mem_filter.mpr
        ⟨hleftRange, hleftUnit, hleftMask⟩
    · exact Finset.mem_filter.mpr
        ⟨hrightRange, hrightUnit, hrightMask⟩
  · intro htriple
    obtain ⟨hlabel, hremaining⟩ := Finset.mem_product.mp htriple
    obtain ⟨hleft, hright⟩ := Finset.mem_product.mp hremaining
    obtain ⟨hlabelRange, hlabelTarget, hlabelUnit⟩ :=
      Finset.mem_filter.mp hlabel
    obtain ⟨hleftRange, hleftUnit, hleftMask⟩ :=
      Finset.mem_filter.mp hleft
    obtain ⟨hrightRange, hrightUnit, hrightMask⟩ :=
      Finset.mem_filter.mp hright
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨hlabelRange, Finset.mem_product.mpr
        ⟨hleftRange, hrightRange⟩⟩, ?_⟩
    exact ⟨hlabelTarget, hlabelUnit, hleftUnit,
      hrightUnit, hleftMask, hrightMask⟩

/-- The complete genuine common-modulus admissible three-cell character
factors into the three exact support-switched UNIT-residue phase sums.
This holds for EVERY denominator, including all mixed support conductors. -/
theorem actualMajorArcSingular_admissible_phase_eq_three_unit_sums
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ) (effective : ℤ) :
    (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator,
      actualMajorArcArchimedeanCellPhase
        (actualMajorArcLcmResidueModulus S denominator)
        triple.1 triple.2.1 triple.2.2 a d effective) =
      (∑ label ∈ actualMajorArcSingularLabelResidues
          S target denominator,
        GoldbachChain.e
          (((label : ℝ) * effective) /
            actualMajorArcLcmResidueModulus S denominator)) *
      (∑ left ∈ actualMajorArcSingularLeftResidues
          S b a denominator,
        GoldbachChain.e
          ((((a : ℝ) * left) * effective) /
            actualMajorArcLcmResidueModulus S denominator)) *
      (∑ right ∈ actualMajorArcSingularRightResidues
          S b d denominator,
        GoldbachChain.e
          (((((-2 * (d : ℤ) : ℤ) : ℝ) * right) * effective) /
            actualMajorArcLcmResidueModulus S denominator)) := by
  classical
  rw [actualMajorArcSingular_admissible_triples_eq_selector_product]
  let labels := actualMajorArcSingularLabelResidues S target denominator
  let lefts := actualMajorArcSingularLeftResidues S b a denominator
  let rights := actualMajorArcSingularRightResidues S b d denominator
  let L := actualMajorArcLcmResidueModulus S denominator
  let F : ℕ → ℂ := fun label =>
    GoldbachChain.e (((label : ℝ) * effective) / L)
  let G : ℕ → ℂ := fun left =>
    GoldbachChain.e ((((a : ℝ) * left) * effective) / L)
  let H : ℕ → ℂ := fun right =>
    GoldbachChain.e (((((-2 * (d : ℤ) : ℤ) : ℝ) * right) * effective) / L)
  change
    (∑ triple ∈ labels.product (lefts.product rights),
      F triple.1 * G triple.2.1 * H triple.2.2) =
      (∑ label ∈ labels, F label) *
        (∑ left ∈ lefts, G left) *
        (∑ right ∈ rights, H right)
  simp [Finset.sum_product, Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ label ∈ labels, ∑ right ∈ rights, ∑ left ∈ lefts,
        F label * G left * H right := by
      apply Finset.sum_congr rfl
      intro label hlabel
      exact Finset.sum_comm
    _ = ∑ right ∈ rights, ∑ label ∈ labels, ∑ left ∈ lefts,
        F label * G left * H right := by
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro right hright
      exact Finset.sum_comm

/-- The true numerator of an ORIGINAL shifted rational major center,
including the support character and integer periodic lift. -/
def actualMajorArcSingularShiftedNumerator
    (S : Finset ℕ) (denominator numerator : ℕ)
    (shift lift : ℤ) : ℤ :=
  (numerator : ℤ) *
      ((actualMajorArcLcmResidueModulus S denominator /
        denominator : ℕ) : ℤ) -
    shift *
      ((actualMajorArcLcmResidueModulus S denominator /
        (∏ p ∈ S, p) : ℕ) : ℤ) +
    lift * (actualMajorArcLcmResidueModulus S denominator : ℤ)

/-- The actual fixed-label UNIT factor of the full three-cell phase cancels
at every true shifted mixed denominator containing a squared support prime. -/
theorem actualMajorArcSingular_shifted_label_phase_zero_of_support_square
    (S : Finset ℕ)
    (denominator p numerator target : ℕ)
    (shift lift : ℤ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdenominator : 0 < denominator)
    (hpSupport : p ∈ S)
    (hpSquare : p ^ 2 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    (∑ label ∈ actualMajorArcSingularLabelResidues
        S target denominator,
      GoldbachChain.e
        (((label : ℝ) *
          actualMajorArcSingularShiftedNumerator
            S denominator numerator shift lift) /
              actualMajorArcLcmResidueModulus S denominator)) = 0 := by
  simpa [actualMajorArcSingularLabelResidues,
    actualMajorArcSingularShiftedNumerator, mul_comm] using
      (actualMajorArcUnitOrbit_actual_shifted_unit_label_sum_zero
        S denominator p numerator target shift lift
        hsupport hdenominator hpSupport hpSquare hnumerator)

/-- The COMPLETE ACTUAL signed admissible three-cell phase is ZERO at every
mixed denominator carrying a squared switched-support prime.  All three
full-modulus unit filters, both switched masks, the genuine robust label,
and the entire original shifted numerator are preserved. -/
theorem actualMajorArcSingular_admissible_phase_zero_of_support_square
    (S : Finset ℕ) (b : ℕ → ℕ)
    (denominator p numerator target a d : ℕ)
    (shift lift : ℤ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdenominator : 0 < denominator)
    (hpSupport : p ∈ S)
    (hpSquare : p ^ 2 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator,
      actualMajorArcArchimedeanCellPhase
        (actualMajorArcLcmResidueModulus S denominator)
        triple.1 triple.2.1 triple.2.2 a d
        (actualMajorArcSingularShiftedNumerator
          S denominator numerator shift lift)) = 0 := by
  rw [actualMajorArcSingular_admissible_phase_eq_three_unit_sums]
  rw [actualMajorArcSingular_shifted_label_phase_zero_of_support_square
    S denominator p numerator target shift lift
    hsupport hdenominator hpSupport hpSquare hnumerator]
  ring

/-- Exact factorization of the COMPLETE original admissible smooth cubic:
the genuine signed three-cell phase times the full `φ(lcm(q,W))⁻³`
density and the actual coefficient-sensitive two-edge archimedean cubic. -/
theorem actualMajorArcSingular_admissible_smooth_eq_phase_cubic
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d denominator : ℕ)
    (τ ell : ℝ) (effective : ℤ) (β : ℝ) :
    (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator,
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator triple.1 triple.2.1 triple.2.2
        τ ell effective β) =
      (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
          S b target a d denominator,
        actualMajorArcArchimedeanCellPhase
          (actualMajorArcLcmResidueModulus S denominator)
          triple.1 triple.2.1 triple.2.2 a d effective) *
        (1 / ((actualMajorArcLcmResidueModulus S denominator).totient : ℂ)) ^ 3 *
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β := by
  classical
  calc
    _ = ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
          S b target a d denominator,
        (actualMajorArcArchimedeanCellPhase
          (actualMajorArcLcmResidueModulus S denominator)
          triple.1 triple.2.1 triple.2.2 a d effective *
            (1 / ((actualMajorArcLcmResidueModulus
              S denominator).totient : ℂ)) ^ 3) *
              actualMajorArcArchimedeanSmoothCubic a d n τ ell β := by
      apply Finset.sum_congr rfl
      intro triple htriple
      exact actualMajorArcArchimedean_smooth_cell_eq_phase_cubic
        S n a d denominator triple.1 triple.2.1 triple.2.2
          τ ell effective β
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]

/-- Every squared switched-support prime annihilates the ENTIRE actual
modeled signed smooth cubic, pointwise at every true shifted center and
every offset.  This is cancellation of genuine admissible three-cell
contributions, not cancellation over spurious nonunit label lifts. -/
theorem actualMajorArcSingular_admissible_smooth_zero_of_support_square
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n denominator p numerator target a d : ℕ)
    (shift lift : ℤ) (τ ell β : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdenominator : 0 < denominator)
    (hpSupport : p ∈ S)
    (hpSquare : p ^ 2 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator,
      actualMajorArcLcmSmoothCellCubic
        S n a d denominator triple.1 triple.2.1 triple.2.2
        τ ell
        (actualMajorArcSingularShiftedNumerator
          S denominator numerator shift lift) β) = 0 := by
  rw [actualMajorArcSingular_admissible_smooth_eq_phase_cubic]
  rw [actualMajorArcSingular_admissible_phase_zero_of_support_square
    S b denominator p numerator target a d shift lift
    hsupport hdenominator hpSupport hpSquare hnumerator]
  ring

/-- The EXACT genuine support selector normalization contains the
indispensable compensating `a*d`: the true selector density
`#selector*W/φ(W)^3` is precisely `a*d*actualWeight/φ(W)`.
The weight already contains its own reciprocal coefficient factors. -/
theorem actualMajorArcSingular_actual_selector_compensated_normalization
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d q₀ r₀ : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : 2 * d * r₀ = a * q₀ + target) :
    (((actualLabelFiberUnitSelectorResidues
      S b target a d q₀ r₀).card : ℕ) : ℝ) *
      (((∏ p ∈ S, p) : ℕ) : ℝ) /
        ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 3 =
      ((a : ℝ) * d *
        actualFixedLabelDoubleCoefficientWeight S target b a d) /
          ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) := by
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have haPositive : 0 < a := Nat.pos_of_dvd_of_pos ha hW
  have hdPositive : 0 < d := Nat.pos_of_dvd_of_pos hd hW
  have hphi : 0 < (∏ p ∈ S, p).totient := Nat.totient_pos.mpr hW
  have haReal : (a : ℝ) ≠ 0 := by exact_mod_cast haPositive.ne'
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hdPositive.ne'
  have hphiReal : ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hphi.ne'
  rw [sharpLabel_actual_selector_coefficient_normalization_of_seed
    S target a d q₀ r₀ b
    (fun p hp => (hsupport p hp).1)
    (fun p hp => by have h := (hsupport p hp).2; omega)
    ha hd hcoprime htarget hb hseed]
  field_simp

#print axioms Erdos689.actualMajorArcSingular_admissible_triples_eq_selector_product
#print axioms Erdos689.actualMajorArcSingular_admissible_phase_eq_three_unit_sums
#print axioms Erdos689.actualMajorArcSingular_shifted_label_phase_zero_of_support_square
#print axioms Erdos689.actualMajorArcSingular_admissible_phase_zero_of_support_square
#print axioms Erdos689.actualMajorArcSingular_admissible_smooth_eq_phase_cubic
#print axioms Erdos689.actualMajorArcSingular_admissible_smooth_zero_of_support_square
#print axioms Erdos689.actualMajorArcSingular_actual_selector_compensated_normalization

end Erdos689
