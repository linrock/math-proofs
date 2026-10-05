module

public import ActualRightVertexMajorMixedConductor433
public import ActualLeftVertexMajorFullApprox433

@[expose] public section


/-!
# Exact signed support-shift projection and the parity conductor

The generic coprime-denominator singular series cannot simply discard
support-sharing rational centers or incompatible residue triples.  Summing
ALL genuine support character shifts instead projects the actual three-form
phase onto precisely the manuscript affine congruence.  Incompatible cells
cancel exactly.  At conductor two, the original odd label and odd left
prime with odd support-divisor coefficient give the genuine positive parity
factor two.  No integrated global major-arc positivity is asserted.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The signed integer affine defect of an ORIGINAL manuscript residue
triple; its vanishing modulo the support is the true compatibility test. -/
def actualMajorArcSquarefreeAffineDefect
    (label left right a d : ℕ) : ℤ :=
  (label : ℤ) + (a : ℤ) * left - 2 * (d : ℤ) * right

/-- The genuine three-form cell phase at an arbitrary REAL center.  All
three original frequencies, including the negative doubled center, remain. -/
noncomputable def actualMajorArcSquarefreeTriplePhase
    (label left right a d : ℕ) (center : ℝ) : ℂ :=
  GoldbachChain.e ((label : ℝ) * center) *
    GoldbachChain.e (((a : ℝ) * left) * center) *
    GoldbachChain.e
      ((((-2 * (d : ℤ) : ℤ) : ℝ) * right) * center)

/-- The full original three-coordinate phase is exactly the single
additive character of its signed affine defect. -/
theorem actualMajorArcSquarefreeTriplePhase_eq_defect_phase
    (label left right a d : ℕ) (center : ℝ) :
    actualMajorArcSquarefreeTriplePhase label left right a d center =
      GoldbachChain.e
        ((actualMajorArcSquarefreeAffineDefect
          label left right a d : ℝ) * center) := by
  unfold actualMajorArcSquarefreeTriplePhase
    actualMajorArcSquarefreeAffineDefect
  rw [GoldbachChain.e_add, GoldbachChain.e_add]
  congr 1
  push_cast
  ring

/-- Exact support divisibility of the signed defect is equivalent to the
ORIGINAL manuscript congruence; no incompatible triple is identified as
admissible. -/
theorem actualMajorArcSquarefreeAffineDefect_dvd_iff
    (modulus label left right a d : ℕ) :
    (modulus : ℤ) ∣
        actualMajorArcSquarefreeAffineDefect label left right a d ↔
      (a * left + label) % modulus = (2 * d * right) % modulus := by
  have hdefect :
      actualMajorArcSquarefreeAffineDefect label left right a d =
        ((a * left + label : ℕ) : ℤ) -
          ((2 * d * right : ℕ) : ℤ) := by
    unfold actualMajorArcSquarefreeAffineDefect
    push_cast
    ring
  rw [hdefect]
  constructor
  · intro hdivide
    exact (Nat.modEq_iff_dvd.mpr hdivide).symm
  · intro hcongruence
    exact Nat.modEq_iff_dvd.mp hcongruence.symm

/-- EXACT sum over EVERY genuine support character shift, retaining the
full outside rational numerator and arbitrary periodic integer lift.  All
incompatible actual triple cells cancel; compatible cells retain factor W. -/
theorem actualMajorArcSquarefree_support_shift_phase_projection
    (support denominator label left right a d : ℕ)
    (numerator periodic : ℤ)
    (hsupport : 0 < support) :
    (∑ shift ∈ Finset.range support,
      actualMajorArcSquarefreeTriplePhase label left right a d
        ((numerator : ℝ) / denominator -
          (shift : ℝ) / support + (periodic : ℝ))) =
      GoldbachChain.e
        (((actualMajorArcSquarefreeAffineDefect
            label left right a d : ℝ) * numerator) / denominator) *
        if (a * left + label) % support =
            (2 * d * right) % support
          then (support : ℂ) else 0 := by
  let defect := actualMajorArcSquarefreeAffineDefect
    label left right a d
  have hphase (shift : ℕ) :
      actualMajorArcSquarefreeTriplePhase label left right a d
        ((numerator : ℝ) / denominator -
          (shift : ℝ) / support + (periodic : ℝ)) =
        GoldbachChain.e (((defect : ℝ) * numerator) / denominator) *
          GoldbachChain.e ((((-defect : ℤ) : ℝ) * shift) / support) := by
    rw [actualMajorArcSquarefreeTriplePhase_eq_defect_phase]
    have hsplit :
        (defect : ℝ) *
            ((numerator : ℝ) / denominator -
              (shift : ℝ) / support + (periodic : ℝ)) =
          (((defect : ℝ) * numerator) / denominator +
            (((-defect : ℤ) : ℝ) * shift) / support) +
              (((defect * periodic : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [hsplit, ← GoldbachChain.e_add,
      GoldbachChain.MinorArc.e_int, mul_one,
      ← GoldbachChain.e_add]
  calc
    (∑ shift ∈ Finset.range support,
      actualMajorArcSquarefreeTriplePhase label left right a d
        ((numerator : ℝ) / denominator -
          (shift : ℝ) / support + (periodic : ℝ))) =
        ∑ shift ∈ Finset.range support,
          GoldbachChain.e (((defect : ℝ) * numerator) / denominator) *
            GoldbachChain.e
              ((((-defect : ℤ) : ℝ) * shift) / support) := by
          apply Finset.sum_congr rfl
          intro shift hshift
          exact hphase shift
    _ = GoldbachChain.e (((defect : ℝ) * numerator) / denominator) *
          ∑ shift ∈ Finset.range support,
            GoldbachChain.e
              ((((-defect : ℤ) : ℝ) * shift) / support) := by
          rw [Finset.mul_sum]
    _ = GoldbachChain.e (((defect : ℝ) * numerator) / denominator) *
          (if (support : ℤ) ∣ -defect then (support : ℂ) else 0) := by
          rw [GoldbachChain.MinorArc.char_orthogonality
            (-defect) support hsupport.ne']
    _ = _ := by
      by_cases hcongruence :
          (a * left + label) % support =
            (2 * d * right) % support
      · have hdivide : (support : ℤ) ∣ defect :=
          (actualMajorArcSquarefreeAffineDefect_dvd_iff
            support label left right a d).mpr hcongruence
        simp [defect, hcongruence, hdivide]
      · have hnot : ¬ (support : ℤ) ∣ defect := by
          intro hdivide
          exact hcongruence
            ((actualMajorArcSquarefreeAffineDefect_dvd_iff
              support label left right a d).mp hdivide)
        simp [defect, hcongruence, hnot]

/-- ALL true switched-selector/unit/robust triple cells obey exact signed
support-shift projection simultaneously, with arbitrary genuine cell
weights.  Incompatible selected triples cancel rather than being dropped. -/
theorem actualMajorArcSquarefree_admissible_triple_shift_projection
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ)
    (numerator periodic : ℤ)
    (weight : (ℕ × ℕ × ℕ) → ℂ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (∑ shift ∈ Finset.range (∏ p ∈ S, p),
      ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
          S b target a d denominator,
        weight triple *
          actualMajorArcSquarefreeTriplePhase
            triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / denominator -
              (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
                (periodic : ℝ))) =
      (((∏ p ∈ S, p) : ℕ) : ℂ) *
        ∑ triple ∈
            (actualMajorArcLcmAdmissibleCellTriples
              S b target a d denominator).filter
              (fun triple =>
                (a * triple.2.1 + triple.1) % (∏ p ∈ S, p) =
                  (2 * d * triple.2.2) % (∏ p ∈ S, p)),
          weight triple *
            GoldbachChain.e
              (((actualMajorArcSquarefreeAffineDefect
                  triple.1 triple.2.1 triple.2.2 a d : ℝ) *
                    numerator) / denominator) := by
  classical
  let W := ∏ p ∈ S, p
  let cells := actualMajorArcLcmAdmissibleCellTriples
    S b target a d denominator
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  change
    (∑ shift ∈ Finset.range W,
      ∑ triple ∈ cells,
        weight triple *
          actualMajorArcSquarefreeTriplePhase
            triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / denominator -
              (shift : ℝ) / W + (periodic : ℝ))) =
      (W : ℂ) *
        ∑ triple ∈ cells.filter
          (fun triple =>
            (a * triple.2.1 + triple.1) % W =
              (2 * d * triple.2.2) % W),
          weight triple *
            GoldbachChain.e
              (((actualMajorArcSquarefreeAffineDefect
                triple.1 triple.2.1 triple.2.2 a d : ℝ) *
                  numerator) / denominator)
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [actualMajorArcSquarefree_support_shift_phase_projection
    W denominator _ _ _ a d numerator periodic hW]
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro triple htriple
  by_cases hcompatible :
      (a * triple.2.1 + triple.1) % W =
        (2 * d * triple.2.2) % W
  · simp [hcompatible]
    ring
  · simp [hcompatible]

/-- The actual parity defect vanishes modulo two whenever its true label,
left prime, and support-divisor coefficient are odd.  The doubled center
term never creates a spurious parity obstruction. -/
theorem actualMajorArcSquarefree_odd_triple_defect_even
    (label left right a d : ℕ)
    (hlabel : label % 2 = 1)
    (hleft : left % 2 = 1)
    (ha : a % 2 = 1) :
    (2 : ℤ) ∣ actualMajorArcSquarefreeAffineDefect
      label left right a d := by
  apply (actualMajorArcSquarefreeAffineDefect_dvd_iff
    2 label left right a d).mpr
  simp [Nat.add_mod, Nat.mul_mod, hlabel, hleft, ha]

/-- The genuine nonprincipal parity center has constructive phase ONE,
not an uncontrolled signed contribution, for every actual odd triple. -/
theorem actualMajorArcSquarefree_parity_center_phase_eq_one
    (label left right a d : ℕ)
    (hlabel : label % 2 = 1)
    (hleft : left % 2 = 1)
    (ha : a % 2 = 1) :
    actualMajorArcSquarefreeTriplePhase label left right a d
      (1 / 2 : ℝ) = 1 := by
  rw [actualMajorArcSquarefreeTriplePhase_eq_defect_phase]
  obtain ⟨k, hk⟩ := actualMajorArcSquarefree_odd_triple_defect_even
    label left right a d hlabel hleft ha
  have hphase :
      (actualMajorArcSquarefreeAffineDefect
        label left right a d : ℝ) * (1 / 2 : ℝ) = (k : ℝ) := by
    rw [hk]
    push_cast
    ring
  rw [hphase, GoldbachChain.MinorArc.e_int]

/-- Principal plus genuine parity-center phases give the EXACT positive
local factor TWO.  The denominator-two center is not discarded. -/
theorem actualMajorArcSquarefree_parity_local_factor_eq_two
    (label left right a d : ℕ)
    (hlabel : label % 2 = 1)
    (hleft : left % 2 = 1)
    (ha : a % 2 = 1) :
    actualMajorArcSquarefreeTriplePhase label left right a d 0 +
      actualMajorArcSquarefreeTriplePhase label left right a d
        (1 / 2 : ℝ) = 2 := by
  rw [actualMajorArcSquarefree_parity_center_phase_eq_one
    label left right a d hlabel hleft ha]
  norm_num [actualMajorArcSquarefreeTriplePhase, GoldbachChain.e]

/-- Exact true switched-support coefficient sum TIMES the parity factor
two TIMES the genuine sharp-cutoff outside singular series is eventually at
least half the ORIGINAL manuscript local singular factor.  All support
divisor branches, target residue, cutoff, and absolute constants remain. -/
theorem actualMajorArcSquarefree_support_parity_outside_lower
    (S : Finset ℕ) (b : ℕ → ℕ) (J target : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (htarget : target ∈ robustResidues S b J) :
    ∀ᶠ n : ℕ in Filter.atTop,
      manuscriptLocalSingularFactor S b target / 2 ≤
        (2 : ℝ) *
          ((∑ c ∈ ((∏ p ∈ S, p).divisors.product
              (∏ p ∈ S, p).divisors),
            actualFixedLabelDoubleCoefficientWeight
              S target b c.1 c.2) /
                ((((∏ p ∈ S, p).totient : ℕ) : ℝ))) *
          (∑ denominator ∈ Finset.Icc 1
              (compatibleLogMinorCutoff n),
            actualMajorArcRestrictedSignedCoefficient
              (2 * (∏ p ∈ S, p)) denominator) := by
  let W := ∏ p ∈ S, p
  have hpositive : 0 < manuscriptLocalSingularFactor S b target :=
    manuscriptLocalSingularFactor_pos S b target
      (fun p hp => (hsupport p hp).2)
  have heven : 2 ∣ 2 * W := dvd_mul_right 2 W
  filter_upwards
    [actualMajorArcRestrictedSignedCoefficient_compatible_cutoff_ge_quarter
      (2 * W) heven] with n hn
  rw [actualMajorArcSupport_double_coefficient_sum_div_totient_eq_local
    S b J target hsupport hb htarget]
  change
    manuscriptLocalSingularFactor S b target / 2 ≤
      2 * manuscriptLocalSingularFactor S b target *
        (∑ denominator ∈ Finset.Icc 1
            (compatibleLogMinorCutoff n),
          actualMajorArcRestrictedSignedCoefficient
            (2 * W) denominator)
  nlinarith [mul_le_mul_of_nonneg_left hn hpositive.le]


end Erdos689
