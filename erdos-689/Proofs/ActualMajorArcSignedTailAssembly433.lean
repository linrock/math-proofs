module

public import ActualSingularTailCompletion433
public import ActualMajorArcInterior433
public import ActualMajorArcCorrectedModel433

@[expose] public section


/-!
# Complete parity-corrected signed smooth-tail assembly

The original surviving conductor families have different true Farey widths:
the outside family uses denominator `r ≤ P`, while its parity companion uses
denominator `2*r ≤ P`.  Their signed coefficients are identical, but their
archimedean tails are not.  This module sums BOTH genuine tails with the
actual support-divisor weights and proves their normalized contribution
vanishes.  It also identifies the resulting signed smooth/lattice model
with the exact corrected finite main term, retaining its `A(P)+A(P/2)`
cutoff and all original edge windows.

No assertion identifies deduplicated actual center integrals with this
model; that separate center-reindexing step remains explicit.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- BOTH true conductor families, with their different original Farey widths
and their different sharp cutoffs. -/
noncomputable def actualMajorArcSignedTailBothConductors
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  actualMajorArcFullSignedFareyTail excluded lower a d n τ ell +
    actualMajorArcParitySignedFareyTail excluded lower a d n τ ell

/-- The full signed original odd-plus-doubled conductor tail is `o(n²)`;
both different actual widths and both sharp cutoffs remain intact. -/
theorem actualMajorArcSignedTail_both_conductors_normalized_tendsto_zero
    (excluded : ℕ) (lower : ℕ → ℕ)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcSignedTailBothConductors
          excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hodd := actualMajorArcFullSignedFareyTail_normalized_tendsto_zero
    excluded lower hendpoint a d ha hd τ ell
  have heven := actualMajorArcParitySignedFareyTail_normalized_tendsto_zero
    excluded lower hendpoint a d ha hd τ ell
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ‖actualMajorArcFullSignedFareyTail
              excluded lower a d n τ ell‖ / (n : ℝ) ^ 2 +
            ‖actualMajorArcParitySignedFareyTail
              excluded lower a d n τ ell‖ / (n : ℝ) ^ 2)
        atTop (nhds 0) := by
    simpa using hodd.add heven
  apply squeeze_zero'
    (Eventually.of_forall fun n => by positivity)
    (Eventually.of_forall fun n => ?_) hsum
  unfold actualMajorArcSignedTailBothConductors
  calc
    _ ≤ (‖actualMajorArcFullSignedFareyTail
            excluded lower a d n τ ell‖ +
          ‖actualMajorArcParitySignedFareyTail
            excluded lower a d n τ ell‖) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = _ := by ring

/-- The ACTUAL support-normalized, coefficient-compensated conductor-tail
sum.  Its factor is precisely `a*d*actualWeight/φ(W)`, as proved by the
genuine full support/outside CRT phase calculation. -/
noncomputable def actualMajorArcSignedTailCoefficientSum
    (S : Finset ℕ) (b : ℕ → ℕ) (target : ℕ)
    (lower : ℕ → ℕ) (n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      (((actualFixedLabelDoubleCoefficientWeight S target b a d *
        (a : ℝ) * d / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) : ℝ) : ℂ) *
        actualMajorArcSignedTailBothConductors
          (2 * (∏ p ∈ S, p)) lower a d n τ ell

/-- The norm of the ENTIRE actual double-coefficient tail is bounded by
the corresponding finite sum of normalized individual signed tails. -/
theorem actualMajorArcSignedTail_coefficient_normalized_le
    (S : Finset ℕ) (b : ℕ → ℕ) (target : ℕ)
    (lower : ℕ → ℕ) (n : ℕ) (τ ell : ℝ) :
    ‖actualMajorArcSignedTailCoefficientSum
      S b target lower n τ ell‖ / (n : ℝ) ^ 2 ≤
      ∑ a ∈ (∏ p ∈ S, p).divisors,
        ∑ d ∈ (∏ p ∈ S, p).divisors,
          ‖actualFixedLabelDoubleCoefficientWeight S target b a d *
            (a : ℝ) * d /
              (((∏ p ∈ S, p).totient : ℕ) : ℝ)‖ *
            (‖actualMajorArcSignedTailBothConductors
              (2 * (∏ p ∈ S, p)) lower a d n τ ell‖ /
                (n : ℝ) ^ 2) := by
  unfold actualMajorArcSignedTailCoefficientSum
  calc
    _ ≤
        (∑ a ∈ (∏ p ∈ S, p).divisors,
          ‖∑ d ∈ (∏ p ∈ S, p).divisors,
            (((actualFixedLabelDoubleCoefficientWeight S target b a d *
              (a : ℝ) * d /
                (((∏ p ∈ S, p).totient : ℕ) : ℝ)) : ℝ) : ℂ) *
              actualMajorArcSignedTailBothConductors
                (2 * (∏ p ∈ S, p)) lower a d n τ ell‖) /
              (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ ≤
        (∑ a ∈ (∏ p ∈ S, p).divisors,
          ∑ d ∈ (∏ p ∈ S, p).divisors,
            ‖(((actualFixedLabelDoubleCoefficientWeight S target b a d *
              (a : ℝ) * d /
                (((∏ p ∈ S, p).totient : ℕ) : ℝ)) : ℝ) : ℂ) *
              actualMajorArcSignedTailBothConductors
                (2 * (∏ p ∈ S, p)) lower a d n τ ell‖) /
              (n : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ = _ := by
      simp_rw [norm_mul, Complex.norm_real, Finset.sum_div]
      congr 1
      funext a
      congr 1
      funext d
      ring

/-- The COMPLETE original signed outside-plus-parity tail, summed over
every actual support-divisor coefficient pair with its exact compensated
CRT density, is `o(n²)`.  No support state, sign, width, or conductor
endpoint is omitted. -/
theorem actualMajorArcSignedTail_coefficient_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ) (target : ℕ)
    (lower : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcSignedTailCoefficientSum
          S b target lower n τ ell‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hpositive (a : ℕ) (ha : a ∈ W.divisors) : 0 < a :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hW
  have hmajor :
      Tendsto
        (fun n : ℕ =>
          ∑ a ∈ W.divisors,
            ∑ d ∈ W.divisors,
              ‖actualFixedLabelDoubleCoefficientWeight S target b a d *
                (a : ℝ) * d / (W.totient : ℝ)‖ *
                (‖actualMajorArcSignedTailBothConductors
                  (2 * W) lower a d n τ ell‖ / (n : ℝ) ^ 2))
        atTop (nhds 0) := by
    have houter := tendsto_finsetSum W.divisors
      (fun a ha => tendsto_finsetSum W.divisors
        (fun d hd =>
          (actualMajorArcSignedTail_both_conductors_normalized_tendsto_zero
            (2 * W) lower hendpoint a d
            (hpositive a ha) (hpositive d hd) τ ell).const_mul
              ‖actualFixedLabelDoubleCoefficientWeight S target b a d *
                (a : ℝ) * d / (W.totient : ℝ)‖))
    simpa using houter
  apply squeeze_zero'
    (Eventually.of_forall fun n => by positivity)
    (Eventually.of_forall fun n => ?_) hmajor
  exact actualMajorArcSignedTail_coefficient_normalized_le
    S b target lower n τ ell

/-- Exact outside-conductor smooth model: EVERY signed original denominator
uses its own genuine archimedean middle tail and the true two-edge lattice. -/
noncomputable def actualMajorArcSignedTailOddSmoothModel
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ denominator ∈ Finset.Icc 1 (compatibleLogMinorCutoff n),
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      (((ternaryAffineTriples
        (actualMajorArcArchimedeanLeftWindow a n)
        (actualMajorArcArchimedeanCenterWindow d n)
        (actualMajorArcArchimedeanLabelWindow τ ell n)
        a (2 * d)).card : ℕ) -
        ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n denominator)
          (1 - actualMajorArcTailFareyRadius lower n denominator),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β)

/-- Exact doubled-parity smooth model: its coefficient is indexed by `r`,
but its TRUE radius is indexed by `2*r` and its cutoff is `P/2`. -/
noncomputable def actualMajorArcSignedTailEvenSmoothModel
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ denominator ∈ Finset.Icc 1 (compatibleLogMinorCutoff n / 2),
    ((actualMajorArcRestrictedSignedCoefficient
      excluded denominator : ℝ) : ℂ) *
      (((ternaryAffineTriples
        (actualMajorArcArchimedeanLeftWindow a n)
        (actualMajorArcArchimedeanCenterWindow d n)
        (actualMajorArcArchimedeanLabelWindow τ ell n)
        a (2 * d)).card : ℕ) -
        ∫ β in Set.Icc
          (actualMajorArcTailFareyRadius lower n (2 * denominator))
          (1 - actualMajorArcTailFareyRadius lower n (2 * denominator)),
          actualMajorArcArchimedeanSmoothCubic a d n τ ell β)

/-- Exact odd-outside signed conductor decomposition into its sharp
arithmetic sum times the original lattice minus its actual signed tail. -/
theorem actualMajorArcSignedTail_odd_smooth_eq_partial_lattice_sub_tail
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) :
    actualMajorArcSignedTailOddSmoothModel
        excluded lower a d n τ ell =
      ((actualMajorArcParityOutsidePartial excluded
          (compatibleLogMinorCutoff n) : ℝ) : ℂ) *
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        actualMajorArcFullSignedFareyTail
          excluded lower a d n τ ell := by
  unfold actualMajorArcSignedTailOddSmoothModel
    actualMajorArcFullSignedFareyTail actualMajorArcParityOutsidePartial
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_mul]
  norm_cast

/-- Exact genuine doubled-even decomposition, retaining its actual `P/2`
cutoff AND the true radius at original denominator `2*r`. -/
theorem actualMajorArcSignedTail_even_smooth_eq_partial_lattice_sub_tail
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) :
    actualMajorArcSignedTailEvenSmoothModel
        excluded lower a d n τ ell =
      ((actualMajorArcParityOutsidePartial excluded
          (compatibleLogMinorCutoff n / 2) : ℝ) : ℂ) *
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        actualMajorArcParitySignedFareyTail
          excluded lower a d n τ ell := by
  unfold actualMajorArcSignedTailEvenSmoothModel
    actualMajorArcParitySignedFareyTail actualMajorArcParityOutsidePartial
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_mul]
  norm_cast

/-- BOTH genuine signed conductor models equal the EXACT finite corrected
parity coefficient times the original edge-bounded lattice minus both true
denominator-dependent tails.  The false finite replacement `2*A(P)` is
never used. -/
theorem actualMajorArcSignedTail_both_smooth_eq_corrected_lattice_sub_tail
    (excluded : ℕ) (lower : ℕ → ℕ)
    (a d n : ℕ) (τ ell : ℝ) :
    actualMajorArcSignedTailOddSmoothModel
        excluded lower a d n τ ell +
      actualMajorArcSignedTailEvenSmoothModel
        excluded lower a d n τ ell =
      ((actualMajorArcParitySharpPartial excluded
          (compatibleLogMinorCutoff n) : ℝ) : ℂ) *
        ((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
        actualMajorArcSignedTailBothConductors
          excluded lower a d n τ ell := by
  rw [actualMajorArcSignedTail_odd_smooth_eq_partial_lattice_sub_tail,
    actualMajorArcSignedTail_even_smooth_eq_partial_lattice_sub_tail]
  unfold actualMajorArcParitySharpPartial
    actualMajorArcSignedTailBothConductors
  push_cast
  ring

/-- Complete coefficient-summed, parity-corrected, denominator-indexed
smooth singular model with the ACTUAL support CRT normalization. -/
noncomputable def actualMajorArcSignedTailCorrectedSmoothModel
    (S : Finset ℕ) (b : ℕ → ℕ) (target : ℕ)
    (lower : ℕ → ℕ) (n : ℕ) (τ ell : ℝ) : ℂ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      (((actualFixedLabelDoubleCoefficientWeight S target b a d *
        (a : ℝ) * d / (((∏ p ∈ S, p).totient : ℕ) : ℝ)) : ℝ) : ℂ) *
        (actualMajorArcSignedTailOddSmoothModel
          (2 * (∏ p ∈ S, p)) lower a d n τ ell +
          actualMajorArcSignedTailEvenSmoothModel
            (2 * (∏ p ∈ S, p)) lower a d n τ ell)

/-- The full actual-support, signed two-conductor smooth model is EXACTLY
the corrected finite positive lattice main term minus the coefficient-summed
genuine original-width tail. -/
theorem actualMajorArcSignedTail_corrected_smooth_eq_main_sub_tail
    (S : Finset ℕ) (b : ℕ → ℕ) (target : ℕ)
    (lower : ℕ → ℕ) (n : ℕ) (τ ell : ℝ) :
    actualMajorArcSignedTailCorrectedSmoothModel
        S b target lower n τ ell =
      ((actualMajorArcCorrectedPredictedMain
        S b n target τ ell : ℝ) : ℂ) -
        actualMajorArcSignedTailCoefficientSum
          S b target lower n τ ell := by
  unfold actualMajorArcSignedTailCorrectedSmoothModel
    actualMajorArcSignedTailCoefficientSum
  simp_rw [actualMajorArcSignedTail_both_smooth_eq_corrected_lattice_sub_tail,
    mul_sub, Finset.sum_sub_distrib]
  congr 1
  unfold actualMajorArcCorrectedPredictedMain
    actualMajorArcFinalCoefficientLatticeMass
  push_cast
  simp_rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- UNCONDITIONAL coupling of the complete genuine signed
denominator-indexed smooth model to the corrected ORIGINAL two-cutoff
coefficient-lattice main term at scale `o(n²)`.  The only separate issue is
identifying the actual deduplicated center family with this exact model. -/
theorem actualMajorArcSignedTail_corrected_smooth_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ) (target : ℕ)
    (lower : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hendpoint : ∀ᶠ n : ℕ in atTop, lower n ≤ n)
    (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ‖actualMajorArcSignedTailCorrectedSmoothModel
            S b target lower n τ ell -
          ((actualMajorArcCorrectedPredictedMain
            S b n target τ ell : ℝ) : ℂ)‖ / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have htail := actualMajorArcSignedTail_coefficient_normalized_tendsto_zero
    S b target lower hsupport hendpoint τ ell
  convert htail using 1
  ext n
  rw [actualMajorArcSignedTail_corrected_smooth_eq_main_sub_tail]
  have hequal :
      ((actualMajorArcCorrectedPredictedMain
          S b n target τ ell : ℝ) : ℂ) -
        actualMajorArcSignedTailCoefficientSum
          S b target lower n τ ell -
        ((actualMajorArcCorrectedPredictedMain
          S b n target τ ell : ℝ) : ℂ) =
      -actualMajorArcSignedTailCoefficientSum
        S b target lower n τ ell := by ring
  rw [hequal, norm_neg]

#print axioms Erdos689.actualMajorArcSignedTail_both_conductors_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcSignedTail_coefficient_normalized_le
#print axioms Erdos689.actualMajorArcSignedTail_coefficient_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcSignedTail_odd_smooth_eq_partial_lattice_sub_tail
#print axioms Erdos689.actualMajorArcSignedTail_even_smooth_eq_partial_lattice_sub_tail
#print axioms Erdos689.actualMajorArcSignedTail_both_smooth_eq_corrected_lattice_sub_tail
#print axioms Erdos689.actualMajorArcSignedTail_corrected_smooth_eq_main_sub_tail
#print axioms Erdos689.actualMajorArcSignedTail_corrected_smooth_normalized_tendsto_zero

end Erdos689
