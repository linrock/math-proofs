module

public import ActualLeftVertexMajorExceptional433
public import ActualMajorArcPositivityTail433

@[expose] public section


/-!
# Actual deduplicated-center integration and complete error bookkeeping

Each distinct genuine shifted rational center uses its ORIGINAL widest
anchor, never one representative per duplicated shift. The full prime
cubic is integrated against the exact admissible smooth-cell model PLUS
every retained signed exceptional cell. Its integrated error is the actual
sum of all Siegel--Walfisz cubic and proper-prime-power terms. Independent
global bounds dispose of every prime-power and exceptional contribution
over all centers, cells, and support-divisor coefficient pairs. No sign of
the remaining smooth rational-center sum is presumed.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Exact `lcm(q,W)` numerator of an actual already-lifted shifted Farey
anchor; the anchor's integer numerator includes its periodic lift. -/
noncomputable def actualMajorArcIntegratedAnchorNumerator
    (S : Finset ℕ) (anchor : ShiftedFareyAnchor) : ℤ :=
  anchor.2.1 *
    ((actualMajorArcLcmResidueModulus S anchor.1 / anchor.1 : ℕ) : ℤ) -
  anchor.2.2 *
    ((actualMajorArcLcmResidueModulus S anchor.1 /
      (∏ p ∈ S, p) : ℕ) : ℤ)

/-- ALL genuine switched-unit smooth triple cells at one actual anchor,
using the true shifted center and its correct lifted common numerator. -/
noncomputable def actualMajorArcIntegratedAnchorSmooth
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor) (α : ℝ) : ℂ :=
  ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
      S b target a d anchor.1,
    actualMajorArcLcmSmoothCellCubic
      S n a d anchor.1 triple.1 triple.2.1 triple.2.2 τ ell
      (actualMajorArcIntegratedAnchorNumerator S anchor)
      (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
        anchor.1 anchor.2.1 anchor.2.2)

/-- Every original signed nonunit/incompatible cell, retained exactly at
the actual anchor denominator; it is never treated as positive. -/
noncomputable def actualMajorArcIntegratedAnchorExceptional
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor) (α : ℝ) : ℂ :=
  ∑ triple ∈ actualMajorArcLcmExceptionalCellTriples
      S b target a d anchor.1,
    actualMajorArcLcmPrimeCellCubic
      S b n J target a d anchor.1
        triple.1 triple.2.1 triple.2.2 τ ell α

/-- The FULL actual per-anchor error, summing the original explicit
three-form Siegel--Walfisz and prime-power bounds over every unit cell. -/
noncomputable def actualMajorArcIntegratedAnchorError
    (S : Finset ℕ) (b : ℕ → ℕ) (c C : ℝ)
    (n target a d : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor) (α : ℝ) : ℝ :=
  ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
      S b target a d anchor.1,
    (ternaryManuscriptMajorArcCubicError
      c C n (actualMajorArcLcmResidueModulus S anchor.1)
      triple.1 triple.2.1 triple.2.2 a d
      (manuscriptRealLabelLower τ n)
      (manuscriptRealLabelUpper τ ell n)
      1 (n / (2 * a) + 1)
      1 (n / (4 * d) + 1)
      (actualMajorArcIntegratedAnchorNumerator S anchor)
      (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
        anchor.1 anchor.2.1 anchor.2.2) +
      actualMajorArcFullCubicPrimePowerError n)

/-- The true finite switched-unit smooth model is continuous on the whole
Fourier circle, including every negative-frequency manuscript factor. -/
theorem actualMajorArcIntegratedAnchorSmooth_continuous
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor) :
    Continuous (actualMajorArcIntegratedAnchorSmooth
      S b n target a d τ ell anchor) := by
  unfold actualMajorArcIntegratedAnchorSmooth
    actualMajorArcLcmSmoothCellCubic ternaryMajorArcIntervalModel
    ternaryExponentialSum GoldbachChain.e
  fun_prop

/-- The complete signed exceptional complement is a continuous finite
sum of actual prime exponential cubics. -/
theorem actualMajorArcIntegratedAnchorExceptional_continuous
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor) :
    Continuous (actualMajorArcIntegratedAnchorExceptional
      S b n J target a d τ ell anchor) := by
  unfold actualMajorArcIntegratedAnchorExceptional
    actualMajorArcLcmPrimeCellCubic ternaryExponentialSum GoldbachChain.e
  fun_prop

/-- The full genuine per-anchor cubic error is continuous; it therefore
has a well-defined integral on every exact clipped rational-center region. -/
theorem actualMajorArcIntegratedAnchorError_continuous
    (S : Finset ℕ) (b : ℕ → ℕ) (c C : ℝ)
    (n target a d : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor) :
    Continuous (actualMajorArcIntegratedAnchorError
      S b c C n target a d τ ell anchor) := by
  unfold actualMajorArcIntegratedAnchorError
    ternaryManuscriptMajorArcCubicError ternaryMajorArcProgressionError
    ternaryMajorArcIntervalModel ternaryExponentialSum GoldbachChain.e
  fun_prop

/-- At every genuine translated Farey anchor, the original complete prime
cubic equals its admissible smooth model plus its full signed exception,
up to the EXACT sum of actual three-form SW and prime-power errors. -/
theorem actualMajorArcIntegratedAnchor_full_pointwise_model
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (J target a d : ℕ) (τ ell : ℝ)
          (anchor : ShiftedFareyAnchor),
          0 < anchor.1 → anchor.1 ≤ compatibleLogMinorCutoff n →
          0 < a → 0 < d →
          target ∈ robustResidues S b J →
          manuscriptRealLabelLower τ n ≤ manuscriptRealLabelUpper τ ell n →
          manuscriptRealLabelUpper τ ell n ≤ n →
          n / (2 * a) + 1 ≤ n →
          n / (4 * d) + 1 ≤ n →
          ∀ α : ℝ,
            ‖actualMajorArcPrimeCubic S b n J target a d τ ell α -
              (actualMajorArcIntegratedAnchorSmooth
                S b n target a d τ ell anchor α +
               actualMajorArcIntegratedAnchorExceptional
                S b n J target a d τ ell anchor α)‖ ≤
              actualMajorArcIntegratedAnchorError
                S b c C n target a d τ ell anchor α := by
  obtain ⟨c, C, hc, hC, hmodel⟩ :=
    actualMajorArcPrimeCubic_shifted_full_cell_model S b hsupport
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hmodel] with n hn
  intro J target a d τ ell anchor hanchor hcutoff ha hd htarget
    hlower hupper hleft hright α
  have hactual := hn J target a d anchor.1 τ ell hanchor hcutoff
    ha hd htarget hlower hupper hleft hright anchor.2.1 anchor.2.2 0
      (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
        anchor.1 anchor.2.1 anchor.2.2)
  dsimp only at hactual
  simp only [Int.cast_zero, zero_mul, add_zero] at hactual
  have hfrequency :
      (anchor.2.1 : ℝ) / anchor.1 -
        (anchor.2.2 : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) +
        (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
          anchor.1 anchor.2.1 anchor.2.2) = α := by
    unfold shiftedFareyAnchorCenter
    ring
  rw [hfrequency] at hactual
  simpa [actualMajorArcIntegratedAnchorSmooth,
    actualMajorArcIntegratedAnchorExceptional,
    actualMajorArcIntegratedAnchorError,
    actualMajorArcIntegratedAnchorNumerator] using hactual

/-- Each DISTINCT actual shifted center is represented by its genuine
widest original anchor, and the integral of the full original prime cubic
differs from its full signed smooth-plus-exception model by at most the
integral of ALL its actual SW and prime-power errors. Duplicate widths are
never confused with separate anchors or discarded. -/
theorem actualMajorArcIntegrated_deduplicated_widest_center_error
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (J target a d Q : ℕ) (τ ell : ℝ),
          0 < a → 0 < d →
          target ∈ robustResidues S b J →
          manuscriptRealLabelLower τ n ≤ manuscriptRealLabelUpper τ ell n →
          manuscriptRealLabelUpper τ ell n ≤ n →
          n / (2 * a) + 1 ≤ n →
          n / (4 * d) + 1 ≤ n →
          ∀ center ∈ shiftedFareyCenterClasses (∏ p ∈ S, p)
              (actualShiftedFareyAnchors (∏ p ∈ S, p)
                (compatibleLogMinorCutoff n)),
            ∃ anchor ∈ actualShiftedFareyAnchors (∏ p ∈ S, p)
                (compatibleLogMinorCutoff n),
              shiftedFareyAnchorCenter (∏ p ∈ S, p)
                anchor.1 anchor.2.1 anchor.2.2 = center ∧
              shiftedFareyCenterRegion (∏ p ∈ S, p) Q
                (actualShiftedFareyAnchors (∏ p ∈ S, p)
                  (compatibleLogMinorCutoff n)) center =
                shiftedFareyAnchorArc (∏ p ∈ S, p)
                  Q anchor.1 anchor.2.1 anchor.2.2 ∧
              ‖(∫ α in Set.Ioc (0 : ℝ) 1 ∩
                  shiftedFareyCenterRegion (∏ p ∈ S, p) Q
                    (actualShiftedFareyAnchors (∏ p ∈ S, p)
                      (compatibleLogMinorCutoff n)) center,
                  actualMajorArcPrimeCubic S b n J target a d τ ell α) -
                (∫ α in Set.Ioc (0 : ℝ) 1 ∩
                  shiftedFareyCenterRegion (∏ p ∈ S, p) Q
                    (actualShiftedFareyAnchors (∏ p ∈ S, p)
                      (compatibleLogMinorCutoff n)) center,
                  actualMajorArcIntegratedAnchorSmooth
                    S b n target a d τ ell anchor α +
                  actualMajorArcIntegratedAnchorExceptional
                    S b n J target a d τ ell anchor α)‖ ≤
                ∫ α in Set.Ioc (0 : ℝ) 1 ∩
                  shiftedFareyCenterRegion (∏ p ∈ S, p) Q
                    (actualShiftedFareyAnchors (∏ p ∈ S, p)
                      (compatibleLogMinorCutoff n)) center,
                  actualMajorArcIntegratedAnchorError
                    S b c C n target a d τ ell anchor α := by
  classical
  obtain ⟨c, C, hc, hC, hpoint⟩ :=
    actualMajorArcIntegratedAnchor_full_pointwise_model S b hsupport
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hpoint] with n hn
  intro J target a d Q τ ell ha hd htarget hlower hupper hleft hright
    center hcenter
  let W : ℕ := ∏ p ∈ S, p
  let P : ℕ := compatibleLogMinorCutoff n
  let A := actualShiftedFareyAnchors W P
  obtain ⟨anchor, hanchor, hcorrect, hwidest⟩ :=
    shiftedFareyCenterRegion_eq_widest_anchor W Q A center hcenter
      (fun t ht => (actualShiftedFareyAnchors_denominator_bounds
        W P t ht).1)
  refine ⟨anchor, hanchor, hcorrect, hwidest, ?_⟩
  let region := Set.Ioc (0 : ℝ) 1 ∩
    shiftedFareyCenterRegion W Q A center
  have hregion : MeasurableSet region :=
    measurableSet_Ioc.inter
      (shiftedFareyCenterRegion_measurable W Q A center)
  have hactual : IntegrableOn
      (actualMajorArcPrimeCubic S b n J target a d τ ell)
      region volume :=
    (actualMajorArcPrimeCubic_continuous
      S b n J target a d τ ell).integrableOn_Ioc.mono_set
        Set.inter_subset_left
  have hsmooth := actualMajorArcIntegratedAnchorSmooth_continuous
    S b n target a d τ ell anchor
  have hexception := actualMajorArcIntegratedAnchorExceptional_continuous
    S b n J target a d τ ell anchor
  have hmodel : IntegrableOn
      (fun α => actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α +
        actualMajorArcIntegratedAnchorExceptional
          S b n J target a d τ ell anchor α)
      region volume :=
    (hsmooth.add hexception).integrableOn_Ioc.mono_set
      Set.inter_subset_left
  have herror : IntegrableOn
      (actualMajorArcIntegratedAnchorError
        S b c C n target a d τ ell anchor)
      region volume :=
    (actualMajorArcIntegratedAnchorError_continuous
      S b c C n target a d τ ell anchor).integrableOn_Ioc.mono_set
        Set.inter_subset_left
  apply ternary_major_arc_integrated_error region hregion
    (actualMajorArcPrimeCubic S b n J target a d τ ell)
    (fun α => actualMajorArcIntegratedAnchorSmooth
      S b n target a d τ ell anchor α +
      actualMajorArcIntegratedAnchorExceptional
        S b n J target a d τ ell anchor α)
    (actualMajorArcIntegratedAnchorError
      S b c C n target a d τ ell anchor)
    hactual hmodel herror
  intro α _
  obtain ⟨hpositive, hbounded⟩ :=
    actualShiftedFareyAnchors_denominator_bounds W P anchor hanchor
  exact hn J target a d τ ell anchor hpositive hbounded
    ha hd htarget hlower hupper hleft hright α

/-- ALL actual coefficient pairs, deduplicated shifted centers, common
modulus cells, and true Farey-arc widths together still give a genuinely
vanishing normalized proper-prime-power error. -/
theorem actualMajorArcIntegrated_all_coefficients_prime_power_tendsto_zero
    (S : Finset ℕ) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto
      (fun n : ℕ =>
        ((((∏ p ∈ S, p).divisors).card : ℝ) ^ 2) *
          ((shiftedFareyCenterClasses (∏ p ∈ S, p)
            (actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n))).card : ℝ) *
          (((∏ p ∈ S, p) * compatibleLogMinorCutoff n : ℕ) : ℝ) ^ 3 *
          ((2 / κ) * (compatibleLogMinorCutoff n : ℝ)) *
          (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2))
      atTop (nhds 0) := by
  let W : ℕ := ∏ p ∈ S, p
  have hbase :=
    (actualMajorArcError_cutoff_power_prime_power_normalized_tendsto_zero
      6).const_mul
        (((W.divisors.card : ℝ) ^ 2) * (8 * (W : ℝ) ^ 4) * (2 / κ))
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by
      unfold ternaryPrimePowerErrorBound
      positivity)
    _ (by simpa using hbase)
  filter_upwards
    [compatibleLogMinorCutoff_tendsto_atTop.eventually
      (eventually_ge_atTop (1 : ℕ))] with n hn
  let P : ℕ := compatibleLogMinorCutoff n
  have hcard := actualMajorArcError_shifted_center_card_le W P hn
  have hcardReal :
      ((shiftedFareyCenterClasses W
        (actualShiftedFareyAnchors W P)).card : ℝ) ≤
        8 * (W : ℝ) * (P : ℝ) ^ 2 := by
    exact_mod_cast hcard
  have hprime : 0 ≤ ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2 := by
    unfold ternaryPrimePowerErrorBound
    positivity
  calc
    ((W.divisors.card : ℝ) ^ 2) *
        ((shiftedFareyCenterClasses W
          (actualShiftedFareyAnchors W P)).card : ℝ) *
        ((W * P : ℕ) : ℝ) ^ 3 * ((2 / κ) * (P : ℝ)) *
        (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2) ≤
      ((W.divisors.card : ℝ) ^ 2) *
        (8 * (W : ℝ) * (P : ℝ) ^ 2) *
        ((W * P : ℕ) : ℝ) ^ 3 * ((2 / κ) * (P : ℝ)) *
        (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2) := by
          gcongr
    _ = (((W.divisors.card : ℝ) ^ 2) *
          (8 * (W : ℝ) ^ 4) * (2 / κ)) *
          ((P : ℝ) ^ 6 *
            (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2)) := by
          push_cast
          ring

/-- The ENTIRE signed exceptional family remains negligible even after
ALL original support-divisor coefficient pairs are included. -/
theorem actualMajorArcIntegrated_all_coefficients_exceptional_tendsto_zero
    (S : Finset ℕ) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto
      (fun n : ℕ =>
        ((((∏ p ∈ S, p).divisors).card : ℝ) ^ 2) *
          (((shiftedFareyCenterClasses (∏ p ∈ S, p)
            (actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n))).card : ℝ) *
            ((2 / κ) * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 3 *
              (compatibleLogMinorCutoff n : ℝ) ^ 5 *
              (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2))))
      atTop (nhds 0) := by
  simpa using
    (actualMajorArcExceptional_all_shifted_centers_normalized_tendsto_zero
      S κ hκ).const_mul ((((∏ p ∈ S, p).divisors).card : ℝ) ^ 2)

/-- Any fixed polynomial Abel/Farey loss in the true SW cubic error is
annihilated even after EVERY support coefficient pair, exact distinct
center, and genuine common-modulus triple cell has been counted. -/
theorem actualMajorArcIntegrated_all_coefficients_siegel_decay_tendsto_zero
    (S : Finset ℕ) (c : ℝ) (hc : 0 < c)
    (extraPower : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((((∏ p ∈ S, p).divisors).card : ℝ) ^ 2) *
          (((shiftedFareyCenterClasses (∏ p ∈ S, p)
            (actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n))).card : ℝ) *
            (((∏ p ∈ S, p) * compatibleLogMinorCutoff n : ℕ) : ℝ) ^ 3 *
            (compatibleLogMinorCutoff n : ℝ) ^ extraPower *
            Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10))))
      atTop (nhds 0) := by
  simpa using
    (actualMajorArcError_shifted_center_triple_cells_exp_tendsto_zero
      (∏ p ∈ S, p) c hc extraPower).const_mul
        ((((∏ p ∈ S, p).divisors).card : ℝ) ^ 2)

#print axioms Erdos689.actualMajorArcIntegratedAnchorSmooth_continuous
#print axioms Erdos689.actualMajorArcIntegratedAnchorExceptional_continuous
#print axioms Erdos689.actualMajorArcIntegratedAnchorError_continuous
#print axioms Erdos689.actualMajorArcIntegratedAnchor_full_pointwise_model
#print axioms Erdos689.actualMajorArcIntegrated_deduplicated_widest_center_error
#print axioms Erdos689.actualMajorArcIntegrated_all_coefficients_prime_power_tendsto_zero
#print axioms Erdos689.actualMajorArcIntegrated_all_coefficients_exceptional_tendsto_zero
#print axioms Erdos689.actualMajorArcIntegrated_all_coefficients_siegel_decay_tendsto_zero

end Erdos689
