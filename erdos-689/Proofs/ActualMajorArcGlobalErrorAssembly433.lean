import ActualMajorArcBoundary433
import ActualMajorArcSupportSelectorBridge433
import ActualLeftVertexMajorSW433

/-!
# Global genuine deduplicated-major error assembly

Every summand is indexed by an ACTUAL distinct rational center, represented
by its widest original Farey anchor.  The canonical anchor is defined only
on the subtype of genuine centers, never by a fabricated fallback outside
that domain.  The model retains the complete signed exceptional family,
all original switched selectors, both coefficient divisors, and the exact
clipped major-arc geometry.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The finite subtype of ACTUAL distinct translated rational centers. -/
abbrev ActualMajorArcGlobalCenter (W P : ℕ) :=
  {center : ℝ // center ∈ shiftedFareyCenterClasses W
    (actualShiftedFareyAnchors W P)}

/-- Canonical genuinely widest anchor, defined ONLY for a real actual center.
The choice retains its original denominator and exact support shift. -/
noncomputable def actualMajorArcGlobalCanonicalWidestAnchor
    (W P Q : ℕ) (center : ActualMajorArcGlobalCenter W P) :
    ShiftedFareyAnchor :=
  Classical.choose
    (shiftedFareyCenterRegion_eq_widest_anchor
      W Q (actualShiftedFareyAnchors W P) center.val center.property
      (fun anchor hanchor =>
        (actualShiftedFareyAnchors_denominator_bounds
          W P anchor hanchor).1))

/-- The canonical representative belongs to the ORIGINAL finite anchor
family, has the correct real center, and gives its entire widest region. -/
theorem actualMajorArcGlobalCanonicalWidestAnchor_spec
    (W P Q : ℕ) (center : ActualMajorArcGlobalCenter W P) :
    actualMajorArcGlobalCanonicalWidestAnchor W P Q center ∈
        actualShiftedFareyAnchors W P ∧
      shiftedFareyAnchorCenter W
        (actualMajorArcGlobalCanonicalWidestAnchor W P Q center).1
        (actualMajorArcGlobalCanonicalWidestAnchor W P Q center).2.1
        (actualMajorArcGlobalCanonicalWidestAnchor W P Q center).2.2 =
          center.val ∧
      shiftedFareyCenterRegion W Q
          (actualShiftedFareyAnchors W P) center.val =
        shiftedFareyAnchorArc W Q
          (actualMajorArcGlobalCanonicalWidestAnchor W P Q center).1
          (actualMajorArcGlobalCanonicalWidestAnchor W P Q center).2.1
          (actualMajorArcGlobalCanonicalWidestAnchor W P Q center).2.2 := by
  exact Classical.choose_spec
    (shiftedFareyCenterRegion_eq_widest_anchor
      W Q (actualShiftedFareyAnchors W P) center.val center.property
      (fun anchor hanchor =>
        (actualShiftedFareyAnchors_denominator_bounds
          W P anchor hanchor).1))

/-- Genuine coefficient-summed prime mass using the actual center SUBTYPE;
no noncenter input and no invented representative appear in any summand. -/
noncomputable def actualMajorArcGlobalAttachedPrimeMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target P Q : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      ∑ center ∈
        (shiftedFareyCenterClasses (∏ p ∈ S, p)
          (actualShiftedFareyAnchors (∏ p ∈ S, p) P)).attach,
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            shiftedFareyCenterRegion (∏ p ∈ S, p) Q
              (actualShiftedFareyAnchors (∏ p ∈ S, p) P) center.val,
          actualMajorArcPrimeCubic
            S b n J target a d τ ell α).re

/-- Attaching a real membership proof changes NONE of the original
deduplicated coefficient-summed prime-major mass. -/
theorem actualMajorArcGlobalAttachedPrimeMass_eq_original
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target P Q : ℕ) (τ ell : ℝ) :
    actualMajorArcGlobalAttachedPrimeMass
      S b n J target P Q τ ell =
      actualDeduplicatedMajorPrimeMass
        S b n J target P Q τ ell := by
  unfold actualMajorArcGlobalAttachedPrimeMass
    actualDeduplicatedMajorPrimeMass
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  exact Finset.sum_attach
    (shiftedFareyCenterClasses (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) P))
    (fun center : ℝ =>
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩
          shiftedFareyCenterRegion (∏ p ∈ S, p) Q
            (actualShiftedFareyAnchors (∏ p ∈ S, p) P) center,
        actualMajorArcPrimeCubic S b n J target a d τ ell α).re)

/-- Exact global smooth-plus-SIGNED-exception model, evaluated for each
center at its canonical actual WIDEST original denominator. -/
noncomputable def actualMajorArcGlobalCanonicalModelMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target P Q : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      ∑ center ∈
        (shiftedFareyCenterClasses (∏ p ∈ S, p)
          (actualShiftedFareyAnchors (∏ p ∈ S, p) P)).attach,
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            shiftedFareyCenterRegion (∏ p ∈ S, p) Q
              (actualShiftedFareyAnchors (∏ p ∈ S, p) P) center.val,
          actualMajorArcIntegratedAnchorSmooth
            S b n target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) P Q center) α +
          actualMajorArcIntegratedAnchorExceptional
            S b n J target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) P Q center) α).re

/-- The exact complete three-form Siegel--Walfisz PLUS proper-prime-power
error budget, summed over every true coefficient pair and distinct center. -/
noncomputable def actualMajorArcGlobalCanonicalErrorBudget
    (S : Finset ℕ) (b : ℕ → ℕ) (c C : ℝ)
    (n target P Q : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      ∑ center ∈
        (shiftedFareyCenterClasses (∏ p ∈ S, p)
          (actualShiftedFareyAnchors (∏ p ∈ S, p) P)).attach,
        ∫ α in Set.Ioc (0 : ℝ) 1 ∩
            shiftedFareyCenterRegion (∏ p ∈ S, p) Q
              (actualShiftedFareyAnchors (∏ p ∈ S, p) P) center.val,
          actualMajorArcIntegratedAnchorError
            S b c C n target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) P Q center) α

/-- True quadratically normalized integrated three-form SW rate per
genuine switched-unit residue cell and actual widest anchor. -/
noncomputable def actualMajorArcGlobalSWRate
    (S : Finset ℕ) (κ c C : ℝ) (n : ℕ) : ℝ :=
  (2 / κ) * actualMajorArcSWCubicCoefficient C κ (∏ p ∈ S, p) *
    (compatibleLogMinorCutoff n : ℝ) ^ 4 *
    Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10))

/-- True quadratically normalized integrated proper-prime-power rate;
the indispensable genuine inverse-`n` Farey width has already been kept. -/
noncomputable def actualMajorArcGlobalPrimePowerRate
    (κ : ℝ) (n : ℕ) : ℝ :=
  ((2 / κ) * (compatibleLogMinorCutoff n : ℝ)) *
    (ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2)

/-- Full actual center/coefficient/common-modulus counting majorant for the
combined genuinely integrated SW and proper-prime-power errors. -/
noncomputable def actualMajorArcGlobalCanonicalErrorMajorant
    (S : Finset ℕ) (κ c C : ℝ) (n : ℕ) : ℝ :=
  ((((∏ p ∈ S, p).divisors).card : ℝ) ^ 2) *
    ((shiftedFareyCenterClasses (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p)
        (compatibleLogMinorCutoff n))).card : ℝ) *
    (((∏ p ∈ S, p) * compatibleLogMinorCutoff n : ℕ) : ℝ) ^ 3 *
    (actualMajorArcGlobalSWRate S κ c C n +
      actualMajorArcGlobalPrimePowerRate κ n)

/-- The combined genuine global majorant tends to zero, simultaneously
including every support-divisor pair, deduplicated center, full common-
modulus triple cell, SW loss, prime-power term, and true arc width. -/
theorem actualMajorArcGlobalCanonicalErrorMajorant_tendsto_zero
    (S : Finset ℕ) (κ c C : ℝ)
    (hκ : 0 < κ) (hc : 0 < c) (hC : 0 ≤ C) :
    Tendsto
      (fun n : ℕ => actualMajorArcGlobalCanonicalErrorMajorant
        S κ c C n)
      atTop (nhds 0) := by
  have hsw := actualMajorArcSW_all_coefficients_centers_cells_tendsto_zero
    S κ hκ c C hc hC
  have hprime :=
    actualMajorArcIntegrated_all_coefficients_prime_power_tendsto_zero
      S κ hκ
  convert hsw.add hprime using 1
  · ext n
    unfold actualMajorArcGlobalCanonicalErrorMajorant
      actualMajorArcGlobalSWRate actualMajorArcGlobalPrimePowerRate
    ring
  · norm_num

/-- The ACTUAL coefficient-summed canonical error budget is nonnegative;
no signed prime or smooth contribution is used as an error majorant. -/
theorem actualMajorArcGlobalCanonicalErrorBudget_nonneg
    (S : Finset ℕ) (b : ℕ → ℕ)
    (c C : ℝ) (hC : 0 ≤ C)
    (n target P Q : ℕ) (τ ell : ℝ) :
    0 ≤ actualMajorArcGlobalCanonicalErrorBudget
      S b c C n target P Q τ ell := by
  unfold actualMajorArcGlobalCanonicalErrorBudget
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro center hcenter
  apply integral_nonneg
  intro α
  unfold actualMajorArcIntegratedAnchorError
  apply Finset.sum_nonneg
  intro triple htriple
  unfold ternaryManuscriptMajorArcCubicError
    ternaryMajorArcProgressionError
    actualMajorArcFullCubicPrimePowerError
  positivity

/-- Every actual distinct center, represented by its CANONICAL widest
genuine anchor, satisfies the complete original integrated prime-versus-
smooth-plus-signed-exception error inequality. -/
theorem actualMajorArcGlobalCanonicalCenter_error
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
          ∀ center : ActualMajorArcGlobalCenter
              (∏ p ∈ S, p) (compatibleLogMinorCutoff n),
            ‖(∫ α in Set.Ioc (0 : ℝ) 1 ∩
                shiftedFareyCenterRegion (∏ p ∈ S, p) Q
                  (actualShiftedFareyAnchors (∏ p ∈ S, p)
                    (compatibleLogMinorCutoff n)) center.val,
                actualMajorArcPrimeCubic
                  S b n J target a d τ ell α) -
              (∫ α in Set.Ioc (0 : ℝ) 1 ∩
                shiftedFareyCenterRegion (∏ p ∈ S, p) Q
                  (actualShiftedFareyAnchors (∏ p ∈ S, p)
                    (compatibleLogMinorCutoff n)) center.val,
                actualMajorArcIntegratedAnchorSmooth
                  S b n target a d τ ell
                  (actualMajorArcGlobalCanonicalWidestAnchor
                    (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α +
                actualMajorArcIntegratedAnchorExceptional
                  S b n J target a d τ ell
                  (actualMajorArcGlobalCanonicalWidestAnchor
                    (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α)‖ ≤
              ∫ α in Set.Ioc (0 : ℝ) 1 ∩
                shiftedFareyCenterRegion (∏ p ∈ S, p) Q
                  (actualShiftedFareyAnchors (∏ p ∈ S, p)
                    (compatibleLogMinorCutoff n)) center.val,
                actualMajorArcIntegratedAnchorError
                  S b c C n target a d τ ell
                  (actualMajorArcGlobalCanonicalWidestAnchor
                    (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α := by
  classical
  obtain ⟨c, C, hc, hC, hpoint⟩ :=
    actualMajorArcIntegratedAnchor_full_pointwise_model S b hsupport
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hpoint] with n hn
  intro J target a d Q τ ell ha hd htarget
    hlower hupper hleft hright center
  let W : ℕ := ∏ p ∈ S, p
  let P : ℕ := compatibleLogMinorCutoff n
  let anchor := actualMajorArcGlobalCanonicalWidestAnchor W P Q center
  let region := Set.Ioc (0 : ℝ) 1 ∩
    shiftedFareyCenterRegion W Q
      (actualShiftedFareyAnchors W P) center.val
  have hanchor :=
    (actualMajorArcGlobalCanonicalWidestAnchor_spec W P Q center).1
  have hbounds := actualShiftedFareyAnchors_denominator_bounds
    W P anchor hanchor
  have hregion : MeasurableSet region :=
    measurableSet_Ioc.inter
      (shiftedFareyCenterRegion_measurable W Q
        (actualShiftedFareyAnchors W P) center.val)
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
  exact hn J target a d τ ell anchor hbounds.1 hbounds.2
    ha hd htarget hlower hupper hleft hright α

/-- Finite signed errors can be summed without presuming positivity of
either the genuine original quantity or its signed major-arc model. -/
theorem actualMajorArcGlobal_finset_sum_abs_sub_le
    {ι : Type*} (F : Finset ι)
    (actual model error : ι → ℝ)
    (herror : ∀ i ∈ F, |actual i - model i| ≤ error i) :
    |(∑ i ∈ F, actual i) - (∑ i ∈ F, model i)| ≤
      ∑ i ∈ F, error i := by
  calc
    |(∑ i ∈ F, actual i) - (∑ i ∈ F, model i)| =
        |∑ i ∈ F, (actual i - model i)| := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ F, |actual i - model i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ F, error i := Finset.sum_le_sum herror

/-- FULL ORIGINAL coefficient-summed deduplicated prime-major mass differs
from its genuine canonical-widest smooth-plus-signed-exception model by at
most the complete summed actual integrated three-form SW/prime-power error.
No center, support divisor, switched selector, or exceptional sign is lost. -/
theorem actualMajorArcGlobalCanonicalMass_error
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (J target Q : ℕ) (τ ell : ℝ),
          target ∈ robustResidues S b J →
          manuscriptRealLabelLower τ n ≤ manuscriptRealLabelUpper τ ell n →
          manuscriptRealLabelUpper τ ell n ≤ n →
          (∀ a ∈ (∏ p ∈ S, p).divisors,
            n / (2 * a) + 1 ≤ n) →
          (∀ d ∈ (∏ p ∈ S, p).divisors,
            n / (4 * d) + 1 ≤ n) →
          |actualDeduplicatedMajorPrimeMass
              S b n J target (compatibleLogMinorCutoff n) Q τ ell -
            actualMajorArcGlobalCanonicalModelMass
              S b n J target (compatibleLogMinorCutoff n) Q τ ell| ≤
            actualMajorArcGlobalCanonicalErrorBudget
              S b c C n target (compatibleLogMinorCutoff n) Q τ ell := by
  classical
  obtain ⟨c, C, hc, hC, hcenters⟩ :=
    actualMajorArcGlobalCanonicalCenter_error S b hsupport
  refine ⟨c, C, hc, hC, ?_⟩
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  filter_upwards [hcenters] with n hn
  intro J target Q τ ell htarget hlower hupper hleft hright
  rw [← actualMajorArcGlobalAttachedPrimeMass_eq_original]
  unfold actualMajorArcGlobalAttachedPrimeMass
    actualMajorArcGlobalCanonicalModelMass
    actualMajorArcGlobalCanonicalErrorBudget
  apply actualMajorArcGlobal_finset_sum_abs_sub_le
  intro a ha
  apply actualMajorArcGlobal_finset_sum_abs_sub_le
  intro d hd
  apply actualMajorArcGlobal_finset_sum_abs_sub_le
  intro center hcenter
  have haPositive : 0 < a :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hW
  have hdPositive : 0 < d :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hW
  have hbound := hn J target a d Q τ ell haPositive hdPositive
    htarget hlower hupper (hleft a ha) (hright d hd) center
  calc
    |(∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion (∏ p ∈ S, p) Q
          (actualShiftedFareyAnchors (∏ p ∈ S, p)
            (compatibleLogMinorCutoff n)) center.val,
        actualMajorArcPrimeCubic S b n J target a d τ ell α).re -
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion (∏ p ∈ S, p) Q
          (actualShiftedFareyAnchors (∏ p ∈ S, p)
            (compatibleLogMinorCutoff n)) center.val,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α +
        actualMajorArcIntegratedAnchorExceptional
          S b n J target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α).re| =
      |((∫ α in Set.Ioc (0 : ℝ) 1 ∩
          shiftedFareyCenterRegion (∏ p ∈ S, p) Q
            (actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n)) center.val,
          actualMajorArcPrimeCubic S b n J target a d τ ell α) -
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
          shiftedFareyCenterRegion (∏ p ∈ S, p) Q
            (actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n)) center.val,
          actualMajorArcIntegratedAnchorSmooth
            S b n target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α +
          actualMajorArcIntegratedAnchorExceptional
            S b n J target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α)).re| := by
        rw [Complex.sub_re]
    _ ≤ ‖(∫ α in Set.Ioc (0 : ℝ) 1 ∩
          shiftedFareyCenterRegion (∏ p ∈ S, p) Q
            (actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n)) center.val,
          actualMajorArcPrimeCubic S b n J target a d τ ell α) -
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩
          shiftedFareyCenterRegion (∏ p ∈ S, p) Q
            (actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n)) center.val,
          actualMajorArcIntegratedAnchorSmooth
            S b n target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α +
          actualMajorArcIntegratedAnchorExceptional
            S b n J target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) (compatibleLogMinorCutoff n) Q center) α)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ _ := hbound

/-- ALL genuine real-strip and coefficient-divisor window endpoints lie in
the original ambient interval at every positive scale; no extra eventual
or coefficient-dependent endpoint hypothesis is necessary. -/
theorem actualMajorArcGlobal_true_window_endpoints
    (S : Finset ℕ) (τ ell : ℝ) (n : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hn : 0 < n)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell)
    (hstrip : τ + ell < 1) :
    manuscriptRealLabelLower τ n ≤ manuscriptRealLabelUpper τ ell n ∧
      manuscriptRealLabelUpper τ ell n ≤ n ∧
      (∀ a ∈ (∏ p ∈ S, p).divisors,
        n / (2 * a) + 1 ≤ n) ∧
      (∀ d ∈ (∏ p ∈ S, p).divisors,
        n / (4 * d) + 1 ≤ n) := by
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · unfold manuscriptRealLabelLower manuscriptRealLabelUpper
    apply Nat.add_le_add_right
    apply Nat.floor_mono
    nlinarith
  constructor
  · unfold manuscriptRealLabelUpper
    have hnonnegative : 0 ≤ (τ + ell) * (n : ℝ) := by positivity
    have hstrict : (τ + ell) * (n : ℝ) < n := by nlinarith
    have hfloor : Nat.floor ((τ + ell) * (n : ℝ)) < n :=
      (Nat.floor_lt hnonnegative).mpr hstrict
    omega
  constructor
  · intro a ha
    have haPositive := Nat.pos_of_dvd_of_pos
      (Nat.mem_divisors.mp ha).1 hW
    have hdenominator : 1 < 2 * a := by omega
    have hdivision := Nat.div_lt_self hn hdenominator
    omega
  · intro d hd
    have hdPositive := Nat.pos_of_dvd_of_pos
      (Nat.mem_divisors.mp hd).1 hW
    have hdenominator : 1 < 4 * d := by omega
    have hdivision := Nat.div_lt_self hn hdenominator
    omega

/-- The complete genuine deduplicated-major analytic transfer at the TRUE
manuscript Farey cutoff: every auxiliary interval and divisor endpoint
hypothesis has been discharged, and the exact signed full-model difference
is bounded solely by its actual integrated SW/prime-power budget. -/
theorem actualMajorArcGlobalCanonicalMass_error_original
    (S : Finset ℕ) (b : ℕ → ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (J target : ℕ), target ∈ robustResidues S b J →
          |actualDeduplicatedMajorPrimeMass
              S b n J target (compatibleLogMinorCutoff n)
              (fullyCompatibleFareyCutoff
                (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell -
            actualMajorArcGlobalCanonicalModelMass
              S b n J target (compatibleLogMinorCutoff n)
              (fullyCompatibleFareyCutoff
                (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell| ≤
            actualMajorArcGlobalCanonicalErrorBudget
              S b c C n target (compatibleLogMinorCutoff n)
              (fullyCompatibleFareyCutoff
                (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell := by
  obtain ⟨c, C, hc, hC, hglobal⟩ :=
    actualMajorArcGlobalCanonicalMass_error S b hsupport
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hglobal, eventually_gt_atTop (0 : ℕ)] with n hn hpositive
  intro J target htarget
  obtain ⟨hlower, hupper, hleft, hright⟩ :=
    actualMajorArcGlobal_true_window_endpoints
      S τ ell n hsupport hpositive hτ.le hell.le
      (by nlinarith)
  exact hn J target
    (fullyCompatibleFareyCutoff
      (fun m => Nat.floor (τ * (m : ℝ))) n)
    τ ell htarget hlower hupper hleft hright

/-- The ACTUAL complete integrated canonical-anchor error, summed over all
its real switched-unit cells, is bounded by the precise combined SW and
prime-power cell rates.  The original widest denominator supplies the
essential inverse-`n` factor for BOTH contributions. -/
theorem actualMajorArcGlobalCanonicalAnchorError_normalized_eventually
    (S : Finset ℕ) (b : ℕ → ℕ)
    (lower : ℕ → ℕ) (κ c C : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a ∈ (∏ p ∈ S, p).divisors,
        ∀ d ∈ (∏ p ∈ S, p).divisors,
          ∀ (target : ℕ) (τ ell : ℝ),
            manuscriptRealLabelUpper τ ell n ≤ n →
            n / (2 * a) + 1 ≤ n →
            n / (4 * d) + 1 ≤ n →
            ∀ center : ActualMajorArcGlobalCenter
                (∏ p ∈ S, p) (compatibleLogMinorCutoff n),
              (∫ α in Set.Ioc (0 : ℝ) 1 ∩
                shiftedFareyCenterRegion (∏ p ∈ S, p)
                  (fullyCompatibleFareyCutoff lower n)
                  (actualShiftedFareyAnchors (∏ p ∈ S, p)
                    (compatibleLogMinorCutoff n)) center.val,
                actualMajorArcIntegratedAnchorError
                  S b c C n target a d τ ell
                  (actualMajorArcGlobalCanonicalWidestAnchor
                    (∏ p ∈ S, p) (compatibleLogMinorCutoff n)
                    (fullyCompatibleFareyCutoff lower n) center) α) /
                    (n : ℝ) ^ 2 ≤
                (((∏ p ∈ S, p) * compatibleLogMinorCutoff n : ℕ) : ℝ) ^ 3 *
                  (actualMajorArcGlobalSWRate S κ c C n +
                    actualMajorArcGlobalPrimePowerRate κ n) := by
  classical
  filter_upwards
    [actualMajorArcSW_true_anchor_cubic_error_eventually
      S hsupport lower κ hκ hlower c C hc hC,
      actualMajorArcArchimedean_shifted_anchor_scaled_volume_eventually
        lower κ hκ hlower (∏ p ∈ S, p),
      eventually_gt_atTop (0 : ℕ)]
      with n hsw hvolume hn
  intro a ha d hd target τ ell hupper hleft hright center
  let W : ℕ := ∏ p ∈ S, p
  let P : ℕ := compatibleLogMinorCutoff n
  let Q : ℕ := fullyCompatibleFareyCutoff lower n
  let anchor := actualMajorArcGlobalCanonicalWidestAnchor W P Q center
  let cells := actualMajorArcLcmAdmissibleCellTriples
    S b target a d anchor.1
  let B := actualMajorArcSWCubicCoefficient C κ W
  let decay := Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10))
  let M : ℝ := (((W * P : ℕ) : ℝ)) ^ 3
  let bound : ℝ :=
    M * (B * (n : ℝ) ^ 3 * (P : ℝ) ^ 3 * decay +
      actualMajorArcFullCubicPrimePowerError n)
  have hspec := actualMajorArcGlobalCanonicalWidestAnchor_spec
    W P Q center
  have hanchor := hspec.1
  have hbounds := actualShiftedFareyAnchors_denominator_bounds
    W P anchor hanchor
  have hcard := actualMajorArcLcmAdmissibleCellTriples_card_le
    S b target a d anchor.1 P hbounds.1 hbounds.2 hsupport
  have hcardReal : (cells.card : ℝ) ≤ M := by
    dsimp [cells, M, W]
    exact_mod_cast hcard
  have hB : 0 ≤ B := by
    dsimp [B, actualMajorArcSWCubicCoefficient,
      actualMajorArcSWLinearCoefficient]
    positivity
  have hprime : 0 ≤ actualMajorArcFullCubicPrimePowerError n := by
    rw [actualMajorArcFullCubicPrimePowerError_eq_n_mul]
    unfold ternaryPrimePowerErrorBound
    positivity
  have hterm :
      0 ≤ B * (n : ℝ) ^ 3 * (P : ℝ) ^ 3 * decay +
        actualMajorArcFullCubicPrimePowerError n := by
    dsimp [decay]
    positivity
  rw [hspec.2.2]
  let region := Set.Ioc (0 : ℝ) 1 ∩
    shiftedFareyAnchorArc W Q anchor.1 anchor.2.1 anchor.2.2
  let error : ℝ → ℝ := actualMajorArcIntegratedAnchorError
    S b c C n target a d τ ell anchor
  have hpoint : ∀ α ∈ region, error α ≤ bound := by
    intro α hα
    dsimp [error]
    unfold actualMajorArcIntegratedAnchorError
    change
      (∑ triple ∈ cells,
        (ternaryManuscriptMajorArcCubicError
          c C n (actualMajorArcLcmResidueModulus S anchor.1)
          triple.1 triple.2.1 triple.2.2 a d
          (manuscriptRealLabelLower τ n)
          (manuscriptRealLabelUpper τ ell n)
          1 (n / (2 * a) + 1)
          1 (n / (4 * d) + 1)
          (actualMajorArcIntegratedAnchorNumerator S anchor)
          (α - shiftedFareyAnchorCenter W
            anchor.1 anchor.2.1 anchor.2.2) +
          actualMajorArcFullCubicPrimePowerError n)) ≤ bound
    calc
      _ ≤ ∑ _triple ∈ cells,
          (B * (n : ℝ) ^ 3 * (P : ℝ) ^ 3 * decay +
            actualMajorArcFullCubicPrimePowerError n) := by
        apply Finset.sum_le_sum
        intro triple htriple
        exact add_le_add (hsw a ha d hd anchor hanchor
          triple.1 triple.2.1 triple.2.2
          (manuscriptRealLabelLower τ n)
          (manuscriptRealLabelUpper τ ell n)
          1 (n / (2 * a) + 1)
          1 (n / (4 * d) + 1)
          hupper hleft hright
          (actualMajorArcIntegratedAnchorNumerator S anchor)
          α hα.2) (le_refl _)
      _ = (cells.card : ℝ) *
          (B * (n : ℝ) ^ 3 * (P : ℝ) ^ 3 * decay +
            actualMajorArcFullCubicPrimePowerError n) := by
        simp [mul_add]
      _ ≤ M *
          (B * (n : ℝ) ^ 3 * (P : ℝ) ^ 3 * decay +
            actualMajorArcFullCubicPrimePowerError n) :=
        mul_le_mul_of_nonneg_right hcardReal hterm
      _ = bound := rfl
  have hcontinuous := actualMajorArcIntegratedAnchorError_continuous
    S b c C n target a d τ ell anchor
  have hmeasurable : MeasurableSet region :=
    measurableSet_Ioc.inter Metric.isClosed_closedBall.measurableSet
  have hfinite : volume region < ⊤ :=
    (measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top
  have hintegrable : IntegrableOn error region volume :=
    hcontinuous.integrableOn_Ioc.mono_set Set.inter_subset_left
  have hintegral : (∫ α in region, error α) ≤
      (volume region).toReal * bound := by
    calc
      (∫ α in region, error α) ≤ ∫ _α in region, bound := by
        apply setIntegral_mono_on hintegrable
          (integrableOn_const hfinite.ne) hmeasurable
        exact hpoint
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul]
        rfl
  have hqReal : (1 : ℝ) ≤ (anchor.1 : ℝ) := by
    exact_mod_cast hbounds.1
  have hdenominator : κ ≤ κ * (anchor.1 : ℝ) := by nlinarith
  have hscale0 := hvolume anchor.1 hbounds.1
    anchor.2.1 anchor.2.2
  rw [Set.inter_comm] at hscale0
  have hscale : (volume region).toReal * n ≤
      2 * (P : ℝ) / κ :=
    hscale0.trans
      (div_le_div_of_nonneg_left (by positivity) hκ hdenominator)
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnormalizedPrime :
      0 ≤ ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2 := by
    unfold ternaryPrimePowerErrorBound
    positivity
  have hinner :
      0 ≤ B * (P : ℝ) ^ 3 * decay +
        ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2 := by
    dsimp [decay]
    positivity
  change (∫ α in region, error α) / (n : ℝ) ^ 2 ≤ _
  calc
    (∫ α in region, error α) / (n : ℝ) ^ 2 ≤
        ((volume region).toReal * bound) / (n : ℝ) ^ 2 := by
          gcongr
    _ = M * ((volume region).toReal * n) *
          (B * (P : ℝ) ^ 3 * decay +
            ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2) := by
          dsimp [bound]
          rw [actualMajorArcFullCubicPrimePowerError_eq_n_mul]
          field_simp
    _ ≤ M * (2 * (P : ℝ) / κ) *
          (B * (P : ℝ) ^ 3 * decay +
            ternaryPrimePowerErrorBound n / (n : ℝ) ^ 2) := by
          gcongr
    _ = M *
          (actualMajorArcGlobalSWRate S κ c C n +
            actualMajorArcGlobalPrimePowerRate κ n) := by
          dsimp [M, W, P, B, decay]
          unfold actualMajorArcGlobalSWRate
            actualMajorArcGlobalPrimePowerRate
          ring

/-- The REAL canonical integrated error, over every original coefficient
pair and every DISTINCT translated center, is bounded by its vanishing
all-cells majorant.  No duplicate-anchor counting or fictional arc occurs. -/
theorem actualMajorArcGlobalCanonicalErrorBudget_normalized_le_majorant_eventually
    (S : Finset ℕ) (b : ℕ → ℕ)
    (lower : ℕ → ℕ) (κ c C : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (hc : 0 < c) (hC : 0 ≤ C)
    (τ ell : ℝ)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell)
    (hstrip : τ + ell < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ target : ℕ,
      actualMajorArcGlobalCanonicalErrorBudget
          S b c C n target (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff lower n) τ ell /
        (n : ℝ) ^ 2 ≤
          actualMajorArcGlobalCanonicalErrorMajorant S κ c C n := by
  classical
  filter_upwards
    [actualMajorArcGlobalCanonicalAnchorError_normalized_eventually
      S b lower κ c C hsupport hκ hlower hc hC,
      eventually_gt_atTop (0 : ℕ)] with n hanchor hn
  intro target
  obtain ⟨_, hupper, hleft, hright⟩ :=
    actualMajorArcGlobal_true_window_endpoints
      S τ ell n hsupport hn hτ hell hstrip
  let W : ℕ := ∏ p ∈ S, p
  let P : ℕ := compatibleLogMinorCutoff n
  let centers := shiftedFareyCenterClasses W
    (actualShiftedFareyAnchors W P)
  let bound : ℝ := (((W * P : ℕ) : ℝ)) ^ 3 *
    (actualMajorArcGlobalSWRate S κ c C n +
      actualMajorArcGlobalPrimePowerRate κ n)
  have htotal :
      actualMajorArcGlobalCanonicalErrorBudget
          S b c C n target P
          (fullyCompatibleFareyCutoff lower n) τ ell /
        (n : ℝ) ^ 2 ≤
        ∑ a ∈ W.divisors,
          ∑ d ∈ W.divisors,
            ∑ _center ∈ centers.attach, bound := by
    unfold actualMajorArcGlobalCanonicalErrorBudget
    simp_rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro center hcenter
    exact hanchor a ha d hd target τ ell hupper
      (hleft a ha) (hright d hd) center
  calc
    actualMajorArcGlobalCanonicalErrorBudget
          S b c C n target P
          (fullyCompatibleFareyCutoff lower n) τ ell /
        (n : ℝ) ^ 2 ≤
        ∑ a ∈ W.divisors,
          ∑ d ∈ W.divisors,
            ∑ _center ∈ centers.attach, bound := htotal
    _ = actualMajorArcGlobalCanonicalErrorMajorant S κ c C n := by
      unfold actualMajorArcGlobalCanonicalErrorMajorant
      dsimp [W, P, centers, bound]
      simp
      ring

/-- The COMPLETE actual original coefficient-summed, deduplicated,
canonical-widest integrated SW plus proper-prime-power error is `o(n²)`.
Every switched cell, true inverse-scale arc width, and support divisor
is included in the quantity that tends to zero. -/
theorem actualMajorArcGlobalCanonicalErrorBudget_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (lower : ℕ → ℕ) (κ c C : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (hc : 0 < c) (hC : 0 ≤ C)
    (target : ℕ) (τ ell : ℝ)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell)
    (hstrip : τ + ell < 1) :
    Tendsto
      (fun n : ℕ =>
        actualMajorArcGlobalCanonicalErrorBudget
          S b c C n target (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff lower n) τ ell /
            (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      div_nonneg
        (actualMajorArcGlobalCanonicalErrorBudget_nonneg
          S b c C hC n target (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff lower n) τ ell)
        (sq_nonneg _)
  · filter_upwards
      [actualMajorArcGlobalCanonicalErrorBudget_normalized_le_majorant_eventually
        S b lower κ c C hsupport hκ hlower hc hC
        τ ell hτ hell hstrip] with n hn
    exact hn target
  · exact actualMajorArcGlobalCanonicalErrorMajorant_tendsto_zero
      S κ c C hκ hc hC

/-- At the GENUINE original real-strip Farey cutoff, the full actual
integrated canonical SW plus proper-prime-power error is `o(n²)`.
The lower-endpoint growth, every divisor interval, every distinct center,
and the indispensable true inverse-scale arc width are all unconditional. -/
theorem actualMajorArcGlobalCanonicalErrorBudget_original_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (c C : ℝ) (target : ℕ) (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hc : 0 < c) (hC : 0 ≤ C)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    Tendsto
      (fun n : ℕ =>
        actualMajorArcGlobalCanonicalErrorBudget
          S b c C n target (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff
            (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell /
              (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  exact actualMajorArcGlobalCanonicalErrorBudget_normalized_tendsto_zero
    S b (fun m => Nat.floor (τ * (m : ℝ))) (τ / 2) c C
    hsupport (by positivity)
    (actualMajorArc_real_lower_floor_eventually_linear τ hτ)
    hc hC target τ ell hτ.le hell.le (by nlinarith)

/-- COMPLETE original analytic transfer: the actual prime-only,
coefficient-summed, deduplicated major-region mass equals its real
canonical-widest smooth PLUS SIGNED EXCEPTIONAL center model up to `o(n²)`.
No exceptional term, incompatible sign, support selector, proper prime
power, shifted center, support divisor, or Farey boundary is discarded. -/
theorem actualMajorArcGlobalCanonicalPrimeModel_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (J target : ℕ) (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (htarget : target ∈ robustResidues S b J)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    Tendsto
      (fun n : ℕ =>
        |actualDeduplicatedMajorPrimeMass
            S b n J target (compatibleLogMinorCutoff n)
            (fullyCompatibleFareyCutoff
              (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell -
          actualMajorArcGlobalCanonicalModelMass
            S b n J target (compatibleLogMinorCutoff n)
            (fullyCompatibleFareyCutoff
              (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell| /
              (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  obtain ⟨c, C, hc, hC, herror⟩ :=
    actualMajorArcGlobalCanonicalMass_error_original
      S b τ ell hsupport hτ hell hstrip
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      div_nonneg (abs_nonneg _) (sq_nonneg _)
  · filter_upwards [herror] with n hn
    exact div_le_div_of_nonneg_right
      (hn J target htarget) (sq_nonneg _)
  · exact actualMajorArcGlobalCanonicalErrorBudget_original_tendsto_zero
      S b c C target τ ell hsupport hc hC.le hτ hell hstrip

#print axioms Erdos689.actualMajorArcGlobalCanonicalWidestAnchor_spec
#print axioms Erdos689.actualMajorArcGlobalAttachedPrimeMass_eq_original
#print axioms Erdos689.actualMajorArcGlobalCanonicalErrorMajorant_tendsto_zero
#print axioms Erdos689.actualMajorArcGlobalCanonicalErrorBudget_nonneg
#print axioms Erdos689.actualMajorArcGlobalCanonicalCenter_error
#print axioms Erdos689.actualMajorArcGlobal_finset_sum_abs_sub_le
#print axioms Erdos689.actualMajorArcGlobalCanonicalMass_error
#print axioms Erdos689.actualMajorArcGlobal_true_window_endpoints
#print axioms Erdos689.actualMajorArcGlobalCanonicalMass_error_original
#print axioms Erdos689.actualMajorArcGlobalCanonicalAnchorError_normalized_eventually
#print axioms Erdos689.actualMajorArcGlobalCanonicalErrorBudget_normalized_le_majorant_eventually
#print axioms Erdos689.actualMajorArcGlobalCanonicalErrorBudget_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcGlobalCanonicalErrorBudget_original_tendsto_zero
#print axioms Erdos689.actualMajorArcGlobalCanonicalPrimeModel_normalized_tendsto_zero

end Erdos689
