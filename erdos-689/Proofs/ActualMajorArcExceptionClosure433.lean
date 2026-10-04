module

public import ActualMajorArcGlobalErrorAssembly433
public import ActualMajorArcCorrectedModel433

@[expose] public section


/-!
# Exact exceptional closure for the genuine canonical major model

All quantities use the ORIGINAL support-divisor pairs, DISTINCT translated
major centers, canonical genuine WIDEST anchors, and exactly clipped Farey
arcs. The exceptional triple complement is signed and is disposed of only
after its actual integrated absolute value is bounded. No center, support
selector, incompatible residue, or true inverse-scale width is dropped.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The PURE switched-unit smooth canonical model, with every original
coefficient divisor, actual distinct center, and canonical widest arc. -/
noncomputable def actualMajorArcExceptionCanonicalSmoothMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target P Q : ℕ) (τ ell : ℝ) : ℝ :=
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
              (∏ p ∈ S, p) P Q center) α).re

/-- The ENTIRE genuine signed exceptional complement at precisely the
same original coefficient divisors, distinct centers, and widest arcs. -/
noncomputable def actualMajorArcExceptionCanonicalExceptionalMass
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
          actualMajorArcIntegratedAnchorExceptional
            S b n J target a d τ ell
            (actualMajorArcGlobalCanonicalWidestAnchor
              (∏ p ∈ S, p) P Q center) α).re

/-- EXACT original canonical decomposition. In particular the exceptional
contribution is retained with its actual sign, not discarded. -/
theorem actualMajorArcExceptionCanonicalModel_eq_smooth_add_exceptional
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target P Q : ℕ) (τ ell : ℝ) :
    actualMajorArcGlobalCanonicalModelMass
        S b n J target P Q τ ell =
      actualMajorArcExceptionCanonicalSmoothMass
          S b n target P Q τ ell +
        actualMajorArcExceptionCanonicalExceptionalMass
          S b n J target P Q τ ell := by
  classical
  unfold actualMajorArcGlobalCanonicalModelMass
    actualMajorArcExceptionCanonicalSmoothMass
    actualMajorArcExceptionCanonicalExceptionalMass
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro center hcenter
  let W : ℕ := ∏ p ∈ S, p
  let region : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩
    shiftedFareyCenterRegion W Q
      (actualShiftedFareyAnchors W P) center.val
  let anchor := actualMajorArcGlobalCanonicalWidestAnchor
    W P Q center
  have hsmooth : IntegrableOn
      (actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor)
      region volume :=
    (actualMajorArcIntegratedAnchorSmooth_continuous
      S b n target a d τ ell anchor).integrableOn_Ioc.mono_set
        Set.inter_subset_left
  have hexception : IntegrableOn
      (actualMajorArcIntegratedAnchorExceptional
        S b n J target a d τ ell anchor)
      region volume :=
    (actualMajorArcIntegratedAnchorExceptional_continuous
      S b n J target a d τ ell anchor).integrableOn_Ioc.mono_set
        Set.inter_subset_left
  rw [MeasureTheory.integral_add hsmooth hexception]
  rfl

/-- At EVERY true distinct center, the ACTUAL integrated signed exceptional
family is bounded by the precise known exceptional majorant. The original
canonical widest anchor supplies the indispensable genuine `1/n` width. -/
theorem actualMajorArcExceptionCanonicalAnchor_normalized_eventually
    (S : Finset ℕ) (b : ℕ → ℕ)
    (lower : ℕ → ℕ) (κ : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (J target a d : ℕ) (τ ell : ℝ),
        manuscriptRealLabelUpper τ ell n ≤ n →
        ∀ center : ActualMajorArcGlobalCenter
            (∏ p ∈ S, p) (compatibleLogMinorCutoff n),
          |(∫ α in Set.Ioc (0 : ℝ) 1 ∩
              shiftedFareyCenterRegion (∏ p ∈ S, p)
                (fullyCompatibleFareyCutoff lower n)
                (actualShiftedFareyAnchors (∏ p ∈ S, p)
                  (compatibleLogMinorCutoff n)) center.val,
              actualMajorArcIntegratedAnchorExceptional
                S b n J target a d τ ell
                (actualMajorArcGlobalCanonicalWidestAnchor
                  (∏ p ∈ S, p) (compatibleLogMinorCutoff n)
                  (fullyCompatibleFareyCutoff lower n) center) α).re| /
                (n : ℝ) ^ 2 ≤
            (2 / κ) * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 3 *
              (compatibleLogMinorCutoff n : ℝ) ^ 5 *
              (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2) := by
  classical
  filter_upwards
    [actualMajorArcArchimedean_shifted_anchor_scaled_volume_eventually
      lower κ hκ hlower (∏ p ∈ S, p)] with n hvolume
  intro J target a d τ ell hupper center
  let W : ℕ := ∏ p ∈ S, p
  let P : ℕ := compatibleLogMinorCutoff n
  let Q : ℕ := fullyCompatibleFareyCutoff lower n
  let anchor := actualMajorArcGlobalCanonicalWidestAnchor
    W P Q center
  have hspec := actualMajorArcGlobalCanonicalWidestAnchor_spec
    W P Q center
  have hbounds := actualShiftedFareyAnchors_denominator_bounds
    W P anchor hspec.1
  rw [hspec.2.2]
  let region : Set ℝ := Set.Ioc (0 : ℝ) 1 ∩
    shiftedFareyAnchorArc W Q anchor.1 anchor.2.1 anchor.2.2
  let exception : ℝ → ℂ := actualMajorArcIntegratedAnchorExceptional
    S b n J target a d τ ell anchor
  let E : ℝ := (((W * P) ^ 3 : ℕ) : ℝ) *
    ((P : ℝ) * Real.log n * ((n : ℝ) * Real.log n) ^ 2)
  have hpoint : ∀ α ∈ region, ‖exception α‖ ≤ E := by
    intro α hα
    dsimp [exception, E, W, P]
    unfold actualMajorArcIntegratedAnchorExceptional
    exact actualMajorArcExceptionalCellSum_cutoff_norm_le
      S b n J target a d anchor.1 (compatibleLogMinorCutoff n)
      τ ell α hbounds.1 hbounds.2 hsupport hupper
  have hmeasurable : MeasurableSet region :=
    measurableSet_Ioc.inter Metric.isClosed_closedBall.measurableSet
  have hfinite : volume region < ⊤ :=
    (measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top
  have hintegrable : IntegrableOn (fun α => ‖exception α‖)
      region volume :=
    (actualMajorArcIntegratedAnchorExceptional_continuous
      S b n J target a d τ ell anchor).norm.integrableOn_Ioc.mono_set
        Set.inter_subset_left
  have hintegral : ‖∫ α in region, exception α‖ ≤
      (volume region).toReal * E := by
    calc
      ‖∫ α in region, exception α‖ ≤
          ∫ α in region, ‖exception α‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ _α in region, E := by
        apply setIntegral_mono_on hintegrable
          (integrableOn_const hfinite.ne) hmeasurable
        exact hpoint
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul]
        rfl
  have hdenominator : (1 : ℝ) ≤ (anchor.1 : ℝ) := by
    exact_mod_cast hbounds.1
  have hκdenominator : κ ≤ κ * (anchor.1 : ℝ) := by nlinarith
  have hwidth0 := hvolume anchor.1 hbounds.1
    anchor.2.1 anchor.2.2
  rw [Set.inter_comm] at hwidth0
  have hwidth : (volume region).toReal * n ≤
      2 * (P : ℝ) / κ :=
    hwidth0.trans
      (div_le_div_of_nonneg_left (by positivity) hκ hκdenominator)
  change |(∫ α in region, exception α).re| /
    (n : ℝ) ^ 2 ≤ _
  calc
    |(∫ α in region, exception α).re| / (n : ℝ) ^ 2 ≤
        ‖∫ α in region, exception α‖ / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right
        (Complex.abs_re_le_norm _) (sq_nonneg _)
    _ ≤ ((volume region).toReal * E) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hintegral (sq_nonneg _)
    _ = ((volume region).toReal * n) *
        ((W : ℝ) ^ 3 * (P : ℝ) ^ 4) *
          (((n : ℝ) * Real.log (n : ℝ) ^ 3) /
            (n : ℝ) ^ 2) := by
      dsimp [E]
      push_cast
      ring
    _ ≤ (2 * (P : ℝ) / κ) *
        ((W : ℝ) ^ 3 * (P : ℝ) ^ 4) *
          (((n : ℝ) * Real.log (n : ℝ) ^ 3) /
            (n : ℝ) ^ 2) := by
      gcongr
    _ = _ := by
      dsimp [W, P]
      ring

/-- The proved exceptional majorant after EVERY original support-divisor
pair and every DISTINCT actual translated major center are counted. -/
noncomputable def actualMajorArcExceptionGlobalMajorant
    (S : Finset ℕ) (κ : ℝ) (n : ℕ) : ℝ :=
  ((((∏ p ∈ S, p).divisors).card : ℝ) ^ 2) *
    (((shiftedFareyCenterClasses (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p)
        (compatibleLogMinorCutoff n))).card : ℝ) *
      ((2 / κ) * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 3 *
        (compatibleLogMinorCutoff n : ℝ) ^ 5 *
        (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2)))

/-- The full original-support, all-center exceptional majorant vanishes. -/
theorem actualMajorArcExceptionGlobalMajorant_tendsto_zero
    (S : Finset ℕ) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto
      (fun n : ℕ => actualMajorArcExceptionGlobalMajorant S κ n)
      atTop (nhds 0) := by
  exact actualMajorArcIntegrated_all_coefficients_exceptional_tendsto_zero
    S κ hκ

/-- The REAL signed canonical exceptional mass, over ALL support-divisor
pairs and true deduplicated centers, is bounded after quadratic
normalization by the proved all-center exceptional majorant. -/
theorem actualMajorArcExceptionCanonicalMass_normalized_le_majorant_eventually
    (S : Finset ℕ) (b : ℕ → ℕ)
    (lower : ℕ → ℕ) (κ : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (τ ell : ℝ) (hτ : 0 ≤ τ) (hell : 0 ≤ ell)
    (hstrip : τ + ell < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ J target : ℕ,
      |actualMajorArcExceptionCanonicalExceptionalMass
          S b n J target (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff lower n) τ ell| /
        (n : ℝ) ^ 2 ≤
          actualMajorArcExceptionGlobalMajorant S κ n := by
  classical
  filter_upwards
    [actualMajorArcExceptionCanonicalAnchor_normalized_eventually
      S b lower κ hsupport hκ hlower,
      eventually_gt_atTop (0 : ℕ)] with n hanchor hn
  intro J target
  obtain ⟨_, hupper, _, _⟩ :=
    actualMajorArcGlobal_true_window_endpoints
      S τ ell n hsupport hn hτ hell hstrip
  let W : ℕ := ∏ p ∈ S, p
  let P : ℕ := compatibleLogMinorCutoff n
  let Q : ℕ := fullyCompatibleFareyCutoff lower n
  let centers := shiftedFareyCenterClasses W
    (actualShiftedFareyAnchors W P)
  let rate : ℝ := (2 / κ) * (W : ℝ) ^ 3 * (P : ℝ) ^ 5 *
    (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2)
  let contribution : ℕ → ℕ → ActualMajorArcGlobalCenter W P → ℝ :=
    fun a d center =>
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion W Q
          (actualShiftedFareyAnchors W P) center.val,
        actualMajorArcIntegratedAnchorExceptional
          S b n J target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            W P Q center) α).re
  have hsingle (a d : ℕ) (center : ActualMajorArcGlobalCenter W P) :
      |contribution a d center / (n : ℝ) ^ 2| ≤ rate := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
    exact hanchor J target a d τ ell hupper center
  have hcenter (a d : ℕ) :
      |∑ center ∈ centers.attach,
        contribution a d center / (n : ℝ) ^ 2| ≤
        ∑ _center ∈ centers.attach, rate := by
    calc
      |∑ center ∈ centers.attach,
        contribution a d center / (n : ℝ) ^ 2| ≤
          ∑ center ∈ centers.attach,
            |contribution a d center / (n : ℝ) ^ 2| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _center ∈ centers.attach, rate := by
        apply Finset.sum_le_sum
        intro center hcenter
        exact hsingle a d center
  have hdivisor (a : ℕ) :
      |∑ d ∈ W.divisors,
        ∑ center ∈ centers.attach,
          contribution a d center / (n : ℝ) ^ 2| ≤
        ∑ d ∈ W.divisors,
          ∑ _center ∈ centers.attach, rate := by
    calc
      |∑ d ∈ W.divisors,
        ∑ center ∈ centers.attach,
          contribution a d center / (n : ℝ) ^ 2| ≤
        ∑ d ∈ W.divisors,
          |∑ center ∈ centers.attach,
            contribution a d center / (n : ℝ) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ W.divisors,
          ∑ _center ∈ centers.attach, rate := by
        apply Finset.sum_le_sum
        intro d hd
        exact hcenter a d
  have htotal :
      |∑ a ∈ W.divisors,
        ∑ d ∈ W.divisors,
          ∑ center ∈ centers.attach,
            contribution a d center / (n : ℝ) ^ 2| ≤
        ∑ a ∈ W.divisors,
          ∑ d ∈ W.divisors,
            ∑ _center ∈ centers.attach, rate := by
    calc
      |∑ a ∈ W.divisors,
        ∑ d ∈ W.divisors,
          ∑ center ∈ centers.attach,
            contribution a d center / (n : ℝ) ^ 2| ≤
        ∑ a ∈ W.divisors,
          |∑ d ∈ W.divisors,
            ∑ center ∈ centers.attach,
              contribution a d center / (n : ℝ) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ W.divisors,
          ∑ d ∈ W.divisors,
            ∑ _center ∈ centers.attach, rate := by
        apply Finset.sum_le_sum
        intro a ha
        exact hdivisor a
  calc
    |actualMajorArcExceptionCanonicalExceptionalMass
        S b n J target P Q τ ell| / (n : ℝ) ^ 2 =
      |∑ a ∈ W.divisors,
        ∑ d ∈ W.divisors,
          ∑ center ∈ centers.attach,
            contribution a d center / (n : ℝ) ^ 2| := by
      unfold actualMajorArcExceptionCanonicalExceptionalMass
      change
        |∑ a ∈ W.divisors,
          ∑ d ∈ W.divisors,
            ∑ center ∈ centers.attach,
              contribution a d center| / (n : ℝ) ^ 2 = _
      calc
        |∑ a ∈ W.divisors,
          ∑ d ∈ W.divisors,
            ∑ center ∈ centers.attach,
              contribution a d center| / (n : ℝ) ^ 2 =
          |(∑ a ∈ W.divisors,
            ∑ d ∈ W.divisors,
              ∑ center ∈ centers.attach,
                contribution a d center) / (n : ℝ) ^ 2| := by
            rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
        _ = _ := by
          congr 1
          simp_rw [Finset.sum_div]
    _ ≤ ∑ a ∈ W.divisors,
          ∑ d ∈ W.divisors,
            ∑ _center ∈ centers.attach, rate := htotal
    _ = actualMajorArcExceptionGlobalMajorant S κ n := by
      unfold actualMajorArcExceptionGlobalMajorant
      dsimp [W, P, centers, rate]
      simp
      ring

/-- The COMPLETE ACTUAL signed canonical exceptional mass is `o(n²)`,
including all true support-divisor pairs and every distinct genuine center. -/
theorem actualMajorArcExceptionCanonicalMass_normalized_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (lower : ℕ → ℕ) (κ : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (J target : ℕ) (τ ell : ℝ)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell)
    (hstrip : τ + ell < 1) :
    Tendsto
      (fun n : ℕ =>
        |actualMajorArcExceptionCanonicalExceptionalMass
            S b n J target (compatibleLogMinorCutoff n)
            (fullyCompatibleFareyCutoff lower n) τ ell| /
          (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      div_nonneg (abs_nonneg _) (sq_nonneg _)
  · filter_upwards
      [actualMajorArcExceptionCanonicalMass_normalized_le_majorant_eventually
        S b lower κ hsupport hκ hlower τ ell hτ hell hstrip]
        with n hn
    exact hn J target
  · exact actualMajorArcExceptionGlobalMajorant_tendsto_zero S κ hκ

/-- At the TRUE original manuscript lower endpoint and Farey scale, the
entire genuinely signed exceptional complement is unconditionally `o(n²)`. -/
theorem actualMajorArcExceptionCanonicalMass_original_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (J target : ℕ) (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    Tendsto
      (fun n : ℕ =>
        |actualMajorArcExceptionCanonicalExceptionalMass
            S b n J target (compatibleLogMinorCutoff n)
            (fullyCompatibleFareyCutoff
              (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell| /
          (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  exact actualMajorArcExceptionCanonicalMass_normalized_tendsto_zero
    S b (fun m => Nat.floor (τ * (m : ℝ))) (τ / 2)
    hsupport (by positivity)
    (actualMajorArc_real_lower_floor_eventually_linear τ hτ)
    J target τ ell hτ.le hell.le (by nlinarith)

/-- COMPLETE unconditional original analytic closure: the ACTUAL
coefficient-summed, deduplicated prime major mass equals the PURE genuine
canonical-widest switched-unit smooth model up to `o(n²)`. All true SW,
proper-prime-power, and signed nonunit/incompatible exceptional families
have been rigorously eliminated while preserving original arc geometry. -/
theorem actualMajorArcException_prime_minus_pure_smooth_tendsto_zero
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
          actualMajorArcExceptionCanonicalSmoothMass
            S b n target (compatibleLogMinorCutoff n)
            (fullyCompatibleFareyCutoff
              (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell| /
              (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hmodel := actualMajorArcGlobalCanonicalPrimeModel_normalized_tendsto_zero
    S b J target τ ell hsupport htarget hτ hell hstrip
  have hexception := actualMajorArcExceptionCanonicalMass_original_tendsto_zero
    S b J target τ ell hsupport hτ hell hstrip
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      div_nonneg (abs_nonneg _) (sq_nonneg _)
  · exact Eventually.of_forall fun n => by
      let P := compatibleLogMinorCutoff n
      let Q := fullyCompatibleFareyCutoff
        (fun m => Nat.floor (τ * (m : ℝ))) n
      let actual := actualDeduplicatedMajorPrimeMass
        S b n J target P Q τ ell
      let smooth := actualMajorArcExceptionCanonicalSmoothMass
        S b n target P Q τ ell
      let model := actualMajorArcGlobalCanonicalModelMass
        S b n J target P Q τ ell
      let exception := actualMajorArcExceptionCanonicalExceptionalMass
        S b n J target P Q τ ell
      have hsplit : model = smooth + exception :=
        actualMajorArcExceptionCanonicalModel_eq_smooth_add_exceptional
          S b n J target P Q τ ell
      have hidentity : actual - smooth =
          (actual - model) + exception := by
        rw [hsplit]
        ring
      change |actual - smooth| / (n : ℝ) ^ 2 ≤
        |actual - model| / (n : ℝ) ^ 2 +
          |exception| / (n : ℝ) ^ 2
      calc
        |actual - smooth| / (n : ℝ) ^ 2 =
            |(actual - model) + exception| / (n : ℝ) ^ 2 := by
              rw [hidentity]
        _ ≤ (|actual - model| + |exception|) / (n : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right
            (abs_add_le _ _) (sq_nonneg _)
        _ = _ := by ring
  · simpa using hmodel.add hexception

#print axioms Erdos689.actualMajorArcExceptionCanonicalModel_eq_smooth_add_exceptional
#print axioms Erdos689.actualMajorArcExceptionCanonicalAnchor_normalized_eventually
#print axioms Erdos689.actualMajorArcExceptionGlobalMajorant_tendsto_zero
#print axioms Erdos689.actualMajorArcExceptionCanonicalMass_normalized_le_majorant_eventually
#print axioms Erdos689.actualMajorArcExceptionCanonicalMass_normalized_tendsto_zero
#print axioms Erdos689.actualMajorArcExceptionCanonicalMass_original_tendsto_zero
#print axioms Erdos689.actualMajorArcException_prime_minus_pure_smooth_tendsto_zero

end Erdos689
