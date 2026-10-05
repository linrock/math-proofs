module

public import ActualLeftVertexMajorIntegrated433

@[expose] public section


/-!
# Fully integrated actual three-form Siegel--Walfisz error

Every genuine Farey anchor has `n * |β| ≤ P / (κ*q)`. The true
support-divisor coefficients therefore have a common polynomial Abel
bound, including the negative center frequency `-2*d`. The ACTUAL
three-factor manuscript error is dominated by
`B(S,C,κ) * n^3 * P^3 * exp(-c*(log n)^(1/10))`. Its true anchor
width restores the missing `1/n`, and all genuine common-modulus cells,
deduplicated centers, and original coefficient pairs can be summed.
No rational-center sign or singular-series positivity is assumed.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Fixed actual-support constant controlling all three coefficient
frequencies on every logarithmic Farey anchor. -/
noncomputable def actualMajorArcSWLinearCoefficient
    (C κ : ℝ) (supportModulus : ℕ) : ℝ :=
  2 * C * (1 + 4 * Real.pi * supportModulus / κ)

/-- Fixed positive polynomial coefficient for the ORIGINAL fully expanded
three-factor Siegel--Walfisz/Abel cubic error. -/
noncomputable def actualMajorArcSWCubicCoefficient
    (C κ : ℝ) (supportModulus : ℕ) : ℝ :=
  3 * actualMajorArcSWLinearCoefficient C κ supportModulus *
    (1 + actualMajorArcSWLinearCoefficient C κ supportModulus) ^ 2

/-- Any actual coefficient frequency bounded by `2W` has the claimed
uniform progression error on the genuine `n|β|≤P/κ` anchor scale. -/
theorem actualMajorArcSW_progression_error_le
    (c C κ : ℝ) (hC : 0 ≤ C) (_hκ : 0 < κ)
    (n supportModulus cutoff : ℕ)
    (frequency : ℤ) (β : ℝ)
    (hcutoff : 1 ≤ cutoff)
    (hfrequency : |(frequency : ℝ)| ≤ 2 * (supportModulus : ℝ))
    (hbeta : (n : ℝ) * |β| ≤ (cutoff : ℝ) / κ) :
    2 * ternaryMajorArcProgressionError c C n frequency β ≤
      actualMajorArcSWLinearCoefficient C κ supportModulus *
        (n : ℝ) * cutoff *
        Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10)) := by
  have hcutoffReal : (1 : ℝ) ≤ (cutoff : ℝ) := by
    exact_mod_cast hcutoff
  have htwist :
      (n : ℝ) * |(frequency : ℝ) * β| ≤
        (2 * (supportModulus : ℝ)) * ((cutoff : ℝ) / κ) := by
    rw [abs_mul]
    calc
      (n : ℝ) * (|(frequency : ℝ)| * |β|) =
          |(frequency : ℝ)| * ((n : ℝ) * |β|) := by ring
      _ ≤ (2 * (supportModulus : ℝ)) * ((cutoff : ℝ) / κ) := by
        exact mul_le_mul hfrequency hbeta (by positivity) (by positivity)
  have hphase :
      1 + 2 * Real.pi * (n : ℝ) * |(frequency : ℝ) * β| ≤
        (cutoff : ℝ) *
          (1 + 4 * Real.pi * (supportModulus : ℝ) / κ) := by
    have hpi := Real.pi_pos
    calc
      1 + 2 * Real.pi * (n : ℝ) * |(frequency : ℝ) * β| ≤
          1 + 2 * Real.pi *
            ((2 * (supportModulus : ℝ)) * ((cutoff : ℝ) / κ)) := by
        nlinarith
      _ ≤ (cutoff : ℝ) +
          2 * Real.pi *
            ((2 * (supportModulus : ℝ)) * ((cutoff : ℝ) / κ)) := by
        linarith
      _ = _ := by ring
  unfold ternaryMajorArcProgressionError
    actualMajorArcSWLinearCoefficient
  calc
    2 * (C * n * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) *
      (1 + 2 * Real.pi * n * |(frequency : ℝ) * β|)) ≤
      2 * (C * n * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) *
        ((cutoff : ℝ) *
          (1 + 4 * Real.pi * (supportModulus : ℝ) / κ))) := by
        gcongr
    _ = _ := by ring

/-- The actual cubic error loses exactly one SW exponential factor and
costs at most three powers of the TRUE Farey cutoff. -/
theorem actualMajorArcSW_cubic_error_polynomial_le
    (c C κ : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hκ : 0 < κ)
    (n supportModulus cutoff modulus
      labelResidue leftResidue rightResidue a d : ℕ)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) (β : ℝ)
    (hsupportModulus : 0 < supportModulus)
    (hcutoff : 1 ≤ cutoff)
    (hmodulus : 0 < modulus)
    (ha : a ≤ supportModulus)
    (hd : d ≤ supportModulus)
    (hlabelUpper : labelUpper ≤ n)
    (hleftUpper : leftUpper ≤ n)
    (hrightUpper : rightUpper ≤ n)
    (hbeta : (n : ℝ) * |β| ≤ (cutoff : ℝ) / κ) :
    ternaryManuscriptMajorArcCubicError
      c C n modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper rightLower rightUpper
      numerator β ≤
      actualMajorArcSWCubicCoefficient C κ supportModulus *
        (n : ℝ) ^ 3 * (cutoff : ℝ) ^ 3 *
        Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10)) := by
  let A := actualMajorArcSWLinearCoefficient C κ supportModulus
  let decay := Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10))
  let E := A * (n : ℝ) * (cutoff : ℝ) * decay
  have hA : 0 ≤ A := by
    dsimp [A, actualMajorArcSWLinearCoefficient]
    positivity
  have hdecay : 0 ≤ decay := (Real.exp_pos _).le
  have hdecayOne : decay ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have hpower : 0 ≤ Real.log (n : ℝ) ^ ((1 : ℝ) / 10) := by
      positivity
    nlinarith
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hW : (1 : ℝ) ≤ (supportModulus : ℝ) := by
    exact_mod_cast hsupportModulus
  have hlabelFreq : |((1 : ℤ) : ℝ)| ≤
      2 * (supportModulus : ℝ) := by
    norm_num
    linarith
  have hleftFreq : |((a : ℤ) : ℝ)| ≤
      2 * (supportModulus : ℝ) := by
    norm_num
    have ha' : (a : ℝ) ≤ supportModulus := by exact_mod_cast ha
    nlinarith
  have hrightFreq : |((-2 * (d : ℤ) : ℤ) : ℝ)| ≤
      2 * (supportModulus : ℝ) := by
    push_cast
    have hd' : (d : ℝ) ≤ supportModulus := by exact_mod_cast hd
    rw [abs_of_nonpos (by
      nlinarith [Nat.cast_nonneg (α := ℝ) d])]
    nlinarith
  have hlabel := actualMajorArcSW_progression_error_le
    c C κ hC hκ n supportModulus cutoff 1 β
      hcutoff hlabelFreq hbeta
  have hleft := actualMajorArcSW_progression_error_le
    c C κ hC hκ n supportModulus cutoff (a : ℤ) β
      hcutoff hleftFreq hbeta
  have hright := actualMajorArcSW_progression_error_le
    c C κ hC hκ n supportModulus cutoff (-2 * (d : ℤ)) β
      hcutoff hrightFreq hbeta
  have hthree := ternaryManuscriptMajorArcCubicError_le
    c C hC n modulus labelResidue leftResidue rightResidue a d
      hmodulus labelLower labelUpper leftLower leftUpper
      rightLower rightUpper hlabelUpper hleftUpper hrightUpper
      numerator β E hE hlabel hleft hright
  have hEnod : E ≤ A * (n : ℝ) * (cutoff : ℝ) := by
    dsimp [E]
    calc
      A * (n : ℝ) * (cutoff : ℝ) * decay ≤
        A * (n : ℝ) * (cutoff : ℝ) * 1 := by gcongr
      _ = _ := by ring
  have hcutoffReal : (1 : ℝ) ≤ (cutoff : ℝ) := by
    exact_mod_cast hcutoff
  have hnscaled : (n : ℝ) ≤ (n : ℝ) * cutoff := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hsum :
      (n : ℝ) + E ≤ (1 + A) * (n : ℝ) * cutoff := by
    nlinarith
  calc
    _ ≤ 3 * E * ((n : ℝ) + E) ^ 2 := hthree
    _ ≤ 3 * E * ((1 + A) * (n : ℝ) * cutoff) ^ 2 := by
      gcongr
    _ = actualMajorArcSWCubicCoefficient C κ supportModulus *
      (n : ℝ) ^ 3 * (cutoff : ℝ) ^ 3 * decay := by
        dsimp [E, A, actualMajorArcSWCubicCoefficient]
        ring

/-- Every point in the ORIGINAL shifted Farey anchor satisfies the true
uniform Abel bound, with its actual original denominator and cutoff. -/
theorem actualMajorArcSW_true_anchor_beta_eventually
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (supportModulus : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ anchor ∈ actualShiftedFareyAnchors supportModulus
          (compatibleLogMinorCutoff n),
        ∀ α ∈ shiftedFareyAnchorArc supportModulus
            (fullyCompatibleFareyCutoff lower n)
            anchor.1 anchor.2.1 anchor.2.2,
          (n : ℝ) *
            |α - shiftedFareyAnchorCenter supportModulus
              anchor.1 anchor.2.1 anchor.2.2| ≤
            (compatibleLogMinorCutoff n : ℝ) / κ := by
  filter_upwards
    [fullyCompatibleFareyCutoff_major_beta_eventually
      lower κ hκ hlower] with n hn
  intro anchor hanchor α hα
  have hpositive := (actualShiftedFareyAnchors_denominator_bounds
    supportModulus (compatibleLogMinorCutoff n) anchor hanchor).1
  have hball :
      |α - shiftedFareyAnchorCenter supportModulus
        anchor.1 anchor.2.1 anchor.2.2| ≤
          1 / ((anchor.1 : ℝ) *
            (fullyCompatibleFareyCutoff lower n + 1 : ℕ)) := by
    simpa [shiftedFareyAnchorArc, Real.dist_eq] using hα
  have hfirst := hn anchor.1 hpositive
    (α - shiftedFareyAnchorCenter supportModulus
      anchor.1 anchor.2.1 anchor.2.2) hball
  have hq : (1 : ℝ) ≤ (anchor.1 : ℝ) := by
    exact_mod_cast hpositive
  have hκq : κ ≤ κ * (anchor.1 : ℝ) := by nlinarith
  exact hfirst.trans
    (div_le_div_of_nonneg_left (by positivity) hκ hκq)

/-- The ACTUAL manuscript cubic SW error for every support-divisor
coefficient pair and EVERY original shifted Farey anchor has a uniform
`B*n^3*P^3*exp(-c*(log n)^(1/10))` bound on the whole genuine arc. -/
theorem actualMajorArcSW_true_anchor_cubic_error_eventually
    (S : Finset ℕ) (hsupport : ∀ p ∈ S, p.Prime)
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a ∈ (∏ p ∈ S, p).divisors,
        ∀ d ∈ (∏ p ∈ S, p).divisors,
          ∀ anchor ∈ actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n),
            ∀ labelResidue leftResidue rightResidue
              labelLower labelUpper leftLower leftUpper
              rightLower rightUpper : ℕ,
              labelUpper ≤ n → leftUpper ≤ n → rightUpper ≤ n →
              ∀ numerator : ℤ,
                ∀ α ∈ shiftedFareyAnchorArc (∏ p ∈ S, p)
                    (fullyCompatibleFareyCutoff lower n)
                    anchor.1 anchor.2.1 anchor.2.2,
                  ternaryManuscriptMajorArcCubicError
                    c C n (actualMajorArcLcmResidueModulus S anchor.1)
                    labelResidue leftResidue rightResidue a d
                    labelLower labelUpper leftLower leftUpper
                    rightLower rightUpper numerator
                    (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
                      anchor.1 anchor.2.1 anchor.2.2) ≤
                    actualMajorArcSWCubicCoefficient C κ (∏ p ∈ S, p) *
                      (n : ℝ) ^ 3 *
                      (compatibleLogMinorCutoff n : ℝ) ^ 3 *
                      Real.exp (-c * Real.log (n : ℝ) ^
                        ((1 : ℝ) / 10)) := by
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  filter_upwards
    [actualMajorArcSW_true_anchor_beta_eventually
      lower κ hκ hlower (∏ p ∈ S, p),
      compatibleLogMinorCutoff_tendsto_atTop.eventually
        (eventually_ge_atTop (1 : ℕ))] with n hn hP
  intro a ha d hd anchor hanchor labelResidue leftResidue rightResidue
    labelLower labelUpper leftLower leftUpper rightLower rightUpper
    hlabel hleft hright numerator α hα
  have hadiv := (Nat.mem_divisors.mp ha).1
  have hddiv := (Nat.mem_divisors.mp hd).1
  have haW : a ≤ ∏ p ∈ S, p := Nat.le_of_dvd hW hadiv
  have hdW : d ≤ ∏ p ∈ S, p := Nat.le_of_dvd hW hddiv
  have hanchorPos := (actualShiftedFareyAnchors_denominator_bounds
    (∏ p ∈ S, p) (compatibleLogMinorCutoff n) anchor hanchor).1
  have hL := actualMajorArcLcmResidueModulus_pos
    S anchor.1 hanchorPos hsupport
  exact actualMajorArcSW_cubic_error_polynomial_le
    c C κ hc hC hκ n (∏ p ∈ S, p)
      (compatibleLogMinorCutoff n)
      (actualMajorArcLcmResidueModulus S anchor.1)
      labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator
      (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
        anchor.1 anchor.2.1 anchor.2.2)
      hW hP hL haW hdW hlabel hleft hright
      (hn anchor hanchor α hα)

/-- Integrating ONE genuine switched-unit manuscript cubic SW error over
its true clipped original-denominator Farey anchor restores `1/n`; its
quadratically normalized bound is `2*B/κ * P^4 * exp(-c log^.1)`. -/
theorem actualMajorArcSW_true_anchor_cell_integral_normalized_eventually
    (S : Finset ℕ) (hsupport : ∀ p ∈ S, p.Prime)
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ))
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a ∈ (∏ p ∈ S, p).divisors,
        ∀ d ∈ (∏ p ∈ S, p).divisors,
          ∀ anchor ∈ actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n),
            ∀ labelResidue leftResidue rightResidue
              labelLower labelUpper leftLower leftUpper
              rightLower rightUpper : ℕ,
              labelUpper ≤ n → leftUpper ≤ n → rightUpper ≤ n →
              ∀ numerator : ℤ,
                (∫ α in Set.Ioc (0 : ℝ) 1 ∩
                  shiftedFareyAnchorArc (∏ p ∈ S, p)
                    (fullyCompatibleFareyCutoff lower n)
                    anchor.1 anchor.2.1 anchor.2.2,
                  ternaryManuscriptMajorArcCubicError
                    c C n (actualMajorArcLcmResidueModulus S anchor.1)
                    labelResidue leftResidue rightResidue a d
                    labelLower labelUpper leftLower leftUpper
                    rightLower rightUpper numerator
                    (α - shiftedFareyAnchorCenter (∏ p ∈ S, p)
                      anchor.1 anchor.2.1 anchor.2.2)) /
                    (n : ℝ) ^ 2 ≤
                  (2 / κ) *
                    actualMajorArcSWCubicCoefficient C κ (∏ p ∈ S, p) *
                    (compatibleLogMinorCutoff n : ℝ) ^ 4 *
                    Real.exp (-c * Real.log (n : ℝ) ^
                      ((1 : ℝ) / 10)) := by
  filter_upwards
    [actualMajorArcSW_true_anchor_cubic_error_eventually
      S hsupport lower κ hκ hlower c C hc hC,
      actualMajorArcArchimedean_shifted_anchor_scaled_volume_eventually
        lower κ hκ hlower (∏ p ∈ S, p),
      eventually_ge_atTop (1 : ℕ)] with n hn hvolume hnpos
  intro a ha d hd anchor hanchor labelResidue leftResidue rightResidue
    labelLower labelUpper leftLower leftUpper rightLower rightUpper
    hlabel hleft hright numerator
  let W : ℕ := ∏ p ∈ S, p
  let P : ℕ := compatibleLogMinorCutoff n
  let region := Set.Ioc (0 : ℝ) 1 ∩
    shiftedFareyAnchorArc W (fullyCompatibleFareyCutoff lower n)
      anchor.1 anchor.2.1 anchor.2.2
  let B := actualMajorArcSWCubicCoefficient C κ W
  let decay := Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10))
  let bound := B * (n : ℝ) ^ 3 * (P : ℝ) ^ 3 * decay
  let error : ℝ → ℝ := fun α =>
    ternaryManuscriptMajorArcCubicError
      c C n (actualMajorArcLcmResidueModulus S anchor.1)
      labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper rightLower rightUpper
      numerator
      (α - shiftedFareyAnchorCenter W
        anchor.1 anchor.2.1 anchor.2.2)
  have hcont : Continuous error := by
    unfold error ternaryManuscriptMajorArcCubicError
      ternaryMajorArcProgressionError ternaryMajorArcIntervalModel
      ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hmeas : MeasurableSet region :=
    measurableSet_Ioc.inter Metric.isClosed_closedBall.measurableSet
  have hfinite : volume region < ⊤ :=
    (measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top
  have hint : IntegrableOn error region volume :=
    hcont.integrableOn_Ioc.mono_set Set.inter_subset_left
  have hcompare :
      (∫ α in region, error α) ≤ ∫ _α in region, bound := by
    apply setIntegral_mono_on hint
      (integrableOn_const hfinite.ne) hmeas
    intro α hα
    exact hn a ha d hd anchor hanchor
      labelResidue leftResidue rightResidue
      labelLower labelUpper leftLower leftUpper rightLower rightUpper
      hlabel hleft hright numerator α hα.2
  have hcompare' :
      (∫ α in region, error α) ≤ bound * (volume region).toReal := by
    calc
      _ ≤ ∫ _α in region, bound := hcompare
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul]
        change (volume region).toReal * bound =
          bound * (volume region).toReal
        ring
  have hpositive := (actualShiftedFareyAnchors_denominator_bounds
    W P anchor hanchor).1
  have hq : (1 : ℝ) ≤ (anchor.1 : ℝ) := by
    exact_mod_cast hpositive
  have hκq : κ ≤ κ * (anchor.1 : ℝ) := by nlinarith
  have hscale0 := hvolume anchor.1 hpositive
    anchor.2.1 anchor.2.2
  have hscale : (volume region).toReal * n ≤ 2 * (P : ℝ) / κ := by
    rw [Set.inter_comm] at hscale0
    exact hscale0.trans
      (div_le_div_of_nonneg_left (by positivity) hκ hκq)
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have hB : 0 ≤ B := by
    dsimp [B, actualMajorArcSWCubicCoefficient,
      actualMajorArcSWLinearCoefficient]
    positivity
  change (∫ α in region, error α) / (n : ℝ) ^ 2 ≤ _
  calc
    (∫ α in region, error α) / (n : ℝ) ^ 2 ≤
        (bound * (volume region).toReal) / (n : ℝ) ^ 2 := by
      gcongr
    _ = B * (P : ℝ) ^ 3 * decay *
      ((volume region).toReal * n) := by
        dsimp [bound]
        field_simp
    _ ≤ B * (P : ℝ) ^ 3 * decay *
      (2 * (P : ℝ) / κ) := by
        gcongr
    _ = _ := by ring

/-- The COMPLETE actual cubic SW error vanishes after summing all original
support-divisor coefficient pairs, all distinct shifted rational centers,
and every genuine `lcm(q,W)` triple cell with its true Farey width. -/
theorem actualMajorArcSW_all_coefficients_centers_cells_tendsto_zero
    (S : Finset ℕ) (κ : ℝ) (_hκ : 0 < κ)
    (c C : ℝ) (hc : 0 < c) (_hC : 0 ≤ C) :
    Tendsto
      (fun n : ℕ =>
        ((((∏ p ∈ S, p).divisors).card : ℝ) ^ 2) *
          ((shiftedFareyCenterClasses (∏ p ∈ S, p)
            (actualShiftedFareyAnchors (∏ p ∈ S, p)
              (compatibleLogMinorCutoff n))).card : ℝ) *
          (((∏ p ∈ S, p) * compatibleLogMinorCutoff n : ℕ) : ℝ) ^ 3 *
          ((2 / κ) *
            actualMajorArcSWCubicCoefficient C κ (∏ p ∈ S, p) *
            (compatibleLogMinorCutoff n : ℝ) ^ 4 *
            Real.exp (-c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10))))
      atTop (nhds 0) := by
  have hbase :=
    (actualMajorArcIntegrated_all_coefficients_siegel_decay_tendsto_zero
      S c hc 4).const_mul
        ((2 / κ) * actualMajorArcSWCubicCoefficient C κ (∏ p ∈ S, p))
  convert hbase using 1
  · ext n
    ring
  · norm_num


end Erdos689
