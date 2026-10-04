module

public import ThreePrimeMajorArcClosure433

@[expose] public section


/-!
# Quantitative central-arc Siegel--Walfisz error for Erdős #689

The local cubic major-arc model has a genuinely exponentially decaying error.
These lemmas keep the actual interval model and affine coefficient explicit.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- A true interval major-arc model has norm at most its actual interval
cardinality; the residue-density and rational-phase factors never enlarge it. -/
theorem ternaryMajorArcIntervalModel_norm_le_card
    (lower upper modulus residue : ℕ)
    (frequency numerator : ℤ) (β : ℝ)
    (hmodulus : 0 < modulus) :
    ‖ternaryMajorArcIntervalModel
      lower upper modulus residue frequency numerator β‖ ≤
      ((Finset.Ico lower upper).card : ℝ) := by
  have htotient : 0 < modulus.totient := Nat.totient_pos.mpr hmodulus
  have hfactor : ‖(1 / (modulus.totient : ℂ))‖ ≤ (1 : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
    exact (div_le_one (by exact_mod_cast htotient)).mpr (by
      exact_mod_cast htotient)
  unfold ternaryMajorArcIntervalModel
  rw [norm_mul, GoldbachChain.e_norm, one_mul, norm_mul]
  calc
    ‖(1 / (modulus.totient : ℂ))‖ *
        ‖ternaryExponentialSum (Finset.Ico lower upper)
          (fun _ => 1) frequency β‖ ≤
      1 * ‖ternaryExponentialSum (Finset.Ico lower upper)
          (fun _ => 1) frequency β‖ := by gcongr
    _ = ‖ternaryExponentialSum (Finset.Ico lower upper)
          (fun _ => 1) frequency β‖ := one_mul _
    _ ≤ ∑ n ∈ Finset.Ico lower upper,
      ‖(1 : ℂ) * GoldbachChain.e ((frequency : ℝ) * n * β)‖ :=
      norm_sum_le _ _
    _ = ((Finset.Ico lower upper).card : ℝ) := by
      simp [GoldbachChain.e_norm]

/-- The true Siegel--Walfisz exponential decay tends to zero along the
natural manuscript scale, with the actual exponent `1/10` from the imported
Goldbach proof. -/
theorem ternary_siegel_walfisz_decay_tendsto_zero
    (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun n : ℕ => Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpower :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ ((1 : ℝ) / 10))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hlog
  have hscaled :
      Tendsto (fun n : ℕ => c * Real.log (n : ℝ) ^ ((1 : ℝ) / 10))
        atTop atTop :=
    hpower.const_mul_atTop hc
  simpa [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled

/-- On the true central-arc scale `n * β ≤ 1`, every individual
coefficient-dilated Abel/Siegel--Walfisz error has an explicit fixed-
coefficient `O(n exp(-c log(n)^(1/10)))` majorant. -/
theorem ternaryMajorArcProgressionError_central_le
    (c C : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (frequency : ℤ) (β : ℝ)
    (hβ : 0 ≤ β) (hcentral : (n : ℝ) * β ≤ 1) :
    2 * ternaryMajorArcProgressionError c C n frequency β ≤
      (2 * C * (1 + 2 * Real.pi * |(frequency : ℝ)|)) *
        (n : ℝ) * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) := by
  have hfrequency : 0 ≤ |(frequency : ℝ)| := abs_nonneg _
  have htwist :
      (n : ℝ) * |(frequency : ℝ) * β| ≤ |(frequency : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hβ]
    nlinarith [mul_nonneg hfrequency
      (sub_nonneg.mpr hcentral)]
  unfold ternaryMajorArcProgressionError
  have hexp : 0 ≤ Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) :=
    (Real.exp_pos _).le
  have htwistPi :
      2 * Real.pi * n * |(frequency : ℝ) * β| ≤
        2 * Real.pi * |(frequency : ℝ)| := by
    calc
      2 * Real.pi * n * |(frequency : ℝ) * β| =
        (2 * Real.pi) * ((n : ℝ) * |(frequency : ℝ) * β|) := by ring
      _ ≤ (2 * Real.pi) * |(frequency : ℝ)| :=
        mul_le_mul_of_nonneg_left htwist (by positivity)
  calc
    2 * (C * n * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) *
          (1 + 2 * Real.pi * n * |(frequency : ℝ) * β|)) ≤
      2 * (C * n * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) *
          (1 + 2 * Real.pi * |(frequency : ℝ)|)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hexp))
        (by norm_num)
    _ = (2 * C * (1 + 2 * Real.pi * |(frequency : ℝ)|)) *
          (n : ℝ) * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) := by
      ring

/-- The explicit polynomial majorant for the *integrated* cubic central-arc
error, normalized by its natural `n²` scale, vanishes for every fixed
coefficient constant. -/
theorem ternary_central_cubic_error_normalized_majorant_tendsto_zero
    (c A : ℝ) (hc : 0 < c) :
    Tendsto
      (fun n : ℕ =>
        3 * A * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) *
          (1 + A * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10))) ^ 2)
      atTop (nhds 0) := by
  have hdecay := ternary_siegel_walfisz_decay_tendsto_zero c hc
  have hscaled :
      Tendsto
        (fun n : ℕ => A * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)))
        atTop (nhds 0) := by
    simpa using hdecay.const_mul A
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hfactor :
      Tendsto
        (fun n : ℕ =>
          (1 + A * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10))) ^ 2)
        atTop (nhds 1) := by
    simpa using (hone.add hscaled).pow 2
  have hlead :
      Tendsto
        (fun n : ℕ =>
          3 * A * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)))
        atTop (nhds 0) := by
    simpa using hdecay.const_mul (3 * A)
  simpa using hlead.mul hfactor

/-- Exact domination of the *actual defined cubic manuscript error* by a
single common one-factor error.  In particular, no surrogate interval model
or omitted residue-density coefficient is used. -/
theorem ternaryManuscriptMajorArcCubicError_le
    (c C : ℝ) (hC : 0 ≤ C)
    (n modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (hlabelUpper : labelUpper ≤ n)
    (hleftUpper : leftUpper ≤ n)
    (hrightUpper : rightUpper ≤ n)
    (numerator : ℤ) (β E : ℝ)
    (hE : 0 ≤ E)
    (hlabel : 2 * ternaryMajorArcProgressionError c C n 1 β ≤ E)
    (hleft : 2 * ternaryMajorArcProgressionError c C n (a : ℤ) β ≤ E)
    (hright :
      2 * ternaryMajorArcProgressionError c C n (-2 * (d : ℤ)) β ≤ E) :
    ternaryManuscriptMajorArcCubicError
        c C n modulus labelResidue leftResidue rightResidue a d
        labelLower labelUpper leftLower leftUpper
        rightLower rightUpper numerator β ≤
      3 * E * ((n : ℝ) + E) ^ 2 := by
  have hlabelModel :
      ‖ternaryMajorArcIntervalModel
        labelLower labelUpper modulus labelResidue 1 numerator β‖ ≤
        (n : ℝ) := by
    calc
      _ ≤ ((Finset.Ico labelLower labelUpper).card : ℝ) :=
        ternaryMajorArcIntervalModel_norm_le_card
          labelLower labelUpper modulus labelResidue 1 numerator β hmodulus
      _ ≤ (n : ℝ) := by
        exact_mod_cast (show (Finset.Ico labelLower labelUpper).card ≤ n by
          simpa using (Nat.sub_le labelUpper labelLower).trans hlabelUpper)
  have hleftModel :
      ‖ternaryMajorArcIntervalModel
        leftLower leftUpper modulus leftResidue (a : ℤ) numerator β‖ ≤
        (n : ℝ) := by
    calc
      _ ≤ ((Finset.Ico leftLower leftUpper).card : ℝ) :=
        ternaryMajorArcIntervalModel_norm_le_card
          leftLower leftUpper modulus leftResidue (a : ℤ) numerator β hmodulus
      _ ≤ (n : ℝ) := by
        exact_mod_cast (show (Finset.Ico leftLower leftUpper).card ≤ n by
          simpa using (Nat.sub_le leftUpper leftLower).trans hleftUpper)
  have hrightModel :
      ‖ternaryMajorArcIntervalModel
        rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β‖ ≤ (n : ℝ) := by
    calc
      _ ≤ ((Finset.Ico rightLower rightUpper).card : ℝ) :=
        ternaryMajorArcIntervalModel_norm_le_card
          rightLower rightUpper modulus rightResidue
          (-2 * (d : ℤ)) numerator β hmodulus
      _ ≤ (n : ℝ) := by
        exact_mod_cast (show (Finset.Ico rightLower rightUpper).card ≤ n by
          simpa using (Nat.sub_le rightUpper rightLower).trans hrightUpper)
  have hnonneg (frequency : ℤ) :
      0 ≤ 2 * ternaryMajorArcProgressionError c C n frequency β := by
    unfold ternaryMajorArcProgressionError
    positivity
  have hlabelNonneg := hnonneg 1
  have hleftNonneg := hnonneg (a : ℤ)
  have hrightNonneg := hnonneg (-2 * (d : ℤ))
  have hnE : (n : ℝ) ≤ (n : ℝ) + E := by linarith
  dsimp [ternaryManuscriptMajorArcCubicError]
  calc
    _ ≤ E * ((n : ℝ) + E) * ((n : ℝ) + E) +
        (n : ℝ) * E * ((n : ℝ) + E) +
        (n : ℝ) * (n : ℝ) * E := by
      gcongr
    _ ≤ E * ((n : ℝ) + E) * ((n : ℝ) + E) +
        E * ((n : ℝ) + E) * ((n : ℝ) + E) +
        E * ((n : ℝ) + E) * ((n : ℝ) + E) := by
      have hmiddle :
          (n : ℝ) * E * ((n : ℝ) + E) ≤
            E * ((n : ℝ) + E) * ((n : ℝ) + E) := by
        calc
          (n : ℝ) * E * ((n : ℝ) + E) =
            E * (n : ℝ) * ((n : ℝ) + E) := by ring
          _ ≤ E * ((n : ℝ) + E) * ((n : ℝ) + E) := by gcongr
      have hlast :
          (n : ℝ) * (n : ℝ) * E ≤
            E * ((n : ℝ) + E) * ((n : ℝ) + E) := by
        calc
          (n : ℝ) * (n : ℝ) * E = E * (n : ℝ) * (n : ℝ) := by ring
          _ ≤ E * ((n : ℝ) + E) * ((n : ℝ) + E) := by gcongr
      linarith
    _ = 3 * E * ((n : ℝ) + E) ^ 2 := by ring

/-- The exact integral of the actual residue-cell cubic error is bounded by
its common one-factor majorant times the true truncated-arc length. -/
theorem ternaryManuscriptMajorArcCubicError_integral_le
    (c C : ℝ) (hC : 0 ≤ C)
    (n modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (hlabelUpper : labelUpper ≤ n)
    (hleftUpper : leftUpper ≤ n)
    (hrightUpper : rightUpper ≤ n)
    (numerator : ℤ) (δ E : ℝ)
    (hδ : 0 ≤ δ) (hE : 0 ≤ E)
    (hlabel : ∀ β ∈ Set.Ioc (0 : ℝ) δ,
      2 * ternaryMajorArcProgressionError c C n 1 β ≤ E)
    (hleft : ∀ β ∈ Set.Ioc (0 : ℝ) δ,
      2 * ternaryMajorArcProgressionError c C n (a : ℤ) β ≤ E)
    (hright : ∀ β ∈ Set.Ioc (0 : ℝ) δ,
      2 * ternaryMajorArcProgressionError c C n (-2 * (d : ℤ)) β ≤ E) :
    (∫ β in Set.Ioc (0 : ℝ) δ,
      ternaryManuscriptMajorArcCubicError
        c C n modulus labelResidue leftResidue rightResidue a d
        labelLower labelUpper leftLower leftUpper
        rightLower rightUpper numerator β) ≤
      3 * E * ((n : ℝ) + E) ^ 2 * δ := by
  let error : ℝ → ℝ := fun β =>
    ternaryManuscriptMajorArcCubicError
      c C n modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β
  have hcontinuous : Continuous error := by
    dsimp [error, ternaryManuscriptMajorArcCubicError,
      ternaryMajorArcProgressionError, ternaryMajorArcIntervalModel]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  have hcomparison :
      (∫ β in Set.Ioc (0 : ℝ) δ, error β) ≤
        ∫ _β in Set.Ioc (0 : ℝ) δ,
          3 * E * ((n : ℝ) + E) ^ 2 := by
    apply setIntegral_mono_on hcontinuous.integrableOn_Ioc
      (integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))
      measurableSet_Ioc
    intro β hβ
    exact ternaryManuscriptMajorArcCubicError_le
      c C hC n modulus labelResidue leftResidue rightResidue a d hmodulus
      labelLower labelUpper leftLower leftUpper rightLower rightUpper
      hlabelUpper hleftUpper hrightUpper numerator β E hE
      (hlabel β hβ) (hleft β hβ) (hright β hβ)
  calc
    (∫ β in Set.Ioc (0 : ℝ) δ, error β) ≤
        ∫ _β in Set.Ioc (0 : ℝ) δ,
          3 * E * ((n : ℝ) + E) ^ 2 := hcomparison
    _ = 3 * E * ((n : ℝ) + E) ^ 2 * δ := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le hδ,
        sub_zero, smul_eq_mul]
      ring

/-- For every fixed actual support modulus and affine coefficients, and for
arbitrary moving manuscript windows contained in `[0,n]`, the integral of the
*actual defined cubic Siegel--Walfisz error* over the central arc
`0 < β ≤ 1/n` is `o(n²)`.  No asymptotic error hypothesis is assumed. -/
theorem ternaryManuscriptMajorArcCubicError_integral_normalized_tendsto_zero
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (labelLower labelUpper leftLower leftUpper
      rightLower rightUpper : ℕ → ℕ)
    (hlabelUpper : ∀ n, labelUpper n ≤ n)
    (hleftUpper : ∀ n, leftUpper n ≤ n)
    (hrightUpper : ∀ n, rightUpper n ≤ n)
    (numerator : ℤ) :
    Tendsto
      (fun n : ℕ =>
        (∫ β in Set.Ioc (0 : ℝ) (1 / (n : ℝ)),
          ternaryManuscriptMajorArcCubicError
            c C n modulus labelResidue leftResidue rightResidue a d
            (labelLower n) (labelUpper n)
            (leftLower n) (leftUpper n)
            (rightLower n) (rightUpper n) numerator β) / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  let F : ℝ := 1 + (a : ℝ) + 2 * (d : ℝ)
  let A : ℝ := 2 * C * (1 + 2 * Real.pi * F)
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hone : |((1 : ℤ) : ℝ)| ≤ F := by
    dsimp [F]
    norm_num
    nlinarith [show (0 : ℝ) ≤ (a : ℝ) by positivity,
      show (0 : ℝ) ≤ (d : ℝ) by positivity]
  have ha : |((a : ℤ) : ℝ)| ≤ F := by
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp [F]
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]
  have hd : |((-2 * (d : ℤ) : ℤ) : ℝ)| ≤ F := by
    push_cast
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Nat.cast_nonneg d)]
    dsimp [F]
    nlinarith [show (0 : ℝ) ≤ (a : ℝ) by positivity]
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by
      apply div_nonneg _ (sq_nonneg _)
      apply setIntegral_nonneg measurableSet_Ioc
      intro β hβ
      dsimp [ternaryManuscriptMajorArcCubicError,
        ternaryMajorArcProgressionError]
      positivity))
    _ (ternary_central_cubic_error_normalized_majorant_tendsto_zero c A hc)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  let decay : ℝ := Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10))
  let E : ℝ := A * n * decay
  have hE : 0 ≤ E := by
    dsimp [E, decay]
    positivity
  have hfrequency
      (frequency : ℤ) (hfrequency : |(frequency : ℝ)| ≤ F)
      (β : ℝ) (hβ : β ∈ Set.Ioc (0 : ℝ) (1 / (n : ℝ))) :
      2 * ternaryMajorArcProgressionError c C n frequency β ≤ E := by
    have hcentral : (n : ℝ) * β ≤ 1 := by
      calc
        (n : ℝ) * β ≤ (n : ℝ) * (1 / (n : ℝ)) := by
          gcongr
          exact hβ.2
        _ = 1 := by field_simp
    calc
      2 * ternaryMajorArcProgressionError c C n frequency β ≤
          (2 * C * (1 + 2 * Real.pi * |(frequency : ℝ)|)) *
            (n : ℝ) * decay :=
        ternaryMajorArcProgressionError_central_le
          c C hC n frequency β hβ.1.le hcentral
      _ ≤ (2 * C * (1 + 2 * Real.pi * F)) *
            (n : ℝ) * decay := by
        dsimp [decay]
        gcongr
      _ = E := rfl
  have hbound := ternaryManuscriptMajorArcCubicError_integral_le
    c C hC n modulus labelResidue leftResidue rightResidue a d hmodulus
    (labelLower n) (labelUpper n) (leftLower n) (leftUpper n)
    (rightLower n) (rightUpper n)
    (hlabelUpper n) (hleftUpper n) (hrightUpper n)
    numerator (1 / (n : ℝ)) E (by positivity) hE
    (fun β hβ => hfrequency 1 hone β hβ)
    (fun β hβ => hfrequency (a : ℤ) ha β hβ)
    (fun β hβ => hfrequency (-2 * (d : ℤ)) hd β hβ)
  calc
    (∫ β in Set.Ioc (0 : ℝ) (1 / (n : ℝ)),
          ternaryManuscriptMajorArcCubicError
            c C n modulus labelResidue leftResidue rightResidue a d
            (labelLower n) (labelUpper n)
            (leftLower n) (leftUpper n)
            (rightLower n) (rightUpper n) numerator β) / (n : ℝ) ^ 2 ≤
        (3 * E * ((n : ℝ) + E) ^ 2 * (1 / (n : ℝ))) /
          (n : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hbound (sq_nonneg _)
    _ = 3 * A * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10)) *
          (1 + A * Real.exp (-c * Real.log n ^ ((1 : ℝ) / 10))) ^ 2 := by
      dsimp [E, decay]
      field_simp

end Erdos689

#print axioms Erdos689.ternaryMajorArcIntervalModel_norm_le_card
#print axioms Erdos689.ternary_siegel_walfisz_decay_tendsto_zero
#print axioms Erdos689.ternaryMajorArcProgressionError_central_le
#print axioms Erdos689.ternary_central_cubic_error_normalized_majorant_tendsto_zero
#print axioms Erdos689.ternaryManuscriptMajorArcCubicError_le
#print axioms Erdos689.ternaryManuscriptMajorArcCubicError_integral_le
#print axioms Erdos689.ternaryManuscriptMajorArcCubicError_integral_normalized_tendsto_zero
