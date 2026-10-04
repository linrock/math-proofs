module

public import ThreePrimeMajorArcError433

@[expose] public section


/-!
# Unconditional positivity of the actual manuscript principal arc

The genuine residue-restricted von-Mangoldt principal arc has a positive
quadratic lower bound whenever all three actual manuscript windows have
positive linear width.  Unlike the preceding main-minus-error theorem, this
module absorbs the independently proved integrated Siegel--Walfisz error.
It makes no assertion about the complementary shifted or minor arcs.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The actual affine manuscript phase is uniformly bounded by its natural
fixed-coefficient scale throughout three windows contained in `[0, N]`. -/
theorem ternary_manuscript_phase_linear_bound
    (a d N x y z : ℕ) (hx : x ≤ N) (hy : y ≤ N) (hz : z ≤ N) :
    |(a : ℝ) * x - (2 * d : ℕ) * y + z| ≤
      (1 + (a : ℝ) + 2 * (d : ℝ)) * (N : ℝ) := by
  have hxreal : (x : ℝ) ≤ N := by exact_mod_cast hx
  have hyreal : (y : ℝ) ≤ N := by exact_mod_cast hy
  have hzreal : (z : ℝ) ≤ N := by exact_mod_cast hz
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hx0 : 0 ≤ (x : ℝ) := Nat.cast_nonneg _
  have hy0 : 0 ≤ (y : ℝ) := Nat.cast_nonneg _
  have hz0 : 0 ≤ (z : ℝ) := Nat.cast_nonneg _
  norm_num only [Nat.cast_ofNat, Nat.cast_mul]
  apply abs_le.mpr
  constructor <;>
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hxreal),
      mul_nonneg hd (sub_nonneg.mpr hyreal), mul_nonneg ha hx0,
      mul_nonneg hd hy0, mul_nonneg ha hN, mul_nonneg hd hN]

/-- The actual defined cubic principal-arc error is pointwise nonnegative;
in particular its integral can only increase when the central arc grows. -/
theorem ternaryManuscriptMajorArcCubicError_nonneg
    (c C : ℝ) (hC : 0 ≤ C)
    (N modulus labelResidue leftResidue rightResidue a d : ℕ)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) (β : ℝ) :
    0 ≤ ternaryManuscriptMajorArcCubicError
      c C N modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β := by
  dsimp [ternaryManuscriptMajorArcCubicError,
    ternaryMajorArcProgressionError]
  positivity

/-- The actual nonnegative cubic error over a narrower central arc is bounded
by the error over any larger central arc. -/
theorem ternaryManuscriptMajorArcCubicError_integral_mono_arc
    (c C : ℝ) (hC : 0 ≤ C)
    (N modulus labelResidue leftResidue rightResidue a d : ℕ)
    (labelLower labelUpper leftLower leftUpper rightLower rightUpper : ℕ)
    (numerator : ℤ) (δ Δ : ℝ) (hδ : δ ≤ Δ) :
    (∫ β in Set.Ioc (0 : ℝ) δ,
      ternaryManuscriptMajorArcCubicError
        c C N modulus labelResidue leftResidue rightResidue a d
        labelLower labelUpper leftLower leftUpper
        rightLower rightUpper numerator β) ≤
      ∫ β in Set.Ioc (0 : ℝ) Δ,
        ternaryManuscriptMajorArcCubicError
          c C N modulus labelResidue leftResidue rightResidue a d
          labelLower labelUpper leftLower leftUpper
          rightLower rightUpper numerator β := by
  let error : ℝ → ℝ := fun β =>
    ternaryManuscriptMajorArcCubicError
      c C N modulus labelResidue leftResidue rightResidue a d
      labelLower labelUpper leftLower leftUpper
      rightLower rightUpper numerator β
  have hcontinuous : Continuous error := by
    dsimp [error, ternaryManuscriptMajorArcCubicError,
      ternaryMajorArcProgressionError, ternaryMajorArcIntervalModel]
    unfold ternaryExponentialSum GoldbachChain.e
    fun_prop
  apply setIntegral_mono_set hcontinuous.integrableOn_Ioc
  · exact Filter.Eventually.of_forall fun β =>
      ternaryManuscriptMajorArcCubicError_nonneg
        c C hC N modulus labelResidue leftResidue rightResidue a d
        labelLower labelUpper leftLower leftUpper
        rightLower rightUpper numerator β
  · exact Filter.Eventually.of_forall fun β hβ =>
      ⟨hβ.1, hβ.2.trans hδ⟩

/-- The true phase-controlled principal arc is contained in the `1 / n`
central arc for every positive `n`, with the actual affine coefficients. -/
theorem ternary_manuscript_principal_arc_le_central
    (a d n : ℕ) (hn : 0 < n) :
    1 / (4 * Real.pi *
      ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ))) ≤
        1 / (n : ℝ) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hF : 1 ≤ 1 + (a : ℝ) + 2 * (d : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ (a : ℝ) by positivity,
      show (0 : ℝ) ≤ (d : ℝ) by positivity]
  have hscale : 1 ≤ 4 * Real.pi * (1 + (a : ℝ) + 2 * (d : ℝ)) := by
    nlinarith [Real.pi_gt_three,
      mul_nonneg (show 0 ≤ 4 * Real.pi by positivity)
        (sub_nonneg.mpr hF)]
  apply one_div_le_one_div_of_le hnreal
  nlinarith [mul_nonneg (sub_nonneg.mpr hscale) hnreal.le]

/-- For the actual, coefficient-sensitive principal arc, the *actual defined*
cubic Siegel--Walfisz error is `o(n²)`, uniformly across arbitrary moving
windows contained in `[0,n]`.  This transfers the existing central-arc
little-o theorem to exactly the smaller positivity arc. -/
theorem ternaryManuscriptMajorArcCubicError_principal_normalized_tendsto_zero
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
        (∫ β in Set.Ioc (0 : ℝ)
          (1 / (4 * Real.pi *
            ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
          ternaryManuscriptMajorArcCubicError
            c C n modulus labelResidue leftResidue rightResidue a d
            (labelLower n) (labelUpper n)
            (leftLower n) (leftUpper n)
            (rightLower n) (rightUpper n) numerator β) / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hcentral :=
    ternaryManuscriptMajorArcCubicError_integral_normalized_tendsto_zero
      c C hc hC modulus labelResidue leftResidue rightResidue a d hmodulus
      labelLower labelUpper leftLower leftUpper rightLower rightUpper
      hlabelUpper hleftUpper hrightUpper numerator
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by
      apply div_nonneg _ (sq_nonneg _)
      apply setIntegral_nonneg measurableSet_Ioc
      intro β _
      exact ternaryManuscriptMajorArcCubicError_nonneg
        c C hC n modulus labelResidue leftResidue rightResidue a d
        (labelLower n) (labelUpper n) (leftLower n) (leftUpper n)
        (rightLower n) (rightUpper n) numerator β)
    _ hcentral
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact ternaryManuscriptMajorArcCubicError_integral_mono_arc
    c C hC n modulus labelResidue leftResidue rightResidue a d
    (labelLower n) (labelUpper n) (leftLower n) (leftUpper n)
    (rightLower n) (rightUpper n) numerator
    (1 / (4 * Real.pi *
      ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ))))
    (1 / (n : ℝ))
    (ternary_manuscript_principal_arc_le_central a d n hn)

/-- The actual residue-restricted three-von-Mangoldt principal arc has a
strictly positive quadratic lower bound for every fixed admissible modulus,
residue cell, and affine coefficient, provided all three genuine moving
windows have positive linear width.  The only window assumptions are their
actual endpoints and widths; no prime-pattern estimate, error hypothesis, or
major/minor-arc cancellation is assumed. -/
theorem ternary_actual_principal_arc_eventually_quadratic_positive
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hlabelResidue : labelResidue < modulus)
    (hleftResidue : leftResidue < modulus)
    (hrightResidue : rightResidue < modulus)
    (hlabelUnit : Nat.gcd labelResidue modulus = 1)
    (hleftUnit : Nat.gcd leftResidue modulus = 1)
    (hrightUnit : Nat.gcd rightResidue modulus = 1)
    (hadmissible : (a * leftResidue + labelResidue) % modulus =
      (2 * d * rightResidue) % modulus)
    (labelLower labelUpper leftLower leftUpper
      rightLower rightUpper : ℕ → ℕ)
    (hlabelLower : ∀ n, labelLower n ≤ labelUpper n)
    (hlabelUpper : ∀ n, labelUpper n ≤ n)
    (hleftLower : ∀ n, leftLower n ≤ leftUpper n)
    (hleftUpper : ∀ n, leftUpper n ≤ n)
    (hrightLower : ∀ n, rightLower n ≤ rightUpper n)
    (hrightUpper : ∀ n, rightUpper n ≤ n)
    (κlabel κleft κright : ℝ)
    (hκlabel : 0 < κlabel)
    (hκleft : 0 < κleft)
    (hκright : 0 < κright)
    (hlabelWidth : ∀ᶠ n : ℕ in atTop,
      κlabel * (n : ℝ) ≤
        ((Finset.Ico (labelLower n) (labelUpper n)).card : ℝ))
    (hleftWidth : ∀ᶠ n : ℕ in atTop,
      κleft * (n : ℝ) ≤
        ((Finset.Ico (leftLower n) (leftUpper n)).card : ℝ))
    (hrightWidth : ∀ᶠ n : ℕ in atTop,
      κright * (n : ℝ) ≤
        ((Finset.Ico (rightLower n) (rightUpper n)).card : ℝ))
    (numerator : ℤ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ^ 2 ≤
        (∫ β in Set.Ioc (0 : ℝ)
          (1 / (4 * Real.pi *
            ((1 + (a : ℝ) + 2 * (d : ℝ)) * (n : ℝ)))),
          ternaryManuscriptResidueCubicVonMangoldt
            modulus labelResidue leftResidue rightResidue a d
            (labelLower n) (labelUpper n)
            (leftLower n) (leftUpper n)
            (rightLower n) (rightUpper n) numerator β).re := by
  obtain ⟨c, C, hc, hC, N₀, hrated⟩ :=
    ternary_rated_manuscript_residue_principal_arc_integral_lower
      1 (by norm_num)
  let F : ℝ := 1 + (a : ℝ) + 2 * (d : ℝ)
  have hF : 0 < F := by
    dsimp [F]
    positivity
  have htotient : 0 < modulus.totient := Nat.totient_pos.mpr hmodulus
  let κ : ℝ :=
    (1 / (modulus.totient : ℝ)) ^ 3 *
      (κleft * κright * κlabel) / (16 * Real.pi * F)
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  refine ⟨κ, hκ, ?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmodlog : ∀ᶠ n : ℕ in atTop,
      (modulus : ℝ) ≤ Real.log (n : ℝ) :=
    (tendsto_atTop.1 hlog (modulus : ℝ))
  have herror :=
    ternaryManuscriptMajorArcCubicError_principal_normalized_tendsto_zero
      c C hc hC.le modulus labelResidue leftResidue rightResidue a d hmodulus
      labelLower labelUpper leftLower leftUpper rightLower rightUpper
      hlabelUpper hleftUpper hrightUpper numerator
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (∫ β in Set.Ioc (0 : ℝ)
        (1 / (4 * Real.pi * (F * (n : ℝ)))),
        ternaryManuscriptMajorArcCubicError
          c C n modulus labelResidue leftResidue rightResidue a d
          (labelLower n) (labelUpper n)
          (leftLower n) (leftUpper n)
          (rightLower n) (rightUpper n) numerator β) /
          (n : ℝ) ^ 2 < κ := by
    simpa [F] using ((tendsto_order.1 herror).2 κ hκ)
  filter_upwards [eventually_ge_atTop (max N₀ 1), hmodlog,
      hlabelWidth, hleftWidth, hrightWidth, hsmall] with
    n hn hmodN hlabelN hleftN hrightN herrorN
  have hnN₀ : N₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnpositive : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right _ _) hn)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpositive
  have hphase : ∀ x ∈ Finset.Ico (leftLower n) (leftUpper n),
      ∀ y ∈ Finset.Ico (rightLower n) (rightUpper n),
        ∀ z ∈ Finset.Ico (labelLower n) (labelUpper n),
          |(a : ℝ) * x - (2 * d : ℕ) * y + z| ≤ F * (n : ℝ) := by
    intro x hx y hy z hz
    exact ternary_manuscript_phase_linear_bound a d n x y z
      ((Nat.le_of_lt (Finset.mem_Ico.mp hx).2).trans (hleftUpper n))
      ((Nat.le_of_lt (Finset.mem_Ico.mp hy).2).trans (hrightUpper n))
      ((Nat.le_of_lt (Finset.mem_Ico.mp hz).2).trans (hlabelUpper n))
  have hprincipal :=
    hrated n hnN₀ (labelLower n) (labelUpper n)
      (leftLower n) (leftUpper n) (rightLower n) (rightUpper n)
      (hlabelLower n) (hlabelUpper n)
      (hleftLower n) (hleftUpper n)
      (hrightLower n) (hrightUpper n)
      modulus hmodulus (by simpa using hmodN)
      labelResidue leftResidue rightResidue
      hlabelResidue hleftResidue hrightResidue
      hlabelUnit hleftUnit hrightUnit
      a d hadmissible numerator (F * (n : ℝ))
      (mul_pos hF hnreal) hphase
  have hproduct :
      κleft * κright * κlabel * (n : ℝ) ^ 3 ≤
        ((Finset.Ico (leftLower n) (leftUpper n)).card : ℝ) *
          ((Finset.Ico (rightLower n) (rightUpper n)).card : ℝ) *
          ((Finset.Ico (labelLower n) (labelUpper n)).card : ℝ) := by
    calc
      κleft * κright * κlabel * (n : ℝ) ^ 3 =
          (κleft * (n : ℝ)) * (κright * (n : ℝ)) *
            (κlabel * (n : ℝ)) := by ring
      _ ≤ ((Finset.Ico (leftLower n) (leftUpper n)).card : ℝ) *
          ((Finset.Ico (rightLower n) (rightUpper n)).card : ℝ) *
          ((Finset.Ico (labelLower n) (labelUpper n)).card : ℝ) := by
        gcongr
  have hmain :
      2 * κ * (n : ℝ) ^ 2 ≤
        (1 / (modulus.totient : ℝ)) ^ 3 *
          (((Finset.Ico (leftLower n) (leftUpper n)).card : ℝ) *
            ((Finset.Ico (rightLower n) (rightUpper n)).card : ℝ) *
            ((Finset.Ico (labelLower n) (labelUpper n)).card : ℝ) /
              (8 * Real.pi * (F * (n : ℝ)))) := by
    calc
      2 * κ * (n : ℝ) ^ 2 =
          (1 / (modulus.totient : ℝ)) ^ 3 *
            (κleft * κright * κlabel * (n : ℝ) ^ 3 /
              (8 * Real.pi * (F * (n : ℝ)))) := by
        dsimp [κ]
        field_simp [hnreal.ne', hF.ne', Real.pi_ne_zero]
        ring
      _ ≤ (1 / (modulus.totient : ℝ)) ^ 3 *
          (((Finset.Ico (leftLower n) (leftUpper n)).card : ℝ) *
            ((Finset.Ico (rightLower n) (rightUpper n)).card : ℝ) *
            ((Finset.Ico (labelLower n) (labelUpper n)).card : ℝ) /
              (8 * Real.pi * (F * (n : ℝ)))) := by
        gcongr
  have herrorScaled :
      (∫ β in Set.Ioc (0 : ℝ)
        (1 / (4 * Real.pi * (F * (n : ℝ)))),
        ternaryManuscriptMajorArcCubicError
          c C n modulus labelResidue leftResidue rightResidue a d
          (labelLower n) (labelUpper n)
          (leftLower n) (leftUpper n)
          (rightLower n) (rightUpper n) numerator β) ≤
        κ * (n : ℝ) ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hnreal)).mp herrorN.le
  change κ * (n : ℝ) ^ 2 ≤
    (∫ β in Set.Ioc (0 : ℝ) (1 / (4 * Real.pi * (F * (n : ℝ)))),
      ternaryManuscriptResidueCubicVonMangoldt
        modulus labelResidue leftResidue rightResidue a d
        (labelLower n) (labelUpper n)
        (leftLower n) (leftUpper n)
        (rightLower n) (rightUpper n) numerator β).re
  linarith

end Erdos689

#print axioms Erdos689.ternary_manuscript_phase_linear_bound
#print axioms Erdos689.ternaryManuscriptMajorArcCubicError_nonneg
#print axioms Erdos689.ternaryManuscriptMajorArcCubicError_integral_mono_arc
#print axioms Erdos689.ternary_manuscript_principal_arc_le_central
#print axioms Erdos689.ternaryManuscriptMajorArcCubicError_principal_normalized_tendsto_zero
#print axioms Erdos689.ternary_actual_principal_arc_eventually_quadratic_positive
