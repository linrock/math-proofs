import ActualMajorArcPositivityFinal433
import ActualMajorArcParityCRT433

/-!
# Exact parity-corrected singular model and its original coupling

At finite cutoff the original odd and doubled Farey denominators contribute
`A(P) + A(P/2)`, not `2*A(P)`.  This module retains the TRUE finite model,
proves its same unconditional quadratic positivity, and proves that replacing
the historical doubled model by the corrected one is asymptotically exact.
No major-arc coupling or original Erdős conclusion is asserted unconditionally.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- A genuine affine triple is injectively determined by its first TWO
coordinates: the third coordinate is forced by the ORIGINAL equation. -/
theorem actualMajorArcCorrected_affine_lattice_card_le
    (left center labels : Finset ℕ) (a c : ℕ) :
    (ternaryAffineTriples left center labels a c).card ≤
      left.card * center.card := by
  classical
  calc
    (ternaryAffineTriples left center labels a c).card ≤
        (left.product center).card := by
      apply Finset.card_le_card_of_injOn
        (fun triple : ℕ × (ℕ × ℕ) => (triple.1, triple.2.1))
      · intro triple htriple
        obtain ⟨hproduct, _⟩ :=
          Finset.mem_filter.mp (Finset.mem_coe.mp htriple)
        obtain ⟨hleft, hrest⟩ := Finset.mem_product.mp hproduct
        exact Finset.mem_coe.mpr
          (Finset.mem_product.mpr
            ⟨hleft, (Finset.mem_product.mp hrest).1⟩)
      · intro first hfirst second hsecond hequal
        obtain ⟨_, hfirstEquation⟩ :=
          Finset.mem_filter.mp (Finset.mem_coe.mp hfirst)
        obtain ⟨_, hsecondEquation⟩ :=
          Finset.mem_filter.mp (Finset.mem_coe.mp hsecond)
        have hleft : first.1 = second.1 :=
          congrArg (fun pair : ℕ × ℕ => pair.1) hequal
        have hcenter : first.2.1 = second.2.1 :=
          congrArg (fun pair : ℕ × ℕ => pair.2) hequal
        rw [hleft, hcenter] at hfirstEquation
        have hlabel : first.2.2 = second.2.2 := by omega
        exact Prod.ext hleft (Prod.ext hcenter hlabel)
    _ = _ := Finset.card_product _ _

/-- The ORIGINAL two sharp edge windows alone bound every true affine
lattice by `n²`; no enlargement of the real strip is needed. -/
theorem actualMajorArcCorrected_true_lattice_card_le_square
    (a d n : ℕ) (τ ell : ℝ) :
    (ternaryAffineTriples
      (actualMajorArcArchimedeanLeftWindow a n)
      (actualMajorArcArchimedeanCenterWindow d n)
      (actualMajorArcArchimedeanLabelWindow τ ell n)
      a (2 * d)).card ≤ n ^ 2 := by
  have hleft :
      (actualMajorArcArchimedeanLeftWindow a n).card ≤ n := by
    simpa [actualMajorArcArchimedeanLeftWindow] using
      Nat.div_le_self n (2 * a)
  have hright :
      (actualMajorArcArchimedeanCenterWindow d n).card ≤ n := by
    simpa [actualMajorArcArchimedeanCenterWindow] using
      Nat.div_le_self n (4 * d)
  calc
    _ ≤ (actualMajorArcArchimedeanLeftWindow a n).card *
        (actualMajorArcArchimedeanCenterWindow d n).card :=
      actualMajorArcCorrected_affine_lattice_card_le _ _ _ _ _
    _ ≤ n * n := Nat.mul_le_mul hleft hright
    _ = n ^ 2 := (pow_two n).symm

/-- A finite, support-dependent coefficient cap; support uniformity is NOT
needed to remove the asymptotically vanishing parity shell. -/
noncomputable def actualMajorArcCorrectedFixedCoefficientBound
    (S : Finset ℕ) (b : ℕ → ℕ) (target : ℕ) : ℝ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      actualFixedLabelDoubleCoefficientWeight S target b a d *
        (a : ℝ) * d

/-- Every genuine original coefficient-compensated lattice main term has a
quadratic upper bound for its fixed support and residue. -/
theorem actualMajorArcCorrected_coefficient_lattice_le_square
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target : ℕ) (τ ell : ℝ) :
    actualMajorArcFinalCoefficientLatticeMass S b n target τ ell ≤
      actualMajorArcCorrectedFixedCoefficientBound S b target *
        (n : ℝ) ^ 2 := by
  unfold actualMajorArcFinalCoefficientLatticeMass
    actualMajorArcCorrectedFixedCoefficientBound
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro d hd
  have hcard :
      ((ternaryAffineTriples
        (actualMajorArcArchimedeanLeftWindow a n)
        (actualMajorArcArchimedeanCenterWindow d n)
        (actualMajorArcArchimedeanLabelWindow τ ell n)
        a (2 * d)).card : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast actualMajorArcCorrected_true_lattice_card_le_square
      a d n τ ell
  have hfactor :
      0 ≤ actualFixedLabelDoubleCoefficientWeight S target b a d *
        (a : ℝ) * d := by
    exact mul_nonneg
      (mul_nonneg
        (actualMajorArcFinal_double_coefficient_weight_nonneg S target b a d)
        (by positivity)) (by positivity)
  exact mul_le_mul_of_nonneg_left hcard hfactor

/-- The coefficient-summed lattice mass is nonnegative, despite the signed
outside-conductor series to which it will subsequently be coupled. -/
theorem actualMajorArcCorrected_coefficient_lattice_nonneg
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target : ℕ) (τ ell : ℝ) :
    0 ≤ actualMajorArcFinalCoefficientLatticeMass
      S b n target τ ell := by
  unfold actualMajorArcFinalCoefficientLatticeMass
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro d hd
  have hweight := actualMajorArcFinal_double_coefficient_weight_nonneg
    S target b a d
  positivity

/-- The TRUE finite original singular model uses both distinct sharp
outside/parity cutoffs and the ORIGINAL compensated two-edge lattice. -/
noncomputable def actualMajorArcCorrectedPredictedMain
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target : ℕ) (τ ell : ℝ) : ℝ :=
  actualMajorArcParitySharpPartial
      (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n) *
    (actualMajorArcFinalCoefficientLatticeMass
      S b n target τ ell /
      (((∏ p ∈ S, p).totient : ℕ) : ℝ))

/-- Exact finite discrepancy: the corrected and historical models differ
by precisely the signed omitted parity shell times the actual lattice. -/
theorem actualMajorArcCorrected_model_sub_old_eq_shell_mul_lattice
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target : ℕ) (τ ell : ℝ) :
    actualMajorArcCorrectedPredictedMain S b n target τ ell -
        actualMajorArcFinalPredictedMain S b n target τ ell =
      (actualMajorArcParitySharpPartial
          (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n) -
        2 * actualMajorArcParityOutsidePartial
          (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n)) *
        (actualMajorArcFinalCoefficientLatticeMass
          S b n target τ ell /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ)) := by
  unfold actualMajorArcCorrectedPredictedMain
    actualMajorArcFinalPredictedMain
    actualMajorArcFinalOutsideSingularSeries
    actualMajorArcParityOutsidePartial
  ring

/-- The genuine omitted parity shell has a uniform-in-`n` quadratic
majorant after multiplying by the ACTUAL full coefficient lattice. -/
theorem actualMajorArcCorrected_model_difference_normalized_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target : ℕ) (τ ell : ℝ)
    (hn : 0 < n) :
    |actualMajorArcCorrectedPredictedMain S b n target τ ell -
        actualMajorArcFinalPredictedMain S b n target τ ell| /
        (n : ℝ) ^ 2 ≤
      |actualMajorArcParitySharpPartial
          (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n) -
        2 * actualMajorArcParityOutsidePartial
          (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n)| *
        (actualMajorArcCorrectedFixedCoefficientBound S b target /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ)) := by
  let mass := actualMajorArcFinalCoefficientLatticeMass
    S b n target τ ell
  let bound := actualMajorArcCorrectedFixedCoefficientBound S b target
  let phi : ℝ := (((∏ p ∈ S, p).totient : ℕ) : ℝ)
  let discrepancy := actualMajorArcParitySharpPartial
    (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n) -
      2 * actualMajorArcParityOutsidePartial
        (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmass : 0 ≤ mass :=
    actualMajorArcCorrected_coefficient_lattice_nonneg
      S b n target τ ell
  have hbound : mass / (n : ℝ) ^ 2 ≤ bound :=
    (div_le_iff₀ (sq_pos_of_pos hnreal)).mpr
      (actualMajorArcCorrected_coefficient_lattice_le_square
        S b n target τ ell)
  have hnormalized : mass / (n : ℝ) ^ 2 / phi ≤ bound / phi :=
    div_le_div_of_nonneg_right hbound (by dsimp [phi]; positivity)
  rw [actualMajorArcCorrected_model_sub_old_eq_shell_mul_lattice]
  change |discrepancy * (mass / phi)| / (n : ℝ) ^ 2 ≤
    |discrepancy| * (bound / phi)
  rw [abs_mul, abs_of_nonneg (div_nonneg hmass (by dsimp [phi]; positivity))]
  calc
    |discrepancy| * (mass / phi) / (n : ℝ) ^ 2 =
        |discrepancy| * (mass / (n : ℝ) ^ 2 / phi) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnormalized (abs_nonneg _)

/-- The corrected TRUE finite singular model and the previously proposed
doubled model are asymptotically identical at the ORIGINAL `n²` scale. -/
theorem actualMajorArcCorrected_model_difference_tendsto_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target : ℕ) (τ ell : ℝ) :
    Tendsto
      (fun n : ℕ =>
        |actualMajorArcCorrectedPredictedMain S b n target τ ell -
          actualMajorArcFinalPredictedMain S b n target τ ell| /
            (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hdiscrepancy :=
    actualMajorArcParity_compatible_cutoff_discrepancy_tendsto_zero
      (2 * (∏ p ∈ S, p))
  have habsolute :
      Tendsto
        (fun n : ℕ =>
          |actualMajorArcParitySharpPartial
            (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n) -
              2 * actualMajorArcParityOutsidePartial
                (2 * (∏ p ∈ S, p)) (compatibleLogMinorCutoff n)|)
        atTop (nhds 0) := by
    simpa using hdiscrepancy.abs
  have hmajor := habsolute.mul_const
    (actualMajorArcCorrectedFixedCoefficientBound S b target /
      (((∏ p ∈ S, p).totient : ℕ) : ℝ))
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity)
    _ (by simpa using hmajor)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact actualMajorArcCorrected_model_difference_normalized_le
    S b n target τ ell hn

/-- Unconditional quadratic positivity of the CORRECT genuine two-cutoff
outside/parity/support/lattice model, with the SAME absolute `1/320`. -/
theorem actualMajorArcCorrected_predicted_main_quadratic_lower
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ)
    (hsupport :
      ∀ p ∈ S, p.Prime ∧ 3 < p ∧ J < p ∧ b p % p ≠ 0)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ∀ᶠ n : ℕ in atTop,
      ∀ target ∈ robustResidues S b J,
        manuscriptLocalSingularFactor S b target *
            ell * (n : ℝ) ^ 2 / 320 ≤
          actualMajorArcCorrectedPredictedMain
            S b n target τ ell := by
  filter_upwards
    [actualMajorArcFinal_coefficient_lattice_lower
      S b J τ ell hsupport hτ hell hstrip,
      actualMajorArcParity_compatible_cutoff_ge_half
        (2 * (∏ p ∈ S, p)) (dvd_mul_right 2 _)]
    with n hlattice hseries
  intro target htarget
  have hmass :
      0 ≤ actualMajorArcFinalCoefficientLatticeMass
        S b n target τ ell /
          (((∏ p ∈ S, p).totient : ℕ) : ℝ) :=
    div_nonneg
      (actualMajorArcCorrected_coefficient_lattice_nonneg
        S b n target τ ell) (by positivity)
  unfold actualMajorArcCorrectedPredictedMain
  calc
    manuscriptLocalSingularFactor S b target *
        ell * (n : ℝ) ^ 2 / 320 =
      (1 / 2 : ℝ) *
        (manuscriptLocalSingularFactor S b target *
          ell * (n : ℝ) ^ 2 / 160) := by ring
    _ ≤ (1 / 2 : ℝ) *
        (actualMajorArcFinalCoefficientLatticeMass
          S b n target τ ell /
            (((∏ p ∈ S, p).totient : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hlattice target htarget) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right hseries hmass

/-- Exact replacement of the old finite doubled model by the ACTUAL
two-cutoff original rational-center model in the sole remaining coupling. -/
def UniformActualDeduplicatedCorrectedSingularModelCoupling : Prop :=
  ∀ (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ),
    (∀ p ∈ S, p.Prime ∧ 3 < p ∧ J < p ∧ b p % p ≠ 0) →
    0 < τ → 0 < ell → τ + ell < (1 : ℝ) / 10 →
      ∀ target ∈ robustResidues S b J,
        Tendsto
          (fun n : ℕ =>
            |actualDeduplicatedMajorPrimeMass S b n J target
                (compatibleLogMinorCutoff n)
                (fullyCompatibleFareyCutoff
                  (fun m => Nat.floor (τ * (m : ℝ))) n)
                τ ell -
              actualMajorArcCorrectedPredictedMain
                S b n target τ ell| / (n : ℝ) ^ 2)
          atTop (nhds 0)

/-- Generic normalized absolute-error transfer; retaining all terms avoids
ever identifying the two finite parity sums incorrectly. -/
theorem actualMajorArcCorrected_absolute_coupling_transfer
    (actual old corrected : ℕ → ℝ)
    (hactual :
      Tendsto
        (fun n : ℕ => |actual n - corrected n| / (n : ℝ) ^ 2)
        atTop (nhds 0))
    (hmodels :
      Tendsto
        (fun n : ℕ => |corrected n - old n| / (n : ℝ) ^ 2)
        atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ => |actual n - old n| / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity)
    (Filter.Eventually.of_forall fun n => ?_)
    (by simpa using hactual.add hmodels)
  have htriangle := abs_sub_le (actual n) (corrected n) (old n)
  simpa [add_div] using
    (div_le_div_of_nonneg_right htriangle (by positivity :
      0 ≤ (n : ℝ) ^ 2))

/-- The actual finite two-cutoff coupling and the previously advertised
doubled-model coupling are LOGICALLY EQUIVALENT, not merely heuristically
interchangeable. -/
theorem actualMajorArcCorrected_coupling_iff_original :
    UniformActualDeduplicatedCorrectedSingularModelCoupling ↔
      UniformActualDeduplicatedSingularModelCoupling := by
  constructor
  · intro hcorrected S b J τ ell hsupport hτ hell hstrip target htarget
    exact actualMajorArcCorrected_absolute_coupling_transfer
      (fun n => actualDeduplicatedMajorPrimeMass
        S b n J target (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff
            (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell)
      (fun n => actualMajorArcFinalPredictedMain S b n target τ ell)
      (fun n => actualMajorArcCorrectedPredictedMain S b n target τ ell)
      (hcorrected S b J τ ell hsupport hτ hell hstrip target htarget)
      (actualMajorArcCorrected_model_difference_tendsto_zero
        S b target τ ell)
  · intro hold S b J τ ell hsupport hτ hell hstrip target htarget
    apply actualMajorArcCorrected_absolute_coupling_transfer
      (fun n => actualDeduplicatedMajorPrimeMass
        S b n J target (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff
            (fun m => Nat.floor (τ * (m : ℝ))) n) τ ell)
      (fun n => actualMajorArcCorrectedPredictedMain S b n target τ ell)
      (fun n => actualMajorArcFinalPredictedMain S b n target τ ell)
      (hold S b J τ ell hsupport hτ hell hstrip target htarget)
    simpa only [abs_sub_comm] using
      actualMajorArcCorrected_model_difference_tendsto_zero
        S b target τ ell

/-- The exact HISTORICAL original Erdős conclusion from the single
genuinely corrected finite rational-center coupling. This remains
conditional until that actual center assembly is proved. -/
theorem officialStatement_of_actual_corrected_singular_model_coupling
    (hcoupling : UniformActualDeduplicatedCorrectedSingularModelCoupling) :
    OfficialStatement := by
  exact officialStatement_of_actual_singular_model_coupling
    (actualMajorArcCorrected_coupling_iff_original.mp hcoupling)

#print axioms Erdos689.actualMajorArcCorrected_affine_lattice_card_le
#print axioms Erdos689.actualMajorArcCorrected_true_lattice_card_le_square
#print axioms Erdos689.actualMajorArcCorrected_coefficient_lattice_le_square
#print axioms Erdos689.actualMajorArcCorrected_coefficient_lattice_nonneg
#print axioms Erdos689.actualMajorArcCorrected_model_sub_old_eq_shell_mul_lattice
#print axioms Erdos689.actualMajorArcCorrected_model_difference_normalized_le
#print axioms Erdos689.actualMajorArcCorrected_model_difference_tendsto_zero
#print axioms Erdos689.actualMajorArcCorrected_predicted_main_quadratic_lower
#print axioms Erdos689.actualMajorArcCorrected_absolute_coupling_transfer
#print axioms Erdos689.actualMajorArcCorrected_coupling_iff_original
#print axioms Erdos689.officialStatement_of_actual_corrected_singular_model_coupling

end Erdos689
