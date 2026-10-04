module

public import ActualMajorArcPositivityTail433
public import ActualRightVertexMajorUnitOrbit433
public import ActualLeftVertexMajorExceptional433
public import ActualLeftVertexMajorIntegrated433
public import ActualFinalCenterReduction433

@[expose] public section


/-!
# Exact final major-arc singular-model reduction for Erdős #689

The support-divisor coefficient state ALREADY contains a reciprocal
coefficient factor. The actual rational-cell density consequently has the
indispensable multiplier `a*d`; omitting it would leave an invalid
support-dependent loss after the true lattice bound `ell*n²/(160*a*d)`.

This file defines the complete explicit model with the genuine support
coefficient, `a*d` compensation, original two-edge real-strip lattice,
parity factor two, and actual sharp outside-support signed singular series.
Its positive quadratic lower bound is unconditional. The only remaining
hypothesis is an exact `o(n²)` coupling of the deduplicated genuine prime
major-center integral to THIS model; it is neither an axiom nor a claimed
unconditional theorem.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- Every ACTUAL fixed-label double-divisor coefficient weight is
nonnegative. Its left and right support states require the genuine prime
divisor condition; no signed rational-center coefficient is asserted
nonnegative. -/
theorem actualMajorArcFinal_double_coefficient_weight_nonneg
    (S : Finset ℕ) (target : ℕ) (b : ℕ → ℕ)
    (a d : ℕ) :
    0 ≤ actualFixedLabelDoubleCoefficientWeight
      S target b a d := by
  unfold actualFixedLabelDoubleCoefficientWeight
  split
  · apply mul_nonneg
    · apply mul_nonneg
      · apply Finset.prod_nonneg
        intro p hp
        have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hlarge : (1 : ℝ) < p := by
          exact_mod_cast hprime.one_lt
        unfold actualFixedLabelLeftFactor
        split <;> positivity
      · apply Finset.prod_nonneg
        intro p hp
        have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hlarge : (1 : ℝ) < p := by
          exact_mod_cast hprime.one_lt
        unfold actualFixedLabelRightFactor
        split <;> positivity
    · apply Finset.prod_nonneg
      intro p hp
      unfold actualFixedLabelPrincipalFactor
      positivity
  · exact le_rfl

/-- The exact ORIGINAL support-divisor summed archimedean lattice model.
The essential `a*d` multiplier compensates the coefficient factors already
present in the true switched-state weight. Both original edge cutoffs and
the arbitrary-real robust strip remain in the lattice count. -/
noncomputable def actualMajorArcFinalCoefficientLatticeMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target : ℕ) (τ ell : ℝ) : ℝ :=
  ∑ a ∈ (∏ p ∈ S, p).divisors,
    ∑ d ∈ (∏ p ∈ S, p).divisors,
      actualFixedLabelDoubleCoefficientWeight S target b a d *
        (a : ℝ) * d *
          ((ternaryAffineTriples
            (actualMajorArcArchimedeanLeftWindow a n)
            (actualMajorArcArchimedeanCenterWindow d n)
            (actualMajorArcArchimedeanLabelWindow τ ell n)
            a (2 * d)).card : ℝ)

/-- The genuinely signed outside-support singular series uses the ACTUAL
sharp Farey denominator cutoff and removes exactly primes dividing `2W`. -/
noncomputable def actualMajorArcFinalOutsideSingularSeries
    (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ denominator ∈ Finset.Icc 1 (compatibleLogMinorCutoff n),
    actualMajorArcRestrictedSignedCoefficient
      (2 * (∏ p ∈ S, p)) denominator

/-- Full proposed rational-center main term: actual parity factor TWO,
sharp signed outside singular series, correct `1/φ(W)` robust-residue
density, and coefficient-compensated original edge-bounded lattice. -/
noncomputable def actualMajorArcFinalPredictedMain
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target : ℕ) (τ ell : ℝ) : ℝ :=
  2 * actualMajorArcFinalOutsideSingularSeries S n *
    (actualMajorArcFinalCoefficientLatticeMass
      S b n target τ ell /
      (((∏ p ∈ S, p).totient : ℕ) : ℝ))

/-- For every actual support-divisor pair, multiplication by its genuine
`a*d` coefficient cancels the corresponding `1/(a*d)` from the true
two-edge lattice. The lower constant is therefore SUPPORT-UNIFORM. -/
theorem actualMajorArcFinal_compensated_lattice_lower
    (a d : ℕ) (τ ell : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ∀ᶠ n : ℕ in atTop,
      ell * (n : ℝ) ^ 2 / 160 ≤
        (a : ℝ) * d *
          ((ternaryAffineTriples
            (actualMajorArcArchimedeanLeftWindow a n)
            (actualMajorArcArchimedeanCenterWindow d n)
            (actualMajorArcArchimedeanLabelWindow τ ell n)
            a (2 * d)).card : ℝ) := by
  filter_upwards
    [actualMajorArcArchimedean_true_edge_lattice_quadratic_lower
      a d τ ell ha hd hτ hell hstrip] with n hn
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    ell * (n : ℝ) ^ 2 / 160 =
        ((a : ℝ) * d) *
          (ell * (n : ℝ) ^ 2 / (160 * (a : ℝ) * d)) := by
      field_simp
    _ ≤ ((a : ℝ) * d) *
          ((ternaryAffineTriples
            (actualMajorArcArchimedeanLeftWindow a n)
            (actualMajorArcArchimedeanCenterWindow d n)
            (actualMajorArcArchimedeanLabelWindow τ ell n)
            a (2 * d)).card : ℝ) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by ring

/-- After summing ALL genuine support-divisor coefficient states and
dividing by the true robust-residue totient, the ORIGINAL compensated
two-edge lattice has uniform quadratic lower bound
`localFactor*ell*n²/160`. -/
theorem actualMajorArcFinal_coefficient_lattice_lower
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ)
    (hsupport :
      ∀ p ∈ S, p.Prime ∧ 3 < p ∧ J < p ∧ b p % p ≠ 0)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ∀ᶠ n : ℕ in atTop,
      ∀ target ∈ robustResidues S b J,
        manuscriptLocalSingularFactor S b target *
            ell * (n : ℝ) ^ 2 / 160 ≤
          actualMajorArcFinalCoefficientLatticeMass
              S b n target τ ell /
            (((∏ p ∈ S, p).totient : ℕ) : ℝ) := by
  classical
  let W := ∏ p ∈ S, p
  have hW : 0 < W :=
    Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hpositive (a : ℕ) (ha : a ∈ W.divisors) : 0 < a :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hW
  have hall :
      ∀ᶠ n : ℕ in atTop,
        ∀ a ∈ W.divisors, ∀ d ∈ W.divisors,
          ell * (n : ℝ) ^ 2 / 160 ≤
            (a : ℝ) * d *
              ((ternaryAffineTriples
                (actualMajorArcArchimedeanLeftWindow a n)
                (actualMajorArcArchimedeanCenterWindow d n)
                (actualMajorArcArchimedeanLabelWindow τ ell n)
                a (2 * d)).card : ℝ) := by
    apply (Filter.eventually_all_finset W.divisors).mpr
    intro a ha
    apply (Filter.eventually_all_finset W.divisors).mpr
    intro d hd
    exact actualMajorArcFinal_compensated_lattice_lower
      a d τ ell (hpositive a ha) (hpositive d hd) hτ hell hstrip
  filter_upwards [hall] with n hn
  intro target htarget
  have hweight (a d : ℕ) :
      0 ≤ actualFixedLabelDoubleCoefficientWeight
        S target b a d :=
    actualMajorArcFinal_double_coefficient_weight_nonneg
      S target b a d
  have hmass :
      (ell * (n : ℝ) ^ 2 / 160) *
        (∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
          actualFixedLabelDoubleCoefficientWeight
            S target b a d) ≤
        actualMajorArcFinalCoefficientLatticeMass
          S b n target τ ell := by
    calc
      _ = ∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
            (ell * (n : ℝ) ^ 2 / 160) *
              actualFixedLabelDoubleCoefficientWeight
                S target b a d := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
            actualFixedLabelDoubleCoefficientWeight
                S target b a d * (a : ℝ) * d *
              ((ternaryAffineTriples
                (actualMajorArcArchimedeanLeftWindow a n)
                (actualMajorArcArchimedeanCenterWindow d n)
                (actualMajorArcArchimedeanLabelWindow τ ell n)
                a (2 * d)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro d hd
          have hterm := mul_le_mul_of_nonneg_left
            (hn a ha d hd) (hweight a d)
          nlinarith
      _ = _ := rfl
  have hb : ∀ p ∈ S, ¬ p ∣ b p := by
    intro p hp hdivide
    exact (hsupport p hp).2.2.2
      (Nat.mod_eq_zero_of_dvd hdivide)
  have hlocal :=
    actualMajorArcSupport_double_coefficient_sum_div_totient_eq_local
      S b J target
      (fun p hp => ⟨(hsupport p hp).1, (hsupport p hp).2.1⟩)
      hb htarget
  have hlocalDouble :
      (∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
        actualFixedLabelDoubleCoefficientWeight S target b a d) /
          (W.totient : ℝ) =
        manuscriptLocalSingularFactor S b target := by
    simpa [W, Finset.sum_product] using hlocal
  change
    manuscriptLocalSingularFactor S b target *
      ell * (n : ℝ) ^ 2 / 160 ≤
        actualMajorArcFinalCoefficientLatticeMass
          S b n target τ ell / (W.totient : ℝ)
  calc
    _ = (ell * (n : ℝ) ^ 2 / 160) *
          manuscriptLocalSingularFactor S b target := by ring
    _ = (ell * (n : ℝ) ^ 2 / 160) *
          ((∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
            actualFixedLabelDoubleCoefficientWeight
              S target b a d) / (W.totient : ℝ)) := by
          rw [hlocalDouble]
    _ = ((ell * (n : ℝ) ^ 2 / 160) *
          (∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
            actualFixedLabelDoubleCoefficientWeight
              S target b a d)) / (W.totient : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hmass (by positivity)

/-- The sharp actual outside-support signed series is eventually at least
`1/4`, including the genuine exclusion of parity and all support primes. -/
theorem actualMajorArcFinal_outside_singular_series_lower
    (S : Finset ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) ≤ actualMajorArcFinalOutsideSingularSeries S n := by
  simpa [actualMajorArcFinalOutsideSingularSeries] using
    (actualMajorArcRestrictedSignedCoefficient_compatible_cutoff_ge_quarter
      (2 * (∏ p ∈ S, p)) (dvd_mul_right 2 _))

/-- UNCONDITIONAL positivity of the complete EXPLICIT original
coefficient-compensated support/parity/outside/archimedean singular model,
uniform for every robust residue, with absolute constant `1/320`. -/
theorem actualMajorArcFinal_predicted_main_quadratic_lower
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ)
    (hsupport :
      ∀ p ∈ S, p.Prime ∧ 3 < p ∧ J < p ∧ b p % p ≠ 0)
    (hτ : 0 < τ) (hell : 0 < ell)
    (hstrip : τ + ell < (1 : ℝ) / 10) :
    ∀ᶠ n : ℕ in atTop,
      ∀ target ∈ robustResidues S b J,
        manuscriptLocalSingularFactor S b target *
            ell * (n : ℝ) ^ 2 / 320 ≤
          actualMajorArcFinalPredictedMain
            S b n target τ ell := by
  filter_upwards
    [actualMajorArcFinal_coefficient_lattice_lower
      S b J τ ell hsupport hτ hell hstrip,
      actualMajorArcFinal_outside_singular_series_lower S]
    with n hlattice hseries
  intro target htarget
  have hlocal : 0 < manuscriptLocalSingularFactor S b target :=
    manuscriptLocalSingularFactor_pos S b target
      (fun p hp => (hsupport p hp).2.1)
  have hmain := hlattice target htarget
  have hmass :
      0 ≤ actualMajorArcFinalCoefficientLatticeMass
          S b n target τ ell /
        (((∏ p ∈ S, p).totient : ℕ) : ℝ) := by
    exact (by positivity :
      0 ≤ manuscriptLocalSingularFactor S b target *
        ell * (n : ℝ) ^ 2 / 160).trans hmain
  unfold actualMajorArcFinalPredictedMain
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
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ ≤ (2 * actualMajorArcFinalOutsideSingularSeries S n) *
          (actualMajorArcFinalCoefficientLatticeMass
            S b n target τ ell /
            (((∏ p ∈ S, p).totient : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hmass
      linarith
    _ = _ := by ring

/-- The single exact unresolved coupling: the ORIGINAL deduplicated,
coefficient-summed prime major-center mass must equal the fully specified
support/parity/outside/lattice singular model up to `o(n²)`.  Every
quantifier retains the actual support, robust residue, true real strip,
sharp Farey cutoff and genuine deduplicated shifted center geometry. -/
def UniformActualDeduplicatedSingularModelCoupling : Prop :=
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
              actualMajorArcFinalPredictedMain
                S b n target τ ell| / (n : ℝ) ^ 2)
          atTop (nhds 0)

/-- Exact single-obligation positivity reduction. Once the actual
deduplicated rational-center integral is coupled to the EXPLICIT genuine
singular model, the original major positivity follows with the absolute
constant `1/640`, chosen BEFORE every support and target. -/
theorem uniformActualCoefficientSummedMajorArcPositivity_of_singular_model_coupling
    (hcoupling : UniformActualDeduplicatedSingularModelCoupling) :
    UniformActualCoefficientSummedMajorArcPositivity := by
  apply uniformActualSummedMajorPositivity_iff_deduplicated_center.mpr
  refine ⟨(1 / 640 : ℝ), by norm_num, ?_⟩
  intro S b J τ ell hsupport hτ hell hstrip
  have herror :
      ∀ᶠ n : ℕ in atTop,
        ∀ target ∈ robustResidues S b J,
          |actualDeduplicatedMajorPrimeMass S b n J target
              (compatibleLogMinorCutoff n)
              (fullyCompatibleFareyCutoff
                (fun m => Nat.floor (τ * (m : ℝ))) n)
              τ ell -
            actualMajorArcFinalPredictedMain
              S b n target τ ell| / (n : ℝ) ^ 2 <
            manuscriptLocalSingularFactor S b target * ell / 640 := by
    apply (Filter.eventually_all_finset
      (robustResidues S b J)).mpr
    intro target htarget
    apply (tendsto_order.1
      (hcoupling S b J τ ell hsupport hτ hell hstrip
        target htarget)).2
    have hlocal : 0 < manuscriptLocalSingularFactor S b target :=
      manuscriptLocalSingularFactor_pos S b target
        (fun p hp => (hsupport p hp).2.1)
    positivity
  filter_upwards
    [actualMajorArcFinal_predicted_main_quadratic_lower
      S b J τ ell hsupport hτ hell hstrip,
      herror, eventually_gt_atTop (0 : ℕ)]
    with n hmain herrorN hn
  intro target htarget
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have htargetMain := hmain target htarget
  have htargetError := herrorN target htarget
  have htargetError' :
      |actualDeduplicatedMajorPrimeMass S b n J target
          (compatibleLogMinorCutoff n)
          (fullyCompatibleFareyCutoff
            (fun m => Nat.floor (τ * (m : ℝ))) n)
          τ ell -
        actualMajorArcFinalPredictedMain
          S b n target τ ell| <
        (manuscriptLocalSingularFactor S b target * ell / 640) *
          (n : ℝ) ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hnreal)).mp htargetError
  have hsign := neg_abs_le
    (actualDeduplicatedMajorPrimeMass S b n J target
      (compatibleLogMinorCutoff n)
      (fullyCompatibleFareyCutoff
        (fun m => Nat.floor (τ * (m : ℝ))) n)
      τ ell -
      actualMajorArcFinalPredictedMain
        S b n target τ ell)
  nlinarith

/-- The exact historical Erdős #689 covering conclusion from its SINGLE
remaining explicit deduplicated-center/singular-factor coupling.  All
three original graph degrees, prime-only minors, singular-factor positivity,
support coefficient normalization, and true edge-window lattice bounds
are inserted unconditionally. This is a conditional theorem, not a
resolution of the still-open original problem. -/
theorem officialStatement_of_actual_singular_model_coupling
    (hcoupling : UniformActualDeduplicatedSingularModelCoupling) :
    OfficialStatement := by
  exact officialStatement_of_actual_summed_major_positivity
    (uniformActualCoefficientSummedMajorArcPositivity_of_singular_model_coupling
      hcoupling)

#print axioms Erdos689.actualMajorArcFinal_double_coefficient_weight_nonneg
#print axioms Erdos689.actualMajorArcFinal_compensated_lattice_lower
#print axioms Erdos689.actualMajorArcFinal_coefficient_lattice_lower
#print axioms Erdos689.actualMajorArcFinal_outside_singular_series_lower
#print axioms Erdos689.actualMajorArcFinal_predicted_main_quadratic_lower
#print axioms Erdos689.uniformActualCoefficientSummedMajorArcPositivity_of_singular_model_coupling
#print axioms Erdos689.officialStatement_of_actual_singular_model_coupling

end Erdos689
