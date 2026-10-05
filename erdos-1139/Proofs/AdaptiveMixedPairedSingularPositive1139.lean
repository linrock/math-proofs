module

public import AdaptiveMixedCorrelationComplexity1139
public import WeightedPrimePatternMomentBridge1139
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section


/-!
# Collision-aware paired singular positivity and genuine signed windows

The actual same-support, same-type shared-target system has two prime labels,
all target forms from both mixed outcomes, and ONE deduplicated common target.
Its normalized local factor is the product of the two ACTUAL collision-aware
individual factors.  Consequently all finite paired Euler products possess one
strictly positive, support-independent floor.

Physical adaptive centers are SIGNED.  The genuine shared-target archimedean
cell is the strict rational convex region in `(h,P,P')` given by BOTH physical
strips

    d P < h < (d+1) P,       e P' < h < (e+1) P',

together with the label cells and target interval.  A cell is used only when it
contains a strict interior point; zero-volume/empty pairs are excluded.

All finite-complexity, local-admissibility, paired singular positivity, and
signed physical-domain facts are proved.  Any Green--Tao--Ziegler prime-count
conclusion remains an EXPLICIT theorem parameter, never an axiom.  This file
does not prove the Erdős #1139 conjecture.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos1139

/-- Package the number of DISTINCT actual forbidden outside-prime slopes
without a dependent typeclass argument; collisions are retained exactly. -/
noncomputable def adaptiveMixedActualOutsideRootCount
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (ell : ℕ) : ℕ :=
  if prime : ell.Prime then
    (@adaptiveMixedOutcomeLocalForbidden
      support scale ell outcome ⟨prime⟩).card
  else 0

/-- The two normalizations of the SAME genuine mixed local selector agree:
the mixed Euler normalization is exactly the audited shared-target
individual-pattern normalization. -/
theorem adaptiveMixedActualNormalizedLocalFactor_eq_shared_normalization
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    [Fact ell.Prime] :
    adaptiveMixedActualNormalizedLocalFactor
      support scale ell outcome =
        sharedTargetIndividualNormalizedFactor ell
          (adaptiveMixedOutcomeActiveIndices support scale outcome).card
          (adaptiveMixedActualLocalSelectors
            support scale ell outcome).card := by
  have prime : ell.Prime := Fact.out
  have ell_nonzero : (ell : ℝ) ≠ 0 := by
    exact_mod_cast prime.ne_zero
  have denominator_nonzero : (ell : ℝ) - 1 ≠ 0 := by
    have larger : (1 : ℝ) < ell := by
      exact_mod_cast prime.one_lt
    linarith
  have density :
      sharedTargetPrimeUnitDensity ell =
        ((ell : ℝ) - 1) / (ell : ℝ) := by
    unfold sharedTargetPrimeUnitDensity
    field_simp
  have inverse_density :
      (ell : ℝ) / ((ell : ℝ) - 1) =
        (sharedTargetPrimeUnitDensity ell)⁻¹ := by
    rw [density]
    field_simp
  unfold adaptiveMixedActualNormalizedLocalFactor
    sharedTargetIndividualNormalizedFactor
  rw [inverse_density]
  simp [div_eq_mul_inv]

/-- The EXACT audited individual shared-target model factor is the ACTUAL
mixed normalized local factor, with every outside-root collision preserved. -/
theorem adaptiveMixedSharedTarget_individual_factor_eq_actual
    (support : Finset ℕ) (scale ell : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (prime : ell.Prime) :
    sharedTargetIndividualPatternLocalFactor support
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card
      (adaptiveMixedActualOutsideRootCount support scale outcome) ell =
        adaptiveMixedActualScalarLocalFactor
          support scale ell outcome := by
  classical
  simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
  rw [@adaptiveMixedActualNormalizedLocalFactor_eq_shared_normalization
    support scale ell outcome ⟨prime⟩]
  unfold sharedTargetIndividualPatternLocalFactor
  split_ifs with supported
  · rw [@adaptiveMixedActualLocalSelectors_card_supported
      support scale ell outcome ⟨prime⟩ primes supported]
  · rw [@adaptiveMixedActualLocalSelectors_card_outside
      support scale ell outcome ⟨prime⟩ primes supported]
    simp [adaptiveMixedActualOutsideRootCount, prime]

/-- The ACTUAL collision-aware, deduplicated same-type shared-target scalar
factor at one prime.  It uses the TRUE ranks and the exact distinct slopes
of each independently sampled outcome. -/
noncomputable def adaptiveMixedActualSharedTargetScalarLocalFactor
    (support : Finset ℕ) (scale : ℕ)
    (first second : ℕ × ℕ) (ell : ℕ) : ℝ :=
  sharedTargetPairedPatternLocalFactor support
    (adaptiveMixedOutcomeActiveIndices support scale first).card
    (adaptiveMixedOutcomeActiveIndices support scale second).card
    (adaptiveMixedActualOutsideRootCount support scale first)
    (adaptiveMixedActualOutsideRootCount support scale second) ell

/-- Single-prime EXACT factorization into the two genuine actual mixed local
factors.  The common target is counted once and local label residues may agree. -/
theorem adaptiveMixedActualSharedTargetScalarLocalFactor_eq_product
    (support : Finset ℕ) (scale ell : ℕ)
    (first second : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (prime : ell.Prime) :
    adaptiveMixedActualSharedTargetScalarLocalFactor
      support scale first second ell =
        adaptiveMixedActualScalarLocalFactor support scale ell first *
          adaptiveMixedActualScalarLocalFactor support scale ell second := by
  unfold adaptiveMixedActualSharedTargetScalarLocalFactor
  rw [sharedTargetPatternLocalFactor_eq_product prime]
  rw [adaptiveMixedSharedTarget_individual_factor_eq_actual
    support scale ell first primes prime]
  rw [adaptiveMixedSharedTarget_individual_factor_eq_actual
    support scale ell second primes prime]

/-- EXACT full finite Euler-product factorization for the ACTUAL two
independently sampled collision-aware mixed outcomes. -/
theorem adaptiveMixedActualSharedTarget_finite_singular_product_eq_product
    (support : Finset ℕ) (scale : ℕ)
    (first second : ℕ × ℕ) (evaluation : Finset ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (evaluation_primes : ∀ ell ∈ evaluation, ell.Prime) :
    (∏ ell ∈ evaluation,
      adaptiveMixedActualSharedTargetScalarLocalFactor
        support scale first second ell) =
      (∏ ell ∈ evaluation,
        adaptiveMixedActualScalarLocalFactor support scale ell first) *
      (∏ ell ∈ evaluation,
        adaptiveMixedActualScalarLocalFactor support scale ell second) := by
  calc
    _ = ∏ ell ∈ evaluation,
          (adaptiveMixedActualScalarLocalFactor support scale ell first *
            adaptiveMixedActualScalarLocalFactor support scale ell second) := by
      apply Finset.prod_congr rfl
      intro ell selected
      exact adaptiveMixedActualSharedTargetScalarLocalFactor_eq_product
        support scale ell first second primes
          (evaluation_primes ell selected)
    _ = _ := by rw [Finset.prod_mul_distrib]

/-- A genuine mixed outcome of rank zero or one has NO possible forbidden
root collisions: its exact root count equals its exact physical rank. -/
theorem adaptiveMixedOutcomeLocalForbidden_card_eq_rank_of_rank_le_one
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (small_rank :
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card ≤ 1) :
    (adaptiveMixedOutcomeLocalForbidden
      support scale ell outcome).card =
        (adaptiveMixedOutcomeActiveIndices support scale outcome).card := by
  unfold adaptiveMixedOutcomeLocalForbidden
  apply Finset.card_image_iff.mpr
  intro first first_active second second_active _equal
  exact (Finset.card_le_one.mp small_rank)
    first first_active second second_active

/-- At every unsupported prime, the genuine rank-zero OR rank-one mixed
normalized local factor is EXACTLY one.  Thus these indispensable adaptive
patterns need no omitted rank-two Euler-tail hypothesis. -/
theorem adaptiveMixedActualNormalizedLocalFactor_outside_eq_one_of_rank_le_one
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (outside : ell ∉ support)
    (small_rank :
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card ≤ 1) :
    adaptiveMixedActualNormalizedLocalFactor
      support scale ell outcome = 1 := by
  have prime : ell.Prime := Fact.out
  have ell_nonzero : (ell : ℝ) ≠ 0 := by
    exact_mod_cast prime.ne_zero
  have denominator_nonzero : (ell : ℝ) - 1 ≠ 0 := by
    have larger : (1 : ℝ) < ell := by
      exact_mod_cast prime.one_lt
    linarith
  rw [adaptiveMixedActualNormalizedLocalFactor_outside primes outside,
    adaptiveMixedOutcomeLocalForbidden_card_eq_rank_of_rank_le_one small_rank]
  have cases_rank :
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card = 0 ∨
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card = 1 := by
    omega
  rcases cases_rank with rank_zero | rank_one
  · simp [rank_zero, ell_nonzero]
  · rw [rank_one]
    push_cast [Nat.cast_sub prime.one_le]
    field_simp

/-- Every rank-zero or rank-one actual mixed local factor is at least one,
including supported squared primes and every omitted outside prime. -/
theorem adaptiveMixedActualNormalizedLocalFactor_ge_one_of_rank_le_one
    {support : Finset ℕ} {scale ell : ℕ} {outcome : ℕ × ℕ}
    [Fact ell.Prime]
    (primes : ∀ prime ∈ support, prime.Prime)
    (small_rank :
      (adaptiveMixedOutcomeActiveIndices support scale outcome).card ≤ 1) :
    (1 : ℝ) ≤ adaptiveMixedActualNormalizedLocalFactor
      support scale ell outcome := by
  by_cases supported : ell ∈ support
  · exact adaptiveMixedActualNormalizedLocalFactor_supported_ge_one
      primes supported
  · rw [adaptiveMixedActualNormalizedLocalFactor_outside_eq_one_of_rank_le_one
      primes supported small_rank]

/-- UNCONDITIONAL actual mixed singular positivity for EVERY retained rank,
including the rank-zero and rank-one patterns present in adaptive sampling. -/
theorem adaptiveMixedActualNormalizedLocalFactor_uniform_positive_all_ranks
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ evaluation : Finset ℕ,
        (∀ ell ∈ evaluation, ell.Prime) →
          constant ≤ ∏ ell ∈ evaluation,
            adaptiveMixedActualScalarLocalFactor
              support scale ell outcome := by
  by_cases large :
      2 ≤ (adaptiveMixedOutcomeActiveIndices support scale outcome).card
  · exact adaptiveMixedActualNormalizedLocalFactor_uniform_positive
      support scale outcome primes large
  · have small :
        (adaptiveMixedOutcomeActiveIndices support scale outcome).card ≤ 1 := by
      omega
    refine ⟨1, by norm_num, ?_⟩
    intro evaluation evaluation_primes
    apply Finset.one_le_prod₀
    intro ell selected
    have prime := evaluation_primes ell selected
    simp only [adaptiveMixedActualScalarLocalFactor, dif_pos prime]
    exact @adaptiveMixedActualNormalizedLocalFactor_ge_one_of_rank_le_one
      support scale ell outcome ⟨prime⟩ primes small

/-- ONE strictly positive pair-dependent constant bounds below EVERY finite
genuine shared-target Euler product, independently of its evaluation support. -/
theorem adaptiveMixedActualSharedTarget_singular_product_uniform_positive
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ evaluation : Finset ℕ,
        (∀ ell ∈ evaluation, ell.Prime) →
          constant ≤ ∏ ell ∈ evaluation,
            adaptiveMixedActualSharedTargetScalarLocalFactor
              support scale first second ell := by
  obtain ⟨first_constant, first_positive, first_lower⟩ :=
    adaptiveMixedActualNormalizedLocalFactor_uniform_positive_all_ranks
      support scale first primes
  obtain ⟨second_constant, second_positive, second_lower⟩ :=
    adaptiveMixedActualNormalizedLocalFactor_uniform_positive_all_ranks
      support scale second primes
  refine ⟨first_constant * second_constant,
    mul_pos first_positive second_positive, ?_⟩
  intro evaluation evaluation_primes
  rw [adaptiveMixedActualSharedTarget_finite_singular_product_eq_product
    support scale first second evaluation primes evaluation_primes]
  exact mul_le_mul
    (first_lower evaluation evaluation_primes)
    (second_lower evaluation evaluation_primes)
    second_positive.le
    (adaptiveMixedActualNormalizedLocalFactor_finite_product_pos
      support scale first primes evaluation evaluation_primes).le

/-- BOTH genuine physical adaptive centers are necessarily negative when
their actual bases are positive.  Positive natural-center boxes therefore do
not parametrize these shared-target edges. -/
theorem adaptiveMixedPairedSignedCenters_negative_of_positive_bases
    (support : Finset ℕ)
    (firstBase secondBase firstLabel secondLabel : ℕ)
    (firstCenter secondCenter : ℤ)
    (first_base_positive : 0 < firstBase)
    (second_base_positive : 0 < secondBase)
    (first_strip_upper :
      weightedPrimePatternSignedResidue
        support firstBase firstLabel firstCenter < (firstLabel : ℤ))
    (second_strip_upper :
      weightedPrimePatternSignedResidue
        support secondBase secondLabel secondCenter < (secondLabel : ℤ)) :
    firstCenter < 0 ∧ secondCenter < 0 := by
  exact
    ⟨weightedPrimePattern_valid_center_negative_of_positive_base
      support firstBase firstLabel firstCenter
        first_base_positive first_strip_upper,
     weightedPrimePattern_valid_center_negative_of_positive_base
      support secondBase secondLabel secondCenter
        second_base_positive second_strip_upper⟩

/-- The TRUE two signed branch centers imply BOTH physical moving strips for
their ONE common target.  The lower edges are genuinely closed and the upper
edges genuinely open. -/
theorem adaptiveMixedPairedSignedTarget_mem_physical_strips
    (support : Finset ℕ)
    (firstBase secondBase firstIndex secondIndex firstLabel secondLabel : ℕ)
    (firstCenter secondCenter target : ℤ)
    (first_strip_lower :
      0 ≤ weightedPrimePatternSignedResidue
        support firstBase firstLabel firstCenter)
    (first_strip_upper :
      weightedPrimePatternSignedResidue
        support firstBase firstLabel firstCenter < (firstLabel : ℤ))
    (second_strip_lower :
      0 ≤ weightedPrimePatternSignedResidue
        support secondBase secondLabel secondCenter)
    (second_strip_upper :
      weightedPrimePatternSignedResidue
        support secondBase secondLabel secondCenter < (secondLabel : ℤ))
    (first_target :
      target = (firstIndex : ℤ) * (firstLabel : ℤ) +
        weightedPrimePatternSignedResidue
          support firstBase firstLabel firstCenter)
    (second_target :
      target = (secondIndex : ℤ) * (secondLabel : ℤ) +
        weightedPrimePatternSignedResidue
          support secondBase secondLabel secondCenter) :
    (firstIndex : ℤ) * (firstLabel : ℤ) ≤ target ∧
      target < ((firstIndex : ℤ) + 1) * (firstLabel : ℤ) ∧
      (secondIndex : ℤ) * (secondLabel : ℤ) ≤ target ∧
      target < ((secondIndex : ℤ) + 1) * (secondLabel : ℤ) := by
  constructor
  · omega
  constructor
  · nlinarith
  constructor
  · omega
  · nlinarith

/-- The honest OPEN interior of an actual shared-target physical cell in
coordinates `(h,P,P')`.  BOTH label cells, the target window, and BOTH true
index-dependent strips are retained; there is no fake independent center box. -/
def adaptiveMixedSharedTargetPhysicalConvexWindow
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {point |
    targetLower < point.1 ∧ point.1 < targetUpper ∧
      firstLabelLower < point.2.1 ∧ point.2.1 < firstLabelUpper ∧
      secondLabelLower < point.2.2 ∧ point.2.2 < secondLabelUpper ∧
      (firstIndex : ℝ) * point.2.1 < point.1 ∧
      point.1 < ((firstIndex + 1 : ℕ) : ℝ) * point.2.1 ∧
      (secondIndex : ℝ) * point.2.2 < point.1 ∧
      point.1 < ((secondIndex + 1 : ℕ) : ℝ) * point.2.2}

/-- Every point of the actual strict archimedean interior satisfies the
original CLOSED-lower/OPEN-upper physical strips on BOTH branches. -/
theorem adaptiveMixedSharedTargetPhysicalConvexWindow_mem_true_strips
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ)
    {point : ℝ × ℝ × ℝ}
    (selected : point ∈ adaptiveMixedSharedTargetPhysicalConvexWindow
      firstIndex secondIndex targetLower targetUpper
      firstLabelLower firstLabelUpper secondLabelLower secondLabelUpper) :
    (firstIndex : ℝ) * point.2.1 ≤ point.1 ∧
      point.1 < ((firstIndex + 1 : ℕ) : ℝ) * point.2.1 ∧
      (secondIndex : ℝ) * point.2.2 ≤ point.1 ∧
      point.1 < ((secondIndex + 1 : ℕ) : ℝ) * point.2.2 := by
  exact ⟨selected.2.2.2.2.2.2.1.le,
    selected.2.2.2.2.2.2.2.1,
    selected.2.2.2.2.2.2.2.2.1.le,
    selected.2.2.2.2.2.2.2.2.2⟩

/-- Nonnegative convex weights summing to one preserve STRICT affine
inequalities; this handles every real physical strip without assuming either
weight separately positive. -/
theorem adaptiveMixedStrictConvexAverage_preserves_lt
    {firstWeight secondWeight firstLeft firstRight secondLeft secondRight : ℝ}
    (first_nonnegative : 0 ≤ firstWeight)
    (second_nonnegative : 0 ≤ secondWeight)
    (normalized : firstWeight + secondWeight = 1)
    (first_strict : firstLeft < firstRight)
    (second_strict : secondLeft < secondRight) :
    firstWeight * firstLeft + secondWeight * secondLeft <
      firstWeight * firstRight + secondWeight * secondRight := by
  by_cases first_zero : firstWeight = 0
  · have second_one : secondWeight = 1 := by linarith
    simpa [first_zero, second_one] using second_strict
  · have first_positive : 0 < firstWeight :=
      lt_of_le_of_ne first_nonnegative (Ne.symm first_zero)
    have first_gain :
        0 < firstWeight * (firstRight - firstLeft) :=
      mul_pos first_positive (sub_pos.mpr first_strict)
    have second_gain :
        0 ≤ secondWeight * (secondRight - secondLeft) :=
      mul_nonneg second_nonnegative (sub_nonneg.mpr second_strict.le)
    nlinarith

/-- The genuine simultaneous `(h,P,P')` physical strip cell is CONVEX,
including all label-cell, target-window, and both moving-strip constraints. -/
theorem adaptiveMixedSharedTargetPhysicalConvexWindow_convex
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ) :
    Convex ℝ (adaptiveMixedSharedTargetPhysicalConvexWindow
      firstIndex secondIndex targetLower targetUpper
      firstLabelLower firstLabelUpper secondLabelLower secondLabelUpper) := by
  intro first first_selected second second_selected
    firstWeight secondWeight first_nonnegative second_nonnegative normalized
  change
    targetLower < first.1 ∧ first.1 < targetUpper ∧
      firstLabelLower < first.2.1 ∧ first.2.1 < firstLabelUpper ∧
      secondLabelLower < first.2.2 ∧ first.2.2 < secondLabelUpper ∧
      (firstIndex : ℝ) * first.2.1 < first.1 ∧
      first.1 < ((firstIndex + 1 : ℕ) : ℝ) * first.2.1 ∧
      (secondIndex : ℝ) * first.2.2 < first.1 ∧
      first.1 < ((secondIndex + 1 : ℕ) : ℝ) * first.2.2 at first_selected
  change
    targetLower < second.1 ∧ second.1 < targetUpper ∧
      firstLabelLower < second.2.1 ∧ second.2.1 < firstLabelUpper ∧
      secondLabelLower < second.2.2 ∧ second.2.2 < secondLabelUpper ∧
      (firstIndex : ℝ) * second.2.1 < second.1 ∧
      second.1 < ((firstIndex + 1 : ℕ) : ℝ) * second.2.1 ∧
      (secondIndex : ℝ) * second.2.2 < second.1 ∧
      second.1 < ((secondIndex + 1 : ℕ) : ℝ) * second.2.2 at second_selected
  change
    targetLower < firstWeight * first.1 + secondWeight * second.1 ∧
      firstWeight * first.1 + secondWeight * second.1 < targetUpper ∧
      firstLabelLower <
        firstWeight * first.2.1 + secondWeight * second.2.1 ∧
      firstWeight * first.2.1 + secondWeight * second.2.1 < firstLabelUpper ∧
      secondLabelLower <
        firstWeight * first.2.2 + secondWeight * second.2.2 ∧
      firstWeight * first.2.2 + secondWeight * second.2.2 < secondLabelUpper ∧
      (firstIndex : ℝ) *
          (firstWeight * first.2.1 + secondWeight * second.2.1) <
        firstWeight * first.1 + secondWeight * second.1 ∧
      firstWeight * first.1 + secondWeight * second.1 <
        ((firstIndex + 1 : ℕ) : ℝ) *
          (firstWeight * first.2.1 + secondWeight * second.2.1) ∧
      (secondIndex : ℝ) *
          (firstWeight * first.2.2 + secondWeight * second.2.2) <
        firstWeight * first.1 + secondWeight * second.1 ∧
      firstWeight * first.1 + secondWeight * second.1 <
        ((secondIndex + 1 : ℕ) : ℝ) *
          (firstWeight * first.2.2 + secondWeight * second.2.2)
  rcases first_selected with
    ⟨first_target_lower, first_target_upper,
      first_label_lower, first_label_upper,
      first_other_lower, first_other_upper,
      first_strip_lower, first_strip_upper,
      first_other_strip_lower, first_other_strip_upper⟩
  rcases second_selected with
    ⟨second_target_lower, second_target_upper,
      second_label_lower, second_label_upper,
      second_other_lower, second_other_upper,
      second_strip_lower, second_strip_upper,
      second_other_strip_lower, second_other_strip_upper⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      targetLower = firstWeight * targetLower +
          secondWeight * targetLower := by
        rw [← add_mul, normalized, one_mul]
      _ < _ := adaptiveMixedStrictConvexAverage_preserves_lt
        first_nonnegative second_nonnegative normalized
          first_target_lower second_target_lower
  · calc
      _ < firstWeight * targetUpper + secondWeight * targetUpper :=
        adaptiveMixedStrictConvexAverage_preserves_lt
          first_nonnegative second_nonnegative normalized
            first_target_upper second_target_upper
      _ = targetUpper := by rw [← add_mul, normalized, one_mul]
  · calc
      firstLabelLower = firstWeight * firstLabelLower +
          secondWeight * firstLabelLower := by
        rw [← add_mul, normalized, one_mul]
      _ < _ := adaptiveMixedStrictConvexAverage_preserves_lt
        first_nonnegative second_nonnegative normalized
          first_label_lower second_label_lower
  · calc
      _ < firstWeight * firstLabelUpper + secondWeight * firstLabelUpper :=
        adaptiveMixedStrictConvexAverage_preserves_lt
          first_nonnegative second_nonnegative normalized
            first_label_upper second_label_upper
      _ = firstLabelUpper := by rw [← add_mul, normalized, one_mul]
  · calc
      secondLabelLower = firstWeight * secondLabelLower +
          secondWeight * secondLabelLower := by
        rw [← add_mul, normalized, one_mul]
      _ < _ := adaptiveMixedStrictConvexAverage_preserves_lt
        first_nonnegative second_nonnegative normalized
          first_other_lower second_other_lower
  · calc
      _ < firstWeight * secondLabelUpper + secondWeight * secondLabelUpper :=
        adaptiveMixedStrictConvexAverage_preserves_lt
          first_nonnegative second_nonnegative normalized
            first_other_upper second_other_upper
      _ = secondLabelUpper := by rw [← add_mul, normalized, one_mul]
  · calc
      _ = firstWeight * ((firstIndex : ℝ) * first.2.1) +
          secondWeight * ((firstIndex : ℝ) * second.2.1) := by ring
      _ < _ := adaptiveMixedStrictConvexAverage_preserves_lt
        first_nonnegative second_nonnegative normalized
          first_strip_lower second_strip_lower
  · calc
      _ < firstWeight *
          (((firstIndex + 1 : ℕ) : ℝ) * first.2.1) +
          secondWeight *
            (((firstIndex + 1 : ℕ) : ℝ) * second.2.1) :=
        adaptiveMixedStrictConvexAverage_preserves_lt
          first_nonnegative second_nonnegative normalized
            first_strip_upper second_strip_upper
      _ = _ := by ring
  · calc
      _ = firstWeight * ((secondIndex : ℝ) * first.2.2) +
          secondWeight * ((secondIndex : ℝ) * second.2.2) := by ring
      _ < _ := adaptiveMixedStrictConvexAverage_preserves_lt
        first_nonnegative second_nonnegative normalized
          first_other_strip_lower second_other_strip_lower
  · calc
      _ < firstWeight *
          (((secondIndex + 1 : ℕ) : ℝ) * first.2.2) +
          secondWeight *
            (((secondIndex + 1 : ℕ) : ℝ) * second.2.2) :=
        adaptiveMixedStrictConvexAverage_preserves_lt
          first_nonnegative second_nonnegative normalized
            first_other_strip_upper second_other_strip_upper
      _ = _ := by ring

/-- Every genuine simultaneous physical cell is OPEN; its lower-strip
boundary was deliberately removed before a positive-volume claim is made. -/
theorem adaptiveMixedSharedTargetPhysicalConvexWindow_isOpen
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ) :
    IsOpen (adaptiveMixedSharedTargetPhysicalConvexWindow
      firstIndex secondIndex targetLower targetUpper
      firstLabelLower firstLabelUpper secondLabelLower secondLabelUpper) := by
  have target_continuous :
      Continuous (fun point : ℝ × ℝ × ℝ => point.1) :=
    continuous_fst
  have first_continuous :
      Continuous (fun point : ℝ × ℝ × ℝ => point.2.1) :=
    continuous_fst.comp continuous_snd
  have second_continuous :
      Continuous (fun point : ℝ × ℝ × ℝ => point.2.2) :=
    continuous_snd.comp continuous_snd
  have first_strip_lower_continuous :
      Continuous (fun point : ℝ × ℝ × ℝ =>
        (firstIndex : ℝ) * point.2.1) :=
    continuous_const.mul first_continuous
  have first_strip_upper_continuous :
      Continuous (fun point : ℝ × ℝ × ℝ =>
        ((firstIndex + 1 : ℕ) : ℝ) * point.2.1) :=
    continuous_const.mul first_continuous
  have second_strip_lower_continuous :
      Continuous (fun point : ℝ × ℝ × ℝ =>
        (secondIndex : ℝ) * point.2.2) :=
    continuous_const.mul second_continuous
  have second_strip_upper_continuous :
      Continuous (fun point : ℝ × ℝ × ℝ =>
        ((secondIndex + 1 : ℕ) : ℝ) * point.2.2) :=
    continuous_const.mul second_continuous
  unfold adaptiveMixedSharedTargetPhysicalConvexWindow
  exact (isOpen_lt continuous_const target_continuous).inter
    ((isOpen_lt target_continuous continuous_const).inter
      ((isOpen_lt continuous_const first_continuous).inter
        ((isOpen_lt first_continuous continuous_const).inter
          ((isOpen_lt continuous_const second_continuous).inter
            ((isOpen_lt second_continuous continuous_const).inter
              ((isOpen_lt first_strip_lower_continuous target_continuous).inter
                ((isOpen_lt target_continuous first_strip_upper_continuous).inter
                  ((isOpen_lt second_strip_lower_continuous target_continuous).inter
                    (isOpen_lt target_continuous
                      second_strip_upper_continuous)))))))))

/-- A strict physical cell has POSITIVE genuine three-dimensional Lebesgue
volume exactly when it contains an actual strict-interior point. -/
theorem adaptiveMixedSharedTargetPhysicalConvexWindow_volume_pos
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ)
    (interior :
      (adaptiveMixedSharedTargetPhysicalConvexWindow
        firstIndex secondIndex targetLower targetUpper
        firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper).Nonempty) :
    0 < volume
      (adaptiveMixedSharedTargetPhysicalConvexWindow
        firstIndex secondIndex targetLower targetUpper
        firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper) := by
  exact (adaptiveMixedSharedTargetPhysicalConvexWindow_isOpen
    firstIndex secondIndex targetLower targetUpper
      firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper).measure_pos volume interior

/-- Zero-volume/empty cell pairs are EXCLUDED rather than silently treated as
positive-volume Green--Tao domains. -/
theorem adaptiveMixedSharedTargetPhysicalConvexWindow_volume_zero_iff_empty
    (firstIndex secondIndex : ℕ)
    (targetLower targetUpper firstLabelLower firstLabelUpper
      secondLabelLower secondLabelUpper : ℝ) :
    volume (adaptiveMixedSharedTargetPhysicalConvexWindow
      firstIndex secondIndex targetLower targetUpper
        firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper) = 0 ↔
    adaptiveMixedSharedTargetPhysicalConvexWindow
      firstIndex secondIndex targetLower targetUpper
        firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper = ∅ := by
  constructor
  · intro zero
    apply Set.not_nonempty_iff_eq_empty.mp
    intro nonempty
    have positive := adaptiveMixedSharedTargetPhysicalConvexWindow_volume_pos
      firstIndex secondIndex targetLower targetUpper
        firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper nonempty
    rw [zero] at positive
    exact (lt_irrefl 0) positive
  · intro empty
    rw [empty, measure_empty]

/-- The exact normalized real original-pattern physical strip, retaining its
SIGNED center and the genuine fundamental representative. -/
def adaptiveMixedSignedOriginalPhysicalDomain
    (support : Finset ℕ) (base : ℕ) : Set (ℝ × ℝ) :=
  {point |
    1 < point.1 ∧ point.1 < 2 ∧
      0 < (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 ∧
      (base : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2 < point.1}

/-- The exact normalized real shared-label physical domain, with ONE label
and TWO independently signed centers in their two actual fundamental strips. -/
def adaptiveMixedSignedSharedLabelPhysicalDomain
    (support : Finset ℕ) (firstBase secondBase : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {point |
    1 < point.1 ∧ point.1 < 2 ∧
      0 < (firstBase : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2.1 ∧
      (firstBase : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2.1 < point.1 ∧
      0 < (secondBase : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2.2 ∧
      (secondBase : ℝ) * point.1 +
        (adaptiveMixedTypeModulus support : ℝ) * point.2.2 < point.1}

/-- A finite SIGNED search window large enough for fundamental-strip centers
with label in `(N,2N]`.  It is not a positive natural-center box. -/
noncomputable def adaptiveMixedSignedSearchCenterWindow
    (base N : ℕ) : Finset ℤ :=
  Finset.Icc (-(base : ℤ) * (2 * (N : ℤ))) (2 * (N : ℤ))

/-- Actual signed original prime-pattern realizations in ANY fixed normalized
convex subwindow.  Every center is a genuine fundamental-strip prime edge. -/
noncomputable def adaptiveMixedSignedOriginalPrimeRealizations
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) : Finset (ℕ × ℤ) := by
  classical
  let centers := adaptiveMixedSignedSearchCenterWindow outcome.1 N
  exact ((Finset.Ioc N (2 * N)).product centers).filter fun pair =>
    pair.2 ∈ weightedPrimePatternEdges
      support scale outcome centers pair.1 ∧
      (((pair.1 : ℝ) / (N : ℝ)),
        ((pair.2 : ℝ) / (N : ℝ))) ∈ domain

/-- Actual signed shared-label realizations in ANY fixed normalized convex
subwindow.  The genuine common label and both independent signed prime edges
are required simultaneously. -/
noncomputable def adaptiveMixedSignedSharedLabelPrimeRealizations
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    Finset (ℕ × ℤ × ℤ) := by
  classical
  let first_centers := adaptiveMixedSignedSearchCenterWindow first.1 N
  let second_centers := adaptiveMixedSignedSearchCenterWindow second.1 N
  exact
    ((Finset.Ioc N (2 * N)).product
      (first_centers.product second_centers)).filter fun triple =>
        triple.2.1 ∈ weightedPrimePatternEdges
          support scale first first_centers triple.1 ∧
        triple.2.2 ∈ weightedPrimePatternEdges
          support scale second second_centers triple.1 ∧
        (((triple.1 : ℝ) / (N : ℝ)),
          ((triple.2.1 : ℝ) / (N : ℝ)),
          ((triple.2.2 : ℝ) / (N : ℝ))) ∈ domain

/-- Actual signed SAME-TYPE shared-target realizations in ANY fixed physical
convex subwindow.  The integer labels are genuinely distinct globally, both
signed branches are genuine prime edges, and their actual physical target is
equal; local residue-label equality remains unrestricted. -/
noncomputable def adaptiveMixedSignedSharedTargetPrimeRealizations
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (firstIndex secondIndex : ℕ)
    (domain : Set (ℝ × ℝ × ℝ)) (N : ℕ) :
    Finset ((ℕ × ℤ) × (ℕ × ℤ)) := by
  classical
  let first_centers := adaptiveMixedSignedSearchCenterWindow first.1 N
  let second_centers := adaptiveMixedSignedSearchCenterWindow second.1 N
  let first_candidates :=
    (Finset.Ioc N (2 * N)).product first_centers
  let second_candidates :=
    (Finset.Ioc N (2 * N)).product second_centers
  exact (first_candidates.product second_candidates).filter fun pair =>
    let first_target : ℤ :=
      (firstIndex : ℤ) * (pair.1.1 : ℤ) +
        weightedPrimePatternSignedResidue
          support first.1 pair.1.1 pair.1.2
    let second_target : ℤ :=
      (secondIndex : ℤ) * (pair.2.1 : ℤ) +
        weightedPrimePatternSignedResidue
          support second.1 pair.2.1 pair.2.2
    pair.1.2 ∈ weightedPrimePatternEdges
      support scale first first_centers pair.1.1 ∧
    pair.2.2 ∈ weightedPrimePatternEdges
      support scale second second_centers pair.2.1 ∧
    pair.1.1 ≠ pair.2.1 ∧
    first_target = second_target ∧
      (((first_target : ℝ) / (N : ℝ)),
        ((pair.1.1 : ℝ) / (N : ℝ)),
        ((pair.2.1 : ℝ) / (N : ℝ))) ∈ domain

/-- ONE fixed signed original pattern, at EVERY actual rank including zero
and one, has finite Cauchy--Schwarz complexity, all-prime local admissibility,
and an evaluation-support-uniform strictly positive singular floor. -/
theorem adaptiveMixedSignedOriginal_structural_hypotheses
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    AdaptiveMixedActualHasCSComplexityAtMost support scale outcome
      ((adaptiveMixedOutcomeActiveIndices
        support scale outcome).card - 1) ∧
    (∀ (ell : ℕ) (_prime : ell.Prime),
      ∃ label center : ZMod ell, label ≠ 0 ∧
        ∀ index ∈ adaptiveMixedOutcomeActiveIndices
            support scale outcome,
          adaptiveMixedActualAffineForm
            support outcome.1 index ell label center ≠ 0) ∧
    (∃ constant : ℝ, 0 < constant ∧
      ∀ evaluation : Finset ℕ,
        (∀ ell ∈ evaluation, ell.Prime) →
          constant ≤ ∏ ell ∈ evaluation,
            adaptiveMixedActualScalarLocalFactor
              support scale ell outcome) := by
  refine ⟨adaptiveMixedActualForms_csComplexity_le_rank_sub_one
    support scale outcome primes, ?_,
    adaptiveMixedActualNormalizedLocalFactor_uniform_positive_all_ranks
      support scale outcome primes⟩
  intro ell prime
  exact @adaptiveMixedOutcome_all_prime_locally_admissible
    support scale outcome primes ell ⟨prime⟩

/-- COMPLETE fixed signed shared-label structural package: deduplicated
genuine three-coordinate Cauchy--Schwarz complexity, all-prime actual local
selectors, and the two individual collision-aware singular floors. -/
theorem adaptiveMixedSignedSharedLabel_structural_hypotheses
    (support : Finset ℕ) (scale : ℕ) (first second : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime) :
    AdaptiveMixedThreeCoordinateHasCSComplexityAtMost
      (adaptiveMixedSharedLabelFormIndices support scale first second)
      (adaptiveMixedSharedLabelFormVector support first.1 second.1)
      ((adaptiveMixedOutcomeActiveIndices support scale first).card +
        (adaptiveMixedOutcomeActiveIndices support scale second).card - 1) ∧
    (∀ (ell : ℕ) (prime : ell.Prime),
      (@adaptiveMixedSharedLabelLocalSelectors
        support scale ell first second ⟨prime⟩).Nonempty) ∧
    (∃ constant : ℝ, 0 < constant ∧
      ∀ evaluation : Finset ℕ,
        (∀ ell ∈ evaluation, ell.Prime) →
          constant ≤
            (∏ ell ∈ evaluation,
              adaptiveMixedActualScalarLocalFactor
                support scale ell first) *
            (∏ ell ∈ evaluation,
              adaptiveMixedActualScalarLocalFactor
                support scale ell second)) := by
  refine ⟨adaptiveMixedSharedLabelForms_csComplexity_le_combined_rank_sub_one
    support scale first second primes, ?_, ?_⟩
  · intro ell prime
    exact @adaptiveMixedSharedLabelLocalSelectors_nonempty
      support scale ell first second ⟨prime⟩ primes
  · obtain ⟨constant, positive, lower⟩ :=
      adaptiveMixedActualSharedTarget_singular_product_uniform_positive
        support scale first second primes
    refine ⟨constant, positive, ?_⟩
    intro evaluation evaluation_primes
    rw [← adaptiveMixedActualSharedTarget_finite_singular_product_eq_product
      support scale first second evaluation primes evaluation_primes]
    exact lower evaluation evaluation_primes

/-- COMPLETE fixed signed same-type shared-target structural package at EVERY
actual rank: true three-coordinate deduplicated complexity, every-prime local
fiber admissibility, and genuine uniform strictly positive paired singular
products. -/
theorem adaptiveMixedSignedSharedTarget_structural_hypotheses
    {support : Finset ℕ} {scale firstIndex secondIndex : ℕ}
    {first second : ℕ × ℕ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_active :
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first)
    (second_active :
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second)
    (same_type :
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex)
    (multiplier correction : ℤ)
    (compatible :
      (adaptiveMixedActualLabelCoefficient
        support second.1 secondIndex : ℤ) * multiplier =
        (adaptiveMixedActualLabelCoefficient
          support first.1 firstIndex : ℤ) +
          (adaptiveMixedActualCenterCoefficient
            support first.1 firstIndex : ℤ) * correction) :
    AdaptiveMixedThreeCoordinateHasCSComplexityAtMost
      (adaptiveMixedSharedTargetFormIndices
        support scale first second secondIndex)
      (adaptiveMixedSharedTargetFormVector support first.1 second.1
        firstIndex secondIndex multiplier correction)
      ((adaptiveMixedOutcomeActiveIndices support scale first).card +
        (adaptiveMixedOutcomeActiveIndices support scale second).card - 1) ∧
    (∀ (ell : ℕ) (prime : ell.Prime),
      (@adaptiveMixedSharedTargetLocalSelectors
        support scale ell first second firstIndex secondIndex
          multiplier correction ⟨prime⟩).Nonempty) ∧
    (∃ constant : ℝ, 0 < constant ∧
      ∀ evaluation : Finset ℕ,
        (∀ ell ∈ evaluation, ell.Prime) →
          constant ≤ ∏ ell ∈ evaluation,
            adaptiveMixedActualSharedTargetScalarLocalFactor
              support scale first second ell) := by
  refine
    ⟨adaptiveMixedSharedTargetForms_csComplexity_le_combined_rank_sub_one
      primes first_active second_active same_type multiplier correction,
      ?_, adaptiveMixedActualSharedTarget_singular_product_uniform_positive
        support scale first second primes⟩
  intro ell prime
  exact @adaptiveMixedSharedTargetLocalSelectors_nonempty
    support scale firstIndex secondIndex ell first second ⟨prime⟩
      primes first_active second_active same_type
      multiplier correction compatible

/-- Exact fixed-pattern singular partial product, retaining actual types and
all collision-aware local roots at every genuine evaluation prime. -/
noncomputable def adaptiveMixedSignedSingularPartialProduct
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (cutoff : ℕ) : ℝ :=
  ∏ ell ∈ Nat.primesLE cutoff,
    adaptiveMixedActualScalarLocalFactor support scale ell outcome

/-- EXPLICIT published analytic input, never an axiom: fixed-system
Green--Tao--Ziegler asymptotics on EVERY genuine positive-volume signed convex
subwindow.  Its three separate fields concern ORIGINAL, SHARED-LABEL, and
SAME-TYPE SHARED-TARGET actual prime counts; they assert no target covariance,
rounding success, conductor uniformity, or Erdős-problem conclusion.

All ranks are allowed.  The original exponent is `r+1`; the shared-label and
shared-target exponents are `r+r'+1`.  The true physical shared-target
Jacobian is `s/W²`; the two integer labels are distinct globally but need not
be distinct modulo any local prime. -/
structure HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics : Prop where
  original :
    ∀ (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
      (domain : Set (ℝ × ℝ)),
      (∀ prime ∈ support, prime.Prime) →
      Convex ℝ domain → IsOpen domain → domain.Nonempty →
      domain ⊆ adaptiveMixedSignedOriginalPhysicalDomain
        support outcome.1 →
      ∃ singular : ℝ,
        Tendsto
          (adaptiveMixedSignedSingularPartialProduct support scale outcome)
          atTop (nhds singular) ∧
        Tendsto
          (fun N : ℕ =>
            ((adaptiveMixedSignedOriginalPrimeRealizations
              support scale outcome domain N).card : ℝ) *
                Real.log (N : ℝ) ^
                  ((adaptiveMixedOutcomeActiveIndices
                    support scale outcome).card + 1) /
                  (N : ℝ) ^ 2)
          atTop (nhds ((volume domain).toReal * singular))
  shared_label :
    ∀ (support : Finset ℕ) (scale : ℕ)
      (first second : ℕ × ℕ) (domain : Set (ℝ × ℝ × ℝ)),
      (∀ prime ∈ support, prime.Prime) →
      Convex ℝ domain → IsOpen domain → domain.Nonempty →
      domain ⊆ adaptiveMixedSignedSharedLabelPhysicalDomain
        support first.1 second.1 →
      ∃ firstSingular secondSingular : ℝ,
        Tendsto
          (adaptiveMixedSignedSingularPartialProduct support scale first)
          atTop (nhds firstSingular) ∧
        Tendsto
          (adaptiveMixedSignedSingularPartialProduct support scale second)
          atTop (nhds secondSingular) ∧
        Tendsto
          (fun N : ℕ =>
            ((adaptiveMixedSignedSharedLabelPrimeRealizations
              support scale first second domain N).card : ℝ) *
                Real.log (N : ℝ) ^
                  ((adaptiveMixedOutcomeActiveIndices
                    support scale first).card +
                   (adaptiveMixedOutcomeActiveIndices
                    support scale second).card + 1) /
                  (N : ℝ) ^ 3)
          atTop (nhds
            ((volume domain).toReal * firstSingular * secondSingular))
  shared_target :
    ∀ (support : Finset ℕ) (scale firstIndex secondIndex : ℕ)
      (first second : ℕ × ℕ)
      (targetLower targetUpper firstLabelLower firstLabelUpper
        secondLabelLower secondLabelUpper : ℝ)
      (domain : Set (ℝ × ℝ × ℝ)),
      (∀ prime ∈ support, prime.Prime) →
      firstIndex ∈ adaptiveMixedOutcomeActiveIndices support scale first →
      secondIndex ∈ adaptiveMixedOutcomeActiveIndices support scale second →
      adaptiveMixedActualIndexType support first.1 firstIndex =
        adaptiveMixedActualIndexType support second.1 secondIndex →
      Convex ℝ domain → IsOpen domain → domain.Nonempty →
      domain ⊆ adaptiveMixedSharedTargetPhysicalConvexWindow
        firstIndex secondIndex targetLower targetUpper
          firstLabelLower firstLabelUpper
          secondLabelLower secondLabelUpper →
      (∀ point ∈ domain,
        (1 : ℝ) < point.2.1 ∧ point.2.1 < 2 ∧
          (1 : ℝ) < point.2.2 ∧ point.2.2 < 2) →
      ∃ firstSingular secondSingular : ℝ,
        Tendsto
          (adaptiveMixedSignedSingularPartialProduct support scale first)
          atTop (nhds firstSingular) ∧
        Tendsto
          (adaptiveMixedSignedSingularPartialProduct support scale second)
          atTop (nhds secondSingular) ∧
        Tendsto
          (fun N : ℕ =>
            ((adaptiveMixedSignedSharedTargetPrimeRealizations
              support scale first second firstIndex secondIndex domain N).card : ℝ) *
                Real.log (N : ℝ) ^
                  ((adaptiveMixedOutcomeActiveIndices
                    support scale first).card +
                   (adaptiveMixedOutcomeActiveIndices
                    support scale second).card + 1) /
                  (N : ℝ) ^ 3)
          atTop (nhds
            ((volume domain).toReal *
              (adaptiveMixedActualIndexType
                support first.1 firstIndex : ℝ) /
              (adaptiveMixedTypeModulus support : ℝ) ^ 2 *
              firstSingular * secondSingular))

end Erdos1139

