module

public import SharedTargetSingularFactorization1139
public import ActualPrimeCorrelationBridge1139
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section


/-!
# Honest finite prime-pattern moment and normalization bookkeeping

The actual mixed-pattern construction samples a genuine prime-pattern center
with weight `mu / d(p)`, where `d(p)` is its INTEGER prime-edge degree.  Its
Green--Tao model uses `mu / D(p)` with the true pattern-specific singular
series, rank, prime label, square-core modulus, and logarithm.

This module proves the finite normalization, exact total-variation error,
exceptional-label deletion, first/shared-target second-moment centering, and
same-cell-to-many-cell aggregation required to pass between those two
distributions. It also identifies an essential shot-noise term: the legacy
first-energy distinct-label bound is equivalent to centered variance PLUS
`F-D`, while the corrected exact-diagonal bound is equivalent to centered
variance alone. No prime-pattern asymptotic is assumed or proved.

All active pattern indices remain physical indices `1,...,T`, and every edge
requires its actual label and every retained mixed affine target form to be
prime.  The shared-target singular/covolume cancellation imported here applies
only to the SAME square-core support and SAME semiprime type.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- The genuine SIGNED integer mixed affine prime form, with the actual
square-core support, physical base, physical index, prime label, and signed
center. Valid centers in the true fundamental residue strip are usually
NEGATIVE when the base is positive; natural centers are not sufficient. -/
def weightedPrimePatternIntegerForm
    (support : Finset ℕ) (base index label : ℕ) (center : ℤ) : ℤ :=
  (((base + index) /
    adaptiveMixedActualIndexType support base index : ℕ) : ℤ) *
      (label : ℤ) +
  ((adaptiveMixedTypeModulus support /
    adaptiveMixedActualIndexType support base index : ℕ) : ℤ) * center

/-- The actual signed representative b*p+W*C. Its fundamental-strip
condition is indispensable and cannot be represented by restricting C to
the natural numbers. -/
def weightedPrimePatternSignedResidue
    (support : Finset ℕ) (base label : ℕ) (center : ℤ) : ℤ :=
  (base : ℤ) * (label : ℤ) +
    (adaptiveMixedTypeModulus support : ℤ) * center

/-- Every genuinely valid fundamental-strip center is STRICTLY NEGATIVE
whenever the pattern base is positive. Thus replacing actual signed centers
by natural-number centers would discard every such prime-pattern edge. -/
theorem weightedPrimePattern_valid_center_negative_of_positive_base
    (support : Finset ℕ) (base label : ℕ) (center : ℤ)
    (base_positive : 0 < base)
    (bounded : weightedPrimePatternSignedResidue
      support base label center < (label : ℤ)) :
    center < 0 := by
  by_contra not_negative
  have center_nonnegative : 0 ≤ center := le_of_not_gt not_negative
  have base_factor_nonnegative : 0 ≤ (base : ℤ) - 1 := by
    have base_at_least_one : (1 : ℤ) ≤ (base : ℤ) := by
      exact_mod_cast base_positive
    linarith
  have label_nonnegative : 0 ≤ (label : ℤ) := Int.natCast_nonneg _
  have modulus_nonnegative :
      0 ≤ (adaptiveMixedTypeModulus support : ℤ) :=
    Int.natCast_nonneg _
  unfold weightedPrimePatternSignedResidue at bounded
  nlinarith [mul_nonneg base_factor_nonnegative label_nonnegative,
    mul_nonneg modulus_nonnegative center_nonnegative]

/-- Genuine finite prime-pattern edges.  The label itself is prime, the
center lies in its actual physical window, and EVERY retained index in the
actual outcome supplies a prime affine form.  No zero index is inserted. -/
def weightedPrimePatternEdges
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (centerWindow : Finset ℤ) (label : ℕ) : Finset ℤ :=
  centerWindow.filter fun center =>
    label.Prime ∧
      0 ≤ weightedPrimePatternSignedResidue
        support outcome.1 label center ∧
      weightedPrimePatternSignedResidue
        support outcome.1 label center < (label : ℤ) ∧
      ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
        0 < weightedPrimePatternIntegerForm support outcome.1 index
          label center ∧
        (weightedPrimePatternIntegerForm support outcome.1 index
          label center).toNat.Prime

/-- Every selected edge has a genuine prime label and prime values at all
retained actual mixed-pattern indices. -/
theorem weightedPrimePatternEdges_prime_certificate
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (centerWindow : Finset ℤ) (label : ℕ) (center : ℤ)
    (selected : center ∈
      weightedPrimePatternEdges support scale outcome centerWindow label) :
    label.Prime ∧ center ∈ centerWindow ∧
      0 ≤ weightedPrimePatternSignedResidue
        support outcome.1 label center ∧
      weightedPrimePatternSignedResidue
        support outcome.1 label center < (label : ℤ) ∧
      ∀ index ∈ adaptiveMixedOutcomeActiveIndices support scale outcome,
        index ∈ Finset.Icc 1 scale ∧
          0 < weightedPrimePatternIntegerForm support outcome.1 index
            label center ∧
          (weightedPrimePatternIntegerForm support outcome.1 index
            label center).toNat.Prime := by
  obtain ⟨window, label_prime, residue_nonnegative,
    residue_bounded, forms_prime⟩ :=
    Finset.mem_filter.mp selected
  refine ⟨label_prime, window, residue_nonnegative, residue_bounded, ?_⟩
  intro index active
  exact ⟨adaptiveMixedOutcomeActiveIndices_subset_physical
    support scale outcome active, forms_prime index active⟩

/-- The exact finite integer degree of a real prime-pattern label. -/
def weightedPrimePatternDegree {α : Type*} (edges : Finset α) : ℕ :=
  edges.card

/-- The genuine edge mass `mu / d(p)`, distinct from the model's singular
series-dependent `mu / D(p)`. -/
noncomputable def weightedPrimePatternActualEdgeWeight
    {α : Type*} (patternMass : ℝ) (edges : Finset α) : ℝ :=
  patternMass / (weightedPrimePatternDegree edges : ℝ)

/-- Every nonempty genuine pattern contributes EXACTLY its pattern mass to
the fixed-label distribution, independent of its actual integer degree. -/
theorem weightedPrimePattern_actual_edges_total_mass
    {α : Type*}
    (patternMass : ℝ) (edges : Finset α) (nonempty : edges.Nonempty) :
    (∑ _center ∈ edges,
      weightedPrimePatternActualEdgeWeight patternMass edges) = patternMass := by
  unfold weightedPrimePatternActualEdgeWeight weightedPrimePatternDegree
  rw [Finset.sum_const, nsmul_eq_mul]
  have nonzero : (edges.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr nonempty
  field_simp

/-- Summing all genuine nonempty patterns gives an honest probability
distribution at EVERY label whenever their original masses sum to one. -/
theorem weightedPrimePattern_label_mass_eq_one
    {ι α : Type*} (patterns : Finset ι)
    (mass : ι → ℝ) (edges : ι → Finset α)
    (nonempty : ∀ pattern ∈ patterns, (edges pattern).Nonempty)
    (normalized : ∑ pattern ∈ patterns, mass pattern = 1) :
    (∑ pattern ∈ patterns, ∑ _center ∈ edges pattern,
      weightedPrimePatternActualEdgeWeight (mass pattern)
        (edges pattern)) = 1 := by
  calc
    _ = ∑ pattern ∈ patterns, mass pattern := by
      apply Finset.sum_congr rfl
      intro pattern selected
      exact weightedPrimePattern_actual_edges_total_mass
        (mass pattern) (edges pattern) (nonempty pattern selected)
    _ = 1 := normalized

/-- The model assigns total pattern mass `mu*d(p)/D(p)` before correcting
the actual integer degree. -/
theorem weightedPrimePattern_model_edges_total_mass
    {α : Type*}
    (patternMass expectedDegree : ℝ) (edges : Finset α) :
    (∑ _center ∈ edges, patternMass / expectedDegree) =
      patternMass * ((edges.card : ℝ) / expectedDegree) := by
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- EXACT full-edge total variation between the ACTUAL and model
distributions.  The integer degree cancels, leaving precisely the relative
degree error; no lower-bound factor `1/(1-eta)` is needed. -/
theorem weightedPrimePattern_edge_total_variation_eq
    {α : Type*}
    (patternMass expectedDegree : ℝ) (edges : Finset α)
    (mass_nonnegative : 0 ≤ patternMass)
    (nonempty : edges.Nonempty) (expected_nonzero : expectedDegree ≠ 0) :
    (∑ _center ∈ edges,
      |weightedPrimePatternActualEdgeWeight patternMass edges -
        patternMass / expectedDegree|) =
      patternMass * |(edges.card : ℝ) / expectedDegree - 1| := by
  unfold weightedPrimePatternActualEdgeWeight weightedPrimePatternDegree
  rw [Finset.sum_const, nsmul_eq_mul]
  have cardinal_nonzero : (edges.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr nonempty
  have algebra :
      (edges.card : ℝ) *
        (patternMass / (edges.card : ℝ) -
          patternMass / expectedDegree) =
        patternMass * (1 - (edges.card : ℝ) / expectedDegree) := by
    field_simp
  calc
    _ = |(edges.card : ℝ) *
      (patternMass / (edges.card : ℝ) -
        patternMass / expectedDegree)| := by
      have absolute_product :=
        abs_mul (edges.card : ℝ)
          (patternMass / (edges.card : ℝ) -
            patternMass / expectedDegree)
      have cardinal_absolute : |(edges.card : ℝ)| = (edges.card : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg edges.card)
      rw [cardinal_absolute] at absolute_product
      exact absolute_product.symm
    _ = |patternMass * (1 - (edges.card : ℝ) / expectedDegree)| := by
      rw [algebra]
    _ = _ := by
      rw [abs_mul, abs_of_nonneg mass_nonnegative, abs_sub_comm]

/-- A simultaneous relative degree estimate controls the COMPLETE
pattern-mixture edge distribution at a good label.  Pattern multiplicities
and genuine finite prime edges are retained exactly. -/
theorem weightedPrimePattern_good_label_total_variation_le
    {ι α : Type*} (patterns : Finset ι)
    (mass expectedDegree : ι → ℝ) (edges : ι → Finset α)
    (eta : ℝ)
    (mass_nonnegative : ∀ pattern ∈ patterns, 0 ≤ mass pattern)
    (nonempty : ∀ pattern ∈ patterns, (edges pattern).Nonempty)
    (expected_nonzero : ∀ pattern ∈ patterns, expectedDegree pattern ≠ 0)
    (relative_error : ∀ pattern ∈ patterns,
      |((edges pattern).card : ℝ) / expectedDegree pattern - 1| ≤ eta)
    (normalized : ∑ pattern ∈ patterns, mass pattern = 1) :
    (∑ pattern ∈ patterns, ∑ _center ∈ edges pattern,
      |weightedPrimePatternActualEdgeWeight (mass pattern) (edges pattern) -
        mass pattern / expectedDegree pattern|) ≤ eta := by
  calc
    _ = ∑ pattern ∈ patterns,
          mass pattern *
            |((edges pattern).card : ℝ) / expectedDegree pattern - 1| := by
      apply Finset.sum_congr rfl
      intro pattern selected
      exact weightedPrimePattern_edge_total_variation_eq
        (mass pattern) (expectedDegree pattern) (edges pattern)
        (mass_nonnegative pattern selected) (nonempty pattern selected)
        (expected_nonzero pattern selected)
    _ ≤ ∑ pattern ∈ patterns, mass pattern * eta := by
      apply Finset.sum_le_sum
      intro pattern selected
      exact mul_le_mul_of_nonneg_left
        (relative_error pattern selected)
        (mass_nonnegative pattern selected)
    _ = eta := by
      rw [← Finset.sum_mul, normalized, one_mul]

/-- Selecting the genuine edges that hit ONE actual target cannot increase
the full-label total variation. The hit predicate may encode the actual
physical target, residue, group, and type simultaneously. -/
theorem weightedPrimePattern_good_label_target_hit_error_le
    {ι α : Type*} (patterns : Finset ι)
    (mass expectedDegree : ι → ℝ) (edges : ι → Finset α)
    (hits : ι → α → Bool) (eta : ℝ)
    (mass_nonnegative : ∀ pattern ∈ patterns, 0 ≤ mass pattern)
    (nonempty : ∀ pattern ∈ patterns, (edges pattern).Nonempty)
    (expected_nonzero : ∀ pattern ∈ patterns, expectedDegree pattern ≠ 0)
    (relative_error : ∀ pattern ∈ patterns,
      |((edges pattern).card : ℝ) / expectedDegree pattern - 1| ≤ eta)
    (normalized : ∑ pattern ∈ patterns, mass pattern = 1) :
    |(∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
        if hits pattern center then
          weightedPrimePatternActualEdgeWeight
            (mass pattern) (edges pattern) else 0) -
      (∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
        if hits pattern center then
          mass pattern / expectedDegree pattern else 0)| ≤ eta := by
  have total_variation :=
    weightedPrimePattern_good_label_total_variation_le
      patterns mass expectedDegree edges eta mass_nonnegative nonempty
        expected_nonzero relative_error normalized
  calc
    _ = |∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
          ((if hits pattern center then
              weightedPrimePatternActualEdgeWeight
                (mass pattern) (edges pattern) else 0) -
           (if hits pattern center then
              mass pattern / expectedDegree pattern else 0))| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro pattern _
      rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ pattern ∈ patterns,
          |∑ center ∈ edges pattern,
            ((if hits pattern center then
                weightedPrimePatternActualEdgeWeight
                  (mass pattern) (edges pattern) else 0) -
             (if hits pattern center then
                mass pattern / expectedDegree pattern else 0))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
          |(if hits pattern center then
              weightedPrimePatternActualEdgeWeight
                (mass pattern) (edges pattern) else 0) -
           (if hits pattern center then
              mass pattern / expectedDegree pattern else 0)| := by
      apply Finset.sum_le_sum
      intro pattern _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ pattern ∈ patterns, ∑ _center ∈ edges pattern,
          |weightedPrimePatternActualEdgeWeight
            (mass pattern) (edges pattern) -
            mass pattern / expectedDegree pattern| := by
      apply Finset.sum_le_sum
      intro pattern _
      apply Finset.sum_le_sum
      intro center _
      split_ifs <;> simp
    _ ≤ eta := total_variation

/-- Aggregate target-incidence variation uses the TRUE hyperedge rank, not
the number of targets. This prevents multiplying the good-label degree
error by the ambient target count when transferring model prime-pattern
moments to actual mu/d probabilities. -/
theorem weightedPrimePattern_good_label_total_target_error_le
    {ι α : Type*} (patterns : Finset ι) (targets : Finset ℕ)
    (mass expectedDegree : ι → ℝ) (edges : ι → Finset α)
    (hits : ι → α → ℕ → Bool)
    (rank : ℕ) (eta : ℝ)
    (mass_nonnegative : ∀ pattern ∈ patterns, 0 ≤ mass pattern)
    (nonempty : ∀ pattern ∈ patterns, (edges pattern).Nonempty)
    (expected_nonzero : ∀ pattern ∈ patterns, expectedDegree pattern ≠ 0)
    (relative_error : ∀ pattern ∈ patterns,
      |((edges pattern).card : ℝ) / expectedDegree pattern - 1| ≤ eta)
    (normalized : ∑ pattern ∈ patterns, mass pattern = 1)
    (edge_rank : ∀ pattern ∈ patterns, ∀ center ∈ edges pattern,
      (targets.filter fun target =>
        hits pattern center target).card ≤ rank) :
    (∑ target ∈ targets,
      |(∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
          if hits pattern center target then
            weightedPrimePatternActualEdgeWeight
              (mass pattern) (edges pattern) else 0) -
        (∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
          if hits pattern center target then
            mass pattern / expectedDegree pattern else 0)|) ≤
      (rank : ℝ) * eta := by
  have total_variation :=
    weightedPrimePattern_good_label_total_variation_le
      patterns mass expectedDegree edges eta mass_nonnegative nonempty
        expected_nonzero relative_error normalized
  calc
    _ ≤ ∑ target ∈ targets, ∑ pattern ∈ patterns,
          ∑ center ∈ edges pattern,
            if hits pattern center target then
              |weightedPrimePatternActualEdgeWeight
                (mass pattern) (edges pattern) -
                mass pattern / expectedDegree pattern|
            else 0 := by
      apply Finset.sum_le_sum
      intro target _
      calc
        _ = |∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
              ((if hits pattern center target then
                  weightedPrimePatternActualEdgeWeight
                    (mass pattern) (edges pattern) else 0) -
               (if hits pattern center target then
                  mass pattern / expectedDegree pattern else 0))| := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro pattern _
          rw [← Finset.sum_sub_distrib]
        _ ≤ ∑ pattern ∈ patterns,
              |∑ center ∈ edges pattern,
                ((if hits pattern center target then
                    weightedPrimePatternActualEdgeWeight
                      (mass pattern) (edges pattern) else 0) -
                 (if hits pattern center target then
                    mass pattern / expectedDegree pattern else 0))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
              |(if hits pattern center target then
                  weightedPrimePatternActualEdgeWeight
                    (mass pattern) (edges pattern) else 0) -
               (if hits pattern center target then
                  mass pattern / expectedDegree pattern else 0)| := by
          apply Finset.sum_le_sum
          intro pattern _
          exact Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro pattern _
          apply Finset.sum_congr rfl
          intro center _
          split_ifs <;> simp
    _ = ∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
          ∑ target ∈ targets,
            if hits pattern center target then
              |weightedPrimePatternActualEdgeWeight
                (mass pattern) (edges pattern) -
                mass pattern / expectedDegree pattern|
            else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pattern _
      rw [Finset.sum_comm]
    _ ≤ ∑ pattern ∈ patterns, ∑ center ∈ edges pattern,
          (rank : ℝ) *
            |weightedPrimePatternActualEdgeWeight
              (mass pattern) (edges pattern) -
              mass pattern / expectedDegree pattern| := by
      apply Finset.sum_le_sum
      intro pattern pattern_selected
      apply Finset.sum_le_sum
      intro center center_selected
      calc
        _ = ((targets.filter fun target =>
              hits pattern center target).card : ℝ) *
                |weightedPrimePatternActualEdgeWeight
                  (mass pattern) (edges pattern) -
                  mass pattern / expectedDegree pattern| := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact_mod_cast edge_rank pattern pattern_selected
            center center_selected
    _ = (rank : ℝ) *
          ∑ pattern ∈ patterns, ∑ _center ∈ edges pattern,
            |weightedPrimePatternActualEdgeWeight
              (mass pattern) (edges pattern) -
              mass pattern / expectedDegree pattern| := by
      simp_rw [Finset.mul_sum]
    _ ≤ (rank : ℝ) * eta :=
      mul_le_mul_of_nonneg_left total_variation (Nat.cast_nonneg _)

/-- Exact finite Markov deletion after aggregate actual/model incidence
control. Bad vertices are measured in TRUE target cardinality rather than
with an assumed pointwise fixed-target prime-pattern estimate. -/
theorem weightedPrimePattern_bad_targets_card_mul_threshold_le
    (targets : Finset ℕ) (actual model : ℕ → ℝ) (threshold : ℝ) :
    let bad := targets.filter fun target =>
      threshold ≤ |actual target - model target|
    (bad.card : ℝ) * threshold ≤
      ∑ target ∈ targets, |actual target - model target| := by
  dsimp
  calc
    _ = ∑ _target ∈
          targets.filter (fun target =>
            threshold ≤ |actual target - model target|),
            threshold := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ target ∈
          targets.filter (fun target =>
            threshold ≤ |actual target - model target|),
            |actual target - model target| := by
      apply Finset.sum_le_sum
      intro target selected
      exact (Finset.mem_filter.mp selected).2
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro target _ _
        exact abs_nonneg _

/-- On the remaining good targets, model centered second moments transfer
to the genuine actual distribution with the sharp elementary quadratic
error budget. Together with the preceding rank-weighted deletion bound,
this avoids any unproved fixed-target prime-pattern theorem. -/
theorem weightedPrimePattern_actual_centered_moment_le_of_model
    (targets : Finset ℕ) (actual model mean : ℕ → ℝ)
    (threshold : ℝ)
    (good : ∀ target ∈ targets,
      |actual target - model target| ≤ threshold) :
    (∑ target ∈ targets, (actual target - mean target) ^ 2) ≤
      2 * (∑ target ∈ targets, (model target - mean target) ^ 2) +
        2 * (targets.card : ℝ) * threshold ^ 2 := by
  calc
    _ ≤ ∑ target ∈ targets,
          (2 * (model target - mean target) ^ 2 +
            2 * threshold ^ 2) := by
      apply Finset.sum_le_sum
      intro target selected
      have square_bound :
          (actual target - model target) ^ 2 ≤ threshold ^ 2 := by
        have absolute := good target selected
        have threshold_nonnegative : 0 ≤ threshold :=
          (abs_nonneg _).trans absolute
        apply sq_le_sq.mpr
        rwa [abs_of_nonneg threshold_nonnegative]
      nlinarith [sq_nonneg
        ((actual target - model target) -
          (model target - mean target))]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring

/-- A simple globally valid quadratic bound controls exceptional model
degrees without any unjustified uniform degree cap. -/
theorem weightedPrimePattern_degree_ratio_le_quadratic (ratio : ℝ) :
    ratio ≤ 2 + (ratio - 1) ^ 2 := by
  nlinarith [sq_nonneg (ratio - (3 / 2 : ℝ))]

/-- Discarding a small exceptional label set is safe only when its actual
degree ratios are controlled too.  This exact finite bound supplies the
required control from bad-label count AND global degree second moment. -/
theorem weightedPrimePattern_exceptional_degree_mass_le
    (labels exceptional : Finset ℕ) (ratio : ℕ → ℝ)
    (subset : exceptional ⊆ labels) :
    (∑ label ∈ exceptional, ratio label) ≤
      2 * (exceptional.card : ℝ) +
        ∑ label ∈ labels, (ratio label - 1) ^ 2 := by
  calc
    _ ≤ ∑ label ∈ exceptional,
          (2 + (ratio label - 1) ^ 2) := by
      apply Finset.sum_le_sum
      intro label _
      exact weightedPrimePattern_degree_ratio_le_quadratic (ratio label)
    _ = 2 * (exceptional.card : ℝ) +
          ∑ label ∈ exceptional, (ratio label - 1) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      gcongr

/-- Finite Chebyshev for the actual degree-ratio exceptional set, with its
true integer label cardinality and exact squared-error scale. -/
theorem weightedPrimePattern_exceptional_card_mul_threshold_sq_le
    (labels : Finset ℕ) (ratio : ℕ → ℝ) (eta : ℝ) :
    let exceptional := labels.filter fun label => eta ^ 2 ≤ (ratio label - 1) ^ 2
    (exceptional.card : ℝ) * eta ^ 2 ≤
      ∑ label ∈ labels, (ratio label - 1) ^ 2 := by
  dsimp
  calc
    _ = ∑ _label ∈
          labels.filter (fun label => eta ^ 2 ≤ (ratio label - 1) ^ 2),
            eta ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ label ∈
          labels.filter (fun label => eta ^ 2 ≤ (ratio label - 1) ^ 2),
            (ratio label - 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro label selected
      exact (Finset.mem_filter.mp selected).2
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro label _ _
        exact sq_nonneg _

/-- Exact prime-edge model mass discarded with exceptional labels. Merely
counting exceptional labels is insufficient; the true integer degree second
moment is retained explicitly and multiplied by its actual pattern mass. -/
theorem weightedPrimePattern_exceptional_model_edge_mass_le
    {α : Type*}
    (labels exceptional : Finset ℕ)
    (edges : ℕ → Finset α)
    (expectedDegree : ℕ → ℝ) (patternMass : ℝ)
    (subset : exceptional ⊆ labels)
    (mass_nonnegative : 0 ≤ patternMass) :
    (∑ label ∈ exceptional, ∑ _center ∈ edges label,
      patternMass / expectedDegree label) ≤
      patternMass *
        (2 * (exceptional.card : ℝ) +
          ∑ label ∈ labels,
            (((edges label).card : ℝ) /
              expectedDegree label - 1) ^ 2) := by
  calc
    _ = ∑ label ∈ exceptional,
          patternMass *
            (((edges label).card : ℝ) / expectedDegree label) := by
      apply Finset.sum_congr rfl
      intro label _
      exact weightedPrimePattern_model_edges_total_mass
        patternMass (expectedDegree label) (edges label)
    _ = patternMass *
          ∑ label ∈ exceptional,
            (((edges label).card : ℝ) / expectedDegree label) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ mass_nonnegative
      exact weightedPrimePattern_exceptional_degree_mass_le
        labels exceptional
        (fun label => ((edges label).card : ℝ) / expectedDegree label)
        subset

end Erdos1139
