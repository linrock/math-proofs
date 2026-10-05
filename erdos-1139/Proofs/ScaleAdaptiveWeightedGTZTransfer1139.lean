module

public import ScaleAdaptiveGTZDegreeRegularity1139
public import ScaleAdaptiveGTZSharedTargetMoments1139

@[expose] public section


/-!
# Exact transfer from raw signed prime incidences to true inverse-degree masses

The adaptive construction chooses an actual signed center with edge mass
`mu(p) / d(p)`, where `d(p)` is its integer prime-pattern degree.  Raw original
and shared-target Green--Tao counts weight every center by one and therefore do
NOT by themselves give the required covering probabilities.

For the genuine moving physical target `h = j*p + (b*p + W*C)`, this file
proves that each nonempty prime-label fiber contributes EXACTLY its pattern
mass to the aggregate target first moment.  It also proves the sharp aggregate
target total-variation bound for an arbitrary positive or nonzero
LABEL-DEPENDENT model degree `D(p)`: the entire transfer cost is

    sum_p mu(p) * |d(p) / D(p) - 1|.

Thus the outstanding analytic input is the actual label-dependent relative
degree error; it is neither assumed nor hidden as a covariance hypothesis.
Dyadic constant-degree models and the final scale-uniform smallness of that
error are deliberately not asserted.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 600000

/-- Only genuine prime labels with at least one actual signed prime-pattern
center can be used in an inverse-degree covering distribution. -/
noncomputable def scaleAdaptiveSignedNonemptyDegreePrimeLabels
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) : Finset ℕ :=
  (scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
    scaleAdaptiveSignedDegree support scale outcome domain N label ≠ 0

/-- The true finite signed-center fiber above ONE actual prime label and ONE
genuine distinguished physical target. -/
noncomputable def scaleAdaptiveSignedIndexedLabelTargetFiber
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N label target : ℕ) : Finset ℤ :=
  (scaleAdaptiveSignedDegreeEdges
    support scale outcome domain N label).filter fun center =>
      scaleAdaptiveGTZIndexedPhysicalTarget
        support outcome.1 index label center = target

/-- Every signed edge above a genuine dyadic label maps into its ACTUAL moving
physical target interval, even before any averaging or prime asymptotic. -/
theorem scaleAdaptiveSignedIndexedLabelTarget_mem_window
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N label : ℕ)
    (label_selected : label ∈ scaleAdaptiveSignedDegreePrimeLabels N)
    (center : ℤ)
    (center_selected : center ∈
      scaleAdaptiveSignedDegreeEdges
        support scale outcome domain N label) :
    scaleAdaptiveGTZIndexedPhysicalTarget
      support outcome.1 index label center ∈
        scaleAdaptiveGTZIndexedTargetWindow index N := by
  have original : (label, center) ∈
      adaptiveMixedSignedOriginalPrimeRealizations
        support scale outcome domain N := by
    apply
      (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
        support scale outcome domain N (label, center)).mpr
    exact ⟨(Finset.mem_filter.mp label_selected).1, center_selected⟩
  exact scaleAdaptiveGTZIndexedPhysicalTarget_mem_window
    support scale outcome domain index N (label, center) original

/-- EXACT target partition at each actual prime label: every signed prime edge
has exactly one physical target in the correct moving interval. -/
theorem scaleAdaptiveSignedIndexedLabelTarget_fibers_sum_card
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N label : ℕ)
    (label_selected : label ∈ scaleAdaptiveSignedDegreePrimeLabels N) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
      (scaleAdaptiveSignedIndexedLabelTargetFiber
        support scale outcome domain index N label target).card) =
      scaleAdaptiveSignedDegree
        support scale outcome domain N label := by
  let edges := scaleAdaptiveSignedDegreeEdges
    support scale outcome domain N label
  have mapped :
      (↑edges : Set ℤ).MapsTo
        (fun center => scaleAdaptiveGTZIndexedPhysicalTarget
          support outcome.1 index label center)
        (scaleAdaptiveGTZIndexedTargetWindow index N) := by
    intro center selected
    exact scaleAdaptiveSignedIndexedLabelTarget_mem_window
      support scale outcome domain index N label label_selected center selected
  have partition := Finset.card_eq_sum_card_fiberwise mapped
  change _ = edges.card
  rw [partition]
  apply Finset.sum_congr rfl
  intro target _selected
  rfl

/-- The actual targetwise mass from the genuine finite inverse-degree
distribution, with zero-degree labels removed instead of divided by zero. -/
noncomputable def scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (mass : ℕ → ℝ) (target : ℕ) : ℝ :=
  ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
      support scale outcome domain N,
    mass label *
      ((scaleAdaptiveSignedIndexedLabelTargetFiber
        support scale outcome domain index N label target).card : ℝ) /
      (scaleAdaptiveSignedDegree
        support scale outcome domain N label : ℝ)

/-- The corresponding targetwise model with the TRUE label-dependent
reference profile `D(p)`; no dyadic constant profile is substituted. -/
noncomputable def scaleAdaptiveSignedModelDegreeIndexedTargetLoad
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (mass expected : ℕ → ℝ) (target : ℕ) : ℝ :=
  ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
      support scale outcome domain N,
    mass label *
      ((scaleAdaptiveSignedIndexedLabelTargetFiber
        support scale outcome domain index N label target).card : ℝ) /
      expected label

/-- EXACT first moment of the genuine inverse-degree target distribution.
Every nonempty actual prime label contributes its entire pattern mass, with no
degree-regularity, first-moment, or Green--Tao hypothesis. -/
theorem scaleAdaptiveSignedInverseDegreeIndexedTarget_firstMoment_eq
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (mass : ℕ → ℝ) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
      scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
        support scale outcome domain index N mass target) =
      ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N, mass label := by
  unfold scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro label selected
  have decoded := Finset.mem_filter.mp selected
  have partition := scaleAdaptiveSignedIndexedLabelTarget_fibers_sum_card
    support scale outcome domain index N label decoded.1
  have real_partition :
      (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
        ((scaleAdaptiveSignedIndexedLabelTargetFiber
          support scale outcome domain index N label target).card : ℝ)) =
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ) := by
    exact_mod_cast partition
  have degree_nonzero :
      (scaleAdaptiveSignedDegree
        support scale outcome domain N label : ℝ) ≠ 0 := by
    exact_mod_cast decoded.2
  calc
    _ = mass label *
          ((∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
            ((scaleAdaptiveSignedIndexedLabelTargetFiber
              support scale outcome domain index N label target).card : ℝ)) /
            (scaleAdaptiveSignedDegree
              support scale outcome domain N label : ℝ)) := by
      simp_rw [mul_div_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_div]
    _ = mass label := by
      rw [real_partition, div_self degree_nonzero, mul_one]

/-- EXACT mass normalization of the label-dependent model.  Its deviation
from the true covering mass is precisely the actual degree ratio `d(p)/D(p)`. -/
theorem scaleAdaptiveSignedModelDegreeIndexedTarget_firstMoment_eq
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (mass expected : ℕ → ℝ) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
      scaleAdaptiveSignedModelDegreeIndexedTargetLoad
        support scale outcome domain index N mass expected target) =
      ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N,
          mass label *
            ((scaleAdaptiveSignedDegree
              support scale outcome domain N label : ℝ) / expected label) := by
  unfold scaleAdaptiveSignedModelDegreeIndexedTargetLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro label selected
  have decoded := Finset.mem_filter.mp selected
  have partition := scaleAdaptiveSignedIndexedLabelTarget_fibers_sum_card
    support scale outcome domain index N label decoded.1
  have real_partition :
      (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
        ((scaleAdaptiveSignedIndexedLabelTargetFiber
          support scale outcome domain index N label target).card : ℝ)) =
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ) := by
    exact_mod_cast partition
  calc
    _ = mass label *
          ((∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
            ((scaleAdaptiveSignedIndexedLabelTargetFiber
              support scale outcome domain index N label target).card : ℝ)) /
            expected label) := by
      simp_rw [mul_div_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_div]
    _ = _ := by rw [real_partition]

/-- At ONE genuine prime label, the total variation across ALL physical
targets is EXACTLY its pattern mass times its label-dependent relative degree
error.  The moving target window does not introduce an ambient-size factor. -/
theorem scaleAdaptiveSignedIndexedLabelTarget_totalVariation_eq
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N label : ℕ)
    (patternMass expected : ℝ)
    (label_selected : label ∈ scaleAdaptiveSignedDegreePrimeLabels N)
    (degree_nonzero :
      scaleAdaptiveSignedDegree
        support scale outcome domain N label ≠ 0)
    (mass_nonnegative : 0 ≤ patternMass)
    (expected_nonzero : expected ≠ 0) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
      |patternMass *
          ((scaleAdaptiveSignedIndexedLabelTargetFiber
            support scale outcome domain index N label target).card : ℝ) /
          (scaleAdaptiveSignedDegree
            support scale outcome domain N label : ℝ) -
        patternMass *
          ((scaleAdaptiveSignedIndexedLabelTargetFiber
            support scale outcome domain index N label target).card : ℝ) /
          expected|) =
      patternMass *
        |(scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ) / expected - 1| := by
  let edges := scaleAdaptiveSignedDegreeEdges
    support scale outcome domain N label
  have nonempty : edges.Nonempty :=
    Finset.card_ne_zero.mp degree_nonzero
  have partition := scaleAdaptiveSignedIndexedLabelTarget_fibers_sum_card
    support scale outcome domain index N label label_selected
  have real_partition :
      (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
        ((scaleAdaptiveSignedIndexedLabelTargetFiber
          support scale outcome domain index N label target).card : ℝ)) =
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ) := by
    exact_mod_cast partition
  calc
    _ = ∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
          ((scaleAdaptiveSignedIndexedLabelTargetFiber
            support scale outcome domain index N label target).card : ℝ) *
            |patternMass /
              (scaleAdaptiveSignedDegree
                support scale outcome domain N label : ℝ) -
              patternMass / expected| := by
      apply Finset.sum_congr rfl
      intro target _
      calc
        _ = |((scaleAdaptiveSignedIndexedLabelTargetFiber
              support scale outcome domain index N label target).card : ℝ) *
                (patternMass /
                  (scaleAdaptiveSignedDegree
                    support scale outcome domain N label : ℝ) -
                  patternMass / expected)| := by
          congr 1
          ring
        _ = _ := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ = (scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ) *
            |patternMass /
              (scaleAdaptiveSignedDegree
                support scale outcome domain N label : ℝ) -
              patternMass / expected| := by
      rw [← Finset.sum_mul, real_partition]
    _ = ∑ _center ∈ edges,
          |weightedPrimePatternActualEdgeWeight patternMass edges -
            patternMass / expected| := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    _ = _ := weightedPrimePattern_edge_total_variation_eq
      patternMass expected edges mass_nonnegative nonempty expected_nonzero

/-- Sharp aggregate targetwise transfer for ACTUAL inverse-degree masses and
an arbitrary label-dependent reference profile.  The ONLY residual is the
true weighted relative degree error.  No concentration is assumed. -/
theorem scaleAdaptiveSignedInverseDegreeIndexedTarget_totalVariation_le
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (index N : ℕ)
    (mass expected : ℕ → ℝ)
    (mass_nonnegative : ∀ label ∈
      scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N, 0 ≤ mass label)
    (expected_nonzero : ∀ label ∈
      scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N, expected label ≠ 0) :
    (∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
      |scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
          support scale outcome domain index N mass target -
        scaleAdaptiveSignedModelDegreeIndexedTargetLoad
          support scale outcome domain index N mass expected target|) ≤
      ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
        support scale outcome domain N,
          mass label *
            |(scaleAdaptiveSignedDegree
              support scale outcome domain N label : ℝ) /
                expected label - 1| := by
  unfold scaleAdaptiveSignedInverseDegreeIndexedTargetLoad
    scaleAdaptiveSignedModelDegreeIndexedTargetLoad
  calc
    _ ≤ ∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
          ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
            support scale outcome domain N,
            |mass label *
                ((scaleAdaptiveSignedIndexedLabelTargetFiber
                  support scale outcome domain index N label target).card : ℝ) /
                (scaleAdaptiveSignedDegree
                  support scale outcome domain N label : ℝ) -
              mass label *
                ((scaleAdaptiveSignedIndexedLabelTargetFiber
                  support scale outcome domain index N label target).card : ℝ) /
                expected label| := by
      apply Finset.sum_le_sum
      intro target _
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ label ∈ scaleAdaptiveSignedNonemptyDegreePrimeLabels
          support scale outcome domain N,
          ∑ target ∈ scaleAdaptiveGTZIndexedTargetWindow index N,
            |mass label *
                ((scaleAdaptiveSignedIndexedLabelTargetFiber
                  support scale outcome domain index N label target).card : ℝ) /
                (scaleAdaptiveSignedDegree
                  support scale outcome domain N label : ℝ) -
              mass label *
                ((scaleAdaptiveSignedIndexedLabelTargetFiber
                  support scale outcome domain index N label target).card : ℝ) /
                expected label| := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro label selected
      obtain ⟨label_selected, nonzero⟩ := Finset.mem_filter.mp selected
      exact scaleAdaptiveSignedIndexedLabelTarget_totalVariation_eq
        support scale outcome domain index N label
          (mass label) (expected label) label_selected nonzero
            (mass_nonnegative label selected)
            (expected_nonzero label selected)


end Erdos1139
