module

public import ScaleAdaptiveGlobalMomentConstruction1139
public import AdaptiveSharedTargetActualFactorization1139

@[expose] public section


/-!
# Genuine signed Green--Tao prime-label degree regularity

The proposed adaptive covering needs degree regularity for the ACTUAL signed
prime-pattern center fibers.  This module relates those fibers directly to the
published-input ORIGINAL and SHARED-LABEL realization counts; no natural-center
proxy, postulated degree concentration, or target-correlation axiom is used.

Every prime label remains in the genuine interval `(N,2N]`, every center is
signed, and every retained mixed affine form is prime.  The shared-label domain
uses the exact fiber square of the original two-dimensional physical domain.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

set_option maxHeartbeats 400000

/-- The exact prime labels occurring in a signed Green--Tao dyadic cell. -/
def scaleAdaptiveSignedDegreePrimeLabels (N : ℕ) : Finset ℕ :=
  (Finset.Ioc N (2 * N)).filter Nat.Prime

/-- The ACTUAL signed prime-edge fiber above one genuine label, retaining the
same normalized convex physical subdomain as the original Green--Tao count. -/
noncomputable def scaleAdaptiveSignedDegreeEdges
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N label : ℕ) : Finset ℤ := by
  classical
  exact
    (weightedPrimePatternEdges support scale outcome
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N) label).filter
        fun center =>
          (((label : ℝ) / (N : ℝ)),
            ((center : ℝ) / (N : ℝ))) ∈ domain

/-- The true integer prime-edge degree; it is zero at nonprime labels. -/
noncomputable def scaleAdaptiveSignedDegree
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N label : ℕ) : ℕ :=
  (scaleAdaptiveSignedDegreeEdges
    support scale outcome domain N label).card

/-- The genuine shared-label subdomain obtained by taking two independent
SIGNED centers in the SAME physical original-domain label fiber. -/
def scaleAdaptiveSignedSharedLabelDomainLift
    (domain : Set (ℝ × ℝ)) : Set (ℝ × ℝ × ℝ) :=
  {point |
    (point.1, point.2.1) ∈ domain ∧
    (point.1, point.2.2) ∈ domain}

/-- Exact membership in the ORIGINAL Green--Tao realization count is
membership in one genuine prime-edge fiber over an actual dyadic label. -/
theorem mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) (pair : ℕ × ℤ) :
    pair ∈ adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N ↔
        pair.1 ∈ Finset.Ioc N (2 * N) ∧
          pair.2 ∈ scaleAdaptiveSignedDegreeEdges
            support scale outcome domain N pair.1 := by
  classical
  simp only [adaptiveMixedSignedOriginalPrimeRealizations,
    scaleAdaptiveSignedDegreeEdges, Finset.mem_filter]
  constructor
  · rintro ⟨window, edge, physical⟩
    have label := (Finset.mem_product.mp window).1
    exact ⟨label, edge, physical⟩
  · rintro ⟨label, edge, physical⟩
    exact ⟨Finset.mem_product.mpr
      ⟨label, (Finset.mem_filter.mp edge).1⟩,
      edge, physical⟩

/-- Exact membership in the SHARED-LABEL Green--Tao realization count is
membership of TWO independently selected actual signed prime edges in the
same genuine prime-label fiber. -/
theorem mem_scaleAdaptiveSignedSharedLabelPrimeRealizations_iff_degree_edges
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ)
    (triple : ℕ × ℤ × ℤ) :
    triple ∈ adaptiveMixedSignedSharedLabelPrimeRealizations
      support scale outcome outcome
        (scaleAdaptiveSignedSharedLabelDomainLift domain) N ↔
      triple.1 ∈ Finset.Ioc N (2 * N) ∧
      triple.2.1 ∈ scaleAdaptiveSignedDegreeEdges
          support scale outcome domain N triple.1 ∧
        triple.2.2 ∈ scaleAdaptiveSignedDegreeEdges
          support scale outcome domain N triple.1 := by
  classical
  simp only [adaptiveMixedSignedSharedLabelPrimeRealizations,
    scaleAdaptiveSignedDegreeEdges, Finset.mem_filter]
  constructor
  · rintro ⟨window,
      first_edge, second_edge, first_physical, second_physical⟩
    have label := (Finset.mem_product.mp window).1
    exact ⟨label, ⟨first_edge, first_physical⟩,
      second_edge, second_physical⟩
  · rintro ⟨label, ⟨first_edge, first_physical⟩,
      second_edge, second_physical⟩
    exact ⟨Finset.mem_product.mpr
      ⟨label, Finset.mem_product.mpr
        ⟨(Finset.mem_filter.mp first_edge).1,
          (Finset.mem_filter.mp second_edge).1⟩⟩,
      first_edge, second_edge, first_physical, second_physical⟩

/-- Every nonempty signed degree fiber lies over a GENUINE prime label. -/
theorem scaleAdaptiveSignedDegreeEdges_label_prime
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N label : ℕ) (center : ℤ)
    (selected : center ∈ scaleAdaptiveSignedDegreeEdges
      support scale outcome domain N label) :
    label.Prime := by
  classical
  have edge := (Finset.mem_filter.mp selected).1
  exact (weightedPrimePatternEdges_prime_certificate
    support scale outcome
      (adaptiveMixedSignedSearchCenterWindow outcome.1 N)
      label center edge).1

/-- EXACT genuine signed prime-label FIRST moment.  The original published
prime-pattern realization count is the sum of the actual integer center
degrees over the real dyadic prime labels, with no model-degree premise. -/
theorem scaleAdaptiveSignedOriginalPrimeRealizations_card_eq_degree_sum
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) :
    (adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N).card =
      ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
        scaleAdaptiveSignedDegree support scale outcome domain N label := by
  classical
  let realizations :=
    adaptiveMixedSignedOriginalPrimeRealizations
      support scale outcome domain N
  let labels := scaleAdaptiveSignedDegreePrimeLabels N
  have mapped :
      (↑realizations : Set (ℕ × ℤ)).MapsTo
        (fun pair => pair.1) labels := by
    intro pair selected
    have decoded :=
      (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
        support scale outcome domain N pair).mp selected
    apply Finset.mem_filter.mpr
    exact ⟨decoded.1,
      scaleAdaptiveSignedDegreeEdges_label_prime
        support scale outcome domain N pair.1 pair.2 decoded.2⟩
  change realizations.card = _
  rw [Finset.card_eq_sum_card_fiberwise mapped]
  apply Finset.sum_congr rfl
  intro label label_selected
  change
    (realizations.filter fun pair => pair.1 = label).card =
      (scaleAdaptiveSignedDegreeEdges
        support scale outcome domain N label).card
  apply Finset.card_bij fun pair _ => pair.2
  · intro pair selected
    obtain ⟨realization, same_label⟩ := Finset.mem_filter.mp selected
    have edge :=
      (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
        support scale outcome domain N pair).mp realization |>.2
    simpa [same_label] using edge
  · intro first first_selected second second_selected same_center
    have first_label := (Finset.mem_filter.mp first_selected).2
    have second_label := (Finset.mem_filter.mp second_selected).2
    exact Prod.ext (first_label.trans second_label.symm) same_center
  · intro center selected
    refine ⟨(label, center), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl⟩
    apply (mem_scaleAdaptiveSignedOriginalPrimeRealizations_iff_degree_edge
      support scale outcome domain N (label, center)).mpr
    exact ⟨(Finset.mem_filter.mp label_selected).1, selected⟩

/-- EXACT genuine signed prime-label SECOND moment.  The raw shared-label
Green--Tao count, with its true fiber-square physical domain, equals the sum
of the SQUARES of the actual integer degrees at the SAME prime labels. -/
theorem scaleAdaptiveSignedSharedLabelPrimeRealizations_card_eq_degree_square_sum
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) :
    (adaptiveMixedSignedSharedLabelPrimeRealizations
      support scale outcome outcome
        (scaleAdaptiveSignedSharedLabelDomainLift domain) N).card =
      ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
        (scaleAdaptiveSignedDegree
          support scale outcome domain N label) ^ 2 := by
  classical
  let realizations :=
    adaptiveMixedSignedSharedLabelPrimeRealizations
      support scale outcome outcome
        (scaleAdaptiveSignedSharedLabelDomainLift domain) N
  let labels := scaleAdaptiveSignedDegreePrimeLabels N
  have mapped :
      (↑realizations : Set (ℕ × ℤ × ℤ)).MapsTo
        (fun triple => triple.1) labels := by
    intro triple selected
    have decoded :=
      (mem_scaleAdaptiveSignedSharedLabelPrimeRealizations_iff_degree_edges
        support scale outcome domain N triple).mp selected
    apply Finset.mem_filter.mpr
    exact ⟨decoded.1,
      scaleAdaptiveSignedDegreeEdges_label_prime
        support scale outcome domain N
          triple.1 triple.2.1 decoded.2.1⟩
  change realizations.card = _
  rw [Finset.card_eq_sum_card_fiberwise mapped]
  apply Finset.sum_congr rfl
  intro label label_selected
  let edges := scaleAdaptiveSignedDegreeEdges
    support scale outcome domain N label
  have fiber :
      (realizations.filter
        fun triple => triple.1 = label).card =
          (edges.product edges).card := by
    apply Finset.card_bij fun triple _ => triple.2
    · intro triple selected
      obtain ⟨realization, same_label⟩ := Finset.mem_filter.mp selected
      have both :=
        (mem_scaleAdaptiveSignedSharedLabelPrimeRealizations_iff_degree_edges
          support scale outcome domain N triple).mp realization |>.2
      apply Finset.mem_product.mpr
      exact ⟨by simpa [edges, same_label] using both.1,
        by simpa [edges, same_label] using both.2⟩
    · intro first first_selected second second_selected same_centers
      have first_label := (Finset.mem_filter.mp first_selected).2
      have second_label := (Finset.mem_filter.mp second_selected).2
      exact Prod.ext (first_label.trans second_label.symm) same_centers
    · intro centers selected
      obtain ⟨first, second⟩ := Finset.mem_product.mp selected
      refine ⟨(label, centers.1, centers.2), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      apply
        (mem_scaleAdaptiveSignedSharedLabelPrimeRealizations_iff_degree_edges
          support scale outcome domain N
            (label, centers.1, centers.2)).mpr
      exact ⟨(Finset.mem_filter.mp label_selected).1,
        first, second⟩
  calc
    _ = (edges.product edges).card := fiber
    _ = edges.card * edges.card := Finset.card_product edges edges
    _ = _ := by
      simp [edges, scaleAdaptiveSignedDegree, pow_two]

/-- The ORIGINAL fixed-system signed Green--Tao theorem directly supplies
the genuine prime-label FIRST degree-moment asymptotic.  No degree
regularity, concentration, covariance, or exceptional-label claim is
assumed as an additional analytic premise. -/
theorem scaleAdaptiveSignedDegree_firstMoment_tendsto_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support outcome.1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          ((∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            scaleAdaptiveSignedDegree
              support scale outcome domain N label : ℕ) : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card + 1) /
                (N : ℝ) ^ 2)
        atTop
          (nhds ((MeasureTheory.volume domain).toReal * singular)) := by
  obtain ⟨singular, positive, _converges, asymptotic⟩ :=
    scaleAdaptiveSignedOriginalPrimeRealizations_positive_asymptotic
      green_tao support scale outcome domain
      primes convex open_domain nonempty physical
  refine ⟨singular, positive, ?_⟩
  convert asymptotic using 1
  funext N
  rw [scaleAdaptiveSignedOriginalPrimeRealizations_card_eq_degree_sum]

/-- The SHARED-LABEL fixed-system signed Green--Tao theorem directly
supplies the genuine SECOND moment of actual integer prime-edge degrees.
Its singular constant is exactly the square of the ORIGINAL constant,
by uniqueness of the common genuine partial Euler-product limit. -/
theorem scaleAdaptiveSignedDegree_secondMoment_tendsto_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ
      (scaleAdaptiveSignedSharedLabelDomainLift domain))
    (open_domain : IsOpen
      (scaleAdaptiveSignedSharedLabelDomainLift domain))
    (nonempty :
      (scaleAdaptiveSignedSharedLabelDomainLift domain).Nonempty)
    (physical : scaleAdaptiveSignedSharedLabelDomainLift domain ⊆
      adaptiveMixedSignedSharedLabelPhysicalDomain
        support outcome.1 outcome.1) :
    ∃ singular : ℝ, 0 < singular ∧
      Tendsto
        (fun N : ℕ =>
          ((∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            (scaleAdaptiveSignedDegree
              support scale outcome domain N label) ^ 2 : ℕ) : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card +
                 (adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card + 1) /
                (N : ℝ) ^ 3)
        atTop
          (nhds
            ((MeasureTheory.volume
              (scaleAdaptiveSignedSharedLabelDomainLift domain)).toReal *
                singular ^ 2)) := by
  obtain ⟨first_singular, second_singular,
      first_converges, second_converges, asymptotic⟩ :=
    green_tao.shared_label support scale outcome outcome
      (scaleAdaptiveSignedSharedLabelDomainLift domain)
      primes convex open_domain nonempty physical
  have same_singular : first_singular = second_singular :=
    tendsto_nhds_unique first_converges second_converges
  subst second_singular
  refine ⟨first_singular,
    scaleAdaptiveSignedSingularLimit_pos
      support scale outcome primes first_singular first_converges, ?_⟩
  have rewritten :
      Tendsto
        (fun N : ℕ =>
          ((∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
            (scaleAdaptiveSignedDegree
              support scale outcome domain N label) ^ 2 : ℕ) : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card +
                 (adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card + 1) /
                (N : ℝ) ^ 3)
        atTop
          (nhds
            ((MeasureTheory.volume
              (scaleAdaptiveSignedSharedLabelDomainLift domain)).toReal *
                first_singular * first_singular)) := by
    convert asymptotic using 1
    funext N
    rw [scaleAdaptiveSignedSharedLabelPrimeRealizations_card_eq_degree_square_sum]
  simpa [pow_two, mul_assoc] using rewritten

/-- The EXACT centered actual prime-label degree variance, expressed using
the two raw signed Green--Tao prime realization counts.  The prime-label
cardinality remains present and must be supplied by the already audited
prime number theorem rather than silently replaced by a heuristic. -/
theorem scaleAdaptiveSignedDegree_centeredVariance_eq_actual_counts
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ) (expected : ℝ) :
    (∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
      ((scaleAdaptiveSignedDegree
        support scale outcome domain N label : ℝ) - expected) ^ 2) =
      ((adaptiveMixedSignedSharedLabelPrimeRealizations
        support scale outcome outcome
          (scaleAdaptiveSignedSharedLabelDomainLift domain) N).card : ℝ) -
      2 * expected *
        ((adaptiveMixedSignedOriginalPrimeRealizations
          support scale outcome domain N).card : ℝ) +
      ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) * expected ^ 2 := by
  rw [scaleAdaptiveSignedOriginalPrimeRealizations_card_eq_degree_sum,
    scaleAdaptiveSignedSharedLabelPrimeRealizations_card_eq_degree_square_sum]
  push_cast
  calc
    _ = ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
          (((scaleAdaptiveSignedDegree
            support scale outcome domain N label : ℝ)) ^ 2 -
            2 * expected *
              (scaleAdaptiveSignedDegree
                support scale outcome domain N label : ℝ) +
            expected ^ 2) := by
      apply Finset.sum_congr rfl
      intro label _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum]

/-- Genuine finite Chebyshev exceptional-label deletion for the ACTUAL
integer signed prime-edge degree ratio. This is an unconditional
consequence of the true same-label second moment, not an extra analytic
degree-regularity hypothesis. -/
theorem scaleAdaptiveSignedDegree_exceptional_card_mul_threshold_sq_le
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ)) (N : ℕ)
    (expected : ℕ → ℝ) (threshold : ℝ) :
    let exceptional :=
      (scaleAdaptiveSignedDegreePrimeLabels N).filter fun label =>
        threshold ^ 2 ≤
          (((scaleAdaptiveSignedDegree
            support scale outcome domain N label : ℝ) /
            expected label) - 1) ^ 2
    (exceptional.card : ℝ) * threshold ^ 2 ≤
      ∑ label ∈ scaleAdaptiveSignedDegreePrimeLabels N,
        (((scaleAdaptiveSignedDegree
          support scale outcome domain N label : ℝ) /
          expected label) - 1) ^ 2 := by
  exact weightedPrimePattern_exceptional_card_mul_threshold_sq_le
    (scaleAdaptiveSignedDegreePrimeLabels N)
    (fun label =>
      (scaleAdaptiveSignedDegree
        support scale outcome domain N label : ℝ) / expected label)
    threshold


end Erdos1139
