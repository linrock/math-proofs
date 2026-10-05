module

public import WeightedPrimePatternMomentBridge1139
public import AdaptiveMixedAffineComplexity1139
public import AdaptiveMixedSingularSeries1139
public import AdaptiveMertens1139
public import AdaptiveHarmonicShellBounds1139
public import AdaptiveMixedPairedSingularPositive1139
public import AdaptiveSharedLabelFactorization1139
public import ScaleAdaptiveParameterDecay1139

@[expose] public section


/-!
# Genuine signed-center global adaptive pattern options

The actual prime-pattern covering edge has SIGNED center C and lies in the
fundamental strip 0 <= b*p + W*C < p. For b > 0, every such C is negative.
Positive-coordinate Green--Tao boxes establish generic prime-pattern
existence but do not realize these covering edges.

This file proves the exact signed physical-target identity, the moving
reciprocal target windows, finite actual edge distributions including
dummy edges, and the exact one-half joint-color marginal for coherent
one-residue-per-label options. No prime-pattern asymptotic is asserted.
-/

open Finset
open scoped BigOperators

namespace Erdos1139

/-- The complete coarse signed center box containing the genuine
fundamental-strip centers. The actual signed inequality is imposed by the
already audited weightedPrimePatternEdges filter. -/
noncomputable def scaleAdaptiveSignedCenterWindow
    (base label : ℕ) : Finset ℤ :=
  Finset.Icc (-((base : ℤ) * (label : ℤ))) (label : ℤ)

/-- Every actual fundamental-strip center lies in the finite signed box;
thus no valid negative center is lost to a positive-coordinate shortcut. -/
theorem scaleAdaptiveSignedCenterWindow_complete
    (support : Finset ℕ) (base label : ℕ) (center : ℤ)
    (modulus_positive : 0 < adaptiveMixedTypeModulus support)
    (lower : 0 ≤ weightedPrimePatternSignedResidue
      support base label center)
    (upper : weightedPrimePatternSignedResidue
      support base label center < (label : ℤ)) :
    center ∈ scaleAdaptiveSignedCenterWindow base label := by
  apply Finset.mem_Icc.mpr
  have modulus_ge_one :
      1 ≤ (adaptiveMixedTypeModulus support : ℤ) := by
    exact_mod_cast modulus_positive
  have base_nonnegative : 0 ≤ (base : ℤ) := Int.natCast_nonneg _
  have label_nonnegative : 0 ≤ (label : ℤ) := Int.natCast_nonneg _
  have base_label_nonnegative :
      0 ≤ (base : ℤ) * (label : ℤ) :=
    mul_nonneg base_nonnegative label_nonnegative
  unfold weightedPrimePatternSignedResidue at lower upper
  constructor
  · by_contra not_lower
    have center_negative : center < 0 := by
      have strict := lt_of_not_ge not_lower
      linarith
    have correction_nonpositive :
        ((adaptiveMixedTypeModulus support : ℤ) - 1) * center ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr modulus_ge_one) center_negative.le
    nlinarith
  · by_contra not_upper
    have center_positive : 0 ≤ center := by
      have strict := lt_of_not_ge not_upper
      linarith
    have correction_nonnegative :
        0 ≤ ((adaptiveMixedTypeModulus support : ℤ) - 1) * center :=
      mul_nonneg (sub_nonneg.mpr modulus_ge_one) center_positive
    nlinarith

/-- The TRUE entire signed-center prime-pattern edge set, with no missing
negative centers and the genuine fundamental-strip restriction. -/
noncomputable def scaleAdaptiveSignedPrimeEdges
    (support : Finset ℕ) (scale : ℕ)
    (outcome : ℕ × ℕ) (label : ℕ) : Finset ℤ :=
  weightedPrimePatternEdges support scale outcome
    (scaleAdaptiveSignedCenterWindow outcome.1 label) label

/-- Exact coefficient recovery for the signed affine prime form. This is
the actual physical target numerator, with the genuine gcd type retained. -/
theorem scaleAdaptiveSignedPhysicalTarget_eq_residue_add_index
    {support : Finset ℕ} {scale index label : ℕ}
    {outcome : ℕ × ℕ} (center : ℤ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome) :
    (adaptiveMixedActualIndexType support outcome.1 index : ℤ) *
      weightedPrimePatternIntegerForm
        support outcome.1 index label center =
      weightedPrimePatternSignedResidue
        support outcome.1 label center +
          (index : ℤ) * (label : ℤ) := by
  have label_factor :=
    adaptiveMixedActualLabelCoefficient_factor primes active
  have center_factor :=
    adaptiveMixedActualCenterCoefficient_factor primes active
  unfold adaptiveMixedActualLabelCoefficient at label_factor
  unfold adaptiveMixedActualCenterCoefficient at center_factor
  have label_integer :
      (adaptiveMixedActualIndexType support outcome.1 index : ℤ) *
        (((outcome.1 + index) /
          adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ℤ) =
          (outcome.1 + index : ℕ) := by
    exact_mod_cast label_factor
  have center_integer :
      (adaptiveMixedActualIndexType support outcome.1 index : ℤ) *
        ((adaptiveMixedTypeModulus support /
          adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ℤ) =
          (adaptiveMixedTypeModulus support : ℤ) := by
    exact_mod_cast center_factor
  unfold weightedPrimePatternIntegerForm weightedPrimePatternSignedResidue
  calc
    _ =
      ((adaptiveMixedActualIndexType support outcome.1 index : ℤ) *
        (((outcome.1 + index) /
          adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ℤ)) *
          (label : ℤ) +
      ((adaptiveMixedActualIndexType support outcome.1 index : ℤ) *
        ((adaptiveMixedTypeModulus support /
          adaptiveMixedActualIndexType support outcome.1 index : ℕ) : ℤ)) *
          center := by ring
    _ = _ := by
      rw [label_integer, center_integer]
      push_cast
      ring

/-- A genuine signed-center edge places each selected physical target in
its EXACT moving reciprocal-scale interval [j*p,(j+1)*p), not in an
artificial positive-center box. -/
theorem scaleAdaptiveSignedPhysicalTarget_mem_moving_window
    {support : Finset ℕ} {scale index label : ℕ}
    {outcome : ℕ × ℕ} {center : ℤ}
    (primes : ∀ prime ∈ support, prime.Prime)
    (edge : center ∈ scaleAdaptiveSignedPrimeEdges
      support scale outcome label)
    (active : index ∈ adaptiveMixedOutcomeActiveIndices
      support scale outcome) :
    (index : ℤ) * (label : ℤ) ≤
      (adaptiveMixedActualIndexType support outcome.1 index : ℤ) *
        weightedPrimePatternIntegerForm
          support outcome.1 index label center ∧
      (adaptiveMixedActualIndexType support outcome.1 index : ℤ) *
        weightedPrimePatternIntegerForm
          support outcome.1 index label center <
        ((index : ℤ) + 1) * (label : ℤ) := by
  have certificate := weightedPrimePatternEdges_prime_certificate
    support scale outcome
      (scaleAdaptiveSignedCenterWindow outcome.1 label)
      label center edge
  rw [scaleAdaptiveSignedPhysicalTarget_eq_residue_add_index
    center primes active]
  constructor <;> nlinarith [certificate.2.2.1, certificate.2.2.2.1]

/-- One finite genuine family choice selects a pattern uniformly and
simultaneously selects a signed prime edge for EVERY pattern. The unused
pattern centers are denominator tags, not additional selected residues. -/
abbrev ScaleAdaptiveSignedFamilyChoice
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ) :=
  ↥patterns × ((pattern : ↥patterns) → ↥(edges pattern))

/-- The exact denominator of the genuine pattern/edge family: number of
patterns times the product of their true integer signed-center degrees. -/
theorem scaleAdaptiveSignedFamilyChoice_card
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ) :
    Fintype.card (ScaleAdaptiveSignedFamilyChoice patterns edges) =
      patterns.card * ∏ pattern : ↥patterns, (edges pattern).card := by
  simp [Fintype.card_prod, Fintype.card_pi]

/-- Nonempty genuine pattern and signed-center edge families make the
finite local denominator strictly positive, including empty-target dummy
edges retained solely for honest label normalization. -/
theorem scaleAdaptiveSignedFamilyChoice_card_pos
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ)
    (patterns_nonempty : patterns.Nonempty)
    (edges_nonempty : ∀ pattern ∈ patterns, (edges pattern).Nonempty) :
    0 < Fintype.card (ScaleAdaptiveSignedFamilyChoice patterns edges) := by
  rw [scaleAdaptiveSignedFamilyChoice_card]
  apply Nat.mul_pos (Finset.card_pos.mpr patterns_nonempty)
  apply Finset.prod_pos
  intro pattern _
  exact Finset.card_pos.mpr
    (edges_nonempty pattern pattern.property)

/-- Decode the ONE genuinely selected pattern and its ONE signed center
from the full family denominator tags. -/
def scaleAdaptiveSignedChosenPattern
    {patterns : Finset (ℕ × ℕ)}
    {edges : (ℕ × ℕ) → Finset ℤ}
    (choice : ScaleAdaptiveSignedFamilyChoice patterns edges) :
    ℕ × ℕ := choice.1

/-- The signed center chosen for the chosen pattern; every other pattern
coordinate is a dummy denominator tag and is NOT a second selected edge. -/
def scaleAdaptiveSignedChosenCenter
    {patterns : Finset (ℕ × ℕ)}
    {edges : (ℕ × ℕ) → Finset ℤ}
    (choice : ScaleAdaptiveSignedFamilyChoice patterns edges) : ℤ :=
  choice.2 choice.1

/-- The selected center is an actual signed member of its selected
pattern's genuine prime-edge set. -/
theorem scaleAdaptiveSignedChosenCenter_mem
    {patterns : Finset (ℕ × ℕ)}
    {edges : (ℕ × ℕ) → Finset ℤ}
    (choice : ScaleAdaptiveSignedFamilyChoice patterns edges) :
    scaleAdaptiveSignedChosenCenter choice ∈
      edges (scaleAdaptiveSignedChosenPattern choice) :=
  (choice.2 choice.1).property

/-- The exact finite event selecting one specified actual pattern and one
specified actual signed prime edge. Other pattern coordinates remain
harmless denominator tags. -/
def scaleAdaptiveSignedFamilyEdgeChoices
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ)
    (pattern : ↥patterns)
    (center : ↥(edges pattern)) :
    Finset (ScaleAdaptiveSignedFamilyChoice patterns edges) :=
  Finset.univ.filter fun choice =>
    choice.1 = pattern ∧ choice.2 pattern = center

/-- Exact multiplicity of one selected pattern/edge. Every other pattern
contributes its full genuine signed-center degree, while the selected
pattern and its selected center are fixed. -/
theorem scaleAdaptiveSignedFamilyEdgeChoices_card
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ)
    (pattern : ↥patterns)
    (center : ↥(edges pattern)) :
    (scaleAdaptiveSignedFamilyEdgeChoices
      patterns edges pattern center).card =
        ∏ other ∈ (Finset.univ.erase pattern),
          (edges other).card := by
  classical
  let assignments :
      Finset ((other : ↥patterns) → ↥(edges other)) :=
    Finset.univ.filter fun choice => choice pattern = center
  have event_bijection :
      (scaleAdaptiveSignedFamilyEdgeChoices
        patterns edges pattern center).card = assignments.card := by
    apply Finset.card_bij fun choice _ => choice.2
    · intro choice selected
      have decoded := (Finset.mem_filter.mp selected).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, decoded.2⟩
    · intro first selected_first second selected_second equal
      have first_pattern :=
        ((Finset.mem_filter.mp selected_first).2).1
      have second_pattern :=
        ((Finset.mem_filter.mp selected_second).2).1
      exact Prod.ext (first_pattern.trans second_pattern.symm) equal
    · intro assignment selected
      have fixed := (Finset.mem_filter.mp selected).2
      refine ⟨(pattern, assignment), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, rfl, fixed⟩
  rw [event_bijection]
  have product_fiber :=
    Fintype.card_filter_piFinset_eq_of_mem
      (fun other : ↥patterns =>
        (Finset.univ : Finset ↥(edges other)))
      pattern (Finset.mem_univ center)
  have complete_product :
      Fintype.piFinset
        (fun other : ↥patterns =>
          (Finset.univ : Finset ↥(edges other))) =
        (Finset.univ :
          Finset ((other : ↥patterns) → ↥(edges other))) := by
    ext assignment
    simp [Fintype.mem_piFinset]
  rw [complete_product] at product_fiber
  simpa [assignments] using product_fiber

/-- The genuine finite family samples the specified actual signed edge
with EXACT probability 1/(#patterns*d_pattern). This is the manuscript's
true mu_theta/d_theta, not uniform sampling over all rich residues. -/
theorem scaleAdaptiveSignedFamilyEdgeChoices_probability
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ)
    (pattern : ↥patterns)
    (center : ↥(edges pattern))
    (patterns_nonempty : patterns.Nonempty)
    (edges_nonempty : ∀ selected ∈ patterns,
      (edges selected).Nonempty) :
    ((scaleAdaptiveSignedFamilyEdgeChoices
      patterns edges pattern center).card : ℝ) /
      (Fintype.card
        (ScaleAdaptiveSignedFamilyChoice patterns edges) : ℝ) =
      1 / ((patterns.card : ℝ) * ((edges pattern).card : ℝ)) := by
  have pattern_nonzero : (patterns.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr patterns_nonempty).ne'
  have center_nonzero : ((edges pattern).card : ℝ) ≠ 0 := by
    exact_mod_cast
      (Finset.card_pos.mpr
        (edges_nonempty pattern pattern.property)).ne'
  have other_positive :
      0 < ∏ other ∈ (Finset.univ.erase pattern),
        (edges other).card := by
    apply Finset.prod_pos
    intro other _
    exact Finset.card_pos.mpr
      (edges_nonempty other other.property)
  have other_nonzero :
      ((∏ other ∈ (Finset.univ.erase pattern),
        (edges other).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast other_positive.ne'
  have other_real_nonzero :
      (∏ other ∈ (Finset.univ.erase pattern),
        ((edges other).card : ℝ)) ≠ 0 := by
    exact_mod_cast other_positive.ne'
  rw [scaleAdaptiveSignedFamilyEdgeChoices_card,
    scaleAdaptiveSignedFamilyChoice_card]
  have split :
      (∏ other ∈ (Finset.univ.erase pattern),
        (edges other).card) * (edges pattern).card =
          ∏ other : ↥patterns, (edges other).card :=
    Finset.prod_erase_mul Finset.univ
      (fun other : ↥patterns => (edges other).card)
      (Finset.mem_univ pattern)
  rw [← split]
  push_cast
  field_simp [pattern_nonzero, center_nonzero,
    other_nonzero, other_real_nonzero]

/-- The actual finite dependent type of genuine pattern/signed-edge
pairs, preserving the edge's own integer degree. -/
abbrev ScaleAdaptiveSignedPatternEdge
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ) :=
  Sigma fun pattern : ↥patterns => ↥(edges pattern)

/-- The ONE actual signed edge selected by a complete family choice. -/
def scaleAdaptiveSignedFamilyChosenEdge
    {patterns : Finset (ℕ × ℕ)}
    {edges : (ℕ × ℕ) → Finset ℤ}
    (choice : ScaleAdaptiveSignedFamilyChoice patterns edges) :
    ScaleAdaptiveSignedPatternEdge patterns edges :=
  ⟨choice.1, choice.2 choice.1⟩

/-- Exact fiber identity for choosing one genuine dependent signed edge.
This makes all target-event decompositions preserve true pattern
multiplicities instead of flattening to uniform rich residues. -/
theorem scaleAdaptiveSignedFamilyChosenEdge_fiber_eq
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ)
    (pattern : ↥patterns)
    (center : ↥(edges pattern)) :
    ((Finset.univ :
      Finset (ScaleAdaptiveSignedFamilyChoice patterns edges)).filter
        fun choice =>
          scaleAdaptiveSignedFamilyChosenEdge choice =
            (⟨pattern, center⟩ :
              ScaleAdaptiveSignedPatternEdge patterns edges)) =
      scaleAdaptiveSignedFamilyEdgeChoices
        patterns edges pattern center := by
  classical
  ext choice
  unfold scaleAdaptiveSignedFamilyEdgeChoices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    scaleAdaptiveSignedFamilyChosenEdge]
  constructor
  · intro selected
    have equal := (Finset.mem_filter.mp selected).2
    cases equal
    exact ⟨rfl, rfl⟩
  · rintro ⟨same_pattern, same_center⟩
    subst pattern
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    congr

/-- Exact full target-event probability under the genuine signed-center
family sampler. The event is the sum of its true edge masses
1/(#patterns*d_pattern); no canonical all-rich distribution appears. -/
theorem scaleAdaptiveSignedFamilyEvent_probability
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ)
    (events : Finset (ScaleAdaptiveSignedPatternEdge patterns edges))
    (patterns_nonempty : patterns.Nonempty)
    (edges_nonempty : ∀ selected ∈ patterns,
      (edges selected).Nonempty) :
    ((((Finset.univ :
      Finset (ScaleAdaptiveSignedFamilyChoice patterns edges)).filter
        fun choice =>
          scaleAdaptiveSignedFamilyChosenEdge choice ∈ events).card : ℝ) /
      (Fintype.card
        (ScaleAdaptiveSignedFamilyChoice patterns edges) : ℝ)) =
      ∑ edge ∈ events,
        1 / ((patterns.card : ℝ) * ((edges edge.1).card : ℝ)) := by
  classical
  have partition :=
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ :
        Finset (ScaleAdaptiveSignedFamilyChoice patterns edges))
      events
      (fun choice => scaleAdaptiveSignedFamilyChosenEdge choice)
  calc
    _ = ((∑ edge ∈ events,
          ((Finset.univ :
            Finset (ScaleAdaptiveSignedFamilyChoice patterns edges)).filter
              fun choice =>
                scaleAdaptiveSignedFamilyChosenEdge choice = edge).card :
            ℕ) : ℝ) /
          (Fintype.card
            (ScaleAdaptiveSignedFamilyChoice patterns edges) : ℝ) := by
      rw [partition]
    _ = ∑ edge ∈ events,
          ((((Finset.univ :
            Finset (ScaleAdaptiveSignedFamilyChoice patterns edges)).filter
              fun choice =>
                scaleAdaptiveSignedFamilyChosenEdge choice = edge).card :
            ℕ) : ℝ) /
            (Fintype.card
              (ScaleAdaptiveSignedFamilyChoice patterns edges) : ℝ) := by
      push_cast
      rw [Finset.sum_div]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro edge _
      rcases edge with ⟨pattern, center⟩
      rw [scaleAdaptiveSignedFamilyChosenEdge_fiber_eq]
      exact scaleAdaptiveSignedFamilyEdgeChoices_probability
        patterns edges pattern center
        patterns_nonempty edges_nonempty

/-- The genuine pattern/signed-edge pairs whose ONE physical residue hits
the specified target. Pattern multiplicities and the actual signed center
are retained; no uniform all-rich residue sampler is substituted. -/
noncomputable def scaleAdaptiveSignedFamilyTargetEdges
    (support : Finset ℕ) (label target : ℕ)
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ) :
    Finset (ScaleAdaptiveSignedPatternEdge patterns edges) :=
  Finset.univ.filter fun edge =>
    (weightedPrimePatternSignedResidue support
      (edge.1 : ℕ × ℕ).1 label (edge.2 : ℤ)).toNat ≡
        target [MOD label]

/-- The true family target-hit marginal is exactly the sum of the actual
signed prime-edge weights mu_theta/d_theta over ALL edges hitting that
target. This is the precise nonuniform marginal needed by the adaptive
first and shared-target moment calculations. -/
theorem scaleAdaptiveSignedFamilyTarget_probability
    (support : Finset ℕ) (label target : ℕ)
    (patterns : Finset (ℕ × ℕ))
    (edges : (ℕ × ℕ) → Finset ℤ)
    (patterns_nonempty : patterns.Nonempty)
    (edges_nonempty : ∀ selected ∈ patterns,
      (edges selected).Nonempty) :
    ((((Finset.univ :
      Finset (ScaleAdaptiveSignedFamilyChoice patterns edges)).filter
        fun choice =>
          (weightedPrimePatternSignedResidue support
            (scaleAdaptiveSignedChosenPattern choice).1 label
            (scaleAdaptiveSignedChosenCenter choice)).toNat ≡
              target [MOD label]).card : ℝ) /
      (Fintype.card
        (ScaleAdaptiveSignedFamilyChoice patterns edges) : ℝ)) =
      ∑ edge ∈ scaleAdaptiveSignedFamilyTargetEdges
        support label target patterns edges,
        1 / ((patterns.card : ℝ) * ((edges edge.1).card : ℝ)) := by
  classical
  have same_events :
      ((Finset.univ :
        Finset (ScaleAdaptiveSignedFamilyChoice patterns edges)).filter
          fun choice =>
            (weightedPrimePatternSignedResidue support
              (scaleAdaptiveSignedChosenPattern choice).1 label
              (scaleAdaptiveSignedChosenCenter choice)).toNat ≡
                target [MOD label]) =
        ((Finset.univ :
          Finset (ScaleAdaptiveSignedFamilyChoice patterns edges)).filter
            fun choice =>
              scaleAdaptiveSignedFamilyChosenEdge choice ∈
                scaleAdaptiveSignedFamilyTargetEdges
                  support label target patterns edges) := by
    ext choice
    constructor
    · intro selected
      have hit := (Finset.mem_filter.mp selected).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hit⟩
    · intro selected
      have edge_selected := (Finset.mem_filter.mp selected).2
      have hit := (Finset.mem_filter.mp edge_selected).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hit⟩
  rw [same_events]
  exact scaleAdaptiveSignedFamilyEvent_probability
    patterns edges
      (scaleAdaptiveSignedFamilyTargetEdges
        support label target patterns edges)
      patterns_nonempty edges_nonempty

/-- EVERY convergent genuine fixed mixed-pattern singular series has a
strictly positive limit. This follows from the already proved uniform
finite-Euler-product floor, including the active ranks zero and one. -/
theorem scaleAdaptiveSignedSingularLimit_pos
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (singular : ℝ)
    (converges : Filter.Tendsto
      (adaptiveMixedSignedSingularPartialProduct support scale outcome)
      Filter.atTop (nhds singular)) :
    0 < singular := by
  obtain ⟨floor, floor_positive, uniformly_lower⟩ :=
    adaptiveMixedActualNormalizedLocalFactor_uniform_positive_all_ranks
      support scale outcome primes
  have floor_le : floor ≤ singular := by
    apply ge_of_tendsto converges
    apply Filter.Eventually.of_forall
    intro cutoff
    exact uniformly_lower (Nat.primesLE cutoff)
      (fun prime selected => Nat.prime_of_mem_primesLE selected)
  exact lt_of_lt_of_le floor_positive floor_le

/-- Genuine shared-LABEL singular products converge to exactly the
product of the two independently normalized prime-pattern singular
series. This uses the ACTUAL shared-label local-selector cardinality,
not a heuristic independence assertion or an abstract substitute. -/
theorem scaleAdaptiveSignedSharedLabelSingularProduct_tendsto
    (support : Finset ℕ) (scale : ℕ)
    (first second : ℕ × ℕ)
    (primes : ∀ prime ∈ support, prime.Prime)
    (first_singular second_singular : ℝ)
    (first_converges : Filter.Tendsto
      (adaptiveMixedSignedSingularPartialProduct support scale first)
      Filter.atTop (nhds first_singular))
    (second_converges : Filter.Tendsto
      (adaptiveMixedSignedSingularPartialProduct support scale second)
      Filter.atTop (nhds second_singular)) :
    Filter.Tendsto
      (fun cutoff : ℕ =>
        ∏ prime ∈ Nat.primesLE cutoff,
          adaptiveMixedActualSharedLabelScalarLocalFactor
            support scale first second prime)
      Filter.atTop (nhds (first_singular * second_singular)) := by
  have factorization :
      (fun cutoff : ℕ =>
        ∏ prime ∈ Nat.primesLE cutoff,
          adaptiveMixedActualSharedLabelScalarLocalFactor
            support scale first second prime) =
        fun cutoff : ℕ =>
          adaptiveMixedSignedSingularPartialProduct
            support scale first cutoff *
          adaptiveMixedSignedSingularPartialProduct
            support scale second cutoff := by
    funext cutoff
    exact adaptiveMixedActualSharedLabel_finite_singular_product_eq_product
      support scale first second (Nat.primesLE cutoff) primes
        (fun prime selected => Nat.prime_of_mem_primesLE selected)
  rw [factorization]
  exact first_converges.mul second_converges

/-- The ONLY explicit external analytic parameter gives an actual
strictly positive singular constant and the genuine SIGNED original
prime-pattern count asymptotic on every fixed open convex subwindow.
This is a consequence of the recognizable Green--Tao input, not a new
postulate or an assumed target-moment estimate. -/
theorem scaleAdaptiveSignedOriginalPrimeRealizations_positive_asymptotic
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
      Filter.Tendsto
        (adaptiveMixedSignedSingularPartialProduct support scale outcome)
        Filter.atTop (nhds singular) ∧
      Filter.Tendsto
        (fun N : ℕ =>
          ((adaptiveMixedSignedOriginalPrimeRealizations
            support scale outcome domain N).card : ℝ) *
              Real.log (N : ℝ) ^
                ((adaptiveMixedOutcomeActiveIndices
                  support scale outcome).card + 1) /
                (N : ℝ) ^ 2)
        Filter.atTop
          (nhds ((MeasureTheory.volume domain).toReal * singular)) := by
  obtain ⟨singular, converges, asymptotic⟩ :=
    green_tao.original support scale outcome domain
      primes convex open_domain nonempty physical
  exact ⟨singular,
    scaleAdaptiveSignedSingularLimit_pos
      support scale outcome primes singular converges,
    converges, asymptotic⟩

/-- On every fixed positive-volume genuine SIGNED physical subwindow, the
explicit Green--Tao input supplies actual prime edges for ALL sufficiently
large scales. In particular, the previously exposed positive-natural-center
substitute is not being used to witness nonempty adaptive edge degrees. -/
theorem scaleAdaptiveSignedOriginalPrimeRealizations_eventually_nonempty
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (support : Finset ℕ) (scale : ℕ) (outcome : ℕ × ℕ)
    (domain : Set (ℝ × ℝ))
    (primes : ∀ prime ∈ support, prime.Prime)
    (convex : Convex ℝ domain)
    (open_domain : IsOpen domain)
    (nonempty : domain.Nonempty)
    (physical : domain ⊆
      adaptiveMixedSignedOriginalPhysicalDomain support outcome.1)
    (volume_positive : 0 < (MeasureTheory.volume domain).toReal) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (adaptiveMixedSignedOriginalPrimeRealizations
        support scale outcome domain N).Nonempty := by
  obtain ⟨singular, singular_positive, _converges, asymptotic⟩ :=
    scaleAdaptiveSignedOriginalPrimeRealizations_positive_asymptotic
      green_tao support scale outcome domain
      primes convex open_domain nonempty physical
  have limit_positive :
      0 < (MeasureTheory.volume domain).toReal * singular :=
    mul_pos volume_positive singular_positive
  filter_upwards [(tendsto_order.1 asymptotic).1 0 limit_positive]
    with N positive
  apply Finset.card_pos.mp
  by_contra not_positive
  have zero :
      (adaptiveMixedSignedOriginalPrimeRealizations
        support scale outcome domain N).card = 0 :=
    Nat.eq_zero_of_not_pos not_positive
  simp [zero] at positive

/-- Exact finite coordinate-event multiplicity in a dependent product of
actual label option spaces. Every unselected label contributes its own
genuine full denominator; no equal-degree hypothesis is imposed. -/
theorem scaleAdaptiveGlobalCoordinateEvent_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (choices : ι → Type*)
    [∀ coordinate, Fintype (choices coordinate)]
    [∀ coordinate, DecidableEq (choices coordinate)]
    (coordinate : ι) (events : Finset (choices coordinate)) :
    ((Finset.univ :
        Finset ((index : ι) → choices index)).filter
      fun assignment => assignment coordinate ∈ events).card =
        events.card *
          ∏ other ∈ (Finset.univ.erase coordinate),
            Fintype.card (choices other) := by
  classical
  let selected :
      Finset ((index : ι) → choices index) :=
    Finset.univ.filter fun assignment =>
      assignment coordinate ∈ events
  have mapped :
      (↑selected : Set ((index : ι) → choices index)).MapsTo
        (fun assignment => assignment coordinate) events := by
    intro assignment selected_assignment
    exact (Finset.mem_filter.mp selected_assignment).2
  change selected.card = _
  rw [Finset.card_eq_sum_card_fiberwise mapped]
  calc
    _ = ∑ event ∈ events,
          ((Finset.univ :
            Finset ((index : ι) → choices index)).filter
              fun assignment =>
                assignment coordinate = event).card := by
      apply Finset.sum_congr rfl
      intro event event_selected
      congr 1
      ext assignment
      simp only [selected, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, equal⟩
        exact equal
      · intro equal
        exact ⟨equal ▸ event_selected, equal⟩
    _ = ∑ _event ∈ events,
          (∏ other ∈ (Finset.univ.erase coordinate),
            Fintype.card (choices other)) := by
      apply Finset.sum_congr rfl
      intro event _
      have fiber :=
        Fintype.card_filter_piFinset_eq_of_mem
          (fun other : ι =>
            (Finset.univ : Finset (choices other)))
          coordinate (Finset.mem_univ event)
      have full :
          Fintype.piFinset
            (fun other : ι =>
              (Finset.univ : Finset (choices other))) =
            (Finset.univ :
              Finset ((index : ι) → choices index)) := by
        ext assignment
        simp
      rw [full] at fiber
      simpa using fiber
    _ = _ := by simp

/-- The actual common family denominator across the whole genuine prime
pool. Each label has its own pattern support and its own signed-center
degree; coordinates at other labels are only finite denominator tags. -/
abbrev ScaleAdaptiveSignedGlobalFamilyChoice
    (R : Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ) :=
  (prime : ↥R) →
    ScaleAdaptiveSignedFamilyChoice (patterns prime) (edges prime)

/-- Exact product cardinality of the actual all-label family denominator. -/
theorem scaleAdaptiveSignedGlobalFamilyChoice_card
    (R : Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ) :
    Fintype.card
      (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges) =
        ∏ prime : ↥R,
          (patterns prime).card *
            ∏ pattern : ↥(patterns prime),
              (edges prime pattern).card := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro prime _
  exact scaleAdaptiveSignedFamilyChoice_card
    (patterns prime) (edges prime)

/-- The common all-label family denominator is positive when every actual
label has at least one pattern and each pattern has a genuine signed
prime edge. -/
theorem scaleAdaptiveSignedGlobalFamilyChoice_card_pos
    (R : Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (patterns_nonempty : ∀ prime, (patterns prime).Nonempty)
    (edges_nonempty : ∀ prime pattern,
      pattern ∈ patterns prime → (edges prime pattern).Nonempty) :
    0 < Fintype.card
      (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges) := by
  rw [Fintype.card_pi]
  apply Finset.prod_pos
  intro prime _
  exact scaleAdaptiveSignedFamilyChoice_card_pos
    (patterns prime) (edges prime)
    (patterns_nonempty prime)
    (fun pattern selected =>
      edges_nonempty prime pattern selected)

/-- Genuine all-label events selecting one exact pattern and signed prime
edge at ONE specified actual label. -/
def scaleAdaptiveSignedGlobalEdgeChoices
    (R : Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (prime : ↥R)
    (pattern : ↥(patterns prime))
    (center : ↥(edges prime pattern)) :
    Finset (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges) :=
  Finset.univ.filter fun assignment =>
    assignment prime ∈
      scaleAdaptiveSignedFamilyEdgeChoices
        (patterns prime) (edges prime) pattern center

/-- Exact global denominator clearing does not distort any local pattern
weight: an actual signed edge at one actual label still has probability
mu_theta/d_theta = 1/(#patterns*d_theta). All other label coordinates are
harmless genuine finite denominator tags. -/
theorem scaleAdaptiveSignedGlobalEdgeChoices_probability
    (R : Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (prime : ↥R)
    (pattern : ↥(patterns prime))
    (center : ↥(edges prime pattern))
    (patterns_nonempty : ∀ label, (patterns label).Nonempty)
    (edges_nonempty : ∀ label selected,
      selected ∈ patterns label →
        (edges label selected).Nonempty) :
    ((scaleAdaptiveSignedGlobalEdgeChoices R patterns edges
      prime pattern center).card : ℝ) /
      (Fintype.card
        (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges) : ℝ) =
      1 / (((patterns prime).card : ℝ) *
        ((edges prime pattern).card : ℝ)) := by
  classical
  let localEvents :=
    scaleAdaptiveSignedFamilyEdgeChoices
      (patterns prime) (edges prime) pattern center
  let localSize :=
    Fintype.card
      (ScaleAdaptiveSignedFamilyChoice
        (patterns prime) (edges prime))
  let otherProduct :=
    ∏ other ∈ (Finset.univ.erase prime),
      Fintype.card
        (ScaleAdaptiveSignedFamilyChoice
          (patterns other) (edges other))
  have event_card :
      (scaleAdaptiveSignedGlobalEdgeChoices R patterns edges
        prime pattern center).card =
          localEvents.card * otherProduct := by
    exact scaleAdaptiveGlobalCoordinateEvent_card
      (fun label : ↥R =>
        ScaleAdaptiveSignedFamilyChoice
          (patterns label) (edges label))
      prime localEvents
  have global_card :
      Fintype.card
        (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges) =
          otherProduct * localSize := by
    rw [Fintype.card_pi]
    exact (Finset.prod_erase_mul Finset.univ
      (fun label : ↥R =>
        Fintype.card (ScaleAdaptiveSignedFamilyChoice
          (patterns label) (edges label)))
      (Finset.mem_univ prime)).symm
  have local_positive : 0 < localSize :=
    scaleAdaptiveSignedFamilyChoice_card_pos
      (patterns prime) (edges prime)
      (patterns_nonempty prime)
      (fun selected member =>
        edges_nonempty prime selected member)
  have other_positive : 0 < otherProduct := by
    apply Finset.prod_pos
    intro other _
    exact scaleAdaptiveSignedFamilyChoice_card_pos
      (patterns other) (edges other)
      (patterns_nonempty other)
      (fun selected member =>
        edges_nonempty other selected member)
  have local_nonzero : (localSize : ℝ) ≠ 0 := by
    exact_mod_cast local_positive.ne'
  have other_nonzero : (otherProduct : ℝ) ≠ 0 := by
    exact_mod_cast other_positive.ne'
  calc
    _ = (localEvents.card : ℝ) / (localSize : ℝ) := by
      rw [event_card, global_card]
      push_cast
      field_simp [local_nonzero, other_nonzero]
    _ = _ :=
      scaleAdaptiveSignedFamilyEdgeChoices_probability
        (patterns prime) (edges prime) pattern center
        (patterns_nonempty prime)
        (fun selected member =>
          edges_nonempty prime selected member)

/-- A single fair Boolean color and one low/high finite family option;
the option of the unchosen color is only a harmless denominator tag. -/
abbrev ScaleAdaptiveActualJointRawChoice
    (lowOptions highOptions : ℕ) :=
  Bool × Fin lowOptions × Fin highOptions

/-- The TRUE shared finite denominator of the coherent color/residue
distribution, including its exact factor two. -/
noncomputable def scaleAdaptiveActualJointDenominator
    (lowOptions highOptions : ℕ) : ℕ :=
  Fintype.card
    (ScaleAdaptiveActualJointRawChoice lowOptions highOptions)

/-- Exact joint denominator; no low/high prime-label pools are split or
silently duplicated. -/
theorem scaleAdaptiveActualJointDenominator_eq
    (lowOptions highOptions : ℕ) :
    scaleAdaptiveActualJointDenominator lowOptions highOptions =
      2 * lowOptions * highOptions := by
  simp [scaleAdaptiveActualJointDenominator, Fintype.card_prod,
    Nat.mul_assoc]

/-- The actual fair joint denominator is nonempty precisely when both
genuine family option spaces are nonempty. -/
theorem scaleAdaptiveActualJointDenominator_pos
    {lowOptions highOptions : ℕ}
    (low_positive : 0 < lowOptions)
    (high_positive : 0 < highOptions) :
    0 < scaleAdaptiveActualJointDenominator lowOptions highOptions := by
  rw [scaleAdaptiveActualJointDenominator_eq]
  positivity

/-- Canonical decoding of the exact coherent finite joint option. -/
noncomputable def scaleAdaptiveActualJointEquiv
    (lowOptions highOptions : ℕ) :
    ScaleAdaptiveActualJointRawChoice lowOptions highOptions ≃
      Fin (scaleAdaptiveActualJointDenominator lowOptions highOptions) :=
  Fintype.equivFin
    (ScaleAdaptiveActualJointRawChoice lowOptions highOptions)

/-- ONE fair label color, chosen jointly with its ONE selected residue. -/
noncomputable def scaleAdaptiveActualJointColor
    (R : Finset ℕ) (lowOptions highOptions : ℕ) :
    ↥R → Fin
      (scaleAdaptiveActualJointDenominator lowOptions highOptions) → Bool :=
  fun _ option =>
    ((scaleAdaptiveActualJointEquiv lowOptions highOptions).symm option).1

/-- Exactly one residue from the selected family's actual finite option;
the opposite-color option is a tag and is never another residue. -/
noncomputable def scaleAdaptiveActualJointResidue
    {lowOptions highOptions : ℕ} (R : Finset ℕ)
    (lowResidue : ↥R → Fin lowOptions → ℕ)
    (highResidue : ↥R → Fin highOptions → ℕ) :
    ↥R → Fin
      (scaleAdaptiveActualJointDenominator lowOptions highOptions) → ℕ :=
  fun prime option =>
    let choice :=
      (scaleAdaptiveActualJointEquiv lowOptions highOptions).symm option
    match choice.1 with
    | false => lowResidue prime choice.2.1
    | true => highResidue prime choice.2.2

/-- Exact low-color hit membership in the true finite joint option. -/
theorem scaleAdaptiveActualJointHit_mem_low
    {lowOptions highOptions : ℕ} (R : Finset ℕ)
    (lowResidue : ↥R → Fin lowOptions → ℕ)
    (highResidue : ↥R → Fin highOptions → ℕ)
    (target : ℕ) (prime : ↥R)
    (option : Fin
      (scaleAdaptiveActualJointDenominator lowOptions highOptions)) :
    option ∈ scaleAdaptiveColorHitChoices R
      (scaleAdaptiveActualJointColor R lowOptions highOptions)
      (scaleAdaptiveActualJointResidue R lowResidue highResidue)
      false target prime ↔
    ((scaleAdaptiveActualJointEquiv
      lowOptions highOptions).symm option).1 = false ∧
      lowResidue prime
        ((scaleAdaptiveActualJointEquiv
          lowOptions highOptions).symm option).2.1 ≡
        target [MOD (prime : ℕ)] := by
  unfold scaleAdaptiveColorHitChoices
    scaleAdaptiveActualJointColor scaleAdaptiveActualJointResidue
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨colored, hit⟩
    exact ⟨colored, by simpa [colored] using hit⟩
  · rintro ⟨colored, hit⟩
    exact ⟨colored, by simpa [colored] using hit⟩

/-- Exact high-color hit membership in the same true finite joint option. -/
theorem scaleAdaptiveActualJointHit_mem_high
    {lowOptions highOptions : ℕ} (R : Finset ℕ)
    (lowResidue : ↥R → Fin lowOptions → ℕ)
    (highResidue : ↥R → Fin highOptions → ℕ)
    (target : ℕ) (prime : ↥R)
    (option : Fin
      (scaleAdaptiveActualJointDenominator lowOptions highOptions)) :
    option ∈ scaleAdaptiveColorHitChoices R
      (scaleAdaptiveActualJointColor R lowOptions highOptions)
      (scaleAdaptiveActualJointResidue R lowResidue highResidue)
      true target prime ↔
    ((scaleAdaptiveActualJointEquiv
      lowOptions highOptions).symm option).1 = true ∧
      highResidue prime
        ((scaleAdaptiveActualJointEquiv
          lowOptions highOptions).symm option).2.2 ≡
        target [MOD (prime : ℕ)] := by
  unfold scaleAdaptiveColorHitChoices
    scaleAdaptiveActualJointColor scaleAdaptiveActualJointResidue
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨colored, hit⟩
    exact ⟨colored, by simpa [colored] using hit⟩
  · rintro ⟨colored, hit⟩
    exact ⟨colored, by simpa [colored] using hit⟩

/-- Exact low-hit multiplicity: every genuine selected low option is
repeated once for each harmless opposite-color high denominator tag. -/
theorem scaleAdaptiveActualJointHit_card_low
    {lowOptions highOptions : ℕ} (R : Finset ℕ)
    (lowResidue : ↥R → Fin lowOptions → ℕ)
    (highResidue : ↥R → Fin highOptions → ℕ)
    (target : ℕ) (prime : ↥R) :
    (scaleAdaptiveColorHitChoices R
      (scaleAdaptiveActualJointColor R lowOptions highOptions)
      (scaleAdaptiveActualJointResidue R lowResidue highResidue)
      false target prime).card =
      (independentResidueHitChoices R lowResidue target prime).card *
        highOptions := by
  classical
  let equivalence :=
    scaleAdaptiveActualJointEquiv lowOptions highOptions
  let lowHits :=
    independentResidueHitChoices R lowResidue target prime
  let highAll : Finset (Fin highOptions) := Finset.univ
  have bijection :
      (scaleAdaptiveColorHitChoices R
        (scaleAdaptiveActualJointColor R lowOptions highOptions)
        (scaleAdaptiveActualJointResidue R lowResidue highResidue)
        false target prime).card = (lowHits.product highAll).card := by
    apply Finset.card_bij fun option _ =>
      ((equivalence.symm option).2.1, (equivalence.symm option).2.2)
    · intro option selected
      have decoded :=
        (scaleAdaptiveActualJointHit_mem_low
          R lowResidue highResidue target prime option).mp selected
      apply Finset.mem_product.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, decoded.2⟩
    · intro first selected_first second selected_second equal
      have first_color :=
        ((scaleAdaptiveActualJointHit_mem_low
          R lowResidue highResidue target prime first).mp
            selected_first).1
      have second_color :=
        ((scaleAdaptiveActualJointHit_mem_low
          R lowResidue highResidue target prime second).mp
            selected_second).1
      apply equivalence.symm.injective
      apply Prod.ext
      · exact first_color.trans second_color.symm
      · exact Prod.ext (congrArg Prod.fst equal)
          (congrArg Prod.snd equal)
    · intro pair selected
      obtain ⟨low_selected, _high_selected⟩ :=
        Finset.mem_product.mp selected
      let choice :
          ScaleAdaptiveActualJointRawChoice lowOptions highOptions :=
        (false, pair.1, pair.2)
      let option := equivalence choice
      refine ⟨option, ?_, ?_⟩
      · apply (scaleAdaptiveActualJointHit_mem_low
          R lowResidue highResidue target prime option).mpr
        have hit := (Finset.mem_filter.mp low_selected).2
        simpa [option, choice, equivalence] using hit
      · simp [option, choice]
  simpa [lowHits, highAll] using bijection

/-- Exact high-hit multiplicity, with all low options as harmless tags. -/
theorem scaleAdaptiveActualJointHit_card_high
    {lowOptions highOptions : ℕ} (R : Finset ℕ)
    (lowResidue : ↥R → Fin lowOptions → ℕ)
    (highResidue : ↥R → Fin highOptions → ℕ)
    (target : ℕ) (prime : ↥R) :
    (scaleAdaptiveColorHitChoices R
      (scaleAdaptiveActualJointColor R lowOptions highOptions)
      (scaleAdaptiveActualJointResidue R lowResidue highResidue)
      true target prime).card =
      lowOptions *
        (independentResidueHitChoices R highResidue target prime).card := by
  classical
  let equivalence :=
    scaleAdaptiveActualJointEquiv lowOptions highOptions
  let lowAll : Finset (Fin lowOptions) := Finset.univ
  let highHits :=
    independentResidueHitChoices R highResidue target prime
  have bijection :
      (scaleAdaptiveColorHitChoices R
        (scaleAdaptiveActualJointColor R lowOptions highOptions)
        (scaleAdaptiveActualJointResidue R lowResidue highResidue)
        true target prime).card = (lowAll.product highHits).card := by
    apply Finset.card_bij fun option _ =>
      ((equivalence.symm option).2.1, (equivalence.symm option).2.2)
    · intro option selected
      have decoded :=
        (scaleAdaptiveActualJointHit_mem_high
          R lowResidue highResidue target prime option).mp selected
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, decoded.2⟩
    · intro first selected_first second selected_second equal
      have first_color :=
        ((scaleAdaptiveActualJointHit_mem_high
          R lowResidue highResidue target prime first).mp
            selected_first).1
      have second_color :=
        ((scaleAdaptiveActualJointHit_mem_high
          R lowResidue highResidue target prime second).mp
            selected_second).1
      apply equivalence.symm.injective
      apply Prod.ext
      · exact first_color.trans second_color.symm
      · exact Prod.ext (congrArg Prod.fst equal)
          (congrArg Prod.snd equal)
    · intro pair selected
      obtain ⟨_low_selected, high_selected⟩ :=
        Finset.mem_product.mp selected
      let choice :
          ScaleAdaptiveActualJointRawChoice lowOptions highOptions :=
        (true, pair.1, pair.2)
      let option := equivalence choice
      refine ⟨option, ?_, ?_⟩
      · apply (scaleAdaptiveActualJointHit_mem_high
          R lowResidue highResidue target prime option).mpr
        have hit := (Finset.mem_filter.mp high_selected).2
        simpa [option, choice, equivalence] using hit
      · simp [option, choice]
  simpa [lowAll, highHits] using bijection

/-- Exact fair low-color hit marginal for ARBITRARY actual rationally
weighted family residues. No deterministic precoloring or second residue
at one label is inserted. -/
theorem scaleAdaptiveActualJointHitFraction_low_eq_half
    {lowOptions highOptions : ℕ} (R : Finset ℕ)
    (lowResidue : ↥R → Fin lowOptions → ℕ)
    (highResidue : ↥R → Fin highOptions → ℕ)
    (target : ℕ) (prime : ↥R)
    (low_positive : 0 < lowOptions)
    (high_positive : 0 < highOptions) :
    scaleAdaptiveColorHitFraction R
      (scaleAdaptiveActualJointColor R lowOptions highOptions)
      (scaleAdaptiveActualJointResidue R lowResidue highResidue)
      false target prime =
        independentResidueHitFraction R
          lowResidue target prime / 2 := by
  have low_nonzero : (lowOptions : ℝ) ≠ 0 := by
    exact_mod_cast low_positive.ne'
  have high_nonzero : (highOptions : ℝ) ≠ 0 := by
    exact_mod_cast high_positive.ne'
  unfold scaleAdaptiveColorHitFraction independentResidueHitFraction
  rw [scaleAdaptiveActualJointHit_card_low,
    scaleAdaptiveActualJointDenominator_eq]
  push_cast
  field_simp [low_nonzero, high_nonzero]

/-- Exact fair high-color hit marginal from the SAME coherent option and
the SAME actual prime label. -/
theorem scaleAdaptiveActualJointHitFraction_high_eq_half
    {lowOptions highOptions : ℕ} (R : Finset ℕ)
    (lowResidue : ↥R → Fin lowOptions → ℕ)
    (highResidue : ↥R → Fin highOptions → ℕ)
    (target : ℕ) (prime : ↥R)
    (low_positive : 0 < lowOptions)
    (high_positive : 0 < highOptions) :
    scaleAdaptiveColorHitFraction R
      (scaleAdaptiveActualJointColor R lowOptions highOptions)
      (scaleAdaptiveActualJointResidue R lowResidue highResidue)
      true target prime =
        independentResidueHitFraction R
          highResidue target prime / 2 := by
  have low_nonzero : (lowOptions : ℝ) ≠ 0 := by
    exact_mod_cast low_positive.ne'
  have high_nonzero : (highOptions : ℝ) ≠ 0 := by
    exact_mod_cast high_positive.ne'
  unfold scaleAdaptiveColorHitFraction independentResidueHitFraction
  rw [scaleAdaptiveActualJointHit_card_high,
    scaleAdaptiveActualJointDenominator_eq]
  push_cast
  field_simp [low_nonzero, high_nonzero]

/-- Actual targets in the same congruence class as a canonical signed-strip
representative. This retains all genuine target hits of the chosen edge. -/
def scaleAdaptiveSignedResidueTargetCandidates
    (targets : Finset ℕ) (prime residue : ℕ) : Finset ℕ :=
  targets.filter fun target => residue ≡ target [MOD prime]

/-- Replace a canonical strip residue by one actual target in its class
when any such target exists; otherwise retain the canonical dummy residue.
This exactly matches the audited actual-pattern support predicate. -/
noncomputable def scaleAdaptiveSignedTargetSupportedResidue
    (targets : Finset ℕ) (prime residue : ℕ) : ℕ :=
  if nonempty :
      (scaleAdaptiveSignedResidueTargetCandidates
        targets prime residue).Nonempty then
    (scaleAdaptiveSignedResidueTargetCandidates
      targets prime residue).min' nonempty
  else
    residue

/-- The target-supported replacement is congruent to the exact original
signed-strip residue; therefore it does not alter ANY actual target hit. -/
theorem scaleAdaptiveSignedTargetSupportedResidue_congruent
    (targets : Finset ℕ) (prime residue : ℕ) :
    residue ≡
      scaleAdaptiveSignedTargetSupportedResidue
        targets prime residue [MOD prime] := by
  unfold scaleAdaptiveSignedTargetSupportedResidue
  split_ifs with nonempty
  · exact (Finset.mem_filter.mp
      (Finset.min'_mem
        (scaleAdaptiveSignedResidueTargetCandidates
          targets prime residue) nonempty)).2
  · exact Nat.ModEq.refl residue

/-- Every supported replacement is either a genuine target of its own
family or an honest dummy option hitting NO target in that family. -/
theorem scaleAdaptiveSignedTargetSupportedResidue_mem_or_dummy
    (targets : Finset ℕ) (prime residue : ℕ) :
    scaleAdaptiveSignedTargetSupportedResidue
        targets prime residue ∈ targets ∨
      ∀ target ∈ targets,
        ¬ scaleAdaptiveSignedTargetSupportedResidue
          targets prime residue ≡ target [MOD prime] := by
  unfold scaleAdaptiveSignedTargetSupportedResidue
  split_ifs with nonempty
  · left
    exact (Finset.mem_filter.mp
      (Finset.min'_mem
        (scaleAdaptiveSignedResidueTargetCandidates
          targets prime residue) nonempty)).1
  · right
    intro target selected congruent
    apply nonempty
    exact ⟨target, Finset.mem_filter.mpr
      ⟨selected, congruent⟩⟩

/-- Replacing the canonical strip representative by a supported target
preserves EVERY target hit, including targets other than the chosen
representative. -/
theorem scaleAdaptiveSignedTargetSupportedResidue_hit_iff
    (targets : Finset ℕ) (prime residue target : ℕ) :
    scaleAdaptiveSignedTargetSupportedResidue
        targets prime residue ≡ target [MOD prime] ↔
      residue ≡ target [MOD prime] := by
  have congruent :=
    scaleAdaptiveSignedTargetSupportedResidue_congruent
      targets prime residue
  constructor
  · intro selected
    exact congruent.trans selected
  · intro selected
    exact congruent.symm.trans selected

/-- Exact equivalence from true all-label signed family choices to ONE
common finite family denominator. -/
noncomputable def scaleAdaptiveSignedGlobalFamilyEquiv
    (R : Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ) :
    ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges ≃
      Fin (Fintype.card
        (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges)) :=
  Fintype.equivFin
    (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges)

/-- The ONE actual target-supported residue chosen by a genuine global
signed-center family option at its ONE actual prime label. All other
pattern/label coordinates are finite denominator tags. -/
noncomputable def scaleAdaptiveSignedGlobalFamilyResidue
    (R targets : Finset ℕ)
    (support : ↥R → Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ) :
    ↥R → Fin (Fintype.card
      (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges)) → ℕ :=
  fun prime option =>
    let localChoice :=
      ((scaleAdaptiveSignedGlobalFamilyEquiv
        R patterns edges).symm option) prime
    scaleAdaptiveSignedTargetSupportedResidue targets prime
      (weightedPrimePatternSignedResidue
        (support prime)
        (scaleAdaptiveSignedChosenPattern localChoice).1
        prime
        (scaleAdaptiveSignedChosenCenter localChoice)).toNat

/-- Every global signed-family residue has genuine target-or-dummy
support at its own actual prime label. -/
theorem scaleAdaptiveSignedGlobalFamilyResidue_supported
    (R targets : Finset ℕ)
    (support : ↥R → Finset ℕ)
    (patterns : ↥R → Finset (ℕ × ℕ))
    (edges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (prime : ↥R)
    (option : Fin (Fintype.card
      (ScaleAdaptiveSignedGlobalFamilyChoice R patterns edges))) :
    scaleAdaptiveSignedGlobalFamilyResidue
        R targets support patterns edges prime option ∈ targets ∨
      ∀ target ∈ targets,
        ¬ scaleAdaptiveSignedGlobalFamilyResidue
          R targets support patterns edges prime option ≡
            target [MOD (prime : ℕ)] := by
  exact scaleAdaptiveSignedTargetSupportedResidue_mem_or_dummy
    targets prime
      (weightedPrimePatternSignedResidue
        (support prime)
        (scaleAdaptiveSignedChosenPattern
          (((scaleAdaptiveSignedGlobalFamilyEquiv
            R patterns edges).symm option) prime)).1
        prime
        (scaleAdaptiveSignedChosenCenter
          (((scaleAdaptiveSignedGlobalFamilyEquiv
            R patterns edges).symm option) prime))).toNat

/-- Any two honestly supported actual family residue lists yield the
existing exact shared-pool weighted-pattern support predicate under ONE
coherent fair joint color/residue option. Dummy edges remain present. -/
theorem scaleAdaptiveActualJointOptions_supported
    {lowOptions highOptions : ℕ}
    (R lowTargets highTargets : Finset ℕ)
    (lowResidue : ↥R → Fin lowOptions → ℕ)
    (highResidue : ↥R → Fin highOptions → ℕ)
    (low_supported : ∀ prime option,
      lowResidue prime option ∈ lowTargets ∨
        ∀ target ∈ lowTargets,
          ¬ lowResidue prime option ≡ target [MOD (prime : ℕ)])
    (high_supported : ∀ prime option,
      highResidue prime option ∈ highTargets ∨
        ∀ target ∈ highTargets,
          ¬ highResidue prime option ≡ target [MOD (prime : ℕ)]) :
    WeightedActualPatternOptionsSupported
      R lowTargets highTargets
      (scaleAdaptiveActualJointColor R lowOptions highOptions)
      (scaleAdaptiveActualJointResidue R lowResidue highResidue) := by
  intro prime option
  constructor
  · intro colored
    have choice_color :
        ((scaleAdaptiveActualJointEquiv
          lowOptions highOptions).symm option).1 = false := colored
    simpa [scaleAdaptiveActualJointResidue, choice_color] using
      low_supported prime
        ((scaleAdaptiveActualJointEquiv
          lowOptions highOptions).symm option).2.1
  · intro colored
    have choice_color :
        ((scaleAdaptiveActualJointEquiv
          lowOptions highOptions).symm option).1 = true := colored
    simpa [scaleAdaptiveActualJointResidue, choice_color] using
      high_supported prime
        ((scaleAdaptiveActualJointEquiv
          lowOptions highOptions).symm option).2.2

/-- The actual common signed-prime-pattern joint denominator for both
families and the ENTIRE shared genuine prime pool. -/
noncomputable def scaleAdaptiveSignedJointOptionCount
    (R : Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ) : ℕ :=
  scaleAdaptiveActualJointDenominator
    (Fintype.card
      (ScaleAdaptiveSignedGlobalFamilyChoice
        R lowPatterns lowEdges))
    (Fintype.card
      (ScaleAdaptiveSignedGlobalFamilyChoice
        R highPatterns highEdges))

/-- The ONE actual color selected by a signed-prime-pattern option at
its ONE actual prime. -/
noncomputable def scaleAdaptiveSignedJointColor
    (R : Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ) :
    ↥R → Fin (scaleAdaptiveSignedJointOptionCount
      R lowPatterns highPatterns lowEdges highEdges) → Bool :=
  scaleAdaptiveActualJointColor R
    (Fintype.card
      (ScaleAdaptiveSignedGlobalFamilyChoice
        R lowPatterns lowEdges))
    (Fintype.card
      (ScaleAdaptiveSignedGlobalFamilyChoice
        R highPatterns highEdges))

/-- The ONE actual target-supported residue chosen by the complete signed
low/high pattern construction. Every opposite-color, opposite-pattern,
and opposite-label coordinate is only a denominator tag. -/
noncomputable def scaleAdaptiveSignedJointResidue
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ) :
    ↥R → Fin (scaleAdaptiveSignedJointOptionCount
      R lowPatterns highPatterns lowEdges highEdges) → ℕ :=
  scaleAdaptiveActualJointResidue R
    (scaleAdaptiveSignedGlobalFamilyResidue
      R lowTargets lowSupport lowPatterns lowEdges)
    (scaleAdaptiveSignedGlobalFamilyResidue
      R highTargets highSupport highPatterns highEdges)

/-- Nonempty genuine signed low/high edge families give a strictly
positive honest COMMON joint finite option count. -/
theorem scaleAdaptiveSignedJointOptionCount_pos
    (R : Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (low_patterns_nonempty : ∀ prime, (lowPatterns prime).Nonempty)
    (high_patterns_nonempty : ∀ prime, (highPatterns prime).Nonempty)
    (low_edges_nonempty : ∀ prime pattern,
      pattern ∈ lowPatterns prime →
        (lowEdges prime pattern).Nonempty)
    (high_edges_nonempty : ∀ prime pattern,
      pattern ∈ highPatterns prime →
        (highEdges prime pattern).Nonempty) :
    0 < scaleAdaptiveSignedJointOptionCount
      R lowPatterns highPatterns lowEdges highEdges := by
  exact scaleAdaptiveActualJointDenominator_pos
    (scaleAdaptiveSignedGlobalFamilyChoice_card_pos
      R lowPatterns lowEdges
      low_patterns_nonempty low_edges_nonempty)
    (scaleAdaptiveSignedGlobalFamilyChoice_card_pos
      R highPatterns highEdges
      high_patterns_nonempty high_edges_nonempty)

/-- The COMPLETE actual signed-center joint construction satisfies the
existing target-or-dummy support predicate, with one common prime pool,
one color, and one residue at every option. -/
theorem scaleAdaptiveSignedJointOptions_supported
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ) :
    WeightedActualPatternOptionsSupported
      R lowTargets highTargets
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges) := by
  exact scaleAdaptiveActualJointOptions_supported
    R lowTargets highTargets
    (scaleAdaptiveSignedGlobalFamilyResidue
      R lowTargets lowSupport lowPatterns lowEdges)
    (scaleAdaptiveSignedGlobalFamilyResidue
      R highTargets highSupport highPatterns highEdges)
    (fun prime option =>
      scaleAdaptiveSignedGlobalFamilyResidue_supported
        R lowTargets lowSupport lowPatterns lowEdges prime option)
    (fun prime option =>
      scaleAdaptiveSignedGlobalFamilyResidue_supported
        R highTargets highSupport highPatterns highEdges prime option)

/-- The genuine signed-center low option distribution keeps EXACTLY half
of its own true global-family target marginal. -/
theorem scaleAdaptiveSignedJointHitFraction_low_eq_half
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ) (prime : ↥R)
    (low_patterns_nonempty : ∀ label, (lowPatterns label).Nonempty)
    (high_patterns_nonempty : ∀ label, (highPatterns label).Nonempty)
    (low_edges_nonempty : ∀ label pattern,
      pattern ∈ lowPatterns label →
        (lowEdges label pattern).Nonempty)
    (high_edges_nonempty : ∀ label pattern,
      pattern ∈ highPatterns label →
        (highEdges label pattern).Nonempty) :
    scaleAdaptiveColorHitFraction R
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges)
      false target prime =
        independentResidueHitFraction R
          (scaleAdaptiveSignedGlobalFamilyResidue
            R lowTargets lowSupport lowPatterns lowEdges)
          target prime / 2 := by
  exact scaleAdaptiveActualJointHitFraction_low_eq_half
    R
    (scaleAdaptiveSignedGlobalFamilyResidue
      R lowTargets lowSupport lowPatterns lowEdges)
    (scaleAdaptiveSignedGlobalFamilyResidue
      R highTargets highSupport highPatterns highEdges)
    target prime
    (scaleAdaptiveSignedGlobalFamilyChoice_card_pos
      R lowPatterns lowEdges
      low_patterns_nonempty low_edges_nonempty)
    (scaleAdaptiveSignedGlobalFamilyChoice_card_pos
      R highPatterns highEdges
      high_patterns_nonempty high_edges_nonempty)

/-- The genuine signed-center high option distribution keeps EXACTLY
half of its own true global-family target marginal. -/
theorem scaleAdaptiveSignedJointHitFraction_high_eq_half
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ) (prime : ↥R)
    (low_patterns_nonempty : ∀ label, (lowPatterns label).Nonempty)
    (high_patterns_nonempty : ∀ label, (highPatterns label).Nonempty)
    (low_edges_nonempty : ∀ label pattern,
      pattern ∈ lowPatterns label →
        (lowEdges label pattern).Nonempty)
    (high_edges_nonempty : ∀ label pattern,
      pattern ∈ highPatterns label →
        (highEdges label pattern).Nonempty) :
    scaleAdaptiveColorHitFraction R
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges)
      true target prime =
        independentResidueHitFraction R
          (scaleAdaptiveSignedGlobalFamilyResidue
            R highTargets highSupport highPatterns highEdges)
          target prime / 2 := by
  exact scaleAdaptiveActualJointHitFraction_high_eq_half
    R
    (scaleAdaptiveSignedGlobalFamilyResidue
      R lowTargets lowSupport lowPatterns lowEdges)
    (scaleAdaptiveSignedGlobalFamilyResidue
      R highTargets highSupport highPatterns highEdges)
    target prime
    (scaleAdaptiveSignedGlobalFamilyChoice_card_pos
      R lowPatterns lowEdges
      low_patterns_nonempty low_edges_nonempty)
    (scaleAdaptiveSignedGlobalFamilyChoice_card_pos
      R highPatterns highEdges
      high_patterns_nonempty high_edges_nonempty)

/-- The TRUE complete low target load of the actual signed-center joint
construction is exactly half the sum of its genuine family marginals.
The factor one half is applied ONCE, after global denominator clearing. -/
theorem scaleAdaptiveSignedJointHitLoad_low_eq_half
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ)
    (low_patterns_nonempty : ∀ label, (lowPatterns label).Nonempty)
    (high_patterns_nonempty : ∀ label, (highPatterns label).Nonempty)
    (low_edges_nonempty : ∀ label pattern,
      pattern ∈ lowPatterns label →
        (lowEdges label pattern).Nonempty)
    (high_edges_nonempty : ∀ label pattern,
      pattern ∈ highPatterns label →
        (highEdges label pattern).Nonempty) :
    weightedActualPatternHitLoad R
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges)
      false target =
        (∑ prime : ↥R,
          independentResidueHitFraction R
            (scaleAdaptiveSignedGlobalFamilyResidue
              R lowTargets lowSupport lowPatterns lowEdges)
            target prime) / 2 := by
  unfold weightedActualPatternHitLoad
  calc
    _ = ∑ prime : ↥R,
          independentResidueHitFraction R
            (scaleAdaptiveSignedGlobalFamilyResidue
              R lowTargets lowSupport lowPatterns lowEdges)
            target prime / 2 := by
      apply Finset.sum_congr rfl
      intro prime _
      exact scaleAdaptiveSignedJointHitFraction_low_eq_half
        R lowTargets highTargets lowSupport highSupport
        lowPatterns highPatterns lowEdges highEdges
        target prime low_patterns_nonempty high_patterns_nonempty
        low_edges_nonempty high_edges_nonempty
    _ = _ := by
      rw [Finset.sum_div]

/-- The TRUE complete high target load receives the same exact fair
color factor one half in the SAME shared prime pool. -/
theorem scaleAdaptiveSignedJointHitLoad_high_eq_half
    (R lowTargets highTargets : Finset ℕ)
    (lowSupport highSupport : ↥R → Finset ℕ)
    (lowPatterns highPatterns : ↥R → Finset (ℕ × ℕ))
    (lowEdges highEdges : ↥R → (ℕ × ℕ) → Finset ℤ)
    (target : ℕ)
    (low_patterns_nonempty : ∀ label, (lowPatterns label).Nonempty)
    (high_patterns_nonempty : ∀ label, (highPatterns label).Nonempty)
    (low_edges_nonempty : ∀ label pattern,
      pattern ∈ lowPatterns label →
        (lowEdges label pattern).Nonempty)
    (high_edges_nonempty : ∀ label pattern,
      pattern ∈ highPatterns label →
        (highEdges label pattern).Nonempty) :
    weightedActualPatternHitLoad R
      (scaleAdaptiveSignedJointColor
        R lowPatterns highPatterns lowEdges highEdges)
      (scaleAdaptiveSignedJointResidue
        R lowTargets highTargets lowSupport highSupport
          lowPatterns highPatterns lowEdges highEdges)
      true target =
        (∑ prime : ↥R,
          independentResidueHitFraction R
            (scaleAdaptiveSignedGlobalFamilyResidue
              R highTargets highSupport highPatterns highEdges)
            target prime) / 2 := by
  unfold weightedActualPatternHitLoad
  calc
    _ = ∑ prime : ↥R,
          independentResidueHitFraction R
            (scaleAdaptiveSignedGlobalFamilyResidue
              R highTargets highSupport highPatterns highEdges)
            target prime / 2 := by
      apply Finset.sum_congr rfl
      intro prime _
      exact scaleAdaptiveSignedJointHitFraction_high_eq_half
        R lowTargets highTargets lowSupport highSupport
        lowPatterns highPatterns lowEdges highEdges
        target prime low_patterns_nonempty high_patterns_nonempty
        low_edges_nonempty high_edges_nonempty
    _ = _ := by
      rw [Finset.sum_div]

end Erdos1139
