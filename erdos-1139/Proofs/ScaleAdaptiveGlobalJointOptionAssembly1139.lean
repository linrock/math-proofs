module

public import ScaleAdaptiveGTZGlobalCover1139
public import ScaleAdaptiveGlobalTypedTargetClassification1139

@[expose] public section


/-!
# One global prime pool and actual joint color/residue options

Every fixed dyadic shell has its own low and high square-core supports, full
mixed-pattern outcome spaces, signed physical center fibers, and canonical
singular factors.  The actual selected prime set must nevertheless be ONE
global pool, with each genuine prime appearing in only one integer-floored
shell and choosing just one color and one residue.

This file assembles the true per-shell two-support good-label intersections,
recovers the unique physical shell of each global label, and constructs one
common finite option denominator with shell-dependent actual outcome and
signed-center families.  It proves primality, fresh-core disjointness,
positive true integer degrees, target-or-dummy support, and full genuine
prime-scale density under the sole explicit fixed-parameter signed
Green--Tao proposition.  No global exponential target budget or completed
cover is assumed.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1139

/-- FIXED shell configuration for one global two-color construction.  Every
support, outcome space, singular, and denominator may depend on its true
physical shell, but no parameter depends on the original interval length. -/
structure ScaleAdaptiveGlobalJointConfiguration where
  exponents : Finset ℕ
  lowSupport : ℕ → Finset ℕ
  highSupport : ℕ → Finset ℕ
  lower : ℝ
  upper : ℝ
  lowSingular : ℕ → (ℕ × ℕ) → ℝ
  highSingular : ℕ → (ℕ × ℕ) → ℝ

/-- The genuine per-shell BOTH-support usable-prime intersection at the
EXACT floored physical scale `length / 2^exponent`. -/
noncomputable def scaleAdaptiveGlobalTwoColorGoodShell
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length exponent : ℕ) : Finset ℕ :=
  scaleAdaptiveSignedTwoColorGoodPrimeLabels
    (configuration.lowSupport exponent)
    (configuration.highSupport exponent)
    (2 ^ exponent) configuration.lower configuration.upper
    (configuration.lowSingular exponent)
    (configuration.highSingular exponent)
    (scaleAdaptiveDyadicPhysicalScale length exponent)

/-- The ONE global set of genuinely selected prime labels.  Different
integer-floored dyadic shells are disjoint, so labels are never duplicated. -/
noncomputable def scaleAdaptiveGlobalJointPrimePool
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) : Finset ℕ :=
  configuration.exponents.biUnion
    (scaleAdaptiveGlobalTwoColorGoodShell configuration length)

/-- Every usable shell label belongs to its ACTUAL original dyadic prime
shell, before any density or prime-pattern theorem is invoked. -/
theorem scaleAdaptiveGlobalTwoColorGoodShell_subset_shell
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length exponent : ℕ) :
    scaleAdaptiveGlobalTwoColorGoodShell configuration length exponent ⊆
      scaleAdaptiveDyadicPrimeShell length exponent := by
  intro label selected
  exact (Finset.mem_sdiff.mp selected).1

/-- The global selected pool is a genuine SUBSET of the actual disjoint
integer-floored prime-shell union; therefore its true product conductor can
be bounded by the already audited physical-shell conductor. -/
theorem scaleAdaptiveGlobalJointPrimePool_subset_shell_union
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    scaleAdaptiveGlobalJointPrimePool configuration length ⊆
      configuration.exponents.biUnion
        (scaleAdaptiveDyadicPrimeShell length) := by
  intro label selected
  obtain ⟨exponent, in_family, in_shell⟩ :=
    Finset.mem_biUnion.mp selected
  exact Finset.mem_biUnion.mpr
    ⟨exponent, in_family,
      scaleAdaptiveGlobalTwoColorGoodShell_subset_shell
        configuration length exponent in_shell⟩

/-- Every globally selected label is an actual prime, not an abstract option
identifier or a reused per-pattern copy. -/
theorem scaleAdaptiveGlobalJointPrimePool_prime
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) {label : ℕ}
    (selected : label ∈ scaleAdaptiveGlobalJointPrimePool
      configuration length) : label.Prime := by
  obtain ⟨exponent, _, in_shell⟩ := Finset.mem_biUnion.mp
    (scaleAdaptiveGlobalJointPrimePool_subset_shell_union
      configuration length selected)
  exact (mem_scaleAdaptiveDyadicPrimeShell.mp in_shell).2.2

/-- Distinct good-shell pools inherit the exact disjointness of their true
integer-floored physical prime-label intervals. -/
theorem scaleAdaptiveGlobalTwoColorGoodShell_disjoint
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) {first second : ℕ} (different : first ≠ second) :
    Disjoint
      (scaleAdaptiveGlobalTwoColorGoodShell configuration length first)
      (scaleAdaptiveGlobalTwoColorGoodShell configuration length second) := by
  apply Finset.disjoint_left.mpr
  intro label in_first in_second
  exact Finset.disjoint_left.mp
    (scaleAdaptiveDyadicPrimeShell_disjoint length different)
      (scaleAdaptiveGlobalTwoColorGoodShell_subset_shell
        configuration length first in_first)
      (scaleAdaptiveGlobalTwoColorGoodShell_subset_shell
        configuration length second in_second)

/-- Canonical unique shell index of an actual label.  The default `0` is
used only outside the selected pool and is never invoked for a pool member. -/
noncomputable def scaleAdaptiveGlobalJointShellIndex
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length label : ℕ) : ℕ :=
  if witness : ∃ exponent,
    exponent ∈ configuration.exponents ∧
      label ∈ scaleAdaptiveGlobalTwoColorGoodShell
        configuration length exponent then
    Nat.find witness
  else 0

/-- A genuine selected label belongs to its canonical actual shell, and the
canonical shell belongs to the fixed finite exponent family. -/
theorem scaleAdaptiveGlobalJointShellIndex_mem
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) {label : ℕ}
    (selected : label ∈ scaleAdaptiveGlobalJointPrimePool
      configuration length) :
    scaleAdaptiveGlobalJointShellIndex configuration length label ∈
      configuration.exponents ∧
    label ∈ scaleAdaptiveGlobalTwoColorGoodShell configuration length
      (scaleAdaptiveGlobalJointShellIndex
        configuration length label) := by
  obtain ⟨exponent, in_family, in_shell⟩ :=
    Finset.mem_biUnion.mp selected
  have witness : ∃ exponent,
      exponent ∈ configuration.exponents ∧
        label ∈ scaleAdaptiveGlobalTwoColorGoodShell
          configuration length exponent :=
    ⟨exponent, in_family, in_shell⟩
  unfold scaleAdaptiveGlobalJointShellIndex
  rw [dif_pos witness]
  exact Nat.find_spec witness

/-- The recovered index is the UNIQUE actual physical shell of the
selected label; integer-flooring cannot create a cross-shell collision. -/
theorem scaleAdaptiveGlobalJointShellIndex_eq_of_mem
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) {exponent label : ℕ}
    (in_family : exponent ∈ configuration.exponents)
    (selected : label ∈ scaleAdaptiveGlobalTwoColorGoodShell
      configuration length exponent) :
    scaleAdaptiveGlobalJointShellIndex configuration length label = exponent := by
  have in_pool : label ∈ scaleAdaptiveGlobalJointPrimePool
      configuration length := Finset.mem_biUnion.mpr
        ⟨exponent, in_family, selected⟩
  obtain ⟨_, canonical⟩ := scaleAdaptiveGlobalJointShellIndex_mem
    configuration length in_pool
  by_contra different
  exact Finset.disjoint_left.mp
    (scaleAdaptiveGlobalTwoColorGoodShell_disjoint
      configuration length different) canonical selected

/-- Shell-dependent genuine LOW square-core support at one selected prime. -/
noncomputable def scaleAdaptiveGlobalJointLowSupport
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    ↥(scaleAdaptiveGlobalJointPrimePool configuration length) → Finset ℕ :=
  fun label => configuration.lowSupport
    (scaleAdaptiveGlobalJointShellIndex configuration length label)

/-- Shell-dependent genuine HIGH square-core support at the SAME prime. -/
noncomputable def scaleAdaptiveGlobalJointHighSupport
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    ↥(scaleAdaptiveGlobalJointPrimePool configuration length) → Finset ℕ :=
  fun label => configuration.highSupport
    (scaleAdaptiveGlobalJointShellIndex configuration length label)

/-- Full actual LOW outcome family at the recovered genuine shell scale. -/
noncomputable def scaleAdaptiveGlobalJointLowPatterns
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    ↥(scaleAdaptiveGlobalJointPrimePool configuration length) →
      Finset (ℕ × ℕ) :=
  fun label =>
    adaptiveMixedOutcomeSpace
      (scaleAdaptiveGlobalJointLowSupport configuration length label)
      (2 ^ scaleAdaptiveGlobalJointShellIndex
        configuration length label)

/-- Full actual HIGH outcome family at the SAME recovered shell scale. -/
noncomputable def scaleAdaptiveGlobalJointHighPatterns
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    ↥(scaleAdaptiveGlobalJointPrimePool configuration length) →
      Finset (ℕ × ℕ) :=
  fun label =>
    adaptiveMixedOutcomeSpace
      (scaleAdaptiveGlobalJointHighSupport configuration length label)
      (2 ^ scaleAdaptiveGlobalJointShellIndex
        configuration length label)

/-- Genuine signed-center LOW prime edges, at their true integer physical
scale and their actual label-dependent square-core support. -/
noncomputable def scaleAdaptiveGlobalJointLowEdges
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    ↥(scaleAdaptiveGlobalJointPrimePool configuration length) →
      (ℕ × ℕ) → Finset ℤ :=
  fun label outcome =>
    let exponent := scaleAdaptiveGlobalJointShellIndex
      configuration length label
    scaleAdaptiveSignedDegreeEdges
      (configuration.lowSupport exponent) (2 ^ exponent) outcome
      (scaleAdaptiveSignedConstantResidueBand
        (configuration.lowSupport exponent) outcome.1
          configuration.lower configuration.upper)
      (scaleAdaptiveDyadicPhysicalScale length exponent) label

/-- Genuine signed-center HIGH edges at the SAME physical prime label. -/
noncomputable def scaleAdaptiveGlobalJointHighEdges
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    ↥(scaleAdaptiveGlobalJointPrimePool configuration length) →
      (ℕ × ℕ) → Finset ℤ :=
  fun label outcome =>
    let exponent := scaleAdaptiveGlobalJointShellIndex
      configuration length label
    scaleAdaptiveSignedDegreeEdges
      (configuration.highSupport exponent) (2 ^ exponent) outcome
      (scaleAdaptiveSignedConstantResidueBand
        (configuration.highSupport exponent) outcome.1
          configuration.lower configuration.upper)
      (scaleAdaptiveDyadicPhysicalScale length exponent) label

/-- Every retained global label has a NONEMPTY actual LOW signed-center
fiber for EVERY outcome of its unique shell-dependent family. -/
theorem scaleAdaptiveGlobalJointLowEdges_nonempty
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ)
    (label : ↥(scaleAdaptiveGlobalJointPrimePool configuration length))
    {outcome : ℕ × ℕ}
    (selected : outcome ∈
      scaleAdaptiveGlobalJointLowPatterns configuration length label) :
    (scaleAdaptiveGlobalJointLowEdges
      configuration length label outcome).Nonempty := by
  obtain ⟨_, good⟩ := scaleAdaptiveGlobalJointShellIndex_mem
    configuration length label.property
  exact scaleAdaptiveSignedTwoColorGoodPrimeLabels_low_usable
    good selected

/-- Every retained global label has a NONEMPTY actual HIGH signed-center
fiber for EVERY outcome of the opposite genuine family. -/
theorem scaleAdaptiveGlobalJointHighEdges_nonempty
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ)
    (label : ↥(scaleAdaptiveGlobalJointPrimePool configuration length))
    {outcome : ℕ × ℕ}
    (selected : outcome ∈
      scaleAdaptiveGlobalJointHighPatterns configuration length label) :
    (scaleAdaptiveGlobalJointHighEdges
      configuration length label outcome).Nonempty := by
  obtain ⟨_, good⟩ := scaleAdaptiveGlobalJointShellIndex_mem
    configuration length label.property
  exact scaleAdaptiveSignedTwoColorGoodPrimeLabels_high_usable
    good selected

/-- Genuine prime supports make every label's LOW full mixed-outcome
family nonempty; its complexity may vary between physical shells. -/
theorem scaleAdaptiveGlobalJointLowPatterns_nonempty
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ)
    (primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (label : ↥(scaleAdaptiveGlobalJointPrimePool configuration length)) :
    (scaleAdaptiveGlobalJointLowPatterns
      configuration length label).Nonempty := by
  obtain ⟨in_family, _⟩ := scaleAdaptiveGlobalJointShellIndex_mem
    configuration length label.property
  exact scaleAdaptiveMixedFullOutcomeSpace_nonempty _ _
    (primes _ in_family)

/-- Genuine HIGH prime supports make every opposite-color full outcome
family nonempty at the SAME selected prime. -/
theorem scaleAdaptiveGlobalJointHighPatterns_nonempty
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ)
    (primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime)
    (label : ↥(scaleAdaptiveGlobalJointPrimePool configuration length)) :
    (scaleAdaptiveGlobalJointHighPatterns
      configuration length label).Nonempty := by
  obtain ⟨in_family, _⟩ := scaleAdaptiveGlobalJointShellIndex_mem
    configuration length label.property
  exact scaleAdaptiveMixedFullOutcomeSpace_nonempty _ _
    (primes _ in_family)

/-- The ONE common finite denominator for all labels, both colors, all
shell-dependent patterns, and every true positive signed-center degree. -/
noncomputable def scaleAdaptiveGlobalJointOptionCount
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) : ℕ :=
  scaleAdaptiveSignedJointOptionCount
    (scaleAdaptiveGlobalJointPrimePool configuration length)
    (scaleAdaptiveGlobalJointLowPatterns configuration length)
    (scaleAdaptiveGlobalJointHighPatterns configuration length)
    (scaleAdaptiveGlobalJointLowEdges configuration length)
    (scaleAdaptiveGlobalJointHighEdges configuration length)

/-- Actual color array for the ONE global finite option space. -/
noncomputable def scaleAdaptiveGlobalJointColor
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    ↥(scaleAdaptiveGlobalJointPrimePool configuration length) →
      Fin (scaleAdaptiveGlobalJointOptionCount configuration length) → Bool :=
  scaleAdaptiveSignedJointColor
    (scaleAdaptiveGlobalJointPrimePool configuration length)
    (scaleAdaptiveGlobalJointLowPatterns configuration length)
    (scaleAdaptiveGlobalJointHighPatterns configuration length)
    (scaleAdaptiveGlobalJointLowEdges configuration length)
    (scaleAdaptiveGlobalJointHighEdges configuration length)

/-- Actual target-or-dummy residue array for the SAME global finite option
space, with ONE color and ONE coherent residue at each true prime. -/
noncomputable def scaleAdaptiveGlobalJointResidue
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) (lowTargets highTargets : Finset ℕ) :
    ↥(scaleAdaptiveGlobalJointPrimePool configuration length) →
      Fin (scaleAdaptiveGlobalJointOptionCount configuration length) → ℕ :=
  scaleAdaptiveSignedJointResidue
    (scaleAdaptiveGlobalJointPrimePool configuration length)
    lowTargets highTargets
    (scaleAdaptiveGlobalJointLowSupport configuration length)
    (scaleAdaptiveGlobalJointHighSupport configuration length)
    (scaleAdaptiveGlobalJointLowPatterns configuration length)
    (scaleAdaptiveGlobalJointHighPatterns configuration length)
    (scaleAdaptiveGlobalJointLowEdges configuration length)
    (scaleAdaptiveGlobalJointHighEdges configuration length)

/-- Positive actual common option denominator, including all differing
shell complexities and integer degree products. -/
theorem scaleAdaptiveGlobalJointOptionCount_positive
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ)
    (low_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ configuration.exponents,
      ∀ prime ∈ configuration.highSupport exponent, prime.Prime) :
    0 < scaleAdaptiveGlobalJointOptionCount configuration length := by
  apply scaleAdaptiveSignedJointOptionCount_pos
  · exact scaleAdaptiveGlobalJointLowPatterns_nonempty
      configuration length low_primes
  · exact scaleAdaptiveGlobalJointHighPatterns_nonempty
      configuration length high_primes
  · intro label pattern selected
    exact scaleAdaptiveGlobalJointLowEdges_nonempty
      configuration length label selected
  · intro label pattern selected
    exact scaleAdaptiveGlobalJointHighEdges_nonempty
      configuration length label selected

/-- Every actual joint global option satisfies the true target-or-dummy
support predicate, separately for its chosen color. -/
theorem scaleAdaptiveGlobalJointOptions_supported
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) (lowTargets highTargets : Finset ℕ) :
    WeightedActualPatternOptionsSupported
      (scaleAdaptiveGlobalJointPrimePool configuration length)
      lowTargets highTargets
      (scaleAdaptiveGlobalJointColor configuration length)
      (scaleAdaptiveGlobalJointResidue
        configuration length lowTargets highTargets) := by
  exact scaleAdaptiveSignedJointOptions_supported
    (scaleAdaptiveGlobalJointPrimePool configuration length)
    lowTargets highTargets
    (scaleAdaptiveGlobalJointLowSupport configuration length)
    (scaleAdaptiveGlobalJointHighSupport configuration length)
    (scaleAdaptiveGlobalJointLowPatterns configuration length)
    (scaleAdaptiveGlobalJointHighPatterns configuration length)
    (scaleAdaptiveGlobalJointLowEdges configuration length)
    (scaleAdaptiveGlobalJointHighEdges configuration length)

/-- In particular, the genuine global arrays support the EXACT low/high
fixed-core target families: both colors address large primes and their own
unique typed semiprimes. -/
theorem scaleAdaptiveGlobalJointOriginalTargetOptions_supported
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length parameter cutoff : ℕ) :
    WeightedActualPatternOptionsSupported
      (scaleAdaptiveGlobalJointPrimePool configuration length)
      (scaleAdaptiveGlobalLowTargets length parameter cutoff)
      (scaleAdaptiveGlobalHighTargets length parameter cutoff)
      (scaleAdaptiveGlobalJointColor configuration length)
      (scaleAdaptiveGlobalJointResidue configuration length
        (scaleAdaptiveGlobalLowTargets length parameter cutoff)
        (scaleAdaptiveGlobalHighTargets length parameter cutoff)) :=
  scaleAdaptiveGlobalJointOptions_supported configuration length
    (scaleAdaptiveGlobalLowTargets length parameter cutoff)
    (scaleAdaptiveGlobalHighTargets length parameter cutoff)

/-- Every shell strictly below the fixed core parameter consists eventually
of genuine FRESH primes.  Finite simultaneous assembly preserves exact
integer flooring and never reuses an already selected old-core prime. -/
theorem scaleAdaptiveGlobalJointPrimePool_eventually_fresh
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (parameter : ℕ)
    (inside : ∀ exponent ∈ configuration.exponents,
      2 ^ exponent < parameter) :
    ∀ᶠ length : ℕ in atTop,
      Disjoint (fixedParameterCorePrimes length parameter)
        (scaleAdaptiveGlobalJointPrimePool configuration length) := by
  have all_shells : ∀ᶠ length : ℕ in atTop,
      ∀ exponent ∈ configuration.exponents,
        ∀ label ∈ scaleAdaptiveDyadicPrimeShell length exponent,
          length / parameter < label := by
    exact (Filter.eventually_all_finset configuration.exponents).mpr
      fun exponent selected =>
        scaleAdaptiveDyadicPrimeShell_eventually_fresh
          exponent parameter (inside exponent selected)
  filter_upwards [all_shells] with length fresh
  apply Finset.disjoint_left.mpr
  intro label old selected
  obtain ⟨exponent, in_family, in_shell⟩ := Finset.mem_biUnion.mp
    (scaleAdaptiveGlobalJointPrimePool_subset_shell_union
      configuration length selected)
  have large := fresh exponent in_family label in_shell
  have bounded : label ≤ length / parameter :=
    Nat.le_of_mem_primesLE old
  omega

/-- Exact cardinality of the disjoint ACTUAL global good-prime union. -/
theorem scaleAdaptiveGlobalJointPrimePool_card
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    (scaleAdaptiveGlobalJointPrimePool configuration length).card =
      ∑ exponent ∈ configuration.exponents,
        (scaleAdaptiveGlobalTwoColorGoodShell
          configuration length exponent).card := by
  apply Finset.card_biUnion
  intro first in_first second in_second different
  exact scaleAdaptiveGlobalTwoColorGoodShell_disjoint
    configuration length different

/-- The selected global product truly divides the original physical-shell
prime product.  This transfers any independently proved conductor bound
without replacing actual primes by abstract coefficient densities. -/
theorem scaleAdaptiveGlobalJointPrimePool_product_dvd_shell_product
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (length : ℕ) :
    (∏ prime ∈ scaleAdaptiveGlobalJointPrimePool
      configuration length, prime) ∣
      (∏ prime ∈ configuration.exponents.biUnion
        (scaleAdaptiveDyadicPrimeShell length), prime) := by
  exact Finset.prod_dvd_prod_of_subset _ _ id
    (scaleAdaptiveGlobalJointPrimePool_subset_shell_union
      configuration length)

/-- Sole signed fixed-complexity Green--Tao chooses canonical positive
collision-aware singular factors SIMULTANEOUSLY for every fixed shell and
BOTH square-core supports.  No uniformity in shell complexity is asserted. -/
theorem scaleAdaptiveGlobalJointSingularFamilies_exists_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (exponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (low_primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ highSupport exponent, prime.Prime)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ,
      ∀ exponent ∈ exponents,
        (∀ outcome : ℕ × ℕ,
          0 < lowSingular exponent outcome ∧
            Tendsto
              (adaptiveMixedSignedSingularPartialProduct
                (lowSupport exponent) (2 ^ exponent) outcome)
              atTop (nhds (lowSingular exponent outcome))) ∧
        (∀ outcome : ℕ × ℕ,
          0 < highSingular exponent outcome ∧
            Tendsto
              (adaptiveMixedSignedSingularPartialProduct
                (highSupport exponent) (2 ^ exponent) outcome)
              atTop (nhds (highSingular exponent outcome))) ∧
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              (lowSupport exponent) (highSupport exponent)
                (2 ^ exponent) lower upper
                  (lowSingular exponent) (highSingular exponent) N).card : ℝ) *
                    scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (0 : ℝ)) ∧
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorGoodPrimeLabels
              (lowSupport exponent) (highSupport exponent)
                (2 ^ exponent) lower upper
                  (lowSingular exponent) (highSingular exponent) N).card : ℝ) *
                    scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (1 : ℝ)) := by
  classical
  have witness : ∀ exponent ∈ exponents,
      ∃ lowSingular highSingular : (ℕ × ℕ) → ℝ,
        (∀ outcome : ℕ × ℕ,
          0 < lowSingular outcome ∧
            Tendsto
              (adaptiveMixedSignedSingularPartialProduct
                (lowSupport exponent) (2 ^ exponent) outcome)
              atTop (nhds (lowSingular outcome))) ∧
        (∀ outcome : ℕ × ℕ,
          0 < highSingular outcome ∧
            Tendsto
              (adaptiveMixedSignedSingularPartialProduct
                (highSupport exponent) (2 ^ exponent) outcome)
              atTop (nhds (highSingular outcome))) ∧
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
              (lowSupport exponent) (highSupport exponent)
                (2 ^ exponent) lower upper
                  lowSingular highSingular N).card : ℝ) *
                    scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (0 : ℝ)) ∧
        Tendsto
          (fun N : ℕ =>
            ((scaleAdaptiveSignedTwoColorGoodPrimeLabels
              (lowSupport exponent) (highSupport exponent)
                (2 ^ exponent) lower upper
                  lowSingular highSingular N).card : ℝ) *
                    scaleAdaptivePrimeLabelNormalizedWeight N)
          atTop (nhds (1 : ℝ)) := by
    intro exponent selected
    obtain ⟨lowSingular, highSingular, low_canonical, high_canonical,
      rejected, retained, _usable⟩ :=
      scaleAdaptiveSignedTwoColorCommonGoodPrimePool_of_GTZ
        green_tao (lowSupport exponent) (highSupport exponent)
          (2 ^ exponent) lower upper
            (low_primes exponent selected)
            (high_primes exponent selected)
              lower_nonnegative band_nonempty upper_bounded
    exact ⟨lowSingular, highSingular, low_canonical,
      high_canonical, rejected, retained⟩
  let lowSingular : ℕ → (ℕ × ℕ) → ℝ := fun exponent =>
    if selected : exponent ∈ exponents then
      Classical.choose (witness exponent selected)
    else fun _ => 1
  let highSingular : ℕ → (ℕ × ℕ) → ℝ := fun exponent =>
    if selected : exponent ∈ exponents then
      Classical.choose
        (Classical.choose_spec (witness exponent selected))
    else fun _ => 1
  refine ⟨lowSingular, highSingular, ?_⟩
  intro exponent selected
  dsimp only [lowSingular, highSingular]
  simp only [dif_pos selected]
  exact Classical.choose_spec
    (Classical.choose_spec (witness exponent selected))

/-- One genuine globally selected shell has the true ORIGINAL prime-scale
density `2^{-j}`; rejection of labels bad for either full outcome family
costs zero density. -/
theorem scaleAdaptiveGlobalTwoColorGoodShell_normalized_tendsto
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (exponent : ℕ)
    (rejected : Tendsto
      (fun N : ℕ =>
        ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
          (configuration.lowSupport exponent)
          (configuration.highSupport exponent)
          (2 ^ exponent) configuration.lower configuration.upper
          (configuration.lowSingular exponent)
          (configuration.highSingular exponent) N).card : ℝ) *
            scaleAdaptivePrimeLabelNormalizedWeight N)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalTwoColorGoodShell
          configuration length exponent).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (((2 ^ exponent : ℕ) : ℝ)⁻¹)) := by
  let bad : ℕ → Finset ℕ := fun N =>
    scaleAdaptiveSignedTwoColorRejectedPrimeLabels
      (configuration.lowSupport exponent)
      (configuration.highSupport exponent)
      (2 ^ exponent) configuration.lower configuration.upper
      (configuration.lowSingular exponent)
      (configuration.highSingular exponent) N
  have local_density : Tendsto
      (fun N : ℕ => ((bad N).card : ℝ) *
        Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) := by
    simpa [bad, scaleAdaptivePrimeLabelNormalizedWeight,
      mul_div_assoc] using rejected
  have global_bad := scaleAdaptiveFixedDivisorBadTargets_global_tendsto_zero
    (2 ^ exponent) (pow_pos (by omega : 0 < (2 : ℕ)) exponent)
      bad local_density
  have full := scaleAdaptiveDyadicPrimeShell_global_normalized_tendsto exponent
  have difference : Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveDyadicPrimeShell length exponent).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ) -
          ((bad (length / 2 ^ exponent)).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds (((2 ^ exponent : ℕ) : ℝ)⁻¹)) := by
    simpa using full.sub global_bad
  apply difference.congr'
  exact Filter.Eventually.of_forall fun length => by
    symm
    let N := scaleAdaptiveDyadicPhysicalScale length exponent
    have subset := scaleAdaptiveSignedTwoColorRejectedPrimeLabels_subset_pool
      (configuration.lowSupport exponent)
      (configuration.highSupport exponent)
      (2 ^ exponent) configuration.lower configuration.upper
      (configuration.lowSingular exponent)
      (configuration.highSingular exponent) N
    change
      (((scaleAdaptiveSignedDegreePrimeLabels N \ bad N).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ)) = _
    rw [Finset.card_sdiff_of_subset subset,
      Nat.cast_sub (Finset.card_le_card subset)]
    change
      (((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) -
        ((bad N).card : ℝ)) * Real.log (length : ℝ) / (length : ℝ) = _
    change
      (((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) -
        ((bad N).card : ℝ)) * Real.log (length : ℝ) / (length : ℝ) =
      ((scaleAdaptiveSignedDegreePrimeLabels N).card : ℝ) *
        Real.log (length : ℝ) / (length : ℝ) -
      ((bad N).card : ℝ) * Real.log (length : ℝ) / (length : ℝ)
    ring

/-- The ONE global actual good-prime pool retains the EXACT sum of the
genuine disjoint shell densities.  This rules out a vacuous empty-pool
construction for every nonempty fixed family. -/
theorem scaleAdaptiveGlobalJointPrimePool_normalized_tendsto
    (configuration : ScaleAdaptiveGlobalJointConfiguration)
    (rejected : ∀ exponent ∈ configuration.exponents,
      Tendsto
        (fun N : ℕ =>
          ((scaleAdaptiveSignedTwoColorRejectedPrimeLabels
            (configuration.lowSupport exponent)
            (configuration.highSupport exponent)
            (2 ^ exponent) configuration.lower configuration.upper
            (configuration.lowSingular exponent)
            (configuration.highSingular exponent) N).card : ℝ) *
              scaleAdaptivePrimeLabelNormalizedWeight N)
        atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun length : ℕ =>
        ((scaleAdaptiveGlobalJointPrimePool
          configuration length).card : ℝ) *
            Real.log (length : ℝ) / (length : ℝ))
      atTop (nhds
        (∑ exponent ∈ configuration.exponents,
          (((2 ^ exponent : ℕ) : ℝ)⁻¹))) := by
  have each := tendsto_finsetSum configuration.exponents
    (fun exponent selected =>
      scaleAdaptiveGlobalTwoColorGoodShell_normalized_tendsto
        configuration exponent (rejected exponent selected))
  apply each.congr'
  exact Filter.Eventually.of_forall fun length => by
    dsimp
    rw [scaleAdaptiveGlobalJointPrimePool_card, Nat.cast_sum,
      Finset.sum_mul, Finset.sum_div]

/-- Sole source-faithful signed Green--Tao builds the ENTIRE genuine global
joint option skeleton: one actual fresh prime pool, its true shell density,
one common positive finite denominator, one color and residue per actual
label, both original typed target families, full exact two-hit deficiency
demand, and the complete `1/z` exception coefficient.

The remaining global exponential budgets and true logarithmic conductor are
NOT assumed or asserted by this theorem. -/
theorem scaleAdaptiveGlobalJointActualOptionData_of_GTZ
    (green_tao : HasFixedSignedMixedGreenTaoZieglerPrimeAsymptotics)
    (parameter cutoff : ℕ) (exponents : Finset ℕ)
    (lowSupport highSupport : ℕ → Finset ℕ)
    (lower upper : ℝ)
    (parameter_positive : 0 < parameter)
    (low_primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ lowSupport exponent, prime.Prime)
    (high_primes : ∀ exponent ∈ exponents,
      ∀ prime ∈ highSupport exponent, prime.Prime)
    (inside : ∀ exponent ∈ exponents, 2 ^ exponent < parameter)
    (lower_nonnegative : 0 ≤ lower)
    (band_nonempty : lower < upper)
    (upper_bounded : upper ≤ 1) :
    ∃ lowSingular highSingular : ℕ → (ℕ × ℕ) → ℝ,
      let configuration : ScaleAdaptiveGlobalJointConfiguration :=
        { exponents := exponents
          lowSupport := lowSupport
          highSupport := highSupport
          lower := lower
          upper := upper
          lowSingular := lowSingular
          highSingular := highSingular }
      Tendsto
        (fun length : ℕ =>
          ((scaleAdaptiveGlobalJointPrimePool
            configuration length).card : ℝ) *
              Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds
          (∑ exponent ∈ exponents,
            (((2 ^ exponent : ℕ) : ℝ)⁻¹))) ∧
      Tendsto
        (fun length : ℕ =>
          ((scaleAdaptiveGlobalCompleteTargetExceptions
            length parameter exponents exponents
              lowSupport highSupport lower upper).card : ℝ) *
                Real.log (length : ℝ) / (length : ℝ))
        atTop (nhds ((parameter : ℝ)⁻¹)) ∧
      ∀ᶠ length : ℕ in atTop,
        let R := scaleAdaptiveGlobalJointPrimePool configuration length
        let lowTargets := scaleAdaptiveGlobalLowTargets
          length parameter cutoff
        let highTargets := scaleAdaptiveGlobalHighTargets
          length parameter cutoff
        let exceptions := scaleAdaptiveGlobalCompleteTargetExceptions
          length parameter exponents exponents
            lowSupport highSupport lower upper
        let k := scaleAdaptiveGlobalJointOptionCount configuration length
        let color := scaleAdaptiveGlobalJointColor configuration length
        let residue := scaleAdaptiveGlobalJointResidue
          configuration length lowTargets highTargets
        0 < k ∧
        (∀ prime ∈ R, prime.Prime) ∧
        Disjoint (fixedParameterCorePrimes length parameter) R ∧
        R ⊆ exponents.biUnion (scaleAdaptiveDyadicPrimeShell length) ∧
        lowTargets ⊆ Finset.Icc 1 length ∧
        highTargets ⊆ Finset.Icc 1 length ∧
        exceptions ⊆ Finset.Icc 1 length ∧
        WeightedActualPatternOptionsSupported
          R lowTargets highTargets color residue ∧
        (∀ target ∈ Finset.Icc 1 length, target ∉ exceptions →
          2 ≤ fixedParameterCoreHits length parameter target +
            (if target ∈ lowTargets then 1 else 0) +
            (if target ∈ highTargets then 1 else 0)) := by
  obtain ⟨lowSingular, highSingular, canonical⟩ :=
    scaleAdaptiveGlobalJointSingularFamilies_exists_of_GTZ
      green_tao exponents lowSupport highSupport lower upper
        low_primes high_primes lower_nonnegative
          band_nonempty upper_bounded
  refine ⟨lowSingular, highSingular, ?_⟩
  let configuration : ScaleAdaptiveGlobalJointConfiguration :=
    { exponents := exponents
      lowSupport := lowSupport
      highSupport := highSupport
      lower := lower
      upper := upper
      lowSingular := lowSingular
      highSingular := highSingular }
  change _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · apply scaleAdaptiveGlobalJointPrimePool_normalized_tendsto
    intro exponent selected
    exact (canonical exponent selected).2.2.1
  · exact scaleAdaptiveGlobalCompleteTargetExceptions_normalized_tendsto
      green_tao parameter exponents exponents
        lowSupport highSupport lower upper parameter_positive
          low_primes high_primes lower_nonnegative
            band_nonempty upper_bounded
  · have fresh := scaleAdaptiveGlobalJointPrimePool_eventually_fresh
      configuration parameter inside
    have threshold : ∀ᶠ length : ℕ in atTop,
        parameter ≤ length / parameter := by
      filter_upwards [eventually_ge_atTop (parameter * parameter)] with
        length large
      exact (Nat.le_div_iff_mul_le parameter_positive).mpr large
    filter_upwards [fresh, threshold] with length fresh_core square_threshold
    refine ⟨scaleAdaptiveGlobalJointOptionCount_positive
      configuration length low_primes high_primes, ?_, fresh_core, ?_,
      scaleAdaptiveGlobalLowTargets_subset_interval parameter_positive,
      scaleAdaptiveGlobalHighTargets_subset_interval parameter_positive,
      scaleAdaptiveGlobalCompleteTargetExceptions_subset_interval
        length parameter exponents exponents
          lowSupport highSupport lower upper,
      scaleAdaptiveGlobalJointOriginalTargetOptions_supported
        configuration length parameter cutoff,
      ?_⟩
    · intro prime selected
      exact scaleAdaptiveGlobalJointPrimePool_prime
        configuration length selected
    · exact scaleAdaptiveGlobalJointPrimePool_subset_shell_union
        configuration length
    · exact scaleAdaptiveGlobalCompleteColoredTargetDemand
        exponents exponents lowSupport highSupport lower upper
          parameter_positive square_threshold


end Erdos1139
