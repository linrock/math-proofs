module

public import ThreePrimePatternBridge433
public import AffineDegreeFibers433
public import UniformLocalFactors

@[expose] public section


/-!
# Exact residue-by-residue major-arc target for the three-prime estimate

The Fourier analysis controls each actual robust prime-label residue class.
This file proves that those classes partition the genuine coefficient-summed
von Mangoldt pattern total exactly.  The already proved switched-prime Euler
product then converts a uniform per-residue singular-series main term into
the exact support-uniform global weighted estimate, with only its genuine
factor of two.

The localized major-arc main term remains an explicit mathematical hypothesis;
it is neither introduced as an axiom nor represented as a completed proof.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos689

/-- The genuine weighted coefficient-pattern contribution of one label residue. -/
noncomputable def manuscriptWeightedResidueCount
    (S : Finset ℕ) (b : ℕ → ℕ) (n J : ℕ) (τ ell : ℝ)
    (r : ℕ) : ℝ :=
  ∑ v ∈ manuscriptPrimePatterns S b n J τ ell,
    if (primePatternEncoding v).2.2 % (∏ s ∈ S, s) = r
    then manuscriptPrimePatternVonMangoldtWeight v
    else 0

/-- Actual robust label residues partition the full weighted pattern total exactly. -/
theorem manuscriptWeightedResidueCount_sum_eq_total
    (S : Finset ℕ) (b : ℕ → ℕ) (n J : ℕ) (τ ell : ℝ)
    (hsupport : ∀ s ∈ S, s.Prime) :
    (∑ r ∈ robustResidues S b J,
      manuscriptWeightedResidueCount S b n J τ ell r) =
        manuscriptWeightedPrimePatternCount S b n J τ ell := by
  classical
  unfold manuscriptWeightedResidueCount manuscriptWeightedPrimePatternCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have hedge := manuscriptPrimePatterns_encoding_mem hv
  have hrobust := (Finset.mem_filter.mp hedge).2.2
  have hmember :
      (primePatternEncoding v).2.2 % (∏ s ∈ S, s) ∈
        robustResidues S b J :=
    (mem_robustResidues_mod_iff
      (fun s hs => (hsupport s hs).pos)).mpr hrobust
  rw [Finset.sum_ite_eq]
  simp [hmember]

/-- Whether a robust label occupies either exceptional switched local class. -/
def manuscriptExceptionalLocalClass
    (b : ℕ → ℕ) (r s : ℕ) : Bool :=
  decide ((2 * r) % s = b s % s ∨ (2 * r + b s) % s = 0)

/-- The actual normalized coefficient-summed switched local singular factor. -/
noncomputable def manuscriptLocalSingularFactor
    (S : Finset ℕ) (b : ℕ → ℕ) (r : ℕ) : ℝ :=
  ∏ s ∈ S,
    normalizedSwitchedFactor s (manuscriptExceptionalLocalClass b r s) /
      ((s : ℝ) - 1)

/-- Every actual switched-prime local numerator is strictly positive. -/
theorem normalizedSwitchedFactor_pos_of_large
    {s : ℕ} (hs : 3 < s) (exceptional : Bool) :
    0 < normalizedSwitchedFactor s exceptional := by
  have hlarge : (4 : ℝ) ≤ s := by exact_mod_cast (by omega : 4 ≤ s)
  have hbase : 0 < (s : ℝ) - 1 := by linarith
  have hdenominator : 0 < ((s : ℝ) - 1) ^ 2 := by positivity
  have hthree : (3 : ℝ) < ((s : ℝ) - 1) ^ 2 := by nlinarith
  have hgeneric : (0 : ℝ) < 1 - 3 / ((s : ℝ) - 1) ^ 2 := by
    exact sub_pos.mpr ((div_lt_one hdenominator).mpr hthree)
  exact hgeneric.trans_le (normalized_switched_factor_lower s exceptional)

/-- Every robust residue has a genuinely positive local singular-series weight. -/
theorem manuscriptLocalSingularFactor_pos
    (S : Finset ℕ) (b : ℕ → ℕ) (r : ℕ)
    (hsupport : ∀ s ∈ S, 3 < s) :
    0 < manuscriptLocalSingularFactor S b r := by
  unfold manuscriptLocalSingularFactor
  apply Finset.prod_pos
  intro s hs
  have hlarge : (3 : ℝ) < s := by exact_mod_cast hsupport s hs
  exact div_pos
    (normalizedSwitchedFactor_pos_of_large
      (hsupport s hs) (manuscriptExceptionalLocalClass b r s))
    (by linarith)

/-- The coefficient-summed robust local masses dominate half the true density. -/
theorem robust_local_singular_factor_sum_lower
    (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime ∧ 3 < s) :
    (((robustResidues S b J).card : ℝ) /
      (((∏ s ∈ S, s).totient : ℕ) : ℝ)) / 2 ≤
        ∑ r ∈ robustResidues S b J,
          manuscriptLocalSingularFactor S b r := by
  exact robust_selector_totient_density_lower
    (robustResidues S b J) S hsupport
      (fun r s => manuscriptExceptionalLocalClass b r s)

/-- The remaining true ternary major-arc goal, one robust label residue at a time. -/
def UniformLocalizedThreePrimeMajorArcLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (S : Finset ℕ) (b : ℕ → ℕ) (J : ℕ) (τ ell : ℝ),
      (∀ s ∈ S, s.Prime ∧ 3 < s ∧ J < s ∧ b s % s ≠ 0) →
      0 < τ → 0 < ell → τ + ell < 1 / 10 →
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ r ∈ robustResidues S b J,
            c * manuscriptLocalSingularFactor S b r * ell * (n : ℝ) ^ 2 ≤
              manuscriptWeightedResidueCount S b n J τ ell r

/-- Localized major-arc asymptotics imply the exact global three-prime estimate. -/
theorem uniformWeightedPrimePatternLowerBound_of_localized_major_arcs
    (hmajor : UniformLocalizedThreePrimeMajorArcLowerBound) :
    UniformWeightedManuscriptPrimePatternLowerBound := by
  obtain ⟨c, hc, hmajor⟩ := hmajor
  refine ⟨c / 2, by positivity, ?_⟩
  intro S b J τ ell hsupport hτ hell hstrip
  have hprimes : ∀ s ∈ S, s.Prime := fun s hs => (hsupport s hs).1
  have hlarge : ∀ s ∈ S, s.Prime ∧ 3 < s :=
    fun s hs => ⟨(hsupport s hs).1, (hsupport s hs).2.1⟩
  filter_upwards [hmajor S b J τ ell hsupport hτ hell hstrip] with n hn
  have hlocal := robust_local_singular_factor_sum_lower S b J hlarge
  have hsum :
      (∑ r ∈ robustResidues S b J,
        c * manuscriptLocalSingularFactor S b r * ell * (n : ℝ) ^ 2) ≤
          ∑ r ∈ robustResidues S b J,
            manuscriptWeightedResidueCount S b n J τ ell r := by
    apply Finset.sum_le_sum
    intro r hr
    exact hn r hr
  calc
    c / 2 * (((robustResidues S b J).card : ℝ) /
        (((∏ s ∈ S, s).totient : ℕ) : ℝ)) * ell * (n : ℝ) ^ 2 =
      c * ((((robustResidues S b J).card : ℝ) /
        (((∏ s ∈ S, s).totient : ℕ) : ℝ)) / 2) * ell *
          (n : ℝ) ^ 2 := by ring
    _ ≤ c * (∑ r ∈ robustResidues S b J,
          manuscriptLocalSingularFactor S b r) * ell * (n : ℝ) ^ 2 := by
      gcongr
    _ = ∑ r ∈ robustResidues S b J,
          c * manuscriptLocalSingularFactor S b r * ell * (n : ℝ) ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    _ ≤ ∑ r ∈ robustResidues S b J,
          manuscriptWeightedResidueCount S b n J τ ell r := hsum
    _ = manuscriptWeightedPrimePatternCount S b n J τ ell :=
      manuscriptWeightedResidueCount_sum_eq_total S b n J τ ell hprimes

/-- The original covering conjecture follows from its exact localized
three-prime major arcs and the exact selector-preserving two-form sieve sums. -/
theorem officialStatement_of_localized_major_arcs_and_selector_sieve
    (hmajor : UniformLocalizedThreePrimeMajorArcLowerBound)
    (hsieve : SelectorPreservingTwoPrimeDegreeEstimate) :
    OfficialStatement := by
  exact officialStatement_of_weighted_prime_patterns_and_two_form_degree
    (uniformWeightedPrimePatternLowerBound_of_localized_major_arcs hmajor)
    (fixedModulusTwoFormDegreeBound_of_selector_preserving_estimate hsieve)

end Erdos689

