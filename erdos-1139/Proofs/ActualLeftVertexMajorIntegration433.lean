module

public import ActualLeftVertexMajorSupport433

@[expose] public section


/-!
# Exact `lcm(q,W)` decomposition of the ACTUAL switched prime cubic

Every original manuscript prime window is partitioned exactly into residue
cells for the true common rational/support modulus `L=lcm(q,W)`.  This
preserves both coefficient-sensitive edge cutoffs, all switched exclusions,
the robust prime-label strip, and every prime outside the switched support.
The only nonunit cells consist of actual primes dividing the rational
denominator; their cardinality is explicitly bounded by its distinct prime
factors.  The common modulus lies in the already audited Siegel--Walfisz
range at every logarithmic Farey denominator.  The resulting threefold
expansion is an exact identity for the ORIGINAL prime-only Fourier cubic;
it does not assert an integrated major-arc error estimate.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos689

/-- The true common modulus required to combine a rational Farey
denominator with every switched support congruence. -/
def actualMajorArcLcmResidueModulus
    (S : Finset ℕ) (denominator : ℕ) : ℕ :=
  Nat.lcm denominator (∏ p ∈ S, p)

/-- Both the rational denominator and the full switched support product
divide their ACTUAL common residue modulus. -/
theorem actualMajorArcLcmResidueModulus_divisibility
    (S : Finset ℕ) (denominator : ℕ) :
    denominator ∣ actualMajorArcLcmResidueModulus S denominator ∧
      (∏ p ∈ S, p) ∣ actualMajorArcLcmResidueModulus S denominator := by
  exact ⟨Nat.dvd_lcm_left denominator (∏ p ∈ S, p),
    Nat.dvd_lcm_right denominator (∏ p ∈ S, p)⟩

/-- The actual common rational/support modulus is positive at every genuine
Farey denominator and every prime support. -/
theorem actualMajorArcLcmResidueModulus_pos
    (S : Finset ℕ) (denominator : ℕ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime) :
    0 < actualMajorArcLcmResidueModulus S denominator := by
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  unfold actualMajorArcLcmResidueModulus
  exact Nat.lcm_pos hdenominator hW

/-- Uniform in EVERY actual Farey denominator below the compatible
logarithmic cutoff, the true `lcm(q,W)` lies in the independently proved
Siegel--Walfisz modulus range `(log n)^13`. -/
theorem actualMajorArcLcmResidueModulus_eventually_siegel_walfisz_range
    (S : Finset ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ denominator : ℕ,
        0 < denominator → denominator ≤ compatibleLogMinorCutoff n →
          (actualMajorArcLcmResidueModulus S denominator : ℝ) ≤
            Real.log (n : ℝ) ^ 13 := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  filter_upwards
    [compatibleLogMinorCutoff_fixed_modulus_le_log_pow_thirteen W]
      with n hlog
  intro denominator hdenominator hcutoff
  have hdivisor : Nat.lcm denominator W ∣ denominator * W := by
    apply Nat.lcm_dvd
    · exact dvd_mul_right denominator W
    · exact dvd_mul_left W denominator
  have hupper : Nat.lcm denominator W ≤ denominator * W :=
    Nat.le_of_dvd (Nat.mul_pos hdenominator hW) hdivisor
  have hcast : (Nat.lcm denominator W : ℝ) ≤
      (denominator : ℝ) * W := by
    exact_mod_cast hupper
  change (Nat.lcm denominator W : ℝ) ≤ _
  calc
    (Nat.lcm denominator W : ℝ) ≤ (denominator : ℝ) * W := hcast
    _ ≤ (compatibleLogMinorCutoff n : ℝ) * W := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcutoff) (by positivity)
    _ = (W : ℝ) * (compatibleLogMinorCutoff n : ℝ) := by ring
    _ ≤ _ := hlog

/-- Exact disjoint residue-cell expansion of ANY finite weighted
exponential sum at a positive common modulus. -/
theorem actualMajorArc_exponentialSum_eq_residue_cell_sum
    (window : Finset ℕ) (weight : ℕ → ℂ)
    (frequency : ℤ) (modulus : ℕ) (α : ℝ)
    (hmodulus : 0 < modulus) :
    ternaryExponentialSum window weight frequency α =
      ∑ residue ∈ Finset.range modulus,
        ternaryExponentialSum
          (window.filter fun t => t % modulus = residue)
          weight frequency α := by
  classical
  unfold ternaryExponentialSum
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp [Nat.mod_lt t hmodulus]

/-- Reducing an actual prime parameter modulo `lcm(q,W)` preserves EVERY
switched support hit, including arbitrary actual affine multipliers. -/
theorem actualMajorArcLcm_support_switchedHits_eq
    (S : Finset ℕ) (b : ℕ → ℕ)
    (denominator multiplier t : ℕ) :
    switchedHits S b (multiplier * t) =
      switchedHits S b
        (multiplier * (t % actualMajorArcLcmResidueModulus S denominator)) := by
  let W : ℕ := ∏ p ∈ S, p
  let L := actualMajorArcLcmResidueModulus S denominator
  have hWdiv : W ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  have hprojection : (t % L) % W = t % W :=
    Nat.mod_mod_of_dvd t hWdiv
  have hfirst := switchedHits_mul_eq_of_support_residue
    S b multiplier t (t % W) rfl
  have hsecond := switchedHits_mul_eq_of_support_residue
    S b multiplier (t % L) ((t % L) % W) rfl
  change switchedHits S b (multiplier * t) =
    switchedHits S b (multiplier * (t % L))
  rw [hfirst, hsecond, hprojection]

/-- A genuine prime outside the switched support fails the common-modulus
unit condition IFF it divides the rational denominator.  These are real
finite denominator-prime exceptions, never silently discarded. -/
theorem actualMajorArcOutsidePrime_coprime_lcm_iff
    (S : Finset ℕ) (denominator p : ℕ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hp : p.Prime) (houtside : p ∉ S) :
    Nat.Coprime p (actualMajorArcLcmResidueModulus S denominator) ↔
      ¬ p ∣ denominator := by
  let W : ℕ := ∏ s ∈ S, s
  have hpW : ¬ p ∣ W := by
    intro hdivide
    exact houtside
      (prime_mem_of_dvd_support_product hp hsupport hdivide)
  have hpWcoprime : Nat.Coprime p W :=
    (hp.coprime_iff_not_dvd).mpr hpW
  constructor
  · intro hcoprime hdivide
    have hLdivide : p ∣ actualMajorArcLcmResidueModulus S denominator :=
      dvd_trans hdivide
        (actualMajorArcLcmResidueModulus_divisibility S denominator).1
    exact (hp.coprime_iff_not_dvd.mp hcoprime) hLdivide
  · intro hpdenominator
    have hpcoprime : Nat.Coprime p denominator :=
      (hp.coprime_iff_not_dvd).mpr hpdenominator
    have hproduct : Nat.Coprime p (denominator * W) :=
      Nat.Coprime.mul_right hpcoprime hpWcoprime
    apply hproduct.coprime_dvd_right
    apply Nat.lcm_dvd
    · exact dvd_mul_right denominator W
    · exact dvd_mul_left W denominator

/-- ALL nonunit cells of an actual outside-support prime window consist
of distinct prime divisors of the rational denominator. -/
theorem actualMajorArcOutsidePrime_nonunit_exception_card_le
    (S window : Finset ℕ) (denominator : ℕ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hprimes : ∀ p ∈ window, p.Prime)
    (houtside : ∀ p ∈ window, p ∉ S) :
    (window.filter fun p =>
      ¬ Nat.Coprime p (actualMajorArcLcmResidueModulus S denominator)).card ≤
        denominator.primeFactors.card := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpwindow, hpnonunit⟩ := Finset.mem_filter.mp hp
  have hpprime := hprimes p hpwindow
  have hpdivide : p ∣ denominator := by
    by_contra hnot
    exact hpnonunit
      ((actualMajorArcOutsidePrime_coprime_lcm_iff
        S denominator p hsupport hpprime (houtside p hpwindow)).mpr hnot)
  exact Nat.mem_primeFactors.mpr
    ⟨hpprime, hpdivide, Nat.ne_of_gt hdenominator⟩

/-- An actual fixed-left prime cell preserves its prime/outside-support
tests, genuine original edge cutoff `2*a*t ≤ n`, and switched target. -/
theorem actualMajorArcLeftPrimeWindow_lcm_cell_mem_iff
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n a denominator residue t : ℕ) :
    t ∈ (actualMajorArcLeftPrimeWindow S b n a).filter
        (fun u => u % actualMajorArcLcmResidueModulus S denominator = residue) ↔
      t ∈ Finset.Icc 1 n ∧ t.Prime ∧ t ∉ S ∧
        2 * (a * t) ≤ n ∧ switchedHits S b (2 * (a * t)) = 0 ∧
          t % actualMajorArcLcmResidueModulus S denominator = residue := by
  simp [actualMajorArcLeftPrimeWindow, and_assoc]

/-- An actual fixed-center prime cell preserves its prime/outside-support
tests, genuine original endpoint `4*d*t ≤ n`, and switched target. -/
theorem actualMajorArcCenterPrimeWindow_lcm_cell_mem_iff
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n d denominator residue t : ℕ) :
    t ∈ (actualMajorArcCenterPrimeWindow S b n d).filter
        (fun u => u % actualMajorArcLcmResidueModulus S denominator = residue) ↔
      t ∈ Finset.Icc 1 n ∧ t.Prime ∧ t ∉ S ∧
        2 * (2 * d * t) ≤ n ∧ switchedHits S b (2 * (2 * d * t)) = 0 ∧
          t % actualMajorArcLcmResidueModulus S denominator = residue := by
  simp [actualMajorArcCenterPrimeWindow, and_assoc]

/-- An actual label prime cell preserves its strict/weak real strip, genuine
primality, robust predicate, exact ORIGINAL support residue, and its new
common-modulus residue simultaneously. -/
theorem actualMajorArcLabelPrimeWindow_lcm_cell_mem_iff
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target denominator residue t : ℕ) (τ ell : ℝ) :
    t ∈ (actualMajorArcLabelPrimeWindow S b n J target τ ell).filter
        (fun u => u % actualMajorArcLcmResidueModulus S denominator = residue) ↔
      t ∈ Finset.Ico (manuscriptRealLabelLower τ n)
          (manuscriptRealLabelUpper τ ell n) ∧
        t.Prime ∧ robustResidue S b J t ∧
          t % (∏ p ∈ S, p) = target ∧
            t % actualMajorArcLcmResidueModulus S denominator = residue := by
  classical
  simp [actualMajorArcLabelPrimeWindow, and_assoc]

/-- EXACT full `lcm(q,W)` three-residue expansion of the ORIGINAL
coefficient-specific prime-only manuscript cubic.  Every unit and nonunit
cell, every true support filter, both edge endpoints, the robust label,
and ALL signed incompatible residue triples remain present. -/
theorem actualMajorArcPrimeCubic_eq_lcm_residue_cell_triple_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d denominator : ℕ) (τ ell : ℝ) (α : ℝ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime) :
    actualMajorArcPrimeCubic S b n J target a d τ ell α =
      ∑ labelResidue ∈
          Finset.range (actualMajorArcLcmResidueModulus S denominator),
        ∑ leftResidue ∈
            Finset.range (actualMajorArcLcmResidueModulus S denominator),
          ∑ rightResidue ∈
              Finset.range (actualMajorArcLcmResidueModulus S denominator),
            ternaryExponentialSum
              ((actualMajorArcLabelPrimeWindow S b n J target τ ell).filter
                (fun t =>
                  t % actualMajorArcLcmResidueModulus S denominator =
                    labelResidue))
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) 1 α *
            ternaryExponentialSum
              ((actualMajorArcLeftPrimeWindow S b n a).filter
                (fun t =>
                  t % actualMajorArcLcmResidueModulus S denominator =
                    leftResidue))
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
                (a : ℤ) α *
            ternaryExponentialSum
              ((actualMajorArcCenterPrimeWindow S b n d).filter
                (fun t =>
                  t % actualMajorArcLcmResidueModulus S denominator =
                    rightResidue))
              (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
                (-2 * (d : ℤ)) α := by
  let L := actualMajorArcLcmResidueModulus S denominator
  have hL : 0 < L := actualMajorArcLcmResidueModulus_pos
    S denominator hdenominator hsupport
  unfold actualMajorArcPrimeCubic
  rw [actualMajorArc_exponentialSum_eq_residue_cell_sum
      (actualMajorArcLabelPrimeWindow S b n J target τ ell)
        (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          1 L α hL,
    actualMajorArc_exponentialSum_eq_residue_cell_sum
      (actualMajorArcLeftPrimeWindow S b n a)
        (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          (a : ℤ) L α hL,
    actualMajorArc_exponentialSum_eq_residue_cell_sum
      (actualMajorArcCenterPrimeWindow S b n d)
        (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          (-2 * (d : ℤ)) L α hL]
  dsimp [L]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro labelResidue hlabelResidue
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leftResidue hleftResidue
  rw [← mul_assoc, Finset.mul_sum]


end Erdos689
