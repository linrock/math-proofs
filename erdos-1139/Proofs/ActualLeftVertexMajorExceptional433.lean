module

public import ActualLeftVertexMajorFullApprox433
public import ActualMajorArcPositivityArchimedean433
public import ActualRightVertexMajorMixedConductor433

@[expose] public section


/-!
# The full signed exceptional-cell complement

Cells with an incompatible robust label projection or a failed ACTUAL
switched target are identically empty, not merely discarded. Every
remaining nonunit outside-support prime divides the true rational
denominator, giving the sharp `ω(q) log n` exponential bound. The full
retained signed exceptional cubic consequently loses an entire factor of
`n`; the true Farey-arc measure supplies the indispensable further `1/n`.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The true robust label cell vanishes identically if its common-modulus
residue does not project to the ORIGINAL target residue. -/
theorem actualMajorArcLabelCell_eq_zero_of_projection_ne
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target denominator residue : ℕ)
    (τ ell α : ℝ)
    (hincompatible : residue % (∏ p ∈ S, p) ≠ target) :
    ternaryExponentialSum
      ((actualMajorArcLabelPrimeWindow S b n J target τ ell).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          residue))
      (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      1 α = 0 := by
  classical
  have hempty :
      ((actualMajorArcLabelPrimeWindow S b n J target τ ell).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          residue)) = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨t, ht⟩
    obtain ⟨_, _, _, htarget, hresidue⟩ :=
      (actualMajorArcLabelPrimeWindow_lcm_cell_mem_iff
        S b n J target denominator residue t τ ell).mp ht
    have hprojection := Nat.mod_mod_of_dvd t
      (actualMajorArcLcmResidueModulus_divisibility S denominator).2
    exact hincompatible (by simpa [hresidue, htarget] using hprojection)
  simp [hempty, ternaryExponentialSum]

/-- An actual fixed-left prime cell with a failed switched target is
identically empty; the selector is genuinely constant on its `lcm` cell. -/
theorem actualMajorArcLeftCell_eq_zero_of_switched_ne
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n a denominator residue : ℕ) (α : ℝ)
    (hincompatible : switchedHits S b (2 * (a * residue)) ≠ 0) :
    ternaryExponentialSum
      ((actualMajorArcLeftPrimeWindow S b n a).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          residue))
      (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (a : ℤ) α = 0 := by
  classical
  have hempty :
      ((actualMajorArcLeftPrimeWindow S b n a).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          residue)) = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨t, ht⟩
    obtain ⟨_, _, _, _, hmask, hresidue⟩ :=
      (actualMajorArcLeftPrimeWindow_lcm_cell_mem_iff
        S b n a denominator residue t).mp ht
    have hsame := actualMajorArcLcm_support_switchedHits_eq
      S b denominator (2 * a) t
    have hsame' :
        switchedHits S b (2 * (a * t)) =
          switchedHits S b (2 * (a * residue)) := by
      simpa [Nat.mul_assoc, hresidue] using hsame
    exact hincompatible (hsame' ▸ hmask)
  simp [hempty, ternaryExponentialSum]

/-- An actual fixed-center prime cell with a failed original switched
target is identically empty, preserving the true `4*d` multiplier. -/
theorem actualMajorArcCenterCell_eq_zero_of_switched_ne
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n d denominator residue : ℕ) (α : ℝ)
    (hincompatible : switchedHits S b (2 * (2 * d * residue)) ≠ 0) :
    ternaryExponentialSum
      ((actualMajorArcCenterPrimeWindow S b n d).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          residue))
      (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (-2 * (d : ℤ)) α = 0 := by
  classical
  have hempty :
      ((actualMajorArcCenterPrimeWindow S b n d).filter
        (fun t => t % actualMajorArcLcmResidueModulus S denominator =
          residue)) = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨t, ht⟩
    obtain ⟨_, _, _, _, hmask, hresidue⟩ :=
      (actualMajorArcCenterPrimeWindow_lcm_cell_mem_iff
        S b n d denominator residue t).mp ht
    have hsame := actualMajorArcLcm_support_switchedHits_eq
      S b denominator (2 * (2 * d)) t
    have hsame' :
        switchedHits S b (2 * (2 * d * t)) =
          switchedHits S b (2 * (2 * d * residue)) := by
      simpa [Nat.mul_assoc, hresidue] using hsame
    exact hincompatible (hsame' ▸ hmask)
  simp [hempty, ternaryExponentialSum]

/-- Every actual prime window with outside-support parameters has at most
`ω(q)` points in a nonunit common-modulus residue cell, and its weighted
exponential norm is at most `ω(q) log n`. -/
theorem actualMajorArcOutsidePrime_nonunit_cell_exponential_norm_le
    (S window : Finset ℕ) (denominator residue n : ℕ)
    (frequency : ℤ) (α : ℝ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hwindow : window ⊆ Finset.Ioc 0 n)
    (hprimes : ∀ p ∈ window, p.Prime)
    (houtside : ∀ p ∈ window, p ∉ S)
    (hnonunit : ¬ Nat.Coprime residue
      (actualMajorArcLcmResidueModulus S denominator)) :
    ‖ternaryExponentialSum
      (window.filter fun t =>
        t % actualMajorArcLcmResidueModulus S denominator = residue)
      (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      frequency α‖ ≤
        (denominator.primeFactors.card : ℝ) * Real.log n := by
  classical
  let L := actualMajorArcLcmResidueModulus S denominator
  let cell := window.filter fun t => t % L = residue
  have hsub :
      cell ⊆ window.filter fun p => ¬ Nat.Coprime p L := by
    intro p hp
    obtain ⟨hpwindow, hpresidue⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hpwindow, ?_⟩
    intro hunit
    have hmod := (ZMod.coprime_mod_iff_coprime p L).mpr hunit
    exact hnonunit (by simpa [L, hpresidue] using hmod)
  have hcard : cell.card ≤ denominator.primeFactors.card :=
    (Finset.card_le_card hsub).trans
      (actualMajorArcOutsidePrime_nonunit_exception_card_le
        S window denominator hdenominator hsupport hprimes houtside)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  change ‖ternaryExponentialSum cell
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
    frequency α‖ ≤ _
  unfold ternaryExponentialSum
  calc
    ‖∑ k ∈ cell,
        ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
          GoldbachChain.e ((frequency : ℝ) * k * α)‖ ≤
        ∑ k ∈ cell,
          ‖((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
            GoldbachChain.e ((frequency : ℝ) * k * α)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ cell, Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkbound := Finset.mem_Ioc.mp
        (hwindow (Finset.mem_of_mem_filter k hk))
      rw [norm_mul, GoldbachChain.e_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hkbound.1)
          (by exact_mod_cast hkbound.2))
    _ = (cell.card : ℝ) * Real.log (n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast hcard

/-- A positive denominator has at most `q` distinct prime divisors. -/
theorem actualMajorArcDenominator_primeFactors_card_le
    (denominator : ℕ) (hdenominator : 0 < denominator) :
    denominator.primeFactors.card ≤ denominator := by
  have hsub : denominator.primeFactors ⊆ Finset.Icc 1 denominator := by
    intro p hp
    obtain ⟨hprime, hdivisor, _⟩ := Nat.mem_primeFactors.mp hp
    exact Finset.mem_Icc.mpr
      ⟨hprime.pos, Nat.le_of_dvd hdenominator hdivisor⟩
  simpa using Finset.card_le_card hsub

/-- The actual robust label prime window is bounded by `n`, consists
entirely of genuine primes, and contains no switched-support prime. -/
theorem actualMajorArcLabelPrimeWindow_outside_prime_bounded
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target : ℕ) (τ ell : ℝ)
    (hupper : manuscriptRealLabelUpper τ ell n ≤ n) :
    (actualMajorArcLabelPrimeWindow S b n J target τ ell ⊆
      Finset.Ioc 0 n) ∧
      (∀ p ∈ actualMajorArcLabelPrimeWindow S b n J target τ ell,
        p.Prime) ∧
      (∀ p ∈ actualMajorArcLabelPrimeWindow S b n J target τ ell,
        p ∉ S) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hinterval, hprime, _, _⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Ioc.mpr
      ⟨hprime.pos, (Nat.le_of_lt (Finset.mem_Ico.mp hinterval).2).trans
        hupper⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  · intro p hp
    obtain ⟨_, hprime, hrobust, _⟩ := Finset.mem_filter.mp hp
    exact robustResidue_prime_not_mem_support hprime hrobust

/-- Both true edge-prime windows are bounded outside-support prime
families; their indispensable edge cutoffs remain in the windows. -/
theorem actualMajorArcEdgePrimeWindows_outside_prime_bounded
    (S : Finset ℕ) (b : ℕ → ℕ) (n a d : ℕ) :
    (actualMajorArcLeftPrimeWindow S b n a ⊆ Finset.Ioc 0 n) ∧
      (∀ p ∈ actualMajorArcLeftPrimeWindow S b n a, p.Prime) ∧
      (∀ p ∈ actualMajorArcLeftPrimeWindow S b n a, p ∉ S) ∧
      (actualMajorArcCenterPrimeWindow S b n d ⊆ Finset.Ioc 0 n) ∧
      (∀ p ∈ actualMajorArcCenterPrimeWindow S b n d, p.Prime) ∧
      (∀ p ∈ actualMajorArcCenterPrimeWindow S b n d, p ∉ S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hinterval := (Finset.mem_filter.mp hp).1
    have hb := Finset.mem_Icc.mp hinterval
    exact Finset.mem_Ioc.mpr ⟨by omega, hb.2⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.2.1
  · intro p hp
    have hinterval := (Finset.mem_filter.mp hp).1
    have hb := Finset.mem_Icc.mp hinterval
    exact Finset.mem_Ioc.mpr ⟨by omega, hb.2⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.2.1

/-- Every signed actual exceptional triple is either identically zero by
its genuine label/switched selector, or has a denominator-dividing prime
coordinate. Its COMPLETE cubic norm therefore saves one whole factor `n`. -/
theorem actualMajorArcExceptionalPrimeCell_norm_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d denominator : ℕ)
    (τ ell α : ℝ) (triple : ℕ × ℕ × ℕ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hupper : manuscriptRealLabelUpper τ ell n ≤ n)
    (htriple : triple ∈ actualMajorArcLcmExceptionalCellTriples
      S b target a d denominator) :
    ‖actualMajorArcLcmPrimeCellCubic
      S b n J target a d denominator
        triple.1 triple.2.1 triple.2.2 τ ell α‖ ≤
      (denominator.primeFactors.card : ℝ) * Real.log n *
        ((n : ℝ) * Real.log n) ^ 2 := by
  classical
  let L := actualMajorArcLcmResidueModulus S denominator
  let label := ternaryExponentialSum
    ((actualMajorArcLabelPrimeWindow S b n J target τ ell).filter
      (fun t => t % L = triple.1))
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) 1 α
  let left := ternaryExponentialSum
    ((actualMajorArcLeftPrimeWindow S b n a).filter
      (fun t => t % L = triple.2.1))
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (a : ℤ) α
  let right := ternaryExponentialSum
    ((actualMajorArcCenterPrimeWindow S b n d).filter
      (fun t => t % L = triple.2.2))
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (-2 * (d : ℤ)) α
  change ‖label * left * right‖ ≤ _
  by_cases hzero : label * left * right = 0
  · rw [hzero, norm_zero]
    positivity
  have hparts := (mul_ne_zero_iff.mp hzero)
  have hfirst := (mul_ne_zero_iff.mp hparts.1)
  have hlabelne : label ≠ 0 := hfirst.1
  have hleftne : left ≠ 0 := hfirst.2
  have hrightne : right ≠ 0 := hparts.2
  have hprojection : triple.1 % (∏ p ∈ S, p) = target := by
    by_contra hne
    exact hlabelne
      (actualMajorArcLabelCell_eq_zero_of_projection_ne
        S b n J target denominator triple.1 τ ell α hne)
  have hleftmask : switchedHits S b (2 * (a * triple.2.1)) = 0 := by
    by_contra hne
    exact hleftne
      (actualMajorArcLeftCell_eq_zero_of_switched_ne
        S b n a denominator triple.2.1 α hne)
  have hrightmask :
      switchedHits S b (2 * (2 * d * triple.2.2)) = 0 := by
    by_contra hne
    exact hrightne
      (actualMajorArcCenterCell_eq_zero_of_switched_ne
        S b n d denominator triple.2.2 α hne)
  have htriple' :
      triple ∈ (actualMajorArcLcmAllCellTriples S denominator).filter
        (fun t =>
          ¬ actualMajorArcLcmAdmissibleCell S b target a d denominator t) := by
    simpa [actualMajorArcLcmExceptionalCellTriples] using htriple
  have hnot := (Finset.mem_filter.mp htriple').2
  have hnonunit :
      ¬ (Nat.Coprime triple.1 L ∧
        Nat.Coprime triple.2.1 L ∧ Nat.Coprime triple.2.2 L) := by
    intro hunits
    apply hnot
    exact ⟨hprojection, hunits.1, hunits.2.1, hunits.2.2,
      hleftmask, hrightmask⟩
  obtain ⟨hlabelWindow, hlabelPrime, hlabelOutside⟩ :=
    actualMajorArcLabelPrimeWindow_outside_prime_bounded
      S b n J target τ ell hupper
  obtain ⟨hleftWindow, hleftPrime, hleftOutside,
    hrightWindow, hrightPrime, hrightOutside⟩ :=
      actualMajorArcEdgePrimeWindows_outside_prime_bounded
        S b n a d
  have hlabelBound : ‖label‖ ≤ (n : ℝ) * Real.log n :=
    ternary_vonMangoldt_window_exponential_norm_le
      ((actualMajorArcLabelPrimeWindow S b n J target τ ell).filter
        (fun t => t % L = triple.1)) n
        (fun t ht => hlabelWindow (Finset.mem_of_mem_filter t ht)) 1 α
  have hleftBound : ‖left‖ ≤ (n : ℝ) * Real.log n :=
    ternary_vonMangoldt_window_exponential_norm_le
      ((actualMajorArcLeftPrimeWindow S b n a).filter
        (fun t => t % L = triple.2.1)) n
        (fun t ht => hleftWindow (Finset.mem_of_mem_filter t ht))
          (a : ℤ) α
  have hrightBound : ‖right‖ ≤ (n : ℝ) * Real.log n :=
    ternary_vonMangoldt_window_exponential_norm_le
      ((actualMajorArcCenterPrimeWindow S b n d).filter
        (fun t => t % L = triple.2.2)) n
        (fun t ht => hrightWindow (Finset.mem_of_mem_filter t ht))
          (-2 * (d : ℤ)) α
  rcases not_and_or.mp hnonunit with hlabelUnit | hremaining
  · have hexception :
        ‖label‖ ≤ (denominator.primeFactors.card : ℝ) * Real.log n :=
      actualMajorArcOutsidePrime_nonunit_cell_exponential_norm_le
        S (actualMajorArcLabelPrimeWindow S b n J target τ ell)
          denominator triple.1 n 1 α hdenominator hsupport
          hlabelWindow hlabelPrime hlabelOutside hlabelUnit
    rw [norm_mul, norm_mul]
    calc
      ‖label‖ * ‖left‖ * ‖right‖ ≤
          ((denominator.primeFactors.card : ℝ) * Real.log n) *
            ((n : ℝ) * Real.log n) * ((n : ℝ) * Real.log n) := by
        gcongr
      _ = _ := by ring
  · rcases not_and_or.mp hremaining with hleftUnit | hrightUnit
    · have hexception :
          ‖left‖ ≤ (denominator.primeFactors.card : ℝ) * Real.log n :=
        actualMajorArcOutsidePrime_nonunit_cell_exponential_norm_le
          S (actualMajorArcLeftPrimeWindow S b n a)
            denominator triple.2.1 n (a : ℤ) α hdenominator hsupport
            hleftWindow hleftPrime hleftOutside hleftUnit
      rw [norm_mul, norm_mul]
      calc
        ‖label‖ * ‖left‖ * ‖right‖ ≤
            ((n : ℝ) * Real.log n) *
              ((denominator.primeFactors.card : ℝ) * Real.log n) *
              ((n : ℝ) * Real.log n) := by
          gcongr
        _ = _ := by ring
    · have hexception :
          ‖right‖ ≤ (denominator.primeFactors.card : ℝ) * Real.log n :=
        actualMajorArcOutsidePrime_nonunit_cell_exponential_norm_le
          S (actualMajorArcCenterPrimeWindow S b n d)
            denominator triple.2.2 n (-2 * (d : ℤ)) α
            hdenominator hsupport hrightWindow hrightPrime
            hrightOutside hrightUnit
      rw [norm_mul, norm_mul]
      calc
        ‖label‖ * ‖left‖ * ‖right‖ ≤
            ((n : ℝ) * Real.log n) *
              ((n : ℝ) * Real.log n) *
              ((denominator.primeFactors.card : ℝ) * Real.log n) := by
          gcongr
        _ = _ := by ring

/-- The FULL signed exceptional complement, with no term removed, is
bounded by `lcm(q,W)^3 * ω(q) * log n * (n log n)^2`. -/
theorem actualMajorArcExceptionalCellSum_norm_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d denominator : ℕ) (τ ell α : ℝ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hupper : manuscriptRealLabelUpper τ ell n ≤ n) :
    ‖∑ triple ∈ actualMajorArcLcmExceptionalCellTriples
        S b target a d denominator,
      actualMajorArcLcmPrimeCellCubic
        S b n J target a d denominator
          triple.1 triple.2.1 triple.2.2 τ ell α‖ ≤
      ((actualMajorArcLcmResidueModulus S denominator) ^ 3 : ℕ) *
        ((denominator.primeFactors.card : ℝ) * Real.log n *
          ((n : ℝ) * Real.log n) ^ 2) := by
  classical
  let bad := actualMajorArcLcmExceptionalCellTriples
    S b target a d denominator
  let E : ℝ := (denominator.primeFactors.card : ℝ) * Real.log n *
    ((n : ℝ) * Real.log n) ^ 2
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hcard : bad.card ≤
      (actualMajorArcLcmResidueModulus S denominator) ^ 3 := by
    have hfilter : bad.card ≤
        (actualMajorArcLcmAllCellTriples S denominator).card := by
      change
        ((actualMajorArcLcmAllCellTriples S denominator).filter
          (fun t => ¬ actualMajorArcLcmAdmissibleCell
            S b target a d denominator t)).card ≤ _
      exact Finset.card_filter_le _ _
    simpa [actualMajorArcLcmAllCellTriples_card] using hfilter
  change
    ‖∑ triple ∈ bad, actualMajorArcLcmPrimeCellCubic
      S b n J target a d denominator
      triple.1 triple.2.1 triple.2.2 τ ell α‖ ≤ _
  calc
    ‖∑ triple ∈ bad, actualMajorArcLcmPrimeCellCubic
      S b n J target a d denominator
      triple.1 triple.2.1 triple.2.2 τ ell α‖ ≤
        ∑ triple ∈ bad, ‖actualMajorArcLcmPrimeCellCubic
          S b n J target a d denominator
          triple.1 triple.2.1 triple.2.2 τ ell α‖ := norm_sum_le _ _
    _ ≤ ∑ _triple ∈ bad, E := by
      apply Finset.sum_le_sum
      intro triple htriple
      exact actualMajorArcExceptionalPrimeCell_norm_le
        S b n J target a d denominator τ ell α triple
        hdenominator hsupport hupper htriple
    _ = (bad.card : ℝ) * E := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast hcard

/-- Uniformly at ALL Farey denominators `q≤P`, the full signed exceptional
complement is at most `(W*P)^3 * P * log n * (n log n)^2`. -/
theorem actualMajorArcExceptionalCellSum_cutoff_norm_le
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J target a d denominator cutoff : ℕ) (τ ell α : ℝ)
    (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hupper : manuscriptRealLabelUpper τ ell n ≤ n) :
    ‖∑ triple ∈ actualMajorArcLcmExceptionalCellTriples
        S b target a d denominator,
      actualMajorArcLcmPrimeCellCubic
        S b n J target a d denominator
          triple.1 triple.2.1 triple.2.2 τ ell α‖ ≤
      (((∏ p ∈ S, p) * cutoff) ^ 3 : ℕ) *
        ((cutoff : ℝ) * Real.log n *
          ((n : ℝ) * Real.log n) ^ 2) := by
  have hcell := actualMajorArcExceptionalCellSum_norm_le
    S b n J target a d denominator τ ell α
      hdenominator hsupport hupper
  have hmodulus := actualMajorArcError_lcm_triple_cell_card_le
    S denominator cutoff hdenominator hcutoff hsupport
  have hprime := (actualMajorArcDenominator_primeFactors_card_le
    denominator hdenominator).trans hcutoff
  calc
    _ ≤ ((actualMajorArcLcmResidueModulus S denominator) ^ 3 : ℕ) *
      ((denominator.primeFactors.card : ℝ) * Real.log n *
        ((n : ℝ) * Real.log n) ^ 2) := hcell
    _ ≤ _ := by
      gcongr

/-- The entire logarithmic-scale exceptional error, even multiplied by
ANY fixed polynomial in the actual cutoff, is `o(n²)` after the necessary
major-arc `1/n` width has been applied. -/
theorem actualMajorArcExceptional_normalized_polylog_tendsto_zero
    (power : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (compatibleLogMinorCutoff n : ℝ) ^ power *
          (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2))
      atTop (nhds 0) := by
  have hbase :=
    actualMajorArcError_cutoff_power_prime_power_normalized_tendsto_zero
      power
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity) _ hbase
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hsqrtNat : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  have hsqrt : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hsqrtNat
  have hcount : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hdom :
      (n : ℝ) * Real.log (n : ℝ) ^ 3 ≤
        ternaryPrimePowerErrorBound n := by
    unfold ternaryPrimePowerErrorBound
    calc
      (n : ℝ) * Real.log (n : ℝ) ^ 3 ≤
          3 * (n : ℝ) * 1 * 1 * Real.log (n : ℝ) ^ 3 := by
        nlinarith [mul_nonneg (Nat.cast_nonneg n)
          (pow_nonneg hlog 3)]
      _ ≤ 3 * (n : ℝ) * (Nat.sqrt n : ℝ) *
          ((Nat.log 2 n : ℝ) + 1) * Real.log (n : ℝ) ^ 3 := by
        gcongr
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hdom (sq_nonneg (n : ℝ)))
      (by positivity)

/-- At EVERY actual translated Farey anchor, multiplying the FULL signed
exceptional cell complement by its TRUE clipped arc measure restores the
essential `1/n`. The resulting explicit bound is uniform in all genuine
coefficient/residue data and retains every support-dependent constant. -/
theorem actualMajorArcExceptional_shifted_anchor_normalized_eventually
    (S : Finset ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (lower : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      κ * (n : ℝ) ≤ (lower n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (J target a d denominator : ℕ) (τ ell : ℝ),
        0 < denominator → denominator ≤ compatibleLogMinorCutoff n →
        manuscriptRealLabelUpper τ ell n ≤ n →
        ∀ numerator shift : ℤ, ∀ α : ℝ,
          (volume (shiftedFareyAnchorArc (∏ p ∈ S, p)
            (fullyCompatibleFareyCutoff lower n) denominator
            numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal *
            ‖∑ triple ∈ actualMajorArcLcmExceptionalCellTriples
                S b target a d denominator,
              actualMajorArcLcmPrimeCellCubic
                S b n J target a d denominator
                  triple.1 triple.2.1 triple.2.2 τ ell α‖ /
              (n : ℝ) ^ 2 ≤
            (2 / κ) * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 3 *
              (compatibleLogMinorCutoff n : ℝ) ^ 5 *
              (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2) := by
  filter_upwards
    [actualMajorArcArchimedean_shifted_anchor_scaled_volume_eventually
      lower κ hκ hlower (∏ p ∈ S, p)] with n hn
  intro J target a d denominator τ ell hdenominator hcutoff hupper
    numerator shift α
  let W : ℕ := ∏ p ∈ S, p
  let P : ℕ := compatibleLogMinorCutoff n
  let V : ℝ := (volume (shiftedFareyAnchorArc W
    (fullyCompatibleFareyCutoff lower n) denominator
    numerator shift ∩ Set.Ioc (0 : ℝ) 1)).toReal
  let E : ℝ := ‖∑ triple ∈ actualMajorArcLcmExceptionalCellTriples
    S b target a d denominator,
      actualMajorArcLcmPrimeCellCubic
        S b n J target a d denominator
          triple.1 triple.2.1 triple.2.2 τ ell α‖
  have hdenomReal : (1 : ℝ) ≤ (denominator : ℝ) := by
    exact_mod_cast hdenominator
  have hκdenom : κ ≤ κ * (denominator : ℝ) := by
    nlinarith [hκ, hdenomReal]
  have hdrop :
      2 * (P : ℝ) / (κ * denominator) ≤ 2 * (P : ℝ) / κ :=
    div_le_div_of_nonneg_left (by positivity) hκ hκdenom
  have hvolume : V * n ≤ 2 * (P : ℝ) / κ :=
    (hn denominator hdenominator numerator shift).trans hdrop
  have hpoint := actualMajorArcExceptionalCellSum_cutoff_norm_le
    S b n J target a d denominator P τ ell α
      hdenominator hcutoff hsupport hupper
  have hpoint' :
      E ≤ (W : ℝ) ^ 3 * (P : ℝ) ^ 4 * (n : ℝ) ^ 2 *
        Real.log (n : ℝ) ^ 3 := by
    calc
      E ≤ ((W * P) ^ 3 : ℕ) *
        ((P : ℝ) * Real.log n * ((n : ℝ) * Real.log n) ^ 2) := hpoint
      _ = _ := by
        push_cast
        ring
  change V * E / (n : ℝ) ^ 2 ≤ _
  calc
    V * E / (n : ℝ) ^ 2 ≤
      V * ((W : ℝ) ^ 3 * (P : ℝ) ^ 4 * (n : ℝ) ^ 2 *
        Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2 := by
          gcongr
    _ = (V * n) * ((W : ℝ) ^ 3 * (P : ℝ) ^ 4) *
      (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2) := by ring
    _ ≤ (2 * (P : ℝ) / κ) *
      ((W : ℝ) ^ 3 * (P : ℝ) ^ 4) *
      (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- Even after summing the true per-anchor exceptional bound over EVERY
deduplicated shifted Farey center, the ENTIRE signed exceptional family
is `o(n²)`. This uses the exact center count, true common-modulus cells,
denominator-prime sparsity, and the indispensable actual arc width. -/
theorem actualMajorArcExceptional_all_shifted_centers_normalized_tendsto_zero
    (S : Finset ℕ) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto
      (fun n : ℕ =>
        ((shiftedFareyCenterClasses (∏ p ∈ S, p)
          (actualShiftedFareyAnchors (∏ p ∈ S, p)
            (compatibleLogMinorCutoff n))).card : ℝ) *
          ((2 / κ) * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 3 *
            (compatibleLogMinorCutoff n : ℝ) ^ 5 *
            (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2)))
      atTop (nhds 0) := by
  let W : ℕ := ∏ p ∈ S, p
  have hbase :=
    (actualMajorArcExceptional_normalized_polylog_tendsto_zero 7).const_mul
      (8 * (W : ℝ) * ((2 / κ) * (W : ℝ) ^ 3))
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n => by positivity) _
      (by simpa using hbase)
  filter_upwards
    [compatibleLogMinorCutoff_tendsto_atTop.eventually
      (eventually_ge_atTop (1 : ℕ))] with n hn
  let P : ℕ := compatibleLogMinorCutoff n
  have hcard := actualMajorArcError_shifted_center_card_le W P hn
  have hcardReal :
      ((shiftedFareyCenterClasses W
        (actualShiftedFareyAnchors W P)).card : ℝ) ≤
        8 * (W : ℝ) * (P : ℝ) ^ 2 := by
    exact_mod_cast hcard
  calc
    ((shiftedFareyCenterClasses W
      (actualShiftedFareyAnchors W P)).card : ℝ) *
        ((2 / κ) * (W : ℝ) ^ 3 * (P : ℝ) ^ 5 *
          (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2)) ≤
      (8 * (W : ℝ) * (P : ℝ) ^ 2) *
        ((2 / κ) * (W : ℝ) ^ 3 * (P : ℝ) ^ 5 *
          (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2)) := by
        gcongr
    _ = (8 * (W : ℝ) * ((2 / κ) * (W : ℝ) ^ 3)) *
        ((P : ℝ) ^ 7 *
          (((n : ℝ) * Real.log (n : ℝ) ^ 3) / (n : ℝ) ^ 2)) := by ring


end Erdos689
