module

public import AllScaleRealStripLattice433

@[expose] public section


/-!
# Exact manuscript-pattern interface for the actual three-prime major arcs

The Fourier developments analyze affine triples, while the original
major-arc target is stated on coefficient-summed genuine manuscript patterns.
This file connects those objects without discarding either edge cutoff, the
switched support selectors, external-prime conditions, robust label filter,
or the actual strict/weak arbitrary-real label strip.

No positive major-arc or singular-series estimate is assumed or proved.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The actual left outside-prime window, with its true manuscript edge
cutoff and the original switched-support target selector. -/
noncomputable def actualMajorArcLeftPrimeWindow
    (S : Finset ℕ) (b : ℕ → ℕ) (n a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun q =>
    q.Prime ∧ q ∉ S ∧ 2 * (a * q) ≤ n ∧
      switchedHits S b (2 * (a * q)) = 0

/-- The actual center outside-prime window.  Its edge endpoint is
`2 * (2*d*q) ≤ n`, not the unrestricted prime window. -/
noncomputable def actualMajorArcCenterPrimeWindow
    (S : Finset ℕ) (b : ℕ → ℕ) (n d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun q =>
    q.Prime ∧ q ∉ S ∧ 2 * (2 * d * q) ≤ n ∧
      switchedHits S b (2 * (2 * d * q)) = 0

/-- The exact robust prime label window, retaining its genuine residue and
the strict lower / weak upper inequalities for arbitrary real parameters. -/
noncomputable def actualMajorArcLabelPrimeWindow
    (S : Finset ℕ) (b : ℕ → ℕ) (n J residue : ℕ)
    (τ ell : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico (manuscriptRealLabelLower τ n)
    (manuscriptRealLabelUpper τ ell n)).filter fun p =>
      p.Prime ∧ robustResidue S b J p ∧
        p % (∏ s ∈ S, s) = residue

/-- The genuine affine triple family for one pair of actual support
divisors and one prescribed robust label residue. -/
noncomputable def actualMajorArcPrimeTriples
    (S : Finset ℕ) (b : ℕ → ℕ) (n J residue a d : ℕ)
    (τ ell : ℝ) : Finset (ℕ × (ℕ × ℕ)) :=
  ternaryAffineTriples
    (actualMajorArcLeftPrimeWindow S b n a)
    (actualMajorArcCenterPrimeWindow S b n d)
    (actualMajorArcLabelPrimeWindow S b n J residue τ ell)
    a (2 * d)

/-- The actual manuscript-pattern coefficient fiber at one label residue. -/
noncomputable def actualMajorArcPatternFiber
    (S : Finset ℕ) (b : ℕ → ℕ) (n J residue a d : ℕ)
    (τ ell : ℝ) : Finset PrimePatternParameters :=
  (manuscriptPrimePatterns S b n J τ ell).filter fun v =>
    v.1 = (a, d) ∧
      (primePatternEncoding v).2.2 % (∏ s ∈ S, s) = residue

/-- On a genuine robust residue, robustness is constant across its entire
support-product congruence class; the original label window therefore is
exactly the usual residue-filtered, genuine-prime interval. -/
theorem actualMajorArcLabelPrimeWindow_eq_residue_prime_filter
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue : ℕ) (τ ell : ℝ)
    (hresidue : residue ∈ robustResidues S b J) :
    actualMajorArcLabelPrimeWindow S b n J residue τ ell =
      ((Finset.Ico (manuscriptRealLabelLower τ n)
        (manuscriptRealLabelUpper τ ell n)).filter fun p =>
          p % (∏ s ∈ S, s) = residue).filter Nat.Prime := by
  classical
  have hresidue' :
      residue < (∏ s ∈ S, s) ∧ robustResidue S b J residue := by
    obtain ⟨hrange, hrobust⟩ := Finset.mem_filter.mp hresidue
    exact ⟨Finset.mem_range.mp hrange, hrobust⟩
  ext p
  unfold actualMajorArcLabelPrimeWindow
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hinterval, hprime, _, hclass⟩
    exact ⟨⟨hinterval, hclass⟩, hprime⟩
  · rintro ⟨⟨hinterval, hclass⟩, hprime⟩
    refine ⟨hinterval, hprime, ?_, hclass⟩
    have hmod : p % (∏ s ∈ S, s) = residue % (∏ s ∈ S, s) := by
      rw [hclass, Nat.mod_eq_of_lt hresidue'.1]
    exact (robustResidue_iff_of_mod_product_eq
      (S := S) (b := b) (J := J) (r := p) (r' := residue) hmod).mpr
        hresidue'.2

/-- The original arbitrary-real strict/weak robust label window is exactly
the genuine `Ioc floor(τn) floor((τ+ell)n)` prime residue strip used by
the already-audited two-sided shifted minor-arc estimate. -/
theorem actualMajorArcLabelPrimeWindow_eq_exact_Ioc_prime_filter
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue : ℕ) (τ ell : ℝ)
    (hresidue : residue ∈ robustResidues S b J) :
    actualMajorArcLabelPrimeWindow S b n J residue τ ell =
      ((Finset.Ioc (Nat.floor (τ * (n : ℝ)))
        (Nat.floor ((τ + ell) * (n : ℝ)))).filter fun p =>
          p % (∏ s ∈ S, s) = residue).filter Nat.Prime := by
  rw [actualMajorArcLabelPrimeWindow_eq_residue_prime_filter
    S b n J residue τ ell hresidue]
  congr 2
  ext p
  simp only [Finset.mem_Ico, Finset.mem_Ioc,
    manuscriptRealLabelLower, manuscriptRealLabelUpper]
  omega

/-- A genuine coefficient-pattern belongs to its exact residue fiber iff its
two outside primes and its actual encoded label form a member of the fully
filtered affine triple family. -/
theorem actualMajorArcPatternFiber_mem_iff_primeTriple
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue a d q t : ℕ) (τ ell : ℝ)
    (ha : a ∈ (∏ s ∈ S, s).divisors)
    (hd : d ∈ (∏ s ∈ S, s).divisors)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell) :
    ((a, d), (q, t)) ∈
        actualMajorArcPatternFiber S b n J residue a d τ ell ↔
      (q, t, 2 * d * t - a * q) ∈
        actualMajorArcPrimeTriples S b n J residue a d τ ell := by
  classical
  constructor
  · intro hmember
    obtain ⟨hpattern, _, hresidue⟩ := Finset.mem_filter.mp hmember
    obtain ⟨_, _, hqprime, hqoutside, htprime, htoutside⟩ :=
      manuscriptPrimePatterns_admissible hpattern
    obtain ⟨_, hqn, _, htn, _, _⟩ :=
      manuscriptPrimePatterns_three_primes_le hpattern
    obtain ⟨_, hedge, hrobust⟩ :=
      Finset.mem_filter.mp (manuscriptPrimePatterns_encoding_mem hpattern)
    change manuscriptEdge S b n τ ell
      (a * q, 2 * d * t, 2 * d * t - a * q) at hedge
    obtain ⟨hzprime, hequation, hleft, hcenter,
      hleftselector, hcenterselector, hzlower, hzupper, _, _⟩ := hedge
    unfold actualMajorArcPrimeTriples ternaryAffineTriples
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,
      Finset.mem_product.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · unfold actualMajorArcLeftPrimeWindow
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hqprime.one_le, hqn⟩,
          hqprime, hqoutside, hleft, hleftselector⟩
    · unfold actualMajorArcCenterPrimeWindow
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨htprime.one_le, htn⟩,
          htprime, htoutside, hcenter, hcenterselector⟩
    · unfold actualMajorArcLabelPrimeWindow
      apply Finset.mem_filter.mpr
      refine ⟨(mem_manuscriptRealLabelWindow_iff
        τ ell n (2 * d * t - a * q) hτ hell).mpr
          ⟨hzlower, hzupper⟩, hzprime, ?_, ?_⟩
      · exact hrobust
      · exact hresidue
    · simpa [Nat.mul_assoc] using hequation.symm
  · intro htriple
    unfold actualMajorArcPrimeTriples ternaryAffineTriples at htriple
    obtain ⟨hproduct, hequation⟩ := Finset.mem_filter.mp htriple
    obtain ⟨hleft, hremaining⟩ := Finset.mem_product.mp hproduct
    obtain ⟨hcenter, hlabel⟩ := Finset.mem_product.mp hremaining
    unfold actualMajorArcLeftPrimeWindow at hleft
    unfold actualMajorArcCenterPrimeWindow at hcenter
    unfold actualMajorArcLabelPrimeWindow at hlabel
    obtain ⟨hqinterval, hqprime, hqoutside, hleftbound, hleftselector⟩ :=
      Finset.mem_filter.mp hleft
    obtain ⟨htinterval, htprime, htoutside, hcenterbound,
      hcenterselector⟩ := Finset.mem_filter.mp hcenter
    obtain ⟨hzinterval, hzprime, hrobust, hresidue⟩ :=
      Finset.mem_filter.mp hlabel
    have hstrip := (mem_manuscriptRealLabelWindow_iff
      τ ell n (2 * d * t - a * q) hτ hell).mp hzinterval
    unfold actualMajorArcPatternFiber
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl, hresidue⟩
    unfold manuscriptPrimePatterns
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨ha, hd⟩,
        Finset.mem_product.mpr ⟨hqinterval, htinterval⟩⟩,
      hqprime, hqoutside, htprime, htoutside, ?_, hrobust⟩
    change manuscriptEdge S b n τ ell
      (a * q, 2 * d * t, 2 * d * t - a * q)
    refine ⟨hzprime, ?_, hleftbound, hcenterbound,
      hleftselector, hcenterselector, hstrip.1, hstrip.2, ?_, ?_⟩
    · simpa [Nat.mul_assoc] using hequation.symm
    · exact ⟨a, q, (Nat.mem_divisors.mp ha).1, hqprime, rfl⟩
    · exact ⟨d, t, (Nat.mem_divisors.mp hd).1, htprime, rfl⟩

/-- The exact genuine three-von-Mangoldt mass of one actual coefficient
fiber equals the weight of its fully filtered affine prime triples. -/
theorem actualMajorArcPatternFiber_weight_eq_primeTriple_weight
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue a d : ℕ) (τ ell : ℝ)
    (ha : a ∈ (∏ s ∈ S, s).divisors)
    (hd : d ∈ (∏ s ∈ S, s).divisors)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell) :
    (∑ v ∈ actualMajorArcPatternFiber S b n J residue a d τ ell,
      manuscriptPrimePatternVonMangoldtWeight v) =
      ∑ v ∈ actualMajorArcPrimeTriples S b n J residue a d τ ell,
        ternaryAffineVonMangoldtWeight v := by
  classical
  apply Finset.sum_bij
    (fun v _ => (v.2.1, v.2.2, (primePatternEncoding v).2.2))
  · intro v hv
    obtain ⟨_, hcoefficient, _⟩ := Finset.mem_filter.mp hv
    have hfirst : v.1.1 = a := congrArg Prod.fst hcoefficient
    have hsecond : v.1.2 = d := congrArg Prod.snd hcoefficient
    subst a
    subst d
    have h := (actualMajorArcPatternFiber_mem_iff_primeTriple
      S b n J residue v.1.1 v.1.2 v.2.1 v.2.2 τ ell
      ha hd hτ hell).mp (by simpa using hv)
    simpa [primePatternEncoding, primePatternEdge] using h
  · intro v hv w hw heq
    have hvcoefficient := (Finset.mem_filter.mp hv).2.1
    have hwcoefficient := (Finset.mem_filter.mp hw).2.1
    have hq : v.2.1 = w.2.1 :=
      congrArg (fun x : ℕ × (ℕ × ℕ) => x.1) heq
    have ht : v.2.2 = w.2.2 :=
      congrArg (fun x : ℕ × (ℕ × ℕ) => x.2.1) heq
    exact Prod.ext (hvcoefficient.trans hwcoefficient.symm)
      (Prod.ext hq ht)
  · intro v hv
    have hequation : a * v.1 + v.2.2 = (2 * d) * v.2.1 := by
      exact (Finset.mem_filter.mp hv).2
    have hlabel : v.2.2 = 2 * d * v.2.1 - a * v.1 := by omega
    refine ⟨((a, d), (v.1, v.2.1)), ?_, ?_⟩
    · apply (actualMajorArcPatternFiber_mem_iff_primeTriple
        S b n J residue a d v.1 v.2.1 τ ell ha hd hτ hell).mpr
      simpa [← hlabel] using hv
    · change (v.1, v.2.1, 2 * d * v.2.1 - a * v.1) = v
      rw [← hlabel]
  · intro v hv
    rfl

/-- The *original* residue-localized weighted manuscript count partitions
exactly by its two genuine support-divisor coefficients. -/
theorem manuscriptWeightedResidueCount_eq_actualMajorArc_fiber_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue : ℕ) (τ ell : ℝ) :
    manuscriptWeightedResidueCount S b n J τ ell residue =
      ∑ a ∈ (∏ s ∈ S, s).divisors,
        ∑ d ∈ (∏ s ∈ S, s).divisors,
          ∑ v ∈ actualMajorArcPatternFiber
            S b n J residue a d τ ell,
              manuscriptPrimePatternVonMangoldtWeight v := by
  classical
  let F := manuscriptPrimePatterns S b n J τ ell
  let W := ∏ s ∈ S, s
  calc
    manuscriptWeightedResidueCount S b n J τ ell residue =
        ∑ v ∈ F, ∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
          if v.1 = (a, d) ∧
            (primePatternEncoding v).2.2 % W = residue
          then manuscriptPrimePatternVonMangoldtWeight v else 0 := by
      unfold manuscriptWeightedResidueCount
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨hcoefficients, _⟩ :=
        Finset.mem_product.mp (Finset.mem_filter.mp hv).1
      obtain ⟨ha, hd⟩ := Finset.mem_product.mp hcoefficients
      change v.1.1 ∈ W.divisors at ha
      change v.1.2 ∈ W.divisors at hd
      have hinner :
          (∑ d ∈ W.divisors,
            if v.1 = (v.1.1, d) ∧
              (primePatternEncoding v).2.2 % W = residue
            then manuscriptPrimePatternVonMangoldtWeight v else 0) =
              if (primePatternEncoding v).2.2 % W = residue
              then manuscriptPrimePatternVonMangoldtWeight v else 0 := by
        rw [Finset.sum_eq_single v.1.2]
        · simp
        · intro d hd' hne
          have hpair : v.1 ≠ (v.1.1, d) := by
            intro hpair
            exact hne (congrArg Prod.snd hpair).symm
          simp [hpair]
        · intro hnot
          exact (hnot hd).elim
      have houter :
          (∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
            if v.1 = (a, d) ∧
              (primePatternEncoding v).2.2 % W = residue
            then manuscriptPrimePatternVonMangoldtWeight v else 0) =
              ∑ d ∈ W.divisors,
                if v.1 = (v.1.1, d) ∧
                  (primePatternEncoding v).2.2 % W = residue
                then manuscriptPrimePatternVonMangoldtWeight v else 0 := by
        apply Finset.sum_eq_single v.1.1
        · intro a ha' hne
          apply Finset.sum_eq_zero
          intro d hd'
          have hpair : v.1 ≠ (a, d) := by
            intro hpair
            exact hne (congrArg Prod.fst hpair).symm
          simp [hpair]
        · intro hnot
          exact (hnot ha).elim
      exact (houter.trans hinner).symm
    _ = ∑ a ∈ W.divisors, ∑ d ∈ W.divisors,
          ∑ v ∈ F,
            if v.1 = (a, d) ∧
              (primePatternEncoding v).2.2 % W = residue
            then manuscriptPrimePatternVonMangoldtWeight v else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro d hd
      unfold actualMajorArcPatternFiber
      rw [Finset.sum_filter]

/-- Exact coefficient-summed actual prime-triple expression for the original
residue-localized three-von-Mangoldt pattern count. -/
theorem manuscriptWeightedResidueCount_eq_actualMajorArc_primeTriple_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue : ℕ) (τ ell : ℝ)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell) :
    manuscriptWeightedResidueCount S b n J τ ell residue =
      ∑ a ∈ (∏ s ∈ S, s).divisors,
        ∑ d ∈ (∏ s ∈ S, s).divisors,
          ∑ v ∈ actualMajorArcPrimeTriples
            S b n J residue a d τ ell,
              ternaryAffineVonMangoldtWeight v := by
  rw [manuscriptWeightedResidueCount_eq_actualMajorArc_fiber_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  exact actualMajorArcPatternFiber_weight_eq_primeTriple_weight
    S b n J residue a d τ ell ha hd hτ hell

/-- The actual coefficient-specific Fourier cubic: every one of its three
windows consists of genuine primes satisfying the original manuscript
support, edge, robust-residue, and archimedean restrictions. -/
noncomputable def actualMajorArcPrimeCubic
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue a d : ℕ) (τ ell : ℝ) (α : ℝ) : ℂ :=
  ternaryExponentialSum
    (actualMajorArcLabelPrimeWindow S b n J residue τ ell)
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) 1 α *
  ternaryExponentialSum
    (actualMajorArcLeftPrimeWindow S b n a)
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
    (a : ℤ) α *
  ternaryExponentialSum
    (actualMajorArcCenterPrimeWindow S b n d)
    (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
    (-2 * (d : ℤ)) α

/-- Exact prime-only Fourier extraction for a fully filtered, genuine
manuscript coefficient fiber, with the actual three von-Mangoldt weights. -/
theorem actualMajorArcPrimeTriple_weight_eq_fourier_integral
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue a d : ℕ) (τ ell : ℝ) :
    (∑ v ∈ actualMajorArcPrimeTriples S b n J residue a d τ ell,
      ternaryAffineVonMangoldtWeight v) =
        (∫ α in (0 : ℝ)..1,
          actualMajorArcPrimeCubic S b n J residue a d τ ell α).re := by
  let left := actualMajorArcLeftPrimeWindow S b n a
  let center := actualMajorArcCenterPrimeWindow S b n d
  let labels := actualMajorArcLabelPrimeWindow S b n J residue τ ell
  let weight : ℕ → ℂ :=
    fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)
  have hfrequency : (-(2 * d : ℕ) : ℤ) = -2 * (d : ℤ) := by
    push_cast
    ring
  have hfourier := ternary_affine_nat_fourier_identity
    left center labels weight weight weight a (2 * d)
  rw [hfrequency] at hfourier
  have hactual :
      (∫ α in (0 : ℝ)..1,
        actualMajorArcPrimeCubic S b n J residue a d τ ell α) =
          ∑ v ∈ actualMajorArcPrimeTriples
              S b n J residue a d τ ell,
            weight v.1 * weight v.2.1 * weight v.2.2 := by
    change
      (∫ α in (0 : ℝ)..1,
        actualMajorArcPrimeCubic S b n J residue a d τ ell α) =
          ∑ v ∈ ternaryAffineTriples left center labels a (2 * d),
            weight v.1 * weight v.2.1 * weight v.2.2
    rw [← hfourier]
    apply intervalIntegral.integral_congr
    intro α hα
    dsimp [actualMajorArcPrimeCubic, left, center, labels, weight]
    ring
  rw [hactual]
  simp [ternaryAffineVonMangoldtWeight, weight, Complex.mul_re]

/-- The original robust-residue weighted manuscript count is *exactly* the
sum of genuine prime-only coefficient Fourier integrals.  This connects the
actual covering-problem major-arc target to the analytic Fourier machinery
without substituting unweighted lattice points or dropping any edge filter. -/
theorem manuscriptWeightedResidueCount_eq_actualMajorArc_fourier_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue : ℕ) (τ ell : ℝ)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell) :
    manuscriptWeightedResidueCount S b n J τ ell residue =
      ∑ a ∈ (∏ s ∈ S, s).divisors,
        ∑ d ∈ (∏ s ∈ S, s).divisors,
          (∫ α in (0 : ℝ)..1,
            actualMajorArcPrimeCubic
              S b n J residue a d τ ell α).re := by
  rw [manuscriptWeightedResidueCount_eq_actualMajorArc_primeTriple_sum
    S b n J residue τ ell hτ hell]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  exact actualMajorArcPrimeTriple_weight_eq_fourier_integral
    S b n J residue a d τ ell

/-- Every genuinely filtered prime-only manuscript cubic is continuous, so
its complete shifted major/minor decomposition is available without any
integrability or regularity hypothesis. -/
theorem actualMajorArcPrimeCubic_continuous
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue a d : ℕ) (τ ell : ℝ) :
    Continuous (actualMajorArcPrimeCubic
      S b n J residue a d τ ell) := by
  unfold actualMajorArcPrimeCubic ternaryExponentialSum GoldbachChain.e
  fun_prop

/-- Exact major/minor partition for the *original* weighted residue count,
summed over both actual coefficient divisors.  The major region is the
entire genuine shifted complement; no principal-arc positivity or
nonnegativity of the remaining major arcs is assumed. -/
theorem manuscriptWeightedResidueCount_eq_actual_shifted_major_minor_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n J residue P Q : ℕ) (τ ell : ℝ)
    (hτ : 0 ≤ τ) (hell : 0 ≤ ell) :
    manuscriptWeightedResidueCount S b n J τ ell residue =
      (∑ a ∈ (∏ s ∈ S, s).divisors,
        ∑ d ∈ (∏ s ∈ S, s).divisors,
          (∫ α in Set.Ioc (0 : ℝ) 1 \
              ternaryShiftedMinorArcs (∏ s ∈ S, s) P Q,
            actualMajorArcPrimeCubic
              S b n J residue a d τ ell α).re) +
      (∑ a ∈ (∏ s ∈ S, s).divisors,
        ∑ d ∈ (∏ s ∈ S, s).divisors,
          (∫ α in ternaryShiftedMinorArcs
              (∏ s ∈ S, s) P Q,
            actualMajorArcPrimeCubic
              S b n J residue a d τ ell α).re) := by
  rw [manuscriptWeightedResidueCount_eq_actualMajorArc_fourier_sum
    S b n J residue τ ell hτ hell]
  simp_rw [intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    (∑ a ∈ (∏ s ∈ S, s).divisors,
      ∑ d ∈ (∏ s ∈ S, s).divisors,
        (∫ α in Set.Ioc (0 : ℝ) 1,
          actualMajorArcPrimeCubic
            S b n J residue a d τ ell α).re) =
      ∑ a ∈ (∏ s ∈ S, s).divisors,
        ∑ d ∈ (∏ s ∈ S, s).divisors,
          ((∫ α in Set.Ioc (0 : ℝ) 1 \
              ternaryShiftedMinorArcs (∏ s ∈ S, s) P Q,
            actualMajorArcPrimeCubic
              S b n J residue a d τ ell α).re +
          (∫ α in ternaryShiftedMinorArcs
              (∏ s ∈ S, s) P Q,
            actualMajorArcPrimeCubic
              S b n J residue a d τ ell α).re) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro d hd
        rw [ternary_shifted_major_minor_integral_partition
          (∏ s ∈ S, s) P Q
          (actualMajorArcPrimeCubic S b n J residue a d τ ell)
          (actualMajorArcPrimeCubic_continuous
            S b n J residue a d τ ell)]
        exact Complex.add_re _ _
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]


end Erdos689
