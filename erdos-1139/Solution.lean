module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License") for the
attributed Formal Conjectures definitions and statement forms, and the MIT
License for the local proof development.

This module does not import or reference `Challenge`.
-/

public import AdaptiveMixedPublishedGTZCapstone1139
public import AdaptivePrimeProgressionConsequence1139
public import UniformMaxGap1139

@[expose] public section


/-!
# Erdős Problem 1139: proved unconditional gap theorems, bridges, and GTZ-conditional capstone

This module proves the seven unconditional targets in `Erdos1139.Palomar`
(`uniform_maximal_gap`, `limsup_strictly_gt_one`, `cover_crt_interval`,
`seven_square_crt`, `primorial_log_limit`, `limsup_top_of_sparse`, and
`core_classification`) together with the complete Green–Tao–Ziegler
conditional capstone `erdos_1139_of_gtz` and its reverse prime-progression
implication `prime_ap_of_gtz`.
-/

namespace Erdos1139.Palomar

open Finset Filter
open scoped ArithmeticFunction.Omega BigOperators Topology

/-- Selected exponent (2 if squared, 1 otherwise) for a prime in a mixed cover. -/
def selectedPrimeExponent (squared : Finset ℕ) (p : ℕ) : ℕ :=
  if p ∈ squared then 2 else 1

/-- Selected prime-power modulus $p^{\text{selectedPrimeExponent}}$ in the CRT conductor. -/
def selectedPrimePower (squared : Finset ℕ) (p : ℕ) : ℕ :=
  p ^ selectedPrimeExponent squared p

/-- An unrestricted mixed prime/prime-square double cover of $[1, y]$. -/
def UnrestrictedPrimeSquareDoubleCover
    (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) : Prop :=
  (∀ p ∈ P, p.Prime) ∧ squared ⊆ P ∧
    ∀ h ∈ Finset.Icc 1 y,
      2 ≤ (P.filter fun p => a p ≡ h [MOD p]).card +
        (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card

/-- Existence of mixed prime/prime-square double covers with sublinear logarithmic conductor. -/
def HasSublinearUnrestrictedConductorCovers : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ Y₀ : ℕ,
    ∃ (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ),
      Y₀ ≤ y ∧ UnrestrictedPrimeSquareDoubleCover y P squared a ∧
        Real.log
          ((∏ p ∈ P, selectedPrimePower squared p : ℕ) : ℝ)
          ≤ ε * (y : ℝ)

/-- Targets in $[1, y]$ that receive fewer than two total prime/prime-square
residue hits from $(P, \mathrm{squared}, a)$. -/
def deficientTargets (y : ℕ) (P squared : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun h =>
    (P.filter fun p => a p ≡ h [MOD p]).card +
      (squared.filter fun p => a p ≡ h [MOD p ^ 2]).card < 2

/-- Broad prime support of the fixed-parameter core: all primes up to $y / z$. -/
def fixedParameterCorePrimes (y z : ℕ) : Finset ℕ :=
  Nat.primesLE (y / z)

/-- Squared prime support of the fixed-parameter core: primes up to $z$ in the broad support. -/
def fixedParameterCoreSquared (y z : ℕ) : Finset ℕ :=
  Nat.primesLE z ∩ fixedParameterCorePrimes y z

/-- The four target families surviving the fixed-parameter squared-prime core:
the unit $1$, primes, semiprimes $p q$ with $p < z$ and $q > y / z$, and prime
powers $p^e$ ($e \ge 2$) with $z < p \le y / z$. -/
def FixedParameterCoreDeficientType (y z h : ℕ) : Prop :=
  h = 1 ∨ h.Prime ∨
    (∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ p < z ∧ y / z < q ∧ h = p * q) ∨
    (∃ p e : ℕ,
      p.Prime ∧ z < p ∧ p ≤ y / z ∧ 2 ≤ e ∧ h = p ^ e)

/-- Below every sufficiently large height, an interval of length at least
`c * log X`, for one fixed `c > 1`, contains only integers with at least
three prime factors counted with multiplicity. -/
theorem uniform_maximal_gap :
    ∃ c : ℝ, 1 < c ∧
      ∀ᶠ X : ℕ in atTop,
        ∃ N y : ℕ,
          0 < N ∧ N + y ≤ X ∧
          c * Real.log (X : ℝ) ≤ (y : ℝ) ∧
          ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) :=
  _root_.Erdos1139.uniform_maximal_almost_prime_gap_strictly_exceeds_logarithm

/-- Unconditional strict improvement over coefficient $1$ for the literal
Formal Conjectures normalized almost-prime gap limsup. -/
theorem limsup_strictly_gt_one :
    ∃ A : ℝ, 1 < A ∧
      (A : EReal) ≤
        Filter.atTop.limsup
          (fun k : ℕ =>
            (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
               (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
              Real.log ((k : ℝ) + 1) : EReal)) := by
  obtain ⟨r, hr, hcovers⟩ :=
    _root_.Erdos1139.eventual_original_covers_with_strictly_improved_conductor
  exact _root_.Erdos1139.original_normalized_limsup_gt_one_of_eventual_improved_conductor
    r hr hcovers

/-- Every unrestricted mixed prime/prime-square double cover forces an interval
$[N+1, N+y]$ with $Q < N \le 2Q$ on which every integer satisfies $\Omega(N+h) \ge 3$. -/
theorem cover_crt_interval
    {y : ℕ} {P squared : Finset ℕ} {a : ℕ → ℕ}
    (hcover : UnrestrictedPrimeSquareDoubleCover y P squared a) :
    ∃ N : ℕ,
      (∏ p ∈ P, selectedPrimePower squared p) < N ∧
      N ≤ 2 * (∏ p ∈ P, selectedPrimePower squared p) ∧
        ∀ h ∈ Finset.Icc 1 y, 3 ≤ Ω (N + h) :=
  _root_.Erdos1139.unrestricted_square_double_cover_forces_three_factor_interval hcover

/-- Explicit CRT witness $N = 40323$ with conductor $Q = 44100$ for the 7-target
nested-square cover on $\{2, 3, 5, 7\}$. -/
theorem seven_square_crt :
    7 ^ 2 < 40323 ∧ 40323 ≤ 7 ^ 2 + 44100 ∧
      ∀ p ∈ ({2, 3, 5, 7} : Finset ℕ),
        p ^ 2 ∣ 40323 + (if p = 2 then 1 else if p = 3 then 6 else if p = 5 then 2 else 4) :=
  _root_.Erdos1139.seven_square_explicit_crt_shift

/-- By the Prime Number Theorem, the logarithmic primorial conductor satisfies
$\lim_{y \to \infty} \frac{\log(\text{primorial } y)}{y} = 1$. -/
theorem primorial_log_limit :
    Tendsto (fun y : ℕ => Real.log (primorial y : ℝ) / (y : ℝ))
      atTop (𝓝 (1 : ℝ)) :=
  _root_.Erdos1139.original_primorial_log_div_length_tendsto_one

/-- Sublinear logarithmic CRT conductors imply the exact Formal Conjectures
infinite-limsup statement for Erdős Problem 1139. -/
theorem limsup_top_of_sparse
    (hsublinear : HasSublinearUnrestrictedConductorCovers) :
    Filter.atTop.limsup
      (fun k : ℕ =>
        (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
           (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
          Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  _root_.Erdos1139.original_normalized_limsup_top_of_sublinear_unrestricted_conductors hsublinear

/-- Complete conditional proof of the literal Formal Conjectures `erdos_1139`
statement from the published Green–Tao–Ziegler von Mangoldt linear-forms asymptotic. -/
theorem erdos_1139_of_gtz
    (published : _root_.Erdos1139.HasFixedSignedMixedPublishedVonMangoldtAsymptotics) :
    True ↔
      Filter.atTop.limsup
        (fun k : ℕ =>
          (((Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) (k + 1) : ℝ) -
             (Nat.nth (fun n => 0 < n ∧ Ω n ≤ 2) k : ℝ)) /
            Real.log ((k : ℝ) + 1) : EReal)) = ⊤ :=
  ⟨fun _ => _root_.Erdos1139.original_normalized_limsup_top_of_published_von_mangoldt published,
   fun _ => True.intro⟩

/-- Reverse reduction: the published Green–Tao–Ziegler von Mangoldt linear-forms
hypothesis used in the #1139 proof implies arbitrary-length prime progressions. -/
theorem prime_ap_of_gtz
    (published : _root_.Erdos1139.HasFixedSignedMixedPublishedVonMangoldtAsymptotics)
    (length : ℕ) :
    ∃ first difference : ℕ, 0 < difference ∧
      ∀ index < length, (first + index * difference).Prime :=
  _root_.Erdos1139.adaptivePrimeProgression_of_published_von_mangoldt published length

/-- Exact four-family classification of deficient targets after the fixed-parameter
squared-prime core. -/
theorem core_classification
    {y z h : ℕ} (parameter_positive : 0 < z)
    (square_threshold : z ≤ y / z) :
    h ∈ deficientTargets y (fixedParameterCorePrimes y z)
      (fixedParameterCoreSquared y z) (fun _ => 0) ↔
      h ∈ Finset.Icc 1 y ∧ FixedParameterCoreDeficientType y z h :=
  _root_.Erdos1139.fixedParameterCore_deficiency_exact_classification
    parameter_positive square_threshold

end Erdos1139.Palomar
