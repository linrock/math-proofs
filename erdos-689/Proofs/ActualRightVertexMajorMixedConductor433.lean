import ActualRightVertexMajorConductor433
import ActualLeftVertexMajorCellModel433

/-!
# Actual mixed support-conductor and shifted-center cancellation

A center whose rational denominator shares a squared prime with the switched
support is not covered by the positive coprime-denominator subseries.  This
file keeps its true common modulus `L=lcm(q,W)` and its genuine shifted
numerator `h*(L/q)-j*(L/W)+k*L`.  It proves that the complete actual label
residue-cell phase cancels at such a mixed conductor; support-shared signed
centers are not merely dropped.  An integrated global major-arc asymptotic
is still not asserted.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- Integer-frequency additive orthogonality at any nondividing conductor,
including the negative effective numerators of shifted major centers. -/
theorem actualMajorArcMixedConductor_complete_int_phase_sum_zero
    (modulus : ℕ) (frequency : ℤ)
    (hmodulus : 0 < modulus)
    (hfrequency : ¬ (modulus : ℤ) ∣ frequency) :
    (∑ t ∈ Finset.range modulus,
      GoldbachChain.e (((frequency : ℝ) * t) / modulus)) = 0 := by
  simpa [hfrequency] using
    (GoldbachChain.MinorArc.char_orthogonality
      frequency modulus hmodulus.ne')

/-- Exact integer-frequency factorization at every lift of a fixed genuine
support residue.  Unlike a coprime-denominator model, this permits negative
shifted-center numerators and arbitrary mixed support conductors. -/
theorem actualMajorArcMixedConductor_support_lift_int_phase_factor
    (support lift residue : ℕ) (frequency : ℤ)
    (hsupport : 0 < support)
    (hlift : 0 < lift) :
    (∑ t ∈ Finset.range lift,
      GoldbachChain.e
        (((frequency : ℝ) * (residue + support * t)) /
          (support * lift))) =
      GoldbachChain.e
        (((frequency : ℝ) * residue) / (support * lift)) *
        ∑ t ∈ Finset.range lift,
          GoldbachChain.e (((frequency : ℝ) * t) / lift) := by
  have hsreal : (support : ℝ) ≠ 0 := by exact_mod_cast hsupport.ne'
  have hlreal : (lift : ℝ) ≠ 0 := by exact_mod_cast hlift.ne'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [GoldbachChain.e_add]
  congr 1
  field_simp

/-- Exact full-period support-residue-cell reindexing, retaining the ACTUAL
mixed conductor and all of its fixed-residue lifts. -/
theorem actualMajorArcMixedConductor_support_cell_phase_eq_lifts
    (support denominator residue : ℕ) (frequency : ℤ)
    (hsupport : 0 < support)
    (hdivide : support ∣ denominator)
    (hresidue : residue < support) :
    (∑ t ∈ (Finset.range denominator).filter
        (fun t => t % support = residue),
      GoldbachChain.e (((frequency : ℝ) * t) / denominator)) =
      ∑ t ∈ Finset.range (denominator / support),
        GoldbachChain.e
          (((frequency : ℝ) * (residue + support * t)) /
            denominator) := by
  classical
  rw [affine_residue_parameters_eq_progression_image
    denominator support residue hsupport hresidue]
  rw [Finset.sum_image]
  · simp [affineProgressionLength, Nat.mod_eq_zero_of_dvd hdivide]
  · intro x hx y hy hequal
    exact Nat.eq_of_mul_eq_mul_left hsupport
      (Nat.add_left_cancel hequal)

/-- A complete genuine support-residue-cell phase vanishes whenever a prime
divides the mixed conductor's lift but not its actual integer numerator. -/
theorem actualMajorArcMixedConductor_support_cell_phase_sum_zero
    (support denominator residue p : ℕ) (frequency : ℤ)
    (hsupport : 0 < support)
    (hdenominator : 0 < denominator)
    (hdivide : support ∣ denominator)
    (hresidue : residue < support)
    (hprimeLift : p ∣ denominator / support)
    (hfrequency : ¬ (p : ℤ) ∣ frequency) :
    (∑ t ∈ (Finset.range denominator).filter
        (fun t => t % support = residue),
      GoldbachChain.e (((frequency : ℝ) * t) / denominator)) = 0 := by
  let lift := denominator / support
  have hfactor : support * lift = denominator :=
    Nat.mul_div_cancel' hdivide
  have hlift : 0 < lift := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hdenominator hdivide
    · exact hsupport
  have hnot : ¬ (lift : ℤ) ∣ frequency := by
    intro hdivideLift
    apply hfrequency
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hprimeLift)
      hdivideLift
  rw [actualMajorArcMixedConductor_support_cell_phase_eq_lifts
    support denominator residue frequency hsupport hdivide hresidue]
  have hfactorReal : (support : ℝ) * lift = (denominator : ℝ) := by
    exact_mod_cast hfactor
  change
    (∑ t ∈ Finset.range lift,
      GoldbachChain.e
        (((frequency : ℝ) * (residue + support * t)) /
          (denominator : ℝ))) = 0
  rw [← hfactorReal,
    actualMajorArcMixedConductor_support_lift_int_phase_factor
      support lift residue frequency hsupport hlift,
    actualMajorArcMixedConductor_complete_int_phase_sum_zero
      lift frequency hlift hnot, mul_zero]

/-- A squarefree switched support contributes no rational-denominator prime
to the exact scaling factor `lcm(q,W)/q`, even when `q` shares support
primes and their higher powers. -/
theorem actualMajorArcMixedConductor_lcm_div_coprime_denominator
    (support denominator : ℕ)
    (hsquarefree : Squarefree support)
    (hdenominator : 0 < denominator) :
    Nat.Coprime
      (Nat.lcm denominator support / denominator) denominator := by
  let G := Nat.gcd support denominator
  let L := Nat.lcm denominator support
  have hG : 0 < G := Nat.gcd_pos_of_pos_right support hdenominator
  have hdenominatorDivides : denominator ∣ L :=
    Nat.dvd_lcm_left denominator support
  have hGDivides : G ∣ support := Nat.gcd_dvd_left support denominator
  have hLfactor : denominator * (L / denominator) = L :=
    Nat.mul_div_cancel' hdenominatorDivides
  have hGfactor : G * (support / G) = support :=
    Nat.mul_div_cancel' hGDivides
  have hproduct : G * L = denominator * support := by
    simpa [G, L, Nat.gcd_comm] using
      (Nat.gcd_mul_lcm denominator support)
  have hequal :
      (denominator * G) * (L / denominator) =
        (denominator * G) * (support / G) := by
    calc
      (denominator * G) * (L / denominator) =
          G * (denominator * (L / denominator)) := by ring
      _ = G * L := by rw [hLfactor]
      _ = denominator * support := hproduct
      _ = denominator * (G * (support / G)) := by rw [hGfactor]
      _ = (denominator * G) * (support / G) := by ring
  have hquotient : L / denominator = support / G :=
    Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hdenominator hG) hequal
  change Nat.Coprime (L / denominator) denominator
  rw [hquotient]
  exact Nat.coprime_div_gcd_of_squarefree hsquarefree hdenominator.ne'

/-- If a support prime occurs squared in the genuine Farey denominator,
then it necessarily divides the full common-modulus support lift `L/W`.
This keeps every other prime factor of the mixed denominator. -/
theorem actualMajorArcMixedConductor_support_prime_dvd_lcm_support_lift
    (support denominator p : ℕ)
    (hp : p.Prime)
    (hsquarefree : Squarefree support)
    (hpSupport : p ∣ support)
    (hpSquare : p ^ 2 ∣ denominator) :
    p ∣ Nat.lcm denominator support / support := by
  let L := Nat.lcm denominator support
  have hsupportDivides : support ∣ L :=
    Nat.dvd_lcm_right denominator support
  have hpSquareL : p ^ 2 ∣ L := dvd_trans hpSquare
    (Nat.dvd_lcm_left denominator support)
  have hquotientL : support / p ∣ L :=
    dvd_trans (Nat.div_dvd_of_dvd hpSupport) hsupportDivides
  have hcoprime : Nat.Coprime (support / p) p := by
    have h := Nat.coprime_div_gcd_of_squarefree
      hsquarefree hp.ne_zero
    simpa [Nat.gcd_eq_right hpSupport] using h
  have hcoprimePower : Nat.Coprime (p ^ 2) (support / p) :=
    (hcoprime.pow_right 2).symm
  have hproduct : p ^ 2 * (support / p) ∣ L :=
    hcoprimePower.mul_dvd_of_dvd_of_dvd hpSquareL hquotientL
  have hsupportFactor : p * (support / p) = support :=
    Nat.mul_div_cancel' hpSupport
  have hrewrite : p ^ 2 * (support / p) = p * support := by
    rw [pow_two, mul_assoc, hsupportFactor]
  apply (Nat.dvd_div_iff_mul_dvd hsupportDivides).mpr
  simpa [hrewrite, Nat.mul_comm] using hproduct

/-- The genuine shifted numerator `h*(L/q)-j*(L/W)+k*L` remains a unit
at EVERY support prime whose square divides the actual Farey denominator.
Neither the support character shift nor the periodic lift is discarded. -/
theorem actualMajorArcMixedConductor_shifted_numerator_not_dvd
    (support denominator p numerator : ℕ)
    (shift lift : ℤ)
    (hp : p.Prime)
    (hsquarefree : Squarefree support)
    (hdenominator : 0 < denominator)
    (hpSupport : p ∣ support)
    (hpSquare : p ^ 2 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator) :
    ¬ (p : ℤ) ∣
      (numerator : ℤ) *
          ((Nat.lcm denominator support / denominator : ℕ) : ℤ) -
        shift *
          ((Nat.lcm denominator support / support : ℕ) : ℤ) +
        lift * (Nat.lcm denominator support : ℤ) := by
  let L := Nat.lcm denominator support
  have hpDenominator : p ∣ denominator :=
    dvd_trans (by simp : p ∣ p ^ 2) hpSquare
  have hpNumerator : ¬ p ∣ numerator := by
    have hcoprime := hnumerator.coprime_dvd_right hpDenominator
    exact hp.coprime_iff_not_dvd.mp hcoprime.symm
  have hscaleCoprime : Nat.Coprime (L / denominator) denominator :=
    actualMajorArcMixedConductor_lcm_div_coprime_denominator
      support denominator hsquarefree hdenominator
  have hpScale : ¬ p ∣ L / denominator := by
    have hcoprime := hscaleCoprime.coprime_dvd_right hpDenominator
    exact hp.coprime_iff_not_dvd.mp hcoprime.symm
  have hpSupportLift : p ∣ L / support :=
    actualMajorArcMixedConductor_support_prime_dvd_lcm_support_lift
      support denominator p hp hsquarefree hpSupport hpSquare
  have hpCommon : p ∣ L := dvd_trans hpDenominator
    (Nat.dvd_lcm_left denominator support)
  have hpSupportLiftInt : (p : ℤ) ∣ ((L / support : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpSupportLift
  have hpCommonInt : (p : ℤ) ∣ (L : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpCommon
  have hshift : (p : ℤ) ∣ shift * ((L / support : ℕ) : ℤ) :=
    dvd_mul_of_dvd_right hpSupportLiftInt shift
  have hlift : (p : ℤ) ∣ lift * (L : ℤ) :=
    dvd_mul_of_dvd_right hpCommonInt lift
  intro hfrequency
  have hfirst : (p : ℤ) ∣
      (numerator : ℤ) * ((L / denominator : ℕ) : ℤ) := by
    have hrecovery :
        (numerator : ℤ) * ((L / denominator : ℕ) : ℤ) =
          ((numerator : ℤ) * ((L / denominator : ℕ) : ℤ) -
              shift * ((L / support : ℕ) : ℤ) +
              lift * (L : ℤ)) +
            shift * ((L / support : ℕ) : ℤ) - lift * (L : ℤ) := by
      ring
    rw [hrecovery]
    exact dvd_sub (dvd_add hfrequency hshift) hlift
  have hnatural : p ∣ numerator * (L / denominator) := by
    exact_mod_cast hfirst
  rcases hp.dvd_mul.mp hnatural with hfirst | hsecond
  · exact hpNumerator hfirst
  · exact hpScale hsecond

/-- COMPLETE actual fixed-label support-residue-cell cancellation at EVERY
mixed shifted rational center carrying a squared switched-support prime.
The phase uses `L=lcm(q,W)` and its ORIGINAL full signed numerator
`h*(L/q)-j*(L/W)+k*L`; every genuine label lift modulo `W` is present. -/
theorem actualMajorArcMixedConductor_actual_shifted_label_cell_sum_zero
    (S : Finset ℕ)
    (denominator p numerator target : ℕ)
    (shift lift : ℤ)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hdenominator : 0 < denominator)
    (hpSupport : p ∈ S)
    (hpSquare : p ^ 2 ∣ denominator)
    (hnumerator : Nat.Coprime numerator denominator)
    (htarget : target < ∏ s ∈ S, s) :
    (∑ t ∈ (Finset.range
        (actualMajorArcLcmResidueModulus S denominator)).filter
          (fun t => t % (∏ s ∈ S, s) = target),
      GoldbachChain.e
        (((((numerator : ℤ) *
                ((actualMajorArcLcmResidueModulus S denominator /
                  denominator : ℕ) : ℤ) -
              shift *
                ((actualMajorArcLcmResidueModulus S denominator /
                  (∏ s ∈ S, s) : ℕ) : ℤ) +
              lift *
                (actualMajorArcLcmResidueModulus S denominator : ℤ) : ℤ) : ℝ) * t) /
          (actualMajorArcLcmResidueModulus S denominator))) = 0 := by
  let W := ∏ s ∈ S, s
  let L := actualMajorArcLcmResidueModulus S denominator
  have hW : 0 < W := Finset.prod_pos fun s hs => (hsupport s hs).pos
  have hL : 0 < L := actualMajorArcLcmResidueModulus_pos
    S denominator hdenominator hsupport
  have hWsquare : Squarefree W :=
    Sieve.prodDistinctPrimes_squarefree S hsupport
  have hp : p.Prime := hsupport p hpSupport
  have hpW : p ∣ W :=
    Finset.dvd_prod_of_mem (fun s : ℕ => s) hpSupport
  have hWdiv : W ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S denominator).2
  have hpLift : p ∣ L / W :=
    actualMajorArcMixedConductor_support_prime_dvd_lcm_support_lift
      W denominator p hp hWsquare hpW hpSquare
  have hnot : ¬ (p : ℤ) ∣
      (numerator : ℤ) * ((L / denominator : ℕ) : ℤ) -
        shift * ((L / W : ℕ) : ℤ) + lift * (L : ℤ) :=
    actualMajorArcMixedConductor_shifted_numerator_not_dvd
      W denominator p numerator shift lift hp hWsquare
        hdenominator hpW hpSquare hnumerator
  exact actualMajorArcMixedConductor_support_cell_phase_sum_zero
    W L target p
      ((numerator : ℤ) * ((L / denominator : ℕ) : ℤ) -
        shift * ((L / W : ℕ) : ℤ) + lift * (L : ℤ))
      hW hL hWdiv htarget hpLift hnot

#print axioms Erdos689.actualMajorArcMixedConductor_complete_int_phase_sum_zero
#print axioms Erdos689.actualMajorArcMixedConductor_support_lift_int_phase_factor
#print axioms Erdos689.actualMajorArcMixedConductor_support_cell_phase_eq_lifts
#print axioms Erdos689.actualMajorArcMixedConductor_support_cell_phase_sum_zero
#print axioms Erdos689.actualMajorArcMixedConductor_lcm_div_coprime_denominator
#print axioms Erdos689.actualMajorArcMixedConductor_support_prime_dvd_lcm_support_lift
#print axioms Erdos689.actualMajorArcMixedConductor_shifted_numerator_not_dvd
#print axioms Erdos689.actualMajorArcMixedConductor_actual_shifted_label_cell_sum_zero

end Erdos689
