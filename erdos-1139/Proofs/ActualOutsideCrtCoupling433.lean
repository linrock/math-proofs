module

public import ActualMajorArcParityCRT433
public import ActualMajorArcSupportSelectorBridge433
public import ActualMajorArcPositivityComposite433

@[expose] public section


/-!
# Exact outside-conductor CRT coupling for the genuine major-arc cells

The existing parity/CRT theorem evaluates the outside character phase over
one fixed switched-support triple.  The actual singular model needs the sum
over *all* genuine compatible support triples and *all* reduced outside
rational numerators.  These identities preserve all three full-modulus unit
conditions, both switched masks, the robust label, and the actual signed
outside Möbius phase.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- Summing the actual outside CRT fibers over every genuine compatible
support triple gives exactly its full cardinality times the true outside
three-prime character phase. -/
theorem actualOutsideCrt_full_compatible_phase_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside numerator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside) :
    (∑ triple ∈ actualMajorArcParityCompatibleFullCellTriples
        S b target a d outside,
      actualMajorArcSquarefreeTriplePhase
        triple.1 triple.2.1 triple.2.2 a d
          ((numerator : ℝ) / outside)) =
      (((actualMajorArcSupportCompatibleCellTriples
        S b target a d).card : ℕ) : ℂ) *
        actualMajorArcGenericPrimeCenterPhase outside a d numerator := by
  classical
  let W := ∏ p ∈ S, p
  let full := actualMajorArcParityCompatibleFullCellTriples
    S b target a d outside
  let support := actualMajorArcSupportCompatibleCellTriples
    S b target a d
  let projection : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun triple =>
    (triple.1 % W, triple.2.1 % W, triple.2.2 % W)
  have hmaps : ∀ triple ∈ full, projection triple ∈ support := by
    intro triple htriple
    exact actualMajorArcParity_full_triple_support_reduction_mem
      S b target a d outside triple hsupport htriple
  calc
    (∑ triple ∈ full,
      actualMajorArcSquarefreeTriplePhase
        triple.1 triple.2.1 triple.2.2 a d
          ((numerator : ℝ) / outside)) =
        ∑ supportTriple ∈ support,
          ∑ triple ∈ full.filter
              (fun triple => projection triple = supportTriple),
            actualMajorArcSquarefreeTriplePhase
              triple.1 triple.2.1 triple.2.2 a d
                ((numerator : ℝ) / outside) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ _supportTriple ∈ support,
          actualMajorArcGenericPrimeCenterPhase
            outside a d numerator := by
      apply Finset.sum_congr rfl
      intro supportTriple htriple
      exact actualMajorArcParity_support_fiber_phase_sum
        S b target a d outside numerator supportTriple
        hsupport houtside hcoprime htriple
    _ = _ := by simp [support]

/-- Summing every reduced rational numerator as well gives the exact
signed genuine outside-conductor Möbius phase for the COMPLETE actual
support-compatible three-cell family. -/
theorem actualOutsideCrt_full_compatible_reduced_phase_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (hcoeff : Nat.Coprime outside (2 * a * d)) :
    (∑ numerator ∈ (Finset.range outside).filter
        (fun numerator => Nat.gcd numerator outside = 1),
      ∑ triple ∈ actualMajorArcParityCompatibleFullCellTriples
          S b target a d outside,
        actualMajorArcSquarefreeTriplePhase
          triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / outside)) =
      (((actualMajorArcSupportCompatibleCellTriples
        S b target a d).card : ℕ) : ℂ) *
        (Nat.totient outside : ℂ) *
          (ArithmeticFunction.moebius outside : ℂ) ^ 3 := by
  simp_rw [actualOutsideCrt_full_compatible_phase_sum
    S b target a d outside _ hsupport houtside hcoprime]
  rw [← Finset.mul_sum,
    actualMajorArcCompositeCenterPhase_sum
      outside a d houtside hcoeff]
  ring

/-- Exact normalization at the TRUE full modulus `W*r`, including the
indispensable `W` from complete support-character projection.  Its outside
factor is the signed rational-center value `μ(r)/φ(r)^2`. -/
theorem actualOutsideCrt_normalized_reduced_phase_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (hcoeff : Nat.Coprime outside (2 * a * d)) :
    ((((∏ p ∈ S, p) : ℕ) : ℂ) *
      (∑ numerator ∈ (Finset.range outside).filter
          (fun numerator => Nat.gcd numerator outside = 1),
        ∑ triple ∈ actualMajorArcParityCompatibleFullCellTriples
            S b target a d outside,
          actualMajorArcSquarefreeTriplePhase
            triple.1 triple.2.1 triple.2.2 a d
              ((numerator : ℝ) / outside))) /
        (Nat.totient ((∏ p ∈ S, p) * outside) : ℂ) ^ 3 =
      ((((actualMajorArcSupportCompatibleCellTriples
          S b target a d).card : ℕ) : ℂ) *
        (((∏ p ∈ S, p) : ℕ) : ℂ) /
          (Nat.totient (∏ p ∈ S, p) : ℂ) ^ 3) *
      ((ArithmeticFunction.moebius outside : ℂ) /
        (Nat.totient outside : ℂ) ^ 2) := by
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hφW : (Nat.totient (∏ p ∈ S, p) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hW).ne'
  have hφoutside : (Nat.totient outside : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr houtside).ne'
  rw [actualOutsideCrt_full_compatible_reduced_phase_sum
    S b target a d outside hsupport houtside hcoprime hcoeff,
    Nat.totient_mul hcoprime,
    actualMajorArcComposite_moebius_cube outside]
  push_cast
  field_simp

/-- The COMPLETE genuine outside-support rational-center coefficient,
after summing all support characters, all selected unit triples, and all
reduced outside numerators, is EXACTLY the manuscript's indispensable
`a*d`-compensated support weight times its signed outside Möbius factor. -/
theorem actualOutsideCrt_compensated_normalized_reduced_phase_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (had : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (hcoeff : Nat.Coprime outside (2 * a * d)) :
    ((((∏ p ∈ S, p) : ℕ) : ℂ) *
      (∑ numerator ∈ (Finset.range outside).filter
          (fun numerator => Nat.gcd numerator outside = 1),
        ∑ triple ∈ actualMajorArcParityCompatibleFullCellTriples
            S b target a d outside,
          actualMajorArcSquarefreeTriplePhase
            triple.1 triple.2.1 triple.2.2 a d
              ((numerator : ℝ) / outside))) /
        (Nat.totient ((∏ p ∈ S, p) * outside) : ℂ) ^ 3 =
      (((a : ℝ) * d *
        actualFixedLabelDoubleCoefficientWeight S target b a d /
          (Nat.totient (∏ p ∈ S, p) : ℝ) : ℝ) : ℂ) *
      ((ArithmeticFunction.moebius outside : ℂ) /
        (Nat.totient outside : ℂ) ^ 2) := by
  rw [actualOutsideCrt_normalized_reduced_phase_sum
    S b target a d outside (fun p hp => (hsupport p hp).1)
      houtside hcoprime hcoeff]
  congr 1
  have hnormal :=
    actualMajorArcSupportCompatibleCellTriples_compensated_normalization
      S b target a d hsupport ha hd had htargetRange htarget hb
  have hcomplex := congrArg (fun value : ℝ => (value : ℂ)) hnormal
  push_cast at hcomplex
  push_cast
  exact hcomplex


end Erdos689
