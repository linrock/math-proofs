import ActualMajorArcCenterReindex433
import TernaryMajorArcCompletion433
import ActualMajorArcExceptionClosure433
import ActualMajorArcGlobalStrata433

/-!
# Actual canonical-center phase and original-anchor orbit bridge

Every actual canonical widest center in a support-free conductor stratum
has exactly that original denominator.  Its normalized real representative
differs from the corresponding reduced-numerator/support-shift Farey center
by an integer, so the COMPLETE signed selected-unit anchor coefficient is
unchanged.  Consequently the exact deduplicated real-center stratum has the
same signed phase sum as the full original reduced-numerator/shift orbit.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Erdos689

/-- The canonical normalized REAL representative of `h/q-j/W` differs
from the actual signed shifted rational center by an INTEGER, retaining the
correct original support-character sign and denominator. -/
theorem actualMajorArcCenterPhaseBridge_normalized_eq_shifted_add_int
    (support denominator numerator shift : ℕ)
    (hsupport : 0 < support)
    (hdenominator : 0 < denominator)
    (hshift : shift < support) :
    ∃ period : ℤ,
      actualMajorArcCenterReindexNormalizedCenter
          support denominator numerator
            (actualMajorArcCenterReindexNegShift support shift) =
        ((numerator : ℝ) / denominator -
          (shift : ℝ) / support) + (period : ℝ) := by
  let negative := actualMajorArcCenterReindexNegShift support shift
  let correction : ℕ := if shift = 0 then 0 else 1
  let total := numerator * support + negative * denominator
  let common := denominator * support
  let quotient := total / common
  have hsign : negative + shift = correction * support := by
    by_cases hzero : shift = 0
    · simp [negative, correction,
        actualMajorArcCenterReindexNegShift, hzero]
    · have hpositive : 0 < shift := Nat.pos_of_ne_zero hzero
      have hless : support - shift < support := by omega
      simp [negative, correction,
        actualMajorArcCenterReindexNegShift, hzero,
        Nat.mod_eq_of_lt hless]
      omega
  have hdivision : total % common + common * quotient = total :=
    Nat.mod_add_div total common
  have hsignReal : (negative : ℝ) + shift =
      (correction : ℝ) * support := by exact_mod_cast hsign
  have hdivisionReal :
      ((total % common : ℕ) : ℝ) +
        (common : ℝ) * (quotient : ℝ) = (total : ℝ) := by
    exact_mod_cast hdivision
  refine ⟨(correction : ℤ) - (quotient : ℤ), ?_⟩
  change (((total % common : ℕ) : ℝ) / (common : ℝ)) =
    ((numerator : ℝ) / denominator - (shift : ℝ) / support) +
      (((correction : ℤ) - (quotient : ℤ) : ℤ) : ℝ)
  push_cast
  dsimp [total, common] at hdivisionReal
  push_cast at hdivisionReal
  dsimp [total, common]
  push_cast
  field_simp
  linear_combination hdivisionReal + (denominator : ℝ) * hsignReal

/-- The COMPLETE actual signed selected-unit canonical coefficient at a
REAL center, zero only outside the actual finite center family. -/
noncomputable def actualMajorArcCenterPhaseBridgeCanonicalCoefficient
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff : ℕ) (center : ℝ) : ℂ :=
  if hcenter : center ∈ shiftedFareyCenterClasses
      (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) then
    actualCenterCouplingAnchorCoefficient S b target a d
      (actualMajorArcGlobalCanonicalWidestAnchor
        (∏ p ∈ S, p) cutoff fareyCutoff ⟨center, hcenter⟩)
  else 0

/-- At the exact normalized canonical real center, the actual canonical
widest selected-unit coefficient equals the ORIGINAL raw Farey anchor
coefficient with numerator `h` and support shift `j`. The true original
denominator, signed integer lift, and all three switched selectors remain. -/
theorem actualMajorArcCenterPhaseBridge_canonical_coefficient_eq_raw
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff denominator numerator shift : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator (∏ p ∈ S, p))
    (hnumerator : Nat.Coprime numerator denominator)
    (hshift : shift < ∏ p ∈ S, p) :
    actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff
        (actualMajorArcCenterReindexNormalizedCenter
          (∏ p ∈ S, p) denominator numerator
            (actualMajorArcCenterReindexNegShift
              (∏ p ∈ S, p) shift)) =
      actualCenterCouplingAnchorCoefficient S b target a d
        (denominator, (numerator : ℤ), (shift : ℤ)) := by
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  let center := actualMajorArcCenterReindexNormalizedCenter
    W denominator numerator
      (actualMajorArcCenterReindexNegShift W shift)
  have hcenterMem :=
    actualMajorArcCenterReindex_normalized_center_mem_actual_classes
      W cutoff denominator numerator
        (actualMajorArcCenterReindexNegShift W shift)
        hW hdenominator hcutoff hnumerator
  let attached : ActualMajorArcGlobalCenter W cutoff :=
    ⟨center, hcenterMem⟩
  obtain ⟨other, hother, hotherDenominator, hotherCenter⟩ :=
    actualMajorArcCenterReindex_normalized_center_actual_anchor
      W cutoff denominator numerator
        (actualMajorArcCenterReindexNegShift W shift)
        hW hdenominator hcutoff hnumerator
  have hcanonicalDenominator :
      (actualMajorArcGlobalCanonicalWidestAnchor
        W cutoff fareyCutoff attached).1 = denominator := by
    rw [← hotherDenominator]
    apply actualConductorDedup_canonical_denominator_eq_support_free
      W cutoff fareyCutoff attached other hW hother
    · exact hotherCenter
    · rw [hotherDenominator]
      exact hcoprime
  obtain ⟨period, hperiod⟩ :=
    actualMajorArcCenterPhaseBridge_normalized_eq_shifted_add_int
      W denominator numerator shift hW hdenominator hshift
  unfold actualMajorArcCenterPhaseBridgeCanonicalCoefficient
  rw [dif_pos hcenterMem]
  apply ternaryMajorArc_anchor_coefficient_eq_of_periodic_centers
    S b target a d
      (actualMajorArcGlobalCanonicalWidestAnchor
        W cutoff fareyCutoff attached)
      (denominator, (numerator : ℤ), (shift : ℤ)) period
  · exact hcanonicalDenominator
  · rw [hcanonicalDenominator]
    exact hdenominator
  · exact hsupport
  · rw [(actualMajorArcGlobalCanonicalWidestAnchor_spec
      W cutoff fareyCutoff attached).2.1]
    change center =
      ((numerator : ℝ) / denominator - (shift : ℝ) / W) +
        (period : ℝ)
    exact hperiod

/-- EXACT genuine support-free conductor stratum phase sum. The ORIGINAL
deduplicated canonical selected-unit coefficient, summed ONCE over actual
real centers in `[0,1)`, equals the full original reduced-numerator / true
support-character anchor orbit. No support shift or duplicate real center
is omitted. -/
theorem actualMajorArcCenterPhaseBridge_actual_stratum_coefficient_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator (∏ p ∈ S, p)) :
    (∑ center ∈ actualMajorArcCenterReindexActualStratum
        (∏ p ∈ S, p) cutoff denominator,
      actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff center) =
      ∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range (∏ p ∈ S, p),
          actualCenterCouplingAnchorCoefficient S b target a d
            (denominator, (numerator : ℤ), (shift : ℤ)) := by
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  rw [actualMajorArcCenterReindex_actual_stratum_sum
    W cutoff denominator
      (actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff)
      hW hdenominator hcutoff hcoprime]
  apply Finset.sum_congr rfl
  intro numerator hnumerator
  apply Finset.sum_congr rfl
  intro shift hshift
  exact actualMajorArcCenterPhaseBridge_canonical_coefficient_eq_raw
    S b target a d cutoff fareyCutoff denominator numerator shift
    hsupport hdenominator hcutoff hcoprime
      (Finset.mem_filter.mp hnumerator).2
      (Finset.mem_range.mp hshift)

/-- At an ODD support-free denominator, the ACTUAL deduplicated real-center
stratum coefficient is EXACTLY the compensated signed outside factor
`a*d*actualWeight/φ(W) * μ(q)/φ(q)^2`. -/
theorem actualMajorArcCenterPhaseBridge_actual_odd_stratum_factor
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (had : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (houtside : 0 < outside)
    (hcutoff : outside ≤ cutoff)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (hcoeff : Nat.Coprime outside (2 * a * d)) :
    (∑ center ∈ actualMajorArcCenterReindexActualStratum
        (∏ p ∈ S, p) cutoff outside,
      actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff center) =
      (((a : ℂ) * d *
        (actualFixedLabelDoubleCoefficientWeight S target b a d : ℂ)) /
          (Nat.totient (∏ p ∈ S, p) : ℂ)) *
        ((ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2) := by
  rw [actualMajorArcCenterPhaseBridge_actual_stratum_coefficient_sum
    S b target a d cutoff fareyCutoff outside
    (fun p hp => (hsupport p hp).1)
      houtside hcutoff hcoprime.symm]
  exact ternaryMajorArc_actual_odd_anchor_coefficient_sum
    S b target a d outside hsupport ha hd had
      htargetRange htarget hb houtside hcoprime hcoeff

/-- At the genuine original PARITY-DOUBLED conductor `2*r`, the ACTUAL
deduplicated real-center coefficient has the SAME signed outside factor,
with its original `2*r` Farey denominator still unreplaced. -/
theorem actualMajorArcCenterPhaseBridge_actual_even_stratum_factor
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff outside : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (had : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (houtside : 0 < outside)
    (hcutoff : 2 * outside ≤ cutoff)
    (hodd : Nat.Coprime 2 outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (hcoeff : Nat.Coprime outside (2 * a * d)) :
    (∑ center ∈ actualMajorArcCenterReindexActualStratum
        (∏ p ∈ S, p) cutoff (2 * outside),
      actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff center) =
      (((a : ℂ) * d *
        (actualFixedLabelDoubleCoefficientWeight S target b a d : ℂ)) /
          (Nat.totient (∏ p ∈ S, p) : ℂ)) *
        ((ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2) := by
  have hWtwo : Nat.Coprime (∏ p ∈ S, p) 2 :=
    oddSupportDivisor_coprime_two
      S (∏ p ∈ S, p) hsupport (dvd_refl _)
  have hWdouble : Nat.Coprime (∏ p ∈ S, p) (2 * outside) :=
    (Nat.coprime_mul_iff_right).mpr ⟨hWtwo, hcoprime⟩
  rw [actualMajorArcCenterPhaseBridge_actual_stratum_coefficient_sum
    S b target a d cutoff fareyCutoff (2 * outside)
    (fun p hp => (hsupport p hp).1)
      (by omega) hcutoff hWdouble.symm]
  exact ternaryMajorArc_actual_doubled_anchor_coefficient_sum
    S b target a d outside hsupport ha hd had
      htargetRange htarget hb houtside hodd hcoprime hcoeff

/-- Even when an individual actual center contribution is nonzero, EVERY
support-free deduplicated real-center stratum cancels completely at a
noncoprime support-divisor pair. The robust label excludes all compatible
support triples; no signed center was discarded. -/
theorem actualMajorArcCenterPhaseBridge_noncoprime_stratum_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hnotcoprime : ¬ Nat.Coprime a d)
    (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator (∏ p ∈ S, p)) :
    (∑ center ∈ actualMajorArcCenterReindexActualStratum
        (∏ p ∈ S, p) cutoff denominator,
      actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff center) = 0 := by
  rw [actualMajorArcCenterPhaseBridge_actual_stratum_coefficient_sum
    S b target a d cutoff fareyCutoff denominator
    hsupport hdenominator hcutoff hcoprime]
  apply Finset.sum_eq_zero
  intro numerator hnumerator
  rw [ternaryMajorArc_anchor_coefficient_support_shift_sum
    S b target a d denominator numerator hdenominator hsupport,
    actualConductorDedup_full_triples_empty_of_not_coprime
      S b target a d denominator hsupport ha hd htarget hnotcoprime]
  simp

/-- The original genuinely CLIPPED complex canonical smooth contribution
at an actual real center; noncenters are totalized by zero. -/
noncomputable def actualMajorArcCenterPhaseBridgeCanonicalIntegral
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ) (center : ℝ) : ℂ :=
  if hcenter : center ∈ shiftedFareyCenterClasses
      (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) then
    ∫ α in Set.Ioc (0 : ℝ) 1 ∩
      shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff) center,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff ⟨center, hcenter⟩) α
  else 0

/-- Genuine half-open-circle boundary pairing: the actual center zero
includes its DISTINCT clipped center-one partner exactly once. -/
noncomputable def actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ) (center : ℝ) : ℂ :=
  if center = 0 then
    actualMajorArcCenterPhaseBridgeCanonicalIntegral
      S b n target a d cutoff fareyCutoff τ ell 0 +
    actualMajorArcCenterPhaseBridgeCanonicalIntegral
      S b n target a d cutoff fareyCutoff τ ell 1
  else actualMajorArcCenterPhaseBridgeCanonicalIntegral
    S b n target a d cutoff fareyCutoff τ ell center

/-- The real part of the EXACT complex boundary-paired actual canonical
integral is precisely the genuine paired real weight in the global center
partition, including the distinct `0/1` principal representatives. -/
theorem actualMajorArcCenterPhaseBridge_paired_real_eq_global
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell center : ℝ) :
    (actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
      S b n target a d cutoff fareyCutoff τ ell center).re =
      actualMajorArcGlobalStrataPairedCanonicalWeight
        S b n target a d cutoff fareyCutoff τ ell center := by
  classical
  have hsingle (value : ℝ) :
      (actualMajorArcCenterPhaseBridgeCanonicalIntegral
        S b n target a d cutoff fareyCutoff τ ell value).re =
        actualMajorArcGlobalStrataCanonicalWeight
          S b n target a d cutoff fareyCutoff τ ell value := by
    by_cases hcenter : value ∈ shiftedFareyCenterClasses
        (∏ p ∈ S, p)
        (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff)
    · simp [actualMajorArcCenterPhaseBridgeCanonicalIntegral,
        actualMajorArcGlobalStrataCanonicalWeight, hcenter]
    · simp [actualMajorArcCenterPhaseBridgeCanonicalIntegral,
        actualMajorArcGlobalStrataCanonicalWeight, hcenter]
  unfold actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
    actualMajorArcGlobalStrataPairedCanonicalWeight
  split
  · simp [hsingle]
  · exact hsingle center

/-- The two DISTINCT genuinely clipped canonical boundary centers glue to
ONE complete symmetric principal singular integral, with their common
actual selected-unit coefficient.  No principal mass is doubled. -/
theorem actualMajorArcCenterPhaseBridge_boundary_pair_eq_signed_symmetric
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff) (hfarey : 0 < fareyCutoff) :
    actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
        S b n target a d cutoff fareyCutoff τ ell 0 =
      actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff 0 *
        (∫ β in Set.Icc
          (-(1 / ((fareyCutoff : ℝ) + 1)))
          (1 / ((fareyCutoff : ℝ) + 1)),
          actualMajorArcArchimedeanSmoothCubic
            a d n τ ell β) := by
  classical
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hzeroMem := actualMajorArcBoundary_zero_center_mem
    W cutoff hW hcutoff
  have honeMem := actualMajorArcBoundary_one_center_mem
    W cutoff hW hcutoff
  let zeroCenter : ActualMajorArcGlobalCenter W cutoff :=
    ⟨0, hzeroMem⟩
  let oneCenter : ActualMajorArcGlobalCenter W cutoff :=
    ⟨1, honeMem⟩
  unfold actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
  rw [if_pos rfl]
  unfold actualMajorArcCenterPhaseBridgeCanonicalIntegral
    actualMajorArcCenterPhaseBridgeCanonicalCoefficient
  rw [dif_pos hzeroMem, dif_pos honeMem, dif_pos hzeroMem]
  have hpair :=
    ternaryMajorArc_canonical_boundary_pair_eq_principal_lattice_sub_tail
      S b n target a d cutoff fareyCutoff τ ell
      zeroCenter oneCenter hsupport hcutoff hfarey rfl rfl
  rw [hpair]
  congr 1
  have hfareyReal : (1 : ℝ) ≤ fareyCutoff := by
    exact_mod_cast hfarey
  have hhalf : 2 * (1 / ((fareyCutoff : ℝ) + 1)) ≤ 1 := by
    calc
      2 * (1 / ((fareyCutoff : ℝ) + 1)) =
          2 / ((fareyCutoff : ℝ) + 1) := by ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hsym := actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
    a d n τ ell (1 / ((fareyCutoff : ℝ) + 1)) (by positivity) hhalf
  simpa [ternaryMajorArcOriginalDenominatorMiddleIntegral] using hsym.symm

/-- At EVERY genuine support-free conductor center, including the paired
principal center, the exact clipped canonical smooth contribution is its
complete signed canonical coefficient times the SAME true original
denominator symmetric archimedean integral. -/
theorem actualMajorArcCenterPhaseBridge_paired_center_eq_signed_symmetric
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff denominator : ℕ)
    (τ ell center : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff) (hfarey : 0 < fareyCutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1)
    (_hdenominator : 0 < denominator)
    (_hdenominatorCutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator (∏ p ∈ S, p))
    (hstratum : center ∈ actualMajorArcCenterReindexActualStratum
      (∏ p ∈ S, p) cutoff denominator) :
    actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
        S b n target a d cutoff fareyCutoff τ ell center =
      actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff center *
        (∫ β in Set.Icc
          (-(1 / ((denominator : ℝ) * (fareyCutoff + 1))))
          (1 / ((denominator : ℝ) * (fareyCutoff + 1))),
          actualMajorArcArchimedeanSmoothCubic
            a d n τ ell β) := by
  classical
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  unfold actualMajorArcCenterReindexActualStratum at hstratum
  obtain ⟨hcenterMem, hzero, hone,
      witness, hwitness, hwitnessDenominator,
      hwitnessCenter⟩ := Finset.mem_filter.mp hstratum
  let attached : ActualMajorArcGlobalCenter W cutoff :=
    ⟨center, hcenterMem⟩
  let anchor := actualMajorArcGlobalCanonicalWidestAnchor
    W cutoff fareyCutoff attached
  obtain ⟨hanchor, hanchorCenter, hanchorRegion⟩ :=
    actualMajorArcGlobalCanonicalWidestAnchor_spec
      W cutoff fareyCutoff attached
  have hanchorDenominator : anchor.1 = denominator := by
    rw [← hwitnessDenominator]
    apply actualConductorDedup_canonical_denominator_eq_support_free
      W cutoff fareyCutoff attached witness hW hwitness
    · exact hwitnessCenter
    · rw [hwitnessDenominator]
      exact hcoprime
  by_cases hboundary : center = 0
  · have hprincipal := actualMajorArcBoundary_zero_anchor_mem
      W cutoff hW hcutoff
    have hprincipalDenominator : anchor.1 = 1 := by
      apply actualConductorDedup_canonical_denominator_eq_support_free
        W cutoff fareyCutoff attached
          (1, (0 : ℤ), (0 : ℤ)) hW hprincipal
      · simpa [shiftedFareyAnchorCenter, attached] using hboundary.symm
      · simp
    have honeDenominator : denominator = 1 := by
      omega
    rw [hboundary, honeDenominator]
    simpa using
      actualMajorArcCenterPhaseBridge_boundary_pair_eq_signed_symmetric
        S b n target a d cutoff fareyCutoff τ ell
        hsupport hcutoff hfarey
  · have hpositive : 0 < center :=
      lt_of_le_of_ne hzero (Ne.symm hboundary)
    unfold actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
    rw [if_neg hboundary]
    unfold actualMajorArcCenterPhaseBridgeCanonicalIntegral
      actualMajorArcCenterPhaseBridgeCanonicalCoefficient
    rw [dif_pos hcenterMem, dif_pos hcenterMem]
    have hmodel := actualMajorArcInterior_integrated_smooth_eq_signed_symmetric
      S b n target a d cutoff fareyCutoff τ ell center anchor
      hsupport hcutoff hseparation hcenterMem hpositive hone
      hanchor hanchorCenter hanchorRegion
    change
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion W fareyCutoff
          (actualShiftedFareyAnchors W cutoff) center,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell anchor α) =
        actualCenterCouplingAnchorCoefficient
          S b target a d anchor *
          (∫ β in Set.Icc
            (-(1 / ((denominator : ℝ) * (fareyCutoff + 1))))
            (1 / ((denominator : ℝ) * (fareyCutoff + 1))),
            actualMajorArcArchimedeanSmoothCubic
              a d n τ ell β)
    rw [hmodel]
    change actualCenterCouplingAnchorCoefficient
      S b target a d anchor * _ = _
    rw [hanchorDenominator]

/-- Exact actual denominator-stratum COMPLEX smooth identity, retaining
the genuine `0/1` boundary gluing and original width. The full signed
coefficient orbit multiplies one common true symmetric lattice integral. -/
theorem actualMajorArcCenterPhaseBridge_paired_stratum_integral
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff denominator : ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff) (hfarey : 0 < fareyCutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1)
    (hdenominator : 0 < denominator)
    (hdenominatorCutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator (∏ p ∈ S, p)) :
    (∑ center ∈ actualMajorArcCenterReindexActualStratum
        (∏ p ∈ S, p) cutoff denominator,
      actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
        S b n target a d cutoff fareyCutoff τ ell center) =
      (∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range (∏ p ∈ S, p),
          actualCenterCouplingAnchorCoefficient S b target a d
            (denominator, (numerator : ℤ), (shift : ℤ))) *
        (∫ β in Set.Icc
          (-(1 / ((denominator : ℝ) * (fareyCutoff + 1))))
          (1 / ((denominator : ℝ) * (fareyCutoff + 1))),
          actualMajorArcArchimedeanSmoothCubic
            a d n τ ell β) := by
  calc
    _ = ∑ center ∈ actualMajorArcCenterReindexActualStratum
        (∏ p ∈ S, p) cutoff denominator,
      actualMajorArcCenterPhaseBridgeCanonicalCoefficient
        S b target a d cutoff fareyCutoff center *
        (∫ β in Set.Icc
          (-(1 / ((denominator : ℝ) * (fareyCutoff + 1))))
          (1 / ((denominator : ℝ) * (fareyCutoff + 1))),
          actualMajorArcArchimedeanSmoothCubic
            a d n τ ell β) := by
      apply Finset.sum_congr rfl
      intro center hcenter
      exact actualMajorArcCenterPhaseBridge_paired_center_eq_signed_symmetric
        S b n target a d cutoff fareyCutoff denominator
        τ ell center hsupport hcutoff hfarey hseparation
        hdenominator hdenominatorCutoff hcoprime hcenter
    _ = _ := by
      rw [← Finset.sum_mul,
        actualMajorArcCenterPhaseBridge_actual_stratum_coefficient_sum
          S b target a d cutoff fareyCutoff denominator
          hsupport hdenominator hdenominatorCutoff hcoprime]

/-- TERMINAL per-conductor identity needed by the global original major
assembly: the sum of the TRUE paired real canonical center weights over
all reduced numerators and genuine support shifts is exactly the REAL
part of the complete ORIGINAL-width raw Farey-anchor smooth orbit.
This includes the distinct `0/1` boundary clips at denominator one. -/
theorem actualMajorArcCenterPhaseBridge_actual_paired_orbit_eq_original
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff denominator : ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff) (hfarey : 0 < fareyCutoff)
    (hseparation :
      2 * ((∏ p ∈ S, p) * cutoff) ^ 2 < fareyCutoff + 1)
    (hdenominator : 0 < denominator)
    (hdenominatorCutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator (∏ p ∈ S, p)) :
    (∑ numerator ∈ (Finset.range denominator).filter
        (fun numerator => Nat.gcd numerator denominator = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        actualMajorArcGlobalStrataPairedCanonicalWeight
          S b n target a d cutoff fareyCutoff τ ell
          (actualMajorArcCenterReindexNormalizedCenter
            (∏ p ∈ S, p) denominator numerator
              (actualMajorArcCenterReindexNegShift
                (∏ p ∈ S, p) shift))) =
      (ternaryMajorArcOriginalAnchorOrbitSmoothMass
        S b n target a d denominator fareyCutoff τ ell).re := by
  let W := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  rw [← actualMajorArcCenterReindex_actual_stratum_sum
    W cutoff denominator
      (actualMajorArcGlobalStrataPairedCanonicalWeight
        S b n target a d cutoff fareyCutoff τ ell)
      hW hdenominator hdenominatorCutoff hcoprime]
  have hcomplex := actualMajorArcCenterPhaseBridge_paired_stratum_integral
    S b n target a d cutoff fareyCutoff denominator τ ell
    hsupport hcutoff hfarey hseparation hdenominator
      hdenominatorCutoff hcoprime
  have horbit := ternaryMajorArc_original_anchor_orbit_eq_coefficient_lattice_sub_tail
    S b n target a d denominator fareyCutoff τ ell
      hdenominator hfarey
  have hsym := actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
    a d n τ ell
      (1 / ((denominator : ℝ) * (fareyCutoff + 1)))
      (by positivity) (by
        have hdreal : (1 : ℝ) ≤ denominator := by
          exact_mod_cast hdenominator
        have hqreal : (1 : ℝ) ≤ fareyCutoff := by
          exact_mod_cast hfarey
        have hproduct : (2 : ℝ) ≤
            (denominator : ℝ) * (fareyCutoff + 1) := by
          calc
            (2 : ℝ) = 1 * (1 + 1) := by ring
            _ ≤ (denominator : ℝ) * (fareyCutoff + 1) :=
              mul_le_mul hdreal (by linarith)
                (by positivity) (by positivity)
        calc
          2 * (1 / ((denominator : ℝ) * (fareyCutoff + 1))) =
              2 / ((denominator : ℝ) * (fareyCutoff + 1)) := by ring
          _ ≤ 1 := (div_le_iff₀ (by positivity :
            (0 : ℝ) < (denominator : ℝ) * (fareyCutoff + 1))).mpr
              (by simpa using hproduct))
  have hrewrite :
      (∑ center ∈ actualMajorArcCenterReindexActualStratum
          W cutoff denominator,
        actualMajorArcCenterPhaseBridgeBoundaryPairedIntegral
          S b n target a d cutoff fareyCutoff τ ell center) =
        ternaryMajorArcOriginalAnchorOrbitSmoothMass
          S b n target a d denominator fareyCutoff τ ell := by
    rw [hcomplex, horbit]
    congr 1
  have hreal := congrArg Complex.re hrewrite
  simpa [map_sum,
    actualMajorArcCenterPhaseBridge_paired_real_eq_global] using hreal

#print axioms Erdos689.actualMajorArcCenterPhaseBridge_normalized_eq_shifted_add_int
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_canonical_coefficient_eq_raw
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_actual_stratum_coefficient_sum
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_actual_odd_stratum_factor
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_actual_even_stratum_factor
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_noncoprime_stratum_zero
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_paired_real_eq_global
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_boundary_pair_eq_signed_symmetric
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_paired_center_eq_signed_symmetric
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_paired_stratum_integral
#print axioms Erdos689.actualMajorArcCenterPhaseBridge_actual_paired_orbit_eq_original

end Erdos689
