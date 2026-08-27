import ActualMajorArcInterior433
import ActualMajorArcParityCRT433

/-!
# Exact genuine shifted-center reindexing

Normalized support-character/reduced-numerator pairs must correspond to
ACTUAL distinct real shifted Farey centers, not to raw duplicate anchors.
The finite bijection below keeps the original denominator, the canonical
half-open circle representative, every support character, and genuine
reduced numerators.  Its cardinality is `W*φ(q)` with no boundary double
count; the actual full-cell phase is then identified at the REAL center.
-/

open Finset MeasureTheory
open scoped BigOperators

namespace Erdos689

/-- The canonical REAL circle representative of a genuine reduced outside
numerator and a complete support character. -/
noncomputable def actualMajorArcCenterReindexNormalizedCenter
    (support denominator numerator character : ℕ) : ℝ :=
  (actualMajorArcCenterNormalizedCode
    support denominator numerator character : ℝ) /
      (denominator * support : ℕ)

/-- The finite distinct REAL normalized center family at one fixed genuine
outside original denominator. -/
noncomputable def actualMajorArcCenterReindexNormalizedCenters
    (support denominator : ℕ) : Finset ℝ := by
  classical
  exact Finset.image (α := ℕ) (β := ℝ)
    (fun code : ℕ => (code : ℝ) / (denominator * support : ℕ))
    (actualMajorArcCenterNormalizedCodes support denominator)

/-- Positive common denominator makes the map from exact finite center
codes to REAL circle centers injective; there is no analytic identification
or quotient over coincident real values. -/
theorem actualMajorArcCenterReindex_code_real_injective
    (support denominator : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator) :
    Function.Injective
      (fun code : ℕ => (code : ℝ) /
        (denominator * support : ℕ)) := by
  intro left right hequal
  have hcommon : (0 : ℝ) < (denominator * support : ℕ) := by
    exact_mod_cast Nat.mul_pos hdenominator hsupport
  have hreal : (left : ℝ) = (right : ℝ) :=
    (div_left_inj' hcommon.ne').mp hequal
  exact_mod_cast hreal

/-- At every genuine support-coprime original denominator, there are
EXACTLY `W*φ(q)` distinct normalized REAL circle centers. -/
theorem actualMajorArcCenterReindex_normalized_real_centers_card
    (support denominator : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcoprime : Nat.Coprime denominator support) :
    (actualMajorArcCenterReindexNormalizedCenters
      support denominator).card = support * Nat.totient denominator := by
  change ((actualMajorArcCenterNormalizedCodes support denominator).image
    (fun code : ℕ => (code : ℝ) /
      (denominator * support : ℕ))).card = _
  rw [Finset.card_image_of_injective _
    (actualMajorArcCenterReindex_code_real_injective
      support denominator hsupport hdenominator)]
  exact actualMajorArcCenter_normalized_codes_card
    support denominator hcoprime

/-- The canonical finite real-center code always lies in the genuine
half-open Fourier circle `[0,1)`. -/
theorem actualMajorArcCenterReindex_normalized_center_bounds
    (support denominator numerator character : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator) :
    0 ≤ actualMajorArcCenterReindexNormalizedCenter
      support denominator numerator character ∧
      actualMajorArcCenterReindexNormalizedCenter
        support denominator numerator character < 1 := by
  have hcommon : 0 < denominator * support :=
    Nat.mul_pos hdenominator hsupport
  have hcommonReal : (0 : ℝ) < (denominator * support : ℕ) := by
    exact_mod_cast hcommon
  have hcode := Nat.mod_lt
    (numerator * support + character * denominator) hcommon
  have hcodeReal :
      (actualMajorArcCenterNormalizedCode
        support denominator numerator character : ℝ) <
        (denominator * support : ℕ) := by
    exact_mod_cast hcode
  unfold actualMajorArcCenterReindexNormalizedCenter
  exact ⟨by positivity, (div_lt_one hcommonReal).mpr hcodeReal⟩

/-- Every reduced numerator and COMPLETE support character produces an
ORIGINAL finite Farey anchor at its exact normalized REAL center.  The
integer periodic quotient and negative character are normalized into the
actual allowed anchor family, with the original denominator unchanged. -/
theorem actualMajorArcCenterReindex_normalized_center_actual_anchor
    (support cutoff denominator numerator character : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hnumerator : Nat.Coprime numerator denominator) :
    ∃ anchor ∈ actualShiftedFareyAnchors support cutoff,
      anchor.1 = denominator ∧
        shiftedFareyAnchorCenter support
          anchor.1 anchor.2.1 anchor.2.2 =
            actualMajorArcCenterReindexNormalizedCenter
              support denominator numerator character := by
  let total := numerator * support + character * denominator
  let common := denominator * support
  let period := total / common
  let signedNumerator : ℤ :=
    (numerator : ℤ) - (period : ℤ) * (denominator : ℤ)
  let signedCharacter : ℤ := -(character : ℤ)
  have hcommon : 0 < common := Nat.mul_pos hdenominator hsupport
  have hdivision : total % common + common * period = total :=
    Nat.mod_add_div total common
  have hdivisionReal :
      ((total % common : ℕ) : ℝ) +
        (common : ℝ) * (period : ℝ) = (total : ℝ) := by
    exact_mod_cast hdivision
  have hsignedReduced : Int.gcd signedNumerator denominator = 1 := by
    change Int.gcd
      ((numerator : ℤ) - (period : ℤ) * (denominator : ℤ))
        (denominator : ℤ) = 1
    rw [show (numerator : ℤ) - (period : ℤ) * (denominator : ℤ) =
      (numerator : ℤ) + (denominator : ℤ) * (-(period : ℤ)) by ring,
      Int.gcd_add_mul_left_left, Int.gcd_natCast_natCast]
    exact hnumerator.gcd_eq_one
  have hsignedCenter :
      shiftedFareyAnchorCenter support denominator
          signedNumerator signedCharacter =
        actualMajorArcCenterReindexNormalizedCenter
          support denominator numerator character := by
    unfold shiftedFareyAnchorCenter
      actualMajorArcCenterReindexNormalizedCenter
      actualMajorArcCenterNormalizedCode
    dsimp [signedNumerator, signedCharacter]
    push_cast
    dsimp [total, common, period] at hdivisionReal
    push_cast at hdivisionReal
    dsimp [period, total, common]
    field_simp
    linear_combination -hdivisionReal
  obtain ⟨normalizedNumerator, normalizedCharacter,
      hnormalizedBound, hnormalizedReduced, hnormalizedCenter⟩ :=
    actualMajorArcCenter_character_normalized_reanchor
      support denominator signedNumerator signedCharacter
      hsupport hdenominator hsignedReduced
  have hcenter : shiftedFareyAnchorCenter support denominator
        normalizedNumerator (normalizedCharacter : ℤ) =
      actualMajorArcCenterReindexNormalizedCenter
        support denominator numerator character :=
    hnormalizedCenter.symm.trans hsignedCenter
  obtain ⟨hzero, hone⟩ :=
    actualMajorArcCenterReindex_normalized_center_bounds
      support denominator numerator character hsupport hdenominator
  refine ⟨(denominator, normalizedNumerator,
    (normalizedCharacter : ℤ)), ?_, rfl, hcenter⟩
  apply actualMajorArcCenter_normalized_actual_anchor_mem
    support cutoff denominator normalizedNumerator normalizedCharacter
    hsupport hdenominator hcutoff hnormalizedBound hnormalizedReduced
  · rw [hcenter]
    exact hzero
  · rw [hcenter]
    exact hone.le

/-- Every normalized genuine outside/support REAL center occurs in the
ORIGINAL finite deduplicated shifted-center classes; no illustrative or
enlarged rational-center family is used. -/
theorem actualMajorArcCenterReindex_normalized_center_mem_actual_classes
    (support cutoff denominator numerator character : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hnumerator : Nat.Coprime numerator denominator) :
    actualMajorArcCenterReindexNormalizedCenter
        support denominator numerator character ∈
      shiftedFareyCenterClasses support
        (actualShiftedFareyAnchors support cutoff) := by
  obtain ⟨anchor, hanchor, _, hcenter⟩ :=
    actualMajorArcCenterReindex_normalized_center_actual_anchor
      support cutoff denominator numerator character
        hsupport hdenominator hcutoff hnumerator
  unfold shiftedFareyCenterClasses
  exact Finset.mem_image.mpr ⟨anchor, hanchor, hcenter⟩

/-- EVERY original finite shifted anchor whose REAL center is in the
canonical half-open circle has a reduced-numerator / full support-character
normalized code at the SAME original denominator.  This is the reverse
direction needed for an exact actual-center bijection. -/
theorem actualMajorArcCenterReindex_actual_anchor_normalized
    (support cutoff : ℕ) (anchor : ShiftedFareyAnchor)
    (hsupport : 0 < support)
    (hanchor : anchor ∈ actualShiftedFareyAnchors support cutoff)
    (hzero : 0 ≤ shiftedFareyAnchorCenter support
      anchor.1 anchor.2.1 anchor.2.2)
    (hone : shiftedFareyAnchorCenter support
      anchor.1 anchor.2.1 anchor.2.2 < 1) :
    ∃ numerator character : ℕ,
      numerator < anchor.1 ∧ Nat.Coprime numerator anchor.1 ∧
        character < support ∧
        shiftedFareyAnchorCenter support
          anchor.1 anchor.2.1 anchor.2.2 =
            actualMajorArcCenterReindexNormalizedCenter
              support anchor.1 numerator character := by
  have hdenominator :=
    (actualShiftedFareyAnchors_denominator_bounds
      support cutoff anchor hanchor).1
  have hnumerator := actualMajorArcCenter_actual_anchor_numerator_coprime
    support cutoff anchor hanchor
  obtain ⟨numerator, lift, hnumeratorBound,
      hnumeratorReduced, hnumeratorRepresentation⟩ :=
    actualMajorArcCenter_signed_numerator_eq_nat_plus_lift
      anchor.1 anchor.2.1 hdenominator hnumerator
  let character := ((-anchor.2.2) % (support : ℤ)).toNat
  let period := (-anchor.2.2) / (support : ℤ)
  have hsupportInt : (0 : ℤ) < support := by exact_mod_cast hsupport
  have hcharacterNonnegative :
      0 ≤ (-anchor.2.2) % (support : ℤ) :=
    Int.emod_nonneg (-anchor.2.2) hsupportInt.ne'
  have hcharacterCast : (character : ℤ) =
      (-anchor.2.2) % (support : ℤ) :=
    Int.toNat_of_nonneg hcharacterNonnegative
  have hcharacterBound : character < support := by
    have hbound : (character : ℤ) < support := by
      rw [hcharacterCast]
      exact Int.emod_lt_of_pos (-anchor.2.2) hsupportInt
    exact_mod_cast hbound
  have hcharacterRepresentation : -anchor.2.2 =
      (character : ℤ) + (support : ℤ) * period := by
    rw [hcharacterCast]
    exact (Int.emod_add_mul_ediv
      (-anchor.2.2) (support : ℤ)).symm
  let centerNumerator : ℤ :=
    anchor.2.1 * (support : ℤ) -
      anchor.2.2 * (anchor.1 : ℤ)
  let common : ℕ := anchor.1 * support
  have hcommon : 0 < common := Nat.mul_pos hdenominator hsupport
  have hcommonReal : (0 : ℝ) < common := by exact_mod_cast hcommon
  have hcenterCommon :
      shiftedFareyAnchorCenter support
          anchor.1 anchor.2.1 anchor.2.2 =
        (centerNumerator : ℝ) / (common : ℝ) :=
    shiftedFareyAnchorCenter_eq_common_fraction
      support anchor.1 anchor.2.1 anchor.2.2
      hsupport hdenominator
  have hcenterNumeratorNonnegativeReal : (0 : ℝ) ≤ centerNumerator := by
    have hratio : (0 : ℝ) ≤ (centerNumerator : ℝ) / common := by
      rw [← hcenterCommon]
      exact hzero
    simpa using (le_div_iff₀ hcommonReal).mp hratio
  have hcenterNumeratorLessReal : (centerNumerator : ℝ) < common := by
    apply (div_lt_one hcommonReal).mp
    rw [← hcenterCommon]
    exact hone
  have hcenterNumeratorNonnegative : (0 : ℤ) ≤ centerNumerator := by
    exact_mod_cast hcenterNumeratorNonnegativeReal
  have hcenterNumeratorLess : centerNumerator < (common : ℤ) := by
    exact_mod_cast hcenterNumeratorLessReal
  have hrepresentation : centerNumerator =
      ((numerator * support + character * anchor.1 : ℕ) : ℤ) +
        (lift + period) * (common : ℤ) := by
    dsimp [centerNumerator, common]
    rw [hnumeratorRepresentation]
    calc
      ((numerator : ℤ) + lift * (anchor.1 : ℤ)) *
          (support : ℤ) - anchor.2.2 * (anchor.1 : ℤ) =
        (numerator : ℤ) * support +
          (-anchor.2.2) * (anchor.1 : ℤ) +
          lift * ((anchor.1 : ℤ) * support) := by ring
      _ = _ := by
        rw [hcharacterRepresentation]
        ring
  have hcode :
      (actualMajorArcCenterNormalizedCode
        support anchor.1 numerator character : ℤ) =
        centerNumerator := by
    unfold actualMajorArcCenterNormalizedCode
    rw [Int.natCast_mod]
    have hmod := congrArg (fun value : ℤ =>
      value % (common : ℤ)) hrepresentation
    rw [Int.emod_eq_of_lt hcenterNumeratorNonnegative
      hcenterNumeratorLess] at hmod
    dsimp [common] at hmod ⊢
    simpa [Int.add_emod, Int.mul_emod] using hmod.symm
  refine ⟨numerator, character, hnumeratorBound,
    hnumeratorReduced, hcharacterBound, ?_⟩
  rw [hcenterCommon]
  unfold actualMajorArcCenterReindexNormalizedCenter
  have hcodeReal : (centerNumerator : ℝ) =
      (actualMajorArcCenterNormalizedCode
        support anchor.1 numerator character : ℝ) := by
    exact_mod_cast hcode.symm
  rw [hcodeReal]

/-- Genuine deduplicated REAL centers in `[0,1)` whose ORIGINAL finite
anchor family contains a representative of exactly the stated denominator. -/
noncomputable def actualMajorArcCenterReindexActualStratum
    (support cutoff denominator : ℕ) : Finset ℝ := by
  classical
  exact (shiftedFareyCenterClasses support
    (actualShiftedFareyAnchors support cutoff)).filter fun center =>
      0 ≤ center ∧ center < 1 ∧
        ∃ anchor ∈ actualShiftedFareyAnchors support cutoff,
          anchor.1 = denominator ∧
            shiftedFareyAnchorCenter support
              anchor.1 anchor.2.1 anchor.2.2 = center

/-- EXACT finite real-center bijection: the complete reduced numerator / W
support-character code family is PRECISELY the ORIGINAL deduplicated
half-open-circle center stratum at that genuine support-coprime original
denominator. Both directions construct actual anchors; no center is omitted
and no duplicate anchor is counted. -/
theorem actualMajorArcCenterReindex_normalized_centers_eq_actual_stratum
    (support cutoff denominator : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator support) :
    actualMajorArcCenterReindexNormalizedCenters support denominator =
      actualMajorArcCenterReindexActualStratum
        support cutoff denominator := by
  classical
  ext center
  constructor
  · intro hmember
    change center ∈ (Finset.image (α := ℕ) (β := ℝ)
      (fun code : ℕ => (code : ℝ) /
        (denominator * support : ℕ))
      (actualMajorArcCenterNormalizedCodes support denominator)) at hmember
    obtain ⟨code, hcode, rfl⟩ := Finset.mem_image.mp hmember
    unfold actualMajorArcCenterNormalizedCodes at hcode
    obtain ⟨parameter, hparameter, rfl⟩ :=
      Finset.mem_image.mp hcode
    obtain ⟨hnumerator, hcharacter⟩ :=
      Finset.mem_product.mp hparameter
    obtain ⟨hnumeratorRange, hnumeratorReduced⟩ :=
      Finset.mem_filter.mp hnumerator
    have hnumeratorCoprime :
        Nat.Coprime parameter.1 denominator :=
      hnumeratorReduced
    have hnormalized :
        (actualMajorArcCenterNormalizedCode
            support denominator parameter.1 parameter.2 : ℝ) /
          (denominator * support : ℕ) =
        actualMajorArcCenterReindexNormalizedCenter
          support denominator parameter.1 parameter.2 := rfl
    have hactual :=
      actualMajorArcCenterReindex_normalized_center_actual_anchor
        support cutoff denominator parameter.1 parameter.2
        hsupport hdenominator hcutoff hnumeratorCoprime
    obtain ⟨hzero, hone⟩ :=
      actualMajorArcCenterReindex_normalized_center_bounds
        support denominator parameter.1 parameter.2
        hsupport hdenominator
    unfold actualMajorArcCenterReindexActualStratum
    apply Finset.mem_filter.mpr
    rw [hnormalized]
    refine ⟨actualMajorArcCenterReindex_normalized_center_mem_actual_classes
      support cutoff denominator parameter.1 parameter.2
      hsupport hdenominator hcutoff hnumeratorCoprime,
      hzero, hone, ?_⟩
    exact hactual
  · intro hmember
    unfold actualMajorArcCenterReindexActualStratum at hmember
    obtain ⟨_, hzero, hone, anchor, hanchor,
      hdenominatorEq, hanchorCenter⟩ := Finset.mem_filter.mp hmember
    obtain ⟨numerator, character, hnumeratorBound,
      hnumeratorReduced, hcharacterBound, hnormalized⟩ :=
        actualMajorArcCenterReindex_actual_anchor_normalized
          support cutoff anchor hsupport hanchor
          (hanchorCenter.symm ▸ hzero)
          (hanchorCenter.symm ▸ hone)
    have hdenominatorEq' : anchor.1 = denominator := hdenominatorEq
    subst denominator
    change center ∈ (Finset.image (α := ℕ) (β := ℝ)
      (fun code : ℕ => (code : ℝ) /
        (anchor.1 * support : ℕ))
      (actualMajorArcCenterNormalizedCodes support anchor.1))
    apply Finset.mem_image.mpr
    refine ⟨actualMajorArcCenterNormalizedCode
      support anchor.1 numerator character, ?_, ?_⟩
    · unfold actualMajorArcCenterNormalizedCodes
      apply Finset.mem_image.mpr
      refine ⟨(numerator, character), ?_, rfl⟩
      unfold actualMajorArcCenterNormalizedParameters
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hnumeratorBound,
          hnumeratorReduced.gcd_eq_one⟩,
        Finset.mem_range.mpr hcharacterBound⟩
    · change actualMajorArcCenterReindexNormalizedCenter
        support anchor.1 numerator character = center
      exact hnormalized.symm.trans hanchorCenter

/-- The ACTUAL original finite deduplicated half-open-circle stratum at
every support-coprime denominator has EXACTLY `W*φ(q)` real centers. -/
theorem actualMajorArcCenterReindex_actual_stratum_card
    (support cutoff denominator : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator support) :
    (actualMajorArcCenterReindexActualStratum
      support cutoff denominator).card =
      support * Nat.totient denominator := by
  rw [← actualMajorArcCenterReindex_normalized_centers_eq_actual_stratum
    support cutoff denominator hsupport hdenominator hcutoff hcoprime]
  exact actualMajorArcCenterReindex_normalized_real_centers_card
    support denominator hsupport hdenominator hcoprime

/-- The genuine support-character sign reversal, with its exact canonical
representative in the original finite range. -/
def actualMajorArcCenterReindexNegShift
    (support shift : ℕ) : ℕ :=
  (support - shift) % support

/-- Finite support-character sign reversal is its own inverse on the
complete original range; it never introduces a duplicate shift. -/
theorem actualMajorArcCenterReindex_neg_shift_involution
    (support shift : ℕ)
    (_hsupport : 0 < support) (hshift : shift < support) :
    actualMajorArcCenterReindexNegShift support
      (actualMajorArcCenterReindexNegShift support shift) = shift := by
  unfold actualMajorArcCenterReindexNegShift
  by_cases hzero : shift = 0
  · simp [hzero]
  · have hpositive : 0 < shift := Nat.pos_of_ne_zero hzero
    have hfirst : support - shift < support := by omega
    rw [Nat.mod_eq_of_lt hfirst]
    have hsecond : support - (support - shift) = shift := by omega
    rw [hsecond, Nat.mod_eq_of_lt hshift]

/-- The finite sign reversal is injective on the exact support-character
range, with no group-quotient or counting assumption. -/
theorem actualMajorArcCenterReindex_neg_shift_injective
    (support left right : ℕ)
    (hsupport : 0 < support)
    (hleft : left < support) (hright : right < support)
    (hequal : actualMajorArcCenterReindexNegShift support left =
      actualMajorArcCenterReindexNegShift support right) :
    left = right := by
  calc
    left = actualMajorArcCenterReindexNegShift support
        (actualMajorArcCenterReindexNegShift support left) :=
      (actualMajorArcCenterReindex_neg_shift_involution
        support left hsupport hleft).symm
    _ = actualMajorArcCenterReindexNegShift support
        (actualMajorArcCenterReindexNegShift support right) := by
      rw [hequal]
    _ = right := actualMajorArcCenterReindex_neg_shift_involution
      support right hsupport hright

/-- EXACT arbitrary-weight finite reindexing of the ORIGINAL deduplicated
real-center stratum by reduced numerators and EVERY genuine signed support
shift. This retains the canonical `[0,1)` representative and contains no
duplicate-anchor or boundary overcount. -/
theorem actualMajorArcCenterReindex_actual_stratum_sum
    {A : Type*} [AddCommMonoid A]
    (support cutoff denominator : ℕ) (weight : ℝ → A)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator support) :
    (∑ center ∈ actualMajorArcCenterReindexActualStratum
        support cutoff denominator, weight center) =
      ∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range support,
          weight (actualMajorArcCenterReindexNormalizedCenter
            support denominator numerator
              (actualMajorArcCenterReindexNegShift support shift)) := by
  classical
  let parameters :=
    ((Finset.range denominator).filter
      (fun numerator => Nat.gcd numerator denominator = 1)).product
        (Finset.range support)
  have hrewrite :
      (∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range support,
          weight (actualMajorArcCenterReindexNormalizedCenter
            support denominator numerator
              (actualMajorArcCenterReindexNegShift support shift))) =
        ∑ parameter ∈ parameters,
          weight (actualMajorArcCenterReindexNormalizedCenter
            support denominator parameter.1
              (actualMajorArcCenterReindexNegShift
                support parameter.2)) := by
    simp [parameters, Finset.sum_product]
  rw [hrewrite]
  symm
  apply Finset.sum_bij
    (fun parameter _ => actualMajorArcCenterReindexNormalizedCenter
      support denominator parameter.1
        (actualMajorArcCenterReindexNegShift support parameter.2))
  · intro parameter hparameter
    obtain ⟨hnumerator, hshift⟩ := Finset.mem_product.mp hparameter
    obtain ⟨hnumeratorRange, hnumeratorReduced⟩ :=
      Finset.mem_filter.mp hnumerator
    have hcoprimeNumerator : Nat.Coprime parameter.1 denominator :=
      hnumeratorReduced
    have hnegBound :
        actualMajorArcCenterReindexNegShift
          support parameter.2 < support :=
      Nat.mod_lt _ hsupport
    obtain ⟨hzero, hone⟩ :=
      actualMajorArcCenterReindex_normalized_center_bounds
        support denominator parameter.1
        (actualMajorArcCenterReindexNegShift support parameter.2)
        hsupport hdenominator
    obtain ⟨anchor, hanchor, hdenominatorEq, hcenter⟩ :=
      actualMajorArcCenterReindex_normalized_center_actual_anchor
        support cutoff denominator parameter.1
        (actualMajorArcCenterReindexNegShift support parameter.2)
        hsupport hdenominator hcutoff hcoprimeNumerator
    unfold actualMajorArcCenterReindexActualStratum
    apply Finset.mem_filter.mpr
    refine ⟨actualMajorArcCenterReindex_normalized_center_mem_actual_classes
      support cutoff denominator parameter.1
      (actualMajorArcCenterReindexNegShift support parameter.2)
      hsupport hdenominator hcutoff hcoprimeNumerator,
      hzero, hone, anchor, hanchor, hdenominatorEq, hcenter⟩
  · intro left hleft right hright hequal
    obtain ⟨hleftNumerator, hleftShift⟩ :=
      Finset.mem_product.mp hleft
    obtain ⟨hrightNumerator, hrightShift⟩ :=
      Finset.mem_product.mp hright
    have hleftNum := Finset.mem_range.mp
      (Finset.mem_filter.mp hleftNumerator).1
    have hrightNum := Finset.mem_range.mp
      (Finset.mem_filter.mp hrightNumerator).1
    have hleftShift' := Finset.mem_range.mp hleftShift
    have hrightShift' := Finset.mem_range.mp hrightShift
    have hcodes :
        actualMajorArcCenterNormalizedCode support denominator
          left.1 (actualMajorArcCenterReindexNegShift support left.2) =
        actualMajorArcCenterNormalizedCode support denominator
          right.1 (actualMajorArcCenterReindexNegShift support right.2) := by
      exact actualMajorArcCenterReindex_code_real_injective
        support denominator hsupport hdenominator hequal
    obtain ⟨hfirst, hsecond⟩ :=
      actualMajorArcCenter_normalized_code_injective
        support denominator left.1 right.1
        (actualMajorArcCenterReindexNegShift support left.2)
        (actualMajorArcCenterReindexNegShift support right.2)
        hcoprime hleftNum hrightNum
        (Nat.mod_lt _ hsupport) (Nat.mod_lt _ hsupport) hcodes
    exact Prod.ext hfirst
      (actualMajorArcCenterReindex_neg_shift_injective
        support left.2 right.2 hsupport
          hleftShift' hrightShift' hsecond)
  · intro center hcenter
    unfold actualMajorArcCenterReindexActualStratum at hcenter
    obtain ⟨_, hzero, hone, anchor, hanchor,
      hanchorDenominator, hanchorCenter⟩ :=
      Finset.mem_filter.mp hcenter
    obtain ⟨numerator, character, hnumeratorBound,
      hnumeratorReduced, hcharacterBound, hnormalized⟩ :=
      actualMajorArcCenterReindex_actual_anchor_normalized
        support cutoff anchor hsupport hanchor
          (hanchorCenter.symm ▸ hzero)
          (hanchorCenter.symm ▸ hone)
    subst denominator
    let shift := actualMajorArcCenterReindexNegShift support character
    have hshift : shift < support := Nat.mod_lt _ hsupport
    refine ⟨(numerator, shift), Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hnumeratorBound,
          hnumeratorReduced.gcd_eq_one⟩,
        Finset.mem_range.mpr hshift⟩, ?_⟩
    have hinvolution :
        actualMajorArcCenterReindexNegShift support shift = character :=
      actualMajorArcCenterReindex_neg_shift_involution
        support character hsupport hcharacterBound
    change actualMajorArcCenterReindexNormalizedCenter
      support anchor.1 numerator
        (actualMajorArcCenterReindexNegShift support shift) = center
    rw [hinvolution]
    exact hnormalized.symm.trans hanchorCenter
  · intro parameter _
    rfl

#print axioms Erdos689.actualMajorArcCenterReindex_code_real_injective
#print axioms Erdos689.actualMajorArcCenterReindex_normalized_real_centers_card
#print axioms Erdos689.actualMajorArcCenterReindex_normalized_center_bounds
#print axioms Erdos689.actualMajorArcCenterReindex_normalized_center_actual_anchor
#print axioms Erdos689.actualMajorArcCenterReindex_normalized_center_mem_actual_classes
#print axioms Erdos689.actualMajorArcCenterReindex_actual_anchor_normalized
#print axioms Erdos689.actualMajorArcCenterReindex_normalized_centers_eq_actual_stratum
#print axioms Erdos689.actualMajorArcCenterReindex_actual_stratum_card
#print axioms Erdos689.actualMajorArcCenterReindex_neg_shift_involution
#print axioms Erdos689.actualMajorArcCenterReindex_neg_shift_injective
#print axioms Erdos689.actualMajorArcCenterReindex_actual_stratum_sum

end Erdos689
