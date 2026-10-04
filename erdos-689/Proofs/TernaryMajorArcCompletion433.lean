module

public import ActualCenterCouplingFourier433
public import ActualConductorDedupCompletion433
public import ActualOutsideCrtCoupling433
public import ActualSingularTailCompletion433

@[expose] public section


/-!
# Full original-anchor Fourier and outside-conductor coupling

Every coefficient here comes from the *actual integrated shifted anchor*,
including its true `lcm(q,W)` effective numerator and all three switched
unit-cell filters.  Summing all support shifts and all reduced rational
numerators identifies that actual coefficient with the compensated signed
outside factor; the odd and genuine parity-doubled families retain their
different original denominators and Farey widths.

No identification with the distinct-center/canonical-widest sum is made
without an explicit proved finite reindexing.
-/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Erdos689

/-- The exact `lcm(q,W)` effective phase of an ORIGINAL integrated anchor
is its genuine shifted real-center phase. This retains both the rational
numerator and the support-character shift. -/
theorem ternaryMajorArc_anchor_cell_phase_eq_shifted_phase
    (S : Finset ℕ)
    (denominator label left right a d : ℕ)
    (numerator shift : ℤ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime) :
    actualMajorArcArchimedeanCellPhase
        (actualMajorArcLcmResidueModulus S denominator)
        label left right a d
        (actualMajorArcIntegratedAnchorNumerator S
          (denominator, numerator, shift)) =
      actualMajorArcSquarefreeTriplePhase label left right a d
        ((numerator : ℝ) / denominator -
          (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ)) := by
  have hcenter := actualMajorArcLcm_rescaled_shifted_rational_center
    S denominator numerator shift 0 hdenominator hsupport
  simp only [Int.cast_zero, add_zero, zero_mul] at hcenter
  unfold actualMajorArcArchimedeanCellPhase
    actualMajorArcSquarefreeTriplePhase
  rw [hcenter]
  unfold actualMajorArcIntegratedAnchorNumerator
  dsimp
  congr 2 <;> congr 1 <;> ring

/-- The sum of the actual normalized anchor coefficients over EVERY true
support shift projects onto precisely the compatible full-modulus triples.
No incompatible switched cell is silently discarded. -/
theorem ternaryMajorArc_anchor_coefficient_support_shift_sum
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ)
    (numerator : ℕ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (∑ shift ∈ Finset.range (∏ p ∈ S, p),
      actualCenterCouplingAnchorCoefficient S b target a d
        (denominator, (numerator : ℤ), (shift : ℤ))) =
      (((∏ p ∈ S, p) : ℕ) : ℂ) *
        (∑ triple ∈ actualMajorArcParityCompatibleFullCellTriples
          S b target a d denominator,
            actualMajorArcSquarefreeTriplePhase
              triple.1 triple.2.1 triple.2.2 a d
                ((numerator : ℝ) / denominator)) *
          (1 / ((actualMajorArcLcmResidueModulus
            S denominator).totient : ℂ)) ^ 3 := by
  classical
  have hprojection :=
    actualMajorArcSquarefree_admissible_triple_shift_projection
      S b target a d denominator (numerator : ℤ) 0
      (fun _ => (1 : ℂ)) hsupport
  simp only [Int.cast_natCast, Int.cast_zero, add_zero,
    one_mul] at hprojection
  change
    (∑ shift ∈ Finset.range (∏ p ∈ S, p),
      (∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator,
          actualMajorArcArchimedeanCellPhase
            (actualMajorArcLcmResidueModulus S denominator)
            triple.1 triple.2.1 triple.2.2 a d
            (actualMajorArcIntegratedAnchorNumerator S
              (denominator, (numerator : ℤ), (shift : ℤ)))) *
          (1 / ((actualMajorArcLcmResidueModulus
            S denominator).totient : ℂ)) ^ 3) = _
  simp_rw [ternaryMajorArc_anchor_cell_phase_eq_shifted_phase
    S denominator _ _ _ a d _ _ hdenominator hsupport]
  simp only [Int.cast_natCast]
  rw [← Finset.sum_mul]
  rw [show
      (actualMajorArcLcmAdmissibleCellTriples
        S b target a d denominator).filter
        (fun triple =>
          (a * triple.2.1 + triple.1) % (∏ p ∈ S, p) =
            (2 * d * triple.2.2) % (∏ p ∈ S, p)) =
        actualMajorArcParityCompatibleFullCellTriples
          S b target a d denominator by rfl] at hprojection
  have hterms (triple : ℕ × ℕ × ℕ) :
      GoldbachChain.e
        (((actualMajorArcSquarefreeAffineDefect
          triple.1 triple.2.1 triple.2.2 a d : ℝ) *
            numerator) / denominator) =
        actualMajorArcSquarefreeTriplePhase
          triple.1 triple.2.1 triple.2.2 a d
            ((numerator : ℝ) / denominator) := by
    rw [actualMajorArcSquarefreeTriplePhase_eq_defect_phase]
    congr 1
    ring
  simp_rw [hterms] at hprojection
  rw [hprojection]

/-- The complete signed three-cell character is invariant under EVERY
integer periodic lift, including negative lifts and the doubled frequency. -/
theorem ternaryMajorArc_triple_phase_add_integer
    (label left right a d : ℕ) (center : ℝ) (period : ℤ) :
    actualMajorArcSquarefreeTriplePhase
        label left right a d (center + (period : ℝ)) =
      actualMajorArcSquarefreeTriplePhase
        label left right a d center := by
  rw [actualMajorArcSquarefreeTriplePhase_eq_defect_phase,
    actualMajorArcSquarefreeTriplePhase_eq_defect_phase]
  have hargument :
      (actualMajorArcSquarefreeAffineDefect
          label left right a d : ℝ) * (center + (period : ℝ)) =
        (actualMajorArcSquarefreeAffineDefect
          label left right a d : ℝ) * center +
          ((actualMajorArcSquarefreeAffineDefect
            label left right a d * period : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hargument, ← GoldbachChain.e_add,
    GoldbachChain.MinorArc.e_int, mul_one]

/-- Actual normalized integrated-anchor coefficients depend only on the
ORIGINAL denominator and the real center modulo an integer. All three
unit/switched selectors are retained; no choice of lift changes the phase. -/
theorem ternaryMajorArc_anchor_coefficient_eq_of_periodic_centers
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d : ℕ)
    (anchor other : ShiftedFareyAnchor)
    (period : ℤ)
    (hdenominator : anchor.1 = other.1)
    (hpositive : 0 < anchor.1)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcenter : shiftedFareyAnchorCenter (∏ p ∈ S, p)
        anchor.1 anchor.2.1 anchor.2.2 =
      shiftedFareyAnchorCenter (∏ p ∈ S, p)
        other.1 other.2.1 other.2.2 + (period : ℝ)) :
    actualCenterCouplingAnchorCoefficient S b target a d anchor =
      actualCenterCouplingAnchorCoefficient S b target a d other := by
  rcases anchor with ⟨denominator, numerator, shift⟩
  rcases other with ⟨otherDenominator, otherNumerator, otherShift⟩
  dsimp at hdenominator hpositive hcenter ⊢
  subst otherDenominator
  unfold actualCenterCouplingAnchorCoefficient
  dsimp
  apply congrArg
    (fun value : ℂ => value *
      (1 / ((actualMajorArcLcmResidueModulus
        S denominator).totient : ℂ)) ^ 3)
  apply Finset.sum_congr rfl
  intro triple htriple
  rw [ternaryMajorArc_anchor_cell_phase_eq_shifted_phase
    S denominator triple.1 triple.2.1 triple.2.2 a d
      numerator shift hpositive hsupport,
    ternaryMajorArc_anchor_cell_phase_eq_shifted_phase
      S denominator triple.1 triple.2.1 triple.2.2 a d
        otherNumerator otherShift hpositive hsupport]
  have hreal :
      (numerator : ℝ) / denominator -
          (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) =
        ((otherNumerator : ℝ) / denominator -
          (otherShift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ)) +
            (period : ℝ) := by
    simpa [shiftedFareyAnchorCenter] using hcenter
  rw [hreal, ternaryMajorArc_triple_phase_add_integer]

/-- Equal-denominator anchors representing the EXACT same actual real
center have identical complete signed selected-unit coefficients. -/
theorem ternaryMajorArc_anchor_coefficient_eq_of_same_center
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d : ℕ)
    (anchor other : ShiftedFareyAnchor)
    (hdenominator : anchor.1 = other.1)
    (hpositive : 0 < anchor.1)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcenter : shiftedFareyAnchorCenter (∏ p ∈ S, p)
        anchor.1 anchor.2.1 anchor.2.2 =
      shiftedFareyAnchorCenter (∏ p ∈ S, p)
        other.1 other.2.1 other.2.2) :
    actualCenterCouplingAnchorCoefficient S b target a d anchor =
      actualCenterCouplingAnchorCoefficient S b target a d other := by
  apply ternaryMajorArc_anchor_coefficient_eq_of_periodic_centers
    S b target a d anchor other 0 hdenominator hpositive hsupport
  simpa using hcenter

/-- The two REAL boundary representatives have equal actual canonical
selected-unit coefficients.  Both widest original denominators are exactly
one, and their genuine cell phases differ by the integer lift one. -/
theorem ternaryMajorArc_canonical_boundary_coefficients_eq
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff : ℕ)
    (zeroCenter oneCenter : ActualMajorArcGlobalCenter
      (∏ p ∈ S, p) cutoff)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff)
    (hzero : zeroCenter.val = 0)
    (hone : oneCenter.val = 1) :
    actualCenterCouplingAnchorCoefficient S b target a d
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff zeroCenter) =
      actualCenterCouplingAnchorCoefficient S b target a d
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff oneCenter) := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  let zeroAnchor := actualMajorArcGlobalCanonicalWidestAnchor
    W cutoff fareyCutoff zeroCenter
  let oneAnchor := actualMajorArcGlobalCanonicalWidestAnchor
    W cutoff fareyCutoff oneCenter
  have hzeroDenominator : zeroAnchor.1 = 1 := by
    apply actualConductorDedup_canonical_denominator_eq_support_free
      W cutoff fareyCutoff zeroCenter (1, (0 : ℤ), (0 : ℤ)) hW
    · exact actualMajorArcBoundary_zero_anchor_mem W cutoff hW hcutoff
    · simp [shiftedFareyAnchorCenter, hzero]
    · simp
  have honeDenominator : oneAnchor.1 = 1 := by
    apply actualConductorDedup_canonical_denominator_eq_support_free
      W cutoff fareyCutoff oneCenter (1, (1 : ℤ), (0 : ℤ)) hW
    · exact actualMajorArcBoundary_one_anchor_mem W cutoff hW hcutoff
    · simp [shiftedFareyAnchorCenter, hone]
    · simp
  apply ternaryMajorArc_anchor_coefficient_eq_of_periodic_centers
    S b target a d zeroAnchor oneAnchor (-1)
  · exact hzeroDenominator.trans honeDenominator.symm
  · omega
  · exact hsupport
  · rw [(actualMajorArcGlobalCanonicalWidestAnchor_spec
      W cutoff fareyCutoff zeroCenter).2.1,
      (actualMajorArcGlobalCanonicalWidestAnchor_spec
        W cutoff fareyCutoff oneCenter).2.1,
      hzero, hone]
    norm_num

/-- The exact normalized real circle center differs from its unnormalized
positive-character rational center by the integer Euclidean quotient. -/
theorem ternaryMajorArc_normalized_center_eq_rational_add_character_sub_quotient
    (support denominator numerator character : ℕ)
    (hsupport : 0 < support)
    (hdenominator : 0 < denominator) :
    actualMajorArcCenterReindexNormalizedCenter
        support denominator numerator character =
      (numerator : ℝ) / denominator +
        (character : ℝ) / support -
          (((numerator * support + character * denominator) /
            (denominator * support) : ℕ) : ℝ) := by
  let total : ℕ := numerator * support + character * denominator
  let common : ℕ := denominator * support
  have hdivision : total % common +
      common * (total / common) = total := Nat.mod_add_div total common
  have hreal := congrArg (fun value : ℕ => (value : ℝ)) hdivision
  dsimp [total, common] at hreal
  push_cast at hreal
  unfold actualMajorArcCenterReindexNormalizedCenter
    actualMajorArcCenterNormalizedCode
  have hdenominatorReal : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast hdenominator.ne'
  have hsupportReal : (support : ℝ) ≠ 0 := by
    exact_mod_cast hsupport.ne'
  push_cast
  field_simp
  nlinarith

/-- The normalized NEGATED support-character center differs from the
ORIGINAL manuscript anchor `h/q-j/W` by an explicit integer lift. -/
theorem ternaryMajorArc_normalized_negative_character_eq_anchor_add_integer
    (support denominator numerator shift : ℕ)
    (hsupport : 0 < support)
    (hdenominator : 0 < denominator)
    (hshift : shift < support) :
    ∃ period : ℤ,
      actualMajorArcCenterReindexNormalizedCenter
          support denominator numerator
            ((support - shift) % support) =
        (numerator : ℝ) / denominator -
          (shift : ℝ) / support + (period : ℝ) := by
  let character : ℕ := (support - shift) % support
  let quotient : ℕ :=
    (numerator * support + character * denominator) /
      (denominator * support)
  have hnormalized :=
    ternaryMajorArc_normalized_center_eq_rational_add_character_sub_quotient
      support denominator numerator character hsupport hdenominator
  have hsupportReal : (support : ℝ) ≠ 0 := by
    exact_mod_cast hsupport.ne'
  by_cases hzero : shift = 0
  · subst shift
    have hcharacter : character = 0 := by
      simp [character]
    refine ⟨-(quotient : ℤ), ?_⟩
    rw [hnormalized]
    rw [show
      (numerator * support + character * denominator) /
        (denominator * support) = quotient from rfl,
      hcharacter]
    push_cast
    ring
  · have hpositive : 0 < shift := Nat.pos_of_ne_zero hzero
    have hcharacter : character = support - shift := by
      dsimp [character]
      exact Nat.mod_eq_of_lt (Nat.sub_lt hsupport hpositive)
    have hcharacterPhase :
        (character : ℝ) / support =
          1 - (shift : ℝ) / support := by
      rw [hcharacter, Nat.cast_sub (Nat.le_of_lt hshift)]
      field_simp
    refine ⟨1 - (quotient : ℤ), ?_⟩
    rw [hnormalized, hcharacterPhase]
    push_cast
    ring

/-- At a genuine normalized NEGATED-character real center, its actual
canonical widest-anchor coefficient is exactly the coefficient of the
ORIGINAL `h/q-j/W` anchor, independent of its integer periodic lift. -/
theorem ternaryMajorArc_canonical_normalized_coefficient_eq_original
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff denominator numerator shift : ℕ)
    (center : ActualMajorArcGlobalCenter (∏ p ∈ S, p) cutoff)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hnumerator : Nat.Coprime numerator denominator)
    (hshift : shift < ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime denominator (∏ p ∈ S, p))
    (hcenter : center.val =
      actualMajorArcCenterReindexNormalizedCenter
        (∏ p ∈ S, p) denominator numerator
          (((∏ p ∈ S, p) - shift) % (∏ p ∈ S, p))) :
    actualCenterCouplingAnchorCoefficient S b target a d
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center) =
      actualCenterCouplingAnchorCoefficient S b target a d
        (denominator, (numerator : ℤ), (shift : ℤ)) := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  obtain ⟨representative, hrepresentative,
      hrepresentativeDenominator, hrepresentativeCenter⟩ :=
    actualMajorArcCenterReindex_normalized_center_actual_anchor
      W cutoff denominator numerator ((W - shift) % W)
        hW hdenominator hcutoff hnumerator
  have hcenterRepresentative : shiftedFareyAnchorCenter
      W representative.1 representative.2.1 representative.2.2 =
        center.val := hrepresentativeCenter.trans hcenter.symm
  have hrepresentativeCoprime :
      Nat.Coprime representative.1 W := by
    rwa [hrepresentativeDenominator]
  have hcanonicalDenominator :=
    actualConductorDedup_canonical_denominator_eq_support_free
      W cutoff fareyCutoff center representative hW hrepresentative
        hcenterRepresentative hrepresentativeCoprime
  have hdenominatorCanonical :
      (actualMajorArcGlobalCanonicalWidestAnchor
        W cutoff fareyCutoff center).1 = denominator :=
    hcanonicalDenominator.trans hrepresentativeDenominator
  obtain ⟨period, hperiod⟩ :=
    ternaryMajorArc_normalized_negative_character_eq_anchor_add_integer
      W denominator numerator shift hW hdenominator hshift
  apply ternaryMajorArc_anchor_coefficient_eq_of_periodic_centers
    S b target a d
      (actualMajorArcGlobalCanonicalWidestAnchor
        W cutoff fareyCutoff center)
      (denominator, (numerator : ℤ), (shift : ℤ)) period
  · exact hdenominatorCanonical
  · omega
  · exact hsupport
  · rw [(actualMajorArcGlobalCanonicalWidestAnchor_spec
      W cutoff fareyCutoff center).2.1,
      hcenter, hperiod]
    simp [shiftedFareyAnchorCenter, W]

/-- The complete actual canonical selected-cell coefficient at a real
center, extended by zero outside the genuine original center family. -/
noncomputable def ternaryMajorArcCanonicalRealCenterCoefficient
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff : ℕ)
    (center : ℝ) : ℂ :=
  if hcenter : center ∈ shiftedFareyCenterClasses (∏ p ∈ S, p)
      (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff)
    then actualCenterCouplingAnchorCoefficient S b target a d
      (actualMajorArcGlobalCanonicalWidestAnchor
        (∏ p ∈ S, p) cutoff fareyCutoff ⟨center, hcenter⟩)
    else 0

/-- The FULL actual signed canonical-widest coefficient on one
deduplicated half-open conductor stratum equals the COMPLETE ORIGINAL
reduced-numerator/support-shift anchor coefficient orbit.  Every real
center, integer periodic lift, and negative support-character sign is
accounted for exactly. -/
theorem ternaryMajorArc_canonical_stratum_coefficients_eq_original_orbit
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d cutoff fareyCutoff denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator (∏ p ∈ S, p)) :
    (∑ center ∈ actualConductorDedupCanonicalStratum
        (∏ p ∈ S, p) cutoff fareyCutoff denominator,
      ternaryMajorArcCanonicalRealCenterCoefficient
        S b target a d cutoff fareyCutoff center) =
      ∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range (∏ p ∈ S, p),
          actualCenterCouplingAnchorCoefficient S b target a d
            (denominator, (numerator : ℤ), (shift : ℤ)) := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  rw [actualConductorDedup_canonical_stratum_sum_neg_character
    W cutoff fareyCutoff denominator hW hdenominator hcutoff hcoprime
      (ternaryMajorArcCanonicalRealCenterCoefficient
        S b target a d cutoff fareyCutoff)]
  apply Finset.sum_congr rfl
  intro numerator hnumerator
  have hnum : Nat.Coprime numerator denominator :=
    (Finset.mem_filter.mp hnumerator).2
  apply Finset.sum_congr rfl
  intro shift hshift
  have hshiftBound : shift < W := Finset.mem_range.mp hshift
  let normalized : ℝ :=
    actualMajorArcCenterReindexNormalizedCenter
      W denominator numerator ((W - shift) % W)
  have hmember : normalized ∈ shiftedFareyCenterClasses W
      (actualShiftedFareyAnchors W cutoff) :=
    actualMajorArcCenterReindex_normalized_center_mem_actual_classes
      W cutoff denominator numerator ((W - shift) % W)
        hW hdenominator hcutoff hnum
  change
    ternaryMajorArcCanonicalRealCenterCoefficient
      S b target a d cutoff fareyCutoff normalized = _
  unfold ternaryMajorArcCanonicalRealCenterCoefficient
  split
  next hactual =>
    exact ternaryMajorArc_canonical_normalized_coefficient_eq_original
      S b target a d cutoff fareyCutoff denominator numerator shift
        ⟨normalized, hactual⟩ hsupport hdenominator hcutoff hnum
        hshiftBound hcoprime rfl
  next hnot =>
    exact False.elim (hnot hmember)

/-- Every complete reduced-numerator/support-shift family of ACTUAL
integrated-anchor coefficients equals the already audited genuine shifted
three-cell phase density, at the exact common modulus `lcm(q,W)`. -/
theorem ternaryMajorArc_all_anchor_coefficients_eq_shifted_density
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ)
    (hdenominator : 0 < denominator)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (∑ numerator ∈ (Finset.range denominator).filter
        (fun numerator => Nat.gcd numerator denominator = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        actualCenterCouplingAnchorCoefficient S b target a d
          (denominator, (numerator : ℤ), (shift : ℤ))) =
      (∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range (∏ p ∈ S, p),
          ∑ triple ∈ actualMajorArcLcmAdmissibleCellTriples
              S b target a d denominator,
            actualMajorArcSquarefreeTriplePhase
              triple.1 triple.2.1 triple.2.2 a d
                ((numerator : ℝ) / denominator -
                  (shift : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ))) /
        (Nat.totient (actualMajorArcLcmResidueModulus
          S denominator) : ℂ) ^ 3 := by
  unfold actualCenterCouplingAnchorCoefficient
  simp_rw [ternaryMajorArc_anchor_cell_phase_eq_shifted_phase
    S denominator _ _ _ a d _ _ hdenominator hsupport]
  simp only [Int.cast_natCast]
  simp_rw [← Finset.sum_mul]
  simp [div_eq_mul_inv]

/-- At each genuine odd outside denominator, the COMPLETE signed sum of
actual integrated-anchor coefficients is exactly the indispensable
`a*d`-compensated support weight times `μ(r)/φ(r)²`. -/
theorem ternaryMajorArc_actual_odd_anchor_coefficient_sum
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
    (∑ numerator ∈ (Finset.range outside).filter
        (fun numerator => Nat.gcd numerator outside = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        actualCenterCouplingAnchorCoefficient S b target a d
          (outside, (numerator : ℤ), (shift : ℤ))) =
      (((a : ℂ) * d *
        (actualFixedLabelDoubleCoefficientWeight S target b a d : ℂ)) /
          (Nat.totient (∏ p ∈ S, p) : ℂ)) *
        ((ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2) := by
  rw [ternaryMajorArc_all_anchor_coefficients_eq_shifted_density
    S b target a d outside houtside (fun p hp => (hsupport p hp).1)]
  exact actualMajorArcParity_actual_odd_center_normalized_factor
    S b target a d outside hsupport ha hd had
      htargetRange htarget hb houtside hcoprime hcoeff

/-- At the genuinely parity-doubled original denominator `2*r`, the FULL
sum of actual integrated-anchor coefficients is the SAME signed outside
factor, while its original Farey width remains the separate `2*r` width. -/
theorem ternaryMajorArc_actual_doubled_anchor_coefficient_sum
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
    (hodd : Nat.Coprime 2 outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (hcoeff : Nat.Coprime outside (2 * a * d)) :
    (∑ numerator ∈ (Finset.range (2 * outside)).filter
        (fun numerator => Nat.gcd numerator (2 * outside) = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        actualCenterCouplingAnchorCoefficient S b target a d
          (2 * outside, (numerator : ℤ), (shift : ℤ))) =
      (((a : ℂ) * d *
        (actualFixedLabelDoubleCoefficientWeight S target b a d : ℂ)) /
          (Nat.totient (∏ p ∈ S, p) : ℂ)) *
        ((ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2) := by
  rw [ternaryMajorArc_all_anchor_coefficients_eq_shifted_density
    S b target a d (2 * outside) (by omega)
      (fun p hp => (hsupport p hp).1)]
  exact actualMajorArcParity_actual_doubled_center_normalized_factor
    S b target a d outside hsupport ha hd had
      htargetRange htarget hb houtside hodd hcoprime hcoeff

/-- The complete ORIGINAL-anchor complex smooth mass at one fixed
denominator, summed over every reduced numerator and every support shift.
Arcs are deliberately unclipped: equivalence with distinct unit-circle
centers still requires a genuine periodic-boundary/deduplication theorem. -/
noncomputable def ternaryMajorArcOriginalAnchorOrbitSmoothMass
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d denominator fareyCutoff : ℕ)
    (τ ell : ℝ) : ℂ :=
  ∑ numerator ∈ (Finset.range denominator).filter
      (fun numerator => Nat.gcd numerator denominator = 1),
    ∑ shift ∈ Finset.range (∏ p ∈ S, p),
      ∫ α in shiftedFareyAnchorArc
          (∏ p ∈ S, p) fareyCutoff denominator numerator shift,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell
            (denominator, (numerator : ℤ), (shift : ℤ)) α

/-- The exact denominator-dependent middle integral corresponding to the
original anchor width `1/(q*(Q+1))`. -/
noncomputable def ternaryMajorArcOriginalDenominatorMiddleIntegral
    (a d n denominator fareyCutoff : ℕ)
    (τ ell : ℝ) : ℂ :=
  ∫ β in Set.Icc
      (1 / ((denominator : ℝ) * ((fareyCutoff : ℝ) + 1)))
      (1 - 1 / ((denominator : ℝ) * ((fareyCutoff : ℝ) + 1))),
    actualMajorArcArchimedeanSmoothCubic a d n τ ell β

/-- Exact full reduced-numerator/support-shift anchor integration: the
TOTAL actual signed anchor coefficient multiplies the true affine lattice
minus the denominator-specific signed resonant middle tail. -/
theorem ternaryMajorArc_original_anchor_orbit_eq_coefficient_lattice_sub_tail
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d denominator fareyCutoff : ℕ)
    (τ ell : ℝ)
    (hdenominator : 0 < denominator)
    (hfarey : 0 < fareyCutoff) :
    ternaryMajorArcOriginalAnchorOrbitSmoothMass
        S b n target a d denominator fareyCutoff τ ell =
      (∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range (∏ p ∈ S, p),
          actualCenterCouplingAnchorCoefficient S b target a d
            (denominator, (numerator : ℤ), (shift : ℤ))) *
        (((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
            ternaryMajorArcOriginalDenominatorMiddleIntegral
              a d n denominator fareyCutoff τ ell) := by
  unfold ternaryMajorArcOriginalAnchorOrbitSmoothMass
  calc
    (∑ numerator ∈ (Finset.range denominator).filter
        (fun numerator => Nat.gcd numerator denominator = 1),
      ∑ shift ∈ Finset.range (∏ p ∈ S, p),
        ∫ α in shiftedFareyAnchorArc
            (∏ p ∈ S, p) fareyCutoff denominator numerator shift,
          actualMajorArcIntegratedAnchorSmooth
            S b n target a d τ ell
              (denominator, (numerator : ℤ), (shift : ℤ)) α) =
      ∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range (∏ p ∈ S, p),
          actualCenterCouplingAnchorCoefficient S b target a d
            (denominator, (numerator : ℤ), (shift : ℤ)) *
            (((ternaryAffineTriples
              (actualMajorArcArchimedeanLeftWindow a n)
              (actualMajorArcArchimedeanCenterWindow d n)
              (actualMajorArcArchimedeanLabelWindow τ ell n)
              a (2 * d)).card : ℂ) -
              ternaryMajorArcOriginalDenominatorMiddleIntegral
                a d n denominator fareyCutoff τ ell) := by
      apply Finset.sum_congr rfl
      intro numerator hnumerator
      apply Finset.sum_congr rfl
      intro shift hshift
      simpa [actualCenterCouplingAnchorRadius,
        ternaryMajorArcOriginalDenominatorMiddleIntegral] using
          actualCenterCoupling_anchor_integral_eq_signed_lattice_sub_tail
            S b n target a d fareyCutoff τ ell
              (denominator, (numerator : ℤ), (shift : ℤ))
                hdenominator hfarey
    _ = _ := by
      simp_rw [← Finset.sum_mul]

/-- EXACT actual-canonical periodic-boundary gluing: the TWO distinct real
centers `0` and `1`, with their genuine widest original anchors and
separately clipped half arcs, contribute ONE full signed principal lattice
term minus its true denominator-one resonant middle tail. -/
theorem ternaryMajorArc_canonical_boundary_pair_eq_principal_lattice_sub_tail
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ)
    (τ ell : ℝ)
    (zeroCenter oneCenter : ActualMajorArcGlobalCenter
      (∏ p ∈ S, p) cutoff)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcutoff : 0 < cutoff)
    (hfarey : 0 < fareyCutoff)
    (hzero : zeroCenter.val = 0)
    (hone : oneCenter.val = 1) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
          (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff)
            zeroCenter.val,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            (∏ p ∈ S, p) cutoff fareyCutoff zeroCenter) α) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        shiftedFareyCenterRegion (∏ p ∈ S, p) fareyCutoff
          (actualShiftedFareyAnchors (∏ p ∈ S, p) cutoff)
            oneCenter.val,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            (∏ p ∈ S, p) cutoff fareyCutoff oneCenter) α) =
      actualCenterCouplingAnchorCoefficient S b target a d
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff zeroCenter) *
        (((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
          ternaryMajorArcOriginalDenominatorMiddleIntegral
            a d n 1 fareyCutoff τ ell) := by
  let W : ℕ := ∏ p ∈ S, p
  let zeroAnchor := actualMajorArcGlobalCanonicalWidestAnchor
    W cutoff fareyCutoff zeroCenter
  let oneAnchor := actualMajorArcGlobalCanonicalWidestAnchor
    W cutoff fareyCutoff oneCenter
  let coefficient := actualCenterCouplingAnchorCoefficient
    S b target a d zeroAnchor
  let radius : ℝ := 1 / ((fareyCutoff : ℝ) + 1)
  let smooth := actualMajorArcArchimedeanSmoothCubic a d n τ ell
  have hW : 0 < W :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hcoeff : actualCenterCouplingAnchorCoefficient
      S b target a d zeroAnchor =
      actualCenterCouplingAnchorCoefficient
        S b target a d oneAnchor :=
    ternaryMajorArc_canonical_boundary_coefficients_eq
      S b target a d cutoff fareyCutoff zeroCenter oneCenter
        hsupport hcutoff hzero hone
  have hzeroPhase (α : ℝ) :
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell zeroAnchor α =
        coefficient * smooth α := by
    rw [actualCenterCoupling_anchor_smooth_eq_coefficient_mul,
      (actualMajorArcGlobalCanonicalWidestAnchor_spec
        W cutoff fareyCutoff zeroCenter).2.1,
      hzero]
    simp [coefficient, smooth]
  have honePhase (α : ℝ) :
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell oneAnchor α =
        coefficient * smooth α := by
    rw [actualCenterCoupling_anchor_smooth_eq_coefficient_mul,
      (actualMajorArcGlobalCanonicalWidestAnchor_spec
        W cutoff fareyCutoff oneCenter).2.1,
      hone, ← hcoeff]
    have hperiod :=
      actualMajorArcBoundary_smooth_cubic_periodic a d n τ ell
        (α - 1)
    have hshift : smooth (α - 1) = smooth α := by
      simpa [smooth] using hperiod.symm
    change coefficient * smooth (α - 1) = coefficient * smooth α
    rw [hshift]
  have hnonnegative : 0 ≤ radius := by
    dsimp [radius]
    positivity
  have hless : radius < 1 := by
    dsimp [radius]
    apply (div_lt_one (by positivity :
      (0 : ℝ) < (fareyCutoff : ℝ) + 1)).mpr
    have hpositive : (0 : ℝ) < fareyCutoff := by
      exact_mod_cast hfarey
    linarith
  have htwo : 2 * radius ≤ 1 := by
    calc
      2 * radius = 2 / ((fareyCutoff : ℝ) + 1) := by
        dsimp [radius]
        ring
      _ ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        have hpositive : (1 : ℝ) ≤ fareyCutoff := by
          exact_mod_cast hfarey
        linarith
  rw [hzero, hone,
    actualMajorArcBoundary_actual_zero_center_region
      W cutoff fareyCutoff hW hcutoff,
    actualMajorArcBoundary_actual_one_center_region
      W cutoff fareyCutoff hW hcutoff]
  change
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      Metric.closedBall (0 : ℝ) radius,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell zeroAnchor α) +
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩
      Metric.closedBall (1 : ℝ) radius,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell oneAnchor α) = _
  calc
    _ =
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        Metric.closedBall (0 : ℝ) radius,
          coefficient * smooth α) +
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩
        Metric.closedBall (1 : ℝ) radius,
          coefficient * smooth α) := by
      congr 1
      · apply setIntegral_congr_fun
          (measurableSet_Ioc.inter Metric.isClosed_closedBall.measurableSet)
        intro α hα
        exact hzeroPhase α
      · apply setIntegral_congr_fun
          (measurableSet_Ioc.inter Metric.isClosed_closedBall.measurableSet)
        intro α hα
        exact honePhase α
    _ = coefficient *
        ((∫ α in Set.Ioc (0 : ℝ) 1 ∩
            Metric.closedBall (0 : ℝ) radius, smooth α) +
          (∫ α in Set.Ioc (0 : ℝ) 1 ∩
            Metric.closedBall (1 : ℝ) radius, smooth α)) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      ring
    _ = coefficient *
        (∫ α in Set.Icc (-radius) radius, smooth α) := by
      rw [actualMajorArcBoundary_actual_smooth_half_arcs_eq_symmetric
        a d n τ ell radius hnonnegative hless]
    _ = _ := by
      rw [actualMajorArcBoundary_smooth_symmetric_eq_lattice_sub_middle
        a d n τ ell radius hnonnegative htwo]
      simp [coefficient, zeroAnchor, W, radius,
        ternaryMajorArcOriginalDenominatorMiddleIntegral]

/-- Exact complete genuine odd-outside original-anchor smooth mass: the
true compensated signed Möbius coefficient multiplies its real affine
lattice count minus its OWN original denominator-specific middle tail. -/
theorem ternaryMajorArc_actual_odd_orbit_eq_signed_lattice_sub_tail
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d outside fareyCutoff : ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (had : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (houtside : 0 < outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (hcoeff : Nat.Coprime outside (2 * a * d))
    (hfarey : 0 < fareyCutoff) :
    ternaryMajorArcOriginalAnchorOrbitSmoothMass
        S b n target a d outside fareyCutoff τ ell =
      ((((a : ℂ) * d *
        (actualFixedLabelDoubleCoefficientWeight S target b a d : ℂ)) /
          (Nat.totient (∏ p ∈ S, p) : ℂ)) *
        ((ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2)) *
        (((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
            ternaryMajorArcOriginalDenominatorMiddleIntegral
              a d n outside fareyCutoff τ ell) := by
  rw [ternaryMajorArc_original_anchor_orbit_eq_coefficient_lattice_sub_tail
    S b n target a d outside fareyCutoff τ ell houtside hfarey,
    ternaryMajorArc_actual_odd_anchor_coefficient_sum
      S b target a d outside hsupport ha hd had
        htargetRange htarget hb houtside hcoprime hcoeff]

/-- Exact complete genuine parity-doubled original-anchor smooth mass.
Its signed outside coefficient equals the odd family's coefficient, but
its middle tail uses the DISTINCT true `2*r` Farey width. -/
theorem ternaryMajorArc_actual_doubled_orbit_eq_signed_lattice_sub_tail
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d outside fareyCutoff : ℕ)
    (τ ell : ℝ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (had : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (houtside : 0 < outside)
    (hodd : Nat.Coprime 2 outside)
    (hcoprime : Nat.Coprime (∏ p ∈ S, p) outside)
    (hcoeff : Nat.Coprime outside (2 * a * d))
    (hfarey : 0 < fareyCutoff) :
    ternaryMajorArcOriginalAnchorOrbitSmoothMass
        S b n target a d (2 * outside) fareyCutoff τ ell =
      ((((a : ℂ) * d *
        (actualFixedLabelDoubleCoefficientWeight S target b a d : ℂ)) /
          (Nat.totient (∏ p ∈ S, p) : ℂ)) *
        ((ArithmeticFunction.moebius outside : ℂ) /
          (Nat.totient outside : ℂ) ^ 2)) *
        (((ternaryAffineTriples
          (actualMajorArcArchimedeanLeftWindow a n)
          (actualMajorArcArchimedeanCenterWindow d n)
          (actualMajorArcArchimedeanLabelWindow τ ell n)
          a (2 * d)).card : ℂ) -
            ternaryMajorArcOriginalDenominatorMiddleIntegral
              a d n (2 * outside) fareyCutoff τ ell) := by
  rw [ternaryMajorArc_original_anchor_orbit_eq_coefficient_lattice_sub_tail
    S b n target a d (2 * outside) fareyCutoff τ ell (by omega) hfarey,
    ternaryMajorArc_actual_doubled_anchor_coefficient_sum
      S b target a d outside hsupport ha hd had
        htargetRange htarget hb houtside hodd hcoprime hcoeff]

end Erdos689

#print axioms Erdos689.ternaryMajorArc_anchor_cell_phase_eq_shifted_phase
#print axioms Erdos689.ternaryMajorArc_anchor_coefficient_support_shift_sum
#print axioms Erdos689.ternaryMajorArc_triple_phase_add_integer
#print axioms Erdos689.ternaryMajorArc_anchor_coefficient_eq_of_periodic_centers
#print axioms Erdos689.ternaryMajorArc_anchor_coefficient_eq_of_same_center
#print axioms Erdos689.ternaryMajorArc_canonical_boundary_coefficients_eq
#print axioms Erdos689.ternaryMajorArc_normalized_center_eq_rational_add_character_sub_quotient
#print axioms Erdos689.ternaryMajorArc_normalized_negative_character_eq_anchor_add_integer
#print axioms Erdos689.ternaryMajorArc_canonical_normalized_coefficient_eq_original
#print axioms Erdos689.ternaryMajorArc_canonical_stratum_coefficients_eq_original_orbit
#print axioms Erdos689.ternaryMajorArc_all_anchor_coefficients_eq_shifted_density
#print axioms Erdos689.ternaryMajorArc_actual_odd_anchor_coefficient_sum
#print axioms Erdos689.ternaryMajorArc_actual_doubled_anchor_coefficient_sum
#print axioms Erdos689.ternaryMajorArc_original_anchor_orbit_eq_coefficient_lattice_sub_tail
#print axioms Erdos689.ternaryMajorArc_canonical_boundary_pair_eq_principal_lattice_sub_tail
#print axioms Erdos689.ternaryMajorArc_actual_odd_orbit_eq_signed_lattice_sub_tail
#print axioms Erdos689.ternaryMajorArc_actual_doubled_orbit_eq_signed_lattice_sub_tail
