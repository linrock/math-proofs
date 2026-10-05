module

public import ActualMajorArcCenterReduction433
public import ActualMajorArcCenterReindex433
public import ActualMajorArcGlobalErrorAssembly433
public import ActualMajorArcParityCRT433

@[expose] public section


/-!
# Genuine canonical widest-center conductor classification

The global major-arc model chooses an actual widest original Farey anchor
for each distinct real center.  Existing support-free reanchoring alone does
not identify the denominator chosen by that canonical representative.  The
results here recover its genuine denominator minimality from the exact union
of all duplicate-center intervals, then transfer support-conductor
classification to the actual canonical model.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- The canonical actual widest anchor has no larger original denominator
than ANY original anchor representing its same exact real center.  This
uses its genuine full center-region equality, not an assumed choice rule. -/
theorem actualConductorDedup_canonical_denominator_le
    (support cutoff fareyCutoff : ℕ)
    (center : ActualMajorArcGlobalCenter support cutoff)
    (other : ShiftedFareyAnchor)
    (hother : other ∈ actualShiftedFareyAnchors support cutoff)
    (hcenter : shiftedFareyAnchorCenter
      support other.1 other.2.1 other.2.2 = center.val) :
    (actualMajorArcGlobalCanonicalWidestAnchor
      support cutoff fareyCutoff center).1 ≤ other.1 := by
  let canonical := actualMajorArcGlobalCanonicalWidestAnchor
    support cutoff fareyCutoff center
  obtain ⟨hcanonical, hcanonicalCenter, hcanonicalRegion⟩ :=
    actualMajorArcGlobalCanonicalWidestAnchor_spec
      support cutoff fareyCutoff center
  have hcanonicalPositive : 0 < canonical.1 :=
    (actualShiftedFareyAnchors_denominator_bounds
      support cutoff canonical hcanonical).1
  have hotherPositive : 0 < other.1 :=
    (actualShiftedFareyAnchors_denominator_bounds
      support cutoff other hother).1
  let radius : ℝ := 1 / ((other.1 : ℝ) * (fareyCutoff + 1))
  have hradius : 0 ≤ radius := by
    dsimp [radius]
    positivity
  have hpoint : center.val + radius ∈
      shiftedFareyAnchorArc support fareyCutoff
        other.1 other.2.1 other.2.2 := by
    unfold shiftedFareyAnchorArc
    rw [hcenter, Metric.mem_closedBall, Real.dist_eq]
    change |center.val + radius - center.val| ≤ radius
    simp [abs_of_nonneg hradius]
  have hregion : center.val + radius ∈
      shiftedFareyCenterRegion support fareyCutoff
        (actualShiftedFareyAnchors support cutoff) center.val := by
    simp only [shiftedFareyCenterRegion, Set.mem_iUnion]
    exact ⟨other, Finset.mem_filter.mpr
      ⟨hother, hcenter⟩, hpoint⟩
  rw [hcanonicalRegion] at hregion
  unfold shiftedFareyAnchorArc at hregion
  rw [hcanonicalCenter, Metric.mem_closedBall, Real.dist_eq] at hregion
  have hradial : radius ≤
      1 / ((canonical.1 : ℝ) * (fareyCutoff + 1)) := by
    simpa [abs_of_nonneg hradius] using hregion
  have hotherDen : (0 : ℝ) <
      (other.1 : ℝ) * (fareyCutoff + 1) := by positivity
  have hcanonicalDen : (0 : ℝ) <
      (canonical.1 : ℝ) * (fareyCutoff + 1) := by positivity
  dsimp [radius] at hradial
  have hreverse := (div_le_div_iff₀ hotherDen hcanonicalDen).mp hradial
  norm_num at hreverse
  have hQ : (0 : ℝ) < (fareyCutoff : ℝ) + 1 := by positivity
  have hreal : (canonical.1 : ℝ) ≤ other.1 := by
    nlinarith
  exact_mod_cast hreal

/-- If a genuine center admits ANY original support-coprime anchor, the
canonical widest anchor has EXACTLY that same support-free denominator.
Thus its Farey radius is the true outside-conductor radius. -/
theorem actualConductorDedup_canonical_denominator_eq_support_free
    (support cutoff fareyCutoff : ℕ)
    (center : ActualMajorArcGlobalCenter support cutoff)
    (other : ShiftedFareyAnchor)
    (hsupport : 0 < support)
    (hother : other ∈ actualShiftedFareyAnchors support cutoff)
    (hcenter : shiftedFareyAnchorCenter
      support other.1 other.2.1 other.2.2 = center.val)
    (hcoprime : Nat.Coprime other.1 support) :
    (actualMajorArcGlobalCanonicalWidestAnchor
      support cutoff fareyCutoff center).1 = other.1 := by
  let canonical := actualMajorArcGlobalCanonicalWidestAnchor
    support cutoff fareyCutoff center
  obtain ⟨hcanonical, hcanonicalCenter, _⟩ :=
    actualMajorArcGlobalCanonicalWidestAnchor_spec
      support cutoff fareyCutoff center
  have hcanonicalPositive : 0 < canonical.1 :=
    (actualShiftedFareyAnchors_denominator_bounds
      support cutoff canonical hcanonical).1
  have hotherPositive : 0 < other.1 :=
    (actualShiftedFareyAnchors_denominator_bounds
      support cutoff other hother).1
  have hreduced := actualMajorArcCenter_actual_anchor_numerator_coprime
    support cutoff other hother
  have hdivides : other.1 ∣ canonical.1 :=
    actualMajorArcCenterReduction_support_free_denominator_dvd
      support other.1 canonical.1
      other.2.1 other.2.2 canonical.2.1 canonical.2.2
      hsupport hotherPositive hcanonicalPositive hreduced hcoprime
        (hcenter.trans hcanonicalCenter.symm)
  exact Nat.le_antisymm
    (actualConductorDedup_canonical_denominator_le
      support cutoff fareyCutoff center other hother hcenter)
    (Nat.le_of_dvd hcanonicalPositive hdivides)

/-- At every genuine nonempty unit-circle center, its actual canonical
widest original anchor either carries a support-prime square and its FULL
smooth cubic vanishes, or its OWN denominator is support-coprime.
The surviving global model therefore uses the true outside denominator,
not merely a hypothetical differently indexed reanchor. -/
theorem actualConductorDedup_canonical_support_square_or_coprime
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ) (τ ell : ℝ)
    (center : ActualMajorArcGlobalCenter (∏ p ∈ S, p) cutoff)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcenterZero : 0 ≤ center.val)
    (hcenterOne : center.val ≤ 1) :
    (∃ p ∈ S,
      p ^ 2 ∣
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center).1 ∧
      ∀ α : ℝ,
        actualMajorArcIntegratedAnchorSmooth
          S b n target a d τ ell
          (actualMajorArcGlobalCanonicalWidestAnchor
            (∏ p ∈ S, p) cutoff fareyCutoff center) α = 0) ∨
      Nat.Coprime
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center).1
        (∏ p ∈ S, p) := by
  let W := ∏ p ∈ S, p
  let canonical := actualMajorArcGlobalCanonicalWidestAnchor
    W cutoff fareyCutoff center
  obtain ⟨hcanonical, hcanonicalCenter, _⟩ :=
    actualMajorArcGlobalCanonicalWidestAnchor_spec
      W cutoff fareyCutoff center
  have hW : 0 < W :=
    Finset.prod_pos fun p hp => (hsupport p hp).pos
  obtain hzero | hreanchor :=
    actualMajorArcCenterReduction_actual_anchor_dichotomy
      S b n target a d cutoff τ ell canonical hsupport
      hcanonical (hcanonicalCenter.symm ▸ hcenterZero)
        (hcanonicalCenter.symm ▸ hcenterOne)
  · exact Or.inl hzero
  · obtain ⟨replacement, hreplacement, _, hcoprime,
        hreplacementCenter⟩ := hreanchor
    right
    have hcenterReplacement : shiftedFareyAnchorCenter
        W replacement.1 replacement.2.1 replacement.2.2 = center.val :=
      hreplacementCenter.trans hcanonicalCenter
    have hdenominator :=
      actualConductorDedup_canonical_denominator_eq_support_free
        W cutoff fareyCutoff center replacement hW
        hreplacement hcenterReplacement hcoprime
    rw [hdenominator]
    exact hcoprime

/-- The actual canonical smooth cubic can be nonzero only at a genuine
support-coprime original denominator. -/
theorem actualConductorDedup_canonical_coprime_of_smooth_ne_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ) (τ ell : ℝ)
    (center : ActualMajorArcGlobalCenter (∏ p ∈ S, p) cutoff)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hcenterZero : 0 ≤ center.val)
    (hcenterOne : center.val ≤ 1)
    (hnonzero : ∃ α : ℝ,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center) α ≠ 0) :
    Nat.Coprime
      (actualMajorArcGlobalCanonicalWidestAnchor
        (∏ p ∈ S, p) cutoff fareyCutoff center).1
      (∏ p ∈ S, p) := by
  obtain hzero | hcoprime :=
    actualConductorDedup_canonical_support_square_or_coprime
      S b n target a d cutoff fareyCutoff τ ell center
      hsupport hcenterZero hcenterOne
  · obtain ⟨_, _, _, hvanish⟩ := hzero
    obtain ⟨α, hα⟩ := hnonzero
    exact False.elim (hα (hvanish α))
  · exact hcoprime

/-- A positive support-coprime conductor with no factor four is EXACTLY
either an odd outside conductor `r` or its unique genuine parity companion
`2*r`, with `r` coprime to the complete excluded modulus `2*W`. -/
theorem actualConductorDedup_odd_or_twice_odd
    (support denominator : ℕ)
    (hcoprime : Nat.Coprime denominator support)
    (hfour : ¬ 4 ∣ denominator) :
    (¬ 2 ∣ denominator ∧ Nat.Coprime denominator (2 * support)) ∨
      ∃ outside : ℕ,
        denominator = 2 * outside ∧ ¬ 2 ∣ outside ∧
          Nat.Coprime outside (2 * support) := by
  by_cases htwo : 2 ∣ denominator
  · right
    let outside := denominator / 2
    have hrepresentation : denominator = 2 * outside := by
      exact (Nat.mul_div_cancel' htwo).symm
    have houtsideOdd : ¬ 2 ∣ outside := by
      intro hdivide
      apply hfour
      rw [hrepresentation]
      obtain ⟨k, hk⟩ := hdivide
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    have houtsideDivide : outside ∣ denominator := by
      rw [hrepresentation]
      exact dvd_mul_left outside 2
    have houtsideSupport : Nat.Coprime outside support :=
      hcoprime.coprime_dvd_left houtsideDivide
    have houtsideTwo : Nat.Coprime outside 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr houtsideOdd).symm
    exact ⟨outside, hrepresentation, houtsideOdd,
      (Nat.coprime_mul_iff_right).mpr
        ⟨houtsideTwo, houtsideSupport⟩⟩
  · left
    have hdenominatorTwo : Nat.Coprime denominator 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr htwo).symm
    exact ⟨htwo, (Nat.coprime_mul_iff_right).mpr
      ⟨hdenominatorTwo, hcoprime⟩⟩

/-- EVERY genuine original shifted anchor with denominator divisible by
four has identically zero FULL selected smooth cubic, including its signed
already-lifted numerator and all three true common-modulus unit filters. -/
theorem actualConductorDedup_actual_anchor_smooth_zero_of_four_dvd
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff : ℕ) (τ ell : ℝ)
    (anchor : ShiftedFareyAnchor)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hanchor : anchor ∈ actualShiftedFareyAnchors
      (∏ p ∈ S, p) cutoff)
    (hfour : 4 ∣ anchor.1) :
    ∀ α : ℝ,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell anchor α = 0 := by
  intro α
  have hdenominator :=
    (actualShiftedFareyAnchors_denominator_bounds
      (∏ p ∈ S, p) cutoff anchor hanchor).1
  have hcoprime := actualMajorArcCenter_actual_anchor_numerator_coprime
    (∏ p ∈ S, p) cutoff anchor hanchor
  obtain ⟨reduced, lift, _, hreduced, hrepresentation⟩ :=
    actualMajorArcCenter_signed_numerator_eq_nat_plus_lift
      anchor.1 anchor.2.1 hdenominator hcoprime
  let L := actualMajorArcLcmResidueModulus S anchor.1
  have hdivide : anchor.1 ∣ L :=
    (actualMajorArcLcmResidueModulus_divisibility S anchor.1).1
  have hfactor : anchor.1 * (L / anchor.1) = L :=
    Nat.mul_div_cancel' hdivide
  have hfactorInt :
      (anchor.1 : ℤ) * ((L / anchor.1 : ℕ) : ℤ) = (L : ℤ) := by
    exact_mod_cast hfactor
  have hfrequency :
      actualMajorArcIntegratedAnchorNumerator S anchor =
        actualMajorArcSingularShiftedNumerator
          S anchor.1 reduced anchor.2.2 lift := by
    unfold actualMajorArcIntegratedAnchorNumerator
      actualMajorArcSingularShiftedNumerator
    rw [hrepresentation, ← hfactorInt]
    ring
  unfold actualMajorArcIntegratedAnchorSmooth
  rw [hfrequency]
  exact actualMajorArcParity_admissible_smooth_zero_of_four_dvd
    S b n anchor.1 reduced target a d anchor.2.2 lift τ ell
      (α - shiftedFareyAnchorCenter
        (∏ p ∈ S, p) anchor.1 anchor.2.1 anchor.2.2)
      hsupport hdenominator hfour hreduced

/-- COMPLETE actual-canonical conductor classification: every genuine
nonempty-circle widest center either has identically zero selected smooth
cubic or belongs to exactly the two surviving original denominator families
`r` and `2*r`, with positive odd `r` coprime to the full excluded support
`2W` and inside the true Farey cutoff.  No artificial reanchor, duplicate
center, periodic lift, or discarded unit selector appears. -/
theorem actualConductorDedup_canonical_zero_or_outside_parity
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff fareyCutoff : ℕ) (τ ell : ℝ)
    (center : ActualMajorArcGlobalCenter (∏ p ∈ S, p) cutoff)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hcenterZero : 0 ≤ center.val)
    (hcenterOne : center.val ≤ 1) :
    (∀ α : ℝ,
      actualMajorArcIntegratedAnchorSmooth
        S b n target a d τ ell
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center) α = 0) ∨
      ∃ outside : ℕ, 0 < outside ∧ outside ≤ cutoff ∧
        ¬ 2 ∣ outside ∧
        Nat.Coprime outside (2 * (∏ p ∈ S, p)) ∧
        ((actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center).1 = outside ∨
        (actualMajorArcGlobalCanonicalWidestAnchor
          (∏ p ∈ S, p) cutoff fareyCutoff center).1 =
            2 * outside) := by
  let W := ∏ p ∈ S, p
  let canonical := actualMajorArcGlobalCanonicalWidestAnchor
    W cutoff fareyCutoff center
  have hcanonical :=
    (actualMajorArcGlobalCanonicalWidestAnchor_spec
      W cutoff fareyCutoff center).1
  have hbounds := actualShiftedFareyAnchors_denominator_bounds
    W cutoff canonical hcanonical
  obtain hzero | hcoprime :=
    actualConductorDedup_canonical_support_square_or_coprime
      S b n target a d cutoff fareyCutoff τ ell center
      (fun p hp => (hsupport p hp).1) hcenterZero hcenterOne
  · left
    exact hzero.choose_spec.2.2
  · by_cases hfour : 4 ∣ canonical.1
    · left
      exact actualConductorDedup_actual_anchor_smooth_zero_of_four_dvd
        S b n target a d cutoff τ ell canonical
        hsupport hcanonical hfour
    · right
      obtain hodd | heven :=
        actualConductorDedup_odd_or_twice_odd W canonical.1
          hcoprime hfour
      · exact ⟨canonical.1, hbounds.1, hbounds.2,
          hodd.1, hodd.2, Or.inl rfl⟩
      · obtain ⟨outside, hrepresentation, houtsideOdd,
          houtsideCoprime⟩ := heven
        refine ⟨outside, ?_, ?_, houtsideOdd,
          houtsideCoprime, Or.inr hrepresentation⟩
        · omega
        · omega

/-- The genuine finite deduplicated half-open-circle centers whose ACTUAL
canonical widest original denominator is exactly `denominator`. -/
noncomputable def actualConductorDedupCanonicalStratum
    (support cutoff fareyCutoff denominator : ℕ) : Finset ℝ := by
  classical
  exact (shiftedFareyCenterClasses support
    (actualShiftedFareyAnchors support cutoff)).filter fun center =>
      0 ≤ center ∧ center < 1 ∧
        ∃ genuine : ActualMajorArcGlobalCenter support cutoff,
          genuine.val = center ∧
            (actualMajorArcGlobalCanonicalWidestAnchor
              support cutoff fareyCutoff genuine).1 = denominator

/-- At every support-coprime original denominator, the exact finite
normalized real-center stratum is precisely the ACTUAL canonical-widest
denominator stratum.  Support-linear duplicate anchors cannot introduce
either extra centers or a falsely narrower Farey radius. -/
theorem actualConductorDedup_canonical_stratum_eq_actual
    (support cutoff fareyCutoff denominator : ℕ)
    (hsupport : 0 < support)
    (hcoprime : Nat.Coprime denominator support) :
    actualConductorDedupCanonicalStratum
        support cutoff fareyCutoff denominator =
      actualMajorArcCenterReindexActualStratum
        support cutoff denominator := by
  classical
  ext value
  unfold actualConductorDedupCanonicalStratum
    actualMajorArcCenterReindexActualStratum
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hactual, hzero, hone, center, hvalue, hdenominator⟩
    subst value
    let anchor := actualMajorArcGlobalCanonicalWidestAnchor
      support cutoff fareyCutoff center
    obtain ⟨hanchor, hanchorCenter, _⟩ :=
      actualMajorArcGlobalCanonicalWidestAnchor_spec
        support cutoff fareyCutoff center
    exact ⟨hactual, hzero, hone, anchor,
      hanchor, hdenominator, hanchorCenter⟩
  · rintro ⟨hactual, hzero, hone, anchor,
      hanchor, hdenominator, hanchorCenter⟩
    let center : ActualMajorArcGlobalCenter support cutoff :=
      ⟨value, hactual⟩
    have hcoprimeAnchor : Nat.Coprime anchor.1 support := by
      rw [hdenominator]
      exact hcoprime
    have hequal := actualConductorDedup_canonical_denominator_eq_support_free
      support cutoff fareyCutoff center anchor hsupport hanchor
        hanchorCenter hcoprimeAnchor
    exact ⟨hactual, hzero, hone, center, rfl,
      hequal.trans hdenominator⟩

/-- EXACT cardinality of the genuine canonical-widest original denominator
stratum, with all real-center duplicate anchors already removed. -/
theorem actualConductorDedup_canonical_stratum_card
    (support cutoff fareyCutoff denominator : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator support) :
    (actualConductorDedupCanonicalStratum
      support cutoff fareyCutoff denominator).card =
        support * Nat.totient denominator := by
  rw [actualConductorDedup_canonical_stratum_eq_actual
    support cutoff fareyCutoff denominator hsupport hcoprime]
  exact actualMajorArcCenterReindex_actual_stratum_card
    support cutoff denominator hsupport hdenominator hcutoff hcoprime

/-- Exact weighted reindexing of every ACTUAL canonical-widest half-open
real-center stratum by ALL reduced original numerators and ALL support
characters.  This is a finite equality of arbitrary signed complex
weights, not merely a cardinality comparison. -/
theorem actualConductorDedup_canonical_stratum_sum
    (support cutoff fareyCutoff denominator : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator support)
    (weight : ℝ → ℂ) :
    (∑ center ∈ actualConductorDedupCanonicalStratum
        support cutoff fareyCutoff denominator,
      weight center) =
      ∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ character ∈ Finset.range support,
          weight (actualMajorArcCenterReindexNormalizedCenter
            support denominator numerator character) := by
  classical
  rw [actualConductorDedup_canonical_stratum_eq_actual
    support cutoff fareyCutoff denominator hsupport hcoprime,
    ← actualMajorArcCenterReindex_normalized_centers_eq_actual_stratum
      support cutoff denominator hsupport hdenominator hcutoff hcoprime]
  unfold actualMajorArcCenterReindexNormalizedCenters
  rw [Finset.sum_image]
  · unfold actualMajorArcCenterNormalizedCodes
    rw [Finset.sum_image]
    · unfold actualMajorArcCenterNormalizedParameters
      simp [Finset.sum_product,
        actualMajorArcCenterReindexNormalizedCenter]
    · intro left hleft right hright hequal
      obtain ⟨hleftNumerator, hleftCharacter⟩ :=
        Finset.mem_product.mp hleft
      obtain ⟨hrightNumerator, hrightCharacter⟩ :=
        Finset.mem_product.mp hright
      obtain ⟨hfirst, hsecond⟩ :=
        actualMajorArcCenter_normalized_code_injective
          support denominator left.1 right.1 left.2 right.2
          hcoprime
          (Finset.mem_range.mp (Finset.mem_filter.mp hleftNumerator).1)
          (Finset.mem_range.mp (Finset.mem_filter.mp hrightNumerator).1)
          (Finset.mem_range.mp hleftCharacter)
          (Finset.mem_range.mp hrightCharacter)
          hequal
      exact Prod.ext hfirst hsecond
  · intro left _ right _ hequal
    exact actualMajorArcCenterReindex_code_real_injective
      support denominator hsupport hdenominator hequal

/-- Negating an actual support character modulo its positive modulus is
an involution on the complete genuine character range. -/
theorem actualConductorDedup_neg_mod_involutive
    (support character : ℕ)
    (hsupport : 0 < support) (hcharacter : character < support) :
    (support - ((support - character) % support)) % support =
      character := by
  by_cases hzero : character = 0
  · subst character
    simp
  · have hpositive : 0 < character := Nat.pos_of_ne_zero hzero
    have hsubLess : support - character < support :=
      Nat.sub_lt hsupport hpositive
    rw [Nat.mod_eq_of_lt hsubLess,
      Nat.sub_sub_self (Nat.le_of_lt hcharacter),
      Nat.mod_eq_of_lt hcharacter]

/-- Summing over every genuine support character is unchanged by the
signed-character permutation `j ↦ -j mod W`. -/
theorem actualConductorDedup_sum_neg_mod
    (support : ℕ) (hsupport : 0 < support)
    (weight : ℕ → ℂ) :
    (∑ character ∈ Finset.range support,
      weight ((support - character) % support)) =
      ∑ character ∈ Finset.range support, weight character := by
  classical
  apply Finset.sum_bij
    (fun character _ => (support - character) % support)
  · intro character _
    exact Finset.mem_range.mpr
      (Nat.mod_lt (support - character) hsupport)
  · intro left hleft right hright hequal
    have hdouble := congrArg
      (fun character : ℕ => (support - character) % support) hequal
    rwa [actualConductorDedup_neg_mod_involutive
      support left hsupport (Finset.mem_range.mp hleft),
      actualConductorDedup_neg_mod_involutive
        support right hsupport (Finset.mem_range.mp hright)] at hdouble
  · intro character hcharacter
    refine ⟨(support - character) % support,
      Finset.mem_range.mpr
        (Nat.mod_lt (support - character) hsupport), ?_⟩
    exact actualConductorDedup_neg_mod_involutive
      support character hsupport (Finset.mem_range.mp hcharacter)
  · intro character _
    rfl

/-- Exact canonical-center weighted reindexing with the ORIGINAL manuscript
support-character sign.  The half-open normalized center now uses
`-shift mod W`, matching the genuine Farey anchor `h/q - shift/W`. -/
theorem actualConductorDedup_canonical_stratum_sum_neg_character
    (support cutoff fareyCutoff denominator : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff)
    (hcoprime : Nat.Coprime denominator support)
    (weight : ℝ → ℂ) :
    (∑ center ∈ actualConductorDedupCanonicalStratum
        support cutoff fareyCutoff denominator,
      weight center) =
      ∑ numerator ∈ (Finset.range denominator).filter
          (fun numerator => Nat.gcd numerator denominator = 1),
        ∑ shift ∈ Finset.range support,
          weight (actualMajorArcCenterReindexNormalizedCenter
            support denominator numerator
              ((support - shift) % support)) := by
  rw [actualConductorDedup_canonical_stratum_sum
    support cutoff fareyCutoff denominator hsupport
      hdenominator hcutoff hcoprime weight]
  apply Finset.sum_congr rfl
  intro numerator _
  exact (actualConductorDedup_sum_neg_mod support hsupport
    (fun character => weight
      (actualMajorArcCenterReindexNormalizedCenter
        support denominator numerator character))).symm

/-- A genuinely noncoprime support-divisor pair has NO compatible selected
support triple when the original robust label is a support unit.  This
discharges the missing `Coprime a d` branch in the full coefficient sum. -/
theorem actualConductorDedup_support_triples_empty_of_not_coprime
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (_hd : d ∣ ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hcoprime : ¬ Nat.Coprime a d) :
    actualMajorArcSupportCompatibleCellTriples
      S b target a d = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨triple, htriple⟩
  obtain ⟨p, hp, hpa, hpd⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcoprime
  have hpW : p ∣ ∏ q ∈ S, q := dvd_trans hpa ha
  have hpSupport : p ∈ S :=
    prime_mem_of_dvd_support_product hp hsupport hpW
  obtain ⟨hlabelRange, _, _, hlabelTarget, _, _, _, _, _, hcompatible⟩ :=
    (actualMajorArcSupportCompatibleCellTriples_mem_iff
      S b target a d triple).mp htriple
  have hlabel : triple.1 = target := by
    simpa [Nat.mod_eq_of_lt hlabelRange] using hlabelTarget
  have hmod :
      Nat.ModEq p (a * triple.2.1 + triple.1)
        (2 * d * triple.2.2) :=
    (show Nat.ModEq (∏ q ∈ S, q)
      (a * triple.2.1 + triple.1)
        (2 * d * triple.2.2) from hcompatible).of_dvd hpW
  change (a * triple.2.1 + triple.1) % p =
    (2 * d * triple.2.2) % p at hmod
  have htargetMod : target % p = 0 := by
    rw [← hlabel]
    simpa [Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_zero_of_dvd hpa,
      Nat.mod_eq_zero_of_dvd hpd] using hmod
  exact htarget p hpSupport (Nat.dvd_of_mod_eq_zero htargetMod)

/-- Every genuine full-common-modulus compatible triple family also
vanishes at a noncoprime support-divisor pair; projection retains the true
three unit conditions and both switched masks. -/
theorem actualConductorDedup_full_triples_empty_of_not_coprime
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hcoprime : ¬ Nat.Coprime a d) :
    actualMajorArcParityCompatibleFullCellTriples
      S b target a d denominator = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨triple, htriple⟩
  have hsupportTriple :=
    actualMajorArcParity_full_triple_support_reduction_mem
      S b target a d denominator triple hsupport htriple
  rw [actualConductorDedup_support_triples_empty_of_not_coprime
    S b target a d hsupport ha hd htarget hcoprime] at hsupportTriple
  simp at hsupportTriple

/-- The actual manuscript coefficient state and all genuinely compatible
CRT fibers vanish together at every noncoprime support-divisor pair. -/
theorem actualConductorDedup_noncoprime_coefficient_and_fibers_zero
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hcoprime : ¬ Nat.Coprime a d) :
    actualFixedLabelDoubleCoefficientWeight S target b a d = 0 ∧
      actualMajorArcParityCompatibleFullCellTriples
        S b target a d denominator = ∅ := by
  constructor
  · simp [actualFixedLabelDoubleCoefficientWeight, hcoprime]
  · exact actualConductorDedup_full_triples_empty_of_not_coprime
      S b target a d denominator hsupport ha hd htarget hcoprime

/-- The canonical genuine widest original denominator attached to an
actual real center; noncenters receive zero only to totalize the finite
fiber map and never occur in its genuine center domain. -/
noncomputable def actualConductorDedupCanonicalDenominator
    (support cutoff fareyCutoff : ℕ) (value : ℝ) : ℕ :=
  if hcenter : value ∈ shiftedFareyCenterClasses support
      (actualShiftedFareyAnchors support cutoff) then
    (actualMajorArcGlobalCanonicalWidestAnchor
      support cutoff fareyCutoff ⟨value, hcenter⟩).1
  else 0

/-- The previously defined genuine canonical stratum is exactly the
finite fiber of the ACTUAL canonical denominator on the half-open circle. -/
theorem actualConductorDedup_canonical_stratum_eq_denominator_filter
    (support cutoff fareyCutoff denominator : ℕ) :
    actualConductorDedupCanonicalStratum
        support cutoff fareyCutoff denominator =
      (shiftedFareyCenterClasses support
        (actualShiftedFareyAnchors support cutoff)).filter
          (fun value => 0 ≤ value ∧ value < 1 ∧
            actualConductorDedupCanonicalDenominator
              support cutoff fareyCutoff value = denominator) := by
  classical
  ext value
  unfold actualConductorDedupCanonicalStratum
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hactual, hzero, hone, center, hvalue, hdenominator⟩
    subst value
    refine ⟨hactual, hzero, hone, ?_⟩
    simp only [actualConductorDedupCanonicalDenominator,
      center.property, dite_true]
    exact hdenominator
  · rintro ⟨hactual, hzero, hone, hdenominator⟩
    refine ⟨hactual, hzero, hone,
      (⟨value, hactual⟩ : ActualMajorArcGlobalCenter
        support cutoff), rfl, ?_⟩
    simpa only [actualConductorDedupCanonicalDenominator,
      hactual, dite_true] using hdenominator

/-- EXACT global finite partition: the complete ORIGINAL distinct real
centers on the genuine half-open Fourier circle split by their ACTUAL
canonical widest denominators, with arbitrary signed complex weights.
Every denominator is positive and below the original sharp cutoff. -/
theorem actualConductorDedup_half_open_sum_eq_canonical_strata
    (support cutoff fareyCutoff : ℕ)
    (weight : ℝ → ℂ) :
    (∑ center ∈ (shiftedFareyCenterClasses support
        (actualShiftedFareyAnchors support cutoff)).filter
          (fun center => 0 ≤ center ∧ center < 1),
      weight center) =
      ∑ denominator ∈ Finset.Icc 1 cutoff,
        ∑ center ∈ actualConductorDedupCanonicalStratum
            support cutoff fareyCutoff denominator,
          weight center := by
  classical
  let centers := shiftedFareyCenterClasses support
    (actualShiftedFareyAnchors support cutoff)
  let inside := centers.filter
    (fun center : ℝ => 0 ≤ center ∧ center < 1)
  let denominator := actualConductorDedupCanonicalDenominator
    support cutoff fareyCutoff
  have hmaps : ∀ center ∈ inside,
      denominator center ∈ Finset.Icc 1 cutoff := by
    intro center hcenter
    have hactual : center ∈ centers :=
      (Finset.mem_filter.mp hcenter).1
    have hcanonical :=
      (actualMajorArcGlobalCanonicalWidestAnchor_spec
        support cutoff fareyCutoff
          (⟨center, hactual⟩ : ActualMajorArcGlobalCenter
            support cutoff)).1
    have hbounds := actualShiftedFareyAnchors_denominator_bounds
      support cutoff
      (actualMajorArcGlobalCanonicalWidestAnchor
        support cutoff fareyCutoff
          (⟨center, hactual⟩ : ActualMajorArcGlobalCenter
            support cutoff)) hcanonical
    apply Finset.mem_Icc.mpr
    have hden : denominator center =
        (actualMajorArcGlobalCanonicalWidestAnchor
          support cutoff fareyCutoff
            (⟨center, hactual⟩ : ActualMajorArcGlobalCenter
              support cutoff)).1 := by
      dsimp [denominator, actualConductorDedupCanonicalDenominator]
      split <;> rename_i h
      · rfl
      · exact False.elim (h hactual)
    rw [hden]
    exact ⟨hbounds.1, hbounds.2⟩
  calc
    (∑ center ∈ inside, weight center) =
        ∑ q ∈ Finset.Icc 1 cutoff,
          ∑ center ∈ inside.filter
              (fun center => denominator center = q),
            weight center :=
      (Finset.sum_fiberwise_of_maps_to hmaps weight).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      rw [actualConductorDedup_canonical_stratum_eq_denominator_filter]
      ext value
      simp only [inside, centers, denominator,
        Finset.mem_filter, and_assoc]

/-- Adding back the REAL center `1` gives the exact global canonical
center sum whenever all exterior clipped contributions vanish.  The
half-open stratum already contains center `0`, so the principal periodic
boundary pair is counted exactly once each, never twice as full arcs. -/
theorem actualConductorDedup_global_sum_eq_one_add_strata
    (support cutoff fareyCutoff : ℕ)
    (weight : ℝ → ℂ)
    (hsupport : 0 < support)
    (hcutoff : 0 < cutoff)
    (hexterior : ∀ center ∈ shiftedFareyCenterClasses support
        (actualShiftedFareyAnchors support cutoff),
      (center < 0 ∨ 1 < center) → weight center = 0) :
    (∑ center ∈ shiftedFareyCenterClasses support
        (actualShiftedFareyAnchors support cutoff),
      weight center) =
      weight 1 +
        ∑ denominator ∈ Finset.Icc 1 cutoff,
          ∑ center ∈ actualConductorDedupCanonicalStratum
              support cutoff fareyCutoff denominator,
            weight center := by
  classical
  let centers := shiftedFareyCenterClasses support
    (actualShiftedFareyAnchors support cutoff)
  let inside := centers.filter
    (fun center : ℝ => 0 ≤ center ∧ center < 1)
  have hone : (1 : ℝ) ∈ centers :=
    actualMajorArcBoundary_one_center_mem
      support cutoff hsupport hcutoff
  have honeNotInside : (1 : ℝ) ∉ inside := by
    simp [inside]
  have hsubset : insert (1 : ℝ) inside ⊆ centers := by
    intro center hcenter
    rcases Finset.mem_insert.mp hcenter with hcenter | hcenter
    · simpa [hcenter] using hone
    · exact (Finset.mem_filter.mp hcenter).1
  have hsum :
      (∑ center ∈ insert (1 : ℝ) inside, weight center) =
        ∑ center ∈ centers, weight center := by
    apply Finset.sum_subset hsubset
    intro center hcenter hnot
    have hne : center ≠ 1 := by
      intro hequal
      apply hnot
      simp [hequal]
    have hnotInside : center ∉ inside := by
      intro hinside
      exact hnot (Finset.mem_insert_of_mem hinside)
    have hnotBounds : ¬ (0 ≤ center ∧ center < 1) := by
      intro hbounds
      exact hnotInside (Finset.mem_filter.mpr
        ⟨hcenter, hbounds⟩)
    apply hexterior center hcenter
    by_cases hzero : 0 ≤ center
    · right
      have honele : 1 ≤ center := le_of_not_gt
        (fun hless => hnotBounds ⟨hzero, hless⟩)
      exact lt_of_le_of_ne honele (Ne.symm hne)
    · left
      exact lt_of_not_ge hzero
  rw [← hsum, Finset.sum_insert honeNotInside,
    actualConductorDedup_half_open_sum_eq_canonical_strata]


end Erdos689
