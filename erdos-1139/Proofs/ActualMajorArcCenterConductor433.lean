module

public import ActualRightVertexMajorSingularAssembly433
public import ActualMajorArcPositivityFinal433

@[expose] public section


/-!
# Genuine shifted-center conductor classification

Actual translated Farey anchors have signed, possibly already lifted
numerators.  Their squarefree support factors disappear from the widest
original denominator, while repeated support factors remain and their full
genuine smooth cubic vanishes.  This file works with the ORIGINAL finite
anchor family and exact shifted centers, preserving signed numerators,
support characters, full-modulus prime-unit selectors, and widest-anchor
geometry.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- Every ORIGINAL finite shifted Farey anchor, including either integer
periodic lift, has a genuinely reduced SIGNED numerator. -/
theorem actualMajorArcCenter_actual_anchor_numerator_coprime
    (support cutoff : ℕ) (anchor : ShiftedFareyAnchor)
    (hanchor : anchor ∈ actualShiftedFareyAnchors support cutoff) :
    Int.gcd anchor.2.1 anchor.1 = 1 := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hanchor
  obtain ⟨hpair, hlift⟩ := Finset.mem_product.mp hu
  obtain ⟨hfarey, hshift⟩ := Finset.mem_product.mp hpair
  have hreduced := (Finset.mem_filter.mp hfarey).2
  simpa [Int.gcd_add_mul_left_left, mul_comm] using hreduced

/-- Every reduced SIGNED rational numerator has its unique nonnegative
reduced numerator together with the exact integer periodic quotient. -/
theorem actualMajorArcCenter_signed_numerator_eq_nat_plus_lift
    (denominator : ℕ) (numerator : ℤ)
    (hdenominator : 0 < denominator)
    (hnumerator : Int.gcd numerator denominator = 1) :
    ∃ reduced : ℕ, ∃ lift : ℤ,
      reduced < denominator ∧ Nat.Coprime reduced denominator ∧
        numerator = (reduced : ℤ) + lift * (denominator : ℤ) := by
  have hdenInt : (0 : ℤ) < denominator := by exact_mod_cast hdenominator
  have hnonnegative : 0 ≤ numerator % (denominator : ℤ) :=
    Int.emod_nonneg numerator hdenInt.ne'
  have hless : numerator % (denominator : ℤ) < denominator :=
    Int.emod_lt_of_pos numerator hdenInt
  let reduced := (numerator % (denominator : ℤ)).toNat
  have hcast : (reduced : ℤ) = numerator % (denominator : ℤ) := by
    exact Int.toNat_of_nonneg hnonnegative
  have hreduced : reduced < denominator := by
    have hcastLess : (reduced : ℤ) < denominator := by
      rwa [hcast]
    exact_mod_cast hcastLess
  have hcoprime : Nat.Coprime reduced denominator := by
    change Nat.gcd reduced denominator = 1
    have hgcd : Int.gcd (numerator % (denominator : ℤ))
        (denominator : ℤ) = 1 := by
      rw [Int.gcd_emod]
      exact hnumerator
    rw [← hcast, Int.gcd_natCast_natCast] at hgcd
    exact hgcd
  refine ⟨reduced, numerator / (denominator : ℤ),
    hreduced, hcoprime, ?_⟩
  rw [hcast]
  have hdivision := Int.emod_add_mul_ediv numerator (denominator : ℤ)
  calc
    numerator = numerator % (denominator : ℤ) +
        (denominator : ℤ) * (numerator / (denominator : ℤ)) := hdivision.symm
    _ = _ := by ring

/-- A genuine support-prime square occurs in the original denominator IFF
the quotient by its support gcd still shares a support prime.  This is the
exact conductor dichotomy needed for widest-anchor reduction. -/
theorem actualMajorArcCenter_outside_denominator_coprime_iff
    (S : Finset ℕ) (denominator : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    Nat.Coprime
        (denominator / Nat.gcd denominator (∏ p ∈ S, p))
        (∏ p ∈ S, p) ↔
      ∀ p ∈ S, ¬ p ^ 2 ∣ denominator := by
  let W := ∏ p ∈ S, p
  let G := Nat.gcd denominator W
  have hdivide : G ∣ denominator := Nat.gcd_dvd_left denominator W
  have hfactor : G * (denominator / G) = denominator :=
    Nat.mul_div_cancel' hdivide
  have hsquarefree : Squarefree G :=
    Squarefree.squarefree_of_dvd
      (Nat.gcd_dvd_right denominator W)
      (Sieve.prodDistinctPrimes_squarefree S hsupport)
  constructor
  · intro hcoprime p hp hpsquare
    have hprime := hsupport p hp
    have hpW : p ∣ W :=
      Finset.dvd_prod_of_mem (fun s : ℕ => s) hp
    have hquotient : ¬ p ∣ denominator / G := by
      have hsmall := hcoprime.coprime_dvd_right hpW
      exact hprime.coprime_iff_not_dvd.mp hsmall.symm
    have hprimeCoprime : Nat.Coprime p (denominator / G) :=
      hprime.coprime_iff_not_dvd.mpr hquotient
    have hpowerCoprime : Nat.Coprime (p ^ 2) (denominator / G) :=
      hprimeCoprime.pow_left 2
    have hpowerG : p ^ 2 ∣ G := by
      apply hpowerCoprime.dvd_of_dvd_mul_right
      simpa [hfactor] using hpsquare
    apply (Nat.squarefree_iff_prime_squarefree.mp hsquarefree) p hprime
    simpa [pow_two] using hpowerG
  · intro hno
    by_contra hnot
    obtain ⟨p, hp, hpquotient, hpW⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hnot
    change p ∣ denominator / G at hpquotient
    have hpSupport : p ∈ S :=
      prime_mem_of_dvd_support_product hp hsupport hpW
    have hpDenominator : p ∣ denominator :=
      dvd_trans hpquotient (Nat.div_dvd_of_dvd hdivide)
    have hpG : p ∣ G := Nat.dvd_gcd hpDenominator hpW
    apply hno p hpSupport
    have hproduct := mul_dvd_mul hpG hpquotient
    simpa [pow_two, hfactor] using hproduct

/-- Every ACTUAL signed, already-lifted shifted Farey anchor carrying a
square of a support prime has identically zero genuine smooth cubic.  This
bridges the natural-numerator cancellation theorem to the original finite
anchor family used by the deduplicated widest-center integral. -/
theorem actualMajorArcCenter_actual_anchor_smooth_zero_of_support_square
    (S : Finset ℕ) (b : ℕ → ℕ)
    (n target a d cutoff p : ℕ)
    (τ ell α : ℝ) (anchor : ShiftedFareyAnchor)
    (hsupport : ∀ s ∈ S, s.Prime)
    (hanchor : anchor ∈ actualShiftedFareyAnchors
      (∏ s ∈ S, s) cutoff)
    (hpSupport : p ∈ S)
    (hpSquare : p ^ 2 ∣ anchor.1) :
    actualMajorArcIntegratedAnchorSmooth
      S b n target a d τ ell anchor α = 0 := by
  have hdenominator :=
    (actualShiftedFareyAnchors_denominator_bounds
      (∏ s ∈ S, s) cutoff anchor hanchor).1
  have hcoprime := actualMajorArcCenter_actual_anchor_numerator_coprime
    (∏ s ∈ S, s) cutoff anchor hanchor
  obtain ⟨reduced, lift, hless, hreduced, hrepresentation⟩ :=
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
  exact actualMajorArcSingular_admissible_smooth_zero_of_support_square
    S b n anchor.1 p reduced target a d anchor.2.2 lift
      τ ell
      (α - shiftedFareyAnchorCenter (∏ s ∈ S, s)
        anchor.1 anchor.2.1 anchor.2.2)
      hsupport hdenominator hpSupport hpSquare hreduced

/-- The complete natural support-character / reduced-numerator parameter
set at a candidate support-free original denominator. -/
noncomputable def actualMajorArcCenterNormalizedParameters
    (support denominator : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range denominator).filter
    (fun numerator => Nat.gcd numerator denominator = 1)).product
      (Finset.range support)

/-- Exact common-denominator circle code of a reduced outside numerator
and one complete support-character coordinate. -/
def actualMajorArcCenterNormalizedCode
    (support denominator numerator character : ℕ) : ℕ :=
  (numerator * support + character * denominator) %
    (denominator * support)

/-- Distinct reduced support-free numerator/character pairs produce
distinct genuine rational circle centers; no support shift is duplicated. -/
theorem actualMajorArcCenter_normalized_code_injective
    (support denominator numerator numerator' character character' : ℕ)
    (hcoprime : Nat.Coprime denominator support)
    (hnumerator : numerator < denominator)
    (hnumerator' : numerator' < denominator)
    (hcharacter : character < support)
    (hcharacter' : character' < support)
    (hequal :
      actualMajorArcCenterNormalizedCode
          support denominator numerator character =
        actualMajorArcCenterNormalizedCode
          support denominator numerator' character') :
    numerator = numerator' ∧ character = character' := by
  have hdenominatorDivide : denominator ∣ denominator * support :=
    dvd_mul_right denominator support
  have hsupportDivide : support ∣ denominator * support := by
    exact dvd_mul_left support denominator
  have hnumeratorMod :
      (numerator * support) % denominator =
        (numerator' * support) % denominator := by
    have h := congrArg (fun k : ℕ => k % denominator) hequal
    simpa [actualMajorArcCenterNormalizedCode,
      Nat.mod_mod_of_dvd _ hdenominatorDivide,
      Nat.add_mod, Nat.mul_mod] using h
  have hcharacterMod :
      (character * denominator) % support =
        (character' * denominator) % support := by
    have h := congrArg (fun k : ℕ => k % support) hequal
    simpa [actualMajorArcCenterNormalizedCode,
      Nat.mod_mod_of_dvd _ hsupportDivide,
      Nat.add_mod, Nat.mul_mod] using h
  have hnumeratorEq : numerator = numerator' := by
    have hmodeq : numerator * support ≡
        numerator' * support [MOD denominator] := hnumeratorMod
    exact (Nat.ModEq.cancel_right_of_coprime
      hcoprime.gcd_eq_one hmodeq).eq_of_lt_of_lt
        hnumerator hnumerator'
  have hcharacterEq : character = character' := by
    have hmodeq : character * denominator ≡
        character' * denominator [MOD support] := hcharacterMod
    exact (Nat.ModEq.cancel_right_of_coprime
      hcoprime.symm.gcd_eq_one hmodeq).eq_of_lt_of_lt
        hcharacter hcharacter'
  exact ⟨hnumeratorEq, hcharacterEq⟩

/-- The genuine distinct support-free rational circle-center codes. -/
noncomputable def actualMajorArcCenterNormalizedCodes
    (support denominator : ℕ) : Finset ℕ := by
  classical
  exact (actualMajorArcCenterNormalizedParameters support denominator).image
    fun parameter => actualMajorArcCenterNormalizedCode
      support denominator parameter.1 parameter.2

/-- At EVERY support-coprime denominator the complete actual support
character / reduced Farey numerator family has exactly `W*phi(r)` distinct
rational circle centers.  No parity or support multiplicity is omitted. -/
theorem actualMajorArcCenter_normalized_codes_card
    (support denominator : ℕ)
    (hcoprime : Nat.Coprime denominator support) :
    (actualMajorArcCenterNormalizedCodes support denominator).card =
      support * Nat.totient denominator := by
  classical
  let parameters := actualMajorArcCenterNormalizedParameters
    support denominator
  have hinjective :
      Set.InjOn
        (fun parameter : ℕ × ℕ =>
          actualMajorArcCenterNormalizedCode
            support denominator parameter.1 parameter.2)
        (↑parameters : Set (ℕ × ℕ)) := by
    intro left hleft right hright hequal
    have hleft' := Finset.mem_product.mp (Finset.mem_coe.mp hleft)
    have hright' := Finset.mem_product.mp (Finset.mem_coe.mp hright)
    obtain ⟨hfirst, hsecond⟩ :=
      actualMajorArcCenter_normalized_code_injective
        support denominator left.1 right.1 left.2 right.2
        hcoprime
        (Finset.mem_range.mp (Finset.mem_filter.mp hleft'.1).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hright'.1).1)
        (Finset.mem_range.mp hleft'.2)
        (Finset.mem_range.mp hright'.2)
        hequal
    exact Prod.ext hfirst hsecond
  change (parameters.image _).card = support * Nat.totient denominator
  rw [Finset.card_image_iff.mpr hinjective]
  simp [parameters, actualMajorArcCenterNormalizedParameters,
    actualMajorArcComposite_unit_numerators_card, Nat.mul_comm]

/-- Every original denominator having no repeated support prime can be
reanchored at its support-free quotient without changing the EXACT REAL
shifted center.  The new numerator remains genuinely reduced.  Both
numerators and support characters are signed, so this applies directly to
the finite periodic anchor family rather than only to circle codes. -/
theorem actualMajorArcCenter_support_linear_reanchor
    (support denominator : ℕ) (numerator character : ℤ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hnumerator : Int.gcd numerator denominator = 1)
    (hcoprime : Nat.Coprime
      (denominator / Nat.gcd denominator support) support) :
    ∃ reducedNumerator reducedCharacter : ℤ,
      Int.gcd reducedNumerator
          (denominator / Nat.gcd denominator support) = 1 ∧
        shiftedFareyAnchorCenter support denominator numerator character =
          shiftedFareyAnchorCenter support
            (denominator / Nat.gcd denominator support)
            reducedNumerator reducedCharacter := by
  let G := Nat.gcd denominator support
  let r := denominator / G
  let s := support / G
  have hGpositive : 0 < G := Nat.gcd_pos_of_pos_left support hdenominator
  have hrpositive : 0 < r :=
    Nat.div_pos (Nat.le_of_dvd hdenominator
      (Nat.gcd_dvd_left denominator support)) hGpositive
  have hspositive : 0 < s :=
    Nat.div_pos (Nat.le_of_dvd hsupport
      (Nat.gcd_dvd_right denominator support)) hGpositive
  have hdenFactor : G * r = denominator :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left denominator support)
  have hsupportFactor : G * s = support :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right denominator support)
  let x := Nat.gcdA r support
  let y := Nat.gcdB r support
  have hbezout : (r : ℤ) * x + (support : ℤ) * y = 1 := by
    have hidentity := Nat.gcd_eq_gcd_ab r support
    rw [hcoprime.gcd_eq_one] at hidentity
    simpa [x, y] using hidentity.symm
  let reducedNumerator : ℤ := numerator * (s : ℤ) * y
  let reducedCharacter : ℤ := character - numerator * (s : ℤ) * x
  have hsupportInt : (support : ℤ) = (G : ℤ) * (s : ℤ) := by
    exact_mod_cast hsupportFactor.symm
  have hlinear : numerator =
      (G : ℤ) * reducedNumerator +
        (r : ℤ) * (numerator * x) := by
    rw [hsupportInt] at hbezout
    calc
      numerator = numerator * 1 := by ring
      _ = numerator *
        ((r : ℤ) * x + (G : ℤ) * (s : ℤ) * y) := by rw [hbezout]
      _ = _ := by dsimp [reducedNumerator]; ring
  have hnumeratorReduced : Int.gcd numerator (r : ℤ) = 1 := by
    have hfull : Int.gcd numerator ((G * r : ℕ) : ℤ) = 1 := by
      rw [hdenFactor]
      exact hnumerator
    exact Int.gcd_eq_one_of_gcd_mul_right_eq_one_right hfull
  have hnewReduced : Int.gcd reducedNumerator (r : ℤ) = 1 := by
    let K := Int.gcd reducedNumerator (r : ℤ)
    have hKfirst : (K : ℤ) ∣ reducedNumerator :=
      Int.gcd_dvd_left reducedNumerator (r : ℤ)
    have hKsecond : (K : ℤ) ∣ (r : ℤ) :=
      Int.gcd_dvd_right reducedNumerator (r : ℤ)
    have hKnumerator : (K : ℤ) ∣ numerator := by
      rw [hlinear]
      exact dvd_add (dvd_mul_of_dvd_right hKfirst (G : ℤ))
        (dvd_mul_of_dvd_left hKsecond (numerator * x))
    have hKone : (K : ℤ) ∣ (1 : ℤ) := by
      simpa [hnumeratorReduced] using
        (Int.dvd_coe_gcd hKnumerator hKsecond)
    have hKoneNat : K ∣ 1 := by
      exact_mod_cast hKone
    exact Nat.dvd_one.mp hKoneNat
  refine ⟨reducedNumerator, reducedCharacter, hnewReduced, ?_⟩
  have hdenReal : (denominator : ℝ) = (G : ℝ) * (r : ℝ) := by
    exact_mod_cast hdenFactor.symm
  have hsupportReal : (support : ℝ) = (G : ℝ) * (s : ℝ) := by
    exact_mod_cast hsupportFactor.symm
  have hbezoutReal :
      (r : ℝ) * (x : ℝ) + (support : ℝ) * (y : ℝ) = 1 := by
    exact_mod_cast hbezout
  rw [hsupportReal] at hbezoutReal
  change shiftedFareyAnchorCenter support denominator numerator character =
    shiftedFareyAnchorCenter support r reducedNumerator reducedCharacter
  unfold shiftedFareyAnchorCenter
  dsimp [reducedNumerator, reducedCharacter]
  push_cast
  rw [hdenReal, hsupportReal]
  field_simp
  linear_combination -(numerator : ℝ) * (s : ℝ) * hbezoutReal

/-- Normalize an arbitrary SIGNED support character into the actual
`range W`, transferring its integer period into the reduced numerator
without changing the exact real shifted center or its reducedness. -/
theorem actualMajorArcCenter_character_normalized_reanchor
    (support denominator : ℕ) (numerator character : ℤ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hnumerator : Int.gcd numerator denominator = 1) :
    ∃ normalizedNumerator : ℤ, ∃ normalizedCharacter : ℕ,
      normalizedCharacter < support ∧
        Int.gcd normalizedNumerator denominator = 1 ∧
        shiftedFareyAnchorCenter support denominator numerator character =
          shiftedFareyAnchorCenter support denominator
            normalizedNumerator (normalizedCharacter : ℤ) := by
  have hsupportInt : (0 : ℤ) < support := by exact_mod_cast hsupport
  let normalizedCharacter := (character % (support : ℤ)).toNat
  let period := character / (support : ℤ)
  have hnonnegative : 0 ≤ character % (support : ℤ) :=
    Int.emod_nonneg character hsupportInt.ne'
  have hcharacterCast : (normalizedCharacter : ℤ) =
      character % (support : ℤ) :=
    Int.toNat_of_nonneg hnonnegative
  have hcharacterBound : normalizedCharacter < support := by
    have hbound : (normalizedCharacter : ℤ) < support := by
      rw [hcharacterCast]
      exact Int.emod_lt_of_pos character hsupportInt
    exact_mod_cast hbound
  have hcharacterRepresentation : character =
      (normalizedCharacter : ℤ) + (support : ℤ) * period := by
    rw [hcharacterCast]
    exact (Int.emod_add_mul_ediv character (support : ℤ)).symm
  let normalizedNumerator := numerator - period * (denominator : ℤ)
  have hnormalizedReduced :
      Int.gcd normalizedNumerator denominator = 1 := by
    change Int.gcd (numerator - period * (denominator : ℤ))
      (denominator : ℤ) = 1
    rw [show numerator - period * (denominator : ℤ) =
      numerator + (denominator : ℤ) * (-period) by ring,
      Int.gcd_add_mul_left_left]
    exact hnumerator
  refine ⟨normalizedNumerator, normalizedCharacter,
    hcharacterBound, hnormalizedReduced, ?_⟩
  have hcharacterReal : (character : ℝ) =
      (normalizedCharacter : ℝ) +
        (support : ℝ) * (period : ℝ) := by
    exact_mod_cast hcharacterRepresentation
  unfold shiftedFareyAnchorCenter
  dsimp [normalizedNumerator]
  push_cast
  rw [hcharacterReal]
  field_simp
  ring

/-- A reduced normalized shifted center in the genuine unit interval
belongs to the ORIGINAL finite Farey-anchor family, provided its original
denominator is within the actual cutoff.  No artificial rational anchors
are added. -/
theorem actualMajorArcCenter_normalized_actual_anchor_mem
    (support cutoff denominator : ℕ)
    (numerator : ℤ) (character : ℕ)
    (hsupport : 0 < support) (hdenominator : 0 < denominator)
    (hcutoff : denominator ≤ cutoff) (hcharacter : character < support)
    (hnumerator : Int.gcd numerator denominator = 1)
    (hcenterZero : 0 ≤ shiftedFareyAnchorCenter
      support denominator numerator (character : ℤ))
    (hcenterOne : shiftedFareyAnchorCenter
      support denominator numerator (character : ℤ) ≤ 1) :
    (denominator, numerator, (character : ℤ)) ∈
      actualShiftedFareyAnchors support cutoff := by
  have hsupportReal : (0 : ℝ) < support := by exact_mod_cast hsupport
  have hdenominatorReal : (0 : ℝ) < denominator := by
    exact_mod_cast hdenominator
  have hcharacterReal : (character : ℝ) < support := by
    exact_mod_cast hcharacter
  have hcharacterNonnegative :
      0 ≤ (character : ℝ) / support :=
    div_nonneg (Nat.cast_nonneg character) hsupportReal.le
  have hcharacterLess : (character : ℝ) / support < 1 :=
    (div_lt_one hsupportReal).mpr hcharacterReal
  change 0 ≤ (numerator : ℝ) / denominator -
    (character : ℝ) / support at hcenterZero
  change (numerator : ℝ) / denominator -
    (character : ℝ) / support ≤ 1 at hcenterOne
  have hnumeratorQuotientNonnegative :
      0 ≤ (numerator : ℝ) / denominator := by linarith
  have hnumeratorQuotientLess :
      (numerator : ℝ) / denominator < 2 := by linarith
  have hclear : ((numerator : ℝ) / denominator) *
      (denominator : ℝ) = numerator :=
    div_mul_cancel₀ (numerator : ℝ) hdenominatorReal.ne'
  have hnumeratorNonnegativeReal : (0 : ℝ) ≤ numerator := by
    nlinarith
  have hnumeratorLessReal :
      (numerator : ℝ) < 2 * (denominator : ℝ) := by
    nlinarith
  have hnumeratorNonnegative : (0 : ℤ) ≤ numerator := by
    exact_mod_cast hnumeratorNonnegativeReal
  have hnumeratorLess : numerator < 2 * (denominator : ℤ) := by
    exact_mod_cast hnumeratorLessReal
  have hfarey : (denominator, numerator) ∈
      GoldbachChain.anchors cutoff := by
    unfold GoldbachChain.anchors
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hnumerator⟩
    · exact Finset.mem_Icc.mpr ⟨hdenominator, hcutoff⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · omega
      · omega
  unfold actualShiftedFareyAnchors
  apply Finset.mem_image.mpr
  refine ⟨(((denominator, numerator), character), (0 : ℤ)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨hfarey, Finset.mem_range.mpr hcharacter⟩, ?_⟩
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · simp

/-- Every genuine finite shifted anchor whose support-free conductor has
no repeated support prime can be replaced by another GENUINE finite
shifted anchor with the SAME EXACT real center and the support-coprime
original denominator `q/gcd(q,W)`.  The center must meet the actual unit
circle, and the replacement respects the original Farey cutoff. -/
theorem actualMajorArcCenter_actual_anchor_support_free_reanchor
    (support cutoff : ℕ) (anchor : ShiftedFareyAnchor)
    (hsupport : 0 < support)
    (hanchor : anchor ∈ actualShiftedFareyAnchors support cutoff)
    (hcoprime : Nat.Coprime
      (anchor.1 / Nat.gcd anchor.1 support) support)
    (hcenterZero : 0 ≤ shiftedFareyAnchorCenter
      support anchor.1 anchor.2.1 anchor.2.2)
    (hcenterOne : shiftedFareyAnchorCenter
      support anchor.1 anchor.2.1 anchor.2.2 ≤ 1) :
    ∃ replacement ∈ actualShiftedFareyAnchors support cutoff,
      replacement.1 = anchor.1 / Nat.gcd anchor.1 support ∧
        Nat.Coprime replacement.1 support ∧
        shiftedFareyAnchorCenter support
            replacement.1 replacement.2.1 replacement.2.2 =
          shiftedFareyAnchorCenter support
            anchor.1 anchor.2.1 anchor.2.2 := by
  obtain ⟨hdenominator, hcutoff⟩ :=
    actualShiftedFareyAnchors_denominator_bounds
      support cutoff anchor hanchor
  have hnumerator := actualMajorArcCenter_actual_anchor_numerator_coprime
    support cutoff anchor hanchor
  let reducedDenominator := anchor.1 / Nat.gcd anchor.1 support
  have hreducedPositive : 0 < reducedDenominator := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hdenominator
        (Nat.gcd_dvd_left anchor.1 support)
    · exact Nat.gcd_pos_of_pos_left support hdenominator
  have hreducedCutoff : reducedDenominator ≤ cutoff :=
    le_trans (Nat.div_le_self anchor.1
      (Nat.gcd anchor.1 support)) hcutoff
  obtain ⟨numerator, character, hnumerator', hcenter'⟩ :=
    actualMajorArcCenter_support_linear_reanchor
      support anchor.1 anchor.2.1 anchor.2.2
      hsupport hdenominator hnumerator hcoprime
  obtain ⟨normalizedNumerator, normalizedCharacter,
      hnormalizedBound, hnormalizedReduced, hnormalizedCenter⟩ :=
    actualMajorArcCenter_character_normalized_reanchor
      support reducedDenominator numerator character
      hsupport hreducedPositive hnumerator'
  have hcenterEqual :
      shiftedFareyAnchorCenter support reducedDenominator
        normalizedNumerator (normalizedCharacter : ℤ) =
        shiftedFareyAnchorCenter support
          anchor.1 anchor.2.1 anchor.2.2 := by
    exact (hcenter'.trans hnormalizedCenter).symm
  refine ⟨(reducedDenominator, normalizedNumerator,
    (normalizedCharacter : ℤ)), ?_, rfl, hcoprime, hcenterEqual⟩
  apply actualMajorArcCenter_normalized_actual_anchor_mem
    support cutoff reducedDenominator normalizedNumerator
    normalizedCharacter hsupport hreducedPositive hreducedCutoff
    hnormalizedBound hnormalizedReduced
  · rw [hcenterEqual]
    exact hcenterZero
  · rw [hcenterEqual]
    exact hcenterOne


end Erdos689
