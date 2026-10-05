module

public import ActualRightVertexMajorSingularAssembly433
public import ActualLabelCanonicalSeeds433

@[expose] public section


/-!
# Exact support-compatible major-arc selector bridge

The major-arc support-character projection produces compatible triples of
unit residues.  The optimized graph sieve instead counts a single affine
progression parameter.  This module identifies those two actual finite
families, including both switched masks, their canonical affine seed, and
the indispensable coefficient compensation.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The true major-arc support-compatible family is the actual denominator-one
common-modulus switched/unit triple family with its affine congruence. -/
noncomputable def actualMajorArcSupportCompatibleCellTriples
    (S : Finset ℕ) (b : ℕ → ℕ) (target a d : ℕ) :
    Finset (ℕ × ℕ × ℕ) :=
  (actualMajorArcLcmAdmissibleCellTriples S b target a d 1).filter
    fun triple =>
      (a * triple.2.1 + triple.1) % (∏ p ∈ S, p) =
        (2 * d * triple.2.2) % (∏ p ∈ S, p)

/-- The actual affine progression parameter gives the original robust-label,
left-prime, and right-prime support residue triple. -/
def actualMajorArcSupportSelectorTriple
    (S : Finset ℕ) (target a d q₀ r₀ k : ℕ) : ℕ × ℕ × ℕ :=
  (target,
    (((2 * d) * k + q₀) % (∏ p ∈ S, p),
      (a * k + r₀) % (∏ p ∈ S, p)))

/-- Unfolding the genuine denominator-one common-modulus family retains all
three range bounds, three unit conditions, both original switched masks,
and the exact affine support congruence. -/
theorem actualMajorArcSupportCompatibleCellTriples_mem_iff
    (S : Finset ℕ) (b : ℕ → ℕ) (target a d : ℕ)
    (triple : ℕ × ℕ × ℕ) :
    triple ∈ actualMajorArcSupportCompatibleCellTriples S b target a d ↔
      triple.1 < (∏ p ∈ S, p) ∧
        triple.2.1 < (∏ p ∈ S, p) ∧
        triple.2.2 < (∏ p ∈ S, p) ∧
        triple.1 % (∏ p ∈ S, p) = target ∧
        Nat.Coprime triple.1 (∏ p ∈ S, p) ∧
        Nat.Coprime triple.2.1 (∏ p ∈ S, p) ∧
        Nat.Coprime triple.2.2 (∏ p ∈ S, p) ∧
        switchedHits S b (2 * (a * triple.2.1)) = 0 ∧
        switchedHits S b (2 * (2 * d * triple.2.2)) = 0 ∧
        (a * triple.2.1 + triple.1) % (∏ p ∈ S, p) =
          (2 * d * triple.2.2) % (∏ p ∈ S, p) := by
  simp [actualMajorArcSupportCompatibleCellTriples,
    actualMajorArcLcmAdmissibleCellTriples,
    actualMajorArcLcmAllCellTriples,
    actualMajorArcLcmAdmissibleCell,
    actualMajorArcLcmResidueModulus, and_assoc]

/-- Genuine support-unit conditions are precisely coprimality to the full
squarefree support product; no coefficient or affine-seed assumption enters. -/
theorem actualMajorArcSupport_affineSupportUnit_iff_coprime
    (S : Finset ℕ) (u v k : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    affineSupportUnit S u v k ↔
      Nat.Coprime (u * k + v) (∏ p ∈ S, p) := by
  constructor
  · intro hunit
    apply Nat.Coprime.prod_right
    intro p hp
    exact ((hsupport p hp).coprime_iff_not_dvd.mpr
      (hunit p hp)).symm
  · intro hcoprime p hp
    have hpW : p ∣ ∏ q ∈ S, q :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    have hlocal := hcoprime.coprime_dvd_right hpW
    exact (hsupport p hp).coprime_iff_not_dvd.mp hlocal.symm

/-- The doubled support-divisor coefficients have a genuine global Bézout
identity in the entire support residue ring, including nonfield cases. -/
theorem actualMajorArcSupport_bezout_zmod
    (W a d : ℕ) (hcoprime : Nat.Coprime a (2 * d)) :
    (a : ZMod W) * (Nat.gcdA a (2 * d) : ZMod W) +
      ((2 * d : ℕ) : ZMod W) *
        (Nat.gcdB a (2 * d) : ZMod W) = 1 := by
  have hidentity := Nat.gcd_eq_gcd_ab a (2 * d)
  have hcast := congrArg (fun x : ℤ => (x : ZMod W)) hidentity
  simpa [hcoprime] using hcast.symm

/-- Every genuine compatible support-residue pair has a unique affine
progression parameter in `ZMod W`, with BOTH original coefficients. -/
theorem actualMajorArcSupport_affine_parameter_exists_unique
    (W target a d q₀ r₀ : ℕ)
    (hcoprime : Nat.Coprime a (2 * d))
    (hseed : 2 * d * r₀ = a * q₀ + target)
    (left right : ZMod W)
    (hcompatible :
      (a : ZMod W) * left + (target : ZMod W) =
        ((2 * d : ℕ) : ZMod W) * right) :
    ∃! k : ZMod W,
      left = ((2 * d : ℕ) : ZMod W) * k + (q₀ : ZMod W) ∧
        right = (a : ZMod W) * k + (r₀ : ZMod W) := by
  let A : ZMod W := a
  let B : ZMod W := (2 * d : ℕ)
  let U : ZMod W := Nat.gcdA a (2 * d)
  let V : ZMod W := Nat.gcdB a (2 * d)
  have hbezout : A * U + B * V = 1 :=
    actualMajorArcSupport_bezout_zmod W a d hcoprime
  have hseedRing :
      B * (r₀ : ZMod W) = A * (q₀ : ZMod W) + (target : ZMod W) := by
    simpa [A, B] using
      congrArg (fun value : ℕ => (value : ZMod W)) hseed
  have hcross :
      A * (left - (q₀ : ZMod W)) =
        B * (right - (r₀ : ZMod W)) := by
    dsimp [A, B] at hcompatible hseedRing ⊢
    linear_combination hcompatible + hseedRing
  let k : ZMod W :=
    U * (right - (r₀ : ZMod W)) + V * (left - (q₀ : ZMod W))
  have hleft : B * k = left - (q₀ : ZMod W) := by
    dsimp [k]
    calc
      B * (U * (right - (r₀ : ZMod W)) +
          V * (left - (q₀ : ZMod W))) =
        U * (B * (right - (r₀ : ZMod W))) +
          B * V * (left - (q₀ : ZMod W)) := by ring
      _ = U * (A * (left - (q₀ : ZMod W))) +
          B * V * (left - (q₀ : ZMod W)) := by rw [← hcross]
      _ = (A * U + B * V) * (left - (q₀ : ZMod W)) := by ring
      _ = _ := by rw [hbezout, one_mul]
  have hright : A * k = right - (r₀ : ZMod W) := by
    dsimp [k]
    calc
      A * (U * (right - (r₀ : ZMod W)) +
          V * (left - (q₀ : ZMod W))) =
        A * U * (right - (r₀ : ZMod W)) +
          V * (A * (left - (q₀ : ZMod W))) := by ring
      _ = A * U * (right - (r₀ : ZMod W)) +
          V * (B * (right - (r₀ : ZMod W))) := by rw [hcross]
      _ = (A * U + B * V) * (right - (r₀ : ZMod W)) := by ring
      _ = _ := by rw [hbezout, one_mul]
  refine ⟨k, ⟨?_, ?_⟩, ?_⟩
  · change left = B * k + (q₀ : ZMod W)
    calc
      left = (left - (q₀ : ZMod W)) + q₀ := by ring
      _ = B * k + q₀ := by rw [← hleft]
  · change right = A * k + (r₀ : ZMod W)
    calc
      right = (right - (r₀ : ZMod W)) + r₀ := by ring
      _ = A * k + r₀ := by rw [← hright]
  · intro k' hk'
    have hB : B * k' = B * k := by
      calc
        B * k' = left - (q₀ : ZMod W) := by
          change ((2 * d : ℕ) : ZMod W) * k' =
            left - (q₀ : ZMod W)
          rw [hk'.1]
          ring
        _ = B * k := hleft.symm
    have hA : A * k' = A * k := by
      calc
        A * k' = right - (r₀ : ZMod W) := by
          change (a : ZMod W) * k' = right - (r₀ : ZMod W)
          rw [hk'.2]
          ring
        _ = A * k := hright.symm
    calc
      k' = (A * U + B * V) * k' := by rw [hbezout, one_mul]
      _ = U * (A * k') + V * (B * k') := by ring
      _ = U * (A * k) + V * (B * k) := by rw [hA, hB]
      _ = (A * U + B * V) * k := by ring
      _ = k := by rw [hbezout, one_mul]

/-- Membership in the original unit-refined affine parameter selector is
EXACTLY membership of its actual support-compatible switched/unit triple.
The finite parameter range is retained explicitly. -/
theorem actualMajorArcSupportSelectorTriple_mem_iff
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d q₀ r₀ k : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (htargetRange : target < ∏ p ∈ S, p)
    (htargetUnit : Nat.Coprime target (∏ p ∈ S, p))
    (hseed : 2 * d * r₀ = a * q₀ + target) :
    k ∈ actualLabelFiberUnitSelectorResidues
        S b target a d q₀ r₀ ↔
      k < (∏ p ∈ S, p) ∧
        actualMajorArcSupportSelectorTriple
            S target a d q₀ r₀ k ∈
          actualMajorArcSupportCompatibleCellTriples
            S b target a d := by
  classical
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  have hprogression := labelFiber_second_prime_progression_value
    a d target q₀ r₀ k hseed
  have hleftHits :
      switchedHits S b
          (2 * (a * (((2 * d) * k + q₀) % W))) =
        switchedHits S b (2 * a * (q₀ + 2 * d * k)) := by
    apply labelFiber_switchedHits_eq_of_support_mod
    simp [W, Nat.mul_mod, Nat.add_mod, add_comm,
      mul_comm, mul_left_comm, mul_assoc]
  have hrightHits :
      switchedHits S b
          (2 * (2 * d * ((a * k + r₀) % W))) =
        switchedHits S b
          (2 * (a * (q₀ + 2 * d * k) + target)) := by
    apply labelFiber_switchedHits_eq_of_support_mod
    rw [hprogression]
    have hparameter :
        Nat.ModEq W ((a * k + r₀) % W) (r₀ + a * k) := by
      simp [Nat.ModEq, add_comm]
    change Nat.ModEq W
      (2 * (2 * d * ((a * k + r₀) % W)))
      (2 * ((2 * d) * (r₀ + a * k)))
    simpa [mul_assoc] using hparameter.mul_left (2 * (2 * d))
  have hcompatible :
      (a * (((2 * d) * k + q₀) % W) + target) % W =
        (2 * d * ((a * k + r₀) % W)) % W := by
    have hleftParameter :
        Nat.ModEq W (((2 * d) * k + q₀) % W)
          (q₀ + 2 * d * k) := by
      simp [Nat.ModEq, add_comm]
    have hrightParameter :
        Nat.ModEq W ((a * k + r₀) % W) (r₀ + a * k) := by
      simp [Nat.ModEq, add_comm]
    change Nat.ModEq W
      (a * (((2 * d) * k + q₀) % W) + target)
      (2 * d * ((a * k + r₀) % W))
    exact ((hleftParameter.mul_left a).add_right target).trans
      (hprogression ▸ (hrightParameter.mul_left (2 * d)).symm)
  constructor
  · intro hmember
    unfold actualLabelFiberUnitSelectorResidues at hmember
    obtain ⟨hselector, hleftUnit, hrightUnit⟩ :=
      Finset.mem_filter.mp hmember
    unfold actualLabelFiberSelectorResidues at hselector
    obtain ⟨hrange, hselected⟩ := Finset.mem_filter.mp hselector
    have hk : k < W := Finset.mem_range.mp hrange
    refine ⟨hk, ?_⟩
    rw [actualMajorArcSupportCompatibleCellTriples_mem_iff]
    dsimp [actualMajorArcSupportSelectorTriple]
    refine ⟨htargetRange,
      Nat.mod_lt _ hW, Nat.mod_lt _ hW,
      Nat.mod_eq_of_lt htargetRange, htargetUnit, ?_, ?_, ?_, ?_,
      hcompatible⟩
    · apply (ZMod.coprime_mod_iff_coprime _ W).mpr
      exact (actualMajorArcSupport_affineSupportUnit_iff_coprime
        S (2 * d) q₀ k hsupport).mp hleftUnit
    · apply (ZMod.coprime_mod_iff_coprime _ W).mpr
      exact (actualMajorArcSupport_affineSupportUnit_iff_coprime
        S a r₀ k hsupport).mp hrightUnit
    · rw [hleftHits]
      exact hselected.1
    · rw [hrightHits]
      exact hselected.2
  · rintro ⟨hk, htriple⟩
    rw [actualMajorArcSupportCompatibleCellTriples_mem_iff] at htriple
    dsimp [actualMajorArcSupportSelectorTriple] at htriple
    obtain ⟨_, _, _, _, _, hleftUnit, hrightUnit,
      hleftSelected, hrightSelected, _⟩ := htriple
    unfold actualLabelFiberUnitSelectorResidues
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_, ?_⟩
    · unfold actualLabelFiberSelectorResidues
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hk, ?_⟩
      constructor
      · rw [← hleftHits]
        exact hleftSelected
      · rw [← hrightHits]
        exact hrightSelected
    · apply (actualMajorArcSupport_affineSupportUnit_iff_coprime
        S (2 * d) q₀ k hsupport).mpr
      exact (ZMod.coprime_mod_iff_coprime _ W).mp hleftUnit
    · apply (actualMajorArcSupport_affineSupportUnit_iff_coprime
        S a r₀ k hsupport).mpr
      exact (ZMod.coprime_mod_iff_coprime _ W).mp hrightUnit

/-- The COMPLETE actual major-arc support-compatible switched/unit triple
family has exactly the same cardinality as the original optimized-sieve
affine parameter selector.  This is a genuine finite bijection, not a
comparison of separately computed heuristic local densities. -/
theorem actualMajorArcSupportCompatibleCellTriples_card_eq_selector
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d q₀ r₀ : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (htargetRange : target < ∏ p ∈ S, p)
    (htargetUnit : Nat.Coprime target (∏ p ∈ S, p))
    (hcoprime : Nat.Coprime a (2 * d))
    (hseed : 2 * d * r₀ = a * q₀ + target) :
    (actualMajorArcSupportCompatibleCellTriples
      S b target a d).card =
      (actualLabelFiberUnitSelectorResidues
        S b target a d q₀ r₀).card := by
  classical
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).pos
  let _ : NeZero W := ⟨Nat.ne_of_gt hW⟩
  symm
  apply Finset.card_bij
    (fun k _ => actualMajorArcSupportSelectorTriple
      S target a d q₀ r₀ k)
  · intro k hk
    exact (actualMajorArcSupportSelectorTriple_mem_iff
      S b target a d q₀ r₀ k hsupport
        htargetRange htargetUnit hseed).mp hk |>.2
  · intro k hk l hl hequal
    have hkbound := (actualMajorArcSupportSelectorTriple_mem_iff
      S b target a d q₀ r₀ k hsupport
        htargetRange htargetUnit hseed).mp hk |>.1
    have hlbound := (actualMajorArcSupportSelectorTriple_mem_iff
      S b target a d q₀ r₀ l hsupport
        htargetRange htargetUnit hseed).mp hl |>.1
    have hleftNatural := congrArg
      (fun triple : ℕ × ℕ × ℕ => triple.2.1) hequal
    have hrightNatural := congrArg
      (fun triple : ℕ × ℕ × ℕ => triple.2.2) hequal
    change ((2 * d) * k + q₀) % W =
      ((2 * d) * l + q₀) % W at hleftNatural
    change (a * k + r₀) % W =
      (a * l + r₀) % W at hrightNatural
    have hleftCast :
        (((2 * d) * k + q₀ : ℕ) : ZMod W) =
          (((2 * d) * l + q₀ : ℕ) : ZMod W) :=
      (ZMod.natCast_eq_natCast_iff'
        ((2 * d) * k + q₀) ((2 * d) * l + q₀) W).mpr hleftNatural
    have hrightCast :
        ((a * k + r₀ : ℕ) : ZMod W) =
          ((a * l + r₀ : ℕ) : ZMod W) :=
      (ZMod.natCast_eq_natCast_iff'
        (a * k + r₀) (a * l + r₀) W).mpr hrightNatural
    have hB :
        ((2 * d : ℕ) : ZMod W) * (k : ZMod W) =
          ((2 * d : ℕ) : ZMod W) * (l : ZMod W) := by
      have hcancel :
          (((2 * d) * k : ℕ) : ZMod W) =
            (((2 * d) * l : ℕ) : ZMod W) := by
        apply add_right_cancel (b := (q₀ : ZMod W))
        simpa only [Nat.cast_add] using hleftCast
      simpa only [Nat.cast_mul] using hcancel
    have hA :
        (a : ZMod W) * (k : ZMod W) =
          (a : ZMod W) * (l : ZMod W) := by
      have hcancel :
          ((a * k : ℕ) : ZMod W) =
            ((a * l : ℕ) : ZMod W) := by
        apply add_right_cancel (b := (r₀ : ZMod W))
        simpa only [Nat.cast_add] using hrightCast
      simpa only [Nat.cast_mul] using hcancel
    let U : ZMod W := Nat.gcdA a (2 * d)
    let V : ZMod W := Nat.gcdB a (2 * d)
    have hbezout :
        (a : ZMod W) * U + ((2 * d : ℕ) : ZMod W) * V = 1 :=
      actualMajorArcSupport_bezout_zmod W a d hcoprime
    have hparameter : (k : ZMod W) = (l : ZMod W) := by
      calc
        (k : ZMod W) =
          ((a : ZMod W) * U + ((2 * d : ℕ) : ZMod W) * V) *
            (k : ZMod W) := by rw [hbezout, one_mul]
        _ = U * ((a : ZMod W) * (k : ZMod W)) +
          V * (((2 * d : ℕ) : ZMod W) * (k : ZMod W)) := by ring
        _ = U * ((a : ZMod W) * (l : ZMod W)) +
          V * (((2 * d : ℕ) : ZMod W) * (l : ZMod W)) := by
            rw [hA, hB]
        _ = ((a : ZMod W) * U +
          ((2 * d : ℕ) : ZMod W) * V) * (l : ZMod W) := by ring
        _ = (l : ZMod W) := by rw [hbezout, one_mul]
    have hval := congrArg ZMod.val hparameter
    simpa [ZMod.val_natCast_of_lt hkbound,
      ZMod.val_natCast_of_lt hlbound] using hval
  · intro triple htriple
    have hconditions :=
      (actualMajorArcSupportCompatibleCellTriples_mem_iff
        S b target a d triple).mp htriple
    obtain ⟨hlabelRange, hleftRange, hrightRange,
      hlabelTarget, _, _, _, _, _, hcompatible⟩ := hconditions
    have hlabel : triple.1 = target := by
      simpa [Nat.mod_eq_of_lt hlabelRange] using hlabelTarget
    have hcompatibleRing :
        (a : ZMod W) * (triple.2.1 : ZMod W) +
            (target : ZMod W) =
          ((2 * d : ℕ) : ZMod W) * (triple.2.2 : ZMod W) := by
      have hcast :=
        (ZMod.natCast_eq_natCast_iff'
          (a * triple.2.1 + triple.1)
          (2 * d * triple.2.2) W).mpr hcompatible
      simpa [hlabel] using hcast
    obtain ⟨k, hk, _⟩ :=
      actualMajorArcSupport_affine_parameter_exists_unique
        W target a d q₀ r₀ hcoprime hseed
          (triple.2.1 : ZMod W) (triple.2.2 : ZMod W)
            hcompatibleRing
    have hkbound : k.val < W := ZMod.val_lt k
    have hleftCast :
        (triple.2.1 : ZMod W) =
          (((2 * d) * k.val + q₀ : ℕ) : ZMod W) := by
      simpa only [Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_zmod_val] using hk.1
    have hrightCast :
        (triple.2.2 : ZMod W) =
          ((a * k.val + r₀ : ℕ) : ZMod W) := by
      simpa only [Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_zmod_val] using hk.2
    have hleftNatural :=
      (ZMod.natCast_eq_natCast_iff'
        triple.2.1 ((2 * d) * k.val + q₀) W).mp hleftCast
    have hrightNatural :=
      (ZMod.natCast_eq_natCast_iff'
        triple.2.2 (a * k.val + r₀) W).mp hrightCast
    rw [Nat.mod_eq_of_lt hleftRange] at hleftNatural
    rw [Nat.mod_eq_of_lt hrightRange] at hrightNatural
    have hmap :
        actualMajorArcSupportSelectorTriple
          S target a d q₀ r₀ k.val = triple := by
      apply Prod.ext
      · exact hlabel.symm
      · apply Prod.ext
        · exact hleftNatural.symm
        · exact hrightNatural.symm
    have hmapMember :
        actualMajorArcSupportSelectorTriple
          S target a d q₀ r₀ k.val ∈
            actualMajorArcSupportCompatibleCellTriples
              S b target a d := by
      rw [hmap]
      exact htriple
    refine ⟨k.val, ?_, hmap⟩
    exact (actualMajorArcSupportSelectorTriple_mem_iff
      S b target a d q₀ r₀ k.val hsupport
        htargetRange htargetUnit hseed).mpr ⟨hkbound, hmapMember⟩

/-- The actual major-arc support-compatible triple cardinality equals the
genuine CANONICAL affine selector, with no seed-existence hypothesis. -/
theorem actualMajorArcSupportCompatibleCellTriples_card_eq_canonical_selector
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htargetUnit : Nat.Coprime target (∏ p ∈ S, p)) :
    (actualMajorArcSupportCompatibleCellTriples
      S b target a d).card =
      (actualLabelFiberUnitSelectorResidues
        S b target a d
        (actualLabelCanonicalSeedQ target a d)
        (actualLabelCanonicalSeedR target a d)).card := by
  apply actualMajorArcSupportCompatibleCellTriples_card_eq_selector
    S b target a d
    (actualLabelCanonicalSeedQ target a d)
    (actualLabelCanonicalSeedR target a d)
    (fun p hp => (hsupport p hp).1)
    htargetRange htargetUnit
    (coprimeSupportDivisors_coprime_doubled
      S a d hsupport ha hcoprime)
  exact (coprimeSupportDivisors_actualLabelCanonicalSeeds
    S target a d hsupport ha hd hcoprime).2

/-- EXACT genuine support singular density after projection of the actual
major-arc triple cells.  Its cardinality is that of the real switched/unit
compatible triple family, and the indispensible `a*d` compensation is
derived without ANY auxiliary affine-seed assumption. -/
theorem actualMajorArcSupportCompatibleCellTriples_compensated_normalization
    (S : Finset ℕ) (b : ℕ → ℕ)
    (target a d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d)
    (htargetRange : target < ∏ p ∈ S, p)
    (htarget : ∀ p ∈ S, ¬ p ∣ target)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    (((actualMajorArcSupportCompatibleCellTriples
      S b target a d).card : ℕ) : ℝ) *
      (((∏ p ∈ S, p) : ℕ) : ℝ) /
        ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 3 =
      ((a : ℝ) * d *
        actualFixedLabelDoubleCoefficientWeight S target b a d) /
          ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) := by
  have htargetUnit : Nat.Coprime target (∏ p ∈ S, p) := by
    apply Nat.Coprime.prod_right
    intro p hp
    exact ((hsupport p hp).1.coprime_iff_not_dvd.mpr
      (htarget p hp)).symm
  rw [actualMajorArcSupportCompatibleCellTriples_card_eq_canonical_selector
    S b target a d hsupport ha hd hcoprime htargetRange htargetUnit]
  apply actualMajorArcSingular_actual_selector_compensated_normalization
    S b target a d
    (actualLabelCanonicalSeedQ target a d)
    (actualLabelCanonicalSeedR target a d)
    hsupport ha hd hcoprime htarget hb
  exact (coprimeSupportDivisors_actualLabelCanonicalSeeds
    S target a d hsupport ha hd hcoprime).2


end Erdos689
