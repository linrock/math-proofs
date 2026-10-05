module

public import ActualLeftVertexMajorOnlyCovering433
public import ActualMajorArcPositivityComposite433

@[expose] public section


/-!
# Actual switched-support major-arc phases and local singular factors

At a rational denominator dividing the switched support, compatible actual
residue triples have genuinely constructive phase: each three-form phase
product is one, and the complete reduced-numerator sum is exactly Euler's
totient.  The three true coefficient-divisibility branches give precisely
the manuscript's exceptional/generic local factors, including the exact
`1/φ(W)` fixed-residue normalization.  Coupling this proven support factor
with every coefficient-coprime outside rational center gives a rigorous
finite singular-series lower bound of one half the ACTUAL manuscript local
factor.  This does not assert the remaining integrated major-arc asymptotic.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- The manuscript's two natural exceptional congruences are EXACTLY the
positive and negative genuine finite-field exceptional label classes. -/
theorem actualMajorArcSupportExceptionalClass_iff_zmod
    (p z bp : ℕ) :
    ((2 * z) % p = bp % p ∨ (2 * z + bp) % p = 0) ↔
      ((2 : ZMod p) * (z : ZMod p) = (bp : ZMod p) ∨
        (2 : ZMod p) * (-(z : ZMod p)) = (bp : ZMod p)) := by
  have hpositive :
      (2 * z) % p = bp % p ↔
        (2 : ZMod p) * (z : ZMod p) = (bp : ZMod p) := by
    constructor
    · intro hmod
      have hcast :=
        (ZMod.natCast_eq_natCast_iff (2 * z) bp p).mpr hmod
      simpa using hcast
    · intro hcast
      apply (ZMod.natCast_eq_natCast_iff (2 * z) bp p).mp
      simpa using hcast
  have hnegative :
      (2 * z + bp) % p = 0 ↔
        (2 : ZMod p) * (-(z : ZMod p)) = (bp : ZMod p) := by
    constructor
    · intro hmod
      have hzero : ((2 * z + bp : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff (2 * z + bp) p).mpr
          (Nat.dvd_iff_mod_eq_zero.mpr hmod)
      push_cast at hzero
      linear_combination -hzero
    · intro heq
      apply Nat.dvd_iff_mod_eq_zero.mp
      apply (ZMod.natCast_eq_zero_iff (2 * z + bp) p).mp
      push_cast
      linear_combination -heq
  rw [hpositive, hnegative]

/-- Exact Boolean equality between the original robust-residue exceptional
flag and the genuine positive/negative finite-field coefficient branches. -/
theorem actualMajorArcSupportExceptionalClass_bool_eq
    (b : ℕ → ℕ) (z p : ℕ) :
    manuscriptExceptionalLocalClass b z p =
      decide ((2 : ZMod p) * (z : ZMod p) = (b p : ZMod p) ∨
        (2 : ZMod p) * (-(z : ZMod p)) = (b p : ZMod p)) := by
  unfold manuscriptExceptionalLocalClass
  congr 1
  exact propext (actualMajorArcSupportExceptionalClass_iff_zmod p z (b p))

/-- The three ACTUAL switched support-divisor branches sum exactly to the
local factor appearing in the original robust-residue major-arc target. -/
theorem actualMajorArcSupport_three_state_eq_manuscript_factor
    (p z : ℕ) (b : ℕ → ℕ)
    (hp : p.Prime) (hlarge : 3 < p)
    (hz : (z : ZMod p) ≠ 0)
    (hb : (b p : ZMod p) ≠ 0) :
    actualFixedLabelPrincipalFactor p z (b p) +
      actualFixedLabelLeftFactor p z (b p) +
      actualFixedLabelRightFactor p z (b p) =
        normalizedSwitchedFactor p (manuscriptExceptionalLocalClass b z p) := by
  rw [actualMajorArcSupportExceptionalClass_bool_eq]
  exact actualFixedLabel_three_state_sum_eq p z (b p)
    hp hlarge hz hb

/-- Every genuine robust manuscript residue is a support unit at each
individual actual switched prime. -/
theorem actualMajorArcSupport_robust_residue_unit
    (S : Finset ℕ) (b : ℕ → ℕ) (J z p : ℕ)
    (hresidue : z ∈ robustResidues S b J)
    (hp : p ∈ S) (hprime : p.Prime) :
    (z : ZMod p) ≠ 0 := by
  classical
  have hrobust := (Finset.mem_filter.mp hresidue).2
  have hdivisor : p ∣ ∏ s ∈ S, s :=
    Finset.dvd_prod_of_mem (fun s : ℕ => s) hp
  have hcoprime : Nat.Coprime z p :=
    hrobust.1.coprime_dvd_right hdivisor
  intro hzero
  have hdivide := (ZMod.natCast_eq_zero_iff z p).mp hzero
  exact (hprime.coprime_iff_not_dvd.mp hcoprime.symm) hdivide

/-- The complete ACTUAL coprime double-divisor coefficient sum, divided
by the TRUE support totient, is exactly the original manuscript's fixed
robust-residue local singular factor. -/
theorem actualMajorArcSupport_double_coefficient_sum_div_totient_eq_local
    (S : Finset ℕ) (b : ℕ → ℕ) (J z : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hresidue : z ∈ robustResidues S b J) :
    (∑ c ∈ ((∏ p ∈ S, p).divisors.product
        (∏ p ∈ S, p).divisors),
      actualFixedLabelDoubleCoefficientWeight S z b c.1 c.2) /
        ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) =
      manuscriptLocalSingularFactor S b z := by
  have hweight := actualFixedLabel_double_divisor_coefficient_sum_eq_product
    S z b hsupport
      (fun p hp => actualMajorArcSupport_robust_residue_unit
        S b J z p hresidue hp (hsupport p hp).1)
      (fun p hp hzero =>
        hb p hp ((ZMod.natCast_eq_zero_iff (b p) p).mp hzero))
  rw [hweight,
    prime_support_totient_real_product S (fun p hp => (hsupport p hp).1)]
  unfold manuscriptLocalSingularFactor
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [actualMajorArcSupportExceptionalClass_bool_eq]

/-- The actual three-coordinate rational-center phase at any fixed residue
triple.  Unlike unrestricted unit sums, this remembers the genuine support
classes of the label, left outside prime, and right outside prime. -/
noncomputable def actualMajorArcSupportResidueCenterPhase
    (modulus labelResidue leftResidue rightResidue a d h : ℕ) : ℂ :=
  GoldbachChain.e
        ((labelResidue : ℝ) * (h : ℝ) / modulus) *
    GoldbachChain.e
        (((a : ℝ) * leftResidue) * (h : ℝ) / modulus) *
    GoldbachChain.e
        ((((-2 * (d : ℤ) : ℤ) : ℝ) * rightResidue) *
          (h : ℝ) / modulus)

/-- At EVERY support-dividing rational denominator, every actual compatible
residue triple has constructive total phase `1`; no nonprincipal support
center is falsely discarded or assigned an uncontrolled sign. -/
theorem actualMajorArcSupportResidueCenterPhase_eq_one
    (modulus labelResidue leftResidue rightResidue a d h : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus) :
    actualMajorArcSupportResidueCenterPhase
      modulus labelResidue leftResidue rightResidue a d h = 1 := by
  simpa [actualMajorArcSupportResidueCenterPhase] using
    ternary_manuscript_major_arc_phase_cancel
      modulus labelResidue leftResidue rightResidue a d
        hmodulus hadmissible (h : ℤ)

/-- The COMPLETE signed numerator sum at a genuine support-dividing
rational denominator is exactly its Euler totient for every compatible
actual residue triple; this includes composite support denominators. -/
theorem actualMajorArcSupportResidueCenterPhase_sum_eq_totient
    (modulus labelResidue leftResidue rightResidue a d : ℕ)
    (hmodulus : 0 < modulus)
    (hadmissible :
      (a * leftResidue + labelResidue) % modulus =
        (2 * d * rightResidue) % modulus) :
    (∑ h ∈ (Finset.range modulus).filter
        (fun h => Nat.gcd h modulus = 1),
      actualMajorArcSupportResidueCenterPhase
        modulus labelResidue leftResidue rightResidue a d h) =
      (Nat.totient modulus : ℂ) := by
  calc
    (∑ h ∈ (Finset.range modulus).filter
        (fun h => Nat.gcd h modulus = 1),
      actualMajorArcSupportResidueCenterPhase
        modulus labelResidue leftResidue rightResidue a d h) =
      ∑ _h ∈ (Finset.range modulus).filter
        (fun h => Nat.gcd h modulus = 1), (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro h hh
        exact actualMajorArcSupportResidueCenterPhase_eq_one
          modulus labelResidue leftResidue rightResidue a d h
            hmodulus hadmissible
    _ = (Nat.totient modulus : ℂ) := by
      simp [actualMajorArcComposite_unit_numerators_card]

/-- Exact finite singular-series lower bound for the TRUE robust manuscript
local factor coupled to all actual signed outside-support rational centers.
The support coefficient sum retains all three divisibility branches and
its indispensable exact `1/φ(W)` residue normalization. -/
theorem actualMajorArcSupport_and_outside_signed_center_sum_ge_local_half
    (S : Finset ℕ) (b : ℕ → ℕ)
    (J z modulus a d : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hresidue : z ∈ robustResidues S b J)
    (hsquarefree : Squarefree modulus)
    (houtside : Nat.Coprime modulus (2 * (∏ p ∈ S, p)))
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p) :
    manuscriptLocalSingularFactor S b z / 2 ≤
      ((∑ c ∈ ((∏ p ∈ S, p).divisors.product
          (∏ p ∈ S, p).divisors),
        actualFixedLabelDoubleCoefficientWeight S z b c.1 c.2) /
          ((((∏ p ∈ S, p).totient : ℕ) : ℝ))) *
        (∑ divisor ∈ modulus.divisors,
          ((∑ h ∈ (Finset.range divisor).filter
              (fun h => Nat.gcd h divisor = 1),
            actualMajorArcGenericPrimeCenterPhase divisor a d h) /
              (Nat.totient divisor : ℂ) ^ 3).re) := by
  let W : ℕ := ∏ p ∈ S, p
  have hWdiv : W ∣ 2 * W := by
    refine ⟨2, ?_⟩
    ring
  have htwo : Nat.Coprime modulus 2 :=
    houtside.coprime_dvd_right (dvd_mul_right 2 W)
  have ha' : Nat.Coprime modulus a :=
    houtside.coprime_dvd_right (dvd_trans ha hWdiv)
  have hd' : Nat.Coprime modulus d :=
    houtside.coprime_dvd_right (dvd_trans hd hWdiv)
  have hcoeff : Nat.Coprime modulus (2 * a * d) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right htwo ha') hd'
  have hodd : ¬ 2 ∣ modulus :=
    Nat.prime_two.coprime_iff_not_dvd.mp htwo.symm
  have hgeneric := actualMajorArcComposite_divisor_signed_phase_sum_ge_half
    modulus a d hsquarefree hodd hcoeff
  have hlocal := manuscriptLocalSingularFactor_pos
    S b z (fun p hp => (hsupport p hp).2)
  rw [actualMajorArcSupport_double_coefficient_sum_div_totient_eq_local
    S b J z hsupport hb hresidue]
  nlinarith [mul_le_mul_of_nonneg_left hgeneric hlocal.le]


end Erdos689
