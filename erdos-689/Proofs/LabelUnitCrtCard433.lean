module

public import LabelUnitSelectorBridge433

@[expose] public section


/-!
# Exact local compatibility of actual unit-refined fixed-label selectors

The old graph selector and the coefficient-product selector differ because
the latter removes affine values divisible by support primes.  This file
records that discrepancy as an independently checked concrete example and
develops the genuine local selector conditions used by CRT factorization.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- Vanishing of the actual switched-hit count is exactly avoidance of every
genuine support-prime target, not a formal density hypothesis. -/
theorem switchedHits_zero_iff_forall_not_modEq
    (S : Finset ℕ) (b : ℕ → ℕ) (x : ℕ) :
    switchedHits S b x = 0 ↔
      ∀ p ∈ S, ¬ b p ≡ x [MOD p] := by
  classical
  simp [switchedHits, Finset.card_eq_zero]

/-- The old fixed-label selector genuinely has three classes in the minimal
generic support-prime example, whereas the correctly unit-refined selector
and the genuine three-state local principal selector have only one. -/
theorem labelFiber_unit_selector_card_counterexample :
    (actualLabelFiberSelectorResidues {5} (fun _ => 1) 1 1 1 1).card = 3 ∧
      (actualLabelFiberUnitSelectorResidues
        {5} (fun _ => 1) 1 1 1 1 1).card = 1 ∧
      (fixedLabelNaturalAdmissibleResidues 5 1 1).card = 1 := by
  classical
  constructor
  · norm_num [actualLabelFiberSelectorResidues,
      actualLabelFiberProgressionSelectors, switchedHits]
    decide
  constructor
  · norm_num [actualLabelFiberUnitSelectorResidues,
      actualLabelFiberSelectorResidues,
      actualLabelFiberProgressionSelectors, switchedHits,
      affineSupportUnit]
    decide
  · have h := fixedLabelNaturalAdmissibleResidues_card
      5 1 1 (by norm_num) (by norm_num) (by decide) (by decide)
    norm_num at h ⊢
    exact h

/-- On the genuine principal coefficient branch (`p ∤ a*d`), the actual
unit-refined progression conditions are *exactly* membership in the
finite-field selector used by the three-state coefficient product.  The
seed relation supplies the second affine unit, and neither switched-hit
target is replaced by a formal density assumption. -/
theorem labelUnit_principal_local_conditions_iff
    (p a d q₀ r₀ z b k : ℕ)
    [Fact p.Prime]
    (ha : ¬ p ∣ a)
    (hd : ¬ p ∣ 2 * d)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (¬ p ∣ (2 * d) * k + q₀) ∧
        (¬ p ∣ a * k + r₀) ∧
        (¬ b ≡ 2 * (a * ((2 * d) * k + q₀)) [MOD p]) ∧
        (¬ b ≡ 2 * (a * ((2 * d) * k + q₀) + z) [MOD p]) ↔
      ((a * ((2 * d) * k + q₀) : ℕ) : ZMod p) ∈
        fixedLabelAdmissibleResidues (ZMod p)
          (z : ZMod p) (b : ZMod p) := by
  classical
  let q := (2 * d) * k + q₀
  let r := a * k + r₀
  let x := a * q
  have haZ : (a : ZMod p) ≠ 0 := by
    intro hzero
    exact ha ((ZMod.natCast_eq_zero_iff a p).mp hzero)
  have hdZ : ((2 * d : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hd ((ZMod.natCast_eq_zero_iff (2 * d) p).mp hzero)
  have hvalue : x + z = (2 * d) * r := by
    have h := labelFiber_second_prime_progression_value
      a d z q₀ r₀ k hseed
    simpa [x, q, r, Nat.add_comm] using h
  have hq : (¬ p ∣ q) ↔ (x : ZMod p) ≠ 0 := by
    rw [← ZMod.natCast_eq_zero_iff q p]
    change ((q : ZMod p) ≠ 0) ↔
      (((a * q : ℕ) : ZMod p) ≠ 0)
    push_cast
    simp [haZ]
  have hr : (¬ p ∣ r) ↔
      (x : ZMod p) + (z : ZMod p) ≠ 0 := by
    rw [← ZMod.natCast_eq_zero_iff r p]
    have hcast : (x : ZMod p) + (z : ZMod p) =
        ((2 * d : ℕ) : ZMod p) * (r : ZMod p) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using
        congrArg (fun n : ℕ => (n : ZMod p)) hvalue
    constructor
    · intro hrzero hzero
      rw [hcast] at hzero
      exact hrzero ((mul_eq_zero.mp hzero).resolve_left hdZ)
    · intro hzero hrzero
      apply hzero
      rw [hcast, hrzero, mul_zero]
  have hswitch₁ :
      (¬ b ≡ 2 * x [MOD p]) ↔
        (2 : ZMod p) * (x : ZMod p) ≠ (b : ZMod p) := by
    constructor
    · intro h heq
      apply h
      apply (ZMod.natCast_eq_natCast_iff b (2 * x) p).mp
      push_cast
      exact heq.symm
    · intro h hmod
      apply h
      have heq :=
        (ZMod.natCast_eq_natCast_iff b (2 * x) p).mpr hmod
      push_cast at heq
      exact heq.symm
  have hswitch₂ :
      (¬ b ≡ 2 * (x + z) [MOD p]) ↔
        (2 : ZMod p) * ((x : ZMod p) + (z : ZMod p)) ≠
          (b : ZMod p) := by
    constructor
    · intro h heq
      apply h
      apply (ZMod.natCast_eq_natCast_iff b (2 * (x + z)) p).mp
      push_cast
      exact heq.symm
    · intro h hmod
      apply h
      have heq :=
        (ZMod.natCast_eq_natCast_iff b (2 * (x + z)) p).mpr hmod
      push_cast at heq
      exact heq.symm
  change
    (¬ p ∣ q) ∧ (¬ p ∣ r) ∧
        (¬ b ≡ 2 * x [MOD p]) ∧
        (¬ b ≡ 2 * (x + z) [MOD p]) ↔
      (x : ZMod p) ∈
        fixedLabelAdmissibleResidues (ZMod p)
          (z : ZMod p) (b : ZMod p)
  simp only [fixedLabelAdmissibleResidues, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [hq, hr, hswitch₁, hswitch₂]

/-- On the genuine left-only coefficient branch, the right affine prime is
automatically a support unit and the first switched condition is automatic.
The remaining exact condition is the `2*z ≠ b` indicator used by the
three-state left factor, together with the one surviving prime-unit class. -/
theorem labelUnit_left_local_conditions_iff
    (p a d q₀ r₀ z b k : ℕ)
    (ha : p ∣ a)
    (hz : ¬ p ∣ z)
    (hb : ¬ p ∣ b)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (¬ p ∣ (2 * d) * k + q₀) ∧
        (¬ p ∣ a * k + r₀) ∧
        (¬ b ≡ 2 * (a * ((2 * d) * k + q₀)) [MOD p]) ∧
        (¬ b ≡ 2 * (a * ((2 * d) * k + q₀) + z) [MOD p]) ↔
      (¬ p ∣ (2 * d) * k + q₀) ∧ (¬ b ≡ 2 * z [MOD p]) := by
  let q := (2 * d) * k + q₀
  let r := a * k + r₀
  let x := a * q
  have hvalue : x + z = (2 * d) * r := by
    have h := labelFiber_second_prime_progression_value
      a d z q₀ r₀ k hseed
    simpa [x, q, r, Nat.add_comm] using h
  have hx : p ∣ x := dvd_mul_of_dvd_left ha q
  have hr : ¬ p ∣ r := by
    intro hrdiv
    have hsum : p ∣ x + z := by
      rw [hvalue]
      exact dvd_mul_of_dvd_right hrdiv (2 * d)
    exact hz ((Nat.dvd_add_iff_right hx).mpr hsum)
  have hfirst : ¬ b ≡ 2 * x [MOD p] := by
    intro hmod
    have htarget : p ∣ 2 * x := dvd_mul_of_dvd_right hx 2
    exact hb (Nat.modEq_zero_iff_dvd.mp
      (hmod.trans (Nat.modEq_zero_iff_dvd.mpr htarget)))
  have hmod : 2 * (x + z) ≡ 2 * z [MOD p] := by
    change (2 * (x + z)) % p = (2 * z) % p
    simp [Nat.add_mod, Nat.mul_mod, Nat.dvd_iff_mod_eq_zero.mp hx]
  have hsecond :
      (¬ b ≡ 2 * (x + z) [MOD p]) ↔
        (¬ b ≡ 2 * z [MOD p]) := by
    constructor
    · intro h hzmod
      exact h (hzmod.trans hmod.symm)
    · intro h hxmod
      exact h (hxmod.trans hmod)
  change
    (¬ p ∣ q) ∧ (¬ p ∣ r) ∧
      (¬ b ≡ 2 * x [MOD p]) ∧
      (¬ b ≡ 2 * (x + z) [MOD p]) ↔
        (¬ p ∣ q) ∧ (¬ b ≡ 2 * z [MOD p])
  rw [hsecond]
  tauto

/-- On the genuine right-only coefficient branch, the left affine prime is
automatically a support unit and the second switched condition is automatic.
The exact remaining switched indicator is `2*(-z) ≠ b`, precisely the
three-state right coefficient factor. -/
theorem labelUnit_right_local_conditions_iff
    (p a d q₀ r₀ z b k : ℕ)
    (hd : p ∣ d)
    (hz : ¬ p ∣ z)
    (hb : ¬ p ∣ b)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (¬ p ∣ (2 * d) * k + q₀) ∧
        (¬ p ∣ a * k + r₀) ∧
        (¬ b ≡ 2 * (a * ((2 * d) * k + q₀)) [MOD p]) ∧
        (¬ b ≡ 2 * (a * ((2 * d) * k + q₀) + z) [MOD p]) ↔
      (¬ p ∣ a * k + r₀) ∧
        (2 : ZMod p) * (-(z : ZMod p)) ≠ (b : ZMod p) := by
  let q := (2 * d) * k + q₀
  let r := a * k + r₀
  let x := a * q
  have hvalue : x + z = (2 * d) * r := by
    have h := labelFiber_second_prime_progression_value
      a d z q₀ r₀ k hseed
    simpa [x, q, r, Nat.add_comm] using h
  have hcoefficient : p ∣ 2 * d := dvd_mul_of_dvd_right hd 2
  have hsum : p ∣ x + z := by
    rw [hvalue]
    exact dvd_mul_of_dvd_left hcoefficient r
  have hq : ¬ p ∣ q := by
    intro hqdiv
    have hx : p ∣ x := dvd_mul_of_dvd_right hqdiv a
    exact hz ((Nat.dvd_add_iff_right hx).mpr hsum)
  have hsecond : ¬ b ≡ 2 * (x + z) [MOD p] := by
    intro hmod
    have htarget : p ∣ 2 * (x + z) :=
      dvd_mul_of_dvd_right hsum 2
    exact hb (Nat.modEq_zero_iff_dvd.mp
      (hmod.trans (Nat.modEq_zero_iff_dvd.mpr htarget)))
  have hxzero : (x : ZMod p) + (z : ZMod p) = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (x + z) p).mpr hsum
    simpa only [Nat.cast_add] using h
  have hxneg : (x : ZMod p) = -(z : ZMod p) :=
    eq_neg_of_add_eq_zero_left hxzero
  have hfirst :
      (¬ b ≡ 2 * x [MOD p]) ↔
        (2 : ZMod p) * (-(z : ZMod p)) ≠ (b : ZMod p) := by
    constructor
    · intro h heq
      apply h
      apply (ZMod.natCast_eq_natCast_iff b (2 * x) p).mp
      push_cast
      rw [hxneg]
      exact heq.symm
    · intro h hmod
      apply h
      have heq :=
        (ZMod.natCast_eq_natCast_iff b (2 * x) p).mpr hmod
      push_cast at heq
      rw [hxneg] at heq
      exact heq.symm
  change
    (¬ p ∣ q) ∧ (¬ p ∣ r) ∧
      (¬ b ≡ 2 * x [MOD p]) ∧
      (¬ b ≡ 2 * (x + z) [MOD p]) ↔
        (¬ p ∣ r) ∧
          (2 : ZMod p) * (-(z : ZMod p)) ≠ (b : ZMod p)
  rw [hfirst]
  tauto

#print axioms Erdos689.switchedHits_zero_iff_forall_not_modEq
#print axioms Erdos689.labelFiber_unit_selector_card_counterexample
#print axioms Erdos689.labelUnit_principal_local_conditions_iff
#print axioms Erdos689.labelUnit_left_local_conditions_iff
#print axioms Erdos689.labelUnit_right_local_conditions_iff

end Erdos689
