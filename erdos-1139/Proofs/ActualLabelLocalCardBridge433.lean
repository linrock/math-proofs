module

public import SharpLabelCoefficientAssembly433

@[expose] public section


/-!
# Exact cardinalities of the genuine fixed-label local selectors

The parameter-coordinate selectors in the actual manuscript progression
are related to the already audited three-state local coefficient factors by
genuine finite-field affine permutations.  This module supplies that final
local cardinality identification under the original seed and unit hypotheses.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- A nonconstant genuine affine function on a prime residue field omits zero
at exactly `p-1` parameters. -/
theorem zmod_affine_nonzero_residues_card
    (p u v : ℕ) [Fact p.Prime] (hu : ¬ p ∣ u) :
    (Finset.univ.filter fun k : ZMod p =>
      (u : ZMod p) * k + (v : ZMod p) ≠ 0).card = p - 1 := by
  classical
  have huunit : (u : ZMod p) ≠ 0 := fun h =>
    hu ((ZMod.natCast_eq_zero_iff u p).mp h)
  let e : ZMod p ≃ ZMod p :=
    (Equiv.mulLeft₀ (u : ZMod p) huunit).trans
      (Equiv.addRight (v : ZMod p))
  have hcard :
      (Finset.univ.filter fun k : ZMod p =>
        (u : ZMod p) * k + (v : ZMod p) ≠ 0).card =
          (Finset.univ.erase (0 : ZMod p)).card := by
    apply Finset.card_equiv e
    intro k
    simp [e]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p))] at hcard
  simpa using hcard

/-- On the principal branch the actual progression parameter and the genuine
fixed-label residue differ by an invertible affine finite-field change of
coordinate; therefore their selectors have exactly the same cardinality. -/
theorem actualLabelUnitLocalParameterResidues_card_principal
    (p z b a d q₀ r₀ : ℕ)
    (hp : p.Prime)
    (ha : ¬ p ∣ a)
    (hd : ¬ p ∣ 2 * d)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (actualLabelUnitLocalParameterResidues
      p z b a d q₀ r₀).card =
        (fixedLabelNaturalAdmissibleResidues p z b).card := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have haunit : (a : ZMod p) ≠ 0 := fun h =>
    ha ((ZMod.natCast_eq_zero_iff a p).mp h)
  have hdunit : ((2 * d : ℕ) : ZMod p) ≠ 0 := fun h =>
    hd ((ZMod.natCast_eq_zero_iff (2 * d) p).mp h)
  have hslope :
      (a : ZMod p) * ((2 * d : ℕ) : ZMod p) ≠ 0 :=
    mul_ne_zero haunit hdunit
  let e : ZMod p ≃ ZMod p :=
    (Equiv.mulLeft₀
      ((a : ZMod p) * ((2 * d : ℕ) : ZMod p)) hslope).trans
        (Equiv.addRight ((a * q₀ : ℕ) : ZMod p))
  apply Finset.card_equiv e
  intro k
  rw [← ZMod.natCast_zmod_val k]
  rw [actualLabelUnitLocalParameterResidues_mem_natCast_iff
    p z b a d q₀ r₀ k.val hp]
  rw [labelUnit_principal_local_conditions_iff
    p a d q₀ r₀ z b k.val ha hd hseed]
  unfold fixedLabelNaturalAdmissibleResidues
  simp only [hp, ↓reduceDIte]
  have hmap :
      e (k.val : ZMod p) =
        ((a * ((2 * d) * k.val + q₀) : ℕ) : ZMod p) := by
    dsimp [e]
    rw [show
      (Equiv.mulLeft₀
        ((a : ZMod p) * ((2 * d : ℕ) : ZMod p)) hslope)
          (k.val : ZMod p) =
        ((a : ZMod p) * ((2 * d : ℕ) : ZMod p)) *
          (k.val : ZMod p) from
        congrFun (Equiv.mulLeft₀_apply _ _) _]
    push_cast
    ring
  rw [hmap]

/-- On the left-only coefficient branch the genuine selector is either empty
or the complement of the unique zero of its invertible first affine value. -/
theorem actualLabelUnitLocalParameterResidues_card_left
    (p z b a d q₀ r₀ : ℕ)
    (hp : p.Prime)
    (ha : p ∣ a)
    (hd : ¬ p ∣ 2 * d)
    (hz : ¬ p ∣ z)
    (hb : ¬ p ∣ b)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (actualLabelUnitLocalParameterResidues
      p z b a d q₀ r₀).card =
        if (2 : ZMod p) * (z : ZMod p) = (b : ZMod p)
          then 0 else p - 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  by_cases htarget : (2 : ZMod p) * (z : ZMod p) = (b : ZMod p)
  · simp only [htarget, ↓reduceIte]
    apply Finset.card_eq_zero.mpr
    ext k
    simp
    intro hmember
    have hnatural :
        (k.val : ZMod p) ∈
          actualLabelUnitLocalParameterResidues p z b a d q₀ r₀ := by
      simpa only [ZMod.natCast_zmod_val] using hmember
    have hconditions :=
      (actualLabelUnitLocalParameterResidues_mem_natCast_iff
        p z b a d q₀ r₀ k.val hp).mp hnatural
    have hbranch :=
      (labelUnit_left_local_conditions_iff
        p a d q₀ r₀ z b k.val ha hz hb hseed).mp hconditions
    exact ((zmod_switched_target_ne_iff_not_modEq p b z).mpr
      hbranch.2) htarget
  · simp only [htarget, ↓reduceIte]
    have htargetmod : ¬ b ≡ 2 * z [MOD p] :=
      (zmod_switched_target_ne_iff_not_modEq p b z).mp htarget
    have hset :
        actualLabelUnitLocalParameterResidues p z b a d q₀ r₀ =
          Finset.univ.filter fun k : ZMod p =>
            ((2 * d : ℕ) : ZMod p) * k + (q₀ : ZMod p) ≠ 0 := by
      ext k
      rw [← ZMod.natCast_zmod_val k]
      rw [actualLabelUnitLocalParameterResidues_mem_natCast_iff
        p z b a d q₀ r₀ k.val hp]
      rw [labelUnit_left_local_conditions_iff
        p a d q₀ r₀ z b k.val ha hz hb hseed]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [zmod_affine_ne_zero_iff_not_dvd p (2 * d) q₀ k.val]
      simp [htargetmod]
    rw [hset]
    exact zmod_affine_nonzero_residues_card p (2 * d) q₀ hd

/-- On the right-only coefficient branch the genuine selector is either empty
or the complement of the unique zero of its invertible second affine value. -/
theorem actualLabelUnitLocalParameterResidues_card_right
    (p z b a d q₀ r₀ : ℕ)
    (hp : p.Prime)
    (ha : ¬ p ∣ a)
    (hd : p ∣ d)
    (hz : ¬ p ∣ z)
    (hb : ¬ p ∣ b)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (actualLabelUnitLocalParameterResidues
      p z b a d q₀ r₀).card =
        if (2 : ZMod p) * (-(z : ZMod p)) = (b : ZMod p)
          then 0 else p - 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  by_cases htarget :
      (2 : ZMod p) * (-(z : ZMod p)) = (b : ZMod p)
  · simp only [htarget, ↓reduceIte]
    apply Finset.card_eq_zero.mpr
    ext k
    simp
    intro hmember
    have hnatural :
        (k.val : ZMod p) ∈
          actualLabelUnitLocalParameterResidues p z b a d q₀ r₀ := by
      simpa only [ZMod.natCast_zmod_val] using hmember
    have hconditions :=
      (actualLabelUnitLocalParameterResidues_mem_natCast_iff
        p z b a d q₀ r₀ k.val hp).mp hnatural
    have hbranch :=
      (labelUnit_right_local_conditions_iff
        p a d q₀ r₀ z b k.val hd hz hb hseed).mp hconditions
    exact hbranch.2 htarget
  · simp only [htarget, ↓reduceIte]
    have hset :
        actualLabelUnitLocalParameterResidues p z b a d q₀ r₀ =
          Finset.univ.filter fun k : ZMod p =>
            (a : ZMod p) * k + (r₀ : ZMod p) ≠ 0 := by
      ext k
      rw [← ZMod.natCast_zmod_val k]
      rw [actualLabelUnitLocalParameterResidues_mem_natCast_iff
        p z b a d q₀ r₀ k.val hp]
      rw [labelUnit_right_local_conditions_iff
        p a d q₀ r₀ z b k.val hd hz hb hseed]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [zmod_affine_ne_zero_iff_not_dvd p a r₀ k.val]
      exact and_iff_left htarget
    rw [hset]
    exact zmod_affine_nonzero_residues_card p a r₀ ha

/-- Under the genuine odd-prime, seed, and label/target-unit hypotheses,
the actual local progression selector has exactly its predicted three-state
coefficient cardinality. -/
theorem actualLabelUnitLocalParameterResidues_card_eq_sharp
    (p z b a d q₀ r₀ : ℕ)
    (hp : p.Prime)
    (hodd : p ≠ 2)
    (hz : ¬ p ∣ z)
    (hb : ¬ p ∣ b)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (actualLabelUnitLocalParameterResidues
      p z b a d q₀ r₀).card =
        sharpLabelLocalSelectorCard p z b a d := by
  classical
  by_cases ha : p ∣ a
  · have hd : ¬ p ∣ 2 * d := by
      intro hdiv
      have hsum : p ∣ a * q₀ + z := by
        rw [← hseed]
        exact dvd_mul_of_dvd_left hdiv r₀
      have hleft : p ∣ a * q₀ := dvd_mul_of_dvd_left ha q₀
      exact hz ((Nat.dvd_add_iff_right hleft).mpr hsum)
    simp only [sharpLabelLocalSelectorCard, ha, ↓reduceIte]
    exact actualLabelUnitLocalParameterResidues_card_left
      p z b a d q₀ r₀ hp ha hd hz hb hseed
  · by_cases hd : p ∣ d
    · simp only [sharpLabelLocalSelectorCard, ha, hd, ↓reduceIte]
      exact actualLabelUnitLocalParameterResidues_card_right
        p z b a d q₀ r₀ hp ha hd hz hb hseed
    · have hdoubled : ¬ p ∣ 2 * d := by
        intro hdiv
        rcases (hp.dvd_mul).mp hdiv with htwo | hd'
        · exact hodd
            ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo)
        · exact hd hd'
      simp only [sharpLabelLocalSelectorCard, ha, hd, ↓reduceIte]
      exact actualLabelUnitLocalParameterResidues_card_principal
        p z b a d q₀ r₀ hp ha hdoubled hseed

/-- The actual unit-refined support CRT selector has exactly the product of
the genuine three-state local cardinalities; all conditions are original
prime-support, oddness, label/target-unit, and affine-seed assumptions. -/
theorem actualLabelFiberUnitSelectorResidues_card_eq_sharp_product
    (S : Finset ℕ) (b : ℕ → ℕ)
    (z a d q₀ r₀ : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : ∀ p ∈ S, p ≠ 2)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    (actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀).card =
      ∏ p ∈ S, sharpLabelLocalSelectorCard p z (b p) a d := by
  rw [actualLabelFiberUnitSelectorResidues_card_eq_local_product
    S b z a d q₀ r₀ hsupport]
  apply Finset.prod_congr rfl
  intro p hp
  exact actualLabelUnitLocalParameterResidues_card_eq_sharp
    p z (b p) a d q₀ r₀
    (hsupport p hp) (hodd p hp) (hz p hp) (hb p hp) hseed

/-- Full, unconditional-under-genuine-hypotheses sharp coefficient
normalization for the *actual* fixed-label unit-refined selector.  No
external local-cardinality, independence, or CRT assumption remains. -/
theorem sharpLabel_actual_selector_coefficient_normalization_of_seed
    (S : Finset ℕ) (z a d q₀ r₀ : ℕ) (b : ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (hodd : ∀ p ∈ S, p ≠ 2)
    (ha : a ∣ ∏ p ∈ S, p)
    (hd : d ∣ ∏ p ∈ S, p)
    (hcoprime : Nat.Coprime a d)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : 2 * d * r₀ = a * q₀ + z) :
    actualFixedLabelDoubleCoefficientWeight S z b a d =
      (((actualLabelFiberUnitSelectorResidues
        S b z a d q₀ r₀).card : ℕ) : ℝ) *
        (((∏ p ∈ S, p) : ℕ) : ℝ) /
          ((a : ℝ) * (d : ℝ) *
            ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2) := by
  apply sharpLabel_actual_selector_coefficient_normalization
    S z a d q₀ r₀ b hsupport ha hd hcoprime
  exact actualLabelFiberUnitSelectorResidues_card_eq_sharp_product
    S b z a d q₀ r₀ hsupport hodd hz hb hseed


end Erdos689
