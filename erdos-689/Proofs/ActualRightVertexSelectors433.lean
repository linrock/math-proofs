import ActualLabelAllPairTransfer433

/-!
# Actual support-unit selectors for fixed-right manuscript vertices

The previously audited fixed-right selector remembers both switched
conditions but omits the two genuine support-unit conditions on the moving
prime and descending prime label.  Here the selector is built from the real
finite-field conditions.  Its local factors are exactly the already audited
fixed-vertex admissible factors on the principal branch and `p - 1` on the
divisible branch; their simultaneous natural-coordinate cardinality is an
actual Chinese-remainder product.  No graph-degree estimate is assumed.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- The actual fixed-right parameter selector over a genuine prime field:
both moving prime values are support units and both original switched
conditions hold. -/
noncomputable def actualRightVertexLocalResidues
    (p y bp a : ℕ) : Finset (ZMod p) := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    Finset.univ.filter fun q : ZMod p =>
      q ≠ 0 ∧
        (y : ZMod p) - (a : ZMod p) * q ≠ 0 ∧
        (2 : ZMod p) * ((a : ZMod p) * q) ≠ (bp : ZMod p) ∧
        (2 : ZMod p) * (y : ZMod p) ≠ (bp : ZMod p)
  else ∅

/-- Under a nonzero coefficient, multiplication by that coefficient is an
actual finite-field permutation carrying the fixed-right parameter selector
to the previously audited genuine moving-vertex selector. -/
theorem actualRightVertexLocalResidues_card_principal
    (p y bp a : ℕ)
    (hp : p.Prime)
    (ha : ¬ p ∣ a)
    (hfixed : (2 : ZMod p) * (y : ZMod p) ≠ (bp : ZMod p)) :
    (actualRightVertexLocalResidues p y bp a).card =
      (fixedVertexNaturalAdmissibleResidues p y bp).card := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have haunit : (a : ZMod p) ≠ 0 := fun h =>
    ha ((ZMod.natCast_eq_zero_iff a p).mp h)
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (a : ZMod p) haunit
  unfold actualRightVertexLocalResidues fixedVertexNaturalAdmissibleResidues
  simp only [hp, ↓reduceDIte]
  apply Finset.card_equiv e
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    fixedVertexAdmissibleResidues]
  have he : e q = (a : ZMod p) * q :=
    congrFun (Equiv.mulLeft₀_apply _ _) q
  rw [he]
  have hzero : (a : ZMod p) * q ≠ 0 ↔ q ≠ 0 :=
    mul_ne_zero_iff_left haunit
  have hsubtract :
      (y : ZMod p) - (a : ZMod p) * q ≠ 0 ↔
        (a : ZMod p) * q ≠ (y : ZMod p) := by
    rw [sub_ne_zero]
    exact ne_comm
  rw [hzero, hsubtract]
  tauto

/-- If the support prime divides the moving coefficient, a genuine
fixed-right selector is empty when it also divides the fixed vertex;
otherwise exactly `p - 1` parameter classes survive. -/
theorem actualRightVertexLocalResidues_card_divisible
    (p y bp a : ℕ)
    (hp : p.Prime)
    (ha : p ∣ a)
    (hb : ¬ p ∣ bp)
    (hfixed : (2 : ZMod p) * (y : ZMod p) ≠ (bp : ZMod p)) :
    (actualRightVertexLocalResidues p y bp a).card =
      if p ∣ y then 0 else p - 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have hazero : (a : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff a p).mpr ha
  have hbnonzero : (bp : ZMod p) ≠ 0 := fun h =>
    hb ((ZMod.natCast_eq_zero_iff bp p).mp h)
  unfold actualRightVertexLocalResidues
  simp only [hp, ↓reduceDIte, hazero, zero_mul, sub_zero, mul_zero]
  by_cases hy : p ∣ y
  · have hyzero : (y : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff y p).mpr hy
    simp [hy, hyzero]
  · have hynonzero : (y : ZMod p) ≠ 0 := fun h =>
      hy ((ZMod.natCast_eq_zero_iff y p).mp h)
    have hzerob : (0 : ZMod p) ≠ (bp : ZMod p) := Ne.symm hbnonzero
    simp only [hy, ↓reduceIte]
    have hset :
        (Finset.univ.filter fun q : ZMod p =>
          q ≠ 0 ∧ (y : ZMod p) ≠ 0 ∧
            (0 : ZMod p) ≠ (bp : ZMod p) ∧
              (2 : ZMod p) * (y : ZMod p) ≠ (bp : ZMod p)) =
          Finset.univ.erase (0 : ZMod p) := by
      ext q
      simp [hynonzero, hzerob, hfixed]
    rw [hset, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p))]
    simp

/-- The genuine natural-coordinate selector simultaneously imposes every
actual prime-field support-unit and switched-target condition. -/
noncomputable def actualRightVertexUnitSelectorResidues
    (S : Finset ℕ) (b : ℕ → ℕ) (y a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (∏ p ∈ S, p)).filter fun q : ℕ =>
    ∀ p : S, (q : ZMod (p : ℕ)) ∈
      actualRightVertexLocalResidues (p : ℕ) y (b p) a

/-- The complete actual fixed-right support-unit selector has precisely the
product of its genuine prime-by-prime local parameter cardinalities. -/
theorem actualRightVertexUnitSelectorResidues_card_eq_local_product
    (S : Finset ℕ) (b : ℕ → ℕ) (y a : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    (actualRightVertexUnitSelectorResidues S b y a).card =
      ∏ p ∈ S, (actualRightVertexLocalResidues p y (b p) a).card := by
  classical
  unfold actualRightVertexUnitSelectorResidues
  have hcrt := naturalPrimeSupportCrtSelector_card S hprime
    (fun p : S => actualRightVertexLocalResidues (p : ℕ) y (b p) a)
  rw [Finset.prod_coe_sort S (fun p : ℕ => p)] at hcrt
  rw [Finset.prod_coe_sort S
    (fun p : ℕ => (actualRightVertexLocalResidues p y (b p) a).card)]
      at hcrt
  exact hcrt

/-- For support `{5}`, fixed vertex `1`, switched target `1`, and coefficient
`1`, the old selector really has four classes, while the actual support-unit
selector has exactly two.  The omitted support-unit exclusions cannot be
ignored when importing the audited local coefficient cancellation. -/
theorem actualRightVertexUnitSelector_old_selector_counterexample :
    (actualRightFiberSelectorResidues {5} (fun _ => 1) 1 1).card = 4 ∧
      (actualRightVertexUnitSelectorResidues {5} (fun _ => 1) 1 1).card = 2 := by
  constructor
  · decide
  · rw [actualRightVertexUnitSelectorResidues_card_eq_local_product]
    · simp only [Finset.prod_singleton]
      have hfixed : (2 : ZMod 5) * (1 : ZMod 5) ≠ (1 : ZMod 5) := by
        decide
      rw [actualRightVertexLocalResidues_card_principal
        5 1 1 1 (by norm_num) (by norm_num) hfixed]
      rw [fixedVertexNaturalAdmissibleResidues_card
        5 1 1 (by norm_num) (by norm_num) (by decide) hfixed]
      decide
    · intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      norm_num

#print axioms Erdos689.actualRightVertexLocalResidues_card_principal
#print axioms Erdos689.actualRightVertexLocalResidues_card_divisible
#print axioms Erdos689.actualRightVertexUnitSelectorResidues_card_eq_local_product
#print axioms Erdos689.actualRightVertexUnitSelector_old_selector_counterexample

end Erdos689
