module

public import LabelUnitCrtCard433

@[expose] public section


/-!
# Genuine CRT assembly for actual support-unit fixed-label selectors

Natural canonical residue classes and their `ZMod` representatives carry
the same exact selector cardinality.  This module develops the explicit
bridges needed to assemble the genuine unit-refined label progression
selector from its independently audited local conditions.
-/

open Finset
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- Any genuine natural selector on canonical residues has exactly the
cardinality of the corresponding finite-ring selector. -/
theorem naturalResidueSelector_card_eq_zmod_filter
    (m : ℕ) [NeZero m]
    (predicate : ZMod m → Prop) [DecidablePred predicate] :
    ((Finset.range m).filter fun r : ℕ => predicate (r : ZMod m)).card =
      (Finset.univ.filter predicate).card := by
  classical
  apply Finset.card_bij
    (s := (Finset.range m).filter fun r : ℕ => predicate (r : ZMod m))
    (t := Finset.univ.filter predicate)
    (fun r _ => (r : ZMod m))
  · intro r hr
    obtain ⟨_, hpredicate⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpredicate⟩
  · intro r hr s hs heq
    have hrlt : r < m := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hslt : s < m := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have hval := congrArg ZMod.val heq
    simpa [ZMod.val_natCast_of_lt hrlt,
      ZMod.val_natCast_of_lt hslt] using hval
  · intro x hx
    have hpredicate := (Finset.mem_filter.mp hx).2
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr x.val_lt,
      by simpa [ZMod.natCast_zmod_val] using hpredicate⟩

/-- Arbitrary genuine prime-by-prime finite-ring selectors have exactly
their product cardinality on canonical *natural* support residues.  This
is the missing natural-coordinate, multi-prime CRT counting interface. -/
theorem naturalPrimeSupportCrtSelector_card
    (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (T : ∀ p : S, Finset (ZMod (p : ℕ))) :
    ((Finset.range (∏ p : S, (p : ℕ))).filter fun r : ℕ =>
      ∀ p : S, (r : ZMod (p : ℕ)) ∈ T p).card =
        ∏ p : S, (T p).card := by
  classical
  let W := ∏ p : S, (p : ℕ)
  have hW : 0 < W := Finset.prod_pos fun p _ =>
    (hprime p p.property).pos
  let _ : NeZero W := ⟨Nat.ne_of_gt hW⟩
  let hcoprime := affineSelector_primeSupport_pairwise_coprime S hprime
  let e := ZMod.prodEquivPi (fun p : S => (p : ℕ)) hcoprime
  have hcoordinate : ∀ (r : ℕ) (p : S),
      e (r : ZMod W) p = (r : ZMod (p : ℕ)) := by
    intro r p
    exact congrFun (map_natCast e r) p
  let predicate : ZMod W → Prop := fun x => ∀ p : S, e x p ∈ T p
  have hnatural := naturalResidueSelector_card_eq_zmod_filter W predicate
  have hleft :
      ((Finset.range W).filter fun r : ℕ => predicate (r : ZMod W)) =
        (Finset.range W).filter fun r : ℕ =>
          ∀ p : S, (r : ZMod (p : ℕ)) ∈ T p := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    unfold predicate
    simp only [hcoordinate]
  have hright :
      (Finset.univ.filter predicate) =
        affineCrtRestrictedResidues
          (fun p : S => (p : ℕ)) hcoprime T := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (affineCrtRestrictedResidues_mem_iff
      (fun p : S => (p : ℕ)) hcoprime T x).symm
  rw [hleft, hright] at hnatural
  rw [affineCrtRestrictedResidues_card] at hnatural
  exact hnatural

/-- Nonvanishing of a genuine affine finite-field value is exactly the
natural support-prime nondivisibility condition. -/
theorem zmod_affine_ne_zero_iff_not_dvd
    (p u v k : ℕ) :
    (u : ZMod p) * (k : ZMod p) + (v : ZMod p) ≠ 0 ↔
      ¬ p ∣ u * k + v := by
  have hcast :
      ((u * k + v : ℕ) : ZMod p) =
        (u : ZMod p) * (k : ZMod p) + (v : ZMod p) := by
    push_cast
    rfl
  rw [← hcast]
  exact not_congr (ZMod.natCast_eq_zero_iff (u * k + v) p)

/-- The genuine switched target condition in the residue field is exactly
the original natural manuscript congruence condition. -/
theorem zmod_switched_target_ne_iff_not_modEq
    (p b x : ℕ) :
    (2 : ZMod p) * (x : ZMod p) ≠ (b : ZMod p) ↔
      ¬ b ≡ 2 * x [MOD p] := by
  constructor
  · intro h hmod
    apply h
    have heq :=
      (ZMod.natCast_eq_natCast_iff b (2 * x) p).mpr hmod
    push_cast at heq
    exact heq.symm
  · intro h heq
    apply h
    apply (ZMod.natCast_eq_natCast_iff b (2 * x) p).mp
    push_cast
    exact heq.symm

/-- The *actual* local progression-parameter selector: both genuine affine
values are units and both original switched targets are avoided. -/
noncomputable def actualLabelUnitLocalParameterResidues
    (p z bp a d q₀ r₀ : ℕ) : Finset (ZMod p) := by
  classical
  exact if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    Finset.univ.filter fun k : ZMod p =>
      (((2 * d : ℕ) : ZMod p) * k + (q₀ : ZMod p)) ≠ 0 ∧
        ((a : ZMod p) * k + (r₀ : ZMod p)) ≠ 0 ∧
        (2 : ZMod p) *
            ((a : ZMod p) *
              (((2 * d : ℕ) : ZMod p) * k + (q₀ : ZMod p))) ≠
          (bp : ZMod p) ∧
        (2 : ZMod p) *
            ((a : ZMod p) *
                (((2 * d : ℕ) : ZMod p) * k + (q₀ : ZMod p)) +
              (z : ZMod p)) ≠
          (bp : ZMod p)
  else ∅

/-- Natural parameters belong to the exact local finite-field selector iff
they satisfy the four genuine support-unit and switched-hit conditions. -/
theorem actualLabelUnitLocalParameterResidues_mem_natCast_iff
    (p z bp a d q₀ r₀ k : ℕ) (hp : p.Prime) :
    (k : ZMod p) ∈ actualLabelUnitLocalParameterResidues
        p z bp a d q₀ r₀ ↔
      (¬ p ∣ (2 * d) * k + q₀) ∧
        (¬ p ∣ a * k + r₀) ∧
        (¬ bp ≡ 2 * (a * ((2 * d) * k + q₀)) [MOD p]) ∧
        (¬ bp ≡ 2 * (a * ((2 * d) * k + q₀) + z) [MOD p]) := by
  classical
  unfold actualLabelUnitLocalParameterResidues
  simp only [hp, ↓reduceDIte, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hq := zmod_affine_ne_zero_iff_not_dvd p (2 * d) q₀ k
  have hr := zmod_affine_ne_zero_iff_not_dvd p a r₀ k
  have hx :
      ((a : ZMod p) *
        (((2 * d : ℕ) : ZMod p) * (k : ZMod p) + (q₀ : ZMod p))) =
          ((a * ((2 * d) * k + q₀) : ℕ) : ZMod p) := by
    push_cast
    rfl
  rw [hq, hr, hx,
    zmod_switched_target_ne_iff_not_modEq]
  have hsum :
      ((a * ((2 * d) * k + q₀) : ℕ) : ZMod p) + (z : ZMod p) =
        ((a * ((2 * d) * k + q₀) + z : ℕ) : ZMod p) := by
    push_cast
    rfl
  rw [hsum, zmod_switched_target_ne_iff_not_modEq]

/-- Membership in the *actual*, unit-refined manuscript selector is exactly
simultaneous membership in its genuine local progression-parameter selectors.
No coprimality, seed, or coefficient-divisor assumptions are needed for this
pure CRT decomposition. -/
theorem actualLabelFiberUnitSelectorResidues_mem_iff_all_local
    (S : Finset ℕ) (b : ℕ → ℕ)
    (z a d q₀ r₀ k : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    k ∈ actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀ ↔
      k < (∏ p ∈ S, p) ∧
        ∀ p : S, (k : ZMod (p : ℕ)) ∈
          actualLabelUnitLocalParameterResidues
            (p : ℕ) z (b p) a d q₀ r₀ := by
  classical
  have hfirst (p : ℕ) :
      2 * a * (q₀ + 2 * d * k) =
        2 * (a * ((2 * d) * k + q₀)) := by ring
  have hsecond (p : ℕ) :
      2 * (a * (q₀ + 2 * d * k) + z) =
        2 * (a * ((2 * d) * k + q₀) + z) := by ring
  constructor
  · intro hmember
    unfold actualLabelFiberUnitSelectorResidues at hmember
    obtain ⟨hold, hqunit, hrunit⟩ := Finset.mem_filter.mp hmember
    unfold actualLabelFiberSelectorResidues at hold
    obtain ⟨hcanonical, hselectors⟩ := Finset.mem_filter.mp hold
    refine ⟨Finset.mem_range.mp hcanonical, ?_⟩
    unfold actualLabelFiberProgressionSelectors at hselectors
    have hfirsthits :=
      (switchedHits_zero_iff_forall_not_modEq S b
        (2 * a * (q₀ + 2 * d * k))).mp hselectors.1
    have hsecondhits :=
      (switchedHits_zero_iff_forall_not_modEq S b
        (2 * (a * (q₀ + 2 * d * k) + z))).mp hselectors.2
    unfold affineSupportUnit at hqunit hrunit
    intro p
    apply (actualLabelUnitLocalParameterResidues_mem_natCast_iff
      (p : ℕ) z (b p) a d q₀ r₀ k (hprime p p.property)).mpr
    refine ⟨hqunit p p.property, hrunit p p.property, ?_, ?_⟩
    · rw [← hfirst p]
      exact hfirsthits p p.property
    · rw [← hsecond p]
      exact hsecondhits p p.property
  · rintro ⟨hcanonical, hlocal⟩
    have hconditions (p : ℕ) (hp : p ∈ S) :=
      (actualLabelUnitLocalParameterResidues_mem_natCast_iff
        p z (b p) a d q₀ r₀ k (hprime p hp)).mp
          (hlocal ⟨p, hp⟩)
    unfold actualLabelFiberUnitSelectorResidues
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_, ?_⟩
    · unfold actualLabelFiberSelectorResidues
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hcanonical, ?_⟩
      unfold actualLabelFiberProgressionSelectors
      constructor
      · apply (switchedHits_zero_iff_forall_not_modEq S b
          (2 * a * (q₀ + 2 * d * k))).mpr
        intro p hp
        rw [hfirst p]
        exact (hconditions p hp).2.2.1
      · apply (switchedHits_zero_iff_forall_not_modEq S b
          (2 * (a * (q₀ + 2 * d * k) + z))).mpr
        intro p hp
        rw [hsecond p]
        exact (hconditions p hp).2.2.2
    · intro p hp
      exact (hconditions p hp).1
    · intro p hp
      exact (hconditions p hp).2.1

/-- Exact global CRT factorization for the *actual* unit-refined fixed-label
selector.  Every local factor counts the real pair of affine support units
and the real two switched-target exclusions; no symbolic stand-in selector
or independence assumption occurs. -/
theorem actualLabelFiberUnitSelectorResidues_card_eq_local_product
    (S : Finset ℕ) (b : ℕ → ℕ)
    (z a d q₀ r₀ : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) :
    (actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀).card =
      ∏ p ∈ S,
        (actualLabelUnitLocalParameterResidues
          p z (b p) a d q₀ r₀).card := by
  classical
  have hset :
      actualLabelFiberUnitSelectorResidues S b z a d q₀ r₀ =
        (Finset.range (∏ p ∈ S, p)).filter fun k : ℕ =>
          ∀ p : S, (k : ZMod (p : ℕ)) ∈
            actualLabelUnitLocalParameterResidues
              (p : ℕ) z (b p) a d q₀ r₀ := by
    ext k
    rw [actualLabelFiberUnitSelectorResidues_mem_iff_all_local
      S b z a d q₀ r₀ k hprime]
    simp only [Finset.mem_filter, Finset.mem_range]
  rw [hset]
  have hcrt := naturalPrimeSupportCrtSelector_card S hprime
    (fun p : S => actualLabelUnitLocalParameterResidues
      (p : ℕ) z (b p) a d q₀ r₀)
  rw [Finset.prod_coe_sort S (fun p : ℕ => p)] at hcrt
  rw [Finset.prod_coe_sort S
    (fun p : ℕ => (actualLabelUnitLocalParameterResidues
      p z (b p) a d q₀ r₀).card)] at hcrt
  exact hcrt

#print axioms Erdos689.naturalResidueSelector_card_eq_zmod_filter
#print axioms Erdos689.naturalPrimeSupportCrtSelector_card
#print axioms Erdos689.zmod_affine_ne_zero_iff_not_dvd
#print axioms Erdos689.zmod_switched_target_ne_iff_not_modEq
#print axioms Erdos689.actualLabelUnitLocalParameterResidues_mem_natCast_iff
#print axioms Erdos689.actualLabelFiberUnitSelectorResidues_mem_iff_all_local
#print axioms Erdos689.actualLabelFiberUnitSelectorResidues_card_eq_local_product

end Erdos689
