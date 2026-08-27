import ActualMajorArcPrimeMinor433

/-!
# Genuine outside-support ternary singular-series local factors

The three original affine prime forms are `q`, `r`, and `2*d*r-a*q`.
At every odd prime not dividing `a*d`, their finite-field nonvanishing
conditions select exactly `(p-1)*(p-2)` pairs.  The resulting normalized
Green--Tao local factor is `1-1/(p-1)^2`; arbitrary finite products of
these *actual* factors have the uniform positive lower bound `1/2`.

This file does not identify the full shifted rational-center integral with
its Euler product.  That analytic singular-series coupling remains open.
-/

open Finset
open scoped BigOperators

namespace Erdos689

/-- The actual finite-field right-coordinate fiber of the original three
affine prime forms at a fixed nonzero left coordinate. -/
noncomputable def actualMajorArcGenericLocalRightResidues
    (K : Type*) [Field K] [Fintype K]
    (A C x : K) : Finset K := by
  classical
  exact Finset.univ.filter fun y => y ≠ 0 ∧ C * y - A * x ≠ 0

/-- The actual pair of independent finite-field coordinates on which all
three original affine forms are simultaneously nonzero. -/
noncomputable def actualMajorArcGenericLocalPrimePairs
    (K : Type*) [Field K] [Fintype K]
    (A C : K) : Finset (K × K) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun v =>
    v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ C * v.2 - A * v.1 ≠ 0

/-- For nonzero second coefficient, the two genuinely forbidden right
residues are zero and the actual affine root `A*x/C`. -/
theorem actualMajorArcGenericLocalRightResidues_eq_erase
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (A C x : K) (hC : C ≠ 0) :
    actualMajorArcGenericLocalRightResidues K A C x =
      (Finset.univ.erase 0).erase (A * x / C) := by
  classical
  ext y
  simp only [actualMajorArcGenericLocalRightResidues,
    Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase]
  have hroot : C * y - A * x ≠ 0 ↔ y ≠ A * x / C := by
    constructor
    · intro h heq
      apply h
      apply sub_eq_zero.mpr
      have hmul := (eq_div_iff hC).mp heq
      simpa [mul_comm] using hmul
    · intro h heq
      apply h
      apply (eq_div_iff hC).mpr
      have hmul := sub_eq_zero.mp heq
      simpa [mul_comm] using hmul
  rw [hroot]
  tauto

/-- If both affine coefficients and the left residue are nonzero, its
genuine right-coordinate fiber has exactly `#K-2` elements. -/
theorem actualMajorArcGenericLocalRightResidues_card
    {K : Type*} [Field K] [Fintype K]
    (A C x : K) (hA : A ≠ 0) (hC : C ≠ 0) (hx : x ≠ 0) :
    (actualMajorArcGenericLocalRightResidues K A C x).card =
      Fintype.card K - 2 := by
  classical
  have hroot : A * x / C ≠ 0 :=
    div_ne_zero (mul_ne_zero hA hx) hC
  rw [actualMajorArcGenericLocalRightResidues_eq_erase A C x hC]
  have hmember : A * x / C ∈ (Finset.univ.erase 0 : Finset K) := by
    simp [hroot]
  rw [Finset.card_erase_of_mem hmember,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : K)),
    Finset.card_univ]
  omega

/-- The exact first-coordinate fiber of the genuine two-variable prime-form
selector is in bijection with the actual one-variable right residue set. -/
theorem actualMajorArcGenericLocalPrimePairs_fiber_card
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (A C x : K) (hx : x ≠ 0) :
    ((actualMajorArcGenericLocalPrimePairs K A C).filter
      fun v : K × K => v.1 = x).card =
        (actualMajorArcGenericLocalRightResidues K A C x).card := by
  classical
  apply Finset.card_bij (fun v _ => v.2)
  · intro v hv
    obtain ⟨hpair, hfirst⟩ := Finset.mem_filter.mp hv
    have hconditions :
        v.1 ≠ 0 ∧ v.2 ≠ 0 ∧ C * v.2 - A * v.1 ≠ 0 := by
      simpa [actualMajorArcGenericLocalPrimePairs] using hpair
    obtain ⟨_, hsecond, hthird⟩ := hconditions
    rw [hfirst] at hthird
    simpa [actualMajorArcGenericLocalRightResidues] using
      (show v.2 ≠ 0 ∧ C * v.2 - A * x ≠ 0 from
        ⟨hsecond, hthird⟩)
  · intro v hv w hw hsecond
    have hvfirst := (Finset.mem_filter.mp hv).2
    have hwfirst := (Finset.mem_filter.mp hw).2
    exact Prod.ext (hvfirst.trans hwfirst.symm) hsecond
  · intro y hy
    have hconditions : y ≠ 0 ∧ C * y - A * x ≠ 0 := by
      simpa [actualMajorArcGenericLocalRightResidues] using hy
    obtain ⟨hyzero, hroot⟩ := hconditions
    refine ⟨(x, y), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl⟩
    simpa [actualMajorArcGenericLocalPrimePairs] using
      (show x ≠ 0 ∧ y ≠ 0 ∧ C * y - A * x ≠ 0 from
        ⟨hx, hyzero, hroot⟩)

/-- The complete actual finite-field local count for the original three
affine forms, not a symbolic Euler-product assumption. -/
theorem actualMajorArcGenericLocalPrimePairs_card
    {K : Type*} [Field K] [Fintype K]
    (A C : K) (hA : A ≠ 0) (hC : C ≠ 0) :
    (actualMajorArcGenericLocalPrimePairs K A C).card =
      (Fintype.card K - 1) * (Fintype.card K - 2) := by
  classical
  let pairs := actualMajorArcGenericLocalPrimePairs K A C
  let units : Finset K := Finset.univ.erase 0
  have hfilter : pairs.filter (fun v => v.1 ∈ units) = pairs := by
    apply Finset.filter_true_of_mem
    intro v hv
    have hfirst := (Finset.mem_filter.mp hv).2.1
    exact Finset.mem_erase.mpr ⟨hfirst, Finset.mem_univ _⟩
  have hfibers := Finset.sum_card_fiberwise_eq_card_filter
    pairs units (fun v : K × K => v.1)
  rw [hfilter] at hfibers
  calc
    pairs.card =
        ∑ x ∈ units, (pairs.filter fun v => v.1 = x).card :=
      hfibers.symm
    _ = ∑ _x ∈ units, (Fintype.card K - 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxzero : x ≠ 0 := (Finset.mem_erase.mp hx).1
      rw [actualMajorArcGenericLocalPrimePairs_fiber_card A C x hxzero,
        actualMajorArcGenericLocalRightResidues_card A C x hA hC hxzero]
    _ = (Fintype.card K - 1) * (Fintype.card K - 2) := by
      simp [units]

/-- At every genuine odd prime avoiding both original support-divisor
coefficients, the exact local triple-prime solution count is
`(p-1)*(p-2)`.  The third form is precisely `2*d*r-a*q`. -/
theorem actualMajorArcGenericLocalPrimePairs_card_zmod
    (p a d : ℕ) [Fact p.Prime]
    (hp : p.Prime) (hpodd : p ≠ 2)
    (ha : ¬ p ∣ a) (hd : ¬ p ∣ d) :
    (actualMajorArcGenericLocalPrimePairs (ZMod p)
      (a : ZMod p) ((2 : ZMod p) * (d : ZMod p))).card =
        (p - 1) * (p - 2) := by
  have hA : (a : ZMod p) ≠ 0 := by
    intro h
    exact ha ((ZMod.natCast_eq_zero_iff a p).mp h)
  have hD : (d : ZMod p) ≠ 0 := by
    intro h
    exact hd ((ZMod.natCast_eq_zero_iff d p).mp h)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)
  simpa using actualMajorArcGenericLocalPrimePairs_card
    (a : ZMod p) ((2 : ZMod p) * (d : ZMod p)) hA
      (mul_ne_zero htwo hD)

/-- The positive outside-support local singular factor written with its
actual finite-field count already simplified. -/
noncomputable def actualMajorArcGenericLocalFactor (p : ℕ) : ℝ :=
  (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2

/-- Exact scalar identity for the generic three-form singular factor. -/
theorem actualMajorArcGenericLocalFactor_eq_one_sub_inverse_square
    (p : ℕ) (hp : 1 < p) :
    actualMajorArcGenericLocalFactor p =
      1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hreal : (1 : ℝ) < p := by exact_mod_cast hp
  have hdenominator : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold actualMajorArcGenericLocalFactor
  field_simp
  ring

/-- The scalar factor is exactly the REAL normalized density of the genuine
two-coordinate finite-field selector: `(#solutions/p²)*(p/(p-1))³`.
No local factor is asserted without its underlying actual cardinality. -/
theorem actualMajorArcGenericLocalPrimePairs_normalized_factor
    (p a d : ℕ) [Fact p.Prime]
    (hp : p.Prime) (hpodd : p ≠ 2)
    (ha : ¬ p ∣ a) (hd : ¬ p ∣ d) :
    (((actualMajorArcGenericLocalPrimePairs (ZMod p)
        (a : ZMod p) ((2 : ZMod p) * (d : ZMod p))).card : ℝ) /
          (p : ℝ) ^ 2) *
        ((p : ℝ) / ((p : ℝ) - 1)) ^ 3 =
      actualMajorArcGenericLocalFactor p := by
  rw [actualMajorArcGenericLocalPrimePairs_card_zmod
    p a d hp hpodd ha hd]
  have hpzero : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpone : (p : ℝ) - 1 ≠ 0 := by
    have hreal : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hptwo : 2 ≤ p := hp.two_le
  push_cast [Nat.cast_sub hp.one_le, Nat.cast_sub hptwo]
  unfold actualMajorArcGenericLocalFactor
  field_simp

/-- Every actual generic odd-prime three-form singular factor is strictly
positive; coefficient or support size does not enter the lower sign. -/
theorem actualMajorArcGenericLocalFactor_pos
    (p : ℕ) (hp : 2 < p) :
    0 < actualMajorArcGenericLocalFactor p := by
  unfold actualMajorArcGenericLocalFactor
  have hreal : (2 : ℝ) < p := by exact_mod_cast hp
  exact div_pos (mul_pos (by linarith) (by linarith))
    (sq_pos_of_ne_zero (by linarith))

/-- Every actual generic odd-prime three-form singular factor is at most one. -/
theorem actualMajorArcGenericLocalFactor_le_one
    (p : ℕ) (hp : 1 < p) :
    actualMajorArcGenericLocalFactor p ≤ 1 := by
  rw [actualMajorArcGenericLocalFactor_eq_one_sub_inverse_square p hp]
  exact sub_le_self _ (by positivity)

/-- The complete product of the exact genuine generic local factors at ANY
finite set of odd primes retains the absolute support-independent bound
`1/2`.  The factors are the actual finite-field densities proved above. -/
theorem actualMajorArcGenericLocalFactor_product_ge_half
    (T : Finset ℕ) (hlarge : ∀ p ∈ T, 2 < p) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ T, actualMajorArcGenericLocalFactor p := by
  classical
  let shifted := T.image fun p => p - 1
  have hshifted : ∀ j ∈ shifted, 2 ≤ j := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    have h := hlarge p hp
    omega
  have hcomparison := finite_inverse_square_product_lower shifted hshifted
  have hinjective :
      Set.InjOn (fun p : ℕ => p - 1) (↑T : Set ℕ) := by
    intro p hp q hq heq
    change p - 1 = q - 1 at heq
    have hp' := hlarge p (Finset.mem_coe.mp hp)
    have hq' := hlarge q (Finset.mem_coe.mp hq)
    omega
  have hproduct :
      (∏ j ∈ shifted, (1 - 1 / (j : ℝ) ^ 2)) =
        ∏ p ∈ T, actualMajorArcGenericLocalFactor p := by
    dsimp [shifted]
    rw [Finset.prod_image hinjective]
    apply Finset.prod_congr rfl
    intro p hp
    rw [actualMajorArcGenericLocalFactor_eq_one_sub_inverse_square
      p (by have := hlarge p hp; omega)]
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := hlarge p hp; omega)]
      norm_num
    rw [hcast]
  exact hproduct ▸ hcomparison

#print axioms Erdos689.actualMajorArcGenericLocalRightResidues_eq_erase
#print axioms Erdos689.actualMajorArcGenericLocalRightResidues_card
#print axioms Erdos689.actualMajorArcGenericLocalPrimePairs_fiber_card
#print axioms Erdos689.actualMajorArcGenericLocalPrimePairs_card
#print axioms Erdos689.actualMajorArcGenericLocalPrimePairs_card_zmod
#print axioms Erdos689.actualMajorArcGenericLocalFactor_eq_one_sub_inverse_square
#print axioms Erdos689.actualMajorArcGenericLocalPrimePairs_normalized_factor
#print axioms Erdos689.actualMajorArcGenericLocalFactor_pos
#print axioms Erdos689.actualMajorArcGenericLocalFactor_le_one
#print axioms Erdos689.actualMajorArcGenericLocalFactor_product_ge_half

end Erdos689
