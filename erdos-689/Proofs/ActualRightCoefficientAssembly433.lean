import ActualRightVertexSelectors433

/-!
# Genuine support-uniform fixed-right selector coefficient cancellation

The fixed-right graph coefficient divides the support product.  Support
primes dividing that coefficient select the exceptional branch; the others
select the principal branch, the opposite orientation from the historical
abstract divisor sum.  Using the genuine unit-refined graph selectors, this
module restores the exact `1/a` endpoint and `φ(W)^2` normalization and
proves the complete actual coefficient sum is at most one.
-/

open scoped BigOperators

namespace Erdos689

/-- The actual coefficient branch attached to a fixed-right graph divisor:
coefficient primes contribute the exceptional factor, not the principal one. -/
noncomputable def actualRightVertexCoefficientFactor
    (p y bp a : ℕ) : ℝ :=
  if p ∣ a then actualFixedVertexExceptionalFactor p y
    else actualFixedVertexPrincipalFactor p y bp

/-- Exact finite-field normalization of the genuine fixed-right selector,
retaining its actual coefficient factor and both prime-support units. -/
theorem actualRightVertexCoefficientFactor_local_normalization
    (p y bp a : ℕ)
    (hp : p.Prime)
    (hb : ¬ p ∣ bp)
    (hfixed : (2 : ZMod p) * (y : ZMod p) ≠ (bp : ZMod p)) :
    actualRightVertexCoefficientFactor p y bp a *
      (if p ∣ a then (p : ℝ) else 1) *
      ((p : ℝ) - 1) ^ 2 =
        ((actualRightVertexLocalResidues p y bp a).card : ℝ) * p := by
  have hpone : (p : ℝ) - 1 ≠ 0 := by
    have hcast : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  by_cases ha : p ∣ a
  · rw [actualRightVertexLocalResidues_card_divisible
      p y bp a hp ha hb hfixed]
    by_cases hy : p ∣ y
    · have hyzero : (y : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff y p).mpr hy
      simp [actualRightVertexCoefficientFactor,
        actualFixedVertexExceptionalFactor, ha, hy, hyzero]
    · have hynonzero : (y : ZMod p) ≠ 0 := fun h =>
        hy ((ZMod.natCast_eq_zero_iff y p).mp h)
      simp only [actualRightVertexCoefficientFactor,
        actualFixedVertexExceptionalFactor, ha, hy, hynonzero,
        ↓reduceIte]
      rw [Nat.cast_sub hp.one_le]
      norm_num
      field_simp
  · rw [actualRightVertexLocalResidues_card_principal
      p y bp a hp ha hfixed]
    simp only [actualRightVertexCoefficientFactor,
      actualFixedVertexPrincipalFactor, ha, ↓reduceIte]
    field_simp

/-- Multiplying the actual local branch identities gives the true
coefficient/totient normalization for the genuine global right selector. -/
theorem actualRightVertexCoefficientFactor_product_normalization
    (S : Finset ℕ) (b : ℕ → ℕ) (y a : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (y : ZMod p) ≠ (b p : ZMod p)) :
    (∏ p ∈ S, actualRightVertexCoefficientFactor p y (b p) a) *
      (a : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 =
      (((actualRightVertexUnitSelectorResidues S b y a).card : ℕ) : ℝ) *
        ((∏ p ∈ S, p : ℕ) : ℝ) := by
  rw [actualRightVertexUnitSelectorResidues_card_eq_local_product
    S b y a hsupport,
    ← sharpLabel_support_divisor_prime_product S a hsupport ha,
    prime_support_totient_real_product S hsupport,
    ← Finset.prod_pow,
    Finset.prod_natCast S
      (fun p => (actualRightVertexLocalResidues p y (b p) a).card),
    Finset.prod_natCast S (fun p : ℕ => p)]
  rw [← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact actualRightVertexCoefficientFactor_local_normalization
    p y (b p) a (hsupport p hp) (hb p hp) (hfixed p hp)

/-- The genuine global fixed-right selector gives precisely its true
`#selector * W / (a * φ(W)^2)` coefficient, with no surrogate local set. -/
theorem actualRightVertexCoefficientFactor_product_eq_actual_weight
    (S : Finset ℕ) (b : ℕ → ℕ) (y a : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime)
    (ha : a ∣ ∏ p ∈ S, p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (y : ZMod p) ≠ (b p : ZMod p)) :
    (∏ p ∈ S, actualRightVertexCoefficientFactor p y (b p) a) =
      (((actualRightVertexUnitSelectorResidues S b y a).card : ℕ) : ℝ) *
        ((∏ p ∈ S, p : ℕ) : ℝ) /
          ((a : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2) := by
  have hW : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp =>
    (hsupport p hp).pos
  have hapositive : 0 < a := Nat.pos_of_dvd_of_pos ha hW
  have hphi : 0 < (∏ p ∈ S, p).totient := Nat.totient_pos.mpr hW
  have hdenominator :
      (a : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 ≠ 0 := by
    have hareal : (0 : ℝ) < a := by exact_mod_cast hapositive
    have hphireal : (0 : ℝ) < ((∏ p ∈ S, p).totient : ℕ) := by
      exact_mod_cast hphi
    positivity
  apply (eq_div_iff hdenominator).mpr
  simpa [mul_assoc] using
    actualRightVertexCoefficientFactor_product_normalization
      S b y a hsupport ha hb hfixed

/-- The genuinely oriented right-coefficient divisor sum factors into the
original fixed-vertex switched Euler product; coefficient primes select the
exceptional branch, not the opposite historical abstract orientation. -/
theorem actualRightVertexCoefficientFactor_divisor_sum_eq_product
    (S : Finset ℕ) (b : ℕ → ℕ) (y : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime) :
    (∑ a ∈ (∏ p ∈ S, p).divisors,
      ∏ p ∈ S, actualRightVertexCoefficientFactor p y (b p) a) =
      ∏ p ∈ S, actualFixedVertexNaturalSwitchedFactor p y (b p) := by
  classical
  rw [affineSelector_sum_divisors_eq_powerset S hsupport]
  calc
    (∑ T ∈ S.powerset,
      ∏ p ∈ S,
        actualRightVertexCoefficientFactor p y (b p)
          (∏ q ∈ T, q)) =
        ∑ T ∈ S.powerset,
          (∏ p ∈ T, actualFixedVertexExceptionalFactor p y) *
          ∏ p ∈ S \ T, actualFixedVertexPrincipalFactor p y (b p) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hsubset : T ⊆ S := Finset.mem_powerset.mp hT
      have hTprime : ∀ p ∈ T, p.Prime :=
        fun p hp => hsupport p (hsubset hp)
      have hTprod :
          (∏ p ∈ T,
            actualRightVertexCoefficientFactor p y (b p)
              (∏ q ∈ T, q)) =
          ∏ p ∈ T, actualFixedVertexExceptionalFactor p y := by
        apply Finset.prod_congr rfl
        intro p hp
        have hdivisor : p ∣ ∏ q ∈ T, q :=
          Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
        simp [actualRightVertexCoefficientFactor, hdivisor]
      have hcomplement :
          (∏ p ∈ S \ T,
            actualRightVertexCoefficientFactor p y (b p)
              (∏ q ∈ T, q)) =
          ∏ p ∈ S \ T, actualFixedVertexPrincipalFactor p y (b p) := by
        apply Finset.prod_congr rfl
        intro p hp
        obtain ⟨hpS, hpnot⟩ := Finset.mem_sdiff.mp hp
        have hnotdivisor : ¬ p ∣ ∏ q ∈ T, q := by
          intro hdivisor
          exact hpnot
            (prime_mem_of_dvd_support_product
              (hsupport p hpS) hTprime hdivisor)
        simp [actualRightVertexCoefficientFactor, hnotdivisor]
      calc
        (∏ p ∈ S,
          actualRightVertexCoefficientFactor p y (b p)
            (∏ q ∈ T, q)) =
            (∏ p ∈ S \ T,
              actualRightVertexCoefficientFactor p y (b p)
                (∏ q ∈ T, q)) *
            ∏ p ∈ T,
              actualRightVertexCoefficientFactor p y (b p)
                (∏ q ∈ T, q) :=
              (Finset.prod_sdiff hsubset).symm
        _ = _ := by rw [hTprod, hcomplement]; ring
    _ = ∏ p ∈ S,
      (actualFixedVertexExceptionalFactor p y +
        actualFixedVertexPrincipalFactor p y (b p)) :=
          (Finset.prod_add
            (fun p => actualFixedVertexExceptionalFactor p y)
            (fun p => actualFixedVertexPrincipalFactor p y (b p)) S).symm
    _ = ∏ p ∈ S, actualFixedVertexNaturalSwitchedFactor p y (b p) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [add_comm]
      exact actualFixedVertex_branch_sum_eq p y (b p) (hsupport p hp)

/-- The complete genuinely oriented fixed-right coefficient sum is at most
one uniformly over every actual prime support and switched assignment. -/
theorem actualRightVertexCoefficientFactor_divisor_sum_le_one
    (S : Finset ℕ) (b : ℕ → ℕ) (y : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (y : ZMod p) ≠ (b p : ZMod p)) :
    (∑ a ∈ (∏ p ∈ S, p).divisors,
      ∏ p ∈ S, actualRightVertexCoefficientFactor p y (b p) a) ≤ 1 := by
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (hsupport p hp).1
  rw [actualRightVertexCoefficientFactor_divisor_sum_eq_product S b y hprime]
  rw [← actualFixedVertex_divisor_coefficient_sum_eq_product S y b hprime]
  apply actualFixedVertex_divisor_coefficient_sum_le_one S y b hsupport
  · intro p hp hzero
    exact hb p hp ((ZMod.natCast_eq_zero_iff (b p) p).mp hzero)
  · exact hfixed

/-- The full sum of ACTUAL unit-refined right-graph selector cardinalities,
including the indispensable `1/a` edge coefficient and exact totient
normalization, is support-uniformly bounded by one. -/
theorem actualRightVertexUnitSelector_normalized_sum_le_one
    (S : Finset ℕ) (b : ℕ → ℕ) (y : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (y : ZMod p) ≠ (b p : ZMod p)) :
    (∑ a ∈ (∏ p ∈ S, p).divisors,
      (((actualRightVertexUnitSelectorResidues S b y a).card : ℕ) : ℝ) *
        ((∏ p ∈ S, p : ℕ) : ℝ) /
          ((a : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2)) ≤ 1 := by
  calc
    (∑ a ∈ (∏ p ∈ S, p).divisors,
      (((actualRightVertexUnitSelectorResidues S b y a).card : ℕ) : ℝ) *
        ((∏ p ∈ S, p : ℕ) : ℝ) /
          ((a : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2)) =
      ∑ a ∈ (∏ p ∈ S, p).divisors,
        ∏ p ∈ S, actualRightVertexCoefficientFactor p y (b p) a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (actualRightVertexCoefficientFactor_product_eq_actual_weight
        S b y a (fun p hp => (hsupport p hp).1)
        (Nat.mem_divisors.mp ha).1 hb hfixed).symm
    _ ≤ 1 :=
      actualRightVertexCoefficientFactor_divisor_sum_le_one
        S b y hsupport hb hfixed

#print axioms Erdos689.actualRightVertexCoefficientFactor_local_normalization
#print axioms Erdos689.actualRightVertexCoefficientFactor_product_normalization
#print axioms Erdos689.actualRightVertexCoefficientFactor_product_eq_actual_weight
#print axioms Erdos689.actualRightVertexCoefficientFactor_divisor_sum_eq_product
#print axioms Erdos689.actualRightVertexCoefficientFactor_divisor_sum_le_one
#print axioms Erdos689.actualRightVertexUnitSelector_normalized_sum_le_one

end Erdos689
