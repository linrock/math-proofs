import ActualLabelLocalCardBridge433

/-!
# Support-uniform cancellation for the actual fixed-label selectors

The local finite-field permutations and global CRT identity identify every
genuine unit-refined selector with its three-state coefficient weight.  This
file sums those *actual selector cardinalities* over both support divisors,
with the indispensable `1 / (a * d)` endpoint factor.  The resulting exact
product is at most one uniformly in the support, and at least one half.
-/

open scoped BigOperators

namespace Erdos689

/-- The genuinely selected fixed-label normalized coefficient: actual progression
selector cardinalities, both actual support divisors, and the true squared
support totient.  Noncoprime coefficient pairs contribute zero. -/
noncomputable def actualFixedLabelSummedSelectorCoefficient
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (q₀ r₀ : ℕ → ℕ → ℕ) : ℝ :=
  ∑ c ∈ ((∏ p ∈ S, p).divisors.product
        (∏ p ∈ S, p).divisors),
    if Nat.Coprime c.1 c.2 then
      (((actualLabelFiberUnitSelectorResidues
        S b z c.1 c.2 (q₀ c.1 c.2) (r₀ c.1 c.2)).card : ℕ) : ℝ) *
        (((∏ p ∈ S, p) : ℕ) : ℝ) /
          ((c.1 : ℝ) * (c.2 : ℝ) *
            ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2)
    else 0

/-- Every actual selected support-divisor summand equals its genuine
three-state coefficient weight.  Seeds are required only for coprime
coefficient pairs, exactly the pairs that can contribute. -/
theorem actualFixedLabelSummedSelectorCoefficient_eq_weight_sum
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (q₀ r₀ : ℕ → ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : ∀ a ∈ (∏ p ∈ S, p).divisors,
      ∀ d ∈ (∏ p ∈ S, p).divisors,
        Nat.Coprime a d → 2 * d * r₀ a d = a * q₀ a d + z) :
    actualFixedLabelSummedSelectorCoefficient S b z q₀ r₀ =
      ∑ c ∈ ((∏ p ∈ S, p).divisors.product
        (∏ p ∈ S, p).divisors),
          actualFixedLabelDoubleCoefficientWeight S z b c.1 c.2 := by
  classical
  unfold actualFixedLabelSummedSelectorCoefficient
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp hc
  by_cases hcoprime : Nat.Coprime c.1 c.2
  · rw [if_pos hcoprime]
    exact (sharpLabel_actual_selector_coefficient_normalization_of_seed
      S z c.1 c.2 (q₀ c.1 c.2) (r₀ c.1 c.2) b
      (fun p hp => (hsupport p hp).1)
      (fun p hp => by have h := (hsupport p hp).2; omega)
      (Nat.mem_divisors.mp ha).1
      (Nat.mem_divisors.mp hd).1
      hcoprime hz hb
      (hseed c.1 ha c.2 hd hcoprime)).symm
  · simp [hcoprime, actualFixedLabelDoubleCoefficientWeight]

/-- The complete *actual* unit-refined selected double-divisor coefficient
sum equals the exact normalized three-state support Euler product. -/
theorem actualFixedLabelSummedSelectorCoefficient_eq_product
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (q₀ r₀ : ℕ → ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : ∀ a ∈ (∏ p ∈ S, p).divisors,
      ∀ d ∈ (∏ p ∈ S, p).divisors,
        Nat.Coprime a d → 2 * d * r₀ a d = a * q₀ a d + z) :
    actualFixedLabelSummedSelectorCoefficient S b z q₀ r₀ =
      ∏ p ∈ S,
        normalizedSwitchedFactor p
          (decide ((2 : ZMod p) * (z : ZMod p) = (b p : ZMod p) ∨
            (2 : ZMod p) * (-(z : ZMod p)) = (b p : ZMod p))) := by
  rw [actualFixedLabelSummedSelectorCoefficient_eq_weight_sum
    S b z q₀ r₀ hsupport hz hb hseed]
  apply actualFixedLabel_double_divisor_coefficient_sum_eq_product
    S z b hsupport
  · intro p hp hzero
    exact hz p hp ((ZMod.natCast_eq_zero_iff z p).mp hzero)
  · intro p hp hzero
    exact hb p hp ((ZMod.natCast_eq_zero_iff (b p) p).mp hzero)

/-- The genuine fixed-label selector-cardinality sum is at most one with an
absolute constant independent of the size, primes, and targets of the
support.  No abstract local-cardinality or independence hypothesis remains. -/
theorem actualFixedLabelSummedSelectorCoefficient_le_one
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (q₀ r₀ : ℕ → ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : ∀ a ∈ (∏ p ∈ S, p).divisors,
      ∀ d ∈ (∏ p ∈ S, p).divisors,
        Nat.Coprime a d → 2 * d * r₀ a d = a * q₀ a d + z) :
    actualFixedLabelSummedSelectorCoefficient S b z q₀ r₀ ≤ 1 := by
  rw [actualFixedLabelSummedSelectorCoefficient_eq_weight_sum
    S b z q₀ r₀ hsupport hz hb hseed]
  apply actualFixedLabel_double_divisor_coefficient_sum_le_one
    S z b hsupport
  · intro p hp hzero
    exact hz p hp ((ZMod.natCast_eq_zero_iff z p).mp hzero)
  · intro p hp hzero
    exact hb p hp ((ZMod.natCast_eq_zero_iff (b p) p).mp hzero)

/-- The same sum of *actual* selected progression cardinalities retains the
absolute universal one-half lower bound. -/
theorem actualFixedLabelSummedSelectorCoefficient_ge_half
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (q₀ r₀ : ℕ → ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : ∀ a ∈ (∏ p ∈ S, p).divisors,
      ∀ d ∈ (∏ p ∈ S, p).divisors,
        Nat.Coprime a d → 2 * d * r₀ a d = a * q₀ a d + z) :
    (1 / 2 : ℝ) ≤ actualFixedLabelSummedSelectorCoefficient S b z q₀ r₀ := by
  rw [actualFixedLabelSummedSelectorCoefficient_eq_weight_sum
    S b z q₀ r₀ hsupport hz hb hseed]
  apply actualFixedLabel_double_divisor_coefficient_sum_ge_half
    S z b hsupport
  · intro p hp hzero
    exact hz p hp ((ZMod.natCast_eq_zero_iff z p).mp hzero)
  · intro p hp hzero
    exact hb p hp ((ZMod.natCast_eq_zero_iff (b p) p).mp hzero)

/-- Purely algebraic rescaling of the genuine normalized selector sum by
`605/12`.  This is not an actual Selberg degree or graph-fiber constant:
the even excluded modulus `2*W` introduces an additional factor of four in
its reciprocal-totient normalization. -/
theorem actualFixedLabelSummedSelectorCoefficient_selberg_leading_le
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (q₀ r₀ : ℕ → ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : ∀ a ∈ (∏ p ∈ S, p).divisors,
      ∀ d ∈ (∏ p ∈ S, p).divisors,
        Nat.Coprime a d → 2 * d * r₀ a d = a * q₀ a d + z) :
    (605 / 12 : ℝ) * actualFixedLabelSummedSelectorCoefficient
        S b z q₀ r₀ ≤ 605 / 12 := by
  have hsum := actualFixedLabelSummedSelectorCoefficient_le_one
    S b z q₀ r₀ hsupport hz hb hseed
  nlinarith

/-- The same purely algebraically rescaled normalized selector sum is below
`51`; this is not a bound for the actual Selberg or graph-degree constant. -/
theorem actualFixedLabelSummedSelectorCoefficient_selberg_leading_lt_51
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ)
    (q₀ r₀ : ℕ → ℕ → ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hseed : ∀ a ∈ (∏ p ∈ S, p).divisors,
      ∀ d ∈ (∏ p ∈ S, p).divisors,
        Nat.Coprime a d → 2 * d * r₀ a d = a * q₀ a d + z) :
    (605 / 12 : ℝ) * actualFixedLabelSummedSelectorCoefficient
        S b z q₀ r₀ < 51 := by
  calc
    (605 / 12 : ℝ) * actualFixedLabelSummedSelectorCoefficient
        S b z q₀ r₀ ≤ 605 / 12 :=
      actualFixedLabelSummedSelectorCoefficient_selberg_leading_le
        S b z q₀ r₀ hsupport hz hb hseed
    _ < 51 := by norm_num

#print axioms Erdos689.actualFixedLabelSummedSelectorCoefficient_eq_weight_sum
#print axioms Erdos689.actualFixedLabelSummedSelectorCoefficient_eq_product
#print axioms Erdos689.actualFixedLabelSummedSelectorCoefficient_le_one
#print axioms Erdos689.actualFixedLabelSummedSelectorCoefficient_ge_half
#print axioms Erdos689.actualFixedLabelSummedSelectorCoefficient_selberg_leading_le
#print axioms Erdos689.actualFixedLabelSummedSelectorCoefficient_selberg_leading_lt_51

end Erdos689
