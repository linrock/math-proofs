module

public import ActualLabelSummedSieve433

@[expose] public section


/-!
# Sharp main term for the actual summed fixed-label Selberg sieve

The genuine graph endpoint gives progression length `n/(4*a*d)+O(1)`.
After summing the actual unit-refined selector cardinalities, their sharp
support-divisor normalization cancels uniformly; every Selberg remainder
and support-prime exception remains explicit.
-/

open scoped BigOperators

namespace Erdos689

/-- The exact genuine fixed-label progression length retains both support
divisors and has an absolute additive endpoint error of at most two. -/
theorem actualCanonicalLabelProgressionLength_le_sharp_endpoint
    (n z a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    (actualCanonicalLabelProgressionLength n z a d : ℝ) ≤
      (n : ℝ) / (4 * (a : ℝ) * (d : ℝ)) + 2 := by
  have hlength := affine_progression_length_real_le
    (n / (2 * a) + 1) (2 * d) (actualLabelCanonicalSeedQ z a d)
  have hdivision :
      ((n / (2 * a) : ℕ) : ℝ) ≤ (n : ℝ) / ((2 * a : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hareal : (0 : ℝ) < a := by exact_mod_cast ha
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hfraction : (1 : ℝ) / (2 * d) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mpr
    have hdone : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  change (actualCanonicalLabelProgressionLength n z a d : ℝ) ≤ _
  calc
    (actualCanonicalLabelProgressionLength n z a d : ℝ) ≤
        (((n / (2 * a) + 1 : ℕ) : ℝ) /
          ((2 * d : ℕ) : ℝ)) + 1 := hlength
    _ = (((n / (2 * a) : ℕ) : ℝ) + 1) /
          (2 * (d : ℝ)) + 1 := by push_cast; ring
    _ ≤ ((n : ℝ) / (2 * (a : ℝ)) + 1) /
          (2 * (d : ℝ)) + 1 := by
      gcongr
      simpa using hdivision
    _ = (n : ℝ) / (4 * (a : ℝ) * (d : ℝ)) +
          1 / (2 * (d : ℝ)) + 1 := by
      field_simp
      ring
    _ ≤ (n : ℝ) / (4 * (a : ℝ) * (d : ℝ)) + 2 := by
      linarith

/-- Dividing the true fixed-label progression by the support modulus keeps
the sharp coefficient `1/(4*a*d*W)` and costs at most three endpoint units. -/
theorem actualCanonicalLabelProgressionLength_support_normalized_le
    (S : Finset ℕ) (n z a d : ℕ)
    (hW : 0 < ∏ p ∈ S, p) (ha : 0 < a) (hd : 0 < d) :
    (actualCanonicalLabelProgressionLength n z a d : ℝ) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 ≤
      (n : ℝ) /
        (4 * (a : ℝ) * (d : ℝ) *
          (((∏ p ∈ S, p) : ℕ) : ℝ)) + 3 := by
  have hWreal : (0 : ℝ) < ((∏ p ∈ S, p) : ℕ) := by
    exact_mod_cast hW
  have hWone : (1 : ℝ) ≤ ((∏ p ∈ S, p) : ℕ) := by
    exact_mod_cast hW
  have hendpoint :=
    actualCanonicalLabelProgressionLength_le_sharp_endpoint n z a d ha hd
  have hquotient :
      (2 : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hWreal).mpr
    nlinarith
  calc
    (actualCanonicalLabelProgressionLength n z a d : ℝ) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 ≤
      ((n : ℝ) / (4 * (a : ℝ) * (d : ℝ)) + 2) /
        (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 := by
          gcongr
    _ = (n : ℝ) /
          (4 * (a : ℝ) * (d : ℝ) *
            (((∏ p ∈ S, p) : ℕ) : ℝ)) +
          2 / (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 := by
          field_simp
    _ ≤ (n : ℝ) /
          (4 * (a : ℝ) * (d : ℝ) *
            (((∏ p ∈ S, p) : ℕ) : ℝ)) + 3 := by
          linarith

/-- Reindexing the exact canonical coefficient sum as a sum over genuine
coprime support-divisor pairs does not discard or replace actual selector
cardinalities. -/
theorem actualCanonicalLabelSelector_normalized_sum_eq
    (S : Finset ℕ) (b : ℕ → ℕ) (z : ℕ) :
    (∑ c ∈ actualCanonicalLabelCoefficientPairs S,
      (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
        (((∏ p ∈ S, p) : ℕ) : ℝ) /
          ((c.1 : ℝ) * (c.2 : ℝ) *
            ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2)) =
      actualFixedLabelSummedSelectorCoefficient S b z
        (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z) := by
  classical
  unfold actualCanonicalLabelCoefficientPairs
    actualFixedLabelSummedSelectorCoefficient
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hcoprime
  · rfl
  · rfl

/-- Every genuine canonical unit-refined selector is a subset of the actual
support-residue interval and therefore has at most `W` classes. -/
theorem actualCanonicalLabelSelectorCard_le_support
    (S : Finset ℕ) (b : ℕ → ℕ) (z a d : ℕ) :
    actualCanonicalLabelSelectorCard S b z a d ≤ ∏ p ∈ S, p := by
  classical
  unfold actualCanonicalLabelSelectorCard
  rw [← Finset.card_range (∏ p ∈ S, p)]
  apply Finset.card_le_card
  intro k hk
  have hunit := Finset.mem_filter.mp hk
  have hselector := Finset.mem_filter.mp hunit.1
  exact hselector.1

/-- The sharp sum of the *actual* selector-cardinality main terms cancels
uniformly over both support divisors.  Its exact surviving factor is
`n * φ(W)^2 / (4 * W^2)`, independent of the number of coefficient pairs. -/
theorem actualCanonicalLabelSelector_sharp_density_sum_le
    (S : Finset ℕ) (b : ℕ → ℕ) (n z : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p) :
    (∑ c ∈ actualCanonicalLabelCoefficientPairs S,
      (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
        ((n : ℝ) /
          (4 * (c.1 : ℝ) * (c.2 : ℝ) *
            (((∏ p ∈ S, p) : ℕ) : ℝ)))) ≤
      (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2) := by
  classical
  have hW : 0 < ∏ p ∈ S, p :=
    Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hWreal : (0 : ℝ) < ((∏ p ∈ S, p) : ℕ) := by
    exact_mod_cast hW
  have hphi : 0 < (∏ p ∈ S, p).totient := Nat.totient_pos.mpr hW
  have hphireal : (0 : ℝ) < ((∏ p ∈ S, p).totient : ℕ) := by
    exact_mod_cast hphi
  let A : ℝ :=
    (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
      (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hnormal := actualFixedLabelCanonicalSummedSelectorCoefficient_le_one
    S b z hsupport hz hb
  calc
    (∑ c ∈ actualCanonicalLabelCoefficientPairs S,
      (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
        ((n : ℝ) /
          (4 * (c.1 : ℝ) * (c.2 : ℝ) *
            (((∏ p ∈ S, p) : ℕ) : ℝ)))) =
      A * (∑ c ∈ actualCanonicalLabelCoefficientPairs S,
        (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
          (((∏ p ∈ S, p) : ℕ) : ℝ) /
            ((c.1 : ℝ) * (c.2 : ℝ) *
              ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨hdivisors, _⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hd⟩ := Finset.mem_product.mp hdivisors
      have hapositive : 0 < c.1 :=
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hW
      have hdpositive : 0 < c.2 :=
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hW
      have hareal : (0 : ℝ) < c.1 := by exact_mod_cast hapositive
      have hdreal : (0 : ℝ) < c.2 := by exact_mod_cast hdpositive
      dsimp [A]
      field_simp
    _ = A * actualFixedLabelSummedSelectorCoefficient S b z
      (actualLabelCanonicalSeedQ z) (actualLabelCanonicalSeedR z) := by
      rw [actualCanonicalLabelSelector_normalized_sum_eq]
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hnormal hA
    _ = (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2) := by
          simp [A]

/-- Full finite optimized sieve bound for the sum of the *actual*
edge-bounded fixed-label fibers.  Its main term has the exact support-uniform
coefficient `φ(W)^2/(4*W^2*D)`, where `D` is the genuine Selberg
denominator; all fourth-power remainders, small-sieve-prime exceptions,
incomplete-block errors, and switched-support-prime exceptions remain
explicit.  No graph-degree or analytic remainder estimate is assumed. -/
theorem actualCanonicalLabelFiber_sum_le_sharp_main_and_errors
    (S P : Finset ℕ) (b : ℕ → ℕ)
    (n z M cutoff : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hz : ∀ p ∈ S, ¬ p ∣ z)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hcutoff : 0 < cutoff)
    (havoidz : ∀ p ∈ P, ¬ p ∣ z)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : (∏ s ∈ S, s) ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ cutoff ∧ Nat.Coprime p M)) :
    (∑ c ∈ actualCanonicalLabelCoefficientPairs S,
      ((edgeBoundedLabelFiberSwitchedPrimeParameters
        S b n z c.1 c.2).card : ℝ)) ≤
      (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
          (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2 *
            twoRootSelbergDenominator M cutoff) +
        ((actualCanonicalLabelCoefficientPairs S).card : ℝ) *
          ((((∏ p ∈ S, p) : ℕ) : ℝ) *
            (3 / twoRootSelbergDenominator M cutoff +
              (cutoff : ℝ) ^ 4 +
                ((2 * Nat.primeCounting cutoff : ℕ) : ℝ)) +
              ((2 * S.card : ℕ) : ℝ)) := by
  classical
  let W : ℕ := ∏ p ∈ S, p
  let F := actualCanonicalLabelCoefficientPairs S
  let D : ℝ := twoRootSelbergDenominator M cutoff
  let E : ℝ := (cutoff : ℝ) ^ 4 +
    ((2 * Nat.primeCounting cutoff : ℕ) : ℝ)
  let B : ℝ := ((2 * S.card : ℕ) : ℝ)
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hD : 0 < D := twoRootSelbergDenominator_pos hM (by omega)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hstart := actualCanonicalLabelFiber_sum_le_selected_sieve
    S P b n z M cutoff hsupport hprime hlarge hcutoff havoidz
    hM hPM hWM hprimes
  have hterm : ∀ c ∈ F,
      (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
          (((actualCanonicalLabelProgressionLength n z c.1 c.2 : ℝ) /
              (W : ℝ) + 1) / D + E) + B ≤
        (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
            ((n : ℝ) /
              (4 * (c.1 : ℝ) * (c.2 : ℝ) * (W : ℝ))) / D +
          ((W : ℝ) * (3 / D + E) + B) := by
    intro c hc
    obtain ⟨hdivisors, _⟩ := Finset.mem_filter.mp hc
    obtain ⟨ha, hd⟩ := Finset.mem_product.mp hdivisors
    have hapositive : 0 < c.1 :=
      Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hW
    have hdpositive : 0 < c.2 :=
      Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hW
    have hendpoint :=
      actualCanonicalLabelProgressionLength_support_normalized_le
        S n z c.1 c.2 hW hapositive hdpositive
    have hselector :
        (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) ≤ W := by
      exact_mod_cast actualCanonicalLabelSelectorCard_le_support
        S b z c.1 c.2
    calc
      (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
          (((actualCanonicalLabelProgressionLength n z c.1 c.2 : ℝ) /
              (W : ℝ) + 1) / D + E) + B ≤
        (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
          (((n : ℝ) /
            (4 * (c.1 : ℝ) * (c.2 : ℝ) * (W : ℝ)) + 3) /
              D + E) + B := by
            gcongr
      _ = (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
            ((n : ℝ) /
              (4 * (c.1 : ℝ) * (c.2 : ℝ) * (W : ℝ))) / D +
          (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
            (3 / D + E) + B := by ring
      _ ≤ (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
            ((n : ℝ) /
              (4 * (c.1 : ℝ) * (c.2 : ℝ) * (W : ℝ))) / D +
          ((W : ℝ) * (3 / D + E) + B) := by
            have herror : 0 ≤ 3 / D + E := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hselector herror]
  have hdensity := actualCanonicalLabelSelector_sharp_density_sum_le
    S b n z hsupport hz hb
  suffices hgoal :
      (∑ c ∈ F,
        ((edgeBoundedLabelFiberSwitchedPrimeParameters
          S b n z c.1 c.2).card : ℝ)) ≤
        (n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2 * D) +
          (F.card : ℝ) * ((W : ℝ) * (3 / D + E) + B) by
    simpa [F, W, D, E, B, add_assoc] using hgoal
  calc
    (∑ c ∈ F,
      ((edgeBoundedLabelFiberSwitchedPrimeParameters
        S b n z c.1 c.2).card : ℝ)) ≤
      ∑ c ∈ F,
        ((actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
          (((actualCanonicalLabelProgressionLength n z c.1 c.2 : ℝ) /
            (W : ℝ) + 1) / D + E) + B) := by
          simpa [F, W, D, E, B, add_assoc] using hstart
    _ ≤ ∑ c ∈ F,
      ((actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
          ((n : ℝ) /
            (4 * (c.1 : ℝ) * (c.2 : ℝ) * (W : ℝ))) / D +
        ((W : ℝ) * (3 / D + E) + B)) := by
          exact Finset.sum_le_sum hterm
    _ = (∑ c ∈ F,
          (actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
            ((n : ℝ) /
              (4 * (c.1 : ℝ) * (c.2 : ℝ) * (W : ℝ)))) / D +
          (F.card : ℝ) * ((W : ℝ) * (3 / D + E) + B) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_div]
            simp [nsmul_eq_mul]
            ring
    _ ≤ ((n : ℝ) * (W.totient : ℝ) ^ 2 /
          (4 * (W : ℝ) ^ 2)) / D +
          (F.card : ℝ) * ((W : ℝ) * (3 / D + E) + B) := by
            gcongr
    _ = (n : ℝ) * (W.totient : ℝ) ^ 2 /
          (4 * (W : ℝ) ^ 2 * D) +
          (F.card : ℝ) * ((W : ℝ) * (3 / D + E) + B) := by
            rw [div_div]

#print axioms Erdos689.actualCanonicalLabelProgressionLength_le_sharp_endpoint
#print axioms Erdos689.actualCanonicalLabelProgressionLength_support_normalized_le
#print axioms Erdos689.actualCanonicalLabelSelector_normalized_sum_eq
#print axioms Erdos689.actualCanonicalLabelSelectorCard_le_support
#print axioms Erdos689.actualCanonicalLabelSelector_sharp_density_sum_le
#print axioms Erdos689.actualCanonicalLabelFiber_sum_le_sharp_main_and_errors

end Erdos689
