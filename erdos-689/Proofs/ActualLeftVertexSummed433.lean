import ActualLeftVertexDegree433

/-!
# Complete coefficient-summed finite sieve for genuine fixed-left vertices

The actual graph endpoint is `4*d*q ≤ n`; its sharp main term is therefore
`n*φ(W)^2/(4*W^2*D)`.  The genuine support-unit selector normalization
cancels all support-divisor coefficients uniformly.  Every optimized sieve,
incomplete-block, small-prime, and support-prime error remains explicit.
-/

open scoped BigOperators

namespace Erdos689

/-- The actual fixed-left unit selector lies in the genuine canonical
support-product interval. -/
theorem actualLeftVertexUnitSelectorCard_le_support
    (S : Finset ℕ) (b : ℕ → ℕ) (x d : ℕ) :
    (actualLeftVertexUnitSelectorResidues S b x d).card ≤
      ∏ p ∈ S, p := by
  unfold actualLeftVertexUnitSelectorResidues
  simpa using Finset.card_filter_le
    (s := Finset.range (∏ p ∈ S, p))
    (p := fun q : ℕ => ∀ p : S,
      (q : ZMod (p : ℕ)) ∈
        actualLeftVertexLocalResidues (p : ℕ) x (b p) d)

/-- Exact support-uniform coefficient cancellation for the actual left
selectors at their original `1/(4*d*W)` graph endpoint. -/
theorem actualLeftVertexUnitSelector_sharp_density_sum_le
    (S : Finset ℕ) (b : ℕ → ℕ) (n x : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (x : ZMod p) ≠ (b p : ZMod p)) :
    (∑ d ∈ (∏ p ∈ S, p).divisors,
      ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
        ((n : ℝ) /
          (4 * (d : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)))) ≤
      (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2) := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hWreal : (0 : ℝ) < W := by exact_mod_cast hW
  have hphi : 0 < W.totient := Nat.totient_pos.mpr hW
  have hphireal : (0 : ℝ) < W.totient := by exact_mod_cast hphi
  have hnormal := actualLeftVertexUnitSelector_normalized_sum_le_one
    S b x hsupport hb hfixed
  let A : ℝ := (n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  change
    (∑ d ∈ W.divisors,
      ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
        ((n : ℝ) / (4 * (d : ℝ) * (W : ℝ)))) ≤ A
  calc
    (∑ d ∈ W.divisors,
      ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
        ((n : ℝ) / (4 * (d : ℝ) * (W : ℝ)))) =
      A * ∑ d ∈ W.divisors,
        ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
          (W : ℝ) / ((d : ℝ) * (W.totient : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hdpositive : 0 < d :=
          Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hW
        have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpositive
        dsimp [A]
        field_simp
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hnormal hA
    _ = A := mul_one A

/-- Complete finite optimized Selberg estimate for the sum over ALL
genuine support-divisor left graph fibers.  The true graph main term is
`n*φ(W)^2/(4*W^2*D)` and every actual error remains explicit. -/
theorem actualLeftVertexFiber_sum_le_sharp_main_and_errors
    (S P : Finset ℕ) (b : ℕ → ℕ)
    (n x M cutoff : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (x : ZMod p) ≠ (b p : ZMod p))
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hcutoff : 0 < cutoff)
    (havoidx : ∀ p ∈ P, ¬ p ∣ x)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : (∏ p ∈ S, p) ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ cutoff ∧ Nat.Coprime p M)) :
    (∑ d ∈ (∏ p ∈ S, p).divisors,
      ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ)) ≤
      (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (4 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2 *
          twoRootSelbergDenominator M cutoff) +
        (((∏ p ∈ S, p).divisors.card : ℕ) : ℝ) *
          ((((∏ p ∈ S, p) : ℕ) : ℝ) *
            (2 / twoRootSelbergDenominator M cutoff +
              (cutoff : ℝ) ^ 4 +
                ((2 * Nat.primeCounting cutoff : ℕ) : ℝ)) +
              ((2 * S.card : ℕ) : ℝ)) := by
  classical
  let W : ℕ := ∏ p ∈ S, p
  let D : ℝ := twoRootSelbergDenominator M cutoff
  let E : ℝ := (cutoff : ℝ) ^ 4 +
    ((2 * Nat.primeCounting cutoff : ℕ) : ℝ)
  let B : ℝ := ((2 * S.card : ℕ) : ℝ)
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hD : 0 < D := twoRootSelbergDenominator_pos hM (by omega)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm : ∀ d ∈ W.divisors,
      ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ) ≤
        ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
          ((n : ℝ) / (4 * (d : ℝ) * (W : ℝ))) / D +
            ((W : ℝ) * (2 / D + E) + B) := by
    intro d hd
    have hdW : d ∣ W := (Nat.mem_divisors.mp hd).1
    have hdpositive : 0 < d := Nat.pos_of_dvd_of_pos hdW hW
    have havoidd : ∀ p ∈ P, ¬ p ∣ 2 * d := by
      intro p hp hdivisor
      rcases ((hprime p hp).dvd_mul).mp hdivisor with htwo | hdprime
      · have hpbound : p ≤ 2 := Nat.le_of_dvd (by norm_num) htwo
        have hplarge := hlarge p hp
        omega
      · exact actualLabel_sievePrime_not_dvd_support S P M p
          hprime hPM hWM hp (dvd_trans hdprime hdW)
    have hbound := edgeBoundedLeftVertexPrimeParameters_card_le_unit_selected_sieve
      S P b M n cutoff x d (fun p hp => (hsupport p hp).1)
        hW hprime hlarge hcutoff havoidd havoidx hM hPM hWM
          hprimes hdpositive
    have hselector :
        ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) ≤ W := by
      exact_mod_cast actualLeftVertexUnitSelectorCard_le_support S b x d
    have herror : 0 ≤ 2 / D + E := by positivity
    calc
      ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ) ≤
        ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
          (((n : ℝ) / (4 * (d : ℝ) * (W : ℝ)) + 2) / D + E) + B := by
            simpa [W, D, E, B, add_assoc] using hbound
      _ = ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
            ((n : ℝ) / (4 * (d : ℝ) * (W : ℝ))) / D +
          ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
            (2 / D + E) + B := by ring
      _ ≤ ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
            ((n : ℝ) / (4 * (d : ℝ) * (W : ℝ))) / D +
          ((W : ℝ) * (2 / D + E) + B) := by
            nlinarith [mul_le_mul_of_nonneg_right hselector herror]
  have hdensity := actualLeftVertexUnitSelector_sharp_density_sum_le
    S b n x hsupport hb hfixed
  suffices hgoal :
      (∑ d ∈ W.divisors,
        ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ)) ≤
        (n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2 * D) +
          (W.divisors.card : ℝ) *
            ((W : ℝ) * (2 / D + E) + B) by
    simpa [W, D, E, B, add_assoc] using hgoal
  calc
    (∑ d ∈ W.divisors,
      ((edgeBoundedLeftVertexPrimeParameters S b n x d).card : ℝ)) ≤
      ∑ d ∈ W.divisors,
        (((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
          ((n : ℝ) / (4 * (d : ℝ) * (W : ℝ))) / D +
            ((W : ℝ) * (2 / D + E) + B)) :=
      Finset.sum_le_sum hterm
    _ = (∑ d ∈ W.divisors,
          ((actualLeftVertexUnitSelectorResidues S b x d).card : ℝ) *
            ((n : ℝ) / (4 * (d : ℝ) * (W : ℝ)))) / D +
          (W.divisors.card : ℝ) *
            ((W : ℝ) * (2 / D + E) + B) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div]
          simp [nsmul_eq_mul]
          ring
    _ ≤ ((n : ℝ) * (W.totient : ℝ) ^ 2 /
          (4 * (W : ℝ) ^ 2)) / D +
          (W.divisors.card : ℝ) *
            ((W : ℝ) * (2 / D + E) + B) := by
          gcongr
    _ = (n : ℝ) * (W.totient : ℝ) ^ 2 / (4 * (W : ℝ) ^ 2 * D) +
          (W.divisors.card : ℝ) *
            ((W : ℝ) * (2 / D + E) + B) := by
          rw [div_div]

#print axioms Erdos689.actualLeftVertexUnitSelectorCard_le_support
#print axioms Erdos689.actualLeftVertexUnitSelector_sharp_density_sum_le
#print axioms Erdos689.actualLeftVertexFiber_sum_le_sharp_main_and_errors

end Erdos689
