module

public import ActualRightVertexDegree433
public import ActualRightCoefficientAssembly433

@[expose] public section


/-!
# Complete coefficient-summed finite Selberg bound for actual right vertices

The true descending graph fibers carry the exact edge endpoint `n/(2*a)`.
Combining their genuine support-unit selectors with the independently
verified reversed-branch coefficient normalization yields a support-uniform
main term `n*φ(W)^2/(2*W^2*D)`.  Every real optimized Selberg, incomplete
block, small-prime, and support-prime error is retained explicitly.
-/

open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Erdos689

/-- Every genuine natural fixed-right support-unit selector lies inside
the actual canonical support interval and hence has at most `W` classes. -/
theorem actualRightVertexUnitSelectorCard_le_support
    (S : Finset ℕ) (b : ℕ → ℕ) (y a : ℕ) :
    (actualRightVertexUnitSelectorResidues S b y a).card ≤
      ∏ p ∈ S, p := by
  unfold actualRightVertexUnitSelectorResidues
  simpa using Finset.card_filter_le
    (s := Finset.range (∏ p ∈ S, p))
    (p := fun q : ℕ => ∀ p : S,
      (q : ZMod (p : ℕ)) ∈
        actualRightVertexLocalResidues (p : ℕ) y (b p) a)

/-- The coefficient-summed ACTUAL right-selector main density is uniformly
at most the exact `n*φ(W)^2/(2*W^2)` required by the true graph endpoint.
No selector is replaced by its switched-only enlargement. -/
theorem actualRightVertexUnitSelector_sharp_density_sum_le
    (S : Finset ℕ) (b : ℕ → ℕ) (n y : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (y : ZMod p) ≠ (b p : ZMod p)) :
    (∑ a ∈ (∏ p ∈ S, p).divisors,
      ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
        ((n : ℝ) /
          (2 * (a : ℝ) * (((∏ p ∈ S, p) : ℕ) : ℝ)))) ≤
      (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (2 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2) := by
  let W : ℕ := ∏ p ∈ S, p
  have hW : 0 < W := Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  have hWreal : (0 : ℝ) < W := by exact_mod_cast hW
  have hphi : 0 < W.totient := Nat.totient_pos.mpr hW
  have hphireal : (0 : ℝ) < W.totient := by exact_mod_cast hphi
  have hnormal := actualRightVertexUnitSelector_normalized_sum_le_one
    S b y hsupport hb hfixed
  let A : ℝ := (n : ℝ) * (W.totient : ℝ) ^ 2 / (2 * (W : ℝ) ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  change
    (∑ a ∈ W.divisors,
      ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
        ((n : ℝ) / (2 * (a : ℝ) * (W : ℝ)))) ≤ A
  calc
    (∑ a ∈ W.divisors,
      ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
        ((n : ℝ) / (2 * (a : ℝ) * (W : ℝ)))) =
      A * ∑ a ∈ W.divisors,
        ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
          (W : ℝ) / ((a : ℝ) * (W.totient : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        have hapositive : 0 < a :=
          Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hW
        have hareal : (0 : ℝ) < a := by exact_mod_cast hapositive
        dsimp [A]
        field_simp
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hnormal hA
    _ = A := mul_one A

/-- The full finite optimized Selberg bound summed over EVERY genuine
support-divisor coefficient of the edge-bounded actual fixed-right graph
fiber.  The main term is support-uniform after the true selector
cancellation, and all actual fourth-power, small-sieve-prime, endpoint,
and support-prime errors remain explicit. -/
theorem actualRightVertexFiber_sum_le_sharp_main_and_errors
    (S P : Finset ℕ) (b : ℕ → ℕ)
    (n y M cutoff : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
    (hb : ∀ p ∈ S, ¬ p ∣ b p)
    (hfixed : ∀ p ∈ S,
      (2 : ZMod p) * (y : ZMod p) ≠ (b p : ZMod p))
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 2 < p)
    (hcutoff : 0 < cutoff)
    (havoidy : ∀ p ∈ P, ¬ p ∣ y)
    (hM : 2 ∣ M)
    (hPM : Nat.Coprime (∏ p ∈ P, p) M)
    (hWM : (∏ p ∈ S, p) ∣ M)
    (hprimes : ∀ p : ℕ, p.Prime →
      (p ∣ ∏ q ∈ P, q ↔ p ≤ cutoff ∧ Nat.Coprime p M)) :
    (∑ a ∈ (∏ p ∈ S, p).divisors,
      ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ)) ≤
      (n : ℝ) * ((((∏ p ∈ S, p).totient : ℕ) : ℝ)) ^ 2 /
        (2 * (((∏ p ∈ S, p) : ℕ) : ℝ) ^ 2 *
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
  have hterm : ∀ a ∈ W.divisors,
      ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ) ≤
        ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
          ((n : ℝ) / (2 * (a : ℝ) * (W : ℝ))) / D +
            ((W : ℝ) * (2 / D + E) + B) := by
    intro a ha
    have haW : a ∣ W := (Nat.mem_divisors.mp ha).1
    have hapositive : 0 < a := Nat.pos_of_dvd_of_pos haW hW
    have havoida : ∀ p ∈ P, ¬ p ∣ a := by
      intro p hp hdivisor
      exact actualLabel_sievePrime_not_dvd_support S P M p
        hprime hPM hWM hp (dvd_trans hdivisor haW)
    have hbound := edgeBoundedRightVertexPrimeParameters_card_le_unit_selected_sieve
      S P b M n cutoff y a (fun p hp => (hsupport p hp).1)
        hW hprime hlarge hcutoff havoida havoidy hM hPM hWM
          hprimes hapositive
    have hselector :
        ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) ≤ W := by
      exact_mod_cast actualRightVertexUnitSelectorCard_le_support S b y a
    have herror : 0 ≤ 2 / D + E := by positivity
    calc
      ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ) ≤
        ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
          (((n : ℝ) / (2 * (a : ℝ) * (W : ℝ)) + 2) / D + E) + B := by
            simpa [W, D, E, B, add_assoc] using hbound
      _ = ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
            ((n : ℝ) / (2 * (a : ℝ) * (W : ℝ))) / D +
          ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
            (2 / D + E) + B := by ring
      _ ≤ ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
            ((n : ℝ) / (2 * (a : ℝ) * (W : ℝ))) / D +
          ((W : ℝ) * (2 / D + E) + B) := by
            nlinarith [mul_le_mul_of_nonneg_right hselector herror]
  have hdensity := actualRightVertexUnitSelector_sharp_density_sum_le
    S b n y hsupport hb hfixed
  suffices hgoal :
      (∑ a ∈ W.divisors,
        ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ)) ≤
        (n : ℝ) * (W.totient : ℝ) ^ 2 / (2 * (W : ℝ) ^ 2 * D) +
          (W.divisors.card : ℝ) *
            ((W : ℝ) * (2 / D + E) + B) by
    simpa [W, D, E, B, add_assoc] using hgoal
  calc
    (∑ a ∈ W.divisors,
      ((edgeBoundedRightVertexPrimeParameters S b n y a).card : ℝ)) ≤
      ∑ a ∈ W.divisors,
        (((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
          ((n : ℝ) / (2 * (a : ℝ) * (W : ℝ))) / D +
            ((W : ℝ) * (2 / D + E) + B)) :=
      Finset.sum_le_sum hterm
    _ = (∑ a ∈ W.divisors,
          ((actualRightVertexUnitSelectorResidues S b y a).card : ℝ) *
            ((n : ℝ) / (2 * (a : ℝ) * (W : ℝ)))) / D +
          (W.divisors.card : ℝ) *
            ((W : ℝ) * (2 / D + E) + B) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div]
          simp [nsmul_eq_mul]
          ring
    _ ≤ ((n : ℝ) * (W.totient : ℝ) ^ 2 /
          (2 * (W : ℝ) ^ 2)) / D +
          (W.divisors.card : ℝ) *
            ((W : ℝ) * (2 / D + E) + B) := by
          gcongr
    _ = (n : ℝ) * (W.totient : ℝ) ^ 2 / (2 * (W : ℝ) ^ 2 * D) +
          (W.divisors.card : ℝ) *
            ((W : ℝ) * (2 / D + E) + B) := by
          rw [div_div]

#print axioms Erdos689.actualRightVertexUnitSelectorCard_le_support
#print axioms Erdos689.actualRightVertexUnitSelector_sharp_density_sum_le
#print axioms Erdos689.actualRightVertexFiber_sum_le_sharp_main_and_errors

end Erdos689
