module

public import ActualLabelCanonicalSeeds433

@[expose] public section


/-!
# Finite optimized sieve for the sum of actual fixed-label graph fibers

The optimized two-form sieve is instantiated on every genuine coprime pair
of support divisors using the canonical finite-ring seeds.  The theorem sums
actual edge-bounded graph-fiber cardinalities and retains every genuine
Selberg remainder, small-prime exception, and support-prime exception.
-/

open scoped BigOperators

namespace Erdos689

/-- Exactly the genuine coprime pairs of support divisors relevant to a fixed
prime-label fiber. -/
def actualCanonicalLabelCoefficientPairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((∏ p ∈ S, p).divisors.product
    (∏ p ∈ S, p).divisors).filter fun c => Nat.Coprime c.1 c.2

/-- The actual support-unit-refined selector cardinality with its canonical
finite-ring seed. -/
noncomputable def actualCanonicalLabelSelectorCard
    (S : Finset ℕ) (b : ℕ → ℕ) (z a d : ℕ) : ℕ :=
  (actualLabelFiberUnitSelectorResidues S b z a d
    (actualLabelCanonicalSeedQ z a d)
    (actualLabelCanonicalSeedR z a d)).card

/-- The exact genuine first-prime progression length, retaining the true
graph endpoint `2*a*q ≤ n`. -/
noncomputable def actualCanonicalLabelProgressionLength
    (n z a d : ℕ) : ℕ :=
  affineProgressionLength (n / (2 * a) + 1) (2 * d)
    (actualLabelCanonicalSeedQ z a d)

/-- A sieve prime outside the common actual excluded modulus cannot divide
any fixed support prime product. -/
theorem actualLabel_sievePrime_not_dvd_support
    (S P : Finset ℕ) (M p : ℕ)
    (hprime : ∀ q ∈ P, q.Prime)
    (hPM : Nat.Coprime (∏ q ∈ P, q) M)
    (hWM : (∏ s ∈ S, s) ∣ M)
    (hp : p ∈ P) :
    ¬ p ∣ (∏ s ∈ S, s) := by
  intro hdivisor
  have hpP : p ∣ ∏ q ∈ P, q := Finset.dvd_prod_of_mem (fun q => q) hp
  have hpcoprime : Nat.Coprime p M := hPM.coprime_dvd_left hpP
  exact ((hprime p hp).coprime_iff_not_dvd.mp hpcoprime)
    (dvd_trans hdivisor hWM)

/-- The complete finite optimized sieve bound for the sum of the *actual*
edge-bounded fixed-label coefficient fibers.  The same genuine sieve set,
moving excluded modulus, and cutoff are used for every pair.  No seed,
selector-density, local-factor, remainder, or graph-degree estimate is
assumed: every term is the existing proven optimized-sieve expression. -/
theorem actualCanonicalLabelFiber_sum_le_selected_sieve
    (S P : Finset ℕ) (b : ℕ → ℕ)
    (n z M cutoff : ℕ)
    (hsupport : ∀ p ∈ S, p.Prime ∧ 3 < p)
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
      ∑ c ∈ actualCanonicalLabelCoefficientPairs S,
        ((actualCanonicalLabelSelectorCard S b z c.1 c.2 : ℝ) *
          (((actualCanonicalLabelProgressionLength n z c.1 c.2 : ℝ) /
              (((∏ s ∈ S, s) : ℕ) : ℝ) + 1) /
            twoRootSelbergDenominator M cutoff +
              (cutoff : ℝ) ^ 4 +
                ((2 * Nat.primeCounting cutoff : ℕ) : ℝ)) +
          ((2 * S.card : ℕ) : ℝ)) := by
  classical
  have hW : 0 < ∏ s ∈ S, s :=
    Finset.prod_pos fun p hp => (hsupport p hp).1.pos
  apply Finset.sum_le_sum
  intro c hc
  obtain ⟨hdivisors, hcoprime⟩ := Finset.mem_filter.mp hc
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp hdivisors
  have haW : c.1 ∣ ∏ p ∈ S, p := (Nat.mem_divisors.mp ha).1
  have hdW : c.2 ∣ ∏ p ∈ S, p := (Nat.mem_divisors.mp hd).1
  have hapositive : 0 < c.1 := Nat.pos_of_dvd_of_pos haW hW
  have hdpositive : 0 < c.2 := Nat.pos_of_dvd_of_pos hdW hW
  have hcanonical := coprimeSupportDivisors_actualLabelCanonicalSeeds
    S z c.1 c.2 hsupport haW hdW hcoprime
  have hcoprimeDoubled := coprimeSupportDivisors_coprime_doubled
    S c.1 c.2 hsupport haW hcoprime
  have havoida : ∀ p ∈ P, ¬ p ∣ c.1 := by
    intro p hp hpdivisor
    exact actualLabel_sievePrime_not_dvd_support S P M p hprime hPM hWM hp
      (dvd_trans hpdivisor haW)
  have havoidd : ∀ p ∈ P, ¬ p ∣ 2 * c.2 := by
    intro p hp hpdivisor
    rcases ((hprime p hp).dvd_mul).mp hpdivisor with htwo | hdprime
    · have hpbound : p ≤ 2 := Nat.le_of_dvd (by norm_num) htwo
      have hplarge := hlarge p hp
      omega
    · exact actualLabel_sievePrime_not_dvd_support
        S P M p hprime hPM hWM hp (dvd_trans hdprime hdW)
  exact edgeBoundedLabelFiber_card_le_unit_selected_sieve
    S P b M n cutoff z c.1 c.2
      (actualLabelCanonicalSeedQ z c.1 c.2)
      (actualLabelCanonicalSeedR z c.1 c.2)
      (fun p hp => (hsupport p hp).1)
      hW hdpositive hapositive hcanonical.1 hcoprimeDoubled hcanonical.2
      hprime hlarge hcutoff havoidd havoida havoidz hM hPM hWM hprimes


end Erdos689
