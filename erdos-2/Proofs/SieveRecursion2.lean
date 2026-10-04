module

public import SieveStage2
public import SieveBase2
public import StripPrime2
public import TailChoice2


@[expose] public section

/-!
# Largest-prime induction for the recursive probability sieve

Recursively strips the largest prime power $p^\gamma \parallel N$ for primes
$p > A$, combining `SieveBase.uniform_base_stage` and
`SieveStage.one_prime_stage` to construct a probability weight on `ZMod N`
whose covered mass is bounded by the $A$-smooth reciprocal sum plus the late-prime
second-moment tail $\sum_{p \mid N,\, p > A} C (\log p)^6 / (p - 1)^2$.
-/

open scoped BigOperators
namespace Erdos2.SieveRecursion

theorem exists_sieve_weight (N : ℕ) [NeZero N]
    (D : Finset ℕ) (r : ℕ → ℤ) (C : ℝ) (A : ℕ) (hC : 0 ≤ C)
    (hprod : ∀ p : ℕ, 2 ≤ p → ∀ s : Finset ℕ,
      (∀ q ∈ s, q.Prime ∧ q < p) →
        (∏ q ∈ s, EulerMoment.factorBound (q : ℝ)) ≤
          C * Real.log (p : ℝ) ^ 6) :
    ∃ w : ProductProbability.ProbabilityWeight (ZMod N),
      ProgressionUpdate.HasProgressionBounds N w.value ∧
      FiniteWeight.mass w.value (CoveringModel.coveredSet D r N) ≤
        (∑ d ∈ D.filter (fun d => ∀ q ∈ d.primeFactors, q ≤ A), 1 / (d : ℝ)) +
        (∑ p ∈ N.primeFactors.filter (fun p => A < p), Analytic.latePrimeCost C p) := by
  classical
  revert ‹NeZero N›
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN
    have _ : NeZero N := hN
    by_cases hsmall : ∀ q ∈ N.primeFactors, q ≤ A
    · obtain ⟨w, hw, hmass⟩ := SieveBase.uniform_base_stage N D r A hsmall
      refine ⟨w, hw, hmass.trans ?_⟩
      have htail : 0 ≤ ∑ p ∈ N.primeFactors.filter (fun p => A < p),
          Analytic.latePrimeCost C p := by
        apply Finset.sum_nonneg
        intro p hp
        dsimp [Analytic.latePrimeCost]
        positivity
      exact le_add_of_nonneg_right htail
    · have hNgt : 1 < N := by
        by_contra h
        have hN1 : N = 1 := by have := NeZero.ne N; omega
        subst N
        simp at hsmall
      obtain ⟨p, γ, Q, hp, hγ, hQ, hQN, hpQ, hdecomp, hmax, hsupport⟩ :=
        StripPrime.exists_largest_prime_decomposition hNgt
      have hpA : A < p := by
        by_contra h
        have hpA' : p ≤ A := by omega
        apply hsmall
        intro q hq
        rw [hsupport] at hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hpA'
        · exact (hmax q hq).le.trans hpA'
      have _ : NeZero Q := ⟨hQ.ne'⟩
      have _ : NeZero p := ⟨hp.ne_zero⟩
      obtain ⟨w, hw, hmass⟩ := ih Q hQN
      have hprodQ := hprod p hp.two_le Q.primeFactors
        (fun q hq => ⟨Nat.prime_of_mem_primeFactors hq, hmax q hq⟩)
      obtain ⟨v, hv, hstep⟩ :=
        SieveStage.one_prime_stage (γ := γ) hp hpQ D r w hw C hprodQ
      have hnot : p ∉ Q.primeFactors.filter (fun p => A < p) := by
        intro h
        exact hpQ (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp h).1)
      have htail :
          (∑ q ∈ N.primeFactors.filter (fun q => A < q), Analytic.latePrimeCost C q) =
            Analytic.latePrimeCost C p +
              ∑ q ∈ Q.primeFactors.filter (fun q => A < q), Analytic.latePrimeCost C q := by
        rw [hsupport]
        simp only [Finset.filter_insert, hpA, ↓reduceIte, Finset.sum_insert hnot]
      subst N
      refine ⟨v, hv, ?_⟩
      calc
        _ ≤ FiniteWeight.mass w.value (CoveringModel.coveredSet D r Q) +
            Analytic.latePrimeCost C p := hstep
        _ ≤ (∑ d ∈ D.filter (fun d => ∀ q ∈ d.primeFactors, q ≤ A), 1 / (d : ℝ)) +
            (∑ q ∈ Q.primeFactors.filter (fun q => A < q), Analytic.latePrimeCost C q) +
            Analytic.latePrimeCost C p := add_le_add hmass le_rfl
        _ = _ := by rw [htail]; ring

end Erdos2.SieveRecursion
