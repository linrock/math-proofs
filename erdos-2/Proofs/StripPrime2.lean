module

public import Mathlib


@[expose] public section

/-!
# Largest-prime power decomposition for natural numbers

Factors any $N > 1$ as $N = Q p^\gamma$ where $p$ is the largest prime factor of
$N$, $\gamma = v_p(N) > 0$, $p \nmid Q$, and every prime factor of $Q$ is
strictly less than $p$.
-/

namespace Erdos2.StripPrime

theorem primeFactors_ordCompl (N p : ℕ) :
    (ordCompl[p] N).primeFactors = N.primeFactors.erase p := by
  rw [← Nat.support_factorization, Nat.factorization_ordCompl]
  simp

theorem strip_prime_decomposition {N p : ℕ}
    (hN : N ≠ 0) (hp : p.Prime) (hpN : p ∣ N) :
    0 < N.factorization p ∧
    0 < ordCompl[p] N ∧
    ordCompl[p] N < N ∧
    ¬p ∣ ordCompl[p] N ∧
    N = ordCompl[p] N * p ^ N.factorization p ∧
    N.primeFactors = insert p (ordCompl[p] N).primeFactors := by
  have hgamma : 0 < N.factorization p := hp.factorization_pos_of_dvd hN hpN
  have hQ : 0 < ordCompl[p] N := Nat.ordCompl_pos p hN
  have hpSupport : p ∈ N.primeFactors := hp.mem_primeFactors hpN hN
  refine ⟨hgamma, hQ, ?_, Nat.not_dvd_ordCompl hp hN, ?_, ?_⟩
  · exact Nat.div_lt_self (Nat.pos_of_ne_zero hN) (one_lt_pow' hp.one_lt hgamma.ne')
  · simpa only [Nat.mul_comm] using (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  · rw [primeFactors_ordCompl, Finset.insert_erase hpSupport]

theorem exists_largest_prime_decomposition {N : ℕ} (hN : 1 < N) :
    ∃ p gamma Q : ℕ,
      p.Prime ∧ 0 < gamma ∧ 0 < Q ∧ Q < N ∧ ¬p ∣ Q ∧
      N = Q * p ^ gamma ∧
      (∀ q ∈ Q.primeFactors, q < p) ∧
      N.primeFactors = insert p Q.primeFactors := by
  obtain ⟨p, hpSupport, hpMax⟩ :=
    Finset.exists_max_image N.primeFactors id (Nat.nonempty_primeFactors.mpr hN)
  have hN0 : N ≠ 0 := by omega
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpSupport
  obtain ⟨hgamma, hQ, hQN, hpQ, hdecomp, hsupport⟩ :=
    strip_prime_decomposition hN0 hp (Nat.dvd_of_mem_primeFactors hpSupport)
  refine ⟨p, N.factorization p, ordCompl[p] N, hp, hgamma, hQ, hQN, hpQ,
    hdecomp, ?_, hsupport⟩
  intro q hq
  have hqErase : q ∈ N.primeFactors.erase p := by
    simpa only [primeFactors_ordCompl] using hq
  obtain ⟨hqp, hqN⟩ := Finset.mem_erase.mp hqErase
  exact lt_of_le_of_ne (hpMax q hqN) hqp

end Erdos2.StripPrime
