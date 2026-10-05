module

public import DeficientCoreConstruction1139

@[expose] public section


/-!
# Exact initial-deficiency classification for Erdős problem #1139

For a fixed positive parameter `z` with `z ≤ y / z`, the genuine initial
mixed conductor is `primorial (y / z) * primorial z`.  This module proves an
exact, bidirectional classification of all targets left deficient by its
zero-residue prime and nested-prime-square classes.

The only target types are the endpoint `1`, primes, products of a prime
strictly below `z` with a prime strictly above `y / z`, and exceptional prime
powers whose prime base lies strictly above `z` but at most `y / z`.

No prime-pattern asymptotic, hypergraph matching, or complete solution of
the original infinite-limsup problem is assumed.
-/

open Finset Filter
open scoped ArithmeticFunction.Omega Topology

namespace Erdos1139

/-- The genuine mixed deficiency is exactly the simultaneous presence of at
most one distinct broad prime divisor and absence of every paid small-prime
square divisor.  This equivalence keeps the historical closed endpoint. -/
theorem fixedParameterCore_deficient_iff_factor_and_square_data
    {y z h : ℕ} (interval : h ∈ Finset.Icc 1 y) :
    h ∈ deficientTargets y (fixedParameterCorePrimes y z)
      (fixedParameterCoreSquared y z) (fun _ => 0) ↔
      (h.primeFactors.filter (fun p => p ≤ y / z)).card ≤ 1 ∧
        ∀ p ∈ fixedParameterCoreSquared y z, ¬ p ^ 2 ∣ h := by
  classical
  constructor
  · intro deficient
    exact ⟨deficient_fixedParameterCore_small_prime_factors_card_le_one
      deficient, fun p hp =>
        deficient_fixedParameterCore_not_dvd_selected_square deficient hp⟩
  · rintro ⟨few_factors, no_square⟩
    have hpositive : 0 < h := (Finset.mem_Icc.mp interval).1
    have empty_square_hits :
        ((fixedParameterCoreSquared y z).filter
          fun p => (0 : ℕ) ≡ h [MOD p ^ 2]) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro p selected square_hit
      exact no_square p selected
        (Nat.modEq_zero_iff_dvd.mp square_hit.symm)
    apply Finset.mem_filter.mpr
    refine ⟨interval, ?_⟩
    rw [fixedParameterCore_zero_broad_hits_eq_small_prime_factors hpositive,
      empty_square_hits]
    simpa using few_factors

/-- Exactly the four target types surviving the paid fixed-parameter core.
The semiprime is genuinely typed by a small prime `< z` and a large prime
`> y / z`; the exceptional prime powers have exponent at least two and a
base strictly above the squared-prime threshold. -/
def FixedParameterCoreDeficientType (y z h : ℕ) : Prop :=
  h = 1 ∨ h.Prime ∨
    (∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ p < z ∧ y / z < q ∧ h = p * q) ∨
    (∃ p e : ℕ,
      p.Prime ∧ z < p ∧ p ≤ y / z ∧ 2 ≤ e ∧ h = p ^ e)

/-- Every genuine initial deficiency has one of the four exact types.  The
large-prime branch uses the already verified strict cofactor classification;
the complementary branch has a unique prime divisor and hence is a prime
power by Mathlib's exact prime-factor theorem. -/
theorem deficient_fixedParameterCore_has_exact_type
    {y z h : ℕ} (parameter_positive : 0 < z)
    (square_threshold : z ≤ y / z)
    (deficient :
      h ∈ deficientTargets y (fixedParameterCorePrimes y z)
        (fixedParameterCoreSquared y z) (fun _ => 0)) :
    FixedParameterCoreDeficientType y z h := by
  classical
  by_cases one : h = 1
  · exact Or.inl one
  have hpositive : 0 < h :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp deficient).1).1
  by_cases large : ∃ q : ℕ, q.Prime ∧ y / z < q ∧ q ∣ h
  · obtain ⟨q, qprime, qlarge, qdivides⟩ := large
    rcases deficient_fixedParameterCore_large_prime_classification
      parameter_positive square_threshold deficient qprime qlarge qdivides with
      equal | ⟨p, pprime, psmall, factorization⟩
    · exact Or.inr (Or.inl (equal.symm ▸ qprime))
    · exact Or.inr (Or.inr (Or.inl
        ⟨p, q, pprime, qprime, psmall, qlarge, factorization⟩))
  · obtain ⟨p, pprime, pdivides⟩ := Nat.exists_prime_and_dvd one
    have all_small : ∀ {q : ℕ}, q.Prime → q ∣ h → q ≤ y / z := by
      intro q qprime qdivides
      by_contra not_small
      exact large ⟨q, qprime, Nat.lt_of_not_ge not_small, qdivides⟩
    have pbound : p ≤ y / z := all_small pprime pdivides
    have unique : ∀ {q : ℕ}, q.Prime → q ∣ h → q = p := by
      intro q qprime qdivides
      exact deficient_fixedParameterCore_small_prime_divisors_equal
        deficient qprime pprime (all_small qprime qdivides)
        pbound qdivides pdivides
    have factorization : h = p ^ h.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hpositive.ne' unique
    let e : ℕ := h.primeFactorsList.length
    by_cases ezero : e = 0
    · have : h = 1 := by simpa [e, ezero] using factorization
      exact False.elim (one this)
    by_cases eone : e = 1
    · have equal : h = p := by simpa [e, eone] using factorization
      exact Or.inr (Or.inl (equal.symm ▸ pprime))
    · have exponent : 2 ≤ e := by omega
      have base_large : z < p := by
        by_contra not_large
        have psmall : p ≤ z := Nat.le_of_not_gt not_large
        have selected : p ∈ fixedParameterCoreSquared y z := by
          apply Finset.mem_inter.mpr
          exact ⟨Nat.mem_primesLE.mpr ⟨psmall, pprime⟩,
            Nat.mem_primesLE.mpr ⟨pbound, pprime⟩⟩
        apply deficient_fixedParameterCore_not_dvd_selected_square
          deficient selected
        rw [factorization]
        exact Nat.pow_dvd_pow p exponent
      exact Or.inr (Or.inr (Or.inr
        ⟨p, e, pprime, base_large, pbound, exponent, factorization⟩))

/-- Every squarefree integer with at most one broad prime factor is
genuinely deficient for the initial core. -/
theorem fixedParameterCore_deficient_of_squarefree
    {y z h : ℕ} (interval : h ∈ Finset.Icc 1 y)
    (squarefree : Squarefree h)
    (few_factors :
      (h.primeFactors.filter (fun p => p ≤ y / z)).card ≤ 1) :
    h ∈ deficientTargets y (fixedParameterCorePrimes y z)
      (fixedParameterCoreSquared y z) (fun _ => 0) := by
  apply (fixedParameterCore_deficient_iff_factor_and_square_data interval).mpr
  refine ⟨few_factors, ?_⟩
  intro p selected square_divides
  have pprime := fixedParameterCorePrimes_prime y z p
    (fixedParameterCoreSquared_subset y z selected)
  exact (Nat.squarefree_iff_prime_squarefree.mp squarefree p pprime)
    (by simpa [pow_two] using square_divides)

/-- Exact bidirectional classification of the initial mixed deficiency.
This preserves all original domains, strict cutoffs, positivity, prime
multiplicity, and the target `h = 1`; no exceptional family is dropped. -/
theorem fixedParameterCore_deficiency_exact_classification
    {y z h : ℕ} (parameter_positive : 0 < z)
    (square_threshold : z ≤ y / z) :
    h ∈ deficientTargets y (fixedParameterCorePrimes y z)
      (fixedParameterCoreSquared y z) (fun _ => 0) ↔
      h ∈ Finset.Icc 1 y ∧ FixedParameterCoreDeficientType y z h := by
  classical
  constructor
  · intro deficient
    exact ⟨(Finset.mem_filter.mp deficient).1,
      deficient_fixedParameterCore_has_exact_type
        parameter_positive square_threshold deficient⟩
  · rintro ⟨interval, target_type⟩
    rcases target_type with one | prime | semiprime | prime_power
    · subst h
      apply fixedParameterCore_deficient_of_squarefree interval
        squarefree_one
      simp
    · apply fixedParameterCore_deficient_of_squarefree interval prime.squarefree
      calc
        (h.primeFactors.filter (fun p => p ≤ y / z)).card ≤
            h.primeFactors.card := Finset.card_filter_le _ _
        _ = 1 := by simp [prime]
    · obtain ⟨p, q, pprime, qprime, psmall, qlarge, factorization⟩ :=
        semiprime
      subst h
      have pbound : p ≤ y / z := (Nat.le_of_lt psmall).trans square_threshold
      have distinct : p ≠ q := by omega
      have squarefree : Squarefree (p * q) :=
        (Nat.squarefree_mul ((Nat.coprime_primes pprime qprime).mpr
          distinct)).mpr ⟨pprime.squarefree, qprime.squarefree⟩
      apply fixedParameterCore_deficient_of_squarefree interval squarefree
      have subset :
          ((p * q).primeFactors.filter (fun r => r ≤ y / z)) ⊆ {p} := by
        intro r hr
        obtain ⟨factor, bound⟩ := Finset.mem_filter.mp hr
        have rprime := Nat.prime_of_mem_primeFactors factor
        have divides := Nat.dvd_of_mem_primeFactors factor
        rcases (rprime.dvd_mul).mp divides with divides_p | divides_q
        · exact Finset.mem_singleton.mpr
            ((Nat.prime_dvd_prime_iff_eq rprime pprime).mp divides_p)
        · have equal : r = q :=
            (Nat.prime_dvd_prime_iff_eq rprime qprime).mp divides_q
          omega
      exact (Finset.card_le_card subset).trans (by simp)
    · obtain ⟨p, e, pprime, base_large, pbound, exponent, factorization⟩ :=
        prime_power
      subst h
      apply (fixedParameterCore_deficient_iff_factor_and_square_data
        interval).mpr
      constructor
      · rw [Nat.primeFactors_prime_pow (by omega) pprime]
        exact (Finset.card_filter_le _ _).trans (by simp)
      · intro q selected square_divides
        have qprime := fixedParameterCorePrimes_prime y z q
          (fixedParameterCoreSquared_subset y z selected)
        have qdivides : q ∣ p ^ e :=
          dvd_trans (by simp [pow_two]) square_divides
        have qdivides_p : q ∣ p := qprime.dvd_of_dvd_pow qdivides
        have equal : q = p :=
          (Nat.prime_dvd_prime_iff_eq qprime pprime).mp qdivides_p
        have qsmall : q ≤ z :=
          Nat.le_of_mem_primesLE (Finset.mem_inter.mp selected).1
        omega


end Erdos1139
