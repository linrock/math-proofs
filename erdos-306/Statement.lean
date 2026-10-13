module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Erdos306Unified435
public import HeadPrimeRowAdmissibilityDefectsAndMultiTailWitnesses306
public import Blueprint306

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos306.Challenge

open ArithmeticFunction Finset Erdos306.PrimeResidueAndRowPotential
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

theorem statement_erdos_306 :
    True ↔ ∀ (q : ℚ), 0 < q → Squarefree q.den →
      ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) :=
  Erdos306.erdos_306_iff_true

theorem statement_erdos_306_formal_conjectures :
    ∀ (q : ℚ), 0 < q → Squarefree q.den →
      ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) :=
  Erdos306.erdos_306_formal_conjectures

theorem statement_erdos_306_variants_integer_three_primes (m : ℕ) (h : 0 < m) :
    ∃ k > (0 : ℕ), ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧
    ∀ i, (hik : i < k) → n ⟨i, Nat.lt_succ_of_lt hik⟩ < n ⟨(i + 1), Nat.succ_lt_succ hik⟩ ∧
    (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 3 ∧ Ω (n i) = 3) ∧
    m = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) :=
  Erdos306.erdos_306.variants.integer_three_primes m h

theorem statement_erdos_306_finset_omega_Omega (q : ℚ) (hq : 0 < q) (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ,
      (∀ n ∈ F, ω n = 2 ∧ Ω n = 2) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q :=
  Erdos306.erdos_306_finset_omega_Omega q hq hsq

theorem statement_integer_three_primes_finset (m : ℕ) (hm : 0 < m) :
    ∃ F : Finset ℕ,
      (∀ n ∈ F, ω n = 3 ∧ Ω n = 3 ∧ 1 < n) ∧
      (m : ℚ) = ∑ n ∈ F, (1 : ℚ) / (n : ℚ) :=
  Erdos306.integer_three_primes_finset m hm

theorem statement_exists_semiprime_set_sum_eq_one_iff_ten_le (d : ℕ) :
    (∃ S : Finset ℕ,
      (∀ n ∈ S, ω n = 2 ∧ Ω n = 2) ∧
      (∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ d) ∧
      (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) ↔ 10 ≤ d :=
  Erdos306.PrimeResidueAndRowPotential.exists_semiprime_set_sum_eq_one_iff_ten_le d

theorem statement_semiprime_set_card_ge_fifty_eight_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    58 ≤ S.card :=
  Erdos306.PrimeResidueAndRowPotential.semiprime_set_card_ge_fifty_eight_of_sum_eq_one S hS hdeg hsum

theorem statement_semiprime_set_card_ge_fifty_nine_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    59 ≤ S.card :=
  Erdos306.PrimeResidueAndRowPotential.semiprime_set_card_ge_fifty_nine_of_sum_eq_one S hS hdeg hsum

theorem statement_semiprime_set_card_ge_sixty_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    60 ≤ S.card :=
  Erdos306.PrimeResidueAndRowPotential.semiprime_set_card_ge_sixty_of_sum_eq_one S hS hdeg hsum

theorem statement_semiprime_set_card_ge_sixty_one_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    61 ≤ S.card :=
  Erdos306.PrimeResidueAndRowPotential.semiprime_set_card_ge_sixty_one_of_sum_eq_one S hS hdeg hsum

theorem statement_semiprime_set_card_ge_sixty_three_of_odd_card_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1)
    (hodd : ¬ 2 ∣ S.card) :
    63 ≤ S.card :=
  Erdos306.PrimeResidueAndRowPotential.semiprime_set_card_ge_sixty_three_of_odd_card_of_sum_eq_one S hS hdeg hsum hodd

theorem statement_prime_edges_card_ge_fifty_nine_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    59 ≤ E.card :=
  Erdos306.PrimeResidueAndRowPotential.prime_edges_card_ge_fifty_nine_of_sum_eq_one E hE hdeg hsum

theorem statement_prime_edges_card_ge_sixty_one_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    61 ≤ E.card :=
  Erdos306.PrimeResidueAndRowPotential.prime_edges_card_ge_sixty_one_of_sum_eq_one E hE hdeg hsum

theorem statement_sum_graphNeighbors_two_add_two_mul_card_mod_four_eq_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    ((∑ q ∈ graphNeighbors E 2, q) + 2 * E.card) % 4 = 2 :=
  Erdos306.PrimeResidueAndRowPotential.sum_graphNeighbors_two_add_two_mul_card_mod_four_eq_two E hE hsum

theorem statement_even_card_iff_sum_graphNeighbors_two_mod_four_eq_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    2 ∣ E.card ↔ (∑ q ∈ graphNeighbors E 2, q) % 4 = 2 :=
  Erdos306.PrimeResidueAndRowPotential.even_card_iff_sum_graphNeighbors_two_mod_four_eq_two E hE hsum

theorem statement_odd_card_iff_four_dvd_sum_graphNeighbors_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    ¬ 2 ∣ E.card ↔ 4 ∣ ∑ q ∈ graphNeighbors E 2, q :=
  Erdos306.PrimeResidueAndRowPotential.odd_card_iff_four_dvd_sum_graphNeighbors_two E hE hsum

theorem statement_prime_edges_card_ge_sixty_three_of_odd_card_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1)
    (hodd : ¬ 2 ∣ E.card) :
    63 ≤ E.card :=
  Erdos306.PrimeResidueAndRowPotential.prime_edges_card_ge_sixty_three_of_odd_card_of_sum_eq_one E hE hdeg hsum hodd

theorem statement_witnessEdges71Cell111_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges71Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges71Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges71Cell111.card = 71 ∧
      ¬ 2 ∣ witnessEdges71Cell111.card ∧
      incidenceDegree witnessEdges71Cell111 47 = 0 ∧
      incidenceDegree witnessEdges71Cell111 53 = 3 ∧
      incidenceDegree witnessEdges71Cell111 59 = 3 ∧
      incidenceDegree witnessEdges71Cell111 61 = 5 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges71Cell111 p ≤ d :=
  Erdos306.PrimeResidueAndRowPotential.witnessEdges71Cell111_valid_and_sum_eq_one d hd

theorem statement_witnessEdges72Cell111_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges72Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges72Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges72Cell111.card = 72 ∧
      2 ∣ witnessEdges72Cell111.card ∧
      incidenceDegree witnessEdges72Cell111 53 = 6 ∧
      incidenceDegree witnessEdges72Cell111 59 = 8 ∧
      incidenceDegree witnessEdges72Cell111 61 = 5 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges72Cell111 p ≤ d :=
  Erdos306.PrimeResidueAndRowPotential.witnessEdges72Cell111_valid_and_sum_eq_one d hd

theorem statement_witnessEdges73Cell111_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges73Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges73Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges73Cell111.card = 73 ∧
      ¬ 2 ∣ witnessEdges73Cell111.card ∧
      incidenceDegree witnessEdges73Cell111 53 = 5 ∧
      incidenceDegree witnessEdges73Cell111 59 = 5 ∧
      incidenceDegree witnessEdges73Cell111 61 = 4 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges73Cell111 p ≤ d :=
  Erdos306.PrimeResidueAndRowPotential.witnessEdges73Cell111_valid_and_sum_eq_one d hd

end Erdos306.Challenge

end
