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

public import Mathlib

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos306.Core.PrimeResidueAndRowPotential

def incidenceDegree {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (v : α) : ℕ :=
  (E.filter fun e => e.1 = v).card + (E.filter fun e => e.2 = v).card

def rightNeighbors (E : Finset (ℕ × ℕ)) (p : ℕ) : Finset ℕ :=
  (E.filter fun e => e.1 = p).image Prod.snd

def leftNeighbors (E : Finset (ℕ × ℕ)) (p : ℕ) : Finset ℕ :=
  (E.filter fun e => e.2 = p).image Prod.fst

def graphNeighbors (E : Finset (ℕ × ℕ)) (p : ℕ) : Finset ℕ :=
  rightNeighbors E p ∪ leftNeighbors E p

def primes61 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}

def witnessEdges71Cell111 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 37),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 29), (13, 37), (13, 43), (17, 19), (17, 23), (17, 43), (17, 53), (19, 29),
   (19, 41), (19, 43), (23, 29), (23, 31), (23, 41), (23, 43), (29, 31), (29, 41), (29, 43), (29, 61),
   (31, 41), (31, 43), (31, 59), (31, 61), (37, 41), (37, 53), (37, 59), (37, 61), (41, 61), (43, 59),
   (43, 61)}

def witnessEdges72Cell111 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 23), (13, 37), (13, 59), (17, 19), (17, 29), (17, 37), (17, 59), (19, 23),
   (19, 53), (23, 41), (23, 43), (23, 59), (29, 31), (29, 37), (29, 43), (29, 53), (29, 59), (29, 61),
   (31, 61), (37, 53), (37, 59), (37, 61), (41, 43), (41, 47), (41, 59), (41, 61), (43, 59), (43, 61),
   (47, 53), (53, 59)}

def witnessEdges73Cell111 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 37),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 23), (13, 37), (13, 59), (17, 23), (17, 37), (17, 41), (17, 53), (19, 23),
   (19, 29), (19, 31), (19, 41), (23, 47), (23, 61), (29, 31), (29, 43), (29, 47), (29, 61), (31, 37),
   (31, 41), (31, 47), (31, 53), (31, 59), (37, 41), (37, 43), (37, 59), (41, 43), (41, 47), (41, 53),
   (43, 61), (53, 59), (59, 61)}

end Erdos306.Core.PrimeResidueAndRowPotential

namespace Erdos306

open ArithmeticFunction Finset Erdos306.Core.PrimeResidueAndRowPotential
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

theorem erdos_306 :
    ∀ (q : ℚ), 0 < q → Squarefree q.den →
      ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) := by
  sorry

namespace variants

theorem integer_three_primes (m : ℕ) (h : 0 < m) :
    ∃ k > (0 : ℕ), ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧
    ∀ i, (hik : i < k) → n ⟨i, Nat.lt_succ_of_lt hik⟩ < n ⟨(i + 1), Nat.succ_lt_succ hik⟩ ∧
    (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 3 ∧ Ω (n i) = 3) ∧
    m = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) := by
  sorry

theorem finset_omega_Omega (q : ℚ) (hq : 0 < q) (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ,
      (∀ n ∈ F, ω n = 2 ∧ Ω n = 2) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q := by
  sorry

theorem integer_three_primes_finset (m : ℕ) (hm : 0 < m) :
    ∃ F : Finset ℕ,
      (∀ n ∈ F, ω n = 3 ∧ Ω n = 3 ∧ 1 < n) ∧
      (m : ℚ) = ∑ n ∈ F, (1 : ℚ) / (n : ℚ) := by
  sorry

theorem incidence_ten_iff (d : ℕ) :
    (∃ S : Finset ℕ,
      (∀ n ∈ S, ω n = 2 ∧ Ω n = 2) ∧
      (∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ d) ∧
      (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) ↔ 10 ≤ d := by
  sorry

theorem semiprime_card_ge_fifty_eight
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    58 ≤ S.card := by
  sorry

theorem semiprime_card_ge_fifty_nine
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    59 ≤ S.card := by
  sorry

theorem semiprime_card_ge_sixty
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    60 ≤ S.card := by
  sorry

theorem semiprime_card_ge_sixty_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    61 ≤ S.card := by
  sorry

theorem semiprime_card_ge_sixty_three_of_odd_card
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ω n = 2 ∧ Ω n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1)
    (hodd : ¬ 2 ∣ S.card) :
    63 ≤ S.card := by
  sorry

theorem prime_edges_card_ge_fifty_nine
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    59 ≤ E.card := by
  sorry

theorem prime_edges_card_ge_sixty_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    61 ≤ E.card := by
  sorry

theorem sum_graphNeighbors_two_add_two_mul_card_mod_four_eq_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    ((∑ q ∈ graphNeighbors E 2, q) + 2 * E.card) % 4 = 2 := by
  sorry

theorem even_card_iff_sum_graphNeighbors_two_mod_four_eq_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    2 ∣ E.card ↔ (∑ q ∈ graphNeighbors E 2, q) % 4 = 2 := by
  sorry

theorem odd_card_iff_four_dvd_sum_graphNeighbors_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    ¬ 2 ∣ E.card ↔ 4 ∣ ∑ q ∈ graphNeighbors E 2, q := by
  sorry

theorem prime_edges_card_ge_sixty_three_of_odd_card
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1)
    (hodd : ¬ 2 ∣ E.card) :
    63 ≤ E.card := by
  sorry

theorem witness_71_cell_111 (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges71Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges71Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges71Cell111.card = 71 ∧
      ¬ 2 ∣ witnessEdges71Cell111.card ∧
      incidenceDegree witnessEdges71Cell111 47 = 0 ∧
      incidenceDegree witnessEdges71Cell111 53 = 3 ∧
      incidenceDegree witnessEdges71Cell111 59 = 3 ∧
      incidenceDegree witnessEdges71Cell111 61 = 5 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges71Cell111 p ≤ d := by
  sorry

theorem witness_72_cell_111 (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges72Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges72Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges72Cell111.card = 72 ∧
      2 ∣ witnessEdges72Cell111.card ∧
      incidenceDegree witnessEdges72Cell111 53 = 6 ∧
      incidenceDegree witnessEdges72Cell111 59 = 8 ∧
      incidenceDegree witnessEdges72Cell111 61 = 5 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges72Cell111 p ≤ d := by
  sorry

theorem witness_73_cell_111 (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges73Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges73Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges73Cell111.card = 73 ∧
      ¬ 2 ∣ witnessEdges73Cell111.card ∧
      incidenceDegree witnessEdges73Cell111 53 = 5 ∧
      incidenceDegree witnessEdges73Cell111 59 = 5 ∧
      incidenceDegree witnessEdges73Cell111 61 = 4 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges73Cell111 p ≤ d := by
  sorry

end variants

end Erdos306

end
