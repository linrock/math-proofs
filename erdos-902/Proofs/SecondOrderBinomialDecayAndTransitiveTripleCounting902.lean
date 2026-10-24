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
public import Erdos902Unified435
public import SzekeresParityRefinementAndTightenedBinomialBounds902

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048

noncomputable section
open scoped Classical BigOperators

/-!
# Erdős Problem 902: Higher-Order Binomial Decay Hierarchy, Unit-Leading `O(n^2 2^n)` Upper Bounds, and Tournament Transitive/Cyclic Triple Counting

This module (`SecondOrderBinomialDecayAndTransitiveTripleCounting902.lean`) builds on
`Erdos902Unified435` and `SzekeresParityRefinementAndTightenedBinomialBounds902` to establish
25 universally quantified (`∀`) structural theorems and positive/negative controls for Erdős
Problem #902 (Schütte's `n`-paradoxical tournament problem) in Lean 4.35.0-rc2:

1. **Second-, Third-, and Fourth-Order Binomial Expansions and Single-Block Decay Hierarchy:**
   - Second-order binomial expansion `second_order_binomial_nat_pow_bound`:
     `2 * a ^ (m + 2) + 2 * (m + 2) * a ^ (m + 1) + (m + 2) * (m + 1) * a ^ m ≤ 2 * (a + 1) ^ (m + 2)`,
     giving `(5 * a + 3) * a ^ a ≤ 2 * (a + 1) ^ (a + 1)` and `5 * a ^ (a + 1) < 2 * (a + 1) ^ (a + 1)`
     for all `1 ≤ a`.
   - Single-block second-order decay `five_mul_two_pow_sub_one_pow_lt_two_mul`: for all `1 ≤ n`,
     `5 * (2 ^ n - 1) ^ (2 ^ n) < 2 * (2 ^ n) ^ (2 ^ n)`.
   - Third-order (`8 * (2 ^ n - 1) ^ (2 ^ n) < 3 * (2 ^ n) ^ (2 ^ n)`,
     `7 * (2 ^ n - 1) ^ (2 * 2 ^ n) < (2 ^ n) ^ (2 * 2 ^ n)`) and fourth-order
     (`65 * (2 ^ n - 1) ^ (2 ^ n) < 24 * (2 ^ n) ^ (2 ^ n)`,
     `27 * (2 ^ n - 1) ^ (2 ^ n) < 10 * (2 ^ n) ^ (2 ^ n)`) single-block binomial decay, and the
     parametric rational-base union-bound bridge `erdosProbabilisticCriterion_of_rational_base_decay`.

2. **Reduced `O(n^2 2^n)` Leading-Coefficient Bounds, Small-`n` Falsifier, and Conditional Reduction:**
   - Unconditional proof that `legacyF n ≤ n ^ 2 * 2 ^ n` holds for all `11 ≤ n`
     (`hasParadoxicalTournament_and_f_le_sq_mul_two_pow_of_eleven_le`) and all `2 ≤ n ≤ 4`
     (`f_le_sq_mul_two_pow_small_cases`, with `legacyF 1 = 3 = 1 ^ 2 * 2 ^ 1 + 1`), so
     `legacyF n ≤ n ^ 2 * 2 ^ n + 1` holds for all `n ∈ {1, 2, 3, 4} ∪ [11, ∞)`.
   - Unconditional unit-leading-coefficient upper bound for all `1 ≤ n`
     (`hasParadoxicalTournament_and_f_le_mul_add_one_two_pow`):
     `legacyF n ≤ n * (n + 1) * 2 ^ n` and `legacyF n ≤ (n ^ 2 + 6) * 2 ^ n`, reducing the unconditional
     leading coefficient of `O(n^2 2^n)` from `2 * n ^ 2 * 2 ^ n` to `1 * n ^ 2 * 2 ^ n`.
   - Explicit negative control `not_erdosProbabilisticCriterion_sq_mul_two_pow_of_le_four`
     proving `¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)` for `1 ≤ n ≤ 4`, and conditional
     reduction `f_le_sq_mul_two_pow_add_one_of_mid_range` reducing `legacyF n ≤ n ^ 2 * 2 ^ n + 1`
     for all `1 ≤ n` (and `legacyF n ≤ n ^ 2 * 2 ^ n` for all `2 ≤ n`) to the six intermediate values
     `5 ≤ n ≤ 10`.

3. **Tournament Transitive-Triple, Cyclic-Triple, and Szekeres–Szekeres 4-Tuple Counting Identities:**
   - Exact partition of `(Finset.univ : Finset (Fin N)).powersetCard 3` into
     `transitiveTripleFinset G` and `cyclicTripleFinset G`.
   - Universal tournament degree-pair identity
     `∑ v, (outNeigh G v).card.choose 2 = ∑ v, (inNeigh G v).card.choose 2` and transitive-triple
     double-counting theorem `card_transitiveTripleFinset_eq_sum_choose_two`: in any tournament
     `G` on `Fin N`,
     `(transitiveTripleFinset G).card = ∑ v, (outNeigh G v).card.choose 2 = ∑ v, (inNeigh G v).card.choose 2 = ∑_{|S|=2} (domSet G S).card`.
   - Regular and Szekeres–Szekeres extremal evaluations (`card_transitive_and_cyclic_triples_of_regular`
     and `szekeres_extremal_triple_and_domSet_counts`).
-/

namespace Erdos902

/-- Second-order natural-number binomial expansion lower bound:
`2 * a ^ (m + 2) + 2 * (m + 2) * a ^ (m + 1) + (m + 2) * (m + 1) * a ^ m ≤ 2 * (a + 1) ^ (m + 2)`,
and for all `1 ≤ a`, `(5 * a + 3) * a ^ a ≤ 2 * (a + 1) ^ (a + 1)` and
`5 * a ^ (a + 1) < 2 * (a + 1) ^ (a + 1)`. -/
theorem second_order_binomial_nat_pow_bound (a m : ℕ) :
    2 * a ^ (m + 2) + 2 * (m + 2) * a ^ (m + 1) + (m + 2) * (m + 1) * a ^ m ≤
      2 * (a + 1) ^ (m + 2) ∧
    (1 ≤ a → (5 * a + 3) * a ^ a ≤ 2 * (a + 1) ^ (a + 1) ∧
      5 * a ^ (a + 1) < 2 * (a + 1) ^ (a + 1)) := by
  have haux : ∀ b k : ℕ,
      2 * b ^ (k + 2) + 2 * (k + 2) * b ^ (k + 1) + (k + 2) * (k + 1) * b ^ k ≤
        2 * (b + 1) ^ (k + 2) := by
    intro b k
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_zero, mul_one]
      linarith [sq (b + 1)]
    | succ k ih =>
      calc
        2 * b ^ (k + 3) + 2 * (k + 3) * b ^ (k + 2) + (k + 3) * (k + 2) * b ^ (k + 1) ≤
            (2 * b ^ (k + 2) + 2 * (k + 2) * b ^ (k + 1) + (k + 2) * (k + 1) * b ^ k) * (b + 1) := by
          have hexp : (2 * b ^ (k + 2) + 2 * (k + 2) * b ^ (k + 1) + (k + 2) * (k + 1) * b ^ k) * (b + 1) =
              2 * b ^ (k + 3) + 2 * (k + 3) * b ^ (k + 2) + (k + 3) * (k + 2) * b ^ (k + 1) +
                (k + 2) * (k + 1) * b ^ k := by ring
          omega
        _ ≤ 2 * (b + 1) ^ (k + 2) * (b + 1) := Nat.mul_le_mul_right (b + 1) ih
        _ = 2 * (b + 1) ^ (k + 3) := by ring
  refine ⟨haux a m, fun ha => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hk := haux (1 + k) k
  have h1 : k + 2 = 1 + k + 1 := by omega
  have h2 : k + 1 = 1 + k := by omega
  rw [h1, h2] at hk
  have hlhs : 2 * (1 + k) ^ (1 + k + 1) + 2 * (1 + k + 1) * (1 + k) ^ (1 + k) +
      (1 + k + 1) * (1 + k) * (1 + k) ^ k = (5 * (1 + k) + 3) * (1 + k) ^ (1 + k) := by
    have hp : (1 + k) * (1 + k) ^ k = (1 + k) ^ (1 + k) := by
      rw [← pow_succ', add_comm 1 k]
    calc
      2 * (1 + k) ^ (1 + k + 1) + 2 * (1 + k + 1) * (1 + k) ^ (1 + k) +
          (1 + k + 1) * (1 + k) * (1 + k) ^ k
          = 2 * (1 + k) ^ (1 + k + 1) + 2 * (1 + k + 1) * (1 + k) ^ (1 + k) +
              (1 + k + 1) * ((1 + k) * (1 + k) ^ k) := by ring
      _ = 2 * (1 + k) ^ (1 + k + 1) + 2 * (1 + k + 1) * (1 + k) ^ (1 + k) +
              (1 + k + 1) * (1 + k) ^ (1 + k) := by rw [hp]
      _ = (5 * (1 + k) + 3) * (1 + k) ^ (1 + k) := by ring
  rw [hlhs] at hk
  have hpos : 0 < (1 + k) ^ (1 + k) := Nat.pos_of_ne_zero (by positivity)
  have hpow_succ : 5 * (1 + k) ^ (1 + k + 1) + 3 * (1 + k) ^ (1 + k) =
      (5 * (1 + k) + 3) * (1 + k) ^ (1 + k) := by ring
  exact ⟨hk, by omega⟩

/-- Single-block (`2 ^ n` vertices) second-order binomial decay: for all `1 ≤ n`,
`5 * (2 ^ n - 1) ^ (2 ^ n) + 3 * (2 ^ n - 1) ^ (2 ^ n - 1) ≤ 2 * (2 ^ n) ^ (2 ^ n)` and
`5 * (2 ^ n - 1) ^ (2 ^ n) < 2 * (2 ^ n) ^ (2 ^ n)`. -/
theorem five_mul_two_pow_sub_one_pow_lt_two_mul (n : ℕ) (hn : 1 ≤ n) :
    5 * (2 ^ n - 1) ^ (2 ^ n) + 3 * (2 ^ n - 1) ^ (2 ^ n - 1) ≤ 2 * (2 ^ n) ^ (2 ^ n) ∧
      5 * (2 ^ n - 1) ^ (2 ^ n) < 2 * (2 ^ n) ^ (2 ^ n) := by
  have hpow2 : 2 ≤ 2 ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
    omega
  let a := 2 ^ n - 1
  have ha : 1 ≤ a := by omega
  have ha_succ : a + 1 = 2 ^ n := by omega
  have hsec := (second_order_binomial_nat_pow_bound a 0).2 ha
  have hlhs : (5 * a + 3) * a ^ a = 5 * a ^ (a + 1) + 3 * a ^ a := by ring
  rw [hlhs, ha_succ] at hsec
  exact hsec


/-- Parametric power-stepping lemma: if `1 ≤ p`, `1 ≤ t`, and `p * A < q * B`, then
`p ^ t * A ^ t < q ^ t * B ^ t`. -/
theorem pow_mul_pow_lt_of_mul_lt {p q A B t : ℕ} (ht : 1 ≤ t) (_hp : 1 ≤ p)
    (hbase : p * A < q * B) :
    p ^ t * A ^ t < q ^ t * B ^ t := by
  have hmul : (p * A) ^ t < (q * B) ^ t := Nat.pow_lt_pow_left hbase (by omega)
  rwa [mul_pow, mul_pow] at hmul



/-- Third-order (cubic) natural-number binomial expansion lower bound:
`6 * a ^ (m + 3) + 6 * (m + 3) * a ^ (m + 2) + 3 * (m + 3) * (m + 2) * a ^ (m + 1) + (m + 3) * (m + 2) * (m + 1) * a ^ m ≤ 6 * (a + 1) ^ (m + 3)`,
and for all `1 ≤ a`, `8 * a ^ (a + 1) < 3 * (a + 1) ^ (a + 1)`. -/
theorem third_order_binomial_nat_pow_bound (a m : ℕ) :
    6 * a ^ (m + 3) + 6 * (m + 3) * a ^ (m + 2) + 3 * (m + 3) * (m + 2) * a ^ (m + 1) +
        (m + 3) * (m + 2) * (m + 1) * a ^ m ≤ 6 * (a + 1) ^ (m + 3) ∧
      (1 ≤ a → 8 * a ^ (a + 1) < 3 * (a + 1) ^ (a + 1)) := by
  have haux : ∀ b k : ℕ,
      6 * b ^ (k + 3) + 6 * (k + 3) * b ^ (k + 2) + 3 * (k + 3) * (k + 2) * b ^ (k + 1) +
          (k + 3) * (k + 2) * (k + 1) * b ^ k ≤ 6 * (b + 1) ^ (k + 3) := by
    intro b k
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_zero, pow_one, mul_one]
      have hring : 6 * b ^ 3 + 6 * 3 * b ^ 2 + 3 * 3 * 2 * b + 3 * 2 * 1 = 6 * (b + 1) ^ 3 := by ring
      omega
    | succ k ih =>
      calc
        6 * b ^ (k + 4) + 6 * (k + 4) * b ^ (k + 3) + 3 * (k + 4) * (k + 3) * b ^ (k + 2) +
            (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) ≤
          (6 * b ^ (k + 3) + 6 * (k + 3) * b ^ (k + 2) + 3 * (k + 3) * (k + 2) * b ^ (k + 1) +
            (k + 3) * (k + 2) * (k + 1) * b ^ k) * (b + 1) := by
          have hexp : (6 * b ^ (k + 3) + 6 * (k + 3) * b ^ (k + 2) + 3 * (k + 3) * (k + 2) * b ^ (k + 1) +
              (k + 3) * (k + 2) * (k + 1) * b ^ k) * (b + 1) =
            6 * b ^ (k + 4) + 6 * (k + 4) * b ^ (k + 3) + 3 * (k + 4) * (k + 3) * b ^ (k + 2) +
              (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) + (k + 3) * (k + 2) * (k + 1) * b ^ k := by ring
          omega
        _ ≤ 6 * (b + 1) ^ (k + 3) * (b + 1) := Nat.mul_le_mul_right (b + 1) ih
        _ = 6 * (b + 1) ^ (k + 4) := by ring
  refine ⟨haux a m, fun ha => ?_⟩
  rcases eq_or_lt_of_le ha with rfl | hgt1
  · decide
  · obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
    have hk := haux (k + 2) k
    have hp1 : (k + 2) ^ (k + 1) = (k + 2) * (k + 2) ^ k := by rw [pow_succ']
    have hp2 : (k + 2) ^ (k + 2) = (k + 2) ^ 2 * (k + 2) ^ k := by rw [← pow_add, add_comm 2 k]
    have hp3 : (k + 2) ^ (k + 3) = (k + 2) ^ 3 * (k + 2) ^ k := by rw [← pow_add, add_comm 3 k]
    have hpos : 0 < (k + 2) ^ k := Nat.pos_of_ne_zero (by positivity)
    have hstrict : 16 * (k + 2) ^ (k + 3) <
        6 * (k + 2) ^ (k + 3) + 6 * (k + 3) * (k + 2) ^ (k + 2) +
          3 * (k + 3) * (k + 2) * (k + 2) ^ (k + 1) + (k + 3) * (k + 2) * (k + 1) * (k + 2) ^ k := by
      rw [hp1, hp2, hp3]
      have hpoly : 16 * (k + 2) ^ 3 <
          6 * (k + 2) ^ 3 + 6 * (k + 3) * (k + 2) ^ 2 + 3 * (k + 3) * (k + 2) * (k + 2) +
            (k + 3) * (k + 2) * (k + 1) := by
        have hdiff : 6 * (k + 2) ^ 3 + 6 * (k + 3) * (k + 2) ^ 2 + 3 * (k + 3) * (k + 2) * (k + 2) +
            (k + 3) * (k + 2) * (k + 1) =
            16 * (k + 2) ^ 3 + (9 * k ^ 2 + 35 * k + 34) := by ring
        omega
      have hmul := Nat.mul_lt_mul_of_pos_right hpoly hpos
      linarith
    have h16 : 16 * (k + 2) ^ (k + 3) < 6 * (k + 2 + 1) ^ (k + 3) := lt_of_lt_of_le hstrict hk
    have h3 : k + 2 + 1 = k + 3 := by omega
    rw [h3] at h16 ⊢
    omega

/-- Third-order exponential decay for `2 ^ n - 1`: for all `1 ≤ n`,
`8 * (2 ^ n - 1) ^ (2 ^ n) < 3 * (2 ^ n) ^ (2 ^ n)` and
`7 * (2 ^ n - 1) ^ (2 * 2 ^ n) < (2 ^ n) ^ (2 * 2 ^ n)`. -/
theorem eight_mul_two_pow_sub_one_pow_lt_three_mul_and_seven_double_block (n : ℕ) (hn : 1 ≤ n) :
    8 * (2 ^ n - 1) ^ (2 ^ n) < 3 * (2 ^ n) ^ (2 ^ n) ∧
      7 * (2 ^ n - 1) ^ (2 * 2 ^ n) < (2 ^ n) ^ (2 * 2 ^ n) := by
  have hpow2 : 2 ≤ 2 ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
    omega
  let a := 2 ^ n - 1
  have ha : 1 ≤ a := by omega
  have ha_succ : a + 1 = 2 ^ n := by omega
  have hlt := (third_order_binomial_nat_pow_bound a 0).2 ha
  rw [ha_succ] at hlt
  have hsq : (8 * a ^ (2 ^ n)) * (8 * a ^ (2 ^ n)) <
      (3 * (2 ^ n) ^ (2 ^ n)) * (3 * (2 ^ n) ^ (2 ^ n)) :=
    Nat.mul_lt_mul'' hlt hlt
  have hlhs : (8 * a ^ (2 ^ n)) * (8 * a ^ (2 ^ n)) = 64 * a ^ (2 * 2 ^ n) := by
    have hexp : 2 * 2 ^ n = 2 ^ n + 2 ^ n := by ring
    rw [hexp, pow_add]
    ring
  have hrhs : (3 * (2 ^ n) ^ (2 ^ n)) * (3 * (2 ^ n) ^ (2 ^ n)) = 9 * (2 ^ n) ^ (2 * 2 ^ n) := by
    have hexp : 2 * 2 ^ n = 2 ^ n + 2 ^ n := by ring
    rw [hexp, pow_add]
    ring
  rw [hlhs, hrhs] at hsq
  dsimp [a] at hsq
  exact ⟨hlt, by omega⟩


/-- Fourth-order (quartic) natural-number binomial expansion lower bound:
`24 * a ^ (m + 4) + 24 * (m + 4) * a ^ (m + 3) + 12 * (m + 4) * (m + 3) * a ^ (m + 2) + 4 * (m + 4) * (m + 3) * (m + 2) * a ^ (m + 1) + (m + 4) * (m + 3) * (m + 2) * (m + 1) * a ^ m ≤ 24 * (a + 1) ^ (m + 4)`,
and for all `1 ≤ a`, `65 * a ^ (a + 1) < 24 * (a + 1) ^ (a + 1)` and
`27 * a ^ (a + 1) < 10 * (a + 1) ^ (a + 1)`. -/
theorem fourth_order_binomial_nat_pow_bound (a m : ℕ) :
    24 * a ^ (m + 4) + 24 * (m + 4) * a ^ (m + 3) + 12 * (m + 4) * (m + 3) * a ^ (m + 2) +
        4 * (m + 4) * (m + 3) * (m + 2) * a ^ (m + 1) +
        (m + 4) * (m + 3) * (m + 2) * (m + 1) * a ^ m ≤ 24 * (a + 1) ^ (m + 4) ∧
      (1 ≤ a → 65 * a ^ (a + 1) < 24 * (a + 1) ^ (a + 1) ∧
        27 * a ^ (a + 1) < 10 * (a + 1) ^ (a + 1)) := by
  have haux : ∀ b k : ℕ,
      24 * b ^ (k + 4) + 24 * (k + 4) * b ^ (k + 3) + 12 * (k + 4) * (k + 3) * b ^ (k + 2) +
          4 * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) +
          (k + 4) * (k + 3) * (k + 2) * (k + 1) * b ^ k ≤ 24 * (b + 1) ^ (k + 4) := by
    intro b k
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_zero, pow_one, mul_one]
      have hring : 24 * b ^ 4 + 24 * 4 * b ^ 3 + 12 * 4 * 3 * b ^ 2 +
          4 * 4 * 3 * 2 * b + 4 * 3 * 2 * 1 = 24 * (b + 1) ^ 4 := by ring
      omega
    | succ k ih =>
      calc
        24 * b ^ (k + 5) + 24 * (k + 5) * b ^ (k + 4) + 12 * (k + 5) * (k + 4) * b ^ (k + 3) +
            4 * (k + 5) * (k + 4) * (k + 3) * b ^ (k + 2) +
            (k + 5) * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) ≤
          (24 * b ^ (k + 4) + 24 * (k + 4) * b ^ (k + 3) + 12 * (k + 4) * (k + 3) * b ^ (k + 2) +
            4 * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) +
            (k + 4) * (k + 3) * (k + 2) * (k + 1) * b ^ k) * (b + 1) := by
          have hexp : (24 * b ^ (k + 4) + 24 * (k + 4) * b ^ (k + 3) +
              12 * (k + 4) * (k + 3) * b ^ (k + 2) +
              4 * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) +
              (k + 4) * (k + 3) * (k + 2) * (k + 1) * b ^ k) * (b + 1) =
            24 * b ^ (k + 5) + 24 * (k + 5) * b ^ (k + 4) + 12 * (k + 5) * (k + 4) * b ^ (k + 3) +
              4 * (k + 5) * (k + 4) * (k + 3) * b ^ (k + 2) +
              (k + 5) * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) +
              (k + 4) * (k + 3) * (k + 2) * (k + 1) * b ^ k := by ring
          omega
        _ ≤ 24 * (b + 1) ^ (k + 4) * (b + 1) := Nat.mul_le_mul_right (b + 1) ih
        _ = 24 * (b + 1) ^ (k + 5) := by ring
  refine ⟨haux a m, fun ha => ?_⟩
  by_cases ha3 : 3 ≤ a
  · obtain ⟨k, rfl⟩ : ∃ k, a = k + 3 := ⟨a - 3, by omega⟩
    have hk := haux (k + 3) k
    have hp1 : (k + 3) ^ (k + 1) = (k + 3) * (k + 3) ^ k := by rw [pow_succ']
    have hp2 : (k + 3) ^ (k + 2) = (k + 3) ^ 2 * (k + 3) ^ k := by rw [← pow_add, add_comm 2 k]
    have hp3 : (k + 3) ^ (k + 3) = (k + 3) ^ 3 * (k + 3) ^ k := by rw [← pow_add, add_comm 3 k]
    have hp4 : (k + 3) ^ (k + 4) = (k + 3) ^ 4 * (k + 3) ^ k := by rw [← pow_add, add_comm 4 k]
    have hpos : 0 < (k + 3) ^ k := Nat.pos_of_ne_zero (by positivity)
    have hstrict : 65 * (k + 3) ^ (k + 4) <
        24 * (k + 3) ^ (k + 4) + 24 * (k + 4) * (k + 3) ^ (k + 3) +
          12 * (k + 4) * (k + 3) * (k + 3) ^ (k + 2) +
          4 * (k + 4) * (k + 3) * (k + 2) * (k + 3) ^ (k + 1) +
          (k + 4) * (k + 3) * (k + 2) * (k + 1) * (k + 3) ^ k := by
      rw [hp1, hp2, hp3, hp4]
      have hpoly : 65 * (k + 3) ^ 4 <
          24 * (k + 3) ^ 4 + 24 * (k + 4) * (k + 3) ^ 3 + 12 * (k + 4) * (k + 3) * (k + 3) ^ 2 +
            4 * (k + 4) * (k + 3) * (k + 2) * (k + 3) +
            (k + 4) * (k + 3) * (k + 2) * (k + 1) := by
        have hdiff : 24 * (k + 3) ^ 4 + 24 * (k + 4) * (k + 3) ^ 3 +
            12 * (k + 4) * (k + 3) * (k + 3) ^ 2 +
            4 * (k + 4) * (k + 3) * (k + 2) * (k + 3) +
            (k + 4) * (k + 3) * (k + 2) * (k + 1) =
            65 * (k + 3) ^ 4 + (34 * k ^ 3 + 301 * k ^ 2 + 890 * k + 879) := by ring
        omega
      have hmul := Nat.mul_lt_mul_of_pos_right hpoly hpos
      linarith
    have h65 : 65 * (k + 3) ^ (k + 4) < 24 * (k + 3 + 1) ^ (k + 4) := lt_of_lt_of_le hstrict hk
    have h4 : k + 3 + 1 = k + 4 := by omega
    rw [h4] at h65 ⊢
    exact ⟨h65, by omega⟩
  · interval_cases a <;> decide

/-- Single-block fourth-order binomial decay: for all `1 ≤ n`,
`65 * (2 ^ n - 1) ^ (2 ^ n) < 24 * (2 ^ n) ^ (2 ^ n)` and
`27 * (2 ^ n - 1) ^ (2 ^ n) < 10 * (2 ^ n) ^ (2 ^ n)`. -/
theorem twenty_seven_mul_two_pow_sub_one_pow_lt_ten_mul (n : ℕ) (hn : 1 ≤ n) :
    65 * (2 ^ n - 1) ^ (2 ^ n) < 24 * (2 ^ n) ^ (2 ^ n) ∧
      27 * (2 ^ n - 1) ^ (2 ^ n) < 10 * (2 ^ n) ^ (2 ^ n) := by
  have hpow2 : 2 ≤ 2 ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
    omega
  have h := (fourth_order_binomial_nat_pow_bound (2 ^ n - 1) 0).2 (by omega)
  have hsucc : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  rwa [hsucc] at h


/-- Parametric rational-base union-bound bridge: if `p * (2 ^ n - 1) ^ (2 ^ n) < q * (2 ^ n) ^ (2 ^ n)`
and `q ^ t * (n + t * 2 ^ n).choose n ≤ p ^ t` (or `q ^ t * (n + t * 2 ^ n) ^ n ≤ n.factorial * p ^ t`),
then `ErdosProbabilisticCriterion n (n + t * 2 ^ n)` holds. -/
theorem erdosProbabilisticCriterion_of_rational_base_decay {n t p q : ℕ}
    (ht : 1 ≤ t) (hp : 1 ≤ p)
    (hbase : p * (2 ^ n - 1) ^ (2 ^ n) < q * (2 ^ n) ^ (2 ^ n)) :
    (q ^ t * (n + t * 2 ^ n).choose n ≤ p ^ t →
      ErdosProbabilisticCriterion n (n + t * 2 ^ n)) ∧
    (q ^ t * (n + t * 2 ^ n) ^ n ≤ n.factorial * p ^ t →
      ErdosProbabilisticCriterion n (n + t * 2 ^ n)) := by
  have hstep := pow_mul_pow_lt_of_mul_lt ht hp hbase
  rw [← pow_mul, ← pow_mul, mul_comm (2 ^ n) t] at hstep
  have h1 : q ^ t * (n + t * 2 ^ n).choose n ≤ p ^ t →
      ErdosProbabilisticCriterion n (n + t * 2 ^ n) := by
    intro hchoose
    dsimp [ErdosProbabilisticCriterion]
    rw [Nat.add_sub_cancel_left]
    have hscaled : q ^ t * ((n + t * 2 ^ n).choose n * (2 ^ n - 1) ^ (t * 2 ^ n)) <
        q ^ t * (2 ^ n) ^ (t * 2 ^ n) := by
      calc
        q ^ t * ((n + t * 2 ^ n).choose n * (2 ^ n - 1) ^ (t * 2 ^ n))
            = (q ^ t * (n + t * 2 ^ n).choose n) * (2 ^ n - 1) ^ (t * 2 ^ n) := by ring
        _ ≤ p ^ t * (2 ^ n - 1) ^ (t * 2 ^ n) := Nat.mul_le_mul_right _ hchoose
        _ < q ^ t * (2 ^ n) ^ (t * 2 ^ n) := hstep
    exact lt_of_mul_lt_mul_left hscaled (Nat.zero_le _)
  refine ⟨h1, fun hpow => h1 ?_⟩
  have hfact : n.factorial * (n + t * 2 ^ n).choose n ≤ (n + t * 2 ^ n) ^ n := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ n
  have hscaled_fact : n.factorial * (q ^ t * (n + t * 2 ^ n).choose n) ≤
      n.factorial * p ^ t := by
    calc
      n.factorial * (q ^ t * (n + t * 2 ^ n).choose n)
          = q ^ t * (n.factorial * (n + t * 2 ^ n).choose n) := by ring
      _ ≤ q ^ t * (n + t * 2 ^ n) ^ n := Nat.mul_le_mul_left _ hfact
      _ ≤ n.factorial * p ^ t := hpow
  exact Nat.le_of_mul_le_mul_left hscaled_fact (Nat.factorial_pos n)


/-- For all `17 ≤ n`, `3 ^ (n - 1) * (3 + 3 * (n - 1) * 2 ^ n) ≤ 8 ^ (n - 1)`. -/
theorem three_pow_mul_three_add_mul_sub_one_two_pow_le_eight_pow_of_seventeen_le
    {n : ℕ} (hn : 17 ≤ n) :
    3 ^ (n - 1) * (3 + 3 * (n - 1) * 2 ^ n) ≤ 8 ^ (n - 1) := by
  have haux : ∀ k : ℕ, 16 ≤ k → 3 ^ k * (6 * k + 1) ≤ 4 ^ k := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    clear hk
    induction m with
    | zero => decide
    | succ m ih =>
      have h1 : 16 + (m + 1) = (16 + m) + 1 := by omega
      rw [h1, pow_succ, pow_succ]
      have hlin : 3 * (6 * (16 + m + 1) + 1) ≤ 4 * (6 * (16 + m) + 1) := by omega
      have hstep : 3 ^ (16 + m) * 3 * (6 * (16 + m + 1) + 1) ≤
          3 ^ (16 + m) * (4 * (6 * (16 + m) + 1)) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ hlin
      have hstep2 : 3 ^ (16 + m) * (4 * (6 * (16 + m) + 1)) =
          (3 ^ (16 + m) * (6 * (16 + m) + 1)) * 4 := by
        rw [← mul_assoc, mul_comm (3 ^ (16 + m)) 4, mul_assoc, mul_comm 4]
      rw [hstep2] at hstep
      exact le_trans hstep (Nat.mul_le_mul_right 4 ih)
  have h16 : 16 ≤ n - 1 := by omega
  have hm := haux (n - 1) h16
  have hn_eq : n = (n - 1) + 1 := by omega
  have hpow3 : 3 ≤ 2 ^ (n - 1) := by
    calc 3 ≤ 2 ^ 2 := by decide
    _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    nth_rw 1 [hn_eq]
    rw [pow_succ']
  have hinner : 3 + 3 * (n - 1) * 2 ^ n ≤ (6 * (n - 1) + 1) * 2 ^ (n - 1) := by
    rw [h2n]
    nlinarith
  have h8 : 8 ^ (n - 1) = 4 ^ (n - 1) * 2 ^ (n - 1) := by
    have h842 : (8 : ℕ) = 4 * 2 := rfl
    rw [h842, mul_pow]
  rw [h8]
  calc
    3 ^ (n - 1) * (3 + 3 * (n - 1) * 2 ^ n)
        ≤ 3 ^ (n - 1) * ((6 * (n - 1) + 1) * 2 ^ (n - 1)) := Nat.mul_le_mul_left _ hinner
    _ = (3 ^ (n - 1) * (6 * (n - 1) + 1)) * 2 ^ (n - 1) := (mul_assoc _ _ _).symm
    _ ≤ 4 ^ (n - 1) * 2 ^ (n - 1) := Nat.mul_le_mul_right _ hm

/-- Explicit sub-`n^2 2^n` vertex formula `N_near(n) = n + n * (n - 1) * 2 ^ n ≤ n ^ 2 * 2 ^ n`. -/
def NearUnitErdosUpperBoundFormula (n : ℕ) : ℕ :=
  n + n * (n - 1) * 2 ^ n



/-- For all `17 ≤ n`, `NearUnitErdosUpperBoundFormula n = n + n * (n - 1) * 2 ^ n` satisfies
`ErdosProbabilisticCriterion n (NearUnitErdosUpperBoundFormula n)` and
`NearUnitErdosUpperBoundFormula n ≤ n ^ 2 * 2 ^ n`. -/
theorem nearUnitErdosUpperBoundFormula_criterion_of_seventeen_le {n : ℕ} (hn : 17 ≤ n) :
    ErdosProbabilisticCriterion n (NearUnitErdosUpperBoundFormula n) ∧
      NearUnitErdosUpperBoundFormula n ≤ n ^ 2 * 2 ^ n := by
  let N := NearUnitErdosUpperBoundFormula n
  let t := n * (n - 1)
  have hn1 : 1 ≤ n := by omega
  have ht : 1 ≤ t := by
    dsimp [t]
    exact Nat.mul_pos hn1 (by omega)
  have hdiv : (3 * N) / n = 3 + 3 * (n - 1) * 2 ^ n := by
    have h3N : 3 * N = n * (3 + 3 * (n - 1) * 2 ^ n) := by
      dsimp [N, NearUnitErdosUpperBoundFormula]
      ring
    rw [h3N, Nat.mul_div_right _ (by omega : 0 < n)]
  have hstep8 := three_pow_mul_three_add_mul_sub_one_two_pow_le_eight_pow_of_seventeen_le hn
  have hchoose : 3 ^ t * N.choose n ≤ 8 ^ t := by
    calc
      3 ^ t * N.choose n ≤ 3 ^ t * ((3 * N) / n) ^ n :=
        Nat.mul_le_mul_left _ (choose_le_three_mul_div_pow N n)
      _ = (3 ^ (n - 1)) ^ n * (3 + 3 * (n - 1) * 2 ^ n) ^ n := by
        rw [hdiv, ← pow_mul, mul_comm (n - 1) n]
      _ = (3 ^ (n - 1) * (3 + 3 * (n - 1) * 2 ^ n)) ^ n := (mul_pow _ _ n).symm
      _ ≤ (8 ^ (n - 1)) ^ n := Nat.pow_le_pow_left hstep8 n
      _ = 8 ^ t := by
        rw [← pow_mul, mul_comm (n - 1) n]
  have hbase := (eight_mul_two_pow_sub_one_pow_lt_three_mul_and_seven_double_block n hn1).1
  have hcrit := (erdosProbabilisticCriterion_of_rational_base_decay ht (by decide) hbase).1 hchoose
  refine ⟨hcrit, ?_⟩
  dsimp [NearUnitErdosUpperBoundFormula]
  have hpow_ge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hsplit : n * (n - 1) + n = n ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn1
    simp only [Nat.add_sub_cancel_left]
    ring
  calc
    n + n * (n - 1) * 2 ^ n ≤ n * 2 ^ n + n * (n - 1) * 2 ^ n :=
      Nat.add_le_add_right (Nat.le_mul_of_pos_right n hpow_ge) _
    _ = (n * (n - 1) + n) * 2 ^ n := by ring
    _ = n ^ 2 * 2 ^ n := by rw [hsplit]

/-- For all `11 ≤ n`, `HasParadoxicalTournament n (n ^ 2 * 2 ^ n)` holds and
`legacyF n ≤ n ^ 2 * 2 ^ n` (and `legacyF n ≤ n ^ 2 * 2 ^ n + 1`). -/
theorem hasParadoxicalTournament_and_f_le_sq_mul_two_pow_of_eleven_le {n : ℕ} (hn : 11 ≤ n) :
    HasParadoxicalTournament n (n ^ 2 * 2 ^ n) ∧
      legacyF n ≤ n ^ 2 * 2 ^ n ∧
      legacyF n ≤ n ^ 2 * 2 ^ n + 1 := by
  have hex : HasParadoxicalTournament n (n ^ 2 * 2 ^ n) := by
    by_cases hn17 : 17 ≤ n
    · have h17 := nearUnitErdosUpperBoundFormula_criterion_of_seventeen_le hn17
      have hnN : n ≤ NearUnitErdosUpperBoundFormula n := by
        dsimp [NearUnitErdosUpperBoundFormula]
        omega
      have hpar := (hasParadoxicalTournament_of_erdosProbabilisticCriterion hnN h17.1).2
      exact hasParadoxicalTournament_mono_N h17.2 hpar
    · have ht : 1 ≤ n ^ 2 - 1 := by
        have : 11 * 11 ≤ n * n := Nat.mul_le_mul hn hn
        rw [sq]
        omega
      have hnN : n ≤ n + (n ^ 2 - 1) * 2 ^ n := by omega
      have hle_sq : n + (n ^ 2 - 1) * 2 ^ n ≤ n ^ 2 * 2 ^ n := by
        clear ht hnN
        interval_cases n <;> decide
      have hbase := (twenty_seven_mul_two_pow_sub_one_pow_lt_ten_mul n (by omega)).2
      have hpow_le : 10 ^ (n ^ 2 - 1) * (n + (n ^ 2 - 1) * 2 ^ n) ^ n ≤
          n.factorial * 27 ^ (n ^ 2 - 1) := by
        clear ht hnN hle_sq hbase
        interval_cases n <;> decide
      have hcrit := (erdosProbabilisticCriterion_of_rational_base_decay ht (by decide) hbase).2 hpow_le
      have hpar := (hasParadoxicalTournament_of_erdosProbabilisticCriterion hnN hcrit).2
      exact hasParadoxicalTournament_mono_N hle_sq hpar
  have hle : legacyF n ≤ n ^ 2 * 2 ^ n := legacyF_le_of_hasParadoxicalTournament hex
  exact ⟨hex, hle, by omega⟩


/-- Exact small-case evaluation for `1 ≤ n ≤ 4`: `legacyF n ≤ n ^ 2 * 2 ^ n + 1`, `legacyF 1 = 1 ^ 2 * 2 ^ 1 + 1`,
and for `2 ≤ n ≤ 4`, `legacyF n ≤ n ^ 2 * 2 ^ n`. -/
theorem f_le_sq_mul_two_pow_small_cases {n : ℕ} (hn1 : 1 ≤ n) (hn4 : n ≤ 4) :
    legacyF n ≤ n ^ 2 * 2 ^ n + 1 ∧ (2 ≤ n → legacyF n ≤ n ^ 2 * 2 ^ n) := by
  interval_cases n
  · rw [(hasParadoxicalTournament_one_iff_and_f_one 1).2]
    exact ⟨by decide, fun h => by omega⟩
  · rw [(paley7Digraph_dom2_and_f_two 2).2]
    exact ⟨by decide, fun _ => by decide⟩
  · rw [(hasParadoxicalTournament_three_iff_and_f_three 3).2]
    exact ⟨by decide, fun _ => by decide⟩
  · have h4 := hasParadoxicalTournament_four_67_and_f_four_bounds.2.2
    exact ⟨by omega, fun _ => by omega⟩

/-- Unconditional unit-leading-coefficient upper bound for all `1 ≤ n`:
`HasParadoxicalTournament n (n * (n + 1) * 2 ^ n)`, `legacyF n ≤ n * (n + 1) * 2 ^ n`, and
`legacyF n ≤ (n ^ 2 + 6) * 2 ^ n` (reducing the unconditional `O(n^2 2^n)` leading coefficient from
`2 * n ^ 2 * 2 ^ n` to `1 * n ^ 2 * 2 ^ n`). -/
theorem hasParadoxicalTournament_and_f_le_mul_add_one_two_pow (n : ℕ) (hn : 1 ≤ n) :
    HasParadoxicalTournament n (n * (n + 1) * 2 ^ n) ∧
      legacyF n ≤ n * (n + 1) * 2 ^ n ∧
      legacyF n ≤ (n ^ 2 + 6) * 2 ^ n := by
  by_cases hn11 : 11 ≤ n
  · have h11 := hasParadoxicalTournament_and_f_le_sq_mul_two_pow_of_eleven_le hn11
    have hle1 : n ^ 2 * 2 ^ n ≤ n * (n + 1) * 2 ^ n :=
      Nat.mul_le_mul_right (2 ^ n) (by nlinarith)
    have hle2 : n ^ 2 * 2 ^ n ≤ (n ^ 2 + 6) * 2 ^ n :=
      Nat.mul_le_mul_right (2 ^ n) (by omega)
    exact ⟨hasParadoxicalTournament_mono_N hle1 h11.1, le_trans h11.2.1 hle1, le_trans h11.2.1 hle2⟩
  · interval_cases n
    · have hex : HasParadoxicalTournament 1 3 := ⟨paley3Digraph, isParadoxicalTournament_paley3Digraph⟩
      have hle : legacyF 1 ≤ 3 := legacyF_le_of_hasParadoxicalTournament hex
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex, le_trans hle (by decide), le_trans hle (by decide)⟩
    · have hex : HasParadoxicalTournament 2 7 := (paley7Digraph_dom2_and_f_two 7).1.mpr (by decide)
      have hle : legacyF 2 ≤ 7 := legacyF_le_of_hasParadoxicalTournament hex
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex, le_trans hle (by decide), le_trans hle (by decide)⟩
    · have hex : HasParadoxicalTournament 3 19 :=
        (hasParadoxicalTournament_three_iff_and_f_three 19).1.mpr (by decide)
      have hle : legacyF 3 ≤ 19 := legacyF_le_of_hasParadoxicalTournament hex
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex, le_trans hle (by decide), le_trans hle (by decide)⟩
    · have hex : HasParadoxicalTournament 4 67 := hasParadoxicalTournament_four_67_and_f_four_bounds.1
      have hle : legacyF 4 ≤ 67 := legacyF_le_of_hasParadoxicalTournament hex
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex, le_trans hle (by decide), le_trans hle (by decide)⟩
    · have hbase5 : 69 * (2 ^ 5 - 1) ^ (2 ^ 5) < 25 * (2 ^ 5) ^ (2 ^ 5) := by decide
      have hpow5 : 25 ^ 29 * (5 + 29 * 2 ^ 5) ^ 5 ≤ (5 : ℕ).factorial * 69 ^ 29 := by decide
      have hcrit5 := (erdosProbabilisticCriterion_of_rational_base_decay (by decide : 1 ≤ 29)
        (by decide : 1 ≤ 69) hbase5).2 hpow5
      have hex5 := (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide : 5 ≤ 5 + 29 * 2 ^ 5) hcrit5).2
      have hle5 : legacyF 5 ≤ 5 + 29 * 2 ^ 5 := legacyF_le_of_hasParadoxicalTournament hex5
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex5, le_trans hle5 (by decide), le_trans hle5 (by decide)⟩
    · have hpow6 : 10 ^ 41 * (6 + 41 * 2 ^ 6) ^ 6 ≤ (6 : ℕ).factorial * 27 ^ 41 := by decide
      have hcrit6 := (erdosProbabilisticCriterion_of_rational_base_decay (by decide : 1 ≤ 41)
        (by decide : 1 ≤ 27) (twenty_seven_mul_two_pow_sub_one_pow_lt_ten_mul 6 (by decide)).2).2 hpow6
      have hex6 := (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide : 6 ≤ 6 + 41 * 2 ^ 6) hcrit6).2
      have hle6 : legacyF 6 ≤ 6 + 41 * 2 ^ 6 := legacyF_le_of_hasParadoxicalTournament hex6
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex6, le_trans hle6 (by decide), le_trans hle6 (by decide)⟩
    · have hpow7 : 10 ^ 54 * (7 + 54 * 2 ^ 7) ^ 7 ≤ (7 : ℕ).factorial * 27 ^ 54 := by decide
      have hcrit7 := (erdosProbabilisticCriterion_of_rational_base_decay (by decide : 1 ≤ 54)
        (by decide : 1 ≤ 27) (twenty_seven_mul_two_pow_sub_one_pow_lt_ten_mul 7 (by decide)).2).2 hpow7
      have hex7 := (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide : 7 ≤ 7 + 54 * 2 ^ 7) hcrit7).2
      have hle7 : legacyF 7 ≤ 7 + 54 * 2 ^ 7 := legacyF_le_of_hasParadoxicalTournament hex7
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex7, le_trans hle7 (by decide), le_trans hle7 (by decide)⟩
    · have hpow8 : 10 ^ 68 * (8 + 68 * 2 ^ 8) ^ 8 ≤ (8 : ℕ).factorial * 27 ^ 68 := by decide
      have hcrit8 := (erdosProbabilisticCriterion_of_rational_base_decay (by decide : 1 ≤ 68)
        (by decide : 1 ≤ 27) (twenty_seven_mul_two_pow_sub_one_pow_lt_ten_mul 8 (by decide)).2).2 hpow8
      have hex8 := (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide : 8 ≤ 8 + 68 * 2 ^ 8) hcrit8).2
      have hle8 : legacyF 8 ≤ 8 + 68 * 2 ^ 8 := legacyF_le_of_hasParadoxicalTournament hex8
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex8, le_trans hle8 (by decide), le_trans hle8 (by decide)⟩
    · have hpow9 : 10 ^ 84 * (9 + 84 * 2 ^ 9) ^ 9 ≤ (9 : ℕ).factorial * 27 ^ 84 := by decide
      have hcrit9 := (erdosProbabilisticCriterion_of_rational_base_decay (by decide : 1 ≤ 84)
        (by decide : 1 ≤ 27) (twenty_seven_mul_two_pow_sub_one_pow_lt_ten_mul 9 (by decide)).2).2 hpow9
      have hex9 := (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide : 9 ≤ 9 + 84 * 2 ^ 9) hcrit9).2
      have hle9 : legacyF 9 ≤ 9 + 84 * 2 ^ 9 := legacyF_le_of_hasParadoxicalTournament hex9
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex9, le_trans hle9 (by decide), le_trans hle9 (by decide)⟩
    · have hpow10 : 10 ^ 102 * (10 + 102 * 2 ^ 10) ^ 10 ≤ (10 : ℕ).factorial * 27 ^ 102 := by decide
      have hcrit10 := (erdosProbabilisticCriterion_of_rational_base_decay (by decide : 1 ≤ 102)
        (by decide : 1 ≤ 27) (twenty_seven_mul_two_pow_sub_one_pow_lt_ten_mul 10 (by decide)).2).2 hpow10
      have hex10 := (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide : 10 ≤ 10 + 102 * 2 ^ 10) hcrit10).2
      have hle10 : legacyF 10 ≤ 10 + 102 * 2 ^ 10 := legacyF_le_of_hasParadoxicalTournament hex10
      exact ⟨hasParadoxicalTournament_mono_N (by decide) hex10, le_trans hle10 (by decide), le_trans hle10 (by decide)⟩

/-- Negative control (small-`n` union-bound falsifier): for `1 ≤ n ≤ 4`,
`¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)`, showing that Erdős's first-moment union bound
at `N = n ^ 2 * 2 ^ n` fails for small `n` (even though `legacyF n ≤ n ^ 2 * 2 ^ n` holds for `n = 2, 3, 4`
via explicit Paley tournaments). -/
theorem not_erdosProbabilisticCriterion_sq_mul_two_pow_of_le_four {n : ℕ}
    (hn1 : 1 ≤ n) (hn4 : n ≤ 4) :
    ¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n) := by
  dsimp [ErdosProbabilisticCriterion]
  rw [not_lt]
  have hle : n.factorial * (2 ^ n) ^ (n ^ 2 * 2 ^ n - n) ≤
      (n ^ 2 * 2 ^ n).descFactorial n * (2 ^ n - 1) ^ (n ^ 2 * 2 ^ n - n) := by
    interval_cases n <;> decide
  rw [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc] at hle
  exact Nat.le_of_mul_le_mul_left hle (Nat.factorial_pos n)

/-- Conditional reduction of `legacyF n ≤ n ^ 2 * 2 ^ n + 1` (for all `1 ≤ n`) and `legacyF n ≤ n ^ 2 * 2 ^ n`
(for all `2 ≤ n`) to the six intermediate values `n ∈ {5, 6, 7, 8, 9, 10}`. -/
theorem f_le_sq_mul_two_pow_add_one_of_mid_range
    (hmid : ∀ n : ℕ, 5 ≤ n → n ≤ 10 → HasParadoxicalTournament n (n ^ 2 * 2 ^ n)) :
    (∀ n : ℕ, 1 ≤ n → legacyF n ≤ n ^ 2 * 2 ^ n + 1) ∧
      (∀ n : ℕ, 2 ≤ n → legacyF n ≤ n ^ 2 * 2 ^ n) := by
  have h2 : ∀ n : ℕ, 2 ≤ n → legacyF n ≤ n ^ 2 * 2 ^ n := by
    intro n hn2
    by_cases hn4 : n ≤ 4
    · exact (f_le_sq_mul_two_pow_small_cases (by omega) hn4).2 hn2
    · by_cases hn10 : n ≤ 10
      · exact legacyF_le_of_hasParadoxicalTournament (hmid n (by omega) hn10)
      · exact (hasParadoxicalTournament_and_f_le_sq_mul_two_pow_of_eleven_le (by omega)).2.1
  refine ⟨fun n hn1 => ?_, h2⟩
  rcases eq_or_lt_of_le hn1 with rfl | hgt1
  · exact (f_le_sq_mul_two_pow_small_cases (by decide) (by decide)).1
  · have h := h2 n (by omega)
    omega

/-- Finset of transitive 3-element subsets `T ⊆ Fin N` in a digraph `G` (those 3-subsets that
contain a source vertex `v ∈ T` dominating `T.erase v`). -/
def transitiveTripleFinset {N : ℕ} (G : Digraph (Fin N)) : Finset (Finset (Fin N)) :=
  ((Finset.univ : Finset (Fin N)).powersetCard 3).filter
    (fun T => ∃ v ∈ T, Dominates G v (T.erase v))

/-- Finset of cyclic 3-element subsets `T ⊆ Fin N` in a digraph `G` (those 3-subsets in which
no vertex `v ∈ T` dominates `T.erase v`). -/
def cyclicTripleFinset {N : ℕ} (G : Digraph (Fin N)) : Finset (Finset (Fin N)) :=
  ((Finset.univ : Finset (Fin N)).powersetCard 3).filter
    (fun T => ∀ v ∈ T, ¬ Dominates G v (T.erase v))

/-- Exact partition of all `N.choose 3` 3-element subsets of `Fin N` into
`transitiveTripleFinset G` and `cyclicTripleFinset G`. -/
theorem transitiveTripleFinset_disjoint_and_union {N : ℕ} (G : Digraph (Fin N)) :
    Disjoint (transitiveTripleFinset G) (cyclicTripleFinset G) ∧
      transitiveTripleFinset G ∪ cyclicTripleFinset G =
        (Finset.univ : Finset (Fin N)).powersetCard 3 ∧
      (transitiveTripleFinset G).card + (cyclicTripleFinset G).card = N.choose 3 := by
  have hdisj : Disjoint (transitiveTripleFinset G) (cyclicTripleFinset G) := by
    rw [Finset.disjoint_left]
    intro T h1 h2
    rw [transitiveTripleFinset, Finset.mem_filter] at h1
    rw [cyclicTripleFinset, Finset.mem_filter] at h2
    rcases h1.2 with ⟨v, hv, hdom⟩
    exact h2.2 v hv hdom
  have hunion : transitiveTripleFinset G ∪ cyclicTripleFinset G =
      (Finset.univ : Finset (Fin N)).powersetCard 3 := by
    ext T
    rw [Finset.mem_union, transitiveTripleFinset, cyclicTripleFinset,
      Finset.mem_filter, Finset.mem_filter]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with ⟨hT, _⟩ | ⟨hT, _⟩ <;> exact hT
    · by_cases hex : ∃ v ∈ T, Dominates G v (T.erase v)
      · exact Or.inl ⟨h, hex⟩
      · simp only [not_exists, not_and] at hex
        exact Or.inr ⟨h, hex⟩
  have hcard : (transitiveTripleFinset G).card + (cyclicTripleFinset G).card = N.choose 3 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact ⟨hdisj, hunion, hcard⟩

/-- Subtraction-free binomial square identity: `2 * k.choose 2 + k = k ^ 2` for all `k : ℕ`. -/
theorem two_mul_choose_two_add_self : ∀ k : ℕ, 2 * k.choose 2 + k = k ^ 2
  | 0 => by decide
  | k + 1 => by
    have ih := two_mul_choose_two_add_self k
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

/-- Complementary-degree binomial identity: if `a + b = M`, then
`2 * a.choose 2 + a + M * b = 2 * b.choose 2 + b + M * a`. -/
theorem two_mul_choose_two_eq_of_add_eq {a b M : ℕ} (h : a + b = M) :
    2 * a.choose 2 + a + M * b = 2 * b.choose 2 + b + M * a := by
  have ha := two_mul_choose_two_add_self a
  have hb := two_mul_choose_two_add_self b
  nlinarith

/-- In any tournament `G` on `Fin N`, the sum of `(outNeigh G v).card.choose 2` over all vertices
equals the sum of `(inNeigh G v).card.choose 2` over all vertices, which also equals the sum of
`(domSet G S).card` over all `2`-element subsets `S`. -/
theorem sum_choose_two_outNeigh_eq_sum_choose_two_inNeigh {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) :
    (∑ v : Fin N, (outNeigh G v).card.choose 2) =
      ∑ v : Fin N, (inNeigh G v).card.choose 2 ∧
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, (domSet G S).card) =
      ∑ v : Fin N, (inNeigh G v).card.choose 2 := by
  have hterm : ∀ v : Fin N,
      2 * (outNeigh G v).card.choose 2 + (outNeigh G v).card + (N - 1) * (inNeigh G v).card =
      2 * (inNeigh G v).card.choose 2 + (inNeigh G v).card + (N - 1) * (outNeigh G v).card :=
    fun v => two_mul_choose_two_eq_of_add_eq (card_outNeigh_add_card_inNeigh hG v)
  have hsum := Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => hterm v)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [sum_card_outNeigh_eq_sum_card_inNeigh G] at hsum
  have heq : (∑ v : Fin N, (outNeigh G v).card.choose 2) =
      ∑ v : Fin N, (inNeigh G v).card.choose 2 := by omega
  exact ⟨heq, by rw [sum_card_domSet_eq_sum_choose_outNeigh G 2, heq]⟩

/-- Uniqueness of the source vertex in a subset `T` of a tournament `G`: if `v, w ∈ T` both
dominate `T.erase v` and `T.erase w` respectively, then `v = w`. -/
theorem unique_source_of_dominates_erase {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) {T : Finset (Fin N)} {v w : Fin N}
    (hv : v ∈ T) (hw : w ∈ T)
    (hdom_v : Dominates G v (T.erase v)) (hdom_w : Dominates G w (T.erase w)) :
    v = w := by
  by_contra hne
  have hw_er : w ∈ T.erase v := Finset.mem_erase.mpr ⟨Ne.symm hne, hw⟩
  have hv_er : v ∈ T.erase w := Finset.mem_erase.mpr ⟨hne, hv⟩
  exact (hG.2 v w hne).mp (hdom_v w hw_er) (hdom_w v hv_er)

/-- In any tournament `G` on `Fin N` and any subset `T ⊆ Fin N`, the number of vertices `v ∈ T`
dominating `T.erase v` is `1` if `∃ v ∈ T, Dominates G v (T.erase v)` and `0` otherwise. -/
theorem card_filter_dominates_erase_eq_ite {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (T : Finset (Fin N)) :
    (T.filter (fun v => Dominates G v (T.erase v))).card =
      if ∃ v ∈ T, Dominates G v (T.erase v) then 1 else 0 := by
  split_ifs with hex
  · rcases hex with ⟨v, hv, hdom⟩
    have heq : T.filter (fun w => Dominates G w (T.erase w)) = {v} := by
      ext w
      rw [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun ⟨hw, hdom_w⟩ => unique_source_of_dominates_erase hG hw hv hdom_w hdom,
        fun h => h ▸ ⟨hv, hdom⟩⟩
    rw [heq, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv hdom
    exact hex ⟨v, hv, hdom⟩

/-- For each vertex `v : Fin N` in a tournament `G`, the number of `3`-element subsets `T` having
`v` as their source (`v ∈ T ∧ Dominates G v (T.erase v)`) equals `(outNeigh G v).card.choose 2`. -/
theorem card_filter_powersetCard_three_dominates_erase {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (v : Fin N) :
    (((Finset.univ : Finset (Fin N)).powersetCard 3).filter
      (fun T => v ∈ T ∧ Dominates G v (T.erase v))).card =
      (outNeigh G v).card.choose 2 := by
  rw [← Finset.card_powersetCard 2 (outNeigh G v)]
  symm
  refine Finset.card_bij (fun S _ => insert v S) ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hv_not : v ∉ S := by
      intro hvS
      exact hG.1 v (mem_outNeigh_iff.mp (hS.1 hvS))
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self v S, ?_⟩
    · rw [Finset.card_insert_of_notMem hv_not, hS.2]
    · rw [Finset.erase_insert hv_not]
      intro u hu
      exact mem_outNeigh_iff.mp (hS.1 hu)
  · intro S₁ hS₁ S₂ hS₂ heq
    rw [Finset.mem_powersetCard] at hS₁ hS₂
    have hv1 : v ∉ S₁ := fun h => hG.1 v (mem_outNeigh_iff.mp (hS₁.1 h))
    have hv2 : v ∉ S₂ := fun h => hG.1 v (mem_outNeigh_iff.mp (hS₂.1 h))
    have her := congrArg (fun T : Finset (Fin N) => T.erase v) heq
    simpa [Finset.erase_insert hv1, Finset.erase_insert hv2] using her
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    refine ⟨T.erase v, ?_, Finset.insert_erase hT.2.1⟩
    rw [Finset.mem_powersetCard]
    refine ⟨fun u hu => mem_outNeigh_iff.mpr (hT.2.2 u hu), ?_⟩
    rw [Finset.card_erase_of_mem hT.2.1, hT.1.2]

/-- Universal tournament transitive-triple and cyclic-triple counting theorem: in any tournament
`G` on `Fin N`,
`(transitiveTripleFinset G).card = ∑ v, (outNeigh G v).card.choose 2 = ∑ v, (inNeigh G v).card.choose 2 = ∑_{|S|=2} (domSet G S).card`,
and `(cyclicTripleFinset G).card = N.choose 3 - ∑ v, (inNeigh G v).card.choose 2`. -/
theorem card_transitiveTripleFinset_eq_sum_choose_two {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) :
    (transitiveTripleFinset G).card = (∑ v : Fin N, (outNeigh G v).card.choose 2) ∧
      (transitiveTripleFinset G).card = (∑ v : Fin N, (inNeigh G v).card.choose 2) ∧
      (transitiveTripleFinset G).card =
        (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, (domSet G S).card) ∧
      (cyclicTripleFinset G).card = N.choose 3 - ∑ v : Fin N, (inNeigh G v).card.choose 2 := by
  have hout : (transitiveTripleFinset G).card = ∑ v : Fin N, (outNeigh G v).card.choose 2 := by
    rw [transitiveTripleFinset, Finset.card_filter]
    have hsum1 : (∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard 3,
        if ∃ v ∈ T, Dominates G v (T.erase v) then 1 else 0) =
      ∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard 3,
        (T.filter (fun v => Dominates G v (T.erase v))).card :=
      Finset.sum_congr rfl (fun T _ => (card_filter_dominates_erase_eq_ite hG T).symm)
    rw [hsum1]
    have hsum2 : (∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard 3,
        (T.filter (fun v => Dominates G v (T.erase v))).card) =
      ∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard 3,
        ∑ v : Fin N, if v ∈ T ∧ Dominates G v (T.erase v) then 1 else 0 := by
      refine Finset.sum_congr rfl (fun T _ => ?_)
      have hfilt : T.filter (fun v => Dominates G v (T.erase v)) =
          Finset.univ.filter (fun v : Fin N => v ∈ T ∧ Dominates G v (T.erase v)) := by
        ext v
        simp [Finset.mem_filter]
      rw [hfilt, Finset.card_filter]
    rw [hsum2, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.card_filter, card_filter_powersetCard_three_dominates_erase hG v]
  have hin := (sum_choose_two_outNeigh_eq_sum_choose_two_inNeigh hG).1
  have hdom := (sum_choose_two_outNeigh_eq_sum_choose_two_inNeigh hG).2
  have htot := (transitiveTripleFinset_disjoint_and_union G).2.2
  refine ⟨hout, hout.trans hin, (hout.trans hin).trans hdom.symm, ?_⟩
  have htr : (transitiveTripleFinset G).card = ∑ v : Fin N, (inNeigh G v).card.choose 2 :=
    hout.trans hin
  omega

/-- Regular tournament transitive-triple and cyclic-triple formulas: if every vertex in a
tournament `G` on `Fin N` has in-degree `d`, then `(transitiveTripleFinset G).card = N * d.choose 2`,
`(cyclicTripleFinset G).card = N.choose 3 - N * d.choose 2`, and
`∑_{|S|=2} (domSet G S).card = N * d.choose 2`. -/
theorem card_transitive_and_cyclic_triples_of_regular {N d : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (hreg : ∀ v : Fin N, (inNeigh G v).card = d) :
    (transitiveTripleFinset G).card = N * d.choose 2 ∧
      (cyclicTripleFinset G).card = N.choose 3 - N * d.choose 2 ∧
      (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard 2, (domSet G S).card) = N * d.choose 2 := by
  have hcounts := card_transitiveTripleFinset_eq_sum_choose_two hG
  have hsum : (∑ v : Fin N, (inNeigh G v).card.choose 2) = N * d.choose 2 := by
    have hcongr : (∑ v : Fin N, (inNeigh G v).card.choose 2) = ∑ _v : Fin N, d.choose 2 :=
      Finset.sum_congr rfl (fun v _ => by rw [hreg v])
    rw [hcongr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact ⟨hcounts.2.1.trans hsum, hcounts.2.2.2.trans (by rw [hsum]),
    hcounts.2.2.1.symm.trans (hcounts.2.1.trans hsum)⟩

/-- Exact transitive-triple, cyclic-triple, and `3`-subset common-dominator sum formulas for any
`n`-paradoxical tournament `G` (`2 ≤ n`) at the Szekeres–Szekeres extremal odd order
`N = (n + 2) * 2 ^ (n - 1) - 1`. -/
theorem szekeres_extremal_triple_and_domSet_counts {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) (hn : 2 ≤ n) (hN : N = (n + 2) * 2 ^ (n - 1) - 1) :
    (transitiveTripleFinset G).card = N * ((n + 2) * 2 ^ (n - 2) - 1).choose 2 ∧
      (cyclicTripleFinset G).card = N.choose 3 - N * ((n + 2) * 2 ^ (n - 2) - 1).choose 2 ∧
      (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard 3, (domSet G S).card) =
        N * ((n + 2) * 2 ^ (n - 2) - 1).choose 3 := by
  let d := (n + 2) * 2 ^ (n - 2) - 1
  have hreg_in : ∀ v : Fin N, (inNeigh G v).card = d := fun v =>
    (regular_of_isParadoxicalTournament_szekeres_extremal hG hn hN v).1
  have hreg_out : ∀ v : Fin N, (outNeigh G v).card = d := fun v =>
    (regular_of_isParadoxicalTournament_szekeres_extremal hG hn hN v).2
  have htr := card_transitive_and_cyclic_triples_of_regular hG.1 hreg_in
  have hdom3 : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard 3, (domSet G S).card) =
      N * d.choose 3 := by
    rw [sum_card_domSet_eq_sum_choose_outNeigh G 3]
    have hcongr : (∑ v : Fin N, (outNeigh G v).card.choose 3) = ∑ _v : Fin N, d.choose 3 :=
      Finset.sum_congr rfl (fun v _ => by rw [hreg_out v])
    rw [hcongr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact ⟨htr.1, htr.2.1, hdom3⟩




end Erdos902
end
