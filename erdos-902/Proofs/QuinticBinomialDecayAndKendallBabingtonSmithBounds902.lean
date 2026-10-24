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
public import SecondOrderBinomialDecayAndTransitiveTripleCounting902

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
set_option maxRecDepth 200000
set_option exponentiation.threshold 4096

noncomputable section
open scoped Classical BigOperators

namespace Erdos902

/-!
## Section 1: Fifth-Order (Quintic) Binomial Decay (`163/60` and `19/7`) & Dyadic Lower-Bound Monotonicity
-/

/-- Theorem 1: Fifth-order (quintic) natural-number binomial expansion lower bound:
`120 * a ^ (m + 5) + 120 * (m + 5) * a ^ (m + 4) + 60 * (m + 5) * (m + 4) * a ^ (m + 3) + 20 * (m + 5) * (m + 4) * (m + 3) * a ^ (m + 2) + 5 * (m + 5) * (m + 4) * (m + 3) * (m + 2) * a ^ (m + 1) + (m + 5) * (m + 4) * (m + 3) * (m + 2) * (m + 1) * a ^ m ≤ 120 * (a + 1) ^ (m + 5)`,
and for all `1 ≤ a`, `163 * a ^ (a + 1) < 60 * (a + 1) ^ (a + 1)` and
`19 * a ^ (a + 1) < 7 * (a + 1) ^ (a + 1)`. -/
theorem fifth_order_binomial_nat_pow_bound (a m : ℕ) :
    120 * a ^ (m + 5) + 120 * (m + 5) * a ^ (m + 4) +
        60 * (m + 5) * (m + 4) * a ^ (m + 3) +
        20 * (m + 5) * (m + 4) * (m + 3) * a ^ (m + 2) +
        5 * (m + 5) * (m + 4) * (m + 3) * (m + 2) * a ^ (m + 1) +
        (m + 5) * (m + 4) * (m + 3) * (m + 2) * (m + 1) * a ^ m ≤
      120 * (a + 1) ^ (m + 5) ∧
    (1 ≤ a →
      163 * a ^ (a + 1) < 60 * (a + 1) ^ (a + 1) ∧
        19 * a ^ (a + 1) < 7 * (a + 1) ^ (a + 1)) := by
  have haux : ∀ b k : ℕ,
      120 * b ^ (k + 5) + 120 * (k + 5) * b ^ (k + 4) +
          60 * (k + 5) * (k + 4) * b ^ (k + 3) +
          20 * (k + 5) * (k + 4) * (k + 3) * b ^ (k + 2) +
          5 * (k + 5) * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) +
          (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) * b ^ k ≤
        120 * (b + 1) ^ (k + 5) := by
    intro b k
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_zero, pow_one, mul_one]
      have hring :
          120 * b ^ 5 + 120 * 5 * b ^ 4 + 60 * 5 * 4 * b ^ 3 +
            20 * 5 * 4 * 3 * b ^ 2 + 5 * 5 * 4 * 3 * 2 * b + 5 * 4 * 3 * 2 * 1 =
            120 * (b + 1) ^ 5 := by ring
      omega
    | succ k ih =>
      calc
        120 * b ^ (k + 6) + 120 * (k + 6) * b ^ (k + 5) +
            60 * (k + 6) * (k + 5) * b ^ (k + 4) +
            20 * (k + 6) * (k + 5) * (k + 4) * b ^ (k + 3) +
            5 * (k + 6) * (k + 5) * (k + 4) * (k + 3) * b ^ (k + 2) +
            (k + 6) * (k + 5) * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) ≤
          (120 * b ^ (k + 5) + 120 * (k + 5) * b ^ (k + 4) +
            60 * (k + 5) * (k + 4) * b ^ (k + 3) +
            20 * (k + 5) * (k + 4) * (k + 3) * b ^ (k + 2) +
            5 * (k + 5) * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) +
            (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) * b ^ k) * (b + 1) := by
          have hexp :
              (120 * b ^ (k + 5) + 120 * (k + 5) * b ^ (k + 4) +
                60 * (k + 5) * (k + 4) * b ^ (k + 3) +
                20 * (k + 5) * (k + 4) * (k + 3) * b ^ (k + 2) +
                5 * (k + 5) * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) +
                (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) * b ^ k) * (b + 1) =
              120 * b ^ (k + 6) + 120 * (k + 6) * b ^ (k + 5) +
                60 * (k + 6) * (k + 5) * b ^ (k + 4) +
                20 * (k + 6) * (k + 5) * (k + 4) * b ^ (k + 3) +
                5 * (k + 6) * (k + 5) * (k + 4) * (k + 3) * b ^ (k + 2) +
                (k + 6) * (k + 5) * (k + 4) * (k + 3) * (k + 2) * b ^ (k + 1) +
                (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) * b ^ k := by ring
          omega
        _ ≤ 120 * (b + 1) ^ (k + 5) * (b + 1) := Nat.mul_le_mul_right (b + 1) ih
        _ = 120 * (b + 1) ^ (k + 6) := by ring
  refine ⟨haux a m, fun ha => ?_⟩
  by_cases ha4 : 4 ≤ a
  · obtain ⟨k, rfl⟩ : ∃ k, a = k + 4 := ⟨a - 4, by omega⟩
    have hk := haux (k + 4) k
    have hp1 : (k + 4) ^ (k + 1) = (k + 4) * (k + 4) ^ k := by rw [pow_succ']
    have hp2 : (k + 4) ^ (k + 2) = (k + 4) ^ 2 * (k + 4) ^ k := by rw [← pow_add, add_comm 2 k]
    have hp3 : (k + 4) ^ (k + 3) = (k + 4) ^ 3 * (k + 4) ^ k := by rw [← pow_add, add_comm 3 k]
    have hp4 : (k + 4) ^ (k + 4) = (k + 4) ^ 4 * (k + 4) ^ k := by rw [← pow_add, add_comm 4 k]
    have hp5 : (k + 4) ^ (k + 5) = (k + 4) ^ 5 * (k + 4) ^ k := by rw [← pow_add, add_comm 5 k]
    have hpos : 0 < (k + 4) ^ k := Nat.pos_of_ne_zero (by positivity)
    have hstrict :
        326 * (k + 4) ^ (k + 5) <
          120 * (k + 4) ^ (k + 5) + 120 * (k + 5) * (k + 4) ^ (k + 4) +
            60 * (k + 5) * (k + 4) * (k + 4) ^ (k + 3) +
            20 * (k + 5) * (k + 4) * (k + 3) * (k + 4) ^ (k + 2) +
            5 * (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 4) ^ (k + 1) +
            (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) * (k + 4) ^ k := by
      rw [hp1, hp2, hp3, hp4, hp5]
      have hpoly :
          326 * (k + 4) ^ 5 <
            120 * (k + 4) ^ 5 + 120 * (k + 5) * (k + 4) ^ 4 +
              60 * (k + 5) * (k + 4) * (k + 4) ^ 3 +
              20 * (k + 5) * (k + 4) * (k + 3) * (k + 4) ^ 2 +
              5 * (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 4) +
              (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) := by
        have hdiff :
            120 * (k + 4) ^ 5 + 120 * (k + 5) * (k + 4) ^ 4 +
              60 * (k + 5) * (k + 4) * (k + 4) ^ 3 +
              20 * (k + 5) * (k + 4) * (k + 3) * (k + 4) ^ 2 +
              5 * (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 4) +
              (k + 5) * (k + 4) * (k + 3) * (k + 2) * (k + 1) =
            326 * (k + 4) ^ 5 +
              (165 * k ^ 4 + 2620 * k ^ 3 + 15615 * k ^ 2 + 41394 * k + 41176) := by ring
        omega
      have hmul := Nat.mul_lt_mul_of_pos_right hpoly hpos
      linarith
    have h326 : 326 * (k + 4) ^ (k + 5) < 120 * (k + 4 + 1) ^ (k + 5) :=
      lt_of_lt_of_le hstrict hk
    have h5 : k + 4 + 1 = k + 5 := by omega
    rw [h5] at h326 ⊢
    exact ⟨by omega, by omega⟩
  · interval_cases a <;> decide

/-- Theorem 2: Single-block fifth-order binomial decay: for all `1 ≤ n`,
`163 * (2 ^ n - 1) ^ (2 ^ n) < 60 * (2 ^ n) ^ (2 ^ n)` and
`19 * (2 ^ n - 1) ^ (2 ^ n) < 7 * (2 ^ n) ^ (2 ^ n)`. -/
theorem nineteen_mul_two_pow_sub_one_pow_lt_seven_mul (n : ℕ) (hn : 1 ≤ n) :
    163 * (2 ^ n - 1) ^ (2 ^ n) < 60 * (2 ^ n) ^ (2 ^ n) ∧
      19 * (2 ^ n - 1) ^ (2 ^ n) < 7 * (2 ^ n) ^ (2 ^ n) := by
  have hpow2 : 2 ≤ 2 ^ n := by
    have : 1 ≤ n := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le this
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
    omega
  have h := (fifth_order_binomial_nat_pow_bound (2 ^ n - 1) 0).2 (by omega)
  have hsucc : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  rwa [hsucc] at h


/-- Theorem 3: Universal dyadic monotonicity of `(1 - 2 ^ (-n)) ^ (2 ^ n)`:
for all `1 ≤ B`, `(B - 1) * (2 * B) ^ 2 < B * (2 * B - 1) ^ 2` and
`(B - 1) ^ B * (2 * B) ^ (2 * B) < B ^ B * (2 * B - 1) ^ (2 * B)`; in particular, for all `1 ≤ n`,
`(2 ^ n - 1) ^ (2 ^ n) * (2 ^ (n + 1)) ^ (2 ^ (n + 1)) < (2 ^ n) ^ (2 ^ n) * (2 ^ (n + 1) - 1) ^ (2 ^ (n + 1))`. -/
theorem dyadic_square_step_and_one_minus_inv_pow_strict_mono (B n : ℕ)
    (hB : 1 ≤ B) (_hn : 1 ≤ n) :
    (B - 1) * (2 * B) ^ 2 < B * (2 * B - 1) ^ 2 ∧
      (B - 1) ^ B * (2 * B) ^ (2 * B) < B ^ B * (2 * B - 1) ^ (2 * B) ∧
      (2 ^ n - 1) ^ (2 ^ n) * (2 ^ (n + 1)) ^ (2 ^ (n + 1)) <
        (2 ^ n) ^ (2 ^ n) * (2 ^ (n + 1) - 1) ^ (2 ^ (n + 1)) := by
  have hquad : ∀ M : ℕ, 1 ≤ M → (M - 1) * (2 * M) ^ 2 < M * (2 * M - 1) ^ 2 := by
    intro M hM
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
    have h1 : 1 + k - 1 = k := by omega
    have h2 : 2 * (1 + k) - 1 = 2 * k + 1 := by omega
    rw [h1, h2]
    have hexp : (1 + k) * (2 * k + 1) ^ 2 = k * (2 * (1 + k)) ^ 2 + (1 + k) := by ring
    omega
  have hpow_step : ∀ M : ℕ, 1 ≤ M →
      (M - 1) ^ M * (2 * M) ^ (2 * M) < M ^ M * (2 * M - 1) ^ (2 * M) := by
    intro M hM
    have hq := hquad M hM
    have hp := Nat.pow_lt_pow_left hq (by omega : M ≠ 0)
    have hl : ((M - 1) * (2 * M) ^ 2) ^ M = (M - 1) ^ M * (2 * M) ^ (2 * M) := by
      rw [mul_pow, ← pow_mul]
    have hr : (M * (2 * M - 1) ^ 2) ^ M = M ^ M * (2 * M - 1) ^ (2 * M) := by
      rw [mul_pow, ← pow_mul]
    rwa [hl, hr] at hp
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hstep_n := hpow_step (2 ^ n) h2n
  have hsucc : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ']
  rw [hsucc] at hstep_n
  exact ⟨hquad B hB, hpow_step B hB, hstep_n⟩

/-- Theorem 4: Universal upward propagation of rational lower bounds `p / q` on `(1 - 2 ^ (-n)) ^ (2 ^ n)`
and explicit lower bounds `1 / 3` (`n ≥ 3`), `4 / 11` (`n ≥ 6`), and `7 / 20` (`n ≥ 4`). -/
theorem rational_lower_bound_step_and_three_eleven_twenty
    {p q k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hbase : p * (2 ^ k) ^ (2 ^ k) ≤ q * (2 ^ k - 1) ^ (2 ^ k)) :
    p * (2 ^ n) ^ (2 ^ n) ≤ q * (2 ^ n - 1) ^ (2 ^ n) ∧
      (3 ≤ n → (2 ^ n) ^ (2 ^ n) < 3 * (2 ^ n - 1) ^ (2 ^ n)) ∧
      (4 ≤ n → 7 * (2 ^ n) ^ (2 ^ n) < 20 * (2 ^ n - 1) ^ (2 ^ n)) ∧
      (6 ≤ n → 4 * (2 ^ n) ^ (2 ^ n) < 11 * (2 ^ n - 1) ^ (2 ^ n)) := by
  have hprop_le : ∀ p₀ q₀ k₀ d : ℕ, 1 ≤ k₀ →
      p₀ * (2 ^ k₀) ^ (2 ^ k₀) ≤ q₀ * (2 ^ k₀ - 1) ^ (2 ^ k₀) →
      p₀ * (2 ^ (k₀ + d)) ^ (2 ^ (k₀ + d)) ≤ q₀ * (2 ^ (k₀ + d) - 1) ^ (2 ^ (k₀ + d)) := by
    intro p₀ q₀ k₀ d hk₀ hb
    induction d with
    | zero => simpa using hb
    | succ d ih =>
      let m := k₀ + d
      have hm : 1 ≤ m := by omega
      have hmono := (dyadic_square_step_and_one_minus_inv_pow_strict_mono 1 m (by decide) hm).2.2
      have hpos : 0 < (2 ^ m) ^ (2 ^ m) := Nat.pos_of_ne_zero (by positivity)
      have hmul :
          (2 ^ m) ^ (2 ^ m) * (p₀ * (2 ^ (m + 1)) ^ (2 ^ (m + 1))) ≤
            (2 ^ m) ^ (2 ^ m) * (q₀ * (2 ^ (m + 1) - 1) ^ (2 ^ (m + 1))) := by
        calc
          (2 ^ m) ^ (2 ^ m) * (p₀ * (2 ^ (m + 1)) ^ (2 ^ (m + 1)))
              = (p₀ * (2 ^ m) ^ (2 ^ m)) * (2 ^ (m + 1)) ^ (2 ^ (m + 1)) := by ring
          _ ≤ (q₀ * (2 ^ m - 1) ^ (2 ^ m)) * (2 ^ (m + 1)) ^ (2 ^ (m + 1)) :=
            Nat.mul_le_mul_right _ ih
          _ = q₀ * ((2 ^ m - 1) ^ (2 ^ m) * (2 ^ (m + 1)) ^ (2 ^ (m + 1))) := by ring
          _ ≤ q₀ * ((2 ^ m) ^ (2 ^ m) * (2 ^ (m + 1) - 1) ^ (2 ^ (m + 1))) :=
            Nat.mul_le_mul_left q₀ (le_of_lt hmono)
          _ = (2 ^ m) ^ (2 ^ m) * (q₀ * (2 ^ (m + 1) - 1) ^ (2 ^ (m + 1))) := by ring
      have h1 : k₀ + (d + 1) = m + 1 := by omega
      rw [h1]
      exact Nat.le_of_mul_le_mul_left hmul hpos
  have hprop_lt : ∀ p₀ q₀ k₀ d : ℕ, 1 ≤ k₀ →
      p₀ * (2 ^ k₀) ^ (2 ^ k₀) < q₀ * (2 ^ k₀ - 1) ^ (2 ^ k₀) →
      p₀ * (2 ^ (k₀ + d)) ^ (2 ^ (k₀ + d)) < q₀ * (2 ^ (k₀ + d) - 1) ^ (2 ^ (k₀ + d)) := by
    intro p₀ q₀ k₀ d hk₀ hb
    induction d with
    | zero => simpa using hb
    | succ d ih =>
      let m := k₀ + d
      have hm : 1 ≤ m := by omega
      have hmono := (dyadic_square_step_and_one_minus_inv_pow_strict_mono 1 m (by decide) hm).2.2
      have hpos_next : 0 < (2 ^ (m + 1)) ^ (2 ^ (m + 1)) := Nat.pos_of_ne_zero (by positivity)
      have hmul :
          (2 ^ m) ^ (2 ^ m) * (p₀ * (2 ^ (m + 1)) ^ (2 ^ (m + 1))) <
            (2 ^ m) ^ (2 ^ m) * (q₀ * (2 ^ (m + 1) - 1) ^ (2 ^ (m + 1))) := by
        calc
          (2 ^ m) ^ (2 ^ m) * (p₀ * (2 ^ (m + 1)) ^ (2 ^ (m + 1)))
              = (p₀ * (2 ^ m) ^ (2 ^ m)) * (2 ^ (m + 1)) ^ (2 ^ (m + 1)) := by ring
          _ < (q₀ * (2 ^ m - 1) ^ (2 ^ m)) * (2 ^ (m + 1)) ^ (2 ^ (m + 1)) :=
            Nat.mul_lt_mul_of_pos_right ih hpos_next
          _ = q₀ * ((2 ^ m - 1) ^ (2 ^ m) * (2 ^ (m + 1)) ^ (2 ^ (m + 1))) := by ring
          _ ≤ q₀ * ((2 ^ m) ^ (2 ^ m) * (2 ^ (m + 1) - 1) ^ (2 ^ (m + 1))) :=
            Nat.mul_le_mul_left q₀ (le_of_lt hmono)
          _ = (2 ^ m) ^ (2 ^ m) * (q₀ * (2 ^ (m + 1) - 1) ^ (2 ^ (m + 1))) := by ring
      have h1 : k₀ + (d + 1) = m + 1 := by omega
      rw [h1]
      exact lt_of_mul_lt_mul_left hmul (Nat.zero_le _)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  refine ⟨hprop_le p q k d hk hbase, ?_, ?_, ?_⟩
  · intro hn3
    obtain ⟨d3, hd3⟩ := Nat.exists_eq_add_of_le hn3
    rw [hd3]
    simpa using hprop_lt 1 3 3 d3 (by decide) (by decide)
  · intro hn4
    obtain ⟨d4, hd4⟩ := Nat.exists_eq_add_of_le hn4
    rw [hd4]
    simpa using hprop_lt 7 20 4 d4 (by decide) (by decide)
  · intro hn6
    obtain ⟨d6, hd6⟩ := Nat.exists_eq_add_of_le hn6
    rw [hd6]
    simpa using hprop_lt 4 11 6 d6 (by decide) (by decide)

/-!
## Section 2: `Nat.descFactorial` Probabilistic Bridges & Sub-Quadratic Mid-Range Bounds
-/

/-- Theorem 5: Exact bridge from `Nat.descFactorial` to `ErdosProbabilisticCriterion`:
if `p * (2 ^ n - 1) ^ (2 ^ n) < q * (2 ^ n) ^ (2 ^ n)` and
`q ^ t * (n + t * 2 ^ n).descFactorial n ≤ n.factorial * p ^ t`, then
`ErdosProbabilisticCriterion n (n + t * 2 ^ n)` holds. -/
theorem erdosProbabilisticCriterion_of_descFactorial_le {n t p q : ℕ}
    (ht : 1 ≤ t) (hp : 1 ≤ p)
    (hbase : p * (2 ^ n - 1) ^ (2 ^ n) < q * (2 ^ n) ^ (2 ^ n))
    (hdesc : q ^ t * (n + t * 2 ^ n).descFactorial n ≤ n.factorial * p ^ t) :
    ErdosProbabilisticCriterion n (n + t * 2 ^ n) := by
  apply (erdosProbabilisticCriterion_of_rational_base_decay ht hp hbase).1
  have hfact_pos : 0 < n.factorial := Nat.factorial_pos n
  have heq := Nat.descFactorial_eq_factorial_mul_choose (n + t * 2 ^ n) n
  have hmul : n.factorial * (q ^ t * (n + t * 2 ^ n).choose n) ≤ n.factorial * p ^ t := by
    calc
      n.factorial * (q ^ t * (n + t * 2 ^ n).choose n)
          = q ^ t * (n.factorial * (n + t * 2 ^ n).choose n) := by ring
      _ = q ^ t * (n + t * 2 ^ n).descFactorial n := by rw [← heq]
      _ ≤ n.factorial * p ^ t := hdesc
  exact Nat.le_of_mul_le_mul_left hmul hfact_pos

/-- Theorem 6: Universal rational-lower-bound falsifier for `ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)`
via `Nat.descFactorial`:
if `1 ≤ n`, `1 ≤ p`, `p * (2 ^ n) ^ (2 ^ n) ≤ q * (2 ^ n - 1) ^ (2 ^ n)`, and
`n.factorial * q ^ (n ^ 2) ≤ (n ^ 2 * 2 ^ n).descFactorial n * p ^ (n ^ 2)`, then
`¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)`. -/
theorem not_erdosProbabilisticCriterion_sq_of_rational_lower_bound (n p q : ℕ)
    (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hlb : p * (2 ^ n) ^ (2 ^ n) ≤ q * (2 ^ n - 1) ^ (2 ^ n))
    (hdesc : n.factorial * q ^ (n ^ 2) ≤ (n ^ 2 * 2 ^ n).descFactorial n * p ^ (n ^ 2)) :
    ¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n) := by
  have hchoose : q ^ (n ^ 2) ≤ (n ^ 2 * 2 ^ n).choose n * p ^ (n ^ 2) := by
    have hfact_pos : 0 < n.factorial := Nat.factorial_pos n
    have heq := Nat.descFactorial_eq_factorial_mul_choose (n ^ 2 * 2 ^ n) n
    rw [heq] at hdesc
    have hmul : n.factorial * q ^ (n ^ 2) ≤
        n.factorial * ((n ^ 2 * 2 ^ n).choose n * p ^ (n ^ 2)) := by
      linarith
    exact Nat.le_of_mul_le_mul_left hmul hfact_pos
  dsimp [ErdosProbabilisticCriterion]
  push Not
  let N := n ^ 2 * 2 ^ n
  let t := n ^ 2
  have hpow_t : p ^ t * (2 ^ n) ^ N ≤ q ^ t * (2 ^ n - 1) ^ N := by
    have hstep := Nat.pow_le_pow_left hlb t
    have hl : (p * (2 ^ n) ^ (2 ^ n)) ^ t = p ^ t * (2 ^ n) ^ N := by
      rw [mul_pow, ← pow_mul (2 ^ n) (2 ^ n) t]
      have hexp : 2 ^ n * t = N := by dsimp [N, t]; ring
      rw [hexp]
    have hr : (q * (2 ^ n - 1) ^ (2 ^ n)) ^ t = q ^ t * (2 ^ n - 1) ^ N := by
      rw [mul_pow, ← pow_mul (2 ^ n - 1) (2 ^ n) t]
      have hexp : 2 ^ n * t = N := by dsimp [N, t]; ring
      rw [hexp]
    rwa [hl, hr] at hstep
  have h2n_ge : 2 ≤ 2 ^ n := by
    have : 1 ≤ n := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le this
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
    omega
  have hn_le_N : n ≤ N := by
    dsimp [N]
    have h1 : 1 ≤ n ^ 2 := by nlinarith
    have h2 : n ≤ 2 ^ n := le_of_lt (Nat.lt_two_pow_self)
    nlinarith
  have hN_split : N - n + n = N := Nat.sub_add_cancel hn_le_N
  have ha_pos : 0 < (2 ^ n - 1) ^ n := Nat.pos_of_ne_zero (by
    apply pow_ne_zero
    omega)
  have hpt_pos : 0 < p ^ t := Nat.pos_of_ne_zero (by
    apply pow_ne_zero
    omega)
  have hfactor : (2 ^ n - 1) ^ n ≤ (2 ^ n) ^ n :=
    Nat.pow_le_pow_left (by omega) n
  have hchain :
      (p ^ t * (2 ^ n - 1) ^ n) * (2 ^ n) ^ (N - n) ≤
        (p ^ t * (2 ^ n - 1) ^ n) * (N.choose n * (2 ^ n - 1) ^ (N - n)) := by
    calc
      (p ^ t * (2 ^ n - 1) ^ n) * (2 ^ n) ^ (N - n)
          ≤ (p ^ t * (2 ^ n) ^ n) * (2 ^ n) ^ (N - n) := by
            apply Nat.mul_le_mul_right
            exact Nat.mul_le_mul_left _ hfactor
      _ = p ^ t * ((2 ^ n) ^ (N - n) * (2 ^ n) ^ n) := by ring
      _ = p ^ t * (2 ^ n) ^ N := by rw [← pow_add, hN_split]
      _ ≤ q ^ t * (2 ^ n - 1) ^ N := hpow_t
      _ ≤ (N.choose n * p ^ t) * (2 ^ n - 1) ^ N := Nat.mul_le_mul_right _ hchoose
      _ = (N.choose n * p ^ t) * ((2 ^ n - 1) ^ (N - n) * (2 ^ n - 1) ^ n) := by
            rw [← pow_add, hN_split]
      _ = (p ^ t * (2 ^ n - 1) ^ n) * (N.choose n * (2 ^ n - 1) ^ (N - n)) := by ring
  exact Nat.le_of_mul_le_mul_left hchain (Nat.mul_pos hpt_pos ha_pos)

/-- Theorem 7: Complete falsification of `ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n)`
for all `1 ≤ n ≤ 9`. -/
theorem not_erdosProbabilisticCriterion_sq_mul_two_pow_of_le_nine {n : ℕ}
    (hn1 : 1 ≤ n) (hn9 : n ≤ 9) :
    ¬ ErdosProbabilisticCriterion n (n ^ 2 * 2 ^ n) := by
  by_cases hn4 : n ≤ 4
  · exact not_erdosProbabilisticCriterion_sq_mul_two_pow_of_le_four hn1 hn4
  · have hbounds := rational_lower_bound_step_and_three_eleven_twenty
      (by decide : 1 ≤ 3) (by omega : 3 ≤ n) (by decide : 1 * (2 ^ 3) ^ (2 ^ 3) ≤ 3 * (2 ^ 3 - 1) ^ (2 ^ 3))
    interval_cases n
    · have h3 := hbounds.2.1 (by decide)
      exact not_erdosProbabilisticCriterion_sq_of_rational_lower_bound 5 1 3 (by decide) (by decide)
        (by linarith) (by decide)
    · have h3 := hbounds.2.1 (by decide)
      exact not_erdosProbabilisticCriterion_sq_of_rational_lower_bound 6 1 3 (by decide) (by decide)
        (by linarith) (by decide)
    · have h11 := hbounds.2.2.2 (by decide)
      exact not_erdosProbabilisticCriterion_sq_of_rational_lower_bound 7 4 11 (by decide) (by decide)
        (le_of_lt h11) (by decide)
    · have h11 := hbounds.2.2.2 (by decide)
      exact not_erdosProbabilisticCriterion_sq_of_rational_lower_bound 8 4 11 (by decide) (by decide)
        (le_of_lt h11) (by decide)
    · have h11 := hbounds.2.2.2 (by decide)
      exact not_erdosProbabilisticCriterion_sq_of_rational_lower_bound 9 4 11 (by decide) (by decide)
        (le_of_lt h11) (by decide)

/-- Theorem 8: Explicit intermediate upper bounds for `5 ≤ n ≤ 10` via the `19 / 7` fifth-order
binomial decay:
`legacyF 5 ≤ 965`, `legacyF 6 ≤ 2630`, `legacyF 7 ≤ 6919`, `legacyF 8 ≤ 17416`, `legacyF 9 ≤ 43017`, `legacyF 10 ≤ 103434`,
and for all `1 ≤ n`, `legacyF n ≤ n + (n ^ 2 + 5) * 2 ^ n`. -/
theorem mid_range_quintic_upper_bounds_and_global_add_five :
    legacyF 5 ≤ 965 ∧
      legacyF 6 ≤ 2630 ∧
      legacyF 7 ≤ 6919 ∧
      legacyF 8 ≤ 17416 ∧
      legacyF 9 ≤ 43017 ∧
      legacyF 10 ≤ 103434 ∧
      (∀ n : ℕ, 1 ≤ n → legacyF n ≤ n + (n ^ 2 + 5) * 2 ^ n) := by
  have h5 : legacyF 5 ≤ 965 := by
    have hb := (nineteen_mul_two_pow_sub_one_pow_lt_seven_mul 5 (by decide)).2
    have hc := erdosProbabilisticCriterion_of_descFactorial_le
      (by decide : 1 ≤ 30) (by decide : 1 ≤ 19) hb (by decide)
    exact legacyF_le_of_hasParadoxicalTournament
      (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide) hc).2
  have h6 : legacyF 6 ≤ 2630 := by
    have hb := (nineteen_mul_two_pow_sub_one_pow_lt_seven_mul 6 (by decide)).2
    have hc := erdosProbabilisticCriterion_of_descFactorial_le
      (by decide : 1 ≤ 41) (by decide : 1 ≤ 19) hb (by decide)
    exact legacyF_le_of_hasParadoxicalTournament
      (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide) hc).2
  have h7 : legacyF 7 ≤ 6919 := by
    have hb := (nineteen_mul_two_pow_sub_one_pow_lt_seven_mul 7 (by decide)).2
    have hc := erdosProbabilisticCriterion_of_descFactorial_le
      (by decide : 1 ≤ 54) (by decide : 1 ≤ 19) hb (by decide)
    exact legacyF_le_of_hasParadoxicalTournament
      (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide) hc).2
  have h8 : legacyF 8 ≤ 17416 := by
    have hb := (nineteen_mul_two_pow_sub_one_pow_lt_seven_mul 8 (by decide)).2
    have hc := erdosProbabilisticCriterion_of_descFactorial_le
      (by decide : 1 ≤ 68) (by decide : 1 ≤ 19) hb (by decide)
    exact legacyF_le_of_hasParadoxicalTournament
      (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide) hc).2
  have h9 : legacyF 9 ≤ 43017 := by
    have hb := (nineteen_mul_two_pow_sub_one_pow_lt_seven_mul 9 (by decide)).2
    have hc := erdosProbabilisticCriterion_of_descFactorial_le
      (by decide : 1 ≤ 84) (by decide : 1 ≤ 19) hb (by decide)
    exact legacyF_le_of_hasParadoxicalTournament
      (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide) hc).2
  have h10 : legacyF 10 ≤ 103434 := by
    have hb := (nineteen_mul_two_pow_sub_one_pow_lt_seven_mul 10 (by decide)).2
    have hc := erdosProbabilisticCriterion_of_descFactorial_le
      (by decide : 1 ≤ 101) (by decide : 1 ≤ 19) hb (by decide)
    exact legacyF_le_of_hasParadoxicalTournament
      (hasParadoxicalTournament_of_erdosProbabilisticCriterion (by decide) hc).2
  refine ⟨h5, h6, h7, h8, h9, h10, fun n hn => ?_⟩
  by_cases hn11 : 11 ≤ n
  · have hle := (hasParadoxicalTournament_and_f_le_sq_mul_two_pow_of_eleven_le hn11).2.1
    have h2 : n ^ 2 * 2 ^ n ≤ n + (n ^ 2 + 5) * 2 ^ n := by
      have : n ^ 2 * 2 ^ n ≤ (n ^ 2 + 5) * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      omega
    exact le_trans hle h2
  · interval_cases n
    · have := (f_le_sq_mul_two_pow_small_cases (by decide : 1 ≤ 1) (by decide)).1; omega
    · have := (f_le_sq_mul_two_pow_small_cases (by decide : 1 ≤ 2) (by decide)).1; omega
    · have := (f_le_sq_mul_two_pow_small_cases (by decide : 1 ≤ 3) (by decide)).1; omega
    · have := (f_le_sq_mul_two_pow_small_cases (by decide : 1 ≤ 4) (by decide)).1; omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega

/-!
## Section 3: Kendall–Babington Smith (1940) Cyclic-Triple Upper Bounds for Odd and Even Tournaments
-/

/-- Theorem 9: Degree-pair binomial convexity for even sum `a + b = 2 * m`:
`2 * m.choose 2 ≤ a.choose 2 + b.choose 2`, with equality iff `a = m ∧ b = m`. -/
theorem choose_two_add_choose_two_ge_of_add_eq_two_mul {a b m : ℕ}
    (hab : a + b = 2 * m) :
    2 * m.choose 2 ≤ a.choose 2 + b.choose 2 ∧
      (a.choose 2 + b.choose 2 = 2 * m.choose 2 ↔ a = m ∧ b = m) := by
  have ha := two_mul_choose_two_add_self a
  have hb := two_mul_choose_two_add_self b
  have hm := two_mul_choose_two_add_self m
  have hsq : 2 * m ^ 2 ≤ a ^ 2 + b ^ 2 := by
    zify at hab ⊢
    nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]
  refine ⟨by omega, ⟨fun heq => ?_, fun ⟨ha_eq, hb_eq⟩ => by subst ha_eq hb_eq; omega⟩⟩
  have hsq_eq : a ^ 2 + b ^ 2 = 2 * m ^ 2 := by omega
  have hab_z : (a : ℤ) + (b : ℤ) = 2 * (m : ℤ) := by exact_mod_cast hab
  have hsq_z : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = 2 * (m : ℤ) ^ 2 := by exact_mod_cast hsq_eq
  have hdiff_sq : ((a : ℤ) - (b : ℤ)) ^ 2 = 0 := by nlinarith
  have hab_eq_z : (a : ℤ) = (b : ℤ) := sub_eq_zero.mp (sq_eq_zero_iff.mp hdiff_sq)
  have hab_eq : a = b := by exact_mod_cast hab_eq_z
  omega

/-- Theorem 10: Degree-pair binomial convexity for odd sum `a + b = 2 * m - 1` (`1 ≤ m`):
`(m - 1) ^ 2 ≤ a.choose 2 + b.choose 2`. -/
theorem choose_two_add_choose_two_ge_of_add_eq_two_mul_sub_one {a b m : ℕ}
    (hm1 : 1 ≤ m) (hab : a + b = 2 * m - 1) :
    (m - 1) ^ 2 ≤ a.choose 2 + b.choose 2 := by
  have ha := two_mul_choose_two_add_self a
  have hb := two_mul_choose_two_add_self b
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm1
  have hab' : a + b = 2 * k + 1 := by omega
  have h1 : 1 + k - 1 = k := by omega
  rw [h1]
  have hne : a ≠ b := by omega
  have hdiff_ge : 1 ≤ ((a : ℤ) - (b : ℤ)) ^ 2 := by
    have hnez : (a : ℤ) - (b : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    have hpos : 0 < ((a : ℤ) - (b : ℤ)) ^ 2 := sq_pos_of_ne_zero hnez
    linarith
  have hab_z : (a : ℤ) + (b : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hab'
  have hsq_z : 2 * (k : ℤ) ^ 2 + 2 * (k : ℤ) + 1 ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    nlinarith
  have hsq_n : 2 * k ^ 2 + 2 * k + 1 ≤ a ^ 2 + b ^ 2 := by exact_mod_cast hsq_z
  omega

/-- Theorem 11: Polynomial identity for the odd-order Kendall–Babington Smith cyclic-triple maximum:
`6 * (2 * m + 1) * m.choose 2 + m * (m + 1) * (2 * m + 1) = 6 * (2 * m + 1).choose 3` and
`24 * ((2 * m + 1).choose 3 - (2 * m + 1) * m.choose 2) = (2 * m + 1) * ((2 * m + 1) ^ 2 - 1)`. -/
theorem kendall_babington_smith_odd_polynomial_identity (m : ℕ) :
    6 * (2 * m + 1) * m.choose 2 + m * (m + 1) * (2 * m + 1) = 6 * (2 * m + 1).choose 3 ∧
      24 * ((2 * m + 1).choose 3 - (2 * m + 1) * m.choose 2) =
        (2 * m + 1) * ((2 * m + 1) ^ 2 - 1) := by
  rcases m with _ | k
  · decide
  · have hm2 := two_mul_choose_two_add_self (k + 1)
    have hdesc := (Nat.descFactorial_eq_factorial_mul_choose (2 * (k + 1) + 1) 3).symm
    have hd3 : (2 * (k + 1) + 1).descFactorial 3 =
        (2 * (k + 1) + 1) * (2 * (k + 1)) * (2 * k + 1) := by
      simp [Nat.descFactorial_succ, Nat.descFactorial_zero]
      have hsub1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [hsub1]
      ring
    have hf3 : (3 : ℕ).factorial = 6 := by decide
    rw [hd3, hf3] at hdesc
    have hsq_sub : (2 * (k + 1) + 1) ^ 2 - 1 = 4 * (k + 1) * (k + 2) := by
      have : (2 * (k + 1) + 1) ^ 2 = 4 * (k + 1) * (k + 2) + 1 := by ring
      omega
    have hpart1 :
        6 * (2 * (k + 1) + 1) * (k + 1).choose 2 +
            (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) =
          6 * (2 * (k + 1) + 1).choose 3 := by
      nlinarith [hm2, hdesc]
    refine ⟨hpart1, ?_⟩
    rw [hsq_sub, Nat.mul_sub_left_distrib]
    have h4 :
        24 * ((2 * (k + 1) + 1) * (k + 1).choose 2) +
            (2 * (k + 1) + 1) * (4 * (k + 1) * (k + 2)) =
          24 * (2 * (k + 1) + 1).choose 3 := by
      linear_combination 4 * hpart1
    omega

/-- Theorem 12 (Kendall–Babington Smith 1940 Odd Tournament Theorem):
In any tournament `G` on `Fin (2 * m + 1)`:
1. `(2 * m + 1) * m.choose 2 ≤ (transitiveTripleFinset G).card`,
2. `(cyclicTripleFinset G).card ≤ (2 * m + 1).choose 3 - (2 * m + 1) * m.choose 2`, and
3. `24 * (cyclicTripleFinset G).card ≤ (2 * m + 1) * ((2 * m + 1) ^ 2 - 1)`,
with equality whenever `G` is `m`-regular. -/
theorem kendall_babington_smith_odd_tournament_bounds {m : ℕ}
    {G : Digraph (Fin (2 * m + 1))} (hG : IsTournament G) :
    (2 * m + 1) * m.choose 2 ≤ (transitiveTripleFinset G).card ∧
      (cyclicTripleFinset G).card ≤ (2 * m + 1).choose 3 - (2 * m + 1) * m.choose 2 ∧
      24 * (cyclicTripleFinset G).card ≤ (2 * m + 1) * ((2 * m + 1) ^ 2 - 1) ∧
      ((∀ v : Fin (2 * m + 1), (inNeigh G v).card = m) →
        24 * (cyclicTripleFinset G).card = (2 * m + 1) * ((2 * m + 1) ^ 2 - 1)) := by
  have htrans := card_transitiveTripleFinset_eq_sum_choose_two hG
  have hcard_union := (transitiveTripleFinset_disjoint_and_union G).2.2
  have hv_bound : ∀ v : Fin (2 * m + 1),
      2 * m.choose 2 ≤ (outNeigh G v).card.choose 2 + (inNeigh G v).card.choose 2 := by
    intro v
    have hdeg := card_outNeigh_add_card_inNeigh hG v
    have h2m : 2 * m + 1 - 1 = 2 * m := by omega
    rw [h2m] at hdeg
    exact (choose_two_add_choose_two_ge_of_add_eq_two_mul hdeg).1
  have hsum_le :
      ∑ v : Fin (2 * m + 1), 2 * m.choose 2 ≤
        (∑ v : Fin (2 * m + 1), (outNeigh G v).card.choose 2) +
          (∑ v : Fin (2 * m + 1), (inNeigh G v).card.choose 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun v _ => hv_bound v)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_le
  have htrans_out := htrans.1
  have htrans_in := htrans.2.1
  have htrans_ge : (2 * m + 1) * m.choose 2 ≤ (transitiveTripleFinset G).card := by
    linarith
  have hcyc_le :
      (cyclicTripleFinset G).card ≤ (2 * m + 1).choose 3 - (2 * m + 1) * m.choose 2 := by
    omega
  have hpoly := (kendall_babington_smith_odd_polynomial_identity m).2
  refine ⟨htrans_ge, hcyc_le, by omega, fun hreg => ?_⟩
  have hreg_cyc := (card_transitive_and_cyclic_triples_of_regular hG hreg).2.1
  rw [hreg_cyc, hpoly]

/-- Theorem 13 (Kendall–Babington Smith Even Tournament Theorem):
In any tournament `G` on `Fin (2 * m)` (`1 ≤ m`):
1. `m * (m - 1) ^ 2 ≤ (transitiveTripleFinset G).card`,
2. `(cyclicTripleFinset G).card ≤ (2 * m).choose 3 - m * (m - 1) ^ 2`, and
3. `24 * (cyclicTripleFinset G).card ≤ 2 * m * ((2 * m) ^ 2 - 4)`. -/
theorem kendall_babington_smith_even_tournament_bounds {m : ℕ} (hm : 1 ≤ m)
    {G : Digraph (Fin (2 * m))} (hG : IsTournament G) :
    m * (m - 1) ^ 2 ≤ (transitiveTripleFinset G).card ∧
      (cyclicTripleFinset G).card ≤ (2 * m).choose 3 - m * (m - 1) ^ 2 ∧
      24 * (cyclicTripleFinset G).card ≤ 2 * m * ((2 * m) ^ 2 - 4) := by
  have htrans := card_transitiveTripleFinset_eq_sum_choose_two hG
  have hcard_union := (transitiveTripleFinset_disjoint_and_union G).2.2
  have hv_bound : ∀ v : Fin (2 * m),
      (m - 1) ^ 2 ≤ (outNeigh G v).card.choose 2 + (inNeigh G v).card.choose 2 := by
    intro v
    have hdeg := card_outNeigh_add_card_inNeigh hG v
    exact choose_two_add_choose_two_ge_of_add_eq_two_mul_sub_one hm hdeg
  have hsum_le :
      ∑ v : Fin (2 * m), (m - 1) ^ 2 ≤
        (∑ v : Fin (2 * m), (outNeigh G v).card.choose 2) +
          (∑ v : Fin (2 * m), (inNeigh G v).card.choose 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun v _ => hv_bound v)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_le
  have htrans_out := htrans.1
  have htrans_in := htrans.2.1
  have htrans_ge : m * (m - 1) ^ 2 ≤ (transitiveTripleFinset G).card := by
    nlinarith
  have hcyc_le : (cyclicTripleFinset G).card ≤ (2 * m).choose 3 - m * (m - 1) ^ 2 := by
    omega
  refine ⟨htrans_ge, hcyc_le, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hdesc := (Nat.descFactorial_eq_factorial_mul_choose (2 * (1 + k)) 3).symm
  have hd3 : (2 * (1 + k)).descFactorial 3 = (2 * (1 + k)) * (2 * k + 1) * (2 * k) := by
    simp [Nat.descFactorial_succ, Nat.descFactorial_zero]
    have hsub1 : 2 * (1 + k) - 1 = 2 * k + 1 := by omega
    have hsub2 : 2 * (1 + k) - 2 = 2 * k := by omega
    rw [hsub1, hsub2]
    ring
  have hf3 : (3 : ℕ).factorial = 6 := by decide
  rw [hd3, hf3] at hdesc
  have hm1 : 1 + k - 1 = k := by omega
  have hsq4 : (2 * (1 + k)) ^ 2 - 4 = 4 * k * (k + 2) := by
    have : (2 * (1 + k)) ^ 2 = 4 * k * (k + 2) + 4 := by ring
    omega
  rw [hm1] at hcyc_le
  rw [hsq4]
  have hpoly :
      24 * ((1 + k) * k ^ 2) + 2 * (1 + k) * (4 * k * (k + 2)) =
        24 * (2 * (1 + k)).choose 3 := by
    nlinarith [hdesc]
  have h24 :
      24 * (cyclicTripleFinset G).card ≤
        24 * (2 * (1 + k)).choose 3 - 24 * ((1 + k) * k ^ 2) := by
    rw [← Nat.mul_sub_left_distrib]
    exact Nat.mul_le_mul_left 24 hcyc_le
  omega

/-- Theorem 14 (Positive Control: Szekeres–Szekeres Extremal `n`-Paradoxical Tournaments
on `Fin ((n + 2) * 2 ^ (n - 1) - 1)` Attain Exact Equality in the Kendall–Babington Smith Bound). -/
theorem szekeres_extremal_attains_kendall_babington_smith {n m : ℕ}
    {G : Digraph (Fin (2 * m + 1))}
    (hG : IsParadoxicalTournament n G) (hn : 2 ≤ n)
    (hm : m = (n + 2) * 2 ^ (n - 2) - 1)
    (hN : 2 * m + 1 = (n + 2) * 2 ^ (n - 1) - 1) :
    24 * (cyclicTripleFinset G).card =
      (2 * m + 1) * ((2 * m + 1) ^ 2 - 1) := by
  apply (kendall_babington_smith_odd_tournament_bounds hG.1).2.2.2
  intro v
  exact ((regular_of_isParadoxicalTournament_szekeres_extremal hG hn hN v).1).trans hm.symm

end Erdos902
end
