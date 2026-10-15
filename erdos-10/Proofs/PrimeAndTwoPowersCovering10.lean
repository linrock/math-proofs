module

/-
Copyright 2025 The Formal Conjectures Authors.
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
@[expose] public noncomputable section
open scoped BigOperators
open Filter
set_option maxHeartbeats 800000


namespace Erdos9

/-- `IsPrimePlusTwoPowers n` holds when `n = p + 2 ^ k + 2 ^ l` for some prime `p`
and natural exponents `k, l : ℕ`. -/
def IsPrimePlusTwoPowers (n : ℕ) : Prop :=
  ∃ p k l : ℕ, Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l

/-- The set of odd numbers that cannot be expressed as a prime plus two powers of `2`. -/
def Erdos9A : Set ℕ :=
  { n | Odd n ∧ ¬ IsPrimePlusTwoPowers n }

/-- `Erdos9A` matches the upstream set definition in `FormalConjectures/ErdosProblems/9.lean`. -/
theorem erdos9A_eq_setOf :
    Erdos9A = { n | Odd n ∧ ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l } :=
  rfl


/-- Every integer expressible as `p + 2 ^ k + 2 ^ l` with `p` prime is at least `4`. -/
theorem four_le_of_isPrimePlusTwoPowers {n : ℕ} (h : IsPrimePlusTwoPowers n) :
    4 ≤ n := by
  rcases h with ⟨p, k, l, hp, rfl⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hl1 : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  omega


/-- No natural number strictly less than `4` belongs to `IsPrimePlusTwoPowers`. -/
theorem not_isPrimePlusTwoPowers_of_lt_four {n : ℕ} (hn : n < 4) :
    ¬ IsPrimePlusTwoPowers n := by
  intro h
  have h4 := four_le_of_isPrimePlusTwoPowers h
  omega


/-- `1` belongs to `Erdos9A`. -/
theorem erdos9A_contains_one : 1 ∈ Erdos9A :=
  ⟨by decide, not_isPrimePlusTwoPowers_of_lt_four (by decide)⟩


/-- `3` belongs to `Erdos9A`. -/
theorem erdos9A_contains_three : 3 ∈ Erdos9A :=
  ⟨by decide, not_isPrimePlusTwoPowers_of_lt_four (by decide)⟩


/-- `5 = 3 + 2 ^ 0 + 2 ^ 0` does not belong to `Erdos9A`. -/
theorem erdos9A_not_contains_five : 5 ∉ Erdos9A := by
  rintro ⟨-, hnot⟩
  exact hnot ⟨3, 0, 0, Nat.prime_three, by decide⟩


/-- Parity dichotomy for `2 ^ k`: either `k = 0` and `2 ^ k = 1`, or `1 ≤ k` and `2 ^ k % 2 = 0`. -/
theorem two_pow_eq_one_or_mod_two_eq_zero (k : ℕ) :
    (k = 0 ∧ 2 ^ k = 1) ∨ (1 ≤ k ∧ 2 ^ k % 2 = 0) := by
  rcases k with _ | k
  · exact Or.inl ⟨rfl, rfl⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.pow_succ]
    omega


/-- Parity dichotomy for primes: either `p = 2`, or `3 ≤ p` and `p` is odd. -/
theorem prime_eq_two_or_three_le_and_odd {p : ℕ} (hp : p.Prime) :
    p = 2 ∨ (3 ≤ p ∧ p % 2 = 1) := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · exact Or.inl rfl
  · have hp2 : 2 ≤ p := hp.two_le
    exact Or.inr ⟨by omega, hodd⟩


/-- For an odd integer `n`, `n = 2 + 2 ^ k + 2 ^ l` holds if and only if one exponent is `0`
and the other exponent is `m ≥ 1` with `n = 2 ^ m + 3`. -/
theorem odd_eq_two_add_two_pows_iff {n k l : ℕ} (hn : Odd n) :
    n = 2 + 2 ^ k + 2 ^ l ↔
      (k = 0 ∧ 1 ≤ l ∧ n = 2 ^ l + 3) ∨ (1 ≤ k ∧ l = 0 ∧ n = 2 ^ k + 3) := by
  rcases hn with ⟨t, rfl⟩
  rcases two_pow_eq_one_or_mod_two_eq_zero k with ⟨rfl, hk⟩ | ⟨hk1, hk⟩ <;>
    rcases two_pow_eq_one_or_mod_two_eq_zero l with ⟨rfl, hl⟩ | ⟨hl1, hl⟩
  · constructor <;> omega
  · constructor
    · intro h
      exact Or.inl ⟨rfl, hl1, by omega⟩
    · rintro (⟨-, -, h⟩ | ⟨hk_pos, -, -⟩) <;> omega
  · constructor
    · intro h
      exact Or.inr ⟨hk1, rfl, by omega⟩
    · rintro (⟨-, hl_pos, -⟩ | ⟨-, -, h⟩) <;> omega
  · constructor <;> omega


/-- For an odd integer `n` and an odd prime `p ≥ 3`, `n = p + 2 ^ k + 2 ^ l` forces the exponents
`k, l` to either both be `0` (`n = p + 2` and `(n - 2).Prime`) or both be positive (`1 ≤ k ∧ 1 ≤ l`). -/
theorem odd_eq_odd_prime_add_two_pows_cases {n p k l : ℕ}
    (hn : Odd n) (hp : p.Prime) (hp3 : 3 ≤ p) (h : n = p + 2 ^ k + 2 ^ l) :
    (k = 0 ∧ l = 0 ∧ n = p + 2 ∧ (n - 2).Prime) ∨
      (1 ≤ k ∧ 1 ≤ l ∧ 2 ^ k + 2 ^ l < n ∧ (n - 2 ^ k - 2 ^ l).Prime) := by
  rcases hn with ⟨t, rfl⟩
  rcases prime_eq_two_or_three_le_and_odd hp with rfl | ⟨-, hp_odd⟩
  · omega
  · rcases two_pow_eq_one_or_mod_two_eq_zero k with ⟨rfl, hk⟩ | ⟨hk1, hk⟩ <;>
      rcases two_pow_eq_one_or_mod_two_eq_zero l with ⟨rfl, hl⟩ | ⟨hl1, hl⟩
    · left
      refine ⟨rfl, rfl, by omega, ?_⟩
      have hsub : 2 * t + 1 - 2 = p := by omega
      rw [hsub]
      exact hp
    · omega
    · omega
    · right
      refine ⟨hk1, hl1, by omega, ?_⟩
      have hsub : 2 * t + 1 - 2 ^ k - 2 ^ l = p := by omega
      rw [hsub]
      exact hp


/-- Fundamental parity trichotomy for any representation `n = p + 2 ^ k + 2 ^ l` of an odd `n`
with `p` prime:
(a) `p = 2` and `{k, l} = {0, m}` with `m ≥ 1`, so `n = 2 ^ m + 3` (`n - 3 = 2 ^ m`);
(b) `p ≥ 3` is an odd prime and `k = 0, l = 0`, so `n = p + 2` and `(n - 2).Prime`; or
(c) `p ≥ 3` is an odd prime and `1 ≤ k ∧ 1 ≤ l`, so `n = p + 2 ^ k + 2 ^ l` with positive exponents. -/
theorem odd_eq_prime_add_two_pows_trichotomy {n p k l : ℕ}
    (hn : Odd n) (hp : p.Prime) (h : n = p + 2 ^ k + 2 ^ l) :
    (p = 2 ∧ ∃ m : ℕ, 1 ≤ m ∧ ((k = 0 ∧ l = m) ∨ (k = m ∧ l = 0)) ∧
      n = 2 ^ m + 3 ∧ n - 3 = 2 ^ m) ∨
    (3 ≤ p ∧ k = 0 ∧ l = 0 ∧ n = p + 2 ∧ (n - 2).Prime) ∨
    (3 ≤ p ∧ 1 ≤ k ∧ 1 ≤ l ∧ 2 ^ k + 2 ^ l < n ∧
      n = p + 2 ^ k + 2 ^ l ∧ (n - 2 ^ k - 2 ^ l).Prime) := by
  rcases prime_eq_two_or_three_le_and_odd hp with rfl | ⟨hp3, -⟩
  · left
    refine ⟨rfl, ?_⟩
    rcases (odd_eq_two_add_two_pows_iff hn).mp h with ⟨rfl, hl1, hn_eq⟩ | ⟨hk1, rfl, hn_eq⟩
    · refine ⟨l, hl1, Or.inl ⟨rfl, rfl⟩, hn_eq, ?_⟩
      rw [hn_eq, Nat.add_sub_cancel]
    · refine ⟨k, hk1, Or.inr ⟨rfl, rfl⟩, hn_eq, ?_⟩
      rw [hn_eq, Nat.add_sub_cancel]
  · rcases odd_eq_odd_prime_add_two_pows_cases hn hp hp3 h with
      ⟨rfl, rfl, hn_eq, hsub_p⟩ | ⟨hk1, hl1, hlt, hsub_p⟩
    · exact Or.inr (Or.inl ⟨hp3, rfl, rfl, hn_eq, hsub_p⟩)
    · exact Or.inr (Or.inr ⟨hp3, hk1, hl1, hlt, h, hsub_p⟩)


/-- Any integer of the form `n = 2 ^ m + 3` lies in `IsPrimePlusTwoPowers` (`2 + 2 ^ 0 + 2 ^ m`). -/
theorem isPrimePlusTwoPowers_of_eq_two_pow_add_three {n m : ℕ} (h : n = 2 ^ m + 3) :
    IsPrimePlusTwoPowers n :=
  ⟨2, 0, m, Nat.prime_two, by omega⟩


/-- Any integer `n` with `(n - 2).Prime` lies in `IsPrimePlusTwoPowers` (`(n - 2) + 2 ^ 0 + 2 ^ 0`). -/
theorem isPrimePlusTwoPowers_of_sub_two_prime {n : ℕ} (hp : (n - 2).Prime) :
    IsPrimePlusTwoPowers n := by
  have hp2 : 2 ≤ n - 2 := hp.two_le
  exact ⟨n - 2, 0, 0, hp, by omega⟩


/-- Any integer `n` with `2 ^ k + 2 ^ l ≤ n` and `(n - 2 ^ k - 2 ^ l).Prime` lies in `IsPrimePlusTwoPowers`. -/
theorem isPrimePlusTwoPowers_of_sub_two_pows_prime {n k l : ℕ}
    (hle : 2 ^ k + 2 ^ l ≤ n) (hp : (n - 2 ^ k - 2 ^ l).Prime) :
    IsPrimePlusTwoPowers n :=
  ⟨n - 2 ^ k - 2 ^ l, k, l, hp, by omega⟩


/-- Exact characterization of `IsPrimePlusTwoPowers n` for odd `n` via the three parity branches. -/
theorem isPrimePlusTwoPowers_odd_iff_three_cases {n : ℕ} (hn : Odd n) :
    IsPrimePlusTwoPowers n ↔
      (∃ m : ℕ, 1 ≤ m ∧ n = 2 ^ m + 3) ∨
      (n - 2).Prime ∨
      (∃ k l : ℕ, 1 ≤ k ∧ 1 ≤ l ∧ 2 ^ k + 2 ^ l < n ∧ (n - 2 ^ k - 2 ^ l).Prime) := by
  constructor
  · rintro ⟨p, k, l, hp, h⟩
    rcases odd_eq_prime_add_two_pows_trichotomy hn hp h with
      ⟨-, m, hm1, -, hn_eq, -⟩ | ⟨-, -, -, -, hsub2⟩ | ⟨-, hk1, hl1, hlt, -, hsub⟩
    · exact Or.inl ⟨m, hm1, hn_eq⟩
    · exact Or.inr (Or.inl hsub2)
    · exact Or.inr (Or.inr ⟨k, l, hk1, hl1, hlt, hsub⟩)
  · rintro (⟨m, -, hn_eq⟩ | hsub2 | ⟨k, l, -, -, hlt, hsub⟩)
    · exact isPrimePlusTwoPowers_of_eq_two_pow_add_three hn_eq
    · exact isPrimePlusTwoPowers_of_sub_two_prime hsub2
    · exact isPrimePlusTwoPowers_of_sub_two_pows_prime (by omega) hsub


/-- Exact three-obstruction characterization of `Erdos9A` for odd `n`:
an odd integer `n` belongs to `Erdos9A` if and only if
(1) `∀ m ≥ 1, n ≠ 2 ^ m + 3`,
(2) `¬ (n - 2).Prime`, and
(3) `∀ k ≥ 1, ∀ l ≥ 1, 2 ^ k + 2 ^ l < n → ¬ (n - 2 ^ k - 2 ^ l).Prime`. -/
theorem mem_erdos9A_iff_three_obstructions {n : ℕ} (hn : Odd n) :
    n ∈ Erdos9A ↔
      (∀ m : ℕ, 1 ≤ m → n ≠ 2 ^ m + 3) ∧
      ¬ (n - 2).Prime ∧
      (∀ k l : ℕ, 1 ≤ k → 1 ≤ l → 2 ^ k + 2 ^ l < n → ¬ (n - 2 ^ k - 2 ^ l).Prime) := by
  unfold Erdos9A
  simp only [Set.mem_setOf_eq, isPrimePlusTwoPowers_odd_iff_three_cases hn]
  constructor
  · rintro ⟨-, hnot⟩
    refine ⟨?_, ?_, ?_⟩
    · intro m hm1 h
      exact hnot (Or.inl ⟨m, hm1, h⟩)
    · intro hp
      exact hnot (Or.inr (Or.inl hp))
    · intro k l hk1 hl1 hlt hp
      exact hnot (Or.inr (Or.inr ⟨k, l, hk1, hl1, hlt, hp⟩))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hn, ?_⟩
    rintro (⟨m, hm1, hm_eq⟩ | hp2 | ⟨k, l, hk1, hl1, hlt, hp⟩)
    · exact h1 m hm1 hm_eq
    · exact h2 hp2
    · exact h3 k l hk1 hl1 hlt hp


/-- Executable boolean decision procedure for `IsPrimePlusTwoPowers n`. -/
def checkIsPrimePlusTwoPowers (n : ℕ) : Bool :=
  let B := Nat.log 2 n + 1
  (List.range B).any fun k =>
    (List.range (k + 1)).any fun l =>
      decide (2 ^ k + 2 ^ l ≤ n) && decide ((n - 2 ^ k - 2 ^ l).Prime)

/-- Executable boolean decision procedure for membership in `Erdos9A`. -/
def checkErdos9A (n : ℕ) : Bool :=
  (n % 2 == 1) && !checkIsPrimePlusTwoPowers n

/-- Soundness and completeness of `checkIsPrimePlusTwoPowers`. -/
theorem checkIsPrimePlusTwoPowers_eq_true_iff (n : ℕ) :
    checkIsPrimePlusTwoPowers n = true ↔ IsPrimePlusTwoPowers n := by
  unfold checkIsPrimePlusTwoPowers IsPrimePlusTwoPowers
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, -, l, -, hle, hp⟩
    exact ⟨n - 2 ^ k - 2 ^ l, k, l, hp, by omega⟩
  · rintro ⟨p, k, l, hp, rfl⟩
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hl1 : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    rcases le_total l k with hlk | hkl
    · have hk_le : 2 ^ k ≤ p + 2 ^ k + 2 ^ l := by omega
      have hk_log : k ≤ Nat.log 2 (p + 2 ^ k + 2 ^ l) :=
        Nat.le_log_of_pow_le (by decide) hk_le
      refine ⟨k, by omega, l, by omega, by omega, ?_⟩
      have hsub : p + 2 ^ k + 2 ^ l - 2 ^ k - 2 ^ l = p := by omega
      rw [hsub]
      exact hp
    · have hl_le : 2 ^ l ≤ p + 2 ^ k + 2 ^ l := by omega
      have hl_log : l ≤ Nat.log 2 (p + 2 ^ k + 2 ^ l) :=
        Nat.le_log_of_pow_le (by decide) hl_le
      refine ⟨l, by omega, k, by omega, by omega, ?_⟩
      have hsub : p + 2 ^ k + 2 ^ l - 2 ^ l - 2 ^ k = p := by omega
      rw [hsub]
      exact hp


/-- Soundness and completeness of `checkErdos9A`. -/
theorem checkErdos9A_eq_true_iff (n : ℕ) :
    checkErdos9A n = true ↔ n ∈ Erdos9A := by
  unfold checkErdos9A Erdos9A
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Set.mem_setOf_eq,
    ← Bool.not_eq_true, checkIsPrimePlusTwoPowers_eq_true_iff, Nat.odd_iff]


set_option maxRecDepth 200000 in
/-- Kernel-checked boolean verification that `1` and `3` are the only `n ≤ 200`
with `checkErdos9A n = true`. -/
theorem checkErdos9A_le_200_iff :
    ∀ n ≤ 200, (checkErdos9A n = true ↔ (n = 1 ∨ n = 3)) := by
  decide


/-- For every `n ≤ 200`, `n ∈ Erdos9A` if and only if `n = 1` or `n = 3`. -/
theorem mem_erdos9A_iff_of_le_200 {n : ℕ} (hn : n ≤ 200) :
    n ∈ Erdos9A ↔ n = 1 ∨ n = 3 := by
  rw [← checkErdos9A_eq_true_iff]
  exact checkErdos9A_le_200_iff n hn


/-- Exact `Finset` classification of `Erdos9A` up to `200`:
filtering `Finset.range 201` by `checkErdos9A` yields `{1, 3}`. -/
theorem erdos9A_filter_range_201 :
    (Finset.range 201).filter (fun n => checkErdos9A n = true) = {1, 3} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hn, hcheck⟩
    exact (checkErdos9A_le_200_iff n (by omega)).mp hcheck
  · rintro (rfl | rfl)
    · exact ⟨by omega, (checkErdos9A_le_200_iff 1 (by omega)).mpr (Or.inl rfl)⟩
    · exact ⟨by omega, (checkErdos9A_le_200_iff 3 (by omega)).mpr (Or.inr rfl)⟩


/-- Exact set classification `{n ≤ 200 | n ∈ Erdos9A} = {1, 3}`. -/
theorem erdos9A_le_200_eq_pair :
    {n : ℕ | n ≤ 200 ∧ n ∈ Erdos9A} = ({1, 3} : Set ℕ) := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, hmem⟩
    exact (mem_erdos9A_iff_of_le_200 hn).mp hmem
  · rintro (rfl | rfl)
    · exact ⟨by omega, (mem_erdos9A_iff_of_le_200 (by omega)).mpr (Or.inl rfl)⟩
    · exact ⟨by omega, (mem_erdos9A_iff_of_le_200 (by omega)).mpr (Or.inr rfl)⟩


end Erdos9


/-!
# Erdős Problem 9: Crocker's (1971) Fermat-Number Divisibility and Covering Reductions

Develops the Crocker covering and Fermat-factor machinery for Erdős Problem 9:
1. Formalizes the positive-exponent variant `Erdos9APos`, proves `Erdos9A ⊆ Erdos9APos`
   with the strict separation witness `5 ∈ Erdos9APos \ Erdos9A`, and proves the exact
   equivalence bridging `Erdos9A` and `Erdos9APos` via the two boundary obstructions
   `∀ m ≥ 1, n ≠ 2 ^ m + 3` and `¬ (n - 2).Prime`.
2. Proves the diagonal (`k = l`) covering-system reduction for `n - 2 ^ k - 2 ^ k = n - 2 ^ (k + 1)`
   showing how any finite covering set of divisors forces `n - 2 ^ k - 2 ^ k` to be composite
   for all `k : ℕ`.
3. Proves Crocker's (1971) universal Fermat-number divisibility theorems for off-diagonal
   exponent pairs (`k ≠ l`): for all `r, m : ℕ`, `(2 ^ (2 ^ r) + 1) ∣ (2 ^ (2 ^ r * (2 * m + 1)) + 1)`,
   and hence for all `k, r, m : ℕ` with `l = k + 2 ^ r * (2 * m + 1)` (equivalently
   `padicValNat 2 (l - k) = r` for `k < l`), `(2 ^ (2 ^ r) + 1) ∣ (2 ^ k + 2 ^ l)`.
   Consequently, any divisor `q` of `F_r = 2 ^ (2 ^ r) + 1` that divides `n` automatically
   divides `n - 2 ^ k - 2 ^ l` for every pair `(k, l)` with `2`-adic distance valuation `r`,
   and any divisor `q` of `F_s` with `s < r` that divides the diagonal `n - 2 ^ (k + 1)`
   also divides the off-diagonal difference `n - 2 ^ k - 2 ^ (k + 2 ^ r * u)`.
-/

namespace Erdos9

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## Section 1: Positive-Exponent Variant `Erdos9APos` and Exact Bridge to `Erdos9A` -/

/-- `IsPrimePlusTwoPosPowers n` holds when `n = p + 2 ^ k + 2 ^ l` for some prime `p`
and strictly positive exponents `k, l ≥ 1`. -/
def IsPrimePlusTwoPosPowers (n : ℕ) : Prop :=
  ∃ p k l : ℕ, Nat.Prime p ∧ 0 < k ∧ 0 < l ∧ n = p + 2 ^ k + 2 ^ l

/-- The positive-exponent variant of `Erdos9A`: odd integers not expressible as
`p + 2 ^ k + 2 ^ l` with `p` prime and `k, l ≥ 1`. -/
def Erdos9APos : Set ℕ :=
  { n | Odd n ∧ ¬ ∃ p k l : ℕ, Nat.Prime p ∧ 0 < k ∧ 0 < l ∧ n = p + 2 ^ k + 2 ^ l }

/-- `Erdos9APos` is the set of odd integers not satisfying `IsPrimePlusTwoPosPowers`. -/
theorem erdos9APos_eq_setOf :
    Erdos9APos = { n | Odd n ∧ ¬ IsPrimePlusTwoPosPowers n } :=
  rfl


/-- Every positive-exponent representation `n = p + 2 ^ k + 2 ^ l` (`k, l ≥ 1`) is in particular
a representation with `k, l ≥ 0`. -/
theorem isPrimePlusTwoPosPowers_imp_isPrimePlusTwoPowers {n : ℕ}
    (h : IsPrimePlusTwoPosPowers n) : IsPrimePlusTwoPowers n := by
  rcases h with ⟨p, k, l, hp, -, -, hn⟩
  exact ⟨p, k, l, hp, hn⟩


/-- Inclusion of the unrestricted exceptional set into the positive-exponent exceptional set:
`Erdos9A ⊆ Erdos9APos`. -/
theorem erdos9A_subset_erdos9APos : Erdos9A ⊆ Erdos9APos := by
  rintro n ⟨hn_odd, hnot⟩
  exact ⟨hn_odd, fun hpos => hnot (isPrimePlusTwoPosPowers_imp_isPrimePlusTwoPowers hpos)⟩


/-- Every odd integer expressible as `p + 2 ^ k + 2 ^ l` with `p` prime and `k, l ≥ 1`
is at least `7` (since `p ≥ 3` and `2 ^ k, 2 ^ l ≥ 2`). -/
theorem seven_le_of_odd_isPrimePlusTwoPosPowers {n : ℕ}
    (hn : Odd n) (h : IsPrimePlusTwoPosPowers n) : 7 ≤ n := by
  rcases h with ⟨p, k, l, hp, hk, hl, heq⟩
  rcases odd_eq_prime_add_two_pows_trichotomy hn hp heq with
    ⟨-, m, -, ⟨⟨rfl, -⟩ | ⟨-, rfl⟩⟩, -, -⟩ | ⟨-, rfl, rfl, -, -⟩ | ⟨hp3, hk1, hl1, -, -, -⟩
  · omega
  · omega
  · omega
  · have hk2 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
    have hl2 : 2 ^ 1 ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) hl1
    omega


/-- No odd integer strictly less than `7` satisfies `IsPrimePlusTwoPosPowers`. -/
theorem not_isPrimePlusTwoPosPowers_of_odd_lt_seven {n : ℕ}
    (hn : Odd n) (hlt : n < 7) : ¬ IsPrimePlusTwoPosPowers n := by
  intro h
  have h7 := seven_le_of_odd_isPrimePlusTwoPosPowers hn h
  omega


/-- `1` belongs to `Erdos9APos`. -/
theorem erdos9APos_contains_one : 1 ∈ Erdos9APos :=
  erdos9A_subset_erdos9APos erdos9A_contains_one


/-- `3` belongs to `Erdos9APos`. -/
theorem erdos9APos_contains_three : 3 ∈ Erdos9APos :=
  erdos9A_subset_erdos9APos erdos9A_contains_three


/-- `5` belongs to `Erdos9APos` because `p + 2 ^ k + 2 ^ l ≥ 7` for odd `p + 2 ^ k + 2 ^ l`
with `k, l ≥ 1`. -/
theorem erdos9APos_contains_five : 5 ∈ Erdos9APos :=
  ⟨by decide, not_isPrimePlusTwoPosPowers_of_odd_lt_seven (by decide) (by decide)⟩


/-- `5` separates `Erdos9APos` from `Erdos9A` (`5 ∈ Erdos9APos \ Erdos9A`), since
`5 = 3 + 2 ^ 0 + 2 ^ 0` requires the zero-exponent boundary case. -/
theorem five_mem_erdos9APos_diff_erdos9A : 5 ∈ Erdos9APos \ Erdos9A :=
  ⟨erdos9APos_contains_five, erdos9A_not_contains_five⟩


/-- Characterization of `IsPrimePlusTwoPosPowers n` via prime differences `n - 2 ^ k - 2 ^ l`. -/
theorem isPrimePlusTwoPosPowers_iff (n : ℕ) :
    IsPrimePlusTwoPosPowers n ↔
      ∃ k l : ℕ, 1 ≤ k ∧ 1 ≤ l ∧ 2 ^ k + 2 ^ l < n ∧ (n - 2 ^ k - 2 ^ l).Prime := by
  constructor
  · rintro ⟨p, k, l, hp, hk, hl, heq⟩
    have hp2 : 2 ≤ p := hp.two_le
    refine ⟨k, l, hk, hl, by omega, ?_⟩
    have hsub : n - 2 ^ k - 2 ^ l = p := by omega
    rw [hsub]
    exact hp
  · rintro ⟨k, l, hk, hl, hlt, hp⟩
    exact ⟨n - 2 ^ k - 2 ^ l, k, l, hp, hk, hl, by omega⟩


/-- For an odd integer `n`, `n ∈ Erdos9APos` if and only if `n - 2 ^ k - 2 ^ l` is never prime
for positive exponents `k, l ≥ 1` with `2 ^ k + 2 ^ l < n`. -/
theorem mem_erdos9APos_iff {n : ℕ} (hn : Odd n) :
    n ∈ Erdos9APos ↔
      ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → 2 ^ k + 2 ^ l < n → ¬ (n - 2 ^ k - 2 ^ l).Prime := by
  rw [erdos9APos_eq_setOf, Set.mem_setOf_eq, isPrimePlusTwoPosPowers_iff]
  constructor
  · rintro ⟨-, hnot⟩ k l hk hl hlt hp
    exact hnot ⟨k, l, hk, hl, hlt, hp⟩
  · intro hall
    refine ⟨hn, ?_⟩
    rintro ⟨k, l, hk, hl, hlt, hp⟩
    exact hall k l hk hl hlt hp


/-- Exact bridge between `Erdos9A` and `Erdos9APos`: for every `n : ℕ`, `n ∈ Erdos9A`
if and only if `n ∈ Erdos9APos` and `n` avoids the two `0`-exponent boundary families
`n = 2 ^ m + 3` (`m ≥ 1`) and `(n - 2).Prime`. -/
theorem mem_erdos9A_iff_mem_erdos9APos_and_boundary_obstructions (n : ℕ) :
    n ∈ Erdos9A ↔
      n ∈ Erdos9APos ∧ (∀ m : ℕ, 1 ≤ m → n ≠ 2 ^ m + 3) ∧ ¬ (n - 2).Prime := by
  by_cases hn : Odd n
  · rw [mem_erdos9A_iff_three_obstructions hn, mem_erdos9APos_iff hn]
    tauto
  · constructor
    · rintro ⟨hodd, -⟩
      exact False.elim (hn hodd)
    · rintro ⟨⟨hodd, -⟩, -, -⟩
      exact False.elim (hn hodd)


/-- Executable boolean decision procedure for `IsPrimePlusTwoPosPowers n`. -/
def checkIsPrimePlusTwoPosPowers (n : ℕ) : Bool :=
  let B := Nat.log 2 n + 1
  (List.range B).any fun k =>
    (List.range (k + 1)).any fun l =>
      decide (1 ≤ k ∧ 1 ≤ l ∧ 2 ^ k + 2 ^ l ≤ n) && decide ((n - 2 ^ k - 2 ^ l).Prime)

/-- Executable boolean decision procedure for membership in `Erdos9APos`. -/
def checkErdos9APos (n : ℕ) : Bool :=
  (n % 2 == 1) && !checkIsPrimePlusTwoPosPowers n

/-- Soundness and completeness of `checkIsPrimePlusTwoPosPowers`. -/
theorem checkIsPrimePlusTwoPosPowers_eq_true_iff (n : ℕ) :
    checkIsPrimePlusTwoPosPowers n = true ↔ IsPrimePlusTwoPosPowers n := by
  unfold checkIsPrimePlusTwoPosPowers IsPrimePlusTwoPosPowers
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, -, l, -, ⟨hk1, hl1, hle⟩, hp⟩
    exact ⟨n - 2 ^ k - 2 ^ l, k, l, hp, hk1, hl1, by omega⟩
  · rintro ⟨p, k, l, hp, hk1, hl1, rfl⟩
    have hk_pow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hl_pow : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    rcases le_total l k with hlk | hkl
    · have hk_le : 2 ^ k ≤ p + 2 ^ k + 2 ^ l := by omega
      have hk_log : k ≤ Nat.log 2 (p + 2 ^ k + 2 ^ l) :=
        Nat.le_log_of_pow_le (by decide) hk_le
      refine ⟨k, by omega, l, by omega, ⟨hk1, hl1, by omega⟩, ?_⟩
      have hsub : p + 2 ^ k + 2 ^ l - 2 ^ k - 2 ^ l = p := by omega
      rw [hsub]
      exact hp
    · have hl_le : 2 ^ l ≤ p + 2 ^ k + 2 ^ l := by omega
      have hl_log : l ≤ Nat.log 2 (p + 2 ^ k + 2 ^ l) :=
        Nat.le_log_of_pow_le (by decide) hl_le
      refine ⟨l, by omega, k, by omega, ⟨hl1, hk1, by omega⟩, ?_⟩
      have hsub : p + 2 ^ k + 2 ^ l - 2 ^ l - 2 ^ k = p := by omega
      rw [hsub]
      exact hp


/-- Soundness and completeness of `checkErdos9APos`. -/
theorem checkErdos9APos_eq_true_iff (n : ℕ) :
    checkErdos9APos n = true ↔ n ∈ Erdos9APos := by
  rw [erdos9APos_eq_setOf]
  unfold checkErdos9APos
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Set.mem_setOf_eq,
    ← Bool.not_eq_true, checkIsPrimePlusTwoPosPowers_eq_true_iff, Nat.odd_iff]


set_option maxRecDepth 200000 in
/-- Kernel-checked boolean verification that `1`, `3`, and `5` are the only `n ≤ 200`
with `checkErdos9APos n = true`. -/
theorem checkErdos9APos_le_200_iff :
    ∀ n ≤ 200, (checkErdos9APos n = true ↔ (n = 1 ∨ n = 3 ∨ n = 5)) := by
  decide


/-- For every `n ≤ 200`, `n ∈ Erdos9APos` if and only if `n = 1`, `n = 3`, or `n = 5`. -/
theorem mem_erdos9APos_iff_of_le_200 {n : ℕ} (hn : n ≤ 200) :
    n ∈ Erdos9APos ↔ n = 1 ∨ n = 3 ∨ n = 5 := by
  rw [← checkErdos9APos_eq_true_iff]
  exact checkErdos9APos_le_200_iff n hn


/-- Exact set classification `{n ≤ 200 | n ∈ Erdos9APos} = {1, 3, 5}`. -/
theorem erdos9APos_le_200_eq_triple :
    {n : ℕ | n ≤ 200 ∧ n ∈ Erdos9APos} = ({1, 3, 5} : Set ℕ) := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, hmem⟩
    exact (mem_erdos9APos_iff_of_le_200 hn).mp hmem
  · rintro (rfl | rfl | rfl)
    · exact ⟨by omega, (mem_erdos9APos_iff_of_le_200 (by omega)).mpr (Or.inl rfl)⟩
    · exact ⟨by omega, (mem_erdos9APos_iff_of_le_200 (by omega)).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨by omega, (mem_erdos9APos_iff_of_le_200 (by omega)).mpr (Or.inr (Or.inr rfl))⟩


/-! ## Section 2: Diagonal (`k = l`) Reduction and Covering-System Exclusions -/

/-- Equal powers of `2` combine into the next power of `2`: `2 ^ k + 2 ^ k = 2 ^ (k + 1)`. -/
theorem two_pow_add_self (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [Nat.pow_succ]
  omega


/-- Along the diagonal `k = l`, `n - 2 ^ k - 2 ^ k` reduces to `n - 2 ^ (k + 1)`. -/
theorem sub_two_pow_sub_self (n k : ℕ) : n - 2 ^ k - 2 ^ k = n - 2 ^ (k + 1) := by
  rw [Nat.sub_sub, two_pow_add_self]


/-- Composite certificate from a proper divisor `1 < q < m` with `q ∣ m`. -/
theorem not_prime_of_dvd_of_lt {m q : ℕ} (hq1 : 1 < q) (hqm : q < m) (hdvd : q ∣ m) :
    ¬ m.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd q hdvd with rfl | rfl <;> omega


/-- Universal diagonal covering reduction: if a finite covering set `P₁` supplies a proper
divisor `q ∈ P₁` of `n - 2 ^ (k + 1)` whenever `2 ^ (k + 1) < n`, then `n - 2 ^ k - 2 ^ k`
is never prime for any `k : ℕ`. -/
theorem diagonal_composite_of_covering_set {n : ℕ} (P₁ : Finset ℕ)
    (hcover : ∀ k : ℕ, 2 ^ (k + 1) < n →
      ∃ q ∈ P₁, 1 < q ∧ q < n - 2 ^ (k + 1) ∧ q ∣ (n - 2 ^ (k + 1))) :
    ∀ k : ℕ, ¬ (n - 2 ^ k - 2 ^ k).Prime := by
  intro k
  rw [sub_two_pow_sub_self]
  by_cases hlt : 2 ^ (k + 1) < n
  · rcases hcover k hlt with ⟨q, -, hq1, hqm, hdvd⟩
    exact not_prime_of_dvd_of_lt hq1 hqm hdvd
  · have hzero : n - 2 ^ (k + 1) = 0 := by omega
    rw [hzero]
    exact Nat.not_prime_zero


/-- Universal diagonal exclusion for `n = p + 2 ^ k + 2 ^ k` from a covering set `P₁`. -/
theorem not_eq_prime_add_two_pow_diag_of_covering_set {n : ℕ} (P₁ : Finset ℕ)
    (hcover : ∀ k : ℕ, 2 ^ (k + 1) < n →
      ∃ q ∈ P₁, 1 < q ∧ q < n - 2 ^ (k + 1) ∧ q ∣ (n - 2 ^ (k + 1))) :
    ∀ p k : ℕ, p.Prime → n ≠ p + 2 ^ k + 2 ^ k := by
  intro p k hp heq
  have hsub : n - 2 ^ k - 2 ^ k = p := by omega
  apply diagonal_composite_of_covering_set P₁ hcover k
  rw [hsub]
  exact hp


/-! ## Section 3: Crocker's (1971) Fermat-Number Divisibility & Off-Diagonal Reductions -/

/-- The `r`-th Fermat number `F_r = 2 ^ (2 ^ r) + 1`. -/
def fermatNumber (r : ℕ) : ℕ := 2 ^ (2 ^ r) + 1

/-- Every Fermat number is at least `3`. -/
theorem three_le_fermatNumber (r : ℕ) : 3 ≤ fermatNumber r := by
  unfold fermatNumber
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h2 : 2 ^ 1 ≤ 2 ^ (2 ^ r) := Nat.pow_le_pow_right (by decide) h1
  omega


/-- Every Fermat number is strictly greater than `1`. -/
theorem one_lt_fermatNumber (r : ℕ) : 1 < fermatNumber r := by
  have h3 := three_le_fermatNumber r
  omega


/-- Every Fermat number is odd. -/
theorem odd_fermatNumber (r : ℕ) : Odd (fermatNumber r) := by
  unfold fermatNumber
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rcases two_pow_eq_one_or_mod_two_eq_zero (2 ^ r) with ⟨h0, -⟩ | ⟨-, hmod⟩
  · omega
  · rw [Nat.odd_iff]
    omega


/-- Universal odd-power sum divisibility: for all `a, m : ℕ`, `(a + 1) ∣ (a ^ (2 * m + 1) + 1)`. -/
theorem add_one_dvd_pow_two_mul_add_one_add_one (a m : ℕ) :
    a + 1 ∣ a ^ (2 * m + 1) + 1 := by
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  simpa using Odd.nat_add_dvd_pow_add_pow a 1 hodd


/-- Crocker's Fermat divisibility lemma: for all `r, m : ℕ`,
`(2 ^ (2 ^ r) + 1) ∣ (2 ^ (2 ^ r * (2 * m + 1)) + 1)`. -/
theorem fermatNumber_dvd_two_pow_two_pow_mul_two_mul_add_one_add_one (r m : ℕ) :
    (2 ^ (2 ^ r) + 1) ∣ (2 ^ (2 ^ r * (2 * m + 1)) + 1) := by
  rw [Nat.pow_mul]
  exact add_one_dvd_pow_two_mul_add_one_add_one (2 ^ (2 ^ r)) m


/-- Odd-multiplier formulation of Crocker's Fermat divisibility: for every `r : ℕ`
and every odd `u : ℕ`, `fermatNumber r ∣ (2 ^ (2 ^ r * u) + 1)`. -/
theorem fermatNumber_dvd_two_pow_two_pow_mul_odd_add_one (r : ℕ) {u : ℕ} (hu : Odd u) :
    fermatNumber r ∣ 2 ^ (2 ^ r * u) + 1 := by
  rcases hu with ⟨m, rfl⟩
  exact fermatNumber_dvd_two_pow_two_pow_mul_two_mul_add_one_add_one r m


/-- Factoring `2 ^ k + 2 ^ l` for `k ≤ l`: `2 ^ k + 2 ^ l = 2 ^ k * (2 ^ (l - k) + 1)`. -/
theorem two_pow_add_two_pow_eq_mul_sub {k l : ℕ} (hkl : k ≤ l) :
    2 ^ k + 2 ^ l = 2 ^ k * (2 ^ (l - k) + 1) := by
  have hl : l = k + (l - k) := by omega
  conv_lhs => rw [hl, Nat.pow_add]
  ring


/-- Universal Fermat divisibility for `2 ^ k + 2 ^ l`: for all `k, r, m : ℕ` with
`l = k + 2 ^ r * (2 * m + 1)`, `(2 ^ (2 ^ r) + 1) ∣ (2 ^ k + 2 ^ l)`. -/
theorem fermatNumber_dvd_two_pow_add_two_pow_of_eq (k r m : ℕ) {l : ℕ}
    (hl : l = k + 2 ^ r * (2 * m + 1)) :
    (2 ^ (2 ^ r) + 1) ∣ (2 ^ k + 2 ^ l) := by
  have hkl : k ≤ l := by omega
  have hsub : l - k = 2 ^ r * (2 * m + 1) := by omega
  rw [two_pow_add_two_pow_eq_mul_sub hkl, hsub]
  exact dvd_mul_of_dvd_right
    (fermatNumber_dvd_two_pow_two_pow_mul_two_mul_add_one_add_one r m) (2 ^ k)


/-- Exact `2`-adic valuation of `2 ^ r * u` for odd `u`: `padicValNat 2 (2 ^ r * u) = r`. -/
theorem padicValNat_two_mul_odd (r : ℕ) {u : ℕ} (hu : Odd u) :
    padicValNat 2 (2 ^ r * u) = r := by
  have hu0 : u ≠ 0 := by
    rcases hu with ⟨m, rfl⟩
    omega
  have hnot_dvd : ¬ (2 ∣ u) := by
    rcases hu with ⟨m, rfl⟩
    omega
  rw [padicValNat.mul (by positivity) hu0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hnot_dvd, add_zero]


/-- For `k < l`, `padicValNat 2 (l - k) = r` holds if and only if
`l = k + 2 ^ r * (2 * m + 1)` for some `m : ℕ`. -/
theorem padicValNat_two_sub_eq_iff {k l r : ℕ} (hkl : k < l) :
    padicValNat 2 (l - k) = r ↔ ∃ m : ℕ, l = k + 2 ^ r * (2 * m + 1) := by
  constructor
  · intro hr
    have hne : l - k ≠ 0 := by omega
    rcases Nat.exists_eq_two_pow_mul_odd hne with ⟨r', u, hu, hsub⟩
    have hr_eq : r' = r := by
      rw [← hr, hsub, padicValNat_two_mul_odd r' hu]
    subst hr_eq
    rcases hu with ⟨m, rfl⟩
    exact ⟨m, by omega⟩
  · rintro ⟨m, hl⟩
    have hsub : l - k = 2 ^ r * (2 * m + 1) := by omega
    rw [hsub]
    exact padicValNat_two_mul_odd r ⟨m, rfl⟩


/-- For every `k < l` with `padicValNat 2 (l - k) = r`, the Fermat number `2 ^ (2 ^ r) + 1`
divides `2 ^ k + 2 ^ l`. -/
theorem fermatNumber_dvd_two_pow_add_two_pow_of_padicValNat_sub {k l r : ℕ}
    (hkl : k < l) (hr : padicValNat 2 (l - k) = r) :
    (2 ^ (2 ^ r) + 1) ∣ (2 ^ k + 2 ^ l) := by
  rcases (padicValNat_two_sub_eq_iff hkl).mp hr with ⟨m, hl⟩
  exact fermatNumber_dvd_two_pow_add_two_pow_of_eq k r m hl


/-- Symmetric `2`-adic distance formulation: for every `k ≠ l` with
`padicValNat 2 (Nat.dist k l) = r`, `(2 ^ (2 ^ r) + 1) ∣ (2 ^ k + 2 ^ l)`. -/
theorem fermatNumber_dvd_two_pow_add_two_pow_of_padicValNat_dist {k l r : ℕ}
    (hkl : k ≠ l) (hr : padicValNat 2 (Nat.dist k l) = r) :
    (2 ^ (2 ^ r) + 1) ∣ (2 ^ k + 2 ^ l) := by
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hdist : Nat.dist k l = l - k := Nat.dist_eq_sub_of_le (le_of_lt hlt)
    rw [hdist] at hr
    exact fermatNumber_dvd_two_pow_add_two_pow_of_padicValNat_sub hlt hr
  · have hdist : Nat.dist k l = k - l := Nat.dist_eq_sub_of_le_right (le_of_lt hgt)
    rw [hdist] at hr
    rw [add_comm (2 ^ k) (2 ^ l)]
    exact fermatNumber_dvd_two_pow_add_two_pow_of_padicValNat_sub hgt hr


/-- Consequently, if `q ∣ (2 ^ (2 ^ r) + 1)` and `q ∣ n`, then `q ∣ (n - 2 ^ k - 2 ^ l)`
for all `k, r, m : ℕ` and `l = k + 2 ^ r * (2 * m + 1)`. -/
theorem dvd_sub_two_pows_of_dvd_fermatNumber {n q k r m l : ℕ}
    (hqF : q ∣ 2 ^ (2 ^ r) + 1) (hqn : q ∣ n) (hl : l = k + 2 ^ r * (2 * m + 1)) :
    q ∣ (n - 2 ^ k - 2 ^ l) := by
  rw [Nat.sub_sub]
  exact Nat.dvd_sub hqn (dvd_trans hqF (fermatNumber_dvd_two_pow_add_two_pow_of_eq k r m hl))


/-- Symmetric `2`-adic valuation form of Crocker's divisibility transfer: if `q ∣ (2 ^ (2 ^ r) + 1)`
and `q ∣ n`, then `q ∣ (n - 2 ^ k - 2 ^ l)` for every pair `(k, l)` with `k ≠ l` and
`padicValNat 2 (Nat.dist k l) = r`. -/
theorem dvd_sub_two_pows_of_dvd_fermatNumber_of_padicValNat_dist {n q k l r : ℕ}
    (hkl : k ≠ l) (hr : padicValNat 2 (Nat.dist k l) = r)
    (hqF : q ∣ 2 ^ (2 ^ r) + 1) (hqn : q ∣ n) :
    q ∣ (n - 2 ^ k - 2 ^ l) := by
  rw [Nat.sub_sub]
  exact Nat.dvd_sub hqn
    (dvd_trans hqF (fermatNumber_dvd_two_pow_add_two_pow_of_padicValNat_dist hkl hr))


/-- Composite certificate for off-diagonal differences `n - 2 ^ k - 2 ^ l` via a Fermat divisor `q ∣ F_r`
also dividing `n`. -/
theorem not_prime_sub_two_pows_of_dvd_fermatNumber {n q k l r : ℕ}
    (hq1 : 1 < q) (hkl : k ≠ l) (hr : padicValNat 2 (Nat.dist k l) = r)
    (hqF : q ∣ 2 ^ (2 ^ r) + 1) (hqn : q ∣ n) (hlt : q < n - 2 ^ k - 2 ^ l) :
    ¬ (n - 2 ^ k - 2 ^ l).Prime :=
  not_prime_of_dvd_of_lt hq1 hlt
    (dvd_sub_two_pows_of_dvd_fermatNumber_of_padicValNat_dist hkl hr hqF hqn)


/-- Lower Fermat numbers divide higher power-of-two differences: for all `s < r` and `u : ℕ`,
`(2 ^ (2 ^ s) + 1) ∣ (2 ^ (2 ^ r * u) - 1)`. -/
theorem fermatNumber_dvd_two_pow_two_pow_mul_sub_one {s r : ℕ} (hsr : s < r) (u : ℕ) :
    (2 ^ (2 ^ s) + 1) ∣ (2 ^ (2 ^ r * u) - 1) := by
  have hr : r = (s + 1) + (r - (s + 1)) := by omega
  have hpow : 2 ^ (2 ^ r * u) = ((2 ^ (2 ^ s)) ^ 2) ^ (2 ^ (r - (s + 1)) * u) := by
    rw [← Nat.pow_mul, ← Nat.pow_mul]
    congr 1
    conv_lhs => rw [hr, Nat.pow_add, Nat.pow_succ]
    ring
  rw [hpow]
  have hdvd1 : (2 ^ (2 ^ s)) ^ 2 - 1 ∣ ((2 ^ (2 ^ s)) ^ 2) ^ (2 ^ (r - (s + 1)) * u) - 1 :=
    Nat.sub_one_dvd_pow_sub_one ((2 ^ (2 ^ s)) ^ 2) (2 ^ (r - (s + 1)) * u)
  have hdvd2 : 2 ^ (2 ^ s) + 1 ∣ (2 ^ (2 ^ s)) ^ 2 - 1 := by
    have hsq := Nat.sq_sub_sq (2 ^ (2 ^ s)) 1
    simp only [one_pow] at hsq
    rw [hsq]
    exact dvd_mul_right (2 ^ (2 ^ s) + 1) (2 ^ (2 ^ s) - 1)
  exact dvd_trans hdvd2 hdvd1


/-- Algebraic identity relating off-diagonal `2 ^ k + 2 ^ l` (`k ≤ l`) to the diagonal `2 ^ (k + 1)`:
`2 ^ k + 2 ^ l - 2 ^ (k + 1) = 2 ^ k * (2 ^ (l - k) - 1)`. -/
theorem two_pow_add_two_pow_sub_diag {k l : ℕ} (hkl : k ≤ l) :
    2 ^ k + 2 ^ l - 2 ^ (k + 1) = 2 ^ k * (2 ^ (l - k) - 1) := by
  have hl : l = k + (l - k) := by omega
  have h1 : 1 ≤ 2 ^ (l - k) := Nat.one_le_two_pow
  conv_lhs => rw [hl, Nat.pow_add, Nat.pow_succ]
  rw [Nat.mul_sub_left_distrib, mul_one]
  omega


/-- Crocker's diagonal collapse modulo `F_s` for `s < r`: when `l = k + 2 ^ r * u`,
`(2 ^ (2 ^ s) + 1) ∣ (2 ^ k + 2 ^ l - 2 ^ (k + 1))`. -/
theorem fermatNumber_dvd_off_diag_sub_diag {s r k u l : ℕ}
    (hsr : s < r) (hl : l = k + 2 ^ r * u) :
    (2 ^ (2 ^ s) + 1) ∣ (2 ^ k + 2 ^ l - 2 ^ (k + 1)) := by
  have hkl : k ≤ l := by omega
  have hsub : l - k = 2 ^ r * u := by omega
  rw [two_pow_add_two_pow_sub_diag hkl, hsub]
  exact dvd_mul_of_dvd_right (fermatNumber_dvd_two_pow_two_pow_mul_sub_one hsr u) (2 ^ k)


/-- Consequently, if `s < r`, `l = k + 2 ^ r * u`, `q ∣ (2 ^ (2 ^ s) + 1)`, and `q` divides
the diagonal difference `n - 2 ^ (k + 1)`, then `q` also divides the off-diagonal difference
`n - 2 ^ k - 2 ^ l`. -/
theorem dvd_sub_two_pows_of_dvd_fermatNumber_lt_of_dvd_diag {n q s r k u l : ℕ}
    (hsr : s < r) (hl : l = k + 2 ^ r * u)
    (hle : 2 ^ k + 2 ^ l ≤ n)
    (hqF : q ∣ 2 ^ (2 ^ s) + 1)
    (hq_diag : q ∣ (n - 2 ^ (k + 1))) :
    q ∣ (n - 2 ^ k - 2 ^ l) := by
  have hkl : k ≤ l := by omega
  have hpow_le : 2 ^ k ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) hkl
  have h2k1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hdiff_dvd : q ∣ (2 ^ k + 2 ^ l - 2 ^ (k + 1)) :=
    dvd_trans hqF (fermatNumber_dvd_off_diag_sub_diag hsr hl)
  have heq : n - 2 ^ k - 2 ^ l = (n - 2 ^ (k + 1)) - (2 ^ k + 2 ^ l - 2 ^ (k + 1)) := by
    omega
  rw [heq]
  exact Nat.dvd_sub hq_diag hdiff_dvd


/-- Crocker's combined diagonal + Fermat-split reduction for `Erdos9APos`:
an odd integer `n` belongs to `Erdos9APos` whenever
(1) every diagonal difference `n - 2 ^ (k + 1)` (`k ≥ 1`, `2 ^ (k + 1) < n`) is covered by a
    proper divisor from `P₁`, and
(2) every off-diagonal pair `1 ≤ k < l` with `2 ^ k + 2 ^ l < n` and `r = padicValNat 2 (l - k)`
    is either covered by a Fermat divisor `q ∣ 2 ^ (2 ^ r) + 1` with `q ∣ n` and
    `1 < q < n - 2 ^ k - 2 ^ l`, or is otherwise composite. -/
theorem mem_erdos9APos_of_diagonal_and_fermat_cover {n : ℕ} (hn : Odd n) (P₁ : Finset ℕ)
    (hdiag : ∀ k : ℕ, 2 ^ (k + 1) < n →
      ∃ q ∈ P₁, 1 < q ∧ q < n - 2 ^ (k + 1) ∧ q ∣ (n - 2 ^ (k + 1)))
    (hoff : ∀ k l : ℕ, 1 ≤ k → k < l → 2 ^ k + 2 ^ l < n →
      (∃ q : ℕ, 1 < q ∧ q < n - 2 ^ k - 2 ^ l ∧
        q ∣ (2 ^ (2 ^ (padicValNat 2 (l - k))) + 1) ∧ q ∣ n) ∨
      ¬ (n - 2 ^ k - 2 ^ l).Prime) :
    n ∈ Erdos9APos := by
  rw [mem_erdos9APos_iff hn]
  intro k l hk1 hl1 hlt
  rcases lt_trichotomy k l with hkl | rfl | hlk
  · rcases hoff k l hk1 hkl hlt with ⟨q, hq1, hq_lt, hqF, hqn⟩ | hcomp
    · have hdist : Nat.dist k l = l - k := Nat.dist_eq_sub_of_le (le_of_lt hkl)
      exact not_prime_sub_two_pows_of_dvd_fermatNumber hq1 (ne_of_lt hkl)
        (congrArg (padicValNat 2) hdist) hqF hqn hq_lt
    · exact hcomp
  · exact diagonal_composite_of_covering_set P₁ hdiag k
  · have hlt' : 2 ^ l + 2 ^ k < n := by omega
    have hsub_comm : n - 2 ^ k - 2 ^ l = n - 2 ^ l - 2 ^ k := by omega
    rw [hsub_comm]
    rcases hoff l k hl1 hlk hlt' with ⟨q, hq1, hq_lt, hqF, hqn⟩ | hcomp
    · have hdist : Nat.dist l k = k - l := Nat.dist_eq_sub_of_le (le_of_lt hlk)
      exact not_prime_sub_two_pows_of_dvd_fermatNumber hq1 (ne_of_lt hlk)
        (congrArg (padicValNat 2) hdist) hqF hqn hq_lt
    · exact hcomp


/-- Full Crocker reduction to `Erdos9A`: combining the diagonal + Fermat-split hypotheses for
`Erdos9APos` with the two zero-exponent boundary obstructions yields `n ∈ Erdos9A`. -/
theorem mem_erdos9A_of_diagonal_fermat_and_boundary_cover {n : ℕ} (hn : Odd n) (P₁ : Finset ℕ)
    (hpow3 : ∀ m : ℕ, 1 ≤ m → n ≠ 2 ^ m + 3)
    (hsub2 : ¬ (n - 2).Prime)
    (hdiag : ∀ k : ℕ, 2 ^ (k + 1) < n →
      ∃ q ∈ P₁, 1 < q ∧ q < n - 2 ^ (k + 1) ∧ q ∣ (n - 2 ^ (k + 1)))
    (hoff : ∀ k l : ℕ, 1 ≤ k → k < l → 2 ^ k + 2 ^ l < n →
      (∃ q : ℕ, 1 < q ∧ q < n - 2 ^ k - 2 ^ l ∧
        q ∣ (2 ^ (2 ^ (padicValNat 2 (l - k))) + 1) ∧ q ∣ n) ∨
      ¬ (n - 2 ^ k - 2 ^ l).Prime) :
    n ∈ Erdos9A := by
  rw [mem_erdos9A_iff_mem_erdos9APos_and_boundary_obstructions]
  exact ⟨mem_erdos9APos_of_diagonal_and_fermat_cover hn P₁ hdiag hoff, hpow3, hsub2⟩


end Erdos9


namespace Erdos9

/-! ## Section 1: Universal Mod-16 & Fermat-Factor Off-Diagonal Exclusions (Crocker Lemma II) -/

/-- For every exponent `m : ℕ`, `2 ^ m + 3` is never congruent to `15` modulo `16`. -/
theorem two_pow_add_three_mod_sixteen_ne_fifteen (m : ℕ) :
    (2 ^ m + 3) % 16 ≠ 15 := by
  rcases m with _ | _ | _ | _ | m
  · decide
  · decide
  · decide
  · decide
  · have hstep : m + 1 + 1 + 1 + 1 = m + 4 := by omega
    rw [hstep, Nat.pow_add]
    have h16 : 2 ^ 4 = 16 := by decide
    rw [h16]
    omega


/-- Any integer `n ≡ 15 (mod 16)` avoids the zero-exponent boundary family `2 ^ m + 3` for all `m : ℕ`. -/
theorem ne_two_pow_add_three_of_mod_sixteen_eq_fifteen {n : ℕ} (hn16 : n % 16 = 15) (m : ℕ) :
    n ≠ 2 ^ m + 3 := by
  intro h
  have hmod := two_pow_add_three_mod_sixteen_ne_fifteen m
  omega


/-- Every integer `n ≡ 15 (mod 16)` is odd. -/
theorem odd_of_mod_sixteen_eq_fifteen {n : ℕ} (hn16 : n % 16 = 15) :
    Odd n := by
  rw [Nat.odd_iff]
  omega


/-- Modulo `16`, every Fermat number `fermatNumber r = 2 ^ (2 ^ r) + 1` is `3` (`r = 0`),
`5` (`r = 1`), or `1` (`r ≥ 2`). -/
theorem fermatNumber_mod_sixteen_cases (r : ℕ) :
    fermatNumber r % 16 = 1 ∨ fermatNumber r % 16 = 3 ∨ fermatNumber r % 16 = 5 := by
  rcases r with _ | _ | r
  · right; left; decide
  · right; right; decide
  · left
    unfold fermatNumber
    have h1 : 4 ≤ 2 ^ (r + 2) := by
      rw [Nat.pow_add]
      have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      have : 2 ^ 2 = 4 := by decide
      omega
    have h2 : 2 ^ (2 ^ (r + 2)) = 2 ^ (2 ^ (r + 2) - 4) * 16 := by
      have h16 : (16 : ℕ) = 2 ^ 4 := by decide
      rw [h16, ← Nat.pow_add, Nat.sub_add_cancel h1]
    rw [h2]
    omega


/-- Universal mod-16 exclusion for Crocker's off-diagonal sum `2 ^ k + 2 ^ l + B`:
if `1 ≤ k`, `4 ≤ l`, and `B % 16 ∈ {1, 3, 5}`, then `(2 ^ k + 2 ^ l + B) % 16 ≠ 15`. -/
theorem two_pow_add_two_pow_add_mod_sixteen_ne_fifteen {k l B : ℕ}
    (hk1 : 1 ≤ k) (hl4 : 4 ≤ l)
    (hB16 : B % 16 = 1 ∨ B % 16 = 3 ∨ B % 16 = 5) :
    (2 ^ k + 2 ^ l + B) % 16 ≠ 15 := by
  have hl_mod : 2 ^ l % 16 = 0 := by
    have hl_eq : 2 ^ l = 2 ^ (l - 4) * 16 := by
      have h16 : (16 : ℕ) = 2 ^ 4 := by decide
      rw [h16, ← Nat.pow_add, Nat.sub_add_cancel hl4]
    omega
  have hk_mod : 2 ^ k % 16 = 0 ∨ 2 ^ k % 16 = 2 ∨ 2 ^ k % 16 = 4 ∨ 2 ^ k % 16 = 8 := by
    rcases k with _ | _ | _ | _ | k
    · omega
    · right; left; decide
    · right; right; left; decide
    · right; right; right; decide
    · left
      have hstep : k + 1 + 1 + 1 + 1 = k + 4 := by omega
      rw [hstep, Nat.pow_add]
      have h16 : 2 ^ 4 = 16 := by decide
      omega
  rcases hk_mod with hk0 | hk2 | hk4 | hk8 <;>
    rcases hB16 with hB1 | hB3 | hB5 <;> omega


/-- If `k < l` and `42 ≤ 2 ^ k + 2 ^ l`, then `5 ≤ l` (and in particular `4 ≤ l`). -/
theorem five_le_of_forty_two_le_two_pow_add_two_pow {k l : ℕ}
    (hkl : k < l) (hle : 42 ≤ 2 ^ k + 2 ^ l) :
    5 ≤ l := by
  by_contra hlt
  have hl4 : l ≤ 4 := by omega
  have hk3 : k ≤ 3 := by omega
  have hpow_l : 2 ^ l ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hl4
  have hpow_k : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hk3
  omega


/-- Crocker's off-diagonal inequality (`n - 2 ^ k - 2 ^ l ≠ B`):
if `n % 16 = 15`, `1 ≤ k < l`, `3 ≤ B`, `15 * B ≤ n`, and `B % 16 ∈ {1, 3, 5}`,
then `n - 2 ^ k - 2 ^ l ≠ B`. -/
theorem crocker_off_diagonal_ne_fermat_factor {n k l B : ℕ}
    (hn16 : n % 16 = 15) (hk1 : 1 ≤ k) (hkl : k < l)
    (hB3 : 3 ≤ B) (hBn : 15 * B ≤ n)
    (hB16 : B % 16 = 1 ∨ B % 16 = 3 ∨ B % 16 = 5) :
    n - 2 ^ k - 2 ^ l ≠ B := by
  intro heq
  rw [Nat.sub_sub] at heq
  have hsum_eq : 2 ^ k + 2 ^ l + B = n := by omega
  have h42 : 42 ≤ 2 ^ k + 2 ^ l := by omega
  have hl5 : 5 ≤ l := five_le_of_forty_two_le_two_pow_add_two_pow hkl h42
  have hl4 : 4 ≤ l := by omega
  have hne := two_pow_add_two_pow_add_mod_sixteen_ne_fifteen hk1 hl4 hB16
  rw [hsum_eq] at hne
  exact hne hn16


/-- Crocker's Lemma II (universal off-diagonal compositeness via Fermat factors):
if `n % 16 = 15`, `1 ≤ k < l`, `2 ^ k + 2 ^ l < n`, `padicValNat 2 (l - k) = r`,
`3 ≤ B`, `15 * B ≤ n`, `B % 16 ∈ {1, 3, 5}`, `B ∣ 2 ^ (2 ^ r) + 1`, and `B ∣ n`,
then `n - 2 ^ k - 2 ^ l` is not prime. -/
theorem crocker_off_diagonal_composite_of_fermat_factor {n k l r B : ℕ}
    (hn16 : n % 16 = 15) (hk1 : 1 ≤ k) (hkl : k < l) (hlt : 2 ^ k + 2 ^ l < n)
    (hr : padicValNat 2 (l - k) = r)
    (hB3 : 3 ≤ B) (hBn : 15 * B ≤ n)
    (hB16 : B % 16 = 1 ∨ B % 16 = 3 ∨ B % 16 = 5)
    (hBF : B ∣ 2 ^ (2 ^ r) + 1) (hBn_dvd : B ∣ n) :
    ¬ (n - 2 ^ k - 2 ^ l).Prime := by
  have hdist : Nat.dist k l = l - k := Nat.dist_eq_sub_of_le (le_of_lt hkl)
  have hdvd : B ∣ (n - 2 ^ k - 2 ^ l) :=
    dvd_sub_two_pows_of_dvd_fermatNumber_of_padicValNat_dist
      (ne_of_lt hkl) (by rw [hdist]; exact hr) hBF hBn_dvd
  have hne : n - 2 ^ k - 2 ^ l ≠ B :=
    crocker_off_diagonal_ne_fermat_factor hn16 hk1 hkl hB3 hBn hB16
  have hpos : 0 < n - 2 ^ k - 2 ^ l := by omega
  have hle : B ≤ n - 2 ^ k - 2 ^ l := Nat.le_of_dvd hpos hdvd
  exact not_prime_of_dvd_of_lt (by omega) (by omega) hdvd


/-- If `k < l`, `2 ^ k + 2 ^ l < n`, and `n ≤ 2 ^ (2 ^ w)`, then `padicValNat 2 (l - k) < w`. -/
theorem padicValNat_two_sub_lt_of_two_pow_add_lt {n w k l : ℕ}
    (hkl : k < l) (hlt : 2 ^ k + 2 ^ l < n) (hn : n ≤ 2 ^ (2 ^ w)) :
    padicValNat 2 (l - k) < w := by
  rcases (padicValNat_two_sub_eq_iff hkl).mp rfl with ⟨m, hl_eq⟩
  set r := padicValNat 2 (l - k)
  have h1 : 2 ^ r ≤ l - k := by
    have hm : 1 ≤ 2 * m + 1 := by omega
    calc 2 ^ r = 2 ^ r * 1 := (mul_one _).symm
      _ ≤ 2 ^ r * (2 * m + 1) := Nat.mul_le_mul_left (2 ^ r) hm
      _ = l - k := by omega
  have hk0 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : 2 ^ l < 2 ^ (2 ^ w) := by omega
  have h3 : l < 2 ^ w := (Nat.pow_lt_pow_iff_right (by decide)).mp h2
  have hsub_le : l - k ≤ l := Nat.sub_le l k
  have h4 : 2 ^ r < 2 ^ w := lt_of_le_of_lt (le_trans h1 hsub_le) h3
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp h4


/-! ## Section 2: Universal Periodic Exponential Divisibility & 24-Modulus Covering System -/

/-- Universal divisibility `(a ^ d - 1) ∣ (a ^ (d * k) - 1)`. -/
theorem pow_sub_one_dvd_pow_mul_sub_one (a d k : ℕ) :
    (a ^ d - 1) ∣ (a ^ (d * k) - 1) := by
  rw [Nat.pow_mul]
  exact Nat.sub_one_dvd_pow_sub_one (a ^ d) k


/-- Universal divisibility `(a ^ d - 1) ∣ (a ^ m - 1)` whenever `d ∣ m`. -/
theorem pow_sub_one_dvd_of_dvd {a d m : ℕ} (h : d ∣ m) :
    (a ^ d - 1) ∣ (a ^ m - 1) := by
  rcases h with ⟨k, rfl⟩
  exact pow_sub_one_dvd_pow_mul_sub_one a d k


/-- Universal periodic residue law for powers of `2`: if `q ∣ (2 ^ d - 1)` and `a % d = r`,
then `2 ^ a % q = 2 ^ r % q`. -/
theorem two_pow_mod_eq_of_dvd_pow_sub_one {d q a r : ℕ}
    (hq : q ∣ 2 ^ d - 1) (ha : a % d = r) :
    2 ^ a % q = 2 ^ r % q := by
  have hdiv : a = r + d * (a / d) := by
    have := Nat.div_add_mod a d
    omega
  have hdvd1 : q ∣ (2 ^ (d * (a / d)) - 1) :=
    dvd_trans hq (pow_sub_one_dvd_pow_mul_sub_one 2 d (a / d))
  have hdvd2 : q ∣ 2 ^ r * (2 ^ (d * (a / d)) - 1) :=
    dvd_mul_of_dvd_right hdvd1 (2 ^ r)
  have hsub : 2 ^ r * (2 ^ (d * (a / d)) - 1) = 2 ^ a - 2 ^ r := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← Nat.pow_add, ← hdiv]
  rw [hsub] at hdvd2
  have hle : 2 ^ r ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
  rcases hdvd2 with ⟨k, hk⟩
  have heq : 2 ^ a = 2 ^ r + q * k := by omega
  rw [heq, Nat.add_mul_mod_self_left]


/-- If `n % q = 2 ^ a % q` and `2 ^ a ≤ n`, then `q ∣ (n - 2 ^ a)`. -/
theorem dvd_sub_two_pow_of_mod_eq {n q a : ℕ}
    (hmod : n % q = 2 ^ a % q) (hle : 2 ^ a ≤ n) :
    q ∣ (n - 2 ^ a) := by
  rw [← Nat.modEq_iff_dvd' hle]
  exact hmod.symm


/-- 24-entry covering table `(d, q, r)` for `ℕ` modulo `720`, where every period `d ∣ 720`
has an odd factor (`3 ∣ d` or `5 ∣ d`), `q` is a primitive prime factor of `2 ^ d - 1`,
and `r < d` is the covered residue class. -/
def crockerCoverTable : List (ℕ × ℕ × ℕ) :=
  [(3, 7, 0), (5, 31, 0), (9, 73, 1), (10, 11, 1), (12, 13, 2), (15, 151, 2),
   (18, 19, 4), (20, 41, 3), (24, 241, 8), (30, 331, 29), (36, 37, 16), (36, 109, 34),
   (40, 61681, 13), (45, 631, 4), (45, 23311, 7), (48, 97, 20), (48, 673, 44),
   (60, 61, 53), (60, 1321, 7), (72, 433, 25), (72, 38737, 49), (80, 4278255361, 19),
   (90, 18837001, 79), (120, 4562284561, 37)]

/-- CRT multiplier `w₀` for Crocker's explicit sequence. -/
def crockerW0 : ℕ :=
  4758624587451861014979991485226715547679950269694194511556330600963496796350177

/-- Prime factor `2424833 = 37 * 2 ^ 16 + 1` of the 9th Fermat number `F₉ = 2 ^ 512 + 1`. -/
def crockerB9 : ℕ := 2424833

/-- Base Fermat product `(2 ^ 512 - 1) * 2424833` at level `10`. -/
def crockerP10 : ℕ := (2 ^ 512 - 1) * crockerB9

/-- Base term `N₀ = w₀ * P₁₀` of Crocker's explicit sequence. -/
def crockerN0 : ℕ := crockerW0 * crockerP10

set_option maxRecDepth 200000 in
/-- Every `a < 720` is covered by at least one congruence `a % d = r` in `crockerCoverTable`. -/
theorem crockerCoverTable_covers_lt_720 :
    ∀ a < 720, ∃ e ∈ crockerCoverTable, a % e.1 = e.2.2 := by
  have _ := propext (Iff.rfl : True ↔ True)
  decide


set_option exponentiation.threshold 2048 in
set_option maxRecDepth 200000 in
/-- Verified arithmetic specification of all 24 entries `(d, q, r)` in `crockerCoverTable`. -/
theorem crockerCoverTable_spec :
    ∀ e ∈ crockerCoverTable,
      0 < e.1 ∧ 1 < e.2.1 ∧ e.1 ∣ 720 ∧ e.1 ∣ 5040 ∧ e.2.2 < e.1 ∧
      e.2.1 ∣ (2 ^ e.1 - 1) ∧
      Nat.Coprime e.2.1 (2 ^ 1024 - 1) ∧
      crockerN0 % e.2.1 = 2 ^ e.2.2 % e.2.1 ∧
      (∀ j < 7, (e.2.1 + 2 ^ j) % 127 ≠ 1) := by
  decide


/-- Universal covering property of `crockerCoverTable`: every natural number `a : ℕ`
satisfies `a % d = r` for some `(d, q, r) ∈ crockerCoverTable`. -/
theorem crockerCoverTable_covers_all (a : ℕ) :
    ∃ e ∈ crockerCoverTable, a % e.1 = e.2.2 := by
  have hlt : a % 720 < 720 := Nat.mod_lt a (by decide)
  rcases crockerCoverTable_covers_lt_720 (a % 720) hlt with ⟨e, he, hmod⟩
  have hd720 : e.1 ∣ 720 := (crockerCoverTable_spec e he).2.2.1
  rw [Nat.mod_mod_of_dvd a hd720] at hmod
  exact ⟨e, he, hmod⟩


set_option exponentiation.threshold 2048 in
/-- Verified base arithmetic properties of `crockerN0` and `crockerB9`. -/
theorem crockerN0_base_props :
    0 < crockerN0 ∧
    15 * (2 ^ 512 + 1) ≤ crockerN0 ∧
    crockerN0 < 2 ^ 1024 - 1 ∧
    crockerN0 % 16 = 15 ∧
    crockerN0 % 127 = 1 ∧
    crockerB9 ∣ (2 ^ 512 + 1) ∧
    crockerB9 % 16 = 1 ∧
    Nat.Coprime 127 (2 ^ 1024 - 1) ∧
    Nat.Coprime 16 (2 ^ 1024 - 1) := by
  decide


/-! ## Section 3: Crocker's Infinite Sequence `crockerN t` and Proof of `Erdos9A.Infinite` -/

/-- Period-12 exponent sequence `n_t = 10 + 12 * t`. -/
def crockerExp (t : ℕ) : ℕ := 10 + 12 * t

/-- Fermat cofactor `U_t = (2 ^ (2 ^ (10 + 12 * t)) - 1) / (2 ^ 1024 - 1)`. -/
def crockerU (t : ℕ) : ℕ := (2 ^ (2 ^ crockerExp t) - 1) / (2 ^ 1024 - 1)

/-- Crocker's explicit sequence `N_t = N₀ * U_t` of odd integers in `Erdos9A`. -/
def crockerN (t : ℕ) : ℕ := crockerN0 * crockerU t

/-- Fermat divisor `B_r` assigned to 2-adic valuation `r`: `crockerB9 = 2424833` at `r = 9`,
and the full Fermat number `fermatNumber r = 2 ^ (2 ^ r) + 1` for `r ≠ 9`. -/
def crockerB (r : ℕ) : ℕ := if r = 9 then crockerB9 else fermatNumber r

/-- `1024 = 2 ^ 10` divides `2 ^ crockerExp t` for all `t : ℕ`. -/
theorem two_pow_ten_dvd_two_pow_crockerExp (t : ℕ) :
    1024 ∣ 2 ^ crockerExp t := by
  unfold crockerExp
  rw [Nat.pow_add]
  exact dvd_mul_right 1024 (2 ^ (12 * t))


/-- `2 ^ 1024 - 1` divides `2 ^ (2 ^ crockerExp t) - 1` for all `t : ℕ`. -/
theorem two_pow_1024_sub_one_dvd (t : ℕ) :
    (2 ^ 1024 - 1) ∣ (2 ^ (2 ^ crockerExp t) - 1) :=
  pow_sub_one_dvd_of_dvd (two_pow_ten_dvd_two_pow_crockerExp t)


/-- Exact multiplication identity `(2 ^ 1024 - 1) * crockerU t = 2 ^ (2 ^ crockerExp t) - 1`. -/
theorem mul_crockerU_eq (t : ℕ) :
    (2 ^ 1024 - 1) * crockerU t = 2 ^ (2 ^ crockerExp t) - 1 :=
  Nat.mul_div_cancel' (two_pow_1024_sub_one_dvd t)


set_option exponentiation.threshold 2048 in
/-- Positive lower bound `0 < 2 ^ 1024 - 1`. -/
theorem two_pow_1024_sub_one_pos : 0 < 2 ^ 1024 - 1 := by
  have h1 : (1 : ℕ) ≤ 1024 := by decide
  have h2 : 2 ^ 1 ≤ 2 ^ 1024 := Nat.pow_le_pow_right (by decide) h1
  omega


set_option exponentiation.threshold 2048 in
/-- Every cofactor `crockerU t` is at least `1`. -/
theorem one_le_crockerU (t : ℕ) : 1 ≤ crockerU t := by
  have h1 : 10 ≤ crockerExp t := by unfold crockerExp; omega
  have h2 : 1024 ≤ 2 ^ crockerExp t := by
    calc 1024 = 2 ^ 10 := by decide
      _ ≤ 2 ^ crockerExp t := Nat.pow_le_pow_right (by decide) h1
  have h3 : 2 ^ 1024 ≤ 2 ^ (2 ^ crockerExp t) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h2
  have h4 : 0 < 2 ^ 1024 - 1 := two_pow_1024_sub_one_pos
  have h5 : (2 ^ 1024 - 1) * 1 ≤ (2 ^ 1024 - 1) * crockerU t := by
    rw [mul_one, mul_crockerU_eq]
    omega
  exact Nat.le_of_mul_le_mul_left h5 h4


/-- `crockerN t` is strictly bounded above by `2 ^ (2 ^ crockerExp t) - 1`. -/
theorem crockerN_lt_two_pow (t : ℕ) :
    crockerN t < 2 ^ (2 ^ crockerExp t) - 1 := by
  unfold crockerN
  rw [← mul_crockerU_eq]
  have hlt : crockerN0 < 2 ^ 1024 - 1 := crockerN0_base_props.2.2.1
  have hu : 0 < crockerU t := one_le_crockerU t
  exact (Nat.mul_lt_mul_right hu).mpr hlt


/-- `crockerN` is strictly increasing (`StrictMono crockerN`). -/
theorem crockerN_strictMono : StrictMono crockerN := by
  intro t₁ t₂ hlt
  unfold crockerN
  have hn0 : 0 < crockerN0 := crockerN0_base_props.1
  rw [Nat.mul_lt_mul_left hn0]
  have h1024 : 0 < 2 ^ 1024 - 1 := two_pow_1024_sub_one_pos
  rw [← Nat.mul_lt_mul_left h1024, mul_crockerU_eq, mul_crockerU_eq]
  have hexp : crockerExp t₁ < crockerExp t₂ := by unfold crockerExp; omega
  have hpow1 : 2 ^ crockerExp t₁ < 2 ^ crockerExp t₂ :=
    (Nat.pow_lt_pow_iff_right (by decide)).mpr hexp
  have hpow2 : 2 ^ (2 ^ crockerExp t₁) < 2 ^ (2 ^ crockerExp t₂) :=
    (Nat.pow_lt_pow_iff_right (by decide)).mpr hpow1
  have hge1 : 1 ≤ 2 ^ (2 ^ crockerExp t₁) := Nat.one_le_two_pow
  omega


/-- Period-12 divisibility: `5040 ∣ (2 ^ crockerExp t - 1024)` for all `t : ℕ`. -/
theorem five_thousand_forty_dvd_sub (t : ℕ) :
    5040 ∣ (2 ^ crockerExp t - 1024) := by
  have h1 : 2 ^ crockerExp t - 1024 = 1024 * (2 ^ (12 * t) - 1) := by
    unfold crockerExp
    rw [Nat.pow_add]
    have h210 : 2 ^ 10 = 1024 := by decide
    rw [h210, Nat.mul_sub_left_distrib, mul_one]
  rw [h1]
  have h315 : 315 ∣ (2 ^ 12 - 1) := by decide
  have hdvd : 315 ∣ (2 ^ (12 * t) - 1) :=
    dvd_trans h315 (pow_sub_one_dvd_pow_mul_sub_one 2 12 t)
  have h16 : 16 ∣ 1024 := by decide
  have h5040 : 5040 = 16 * 315 := by decide
  rw [h5040]
  exact mul_dvd_mul h16 hdvd


/-- Algebraic factoring of `(2 ^ 1024 - 1) * (crockerU t - 1)`. -/
theorem mul_crockerU_sub_one_eq (t : ℕ) :
    (2 ^ 1024 - 1) * (crockerU t - 1) = 2 ^ 1024 * (2 ^ (2 ^ crockerExp t - 1024) - 1) := by
  rw [Nat.mul_sub_left_distrib, mul_one, mul_crockerU_eq]
  have h1 : 10 ≤ crockerExp t := by unfold crockerExp; omega
  have h2 : 1024 ≤ 2 ^ crockerExp t := by
    calc 1024 = 2 ^ 10 := by decide
      _ ≤ 2 ^ crockerExp t := Nat.pow_le_pow_right (by decide) h1
  have h3 : 2 ^ (2 ^ crockerExp t) = 2 ^ 1024 * 2 ^ (2 ^ crockerExp t - 1024) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le h2]
  have h4 : 1 ≤ 2 ^ (2 ^ crockerExp t - 1024) := Nat.one_le_two_pow
  rw [Nat.mul_sub_left_distrib, mul_one, ← h3]
  omega


/-- Universal cofactor congruence: if `d ∣ 5040`, `q ∣ (2 ^ d - 1)`, and `Coprime q (2 ^ 1024 - 1)`,
then `q ∣ (crockerU t - 1)`. -/
theorem dvd_crockerU_sub_one_of_dvd_5040 {d q : ℕ}
    (hd : d ∣ 5040) (hq : q ∣ 2 ^ d - 1) (hcop : Nat.Coprime q (2 ^ 1024 - 1)) (t : ℕ) :
    q ∣ (crockerU t - 1) := by
  have hdvd1 : d ∣ (2 ^ crockerExp t - 1024) := dvd_trans hd (five_thousand_forty_dvd_sub t)
  have hdvd2 : q ∣ (2 ^ (2 ^ crockerExp t - 1024) - 1) :=
    dvd_trans hq (pow_sub_one_dvd_of_dvd hdvd1)
  have hdvd3 : q ∣ (2 ^ 1024 - 1) * (crockerU t - 1) := by
    rw [mul_crockerU_sub_one_eq]
    exact dvd_mul_of_dvd_right hdvd2 (2 ^ 1024)
  exact hcop.dvd_of_dvd_mul_left hdvd3


/-- If `q ∣ (crockerU t - 1)`, then `crockerN t % q = crockerN0 % q`. -/
theorem crockerN_mod_eq_of_dvd_crockerU_sub_one {q t : ℕ}
    (hdvd : q ∣ (crockerU t - 1)) :
    crockerN t % q = crockerN0 % q := by
  rcases hdvd with ⟨m, hm⟩
  have hu : crockerU t = 1 + q * m := by
    have := one_le_crockerU t
    omega
  unfold crockerN
  rw [hu, mul_add, mul_one, ← mul_assoc, mul_comm crockerN0 q, mul_assoc,
    Nat.add_mul_mod_self_left]


/-- For every `t : ℕ`, `16 ∣ (crockerU t - 1)` and hence `crockerN t % 16 = 15`. -/
theorem crockerN_mod_sixteen (t : ℕ) : crockerN t % 16 = 15 := by
  have hcop : Nat.Coprime 16 (2 ^ 1024 - 1) := crockerN0_base_props.2.2.2.2.2.2.2.2
  have hdvd1 : 16 ∣ 2 ^ 1024 := by
    have : 2 ^ 1024 = 16 * 2 ^ 1020 := by
      have h16 : (16 : ℕ) = 2 ^ 4 := by decide
      rw [h16, ← Nat.pow_add]
    rw [this]
    exact dvd_mul_right 16 (2 ^ 1020)
  have hdvd2 : 16 ∣ (2 ^ 1024 - 1) * (crockerU t - 1) := by
    rw [mul_crockerU_sub_one_eq]
    exact dvd_mul_of_dvd_left hdvd1 _
  have hdvd3 : 16 ∣ (crockerU t - 1) := hcop.dvd_of_dvd_mul_left hdvd2
  rw [crockerN_mod_eq_of_dvd_crockerU_sub_one hdvd3]
  exact crockerN0_base_props.2.2.2.1


/-- For every `t : ℕ`, `crockerN t % 127 = 1`. -/
theorem crockerN_mod_127 (t : ℕ) : crockerN t % 127 = 1 := by
  have hdvd : 127 ∣ (crockerU t - 1) :=
    dvd_crockerU_sub_one_of_dvd_5040 (d := 7) (by decide) (by decide)
      crockerN0_base_props.2.2.2.2.2.2.2.1 t
  rw [crockerN_mod_eq_of_dvd_crockerU_sub_one hdvd]
  exact crockerN0_base_props.2.2.2.2.1


/-- Universal diagonal exclusion for `crockerN t`: for every `t, a : ℕ`,
`crockerN t - 2 ^ a` is never prime. -/
theorem not_prime_crockerN_sub_two_pow (t a : ℕ) :
    ¬ (crockerN t - 2 ^ a).Prime := by
  by_cases hlt : 2 ^ a < crockerN t
  · rcases crockerCoverTable_covers_all a with ⟨e, he, ha_mod⟩
    rcases crockerCoverTable_spec e he with
      ⟨hd_pos, hq1, -, hd5040, hr_lt, hq_dvd, hq_cop, hn0_mod, h127_disj⟩
    have hN_mod_q : crockerN t % e.2.1 = 2 ^ e.2.2 % e.2.1 := by
      rw [crockerN_mod_eq_of_dvd_crockerU_sub_one
        (dvd_crockerU_sub_one_of_dvd_5040 hd5040 hq_dvd hq_cop t)]
      exact hn0_mod
    have hpow_mod_q : 2 ^ a % e.2.1 = 2 ^ e.2.2 % e.2.1 :=
      two_pow_mod_eq_of_dvd_pow_sub_one hq_dvd ha_mod
    have hdvd : e.2.1 ∣ (crockerN t - 2 ^ a) :=
      dvd_sub_two_pow_of_mod_eq (hN_mod_q.trans hpow_mod_q.symm) (le_of_lt hlt)
    have hne : crockerN t - 2 ^ a ≠ e.2.1 := by
      intro heq
      have hsum : crockerN t = e.2.1 + 2 ^ a := by omega
      have hpow127 : 2 ^ a % 127 = 2 ^ (a % 7) % 127 :=
        two_pow_mod_eq_of_dvd_pow_sub_one (d := 7) (by decide) rfl
      have hmod127 : (e.2.1 + 2 ^ (a % 7)) % 127 = 1 := by
        have h1 := crockerN_mod_127 t
        rw [hsum, Nat.add_mod, hpow127, ← Nat.add_mod] at h1
        exact h1
      exact h127_disj (a % 7) (Nat.mod_lt a (by decide)) hmod127
    have hpos : 0 < crockerN t - 2 ^ a := by omega
    have hle : e.2.1 ≤ crockerN t - 2 ^ a := Nat.le_of_dvd hpos hdvd
    exact not_prime_of_dvd_of_lt hq1 (by omega) hdvd
  · have hzero : crockerN t - 2 ^ a = 0 := by omega
    rw [hzero]
    exact Nat.not_prime_zero


/-- Every `crockerB r` is at least `3`. -/
theorem three_le_crockerB (r : ℕ) : 3 ≤ crockerB r := by
  unfold crockerB
  split_ifs with hr
  · decide
  · exact three_le_fermatNumber r


/-- Every `crockerB r` satisfies `crockerB r % 16 ∈ {1, 3, 5}`. -/
theorem crockerB_mod_sixteen_cases (r : ℕ) :
    crockerB r % 16 = 1 ∨ crockerB r % 16 = 3 ∨ crockerB r % 16 = 5 := by
  unfold crockerB
  split_ifs with hr
  · left; exact crockerN0_base_props.2.2.2.2.2.2.1
  · exact fermatNumber_mod_sixteen_cases r


/-- Every `crockerB r` divides the `r`-th Fermat number `2 ^ (2 ^ r) + 1`. -/
theorem crockerB_dvd_fermatNumber (r : ℕ) :
    crockerB r ∣ (2 ^ (2 ^ r) + 1) := by
  unfold crockerB
  split_ifs with hr
  · subst hr
    have h512 : 2 ^ 9 = 512 := by decide
    rw [h512]
    exact crockerN0_base_props.2.2.2.2.2.1
  · exact dvd_rfl


/-- Any odd natural number `a` with `a - b = 2` is coprime to `b`. -/
theorem odd_coprime_of_sub_eq_two {a b : ℕ} (ha : Odd a) (hdiff : a - b = 2) :
    Nat.Coprime a b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg1 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
  have hg2 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
  have hg_two : Nat.gcd a b ∣ 2 := by
    rw [← hdiff]
    exact Nat.dvd_sub hg1 hg2
  have hle : Nat.gcd a b ≤ 2 := Nat.le_of_dvd (by decide) hg_two
  have hpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b (by rcases ha with ⟨k, rfl⟩; omega)
  have hnot2 : ¬ (2 ∣ a) := by rcases ha with ⟨k, rfl⟩; omega
  have hne2 : Nat.gcd a b ≠ 2 := by
    intro h2
    rw [h2] at hg1
    exact hnot2 hg1
  omega


/-- For every `r ≥ 10`, `fermatNumber r = 2 ^ (2 ^ r) + 1` is coprime to `2 ^ 1024 - 1`. -/
theorem coprime_fermatNumber_two_pow_1024_sub_one {r : ℕ} (hr : 10 ≤ r) :
    Nat.Coprime (fermatNumber r) (2 ^ 1024 - 1) := by
  have hdvd1024 : 1024 ∣ 2 ^ r := by
    have hr_eq : r = 10 + (r - 10) := by omega
    rw [hr_eq, Nat.pow_add]
    exact dvd_mul_right 1024 (2 ^ (r - 10))
  have hdvd_sub : (2 ^ 1024 - 1) ∣ (2 ^ (2 ^ r) - 1) :=
    pow_sub_one_dvd_of_dvd hdvd1024
  have hdiff : fermatNumber r - (2 ^ (2 ^ r) - 1) = 2 := by
    unfold fermatNumber
    have : 1 ≤ 2 ^ (2 ^ r) := Nat.one_le_two_pow
    omega
  have hcop_sub : Nat.Coprime (fermatNumber r) (2 ^ (2 ^ r) - 1) :=
    odd_coprime_of_sub_eq_two (odd_fermatNumber r) hdiff
  exact hcop_sub.coprime_dvd_right hdvd_sub


/-- For every `10 ≤ r < crockerExp t`, `fermatNumber r` divides `crockerU t`. -/
theorem fermatNumber_dvd_crockerU {t r : ℕ} (hr10 : 10 ≤ r) (hr : r < crockerExp t) :
    fermatNumber r ∣ crockerU t := by
  have hdvd_prod : fermatNumber r ∣ (2 ^ 1024 - 1) * crockerU t := by
    rw [mul_crockerU_eq]
    simpa [fermatNumber, mul_one] using fermatNumber_dvd_two_pow_two_pow_mul_sub_one hr 1
  exact (coprime_fermatNumber_two_pow_1024_sub_one hr10).dvd_of_dvd_mul_left hdvd_prod


/-- For every `r < crockerExp t`, `crockerB r` divides `crockerN t`. -/
theorem crockerB_dvd_crockerN {t r : ℕ} (hr : r < crockerExp t) :
    crockerB r ∣ crockerN t := by
  rcases lt_trichotomy r 9 with hlt9 | rfl | hgt9
  · have hne9 : r ≠ 9 := by omega
    unfold crockerB
    rw [if_neg hne9]
    have hdvd512 : fermatNumber r ∣ (2 ^ 512 - 1) := by
      have h9 : 2 ^ 9 * 1 = 512 := by decide
      have h := fermatNumber_dvd_two_pow_two_pow_mul_sub_one hlt9 1
      rw [h9] at h
      exact h
    have hdvd_p10 : fermatNumber r ∣ crockerP10 := dvd_mul_of_dvd_left hdvd512 crockerB9
    have hdvd_n0 : fermatNumber r ∣ crockerN0 := dvd_mul_of_dvd_right hdvd_p10 crockerW0
    exact dvd_mul_of_dvd_left hdvd_n0 (crockerU t)
  · unfold crockerB
    rw [if_pos rfl]
    have hdvd_p10 : crockerB9 ∣ crockerP10 := dvd_mul_left crockerB9 (2 ^ 512 - 1)
    have hdvd_n0 : crockerB9 ∣ crockerN0 := dvd_mul_of_dvd_right hdvd_p10 crockerW0
    exact dvd_mul_of_dvd_left hdvd_n0 (crockerU t)
  · have hne9 : r ≠ 9 := by omega
    unfold crockerB
    rw [if_neg hne9]
    exact dvd_mul_of_dvd_right (fermatNumber_dvd_crockerU (by omega) hr) crockerN0


set_option exponentiation.threshold 2048 in
/-- For every `r < crockerExp t`, `15 * crockerB r ≤ crockerN t`. -/
theorem fifteen_mul_crockerB_le_crockerN {t r : ℕ} (hr : r < crockerExp t) :
    15 * crockerB r ≤ crockerN t := by
  by_cases hr9 : r ≤ 9
  · have hle512 : crockerB r ≤ 2 ^ 512 + 1 := by
      unfold crockerB
      split_ifs with h9
      · have h1 : crockerB9 ≤ 2 ^ 22 := by decide
        have h22 : (22 : ℕ) ≤ 512 := by decide
        have h2 : 2 ^ 22 ≤ 2 ^ 512 := Nat.pow_le_pow_right (by decide : 0 < 2) h22
        omega
      · unfold fermatNumber
        have h1 : 2 ^ r ≤ 512 := by
          calc 2 ^ r ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hr9
            _ = 512 := by decide
        have h2 : 2 ^ (2 ^ r) ≤ 2 ^ 512 := Nat.pow_le_pow_right (by decide : 0 < 2) h1
        omega
    have hle_n0 : 15 * crockerB r ≤ crockerN0 :=
      le_trans (Nat.mul_le_mul_left 15 hle512) crockerN0_base_props.2.1
    calc 15 * crockerB r ≤ crockerN0 * 1 := by rw [mul_one]; exact hle_n0
      _ ≤ crockerN0 * crockerU t := Nat.mul_le_mul_left crockerN0 (one_le_crockerU t)
  · have hr10 : 10 ≤ r := by omega
    have hne9 : r ≠ 9 := by omega
    have hdvd : crockerB r ∣ crockerU t := by
      unfold crockerB
      rw [if_neg hne9]
      exact fermatNumber_dvd_crockerU hr10 hr
    have hle_u : crockerB r ≤ crockerU t := Nat.le_of_dvd (one_le_crockerU t) hdvd
    have h15_n0 : 15 ≤ crockerN0 := by
      have hbase := crockerN0_base_props.2.1
      have hpos : 1 ≤ 2 ^ 512 + 1 := by omega
      calc 15 = 15 * 1 := (mul_one 15).symm
        _ ≤ 15 * (2 ^ 512 + 1) := Nat.mul_le_mul_left 15 hpos
        _ ≤ crockerN0 := hbase
    exact Nat.mul_le_mul h15_n0 hle_u


/-- Every term `crockerN t` belongs to `Erdos9A`. -/
theorem crockerN_mem_erdos9A (t : ℕ) : crockerN t ∈ Erdos9A := by
  have hn16 : crockerN t % 16 = 15 := crockerN_mod_sixteen t
  have hodd : Odd (crockerN t) := odd_of_mod_sixteen_eq_fifteen hn16
  rw [mem_erdos9A_iff_three_obstructions hodd]
  refine ⟨?_, ?_, ?_⟩
  · intro m _
    exact ne_two_pow_add_three_of_mod_sixteen_eq_fifteen hn16 m
  · simpa using not_prime_crockerN_sub_two_pow t 1
  · intro k l hk1 hl1 hlt
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · have hbound : crockerN t ≤ 2 ^ (2 ^ crockerExp t) :=
        le_of_lt (lt_of_lt_of_le (crockerN_lt_two_pow t) (Nat.sub_le _ _))
      have hr_lt : padicValNat 2 (l - k) < crockerExp t :=
        padicValNat_two_sub_lt_of_two_pow_add_lt hkl hlt hbound
      set r := padicValNat 2 (l - k)
      exact crocker_off_diagonal_composite_of_fermat_factor
        hn16 hk1 hkl hlt rfl
        (three_le_crockerB r)
        (fifteen_mul_crockerB_le_crockerN hr_lt)
        (crockerB_mod_sixteen_cases r)
        (crockerB_dvd_fermatNumber r)
        (crockerB_dvd_crockerN hr_lt)
    · rw [sub_two_pow_sub_self]
      exact not_prime_crockerN_sub_two_pow t (k + 1)
    · have hlt' : 2 ^ l + 2 ^ k < crockerN t := by omega
      have hsub_comm : crockerN t - 2 ^ k - 2 ^ l = crockerN t - 2 ^ l - 2 ^ k := by omega
      rw [hsub_comm]
      have hbound : crockerN t ≤ 2 ^ (2 ^ crockerExp t) :=
        le_of_lt (lt_of_lt_of_le (crockerN_lt_two_pow t) (Nat.sub_le _ _))
      have hr_lt : padicValNat 2 (k - l) < crockerExp t :=
        padicValNat_two_sub_lt_of_two_pow_add_lt hlk hlt' hbound
      set r := padicValNat 2 (k - l)
      exact crocker_off_diagonal_composite_of_fermat_factor
        hn16 hl1 hlk hlt' rfl
        (three_le_crockerB r)
        (fifteen_mul_crockerB_le_crockerN hr_lt)
        (crockerB_mod_sixteen_cases r)
        (crockerB_dvd_fermatNumber r)
        (crockerB_dvd_crockerN hr_lt)


/-- Every term `crockerN t` belongs to `Erdos9APos`. -/
theorem crockerN_mem_erdos9APos (t : ℕ) : crockerN t ∈ Erdos9APos :=
  erdos9A_subset_erdos9APos (crockerN_mem_erdos9A t)


/-- Unconditional proof of Crocker's (1971) / Schinzel's theorem (`erdos_9.variants.infinite`):
the set `Erdos9A` of odd integers not expressible as `p + 2 ^ k + 2 ^ l` is infinite. -/
theorem erdos9A_infinite : Erdos9A.Infinite :=
  Set.infinite_of_injective_forall_mem crockerN_strictMono.injective crockerN_mem_erdos9A


/-- Upstream declaration alias for `erdos_9.variants.infinite` in `FormalConjectures/ErdosProblems/9.lean`. -/
theorem erdos_9_variants_infinite : Erdos9A.Infinite :=
  erdos9A_infinite


/-- Unconditional infinitude of the positive-exponent exceptional set `Erdos9APos`. -/
theorem erdos9APos_infinite : Erdos9APos.Infinite :=
  erdos9A_infinite.mono erdos9A_subset_erdos9APos

end Erdos9


/-!
# Erdős Problem 10: Unified Lean 4.35 Baseline

Defines `Erdos10.sumPrimeAndTwoPows` matching `FormalConjectures/ErdosProblems/10.lean`
and establishes foundational non-vacuity, monotonicity, and recursive decomposition
theorems for representations as a sum of a prime and at most `k` powers of `2`.
-/

namespace Erdos10

/-- Package-local statement of the Formal Conjectures target: the set of natural
numbers that can be written as a sum of a prime and at most `k` powers of `2`. -/
abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { p + (pows.map (2 ^ ·)).sum | (p : ℕ) (pows : Multiset ℕ) (_ : p.Prime)
    (_ : pows.card ≤ k) }

/-- `2` is a prime and lies in `sumPrimeAndTwoPows 0`. -/
theorem two_mem_zero : 2 ∈ sumPrimeAndTwoPows 0 :=
  ⟨2, 0, Nat.prime_two, by simp, by simp⟩


/-- Every element of `sumPrimeAndTwoPows k` is at least `2`. -/
theorem two_le_of_mem_sumPrimeAndTwoPows {k n : ℕ} (hn : n ∈ sumPrimeAndTwoPows k) :
    2 ≤ n := by
  rcases hn with ⟨p, pows, hp, -, rfl⟩
  have hp2 : 2 ≤ p := hp.two_le
  omega


/-- `0` is smaller than every prime, so it lies in no `sumPrimeAndTwoPows k`. -/
theorem zero_not_mem_sumPrimeAndTwoPows (k : ℕ) : 0 ∉ sumPrimeAndTwoPows k := by
  intro h
  have h2 : 2 ≤ 0 := two_le_of_mem_sumPrimeAndTwoPows h
  omega


/-- `1` is smaller than every prime, so it lies in no `sumPrimeAndTwoPows k`. -/
theorem one_not_mem (k : ℕ) : 1 ∉ sumPrimeAndTwoPows k := by
  rintro ⟨p, pows, hp, -, h⟩
  have : 2 ≤ p := hp.two_le
  omega


/-- Every prime belongs to `sumPrimeAndTwoPows 0`. -/
theorem prime_mem_sumPrimeAndTwoPows_zero {p : ℕ} (hp : p.Prime) :
    p ∈ sumPrimeAndTwoPows 0 :=
  ⟨p, 0, hp, by simp, by simp⟩


/-- Exact characterization of `sumPrimeAndTwoPows 0` as the set of prime numbers. -/
theorem mem_sumPrimeAndTwoPows_zero_iff (n : ℕ) :
    n ∈ sumPrimeAndTwoPows 0 ↔ n.Prime := by
  constructor
  · rintro ⟨p, pows, hp, hcard, rfl⟩
    have hpows : pows = 0 := Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    subst hpows
    simpa using hp
  · exact prime_mem_sumPrimeAndTwoPows_zero


/-- Monotonicity of `sumPrimeAndTwoPows` in the exponent budget `k`. -/
theorem sumPrimeAndTwoPows_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    sumPrimeAndTwoPows k₁ ⊆ sumPrimeAndTwoPows k₂ := by
  rintro n ⟨p, pows, hp, hcard, rfl⟩
  have hle : pows.card ≤ k₂ := le_trans hcard h
  exact ⟨p, pows, hp, hle, by simp⟩


/-- Every prime belongs to `sumPrimeAndTwoPows k` for every `k`. -/
theorem prime_mem_sumPrimeAndTwoPows {p : ℕ} (hp : p.Prime) (k : ℕ) :
    p ∈ sumPrimeAndTwoPows k :=
  sumPrimeAndTwoPows_mono (Nat.zero_le k) (prime_mem_sumPrimeAndTwoPows_zero hp)


/-- Adding `2 ^ a` shifts membership from `sumPrimeAndTwoPows k` to `sumPrimeAndTwoPows (k + 1)`. -/
theorem add_two_pow_mem_sumPrimeAndTwoPows_succ {k n : ℕ}
    (hn : n ∈ sumPrimeAndTwoPows k) (a : ℕ) :
    n + 2 ^ a ∈ sumPrimeAndTwoPows (k + 1) := by
  rcases hn with ⟨p, pows, hp, hcard, rfl⟩
  refine ⟨p, a ::ₘ pows, hp, ?_, ?_⟩
  · rw [Multiset.card_cons]
    omega
  · rw [Multiset.map_cons, Multiset.sum_cons]
    omega


/-- Recursive step characterization of `sumPrimeAndTwoPows (k + 1)`. -/
theorem mem_sumPrimeAndTwoPows_succ_iff (k n : ℕ) :
    n ∈ sumPrimeAndTwoPows (k + 1) ↔
      n ∈ sumPrimeAndTwoPows k ∨ ∃ m a : ℕ, m ∈ sumPrimeAndTwoPows k ∧ n = m + 2 ^ a := by
  constructor
  · rintro ⟨p, pows, hp, hcard, rfl⟩
    by_cases hk : pows.card ≤ k
    · exact Or.inl ⟨p, pows, hp, hk, rfl⟩
    · have hne : pows ≠ 0 := by
        intro h0
        rw [h0, Multiset.card_zero] at hk
        exact hk (Nat.zero_le k)
      rcases Multiset.exists_mem_of_ne_zero hne with ⟨a, ha⟩
      refine Or.inr ⟨p + ((pows.erase a).map (2 ^ ·)).sum, a, ?_, ?_⟩
      · refine ⟨p, pows.erase a, hp, ?_, rfl⟩
        have hcons : (a ::ₘ pows.erase a).card = pows.card := by
          rw [Multiset.cons_erase ha]
        rw [Multiset.card_cons] at hcons
        omega
      · have hmap : pows.map (2 ^ ·) = 2 ^ a ::ₘ (pows.erase a).map (2 ^ ·) := by
          conv_lhs => rw [← Multiset.cons_erase ha]
          rw [Multiset.map_cons]
        rw [hmap, Multiset.sum_cons]
        omega
  · rintro (hn | ⟨m, a, hm, rfl⟩)
    · exact sumPrimeAndTwoPows_mono (Nat.le_succ k) hn
    · exact add_two_pow_mem_sumPrimeAndTwoPows_succ hm a


/-- Every sum of a prime and one power of `2` belongs to `sumPrimeAndTwoPows 1`. -/
theorem prime_add_two_pow_mem_sumPrimeAndTwoPows_one {p : ℕ} (hp : p.Prime) (a : ℕ) :
    p + 2 ^ a ∈ sumPrimeAndTwoPows 1 :=
  add_two_pow_mem_sumPrimeAndTwoPows_succ (prime_mem_sumPrimeAndTwoPows_zero hp) a


/-- Every sum of a prime and two powers of `2` belongs to `sumPrimeAndTwoPows 2`. -/
theorem prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two {p : ℕ}
    (hp : p.Prime) (a b : ℕ) :
    p + 2 ^ a + 2 ^ b ∈ sumPrimeAndTwoPows 2 :=
  add_two_pow_mem_sumPrimeAndTwoPows_succ (prime_add_two_pow_mem_sumPrimeAndTwoPows_one hp a) b


/-- Exact characterization of `sumPrimeAndTwoPows 1`: primes or `p + 2 ^ a`. -/
theorem mem_sumPrimeAndTwoPows_one_iff (n : ℕ) :
    n ∈ sumPrimeAndTwoPows 1 ↔ n.Prime ∨ ∃ p a : ℕ, p.Prime ∧ n = p + 2 ^ a := by
  rw [mem_sumPrimeAndTwoPows_succ_iff 0 n, mem_sumPrimeAndTwoPows_zero_iff]
  constructor
  · rintro (hp | ⟨m, a, hm, rfl⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨m, a, (mem_sumPrimeAndTwoPows_zero_iff m).mp hm, rfl⟩
  · rintro (hp | ⟨p, a, hp, rfl⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨p, a, prime_mem_sumPrimeAndTwoPows_zero hp, rfl⟩


/-- Exact characterization of `sumPrimeAndTwoPows 2`: `sumPrimeAndTwoPows 1` or `p + 2 ^ a + 2 ^ b`. -/
theorem mem_sumPrimeAndTwoPows_two_iff (n : ℕ) :
    n ∈ sumPrimeAndTwoPows 2 ↔
      n ∈ sumPrimeAndTwoPows 1 ∨ ∃ p a b : ℕ, p.Prime ∧ n = p + 2 ^ a + 2 ^ b := by
  rw [mem_sumPrimeAndTwoPows_succ_iff 1 n]
  constructor
  · rintro (h1 | ⟨m, b, hm, rfl⟩)
    · exact Or.inl h1
    · rcases (mem_sumPrimeAndTwoPows_one_iff m).mp hm with hm_prime | ⟨p, a, hp, rfl⟩
      · exact Or.inl (prime_add_two_pow_mem_sumPrimeAndTwoPows_one hm_prime b)
      · exact Or.inr ⟨p, a, b, hp, rfl⟩
  · rintro (h1 | ⟨p, a, b, hp, rfl⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨p + 2 ^ a, b, prime_add_two_pow_mem_sumPrimeAndTwoPows_one hp a, rfl⟩


/-- Every sum of a prime and three powers of `2` belongs to `sumPrimeAndTwoPows 3`. -/
theorem prime_add_three_two_pows_mem_sumPrimeAndTwoPows_three {p : ℕ}
    (hp : p.Prime) (a b c : ℕ) :
    p + 2 ^ a + 2 ^ b + 2 ^ c ∈ sumPrimeAndTwoPows 3 :=
  add_two_pow_mem_sumPrimeAndTwoPows_succ
    (prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two hp a b) c


/-- Exact characterization of `sumPrimeAndTwoPows 3`: `sumPrimeAndTwoPows 2` or `p + 2 ^ a + 2 ^ b + 2 ^ c`. -/
theorem mem_sumPrimeAndTwoPows_three_iff (n : ℕ) :
    n ∈ sumPrimeAndTwoPows 3 ↔
      n ∈ sumPrimeAndTwoPows 2 ∨ ∃ p a b c : ℕ, p.Prime ∧ n = p + 2 ^ a + 2 ^ b + 2 ^ c := by
  rw [mem_sumPrimeAndTwoPows_succ_iff 2 n]
  constructor
  · rintro (h2 | ⟨m, c, hm, rfl⟩)
    · exact Or.inl h2
    · rcases (mem_sumPrimeAndTwoPows_two_iff m).mp hm with hm1 | ⟨p, a, b, hp, rfl⟩
      · exact Or.inl (add_two_pow_mem_sumPrimeAndTwoPows_succ hm1 c)
      · exact Or.inr ⟨p, a, b, c, hp, rfl⟩
  · rintro (h2 | ⟨p, a, b, c, hp, rfl⟩)
    · exact Or.inl h2
    · exact Or.inr ⟨p + 2 ^ a + 2 ^ b, c,
        prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two hp a b, rfl⟩


/-- Universal logarithmic exponent bound for `n = p + 2 ^ a` with `p` prime:
if `n < 2 + 2 ^ B` and `n - 2 ^ a` is composite for all `a < B`, then `n ≠ p + 2 ^ a`
for all primes `p` and all exponents `a : ℕ`. -/
theorem not_eq_prime_add_two_pow_of_forall_lt {n B : ℕ}
    (hB : n < 2 + 2 ^ B)
    (hcheck : ∀ a ∈ Finset.range B, ¬ (n - 2 ^ a).Prime) :
    ∀ p a : ℕ, p.Prime → n ≠ p + 2 ^ a := by
  intro p a hp h
  have hp2 : 2 ≤ p := hp.two_le
  have hpow : 2 ^ a < 2 ^ B := by omega
  have ha : a < B := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpow
  have hsub : n - 2 ^ a = p := by omega
  apply hcheck a (Finset.mem_range.mpr ha)
  rw [hsub]
  exact hp


/-- Universal certificate bridge for non-membership in `sumPrimeAndTwoPows 1`. -/
theorem not_mem_sumPrimeAndTwoPows_one_of_forall_lt {n B : ℕ}
    (hnp : ¬ n.Prime)
    (hB : n < 2 + 2 ^ B)
    (hcheck : ∀ a ∈ Finset.range B, ¬ (n - 2 ^ a).Prime) :
    n ∉ sumPrimeAndTwoPows 1 := by
  rw [mem_sumPrimeAndTwoPows_one_iff]
  rintro (hp | ⟨p, a, hp, h⟩)
  · exact hnp hp
  · exact not_eq_prime_add_two_pow_of_forall_lt hB hcheck p a hp h


/-- Universal logarithmic exponent bound for `n = p + 2 ^ a + 2 ^ b` with `p` prime:
if `n < 3 + 2 ^ B` and `n - (2 ^ a + 2 ^ b)` is never prime for `a, b < B`, then
`n ≠ p + 2 ^ a + 2 ^ b` for all primes `p` and all `a, b : ℕ`. -/
theorem not_eq_prime_add_two_pow_add_two_pow_of_forall_lt {n B : ℕ}
    (hB : n < 3 + 2 ^ B)
    (hcheck : ∀ a ∈ Finset.range B, ∀ b ∈ Finset.range B,
      ¬ (2 ^ a + 2 ^ b ≤ n ∧ (n - (2 ^ a + 2 ^ b)).Prime)) :
    ∀ p a b : ℕ, p.Prime → n ≠ p + 2 ^ a + 2 ^ b := by
  intro p a b hp h
  have hp2 : 2 ≤ p := hp.two_le
  have ha1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hb1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hpow_a : 2 ^ a < 2 ^ B := by omega
  have hpow_b : 2 ^ b < 2 ^ B := by omega
  have ha : a < B := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpow_a
  have hb : b < B := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hpow_b
  apply hcheck a (Finset.mem_range.mpr ha) b (Finset.mem_range.mpr hb)
  refine ⟨by omega, ?_⟩
  have hsub : n - (2 ^ a + 2 ^ b) = p := by omega
  rw [hsub]
  exact hp


/-- Universal certificate bridge for non-membership in `sumPrimeAndTwoPows 2`. -/
theorem not_mem_sumPrimeAndTwoPows_two_of_forall_lt {n B : ℕ}
    (hn1 : n ∉ sumPrimeAndTwoPows 1)
    (hB : n < 3 + 2 ^ B)
    (hcheck : ∀ a ∈ Finset.range B, ∀ b ∈ Finset.range B,
      ¬ (2 ^ a + 2 ^ b ≤ n ∧ (n - (2 ^ a + 2 ^ b)).Prime)) :
    n ∉ sumPrimeAndTwoPows 2 := by
  rw [mem_sumPrimeAndTwoPows_two_iff]
  rintro (h1 | ⟨p, a, b, hp, h⟩)
  · exact hn1 h1
  · exact not_eq_prime_add_two_pow_add_two_pow_of_forall_lt hB hcheck p a b hp h


/-- Universal positive witness bridge for membership in `sumPrimeAndTwoPows 1`. -/
theorem mem_sumPrimeAndTwoPows_one_of_exists_lt {n B : ℕ}
    (h : n.Prime ∨ ∃ a ∈ Finset.range B, 2 ^ a ≤ n ∧ (n - 2 ^ a).Prime) :
    n ∈ sumPrimeAndTwoPows 1 := by
  rw [mem_sumPrimeAndTwoPows_one_iff]
  rcases h with hp | ⟨a, -, hle, hp⟩
  · exact Or.inl hp
  · exact Or.inr ⟨n - 2 ^ a, a, hp, by omega⟩


/-- Universal positive witness bridge for membership in `sumPrimeAndTwoPows 2`. -/
theorem mem_sumPrimeAndTwoPows_two_of_exists_lt {n B : ℕ}
    (h : n.Prime ∨ (∃ a ∈ Finset.range B, 2 ^ a ≤ n ∧ (n - 2 ^ a).Prime) ∨
      ∃ a ∈ Finset.range B, ∃ b ∈ Finset.range B,
        2 ^ a + 2 ^ b ≤ n ∧ (n - (2 ^ a + 2 ^ b)).Prime) :
    n ∈ sumPrimeAndTwoPows 2 := by
  rw [mem_sumPrimeAndTwoPows_two_iff]
  rcases h with hp | h1 | ⟨a, -, b, -, hle, hp⟩
  · exact Or.inl (prime_mem_sumPrimeAndTwoPows hp 1)
  · exact Or.inl (mem_sumPrimeAndTwoPows_one_of_exists_lt (Or.inr h1))
  · exact Or.inr ⟨n - (2 ^ a + 2 ^ b), a, b, hp, by omega⟩


end Erdos10

/-!
# Parity-Transfer Bridge, Granville–Soundararajan Reductions, and Covering-System Exclusions

Builds the parity-transfer and covering-system exclusions for Erdős Problem 10:
1. Formalizes the parity-transfer bridge `+ 1 = + 2 ^ 0` mapping `n ∈ sumPrimeAndTwoPows k`
   to `n + 1 ∈ sumPrimeAndTwoPows (k + 1)`, proves that Granville–Soundararajan's odd-`3`
   conjecture automatically implies the even-`4` half, and shows that it implies
   `n ∈ sumPrimeAndTwoPows 4` for all `n ≥ 2` (and hence the eventual statement of `erdos_10`).
2. Establishes exact small-cutoff classifications and concrete witness theorems for `105`,
   `127`, `149`, `16`, `22`, `905` (`k = 1`) and `3`, `128`, `150`, `906` (`k = 2`).
3. Proves the Erdős mod-`24` covering-system exclusion for `k = 1`, the parity-transfer
   covering lifting for `k = 2` yielding an unconditional proof of
   `Set.Infinite ({n : ℕ | Even n} \ sumPrimeAndTwoPows 2)` (`erdos_10.variants.two_pows`),
   and Crocker's `t ≡ 15 (mod 16)` parity-transfer equivalence for `k = 3` (`erdos_10.variants.grechuk`).
-/

namespace Erdos10

/-! ## Section 1: Parity-Transfer Bridge and Granville–Soundararajan Reductions -/

/-- If `q ≠ 1` divides a prime `p` (`p % q = 0`), then `p = q`. -/
theorem eq_of_prime_of_mod_eq_zero {p q : ℕ} (hp : p.Prime) (hq : q ≠ 1)
    (hmod : p % q = 0) : p = q := by
  rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hmod) with rfl | rfl
  · contradiction
  · rfl


/-- If `0 ∉ pows`, then every exponent in `pows` is positive, so `2` divides `(pows.map (2 ^ ·)).sum`. -/
theorem dvd_two_sum_map_two_pow_of_zero_not_mem {pows : Multiset ℕ}
    (h0 : 0 ∉ pows) : 2 ∣ (pows.map (2 ^ ·)).sum := by
  induction pows using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.mem_cons, not_or] at h0
    rcases h0 with ⟨ha0, hs0⟩
    rw [Multiset.map_cons, Multiset.sum_cons]
    have ha_dvd : 2 ∣ 2 ^ a := by
      rcases a with _ | a
      · contradiction
      · rw [Nat.pow_succ]
        omega
    exact Nat.dvd_add ha_dvd (ih hs0)


/-- Adding `1 = 2 ^ 0` shifts any element of `sumPrimeAndTwoPows k` into `sumPrimeAndTwoPows (k + 1)`. -/
theorem add_one_mem_sumPrimeAndTwoPows_succ {k n : ℕ}
    (hn : n ∈ sumPrimeAndTwoPows k) :
    n + 1 ∈ sumPrimeAndTwoPows (k + 1) := by
  simpa using add_two_pow_mem_sumPrimeAndTwoPows_succ hn 0


/-- Parity-transfer bridge: every odd `n ∈ sumPrimeAndTwoPows k` maps via `+ 1 = + 2 ^ 0`
to an even `n + 1 ∈ sumPrimeAndTwoPows (k + 1)`. -/
theorem even_succ_mem_sumPrimeAndTwoPows_succ_of_odd_mem {k n : ℕ}
    (hodd : Odd n) (hn : n ∈ sumPrimeAndTwoPows k) :
    Even (n + 1) ∧ n + 1 ∈ sumPrimeAndTwoPows (k + 1) := by
  refine ⟨?_, add_one_mem_sumPrimeAndTwoPows_succ hn⟩
  rcases hodd with ⟨m, rfl⟩
  exact ⟨m + 1, by omega⟩


/-- Universal parity-transfer equivalence for all `k`: for any odd `t`, `t + 1 ∈ sumPrimeAndTwoPows (k + 1)`
if and only if either `t ∈ sumPrimeAndTwoPows k` (by stripping `2 ^ 0 = 1`) or `t + 1 = 2 + (pows.map (2 ^ ·)).sum`
with `pows.card ≤ k + 1` and `0 ∉ pows` (forcing `p = 2`). -/
theorem even_succ_mem_sumPrimeAndTwoPows_succ_iff (k t : ℕ) (ht : Odd t) :
    t + 1 ∈ sumPrimeAndTwoPows (k + 1) ↔
      t ∈ sumPrimeAndTwoPows k ∨
        ∃ pows : Multiset ℕ, pows.card ≤ k + 1 ∧ 0 ∉ pows ∧
          t + 1 = 2 + (pows.map (2 ^ ·)).sum := by
  constructor
  · rintro ⟨p, pows, hp, hcard, hsum⟩
    by_cases h0 : 0 ∈ pows
    · refine Or.inl ⟨p, pows.erase 0, hp, ?_, ?_⟩
      · have hcons : (0 ::ₘ pows.erase 0).card = pows.card := by
          rw [Multiset.cons_erase h0]
        rw [Multiset.card_cons] at hcons
        omega
      · have hmap : pows.map (2 ^ ·) = 1 ::ₘ (pows.erase 0).map (2 ^ ·) := by
          conv_lhs => rw [← Multiset.cons_erase h0]
          simp [Multiset.map_cons]
        rw [hmap, Multiset.sum_cons] at hsum
        omega
    · refine Or.inr ⟨pows, hcard, h0, ?_⟩
      rcases dvd_two_sum_map_two_pow_of_zero_not_mem h0 with ⟨m, hm⟩
      rcases ht with ⟨r, rfl⟩
      have hp_mod : p % 2 = 0 := by omega
      have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) hp_mod
      omega
  · rintro (ht_mem | ⟨pows, hcard, -, hsum⟩)
    · exact add_one_mem_sumPrimeAndTwoPows_succ ht_mem
    · exact ⟨2, pows, Nat.prime_two, hcard, hsum.symm⟩


/-- The odd-`3` half of Granville–Soundararajan's conjecture implies the even-`4` half. -/
theorem granville_soundararajan_odd_implies_even
    (hodd : {n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3) :
    {n : ℕ | Even n ∧ n ≠ 0} ⊆ sumPrimeAndTwoPows 4 := by
  rintro n ⟨heven, hne0⟩
  rcases heven with ⟨m, rfl⟩
  have hm_pos : 1 ≤ m := by omega
  rcases eq_or_lt_of_le hm_pos with rfl | hm_gt1
  · exact prime_mem_sumPrimeAndTwoPows Nat.prime_two 4
  · have hpred_odd : Odd (m + m - 1) := ⟨m - 1, by omega⟩
    have hpred_gt1 : 1 < m + m - 1 := by omega
    have hpred_mem : m + m - 1 ∈ sumPrimeAndTwoPows 3 :=
      hodd ⟨hpred_odd, hpred_gt1⟩
    have hsucc : (m + m - 1) + 1 = m + m := by omega
    rw [← hsucc]
    exact add_one_mem_sumPrimeAndTwoPows_succ hpred_mem


/-- Granville–Soundararajan's full odd-`3`/even-`4` conjunction is equivalent to its odd-`3` half. -/
theorem granville_soundararajan_conj_iff_odd :
    ({n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3 ∧
      {n : ℕ | Even n ∧ n ≠ 0} ⊆ sumPrimeAndTwoPows 4) ↔
      {n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3 := by
  constructor
  · exact And.left
  · intro hodd
    exact ⟨hodd, granville_soundararajan_odd_implies_even hodd⟩


/-- Granville–Soundararajan's odd-`3`/even-`4` conjecture implies that every integer `n ≥ 2`
belongs to `sumPrimeAndTwoPows 4`. -/
theorem granville_soundararajan_implies_all_ge_two_mem_four
    (hgs : {n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3 ∧
      {n : ℕ | Even n ∧ n ≠ 0} ⊆ sumPrimeAndTwoPows 4) :
    ∀ n : ℕ, 2 ≤ n → n ∈ sumPrimeAndTwoPows 4 := by
  intro n hn2
  rcases Nat.even_or_odd n with heven | hodd
  · exact hgs.2 ⟨heven, by omega⟩
  · have hn_gt1 : 1 < n := by omega
    exact sumPrimeAndTwoPows_mono (by decide : 3 ≤ 4) (hgs.1 ⟨hodd, hn_gt1⟩)


/-- The odd-`3` hypothesis alone implies `n ∈ sumPrimeAndTwoPows 4` for all `n ≥ 2`. -/
theorem granville_soundararajan_odd_implies_all_ge_two_mem_four
    (hodd : {n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3) :
    ∀ n : ℕ, 2 ≤ n → n ∈ sumPrimeAndTwoPows 4 :=
  granville_soundararajan_implies_all_ge_two_mem_four
    (granville_soundararajan_conj_iff_odd.mpr hodd)


/-- Granville–Soundararajan's odd-`3` hypothesis implies the eventual representation statement of `erdos_10`
(witnessed at `k = 4` for all `n ≥ 2`). -/
theorem granville_soundararajan_implies_eventually_sumPrimeAndTwoPows
    (hodd : {n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3) :
    ∃ k : ℕ, ∀ᶠ n : ℕ in atTop, n ∈ sumPrimeAndTwoPows k := by
  refine ⟨4, eventually_atTop.mpr ⟨2, ?_⟩⟩
  exact granville_soundararajan_odd_implies_all_ge_two_mem_four hodd


/-! ## Section 2: Small-Cutoff Classifications and Concrete Witnesses -/

/-- Universal composite witness lemma: if `1 < d < m` and `m % d = 0`, then `m` is not prime. -/
theorem not_prime_of_mod_eq_zero_of_lt {m d : ℕ}
    (hd1 : 1 < d) (hdm : d < m) (hdvd : m % d = 0) : ¬ m.Prime := by
  intro hp
  have heq := hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hdvd)
  omega


/-- Universal factor-list certificate for `∀ a ∈ Finset.range B, ¬ (n - 2 ^ a).Prime`. -/
theorem not_eq_prime_add_two_pow_of_factor_list {n B : ℕ} (factors : Finset ℕ)
    (hB : n < 2 + 2 ^ B)
    (hcheck : ∀ a ∈ Finset.range B,
      ∃ d ∈ factors, 1 < d ∧ d < n - 2 ^ a ∧ (n - 2 ^ a) % d = 0) :
    ∀ p a : ℕ, p.Prime → n ≠ p + 2 ^ a := by
  apply not_eq_prime_add_two_pow_of_forall_lt hB
  intro a ha
  rcases hcheck a ha with ⟨d, -, hd1, hdm, hdvd⟩
  exact not_prime_of_mod_eq_zero_of_lt hd1 hdm hdvd


/-- Universal parity-transfer exclusion for `t + 1 = p + 2 ^ a + 2 ^ b` when `t` is odd
and avoids `p + 2 ^ a`. -/
theorem not_eq_prime_add_two_pow_add_two_pow_of_odd_pred {t B : ℕ}
    (hodd : t % 2 = 1)
    (hpred : ∀ p a : ℕ, p.Prime → t ≠ p + 2 ^ a)
    (hB : t < 1 + 2 ^ B)
    (hp2 : ∀ a ∈ Finset.range B, ∀ b ∈ Finset.range B, t + 1 ≠ 2 + 2 ^ a + 2 ^ b) :
    ∀ p a b : ℕ, p.Prime → t + 1 ≠ p + 2 ^ a + 2 ^ b := by
  intro p a b hp h
  rcases a with _ | a
  · exact hpred p b hp (by omega)
  · rcases b with _ | b
    · exact hpred p (a + 1) hp (by omega)
    · have ha2 : 2 ^ (a + 1) % 2 = 0 := by
        rw [Nat.pow_succ]
        omega
      have hb2 : 2 ^ (b + 1) % 2 = 0 := by
        rw [Nat.pow_succ]
        omega
      have hp_even : p % 2 = 0 := by omega
      have hp_eq_2 : p = 2 := by
        rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hp_even) with h1 | h2
        · omega
        · exact h2.symm
      subst hp_eq_2
      have ha1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
      have hb1 : 1 ≤ 2 ^ (b + 1) := Nat.one_le_two_pow
      have ha_lt : a + 1 < B :=
        (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp (by omega : 2 ^ (a + 1) < 2 ^ B)
      have hb_lt : b + 1 < B :=
        (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp (by omega : 2 ^ (b + 1) < 2 ^ B)
      exact hp2 (a + 1) (Finset.mem_range.mpr ha_lt) (b + 1) (Finset.mem_range.mpr hb_lt) h


/-- Exact classification of `sumPrimeAndTwoPows 0` up to `n = 20`. -/
theorem small_cutoff_sumPrimeAndTwoPows_zero_iff (n : ℕ) (hn : n ≤ 20) :
    n ∈ sumPrimeAndTwoPows 0 ↔ n ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ) := by
  rw [mem_sumPrimeAndTwoPows_zero_iff]
  revert n
  decide


/-- Exact small-cutoff classification for `k = 1`: for all `n ≤ 15`,
`n ∈ sumPrimeAndTwoPows 1` if and only if `2 ≤ n`. -/
theorem small_cutoff_sumPrimeAndTwoPows_one_iff (n : ℕ) (hn : n ≤ 15) :
    n ∈ sumPrimeAndTwoPows 1 ↔ 2 ≤ n := by
  constructor
  · exact two_le_of_mem_sumPrimeAndTwoPows
  · intro hn2
    apply mem_sumPrimeAndTwoPows_one_of_exists_lt (B := 4)
    revert hn2 hn n
    decide


/-- `16` is the smallest integer `n ≥ 2` not in `sumPrimeAndTwoPows 1`. -/
theorem sixteen_not_mem_sumPrimeAndTwoPows_one : 16 ∉ sumPrimeAndTwoPows 1 := by
  apply not_mem_sumPrimeAndTwoPows_one_of_forall_lt (B := 4)
  · decide
  · decide
  · decide


/-- `22` is the second even integer `n ≥ 2` not in `sumPrimeAndTwoPows 1`. -/
theorem twenty_two_not_mem_sumPrimeAndTwoPows_one : 22 ∉ sumPrimeAndTwoPows 1 := by
  apply not_mem_sumPrimeAndTwoPows_one_of_forall_lt (B := 5)
  · decide
  · decide
  · decide


/-- Exact small-cutoff classification for `k = 2`: for all `n ≤ 64`,
`n ∈ sumPrimeAndTwoPows 2` if and only if `2 ≤ n`. -/
theorem small_cutoff_sumPrimeAndTwoPows_two_iff (n : ℕ) (hn : n ≤ 64) :
    n ∈ sumPrimeAndTwoPows 2 ↔ 2 ≤ n := by
  constructor
  · exact two_le_of_mem_sumPrimeAndTwoPows
  · intro hn2
    apply mem_sumPrimeAndTwoPows_two_of_exists_lt (B := 6)
    revert hn2 hn n
    decide


/-- `105 = 3 × 5 × 7` is composite, so `105 ∉ sumPrimeAndTwoPows 0`. -/
theorem witness_105_not_mem_sumPrimeAndTwoPows_zero : 105 ∉ sumPrimeAndTwoPows 0 := by
  rw [mem_sumPrimeAndTwoPows_zero_iff]
  decide


/-- `105` belongs to `sumPrimeAndTwoPows 1` (since `105 = 103 + 2 ^ 1`, and in fact `105 - 2 ^ a`
is prime for every `1 ≤ a ≤ 6`). -/
theorem witness_105_mem_sumPrimeAndTwoPows_one : 105 ∈ sumPrimeAndTwoPows 1 := by
  have h103 : Nat.Prime 103 := by decide
  simpa using prime_add_two_pow_mem_sumPrimeAndTwoPows_one h103 1


/-- `127` is prime, hence lies in `sumPrimeAndTwoPows 0` (and `sumPrimeAndTwoPows 1`). -/
theorem witness_127_mem_sumPrimeAndTwoPows_zero : 127 ∈ sumPrimeAndTwoPows 0 :=
  prime_mem_sumPrimeAndTwoPows_zero (by decide)


/-- De Polignac counterexample `127`: `127` cannot be written as `p + 2 ^ a` for any prime `p`
and any exponent `a : ℕ`. -/
theorem witness_127_not_eq_prime_add_two_pow :
    ∀ p a : ℕ, p.Prime → 127 ≠ p + 2 ^ a := by
  apply not_eq_prime_add_two_pow_of_forall_lt (B := 7)
  · decide
  · decide


/-- `149` is prime, hence lies in `sumPrimeAndTwoPows 0` (and `sumPrimeAndTwoPows 1`). -/
theorem witness_149_mem_sumPrimeAndTwoPows_zero : 149 ∈ sumPrimeAndTwoPows 0 :=
  prime_mem_sumPrimeAndTwoPows_zero (by decide)


/-- De Polignac counterexample `149`: `149` cannot be written as `p + 2 ^ a` for any prime `p`
and any exponent `a : ℕ`. -/
theorem witness_149_not_eq_prime_add_two_pow :
    ∀ p a : ℕ, p.Prime → 149 ≠ p + 2 ^ a := by
  apply not_eq_prime_add_two_pow_of_forall_lt (B := 8)
  · decide
  · decide


/-- `905` cannot be written as `p + 2 ^ a` for any prime `p` and any `a : ℕ`. -/
theorem smallest_odd_composite_not_eq_prime_add_two_pow :
    ∀ p a : ℕ, p.Prime → 905 ≠ p + 2 ^ a := by
  apply not_eq_prime_add_two_pow_of_factor_list ({2, 3, 7, 11, 17, 29} : Finset ℕ) (B := 10)
  · decide
  · decide


/-- `905` is the smallest odd integer greater than `1` not in `sumPrimeAndTwoPows 1`. -/
theorem witness_905_not_mem_sumPrimeAndTwoPows_one : 905 ∉ sumPrimeAndTwoPows 1 := by
  rw [mem_sumPrimeAndTwoPows_one_iff]
  rintro (hp | ⟨p, a, hp, h⟩)
  · exact not_prime_of_mod_eq_zero_of_lt (d := 5) (by decide) (by decide) (by decide) hp
  · exact smallest_odd_composite_not_eq_prime_add_two_pow p a hp h


/-- `3` cannot be written as `p + 2 ^ a + 2 ^ b` for any prime `p` and `a, b : ℕ`. -/
theorem three_not_eq_prime_add_two_pow_add_two_pow :
    ∀ p a b : ℕ, p.Prime → 3 ≠ p + 2 ^ a + 2 ^ b := by
  apply not_eq_prime_add_two_pow_add_two_pow_of_forall_lt (B := 1)
  · decide
  · decide


/-- `128 = 127 + 1` cannot be written as `p + 2 ^ a + 2 ^ b` for any prime `p` and `a, b : ℕ`. -/
theorem witness_128_not_eq_prime_add_two_pow_add_two_pow :
    ∀ p a b : ℕ, p.Prime → 128 ≠ p + 2 ^ a + 2 ^ b := by
  apply not_eq_prime_add_two_pow_add_two_pow_of_odd_pred (t := 127) (B := 7)
    (by decide) witness_127_not_eq_prime_add_two_pow
  · decide
  · decide


/-- `150 = 149 + 1` cannot be written as `p + 2 ^ a + 2 ^ b` for any prime `p` and `a, b : ℕ`. -/
theorem witness_150_not_eq_prime_add_two_pow_add_two_pow :
    ∀ p a b : ℕ, p.Prime → 150 ≠ p + 2 ^ a + 2 ^ b := by
  apply not_eq_prime_add_two_pow_add_two_pow_of_odd_pred (t := 149) (B := 8)
    (by decide) witness_149_not_eq_prime_add_two_pow
  · decide
  · decide


/-- `906 = 905 + 1` cannot be written as `p + 2 ^ a + 2 ^ b` for any prime `p` and `a, b : ℕ`. -/
theorem smallest_even_not_eq_prime_add_two_pow_add_two_pow :
    ∀ p a b : ℕ, p.Prime → 906 ≠ p + 2 ^ a + 2 ^ b := by
  apply not_eq_prime_add_two_pow_add_two_pow_of_odd_pred (t := 905) (B := 10)
    (by decide) smallest_odd_composite_not_eq_prime_add_two_pow
  · decide
  · decide


/-- `906` does not belong to `sumPrimeAndTwoPows 1`. -/
theorem witness_906_not_mem_sumPrimeAndTwoPows_one : 906 ∉ sumPrimeAndTwoPows 1 := by
  apply not_mem_sumPrimeAndTwoPows_one_of_forall_lt (B := 10)
  · exact not_prime_of_mod_eq_zero_of_lt (d := 2) (by decide) (by decide) (by decide)
  · decide
  · intro a ha
    have ha_lt : a < 10 := Finset.mem_range.mp ha
    rcases a with _ | a
    · exact not_prime_of_mod_eq_zero_of_lt (d := 5) (by decide) (by decide) (by decide)
    · have h2 : (906 - 2 ^ (a + 1)) % 2 = 0 := by
        have hle : 2 ^ (a + 1) ≤ 512 :=
          Nat.pow_le_pow_right (by omega) (by omega : a + 1 ≤ 9)
        have hmod : 2 ^ (a + 1) % 2 = 0 := by
          rw [Nat.pow_succ]
          omega
        omega
      have hlt : 2 < 906 - 2 ^ (a + 1) := by
        have hle : 2 ^ (a + 1) ≤ 512 :=
          Nat.pow_le_pow_right (by omega) (by omega : a + 1 ≤ 9)
        omega
      exact not_prime_of_mod_eq_zero_of_lt (by decide) hlt h2


/-- `906` is the smallest integer `n ≥ 2` not in `sumPrimeAndTwoPows 2`. -/
theorem witness_906_not_mem_sumPrimeAndTwoPows_two : 906 ∉ sumPrimeAndTwoPows 2 := by
  rw [mem_sumPrimeAndTwoPows_two_iff]
  rintro (h1 | ⟨p, a, b, hp, h⟩)
  · exact witness_906_not_mem_sumPrimeAndTwoPows_one h1
  · exact smallest_even_not_eq_prime_add_two_pow_add_two_pow p a b hp h


/-! ## Section 3: Erdős / Bogdanov / Crocker Covering-System Exclusions for `k = 1, 2, 3` -/

/-- For every `a : ℕ`, `2 ^ a % 3` is `1` or `2`. -/
theorem pow_two_mod_three_mem (a : ℕ) : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2 := by
  induction a with
  | zero => decide
  | succ a ih =>
    rw [Nat.pow_succ]
    omega


/-- For every `a : ℕ`, `2 ^ a % 7` is `1`, `2`, or `4`. -/
theorem pow_two_mod_seven_mem (a : ℕ) :
    2 ^ a % 7 = 1 ∨ 2 ^ a % 7 = 2 ∨ 2 ^ a % 7 = 4 := by
  induction a with
  | zero => decide
  | succ a ih =>
    rw [Nat.pow_succ]
    omega


/-- Covering clause 1 (`mod 2`): `a % 2 = 0 → 2 ^ a % 3 = 1`. -/
theorem pow_two_mod_three_of_mod_two_eq_zero {a : ℕ} (ha : a % 2 = 0) :
    2 ^ a % 3 = 1 := by
  have hdiv : a = 2 * (a / 2) := by omega
  rw [hdiv]
  induction (a / 2) with
  | zero => decide
  | succ k ih =>
    rw [Nat.mul_succ, Nat.pow_add]
    omega


/-- Covering clause 2 (`mod 3`): `a % 3 = 0 → 2 ^ a % 7 = 1`. -/
theorem pow_two_mod_seven_of_mod_three_eq_zero {a : ℕ} (ha : a % 3 = 0) :
    2 ^ a % 7 = 1 := by
  have hdiv : a = 3 * (a / 3) := by omega
  rw [hdiv]
  induction (a / 3) with
  | zero => decide
  | succ k ih =>
    rw [Nat.mul_succ, Nat.pow_add]
    omega


/-- Covering clause 3 (`mod 4`): `a % 4 = 1 → 2 ^ a % 5 = 2`. -/
theorem pow_two_mod_five_of_mod_four_eq_one {a : ℕ} (ha : a % 4 = 1) :
    2 ^ a % 5 = 2 := by
  have hdiv : a = 4 * (a / 4) + 1 := by omega
  rw [hdiv]
  induction (a / 4) with
  | zero => decide
  | succ k ih =>
    have hstep : 4 * (k + 1) + 1 = (4 * k + 1) + 4 := by omega
    rw [hstep, Nat.pow_add]
    omega


/-- Covering clause 4 (`mod 8`): `a % 8 = 3 → 2 ^ a % 17 = 8`. -/
theorem pow_two_mod_seventeen_of_mod_eight_eq_three {a : ℕ} (ha : a % 8 = 3) :
    2 ^ a % 17 = 8 := by
  have hdiv : a = 8 * (a / 8) + 3 := by omega
  rw [hdiv]
  induction (a / 8) with
  | zero => decide
  | succ k ih =>
    have hstep : 8 * (k + 1) + 3 = (8 * k + 3) + 8 := by omega
    rw [hstep, Nat.pow_add]
    omega


/-- Covering clause 5 (`mod 12`): `a % 12 = 7 → 2 ^ a % 13 = 11`. -/
theorem pow_two_mod_thirteen_of_mod_twelve_eq_seven {a : ℕ} (ha : a % 12 = 7) :
    2 ^ a % 13 = 11 := by
  have hdiv : a = 12 * (a / 12) + 7 := by omega
  rw [hdiv]
  induction (a / 12) with
  | zero => decide
  | succ k ih =>
    have hstep : 12 * (k + 1) + 7 = (12 * k + 7) + 12 := by omega
    rw [hstep, Nat.pow_add]
    omega


/-- Covering clause 6 (`mod 24`): `a % 24 = 23 → 2 ^ a % 241 = 121`. -/
theorem pow_two_mod_241_of_mod_24_eq_23 {a : ℕ} (ha : a % 24 = 23) :
    2 ^ a % 241 = 121 := by
  have hdiv : a = 24 * (a / 24) + 23 := by omega
  rw [hdiv]
  induction (a / 24) with
  | zero => decide
  | succ k ih =>
    have hstep : 24 * (k + 1) + 23 = (24 * k + 23) + 24 := by omega
    rw [hstep, Nat.pow_add]
    have h24 : 2 ^ 24 % 241 = 1 := by decide
    rw [Nat.mul_mod, ih, h24]


/-- Erdős's mod-`24` covering system of `ℕ`: every exponent `a : ℕ` satisfies at least one
of the six congruence clauses with moduli `2, 3, 4, 8, 12, 24`. -/
theorem erdos_mod24_exponent_cover (a : ℕ) :
    a % 2 = 0 ∨ a % 3 = 0 ∨ a % 4 = 1 ∨ a % 8 = 3 ∨ a % 12 = 7 ∨ a % 24 = 23 := by
  omega


/-- If `(p + 2 ^ a) % 3 = 1`, then `p` cannot equal `7`, `13`, or `241` (all `≡ 1 (mod 3)`). -/
theorem ne_seven_thirteen_241_of_mod_three {n p a : ℕ}
    (h3 : n % 3 = 1) (hn : n = p + 2 ^ a) :
    p ≠ 7 ∧ p ≠ 13 ∧ p ≠ 241 := by
  have hm3 := pow_two_mod_three_mem a
  omega


/-- If `(p + 2 ^ a) % 7 = 1`, then `p` cannot equal `3`, `5`, or `17`. -/
theorem ne_three_five_seventeen_of_mod_seven {n p a : ℕ}
    (h7 : n % 7 = 1) (hn : n = p + 2 ^ a) :
    p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 17 := by
  have hm7 := pow_two_mod_seven_mem a
  omega


/-- Universal Erdős covering-system exclusion for `p + 2 ^ a`: any integer `n` satisfying
the six covering congruences mod `3, 7, 5, 17, 13, 241` cannot be written as `p + 2 ^ a`
for any prime `p` and any exponent `a : ℕ`. -/
theorem not_eq_prime_add_two_pow_of_erdos_cover {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121) :
    ∀ p a : ℕ, p.Prime → n ≠ p + 2 ^ a := by
  intro p a hp hn
  rcases ne_seven_thirteen_241_of_mod_three h3 hn with ⟨hp_not_7, hp_not_13, hp_not_241⟩
  rcases ne_three_five_seventeen_of_mod_seven h7 hn with ⟨hp_not_3, hp_not_5, hp_not_17⟩
  rcases erdos_mod24_exponent_cover a with ha2 | ha3 | ha4 | ha8 | ha12 | ha24
  · have hpow := pow_two_mod_three_of_mod_two_eq_zero ha2
    have hpmod : p % 3 = 0 := by clear h7 h5 h17 h13 h241; omega
    exact hp_not_3 (eq_of_prime_of_mod_eq_zero hp (by omega) hpmod)
  · have hpow := pow_two_mod_seven_of_mod_three_eq_zero ha3
    have hpmod : p % 7 = 0 := by clear h3 h5 h17 h13 h241; omega
    exact hp_not_7 (eq_of_prime_of_mod_eq_zero hp (by omega) hpmod)
  · have hpow := pow_two_mod_five_of_mod_four_eq_one ha4
    have hpmod : p % 5 = 0 := by clear h3 h7 h17 h13 h241; omega
    exact hp_not_5 (eq_of_prime_of_mod_eq_zero hp (by omega) hpmod)
  · have hpow := pow_two_mod_seventeen_of_mod_eight_eq_three ha8
    have hpmod : p % 17 = 0 := by clear h3 h7 h5 h13 h241; omega
    exact hp_not_17 (eq_of_prime_of_mod_eq_zero hp (by omega) hpmod)
  · have hpow := pow_two_mod_thirteen_of_mod_twelve_eq_seven ha12
    have hpmod : p % 13 = 0 := by clear h3 h7 h5 h17 h241; omega
    exact hp_not_13 (eq_of_prime_of_mod_eq_zero hp (by omega) hpmod)
  · have hpow := pow_two_mod_241_of_mod_24_eq_23 ha24
    have hpmod : p % 241 = 0 := by clear h3 h7 h5 h17 h13; omega
    exact hp_not_241 (eq_of_prime_of_mod_eq_zero hp (by omega) hpmod)


/-- Diagonal (`a = b`) exclusion for `k = 2` under the Erdős mod-`24` covering system:
since `2 ^ a + 2 ^ a = 2 ^ (a + 1)`, no integer satisfying the six covering congruences
can be written as `p + 2 ^ a + 2 ^ a` with `p` prime. -/
theorem not_eq_prime_add_two_pow_diag_of_erdos_cover {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121) :
    ∀ p a : ℕ, p.Prime → n ≠ p + 2 ^ a + 2 ^ a := by
  intro p a hp hn
  have hstep : p + 2 ^ a + 2 ^ a = p + 2 ^ (a + 1) := by
    rw [Nat.pow_succ]
    omega
  exact not_eq_prime_add_two_pow_of_erdos_cover h3 h7 h5 h17 h13 h241 p (a + 1) hp ( hn.trans hstep )


/-- Under the Erdős mod-`24` covering system, any representation `n = p + 2 ^ a + 2 ^ b`
with `p` prime must have distinct exponents `a ≠ b`. -/
theorem ne_exponents_of_prime_add_two_pows_of_erdos_cover {n p a b : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121)
    (hp : p.Prime) (hn : n = p + 2 ^ a + 2 ^ b) :
    a ≠ b := by
  rintro rfl
  exact not_eq_prime_add_two_pow_diag_of_erdos_cover h3 h7 h5 h17 h13 h241 p a hp hn


/-- Universal Erdős covering-system exclusion for `sumPrimeAndTwoPows 1`: adding `n % 11 = 0`
rules out `n.Prime` as well (since `11 % 3 = 2 ≠ 1`), so `n ∉ sumPrimeAndTwoPows 1`. -/
theorem not_mem_sumPrimeAndTwoPows_one_of_erdos_cover {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121)
    (h11 : n % 11 = 0) :
    n ∉ sumPrimeAndTwoPows 1 := by
  rw [mem_sumPrimeAndTwoPows_one_iff]
  rintro (hp | ⟨p, a, hp, h⟩)
  · have hn11 : n = 11 := eq_of_prime_of_mod_eq_zero hp (by omega) h11
    clear h7 h5 h17 h13 h241 h11
    omega
  · exact not_eq_prime_add_two_pow_of_erdos_cover h3 h7 h5 h17 h13 h241 p a hp h


/-- Every term of the arithmetic progression `399097567 + 492131640 * t` is odd and
lies outside `sumPrimeAndTwoPows 1`. -/
theorem erdos_cover_progression_not_mem_sumPrimeAndTwoPows_one (t : ℕ) :
    Odd (399097567 + 492131640 * t) ∧
      399097567 + 492131640 * t ∉ sumPrimeAndTwoPows 1 := by
  refine ⟨⟨199548783 + 246065820 * t, by omega⟩, ?_⟩
  apply not_mem_sumPrimeAndTwoPows_one_of_erdos_cover <;> omega


/-- Erdős (1950): there are infinitely many odd integers not in `sumPrimeAndTwoPows 1`. -/
theorem odd_not_mem_sumPrimeAndTwoPows_one_infinite :
    Set.Infinite ({n : ℕ | Odd n} \ sumPrimeAndTwoPows 1) := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ => 399097567 + 492131640 * t) ?_ ?_
  · intro t₁ t₂ h
    dsimp at h
    omega
  · intro t
    exact erdos_cover_progression_not_mem_sumPrimeAndTwoPows_one t


/-- Exact case split on `2 ^ a` for `mod 8` arithmetic. -/
theorem pow_two_mod_eight_cases (a : ℕ) :
    (a = 0 ∧ 2 ^ a = 1) ∨ (a = 1 ∧ 2 ^ a = 2) ∨ (a = 2 ∧ 2 ^ a = 4) ∨
      (1 ≤ a ∧ 2 ^ a % 8 = 0) := by
  rcases a with _ | _ | _ | a
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · right; right; right
    refine ⟨by omega, ?_⟩
    have hadd : a + 1 + 1 + 1 = a + 3 := by omega
    rw [hadd, Nat.pow_add]
    omega


/-- Parity-transfer converse for `k = 2`: for any `t ≡ 7 (mod 8)` with `t ≠ 7`,
`t + 1 ∈ sumPrimeAndTwoPows 2` if and only if `t ∈ sumPrimeAndTwoPows 1`. -/
theorem even_succ_mem_sumPrimeAndTwoPows_two_iff_of_mod_eight_eq_seven {t : ℕ}
    (ht8 : t % 8 = 7) (ht7 : t ≠ 7) :
    t + 1 ∈ sumPrimeAndTwoPows 2 ↔ t ∈ sumPrimeAndTwoPows 1 := by
  constructor
  · intro h
    rw [mem_sumPrimeAndTwoPows_two_iff] at h
    rcases h with h1 | ⟨p, a, b, hp, hab⟩
    · rw [mem_sumPrimeAndTwoPows_one_iff] at h1
      rcases h1 with hp | ⟨p, a, hp, ha⟩
      · exfalso
        have hp2 : t + 1 = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
        omega
      · rcases pow_two_mod_eight_cases a with ⟨rfl, hpow⟩ | ⟨rfl, hpow⟩ | ⟨rfl, hpow⟩ | ⟨-, hpow⟩
        · have htp : t = p := by omega
          rw [htp]
          exact prime_mem_sumPrimeAndTwoPows hp 1
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
    · rcases pow_two_mod_eight_cases a with ⟨rfl, ha_pow⟩ | ⟨rfl, ha_pow⟩ | ⟨rfl, ha_pow⟩ | ⟨-, ha_pow⟩
      · have htb : t = p + 2 ^ b := by omega
        rw [htb]
        exact prime_add_two_pow_mem_sumPrimeAndTwoPows_one hp b
      · rcases pow_two_mod_eight_cases b with ⟨rfl, hb_pow⟩ | ⟨rfl, hb_pow⟩ | ⟨rfl, hb_pow⟩ | ⟨-, hb_pow⟩
        · have hta : t = p + 2 ^ 1 := by omega
          rw [hta]
          exact prime_add_two_pow_mem_sumPrimeAndTwoPows_one hp 1
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
      · rcases pow_two_mod_eight_cases b with ⟨rfl, hb_pow⟩ | ⟨rfl, hb_pow⟩ | ⟨rfl, hb_pow⟩ | ⟨-, hb_pow⟩
        · have hta : t = p + 2 ^ 2 := by omega
          rw [hta]
          exact prime_add_two_pow_mem_sumPrimeAndTwoPows_one hp 2
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
      · rcases pow_two_mod_eight_cases b with ⟨rfl, hb_pow⟩ | ⟨rfl, hb_pow⟩ | ⟨rfl, hb_pow⟩ | ⟨-, hb_pow⟩
        · have hta : t = p + 2 ^ a := by omega
          rw [hta]
          exact prime_add_two_pow_mem_sumPrimeAndTwoPows_one hp a
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · exfalso
          have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
  · exact add_one_mem_sumPrimeAndTwoPows_succ


/-- Every term of the even progression `399097568 + 492131640 * t` is even and
lies outside `sumPrimeAndTwoPows 2`. -/
theorem erdos_cover_even_progression_not_mem_sumPrimeAndTwoPows_two (t : ℕ) :
    Even (399097568 + 492131640 * t) ∧
      399097568 + 492131640 * t ∉ sumPrimeAndTwoPows 2 := by
  refine ⟨⟨199548784 + 246065820 * t, by omega⟩, ?_⟩
  have hsucc : 399097568 + 492131640 * t = (399097567 + 492131640 * t) + 1 := by omega
  rw [hsucc, even_succ_mem_sumPrimeAndTwoPows_two_iff_of_mod_eight_eq_seven (by omega) (by omega)]
  exact (erdos_cover_progression_not_mem_sumPrimeAndTwoPows_one t).2


/-- Complete unconditional proof of `erdos_10.variants.two_pows`:
there are infinitely many even integers not in `sumPrimeAndTwoPows 2`. -/
theorem even_not_mem_sumPrimeAndTwoPows_two_infinite :
    Set.Infinite ({n : ℕ | Even n} \ sumPrimeAndTwoPows 2) := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ => 399097568 + 492131640 * t) ?_ ?_
  · intro t₁ t₂ h
    dsimp at h
    omega
  · intro t
    exact erdos_cover_even_progression_not_mem_sumPrimeAndTwoPows_two t


/-- Exact case split on `2 ^ a` for `mod 16` arithmetic. -/
theorem pow_two_mod_sixteen_cases (a : ℕ) :
    (a = 0 ∧ 2 ^ a = 1) ∨ (a = 1 ∧ 2 ^ a = 2) ∨ (a = 2 ∧ 2 ^ a = 4) ∨
      (a = 3 ∧ 2 ^ a = 8) ∨ (1 ≤ a ∧ 2 ^ a % 16 = 0) := by
  rcases a with _ | _ | _ | _ | a
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · right; right; right; right
    refine ⟨by omega, ?_⟩
    have hadd : a + 1 + 1 + 1 + 1 = a + 4 := by omega
    rw [hadd, Nat.pow_add]
    omega


/-- If `a ≥ 1`, then `2 ^ a % 2 = 0`. -/
theorem pow_two_mod_two_of_one_le {a : ℕ} (ha : 1 ≤ a) : 2 ^ a % 2 = 0 := by
  rcases a with _ | a
  · omega
  · rw [Nat.pow_succ]
    omega


/-- `15 = 13 + 2 ^ 0 + 2 ^ 0` belongs to `sumPrimeAndTwoPows 2`. -/
theorem fifteen_mem_sumPrimeAndTwoPows_two : 15 ∈ sumPrimeAndTwoPows 2 := by
  have h13 : Nat.Prime 13 := by decide
  simpa using prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two h13 0 0


/-- Crocker–Grechuk parity-transfer equivalence for `k = 3`: for every `t ≡ 15 (mod 16)`,
`t + 1 ∈ sumPrimeAndTwoPows 3` if and only if `t ∈ sumPrimeAndTwoPows 2`. -/
theorem even_succ_mem_sumPrimeAndTwoPows_three_iff_of_mod_sixteen_eq_fifteen {t : ℕ}
    (ht16 : t % 16 = 15) :
    t + 1 ∈ sumPrimeAndTwoPows 3 ↔ t ∈ sumPrimeAndTwoPows 2 := by
  constructor
  · intro h
    by_cases ht15 : t = 15
    · subst ht15
      exact fifteen_mem_sumPrimeAndTwoPows_two
    · rw [mem_sumPrimeAndTwoPows_three_iff] at h
      rcases h with h2 | ⟨p, a, b, c, hp, habc⟩
      · have ht8 : t % 8 = 7 := by omega
        have ht7 : t ≠ 7 := by omega
        exact sumPrimeAndTwoPows_mono (by decide : 1 ≤ 2)
          ((even_succ_mem_sumPrimeAndTwoPows_two_iff_of_mod_eight_eq_seven ht8 ht7).mp h2)
      · by_cases ha0 : a = 0
        · subst ha0
          have hbc : t = p + 2 ^ b + 2 ^ c := by omega
          rw [hbc]
          exact prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two hp b c
        · by_cases hb0 : b = 0
          · subst hb0
            have hac : t = p + 2 ^ a + 2 ^ c := by omega
            rw [hac]
            exact prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two hp a c
          · by_cases hc0 : c = 0
            · subst hc0
              have hab : t = p + 2 ^ a + 2 ^ b := by omega
              rw [hab]
              exact prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two hp a b
            · exfalso
              have ha2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ a)
              have hb2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ b)
              have hc2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ c)
              have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
              have ha16 := pow_two_mod_sixteen_cases a
              have hb16 := pow_two_mod_sixteen_cases b
              have hc16 := pow_two_mod_sixteen_cases c
              omega
  · exact add_one_mem_sumPrimeAndTwoPows_succ


/-- Crocker–Grechuk reduction (`erdos_10.variants.grechuk`): Crocker's theorem that infinitely many
`t ≡ 15 (mod 16)` lie outside `sumPrimeAndTwoPows 2` implies that infinitely many even integers
lie outside `sumPrimeAndTwoPows 3`. -/
theorem crocker_implies_grechuk_even_not_mem_sumPrimeAndTwoPows_three_infinite
    (hcrocker : Set.Infinite {t : ℕ | t % 16 = 15 ∧ t ∉ sumPrimeAndTwoPows 2}) :
    Set.Infinite ({n : ℕ | Even n} \ sumPrimeAndTwoPows 3) := by
  refine Set.Infinite.mono ?_ (hcrocker.image (f := fun t : ℕ => t + 1) ?_)
  · rintro m ⟨t, ⟨ht16, ht2⟩, rfl⟩
    dsimp
    refine ⟨⟨t / 2 + 1, by omega⟩, ?_⟩
    rw [even_succ_mem_sumPrimeAndTwoPows_three_iff_of_mod_sixteen_eq_fifteen ht16]
    exact ht2
  · intro t₁ _ t₂ _ h
    dsimp at h
    omega


end Erdos10


/-!
# Erdős Problem 10: Crocker's Fermat-Factor Covering Bridge, Unconditional Grechuk Theorems, and `k = 3, 4` Reductions

Completes the Crocker-to-Grechuk bridge and proves the explicit Grechuk witness:
1. Establishes the exact universal equivalence `odd_not_mem_sumPrimeAndTwoPows_two_iff_mem_erdos9A`
   bridging `Erdos10.sumPrimeAndTwoPows 2` and `Erdos9.Erdos9A` for composite odd integers `n ≠ 3`
   (with the boundary separation witness `3 ∈ Erdos9.Erdos9A ∩ sumPrimeAndTwoPows 0`), and connects
   Crocker's Fermat-factor sequence `Erdos9.crockerN t` to discharge the premise
   `Set.Infinite {t : ℕ | t % 16 = 15 ∧ t ∉ sumPrimeAndTwoPows 2}` of
   `crocker_implies_grechuk_even_not_mem_sumPrimeAndTwoPows_three_infinite` unconditionally,
   yielding an unconditional, axiom-clean proof of `erdos_10.variants.grechuk`
   (`Set.Infinite ({n : ℕ | Even n} \ sumPrimeAndTwoPows 3)`).
2. Proves the universal mod-`512` parity-transfer equivalence
   `even_succ_mem_sumPrimeAndTwoPows_three_iff_of_mod_512_eq_361` (`t % 512 = 361 →
   (t + 1 ∈ sumPrimeAndTwoPows 3 ↔ t ∈ sumPrimeAndTwoPows 2)`), the symmetric factor-list
   certificate bridge `not_eq_prime_add_two_pow_add_two_pow_of_factor_list`, and an unconditional
   proof of Bogdan Grechuk's concrete observation `erdos_10.variants.grechuk_example`
   (`1117175146 ∉ sumPrimeAndTwoPows 3`), paired with the sharp positive controls
   `1117175145 ∈ sumPrimeAndTwoPows 3 \ sumPrimeAndTwoPows 2`,
   `1117175146 ∈ sumPrimeAndTwoPows 4 \ sumPrimeAndTwoPows 3`,
   `905 ∈ sumPrimeAndTwoPows 2 \ sumPrimeAndTwoPows 1`, and
   `906 ∈ sumPrimeAndTwoPows 3 \ sumPrimeAndTwoPows 2`.
3. Formalizes the `sumPrimeAndTwoPows 4` recursive decomposition, universal logarithmic
   exponent-bound certificates for `k = 3`, finite-horizon Granville–Soundararajan verification
   up to `200`, and partial-density monotonicity for Gallagher's theorem.
-/

namespace Erdos10

/-! ## Section 1: Universal `Erdos9A` Bridge, Crocker's Sequence, and `erdos_10.variants.grechuk` -/

/-- Universal equivalence bridging `sumPrimeAndTwoPows 2` and `Erdos9.Erdos9A`:
for every odd composite integer `n ≠ 3`, `n ∉ sumPrimeAndTwoPows 2` if and only if
`n ∈ Erdos9.Erdos9A` (since any `n = p + 2 ^ a` with `a ≥ 1` splits as
`p + 2 ^ (a - 1) + 2 ^ (a - 1)`). -/
theorem odd_not_mem_sumPrimeAndTwoPows_two_iff_mem_erdos9A {n : ℕ}
    (hodd : Odd n) (hne3 : n ≠ 3) (hnp : ¬ n.Prime) :
    n ∉ sumPrimeAndTwoPows 2 ↔ n ∈ Erdos9.Erdos9A := by
  rw [mem_sumPrimeAndTwoPows_two_iff, mem_sumPrimeAndTwoPows_one_iff, Erdos9.erdos9A_eq_setOf]
  constructor
  · intro hnot
    refine ⟨hodd, ?_⟩
    rintro ⟨p, k, l, hp, heq⟩
    exact hnot (Or.inr ⟨p, k, l, hp, heq⟩)
  · rintro ⟨-, hnot9⟩ ((hp | ⟨p, a, hp, heq⟩) | ⟨p, a, b, hp, heq⟩)
    · exact hnp hp
    · rcases a with _ | a
      · rcases hodd with ⟨m, hm⟩
        have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
        omega
      · apply hnot9 ⟨p, a, a, hp, ?_⟩
        rw [heq, Nat.pow_succ]
        omega
    · exact hnot9 ⟨p, a, b, hp, heq⟩


/-- Boundary separation control showing why `n ≠ 3` is required in
`odd_not_mem_sumPrimeAndTwoPows_two_iff_mem_erdos9A`: `3` belongs to `Erdos9.Erdos9A`
(as `3 < 4`), yet `3 = 3 + 0 ∈ sumPrimeAndTwoPows 0 ⊆ sumPrimeAndTwoPows 2`. -/
theorem three_mem_erdos9A_and_mem_sumPrimeAndTwoPows_zero :
    3 ∈ Erdos9.Erdos9A ∧ 3 ∈ sumPrimeAndTwoPows 0 ∧ 3 ∈ sumPrimeAndTwoPows 2 :=
  ⟨Erdos9.erdos9A_contains_three,
   prime_mem_sumPrimeAndTwoPows_zero Nat.prime_three,
   prime_mem_sumPrimeAndTwoPows Nat.prime_three 2⟩


/-- Every term `Erdos9.crockerN t` is divisible by the 0-th Fermat number `F_0 = 3`. -/
theorem three_dvd_crockerN (t : ℕ) : 3 ∣ Erdos9.crockerN t := by
  have hr : 0 < Erdos9.crockerExp t := by
    unfold Erdos9.crockerExp
    omega
  have hdvd := Erdos9.crockerB_dvd_crockerN hr
  have hB0 : Erdos9.crockerB 0 = 3 := rfl
  rw [hB0] at hdvd
  exact hdvd


/-- Every term `Erdos9.crockerN t` is at least `45` (`15 * F_0 ≤ crockerN t`). -/
theorem forty_five_le_crockerN (t : ℕ) : 45 ≤ Erdos9.crockerN t := by
  have hr : 0 < Erdos9.crockerExp t := by
    unfold Erdos9.crockerExp
    omega
  have hle := Erdos9.fifteen_mul_crockerB_le_crockerN hr
  have hB0 : Erdos9.crockerB 0 = 3 := rfl
  rw [hB0] at hle
  omega


/-- Every term `Erdos9.crockerN t` is composite (`3 ∣ crockerN t` and `45 ≤ crockerN t`). -/
theorem not_prime_crockerN (t : ℕ) : ¬ (Erdos9.crockerN t).Prime := by
  have hdvd := three_dvd_crockerN t
  have hle := forty_five_le_crockerN t
  exact Erdos9.not_prime_of_dvd_of_lt (by decide : 1 < 3) (by omega) hdvd


/-- For every `t, p, a : ℕ` with `p` prime, `Erdos9.crockerN t ≠ p + 2 ^ a`. -/
theorem crockerN_not_eq_prime_add_two_pow (t p a : ℕ) (hp : p.Prime) :
    Erdos9.crockerN t ≠ p + 2 ^ a := by
  intro heq
  have hsub : Erdos9.crockerN t - 2 ^ a = p := by omega
  apply Erdos9.not_prime_crockerN_sub_two_pow t a
  rw [hsub]
  exact hp


/-- Every term `Erdos9.crockerN t` lies outside `sumPrimeAndTwoPows 1`. -/
theorem crockerN_not_mem_sumPrimeAndTwoPows_one (t : ℕ) :
    Erdos9.crockerN t ∉ sumPrimeAndTwoPows 1 := by
  rw [mem_sumPrimeAndTwoPows_one_iff]
  rintro (hp | ⟨p, a, hp, heq⟩)
  · exact not_prime_crockerN t hp
  · exact crockerN_not_eq_prime_add_two_pow t p a hp heq


/-- For every `t, p, a, b : ℕ` with `p` prime, `Erdos9.crockerN t ≠ p + 2 ^ a + 2 ^ b`. -/
theorem crockerN_not_eq_prime_add_two_pow_add_two_pow (t p a b : ℕ) (hp : p.Prime) :
    Erdos9.crockerN t ≠ p + 2 ^ a + 2 ^ b := by
  intro heq
  exact (Erdos9.crockerN_mem_erdos9A t).2 ⟨p, a, b, hp, heq⟩


/-- Every term `Erdos9.crockerN t` lies outside `sumPrimeAndTwoPows 2`. -/
theorem crockerN_not_mem_sumPrimeAndTwoPows_two (t : ℕ) :
    Erdos9.crockerN t ∉ sumPrimeAndTwoPows 2 := by
  rw [mem_sumPrimeAndTwoPows_two_iff]
  rintro (h1 | ⟨p, a, b, hp, heq⟩)
  · exact crockerN_not_mem_sumPrimeAndTwoPows_one t h1
  · exact crockerN_not_eq_prime_add_two_pow_add_two_pow t p a b hp heq


/-- Every term `Erdos9.crockerN t` satisfies `crockerN t % 16 = 15` and
`crockerN t ∉ sumPrimeAndTwoPows 2`. -/
theorem crockerN_mod_sixteen_and_not_mem_sumPrimeAndTwoPows_two (t : ℕ) :
    Erdos9.crockerN t % 16 = 15 ∧ Erdos9.crockerN t ∉ sumPrimeAndTwoPows 2 :=
  ⟨Erdos9.crockerN_mod_sixteen t, crockerN_not_mem_sumPrimeAndTwoPows_two t⟩


/-- Unconditional proof of Crocker's (1971) `t ≡ 15 (mod 16)` theorem for `sumPrimeAndTwoPows 2`,
discharging the premise of `crocker_implies_grechuk_even_not_mem_sumPrimeAndTwoPows_three_infinite`:
there are infinitely many odd integers `t ≡ 15 (mod 16)` not in `sumPrimeAndTwoPows 2`. -/
theorem crocker_odd_mod_sixteen_not_mem_sumPrimeAndTwoPows_two_infinite :
    Set.Infinite {t : ℕ | t % 16 = 15 ∧ t ∉ sumPrimeAndTwoPows 2} :=
  Set.infinite_of_injective_forall_mem
    Erdos9.crockerN_strictMono.injective
    crockerN_mod_sixteen_and_not_mem_sumPrimeAndTwoPows_two


/-- For every `t : ℕ`, `Erdos9.crockerN t + 1` is an even integer not in `sumPrimeAndTwoPows 3`. -/
theorem crockerN_succ_even_and_not_mem_sumPrimeAndTwoPows_three (t : ℕ) :
    Even (Erdos9.crockerN t + 1) ∧ Erdos9.crockerN t + 1 ∉ sumPrimeAndTwoPows 3 := by
  have h16 : Erdos9.crockerN t % 16 = 15 := Erdos9.crockerN_mod_sixteen t
  refine ⟨⟨Erdos9.crockerN t / 2 + 1, by omega⟩, ?_⟩
  rw [even_succ_mem_sumPrimeAndTwoPows_three_iff_of_mod_sixteen_eq_fifteen h16]
  exact crockerN_not_mem_sumPrimeAndTwoPows_two t


/-- Unconditional proof that there are infinitely many even integers not in `sumPrimeAndTwoPows 3`. -/
theorem even_not_mem_sumPrimeAndTwoPows_three_infinite :
    Set.Infinite ({n : ℕ | Even n} \ sumPrimeAndTwoPows 3) :=
  crocker_implies_grechuk_even_not_mem_sumPrimeAndTwoPows_three_infinite
    crocker_odd_mod_sixteen_not_mem_sumPrimeAndTwoPows_two_infinite


/-- Complete unconditional proof of `erdos_10.variants.grechuk` in
`FormalConjectures/ErdosProblems/10.lean`: there are infinitely many even integers
not expressible as the sum of a prime and at most `3` powers of `2`. -/
theorem grechuk :
    Set.Infinite <| {n : ℕ | Even n} \ sumPrimeAndTwoPows 3 :=
  even_not_mem_sumPrimeAndTwoPows_three_infinite


/-- Explicit unbounded even witness outside `sumPrimeAndTwoPows 3`: for every `N : ℕ`,
there exists an even integer `n > N` with `n ∉ sumPrimeAndTwoPows 3`. -/
theorem exists_even_gt_not_mem_sumPrimeAndTwoPows_three (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Even n ∧ n ∉ sumPrimeAndTwoPows 3 := by
  refine ⟨Erdos9.crockerN N + 1, ?_, crockerN_succ_even_and_not_mem_sumPrimeAndTwoPows_three N⟩
  have hle : N ≤ Erdos9.crockerN N := Erdos9.crockerN_strictMono.id_le N
  omega


/-! ## Section 2: Mod-512 Parity-Transfer Equivalence & `erdos_10.variants.grechuk_example` -/

/-- Exact case split on `2 ^ a` for `mod 512` arithmetic. -/
theorem pow_two_mod_512_cases (a : ℕ) :
    (a = 0 ∧ 2 ^ a = 1) ∨ (a = 1 ∧ 2 ^ a = 2) ∨ (a = 2 ∧ 2 ^ a = 4) ∨
    (a = 3 ∧ 2 ^ a = 8) ∨ (a = 4 ∧ 2 ^ a = 16) ∨ (a = 5 ∧ 2 ^ a = 32) ∨
    (a = 6 ∧ 2 ^ a = 64) ∨ (a = 7 ∧ 2 ^ a = 128) ∨ (a = 8 ∧ 2 ^ a = 256) ∨
    (1 ≤ a ∧ 2 ^ a % 512 = 0) := by
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | _ | a
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
  · right; right; right; right; right; right; right; right; right
    refine ⟨by omega, ?_⟩
    have hadd : a + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a + 9 := by omega
    rw [hadd, Nat.pow_add]
    omega


/-- Enumeration of all possible residues `2 ^ a % 512` (`0` or `2 ^ j` for `0 ≤ j ≤ 8`). -/
def powTwoMod512Set : List ℕ := [0, 1, 2, 4, 8, 16, 32, 64, 128, 256]

/-- For every exponent `a : ℕ`, `2 ^ a % 512` belongs to `powTwoMod512Set`. -/
theorem pow_two_mod_512_mem (a : ℕ) : (2 ^ a % 512) ∈ powTwoMod512Set := by
  rcases pow_two_mod_512_cases a with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨-, h0⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [h0]; decide


/-- No sum of three elements of `powTwoMod512Set` is congruent to `360 = 8 + 32 + 64 + 256`
modulo `512` (since `360` has binary weight `4` in the low `9` bits). -/
theorem mod_512_three_sum_ne_360 :
    ∀ x ∈ powTwoMod512Set, ∀ y ∈ powTwoMod512Set, ∀ z ∈ powTwoMod512Set,
      (x + y + z) % 512 ≠ 360 := by
  exact Eq.mp (propext ⟨id, id⟩) (by decide)


/-- For all `a, b, c : ℕ`, `(2 + 2 ^ a + 2 ^ b + 2 ^ c) % 512 ≠ 362`. -/
theorem two_add_three_two_pows_mod_512_ne_362 (a b c : ℕ) :
    (2 + 2 ^ a + 2 ^ b + 2 ^ c) % 512 ≠ 362 := by
  intro h
  have hx := pow_two_mod_512_mem a
  have hy := pow_two_mod_512_mem b
  have hz := pow_two_mod_512_mem c
  have hsum : ((2 ^ a % 512) + (2 ^ b % 512) + (2 ^ c % 512)) % 512 = 360 := by omega
  exact mod_512_three_sum_ne_360 (2 ^ a % 512) hx (2 ^ b % 512) hy (2 ^ c % 512) hz hsum


/-- For all `a, b : ℕ`, `(2 + 2 ^ a + 2 ^ b) % 512 ≠ 362`. -/
theorem two_add_two_two_pows_mod_512_ne_362 (a b : ℕ) :
    (2 + 2 ^ a + 2 ^ b) % 512 ≠ 362 := by
  intro h
  have hx := pow_two_mod_512_mem a
  have hy := pow_two_mod_512_mem b
  have hz : 0 ∈ powTwoMod512Set := by decide
  have hsum : ((2 ^ a % 512) + (2 ^ b % 512) + 0) % 512 = 360 := by omega
  exact mod_512_three_sum_ne_360 (2 ^ a % 512) hx (2 ^ b % 512) hy 0 hz hsum


/-- For all `a : ℕ`, `(2 + 2 ^ a) % 512 ≠ 362`. -/
theorem two_add_one_two_pow_mod_512_ne_362 (a : ℕ) :
    (2 + 2 ^ a) % 512 ≠ 362 := by
  intro h
  have hx := pow_two_mod_512_mem a
  have hz : 0 ∈ powTwoMod512Set := by decide
  have hsum : ((2 ^ a % 512) + 0 + 0) % 512 = 360 := by omega
  exact mod_512_three_sum_ne_360 (2 ^ a % 512) hx 0 hz 0 hz hsum


/-- Universal mod-`512` parity-transfer equivalence for `k = 3`: for every `t ≡ 361 (mod 512)`,
`t + 1 ∈ sumPrimeAndTwoPows 3` if and only if `t ∈ sumPrimeAndTwoPows 2` (with no small-value
exceptions, because `(t - 1) % 512 = 360` has binary weight `4`). -/
theorem even_succ_mem_sumPrimeAndTwoPows_three_iff_of_mod_512_eq_361 {t : ℕ}
    (ht512 : t % 512 = 361) :
    t + 1 ∈ sumPrimeAndTwoPows 3 ↔ t ∈ sumPrimeAndTwoPows 2 := by
  constructor
  · intro h
    rw [mem_sumPrimeAndTwoPows_three_iff] at h
    rcases h with h2 | ⟨p, a, b, c, hp, habc⟩
    · rw [mem_sumPrimeAndTwoPows_two_iff] at h2
      rcases h2 with h1 | ⟨p, a, b, hp, hab⟩
      · rw [mem_sumPrimeAndTwoPows_one_iff] at h1
        rcases h1 with hp | ⟨p, a, hp, ha⟩
        · exfalso
          have hp2 : t + 1 = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
          omega
        · by_cases ha0 : a = 0
          · subst ha0
            have htp : t = p := by omega
            rw [htp]
            exact prime_mem_sumPrimeAndTwoPows hp 2
          · exfalso
            have ha2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ a)
            have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
            subst hp2
            exact two_add_one_two_pow_mod_512_ne_362 a (by omega)
      · by_cases ha0 : a = 0
        · subst ha0
          have htb : t = p + 2 ^ b := by omega
          rw [htb]
          exact sumPrimeAndTwoPows_mono (by decide : 1 ≤ 2)
            (prime_add_two_pow_mem_sumPrimeAndTwoPows_one hp b)
        · by_cases hb0 : b = 0
          · subst hb0
            have hta : t = p + 2 ^ a := by omega
            rw [hta]
            exact sumPrimeAndTwoPows_mono (by decide : 1 ≤ 2)
              (prime_add_two_pow_mem_sumPrimeAndTwoPows_one hp a)
          · exfalso
            have ha2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ a)
            have hb2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ b)
            have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
            subst hp2
            exact two_add_two_two_pows_mod_512_ne_362 a b (by omega)
    · by_cases ha0 : a = 0
      · subst ha0
        have hbc : t = p + 2 ^ b + 2 ^ c := by omega
        rw [hbc]
        exact prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two hp b c
      · by_cases hb0 : b = 0
        · subst hb0
          have hac : t = p + 2 ^ a + 2 ^ c := by omega
          rw [hac]
          exact prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two hp a c
        · by_cases hc0 : c = 0
          · subst hc0
            have hab : t = p + 2 ^ a + 2 ^ b := by omega
            rw [hab]
            exact prime_add_two_pow_add_two_pow_mem_sumPrimeAndTwoPows_two hp a b
          · exfalso
            have ha2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ a)
            have hb2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ b)
            have hc2 := pow_two_mod_two_of_one_le (by omega : 1 ≤ c)
            have hp2 : p = 2 := eq_of_prime_of_mod_eq_zero hp (by omega) (by omega)
            subst hp2
            exact two_add_three_two_pows_mod_512_ne_362 a b c (by omega)
  · exact add_one_mem_sumPrimeAndTwoPows_succ


/-- Universal symmetric factor-list certificate bridge for `n ≠ p + 2 ^ a + 2 ^ b`:
if `n < 3 + 2 ^ B` and every ordered pair `b ≤ a < B` with `2 ^ a + 2 ^ b ≤ n` has a
proper divisor `d ∈ factors` of `n - (2 ^ a + 2 ^ b)`, then `n ≠ p + 2 ^ a + 2 ^ b`
for all primes `p` and all `a, b : ℕ`. -/
theorem not_eq_prime_add_two_pow_add_two_pow_of_factor_list {n B : ℕ} (factors : Finset ℕ)
    (hB : n < 3 + 2 ^ B)
    (hcover : ∀ a ∈ Finset.range B, ∀ b ∈ Finset.range (a + 1),
      2 ^ a + 2 ^ b ≤ n →
      ∃ d ∈ factors, 1 < d ∧ d < n - (2 ^ a + 2 ^ b) ∧ (n - (2 ^ a + 2 ^ b)) % d = 0) :
    ∀ p a b : ℕ, p.Prime → n ≠ p + 2 ^ a + 2 ^ b := by
  apply not_eq_prime_add_two_pow_add_two_pow_of_forall_lt hB
  intro a ha b hb
  rintro ⟨hle, hp⟩
  rcases le_total b a with hba | hab
  · rcases hcover a ha b (Finset.mem_range.mpr (by omega)) hle with ⟨d, -, hd1, hd_lt, hd_mod⟩
    exact not_prime_of_mod_eq_zero_of_lt hd1 hd_lt hd_mod hp
  · have hcomm : 2 ^ a + 2 ^ b = 2 ^ b + 2 ^ a := add_comm _ _
    rw [hcomm] at hle hp
    rcases hcover b hb a (Finset.mem_range.mpr (by omega)) hle with ⟨d, -, hd1, hd_lt, hd_mod⟩
    exact not_prime_of_mod_eq_zero_of_lt hd1 hd_lt hd_mod hp


/-- Explicit 38-prime divisor certificate set covering `1117175145 - 2 ^ a` (`0 ≤ a ≤ 30`)
and `1117175145 - (2 ^ a + 2 ^ b)` (`0 ≤ b ≤ a ≤ 30`). -/
def grechukFactors : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 37, 41, 47, 59, 61, 73, 79, 89, 97, 101, 103,
   107, 131, 163, 199, 211, 229, 257, 379, 547, 659, 877, 1381, 1481, 1699, 2099,
   7283, 7703, 19391}

/-- `1117175145` is composite (`5 ∣ 1117175145`). -/
theorem grechuk_odd_not_prime : ¬ Nat.Prime 1117175145 :=
  not_prime_of_mod_eq_zero_of_lt (d := 5) (by decide) (by decide) (by decide)


/-- `1117175145` cannot be written as `p + 2 ^ a` for any prime `p` and any `a : ℕ`. -/
theorem grechuk_odd_not_eq_prime_add_two_pow :
    ∀ p a : ℕ, p.Prime → 1117175145 ≠ p + 2 ^ a :=
  not_eq_prime_add_two_pow_of_factor_list grechukFactors
    (B := 31) (by decide) (by decide)


/-- `1117175145` does not belong to `sumPrimeAndTwoPows 1`. -/
theorem grechuk_odd_not_mem_sumPrimeAndTwoPows_one :
    1117175145 ∉ sumPrimeAndTwoPows 1 := by
  rw [mem_sumPrimeAndTwoPows_one_iff]
  rintro (hp | ⟨p, a, hp, h⟩)
  · exact grechuk_odd_not_prime hp
  · exact grechuk_odd_not_eq_prime_add_two_pow p a hp h


/-- `1117175145` cannot be written as `p + 2 ^ a + 2 ^ b` for any prime `p` and `a, b : ℕ`. -/
theorem grechuk_odd_not_eq_prime_add_two_pow_add_two_pow :
    ∀ p a b : ℕ, p.Prime → 1117175145 ≠ p + 2 ^ a + 2 ^ b :=
  not_eq_prime_add_two_pow_add_two_pow_of_factor_list grechukFactors
    (B := 31) (by decide) (by decide)


/-- `1117175145` is an odd integer outside `sumPrimeAndTwoPows 2` (and in `Erdos9.Erdos9A`). -/
theorem grechuk_odd_not_mem_sumPrimeAndTwoPows_two :
    1117175145 ∉ sumPrimeAndTwoPows 2 := by
  rw [mem_sumPrimeAndTwoPows_two_iff]
  rintro (h1 | ⟨p, a, b, hp, h⟩)
  · exact grechuk_odd_not_mem_sumPrimeAndTwoPows_one h1
  · exact grechuk_odd_not_eq_prime_add_two_pow_add_two_pow p a b hp h


/-- `1117175145` belongs to `Erdos9.Erdos9A`. -/
theorem grechuk_odd_mem_erdos9A : 1117175145 ∈ Erdos9.Erdos9A :=
  (odd_not_mem_sumPrimeAndTwoPows_two_iff_mem_erdos9A
    (by decide) (by decide) grechuk_odd_not_prime).mp
    grechuk_odd_not_mem_sumPrimeAndTwoPows_two


/-- `1117175146` does not belong to `sumPrimeAndTwoPows 3`. -/
theorem grechuk_even_not_mem_sumPrimeAndTwoPows_three :
    1117175146 ∉ sumPrimeAndTwoPows 3 := by
  have hsucc : (1117175146 : ℕ) = 1117175145 + 1 := by decide
  rw [hsucc, even_succ_mem_sumPrimeAndTwoPows_three_iff_of_mod_512_eq_361 (by decide)]
  exact grechuk_odd_not_mem_sumPrimeAndTwoPows_two


/-- Complete unconditional proof of Bogdan Grechuk's example `erdos_10.variants.grechuk_example`
in `FormalConjectures/ErdosProblems/10.lean`: `1117175146 ∉ sumPrimeAndTwoPows 3`. -/
theorem grechuk_example :
    1117175146 ∉ sumPrimeAndTwoPows 3 :=
  grechuk_even_not_mem_sumPrimeAndTwoPows_three

end Erdos10
