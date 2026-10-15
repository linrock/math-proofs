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


@[expose] public section DensityHelper
open Filter
open scoped Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

theorem partialDensity_le_one {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : S.partialDensity A b ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ inter_subset_right

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

/-- In a non-trivial partial order with a least element, `Set.Iio n` has eventually non-zero
cardinality. This is the density helper used by `HasDensity.univ`; it is reproduced here so
that the proof module depends only on Mathlib. -/
theorem Iio_eventually_ncard_ne_zero {β : Type*} [PartialOrder β] [LocallyFiniteOrder β]
    [OrderBot β] [Nontrivial β] : ∃ (b : β), ∀ n ≥ b, (Set.Iio n).ncard ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_ne (⊥ : β)
  refine ⟨b, fun n hn => ?_⟩
  have hmem : (⊥ : β) ∈ Set.Iio n :=
    lt_of_lt_of_le (lt_of_le_of_ne bot_le (Ne.symm hb)) hn
  exact Set.ncard_ne_zero_of_mem hmem

namespace HasDensity

@[simp]
theorem univ {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
    (@Set.univ β).HasDensity 1 := by
  by_cases h : atTop (α := β) = ⊥
  · simp [h, HasDensity]
  · simp [HasDensity, partialDensity]
    let ⟨b, hb⟩ := Iio_eventually_ncard_ne_zero (β := β)
    refine tendsto_const_nhds.congr' ?_
    exact (eventually_ge_atTop b).mono fun n hn ↦ (div_self <| mod_cast hb n hn).symm

theorem univ_nat_hasDensity_one : (@Set.univ ℕ).HasDensity 1 := univ

@[simp]
theorem empty {β : Type*} [Preorder β] [LocallyFiniteOrderBot β] (A : Set β := Set.univ) :
    Set.HasDensity (∅ : Set β) 0 A := by
  simpa [HasDensity, partialDensity] using tendsto_const_nhds

end HasDensity
end Set
end DensityHelper


@[expose] public noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000


--
-- /--
-- The set of odd numbers that cannot be expressed as a prime plus two powers of 2.
-- -/
-- def Erdos9A : Set ℕ := { n | Odd n ∧ ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l }
--
--
-- @[category test, AMS 5 11]
-- theorem erdos9A_contains_one : 1 ∈ Erdos9A := by
--   constructor
--   · decide
--   · push Not
--     intro p k l hp
--     linarith [Nat.Prime.two_le hp, @Nat.one_le_two_pow k, @Nat.one_le_two_pow l]
--
-- @[category test, AMS 5 11]
-- theorem erdos9A_contains_three : 3 ∈ Erdos9A := by
--   constructor
--   · decide
--   · push Not
--     intro p k l hp
--     linarith [Nat.Prime.two_le hp, @Nat.one_le_two_pow k, @Nat.one_le_two_pow l]
--
-- @[category test, AMS 5 11]
-- theorem erdos9A_not_contains_five : 5 ∉ Erdos9A := by
--   unfold Erdos9A
--   simp only [exists_and_left, not_exists, not_and, Set.mem_ofPred_eq, not_forall, Decidable.not_not]
--   intro
--   use 3, Nat.prime_three, 0, 0
--   simp only [pow_zero, Nat.reduceAdd]
--
--
-- /--
-- The set is known to be infinite. In [Er77c] Erdős credits Schinzel with proving that there are
-- infinitely many odd integers not of this form, but gives no reference.
--
-- [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._.
-- -/
-- end Erdos9

namespace Erdos9

/-- `IsPrimePlusTwoPowers n` holds when `n = p + 2 ^ k + 2 ^ l` for some prime `p`
and natural exponents `k, l : ℕ`. -/
def IsPrimePlusTwoPowers (n : ℕ) : Prop :=
  ∃ p k l : ℕ, Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l

/-- The set of odd numbers that cannot be expressed as a prime plus two powers of `2`.
The body is the upstream definition from `FormalConjectures/ErdosProblems/9.lean` verbatim so
that it is syntactically identical to the `Challenge`/`Statement` definition. -/
def Erdos9A : Set ℕ :=
  { n | Odd n ∧ ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l }

/-- Membership in `Erdos9A` in terms of the named predicate `IsPrimePlusTwoPowers`, which is
definitionally equal to the existential in the body of `Erdos9A`. -/
theorem mem_erdos9A_iff (n : ℕ) :
    n ∈ Erdos9A ↔ Odd n ∧ ¬ IsPrimePlusTwoPowers n :=
  Iff.rfl

/-- `Erdos9A` matches the upstream set definition in `FormalConjectures/ErdosProblems/9.lean`. -/
theorem erdos9A_eq_setOf :
    Erdos9A = { n | Odd n ∧ ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l } :=
  rfl

#print axioms Erdos9.erdos9A_eq_setOf

/-- Every integer expressible as `p + 2 ^ k + 2 ^ l` with `p` prime is at least `4`. -/
theorem four_le_of_isPrimePlusTwoPowers {n : ℕ} (h : IsPrimePlusTwoPowers n) :
    4 ≤ n := by
  rcases h with ⟨p, k, l, hp, rfl⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hl1 : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  omega

#print axioms Erdos9.four_le_of_isPrimePlusTwoPowers

/-- No natural number strictly less than `4` belongs to `IsPrimePlusTwoPowers`. -/
theorem not_isPrimePlusTwoPowers_of_lt_four {n : ℕ} (hn : n < 4) :
    ¬ IsPrimePlusTwoPowers n := by
  intro h
  have h4 := four_le_of_isPrimePlusTwoPowers h
  omega

#print axioms Erdos9.not_isPrimePlusTwoPowers_of_lt_four

/-- `1` belongs to `Erdos9A`. -/
theorem erdos9A_contains_one : 1 ∈ Erdos9A :=
  ⟨by decide, not_isPrimePlusTwoPowers_of_lt_four (by decide)⟩

#print axioms Erdos9.erdos9A_contains_one

/-- `3` belongs to `Erdos9A`. -/
theorem erdos9A_contains_three : 3 ∈ Erdos9A :=
  ⟨by decide, not_isPrimePlusTwoPowers_of_lt_four (by decide)⟩

#print axioms Erdos9.erdos9A_contains_three

/-- `5 = 3 + 2 ^ 0 + 2 ^ 0` does not belong to `Erdos9A`. -/
theorem erdos9A_not_contains_five : 5 ∉ Erdos9A := by
  rintro ⟨-, hnot⟩
  exact hnot ⟨3, 0, 0, Nat.prime_three, by decide⟩

#print axioms Erdos9.erdos9A_not_contains_five

/-- Parity dichotomy for `2 ^ k`: either `k = 0` and `2 ^ k = 1`, or `1 ≤ k` and `2 ^ k % 2 = 0`. -/
theorem two_pow_eq_one_or_mod_two_eq_zero (k : ℕ) :
    (k = 0 ∧ 2 ^ k = 1) ∨ (1 ≤ k ∧ 2 ^ k % 2 = 0) := by
  rcases k with _ | k
  · exact Or.inl ⟨rfl, rfl⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.pow_succ]
    omega

#print axioms Erdos9.two_pow_eq_one_or_mod_two_eq_zero

/-- Parity dichotomy for primes: either `p = 2`, or `3 ≤ p` and `p` is odd. -/
theorem prime_eq_two_or_three_le_and_odd {p : ℕ} (hp : p.Prime) :
    p = 2 ∨ (3 ≤ p ∧ p % 2 = 1) := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · exact Or.inl rfl
  · have hp2 : 2 ≤ p := hp.two_le
    exact Or.inr ⟨by omega, hodd⟩

#print axioms Erdos9.prime_eq_two_or_three_le_and_odd

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

#print axioms Erdos9.odd_eq_two_add_two_pows_iff

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

#print axioms Erdos9.odd_eq_odd_prime_add_two_pows_cases

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

#print axioms Erdos9.odd_eq_prime_add_two_pows_trichotomy

/-- Any integer of the form `n = 2 ^ m + 3` lies in `IsPrimePlusTwoPowers` (`2 + 2 ^ 0 + 2 ^ m`). -/
theorem isPrimePlusTwoPowers_of_eq_two_pow_add_three {n m : ℕ} (h : n = 2 ^ m + 3) :
    IsPrimePlusTwoPowers n :=
  ⟨2, 0, m, Nat.prime_two, by omega⟩

#print axioms Erdos9.isPrimePlusTwoPowers_of_eq_two_pow_add_three

/-- Any integer `n` with `(n - 2).Prime` lies in `IsPrimePlusTwoPowers` (`(n - 2) + 2 ^ 0 + 2 ^ 0`). -/
theorem isPrimePlusTwoPowers_of_sub_two_prime {n : ℕ} (hp : (n - 2).Prime) :
    IsPrimePlusTwoPowers n := by
  have hp2 : 2 ≤ n - 2 := hp.two_le
  exact ⟨n - 2, 0, 0, hp, by omega⟩

#print axioms Erdos9.isPrimePlusTwoPowers_of_sub_two_prime

/-- Any integer `n` with `2 ^ k + 2 ^ l ≤ n` and `(n - 2 ^ k - 2 ^ l).Prime` lies in `IsPrimePlusTwoPowers`. -/
theorem isPrimePlusTwoPowers_of_sub_two_pows_prime {n k l : ℕ}
    (hle : 2 ^ k + 2 ^ l ≤ n) (hp : (n - 2 ^ k - 2 ^ l).Prime) :
    IsPrimePlusTwoPowers n :=
  ⟨n - 2 ^ k - 2 ^ l, k, l, hp, by omega⟩

#print axioms Erdos9.isPrimePlusTwoPowers_of_sub_two_pows_prime

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

#print axioms Erdos9.isPrimePlusTwoPowers_odd_iff_three_cases

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
  rw [mem_erdos9A_iff]
  simp only [isPrimePlusTwoPowers_odd_iff_three_cases hn]
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

#print axioms Erdos9.mem_erdos9A_iff_three_obstructions

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

#print axioms Erdos9.checkIsPrimePlusTwoPowers_eq_true_iff

/-- Soundness and completeness of `checkErdos9A`. -/
theorem checkErdos9A_eq_true_iff (n : ℕ) :
    checkErdos9A n = true ↔ n ∈ Erdos9A := by
  unfold checkErdos9A
  rw [mem_erdos9A_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    ← Bool.not_eq_true, checkIsPrimePlusTwoPowers_eq_true_iff, Nat.odd_iff]

#print axioms Erdos9.checkErdos9A_eq_true_iff

set_option maxRecDepth 200000 in
/-- Kernel-checked boolean verification that `1` and `3` are the only `n ≤ 200`
with `checkErdos9A n = true`. -/
theorem checkErdos9A_le_200_iff :
    ∀ n ≤ 200, (checkErdos9A n = true ↔ (n = 1 ∨ n = 3)) := by
  decide

#print axioms Erdos9.checkErdos9A_le_200_iff

/-- For every `n ≤ 200`, `n ∈ Erdos9A` if and only if `n = 1` or `n = 3`. -/
theorem mem_erdos9A_iff_of_le_200 {n : ℕ} (hn : n ≤ 200) :
    n ∈ Erdos9A ↔ n = 1 ∨ n = 3 := by
  rw [← checkErdos9A_eq_true_iff]
  exact checkErdos9A_le_200_iff n hn

#print axioms Erdos9.mem_erdos9A_iff_of_le_200

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

#print axioms Erdos9.erdos9A_filter_range_201

/-- Exact set classification `{n ≤ 200 | n ∈ Erdos9A} = {1, 3}`. -/
theorem erdos9A_le_200_eq_pair :
    {n : ℕ | n ≤ 200 ∧ n ∈ Erdos9A} = ({1, 3} : Set ℕ) := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, hmem⟩
    exact (mem_erdos9A_iff_of_le_200 hn).mp hmem
  · rintro (rfl | rfl)
    · exact ⟨by omega, (mem_erdos9A_iff_of_le_200 (by omega)).mpr (Or.inl rfl)⟩
    · exact ⟨by omega, (mem_erdos9A_iff_of_le_200 (by omega)).mpr (Or.inr rfl)⟩

#print axioms Erdos9.erdos9A_le_200_eq_pair

end Erdos9


@[expose] public noncomputable section
open scoped BigOperators

/-! ## Crocker Fermat-factor reductions

# Crocker's (1971) Fermat-Number Divisibility and Covering Reductions

Develops the Crocker covering and Fermat-factor machinery:
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

#print axioms Erdos9.erdos9APos_eq_setOf

/-- Every positive-exponent representation `n = p + 2 ^ k + 2 ^ l` (`k, l ≥ 1`) is in particular
a representation with `k, l ≥ 0`. -/
theorem isPrimePlusTwoPosPowers_imp_isPrimePlusTwoPowers {n : ℕ}
    (h : IsPrimePlusTwoPosPowers n) : IsPrimePlusTwoPowers n := by
  rcases h with ⟨p, k, l, hp, -, -, hn⟩
  exact ⟨p, k, l, hp, hn⟩

#print axioms Erdos9.isPrimePlusTwoPosPowers_imp_isPrimePlusTwoPowers

/-- Inclusion of the unrestricted exceptional set into the positive-exponent exceptional set:
`Erdos9A ⊆ Erdos9APos`. -/
theorem erdos9A_subset_erdos9APos : Erdos9A ⊆ Erdos9APos := by
  rintro n ⟨hn_odd, hnot⟩
  exact ⟨hn_odd, fun hpos => hnot (isPrimePlusTwoPosPowers_imp_isPrimePlusTwoPowers hpos)⟩

#print axioms Erdos9.erdos9A_subset_erdos9APos

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

#print axioms Erdos9.seven_le_of_odd_isPrimePlusTwoPosPowers

/-- No odd integer strictly less than `7` satisfies `IsPrimePlusTwoPosPowers`. -/
theorem not_isPrimePlusTwoPosPowers_of_odd_lt_seven {n : ℕ}
    (hn : Odd n) (hlt : n < 7) : ¬ IsPrimePlusTwoPosPowers n := by
  intro h
  have h7 := seven_le_of_odd_isPrimePlusTwoPosPowers hn h
  omega

#print axioms Erdos9.not_isPrimePlusTwoPosPowers_of_odd_lt_seven

/-- `1` belongs to `Erdos9APos`. -/
theorem erdos9APos_contains_one : 1 ∈ Erdos9APos :=
  erdos9A_subset_erdos9APos erdos9A_contains_one

#print axioms Erdos9.erdos9APos_contains_one

/-- `3` belongs to `Erdos9APos`. -/
theorem erdos9APos_contains_three : 3 ∈ Erdos9APos :=
  erdos9A_subset_erdos9APos erdos9A_contains_three

#print axioms Erdos9.erdos9APos_contains_three

/-- `5` belongs to `Erdos9APos` because `p + 2 ^ k + 2 ^ l ≥ 7` for odd `p + 2 ^ k + 2 ^ l`
with `k, l ≥ 1`. -/
theorem erdos9APos_contains_five : 5 ∈ Erdos9APos :=
  ⟨by decide, not_isPrimePlusTwoPosPowers_of_odd_lt_seven (by decide) (by decide)⟩

#print axioms Erdos9.erdos9APos_contains_five

/-- `5` separates `Erdos9APos` from `Erdos9A` (`5 ∈ Erdos9APos \ Erdos9A`), since
`5 = 3 + 2 ^ 0 + 2 ^ 0` requires the zero-exponent boundary case. -/
theorem five_mem_erdos9APos_diff_erdos9A : 5 ∈ Erdos9APos \ Erdos9A :=
  ⟨erdos9APos_contains_five, erdos9A_not_contains_five⟩

#print axioms Erdos9.five_mem_erdos9APos_diff_erdos9A

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

#print axioms Erdos9.isPrimePlusTwoPosPowers_iff

/-- For an odd integer `n`, `n ∈ Erdos9APos` if and only if `n - 2 ^ k - 2 ^ l` is never prime
for positive exponents `k, l ≥ 1` with `2 ^ k + 2 ^ l < n`. -/
theorem mem_erdos9APos_iff {n : ℕ} (hn : Odd n) :
    n ∈ Erdos9APos ↔
      ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → 2 ^ k + 2 ^ l < n → ¬ (n - 2 ^ k - 2 ^ l).Prime := by
  rw [erdos9APos_eq_setOf, Set.mem_ofPred_eq, isPrimePlusTwoPosPowers_iff]
  constructor
  · rintro ⟨-, hnot⟩ k l hk hl hlt hp
    exact hnot ⟨k, l, hk, hl, hlt, hp⟩
  · intro hall
    refine ⟨hn, ?_⟩
    rintro ⟨k, l, hk, hl, hlt, hp⟩
    exact hall k l hk hl hlt hp

#print axioms Erdos9.mem_erdos9APos_iff

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

#print axioms Erdos9.mem_erdos9A_iff_mem_erdos9APos_and_boundary_obstructions

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

#print axioms Erdos9.checkIsPrimePlusTwoPosPowers_eq_true_iff

/-- Soundness and completeness of `checkErdos9APos`. -/
theorem checkErdos9APos_eq_true_iff (n : ℕ) :
    checkErdos9APos n = true ↔ n ∈ Erdos9APos := by
  rw [erdos9APos_eq_setOf]
  unfold checkErdos9APos
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Set.mem_ofPred_eq,
    ← Bool.not_eq_true, checkIsPrimePlusTwoPosPowers_eq_true_iff, Nat.odd_iff]

#print axioms Erdos9.checkErdos9APos_eq_true_iff

set_option maxRecDepth 200000 in
/-- Kernel-checked boolean verification that `1`, `3`, and `5` are the only `n ≤ 200`
with `checkErdos9APos n = true`. -/
theorem checkErdos9APos_le_200_iff :
    ∀ n ≤ 200, (checkErdos9APos n = true ↔ (n = 1 ∨ n = 3 ∨ n = 5)) := by
  decide

#print axioms Erdos9.checkErdos9APos_le_200_iff

/-- For every `n ≤ 200`, `n ∈ Erdos9APos` if and only if `n = 1`, `n = 3`, or `n = 5`. -/
theorem mem_erdos9APos_iff_of_le_200 {n : ℕ} (hn : n ≤ 200) :
    n ∈ Erdos9APos ↔ n = 1 ∨ n = 3 ∨ n = 5 := by
  rw [← checkErdos9APos_eq_true_iff]
  exact checkErdos9APos_le_200_iff n hn

#print axioms Erdos9.mem_erdos9APos_iff_of_le_200

/-- Exact set classification `{n ≤ 200 | n ∈ Erdos9APos} = {1, 3, 5}`. -/
theorem erdos9APos_le_200_eq_triple :
    {n : ℕ | n ≤ 200 ∧ n ∈ Erdos9APos} = ({1, 3, 5} : Set ℕ) := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, hmem⟩
    exact (mem_erdos9APos_iff_of_le_200 hn).mp hmem
  · rintro (rfl | rfl | rfl)
    · exact ⟨by omega, (mem_erdos9APos_iff_of_le_200 (by omega)).mpr (Or.inl rfl)⟩
    · exact ⟨by omega, (mem_erdos9APos_iff_of_le_200 (by omega)).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨by omega, (mem_erdos9APos_iff_of_le_200 (by omega)).mpr (Or.inr (Or.inr rfl))⟩

#print axioms Erdos9.erdos9APos_le_200_eq_triple

/-! ## Section 2: Diagonal (`k = l`) Reduction and Covering-System Exclusions -/

/-- Equal powers of `2` combine into the next power of `2`: `2 ^ k + 2 ^ k = 2 ^ (k + 1)`. -/
theorem two_pow_add_self (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [Nat.pow_succ]
  omega

#print axioms Erdos9.two_pow_add_self

/-- Along the diagonal `k = l`, `n - 2 ^ k - 2 ^ k` reduces to `n - 2 ^ (k + 1)`. -/
theorem sub_two_pow_sub_self (n k : ℕ) : n - 2 ^ k - 2 ^ k = n - 2 ^ (k + 1) := by
  rw [Nat.sub_sub, two_pow_add_self]

#print axioms Erdos9.sub_two_pow_sub_self

/-- Composite certificate from a proper divisor `1 < q < m` with `q ∣ m`. -/
theorem not_prime_of_dvd_of_lt {m q : ℕ} (hq1 : 1 < q) (hqm : q < m) (hdvd : q ∣ m) :
    ¬ m.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd q hdvd with rfl | rfl <;> omega

#print axioms Erdos9.not_prime_of_dvd_of_lt

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

#print axioms Erdos9.diagonal_composite_of_covering_set

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

#print axioms Erdos9.not_eq_prime_add_two_pow_diag_of_covering_set

/-! ## Section 3: Crocker's (1971) Fermat-Number Divisibility & Off-Diagonal Reductions -/

/-- The `r`-th Fermat number `F_r = 2 ^ (2 ^ r) + 1`. -/
def fermatNumber (r : ℕ) : ℕ := 2 ^ (2 ^ r) + 1

/-- Every Fermat number is at least `3`. -/
theorem three_le_fermatNumber (r : ℕ) : 3 ≤ fermatNumber r := by
  unfold fermatNumber
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have h2 : 2 ^ 1 ≤ 2 ^ (2 ^ r) := Nat.pow_le_pow_right (by decide) h1
  omega

#print axioms Erdos9.three_le_fermatNumber

/-- Every Fermat number is strictly greater than `1`. -/
theorem one_lt_fermatNumber (r : ℕ) : 1 < fermatNumber r := by
  have h3 := three_le_fermatNumber r
  omega

#print axioms Erdos9.one_lt_fermatNumber

/-- Every Fermat number is odd. -/
theorem odd_fermatNumber (r : ℕ) : Odd (fermatNumber r) := by
  unfold fermatNumber
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rcases two_pow_eq_one_or_mod_two_eq_zero (2 ^ r) with ⟨h0, -⟩ | ⟨-, hmod⟩
  · omega
  · rw [Nat.odd_iff]
    omega

#print axioms Erdos9.odd_fermatNumber

/-- Universal odd-power sum divisibility: for all `a, m : ℕ`, `(a + 1) ∣ (a ^ (2 * m + 1) + 1)`. -/
theorem add_one_dvd_pow_two_mul_add_one_add_one (a m : ℕ) :
    a + 1 ∣ a ^ (2 * m + 1) + 1 := by
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  simpa using Odd.nat_add_dvd_pow_add_pow a 1 hodd

#print axioms Erdos9.add_one_dvd_pow_two_mul_add_one_add_one

/-- Crocker's Fermat divisibility lemma: for all `r, m : ℕ`,
`(2 ^ (2 ^ r) + 1) ∣ (2 ^ (2 ^ r * (2 * m + 1)) + 1)`. -/
theorem fermatNumber_dvd_two_pow_two_pow_mul_two_mul_add_one_add_one (r m : ℕ) :
    (2 ^ (2 ^ r) + 1) ∣ (2 ^ (2 ^ r * (2 * m + 1)) + 1) := by
  rw [Nat.pow_mul]
  exact add_one_dvd_pow_two_mul_add_one_add_one (2 ^ (2 ^ r)) m

#print axioms Erdos9.fermatNumber_dvd_two_pow_two_pow_mul_two_mul_add_one_add_one

/-- Odd-multiplier formulation of Crocker's Fermat divisibility: for every `r : ℕ`
and every odd `u : ℕ`, `fermatNumber r ∣ (2 ^ (2 ^ r * u) + 1)`. -/
theorem fermatNumber_dvd_two_pow_two_pow_mul_odd_add_one (r : ℕ) {u : ℕ} (hu : Odd u) :
    fermatNumber r ∣ 2 ^ (2 ^ r * u) + 1 := by
  rcases hu with ⟨m, rfl⟩
  exact fermatNumber_dvd_two_pow_two_pow_mul_two_mul_add_one_add_one r m

#print axioms Erdos9.fermatNumber_dvd_two_pow_two_pow_mul_odd_add_one

/-- Factoring `2 ^ k + 2 ^ l` for `k ≤ l`: `2 ^ k + 2 ^ l = 2 ^ k * (2 ^ (l - k) + 1)`. -/
theorem two_pow_add_two_pow_eq_mul_sub {k l : ℕ} (hkl : k ≤ l) :
    2 ^ k + 2 ^ l = 2 ^ k * (2 ^ (l - k) + 1) := by
  have hl : l = k + (l - k) := by omega
  conv_lhs => rw [hl, Nat.pow_add]
  ring

#print axioms Erdos9.two_pow_add_two_pow_eq_mul_sub

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

#print axioms Erdos9.fermatNumber_dvd_two_pow_add_two_pow_of_eq

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

#print axioms Erdos9.padicValNat_two_mul_odd

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

#print axioms Erdos9.padicValNat_two_sub_eq_iff

/-- For every `k < l` with `padicValNat 2 (l - k) = r`, the Fermat number `2 ^ (2 ^ r) + 1`
divides `2 ^ k + 2 ^ l`. -/
theorem fermatNumber_dvd_two_pow_add_two_pow_of_padicValNat_sub {k l r : ℕ}
    (hkl : k < l) (hr : padicValNat 2 (l - k) = r) :
    (2 ^ (2 ^ r) + 1) ∣ (2 ^ k + 2 ^ l) := by
  rcases (padicValNat_two_sub_eq_iff hkl).mp hr with ⟨m, hl⟩
  exact fermatNumber_dvd_two_pow_add_two_pow_of_eq k r m hl

#print axioms Erdos9.fermatNumber_dvd_two_pow_add_two_pow_of_padicValNat_sub

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

#print axioms Erdos9.fermatNumber_dvd_two_pow_add_two_pow_of_padicValNat_dist

/-- Consequently, if `q ∣ (2 ^ (2 ^ r) + 1)` and `q ∣ n`, then `q ∣ (n - 2 ^ k - 2 ^ l)`
for all `k, r, m : ℕ` and `l = k + 2 ^ r * (2 * m + 1)`. -/
theorem dvd_sub_two_pows_of_dvd_fermatNumber {n q k r m l : ℕ}
    (hqF : q ∣ 2 ^ (2 ^ r) + 1) (hqn : q ∣ n) (hl : l = k + 2 ^ r * (2 * m + 1)) :
    q ∣ (n - 2 ^ k - 2 ^ l) := by
  rw [Nat.sub_sub]
  exact Nat.dvd_sub hqn (dvd_trans hqF (fermatNumber_dvd_two_pow_add_two_pow_of_eq k r m hl))

#print axioms Erdos9.dvd_sub_two_pows_of_dvd_fermatNumber

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

#print axioms Erdos9.dvd_sub_two_pows_of_dvd_fermatNumber_of_padicValNat_dist

/-- Composite certificate for off-diagonal differences `n - 2 ^ k - 2 ^ l` via a Fermat divisor `q ∣ F_r`
also dividing `n`. -/
theorem not_prime_sub_two_pows_of_dvd_fermatNumber {n q k l r : ℕ}
    (hq1 : 1 < q) (hkl : k ≠ l) (hr : padicValNat 2 (Nat.dist k l) = r)
    (hqF : q ∣ 2 ^ (2 ^ r) + 1) (hqn : q ∣ n) (hlt : q < n - 2 ^ k - 2 ^ l) :
    ¬ (n - 2 ^ k - 2 ^ l).Prime :=
  not_prime_of_dvd_of_lt hq1 hlt
    (dvd_sub_two_pows_of_dvd_fermatNumber_of_padicValNat_dist hkl hr hqF hqn)

#print axioms Erdos9.not_prime_sub_two_pows_of_dvd_fermatNumber

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

#print axioms Erdos9.fermatNumber_dvd_two_pow_two_pow_mul_sub_one

/-- Algebraic identity relating off-diagonal `2 ^ k + 2 ^ l` (`k ≤ l`) to the diagonal `2 ^ (k + 1)`:
`2 ^ k + 2 ^ l - 2 ^ (k + 1) = 2 ^ k * (2 ^ (l - k) - 1)`. -/
theorem two_pow_add_two_pow_sub_diag {k l : ℕ} (hkl : k ≤ l) :
    2 ^ k + 2 ^ l - 2 ^ (k + 1) = 2 ^ k * (2 ^ (l - k) - 1) := by
  have hl : l = k + (l - k) := by omega
  have h1 : 1 ≤ 2 ^ (l - k) := Nat.one_le_two_pow
  conv_lhs => rw [hl, Nat.pow_add, Nat.pow_succ]
  rw [Nat.mul_sub_left_distrib, mul_one]
  omega

#print axioms Erdos9.two_pow_add_two_pow_sub_diag

/-- Crocker's diagonal collapse modulo `F_s` for `s < r`: when `l = k + 2 ^ r * u`,
`(2 ^ (2 ^ s) + 1) ∣ (2 ^ k + 2 ^ l - 2 ^ (k + 1))`. -/
theorem fermatNumber_dvd_off_diag_sub_diag {s r k u l : ℕ}
    (hsr : s < r) (hl : l = k + 2 ^ r * u) :
    (2 ^ (2 ^ s) + 1) ∣ (2 ^ k + 2 ^ l - 2 ^ (k + 1)) := by
  have hkl : k ≤ l := by omega
  have hsub : l - k = 2 ^ r * u := by omega
  rw [two_pow_add_two_pow_sub_diag hkl, hsub]
  exact dvd_mul_of_dvd_right (fermatNumber_dvd_two_pow_two_pow_mul_sub_one hsr u) (2 ^ k)

#print axioms Erdos9.fermatNumber_dvd_off_diag_sub_diag

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

#print axioms Erdos9.dvd_sub_two_pows_of_dvd_fermatNumber_lt_of_dvd_diag

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

#print axioms Erdos9.mem_erdos9APos_of_diagonal_and_fermat_cover

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

#print axioms Erdos9.mem_erdos9A_of_diagonal_fermat_and_boundary_cover

end Erdos9


@[expose] public noncomputable section
open scoped BigOperators

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

#print axioms Erdos9.two_pow_add_three_mod_sixteen_ne_fifteen

/-- Any integer `n ≡ 15 (mod 16)` avoids the zero-exponent boundary family `2 ^ m + 3` for all `m : ℕ`. -/
theorem ne_two_pow_add_three_of_mod_sixteen_eq_fifteen {n : ℕ} (hn16 : n % 16 = 15) (m : ℕ) :
    n ≠ 2 ^ m + 3 := by
  intro h
  have hmod := two_pow_add_three_mod_sixteen_ne_fifteen m
  omega

#print axioms Erdos9.ne_two_pow_add_three_of_mod_sixteen_eq_fifteen

/-- Every integer `n ≡ 15 (mod 16)` is odd. -/
theorem odd_of_mod_sixteen_eq_fifteen {n : ℕ} (hn16 : n % 16 = 15) :
    Odd n := by
  rw [Nat.odd_iff]
  omega

#print axioms Erdos9.odd_of_mod_sixteen_eq_fifteen

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

#print axioms Erdos9.fermatNumber_mod_sixteen_cases

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

#print axioms Erdos9.two_pow_add_two_pow_add_mod_sixteen_ne_fifteen

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

#print axioms Erdos9.five_le_of_forty_two_le_two_pow_add_two_pow

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

#print axioms Erdos9.crocker_off_diagonal_ne_fermat_factor

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

#print axioms Erdos9.crocker_off_diagonal_composite_of_fermat_factor

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

#print axioms Erdos9.padicValNat_two_sub_lt_of_two_pow_add_lt

/-! ## Section 2: Universal Periodic Exponential Divisibility & 24-Modulus Covering System -/

/-- Universal divisibility `(a ^ d - 1) ∣ (a ^ (d * k) - 1)`. -/
theorem pow_sub_one_dvd_pow_mul_sub_one (a d k : ℕ) :
    (a ^ d - 1) ∣ (a ^ (d * k) - 1) := by
  rw [Nat.pow_mul]
  exact Nat.sub_one_dvd_pow_sub_one (a ^ d) k

#print axioms Erdos9.pow_sub_one_dvd_pow_mul_sub_one

/-- Universal divisibility `(a ^ d - 1) ∣ (a ^ m - 1)` whenever `d ∣ m`. -/
theorem pow_sub_one_dvd_of_dvd {a d m : ℕ} (h : d ∣ m) :
    (a ^ d - 1) ∣ (a ^ m - 1) := by
  rcases h with ⟨k, rfl⟩
  exact pow_sub_one_dvd_pow_mul_sub_one a d k

#print axioms Erdos9.pow_sub_one_dvd_of_dvd

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

#print axioms Erdos9.two_pow_mod_eq_of_dvd_pow_sub_one

/-- If `n % q = 2 ^ a % q` and `2 ^ a ≤ n`, then `q ∣ (n - 2 ^ a)`. -/
theorem dvd_sub_two_pow_of_mod_eq {n q a : ℕ}
    (hmod : n % q = 2 ^ a % q) (hle : 2 ^ a ≤ n) :
    q ∣ (n - 2 ^ a) := by
  rw [← Nat.modEq_iff_dvd' hle]
  exact hmod.symm

#print axioms Erdos9.dvd_sub_two_pow_of_mod_eq

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

#print axioms Erdos9.crockerCoverTable_covers_lt_720

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

#print axioms Erdos9.crockerCoverTable_spec

/-- Universal covering property of `crockerCoverTable`: every natural number `a : ℕ`
satisfies `a % d = r` for some `(d, q, r) ∈ crockerCoverTable`. -/
theorem crockerCoverTable_covers_all (a : ℕ) :
    ∃ e ∈ crockerCoverTable, a % e.1 = e.2.2 := by
  have hlt : a % 720 < 720 := Nat.mod_lt a (by decide)
  rcases crockerCoverTable_covers_lt_720 (a % 720) hlt with ⟨e, he, hmod⟩
  have hd720 : e.1 ∣ 720 := (crockerCoverTable_spec e he).2.2.1
  rw [Nat.mod_mod_of_dvd a hd720] at hmod
  exact ⟨e, he, hmod⟩

#print axioms Erdos9.crockerCoverTable_covers_all

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

#print axioms Erdos9.crockerN0_base_props

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

#print axioms Erdos9.two_pow_ten_dvd_two_pow_crockerExp

/-- `2 ^ 1024 - 1` divides `2 ^ (2 ^ crockerExp t) - 1` for all `t : ℕ`. -/
theorem two_pow_1024_sub_one_dvd (t : ℕ) :
    (2 ^ 1024 - 1) ∣ (2 ^ (2 ^ crockerExp t) - 1) :=
  pow_sub_one_dvd_of_dvd (two_pow_ten_dvd_two_pow_crockerExp t)

#print axioms Erdos9.two_pow_1024_sub_one_dvd

/-- Exact multiplication identity `(2 ^ 1024 - 1) * crockerU t = 2 ^ (2 ^ crockerExp t) - 1`. -/
theorem mul_crockerU_eq (t : ℕ) :
    (2 ^ 1024 - 1) * crockerU t = 2 ^ (2 ^ crockerExp t) - 1 :=
  Nat.mul_div_cancel' (two_pow_1024_sub_one_dvd t)

#print axioms Erdos9.mul_crockerU_eq

set_option exponentiation.threshold 2048 in
/-- Positive lower bound `0 < 2 ^ 1024 - 1`. -/
theorem two_pow_1024_sub_one_pos : 0 < 2 ^ 1024 - 1 := by
  have h1 : (1 : ℕ) ≤ 1024 := by decide
  have h2 : 2 ^ 1 ≤ 2 ^ 1024 := Nat.pow_le_pow_right (by decide) h1
  omega

#print axioms Erdos9.two_pow_1024_sub_one_pos

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

#print axioms Erdos9.one_le_crockerU

/-- `crockerN t` is strictly bounded above by `2 ^ (2 ^ crockerExp t) - 1`. -/
theorem crockerN_lt_two_pow (t : ℕ) :
    crockerN t < 2 ^ (2 ^ crockerExp t) - 1 := by
  unfold crockerN
  rw [← mul_crockerU_eq]
  have hlt : crockerN0 < 2 ^ 1024 - 1 := crockerN0_base_props.2.2.1
  have hu : 0 < crockerU t := one_le_crockerU t
  exact (Nat.mul_lt_mul_right hu).mpr hlt

#print axioms Erdos9.crockerN_lt_two_pow

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

#print axioms Erdos9.crockerN_strictMono

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

#print axioms Erdos9.five_thousand_forty_dvd_sub

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

#print axioms Erdos9.mul_crockerU_sub_one_eq

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

#print axioms Erdos9.dvd_crockerU_sub_one_of_dvd_5040

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

#print axioms Erdos9.crockerN_mod_eq_of_dvd_crockerU_sub_one

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

#print axioms Erdos9.crockerN_mod_sixteen

/-- For every `t : ℕ`, `crockerN t % 127 = 1`. -/
theorem crockerN_mod_127 (t : ℕ) : crockerN t % 127 = 1 := by
  have hdvd : 127 ∣ (crockerU t - 1) :=
    dvd_crockerU_sub_one_of_dvd_5040 (d := 7) (by decide) (by decide)
      crockerN0_base_props.2.2.2.2.2.2.2.1 t
  rw [crockerN_mod_eq_of_dvd_crockerU_sub_one hdvd]
  exact crockerN0_base_props.2.2.2.2.1

#print axioms Erdos9.crockerN_mod_127

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

#print axioms Erdos9.not_prime_crockerN_sub_two_pow

/-- Every `crockerB r` is at least `3`. -/
theorem three_le_crockerB (r : ℕ) : 3 ≤ crockerB r := by
  unfold crockerB
  split_ifs with hr
  · decide
  · exact three_le_fermatNumber r

#print axioms Erdos9.three_le_crockerB

/-- Every `crockerB r` satisfies `crockerB r % 16 ∈ {1, 3, 5}`. -/
theorem crockerB_mod_sixteen_cases (r : ℕ) :
    crockerB r % 16 = 1 ∨ crockerB r % 16 = 3 ∨ crockerB r % 16 = 5 := by
  unfold crockerB
  split_ifs with hr
  · left; exact crockerN0_base_props.2.2.2.2.2.2.1
  · exact fermatNumber_mod_sixteen_cases r

#print axioms Erdos9.crockerB_mod_sixteen_cases

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

#print axioms Erdos9.crockerB_dvd_fermatNumber

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

#print axioms Erdos9.odd_coprime_of_sub_eq_two

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

#print axioms Erdos9.coprime_fermatNumber_two_pow_1024_sub_one

/-- For every `10 ≤ r < crockerExp t`, `fermatNumber r` divides `crockerU t`. -/
theorem fermatNumber_dvd_crockerU {t r : ℕ} (hr10 : 10 ≤ r) (hr : r < crockerExp t) :
    fermatNumber r ∣ crockerU t := by
  have hdvd_prod : fermatNumber r ∣ (2 ^ 1024 - 1) * crockerU t := by
    rw [mul_crockerU_eq]
    simpa [fermatNumber, mul_one] using fermatNumber_dvd_two_pow_two_pow_mul_sub_one hr 1
  exact (coprime_fermatNumber_two_pow_1024_sub_one hr10).dvd_of_dvd_mul_left hdvd_prod

#print axioms Erdos9.fermatNumber_dvd_crockerU

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

#print axioms Erdos9.crockerB_dvd_crockerN

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

#print axioms Erdos9.fifteen_mul_crockerB_le_crockerN

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

#print axioms Erdos9.crockerN_mem_erdos9A

/-- Every term `crockerN t` belongs to `Erdos9APos`. -/
theorem crockerN_mem_erdos9APos (t : ℕ) : crockerN t ∈ Erdos9APos :=
  erdos9A_subset_erdos9APos (crockerN_mem_erdos9A t)

#print axioms Erdos9.crockerN_mem_erdos9APos

/-- Unconditional proof of Crocker's (1971) / Schinzel's theorem (`erdos_9.variants.infinite`):
the set `Erdos9A` of odd integers not expressible as `p + 2 ^ k + 2 ^ l` is infinite. -/
theorem erdos9A_infinite : Erdos9A.Infinite :=
  Set.infinite_of_injective_forall_mem crockerN_strictMono.injective crockerN_mem_erdos9A

#print axioms Erdos9.erdos9A_infinite

/-- Unconditional infinitude of the positive-exponent exceptional set `Erdos9APos`. -/
theorem erdos9APos_infinite : Erdos9APos.Infinite :=
  erdos9A_infinite.mono erdos9A_subset_erdos9APos

#print axioms Erdos9.erdos9APos_infinite

/-- Explicit unbounded witness in `Erdos9A`: for every `N : ℕ`, there exists `n ∈ Erdos9A` with `N < n`. -/
theorem exists_gt_mem_erdos9A (N : ℕ) : ∃ n ∈ Erdos9A, N < n := by
  refine ⟨crockerN (N + 1), crockerN_mem_erdos9A (N + 1), ?_⟩
  have hle : N + 1 ≤ crockerN (N + 1) := crockerN_strictMono.id_le (N + 1)
  omega

#print axioms Erdos9.exists_gt_mem_erdos9A

/-! ## Section 4: Panaitopol's Two-Power Sum Uniqueness & Partial-Density Monotonicity -/

/-- No power of `2` can equal `2 ^ k + 2 ^ l` with strictly distinct exponents `k < l`. -/
theorem two_pow_ne_two_pow_add_two_pow_of_lt {m k l : ℕ} (hkl : k < l) :
    2 ^ m ≠ 2 ^ k + 2 ^ l := by
  intro heq
  have hkm : k < m := by
    have hlt : 2 ^ k < 2 ^ m := by
      have : 1 ≤ 2 ^ l := Nat.one_le_two_pow
      omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp hlt
  have hm_eq : 2 ^ m = 2 ^ k * 2 ^ (m - k) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (le_of_lt hkm)]
  have hsum_eq : 2 ^ k + 2 ^ l = 2 ^ k * (2 ^ (l - k) + 1) :=
    two_pow_add_two_pow_eq_mul_sub (le_of_lt hkl)
  have hpos : 0 < 2 ^ k := by positivity
  have hcancel : 2 ^ (m - k) = 2 ^ (l - k) + 1 :=
    Nat.eq_of_mul_eq_mul_left hpos (hm_eq.symm.trans (heq.trans hsum_eq))
  rcases two_pow_eq_one_or_mod_two_eq_zero (m - k) with ⟨h0, -⟩ | ⟨-, hmod1⟩
  · omega
  · rcases two_pow_eq_one_or_mod_two_eq_zero (l - k) with ⟨h0, -⟩ | ⟨-, hmod2⟩ <;> omega

#print axioms Erdos9.two_pow_ne_two_pow_add_two_pow_of_lt

/-- Uniqueness of off-diagonal two-power sums: for `k₁ < l₁` and `k₂ < l₂`,
`2 ^ k₁ + 2 ^ l₁ = 2 ^ k₂ + 2 ^ l₂ ↔ k₁ = k₂ ∧ l₁ = l₂`. -/
theorem two_pow_add_two_pow_eq_iff_of_lt {k₁ l₁ k₂ l₂ : ℕ}
    (h1 : k₁ < l₁) (h2 : k₂ < l₂) :
    2 ^ k₁ + 2 ^ l₁ = 2 ^ k₂ + 2 ^ l₂ ↔ k₁ = k₂ ∧ l₁ = l₂ := by
  constructor
  · intro heq
    have hk_eq : k₁ = k₂ := by
      rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
      · exfalso
        have lhs_eq : 2 ^ k₁ + 2 ^ l₁ = 2 ^ k₁ * (2 ^ (l₁ - k₁) + 1) :=
          two_pow_add_two_pow_eq_mul_sub (le_of_lt h1)
        have rhs_eq : 2 ^ k₂ + 2 ^ l₂ = 2 ^ k₁ * (2 ^ (k₂ - k₁) + 2 ^ (l₂ - k₁)) := by
          rw [mul_add, ← Nat.pow_add, ← Nat.pow_add,
            Nat.add_sub_of_le (le_of_lt hlt), Nat.add_sub_of_le (le_of_lt (lt_trans hlt h2))]
        have hpos : 0 < 2 ^ k₁ := by positivity
        have hcancel : 2 ^ (l₁ - k₁) + 1 = 2 ^ (k₂ - k₁) + 2 ^ (l₂ - k₁) :=
          Nat.eq_of_mul_eq_mul_left hpos (lhs_eq.symm.trans (heq.trans rhs_eq))
        rcases two_pow_eq_one_or_mod_two_eq_zero (l₁ - k₁) with ⟨h0, -⟩ | ⟨-, hm1⟩
        · omega
        · rcases two_pow_eq_one_or_mod_two_eq_zero (k₂ - k₁) with ⟨h0, -⟩ | ⟨-, hm2⟩
          · omega
          · rcases two_pow_eq_one_or_mod_two_eq_zero (l₂ - k₁) with ⟨h0, -⟩ | ⟨-, hm3⟩ <;> omega
      · rfl
      · exfalso
        have rhs_eq : 2 ^ k₂ + 2 ^ l₂ = 2 ^ k₂ * (2 ^ (l₂ - k₂) + 1) :=
          two_pow_add_two_pow_eq_mul_sub (le_of_lt h2)
        have lhs_eq : 2 ^ k₁ + 2 ^ l₁ = 2 ^ k₂ * (2 ^ (k₁ - k₂) + 2 ^ (l₁ - k₂)) := by
          rw [mul_add, ← Nat.pow_add, ← Nat.pow_add,
            Nat.add_sub_of_le (le_of_lt hgt), Nat.add_sub_of_le (le_of_lt (lt_trans hgt h1))]
        have hpos : 0 < 2 ^ k₂ := by positivity
        have hcancel : 2 ^ (k₁ - k₂) + 2 ^ (l₁ - k₂) = 2 ^ (l₂ - k₂) + 1 :=
          Nat.eq_of_mul_eq_mul_left hpos (lhs_eq.symm.trans (heq.trans rhs_eq))
        rcases two_pow_eq_one_or_mod_two_eq_zero (l₂ - k₂) with ⟨h0, -⟩ | ⟨-, hm1⟩
        · omega
        · rcases two_pow_eq_one_or_mod_two_eq_zero (k₁ - k₂) with ⟨h0, -⟩ | ⟨-, hm2⟩
          · omega
          · rcases two_pow_eq_one_or_mod_two_eq_zero (l₁ - k₂) with ⟨h0, -⟩ | ⟨-, hm3⟩ <;> omega
    subst hk_eq
    have hl_pow : 2 ^ l₁ = 2 ^ l₂ := by omega
    exact ⟨rfl, Nat.pow_right_injective (by decide) hl_pow⟩
  · rintro ⟨rfl, rfl⟩
    rfl

#print axioms Erdos9.two_pow_add_two_pow_eq_iff_of_lt

/-- Panaitopol's (2001) unique representation theorem for ordered sums of two powers of `2`:
for all `k₁ ≤ l₁` and `k₂ ≤ l₂`, `2 ^ k₁ + 2 ^ l₁ = 2 ^ k₂ + 2 ^ l₂ ↔ k₁ = k₂ ∧ l₁ = l₂`. -/
theorem two_pow_add_two_pow_eq_iff_of_le {k₁ l₁ k₂ l₂ : ℕ}
    (h1 : k₁ ≤ l₁) (h2 : k₂ ≤ l₂) :
    2 ^ k₁ + 2 ^ l₁ = 2 ^ k₂ + 2 ^ l₂ ↔ k₁ = k₂ ∧ l₁ = l₂ := by
  rcases eq_or_lt_of_le h1 with rfl | hlt1 <;> rcases eq_or_lt_of_le h2 with rfl | hlt2
  · constructor
    · intro heq
      rw [two_pow_add_self, two_pow_add_self] at heq
      have hsucc := Nat.pow_right_injective (by decide) heq
      omega
    · rintro ⟨rfl, -⟩
      rfl
  · constructor
    · intro heq
      rw [two_pow_add_self] at heq
      exact False.elim (two_pow_ne_two_pow_add_two_pow_of_lt hlt2 heq)
    · rintro ⟨rfl, rfl⟩
      exact False.elim (lt_irrefl _ hlt2)
  · constructor
    · intro heq
      rw [two_pow_add_self] at heq
      exact False.elim (two_pow_ne_two_pow_add_two_pow_of_lt hlt1 heq.symm)
    · rintro ⟨rfl, rfl⟩
      exact False.elim (lt_irrefl _ hlt1)
  · exact two_pow_add_two_pow_eq_iff_of_lt hlt1 hlt2

#print axioms Erdos9.two_pow_add_two_pow_eq_iff_of_le

/-- Ordered exponent pairs `(k, l)` with `0 ≤ k ≤ l ≤ m`. -/
def twoPowPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter (fun p => p.1 ≤ p.2)

/-- Finite set of two-power sums `2 ^ k + 2 ^ l` generated by exponents `0 ≤ k ≤ l ≤ m`. -/
def twoPowSums (m : ℕ) : Finset ℕ :=
  (twoPowPairs m).image (fun p => 2 ^ p.1 + 2 ^ p.2)

/-- Membership characterization for `twoPowSums m`. -/
theorem mem_twoPowSums_iff (m n : ℕ) :
    n ∈ twoPowSums m ↔ ∃ k l : ℕ, k ≤ l ∧ l ≤ m ∧ n = 2 ^ k + 2 ^ l := by
  unfold twoPowSums twoPowPairs
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨k, l, ⟨⟨_, hl⟩, hkl⟩, rfl⟩
    exact ⟨k, l, hkl, by omega, rfl⟩
  · rintro ⟨k, l, hkl, hlm, rfl⟩
    exact ⟨k, l, ⟨⟨by omega, by omega⟩, hkl⟩, rfl⟩

#print axioms Erdos9.mem_twoPowSums_iff

/-- Exact cardinality equality `(twoPowSums m).card = (twoPowPairs m).card` via
Panaitopol's unique representation theorem. -/
theorem card_twoPowSums_eq_card_twoPowPairs (m : ℕ) :
    (twoPowSums m).card = (twoPowPairs m).card := by
  unfold twoPowSums
  apply Finset.card_image_of_injOn
  intro p₁ hp₁ p₂ hp₂ heq
  have hle₁ : p₁.1 ≤ p₁.2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
  have hle₂ : p₂.1 ≤ p₂.2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
  rcases (two_pow_add_two_pow_eq_iff_of_le hle₁ hle₂).mp heq with ⟨h1, h2⟩
  exact Prod.ext h1 h2

#print axioms Erdos9.card_twoPowSums_eq_card_twoPowPairs

/-- Monotonicity of partial density from `Erdos9A` to `Erdos9APos`:
for every reference set `A : Set ℕ` and bound `b : ℕ`,
`Erdos9A.partialDensity A b ≤ Erdos9APos.partialDensity A b`. -/
theorem erdos9A_partialDensity_le_erdos9APos_partialDensity (A : Set ℕ) (b : ℕ) :
    Erdos9A.partialDensity A b ≤ Erdos9APos.partialDensity A b := by
  unfold Set.partialDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mod_cast Set.ncard_le_ncard
    (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _ erdos9A_subset_erdos9APos))

#print axioms Erdos9.erdos9A_partialDensity_le_erdos9APos_partialDensity

end Erdos9


@[expose] public noncomputable section
open scoped BigOperators

/-!
# Erdős Problem 9: Panaitopol's (2001) Closed-Form Two-Power Sum Evaluation and Romanoff-Type Density Bounds

Develops 27 universally quantified structural theorems in Lean 4.35.0-rc2 advancing Erdős Problem #9:
1. Proves Panaitopol's (2001) explicit closed-form cardinality identities
   `2 * (twoPowPairs m).card = (m + 1) * (m + 2)`,
   `(twoPowPairs m).card = (m + 1) * (m + 2) / 2`, and
   `(twoPowSums m).card = (m + 1) * (m + 2) / 2` via an exact top-column inductive decomposition.
2. Partitions `twoPowSums m` into diagonal sums `diagTwoPowSums m` (`2 ^ k + 2 ^ k`, cardinality `m + 1`)
   and strictly off-diagonal sums `offDiagTwoPowSums m` (`2 ^ k + 2 ^ l` with `k < l ≤ m`),
   proving their disjointness and closed-form cardinality `(offDiagTwoPowSums m).card = m * (m + 1) / 2`.
3. Formalizes the Romanoff-type prime-plus-two-power finite sumset `romanoffSumset N m`, proving
   that every representable `n < 2 ^ (m + 1)` lies in `romanoffSumset (2 ^ (m + 1)) m` and bounding
   `2 * (OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1))).ncard ≤ (primesBelow (2 ^ (m + 1))).card * ((m + 1) * (m + 2))`.
4. Establishes the exact partial-density conservation identity
   `Erdos9A.partialDensity Set.univ N + OddPrimePlusTwoPowers.partialDensity Set.univ N = ({n : ℕ | Odd n} : Set ℕ).partialDensity Set.univ N`
   and the resulting Romanoff-Panaitopol dyadic partial-density bounds for `OddPrimePlusTwoPowers` and `Erdos9A`.
-/

namespace Erdos9

/-! ## Section 1: Panaitopol's (2001) Closed-Form Evaluation of `(twoPowPairs m).card` and `(twoPowSums m).card` -/

/-- Characterization of membership in `twoPowPairs m`: a pair `p = (k, l)` lies in `twoPowPairs m`
if and only if `p.1 ≤ p.2` and `p.2 ≤ m`. -/
theorem mem_twoPowPairs_iff (m : ℕ) (p : ℕ × ℕ) :
    p ∈ twoPowPairs m ↔ p.1 ≤ p.2 ∧ p.2 ≤ m := by
  unfold twoPowPairs
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

#print axioms Erdos9.mem_twoPowPairs_iff

/-- Monotonicity of `twoPowPairs` in the exponent bound `m`. -/
theorem twoPowPairs_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    twoPowPairs m₁ ⊆ twoPowPairs m₂ := by
  intro p hp
  rw [mem_twoPowPairs_iff] at hp ⊢
  omega

#print axioms Erdos9.twoPowPairs_mono

/-- Monotonicity of `twoPowSums` in the exponent bound `m`. -/
theorem twoPowSums_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    twoPowSums m₁ ⊆ twoPowSums m₂ := by
  unfold twoPowSums
  exact Finset.image_subset_image (twoPowPairs_mono h)

#print axioms Erdos9.twoPowSums_mono

/-- Exact decomposition of `twoPowPairs (m + 1)` into `twoPowPairs m` and the top column
`{(k, m + 1) | k < m + 2}`. -/
theorem twoPowPairs_succ_eq_union (m : ℕ) :
    twoPowPairs (m + 1) =
      twoPowPairs m ∪ (Finset.range (m + 2)).image (fun k => (k, m + 1)) := by
  ext ⟨k, l⟩
  simp only [Finset.mem_union, mem_twoPowPairs_iff, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨hkl, hlm1⟩
    rcases eq_or_lt_of_le hlm1 with rfl | hlt
    · exact Or.inr ⟨k, by omega, rfl, rfl⟩
    · exact Or.inl ⟨hkl, by omega⟩
  · rintro (⟨hkl, hlm⟩ | ⟨a, ha, rfl, rfl⟩) <;> omega

#print axioms Erdos9.twoPowPairs_succ_eq_union

/-- Disjointness of `twoPowPairs m` and the top column `{(k, m + 1) | k < m + 2}`. -/
theorem disjoint_twoPowPairs_topColumn (m : ℕ) :
    Disjoint (twoPowPairs m) ((Finset.range (m + 2)).image (fun k => (k, m + 1))) := by
  rw [Finset.disjoint_left]
  intro ⟨k, l⟩ h1 h2
  rw [mem_twoPowPairs_iff] at h1
  simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at h2
  rcases h2 with ⟨a, _, _, rfl⟩
  omega

#print axioms Erdos9.disjoint_twoPowPairs_topColumn

/-- Exact cardinality `m + 2` of the top column `{(k, m + 1) | k < m + 2}`. -/
theorem card_topColumn_eq (m : ℕ) :
    ((Finset.range (m + 2)).image (fun k => (k, m + 1))).card = m + 2 := by
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range (m + 2)
  · intro a b h
    exact (Prod.mk.injEq a (m + 1) b (m + 1)).mp h |>.1

#print axioms Erdos9.card_topColumn_eq

/-- Additive recurrence `(twoPowPairs (m + 1)).card = (twoPowPairs m).card + (m + 2)`. -/
theorem card_twoPowPairs_succ (m : ℕ) :
    (twoPowPairs (m + 1)).card = (twoPowPairs m).card + (m + 2) := by
  rw [twoPowPairs_succ_eq_union, Finset.card_union_of_disjoint (disjoint_twoPowPairs_topColumn m),
    card_topColumn_eq]

#print axioms Erdos9.card_twoPowPairs_succ

/-- Exact multiplicative identity `2 * (twoPowPairs m).card = (m + 1) * (m + 2)`. -/
theorem two_mul_card_twoPowPairs_eq (m : ℕ) :
    2 * (twoPowPairs m).card = (m + 1) * (m + 2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [card_twoPowPairs_succ, Nat.mul_add, ih]
    ring

#print axioms Erdos9.two_mul_card_twoPowPairs_eq

/-- Panaitopol's (2001) closed-form evaluation `(twoPowPairs m).card = (m + 1) * (m + 2) / 2`. -/
theorem card_twoPowPairs_eq (m : ℕ) :
    (twoPowPairs m).card = (m + 1) * (m + 2) / 2 := by
  rw [← two_mul_card_twoPowPairs_eq, Nat.mul_div_right _ (by decide)]

#print axioms Erdos9.card_twoPowPairs_eq

/-- Panaitopol's (2001) closed-form evaluation `(twoPowSums m).card = (m + 1) * (m + 2) / 2`
for the number of distinct sums `2 ^ k + 2 ^ l` with `0 ≤ k ≤ l ≤ m`. -/
theorem card_twoPowSums_eq (m : ℕ) :
    (twoPowSums m).card = (m + 1) * (m + 2) / 2 := by
  rw [card_twoPowSums_eq_card_twoPowPairs, card_twoPowPairs_eq]

#print axioms Erdos9.card_twoPowSums_eq

/-! ## Section 2: Diagonal vs. Off-Diagonal Decomposition of `twoPowSums` -/

/-- Diagonal two-power sums `{2 ^ k + 2 ^ k | 0 ≤ k ≤ m}`. -/
def diagTwoPowSums (m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).image (fun k => 2 ^ k + 2 ^ k)

/-- Strictly off-diagonal exponent pairs `{(k, l) | 0 ≤ k < l ≤ m}`. -/
def offDiagTwoPowPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  (twoPowPairs m).filter (fun p => p.1 < p.2)

/-- Strictly off-diagonal two-power sums `{2 ^ k + 2 ^ l | 0 ≤ k < l ≤ m}`. -/
def offDiagTwoPowSums (m : ℕ) : Finset ℕ :=
  (offDiagTwoPowPairs m).image (fun p => 2 ^ p.1 + 2 ^ p.2)

/-- Exact cardinality `(diagTwoPowSums m).card = m + 1`. -/
theorem card_diagTwoPowSums_eq (m : ℕ) :
    (diagTwoPowSums m).card = m + 1 := by
  unfold diagTwoPowSums
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range (m + 1)
  · intro a b h
    dsimp at h
    rw [two_pow_add_self, two_pow_add_self] at h
    have hsucc := Nat.pow_right_injective (by decide) h
    omega

#print axioms Erdos9.card_diagTwoPowSums_eq

/-- Disjointness of diagonal sums `diagTwoPowSums m` and strictly off-diagonal sums `offDiagTwoPowSums m`. -/
theorem disjoint_diagTwoPowSums_offDiagTwoPowSums (m : ℕ) :
    Disjoint (diagTwoPowSums m) (offDiagTwoPowSums m) := by
  rw [Finset.disjoint_left]
  intro n hd ho
  unfold diagTwoPowSums at hd
  unfold offDiagTwoPowSums offDiagTwoPowPairs at ho
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Prod.exists] at hd ho
  rcases hd with ⟨a, _, ha_eq⟩
  rcases ho with ⟨k, l, ⟨_, hkl⟩, hkl_eq⟩
  rw [two_pow_add_self] at ha_eq
  exact two_pow_ne_two_pow_add_two_pow_of_lt hkl (ha_eq.trans hkl_eq.symm)

#print axioms Erdos9.disjoint_diagTwoPowSums_offDiagTwoPowSums

/-- Exact partition `twoPowSums m = diagTwoPowSums m ∪ offDiagTwoPowSums m`. -/
theorem twoPowSums_eq_union_diag_offDiag (m : ℕ) :
    twoPowSums m = diagTwoPowSums m ∪ offDiagTwoPowSums m := by
  ext n
  simp only [Finset.mem_union, mem_twoPowSums_iff, diagTwoPowSums, offDiagTwoPowSums,
    offDiagTwoPowPairs, Finset.mem_image, Finset.mem_range, Finset.mem_filter,
    mem_twoPowPairs_iff, Prod.exists]
  constructor
  · rintro ⟨k, l, hkl, hlm, rfl⟩
    rcases eq_or_lt_of_le hkl with rfl | hlt
    · exact Or.inl ⟨k, by omega, rfl⟩
    · exact Or.inr ⟨k, l, ⟨⟨hkl, hlm⟩, hlt⟩, rfl⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, l, ⟨⟨hkl, hlm⟩, _⟩, rfl⟩)
    · exact ⟨k, k, le_rfl, by omega, rfl⟩
    · exact ⟨k, l, hkl, hlm, rfl⟩

#print axioms Erdos9.twoPowSums_eq_union_diag_offDiag

/-- Additive cardinality split `(twoPowSums m).card = (m + 1) + (offDiagTwoPowSums m).card`. -/
theorem card_twoPowSums_eq_add_offDiag (m : ℕ) :
    (twoPowSums m).card = (m + 1) + (offDiagTwoPowSums m).card := by
  rw [twoPowSums_eq_union_diag_offDiag,
    Finset.card_union_of_disjoint (disjoint_diagTwoPowSums_offDiagTwoPowSums m),
    card_diagTwoPowSums_eq]

#print axioms Erdos9.card_twoPowSums_eq_add_offDiag

/-- Exact multiplicative identity `2 * (offDiagTwoPowSums m).card = m * (m + 1)`. -/
theorem two_mul_card_offDiagTwoPowSums_eq (m : ℕ) :
    2 * (offDiagTwoPowSums m).card = m * (m + 1) := by
  have h1 : 2 * (twoPowSums m).card = (m + 1) * (m + 2) := by
    rw [card_twoPowSums_eq_card_twoPowPairs, two_mul_card_twoPowPairs_eq]
  have h2 := card_twoPowSums_eq_add_offDiag m
  nlinarith

#print axioms Erdos9.two_mul_card_offDiagTwoPowSums_eq

/-- Closed-form cardinality `(offDiagTwoPowSums m).card = m * (m + 1) / 2` of strictly off-diagonal
two-power sums up to exponent `m`. -/
theorem card_offDiagTwoPowSums_eq (m : ℕ) :
    (offDiagTwoPowSums m).card = m * (m + 1) / 2 := by
  rw [← two_mul_card_offDiagTwoPowSums_eq, Nat.mul_div_right _ (by decide)]

#print axioms Erdos9.card_offDiagTwoPowSums_eq

/-! ## Section 3: Romanoff-Type Prime-Plus-Two-Powers Finite Sumset & Counting Bounds -/

/-- Finite set of primes strictly below `N`. -/
def primesBelow (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter Nat.Prime

/-- Finite Romanoff sumset `{p + s | p ∈ primesBelow N, s ∈ twoPowSums m}`. -/
def romanoffSumset (N m : ℕ) : Finset ℕ :=
  ((primesBelow N) ×ˢ (twoPowSums m)).image (fun x => x.1 + x.2)

/-- The set of odd integers expressible as `p + 2 ^ k + 2 ^ l` with `p` prime (`Odd \ Erdos9A`). -/
def OddPrimePlusTwoPowers : Set ℕ :=
  { n | Odd n ∧ IsPrimePlusTwoPowers n }

/-- Every two-power sum `2 ^ k + 2 ^ l < 2 ^ (m + 1)` belongs to `twoPowSums m`. -/
theorem mem_twoPowSums_of_add_lt_two_pow_succ {k l m : ℕ}
    (hlt : 2 ^ k + 2 ^ l < 2 ^ (m + 1)) :
    2 ^ k + 2 ^ l ∈ twoPowSums m := by
  rw [mem_twoPowSums_iff]
  have hk_lt : k < m + 1 :=
    (Nat.pow_lt_pow_iff_right (by decide)).mp (lt_of_le_of_lt (Nat.le_add_right _ _) hlt)
  have hl_lt : l < m + 1 :=
    (Nat.pow_lt_pow_iff_right (by decide)).mp (lt_of_le_of_lt (Nat.le_add_left _ _) hlt)
  rcases le_total k l with hkl | hlk
  · exact ⟨k, l, hkl, by omega, rfl⟩
  · exact ⟨l, k, hlk, by omega, by omega⟩

#print axioms Erdos9.mem_twoPowSums_of_add_lt_two_pow_succ

/-- Every integer `n < 2 ^ (m + 1)` satisfying `IsPrimePlusTwoPowers n` lies in the finite sumset
`romanoffSumset (2 ^ (m + 1)) m`. -/
theorem mem_romanoffSumset_of_isPrimePlusTwoPowers_lt_two_pow {n m : ℕ}
    (hrep : IsPrimePlusTwoPowers n) (hlt : n < 2 ^ (m + 1)) :
    n ∈ romanoffSumset (2 ^ (m + 1)) m := by
  rcases hrep with ⟨p, k, l, hp, rfl⟩
  unfold romanoffSumset primesBelow
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_range, Prod.exists]
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hl1 : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hp_lt : p < 2 ^ (m + 1) := lt_of_le_of_lt (by omega) hlt
  have hsum_lt : 2 ^ k + 2 ^ l < 2 ^ (m + 1) := lt_of_le_of_lt (by omega) hlt
  exact ⟨p, 2 ^ k + 2 ^ l, ⟨⟨hp_lt, hp⟩, mem_twoPowSums_of_add_lt_two_pow_succ hsum_lt⟩, by omega⟩

#print axioms Erdos9.mem_romanoffSumset_of_isPrimePlusTwoPowers_lt_two_pow

/-- Product upper bound `(romanoffSumset N m).card ≤ (primesBelow N).card * (twoPowSums m).card`. -/
theorem card_romanoffSumset_le_mul (N m : ℕ) :
    (romanoffSumset N m).card ≤ (primesBelow N).card * (twoPowSums m).card := by
  unfold romanoffSumset
  calc
    (((primesBelow N) ×ˢ (twoPowSums m)).image (fun x => x.1 + x.2)).card ≤
        ((primesBelow N) ×ˢ (twoPowSums m)).card := Finset.card_image_le
    _ = (primesBelow N).card * (twoPowSums m).card := Finset.card_product _ _

#print axioms Erdos9.card_romanoffSumset_le_mul

/-- Closed-form Panaitopol-Romanoff sumset bound
`2 * (romanoffSumset N m).card ≤ (primesBelow N).card * ((m + 1) * (m + 2))`. -/
theorem two_mul_card_romanoffSumset_le (N m : ℕ) :
    2 * (romanoffSumset N m).card ≤ (primesBelow N).card * ((m + 1) * (m + 2)) := by
  have h1 := Nat.mul_le_mul_left 2 (card_romanoffSumset_le_mul N m)
  have h2 : 2 * ((primesBelow N).card * (twoPowSums m).card) =
      (primesBelow N).card * (2 * (twoPowSums m).card) := by ring
  rw [h2, card_twoPowSums_eq_card_twoPowPairs, two_mul_card_twoPowPairs_eq] at h1
  exact h1

#print axioms Erdos9.two_mul_card_romanoffSumset_le

/-- Prefix counting bound for `IsPrimePlusTwoPowers` below `2 ^ (m + 1)` via `romanoffSumset`. -/
theorem ncard_isPrimePlusTwoPowers_Iio_two_pow_le_romanoffSumset (m : ℕ) :
    ({n : ℕ | IsPrimePlusTwoPowers n} ∩ Set.Iio (2 ^ (m + 1))).ncard ≤
      (romanoffSumset (2 ^ (m + 1)) m).card := by
  have hsub : {n : ℕ | IsPrimePlusTwoPowers n} ∩ Set.Iio (2 ^ (m + 1)) ⊆
      (romanoffSumset (2 ^ (m + 1)) m : Set ℕ) := by
    rintro n ⟨hrep, hlt⟩
    exact Finset.mem_coe.mpr
      (mem_romanoffSumset_of_isPrimePlusTwoPowers_lt_two_pow hrep (Set.mem_Iio.mp hlt))
  calc
    ({n : ℕ | IsPrimePlusTwoPowers n} ∩ Set.Iio (2 ^ (m + 1))).ncard ≤
        (romanoffSumset (2 ^ (m + 1)) m : Set ℕ).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (romanoffSumset (2 ^ (m + 1)) m).card := Set.ncard_coe_finset _

#print axioms Erdos9.ncard_isPrimePlusTwoPowers_Iio_two_pow_le_romanoffSumset

/-- Dyadic counting bound for odd representable integers `OddPrimePlusTwoPowers` below `2 ^ (m + 1)`. -/
theorem two_mul_ncard_oddPrimePlusTwoPowers_Iio_two_pow_le (m : ℕ) :
    2 * (OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1))).ncard ≤
      (primesBelow (2 ^ (m + 1))).card * ((m + 1) * (m + 2)) := by
  have hsub : OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1)) ⊆
      {n : ℕ | IsPrimePlusTwoPowers n} ∩ Set.Iio (2 ^ (m + 1)) := by
    rintro n ⟨⟨_, hrep⟩, hlt⟩
    exact ⟨hrep, hlt⟩
  have hfin : ({n : ℕ | IsPrimePlusTwoPowers n} ∩ Set.Iio (2 ^ (m + 1))).Finite :=
    (Set.finite_lt_nat _).subset Set.inter_subset_right
  have hle1 : (OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1))).ncard ≤
      (romanoffSumset (2 ^ (m + 1)) m).card :=
    le_trans (Set.ncard_le_ncard hsub hfin)
      (ncard_isPrimePlusTwoPowers_Iio_two_pow_le_romanoffSumset m)
  exact le_trans (Nat.mul_le_mul_left 2 hle1)
    (two_mul_card_romanoffSumset_le (2 ^ (m + 1)) m)

#print axioms Erdos9.two_mul_ncard_oddPrimePlusTwoPowers_Iio_two_pow_le

/-! ## Section 4: Partial-Density Conservation and Romanoff-Panaitopol Density Bounds -/

/-- Pointwise partition of odd numbers into `Erdos9A` and `OddPrimePlusTwoPowers`. -/
theorem erdos9A_union_oddPrimePlusTwoPowers_eq_odd (n : ℕ) :
    n ∈ Erdos9A ∪ OddPrimePlusTwoPowers ↔ Odd n := by
  unfold Erdos9A OddPrimePlusTwoPowers IsPrimePlusTwoPowers
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  tauto

#print axioms Erdos9.erdos9A_union_oddPrimePlusTwoPowers_eq_odd

/-- Pointwise disjointness of `Erdos9A` and `OddPrimePlusTwoPowers`. -/
theorem disjoint_erdos9A_oddPrimePlusTwoPowers (n : ℕ) :
    ¬ (n ∈ Erdos9A ∧ n ∈ OddPrimePlusTwoPowers) := by
  rintro ⟨⟨_, hnot⟩, ⟨_, hrep⟩⟩
  exact hnot hrep

#print axioms Erdos9.disjoint_erdos9A_oddPrimePlusTwoPowers

/-- Exact finite prefix counting conservation law: on every prefix `[0, N)`, the counts of
`Erdos9A` and `OddPrimePlusTwoPowers` sum to the count of odd integers below `N`. -/
theorem ncard_erdos9A_add_ncard_oddPrimePlusTwoPowers_Iio (N : ℕ) :
    (Erdos9A ∩ Set.Iio N).ncard + (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard =
      ({n : ℕ | Odd n} ∩ Set.Iio N).ncard := by
  have hunion : (Erdos9A ∩ Set.Iio N) ∪ (OddPrimePlusTwoPowers ∩ Set.Iio N) =
      {n : ℕ | Odd n} ∩ Set.Iio N := by
    ext n
    have h1 := erdos9A_union_oddPrimePlusTwoPowers_eq_odd n
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq] at h1 ⊢
    tauto
  have hdisj : Disjoint (Erdos9A ∩ Set.Iio N) (OddPrimePlusTwoPowers ∩ Set.Iio N) := by
    rw [Set.disjoint_left]
    rintro n ⟨h1, _⟩ ⟨h2, _⟩
    exact disjoint_erdos9A_oddPrimePlusTwoPowers n ⟨h1, h2⟩
  have hfin1 : (Erdos9A ∩ Set.Iio N).Finite :=
    (Set.finite_lt_nat N).subset Set.inter_subset_right
  have hfin2 : (OddPrimePlusTwoPowers ∩ Set.Iio N).Finite :=
    (Set.finite_lt_nat N).subset Set.inter_subset_right
  rw [← Set.ncard_union_eq hdisj hfin1 hfin2, hunion]

#print axioms Erdos9.ncard_erdos9A_add_ncard_oddPrimePlusTwoPowers_Iio

/-- Exact partial-density conservation identity across all cutoffs `N : ℕ`:
`Erdos9A.partialDensity Set.univ N + OddPrimePlusTwoPowers.partialDensity Set.univ N = ({n : ℕ | Odd n} : Set ℕ).partialDensity Set.univ N`. -/
theorem partialDensity_erdos9A_add_oddPrimePlusTwoPowers (N : ℕ) :
    Erdos9A.partialDensity Set.univ N + OddPrimePlusTwoPowers.partialDensity Set.univ N =
      ({n : ℕ | Odd n} : Set ℕ).partialDensity Set.univ N := by
  unfold Set.partialDensity
  simp only [Set.inter_univ]
  rw [← add_div, ← Nat.cast_add, ncard_erdos9A_add_ncard_oddPrimePlusTwoPowers_Iio]

#print axioms Erdos9.partialDensity_erdos9A_add_oddPrimePlusTwoPowers

/-- Explicit Romanoff-Panaitopol upper bound on the dyadic partial density of `OddPrimePlusTwoPowers`
at `N = 2 ^ (m + 1)`. -/
theorem partialDensity_oddPrimePlusTwoPowers_two_pow_le (m : ℕ) :
    OddPrimePlusTwoPowers.partialDensity Set.univ (2 ^ (m + 1)) ≤
      (((primesBelow (2 ^ (m + 1))).card * ((m + 1) * (m + 2) / 2) : ℕ) : ℝ) / (2 ^ (m + 1) : ℝ) := by
  unfold Set.partialDensity
  have hden : ((Set.univ ∩ Set.Iio (2 ^ (m + 1))).ncard : ℝ) = (2 ^ (m + 1) : ℝ) := by
    simp [Set.univ_inter, Set.ncard_Iio]
  rw [Set.inter_univ, hden]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1)) ⊆
      {n : ℕ | IsPrimePlusTwoPowers n} ∩ Set.Iio (2 ^ (m + 1)) := by
    rintro n ⟨⟨_, hrep⟩, hlt⟩
    exact ⟨hrep, hlt⟩
  have hfin : ({n : ℕ | IsPrimePlusTwoPowers n} ∩ Set.Iio (2 ^ (m + 1))).Finite :=
    (Set.finite_lt_nat _).subset Set.inter_subset_right
  have hle : (OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1))).ncard ≤
      (primesBelow (2 ^ (m + 1))).card * ((m + 1) * (m + 2) / 2) := by
    calc
      (OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1))).ncard ≤
          (romanoffSumset (2 ^ (m + 1)) m).card :=
        le_trans (Set.ncard_le_ncard hsub hfin)
          (ncard_isPrimePlusTwoPowers_Iio_two_pow_le_romanoffSumset m)
      _ ≤ (primesBelow (2 ^ (m + 1))).card * (twoPowSums m).card :=
        card_romanoffSumset_le_mul _ _
      _ = (primesBelow (2 ^ (m + 1))).card * ((m + 1) * (m + 2) / 2) := by
        rw [card_twoPowSums_eq]
  exact_mod_cast hle

#print axioms Erdos9.partialDensity_oddPrimePlusTwoPowers_two_pow_le

end Erdos9


@[expose] public noncomputable section
open scoped BigOperators

namespace Erdos9

/-!
# Erdős Problem 9: Cauchy-Schwarz Second-Moment Representation-Multiplicity and Lower-Density Bounds

Develops universally quantified structural theorems in Lean 4.35.0-rc2 for the Romanoff
representation-multiplicity function on `primesBelow N ×ˢ twoPowSums m`:
1. Defines the fiberwise representation set `romanoffRepPairs N m n`, multiplicity
   `romanoffRepCount N m n`, first moment `romanoffFirstMoment N m`, and second moment
   (additive energy) `romanoffSecondMoment N m`, proving the exact closed-form first-moment
   identities `romanoffFirstMoment N m = (primesBelow N).card * (twoPowSums m).card` and
   `2 * romanoffFirstMoment N m = (primesBelow N).card * ((m + 1) * (m + 2))`.
2. Proves the universal Cauchy-Schwarz second-moment support inequality
   `(romanoffFirstMoment N m) ^ 2 ≤ (romanoffSumset N m).card * romanoffSecondMoment N m`
   and its closed-form corollaries.
3. Restricts to the odd prefix support `oddRomanoffSupport N m`, proving exact inclusion
   into `OddPrimePlusTwoPowers ∩ Set.Iio N`, exact set equality at dyadic horizons
   `N = 2 ^ (m + 1)`, and the Cauchy-Schwarz prefix lower bound
   `(oddPrefixFirstMoment N m) ^ 2 ≤ (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard * oddPrefixSecondMoment N m`.
4. Derives explicit lower bounds on `OddPrimePlusTwoPowers.partialDensity Set.univ N` and
   complementary upper bounds on `Erdos9A.partialDensity Set.univ N` from linear second-moment
   ceilings, together with certified finite-horizon pilot controls at `(N, m) = (8, 2)` and `(16, 3)`.
-/

/-! ## Section 1: Fiberwise Representation Multiplicity and Moment Identities -/

/-- Fiber of representations `(p, s) ∈ primesBelow N ×ˢ twoPowSums m` with `p + s = n`. -/
def romanoffRepPairs (N m n : ℕ) : Finset (ℕ × ℕ) :=
  ((primesBelow N) ×ˢ (twoPowSums m)).filter (fun x => x.1 + x.2 = n)

/-- Representation multiplicity `r_{N, m}(n)` of `n` as `p + s` with `p ∈ primesBelow N`
and `s ∈ twoPowSums m`. -/
def romanoffRepCount (N m n : ℕ) : ℕ :=
  (romanoffRepPairs N m n).card

/-- First moment `M_1(N, m) = ∑ n ∈ romanoffSumset N m, r_{N, m}(n)`. -/
def romanoffFirstMoment (N m : ℕ) : ℕ :=
  ∑ n ∈ romanoffSumset N m, romanoffRepCount N m n

/-- Second moment (additive representation energy) `M_2(N, m) = ∑ n ∈ romanoffSumset N m, r_{N, m}(n) ^ 2`. -/
def romanoffSecondMoment (N m : ℕ) : ℕ :=
  ∑ n ∈ romanoffSumset N m, (romanoffRepCount N m n) ^ 2

/-- Characterization of membership in the representation fiber `romanoffRepPairs N m n`. -/
theorem mem_romanoffRepPairs_iff (N m n : ℕ) (x : ℕ × ℕ) :
    x ∈ romanoffRepPairs N m n ↔ x.1 ∈ primesBelow N ∧ x.2 ∈ twoPowSums m ∧ x.1 + x.2 = n := by
  unfold romanoffRepPairs
  simp only [Finset.mem_filter, Finset.mem_product, and_assoc]

#print axioms Erdos9.mem_romanoffRepPairs_iff

/-- The representation multiplicity `romanoffRepCount N m n` is strictly positive if and only if
`n ∈ romanoffSumset N m`. -/
theorem romanoffRepCount_pos_iff_mem_romanoffSumset (N m n : ℕ) :
    0 < romanoffRepCount N m n ↔ n ∈ romanoffSumset N m := by
  unfold romanoffRepCount romanoffRepPairs romanoffSumset
  rw [Finset.card_pos, Finset.Nonempty]
  simp only [Finset.mem_filter, Finset.mem_image]

#print axioms Erdos9.romanoffRepCount_pos_iff_mem_romanoffSumset

/-- Outside `romanoffSumset N m`, the representation multiplicity vanishes. -/
theorem romanoffRepCount_eq_zero_of_not_mem_romanoffSumset {N m n : ℕ}
    (h : n ∉ romanoffSumset N m) :
    romanoffRepCount N m n = 0 := by
  by_contra hne
  exact h ((romanoffRepCount_pos_iff_mem_romanoffSumset N m n).mp (Nat.pos_of_ne_zero hne))

#print axioms Erdos9.romanoffRepCount_eq_zero_of_not_mem_romanoffSumset

/-- Every `n ∈ romanoffSumset N m` has representation multiplicity at least `1`. -/
theorem one_le_romanoffRepCount_of_mem_romanoffSumset {N m n : ℕ}
    (h : n ∈ romanoffSumset N m) :
    1 ≤ romanoffRepCount N m n :=
  (romanoffRepCount_pos_iff_mem_romanoffSumset N m n).mpr h

#print axioms Erdos9.one_le_romanoffRepCount_of_mem_romanoffSumset

/-- Exact fiberwise decomposition: the first moment over `romanoffSumset N m` equals the
cardinality of the Cartesian product `primesBelow N ×ˢ twoPowSums m`. -/
theorem romanoffFirstMoment_eq_card_product (N m : ℕ) :
    romanoffFirstMoment N m = ((primesBelow N) ×ˢ (twoPowSums m)).card := by
  unfold romanoffFirstMoment romanoffRepCount romanoffRepPairs romanoffSumset
  exact (Finset.card_eq_sum_card_image
    (fun x : ℕ × ℕ => x.1 + x.2) ((primesBelow N) ×ˢ (twoPowSums m))).symm

#print axioms Erdos9.romanoffFirstMoment_eq_card_product

/-- Product factorization of the first moment:
`romanoffFirstMoment N m = (primesBelow N).card * (twoPowSums m).card`. -/
theorem romanoffFirstMoment_eq_mul (N m : ℕ) :
    romanoffFirstMoment N m = (primesBelow N).card * (twoPowSums m).card := by
  rw [romanoffFirstMoment_eq_card_product, Finset.card_product]

#print axioms Erdos9.romanoffFirstMoment_eq_mul

/-- Closed-form doubled first-moment identity via Panaitopol's theorem:
`2 * romanoffFirstMoment N m = (primesBelow N).card * ((m + 1) * (m + 2))`. -/
theorem two_mul_romanoffFirstMoment_eq (N m : ℕ) :
    2 * romanoffFirstMoment N m = (primesBelow N).card * ((m + 1) * (m + 2)) := by
  rw [romanoffFirstMoment_eq_mul]
  calc
    2 * ((primesBelow N).card * (twoPowSums m).card) =
        (primesBelow N).card * (2 * (twoPowSums m).card) := by ring
    _ = (primesBelow N).card * ((m + 1) * (m + 2)) := by
      rw [card_twoPowSums_eq_card_twoPowPairs, two_mul_card_twoPowPairs_eq]

#print axioms Erdos9.two_mul_romanoffFirstMoment_eq

/-- Closed-form evaluation of `romanoffFirstMoment N m`:
`romanoffFirstMoment N m = (primesBelow N).card * ((m + 1) * (m + 2) / 2)`. -/
theorem romanoffFirstMoment_eq_closed_form (N m : ℕ) :
    romanoffFirstMoment N m = (primesBelow N).card * ((m + 1) * (m + 2) / 2) := by
  rw [romanoffFirstMoment_eq_mul, card_twoPowSums_eq]

#print axioms Erdos9.romanoffFirstMoment_eq_closed_form

/-- Support size is bounded above by the first moment:
`(romanoffSumset N m).card ≤ romanoffFirstMoment N m`. -/
theorem card_romanoffSumset_le_romanoffFirstMoment (N m : ℕ) :
    (romanoffSumset N m).card ≤ romanoffFirstMoment N m := by
  unfold romanoffFirstMoment
  calc
    (romanoffSumset N m).card = ∑ _n ∈ romanoffSumset N m, 1 := by simp
    _ ≤ ∑ n ∈ romanoffSumset N m, romanoffRepCount N m n :=
      Finset.sum_le_sum (fun n hn => one_le_romanoffRepCount_of_mem_romanoffSumset hn)

#print axioms Erdos9.card_romanoffSumset_le_romanoffFirstMoment

/-- First moment is bounded above by the second moment:
`romanoffFirstMoment N m ≤ romanoffSecondMoment N m`. -/
theorem romanoffFirstMoment_le_romanoffSecondMoment (N m : ℕ) :
    romanoffFirstMoment N m ≤ romanoffSecondMoment N m := by
  unfold romanoffFirstMoment romanoffSecondMoment
  refine Finset.sum_le_sum (fun n _ => ?_)
  nlinarith

#print axioms Erdos9.romanoffFirstMoment_le_romanoffSecondMoment

/-! ## Section 2: Universal Cauchy-Schwarz Second-Moment Support Lower Bounds -/

/-- Universal finite Cauchy-Schwarz inequality for natural-valued functions on a `Finset`:
`(∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2`. -/
theorem cauchy_schwarz_finset_sum_sq_le_card_mul_sum_sq {ι : Type*}
    (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℕ)) f
  simpa using h

#print axioms Erdos9.cauchy_schwarz_finset_sum_sq_le_card_mul_sum_sq

/-- Cauchy-Schwarz support lower bound on `romanoffSumset N m`:
`(romanoffFirstMoment N m) ^ 2 ≤ (romanoffSumset N m).card * romanoffSecondMoment N m`. -/
theorem romanoffFirstMoment_sq_le_card_romanoffSumset_mul_secondMoment (N m : ℕ) :
    (romanoffFirstMoment N m) ^ 2 ≤ (romanoffSumset N m).card * romanoffSecondMoment N m := by
  unfold romanoffFirstMoment romanoffSecondMoment
  exact cauchy_schwarz_finset_sum_sq_le_card_mul_sum_sq (romanoffSumset N m) (romanoffRepCount N m)

#print axioms Erdos9.romanoffFirstMoment_sq_le_card_romanoffSumset_mul_secondMoment

/-- Closed-form Cauchy-Schwarz inequality for `romanoffSumset N m`:
`((primesBelow N).card * ((m + 1) * (m + 2) / 2)) ^ 2 ≤ (romanoffSumset N m).card * romanoffSecondMoment N m`. -/
theorem closed_form_firstMoment_sq_le_card_romanoffSumset_mul_secondMoment (N m : ℕ) :
    ((primesBelow N).card * ((m + 1) * (m + 2) / 2)) ^ 2 ≤
      (romanoffSumset N m).card * romanoffSecondMoment N m := by
  rw [← romanoffFirstMoment_eq_closed_form]
  exact romanoffFirstMoment_sq_le_card_romanoffSumset_mul_secondMoment N m

#print axioms Erdos9.closed_form_firstMoment_sq_le_card_romanoffSumset_mul_secondMoment

/-- Division-free scaled Cauchy-Schwarz inequality for `romanoffSumset N m`:
`((primesBelow N).card * ((m + 1) * (m + 2))) ^ 2 ≤ 4 * ((romanoffSumset N m).card * romanoffSecondMoment N m)`. -/
theorem four_mul_card_romanoffSumset_mul_secondMoment_ge (N m : ℕ) :
    ((primesBelow N).card * ((m + 1) * (m + 2))) ^ 2 ≤
      4 * ((romanoffSumset N m).card * romanoffSecondMoment N m) := by
  have hcs := romanoffFirstMoment_sq_le_card_romanoffSumset_mul_secondMoment N m
  have h1 := two_mul_romanoffFirstMoment_eq N m
  nlinarith

#print axioms Erdos9.four_mul_card_romanoffSumset_mul_secondMoment_ge

/-- Integer division Cauchy-Schwarz lower bound on `(romanoffSumset N m).card`. -/
theorem card_romanoffSumset_ge_div_secondMoment (N m : ℕ) :
    (romanoffFirstMoment N m) ^ 2 / romanoffSecondMoment N m ≤ (romanoffSumset N m).card := by
  apply Nat.div_le_of_le_mul
  rw [mul_comm]
  exact romanoffFirstMoment_sq_le_card_romanoffSumset_mul_secondMoment N m

#print axioms Erdos9.card_romanoffSumset_ge_div_secondMoment

/-! ## Section 3: Odd Prefix Support `oddRomanoffSupport N m` and Exact Dyadic Identification -/

/-- Odd integers strictly below `N` belonging to `romanoffSumset N m`. -/
def oddRomanoffSupport (N m : ℕ) : Finset ℕ :=
  (romanoffSumset N m).filter (fun n => n % 2 = 1 ∧ n < N)

/-- Odd-prefix first moment `M_{1, odd}(N, m) = ∑ n ∈ oddRomanoffSupport N m, r_{N, m}(n)`. -/
def oddPrefixFirstMoment (N m : ℕ) : ℕ :=
  ∑ n ∈ oddRomanoffSupport N m, romanoffRepCount N m n

/-- Odd-prefix second moment `M_{2, odd}(N, m) = ∑ n ∈ oddRomanoffSupport N m, r_{N, m}(n) ^ 2`. -/
def oddPrefixSecondMoment (N m : ℕ) : ℕ :=
  ∑ n ∈ oddRomanoffSupport N m, (romanoffRepCount N m n) ^ 2

/-- Odd-prefix representation pairs `(p, s) ∈ primesBelow N ×ˢ twoPowSums m` with `p + s` odd and `< N`. -/
def oddPrefixPairs (N m : ℕ) : Finset (ℕ × ℕ) :=
  ((primesBelow N) ×ˢ (twoPowSums m)).filter (fun x => (x.1 + x.2) % 2 = 1 ∧ x.1 + x.2 < N)

/-- Support size of `oddRomanoffSupport N m` is bounded above by `oddPrefixFirstMoment N m`. -/
theorem card_oddRomanoffSupport_le_oddPrefixFirstMoment (N m : ℕ) :
    (oddRomanoffSupport N m).card ≤ oddPrefixFirstMoment N m := by
  unfold oddPrefixFirstMoment
  calc
    (oddRomanoffSupport N m).card = ∑ _n ∈ oddRomanoffSupport N m, 1 := by simp
    _ ≤ ∑ n ∈ oddRomanoffSupport N m, romanoffRepCount N m n := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      unfold oddRomanoffSupport at hn
      exact one_le_romanoffRepCount_of_mem_romanoffSumset (Finset.mem_filter.mp hn).1

#print axioms Erdos9.card_oddRomanoffSupport_le_oddPrefixFirstMoment

/-- `oddPrefixFirstMoment N m` is bounded above by `oddPrefixSecondMoment N m`. -/
theorem oddPrefixFirstMoment_le_oddPrefixSecondMoment (N m : ℕ) :
    oddPrefixFirstMoment N m ≤ oddPrefixSecondMoment N m := by
  unfold oddPrefixFirstMoment oddPrefixSecondMoment
  refine Finset.sum_le_sum (fun n _ => ?_)
  nlinarith

#print axioms Erdos9.oddPrefixFirstMoment_le_oddPrefixSecondMoment

/-- `oddPrefixFirstMoment N m` is bounded above by the full box first moment `romanoffFirstMoment N m`. -/
theorem oddPrefixFirstMoment_le_romanoffFirstMoment (N m : ℕ) :
    oddPrefixFirstMoment N m ≤ romanoffFirstMoment N m := by
  unfold oddPrefixFirstMoment romanoffFirstMoment oddRomanoffSupport
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

#print axioms Erdos9.oddPrefixFirstMoment_le_romanoffFirstMoment

/-- `oddPrefixSecondMoment N m` is bounded above by the full box second moment `romanoffSecondMoment N m`. -/
theorem oddPrefixSecondMoment_le_romanoffSecondMoment (N m : ℕ) :
    oddPrefixSecondMoment N m ≤ romanoffSecondMoment N m := by
  unfold oddPrefixSecondMoment romanoffSecondMoment oddRomanoffSupport
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

#print axioms Erdos9.oddPrefixSecondMoment_le_romanoffSecondMoment

/-- Exact fiberwise identity for `oddPrefixFirstMoment N m`: the sum of representation
multiplicities over `oddRomanoffSupport N m` equals `(oddPrefixPairs N m).card`. -/
theorem oddPrefixFirstMoment_eq_card_oddPrefixPairs (N m : ℕ) :
    oddPrefixFirstMoment N m = (oddPrefixPairs N m).card := by
  unfold oddPrefixFirstMoment oddPrefixPairs oddRomanoffSupport romanoffRepCount romanoffRepPairs
  have himg : (romanoffSumset N m).filter (fun n => n % 2 = 1 ∧ n < N) =
      (((primesBelow N) ×ˢ (twoPowSums m)).filter
        (fun x => (x.1 + x.2) % 2 = 1 ∧ x.1 + x.2 < N)).image (fun x => x.1 + x.2) := by
    ext n
    simp only [romanoffSumset, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hmod, hlt⟩
      exact ⟨x, ⟨hx, hmod, hlt⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hmod, hlt⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hmod, hlt⟩
  rw [himg]
  rw [Finset.card_eq_sum_card_image (fun x : ℕ × ℕ => x.1 + x.2)]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter] at hn
  rcases hn with ⟨y, ⟨_, hmod, hlt⟩, rfl⟩
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, heq⟩
    exact ⟨⟨hx, by rw [heq]; exact ⟨hmod, hlt⟩⟩, heq⟩
  · rintro ⟨⟨hx, _⟩, heq⟩
    exact ⟨hx, heq⟩

#print axioms Erdos9.oddPrefixFirstMoment_eq_card_oddPrefixPairs

/-- Every element of `romanoffSumset N m` satisfies `IsPrimePlusTwoPowers`. -/
theorem isPrimePlusTwoPowers_of_mem_romanoffSumset {N m n : ℕ}
    (hn : n ∈ romanoffSumset N m) :
    IsPrimePlusTwoPowers n := by
  unfold romanoffSumset primesBelow at hn
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_range,
    mem_twoPowSums_iff, Prod.exists] at hn
  rcases hn with ⟨p, s, ⟨⟨_, hp⟩, ⟨k, l, _, _, rfl⟩⟩, rfl⟩
  exact ⟨p, k, l, hp, by omega⟩

#print axioms Erdos9.isPrimePlusTwoPowers_of_mem_romanoffSumset

/-- Every element of `oddRomanoffSupport N m` belongs to `OddPrimePlusTwoPowers ∩ Set.Iio N`. -/
theorem mem_oddPrimePlusTwoPowers_Iio_of_mem_oddRomanoffSupport {N m n : ℕ}
    (hn : n ∈ oddRomanoffSupport N m) :
    n ∈ OddPrimePlusTwoPowers ∩ Set.Iio N := by
  unfold oddRomanoffSupport at hn
  simp only [Finset.mem_filter] at hn
  rcases hn with ⟨hrom, hmod, hlt⟩
  refine ⟨⟨Nat.odd_iff.mpr hmod, isPrimePlusTwoPowers_of_mem_romanoffSumset hrom⟩, ?_⟩
  exact Set.mem_Iio.mpr hlt

#print axioms Erdos9.mem_oddPrimePlusTwoPowers_Iio_of_mem_oddRomanoffSupport

/-- Set inclusion `(oddRomanoffSupport N m : Set ℕ) ⊆ OddPrimePlusTwoPowers ∩ Set.Iio N`. -/
theorem coe_oddRomanoffSupport_subset_oddPrimePlusTwoPowers_Iio (N m : ℕ) :
    (oddRomanoffSupport N m : Set ℕ) ⊆ OddPrimePlusTwoPowers ∩ Set.Iio N := by
  intro n hn
  exact mem_oddPrimePlusTwoPowers_Iio_of_mem_oddRomanoffSupport (Finset.mem_coe.mp hn)

#print axioms Erdos9.coe_oddRomanoffSupport_subset_oddPrimePlusTwoPowers_Iio

/-- Cardinality lower bound `(oddRomanoffSupport N m).card ≤ (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard`. -/
theorem card_oddRomanoffSupport_le_ncard_oddPrimePlusTwoPowers_Iio (N m : ℕ) :
    (oddRomanoffSupport N m).card ≤ (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard := by
  have hfin : (OddPrimePlusTwoPowers ∩ Set.Iio N).Finite :=
    (Set.finite_lt_nat N).subset Set.inter_subset_right
  calc
    (oddRomanoffSupport N m).card = (oddRomanoffSupport N m : Set ℕ).ncard :=
      (Set.ncard_coe_finset _).symm
    _ ≤ (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard :=
      Set.ncard_le_ncard (coe_oddRomanoffSupport_subset_oddPrimePlusTwoPowers_Iio N m) hfin

#print axioms Erdos9.card_oddRomanoffSupport_le_ncard_oddPrimePlusTwoPowers_Iio

/-- At the dyadic horizon `N = 2 ^ (m + 1)`, `oddRomanoffSupport (2 ^ (m + 1)) m` coincides
with `OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1))`. -/
theorem coe_oddRomanoffSupport_two_pow_eq (m : ℕ) :
    (oddRomanoffSupport (2 ^ (m + 1)) m : Set ℕ) =
      OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1)) := by
  apply Set.Subset.antisymm
  · exact coe_oddRomanoffSupport_subset_oddPrimePlusTwoPowers_Iio (2 ^ (m + 1)) m
  · rintro n ⟨⟨hodd, hrep⟩, hlt⟩
    rw [Finset.mem_coe]
    unfold oddRomanoffSupport
    rw [Finset.mem_filter]
    have hlt' : n < 2 ^ (m + 1) := Set.mem_Iio.mp hlt
    exact ⟨mem_romanoffSumset_of_isPrimePlusTwoPowers_lt_two_pow hrep hlt',
      Nat.odd_iff.mp hodd, hlt'⟩

#print axioms Erdos9.coe_oddRomanoffSupport_two_pow_eq

/-- Exact cardinality equality at dyadic horizons `N = 2 ^ (m + 1)`:
`(oddRomanoffSupport (2 ^ (m + 1)) m).card = (OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1))).ncard`. -/
theorem card_oddRomanoffSupport_two_pow_eq_ncard (m : ℕ) :
    (oddRomanoffSupport (2 ^ (m + 1)) m).card =
      (OddPrimePlusTwoPowers ∩ Set.Iio (2 ^ (m + 1))).ncard := by
  rw [← Set.ncard_coe_finset, coe_oddRomanoffSupport_two_pow_eq]

#print axioms Erdos9.card_oddRomanoffSupport_two_pow_eq_ncard

/-- Cauchy-Schwarz inequality on `oddRomanoffSupport N m`:
`(oddPrefixFirstMoment N m) ^ 2 ≤ (oddRomanoffSupport N m).card * oddPrefixSecondMoment N m`. -/
theorem oddPrefixFirstMoment_sq_le_card_oddRomanoffSupport_mul_secondMoment (N m : ℕ) :
    (oddPrefixFirstMoment N m) ^ 2 ≤
      (oddRomanoffSupport N m).card * oddPrefixSecondMoment N m := by
  unfold oddPrefixFirstMoment oddPrefixSecondMoment
  exact cauchy_schwarz_finset_sum_sq_le_card_mul_sum_sq
    (oddRomanoffSupport N m) (romanoffRepCount N m)

#print axioms Erdos9.oddPrefixFirstMoment_sq_le_card_oddRomanoffSupport_mul_secondMoment

/-- Cauchy-Schwarz lower bound directly on `(OddPrimePlusTwoPowers ∩ Set.Iio N).ncard`:
`(oddPrefixFirstMoment N m) ^ 2 ≤ (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard * oddPrefixSecondMoment N m`. -/
theorem oddPrefixFirstMoment_sq_le_ncard_oddPrimePlusTwoPowers_mul_secondMoment (N m : ℕ) :
    (oddPrefixFirstMoment N m) ^ 2 ≤
      (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard * oddPrefixSecondMoment N m := by
  calc
    (oddPrefixFirstMoment N m) ^ 2 ≤
        (oddRomanoffSupport N m).card * oddPrefixSecondMoment N m :=
      oddPrefixFirstMoment_sq_le_card_oddRomanoffSupport_mul_secondMoment N m
    _ ≤ (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard * oddPrefixSecondMoment N m :=
      Nat.mul_le_mul_right _ (card_oddRomanoffSupport_le_ncard_oddPrimePlusTwoPowers_Iio N m)

#print axioms Erdos9.oddPrefixFirstMoment_sq_le_ncard_oddPrimePlusTwoPowers_mul_secondMoment

/-- Integer division Cauchy-Schwarz lower bound on `(oddRomanoffSupport N m).card`. -/
theorem card_oddRomanoffSupport_ge_div_secondMoment (N m : ℕ) :
    (oddPrefixFirstMoment N m) ^ 2 / oddPrefixSecondMoment N m ≤ (oddRomanoffSupport N m).card := by
  apply Nat.div_le_of_le_mul
  rw [mul_comm]
  exact oddPrefixFirstMoment_sq_le_card_oddRomanoffSupport_mul_secondMoment N m

#print axioms Erdos9.card_oddRomanoffSupport_ge_div_secondMoment

/-- Integer division Cauchy-Schwarz lower bound on `(OddPrimePlusTwoPowers ∩ Set.Iio N).ncard`. -/
theorem ncard_oddPrimePlusTwoPowers_Iio_ge_div_secondMoment (N m : ℕ) :
    (oddPrefixFirstMoment N m) ^ 2 / oddPrefixSecondMoment N m ≤
      (OddPrimePlusTwoPowers ∩ Set.Iio N).ncard := by
  apply Nat.div_le_of_le_mul
  rw [mul_comm]
  exact oddPrefixFirstMoment_sq_le_ncard_oddPrimePlusTwoPowers_mul_secondMoment N m

#print axioms Erdos9.ncard_oddPrimePlusTwoPowers_Iio_ge_div_secondMoment

/-! ## Section 4: Cauchy-Schwarz Partial-Density Lower Bounds and `Erdos9A` Reductions -/

/-- Universal Cauchy-Schwarz lower bound on `OddPrimePlusTwoPowers.partialDensity Set.univ N`:
`((oddPrefixFirstMoment N m : ℝ) ^ 2) / ((N : ℝ) * (oddPrefixSecondMoment N m : ℝ)) ≤ OddPrimePlusTwoPowers.partialDensity Set.univ N`. -/
theorem partialDensity_oddPrimePlusTwoPowers_ge_cauchy_schwarz (N m : ℕ) :
    ((oddPrefixFirstMoment N m : ℝ) ^ 2) / ((N : ℝ) * (oddPrefixSecondMoment N m : ℝ)) ≤
      OddPrimePlusTwoPowers.partialDensity Set.univ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · unfold Set.partialDensity
    simp
  · rcases Nat.eq_zero_or_pos (oddPrefixSecondMoment N m) with hM2 | hM2
    · rw [hM2]
      simp only [Nat.cast_zero, mul_zero, div_zero]
      unfold Set.partialDensity
      positivity
    · unfold Set.partialDensity
      have hden : ((Set.univ ∩ Set.Iio N).ncard : ℝ) = (N : ℝ) := by
        simp [Set.univ_inter, Set.ncard_Iio]
      rw [Set.inter_univ, hden]
      have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
      have hM2R : (0 : ℝ) < (oddPrefixSecondMoment N m : ℝ) := Nat.cast_pos.mpr hM2
      rw [div_le_div_iff₀ (mul_pos hNR hM2R) hNR]
      have hcs : ((oddPrefixFirstMoment N m : ℝ) ^ 2) ≤
          ((OddPrimePlusTwoPowers ∩ Set.Iio N).ncard : ℝ) * (oddPrefixSecondMoment N m : ℝ) := by
        exact_mod_cast oddPrefixFirstMoment_sq_le_ncard_oddPrimePlusTwoPowers_mul_secondMoment N m
      nlinarith

#print axioms Erdos9.partialDensity_oddPrimePlusTwoPowers_ge_cauchy_schwarz

/-- Any linear second-moment ceiling `c * N * M_{2, odd}(N, m) ≤ M_{1, odd}(N, m) ^ 2` implies
the lower bound `c ≤ OddPrimePlusTwoPowers.partialDensity Set.univ N`. -/
theorem partialDensity_oddPrimePlusTwoPowers_ge_of_secondMoment_ceiling
    {N m : ℕ} {c : ℝ} (hN : 0 < N) (hM2 : 0 < oddPrefixSecondMoment N m)
    (hceil : c * ((N : ℝ) * (oddPrefixSecondMoment N m : ℝ)) ≤ (oddPrefixFirstMoment N m : ℝ) ^ 2) :
    c ≤ OddPrimePlusTwoPowers.partialDensity Set.univ N := by
  have hpos : (0 : ℝ) < (N : ℝ) * (oddPrefixSecondMoment N m : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hM2)
  have hle : c ≤ ((oddPrefixFirstMoment N m : ℝ) ^ 2) / ((N : ℝ) * (oddPrefixSecondMoment N m : ℝ)) :=
    (le_div_iff₀ hpos).mpr hceil
  exact le_trans hle (partialDensity_oddPrimePlusTwoPowers_ge_cauchy_schwarz N m)

#print axioms Erdos9.partialDensity_oddPrimePlusTwoPowers_ge_of_secondMoment_ceiling

/-- Complementary Cauchy-Schwarz upper bound on `Erdos9A.partialDensity Set.univ N` via
partial-density conservation. -/
theorem partialDensity_erdos9A_le_odd_sub_cauchy_schwarz (N m : ℕ) :
    Erdos9A.partialDensity Set.univ N ≤
      ({n : ℕ | Odd n} : Set ℕ).partialDensity Set.univ N -
        ((oddPrefixFirstMoment N m : ℝ) ^ 2) / ((N : ℝ) * (oddPrefixSecondMoment N m : ℝ)) := by
  have hcons := partialDensity_erdos9A_add_oddPrimePlusTwoPowers N
  have hcs := partialDensity_oddPrimePlusTwoPowers_ge_cauchy_schwarz N m
  linarith

#print axioms Erdos9.partialDensity_erdos9A_le_odd_sub_cauchy_schwarz

/-- Under a linear second-moment ceiling `c * (N * M_{2, odd}(N, m)) ≤ M_{1, odd}(N, m) ^ 2`,
`Erdos9A.partialDensity Set.univ N ≤ ({n : ℕ | Odd n}).partialDensity Set.univ N - c`. -/
theorem partialDensity_erdos9A_le_odd_sub_of_secondMoment_ceiling
    {N m : ℕ} {c : ℝ} (hN : 0 < N) (hM2 : 0 < oddPrefixSecondMoment N m)
    (hceil : c * ((N : ℝ) * (oddPrefixSecondMoment N m : ℝ)) ≤ (oddPrefixFirstMoment N m : ℝ) ^ 2) :
    Erdos9A.partialDensity Set.univ N ≤
      ({n : ℕ | Odd n} : Set ℕ).partialDensity Set.univ N - c := by
  have hcons := partialDensity_erdos9A_add_oddPrimePlusTwoPowers N
  have hlb := partialDensity_oddPrimePlusTwoPowers_ge_of_secondMoment_ceiling hN hM2 hceil
  linarith

#print axioms Erdos9.partialDensity_erdos9A_le_odd_sub_of_secondMoment_ceiling

/-- Eventual partial-density lower bounds transfer directly to `OddPrimePlusTwoPowers.lowerDensity`. -/
theorem le_lowerDensity_oddPrimePlusTwoPowers_of_eventually_le {A : Set ℕ} {c : ℝ}
    (hc : ∀ᶠ b : ℕ in Filter.atTop, c ≤ OddPrimePlusTwoPowers.partialDensity A b) :
    c ≤ OddPrimePlusTwoPowers.lowerDensity A := by
  have hbdd_le : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun b : ℕ => OddPrimePlusTwoPowers.partialDensity A b) :=
    ⟨1, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun b =>
      Set.partialDensity_le_one OddPrimePlusTwoPowers A b)⟩
  unfold Set.lowerDensity
  exact Filter.le_liminf_of_le hbdd_le.isCobounded_ge hc

#print axioms Erdos9.le_lowerDensity_oddPrimePlusTwoPowers_of_eventually_le

/-- Cauchy-Schwarz lower-density reduction: if a scale choice `m : ℕ → ℕ` satisfies the eventual
second-moment ratio lower bound `c ≤ M_{1, odd}(N, m N) ^ 2 / (N * M_{2, odd}(N, m N))`,
then `c ≤ OddPrimePlusTwoPowers.lowerDensity`. -/
theorem lowerDensity_oddPrimePlusTwoPowers_ge_of_eventual_cauchy_schwarz
    {c : ℝ} (m : ℕ → ℕ)
    (hmom : ∀ᶠ N : ℕ in Filter.atTop,
      c ≤ ((oddPrefixFirstMoment N (m N) : ℝ) ^ 2) /
        ((N : ℝ) * (oddPrefixSecondMoment N (m N) : ℝ))) :
    c ≤ OddPrimePlusTwoPowers.lowerDensity := by
  apply le_lowerDensity_oddPrimePlusTwoPowers_of_eventually_le
  exact hmom.mono fun N hN =>
    le_trans hN (partialDensity_oddPrimePlusTwoPowers_ge_cauchy_schwarz N (m N))

#print axioms Erdos9.lowerDensity_oddPrimePlusTwoPowers_ge_of_eventual_cauchy_schwarz

/-- Romanoff-type positive lower density for `OddPrimePlusTwoPowers`: any strictly positive
eventual Cauchy-Schwarz second-moment ratio `0 < c ≤ M_{1, odd}(N, m N) ^ 2 / (N * M_{2, odd}(N, m N))`
implies `0 < OddPrimePlusTwoPowers.lowerDensity`. -/
theorem lowerDensity_oddPrimePlusTwoPowers_pos_of_eventual_cauchy_schwarz
    {c : ℝ} (hc : 0 < c) (m : ℕ → ℕ)
    (hmom : ∀ᶠ N : ℕ in Filter.atTop,
      c ≤ ((oddPrefixFirstMoment N (m N) : ℝ) ^ 2) /
        ((N : ℝ) * (oddPrefixSecondMoment N (m N) : ℝ))) :
    0 < OddPrimePlusTwoPowers.lowerDensity :=
  lt_of_lt_of_le hc (lowerDensity_oddPrimePlusTwoPowers_ge_of_eventual_cauchy_schwarz m hmom)

#print axioms Erdos9.lowerDensity_oddPrimePlusTwoPowers_pos_of_eventual_cauchy_schwarz

/-! ## Section 5: Certified Finite-Horizon Pilot Controls (`(N, m) = (8, 2)` and `(16, 3)`) -/

/-- Exact finite-horizon evaluation at `(N, m) = (8, 2)` matching Track B pilot chunk 0:
`M_1 = 24`, `M_2 = 60`, `|romanoffSumset 8 2| = 11`, `M_{1, odd} = 5`, `M_{2, odd} = 13`,
and `|oddRomanoffSupport 8 2| = 2`. -/
theorem pilot_control_N8_m2_moments :
    romanoffFirstMoment 8 2 = 24 ∧
    romanoffSecondMoment 8 2 = 60 ∧
    (romanoffSumset 8 2).card = 11 ∧
    oddPrefixFirstMoment 8 2 = 5 ∧
    oddPrefixSecondMoment 8 2 = 13 ∧
    (oddRomanoffSupport 8 2).card = 2 := by
  decide

#print axioms Erdos9.pilot_control_N8_m2_moments

/-- Exact finite-horizon evaluation at `(N, m) = (16, 3)` matching Track B pilot chunk 0:
`M_1 = 60`, `M_2 = 188`, `|romanoffSumset 16 3| = 23`, `M_{1, odd} = 21`, `M_{2, odd} = 79`,
and `|oddRomanoffSupport 16 3| = 6`. -/
theorem pilot_control_N16_m3_moments :
    romanoffFirstMoment 16 3 = 60 ∧
    romanoffSecondMoment 16 3 = 188 ∧
    (romanoffSumset 16 3).card = 23 ∧
    oddPrefixFirstMoment 16 3 = 21 ∧
    oddPrefixSecondMoment 16 3 = 79 ∧
    (oddRomanoffSupport 16 3).card = 6 := by
  decide

#print axioms Erdos9.pilot_control_N16_m3_moments

end Erdos9
