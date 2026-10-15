module

/-
Copyright 2026 The Formal Conjectures Authors.
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

public import Erdos726Unified435

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Topology Asymptotics
open Nat Filter Finset

namespace Erdos726

/-! ## Section 1: Bounded-Horizon Prime Residue Sets and Small-Prime Tail Support -/

/-- Primes `p ≤ B` whose remainder `n % p` lies in the upper half `(p / 2, p)`. -/
def upperBoundedPrimes (B n : ℕ) : Finset ℕ :=
  (primeRange B).filter (fun p : ℕ ↦ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ))

/-- Primes `p ≤ B` whose remainder `n % p` lies in the lower complement `[0, p / 2]`. -/
def lowerBoundedPrimes (B n : ℕ) : Finset ℕ :=
  (primeRange B).filter (fun p : ℕ ↦ ¬((p : ℝ) / 2 < ((n % p : ℕ) : ℝ)))

/-- Odd primes `p ≤ B` not dividing `n` whose remainder lies in the strict lower half `(0, p / 2)`. -/
def strictLowerOddBoundedPrimes (B n : ℕ) : Finset ℕ :=
  (oddPrimeRange B).filter (fun p : ℕ ↦ ¬(p ∣ n) ∧ ¬((p : ℝ) / 2 < ((n % p : ℕ) : ℝ)))

/-- Odd primes `p ≤ B` dividing `n`. -/
def dividingOddBoundedPrimes (B n : ℕ) : Finset ℕ :=
  (oddPrimeRange B).filter (fun p : ℕ ↦ p ∣ n)

/-- Reciprocal sum over `upperBoundedPrimes B n`. -/
def upperBoundedPrimeSum (B n : ℕ) : ℝ :=
  ∑ p ∈ upperBoundedPrimes B n, (1 : ℝ) / (p : ℝ)

/-- Reciprocal sum over `lowerBoundedPrimes B n`. -/
def lowerBoundedPrimeSum (B n : ℕ) : ℝ :=
  ∑ p ∈ lowerBoundedPrimes B n, (1 : ℝ) / (p : ℝ)

/-- Reciprocal sum over `strictLowerOddBoundedPrimes B n`. -/
def strictLowerOddBoundedSum (B n : ℕ) : ℝ :=
  ∑ p ∈ strictLowerOddBoundedPrimes B n, (1 : ℝ) / (p : ℝ)

/-- Reciprocal sum over `dividingOddBoundedPrimes B n`. -/
def dividingOddBoundedSum (B n : ℕ) : ℝ :=
  ∑ p ∈ dividingOddBoundedPrimes B n, (1 : ℝ) / (p : ℝ)

/-- Reciprocal sum over all odd primes `p ≤ B`. -/
def oddPrimeReciprocalSum (B : ℕ) : ℝ :=
  ∑ p ∈ oddPrimeRange B, (1 : ℝ) / (p : ℝ)

/-- Division threshold symmetry: for `0 < p`, `p ≤ n / (K + 1)` iff `K + 1 ≤ n / p`. -/
theorem prime_le_div_succ_iff_succ_le_div :
    ∀ n K p : ℕ, 0 < p → (p ≤ n / (K + 1) ↔ K + 1 ≤ n / p) := by
  intro n K p hp
  have hK : 0 < K + 1 := Nat.succ_pos K
  rw [Nat.le_div_iff_mul_le hK, Nat.le_div_iff_mul_le hp, mul_comm]

/-- Exact support identification of `upperSmallPrimeTail n K` with `upperBoundedPrimes (n / (K + 1)) n`. -/
theorem upperSmallPrimeTail_eq_upperBoundedPrimes :
    ∀ n K : ℕ,
      upperSmallPrimeTail n K = upperBoundedPrimes (n / (K + 1)) n ∧
        upperSmallPrimeTailSum n K = upperBoundedPrimeSum (n / (K + 1)) n := by
  intro n K
  have hset : upperSmallPrimeTail n K = upperBoundedPrimes (n / (K + 1)) n := by
    ext p
    simp only [upperSmallPrimeTail, upperHalfPrimes, upperBoundedPrimes, primeRange,
      Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_, hp, hup⟩, hdiv⟩
      exact ⟨⟨(prime_le_div_succ_iff_succ_le_div n K p hp.pos).mpr hdiv, hp⟩, hup⟩
    · rintro ⟨⟨hple, hp⟩, hup⟩
      have hdiv := (prime_le_div_succ_iff_succ_le_div n K p hp.pos).mp hple
      have hle_n : p ≤ n := le_trans hple (Nat.div_le_self n (K + 1))
      exact ⟨⟨hle_n, hp, hup⟩, hdiv⟩
  refine ⟨hset, ?_⟩
  unfold upperSmallPrimeTailSum upperBoundedPrimeSum
  rw [hset]

/-- Exact support identification of `lowerSmallPrimeTail n K` with `lowerBoundedPrimes (n / (K + 1)) n`. -/
theorem lowerSmallPrimeTail_eq_lowerBoundedPrimes :
    ∀ n K : ℕ,
      lowerSmallPrimeTail n K = lowerBoundedPrimes (n / (K + 1)) n ∧
        lowerSmallPrimeTailSum n K = lowerBoundedPrimeSum (n / (K + 1)) n := by
  intro n K
  have hset : lowerSmallPrimeTail n K = lowerBoundedPrimes (n / (K + 1)) n := by
    ext p
    simp only [lowerSmallPrimeTail, lowerComplementPrimes, lowerBoundedPrimes, primeRange,
      Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_, hp, hlow⟩, hdiv⟩
      exact ⟨⟨(prime_le_div_succ_iff_succ_le_div n K p hp.pos).mpr hdiv, hp⟩, hlow⟩
    · rintro ⟨⟨hple, hp⟩, hlow⟩
      have hdiv := (prime_le_div_succ_iff_succ_le_div n K p hp.pos).mp hple
      have hle_n : p ≤ n := le_trans hple (Nat.div_le_self n (K + 1))
      exact ⟨⟨hle_n, hp, hlow⟩, hdiv⟩
  refine ⟨hset, ?_⟩
  unfold lowerSmallPrimeTailSum lowerBoundedPrimeSum
  rw [hset]

/-- Partition of `primeRange B` into `upperBoundedPrimes B n` and `lowerBoundedPrimes B n`. -/
theorem disjoint_upperBoundedPrimes_lowerBoundedPrimes :
    ∀ B n : ℕ,
      Disjoint (upperBoundedPrimes B n) (lowerBoundedPrimes B n) ∧
        upperBoundedPrimes B n ∪ lowerBoundedPrimes B n = primeRange B := by
  intro B n
  constructor
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [upperBoundedPrimes, lowerBoundedPrimes, Finset.mem_filter] at hp1 hp2
    exact hp2.2 hp1.2
  · ext p
    simp only [upperBoundedPrimes, lowerBoundedPrimes, Finset.mem_union, Finset.mem_filter]
    tauto

/-- Additive decomposition of `fullPrimeReciprocalSum B` into bounded upper and lower sums. -/
theorem upperBoundedPrimeSum_add_lowerBoundedPrimeSum :
    ∀ B n : ℕ, upperBoundedPrimeSum B n + lowerBoundedPrimeSum B n = fullPrimeReciprocalSum B := by
  intro B n
  have hpart := disjoint_upperBoundedPrimes_lowerBoundedPrimes B n
  unfold upperBoundedPrimeSum lowerBoundedPrimeSum fullPrimeReciprocalSum
  rw [← hpart.2, Finset.sum_union hpart.1]

/-- Sum of `upperSmallPrimeTailSum n K` and `lowerSmallPrimeTailSum n K` equals `fullPrimeReciprocalSum (n / (K + 1))`. -/
theorem upperSmallPrimeTailSum_add_lowerSmallPrimeTailSum :
    ∀ n K : ℕ,
      upperSmallPrimeTailSum n K + lowerSmallPrimeTailSum n K =
        fullPrimeReciprocalSum (n / (K + 1)) := by
  intro n K
  rw [(upperSmallPrimeTail_eq_upperBoundedPrimes n K).2,
    (lowerSmallPrimeTail_eq_lowerBoundedPrimes n K).2,
    upperBoundedPrimeSum_add_lowerBoundedPrimeSum]

/-- Unconditional triangle bound on the small-prime tail discrepancy in terms of `fullPrimeReciprocalSum (n / (K + 1))`. -/
theorem abs_smallPrimeTail_discrepancy_le_fullPrimeReciprocalSum :
    ∀ n K : ℕ,
      |upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K| ≤
        fullPrimeReciprocalSum (n / (K + 1)) := by
  intro n K
  have hu : 0 ≤ upperSmallPrimeTailSum n K := by
    unfold upperSmallPrimeTailSum
    apply Finset.sum_nonneg
    intro p _; positivity
  have hl : 0 ≤ lowerSmallPrimeTailSum n K := by
    unfold lowerSmallPrimeTailSum
    apply Finset.sum_nonneg
    intro p _; positivity
  have hadd := upperSmallPrimeTailSum_add_lowerSmallPrimeTailSum n K
  rw [abs_le]
  constructor <;> linarith

/-! ## Section 2: Modular Period Reflection on Bounded Prime Ranges and Small-Prime Tails -/

/-- Every prime in `upperBoundedPrimes B n` is an odd prime in `oddPrimeRange B`. -/
theorem upperBoundedPrimes_subset_oddPrimeRange :
    ∀ B n : ℕ, upperBoundedPrimes B n ⊆ oddPrimeRange B := by
  intro B n p hp
  simp only [upperBoundedPrimes, primeRange, oddPrimeRange, Finset.mem_filter] at hp ⊢
  have hlt : p < 2 * (n % p) := (inUpperHalfReal_iff_lt_two_mul_mod n p).mp hp.2
  have hne2 : p ≠ 2 := by rintro rfl; omega
  exact ⟨hp.1.1, hp.1.2, hp.1.2.eq_two_or_odd.resolve_left hne2⟩

/-- Characterization of `upperBoundedPrimes B n` as non-dividing upper-half primes in `oddPrimeRange B`. -/
theorem upperBoundedPrimes_eq_oddPrimeRange_filter :
    ∀ B n : ℕ,
      upperBoundedPrimes B n =
        (oddPrimeRange B).filter (fun p : ℕ ↦ ¬(p ∣ n) ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)) := by
  intro B n
  ext p
  constructor
  · intro hp
    have hodd := upperBoundedPrimes_subset_oddPrimeRange B n hp
    simp only [upperBoundedPrimes, Finset.mem_filter] at hp ⊢
    have hlt : p < 2 * (n % p) := (inUpperHalfReal_iff_lt_two_mul_mod n p).mp hp.2
    have hndvd : ¬(p ∣ n) := by
      intro hdvd
      have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
      omega
    exact ⟨hodd, hndvd, hp.2⟩
  · intro hp
    simp only [upperBoundedPrimes, oddPrimeRange, primeRange, Finset.mem_filter] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.1⟩, hp.2.2⟩

/-- Three-way disjoint partition of `oddPrimeRange B` into `upperBoundedPrimes B n`,
`strictLowerOddBoundedPrimes B n`, and `dividingOddBoundedPrimes B n`. -/
theorem oddPrimeRange_three_way_partition :
    ∀ B n : ℕ,
      Disjoint (upperBoundedPrimes B n) (strictLowerOddBoundedPrimes B n) ∧
        Disjoint (upperBoundedPrimes B n ∪ strictLowerOddBoundedPrimes B n)
          (dividingOddBoundedPrimes B n) ∧
        upperBoundedPrimes B n ∪ strictLowerOddBoundedPrimes B n ∪
          dividingOddBoundedPrimes B n = oddPrimeRange B := by
  intro B n
  rw [upperBoundedPrimes_eq_oddPrimeRange_filter]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [strictLowerOddBoundedPrimes, Finset.mem_filter] at hp1 hp2
    exact hp2.2.2 hp1.2.2
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [strictLowerOddBoundedPrimes, dividingOddBoundedPrimes,
      Finset.mem_union, Finset.mem_filter] at hp1 hp2
    rcases hp1 with hp1 | hp1
    · exact hp1.2.1 hp2.2
    · exact hp1.2.1 hp2.2
  · ext p
    simp only [strictLowerOddBoundedPrimes, dividingOddBoundedPrimes,
      Finset.mem_union, Finset.mem_filter]
    tauto

/-- Additive decomposition of `oddPrimeReciprocalSum B` into upper, strict-lower, and dividing odd prime sums. -/
theorem oddPrimeReciprocalSum_three_way_decomposition :
    ∀ B n : ℕ,
      upperBoundedPrimeSum B n + strictLowerOddBoundedSum B n + dividingOddBoundedSum B n =
        oddPrimeReciprocalSum B := by
  intro B n
  have hpart := oddPrimeRange_three_way_partition B n
  unfold upperBoundedPrimeSum strictLowerOddBoundedSum dividingOddBoundedSum oddPrimeReciprocalSum
  rw [← hpart.2.2, Finset.sum_union hpart.2.1, Finset.sum_union hpart.1]

/-- For `2 ≤ B`, `lowerBoundedPrimes B n` partitions into `strictLowerOddBoundedPrimes B n`,
`dividingOddBoundedPrimes B n`, and `{2}`. -/
theorem lowerBoundedPrimes_union_of_two_le :
    ∀ B n : ℕ, 2 ≤ B →
      Disjoint (strictLowerOddBoundedPrimes B n) (dividingOddBoundedPrimes B n) ∧
        Disjoint (strictLowerOddBoundedPrimes B n ∪ dividingOddBoundedPrimes B n) ({2} : Finset ℕ) ∧
        strictLowerOddBoundedPrimes B n ∪ dividingOddBoundedPrimes B n ∪ ({2} : Finset ℕ) =
          lowerBoundedPrimes B n := by
  intro B n hB
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [strictLowerOddBoundedPrimes, dividingOddBoundedPrimes, Finset.mem_filter] at hp1 hp2
    exact hp1.2.1 hp2.2
  · rw [Finset.disjoint_singleton_right]
    simp [strictLowerOddBoundedPrimes, dividingOddBoundedPrimes, oddPrimeRange]
  · ext p
    simp only [strictLowerOddBoundedPrimes, dividingOddBoundedPrimes, lowerBoundedPrimes,
      oddPrimeRange, primeRange, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton, Nat.lt_succ_iff]
    constructor
    · rintro ((⟨⟨hle, hp, _⟩, _, hlow⟩ | ⟨⟨hle, hp, _⟩, hdvd⟩) | rfl)
      · exact ⟨⟨hle, hp⟩, hlow⟩
      · refine ⟨⟨hle, hp⟩, ?_⟩
        change ¬inUpperHalfReal n p
        rw [inUpperHalfReal_iff_lt_two_mul_mod, Nat.mod_eq_zero_of_dvd hdvd]
        omega
      · refine ⟨⟨hB, Nat.prime_two⟩, ?_⟩
        change ¬inUpperHalfReal n 2
        rw [inUpperHalfReal_iff_lt_two_mul_mod]
        omega
    · rintro ⟨⟨hle, hp⟩, hlow⟩
      rcases hp.eq_two_or_odd with rfl | hodd
      · right; rfl
      · left
        by_cases hdvd : p ∣ n
        · right; exact ⟨⟨hle, hp, hodd⟩, hdvd⟩
        · left; exact ⟨⟨hle, hp, hodd⟩, hdvd, hlow⟩

/-- For `2 ≤ B`, `lowerBoundedPrimeSum B n = strictLowerOddBoundedSum B n + dividingOddBoundedSum B n + 1 / 2`. -/
theorem lowerBoundedPrimeSum_decomposition_of_two_le :
    ∀ B n : ℕ, 2 ≤ B →
      lowerBoundedPrimeSum B n =
        strictLowerOddBoundedSum B n + dividingOddBoundedSum B n + 1 / 2 := by
  intro B n hB
  have hpart := lowerBoundedPrimes_union_of_two_le B n hB
  unfold lowerBoundedPrimeSum strictLowerOddBoundedSum dividingOddBoundedSum
  rw [← hpart.2.2, Finset.sum_union hpart.2.1, Finset.sum_union hpart.1, Finset.sum_singleton]
  norm_num

/-- Divisibility reflection invariance: for `n ≤ M` and `p ∣ M`, `p ∣ (M - n) ↔ p ∣ n`. -/
theorem dvd_sub_iff_of_dvd_left :
    ∀ M n p : ℕ, n ≤ M → p ∣ M → (p ∣ (M - n) ↔ p ∣ n) := by
  intro M n p hle hdvd
  constructor
  · intro hmn
    have hadd : M - n + n = M := Nat.sub_add_cancel hle
    rw [← hadd] at hdvd
    exact (Nat.dvd_add_right hmn).mp hdvd
  · intro hn
    exact Nat.dvd_sub hdvd hn

/-- Modular period reflection preserves `dividingOddBoundedPrimes B` and `dividingOddBoundedSum B`. -/
theorem dividingOddBoundedPrimes_reflect_eq :
    ∀ B M n : ℕ, n ≤ M → (∀ p ∈ oddPrimeRange B, p ∣ M) →
      dividingOddBoundedPrimes B (M - n) = dividingOddBoundedPrimes B n ∧
        dividingOddBoundedSum B (M - n) = dividingOddBoundedSum B n := by
  intro B M n hle hM
  have hset : dividingOddBoundedPrimes B (M - n) = dividingOddBoundedPrimes B n := by
    ext p
    simp only [dividingOddBoundedPrimes, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hdvd⟩
      exact ⟨hp, (dvd_sub_iff_of_dvd_left M n p hle (hM p hp)).mp hdvd⟩
    · rintro ⟨hp, hdvd⟩
      exact ⟨hp, (dvd_sub_iff_of_dvd_left M n p hle (hM p hp)).mpr hdvd⟩
  refine ⟨hset, ?_⟩
  unfold dividingOddBoundedSum
  rw [hset]

/-- Modular period reflection maps `upperBoundedPrimes B (M - n)` onto `strictLowerOddBoundedPrimes B n`. -/
theorem upperBoundedPrimes_reflect_eq_strictLowerOdd :
    ∀ B M n : ℕ, n ≤ M → (∀ p ∈ oddPrimeRange B, p ∣ M) →
      upperBoundedPrimes B (M - n) = strictLowerOddBoundedPrimes B n ∧
        upperBoundedPrimeSum B (M - n) = strictLowerOddBoundedSum B n := by
  intro B M n hle hM
  have hset : upperBoundedPrimes B (M - n) = strictLowerOddBoundedPrimes B n := by
    rw [upperBoundedPrimes_eq_oddPrimeRange_filter]
    ext p
    simp only [strictLowerOddBoundedPrimes, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hndvd, hup⟩
      have hp_dvd : p ∣ M := hM p hp
      have hndvd_n : ¬(p ∣ n) := mt (dvd_sub_iff_of_dvd_left M n p hle hp_dvd).mpr hndvd
      have hodd : p % 2 = 1 := by
        simp only [oddPrimeRange, Finset.mem_filter] at hp
        exact hp.2.2
      have hnot_up : ¬inUpperHalfReal n p :=
        (odd_inUpperHalfReal_sub_iff_not_inUpperHalfReal M n p hodd hle hp_dvd hndvd_n).mp hup
      exact ⟨hp, hndvd_n, hnot_up⟩
    · rintro ⟨hp, hndvd_n, hnot_up⟩
      have hp_dvd : p ∣ M := hM p hp
      have hndvd_sub : ¬(p ∣ (M - n)) := mt (dvd_sub_iff_of_dvd_left M n p hle hp_dvd).mp hndvd_n
      have hodd : p % 2 = 1 := by
        simp only [oddPrimeRange, Finset.mem_filter] at hp
        exact hp.2.2
      have hup : inUpperHalfReal (M - n) p :=
        (odd_inUpperHalfReal_sub_iff_not_inUpperHalfReal M n p hodd hle hp_dvd hndvd_n).mpr hnot_up
      exact ⟨hp, hndvd_sub, hup⟩
  refine ⟨hset, ?_⟩
  unfold upperBoundedPrimeSum strictLowerOddBoundedSum
  rw [hset]

/-- Modular period reflection maps `strictLowerOddBoundedPrimes B (M - n)` onto `upperBoundedPrimes B n`. -/
theorem strictLowerOddBoundedPrimes_reflect_eq_upper :
    ∀ B M n : ℕ, n ≤ M → (∀ p ∈ oddPrimeRange B, p ∣ M) →
      strictLowerOddBoundedPrimes B (M - n) = upperBoundedPrimes B n ∧
        strictLowerOddBoundedSum B (M - n) = upperBoundedPrimeSum B n := by
  intro B M n hle hM
  have hsub : M - (M - n) = n := Nat.sub_sub_self hle
  have hrefl := upperBoundedPrimes_reflect_eq_strictLowerOdd B M (M - n) (Nat.sub_le M n) hM
  rw [hsub] at hrefl
  exact ⟨hrefl.1.symm, hrefl.2.symm⟩

/-- For `2 ≤ B`, `n ≤ M`, and `M` divisible by all odd primes `p ≤ B`, the bounded prime discrepancy
`upperBoundedPrimeSum B n - lowerBoundedPrimeSum B n` equals the reflection difference
`(upperBoundedPrimeSum B n - upperBoundedPrimeSum B (M - n)) - dividingOddBoundedSum B n - 1 / 2`. -/
theorem bounded_discrepancy_eq_reflect_diff :
    ∀ B M n : ℕ, 2 ≤ B → n ≤ M → (∀ p ∈ oddPrimeRange B, p ∣ M) →
      upperBoundedPrimeSum B n - lowerBoundedPrimeSum B n =
        (upperBoundedPrimeSum B n - upperBoundedPrimeSum B (M - n)) -
          dividingOddBoundedSum B n - 1 / 2 := by
  intro B M n hB hle hM
  rw [lowerBoundedPrimeSum_decomposition_of_two_le B n hB,
    ← (upperBoundedPrimes_reflect_eq_strictLowerOdd B M n hle hM).2]
  ring

/-- Reflection anti-symmetry identity: summing the bounded prime discrepancy at `n` and at `M - n`
cancels all non-dividing odd primes and equals `-2 * dividingOddBoundedSum B n - 1`. -/
theorem bounded_discrepancy_add_reflect_eq :
    ∀ B M n : ℕ, 2 ≤ B → n ≤ M → (∀ p ∈ oddPrimeRange B, p ∣ M) →
      (upperBoundedPrimeSum B n - lowerBoundedPrimeSum B n) +
        (upperBoundedPrimeSum B (M - n) - lowerBoundedPrimeSum B (M - n)) =
        -2 * dividingOddBoundedSum B n - 1 := by
  intro B M n hB hle hM
  have h1 := bounded_discrepancy_eq_reflect_diff B M n hB hle hM
  have h2 := lowerBoundedPrimeSum_decomposition_of_two_le B (M - n) hB
  have h3 := (strictLowerOddBoundedPrimes_reflect_eq_upper B M n hle hM).2
  have h4 := (dividingOddBoundedPrimes_reflect_eq B M n hle hM).2
  linarith

/-- Modular reflection bound on the small-prime tail discrepancy
`|upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K|` for `2 ≤ n / (K + 1)`. -/
theorem abs_smallPrimeTail_discrepancy_le_of_modular_reflection :
    ∀ n K M : ℕ, 2 ≤ n / (K + 1) → n ≤ M → (∀ p ∈ oddPrimeRange (n / (K + 1)), p ∣ M) →
      |upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K| ≤
        |upperBoundedPrimeSum (n / (K + 1)) n - upperBoundedPrimeSum (n / (K + 1)) (M - n)| +
          dividingOddBoundedSum (n / (K + 1)) n + 1 / 2 := by
  intro n K M hB hle hM
  rw [(upperSmallPrimeTail_eq_upperBoundedPrimes n K).2,
    (lowerSmallPrimeTail_eq_lowerBoundedPrimes n K).2,
    bounded_discrepancy_eq_reflect_diff (n / (K + 1)) M n hB hle hM]
  have hdiv_nonneg : 0 ≤ dividingOddBoundedSum (n / (K + 1)) n := by
    unfold dividingOddBoundedSum
    apply Finset.sum_nonneg
    intro p _; positivity
  have hrew :
      upperBoundedPrimeSum (n / (K + 1)) n - upperBoundedPrimeSum (n / (K + 1)) (M - n) -
        dividingOddBoundedSum (n / (K + 1)) n - 1 / 2 =
      (upperBoundedPrimeSum (n / (K + 1)) n - upperBoundedPrimeSum (n / (K + 1)) (M - n)) +
        (-(dividingOddBoundedSum (n / (K + 1)) n + 1 / 2)) := by ring
  rw [hrew]
  have htri := abs_add_le
    (upperBoundedPrimeSum (n / (K + 1)) n - upperBoundedPrimeSum (n / (K + 1)) (M - n))
    (-(dividingOddBoundedSum (n / (K + 1)) n + 1 / 2))
  have habs :
      |-(dividingOddBoundedSum (n / (K + 1)) n + 1 / 2)| =
        dividingOddBoundedSum (n / (K + 1)) n + 1 / 2 := by
    rw [abs_neg, abs_of_nonneg (by linarith)]
  linarith

/-! ## Section 3: Prime-Counting Representations of `U_k(n)`, `L_k(n)`, and `Q_k(n)` -/

/-- The prime-counting function `π(m) = (primeRange m).card`. -/
def primeCount (m : ℕ) : ℕ :=
  (primeRange m).card

/-- Prime-count discrepancy `|U_k(n)| - |L_k(n)|` on the `k`-th harmonic quotient window. -/
def windowCountDiscrepancy (n k : ℕ) : ℝ :=
  ((upperQuotientPrimes n k).card : ℝ) - ((lowerQuotientPrimes n k).card : ℝ)

/-- Midpoint-weighted prime-count approximation `((2k + 1) / (2n)) (|U_k(n)| - |L_k(n)|)`. -/
def midpointWindowApprox (n k : ℕ) : ℝ :=
  ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) * windowCountDiscrepancy n k

/-- Monotonicity of `primeRange` and `primeCount`. -/
theorem primeRange_mono :
    ∀ a b : ℕ, a ≤ b → primeRange a ⊆ primeRange b ∧ primeCount a ≤ primeCount b := by
  intro a b hab
  have hsub : primeRange a ⊆ primeRange b := by
    intro p hp
    simp only [primeRange, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hp ⊢
    exact ⟨le_trans hp.1 hab, hp.2⟩
  exact ⟨hsub, Finset.card_le_card hsub⟩

/-- For every `n`, `primeCount n ≤ n`. -/
theorem primeCount_le_self :
    ∀ n : ℕ, primeCount n ≤ n := by
  intro n
  unfold primeCount
  rw [primeRange_eq_Ioc_filter_prime]
  calc ((Finset.Ioc 0 n).filter Nat.Prime).card
    _ ≤ (Finset.Ioc 0 n).card := Finset.card_filter_le _ _
    _ = n := Nat.card_Ioc 0 n

/-- Additivity of cardinalities across the `k`-th quotient fiber `Q_k(n) = U_k(n) ∪ L_k(n)`. -/
theorem quotientPrimeFiber_card_eq_add :
    ∀ n k : ℕ,
      (quotientPrimeFiber n k).card =
        (upperQuotientPrimes n k).card + (lowerQuotientPrimes n k).card := by
  intro n k
  have hpart := disjoint_upperQuotientPrimes_lowerQuotientPrimes n k
  rw [← hpart.2, Finset.card_union_of_disjoint hpart.1]

/-- Pairwise disjointness of `quotientPrimeFiber n k` across `k`. -/
theorem pairwiseDisjoint_quotientPrimeFiber :
    ∀ n : ℕ, ∀ s : Set ℕ, s.PairwiseDisjoint (quotientPrimeFiber n) := by
  intro n s k₁ _ k₂ _ hne
  change Disjoint (quotientPrimeFiber n k₁) (quotientPrimeFiber n k₂)
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [quotientPrimeFiber, Finset.mem_filter] at hp1 hp2
  exact hne (hp1.2.symm.trans hp2.2)

/-- Cutoff partition of `primeRange n` into `primeRange (n / (K + 1))` and the disjoint union
of `quotientPrimeFiber n k` over `k ∈ Icc 1 K`. -/
theorem primeRange_cutoff_partition :
    ∀ n K : ℕ,
      Disjoint (primeRange (n / (K + 1))) ((Finset.Icc 1 K).biUnion (quotientPrimeFiber n)) ∧
        primeRange (n / (K + 1)) ∪ (Finset.Icc 1 K).biUnion (quotientPrimeFiber n) =
          primeRange n := by
  intro n K
  constructor
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [primeRange, quotientPrimeFiber, Finset.mem_filter, Finset.mem_range,
      Finset.mem_biUnion, Finset.mem_Icc, Nat.lt_succ_iff] at hp1 hp2
    rcases hp2 with ⟨k, ⟨_, hkK⟩, _, hdiv⟩
    have hge := (prime_le_div_succ_iff_succ_le_div n K p hp1.2.pos).mp hp1.1
    omega
  · ext p
    simp only [primeRange, quotientPrimeFiber, Finset.mem_union, Finset.mem_filter,
      Finset.mem_range, Finset.mem_biUnion, Finset.mem_Icc, Nat.lt_succ_iff]
    constructor
    · rintro (⟨hple, hp⟩ | ⟨k, _, ⟨hple, hp⟩, _⟩)
      · exact ⟨le_trans hple (Nat.div_le_self n (K + 1)), hp⟩
      · exact ⟨hple, hp⟩
    · rintro ⟨hple, hp⟩
      by_cases hge : K + 1 ≤ n / p
      · left
        exact ⟨(prime_le_div_succ_iff_succ_le_div n K p hp.pos).mpr hge, hp⟩
      · right
        have hq_pos : 1 ≤ n / p := Nat.div_pos hple hp.pos
        exact ⟨n / p, ⟨hq_pos, by omega⟩, ⟨hple, hp⟩, rfl⟩

/-- Telescoping prime-count identity across quotient fibers `k ∈ Icc 1 K`. -/
theorem sum_quotientPrimeFiber_card_eq_primeCount_sub :
    ∀ n K : ℕ,
      ∑ k ∈ Finset.Icc 1 K, (quotientPrimeFiber n k).card =
        primeCount n - primeCount (n / (K + 1)) := by
  intro n K
  have hpart := primeRange_cutoff_partition n K
  have hcard :
      (primeRange (n / (K + 1))).card +
        ∑ k ∈ Finset.Icc 1 K, (quotientPrimeFiber n k).card =
        (primeRange n).card := by
    rw [← Finset.card_biUnion (pairwiseDisjoint_quotientPrimeFiber n _),
      ← Finset.card_union_of_disjoint hpart.1, hpart.2]
  unfold primeCount
  omega

/-- The total number of primes across all quotient fibers `k ∈ Icc 1 K` is at most `primeCount n`. -/
theorem sum_quotientPrimeFiber_card_le_primeCount :
    ∀ n K : ℕ, ∑ k ∈ Finset.Icc 1 K, (quotientPrimeFiber n k).card ≤ primeCount n := by
  intro n K
  rw [sum_quotientPrimeFiber_card_eq_primeCount_sub]
  exact Nat.sub_le _ _

/-- Set-difference representation of `upperQuotientPrimes n k` via `primeRange`. -/
theorem upperQuotientPrimes_eq_sdiff_primeRange :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      upperQuotientPrimes n k =
        primeRange ((2 * n - 1) / (2 * k + 1)) \ primeRange (n / (k + 1)) := by
  intro n k hn hk
  have hk1 : 0 < k + 1 := by omega
  have h2k1 : 0 < 2 * k + 1 := by omega
  ext p
  have hcomm1 : p * (k + 1) = (k + 1) * p := Nat.mul_comm _ _
  have hcomm2 : p * (2 * k + 1) = (2 * k + 1) * p := Nat.mul_comm _ _
  simp only [upperQuotientPrimes, primeRange, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨_, hp⟩, hlow, hhigh⟩
    have hp_le : p ≤ (2 * n - 1) / (2 * k + 1) := by
      rw [Nat.le_div_iff_mul_le h2k1, hcomm2]
      omega
    have hp_gt : ¬(p ≤ n / (k + 1) ∧ p.Prime) := by
      rintro ⟨hple, _⟩
      have hmul := (Nat.le_div_iff_mul_le hk1).mp hple
      rw [hcomm1] at hmul
      omega
    exact ⟨⟨hp_le, hp⟩, hp_gt⟩
  · rintro ⟨⟨hp_le, hp⟩, hp_gt⟩
    have hmul_high : p * (2 * k + 1) ≤ 2 * n - 1 :=
      (Nat.le_div_iff_mul_le h2k1).mp hp_le
    rw [hcomm2] at hmul_high
    have hnot_le : ¬(p ≤ n / (k + 1)) := fun h => hp_gt ⟨h, hp⟩
    have hgt : n / (k + 1) < p := Nat.lt_of_not_ge hnot_le
    have hmul_low : n < p * (k + 1) := (Nat.div_lt_iff_lt_mul hk1).mp hgt
    rw [hcomm1] at hmul_low
    have h3p : 3 * p ≤ (2 * k + 1) * p := Nat.mul_le_mul_right p (by omega)
    exact ⟨⟨by omega, hp⟩, hmul_low, by omega⟩

/-- Exact prime-counting formula for `|U_k(n)|`:
`(upperQuotientPrimes n k).card = primeCount ((2 * n - 1) / (2 * k + 1)) - primeCount (n / (k + 1))`. -/
theorem upperQuotientPrimes_card_eq_primeCount_sub :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (upperQuotientPrimes n k).card =
        primeCount ((2 * n - 1) / (2 * k + 1)) - primeCount (n / (k + 1)) := by
  intro n k hn hk
  have hcut_le : n / (k + 1) ≤ (2 * n - 1) / (2 * k + 1) := by
    rcases Nat.eq_zero_or_pos (n / (k + 1)) with hzero | hpos
    · rw [hzero]; exact Nat.zero_le _
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * k + 1)]
      have hmul : (n / (k + 1)) * (k + 1) ≤ n := Nat.div_mul_le_self n (k + 1)
      have hstep : (n / (k + 1)) * (2 * k + 1) + 1 ≤ 2 * ((n / (k + 1)) * (k + 1)) := by nlinarith
      omega
  have hsub := (primeRange_mono _ _ hcut_le).1
  rw [upperQuotientPrimes_eq_sdiff_primeRange n k hn hk, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsub]
  rfl

/-- Set-difference representation of `lowerQuotientPrimes n k` via `primeRange`. -/
theorem lowerQuotientPrimes_eq_sdiff_primeRange :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      lowerQuotientPrimes n k =
        primeRange (n / k) \ primeRange ((2 * n - 1) / (2 * k + 1)) := by
  intro n k hn hk
  have hk_pos : 0 < k := by omega
  have h2k1 : 0 < 2 * k + 1 := by omega
  ext p
  have hcommk : p * k = k * p := Nat.mul_comm _ _
  have hcomm2 : p * (2 * k + 1) = (2 * k + 1) * p := Nat.mul_comm _ _
  simp only [lowerQuotientPrimes, primeRange, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨_, hp⟩, hlow, hhigh⟩
    have hp_le : p ≤ n / k := (Nat.le_div_iff_mul_le hk_pos).mpr (by linarith)
    have hp_gt : ¬(p ≤ (2 * n - 1) / (2 * k + 1) ∧ p.Prime) := by
      rintro ⟨hple, _⟩
      have hmul := (Nat.le_div_iff_mul_le h2k1).mp hple
      rw [hcomm2] at hmul
      omega
    exact ⟨⟨hp_le, hp⟩, hp_gt⟩
  · rintro ⟨⟨hp_le, hp⟩, hp_gt⟩
    have hmul_low : p * k ≤ n := (Nat.le_div_iff_mul_le hk_pos).mp hp_le
    rw [hcommk] at hmul_low
    have hnot_le : ¬(p ≤ (2 * n - 1) / (2 * k + 1)) := fun h => hp_gt ⟨h, hp⟩
    have hgt : (2 * n - 1) / (2 * k + 1) < p := Nat.lt_of_not_ge hnot_le
    have hmul_high : 2 * n - 1 < p * (2 * k + 1) := (Nat.div_lt_iff_lt_mul h2k1).mp hgt
    rw [hcomm2] at hmul_high
    have hp_le_n : p ≤ n := le_trans hp_le (Nat.div_le_self n k)
    exact ⟨⟨hp_le_n, hp⟩, hmul_low, by omega⟩

/-- Exact prime-counting formula for `|L_k(n)|`:
`(lowerQuotientPrimes n k).card = primeCount (n / k) - primeCount ((2 * n - 1) / (2 * k + 1))`. -/
theorem lowerQuotientPrimes_card_eq_primeCount_sub :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (lowerQuotientPrimes n k).card =
        primeCount (n / k) - primeCount ((2 * n - 1) / (2 * k + 1)) := by
  intro n k hn hk
  have hcut_le : (2 * n - 1) / (2 * k + 1) ≤ n / k := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < k)]
    have hmul : ((2 * n - 1) / (2 * k + 1)) * (2 * k + 1) ≤ 2 * n - 1 :=
      Nat.div_mul_le_self (2 * n - 1) (2 * k + 1)
    have hle2n : ((2 * n - 1) / (2 * k + 1)) * (2 * k + 1) ≤ 2 * n :=
      le_trans hmul (Nat.sub_le (2 * n) 1)
    nlinarith
  have hsub := (primeRange_mono _ _ hcut_le).1
  rw [lowerQuotientPrimes_eq_sdiff_primeRange n k hn hk, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsub]
  rfl

/-! ## Section 4: Midpoint-Quadrature Defect Bounds and Combined Asymptotic Discrepancy -/

/-- Nonnegativity and upper bound on the midpoint-quadrature defect for the `k`-th quotient window:
`0 ≤ (u_k(n) - ℓ_k(n)) - midpointWindowApprox n k ≤ |Q_k(n)| / (2n)`. -/
theorem window_midpoint_quadrature_defect_bounds :
    ∀ n k : ℕ, 0 < n →
      0 ≤ (upperQuotientSum n k - lowerQuotientSum n k) - midpointWindowApprox n k ∧
        (upperQuotientSum n k - lowerQuotientSum n k) - midpointWindowApprox n k ≤
          ((quotientPrimeFiber n k).card : ℝ) / (2 * (n : ℝ)) := by
  intro n k hn
  have hsand := quotient_window_discrepancy_sandwich n k hn
  have hcard :
      ((quotientPrimeFiber n k).card : ℝ) =
        ((upperQuotientPrimes n k).card : ℝ) + ((lowerQuotientPrimes n k).card : ℝ) := by
    exact_mod_cast quotientPrimeFiber_card_eq_add n k
  unfold midpointWindowApprox windowCountDiscrepancy
  have halg :
      (((k : ℝ) + 1) / (n : ℝ)) * ((upperQuotientPrimes n k).card : ℝ) -
        ((k : ℝ) / (n : ℝ)) * ((lowerQuotientPrimes n k).card : ℝ) -
        ((2 * (k : ℝ) + 1) / (2 * (n : ℝ))) *
          (((upperQuotientPrimes n k).card : ℝ) - ((lowerQuotientPrimes n k).card : ℝ)) =
      (((upperQuotientPrimes n k).card : ℝ) + ((lowerQuotientPrimes n k).card : ℝ)) /
        (2 * (n : ℝ)) := by
    ring
  rw [hcard]
  constructor <;> linarith

/-- Pointwise triangle bound on `|upperQuotientSum n k - lowerQuotientSum n k|` via
`|midpointWindowApprox n k| + |Q_k(n)| / (2n)`. -/
theorem abs_window_discrepancy_le_midpoint_add_fiber :
    ∀ n k : ℕ, 0 < n →
      |upperQuotientSum n k - lowerQuotientSum n k| ≤
        |midpointWindowApprox n k| + ((quotientPrimeFiber n k).card : ℝ) / (2 * (n : ℝ)) := by
  intro n k hn
  have hdef := window_midpoint_quadrature_defect_bounds n k hn
  rw [abs_le]
  have hmid := le_abs_self (midpointWindowApprox n k)
  have hmid_neg := neg_le_abs (midpointWindowApprox n k)
  constructor <;> linarith

/-- Cumulative midpoint-quadrature defect bounds across `k ∈ Icc 1 K`:
`0 ≤ ∑ (u_k - ℓ_k) - ∑ midpointWindowApprox ≤ (primeCount n - primeCount (n / (K + 1))) / (2n)`. -/
theorem sum_window_midpoint_quadrature_defect_bounds :
    ∀ n K : ℕ, 0 < n →
      0 ≤ (∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k)) -
            (∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k) ∧
        (∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k)) -
            (∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k) ≤
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by
  intro n K hn
  rw [← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro k _
    exact (window_midpoint_quadrature_defect_bounds n k hn).1
  · have hle :
        ∑ k ∈ Finset.Icc 1 K,
          ((upperQuotientSum n k - lowerQuotientSum n k) - midpointWindowApprox n k) ≤
        ∑ k ∈ Finset.Icc 1 K, (((quotientPrimeFiber n k).card : ℝ) / (2 * (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro k _
      exact (window_midpoint_quadrature_defect_bounds n k hn).2
    have hsum_card :
        ∑ k ∈ Finset.Icc 1 K, (((quotientPrimeFiber n k).card : ℝ) / (2 * (n : ℝ))) =
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by
      rw [← Finset.sum_div, ← Nat.cast_sum, sum_quotientPrimeFiber_card_eq_primeCount_sub]
    linarith

/-- Uniform bound on the cumulative midpoint-quadrature defect by `primeCount n / (2n) ≤ 1 / 2`. -/
theorem sum_window_midpoint_quadrature_defect_le_half :
    ∀ n K : ℕ, 0 < n →
      (∑ k ∈ Finset.Icc 1 K, (upperQuotientSum n k - lowerQuotientSum n k)) -
          (∑ k ∈ Finset.Icc 1 K, midpointWindowApprox n k) ≤
        (primeCount n : ℝ) / (2 * (n : ℝ)) ∧
      (primeCount n : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
  intro n K hn
  have hdef := (sum_window_midpoint_quadrature_defect_bounds n K hn).2
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hsub_le : ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) ≤ (primeCount n : ℝ) := by
    exact_mod_cast Nat.sub_le (primeCount n) (primeCount (n / (K + 1)))
  have hpi_le : (primeCount n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast primeCount_le_self n
  have hdiv1 :
      ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) ≤
        (primeCount n : ℝ) / (2 * (n : ℝ)) := by
    exact div_le_div_of_nonneg_right hsub_le (le_of_lt h2n)
  have hdiv2 : (primeCount n : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ h2n (by norm_num : (0 : ℝ) < 2)]
    linarith
  exact ⟨le_trans hdef hdiv1, hdiv2⟩

/-- Cumulative triangle bound on `∑_{k ∈ Icc 1 K} |u_k(n) - ℓ_k(n)|` in terms of
`∑_{k ∈ Icc 1 K} |midpointWindowApprox n k|` and `(primeCount n - primeCount (n / (K + 1))) / (2n)`. -/
theorem sum_abs_window_discrepancy_le_sum_abs_midpoint_add_primeCount :
    ∀ n K : ℕ, 0 < n →
      ∑ k ∈ Finset.Icc 1 K, |upperQuotientSum n k - lowerQuotientSum n k| ≤
        (∑ k ∈ Finset.Icc 1 K, |midpointWindowApprox n k|) +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by
  intro n K hn
  have hle :
      ∑ k ∈ Finset.Icc 1 K, |upperQuotientSum n k - lowerQuotientSum n k| ≤
        ∑ k ∈ Finset.Icc 1 K,
          (|midpointWindowApprox n k| + ((quotientPrimeFiber n k).card : ℝ) / (2 * (n : ℝ))) := by
    apply Finset.sum_le_sum
    intro k _
    exact abs_window_discrepancy_le_midpoint_add_fiber n k hn
  rw [Finset.sum_add_distrib] at hle
  have hsum_card :
      ∑ k ∈ Finset.Icc 1 K, (((quotientPrimeFiber n k).card : ℝ) / (2 * (n : ℝ))) =
        ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) := by
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_quotientPrimeFiber_card_eq_primeCount_sub]
  linarith

/-- Combined discrepancy bound for `|upperHalfPrimeSum n - log(log n) / 2|` in terms of the
small-prime tail discrepancy, the midpoint prime-count discrepancy sum over `1 ≤ k ≤ K`,
the prime-counting quadrature defect, and the Mertens remainder. -/
theorem abs_upperHalfPrimeSum_sub_half_mertens_le_tail_and_primeCount :
    ∀ n K : ℕ, 0 < n →
      |upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2| ≤
        (|upperSmallPrimeTailSum n K - lowerSmallPrimeTailSum n K| +
          (∑ k ∈ Finset.Icc 1 K, |midpointWindowApprox n k|) +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) +
          |Mertens.M + Mertens.E₂p (n : ℝ)|) / 2 := by
  intro n K hn
  have hcut := abs_upperHalfPrimeSum_sub_half_mertens_le_cutoff n K
  have hwin := sum_abs_window_discrepancy_le_sum_abs_midpoint_add_primeCount n K hn
  linarith

/-- Master asymptotic discrepancy bound combining modular period reflection on the small-prime
tail `p ≤ n / (K + 1)` with the prime-counting midpoint-quadrature bounds on `U_k(n)` and `L_k(n)`
across `1 ≤ k ≤ K`. -/
theorem abs_upperHalfPrimeSum_sub_half_mertens_le_reflection_and_primeCount :
    ∀ n K M : ℕ, 0 < n → 2 ≤ n / (K + 1) → n ≤ M →
      (∀ p ∈ oddPrimeRange (n / (K + 1)), p ∣ M) →
      |upperHalfPrimeSum n - Real.log (Real.log (n : ℝ)) / 2| ≤
        (|upperBoundedPrimeSum (n / (K + 1)) n - upperBoundedPrimeSum (n / (K + 1)) (M - n)| +
          dividingOddBoundedSum (n / (K + 1)) n + 1 / 2 +
          (∑ k ∈ Finset.Icc 1 K, |midpointWindowApprox n k|) +
          ((primeCount n - primeCount (n / (K + 1)) : ℕ) : ℝ) / (2 * (n : ℝ)) +
          |Mertens.M + Mertens.E₂p (n : ℝ)|) / 2 := by
  intro n K M hn hB hle hM
  have hbase := abs_upperHalfPrimeSum_sub_half_mertens_le_tail_and_primeCount n K hn
  have hrefl := abs_smallPrimeTail_discrepancy_le_of_modular_reflection n K M hB hle hM
  linarith

/-! ## Section 5: Positive and Negative Falsifying Controls -/

/-- Positive control at `B = 5`, `n = 4`: `dividingOddBoundedPrimes 5 4 = ∅` and
`dividingOddBoundedSum 5 4 = 0`, and every odd prime `p ≤ 5` divides the odd primorial `M = 15`. -/
theorem positive_control_oddPrimeRange_five_four :
    dividingOddBoundedPrimes 5 4 = ∅ ∧
      dividingOddBoundedSum 5 4 = 0 ∧
      ∀ p ∈ oddPrimeRange 5, p ∣ 15 := by
  have hemp : dividingOddBoundedPrimes 5 4 = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false, dividingOddBoundedPrimes, oddPrimeRange,
      Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    rintro ⟨⟨hle, hp, hodd⟩, hdvd⟩
    have hp2 : 2 ≤ p := hp.two_le
    interval_cases p <;> omega
  refine ⟨hemp, ?_, ?_⟩
  · unfold dividingOddBoundedSum
    rw [hemp, Finset.sum_empty]
  · intro p hp
    simp only [oddPrimeRange, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hp
    rcases hp with ⟨hle, hprime, hodd⟩
    have hp2 : 2 ≤ p := hprime.two_le
    interval_cases p <;> omega

/-- Negative control at `B = 5`, `M = 15`, `n = 4`: the sum of the bounded tail discrepancies at
`n = 4` and its modular reflection `M - n = 11` equals `-1` (and does not vanish) because `p = 2`
contributes `-1 / 2` to both `n` and `M - n`. -/
theorem negative_control_tail_reflection_sum_fifteen_four :
    (upperBoundedPrimeSum 5 4 - lowerBoundedPrimeSum 5 4) +
        (upperBoundedPrimeSum 5 11 - lowerBoundedPrimeSum 5 11) = -1 ∧
      (upperBoundedPrimeSum 5 4 - lowerBoundedPrimeSum 5 4) +
        (upperBoundedPrimeSum 5 11 - lowerBoundedPrimeSum 5 11) ≠ 0 := by
  have hctrl := positive_control_oddPrimeRange_five_four
  have hrefl := bounded_discrepancy_add_reflect_eq 5 15 4 (by decide) (by decide) hctrl.2.2
  rw [show 15 - 4 = 11 by rfl, hctrl.2.1] at hrefl
  constructor <;> linarith


end Erdos726

end
