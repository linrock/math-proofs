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

public import Erdos423Unified435

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open Finset BigOperators Filter Asymptotics

namespace Erdos423

/-!
# Eventual-Stabilization Obstruction, Odd-Factor Two-Power Exclusion, and Bounded-Prefix Interval Bounds for Erdős Problem #423

This module develops the eventual-stabilization obstruction for Hofstadter sequences. It proves
linear-shift block-sum identities, excludes powers of two as long linear-block sums, and derives
strict excess growth across power-of-two block sums. It then forces a prefix-crossing representation
under an assumed linear tail, proves that bounded nondecreasing excess stabilizes, and reduces
unboundedness and infinitude of the omitted complement to non-stabilization.
-/

/-- Universal linear-shift block-sum identity: for all `i ≤ j` and `C : ℕ`,
`2 * ∑ l ∈ Finset.Icc i j, (l + C) = (j - i + 1) * (2 * i + 2 * C + (j - i))`. -/
theorem two_mul_sum_Icc_add_const :
    ∀ (i j C : ℕ), i ≤ j →
      2 * ∑ l ∈ Finset.Icc i j, (l + C) = (j - i + 1) * (2 * i + 2 * C + (j - i)) := by
  intro i j C hij
  induction j, hij using Nat.le_induction with
  | base =>
    simp
    ring
  | succ k hik ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.mul_add, ih]
    set d := k - i
    have hk : k + 1 - i = d + 1 := by omega
    have hk2 : 2 * (k + 1 + C) = 2 * i + 2 * C + 2 * d + 2 := by omega
    rw [hk, hk2]
    ring

/-- Unshifted consecutive-integer block-sum identity (`C = 0`): for `i ≤ j`,
`2 * ∑ l ∈ Finset.Icc i j, l = (j - i + 1) * (i + j)`. -/
theorem two_mul_sum_Icc_id :
    ∀ (i j : ℕ), i ≤ j →
      2 * ∑ l ∈ Finset.Icc i j, l = (j - i + 1) * (i + j) := by
  intro i j hij
  have h := two_mul_sum_Icc_add_const i j 0 hij
  simp only [add_zero, mul_zero] at h
  have hij_add : 2 * i + (j - i) = i + j := by omega
  rw [hij_add] at h
  exact h

/-- If `a n = n + C` for all `n ≥ n₀`, then for any `n₀ ≤ i` and any `j`,
`∑ l ∈ Finset.Icc i j, a l = ∑ l ∈ Finset.Icc i j, (l + C)`. -/
theorem sum_Icc_eq_of_eventual_linear :
    ∀ (a : ℕ → ℕ) (n₀ C i j : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) → n₀ ≤ i →
      ∑ l ∈ Finset.Icc i j, a l = ∑ l ∈ Finset.Icc i j, (l + C) := by
  intro a n₀ C i j hlin hi
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_Icc] at hl
  exact hlin l (by omega)

/-- Eventual-stabilization tail block-sum identity: if `a n = n + C` for all `n ≥ n₀`,
then for all `n₀ ≤ i ≤ j`,
`2 * ∑ l ∈ Finset.Icc i j, a l = (j - i + 1) * (2 * i + 2 * C + (j - i))`. -/
theorem two_mul_sum_Icc_of_eventual_linear :
    ∀ (a : ℕ → ℕ) (n₀ C i j : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) → n₀ ≤ i → i ≤ j →
      2 * ∑ l ∈ Finset.Icc i j, a l = (j - i + 1) * (2 * i + 2 * C + (j - i)) := by
  intro a n₀ C i j hlin hi hij
  rw [sum_Icc_eq_of_eventual_linear a n₀ C i j hlin hi]
  exact two_mul_sum_Icc_add_const i j C hij

/-- Eventual-stabilization prefix-difference identity: if `a n = n + C` for all `n ≥ n₀`,
then for all `1 ≤ i`, `n₀ ≤ i`, and `i ≤ j`,
`2 * (prefixSum a j - prefixSum a (i - 1)) = (j - i + 1) * (2 * i + 2 * C + (j - i))`. -/
theorem two_mul_prefixSum_sub_of_eventual_linear :
    ∀ (a : ℕ → ℕ) (n₀ C i j : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) → 1 ≤ i → n₀ ≤ i → i ≤ j →
      2 * (prefixSum a j - prefixSum a (i - 1)) = (j - i + 1) * (2 * i + 2 * C + (j - i)) := by
  intro a n₀ C i j hlin hi1 hin₀ hij
  rw [prefixSum_sub_prefixSum a (by omega), show i - 1 + 1 = i by omega]
  exact two_mul_sum_Icc_of_eventual_linear a n₀ C i j hlin hin₀ hij

/-- Exact quadratic decomposition of `2 * prefixSum a j` for `j ≥ n₀ ≥ 1` when `a n = n + C`
for all `n ≥ n₀`. -/
theorem two_mul_prefixSum_tail_decomposition :
    ∀ (a : ℕ → ℕ) (n₀ C j : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) → 1 ≤ n₀ → n₀ ≤ j →
      2 * prefixSum a j =
        2 * prefixSum a (n₀ - 1) + (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀)) := by
  intro a n₀ C j hlin hn₀1 hj
  have hadd := prefixSum_add_sum_Icc a (i := n₀ - 1) (j := j) (by omega)
  rw [show n₀ - 1 + 1 = n₀ by omega] at hadd
  have hmul := congrArg (2 * ·) hadd
  have hsum := two_mul_sum_Icc_of_eventual_linear a n₀ C n₀ j hlin le_rfl hj
  omega

/-- Universal Diophantine lemma: any odd natural number dividing `2 ^ r` via `x * y = 2 ^ r`
must equal `1`. -/
theorem odd_eq_one_of_mul_eq_two_pow :
    ∀ (r x y : ℕ), x % 2 = 1 → x * y = 2 ^ r → x = 1 := by
  intro r
  induction r with
  | zero =>
    intro x y _ hxy
    simp only [pow_zero] at hxy
    rcases y with _ | y
    · simp at hxy
    · nlinarith
  | succ k ih =>
    intro x y hx hxy
    have hy_even : y % 2 = 0 := by
      have hmul : (x * y) % 2 = (2 ^ (k + 1)) % 2 := congrArg (· % 2) hxy
      rw [Nat.mul_mod, hx, pow_succ, Nat.mul_mod] at hmul
      omega
    have hy_div : y = 2 * (y / 2) := by omega
    have hxy2 : x * (y / 2) = 2 ^ k := by
      rw [hy_div, pow_succ] at hxy
      linarith
    exact ih x (y / 2) hx hxy2

/-- Every factor `x ≥ 2` in a factorization `x * y = 2 ^ r` is even. -/
theorem even_of_mul_eq_two_pow_of_ge_two :
    ∀ (r x y : ℕ), 2 ≤ x → x * y = 2 ^ r → x % 2 = 0 := by
  intro r x y hx hxy
  by_contra hodd
  have hx1 : x % 2 = 1 := by omega
  have heq := odd_eq_one_of_mul_eq_two_pow r x y hx1 hxy
  omega

/-- No product `x * y` with `2 ≤ x`, `2 ≤ y`, and `x + y` odd can equal a power of two `2 ^ r`. -/
theorem not_mul_eq_two_pow_of_ge_two_of_add_odd :
    ∀ (r x y : ℕ), 2 ≤ x → 2 ≤ y → (x + y) % 2 = 1 → x * y ≠ 2 ^ r := by
  intro r x y hx hy hodd hxy
  have hx_even : x % 2 = 0 := even_of_mul_eq_two_pow_of_ge_two r x y hx hxy
  have hy_even : y % 2 = 0 := even_of_mul_eq_two_pow_of_ge_two r y x hy (by linarith)
  omega

/-- Opposite-parity invariant for the linear-shift block-sum factors: for `i ≤ j`,
`(j - i + 1) + (2 * i + 2 * C + (j - i)) = 2 * j + 2 * C + 1` is always odd. -/
theorem linear_blockSum_factors_add_odd :
    ∀ (i j C : ℕ), i ≤ j →
      ((j - i + 1) + (2 * i + 2 * C + (j - i))) % 2 = 1 := by
  intro i j C hij
  omega

/-- No consecutive block sum of length at least `2` (`i + 1 ≤ j`) of a shifted linear sequence
`l ↦ l + C` (`i ≥ 1`) can equal a power of two `2 ^ r`. -/
theorem linear_blockSum_ne_two_pow :
    ∀ (i j C r : ℕ), 1 ≤ i → i + 1 ≤ j →
      ∑ l ∈ Finset.Icc i j, (l + C) ≠ 2 ^ r := by
  intro i j C r hi hij hsum
  have hmul : (j - i + 1) * (2 * i + 2 * C + (j - i)) = 2 ^ (r + 1) := by
    have h2 := two_mul_sum_Icc_add_const i j C (by omega)
    rw [hsum] at h2
    rw [pow_succ', ← h2]
  exact not_mul_eq_two_pow_of_ge_two_of_add_odd (r + 1)
    (j - i + 1) (2 * i + 2 * C + (j - i))
    (by omega) (by omega)
    (linear_blockSum_factors_add_odd i j C (by omega))
    hmul

/-- Classical corollary (`C = 0`): no sum of at least two consecutive positive integers
can equal a power of two `2 ^ r`. -/
theorem id_blockSum_ne_two_pow :
    ∀ (i j r : ℕ), 1 ≤ i → i + 1 ≤ j →
      ∑ l ∈ Finset.Icc i j, l ≠ 2 ^ r := by
  intro i j r hi hij
  simpa using linear_blockSum_ne_two_pow i j 0 r hi hij

/-- Eventual-stabilization tail power-of-two obstruction: if `a n = n + C` for all `n ≥ n₀`,
then no block sum `∑ l ∈ Finset.Icc i j, a l` with `1 ≤ i`, `n₀ ≤ i`, and `i + 1 ≤ j`
can equal `2 ^ r`. -/
theorem tail_blockSum_ne_two_pow_of_eventual_linear :
    ∀ (a : ℕ → ℕ) (n₀ C i j r : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) → 1 ≤ i → n₀ ≤ i → i + 1 ≤ j →
      ∑ l ∈ Finset.Icc i j, a l ≠ 2 ^ r := by
  intro a n₀ C i j r hlin hi1 hin₀ hij
  rw [sum_Icc_eq_of_eventual_linear a n₀ C i j hlin hin₀]
  exact linear_blockSum_ne_two_pow i j C r hi1 hij

/-- Prefix-difference form of the tail power-of-two obstruction: if `a n = n + C` for all
`n ≥ n₀`, then for all `1 ≤ i`, `n₀ ≤ i`, and `i + 1 ≤ j`,
`prefixSum a j - prefixSum a (i - 1) ≠ 2 ^ r`. -/
theorem tail_prefixSum_sub_ne_two_pow_of_eventual_linear :
    ∀ (a : ℕ → ℕ) (n₀ C i j r : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) → 1 ≤ i → n₀ ≤ i → i + 1 ≤ j →
      prefixSum a j - prefixSum a (i - 1) ≠ 2 ^ r := by
  intro a n₀ C i j r hlin hi1 hin₀ hij
  rw [prefixSum_sub_prefixSum a (by omega), show i - 1 + 1 = i by omega]
  exact tail_blockSum_ne_two_pow_of_eventual_linear a n₀ C i j r hlin hi1 hin₀ hij

/-- Flat-excess plateau lemma: if `a i - i = a j - j` (`1 ≤ i ≤ j`) in a Hofstadter sequence,
then for every `l ∈ [i, j]`, `a l = l + (a i - i)`. -/
theorem constant_excess_on_Icc_of_eq :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j l : ℕ),
      1 ≤ i → i ≤ l → l ≤ j → a i - i = a j - j → a l = l + (a i - i) := by
  intro a ha i j l hi hil hlj heq
  have h1 : a i - i ≤ a l - l := erdos_423_variants_nondecreasing a ha i l hi hil
  have h2 : a l - l ≤ a j - j := erdos_423_variants_nondecreasing a ha l j (by omega) hlj
  have h3 : l ≤ a l := IsHofstadterSeq_le_apply ha l (by omega)
  omega

/-- Unconditional strict excess growth across power-of-two block sums: in any Hofstadter
sequence `a`, if `∑ l ∈ Finset.Icc i j, a l = 2 ^ r` (`1 ≤ i`, `i + 1 ≤ j`), then the
excess strictly increases across the block (`a i - i < a j - j`). -/
theorem strict_excess_increase_of_blockSum_eq_two_pow :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j r : ℕ),
      1 ≤ i → i + 1 ≤ j → ∑ l ∈ Finset.Icc i j, a l = 2 ^ r → a i - i < a j - j := by
  intro a ha i j r hi hij hsum
  have hle : a i - i ≤ a j - j := erdos_423_variants_nondecreasing a ha i j hi (by omega)
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    have hcongr : ∑ l ∈ Finset.Icc i j, a l = ∑ l ∈ Finset.Icc i j, (l + (a i - i)) := by
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_Icc] at hl
      exact constant_excess_on_Icc_of_eq a ha i j l hi hl.1 hl.2 heq
    rw [hcongr] at hsum
    exact linear_blockSum_ne_two_pow i j (a i - i) r hi hij hsum
  · exact hlt

/-- Every power of two `a k = 2 ^ r` (`k ≥ 3`) occurring in the Hofstadter sequence is
witnessed by a consecutive block `[i, j]` (`1 ≤ i < j < k`) with strict excess increase
`a i - i < a j - j`. -/
theorem exists_strict_excess_block_of_term_eq_two_pow :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (k r : ℕ),
      3 ≤ k → a k = 2 ^ r →
      ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
        2 ^ r = ∑ l ∈ Finset.Icc i j, a l ∧ a i - i < a j - j := by
  intro a ha k r hk3 hak
  obtain ⟨⟨i, j, hi, hij, hjk, hsum⟩, -, -⟩ := ha.2.2 k hk3
  rw [hak] at hsum
  refine ⟨i, j, hi, hij, hjk, hsum, ?_⟩
  exact strict_excess_increase_of_blockSum_eq_two_pow a ha i j r hi hij hsum.symm

/-- Bounded-width prefix-difference interval bound: for any sequence `a` and `1 ≤ i < n₀`,
`prefixSum a j - prefixSum a (n₀ - 1) ≤ prefixSum a j - prefixSum a (i - 1) ≤ prefixSum a j`. -/
theorem prefixSum_sub_mem_interval_of_lt :
    ∀ (a : ℕ → ℕ) (n₀ i j : ℕ), 1 ≤ i → i < n₀ →
      prefixSum a j - prefixSum a (n₀ - 1) ≤ prefixSum a j - prefixSum a (i - 1) ∧
        prefixSum a j - prefixSum a (i - 1) ≤ prefixSum a j := by
  intro a n₀ i j hi1 hin₀
  have hmono : prefixSum a (i - 1) ≤ prefixSum a (n₀ - 1) := prefixSum_mono a (by omega)
  omega

/-- Bounded-width interval bound for prefix-crossing block sums (`1 ≤ i < n₀`, `i ≤ j`):
`prefixSum a j - prefixSum a (n₀ - 1) ≤ ∑ l ∈ Finset.Icc i j, a l ≤ prefixSum a j`. -/
theorem blockSum_mem_interval_of_lt :
    ∀ (a : ℕ → ℕ) (n₀ i j : ℕ), 1 ≤ i → i < n₀ → i ≤ j →
      prefixSum a j - prefixSum a (n₀ - 1) ≤ ∑ l ∈ Finset.Icc i j, a l ∧
        ∑ l ∈ Finset.Icc i j, a l ≤ prefixSum a j := by
  intro a n₀ i j hi1 hin₀ hij
  have hsub := prefixSum_sub_prefixSum a (i := i - 1) (j := j) (by omega)
  rw [show i - 1 + 1 = i by omega] at hsub
  rw [← hsub]
  exact prefixSum_sub_mem_interval_of_lt a n₀ i j hi1 hin₀

/-- Tightened bounded-width interval bound for prefix-crossing block sums (`1 ≤ i < n₀`, `i ≤ j`):
since `i - 1 ≤ n₀ - 2`, `prefixSum a j - prefixSum a (n₀ - 2) ≤ ∑ l ∈ Finset.Icc i j, a l ≤ prefixSum a j`. -/
theorem blockSum_mem_tight_interval_of_lt :
    ∀ (a : ℕ → ℕ) (n₀ i j : ℕ), 1 ≤ i → i < n₀ → i ≤ j →
      prefixSum a j - prefixSum a (n₀ - 2) ≤ ∑ l ∈ Finset.Icc i j, a l ∧
        ∑ l ∈ Finset.Icc i j, a l ≤ prefixSum a j := by
  intro a n₀ i j hi1 hin₀ hij
  have hsub := prefixSum_sub_prefixSum a (i := i - 1) (j := j) (by omega)
  rw [show i - 1 + 1 = i by omega] at hsub
  rw [← hsub]
  have hmono : prefixSum a (i - 1) ≤ prefixSum a (n₀ - 2) := prefixSum_mono a (by omega)
  omega

/-- Inter-prefix gap exclusion: if `m` lies strictly between `prefixSum a j` and
`prefixSum a (j + 1) - prefixSum a (n₀ - 1)`, then `m` cannot equal any prefix-crossing
block sum `∑ l ∈ Finset.Icc i j', a l` with `1 ≤ i < n₀` and `i ≤ j'`. -/
theorem not_prefix_crossing_blockSum_of_in_inter_prefix_gap :
    ∀ (a : ℕ → ℕ) (n₀ j m i j' : ℕ),
      prefixSum a j < m →
      m < prefixSum a (j + 1) - prefixSum a (n₀ - 1) →
      1 ≤ i → i < n₀ → i ≤ j' →
      ∑ l ∈ Finset.Icc i j', a l ≠ m := by
  intro a n₀ j m i j' hlo hhi hi1 hin₀ hij' hsum
  have hint := blockSum_mem_interval_of_lt a n₀ i j' hi1 hin₀ hij'
  rcases le_or_gt j' j with hj'le | hj'gt
  · have hPj' : prefixSum a j' ≤ prefixSum a j := prefixSum_mono a hj'le
    omega
  · have hPj' : prefixSum a (j + 1) ≤ prefixSum a j' := prefixSum_mono a (by omega)
    omega

/-- Global two-power exclusion in inter-prefix gaps under eventual stabilization: if
`a n = n + C` for all `n ≥ n₀` and `2 ^ r` lies strictly in the inter-prefix gap
`(prefixSum a j, prefixSum a (j + 1) - prefixSum a (n₀ - 1))`, then `2 ^ r` is not a
global consecutive block sum of `a`. -/
theorem not_isGlobalConsecutiveBlockSum_two_pow_of_in_inter_prefix_gap :
    ∀ (a : ℕ → ℕ) (n₀ C j r : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      prefixSum a j < 2 ^ r →
      2 ^ r < prefixSum a (j + 1) - prefixSum a (n₀ - 1) →
      ¬IsGlobalConsecutiveBlockSum a (2 ^ r) := by
  intro a n₀ C j r hlin hlo hhi ⟨i, j', hi1, hij', hsum⟩
  rcases lt_or_ge i n₀ with hin₀ | hin₀
  · exact not_prefix_crossing_blockSum_of_in_inter_prefix_gap a n₀ j (2 ^ r) i j'
      hlo hhi hi1 hin₀ (by omega) hsum.symm
  · exact tail_blockSum_ne_two_pow_of_eventual_linear a n₀ C i j' r
      hlin hi1 hin₀ hij' hsum.symm

/-- Under eventual stabilization `a n = n + C` for `n ≥ n₀`, every integer `m ≥ max n₀ 3 + C`
occurs as `a (m - C)` with `m - C ≥ 3` and therefore satisfies `IsGlobalConsecutiveBlockSum a m`. -/
theorem isGlobalConsecutiveBlockSum_of_ge_eventual_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C m : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      max n₀ 3 + C ≤ m → IsGlobalConsecutiveBlockSum a m := by
  intro a ha n₀ C m hlin hm
  have h1 : n₀ ≤ m - C := by omega
  have h2 : 3 ≤ m - C := by omega
  have hak : a (m - C) = m := by
    rw [hlin (m - C) h1]
    omega
  exact (IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum ha m).1
    ⟨m - C, h2, hak⟩

/-- Prefix-crossing left-endpoint forcing: if `a n = n + C` for all `n ≥ n₀`, any consecutive
block `[i, j]` (`1 ≤ i`, `i + 1 ≤ j`) summing to `2 ^ r` must start strictly before `n₀` (`i < n₀`). -/
theorem left_endpoint_lt_of_blockSum_eq_two_pow_of_eventual_linear :
    ∀ (a : ℕ → ℕ) (n₀ C i j r : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      1 ≤ i → i + 1 ≤ j → ∑ l ∈ Finset.Icc i j, a l = 2 ^ r → i < n₀ := by
  intro a n₀ C i j r hlin hi1 hij hsum
  by_contra hge
  exact tail_blockSum_ne_two_pow_of_eventual_linear a n₀ C i j r hlin hi1 (by omega) hij hsum

/-- Prefix-crossing interval trapping for powers of two under eventual stabilization:
if `a n = n + C` for all `n ≥ n₀`, then every `2 ^ r ≥ max n₀ 3 + C` has a representation
`prefixSum a j - prefixSum a (i - 1) = 2 ^ r` with `1 ≤ i < n₀`, `i + 1 ≤ j`, and
`prefixSum a j - prefixSum a (n₀ - 1) ≤ 2 ^ r ≤ prefixSum a j`. -/
theorem exists_prefix_crossing_rep_of_two_pow_of_eventual_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r : ℕ),
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      max n₀ 3 + C ≤ 2 ^ r →
      ∃ i j : ℕ, 1 ≤ i ∧ i < n₀ ∧ i + 1 ≤ j ∧
        prefixSum a j - prefixSum a (i - 1) = 2 ^ r ∧
        prefixSum a j - prefixSum a (n₀ - 1) ≤ 2 ^ r ∧ 2 ^ r ≤ prefixSum a j := by
  intro a ha n₀ C r hlin hr
  have hglob := isGlobalConsecutiveBlockSum_of_ge_eventual_linear a ha n₀ C (2 ^ r) hlin hr
  rcases hglob with ⟨i, j, hi1, hij, hsum⟩
  have hin₀ : i < n₀ :=
    left_endpoint_lt_of_blockSum_eq_two_pow_of_eventual_linear a n₀ C i j r hlin hi1 hij hsum.symm
  have hsub := prefixSum_sub_prefixSum a (i := i - 1) (j := j) (by omega)
  rw [show i - 1 + 1 = i by omega] at hsub
  have hp : prefixSum a j - prefixSum a (i - 1) = 2 ^ r := by omega
  have hint := prefixSum_sub_mem_interval_of_lt a n₀ i j hi1 hin₀
  exact ⟨i, j, hi1, hin₀, hij, hp, by omega, by omega⟩

/-- Tang's quadratic-exponential equation for powers of two under eventual stabilization:
whenever `a n = n + C` for `n ≥ n₀` (`1 ≤ n₀`), every `2 ^ r` exceeding `max n₀ 3 + C` and
`prefixSum a (n₀ - 1)` satisfies
`2 * 2 ^ r = 2 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) + (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀))`
for some `1 ≤ i < n₀` and `j ≥ n₀`. -/
theorem exists_prefix_crossing_quadratic_eq_of_two_pow :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C r : ℕ),
      1 ≤ n₀ →
      (∀ n : ℕ, n₀ ≤ n → a n = n + C) →
      max n₀ 3 + C ≤ 2 ^ r →
      prefixSum a (n₀ - 1) < 2 ^ r →
      ∃ i j : ℕ, 1 ≤ i ∧ i < n₀ ∧ n₀ ≤ j ∧
        2 * 2 ^ r =
          2 * (prefixSum a (n₀ - 1) - prefixSum a (i - 1)) +
            (j - n₀ + 1) * (2 * n₀ + 2 * C + (j - n₀)) := by
  intro a ha n₀ C r hn₀1 hlin hr hP
  obtain ⟨i, j, hi1, hin₀, hij, hp, -, hle_Pj⟩ :=
    exists_prefix_crossing_rep_of_two_pow_of_eventual_linear a ha n₀ C r hlin hr
  have hjn₀ : n₀ ≤ j := by
    by_contra hlt
    have hPj_le : prefixSum a j ≤ prefixSum a (n₀ - 1) := prefixSum_mono a (by omega)
    omega
  have hdecomp := two_mul_prefixSum_tail_decomposition a n₀ C j hlin hn₀1 hjn₀
  have hPi_le_Pn₀ : prefixSum a (i - 1) ≤ prefixSum a (n₀ - 1) := prefixSum_mono a (by omega)
  have hPi_le_Pj : prefixSum a (i - 1) ≤ prefixSum a j := prefixSum_mono a (by omega)
  refine ⟨i, j, hi1, hin₀, hjn₀, ?_⟩
  omega

/-- Unconditional exclusion of global linear shift from `n₀ = 1`: no Hofstadter sequence `a`
can satisfy `a n = n + C` for all `n ≥ 1`. -/
theorem not_eventual_linear_from_one :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (C : ℕ),
      ¬(∀ n : ℕ, 1 ≤ n → a n = n + C) := by
  intro a ha C hlin
  have hpow : max 1 3 + C ≤ 2 ^ (3 + C) := by
    have hle : 3 + C < 2 ^ (3 + C) := Nat.lt_two_pow_self
    omega
  obtain ⟨i, _, hi1, hin₀, -⟩ :=
    exists_prefix_crossing_rep_of_two_pow_of_eventual_linear a ha 1 C (3 + C) hlin hpow
  omega

/-- Inter-prefix gap refutation criterion: if a power of two `2 ^ r ≥ max n₀ 3 + C` lies
strictly inside an inter-prefix gap `(prefixSum a j, prefixSum a (j + 1) - prefixSum a (n₀ - 1))`,
then `a` cannot stabilize to `n + C` at `n₀`. -/
theorem not_eventual_linear_of_inter_prefix_gap_two_pow :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n₀ C j r : ℕ),
      max n₀ 3 + C ≤ 2 ^ r →
      prefixSum a j < 2 ^ r →
      2 ^ r < prefixSum a (j + 1) - prefixSum a (n₀ - 1) →
      ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C) := by
  intro a ha n₀ C j r hr hlo hhi hlin
  have hglob := isGlobalConsecutiveBlockSum_of_ge_eventual_linear a ha n₀ C (2 ^ r) hlin hr
  exact not_isGlobalConsecutiveBlockSum_two_pow_of_in_inter_prefix_gap a n₀ C j r hlin hlo hhi hglob

/-- Universal bounded monotone stabilization lemma on `ℕ`: any nondecreasing function
`f : ℕ → ℕ` on `n ≥ 1` bounded above by `M` is eventually constant. -/
theorem nat_mono_stabilizes_of_bdd :
    ∀ (f : ℕ → ℕ) (M : ℕ),
      (∀ n m : ℕ, 1 ≤ n → n ≤ m → f n ≤ f m) →
      (∀ n : ℕ, 1 ≤ n → f n ≤ M) →
      ∃ n₀ C : ℕ, 1 ≤ n₀ ∧ C ≤ M ∧ ∀ n : ℕ, n₀ ≤ n → f n = C := by
  intro f M hmono hbdd
  suffices haux : ∀ k : ℕ, k ≤ M → (∃ n : ℕ, 1 ≤ n ∧ M - k ≤ f n) →
      ∃ n₀ C : ℕ, 1 ≤ n₀ ∧ C ≤ M ∧ ∀ n : ℕ, n₀ ≤ n → f n = C by
    exact haux M le_rfl ⟨1, le_rfl, by omega⟩
  intro k
  induction k with
  | zero =>
    rintro _ ⟨n₀, hn₀1, hn₀M⟩
    refine ⟨n₀, M, hn₀1, le_rfl, fun n hn => ?_⟩
    have h1 := hmono n₀ n hn₀1 hn
    have h2 := hbdd n (by omega)
    omega
  | succ k ih =>
    intro hkM ⟨n₁, hn₁1, hn₁k⟩
    by_cases hreach : ∃ n : ℕ, 1 ≤ n ∧ M - k ≤ f n
    · exact ih (by omega) hreach
    · refine ⟨n₁, M - (k + 1), hn₁1, by omega, fun n hn => ?_⟩
      have h1 := hmono n₁ n hn₁1 hn
      have h2 : f n < M - k := Nat.lt_of_not_ge (fun hge => hreach ⟨n, by omega, hge⟩)
      omega

/-- Bounded-excess stabilization lemma (following [Ta26]): if the excess `a n - n` of a
Hofstadter sequence is bounded above by `M` for all `n ≥ 1`, then there exist `n₀ ≥ 1`
and `C ≤ M` such that `a n = n + C` for all `n ≥ n₀`. -/
theorem exists_eventual_linear_of_bounded_excess :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (M : ℕ),
      (∀ n : ℕ, 1 ≤ n → a n - n ≤ M) →
      ∃ n₀ C : ℕ, 1 ≤ n₀ ∧ C ≤ M ∧ ∀ n : ℕ, n₀ ≤ n → a n = n + C := by
  intro a ha M hbdd
  obtain ⟨n₀, C, hn₀1, hCM, hstab⟩ :=
    nat_mono_stabilizes_of_bdd (fun n => a n - n) M (erdos_423_variants_nondecreasing a ha) hbdd
  refine ⟨n₀, C, hn₀1, hCM, fun n hn => ?_⟩
  have hsub := hstab n hn
  have hle := IsHofstadterSeq_le_apply ha n (by omega)
  omega

/-- Pointwise excess-unboundedness deduction from non-stabilization: if `a n` never stabilizes
to `n + C` (`n ≥ n₀ ≥ 1`), then for every `M : ℕ`, there exists `n ≥ 1` with `M + n ≤ a n`. -/
theorem forall_exists_excess_of_not_eventual_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ n₀ C : ℕ, 1 ≤ n₀ → ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C)) →
      ∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M + n ≤ a n := by
  intro a ha hno M
  by_contra hnot
  have hbdd : ∀ n : ℕ, 1 ≤ n → a n - n ≤ M := by
    intro n hn1
    have hlt : a n < M + n := Nat.lt_of_not_ge (fun hge => hnot ⟨n, hn1, hge⟩)
    omega
  obtain ⟨n₀, C, hn₀1, -, hlin⟩ := exists_eventual_linear_of_bounded_excess a ha M hbdd
  exact hno n₀ C hn₀1 hlin

/-- Joint reduction of `erdos_423.variants.unbounded` and `erdos_423.variants.infinite_complement`
to the eventual-stabilization obstruction via `eventually_add_le_iff_exists_ge_one` and
`infinite_compl_of_forall_exists_excess`. -/
theorem unbounded_and_infinite_compl_of_not_eventual_linear :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ n₀ C : ℕ, 1 ≤ n₀ → ¬(∀ n : ℕ, n₀ ≤ n → a n = n + C)) →
      (∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n) ∧ Set.Infinite (Set.range a)ᶜ := by
  intro a ha hno
  have hex := forall_exists_excess_of_not_eventual_linear a ha hno
  refine ⟨fun M => (eventually_add_le_iff_exists_ge_one a ha M).2 (hex M),
    infinite_compl_of_forall_exists_excess a ha hex⟩

end Erdos423

end
