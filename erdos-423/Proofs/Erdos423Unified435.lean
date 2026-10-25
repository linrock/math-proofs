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

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open Finset BigOperators Filter Asymptotics

namespace Erdos423

/-!
# Universal Structural Theorems and Prefix-Difference Bounds for Erdős Problem #423

This module develops the structural theory of consecutive block sums and Hofstadter sequences
(OEIS A005243). It establishes monotonicity, step bounds, and trajectory certificates; re-proves
the nondecreasing-excess variant (already formalized independently by Anatolii Ohorodnyk in
`lean-fc-proofs`) and proves exact omitted-integer counting; characterizes global
block sums; and develops the telescoping and collision bounds for positive prefix differences
that support unboundedness and omitted-value arguments.
-/

/-!
## Adapted Definitions and Initial Structural Lemmas (`FormalConjectures/ErdosProblems/423.lean`)
-/

/-- `IsConsecutiveBlockSum a k m` means that `m` equals the sum of at least two
    consecutive terms of the sequence `a`, using indices from `{1, ..., k - 1}`. -/
def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

/-- The Hofstadter sequence (OEIS A005243): `a(1) = 1`, `a(2) = 2`, and for `k ≥ 3`,
`a(k)` is the least integer `> a(k-1)` that equals the sum of at least two consecutive terms from
`{a(1), ..., a(k-1)}`. -/
def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

/-- The third term of the Hofstadter sequence is `a(3) = 3 = a(1) + a(2) = 1 + 2`. -/
theorem erdos_423_test_a3 : ∀ a : ℕ → ℕ, IsHofstadterSeq a → a 3 = 3 := by
  intro a ⟨ha1, ha2, hk⟩
  obtain ⟨⟨i, j, hi, hij, hjk, hsum⟩, _, _⟩ := hk 3 (by omega)
  have : i = 1 ∧ j = 2 := by omega
  obtain ⟨rfl, rfl⟩ := this
  simp only [show Finset.Icc 1 2 = {1, 2} from by decide,
    Finset.sum_pair (show (1 : ℕ) ≠ 2 from by decide), ha1, ha2] at hsum
  omega

/-- The fourth term of the Hofstadter sequence is `a(4) = 5 = a(2) + a(3) = 2 + 3`. -/
theorem erdos_423_test_a4 : ∀ a : ℕ → ℕ, IsHofstadterSeq a → a 4 = 5 := by
  intro a ⟨ha1, ha2, hk⟩
  have ha3 : a 3 = 3 := erdos_423_test_a3 a ⟨ha1, ha2, hk⟩
  obtain ⟨⟨i, j, hi, hij, hjk, hsum⟩, hlt, hmin⟩ := hk 4 (by omega)
  have h_ij : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by omega
  rcases h_ij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [show Finset.Icc 1 2 = {1, 2} from by decide,
      Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), ha1, ha2] at hsum
    rw [ha3] at hlt
    omega
  · simp only [show Finset.Icc 2 3 = {2, 3} from by decide,
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), ha2, ha3] at hsum
    omega
  · rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide,
      Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3} : Finset ℕ)),
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), ha1, ha2, ha3] at hsum
    rw [ha3] at hlt
    have ha4_eq : a 4 = 6 := by omega
    have h3_lt_5 : a 3 < 5 := by omega
    have h5_lt_a4 : 5 < a 4 := by omega
    exfalso
    apply hmin 5 h3_lt_5 h5_lt_a4
    refine ⟨2, 3, by omega, by omega, by omega, ?_⟩
    rw [show Finset.Icc 2 3 = {2, 3} from by decide,
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), ha2, ha3]

/-- A Hofstadter sequence is strictly increasing from index `1` on. -/
theorem IsHofstadterSeq_strictMono {a : ℕ → ℕ} (ha : IsHofstadterSeq a) :
    StrictMono fun k => a (k + 1) := by
  obtain ⟨h1, h2, hk⟩ := ha
  refine strictMono_nat_of_lt_succ fun k => ?_
  show a (k + 1) < a (k + 1 + 1)
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · show a 1 < a 2
    omega
  · have := (hk (k + 2) (by omega)).2.1
    simpa using this

/-- A Hofstadter sequence satisfies `n ≤ a n` for `n ≥ 1`. -/
theorem IsHofstadterSeq_le_apply {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (n : ℕ)
    (hn : 1 ≤ n) : n ≤ a n := by
  have h1 := ha.1
  induction n, hn using Nat.le_induction with
  | base => omega
  | succ k hk ih =>
    have := (IsHofstadterSeq_strictMono ha) (Nat.lt_succ_self (k - 1))
    simp only [show k - 1 + 1 = k by omega, show k - 1 + 1 + 1 = k + 1 by omega] at this
    omega

/-- For indices `≥ 1`, a Hofstadter sequence preserves and reflects `<`. -/
theorem IsHofstadterSeq_lt_iff_lt {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    a i < a j ↔ i < j := by
  obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [(IsHofstadterSeq_strictMono ha).lt_iff_lt]
  omega

/-- If `a n - n` is unbounded, infinitely many integers are missed. -/
theorem IsHofstadterSeq_infinite_compl_of_unbounded {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (h : ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n) : Set.Infinite (Set.range a)ᶜ := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨n, hn⟩ := (h (N + 2)).exists_forall_of_atTop
  obtain ⟨n, hn1, hn⟩ : ∃ n, 1 ≤ n ∧ N + 2 + n ≤ a n :=
    ⟨max n 1, by omega, hn _ (le_max_left _ _)⟩
  have hcard : ((Finset.range n).image a).card < (Finset.Icc (N + 1) (a n - 1)).card := by
    calc ((Finset.range n).image a).card ≤ n := by
          simpa using Finset.card_image_le (s := Finset.range n) (f := a)
      _ < (Finset.Icc (N + 1) (a n - 1)).card := by simp; omega
  obtain ⟨x, hx, hxi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_Icc] at hx
  refine ⟨x, ?_, by omega⟩
  rintro ⟨k, rfl⟩
  rcases Nat.lt_or_ge k n with hk | hk
  · exact hxi (Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, rfl⟩)
  · have : a n ≤ a k := by
      rcases eq_or_lt_of_le hk with rfl | hklt
      · exact le_rfl
      · exact ((IsHofstadterSeq_lt_iff_lt ha hn1 (by omega)).2 hklt).le
    omega

/-- If infinitely many integers are missed, `a n - n` is unbounded. -/
theorem IsHofstadterSeq_unbounded_of_infinite_compl {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (h : Set.Infinite (Set.range a)ᶜ) : ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n := by
  intro M
  obtain ⟨t, hts, htc⟩ := h.exists_subset_card_eq (M + 1)
  set X := t.sup id with hX
  rw [Filter.eventually_atTop]
  refine ⟨X + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  set A := (Finset.Icc 1 n).image a with hA
  set T := t.filter (fun x => 1 ≤ x) with hT
  have hAcard : A.card = n := by
    rw [hA, Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro i hi j hj hij
      rw [Finset.coe_Icc, Set.mem_Icc] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd hij ((IsHofstadterSeq_lt_iff_lt ha hi.1 hj.1).2 hlt).ne
      · exact absurd hij.symm ((IsHofstadterSeq_lt_iff_lt ha hj.1 hi.1).2 hlt).ne
  have hTcard : M ≤ T.card := by
    have : (t.filter (fun x => ¬ 1 ≤ x)).card ≤ 1 := by
      calc (t.filter (fun x => ¬ 1 ≤ x)).card ≤ ({0} : Finset ℕ).card :=
            Finset.card_le_card fun x hx => by
              rw [Finset.mem_filter] at hx; simp; omega
        _ = 1 := rfl
    have := Finset.card_filter_add_card_filter_not (s := t) (fun x => 1 ≤ x)
    rw [← hT] at this
    omega
  have hdisj : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro x hxA hxT
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hxA
    exact hts (Finset.mem_filter.1 hxT).1 ⟨k, rfl⟩
  have hsub : A ∪ T ⊆ Finset.Icc 1 (a n) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Finset.mem_Icc]
    rcases hx with hx | hx
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_Icc] at hk
      refine ⟨le_trans (by omega) (IsHofstadterSeq_le_apply ha k hk.1), ?_⟩
      rcases eq_or_lt_of_le hk.2 with rfl | hlt
      · exact le_rfl
      · exact ((IsHofstadterSeq_lt_iff_lt ha hk.1 hn1).2 hlt).le
    · obtain ⟨hxt, hx1⟩ := Finset.mem_filter.1 hx
      have : x ≤ X := Finset.le_sup (f := id) hxt
      exact ⟨hx1, by have := IsHofstadterSeq_le_apply ha n hn1; omega⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hAcard, Nat.card_Icc] at this
  omega

/-- `IsConsecutiveBlockSum` is monotone in the horizon parameter `k`. -/
theorem IsConsecutiveBlockSum_mono {a : ℕ → ℕ} {k₁ k₂ m : ℕ} (hk : k₁ ≤ k₂)
    (h : IsConsecutiveBlockSum a k₁ m) : IsConsecutiveBlockSum a k₂ m := by
  rcases h with ⟨i, j, hi, hij, hjk, hsum⟩
  unfold IsConsecutiveBlockSum
  refine ⟨i, j, hi, hij, by omega, ?_⟩
  simpa only [eq_comm] using hsum.symm

/-- `IsConsecutiveBlockSum a k m` depends only on the values `a l` for `1 ≤ l < k`. -/
theorem IsConsecutiveBlockSum_congr {a b : ℕ → ℕ} {k m : ℕ}
    (hab : ∀ l : ℕ, 1 ≤ l → l < k → a l = b l) :
    IsConsecutiveBlockSum a k m ↔ IsConsecutiveBlockSum b k m := by
  constructor <;> rintro ⟨i, j, hi, hij, hjk, rfl⟩ <;> refine ⟨i, j, hi, hij, hjk, ?_⟩
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_Icc] at hl
    exact hab l (by omega) (by omega)
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_Icc] at hl
    exact (hab l (by omega) (by omega)).symm

/-- Negative control: no consecutive block sum of length `≥ 2` exists when the horizon `k ≤ 2`. -/
theorem IsConsecutiveBlockSum_not_of_le_two (a : ℕ → ℕ) {k : ℕ} (hk : k ≤ 2) (m : ℕ) :
    ¬IsConsecutiveBlockSum a k m := by
  simp only [IsConsecutiveBlockSum, not_exists, not_and]
  omega

/-- Helper: sum over the two-element interval `Finset.Icc i (i + 1)`. -/
theorem sum_Icc_succ (a : ℕ → ℕ) (i : ℕ) :
    ∑ l ∈ Finset.Icc i (i + 1), a l = a i + a (i + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

/-- Helper: sum over the three-element interval `Finset.Icc i (i + 2)`. -/
theorem sum_Icc_add_two (a : ℕ → ℕ) (i : ℕ) :
    ∑ l ∈ Finset.Icc i (i + 2), a l = a i + a (i + 1) + a (i + 2) := by
  rw [show i + 2 = (i + 1) + 1 by omega, Finset.sum_Icc_succ_top (by omega), sum_Icc_succ]

/-- Positive control: any adjacent pair sum `a i + a (i + 1)` with `1 ≤ i` and `i + 2 ≤ k`
is a valid consecutive block sum at horizon `k`. -/
theorem IsConsecutiveBlockSum_pair_mem (a : ℕ → ℕ) {i k : ℕ} (hi : 1 ≤ i) (hik : i + 2 ≤ k) :
    IsConsecutiveBlockSum a k (a i + a (i + 1)) :=
  ⟨i, i + 1, hi, le_refl (i + 1), hik, (sum_Icc_succ a i).symm⟩

/-- Positive control: any adjacent triple sum `a i + a (i + 1) + a (i + 2)` with `1 ≤ i`
and `i + 3 ≤ k` is a valid consecutive block sum at horizon `k`. -/
theorem IsConsecutiveBlockSum_triple_mem (a : ℕ → ℕ) {i k : ℕ} (hi : 1 ≤ i) (hik : i + 3 ≤ k) :
    IsConsecutiveBlockSum a k (a i + a (i + 1) + a (i + 2)) :=
  ⟨i, i + 2, hi, by omega, hik, (sum_Icc_add_two a i).symm⟩

/-- Every consecutive block sum of length `≥ 2` over `[i, j]` is at least the sum of its
last two terms `a (j - 1) + a j`. -/
theorem le_sum_Icc_of_two_terms (a : ℕ → ℕ) {i j : ℕ} (hij : i + 1 ≤ j) :
    a (j - 1) + a j ≤ ∑ l ∈ Finset.Icc i j, a l := by
  have hsub : Finset.Icc (j - 1) j ⊆ Finset.Icc i j := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    omega
  have hle := Finset.sum_le_sum_of_subset (f := a) hsub
  have hlen : j - 1 + 1 = j := by omega
  have hpair := sum_Icc_succ a (j - 1)
  rw [hlen] at hpair
  omega

/-- For any Hofstadter sequence `a` and `n ≥ 1`, `1 ≤ a n`. -/
theorem IsHofstadterSeq_pos_of_ge_one {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {n : ℕ}
    (hn : 1 ≤ n) : 1 ≤ a n :=
  hn.trans (IsHofstadterSeq_le_apply ha n hn)

/-- For `1 ≤ i ≤ j`, a Hofstadter sequence satisfies `a i ≤ a j`. -/
theorem IsHofstadterSeq_mono_of_ge_one {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) : a i ≤ a j := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact ((IsHofstadterSeq_lt_iff_lt ha hi (by omega)).2 hlt).le

/-- Any candidate consecutive block sum strictly exceeding `a (k - 1)` at stage `k ≥ 3`
upper-bounds `a k`. -/
theorem IsHofstadterSeq_le_of_isConsecutiveBlockSum {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {k m : ℕ} (hk : 3 ≤ k) (hm : a (k - 1) < m) (hblk : IsConsecutiveBlockSum a k m) :
    a k ≤ m := by
  by_contra hlt
  exact (ha.2.2 k hk).2.2 m hm (by omega) hblk

/-- Universal step upper bound: for every `k ≥ 3`, `a k ≤ a (k - 2) + a (k - 1)`. -/
theorem IsHofstadterSeq_step_upper_bound {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {k : ℕ} (hk : 3 ≤ k) : a k ≤ a (k - 2) + a (k - 1) := by
  have hk2 : 1 ≤ k - 2 := by omega
  have hpos : 1 ≤ a (k - 2) := IsHofstadterSeq_pos_of_ge_one ha hk2
  have hgt : a (k - 1) < a (k - 2) + a (k - 1) := by omega
  have hblk : IsConsecutiveBlockSum a k (a (k - 2) + a (k - 1)) := by
    have hpair := IsConsecutiveBlockSum_pair_mem a hk2 (k := k) (by omega)
    simpa [show k - 2 + 1 = k - 1 by omega] using hpair
  exact IsHofstadterSeq_le_of_isConsecutiveBlockSum ha hk hgt hblk

/-- Universal uniqueness: any two sequences satisfying `IsHofstadterSeq` agree on all `n ≥ 1`. -/
theorem IsHofstadterSeq_eq_of_ge_one {a b : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (hb : IsHofstadterSeq b) {n : ℕ} (hn : 1 ≤ n) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | h k ih =>
    rcases ( by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k ) with rfl | rfl | hk3
    · exact ha.1.trans hb.1.symm
    · exact ha.2.1.trans hb.2.1.symm
    · have hprev : a (k - 1) = b (k - 1) := ih (k - 1) (by omega) (by omega)
      have hcongr : ∀ m, IsConsecutiveBlockSum a k m ↔ IsConsecutiveBlockSum b k m :=
        fun m => IsConsecutiveBlockSum_congr fun l hl1 hlk => ih l hlk hl1
      obtain ⟨hablk, halt, hamin⟩ := ha.2.2 k hk3
      obtain ⟨hbblk, hblt, hbmin⟩ := hb.2.2 k hk3
      rcases lt_trichotomy (a k) (b k) with hlt | heq | hgt
      · exfalso
        exact hbmin (a k) (by omega) hlt ((hcongr (a k)).1 hablk)
      · exact heq
      · exfalso
        exact hamin (b k) (by omega) hgt ((hcongr (b k)).2 hbblk)

/-- Negative control: the identity sequence `n ↦ n` is not a Hofstadter sequence
(it fails at `k = 4` because `4` is not a consecutive block sum of `{1, 2, 3}`). -/
theorem not_isHofstadterSeq_id : ¬IsHofstadterSeq (fun n : ℕ => n) := by
  intro h
  have h4 := erdos_423_test_a4 (fun n : ℕ => n) h
  omega

/-- Negative control: no constant sequence is a Hofstadter sequence. -/
theorem not_isHofstadterSeq_const (c : ℕ) : ¬IsHofstadterSeq (fun _ : ℕ => c) := by
  rintro ⟨h1, h2, -⟩
  dsimp only at h1 h2
  omega

/-- `HasEligibleBlockSum a k` means there exists a consecutive block sum at horizon `k`
strictly exceeding `a (k - 1)`. -/
def HasEligibleBlockSum (a : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ m : ℕ, a (k - 1) < m ∧ IsConsecutiveBlockSum a k m

/-- Next-term selector for the canonical Hofstadter recursion. -/
noncomputable def hofstadterNext (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  open Classical in
  if h : HasEligibleBlockSum a k then Nat.find h else a (k - 1) + 1

/-- `hofstadterNext a k` is always strictly greater than `a (k - 1)`. -/
theorem lt_hofstadterNext (a : ℕ → ℕ) (k : ℕ) :
    a (k - 1) < hofstadterNext a k := by
  classical
  unfold hofstadterNext
  split_ifs with h
  · exact (Nat.find_spec h).1
  · omega

/-- The canonical Hofstadter sequence `hofstadterSeq : ℕ → ℕ` (with `hofstadterSeq 0 = 0`). -/
noncomputable def hofstadterSeq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | k + 3 =>
    hofstadterNext (fun l => if l < k + 3 then hofstadterSeq l else 0) (k + 3)
termination_by k => k
decreasing_by omega

@[simp] theorem hofstadterSeq_zero : hofstadterSeq 0 = 0 := by simp [hofstadterSeq]
@[simp] theorem hofstadterSeq_one : hofstadterSeq 1 = 1 := by simp [hofstadterSeq]
@[simp] theorem hofstadterSeq_two : hofstadterSeq 2 = 2 := by simp [hofstadterSeq]

/-- Unfolding equation for `hofstadterSeq k` when `k ≥ 3`. -/
theorem hofstadterSeq_ge_three {k : ℕ} (hk : 3 ≤ k) :
    hofstadterSeq k = hofstadterNext (fun l => if l < k then hofstadterSeq l else 0) k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 3 := ⟨k - 3, by omega⟩
  rw [hofstadterSeq]

/-- One-step strict growth of `hofstadterSeq` for `k ≥ 2`. -/
theorem hofstadterSeq_lt_succ {k : ℕ} (hk : 2 ≤ k) :
    hofstadterSeq (k - 1) < hofstadterSeq k := by
  rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
  · simp [hofstadterSeq_one, hofstadterSeq_two]
  · rw [hofstadterSeq_ge_three hk3]
    have hlt := lt_hofstadterNext (fun l => if l < k then hofstadterSeq l else 0) k
    simpa [show k - 1 < k by omega] using hlt

/-- Positivity of `hofstadterSeq n` for all `n ≥ 1`. -/
theorem hofstadterSeq_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ hofstadterSeq n := by
  induction n, hn using Nat.le_induction with
  | base => simp [hofstadterSeq_one]
  | succ k hk ih =>
    have hlt := hofstadterSeq_lt_succ (k := k + 1) (by omega)
    omega

/-- Unconditional non-vacuity: `hofstadterSeq` satisfies `IsHofstadterSeq`. -/
theorem isHofstadterSeq_hofstadterSeq : IsHofstadterSeq hofstadterSeq := by
  classical
  refine ⟨hofstadterSeq_one, hofstadterSeq_two, fun k hk => ?_⟩
  let f : ℕ → ℕ := fun l => if l < k then hofstadterSeq l else 0
  have hcongr : ∀ m, IsConsecutiveBlockSum f k m ↔ IsConsecutiveBlockSum hofstadterSeq k m :=
    fun m => IsConsecutiveBlockSum_congr fun l _ hlk => by simp [f, hlk]
  have hf_k1 : f (k - 1) = hofstadterSeq (k - 1) := by
    simp [f, show k - 1 < k by omega]
  have helig : HasEligibleBlockSum f k := by
    refine ⟨hofstadterSeq (k - 2) + hofstadterSeq (k - 1), ?_, ?_⟩
    · have hpos : 1 ≤ hofstadterSeq (k - 2) := hofstadterSeq_pos (by omega)
      omega
    · rw [hcongr]
      have hpr := IsConsecutiveBlockSum_pair_mem hofstadterSeq (i := k - 2) (k := k)
        (by omega) (by omega)
      simpa [show k - 2 + 1 = k - 1 by omega] using hpr
  have hfk : hofstadterSeq k = Nat.find helig := by
    rw [hofstadterSeq_ge_three hk]
    change hofstadterNext f k = Nat.find helig
    simp [hofstadterNext, helig]
  have hspec := Nat.find_spec helig
  refine ⟨(hcongr _).1 (hfk ▸ hspec.2), hofstadterSeq_lt_succ (by omega), fun m hlo hhi hblk => ?_⟩
  rw [hfk] at hhi
  have hmin := Nat.find_min helig hhi
  exact hmin ⟨by omega, (hcongr m).2 hblk⟩

/-- Unconditional existence of a sequence satisfying `IsHofstadterSeq`. -/
theorem exists_isHofstadterSeq : ∃ a : ℕ → ℕ, IsHofstadterSeq a :=
  ⟨hofstadterSeq, isHofstadterSeq_hofstadterSeq⟩

/-- Unique existence of the normalized Hofstadter sequence (`a 0 = 0 ∧ IsHofstadterSeq a`). -/
theorem existsUnique_isHofstadterSeq : ∃! a : ℕ → ℕ, a 0 = 0 ∧ IsHofstadterSeq a := by
  refine ⟨hofstadterSeq, ⟨hofstadterSeq_zero, isHofstadterSeq_hofstadterSeq⟩, ?_⟩
  rintro a ⟨ha0, ha⟩
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ha0.trans hofstadterSeq_zero.symm
  · exact IsHofstadterSeq_eq_of_ge_one ha isHofstadterSeq_hofstadterSeq hn

/-- One-step nondecreasing excess: `a n - n ≤ a (n + 1) - (n + 1)` for `n ≥ 1`. -/
theorem IsHofstadterSeq_sub_self_step_le {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {n : ℕ} (hn : 1 ≤ n) : a n - n ≤ a (n + 1) - (n + 1) := by
  have hlt : a n < a (n + 1) := (IsHofstadterSeq_lt_iff_lt ha hn (by omega)).2 (Nat.lt_succ_self n)
  have hle : n ≤ a n := IsHofstadterSeq_le_apply ha n hn
  omega

/-- Re-proof of the nondecreasing-excess variant proved independently by Bolan and Tang (2026):
for any Hofstadter sequence `a`, `a n - n` is nondecreasing for `n ≥ 1`. The same statement is
already registered by a separate external formalization (Anatolii Ohorodnyk, lean-fc-proofs), so
this result duplicates a known proof and is not claimed as new mathematics. -/
theorem erdos_423_variants_nondecreasing :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m := by
  intro a ha n m hn hnm
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hnk ih =>
    exact ih.trans (IsHofstadterSeq_sub_self_step_le ha (by omega))

/-- Exact characterization of when the excess `a n - n` strictly increases across `[n, n + 1]`. -/
theorem IsHofstadterSeq_sub_self_strict_step_iff {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {n : ℕ} (hn : 1 ≤ n) :
    a n - n < a (n + 1) - (n + 1) ↔ a n + 2 ≤ a (n + 1) := by
  have hlt : a n < a (n + 1) := (IsHofstadterSeq_lt_iff_lt ha hn (by omega)).2 (Nat.lt_succ_self n)
  have hle : n ≤ a n := IsHofstadterSeq_le_apply ha n hn
  omega

/-- Any integer strictly between `a (k - 1)` and `a k` (`k ≥ 2`) never occurs as `a n` for `n ≥ 1`. -/
theorem IsHofstadterSeq_not_mem_pos_range_of_between {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {k m : ℕ} (hk : 2 ≤ k) (hlo : a (k - 1) < m) (hhi : m < a k) :
    ∀ n : ℕ, 1 ≤ n → a n ≠ m := by
  intro n hn hnm
  subst hnm
  have hk1 : 1 ≤ k - 1 := by omega
  have h1 : k - 1 < n := (IsHofstadterSeq_lt_iff_lt ha hk1 hn).1 hlo
  have h2 : n < k := (IsHofstadterSeq_lt_iff_lt ha hn (by omega)).1 hhi
  omega

/-- Exact omitted-integer counting identity: for `n ≥ 1`, the number of positive integers
in `[1, a n]` omitted by `{a 1, ..., a n}` equals `a n - n`. -/
theorem IsHofstadterSeq_card_omitted_Icc_eq_sub {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {n : ℕ} (hn : 1 ≤ n) :
    ((Finset.Icc 1 (a n)) \ ((Finset.Icc 1 n).image a)).card = a n - n := by
  have hsub : (Finset.Icc 1 n).image a ⊆ Finset.Icc 1 (a n) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_Icc] at hk ⊢
    exact ⟨IsHofstadterSeq_pos_of_ge_one ha hk.1, IsHofstadterSeq_mono_of_ge_one ha hk.1 hk.2⟩
  have hinj : Set.InjOn a (Finset.Icc 1 n) := by
    intro i hi j hj hij
    rw [Finset.coe_Icc, Set.mem_Icc] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact ((IsHofstadterSeq_lt_iff_lt ha hi.1 hj.1).2 hlt).ne hij
    · exact ((IsHofstadterSeq_lt_iff_lt ha hj.1 hi.1).2 hlt).ne hij.symm
  rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, Finset.card_image_of_injOn hinj,
    Nat.card_Icc, Nat.card_Icc]
  have := IsHofstadterSeq_le_apply ha n hn
  omega

/-- `IsGlobalConsecutiveBlockSum a m` means `m` is the sum of at least two consecutive terms
`a i + ... + a j` (`1 ≤ i < j`) with no upper horizon restriction on `j`. -/
def IsGlobalConsecutiveBlockSum (a : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ m = ∑ l ∈ Finset.Icc i j, a l

/-- Every consecutive block sum of length `≥ 2` strictly exceeds its right endpoint value `a j`. -/
theorem IsHofstadterSeq_blockSum_gt_right_endpoint {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + 1 ≤ j) :
    a j < ∑ l ∈ Finset.Icc i j, a l := by
  have h2 := le_sum_Icc_of_two_terms a hij
  have hj1 : 1 ≤ j - 1 := by omega
  have hpos : 1 ≤ a (j - 1) := IsHofstadterSeq_pos_of_ge_one ha hj1
  omega

/-- Horizon cutoff equivalence: for any `k ≥ 1` and `m ≤ a k`, `m` is a consecutive block sum
at horizon `k` if and only if `m` is a global consecutive block sum. -/
theorem IsHofstadterSeq_isConsecutiveBlockSum_iff_global_of_le {a : ℕ → ℕ}
    (ha : IsHofstadterSeq a) {k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ a k) :
    IsConsecutiveBlockSum a k m ↔ IsGlobalConsecutiveBlockSum a m := by
  constructor
  · rintro ⟨i, j, hi, hij, -, hsum⟩
    exact ⟨i, j, hi, hij, hsum⟩
  · rintro ⟨i, j, hi, hij, hsum⟩
    refine ⟨i, j, hi, hij, ?_, hsum⟩
    by_contra hjk
    have hkj : k ≤ j := by omega
    have hakj : a k ≤ a j := IsHofstadterSeq_mono_of_ge_one ha hk hkj
    have hgt : a j < m := by
      rw [hsum]
      exact IsHofstadterSeq_blockSum_gt_right_endpoint ha hi hij
    omega

/-- Global Consecutive-Block-Sum Closure Theorem: every global consecutive block sum of length `≥ 2`
occurs in the Hofstadter sequence at some index `k ≥ 3`. -/
theorem IsHofstadterSeq_exists_eq_of_isGlobalConsecutiveBlockSum {a : ℕ → ℕ}
    (ha : IsHofstadterSeq a) {m : ℕ} (hm : IsGlobalConsecutiveBlockSum a m) :
    ∃ k : ℕ, 3 ≤ k ∧ a k = m := by
  rcases hm with ⟨i, j, hi, hij, hsum⟩
  have hj_gt : a j < m := by
    rw [hsum]
    exact IsHofstadterSeq_blockSum_gt_right_endpoint ha hi hij
  have hm_ge1 : 1 ≤ m := by omega
  have hex : ∃ k : ℕ, 1 ≤ k ∧ m ≤ a k := ⟨m, hm_ge1, IsHofstadterSeq_le_apply ha m hm_ge1⟩
  classical
  let k := Nat.find hex
  have hk_spec : 1 ≤ k ∧ m ≤ a k := Nat.find_spec hex
  have hj_lt_k : j < k := by
    by_contra hle
    have hkj : k ≤ j := by omega
    have : a k ≤ a j := IsHofstadterSeq_mono_of_ge_one ha hk_spec.1 hkj
    omega
  have hk3 : 3 ≤ k := by omega
  have hk1_lt : k - 1 < k := by omega
  have hmin_k1 := Nat.find_min hex hk1_lt
  have hk1_ge1 : 1 ≤ k - 1 := by omega
  have ha_k1_lt : a (k - 1) < m := by
    by_contra hge
    exact hmin_k1 ⟨hk1_ge1, by omega⟩
  have hblk_k : IsConsecutiveBlockSum a k m := ⟨i, j, hi, hij, by omega, hsum⟩
  have hak_le : a k ≤ m := IsHofstadterSeq_le_of_isConsecutiveBlockSum ha hk3 ha_k1_lt hblk_k
  exact ⟨k, hk3, by omega⟩

/-- Exact characterization of Hofstadter sequence terms from index `3` onward:
`m` equals `a k` for some `k ≥ 3` if and only if `m` is a global consecutive block sum. -/
theorem IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum
    {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (m : ℕ) :
    (∃ k : ℕ, 3 ≤ k ∧ a k = m) ↔ IsGlobalConsecutiveBlockSum a m := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases (ha.2.2 k hk).1 with ⟨i, j, hi, hij, -, hsum⟩
    exact ⟨i, j, hi, hij, hsum⟩
  · exact IsHofstadterSeq_exists_eq_of_isGlobalConsecutiveBlockSum ha

/-- Full membership characterization for `{a k : k ≥ 1}`: a natural number `m` occurs in
`{a k : k ≥ 1}` iff `m = 1`, `m = 2`, or `m` is a global consecutive block sum. -/
theorem IsHofstadterSeq_exists_ge_one_eq_iff {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (m : ℕ) :
    (∃ k : ℕ, 1 ≤ k ∧ a k = m) ↔ m = 1 ∨ m = 2 ∨ IsGlobalConsecutiveBlockSum a m := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
    · exact Or.inl ha.1
    · exact Or.inr (Or.inl ha.2.1)
    · exact Or.inr (Or.inr ((IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum ha (a k)).1 ⟨k, hk3, rfl⟩))
  · rintro (rfl | rfl | hm)
    · exact ⟨1, le_rfl, ha.1⟩
    · exact ⟨2, by omega, ha.2.1⟩
    · obtain ⟨k, hk3, hk⟩ := IsHofstadterSeq_exists_eq_of_isGlobalConsecutiveBlockSum ha hm
      exact ⟨k, by omega, hk⟩

/-- Prefix sums `P(n) = ∑_{l=1}^n a(l)` of a sequence `a`. -/
def prefixSum (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ l ∈ Finset.Icc 1 n, a l

@[simp]
theorem prefixSum_zero (a : ℕ → ℕ) : prefixSum a 0 = 0 := by
  simp [prefixSum]

/-- One-step recurrence for `prefixSum`. -/
theorem prefixSum_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixSum a (n + 1) = prefixSum a n + a (n + 1) := by
  simp only [prefixSum]
  exact Finset.sum_Icc_succ_top (by omega) a

/-- Additive telescoping identity for `prefixSum`: for `i ≤ j`,
`prefixSum a i + ∑_{l=i+1}^j a(l) = prefixSum a j`. -/
theorem prefixSum_add_sum_Icc (a : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    prefixSum a i + ∑ l ∈ Finset.Icc (i + 1) j, a l = prefixSum a j := by
  induction j, hij using Nat.le_induction with
  | base =>
    simp
  | succ k hik ih =>
    rw [prefixSum_succ, Finset.sum_Icc_succ_top (by omega), ← add_assoc, ih]

/-- Difference telescoping identity for `prefixSum`: for `i ≤ j`,
`prefixSum a j - prefixSum a i = ∑_{l=i+1}^j a(l)`. -/
theorem prefixSum_sub_prefixSum (a : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    prefixSum a j - prefixSum a i = ∑ l ∈ Finset.Icc (i + 1) j, a l := by
  have h := prefixSum_add_sum_Icc a hij
  omega

/-- First differences of `prefixSum a` recover the sequence `a (n + 1)`. -/
theorem prefixSum_succ_sub (a : ℕ → ℕ) (n : ℕ) :
    prefixSum a (n + 1) - prefixSum a n = a (n + 1) := by
  have h := prefixSum_succ a n
  omega

/-- Strict convexity of `prefixSum a`: its consecutive first differences are strictly increasing. -/
theorem IsHofstadterSeq_prefixSum_strictConvex_diff {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (n : ℕ) :
    prefixSum a (n + 1) - prefixSum a n < prefixSum a (n + 2) - prefixSum a (n + 1) := by
  rw [prefixSum_succ_sub, prefixSum_succ_sub]
  exact (IsHofstadterSeq_lt_iff_lt ha (by omega) (by omega)).2 (by omega)

/-- Bolan–Tang Prefix-Difference Inclusion Theorem: for any Hofstadter sequence `a` and any
`0 ≤ i < j`, the positive prefix difference `prefixSum a j - prefixSum a i` belongs to `{a k : k ≥ 1}`. -/
theorem IsHofstadterSeq_exists_eq_prefixSum_sub {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {i j : ℕ} (hij : i < j) :
    ∃ k : ℕ, 1 ≤ k ∧ a k = prefixSum a j - prefixSum a i := by
  rcases (by omega : j = i + 1 ∨ i + 2 ≤ j) with rfl | hij2
  · refine ⟨i + 1, by omega, ?_⟩
    exact (prefixSum_succ_sub a i).symm
  · have hglob : IsGlobalConsecutiveBlockSum a (prefixSum a j - prefixSum a i) := by
      refine ⟨i + 1, j, by omega, by omega, ?_⟩
      exact prefixSum_sub_prefixSum a (by omega)
    obtain ⟨k, hk3, hk⟩ := IsHofstadterSeq_exists_eq_of_isGlobalConsecutiveBlockSum ha hglob
    exact ⟨k, by omega, hk⟩

/-- `posPrefixDiffs a m` is the finset of all positive prefix-sum differences
`P(j) - P(i)` for `0 ≤ i < j ≤ m`. -/
def posPrefixDiffs (a : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  ((Finset.Iic m ×ˢ Finset.Iic m).filter (fun p : ℕ × ℕ => p.1 < p.2)).image
    (fun p : ℕ × ℕ => prefixSum a p.2 - prefixSum a p.1)

/-- Monotonicity of `prefixSum a`. -/
theorem prefixSum_mono (a : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    prefixSum a i ≤ prefixSum a j := by
  have h := prefixSum_add_sum_Icc a hij
  omega

/-- Finite-Horizon Positive Prefix-Difference Embedding (Bolan–Tang bridge):
whenever `prefixSum a m ≤ a N` (`N ≥ 1`), every positive prefix-sum difference of
`{P(0), ..., P(m)}` belongs to `{a 1, ..., a N}`. -/
theorem IsHofstadterSeq_posPrefixDiffs_subset_image_Icc {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {m N : ℕ} (hN : 1 ≤ N) (hP : prefixSum a m ≤ a N) :
    posPrefixDiffs a m ⊆ (Finset.Icc 1 N).image a := by
  intro d hd
  rcases Finset.mem_image.1 hd with ⟨⟨i, j⟩, hp, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Iic, Finset.mem_Iic] at hp
  rcases hp with ⟨⟨hi, hj⟩, hij⟩
  dsimp only at hij ⊢
  obtain ⟨k, hk1, hk⟩ := IsHofstadterSeq_exists_eq_prefixSum_sub ha hij
  have hPj : prefixSum a j ≤ prefixSum a m := prefixSum_mono a hj
  have hak_le : a k ≤ a N := by omega
  have hkN : k ≤ N := by
    by_contra hgt
    have hNk : N < k := by omega
    have := (IsHofstadterSeq_lt_iff_lt ha hN hk1).2 hNk
    omega
  exact Finset.mem_image.2 ⟨k, Finset.mem_Icc.2 ⟨hk1, hkN⟩, hk⟩

/-- Finite-Horizon Positive Prefix-Difference Cardinality Bound:
whenever `prefixSum a m ≤ a N` (`N ≥ 1`), `(posPrefixDiffs a m).card ≤ N`. -/
theorem IsHofstadterSeq_card_posPrefixDiffs_le {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    {m N : ℕ} (hN : 1 ≤ N) (hP : prefixSum a m ≤ a N) :
    (posPrefixDiffs a m).card ≤ N := by
  calc (posPrefixDiffs a m).card
      ≤ ((Finset.Icc 1 N).image a).card :=
        Finset.card_le_card (IsHofstadterSeq_posPrefixDiffs_subset_image_Icc ha hN hP)
    _ ≤ (Finset.Icc 1 N).card := Finset.card_image_le
    _ = N := by simp

/-- Permanent omission of `4`: `a n ≠ 4` for all `n ≥ 1`. -/
theorem IsHofstadterSeq_four_omitted {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (n : ℕ) (hn : 1 ≤ n) : a n ≠ 4 := by
  have ha3 : a 3 = 3 := erdos_423_test_a3 a ha
  have ha4 : a 4 = 5 := erdos_423_test_a4 a ha
  exact IsHofstadterSeq_not_mem_pos_range_of_between ha (k := 4) (by omega) (by simp [ha3]) (by simp [ha4]) n hn

/-- The fifth term of the Hofstadter sequence is `a(5) = 6 = a(1) + a(2) + a(3)`. -/
theorem erdos_423_test_a_five : ∀ a : ℕ → ℕ, IsHofstadterSeq a → a 5 = 6 := by
  intro a ha
  have ha1 : a 1 = 1 := ha.1
  have ha2 : a 2 = 2 := ha.2.1
  have ha3 : a 3 = 3 := erdos_423_test_a3 a ha
  have ha4 : a 4 = 5 := erdos_423_test_a4 a ha
  have hlt : 5 < a 5 := by
    have := (ha.2.2 5 (by omega)).2.1
    simpa [ha4] using this
  have hblk6 : IsConsecutiveBlockSum a 5 6 := by
    have htr := IsConsecutiveBlockSum_triple_mem a (i := 1) (k := 5) (by omega) (by omega)
    simpa [ha1, ha2, ha3] using htr
  have hle6 : a 5 ≤ 6 := IsHofstadterSeq_le_of_isConsecutiveBlockSum ha (by omega) (by simp [ha4]) hblk6
  omega

/-- The sixth term of the Hofstadter sequence is `a(6) = 8 = a(3) + a(4) = 3 + 5`. -/
theorem erdos_423_test_a_six : ∀ a : ℕ → ℕ, IsHofstadterSeq a → a 6 = 8 := by
  intro a ha
  have ha1 : a 1 = 1 := ha.1
  have ha2 : a 2 = 2 := ha.2.1
  have ha3 : a 3 = 3 := erdos_423_test_a3 a ha
  have ha4 : a 4 = 5 := erdos_423_test_a4 a ha
  have ha5 : a 5 = 6 := erdos_423_test_a_five a ha
  have hblk8 : IsConsecutiveBlockSum a 6 8 := by
    have hpr := IsConsecutiveBlockSum_pair_mem a (i := 3) (k := 6) (by omega) (by omega)
    simpa [ha3, ha4] using hpr
  have hstep : a 6 ≤ 8 := by
    exact IsHofstadterSeq_le_of_isConsecutiveBlockSum ha (by omega) (by simp [ha5]) hblk8
  obtain ⟨⟨i, j, hi, hij, hjk, hsum⟩, hlt, -⟩ := ha.2.2 6 (by omega)
  have h6_lt : 6 < a 6 := by simpa [ha5] using hlt
  have hij_cases :
      (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 1 ∧ j = 5) ∨
      (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 2 ∧ j = 5) ∨
      (i = 3 ∧ j = 4) ∨ (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 5) := by omega
  rcases hij_cases with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [sum_Icc_succ, ha1, ha2] at hsum; omega
  · rw [sum_Icc_add_two, ha1, ha2, ha3] at hsum; omega
  · have h14 : ∑ l ∈ Finset.Icc 1 4, a l = 11 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.sum_Icc_succ_top (by omega),
        sum_Icc_add_two, ha1, ha2, ha3, ha4]
    omega
  · have h15 : ∑ l ∈ Finset.Icc 1 5, a l = 17 := by
      rw [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_Icc_succ_top (by omega),
        show (4 : ℕ) = 3 + 1 from rfl, Finset.sum_Icc_succ_top (by omega),
        sum_Icc_add_two, ha1, ha2, ha3, ha4, ha5]
    omega
  · rw [sum_Icc_succ, ha2, ha3] at hsum; omega
  · rw [sum_Icc_add_two, ha2, ha3, ha4] at hsum; omega
  · have h25 : ∑ l ∈ Finset.Icc 2 5, a l = 16 := by
      rw [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_Icc_succ_top (by omega),
        sum_Icc_add_two, ha2, ha3, ha4, ha5]
    omega
  · rw [sum_Icc_succ, ha3, ha4] at hsum; omega
  · rw [sum_Icc_add_two, ha3, ha4, ha5] at hsum; omega
  · rw [sum_Icc_succ, ha4, ha5] at hsum; omega

/-- Permanent omission of `7`: `a n ≠ 7` for all `n ≥ 1`. -/
theorem IsHofstadterSeq_seven_omitted {a : ℕ → ℕ} (ha : IsHofstadterSeq a)
    (n : ℕ) (hn : 1 ≤ n) : a n ≠ 7 := by
  have ha5 : a 5 = 6 := erdos_423_test_a_five a ha
  have ha6 : a 6 = 8 := erdos_423_test_a_six a ha
  exact IsHofstadterSeq_not_mem_pos_range_of_between ha (k := 6) (by omega) (by simp [ha5]) (by simp [ha6]) n hn

/-!
## Prefix-Difference Collision Bounds, Convex Slice Injectivity, and Unbounded-Excess Reductions

This module advances the Bolan--Tang convex prefix-difference method. It proves monotonicity and
convexity of prefix sums, obtains the linear lower bound on distinct positive prefix differences,
and bounds collision fibers. Together with nondecreasing excess, these results reduce eventual
unboundedness and infinitude of the omitted complement to a single threshold witness.
-/

/-- For any Hofstadter sequence `a` and `n ≥ 1`, `1 ≤ prefixSum a n`. -/
theorem prefixSum_pos_of_ge_one :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (n : ℕ), 1 ≤ n → 1 ≤ prefixSum a n := by
  intro a ha n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [prefixSum_succ]
  have hpos : 1 ≤ a (k + 1) := IsHofstadterSeq_pos_of_ge_one ha (by omega)
  omega

/-- `prefixSum a` is strictly increasing for any Hofstadter sequence `a`. -/
theorem prefixSum_strictMono :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j : ℕ), i < j → prefixSum a i < prefixSum a j := by
  intro a ha i j hij
  have hdiff := prefixSum_add_sum_Icc a (le_of_lt hij)
  have hmem : i + 1 ∈ Finset.Icc (i + 1) j := Finset.mem_Icc.2 ⟨le_rfl, hij⟩
  have hle : a (i + 1) ≤ ∑ l ∈ Finset.Icc (i + 1) j, a l :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  have hpos : 1 ≤ a (i + 1) := IsHofstadterSeq_pos_of_ge_one ha (by omega)
  omega

/-- `prefixSum a` preserves and reflects strict inequality `<`. -/
theorem prefixSum_lt_iff_lt :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j : ℕ), prefixSum a i < prefixSum a j ↔ i < j := by
  intro a ha i j
  constructor
  · intro hlt
    by_contra hge
    have hle : prefixSum a j ≤ prefixSum a i := prefixSum_mono a (by omega)
    omega
  · exact prefixSum_strictMono a ha i j

/-- `prefixSum a` is injective on all of `ℕ`. -/
theorem prefixSum_inj_iff :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j : ℕ), prefixSum a i = prefixSum a j ↔ i = j := by
  intro a ha i j
  constructor
  · intro heq
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have := prefixSum_strictMono a ha i j hlt
      omega
    · rfl
    · have := prefixSum_strictMono a ha j i hgt
      omega
  · intro h
    rw [h]

/-- Every positive prefix difference `prefixSum a j - prefixSum a i` (`i < j`) is at least `1`. -/
theorem prefixSum_sub_pos_of_lt :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j : ℕ), i < j → 1 ≤ prefixSum a j - prefixSum a i := by
  intro a ha i j hij
  have hlt := prefixSum_strictMono a ha i j hij
  omega

/-- For a fixed left endpoint `i`, `j ↦ prefixSum a j - prefixSum a i` is strictly increasing
on `i ≤ j`. -/
theorem prefixSum_sub_strictMono_right :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i j₁ j₂ : ℕ),
      i ≤ j₁ → j₁ < j₂ → prefixSum a j₁ - prefixSum a i < prefixSum a j₂ - prefixSum a i := by
  intro a ha i j₁ j₂ hij₁ hj₁₂
  have hle : prefixSum a i ≤ prefixSum a j₁ := prefixSum_mono a hij₁
  have hlt : prefixSum a j₁ < prefixSum a j₂ := prefixSum_strictMono a ha j₁ j₂ hj₁₂
  omega

/-- For a fixed right endpoint `j`, `i ↦ prefixSum a j - prefixSum a i` is strictly decreasing
on `i ≤ j`. -/
theorem prefixSum_sub_strictAnti_left :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i₁ i₂ j : ℕ),
      i₁ < i₂ → i₂ ≤ j → prefixSum a j - prefixSum a i₂ < prefixSum a j - prefixSum a i₁ := by
  intro a ha i₁ i₂ j hi₁₂ hi₂j
  have hlt : prefixSum a i₁ < prefixSum a i₂ := prefixSum_strictMono a ha i₁ i₂ hi₁₂
  have hle : prefixSum a i₂ ≤ prefixSum a j := prefixSum_mono a hi₂j
  omega

/-- Exact telescoping identity relating consecutive sliding windows of length `d`:
`(P(i + 1 + d) - P(i + 1)) + a(i + 1) = (P(i + d) - P(i)) + a(i + d + 1)`. -/
theorem prefixSum_shift_step_identity :
    ∀ (a : ℕ → ℕ) (i d : ℕ),
      (prefixSum a (i + 1 + d) - prefixSum a (i + 1)) + a (i + 1) =
        (prefixSum a (i + d) - prefixSum a i) + a (i + d + 1) := by
  intro a i d
  have h1 : prefixSum a i ≤ prefixSum a (i + d) := prefixSum_mono a (by omega)
  have h2 : prefixSum a (i + 1) ≤ prefixSum a (i + 1 + d) := prefixSum_mono a (by omega)
  have h3 := prefixSum_succ a i
  have h4 := prefixSum_succ a (i + d)
  have h5 : i + 1 + d = i + d + 1 := by omega
  rw [h5] at h2 ⊢
  omega

/-- One-step strict convexity along fixed block length `d ≥ 1`: shifting the window `[i + 1, i + d]`
one step right strictly increases its sum. -/
theorem prefixSum_fixed_length_step_lt :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (i d : ℕ), 1 ≤ d →
      prefixSum a (i + d) - prefixSum a i < prefixSum a (i + 1 + d) - prefixSum a (i + 1) := by
  intro a ha i d hd
  have hid := prefixSum_shift_step_identity a i d
  have hlt : a (i + 1) < a (i + d + 1) :=
    (IsHofstadterSeq_lt_iff_lt ha (by omega) (by omega)).2 (by omega)
  omega

/-- Multi-step strict convexity along fixed block length `d ≥ 1`: for any `i₁ < i₂`,
`prefixSum a (i₁ + d) - prefixSum a i₁ < prefixSum a (i₂ + d) - prefixSum a i₂`. -/
theorem prefixSum_fixed_length_strictMono :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (d i₁ i₂ : ℕ), 1 ≤ d → i₁ < i₂ →
      prefixSum a (i₁ + d) - prefixSum a i₁ < prefixSum a (i₂ + d) - prefixSum a i₂ := by
  intro a ha d i₁ i₂ hd hij
  induction i₂, hij using Nat.le_induction with
  | base =>
    exact prefixSum_fixed_length_step_lt a ha i₁ d hd
  | succ k hk ih =>
    exact lt_trans ih (prefixSum_fixed_length_step_lt a ha k d hd)

/-- Fixed-length window injectivity: two positive prefix differences of the same block length
`d ≥ 1` are equal only if their starting indices coincide. -/
theorem prefixSum_fixed_length_inj :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (d i₁ i₂ : ℕ), 1 ≤ d →
      prefixSum a (i₁ + d) - prefixSum a i₁ = prefixSum a (i₂ + d) - prefixSum a i₂ → i₁ = i₂ := by
  intro a ha d i₁ i₂ hd heq
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hgt
  · have := prefixSum_fixed_length_strictMono a ha d i₁ i₂ hd hlt
    omega
  · rfl
  · have := prefixSum_fixed_length_strictMono a ha d i₂ i₁ hd hgt
    omega

/-- Membership constructor for `posPrefixDiffs a m`: for any `i < j ≤ m`,
`prefixSum a j - prefixSum a i ∈ posPrefixDiffs a m`. -/
theorem mem_posPrefixDiffs_of_lt :
    ∀ (a : ℕ → ℕ) (m i j : ℕ), i < j → j ≤ m →
      prefixSum a j - prefixSum a i ∈ posPrefixDiffs a m := by
  intro a m i j hij hjm
  unfold posPrefixDiffs
  refine Finset.mem_image.2 ⟨(i, j), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Iic, Finset.mem_Iic]
  exact ⟨⟨by omega, hjm⟩, hij⟩

/-- Every sequence term `a k` (`1 ≤ k ≤ m`) belongs to `posPrefixDiffs a m` as a unit-length
prefix difference `prefixSum a k - prefixSum a (k - 1)`. -/
theorem term_mem_posPrefixDiffs :
    ∀ (a : ℕ → ℕ) (m k : ℕ), 1 ≤ k → k ≤ m → a k ∈ posPrefixDiffs a m := by
  intro a m k hk1 hkm
  have hsub : prefixSum a k - prefixSum a (k - 1) = a k := by
    have h := prefixSum_succ_sub a (k - 1)
    simpa [show k - 1 + 1 = k by omega] using h
  rw [← hsub]
  exact mem_posPrefixDiffs_of_lt a m (k - 1) k (by omega) hkm

/-- The initial image `(Finset.Icc 1 m).image a` is a subset of `posPrefixDiffs a m`. -/
theorem image_Icc_subset_posPrefixDiffs :
    ∀ (a : ℕ → ℕ) (m : ℕ), (Finset.Icc 1 m).image a ⊆ posPrefixDiffs a m := by
  intro a m x hx
  rcases Finset.mem_image.1 hx with ⟨k, hk, rfl⟩
  rw [Finset.mem_Icc] at hk
  exact term_mem_posPrefixDiffs a m k hk.1 hk.2

/-- Universal baseline cardinality bound: `m ≤ (posPrefixDiffs a m).card` for all `m`. -/
theorem card_posPrefixDiffs_ge_self :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m : ℕ), m ≤ (posPrefixDiffs a m).card := by
  intro a ha m
  have hinj : Set.InjOn a (Finset.Icc 1 m) := by
    intro i hi j hj hij
    rw [Finset.coe_Icc, Set.mem_Icc] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exfalso
      exact ((IsHofstadterSeq_lt_iff_lt ha hi.1 hj.1).2 hlt).ne hij
    · rfl
    · exfalso
      exact ((IsHofstadterSeq_lt_iff_lt ha hj.1 hi.1).2 hgt).ne hij.symm
  have hcard : ((Finset.Icc 1 m).image a).card = m := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  calc m = ((Finset.Icc 1 m).image a).card := hcard.symm
    _ ≤ (posPrefixDiffs a m).card := Finset.card_le_card (image_Icc_subset_posPrefixDiffs a m)

/-- Every suffix difference `prefixSum a m - prefixSum a i` of length at least `2` (`i + 2 ≤ m`)
strictly exceeds `a m`. -/
theorem suffixDiff_gt_last_term :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m i : ℕ), i + 2 ≤ m →
      a m < prefixSum a m - prefixSum a i := by
  intro a ha m i him
  rw [prefixSum_sub_prefixSum a (by omega)]
  exact IsHofstadterSeq_blockSum_gt_right_endpoint ha (by omega) (by omega)

/-- The unit-length slice `{a 1, ..., a m}` and the long suffix-difference slice
`{prefixSum a m - prefixSum a i : 0 ≤ i < m - 1}` are completely disjoint. -/
theorem disjoint_image_Icc_and_longSuffixDiffs :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m : ℕ),
      Disjoint ((Finset.Icc 1 m).image a)
        ((Finset.range (m - 1)).image (fun i => prefixSum a m - prefixSum a i)) := by
  intro a ha m
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases Finset.mem_image.1 hx1 with ⟨k, hk, rfl⟩
  rcases Finset.mem_image.1 hx2 with ⟨i, hi, heq⟩
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_range] at hi
  have hle : a k ≤ a m := IsHofstadterSeq_mono_of_ge_one ha hk.1 hk.2
  have hgt : a m < prefixSum a m - prefixSum a i := suffixDiff_gt_last_term a ha m i (by omega)
  omega

/-- Disjoint-slice linear lower bound: for every `m ≥ 1`,
`2 * m - 1 ≤ (posPrefixDiffs a m).card`. -/
theorem card_posPrefixDiffs_ge_two_mul_sub_one :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m : ℕ), 1 ≤ m →
      2 * m - 1 ≤ (posPrefixDiffs a m).card := by
  intro a ha m hm
  set A := (Finset.Icc 1 m).image a
  set B := (Finset.range (m - 1)).image (fun i => prefixSum a m - prefixSum a i)
  have hA_sub : A ⊆ posPrefixDiffs a m := image_Icc_subset_posPrefixDiffs a m
  have hB_sub : B ⊆ posPrefixDiffs a m := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    exact mem_posPrefixDiffs_of_lt a m i m (by omega) le_rfl
  have hAB_sub : A ∪ B ⊆ posPrefixDiffs a m := Finset.union_subset hA_sub hB_sub
  have hdisj : Disjoint A B := disjoint_image_Icc_and_longSuffixDiffs a ha m
  have hinjA : Set.InjOn a (Finset.Icc 1 m) := by
    intro i hi j hj hij
    rw [Finset.coe_Icc, Set.mem_Icc] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exfalso; exact ((IsHofstadterSeq_lt_iff_lt ha hi.1 hj.1).2 hlt).ne hij
    · rfl
    · exfalso; exact ((IsHofstadterSeq_lt_iff_lt ha hj.1 hi.1).2 hgt).ne hij.symm
  have hinjB : Set.InjOn (fun i => prefixSum a m - prefixSum a i) (Finset.range (m - 1)) := by
    intro i hi j hj hij
    dsimp only at hij
    rw [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exfalso
      have := prefixSum_sub_strictAnti_left a ha i j m hlt (by omega)
      omega
    · rfl
    · exfalso
      have := prefixSum_sub_strictAnti_left a ha j i m hgt (by omega)
      omega
  have hcardA : A.card = m := by
    rw [Finset.card_image_of_injOn hinjA, Nat.card_Icc]
    omega
  have hcardB : B.card = m - 1 := by
    rw [Finset.card_image_of_injOn hinjB, Finset.card_range]
  have hle := Finset.card_le_card hAB_sub
  rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB] at hle
  omega

/-- Whenever `prefixSum a m ≤ a N` (`1 ≤ m`, `1 ≤ N`), the disjoint-slice bound forces
`2 * m - 1 ≤ N`. -/
theorem two_mul_sub_one_le_of_prefixSum_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      prefixSum a m ≤ a N → 2 * m - 1 ≤ N := by
  intro a ha m N hm hN hP
  exact le_trans (card_posPrefixDiffs_ge_two_mul_sub_one a ha m hm)
    (IsHofstadterSeq_card_posPrefixDiffs_le ha hN hP)

/-- The finset of upper-triangular index pairs `(i, j)` with `0 ≤ i < j ≤ m`. -/
def upperPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Iic m ×ˢ Finset.Iic m).filter (fun p : ℕ × ℕ => p.1 < p.2)

/-- The prefix-difference evaluation map `(i, j) ↦ prefixSum a j - prefixSum a i`. -/
def prefixDiffMap (a : ℕ → ℕ) (p : ℕ × ℕ) : ℕ :=
  prefixSum a p.2 - prefixSum a p.1

/-- The collision fiber of a difference value `v` inside `upperPairs m`. -/
def diffFiber (a : ℕ → ℕ) (m v : ℕ) : Finset (ℕ × ℕ) :=
  (upperPairs m).filter (fun p : ℕ × ℕ => prefixDiffMap a p = v)

/-- Left-endpoint fiber injectivity: no two distinct pairs in `diffFiber a m v` share the
same first coordinate `p.1`. -/
theorem diffFiber_fst_injOn :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m v : ℕ),
      Set.InjOn Prod.fst (diffFiber a m v : Set (ℕ × ℕ)) := by
  intro a ha m v p₁ hp₁ p₂ hp₂ hfst
  rw [Finset.mem_coe, diffFiber, Finset.mem_filter, upperPairs, Finset.mem_filter] at hp₁ hp₂
  rcases hp₁ with ⟨⟨_, hp₁_lt⟩, hp₁_eq⟩
  rcases hp₂ with ⟨⟨_, hp₂_lt⟩, hp₂_eq⟩
  unfold prefixDiffMap at hp₁_eq hp₂_eq
  change p₁.1 = p₂.1 at hfst
  have hsnd : p₁.2 = p₂.2 := by
    rcases lt_trichotomy p₁.2 p₂.2 with hlt | heq | hgt
    · exfalso
      have hmono := prefixSum_sub_strictMono_right a ha p₁.1 p₁.2 p₂.2 (by omega) hlt
      rw [hfst] at hp₁_eq hmono
      omega
    · exact heq
    · exfalso
      have hmono := prefixSum_sub_strictMono_right a ha p₁.1 p₂.2 p₁.2 (by omega) hgt
      rw [hfst] at hp₁_eq hmono
      omega
  exact Prod.ext hfst hsnd

/-- Right-endpoint fiber injectivity: no two distinct pairs in `diffFiber a m v` share the
same second coordinate `p.2`. -/
theorem diffFiber_snd_injOn :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m v : ℕ),
      Set.InjOn Prod.snd (diffFiber a m v : Set (ℕ × ℕ)) := by
  intro a ha m v p₁ hp₁ p₂ hp₂ hsnd
  rw [Finset.mem_coe, diffFiber, Finset.mem_filter, upperPairs, Finset.mem_filter] at hp₁ hp₂
  rcases hp₁ with ⟨⟨_, hp₁_lt⟩, hp₁_eq⟩
  rcases hp₂ with ⟨⟨_, hp₂_lt⟩, hp₂_eq⟩
  unfold prefixDiffMap at hp₁_eq hp₂_eq
  change p₁.2 = p₂.2 at hsnd
  have hfst : p₁.1 = p₂.1 := by
    rcases lt_trichotomy p₁.1 p₂.1 with hlt | heq | hgt
    · exfalso
      have hanti := prefixSum_sub_strictAnti_left a ha p₁.1 p₂.1 p₁.2 hlt (by omega)
      rw [hsnd] at hp₁_eq hanti
      omega
    · exact heq
    · exfalso
      have hanti := prefixSum_sub_strictAnti_left a ha p₂.1 p₁.1 p₁.2 hgt (by omega)
      rw [hsnd] at hp₁_eq hanti
      omega
  exact Prod.ext hfst hsnd

/-- Block-length fiber injectivity: by strict convexity of `prefixSum a`, no two distinct pairs
in `diffFiber a m v` can have the same block length `p.2 - p.1`. -/
theorem diffFiber_length_injOn :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m v : ℕ),
      Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (diffFiber a m v : Set (ℕ × ℕ)) := by
  intro a ha m v p₁ hp₁ p₂ hp₂ hlen
  rw [Finset.mem_coe, diffFiber, Finset.mem_filter, upperPairs, Finset.mem_filter] at hp₁ hp₂
  rcases hp₁ with ⟨⟨_, hp₁_lt⟩, hp₁_eq⟩
  rcases hp₂ with ⟨⟨_, hp₂_lt⟩, hp₂_eq⟩
  unfold prefixDiffMap at hp₁_eq hp₂_eq
  dsimp only at hlen
  set d := p₁.2 - p₁.1
  have hd1 : 1 ≤ d := by omega
  have hp₁_snd : p₁.2 = p₁.1 + d := by omega
  have hp₂_snd : p₂.2 = p₂.1 + d := by omega
  have hcomb : prefixSum a (p₁.1 + d) - prefixSum a p₁.1 =
      prefixSum a (p₂.1 + d) - prefixSum a p₂.1 := by
    rw [← hp₁_snd, ← hp₂_snd, hp₁_eq, hp₂_eq]
  have hfst : p₁.1 = p₂.1 := prefixSum_fixed_length_inj a ha d p₁.1 p₂.1 hd1 hcomb
  exact Prod.ext hfst (by omega)

/-- Finite-window collision-multiplicity lower bound: if every difference fiber in `posPrefixDiffs a m`
has size at most `B`, then `(upperPairs m).card ≤ B * (posPrefixDiffs a m).card`. -/
theorem card_upperPairs_le_mul_card_posPrefixDiffs :
    ∀ (a : ℕ → ℕ) (m B : ℕ),
      (∀ v ∈ posPrefixDiffs a m, (diffFiber a m v).card ≤ B) →
      (upperPairs m).card ≤ B * (posPrefixDiffs a m).card := by
  intro a m B hB
  change (upperPairs m).card ≤ B * ((upperPairs m).image (prefixDiffMap a)).card
  exact Finset.card_le_mul_card_image (upperPairs m) B hB

/-- Bolan–Tang collision-multiplicity bridge: whenever `prefixSum a m ≤ a N` (`1 ≤ N`) and
all difference fibers at horizon `m` have multiplicity at most `B`,
`(upperPairs m).card ≤ B * N`. -/
theorem card_upperPairs_le_mul_of_prefixSum_le :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (m N B : ℕ), 1 ≤ N →
      prefixSum a m ≤ a N →
      (∀ v ∈ posPrefixDiffs a m, (diffFiber a m v).card ≤ B) →
      (upperPairs m).card ≤ B * N := by
  intro a ha m N B hN hP hB
  calc (upperPairs m).card
      ≤ B * (posPrefixDiffs a m).card := card_upperPairs_le_mul_card_posPrefixDiffs a m B hB
    _ ≤ B * N := Nat.mul_le_mul_left B (IsHofstadterSeq_card_posPrefixDiffs_le ha hN hP)

/-- Because `a n - n` is nondecreasing (`erdos_423_variants_nondecreasing`), eventual threshold
exceedance `∀ᶠ n in atTop, M + n ≤ a n` is equivalent to a single witness `∃ n ≥ 1, M + n ≤ a n`. -/
theorem eventually_add_le_iff_exists_ge_one :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a → ∀ (M : ℕ),
      (∀ᶠ n in atTop, M + n ≤ a n) ↔ ∃ n : ℕ, 1 ≤ n ∧ M + n ≤ a n := by
  intro a ha M
  rw [Filter.eventually_atTop]
  constructor
  · rintro ⟨n₀, hn₀⟩
    exact ⟨max n₀ 1, le_max_right n₀ 1, hn₀ (max n₀ 1) (le_max_left n₀ 1)⟩
  · rintro ⟨n₀, hn₀1, hn₀M⟩
    refine ⟨n₀, fun n hn => ?_⟩
    have hmono := erdos_423_variants_nondecreasing a ha n₀ n hn₀1 hn
    have hle : n ≤ a n := IsHofstadterSeq_le_apply ha n (by omega)
    omega

/-- Pointwise-witness reduction for `erdos_423.variants.infinite_complement`: if for every `M`
there exists a single index `n ≥ 1` with `M + n ≤ a n`, then `(Set.range a)ᶜ` is infinite. -/
theorem infinite_compl_of_forall_exists_excess :
    ∀ (a : ℕ → ℕ), IsHofstadterSeq a →
      (∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M + n ≤ a n) → Set.Infinite (Set.range a)ᶜ := by
  intro a ha hex
  apply IsHofstadterSeq_infinite_compl_of_unbounded ha
  intro M
  exact (eventually_add_le_iff_exists_ge_one a ha M).2 (hex M)

end Erdos423

end
