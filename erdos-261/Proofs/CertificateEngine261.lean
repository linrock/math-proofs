module

/-
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

public import Definitions261
public import CertificateData261

@[expose] public section

/-!
# Erdős Problem 261: Coalesced Dyadic Block Certificate Engine and Proof of `le_10000`

This module proves the soundness of the pure-kernel certificate verifier in
`CertificateCore261` (`wSpec`, `w64`, `stepVar`, `runB64`, `evalState`,
`checkForestStates`, `mergeAllLists`, `checkSeq`) and combines it with the
kernel-checked certificate theorems in `CertificateData261` to prove
`erdos_261.variants.le_10000` ($\forall 1 \le n \le 10000,\; \text{Erdos261Prop } n$).
-/

open scoped BigOperators

namespace Erdos261

/-- `HasFinsetRep i v` holds if there exists a non-empty finite set $S \subseteq [i, \infty)$
whose dyadic sum $\sum_{a \in S} a / 2^a$ equals $v / 2^{i-1}$. -/
def HasFinsetRep (i v : ℕ) : Prop :=
  ∃ S : Finset ℕ,
    S.Nonempty ∧
    (∀ a ∈ S, i ≤ a) ∧
    (v : ℚ) / (2 ^ (i - 1) : ℚ) = ∑ a ∈ S, dyadicTerm a

/-- For every $b, i, M$ with $1 \le i$ and $M < 2^b$, there exists a finite subset
$S \subseteq [i, i + b)$ whose dyadic sum is $(i \cdot M + \text{wSpec } b\; M) / 2^{i + b - 1}$. -/
theorem wSpec_block_exists : ∀ (b i M : ℕ), 1 ≤ i → M < 2 ^ b →
    ∃ S : Finset ℕ,
      (∀ a ∈ S, i ≤ a ∧ a < i + b) ∧
      ∑ a ∈ S, dyadicTerm a = ((i * M + wSpec b M : ℕ) : ℚ) / (2 ^ (i + b - 1) : ℚ)
  | 0, _, M, _, hM => by
    have hM0 : M = 0 := by omega
    subst hM0
    exact ⟨∅, by simp, by simp [wSpec]⟩
  | b + 1, i, M, hi, hM => by
    have h_div : M / 2 < 2 ^ b := by rw [pow_succ] at hM; omega
    obtain ⟨S', hS'_bounds, hS'_sum⟩ := wSpec_block_exists b i (M / 2) hi h_div
    have h_not_mem : i + b ∉ S' := fun h => by have := (hS'_bounds _ h).2; omega
    have h_div_mod : i * M = i * (2 * (M / 2) + M % 2) :=
      congrArg (i * ·) (Nat.div_add_mod M 2).symm
    have h_exp : i + (b + 1) - 1 = (i + b - 1) + 1 := by omega
    have h_wSpec : wSpec (b + 1) M = 2 * wSpec b (M / 2) + b * (M % 2) := rfl
    by_cases hmod : M % 2 = 0
    · refine ⟨S', fun a ha => ⟨(hS'_bounds a ha).1, by have := (hS'_bounds a ha).2; omega⟩, ?_⟩
      rw [hS'_sum, h_exp, pow_succ (2 : ℚ) (i + b - 1)]
      have h_num : i * M + wSpec (b + 1) M = 2 * (i * (M / 2) + wSpec b (M / 2)) := by
        rw [h_wSpec, h_div_mod, hmod]; ring
      have h_num_q : ((i * M + wSpec (b + 1) M : ℕ) : ℚ) =
          2 * ((i * (M / 2) + wSpec b (M / 2) : ℕ) : ℚ) := by exact_mod_cast h_num
      rw [h_num_q]
      have h2 : (2 : ℚ) ^ (i + b - 1) ≠ 0 := by positivity
      field_simp
    · have hmod1 : M % 2 = 1 := by omega
      refine ⟨insert (i + b) S', ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha'
        · omega
        · have := hS'_bounds a ha'; omega
      · rw [Finset.sum_insert h_not_mem, hS'_sum, h_exp]
        unfold dyadicTerm
        have h_exp2 : i + b = (i + b - 1) + 1 := by omega
        have hpow : (2 : ℚ) ^ (i + b) = (2 : ℚ) ^ (i + b - 1) * 2 := by
          conv_lhs => rw [h_exp2, pow_succ]
        rw [pow_succ (2 : ℚ) (i + b - 1), hpow]
        have h_num : i * M + wSpec (b + 1) M = 2 * (i * (M / 2) + wSpec b (M / 2)) + (i + b) := by
          rw [h_wSpec, h_div_mod, hmod1]; ring
        have h_num_q : ((i * M + wSpec (b + 1) M : ℕ) : ℚ) =
            2 * ((i * (M / 2) + wSpec b (M / 2) : ℕ) : ℚ) + ((i + b : ℕ) : ℚ) := by
          exact_mod_cast h_num
        rw [h_num_q]
        have h2 : (2 : ℚ) ^ (i + b - 1) ≠ 0 := by positivity
        field_simp
        ring

/-- Backward step soundness for a $b$-step block transition. -/
theorem hasFinsetRep_of_wSpec_step {b i v M : ℕ} (hi : 1 ≤ i) (hM : M < 2 ^ b)
    (hsub : i * M + wSpec b M < 2 ^ b * v)
    (hnext : HasFinsetRep (i + b) (2 ^ b * v - (i * M + wSpec b M))) :
    HasFinsetRep i v := by
  obtain ⟨S_block, hblock_bounds, hblock_sum⟩ := wSpec_block_exists b i M hi hM
  obtain ⟨S_tail, htail_ne, htail_bounds, htail_sum⟩ := hnext
  have hdisj : Disjoint S_block S_tail := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    have := (hblock_bounds a ha1).2
    have := htail_bounds a ha2
    omega
  refine ⟨S_block ∪ S_tail, htail_ne.mono Finset.subset_union_right, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with ha1 | ha2
    · exact (hblock_bounds a ha1).1
    · exact le_trans (Nat.le_add_right i b) (htail_bounds a ha2)
  · rw [Finset.sum_union hdisj, hblock_sum, ← htail_sum]
    have h_exp : i + b - 1 = (i - 1) + b := by omega
    rw [h_exp, pow_add (2 : ℚ) (i - 1) b]
    have h_nat : (i * M + wSpec b M) + (2 ^ b * v - (i * M + wSpec b M)) = 2 ^ b * v :=
      Nat.add_sub_of_le (le_of_lt hsub)
    have h_rat : ((i * M + wSpec b M : ℕ) : ℚ) + ((2 ^ b * v - (i * M + wSpec b M) : ℕ) : ℚ) =
        ((2 : ℚ) ^ b) * (v : ℚ) := by
      have : (((i * M + wSpec b M) + (2 ^ b * v - (i * M + wSpec b M)) : ℕ) : ℚ) =
          ((2 ^ b * v : ℕ) : ℚ) := congrArg Nat.cast h_nat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using this
    have h2b : (2 : ℚ) ^ b ≠ 0 := by positivity
    have h2i : (2 : ℚ) ^ (i - 1) ≠ 0 := by positivity
    rw [← add_div, h_rat]
    field_simp

/-- Terminal state soundness: if $2v = i$ and $i \ge 1$, then `{i}` represents $v / 2^{i-1}$. -/
theorem hasFinsetRep_terminal {i v : ℕ} (hi : 1 ≤ i) (hterm : 2 * v = i) :
    HasFinsetRep i v := by
  refine ⟨{i}, Finset.singleton_nonempty i, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_singleton] at ha
    omega
  · simp only [Finset.sum_singleton, dyadicTerm]
    have hi_eq : i = (i - 1) + 1 := by omega
    have hpow : (2 : ℚ) ^ i = (2 : ℚ) ^ (i - 1) * 2 := by
      conv_lhs => rw [hi_eq, pow_succ]
    have hnum : (i : ℚ) = 2 * (v : ℚ) := by exact_mod_cast hterm.symm
    rw [hpow, hnum]
    have h2 : (2 : ℚ) ^ (i - 1) ≠ 0 := by positivity
    field_simp

/-- Root soundness: for $n \ge 2$, `HasFinsetRep (n + 2) (n - 1)` implies `Erdos261Prop n`. -/
theorem erdos261Prop_of_hasFinsetRep {n : ℕ} (hn : 2 ≤ n)
    (hrep : HasFinsetRep (n + 2) (n - 1)) : Erdos261Prop n := by
  obtain ⟨S, hS_ne, hS_bounds, hS_sum⟩ := hrep
  have hn1_not_mem : n + 1 ∉ S := by
    intro hmem
    have := hS_bounds (n + 1) hmem
    omega
  let S' := insert (n + 1) S
  have hS'_card : 2 ≤ S'.card := by
    rw [Finset.card_insert_of_notMem hn1_not_mem]
    have : 1 ≤ S.card := Finset.Nonempty.card_pos hS_ne
    omega
  have hS'_pos : ∀ a ∈ S', 1 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haS
    · omega
    · have := hS_bounds a haS
      omega
  have hS'_sum : (n : ℚ) / (2 ^ n : ℚ) = ∑ a ∈ S', dyadicTerm a := by
    rw [Finset.sum_insert hn1_not_mem, ← hS_sum, dyadicTerm]
    have h_sub : n + 2 - 1 = n + 1 := rfl
    rw [h_sub, pow_succ (2 : ℚ) n]
    have h_nat : (n + 1) + (n - 1) = 2 * n := by omega
    have h_rat : ((n + 1 : ℕ) : ℚ) + ((n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) := by
      exact_mod_cast h_nat
    have h2n : (2 : ℚ) ^ n ≠ 0 := by positivity
    rw [← add_div, h_rat]
    field_simp
  let e := S'.equivFin.symm
  refine ⟨S'.card, hS'_card, fun k => (e k).val, ?_, ?_, ?_⟩
  · intro k1 k2 h
    exact e.injective (Subtype.ext h)
  · intro k
    exact hS'_pos (e k).val (e k).property
  · rw [hS'_sum]
    have hbij : ∑ k : Fin S'.card, dyadicTerm (e k).val = ∑ x : S', dyadicTerm x.val :=
      Equiv.sum_comp e (fun x : S' => dyadicTerm x.val)
    have hcoe : ∑ x : S', dyadicTerm x.val = ∑ a ∈ S', dyadicTerm a :=
      Finset.sum_coe_sort S' dyadicTerm
    exact (hbij.trans hcoe).symm

/-- Base case $n = 1$: $1/2^1 = 3/2^3 + 6/2^6 + 8/2^8$. -/
theorem erdos261Prop_one : Erdos261Prop 1 := by
  let a : Fin 3 → ℕ := ![3, 6, 8]
  refine ⟨3, by decide, a, ?_, ?_, ?_⟩
  · decide
  · intro k
    fin_cases k <;> decide
  · simp only [Fin.sum_univ_three, a, Matrix.cons_val_zero, Matrix.cons_val_one]
    change (1 : ℚ) / 2 ^ 1 = (3 : ℚ) / 2 ^ 3 + (6 : ℚ) / 2 ^ 6 + (8 : ℚ) / 2 ^ 8
    norm_num

/-!
## Bit-Parallel SWAR Identity `(w64 (M <<< (64 - b))) >>> (64 - b) = wSpec b M`
-/

theorem div_two_pow_succ (M d : ℕ) : (M / 2) / 2 ^ d = M / 2 ^ (d + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm 2 (2 ^ d), ← Nat.pow_succ]

theorem mod_two_pow_succ (M d : ℕ) :
    2 * ((M / 2) % 2 ^ d) + M % 2 = M % 2 ^ (d + 1) := by
  have h1 := Nat.div_add_mod M 2
  have h2 := Nat.div_add_mod (M / 2) (2 ^ d)
  have h3 := Nat.div_add_mod M (2 ^ (d + 1))
  rw [div_two_pow_succ] at h2
  have h12 : 2 ^ (d + 1) * (M / 2 ^ (d + 1)) + (2 * ((M / 2) % 2 ^ d) + M % 2) = M := by
    calc 2 ^ (d + 1) * (M / 2 ^ (d + 1)) + (2 * ((M / 2) % 2 ^ d) + M % 2)
      _ = 2 * (2 ^ d * (M / 2 ^ (d + 1)) + (M / 2) % 2 ^ d) + M % 2 := by rw [Nat.pow_succ]; ring
      _ = 2 * (M / 2) + M % 2 := by rw [h2]
      _ = M := h1
  omega

theorem wSpec_add (b : ℕ) : ∀ (d M : ℕ),
    wSpec (b + d) M = 2 ^ d * wSpec b (M / 2 ^ d) + b * (M % 2 ^ d) + wSpec d (M % 2 ^ d)
  | 0, M => by simp [wSpec, Nat.mod_one]
  | d + 1, M => by
    rw [← Nat.add_assoc]
    have h_step : wSpec (b + d + 1) M = 2 * wSpec (b + d) (M / 2) + (b + d) * (M % 2) := rfl
    have h_d : wSpec (d + 1) (M % 2 ^ (d + 1)) =
        2 * wSpec d ((M % 2 ^ (d + 1)) / 2) + d * ((M % 2 ^ (d + 1)) % 2) := rfl
    have h_mod_div : (M % 2 ^ (d + 1)) / 2 = (M / 2) % 2 ^ d := by
      have hm := (mod_two_pow_succ M d).symm
      have h5 : M % 2 < 2 := Nat.mod_lt M (by decide)
      omega
    have h_mod_mod : (M % 2 ^ (d + 1)) % 2 = M % 2 := by
      have hm := (mod_two_pow_succ M d).symm
      omega
    rw [h_step, wSpec_add b d (M / 2), h_d, h_mod_div, h_mod_mod, div_two_pow_succ,
        ← mod_two_pow_succ M d, Nat.pow_succ]
    ring

theorem wSpec_mul_two (b M : ℕ) : wSpec (b + 1) (2 * M) = 2 * wSpec b M := by
  simp [wSpec]

theorem wSpec_shiftLeft (b M : ℕ) : ∀ sh : ℕ,
    wSpec (b + sh) (M <<< sh) = (wSpec b M) <<< sh
  | 0 => by simp
  | sh + 1 => by
    have hsh : M <<< (sh + 1) = 2 * (M <<< sh) := by
      simp only [Nat.shiftLeft_eq, pow_succ]; ring
    have hsh2 : (wSpec b M) <<< (sh + 1) = 2 * ((wSpec b M) <<< sh) := by
      simp only [Nat.shiftLeft_eq, pow_succ]; ring
    rw [← Nat.add_assoc, hsh, wSpec_mul_two, wSpec_shiftLeft b M sh, hsh2]

theorem and_div_two_pow (x y B : ℕ) : (x &&& y) / 2 ^ B = (x / 2 ^ B) &&& (y / 2 ^ B) := by
  simp only [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib]

theorem and_mod_two_pow (x y B : ℕ) : (x &&& y) % 2 ^ B = (x % 2 ^ B) &&& (y % 2 ^ B) := by
  simp only [← Nat.and_two_pow_sub_one_eq_mod]
  ac_rfl

theorem and_decomp_two_pow (B x y : ℕ) :
    x &&& y = 2 ^ B * ((x / 2 ^ B) &&& (y / 2 ^ B)) + ((x % 2 ^ B) &&& (y % 2 ^ B)) := by
  rw [← and_div_two_pow, ← and_mod_two_pow, Nat.div_add_mod]

theorem checkW8_sound : ∀ n m, checkW8 n = true → m < n → w8Swar m = wSpec 8 m
  | 0, _, _, hm => by omega
  | n + 1, m, h, hm => by
    simp only [checkW8, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
    · exact checkW8_sound n m h.2 hlt
    · exact h.1

theorem w8Swar_eq_wSpec8 {M : ℕ} (hM : M < 256) : w8Swar M = wSpec 8 M :=
  checkW8_sound 256 M checkW8_256 hM

theorem w16Swar_decomp (M : ℕ) :
    w16Swar M = 256 * w8Swar (M / 256) + 8 * (M % 256) + w8Swar (M % 256) := by
  unfold w16Swar w8Swar
  rw [and_decomp_two_pow 8 M 0x00FF, and_decomp_two_pow 8 M 0x0F0F,
      and_decomp_two_pow 8 M 0x3333, and_decomp_two_pow 8 M 0x5555]
  have h0 : (M / 2 ^ 8) &&& (0x00FF / 2 ^ 8) = 0 := Nat.and_zero _
  have h1 : (M % 2 ^ 8) &&& (0x00FF % 2 ^ 8) = M % 256 := by
    change (M % 256) &&& (2 ^ 8 - 1) = M % 256
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  change 8 * (256 * ((M / 2 ^ 8) &&& (0x00FF / 2 ^ 8)) + ((M % 2 ^ 8) &&& (0x00FF % 2 ^ 8))) +
    4 * (256 * ((M / 256) &&& 0x0F) + ((M % 256) &&& 0x0F)) +
    2 * (256 * ((M / 256) &&& 0x33) + ((M % 256) &&& 0x33)) +
    (256 * ((M / 256) &&& 0x55) + ((M % 256) &&& 0x55)) = _
  rw [h0, h1]; ring

theorem w32Swar_decomp (M : ℕ) :
    w32Swar M = 65536 * w16Swar (M / 65536) + 16 * (M % 65536) + w16Swar (M % 65536) := by
  unfold w32Swar w16Swar
  rw [and_decomp_two_pow 16 M 0x0000FFFF, and_decomp_two_pow 16 M 0x00FF00FF,
      and_decomp_two_pow 16 M 0x0F0F0F0F, and_decomp_two_pow 16 M 0x33333333,
      and_decomp_two_pow 16 M 0x55555555]
  have h0 : (M / 2 ^ 16) &&& (0x0000FFFF / 2 ^ 16) = 0 := Nat.and_zero _
  have h1 : (M % 2 ^ 16) &&& (0x0000FFFF % 2 ^ 16) = M % 65536 := by
    change (M % 65536) &&& (2 ^ 16 - 1) = M % 65536
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  change 16 * (65536 * ((M / 2 ^ 16) &&& (0x0000FFFF / 2 ^ 16)) + ((M % 2 ^ 16) &&& (0x0000FFFF % 2 ^ 16))) +
    8 * (65536 * ((M / 65536) &&& 0x00FF) + ((M % 65536) &&& 0x00FF)) +
    4 * (65536 * ((M / 65536) &&& 0x0F0F) + ((M % 65536) &&& 0x0F0F)) +
    2 * (65536 * ((M / 65536) &&& 0x3333) + ((M % 65536) &&& 0x3333)) +
    (65536 * ((M / 65536) &&& 0x5555) + ((M % 65536) &&& 0x5555)) = _
  rw [h0, h1]; ring

theorem w64_decomp (M : ℕ) :
    w64 M = 4294967296 * w32Swar (M / 4294967296) + 32 * (M % 4294967296) + w32Swar (M % 4294967296) := by
  unfold w64 w32Swar
  rw [and_decomp_two_pow 32 M 0x00000000FFFFFFFF, and_decomp_two_pow 32 M 0x0000FFFF0000FFFF,
      and_decomp_two_pow 32 M 0x00FF00FF00FF00FF, and_decomp_two_pow 32 M 0x0F0F0F0F0F0F0F0F,
      and_decomp_two_pow 32 M 0x3333333333333333, and_decomp_two_pow 32 M 0x5555555555555555]
  have h0 : (M / 2 ^ 32) &&& (0x00000000FFFFFFFF / 2 ^ 32) = 0 := Nat.and_zero _
  have h1 : (M % 2 ^ 32) &&& (0x00000000FFFFFFFF % 2 ^ 32) = M % 4294967296 := by
    change (M % 4294967296) &&& (2 ^ 32 - 1) = M % 4294967296
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  change 32 * (4294967296 * ((M / 2 ^ 32) &&& (0x00000000FFFFFFFF / 2 ^ 32)) +
      ((M % 2 ^ 32) &&& (0x00000000FFFFFFFF % 2 ^ 32))) +
    16 * (4294967296 * ((M / 4294967296) &&& 0x0000FFFF) + ((M % 4294967296) &&& 0x0000FFFF)) +
    8 * (4294967296 * ((M / 4294967296) &&& 0x00FF00FF) + ((M % 4294967296) &&& 0x00FF00FF)) +
    4 * (4294967296 * ((M / 4294967296) &&& 0x0F0F0F0F) + ((M % 4294967296) &&& 0x0F0F0F0F)) +
    2 * (4294967296 * ((M / 4294967296) &&& 0x33333333) + ((M % 4294967296) &&& 0x33333333)) +
    1 * (4294967296 * ((M / 4294967296) &&& 0x55555555) + ((M % 4294967296) &&& 0x55555555)) = _
  rw [h0, h1]; ring

theorem w16Swar_eq_wSpec16 {M : ℕ} (hM : M < 65536) : w16Swar M = wSpec 16 M := by
  have h1 : M / 256 < 256 := by omega
  have h2 : M % 256 < 256 := by omega
  have hadd := wSpec_add 8 8 M
  rw [w16Swar_decomp, w8Swar_eq_wSpec8 h1, w8Swar_eq_wSpec8 h2]
  simpa using hadd.symm

theorem w32Swar_eq_wSpec32 {M : ℕ} (hM : M < 4294967296) : w32Swar M = wSpec 32 M := by
  have h1 : M / 65536 < 65536 := by omega
  have h2 : M % 65536 < 65536 := by omega
  have hadd := wSpec_add 16 16 M
  rw [w32Swar_decomp, w16Swar_eq_wSpec16 h1, w16Swar_eq_wSpec16 h2]
  simpa using hadd.symm

theorem w64_eq_wSpec64 {M : ℕ} (hM : M < 18446744073709551616) : w64 M = wSpec 64 M := by
  have h1 : M / 4294967296 < 4294967296 := by omega
  have h2 : M % 4294967296 < 4294967296 := by omega
  have hadd := wSpec_add 32 32 M
  rw [w64_decomp, w32Swar_eq_wSpec32 h1, w32Swar_eq_wSpec32 h2]
  simpa using hadd.symm

theorem w64_shift_eq_wSpec {b M : ℕ} (hb : b ≤ 64) (hM : M < 2 ^ b) :
    (w64 (M <<< (64 - b))) >>> (64 - b) = wSpec b M := by
  have hlt : M <<< (64 - b) < 18446744073709551616 := by
    rw [Nat.shiftLeft_eq]
    have h64 : (18446744073709551616 : ℕ) = 2 ^ b * 2 ^ (64 - b) := by
      rw [← pow_add, Nat.add_sub_of_le hb]
      rfl
    rw [h64]
    exact Nat.mul_lt_mul_of_pos_right hM (by positivity)
  rw [w64_eq_wSpec64 hlt]
  set sh := 64 - b
  have h64_eq : (64 : ℕ) = b + sh := by omega
  rw [h64_eq, wSpec_shiftLeft b M sh]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  exact Nat.mul_div_cancel _ (by positivity)

/-!
## Soundness of `stepVar`, `runB64`, and `MergeTree`
-/

def ValidStepFn (f : ℕ → ℕ → Option (ℕ × ℕ)) : Prop :=
  ∀ i v i' v', 1 ≤ i → f i v = some (i', v') →
    1 ≤ i' ∧ (HasFinsetRep i' v' → HasFinsetRep i v)

theorem validStepFn_stepVar (b M : ℕ) : ValidStepFn (stepVar b M) := by
  intro i v i' v' hi h
  dsimp only [stepVar] at h
  split_ifs at h with hb0 hcond hsub
  · injection h with hpair; injection hpair with hi' hv'; subst hi' hv'
    exact ⟨hi, id⟩
  · injection h with hpair; injection hpair with hi' hv'; subst hi' hv'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have h1b : 1 <<< b = 2 ^ b := by simp [Nat.shiftLeft_eq]
    have hM : M < 2 ^ b := by simpa [h1b] using hcond.2
    have hw : (w64 (M <<< (64 - b))) >>> (64 - b) = wSpec b M :=
      w64_shift_eq_wSpec hcond.1 hM
    have hvb : v <<< b = 2 ^ b * v := by rw [Nat.shiftLeft_eq, Nat.mul_comm]
    refine ⟨by omega, fun hnext => ?_⟩
    exact hasFinsetRep_of_wSpec_step hi hM (by simpa [hw, hvb] using hsub)
      (by simpa [hw, hvb] using hnext)

theorem validStepFn_runB64 : ∀ (ms : List ℕ) (b M : ℕ), ValidStepFn (runB64 ms b M)
  | [], b, M => validStepFn_stepVar b M
  | M64 :: ms, b, M => by
    intro i v i'' v'' hi h
    dsimp only [runB64] at h
    cases h64 : stepVar 64 M64 i v with
    | none => rw [h64] at h; contradiction
    | some p =>
      rcases p with ⟨i', v'⟩
      rw [h64] at h
      obtain ⟨hi', hback1⟩ := validStepFn_stepVar 64 M64 i v i' v' hi h64
      obtain ⟨hi'', hback2⟩ := validStepFn_runB64 ms b M i' v' i'' v'' hi' h
      exact ⟨hi'', fun hrep => hback1 (hback2 hrep)⟩

theorem evalState_sound : ∀ (t : MergeTree) (i v : ℕ),
    evalState t = some (i, v) →
    1 ≤ i ∧ (HasFinsetRep i v →
      ∀ acc l, l ∈ treeToLists t acc → l ∈ acc ∨ ∀ n ∈ l, 2 ≤ n ∧ HasFinsetRep (n + 2) (n - 1))
  | .leaf n b64 b M, i, v, h => by
    dsimp only [evalState] at h
    split_ifs at h with hn
    obtain ⟨hi, hback⟩ := validStepFn_runB64 b64 b M (n + 2) (n - 1) i v (by omega) h
    refine ⟨hi, fun hrep acc l hl => ?_⟩
    dsimp only [treeToLists] at hl
    split_ifs at hl
    rcases List.mem_cons.mp hl with rfl | hacc
    · right
      intro m hm
      simp only [List.mem_singleton] at hm
      subst hm
      exact ⟨hn, hback hrep⟩
    · left; exact hacc
  | .merge l r b64 b M, i, v, h => by
    dsimp only [evalState] at h
    cases hl_eq : evalState l with
    | none => rw [hl_eq] at h; contradiction
    | some p1 =>
      rcases p1 with ⟨i1, v1⟩
      cases hr_eq : evalState r with
      | none => rw [hl_eq, hr_eq] at h; contradiction
      | some p2 =>
        rcases p2 with ⟨i2, v2⟩
        rw [hl_eq, hr_eq] at h
        dsimp only at h
        split_ifs at h with heq
        simp only [Bool.and_eq_true, beq_iff_eq] at heq
        rcases heq with ⟨rfl, rfl⟩
        obtain ⟨hi1, hback_l⟩ := evalState_sound l i1 v1 hl_eq
        obtain ⟨_, hback_r⟩ := evalState_sound r i1 v1 hr_eq
        obtain ⟨hi, hback_seg⟩ := validStepFn_runB64 b64 b M i1 v1 i v hi1 h
        refine ⟨hi, fun hrep acc lst hlst => ?_⟩
        have hrep1 : HasFinsetRep i1 v1 := hback_seg hrep
        dsimp only [treeToLists] at hlst
        rcases hback_l hrep1 (treeToLists r acc) lst hlst with h_in_r | h_valid
        · exact hback_r hrep1 acc lst h_in_r
        · right; exact h_valid

theorem checkForestStates_sound : ∀ (fs : List MergeTree) (acc : List (List ℕ)),
    checkForestStates fs = true →
    (∀ l ∈ acc, ∀ n ∈ l, 2 ≤ n ∧ HasFinsetRep (n + 2) (n - 1)) →
    ∀ l ∈ forestToLists fs acc, ∀ n ∈ l, 2 ≤ n ∧ HasFinsetRep (n + 2) (n - 1)
  | [], acc, _, hacc => hacc
  | t :: ts, acc, h, hacc => by
    dsimp only [checkForestStates] at h
    cases ht : evalState t with
    | none => rw [ht] at h; contradiction
    | some p =>
      rcases p with ⟨i, v⟩
      rw [ht] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hi, hback_t⟩ := evalState_sound t i v ht
      have hrep_root : HasFinsetRep i v := hasFinsetRep_terminal hi h.1
      have hts := checkForestStates_sound ts acc h.2 hacc
      intro l hl
      dsimp only [forestToLists] at hl
      rcases hback_t hrep_root (forestToLists ts acc) l hl with h_in_ts | h_valid
      · exact hts l h_in_ts
      · exact h_valid

theorem mem_mergeSorted : ∀ (fuel : ℕ) (xs ys : List ℕ) (a : ℕ),
    a ∈ mergeSorted fuel xs ys → a ∈ xs ∨ a ∈ ys
  | 0, xs, _, _, h => Or.inl h
  | _ + 1, [], _, _, h => Or.inr h
  | _ + 1, _ :: _, [], _, h => Or.inl h
  | fuel + 1, x :: xs, y :: ys, a, h => by
    dsimp only [mergeSorted] at h
    split_ifs at h with hle
    · rcases List.mem_cons.mp h with rfl | htail
      · exact Or.inl List.mem_cons_self
      · rcases mem_mergeSorted fuel xs (y :: ys) a htail with hx | hy
        · exact Or.inl (List.mem_cons_of_mem x hx)
        · exact Or.inr hy
    · rcases List.mem_cons.mp h with rfl | htail
      · exact Or.inr List.mem_cons_self
      · rcases mem_mergeSorted fuel (x :: xs) ys a htail with hx | hy
        · exact Or.inl hx
        · exact Or.inr (List.mem_cons_of_mem y hy)

theorem mergeListPairs_sound (P : ℕ → Prop) : ∀ (fuel : ℕ) (ls : List (List ℕ)),
    (∀ l ∈ ls, ∀ n ∈ l, P n) →
    ∀ l ∈ mergeListPairs fuel ls, ∀ n ∈ l, P n
  | _, [], _, _, hl => by contradiction
  | _, [_], h, l, hl => h l hl
  | fuel, l1 :: l2 :: ls, h, l, hl => by
    dsimp only [mergeListPairs] at hl
    rcases List.mem_cons.mp hl with rfl | htail
    · intro n hn
      rcases mem_mergeSorted fuel l1 l2 n hn with h1 | h2
      · exact h l1 List.mem_cons_self n h1
      · exact h l2 (List.mem_cons_of_mem l1 List.mem_cons_self) n h2
    · exact mergeListPairs_sound P fuel ls
        (fun l' hl' => h l' (List.mem_cons_of_mem l1 (List.mem_cons_of_mem l2 hl'))) l htail

theorem mergeAllLists_sound (P : ℕ → Prop) : ∀ (d w : ℕ) (ls : List (List ℕ)),
    (∀ l ∈ ls, ∀ n ∈ l, P n) →
    ∀ n ∈ mergeAllLists d w ls, P n
  | 0, _, [], _, _, hn => by contradiction
  | 0, _, l :: _, h, n, hn => h l List.mem_cons_self n hn
  | _ + 1, _, [], _, _, hn => by contradiction
  | _ + 1, _, [l], h, n, hn => h l List.mem_cons_self n hn
  | d + 1, w, l1 :: l2 :: ls, h, n, hn => by
    dsimp only [mergeAllLists] at hn
    exact mergeAllLists_sound P d (2 * w) (mergeListPairs (2 * w) (l1 :: l2 :: ls))
      (mergeListPairs_sound P (2 * w) (l1 :: l2 :: ls) h) n hn

theorem checkSeq_sound : ∀ (lo count : ℕ) (ms : List ℕ) (n : ℕ),
    checkSeq lo count ms = true →
    lo ≤ n → n < lo + count → n ∈ ms
  | _, 0, _, _, _, hlo, hhi => by omega
  | _, _ + 1, [], _, h, _, _ => by contradiction
  | lo, c + 1, m :: ms, n, h, hlo, hhi => by
    dsimp only [checkSeq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, hrest⟩
    by_cases heq : n = m
    · subst heq; exact List.mem_cons_self
    · exact List.mem_cons_of_mem m (checkSeq_sound (m + 1) c ms n hrest (by omega) (by omega))

/-- Master certificate bridge: if `f0..f3` pass `checkForestStates` and `checkSeq 2 9999`,
then every integer $1 \le n \le 10000$ satisfies `Erdos261Prop n`. -/
theorem erdos261Prop_of_certificates (f0 f1 f2 f3 : List MergeTree)
    (hf0 : checkForestStates f0 = true)
    (hf1 : checkForestStates f1 = true)
    (hf2 : checkForestStates f2 = true)
    (hf3 : checkForestStates f3 = true)
    (hseq : checkSeq 2 9999
      (mergeAllLists 14 1
        (forestToLists f0
          (forestToLists f1
            (forestToLists f2
              (forestToLists f3 []))))) = true)
    {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    Erdos261Prop n := by
  by_cases hn1 : n = 1
  · subst hn1; exact erdos261Prop_one
  · have hn2 : 2 ≤ n := by omega
    have hlt : n < 2 + 9999 := by omega
    have hmem : n ∈ mergeAllLists 14 1
        (forestToLists f0 (forestToLists f1 (forestToLists f2 (forestToLists f3 [])))) :=
      checkSeq_sound 2 9999 _ n hseq hn2 hlt
    have hall : ∀ l ∈ forestToLists f0 (forestToLists f1 (forestToLists f2 (forestToLists f3 []))),
        ∀ m ∈ l, 2 ≤ m ∧ HasFinsetRep (m + 2) (m - 1) := by
      apply checkForestStates_sound f0 _ hf0
      apply checkForestStates_sound f1 _ hf1
      apply checkForestStates_sound f2 _ hf2
      apply checkForestStates_sound f3 _ hf3
      intro l hl; contradiction
    have hn_rep := mergeAllLists_sound (fun m => 2 ≤ m ∧ HasFinsetRep (m + 2) (m - 1))
      14 1 _ hall n hmem
    exact erdos261Prop_of_hasFinsetRep hn_rep.1 hn_rep.2

/-- **Tengely, Ulas, and Zygadło [TUZ20]**: Every positive integer $n \le 10000$ satisfies
`Erdos261Prop n`. -/
theorem le_10000 {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) : Erdos261Prop n :=
  erdos261Prop_of_certificates forest0 forest1 forest2 forest3
    f0_ok f1_ok f2_ok f3_ok all_seq_ok hn_pos hn

end Erdos261
