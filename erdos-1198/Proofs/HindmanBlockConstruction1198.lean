module

/-
Erdős Problem 1198, `variants.hindman`: Hindman's theorem for an increasing positive sequence.

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

public import Mathlib.Combinatorics.Hindman
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

open Finset

namespace Erdos1198

/-! ## A monochromatic finite-sums stream with positive entries -/

lemma FS.pos {s : Stream' ℕ} (hs : ∀ i, 0 < s.get i) {m : ℕ} (h : Hindman.FS s m) : 0 < m := by
  induction h with
  | head a => exact hs 0
  | of_tail a m _ ih => exact ih (fun i => by simpa using hs (i + 1))
  | cons a m _ ih =>
    have h0 : 0 < a.get 0 := hs 0
    exact Nat.add_pos_left h0 m

theorem reduce (c : ℕ → Fin 2) :
    ∃ (b : ℕ → ℕ) (col : Fin 2), (∀ i, 0 < b i) ∧
      ∀ m : ℕ, Hindman.FS b m → c m = col := by
  classical
  have hcov : ∀ m, Hindman.FS (Stream'.const (1 : ℕ)) m →
      m ∈ ⋃₀ ({c ⁻¹' {0} ∩ {m | Hindman.FS (Stream'.const (1 : ℕ)) m},
              c ⁻¹' {1} ∩ {m | Hindman.FS (Stream'.const (1 : ℕ)) m}} : Set (Set ℕ)) := by
    intro m hm
    rw [Set.mem_sUnion]
    rcases hcm : c m with ⟨v, hv⟩
    have hv2 : v = 0 ∨ v = 1 := by omega
    rcases hv2 with rfl | rfl
    · exact ⟨c ⁻¹' {0} ∩ {m | Hindman.FS (Stream'.const (1 : ℕ)) m}, by simp, by simp [hcm], hm⟩
    · exact ⟨c ⁻¹' {1} ∩ {m | Hindman.FS (Stream'.const (1 : ℕ)) m}, by simp, by simp [hcm], hm⟩
  obtain ⟨C, hC, b, hb⟩ := Hindman.FS_partition_regular (Stream'.const (1 : ℕ))
    ({c ⁻¹' {0} ∩ {m | Hindman.FS (Stream'.const (1 : ℕ)) m},
      c ⁻¹' {1} ∩ {m | Hindman.FS (Stream'.const (1 : ℕ)) m}} : Set (Set ℕ))
    (Set.toFinite _) hcov
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with hC | hC
  · refine ⟨b, 0, fun i => ?_, fun m hm => ?_⟩
    · have hmem : b i ∈ C := hb (b i) (Hindman.FS.singleton b i)
      rw [hC] at hmem
      exact FS.pos (fun _ => by simp) hmem.2
    · have hmem : m ∈ C := hb m hm
      rw [hC] at hmem
      simpa using hmem.1
  · refine ⟨b, 1, fun i => ?_, fun m hm => ?_⟩
    · have hmem : b i ∈ C := hb (b i) (Hindman.FS.singleton b i)
      rw [hC] at hmem
      exact FS.pos (fun _ => by simp) hmem.2
    · have hmem : m ∈ C := hb m hm
      rw [hC] at hmem
      simpa using hmem.1

/-! ## Consecutive blocks with strictly increasing sums -/

namespace BlockExtraction

/-- If every term is at least one, the cardinality of a finset is at most the sum. -/
lemma card_le_sum {b : ℕ → ℕ} (hb : ∀ i, 1 ≤ b i) (s : Finset ℕ) :
    s.card ≤ ∑ i ∈ s, b i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
      have := hb a
      omega

/-- State recursion: `(start k, len k)`.  Block `k` is `Ico (start k) (start (k+1))`. -/
def P (b : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 =>
      let p := P b k
      (p.1 + p.2, (∑ i ∈ Ico p.1 (p.1 + p.2), b i) + 1)

/-- Start of block `k`. -/
def st (b : ℕ → ℕ) (k : ℕ) : ℕ := (P b k).1

/-- Length of block `k`. -/
def ln (b : ℕ → ℕ) (k : ℕ) : ℕ := (P b k).2

/-- Sum of `b` over block `k`. -/
def blk (b : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Ico (st b k) (st b (k+1)), b i

lemma st_zero (b : ℕ → ℕ) : st b 0 = 0 := rfl

lemma st_succ (b : ℕ → ℕ) (k : ℕ) : st b (k+1) = st b k + ln b k := by
  simp [st, ln, P]

lemma ln_succ (b : ℕ → ℕ) (k : ℕ) :
    ln b (k+1) = (∑ i ∈ Ico (st b k) (st b k + ln b k), b i) + 1 := by
  simp [st, ln, P]

/-- The length of block `k+1` is the sum of block `k` plus one. -/
lemma ln_succ' (b : ℕ → ℕ) (k : ℕ) : ln b (k+1) = blk b k + 1 := by
  rw [ln_succ, ← st_succ]
  rfl

lemma ln_pos (b : ℕ → ℕ) (k : ℕ) : 0 < ln b k := by
  induction k with
  | zero => simp [ln, P]
  | succ k ih => rw [ln_succ]; omega

lemma st_lt_succ (b : ℕ → ℕ) (k : ℕ) : st b k < st b (k+1) := by
  rw [st_succ]
  have := ln_pos b k
  omega

lemma card_Ico_add (m l : ℕ) : (Ico m (m + l)).card = l := by
  rw [Nat.card_Ico, Nat.add_sub_cancel_left]

/-- Each block sum is at least its length, since every entry is at least one. -/
lemma blk_ge_ln {b : ℕ → ℕ} (hb : ∀ i, 1 ≤ b i) (k : ℕ) : ln b k ≤ blk b k := by
  have h : (Ico (st b k) (st b (k+1))).card = ln b k := by
    rw [st_succ]
    exact card_Ico_add _ _
  rw [← h]
  exact card_le_sum hb _

lemma blk_lt_succ {b : ℕ → ℕ} (hb : ∀ i, 1 ≤ b i) (k : ℕ) :
    blk b k < blk b (k+1) := by
  have h1 := blk_ge_ln hb (k+1)
  have h2 := ln_succ' b k
  omega

theorem block_extraction (b : ℕ → ℕ) (hb : ∀ i, 0 < b i) :
    ∃ a M : ℕ → ℕ, StrictMono a ∧ M 0 = 0 ∧ (∀ k, M k < M (k+1)) ∧
      (∀ k, a k = ∑ i ∈ Ico (M k) (M (k+1)), b i) := by
  refine ⟨blk b, st b, ?_, st_zero b, st_lt_succ b, fun k => rfl⟩
  exact strictMono_nat_of_lt_succ (blk_lt_succ (b := b) (fun i => hb i))


end BlockExtraction

/-! ## A finite sum of block sums is a finite sum in the original stream -/

lemma block_union_sum (b M : ℕ → ℕ) (hM : ∀ k, M k < M (k + 1)) (T : Finset ℕ) :
    (∑ k ∈ T, (∑ i ∈ Ico (M k) (M (k + 1)), b i))
      = ∑ i ∈ T.biUnion (fun k => Ico (M k) (M (k + 1))), b i := by
  classical
  have hmono : Monotone M := monotone_nat_of_le_succ fun n => Nat.le_of_lt (hM n)
  rw [Finset.sum_biUnion (f := b)]
  · intro k _ k' _ hkk'
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    rw [Finset.mem_Ico] at hx hx'
    rcases lt_or_gt_of_ne hkk' with hlt | hgt
    · have : M (k + 1) ≤ M k' := hmono (by omega)
      omega
    · have : M (k' + 1) ≤ M k := hmono (by omega)
      omega

/-! ## The finite-sums theorem for an arbitrary two-colouring -/

theorem erdos_1198.variants.hindman :
    ∀ c : ℕ → Fin 2, ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧ ∃ col : Fin 2,
      ∀ T : Finset ℕ, T.Nonempty → c (∑ i ∈ T, a i) = col := by
  intro c
  obtain ⟨b, col, hbpos, hbmono⟩ := reduce c
  obtain ⟨a, M, ha_mono, hM0, hMlt, ha_eq⟩ := BlockExtraction.block_extraction b hbpos
  refine ⟨a, ha_mono, ?_, col, fun T hT => ?_⟩
  · have h0 : a 0 = ∑ i ∈ Ico 0 (M 1), b i := by
      rw [ha_eq 0, hM0]
    rw [h0]
    have hne : (Ico 0 (M 1)).Nonempty := by
      have h1 : M 0 < M 1 := hMlt 0
      rw [hM0] at h1
      exact ⟨0, Finset.mem_Ico.mpr ⟨Nat.le_refl _, h1⟩⟩
    exact Finset.sum_pos (fun i _ => hbpos i) hne
  · set U : Finset ℕ := T.biUnion (fun k => Ico (M k) (M (k + 1))) with hU
    have hUne : U.Nonempty := by
      obtain ⟨k, hk⟩ := hT
      exact ⟨M k, Finset.mem_biUnion.mpr
        ⟨k, hk, Finset.mem_Ico.mpr ⟨Nat.le_refl _, hMlt k⟩⟩⟩
    have hsum : (∑ i ∈ T, a i) = ∑ i ∈ U, b i := by
      simp only [ha_eq]
      exact block_union_sum b M hMlt T
    rw [hsum]
    exact hbmono _ (Hindman.FS.finsetSum b U hUne)

end Erdos1198

