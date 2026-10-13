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

public import Erdos306Unified435

@[expose] public section


set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

noncomputable section
open scoped BigOperators

namespace Erdos306.PrimeResidueAndRowPotential

/-! ## Part 1: Directed Constant-Tail Row Decomposition and Head-Row Capacity Defect Conservation -/

theorem sum_graphNeighbors_directed_eq_sum_edges (ψ : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    (∑ p ∈ V, ∑ q ∈ graphNeighbors E p, ψ p q) =
      ∑ e ∈ E, (ψ e.1 e.2 + ψ e.2 e.1) := by
  have hfiber : ∀ p ∈ V,
      (∑ q ∈ graphNeighbors E p, ψ p q) =
        (∑ e ∈ E.filter (fun e => e.1 = p), ψ e.1 e.2) +
        (∑ e ∈ E.filter (fun e => e.2 = p), ψ e.2 e.1) := by
    intro p _
    rw [graphNeighbors,
      Finset.sum_union (disjoint_rightNeighbors_leftNeighbors E hE p),
      rightNeighbors, leftNeighbors,
      Finset.sum_image (injOn_snd_filter_fst E p),
      Finset.sum_image (injOn_fst_filter_snd E p)]
    congr 1
    · apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    · apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
  have hrew :
      (∑ p ∈ V, ∑ q ∈ graphNeighbors E p, ψ p q) =
        (∑ p ∈ V, ∑ e ∈ E.filter (fun e => e.1 = p), ψ e.1 e.2) +
        (∑ p ∈ V, ∑ e ∈ E.filter (fun e => e.2 = p), ψ e.2 e.1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hfiber
  have hfst := Finset.sum_fiberwise_of_maps_to
    (s := E) (t := V) (g := Prod.fst) (fun e he => (hend e he).1)
    (fun e => ψ e.1 e.2)
  have hsnd := Finset.sum_fiberwise_of_maps_to
    (s := E) (t := V) (g := Prod.snd) (fun e he => (hend e he).2)
    (fun e => ψ e.2 e.1)
  rw [hrew, hfst, hsnd, ← Finset.sum_add_distrib]

def headTailEdgeSlack (e : ℕ × ℕ) : ℚ :=
  if e.1 ∈ headPrimes29 ∧ e.2 ∉ headPrimes29 then
    (1 : ℚ) / (e.1 : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (e.2 : ℚ))
  else 0

def directedHeadTailSlack (p q : ℕ) : ℚ :=
  if p ∈ headPrimes29 ∧ q ∉ headPrimes29 then
    (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ))
  else 0

def headRowTailSlack (p : ℕ) (S : Finset ℕ) : ℚ :=
  ∑ q ∈ S \ headPrimes29, (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ))

theorem headTailEdgeSlack_nonneg (e : ℕ × ℕ)
    (he : e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    0 ≤ headTailEdgeSlack e := by
  unfold headTailEdgeSlack
  split_ifs with h
  · have hge2 : 31 ≤ e.2 := prime_ge_thirty_one_of_not_mem_headPrimes29 he.2.1 h.2
    have hinv : (1 : ℚ) / (e.2 : ℚ) ≤ (1 / 31 : ℚ) :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge2)
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hinv)
  · rfl

theorem prime_edge_inv_add_headTailEdgeSlack_le_headCard_decomp (e : ℕ × ℕ)
    (he : e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) + headTailEdgeSlack e ≤
      headCardLam e.1 + headCardLam e.2 + (1 / 31 : ℚ) ^ 2 + headCardSlack e := by
  rcases he with ⟨hp1, hp2, hlt⟩
  have hx0 : (0 : ℚ) ≤ (1 : ℚ) / (e.1 : ℚ) := by positivity
  have hy0 : (0 : ℚ) ≤ (1 : ℚ) / (e.2 : ℚ) := by positivity
  have hsplit : (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) =
      ((1 : ℚ) / (e.1 : ℚ)) * ((1 : ℚ) / (e.2 : ℚ)) :=
    (one_div_mul_one_div (e.1 : ℚ) (e.2 : ℚ)).symm
  rw [hsplit]
  by_cases h1 : e.1 ∈ headPrimes29
  · by_cases h2 : e.2 ∈ headPrimes29
    · have hh : e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29 := ⟨h1, h2⟩
      have hht : ¬ (e.1 ∈ headPrimes29 ∧ e.2 ∉ headPrimes29) := fun h => h.2 h2
      unfold headCardLam headCardSlack headTailEdgeSlack
      rw [if_pos h1, if_pos h2, if_pos hh, if_neg hht]
      linarith [constant_tail_head_head_identity ((1 : ℚ) / (e.1 : ℚ)) ((1 : ℚ) / (e.2 : ℚ)) (1 / 31 : ℚ)]
    · have hh : ¬ (e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29) := fun h => h2 h.2
      have hht : e.1 ∈ headPrimes29 ∧ e.2 ∉ headPrimes29 := ⟨h1, h2⟩
      unfold headCardLam headCardSlack headTailEdgeSlack
      rw [if_pos h1, if_neg h2, if_neg hh, if_pos hht]
      ring_nf
      exact le_rfl
  · have h2 : e.2 ∉ headPrimes29 := by
      intro h2in
      have h2le : e.2 ≤ 29 := (mem_headPrimes29_bounds h2in).2
      have h1ge : 31 ≤ e.1 := prime_ge_thirty_one_of_not_mem_headPrimes29 hp1 h1
      omega
    have hh : ¬ (e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29) := fun h => h1 h.1
    have hht : ¬ (e.1 ∈ headPrimes29 ∧ e.2 ∉ headPrimes29) := fun h => h1 h.1
    have hge1 : 31 ≤ e.1 := prime_ge_thirty_one_of_not_mem_headPrimes29 hp1 h1
    have hge2 : 31 ≤ e.2 := prime_ge_thirty_one_of_not_mem_headPrimes29 hp2 h2
    have hx_le : (1 : ℚ) / (e.1 : ℚ) ≤ (1 / 31 : ℚ) :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge1)
    have hy_le : (1 : ℚ) / (e.2 : ℚ) ≤ (1 / 31 : ℚ) :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge2)
    unfold headCardLam headCardSlack headTailEdgeSlack
    rw [if_neg h1, if_neg h2, if_neg hh, if_neg hht]
    have hbd := constant_tail_tail_tail_bound
      ((1 : ℚ) / (e.1 : ℚ)) ((1 : ℚ) / (e.2 : ℚ)) (1 / 31 : ℚ) hx0 hy0 hx_le hy_le
    linarith

theorem directedHeadTailSlack_add_comm_eq_headTailEdgeSlack (e : ℕ × ℕ)
    (he : e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    directedHeadTailSlack e.1 e.2 + directedHeadTailSlack e.2 e.1 = headTailEdgeSlack e := by
  have hrev : ¬ (e.2 ∈ headPrimes29 ∧ e.1 ∉ headPrimes29) := by
    rintro ⟨h2, h1⟩
    have h2le : e.2 ≤ 29 := (mem_headPrimes29_bounds h2).2
    have h1ge : 31 ≤ e.1 := prime_ge_thirty_one_of_not_mem_headPrimes29 he.1 h1
    omega
  change headTailEdgeSlack e + directedHeadTailSlack e.2 e.1 = headTailEdgeSlack e
  unfold directedHeadTailSlack
  rw [if_neg hrev, add_zero]

theorem sum_directedHeadTailSlack_eq_headRowTailSlack {p : ℕ} (hp : p ∈ headPrimes29)
    (S : Finset ℕ) :
    (∑ q ∈ S, directedHeadTailSlack p q) = headRowTailSlack p S := by
  unfold headRowTailSlack
  have hsub : (∑ q ∈ S \ headPrimes29, directedHeadTailSlack p q) =
      ∑ q ∈ S, directedHeadTailSlack p q := by
    apply Finset.sum_subset Finset.sdiff_subset
    intro q hqS hqnot
    have hqin : q ∈ headPrimes29 := by
      by_contra hqout
      exact hqnot (Finset.mem_sdiff.mpr ⟨hqS, hqout⟩)
    unfold directedHeadTailSlack
    rw [if_neg (fun h => h.2 hqin)]
  rw [← hsub]
  apply Finset.sum_congr rfl
  intro q hq
  have hqout : q ∉ headPrimes29 := (Finset.mem_sdiff.mp hq).2
  unfold directedHeadTailSlack
  rw [if_pos ⟨hp, hqout⟩]

theorem sum_headRowTailSlack_eq_sum_headTailEdgeSlack
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hH : headPrimes29 ⊆ V) :
    (∑ p ∈ headPrimes29, headRowTailSlack p (graphNeighbors E p)) =
      ∑ e ∈ E, headTailEdgeSlack e := by
  have hdir := sum_graphNeighbors_directed_eq_sum_edges directedHeadTailSlack E V
    (fun e he => (hE e he).2.2) hend
  have hV_eq :
      (∑ p ∈ headPrimes29, ∑ q ∈ graphNeighbors E p, directedHeadTailSlack p q) =
        ∑ p ∈ V, ∑ q ∈ graphNeighbors E p, directedHeadTailSlack p q := by
    apply Finset.sum_subset hH
    intro p _ hpnot
    apply Finset.sum_eq_zero
    intro q _
    unfold directedHeadTailSlack
    rw [if_neg (fun h => hpnot h.1)]
  have hL :
      (∑ p ∈ headPrimes29, headRowTailSlack p (graphNeighbors E p)) =
        ∑ p ∈ headPrimes29, ∑ q ∈ graphNeighbors E p, directedHeadTailSlack p q := by
    apply Finset.sum_congr rfl
    intro p hp
    exact (sum_directedHeadTailSlack_eq_headRowTailSlack hp (graphNeighbors E p)).symm
  have hR :
      (∑ e ∈ E, (directedHeadTailSlack e.1 e.2 + directedHeadTailSlack e.2 e.1)) =
        ∑ e ∈ E, headTailEdgeSlack e := by
    apply Finset.sum_congr rfl
    intro e he
    exact directedHeadTailSlack_add_comm_eq_headTailEdgeSlack e (hE e he)
  rw [hL, hV_eq, hdir, hR]

def directedHeadPairSlack (p q : ℕ) : ℚ :=
  if p ∈ headPrimes29 ∧ q ∈ headPrimes29 ∧ p ≠ q then
    ((1 : ℚ) / (p : ℚ) - (1 / 31 : ℚ)) * ((1 : ℚ) / (q : ℚ) - (1 / 31 : ℚ)) / 2
  else 0

def headRowMissingPairSlack (p : ℕ) (S : Finset ℕ) : ℚ :=
  ∑ r ∈ (headPrimes29.erase p) \ S, directedHeadPairSlack p r

theorem directedHeadPairSlack_nonneg (p q : ℕ) :
    0 ≤ directedHeadPairSlack p q := by
  unfold directedHeadPairSlack
  split_ifs with h
  · rcases mem_headPrimes29_bounds h.1 with ⟨h1a, h1b⟩
    rcases mem_headPrimes29_bounds h.2.1 with ⟨h2a, h2b⟩
    have hp : (1 / 31 : ℚ) ≤ (1 : ℚ) / (p : ℚ) :=
      one_div_le_one_div_of_le (by exact_mod_cast h1a) (by exact_mod_cast (show p ≤ 31 by omega))
    have hq : (1 / 31 : ℚ) ≤ (1 : ℚ) / (q : ℚ) :=
      one_div_le_one_div_of_le (by exact_mod_cast h2a) (by exact_mod_cast (show q ≤ 31 by omega))
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)) (by norm_num)
  · rfl

theorem headRowMissingPairSlack_nonneg (p : ℕ) (S : Finset ℕ) :
    0 ≤ headRowMissingPairSlack p S :=
  Finset.sum_nonneg (fun r _ => directedHeadPairSlack_nonneg p r)

theorem directedHeadPairSlack_add_comm_eq_headCardSlack (e : ℕ × ℕ) (hlt : e.1 < e.2) :
    directedHeadPairSlack e.1 e.2 + directedHeadPairSlack e.2 e.1 = headCardSlack e := by
  have hne12 : e.1 ≠ e.2 := ne_of_lt hlt
  have hne21 : e.2 ≠ e.1 := ne_of_gt hlt
  by_cases hh : e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29
  · have h12 : e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29 ∧ e.1 ≠ e.2 := ⟨hh.1, hh.2, hne12⟩
    have h21 : e.2 ∈ headPrimes29 ∧ e.1 ∈ headPrimes29 ∧ e.2 ≠ e.1 := ⟨hh.2, hh.1, hne21⟩
    unfold directedHeadPairSlack headCardSlack
    rw [if_pos h12, if_pos h21, if_pos hh]
    ring
  · have h12 : ¬ (e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29 ∧ e.1 ≠ e.2) :=
      fun h => hh ⟨h.1, h.2.1⟩
    have h21 : ¬ (e.2 ∈ headPrimes29 ∧ e.1 ∈ headPrimes29 ∧ e.2 ≠ e.1) :=
      fun h => hh ⟨h.2.1, h.1⟩
    unfold directedHeadPairSlack headCardSlack
    rw [if_neg h12, if_neg h21, if_neg hh, add_zero]

theorem sum_directedHeadPairSlack_add_missing_eq (p : ℕ) (S : Finset ℕ) :
    (∑ q ∈ S, directedHeadPairSlack p q) + headRowMissingPairSlack p S =
      ∑ r ∈ headPrimes29.erase p, directedHeadPairSlack p r := by
  have hinter :
      (∑ q ∈ S ∩ (headPrimes29.erase p), directedHeadPairSlack p q) =
        ∑ q ∈ S, directedHeadPairSlack p q := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro q hqS hqnot
    have hnot : ¬ (p ∈ headPrimes29 ∧ q ∈ headPrimes29 ∧ p ≠ q) := by
      rintro ⟨_, hqH, hpq⟩
      exact hqnot (Finset.mem_inter.mpr ⟨hqS, Finset.mem_erase.mpr ⟨hpq.symm, hqH⟩⟩)
    unfold directedHeadPairSlack
    rw [if_neg hnot]
  have hsdiff :
      ((headPrimes29.erase p) \ S) ∪ (S ∩ (headPrimes29.erase p)) = headPrimes29.erase p := by
    ext r
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdisj : Disjoint ((headPrimes29.erase p) \ S) (S ∩ (headPrimes29.erase p)) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    exact (Finset.mem_sdiff.mp hr1).2 (Finset.mem_inter.mp hr2).1
  rw [← hinter, add_comm]
  unfold headRowMissingPairSlack
  rw [← Finset.sum_union hdisj, hsdiff]

theorem sum_headPrimes29_directedHeadPairSlack_eq_sum_headPairs29 :
    (∑ p ∈ headPrimes29, ∑ r ∈ headPrimes29.erase p, directedHeadPairSlack p r) =
      ∑ e ∈ headPairs29, headCardSlack e := by
  norm_num [headPrimes29, headPairs29, directedHeadPairSlack, headCardSlack,
    Finset.sum_product, Finset.sum_filter, Finset.sum_erase, Finset.sum_insert,
    Finset.erase_insert, Finset.mem_insert, Finset.mem_singleton, Finset.mem_product,
    Finset.mem_filter, Finset.mem_erase]

theorem sum_headCardSlack_add_sum_missing_eq_sum_headPairs29
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hH : headPrimes29 ⊆ V) :
    (∑ e ∈ E, headCardSlack e) +
      (∑ p ∈ headPrimes29, headRowMissingPairSlack p (graphNeighbors E p)) =
      ∑ e ∈ headPairs29, headCardSlack e := by
  have hdir := sum_graphNeighbors_directed_eq_sum_edges directedHeadPairSlack E V hE hend
  have hV_eq :
      (∑ p ∈ headPrimes29, ∑ q ∈ graphNeighbors E p, directedHeadPairSlack p q) =
        ∑ p ∈ V, ∑ q ∈ graphNeighbors E p, directedHeadPairSlack p q := by
    apply Finset.sum_subset hH
    intro p _ hpnot
    apply Finset.sum_eq_zero
    intro q _
    unfold directedHeadPairSlack
    rw [if_neg (fun h => hpnot h.1)]
  have hR :
      (∑ e ∈ E, (directedHeadPairSlack e.1 e.2 + directedHeadPairSlack e.2 e.1)) =
        ∑ e ∈ E, headCardSlack e := by
    apply Finset.sum_congr rfl
    intro e he
    exact directedHeadPairSlack_add_comm_eq_headCardSlack e (hE e he)
  rw [← hR, ← hdir, ← hV_eq, ← Finset.sum_add_distrib]
  have hcongr :
      (∑ p ∈ headPrimes29,
        ((∑ q ∈ graphNeighbors E p, directedHeadPairSlack p q) +
          headRowMissingPairSlack p (graphNeighbors E p))) =
      ∑ p ∈ headPrimes29, ∑ r ∈ headPrimes29.erase p, directedHeadPairSlack p r := by
    apply Finset.sum_congr rfl
    intro p _
    exact sum_directedHeadPairSlack_add_missing_eq p (graphNeighbors E p)
  rw [hcongr, sum_headPrimes29_directedHeadPairSlack_eq_sum_headPairs29]

def headRowAdmissibilityDefect (p : ℕ) (S : Finset ℕ) : ℚ :=
  ((10 : ℚ) - (S.card : ℚ)) * headCardLam p + headRowTailSlack p S

def headRowCapacityDefect (p : ℕ) (S : Finset ℕ) : ℚ :=
  headRowAdmissibilityDefect p S + headRowMissingPairSlack p S

theorem constant_tail_capacity_with_full_row_defect
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) +
      (∑ p ∈ headPrimes29, headRowCapacityDefect p (graphNeighbors E p)) ≤
      (10 : ℚ) * (∑ p ∈ headPrimes29, headCardLam p) +
        (∑ e ∈ headPairs29, headCardSlack e) +
        ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) := by
  let V := headPrimes29 ∪ E.image Prod.fst ∪ E.image Prod.snd
  have hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V := by
    intro e he
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))
  have hH : headPrimes29 ⊆ V := by
    intro p hp
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hp)))
  have hE_lt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hedge_sum := Finset.sum_le_sum (fun e he =>
    prime_edge_inv_add_headTailEdgeSlack_le_headCard_decomp e (hE e he))
  rw [Finset.sum_add_distrib] at hedge_sum
  have hEND :
      (∑ e ∈ E, (headCardLam e.1 + headCardLam e.2)) =
        ∑ p ∈ headPrimes29, ((graphNeighbors E p).card : ℚ) * headCardLam p := by
    have hfst := Finset.sum_fiberwise_of_maps_to'
      (s := E) (t := V) (g := Prod.fst) (fun e he => (hend e he).1) headCardLam
    have hsnd := Finset.sum_fiberwise_of_maps_to'
      (s := E) (t := V) (g := Prod.snd) (fun e he => (hend e he).2) headCardLam
    have h1 : (∑ e ∈ E, (headCardLam e.1 + headCardLam e.2)) =
        ∑ v ∈ V, (incidenceDegree E v : ℚ) * headCardLam v := by
      rw [Finset.sum_add_distrib, ← hfst, ← hsnd, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      simp [incidenceDegree, Nat.cast_add, add_mul]
    have h2 : (∑ p ∈ headPrimes29, (incidenceDegree E p : ℚ) * headCardLam p) =
        ∑ v ∈ V, (incidenceDegree E v : ℚ) * headCardLam v := by
      apply Finset.sum_subset hH
      intro v _ hvnot
      unfold headCardLam
      rw [if_neg hvnot, mul_zero]
    rw [h1, ← h2]
    apply Finset.sum_congr rfl
    intro p _
    rw [card_graphNeighbors_eq_incidenceDegree E hE_lt p]
  have hdeg_split :
      (∑ p ∈ headPrimes29, ((graphNeighbors E p).card : ℚ) * headCardLam p) +
        (∑ p ∈ headPrimes29, ((10 : ℚ) - ((graphNeighbors E p).card : ℚ)) * headCardLam p) =
        (10 : ℚ) * (∑ p ∈ headPrimes29, headCardLam p) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hht := sum_headRowTailSlack_eq_sum_headTailEdgeSlack E V hE hend hH
  have hmiss := sum_headCardSlack_add_sum_missing_eq_sum_headPairs29 E V hE_lt hend hH
  have hrhs :
      (∑ e ∈ E, (headCardLam e.1 + headCardLam e.2 + (1 / 31 : ℚ) ^ 2 + headCardSlack e)) =
        (∑ e ∈ E, (headCardLam e.1 + headCardLam e.2)) +
          ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) +
          (∑ e ∈ E, headCardSlack e) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hdef_split :
      (∑ p ∈ headPrimes29, headRowCapacityDefect p (graphNeighbors E p)) =
        (∑ p ∈ headPrimes29, ((10 : ℚ) - ((graphNeighbors E p).card : ℚ)) * headCardLam p) +
          (∑ p ∈ headPrimes29, headRowTailSlack p (graphNeighbors E p)) +
          (∑ p ∈ headPrimes29, headRowMissingPairSlack p (graphNeighbors E p)) := by
    unfold headRowCapacityDefect headRowAdmissibilityDefect
    simp only [Finset.sum_add_distrib]
  linarith

theorem constant_tail_capacity_with_row_admissibility_defect
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) +
      (∑ p ∈ headPrimes29, headRowAdmissibilityDefect p (graphNeighbors E p)) ≤
      (10 : ℚ) * (∑ p ∈ headPrimes29, headCardLam p) +
        (∑ e ∈ headPairs29, headCardSlack e) +
        ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) := by
  have hfull := constant_tail_capacity_with_full_row_defect E hE
  have hle :
      (∑ p ∈ headPrimes29, headRowAdmissibilityDefect p (graphNeighbors E p)) ≤
        ∑ p ∈ headPrimes29, headRowCapacityDefect p (graphNeighbors E p) := by
    apply Finset.sum_le_sum
    intro p _
    unfold headRowCapacityDefect
    linarith [headRowMissingPairSlack_nonneg p (graphNeighbors E p)]
  linarith

/-! ## Part 2: Local Prime-Row Admissibility Defects on `headPrimes29` and All-Support Bounds (`|E| ≥ 57, 58`) -/

def headRowCandidate31 (p : ℕ) : Finset ℕ :=
  (headPrimes29.erase p) ∪ {31}

def headDefectPrimes29 : Finset ℕ :=
  (headPrimes29.erase 2).erase 5

def smallTailPrimes43 : Finset ℕ :=
  {31, 37, 41, 43}

theorem card_headRowCandidate31 {p : ℕ} (hp : p ∈ headPrimes29) :
    (headRowCandidate31 p).card = 10 := by
  decide +revert

theorem not_primeRowAdmissible_headRowCandidate31 {p : ℕ} (hp : p ∈ headDefectPrimes29) :
    ¬ PrimeRowAdmissible p (headRowCandidate31 p) := by
  decide +revert

theorem primeRowAdmissible_headRowCandidate31_two_and_five :
    PrimeRowAdmissible 2 (headRowCandidate31 2) ∧
    PrimeRowAdmissible 5 (headRowCandidate31 5) := by
  decide

theorem prime_ge_thirty_seven_of_not_mem_headPrimes29_ne_thirty_one
    {q : ℕ} (hq : q.Prime) (hnot : q ∉ headPrimes29) (hne31 : q ≠ 31) :
    37 ≤ q := by
  have hge31 : 31 ≤ q := prime_ge_thirty_one_of_not_mem_headPrimes29 hq hnot
  by_contra hlt37
  have hmem : q ∈ Finset.Icc 32 36 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcheck : ∀ n ∈ Finset.Icc 32 36, ¬ Nat.Prime n := by decide
  exact hcheck q hmem hq

theorem exists_tail_neighbor_ne_thirty_one_of_card_eq_ten_ne_candidate
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ headPrimes29) (hpS : p ∉ S)
    (hcard : S.card = 10) (hne : S ≠ headRowCandidate31 p) :
    ∃ q ∈ S \ headPrimes29, q ≠ 31 := by
  by_contra hall
  push Not at hall
  have hsub : S ⊆ headRowCandidate31 p := by
    intro q hq
    unfold headRowCandidate31
    by_cases hqH : q ∈ headPrimes29
    · have hqp : q ≠ p := fun h => hpS (h ▸ hq)
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hqp, hqH⟩))
    · have hq31 : q = 31 := hall q (Finset.mem_sdiff.mpr ⟨hq, hqH⟩)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr hq31))
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [card_headRowCandidate31 hp, hcard])
  exact hne heq

def headPrimeMinRowDefect (p : ℕ) : ℚ :=
  if p ∈ headDefectPrimes29 then
    min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ)))
  else 0

theorem headRowTailSlack_nonneg {p : ℕ} {S : Finset ℕ}
    (hprime : ∀ q ∈ S, q.Prime) :
    0 ≤ headRowTailSlack p S := by
  unfold headRowTailSlack
  apply Finset.sum_nonneg
  intro q hq
  rcases Finset.mem_sdiff.mp hq with ⟨hqS, hqnot⟩
  have hge31 : 31 ≤ q := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime q hqS) hqnot
  have hinv : (1 : ℚ) / (q : ℚ) ≤ (1 / 31 : ℚ) :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hinv)

theorem headRowAdmissibilityDefect_nonneg {p : ℕ} {S : Finset ℕ}
    (hcard : S.card ≤ 10) (hprime : ∀ q ∈ S, q.Prime) :
    0 ≤ headRowAdmissibilityDefect p S := by
  unfold headRowAdmissibilityDefect
  have hc : (S.card : ℚ) ≤ 10 := by exact_mod_cast hcard
  exact add_nonneg (mul_nonneg (by linarith) (headCardLam_nonneg p)) (headRowTailSlack_nonneg hprime)

theorem headPrimeMinRowDefect_le_headRowAdmissibilityDefect
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ headPrimes29) (hpS : p ∉ S)
    (hcard : S.card ≤ 10) (hprime : ∀ q ∈ S, q.Prime)
    (hadm : PrimeRowAdmissible p S) :
    headPrimeMinRowDefect p ≤ headRowAdmissibilityDefect p S := by
  unfold headPrimeMinRowDefect
  split_ifs with hp_def
  · by_cases hc9 : S.card ≤ 9
    · have h1 : (1 : ℚ) ≤ (10 : ℚ) - (S.card : ℚ) := by
        have hc9_q : (S.card : ℚ) ≤ 9 := by exact_mod_cast hc9
        linarith
      have hdeg : headCardLam p ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
        nlinarith [headCardLam_nonneg p]
      have hmin : min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ))) ≤
          headCardLam p := min_le_left _ _
      unfold headRowAdmissibilityDefect
      linarith [headRowTailSlack_nonneg (p := p) hprime]
    · have hc10 : S.card = 10 := by omega
      have hne : S ≠ headRowCandidate31 p := by
        intro heq
        exact not_primeRowAdmissible_headRowCandidate31 hp_def (heq ▸ hadm)
      obtain ⟨q, hq, hne31⟩ :=
        exists_tail_neighbor_ne_thirty_one_of_card_eq_ten_ne_candidate hp hpS hc10 hne
      rcases Finset.mem_sdiff.mp hq with ⟨hqS, hqnot⟩
      have hge37 : 37 ≤ q :=
        prime_ge_thirty_seven_of_not_mem_headPrimes29_ne_thirty_one (hprime q hqS) hqnot hne31
      have hinv37 : (1 : ℚ) / (q : ℚ) ≤ (1 / 37 : ℚ) :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge37)
      have hp_pos : (0 : ℚ) ≤ (1 : ℚ) / (p : ℚ) := by positivity
      have hterm :
          (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ)) ≤
            (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hp_pos
      have hsingle :
          (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) ≤ headRowTailSlack p S := by
        unfold headRowTailSlack
        apply Finset.single_le_sum (fun r hr => ?_) hq
        rcases Finset.mem_sdiff.mp hr with ⟨hrS, hrnot⟩
        have hge31 : 31 ≤ r := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime r hrS) hrnot
        have hinv31 : (1 : ℚ) / (r : ℚ) ≤ (1 / 31 : ℚ) :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
        exact mul_nonneg hp_pos (sub_nonneg.mpr hinv31)
      have hmin : min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ))) ≤
          (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ)) := min_le_right _ _
      have hdeg0 : (0 : ℚ) ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
        rw [hc10]
        norm_num
      unfold headRowAdmissibilityDefect
      linarith
  · exact headRowAdmissibilityDefect_nonneg hcard hprime

theorem prime_edges_card_ge_fifty_seven_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    57 ≤ E.card := by
  have hE_lt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hsum_div : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = ((1 : ℤ) : ℚ) / ((1 : ℕ) : ℚ) := by
    simpa using hsum
  have hcap := constant_tail_capacity_with_row_admissibility_defect E hE
  have hdef_sum :
      (∑ p ∈ headPrimes29, headPrimeMinRowDefect p) ≤
        ∑ p ∈ headPrimes29, headRowAdmissibilityDefect p (graphNeighbors E p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp_prime : p.Prime := by
      decide +revert
    have hpS : p ∉ graphNeighbors E p := not_mem_graphNeighbors_self E hE_lt p
    have hcard : (graphNeighbors E p).card ≤ 10 := by
      rw [card_graphNeighbors_eq_incidenceDegree E hE_lt p]
      exact hdeg p hp_prime
    have hprime : ∀ q ∈ graphNeighbors E p, q.Prime := by
      intro q hq
      rcases (mem_graphNeighbors_iff E p q).mp hq with he | he
      · exact (hE (p, q) he).2.1
      · exact (hE (q, p) he).1
    have hadm : PrimeRowAdmissible p (graphNeighbors E p) :=
      (prime_graph_row_admissible_of_sum_eq_div E p 1 1 hE hp_prime (by decide) (Nat.coprime_one_right p) hsum_div).1
    exact headPrimeMinRowDefect_le_headRowAdmissibilityDefect hp hpS hcard hprime hadm
  have hconst :
      (10 : ℚ) * (∑ p ∈ headPrimes29, headCardLam p) +
        (∑ e ∈ headPairs29, headCardSlack e) -
        (∑ p ∈ headPrimes29, headPrimeMinRowDefect p) +
        56 * ((1 / 31 : ℚ) ^ 2) < 1 := by
    decide +kernel
  have hlt : (56 : ℚ) < (E.card : ℚ) := by
    by_contra hle
    have hle' : (E.card : ℚ) ≤ 56 := not_lt.mp hle
    have hmul : ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) ≤ 56 * ((1 / 31 : ℚ) ^ 2) := by linarith
    linarith
  have hlt_nat : 56 < E.card := by exact_mod_cast hlt
  omega

theorem not_primeRowAdmissible_head_union_singleton_of_mem_smallTailPrimes43
    {p q : ℕ} (hp : p ∈ headDefectPrimes29) (hq : q ∈ smallTailPrimes43) :
    ¬ PrimeRowAdmissible p ((headPrimes29.erase p) ∪ {q}) := by
  have h : ∀ x ∈ headDefectPrimes29, ∀ y ∈ smallTailPrimes43,
      ¬ PrimeRowAdmissible x ((headPrimes29.erase x) ∪ {y}) := by decide
  exact h p hp q hq

theorem prime_ge_forty_seven_of_not_mem_headPrimes29_not_mem_smallTailPrimes43
    {q : ℕ} (hq : q.Prime) (hnotH : q ∉ headPrimes29) (hnot43 : q ∉ smallTailPrimes43) :
    47 ≤ q := by
  have hge31 : 31 ≤ q := prime_ge_thirty_one_of_not_mem_headPrimes29 hq hnotH
  by_contra hlt47
  have hmem : q ∈ Finset.Icc 31 46 := Finset.mem_Icc.mpr ⟨hge31, by omega⟩
  have hcheck : ∀ n ∈ Finset.Icc 31 46, Nat.Prime n → n ∈ smallTailPrimes43 := by decide
  exact hnot43 (hcheck q hmem hq)

theorem exists_single_tail_neighbor_of_head_erase_subset_of_card_eq_ten
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ headPrimes29) (hpS : p ∉ S)
    (hsub : headPrimes29.erase p ⊆ S) (hcard : S.card = 10) :
    ∃ q ∈ S \ headPrimes29, S = (headPrimes29.erase p) ∪ {q} := by
  have hinter : S ∩ headPrimes29 = headPrimes29.erase p := by
    ext r
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨hrS, hrH⟩
      exact ⟨fun hrp => hpS (hrp ▸ hrS), hrH⟩
    · intro hr
      exact ⟨hsub (Finset.mem_erase.mpr hr), hr.2⟩
  have hcard_erase : (headPrimes29.erase p).card = 9 := by
    have h : ∀ x ∈ headPrimes29, (headPrimes29.erase x).card = 9 := by decide
    exact h p hp
  have hcard_sdiff : (S \ headPrimes29).card = 1 := by
    have hsplit := Finset.card_sdiff_add_card_inter S headPrimes29
    rw [hinter, hcard_erase, hcard] at hsplit
    omega
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hcard_sdiff
  have hq_mem : q ∈ S \ headPrimes29 := by
    rw [hq_eq]
    exact Finset.mem_singleton_self q
  refine ⟨q, hq_mem, ?_⟩
  have hunion := (Finset.sdiff_union_inter S headPrimes29).symm
  rw [hq_eq, hinter, Finset.union_comm] at hunion
  exact hunion

def headMinMissingPairSlack (p : ℕ) : ℚ :=
  if p = 29 then directedHeadPairSlack 29 23
  else if p ∈ headPrimes29 then directedHeadPairSlack p 29
  else 0

theorem headMinMissingPairSlack_le_directedHeadPairSlack
    {p r : ℕ} (hp : p ∈ headPrimes29) (hr : r ∈ headPrimes29.erase p) :
    headMinMissingPairSlack p ≤ directedHeadPairSlack p r := by
  have h : ∀ x ∈ headPrimes29, ∀ y ∈ headPrimes29.erase x,
      headMinMissingPairSlack x ≤ directedHeadPairSlack x y := by decide +kernel
  exact h p hp r hr

theorem headMinMissingPairSlack_le_headRowMissingPairSlack_of_not_subset
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ headPrimes29)
    (hnot : ¬ headPrimes29.erase p ⊆ S) :
    headMinMissingPairSlack p ≤ headRowMissingPairSlack p S := by
  have hne : ((headPrimes29.erase p) \ S).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun hemp => hnot (Finset.sdiff_eq_empty_iff_subset.mp hemp))
  rcases hne with ⟨r, hr⟩
  have hr_erase : r ∈ headPrimes29.erase p := (Finset.mem_sdiff.mp hr).1
  have hle := headMinMissingPairSlack_le_directedHeadPairSlack hp hr_erase
  have hsingle : directedHeadPairSlack p r ≤ headRowMissingPairSlack p S := by
    unfold headRowMissingPairSlack
    exact Finset.single_le_sum (fun x _ => directedHeadPairSlack_nonneg p x) hr
  linarith

def headPrimeFullRowDefect (p : ℕ) : ℚ :=
  if p ∈ headDefectPrimes29 then
    min (min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ))))
        (headPrimeMinRowDefect p + headMinMissingPairSlack p)
  else 0

theorem headPrimeFullRowDefect_le_headRowCapacityDefect
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ headPrimes29) (hpS : p ∉ S)
    (hcard : S.card ≤ 10) (hprime : ∀ q ∈ S, q.Prime)
    (hadm : PrimeRowAdmissible p S) :
    headPrimeFullRowDefect p ≤ headRowCapacityDefect p S := by
  unfold headPrimeFullRowDefect
  split_ifs with hp_def
  · by_cases hsub : headPrimes29.erase p ⊆ S
    · have hmin1 :
        min (min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ))))
            (headPrimeMinRowDefect p + headMinMissingPairSlack p) ≤
          min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ))) :=
        min_le_left _ _
      by_cases hc9 : S.card ≤ 9
      · have h1 : (1 : ℚ) ≤ (10 : ℚ) - (S.card : ℚ) := by
          have hc9_q : (S.card : ℚ) ≤ 9 := by exact_mod_cast hc9
          linarith
        have hdeg : headCardLam p ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
          nlinarith [headCardLam_nonneg p]
        have hmin2 : min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ))) ≤
            headCardLam p := min_le_left _ _
        unfold headRowCapacityDefect headRowAdmissibilityDefect
        linarith [headRowTailSlack_nonneg (p := p) hprime, headRowMissingPairSlack_nonneg p S]
      · have hc10 : S.card = 10 := by omega
        obtain ⟨q, hq, hS_eq⟩ :=
          exists_single_tail_neighbor_of_head_erase_subset_of_card_eq_ten hp hpS hsub hc10
        rcases Finset.mem_sdiff.mp hq with ⟨hqS, hqnotH⟩
        have hnot43 : q ∉ smallTailPrimes43 := by
          intro hq43
          exact not_primeRowAdmissible_head_union_singleton_of_mem_smallTailPrimes43
            hp_def hq43 (hS_eq ▸ hadm)
        have hge47 : 47 ≤ q :=
          prime_ge_forty_seven_of_not_mem_headPrimes29_not_mem_smallTailPrimes43
            (hprime q hqS) hqnotH hnot43
        have hinv47 : (1 : ℚ) / (q : ℚ) ≤ (1 / 47 : ℚ) :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge47)
        have hp_pos : (0 : ℚ) ≤ (1 : ℚ) / (p : ℚ) := by positivity
        have hterm :
            (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ)) ≤
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hp_pos
        have hsingle :
            (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) ≤ headRowTailSlack p S := by
          unfold headRowTailSlack
          apply Finset.single_le_sum (fun r hr => ?_) hq
          rcases Finset.mem_sdiff.mp hr with ⟨hrS, hrnot⟩
          have hge31 : 31 ≤ r := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime r hrS) hrnot
          have hinv31 : (1 : ℚ) / (r : ℚ) ≤ (1 / 31 : ℚ) :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
          exact mul_nonneg hp_pos (sub_nonneg.mpr hinv31)
        have hmin2 : min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ))) ≤
            (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ)) := min_le_right _ _
        have hdeg0 : (0 : ℚ) ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
          rw [hc10]
          norm_num
        unfold headRowCapacityDefect headRowAdmissibilityDefect
        linarith [headRowMissingPairSlack_nonneg p S]
    · have hmin1 :
        min (min (headCardLam p) ((1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ))))
            (headPrimeMinRowDefect p + headMinMissingPairSlack p) ≤
          headPrimeMinRowDefect p + headMinMissingPairSlack p :=
        min_le_right _ _
      have hadm_lb := headPrimeMinRowDefect_le_headRowAdmissibilityDefect hp hpS hcard hprime hadm
      have hmiss_lb := headMinMissingPairSlack_le_headRowMissingPairSlack_of_not_subset hp hsub
      unfold headRowCapacityDefect
      linarith
  · unfold headRowCapacityDefect
    linarith [headRowAdmissibilityDefect_nonneg (p := p) hcard hprime,
      headRowMissingPairSlack_nonneg p S]

theorem prime_edges_card_ge_fifty_eight_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    58 ≤ E.card := by
  have hE_lt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hsum_div : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = ((1 : ℤ) : ℚ) / ((1 : ℕ) : ℚ) := by
    simpa using hsum
  have hcap := constant_tail_capacity_with_full_row_defect E hE
  have hdef_sum :
      (∑ p ∈ headPrimes29, headPrimeFullRowDefect p) ≤
        ∑ p ∈ headPrimes29, headRowCapacityDefect p (graphNeighbors E p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp_prime : p.Prime := by
      decide +revert
    have hpS : p ∉ graphNeighbors E p := not_mem_graphNeighbors_self E hE_lt p
    have hcard : (graphNeighbors E p).card ≤ 10 := by
      rw [card_graphNeighbors_eq_incidenceDegree E hE_lt p]
      exact hdeg p hp_prime
    have hprime : ∀ q ∈ graphNeighbors E p, q.Prime := by
      intro q hq
      rcases (mem_graphNeighbors_iff E p q).mp hq with he | he
      · exact (hE (p, q) he).2.1
      · exact (hE (q, p) he).1
    have hadm : PrimeRowAdmissible p (graphNeighbors E p) :=
      (prime_graph_row_admissible_of_sum_eq_div E p 1 1 hE hp_prime (by decide) (Nat.coprime_one_right p) hsum_div).1
    exact headPrimeFullRowDefect_le_headRowCapacityDefect hp hpS hcard hprime hadm
  have hconst :
      (10 : ℚ) * (∑ p ∈ headPrimes29, headCardLam p) +
        (∑ e ∈ headPairs29, headCardSlack e) -
        (∑ p ∈ headPrimes29, headPrimeFullRowDefect p) +
        57 * ((1 / 31 : ℚ) ^ 2) < 1 := by
    decide +kernel
  have hlt : (57 : ℚ) < (E.card : ℚ) := by
    by_contra hle
    have hle' : (E.card : ℚ) ≤ 57 := not_lt.mp hle
    have hmul : ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) ≤ 57 * ((1 / 31 : ℚ) ^ 2) := by linarith
    linarith
  have hlt_nat : 57 < E.card := by exact_mod_cast hlt
  omega

theorem semiprime_set_card_ge_fifty_eight_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    58 ≤ S.card := by
  obtain ⟨E, hE, hprod⟩ := Erdos306.PrimeIncidence.semiprime_set_is_prime_edge_image S hS
  have hcard : S.card = E.card := by
    rw [← hprod, Finset.card_image_of_injOn (Erdos306.Representation.product_injOn_prime_edges E hE)]
  have hdegE : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10 := by
    intro p hp
    have hcount := Erdos306.Representation.degree_eq_divisible_denominators E hE p hp
    change incidenceDegree E p = _ at hcount
    rw [hprod] at hcount
    rw [hcount]
    exact hdeg p hp
  have hsumImage := Erdos306.Representation.reciprocal_sum_image_prime_edges E hE
  rw [hprod] at hsumImage
  have hsumE : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 := by
    have hcast :
        (∑ e ∈ E, (1 : ℚ) / (e.1 * e.2 : ℕ)) =
          ∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro e _
      push_cast
      rfl
    rw [← hcast, ← hsumImage]
    exact hsum
  rw [hcard]
  exact prime_edges_card_ge_fifty_eight_of_sum_eq_one E hE hdegE hsumE

theorem semiprime_set_card_ge_fifty_seven_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    57 ≤ S.card :=
  le_trans (by decide : 57 ≤ 58) (semiprime_set_card_ge_fifty_eight_of_sum_eq_one S hS hdeg hsum)

/-! ## Part 3: Two-Parameter Lagrangian Degree-Slack Bounds and Multi-Tail `P_61` Witnesses (`|E| = 70, 71, 75`) -/

theorem two_beta_lagrangian_defect_bounds
    (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (β₁ β₂ B : ℚ) (d K : ℕ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hcard : E.card ≤ K)
    (hsum : (∑ p ∈ V, additiveRowDefect lam s d p (graphNeighbors E p)) ≤ B) :
    (∑ p ∈ V, lagrangianRowDefect lam s β₁ d p (graphNeighbors E p)) ≤
      B - β₁ * ((d : ℚ) * (V.card : ℚ) - 2 * (K : ℚ)) ∧
    (∑ p ∈ V, lagrangianRowDefect lam s β₂ d p (graphNeighbors E p)) ≤
      B - β₂ * ((d : ℚ) * (V.card : ℚ) - 2 * (K : ℚ)) :=
  ⟨sum_lagrangianRowDefect_le_of_card_le lam s β₁ B d K E V hE hend hβ₁ hcard hsum,
   sum_lagrangianRowDefect_le_of_card_le lam s β₂ B d K E V hE hend hβ₂ hcard hsum⟩

theorem headPrimes29_defect_hierarchy_controls :
    (∑ p ∈ headPrimes29, headPrimeMinRowDefect p) = 32598097668 / 7668096072637 ∧
    (∑ p ∈ headPrimes29, headPrimeFullRowDefect p) = 112460475104 / 23004288217911 ∧
    (587819031103 / 621737519403 : ℚ) - 5780631383008 / 943175816934351 +
      58 * ((1 / 31 : ℚ) ^ 2) < 1 ∧
    (587819031103 / 621737519403 : ℚ) - 2481617415778664 / 307071098113340847 +
      60 * ((1 / 31 : ℚ) ^ 2) < 1 := by
  decide +kernel

def witnessEdges70Cell011 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 37), (7, 41), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 23), (13, 37), (13, 59), (17, 31), (17, 37), (17, 43), (17, 47), (19, 23),
   (19, 29), (19, 43), (19, 47), (23, 31), (23, 37), (23, 41), (29, 59), (29, 61), (31, 37), (31, 43),
   (31, 61), (37, 41), (37, 43), (37, 47), (37, 61), (41, 43), (41, 47), (41, 61), (43, 59), (43, 61)}

def witnessEdges70Cell101 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 23), (13, 41), (13, 53), (17, 31), (17, 37), (17, 43), (17, 47), (19, 29),
   (19, 37), (19, 41), (19, 53), (23, 31), (23, 47), (23, 53), (23, 61), (29, 31), (29, 43), (29, 47),
   (29, 61), (31, 37), (31, 41), (37, 41), (37, 47), (41, 43), (43, 47), (43, 53), (47, 53), (47, 61)}

def witnessEdges70Cell110 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 29), (13, 37), (13, 43), (17, 19), (17, 31), (17, 41), (17, 59), (19, 29),
   (19, 41), (19, 43), (23, 31), (23, 47), (29, 31), (29, 43), (29, 47), (29, 59), (31, 41), (31, 47),
   (31, 53), (37, 41), (37, 43), (37, 53), (41, 43), (41, 47), (41, 53), (43, 47), (47, 53), (47, 59)}

def witnessEdges70Cell111 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 23), (13, 37), (13, 59), (17, 23), (17, 37), (17, 41), (17, 53), (19, 29),
   (19, 31), (19, 37), (23, 31), (23, 43), (23, 61), (29, 37), (29, 41), (29, 47), (29, 53), (29, 59),
   (31, 37), (31, 47), (31, 53), (31, 59), (37, 43), (37, 61), (41, 43), (47, 61), (53, 61), (59, 61)}

def witnessEdges71Cell110 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 37),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 29), (13, 37), (13, 43), (17, 19), (17, 23), (17, 37), (17, 41), (19, 31),
   (19, 41), (19, 47), (23, 29), (23, 47), (23, 53), (23, 59), (29, 31), (29, 37), (29, 41), (29, 53),
   (31, 37), (31, 41), (31, 47), (31, 53), (31, 59), (37, 43), (41, 43), (41, 53), (43, 53), (43, 59),
   (53, 59)}

def witnessEdges75Cell100 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 37),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 37), (7, 41), (11, 13), (11, 17), (11, 19), (11, 31), (11, 37), (11, 53),
   (13, 19), (13, 23), (13, 37), (13, 41), (13, 47), (17, 19), (17, 29), (17, 31), (17, 41), (17, 53),
   (19, 29), (19, 41), (19, 43), (23, 29), (23, 31), (23, 41), (23, 43), (23, 47), (29, 31), (29, 37),
   (29, 41), (29, 43), (29, 47), (31, 43), (31, 47), (31, 53), (37, 41), (37, 43), (37, 47), (37, 53),
   (41, 43), (41, 53), (43, 47), (43, 53), (47, 53)}

theorem witnessEdges70Cell011_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges70Cell011,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges70Cell011, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges70Cell011.card = 70 ∧
      incidenceDegree witnessEdges70Cell011 53 = 0 ∧
      incidenceDegree witnessEdges70Cell011 59 = 3 ∧
      incidenceDegree witnessEdges70Cell011 61 = 5 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges70Cell011 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges70Cell011 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges70Cell011 (primorial47 * 59 * 61)
    (by decide) (by decide) (by decide)

theorem witnessEdges70Cell101_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges70Cell101,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges70Cell101, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges70Cell101.card = 70 ∧
      incidenceDegree witnessEdges70Cell101 53 = 6 ∧
      incidenceDegree witnessEdges70Cell101 59 = 0 ∧
      incidenceDegree witnessEdges70Cell101 61 = 3 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges70Cell101 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges70Cell101 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges70Cell101 (primorial47 * 53 * 61)
    (by decide) (by decide) (by decide)

theorem witnessEdges70Cell110_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges70Cell110,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges70Cell110, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges70Cell110.card = 70 ∧
      incidenceDegree witnessEdges70Cell110 53 = 5 ∧
      incidenceDegree witnessEdges70Cell110 59 = 3 ∧
      incidenceDegree witnessEdges70Cell110 61 = 0 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges70Cell110 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges70Cell110 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges70Cell110 (primorial47 * 53 * 59)
    (by decide) (by decide) (by decide)

theorem witnessEdges70Cell111_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges70Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges70Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges70Cell111.card = 70 ∧
      incidenceDegree witnessEdges70Cell111 53 = 5 ∧
      incidenceDegree witnessEdges70Cell111 59 = 4 ∧
      incidenceDegree witnessEdges70Cell111 61 = 5 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges70Cell111 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges70Cell111 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges70Cell111 (primorial47 * 53 * 59 * 61)
    (by decide) (by decide) (by decide)

def multiTailWitness70 (c : Fin 4) : Finset (ℕ × ℕ) :=
  if c = 0 then witnessEdges70Cell011
  else if c = 1 then witnessEdges70Cell101
  else if c = 2 then witnessEdges70Cell110
  else witnessEdges70Cell111

theorem exists_card_seventy_witness_in_every_multi_tail_cell
    (c : Fin 4) (d : ℕ) (hd : 10 ≤ d) :
    let E := multiTailWitness70 c
    (∀ e ∈ E, e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      E.card = 70 ∧
      2 ≤ (({53, 59, 61} : Finset ℕ).filter (fun p => incidenceDegree E p ≠ 0)).card ∧
      ∀ p ∈ primes61, incidenceDegree E p ≤ d := by
  fin_cases c
  · have h := witnessEdges70Cell011_valid_and_sum_eq_one d hd
    exact ⟨h.1, h.2.1, h.2.2.1, by decide, h.2.2.2.2.2.2⟩
  · have h := witnessEdges70Cell101_valid_and_sum_eq_one d hd
    exact ⟨h.1, h.2.1, h.2.2.1, by decide, h.2.2.2.2.2.2⟩
  · have h := witnessEdges70Cell110_valid_and_sum_eq_one d hd
    exact ⟨h.1, h.2.1, h.2.2.1, by decide, h.2.2.2.2.2.2⟩
  · have h := witnessEdges70Cell111_valid_and_sum_eq_one d hd
    exact ⟨h.1, h.2.1, h.2.2.1, by decide, h.2.2.2.2.2.2⟩

theorem witnessEdges71Cell110_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges71Cell110,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges71Cell110, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges71Cell110.card = 71 ∧
      ¬ 2 ∣ witnessEdges71Cell110.card ∧
      incidenceDegree witnessEdges71Cell110 53 = 7 ∧
      incidenceDegree witnessEdges71Cell110 59 = 4 ∧
      incidenceDegree witnessEdges71Cell110 61 = 0 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges71Cell110 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges71Cell110 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, by decide,
    fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges71Cell110 (primorial47 * 53 * 59)
    (by decide) (by decide) (by decide)

theorem witnessEdges75Cell100_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges75Cell100,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges75Cell100, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges75Cell100.card = 75 ∧
      ¬ 2 ∣ witnessEdges75Cell100.card ∧
      incidenceDegree witnessEdges75Cell100 53 = 7 ∧
      incidenceDegree witnessEdges75Cell100 59 = 0 ∧
      incidenceDegree witnessEdges75Cell100 61 = 0 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges75Cell100 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges75Cell100 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, by decide,
    fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges75Cell100 (primorial47 * 53)
    (by decide) (by decide) (by decide)

end Erdos306.PrimeResidueAndRowPotential

