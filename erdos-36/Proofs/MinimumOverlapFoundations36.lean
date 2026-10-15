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

public import Mathlib
@[expose] public section
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open scoped Topology BigOperators
open Filter
namespace Erdos36.Proofs

/--
The number of solutions to the equation $a - b = k$, for $a \in A$ and $b \in B$.
This represents the "overlap" between sets $A$ and $B$ for a given difference $k$.
-/
def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A.product B).filter <| fun (a, b) => a - b = k).card

/--
The maximum overlap for a given pair of sets $A$ and $B$,
taken over all possible integer differences $k$.
-/
noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ := iSup <| Overlap A B

/--
Let $A$ and $B$ be two complementary subsets, a splitting of the numbers $\{1, 2, \dots, 2n\}$,
such that both have the same cardinality $n$.
Define $M(n)$ to be the minimum `MaxOverlap` that can be achieved,
ranging over all such partitions $(A, B)$.
-/
noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

/--
The quotient of the minimum maximum overlap $M(N)$ by $N$. The central question of the
minimum overlap problem is to determine the asymptotic behavior of this quotient as $N \to \infty$.
-/
noncomputable def MinOverlapQuotient (N : ℕ) : ℝ := (M N : ℝ) / N

/-- Every pair `(a, b) ∈ A × B` contributes to `Overlap A B (a - b)`. -/
theorem one_le_overlap {A B : Finset ℤ} {a b : ℤ}
    (ha : a ∈ A) (hb : b ∈ B) : 1 ≤ Overlap A B (a - b) :=
  Finset.card_pos.mpr ⟨(a, b), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩

/-- For a fixed difference `k`, the first coordinate determines the second, so an overlap is
never larger than `A.card`. -/
theorem overlap_le_card_left (A B : Finset ℤ) (k : ℤ) : Overlap A B k ≤ A.card := by
  refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp q hq h => ?_)
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · obtain ⟨-, hpk⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hqk⟩ := Finset.mem_filter.mp hq
    exact Prod.ext h (by omega)

/-- The range of `Overlap A B` is bounded above by `A.card`. -/
theorem bddAbove_range_overlap (A B : Finset ℤ) :
    BddAbove (Set.range (Overlap A B)) := by
  refine ⟨A.card, ?_⟩
  rintro x ⟨k, rfl⟩
  exact overlap_le_card_left A B k

/-- Every individual overlap `Overlap A B k` is bounded above by `MaxOverlap A B`. -/
theorem overlap_le_maxOverlap (A B : Finset ℤ) (k : ℤ) :
    Overlap A B k ≤ MaxOverlap A B :=
  le_ciSup (bddAbove_range_overlap A B) k

/-- `MaxOverlap A B` is bounded above by `A.card`. -/
theorem maxOverlap_le_card_left (A B : Finset ℤ) : MaxOverlap A B ≤ A.card :=
  ciSup_le fun k => overlap_le_card_left A B k

/-- An overlap can only be nonzero for a difference that is actually realised in `A - B`. -/
theorem overlap_eq_zero_of_notMem_sub (A B : Finset ℤ) {k : ℤ}
    (hk : k ∉ (A ×ˢ B).image fun p => p.1 - p.2) : Overlap A B k = 0 := by
  rw [Overlap, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨a, b⟩ hab rfl
  exact hk (Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩)

/-- `MaxOverlap` as a supremum over the finite set of differences `(A ×ˢ B).image (p.1 - p.2)`. -/
theorem maxOverlap_eq_sup (A B : Finset ℤ) :
    MaxOverlap A B = ((A ×ˢ B).image fun p => p.1 - p.2).sup (Overlap A B) := by
  refine le_antisymm (ciSup_le fun k => ?_) (Finset.sup_le fun k _ => ?_)
  · by_cases hk : k ∈ (A ×ˢ B).image fun p => p.1 - p.2
    · exact Finset.le_sup hk
    · simp [overlap_eq_zero_of_notMem_sub A B hk]
  · exact le_ciSup (bddAbove_range_overlap A B) k

/-- Symmetry of `Overlap` under negation of `k` and swapping of `A` and `B`:
`(a, b) ↦ (b, a)` maps `{a ∈ A, b ∈ B | a - b = -k}` bijectively onto `{b ∈ B, a ∈ A | b - a = k}`. -/
theorem overlap_neg (A B : Finset ℤ) (k : ℤ) :
    Overlap A B (-k) = Overlap B A k := by
  unfold Overlap
  refine Finset.card_bij (fun p _ => (p.2, p.1))
    (fun p hp => ?_) (fun p₁ _ p₂ _ h => ?_) (fun q hq => ?_)
  · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by omega⟩
  · exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
  · obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
    obtain ⟨hb, ha⟩ := Finset.mem_product.mp hq1
    refine ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, by omega⟩, rfl⟩

/-- For disjoint sets `A` and `B`, there are no solutions to `a - b = 0`, so `Overlap A B 0 = 0`. -/
theorem overlap_zero_eq_zero_of_disjoint {A B : Finset ℤ} (hdisj : Disjoint A B) :
    Overlap A B 0 = 0 := by
  rw [Overlap, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨a, b⟩ hab hsub
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  have hab_eq : a = b := by omega
  subst hab_eq
  exact Finset.disjoint_left.mp hdisj ha hb

/-- Support bound: if `A, B ⊆ Finset.Icc 1 (2 * n)`, then `Overlap A B k = 0` outside
`[-(2 * n - 1), 2 * n - 1]`. -/
theorem overlap_eq_zero_of_notMem_Icc {n : ℕ} {A B : Finset ℤ}
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    {k : ℤ} (hk : k ∉ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1)) :
    Overlap A B k = 0 := by
  apply overlap_eq_zero_of_notMem_sub
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, rfl⟩
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  have haI := Finset.mem_Icc.mp (hA ha)
  have hbI := Finset.mem_Icc.mp (hB hb)
  apply hk
  rw [Finset.mem_Icc]
  omega

/-- Total sum of `Overlap A B k` over `k ∈ [-(2 * n - 1), 2 * n - 1]` equals `|A| * |B|`
whenever `A, B ⊆ [1, 2 * n]`. -/
theorem sum_overlap_Icc_eq_card_mul {n : ℕ} {A B : Finset ℤ}
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n)) :
    ∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1), Overlap A B k = A.card * B.card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun p : ℤ × ℤ => p.1 - p.2)
    (s := A ×ˢ B)
    (t := Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1))
    (fun p hp => by
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      have haI := Finset.mem_Icc.mp (hA ha)
      have hbI := Finset.mem_Icc.mp (hB hb)
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega)
  rw [Finset.card_product] at h
  exact h.symm

/-- The pairs `M n` ranges over are exactly the `n`-element subsets of `{1, …, 2n}`, each paired
with its complement. -/
theorem M_eq_image (n : ℕ) :
    M n = sInf ((fun A : Finset ℤ => MaxOverlap A (Finset.Icc (1 : ℤ) (2 * n) \ A)) ''
      {A | A ⊆ Finset.Icc (1 : ℤ) (2 * n) ∧ A.card = n}) := by
  rw [M]
  congr 1
  ext m
  constructor
  · rintro ⟨A, B, hdisj, hunion, hcard, rfl⟩
    have hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
    have hB : B = Finset.Icc (1 : ℤ) (2 * n) \ A := by
      rw [← hunion, Finset.union_sdiff_cancel_left hdisj]
    have hn : A.card = n := by
      have := Finset.card_union_of_disjoint hdisj
      rw [hunion] at this
      simp only [Int.card_Icc] at this
      omega
    exact ⟨A, ⟨hA, hn⟩, by simp only [← hB]⟩
  · rintro ⟨A, ⟨hA, hn⟩, rfl⟩
    refine ⟨A, Finset.Icc (1 : ℤ) (2 * n) \ A, Finset.disjoint_sdiff, ?_, ?_, rfl⟩
    · rw [Finset.union_sdiff_of_subset hA]
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hA, Int.card_Icc, hn]
      omega

/-- Computable stand-in for `MaxOverlap`. -/
def maxOverlapC (A B : Finset ℤ) : ℕ :=
  ((A ×ˢ B).image fun p => p.1 - p.2).sup (Overlap A B)

theorem maxOverlap_eq_maxOverlapC (A B : Finset ℤ) :
    MaxOverlap A B = maxOverlapC A B := maxOverlap_eq_sup A B

/-- The `n`-element subsets of `{1, …, 2n}`. -/
def parts (n : ℕ) : Finset (Finset ℤ) :=
  letI : Preorder ℤ := Int.instLinearOrder.toPreorder
  (Finset.Icc (1 : ℤ) (2 * n)).powerset.filter fun A => A.card = n

theorem mem_parts {n : ℕ} {A : Finset ℤ} :
    A ∈ parts n ↔ A ⊆ Finset.Icc (1 : ℤ) (2 * n) ∧ A.card = n := by
  simp [parts, Finset.mem_filter, Finset.mem_powerset]

theorem parts_nonempty (n : ℕ) : (parts n).Nonempty := by
  refine ⟨Finset.Icc (1 : ℤ) n, mem_parts.mpr ⟨?_, ?_⟩⟩
  · exact Finset.Icc_subset_Icc le_rfl (by omega)
  · rw [Int.card_Icc]; omega

/-- `M n` as the minimum of a `Finset` of naturals. -/
theorem M_eq_min_parts (n : ℕ) :
    M n = ((parts n).image fun A => maxOverlapC A (Finset.Icc (1 : ℤ) (2 * n) \ A)).min'
      ((parts_nonempty n).image _) := by
  rw [M_eq_image, ← Finset.Nonempty.csInf_eq_min']
  congr 1
  rw [Finset.coe_image,
    show ((parts n : Finset (Finset ℤ)) : Set (Finset ℤ))
        = {A | A ⊆ Finset.Icc (1 : ℤ) (2 * n) ∧ A.card = n} from by ext A; simp [mem_parts]]
  exact Set.image_congr fun A _ => maxOverlap_eq_maxOverlapC _ _

/-- `MaxOverlap {1} {2} = 1`: the only nonzero overlap is at `k = -1`. -/
theorem maxOverlap_singleton_one_two :
    MaxOverlap ({1} : Finset ℤ) ({2} : Finset ℤ) = 1 := by
  apply le_antisymm
  · rw [show (1 : ℕ) = ({(1, 2)} : Finset (ℤ × ℤ)).card from by decide]
    refine ciSup_le ?_
    intro k
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hp1, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
    simp only [Finset.mem_singleton] at ha hb
    exact Finset.mem_singleton.mpr (Prod.ext ha hb)
  · refine le_ciSup_of_le ?_ (-1) ?_
    · refine ⟨1, ?_⟩
      rintro x ⟨k, rfl⟩
      exact (Finset.card_filter_le _ _).trans (by decide)
    · decide

/-- Exact value $M(1) = 1$. -/
theorem M_one : M 1 = 1 := by
  apply le_antisymm
  · apply Nat.sInf_le
    refine ⟨{1}, {2}, by decide, by decide, by decide, maxOverlap_singleton_one_two⟩
  · apply le_csInf
    · exact ⟨_, {1}, {2}, by decide, by decide, by decide,
        maxOverlap_singleton_one_two⟩
    rintro x ⟨A, B, hd, hu, hsc, rfl⟩
    have hcardsum : A.card + B.card = 2 := by
      rw [← Finset.card_union_of_disjoint hd, hu]; decide
    have hca : A.card = 1 := by omega
    have hcb : B.card = 1 := by omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hca
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hcb
    refine le_ciSup_of_le ?_ (a - b) ?_
    · refine ⟨1, ?_⟩
      rintro x ⟨k, rfl⟩
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.product_eq_sprod, Finset.card_product,
        Finset.card_singleton, Finset.card_singleton]
    · exact one_le_overlap (Finset.mem_singleton.mpr rfl)
        (Finset.mem_singleton.mpr rfl)

/-- Exact value $M(2) = 1$. -/
theorem M_two : M 2 = 1 := by
  rw [M_eq_min_parts]
  decide

/-- Exact value $M(3) = 2$. -/
theorem M_three : M 3 = 2 := by
  rw [M_eq_min_parts]
  decide

/-- Pointwise overlap upper bound for Erdős's middle-half interval $A = [\lfloor n/2 \rfloor + 1, \lfloor n/2 \rfloor + n]$. -/
theorem e36_overlap (n : ℕ) (k : ℤ) :
    Overlap (Finset.Icc ((n / 2 : ℕ) + 1 : ℤ) ((n / 2 : ℕ) + n))
      (Finset.Icc (1 : ℤ) (2 * n) \ Finset.Icc ((n / 2 : ℕ) + 1 : ℤ) ((n / 2 : ℕ) + n)) k ≤
      n - n / 2 := by
  set h : ℕ := n / 2 with hh
  unfold Overlap
  rcases le_or_gt k 0 with hk | hk
  · calc _ ≤ (Finset.Icc ((h : ℤ) + n + 1) (2 * n)).card := by
          apply Finset.card_le_card_of_injOn (fun p => p.2)
          · intro p hp
            obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
            obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
            simp only [Finset.mem_Icc, Finset.mem_sdiff] at ha hb
            simp only [Finset.coe_Icc, Set.mem_Icc]
            omega
          · intro p hp q hq hpq
            simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
            simp only at hpq
            exact Prod.ext (by omega) hpq
      _ ≤ n - h := by rw [Int.card_Icc]; omega
  · calc _ ≤ (Finset.Icc (1 : ℤ) h).card := by
          apply Finset.card_le_card_of_injOn (fun p => p.2)
          · intro p hp
            obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
            obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
            simp only [Finset.mem_Icc, Finset.mem_sdiff] at ha hb
            simp only [Finset.coe_Icc, Set.mem_Icc]
            omega
          · intro p hp q hq hpq
            simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
            simp only at hpq
            exact Prod.ext (by omega) hpq
      _ ≤ n - h := by rw [Int.card_Icc]; omega

/-- Universal middle-interval upper bound $M(n) \le n - \lfloor n/2 \rfloor$. -/
theorem e36_M_le (n : ℕ) : M n ≤ n - n / 2 := by
  rw [M_eq_image]
  refine le_trans (Nat.sInf_le ⟨Finset.Icc ((n / 2 : ℕ) + 1 : ℤ) ((n / 2 : ℕ) + n), ⟨?_, ?_⟩, rfl⟩) ?_
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · rw [Int.card_Icc]; omega
  · exact ciSup_le fun k => e36_overlap n k

/-- Erdős's 1955 asymptotic upper bound $\limsup_{N \to \infty} M(N)/N \le 1/2$. -/
theorem minimum_overlap_variants_upper_erdos_1955 :
    atTop.limsup MinOverlapQuotient ≤ (1 : ℝ) / 2 := by
  have hnn : ∀ n, 0 ≤ MinOverlapQuotient n := fun n => by unfold MinOverlapQuotient; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  apply Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop hnn)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM : (M n : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
    have h1 := e36_M_le n
    have h2 : 2 * (n - n / 2) ≤ n + 1 := by omega
    have h3 : ((2 * (n - n / 2) : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h2
    have h4 : (M n : ℝ) ≤ ((n - n / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  unfold MinOverlapQuotient
  rw [div_le_iff₀ hn0]
  have hNn : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hεn : 1 < ε * n := by
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  nlinarith
/-- The $4n - 2$ nonzero integer differences in $[-(2n - 1), 2n - 1] \setminus \{0\}$. -/
def nonzeroDiffs (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1)).erase 0

/-- For $n \ge 1$, $0$ lies in the difference interval $[-(2n - 1), 2n - 1]$. -/
theorem zero_mem_Icc_diffs {n : ℕ} (hn : 1 ≤ n) :
    (0 : ℤ) ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1) := by
  rw [Finset.mem_Icc]
  omega

/-- For $n \ge 1$, there are exactly $4n - 2$ nonzero differences in $[-(2n - 1), 2n - 1]$. -/
theorem card_nonzeroDiffs {n : ℕ} (hn : 1 ≤ n) :
    (nonzeroDiffs n).card = 4 * n - 2 := by
  unfold nonzeroDiffs
  rw [Finset.card_erase_of_mem (zero_mem_Icc_diffs hn), Int.card_Icc]
  omega

/-- For disjoint $A, B \subseteq [1, 2n]$, the sum of `Overlap A B k` over the nonzero differences
`nonzeroDiffs n` equals `A.card * B.card`. -/
theorem sum_overlap_nonzeroDiffs_eq_card_mul {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n)) :
    ∑ k ∈ nonzeroDiffs n, Overlap A B k = A.card * B.card := by
  unfold nonzeroDiffs
  rw [← sum_overlap_Icc_eq_card_mul hA hB]
  exact Finset.sum_erase _ (overlap_zero_eq_zero_of_disjoint hdisj)

/-- Universal pigeonhole bound for any disjoint $A, B \subseteq [1, 2n]$ ($n \ge 1$):
`A.card * B.card ≤ (4 * n - 2) * MaxOverlap A B`. -/
theorem card_mul_le_four_mul_sub_two_mul_maxOverlap {n : ℕ} {A B : Finset ℤ}
    (hn : 1 ≤ n) (hdisj : Disjoint A B)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n)) :
    A.card * B.card ≤ (4 * n - 2) * MaxOverlap A B := by
  rw [← sum_overlap_nonzeroDiffs_eq_card_mul hdisj hA hB, ← card_nonzeroDiffs hn, ← smul_eq_mul]
  exact Finset.sum_le_card_nsmul (nonzeroDiffs n) (Overlap A B) (MaxOverlap A B)
    (fun k _ => overlap_le_maxOverlap A B k)

/-- Universal pigeonhole lower bound for any disjoint $A, B \subseteq [1, 2n]$ with $|A| = |B| = n$:
`n ^ 2 ≤ (4 * n - 2) * MaxOverlap A B`. -/
theorem sq_le_four_mul_sub_two_mul_maxOverlap {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    (hA_card : A.card = n) (hB_card : B.card = n) :
    n ^ 2 ≤ (4 * n - 2) * MaxOverlap A B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := card_mul_le_four_mul_sub_two_mul_maxOverlap hn hdisj hA hB
    rwa [hA_card, hB_card, ← sq] at h

/-- Universal pigeonhole lower bound on $M(n)$: for all $n \in \mathbb{N}$,
`n ^ 2 ≤ (4 * n - 2) * M n`. -/
theorem sq_le_four_mul_sub_two_mul_M (n : ℕ) :
    n ^ 2 ≤ (4 * n - 2) * M n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hne : ({MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
      (_disjoint : Disjoint A B)
      (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
      (_same_card : A.card = B.card)}).Nonempty := by
      refine ⟨_, Finset.Icc (1 : ℤ) n, Finset.Icc (1 : ℤ) (2 * n) \ Finset.Icc (1 : ℤ) n,
        Finset.disjoint_sdiff, ?_, ?_, rfl⟩
      · exact Finset.union_sdiff_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.Icc_subset_Icc le_rfl (by omega)),
          Int.card_Icc, Int.card_Icc]
        omega
    obtain ⟨A, B, hdisj, hunion, hsame, hM⟩ := Nat.sInf_mem hne
    have hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
    have hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
    have hcard_sum : A.card + B.card = 2 * n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
      omega
    have hA_card : A.card = n := by omega
    have hB_card : B.card = n := by omega
    unfold M
    rw [← hM]
    exact sq_le_four_mul_sub_two_mul_maxOverlap hdisj hA hB hA_card hB_card

/-- Strict quarter lower bound on $M(n)$ for all $n \ge 1$: `n < 4 * M n`. -/
theorem lt_four_mul_M {n : ℕ} (hn : 1 ≤ n) : n < 4 * M n := by
  have h := sq_le_four_mul_sub_two_mul_M n
  have h1 : (4 * n - 2) * M n + 2 * M n = 4 * n * M n := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  nlinarith

/-- For every $n \ge 1$, the minimum overlap quotient strictly exceeds $1/4$:
`(1 : ℝ) / 4 < MinOverlapQuotient n`. -/
theorem one_quarter_lt_minOverlapQuotient {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) / 4 < MinOverlapQuotient n := by
  unfold MinOverlapQuotient
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lt_div_iff₀ hn0]
  have hlt : (n : ℝ) < 4 * (M n : ℝ) := by exact_mod_cast lt_four_mul_M hn
  linarith

/-- Pointwise upper bound `MinOverlapQuotient n ≤ 1` for all $n \in \mathbb{N}$. -/
theorem minOverlapQuotient_le_one (n : ℕ) : MinOverlapQuotient n ≤ 1 := by
  unfold MinOverlapQuotient
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_one hn0]
    have hle : M n ≤ n := (e36_M_le n).trans (by omega)
    exact_mod_cast hle

/-- Erdős's 1955 asymptotic lower bound: $1/4 \le \liminf_{N \to \infty} M(N)/N$. -/
theorem minimum_overlap_variants_lower_erdos_1955 :
    (1 : ℝ) / 4 ≤ atTop.liminf MinOverlapQuotient := by
  apply Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le atTop minOverlapQuotient_le_one)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact le_of_lt (one_quarter_lt_minOverlapQuotient hn)

/-- Universal ceiling-half upper bound: $M(n) \le (n + 1) / 2 = \lceil n / 2 \rceil$ for all $n$. -/
theorem M_le_add_one_div_two (n : ℕ) : M n ≤ (n + 1) / 2 := by
  have h := e36_M_le n
  omega

/-- Algebraic proof of $M(2) = 1$ from the universal pigeonhole lower bound and middle-half upper bound. -/
theorem M_two_eq : M 2 = 1 := by
  have hlb := sq_le_four_mul_sub_two_mul_M 2
  have hub := M_le_add_one_div_two 2
  omega

/-- For $A, B \subseteq [1, 2n]$ and $k \in \mathbb{N}$, every pair $(a, b) \in A \times B$
with $a - b = k$ has $b = a - k \in B \cap [1, 2n - k]$, so
`Overlap A B k ≤ (B ∩ Icc 1 (2n - k)).card`. -/
theorem overlap_le_card_inter_Icc_sub {n : ℕ} {A B : Finset ℤ}
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    {k : ℕ} :
    Overlap A B (k : ℤ) ≤ (B ∩ Finset.Icc (1 : ℤ) (2 * (n : ℤ) - k)).card := by
  unfold Overlap
  refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) (fun p hp q hq h => ?_)
  · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
    have haI := Finset.mem_Icc.mp (hA ha)
    have hbI := Finset.mem_Icc.mp (hB hb)
    simp only [Finset.mem_coe, Finset.mem_inter, Finset.mem_Icc]
    exact ⟨hb, by omega, by omega⟩
  · obtain ⟨_, hp2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    obtain ⟨_, hq2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    exact Prod.ext (by omega) h

/-- Universal boundary-decay inequality: for disjoint $A, B \subseteq [1, 2n]$ and $k \le 2n$,
`Overlap A B k + Overlap A B (-k) ≤ 2 * n - k`. -/
theorem overlap_add_overlap_neg_le_sub {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    {k : ℕ} (hk : k ≤ 2 * n) :
    Overlap A B (k : ℤ) + Overlap A B (-(k : ℤ)) ≤ 2 * n - k := by
  rw [overlap_neg]
  have h1 := overlap_le_card_inter_Icc_sub hA hB (k := k)
  have h2 := overlap_le_card_inter_Icc_sub hB hA (k := k)
  set I : Finset ℤ := Finset.Icc (1 : ℤ) (2 * (n : ℤ) - k)
  have hdisjI : Disjoint (B ∩ I) (A ∩ I) :=
    hdisj.symm.mono Finset.inter_subset_left Finset.inter_subset_left
  have hunion : (B ∩ I) ∪ (A ∩ I) ⊆ I :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have hcardI : I.card = 2 * n - k := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  calc Overlap A B (k : ℤ) + Overlap B A (k : ℤ)
      ≤ (B ∩ I).card + (A ∩ I).card := add_le_add h1 h2
    _ = ((B ∩ I) ∪ (A ∩ I)).card := (Finset.card_union_of_disjoint hdisjI).symm
    _ ≤ I.card := Finset.card_le_card hunion
    _ = 2 * n - k := hcardI

/-- Combined cap-and-decay bound: for disjoint $A, B \subseteq [1, 2n]$ and $k \le 2n$,
`Overlap A B k + Overlap A B (-k) ≤ min (2 * MaxOverlap A B) (2 * n - k)`. -/
theorem overlap_add_overlap_neg_le_min {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    {k : ℕ} (hk : k ≤ 2 * n) :
    Overlap A B (k : ℤ) + Overlap A B (-(k : ℤ)) ≤
      min (2 * MaxOverlap A B) (2 * n - k) := by
  refine le_min ?_ (overlap_add_overlap_neg_le_sub hdisj hA hB hk)
  have h1 := overlap_le_maxOverlap A B (k : ℤ)
  have h2 := overlap_le_maxOverlap A B (-(k : ℤ))
  omega

/-- Folding a symmetric integer interval sum `∑ k ∈ Icc (-m) m, f k` with `f 0 = 0`
into a sum over `k ∈ range m` of `f (k + 1) + f (-(k + 1))`. -/
theorem sum_Icc_neg_eq_sum_range (f : ℤ → ℕ) (hf0 : f 0 = 0) :
    ∀ m : ℕ, ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), f k =
      ∑ k ∈ Finset.range m, (f ((k : ℤ) + 1) + f (-((k : ℤ) + 1)))
  | 0 => by simp [hf0]
  | m + 1 => by
    have hsplit : Finset.Icc (-(((m + 1 : ℕ) : ℤ))) ((m + 1 : ℕ) : ℤ) =
        insert (((m + 1 : ℕ) : ℤ))
          (insert (-(((m + 1 : ℕ) : ℤ))) (Finset.Icc (-(m : ℤ)) (m : ℤ))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hm1 : (((m + 1 : ℕ) : ℤ)) ∉
        insert (-(((m + 1 : ℕ) : ℤ))) (Finset.Icc (-(m : ℤ)) (m : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hm2 : (-(((m + 1 : ℕ) : ℤ))) ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hm1, Finset.sum_insert hm2, sum_Icc_neg_eq_sum_range f hf0 m,
      Finset.sum_range_succ]
    push_cast
    omega

/-- For disjoint $A, B \subseteq [1, 2n]$, the folded sum of `Overlap A B (k + 1) + Overlap A B (-(k + 1))`
over $k \in \operatorname{range} (2n)$ equals `A.card * B.card`. -/
theorem sum_range_overlap_add_neg_eq_card_mul {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n)) :
    ∑ k ∈ Finset.range (2 * n),
      (Overlap A B (((k + 1 : ℕ) : ℤ)) + Overlap A B (-(((k + 1 : ℕ) : ℤ)))) =
        A.card * B.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hA0 : A = ∅ := Finset.subset_empty.mp (by simpa using hA)
    simp [hA0]
  · have hsum := sum_Icc_neg_eq_sum_range (Overlap A B)
      (overlap_zero_eq_zero_of_disjoint hdisj) (2 * n)
    have hcong : ∑ k ∈ Finset.range (2 * n),
        (Overlap A B (((k + 1 : ℕ) : ℤ)) + Overlap A B (-(((k + 1 : ℕ) : ℤ)))) =
      ∑ k ∈ Finset.range (2 * n),
        (Overlap A B ((k : ℤ) + 1) + Overlap A B (-((k : ℤ) + 1))) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      rfl
    rw [hcong, ← hsum]
    have hsplit : Finset.Icc (-((2 * n : ℕ) : ℤ)) ((2 * n : ℕ) : ℤ) =
        insert ((2 * n : ℕ) : ℤ)
          (insert (-((2 * n : ℕ) : ℤ))
            (Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hm1 : ((2 * n : ℕ) : ℤ) ∉
        insert (-((2 * n : ℕ) : ℤ)) (Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hm2 : (-((2 * n : ℕ) : ℤ)) ∉ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hz1 : Overlap A B ((2 * n : ℕ) : ℤ) = 0 :=
      overlap_eq_zero_of_notMem_Icc hA hB (by simp only [Finset.mem_Icc]; omega)
    have hz2 : Overlap A B (-((2 * n : ℕ) : ℤ)) = 0 :=
      overlap_eq_zero_of_notMem_Icc hA hB (by simp only [Finset.mem_Icc]; omega)
    rw [hsplit, Finset.sum_insert hm1, Finset.sum_insert hm2, hz1, hz2,
      sum_overlap_Icc_eq_card_mul hA hB]
    omega

/-- When $N \le C$, every term in `∑ k ∈ range N, min C (N - 1 - k)` equals `N - 1 - k`,
so twice the sum equals `N * (N - 1)`. -/
theorem sum_range_min_sub_of_le (C : ℕ) :
    ∀ N : ℕ, N ≤ C → 2 * ∑ k ∈ Finset.range N, min C (N - 1 - k) = N * (N - 1)
  | 0, _ => by simp
  | N + 1, hN => by
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    have hprev := sum_range_min_sub_of_le C N (by omega)
    have hmin : min C N = N := Nat.min_eq_right (by omega)
    have hcong : ∑ k ∈ Finset.range N, min C (N - (k + 1)) =
        ∑ k ∈ Finset.range N, min C (N - 1 - k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      omega
    rw [hcong, hmin, Nat.mul_add, hprev]
    rcases N with _ | N
    · simp
    · simp only [Nat.add_sub_cancel]
      ring

/-- Exact evaluation of the cap-and-decay sum for $C \le N$:
`2 * ∑ k ∈ range N, min C (N - 1 - k) + C * (C + 1) = 2 * N * C`. -/
theorem sum_range_min_sub_of_ge (C : ℕ) :
    ∀ N : ℕ, C ≤ N →
      2 * ∑ k ∈ Finset.range N, min C (N - 1 - k) + C * (C + 1) = 2 * N * C
  | N, hN => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
    clear hN
    induction d with
    | zero =>
      simp only [Nat.add_zero]
      rw [sum_range_min_sub_of_le C C le_rfl]
      rcases C with _ | C
      · simp
      · simp only [Nat.add_sub_cancel]
        ring
    | succ d ih =>
      rw [← Nat.add_assoc, Finset.sum_range_succ']
      simp only [Nat.add_sub_cancel, Nat.sub_zero]
      have hmin : min C (C + d) = C := Nat.min_eq_left (by omega)
      have hcong : ∑ k ∈ Finset.range (C + d), min C (C + d - (k + 1)) =
          ∑ k ∈ Finset.range (C + d), min C (C + d - 1 - k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        omega
      rw [hcong, hmin]
      linarith

/-- Scherk's universal quadratic lower bound for any disjoint $A, B \subseteq [1, 2n]$
with $|A| = |B| = n$:
`n ^ 2 + 2 * (MaxOverlap A B) ^ 2 + MaxOverlap A B ≤ 4 * n * MaxOverlap A B`. -/
theorem scherk_quadratic_le_maxOverlap {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    (hA_card : A.card = n) (hB_card : B.card = n) :
    n ^ 2 + 2 * (MaxOverlap A B) ^ 2 + MaxOverlap A B ≤ 4 * n * MaxOverlap A B := by
  set m := MaxOverlap A B
  have hm_le : m ≤ n := hA_card ▸ maxOverlap_le_card_left A B
  have hsum_eq : ∑ k ∈ Finset.range (2 * n),
      (Overlap A B (((k + 1 : ℕ) : ℤ)) + Overlap A B (-(((k + 1 : ℕ) : ℤ)))) = n ^ 2 := by
    rw [sum_range_overlap_add_neg_eq_card_mul hdisj hA hB, hA_card, hB_card, sq]
  have hsum_le : ∑ k ∈ Finset.range (2 * n),
      (Overlap A B (((k + 1 : ℕ) : ℤ)) + Overlap A B (-(((k + 1 : ℕ) : ℤ)))) ≤
        ∑ k ∈ Finset.range (2 * n), min (2 * m) (2 * n - 1 - k) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_lt : k < 2 * n := Finset.mem_range.mp hk
    have h1 := overlap_add_overlap_neg_le_min hdisj hA hB (k := k + 1) (by omega)
    have h2 : 2 * n - (k + 1) = 2 * n - 1 - k := by omega
    rwa [h2] at h1
  have hcap := sum_range_min_sub_of_ge (2 * m) (2 * n) (by omega)
  nlinarith

/-- Scherk's universal quadratic lower bound on $M(n)$:
for all $n \in \mathbb{N}$, `n ^ 2 + 2 * (M n) ^ 2 + M n ≤ 4 * n * M n`. -/
theorem scherk_quadratic_le_M (n : ℕ) :
    n ^ 2 + 2 * (M n) ^ 2 + M n ≤ 4 * n * M n := by
  have hne : ({MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
      (_disjoint : Disjoint A B)
      (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
      (_same_card : A.card = B.card)}).Nonempty := by
    refine ⟨_, Finset.Icc (1 : ℤ) n, Finset.Icc (1 : ℤ) (2 * n) \ Finset.Icc (1 : ℤ) n,
      Finset.disjoint_sdiff, ?_, ?_, rfl⟩
    · exact Finset.union_sdiff_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.Icc_subset_Icc le_rfl (by omega)),
        Int.card_Icc, Int.card_Icc]
      omega
  obtain ⟨A, B, hdisj, hunion, hsame, hM⟩ := Nat.sInf_mem hne
  have hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
  have hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
  have hcard_sum : A.card + B.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
    omega
  have hA_card : A.card = n := by omega
  have hB_card : B.card = n := by omega
  unfold M
  rw [← hM]
  exact scherk_quadratic_le_maxOverlap hdisj hA hB hA_card hB_card

/-- Appending $2n + 1$ to $A$ and $2n + 2$ to $B$ increases `Overlap A B k` by at most $1$
for every integer difference $k \in \mathbb{Z}$. -/
theorem overlap_insert_boundary_le {n : ℕ} {A B : Finset ℤ}
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    (k : ℤ) :
    Overlap (insert (2 * (n : ℤ) + 1) A) (insert (2 * (n : ℤ) + 2) B) k ≤
      Overlap A B k + 1 := by
  set a₀ : ℤ := 2 * (n : ℤ) + 1
  set b₀ : ℤ := 2 * (n : ℤ) + 2
  set F1 := ((insert a₀ A).product (insert b₀ B)).filter (fun p : ℤ × ℤ => p.1 - p.2 = k)
  set F := (A.product B).filter (fun p : ℤ × ℤ => p.1 - p.2 = k)
  change F1.card ≤ F.card + 1
  rcases le_or_gt 0 k with hk | hk
  · have hsub : F1 ⊆ insert (a₀, a₀ - k) F := by
      intro ⟨a, b⟩ hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
      simp only [Finset.mem_insert] at ha hb
      rcases hb with rfl | hbB
      · rcases ha with rfl | haA
        · dsimp [a₀, b₀] at hp2; omega
        · have haI := Finset.mem_Icc.mp (hA haA)
          dsimp [b₀] at hp2; omega
      · rcases ha with rfl | haA
        · rw [Finset.mem_insert]
          left
          exact Prod.ext rfl (by omega)
        · rw [Finset.mem_insert]
          right
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haA, hbB⟩, hp2⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  · have hsub : F1 ⊆ insert (b₀ + k, b₀) F := by
      intro ⟨a, b⟩ hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp1
      simp only [Finset.mem_insert] at ha hb
      rcases hb with rfl | hbB
      · rw [Finset.mem_insert]
        left
        exact Prod.ext (by omega) rfl
      · rcases ha with rfl | haA
        · have hbI := Finset.mem_Icc.mp (hB hbB)
          dsimp [a₀] at hp2; omega
        · rw [Finset.mem_insert]
          right
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haA, hbB⟩, hp2⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- Appending $2n + 1$ to $A$ and $2n + 2$ to $B$ increases `MaxOverlap A B` by at most $1$. -/
theorem maxOverlap_insert_boundary_le {n : ℕ} {A B : Finset ℤ}
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n)) :
    MaxOverlap (insert (2 * (n : ℤ) + 1) A) (insert (2 * (n : ℤ) + 2) B) ≤
      MaxOverlap A B + 1 := by
  refine ciSup_le fun k => ?_
  exact (overlap_insert_boundary_le hA hB k).trans
    (Nat.add_le_add_right (overlap_le_maxOverlap A B k) 1)

/-- Universal one-step Lipschitz upper bound: `M (n + 1) ≤ M n + 1` for all $n \in \mathbb{N}$. -/
theorem M_succ_le_M_add_one (n : ℕ) : M (n + 1) ≤ M n + 1 := by
  have hne : ({MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
      (_disjoint : Disjoint A B)
      (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
      (_same_card : A.card = B.card)}).Nonempty := by
    refine ⟨_, Finset.Icc (1 : ℤ) n, Finset.Icc (1 : ℤ) (2 * n) \ Finset.Icc (1 : ℤ) n,
      Finset.disjoint_sdiff, ?_, ?_, rfl⟩
    · exact Finset.union_sdiff_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.Icc_subset_Icc le_rfl (by omega)),
        Int.card_Icc, Int.card_Icc]
      omega
  obtain ⟨A, B, hdisj, hunion, hsame, hM⟩ := Nat.sInf_mem hne
  have hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
  have hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
  set a₀ : ℤ := 2 * (n : ℤ) + 1
  set b₀ : ℤ := 2 * (n : ℤ) + 2
  have ha₀A : a₀ ∉ A := fun h => by
    have := Finset.mem_Icc.mp (hA h); dsimp [a₀] at this; omega
  have ha₀B : a₀ ∉ B := fun h => by
    have := Finset.mem_Icc.mp (hB h); dsimp [a₀] at this; omega
  have hb₀A : b₀ ∉ A := fun h => by
    have := Finset.mem_Icc.mp (hA h); dsimp [b₀] at this; omega
  have hb₀B : b₀ ∉ B := fun h => by
    have := Finset.mem_Icc.mp (hB h); dsimp [b₀] at this; omega
  have hdisj1 : Disjoint (insert a₀ A) (insert b₀ B) := by
    rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
    refine ⟨?_, hb₀A, hdisj⟩
    simp only [Finset.mem_insert]
    rintro (h | h)
    · dsimp [a₀, b₀] at h; omega
    · exact ha₀B h
  have hunion1 : insert a₀ A ∪ insert b₀ B = Finset.Icc (1 : ℤ) (2 * (n + 1 : ℕ)) := by
    ext x
    have hxAB : x ∈ A ∨ x ∈ B ↔ 1 ≤ x ∧ x ≤ 2 * (n : ℤ) := by
      rw [← Finset.mem_union, hunion, Finset.mem_Icc]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_Icc]
    dsimp [a₀, b₀]
    constructor
    · rintro ((rfl | hxA) | (rfl | hxB))
      · omega
      · have := hxAB.mp (Or.inl hxA); omega
      · omega
      · have := hxAB.mp (Or.inr hxB); omega
    · intro hx
      by_cases hle : x ≤ 2 * (n : ℤ)
      · rcases hxAB.mpr ⟨hx.1, hle⟩ with hxA | hxB
        · exact Or.inl (Or.inr hxA)
        · exact Or.inr (Or.inr hxB)
      · have h2 : x = 2 * (n : ℤ) + 1 ∨ x = 2 * (n : ℤ) + 2 := by omega
        rcases h2 with h2 | h2
        · exact Or.inl (Or.inl h2)
        · exact Or.inr (Or.inl h2)
  have hsame1 : (insert a₀ A).card = (insert b₀ B).card := by
    rw [Finset.card_insert_of_notMem ha₀A, Finset.card_insert_of_notMem hb₀B, hsame]
  have hle : M (n + 1) ≤ MaxOverlap (insert a₀ A) (insert b₀ B) :=
    Nat.sInf_le ⟨insert a₀ A, insert b₀ B, hdisj1, hunion1, hsame1, rfl⟩
  unfold M
  rw [← hM]
  exact hle.trans (maxOverlap_insert_boundary_le hA hB)

/-- Multi-step Lipschitz upper bound: `M (n + r) ≤ M n + r` for all $n, r \in \mathbb{N}$. -/
theorem M_add_le (n : ℕ) : ∀ r : ℕ, M (n + r) ≤ M n + r
  | 0 => by simp
  | r + 1 => by
    rw [← Nat.add_assoc]
    exact (M_succ_le_M_add_one (n + r)).trans (by linarith [M_add_le n r])

/-- Explicit 14-block optimal binary step template witness $A_7 \subseteq \{1, \dots, 14\}$. -/
def stepTemplateA7 : Finset ℤ := {1, 2, 3, 6, 12, 13, 14}

/-- Complement $B_7 = \{1, \dots, 14\} \setminus A_7$. -/
def stepTemplateB7 : Finset ℤ := {4, 5, 7, 8, 9, 10, 11}

/-- Positive control: the 14-block witness $(A_7, B_7)$ achieves `MaxOverlap A_7 B_7 = 3`
(quotient $3/7 < 1/2$). -/
theorem maxOverlap_stepTemplate7 : MaxOverlap stepTemplateA7 stepTemplateB7 = 3 := by
  rw [maxOverlap_eq_maxOverlapC]
  decide

/-- Upper bound `M 7 ≤ 3` certified by the 14-block step template $(A_7, B_7)$. -/
theorem M_seven_le_three : M 7 ≤ 3 := by
  have hle : M 7 ≤ MaxOverlap stepTemplateA7 stepTemplateB7 :=
    Nat.sInf_le ⟨stepTemplateA7, stepTemplateB7, by decide, by decide, by decide, rfl⟩
  rwa [maxOverlap_stepTemplate7] at hle

/-- Lower bound `3 ≤ M 7` derived purely algebraically from Scherk's quadratic inequality
`7^2 + 2 * (M 7)^2 + M 7 ≤ 4 * 7 * M 7` (`49 + 2 * (M 7)^2 + M 7 ≤ 28 * M 7`). -/
theorem three_le_M_seven : 3 ≤ M 7 := by
  have h := scherk_quadratic_le_M 7
  nlinarith

/-- Exact value `M 7 = 3`, proved by combining the 14-block step-template upper bound
and Scherk's quadratic lower bound without brute-force powerset enumeration. -/
theorem M_seven_eq_three : M 7 = 3 :=
  le_antisymm M_seven_le_three three_le_M_seven

/-- Exact value `M 8 = 4`, proved from `M 7 = 3`, `M_succ_le_M_add_one 7`,
and Scherk's quadratic lower bound without brute-force powerset enumeration. -/
theorem M_eight_le_four : M 8 ≤ 4 := by
  have h := M_succ_le_M_add_one 7
  rw [M_seven_eq_three] at h
  exact h

/-- Explicit 18-block binary step template witness $A_9 \subseteq \{1, \dots, 18\}$. -/
def stepTemplateA9 : Finset ℤ := {1, 2, 3, 4, 7, 11, 16, 17, 18}

/-- Complement $B_9 = \{1, \dots, 18\} \setminus A_9$. -/
def stepTemplateB9 : Finset ℤ := {5, 6, 8, 9, 10, 12, 13, 14, 15}
set_option maxRecDepth 8000 in

/-- The 18-block witness $(A_9, B_9)$ achieves `MaxOverlap A_9 B_9 = 4` (quotient $4/9$). -/
theorem maxOverlap_stepTemplate9 : MaxOverlap stepTemplateA9 stepTemplateB9 = 4 := by
  rw [maxOverlap_eq_maxOverlapC]
  decide

/-- Upper bound `M 9 ≤ 4` certified by the 18-block step template $(A_9, B_9)$. -/
theorem M_nine_le_four : M 9 ≤ 4 := by
  have hle : M 9 ≤ MaxOverlap stepTemplateA9 stepTemplateB9 :=
    Nat.sInf_le ⟨stepTemplateA9, stepTemplateB9, by decide, by decide, by decide, rfl⟩
  rwa [maxOverlap_stepTemplate9] at hle

/-- Explicit 24-block binary step template witness $A_{12} \subseteq \{1, \dots, 24\}$. -/
def stepTemplateA12 : Finset ℤ := {1, 2, 3, 4, 5, 9, 14, 20, 21, 22, 23, 24}

/-- Complement $B_{12} = \{1, \dots, 24\} \setminus A_{12}$. -/
def stepTemplateB12 : Finset ℤ := {6, 7, 8, 10, 11, 12, 13, 15, 16, 17, 18, 19}
set_option maxRecDepth 8000 in

/-- The 24-block witness $(A_{12}, B_{12})$ achieves `MaxOverlap A_{12} B_{12} = 5`
(quotient $5/12 \approx 0.416667 < 3/7$). -/
theorem maxOverlap_stepTemplate12 : MaxOverlap stepTemplateA12 stepTemplateB12 = 5 := by
  rw [maxOverlap_eq_maxOverlapC]
  decide

/-- Upper bound `M 12 ≤ 5` certified by the 24-block step template $(A_{12}, B_{12})$. -/
theorem M_twelve_le_five : M 12 ≤ 5 := by
  have hle : M 12 ≤ MaxOverlap stepTemplateA12 stepTemplateB12 :=
    Nat.sInf_le ⟨stepTemplateA12, stepTemplateB12, by decide, by decide, by decide, rfl⟩
  rwa [maxOverlap_stepTemplate12] at hle

/-- Universal fiberwise weighted difference-sum identity: for any $A, B \subseteq [1, 2n]$
and any weight function $w : \mathbb{Z} \to \mathbb{R}$,
`∑ k ∈ Icc (-(2n-1)) (2n-1), w k * (Overlap A B k : ℝ) = ∑ a ∈ A, ∑ b ∈ B, w (a - b)`. -/
theorem sum_Icc_weight_mul_overlap {n : ℕ} {A B : Finset ℤ}
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    (w : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1),
      w k * (Overlap A B k : ℝ) = ∑ a ∈ A, ∑ b ∈ B, w (a - b) := by
  have hmaps : ∀ p ∈ A ×ˢ B, p.1 - p.2 ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1) := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have haI := Finset.mem_Icc.mp (hA ha)
    have hbI := Finset.mem_Icc.mp (hB hb)
    rw [Finset.mem_Icc]
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℤ × ℤ => w (p.1 - p.2))
  rw [← Finset.sum_product', ← hfib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold Overlap
  have hconst : ∑ p ∈ (A ×ˢ B).filter (fun p : ℤ × ℤ => p.1 - p.2 = k), w (p.1 - p.2) =
      ∑ _p ∈ (A ×ˢ B).filter (fun p : ℤ × ℤ => p.1 - p.2 = k), w k := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rfl

/-- First-moment difference-sum identity: for $A, B \subseteq [1, 2n]$,
`∑ k ∈ Icc (-(2n-1)) (2n-1), (k : ℝ) * (Overlap A B k : ℝ) = B.card * ∑ a ∈ A, a - A.card * ∑ b ∈ B, b`. -/
theorem sum_Icc_first_moment_overlap {n : ℕ} {A B : Finset ℤ}
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n)) :
    ∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1),
      (k : ℝ) * (Overlap A B k : ℝ) =
      (B.card : ℝ) * (∑ a ∈ A, (a : ℝ)) - (A.card : ℝ) * (∑ b ∈ B, (b : ℝ)) := by
  rw [sum_Icc_weight_mul_overlap hA hB (fun k : ℤ => (k : ℝ))]
  have h1 : ∀ a b : ℤ, ((a - b : ℤ) : ℝ) = (a : ℝ) - (b : ℝ) := fun a b => by push_cast; rfl
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]

/-- Moser's (1959) second-moment difference-sum identity: for $A, B \subseteq [1, 2n]$,
`∑ k ∈ Icc (-(2n-1)) (2n-1), (k : ℝ)^2 * (Overlap A B k : ℝ) = B.card * ∑ a ∈ A, a^2 + A.card * ∑ b ∈ B, b^2 - 2 * (∑ a ∈ A, a) * (∑ b ∈ B, b)`. -/
theorem sum_Icc_second_moment_overlap {n : ℕ} {A B : Finset ℤ}
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n)) :
    ∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1),
      (k : ℝ) ^ 2 * (Overlap A B k : ℝ) =
      (B.card : ℝ) * (∑ a ∈ A, (a : ℝ) ^ 2) + (A.card : ℝ) * (∑ b ∈ B, (b : ℝ) ^ 2) -
        2 * (∑ a ∈ A, (a : ℝ)) * (∑ b ∈ B, (b : ℝ)) := by
  rw [sum_Icc_weight_mul_overlap hA hB (fun k : ℤ => (k : ℝ) ^ 2)]
  have h1 : ∀ a b : ℤ, ((a - b : ℤ) : ℝ) ^ 2 =
      ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) - 2 * ((a : ℝ) * (b : ℝ)) := by
    intro a b
    push_cast
    ring
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring
/-- The contiguous $m$-element integer block `[(x - 1) * m + 1, x * m]` associated with $x \in \mathbb{Z}$. -/
def inflateBlock (m : ℕ) (x : ℤ) : Finset ℤ :=
  Finset.Icc ((x - 1) * (m : ℤ) + 1) (x * (m : ℤ))

/-- Block inflation $A^{(m)} = \bigcup_{x \in A} [(x - 1) m + 1, x m]$ of a finite integer set $A$. -/
def inflateSet (m : ℕ) (A : Finset ℤ) : Finset ℤ :=
  A.biUnion (inflateBlock m)

/-- Explicit membership characterization for the $m$-block `inflateBlock m x`. -/
theorem mem_inflateBlock_iff (m : ℕ) (x u : ℤ) :
    u ∈ inflateBlock m x ↔ (x - 1) * (m : ℤ) + 1 ≤ u ∧ u ≤ x * (m : ℤ) := by
  rw [inflateBlock, Finset.mem_Icc]

/-- Every inflated block `inflateBlock m x` has cardinality exactly $m$. -/
theorem card_inflateBlock (m : ℕ) (x : ℤ) :
    (inflateBlock m x).card = m := by
  rw [inflateBlock, Int.card_Icc]
  have h : x * (m : ℤ) + 1 - ((x - 1) * (m : ℤ) + 1) = (m : ℤ) := by ring
  rw [h, Int.toNat_natCast]

/-- Distinct integer centers $x \neq y$ have disjoint $m$-blocks. -/
theorem disjoint_inflateBlock_of_ne (m : ℕ) {x y : ℤ} (hxy : x ≠ y) :
    Disjoint (inflateBlock m x) (inflateBlock m y) := by
  rw [Finset.disjoint_left]
  intro u hux huy
  rw [mem_inflateBlock_iff] at hux huy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hle : x ≤ y - 1 := by omega
    have hm : (0 : ℤ) ≤ (m : ℤ) := by positivity
    have hmul : x * (m : ℤ) ≤ (y - 1) * (m : ℤ) := mul_le_mul_of_nonneg_right hle hm
    linarith
  · have hle : y ≤ x - 1 := by omega
    have hm : (0 : ℤ) ≤ (m : ℤ) := by positivity
    have hmul : y * (m : ℤ) ≤ (x - 1) * (m : ℤ) := mul_le_mul_of_nonneg_right hle hm
    linarith

/-- The family `inflateBlock m` is pairwise disjoint on any finite set $A \subseteq \mathbb{Z}$. -/
theorem pairwiseDisjoint_inflateBlock (m : ℕ) (A : Finset ℤ) :
    (A : Set ℤ).PairwiseDisjoint (inflateBlock m) := by
  intro x _ y _ hxy
  exact disjoint_inflateBlock_of_ne m hxy

/-- Block inflation scales cardinality by exactly $m$: `|A^{(m)}| = |A| * m`. -/
theorem card_inflateSet (m : ℕ) (A : Finset ℤ) :
    (inflateSet m A).card = A.card * m := by
  rw [inflateSet, Finset.card_biUnion (pairwiseDisjoint_inflateBlock m A)]
  simp [card_inflateBlock]

/-- Block inflation preserves disjointness of finite integer subsets. -/
theorem disjoint_inflateSet (m : ℕ) {A B : Finset ℤ} (hdisj : Disjoint A B) :
    Disjoint (inflateSet m A) (inflateSet m B) := by
  rw [inflateSet, inflateSet, Finset.disjoint_biUnion_left]
  intro a ha
  rw [Finset.disjoint_biUnion_right]
  intro b hb
  apply disjoint_inflateBlock_of_ne m
  rintro rfl
  exact Finset.disjoint_left.mp hdisj ha hb

/-- Block inflation commutes with finite set union. -/
theorem inflateSet_union (m : ℕ) (A B : Finset ℤ) :
    inflateSet m (A ∪ B) = inflateSet m A ∪ inflateSet m B := by
  ext u
  simp only [inflateSet, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨a, ha | hb, hu⟩
    · exact Or.inl ⟨a, ha, hu⟩
    · exact Or.inr ⟨a, hb, hu⟩
  · rintro (⟨a, ha, hu⟩ | ⟨a, hb, hu⟩)
    · exact ⟨a, Or.inl ha, hu⟩
    · exact ⟨a, Or.inr hb, hu⟩

/-- Block inflation maps `[1, n]` onto `[1, n * m]`. -/
theorem inflateSet_Icc (m : ℕ) : ∀ n : ℕ,
    inflateSet m (Finset.Icc (1 : ℤ) n) = Finset.Icc (1 : ℤ) ((n : ℤ) * (m : ℤ))
  | 0 => by
    ext u
    simp [inflateSet]
  | n + 1 => by
    have hsplit : Finset.Icc (1 : ℤ) ((n : ℤ) + 1) = Finset.Icc (1 : ℤ) n ∪ {(n : ℤ) + 1} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
      omega
    push_cast
    rw [hsplit, inflateSet_union, inflateSet_Icc m n]
    ext u
    simp only [Finset.mem_union, Finset.mem_Icc, inflateSet, Finset.singleton_biUnion,
      mem_inflateBlock_iff]
    constructor
    · rintro (⟨hu1, hu2⟩ | ⟨hu1, hu2⟩)
      · refine ⟨hu1, ?_⟩
        have hm : (0 : ℤ) ≤ (m : ℤ) := by positivity
        linarith
      · refine ⟨?_, by linarith⟩
        have hm : (0 : ℤ) ≤ (m : ℤ) := by positivity
        have hnm : (0 : ℤ) ≤ (n : ℤ) * (m : ℤ) := mul_nonneg (by positivity) hm
        linarith
    · rintro ⟨hu1, hu2⟩
      by_cases hle : u ≤ (n : ℤ) * (m : ℤ)
      · exact Or.inl ⟨hu1, hle⟩
      · exact Or.inr ⟨by linarith, by linarith⟩

/-- Every integer shift $d \in \mathbb{Z}$ decomposes as $d = q m + r$ with $q \in \mathbb{Z}$
and $0 \le r \le m$ whenever $m \ge 1$. -/
theorem exists_int_mul_add_nat_le {m : ℕ} (hm : 1 ≤ m) :
    ∀ d : ℤ, ∃ (q : ℤ) (r : ℕ), r ≤ m ∧ d = q * (m : ℤ) + (r : ℤ) := by
  have hnat : ∀ n : ℕ, ∃ (q : ℤ) (r : ℕ), r ≤ m ∧ (n : ℤ) = q * (m : ℤ) + (r : ℤ) := by
    intro n
    induction n with
    | zero => exact ⟨0, 0, by omega, by ring⟩
    | succ n ih =>
      rcases ih with ⟨q, r, hr, hn⟩
      by_cases hrm : r < m
      · refine ⟨q, r + 1, by omega, ?_⟩
        push_cast; linarith
      · have hreq : r = m := by omega
        refine ⟨q + 1, 1, hm, ?_⟩
        subst hreq; push_cast; linarith
  intro d
  rcases Int.eq_nat_or_neg d with ⟨n, rfl | rfl⟩
  · exact hnat n
  · rcases hnat n with ⟨q, r, hr, hn⟩
    by_cases hr0 : r = 0
    · refine ⟨-q, 0, by omega, ?_⟩
      subst hr0; push_cast at hn ⊢; linarith
    · refine ⟨-(q + 1), m - r, by omega, ?_⟩
      have hcast : ((m - r : ℕ) : ℤ) = (m : ℤ) - (r : ℤ) := Int.ofNat_sub hr
      rw [hcast]
      linarith

/-- Double indicator-sum representation of `Overlap A B k`. -/
theorem overlap_eq_sum_sum_ite (A B : Finset ℤ) (k : ℤ) :
    Overlap A B k = ∑ a ∈ A, ∑ b ∈ B, if a - b = k then 1 else 0 := by
  rw [Overlap, Finset.product_eq_sprod, Finset.card_filter, Finset.sum_product]

/-- Additivity of `Overlap` across pairwise disjoint block inflations `inflateSet m A` and `inflateSet m B`. -/
theorem overlap_inflateSet_eq_sum (m : ℕ) (A B : Finset ℤ) (d : ℤ) :
    Overlap (inflateSet m A) (inflateSet m B) d =
      ∑ a ∈ A, ∑ b ∈ B, Overlap (inflateBlock m a) (inflateBlock m b) d := by
  rw [overlap_eq_sum_sum_ite, inflateSet, inflateSet]
  rw [Finset.sum_biUnion (pairwiseDisjoint_inflateBlock m A)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_biUnion (pairwiseDisjoint_inflateBlock m B)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm, ← overlap_eq_sum_sum_ite]

/-- Self-overlap of the base block `[1, m]` at a nonnegative shift $0 \le r \le m$ equals $m - r$. -/
theorem overlap_Icc_self_of_nonneg (m : ℕ) {r : ℕ} (hr : r ≤ m) :
    Overlap (Finset.Icc (1 : ℤ) m) (Finset.Icc (1 : ℤ) m) (r : ℤ) = m - r := by
  unfold Overlap
  have hbij :
      (((Finset.Icc (1 : ℤ) m).product (Finset.Icc (1 : ℤ) m)).filter (fun p => p.1 - p.2 = (r : ℤ))).card =
        (Finset.Icc (1 : ℤ) ((m : ℤ) - (r : ℤ))).card := by
    refine Finset.card_bij
      (fun p _ => p.2)
      (fun ⟨u, v⟩ hp => ?_)
      (fun ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ h => ?_)
      (fun j hj => ?_)
    · simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.1.2.1, by omega⟩
    · simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
      exact Prod.ext (by omega) h
    · simp only [Finset.mem_Icc] at hj
      refine ⟨(j + (r : ℤ), j), ?_, rfl⟩
      simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨by omega, by omega⟩, ⟨hj.1, by omega⟩⟩, by omega⟩
  rw [hbij, Int.card_Icc]
  omega

/-- Self-overlap of the base block `[1, m]` at a negative shift $r - m$ ($0 \le r \le m$) equals $r$. -/
theorem overlap_Icc_self_of_neg (m : ℕ) {r : ℕ} (hr : r ≤ m) :
    Overlap (Finset.Icc (1 : ℤ) m) (Finset.Icc (1 : ℤ) m) ((r : ℤ) - (m : ℤ)) = r := by
  have hneg : (r : ℤ) - (m : ℤ) = -(((m - r : ℕ) : ℤ)) := by omega
  rw [hneg, overlap_neg]
  have hle : m - r ≤ m := Nat.sub_le m r
  rw [overlap_Icc_self_of_nonneg m hle]
  omega

/-- Self-overlap of `[1, m]` vanishes whenever $|s| \ge m$. -/
theorem overlap_Icc_self_eq_zero_of_le (m : ℕ) {s : ℤ} (hs : (m : ℤ) ≤ s ∨ s ≤ -(m : ℤ)) :
    Overlap (Finset.Icc (1 : ℤ) m) (Finset.Icc (1 : ℤ) m) s = 0 := by
  rw [Overlap, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨u, v⟩ hp hsub
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hu hv
  omega

/-- Translation reduction of the overlap between two inflated blocks `inflateBlock m a`
and `inflateBlock m b` to the self-overlap of `[1, m]`. -/
theorem overlap_inflateBlock_eq_overlap_Icc (m : ℕ) (a b d : ℤ) :
    Overlap (inflateBlock m a) (inflateBlock m b) d =
      Overlap (Finset.Icc (1 : ℤ) m) (Finset.Icc (1 : ℤ) m) (d - (a - b) * (m : ℤ)) := by
  unfold Overlap inflateBlock
  refine Finset.card_bij
    (fun p _ => (p.1 - (a - 1) * (m : ℤ), p.2 - (b - 1) * (m : ℤ)))
    (fun ⟨u, v⟩ hp => ?_)
    (fun ⟨u₁, v₁⟩ _ ⟨u₂, v₂⟩ _ h => ?_)
    (fun ⟨i, j⟩ hq => ?_)
  · simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, by linarith⟩
  · simp only [Prod.mk.injEq] at h
    exact Prod.ext (by linarith) (by linarith)
  · simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
    refine ⟨(i + (a - 1) * (m : ℤ), j + (b - 1) * (m : ℤ)), ?_, ?_⟩
    · simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, by linarith⟩
    · exact Prod.ext (by ring) (by ring)

/-- Exact pairwise block-overlap formula at shift $q m + r$ ($0 \le r \le m$). -/
theorem overlap_inflateBlock_eq_ite {m r : ℕ} (hr : r ≤ m) (a b q : ℤ) :
    Overlap (inflateBlock m a) (inflateBlock m b) (q * (m : ℤ) + (r : ℤ)) =
      (if a - b = q then m - r else 0) + (if a - b = q + 1 then r else 0) := by
  rw [overlap_inflateBlock_eq_overlap_Icc]
  split_ifs with h1 h2 h2
  · omega
  · have hshift : q * (m : ℤ) + (r : ℤ) - (a - b) * (m : ℤ) = (r : ℤ) := by
      rw [h1]; ring
    rw [hshift, overlap_Icc_self_of_nonneg m hr, add_zero]
  · have hshift : q * (m : ℤ) + (r : ℤ) - (a - b) * (m : ℤ) = (r : ℤ) - (m : ℤ) := by
      rw [h2]; ring
    rw [zero_add, hshift, overlap_Icc_self_of_neg m hr]
  · rw [zero_add]
    apply overlap_Icc_self_eq_zero_of_le m
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · left
      have hle : (1 : ℤ) ≤ q - (a - b) := by omega
      have hm : (0 : ℤ) ≤ (m : ℤ) := by positivity
      have hmul : (1 : ℤ) * (m : ℤ) ≤ (q - (a - b)) * (m : ℤ) :=
        mul_le_mul_of_nonneg_right hle hm
      linarith
    · right
      have hle : (2 : ℤ) ≤ (a - b) - q := by omega
      have hm : (0 : ℤ) ≤ (m : ℤ) := by positivity
      have hmul : (2 : ℤ) * (m : ℤ) ≤ ((a - b) - q) * (m : ℤ) :=
        mul_le_mul_of_nonneg_right hle hm
      have hrm : (r : ℤ) ≤ (m : ℤ) := by exact_mod_cast hr
      linarith

/-- **General Block-Inflation Identity**: for any finite sets $A, B \subseteq \mathbb{Z}$,
scale $m \in \mathbb{N}$, shift quotient $q \in \mathbb{Z}$, and remainder $0 \le r \le m$,
`Overlap (inflateSet m A) (inflateSet m B) (q * m + r) = (m - r) * Overlap A B q + r * Overlap A B (q + 1)`. -/
theorem overlap_inflateSet_linear_interp {m r : ℕ} (hr : r ≤ m) (A B : Finset ℤ) (q : ℤ) :
    Overlap (inflateSet m A) (inflateSet m B) (q * (m : ℤ) + (r : ℤ)) =
      (m - r) * Overlap A B q + r * Overlap A B (q + 1) := by
  rw [overlap_inflateSet_eq_sum]
  simp_rw [overlap_inflateBlock_eq_ite hr, Finset.sum_add_distrib]
  congr 1
  · rw [overlap_eq_sum_sum_ite, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  · rw [overlap_eq_sum_sum_ite, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring

/-- At aligned block shifts $d = q m$, block inflation scales overlap by $m$:
`Overlap (inflateSet m A) (inflateSet m B) (q * m) = m * Overlap A B q`. -/
theorem overlap_inflateSet_mul_eq (m : ℕ) (A B : Finset ℤ) (q : ℤ) :
    Overlap (inflateSet m A) (inflateSet m B) (q * (m : ℤ)) = m * Overlap A B q := by
  have h := overlap_inflateSet_linear_interp (Nat.zero_le m) A B q
  simpa using h

/-- For every shift $d \in \mathbb{Z}$, `Overlap (inflateSet m A) (inflateSet m B) d ≤ m * MaxOverlap A B`. -/
theorem overlap_inflateSet_le_mul_maxOverlap (m : ℕ) (A B : Finset ℤ) (d : ℤ) :
    Overlap (inflateSet m A) (inflateSet m B) d ≤ m * MaxOverlap A B := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hemp : inflateSet 0 A = ∅ := by
      ext u; simp [inflateSet, mem_inflateBlock_iff]; omega
    rw [hemp, zero_mul]
    exact (overlap_le_card_left ∅ _ d).trans (by simp)
  · rcases exists_int_mul_add_nat_le hmpos d with ⟨q, r, hr, rfl⟩
    rw [overlap_inflateSet_linear_interp hr A B q]
    have hq1 : Overlap A B q ≤ MaxOverlap A B := overlap_le_maxOverlap A B q
    have hq2 : Overlap A B (q + 1) ≤ MaxOverlap A B := overlap_le_maxOverlap A B (q + 1)
    have h1 : (m - r) * Overlap A B q ≤ (m - r) * MaxOverlap A B := Nat.mul_le_mul_left (m - r) hq1
    have h2 : r * Overlap A B (q + 1) ≤ r * MaxOverlap A B := Nat.mul_le_mul_left r hq2
    calc
      (m - r) * Overlap A B q + r * Overlap A B (q + 1)
        ≤ (m - r) * MaxOverlap A B + r * MaxOverlap A B := add_le_add h1 h2
      _ = (m - r + r) * MaxOverlap A B := by ring
      _ = m * MaxOverlap A B := by rw [Nat.sub_add_cancel hr]

/-- **Exact Homogeneity of `MaxOverlap` under Block Inflation**:
`MaxOverlap (inflateSet m A) (inflateSet m B) = m * MaxOverlap A B`. -/
theorem maxOverlap_inflateSet_eq_mul (m : ℕ) (A B : Finset ℤ) :
    MaxOverlap (inflateSet m A) (inflateSet m B) = m * MaxOverlap A B := by
  apply le_antisymm
  · exact ciSup_le fun d => overlap_inflateSet_le_mul_maxOverlap m A B d
  · rw [maxOverlap_eq_sup A B]
    rcases ((A ×ˢ B).image fun p => p.1 - p.2).eq_empty_or_nonempty with hemp | hne
    · rw [hemp, Finset.sup_empty, Nat.bot_eq_zero, mul_zero]
      exact Nat.zero_le _
    · obtain ⟨q, _, hsup⟩ :=
        Finset.exists_mem_eq_sup (s := (A ×ˢ B).image fun p => p.1 - p.2) hne (Overlap A B)
      rw [hsup, ← overlap_inflateSet_mul_eq m A B q]
      exact overlap_le_maxOverlap (inflateSet m A) (inflateSet m B) (q * (m : ℤ))

/-- **Universal Submultiplicativity of $M$**: `M (k * m) ≤ m * M k` for all $k, m \in \mathbb{N}$. -/
theorem M_mul_le_mul_M (k m : ℕ) : M (k * m) ≤ m * M k := by
  have hmin := M_eq_min_parts k
  set S := (parts k).image (fun X => maxOverlapC X (Finset.Icc (1 : ℤ) (2 * k) \ X))
  obtain ⟨y, hy, hy_eq⟩ : ∃ y ∈ parts k, maxOverlapC y (Finset.Icc (1 : ℤ) (2 * k) \ y) = M k := by
    have hmem : S.min' ((parts_nonempty k).image _) ∈ S := Finset.min'_mem S _
    rw [← hmin] at hmem
    simpa [S] using hmem
  obtain ⟨hy_sub, hy_card⟩ := mem_parts.mp hy
  set B := Finset.Icc (1 : ℤ) (2 * k) \ y
  have hdisj : Disjoint y B := Finset.disjoint_sdiff
  have hunion : y ∪ B = Finset.Icc (1 : ℤ) (2 * k) := Finset.union_sdiff_of_subset hy_sub
  have hBcard : B.card = k := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hy_sub, Int.card_Icc, hy_card]
    omega
  have hdisj_inf : Disjoint (inflateSet m y) (inflateSet m B) := disjoint_inflateSet m hdisj
  have hunion_inf : inflateSet m y ∪ inflateSet m B = Finset.Icc (1 : ℤ) (2 * (k * m : ℕ)) := by
    rw [← inflateSet_union, hunion]
    have h2 : (2 : ℤ) * (k : ℤ) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
    rw [h2, inflateSet_Icc m (2 * k)]
    push_cast; ring_nf
  have hcard_inf : (inflateSet m y).card = (inflateSet m B).card := by
    rw [card_inflateSet, card_inflateSet, hy_card, hBcard]
  have hle : M (k * m) ≤ MaxOverlap (inflateSet m y) (inflateSet m B) :=
    Nat.sInf_le ⟨inflateSet m y, inflateSet m B, hdisj_inf, hunion_inf, hcard_inf, rfl⟩
  rw [maxOverlap_inflateSet_eq_mul, maxOverlap_eq_maxOverlapC, hy_eq] at hle
  exact hle

/-- **Euclidean Division-Remainder Upper Bound**: for all $N, k \in \mathbb{N}$,
`M N ≤ (N / k) * M k + N % k`. -/
theorem M_div_mul_add_mod_le (N k : ℕ) :
    M N ≤ (N / k) * M k + N % k := by
  have hdiv : k * (N / k) + N % k = N := Nat.div_add_mod N k
  calc
    M N = M (k * (N / k) + N % k) := by rw [hdiv]
    _ ≤ M (k * (N / k)) + N % k := M_add_le (k * (N / k)) (N % k)
    _ ≤ (N / k) * M k + N % k := Nat.add_le_add_right (M_mul_le_mul_M k (N / k)) (N % k)

/-- Pointwise rational upper bound on `MinOverlapQuotient N` in terms of any anchor $k \ge 1$:
`MinOverlapQuotient N ≤ (M k : ℝ) / k + k / N`. -/
theorem minOverlapQuotient_le_div_add_div {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    MinOverlapQuotient N ≤ (M k : ℝ) / (k : ℝ) + (k : ℝ) / (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hM : (M N : ℝ) ≤ ((N / k : ℕ) : ℝ) * (M k : ℝ) + ((N % k : ℕ) : ℝ) := by
    exact_mod_cast M_div_mul_add_mod_le N k
  have hq : ((N / k : ℕ) : ℝ) * (k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N k
  have hr : ((N % k : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast le_of_lt (Nat.mod_lt N hk)
  have hqk : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / (k : ℝ) :=
    (le_div_iff₀ hk0).mpr hq
  have hmul : ((N / k : ℕ) : ℝ) * (M k : ℝ) ≤ ((N : ℝ) / (k : ℝ)) * (M k : ℝ) :=
    mul_le_mul_of_nonneg_right hqk (by positivity)
  unfold MinOverlapQuotient
  rw [div_le_iff₀ hN0]
  have hcalc : ((M k : ℝ) / (k : ℝ) + (k : ℝ) / (N : ℝ)) * (N : ℝ) =
      ((N : ℝ) / (k : ℝ)) * (M k : ℝ) + (k : ℝ) := by
    field_simp [ne_of_gt hN0, ne_of_gt hk0]
  linarith

/-- **Fekete Asymptotic Submultiplicativity Bound**: for every $k \ge 1$,
`atTop.limsup MinOverlapQuotient ≤ (M k : ℝ) / k`. -/
theorem fekete_limsup_minOverlapQuotient_le_div {k : ℕ} (hk : 1 ≤ k) :
    atTop.limsup MinOverlapQuotient ≤ (M k : ℝ) / (k : ℝ) := by
  have hnn : ∀ n, 0 ≤ MinOverlapQuotient n := fun n => by
    unfold MinOverlapQuotient; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  apply Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop hnn)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((k : ℝ) / ε)
  filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hstep := minOverlapQuotient_le_div_add_div hN1 hk
  have hNgt : (k : ℝ) / ε < (N : ℝ) := by
    have hle : (N₀ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hkN : (k : ℝ) / (N : ℝ) ≤ ε := by
    rw [div_le_iff₀ hNpos]
    rw [div_lt_iff₀ hε] at hNgt
    linarith
  linarith

/-- Universal finite-to-asymptotic upper-bound transfer: any upper bound `M k ≤ b` ($k \ge 1$)
implies `atTop.limsup MinOverlapQuotient ≤ b / k`. -/
theorem limsup_minOverlapQuotient_le_of_M_le {k b : ℕ} (hk : 1 ≤ k) (hM : M k ≤ b) :
    atTop.limsup MinOverlapQuotient ≤ (b : ℝ) / (k : ℝ) := by
  refine (fekete_limsup_minOverlapQuotient_le_div hk).trans ?_
  gcongr

/-- Explicit 30-block balanced binary witness $A_{15} \subseteq \{1, \dots, 30\}$ achieving
maximum overlap $6$ ($6/15 = 2/5$). -/
def mrsBinaryWitnessA : Finset ℤ :=
  {1, 2, 3, 4, 6, 7, 10, 17, 19, 24, 25, 27, 28, 29, 30}

/-- Complement $B_{15} = \{1, \dots, 30\} \setminus A_{15}$. -/
def mrsBinaryWitnessB : Finset ℤ :=
  {5, 8, 9, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23, 26}
set_option maxRecDepth 16000 in

/-- Multi-scale overlap bound for the 30-block witness $(A_{15}, B_{15})$:
`M (15 * m) ≤ 6 * m` for all $m \in \mathbb{N}$. -/
theorem M_fifteen_mul_le (m : ℕ) : M (15 * m) ≤ 6 * m := by
  have hmax : MaxOverlap mrsBinaryWitnessA mrsBinaryWitnessB = 6 := by
    rw [maxOverlap_eq_maxOverlapC]
    decide
  have hM15 : M 15 ≤ 6 := by
    have hle : M 15 ≤ MaxOverlap mrsBinaryWitnessA mrsBinaryWitnessB :=
      Nat.sInf_le ⟨mrsBinaryWitnessA, mrsBinaryWitnessB, by decide, by decide, by decide, rfl⟩
    rwa [hmax] at hle
  calc
    M (15 * m) ≤ m * M 15 := M_mul_le_mul_M 15 m
    _ ≤ m * 6 := Nat.mul_le_mul_left m hM15
    _ = 6 * m := by ring

/-- **Motzkin–Ralston–Selfridge (1956) Asymptotic Upper Bound**:
`atTop.limsup MinOverlapQuotient ≤ c` for every $c \ge 2/5$ (in particular $c = 2/5$,
strictly improving $5/12$, $3/7$, and Erdős's $1/2$). -/
theorem mrs_two_fifths_limsup_bound {c : ℝ} (hc : (2 : ℝ) / 5 ≤ c) :
    atTop.limsup MinOverlapQuotient ≤ c := by
  have hM15 : M 15 ≤ 6 := by
    simpa using M_fifteen_mul_le 1
  have h := limsup_minOverlapQuotient_le_of_M_le (by omega : 1 ≤ 15) hM15
  norm_num at h
  linarith
/-- Closed-form sum of integers on `Icc 1 N`: `2 * ∑ x ∈ Icc 1 N, x = N * (N + 1)`. -/
theorem two_mul_sum_Icc_int_eq : ∀ N : ℕ,
    2 * (∑ x ∈ Finset.Icc (1 : ℤ) N, (x : ℝ)) = (N : ℝ) * ((N : ℝ) + 1)
  | 0 => by simp
  | N + 1 => by
    have hsplit : Finset.Icc (1 : ℤ) ((N + 1 : ℕ) : ℤ) =
        insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (1 : ℤ) N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hmem : (((N + 1 : ℕ) : ℤ)) ∉ Finset.Icc (1 : ℤ) N := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hmem, mul_add, two_mul_sum_Icc_int_eq N]
    push_cast; ring

/-- Closed-form sum of squares on `Icc 1 N`: `6 * ∑ x ∈ Icc 1 N, x^2 = N * (N + 1) * (2N + 1)`. -/
theorem six_mul_sum_Icc_int_sq_eq : ∀ N : ℕ,
    6 * (∑ x ∈ Finset.Icc (1 : ℤ) N, (x : ℝ) ^ 2) =
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1)
  | 0 => by simp
  | N + 1 => by
    have hsplit : Finset.Icc (1 : ℤ) ((N + 1 : ℕ) : ℤ) =
        insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (1 : ℤ) N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hmem : (((N + 1 : ℕ) : ℤ)) ∉ Finset.Icc (1 : ℤ) N := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hmem, mul_add, six_mul_sum_Icc_int_sq_eq N]
    push_cast; ring

/-- Closed-form sum of squares on the symmetric interval `Icc (-R) R`:
`6 * ∑ k ∈ Icc (-R) R, k^2 = 2 * R * (R + 1) * (2R + 1)`. -/
theorem six_mul_sum_Icc_symm_int_sq_eq : ∀ R : ℕ,
    6 * (∑ k ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (k : ℝ) ^ 2) =
      2 * (R : ℝ) * ((R : ℝ) + 1) * (2 * (R : ℝ) + 1)
  | 0 => by simp
  | R + 1 => by
    have hsplit : Finset.Icc (-(((R + 1 : ℕ) : ℤ))) ((R + 1 : ℕ) : ℤ) =
        insert (((R + 1 : ℕ) : ℤ))
          (insert (-(((R + 1 : ℕ) : ℤ))) (Finset.Icc (-(R : ℤ)) (R : ℤ))) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hm1 : (((R + 1 : ℕ) : ℤ)) ∉
        insert (-(((R + 1 : ℕ) : ℤ))) (Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hm2 : (-(((R + 1 : ℕ) : ℤ))) ∉ Finset.Icc (-(R : ℤ)) (R : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have ih := six_mul_sum_Icc_symm_int_sq_eq R
    rw [hsplit, Finset.sum_insert hm1, Finset.sum_insert hm2]
    push_cast
    linarith

/-- **Moser's (1959) Complete Second-Moment Variance Identity**: for any balanced partition
$(A, B)$ of `[1, 2n]`,
`6 * ∑ k ∈ Icc (-(2n-1)) (2n-1), k^2 * Overlap A B k = n^2 * (4 * n^2 - 1) + 3 * (∑ a ∈ A, a - ∑ b ∈ B, b)^2`. -/
theorem moser_second_moment_variance_identity {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (hA : A.card = n) (hB : B.card = n) :
    6 * (∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1),
      (k : ℝ) ^ 2 * (Overlap A B k : ℝ)) =
      (n : ℝ) ^ 2 * (4 * (n : ℝ) ^ 2 - 1) +
        3 * (∑ a ∈ A, (a : ℝ) - ∑ b ∈ B, (b : ℝ)) ^ 2 := by
  have hA_sub : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
  have hB_sub : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
  rw [sum_Icc_second_moment_overlap hA_sub hB_sub, hA, hB]
  have hsum1 : ∑ a ∈ A, (a : ℝ) + ∑ b ∈ B, (b : ℝ) =
      ∑ x ∈ Finset.Icc (1 : ℤ) (2 * n), (x : ℝ) := by
    rw [← hunion, Finset.sum_union hdisj]
  have hsum2 : ∑ a ∈ A, (a : ℝ) ^ 2 + ∑ b ∈ B, (b : ℝ) ^ 2 =
      ∑ x ∈ Finset.Icc (1 : ℤ) (2 * n), (x : ℝ) ^ 2 := by
    rw [← hunion, Finset.sum_union hdisj]
  have hI1 := two_mul_sum_Icc_int_eq (2 * n)
  have hI2 := six_mul_sum_Icc_int_sq_eq (2 * n)
  have hcast : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  rw [hcast] at hI1 hI2
  push_cast at hI1 hI2
  have hI1_eq : ∑ x ∈ Finset.Icc (1 : ℤ) (2 * (n : ℤ)), (x : ℝ) =
      (n : ℝ) * (2 * (n : ℝ) + 1) := by linarith
  have halg : 6 * ((n : ℝ) * ∑ a ∈ A, (a : ℝ) ^ 2 + (n : ℝ) * ∑ b ∈ B, (b : ℝ) ^ 2 -
        2 * (∑ a ∈ A, (a : ℝ)) * ∑ b ∈ B, (b : ℝ)) =
      (n : ℝ) * (6 * (∑ a ∈ A, (a : ℝ) ^ 2 + ∑ b ∈ B, (b : ℝ) ^ 2)) -
        3 * (∑ a ∈ A, (a : ℝ) + ∑ b ∈ B, (b : ℝ)) ^ 2 +
        3 * (∑ a ∈ A, (a : ℝ) - ∑ b ∈ B, (b : ℝ)) ^ 2 := by ring
  rw [halg, hsum1, hsum2, hI2, hI1_eq]
  ring

/-- **Moser's Shifted / Central Second-Moment Identity**: for any shift $q_0 \in \mathbb{R}$,
`6 * ∑ k ∈ Icc (-(2n-1)) (2n-1), (k - q₀)^2 * Overlap A B k = n^2 * (4 * n^2 - 1) - 3 * Δ^2 + 6 * (n * q₀ - Δ)^2`
where $\Delta = \sum_{a \in A} a - \sum_{b \in B} b$. -/
theorem moser_shifted_second_moment_identity {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (hA : A.card = n) (hB : B.card = n) (q₀ : ℝ) :
    6 * (∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1),
      ((k : ℝ) - q₀) ^ 2 * (Overlap A B k : ℝ)) =
      (n : ℝ) ^ 2 * (4 * (n : ℝ) ^ 2 - 1) -
        3 * (∑ a ∈ A, (a : ℝ) - ∑ b ∈ B, (b : ℝ)) ^ 2 +
        6 * ((n : ℝ) * q₀ - (∑ a ∈ A, (a : ℝ) - ∑ b ∈ B, (b : ℝ))) ^ 2 := by
  have hA_sub : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
  have hB_sub : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
  set J := Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1)
  have hexp : ∀ k : ℤ, ((k : ℝ) - q₀) ^ 2 * (Overlap A B k : ℝ) =
      (k : ℝ) ^ 2 * (Overlap A B k : ℝ) -
        2 * q₀ * ((k : ℝ) * (Overlap A B k : ℝ)) +
        q₀ ^ 2 * (Overlap A B k : ℝ) := by
    intro k; ring
  simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hm0 : ∑ k ∈ J, (Overlap A B k : ℝ) = (n : ℝ) ^ 2 := by
    have h0 := sum_overlap_Icc_eq_card_mul hA_sub hB_sub
    rw [hA, hB] at h0
    have hcast : (∑ k ∈ J, Overlap A B k : ℝ) = ((n * n : ℕ) : ℝ) := by exact_mod_cast h0
    simpa [J, sq] using hcast
  have hm1 := sum_Icc_first_moment_overlap hA_sub hB_sub
  rw [hA, hB] at hm1
  have hm2 := moser_second_moment_variance_identity hdisj hunion hA hB
  dsimp [J] at hm0 ⊢
  rw [hm0, hm1]
  linarith

/-- **Exact Closed-Form Parabolic Kernel Sum**: for any integer center $q_0 \in \mathbb{Z}$
and radius $R \in \mathbb{N}$,
`3 * ∑ k ∈ Icc (q₀ - R) (q₀ + R), (R^2 - (k - q₀)^2) = R * (4 * R^2 - 1)`. -/
theorem three_mul_sum_Icc_parabolic_kernel_eq (q₀ : ℤ) (R : ℕ) :
    3 * (∑ k ∈ Finset.Icc (q₀ - (R : ℤ)) (q₀ + (R : ℤ)),
      ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2)) =
      (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) := by
  have hbij : ∑ k ∈ Finset.Icc (q₀ - (R : ℤ)) (q₀ + (R : ℤ)),
      ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) =
      ∑ j ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ((R : ℝ) ^ 2 - (j : ℝ) ^ 2) := by
    refine Finset.sum_bij (fun k _ => k - q₀)
      (fun k hk => ?_) (fun k₁ _ k₂ _ h => by linarith) (fun j hj => ?_) (fun k _ => ?_)
    · rw [Finset.mem_Icc] at hk ⊢; omega
    · rw [Finset.mem_Icc] at hj
      refine ⟨j + q₀, ?_, by ring⟩
      rw [Finset.mem_Icc]; omega
    · push_cast; ring
  rw [hbij, Finset.sum_sub_distrib, Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
  have hcard : (((R : ℤ) + 1 - -(R : ℤ)).toNat : ℝ) = 2 * (R : ℝ) + 1 := by
    have h1 : (R : ℤ) + 1 - -(R : ℤ) = ((2 * R + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.toNat_natCast]
    push_cast; ring
  have hsq := six_mul_sum_Icc_symm_int_sq_eq R
  rw [hcard]
  linarith

/-- **Discrete Downward-Parabolic Bathtub Inequality**: for any $A, B \subseteq [1, 2n]$
with $|A| = |B| = n$, any integer center $q_0 \in \mathbb{Z}$, and any radius $R \in \mathbb{N}$,
`3 * R^2 * n^2 - 3 * ∑ k ∈ Icc (-(2n-1)) (2n-1), (k - q₀)^2 * Overlap A B k ≤ R * (4 * R^2 - 1) * MaxOverlap A B`. -/
theorem parabolic_bathtub_overlap_inequality {n : ℕ} {A B : Finset ℤ}
    (hA_sub : A ⊆ Finset.Icc (1 : ℤ) (2 * n))
    (hB_sub : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    (hA : A.card = n) (hB : B.card = n) (q₀ : ℤ) (R : ℕ) :
    3 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 -
      3 * (∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1),
        ((k : ℝ) - (q₀ : ℝ)) ^ 2 * (Overlap A B k : ℝ)) ≤
      (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (MaxOverlap A B : ℝ) := by
  set J := Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1)
  set IR := Finset.Icc (q₀ - (R : ℤ)) (q₀ + (R : ℤ))
  have hm0 : ∑ k ∈ J, (Overlap A B k : ℝ) = (n : ℝ) ^ 2 := by
    have h0 := sum_overlap_Icc_eq_card_mul hA_sub hB_sub
    rw [hA, hB] at h0
    have hcast : (∑ k ∈ J, Overlap A B k : ℝ) = ((n * n : ℕ) : ℝ) := by exact_mod_cast h0
    simpa [J, sq] using hcast
  have hdiff : (R : ℝ) ^ 2 * (n : ℝ) ^ 2 -
      ∑ k ∈ J, ((k : ℝ) - (q₀ : ℝ)) ^ 2 * (Overlap A B k : ℝ) =
      ∑ k ∈ J, ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (Overlap A B k : ℝ) := by
    rw [← hm0, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hstep1 : ∑ k ∈ J, ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (Overlap A B k : ℝ) ≤
      ∑ k ∈ J, if k ∈ IR then ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (MaxOverlap A B : ℝ) else 0 := by
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with hk
    · have hkI := Finset.mem_Icc.mp hk
      have hsq_le : (k - q₀) ^ 2 ≤ (R : ℤ) ^ 2 := by nlinarith
      have hsq_real : ((k : ℝ) - (q₀ : ℝ)) ^ 2 ≤ (R : ℝ) ^ 2 := by exact_mod_cast hsq_le
      have hnonneg : 0 ≤ (R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2 := by linarith
      have hov : (Overlap A B k : ℝ) ≤ (MaxOverlap A B : ℝ) := by
        exact_mod_cast overlap_le_maxOverlap A B k
      exact mul_le_mul_of_nonneg_left hov hnonneg
    · have hkI : k < q₀ - (R : ℤ) ∨ q₀ + (R : ℤ) < k := by
        rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
        exact hk
      have hsq_ge : (R : ℤ) ^ 2 ≤ (k - q₀) ^ 2 := by
        rcases hkI with hlt | hgt <;> nlinarith
      have hsq_real : (R : ℝ) ^ 2 ≤ ((k : ℝ) - (q₀ : ℝ)) ^ 2 := by exact_mod_cast hsq_ge
      have hnonpos : (R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2 ≤ 0 := by linarith
      have hov : (0 : ℝ) ≤ (Overlap A B k : ℝ) := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg hnonpos hov
  have hstep2 : (∑ k ∈ J, if k ∈ IR then ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (MaxOverlap A B : ℝ) else 0) ≤
      ∑ k ∈ IR, ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (MaxOverlap A B : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.mp hk).2) (fun k hk _ => ?_)
    have hkI := Finset.mem_Icc.mp hk
    have hsq_le : (k - q₀) ^ 2 ≤ (R : ℤ) ^ 2 := by nlinarith
    have hsq_real : ((k : ℝ) - (q₀ : ℝ)) ^ 2 ≤ (R : ℝ) ^ 2 := by exact_mod_cast hsq_le
    have hnonneg : 0 ≤ (R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2 := by linarith
    exact mul_nonneg hnonneg (by positivity)
  rw [← Finset.sum_mul] at hstep2
  have hpar := three_mul_sum_Icc_parabolic_kernel_eq q₀ R
  dsimp [J, IR] at hdiff hstep1 hstep2 ⊢
  nlinarith

/-- Nearest-integer rounding lemma: for every $n \ge 1$ and $\Delta \in \mathbb{Z}$, there exists
$q_0 \in \mathbb{Z}$ such that $4 (n q_0 - \Delta)^2 \le n^2$. -/
theorem exists_int_nearest_mul_le {n : ℕ} (hn : 1 ≤ n) (Δ : ℤ) :
    ∃ q₀ : ℤ, 4 * ((n : ℤ) * q₀ - Δ) ^ 2 ≤ (n : ℤ) ^ 2 := by
  obtain ⟨q, r, hr, hΔ⟩ := exists_int_mul_add_nat_le hn Δ
  by_cases h2r : 2 * r ≤ n
  · refine ⟨q, ?_⟩
    have hdiff : (n : ℤ) * q - Δ = -(r : ℤ) := by linarith
    have h2r_int : 2 * (r : ℤ) ≤ (n : ℤ) := by exact_mod_cast h2r
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
    rw [hdiff]
    nlinarith
  · refine ⟨q + 1, ?_⟩
    have hdiff : (n : ℤ) * (q + 1) - Δ = (n : ℤ) - (r : ℤ) := by linarith
    have h1 : (n : ℤ) < 2 * (r : ℤ) := by
      have : n < 2 * r := by omega
      exact_mod_cast this
    have h2 : (r : ℤ) ≤ (n : ℤ) := by exact_mod_cast hr
    rw [hdiff]
    nlinarith

/-- **Universal Moser Parametric Quadratic Bound on `MaxOverlap`**: for any balanced partition
$(A, B)$ of `[1, 2n]` and any radius $R \in \mathbb{N}$,
`12 * R^2 * n^2 ≤ 8 * n^4 + n^2 + 4 * R * (4 * R^2 - 1) * MaxOverlap A B`. -/
theorem moser_parametric_quadratic_le_maxOverlap {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (hA : A.card = n) (hB : B.card = n) (R : ℕ) :
    12 * R ^ 2 * n ^ 2 ≤ 8 * n ^ 4 + n ^ 2 + 4 * R * (4 * R ^ 2 - 1) * MaxOverlap A B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · have hA_sub : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
      have hB_sub : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
      set Δℤ : ℤ := (∑ a ∈ A, a) - (∑ b ∈ B, b)
      obtain ⟨q₀, hq₀⟩ := exists_int_nearest_mul_le hn Δℤ
      have hq₀_real : 4 * ((n : ℝ) * (q₀ : ℝ) - ((∑ a ∈ A, (a : ℝ)) - (∑ b ∈ B, (b : ℝ)))) ^ 2 ≤
          (n : ℝ) ^ 2 := by
        have hcast : ((n : ℤ) * q₀ - Δℤ : ℝ) =
            (n : ℝ) * (q₀ : ℝ) - ((∑ a ∈ A, (a : ℝ)) - (∑ b ∈ B, (b : ℝ))) := by
          dsimp [Δℤ]; push_cast; ring
        have hq_cast : (4 * ((n : ℤ) * q₀ - Δℤ) ^ 2 : ℝ) ≤ ((n : ℤ) ^ 2 : ℝ) := by
          exact_mod_cast hq₀
        push_cast at hq_cast
        rw [← hcast]
        exact hq_cast
      have hshift := moser_shifted_second_moment_identity hdisj hunion hA hB (q₀ : ℝ)
      have hbat := parabolic_bathtub_overlap_inequality hA_sub hB_sub hA hB q₀ R
      have hΔ_sq : 0 ≤ ((∑ a ∈ A, (a : ℝ)) - (∑ b ∈ B, (b : ℝ))) ^ 2 := sq_nonneg _
      have hreal : 12 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤
          8 * (n : ℝ) ^ 4 + (n : ℝ) ^ 2 +
            4 * (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (MaxOverlap A B : ℝ) := by
        linarith
      have h4R2 : 1 ≤ 4 * R ^ 2 := by nlinarith
      have hcast_rhs : ((8 * n ^ 4 + n ^ 2 + 4 * R * (4 * R ^ 2 - 1) * MaxOverlap A B : ℕ) : ℝ) =
          8 * (n : ℝ) ^ 4 + (n : ℝ) ^ 2 +
            4 * (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (MaxOverlap A B : ℝ) := by
        push_cast [Nat.cast_sub h4R2]; ring
      have hcast_lhs : ((12 * R ^ 2 * n ^ 2 : ℕ) : ℝ) = 12 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
        push_cast; ring
      rw [← hcast_lhs, ← hcast_rhs] at hreal
      exact_mod_cast hreal

/-- **Universal Moser Parametric Quadratic Bound on $M(n)$**: for all $n, R \in \mathbb{N}$,
`12 * R^2 * n^2 ≤ 8 * n^4 + n^2 + 4 * R * (4 * R^2 - 1) * M n`. -/
theorem moser_parametric_quadratic_le_M (n R : ℕ) :
    12 * R ^ 2 * n ^ 2 ≤ 8 * n ^ 4 + n ^ 2 + 4 * R * (4 * R ^ 2 - 1) * M n := by
  have hne : ({MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
      (_disjoint : Disjoint A B)
      (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
      (_same_card : A.card = B.card)}).Nonempty := by
    refine ⟨_, Finset.Icc (1 : ℤ) n, Finset.Icc (1 : ℤ) (2 * n) \ Finset.Icc (1 : ℤ) n,
      Finset.disjoint_sdiff, ?_, ?_, rfl⟩
    · exact Finset.union_sdiff_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.Icc_subset_Icc le_rfl (by omega)),
        Int.card_Icc, Int.card_Icc]
      omega
  obtain ⟨A, B, hdisj, hunion, hsame, hM⟩ := Nat.sInf_mem hne
  have hcard_sum : A.card + B.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
    omega
  have hA : A.card = n := by omega
  have hB : B.card = n := by omega
  unfold M
  rw [← hM]
  exact moser_parametric_quadratic_le_maxOverlap hdisj hunion hA hB R

/-- Positive control 1: Exact value `M 6 = 3`, proved algebraically from `moser_parametric_quadratic_le_M 6 8`
and `M_le_add_one_div_two 6` (where both pigeonhole and Scherk only give `M 6 ≥ 2`). -/
theorem M_six_eq_three : M 6 = 3 := by
  have hlb := moser_parametric_quadratic_le_M 6 8
  have hub := M_le_add_one_div_two 6
  omega

/-- Positive control 2: Exact value `M 9 = 4`, proved algebraically from `moser_parametric_quadratic_le_M 9 11`
and the 18-block step-template upper bound `M_nine_le_four` (where both pigeonhole and Scherk only give `M 9 ≥ 3`). -/
theorem M_nine_eq_four : M 9 = 4 := by
  have hlb := moser_parametric_quadratic_le_M 9 11
  have hub := M_nine_le_four
  omega

/-- Positive control 3: Exact value `M 12 = 5`, proved algebraically from `moser_parametric_quadratic_le_M 12 15`
and the 24-block step-template upper bound `M_twelve_le_five` (where both pigeonhole and Scherk only give `M 12 ≥ 4`). -/
theorem M_twelve_eq_five : M 12 = 5 := by
  have hlb := moser_parametric_quadratic_le_M 12 15
  have hub := M_twelve_le_five
  omega

/-- Positive control 4: Exact value `M 15 = 6`, proved algebraically from `moser_parametric_quadratic_le_M 15 21`
(`1190700 ≤ 405225 + 148092 * M 15`, forcing `6 ≤ M 15`) and the Motzkin–Ralston–Selfridge
30-block witness bound `M_fifteen_mul_le 1` (`M 15 ≤ 6`). -/
theorem M_fifteen_eq_six : M 15 = 6 := by
  have hlb := moser_parametric_quadratic_le_M 15 21
  have hub : M 15 ≤ 6 := by simpa using M_fifteen_mul_le 1
  omega

/-- Double-root polynomial factorization at the optimal Moser aspect ratio $R / n = \sqrt{2}$:
`4 * n * (√2 * R^3 - 3 * R^2 * n + 2 * n^3) = 4 * n * (R - √2 * n)^2 * (√2 * R + n)`. -/
theorem moser_double_root_identity (R n : ℝ) :
    4 * n * (Real.sqrt 2 * R ^ 3 - 3 * R ^ 2 * n + 2 * n ^ 3) =
      4 * n * (R - Real.sqrt 2 * n) ^ 2 * (Real.sqrt 2 * R + n) := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hexp1 : (R - Real.sqrt 2 * n) ^ 2 =
      R ^ 2 - 2 * Real.sqrt 2 * R * n + (Real.sqrt 2) ^ 2 * n ^ 2 := by ring
  rw [hexp1, hsq]
  have hexp2 : 4 * n * (R ^ 2 - 2 * Real.sqrt 2 * R * n + 2 * n ^ 2) * (Real.sqrt 2 * R + n) =
      4 * n * (Real.sqrt 2 * R ^ 3 + R ^ 2 * n - 2 * (Real.sqrt 2) ^ 2 * R ^ 2 * n -
        2 * Real.sqrt 2 * R * n ^ 2 + 2 * Real.sqrt 2 * R * n ^ 2 + 2 * n ^ 3) := by ring
  rw [hexp2, hsq]
  ring

/-- Strict unit bounds $1 < \sqrt{2} < 2$. -/
theorem sqrt_two_bounds : (1 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 2 := by
  constructor
  · rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · have h4 : (2 : ℝ) = Real.sqrt 4 := by norm_num
    rw [h4]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **Universal Pointwise Moser Inequality**: for all $n \in \mathbb{N}$,
`√2 * n ≤ 4 * M n + 8`. -/
theorem sqrt_two_mul_le_four_mul_M_add_eight (n : ℕ) :
    Real.sqrt 2 * (n : ℝ) ≤ 4 * (M n : ℝ) + 8 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    positivity
  · set R : ℕ := Nat.floor (Real.sqrt 2 * (n : ℝ)) + 1
    have hsqrt := sqrt_two_bounds
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnonneg : 0 ≤ Real.sqrt 2 * (n : ℝ) := by positivity
    have hR_gt : Real.sqrt 2 * (n : ℝ) < (R : ℝ) := by
      dsimp [R]
      push_cast
      exact Nat.lt_floor_add_one (Real.sqrt 2 * (n : ℝ))
    have hR_le : (R : ℝ) ≤ Real.sqrt 2 * (n : ℝ) + 1 := by
      dsimp [R]
      push_cast
      linarith [Nat.floor_le hnonneg]
    have hdiff_nonneg : 0 ≤ (R : ℝ) - Real.sqrt 2 * (n : ℝ) := by linarith
    have hdiff_le_one : (R : ℝ) - Real.sqrt 2 * (n : ℝ) ≤ 1 := by linarith
    have hsq_le_one : ((R : ℝ) - Real.sqrt 2 * (n : ℝ)) ^ 2 ≤ 1 := by nlinarith
    have hR_ge_n : (n : ℝ) ≤ (R : ℝ) := by nlinarith [hsqrt.1]
    have hR_le_3n : (R : ℝ) ≤ 3 * (n : ℝ) := by nlinarith [hsqrt.2]
    have hlin_le : Real.sqrt 2 * (R : ℝ) + (n : ℝ) ≤ 7 * (n : ℝ) := by nlinarith [hsqrt.2]
    have hlin_nonneg : 0 ≤ Real.sqrt 2 * (R : ℝ) + (n : ℝ) := by positivity
    have herr1 : 4 * (n : ℝ) * ((R : ℝ) - Real.sqrt 2 * (n : ℝ)) ^ 2 *
        (Real.sqrt 2 * (R : ℝ) + (n : ℝ)) ≤ 28 * (n : ℝ) ^ 2 := by
      have h1 : ((R : ℝ) - Real.sqrt 2 * (n : ℝ)) ^ 2 * (Real.sqrt 2 * (R : ℝ) + (n : ℝ)) ≤
          1 * (7 * (n : ℝ)) := mul_le_mul hsq_le_one hlin_le hlin_nonneg (by norm_num)
      nlinarith
    have hR3_ge_n2 : (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 3 := by
      have hn2_le_n3 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith
      have hn3_le_R3 : (n : ℝ) ^ 3 ≤ (R : ℝ) ^ 3 := by gcongr
      linarith
    have hp_nat := moser_parametric_quadratic_le_M n R
    have hp_le : 12 * R ^ 2 * n ^ 2 ≤ 8 * n ^ 4 + n ^ 2 + 16 * R ^ 3 * M n := by
      have hsub : 4 * R * (4 * R ^ 2 - 1) ≤ 16 * R ^ 3 := by
        have : 4 * R * (4 * R ^ 2 - 1) ≤ 4 * R * (4 * R ^ 2) :=
          Nat.mul_le_mul_left (4 * R) (Nat.sub_le _ _)
        linarith
      have hmul : 4 * R * (4 * R ^ 2 - 1) * M n ≤ 16 * R ^ 3 * M n :=
        Nat.mul_le_mul_right (M n) hsub
      linarith
    have hp_real : 12 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤
        8 * (n : ℝ) ^ 4 + (n : ℝ) ^ 2 + 16 * (R : ℝ) ^ 3 * (M n : ℝ) := by
      exact_mod_cast hp_le
    have hid := moser_double_root_identity (R : ℝ) (n : ℝ)
    have hcub : 4 * (R : ℝ) ^ 3 * (Real.sqrt 2 * (n : ℝ)) ≤
        4 * (R : ℝ) ^ 3 * (4 * (M n : ℝ) + 8) := by
      nlinarith
    have hR3_pos : (0 : ℝ) < 4 * (R : ℝ) ^ 3 := by positivity
    exact le_of_mul_le_mul_left hcub hR3_pos

/-- Pointwise rationalized Moser lower bound on `MinOverlapQuotient n`:
for all $n \ge 1$, `√2 / 4 - 2 / n ≤ MinOverlapQuotient n`. -/
theorem sqrt_two_div_four_sub_two_div_le_minOverlapQuotient {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt 2 / 4 - 2 / (n : ℝ) ≤ MinOverlapQuotient n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlin := sqrt_two_mul_le_four_mul_M_add_eight n
  unfold MinOverlapQuotient
  rw [le_div_iff₀ hn0]
  have hcalc : (Real.sqrt 2 / 4 - 2 / (n : ℝ)) * (n : ℝ) =
      Real.sqrt 2 * (n : ℝ) / 4 - 2 := by
    field_simp [ne_of_gt hn0]
  linarith

/-- **Moser's (1959) Asymptotic Lower Bound**:
`Real.sqrt 2 / 4 ≤ atTop.liminf MinOverlapQuotient` ($\approx 0.35355339$). -/
theorem moser_sqrt_two_div_four_le_liminf :
    Real.sqrt 2 / 4 ≤ atTop.liminf MinOverlapQuotient := by
  have hub : ∀ n : ℕ, MinOverlapQuotient n ≤ 1 := minOverlapQuotient_le_one
  apply le_of_forall_pos_le_add
  intro ε hε
  have h1 : Real.sqrt 2 / 4 - ε ≤ atTop.liminf MinOverlapQuotient := by
    apply Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le atTop hub)
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 / ε)
    filter_upwards [eventually_ge_atTop (N₀ + 1)] with n hn
    have hn1 : 1 ≤ n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hstep := sqrt_two_div_four_sub_two_div_le_minOverlapQuotient hn1
    have hngt : 2 / ε < (n : ℝ) := by
      have hle : (N₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h2n : 2 / (n : ℝ) ≤ ε := by
      rw [div_le_iff₀ hn_pos]
      rw [div_lt_iff₀ hε] at hngt
      linarith
    linarith
  linarith

/-- **Strict Progression of Verified Asymptotic Bounds**:
`1 / 4 < 1 - (√2)⁻¹ < √2 / 4 ≤ atTop.liminf MinOverlapQuotient`, and
`atTop.limsup MinOverlapQuotient ≤ 2 / 5`. -/
theorem erdos_lt_scherk_lt_moser_lt_mrs :
    (1 : ℝ) / 4 < 1 - (Real.sqrt 2)⁻¹ ∧
    1 - (Real.sqrt 2)⁻¹ < Real.sqrt 2 / 4 ∧
    Real.sqrt 2 / 4 ≤ atTop.liminf MinOverlapQuotient ∧
    atTop.limsup MinOverlapQuotient ≤ (2 : ℝ) / 5 := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt := sqrt_two_bounds
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    have hne : Real.sqrt 2 ≠ 0 := by linarith
    rw [inv_eq_iff_eq_inv]
    apply eq_inv_of_mul_eq_one_left
    nlinarith
  refine ⟨?_, ?_, moser_sqrt_two_div_four_le_liminf, mrs_two_fifths_limsup_bound le_rfl⟩
  · rw [hinv]
    have hlt : Real.sqrt 2 < (3 : ℝ) / 2 := by nlinarith
    linarith
  · rw [hinv]
    have hlt : (4 : ℝ) / 3 < Real.sqrt 2 := by nlinarith
    linarith
end Erdos36.Proofs
