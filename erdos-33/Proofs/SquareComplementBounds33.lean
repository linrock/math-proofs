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
open Filter Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos33.Core

/-- Upstream formulation from `FormalConjectures/ErdosProblems/33.lean`: every natural number
`k` can be written as `a + n^2` for some `n : ℕ` and `a ∈ A`. -/
def AdditiveBasisCondition (A : Set ℕ) : Prop :=
  ∀ (k : ℕ), ∃ (n : ℕ) (a : ℕ), a ∈ A ∧ k = a + n ^ 2

/-- Global square additive complement predicate: every `n : ℕ` is of the form `k^2 + a`
with `a ∈ A` and `k : ℕ`. -/
def IsSquareAdditiveComplement (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ a ∈ A, ∃ k : ℕ, n = k ^ 2 + a

/-- Finite-horizon square additive complement predicate on `[0, N]`: every `n ≤ N`
is of the form `k^2 + a` with `a ∈ A` and `k : ℕ`. -/
def IsFiniteSquareComplementOn (A : Set ℕ) (N : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ N → ∃ a ∈ A, ∃ k : ℕ, n = k ^ 2 + a

/-- Finite intersection of `A` with `[1, N]`. -/
def prefixFinset (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (· ∈ A)

/-- Finite intersection of `A` with `[0, N] = Finset.range (N + 1)`. -/
def prefixFinset0 (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (· ∈ A)

/-- Prefix counting function `|A ∩ [1, N]|`. -/
def prefixCount (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/-- Prefix counting function `|A ∩ [0, N]|`. -/
def prefixCount0 (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (· ∈ A)).card

/-- Normalized prefix ratio `|A ∩ [1, N]| / √N` in `ℝ`. -/
def normalizedPrefixRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  (prefixCount A N : ℝ) / Real.sqrt (N : ℝ)

theorem prefixCount_eq_card_prefixFinset (A : Set ℕ) (N : ℕ) :
    prefixCount A N = (prefixFinset A N).card := rfl

theorem prefixCount0_eq_card_prefixFinset0 (A : Set ℕ) (N : ℕ) :
    prefixCount0 A N = (prefixFinset0 A N).card := rfl

/-- `IsSquareAdditiveComplement A` is equivalent to upstream `AdditiveBasisCondition A`. -/
theorem isSquareAdditiveComplement_iff_additiveBasisCondition (A : Set ℕ) :
    IsSquareAdditiveComplement A ↔ AdditiveBasisCondition A := by
  constructor
  · intro h k
    rcases h k with ⟨a, ha, n, rfl⟩
    exact ⟨n, a, ha, by omega⟩
  · intro h n
    rcases h n with ⟨k, a, ha, rfl⟩
    exact ⟨a, ha, k, by omega⟩

/-- Global square additive complements are finite-horizon complements on every `[0, N]`. -/
theorem isFiniteSquareComplementOn_of_isSquareAdditiveComplement {A : Set ℕ}
    (hA : IsSquareAdditiveComplement A) (N : ℕ) :
    IsFiniteSquareComplementOn A N := by
  intro n _
  exact hA n

/-- Zero membership necessity on any finite horizon `[0, N]`: to represent `0 = k^2 + a`,
one must have `0 ∈ A`. -/
theorem zero_mem_of_isFiniteSquareComplementOn {A : Set ℕ} {N : ℕ}
    (hA : IsFiniteSquareComplementOn A N) :
    0 ∈ A := by
  rcases hA 0 (Nat.zero_le N) with ⟨a, ha, k, hrep⟩
  have ha0 : a = 0 := by omega
  simpa [ha0] using ha

/-- Zero membership necessity for global square additive complements (`n = 0`). -/
theorem zero_mem_of_isSquareAdditiveComplement {A : Set ℕ}
    (hA : IsSquareAdditiveComplement A) :
    0 ∈ A :=
  zero_mem_of_isFiniteSquareComplementOn
    (isFiniteSquareComplementOn_of_isSquareAdditiveComplement hA 0)

theorem prefixFinset0_mono_nat (A : Set ℕ) {M N : ℕ} (hMN : M ≤ N) :
    prefixFinset0 A M ⊆ prefixFinset0 A N := by
  intro x hx
  simp only [prefixFinset0, Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

theorem prefixCount0_mono_nat (A : Set ℕ) {M N : ℕ} (hMN : M ≤ N) :
    prefixCount0 A M ≤ prefixCount0 A N :=
  Finset.card_le_card (prefixFinset0_mono_nat A hMN)

theorem zero_not_mem_prefixFinset (A : Set ℕ) (N : ℕ) :
    0 ∉ prefixFinset A N := by
  simp [prefixFinset]

theorem prefixFinset_subset_prefixFinset0 (A : Set ℕ) (N : ℕ) :
    prefixFinset A N ⊆ prefixFinset0 A N := by
  intro x hx
  simp only [prefixFinset, prefixFinset0, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

theorem prefixFinset0_subset_insert_zero_prefixFinset (A : Set ℕ) (N : ℕ) :
    prefixFinset0 A N ⊆ insert 0 (prefixFinset A N) := by
  intro x hx
  simp only [prefixFinset0, prefixFinset, Finset.mem_filter, Finset.mem_range,
    Finset.mem_insert, Finset.mem_Icc] at hx ⊢
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · exact Or.inl rfl
  · exact Or.inr ⟨⟨by omega, by omega⟩, hx.2⟩

theorem prefixFinset0_eq_insert_zero_of_zero_mem {A : Set ℕ} (h0 : 0 ∈ A) (N : ℕ) :
    prefixFinset0 A N = insert 0 (prefixFinset A N) := by
  apply Finset.Subset.antisymm (prefixFinset0_subset_insert_zero_prefixFinset A N)
  intro x hx
  rcases Finset.mem_insert.1 hx with rfl | hx2
  · simp [prefixFinset0, h0]
  · exact prefixFinset_subset_prefixFinset0 A N hx2

theorem prefixCount0_eq_prefixCount_add_one_of_zero_mem {A : Set ℕ} (h0 : 0 ∈ A) (N : ℕ) :
    prefixCount0 A N = prefixCount A N + 1 := by
  rw [prefixCount0_eq_card_prefixFinset0, prefixCount_eq_card_prefixFinset,
    prefixFinset0_eq_insert_zero_of_zero_mem h0 N,
    Finset.card_insert_of_notMem (zero_not_mem_prefixFinset A N)]

theorem prefixCount0_eq_prefixCount_add_one_of_isSquareAdditiveComplement {A : Set ℕ}
    (hA : IsSquareAdditiveComplement A) (N : ℕ) :
    prefixCount0 A N = prefixCount A N + 1 :=
  prefixCount0_eq_prefixCount_add_one_of_zero_mem (zero_mem_of_isSquareAdditiveComplement hA) N

/-- Bridge between upstream `(A ∩ Set.Icc 1 N).ncard` in `erdos_33` and `prefixCount A N`. -/
theorem ncard_inter_Icc_eq_prefixCount (A : Set ℕ) (N : ℕ) :
    (A ∩ Set.Icc 1 N).ncard = prefixCount A N := by
  have hcoe : ((prefixFinset A N : Finset ℕ) : Set ℕ) = A ∩ Set.Icc 1 N := by
    ext x
    simp only [Finset.mem_coe, prefixFinset, Finset.mem_filter, Finset.mem_Icc,
      Set.mem_inter_iff, Set.mem_Icc]
    tauto
  rw [← hcoe, Set.ncard_coe_finset]
  rfl

/-- Every representation `n = k^2 + a` with `n ≤ N` satisfies `a ≤ N`,
`k ≤ Nat.sqrt (N - a)`, and `k ≤ Nat.sqrt N`. -/
theorem rep_summand_bounds {n N a k : ℕ} (hn : n ≤ N) (hrep : n = k ^ 2 + a) :
    a ≤ N ∧ k ≤ Nat.sqrt (N - a) ∧ k ≤ Nat.sqrt N := by
  have ha : a ≤ N := by omega
  have hsq_sub : k * k ≤ N - a := by
    have hk2 : k ^ 2 = k * k := sq k
    omega
  have hk_sub : k ≤ Nat.sqrt (N - a) := Nat.le_sqrt.2 hsq_sub
  have hk_N : k ≤ Nat.sqrt N := le_trans hk_sub (Nat.sqrt_le_sqrt (Nat.sub_le N a))
  exact ⟨ha, hk_sub, hk_N⟩
/-- Exact integer square root of `m^2 - 1` for `m ≥ 1`: `Nat.sqrt (m^2 - 1) = m - 1`. -/
theorem sqrt_sq_sub_one {m : ℕ} (hm : 1 ≤ m) :
    Nat.sqrt (m ^ 2 - 1) = m - 1 := by
  apply le_antisymm
  · have hlt : Nat.sqrt (m ^ 2 - 1) < m := by
      rw [Nat.sqrt_lt]
      have hsq : m ^ 2 = m * m := sq m
      have hmpos : 0 < m * m := Nat.mul_pos hm hm
      omega
    omega
  · rw [Nat.le_sqrt]
    rcases Nat.exists_eq_add_of_le hm with ⟨d, rfl⟩
    have hd : 1 + d - 1 = d := by omega
    rw [hd]
    ring_nf
    omega

/-- For `m ≥ 1`, `Nat.sqrt (m^2 - 1) + 1 = m`. -/
theorem sqrt_sq_sub_one_add_one {m : ℕ} (hm : 1 ≤ m) :
    Nat.sqrt (m ^ 2 - 1) + 1 = m := by
  rw [sqrt_sq_sub_one hm]
  omega

/-- For a fixed `a ≤ N`, `moserFiber N a` is the set of integers `k^2 + a` with
`0 ≤ k ≤ Nat.sqrt (N - a)`. -/
def moserFiber (N a : ℕ) : Finset ℕ :=
  (Finset.range (Nat.sqrt (N - a) + 1)).image (fun k => k ^ 2 + a)

/-- The map `k ↦ k^2 + a` is injective on `ℕ`. -/
theorem sq_add_right_injective (a : ℕ) :
    Function.Injective (fun k : ℕ => k ^ 2 + a) := by
  intro k₁ k₂ h
  have hsq : k₁ * k₁ = k₂ * k₂ := by
    have h1 : k₁ ^ 2 = k₂ ^ 2 := Nat.add_right_cancel h
    simpa [sq] using h1
  exact Nat.mul_self_inj.1 hsq

/-- Exact cardinality of each Moser representation fiber:
`(moserFiber N a).card = Nat.sqrt (N - a) + 1`. -/
theorem card_moserFiber_eq (N a : ℕ) :
    (moserFiber N a).card = Nat.sqrt (N - a) + 1 := by
  unfold moserFiber
  rw [Finset.card_image_of_injective _ (sq_add_right_injective a), Finset.card_range]

/-- Every `n ∈ [0, N]` covered by `A` belongs to `moserFiber N a` for some `a ∈ prefixFinset0 A N`. -/
theorem range_subset_biUnion_moserFiber {A : Set ℕ} {N : ℕ}
    (hA : IsFiniteSquareComplementOn A N) :
    Finset.range (N + 1) ⊆ (prefixFinset0 A N).biUnion (moserFiber N) := by
  intro n hn
  have hn_le : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  rcases hA n hn_le with ⟨a, ha, k, hrep⟩
  rcases rep_summand_bounds hn_le hrep with ⟨haN, hk_sub, _⟩
  rw [Finset.mem_biUnion]
  refine ⟨a, ?_, ?_⟩
  · simp only [prefixFinset0, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ha⟩
  · unfold moserFiber
    refine Finset.mem_image.2 ⟨k, ?_, hrep.symm⟩
    simp only [Finset.mem_range]
    omega

/-- **Moser's Weighted Representation Lower Bound on `[0, N]`** (finite-horizon version):
for any `A` covering `[0, N]` as `k^2 + a`,
`N + 1 ≤ ∑ a ∈ prefixFinset0 A N, (Nat.sqrt (N - a) + 1)`. -/
theorem moser_weighted_lower_bound_on {A : Set ℕ} {N : ℕ}
    (hA : IsFiniteSquareComplementOn A N) :
    N + 1 ≤ ∑ a ∈ prefixFinset0 A N, (Nat.sqrt (N - a) + 1) := by
  have hsub := range_subset_biUnion_moserFiber hA
  have hcard1 : (Finset.range (N + 1)).card ≤ ((prefixFinset0 A N).biUnion (moserFiber N)).card :=
    Finset.card_le_card hsub
  have hcard2 : ((prefixFinset0 A N).biUnion (moserFiber N)).card ≤
      ∑ a ∈ prefixFinset0 A N, (moserFiber N a).card :=
    Finset.card_biUnion_le
  have hsum : (∑ a ∈ prefixFinset0 A N, (moserFiber N a).card) =
      ∑ a ∈ prefixFinset0 A N, (Nat.sqrt (N - a) + 1) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    exact card_moserFiber_eq N a
  simpa [Finset.card_range, hsum] using le_trans hcard1 hcard2

/-- For `a ≤ N`, the filtered square-index set `{k ≤ Nat.sqrt N | a ≤ N - k^2}` is exactly
`Finset.range (Nat.sqrt (N - a) + 1)`. -/
theorem filter_range_sqrt_le_sub_sq_eq {N a : ℕ} (ha : a ≤ N) :
    (Finset.range (Nat.sqrt N + 1)).filter (fun k => a ≤ N - k ^ 2) =
      Finset.range (Nat.sqrt (N - a) + 1) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk_range, hak⟩
    have hkN : k * k ≤ N := Nat.le_sqrt.1 (by omega)
    have hsq : k * k ≤ N - a := by
      have hk2 : k ^ 2 = k * k := sq k
      omega
    have hk_le : k ≤ Nat.sqrt (N - a) := Nat.le_sqrt.2 hsq
    omega
  · intro hk
    have hk_le : k ≤ Nat.sqrt (N - a) := by omega
    have hsq : k * k ≤ N - a := Nat.le_sqrt.1 hk_le
    have hk_N : k ≤ Nat.sqrt N := le_trans hk_le (Nat.sqrt_le_sqrt (Nat.sub_le N a))
    have hk2 : k ^ 2 = k * k := sq k
    refine ⟨by omega, by omega⟩

/-- For `k ≤ Nat.sqrt N`, filtering `prefixFinset0 A N` by `a ≤ N - k^2` yields
`prefixFinset0 A (N - k^2)`. -/
theorem filter_prefixFinset0_le_sub_sq_eq (A : Set ℕ) {N k : ℕ} :
    (prefixFinset0 A N).filter (fun a => a ≤ N - k ^ 2) =
      prefixFinset0 A (N - k ^ 2) := by
  ext a
  simp only [prefixFinset0, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, haA⟩, hak⟩
    exact ⟨by omega, haA⟩
  · rintro ⟨hak, haA⟩
    exact ⟨⟨by omega, haA⟩, by omega⟩

/-- **Moser–Abel Prefix-Integral Dual Identity**:
for any set `A ⊆ ℕ` and any horizon `N : ℕ`,
`∑ a ∈ prefixFinset0 A N, (Nat.sqrt (N - a) + 1) = ∑ k ∈ Finset.range (Nat.sqrt N + 1), prefixCount0 A (N - k^2)`. -/
theorem moser_abel_prefix_sum_identity (A : Set ℕ) (N : ℕ) :
    (∑ a ∈ prefixFinset0 A N, (Nat.sqrt (N - a) + 1)) =
      ∑ k ∈ Finset.range (Nat.sqrt N + 1), prefixCount0 A (N - k ^ 2) := by
  have hL :
      (∑ a ∈ prefixFinset0 A N, (Nat.sqrt (N - a) + 1)) =
        ∑ a ∈ prefixFinset0 A N,
          ∑ k ∈ Finset.range (Nat.sqrt N + 1), (if a ≤ N - k ^ 2 then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    have haN : a ≤ N := by
      simp only [prefixFinset0, Finset.mem_filter, Finset.mem_range] at ha
      omega
    rw [Finset.sum_boole, Nat.cast_id, filter_range_sqrt_le_sub_sq_eq haN, Finset.card_range]
  have hR :
      (∑ k ∈ Finset.range (Nat.sqrt N + 1), prefixCount0 A (N - k ^ 2)) =
        ∑ k ∈ Finset.range (Nat.sqrt N + 1),
          ∑ a ∈ prefixFinset0 A N, (if a ≤ N - k ^ 2 then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_boole, Nat.cast_id, filter_prefixFinset0_le_sub_sq_eq A,
      prefixCount0_eq_card_prefixFinset0]
  rw [hL, hR, Finset.sum_comm]

/-- **Moser Prefix-Integral Lower Bound** on `[0, N]`:
for any finite-horizon square additive complement `A` on `[0, N]`,
`N + 1 ≤ ∑ k ∈ Finset.range (Nat.sqrt N + 1), prefixCount0 A (N - k^2)`. -/
theorem moser_prefix_integral_lower_bound_on {A : Set ℕ} {N : ℕ}
    (hA : IsFiniteSquareComplementOn A N) :
    N + 1 ≤ ∑ k ∈ Finset.range (Nat.sqrt N + 1), prefixCount0 A (N - k ^ 2) := by
  rw [← moser_abel_prefix_sum_identity]
  exact moser_weighted_lower_bound_on hA

/-- The `m`-th consecutive square-gap block `[m^2, m^2 + 2m]`. -/
def squareGapBlock (m : ℕ) : Set ℕ :=
  {n : ℕ | m ^ 2 ≤ n ∧ n ≤ m ^ 2 + 2 * m}

/-- Every natural number `n` lies in the `m = Nat.sqrt n` square-gap block `[m^2, m^2 + 2m]`. -/
theorem mem_squareGapBlock_sqrt (n : ℕ) :
    n ∈ squareGapBlock (Nat.sqrt n) := by
  simp only [squareGapBlock, Set.mem_setOf_eq]
  have hle : (Nat.sqrt n) * (Nat.sqrt n) ≤ n := Nat.sqrt_le n
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have hsq : (Nat.sqrt n) ^ 2 = (Nat.sqrt n) * (Nat.sqrt n) := sq (Nat.sqrt n)
  refine ⟨by omega, ?_⟩
  nlinarith

/-- For every natural number `n`, the square-gap remainder `n - (Nat.sqrt n)^2` is at most
`2 * Nat.sqrt n`. -/
theorem nat_sub_sq_sqrt_le_two_mul_sqrt (n : ℕ) :
    n - (Nat.sqrt n) ^ 2 ≤ 2 * Nat.sqrt n := by
  rcases mem_squareGapBlock_sqrt n with ⟨_, hhi⟩
  omega
/-- Block decomposition of a sum over `Finset.range (R * m)` into `R` blocks of length `m`. -/
theorem sum_range_mul_eq_sum_range_sum_range (f : ℕ → ℕ) (R m : ℕ) :
    (∑ k ∈ Finset.range (R * m), f k) =
      ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range m, f (r * m + j) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Discrete Cilleruelo step-function ceiling height `h(R, r) = ⌊√(R^2 - 1 - r^2)⌋ + 1`. -/
def cillerueloStepHeight (R r : ℕ) : ℕ :=
  Nat.sqrt (R ^ 2 - 1 - r ^ 2) + 1

/-- Total discrete quarter-circle step sum `S(R) = ∑_{r=0}^{R-1} h(R, r)`. -/
def cillerueloStepSum (R : ℕ) : ℕ :=
  ∑ r ∈ Finset.range R, cillerueloStepHeight R r

/-- Every step height `cillerueloStepHeight R r` is at least `1`. -/
theorem cillerueloStepHeight_pos (R r : ℕ) :
    1 ≤ cillerueloStepHeight R r := by
  unfold cillerueloStepHeight
  omega

/-- Key square-dominance property of `cillerueloStepHeight`:
for all `R, r : ℕ`, `R^2 - r^2 ≤ (cillerueloStepHeight R r)^2`. -/
theorem sub_sq_le_cillerueloStepHeight_sq (R r : ℕ) :
    R ^ 2 - r ^ 2 ≤ (cillerueloStepHeight R r) ^ 2 := by
  unfold cillerueloStepHeight
  have hlt : R ^ 2 - 1 - r ^ 2 <
      (Nat.sqrt (R ^ 2 - 1 - r ^ 2) + 1) * (Nat.sqrt (R ^ 2 - 1 - r ^ 2) + 1) :=
    Nat.lt_succ_sqrt (R ^ 2 - 1 - r ^ 2)
  have hsq : (Nat.sqrt (R ^ 2 - 1 - r ^ 2) + 1) ^ 2 =
      (Nat.sqrt (R ^ 2 - 1 - r ^ 2) + 1) * (Nat.sqrt (R ^ 2 - 1 - r ^ 2) + 1) := sq _
  omega

/-- Lower bound `R ≤ cillerueloStepSum R` for all `R : ℕ`. -/
theorem cillerueloStepSum_ge_self (R : ℕ) :
    R ≤ cillerueloStepSum R := by
  unfold cillerueloStepSum
  calc
    R = ∑ _r ∈ Finset.range R, 1 := by simp
    _ ≤ ∑ r ∈ Finset.range R, cillerueloStepHeight R r :=
      Finset.sum_le_sum (fun r _ => cillerueloStepHeight_pos R r)

/-- For `R ≥ 1`, `1 ≤ cillerueloStepSum R`. -/
theorem cillerueloStepSum_pos {R : ℕ} (hR : 1 ≤ R) :
    1 ≤ cillerueloStepSum R :=
  le_trans hR (cillerueloStepSum_ge_self R)

/-- Argument monotonicity bound on the `r`-th block `k = r * m + j`:
`(R * m)^2 - 1 - (r * m + j)^2 ≤ (cillerueloStepHeight R r * m)^2 - 1`. -/
theorem cilleruelo_block_arg_bound (R r m j : ℕ) :
    (R * m) ^ 2 - 1 - (r * m + j) ^ 2 ≤ (cillerueloStepHeight R r * m) ^ 2 - 1 := by
  have h1 : (r * m) ^ 2 ≤ (r * m + j) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right (r * m) j) 2
  have h2 : (R * m) ^ 2 - 1 - (r * m + j) ^ 2 ≤ (R * m) ^ 2 - (r * m) ^ 2 - 1 := by omega
  have h3 : (R * m) ^ 2 - (r * m) ^ 2 = (R ^ 2 - r ^ 2) * m ^ 2 := by
    rw [mul_pow, mul_pow, ← Nat.sub_mul]
  have h4 : (R ^ 2 - r ^ 2) * m ^ 2 ≤ (cillerueloStepHeight R r) ^ 2 * m ^ 2 :=
    Nat.mul_le_mul_right (m ^ 2) (sub_sq_le_cillerueloStepHeight_sq R r)
  have h5 : (cillerueloStepHeight R r) ^ 2 * m ^ 2 = (cillerueloStepHeight R r * m) ^ 2 := by
    rw [mul_pow]
  omega

/-- Every step horizon `(cillerueloStepHeight R r * m)^2` dominates the base scale `m`. -/
theorem step_horizon_ge_base (R r m : ℕ) :
    m ≤ (cillerueloStepHeight R r * m) ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : 1 ≤ cillerueloStepHeight R r := cillerueloStepHeight_pos R r
    have h2 : m ≤ cillerueloStepHeight R r * m := Nat.le_mul_of_pos_left m h1
    have h3 : cillerueloStepHeight R r * m ≤ (cillerueloStepHeight R r * m) ^ 2 := by
      rw [sq]
      exact Nat.le_mul_of_pos_right _ (Nat.mul_pos h1 hm)
    exact le_trans h2 h3

/-- Exact block decomposition of the Moser–Abel prefix sum at `N = (R * m)^2 - 1`. -/
theorem moser_abel_sum_block_decomposition (A : Set ℕ) {R m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.range (Nat.sqrt ((R * m) ^ 2 - 1) + 1), prefixCount0 A ((R * m) ^ 2 - 1 - k ^ 2)) =
      ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range m, prefixCount0 A ((R * m) ^ 2 - 1 - (r * m + j) ^ 2) := by
  have hRm : 1 ≤ R * m := Nat.mul_pos hR hm
  rw [sqrt_sq_sub_one_add_one hRm,
    sum_range_mul_eq_sum_range_sum_range (fun k => prefixCount0 A ((R * m) ^ 2 - 1 - k ^ 2)) R m]

/-- Upper bound on the `r`-th block of the Moser–Abel prefix sum at `N = (R * m)^2 - 1`. -/
theorem moser_abel_block_sum_le_step_sub_one (A : Set ℕ) (R r m : ℕ) :
    (∑ j ∈ Finset.range m, prefixCount0 A ((R * m) ^ 2 - 1 - (r * m + j) ^ 2)) ≤
      m * prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2 - 1) := by
  calc
    (∑ j ∈ Finset.range m, prefixCount0 A ((R * m) ^ 2 - 1 - (r * m + j) ^ 2))
        ≤ ∑ _j ∈ Finset.range m, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2 - 1) :=
          Finset.sum_le_sum (fun j _ => prefixCount0_mono_nat A (cilleruelo_block_arg_bound R r m j))
    _ = m * prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2 - 1) := by simp

/-- Upper bound on the full Moser–Abel prefix sum at `N = (R * m)^2 - 1` by the Cilleruelo
step-function sum at `(cillerueloStepHeight R r * m)^2 - 1`. -/
theorem moser_abel_sum_le_cilleruelo_step_sub_one (A : Set ℕ) {R m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.range (Nat.sqrt ((R * m) ^ 2 - 1) + 1), prefixCount0 A ((R * m) ^ 2 - 1 - k ^ 2)) ≤
      m * ∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2 - 1) := by
  rw [moser_abel_sum_block_decomposition A hR hm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun r _ => moser_abel_block_sum_le_step_sub_one A R r m)

/-- **Universal Finite-Horizon Cilleruelo–Moser Step-Function Lower Bound** at `N = (R * m)^2 - 1`:
for any `R ≥ 1`, `m ≥ 1`, and `A` covering `[0, (R * m)^2 - 1]`,
`R^2 * m ≤ ∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m)^2 - 1)`. -/
theorem cilleruelo_step_sub_one_sum_lower_bound_on {A : Set ℕ} {R m : ℕ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hA : IsFiniteSquareComplementOn A ((R * m) ^ 2 - 1)) :
    R ^ 2 * m ≤ ∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2 - 1) := by
  have hmoser := moser_prefix_integral_lower_bound_on hA
  have hstep := moser_abel_sum_le_cilleruelo_step_sub_one A hR hm
  have hpos : 1 ≤ (R * m) ^ 2 := by
    have hRm : 1 ≤ R * m := Nat.mul_pos hR hm
    have : 1 * 1 ≤ (R * m) * (R * m) := Nat.mul_le_mul hRm hRm
    simpa [sq] using this
  have h1 : (R * m) ^ 2 ≤
      m * ∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2 - 1) := by
    omega
  have h2 : m * (R ^ 2 * m) ≤
      m * ∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2 - 1) := by
    have heq : m * (R ^ 2 * m) = (R * m) ^ 2 := by ring
    omega
  exact Nat.le_of_mul_le_mul_left h2 hm

/-- **Universal Finite-Horizon Cilleruelo–Moser Step-Function Lower Bound** at exact squares
`(cillerueloStepHeight R r * m)^2`. -/
theorem cilleruelo_step_sq_sum_lower_bound_on {A : Set ℕ} {R m : ℕ}
    (hR : 1 ≤ R) (hm : 1 ≤ m) (hA : IsFiniteSquareComplementOn A ((R * m) ^ 2 - 1)) :
    R ^ 2 * m ≤ ∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2) := by
  refine le_trans (cilleruelo_step_sub_one_sum_lower_bound_on hR hm hA) ?_
  exact Finset.sum_le_sum (fun r _ => prefixCount0_mono_nat A (Nat.sub_le _ 1))

/-- **Universal Global Cilleruelo–Moser Step-Function Lower Bound** at exact squares
`(cillerueloStepHeight R r * m)^2`. -/
theorem cilleruelo_step_sq_sum_lower_bound {A : Set ℕ}
    (hA : IsSquareAdditiveComplement A) {R m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) :
    R ^ 2 * m ≤ ∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2) :=
  cilleruelo_step_sq_sum_lower_bound_on hR hm
    (isFiniteSquareComplementOn_of_isSquareAdditiveComplement hA ((R * m) ^ 2 - 1))

/-- **Universal Global Cilleruelo–Moser Step-Function Lower Bound** for `prefixCount A`
(excluding `0`): `R^2 * m ≤ (∑_{r < R} prefixCount A ((h(R, r) * m)^2)) + R`. -/
theorem cilleruelo_step_prefixCount_sq_sum_lower_bound {A : Set ℕ}
    (hA : IsSquareAdditiveComplement A) {R m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) :
    R ^ 2 * m ≤ (∑ r ∈ Finset.range R, prefixCount A ((cillerueloStepHeight R r * m) ^ 2)) + R := by
  have h0 := cilleruelo_step_sq_sum_lower_bound hA hR hm
  have heq :
      (∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2)) =
        (∑ r ∈ Finset.range R, prefixCount A ((cillerueloStepHeight R r * m) ^ 2)) + R := by
    calc
      (∑ r ∈ Finset.range R, prefixCount0 A ((cillerueloStepHeight R r * m) ^ 2))
          = ∑ r ∈ Finset.range R, (prefixCount A ((cillerueloStepHeight R r * m) ^ 2) + 1) := by
            refine Finset.sum_congr rfl (fun r _ => ?_)
            exact prefixCount0_eq_prefixCount_add_one_of_isSquareAdditiveComplement hA _
      _ = (∑ r ∈ Finset.range R, prefixCount A ((cillerueloStepHeight R r * m) ^ 2)) + R := by
            rw [Finset.sum_add_distrib]
            simp
  omega

/-- Exact factoring of `prefixCount A ((cillerueloStepHeight R r * m)^2)` as
`cillerueloStepHeight R r * m * normalizedPrefixRatio A ((cillerueloStepHeight R r * m)^2)`. -/
theorem prefixCount_step_sq_eq_mul_normalizedPrefixRatio
    (A : Set ℕ) (R r : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (prefixCount A ((cillerueloStepHeight R r * m) ^ 2) : ℝ) =
      (cillerueloStepHeight R r : ℝ) * (m : ℝ) *
        normalizedPrefixRatio A ((cillerueloStepHeight R r * m) ^ 2) := by
  unfold normalizedPrefixRatio
  have hpos : 0 < (cillerueloStepHeight R r : ℝ) * (m : ℝ) :=
    mul_pos (Nat.cast_pos.2 (cillerueloStepHeight_pos R r)) (Nat.cast_pos.2 hm)
  have hsqrt : Real.sqrt (((cillerueloStepHeight R r * m) ^ 2 : ℕ) : ℝ) =
      (cillerueloStepHeight R r : ℝ) * (m : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_mul, Real.sqrt_sq (le_of_lt hpos)]
  rw [hsqrt, mul_div_cancel₀ _ (ne_of_gt hpos)]

/-- **Universal Step-Horizon Attainment for `normalizedPrefixRatio`** (excluding `0`):
for any global square additive complement `A` and all `R ≥ 1`, `m ≥ 1`, there exists
`r ∈ Finset.range R` such that
`((R : ℝ)^2 - (R : ℝ) / (m : ℝ)) / (cillerueloStepSum R : ℝ) ≤ normalizedPrefixRatio A ((cillerueloStepHeight R r * m)^2)`. -/
theorem exists_step_horizon_normalizedPrefixRatio_ge {A : Set ℕ}
    (hA : IsSquareAdditiveComplement A) {R m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) :
    ∃ r ∈ Finset.range R,
      ((R : ℝ) ^ 2 - (R : ℝ) / (m : ℝ)) / (cillerueloStepSum R : ℝ) ≤
        normalizedPrefixRatio A ((cillerueloStepHeight R r * m) ^ 2) := by
  by_contra hnot
  have hlt : ∀ r ∈ Finset.range R,
      normalizedPrefixRatio A ((cillerueloStepHeight R r * m) ^ 2) <
        ((R : ℝ) ^ 2 - (R : ℝ) / (m : ℝ)) / (cillerueloStepSum R : ℝ) := by
    intro r hr
    by_contra hge
    exact hnot ⟨r, hr, not_lt.1 hge⟩
  have hsum_lt :
      (∑ r ∈ Finset.range R, (prefixCount A ((cillerueloStepHeight R r * m) ^ 2) : ℝ)) + (R : ℝ) <
        (R : ℝ) ^ 2 * (m : ℝ) := by
    have hlt1 :
        (∑ r ∈ Finset.range R, (prefixCount A ((cillerueloStepHeight R r * m) ^ 2) : ℝ)) <
          (R : ℝ) ^ 2 * (m : ℝ) - (R : ℝ) := by
      calc
        (∑ r ∈ Finset.range R, (prefixCount A ((cillerueloStepHeight R r * m) ^ 2) : ℝ))
            = ∑ r ∈ Finset.range R,
                (cillerueloStepHeight R r : ℝ) * (m : ℝ) *
                  normalizedPrefixRatio A ((cillerueloStepHeight R r * m) ^ 2) := by
              refine Finset.sum_congr rfl (fun r _ => ?_)
              exact prefixCount_step_sq_eq_mul_normalizedPrefixRatio A R r hm
        _ < ∑ r ∈ Finset.range R,
              (cillerueloStepHeight R r : ℝ) * (m : ℝ) *
                (((R : ℝ) ^ 2 - (R : ℝ) / (m : ℝ)) / (cillerueloStepSum R : ℝ)) := by
            apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega))
            intro r hr
            have hpos_h : 0 < (cillerueloStepHeight R r : ℝ) :=
              Nat.cast_pos.2 (cillerueloStepHeight_pos R r)
            have hpos_m : 0 < (m : ℝ) := Nat.cast_pos.2 hm
            exact mul_lt_mul_of_pos_left (hlt r hr) (mul_pos hpos_h hpos_m)
        _ = (cillerueloStepSum R : ℝ) *
              ((m : ℝ) * (((R : ℝ) ^ 2 - (R : ℝ) / (m : ℝ)) / (cillerueloStepSum R : ℝ))) := by
            unfold cillerueloStepSum
            rw [Nat.cast_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun r _ => by ring)
        _ = (R : ℝ) ^ 2 * (m : ℝ) - (R : ℝ) := by
            have hsum_pos : (cillerueloStepSum R : ℝ) ≠ 0 := by
              exact_mod_cast ne_of_gt (cillerueloStepSum_pos hR)
            have hm_pos : (m : ℝ) ≠ 0 := by
              exact_mod_cast ne_of_gt hm
            field_simp [hsum_pos, hm_pos]
    linarith
  have hsum_ge : (R : ℝ) ^ 2 * (m : ℝ) ≤
      (∑ r ∈ Finset.range R, (prefixCount A ((cillerueloStepHeight R r * m) ^ 2) : ℝ)) + (R : ℝ) := by
    exact_mod_cast cilleruelo_step_prefixCount_sq_sum_lower_bound hA hR hm
  linarith

/-- At `R = 60`, `cillerueloStepSum 60 = 2879`, yielding the ratio `3600/2879 ≈ 1.2504 > 5/4`. -/
theorem cillerueloStepSum_sixty : cillerueloStepSum 60 = 2879 := by
  norm_num [cillerueloStepSum, cillerueloStepHeight, Finset.sum_range_succ]

/-- Epsilon-free subsequential lower bound `5/4 = 1.25 ≤ normalizedPrefixRatio A N`
for arbitrarily large `N ≥ M` (proved via `R = 60`, `S(60) = 2879`). -/
theorem exists_ge_five_fourths_normalizedPrefixRatio {A : Set ℕ}
    (hA : IsSquareAdditiveComplement A) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ (5 : ℝ) / 4 ≤ normalizedPrefixRatio A N := by
  let m : ℕ := max M 49
  have hm49 : 49 ≤ m := le_max_right M 49
  have hm1 : 1 ≤ m := by omega
  have hmM : M ≤ m := le_max_left M 49
  rcases exists_step_horizon_normalizedPrefixRatio_ge hA (R := 60) (by omega) hm1 with ⟨r, _, hr_ge⟩
  refine ⟨(cillerueloStepHeight 60 r * m) ^ 2,
    le_trans hmM (step_horizon_ge_base 60 r m), ?_⟩
  rw [cillerueloStepSum_sixty] at hr_ge
  have hm_real : (49 : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hm49
  have hdiv_le : (60 : ℝ) / (m : ℝ) ≤ (60 : ℝ) / 49 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm_real
  linarith

/-- Exact coercion identity bridging upstream `((A ∩ Set.Icc 1 N).ncard : EReal) / (√N : EReal)`
to `(normalizedPrefixRatio A N : EReal)`. -/
theorem ereal_ncard_div_sqrt_eq_coe_normalizedPrefixRatio (A : Set ℕ) (N : ℕ) :
    ((A ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal) =
      (normalizedPrefixRatio A N : EReal) := by
  rw [ncard_inter_Icc_eq_prefixCount]
  unfold normalizedPrefixRatio
  rw [EReal.coe_div, EReal.coe_natCast]

/-- Transfer from cofinal real lower bounds `∀ M, ∃ N ≥ M, c ≤ normalizedPrefixRatio A N`
to the upstream `EReal` `Filter.atTop.limsup`. -/
theorem coe_le_limsup_ncard_div_sqrt_of_forall_exists_ge {A : Set ℕ} {c : ℝ}
    (h : ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ c ≤ normalizedPrefixRatio A N) :
    (c : EReal) ≤ Filter.atTop.limsup (fun N : ℕ =>
      ((A ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) := by
  refine Filter.le_limsup_of_frequently_le ?_ (Filter.isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
  rw [Filter.frequently_atTop]
  intro M
  rcases h M with ⟨N, hMN, hN⟩
  refine ⟨N, hMN, ?_⟩
  rw [ereal_ncard_div_sqrt_eq_coe_normalizedPrefixRatio]
  exact EReal.coe_le_coe_iff.2 hN

/-- Unconditional `5/4 = 1.25` lower bound on the `erdos_33` infimum. -/
theorem five_fourths_le_iInf_limsup :
    (((5 : ℝ) / 4 : ℝ) : EReal) ≤
      ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
        ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) := by
  refine le_iInf (fun A => ?_)
  exact coe_le_limsup_ncard_div_sqrt_of_forall_exists_ge
    (exists_ge_five_fourths_normalizedPrefixRatio
      ((isSquareAdditiveComplement_iff_additiveBasisCondition A.1).2 A.2))

/-- The upstream statement `erdos_33.variants.one_mem_lowerBounds`, obtained from the `5/4`
step-function bound (`formal-conjectures/FormalConjectures/ErdosProblems/33.lean`). -/
theorem erdos_33_variants_one_mem_lowerBounds :
    1 < ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
      ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) := by
  have h1 : (1 : EReal) < (((5 : ℝ) / 4 : ℝ) : EReal) := by
    exact_mod_cast (by norm_num : (1 : ℝ) < (5 : ℝ) / 4)
  exact lt_of_lt_of_le h1 five_fourths_le_iInf_limsup
/-- Shifted block interval `[B, B + 2 * M]` in Wouter van Doorn's construction. -/
def vanDoornBlock (B M : ℕ) : Set ℕ :=
  {a : ℕ | B ≤ a ∧ a ≤ B + 2 * M}

/-- Recursive starting point of the `j`-th van Doorn block for a width sequence `M : ℕ → ℕ`:
`B_0 = 0` and `B_{j+1} = B_j + (M j)^2 + 2 * M j`. -/
def vanDoornBlockStart (M : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => vanDoornBlockStart M j + (M j) ^ 2 + 2 * M j

/-- Global union of van Doorn shifted block intervals across all scales `j : ℕ`. -/
def vanDoornUnion (M : ℕ → ℕ) : Set ℕ :=
  ⋃ j : ℕ, vanDoornBlock (vanDoornBlockStart M j) (M j)

/-- For every integer `n ∈ [B, B + M^2 + 2 * M]`, subtracting `(Nat.sqrt (n - B))^2`
lands inside the shifted block interval `vanDoornBlock B M = [B, B + 2 * M]`. -/
theorem mem_vanDoornBlock_sub_sq_sqrt {B M n : ℕ}
    (hB : B ≤ n) (hn : n ≤ B + M ^ 2 + 2 * M) :
    n - (Nat.sqrt (n - B)) ^ 2 ∈ vanDoornBlock B M := by
  have hk_le : Nat.sqrt (n - B) ≤ M := by
    apply Nat.le_of_lt_succ
    rw [Nat.sqrt_lt]
    have hsucc : M.succ * M.succ = M ^ 2 + 2 * M + 1 := by
      change (M + 1) * (M + 1) = M ^ 2 + 2 * M + 1
      ring
    omega
  have hsq_le : (Nat.sqrt (n - B)) ^ 2 ≤ n - B := by
    simpa [sq] using Nat.sqrt_le (n - B)
  have hgap : n - B - (Nat.sqrt (n - B)) ^ 2 ≤ 2 * Nat.sqrt (n - B) :=
    nat_sub_sq_sqrt_le_two_mul_sqrt (n - B)
  simp only [vanDoornBlock, Set.mem_setOf_eq]
  omega

/-- **Van Doorn Single-Block Covering Lemma**:
every integer `n ∈ [B, B + M^2 + 2 * M]` can be written as `k^2 + a` with
`a ∈ vanDoornBlock B M` and `k ≤ M`. -/
theorem exists_rep_in_vanDoornBlock {B M n : ℕ}
    (hB : B ≤ n) (hn : n ≤ B + M ^ 2 + 2 * M) :
    ∃ a ∈ vanDoornBlock B M, ∃ k ≤ M, n = k ^ 2 + a := by
  have hmem := mem_vanDoornBlock_sub_sq_sqrt hB hn
  have hk_le : Nat.sqrt (n - B) ≤ M := by
    apply Nat.le_of_lt_succ
    rw [Nat.sqrt_lt]
    have hsucc : M.succ * M.succ = M ^ 2 + 2 * M + 1 := by
      change (M + 1) * (M + 1) = M ^ 2 + 2 * M + 1
      ring
    omega
  have hsq_le : (Nat.sqrt (n - B)) ^ 2 ≤ n - B := by
    simpa [sq] using Nat.sqrt_le (n - B)
  exact ⟨n - (Nat.sqrt (n - B)) ^ 2, hmem, Nat.sqrt (n - B), hk_le, by omega⟩

/-- Monotonicity of the recursive block start sequence `vanDoornBlockStart M`. -/
theorem vanDoornBlockStart_mono (M : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    vanDoornBlockStart M i ≤ vanDoornBlockStart M j := by
  induction hij with
  | refl => exact le_rfl
  | @step m _ ih =>
      simp only [vanDoornBlockStart]
      omega

/-- The union of the first `K + 1` van Doorn blocks covers the entire contiguous horizon
`[0, vanDoornBlockStart M (K + 1)]` as `k^2 + a`. -/
theorem isFiniteSquareComplementOn_biUnion_vanDoornBlock (M : ℕ → ℕ) (K : ℕ) :
    IsFiniteSquareComplementOn
      (⋃ j ≤ K, vanDoornBlock (vanDoornBlockStart M j) (M j))
      (vanDoornBlockStart M (K + 1)) := by
  induction K with
  | zero =>
      intro n hn
      simp only [vanDoornBlockStart, zero_add] at hn
      rcases exists_rep_in_vanDoornBlock (Nat.zero_le n) (by simpa [vanDoornBlockStart] using hn)
        with ⟨a, ha, k, _, hrep⟩
      refine ⟨a, ?_, k, hrep⟩
      exact Set.mem_iUnion₂.2 ⟨0, le_rfl, ha⟩
  | succ K ih =>
      intro n hn
      by_cases hle : n ≤ vanDoornBlockStart M (K + 1)
      · rcases ih n hle with ⟨a, ha, k, hrep⟩
        rcases Set.mem_iUnion₂.1 ha with ⟨j, hj, haj⟩
        exact ⟨a, Set.mem_iUnion₂.2 ⟨j, Nat.le_succ_of_le hj, haj⟩, k, hrep⟩
      · have hgt : vanDoornBlockStart M (K + 1) ≤ n := by omega
        simp only [vanDoornBlockStart] at hn
        rcases exists_rep_in_vanDoornBlock hgt hn with ⟨a, ha, k, _, hrep⟩
        exact ⟨a, Set.mem_iUnion₂.2 ⟨K + 1, le_rfl, ha⟩, k, hrep⟩

/-- For any positive block-width sequence `M` (`∀ j, 1 ≤ M j`), the block starts grow
at least linearly: `3 * k ≤ vanDoornBlockStart M k`. -/
theorem three_mul_le_vanDoornBlockStart_of_pos {M : ℕ → ℕ}
    (hM : ∀ j : ℕ, 1 ≤ M j) (k : ℕ) :
    3 * k ≤ vanDoornBlockStart M k := by
  induction k with
  | zero => simp [vanDoornBlockStart]
  | succ k ih =>
      simp only [vanDoornBlockStart]
      have hk1 : 1 ≤ M k := hM k
      have hk2 : 1 ≤ (M k) ^ 2 := by
        have : 1 * 1 ≤ M k * M k := Nat.mul_le_mul hk1 hk1
        simpa [sq] using this
      omega

/-- For every positive block-width sequence `M : ℕ → ℕ`, `vanDoornUnion M` is a global
square additive complement. -/
theorem isSquareAdditiveComplement_vanDoornUnion {M : ℕ → ℕ}
    (hM : ∀ j : ℕ, 1 ≤ M j) :
    IsSquareAdditiveComplement (vanDoornUnion M) := by
  intro n
  have hbound : n ≤ vanDoornBlockStart M (n + 1) := by
    have h3 := three_mul_le_vanDoornBlockStart_of_pos hM (n + 1)
    omega
  rcases isFiniteSquareComplementOn_biUnion_vanDoornBlock M n n hbound with ⟨a, ha, k, hrep⟩
  rcases Set.mem_iUnion₂.1 ha with ⟨j, _, haj⟩
  exact ⟨a, Set.mem_iUnion.2 ⟨j, haj⟩, k, hrep⟩

/-- For every positive block-width sequence `M : ℕ → ℕ`, `vanDoornUnion M` satisfies the
upstream `AdditiveBasisCondition` of `FormalConjectures/ErdosProblems/33.lean`. -/
theorem additiveBasisCondition_vanDoornUnion {M : ℕ → ℕ}
    (hM : ∀ j : ℕ, 1 ≤ M j) :
    AdditiveBasisCondition (vanDoornUnion M) :=
  (isSquareAdditiveComplement_iff_additiveBasisCondition (vanDoornUnion M)).1
    (isSquareAdditiveComplement_vanDoornUnion hM)
/-- For any positive width sequence `M` and `K ≥ 1`, `1 ≤ vanDoornBlockStart M K`. -/
theorem one_le_vanDoornBlockStart_of_pos {M : ℕ → ℕ} (hM : ∀ j : ℕ, 1 ≤ M j)
    {K : ℕ} (hK : 1 ≤ K) :
    1 ≤ vanDoornBlockStart M K := by
  have h3 := three_mul_le_vanDoornBlockStart_of_pos hM K
  omega

/-- Exact finite-horizon truncation of the infinite union `vanDoornUnion M` on `prefixFinset0`:
for all `N < vanDoornBlockStart M (K + 1)`, only the first `K + 1` blocks `j ∈ Finset.range (K + 1)`
can intersect `[0, N]`. -/
theorem prefixFinset0_vanDoornUnion_eq_biUnion_of_lt (M : ℕ → ℕ) {K N : ℕ}
    (hN : N < vanDoornBlockStart M (K + 1)) :
    prefixFinset0 (vanDoornUnion M) N =
      (Finset.range (K + 1)).biUnion
        (fun j => prefixFinset0 (vanDoornBlock (vanDoornBlockStart M j) (M j)) N) := by
  ext x
  simp only [prefixFinset0, vanDoornUnion, Finset.mem_filter, Finset.mem_range,
    Set.mem_iUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨hxN, j, hxj⟩
    have hj : j < K + 1 := by
      by_contra hge
      have hle : vanDoornBlockStart M (K + 1) ≤ vanDoornBlockStart M j :=
        vanDoornBlockStart_mono M (Nat.le_of_not_lt hge)
      simp only [vanDoornBlock, Set.mem_setOf_eq] at hxj
      omega
    exact ⟨j, hj, hxN, hxj⟩
  · rintro ⟨j, _, hxN, hxj⟩
    exact ⟨hxN, j, hxj⟩

/-- Each shifted block `vanDoornBlock B M` contributes at most `2 * M + 1` elements to `prefixCount0`. -/
theorem prefixCount0_vanDoornBlock_le_two_mul_add_one (B M N : ℕ) :
    prefixCount0 (vanDoornBlock B M) N ≤ 2 * M + 1 := by
  rw [prefixCount0_eq_card_prefixFinset0]
  have hsub : prefixFinset0 (vanDoornBlock B M) N ⊆ Finset.Icc B (B + 2 * M) := by
    intro x hx
    simp only [prefixFinset0, vanDoornBlock, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Icc, Set.mem_setOf_eq] at hx ⊢
    exact hx.2
  calc
    (prefixFinset0 (vanDoornBlock B M) N).card ≤ (Finset.Icc B (B + 2 * M)).card :=
      Finset.card_le_card hsub
    _ = 2 * M + 1 := by
      rw [Nat.card_Icc]
      omega

/-- Universal upper bound on `prefixCount0 (vanDoornUnion M) N` for `N < vanDoornBlockStart M (K + 1)`:
`prefixCount0 (vanDoornUnion M) N ≤ 2 * (∑_{j=0}^K M j) + (K + 1)`. -/
theorem prefixCount0_vanDoornUnion_le_of_lt (M : ℕ → ℕ) {K N : ℕ}
    (hN : N < vanDoornBlockStart M (K + 1)) :
    prefixCount0 (vanDoornUnion M) N ≤
      2 * (∑ j ∈ Finset.range (K + 1), M j) + (K + 1) := by
  rw [prefixCount0_eq_card_prefixFinset0, prefixFinset0_vanDoornUnion_eq_biUnion_of_lt M hN]
  calc
    ((Finset.range (K + 1)).biUnion
      (fun j => prefixFinset0 (vanDoornBlock (vanDoornBlockStart M j) (M j)) N)).card
        ≤ ∑ j ∈ Finset.range (K + 1),
            (prefixFinset0 (vanDoornBlock (vanDoornBlockStart M j) (M j)) N).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (K + 1), (2 * M j + 1) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [← prefixCount0_eq_card_prefixFinset0]
        exact prefixCount0_vanDoornBlock_le_two_mul_add_one _ _ _
    _ = 2 * (∑ j ∈ Finset.range (K + 1), M j) + (K + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp

/-- Universal upper bound on `prefixCount (vanDoornUnion M) N` for `N < vanDoornBlockStart M (K + 1)`:
since `0 ∈ vanDoornUnion M`, `prefixCount (vanDoornUnion M) N ≤ 2 * (∑_{j=0}^K M j) + K`. -/
theorem prefixCount_vanDoornUnion_le_of_lt (M : ℕ → ℕ) {K N : ℕ}
    (hN : N < vanDoornBlockStart M (K + 1)) :
    prefixCount (vanDoornUnion M) N ≤
      2 * (∑ j ∈ Finset.range (K + 1), M j) + K := by
  have h0 : 0 ∈ vanDoornUnion M := by
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    simp [vanDoornBlock, vanDoornBlockStart]
  have heq := prefixCount0_eq_prefixCount_add_one_of_zero_mem h0 N
  have hle := prefixCount0_vanDoornUnion_le_of_lt M hN
  omega

/-- **Universal Window Upper Bound on `normalizedPrefixRatio (vanDoornUnion M) N`**:
for any `N` in the `K`-th scale window `[vanDoornBlockStart M K, vanDoornBlockStart M (K + 1) - 1]`
with `1 ≤ vanDoornBlockStart M K`,
`normalizedPrefixRatio (vanDoornUnion M) N ≤ (2 * ∑_{j=0}^K M j + K) / √(vanDoornBlockStart M K)`. -/
theorem normalizedPrefixRatio_vanDoornUnion_le_on_window (M : ℕ → ℕ) {K N : ℕ}
    (hBpos : 1 ≤ vanDoornBlockStart M K)
    (hlo : vanDoornBlockStart M K ≤ N)
    (hhi : N < vanDoornBlockStart M (K + 1)) :
    normalizedPrefixRatio (vanDoornUnion M) N ≤
      ((2 * (∑ j ∈ Finset.range (K + 1), M j) + K : ℕ) : ℝ) /
        Real.sqrt (vanDoornBlockStart M K : ℝ) := by
  unfold normalizedPrefixRatio
  have hcnt : (prefixCount (vanDoornUnion M) N : ℝ) ≤
      ((2 * (∑ j ∈ Finset.range (K + 1), M j) + K : ℕ) : ℝ) := by
    exact_mod_cast prefixCount_vanDoornUnion_le_of_lt M hhi
  have hsqrt_pos : 0 < Real.sqrt (vanDoornBlockStart M K : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 hBpos)
  have hsqrt_le : Real.sqrt (vanDoornBlockStart M K : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt (Nat.cast_le.2 hlo)
  calc
    (prefixCount (vanDoornUnion M) N : ℝ) / Real.sqrt (N : ℝ)
        ≤ ((2 * (∑ j ∈ Finset.range (K + 1), M j) + K : ℕ) : ℝ) / Real.sqrt (N : ℝ) :=
          div_le_div_of_nonneg_right hcnt (Real.sqrt_nonneg _)
    _ ≤ ((2 * (∑ j ∈ Finset.range (K + 1), M j) + K : ℕ) : ℝ) /
          Real.sqrt (vanDoornBlockStart M K : ℝ) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hsqrt_pos hsqrt_le

/-- Every horizon `N ≥ vanDoornBlockStart M K₀` falls into a scale window
`[vanDoornBlockStart M K, vanDoornBlockStart M (K + 1))` with `K₀ ≤ K`. -/
theorem exists_vanDoornBlockStart_window_of_ge {M : ℕ → ℕ} (hM : ∀ j : ℕ, 1 ≤ M j)
    {K₀ N : ℕ} (hN : vanDoornBlockStart M K₀ ≤ N) :
    ∃ K : ℕ, K₀ ≤ K ∧ vanDoornBlockStart M K ≤ N ∧ N < vanDoornBlockStart M (K + 1) := by
  have hex : ∃ m : ℕ, N < vanDoornBlockStart M (K₀ + 1 + m) := by
    refine ⟨N, ?_⟩
    have h3 := three_mul_le_vanDoornBlockStart_of_pos hM (K₀ + 1 + N)
    omega
  let m := Nat.find hex
  have hm : N < vanDoornBlockStart M (K₀ + 1 + m) := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos m with hm0 | hmp
  · refine ⟨K₀, le_rfl, hN, ?_⟩
    simpa [hm0] using hm
  · refine ⟨K₀ + m, by omega, ?_, ?_⟩
    · have hnot : ¬ N < vanDoornBlockStart M (K₀ + 1 + (m - 1)) :=
        Nat.find_min hex (Nat.sub_lt hmp one_pos)
      have heq : K₀ + 1 + (m - 1) = K₀ + m := by omega
      rw [heq] at hnot
      omega
    · have heq : K₀ + 1 + m = K₀ + m + 1 := by omega
      simpa [heq] using hm

/-- **Reduction of Eventual `normalizedPrefixRatio` Bound to Block-Scale Ratios**:
if `1 ≤ K₀` and the block-scale ratios `(2 * ∑_{j=0}^K M j + K) / √(vanDoornBlockStart M K)`
are at most `C` for all `K ≥ K₀`, then `normalizedPrefixRatio (vanDoornUnion M) N ≤ C`
for all `N ≥ vanDoornBlockStart M K₀`. -/
theorem normalizedPrefixRatio_vanDoornUnion_eventually_le_of_block_ratio_le
    {M : ℕ → ℕ} (hM : ∀ j : ℕ, 1 ≤ M j) {K₀ : ℕ} (hK₀_pos : 1 ≤ K₀) {C : ℝ}
    (hC : ∀ K : ℕ, K₀ ≤ K →
      ((2 * (∑ j ∈ Finset.range (K + 1), M j) + K : ℕ) : ℝ) /
        Real.sqrt (vanDoornBlockStart M K : ℝ) ≤ C) :
    ∀ N : ℕ, vanDoornBlockStart M K₀ ≤ N →
      normalizedPrefixRatio (vanDoornUnion M) N ≤ C := by
  intro N hN
  rcases exists_vanDoornBlockStart_window_of_ge hM hN with ⟨K, hK₀, hlo, hhi⟩
  have hBpos : 1 ≤ vanDoornBlockStart M K :=
    one_le_vanDoornBlockStart_of_pos hM (le_trans hK₀_pos hK₀)
  exact le_trans (normalizedPrefixRatio_vanDoornUnion_le_on_window M hBpos hlo hhi) (hC K hK₀)

/-- **Universal Block-Scale Upper-Bound Bridge to `erdos_33`**:
for any positive width sequence `M : ℕ → ℕ` and `1 ≤ K₀`, if the discrete block-scale ratio
`(2 * ∑_{j=0}^K M j + K) / √(vanDoornBlockStart M K) ≤ C` holds for all `K ≥ K₀`, then the
`erdos_33` infimum is at most `C`. -/
theorem iInf_limsup_le_of_vanDoorn_block_ratio_le
    {M : ℕ → ℕ} (hM : ∀ j : ℕ, 1 ≤ M j) {K₀ : ℕ} (hK₀_pos : 1 ≤ K₀) {C : ℝ}
    (hC : ∀ K : ℕ, K₀ ≤ K →
      ((2 * (∑ j ∈ Finset.range (K + 1), M j) + K : ℕ) : ℝ) /
        Real.sqrt (vanDoornBlockStart M K : ℝ) ≤ C) :
    (⨅ B : {B : Set ℕ | AdditiveBasisCondition B}, Filter.atTop.limsup (fun N : ℕ =>
      ((B.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal))) ≤
        (C : EReal) := by
  refine iInf_le_of_le ⟨vanDoornUnion M, additiveBasisCondition_vanDoornUnion hM⟩ ?_
  refine Filter.limsup_le_of_le ?_ ?_
  · isBoundedDefault
  · rw [Filter.eventually_atTop]
    refine ⟨vanDoornBlockStart M K₀, fun N hN => ?_⟩
    rw [ereal_ncard_div_sqrt_eq_coe_normalizedPrefixRatio]
    exact EReal.coe_le_coe_iff.2
      (normalizedPrefixRatio_vanDoornUnion_eventually_le_of_block_ratio_le hM hK₀_pos hC N hN)


/-! ## Universal scale refinement and higher-resolution step sums -/

/-- At `R = 500`, `cillerueloStepSum 500 = 196830`, yielding `250000 / 196830 ≈ 1.27013 > 127 / 100`. -/
theorem cillerueloStepSum_five_hundred : cillerueloStepSum 500 = 196830 := by
  unfold cillerueloStepSum
  rw [show (500 : ℕ) = 25 * 20 by norm_num, sum_range_mul_eq_sum_range_sum_range]
  norm_num [cillerueloStepHeight, Finset.sum_range_succ]

/-- Epsilon-free subsequential lower bound `127 / 100 = 1.27 ≤ normalizedPrefixRatio A N`
for arbitrarily large `N ≥ M` (proved via `R = 500`, `S(500) = 196830`). -/
theorem exists_ge_one_hundred_twenty_seven_over_one_hundred_normalizedPrefixRatio
    {A : Set ℕ} (hA : IsSquareAdditiveComplement A) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ (127 : ℝ) / 100 ≤ normalizedPrefixRatio A N := by
  let m : ℕ := max M 20
  have hm20 : 20 ≤ m := le_max_right M 20
  have hm1 : 1 ≤ m := by omega
  have hmM : M ≤ m := le_max_left M 20
  rcases exists_step_horizon_normalizedPrefixRatio_ge hA (R := 500) (by omega) hm1 with
    ⟨r, _, hr_ge⟩
  refine ⟨(cillerueloStepHeight 500 r * m) ^ 2,
    le_trans hmM (step_horizon_ge_base 500 r m), ?_⟩
  rw [cillerueloStepSum_five_hundred] at hr_ge
  have hm_real : (20 : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hm20
  have hdiv_le : (500 : ℝ) / (m : ℝ) ≤ (500 : ℝ) / 20 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm_real
  linarith

/-- Unconditional `127 / 100 = 1.27 > 317 / 250` lower bound on the `erdos_33` infimum. -/
theorem one_hundred_twenty_seven_over_one_hundred_le_iInf_limsup :
    (((127 : ℝ) / 100 : ℝ) : EReal) ≤
      ⨅ A : {A : Set ℕ | AdditiveBasisCondition A}, Filter.atTop.limsup (fun N : ℕ =>
        ((A.1 ∩ Set.Icc 1 N).ncard : EReal) / (Real.sqrt (N : ℝ) : EReal)) := by
  refine le_iInf (fun A => ?_)
  exact coe_le_limsup_ncard_div_sqrt_of_forall_exists_ge
    (exists_ge_one_hundred_twenty_seven_over_one_hundred_normalizedPrefixRatio
      ((isSquareAdditiveComplement_iff_additiveBasisCondition A.1).2 A.2))

end Erdos33.Core

end
