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
public import Erdos902Unified435

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 200000

noncomputable section
open scoped Classical BigOperators

/-!
# Erdős Problem 902: Szekeres–Szekeres Regular and Doubly-Regular Rigidity, Tightened Binomial Bound `\binom{N}{n} ≤ (3N/n)^n`, and `2 n^2 2^n` Upper Bound

This module (`SzekeresParityRefinementAndTightenedBinomialBounds902.lean`) builds on
`Erdos902Unified435` to establish 30 universally quantified (`∀`) structural theorems and
positive/negative controls for Erdős Problem #902 (Schütte's `n`-paradoxical tournament problem)
in Lean 4.35.0-rc2:

1. **Absorptive-Set Paradoxicality and Generalized Szekeres–Szekeres Strict-Base Refinements:**
   - Every `k`-dominating subset `U ⊆ Fin N` (`DominatesAllSubsets G k U`) in a tournament on
     `Fin N` (`k ≤ N`) satisfies `k ≤ U.card`, induces a `k`-paradoxical subtournament
     (`HasParadoxicalTournament k U.card`), and obeys `legacyF k ≤ U.card`.
   - Generalized Szekeres–Szekeres recurrence `card_ge_of_dominatesAllSubsets_base` from an
     arbitrary base level `m₀ + 1` with lower bound `B ≤ W.card`, giving `(B + 1) * 2 ^ d - 1 ≤ U.card`
     at level `m₀ + d + 1`.
   - Conditional strict-base refinements (`szekeres_strict_base_refinement` and
     `szekeres_strict_two_dominating_refinement_four`) proving that a strict `+1` improvement at
     level `1` (`n + 2 ≤ W.card`) or level `2` (`12 ≤ W.card` for `n = 4`) lifts to
     `(n + 3) * 2 ^ (n - 1) - 1 ≤ N` (respectively `51 ≤ N` and `49 ≤ N` for `n = 4`).

2. **Szekeres–Szekeres Regular and Doubly-Regular Rigidity Hierarchy:**
   - Universal internal degree partition `(U.filter (G.Adj v ·)).card + (U.filter (G.Adj · v)).card = U.card - 1`
     for `v ∈ U` and internal in-degree sum `2 * ∑ v ∈ U, (U.filter (G.Adj · v)).card = U.card * (U.card - 1)`.
   - Universal Szekeres–Szekeres degree bound `inNeigh_card_ge_szekeres_of_isParadoxicalTournament`:
     in any `(n + 1)`-paradoxical tournament `G` on `Fin N` (`1 ≤ n`), every vertex `v` satisfies
     `(n + 3) * 2 ^ (n - 1) - 1 ≤ (inNeigh G v).card` and `(outNeigh G v).card + (n + 3) * 2 ^ (n - 1) ≤ N`
     (strictly sharpening Erdős's `2 ^ (n + 1) - 1` degree bound for all `n ≥ 2`).
   - Extremal odd-order regularity (`internal_regular_of_dominatesAllSubsets_szekeres_extremal` and
     `regular_of_isParadoxicalTournament_szekeres_extremal`): at `N = (n + 2) * 2 ^ (n - 1) - 1`
     (`2 ≤ n`), `G` is regular of exact in-degree and out-degree `(n + 2) * 2 ^ (n - 2) - 1`
     (`23`-regular at `n = 4, N = 47`).
   - Doubly-regular pair rigidity (`doubly_regular_inNeigh_inter_of_szekeres_extremal`, `3 ≤ n`)
     and transitive-triple rigidity (`transitive_triple_inNeigh_inter_of_szekeres_extremal`, `4 ≤ n`)
     at `N = (n + 2) * 2 ^ (n - 1) - 1`.

3. **Tightened Binomial Upper Bound `N.choose n ≤ ((3 * N) / n) ^ n` and Reduced `O(n^2 2^n)` Leading Coefficients:**
   - Symmetric descending-factorial pairing `3 ^ n * N.descFactorial n ≤ (n * ((3 * N) / n)) ^ n`
     (`1 ≤ n ≤ N`), the binomial-sum inequality `(n + 1) ^ n < 3 * n ^ n` (`1 ≤ n`), the factorial
     bound `n ^ n ≤ 3 ^ n * n.factorial`, and the universal tightened binomial bound
     `N.choose n ≤ ((3 * N) / n) ^ n` for all `N, n : ℕ`.
   - Unconditional proof that `TightenedErdosUpperBoundFormula n = n + 2 * n ^ 2 * 2 ^ n` and
     `SharpErdosUpperBoundFormula n = n + n * (2 * n - 1) * 2 ^ n` reduce the explicit upper bound
     on `legacyF n` from `5 * n ^ 2 * 2 ^ n` to `legacyF n ≤ n + 2 * n ^ 2 * 2 ^ n ≤ 3 * n ^ 2 * 2 ^ n` and
     `legacyF n ≤ 2 * n ^ 2 * 2 ^ n` for every `1 ≤ n`.
-/

namespace Erdos902

/-- Every `k`-dominating subset `U ⊆ Fin N` (`DominatesAllSubsets G k U`) in a tournament `G` on
`Fin N` (`k ≤ N`) satisfies `k ≤ U.card`, induces a `k`-paradoxical subtournament
(`HasParadoxicalTournament k U.card`), and obeys `legacyF k ≤ U.card`. -/
theorem hasParadoxicalTournament_of_dominatesAllSubsets {k N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (hk : k ≤ N) {U : Finset (Fin N)} (hU : DominatesAllSubsets G k U) :
    k ≤ U.card ∧ HasParadoxicalTournament k U.card ∧ legacyF k ≤ U.card := by
  have hkU : k ≤ U.card := by
    by_contra hlt
    have hdiff : k - U.card ≤ (Finset.univ \ U).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hdiff
    have hdisj : Disjoint U R :=
      Finset.disjoint_left.mpr (fun x hxU hxR => (Finset.mem_sdiff.mp (hRsub hxR)).2 hxU)
    have hcard_union : (U ∪ R).card = k := by
      rw [Finset.card_union_of_disjoint hdisj, hRcard]
      omega
    obtain ⟨w, hwU, hwdom⟩ := hU (U ∪ R) hcard_union
    exact hG.1 w (hwdom w (Finset.mem_union_left R hwU))
  let M := U.card
  let g : Fin M ↪ Fin N := embOfCardLe (le_refl M)
  have hmap_sub : (Finset.univ : Finset (Fin M)).map g ⊆ U := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
    exact embOfCardLe_mem (le_refl M) i
  have hmap_eq : (Finset.univ : Finset (Fin M)).map g = U :=
    Finset.eq_of_subset_of_card_le hmap_sub (by simp [M])
  have hpar : IsParadoxicalTournament k (comapDigraph G g) := by
    refine ⟨isTournament_comap hG g, by simp [M, hkU], ?_⟩
    intro S hScard
    have hcard_map : (S.map g).card = k := by rw [Finset.card_map, hScard]
    obtain ⟨w, hwU, hwdom⟩ := hU (S.map g) hcard_map
    rw [← hmap_eq] at hwU
    rcases Finset.mem_map.mp hwU with ⟨i, _, rfl⟩
    refine ⟨i, fun j hj => ?_⟩
    exact hwdom (g j) (Finset.mem_map_of_mem g hj)
  have hex : HasParadoxicalTournament k U.card := ⟨comapDigraph G g, hpar⟩
  exact ⟨hkU, hex, legacyF_le_of_hasParadoxicalTournament hex⟩

/-- Generalized Szekeres–Szekeres (1965) inductive lower bound starting from an arbitrary base
level `m₀ + 1`: if every `(m₀ + 1)`-dominating subset `W` in a tournament `G` on `Fin N` has
`B ≤ W.card`, then every `(m₀ + d + 1)`-dominating subset `U` (`m₀ + d + 1 ≤ N`) satisfies
`(B + 1) * 2 ^ d - 1 ≤ U.card`. -/
theorem card_ge_of_dominatesAllSubsets_base {N B m₀ : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G)
    (hbase : ∀ W : Finset (Fin N), DominatesAllSubsets G (m₀ + 1) W → B ≤ W.card) :
    ∀ d : ℕ, m₀ + d + 1 ≤ N → ∀ U : Finset (Fin N),
      DominatesAllSubsets G (m₀ + d + 1) U → (B + 1) * 2 ^ d - 1 ≤ U.card
  | 0, _, U, hU => by
    have h1 := hbase U hU
    simp only [pow_zero, mul_one]
    omega
  | d + 1, hdN, U, hU => by
    have hcard_univ : m₀ + (d + 1) + 1 ≤ (Finset.univ : Finset (Fin N)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      exact hdN
    obtain ⟨S₀, _, hS₀card⟩ := Finset.exists_subset_card_eq hcard_univ
    obtain ⟨w₀, hw₀U, _⟩ := hU S₀ hS₀card
    obtain ⟨v, _, hv_deg⟩ := exists_vertex_in_subset_inDegree_le hG ⟨w₀, hw₀U⟩
    have heq : m₀ + (d + 1) + 1 = (m₀ + d + 1) + 1 := by omega
    rw [heq] at hU hdN
    have hstep : DominatesAllSubsets G (m₀ + d + 1) (U.filter (fun w => G.Adj w v)) :=
      dominatesAllSubsets_filter_of_succ hdN hU v
    have ih := card_ge_of_dominatesAllSubsets_base hG hbase d (by omega)
      (U.filter (fun w => G.Adj w v)) hstep
    have hpow : (B + 1) * 2 ^ (d + 1) = 2 * ((B + 1) * 2 ^ d) := by ring
    have hpos : 1 ≤ (B + 1) * 2 ^ d :=
      Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (by positivity))
    omega

/-- Conditional strict-base Szekeres–Szekeres refinement: if every `1`-dominating subset `W` in an
`n`-paradoxical tournament `G` on `Fin N` (`1 ≤ n`) satisfies `n + 2 ≤ W.card`, then
`(n + 3) * 2 ^ (n - 1) - 1 ≤ N` (in particular `55 ≤ N` and `49 ≤ N` at `n = 4`). -/
theorem szekeres_strict_base_refinement {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) (hn : 1 ≤ n)
    (hstrict : ∀ W : Finset (Fin N), DominatesAllSubsets G 1 W → n + 2 ≤ W.card) :
    (n + 3) * 2 ^ (n - 1) - 1 ≤ N := by
  have hnN : n ≤ N := by simpa using hG.2.1
  have huniv : DominatesAllSubsets G (0 + (n - 1) + 1) Finset.univ := by
    have heq : 0 + (n - 1) + 1 = n := by omega
    rw [heq]
    intro S hScard
    obtain ⟨w, hw⟩ := hG.2.2 S hScard
    exact ⟨w, Finset.mem_univ w, hw⟩
  have hbound := card_ge_of_dominatesAllSubsets_base hG.1 hstrict (n - 1) (by omega) Finset.univ huniv
  simpa using hbound

/-- Conditional `2`-dominating refinement for `n = 4`: if every `2`-dominating subset `W` in a
`4`-paradoxical tournament `G` on `Fin N` has `12 ≤ W.card` (strictly exceeding the Szekeres–Szekeres
value `11`), then `51 ≤ N` and `49 ≤ N`. -/
theorem szekeres_strict_two_dominating_refinement_four {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament 4 G)
    (hstrict2 : ∀ W : Finset (Fin N), DominatesAllSubsets G 2 W → 12 ≤ W.card) :
    51 ≤ N ∧ 49 ≤ N := by
  have h4N : 4 ≤ N := by simpa using hG.2.1
  have huniv : DominatesAllSubsets G (1 + 2 + 1) Finset.univ := by
    intro S hScard
    obtain ⟨w, hw⟩ := hG.2.2 S hScard
    exact ⟨w, Finset.mem_univ w, hw⟩
  have hbound := card_ge_of_dominatesAllSubsets_base hG.1 hstrict2 2 (by omega) Finset.univ huniv
  simp only [Finset.card_univ, Fintype.card_fin] at hbound
  omega

/-- Universal Finset averaging rigidity lemma: if `B ≤ g x` for all `x ∈ s` and
`∑ x ∈ s, g x ≤ s.card * B`, then `g x = B` for every `x ∈ s`. -/
theorem eq_of_sum_le_card_mul_of_forall_ge {α : Type*} (s : Finset α) (g : α → ℕ) (B : ℕ)
    (hge : ∀ x ∈ s, B ≤ g x) (hsum : ∑ x ∈ s, g x ≤ s.card * B) :
    ∀ x ∈ s, g x = B := by
  intro x hx
  by_contra hne
  have hgt : B < g x := lt_of_le_of_ne (hge x hx) (Ne.symm hne)
  have hlt_sum : ∑ y ∈ s, B < ∑ y ∈ s, g y :=
    Finset.sum_lt_sum (fun y hy => hge y hy) ⟨x, hx, hgt⟩
  rw [Finset.sum_const, smul_eq_mul] at hlt_sum
  omega

/-- For any vertex `v ∈ U` in a subset `U` of a tournament `G`, its internal out-degree and
internal in-degree inside `U` sum to `U.card - 1`. -/
theorem card_filter_adj_out_add_in_of_mem {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) {U : Finset (Fin N)} {v : Fin N} (hv : v ∈ U) :
    (U.filter (fun w => G.Adj v w)).card + (U.filter (fun w => G.Adj w v)).card = U.card - 1 := by
  have hdisj : Disjoint (U.filter (fun w => G.Adj v w)) (U.filter (fun w => G.Adj w v)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [Finset.mem_filter] at hw1 hw2
    have hne : v ≠ w := fun h => hG.1 v (h ▸ hw1.2)
    exact (hG.2 v w hne).mp hw1.2 hw2.2
  have hunion : U.filter (fun w => G.Adj v w) ∪ U.filter (fun w => G.Adj w v) = U.erase v := by
    ext w
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with ⟨hwU, h1⟩ | ⟨hwU, h2⟩
      · exact ⟨fun heq => hG.1 v (heq ▸ h1), hwU⟩
      · exact ⟨fun heq => hG.1 v (heq ▸ h2), hwU⟩
    · by_cases hadj : G.Adj v w
      · exact Or.inl ⟨h.2, hadj⟩
      · right
        have hne : v ≠ w := Ne.symm h.1
        refine ⟨h.2, ?_⟩
        by_contra hnot
        exact hadj ((hG.2 v w hne).mpr hnot)
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem hv]

/-- In any subset `U` of a tournament `G` on `Fin N`, twice the sum of internal in-degrees equals
`U.card * (U.card - 1)`. -/
theorem two_mul_sum_card_filter_adj_in {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (U : Finset (Fin N)) :
    2 * (∑ v ∈ U, (U.filter (fun w => G.Adj w v)).card) = U.card * (U.card - 1) := by
  have hsum : ∑ v ∈ U, ((U.filter (fun w => G.Adj v w)).card + (U.filter (fun w => G.Adj w v)).card) =
      ∑ _v ∈ U, (U.card - 1) :=
    Finset.sum_congr rfl (fun v hv => card_filter_adj_out_add_in_of_mem hG hv)
  have hcomm : (∑ v ∈ U, (U.filter (fun w => G.Adj v w)).card) =
      ∑ v ∈ U, (U.filter (fun w => G.Adj w v)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [Finset.sum_add_distrib, hcomm, Finset.sum_const, smul_eq_mul] at hsum
  omega

/-- Pointwise Szekeres–Szekeres in-degree lower bound inside any `(m + 2)`-dominating subset `U`:
for every vertex `v : Fin N` (whether in `U` or outside `U`), `U.filter (fun w => G.Adj w v)` is
`(m + 1)`-dominating and has cardinality at least `(n + 2) * 2 ^ m - 1`. -/
theorem card_filter_adj_ge_szekeres_of_dominatesAllSubsets {n m N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) (hm : m + 2 ≤ n) {U : Finset (Fin N)}
    (hU : DominatesAllSubsets G (m + 2) U) (v : Fin N) :
    DominatesAllSubsets G (m + 1) (U.filter (fun w => G.Adj w v)) ∧
      (n + 2) * 2 ^ m - 1 ≤ (U.filter (fun w => G.Adj w v)).card := by
  have hnN : n ≤ N := by simpa using hG.2.1
  have hdom : DominatesAllSubsets G (m + 1) (U.filter (fun w => G.Adj w v)) :=
    dominatesAllSubsets_filter_of_succ (by omega) hU v
  have hcard : (n + 2) * 2 ^ m - 1 ≤ (U.filter (fun w => G.Adj w v)).card :=
    card_ge_szekeres_of_dominatesAllSubsets hG m (by omega) (U.filter (fun w => G.Adj w v)) hdom
  exact ⟨hdom, hcard⟩

/-- Szekeres–Szekeres (1965) vertex degree bound in any `(n + 1)`-paradoxical tournament `G` on
`Fin N` (`1 ≤ n`): every vertex `v` has `(n + 3) * 2 ^ (n - 1) - 1 ≤ (inNeigh G v).card` and
`(outNeigh G v).card + (n + 3) * 2 ^ (n - 1) ≤ N`. -/
theorem inNeigh_card_ge_szekeres_of_isParadoxicalTournament {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament (n + 1) G) (hn : 1 ≤ n) (v : Fin N) :
    DominatesAllSubsets G n (inNeigh G v) ∧
      (n + 3) * 2 ^ (n - 1) - 1 ≤ (inNeigh G v).card ∧
      (outNeigh G v).card + (n + 3) * 2 ^ (n - 1) ≤ N := by
  have huniv : DominatesAllSubsets G ((n - 1) + 2) Finset.univ := by
    have heq : (n - 1) + 2 = n + 1 := by omega
    rw [heq]
    intro S hScard
    obtain ⟨w, hw⟩ := hG.2.2 S hScard
    exact ⟨w, Finset.mem_univ w, hw⟩
  have hstep := card_filter_adj_ge_szekeres_of_dominatesAllSubsets hG (by omega : (n - 1) + 2 ≤ n + 1) huniv v
  have hin_eq : (Finset.univ : Finset (Fin N)).filter (fun w => G.Adj w v) = inNeigh G v := rfl
  have heq1 : n - 1 + 1 = n := by omega
  have heq2 : n + 1 + 2 = n + 3 := by omega
  rw [hin_eq, heq1, heq2] at hstep
  have hsum := card_outNeigh_add_card_inNeigh hG.1 v
  have hgt := card_gt_of_isParadoxicalTournament hG
  have hpos : 1 ≤ (n + 3) * 2 ^ (n - 1) :=
    Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (by positivity))
  exact ⟨hstep.1, hstep.2, by omega⟩

/-- Internal regularity of any `(m + 2)`-dominating subset `U` achieving the extremal
Szekeres–Szekeres size `U.card = (n + 2) * 2 ^ (m + 1) - 1`: every `v ∈ U` has exact internal
in-degree and internal out-degree `(n + 2) * 2 ^ m - 1`. -/
theorem internal_regular_of_dominatesAllSubsets_szekeres_extremal {n m N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) (hm : m + 2 ≤ n) {U : Finset (Fin N)}
    (hU : DominatesAllSubsets G (m + 2) U) (hUcard : U.card = (n + 2) * 2 ^ (m + 1) - 1) :
    ∀ v ∈ U,
      (U.filter (fun w => G.Adj w v)).card = (n + 2) * 2 ^ m - 1 ∧
      (U.filter (fun w => G.Adj v w)).card = (n + 2) * 2 ^ m - 1 := by
  let B := (n + 2) * 2 ^ m - 1
  have hpos : 1 ≤ (n + 2) * 2 ^ m :=
    Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (by positivity))
  have hpow : (n + 2) * 2 ^ (m + 1) = 2 * ((n + 2) * 2 ^ m) := by ring
  have hU_eq : U.card = 2 * B + 1 := by omega
  have hge : ∀ v ∈ U, B ≤ (U.filter (fun w => G.Adj w v)).card := fun v _ =>
    (card_filter_adj_ge_szekeres_of_dominatesAllSubsets hG hm hU v).2
  have h2sum := two_mul_sum_card_filter_adj_in hG.1 U
  have hsum_le : ∑ v ∈ U, (U.filter (fun w => G.Adj w v)).card ≤ U.card * B := by
    rw [hU_eq] at h2sum ⊢
    have hsub : 2 * B + 1 - 1 = 2 * B := by omega
    rw [hsub] at h2sum
    nlinarith
  have hall_in := eq_of_sum_le_card_mul_of_forall_ge U (fun v => (U.filter (fun w => G.Adj w v)).card) B hge hsum_le
  intro v hv
  have hin := hall_in v hv
  have hadd := card_filter_adj_out_add_in_of_mem hG.1 hv
  exact ⟨hin, by omega⟩

/-- Extremal Szekeres–Szekeres regularity theorem: any `n`-paradoxical tournament `G` (`2 ≤ n`) on
`N = (n + 2) * 2 ^ (n - 1) - 1` vertices is regular of exact in-degree and out-degree
`(n + 2) * 2 ^ (n - 2) - 1` (in particular, `23`-regular at `n = 4, N = 47`). -/
theorem regular_of_isParadoxicalTournament_szekeres_extremal {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) (hn : 2 ≤ n) (hN : N = (n + 2) * 2 ^ (n - 1) - 1)
    (v : Fin N) :
    (inNeigh G v).card = (n + 2) * 2 ^ (n - 2) - 1 ∧
      (outNeigh G v).card = (n + 2) * 2 ^ (n - 2) - 1 := by
  have huniv : DominatesAllSubsets G ((n - 2) + 2) Finset.univ := by
    have heq : (n - 2) + 2 = n := by omega
    rw [heq]
    intro S hScard
    obtain ⟨w, hw⟩ := hG.2.2 S hScard
    exact ⟨w, Finset.mem_univ w, hw⟩
  have hcard : (Finset.univ : Finset (Fin N)).card = (n + 2) * 2 ^ ((n - 2) + 1) - 1 := by
    simp only [Finset.card_univ, Fintype.card_fin]
    have heq : (n - 2) + 1 = n - 1 := by omega
    rw [heq, hN]
  exact internal_regular_of_dominatesAllSubsets_szekeres_extremal hG (by omega) huniv hcard v (Finset.mem_univ v)

/-- Doubly-regular common-dominator rigidity at the Szekeres–Szekeres extremal order
`N = (n + 2) * 2 ^ (n - 1) - 1` (`3 ≤ n`): for every vertex `v` and every `u ∈ inNeigh G v`, the
common in-neighborhood `inNeigh G v ∩ inNeigh G u` is `(n - 2)`-dominating and has exact
cardinality `(n + 2) * 2 ^ (n - 3) - 1` (`11` at `n = 4, N = 47`). -/
theorem doubly_regular_inNeigh_inter_of_szekeres_extremal {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) (hn : 3 ≤ n) (hN : N = (n + 2) * 2 ^ (n - 1) - 1)
    (v : Fin N) {u : Fin N} (hu : u ∈ inNeigh G v) :
    DominatesAllSubsets G (n - 2) (inNeigh G v ∩ inNeigh G u) ∧
      (inNeigh G v ∩ inNeigh G u).card = (n + 2) * 2 ^ (n - 3) - 1 := by
  have huniv : DominatesAllSubsets G ((n - 2) + 2) Finset.univ := by
    have heq : (n - 2) + 2 = n := by omega
    rw [heq]
    intro S hScard
    obtain ⟨w, hw⟩ := hG.2.2 S hScard
    exact ⟨w, Finset.mem_univ w, hw⟩
  have hstep_v := card_filter_adj_ge_szekeres_of_dominatesAllSubsets hG (by omega : (n - 2) + 2 ≤ n) huniv v
  have hin_v : (Finset.univ : Finset (Fin N)).filter (fun w => G.Adj w v) = inNeigh G v := rfl
  rw [hin_v] at hstep_v
  have hdom_v : DominatesAllSubsets G ((n - 3) + 2) (inNeigh G v) := by
    have heq : (n - 3) + 2 = (n - 2) + 1 := by omega
    rw [heq]
    exact hstep_v.1
  have hcard_v : (inNeigh G v).card = (n + 2) * 2 ^ ((n - 3) + 1) - 1 := by
    have heq : (n - 3) + 1 = n - 2 := by omega
    rw [heq]
    exact (regular_of_isParadoxicalTournament_szekeres_extremal hG (by omega) hN v).1
  have hreg_v := internal_regular_of_dominatesAllSubsets_szekeres_extremal hG (by omega : (n - 3) + 2 ≤ n) hdom_v hcard_v u hu
  have hstep_u := card_filter_adj_ge_szekeres_of_dominatesAllSubsets hG (by omega : (n - 3) + 2 ≤ n) hdom_v u
  have hinter : (inNeigh G v).filter (fun w => G.Adj w u) = inNeigh G v ∩ inNeigh G u := by
    ext w
    rw [Finset.mem_filter, Finset.mem_inter, mem_inNeigh_iff, mem_inNeigh_iff]
  rw [hinter] at hreg_v hstep_u
  have heq : (n - 3) + 1 = n - 2 := by omega
  rw [heq] at hstep_u
  exact ⟨hstep_u.1, hreg_v.1⟩

/-- Transitive-triple common-dominator rigidity at the Szekeres–Szekeres extremal order
`N = (n + 2) * 2 ^ (n - 1) - 1` (`4 ≤ n`): for every `v`, `u ∈ inNeigh G v`, and
`z ∈ inNeigh G v ∩ inNeigh G u`, the common in-neighborhood `inNeigh G v ∩ inNeigh G u ∩ inNeigh G z`
is `(n - 3)`-dominating and has exact cardinality `(n + 2) * 2 ^ (n - 4) - 1` (`5` at `n = 4, N = 47`). -/
theorem transitive_triple_inNeigh_inter_of_szekeres_extremal {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) (hn : 4 ≤ n) (hN : N = (n + 2) * 2 ^ (n - 1) - 1)
    (v : Fin N) {u z : Fin N} (hu : u ∈ inNeigh G v) (hz : z ∈ inNeigh G v ∩ inNeigh G u) :
    DominatesAllSubsets G (n - 3) (inNeigh G v ∩ inNeigh G u ∩ inNeigh G z) ∧
      (inNeigh G v ∩ inNeigh G u ∩ inNeigh G z).card = (n + 2) * 2 ^ (n - 4) - 1 := by
  have hpair := doubly_regular_inNeigh_inter_of_szekeres_extremal hG (by omega) hN v hu
  have hdom_uv : DominatesAllSubsets G ((n - 4) + 2) (inNeigh G v ∩ inNeigh G u) := by
    have heq : (n - 4) + 2 = n - 2 := by omega
    rw [heq]
    exact hpair.1
  have hcard_uv : (inNeigh G v ∩ inNeigh G u).card = (n + 2) * 2 ^ ((n - 4) + 1) - 1 := by
    have heq : (n - 4) + 1 = n - 3 := by omega
    rw [heq]
    exact hpair.2
  have hreg_uv := internal_regular_of_dominatesAllSubsets_szekeres_extremal hG (by omega : (n - 4) + 2 ≤ n) hdom_uv hcard_uv z hz
  have hstep_z := card_filter_adj_ge_szekeres_of_dominatesAllSubsets hG (by omega : (n - 4) + 2 ≤ n) hdom_uv z
  have hinter : (inNeigh G v ∩ inNeigh G u).filter (fun w => G.Adj w z) =
      inNeigh G v ∩ inNeigh G u ∩ inNeigh G z := by
    ext w
    simp [Finset.mem_filter, Finset.mem_inter, mem_inNeigh_iff, and_assoc]
  rw [hinter] at hreg_uv hstep_z
  have heq : (n - 4) + 1 = n - 3 := by omega
  rw [heq] at hstep_z
  exact ⟨hstep_z.1, hreg_uv.1⟩




/-- Elementary AM-GM square bound on `ℕ`: if `a + b ≤ 2 * M`, then `a * b ≤ M ^ 2`. -/
theorem mul_le_sq_of_add_le_two_mul {a b M : ℕ} (h : a + b ≤ 2 * M) :
    a * b ≤ M ^ 2 := by
  have hz : (a : ℤ) + b ≤ 2 * M := by exact_mod_cast h
  have hsq1 : 0 ≤ ((a : ℤ) - b) ^ 2 := sq_nonneg _
  have hsq2 : 0 ≤ (2 * (M : ℤ)) ^ 2 - ((a : ℤ) + b) ^ 2 := by
    have hpos : 0 ≤ (a : ℤ) + b := by positivity
    nlinarith
  have hab : (a : ℤ) * b ≤ M ^ 2 := by nlinarith
  exact_mod_cast hab

/-- Product representation of the descending factorial `N.descFactorial n = ∏ k ∈ range n, (N - k)`. -/
theorem descFactorial_eq_prod_range (N n : ℕ) :
    N.descFactorial n = ∏ k ∈ Finset.range n, (N - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, ih, mul_comm]

/-- Symmetric descending-factorial pairing bound: for all `1 ≤ n ≤ N`,
`3 ^ n * N.descFactorial n ≤ (n * ((3 * N) / n)) ^ n`. -/
theorem three_pow_mul_descFactorial_le {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    3 ^ n * N.descFactorial n ≤ (n * ((3 * N) / n)) ^ n := by
  let M := n * ((3 * N) / n)
  have hdiv : n * ((3 * N) / n) + (3 * N) % n = 3 * N := Nat.div_add_mod (3 * N) n
  have hmod : (3 * N) % n < n := Nat.mod_lt (3 * N) (by omega)
  have h3N : 3 * N ≤ M + n - 1 := by omega
  have hprod1 : 3 ^ n * N.descFactorial n = ∏ k ∈ Finset.range n, (3 * (N - k)) := by
    rw [descFactorial_eq_prod_range, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hprod2 : 3 ^ n * N.descFactorial n = ∏ k ∈ Finset.range n, (3 * (N - (n - 1 - k))) := by
    rw [hprod1, ← Finset.prod_range_reflect]
  have hsq : (3 ^ n * N.descFactorial n) ^ 2 ≤ (M ^ n) ^ 2 := by
    calc
      (3 ^ n * N.descFactorial n) ^ 2
          = (3 ^ n * N.descFactorial n) * (3 ^ n * N.descFactorial n) := sq _
      _ = (∏ k ∈ Finset.range n, (3 * (N - k))) *
            (∏ k ∈ Finset.range n, (3 * (N - (n - 1 - k)))) := by
           nth_rw 1 [hprod1]
           nth_rw 1 [hprod2]
      _ = ∏ k ∈ Finset.range n, ((3 * (N - k)) * (3 * (N - (n - 1 - k)))) := by
          rw [← Finset.prod_mul_distrib]
      _ ≤ ∏ _k ∈ Finset.range n, (M ^ 2) := by
          refine Finset.prod_le_prod' (fun k hk => ?_)
          have hk_lt : k < n := Finset.mem_range.mp hk
          have hsum : 3 * (N - k) + 3 * (N - (n - 1 - k)) ≤ 2 * M := by omega
          exact mul_le_sq_of_add_le_two_mul hsum
      _ = (M ^ n) ^ 2 := by
          rw [Finset.prod_const, Finset.card_range, ← pow_mul, ← pow_mul, mul_comm 2 n]
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq

/-- Elementary power-of-two factorial lower bound `2 ^ (k - 1) ≤ k.factorial` for all `k : ℕ`. -/
theorem two_pow_pred_le_factorial : ∀ k : ℕ, 2 ^ (k - 1) ≤ k.factorial
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
    have ih := two_pow_pred_le_factorial (k + 1)
    change 2 ^ k ≤ (k + 1).factorial at ih
    change 2 ^ (k + 1) ≤ (k + 2).factorial
    rw [pow_succ', Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) ih

/-- Binary geometric sum identity `(∑ i ∈ range n, 2 ^ i) + 1 = 2 ^ n`. -/
theorem sum_two_pow_range (n : ℕ) : (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ']
    omega

/-- Reflected binary geometric sum identity `(∑ i ∈ range n, 2 ^ (n - 1 - i)) + 1 = 2 ^ n`. -/
theorem sum_two_pow_sub_one_sub (n : ℕ) :
    (∑ i ∈ Finset.range n, 2 ^ (n - 1 - i)) + 1 = 2 ^ n := by
  rw [Finset.sum_range_reflect]
  exact sum_two_pow_range n

/-- Termwise binomial bound `2 ^ (n - 1) * (n.choose k * n ^ (n - k)) ≤ 2 ^ (n - k) * n ^ n` for
`1 ≤ k ≤ n`. -/
theorem two_pow_pred_mul_choose_mul_pow_le {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    2 ^ (n - 1) * (n.choose k * n ^ (n - k)) ≤ 2 ^ (n - k) * n ^ n := by
  have hfact : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have h2k : 2 ^ (k - 1) ≤ k.factorial := two_pow_pred_le_factorial k
  have hstep1 : 2 ^ (k - 1) * n.choose k ≤ n ^ k :=
    le_trans (Nat.mul_le_mul_right _ h2k) hfact
  have hstep2 : (2 ^ (k - 1) * n.choose k) * n ^ (n - k) ≤ n ^ k * n ^ (n - k) :=
    Nat.mul_le_mul_right _ hstep1
  rw [← pow_add, Nat.add_sub_of_le hkn] at hstep2
  have hstep3 : 2 ^ (n - k) * ((2 ^ (k - 1) * n.choose k) * n ^ (n - k)) ≤ 2 ^ (n - k) * n ^ n :=
    Nat.mul_le_mul_left _ hstep2
  have hexp : (n - k) + (k - 1) = n - 1 := by omega
  calc
    2 ^ (n - 1) * (n.choose k * n ^ (n - k))
        = (2 ^ (n - k) * 2 ^ (k - 1)) * (n.choose k * n ^ (n - k)) := by
          rw [← pow_add, hexp]
    _ = 2 ^ (n - k) * ((2 ^ (k - 1) * n.choose k) * n ^ (n - k)) := by ring
    _ ≤ 2 ^ (n - k) * n ^ n := hstep3

/-- Exact natural-number Euler-base upper bound: for all `1 ≤ n`, `(n + 1) ^ n < 3 * n ^ n`. -/
theorem add_one_pow_lt_three_mul_pow (n : ℕ) (hn : 1 ≤ n) :
    (n + 1) ^ n < 3 * n ^ n := by
  have hexp : (1 + n) ^ n = ∑ k ∈ Finset.range (n + 1), n.choose k * n ^ (n - k) := by
    rw [add_pow]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [one_pow, one_mul, Nat.cast_id]
    ring
  rw [add_comm n 1, hexp, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.sub_zero, one_mul]
  have hmul : 2 ^ (n - 1) * (∑ k ∈ Finset.range n, n.choose (k + 1) * n ^ (n - (k + 1))) ≤
      (∑ k ∈ Finset.range n, 2 ^ (n - 1 - k)) * n ^ n := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hk_lt : k < n := Finset.mem_range.mp hk
    have hterm := two_pow_pred_mul_choose_mul_pow_le (by omega : 1 ≤ k + 1) (by omega : k + 1 ≤ n)
    have hsub : n - (k + 1) = n - 1 - k := by omega
    nth_rw 2 [hsub] at hterm
    exact hterm
  have hsum_pow : (∑ k ∈ Finset.range n, 2 ^ (n - 1 - k)) + 1 = 2 ^ n :=
    sum_two_pow_sub_one_sub n
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left]
    ring
  have hpos : 0 < n ^ n := Nat.pos_of_ne_zero (by positivity)
  have hlt_scaled : 2 ^ (n - 1) * ((∑ k ∈ Finset.range n, n.choose (k + 1) * n ^ (n - (k + 1))) + n ^ n) <
      2 ^ (n - 1) * (3 * n ^ n) := by
    nlinarith
  exact lt_of_mul_lt_mul_left hlt_scaled (Nat.zero_le _)

/-- Universal Stirling-type factorial lower bound: `n ^ n ≤ 3 ^ n * n.factorial` for all `n : ℕ`. -/
theorem self_pow_le_three_pow_mul_factorial : ∀ n : ℕ, n ^ n ≤ 3 ^ n * n.factorial
  | 0 => by decide
  | n + 1 => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · decide
    · have ih := self_pow_le_three_pow_mul_factorial n
      have hlt := le_of_lt (add_one_pow_lt_three_mul_pow n hn)
      calc
        (n + 1) ^ (n + 1) = (n + 1) * (n + 1) ^ n := by ring
        _ ≤ (n + 1) * (3 * n ^ n) := Nat.mul_le_mul_left (n + 1) hlt
        _ = 3 * (n + 1) * n ^ n := by ring
        _ ≤ 3 * (n + 1) * (3 ^ n * n.factorial) := Nat.mul_le_mul_left _ ih
        _ = 3 ^ (n + 1) * (n + 1).factorial := by
          rw [pow_succ', Nat.factorial_succ]
          ring

/-- Universal tightened binomial upper bound: `N.choose n ≤ ((3 * N) / n) ^ n` for all `N, n : ℕ`. -/
theorem choose_le_three_mul_div_pow (N n : ℕ) :
    N.choose n ≤ ((3 * N) / n) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · by_cases hnN : n ≤ N
    · have h1 := self_pow_le_three_pow_mul_factorial n
      have h2 := three_pow_mul_descFactorial_le hn hnN
      have hscaled : n ^ n * N.choose n ≤ n ^ n * ((3 * N) / n) ^ n := by
        calc
          n ^ n * N.choose n ≤ (3 ^ n * n.factorial) * N.choose n :=
            Nat.mul_le_mul_right _ h1
          _ = 3 ^ n * (n.factorial * N.choose n) := by ring
          _ = 3 ^ n * N.descFactorial n := by rw [Nat.descFactorial_eq_factorial_mul_choose]
          _ ≤ (n * ((3 * N) / n)) ^ n := h2
          _ = n ^ n * ((3 * N) / n) ^ n := mul_pow n ((3 * N) / n) n
      have hpos : 0 < n ^ n := Nat.pos_of_ne_zero (by positivity)
      exact Nat.le_of_mul_le_mul_left hscaled hpos
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.zero_le _


/-- General union-bound bridge from `(n + t * 2 ^ n).choose n ≤ 2 ^ t` to
`ErdosProbabilisticCriterion n (n + t * 2 ^ n)` for all `1 ≤ n` and `1 ≤ t`. -/
theorem erdosProbabilisticCriterion_of_choose_le {n t : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t)
    (hchoose : (n + t * 2 ^ n).choose n ≤ 2 ^ t) :
    ErdosProbabilisticCriterion n (n + t * 2 ^ n) := by
  dsimp [ErdosProbabilisticCriterion]
  rw [Nat.add_sub_cancel_left]
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hchoose) (two_pow_mul_sub_one_pow_lt n t hn ht)

/-- Tightened explicit `O(n^2 2^n)` vertex formula `N_tight(n) = n + 2 n^2 2^n`. -/
def TightenedErdosUpperBoundFormula (n : ℕ) : ℕ :=
  n + 2 * n ^ 2 * 2 ^ n

/-- Sharp explicit `O(n^2 2^n)` vertex formula `N_sharp(n) = n + n (2n - 1) 2^n ≤ 2 n^2 2^n`. -/
def SharpErdosUpperBoundFormula (n : ℕ) : ℕ :=
  n + n * (2 * n - 1) * 2 ^ n

/-- For all `5 ≤ n`, `3 + 6 * n * 2 ^ n ≤ 2 ^ (2 * n)`. -/
theorem three_add_six_mul_two_pow_le_four_pow {n : ℕ} (hn : 5 ≤ n) :
    3 + 6 * n * 2 ^ n ≤ 2 ^ (2 * n) := by
  have haux : ∀ m : ℕ, 6 * (m + 5) + 1 ≤ 2 ^ (m + 5) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      have hpow : 2 ^ (m + 1 + 5) = 2 * 2 ^ (m + 5) := by ring
      omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hm := haux m
  have hcomm : 5 + m = m + 5 := by omega
  rw [hcomm]
  have hpow2 : 2 ^ (2 * (m + 5)) = 2 ^ (m + 5) * 2 ^ (m + 5) := by ring
  have hge3 : 3 ≤ 2 ^ (m + 5) := by
    have : 32 ≤ 2 ^ (m + 5) := by
      calc 32 = 2 ^ 5 := by decide
      _ ≤ 2 ^ (m + 5) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [hpow2]
  nlinarith

/-- Via `choose_le_three_mul_div_pow`, `TightenedErdosUpperBoundFormula n = n + 2 * n ^ 2 * 2 ^ n`
satisfies `ErdosProbabilisticCriterion n (TightenedErdosUpperBoundFormula n)` and
`TightenedErdosUpperBoundFormula n ≤ 3 * n ^ 2 * 2 ^ n` for all `5 ≤ n`. -/
theorem tightenedErdosUpperBoundFormula_criterion_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    ErdosProbabilisticCriterion n (TightenedErdosUpperBoundFormula n) ∧
      TightenedErdosUpperBoundFormula n ≤ 3 * n ^ 2 * 2 ^ n := by
  let N := TightenedErdosUpperBoundFormula n
  let t := 2 * n ^ 2
  have hn1 : 1 ≤ n := by omega
  have ht : 1 ≤ t := by
    dsimp [t]
    nlinarith
  have hN_sub : N - n = t * 2 ^ n := by
    dsimp [N, TightenedErdosUpperBoundFormula, t]
    omega
  have hdiv : (3 * N) / n = 3 + 6 * n * 2 ^ n := by
    have h3N : 3 * N = n * (3 + 6 * n * 2 ^ n) := by
      dsimp [N, TightenedErdosUpperBoundFormula]
      ring
    rw [h3N, Nat.mul_div_right _ (by omega : 0 < n)]
  have hchoose_le : N.choose n ≤ 2 ^ t := by
    calc
      N.choose n ≤ ((3 * N) / n) ^ n := choose_le_three_mul_div_pow N n
      _ = (3 + 6 * n * 2 ^ n) ^ n := by rw [hdiv]
      _ ≤ (2 ^ (2 * n)) ^ n := Nat.pow_le_pow_left (three_add_six_mul_two_pow_le_four_pow hn) n
      _ = 2 ^ t := by
        rw [← pow_mul]
        congr 1
        dsimp [t]
        ring
  have hdecay := two_pow_mul_sub_one_pow_lt n t hn1 ht
  have hcrit : ErdosProbabilisticCriterion n N := by
    dsimp [ErdosProbabilisticCriterion]
    rw [hN_sub]
    calc
      N.choose n * (2 ^ n - 1) ^ (t * 2 ^ n) ≤ 2 ^ t * (2 ^ n - 1) ^ (t * 2 ^ n) :=
        Nat.mul_le_mul_right _ hchoose_le
      _ < (2 ^ n) ^ (t * 2 ^ n) := hdecay
  refine ⟨hcrit, ?_⟩
  dsimp [TightenedErdosUpperBoundFormula]
  have hpow_ge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hterm1 : n ≤ n ^ 2 * 2 ^ n := by
    calc
      n ≤ n ^ 2 * 1 := by nlinarith
      _ ≤ n ^ 2 * 2 ^ n := Nat.mul_le_mul_left (n ^ 2) hpow_ge
  calc
    n + 2 * n ^ 2 * 2 ^ n ≤ n ^ 2 * 2 ^ n + 2 * n ^ 2 * 2 ^ n :=
      Nat.add_le_add_right hterm1 _
    _ = 3 * n ^ 2 * 2 ^ n := by ring

/-- Unconditional existence of an `n`-paradoxical tournament on `TightenedErdosUpperBoundFormula n`
(`n + 2 * n ^ 2 * 2 ^ n`) vertices for every `1 ≤ n`. -/
theorem hasParadoxicalTournament_tightenedErdosUpperBoundFormula (n : ℕ) (hn : 1 ≤ n) :
    HasParadoxicalTournament n (TightenedErdosUpperBoundFormula n) := by
  by_cases hn5 : 5 ≤ n
  · have hcrit := (tightenedErdosUpperBoundFormula_criterion_of_five_le hn5).1
    have hnN : n ≤ TightenedErdosUpperBoundFormula n := by
      dsimp [TightenedErdosUpperBoundFormula]
      omega
    exact (hasParadoxicalTournament_of_erdosProbabilisticCriterion hnN hcrit).2
  · interval_cases n
    · exact hasParadoxicalTournament_mono_N (by decide : 3 ≤ TightenedErdosUpperBoundFormula 1)
        ⟨paley3Digraph, isParadoxicalTournament_paley3Digraph⟩
    · exact hasParadoxicalTournament_mono_N (by decide : 7 ≤ TightenedErdosUpperBoundFormula 2)
        ((paley7Digraph_dom2_and_f_two 7).1.mpr (by decide))
    · exact hasParadoxicalTournament_mono_N (by decide : 19 ≤ TightenedErdosUpperBoundFormula 3)
        ((hasParadoxicalTournament_three_iff_and_f_three 19).1.mpr (by decide))
    · exact hasParadoxicalTournament_mono_N (by decide : 67 ≤ TightenedErdosUpperBoundFormula 4)
        hasParadoxicalTournament_four_67_and_f_four_bounds.1

/-- Unconditional tightened upper bound on `legacyF n`: for every `1 ≤ n`,
`legacyF n ≤ n + 2 * n ^ 2 * 2 ^ n` and `legacyF n ≤ 3 * n ^ 2 * 2 ^ n` (reducing the leading coefficient from
`5 * n ^ 2 * 2 ^ n` to `3 * n ^ 2 * 2 ^ n`). -/
theorem f_le_tightenedErdosUpperBoundFormula (n : ℕ) (hn : 1 ≤ n) :
    legacyF n ≤ TightenedErdosUpperBoundFormula n ∧
      legacyF n ≤ n + 2 * n ^ 2 * 2 ^ n ∧
      legacyF n ≤ 3 * n ^ 2 * 2 ^ n := by
  have hex := hasParadoxicalTournament_tightenedErdosUpperBoundFormula n hn
  have hle : legacyF n ≤ TightenedErdosUpperBoundFormula n := legacyF_le_of_hasParadoxicalTournament hex
  have h3 : TightenedErdosUpperBoundFormula n ≤ 3 * n ^ 2 * 2 ^ n := by
    dsimp [TightenedErdosUpperBoundFormula]
    have hpow_ge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
    have hterm1 : n ≤ n ^ 2 * 2 ^ n := by
      calc
        n ≤ n ^ 2 * 1 := by nlinarith
        _ ≤ n ^ 2 * 2 ^ n := Nat.mul_le_mul_left (n ^ 2) hpow_ge
    calc
      n + 2 * n ^ 2 * 2 ^ n ≤ n ^ 2 * 2 ^ n + 2 * n ^ 2 * 2 ^ n :=
        Nat.add_le_add_right hterm1 _
      _ = 3 * n ^ 2 * 2 ^ n := by ring
  exact ⟨hle, hle, le_trans hle h3⟩

/-- For all `7 ≤ n`, `3 + 3 * (2 * n - 1) * 2 ^ n ≤ 2 ^ (2 * n - 1)`. -/
theorem three_add_three_mul_two_mul_sub_one_two_pow_le {n : ℕ} (hn : 7 ≤ n) :
    3 + 3 * (2 * n - 1) * 2 ^ n ≤ 2 ^ (2 * n - 1) := by
  have haux : ∀ m : ℕ, 3 * (2 * (m + 7) - 1) + 1 ≤ 2 ^ (m + 6) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      have hpow : 2 ^ (m + 1 + 6) = 2 * 2 ^ (m + 6) := by ring
      omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hm := haux m
  have hcomm : 7 + m = m + 7 := by omega
  rw [hcomm]
  have hpow : 2 ^ (2 * (m + 7) - 1) = 2 ^ (m + 6) * 2 ^ (m + 7) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  have hge3 : 3 ≤ 2 ^ (m + 7) := by
    have : 128 ≤ 2 ^ (m + 7) := by
      calc 128 = 2 ^ 7 := by decide
      _ ≤ 2 ^ (m + 7) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  nlinarith

/-- Via `choose_le_three_mul_div_pow`, `SharpErdosUpperBoundFormula n = n + n * (2 * n - 1) * 2 ^ n`
satisfies `ErdosProbabilisticCriterion n (SharpErdosUpperBoundFormula n)` and
`SharpErdosUpperBoundFormula n ≤ 2 * n ^ 2 * 2 ^ n` for all `7 ≤ n`. -/
theorem sharpErdosUpperBoundFormula_criterion_of_seven_le {n : ℕ} (hn : 7 ≤ n) :
    ErdosProbabilisticCriterion n (SharpErdosUpperBoundFormula n) ∧
      SharpErdosUpperBoundFormula n ≤ 2 * n ^ 2 * 2 ^ n := by
  let N := SharpErdosUpperBoundFormula n
  let t := n * (2 * n - 1)
  have hn1 : 1 ≤ n := by omega
  have h2n1 : 1 ≤ 2 * n - 1 := by omega
  have ht : 1 ≤ t := by
    dsimp [t]
    exact Nat.mul_pos hn1 h2n1
  have hN_sub : N - n = t * 2 ^ n := by
    dsimp [N, SharpErdosUpperBoundFormula, t]
    omega
  have hdiv : (3 * N) / n = 3 + 3 * (2 * n - 1) * 2 ^ n := by
    have h3N : 3 * N = n * (3 + 3 * (2 * n - 1) * 2 ^ n) := by
      dsimp [N, SharpErdosUpperBoundFormula]
      ring
    rw [h3N, Nat.mul_div_right _ (by omega : 0 < n)]
  have hchoose_le : N.choose n ≤ 2 ^ t := by
    calc
      N.choose n ≤ ((3 * N) / n) ^ n := choose_le_three_mul_div_pow N n
      _ = (3 + 3 * (2 * n - 1) * 2 ^ n) ^ n := by rw [hdiv]
      _ ≤ (2 ^ (2 * n - 1)) ^ n :=
        Nat.pow_le_pow_left (three_add_three_mul_two_mul_sub_one_two_pow_le hn) n
      _ = 2 ^ t := by
        rw [← pow_mul]
        congr 1
        dsimp [t]
        ring
  have hdecay := two_pow_mul_sub_one_pow_lt n t hn1 ht
  have hcrit : ErdosProbabilisticCriterion n N := by
    dsimp [ErdosProbabilisticCriterion]
    rw [hN_sub]
    calc
      N.choose n * (2 ^ n - 1) ^ (t * 2 ^ n) ≤ 2 ^ t * (2 ^ n - 1) ^ (t * 2 ^ n) :=
        Nat.mul_le_mul_right _ hchoose_le
      _ < (2 ^ n) ^ (t * 2 ^ n) := hdecay
  refine ⟨hcrit, ?_⟩
  dsimp [SharpErdosUpperBoundFormula]
  have hpow_ge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hsplit : n * (2 * n - 1) + n = 2 * n ^ 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn1
    have hsub : 2 * (1 + m) - 1 = 2 * m + 1 := by omega
    rw [hsub]
    ring
  calc
    n + n * (2 * n - 1) * 2 ^ n ≤ n * 2 ^ n + n * (2 * n - 1) * 2 ^ n :=
      Nat.add_le_add_right (Nat.le_mul_of_pos_right n hpow_ge) _
    _ = (n * (2 * n - 1) + n) * 2 ^ n := by ring
    _ = 2 * n ^ 2 * 2 ^ n := by rw [hsplit]


end Erdos902
end
