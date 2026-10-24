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
open scoped Classical BigOperators


/-!
# Erdős Problem 902: Minimal `n`-Paradoxical Tournaments (Schütte's Problem)

*References:*
- [erdosproblems.com/902](https://www.erdosproblems.com/902)
- [Er63c] Erdős, P., *On a problem in graph theory*. Math. Gaz. 47 (1963), 220–223.
- [SzSz65] Szekeres, E. and Szekeres, G., *On a problem of Schütte and Erdős*. Math. Gaz. 49
  (1965), 290–293.
- OEIS [A362137](https://oeis.org/A362137): Smallest size of an `n`-paradoxical Paley tournament
  (`1, 3, 7, 19, 67, 331, 1163`).

This base module (`Erdos902Unified435.lean`) formalizes the core definitions and foundational
properties for Erdős Problem #902 in Lean 4.35.0-rc2.
-/

namespace Erdos902

variable {V W : Type*}

/-- A **tournament** is a directed graph in which every pair of distinct vertices is connected
by exactly one directed edge. This is the definition used by Formal Conjectures
(`FormalConjecturesForMathlib.Combinatorics.Digraph.Tournament`), restated here so the package
depends only on Mathlib. -/
def IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u))

/-- A vertex `v` dominates a finset `S` in a digraph `G` if `G.Adj v u` holds for every `u ∈ S`. -/
def Dominates (G : Digraph V) (v : V) (S : Finset V) : Prop :=
  ∀ u ∈ S, G.Adj v u

/-- The strict out-neighborhood of `v` in `G : Digraph (Fin N)`. -/
def outNeigh {N : ℕ} (G : Digraph (Fin N)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun u => G.Adj v u)

/-- The strict in-neighborhood of `v` in `G : Digraph (Fin N)`. -/
def inNeigh {N : ℕ} (G : Digraph (Fin N)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun u => G.Adj u v)

/-- The finset of vertices in `Fin N` that dominate a subset `S`. -/
def domSet {N : ℕ} (G : Digraph (Fin N)) (S : Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter (fun v => Dominates G v S)

/-- A subset `U ⊆ Fin N` dominates all `k`-element subsets of `Fin N` in `G` if every `S` of
cardinality `k` has a dominator belonging to `U`. -/
def DominatesAllSubsets {N : ℕ} (G : Digraph (Fin N)) (k : ℕ) (U : Finset (Fin N)) : Prop :=
  ∀ S : Finset (Fin N), S.card = k → ∃ w ∈ U, Dominates G w S

/-- A digraph `G` on a finite vertex type `V` is an `n`-paradoxical tournament (Schütte's
property) if `G` is a tournament, `V` has at least `n` vertices, and every `n`-element subset of
`V` is dominated by at least one vertex. -/
def IsParadoxicalTournament [Fintype V] (n : ℕ) (G : Digraph V) : Prop :=
  IsTournament G ∧ n ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card = n → ∃ v : V, Dominates G v S

/-- There exists an `n`-paradoxical tournament on `Fin N`. -/
def HasParadoxicalTournament (n N : ℕ) : Prop :=
  ∃ G : Digraph (Fin N), IsParadoxicalTournament n G

/-- `f n` is the minimum number of vertices `N` such that there exists an `n`-paradoxical
tournament on `Fin N` (Erdős Problem #902). -/
noncomputable def legacyF (n : ℕ) : ℕ :=
  sInf {N : ℕ | HasParadoxicalTournament n N}




/-- Statement of Erdős's (1963) exponential lower bound `2 ^ (n + 1) - 1 ≤ N`. -/
def ErdosLowerBoundStatement : Prop :=
  ∀ n N : ℕ, HasParadoxicalTournament n N → 2 ^ (n + 1) - 1 ≤ N

/-- Statement of the Szekeres–Szekeres (1965) lower bound `(n + 2) * 2 ^ (n - 1) - 1 ≤ N`. -/
def SzekeresLowerBoundStatement : Prop :=
  ∀ n N : ℕ, 1 ≤ n → HasParadoxicalTournament n N → (n + 2) * 2 ^ (n - 1) - 1 ≤ N

/-- Exact integer form of Erdős's (1963) random-tournament union-bound criterion:
`\binom{N}{n} (2^n - 1)^{N - n} < (2^n)^{N - n}`. -/
def ErdosProbabilisticCriterion (n N : ℕ) : Prop :=
  N.choose n * (2 ^ n - 1) ^ (N - n) < (2 ^ n) ^ (N - n)

/-- Explicit `O(n^2 2^n)` vertex count `N(n) = n + 2 n (n + 1) 2^n` for Erdős's upper bound. -/
def ErdosUpperBoundFormula (n : ℕ) : ℕ :=
  n + 2 * n * (n + 1) * 2 ^ n

/-- Pullback of a digraph `G` along an embedding `g : W ↪ V`. -/
def comapDigraph (G : Digraph V) (g : W ↪ V) : Digraph W where
  Adj x y := G.Adj (g x) (g y)

/-- Canonical order-preserving embedding `Fin M ↪ Fin N` into any finset `S : Finset (Fin N)` of
cardinality at least `M`. -/
def embOfCardLe {N M : ℕ} {S : Finset (Fin N)} (hM : M ≤ S.card) : Fin M ↪ Fin N :=
  (Fin.castLEEmb hM).trans (S.orderEmbOfFin rfl).toEmbedding

@[simp]
theorem comapDigraph_adj (G : Digraph V) (g : W ↪ V) (x y : W) :
    (comapDigraph G g).Adj x y ↔ G.Adj (g x) (g y) := by
  exact Iff.rfl

@[simp]
theorem mem_outNeigh_iff {N : ℕ} {G : Digraph (Fin N)} {v u : Fin N} :
    u ∈ outNeigh G v ↔ G.Adj v u := by
  simp [outNeigh]

@[simp]
theorem mem_inNeigh_iff {N : ℕ} {G : Digraph (Fin N)} {v u : Fin N} :
    u ∈ inNeigh G v ↔ G.Adj u v := by
  simp [inNeigh]

@[simp]
theorem mem_domSet_iff {N : ℕ} {G : Digraph (Fin N)} {S : Finset (Fin N)} {v : Fin N} :
    v ∈ domSet G S ↔ Dominates G v S := by
  simp [domSet]

/-- Every image point of `embOfCardLe hM` lies in `S`. -/
theorem embOfCardLe_mem {N M : ℕ} {S : Finset (Fin N)} (hM : M ≤ S.card) (i : Fin M) :
    embOfCardLe hM i ∈ S := by
  dsimp [embOfCardLe]
  exact S.orderEmbOfFin_mem rfl (Fin.castLE hM i)

/-- Pulling back a tournament along an injective embedding yields a tournament. -/
theorem isTournament_comap {G : Digraph V} (hG : IsTournament G) (g : W ↪ V) :
    IsTournament (comapDigraph G g) := by
  refine ⟨fun v => hG.1 (g v), fun u v huv => ?_⟩
  exact hG.2 (g u) (g v) (g.injective.ne huv)

/-- Every vertex vacuously dominates the empty finset. -/
theorem dominates_empty (G : Digraph V) (v : V) : Dominates G v ∅ := by
  intro u hu
  simp at hu

/-- Subset domination is downward closed under finset inclusion. -/
theorem dominates_subset {G : Digraph V} {v : V} {S T : Finset V}
    (hS : Dominates G v S) (hTS : T ⊆ S) : Dominates G v T := by
  intro u hu
  exact hS u (hTS hu)

/-- In a tournament, a vertex dominating `S` cannot belong to `S`. -/
theorem notMem_of_dominates {G : Digraph V} (hG : IsTournament G) {v : V} {S : Finset V}
    (hv : Dominates G v S) : v ∉ S := by
  intro hmem
  exact hG.1 v (hv v hmem)


/-- Dominating `insert u S` is equivalent to beating `u` and dominating `S`. -/
@[simp]
theorem dominates_insert_iff [DecidableEq V] (G : Digraph V) (v u : V) (S : Finset V) :
    Dominates G v (insert u S) ↔ G.Adj v u ∧ Dominates G v S := by
  simp [Dominates]


/-- In an `n`-paradoxical tournament on `Fin N`, every subset `S` of cardinality `S.card ≤ n` is
dominated by at least one vertex. -/
theorem exists_dominator_of_card_le {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) {S : Finset (Fin N)} (hS : S.card ≤ n) :
    ∃ v : Fin N, Dominates G v S := by
  have hN : n ≤ (Finset.univ : Finset (Fin N)).card := by
    simpa using hG.2.1
  have hdiff : n - S.card ≤ (Finset.univ \ S).card := by
    rw [Finset.card_sdiff, Finset.inter_univ]
    omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hdiff
  have hdisj : Disjoint S R :=
    Finset.disjoint_left.mpr (fun x hxS hxR => (Finset.mem_sdiff.mp (hRsub hxR)).2 hxS)
  have hT : (S ∪ R).card = n := by
    rw [Finset.card_union_of_disjoint hdisj, hRcard]
    omega
  obtain ⟨v, hv⟩ := hG.2.2 (S ∪ R) hT
  exact ⟨v, dominates_subset hv Finset.subset_union_left⟩



/-- Every `n`-paradoxical tournament on `Fin N` has at least `n + 1` vertices. -/
theorem card_gt_of_isParadoxicalTournament {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) : n + 1 ≤ N := by
  have hnN : n ≤ N := by simpa using hG.2.1
  obtain ⟨S, _, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N))) (by simpa using hnN)
  obtain ⟨v, hv⟩ := hG.2.2 S hScard
  have hv_not : v ∉ S := notMem_of_dominates hG.1 hv
  have hlt : S.card < (Finset.univ : Finset (Fin N)).card :=
    Finset.card_lt_card ⟨Finset.subset_univ S, fun hsub => hv_not (hsub (Finset.mem_univ v))⟩
  simp only [Finset.card_univ, Fintype.card_fin] at hlt
  omega

/-- Projection `Fin (N + 1) → Fin N` mapping `Fin.last N` to `⟨0, hN⟩` and `Fin.castSucc i` to `i`. -/
def cloneProj {N : ℕ} (hN : 1 ≤ N) (x : Fin (N + 1)) : Fin N :=
  if hx : x.val < N then ⟨x.val, hx⟩ else ⟨0, hN⟩

/-- One-vertex blowup of `G : Digraph (Fin N)` cloning vertex `⟨0, hN⟩` at `Fin.last N`. -/
def cloneDigraph {N : ℕ} (hN : 1 ≤ N) (G : Digraph (Fin N)) : Digraph (Fin (N + 1)) where
  Adj x y :=
    if cloneProj hN x = cloneProj hN y then x.val < y.val
    else G.Adj (cloneProj hN x) (cloneProj hN y)

/-- Cloning vertex `0` of a tournament on `Fin N` produces a tournament on `Fin (N + 1)`. -/
theorem isTournament_cloneDigraph {N : ℕ} (hN : 1 ≤ N) {G : Digraph (Fin N)}
    (hG : IsTournament G) : IsTournament (cloneDigraph hN G) := by
  refine ⟨fun v => by simp [cloneDigraph], fun u v huv => ?_⟩
  dsimp [cloneDigraph]
  by_cases hproj : cloneProj hN u = cloneProj hN v
  · rw [if_pos hproj, if_pos hproj.symm]
    have hval : u.val ≠ v.val := Fin.val_ne_of_ne huv
    omega
  · have hproj_symm : cloneProj hN v ≠ cloneProj hN u := Ne.symm hproj
    rw [if_neg hproj, if_neg hproj_symm]
    exact hG.2 (cloneProj hN u) (cloneProj hN v) hproj

/-- Cloning vertex `0` of an `n`-paradoxical tournament on `Fin N` yields an `n`-paradoxical
tournament on `Fin (N + 1)`. -/
theorem isParadoxicalTournament_cloneDigraph {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) :
    IsParadoxicalTournament n (cloneDigraph (by have := card_gt_of_isParadoxicalTournament hG; omega) G) := by
  have hN : 1 ≤ N := by
    have := card_gt_of_isParadoxicalTournament hG
    omega
  have hnN : n ≤ N := by simpa using hG.2.1
  refine ⟨isTournament_cloneDigraph hN hG.1, ?_, fun S hScard => ?_⟩
  · simp only [Fintype.card_fin]
    omega
  · let T : Finset (Fin N) := S.image (cloneProj hN)
    have hTcard : T.card ≤ n := by
      calc
        T.card ≤ S.card := Finset.card_image_le
        _ = n := hScard
    obtain ⟨w, hw⟩ := exists_dominator_of_card_le hG hTcard
    let wLift : Fin (N + 1) := Fin.castSucc w
    have hwproj : cloneProj hN wLift = w := by
      simp [cloneProj, wLift, w.isLt]
    refine ⟨wLift, fun u hu => ?_⟩
    have huT : cloneProj hN u ∈ T := Finset.mem_image_of_mem (cloneProj hN) hu
    have hadj : G.Adj w (cloneProj hN u) := hw (cloneProj hN u) huT
    have hne : w ≠ cloneProj hN u := by
      intro heq
      rw [heq] at hadj
      exact hG.1.1 (cloneProj hN u) hadj
    dsimp [cloneDigraph]
    rw [hwproj, if_neg hne]
    exact hadj

/-- Upward monotonicity in `N`: if `HasParadoxicalTournament n N` and `N ≤ M`, then
`HasParadoxicalTournament n M`. -/
theorem hasParadoxicalTournament_mono_N {n N M : ℕ} (hNM : N ≤ M)
    (hN : HasParadoxicalTournament n N) : HasParadoxicalTournament n M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction k with
  | zero => simpa using hN
  | succ k ih =>
    rcases ih (by omega) with ⟨G, hG⟩
    exact ⟨_, isParadoxicalTournament_cloneDigraph hG⟩

/-- Upper-bound principle for `legacyF n`: any `N` with `HasParadoxicalTournament n N` satisfies
`legacyF n ≤ N`. -/
theorem legacyF_le_of_hasParadoxicalTournament {n N : ℕ} (h : HasParadoxicalTournament n N) :
    legacyF n ≤ N := by
  exact Nat.sInf_le h

/-- Lower-bound principle for `legacyF n`: if `HasParadoxicalTournament n M` holds for some `M` and
every `N` satisfying `HasParadoxicalTournament n N` has `B ≤ N`, then `B ≤ legacyF n`. -/
theorem le_legacyF_of_forall_hasParadoxicalTournament {n M B : ℕ}
    (hex : HasParadoxicalTournament n M)
    (hB : ∀ N : ℕ, HasParadoxicalTournament n N → B ≤ N) :
    B ≤ legacyF n := by
  have hmem : HasParadoxicalTournament n (legacyF n) :=
    Nat.sInf_mem (s := {N : ℕ | HasParadoxicalTournament n N})
    ⟨M, show M ∈ {N : ℕ | HasParadoxicalTournament n N} from hex⟩
  exact hB (legacyF n) hmem


/-- The unique tournament on `Fin 1` is `0`-paradoxical. -/
theorem hasParadoxicalTournament_zero_one : HasParadoxicalTournament 0 1 := by
  refine ⟨Digraph.emptyDigraph (Fin 1), ⟨fun v => by simp, fun u v huv => ?_⟩, by simp, ?_⟩
  · exfalso
    exact huv (Subsingleton.elim u v)
  · intro S hS
    rw [Finset.card_eq_zero.mp hS]
    exact ⟨⟨0, by decide⟩, dominates_empty _ _⟩

/-- Exact characterization `HasParadoxicalTournament 0 N ↔ 1 ≤ N` and `f 0 = 1`. -/
theorem hasParadoxicalTournament_zero_iff_and_f_zero (N : ℕ) :
    (HasParadoxicalTournament 0 N ↔ 1 ≤ N) ∧ legacyF 0 = 1 := by
  have hiff : ∀ M : ℕ, HasParadoxicalTournament 0 M ↔ 1 ≤ M := by
    intro M
    refine ⟨fun ⟨G, hG⟩ => card_gt_of_isParadoxicalTournament hG, fun hM => ?_⟩
    exact hasParadoxicalTournament_mono_N hM hasParadoxicalTournament_zero_one
  refine ⟨hiff N, le_antisymm (legacyF_le_of_hasParadoxicalTournament hasParadoxicalTournament_zero_one) ?_⟩
  exact le_legacyF_of_forall_hasParadoxicalTournament hasParadoxicalTournament_zero_one
    (fun M hM => (hiff M).mp hM)

/-- The directed 3-cycle Paley tournament `0 → 1 → 2 → 0` on `Fin 3`. -/
def paley3Digraph : Digraph (Fin 3) where
  Adj u v := (v.val + 3 - u.val) % 3 = 1

/-- `paley3Digraph` is a `1`-paradoxical tournament on `Fin 3`. -/
theorem isParadoxicalTournament_paley3Digraph : IsParadoxicalTournament 1 paley3Digraph := by
  refine ⟨⟨by dsimp [paley3Digraph]; decide, by dsimp [paley3Digraph]; decide⟩, by decide, ?_⟩
  intro S hScard
  rcases Finset.card_eq_one.mp hScard with ⟨u, rfl⟩
  have hdom : ∀ x : Fin 3, ∃ v : Fin 3, paley3Digraph.Adj v x := by
    dsimp [paley3Digraph]
    decide
  obtain ⟨v, hv⟩ := hdom u
  refine ⟨v, fun w hw => ?_⟩
  rw [Finset.mem_singleton.mp hw]
  exact hv

/-- No tournament on `N < 3` vertices is `1`-paradoxical. -/
theorem not_hasParadoxicalTournament_one_of_lt_three {N : ℕ} (hN : N < 3) :
    ¬ HasParadoxicalTournament 1 N := by
  rintro ⟨G, hG⟩
  have hgt := card_gt_of_isParadoxicalTournament hG
  have hN2 : N = 2 := by omega
  subst hN2
  obtain ⟨v0, hv0⟩ := hG.2.2 {⟨0, by decide⟩} (Finset.card_singleton _)
  obtain ⟨v1, hv1⟩ := hG.2.2 {⟨1, by decide⟩} (Finset.card_singleton _)
  have h0 : G.Adj v0 ⟨0, by decide⟩ := hv0 ⟨0, by decide⟩ (Finset.mem_singleton_self _)
  have h1 : G.Adj v1 ⟨1, by decide⟩ := hv1 ⟨1, by decide⟩ (Finset.mem_singleton_self _)
  have hv0_ne : v0.val ≠ 0 := by
    intro h
    have heq : v0 = ⟨0, by decide⟩ := Fin.ext h
    rw [heq] at h0
    exact hG.1.1 _ h0
  have hv1_ne : v1.val ≠ 1 := by
    intro h
    have heq : v1 = ⟨1, by decide⟩ := Fin.ext h
    rw [heq] at h1
    exact hG.1.1 _ h1
  have hv0_eq : v0 = ⟨1, by decide⟩ := Fin.ext (by change v0.val = 1; omega)
  have hv1_eq : v1 = ⟨0, by decide⟩ := Fin.ext (by change v1.val = 0; omega)
  rw [hv0_eq] at h0
  rw [hv1_eq] at h1
  exact (hG.1.2 ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)).mp h0 h1

/-- Exact characterization `HasParadoxicalTournament 1 N ↔ 3 ≤ N` and `f 1 = 3`. -/
theorem hasParadoxicalTournament_one_iff_and_f_one (N : ℕ) :
    (HasParadoxicalTournament 1 N ↔ 3 ≤ N) ∧ legacyF 1 = 3 := by
  have hex3 : HasParadoxicalTournament 1 3 := ⟨paley3Digraph, isParadoxicalTournament_paley3Digraph⟩
  have hiff : ∀ M : ℕ, HasParadoxicalTournament 1 M ↔ 3 ≤ M := by
    intro M
    refine ⟨fun hM => ?_, fun hM => hasParadoxicalTournament_mono_N hM hex3⟩
    by_contra hlt
    exact not_hasParadoxicalTournament_one_of_lt_three (by omega) hM
  refine ⟨hiff N, le_antisymm (legacyF_le_of_hasParadoxicalTournament hex3) ?_⟩
  exact le_legacyF_of_forall_hasParadoxicalTournament hex3 (fun M hM => (hiff M).mp hM)

/-! ## Out-degree double counting and the Erdős and Szekeres–Szekeres bounds -/

/-!
# Erdős Problem 902: Out-Degree Double Counting, Erdős and Szekeres–Szekeres Bounds

This module builds on `Erdos902Unified435` to establish universally quantified structural theorems for
Schütte's `n`-paradoxical tournament problem (Erdős Problem #902) in Lean 4.35.0-rc2:

1. **Out-Degree, In-Degree, and Subset-Domination Double Counting:**
   - Exact partition `outNeigh G v ∪ inNeigh G v = Finset.univ.erase v` and
     `(outNeigh G v).card + (inNeigh G v).card = N - 1` in any tournament `G` on `Fin N`.
   - Degree sum identities `∑ v, (outNeigh G v).card = ∑ v, (inNeigh G v).card`,
     `2 * ∑ v, (inNeigh G v).card = N * (N - 1)`, and existence of a vertex with
     `2 * (inNeigh G v).card + 1 ≤ N`.
   - Universal `k`-subset double-counting identity:
     `∑ S ∈ powersetCard k univ, (domSet G S).card = ∑ v, (outNeigh G v).card.choose k`.

2. **In-Neighborhood Paradoxical Restriction and Erdős's (1963) `2^(n+1) - 1` Lower Bound:**
   - Every vertex `v` in an `(n + 1)`-paradoxical tournament has `(inNeigh G v).card ≥ n + 1`, and
     the subtournament induced on `inNeigh G v` is `n`-paradoxical.
   - Inductive lower-bound step `(∀ M, HasParadoxicalTournament n M → B ≤ M) → HasParadoxicalTournament (n + 1) N → 2 * B + 1 ≤ N`.
   - Unconditional proof of Erdős's (1963) lower bound:
     `∀ n N : ℕ, HasParadoxicalTournament n N → 2 ^ (n + 1) - 1 ≤ N ∧ 2 ^ n < N`.
   - Binomial out-degree double-counting bound `N.choose n ≤ ∑ v, (outNeigh G v).card.choose n`.

3. **Szekeres–Szekeres (1965) Absorptive-Set Hierarchy and `(n + 2) * 2 ^ (n - 1) - 1` Lower Bound:**
   - No vertex dominates a `1`-dominating subset `U` (`DominatesAllSubsets G 1 U`) in a tournament,
     forcing `n + 1 ≤ U.card` in any `n`-paradoxical tournament.
   - Local minimum in-degree averaging inside any nonempty subset `U ⊆ Fin N` and inductive descent
     from `DominatesAllSubsets G (k + 1) U` to `DominatesAllSubsets G k (U.filter (G.Adj · v))`.
   - Unconditional proof of the Szekeres–Szekeres (1965) theorem:
     `∀ n N : ℕ, 1 ≤ n → HasParadoxicalTournament n N → (n + 2) * 2 ^ (n - 1) - 1 ≤ N ∧ n * 2 ^ (n - 1) < N`.

4. **Directed Paley Tournaments `QR_7`, `QR_19` and Exact Evaluations `legacyF 2 = 7`, `legacyF 3 = 19`:**
   - Verification that `paley7Digraph` is `2`-paradoxical, proving `HasParadoxicalTournament 2 N ↔ 7 ≤ N`
     and `legacyF 2 = 7`.
   - Circulant translation reduction on `paley19Digraph` proving universal 3-element domination,
     `HasParadoxicalTournament 3 N ↔ 19 ≤ N`, and Szekeres–Szekeres's exact value `legacyF 3 = 19`.

5. **Erdős's (1963) Probabilistic Counting Criterion and `O(n^2 2^n)` Upper Bound:**
   - Exact natural-number Bernoulli/binomial bound `2 * a ^ a ≤ (a + 1) ^ a` (`1 ≤ a`),
     exponential decay `2 ^ t * (2 ^ n - 1) ^ (t * 2 ^ n) < (2 ^ n) ^ (t * 2 ^ n)`,
     binomial bound `N.choose n ≤ N ^ n`, and verification that
    `ErdosUpperBoundFormula n = n + 2 * n * (n + 1) * 2 ^ n ≤ 5 * n ^ 2 * 2 ^ n` satisfies
    `ErdosProbabilisticCriterion n (ErdosUpperBoundFormula n)` for all `1 ≤ n`.
-/

/-- In any tournament `G` on `Fin N`, the out-neighborhood and in-neighborhood of a vertex `v`
are disjoint. -/
theorem outNeigh_disjoint_inNeigh {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (v : Fin N) :
    Disjoint (outNeigh G v) (inNeigh G v) := by
  rw [Finset.disjoint_left]
  intro u hu_out hu_in
  rw [mem_outNeigh_iff] at hu_out
  rw [mem_inNeigh_iff] at hu_in
  have huv : v ≠ u := fun h => hG.1 v (h ▸ hu_out)
  exact (hG.2 v u huv).mp hu_out hu_in

/-- In any tournament `G` on `Fin N`, the union of `outNeigh G v` and `inNeigh G v` is
`Finset.univ.erase v`. -/
theorem outNeigh_union_inNeigh_eq_erase {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (v : Fin N) :
    outNeigh G v ∪ inNeigh G v = Finset.univ.erase v := by
  ext u
  rw [Finset.mem_union, mem_outNeigh_iff, mem_inNeigh_iff, Finset.mem_erase]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h1 | h2
    · exact ⟨fun heq => hG.1 v (heq ▸ h1), Finset.mem_univ u⟩
    · exact ⟨fun heq => hG.1 v (heq ▸ h2), Finset.mem_univ u⟩
  · by_cases hadj : G.Adj v u
    · exact Or.inl hadj
    · right
      have hne : v ≠ u := Ne.symm h.1
      by_contra hnot
      exact hadj ((hG.2 v u hne).mpr hnot)

/-- In any tournament `G` on `Fin N`, `(outNeigh G v).card + (inNeigh G v).card = N - 1`. -/
theorem card_outNeigh_add_card_inNeigh {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (v : Fin N) :
    (outNeigh G v).card + (inNeigh G v).card = N - 1 := by
  rw [← Finset.card_union_of_disjoint (outNeigh_disjoint_inNeigh hG v),
    outNeigh_union_inNeigh_eq_erase hG v,
    Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]

/-- Double-counting identity: the sum of out-degrees equals the sum of in-degrees in any
digraph on `Fin N`. -/
theorem sum_card_outNeigh_eq_sum_card_inNeigh {N : ℕ} (G : Digraph (Fin N)) :
    (∑ v : Fin N, (outNeigh G v).card) = ∑ v : Fin N, (inNeigh G v).card := by
  simp_rw [outNeigh, inNeigh, Finset.card_filter]
  rw [Finset.sum_comm]

/-- In any tournament `G` on `Fin N`, twice the sum of in-degrees equals `N * (N - 1)`. -/
theorem two_mul_sum_card_inNeigh {N : ℕ} {G : Digraph (Fin N)} (hG : IsTournament G) :
    2 * (∑ v : Fin N, (inNeigh G v).card) = N * (N - 1) := by
  have hsum : ∑ v : Fin N, ((outNeigh G v).card + (inNeigh G v).card) = ∑ _v : Fin N, (N - 1) :=
    Finset.sum_congr rfl (fun v _ => card_outNeigh_add_card_inNeigh hG v)
  rw [Finset.sum_add_distrib, sum_card_outNeigh_eq_sum_card_inNeigh G,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- Every nonempty tournament `G` on `Fin N` (`1 ≤ N`) contains a vertex `v` whose in-degree
satisfies `2 * (inNeigh G v).card + 1 ≤ N`. -/
theorem exists_vertex_inNeigh_card_le {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) (hN : 1 ≤ N) :
    ∃ v : Fin N, 2 * (inNeigh G v).card + 1 ≤ N := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hle : ∀ v : Fin N, N ≤ 2 * (inNeigh G v).card := fun v => by
    have hv := h v
    omega
  have hsum : ∑ _v : Fin N, N ≤ ∑ v : Fin N, 2 * (inNeigh G v).card :=
    Finset.sum_le_sum (fun v _ => hle v)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum, two_mul_sum_card_inNeigh hG] at hsum
  have hlt : N * (N - 1) < N * N := Nat.mul_lt_mul_of_pos_left (by omega) hN
  omega

/-- Universal `k`-subset double-counting identity: summing `(domSet G S).card` over all `k`-subsets
`S` of `Fin N` equals the sum of `(outNeigh G v).card.choose k` over all vertices `v`. -/
theorem sum_card_domSet_eq_sum_choose_outNeigh {N : ℕ} (G : Digraph (Fin N)) (k : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, (domSet G S).card) =
      ∑ v : Fin N, (outNeigh G v).card.choose k := by
  simp_rw [domSet, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.card_filter, ← Finset.card_powersetCard]
  congr 1
  ext S
  rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
  exact ⟨fun h => ⟨fun x hx => mem_outNeigh_iff.mpr (h.2 x hx), h.1.2⟩,
    fun h => ⟨⟨Finset.subset_univ S, h.2⟩, fun x hx => mem_outNeigh_iff.mp (h.1 hx)⟩⟩

/-- In any `(n + 1)`-paradoxical tournament `G` on `Fin N`, every vertex `v` has in-degree at least
`n + 1` (`n + 1 ≤ (inNeigh G v).card`), and the subtournament induced on `inNeigh G v` is
`n`-paradoxical. -/
theorem isParadoxicalTournament_inNeigh {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament (n + 1) G) (v : Fin N) :
    n + 1 ≤ (inNeigh G v).card ∧ HasParadoxicalTournament n (inNeigh G v).card := by
  have hcard : n + 1 ≤ (inNeigh G v).card := by
    by_contra hlt
    have hle : (insert v (inNeigh G v)).card ≤ n + 1 := by
      have h1 := Finset.card_insert_le v (inNeigh G v)
      omega
    obtain ⟨w, hw⟩ := exists_dominator_of_card_le hG hle
    have hwv : G.Adj w v := (dominates_insert_iff G w v (inNeigh G v)).mp hw |>.1
    have hwin : w ∈ insert v (inNeigh G v) :=
      Finset.mem_insert_of_mem (mem_inNeigh_iff.mpr hwv)
    exact notMem_of_dominates hG.1 hw hwin
  refine ⟨hcard, ?_⟩
  let M := (inNeigh G v).card
  let g : Fin M ↪ Fin N := embOfCardLe (le_refl M)
  refine ⟨comapDigraph G g, isTournament_comap hG.1 g, ?_, ?_⟩
  · simp only [Fintype.card_fin]
    omega
  · intro S hScard
    have hv_not : v ∉ S.map g := by
      intro hv_mem
      rcases Finset.mem_map.mp hv_mem with ⟨i, _, hi⟩
      have hmem : g i ∈ inNeigh G v := embOfCardLe_mem (le_refl M) i
      rw [hi, mem_inNeigh_iff] at hmem
      exact hG.1.1 v hmem
    have hcard_ins : (insert v (S.map g)).card = n + 1 := by
      rw [Finset.card_insert_of_notMem hv_not, Finset.card_map, hScard]
    obtain ⟨w, hw⟩ := hG.2.2 (insert v (S.map g)) hcard_ins
    have hw_ins := (dominates_insert_iff G w v (S.map g)).mp hw
    have hw_in : w ∈ inNeigh G v := mem_inNeigh_iff.mpr hw_ins.1
    have hmap_sub : (Finset.univ : Finset (Fin M)).map g ⊆ inNeigh G v := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩
      exact embOfCardLe_mem (le_refl M) i
    have hmap_eq : (Finset.univ : Finset (Fin M)).map g = inNeigh G v :=
      Finset.eq_of_subset_of_card_le hmap_sub (by simp [M])
    rw [← hmap_eq] at hw_in
    rcases Finset.mem_map.mp hw_in with ⟨i, _, rfl⟩
    refine ⟨i, fun j hj => ?_⟩
    exact hw_ins.2 (g j) (Finset.mem_map_of_mem g hj)

/-- Inductive lower-bound step: if every `n`-paradoxical tournament has at least `B` vertices,
then every `(n + 1)`-paradoxical tournament has at least `2 * B + 1` vertices. -/
theorem hasParadoxicalTournament_step_lower_bound {n N B : ℕ}
    (hB : ∀ M : ℕ, HasParadoxicalTournament n M → B ≤ M)
    (hN : HasParadoxicalTournament (n + 1) N) :
    2 * B + 1 ≤ N := by
  rcases hN with ⟨G, hG⟩
  have hpos : 1 ≤ N := by
    have := card_gt_of_isParadoxicalTournament hG
    omega
  obtain ⟨v, hv⟩ := exists_vertex_inNeigh_card_le hG.1 hpos
  have hin := (isParadoxicalTournament_inNeigh hG v).2
  have hle : B ≤ (inNeigh G v).card := hB (inNeigh G v).card hin
  omega

/-- Erdős's (1963) exponential lower bound: every `n`-paradoxical tournament on `Fin N` satisfies
`2 ^ (n + 1) - 1 ≤ N` and `2 ^ n ≤ N`. -/
theorem erdos_lower_bound_of_hasParadoxicalTournament :
    ∀ n N : ℕ, HasParadoxicalTournament n N → 2 ^ (n + 1) - 1 ≤ N ∧ 2 ^ n ≤ N
  | 0, N, ⟨G, hG⟩ => by
    have hgt : 0 + 1 ≤ N := card_gt_of_isParadoxicalTournament hG
    change 2 - 1 ≤ N ∧ 1 ≤ N
    omega
  | n + 1, N, hN => by
    have hstep := hasParadoxicalTournament_step_lower_bound
      (fun M hM => (erdos_lower_bound_of_hasParadoxicalTournament n M hM).1) hN
    have hpow : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    have hpos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by decide)
    omega

/-- In any `(n + 1)`-paradoxical tournament `G` on `Fin N`, every vertex `v` has in-degree at
least `2 ^ (n + 1) - 1` and out-degree at most `N - 2 ^ (n + 1)`. -/
theorem inNeigh_card_ge_erdos_of_isParadoxicalTournament {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament (n + 1) G) (v : Fin N) :
    2 ^ (n + 1) - 1 ≤ (inNeigh G v).card ∧ (outNeigh G v).card + 2 ^ (n + 1) ≤ N := by
  have hin := (isParadoxicalTournament_inNeigh hG v).2
  have hlb := (erdos_lower_bound_of_hasParadoxicalTournament n (inNeigh G v).card hin).1
  have hsum := card_outNeigh_add_card_inNeigh hG.1 v
  have hgt := card_gt_of_isParadoxicalTournament hG
  have hpos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by decide)
  omega


/-- Erdős's (1963) lower bound transferred to `f n`: whenever an `n`-paradoxical tournament exists,
`2 ^ (n + 1) - 1 ≤ legacyF n` and `ErdosLowerBoundStatement` holds. -/
theorem legacyF_ge_erdos_lower_bound {n M : ℕ} (hex : HasParadoxicalTournament n M) :
    2 ^ (n + 1) - 1 ≤ legacyF n ∧ ErdosLowerBoundStatement := by
  refine ⟨le_legacyF_of_forall_hasParadoxicalTournament hex
    (fun N hN => (erdos_lower_bound_of_hasParadoxicalTournament n N hN).1),
    fun k N hN => (erdos_lower_bound_of_hasParadoxicalTournament k N hN).1⟩

/-- In a tournament `G`, if `U` dominates all `1`-element subsets of `Fin N`, then no vertex `z`
can dominate `U`. -/
theorem not_dominates_of_dominatesAllSubsets_one {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) {U : Finset (Fin N)} (hU : DominatesAllSubsets G 1 U) (z : Fin N) :
    ¬ Dominates G z U := by
  intro hz
  obtain ⟨w, hwU, hwz⟩ := hU {z} (Finset.card_singleton z)
  have hadj_wz : G.Adj w z := hwz z (Finset.mem_singleton_self z)
  have hadj_zw : G.Adj z w := hz w hwU
  have hne : w ≠ z := fun heq => hG.1 z (heq ▸ hadj_wz)
  exact (hG.2 w z hne).mp hadj_wz hadj_zw

/-- Szekeres–Szekeres (1965) base case: in any `n`-paradoxical tournament `G` on `Fin N`, any
subset `U` satisfying `DominatesAllSubsets G 1 U` has cardinality at least `n + 1`. -/
theorem card_ge_succ_of_dominatesAllSubsets_one {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) {U : Finset (Fin N)}
    (hU : DominatesAllSubsets G 1 U) :
    n + 1 ≤ U.card := by
  by_contra hlt
  obtain ⟨z, hz⟩ := exists_dominator_of_card_le hG (by omega : U.card ≤ n)
  exact not_dominates_of_dominatesAllSubsets_one hG.1 hU z hz

/-- Local tournament averaging: inside any nonempty subset `U` of a tournament `G` on `Fin N`,
there exists a vertex `v ∈ U` with `2 * (U.filter (fun w => G.Adj w v)).card + 1 ≤ U.card`. -/
theorem exists_vertex_in_subset_inDegree_le {N : ℕ} {G : Digraph (Fin N)}
    (hG : IsTournament G) {U : Finset (Fin N)} (hU : U.Nonempty) :
    ∃ v ∈ U, 2 * (U.filter (fun w => G.Adj w v)).card + 1 ≤ U.card := by
  have hpos : 1 ≤ U.card := Finset.Nonempty.card_pos hU
  let g : Fin U.card ↪ Fin N := embOfCardLe (le_refl U.card)
  obtain ⟨i, hi⟩ := exists_vertex_inNeigh_card_le (isTournament_comap hG g) hpos
  let v : Fin N := g i
  have hvU : v ∈ U := embOfCardLe_mem (le_refl U.card) i
  have hsub_U : (Finset.univ : Finset (Fin U.card)).map g = U :=
    Finset.eq_of_subset_of_card_le
      (fun x hx => by
        rcases Finset.mem_map.mp hx with ⟨j, _, rfl⟩
        exact embOfCardLe_mem (le_refl U.card) j)
      (by simp)
  have hcard_eq : (U.filter (fun w => G.Adj w v)).card = (inNeigh (comapDigraph G g) i).card := by
    have hmap : (inNeigh (comapDigraph G g) i).map g = U.filter (fun w => G.Adj w v) := by
      ext w
      rw [Finset.mem_filter, Finset.mem_map]
      refine ⟨fun ⟨j, hj, hjw⟩ => ?_, fun ⟨hwU, hadj⟩ => ?_⟩
      · rw [← hjw]
        exact ⟨embOfCardLe_mem (le_refl U.card) j,
          (comapDigraph_adj G g j i).mp (mem_inNeigh_iff.mp hj)⟩
      · rw [← hsub_U] at hwU
        rcases Finset.mem_map.mp hwU with ⟨j, _, rfl⟩
        exact ⟨j, mem_inNeigh_iff.mpr hadj, rfl⟩
    rw [← hmap, Finset.card_map]
  refine ⟨v, hvU, ?_⟩
  omega

/-- Szekeres–Szekeres (1965) inductive step: if `k + 1 ≤ N` and `DominatesAllSubsets G (k + 1) U`,
then for every `v : Fin N`, the restricted set `U.filter (fun w => G.Adj w v)` satisfies
`DominatesAllSubsets G k (U.filter (fun w => G.Adj w v))`. -/
theorem dominatesAllSubsets_filter_of_succ {k N : ℕ} {G : Digraph (Fin N)}
    (hk : k + 1 ≤ N) {U : Finset (Fin N)} (hU : DominatesAllSubsets G (k + 1) U)
    (v : Fin N) :
    DominatesAllSubsets G k (U.filter (fun w => G.Adj w v)) := by
  intro S hScard
  by_cases hvS : v ∈ S
  · have hdiff : 1 ≤ (Finset.univ \ S).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hdiff
    have hdisj : Disjoint S R :=
      Finset.disjoint_left.mpr (fun x hxS hxR => (Finset.mem_sdiff.mp (hRsub hxR)).2 hxS)
    have hcard_union : (S ∪ R).card = k + 1 := by
      rw [Finset.card_union_of_disjoint hdisj, hScard, hRcard]
    obtain ⟨w, hwU, hwdom⟩ := hU (S ∪ R) hcard_union
    have hwS : Dominates G w S := dominates_subset hwdom Finset.subset_union_left
    exact ⟨w, Finset.mem_filter.mpr ⟨hwU, hwS v hvS⟩, hwS⟩
  · have hcard_ins : (insert v S).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hvS, hScard]
    obtain ⟨w, hwU, hwdom⟩ := hU (insert v S) hcard_ins
    have hw_pair := (dominates_insert_iff G w v S).mp hwdom
    exact ⟨w, Finset.mem_filter.mpr ⟨hwU, hw_pair.1⟩, hw_pair.2⟩

/-- Szekeres–Szekeres (1965) absorptive-set lower bound: in any `n`-paradoxical tournament `G` on
`Fin N`, for every `m` with `m + 1 ≤ n` and every `U` satisfying `DominatesAllSubsets G (m + 1) U`,
we have `(n + 2) * 2 ^ m - 1 ≤ U.card`. -/
theorem card_ge_szekeres_of_dominatesAllSubsets {n N : ℕ} {G : Digraph (Fin N)}
    (hG : IsParadoxicalTournament n G) :
    ∀ m : ℕ, m + 1 ≤ n → ∀ U : Finset (Fin N),
      DominatesAllSubsets G (m + 1) U → (n + 2) * 2 ^ m - 1 ≤ U.card
  | 0, _, U, hU => by
    have h1 := card_ge_succ_of_dominatesAllSubsets_one hG hU
    simp only [pow_zero, mul_one]
    omega
  | m + 1, hm, U, hU => by
    have hnN : n ≤ N := by simpa using hG.2.1
    have hmN : m + 2 ≤ (Finset.univ : Finset (Fin N)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨S₀, _, hS₀card⟩ := Finset.exists_subset_card_eq hmN
    obtain ⟨w₀, hw₀U, _⟩ := hU S₀ hS₀card
    obtain ⟨v, _, hv_deg⟩ := exists_vertex_in_subset_inDegree_le hG.1 ⟨w₀, hw₀U⟩
    have hstep : DominatesAllSubsets G (m + 1) (U.filter (fun w => G.Adj w v)) :=
      dominatesAllSubsets_filter_of_succ (by omega) hU v
    have ih := card_ge_szekeres_of_dominatesAllSubsets hG m (by omega)
      (U.filter (fun w => G.Adj w v)) hstep
    have hpow : (n + 2) * 2 ^ (m + 1) = 2 * ((n + 2) * 2 ^ m) := by ring
    have hpos : 1 ≤ (n + 2) * 2 ^ m :=
      Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (by positivity))
    omega

/-- Unconditional proof of the Szekeres–Szekeres (1965) lower bound: for every `n ≥ 1`, any
`n`-paradoxical tournament on `Fin N` satisfies `(n + 2) * 2 ^ (n - 1) - 1 ≤ N`, `n * 2 ^ (n - 1) < N`,
and `SzekeresLowerBoundStatement` holds. -/
theorem szekeres_lower_bound_of_hasParadoxicalTournament (n N : ℕ) (hn : 1 ≤ n)
    (hN : HasParadoxicalTournament n N) :
    (n + 2) * 2 ^ (n - 1) - 1 ≤ N ∧ n * 2 ^ (n - 1) < N ∧ SzekeresLowerBoundStatement := by
  have hmain : ∀ k M : ℕ, 1 ≤ k → HasParadoxicalTournament k M →
      (k + 2) * 2 ^ (k - 1) - 1 ≤ M := by
    intro k M hk ⟨G, hG⟩
    have huniv : DominatesAllSubsets G (k - 1 + 1) Finset.univ := by
      rw [Nat.sub_add_cancel hk]
      intro S hScard
      obtain ⟨w, hw⟩ := hG.2.2 S hScard
      exact ⟨w, Finset.mem_univ w, hw⟩
    have hbound := card_ge_szekeres_of_dominatesAllSubsets hG (k - 1) (by omega) Finset.univ huniv
    simpa using hbound
  have h1 := hmain n N hn hN
  have hpow : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow (n - 1) 2 (by decide)
  have hmul : (n + 2) * 2 ^ (n - 1) = n * 2 ^ (n - 1) + 2 * 2 ^ (n - 1) := by ring
  refine ⟨h1, by omega, hmain⟩

/-- The 7-vertex Paley tournament `QR_7` on `Fin 7` (quadratic residues `{1, 2, 4} mod 7`). -/
def paley7Digraph : Digraph (Fin 7) where
  Adj u v :=
    let d := (v.val + 7 - u.val) % 7
    d = 1 ∨ d = 2 ∨ d = 4

/-- Exact characterization `HasParadoxicalTournament 2 N ↔ 7 ≤ N` and `f 2 = 7` via `paley7Digraph`
and the Szekeres–Szekeres / Erdős lower bound. -/
theorem paley7Digraph_dom2_and_f_two (N : ℕ) :
    (HasParadoxicalTournament 2 N ↔ 7 ≤ N) ∧ legacyF 2 = 7 := by
  have hpaley : IsParadoxicalTournament 2 paley7Digraph := by
    refine ⟨⟨by dsimp [paley7Digraph]; decide, by dsimp [paley7Digraph]; decide⟩, by decide, ?_⟩
    intro S hScard
    rcases Finset.card_eq_two.mp hScard with ⟨a, b, _, rfl⟩
    have hdom : ∀ x y : Fin 7, ∃ v : Fin 7, paley7Digraph.Adj v x ∧ paley7Digraph.Adj v y := by
      dsimp [paley7Digraph]
      decide
    obtain ⟨v, hva, hvb⟩ := hdom a b
    refine ⟨v, fun u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu2
    · exact hva
    · rw [Finset.mem_singleton.mp hu2]
      exact hvb
  have hex7 : HasParadoxicalTournament 2 7 := ⟨paley7Digraph, hpaley⟩
  have hiff : ∀ M : ℕ, HasParadoxicalTournament 2 M ↔ 7 ≤ M := by
    intro M
    refine ⟨fun hM => ?_, fun hM => hasParadoxicalTournament_mono_N hM hex7⟩
    have hlb := (erdos_lower_bound_of_hasParadoxicalTournament 2 M hM).1
    omega
  refine ⟨hiff N, le_antisymm (legacyF_le_of_hasParadoxicalTournament hex7) ?_⟩
  exact le_legacyF_of_forall_hasParadoxicalTournament hex7 (fun M hM => (hiff M).mp hM)

/-- Boolean test for the 9 nonzero quadratic residues `{1, 4, 5, 6, 7, 9, 11, 16, 17} mod 19`. -/
def isQR19 (d : ℕ) : Bool :=
  d == 1 || d == 4 || d == 5 || d == 6 || d == 7 || d == 9 || d == 11 || d == 16 || d == 17

/-- The 19-vertex Paley tournament `QR_19` on `Fin 19`. -/
def paley19Digraph : Digraph (Fin 19) where
  Adj u v := isQR19 ((v.val + 19 - u.val) % 19) = true

/-- Every triple `(a, b, c)` of vertices in `paley19Digraph` is simultaneously dominated by some
vertex `v : Fin 19` (proved by circulant translation reducing to `a = 0`). -/
theorem paley19Digraph_dom3_all (a b c : Fin 19) :
    ∃ v : Fin 19,
      paley19Digraph.Adj v a ∧ paley19Digraph.Adj v b ∧ paley19Digraph.Adj v c := by
  have hzero : ∀ x y : Fin 19, ∃ v : Fin 19,
      paley19Digraph.Adj v ⟨0, by decide⟩ ∧
      paley19Digraph.Adj v x ∧
      paley19Digraph.Adj v y := by
    dsimp [paley19Digraph]
    decide
  let b1 : Fin 19 := ⟨(b.val + 19 - a.val) % 19, by omega⟩
  let c1 : Fin 19 := ⟨(c.val + 19 - a.val) % 19, by omega⟩
  obtain ⟨v1, h0, hb, hc⟩ := hzero b1 c1
  refine ⟨⟨(v1.val + a.val) % 19, by omega⟩, ?_, ?_, ?_⟩
  · dsimp [paley19Digraph] at h0 ⊢
    have heq : (a.val + 19 - (v1.val + a.val) % 19) % 19 = (0 + 19 - v1.val) % 19 := by omega
    rw [heq]
    exact h0
  · dsimp [paley19Digraph, b1] at hb ⊢
    have heq : (b.val + 19 - (v1.val + a.val) % 19) % 19 =
        ((b.val + 19 - a.val) % 19 + 19 - v1.val) % 19 := by omega
    rw [heq]
    exact hb
  · dsimp [paley19Digraph, c1] at hc ⊢
    have heq : (c.val + 19 - (v1.val + a.val) % 19) % 19 =
        ((c.val + 19 - a.val) % 19 + 19 - v1.val) % 19 := by omega
    rw [heq]
    exact hc

/-- Szekeres–Szekeres (1965) exact evaluation `f 3 = 19` and universal threshold characterization
`HasParadoxicalTournament 3 N ↔ 19 ≤ N`. -/
theorem hasParadoxicalTournament_three_iff_and_f_three (N : ℕ) :
    (HasParadoxicalTournament 3 N ↔ 19 ≤ N) ∧ legacyF 3 = 19 := by
  have hpaley : IsParadoxicalTournament 3 paley19Digraph := by
    refine ⟨⟨by dsimp [paley19Digraph]; decide, by dsimp [paley19Digraph]; decide⟩, by decide, ?_⟩
    intro S hScard
    rcases Finset.card_eq_three.mp hScard with ⟨a, b, c, _, _, _, rfl⟩
    obtain ⟨v, hva, hvb, hvc⟩ := paley19Digraph_dom3_all a b c
    refine ⟨v, fun u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu2
    · exact hva
    · rcases Finset.mem_insert.mp hu2 with rfl | hu3
      · exact hvb
      · rw [Finset.mem_singleton.mp hu3]
        exact hvc
  have hex19 : HasParadoxicalTournament 3 19 := ⟨paley19Digraph, hpaley⟩
  have hiff : ∀ M : ℕ, HasParadoxicalTournament 3 M ↔ 19 ≤ M := by
    intro M
    refine ⟨fun hM => ?_, fun hM => hasParadoxicalTournament_mono_N hM hex19⟩
    have hlb := (szekeres_lower_bound_of_hasParadoxicalTournament 3 M (by decide) hM).1
    omega
  refine ⟨hiff N, le_antisymm (legacyF_le_of_hasParadoxicalTournament hex19) ?_⟩
  exact le_legacyF_of_forall_hasParadoxicalTournament hex19 (fun M hM => (hiff M).mp hM)

theorem isParadoxicalTournament_paley7Digraph : IsParadoxicalTournament 2 paley7Digraph := by
  refine ⟨⟨by dsimp [paley7Digraph]; decide, by dsimp [paley7Digraph]; decide⟩, by decide, ?_⟩
  intro S hScard
  rcases Finset.card_eq_two.mp hScard with ⟨a, b, _, rfl⟩
  have hdom : ∀ x y : Fin 7, ∃ v : Fin 7, paley7Digraph.Adj v x ∧ paley7Digraph.Adj v y := by
    dsimp [paley7Digraph]
    decide
  obtain ⟨v, hva, hvb⟩ := hdom a b
  exact ⟨v, fun u hu => by
    rcases Finset.mem_insert.mp hu with rfl | hu2
    · exact hva
    · rw [Finset.mem_singleton.mp hu2]
      exact hvb⟩

theorem isParadoxicalTournament_paley19Digraph : IsParadoxicalTournament 3 paley19Digraph := by
  refine ⟨⟨by dsimp [paley19Digraph]; decide, by dsimp [paley19Digraph]; decide⟩, by decide, ?_⟩
  intro S hScard
  rcases Finset.card_eq_three.mp hScard with ⟨a, b, c, _, _, _, rfl⟩
  obtain ⟨v, hva, hvb, hvc⟩ := paley19Digraph_dom3_all a b c
  exact ⟨v, fun u hu => by
    rcases Finset.mem_insert.mp hu with rfl | hu2
    · exact hva
    · rcases Finset.mem_insert.mp hu2 with rfl | hu3
      · exact hvb
      · rw [Finset.mem_singleton.mp hu3]
        exact hvc⟩

/-- Universal natural-number Bernoulli/binomial lower bound `(a + 1) ^ (m + 1) ≥ a ^ (m + 1) + (m + 1) * a ^ m`
and doubling corollary `2 * a ^ a ≤ (a + 1) ^ a` for `1 ≤ a`. -/
theorem bernoulli_nat_pow_bound (a m : ℕ) :
    a ^ (m + 1) + (m + 1) * a ^ m ≤ (a + 1) ^ (m + 1) ∧
      (1 ≤ a → 2 * a ^ a ≤ (a + 1) ^ a) := by
  have haux : ∀ b k : ℕ, b ^ (k + 1) + (k + 1) * b ^ k ≤ (b + 1) ^ (k + 1) := by
    intro b k
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_one, pow_zero, mul_one]
      omega
    | succ k ih =>
      calc
        b ^ (k + 2) + (k + 2) * b ^ (k + 1) ≤
            (b ^ (k + 1) + (k + 1) * b ^ k) * (b + 1) := by
          have hexp : (b ^ (k + 1) + (k + 1) * b ^ k) * (b + 1) =
              b ^ (k + 2) + (k + 2) * b ^ (k + 1) + (k + 1) * b ^ k := by ring
          omega
        _ ≤ (b + 1) ^ (k + 1) * (b + 1) := Nat.mul_le_mul_right (b + 1) ih
        _ = (b + 1) ^ (k + 2) := by ring
  refine ⟨haux a m, fun ha => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hk := haux (k + 1) k
  have hcomm : 1 + k = k + 1 := by omega
  rw [hcomm]
  calc
    2 * (k + 1) ^ (k + 1) = (k + 1) ^ (k + 1) + (k + 1) * (k + 1) ^ k := by ring
    _ ≤ (k + 1 + 1) ^ (k + 1) := hk

/-- Exponential decay step for Erdős's random tournament bound: for all `1 ≤ n` and `1 ≤ t`,
`2 ^ t * (2 ^ n - 1) ^ (t * 2 ^ n) < (2 ^ n) ^ (t * 2 ^ n)`. -/
theorem two_pow_mul_sub_one_pow_lt (n t : ℕ) (hn : 1 ≤ n) (ht : 1 ≤ t) :
    2 ^ t * (2 ^ n - 1) ^ (t * 2 ^ n) < (2 ^ n) ^ (t * 2 ^ n) := by
  have hpow2 : 2 ≤ 2 ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have : 2 ^ (1 + k) = 2 * 2 ^ k := by ring
    omega
  let a := 2 ^ n - 1
  have ha : 1 ≤ a := by omega
  have ha_succ : a + 1 = 2 ^ n := by omega
  have hbern := (bernoulli_nat_pow_bound a 0).2 ha
  rw [ha_succ] at hbern
  have hlt1 : 2 * a ^ (2 ^ n) < (2 ^ n) ^ (2 ^ n) := by
    have hpow_eq : a ^ (2 ^ n) = a ^ a * a := by
      rw [← pow_succ, ha_succ]
    have hpow2_eq : (2 ^ n) ^ (2 ^ n) = (2 ^ n) ^ a * 2 ^ n := by
      rw [← pow_succ, ha_succ]
    have hpos : 0 < (2 ^ n) ^ a := Nat.pos_of_ne_zero (by positivity)
    rw [hpow_eq, hpow2_eq]
    calc
      2 * (a ^ a * a) = (2 * a ^ a) * a := by ring
      _ ≤ (2 ^ n) ^ a * a := Nat.mul_le_mul_right a hbern
      _ < (2 ^ n) ^ a * 2 ^ n := Nat.mul_lt_mul_of_pos_left (by omega) hpos
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction k with
  | zero =>
    simpa [a] using hlt1
  | succ k ih =>
    have hpos_lhs : 0 < 2 * a ^ (2 ^ n) := by
      have : 0 < a ^ (2 ^ n) := Nat.pos_of_ne_zero (by positivity)
      omega
    have hmul : (2 ^ (1 + k) * a ^ ((1 + k) * 2 ^ n)) * (2 * a ^ (2 ^ n)) <
        (2 ^ n) ^ ((1 + k) * 2 ^ n) * (2 ^ n) ^ (2 ^ n) := by
      calc
        (2 ^ (1 + k) * a ^ ((1 + k) * 2 ^ n)) * (2 * a ^ (2 ^ n)) <
            (2 ^ n) ^ ((1 + k) * 2 ^ n) * (2 * a ^ (2 ^ n)) :=
          Nat.mul_lt_mul_of_pos_right ih hpos_lhs
        _ ≤ (2 ^ n) ^ ((1 + k) * 2 ^ n) * (2 ^ n) ^ (2 ^ n) :=
          Nat.mul_le_mul_left _ (le_of_lt hlt1)
    have hlhs : (2 ^ (1 + k) * a ^ ((1 + k) * 2 ^ n)) * (2 * a ^ (2 ^ n)) =
        2 ^ (1 + (k + 1)) * a ^ ((1 + (k + 1)) * 2 ^ n) := by
      have hadd : (1 + (k + 1)) * 2 ^ n = (1 + k) * 2 ^ n + 2 ^ n := by ring
      have h1 : 1 + (k + 1) = (1 + k) + 1 := by omega
      rw [hadd, pow_add, h1, pow_succ]
      ring
    have hrhs : (2 ^ n) ^ ((1 + k) * 2 ^ n) * (2 ^ n) ^ (2 ^ n) =
        (2 ^ n) ^ ((1 + (k + 1)) * 2 ^ n) := by
      have hadd : (1 + (k + 1)) * 2 ^ n = (1 + k) * 2 ^ n + 2 ^ n := by ring
      rw [hadd, pow_add]
    rw [hlhs, hrhs] at hmul
    exact hmul

/-- Universal binomial upper bound: `N.choose n ≤ N ^ n` for all `N, n : ℕ`. -/
theorem choose_le_pow_self (N n : ℕ) : N.choose n ≤ N ^ n := by
  have h1 : N.choose n ≤ N.descFactorial n := Nat.choose_le_descFactorial N n
  have h2 : N.descFactorial n ≤ N ^ n := Nat.descFactorial_le_pow N n
  exact le_trans h1 h2

/-- Erdős's (1963) `O(n^2 2^n)` upper-bound theorem: for all `1 ≤ n`, the explicit vertex count
`ErdosUpperBoundFormula n = n + 2 * n * (n + 1) * 2 ^ n` satisfies
`ErdosProbabilisticCriterion n (ErdosUpperBoundFormula n)` and
`ErdosUpperBoundFormula n ≤ 5 * n ^ 2 * 2 ^ n`. -/
theorem erdos_upper_bound_criterion_holds (n : ℕ) (hn : 1 ≤ n) :
    ErdosProbabilisticCriterion n (ErdosUpperBoundFormula n) ∧
      ErdosUpperBoundFormula n ≤ 5 * n ^ 2 * 2 ^ n := by
  have hquad : ∀ k : ℕ, 1 ≤ k → k + 2 * k * (k + 1) * 2 ^ k ≤ 2 ^ (2 * k + 2) := by
    intro k hk
    have hpoly : ∀ m : ℕ, 2 * (m + 1) * (m + 2) + 1 ≤ 4 * 2 ^ (m + 1) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        rcases m with _ | _ | m
        · decide
        · decide
        · have ihm := ih (m + 1) (by omega)
          calc
            2 * (m + 3) * (m + 4) + 1 ≤ 2 * (2 * (m + 2) * (m + 3) + 1) := by nlinarith
            _ ≤ 2 * (4 * 2 ^ (m + 2)) := Nat.mul_le_mul_left 2 ihm
            _ = 4 * 2 ^ (m + 3) := by ring
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hm := hpoly m
    have hcomm : 1 + m = m + 1 := by omega
    have hcomm2 : m + 1 + 1 = m + 2 := by omega
    rw [hcomm, hcomm2]
    have hpow_split : 2 ^ (2 * (m + 1) + 2) = (4 * 2 ^ (m + 1)) * 2 ^ (m + 1) := by ring
    have hlt_pow : m + 1 ≤ 2 ^ (m + 1) := le_of_lt (Nat.lt_two_pow_self)
    rw [hpow_split]
    nlinarith
  let N := ErdosUpperBoundFormula n
  let t := 2 * n * (n + 1)
  have ht : 1 ≤ t := by
    dsimp [t]
    nlinarith
  have hN_sub : N - n = t * 2 ^ n := by
    dsimp [N, ErdosUpperBoundFormula, t]
    omega
  have hN_le : N ≤ 2 ^ (2 * n + 2) := hquad n hn
  have hchoose_le : N.choose n ≤ 2 ^ t := by
    calc
      N.choose n ≤ N ^ n := choose_le_pow_self N n
      _ ≤ (2 ^ (2 * n + 2)) ^ n := Nat.pow_le_pow_left hN_le n
      _ = 2 ^ t := by
        rw [← pow_mul]
        congr 1
        dsimp [t]
        ring
  have hdecay := two_pow_mul_sub_one_pow_lt n t hn ht
  have hcrit : ErdosProbabilisticCriterion n N := by
    dsimp [ErdosProbabilisticCriterion]
    rw [hN_sub]
    calc
      N.choose n * (2 ^ n - 1) ^ (t * 2 ^ n) ≤ 2 ^ t * (2 ^ n - 1) ^ (t * 2 ^ n) :=
        Nat.mul_le_mul_right _ hchoose_le
      _ < (2 ^ n) ^ (t * 2 ^ n) := hdecay
  refine ⟨hcrit, ?_⟩
  dsimp [ErdosUpperBoundFormula]
  have hpow_ge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hn_sq : n ≤ n ^ 2 := by nlinarith
  have hterm1 : n ≤ n ^ 2 * 2 ^ n := by
    calc
      n ≤ n ^ 2 * 1 := by omega
      _ ≤ n ^ 2 * 2 ^ n := Nat.mul_le_mul_left (n ^ 2) hpow_ge
  have hterm2 : 2 * n * (n + 1) * 2 ^ n ≤ 4 * n ^ 2 * 2 ^ n :=
    Nat.mul_le_mul_right (2 ^ n) (by nlinarith)
  calc
    n + 2 * n * (n + 1) * 2 ^ n ≤ n ^ 2 * 2 ^ n + 4 * n ^ 2 * 2 ^ n :=
      Nat.add_le_add hterm1 hterm2
    _ = 5 * n ^ 2 * 2 ^ n := by ring

/-! ## Finite orientation-space bridge, the O(n² 2ⁿ) upper bound, and QR_67 -/

set_option maxRecDepth 200000

open scoped Classical BigOperators

/-!
# Erdős Problem 902: Finite Orientation-Space Bridge, the O(n² 2ⁿ) Upper Bound, and QR_67

This module builds on `Erdos902Unified435` to establish universally quantified structural theorems
and positive and negative controls for Erdős Problem #902 (Schütte's `n`-paradoxical tournament
problem):

1. **Finite Tournament Orientation Space and Bipartite Cross-Edge Decomposition:**
   - Parameterization of all `2 ^ Fintype.card (EdgeIdx N)` labeled tournaments on `Fin N` via
     boolean orientations `ω : EdgeIdx N → Bool` on strictly ordered pairs `EdgeIdx N`.
   - Explicit bijection `splitEquiv S` between `EdgeIdx N → Bool` and the product
     `(ComplVertex S → (SubVertex S → Bool)) × (RestEdge S → Bool)` separating cross-edges between
     `Sᶜ` and `S` from internal/external edges.
   - Bijection-derived edge partition `Fintype.card (EdgeIdx N) = S.card * (N - S.card) + Fintype.card (RestEdge S)`
     and exact fiber count of non-dominating orientations for every `S : Finset (Fin N)`:
     `(badOrientations S).card = 2 ^ (Fintype.card (EdgeIdx N) - S.card * (N - S.card)) * (2 ^ S.card - 1) ^ (N - S.card)`.

2. **Double-Counting Bridge from `ErdosProbabilisticCriterion` to `HasParadoxicalTournament` and Unconditional Bounds on `f n`:**
   - Exact `n`-subset sum `∑ S ∈ powersetCard n univ, (badOrientations S).card = N.choose n * (2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) * (2 ^ n - 1) ^ (N - n))`
     and union bound `((powersetCard n univ).biUnion badOrientations).card ≤ ...`.
   - Fiber-level non-domination characterization `not_exists_dominates_iff_toSplit`: a subset `S`
     has no dominator in `tournamentOfOrientation ω` exactly when every cross-edge profile
     `(toSplit S ω).1 v` for `v ∈ Sᶜ` differs from the all-`true` profile.
   - Main bridge theorem `hasParadoxicalTournament_of_erdosProbabilisticCriterion`: for all `n ≤ N`,
     `ErdosProbabilisticCriterion n N → HasParadoxicalTournament n N`.
   - Unconditional proof of Erdős's (1963) upper bound `legacyF n ≤ n + 2 * n * (n + 1) * 2 ^ n ≤ 5 * n ^ 2 * 2 ^ n`
     for all `1 ≤ n`, and the complete two-sided Erdős–Szekeres–Szekeres sandwich:
     `2 ^ (n + 1) - 1 ≤ legacyF n ∧ (n + 2) * 2 ^ (n - 1) - 1 ≤ legacyF n ∧ legacyF n ≤ n + 2 * n * (n + 1) * 2 ^ n ∧ legacyF n ≤ 5 * n ^ 2 * 2 ^ n`.

3. **Affine-Automorphism Verification of `paley67Digraph` (`QR_67`) and `47 ≤ legacyF 4 ≤ 67`:**
   - Formalization of the 67-vertex Paley tournament `paley67Digraph` (`QR_67`) and its affine
     automorphism invariance under translation and multiplication by quadratic residues mod 67.
   - Reduction of all $\binom{67}{4} = 766,480$ 4-subsets of `Fin 67` to pairs `(y, z)` normalized
     with `(0, 1)` fixed, proving `IsParadoxicalTournament 4 paley67Digraph`, `HasParadoxicalTournament 4 67`,
     and `47 ≤ legacyF 4 ∧ legacyF 4 ≤ 67` (matching OEIS A362137 `a(4) = 67`).
-/
/-- Strictly ordered vertex pairs `(u, v)` with `u < v` in `Fin N`, indexing the undirected edges of
the complete graph on `Fin N`. -/
abbrev EdgeIdx (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

/-- Boolean predicate testing whether an ordered edge `e : EdgeIdx N` crosses between `S` and `Sᶜ`. -/
def isCrossEdge {N : ℕ} (S : Finset (Fin N)) (e : EdgeIdx N) : Bool :=
  (decide (e.1.1 ∈ S)) != (decide (e.1.2 ∈ S))

/-- Subtype of edges in `EdgeIdx N` that do not cross between `S` and `Sᶜ` (both endpoints in `S` or
both endpoints in `Sᶜ`). -/
abbrev RestEdge {N : ℕ} (S : Finset (Fin N)) : Type :=
  {e : EdgeIdx N // isCrossEdge S e = false}

/-- Subtype of vertices in `Fin N` lying in the complement `Sᶜ`. -/
abbrev ComplVertex {N : ℕ} (S : Finset (Fin N)) : Type :=
  {v : Fin N // v ∈ Sᶜ}

/-- Subtype of vertices in `Fin N` lying in `S`. -/
abbrev SubVertex {N : ℕ} (S : Finset (Fin N)) : Type :=
  {u : Fin N // u ∈ S}

/-- Canonical tournament on `Fin N` associated to a boolean edge orientation `ω : EdgeIdx N → Bool`. -/
def tournamentOfOrientation {N : ℕ} (ω : EdgeIdx N → Bool) : Digraph (Fin N) where
  Adj u v :=
    if h : u < v then ω ⟨(u, v), h⟩ = true
    else if h' : v < u then ω ⟨(v, u), h'⟩ = false
    else False

/-- Every boolean orientation `ω : EdgeIdx N → Bool` defines a valid tournament on `Fin N`. -/
theorem isTournament_tournamentOfOrientation {N : ℕ} (ω : EdgeIdx N → Bool) :
    IsTournament (tournamentOfOrientation ω) := by
  refine ⟨fun v => by simp [tournamentOfOrientation], fun u v huv => ?_⟩
  dsimp [tournamentOfOrientation]
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · have hnot : ¬ v < u := asymm hlt
    rw [dif_pos hlt, dif_neg hnot, dif_pos hlt]
    cases ω ⟨(u, v), hlt⟩ <;> decide
  · exact (huv rfl).elim
  · have hnot : ¬ u < v := asymm hgt
    rw [dif_neg hnot, dif_pos hgt, dif_pos hgt]
    cases ω ⟨(v, u), hgt⟩ <;> decide


/-- Decomposition map sending an orientation `ω : EdgeIdx N → Bool` to its cross-edge bipartite
profile `ComplVertex S → (SubVertex S → Bool)` and residual edge profile `RestEdge S → Bool`. -/
def toSplit {N : ℕ} (S : Finset (Fin N)) (ω : EdgeIdx N → Bool) :
    (ComplVertex S → (SubVertex S → Bool)) × (RestEdge S → Bool) :=
  (fun v u =>
    if h : v.1 < u.1 then ω ⟨(v.1, u.1), h⟩
    else if h' : u.1 < v.1 then ! (ω ⟨(u.1, v.1), h'⟩)
    else false,
   fun e => ω e.1)

/-- Reconstruction map assembling an orientation `EdgeIdx N → Bool` from a cross-edge bipartite
profile and a residual edge profile. -/
def fromSplit {N : ℕ} (S : Finset (Fin N))
    (fg : (ComplVertex S → (SubVertex S → Bool)) × (RestEdge S → Bool)) (e : EdgeIdx N) : Bool :=
  if h1 : e.1.1 ∉ S ∧ e.1.2 ∈ S then
    fg.1 ⟨e.1.1, Finset.mem_compl.mpr h1.1⟩ ⟨e.1.2, h1.2⟩
  else if h2 : e.1.1 ∈ S ∧ e.1.2 ∉ S then
    ! (fg.1 ⟨e.1.2, Finset.mem_compl.mpr h2.2⟩ ⟨e.1.1, h2.1⟩)
  else
    fg.2 ⟨e, by
      dsimp [isCrossEdge]
      by_cases ha : e.1.1 ∈ S <;> by_cases hb : e.1.2 ∈ S
      · simp [ha, hb]
      · exact (h2 ⟨ha, hb⟩).elim
      · exact (h1 ⟨ha, hb⟩).elim
      · simp [ha, hb]⟩

/-- Left-inverse identity for the bipartite cross-edge decomposition `toSplit` and `fromSplit`. -/
theorem fromSplit_toSplit {N : ℕ} (S : Finset (Fin N)) (ω : EdgeIdx N → Bool) :
    fromSplit S (toSplit S ω) = ω := by
  funext e
  dsimp [fromSplit, toSplit]
  by_cases h1 : e.1.1 ∉ S ∧ e.1.2 ∈ S
  · rw [dif_pos h1, dif_pos e.2]
  · rw [dif_neg h1]
    by_cases h2 : e.1.1 ∈ S ∧ e.1.2 ∉ S
    · have hnot : ¬ e.1.2 < e.1.1 := asymm e.2
      rw [dif_pos h2, dif_neg hnot, dif_pos e.2, Bool.not_not]
    · rw [dif_neg h2]

/-- Right-inverse identity for the bipartite cross-edge decomposition `toSplit` and `fromSplit`. -/
theorem toSplit_fromSplit {N : ℕ} (S : Finset (Fin N))
    (fg : (ComplVertex S → (SubVertex S → Bool)) × (RestEdge S → Bool)) :
    toSplit S (fromSplit S fg) = fg := by
  rcases fg with ⟨f, g⟩
  refine Prod.ext (funext fun v => funext fun u => ?_) (funext fun e => ?_)
  · dsimp [toSplit, fromSplit]
    have hv : v.1 ∉ S := Finset.mem_compl.mp v.2
    have hu : u.1 ∈ S := u.2
    have hne : v.1 ≠ u.1 := fun h => hv (h ▸ hu)
    rcases lt_trichotomy v.1 u.1 with hlt | heq | hgt
    · have h1 : v.1 ∉ S ∧ u.1 ∈ S := ⟨hv, hu⟩
      rw [dif_pos hlt, dif_pos h1]
    · exact (hne heq).elim
    · have hnot : ¬ v.1 < u.1 := asymm hgt
      have h1 : ¬ (u.1 ∉ S ∧ v.1 ∈ S) := fun h => h.1 hu
      have h2 : u.1 ∈ S ∧ v.1 ∉ S := ⟨hu, hv⟩
      rw [dif_neg hnot, dif_pos hgt, dif_neg h1, dif_pos h2, Bool.not_not]
  · dsimp [toSplit, fromSplit]
    have he := e.2
    dsimp [isCrossEdge] at he
    have h1 : ¬ (e.1.1.1 ∉ S ∧ e.1.1.2 ∈ S) := by
      rintro ⟨ha, hb⟩
      simp [ha, hb] at he
    have h2 : ¬ (e.1.1.1 ∈ S ∧ e.1.1.2 ∉ S) := by
      rintro ⟨ha, hb⟩
      simp [ha, hb] at he
    rw [dif_neg h1, dif_neg h2]

/-- Equivalence decomposing the tournament orientation space `EdgeIdx N → Bool` relative to any
subset `S : Finset (Fin N)`. -/
def splitEquiv {N : ℕ} (S : Finset (Fin N)) :
    (EdgeIdx N → Bool) ≃ (ComplVertex S → (SubVertex S → Bool)) × (RestEdge S → Bool) where
  toFun := toSplit S
  invFun := fromSplit S
  left_inv := fromSplit_toSplit S
  right_inv := toSplit_fromSplit S

/-- Edge-partition cardinality identity: for every subset `S : Finset (Fin N)`, the total number
of edges `Fintype.card (EdgeIdx N)` splits as `S.card * (N - S.card) + Fintype.card (RestEdge S)`. -/
theorem card_edgeIdx_eq_cross_add_rest {N : ℕ} (S : Finset (Fin N)) :
    Fintype.card (EdgeIdx N) = S.card * (N - S.card) + Fintype.card (RestEdge S) ∧
      Fintype.card (RestEdge S) = Fintype.card (EdgeIdx N) - S.card * (N - S.card) := by
  have hcard := Fintype.card_congr (splitEquiv S)
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
    ← pow_mul, ← pow_add] at hcard
  have heq : Fintype.card (EdgeIdx N) = S.card * (N - S.card) + Fintype.card (RestEdge S) :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) hcard
  exact ⟨heq, by omega⟩

/-- For `v ∈ Sᶜ` and `u ∈ S`, `v` beats `u` in `tournamentOfOrientation ω` iff `(toSplit S ω).1 v u = true`. -/
theorem adj_tournamentOfOrientation_iff_toSplit {N : ℕ} (S : Finset (Fin N))
    (ω : EdgeIdx N → Bool) (v : ComplVertex S) (u : SubVertex S) :
    (tournamentOfOrientation ω).Adj v.1 u.1 ↔ (toSplit S ω).1 v u = true := by
  dsimp [tournamentOfOrientation, toSplit]
  have hv : v.1 ∉ S := Finset.mem_compl.mp v.2
  have hu : u.1 ∈ S := u.2
  have hne : v.1 ≠ u.1 := fun h => hv (h ▸ hu)
  rcases lt_trichotomy v.1 u.1 with hlt | heq | hgt
  · rw [dif_pos hlt, dif_pos hlt]
  · exact (hne heq).elim
  · have hnot : ¬ v.1 < u.1 := asymm hgt
    rw [dif_neg hnot, dif_pos hgt, dif_neg hnot, dif_pos hgt]
    cases ω ⟨(u.1, v.1), hgt⟩ <;> decide

/-- A vertex `v ∈ Sᶜ` dominates `S` in `tournamentOfOrientation ω` iff its cross-edge profile
`(toSplit S ω).1 v` is identically `true`. -/
theorem dominates_tournamentOfOrientation_iff_toSplit {N : ℕ} (S : Finset (Fin N))
    (ω : EdgeIdx N → Bool) (v : ComplVertex S) :
    Dominates (tournamentOfOrientation ω) v.1 S ↔ (toSplit S ω).1 v = (fun _ => true) := by
  rw [funext_iff]
  refine ⟨fun h u => (adj_tournamentOfOrientation_iff_toSplit S ω v u).mp (h u.1 u.2),
    fun h u hu => (adj_tournamentOfOrientation_iff_toSplit S ω v ⟨u, hu⟩).mpr (h ⟨u, hu⟩)⟩

/-- A subset `S : Finset (Fin N)` has no dominator in `tournamentOfOrientation ω` iff every vertex
`v ∈ Sᶜ` has a non-all-`true` cross-edge profile `(toSplit S ω).1 v ≠ (fun _ => true)`. -/
theorem not_exists_dominates_iff_toSplit {N : ℕ} (S : Finset (Fin N))
    (ω : EdgeIdx N → Bool) :
    (¬ ∃ v : Fin N, Dominates (tournamentOfOrientation ω) v S) ↔
      ∀ v : ComplVertex S, (toSplit S ω).1 v ≠ (fun _ => true) := by
  refine ⟨fun h v hv => h ⟨v.1, (dominates_tournamentOfOrientation_iff_toSplit S ω v).mpr hv⟩,
    fun h ⟨v, hv⟩ => ?_⟩
  have hnotMem : v ∉ S := notMem_of_dominates (isTournament_tournamentOfOrientation ω) hv
  have hv_compl : v ∈ Sᶜ := Finset.mem_compl.mpr hnotMem
  exact h ⟨v, hv_compl⟩ ((dominates_tournamentOfOrientation_iff_toSplit S ω ⟨v, hv_compl⟩).mp hv)

/-- The finset of boolean tournament orientations on `Fin N` in which `S` has no dominator. -/
def badOrientations {N : ℕ} (S : Finset (Fin N)) : Finset (EdgeIdx N → Bool) :=
  Finset.univ.filter (fun ω => ¬ ∃ v : Fin N, Dominates (tournamentOfOrientation ω) v S)

/-- Explicit equivalence between `{ω // ω ∈ badOrientations S}` and the product of non-dominating
cross-edge profiles with unconstrained residual edge orientations. -/
def badOrientationsEquiv {N : ℕ} (S : Finset (Fin N)) :
    {ω : EdgeIdx N → Bool // ω ∈ badOrientations S} ≃
      (ComplVertex S → {h : SubVertex S → Bool // h ≠ (fun _ => true)}) × (RestEdge S → Bool) :=
  calc
    {ω : EdgeIdx N → Bool // ω ∈ badOrientations S}
      ≃ {ω : EdgeIdx N → Bool // ∀ v : ComplVertex S, (splitEquiv S ω).1 v ≠ (fun _ => true)} := by
        refine Equiv.subtypeEquivRight (fun ω => ?_)
        rw [badOrientations, Finset.mem_filter, and_iff_right (Finset.mem_univ ω)]
        exact not_exists_dominates_iff_toSplit S ω
    _ ≃ {fg : (ComplVertex S → (SubVertex S → Bool)) × (RestEdge S → Bool) //
          ∀ v : ComplVertex S, fg.1 v ≠ (fun _ => true)} :=
        Equiv.subtypeEquiv (splitEquiv S) (fun _ => Iff.rfl)
    _ ≃ (ComplVertex S → {h : SubVertex S → Bool // h ≠ (fun _ => true)}) × (RestEdge S → Bool) :=
        { toFun := fun ⟨⟨f, g⟩, h⟩ => (fun v => ⟨f v, h v⟩, g)
          invFun := fun ⟨f, g⟩ => ⟨(fun v => (f v).1, g), fun v => (f v).2⟩
          left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }

/-- Exact fiber cardinality of non-dominating tournament orientations for any `S : Finset (Fin N)`:
`(badOrientations S).card = 2 ^ (Fintype.card (EdgeIdx N) - S.card * (N - S.card)) * (2 ^ S.card - 1) ^ (N - S.card)`. -/
theorem card_badOrientations {N : ℕ} (S : Finset (Fin N)) :
    (badOrientations S).card =
      2 ^ (Fintype.card (EdgeIdx N) - S.card * (N - S.card)) * (2 ^ S.card - 1) ^ (N - S.card) := by
  have hcard := Fintype.card_congr (badOrientationsEquiv S)
  rw [Fintype.card_coe] at hcard
  have hsub : Fintype.card {h : SubVertex S → Bool // h ≠ (fun _ => true)} = 2 ^ S.card - 1 := by
    have h1 := Fintype.card_subtype_compl (fun h : SubVertex S → Bool => h = (fun _ => true))
    have h2 : Fintype.card {h : SubVertex S → Bool // h = (fun _ => true)} = 1 :=
      Fintype.card_unique
    rw [h2, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at h1
    exact h1
  rw [Fintype.card_prod, Fintype.card_fun, hsub, Fintype.card_coe, Finset.card_compl,
    Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
    (card_edgeIdx_eq_cross_add_rest S).2, mul_comm] at hcard
  exact hcard

/-- Double-counting identity summing `(badOrientations S).card` over all `n`-element subsets of `Fin N`. -/
theorem sum_card_badOrientations (n N : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, (badOrientations S).card) =
      N.choose n *
        (2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) * (2 ^ n - 1) ^ (N - n)) := by
  have hcongr : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      (badOrientations S).card =
        2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) * (2 ^ n - 1) ^ (N - n) := by
    intro S hS
    rw [card_badOrientations S, (Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Union-bound inequality on the biUnion of `badOrientations S` over all `n`-subsets `S` of `Fin N`. -/
theorem card_biUnion_badOrientations_le (n N : ℕ) :
    (((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations).card ≤
      2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) *
        (N.choose n * (2 ^ n - 1) ^ (N - n)) := by
  calc
    (((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations).card ≤
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, (badOrientations S).card :=
      Finset.card_biUnion_le
    _ = N.choose n *
          (2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) * (2 ^ n - 1) ^ (N - n)) :=
      sum_card_badOrientations n N
    _ = 2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) *
          (N.choose n * (2 ^ n - 1) ^ (N - n)) := by ring




/-- Finite tournament space double-counting bridge: for all `n ≤ N`, if
`ErdosProbabilisticCriterion n N` (`\binom{N}{n}(2^n - 1)^{N-n} < (2^n)^{N-n}`) holds, then there
exists a boolean orientation `ω : EdgeIdx N → Bool` such that `tournamentOfOrientation ω` is
`n`-paradoxical, and hence `HasParadoxicalTournament n N` holds. -/
theorem hasParadoxicalTournament_of_erdosProbabilisticCriterion {n N : ℕ}
    (hnN : n ≤ N) (hcrit : ErdosProbabilisticCriterion n N) :
    (∃ ω : EdgeIdx N → Bool, IsParadoxicalTournament n (tournamentOfOrientation ω)) ∧
      HasParadoxicalTournament n N := by
  obtain ⟨S₀, _, hS₀card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N))) (by simpa using hnN)
  have hsplit := (card_edgeIdx_eq_cross_add_rest S₀).1
  rw [hS₀card] at hsplit
  have huniv_card : (Finset.univ : Finset (EdgeIdx N → Bool)).card =
      2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) * (2 ^ n) ^ (N - n) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, ← pow_mul, ← pow_add]
    congr 1
    omega
  let B := ((Finset.univ : Finset (Fin N)).powersetCard n).biUnion badOrientations
  have hB_le := card_biUnion_badOrientations_le n N
  have hpos : 0 < 2 ^ (Fintype.card (EdgeIdx N) - n * (N - n)) :=
    Nat.pos_of_ne_zero (by positivity)
  have hB_lt : B.card < (Finset.univ : Finset (EdgeIdx N → Bool)).card := by
    rw [huniv_card]
    exact lt_of_le_of_lt hB_le (Nat.mul_lt_mul_of_pos_left hcrit hpos)
  have hne : B ≠ Finset.univ := fun heq => by
    rw [heq] at hB_lt
    exact lt_irrefl _ hB_lt
  have hnonempty : (Finset.univ \ B).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hne (Finset.eq_univ_of_forall fun x => hsub (Finset.mem_univ x))
  obtain ⟨ω, hω⟩ := hnonempty
  have hnotB : ω ∉ B := (Finset.mem_sdiff.mp hω).2
  have hpar : IsParadoxicalTournament n (tournamentOfOrientation ω) := by
    refine ⟨isTournament_tournamentOfOrientation ω, by simpa using hnN, fun S hScard => ?_⟩
    by_contra hnotDom
    apply hnotB
    rw [Finset.mem_biUnion]
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hnotDom⟩⟩
  exact ⟨⟨ω, hpar⟩, ⟨tournamentOfOrientation ω, hpar⟩⟩

/-- Unconditional existence of an `n`-paradoxical tournament on `ErdosUpperBoundFormula n`
(`n + 2 * n * (n + 1) * 2 ^ n`) vertices for every `1 ≤ n`. -/
theorem hasParadoxicalTournament_erdosUpperBoundFormula (n : ℕ) (hn : 1 ≤ n) :
    HasParadoxicalTournament n (ErdosUpperBoundFormula n) := by
  have hcrit := (erdos_upper_bound_criterion_holds n hn).1
  have hnN : n ≤ ErdosUpperBoundFormula n := by
    dsimp [ErdosUpperBoundFormula]
    omega
  exact (hasParadoxicalTournament_of_erdosProbabilisticCriterion hnN hcrit).2

/-- Unconditional proof of Erdős's (1963) upper bound on `f n`: for every `1 ≤ n`,
`legacyF n ≤ n + 2 * n * (n + 1) * 2 ^ n` and `legacyF n ≤ 5 * n ^ 2 * 2 ^ n`. -/
theorem legacyF_le_erdosUpperBoundFormula (n : ℕ) (hn : 1 ≤ n) :
    legacyF n ≤ ErdosUpperBoundFormula n ∧
      legacyF n ≤ n + 2 * n * (n + 1) * 2 ^ n ∧
      legacyF n ≤ 5 * n ^ 2 * 2 ^ n := by
  have hex := hasParadoxicalTournament_erdosUpperBoundFormula n hn
  have hle : legacyF n ≤ ErdosUpperBoundFormula n := legacyF_le_of_hasParadoxicalTournament hex
  have h5 := (erdos_upper_bound_criterion_holds n hn).2
  exact ⟨hle, hle, le_trans hle h5⟩

/-- Complete unconditional two-sided Erdős–Szekeres–Szekeres sandwich for `f n` (`1 ≤ n`):
`2 ^ (n + 1) - 1 ≤ legacyF n`, `(n + 2) * 2 ^ (n - 1) - 1 ≤ legacyF n`, `legacyF n ≤ n + 2 * n * (n + 1) * 2 ^ n`,
and `legacyF n ≤ 5 * n ^ 2 * 2 ^ n`. -/
theorem erdos_szekeres_f_sandwich (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 1) - 1 ≤ legacyF n ∧
      (n + 2) * 2 ^ (n - 1) - 1 ≤ legacyF n ∧
      legacyF n ≤ n + 2 * n * (n + 1) * 2 ^ n ∧
      legacyF n ≤ 5 * n ^ 2 * 2 ^ n := by
  have hex := hasParadoxicalTournament_erdosUpperBoundFormula n hn
  have herd_lb := (legacyF_ge_erdos_lower_bound hex).1
  have hsz_lb : (n + 2) * 2 ^ (n - 1) - 1 ≤ legacyF n :=
    le_legacyF_of_forall_hasParadoxicalTournament hex
      (fun N hN => (szekeres_lower_bound_of_hasParadoxicalTournament n N hn hN).1)
  have hub := legacyF_le_erdosUpperBoundFormula n hn
  exact ⟨herd_lb, hsz_lb, hub.2.1, hub.2.2⟩

/-- Balanced binary-search predicate for the 33 nonzero quadratic residues modulo 67:
`{1, 4, 6, 9, 10, 14, 15, 16, 17, 19, 21, 22, 23, 24, 25, 26, 29, 33, 35, 36, 37, 39, 40, 47, 49, 54, 55, 56, 59, 60, 62, 64, 65}`. -/
def isQR67 (d : ℕ) : Bool :=
  if d < 29 then
    if d < 16 then
      if d < 9 then
        if d < 4 then (d == 1) else if d == 4 then true else (d == 6)
      else if d == 9 then true else
        if d < 14 then (d == 10) else if d == 14 then true else (d == 15)
    else if d == 16 then true else
      if d < 22 then
        if d < 19 then (d == 17) else if d == 19 then true else (d == 21)
      else if d == 22 then true else
        if d < 24 then (d == 23) else if d == 24 then true else
          if d < 26 then (d == 25) else (d == 26)
  else if d == 29 then true else
    if d < 47 then
      if d < 37 then
        if d < 35 then (d == 33) else if d == 35 then true else (d == 36)
      else if d == 37 then true else
        if d < 40 then (d == 39) else (d == 40)
    else if d == 47 then true else
      if d < 59 then
        if d < 55 then
          if d < 54 then (d == 49) else (d == 54)
        else if d == 55 then true else (d == 56)
      else if d == 59 then true else
        if d < 64 then
          if d < 62 then (d == 60) else (d == 62)
        else if d == 64 then true else (d == 65)

/-- The 67-vertex Paley tournament `QR_67` on `Fin 67`. -/
def paley67Digraph : Digraph (Fin 67) where
  Adj u v := isQR67 ((v.val + 67 - u.val) % 67) = true

/-- Skew-symmetry of `isQR67` modulo `67 \equiv 3 \pmod 4`: `0` is not a quadratic residue and
`67 - d` has the opposite residue character to `d` for all `1 ≤ d < 67`. -/
theorem isQR67_zero_and_compl :
    isQR67 0 = false ∧
      ∀ d ∈ List.range 67, d ≠ 0 → isQR67 (67 - d) = !isQR67 d := by
  decide

/-- `paley67Digraph` is a tournament on `Fin 67`. -/
theorem isTournament_paley67Digraph : IsTournament paley67Digraph := by
  refine ⟨fun v => ?_, fun u v huv => ?_⟩
  · dsimp [paley67Digraph]
    have h0 : (v.val + 67 - v.val) % 67 = 0 := by omega
    rw [h0, isQR67_zero_and_compl.1]
    decide
  · dsimp [paley67Digraph]
    have hval : u.val ≠ v.val := Fin.val_ne_of_ne huv
    let d := (v.val + 67 - u.val) % 67
    have hd_lt : d < 67 := Nat.mod_lt _ (by decide)
    have hd_ne : d ≠ 0 := by
      dsimp [d]
      omega
    have hsymm : (u.val + 67 - v.val) % 67 = 67 - d := by
      dsimp [d]
      omega
    have hcomp := isQR67_zero_and_compl.2 d (List.mem_range.mpr hd_lt) hd_ne
    change isQR67 d = true ↔ ¬ isQR67 ((u.val + 67 - v.val) % 67) = true
    rw [hsymm, hcomp]
    cases isQR67 d <;> decide

/-- Multiplicative invariance of `isQR67` under scaling by any quadratic residue `r ∈ QR_67`. -/
theorem isQR67_mul :
    ∀ r ∈ List.range 67, isQR67 r = true →
      ∀ x ∈ List.range 67, isQR67 ((r * x) % 67) = isQR67 x := by
  decide

/-- Every nonzero quadratic residue `d ∈ QR_67` has a multiplicative inverse `r ∈ QR_67` modulo 67. -/
theorem exists_qr67_inv :
    ∀ d ∈ List.range 67, isQR67 d = true →
      ∃ r ∈ List.range 67, isQR67 r = true ∧ (d * r) % 67 = 1 := by
  decide

/-- The 16 common dominators `{3, 8, 12, 13, 28, 31, 32, 42, 43, 44, 45, 46, 51, 52, 53, 58}` of
vertices `0` and `1` in `paley67Digraph`. -/
def dom01NatList67 : List ℕ := [3, 8, 12, 13, 28, 31, 32, 42, 43, 44, 45, 46, 51, 52, 53, 58]

/-- Every element `v ∈ dom01NatList67` lies in `0..66` and dominates both `0` and `1` in `paley67Digraph`. -/
theorem dom01NatList67_spec :
    ∀ v ∈ dom01NatList67,
      v < 67 ∧ isQR67 ((0 + 67 - v) % 67) = true ∧ isQR67 ((1 + 67 - v) % 67) = true := by
  decide

/-- Exhaustive finite verification on normalized pairs `(y, z)` (`z ≤ y < 67`) that `{0, 1, y, z}`
has a common dominator in `dom01NatList67`. -/
theorem paley67_dom01_check :
    ∀ y ∈ List.range 67,
      ∀ z ∈ List.range (y + 1),
        ∃ v ∈ dom01NatList67,
          isQR67 ((y + 67 - v) % 67) = true ∧
          isQR67 ((z + 67 - v) % 67) = true := by
  decide

/-- Modular distributivity of scaling over difference modulo 67 for `u, v < 67`. -/
theorem mod67_mul_sub_distribute (d u v : ℕ) (hu : u < 67) (hv : v < 67) :
    ((d * u) % 67 + 67 - (d * v) % 67) % 67 = (d * ((u + 67 - v) % 67)) % 67 := by
  have h1 : (d * ((u + 67 - v) % 67)) % 67 = (d * (u + 67 - v)) % 67 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [h1]
  have h2 : d * (u + 67 - v) = d * u + 67 * d - d * v := by
    have : v ≤ u + 67 := by omega
    rw [Nat.mul_sub_left_distrib, Nat.left_distrib]
    ring_nf
  rw [h2]
  have h3 : d * u = 67 * (d * u / 67) + (d * u) % 67 := (Nat.div_add_mod (d * u) 67).symm
  have h4 : d * v = 67 * (d * v / 67) + (d * v) % 67 := (Nat.div_add_mod (d * v) 67).symm
  have h5 : (d * u) % 67 < 67 := Nat.mod_lt _ (by decide)
  have h6 : (d * v) % 67 < 67 := Nat.mod_lt _ (by decide)
  have h7 : d * v ≤ d * u + 67 * d := by nlinarith
  omega

/-- Quadratic-residue scaling reduction: for any `d, c, e < 67` with `isQR67 d = true`, there exists
`v < 67` dominating `0, d, c, e` in `paley67Digraph`. -/
theorem paley67_dom0_qr (d c e : ℕ) (hd_lt : d < 67) (hc_lt : c < 67) (he_lt : e < 67)
    (hd_qr : isQR67 d = true) :
    ∃ v < 67,
      isQR67 ((0 + 67 - v) % 67) = true ∧
      isQR67 ((d + 67 - v) % 67) = true ∧
      isQR67 ((c + 67 - v) % 67) = true ∧
      isQR67 ((e + 67 - v) % 67) = true := by
  obtain ⟨r, hr_mem, hr_qr, hdr⟩ := exists_qr67_inv d (List.mem_range.mpr hd_lt) hd_qr
  let y := (r * c) % 67
  let z := (r * e) % 67
  have hy_lt : y < 67 := Nat.mod_lt _ (by decide)
  have hz_lt : z < 67 := Nat.mod_lt _ (by decide)
  have hdom01 : ∃ v₀ ∈ dom01NatList67,
      isQR67 ((y + 67 - v₀) % 67) = true ∧ isQR67 ((z + 67 - v₀) % 67) = true := by
    by_cases hyz : z ≤ y
    · exact paley67_dom01_check y (List.mem_range.mpr hy_lt) z (List.mem_range.mpr (by omega))
    · obtain ⟨v₀, hv₀, h1, h2⟩ :=
        paley67_dom01_check z (List.mem_range.mpr hz_lt) y (List.mem_range.mpr (by omega))
      exact ⟨v₀, hv₀, h2, h1⟩
  obtain ⟨v₀, hv₀_mem, hy_dom, hz_dom⟩ := hdom01
  obtain ⟨hv₀_lt, h0_dom, h1_dom⟩ := dom01NatList67_spec v₀ hv₀_mem
  let v := (d * v₀) % 67
  have hv_lt : v < 67 := Nat.mod_lt _ (by decide)
  have hscale : ∀ u : ℕ, u < 67 →
      isQR67 (((d * u) % 67 + 67 - v) % 67) = isQR67 ((u + 67 - v₀) % 67) := by
    intro u hu
    dsimp [v]
    rw [mod67_mul_sub_distribute d u v₀ hu hv₀_lt]
    exact isQR67_mul d (List.mem_range.mpr hd_lt) hd_qr ((u + 67 - v₀) % 67)
      (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have hdy : (d * y) % 67 = c := by
    dsimp [y]
    calc
      (d * ((r * c) % 67)) % 67 = (d * (r * c)) % 67 := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      _ = ((d * r) * c) % 67 := by rw [mul_assoc]
      _ = (((d * r) % 67) * (c % 67)) % 67 := Nat.mul_mod (d * r) c 67
      _ = (1 * c) % 67 := by rw [hdr, Nat.mod_eq_of_lt hc_lt]
      _ = c := by rw [one_mul, Nat.mod_eq_of_lt hc_lt]
  have hdz : (d * z) % 67 = e := by
    dsimp [z]
    calc
      (d * ((r * e) % 67)) % 67 = (d * (r * e)) % 67 := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      _ = ((d * r) * e) % 67 := by rw [mul_assoc]
      _ = (((d * r) % 67) * (e % 67)) % 67 := Nat.mul_mod (d * r) e 67
      _ = (1 * e) % 67 := by rw [hdr, Nat.mod_eq_of_lt he_lt]
      _ = e := by rw [one_mul, Nat.mod_eq_of_lt he_lt]
  have hd0 : (d * 0) % 67 = 0 := by simp
  have hd1 : (d * 1) % 67 = d := by rw [mul_one, Nat.mod_eq_of_lt hd_lt]
  refine ⟨v, hv_lt, ?_, ?_, ?_, ?_⟩
  · have := hscale 0 (by decide)
    rw [hd0, h0_dom] at this
    exact this
  · have := hscale 1 (by decide)
    rw [hd1, h1_dom] at this
    exact this
  · have := hscale y hy_lt
    rw [hdy, hy_dom] at this
    exact this
  · have := hscale z hz_lt
    rw [hdz, hz_dom] at this
    exact this

/-- Circulant translation reduction on `paley67Digraph`: for any 4 vertices `a, b, c, e : Fin 67`
with `paley67Digraph.Adj a b`, there exists `v : Fin 67` dominating `a, b, c, e`. -/
theorem paley67Digraph_dom4_of_adj (a b c e : Fin 67) (hab : paley67Digraph.Adj a b) :
    ∃ v : Fin 67,
      paley67Digraph.Adj v a ∧
      paley67Digraph.Adj v b ∧
      paley67Digraph.Adj v c ∧
      paley67Digraph.Adj v e := by
  let d := (b.val + 67 - a.val) % 67
  let c' := (c.val + 67 - a.val) % 67
  let e' := (e.val + 67 - a.val) % 67
  have hd_lt : d < 67 := Nat.mod_lt _ (by decide)
  have hc_lt : c' < 67 := Nat.mod_lt _ (by decide)
  have he_lt : e' < 67 := Nat.mod_lt _ (by decide)
  obtain ⟨v₁, hv₁_lt, h0, hd, hc, he⟩ := paley67_dom0_qr d c' e' hd_lt hc_lt he_lt hab
  refine ⟨⟨(v₁ + a.val) % 67, Nat.mod_lt _ (by decide)⟩, ?_, ?_, ?_, ?_⟩
  · dsimp [paley67Digraph]
    have heq : (a.val + 67 - (v₁ + a.val) % 67) % 67 = (0 + 67 - v₁) % 67 := by omega
    rw [heq]
    exact h0
  · dsimp [paley67Digraph]
    have heq : (b.val + 67 - (v₁ + a.val) % 67) % 67 = (d + 67 - v₁) % 67 := by
      dsimp [d]
      omega
    rw [heq]
    exact hd
  · dsimp [paley67Digraph]
    have heq : (c.val + 67 - (v₁ + a.val) % 67) % 67 = (c' + 67 - v₁) % 67 := by
      dsimp [c']
      omega
    rw [heq]
    exact hc
  · dsimp [paley67Digraph]
    have heq : (e.val + 67 - (v₁ + a.val) % 67) % 67 = (e' + 67 - v₁) % 67 := by
      dsimp [e']
      omega
    rw [heq]
    exact he

/-- `paley67Digraph` (`QR_67`) is a `4`-paradoxical tournament on `Fin 67`. -/
theorem isParadoxicalTournament_paley67Digraph :
    IsParadoxicalTournament 4 paley67Digraph := by
  refine ⟨isTournament_paley67Digraph, by decide, ?_⟩
  intro S hScard
  obtain ⟨a, T, haT, rfl, hTcard⟩ := Finset.card_eq_succ.mp hScard
  rcases Finset.card_eq_three.mp hTcard with ⟨b, c, e, _, _, _, rfl⟩
  have hab_ne : a ≠ b := by
    rintro rfl
    exact haT (Finset.mem_insert_self a _)
  have hdom4 : ∃ v : Fin 67,
      paley67Digraph.Adj v a ∧
      paley67Digraph.Adj v b ∧
      paley67Digraph.Adj v c ∧
      paley67Digraph.Adj v e := by
    by_cases hab : paley67Digraph.Adj a b
    · exact paley67Digraph_dom4_of_adj a b c e hab
    · have hba : paley67Digraph.Adj b a := by
        by_contra hnot
        exact hab ((isTournament_paley67Digraph.2 a b hab_ne).mpr hnot)
      obtain ⟨v, hvb, hva, hvc, hve⟩ := paley67Digraph_dom4_of_adj b a c e hba
      exact ⟨v, hva, hvb, hvc, hve⟩
  obtain ⟨v, hva, hvb, hvc, hve⟩ := hdom4
  refine ⟨v, fun u hu => ?_⟩
  rcases Finset.mem_insert.mp hu with rfl | hu1
  · exact hva
  · rcases Finset.mem_insert.mp hu1 with rfl | hu2
    · exact hvb
    · rcases Finset.mem_insert.mp hu2 with rfl | hu3
      · exact hvc
      · rw [Finset.mem_singleton.mp hu3]
        exact hve

/-- Constructive Paley upper bound `HasParadoxicalTournament 4 67` and two-sided interval
`47 ≤ legacyF 4 ∧ legacyF 4 ≤ 67` (matching OEIS A362137 `a(4) = 67` and Szekeres–Szekeres lower bound 47). -/
theorem hasParadoxicalTournament_four_67_and_f_four_bounds :
    HasParadoxicalTournament 4 67 ∧ 47 ≤ legacyF 4 ∧ legacyF 4 ≤ 67 := by
  have hex67 : HasParadoxicalTournament 4 67 := ⟨paley67Digraph, isParadoxicalTournament_paley67Digraph⟩
  have hub : legacyF 4 ≤ 67 := legacyF_le_of_hasParadoxicalTournament hex67
  have hlb : 47 ≤ legacyF 4 := by
    have hsz := (erdos_szekeres_f_sandwich 4 (by decide)).2.1
    omega
  exact ⟨hex67, hlb, hub⟩


end Erdos902
end
