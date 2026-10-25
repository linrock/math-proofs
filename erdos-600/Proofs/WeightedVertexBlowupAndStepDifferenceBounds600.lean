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

public import Erdos600Unified435
public import NeighborhoodDegreeAndTriangleClusterBounds600
public import LinkGraphCycleDeficitAndTriangleCauchySchwarz600

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Topology Classical

namespace Erdos600

open SimpleGraph Finset Filter

/-!
# Weighted Vertex-Blowup Constructions, Common-Neighbor Weight-Sum Admissibility, Edge-Count Quadratic Forms, and Step-Difference Lower Bounds for Erdős #600

This module develops universally quantified (`∀`) structural theorems about weighted vertex
blow-ups of triangle-covered graphs for Erdős Problem #600:

1. **Weighted Vertex-Blowup Carrier, Graph Construction, and Fiber Structure (Section 1):**
   - Defines `BlowupVertex w = Σ u : α, Fin (w u)` and `weightedBlowupGraph H w = H.comap Sigma.fst`.
   - Proves exact vertex count `Fintype.card (BlowupVertex w) = ∑ u : α, w u`, fiber independence
     `¬ (weightedBlowupGraph H w).Adj ⟨u, i⟩ ⟨u, j⟩`, monotonicity in `H`, sigma-neighborhood
     decomposition `(weightedBlowupGraph H w).neighborFinset x = (H.neighborFinset x.1).sigma (fun _ ↦ Finset.univ)`,
     and exact vertex-degree formula `(weightedBlowupGraph H w).degree x = ∑ v ∈ H.neighborFinset x.1, w v`.

2. **Common-Neighbor Weight-Sum Bijection and Triangle Multiplicity in Weighted Blow-Ups (Section 2):**
   - Defines `commonNeighborWeightSum H w u v = ∑ t ∈ commonNeighborFinset H u v, w t`.
   - Establishes symmetry, additivity, weight monotonicity, positivity lower bounds, uniform upper bounds,
     the exact sigma bijection `commonNeighborFinset (weightedBlowupGraph H w) x y = (commonNeighborFinset H x.1 y.1).sigma (fun _ ↦ Finset.univ)`,
     and the exact triangle-multiplicity identity
     `((weightedBlowupGraph H w).trianglesContaining s(x, y)).card = commonNeighborWeightSum H w x.1 y.1`
     for every adjacent pair in `weightedBlowupGraph H w`.

3. **Common-Neighbor Weight-Sum Admissibility & Locally Linear / `r`-Book-Free Transfer (Section 3):**
   - Defines `IsAdmissibleBlowupWeight H w r` (`∀ u v, H.Adj u v → 1 ≤ commonNeighborWeightSum H w u v ∧ commonNeighborWeightSum H w u v < r`).
   - Proves `IsAdmissibleBlowupWeight H w r → IsAdmissibleBookFree (weightedBlowupGraph H w) r` and the
     exact equivalence under positive weights (`∀ u, 1 ≤ w u`).
   - Proves general bounded-weight transfer: if `IsAdmissibleBookFree H r` (`1 ≤ r`) and `1 ≤ w u ≤ k`,
     then `IsAdmissibleBookFree (weightedBlowupGraph H w) (k * (r - 1) + 1)`.
   - Specializing to locally linear base graphs (`IsAdmissibleBookFree H 2` / `H.LocallyLinear`), proves
     that any weight function satisfying `1 ≤ w u ≤ r - 1` produces an `r`-book-free weighted blow-up
     (`isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBookFree_two_of_le_sub_one`,
     `isAdmissibleBookFree_weightedBlowupGraph_of_locallyLinear_of_le_sub_one`).

4. **Edge-Count Quadratic Form and Unit-Plus-Increment Expansion (Section 4):**
   - Defines `edgeWeightProd w : Sym2 α → ℕ` via `Sym2.lift` and
     `blowupEdgeQuadraticForm H w = ∑ uv ∈ H.edgeFinset, edgeWeightProd w uv`.
   - Proves the exact edge-count identity `(weightedBlowupGraph H w).edgeFinset.card = blowupEdgeQuadraticForm H w`
     and the universal unit-plus-increment expansion
     `blowupEdgeQuadraticForm H (fun u ↦ 1 + δ u) = H.edgeFinset.card + (∑ u, δ u * H.degree u) + blowupEdgeQuadraticForm H δ`.

5. **Constructive Lower Bounds on `maxAdmissibleEdges`, `eFunction`, Uniform Scaling, and `stepDiff` (Section 5):**
   - Transports `weightedBlowupGraph H w` to `Fin n` via `Fintype.equivFinOfCardEq`, proving
     `blowupEdgeQuadraticForm H w ≤ maxAdmissibleEdges n r` and
     `blowupEdgeQuadraticForm H w + 1 ≤ eFunction n r` whenever `∑ u, w u ≤ n` and `IsAdmissibleBlowupWeight H w r`.
   - Proves universal uniform-blowup scaling `c ^ 2 * maxAdmissibleEdges m r ≤ maxAdmissibleEdges (c * m) (c * (r - 1) + 1)`
     and locally linear scaling `c ^ 2 * maxAdmissibleEdges m 2 ≤ maxAdmissibleEdges (c * m) (c + 1)`
     (in particular `4 * maxAdmissibleEdges m 2 ≤ maxAdmissibleEdges (2 * m) 3` and
     `9 * maxAdmissibleEdges m 2 ≤ maxAdmissibleEdges (3 * m) 4`).
   - Proves constructive step-difference lower bounds
     `blowupEdgeQuadraticForm H w - maxAdmissibleEdges n r ≤ stepDiff n r`,
     `blowupEdgeQuadraticForm H w - (n * (n + r - 1)) / 4 ≤ stepDiff n r`, and
     `blowupEdgeQuadraticForm H w - n * ((n - 1) / 2) ≤ stepDiff n 2`, plus the conditional asymptotic
     reduction `tendsto_step_diff_atTop_of_exists_weightedBlowup` and `erdos_600_parts_i_of_forall_exists_weightedBlowup`.

6. **Positive and Negative Controls on $K_3$ Weighted Blow-Ups (Section 6):**
   - Establishes universal formulas for `commonNeighborWeightSum` and `blowupEdgeQuadraticForm` on
     `⊤ : SimpleGraph (Fin 3)` for arbitrary weights `w : Fin 3 → ℕ`, and certifies the diamond-graph
     control `k3Weight211 = ![2, 1, 1]` (5 edges on 4 vertices, admissible for `r = 3`, inadmissible for `r = 2`)
     and zero-weight degeneracy control `k3Weight011 = ![0, 1, 1]` (inadmissible for all `r`).
-/

section WeightedVertexBlowupAndStepDifferenceBounds

/-! ## Section 1: Weighted Vertex-Blowup Carrier, Graph Construction, and Fiber Structure -/

/-- The vertex carrier of the weighted blow-up of a base type `α` by `w : α → ℕ`, sending each
base vertex `u : α` to a fiber `Fin (w u)` of size `w u`. -/
abbrev BlowupVertex {α : Type*} (w : α → ℕ) : Type _ :=
  Σ u : α, Fin (w u)

theorem card_blowupVertex {α : Type*} [Fintype α] (w : α → ℕ) :
    Fintype.card (BlowupVertex w) = ∑ u : α, w u := by
  simp [BlowupVertex, Fintype.card_sigma]

theorem card_blowupVertex_const {α : Type*} [Fintype α] (c : ℕ) :
    Fintype.card (BlowupVertex (fun _ : α ↦ c)) = c * Fintype.card α := by
  rw [card_blowupVertex, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

theorem card_blowupVertex_one_add {α : Type*} [Fintype α] (δ : α → ℕ) :
    Fintype.card (BlowupVertex (fun u : α ↦ 1 + δ u)) =
      Fintype.card α + ∑ u : α, δ u := by
  rw [card_blowupVertex, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.mul_one]

/-- The weighted vertex-blowup simple graph of `H : SimpleGraph α` with vertex weights `w : α → ℕ`:
two fiber vertices `x, y : BlowupVertex w` are adjacent iff their projections `x.1, y.1` are adjacent in `H`. -/
def weightedBlowupGraph {α : Type*} (H : SimpleGraph α) (w : α → ℕ) :
    SimpleGraph (BlowupVertex w) :=
  H.comap Sigma.fst

instance instDecidableRelWeightedBlowupGraphAdj {α : Type*} (H : SimpleGraph α) (w : α → ℕ)
    [DecidableRel H.Adj] : DecidableRel (weightedBlowupGraph H w).Adj := by
  intro x y
  change Decidable (H.Adj x.1 y.1)
  infer_instance

@[simp]
theorem weightedBlowupGraph_adj_iff {α : Type*} (H : SimpleGraph α) (w : α → ℕ)
    (x y : BlowupVertex w) :
    (weightedBlowupGraph H w).Adj x y ↔ H.Adj x.1 y.1 :=
  Iff.rfl

@[simp]
theorem weightedBlowupGraph_adj_mk_iff {α : Type*} (H : SimpleGraph α) (w : α → ℕ)
    (u v : α) (i : Fin (w u)) (j : Fin (w v)) :
    (weightedBlowupGraph H w).Adj ⟨u, i⟩ ⟨v, j⟩ ↔ H.Adj u v :=
  Iff.rfl

theorem weightedBlowupGraph_not_adj_same_fiber {α : Type*} (H : SimpleGraph α) (w : α → ℕ)
    (u : α) (i j : Fin (w u)) :
    ¬ (weightedBlowupGraph H w).Adj ⟨u, i⟩ ⟨u, j⟩ := by
  intro h
  exact H.ne_of_adj h rfl

theorem fst_ne_of_weightedBlowupGraph_adj {α : Type*} {H : SimpleGraph α} {w : α → ℕ}
    {x y : BlowupVertex w} (h : (weightedBlowupGraph H w).Adj x y) :
    x.1 ≠ y.1 :=
  H.ne_of_adj h

theorem weightedBlowupGraph_bot {α : Type*} (w : α → ℕ) :
    weightedBlowupGraph (⊥ : SimpleGraph α) w = ⊥ := by
  ext x y
  rfl

theorem weightedBlowupGraph_mono {α : Type*} {H₁ H₂ : SimpleGraph α} (w : α → ℕ)
    (h : H₁ ≤ H₂) :
    weightedBlowupGraph H₁ w ≤ weightedBlowupGraph H₂ w :=
  fun _ _ hadj ↦ h hadj

theorem sigma_univ_filter_fst_eq_sigma {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℕ) (s : Finset α) :
    (Finset.univ : Finset (BlowupVertex w)).filter (fun z ↦ z.1 ∈ s) =
      s.sigma (fun u ↦ (Finset.univ : Finset (Fin (w u)))) := by
  ext ⟨u, i⟩
  simp [Finset.mem_sigma]

theorem card_sigma_univ_eq_sum {α : Type*} (w : α → ℕ) (s : Finset α) :
    (s.sigma (fun u : α ↦ (Finset.univ : Finset (Fin (w u))))).card = ∑ u ∈ s, w u := by
  simp [Finset.card_sigma]

theorem neighborFinset_weightedBlowupGraph_eq_sigma {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) (x : BlowupVertex w) :
    (weightedBlowupGraph H w).neighborFinset x =
      (H.neighborFinset x.1).sigma (fun v ↦ (Finset.univ : Finset (Fin (w v)))) := by
  ext ⟨v, j⟩
  simp [SimpleGraph.mem_neighborFinset, weightedBlowupGraph_adj_iff, Finset.mem_sigma]

theorem degree_weightedBlowupGraph_eq_sum_neighborFinset {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) (x : BlowupVertex w) :
    (weightedBlowupGraph H w).degree x = ∑ v ∈ H.neighborFinset x.1, w v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_weightedBlowupGraph_eq_sigma, card_sigma_univ_eq_sum]

theorem degree_weightedBlowupGraph_mk_eq {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) (u : α) (i : Fin (w u)) :
    (weightedBlowupGraph H w).degree ⟨u, i⟩ = ∑ v ∈ H.neighborFinset u, w v :=
  degree_weightedBlowupGraph_eq_sum_neighborFinset H w ⟨u, i⟩

theorem degree_weightedBlowupGraph_const {α : Type*} [Fintype α]
    (H : SimpleGraph α) (c : ℕ) (x : BlowupVertex (fun _ : α ↦ c)) :
    (weightedBlowupGraph H (fun _ ↦ c)).degree x = c * H.degree x.1 := by
  rw [degree_weightedBlowupGraph_eq_sum_neighborFinset, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul, Nat.mul_comm]

/-! ## Section 2: Common-Neighbor Weight-Sum Bijection and Triangle Multiplicity in Weighted Blow-Ups -/

/-- Total weight of the common neighbors of `u` and `v` in the base graph `H`:
`commonNeighborWeightSum H w u v = ∑ t ∈ commonNeighborFinset H u v, w t`. -/
noncomputable def commonNeighborWeightSum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) (u v : α) : ℕ :=
  ∑ t ∈ commonNeighborFinset H u v, w t

theorem commonNeighborWeightSum_symm {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) (u v : α) :
    commonNeighborWeightSum H w u v = commonNeighborWeightSum H w v u := by
  unfold commonNeighborWeightSum
  rw [commonNeighborFinset_symm]

theorem commonNeighborWeightSum_bot {α : Type*} [Fintype α]
    (w : α → ℕ) (u v : α) :
    commonNeighborWeightSum (⊥ : SimpleGraph α) w u v = 0 := by
  unfold commonNeighborWeightSum
  rw [commonNeighborFinset_bot, Finset.sum_empty]

theorem commonNeighborWeightSum_zero {α : Type*} [Fintype α]
    (H : SimpleGraph α) (u v : α) :
    commonNeighborWeightSum H (fun _ ↦ 0) u v = 0 := by
  simp [commonNeighborWeightSum]

theorem commonNeighborWeightSum_one {α : Type*} [Fintype α]
    (H : SimpleGraph α) (u v : α) :
    commonNeighborWeightSum H (fun _ ↦ 1) u v = (commonNeighborFinset H u v).card := by
  simp [commonNeighborWeightSum]

theorem commonNeighborWeightSum_const {α : Type*} [Fintype α]
    (H : SimpleGraph α) (c : ℕ) (u v : α) :
    commonNeighborWeightSum H (fun _ ↦ c) u v = c * (commonNeighborFinset H u v).card := by
  rw [commonNeighborWeightSum, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem commonNeighborWeightSum_add {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w₁ w₂ : α → ℕ) (u v : α) :
    commonNeighborWeightSum H (fun t ↦ w₁ t + w₂ t) u v =
      commonNeighborWeightSum H w₁ u v + commonNeighborWeightSum H w₂ u v := by
  unfold commonNeighborWeightSum
  exact Finset.sum_add_distrib

theorem commonNeighborWeightSum_mono_weight {α : Type*} [Fintype α]
    (H : SimpleGraph α) {w₁ w₂ : α → ℕ} (hw : ∀ t : α, w₁ t ≤ w₂ t) (u v : α) :
    commonNeighborWeightSum H w₁ u v ≤ commonNeighborWeightSum H w₂ u v :=
  Finset.sum_le_sum (fun t _ ↦ hw t)

theorem card_commonNeighborFinset_le_commonNeighborWeightSum_of_pos
    {α : Type*} [Fintype α] (H : SimpleGraph α) {w : α → ℕ}
    (hpos : ∀ t : α, 1 ≤ w t) (u v : α) :
    (commonNeighborFinset H u v).card ≤ commonNeighborWeightSum H w u v := by
  rw [← commonNeighborWeightSum_one H u v]
  exact commonNeighborWeightSum_mono_weight H hpos u v

theorem commonNeighborWeightSum_le_mul_card_of_le
    {α : Type*} [Fintype α] (H : SimpleGraph α) {w : α → ℕ} {k : ℕ}
    (hle : ∀ t : α, w t ≤ k) (u v : α) :
    commonNeighborWeightSum H w u v ≤ k * (commonNeighborFinset H u v).card := by
  rw [← commonNeighborWeightSum_const H k u v]
  exact commonNeighborWeightSum_mono_weight H hle u v

theorem commonNeighborWeightSum_eq_weight_of_card_eq_one
    {α : Type*} [Fintype α] {H : SimpleGraph α} (w : α → ℕ) {u v t : α}
    (hcard : (commonNeighborFinset H u v).card = 1)
    (ht : t ∈ commonNeighborFinset H u v) :
    commonNeighborWeightSum H w u v = w t := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  rw [hz, Finset.mem_singleton] at ht
  subst ht
  rw [commonNeighborWeightSum, hz, Finset.sum_singleton]

theorem commonNeighborFinset_weightedBlowupGraph_eq_sigma
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) (x y : BlowupVertex w) :
    commonNeighborFinset (weightedBlowupGraph H w) x y =
      (commonNeighborFinset H x.1 y.1).sigma (fun t ↦ (Finset.univ : Finset (Fin (w t)))) := by
  ext ⟨t, k⟩
  simp [mem_commonNeighborFinset_iff, weightedBlowupGraph_adj_iff, Finset.mem_sigma]

theorem card_commonNeighborFinset_weightedBlowupGraph_eq_commonNeighborWeightSum
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) (x y : BlowupVertex w) :
    (commonNeighborFinset (weightedBlowupGraph H w) x y).card =
      commonNeighborWeightSum H w x.1 y.1 := by
  rw [commonNeighborFinset_weightedBlowupGraph_eq_sigma, card_sigma_univ_eq_sum]
  rfl

theorem card_trianglesContaining_weightedBlowupGraph_eq_commonNeighborWeightSum
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) {x y : BlowupVertex w}
    (hadj : (weightedBlowupGraph H w).Adj x y) :
    ((weightedBlowupGraph H w).trianglesContaining s(x, y)).card =
      commonNeighborWeightSum H w x.1 y.1 := by
  rw [card_trianglesContaining_eq_card_commonNeighborFinset (weightedBlowupGraph H w) hadj,
    card_commonNeighborFinset_weightedBlowupGraph_eq_commonNeighborWeightSum]

theorem nonempty_trianglesContaining_weightedBlowupGraph_iff
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) {x y : BlowupVertex w}
    (hadj : (weightedBlowupGraph H w).Adj x y) :
    ((weightedBlowupGraph H w).trianglesContaining s(x, y)).Nonempty ↔
      1 ≤ commonNeighborWeightSum H w x.1 y.1 := by
  rw [← Finset.card_pos,
    card_trianglesContaining_weightedBlowupGraph_eq_commonNeighborWeightSum H w hadj]
  omega

/-! ## Section 3: Common-Neighbor Weight-Sum Admissibility & Locally Linear / `r`-Book-Free Transfer -/

/-- A weight function `w : α → ℕ` on a base graph `H` is `r`-admissible if for every edge
`H.Adj u v`, the common-neighbor weight sum satisfies `1 ≤ ∑_{t ∈ N_H(u) ∩ N_H(v)} w(t) < r`. -/
def IsAdmissibleBlowupWeight {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) (r : ℕ) : Prop :=
  ∀ u v : α, H.Adj u v →
    1 ≤ commonNeighborWeightSum H w u v ∧ commonNeighborWeightSum H w u v < r

theorem isAdmissibleBlowupWeight_iff_le_sub_one
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) {r : ℕ} (hr : 1 ≤ r) :
    IsAdmissibleBlowupWeight H w r ↔
      ∀ u v : α, H.Adj u v →
        1 ≤ commonNeighborWeightSum H w u v ∧ commonNeighborWeightSum H w u v ≤ r - 1 := by
  unfold IsAdmissibleBlowupWeight
  refine ⟨fun h u v huv ↦ ?_, fun h u v huv ↦ ?_⟩
  · have := h u v huv
    omega
  · have := h u v huv
    omega

theorem isAdmissibleBlowupWeight_mono
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r₁ r₂ : ℕ}
    (hr : r₁ ≤ r₂) (h : IsAdmissibleBlowupWeight H w r₁) :
    IsAdmissibleBlowupWeight H w r₂ := by
  intro u v huv
  obtain ⟨hge, hlt⟩ := h u v huv
  exact ⟨hge, Nat.lt_of_lt_of_le hlt hr⟩

theorem isAdmissibleBlowupWeight_bot
    {α : Type*} [Fintype α] (w : α → ℕ) (r : ℕ) :
    IsAdmissibleBlowupWeight (⊥ : SimpleGraph α) w r := by
  intro _ _ hadj
  exact False.elim hadj

theorem isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBlowupWeight
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r : ℕ}
    (hw : IsAdmissibleBlowupWeight H w r) :
    IsAdmissibleBookFree (weightedBlowupGraph H w) r := by
  rw [isAdmissibleBookFree_iff_commonNeighborFinset]
  refine ⟨fun x y hxy ↦ ?_, fun x y hxy ↦ ?_⟩
  · rw [← Finset.card_pos,
      card_commonNeighborFinset_weightedBlowupGraph_eq_commonNeighborWeightSum]
    exact (hw x.1 y.1 hxy).1
  · rw [card_commonNeighborFinset_weightedBlowupGraph_eq_commonNeighborWeightSum]
    exact (hw x.1 y.1 hxy).2

theorem isAdmissibleBlowupWeight_of_isAdmissibleBookFree_weightedBlowupGraph_of_pos
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r : ℕ}
    (hpos : ∀ u : α, 1 ≤ w u)
    (hG : IsAdmissibleBookFree (weightedBlowupGraph H w) r) :
    IsAdmissibleBlowupWeight H w r := by
  rw [isAdmissibleBookFree_iff_commonNeighborFinset] at hG
  intro u v huv
  let x : BlowupVertex w := ⟨u, ⟨0, hpos u⟩⟩
  let y : BlowupVertex w := ⟨v, ⟨0, hpos v⟩⟩
  have hxy : (weightedBlowupGraph H w).Adj x y := huv
  have hne : 0 < (commonNeighborFinset (weightedBlowupGraph H w) x y).card :=
    Finset.card_pos.mpr (hG.1 x y hxy)
  have hlt := hG.2 x y hxy
  rw [card_commonNeighborFinset_weightedBlowupGraph_eq_commonNeighborWeightSum] at hne hlt
  exact ⟨hne, hlt⟩

theorem isAdmissibleBookFree_weightedBlowupGraph_iff_of_pos
    {α : Type*} [Fintype α] (H : SimpleGraph α) {w : α → ℕ} (r : ℕ)
    (hpos : ∀ u : α, 1 ≤ w u) :
    IsAdmissibleBookFree (weightedBlowupGraph H w) r ↔ IsAdmissibleBlowupWeight H w r :=
  ⟨isAdmissibleBlowupWeight_of_isAdmissibleBookFree_weightedBlowupGraph_of_pos hpos,
    isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBlowupWeight⟩

theorem isAdmissibleBlowupWeight_one_iff_isAdmissibleBookFree
    {α : Type*} [Fintype α] (H : SimpleGraph α) (r : ℕ) :
    IsAdmissibleBlowupWeight H (fun _ ↦ 1) r ↔ IsAdmissibleBookFree H r := by
  rw [isAdmissibleBookFree_iff_commonNeighborFinset]
  unfold IsAdmissibleBlowupWeight
  refine ⟨fun h ↦ ⟨fun u v huv ↦ ?_, fun u v huv ↦ ?_⟩, fun h u v huv ↦ ?_⟩
  · rw [← Finset.card_pos, ← commonNeighborWeightSum_one]
    exact (h u v huv).1
  · rw [← commonNeighborWeightSum_one]
    exact (h u v huv).2
  · rw [commonNeighborWeightSum_one]
    exact ⟨Finset.card_pos.mpr (h.1 u v huv), h.2 u v huv⟩

theorem isAdmissibleBlowupWeight_of_isAdmissibleBookFree_of_bounds
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r k : ℕ}
    (hr : 1 ≤ r) (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ k)
    (hH : IsAdmissibleBookFree H r) :
    IsAdmissibleBlowupWeight H w (k * (r - 1) + 1) := by
  rw [isAdmissibleBookFree_iff_commonNeighborFinset] at hH
  intro u v huv
  have hcard_pos : 1 ≤ (commonNeighborFinset H u v).card :=
    Finset.card_pos.mpr (hH.1 u v huv)
  have hcard_le : (commonNeighborFinset H u v).card ≤ r - 1 := by
    have := hH.2 u v huv
    omega
  have hlo := le_trans hcard_pos
    (card_commonNeighborFinset_le_commonNeighborWeightSum_of_pos H hpos u v)
  have hhi := le_trans (commonNeighborWeightSum_le_mul_card_of_le H hle u v)
    (Nat.mul_le_mul_left k hcard_le)
  exact ⟨hlo, Nat.lt_succ_of_le hhi⟩

theorem isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBookFree_of_bounds
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r k : ℕ}
    (hr : 1 ≤ r) (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ k)
    (hH : IsAdmissibleBookFree H r) :
    IsAdmissibleBookFree (weightedBlowupGraph H w) (k * (r - 1) + 1) :=
  isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBlowupWeight
    (isAdmissibleBlowupWeight_of_isAdmissibleBookFree_of_bounds hr hpos hle hH)

theorem isAdmissibleBlowupWeight_of_isAdmissibleBookFree_two_of_le_sub_one
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r : ℕ}
    (hr : 1 ≤ r) (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ r - 1)
    (hH : IsAdmissibleBookFree H 2) :
    IsAdmissibleBlowupWeight H w r := by
  have h := isAdmissibleBlowupWeight_of_isAdmissibleBookFree_of_bounds
    (by omega : 1 ≤ 2) hpos hle hH
  have heq : (r - 1) * (2 - 1) + 1 = r := by omega
  rwa [heq] at h

theorem isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBookFree_two_of_le_sub_one
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r : ℕ}
    (hr : 1 ≤ r) (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ r - 1)
    (hH : IsAdmissibleBookFree H 2) :
    IsAdmissibleBookFree (weightedBlowupGraph H w) r :=
  isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBlowupWeight
    (isAdmissibleBlowupWeight_of_isAdmissibleBookFree_two_of_le_sub_one hr hpos hle hH)

theorem isAdmissibleBookFree_weightedBlowupGraph_of_locallyLinear_of_le_sub_one
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r : ℕ}
    (hr : 1 ≤ r) (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ r - 1)
    (hH : H.LocallyLinear) :
    IsAdmissibleBookFree (weightedBlowupGraph H w) r :=
  isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBookFree_two_of_le_sub_one
    hr hpos hle ((locallyLinear_iff_trianglesContaining H).mp hH)

theorem isAdmissibleBookFree_three_weightedBlowupGraph_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ}
    (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ 2)
    (hH : IsAdmissibleBookFree H 2) :
    IsAdmissibleBookFree (weightedBlowupGraph H w) 3 :=
  isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBookFree_two_of_le_sub_one
    (by omega : 1 ≤ 3) hpos hle hH

theorem isAdmissibleBookFree_four_weightedBlowupGraph_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ}
    (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ 3)
    (hH : IsAdmissibleBookFree H 2) :
    IsAdmissibleBookFree (weightedBlowupGraph H w) 4 :=
  isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBookFree_two_of_le_sub_one
    (by omega : 1 ≤ 4) hpos hle hH

theorem card_commonNeighborFinset_eq_one_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2)
    {u v : α} (huv : G.Adj u v) :
    (commonNeighborFinset G u v).card = 1 := by
  rw [← card_trianglesContaining_eq_card_commonNeighborFinset G huv]
  exact card_trianglesContaining_eq_one_of_isAdmissibleBookFree_two
    hG (SimpleGraph.mem_edgeFinset.mpr huv)

theorem commonNeighborFinset_eq_singleton_of_mem_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2)
    {u v w : α} (huv : G.Adj u v) (hw : w ∈ commonNeighborFinset G u v) :
    commonNeighborFinset G v w = {u} := by
  rw [mem_commonNeighborFinset_iff] at hw
  have hcard : (commonNeighborFinset G v w).card = 1 :=
    card_commonNeighborFinset_eq_one_of_isAdmissibleBookFree_two hG hw.2
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hu : u ∈ commonNeighborFinset G v w := by
    rw [mem_commonNeighborFinset_iff]
    exact ⟨huv.symm, hw.1.symm⟩
  rw [hz, Finset.mem_singleton] at hu
  subst hu
  exact hz

theorem not_adj_and_adj_of_mem_commonNeighborFinset_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2)
    {u v w x : α} (huv : G.Adj u v) (hw : w ∈ commonNeighborFinset G u v) (hx : x ≠ u) :
    ¬ (G.Adj v x ∧ G.Adj w x) := by
  intro h
  have hmem : x ∈ commonNeighborFinset G v w := by
    rw [mem_commonNeighborFinset_iff]
    exact h
  rw [commonNeighborFinset_eq_singleton_of_mem_of_isAdmissibleBookFree_two hG huv hw,
    Finset.mem_singleton] at hmem
  exact hx hmem

theorem not_adj_of_mem_commonNeighborFinset_of_not_adj_of_isAdmissibleBookFree_two
    {α : Type*} [Fintype α] {G : SimpleGraph α} (hG : IsAdmissibleBookFree G 2)
    {u v x z : α} (huv : G.Adj u v) (hvx : G.Adj v x) (hux : ¬ G.Adj u x) (hne : x ≠ u)
    (hz : z ∈ commonNeighborFinset G v x) :
    z ≠ u ∧ ¬ G.Adj u z := by
  rw [mem_commonNeighborFinset_iff] at hz
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hux hz.2.symm
  · intro huz
    have hz_uv : z ∈ commonNeighborFinset G u v := by
      rw [mem_commonNeighborFinset_iff]
      exact ⟨huz, hz.1⟩
    exact not_adj_and_adj_of_mem_commonNeighborFinset_of_isAdmissibleBookFree_two
      hG huv hz_uv hne ⟨hvx, hz.2.symm⟩

/-! ## Section 4: Edge-Count Quadratic Form and Unit-Plus-Increment Expansion -/

/-- Well-defined product of vertex weights across an unordered pair `uv : Sym2 α`. -/
def edgeWeightProd {α : Type*} (w : α → ℕ) : Sym2 α → ℕ :=
  Sym2.lift ⟨fun u v ↦ w u * w v, fun u v ↦ Nat.mul_comm (w u) (w v)⟩

@[simp]
theorem edgeWeightProd_mk {α : Type*} (w : α → ℕ) (u v : α) :
    edgeWeightProd w s(u, v) = w u * w v :=
  rfl

/-- The edge-count quadratic form `∑_{uv ∈ E(H)} w(u) * w(v)` of a weighted vertex blow-up. -/
noncomputable def blowupEdgeQuadraticForm {α : Type*} [Fintype α]
    (H : SimpleGraph α) (w : α → ℕ) : ℕ :=
  ∑ uv ∈ H.edgeFinset, edgeWeightProd w uv

theorem blowupEdgeQuadraticForm_bot {α : Type*} [Fintype α] (w : α → ℕ) :
    blowupEdgeQuadraticForm (⊥ : SimpleGraph α) w = 0 := by
  simp [blowupEdgeQuadraticForm]

theorem blowupEdgeQuadraticForm_zero {α : Type*} [Fintype α] (H : SimpleGraph α) :
    blowupEdgeQuadraticForm H (fun _ ↦ 0) = 0 := by
  unfold blowupEdgeQuadraticForm
  refine Finset.sum_eq_zero (fun uv _ ↦ ?_)
  induction uv using Sym2.ind with
  | _ u v => rfl

theorem blowupEdgeQuadraticForm_one {α : Type*} [Fintype α] (H : SimpleGraph α) :
    blowupEdgeQuadraticForm H (fun _ ↦ 1) = H.edgeFinset.card := by
  unfold blowupEdgeQuadraticForm
  have h1 : ∀ uv ∈ H.edgeFinset, edgeWeightProd (fun _ : α ↦ 1) uv = 1 := by
    intro uv _
    induction uv using Sym2.ind with
    | _ u v => rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, Nat.mul_one]

theorem blowupEdgeQuadraticForm_const {α : Type*} [Fintype α] (H : SimpleGraph α) (c : ℕ) :
    blowupEdgeQuadraticForm H (fun _ ↦ c) = c ^ 2 * H.edgeFinset.card := by
  unfold blowupEdgeQuadraticForm
  have hc : ∀ uv ∈ H.edgeFinset, edgeWeightProd (fun _ : α ↦ c) uv = c ^ 2 := by
    intro uv _
    induction uv using Sym2.ind with
    | _ u v => exact (sq c).symm
  rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem blowupEdgeQuadraticForm_mono_weight {α : Type*} [Fintype α]
    (H : SimpleGraph α) {w₁ w₂ : α → ℕ} (hw : ∀ u : α, w₁ u ≤ w₂ u) :
    blowupEdgeQuadraticForm H w₁ ≤ blowupEdgeQuadraticForm H w₂ := by
  refine Finset.sum_le_sum (fun uv _ ↦ ?_)
  induction uv using Sym2.ind with
  | _ u v => exact Nat.mul_le_mul (hw u) (hw v)

theorem card_edgeFinset_le_blowupEdgeQuadraticForm_of_pos {α : Type*} [Fintype α]
    (H : SimpleGraph α) {w : α → ℕ} (hpos : ∀ u : α, 1 ≤ w u) :
    H.edgeFinset.card ≤ blowupEdgeQuadraticForm H w := by
  rw [← blowupEdgeQuadraticForm_one H]
  exact blowupEdgeQuadraticForm_mono_weight H hpos

theorem blowupEdgeQuadraticForm_le_sq_mul_card_edgeFinset_of_le {α : Type*} [Fintype α]
    (H : SimpleGraph α) {w : α → ℕ} {k : ℕ} (hle : ∀ u : α, w u ≤ k) :
    blowupEdgeQuadraticForm H w ≤ k ^ 2 * H.edgeFinset.card := by
  rw [← blowupEdgeQuadraticForm_const H k]
  exact blowupEdgeQuadraticForm_mono_weight H hle

theorem sum_neighborFinset_mul_weight_eq_twice_blowupEdgeQuadraticForm
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) :
    (∑ u : α, ∑ v ∈ H.neighborFinset u, w u * w v) =
      2 * blowupEdgeQuadraticForm H w := by
  simpa [blowupEdgeQuadraticForm, edgeWeightProd_mk] using
    sum_neighborFinset_eq_two_mul_sum_edgeFinset H (edgeWeightProd w)

theorem twice_card_edgeFinset_weightedBlowupGraph_eq
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) :
    2 * (weightedBlowupGraph H w).edgeFinset.card =
      2 * blowupEdgeQuadraticForm H w := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, Fintype.sum_sigma]
  have h1 : (∑ u : α, ∑ i : Fin (w u), (weightedBlowupGraph H w).degree ⟨u, i⟩) =
      ∑ u : α, ∑ v ∈ H.neighborFinset u, w u * w v := by
    refine Finset.sum_congr rfl (fun u _ ↦ ?_)
    have hdeg : (∑ i : Fin (w u), (weightedBlowupGraph H w).degree ⟨u, i⟩) =
        ∑ _i : Fin (w u), ∑ v ∈ H.neighborFinset u, w v := by
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      exact degree_weightedBlowupGraph_eq_sum_neighborFinset H w ⟨u, i⟩
    rw [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.mul_sum]
  rw [h1, sum_neighborFinset_mul_weight_eq_twice_blowupEdgeQuadraticForm]

theorem card_edgeFinset_weightedBlowupGraph_eq_blowupEdgeQuadraticForm
    {α : Type*} [Fintype α] (H : SimpleGraph α) (w : α → ℕ) :
    (weightedBlowupGraph H w).edgeFinset.card = blowupEdgeQuadraticForm H w := by
  have h := twice_card_edgeFinset_weightedBlowupGraph_eq H w
  omega

theorem card_edgeFinset_weightedBlowupGraph_const
    {α : Type*} [Fintype α] (H : SimpleGraph α) (c : ℕ) :
    (weightedBlowupGraph H (fun _ ↦ c)).edgeFinset.card = c ^ 2 * H.edgeFinset.card := by
  rw [card_edgeFinset_weightedBlowupGraph_eq_blowupEdgeQuadraticForm,
    blowupEdgeQuadraticForm_const]

theorem sum_edgeFinset_endpoint_sum_eq_sum_mul_degree
    {α : Type*} [Fintype α] (H : SimpleGraph α) (δ : α → ℕ) :
    (∑ uv ∈ H.edgeFinset,
      Sym2.lift ⟨fun u v ↦ δ u + δ v, fun u v ↦ Nat.add_comm (δ u) (δ v)⟩ uv) =
      ∑ u : α, δ u * H.degree u := by
  let f : Sym2 α → ℕ := Sym2.lift ⟨fun u v ↦ δ u + δ v, fun u v ↦ Nat.add_comm (δ u) (δ v)⟩
  have hdouble : (∑ u : α, ∑ v ∈ H.neighborFinset u, f s(u, v)) =
      2 * ∑ uv ∈ H.edgeFinset, f uv :=
    sum_neighborFinset_eq_two_mul_sum_edgeFinset H f
  have hsplit : (∑ u : α, ∑ v ∈ H.neighborFinset u, f s(u, v)) =
      (∑ u : α, ∑ _v ∈ H.neighborFinset u, δ u) +
        (∑ u : α, ∑ v ∈ H.neighborFinset u, δ v) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ ↦ ?_)
    rw [← Finset.sum_add_distrib]
    rfl
  have hleft : (∑ u : α, ∑ _v ∈ H.neighborFinset u, δ u) = ∑ u : α, δ u * H.degree u := by
    refine Finset.sum_congr rfl (fun u _ ↦ ?_)
    rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul, Nat.mul_comm]
  have hright : (∑ u : α, ∑ v ∈ H.neighborFinset u, δ v) = ∑ u : α, δ u * H.degree u := by
    have h1 : (∑ u : α, ∑ v ∈ H.neighborFinset u, δ v) =
        ∑ u : α, ∑ v : α, if H.Adj u v then δ v else 0 := by
      refine Finset.sum_congr rfl (fun u _ ↦ ?_)
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp [SimpleGraph.mem_neighborFinset]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ ↦ ?_)
    have h2 : (∑ u : α, if H.Adj u v then δ v else 0) =
        ∑ _u ∈ H.neighborFinset v, δ v := by
      rw [← Finset.sum_filter]
      congr 1
      ext u
      simp [SimpleGraph.mem_neighborFinset, H.adj_comm]
    rw [h2, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, smul_eq_mul, Nat.mul_comm]
  rw [hsplit, hleft, hright] at hdouble
  change ∑ uv ∈ H.edgeFinset, f uv = ∑ u : α, δ u * H.degree u
  omega

theorem blowupEdgeQuadraticForm_one_add_eq
    {α : Type*} [Fintype α] (H : SimpleGraph α) (δ : α → ℕ) :
    blowupEdgeQuadraticForm H (fun u ↦ 1 + δ u) =
      H.edgeFinset.card + (∑ u : α, δ u * H.degree u) + blowupEdgeQuadraticForm H δ := by
  unfold blowupEdgeQuadraticForm
  let f : Sym2 α → ℕ := Sym2.lift ⟨fun u v ↦ δ u + δ v, fun u v ↦ Nat.add_comm (δ u) (δ v)⟩
  have hpt : ∀ uv ∈ H.edgeFinset,
      edgeWeightProd (fun u ↦ 1 + δ u) uv = 1 + f uv + edgeWeightProd δ uv := by
    intro uv _
    induction uv using Sym2.ind with
    | _ u v =>
      change (1 + δ u) * (1 + δ v) = 1 + (δ u + δ v) + δ u * δ v
      ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, smul_eq_mul, Nat.mul_one, sum_edgeFinset_endpoint_sum_eq_sum_mul_degree]

theorem card_edgeFinset_weightedBlowupGraph_one_add_eq
    {α : Type*} [Fintype α] (H : SimpleGraph α) (δ : α → ℕ) :
    (weightedBlowupGraph H (fun u ↦ 1 + δ u)).edgeFinset.card =
      H.edgeFinset.card + (∑ u : α, δ u * H.degree u) + blowupEdgeQuadraticForm H δ := by
  rw [card_edgeFinset_weightedBlowupGraph_eq_blowupEdgeQuadraticForm,
    blowupEdgeQuadraticForm_one_add_eq]

/-! ## Section 5: Constructive Lower Bounds on `maxAdmissibleEdges`, `eFunction`, Uniform Scaling, and `stepDiff` -/

theorem exists_fin_graph_of_weightedBlowupGraph
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {n r : ℕ}
    (hn : (∑ u : α, w u) = n) (hw : IsAdmissibleBlowupWeight H w r) :
    ∃ G : SimpleGraph (Fin n),
      IsAdmissibleBookFree G r ∧ G.edgeFinset.card = blowupEdgeQuadraticForm H w := by
  have hcard : Fintype.card (BlowupVertex w) = n := by
    rw [card_blowupVertex, hn]
  let e : BlowupVertex w ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨(weightedBlowupGraph H w).map e.toEmbedding, ?_, ?_⟩
  · rw [isAdmissibleBookFree_map_iff]
    exact isAdmissibleBookFree_weightedBlowupGraph_of_isAdmissibleBlowupWeight hw
  · rw [card_edgeFinset_map_eq, card_edgeFinset_weightedBlowupGraph_eq_blowupEdgeQuadraticForm]

theorem blowupEdgeQuadraticForm_le_maxAdmissibleEdges_sum
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {r : ℕ}
    (hw : IsAdmissibleBlowupWeight H w r) :
    blowupEdgeQuadraticForm H w ≤ maxAdmissibleEdges (∑ u : α, w u) r := by
  obtain ⟨G, hG, hcard⟩ := exists_fin_graph_of_weightedBlowupGraph rfl hw
  rw [← hcard]
  exact card_edgeFinset_le_maxAdmissibleEdges_of_isAdmissibleBookFree hG

theorem blowupEdgeQuadraticForm_le_maxAdmissibleEdges_of_sum_le
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {n r : ℕ}
    (hn : (∑ u : α, w u) ≤ n) (hw : IsAdmissibleBlowupWeight H w r) :
    blowupEdgeQuadraticForm H w ≤ maxAdmissibleEdges n r :=
  le_trans (blowupEdgeQuadraticForm_le_maxAdmissibleEdges_sum hw)
    (maxAdmissibleEdges_mono_left hn r)

theorem succ_blowupEdgeQuadraticForm_le_eFunction_of_sum_le
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {n r : ℕ}
    (hn : (∑ u : α, w u) ≤ n) (hw : IsAdmissibleBlowupWeight H w r) :
    blowupEdgeQuadraticForm H w + 1 ≤ eFunction n r := by
  rw [eFunction_eq_maxAdmissibleEdges_add_one]
  exact Nat.add_le_add_right (blowupEdgeQuadraticForm_le_maxAdmissibleEdges_of_sum_le hn hw) 1

theorem sq_mul_maxAdmissibleEdges_le_maxAdmissibleEdges_mul
    (m : ℕ) {r c : ℕ} (hc : 1 ≤ c) (hr : 1 ≤ r) :
    c ^ 2 * maxAdmissibleEdges m r ≤ maxAdmissibleEdges (c * m) (c * (r - 1) + 1) := by
  obtain ⟨H, hH, hcard⟩ := exists_isAdmissibleBookFree_card_eq_maxAdmissibleEdges m r
  have hw : IsAdmissibleBlowupWeight H (fun _ : Fin m ↦ c) (c * (r - 1) + 1) :=
    isAdmissibleBlowupWeight_of_isAdmissibleBookFree_of_bounds
      hr (fun _ ↦ hc) (fun _ ↦ le_rfl) hH
  have hsum : (∑ _u : Fin m, c) ≤ c * m := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  have hle := blowupEdgeQuadraticForm_le_maxAdmissibleEdges_of_sum_le hsum hw
  rwa [blowupEdgeQuadraticForm_const, hcard] at hle

theorem sq_mul_maxAdmissibleEdges_two_le_maxAdmissibleEdges_mul_succ
    (m : ℕ) {c : ℕ} (hc : 1 ≤ c) :
    c ^ 2 * maxAdmissibleEdges m 2 ≤ maxAdmissibleEdges (c * m) (c + 1) := by
  simpa using sq_mul_maxAdmissibleEdges_le_maxAdmissibleEdges_mul m hc (by omega : 1 ≤ 2)

theorem four_mul_maxAdmissibleEdges_two_le_maxAdmissibleEdges_twice_three (m : ℕ) :
    4 * maxAdmissibleEdges m 2 ≤ maxAdmissibleEdges (2 * m) 3 := by
  simpa using sq_mul_maxAdmissibleEdges_two_le_maxAdmissibleEdges_mul_succ m (by omega : 1 ≤ 2)

theorem nine_mul_maxAdmissibleEdges_two_le_maxAdmissibleEdges_thrice_four (m : ℕ) :
    9 * maxAdmissibleEdges m 2 ≤ maxAdmissibleEdges (3 * m) 4 := by
  simpa using sq_mul_maxAdmissibleEdges_two_le_maxAdmissibleEdges_mul_succ m (by omega : 1 ≤ 3)

theorem blowupEdgeQuadraticForm_sub_maxAdmissibleEdges_le_stepDiff
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {n r : ℕ}
    (hn : (∑ u : α, w u) ≤ n) (hw : IsAdmissibleBlowupWeight H w (r + 1)) :
    blowupEdgeQuadraticForm H w - maxAdmissibleEdges n r ≤ stepDiff n r := by
  have hle := blowupEdgeQuadraticForm_le_maxAdmissibleEdges_of_sum_le hn hw
  rw [stepDiff_eq_maxAdmissibleEdges_sub]
  omega

theorem blowupEdgeQuadraticForm_sub_mantel_turan_le_stepDiff
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {n r : ℕ}
    (hr : 1 ≤ r) (hn : (∑ u : α, w u) ≤ n) (hw : IsAdmissibleBlowupWeight H w (r + 1)) :
    blowupEdgeQuadraticForm H w - (n * (n + r - 1)) / 4 ≤ stepDiff n r := by
  have h1 := blowupEdgeQuadraticForm_sub_maxAdmissibleEdges_le_stepDiff hn hw
  have h2 := maxAdmissibleEdges_le_mul_add_sub_one_div_four n hr
  omega

theorem blowupEdgeQuadraticForm_sub_maxAdmissibleEdges_two_le_stepDiff_two_of_locallyLinear
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {n : ℕ}
    (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ 2)
    (hn : (∑ u : α, w u) ≤ n) (hH : IsAdmissibleBookFree H 2) :
    blowupEdgeQuadraticForm H w - maxAdmissibleEdges n 2 ≤ stepDiff n 2 :=
  blowupEdgeQuadraticForm_sub_maxAdmissibleEdges_le_stepDiff hn
    (isAdmissibleBlowupWeight_of_isAdmissibleBookFree_two_of_le_sub_one
      (by omega : 1 ≤ 3) hpos hle hH)

theorem blowupEdgeQuadraticForm_sub_parity_bound_le_stepDiff_two_of_locallyLinear
    {α : Type*} [Fintype α] {H : SimpleGraph α} {w : α → ℕ} {n : ℕ}
    (hpos : ∀ u : α, 1 ≤ w u) (hle : ∀ u : α, w u ≤ 2)
    (hn : (∑ u : α, w u) ≤ n) (hH : IsAdmissibleBookFree H 2) :
    blowupEdgeQuadraticForm H w - n * ((n - 1) / 2) ≤ stepDiff n 2 := by
  have h1 := blowupEdgeQuadraticForm_sub_maxAdmissibleEdges_two_le_stepDiff_two_of_locallyLinear
    hpos hle hn hH
  have h2 := maxAdmissibleEdges_two_le_mul_div_two n
  omega

theorem four_mul_maxAdmissibleEdges_two_sub_maxAdmissibleEdges_twice_two_le_stepDiff (m : ℕ) :
    4 * maxAdmissibleEdges m 2 - maxAdmissibleEdges (2 * m) 2 ≤ stepDiff (2 * m) 2 := by
  have h := four_mul_maxAdmissibleEdges_two_le_maxAdmissibleEdges_twice_three m
  have hstep : stepDiff (2 * m) 2 = maxAdmissibleEdges (2 * m) 3 - maxAdmissibleEdges (2 * m) 2 :=
    stepDiff_eq_maxAdmissibleEdges_sub (2 * m) 2
  omega

theorem tendsto_step_diff_atTop_of_exists_weightedBlowup {r : ℕ}
    (h : ∀ B : ℝ, ∃ (k : ℕ) (m : ℕ) (H : SimpleGraph (Fin m)) (w : Fin m → ℕ),
      (∑ u : Fin m, w u) ≤ k ∧ IsAdmissibleBlowupWeight H w (r + 1) ∧
        ∀ᶠ n : ℕ in atTop,
          B + ((eFunction n r : ℝ) - (eFunction (n - k) r : ℝ)) ≤
            (blowupEdgeQuadraticForm H w : ℝ)) :
    Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ)) atTop atTop := by
  refine tendsto_step_diff_atTop_of_forall_bound_exists_gadget (fun B ↦ ?_)
  obtain ⟨k, m, H, w, hk, hw, h_ev⟩ := h B
  refine ⟨k, h_ev.mono (fun n hn ↦ ?_)⟩
  have hle_nat : blowupEdgeQuadraticForm H w ≤ maxAdmissibleEdges k (r + 1) :=
    blowupEdgeQuadraticForm_le_maxAdmissibleEdges_of_sum_le hk hw
  have he : eFunction k (r + 1) = maxAdmissibleEdges k (r + 1) + 1 :=
    eFunction_eq_maxAdmissibleEdges_add_one k (r + 1)
  have hle_real : (blowupEdgeQuadraticForm H w : ℝ) ≤ (eFunction k (r + 1) : ℝ) - 1 := by
    have hcast : (blowupEdgeQuadraticForm H w : ℝ) ≤ (maxAdmissibleEdges k (r + 1) : ℝ) :=
      Nat.cast_le.mpr hle_nat
    have he_real : (eFunction k (r + 1) : ℝ) = (maxAdmissibleEdges k (r + 1) : ℝ) + 1 := by
      exact_mod_cast he
    linarith
  linarith

theorem erdos_600_parts_i_of_forall_exists_weightedBlowup
    (h : ∀ r : ℕ, 2 ≤ r → ∀ B : ℝ,
      ∃ (k : ℕ) (m : ℕ) (H : SimpleGraph (Fin m)) (w : Fin m → ℕ),
        (∑ u : Fin m, w u) ≤ k ∧ IsAdmissibleBlowupWeight H w (r + 1) ∧
          ∀ᶠ n : ℕ in atTop,
            B + ((eFunction n r : ℝ) - (eFunction (n - k) r : ℝ)) ≤
              (blowupEdgeQuadraticForm H w : ℝ)) :
    ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ)) atTop atTop :=
  fun r hr ↦ tendsto_step_diff_atTop_of_exists_weightedBlowup (h r hr)

/-! ## Section 6: Universal $K_3$ Blow-Up Formulas and Positive/Negative Controls -/

theorem commonNeighborFinset_top_fin_three_one_two :
    commonNeighborFinset (⊤ : SimpleGraph (Fin 3)) 1 2 = {0} := by
  ext x
  rw [mem_commonNeighborFinset_iff, Finset.mem_singleton]
  fin_cases x <;> decide

theorem commonNeighborFinset_top_fin_three_zero_two :
    commonNeighborFinset (⊤ : SimpleGraph (Fin 3)) 0 2 = {1} := by
  ext x
  rw [mem_commonNeighborFinset_iff, Finset.mem_singleton]
  fin_cases x <;> decide

theorem commonNeighborFinset_top_fin_three_zero_one :
    commonNeighborFinset (⊤ : SimpleGraph (Fin 3)) 0 1 = {2} := by
  ext x
  rw [mem_commonNeighborFinset_iff, Finset.mem_singleton]
  fin_cases x <;> decide

theorem commonNeighborWeightSum_top_fin_three_one_two (w : Fin 3 → ℕ) :
    commonNeighborWeightSum (⊤ : SimpleGraph (Fin 3)) w 1 2 = w 0 := by
  rw [commonNeighborWeightSum, commonNeighborFinset_top_fin_three_one_two, Finset.sum_singleton]

theorem commonNeighborWeightSum_top_fin_three_zero_two (w : Fin 3 → ℕ) :
    commonNeighborWeightSum (⊤ : SimpleGraph (Fin 3)) w 0 2 = w 1 := by
  rw [commonNeighborWeightSum, commonNeighborFinset_top_fin_three_zero_two, Finset.sum_singleton]

theorem commonNeighborWeightSum_top_fin_three_zero_one (w : Fin 3 → ℕ) :
    commonNeighborWeightSum (⊤ : SimpleGraph (Fin 3)) w 0 1 = w 2 := by
  rw [commonNeighborWeightSum, commonNeighborFinset_top_fin_three_zero_one, Finset.sum_singleton]

theorem edgeFinset_top_fin_three :
    (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by
  ext uv
  induction uv using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset]
    fin_cases u <;> fin_cases v <;> decide

theorem blowupEdgeQuadraticForm_top_fin_three (w : Fin 3 → ℕ) :
    blowupEdgeQuadraticForm (⊤ : SimpleGraph (Fin 3)) w =
      w 0 * w 1 + w 0 * w 2 + w 1 * w 2 := by
  unfold blowupEdgeQuadraticForm
  trans ∑ uv ∈ ({s(0, 1), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))), edgeWeightProd w uv
  · refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
    ext uv
    rw [← edgeFinset_top_fin_three]
    simp [SimpleGraph.mem_edgeFinset]
  · have h01 : s((0 : Fin 3), 1) ∉ ({s((0 : Fin 3), 2), s(1, 2)} : Finset (Sym2 (Fin 3))) := by
      decide
    have h02 : s((0 : Fin 3), 2) ∉ ({s((1 : Fin 3), 2)} : Finset (Sym2 (Fin 3))) := by
      decide
    rw [Finset.sum_insert h01, Finset.sum_insert h02, Finset.sum_singleton]
    simp only [edgeWeightProd_mk]
    omega

theorem isAdmissibleBlowupWeight_top_fin_three_iff (w : Fin 3 → ℕ) (r : ℕ) :
    IsAdmissibleBlowupWeight (⊤ : SimpleGraph (Fin 3)) w r ↔
      (1 ≤ w 0 ∧ w 0 < r) ∧ (1 ≤ w 1 ∧ w 1 < r) ∧ (1 ≤ w 2 ∧ w 2 < r) := by
  refine ⟨fun h ↦ ?_, fun ⟨h0, h1, h2⟩ u v huv ↦ ?_⟩
  · have h12 := h 1 2 (by decide)
    have h02 := h 0 2 (by decide)
    have h01 := h 0 1 (by decide)
    rw [commonNeighborWeightSum_top_fin_three_one_two] at h12
    rw [commonNeighborWeightSum_top_fin_three_zero_two] at h02
    rw [commonNeighborWeightSum_top_fin_three_zero_one] at h01
    exact ⟨h12, h02, h01⟩
  · fin_cases u <;> fin_cases v
    · exact False.elim (huv rfl)
    · simpa [commonNeighborWeightSum_top_fin_three_zero_one] using h2
    · simpa [commonNeighborWeightSum_top_fin_three_zero_two] using h1
    · rw [commonNeighborWeightSum_symm]
      simpa [commonNeighborWeightSum_top_fin_three_zero_one] using h2
    · exact False.elim (huv rfl)
    · simpa [commonNeighborWeightSum_top_fin_three_one_two] using h0
    · rw [commonNeighborWeightSum_symm]
      simpa [commonNeighborWeightSum_top_fin_three_zero_two] using h1
    · rw [commonNeighborWeightSum_symm]
      simpa [commonNeighborWeightSum_top_fin_three_one_two] using h0
    · exact False.elim (huv rfl)

/-- Weight vector `![2, 1, 1]` on `Fin 3`, whose weighted blow-up of `K_3` is the 4-vertex,
5-edge diamond graph (`K_4` minus one edge). -/
def k3Weight211 : Fin 3 → ℕ := ![2, 1, 1]

/-- Degenerate weight vector `![0, 1, 1]` on `Fin 3`, deleting vertex `0` of `K_3`. -/
def k3Weight011 : Fin 3 → ℕ := ![0, 1, 1]

theorem blowupEdgeQuadraticForm_top_k3Weight211 :
    blowupEdgeQuadraticForm (⊤ : SimpleGraph (Fin 3)) k3Weight211 = 5 := by
  rw [blowupEdgeQuadraticForm_top_fin_three]
  decide

theorem isAdmissibleBlowupWeight_top_k3Weight211_three :
    IsAdmissibleBlowupWeight (⊤ : SimpleGraph (Fin 3)) k3Weight211 3 := by
  rw [isAdmissibleBlowupWeight_top_fin_three_iff]
  decide

theorem not_isAdmissibleBlowupWeight_top_k3Weight211_two :
    ¬ IsAdmissibleBlowupWeight (⊤ : SimpleGraph (Fin 3)) k3Weight211 2 := by
  rw [isAdmissibleBlowupWeight_top_fin_three_iff]
  decide

theorem not_isAdmissibleBlowupWeight_top_k3Weight011 (r : ℕ) :
    ¬ IsAdmissibleBlowupWeight (⊤ : SimpleGraph (Fin 3)) k3Weight011 r := by
  rw [isAdmissibleBlowupWeight_top_fin_three_iff]
  intro h
  have h0 : 1 ≤ k3Weight011 0 := h.1.1
  revert h0
  decide +kernel

end WeightedVertexBlowupAndStepDifferenceBounds

end Erdos600
