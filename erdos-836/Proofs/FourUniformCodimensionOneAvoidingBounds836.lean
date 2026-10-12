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

public import Mathlib
public import Erdos836Unified435

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 20000

open scoped BigOperators

/-!
# Erdős Problem #836: Universal Edge & Active-Vertex Lower Bounds for 4-Uniform Codimension-One Avoiding 3-Chromatic Intersecting Hypergraphs

This module combines the sharpened Erdős–Lovász–Alon co-degree bound and the `δ(H) ≥ 3`
codimension-one avoiding degree bound to establish universal lower bounds on `|E(H)|` and `|V(H)|`
for 3-chromatic intersecting `r`-uniform hypergraphs avoiding pairwise intersection `r - 1`.

## Main Universal Results (`∀`)

1. **Universal Co-Degree & Exact Multi-Intersection Degree-Sum Identities (Section 1)**:
   - `three_mul_r_le_sum_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one`:
     for `r ≥ 3`, every edge `e₀ ∈ H` of a non-2-colourable intersecting `r`-uniform hypergraph `H`
     avoiding pairwise intersection `r - 1` satisfies `3 * r ≤ ∑ v ∈ e₀, vertexDegree H v`.
   - `r_le_card_sub_one_sub_r_mul_r_sub_two_of_not_hasPairwiseIntersectionAtLeast_sub_one` and
     `two_le_card_sub_one_sub_r_of_not_hasPairwiseIntersectionAtLeast_sub_one`:
     combining `3 * r ≤ ∑_{v ∈ e₀} d(v)` with the sharpened Erdős–Lovász–Alon co-degree bound yields
     `r ≤ (H.card - 1 - r) * (r - 2)` and `2 ≤ H.card - 1 - r` for all `r ≥ 3`.
   - `card_inter_eq_two_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three`,
     `sum_card_inter_multiInterEdges_eq_two_mul_card_of_not_hasPairwiseIntersectionAtLeast_three`,
     and `sum_vertexDegree_eq_r_add_card_sub_one_add_card_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three`:
     in any intersecting `r`-uniform hypergraph `H` avoiding pairwise intersection `3`, every edge
     `e ∈ multiInterEdges H e₀` meets `e₀` in exactly `2` vertices, yielding the exact algebraic
     identity `∑ v ∈ e₀, vertexDegree H v = r + (H.card - 1) + (multiInterEdges H e₀).card`.
   - `sum_vertexDegree_eq_card_add_three_add_card_multiInterEdges_of_r_eq_four` and
     `nine_le_card_add_card_multiInterEdges_of_r_eq_four`:
     for `r = 4` avoiding pairwise intersection `3`, `∑ v ∈ e₀, d(v) = H.card + 3 + |multiInterEdges H e₀|`
     and `9 ≤ H.card + (multiInterEdges H e₀).card`.

2. **Maximum-Degree Bounds, 3-Regularity Handshake Obstruction at `|H| = 7`, and Universal Edge Bound `8 ≤ |H|` for `r = 4` (Section 2)**:
   - `vertexDegree_add_three_mul_r_sub_one_le_sum_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one`
     and `vertexDegree_add_three_mul_r_sub_one_le_card_sub_one_sub_r_mul_r_sub_two_add_two_mul_r`:
     for `r ≥ 3` under codimension-one avoidance, every active vertex `v ∈ activeVertices H` obeys
     `vertexDegree H v + 3 * (r - 1) ≤ (H.card - 1 - r) * (r - 2) + 2 * r`.
   - `vertexDegree_add_eleven_le_two_mul_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three`:
     at `r = 4`, every active vertex `v` satisfies `vertexDegree H v + 11 ≤ 2 * H.card`.
   - `vertexDegree_eq_three_of_r_eq_four_of_card_le_seven_of_not_hasPairwiseIntersectionAtLeast_three`:
     if `H.card ≤ 7` at `r = 4` under intersection-3 avoidance, every active vertex has exact degree `3`.
   - `eight_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable`
     and `eight_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree`:
     since 3-regularity at `H.card = 7` forces `3 * |V(H)| = 7 * 4 = 28` (impossible in `ℕ`), every
     4-uniform non-2-colourable (or 3-chromatic) intersecting hypergraph avoiding pairwise
     intersection `3` satisfies `8 ≤ H.card`.
   - `vertexDegree_bounds_of_r_eq_four_of_card_eq_eight_of_not_hasPairwiseIntersectionAtLeast_three`:
     at `H.card = 8`, every active vertex satisfies `3 ≤ vertexDegree H v ∧ vertexDegree H v ≤ 5`.

3. **Universal Active-Vertex Lower Bounds `2r ≤ |V(H)|` (`r ≥ 2`) and `2r + 1 ≤ |V(H)|` (`r ≥ 3`, yielding `9 ≤ |V(H)|` at `r = 4`) (Section 3)**:
   - `hasPairwiseIntersectionAtLeast_sub_one_of_card_activeVertices_le_two_mul_r_sub_one` and
     `two_mul_r_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one`:
     for `r ≥ 2`, private-intersection witnesses on two distinct vertices of an edge `e₀ ∈ H` force
     `2 * r ≤ (activeVertices H).card` whenever `H` avoids pairwise intersection `r - 1`.
   - `mem_or_sdiff_mem_of_subset_activeVertices_of_card_eq_r_of_not_isTwoColorable`:
     universal complementary-pair dichotomy on `(activeVertices H).card ≤ 2 * r`: for every `r`-subset
     `S ⊆ activeVertices H`, either `S ∈ H` or `activeVertices H \ S ∈ H`.
   - `hasPairwiseIntersectionAtLeast_sub_one_of_card_activeVertices_le_two_mul_r` and
     `two_mul_r_add_one_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one`:
     for every `r ≥ 3`, every non-2-colourable intersecting `r`-uniform hypergraph `H` avoiding
     pairwise intersection `r - 1` has at least `2 * r + 1` active vertices (`2 * r + 1 ≤ |V(H)|`).
   - `nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable`,
     `nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree`,
     `card_activeVertices_eq_nine_or_ten_of_r_eq_four_of_card_eq_eight_of_not_hasPairwiseIntersectionAtLeast_three`,
     and `eight_le_card_and_nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three`:
     at `r = 4`, `9 ≤ (activeVertices H).card`, and if `H.card = 8` then `(activeVertices H).card ∈ {9, 10}`.

4. **Concrete Verified Extremal & Projective-Plane Controls (`biplane742` and `projectivePlanePG23`) (Section 4)**:
   - `biplane742` on `Fin 7` (`7` blocks of size `4`, complement of the Fano plane): 4-uniform,
     intersecting, avoids pairwise intersection `3`, 4-regular (`δ = 4 ≥ 3`), and 2-colourable
     (together with every subhypergraph `H ⊆ biplane742`).
   - `projectivePlanePG23` on `Fin 13` (`13` lines of size `4`, cyclic shifts of `{0, 1, 3, 9} mod 13`):
     4-uniform, intersecting, linear (avoids pairwise intersection `2` and `3`), 4-regular
     (`δ = 4 ≥ 3`), and 2-colourable (together with every subhypergraph `H ⊆ projectivePlanePG23`).
-/

namespace Erdos836

variable {V : Type*}

/-! ## Section 1: Universal Degree-Sum Lower Bounds & Exact Intersection-3 Avoiding Co-Degree Identities -/

/-- For `r ≥ 3`, in any non-2-colourable intersecting `r`-uniform hypergraph `H` avoiding pairwise
intersection `r - 1`, the sum of vertex degrees over every hyperedge `e₀ ∈ H` is at least `3 * r`. -/
theorem three_mul_r_le_sum_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    3 * r ≤ ∑ v ∈ e₀, vertexDegree H v := by
  have hsum : ∑ _v ∈ e₀, 3 ≤ ∑ v ∈ e₀, vertexDegree H v :=
    Finset.sum_le_sum (fun _ hv =>
      three_le_vertexDegree_of_mem_edge_of_not_hasPairwiseIntersectionAtLeast_sub_one
        hr hunif hinter hnot2 hno he₀ hv)
  rw [Finset.sum_const, smul_eq_mul, hunif e₀ he₀] at hsum
  linarith

/-- Combining the `δ(H) ≥ 3` edge degree-sum lower bound `3 * r ≤ ∑_{v ∈ e₀} d(v)` with the
sharpened Erdős–Lovász–Alon co-degree upper bound `(H.card - 1 - r) * (r - 2) + 2 * r` yields
the universal inequality `r ≤ (H.card - 1 - r) * (r - 2)` for every `r ≥ 3`. -/
theorem r_le_card_sub_one_sub_r_mul_r_sub_two_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    r ≤ (H.card - 1 - r) * (r - 2) := by
  obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
  have hlow :=
    three_mul_r_le_sum_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one
      hr hunif hinter hnot2 hno he₀
  have hno' : ¬ HasPairwiseIntersectionAtLeast H ((r - 2) + 1) := by
    have heq : (r - 2) + 1 = r - 1 := by omega
    rwa [heq]
  have hup :=
    sum_vertexDegree_le_card_sub_one_sub_r_mul_add_two_mul_r_of_not_hasPairwiseIntersectionAtLeast
      (by omega) (by omega) hunif hinter hnot2 hno' he₀
  omega

/-- For `r ≥ 3`, every non-2-colourable intersecting `r`-uniform hypergraph `H` avoiding pairwise
intersection `r - 1` satisfies `2 ≤ H.card - 1 - r` (and hence `r + 3 ≤ H.card` directly from the
co-degree and minimum-degree inequalities). -/
theorem two_le_card_sub_one_sub_r_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    2 ≤ H.card - 1 - r := by
  have h :=
    r_le_card_sub_one_sub_r_mul_r_sub_two_of_not_hasPairwiseIntersectionAtLeast_sub_one
      hr hunif hinter hnot2 hno
  by_contra hlt
  have hle : H.card - 1 - r ≤ 1 := by omega
  have hmul : (H.card - 1 - r) * (r - 2) ≤ 1 * (r - 2) :=
    Nat.mul_le_mul_right (r - 2) hle
  omega

/-- In any intersecting hypergraph `H` avoiding pairwise intersection `3`, every hyperedge
`e ∈ multiInterEdges H e₀` meets `e₀` in exactly `2` vertices. -/
theorem card_inter_eq_two_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hinter : IsIntersecting H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ e : Finset V} (he₀ : e₀ ∈ H) (he : e ∈ multiInterEdges H e₀) :
    (e ∩ e₀).card = 2 := by
  unfold multiInterEdges at he
  obtain ⟨herase, hne1⟩ := Finset.mem_filter.mp he
  obtain ⟨hne, heH⟩ := Finset.mem_erase.mp herase
  have hpos : 1 ≤ (e ∩ e₀).card := Finset.Nonempty.card_pos (hinter e heH e₀ he₀)
  have hle2 : (e ∩ e₀).card ≤ 2 := by
    by_contra hgt
    exact hno3 ⟨e, heH, e₀, he₀, hne, by omega⟩
  omega

/-- In any intersecting hypergraph `H` avoiding pairwise intersection `3`, the sum of intersection
sizes `(e ∩ e₀).card` over `multiInterEdges H e₀` equals `2 * (multiInterEdges H e₀).card`. -/
theorem sum_card_inter_multiInterEdges_eq_two_mul_card_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hinter : IsIntersecting H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∑ e ∈ multiInterEdges H e₀, (e ∩ e₀).card = 2 * (multiInterEdges H e₀).card := by
  have hcongr : ∑ e ∈ multiInterEdges H e₀, (e ∩ e₀).card = ∑ _e ∈ multiInterEdges H e₀, 2 := by
    refine Finset.sum_congr rfl (fun e he => ?_)
    exact card_inter_eq_two_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
      hinter hno3 he₀ he
  rw [hcongr, Finset.sum_const, smul_eq_mul, mul_comm]

/-- In any intersecting hypergraph `H` avoiding pairwise intersection `3`, for every `e₀ ∈ H`,
`∑ e ∈ H.erase e₀, (e ∩ e₀).card = (H.card - 1) + (multiInterEdges H e₀).card`. -/
theorem sum_card_inter_erase_eq_card_sub_one_add_card_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hinter : IsIntersecting H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∑ e ∈ H.erase e₀, (e ∩ e₀).card = (H.card - 1) + (multiInterEdges H e₀).card := by
  have hsplit := (Finset.sum_filter_add_sum_filter_not (s := H.erase e₀)
    (p := fun e => (e ∩ e₀).card = 1) (f := fun e => (e ∩ e₀).card)).symm
  change ∑ e ∈ H.erase e₀, (e ∩ e₀).card =
    (∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card) +
      (∑ e ∈ multiInterEdges H e₀, (e ∩ e₀).card) at hsplit
  have hunit_sum : ∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card = (unitInterEdges H e₀).card := by
    have hcongr : ∑ e ∈ unitInterEdges H e₀, (e ∩ e₀).card = ∑ _e ∈ unitInterEdges H e₀, 1 := by
      refine Finset.sum_congr rfl (fun e he => ?_)
      unfold unitInterEdges at he
      exact (Finset.mem_filter.mp he).2
    rw [hcongr, Finset.sum_const, smul_eq_mul, mul_one]
  have hmulti_sum :=
    sum_card_inter_multiInterEdges_eq_two_mul_card_of_not_hasPairwiseIntersectionAtLeast_three
      hinter hno3 he₀
  have hpart := card_unitInterEdges_add_card_multiInterEdges he₀
  omega

/-- **Exact Co-Degree / Multi-Intersection Degree-Sum Identity**:
In any intersecting `r`-uniform hypergraph `H` avoiding pairwise intersection `3`, for every `e₀ ∈ H`,
`∑ v ∈ e₀, vertexDegree H v = r + (H.card - 1) + (multiInterEdges H e₀).card`. -/
theorem sum_vertexDegree_eq_r_add_card_sub_one_add_card_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {r : ℕ} {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∑ v ∈ e₀, vertexDegree H v = r + (H.card - 1) + (multiInterEdges H e₀).card := by
  have hcodeg := sum_card_inter_erase_eq_sum_vertexDegree_sub_r hunif he₀
  have hsum :=
    sum_card_inter_erase_eq_card_sub_one_add_card_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
      hinter hno3 he₀
  have hge : r ≤ ∑ v ∈ e₀, vertexDegree H v := by
    have h1 : ∑ _v ∈ e₀, 1 ≤ ∑ v ∈ e₀, vertexDegree H v := by
      refine Finset.sum_le_sum (fun v hv => ?_)
      unfold vertexDegree
      exact Finset.card_pos.mpr ⟨e₀, Finset.mem_filter.mpr ⟨he₀, hv⟩⟩
    rw [Finset.sum_const, smul_eq_mul, mul_one, hunif e₀ he₀] at h1
    exact h1
  omega

/-- At `r = 4`, for every edge `e₀ ∈ H` of an intersecting 4-uniform hypergraph `H` avoiding
pairwise intersection `3`, `∑ v ∈ e₀, vertexDegree H v = H.card + 3 + (multiInterEdges H e₀).card`. -/
theorem sum_vertexDegree_eq_card_add_three_add_card_multiInterEdges_of_r_eq_four
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    ∑ v ∈ e₀, vertexDegree H v = H.card + 3 + (multiInterEdges H e₀).card := by
  have h :=
    sum_vertexDegree_eq_r_add_card_sub_one_add_card_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
      hunif hinter hno3 he₀
  have hpos : 1 ≤ H.card := Finset.card_pos.mpr ⟨e₀, he₀⟩
  omega

/-- At `r = 4`, in any non-2-colourable intersecting 4-uniform hypergraph `H` avoiding pairwise
intersection `3`, every edge `e₀ ∈ H` satisfies `9 ≤ H.card + (multiInterEdges H e₀).card`. -/
theorem nine_le_card_add_card_multiInterEdges_of_r_eq_four
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    9 ≤ H.card + (multiInterEdges H e₀).card := by
  have hdeg :=
    three_mul_r_le_sum_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one
      (by decide) hunif hinter hnot2 hno3 he₀
  have heq :=
    sum_vertexDegree_eq_card_add_three_add_card_multiInterEdges_of_r_eq_four
      hunif hinter hno3 he₀
  omega

/-! ## Section 2: Maximum Degree Upper Bounds, 3-Regularity Handshake Obstruction at `|H| = 7`, and Universal Edge Lower Bound `8 ≤ |H|` for `r = 4` -/

/-- For `r ≥ 3`, in any non-2-colourable intersecting `r`-uniform hypergraph `H` avoiding pairwise
intersection `r - 1`, every edge `e₀ ∈ H` and vertex `v ∈ e₀` satisfy
`vertexDegree H v + 3 * (r - 1) ≤ ∑ u ∈ e₀, vertexDegree H u`. -/
theorem vertexDegree_add_three_mul_r_sub_one_le_sum_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀) :
    vertexDegree H v + 3 * (r - 1) ≤ ∑ u ∈ e₀, vertexDegree H u := by
  rw [← Finset.add_sum_erase e₀ (vertexDegree H) hv]
  have hsum : ∑ _u ∈ e₀.erase v, 3 ≤ ∑ u ∈ e₀.erase v, vertexDegree H u := by
    refine Finset.sum_le_sum (fun u hu => ?_)
    exact three_le_vertexDegree_of_mem_edge_of_not_hasPairwiseIntersectionAtLeast_sub_one
      hr hunif hinter hnot2 hno he₀ (Finset.mem_of_mem_erase hu)
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hv, hunif e₀ he₀] at hsum
  linarith

/-- **Universal Active-Vertex Maximum-Degree Inequality under Codimension-One Avoidance**:
For `r ≥ 3`, in any non-2-colourable intersecting `r`-uniform hypergraph `H` avoiding pairwise
intersection `r - 1`, every active vertex `v ∈ activeVertices H` satisfies
`vertexDegree H v + 3 * (r - 1) ≤ (H.card - 1 - r) * (r - 2) + 2 * r`. -/
theorem vertexDegree_add_three_mul_r_sub_one_le_card_sub_one_sub_r_mul_r_sub_two_add_two_mul_r
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {v : V} (hv : v ∈ activeVertices H) :
    vertexDegree H v + 3 * (r - 1) ≤ (H.card - 1 - r) * (r - 2) + 2 * r := by
  unfold activeVertices at hv
  simp only [Finset.mem_biUnion, id_eq] at hv
  obtain ⟨e₀, he₀, hv₀⟩ := hv
  have h1 :=
    vertexDegree_add_three_mul_r_sub_one_le_sum_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one
      hr hunif hinter hnot2 hno he₀ hv₀
  have hno' : ¬ HasPairwiseIntersectionAtLeast H ((r - 2) + 1) := by
    have heq : (r - 2) + 1 = r - 1 := by omega
    rwa [heq]
  have h2 :=
    sum_vertexDegree_le_card_sub_one_sub_r_mul_add_two_mul_r_of_not_hasPairwiseIntersectionAtLeast
      (by omega) (by omega) hunif hinter hnot2 hno' he₀
  omega

/-- Specializing to `r = 4`: in any non-2-colourable intersecting 4-uniform hypergraph `H` avoiding
pairwise intersection `3`, every active vertex `v ∈ activeVertices H` satisfies
`vertexDegree H v + 11 ≤ 2 * H.card`. -/
theorem vertexDegree_add_eleven_le_two_mul_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {v : V} (hv : v ∈ activeVertices H) :
    vertexDegree H v + 11 ≤ 2 * H.card := by
  have h :=
    vertexDegree_add_three_mul_r_sub_one_le_card_sub_one_sub_r_mul_r_sub_two_add_two_mul_r
      (by decide) hunif hinter hnot2 hno3 hv
  have hcard := r_add_three_le_card_of_isIntersecting_of_not_isTwoColorable
    (by decide) hunif hinter hnot2
  omega

/-- If a non-2-colourable intersecting 4-uniform hypergraph `H` avoiding pairwise intersection `3`
has `H.card ≤ 7`, then every active vertex `v ∈ activeVertices H` has exact degree `3`. -/
theorem vertexDegree_eq_three_of_r_eq_four_of_card_le_seven_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) (hle7 : H.card ≤ 7)
    {v : V} (hv : v ∈ activeVertices H) :
    vertexDegree H v = 3 := by
  have hge :=
    three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
      (by decide) hunif hinter hnot2 hno3 hv
  have hle :=
    vertexDegree_add_eleven_le_two_mul_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
      hunif hinter hnot2 hno3 hv
  omega

/-- **Universal Edge Lower Bound (`8 ≤ H.card`) for 4-Uniform 3-Chromatic Intersecting Hypergraphs
Avoiding Pairwise Intersection `3`**:
Every non-2-colourable intersecting 4-uniform hypergraph `H` with `¬ HasPairwiseIntersectionAtLeast H 3`
has at least `8` hyperedges (`8 ≤ H.card`).
Proof: `7 ≤ H.card` holds by `r_add_three_le_card_of_isIntersecting_of_not_isTwoColorable`; if
`H.card = 7`, then every active vertex has degree `3`, so the handshake identity gives
`3 * (activeVertices H).card = 7 * 4 = 28`, which is impossible in `ℕ`. -/
theorem eight_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    8 ≤ H.card := by
  have hge7 := r_add_three_le_card_of_isIntersecting_of_not_isTwoColorable
    (by decide) hunif hinter hnot2
  by_contra hlt8
  have hle7 : H.card ≤ 7 := by omega
  have hhand := sum_vertexDegree_activeVertices_eq_card_mul_r hunif
  have hcongr : ∑ v ∈ activeVertices H, vertexDegree H v = ∑ _v ∈ activeVertices H, 3 := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    exact vertexDegree_eq_three_of_r_eq_four_of_card_le_seven_of_not_hasPairwiseIntersectionAtLeast_three
      hunif hinter hnot2 hno3 hle7 hv
  rw [hcongr, Finset.sum_const, smul_eq_mul] at hhand
  omega

/-- Every 3-chromatic intersecting 4-uniform hypergraph `H` avoiding pairwise intersection `3`
has at least `8` hyperedges (`8 ≤ H.card`). -/
theorem eight_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hchrom : HasChromaticNumberThree H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    8 ≤ H.card :=
  eight_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    hunif hinter hchrom.2 hno3

/-- At the threshold `H.card = 8` for `r = 4` avoiding pairwise intersection `3`, every active
vertex `v ∈ activeVertices H` satisfies `3 ≤ vertexDegree H v ∧ vertexDegree H v ≤ 5`. -/
theorem vertexDegree_bounds_of_r_eq_four_of_card_eq_eight_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) (hcard8 : H.card = 8)
    {v : V} (hv : v ∈ activeVertices H) :
    3 ≤ vertexDegree H v ∧ vertexDegree H v ≤ 5 := by
  have hge :=
    three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
      (by decide) hunif hinter hnot2 hno3 hv
  have hle :=
    vertexDegree_add_eleven_le_two_mul_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
      hunif hinter hnot2 hno3 hv
  omega

/-! ## Section 3: Universal Active-Vertex Lower Bounds `2r ≤ |V(H)|` (`r ≥ 2`) and `2r + 1 ≤ |V(H)|` (`r ≥ 3`, `9 ≤ |V(H)|` at `r = 4`) -/

/-- For every `r ≥ 2`, if `H` is a non-2-colourable intersecting `r`-uniform hypergraph with
`(activeVertices H).card ≤ 2 * r - 1`, then `H` contains two distinct edges meeting in at least
`r - 1` vertices (`HasPairwiseIntersectionAtLeast H (r - 1)`). -/
theorem hasPairwiseIntersectionAtLeast_sub_one_of_card_activeVertices_le_two_mul_r_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hcard : (activeVertices H).card ≤ 2 * r - 1) :
    HasPairwiseIntersectionAtLeast H (r - 1) := by
  obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
  have he₀_card : e₀.card = r := hunif e₀ he₀
  have h1lt : 1 < e₀.card := by omega
  obtain ⟨u, v, hu, hv, huv⟩ := Finset.one_lt_card_iff.mp h1lt
  obtain ⟨e₁, he₁, h1_sing, _, _⟩ :=
    exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable hr hunif hinter hnot2 he₀ hu
  obtain ⟨e₂, he₂, h2_sing, _, _⟩ :=
    exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable hr hunif hinter hnot2 he₀ hv
  have hne12 : e₁ ≠ e₂ := by
    intro heq
    subst heq
    have hmem : u ∈ ({v} : Finset V) := by
      rw [← h2_sing, h1_sing]
      exact Finset.mem_singleton_self u
    exact huv (Finset.mem_singleton.mp hmem)
  have he₀_sub : e₀ ⊆ activeVertices H := fun x hx => mem_activeVertices_of_mem_edge he₀ hx
  have hsdiff_A : (activeVertices H \ e₀).card ≤ r - 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr he₀_sub, he₀_card]
    omega
  have hsdiff1 : (e₁ \ e₀).card = r - 1 := by
    have h := Finset.card_sdiff_add_card_inter e₁ e₀
    rw [h1_sing, Finset.card_singleton, hunif e₁ he₁] at h
    omega
  have hsdiff2 : (e₂ \ e₀).card = r - 1 := by
    have h := Finset.card_sdiff_add_card_inter e₂ e₀
    rw [h2_sing, Finset.card_singleton, hunif e₂ he₂] at h
    omega
  have hunion_sub : (e₁ \ e₀) ∪ (e₂ \ e₀) ⊆ activeVertices H \ e₀ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · obtain ⟨hx_e₁, hx_not⟩ := Finset.mem_sdiff.mp hx1
      exact Finset.mem_sdiff.mpr ⟨mem_activeVertices_of_mem_edge he₁ hx_e₁, hx_not⟩
    · obtain ⟨hx_e₂, hx_not⟩ := Finset.mem_sdiff.mp hx2
      exact Finset.mem_sdiff.mpr ⟨mem_activeVertices_of_mem_edge he₂ hx_e₂, hx_not⟩
  have hunion_le : ((e₁ \ e₀) ∪ (e₂ \ e₀)).card ≤ r - 1 :=
    le_trans (Finset.card_le_card hunion_sub) hsdiff_A
  have h_ui := Finset.card_union_add_card_inter (e₁ \ e₀) (e₂ \ e₀)
  have hinter_sdiff_sub : (e₁ \ e₀) ∩ (e₂ \ e₀) ⊆ e₁ ∩ e₂ := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx1).1, (Finset.mem_sdiff.mp hx2).1⟩
  have hinter_le := Finset.card_le_card hinter_sdiff_sub
  refine ⟨e₁, he₁, e₂, he₂, hne12, ?_⟩
  omega

/-- For every `r ≥ 2`, if `H` is a non-2-colourable intersecting `r`-uniform hypergraph avoiding
pairwise intersection `r - 1`, then `2 * r ≤ (activeVertices H).card`. -/
theorem two_mul_r_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    2 * r ≤ (activeVertices H).card := by
  by_contra hlt
  exact hno (hasPairwiseIntersectionAtLeast_sub_one_of_card_activeVertices_le_two_mul_r_sub_one
    hr hunif hinter hnot2 (by omega))

/-- **Universal Complementary-Pair Dichotomy on `≤ 2r` Active Vertices**:
In any non-2-colourable `r`-uniform hypergraph `H` with `(activeVertices H).card ≤ 2 * r`, for
every subset `S ⊆ activeVertices H` of cardinality `S.card = r`, either `S ∈ H` or
`activeVertices H \ S ∈ H`. -/
theorem mem_or_sdiff_mem_of_subset_activeVertices_of_card_eq_r_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hnot2 : ¬ IsTwoColorable H) (hcard : (activeVertices H).card ≤ 2 * r)
    {S : Finset V} (hS_sub : S ⊆ activeVertices H) (hS_card : S.card = r) :
    S ∈ H ∨ activeVertices H \ S ∈ H := by
  have hnot_prop : ¬ IsProperColoring H (subsetColoring S) :=
    fun hp => hnot2 ⟨subsetColoring S, hp⟩
  unfold IsProperColoring at hnot_prop
  push Not at hnot_prop
  obtain ⟨e, he, hmono⟩ := hnot_prop
  have he_card : e.card = r := hunif e he
  by_cases hex : ∃ u ∈ e, u ∈ S
  · obtain ⟨u, hu_e, hu_S⟩ := hex
    have hsub : e ⊆ S := by
      intro v hv_e
      by_contra hv_not_S
      have heq_col := hmono u hu_e v hv_e
      simp [subsetColoring, hu_S, hv_not_S] at heq_col
    have heq : e = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact Or.inl (heq ▸ he)
  · have hsub : e ⊆ activeVertices H \ S := by
      intro v hv_e
      refine Finset.mem_sdiff.mpr ⟨mem_activeVertices_of_mem_edge he hv_e, ?_⟩
      intro hv_S
      exact hex ⟨v, hv_e, hv_S⟩
    have hsdiff_le : (activeVertices H \ S).card ≤ e.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS_sub, hS_card, he_card]
      omega
    have heq : e = activeVertices H \ S := Finset.eq_of_subset_of_card_le hsub hsdiff_le
    exact Or.inr (heq ▸ he)

/-- For every `r ≥ 3`, if `H` is a non-2-colourable intersecting `r`-uniform hypergraph with
`(activeVertices H).card ≤ 2 * r`, then `H` contains two distinct edges meeting in at least
`r - 1` vertices (`HasPairwiseIntersectionAtLeast H (r - 1)`). -/
theorem hasPairwiseIntersectionAtLeast_sub_one_of_card_activeVertices_le_two_mul_r
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hcard : (activeVertices H).card ≤ 2 * r) :
    HasPairwiseIntersectionAtLeast H (r - 1) := by
  by_cases hlt : (activeVertices H).card ≤ 2 * r - 1
  · exact hasPairwiseIntersectionAtLeast_sub_one_of_card_activeVertices_le_two_mul_r_sub_one
      (by omega) hunif hinter hnot2 hlt
  · have hA_eq : (activeVertices H).card = 2 * r := by omega
    obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
    have he₀_card : e₀.card = r := hunif e₀ he₀
    have he₀_sub : e₀ ⊆ activeVertices H := fun x hx => mem_activeVertices_of_mem_edge he₀ hx
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < e₀.card)
    have hsdiff_card : (activeVertices H \ e₀).card = r := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr he₀_sub, hA_eq, he₀_card]
      omega
    obtain ⟨w₁, w₂, hw₁_d, hw₂_d, hw_ne⟩ :=
      Finset.one_lt_card_iff.mp (by omega : 1 < (activeVertices H \ e₀).card)
    obtain ⟨hw₁_A, hw₁_not⟩ := Finset.mem_sdiff.mp hw₁_d
    obtain ⟨hw₂_A, hw₂_not⟩ := Finset.mem_sdiff.mp hw₂_d
    let S₁ : Finset V := insert w₁ (e₀.erase v)
    let S₂ : Finset V := insert w₂ (e₀.erase v)
    have hS_helper : ∀ w : V, w ∈ activeVertices H → w ∉ e₀ →
        insert w (e₀.erase v) ⊆ activeVertices H ∧ (insert w (e₀.erase v)).card = r ∧
        insert w (e₀.erase v) ≠ e₀ ∧ r - 1 ≤ (insert w (e₀.erase v) ∩ e₀).card := by
      intro w hw_A hw_not
      have hw_not_er : w ∉ e₀.erase v := fun h => hw_not (Finset.mem_of_mem_erase h)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx_er
        · exact hw_A
        · exact he₀_sub (Finset.mem_of_mem_erase hx_er)
      · rw [Finset.card_insert_of_notMem hw_not_er, Finset.card_erase_of_mem hv, he₀_card]
        omega
      · intro heq
        have hw_in : w ∈ insert w (e₀.erase v) := Finset.mem_insert_self w _
        rw [heq] at hw_in
        exact hw_not hw_in
      · have hsub_inter : e₀.erase v ⊆ insert w (e₀.erase v) ∩ e₀ := by
          intro x hx
          exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx, Finset.mem_of_mem_erase hx⟩
        have hle := Finset.card_le_card hsub_inter
        rw [Finset.card_erase_of_mem hv, he₀_card] at hle
        exact hle
    obtain ⟨hS₁_sub, hS₁_card, hS₁_ne, hS₁_inter⟩ := hS_helper w₁ hw₁_A hw₁_not
    obtain ⟨hS₂_sub, hS₂_card, hS₂_ne, hS₂_inter⟩ := hS_helper w₂ hw₂_A hw₂_not
    rcases mem_or_sdiff_mem_of_subset_activeVertices_of_card_eq_r_of_not_isTwoColorable
        hunif hnot2 hcard hS₁_sub hS₁_card with hS₁_H | hf₁_H
    · exact ⟨S₁, hS₁_H, e₀, he₀, hS₁_ne, hS₁_inter⟩
    · rcases mem_or_sdiff_mem_of_subset_activeVertices_of_card_eq_r_of_not_isTwoColorable
          hunif hnot2 hcard hS₂_sub hS₂_card with hS₂_H | hf₂_H
      · exact ⟨S₂, hS₂_H, e₀, he₀, hS₂_ne, hS₂_inter⟩
      · have hf_ne : activeVertices H \ S₁ ≠ activeVertices H \ S₂ := by
          intro heq
          have hw₂_in : w₂ ∈ activeVertices H \ S₁ := by
            refine Finset.mem_sdiff.mpr ⟨hw₂_A, ?_⟩
            intro hw₂_S₁
            rcases Finset.mem_insert.mp hw₂_S₁ with h21 | h_er
            · exact hw_ne h21.symm
            · exact hw₂_not (Finset.mem_of_mem_erase h_er)
          rw [heq] at hw₂_in
          exact (Finset.mem_sdiff.mp hw₂_in).2 (Finset.mem_insert_self w₂ _)
        let U : Finset V := insert w₁ (insert w₂ (e₀.erase v))
        have hsub_inter : activeVertices H \ U ⊆ (activeVertices H \ S₁) ∩ (activeVertices H \ S₂) := by
          intro x hx
          obtain ⟨hx_A, hx_not_U⟩ := Finset.mem_sdiff.mp hx
          refine Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hx_A, ?_⟩, Finset.mem_sdiff.mpr ⟨hx_A, ?_⟩⟩
          · intro hx_S₁
            rcases Finset.mem_insert.mp hx_S₁ with rfl | hx_er
            · exact hx_not_U (Finset.mem_insert_self x _)
            · exact hx_not_U (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx_er))
          · intro hx_S₂
            exact hx_not_U (Finset.mem_insert_of_mem hx_S₂)
        have hU_le : U.card ≤ r + 1 := by
          dsimp only [U]
          have h1 := Finset.card_insert_le w₁ (insert w₂ (e₀.erase v))
          have h2 := Finset.card_insert_le w₂ (e₀.erase v)
          have h3 : (e₀.erase v).card = r - 1 := by
            rw [Finset.card_erase_of_mem hv, he₀_card]
          omega
        have hsdiff_U := Finset.le_card_sdiff U (activeVertices H)
        have hinter_le := Finset.card_le_card hsub_inter
        refine ⟨activeVertices H \ S₁, hf₁_H, activeVertices H \ S₂, hf₂_H, hf_ne, ?_⟩
        omega

/-- **Universal Codimension-One Avoiding Active-Vertex Lower Bound (`2r + 1 ≤ |V(H)|`)**:
For every `r ≥ 3`, every non-2-colourable intersecting `r`-uniform hypergraph `H` avoiding
pairwise intersection `r - 1` has at least `2 * r + 1` active vertices. -/
theorem two_mul_r_add_one_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 3 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    2 * r + 1 ≤ (activeVertices H).card := by
  by_contra hlt
  exact hno (hasPairwiseIntersectionAtLeast_sub_one_of_card_activeVertices_le_two_mul_r
    hr hunif hinter hnot2 (by omega))

/-- **Universal Active-Vertex Lower Bound (`9 ≤ (activeVertices H).card`) for `r = 4` Avoiding
Pairwise Intersection `3`**:
Every non-2-colourable intersecting 4-uniform hypergraph `H` with `¬ HasPairwiseIntersectionAtLeast H 3`
has at least `9` active vertices (`9 ≤ (activeVertices H).card`). -/
theorem nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    9 ≤ (activeVertices H).card :=
  two_mul_r_add_one_le_card_activeVertices_of_not_hasPairwiseIntersectionAtLeast_sub_one
    (by decide) hunif hinter hnot2 hno3

/-- Every 3-chromatic intersecting 4-uniform hypergraph `H` avoiding pairwise intersection `3`
has at least `9` active vertices (`9 ≤ (activeVertices H).card`). -/
theorem nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hchrom : HasChromaticNumberThree H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    9 ≤ (activeVertices H).card :=
  nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    hunif hinter hchrom.2 hno3

/-- At the minimum possible edge count `H.card = 8` for `r = 4` avoiding pairwise intersection `3`,
the number of active vertices is either `9` or `10`. -/
theorem card_activeVertices_eq_nine_or_ten_of_r_eq_four_of_card_eq_eight_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) (hcard8 : H.card = 8) :
    (activeVertices H).card = 9 ∨ (activeVertices H).card = 10 := by
  have hge9 :=
    nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
      hunif hinter hnot2 hno3
  have hle :=
    three_mul_card_activeVertices_le_card_mul_r_of_not_hasPairwiseIntersectionAtLeast_sub_one
      (by decide) hunif hinter hnot2 hno3
  omega

/-- **Joint Universal Edge & Active-Vertex Lower Bound Theorem for 4-Uniform 3-Chromatic
Intersecting Hypergraphs Avoiding Pairwise Intersection `3` (Resolves Saved `next_task`)**:
Every 3-chromatic intersecting 4-uniform hypergraph `H` avoiding pairwise intersection `3`
satisfies `8 ≤ H.card`, `9 ≤ (activeVertices H).card`, and `3 * (activeVertices H).card ≤ H.card * 4`. -/
theorem eight_le_card_and_nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hchrom : HasChromaticNumberThree H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    8 ≤ H.card ∧ 9 ≤ (activeVertices H).card ∧ 3 * (activeVertices H).card ≤ H.card * 4 :=
  ⟨eight_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
      hunif hinter hchrom hno3,
   nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
      hunif hinter hchrom hno3,
   three_mul_card_activeVertices_le_card_mul_r_of_not_hasPairwiseIntersectionAtLeast_sub_one
      (by decide) hunif hinter hchrom.2 hno3⟩

/-! ## Section 4: Concrete Verified Extremal & Projective-Plane Controls (`biplane742` and `projectivePlanePG23`) -/

/-- The `(7, 4, 2)` biplane on `Fin 7` (complement of the Fano plane `PG(2, 2)`): `7` vertices,
`7` blocks of size `4`, every two distinct blocks meeting in `2` vertices. -/
def biplane742 : Finset (Finset (Fin 7)) :=
  { {2, 4, 5, 6}, {0, 3, 5, 6}, {0, 1, 4, 6}, {0, 1, 2, 5},
    {1, 2, 3, 6}, {0, 2, 3, 4}, {1, 3, 4, 5} }

theorem biplane742_card : biplane742.card = 7 := by decide

theorem biplane742_activeVertices_card : (activeVertices biplane742).card = 7 := by decide

theorem biplane742_isUniform : IsUniform 4 biplane742 := by decide

theorem biplane742_isIntersecting : IsIntersecting biplane742 := by decide

theorem biplane742_not_hasPairwiseIntersectionAtLeast_three :
    ¬ HasPairwiseIntersectionAtLeast biplane742 3 := by decide

theorem biplane742_forall_vertexDegree_eq_four :
    ∀ v ∈ activeVertices biplane742, vertexDegree biplane742 v = 4 := by decide

theorem biplane742_isTransversal_zero_one_two :
    IsTransversal biplane742 ({0, 1, 2} : Finset (Fin 7)) := by decide

theorem biplane742_isTwoColorable : IsTwoColorable biplane742 :=
  isTwoColorable_of_isTransversal_of_card_lt_r biplane742_isUniform
    biplane742_isTransversal_zero_one_two (by decide)

theorem isTwoColorable_of_subset_biplane742 {H : Finset (Finset (Fin 7))}
    (hsub : H ⊆ biplane742) : IsTwoColorable H :=
  isTwoColorable_mono hsub biplane742_isTwoColorable


/-- Universal Indexed-Hypergraph Uniformity Bridge: if every indexed hyperedge `L i` has size `r`,
then `Finset.univ.image L` is `r`-uniform. -/
theorem isUniform_image_univ {ι : Type*} [Fintype ι] [DecidableEq V] {r : ℕ}
    (L : ι → Finset V) (hunif : ∀ i : ι, (L i).card = r) :
    IsUniform r (Finset.univ.image L) := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
  exact hunif i

/-- Universal Indexed-Hypergraph Intersecting Bridge: if every pair `L i, L j` intersects,
then `Finset.univ.image L` is intersecting. -/
theorem isIntersecting_image_univ {ι : Type*} [Fintype ι] [DecidableEq V]
    (L : ι → Finset V) (hinter : ∀ i j : ι, (L i ∩ L j).Nonempty) :
    IsIntersecting (Finset.univ.image L) := by
  intro e₁ he₁ e₂ he₂
  rcases Finset.mem_image.mp he₁ with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp he₂ with ⟨j, _, rfl⟩
  exact hinter i j

/-- Universal Indexed-Hypergraph Linearity Bridge: if every distinct pair `L i, L j` (`i ≠ j`)
meets in at most `1` vertex, then `Finset.univ.image L` is a linear hypergraph. -/
theorem isLinearHypergraph_image_univ {ι : Type*} [Fintype ι] [DecidableEq V]
    (L : ι → Finset V) (hlin : ∀ i j : ι, i ≠ j → (L i ∩ L j).card ≤ 1) :
    IsLinearHypergraph (Finset.univ.image L) := by
  intro e₁ he₁ e₂ he₂ hne
  rcases Finset.mem_image.mp he₁ with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp he₂ with ⟨j, _, rfl⟩
  exact hlin i j (fun hij => hne (hij ▸ rfl))

/-- Universal Indexed-Hypergraph Blocking-Set 2-Colourability Bridge: if `S` intersects every
`L i` and contains no `L i`, then `Finset.univ.image L` is 2-colourable. -/
theorem isTwoColorable_image_univ_of_blocking {ι : Type*} [Fintype ι] [DecidableEq V]
    (L : ι → Finset V) (S : Finset V)
    (htrans : ∀ i : ι, (L i ∩ S).Nonempty) (hnotsub : ∀ i : ι, ¬ L i ⊆ S) :
    IsTwoColorable (Finset.univ.image L) := by
  refine ⟨subsetColoring S, isProperColoring_subsetColoring_of_isTransversal ?_ ?_⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
    exact htrans i
  · intro e he
    rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
    exact hnotsub i

/-- Cyclic difference-set line generator for the projective plane `PG(2, 3)` on `Fin 13`:
`pg23Line i = {i, i + 1, i + 3, i + 9} mod 13`. -/
def pg23Line (i : Fin 13) : Finset (Fin 13) :=
  {i, i + 1, i + 3, i + 9}

/-- The projective plane `PG(2, 3)` on `Fin 13`: `13` points, `13` lines of size `4`, generated
by cyclic shifts of `{0, 1, 3, 9} mod 13`. -/
def projectivePlanePG23 : Finset (Finset (Fin 13)) :=
  Finset.univ.image pg23Line

theorem pg23Line_card : ∀ i : Fin 13, (pg23Line i).card = 4 := by decide

theorem pg23Line_inter_nonempty : ∀ i j : Fin 13, (pg23Line i ∩ pg23Line j).Nonempty := by decide

theorem pg23Line_inter_card_le_one :
    ∀ i j : Fin 13, i ≠ j → (pg23Line i ∩ pg23Line j).card ≤ 1 := by decide

theorem projectivePlanePG23_isUniform : IsUniform 4 projectivePlanePG23 :=
  isUniform_image_univ pg23Line pg23Line_card

theorem projectivePlanePG23_isIntersecting : IsIntersecting projectivePlanePG23 :=
  isIntersecting_image_univ pg23Line pg23Line_inter_nonempty

theorem projectivePlanePG23_isLinearHypergraph : IsLinearHypergraph projectivePlanePG23 :=
  isLinearHypergraph_image_univ pg23Line pg23Line_inter_card_le_one

theorem projectivePlanePG23_not_hasPairwiseIntersectionAtLeast_three :
    ¬ HasPairwiseIntersectionAtLeast projectivePlanePG23 3 :=
  not_hasPairwiseIntersectionAtLeast_of_isLinearHypergraph (by decide)
    projectivePlanePG23_isLinearHypergraph

/-- Explicit 6-point blocking set `S = {0, 1, 2, 3, 4, 5}` in `PG(2, 3)` that intersects every line
and contains no line. -/
def pg23BlockingSet : Finset (Fin 13) := {0, 1, 2, 3, 4, 5}

theorem pg23Line_inter_pg23BlockingSet_nonempty :
    ∀ i : Fin 13, (pg23Line i ∩ pg23BlockingSet).Nonempty := by decide

theorem pg23Line_not_subset_pg23BlockingSet :
    ∀ i : Fin 13, ¬ pg23Line i ⊆ pg23BlockingSet := by decide

theorem projectivePlanePG23_isTwoColorable : IsTwoColorable projectivePlanePG23 :=
  isTwoColorable_image_univ_of_blocking pg23Line pg23BlockingSet
    pg23Line_inter_pg23BlockingSet_nonempty pg23Line_not_subset_pg23BlockingSet

theorem isTwoColorable_of_subset_projectivePlanePG23 {H : Finset (Finset (Fin 13))}
    (hsub : H ⊆ projectivePlanePG23) : IsTwoColorable H :=
  isTwoColorable_mono hsub projectivePlanePG23_isTwoColorable

/-- Universal Indexed-Hypergraph Injectivity Lemma: if every indexed edge `L i` has cardinality
at least `2` and any two distinct indices `i ≠ j` have `(L i ∩ L j).card ≤ 1`, then `L` is
injective. -/
theorem injective_of_two_le_card_of_inter_card_le_one {ι : Type*} [DecidableEq V]
    (L : ι → Finset V) (hcard : ∀ i : ι, 2 ≤ (L i).card)
    (hlin : ∀ i j : ι, i ≠ j → (L i ∩ L j).card ≤ 1) :
    Function.Injective L := by
  intro i j hij
  by_contra hne
  have hle := hlin i j hne
  rw [hij, Finset.inter_self] at hle
  have hge := hcard j
  omega

/-- Universal Indexed-Hypergraph Cardinality Formula: under the hypotheses of
`injective_of_two_le_card_of_inter_card_le_one`, `(Finset.univ.image L).card = Fintype.card ι`. -/
theorem card_image_univ_eq_fintype_card_of_two_le_card_of_inter_card_le_one
    {ι : Type*} [Fintype ι] [DecidableEq V]
    (L : ι → Finset V) (hcard : ∀ i : ι, 2 ≤ (L i).card)
    (hlin : ∀ i j : ι, i ≠ j → (L i ∩ L j).card ≤ 1) :
    (Finset.univ.image L).card = Fintype.card ι := by
  rw [Finset.card_image_of_injective _ (injective_of_two_le_card_of_inter_card_le_one L hcard hlin),
    Finset.card_univ]

/-- Universal Indexed-Hypergraph Active-Vertices Coverage Lemma: if `L : V → Finset V` satisfies
`∀ v : V, v ∈ L v`, then `activeVertices (Finset.univ.image L) = Finset.univ` and
`(activeVertices (Finset.univ.image L)).card = Fintype.card V`. -/
theorem activeVertices_image_univ_eq_univ_of_forall_mem_self
    [Fintype V] [DecidableEq V] (L : V → Finset V) (hmem : ∀ v : V, v ∈ L v) :
    activeVertices (Finset.univ.image L) = Finset.univ ∧
      (activeVertices (Finset.univ.image L)).card = Fintype.card V := by
  have heq : activeVertices (Finset.univ.image L) = Finset.univ := by
    ext v
    simp only [Finset.mem_univ, iff_true]
    exact mem_activeVertices_of_mem_edge
      (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) (hmem v)
  exact ⟨heq, by rw [heq, Finset.card_univ]⟩

theorem projectivePlanePG23_card : projectivePlanePG23.card = 13 := by
  have h := card_image_univ_eq_fintype_card_of_two_le_card_of_inter_card_le_one pg23Line
    (fun i => by rw [pg23Line_card i]; decide) pg23Line_inter_card_le_one
  simpa [projectivePlanePG23] using h

theorem projectivePlanePG23_activeVertices_card :
    (activeVertices projectivePlanePG23).card = 13 := by
  have h := (activeVertices_image_univ_eq_univ_of_forall_mem_self pg23Line
    (fun v => by simp [pg23Line])).2
  simpa [projectivePlanePG23] using h

end Erdos836
