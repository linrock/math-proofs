module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 The Conject Contributors.
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
public import FourUniformCodimensionOneAvoidingBounds836

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 20000

open scoped BigOperators

/-!
# Erdős Problem #836: Degree-3 Vertex Replacement, Multi-Intersection Co-Degree Equations, and Universal Exclusion of `|E(H)| = 8` (`9 ≤ |E(H)|`)

This module establishes the degree-3 vertex replacement and sunflower theorems, rules out
`|E(H)| = 8` (proving `9 ≤ |E(H)|`) for 4-uniform 3-chromatic intersecting hypergraphs avoiding
pairwise intersection 3, proves the universal minimal-blue bipartite double-counting bound
`r ≤ 2t + 1` (adapting and generalizing the argument of Liam Price, 2026, and
`WoshuaJolk/jig-verifier`, `Submissions/Erdos836LinearEdgeIntersection/PricePort.lean`, Apache-2.0),
and constructs Noga Alon's general-`r` equitable-partition hypergraph to resolve both
`erdos_836.parts.i` and `erdos_836.parts.ii`.
-/

namespace Erdos836

variable {V : Type*}

/-! ## Section 1: Degree-3 Vertex Replacement, 2-Colourability Reductions & Sunflower Theorem -/

/-- Degree-3 Vertex Replacement Transversal Theorem: if `v ∈ e₀` belongs only to `e₀, e₁, e₂ ∈ H`
in an intersecting `r`-uniform hypergraph `H` (`r ≥ 2`), then for every `w ∈ e₁ ∩ e₂`,
`insert w (e₀.erase v)` is a transversal of `H`. -/
theorem isTransversal_insert_erase_of_forall_mem_imp_eq_or_eq_or_eq [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {e₀ e₁ e₂ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (honly : ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁ ∨ e = e₂)
    {w : V} (hw : w ∈ e₁ ∩ e₂) :
    IsTransversal H (insert w (e₀.erase v)) := by
  obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
  intro e he
  by_cases hve : v ∈ e
  · rcases honly e he hve with heq | heq | heq
    · rw [heq]
      have hcard : (e₀.erase v).card = r - 1 := by
        rw [Finset.card_erase_of_mem hv, hunif e₀ he₀]
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (e₀.erase v).card)
      exact ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hu, Finset.mem_insert_of_mem hu⟩⟩
    · rw [heq]
      exact ⟨w, Finset.mem_inter.mpr ⟨hw₁, Finset.mem_insert_self w _⟩⟩
    · rw [heq]
      exact ⟨w, Finset.mem_inter.mpr ⟨hw₂, Finset.mem_insert_self w _⟩⟩
  · have havoid : e ∈ vertexAvoidingEdges H v := Finset.mem_filter.mpr ⟨he, hve⟩
    obtain ⟨u, hu⟩ :=
      isTransversal_vertexAvoidingEdges_erase_of_isIntersecting hinter he₀ v e havoid
    rw [Finset.mem_inter] at hu
    exact ⟨u, Finset.mem_inter.mpr ⟨hu.1, Finset.mem_insert_of_mem hu.2⟩⟩

/-- Degree-3 Vertex Replacement Edge-Membership Theorem: if `v ∈ e₀` belongs only to `e₀, e₁, e₂`
in a non-2-colourable intersecting `r`-uniform hypergraph `H` (`r ≥ 2`), then for every
`w ∈ e₁ ∩ e₂`, `insert w (e₀.erase v) ∈ H`. -/
theorem insert_erase_mem_of_forall_mem_imp_eq_or_eq_or_eq_of_not_isTwoColorable [DecidableEq V]
    {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    {e₀ e₁ e₂ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (honly : ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁ ∨ e = e₂)
    {w : V} (hw : w ∈ e₁ ∩ e₂) :
    insert w (e₀.erase v) ∈ H := by
  have hT :=
    isTransversal_insert_erase_of_forall_mem_imp_eq_or_eq_or_eq hr hunif hinter he₀ hv honly hw
  obtain ⟨f, hf, hsub⟩ := exists_edge_subset_of_isTransversal_of_not_isTwoColorable hnot2 hT
  have hcard_le : (insert w (e₀.erase v)).card ≤ f.card := by
    have h1 : (insert w (e₀.erase v)).card ≤ (e₀.erase v).card + 1 := Finset.card_insert_le _ _
    rw [Finset.card_erase_of_mem hv, hunif e₀ he₀] at h1
    rw [hunif f hf]
    omega
  have heq : f = insert w (e₀.erase v) := Finset.eq_of_subset_of_card_le hsub hcard_le
  rwa [← heq]

/-- Degree-3 Vertex Replacement 2-Colourability Reduction: if `v ∈ e₀` belongs only to
`e₀, e₁, e₂ ∈ H` in an intersecting `r`-uniform hypergraph `H` (`r ≥ 2`) and there exists
`w ∈ e₁ ∩ e₂` such that `insert w (e₀.erase v) ∉ H`, then `IsTwoColorable H`. -/
theorem isTwoColorable_of_forall_mem_imp_eq_or_eq_or_eq_of_not_mem [DecidableEq V]
    {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) {e₀ e₁ e₂ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (honly : ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁ ∨ e = e₂)
    {w : V} (hw : w ∈ e₁ ∩ e₂) (hnot_mem : insert w (e₀.erase v) ∉ H) :
    IsTwoColorable H := by
  by_contra hnot2
  exact hnot_mem
    (insert_erase_mem_of_forall_mem_imp_eq_or_eq_or_eq_of_not_isTwoColorable
      hr hunif hinter hnot2 he₀ hv honly hw)

/-- If `v ∈ e₀` belongs only to `e₀, e₁, e₂ ∈ H` in a non-2-colourable intersecting `r`-uniform
hypergraph `H` (`r ≥ 2`) and there exists `w ∈ e₁ ∩ e₂` with `w ∉ e₀`, then `H` contains two
distinct edges meeting in at least `r - 1` vertices. -/
theorem hasPairwiseIntersectionAtLeast_sub_one_of_forall_mem_imp_eq_or_eq_or_eq_of_not_mem
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    {e₀ e₁ e₂ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (honly : ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁ ∨ e = e₂)
    {w : V} (hw : w ∈ e₁ ∩ e₂) (hw_not : w ∉ e₀) :
    HasPairwiseIntersectionAtLeast H (r - 1) := by
  have hf_mem :=
    insert_erase_mem_of_forall_mem_imp_eq_or_eq_or_eq_of_not_isTwoColorable
      hr hunif hinter hnot2 he₀ hv honly hw
  have hf_ne : insert w (e₀.erase v) ≠ e₀ := by
    intro heq
    have hw_in : w ∈ insert w (e₀.erase v) := Finset.mem_insert_self w _
    rw [heq] at hw_in
    exact hw_not hw_in
  have hsub_inter : e₀.erase v ⊆ (insert w (e₀.erase v)) ∩ e₀ := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx, Finset.mem_of_mem_erase hx⟩
  have hcard_inter : r - 1 ≤ ((insert w (e₀.erase v)) ∩ e₀).card := by
    have hle := Finset.card_le_card hsub_inter
    rw [Finset.card_erase_of_mem hv, hunif e₀ he₀] at hle
    exact hle
  exact ⟨insert w (e₀.erase v), hf_mem, e₀, he₀, hf_ne, hcard_inter⟩

/-- Under codimension-one avoidance (`¬ HasPairwiseIntersectionAtLeast H (r - 1)`), if `v ∈ e₀`
belongs only to `e₀, e₁, e₂ ∈ H` in a non-2-colourable intersecting `r`-uniform hypergraph `H`
(`r ≥ 2`), then `e₁ ∩ e₂ ⊆ e₀`. -/
theorem inter_subset_of_forall_mem_imp_eq_or_eq_or_eq_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₀ e₁ e₂ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (honly : ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁ ∨ e = e₂) :
    e₁ ∩ e₂ ⊆ e₀ := by
  intro w hw
  by_contra hw_not
  exact hno
    (hasPairwiseIntersectionAtLeast_sub_one_of_forall_mem_imp_eq_or_eq_or_eq_of_not_mem
      hr hunif hinter hnot2 he₀ hv honly hw hw_not)

/-- Codimension-One Avoiding Degree-3 2-Colourability Reduction: if `H` (`r ≥ 2`) is an
intersecting `r`-uniform hypergraph avoiding pairwise intersection `r - 1`, `v ∈ e₀ ∈ H` belongs
only to `e₀, e₁, e₂`, and `¬ e₁ ∩ e₂ ⊆ e₀`, then `IsTwoColorable H`. -/
theorem isTwoColorable_of_forall_mem_imp_eq_or_eq_or_eq_of_not_subset_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₀ e₁ e₂ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀)
    (honly : ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁ ∨ e = e₂)
    (hnot_sub : ¬ e₁ ∩ e₂ ⊆ e₀) :
    IsTwoColorable H := by
  by_contra hnot2
  exact hnot_sub
    (inter_subset_of_forall_mem_imp_eq_or_eq_or_eq_of_not_hasPairwiseIntersectionAtLeast_sub_one
      hr hunif hinter hnot2 hno he₀ hv honly)

/-- If `e₀, e₁, e₂ ∈ H` are pairwise distinct edges containing `v` and `vertexDegree H v ≤ 3`,
then every edge `e ∈ H` containing `v` is one of `e₀, e₁, e₂`. -/
theorem forall_mem_imp_eq_or_eq_or_eq_of_vertexDegree_le_three [DecidableEq V]
    {H : Finset (Finset V)} {e₀ e₁ e₂ : Finset V}
    (he₀ : e₀ ∈ H) (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H)
    (hne10 : e₁ ≠ e₀) (hne20 : e₂ ≠ e₀) (hne21 : e₂ ≠ e₁)
    {v : V} (hv₀ : v ∈ e₀) (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂)
    (hdeg : vertexDegree H v ≤ 3) :
    ∀ e ∈ H, v ∈ e → e = e₀ ∨ e = e₁ ∨ e = e₂ := by
  have hsub : ({e₂, e₁, e₀} : Finset (Finset V)) ⊆ H.filter (fun e => v ∈ e) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [Finset.mem_filter]
    rcases he with rfl | rfl | rfl
    · exact ⟨he₂, hv₂⟩
    · exact ⟨he₁, hv₁⟩
    · exact ⟨he₀, hv₀⟩
  have hnot_mem : e₂ ∉ ({e₁, e₀} : Finset (Finset V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne21, hne20⟩
  have hcard_triple : ({e₂, e₁, e₀} : Finset (Finset V)).card = 3 := by
    rw [Finset.card_insert_of_notMem hnot_mem, Finset.card_pair hne10]
  have hle : (H.filter (fun e => v ∈ e)).card ≤ ({e₂, e₁, e₀} : Finset (Finset V)).card := by
    rw [hcard_triple]
    exact hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  intro e he hve
  have hmem : e ∈ ({e₂, e₁, e₀} : Finset (Finset V)) := by
    rw [heq, Finset.mem_filter]
    exact ⟨he, hve⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

/-- If two distinct edges `e₁, e₂ ∈ H` with `2 ≤ (e₁ ∩ e₂).card` in a non-2-colourable
intersecting `r`-uniform hypergraph `H` (`r ≥ 2`) share a vertex `v ∈ e₁ ∩ e₂` of degree
`vertexDegree H v ≤ 3`, then `HasPairwiseIntersectionAtLeast H (r - 1)`. -/
theorem hasPairwiseIntersectionAtLeast_sub_one_of_vertexDegree_le_three_of_two_le_card_inter
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    {e₁ e₂ : Finset V} (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H) (hne21 : e₂ ≠ e₁)
    (hcard : 2 ≤ (e₁ ∩ e₂).card) {v : V} (hv : v ∈ e₁ ∩ e₂)
    (hdeg : vertexDegree H v ≤ 3) :
    HasPairwiseIntersectionAtLeast H (r - 1) := by
  by_contra hno
  obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
  obtain ⟨e₀, he₀, heq_sing, hv₀, hne01⟩ :=
    exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable
      hr hunif hinter hnot2 he₁ hv₁
  have hne20 : e₂ ≠ e₀ := by
    intro h_eq
    subst h_eq
    rw [Finset.inter_comm] at heq_sing
    rw [heq_sing, Finset.card_singleton] at hcard
    omega
  have honly :=
    forall_mem_imp_eq_or_eq_or_eq_of_vertexDegree_le_three
      he₀ he₁ he₂ hne01.symm hne20 hne21 hv₀ hv₁ hv₂ hdeg
  have hsub_e₀ :=
    inter_subset_of_forall_mem_imp_eq_or_eq_or_eq_of_not_hasPairwiseIntersectionAtLeast_sub_one
      hr hunif hinter hnot2 hno he₀ hv₀ honly
  have hsub_sing : e₁ ∩ e₂ ⊆ {v} := by
    rw [← heq_sing]
    exact Finset.subset_inter hsub_e₀ Finset.inter_subset_left
  have hle1 := Finset.card_le_card hsub_sing
  rw [Finset.card_singleton] at hle1
  omega

/-- Degree-3 Multi-Intersection 2-Colourability Reduction: if an intersecting `r`-uniform
hypergraph `H` (`r ≥ 2`) avoids pairwise intersection `r - 1` and two distinct edges `e₁, e₂ ∈ H`
with `2 ≤ (e₁ ∩ e₂).card` share a vertex `v ∈ e₁ ∩ e₂` of degree `≤ 3`, then `IsTwoColorable H`. -/
theorem isTwoColorable_of_vertexDegree_le_three_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₁ e₂ : Finset V} (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H) (hne21 : e₂ ≠ e₁)
    (hcard : 2 ≤ (e₁ ∩ e₂).card) {v : V} (hv : v ∈ e₁ ∩ e₂)
    (hdeg : vertexDegree H v ≤ 3) :
    IsTwoColorable H := by
  by_contra hnot2
  exact hno
    (hasPairwiseIntersectionAtLeast_sub_one_of_vertexDegree_le_three_of_two_le_card_inter
      hr hunif hinter hnot2 he₁ he₂ hne21 hcard hv hdeg)

/-- **Universal Multi-Intersection Degree-4 Theorem**: for `r ≥ 2`, in any non-2-colourable
intersecting `r`-uniform hypergraph `H` avoiding pairwise intersection `r - 1`, every vertex
`v ∈ e₁ ∩ e₂` belonging to the intersection of two distinct edges `e₁, e₂ ∈ H` with
`2 ≤ (e₁ ∩ e₂).card` satisfies `4 ≤ vertexDegree H v`. -/
theorem four_le_vertexDegree_of_mem_inter_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₁ e₂ : Finset V} (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H) (hne21 : e₂ ≠ e₁)
    (hcard : 2 ≤ (e₁ ∩ e₂).card) {v : V} (hv : v ∈ e₁ ∩ e₂) :
    4 ≤ vertexDegree H v := by
  by_contra hlt
  exact hno
    (hasPairwiseIntersectionAtLeast_sub_one_of_vertexDegree_le_three_of_two_le_card_inter
      hr hunif hinter hnot2 he₁ he₂ hne21 hcard hv (by omega))

/-- For `r ≥ 2`, in any non-2-colourable intersecting `r`-uniform hypergraph `H` avoiding pairwise
intersection `r - 1`, for every `e₀ ∈ H`, every `e₁ ∈ multiInterEdges H e₀`, and every
`v ∈ e₁ ∩ e₀`, `4 ≤ vertexDegree H v`. -/
theorem four_le_vertexDegree_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₀ e₁ : Finset V} (he₀ : e₀ ∈ H) (he₁ : e₁ ∈ multiInterEdges H e₀)
    {v : V} (hv : v ∈ e₁ ∩ e₀) :
    4 ≤ vertexDegree H v := by
  unfold multiInterEdges at he₁
  obtain ⟨herase, hne1⟩ := Finset.mem_filter.mp he₁
  obtain ⟨hne10, he₁_H⟩ := Finset.mem_erase.mp herase
  have hpos : 1 ≤ (e₁ ∩ e₀).card := Finset.Nonempty.card_pos (hinter e₁ he₁_H e₀ he₀)
  exact four_le_vertexDegree_of_mem_inter_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one
    hr hunif hinter hnot2 hno he₁_H he₀ hne10.symm (by omega) hv

/-- **Degree-3 Sunflower Cardinality Theorem**: for `r ≥ 2`, in any non-2-colourable intersecting
`r`-uniform hypergraph `H` avoiding pairwise intersection `r - 1`, if `vertexDegree H v ≤ 3`, then
any two distinct edges `e₁, e₂ ∈ H` containing `v` satisfy `(e₁ ∩ e₂).card = 1`. -/
theorem card_inter_eq_one_of_vertexDegree_le_three_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₁ e₂ : Finset V} (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H) (hne21 : e₂ ≠ e₁)
    {v : V} (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) (hdeg : vertexDegree H v ≤ 3) :
    (e₁ ∩ e₂).card = 1 := by
  have hpos : 1 ≤ (e₁ ∩ e₂).card := Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hv₁, hv₂⟩⟩
  have hle1 : (e₁ ∩ e₂).card ≤ 1 := by
    by_contra hgt
    have h4 :=
      four_le_vertexDegree_of_mem_inter_of_two_le_card_inter_of_not_hasPairwiseIntersectionAtLeast_sub_one
        hr hunif hinter hnot2 hno he₁ he₂ hne21 (by omega) (Finset.mem_inter.mpr ⟨hv₁, hv₂⟩)
    omega
  omega

/-- **Degree-3 Sunflower Core Theorem**: for `r ≥ 2`, in any non-2-colourable intersecting
`r`-uniform hypergraph `H` avoiding pairwise intersection `r - 1`, if `vertexDegree H v ≤ 3`, then
any two distinct edges `e₁, e₂ ∈ H` containing `v` intersect strictly at `{v}` (`e₁ ∩ e₂ = {v}`). -/
theorem inter_eq_singleton_of_vertexDegree_le_three_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    {e₁ e₂ : Finset V} (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H) (hne21 : e₂ ≠ e₁)
    {v : V} (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) (hdeg : vertexDegree H v ≤ 3) :
    e₁ ∩ e₂ = {v} := by
  have hc :=
    card_inter_eq_one_of_vertexDegree_le_three_of_not_hasPairwiseIntersectionAtLeast_sub_one
      hr hunif hinter hnot2 hno he₁ he₂ hne21 hv₁ hv₂ hdeg
  have hsub : ({v} : Finset V) ⊆ e₁ ∩ e₂ :=
    Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hv₁, hv₂⟩)
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc, Finset.card_singleton])).symm

/-- **3-Regular Linearity Theorem**: for `r ≥ 2`, if every active vertex of a non-2-colourable
intersecting `r`-uniform hypergraph `H` avoiding pairwise intersection `r - 1` has degree at most
`3`, then `H` is a linear hypergraph (`IsLinearHypergraph H`). -/
theorem isLinearHypergraph_of_forall_vertexDegree_le_three_of_not_hasPairwiseIntersectionAtLeast_sub_one
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1))
    (hdeg3 : ∀ v ∈ activeVertices H, vertexDegree H v ≤ 3) :
    IsLinearHypergraph H := by
  intro e₁ he₁ e₂ he₂ hne
  obtain ⟨v, hv⟩ := hinter e₁ he₁ e₂ he₂
  obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
  have hv_act : v ∈ activeVertices H := mem_activeVertices_of_mem_edge he₁ hv₁
  have hc :=
    card_inter_eq_one_of_vertexDegree_le_three_of_not_hasPairwiseIntersectionAtLeast_sub_one
      hr hunif hinter hnot2 hno he₁ he₂ hne.symm hv₁ hv₂ (hdeg3 v hv_act)
  omega

/-! ## Section 2: Multi-Intersection Co-Degree Equations & Second-Moment Degree Identities -/

/-- **Universal Weighted Double-Counting Identity**: for any hypergraph `H` and any vertex weight
function `f : V → ℕ`, `∑ e ∈ H, ∑ v ∈ e, f v = ∑ v ∈ activeVertices H, vertexDegree H v * f v`. -/
theorem sum_sum_edge_eq_sum_activeVertices_vertexDegree_mul [DecidableEq V]
    (H : Finset (Finset V)) (f : V → ℕ) :
    ∑ e ∈ H, ∑ v ∈ e, f v = ∑ v ∈ activeVertices H, vertexDegree H v * f v := by
  have h1 : ∑ e ∈ H, ∑ v ∈ e, f v =
      ∑ e ∈ H, ∑ v ∈ activeVertices H, (if v ∈ e then f v else 0) := by
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [← Finset.sum_filter]
    have hfilter : (activeVertices H).filter (fun v => v ∈ e) = e := by
      ext v
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun hv => mem_activeVertices_of_mem_edge he hv
    rw [hfilter]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  rfl

/-- **Universal Second-Moment Degree Identity**: for any hypergraph `H`,
`∑ e₀ ∈ H, ∑ v ∈ e₀, vertexDegree H v = ∑ v ∈ activeVertices H, vertexDegree H v ^ 2`. -/
theorem sum_sum_vertexDegree_eq_sum_activeVertices_sq [DecidableEq V]
    (H : Finset (Finset V)) :
    ∑ e₀ ∈ H, ∑ v ∈ e₀, vertexDegree H v = ∑ v ∈ activeVertices H, vertexDegree H v ^ 2 := by
  rw [sum_sum_edge_eq_sum_activeVertices_vertexDegree_mul]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

/-- **Global Multi-Intersection Second-Moment Equation**: in any intersecting `r`-uniform
hypergraph `H` avoiding pairwise intersection `3`,
`∑ v ∈ activeVertices H, vertexDegree H v ^ 2 = H.card * (r + (H.card - 1)) + ∑ e₀ ∈ H, (multiInterEdges H e₀).card`. -/
theorem sum_activeVertices_vertexDegree_sq_eq_card_mul_add_sum_card_multiInterEdges
    [DecidableEq V] {r : ℕ} {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    ∑ v ∈ activeVertices H, vertexDegree H v ^ 2 =
      H.card * (r + (H.card - 1)) + ∑ e₀ ∈ H, (multiInterEdges H e₀).card := by
  rw [← sum_sum_vertexDegree_eq_sum_activeVertices_sq]
  have hcongr : ∑ e₀ ∈ H, ∑ v ∈ e₀, vertexDegree H v =
      ∑ e₀ ∈ H, ((r + (H.card - 1)) + (multiInterEdges H e₀).card) := by
    refine Finset.sum_congr rfl (fun e₀ he₀ => ?_)
    exact sum_vertexDegree_eq_r_add_card_sub_one_add_card_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
      hunif hinter hno3 he₀
  rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]

/-- **Universal Multi-Intersection Vertex-Degree Lower Bound**: for `r ≥ 2`, in any non-2-colourable
intersecting `r`-uniform hypergraph `H`, for every edge `e₀ ∈ H` and vertex `v ∈ e₀`,
`2 + ((multiInterEdges H e₀).filter (fun e => v ∈ e)).card ≤ vertexDegree H v`. -/
theorem two_add_card_filter_multiInterEdges_le_vertexDegree_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) {v : V} (hv : v ∈ e₀) :
    2 + ((multiInterEdges H e₀).filter (fun e => v ∈ e)).card ≤ vertexDegree H v := by
  obtain ⟨g, hg, hg_sing, hvg, hne_g⟩ :=
    exists_edge_inter_eq_singleton_of_mem_edge_of_not_isTwoColorable hr hunif hinter hnot2 he₀ hv
  let M := (multiInterEdges H e₀).filter (fun e => v ∈ e)
  have he₀_not_M : e₀ ∉ M := by
    intro hmem
    unfold M multiInterEdges at hmem
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1).1 rfl
  have hg_not_M : g ∉ M := by
    intro hmem
    unfold M multiInterEdges at hmem
    have hne1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
    rw [hg_sing, Finset.card_singleton] at hne1
    exact hne1 rfl
  have he₀_not_ins : e₀ ∉ insert g M := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne_g.symm, he₀_not_M⟩
  have hsub : insert e₀ (insert g M) ⊆ H.filter (fun e => v ∈ e) := by
    intro e he
    simp only [Finset.mem_insert] at he
    rw [Finset.mem_filter]
    rcases he with rfl | rfl | heM
    · exact ⟨he₀, hv⟩
    · exact ⟨hg, hvg⟩
    · unfold M multiInterEdges at heM
      obtain ⟨he_multi, hve⟩ := Finset.mem_filter.mp heM
      exact ⟨Finset.mem_of_mem_erase (Finset.mem_filter.mp he_multi).1, hve⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem he₀_not_ins, Finset.card_insert_of_notMem hg_not_M] at hle
  dsimp only [M] at hle
  unfold vertexDegree
  omega

/-- **Universal Subset Degree-Boost Inequality**: for any `r`-uniform hypergraph `H`, edge `e₀ ∈ H`,
subset `S ⊆ e₀`, and degree threshold `k ≥ 3`, if `∀ v ∈ e₀, 3 ≤ vertexDegree H v` and
`∀ v ∈ S, k ≤ vertexDegree H v`, then `3 * r + S.card * (k - 3) ≤ ∑ v ∈ e₀, vertexDegree H v`. -/
theorem three_mul_r_add_card_mul_sub_three_le_sum_vertexDegree_of_subset
    [DecidableEq V] {r k : ℕ} (hk : 3 ≤ k) {H : Finset (Finset V)} (hunif : IsUniform r H)
    {e₀ S : Finset V} (he₀ : e₀ ∈ H) (hS : S ⊆ e₀)
    (hdeg3 : ∀ v ∈ e₀, 3 ≤ vertexDegree H v)
    (hdegk : ∀ v ∈ S, k ≤ vertexDegree H v) :
    3 * r + S.card * (k - 3) ≤ ∑ v ∈ e₀, vertexDegree H v := by
  have hsplit := (Finset.sum_sdiff hS (f := vertexDegree H)).symm
  have h1 : ∑ _v ∈ e₀ \ S, 3 ≤ ∑ v ∈ e₀ \ S, vertexDegree H v :=
    Finset.sum_le_sum (fun v hv => hdeg3 v (Finset.mem_sdiff.mp hv).1)
  have h2 : ∑ _v ∈ S, k ≤ ∑ v ∈ S, vertexDegree H v :=
    Finset.sum_le_sum hdegk
  rw [Finset.sum_const, smul_eq_mul] at h1 h2
  have hcard := Finset.card_sdiff_add_card_eq_card hS
  rw [hunif e₀ he₀] at hcard
  have hmul : (e₀ \ S).card * 3 + S.card * k = 3 * r + S.card * (k - 3) := by
    have hk_eq : k = 3 + (k - 3) := by omega
    calc (e₀ \ S).card * 3 + S.card * k
        = (e₀ \ S).card * 3 + S.card * (3 + (k - 3)) := by rw [← hk_eq]
      _ = ((e₀ \ S).card + S.card) * 3 + S.card * (k - 3) := by ring
      _ = 3 * r + S.card * (k - 3) := by rw [hcard, mul_comm]
  omega

/-! ## Section 3: Ruling Out `|E(H)| = 8` (`9 ≤ |E(H)|`) on `|V(H)| ∈ {9, 10}` & `|E(H)| = 9` Frontier Bounds -/

/-- At `r = 4`, in any non-2-colourable intersecting 4-uniform hypergraph `H` avoiding pairwise
intersection `3`, every edge `e₀ ∈ H` with `(multiInterEdges H e₀).Nonempty` satisfies
`14 ≤ ∑ v ∈ e₀, vertexDegree H v`. -/
theorem fourteen_le_sum_vertexDegree_of_r_eq_four_of_nonempty_multiInterEdges
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) (hne : (multiInterEdges H e₀).Nonempty) :
    14 ≤ ∑ v ∈ e₀, vertexDegree H v := by
  obtain ⟨e₁, he₁⟩ := hne
  have hcard2 :=
    card_inter_eq_two_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
      hinter hno3 he₀ he₁
  have hdeg :=
    three_mul_r_add_card_mul_sub_three_le_sum_vertexDegree_of_subset
      (k := 4) (by decide) hunif he₀ Finset.inter_subset_right
      (fun v hv =>
        three_le_vertexDegree_of_mem_edge_of_not_hasPairwiseIntersectionAtLeast_sub_one
          (by decide) hunif hinter hnot2 hno3 he₀ hv)
      (fun v hv =>
        four_le_vertexDegree_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_sub_one
          (by decide) hunif hinter hnot2 hno3 he₀ he₁ hv)
  rw [hcard2] at hdeg
  omega

/-- At `r = 4`, in any non-2-colourable intersecting 4-uniform hypergraph `H` avoiding pairwise
intersection `3`, every edge `e₀ ∈ H` with `(multiInterEdges H e₀).Nonempty` satisfies
`11 ≤ H.card + (multiInterEdges H e₀).card`. -/
theorem eleven_le_card_add_card_multiInterEdges_of_r_eq_four_of_nonempty_multiInterEdges
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) (hne : (multiInterEdges H e₀).Nonempty) :
    11 ≤ H.card + (multiInterEdges H e₀).card := by
  have h14 :=
    fourteen_le_sum_vertexDegree_of_r_eq_four_of_nonempty_multiInterEdges
      hunif hinter hnot2 hno3 he₀ hne
  have heq :=
    sum_vertexDegree_eq_card_add_three_add_card_multiInterEdges_of_r_eq_four
      hunif hinter hno3 he₀
  omega

/-- At `r = 4`, if `e₁ ∈ multiInterEdges H e₀` and every `e ∈ multiInterEdges H e₀` shares the
same 2-vertex intersection `e ∩ e₀ = e₁ ∩ e₀`, then both vertices of `e₁ ∩ e₀` have degree at
least `2 + (multiInterEdges H e₀).card`, forcing `7 + (multiInterEdges H e₀).card ≤ H.card`. -/
theorem seven_add_card_multiInterEdges_le_card_of_forall_inter_eq_of_r_eq_four
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ e₁ : Finset V} (he₀ : e₀ ∈ H) (he₁ : e₁ ∈ multiInterEdges H e₀)
    (h_all : ∀ e ∈ multiInterEdges H e₀, e ∩ e₀ = e₁ ∩ e₀) :
    7 + (multiInterEdges H e₀).card ≤ H.card := by
  have hcard2 :=
    card_inter_eq_two_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
      hinter hno3 he₀ he₁
  have hm_ge1 : 1 ≤ (multiInterEdges H e₀).card := Finset.card_pos.mpr ⟨e₁, he₁⟩
  have hdeg :=
    three_mul_r_add_card_mul_sub_three_le_sum_vertexDegree_of_subset
      (k := 2 + (multiInterEdges H e₀).card) (by omega) hunif he₀ Finset.inter_subset_right
      (fun v hv =>
        three_le_vertexDegree_of_mem_edge_of_not_hasPairwiseIntersectionAtLeast_sub_one
          (by decide) hunif hinter hnot2 hno3 he₀ hv)
      (fun v hv => by
        have h2 :=
          two_add_card_filter_multiInterEdges_le_vertexDegree_of_not_isTwoColorable
            (by decide) hunif hinter hnot2 he₀ (Finset.inter_subset_right hv)
        have hfilt : (multiInterEdges H e₀).filter (fun e => v ∈ e) = multiInterEdges H e₀ := by
          refine Finset.filter_eq_self.mpr (fun e he => ?_)
          have hv_in : v ∈ e ∩ e₀ := by rwa [h_all e he]
          exact (Finset.mem_inter.mp hv_in).1
        rwa [hfilt] at h2)
  rw [hcard2] at hdeg
  have heq :=
    sum_vertexDegree_eq_card_add_three_add_card_multiInterEdges_of_r_eq_four
      hunif hinter hno3 he₀
  omega

/-- At `r = 4`, if `multiInterEdges H e₀` contains two edges `e₁, e₂` with distinct 2-vertex
intersections `e₂ ∩ e₀ ≠ e₁ ∩ e₀`, then `(e₁ ∩ e₀) ∪ (e₂ ∩ e₀) ⊆ e₀` contains at least `3`
vertices of degree `≥ 4`, forcing `15 ≤ ∑ v ∈ e₀, vertexDegree H v`. -/
theorem fifteen_le_sum_vertexDegree_of_exists_inter_ne_of_r_eq_four
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    {e₀ e₁ e₂ : Finset V} (he₀ : e₀ ∈ H)
    (he₁ : e₁ ∈ multiInterEdges H e₀) (he₂ : e₂ ∈ multiInterEdges H e₀)
    (hne : e₂ ∩ e₀ ≠ e₁ ∩ e₀) :
    15 ≤ ∑ v ∈ e₀, vertexDegree H v := by
  let U := (e₁ ∩ e₀) ∪ (e₂ ∩ e₀)
  have hU_sub : U ⊆ e₀ := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have hc1 :=
    card_inter_eq_two_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
      hinter hno3 he₀ he₁
  have hc2 :=
    card_inter_eq_two_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_three
      hinter hno3 he₀ he₂
  have hU_ge3 : 3 ≤ U.card := by
    by_contra hlt
    have hle2 : U.card ≤ 2 := by omega
    have h1_eq : e₁ ∩ e₀ = U :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have h2_eq : e₂ ∩ e₀ = U :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    exact hne (h2_eq.trans h1_eq.symm)
  have hdeg :=
    three_mul_r_add_card_mul_sub_three_le_sum_vertexDegree_of_subset
      (k := 4) (by decide) hunif he₀ hU_sub
      (fun v hv =>
        three_le_vertexDegree_of_mem_edge_of_not_hasPairwiseIntersectionAtLeast_sub_one
          (by decide) hunif hinter hnot2 hno3 he₀ hv)
      (fun v hv => by
        rcases Finset.mem_union.mp hv with hv1 | hv2
        · exact four_le_vertexDegree_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_sub_one
            (by decide) hunif hinter hnot2 hno3 he₀ he₁ hv1
        · exact four_le_vertexDegree_of_mem_multiInterEdges_of_not_hasPairwiseIntersectionAtLeast_sub_one
            (by decide) hunif hinter hnot2 hno3 he₀ he₂ hv2)
  omega

/-- **Universal Edge Lower Bound (`9 ≤ H.card`) for 4-Uniform Non-2-Colourable Intersecting
Hypergraphs Avoiding Pairwise Intersection `3` (Resolves Saved `next_task`)**:
Every non-2-colourable intersecting 4-uniform hypergraph `H` avoiding pairwise intersection `3`
has at least `9` hyperedges (`9 ≤ H.card`). -/
theorem nine_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    9 ≤ H.card := by
  obtain ⟨e₀, he₀⟩ := nonempty_of_not_isTwoColorable hnot2
  by_cases hne : (multiInterEdges H e₀).Nonempty
  · obtain ⟨e₁, he₁⟩ := hne
    by_cases h_all : ∀ e ∈ multiInterEdges H e₀, e ∩ e₀ = e₁ ∩ e₀
    · have h1 :=
        eleven_le_card_add_card_multiInterEdges_of_r_eq_four_of_nonempty_multiInterEdges
          hunif hinter hnot2 hno3 he₀ ⟨e₁, he₁⟩
      have h2 :=
        seven_add_card_multiInterEdges_le_card_of_forall_inter_eq_of_r_eq_four
          hunif hinter hnot2 hno3 he₀ he₁ h_all
      omega
    · push Not at h_all
      obtain ⟨e₂, he₂, hne12⟩ := h_all
      have h15 :=
        fifteen_le_sum_vertexDegree_of_exists_inter_ne_of_r_eq_four
          hunif hinter hnot2 hno3 he₀ he₁ he₂ hne12
      have heq :=
        sum_vertexDegree_eq_card_add_three_add_card_multiInterEdges_of_r_eq_four
          hunif hinter hno3 he₀
      have hmulti :=
        card_multiInterEdges_add_r_le_card_sub_one_of_not_isTwoColorable
          (by decide) hunif hinter hnot2 he₀
      omega
  · have h_emp : (multiInterEdges H e₀).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    have h9 :=
      nine_le_card_add_card_multiInterEdges_of_r_eq_four
        hunif hinter hnot2 hno3 he₀
    omega

/-- **Universal Edge Lower Bound (`9 ≤ H.card`) for 4-Uniform 3-Chromatic Intersecting Hypergraphs
Avoiding Pairwise Intersection `3`**:
Every 3-chromatic intersecting 4-uniform hypergraph `H` avoiding pairwise intersection `3`
has at least `9` hyperedges (`9 ≤ H.card`). -/
theorem nine_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hchrom : HasChromaticNumberThree H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    9 ≤ H.card :=
  nine_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    hunif hinter hchrom.2 hno3

/-- **Universal 2-Colourability of `≤ 8`-Edge 4-Uniform Intersecting Hypergraphs Avoiding
Pairwise Intersection `3`**: every intersecting 4-uniform hypergraph `H` avoiding pairwise
intersection `3` with `H.card ≤ 8` is 2-colourable (`IsTwoColorable H`). -/
theorem isTwoColorable_of_r_eq_four_of_card_le_eight_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    (hle8 : H.card ≤ 8) :
    IsTwoColorable H := by
  by_contra hnot2
  have h9 :=
    nine_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
      hunif hinter hnot2 hno3
  omega

/-- **Explicit Exclusion of `|E(H)| = 8` on `|V(H)| ∈ {9, 10}` (and all `|V(H)|`)**:
No 4-uniform 3-chromatic intersecting hypergraph `H` avoiding pairwise intersection `3` can
satisfy `H.card = 8`. -/
theorem card_ne_eight_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hchrom : HasChromaticNumberThree H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    H.card ≠ 8 := by
  have h9 :=
    nine_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
      hunif hinter hchrom hno3
  omega

/-- At the new threshold `H.card = 9` for `r = 4` avoiding pairwise intersection `3`, no edge
`e₀ ∈ H` can have `(multiInterEdges H e₀).card = 1`. -/
theorem card_multiInterEdges_ne_one_of_r_eq_four_of_card_eq_nine
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) (hcard9 : H.card = 9)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    (multiInterEdges H e₀).card ≠ 1 := by
  intro heq1
  have hne : (multiInterEdges H e₀).Nonempty := Finset.card_pos.mp (by omega)
  have h11 :=
    eleven_le_card_add_card_multiInterEdges_of_r_eq_four_of_nonempty_multiInterEdges
      hunif hinter hnot2 hno3 he₀ hne
  omega

/-- At the threshold `H.card = 9` for `r = 4` avoiding pairwise intersection `3`, every edge
`e₀ ∈ H` satisfies `(multiInterEdges H e₀).card = 0 ∨ (2 ≤ (multiInterEdges H e₀).card ∧ (multiInterEdges H e₀).card ≤ 4)`. -/
theorem card_multiInterEdges_profile_of_r_eq_four_of_card_eq_nine
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) (hcard9 : H.card = 9)
    {e₀ : Finset V} (he₀ : e₀ ∈ H) :
    (multiInterEdges H e₀).card = 0 ∨
      (2 ≤ (multiInterEdges H e₀).card ∧ (multiInterEdges H e₀).card ≤ 4) := by
  have hne1 :=
    card_multiInterEdges_ne_one_of_r_eq_four_of_card_eq_nine
      hunif hinter hnot2 hno3 hcard9 he₀
  have hle :=
    card_multiInterEdges_add_r_le_card_sub_one_of_not_isTwoColorable
      (by decide) hunif hinter hnot2 he₀
  omega

/-- At the threshold `H.card = 9` for `r = 4` avoiding pairwise intersection `3`, every active
vertex `v ∈ activeVertices H` satisfies `3 ≤ vertexDegree H v ∧ vertexDegree H v ≤ 7`. -/
theorem vertexDegree_bounds_of_r_eq_four_of_card_eq_nine_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) (hcard9 : H.card = 9)
    {v : V} (hv : v ∈ activeVertices H) :
    3 ≤ vertexDegree H v ∧ vertexDegree H v ≤ 7 := by
  have hge :=
    three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
      (by decide) hunif hinter hnot2 hno3 hv
  have hle :=
    vertexDegree_add_eleven_le_two_mul_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
      hunif hinter hnot2 hno3 hv
  omega

/-! ## Section 4: Universal Minimal-Blue Double-Counting Bound (`r ≤ 2t + 1`), Linear Nonexistence for `r ≥ 4`, and `|E(H)| = 9` Active-Vertex Bounds -/

/-
The minimal-blue bipartite double-counting proof of `r_le_two_mul_add_one_of_forall_card_inter_le`
below adapts and generalizes the `Fin N` proof from `WoshuaJolk/jig-verifier`
(`Submissions/Erdos836LinearEdgeIntersection/PricePort.lean`, Apache-2.0, formalizing Liam Price,
"A Linear Intersection Bound", April 2026) to arbitrary vertex types `V` with `[DecidableEq V]`.
-/

/-- A subset `B : Finset V` is a proper bipartition class for `H` if every edge `e ∈ H` contains
at least one vertex in `B` and at least one vertex outside `B`. -/
def IsProperBipartitionSet [DecidableEq V] (H : Finset (Finset V)) (B : Finset V) : Prop :=
  ∀ e ∈ H, (e ∩ B).Nonempty ∧ (e \ B).Nonempty

/-- Any hypergraph `H` admitting a proper bipartition set `B` is 2-colourable. -/
theorem isTwoColorable_of_isProperBipartitionSet [DecidableEq V]
    {H : Finset (Finset V)} {B : Finset V} (h : IsProperBipartitionSet H B) :
    IsTwoColorable H := by
  refine ⟨subsetColoring B, ?_⟩
  intro e he
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h e he
  obtain ⟨hxe, hxB⟩ := Finset.mem_inter.mp hx
  obtain ⟨hye, hyB⟩ := Finset.mem_sdiff.mp hy
  refine ⟨x, hxe, y, hye, ?_⟩
  simp [subsetColoring, hxB, hyB]

/-- In any intersecting `r`-uniform hypergraph `H` (`A ∈ H`), `activeVertices H \ A` is disjoint
from `A` and is a proper bipartition set for `H.erase A`. -/
theorem initial_isProperBipartitionSet_sdiff [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {A : Finset V} (hA : A ∈ H) :
    Disjoint A (activeVertices H \ A) ∧
      IsProperBipartitionSet (H.erase A) (activeVertices H \ A) := by
  refine ⟨disjoint_sdiff_self_right, ?_⟩
  intro e he
  obtain ⟨hne, heH⟩ := Finset.mem_erase.mp he
  constructor
  · have hnot : ¬ e ⊆ A := by
      intro hsub
      exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [hunif A hA, hunif e heH]))
    obtain ⟨x, hxe, hxA⟩ := Finset.not_subset.mp hnot
    exact ⟨x, Finset.mem_inter.mpr ⟨hxe, Finset.mem_sdiff.mpr ⟨mem_activeVertices_of_mem_edge heH hxe, hxA⟩⟩⟩
  · obtain ⟨x, hx⟩ := hinter e heH A hA
    obtain ⟨hxe, hxA⟩ := Finset.mem_inter.mp hx
    refine ⟨x, Finset.mem_sdiff.mpr ⟨hxe, ?_⟩⟩
    intro hxB
    exact (Finset.mem_sdiff.mp hxB).2 hxA

/-- Every intersecting `r`-uniform hypergraph `H` (`A ∈ H`) admits a minimum-cardinality subset
`B ⊆ activeVertices H` disjoint from `A` that is a proper bipartition set for `H.erase A`. -/
theorem exists_minimal_properBipartitionSet [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    {A : Finset V} (hA : A ∈ H) :
    ∃ B : Finset V, B ⊆ activeVertices H ∧ Disjoint A B ∧
      IsProperBipartitionSet (H.erase A) B ∧
      ∀ C : Finset V, C ⊆ activeVertices H → Disjoint A C →
        IsProperBipartitionSet (H.erase A) C → B.card ≤ C.card := by
  classical
  let choices : Finset (Finset V) :=
    (activeVertices H).powerset.filter (fun B =>
      Disjoint A B ∧ IsProperBipartitionSet (H.erase A) B)
  have hinit := initial_isProperBipartitionSet_sdiff hunif hinter hA
  have hne : choices.Nonempty := by
    refine ⟨activeVertices H \ A, Finset.mem_filter.mpr ⟨?_, hinit⟩⟩
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  obtain ⟨B, hB, hmin⟩ := choices.exists_min_image Finset.card hne
  obtain ⟨hB_pow, hB_disj, hB_prop⟩ := Finset.mem_filter.mp hB
  refine ⟨B, Finset.mem_powerset.mp hB_pow, hB_disj, hB_prop, ?_⟩
  intro C hC_sub hC_disj hC_prop
  exact hmin C (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC_sub, hC_disj, hC_prop⟩)

/-- Red-Flip Witness Lemma: for every vertex `x ∈ A` of an anchor edge `A ∈ H` in a
non-2-colourable `r`-uniform hypergraph `H` (`r ≥ 2`), flipping `x` into `B` forces an edge
`F ∈ H` (`F ≠ A`) with `F \ B = {x}`. -/
theorem exists_edge_sdiff_eq_singleton_of_mem_anchor [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hnot2 : ¬ IsTwoColorable H)
    {A B : Finset V} (hA : A ∈ H) (hd : Disjoint A B)
    (hp : IsProperBipartitionSet (H.erase A) B) {x : V} (hx : x ∈ A) :
    ∃ F ∈ H, F ≠ A ∧ F \ B = {x} := by
  have hnot : ¬ IsProperBipartitionSet H (insert x B) :=
    fun h => hnot2 (isTwoColorable_of_isProperBipartitionSet h)
  unfold IsProperBipartitionSet at hnot
  push Not at hnot
  obtain ⟨F, hF, hbad⟩ := hnot
  have hFA : F ≠ A := by
    intro heq
    subst heq
    have h1 : (F ∩ insert x B).Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_insert_self x B⟩⟩
    have hcard : 0 < (F.erase x).card := by
      rw [Finset.card_erase_of_mem hx, hunif F hF]
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
    obtain ⟨hyx, hyF⟩ := Finset.mem_erase.mp hy
    have h2 : (F \ insert x B).Nonempty := by
      refine ⟨y, Finset.mem_sdiff.mpr ⟨hyF, ?_⟩⟩
      simp only [Finset.mem_insert, not_or]
      exact ⟨hyx, Finset.disjoint_left.mp hd hyF⟩
    exact h2.ne_empty (hbad h1)
  have hprop := hp F (Finset.mem_erase.mpr ⟨hFA, hF⟩)
  have h1 : (F ∩ insert x B).Nonempty := by
    obtain ⟨b, hb⟩ := hprop.1
    obtain ⟨hbF, hbB⟩ := Finset.mem_inter.mp hb
    exact ⟨b, Finset.mem_inter.mpr ⟨hbF, Finset.mem_insert_of_mem hbB⟩⟩
  have hsub : F ⊆ insert x B := Finset.sdiff_eq_empty_iff_subset.mp (hbad h1)
  refine ⟨F, hF, hFA, Finset.Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨hyF, hyB⟩ := Finset.mem_sdiff.mp hy
    rw [Finset.mem_singleton]
    exact (Finset.mem_insert.mp (hsub hyF)).resolve_right hyB
  · obtain ⟨y, hy⟩ := hprop.2
    obtain ⟨hyF, hyB⟩ := Finset.mem_sdiff.mp hy
    have hyx : y = x := (Finset.mem_insert.mp (hsub hyF)).resolve_right hyB
    subst hyx
    exact Finset.singleton_subset_iff.mpr hy

/-- Blue-Flip Witness Lemma: by minimality of `B`, for every vertex `b ∈ B`, removing `b` from `B`
forces an edge `E ∈ H` (`E ≠ A`) with `E ∩ B = {b}`. -/
theorem exists_edge_inter_eq_singleton_of_minimal_properBipartitionSet [DecidableEq V]
    {H : Finset (Finset V)} {A B : Finset V}
    (hB_sub : B ⊆ activeVertices H) (hd : Disjoint A B)
    (hp : IsProperBipartitionSet (H.erase A) B)
    (hmin : ∀ C : Finset V, C ⊆ activeVertices H → Disjoint A C →
      IsProperBipartitionSet (H.erase A) C → B.card ≤ C.card)
    {b : V} (hb : b ∈ B) :
    ∃ E ∈ H, E ≠ A ∧ E ∩ B = {b} := by
  have hnot : ¬ IsProperBipartitionSet (H.erase A) (B.erase b) := by
    intro h
    have hle := hmin (B.erase b) (Finset.Subset.trans (Finset.erase_subset b B) hB_sub)
      (hd.mono_right (Finset.erase_subset b B)) h
    have hpos : 0 < B.card := Finset.card_pos.mpr ⟨b, hb⟩
    rw [Finset.card_erase_of_mem hb] at hle
    omega
  unfold IsProperBipartitionSet at hnot
  push Not at hnot
  obtain ⟨E, hE, hbad⟩ := hnot
  have hprop := hp E hE
  have hempty : ¬ (E ∩ B.erase b).Nonempty := by
    intro hne
    have h2 : (E \ B.erase b).Nonempty :=
      hprop.2.mono (Finset.sdiff_subset_sdiff Finset.Subset.rfl (Finset.erase_subset b B))
    exact h2.ne_empty (hbad hne)
  have hsub : E ∩ B ⊆ {b} := by
    intro z hz
    obtain ⟨hzE, hzB⟩ := Finset.mem_inter.mp hz
    rw [Finset.mem_singleton]
    by_contra hzb
    exact hempty ⟨z, Finset.mem_inter.mpr ⟨hzE, Finset.mem_erase.mpr ⟨hzb, hzB⟩⟩⟩
  obtain ⟨z, hz⟩ := hprop.1
  have hzb := Finset.mem_singleton.mp (hsub hz)
  subst hzb
  exact ⟨E, (Finset.mem_erase.mp hE).2, (Finset.mem_erase.mp hE).1,
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hz)⟩

/-- **Universal Minimal-Blue Double-Counting Pairwise Intersection Theorem (`r ≤ 2t + 1`)**:
In any non-2-colourable intersecting `r`-uniform hypergraph `H` (`r ≥ 2`) over any vertex type `V`
with `[DecidableEq V]`, if every pair of distinct edges meets in at most `t` vertices, then
`r ≤ 2 * t + 1`. -/
theorem r_le_two_mul_add_one_of_forall_card_inter_le [DecidableEq V] {r t : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H)
    (ht : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ t) :
    r ≤ 2 * t + 1 := by
  classical
  obtain ⟨A, hA⟩ := nonempty_of_not_isTwoColorable hnot2
  obtain ⟨B, hB_sub, hd, hp, hmin⟩ := exists_minimal_properBipartitionSet hunif hinter hA
  have hANE : A.Nonempty := Finset.card_pos.mp (by rw [hunif A hA]; omega)
  let hA_sub : Nonempty A := hANE.to_subtype
  choose F hFG hFA hred using fun x : A =>
    exists_edge_sdiff_eq_singleton_of_mem_anchor hr hunif hnot2 hA hd hp x.property
  have hxF (x : A) : x.val ∈ F x := by
    have h := Finset.mem_sdiff.mp ((hred x).symm ▸ Finset.mem_singleton_self x.val)
    exact h.1
  have hfred (x : A) (z : V) (hz : z ∈ F x) (hzB : z ∉ B) : z = x.val := by
    have : z ∈ F x \ B := Finset.mem_sdiff.mpr ⟨hz, hzB⟩
    rwa [hred x, Finset.mem_singleton] at this
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply hfred y x.val
    · rw [← hxy]; exact hxF x
    · exact Finset.disjoint_left.mp hd x.property
  have hdegree (b : V) (hb : b ∈ B) :
      r - t ≤ (Finset.univ.filter fun y : A => b ∈ F y).card := by
    obtain ⟨E, hE, hEA, hEB⟩ :=
      exists_edge_inter_eq_singleton_of_minimal_properBipartitionSet hB_sub hd hp hmin hb
    have hother : (Finset.univ.filter fun y : A => b ∉ F y).card ≤ (E ∩ A).card := by
      apply Finset.card_le_card_of_injOn (fun y : A => y.val)
      · intro y hy
        have hyb : b ∉ F y := (Finset.mem_filter.mp hy).2
        obtain ⟨z, hz⟩ := hinter E hE (F y) (hFG y)
        obtain ⟨hzE, hzF⟩ := Finset.mem_inter.mp hz
        have hzB : z ∉ B := by
          intro hzB
          have hzb : z = b := by
            have hz_in : z ∈ E ∩ B := Finset.mem_inter.mpr ⟨hzE, hzB⟩
            rwa [hEB, Finset.mem_singleton] at hz_in
          exact hyb (hzb ▸ hzF)
        have hzy := hfred y z hzF hzB
        exact Finset.mem_inter.mpr ⟨by simpa only [hzy] using hzE, y.property⟩
      · exact fun x _ y _ h => Subtype.ext h
    have hcount :
        (Finset.univ.filter fun y : A => b ∈ F y).card +
          (Finset.univ.filter fun y : A => b ∉ F y).card = r := by
      rw [Finset.card_filter_add_card_filter_not]
      simpa using hunif A hA
    have htE := ht E hE A hA hEA
    omega
  let x : A := Classical.choice hA_sub
  let P : Finset V := F x ∩ B
  have hP : P.card = r - 1 := by
    have h := Finset.card_inter_add_card_sdiff (F x) B
    rw [hred x, Finset.card_singleton, hunif (F x) (hFG x)] at h
    dsimp [P]
    omega
  have hdouble :
      (∑ y : A, (P.filter fun b => b ∈ F y).card) =
        ∑ b ∈ P, (Finset.univ.filter fun y : A => b ∈ F y).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun y : A => fun b : V => b ∈ F y)
  have hlower : P.card * (r - t) ≤ ∑ b ∈ P, (Finset.univ.filter fun y : A => b ∈ F y).card := by
    calc
      P.card * (r - t) = ∑ _b ∈ P, (r - t) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun b hb => hdegree b (Finset.mem_inter.mp hb).2
  have hdiag : (P.filter fun b => b ∈ F x).card = P.card := by
    congr 1
    apply Finset.filter_eq_self.mpr
    intro b hb
    exact (Finset.mem_inter.mp hb).1
  have hupper : (∑ y : A, (P.filter fun b => b ∈ F y).card) ≤ P.card + (r - 1) * t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x), hdiag]
    have hbound : (∑ y ∈ Finset.univ.erase x, (P.filter fun b => b ∈ F y).card) ≤ (r - 1) * t := by
      calc
        _ ≤ ∑ _y ∈ Finset.univ.erase x, t := by
          apply Finset.sum_le_sum
          intro y hy
          have hyx := (Finset.mem_erase.mp hy).1
          calc
            (P.filter fun b => b ∈ F y).card ≤ (F x ∩ F y).card := by
              apply Finset.card_le_card
              intro b hb
              obtain ⟨hbP, hby⟩ := Finset.mem_filter.mp hb
              exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbP).1, hby⟩
            _ ≤ t := ht (F x) (hFG x) (F y) (hFG y) (fun h => hyx (hFinj h).symm)
        _ = (r - 1) * t := by simp [hunif A hA, mul_comm]
    omega
  rw [← hdouble, hP] at hlower
  rw [hP] at hupper
  have hrt : r - t ≤ t + 1 := by
    by_contra hh
    have hh_lt : t + 1 < r - t := by omega
    have hmul := Nat.mul_lt_mul_of_pos_left hh_lt (by omega : 0 < r - 1)
    nlinarith
  omega

/-- **Universal Linear Hypergraph Rank Upper Bound (`r ≤ 3`)**: every non-2-colourable linear
intersecting `r`-uniform hypergraph (`r ≥ 2`) satisfies `r ≤ 3`. -/
theorem r_le_three_of_isLinearHypergraph_of_not_isTwoColorable [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) (hnot2 : ¬ IsTwoColorable H) :
    r ≤ 3 := by
  have h := r_le_two_mul_add_one_of_forall_card_inter_le hr hunif hinter hnot2 hlin
  omega

/-- **Universal 2-Colourability of Linear Intersecting Hypergraphs for `r ≥ 4`**: for every `r ≥ 4`,
every linear intersecting `r`-uniform hypergraph `H` is 2-colourable (`IsTwoColorable H`). -/
theorem isTwoColorable_of_four_le_r_of_isLinearHypergraph [DecidableEq V] {r : ℕ}
    (hr : 4 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hlin : IsLinearHypergraph H) :
    IsTwoColorable H := by
  by_contra hnot2
  have hle3 := r_le_three_of_isLinearHypergraph_of_not_isTwoColorable (by omega) hunif hinter hlin hnot2
  omega

/-- **Universal Pairwise-Intersection-2 Rank Upper Bound (`r ≤ 5`)**: every non-2-colourable
intersecting `r`-uniform hypergraph `H` (`r ≥ 2`) avoiding pairwise intersection `3` satisfies
`r ≤ 5`. -/
theorem r_le_five_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
    [DecidableEq V] {r : ℕ} (hr : 2 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H)
    (hinter : IsIntersecting H) (hnot2 : ¬ IsTwoColorable H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    r ≤ 5 := by
  have ht : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2 := by
    intro e he f hf hne
    by_contra hgt
    exact hno3 ⟨e, he, f, hf, hne, by omega⟩
  have h := r_le_two_mul_add_one_of_forall_card_inter_le hr hunif hinter hnot2 ht
  omega

/-- For `r ≥ 4`, every non-2-colourable intersecting `r`-uniform hypergraph `H` avoiding pairwise
intersection `r - 1` contains at least one active vertex of degree at least `4` (ruling out
3-regularity for all `r ≥ 4`). -/
theorem exists_activeVertex_four_le_vertexDegree_of_four_le_r [DecidableEq V] {r : ℕ}
    (hr : 4 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    ∃ v ∈ activeVertices H, 4 ≤ vertexDegree H v := by
  by_contra h_all
  push Not at h_all
  have hlin : IsLinearHypergraph H :=
    isLinearHypergraph_of_forall_vertexDegree_le_three_of_not_hasPairwiseIntersectionAtLeast_sub_one
      (by omega) hunif hinter hnot2 hno (fun v hv => by have := h_all v hv; omega)
  exact hnot2 (isTwoColorable_of_four_le_r_of_isLinearHypergraph hr hunif hinter hlin)

/-- **Sharpened Handshake Active-Vertex Inequality (`3|V(H)| + 1 ≤ r|E(H)|`) for `r ≥ 4`**:
In any non-2-colourable intersecting `r`-uniform hypergraph `H` (`r ≥ 4`) avoiding pairwise
intersection `r - 1`, `3 * (activeVertices H).card + 1 ≤ H.card * r`. -/
theorem three_mul_card_activeVertices_add_one_le_card_mul_r_of_four_le_r [DecidableEq V] {r : ℕ}
    (hr : 4 ≤ r) {H : Finset (Finset V)} (hunif : IsUniform r H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno : ¬ HasPairwiseIntersectionAtLeast H (r - 1)) :
    3 * (activeVertices H).card + 1 ≤ H.card * r := by
  obtain ⟨v₀, hv₀, hv₀_4⟩ :=
    exists_activeVertex_four_le_vertexDegree_of_four_le_r hr hunif hinter hnot2 hno
  have hhand := sum_vertexDegree_activeVertices_eq_card_mul_r hunif
  rw [← Finset.add_sum_erase (activeVertices H) (vertexDegree H) hv₀] at hhand
  have hsum : ∑ _v ∈ (activeVertices H).erase v₀, 3 ≤
      ∑ v ∈ (activeVertices H).erase v₀, vertexDegree H v :=
    Finset.sum_le_sum (fun v hv =>
      three_le_vertexDegree_of_not_hasPairwiseIntersectionAtLeast_sub_one_of_not_isTwoColorable
        (by omega) hunif hinter hnot2 hno (Finset.mem_of_mem_erase hv))
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hv₀] at hsum
  have hpos : 1 ≤ (activeVertices H).card := Finset.card_pos.mpr ⟨v₀, hv₀⟩
  omega

/-- At the threshold `H.card = 9` for `r = 4` avoiding pairwise intersection `3`, the number of
active vertices satisfies `9 ≤ (activeVertices H).card ∧ (activeVertices H).card ≤ 11` (ruling out
`(activeVertices H).card = 12`). -/
theorem card_activeVertices_bounds_of_r_eq_four_of_card_eq_nine [DecidableEq V]
    {H : Finset (Finset V)} (hunif : IsUniform 4 H) (hinter : IsIntersecting H)
    (hnot2 : ¬ IsTwoColorable H) (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3)
    (hcard9 : H.card = 9) :
    9 ≤ (activeVertices H).card ∧ (activeVertices H).card ≤ 11 := by
  have hge9 :=
    nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_not_isTwoColorable
      hunif hinter hnot2 hno3
  have hle :=
    three_mul_card_activeVertices_add_one_le_card_mul_r_of_four_le_r
      (by decide) hunif hinter hnot2 hno3
  omega

/-- **Combined Universal Edge & Active-Vertex Lower Bound Theorem (`9 ≤ |E(H)|`, `9 ≤ |V(H)|`,
`3|V(H)| + 1 ≤ 4|E(H)|`) for 4-Uniform 3-Chromatic Intersecting Hypergraphs Avoiding Pairwise
Intersection `3`**: -/
theorem nine_le_card_and_nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three
    [DecidableEq V] {H : Finset (Finset V)} (hunif : IsUniform 4 H)
    (hinter : IsIntersecting H) (hchrom : HasChromaticNumberThree H)
    (hno3 : ¬ HasPairwiseIntersectionAtLeast H 3) :
    9 ≤ H.card ∧ 9 ≤ (activeVertices H).card ∧
      3 * (activeVertices H).card + 1 ≤ H.card * 4 :=
  ⟨nine_le_card_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
      hunif hinter hchrom hno3,
   nine_le_card_activeVertices_of_r_eq_four_of_not_hasPairwiseIntersectionAtLeast_three_of_hasChromaticNumberThree
      hunif hinter hchrom hno3,
   three_mul_card_activeVertices_add_one_le_card_mul_r_of_four_le_r
      (by decide) hunif hinter hchrom.2 hno3⟩

end Erdos836

/-! ## Section 5: Zero-`sorry` Conditional & Unconditional Reductions to `FormalConjectures.ErdosProblems.«836»` -/

namespace Finset

variable {V : Type*}

/-- A family `F` of finite sets has **property B** (equivalently, chromatic number `2`) if there
is a `2`-colouring of the ground set under which no member of `F` is monochromatic. -/
def HasPropertyB (F : Finset (Finset V)) : Prop :=
  ∃ f : V → Fin 2, ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y

/-- Every edge has exactly `r` vertices (`FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite`). -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- A weak proper coloring has no monochromatic edge (`FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite`). -/
def IsProperHypergraphColoring (H : Finset (Finset V)) {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- The edge family admits a weak proper coloring with `k` colors (`FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite`). -/
def HypergraphColorable (H : Finset (Finset V)) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, H.IsProperHypergraphColoring c

/-- The weak chromatic number is exactly `k` (`FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite`). -/
def HasHypergraphChromaticNumber (H : Finset (Finset V)) (k : ℕ) : Prop :=
  H.HypergraphColorable k ∧ ∀ j < k, ¬ H.HypergraphColorable j

end Finset

namespace Erdos836

variable {V : Type*}

/-- Equivalence between `Finset.IsUniform H r` (`FormalConjectures`) and `Erdos836.IsUniform r H`. -/
theorem finset_isUniform_iff_isUniform {r : ℕ} {H : Finset (Finset V)} :
    H.IsUniform r ↔ IsUniform r H := Iff.rfl

/-- Equivalence between `Finset.HasPropertyB H` (`FormalConjectures`) and `Erdos836.IsTwoColorable H`. -/
theorem finset_hasPropertyB_iff_isTwoColorable {H : Finset (Finset V)} :
    H.HasPropertyB ↔ IsTwoColorable H := Iff.rfl

/-- Equivalence between `Finset.HypergraphColorable H k` (`FormalConjectures`) and `Erdos836.IsKColorable H k`. -/
theorem finset_hypergraphColorable_iff_isKColorable {k : ℕ} {H : Finset (Finset V)} :
    H.HypergraphColorable k ↔ IsKColorable H k := Iff.rfl

/-- Equivalence between `H.HasHypergraphChromaticNumber 3` (`FormalConjectures`) and
`Erdos836.HasChromaticNumberThree H`. -/
theorem finset_hasHypergraphChromaticNumber_three_iff_hasChromaticNumberThree
    {H : Finset (Finset V)} :
    H.HasHypergraphChromaticNumber 3 ↔ HasChromaticNumberThree H := by
  constructor
  · intro h
    exact ⟨h.1, h.2 2 (by decide)⟩
  · intro h
    refine ⟨h.1, fun j hj hjcol => ?_⟩
    exact h.2 (isKColorable_mono_colors (by omega : j ≤ 2) hjcol)

/-- Equivalence between `(H : Set (Finset V)).Intersecting` (`Mathlib`/`FormalConjectures`) and
`Erdos836.IsIntersecting H`. -/
theorem set_intersecting_iff_isIntersecting [DecidableEq V] {H : Finset (Finset V)} :
    (H : Set (Finset V)).Intersecting ↔ IsIntersecting H := by
  constructor
  · intro h e₁ he₁ e₂ he₂
    exact Finset.not_disjoint_iff_nonempty_inter.mp (h he₁ he₂)
  · intro h e₁ he₁ e₂ he₂
    exact Finset.not_disjoint_iff_nonempty_inter.mpr (h e₁ he₁ e₂ he₂)

/-- **Zero-`sorry` Conditional Disproof Reduction for `erdos_836.parts.i`**:
If for every `C > 0` there exists `r ≥ 2` and a 3-chromatic intersecting `r`-uniform hypergraph `H`
on `Fin n` with `C * (r : ℝ)^2 < ((activeVertices H).card : ℝ)`, then the literal RHS of
`erdos_836.parts.i` is `False`. -/
theorem not_erdos_836_parts_i_rhs_of_superquadratic_witnesses
    (h_alon : ∀ C : ℝ, 0 < C → ∃ r : ℕ, 2 ≤ r ∧
      ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
        IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
          C * (r : ℝ) ^ 2 < ((activeVertices H).card : ℝ)) :
    ¬ (∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ((H.biUnion id).card : ℝ) ≤ C * (r : ℝ) ^ 2) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨r, hr, n, H, hunif, hinter, hchrom, hgt⟩ := h_alon C hC
  have hle := hbound r hr n H
    (finset_isUniform_iff_isUniform.mpr hunif)
    (finset_hasHypergraphChromaticNumber_three_iff_hasChromaticNumberThree.mpr hchrom)
    (set_intersecting_iff_isIntersecting.mpr hinter)
  change ((activeVertices H).card : ℝ) ≤ C * (r : ℝ) ^ 2 at hle
  linarith

/-- **Exact Equivalence Between the `erdos_836.parts.ii` RHS and `Erdos836LinearIntersectionConjecture`**: -/
theorem erdos_836_parts_ii_rhs_iff_erdos836LinearIntersectionConjecture :
    (∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * (r : ℝ) ≤ ((e ∩ f).card : ℝ)) ↔
      Erdos836LinearIntersectionConjecture := by
  unfold Erdos836LinearIntersectionConjecture
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun r hr n H hunif hinter hchrom => ?_⟩
    exact h r hr n H
      (finset_isUniform_iff_isUniform.mpr hunif)
      (finset_hasHypergraphChromaticNumber_three_iff_hasChromaticNumberThree.mpr hchrom)
      (set_intersecting_iff_isIntersecting.mpr hinter)
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun r hr n H hunif hchrom hinter => ?_⟩
    exact h r hr n H
      (finset_isUniform_iff_isUniform.mp hunif)
      (set_intersecting_iff_isIntersecting.mp hinter)
      (finset_hasHypergraphChromaticNumber_three_iff_hasChromaticNumberThree.mp hchrom)

/-- **Unconditional Proof of `Erdos836LinearIntersectionConjecture` (`c = 1 / 3`)**: -/
theorem erdos836LinearIntersectionConjecture_proved :
    Erdos836LinearIntersectionConjecture := by
  refine ⟨1 / 3, by norm_num, ?_⟩
  intro r hr n H hunif hinter hchrom
  by_contra hnot
  have hle : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ (r - 1) / 3 := by
    intro e he f hf hne
    have hsmall : ¬ (1 / 3 : ℝ) * (r : ℝ) ≤ ((e ∩ f).card : ℝ) :=
      fun h => hnot ⟨e, he, f, hf, hne, h⟩
    have hreal : (3 : ℝ) * ((e ∩ f).card : ℝ) < (r : ℝ) := by linarith
    have hnat : 3 * (e ∩ f).card < r := by exact_mod_cast hreal
    omega
  have h := r_le_two_mul_add_one_of_forall_card_inter_le hr hunif hinter hchrom.2 hle
  omega

/-- **Unconditional Proof of the `FormalConjectures` `erdos_836.parts.ii` RHS (`c = 1 / 3`)**: -/
theorem erdos_836_parts_ii_rhs_proved :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * (r : ℝ) ≤ ((e ∩ f).card : ℝ) :=
  erdos_836_parts_ii_rhs_iff_erdos836LinearIntersectionConjecture.mpr
    erdos836LinearIntersectionConjecture_proved

/-- **Unconditional Proof of `erdos_836.parts.ii` (`True ↔ ...`)**: -/
theorem erdos_836_parts_ii_proved :
    True ↔ ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * (r : ℝ) ≤ ((e ∩ f).card : ℝ) :=
  ⟨fun _ => erdos_836_parts_ii_rhs_proved, fun _ => trivial⟩

end Erdos836

/-! ## Section 6: General-`r` Alon Equitable-Partition Hypergraph & Unconditional Disproof of `erdos_836.parts.i` -/

namespace Erdos836

variable {V W : Type*}

/-- Pushforward of a finite hypergraph `H` along an injective vertex map `f : V ↪ W`. -/
def mapHypergraph [DecidableEq V] [DecidableEq W] (f : V ↪ W) (H : Finset (Finset V)) :
    Finset (Finset W) :=
  H.map (Finset.mapEmbedding f).toEmbedding

/-- Pushing a hypergraph forward along an injection preserves `r`-uniformity. -/
theorem isUniform_mapHypergraph [DecidableEq V] [DecidableEq W] {r : ℕ}
    (f : V ↪ W) {H : Finset (Finset V)} (hunif : IsUniform r H) :
    IsUniform r (mapHypergraph f H) := by
  intro e he
  rcases Finset.mem_map.mp he with ⟨a, ha, rfl⟩
  simpa using hunif a ha

/-- Pushing a hypergraph forward along an injection preserves the intersecting property. -/
theorem isIntersecting_mapHypergraph [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) {H : Finset (Finset V)} (hinter : IsIntersecting H) :
    IsIntersecting (mapHypergraph f H) := by
  intro e₁ he₁ e₂ he₂
  rcases Finset.mem_map.mp he₁ with ⟨a₁, ha₁, rfl⟩
  rcases Finset.mem_map.mp he₂ with ⟨a₂, ha₂, rfl⟩
  obtain ⟨x, hx⟩ := hinter a₁ ha₁ a₂ ha₂
  rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
  exact ⟨f x, Finset.mem_inter.mpr ⟨Finset.mem_map_of_mem f hx1, Finset.mem_map_of_mem f hx2⟩⟩

/-- Pushing a non-2-colourable hypergraph forward along an injection preserves non-2-colourability. -/
theorem not_isTwoColorable_mapHypergraph [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) {H : Finset (Finset V)} (hnot2 : ¬ IsTwoColorable H) :
    ¬ IsTwoColorable (mapHypergraph f H) := by
  rintro ⟨c, hc⟩
  apply hnot2
  refine ⟨fun x => c (f x), fun e he => ?_⟩
  have he_map : e.map f ∈ mapHypergraph f H :=
    Finset.mem_map.mpr ⟨e, he, rfl⟩
  obtain ⟨u, hu, v, hv, hne⟩ := hc (e.map f) he_map
  rcases Finset.mem_map.mp hu with ⟨x, hx, rfl⟩
  rcases Finset.mem_map.mp hv with ⟨y, hy, rfl⟩
  exact ⟨x, hx, y, hy, hne⟩

/-- Pushing a hypergraph forward along an injection preserves the active-vertex count. -/
theorem card_activeVertices_mapHypergraph [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (H : Finset (Finset V)) :
    (activeVertices (mapHypergraph f H)).card = (activeVertices H).card := by
  have heq : activeVertices (mapHypergraph f H) = (activeVertices H).map f := by
    ext w
    simp [activeVertices, mapHypergraph]
    tauto
  rw [heq, Finset.card_map]

/-- Any non-zero element of `Fin 2` equals `1`. -/
theorem fin_two_eq_one_of_ne_zero {a : Fin 2} (ha : a ≠ 0) : a = 1 := by
  ext
  have hlt := a.isLt
  have hne : a.val ≠ 0 := fun h => ha (Fin.ext h)
  change a.val = 1
  omega

/-- Characterization of `a ≠ 0` in `Fin 2`. -/
theorem fin_two_ne_zero_iff_eq_one {a : Fin 2} : a ≠ 0 ↔ a = 1 :=
  ⟨fin_two_eq_one_of_ne_zero, by rintro rfl; decide⟩

/-- Half-central binomial identity `C(2r - 3, r - 2) = C(2r - 2, r - 1) / 2` for `r ≥ 2`. -/
theorem choose_two_mul_sub_three_eq_half {r : ℕ} (hr : 2 ≤ r) :
    Nat.choose (2 * r - 3) (r - 2) = Nat.choose (2 * r - 2) (r - 1) / 2 := by
  have h1 : 2 * r - 2 = (2 * r - 3) + 1 := by omega
  have h2 : r - 1 = (r - 2) + 1 := by omega
  have hsymm : Nat.choose (2 * r - 3) (r - 1) = Nat.choose (2 * r - 3) (r - 2) := by
    have hsub : 2 * r - 3 - (r - 1) = r - 2 := by omega
    rw [← hsub]
    exact (Nat.choose_symm (by omega : r - 1 ≤ 2 * r - 3)).symm
  have hpascal := Nat.choose_succ_succ (2 * r - 3) (r - 2)
  dsimp only [Nat.succ_eq_add_one] at hpascal
  rw [← h1, ← h2, hsymm] at hpascal
  omega

/-- Ambient vertex type for Alon's equitable-partition hypergraph of uniformity `r`. -/
abbrev AlonVertex (r : ℕ) := Fin (2 * r - 2) ⊕ Finset (Fin (2 * r - 2))

/-- Canonical representative of the 2-partition `{S, univ \ S}` of `Fin (2 * r - 2)`:
selects whichever part contains the base vertex with value `0`. -/
def alonCanonPart (r : ℕ) (S : Finset (Fin (2 * r - 2))) : Finset (Fin (2 * r - 2)) :=
  if ∃ x ∈ S, x.val = 0 then S else Finset.univ \ S

/-- Explicit `if-then-else` characterization of `alonCanonPart r S` for `r ≥ 2`. -/
theorem alonCanonPart_eq_ite {r : ℕ} (hr : 2 ≤ r) (S : Finset (Fin (2 * r - 2))) :
    let x₀ : Fin (2 * r - 2) := ⟨0, by omega⟩
    alonCanonPart r S = if x₀ ∈ S then S else Finset.univ \ S := by
  intro x₀
  unfold alonCanonPart
  have hiff : (∃ x ∈ S, x.val = 0) ↔ x₀ ∈ S := by
    constructor
    · rintro ⟨x, hx, hval⟩
      have hx0 : x = x₀ := Fin.ext hval
      rwa [← hx0]
    · intro hx₀
      exact ⟨x₀, hx₀, rfl⟩
  by_cases hx : x₀ ∈ S <;> simp [hiff, hx]

/-- Complement invariance of `alonCanonPart`: `S` and `univ \ S` map to the same canonical part. -/
theorem alonCanonPart_sdiff_univ {r : ℕ} (hr : 2 ≤ r) (S : Finset (Fin (2 * r - 2))) :
    alonCanonPart r (Finset.univ \ S) = alonCanonPart r S := by
  rw [alonCanonPart_eq_ite hr (Finset.univ \ S), alonCanonPart_eq_ite hr S]
  let x₀ : Fin (2 * r - 2) := ⟨0, by omega⟩
  by_cases hx : x₀ ∈ S <;> simp [hx]

/-- If `S` contains the base vertex `0`, then `alonCanonPart r S = S`. -/
theorem alonCanonPart_of_mem_zero {r : ℕ} {S : Finset (Fin (2 * r - 2))}
    {x₀ : Fin (2 * r - 2)} (hx₀ : x₀ ∈ S) (hval : x₀.val = 0) :
    alonCanonPart r S = S := by
  unfold alonCanonPart
  have hex : ∃ x ∈ S, x.val = 0 := ⟨x₀, hx₀, hval⟩
  simp [hex]

/-- Type-1 edge of Alon's hypergraph: an `r`-element subset `T ⊆ X`. -/
def alonType1Edge (r : ℕ) (T : Finset (Fin (2 * r - 2))) : Finset (AlonVertex r) :=
  T.map Function.Embedding.inl

/-- Type-2 edge of Alon's hypergraph: an `(r - 1)`-element subset `S ⊆ X` together with the
vertex in `Y` indexing the induced partition `{S, X \ S}`. -/
def alonType2Edge (r : ℕ) (S : Finset (Fin (2 * r - 2))) : Finset (AlonVertex r) :=
  insert (Sum.inr (alonCanonPart r S)) (S.map Function.Embedding.inl)

/-- All Type-1 edges of Alon's hypergraph for uniformity `r`. -/
def alonType1Family (r : ℕ) : Finset (Finset (AlonVertex r)) :=
  ((Finset.univ : Finset (Fin (2 * r - 2))).powersetCard r).image (alonType1Edge r)

/-- All Type-2 edges of Alon's hypergraph for uniformity `r`. -/
def alonType2Family (r : ℕ) : Finset (Finset (AlonVertex r)) :=
  ((Finset.univ : Finset (Fin (2 * r - 2))).powersetCard (r - 1)).image (alonType2Edge r)

/-- Alon's equitable-partition hypergraph for uniformity `r` on `AlonVertex r`. -/
def alonSumHypergraph (r : ℕ) : Finset (Finset (AlonVertex r)) :=
  alonType1Family r ∪ alonType2Family r

theorem card_alonType1Edge {r : ℕ} (T : Finset (Fin (2 * r - 2))) :
    (alonType1Edge r T).card = T.card := by
  simp [alonType1Edge]

theorem card_alonType2Edge {r : ℕ} (S : Finset (Fin (2 * r - 2))) :
    (alonType2Edge r S).card = S.card + 1 := by
  unfold alonType2Edge
  rw [Finset.card_insert_of_notMem] <;> simp

/-- Alon's hypergraph `alonSumHypergraph r` is `r`-uniform for all `r ≥ 1`. -/
theorem isUniform_alonSumHypergraph {r : ℕ} (hr : 1 ≤ r) :
    IsUniform r (alonSumHypergraph r) := by
  intro e he
  rcases Finset.mem_union.mp he with he1 | he2
  · rcases Finset.mem_image.mp he1 with ⟨T, hT, rfl⟩
    rw [card_alonType1Edge, (Finset.mem_powersetCard.mp hT).2]
  · rcases Finset.mem_image.mp he2 with ⟨S, hS, rfl⟩
    rw [card_alonType2Edge, (Finset.mem_powersetCard.mp hS).2]
    omega

theorem nonempty_inter_of_card_add_gt {r : ℕ} {A B : Finset (Fin (2 * r - 2))}
    (hcard : 2 * r - 2 < A.card + B.card) :
    (A ∩ B).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hdisj : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr h
  have hunion : (A ∪ B).card ≤ 2 * r - 2 := by
    calc (A ∪ B).card ≤ (Finset.univ : Finset (Fin (2 * r - 2))).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = 2 * r - 2 := by simp
  rw [Finset.card_union_of_disjoint hdisj] at hunion
  omega

theorem eq_sdiff_univ_of_disjoint_of_card_eq {r : ℕ} {S₁ S₂ : Finset (Fin (2 * r - 2))}
    (h1 : S₁.card = r - 1) (h2 : S₂.card = r - 1) (hdisj : Disjoint S₁ S₂) :
    S₂ = Finset.univ \ S₁ := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.disjoint_left.mp hdisj.symm hx⟩
  · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _)]
    simp [h1, h2]
    omega

/-- Alon's hypergraph `alonSumHypergraph r` is intersecting for all `r ≥ 2`. -/
theorem isIntersecting_alonSumHypergraph {r : ℕ} (hr : 2 ≤ r) :
    IsIntersecting (alonSumHypergraph r) := by
  intro e₁ he₁ e₂ he₂
  rcases Finset.mem_union.mp he₁ with h1 | h1 <;> rcases Finset.mem_union.mp he₂ with h2 | h2
  · rcases Finset.mem_image.mp h1 with ⟨T₁, hT₁, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨T₂, hT₂, rfl⟩
    have hc1 := (Finset.mem_powersetCard.mp hT₁).2
    have hc2 := (Finset.mem_powersetCard.mp hT₂).2
    obtain ⟨x, hx⟩ := nonempty_inter_of_card_add_gt (A := T₁) (B := T₂) (by omega)
    rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
    refine ⟨Sum.inl x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;> simp [alonType1Edge, hx1, hx2]
  · rcases Finset.mem_image.mp h1 with ⟨T₁, hT₁, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨S₂, hS₂, rfl⟩
    have hc1 := (Finset.mem_powersetCard.mp hT₁).2
    have hc2 := (Finset.mem_powersetCard.mp hS₂).2
    obtain ⟨x, hx⟩ := nonempty_inter_of_card_add_gt (A := T₁) (B := S₂) (by omega)
    rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
    refine ⟨Sum.inl x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · simp [alonType1Edge, hx1]
    · simp [alonType2Edge, hx2]
  · rcases Finset.mem_image.mp h1 with ⟨S₁, hS₁, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨T₂, hT₂, rfl⟩
    have hc1 := (Finset.mem_powersetCard.mp hS₁).2
    have hc2 := (Finset.mem_powersetCard.mp hT₂).2
    obtain ⟨x, hx⟩ := nonempty_inter_of_card_add_gt (A := S₁) (B := T₂) (by omega)
    rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
    refine ⟨Sum.inl x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · simp [alonType2Edge, hx1]
    · simp [alonType1Edge, hx2]
  · rcases Finset.mem_image.mp h1 with ⟨S₁, hS₁, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨S₂, hS₂, rfl⟩
    have hc1 := (Finset.mem_powersetCard.mp hS₁).2
    have hc2 := (Finset.mem_powersetCard.mp hS₂).2
    by_cases hne : (S₁ ∩ S₂).Nonempty
    · obtain ⟨x, hx⟩ := hne
      rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
      refine ⟨Sum.inl x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;> simp [alonType2Edge, hx1, hx2]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hdisj : Disjoint S₁ S₂ := Finset.disjoint_iff_inter_eq_empty.mpr hne
      have heq : S₂ = Finset.univ \ S₁ := eq_sdiff_univ_of_disjoint_of_card_eq hc1 hc2 hdisj
      have hcanon : alonCanonPart r S₂ = alonCanonPart r S₁ := by
        rw [heq, alonCanonPart_sdiff_univ hr]
      refine ⟨Sum.inr (alonCanonPart r S₁), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [alonType2Edge]
      · simp [alonType2Edge, hcanon]

theorem card_filter_color_le_sub_one_of_isProperColoring {r : ℕ}
    {c : AlonVertex r → Fin 2} (hc : IsProperColoring (alonSumHypergraph r) c) (k : Fin 2) :
    ((Finset.univ : Finset (Fin (2 * r - 2))).filter (fun x => c (Sum.inl x) = k)).card ≤ r - 1 := by
  by_contra hlt
  have hge : r ≤ ((Finset.univ : Finset (Fin (2 * r - 2))).filter (fun x => c (Sum.inl x) = k)).card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
  have hTmem : alonType1Edge r T ∈ alonSumHypergraph r := by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩, rfl⟩
  obtain ⟨u, hu, v, hv, hne⟩ := hc (alonType1Edge r T) hTmem
  rcases Finset.mem_map.mp hu with ⟨x, hx, rfl⟩
  rcases Finset.mem_map.mp hv with ⟨y, hy, rfl⟩
  have hcx : c (Sum.inl x) = k := (Finset.mem_filter.mp (hTsub hx)).2
  have hcy : c (Sum.inl y) = k := (Finset.mem_filter.mp (hTsub hy)).2
  exact hne (hcx.trans hcy.symm)

/-- Alon's hypergraph `alonSumHypergraph r` is not 2-colourable for all `r ≥ 2`. -/
theorem not_isTwoColorable_alonSumHypergraph {r : ℕ} (hr : 2 ≤ r) :
    ¬ IsTwoColorable (alonSumHypergraph r) := by
  rintro ⟨c, hc⟩
  let X₀ := (Finset.univ : Finset (Fin (2 * r - 2))).filter (fun x => c (Sum.inl x) = 0)
  let X₁ := (Finset.univ : Finset (Fin (2 * r - 2))).filter (fun x => c (Sum.inl x) = 1)
  have h0_le : X₀.card ≤ r - 1 := card_filter_color_le_sub_one_of_isProperColoring hc 0
  have h1_le : X₁.card ≤ r - 1 := card_filter_color_le_sub_one_of_isProperColoring hc 1
  have hX₁_eq : X₁ = Finset.univ \ X₀ := by
    ext x
    simp only [X₀, X₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      fin_two_ne_zero_iff_eq_one]
  have hsum : X₀.card + X₁.card = 2 * r - 2 := by
    rw [hX₁_eq, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _)]
    have : X₀.card ≤ (Finset.univ : Finset (Fin (2 * r - 2))).card := Finset.card_le_card (Finset.subset_univ _)
    simp at this ⊢
    omega
  have h0_card : X₀.card = r - 1 := by omega
  have h1_card : X₁.card = r - 1 := by omega
  let P := alonCanonPart r X₀
  have hP1 : alonCanonPart r X₁ = P := by
    dsimp [P]
    rw [hX₁_eq, alonCanonPart_sdiff_univ hr]
  by_cases hcp : c (Sum.inr P) = 0
  · have hmem0 : alonType2Edge r X₀ ∈ alonSumHypergraph r := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨X₀, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h0_card⟩, rfl⟩
    obtain ⟨u, hu, v, hv, hne⟩ := hc (alonType2Edge r X₀) hmem0
    have hcol : ∀ w ∈ alonType2Edge r X₀, c w = 0 := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw1
      · exact hcp
      · rcases Finset.mem_map.mp hw1 with ⟨x, hx, rfl⟩
        exact (Finset.mem_filter.mp hx).2
    exact hne ((hcol u hu).trans (hcol v hv).symm)
  · have hcp1 : c (Sum.inr P) = 1 := fin_two_eq_one_of_ne_zero hcp
    have hmem1 : alonType2Edge r X₁ ∈ alonSumHypergraph r := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨X₁, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h1_card⟩, rfl⟩
    obtain ⟨u, hu, v, hv, hne⟩ := hc (alonType2Edge r X₁) hmem1
    have hcol : ∀ w ∈ alonType2Edge r X₁, c w = 1 := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw1
      · rw [hP1]; exact hcp1
      · rcases Finset.mem_map.mp hw1 with ⟨x, hx, rfl⟩
        exact (Finset.mem_filter.mp hx).2
    exact hne ((hcol u hu).trans (hcol v hv).symm)

/-- Active-vertex lower bound for `alonSumHypergraph r`:
`alonVertexCount r ≤ (activeVertices (alonSumHypergraph r)).card` for all `r ≥ 2`. -/
theorem alonVertexCount_le_card_activeVertices_alonSumHypergraph {r : ℕ} (hr : 2 ≤ r) :
    alonVertexCount r ≤ (activeVertices (alonSumHypergraph r)).card := by
  let x₀ : Fin (2 * r - 2) := ⟨0, by omega⟩
  let Xset : Finset (AlonVertex r) :=
    (Finset.univ : Finset (Fin (2 * r - 2))).map Function.Embedding.inl
  let Ybase : Finset (Finset (Fin (2 * r - 2))) :=
    (((Finset.univ : Finset (Fin (2 * r - 2))).erase x₀).powersetCard (r - 2))
  let Yset : Finset (AlonVertex r) :=
    Ybase.image (fun A => Sum.inr (insert x₀ A))
  have hXsub : Xset ⊆ activeVertices (alonSumHypergraph r) := by
    intro v hv
    rcases Finset.mem_map.mp hv with ⟨x, _, rfl⟩
    have hcard_er : ((Finset.univ : Finset (Fin (2 * r - 2))).erase x).card = 2 * r - 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x)]
      simp
      omega
    obtain ⟨B, hBsub, hBcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 * r - 2))).erase x)
        (n := r - 2) (by omega)
    let S := insert x B
    have hxB : x ∉ B := fun h => (Finset.mem_erase.mp (hBsub h)).1 rfl
    have hScard : S.card = r - 1 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem hxB, hBcard]
      omega
    have hSmem : alonType2Edge r S ∈ alonSumHypergraph r := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩, rfl⟩
    refine mem_activeVertices_of_mem_edge hSmem ?_
    apply Finset.mem_insert_of_mem
    exact Finset.mem_map.mpr ⟨x, Finset.mem_insert_self x B, rfl⟩
  have hYsub : Yset ⊆ activeVertices (alonSumHypergraph r) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨A, hA, rfl⟩
    rcases Finset.mem_powersetCard.mp hA with ⟨hAsub, hAcard⟩
    have hx₀A : x₀ ∉ A := fun h => (Finset.mem_erase.mp (hAsub h)).1 rfl
    let S := insert x₀ A
    have hScard : S.card = r - 1 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem hx₀A, hAcard]
      omega
    have hSmem : alonType2Edge r S ∈ alonSumHypergraph r := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩, rfl⟩
    have hcanon : alonCanonPart r S = S :=
      alonCanonPart_of_mem_zero (Finset.mem_insert_self x₀ A) rfl
    refine mem_activeVertices_of_mem_edge hSmem ?_
    unfold alonType2Edge
    rw [hcanon]
    exact Finset.mem_insert_self _ _
  have hdisj : Disjoint Xset Yset := by
    rw [Finset.disjoint_left]
    intro v hvX hvY
    rcases Finset.mem_map.mp hvX with ⟨x, _, rfl⟩
    rcases Finset.mem_image.mp hvY with ⟨A, _, h_eq⟩
    simp at h_eq
  have hYcard : Yset.card = Nat.choose (2 * r - 3) (r - 2) := by
    dsimp [Yset]
    rw [Finset.card_image_of_injOn]
    · dsimp [Ybase]
      rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ x₀)]
      simp [show 2 * r - 2 - 1 = 2 * r - 3 by omega]
    · intro A₁ hA₁ A₂ hA₂ h_eq
      injection h_eq with hins
      have hx1 : x₀ ∉ A₁ := fun h => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hA₁).1 h)).1 rfl
      have hx2 : x₀ ∉ A₂ := fun h => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hA₂).1 h)).1 rfl
      have her := congrArg (fun S : Finset (Fin (2 * r - 2)) => S.erase x₀) hins
      simpa [Finset.erase_insert hx1, Finset.erase_insert hx2] using her
  have hXcard : Xset.card = 2 * r - 2 := by
    dsimp [Xset]
    simp
  have hunion_le : (Xset ∪ Yset).card ≤ (activeVertices (alonSumHypergraph r)).card :=
    Finset.card_le_card (Finset.union_subset hXsub hYsub)
  rw [Finset.card_union_of_disjoint hdisj, hXcard, hYcard, choose_two_mul_sub_three_eq_half hr] at hunion_le
  exact hunion_le

/-- **Alon's Equitable-Partition Construction on `Fin n` for All `r ≥ 2`**:
For every `r ≥ 2`, there exist `n : ℕ` and an `r`-uniform intersecting 3-chromatic hypergraph `H`
on `Fin n` with at least `alonVertexCount r = (2r - 2) + C(2r - 2, r - 1) / 2` active vertices. -/
theorem exists_alon_fin_hypergraph {r : ℕ} (hr : 2 ≤ r) :
    ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
      IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
        alonVertexCount r ≤ (activeVertices H).card := by
  let f := (Fintype.equivFin (AlonVertex r)).toEmbedding
  let H := mapHypergraph f (alonSumHypergraph r)
  have hunif : IsUniform r H :=
    isUniform_mapHypergraph f (isUniform_alonSumHypergraph (by omega))
  have hinter : IsIntersecting H :=
    isIntersecting_mapHypergraph f (isIntersecting_alonSumHypergraph hr)
  have hnot2 : ¬ IsTwoColorable H :=
    not_isTwoColorable_mapHypergraph f (not_isTwoColorable_alonSumHypergraph hr)
  have hchrom : HasChromaticNumberThree H :=
    (hasChromaticNumberThree_iff_not_isTwoColorable_of_isIntersecting hr hunif hinter).mpr hnot2
  refine ⟨Fintype.card (AlonVertex r), H, hunif, hinter, hchrom, ?_⟩
  rw [card_activeVertices_mapHypergraph]
  exact alonVertexCount_le_card_activeVertices_alonSumHypergraph hr

/-- Elementary exponential growth inequality `(m + 2) * (m + 10)^2 < 2^(m + 8)` for all `m : ℕ`. -/
theorem mul_add_ten_sq_lt_two_pow (m : ℕ) :
    (m + 2) * (m + 10) ^ 2 < 2 ^ (m + 8) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hstep : (m + 1 + 2) * (m + 1 + 10) ^ 2 ≤ 2 * ((m + 2) * (m + 10) ^ 2) := by
      have hm2 : 0 ≤ m ^ 2 := Nat.zero_le _
      have hm3 : 0 ≤ m ^ 3 := Nat.zero_le _
      linarith
    have hpow : 2 ^ (m + 1 + 8) = 2 * 2 ^ (m + 8) := by
      rw [show m + 1 + 8 = (m + 8) + 1 by omega, pow_succ, mul_comm]
    omega

/-- **Unconditional Disproof of `Erdos836QuadraticVertexQuestion`**:
There is no constant `C > 0` bounding the active-vertex count of every 3-chromatic intersecting
`r`-uniform hypergraph by `C * r^2`. -/
theorem not_erdos836QuadraticVertexQuestion : ¬ Erdos836QuadraticVertexQuestion := by
  rintro ⟨C, _, hbound⟩
  let r := C + 10
  have hr : 2 ≤ r := by omega
  obtain ⟨n, H, hunif, hinter, hchrom, hcard⟩ := exists_alon_fin_hypergraph hr
  have hle := hbound r hr n H hunif hinter hchrom
  have h1 := mul_add_ten_sq_lt_two_pow C
  have h2 := two_pow_sub_two_add_two_mul_r_sub_two_le_alonVertexCount r hr
  dsimp [r] at h2 hcard hle
  rw [show C + 10 - 2 = C + 8 by omega] at h2
  have hmul : C * (C + 10) ^ 2 ≤ (C + 2) * (C + 10) ^ 2 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- For every real constant `C`, there exists `r ≥ 2` and a 3-chromatic intersecting `r`-uniform
hypergraph `H` on `Fin n` with `C * (r : ℝ)^2 < ((activeVertices H).card : ℝ)`. -/
theorem exists_superquadratic_alon_witness (C : ℝ) :
    ∃ r : ℕ, 2 ≤ r ∧
      ∃ (n : ℕ) (H : Finset (Finset (Fin n))),
        IsUniform r H ∧ IsIntersecting H ∧ HasChromaticNumberThree H ∧
          C * (r : ℝ) ^ 2 < ((activeVertices H).card : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt C
  let r := m + 10
  have hr : 2 ≤ r := by omega
  obtain ⟨n, H, hunif, hinter, hchrom, hcard⟩ := exists_alon_fin_hypergraph hr
  refine ⟨r, hr, n, H, hunif, hinter, hchrom, ?_⟩
  have hlt_nat : (m + 2) * r ^ 2 < (activeVertices H).card := by
    have h1 := mul_add_ten_sq_lt_two_pow m
    have h2 := two_pow_sub_two_add_two_mul_r_sub_two_le_alonVertexCount r hr
    dsimp [r] at h2 hcard ⊢
    rw [show m + 10 - 2 = m + 8 by omega] at h2
    omega
  have hlt_real : (((m + 2) * r ^ 2 : ℕ) : ℝ) < ((activeVertices H).card : ℝ) := by
    exact_mod_cast hlt_nat
  push_cast at hlt_real
  have hr_pos : 0 < (r : ℝ) ^ 2 := by positivity
  nlinarith

/-- **Unconditional Refutation of the `FormalConjectures` `erdos_836.parts.i` RHS**: -/
theorem not_erdos_836_parts_i_rhs_proved :
    ¬ (∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ((H.biUnion id).card : ℝ) ≤ C * (r : ℝ) ^ 2) :=
  not_erdos_836_parts_i_rhs_of_superquadratic_witnesses (fun C _ => exists_superquadratic_alon_witness C)

/-- **Unconditional Proof of `erdos_836.parts.i` (`False ↔ ...`)**: -/
theorem erdos_836_parts_i_proved :
    False ↔ ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
        H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
          (H : Set (Finset (Fin n))).Intersecting →
            ((H.biUnion id).card : ℝ) ≤ C * (r : ℝ) ^ 2 :=
  ⟨False.elim, not_erdos_836_parts_i_rhs_proved⟩

end Erdos836
