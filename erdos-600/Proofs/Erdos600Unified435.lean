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


open Finset SimpleGraph Asymptotics Filter

namespace SimpleGraph

open Finset

open scoped Classical in
/-- The triangles of `G` containing the edge `uv`, that is, the `3`-cliques of `G` whose vertex
set contains both endpoints of `uv`. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α)
    (uv : Sym2 α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.toFinset ⊆ t)

end SimpleGraph

namespace Erdos600

section DefinitionsAndFoundations
open scoped Classical

/--
Let $e(n,r)$ be minimal such that every graph on $n$ vertices with at least $e(n,r)$ edges,
each edge contained in at least one triangle, must have an edge contained in at least
$r$ triangles.
-/
def Erdos600Prop (n : ℕ) (e : ℕ) (r : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.edgeFinset.card ≥ e →
  (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) →
  ∃ uv ∈ G.edgeFinset, r ≤ (G.trianglesContaining uv).card

noncomputable def eFunction (n : ℕ) (r : ℕ) : ℕ := sInf {e : ℕ | Erdos600Prop n e r}

theorem erdos600Prop_mono_edges {n e₁ e₂ r : ℕ} (he : e₁ ≤ e₂)
    (h : Erdos600Prop n e₁ r) : Erdos600Prop n e₂ r := by
  intro G hG htri
  exact h G (he.trans hG) htri

theorem erdos600Prop_anti_triangles {n e r₁ r₂ : ℕ} (hr : r₁ ≤ r₂)
    (h : Erdos600Prop n e r₂) : Erdos600Prop n e r₁ := by
  intro G hG htri
  obtain ⟨uv, huv, hcard⟩ := h G hG htri
  exact ⟨uv, huv, hr.trans hcard⟩

theorem erdos600Prop_choose_two_succ (n r : ℕ) :
    Erdos600Prop n (n.choose 2 + 1) r := by
  intro G hG _
  have hmax : G.edgeFinset.card ≤ n.choose 2 := by
    simpa using SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
  omega

theorem erdos600Prop_set_nonempty (n r : ℕ) :
    ({e : ℕ | Erdos600Prop n e r}).Nonempty :=
  ⟨n.choose 2 + 1, erdos600Prop_choose_two_succ n r⟩

theorem erdos600Prop_eFunction (n r : ℕ) :
    Erdos600Prop n (eFunction n r) r :=
  Nat.sInf_mem (erdos600Prop_set_nonempty n r)

theorem erdos600Prop_iff_eFunction_le (n e r : ℕ) :
    Erdos600Prop n e r ↔ eFunction n r ≤ e := by
  constructor
  · intro h
    exact Nat.sInf_le h
  · intro h
    exact erdos600Prop_mono_edges h (erdos600Prop_eFunction n r)

theorem eFunction_le_choose_two_succ (n r : ℕ) :
    eFunction n r ≤ n.choose 2 + 1 :=
  (erdos600Prop_iff_eFunction_le n (n.choose 2 + 1) r).mp (erdos600Prop_choose_two_succ n r)

theorem not_erdos600Prop_zero (n r : ℕ) :
    ¬ Erdos600Prop n 0 r := by
  intro h
  obtain ⟨uv, huv, _⟩ := h (⊥ : SimpleGraph (Fin n)) (Nat.zero_le _) (by simp)
  simp at huv

theorem one_le_eFunction (n r : ℕ) :
    1 ≤ eFunction n r := by
  by_contra h
  have h0 : eFunction n r ≤ 0 := by omega
  have hprop : Erdos600Prop n 0 r := (erdos600Prop_iff_eFunction_le n 0 r).mpr h0
  exact not_erdos600Prop_zero n r hprop

theorem erdos600Prop_one_one (n : ℕ) :
    Erdos600Prop n 1 1 := by
  intro G hG htri
  obtain ⟨uv, huv⟩ : G.edgeFinset.Nonempty := Finset.card_pos.mp hG
  have hne : (G.trianglesContaining uv).Nonempty := htri uv huv
  exact ⟨uv, huv, Finset.Nonempty.card_pos hne⟩

theorem eFunction_one (n : ℕ) :
    eFunction n 1 = 1 := by
  have hle : eFunction n 1 ≤ 1 := (erdos600Prop_iff_eFunction_le n 1 1).mp (erdos600Prop_one_one n)
  have hge : 1 ≤ eFunction n 1 := one_le_eFunction n 1
  omega

theorem eFunction_zero (n : ℕ) :
    eFunction n 0 = 1 := by
  have h1 : Erdos600Prop n 1 0 :=
    erdos600Prop_anti_triangles (Nat.zero_le 1) (erdos600Prop_one_one n)
  have hle : eFunction n 0 ≤ 1 := (erdos600Prop_iff_eFunction_le n 1 0).mp h1
  have hge : 1 ≤ eFunction n 0 := one_le_eFunction n 0
  omega

theorem eFunction_diff_one_zero (n : ℕ) :
    (eFunction n 1 : ℝ) - (eFunction n 0 : ℝ) = 0 := by
  simp [eFunction_one, eFunction_zero]

theorem eFunction_mono_right {n r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) :
    eFunction n r₁ ≤ eFunction n r₂ := by
  rw [← erdos600Prop_iff_eFunction_le]
  exact erdos600Prop_anti_triangles hr (erdos600Prop_eFunction n r₂)

/-!
## Locally linear bridge at `r = 2`, Behrend lower bounds, and saturation controls

This section proves universal structural results for `Erdos600.Erdos600Prop` and
`Erdos600.eFunction`:

1. Exact equivalence between `SimpleGraph.LocallyLinear` and the $r = 2$ admissibility condition
   `(∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) ∧ (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < 2)`.
2. Exact universal formula `eFunction n 2 = 3 * ruzsaSzemerediNumberNat n + 1` and threshold
   equivalence `Erdos600Prop n e 2 ↔ 3 * ruzsaSzemerediNumberNat n + 1 ≤ e`.
3. Transfer of the Roth–Behrend–Ruzsa–Szemerédi lower bounds (`rothNumberNat_le_ruzsaSzemerediNumberNat`,
   `ruzsaSzemerediNumberNat_lower_bound`, `ruzsaSzemerediNumberNat_asymptotic_lower_bound`) to
   `eFunction n r` for all $r \ge 2$.
4. Universal triangle-multiplicity cap `(G.trianglesContaining uv).card ≤ n - 2`, small-order
   collapse `eFunction n r = 1` for $n < 3$, and complete-graph saturation
   `eFunction n r = n.choose 2 + 1` for all $n \ge 3$ and $r \ge n - 1$.
-/

theorem mem_trianglesContaining_iff {α : Type*} [Fintype α]
    (G : SimpleGraph α) (uv : Sym2 α) (t : Finset α) :
    t ∈ G.trianglesContaining uv ↔ t ∈ G.cliqueFinset 3 ∧ uv ∈ t.sym2 := by
  simp [SimpleGraph.trianglesContaining, Finset.mem_filter, Finset.subset_iff,
    Finset.mem_sym2_iff, Sym2.mem_toFinset]

theorem not_mem_edgeFinset_trianglesContaining_eq_empty {α : Type*} [Fintype α]
    (G : SimpleGraph α) {uv : Sym2 α} (huv : uv ∉ G.edgeFinset)
    (hdiag : ¬ uv.IsDiag) :
    G.trianglesContaining uv = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  rw [mem_trianglesContaining_iff] at ht
  obtain ⟨hclique, hsym⟩ := ht
  rw [SimpleGraph.mem_cliqueFinset_iff] at hclique
  induction uv using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := Sym2.mk_isDiag_iff.not.mp hdiag
    have hx : x ∈ t := Finset.mem_sym2_iff.mp hsym x (Sym2.mem_mk_left x y)
    have hy : y ∈ t := Finset.mem_sym2_iff.mp hsym y (Sym2.mem_mk_right x y)
    have hadj : G.Adj x y := hclique.isClique hx hy hxy
    exact huv (SimpleGraph.mem_edgeFinset.mpr hadj)

theorem edgeDisjointTriangles_iff_forall_trianglesContaining_card_le_one
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    G.EdgeDisjointTriangles ↔
      ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card ≤ 1 := by
  rw [SimpleGraph.edgeDisjointTriangles_iff_mem_sym2_subsingleton]
  constructor
  · intro h uv huv
    have hdiag : ¬ uv.IsDiag := G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp huv)
    have hsub : {s ∈ G.cliqueSet 3 | uv ∈ s.sym2}.Subsingleton := h hdiag
    rw [Finset.card_le_one]
    intro s hs t ht
    rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff] at hs ht
    exact hsub ⟨hs.1, hs.2⟩ ⟨ht.1, ht.2⟩
  · intro h uv hdiag
    by_cases huv : uv ∈ G.edgeFinset
    · have hcard := Finset.card_le_one.mp (h uv huv)
      rintro s ⟨hs1, hs2⟩ t ⟨ht1, ht2⟩
      apply hcard
      · rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
        exact ⟨hs1, hs2⟩
      · rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
        exact ⟨ht1, ht2⟩
    · have hemp := not_mem_edgeFinset_trianglesContaining_eq_empty G huv hdiag
      rintro s ⟨hs1, hs2⟩ _ _
      exfalso
      have hmem : s ∈ G.trianglesContaining uv := by
        rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
        exact ⟨hs1, hs2⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty s hmem

theorem forall_adj_exists_three_clique_iff_forall_trianglesContaining_nonempty
    {α : Type*} [Fintype α] (G : SimpleGraph α) :
    (∀ ⦃x y : α⦄, G.Adj x y → ∃ s : Finset α, G.IsNClique 3 s ∧ x ∈ s ∧ y ∈ s) ↔
      ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty := by
  constructor
  · intro h uv huv
    induction uv using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x y := SimpleGraph.mem_edgeFinset.mp huv
      obtain ⟨s, hs, hx, hy⟩ := h hadj
      refine ⟨s, ?_⟩
      rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
      refine ⟨hs, Finset.mem_sym2_iff.mpr ?_⟩
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
  · intro h x y hadj
    have huv : s(x, y) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj
    obtain ⟨s, hs⟩ := h s(x, y) huv
    rw [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff] at hs
    refine ⟨s, hs.1, ?_, ?_⟩
    · exact Finset.mem_sym2_iff.mp hs.2 x (Sym2.mem_mk_left x y)
    · exact Finset.mem_sym2_iff.mp hs.2 y (Sym2.mem_mk_right x y)

theorem locallyLinear_iff_trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α) :
    G.LocallyLinear ↔
      (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) ∧
        (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < 2) := by
  rw [SimpleGraph.LocallyLinear,
    edgeDisjointTriangles_iff_forall_trianglesContaining_card_le_one,
    forall_adj_exists_three_clique_iff_forall_trianglesContaining_nonempty,
    and_comm]
  congr! 3 with uv huv
  omega

theorem erdos600Prop_two_of_gt_three_mul_ruzsaSzemerediNumberNat (n : ℕ) :
    Erdos600Prop n (3 * ruzsaSzemerediNumberNat n + 1) 2 := by
  intro G hG htri
  by_contra hnot
  push Not at hnot
  have hll : G.LocallyLinear := (locallyLinear_iff_trianglesContaining G).mpr ⟨htri, hnot⟩
  have hcard : G.edgeFinset.card = 3 * (G.cliqueFinset 3).card := hll.card_edgeFinset
  have hrs : (G.cliqueFinset 3).card ≤ ruzsaSzemerediNumberNat n := by
    simpa [ruzsaSzemerediNumberNat] using hll.le_ruzsaSzemerediNumber
  omega

theorem not_erdos600Prop_two_three_mul_ruzsaSzemerediNumberNat (n : ℕ) :
    ¬ Erdos600Prop n (3 * ruzsaSzemerediNumberNat n) 2 := by
  intro hprop
  obtain ⟨G, inst, hcard, hll⟩ := ruzsaSzemerediNumber_spec (α := Fin n)
  have hinst : inst = Classical.decRel G.Adj := Subsingleton.elim _ _
  subst hinst
  have h1 : G.edgeFinset.card = 3 * (G.cliqueFinset 3).card := hll.card_edgeFinset
  have h2 : (G.cliqueFinset 3).card = ruzsaSzemerediNumberNat n := by
    simpa [ruzsaSzemerediNumberNat] using hcard
  have hcard_eq : G.edgeFinset.card ≥ 3 * ruzsaSzemerediNumberNat n := by omega
  obtain ⟨htri, hlt⟩ := (locallyLinear_iff_trianglesContaining G).mp hll
  obtain ⟨uv, huv, hge⟩ := hprop G hcard_eq htri
  have := hlt uv huv
  omega

theorem erdos600Prop_two_iff (n e : ℕ) :
    Erdos600Prop n e 2 ↔ 3 * ruzsaSzemerediNumberNat n + 1 ≤ e := by
  constructor
  · intro h
    by_contra hlt
    have hle : e ≤ 3 * ruzsaSzemerediNumberNat n := by omega
    exact not_erdos600Prop_two_three_mul_ruzsaSzemerediNumberNat n
      (erdos600Prop_mono_edges hle h)
  · intro h
    exact erdos600Prop_mono_edges h
      (erdos600Prop_two_of_gt_three_mul_ruzsaSzemerediNumberNat n)

theorem eFunction_two_eq (n : ℕ) :
    eFunction n 2 = 3 * ruzsaSzemerediNumberNat n + 1 := by
  have h1 : eFunction n 2 ≤ 3 * ruzsaSzemerediNumberNat n + 1 :=
    (erdos600Prop_iff_eFunction_le n (3 * ruzsaSzemerediNumberNat n + 1) 2).mp
      (erdos600Prop_two_of_gt_three_mul_ruzsaSzemerediNumberNat n)
  have h2 : ¬ eFunction n 2 ≤ 3 * ruzsaSzemerediNumberNat n := by
    intro hle
    exact not_erdos600Prop_two_three_mul_ruzsaSzemerediNumberNat n
      ((erdos600Prop_iff_eFunction_le n (3 * ruzsaSzemerediNumberNat n) 2).mpr hle)
  omega

theorem three_mul_ruzsaSzemerediNumberNat_succ_le_eFunction {n r : ℕ} (hr : 2 ≤ r) :
    3 * ruzsaSzemerediNumberNat n + 1 ≤ eFunction n r := by
  rw [← eFunction_two_eq n]
  exact eFunction_mono_right hr

theorem rothNumberNat_lower_bound_eFunction {n r : ℕ} (hr : 2 ≤ r) :
    3 * ((2 * n + 1) * rothNumberNat n) + 1 ≤ eFunction (6 * n + 3) r := by
  have hrs := rothNumberNat_le_ruzsaSzemerediNumberNat n
  have hle := three_mul_ruzsaSzemerediNumberNat_succ_le_eFunction (n := 6 * n + 3) hr
  omega

theorem behrend_explicit_lower_bound_eFunction (n : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    3 * ((n / 3 - 2 : ℝ) * ↑((n - 3) / 6) *
      Real.exp (-4 * Real.sqrt (Real.log ↑((n - 3) / 6)))) + 1 ≤
      (eFunction n r : ℝ) := by
  have hrs : (n / 3 - 2 : ℝ) * ↑((n - 3) / 6) *
      Real.exp (-4 * Real.sqrt (Real.log ↑((n - 3) / 6))) ≤
      (ruzsaSzemerediNumberNat n : ℝ) := ruzsaSzemerediNumberNat_lower_bound n
  have hle : (3 * ruzsaSzemerediNumberNat n + 1 : ℝ) ≤ (eFunction n r : ℝ) := by
    exact_mod_cast three_mul_ruzsaSzemerediNumberNat_succ_le_eFunction (n := n) hr
  linarith

theorem behrend_asymptotic_lower_bound_eFunction {r : ℕ} (hr : 2 ≤ r) :
    (fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.exp (-4 * Real.sqrt (Real.log n))) =O[atTop]
      (fun n : ℕ ↦ (eFunction n r : ℝ)) := by
  refine ruzsaSzemerediNumberNat_asymptotic_lower_bound.trans ?_
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 0] with n _
  have hle : (3 * ruzsaSzemerediNumberNat n + 1 : ℝ) ≤ (eFunction n r : ℝ) := by
    exact_mod_cast three_mul_ruzsaSzemerediNumberNat_succ_le_eFunction (n := n) hr
  have hnonneg : (0 : ℝ) ≤ (ruzsaSzemerediNumberNat n : ℝ) := Nat.cast_nonneg _
  have hpos : (0 : ℝ) ≤ (eFunction n r : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hpos]
  linarith

theorem trianglesContaining_card_le_card_sub_two {α : Type*} [Fintype α]
    (G : SimpleGraph α) {uv : Sym2 α} (huv : uv ∈ G.edgeFinset) :
    (G.trianglesContaining uv).card ≤ Fintype.card α - 2 := by
  have htwo : uv.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset (G := G) ⟨uv, huv⟩
  have hsub : G.trianglesContaining uv ⊆
      (Finset.univ \ uv.toFinset).image (fun w : α ↦ insert w uv.toFinset) := by
    intro t ht
    simp only [SimpleGraph.trianglesContaining, Finset.mem_filter,
      SimpleGraph.mem_cliqueFinset_iff] at ht
    obtain ⟨hclique, hsub_uv⟩ := ht
    have hcard_t : t.card = 3 := hclique.card_eq
    have hcard_sdiff : (t \ uv.toFinset).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub_uv, hcard_t, htwo]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard_sdiff
    have hw_mem : w ∈ t \ uv.toFinset := by rw [hw]; simp
    have hw_univ : w ∈ Finset.univ \ uv.toFinset := by
      simp [(Finset.mem_sdiff.mp hw_mem).2]
    refine Finset.mem_image.mpr ⟨w, hw_univ, ?_⟩
    calc
      insert w uv.toFinset = {w} ∪ uv.toFinset := by ext x; simp
      _ = (t \ uv.toFinset) ∪ uv.toFinset := by rw [hw]
      _ = t := Finset.sdiff_union_of_subset hsub_uv
  calc
    (G.trianglesContaining uv).card
      ≤ ((Finset.univ \ uv.toFinset).image (fun w : α ↦ insert w uv.toFinset)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ \ uv.toFinset).card := Finset.card_image_le
    _ = Fintype.card α - 2 := by
      have hsub_univ : uv.toFinset ⊆ (Finset.univ : Finset α) := Finset.subset_univ _
      rw [Finset.card_sdiff_of_subset hsub_univ, Finset.card_univ, htwo]

theorem trianglesContaining_card_le_sub_two {n : ℕ} (G : SimpleGraph (Fin n))
    {uv : Sym2 (Fin n)} (huv : uv ∈ G.edgeFinset) :
    (G.trianglesContaining uv).card ≤ n - 2 := by
  simpa using trianglesContaining_card_le_card_sub_two G huv

theorem erdos600Prop_one_of_lt_three {n : ℕ} (hn : n < 3) (r : ℕ) :
    Erdos600Prop n 1 r := by
  intro G hG htri
  obtain ⟨uv, huv⟩ : G.edgeFinset.Nonempty := Finset.card_pos.mp hG
  have hne : (G.trianglesContaining uv).Nonempty := htri uv huv
  have hpos : 1 ≤ (G.trianglesContaining uv).card := Finset.Nonempty.card_pos hne
  have hle : (G.trianglesContaining uv).card ≤ n - 2 :=
    trianglesContaining_card_le_sub_two G huv
  omega

theorem eFunction_of_lt_three {n : ℕ} (hn : n < 3) (r : ℕ) :
    eFunction n r = 1 := by
  have hle : eFunction n r ≤ 1 :=
    (erdos600Prop_iff_eFunction_le n 1 r).mp (erdos600Prop_one_of_lt_three hn r)
  have hge : 1 ≤ eFunction n r := one_le_eFunction n r
  omega

theorem trianglesContaining_nonempty_of_eq_top {α : Type*} [Fintype α]
    (G : SimpleGraph α) (hG : G = ⊤) (hcard : 3 ≤ Fintype.card α) :
    ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty := by
  intro uv huv
  have htwo : uv.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset (G := G) ⟨uv, huv⟩
  have hthird : ∃ w : α, w ∉ uv.toFinset := by
    by_contra h
    push Not at h
    have heq : uv.toFinset = (Finset.univ : Finset α) := by
      ext w
      simp [h w]
    rw [heq, Finset.card_univ] at htwo
    omega
  obtain ⟨w, hw⟩ := hthird
  have hcard_t : (insert w uv.toFinset).card = 3 := by
    rw [Finset.card_insert_of_notMem hw, htwo]
  have hclique : insert w uv.toFinset ∈ G.cliqueFinset 3 := by
    rw [SimpleGraph.mem_cliqueFinset_iff, hG]
    exact ⟨SimpleGraph.IsClique.top _, hcard_t⟩
  refine ⟨insert w uv.toFinset, Finset.mem_filter.mpr ⟨hclique, ?_⟩⟩
  exact Finset.subset_insert _ _

theorem card_edgeFinset_of_eq_top {α : Type*} [Fintype α]
    (G : SimpleGraph α) (hG : G = ⊤) :
    G.edgeFinset.card = (Fintype.card α).choose 2 := by
  have h : G.edgeFinset = (⊤ : SimpleGraph α).edgeFinset := by
    ext e
    simp [hG]
  rw [h]
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two

theorem not_erdos600Prop_choose_two_of_sub_one_le {n r : ℕ}
    (hn : 3 ≤ n) (hr : n - 1 ≤ r) :
    ¬ Erdos600Prop n (n.choose 2) r := by
  intro hprop
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (Fin n), G = ⊤ := ⟨⊤, rfl⟩
  have hcard_top : G.edgeFinset.card ≥ n.choose 2 := by
    have h := card_edgeFinset_of_eq_top G hG
    rw [Fintype.card_fin] at h
    omega
  have htri_top : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty := by
    apply trianglesContaining_nonempty_of_eq_top G hG
    simpa using hn
  obtain ⟨uv, huv, hge⟩ := hprop G hcard_top htri_top
  have hle : (G.trianglesContaining uv).card ≤ n - 2 :=
    trianglesContaining_card_le_sub_two G huv
  omega

theorem eFunction_eq_choose_two_succ_of_sub_one_le {n r : ℕ}
    (hn : 3 ≤ n) (hr : n - 1 ≤ r) :
    eFunction n r = n.choose 2 + 1 := by
  have hle : eFunction n r ≤ n.choose 2 + 1 := eFunction_le_choose_two_succ n r
  have hnot : ¬ eFunction n r ≤ n.choose 2 := by
    intro h
    exact not_erdos600Prop_choose_two_of_sub_one_le hn hr
      ((erdos600Prop_iff_eFunction_le n (n.choose 2) r).mpr h)
  omega

theorem eFunction_diff_eq_zero_of_sub_one_le {n r : ℕ}
    (hn : 3 ≤ n) (hr : n - 1 ≤ r) :
    (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ) = 0 := by
  have hr1 : n - 1 ≤ r + 1 := by omega
  rw [eFunction_eq_choose_two_succ_of_sub_one_le hn hr1,
    eFunction_eq_choose_two_succ_of_sub_one_le hn hr, sub_self]

theorem eFunction_div_eq_one_of_sub_one_le {n r : ℕ}
    (hn : 3 ≤ n) (hr : n - 1 ≤ r) :
    (eFunction n (r + 1) : ℝ) / (eFunction n r : ℝ) = 1 := by
  have hr1 : n - 1 ≤ r + 1 := by omega
  rw [eFunction_eq_choose_two_succ_of_sub_one_le hn hr1,
    eFunction_eq_choose_two_succ_of_sub_one_le hn hr]
  apply div_self
  positivity

theorem eFunction_cast_pos (n r : ℕ) : (0 : ℝ) < (eFunction n r : ℝ) := by
  have h := one_le_eFunction n r
  exact_mod_cast (by omega : 0 < eFunction n r)

theorem eFunction_cast_ne_zero (n r : ℕ) : (eFunction n r : ℝ) ≠ 0 :=
  (eFunction_cast_pos n r).ne'

theorem tendsto_sub_add_atTop_of_parts_i
    (hi : ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ)) atTop atTop)
    {r k : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ ↦ (eFunction n (r + k) : ℝ) - (eFunction n r : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n ↦ ?_) (hi r hr)
  have hmono : (eFunction n (r + 1) : ℝ) ≤ (eFunction n (r + k) : ℝ) := by
    exact_mod_cast eFunction_mono_right (n := n) (by omega : r + 1 ≤ r + k)
  linarith

theorem tendsto_div_add_nhds_one_of_parts_ii
    (hii : ∀ r : ℕ, 2 ≤ r →
      Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) / (eFunction n r : ℝ)) atTop (nhds 1))
    {r : ℕ} (hr : 2 ≤ r) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (eFunction n (r + k) : ℝ) / (eFunction n r : ℝ)) atTop (nhds 1) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero]
    refine tendsto_const_nhds.congr (fun n ↦ ?_)
    exact (div_self (eFunction_cast_ne_zero n r)).symm
  | succ k ih =>
    have hstep : Tendsto (fun n : ℕ ↦
        (eFunction n (r + k + 1) : ℝ) / (eFunction n (r + k) : ℝ)) atTop (nhds 1) :=
      hii (r + k) (by omega)
    have hmul := ih.mul hstep
    rw [mul_one] at hmul
    refine hmul.congr (fun n ↦ ?_)
    have hne : (eFunction n (r + k) : ℝ) ≠ 0 := eFunction_cast_ne_zero n (r + k)
    have : r + (k + 1) = r + k + 1 := by omega
    rw [this, div_mul_div_cancel₀' hne]

theorem tendsto_div_nhds_one_iff_sub_isLittleO (r : ℕ) :
    Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) / (eFunction n r : ℝ)) atTop (nhds 1) ↔
      (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (eFunction n r : ℝ)) := by
  rw [Asymptotics.isLittleO_iff_tendsto' (Filter.Eventually.of_forall fun n hn ↦
    (eFunction_cast_ne_zero n r hn).elim)]
  constructor
  · intro h
    have hsub := h.sub (tendsto_const_nhds (x := (1 : ℝ)))
    rw [sub_self] at hsub
    refine hsub.congr (fun n ↦ ?_)
    have hne : (eFunction n r : ℝ) ≠ 0 := eFunction_cast_ne_zero n r
    rw [sub_div, div_self hne]
  · intro h
    have hadd := h.add (tendsto_const_nhds (x := (1 : ℝ)))
    rw [zero_add] at hadd
    refine hadd.congr (fun n ↦ ?_)
    have hne : (eFunction n r : ℝ) ≠ 0 := eFunction_cast_ne_zero n r
    rw [sub_div, div_self hne, sub_add_cancel]

end DefinitionsAndFoundations

/-!
## Triangle-removal cover-charge bounds and subquadratic asymptotics

This section proves universal triangle-covering and triangle-deletion bounds, and applies
the triangle removal lemma of Dillies and Mehta to `Erdos600.Erdos600Prop` and
`Erdos600.eFunction`:

1. Exact characterization of the 3-edge incidence fiber of any triangle
   `t ∈ G.cliqueFinset 3` and the double-counting bound
   `G.edgeFinset.card ≤ 3 * (G.cliqueFinset 3).card`.
2. Triangle-free subgraph deletion bounds for any `H ≤ G` with `H.CliqueFree 3`:
   `(G.cliqueFinset 3).card ≤ (r - 1) * (G.edgeFinset.card - H.edgeFinset.card)`,
   `H.edgeFinset.card ≤ 2 * (G.cliqueFinset 3).card`, and the sharp cover-charge
   bound `G.edgeFinset.card ≤ (2 * r - 1) * (G.edgeFinset.card - H.edgeFinset.card)`.
3. Reduction of dense `r`-book-free triangle-covered graphs to
   `SimpleGraph.FarFromTriangleFree` and unconditional proof of the Ruzsa–Szemerédi
   subquadratic upper bound `erdos_600.variants.ruzsa_szemeredi_upper_bound`:
   `∀ r : ℕ, (fun n : ℕ ↦ (eFunction n r : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2)`.
-/

section TriangleRemovalProofs
open scoped Classical

theorem sym2_mk_ne_left_of_ne {α : Type*} {x y z : α} (hyz : y ≠ z) :
    s(x, y) ≠ s(x, z) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
  · exact hyz rfl
  · exact hyz rfl

theorem sym2_mk_ne_right_of_ne {α : Type*} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) :
    s(x, y) ≠ s(y, z) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hxy h1
  · exact hxz h1

theorem card_three_pair_finset {α : Type*} {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({s(x, y), s(x, z), s(y, z)} : Finset (Sym2 α)).card = 3 := by
  have h1 : s(x, y) ∉ ({s(x, z), s(y, z)} : Finset (Sym2 α)) := by
    simp [sym2_mk_ne_left_of_ne hyz, sym2_mk_ne_right_of_ne hxy hxz]
  have h2 : s(x, z) ∉ ({s(y, z)} : Finset (Sym2 α)) := by
    have hne : s(x, z) ≠ s(y, z) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hxy h1
      · exact hxz h1
    simp [hne]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]

theorem three_clique_edges_eq {α : Type*} [Fintype α]
    (G : SimpleGraph α) {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hclique : G.IsNClique 3 ({x, y, z} : Finset α)) :
    G.edgeFinset.filter (fun uv ↦ ({x, y, z} : Finset α) ∈ G.trianglesContaining uv) =
      {s(x, y), s(x, z), s(y, z)} := by
  ext uv
  rw [Finset.mem_filter, mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff]
  simp only [hclique, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨huv_edge, huv_sym⟩ := h
    have hdiag : ¬ uv.IsDiag := G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp huv_edge)
    induction uv using Sym2.ind with
    | _ u v =>
      have huv_ne : u ≠ v := Sym2.mk_isDiag_iff.not.mp hdiag
      have hu : u = x ∨ u = y ∨ u = z := by
        simpa using Finset.mem_sym2_iff.mp huv_sym u (Sym2.mem_mk_left u v)
      have hv : v = x ∨ v = y ∨ v = z := by
        simpa using Finset.mem_sym2_iff.mp huv_sym v (Sym2.mem_mk_right u v)
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact (huv_ne rfl).elim
      · left; rfl
      · right; left; rfl
      · left; exact Sym2.eq_swap
      · exact (huv_ne rfl).elim
      · right; right; rfl
      · right; left; exact Sym2.eq_swap
      · right; right; exact Sym2.eq_swap
      · exact (huv_ne rfl).elim
  · intro h
    have hadj_xy : G.Adj x y := hclique.isClique (by simp) (by simp) hxy
    have hadj_xz : G.Adj x z := hclique.isClique (by simp) (by simp) hxz
    have hadj_yz : G.Adj y z := hclique.isClique (by simp) (by simp) hyz
    rcases h with rfl | rfl | rfl
    · refine ⟨SimpleGraph.mem_edgeFinset.mpr hadj_xy, Finset.mem_sym2_iff.mpr ?_⟩
      intro w hw; rcases Sym2.mem_iff.mp hw with rfl | rfl <;> simp
    · refine ⟨SimpleGraph.mem_edgeFinset.mpr hadj_xz, Finset.mem_sym2_iff.mpr ?_⟩
      intro w hw; rcases Sym2.mem_iff.mp hw with rfl | rfl <;> simp
    · refine ⟨SimpleGraph.mem_edgeFinset.mpr hadj_yz, Finset.mem_sym2_iff.mpr ?_⟩
      intro w hw; rcases Sym2.mem_iff.mp hw with rfl | rfl <;> simp

theorem card_filter_edgeFinset_trianglesContaining_eq_three {α : Type*} [Fintype α]
    (G : SimpleGraph α) {t : Finset α} (ht : t ∈ G.cliqueFinset 3) :
    (G.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv)).card = 3 := by
  have hclique : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hclique.card_eq
  rw [three_clique_edges_eq G hxy hxz hyz hclique]
  exact card_three_pair_finset hxy hxz hyz

theorem edgeFinset_subset_biUnion_cliqueFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) :
    G.edgeFinset ⊆ (G.cliqueFinset 3).biUnion
      (fun t ↦ G.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv)) := by
  intro uv huv
  obtain ⟨t, ht⟩ := htri uv huv
  have ht_clique : t ∈ G.cliqueFinset 3 := (mem_trianglesContaining_iff G uv t).mp ht |>.1
  rw [Finset.mem_biUnion]
  exact ⟨t, ht_clique, Finset.mem_filter.mpr ⟨huv, ht⟩⟩

theorem card_edgeFinset_le_three_mul_card_cliqueFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) :
    G.edgeFinset.card ≤ 3 * (G.cliqueFinset 3).card := by
  calc
    G.edgeFinset.card
      ≤ ((G.cliqueFinset 3).biUnion
          (fun t ↦ G.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv))).card :=
        Finset.card_le_card (edgeFinset_subset_biUnion_cliqueFinset G htri)
    _ ≤ ∑ t ∈ G.cliqueFinset 3,
          (G.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ G.cliqueFinset 3, 3 := by
        refine Finset.sum_le_sum fun t ht ↦ ?_
        rw [card_filter_edgeFinset_trianglesContaining_eq_three G ht]
    _ = 3 * (G.cliqueFinset 3).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem not_all_three_edges_of_cliqueFree_three {α : Type*} [Fintype α]
    (H : SimpleGraph α) (hH : H.CliqueFree 3)
    {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ¬ (s(x, y) ∈ H.edgeFinset ∧ s(x, z) ∈ H.edgeFinset ∧ s(y, z) ∈ H.edgeFinset) := by
  rintro ⟨h1, h2, h3⟩
  have hadj_xy : H.Adj x y := SimpleGraph.mem_edgeFinset.mp h1
  have hadj_xz : H.Adj x z := SimpleGraph.mem_edgeFinset.mp h2
  have hadj_yz : H.Adj y z := SimpleGraph.mem_edgeFinset.mp h3
  have hcl : H.IsNClique 3 ({x, y, z} : Finset α) := by
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, ?_⟩
    · intro u hu v hv huv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact (huv rfl).elim
      · exact hadj_xy
      · exact hadj_xz
      · exact hadj_xy.symm
      · exact (huv rfl).elim
      · exact hadj_yz
      · exact hadj_xz.symm
      · exact hadj_yz.symm
      · exact (huv rfl).elim
    · rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  exact hH ({x, y, z} : Finset α) hcl

theorem exists_mem_sdiff_edgeFinset_of_mem_cliqueFinset {α : Type*} [Fintype α]
    (G H : SimpleGraph α) (hH : H.CliqueFree 3)
    {t : Finset α} (ht : t ∈ G.cliqueFinset 3) :
    ∃ uv ∈ G.edgeFinset \ H.edgeFinset, t ∈ G.trianglesContaining uv := by
  have hclique : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hclique.card_eq
  have heq := three_clique_edges_eq G hxy hxz hyz hclique
  have hnot := not_all_three_edges_of_cliqueFree_three H hH hxy hxz hyz
  have hmem_xy : s(x, y) ∈ G.edgeFinset ∧ ({x, y, z} : Finset α) ∈ G.trianglesContaining s(x, y) := by
    simpa [Finset.mem_filter] using (by rw [heq]; simp : s(x, y) ∈ G.edgeFinset.filter (fun uv ↦ ({x, y, z} : Finset α) ∈ G.trianglesContaining uv))
  have hmem_xz : s(x, z) ∈ G.edgeFinset ∧ ({x, y, z} : Finset α) ∈ G.trianglesContaining s(x, z) := by
    simpa [Finset.mem_filter] using (by rw [heq]; simp : s(x, z) ∈ G.edgeFinset.filter (fun uv ↦ ({x, y, z} : Finset α) ∈ G.trianglesContaining uv))
  have hmem_yz : s(y, z) ∈ G.edgeFinset ∧ ({x, y, z} : Finset α) ∈ G.trianglesContaining s(y, z) := by
    simpa [Finset.mem_filter] using (by rw [heq]; simp : s(y, z) ∈ G.edgeFinset.filter (fun uv ↦ ({x, y, z} : Finset α) ∈ G.trianglesContaining uv))
  by_cases h1 : s(x, y) ∈ H.edgeFinset
  · by_cases h2 : s(x, z) ∈ H.edgeFinset
    · have h3 : s(y, z) ∉ H.edgeFinset := fun h3 ↦ hnot ⟨h1, h2, h3⟩
      exact ⟨s(y, z), Finset.mem_sdiff.mpr ⟨hmem_yz.1, h3⟩, hmem_yz.2⟩
    · exact ⟨s(x, z), Finset.mem_sdiff.mpr ⟨hmem_xz.1, h2⟩, hmem_xz.2⟩
  · exact ⟨s(x, y), Finset.mem_sdiff.mpr ⟨hmem_xy.1, h1⟩, hmem_xy.2⟩

theorem cliqueFinset_subset_biUnion_sdiff_edgeFinset {α : Type*} [Fintype α]
    (G H : SimpleGraph α) (hH : H.CliqueFree 3) :
    G.cliqueFinset 3 ⊆ (G.edgeFinset \ H.edgeFinset).biUnion G.trianglesContaining := by
  intro t ht
  rw [Finset.mem_biUnion]
  exact exists_mem_sdiff_edgeFinset_of_mem_cliqueFinset G H hH ht

theorem card_cliqueFinset_le_mul_card_sdiff_edgeFinset {α : Type*} [Fintype α]
    (G H : SimpleGraph α) (hH : H.CliqueFree 3) {k : ℕ}
    (hk : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card ≤ k) :
    (G.cliqueFinset 3).card ≤ k * (G.edgeFinset \ H.edgeFinset).card := by
  calc
    (G.cliqueFinset 3).card
      ≤ ((G.edgeFinset \ H.edgeFinset).biUnion G.trianglesContaining).card :=
        Finset.card_le_card (cliqueFinset_subset_biUnion_sdiff_edgeFinset G H hH)
    _ ≤ ∑ uv ∈ G.edgeFinset \ H.edgeFinset, (G.trianglesContaining uv).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _uv ∈ G.edgeFinset \ H.edgeFinset, k := by
        refine Finset.sum_le_sum fun uv huv ↦ hk uv (Finset.mem_sdiff.mp huv).1
    _ = k * (G.edgeFinset \ H.edgeFinset).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_sdiff_edgeFinset_of_le {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) :
    (G.edgeFinset \ H.edgeFinset).card = G.edgeFinset.card - H.edgeFinset.card :=
  Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hle)

theorem card_cliqueFinset_le_sub_one_mul_sub_card {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) (hH : H.CliqueFree 3) {r : ℕ}
    (hr : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r) :
    (G.cliqueFinset 3).card ≤ (r - 1) * (G.edgeFinset.card - H.edgeFinset.card) := by
  rw [← card_sdiff_edgeFinset_of_le hle]
  exact card_cliqueFinset_le_mul_card_sdiff_edgeFinset G H hH fun uv huv ↦
    Nat.le_sub_one_of_lt (hr uv huv)

theorem card_edgeFinset_le_three_mul_sub_one_mul_sub_card {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) (hH : H.CliqueFree 3)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) {r : ℕ}
    (hr : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r) :
    G.edgeFinset.card ≤ 3 * (r - 1) * (G.edgeFinset.card - H.edgeFinset.card) := by
  have h1 := card_edgeFinset_le_three_mul_card_cliqueFinset G htri
  have h2 := card_cliqueFinset_le_sub_one_mul_sub_card hle hH hr
  calc
    G.edgeFinset.card ≤ 3 * (G.cliqueFinset 3).card := h1
    _ ≤ 3 * ((r - 1) * (G.edgeFinset.card - H.edgeFinset.card)) := Nat.mul_le_mul_left 3 h2
    _ = 3 * (r - 1) * (G.edgeFinset.card - H.edgeFinset.card) := (Nat.mul_assoc _ _ _).symm

theorem card_filter_subgraph_edgeFinset_trianglesContaining_le_two {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) (hH : H.CliqueFree 3)
    {t : Finset α} (ht : t ∈ G.cliqueFinset 3) :
    (H.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv)).card ≤ 2 := by
  have hsub : H.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv) ⊆
      G.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv) :=
    Finset.filter_subset_filter _ (SimpleGraph.edgeFinset_mono hle)
  obtain ⟨uv, huv_sdiff, huv_tri⟩ := exists_mem_sdiff_edgeFinset_of_mem_cliqueFinset G H hH ht
  obtain ⟨huv_G, huv_not_H⟩ := Finset.mem_sdiff.mp huv_sdiff
  have hssub : H.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv) ⊂
      G.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨uv, Finset.mem_filter.mpr ⟨huv_G, huv_tri⟩, ?_⟩
    intro hmem
    exact huv_not_H (Finset.mem_filter.mp hmem).1
  have hlt : (H.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv)).card <
      (G.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv)).card :=
    Finset.card_lt_card hssub
  have hthree := card_filter_edgeFinset_trianglesContaining_eq_three G ht
  omega

theorem subgraph_edgeFinset_subset_biUnion_cliqueFinset {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) :
    H.edgeFinset ⊆ (G.cliqueFinset 3).biUnion
      (fun t ↦ H.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv)) := by
  intro uv huv
  have huv_G : uv ∈ G.edgeFinset := SimpleGraph.edgeFinset_mono hle huv
  obtain ⟨t, ht⟩ := htri uv huv_G
  have ht_clique : t ∈ G.cliqueFinset 3 := (mem_trianglesContaining_iff G uv t).mp ht |>.1
  rw [Finset.mem_biUnion]
  exact ⟨t, ht_clique, Finset.mem_filter.mpr ⟨huv, ht⟩⟩

theorem card_subgraph_edgeFinset_le_two_mul_card_cliqueFinset {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) (hH : H.CliqueFree 3)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) :
    H.edgeFinset.card ≤ 2 * (G.cliqueFinset 3).card := by
  calc
    H.edgeFinset.card
      ≤ ((G.cliqueFinset 3).biUnion
          (fun t ↦ H.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv))).card :=
        Finset.card_le_card (subgraph_edgeFinset_subset_biUnion_cliqueFinset hle htri)
    _ ≤ ∑ t ∈ G.cliqueFinset 3,
          (H.edgeFinset.filter (fun uv ↦ t ∈ G.trianglesContaining uv)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ G.cliqueFinset 3, 2 :=
        Finset.sum_le_sum fun t ht ↦
          card_filter_subgraph_edgeFinset_trianglesContaining_le_two hle hH ht
    _ = 2 * (G.cliqueFinset 3).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_edgeFinset_le_two_mul_sub_one_mul_sub_card {α : Type*} [Fintype α]
    {G H : SimpleGraph α} (hle : H ≤ G) (hH : H.CliqueFree 3)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) {r : ℕ}
    (hr : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r) :
    G.edgeFinset.card ≤ (2 * r - 1) * (G.edgeFinset.card - H.edgeFinset.card) := by
  have hle_card : H.edgeFinset.card ≤ G.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)
  have hH_le : H.edgeFinset.card ≤ 2 * (G.cliqueFinset 3).card :=
    card_subgraph_edgeFinset_le_two_mul_card_cliqueFinset hle hH htri
  have hcl_le : (G.cliqueFinset 3).card ≤ (r - 1) * (G.edgeFinset.card - H.edgeFinset.card) :=
    card_cliqueFinset_le_sub_one_mul_sub_card hle hH hr
  rcases r with _ | r
  · have hemp : G.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro uv huv
      exact Nat.not_lt_zero _ (hr uv huv)
    simp [hemp]
  · calc
      G.edgeFinset.card = H.edgeFinset.card + (G.edgeFinset.card - H.edgeFinset.card) :=
        (Nat.add_sub_of_le hle_card).symm
      _ ≤ 2 * (G.cliqueFinset 3).card + (G.edgeFinset.card - H.edgeFinset.card) :=
        Nat.add_le_add_right hH_le _
      _ ≤ 2 * (r * (G.edgeFinset.card - H.edgeFinset.card)) +
          (G.edgeFinset.card - H.edgeFinset.card) := by
        refine Nat.add_le_add_right (Nat.mul_le_mul_left 2 ?_) _
        simpa using hcl_le
      _ = (2 * (r + 1) - 1) * (G.edgeFinset.card - H.edgeFinset.card) := by
        have h2r : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
        rw [h2r]
        ring

theorem card_cliqueFinset_le_sub_one_mul_card_edgeFinset {α : Type*} [Fintype α]
    (G : SimpleGraph α) {r : ℕ}
    (hr : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r) :
    (G.cliqueFinset 3).card ≤ (r - 1) * G.edgeFinset.card := by
  have hbot_free : (⊥ : SimpleGraph α).CliqueFree 3 := SimpleGraph.cliqueFree_bot (by omega)
  have h := card_cliqueFinset_le_sub_one_mul_sub_card (H := ⊥) bot_le hbot_free hr
  exact h.trans (Nat.mul_le_mul_left (r - 1) (Nat.sub_le _ _))

theorem nat_choose_two_le_sq (n : ℕ) : n.choose 2 ≤ n ^ 2 := by
  rw [Nat.choose_two_right, sq]
  exact (Nat.div_le_self (n * (n - 1)) 2).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))

theorem card_cliqueFinset_le_sub_one_mul_card_sq {α : Type*} [Fintype α]
    (G : SimpleGraph α) {r : ℕ}
    (hr : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r) :
    (G.cliqueFinset 3).card ≤ (r - 1) * Fintype.card α ^ 2 := by
  have h1 := card_cliqueFinset_le_sub_one_mul_card_edgeFinset G hr
  have h2 : G.edgeFinset.card ≤ Fintype.card α ^ 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two.trans (nat_choose_two_le_sq (Fintype.card α))
  exact h1.trans (Nat.mul_le_mul_left (r - 1) h2)

theorem farFromTriangleFree_of_trianglesContaining_bounds {α : Type*} [Fintype α]
    (G : SimpleGraph α)
    (htri : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty)
    {r : ℕ} (hr_pos : 1 ≤ r)
    (hr : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r)
    {ε : ℝ}
    (hcard : ((2 * r - 1 : ℕ) : ℝ) * (ε * (Fintype.card α ^ 2 : ℕ)) ≤ (G.edgeFinset.card : ℝ)) :
    G.FarFromTriangleFree ε := by
  rw [SimpleGraph.farFromTriangleFree_iff]
  intro H inst hle hH
  have hinst : inst = Classical.decRel H.Adj := Subsingleton.elim _ _
  subst hinst
  have hle_edge : H.edgeFinset.card ≤ G.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)
  have hcov_nat := card_edgeFinset_le_two_mul_sub_one_mul_sub_card hle hH htri hr
  have hcov_real : (G.edgeFinset.card : ℝ) ≤
      ((2 * r - 1 : ℕ) : ℝ) * ((G.edgeFinset.card : ℝ) - (H.edgeFinset.card : ℝ)) := by
    have hsub : ((G.edgeFinset.card - H.edgeFinset.card : ℕ) : ℝ) =
        (G.edgeFinset.card : ℝ) - (H.edgeFinset.card : ℝ) := Nat.cast_sub hle_edge
    rw [← hsub]
    exact_mod_cast hcov_nat
  have hpos : (0 : ℝ) < ((2 * r - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * r - 1)
  exact le_of_mul_le_mul_left (hcard.trans hcov_real) hpos

theorem triangleRemovalBound_mul_card_le_sub_one_of_farFromTriangleFree {α : Type*} [Fintype α]
    (G : SimpleGraph α) (hcard_pos : 1 ≤ Fintype.card α) {r : ℕ}
    (hr : ∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r)
    {ε : ℝ} (hfar : G.FarFromTriangleFree ε) :
    SimpleGraph.triangleRemovalBound ε * (Fintype.card α : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
  have hrem := hfar.le_card_cliqueFinset
  have hcl_nat := card_cliqueFinset_le_sub_one_mul_card_sq G hr
  have hcl_real : ((G.cliqueFinset 3).card : ℝ) ≤
      ((r - 1 : ℕ) : ℝ) * (Fintype.card α : ℝ) ^ 2 := by
    exact_mod_cast hcl_nat
  have hcube : (SimpleGraph.triangleRemovalBound ε * (Fintype.card α : ℝ)) *
      (Fintype.card α : ℝ) ^ 2 ≤ ((r - 1 : ℕ) : ℝ) * (Fintype.card α : ℝ) ^ 2 := by
    calc
      (SimpleGraph.triangleRemovalBound ε * (Fintype.card α : ℝ)) * (Fintype.card α : ℝ) ^ 2
        = SimpleGraph.triangleRemovalBound ε * (Fintype.card α : ℝ) ^ 3 := by ring
      _ ≤ ((G.cliqueFinset 3).card : ℝ) := hrem
      _ ≤ ((r - 1 : ℕ) : ℝ) * (Fintype.card α : ℝ) ^ 2 := hcl_real
  have hsq_pos : (0 : ℝ) < (Fintype.card α : ℝ) ^ 2 := by
    have : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card α)
    positivity
  exact le_of_mul_le_mul_right hcube hsq_pos

theorem erdos600Prop_of_triangleRemovalBound_lt {n e r : ℕ} (hr_pos : 1 ≤ r)
    {ε : ℝ} (_hε : 0 < ε)
    (hrem_lt : ((r - 1 : ℕ) : ℝ) < SimpleGraph.triangleRemovalBound ε * (n : ℝ))
    (he : ((2 * r - 1 : ℕ) : ℝ) * (ε * (n ^ 2 : ℕ)) ≤ (e : ℝ)) :
    Erdos600Prop n e r := by
  intro G hG htri
  by_contra hnot
  push Not at hnot
  have hn_pos : 1 ≤ n := by
    by_contra hn0
    have hn_eq : n = 0 := by omega
    subst hn_eq
    have hnonneg : (0 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [Nat.cast_zero, mul_zero] at hrem_lt
    linarith
  have hcard_real : ((2 * r - 1 : ℕ) : ℝ) * (ε * (Fintype.card (Fin n) ^ 2 : ℕ)) ≤
      (G.edgeFinset.card : ℝ) := by
    rw [Fintype.card_fin]
    have hG_real : (e : ℝ) ≤ (G.edgeFinset.card : ℝ) := by exact_mod_cast hG
    exact he.trans hG_real
  have hfar : G.FarFromTriangleFree ε :=
    farFromTriangleFree_of_trianglesContaining_bounds G htri hr_pos hnot hcard_real
  have hle := triangleRemovalBound_mul_card_le_sub_one_of_farFromTriangleFree G
    (by simpa using hn_pos) hnot hfar
  rw [Fintype.card_fin] at hle
  linarith

theorem eFunction_le_of_triangleRemovalBound_lt {n r : ℕ} (hr_pos : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε)
    (hrem_lt : ((r - 1 : ℕ) : ℝ) < SimpleGraph.triangleRemovalBound ε * (n : ℝ)) :
    (eFunction n r : ℝ) ≤ ((2 * r - 1 : ℕ) : ℝ) * (ε * (n : ℝ) ^ 2) + 1 := by
  set B : ℝ := ((2 * r - 1 : ℕ) : ℝ) * (ε * (n ^ 2 : ℕ))
  set e : ℕ := ⌊B⌋₊ + 1
  have he : B ≤ (e : ℝ) := by
    dsimp [e]
    exact le_of_lt (by exact_mod_cast Nat.lt_floor_add_one B)
  have hprop : Erdos600Prop n e r :=
    erdos600Prop_of_triangleRemovalBound_lt hr_pos hε hrem_lt he
  have he_le : eFunction n r ≤ e := (erdos600Prop_iff_eFunction_le n e r).mp hprop
  have he_real : (eFunction n r : ℝ) ≤ (e : ℝ) := by exact_mod_cast he_le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hfloor_le : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB_nonneg
  have hB_eq : B = ((2 * r - 1 : ℕ) : ℝ) * (ε * (n : ℝ) ^ 2) := by
    dsimp [B]
    push_cast
    ring
  have he_cast : (e : ℝ) = (⌊B⌋₊ : ℝ) + 1 := by
    dsimp [e]
    push_cast
    ring
  linarith

theorem erdos_600.variants.ruzsa_szemeredi_upper_bound (r : ℕ) :
    (fun n : ℕ ↦ (eFunction n r : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
  have hr1 : 1 ≤ max r 1 := le_max_right r 1
  have hmax : (fun n : ℕ ↦ (eFunction n (max r 1) : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 2) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have h2r_pos : (0 : ℝ) < ((2 * max r 1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 2 * max r 1 - 1)
    set ε : ℝ := c / (2 * ((2 * max r 1 - 1 : ℕ) : ℝ))
    have hε : 0 < ε := div_pos hc (mul_pos zero_lt_two h2r_pos)
    have hδ : 0 < SimpleGraph.triangleRemovalBound ε :=
      SimpleGraph.triangleRemovalBound_pos hε
    set N₁ : ℕ := ⌊((max r 1 - 1 : ℕ) : ℝ) / SimpleGraph.triangleRemovalBound ε⌋₊ + 1
    set N₂ : ℕ := ⌊2 / c⌋₊ + 1
    filter_upwards [eventually_ge_atTop (max N₁ (max N₂ 1))] with n hn
    have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hn_pos : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    have hlt_δ : ((max r 1 - 1 : ℕ) : ℝ) < SimpleGraph.triangleRemovalBound ε * (n : ℝ) := by
      have h1 : ((max r 1 - 1 : ℕ) : ℝ) / SimpleGraph.triangleRemovalBound ε < (N₁ : ℝ) := by
        dsimp [N₁]
        exact_mod_cast Nat.lt_floor_add_one
          (((max r 1 - 1 : ℕ) : ℝ) / SimpleGraph.triangleRemovalBound ε)
      have h2 : (N₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h3 := (div_lt_iff₀ hδ).mp (lt_of_lt_of_le h1 h2)
      linarith
    have hf_le := eFunction_le_of_triangleRemovalBound_lt hr1 hε hlt_δ
    have hmul_ε : ((2 * max r 1 - 1 : ℕ) : ℝ) * ε = c / 2 := by
      dsimp [ε]
      have hne : ((2 * max r 1 - 1 : ℕ) : ℝ) ≠ 0 := h2r_pos.ne'
      field_simp [hne]
    have hone_le : (1 : ℝ) ≤ (c / 2) * (n : ℝ) ^ 2 := by
      have h1 : 2 / c < (N₂ : ℝ) := by
        dsimp [N₂]
        exact_mod_cast Nat.lt_floor_add_one (2 / c)
      have h2 : (N₂ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have h3 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        nlinarith
      have hlt : 2 / c < (n : ℝ) ^ 2 := lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h3
      have hmul := (div_lt_iff₀ hc).mp hlt
      linarith
    have hf_nonneg : (0 : ℝ) ≤ (eFunction n (max r 1) : ℝ) := Nat.cast_nonneg _
    have hsq_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg hf_nonneg, Real.norm_of_nonneg hsq_nonneg]
    calc
      (eFunction n (max r 1) : ℝ) ≤ ((2 * max r 1 - 1 : ℕ) : ℝ) * (ε * (n : ℝ) ^ 2) + 1 := hf_le
      _ = (((2 * max r 1 - 1 : ℕ) : ℝ) * ε) * (n : ℝ) ^ 2 + 1 := by ring
      _ = (c / 2) * (n : ℝ) ^ 2 + 1 := by rw [hmul_ε]
      _ ≤ (c / 2) * (n : ℝ) ^ 2 + (c / 2) * (n : ℝ) ^ 2 := by linarith
      _ = c * (n : ℝ) ^ 2 := by ring
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hmax
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 0] with n _
  have hmono : (eFunction n r : ℝ) ≤ (eFunction n (max r 1) : ℝ) := by
    exact_mod_cast eFunction_mono_right (n := n) (le_max_left r 1)
  have h1 : (0 : ℝ) ≤ (eFunction n r : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (eFunction n (max r 1) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2, one_mul]
  exact hmono

theorem eFunction_sub_isLittleO_sq (r k : ℕ) :
    (fun n : ℕ ↦ (eFunction n (r + k) : ℝ) - (eFunction n r : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ 2) :=
  (Erdos600.erdos_600.variants.ruzsa_szemeredi_upper_bound (r + k)).sub
    (Erdos600.erdos_600.variants.ruzsa_szemeredi_upper_bound r)

end TriangleRemovalProofs

/-!
## Vertex-disjoint graph sums, complete-graph saturation, and step-separation inequalities

This section proves universal structural results for `Erdos600.Erdos600Prop` and
`Erdos600.eFunction`:

1. **Extremal Admissible Witness Theory (`IsAdmissibleBookFree` and `maxAdmissibleEdges`):**
   - `maxAdmissibleEdges n r = eFunction n r - 1` is achieved by an explicit extremal
     $r$-book-free triangle-covered graph on `Fin n` (`exists_isAdmissibleBookFree_card_eq_maxAdmissibleEdges`),
     and bounds the edge count of every admissible witness (`card_edgeFinset_le_maxAdmissibleEdges_of_isAdmissibleBookFree`).
2. **Injective Graph Embedding Invariance and Vertex-Monotonicity:**
   - For any vertex embedding `f : α ↪ β`, `SimpleGraph.map f G` preserves triangle multiplicities
     on all edges (`trianglesContaining_map`, `card_trianglesContaining_map`) and `r`-book-free
     admissibility (`isAdmissibleBookFree_map_iff`), establishing vertex monotonicity
     `eFunction_mono_left : m ≤ n → eFunction m r ≤ eFunction n r`.
3. **Vertex-Disjoint Graph Union Superadditivity and Blow-Up Laws:**
   - For vertex-disjoint graphs `G₁, G₂` on `α`, `G₁ ⊔ G₂` has additive edge count and preserves
     exact triangle sets (`trianglesContaining_sup_eq_left_of_mem_edgeFinset`,
     `trianglesContaining_sup_eq_right_of_mem_edgeFinset`).
   - Transporting via `Fin.castAdd` and `Fin.natAdd` (`finDisjointSum`) proves universal
     superadditivity `maxAdmissibleEdges m r + maxAdmissibleEdges n r ≤ maxAdmissibleEdges (m + n) r`,
     shifted threshold superadditivity `(eFunction m r - 1) + eFunction n r ≤ eFunction (m + n) r`,
     iterated blow-up `k * (eFunction n r - 1) + 1 ≤ eFunction (k * n) r`, and the negative control
     falsifying unshifted superadditivity (`eFunction_unshifted_superadditive_false`).
4. **Local Gadget Augmentation, Complete-Graph Saturation Dichotomy, and Step-Separation Tradeoffs:**
   - Cross-step gadget augmentation `eFunction m r + (eFunction k (r + 1) - 1) ≤ eFunction (m + k) (r + 1)`
     and the step-separation conservation inequality
     `eFunction k (r + 1) - 1 ≤ (eFunction (m + k) (r + 1) - eFunction (m + k) r) + (eFunction (m + k) r - eFunction m r)`.
   - Universal complete-graph triangle multiplicity `trianglesContaining_card_eq_of_eq_top`,
     yielding `eFunction n r ≤ n.choose 2` whenever `3 ≤ n` and `r ≤ n - 2`, the exact saturation
     dichotomy `eFunction n r = n.choose 2 + 1 ↔ n - 1 ≤ r` for `3 ≤ n`, strict local step
     separation at `n = r + 2`, and the exact $n = 4$ values `eFunction 4 2 = 4`, `eFunction 4 3 = 7`.
-/

section DisjointUnionAndStepSeparation
open scoped Classical

/-- A graph `G` is `r`-book-free and triangle-covered if every edge lies in at least `1` and at most `r - 1` triangles. -/
def IsAdmissibleBookFree {α : Type*} [Fintype α] (G : SimpleGraph α) (r : ℕ) : Prop :=
  (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) ∧
    (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).card < r)

/-- The maximum number of edges in an `r`-book-free triangle-covered graph on `Fin n`. -/
noncomputable def maxAdmissibleEdges (n r : ℕ) : ℕ := eFunction n r - 1

theorem eFunction_eq_maxAdmissibleEdges_add_one (n r : ℕ) :
    eFunction n r = maxAdmissibleEdges n r + 1 := by
  have h := one_le_eFunction n r
  dsimp [maxAdmissibleEdges]
  omega

theorem isAdmissibleBookFree_mono {α : Type*} [Fintype α]
    {G : SimpleGraph α} {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) (hG : IsAdmissibleBookFree G r₁) :
    IsAdmissibleBookFree G r₂ :=
  ⟨hG.1, fun uv huv ↦ (hG.2 uv huv).trans_le hr⟩

theorem isAdmissibleBookFree_bot (α : Type*) [Fintype α] (r : ℕ) :
    IsAdmissibleBookFree (⊥ : SimpleGraph α) r := by
  refine ⟨?_, ?_⟩ <;> intro uv huv <;> simp at huv

theorem card_edgeFinset_lt_eFunction_of_isAdmissibleBookFree {n r : ℕ}
    {G : SimpleGraph (Fin n)} (hG : IsAdmissibleBookFree G r) :
    G.edgeFinset.card < eFunction n r := by
  by_contra hge
  have hle : eFunction n r ≤ G.edgeFinset.card := by omega
  obtain ⟨uv, huv, hcard⟩ := erdos600Prop_eFunction n r G hle hG.1
  have hlt := hG.2 uv huv
  omega

theorem card_edgeFinset_le_maxAdmissibleEdges_of_isAdmissibleBookFree {n r : ℕ}
    {G : SimpleGraph (Fin n)} (hG : IsAdmissibleBookFree G r) :
    G.edgeFinset.card ≤ maxAdmissibleEdges n r := by
  have hlt := card_edgeFinset_lt_eFunction_of_isAdmissibleBookFree hG
  have heq := eFunction_eq_maxAdmissibleEdges_add_one n r
  omega

theorem succ_card_edgeFinset_le_eFunction_of_isAdmissibleBookFree {n r : ℕ}
    {G : SimpleGraph (Fin n)} (hG : IsAdmissibleBookFree G r) :
    G.edgeFinset.card + 1 ≤ eFunction n r :=
  card_edgeFinset_lt_eFunction_of_isAdmissibleBookFree hG

theorem exists_isAdmissibleBookFree_card_eq_maxAdmissibleEdges (n r : ℕ) :
    ∃ G : SimpleGraph (Fin n), IsAdmissibleBookFree G r ∧
      G.edgeFinset.card = maxAdmissibleEdges n r := by
  have hnot : ¬ Erdos600Prop n (maxAdmissibleEdges n r) r := by
    rw [erdos600Prop_iff_eFunction_le]
    have heq := eFunction_eq_maxAdmissibleEdges_add_one n r
    omega
  unfold Erdos600Prop at hnot
  push Not at hnot
  obtain ⟨G, hge, htri, hlt⟩ := hnot
  have hadm : IsAdmissibleBookFree G r := ⟨htri, hlt⟩
  have hle := card_edgeFinset_le_maxAdmissibleEdges_of_isAdmissibleBookFree hadm
  exact ⟨G, hadm, by omega⟩

theorem maxAdmissibleEdges_mono_right {n r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) :
    maxAdmissibleEdges n r₁ ≤ maxAdmissibleEdges n r₂ := by
  have h := eFunction_mono_right (n := n) hr
  dsimp [maxAdmissibleEdges]
  omega

theorem map_adj_apply_iff {α β : Type*} (f : α ↪ β) (G : SimpleGraph α) (a b : α) :
    (G.map f).Adj (f a) (f b) ↔ G.Adj a b := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u1, v1, hadj, hu, hv⟩
    rwa [f.injective hu, f.injective hv] at hadj
  · intro hadj
    exact ⟨a, b, hadj, rfl, rfl⟩

theorem trianglesContaining_map {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) (G : SimpleGraph α) (uv : Sym2 α) :
    (G.map f).trianglesContaining (f.sym2Map uv) =
      (G.trianglesContaining uv).map ⟨Finset.map f, Finset.map_injective f⟩ := by
  ext t
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_trianglesContaining_iff,
    SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · rintro ⟨hclique, hsym⟩
    have hmap : (Finset.univ.filter (fun a : α ↦ f a ∈ t)).map f = t := by
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hy
        induction uv using Sym2.ind with
        | _ u v =>
          have hu_t : f u ∈ t := by
            have hmem : f.sym2Map s(u, v) = s(f u, f v) := rfl
            rw [hmem] at hsym
            exact Finset.mem_sym2_iff.mp hsym (f u) (Sym2.mem_mk_left (f u) (f v))
          by_cases hyu : y = f u
          · subst hyu
            exact ⟨u, hu_t, rfl⟩
          · have hadj : (G.map f).Adj (f u) y := hclique.isClique hu_t hy (Ne.symm hyu)
            rw [SimpleGraph.map_adj] at hadj
            rcases hadj with ⟨u1, v1, _, _, rfl⟩
            exact ⟨v1, hy, rfl⟩
    refine ⟨Finset.univ.filter (fun a : α ↦ f a ∈ t), ⟨?_, ?_⟩, hmap⟩
    · rw [SimpleGraph.isNClique_iff]
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_filter] at ha hb
        exact (map_adj_apply_iff f G a b).mp (hclique.isClique ha.2 hb.2 (f.injective.ne hab))
      · rw [← Finset.card_map f, hmap, hclique.card_eq]
    · induction uv using Sym2.ind with
      | _ u v =>
        have hmem : f.sym2Map s(u, v) = s(f u, f v) := rfl
        rw [hmem] at hsym
        rw [Finset.mem_sym2_iff]
        intro a ha
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ a, ?_⟩
        rcases Sym2.mem_iff.mp ha with ha1 | ha2
        · rw [ha1]
          exact Finset.mem_sym2_iff.mp hsym (f u) (Sym2.mem_mk_left (f u) (f v))
        · rw [ha2]
          exact Finset.mem_sym2_iff.mp hsym (f v) (Sym2.mem_mk_right (f u) (f v))
  · rintro ⟨s, ⟨hclique, hsym⟩, rfl⟩
    refine ⟨hclique.map, ?_⟩
    induction uv using Sym2.ind with
    | _ u v =>
      have hmem : f.sym2Map s(u, v) = s(f u, f v) := rfl
      rw [hmem, Finset.mem_sym2_iff]
      intro y hy
      rcases Sym2.mem_iff.mp hy with hy1 | hy2
      · rw [hy1]
        exact Finset.mem_map.mpr ⟨u, Finset.mem_sym2_iff.mp hsym u (Sym2.mem_mk_left u v), rfl⟩
      · rw [hy2]
        exact Finset.mem_map.mpr ⟨v, Finset.mem_sym2_iff.mp hsym v (Sym2.mem_mk_right u v), rfl⟩

theorem card_trianglesContaining_map {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) (G : SimpleGraph α) (uv : Sym2 α) :
    ((G.map f).trianglesContaining (f.sym2Map uv)).card =
      (G.trianglesContaining uv).card := by
  rw [trianglesContaining_map, Finset.card_map]

theorem nonempty_trianglesContaining_map {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) (G : SimpleGraph α) (uv : Sym2 α) :
    ((G.map f).trianglesContaining (f.sym2Map uv)).Nonempty ↔
      (G.trianglesContaining uv).Nonempty := by
  rw [trianglesContaining_map, Finset.map_nonempty]

theorem edgeFinset_map_eq {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) (G : SimpleGraph α)
    {instM : Fintype (G.map f).edgeSet} [instG : Fintype G.edgeSet] :
    @SimpleGraph.edgeFinset β (G.map f) instM =
      (@SimpleGraph.edgeFinset α G instG).map f.sym2Map := by
  convert SimpleGraph.edgeFinset_map f G

theorem card_edgeFinset_map_eq {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) (G : SimpleGraph α)
    {instM : Fintype (G.map f).edgeSet} [instG : Fintype G.edgeSet] :
    (@SimpleGraph.edgeFinset β (G.map f) instM).card =
      (@SimpleGraph.edgeFinset α G instG).card := by
  rw [edgeFinset_map_eq f G (instG := instG), Finset.card_map]

theorem isAdmissibleBookFree_map_iff {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) (G : SimpleGraph α) (r : ℕ) :
    IsAdmissibleBookFree (G.map f) r ↔ IsAdmissibleBookFree G r := by
  unfold IsAdmissibleBookFree
  rw [edgeFinset_map_eq f G]
  constructor
  · rintro ⟨htri, hlt⟩
    refine ⟨fun uv huv ↦ ?_, fun uv huv ↦ ?_⟩
    · exact (nonempty_trianglesContaining_map f G uv).mp
        (htri (f.sym2Map uv) (Finset.mem_map_of_mem f.sym2Map huv))
    · rw [← card_trianglesContaining_map f G uv]
      exact hlt (f.sym2Map uv) (Finset.mem_map_of_mem f.sym2Map huv)
  · rintro ⟨htri, hlt⟩
    refine ⟨fun e he ↦ ?_, fun e he ↦ ?_⟩
    · rcases Finset.mem_map.mp he with ⟨uv, huv, rfl⟩
      exact (nonempty_trianglesContaining_map f G uv).mpr (htri uv huv)
    · rcases Finset.mem_map.mp he with ⟨uv, huv, rfl⟩
      rw [card_trianglesContaining_map f G uv]
      exact hlt uv huv

/-- Canonical embedding of `Fin m` into `Fin n` when `m ≤ n`. -/
def castLEEmb {m n : ℕ} (hmn : m ≤ n) : Fin m ↪ Fin n :=
  ⟨Fin.castLE hmn, Fin.castLE_injective hmn⟩

theorem erdos600Prop_anti_vertices {m n e r : ℕ} (hmn : m ≤ n)
    (h : Erdos600Prop n e r) : Erdos600Prop m e r := by
  intro G hG htri
  by_contra hnot
  push Not at hnot
  have hadm_G : IsAdmissibleBookFree G r := ⟨htri, hnot⟩
  have hadm_map : IsAdmissibleBookFree (G.map (castLEEmb hmn)) r :=
    (isAdmissibleBookFree_map_iff (castLEEmb hmn) G r).mpr hadm_G
  obtain ⟨uv, huv, hge⟩ := h (G.map (castLEEmb hmn))
    (by rw [card_edgeFinset_map_eq (castLEEmb hmn) G]; exact hG) hadm_map.1
  have hlt := hadm_map.2 uv huv
  omega

theorem eFunction_mono_left {m n : ℕ} (hmn : m ≤ n) (r : ℕ) :
    eFunction m r ≤ eFunction n r := by
  rw [← erdos600Prop_iff_eFunction_le]
  exact erdos600Prop_anti_vertices hmn (erdos600Prop_eFunction n r)

theorem maxAdmissibleEdges_mono_left {m n : ℕ} (hmn : m ≤ n) (r : ℕ) :
    maxAdmissibleEdges m r ≤ maxAdmissibleEdges n r := by
  have h := eFunction_mono_left hmn r
  dsimp [maxAdmissibleEdges]
  omega

theorem edgeFinset_sup_eq {α : Type*} [Fintype α] (G₁ G₂ : SimpleGraph α)
    {instS : Fintype (G₁ ⊔ G₂).edgeSet}
    [inst₁ : Fintype G₁.edgeSet] [inst₂ : Fintype G₂.edgeSet] :
    @SimpleGraph.edgeFinset α (G₁ ⊔ G₂) instS =
      @SimpleGraph.edgeFinset α G₁ inst₁ ∪ @SimpleGraph.edgeFinset α G₂ inst₂ := by
  ext e
  simp [SimpleGraph.mem_edgeFinset]

theorem disjoint_edgeFinset_of_forall_adj_not_adj {α : Type*} [Fintype α]
    {G₁ G₂ : SimpleGraph α} [inst₁ : Fintype G₁.edgeSet] [inst₂ : Fintype G₂.edgeSet]
    (hdisj : ∀ ⦃u v w : α⦄, G₁.Adj u v → ¬ G₂.Adj u w) :
    Disjoint (@SimpleGraph.edgeFinset α G₁ inst₁) (@SimpleGraph.edgeFinset α G₂ inst₂) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  induction e using Sym2.ind with
  | _ u v =>
    exact hdisj (SimpleGraph.mem_edgeFinset.mp he1) (SimpleGraph.mem_edgeFinset.mp he2)

theorem card_edgeFinset_sup_of_forall_adj_not_adj {α : Type*} [Fintype α]
    {G₁ G₂ : SimpleGraph α} {instS : Fintype (G₁ ⊔ G₂).edgeSet}
    [inst₁ : Fintype G₁.edgeSet] [inst₂ : Fintype G₂.edgeSet]
    (hdisj : ∀ ⦃u v w : α⦄, G₁.Adj u v → ¬ G₂.Adj u w) :
    (@SimpleGraph.edgeFinset α (G₁ ⊔ G₂) instS).card =
      (@SimpleGraph.edgeFinset α G₁ inst₁).card + (@SimpleGraph.edgeFinset α G₂ inst₂).card := by
  rw [edgeFinset_sup_eq G₁ G₂ (inst₁ := inst₁) (inst₂ := inst₂),
    Finset.card_union_of_disjoint (disjoint_edgeFinset_of_forall_adj_not_adj hdisj)]

theorem trianglesContaining_sup_eq_left_of_mem_edgeFinset {α : Type*} [Fintype α]
    {G₁ G₂ : SimpleGraph α} (hdisj : ∀ ⦃u v w : α⦄, G₁.Adj u v → ¬ G₂.Adj u w)
    {uv : Sym2 α} (huv : uv ∈ G₁.edgeFinset) :
    (G₁ ⊔ G₂).trianglesContaining uv = G₁.trianglesContaining uv := by
  ext t
  simp only [mem_trianglesContaining_iff, SimpleGraph.mem_cliqueFinset_iff,
    SimpleGraph.isNClique_iff]
  constructor
  · rintro ⟨⟨hclique, hcard⟩, hsym⟩
    refine ⟨⟨?_, hcard⟩, hsym⟩
    intro x hx y hy hxy
    have hadj : G₁.Adj x y ∨ G₂.Adj x y := hclique hx hy hxy
    rcases hadj with h1 | h2
    · exact h1
    · exfalso
      induction uv using Sym2.ind with
      | _ u v =>
        have huv_adj : G₁.Adj u v := SimpleGraph.mem_edgeFinset.mp huv
        have hu_t : u ∈ t := Finset.mem_sym2_iff.mp hsym u (Sym2.mem_mk_left u v)
        by_cases hxu : x = u
        · subst hxu
          exact hdisj huv_adj h2
        · have hux : G₁.Adj u x ∨ G₂.Adj u x := hclique hu_t hx (Ne.symm hxu)
          rcases hux with hux1 | hux2
          · exact hdisj hux1.symm h2
          · exact hdisj huv_adj hux2
  · rintro ⟨⟨hclique, hcard⟩, hsym⟩
    refine ⟨⟨?_, hcard⟩, hsym⟩
    exact hclique.mono le_sup_left

theorem trianglesContaining_sup_eq_right_of_mem_edgeFinset {α : Type*} [Fintype α]
    {G₁ G₂ : SimpleGraph α} (hdisj : ∀ ⦃u v w : α⦄, G₁.Adj u v → ¬ G₂.Adj u w)
    {uv : Sym2 α} (huv : uv ∈ G₂.edgeFinset) :
    (G₁ ⊔ G₂).trianglesContaining uv = G₂.trianglesContaining uv := by
  have hdisj_symm : ∀ ⦃u v w : α⦄, G₂.Adj u v → ¬ G₁.Adj u w := by
    intro u v w h2 h1
    exact hdisj h1 h2
  rw [sup_comm]
  exact trianglesContaining_sup_eq_left_of_mem_edgeFinset hdisj_symm huv

theorem isAdmissibleBookFree_sup_of_forall_adj_not_adj {α : Type*} [Fintype α]
    {G₁ G₂ : SimpleGraph α} (hdisj : ∀ ⦃u v w : α⦄, G₁.Adj u v → ¬ G₂.Adj u w)
    {r₁ r₂ : ℕ} (h₁ : IsAdmissibleBookFree G₁ r₁) (h₂ : IsAdmissibleBookFree G₂ r₂) :
    IsAdmissibleBookFree (G₁ ⊔ G₂) (max r₁ r₂) := by
  refine ⟨fun uv huv ↦ ?_, fun uv huv ↦ ?_⟩
  · rw [edgeFinset_sup_eq G₁ G₂, Finset.mem_union] at huv
    rcases huv with huv1 | huv2
    · rw [trianglesContaining_sup_eq_left_of_mem_edgeFinset hdisj huv1]
      exact h₁.1 uv huv1
    · rw [trianglesContaining_sup_eq_right_of_mem_edgeFinset hdisj huv2]
      exact h₂.1 uv huv2
  · rw [edgeFinset_sup_eq G₁ G₂, Finset.mem_union] at huv
    rcases huv with huv1 | huv2
    · rw [trianglesContaining_sup_eq_left_of_mem_edgeFinset hdisj huv1]
      exact (h₁.2 uv huv1).trans_le (le_max_left r₁ r₂)
    · rw [trianglesContaining_sup_eq_right_of_mem_edgeFinset hdisj huv2]
      exact (h₂.2 uv huv2).trans_le (le_max_right r₁ r₂)

theorem isAdmissibleBookFree_sup_iff_of_forall_adj_not_adj {α : Type*} [Fintype α]
    {G₁ G₂ : SimpleGraph α} (hdisj : ∀ ⦃u v w : α⦄, G₁.Adj u v → ¬ G₂.Adj u w) (r : ℕ) :
    IsAdmissibleBookFree (G₁ ⊔ G₂) r ↔
      IsAdmissibleBookFree G₁ r ∧ IsAdmissibleBookFree G₂ r := by
  constructor
  · rintro ⟨htri, hlt⟩
    refine ⟨⟨fun uv huv ↦ ?_, fun uv huv ↦ ?_⟩, ⟨fun uv huv ↦ ?_, fun uv huv ↦ ?_⟩⟩
    · rw [← trianglesContaining_sup_eq_left_of_mem_edgeFinset hdisj huv]
      refine htri uv ?_
      rw [edgeFinset_sup_eq G₁ G₂]
      exact Finset.mem_union_left _ huv
    · rw [← trianglesContaining_sup_eq_left_of_mem_edgeFinset hdisj huv]
      refine hlt uv ?_
      rw [edgeFinset_sup_eq G₁ G₂]
      exact Finset.mem_union_left _ huv
    · rw [← trianglesContaining_sup_eq_right_of_mem_edgeFinset hdisj huv]
      refine htri uv ?_
      rw [edgeFinset_sup_eq G₁ G₂]
      exact Finset.mem_union_right _ huv
    · rw [← trianglesContaining_sup_eq_right_of_mem_edgeFinset hdisj huv]
      refine hlt uv ?_
      rw [edgeFinset_sup_eq G₁ G₂]
      exact Finset.mem_union_right _ huv
  · rintro ⟨h₁, h₂⟩
    have hmax := isAdmissibleBookFree_sup_of_forall_adj_not_adj hdisj h₁ h₂
    simpa using hmax

/-- Left block embedding `Fin m ↪ Fin (m + n)`. -/
def castAddEmb (m n : ℕ) : Fin m ↪ Fin (m + n) :=
  ⟨Fin.castAdd n, Fin.castAdd_injective m n⟩

/-- Right block embedding `Fin n ↪ Fin (m + n)`. -/
def natAddEmb (m n : ℕ) : Fin n ↪ Fin (m + n) :=
  ⟨Fin.natAdd m, Fin.natAdd_injective n m⟩

/-- Vertex-disjoint sum of `G : SimpleGraph (Fin m)` and `H : SimpleGraph (Fin n)` on `Fin (m + n)`. -/
def finDisjointSum {m n : ℕ} (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n)) :
    SimpleGraph (Fin (m + n)) :=
  (G.map (castAddEmb m n)) ⊔ (H.map (natAddEmb m n))

theorem fin_castAdd_ne_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have hval : (Fin.castAdd n i).val = (Fin.natAdd m j).val := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hval
  omega

theorem forall_adj_not_adj_map_castAdd_natAdd {m n : ℕ}
    (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n)) :
    ∀ ⦃u v w : Fin (m + n)⦄,
      (G.map (castAddEmb m n)).Adj u v →
      ¬ (H.map (natAddEmb m n)).Adj u w := by
  intro u v w hG hH
  rw [SimpleGraph.map_adj] at hG hH
  rcases hG with ⟨u1, _, _, rfl, _⟩
  rcases hH with ⟨u2, _, _, hu2, _⟩
  exact fin_castAdd_ne_natAdd u1 u2 (by simpa [castAddEmb, natAddEmb] using hu2.symm)

theorem card_edgeFinset_finDisjointSum {m n : ℕ}
    (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n)) :
    (finDisjointSum G H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  unfold finDisjointSum
  rw [card_edgeFinset_sup_of_forall_adj_not_adj (forall_adj_not_adj_map_castAdd_natAdd G H),
    card_edgeFinset_map_eq (castAddEmb m n) G, card_edgeFinset_map_eq (natAddEmb m n) H]

theorem isAdmissibleBookFree_finDisjointSum {m n r₁ r₂ : ℕ}
    {G : SimpleGraph (Fin m)} {H : SimpleGraph (Fin n)}
    (hG : IsAdmissibleBookFree G r₁) (hH : IsAdmissibleBookFree H r₂) :
    IsAdmissibleBookFree (finDisjointSum G H) (max r₁ r₂) := by
  unfold finDisjointSum
  refine isAdmissibleBookFree_sup_of_forall_adj_not_adj
    (forall_adj_not_adj_map_castAdd_natAdd G H) ?_ ?_
  · exact (isAdmissibleBookFree_map_iff (castAddEmb m n) G r₁).mpr hG
  · exact (isAdmissibleBookFree_map_iff (natAddEmb m n) H r₂).mpr hH

theorem isAdmissibleBookFree_finDisjointSum_iff {m n r : ℕ}
    (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n)) :
    IsAdmissibleBookFree (finDisjointSum G H) r ↔
      IsAdmissibleBookFree G r ∧ IsAdmissibleBookFree H r := by
  unfold finDisjointSum
  rw [isAdmissibleBookFree_sup_iff_of_forall_adj_not_adj
    (forall_adj_not_adj_map_castAdd_natAdd G H),
    isAdmissibleBookFree_map_iff (castAddEmb m n), isAdmissibleBookFree_map_iff (natAddEmb m n)]

theorem maxAdmissibleEdges_add_le_max (m n r₁ r₂ : ℕ) :
    maxAdmissibleEdges m r₁ + maxAdmissibleEdges n r₂ ≤
      maxAdmissibleEdges (m + n) (max r₁ r₂) := by
  obtain ⟨G, hG, hcardG⟩ := exists_isAdmissibleBookFree_card_eq_maxAdmissibleEdges m r₁
  obtain ⟨H, hH, hcardH⟩ := exists_isAdmissibleBookFree_card_eq_maxAdmissibleEdges n r₂
  have hadm := isAdmissibleBookFree_finDisjointSum hG hH
  have hle := card_edgeFinset_le_maxAdmissibleEdges_of_isAdmissibleBookFree hadm
  rw [card_edgeFinset_finDisjointSum, hcardG, hcardH] at hle
  exact hle

theorem maxAdmissibleEdges_superadditive (m n r : ℕ) :
    maxAdmissibleEdges m r + maxAdmissibleEdges n r ≤ maxAdmissibleEdges (m + n) r := by
  simpa using maxAdmissibleEdges_add_le_max m n r r

theorem eFunction_shifted_superadditive (m n r : ℕ) :
    (eFunction m r - 1) + eFunction n r ≤ eFunction (m + n) r := by
  have h := maxAdmissibleEdges_superadditive m n r
  have hm := eFunction_eq_maxAdmissibleEdges_add_one m r
  have hn := eFunction_eq_maxAdmissibleEdges_add_one n r
  have hmn := eFunction_eq_maxAdmissibleEdges_add_one (m + n) r
  dsimp [maxAdmissibleEdges] at h hm hn hmn
  omega

theorem eFunction_add_le_add_one (m n r : ℕ) :
    eFunction m r + eFunction n r ≤ eFunction (m + n) r + 1 := by
  have h := eFunction_shifted_superadditive m n r
  have hm := one_le_eFunction m r
  omega

theorem mul_maxAdmissibleEdges_le (k n r : ℕ) :
    k * maxAdmissibleEdges n r ≤ maxAdmissibleEdges (k * n) r := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hadd : (k + 1) * n = k * n + n := Nat.succ_mul k n
    rw [Nat.succ_mul, hadd]
    exact (Nat.add_le_add_right ih _).trans (maxAdmissibleEdges_superadditive (k * n) n r)

theorem mul_sub_one_add_one_le_eFunction (k n r : ℕ) :
    k * (eFunction n r - 1) + 1 ≤ eFunction (k * n) r := by
  have h := mul_maxAdmissibleEdges_le k n r
  have hkn := eFunction_eq_maxAdmissibleEdges_add_one (k * n) r
  dsimp [maxAdmissibleEdges] at h hkn
  omega

theorem maxAdmissibleEdges_cross_step_superadditive (m k r : ℕ) :
    maxAdmissibleEdges m r + maxAdmissibleEdges k (r + 1) ≤
      maxAdmissibleEdges (m + k) (r + 1) := by
  have h := maxAdmissibleEdges_add_le_max m k r (r + 1)
  have hmax : max r (r + 1) = r + 1 := Nat.max_eq_right (Nat.le_succ r)
  rwa [hmax] at h

theorem eFunction_cross_step_gadget_le (m k r : ℕ) :
    eFunction m r + (eFunction k (r + 1) - 1) ≤ eFunction (m + k) (r + 1) := by
  have h := maxAdmissibleEdges_cross_step_superadditive m k r
  have hm := eFunction_eq_maxAdmissibleEdges_add_one m r
  have hk := eFunction_eq_maxAdmissibleEdges_add_one k (r + 1)
  have hmk := eFunction_eq_maxAdmissibleEdges_add_one (m + k) (r + 1)
  dsimp [maxAdmissibleEdges] at h hm hk hmk
  omega

theorem eFunction_step_separation_tradeoff_nat (m k r : ℕ) :
    eFunction k (r + 1) - 1 ≤
      (eFunction (m + k) (r + 1) - eFunction (m + k) r) +
        (eFunction (m + k) r - eFunction m r) := by
  have hcross := eFunction_cross_step_gadget_le m k r
  have hmono_r := eFunction_mono_right (n := m + k) (Nat.le_succ r)
  have hmono_n := eFunction_mono_left (Nat.le_add_right m k) r
  omega

theorem eFunction_step_separation_tradeoff_real (m k r : ℕ) :
    ((eFunction k (r + 1) : ℝ) - 1) -
        ((eFunction (m + k) r : ℝ) - (eFunction m r : ℝ)) ≤
      (eFunction (m + k) (r + 1) : ℝ) - (eFunction (m + k) r : ℝ) := by
  have hcross := eFunction_cross_step_gadget_le m k r
  have hk1 := one_le_eFunction k (r + 1)
  have hreal : (eFunction m r : ℝ) + ((eFunction k (r + 1) : ℝ) - 1) ≤
      (eFunction (m + k) (r + 1) : ℝ) := by
    have hsub : ((eFunction k (r + 1) - 1 : ℕ) : ℝ) = (eFunction k (r + 1) : ℝ) - 1 :=
      by simpa using Nat.cast_sub hk1
    rw [← hsub]
    exact_mod_cast hcross
  linarith

theorem le_eFunction_step_diff_of_le {n k r : ℕ} (hkn : k ≤ n) :
    ((eFunction k (r + 1) : ℝ) - 1) -
        ((eFunction n r : ℝ) - (eFunction (n - k) r : ℝ)) ≤
      (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ) := by
  have h := eFunction_step_separation_tradeoff_real (n - k) k r
  have hadd : n - k + k = n := Nat.sub_add_cancel hkn
  rwa [hadd] at h

theorem tendsto_step_diff_atTop_of_forall_bound_exists_gadget {r : ℕ}
    (h : ∀ B : ℝ, ∃ k : ℕ, ∀ᶠ n : ℕ in atTop,
      B + ((eFunction n r : ℝ) - (eFunction (n - k) r : ℝ)) ≤
        (eFunction k (r + 1) : ℝ) - 1) :
    Tendsto (fun n : ℕ ↦ (eFunction n (r + 1) : ℝ) - (eFunction n r : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  obtain ⟨k, hk⟩ := h B
  rw [Filter.eventually_atTop] at hk
  obtain ⟨N, hN⟩ := hk
  refine ⟨max N k, fun n hn ↦ ?_⟩
  have hN_le : N ≤ n := (le_max_left N k).trans hn
  have hk_le : k ≤ n := (le_max_right N k).trans hn
  have h1 := hN n hN_le
  have h2 := le_eFunction_step_diff_of_le (r := r) hk_le
  linarith

theorem trianglesContaining_card_eq_of_eq_top {α : Type*} [Fintype α]
    (G : SimpleGraph α) (hG : G = ⊤) {uv : Sym2 α} (huv : uv ∈ G.edgeFinset) :
    (G.trianglesContaining uv).card = Fintype.card α - 2 := by
  have htwo : uv.toFinset.card = 2 :=
    SimpleGraph.card_toFinset_mem_edgeFinset (G := G) ⟨uv, huv⟩
  have heq : G.trianglesContaining uv =
      (Finset.univ \ uv.toFinset).image (fun w : α ↦ insert w uv.toFinset) := by
    ext t
    simp only [Finset.mem_image]
    constructor
    · intro ht
      simp only [SimpleGraph.trianglesContaining, Finset.mem_filter,
        SimpleGraph.mem_cliqueFinset_iff] at ht
      obtain ⟨hclique, hsub_uv⟩ := ht
      have hcard_t : t.card = 3 := hclique.card_eq
      have hcard_sdiff : (t \ uv.toFinset).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsub_uv, hcard_t, htwo]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard_sdiff
      have hw_mem : w ∈ t \ uv.toFinset := by rw [hw]; simp
      have hw_univ : w ∈ Finset.univ \ uv.toFinset := by
        simp [(Finset.mem_sdiff.mp hw_mem).2]
      refine ⟨w, hw_univ, ?_⟩
      calc
        insert w uv.toFinset = {w} ∪ uv.toFinset := by ext x; simp
        _ = (t \ uv.toFinset) ∪ uv.toFinset := by rw [hw]
        _ = t := Finset.sdiff_union_of_subset hsub_uv
    · rintro ⟨w, hw, rfl⟩
      have hw_not : w ∉ uv.toFinset := (Finset.mem_sdiff.mp hw).2
      have hcard_t : (insert w uv.toFinset).card = 3 := by
        rw [Finset.card_insert_of_notMem hw_not, htwo]
      have hclique : insert w uv.toFinset ∈ G.cliqueFinset 3 := by
        rw [SimpleGraph.mem_cliqueFinset_iff, hG]
        exact ⟨SimpleGraph.IsClique.top _, hcard_t⟩
      exact Finset.mem_filter.mpr ⟨hclique, Finset.subset_insert _ _⟩
  rw [heq, Finset.card_image_of_injOn]
  · have hsub_univ : uv.toFinset ⊆ (Finset.univ : Finset α) := Finset.subset_univ _
    rw [Finset.card_sdiff_of_subset hsub_univ, Finset.card_univ, htwo]
  · intro w₁ hw₁ w₂ _ hw_eq
    dsimp at hw_eq
    have hw₁_not : w₁ ∉ uv.toFinset := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hw₁)).2
    have hmem : w₁ ∈ (insert w₂ uv.toFinset : Finset α) := by
      rw [← hw_eq]
      exact Finset.mem_insert_self w₁ uv.toFinset
    rcases Finset.mem_insert.mp hmem with rfl | h2
    · rfl
    · exact (hw₁_not h2).elim

theorem eq_top_of_card_edgeFinset_eq_choose_two {α : Type*} [Fintype α]
    (G : SimpleGraph α) (hcard : G.edgeFinset.card = (Fintype.card α).choose 2) :
    G = ⊤ := by
  have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph α).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have htop : (⊤ : SimpleGraph α).edgeFinset.card = (Fintype.card α).choose 2 :=
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two
  have hedge_eq : G.edgeFinset = (⊤ : SimpleGraph α).edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact SimpleGraph.edgeFinset_inj.mp hedge_eq

theorem erdos600Prop_choose_two_of_le_sub_two {n r : ℕ}
    (hn : 3 ≤ n) (hr : r ≤ n - 2) :
    Erdos600Prop n (n.choose 2) r := by
  intro G hG _
  have hmax : G.edgeFinset.card ≤ n.choose 2 := by
    simpa using SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
  have heq : G.edgeFinset.card = (Fintype.card (Fin n)).choose 2 := by
    rw [Fintype.card_fin]
    omega
  have hG_top : G = ⊤ := eq_top_of_card_edgeFinset_eq_choose_two G heq
  have hchoose_pos : 0 < n.choose 2 := Nat.choose_pos (by omega : 2 ≤ n)
  obtain ⟨uv, huv⟩ : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨uv, huv, ?_⟩
  have hcard := trianglesContaining_card_eq_of_eq_top G hG_top huv
  rw [Fintype.card_fin] at hcard
  omega

theorem eFunction_le_choose_two_of_le_sub_two {n r : ℕ}
    (hn : 3 ≤ n) (hr : r ≤ n - 2) :
    eFunction n r ≤ n.choose 2 :=
  (erdos600Prop_iff_eFunction_le n (n.choose 2) r).mp
    (erdos600Prop_choose_two_of_le_sub_two hn hr)

theorem eFunction_eq_choose_two_succ_iff_of_three_le {n r : ℕ} (hn : 3 ≤ n) :
    eFunction n r = n.choose 2 + 1 ↔ n - 1 ≤ r := by
  constructor
  · intro heq
    by_contra hlt
    have hr : r ≤ n - 2 := by omega
    have hle := eFunction_le_choose_two_of_le_sub_two hn hr
    omega
  · exact eFunction_eq_choose_two_succ_of_sub_one_le hn

theorem one_le_eFunction_step_diff_at_add_two {r : ℕ} (hr : 1 ≤ r) :
    1 ≤ eFunction (r + 2) (r + 1) - eFunction (r + 2) r := by
  have hn : 3 ≤ r + 2 := by omega
  have hle : eFunction (r + 2) r ≤ (r + 2).choose 2 :=
    eFunction_le_choose_two_of_le_sub_two hn (by omega)
  have heq : eFunction (r + 2) (r + 1) = (r + 2).choose 2 + 1 :=
    eFunction_eq_choose_two_succ_of_sub_one_le hn (by omega)
  omega

theorem eFunction_complete_gadget_augmentation (m : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    eFunction m r + (r + 2).choose 2 ≤ eFunction (m + (r + 2)) (r + 1) := by
  have hcross := eFunction_cross_step_gadget_le m (r + 2) r
  have heq : eFunction (r + 2) (r + 1) = (r + 2).choose 2 + 1 :=
    eFunction_eq_choose_two_succ_of_sub_one_le (by omega) (by omega)
  omega

theorem erdos600Prop_four_four_two : Erdos600Prop 4 4 2 := by
  intro G hG htri
  by_contra hnot
  push Not at hnot
  have hll : G.LocallyLinear := (locallyLinear_iff_trianglesContaining G).mpr ⟨htri, hnot⟩
  have hmul : G.edgeFinset.card = 3 * (G.cliqueFinset 3).card := hll.card_edgeFinset
  have hle6 : G.edgeFinset.card ≤ 6 := by
    have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
    rw [Fintype.card_fin] at h
    exact h.trans (by decide : (4).choose 2 ≤ 6)
  have heq6 : G.edgeFinset.card = (Fintype.card (Fin 4)).choose 2 := by
    rw [Fintype.card_fin]
    have hc : (4).choose 2 = 6 := by decide
    omega
  have hG_top : G = ⊤ := eq_top_of_card_edgeFinset_eq_choose_two G heq6
  obtain ⟨uv, huv⟩ : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have hlt2 := hnot uv huv
  have hcard2 := trianglesContaining_card_eq_of_eq_top G hG_top huv
  rw [Fintype.card_fin] at hcard2
  omega

theorem eFunction_three_two : eFunction 3 2 = 4 := by
  have h := eFunction_eq_choose_two_succ_of_sub_one_le (n := 3) (r := 2) (by omega) (by omega)
  have hc : (3).choose 2 = 3 := by decide
  omega

theorem eFunction_four_two : eFunction 4 2 = 4 := by
  have hle : eFunction 4 2 ≤ 4 :=
    (erdos600Prop_iff_eFunction_le 4 4 2).mp erdos600Prop_four_four_two
  have hge : 4 ≤ eFunction 4 2 := by
    have h32 := eFunction_three_two
    have hm := eFunction_mono_left (by omega : 3 ≤ 4) 2
    omega
  omega

theorem eFunction_four_three : eFunction 4 3 = 7 := by
  have h := eFunction_eq_choose_two_succ_of_sub_one_le (n := 4) (r := 3) (by omega) (by omega)
  have hc : (4).choose 2 = 6 := by decide
  omega

theorem eFunction_four_step_diff : eFunction 4 3 - eFunction 4 2 = 3 := by
  rw [eFunction_four_three, eFunction_four_two]

theorem eFunction_unshifted_superadditive_false :
    ¬ (∀ m n r : ℕ, eFunction m r + eFunction n r ≤ eFunction (m + n) r) := by
  intro h
  have h13 := h 1 3 2
  have h1 : eFunction 1 2 = 1 := eFunction_of_lt_three (by omega) 2
  rw [h1, eFunction_three_two, eFunction_four_two] at h13
  omega

end DisjointUnionAndStepSeparation


end Erdos600