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

public import ShiftGraphHierarchy918
@[expose] public section
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
noncomputable section
open Cardinal SimpleGraph
open Erdos918.CardinalCover Erdos918Transfer
open scoped Cardinal
universe u v

/-! ## Successor-Cardinal Color-Class Pigeonhole and Independent Sets -/

namespace Erdos918PigeonholeWalk

/-- The color class (fiber) of a proper vertex coloring `c : G.Coloring C` at color `i : C`. -/
def colorClassSet {V : Type u} {C : Type v} {G : SimpleGraph V}
    (c : G.Coloring C) (i : C) : Set V :=
  {v : V | c v = i}

/-- Every color class of a proper coloring induces the edgeless graph `⊥`. -/
theorem induce_colorClassSet_eq_bot {V : Type u} {C : Type v} {G : SimpleGraph V}
    (c : G.Coloring C) (i : C) :
    G.induce (colorClassSet c i) = ⊥ := by
  ext u v
  simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
  intro hadj
  exact c.valid hadj (u.2.trans v.2.symm)

/-- Any vertex subset `W : Set V` inducing `⊥` has chromatic cardinal at most `1`. -/
theorem chromatic_induce_eq_bot_le_one {V : Type u} (G : SimpleGraph V) (W : Set V)
    (hbot : G.induce W = ⊥) :
    (G.induce W).chromaticCardinal ≤ 1 := by
  let col : (G.induce W).Coloring (ULift.{u} Unit) :=
    Coloring.mk (fun _ => ⟨()⟩) (by
      intro a b hab
      rw [hbot] at hab
      exact False.elim hab)
  simpa using chromatic_le_of_coloring col

/-- Every color class `colorClassSet c i` induces a subgraph of chromatic cardinal at most `1`. -/
theorem chromatic_induce_colorClassSet_le_one {V : Type u} {C : Type v} {G : SimpleGraph V}
    (c : G.Coloring C) (i : C) :
    (G.induce (colorClassSet c i)).chromaticCardinal ≤ 1 :=
  chromatic_induce_eq_bot_le_one G (colorClassSet c i) (induce_colorClassSet_eq_bot c i)

/-- Canonical equivalence between the sigma type of color classes and the ambient vertex type `V`. -/
def colorClassSigmaEquiv {V : Type u} {C : Type v} {G : SimpleGraph V}
    (c : G.Coloring C) :
    (Σ i : C, colorClassSet c i) ≃ V where
  toFun p := p.2.1
  invFun v := ⟨c v, ⟨v, rfl⟩⟩
  left_inv p := by
    rcases p with ⟨i, ⟨v, hv⟩⟩
    dsimp [colorClassSet] at hv
    subst hv
    rfl
  right_inv _ := rfl

/-- Exact cardinal fiber-sum decomposition of `#V` across the color classes of `c : G.Coloring C`. -/
theorem mk_eq_sum_colorClassSet {V C : Type u} {G : SimpleGraph V}
    (c : G.Coloring C) :
    #V = Cardinal.sum (fun i : C => #(colorClassSet c i)) := by
  rw [← Cardinal.mk_sigma]
  exact Cardinal.mk_congr (colorClassSigmaEquiv c).symm

/-- Upper bound on `#V` when every color class of `c : G.Coloring C` has cardinality at most `μ`. -/
theorem mk_le_mul_of_forall_colorClassSet_le {V C : Type u} {G : SimpleGraph V}
    (c : G.Coloring C) {μ : Cardinal.{u}}
    (hle : ∀ i : C, #(colorClassSet c i) ≤ μ) :
    #V ≤ #C * μ := by
  rw [mk_eq_sum_colorClassSet c]
  calc
    Cardinal.sum (fun i : C => #(colorClassSet c i)) ≤ Cardinal.sum (fun _ : C => μ) :=
      Cardinal.sum_le_sum _ _ hle
    _ = #C * μ := by simp [Cardinal.sum_const]

/-- Infinite cardinal color-class pigeonhole lemma: if `ℵ₀ ≤ μ`, `#C ≤ μ`, and `μ < #V`, then
any proper coloring `c : G.Coloring C` has a color class of cardinality strictly greater than `μ`. -/
theorem exists_colorClassSet_gt_of_coloring {V C : Type u} {G : SimpleGraph V}
    (c : G.Coloring C) {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hC : #C ≤ μ) (hV : μ < #V) :
    ∃ i : C, μ < #(colorClassSet c i) := by
  by_contra hall
  simp only [not_exists, not_lt] at hall
  have hmul : #V ≤ #C * μ := mk_le_mul_of_forall_colorClassSet_le c hall
  have hle : #C * μ ≤ μ := by
    calc
      #C * μ ≤ μ * μ := mul_le_mul' hC le_rfl
      _ = μ := Cardinal.mul_eq_self hμ
  exact (hV.trans_le (hmul.trans hle)).false

/-- Global color-class pigeonhole independent-set theorem (two-cardinal form): if `ℵ₀ ≤ μ`,
`κ ≤ μ`, `G.chromaticCardinal ≤ κ`, and `Order.succ μ ≤ #V`, then `G` contains an independent
vertex set `I : Set V` (`G.induce I = ⊥`, `(G.induce I).chromaticCardinal ≤ 1`) of cardinality
`Order.succ μ ≤ #I`. -/
theorem exists_indep_colorClassSet_succ_le_of_chromatic_le {V : Type u}
    (G : SimpleGraph V) {κ μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hκμ : κ ≤ μ)
    (hcol : G.chromaticCardinal ≤ κ)
    (hV : Order.succ μ ≤ #V) :
    ∃ I : Set V, Order.succ μ ≤ #I ∧ G.induce I = ⊥ ∧
      (G.induce I).chromaticCardinal ≤ 1 := by
  obtain ⟨C, hC, ⟨c⟩⟩ := exists_minimal_palette G
  have hCμ : #C ≤ μ := hC.trans_le (hcol.trans hκμ)
  have hlt : μ < #V := Order.succ_le_iff.mp hV
  obtain ⟨i, hi⟩ := exists_colorClassSet_gt_of_coloring c hμ hCμ hlt
  refine ⟨colorClassSet c i, Order.succ_le_iff.mpr hi, induce_colorClassSet_eq_bot c i,
    chromatic_induce_colorClassSet_le_one c i⟩

/-- Exact successor-cardinal independent-set theorem: if `ℵ₀ ≤ κ`, `#V = Order.succ κ`, and
`G.chromaticCardinal ≤ κ`, then `G` has an independent vertex set `I : Set V` of exact
cardinality `#I = Order.succ κ` with `G.induce I = ⊥` and `(G.induce I).chromaticCardinal ≤ 1`. -/
theorem exists_indep_set_card_eq_succ_of_chromatic_le {V : Type u}
    (G : SimpleGraph V) {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hV : #V = Order.succ κ)
    (hcol : G.chromaticCardinal ≤ κ) :
    ∃ I : Set V, #I = Order.succ κ ∧ G.induce I = ⊥ ∧
      (G.induce I).chromaticCardinal ≤ 1 := by
  obtain ⟨I, hI, hbot, hchr⟩ :=
    exists_indep_colorClassSet_succ_le_of_chromatic_le G hκ le_rfl hcol hV.symm.le
  have hle : #I ≤ Order.succ κ := (Cardinal.mk_set_le I).trans_eq hV
  exact ⟨I, le_antisymm hle hI, hbot, hchr⟩

/-- Downward independent-subset extraction: under `ℵ₀ ≤ μ`, `κ ≤ μ`, `G.chromaticCardinal ≤ κ`,
and `Order.succ μ ≤ #V`, for every cardinal `lam ≤ Order.succ μ` (in particular `lam = μ` and
`lam = Order.succ μ`), there exists `W : Set V` with `#W = lam`, `G.induce W = ⊥`, and
`(G.induce W).chromaticCardinal ≤ 1`. -/
theorem exists_indep_subset_of_card_le_succ {V : Type u}
    (G : SimpleGraph V) {κ μ lam : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hκμ : κ ≤ μ)
    (hcol : G.chromaticCardinal ≤ κ)
    (hV : Order.succ μ ≤ #V)
    (hlam : lam ≤ Order.succ μ) :
    ∃ W : Set V, #W = lam ∧ G.induce W = ⊥ ∧
      (G.induce W).chromaticCardinal ≤ 1 := by
  obtain ⟨I, hI, hbotI, _⟩ :=
    exists_indep_colorClassSet_succ_le_of_chromatic_le G hμ hκμ hcol hV
  obtain ⟨S, hS⟩ := Cardinal.le_mk_iff_exists_set.mp (hlam.trans hI)
  let W : Set V := Subtype.val '' S
  have hWI : W ⊆ I := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  have hWcard : #W = lam := by
    calc
      #W = #S := Cardinal.mk_image_eq Subtype.val_injective
      _ = lam := hS
  have hWbot : G.induce W = ⊥ := by
    ext u v
    simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
    intro hadj
    have hadjI : (G.induce I).Adj ⟨u.1, hWI u.2⟩ ⟨v.1, hWI v.2⟩ := hadj
    rw [hbotI] at hadjI
    exact hadjI
  exact ⟨W, hWcard, hWbot, chromatic_induce_eq_bot_le_one G W hWbot⟩

/-- Local-to-independent-subset extraction at a successor cardinal `Order.succ κ`: if `ℵ₀ ≤ κ`,
`Order.succ κ ≤ #V`, and some (or every) `U : Set V` of size `#U = Order.succ κ` has
`(G.induce U).chromaticCardinal ≤ κ`, then `G` contains an independent vertex set `W : Set V` of
exact size `#W = Order.succ κ` with `G.induce W = ⊥` and `(G.induce W).chromaticCardinal ≤ 1`. -/
theorem exists_indep_set_of_local_succ_chromatic_le {V : Type u}
    (G : SimpleGraph V) {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hV : Order.succ κ ≤ #V)
    (hlocal : ∀ W : Set V, #W = Order.succ κ → (G.induce W).chromaticCardinal ≤ κ) :
    ∃ W : Set V, #W = Order.succ κ ∧ G.induce W = ⊥ ∧
      (G.induce W).chromaticCardinal ≤ 1 := by
  obtain ⟨U, hU⟩ := Cardinal.le_mk_iff_exists_set.mp hV
  have hUcol : (G.induce U).chromaticCardinal ≤ κ := hlocal U hU
  obtain ⟨I, hI, hbotI, _⟩ :=
    exists_indep_set_card_eq_succ_of_chromatic_le (G.induce U) hκ hU hUcol
  let W : Set V := Subtype.val '' I
  have hWcard : #W = Order.succ κ := by
    calc
      #W = #I := Cardinal.mk_image_eq Subtype.val_injective
      _ = Order.succ κ := hI
  have hWbot : G.induce W = ⊥ := by
    ext u v
    simp only [SimpleGraph.induce_adj, SimpleGraph.bot_adj, iff_false]
    intro hadj
    rcases u with ⟨u_val, ⟨u_sub, huI, rfl⟩⟩
    rcases v with ⟨v_val, ⟨v_sub, hvI, rfl⟩⟩
    have hadjI : ((G.induce U).induce I).Adj ⟨u_sub, huI⟩ ⟨v_sub, hvI⟩ := hadj
    rw [hbotI] at hadjI
    exact hadjI
  exact ⟨W, hWcard, hWbot, chromatic_induce_eq_bot_le_one G W hWbot⟩

/-- Impossibility of constant non-edgeless induced chromatic cardinal at `Order.succ κ`:
if `ℵ₀ ≤ κ`, `2 ≤ μ`, `μ ≤ κ`, and `Order.succ κ ≤ #V`, then no graph `G` on `V` can satisfy
`∀ W : Set V, #W = Order.succ κ → (G.induce W).chromaticCardinal = μ`. -/
theorem not_forall_induce_chromatic_eq_of_succ {V : Type u}
    (G : SimpleGraph V) {κ μ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (h2 : (2 : Cardinal.{u}) ≤ μ) (hμκ : μ ≤ κ)
    (hV : Order.succ κ ≤ #V) :
    ¬ (∀ W : Set V, #W = Order.succ κ → (G.induce W).chromaticCardinal = μ) := by
  intro hall
  have hlocal : ∀ W : Set V, #W = Order.succ κ → (G.induce W).chromaticCardinal ≤ κ :=
    fun W hW => (hall W hW).le.trans hμκ
  obtain ⟨W, hW, _, hchr⟩ := exists_indep_set_of_local_succ_chromatic_le G hκ hV hlocal
  have heq : (G.induce W).chromaticCardinal = μ := hall W hW
  have hle1 : μ ≤ 1 := heq.symm.le.trans hchr
  have h2le1 : (2 : Cardinal.{u}) ≤ 1 := h2.trans hle1
  norm_num at h2le1

/-! ## Refutations of Induced and All-Subgraph Equality Formulations -/

/-- Requiring chromatic cardinal equal to `ℵ₀` for every ordinary subgraph of size `κ ≤ #V` is
impossible, since the edgeless subgraph on `W` (`#W = κ`) has chromatic cardinal at most `1`. -/
theorem not_all_subgraphs_equal_aleph0 {V : Type u} (G : SimpleGraph V)
    (κ : Cardinal.{u}) (hV : κ ≤ #V) :
    ¬ (∀ H : G.Subgraph, #H.verts = κ → H.coe.chromaticCardinal = ℵ₀) := by
  obtain ⟨W, hW⟩ := Cardinal.le_mk_iff_exists_set.mp hV
  let H : G.Subgraph := (⊥ : G.Subgraph).induce W
  have hc : H.coe.chromaticCardinal ≤ 1 := by
    let color : H.coe.Coloring (ULift.{u} Unit) := Coloring.mk
      (fun _ => ⟨()⟩) (by intro a b hab; simp [H] at hab)
    simpa using chromatic_le_of_coloring color
  intro h
  have heq := h H hW
  rw [heq] at hc
  exact Cardinal.one_lt_aleph0.not_ge hc

/-- Kernel proof of `erdos_918.variants.eq_aleph_0.parts.i`: in ZFC, there is no graph `G` on `V`
with `#V = ℵ_ 2` (or `#V ≥ ℵ₁`) such that every induced subgraph on `ℵ₁` vertices has chromatic
cardinal equal to `ℵ₀`. -/
theorem not_exists_induced_eq_aleph0_parts_i :
    ¬ ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal = ℵ₀ := by
  rintro ⟨V, G, hV, _, hall⟩
  have hsucc : Order.succ (ℵ₀ : Cardinal.{u}) = ℵ₁ := by
    simpa [Cardinal.aleph_zero] using (Cardinal.succ_aleph (0 : Ordinal.{u}))
  have hVle : Order.succ (ℵ₀ : Cardinal.{u}) ≤ #V := by
    rw [hsucc, hV]
    exact Cardinal.aleph_le_aleph.mpr (by norm_num)
  have h2 : (2 : Cardinal.{u}) ≤ ℵ₀ := by
    simpa using (Cardinal.natCast_lt_aleph0 (n := 2)).le
  apply not_forall_induce_chromatic_eq_of_succ G le_rfl h2 le_rfl hVle
  intro W hW
  rw [hsucc] at hW
  exact hall W hW

/-- Kernel proof of `erdos_918.variants.eq_aleph_0_all_subgraphs.parts.i`: no graph `G` on `ℵ_ 2`
vertices has every `ℵ₁`-vertex subgraph of chromatic cardinal equal to `ℵ₀`. -/
theorem not_exists_all_subgraphs_eq_aleph0_parts_i :
    ¬ ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal = ℵ₀ := by
  rintro ⟨V, G, hV, _, hall⟩
  have hVle : (ℵ₁ : Cardinal.{u}) ≤ #V := by
    rw [hV]
    exact Cardinal.aleph_le_aleph.mpr (by norm_num)
  exact not_all_subgraphs_equal_aleph0 G ℵ₁ hVle hall

/-- For every ordinal `ω ≥ 1` and any graph `G` on `#V = ℵ_ (ω + 1)` vertices with
`G.chromaticCardinal ≤ ℵ₁`, global color-class pigeonhole produces an independent vertex set
`W : Set V` of exact cardinality `#W = ℵ_ ω` with `G.induce W = ⊥` and
`(G.induce W).chromaticCardinal ≤ 1`. -/
theorem exists_indep_set_aleph_omega_of_one_le {V : Type u}
    (G : SimpleGraph V) {ω : Ordinal.{u}} (hω : (1 : Ordinal.{u}) ≤ ω)
    (hV : #V = ℵ_ (ω + 1)) (hcol : G.chromaticCardinal ≤ ℵ₁) :
    ∃ W : Set V, #W = ℵ_ ω ∧ G.induce W = ⊥ ∧
      (G.induce W).chromaticCardinal ≤ 1 := by
  have hμ : ℵ₀ ≤ ℵ_ ω := Cardinal.aleph0_le_aleph ω
  have hκμ : (ℵ₁ : Cardinal.{u}) ≤ ℵ_ ω := by
    simpa using Cardinal.aleph_le_aleph.mpr hω
  have hsucc : Order.succ (ℵ_ ω) ≤ #V := by
    rw [Cardinal.succ_aleph, hV]
  exact exists_indep_subset_of_card_le_succ G hμ hκμ hcol hsucc (Order.le_succ (ℵ_ ω))

/-- Kernel proof of `erdos_918.variants.eq_aleph_0.parts.ii` for all ordinals `ω ≥ 1`:
whenever `(1 : Ordinal.{u}) ≤ ω`, no graph on `ℵ_ (ω + 1)` vertices with chromatic cardinal `ℵ₁`
can have every `ℵ_ ω`-vertex induced subgraph of chromatic cardinal equal to `ℵ₀`. -/
theorem not_exists_induced_eq_aleph0_parts_ii_of_one_le
    {ω : Ordinal.{u}} (hω : (1 : Ordinal.{u}) ≤ ω) :
    ¬ ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal = ℵ₀ := by
  rintro ⟨V, G, hV, hG, hall⟩
  obtain ⟨W, hW, _, hchr⟩ := exists_indep_set_aleph_omega_of_one_le G hω hV hG.le
  have heq : (G.induce W).chromaticCardinal = ℵ₀ := hall W hW
  rw [heq] at hchr
  exact Cardinal.one_lt_aleph0.not_ge hchr

/-- Exact ordinal dichotomy for `erdos_918.variants.eq_aleph_0.parts.ii`:
for an arbitrary ordinal `ω : Ordinal.{u}`, the nonexistence of a graph on `ℵ_ (ω + 1)` vertices
with chromatic cardinal `ℵ₁` and all `ℵ_ ω`-vertex induced subgraphs of chromatic cardinal `ℵ₀`
holds if and only if `(1 : Ordinal.{u}) ≤ ω` (failing at `ω = 0` by `K_{ℵ₁}`). -/
theorem induced_eq_aleph0_parts_ii_negation_iff_one_le (ω : Ordinal.{u}) :
    (¬ ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal = ℵ₀) ↔
      (1 : Ordinal.{u}) ≤ ω := by
  constructor
  · intro hnot
    by_contra hlt
    rw [not_le, Ordinal.lt_one_iff_zero] at hlt
    subst hlt
    exact hnot zero_ordinal_induced_equality_witness
  · exact not_exists_induced_eq_aleph0_parts_ii_of_one_le

/-- Kernel proof of `erdos_918.variants.eq_aleph_0_all_subgraphs.parts.ii`: for every ordinal `ω`,
no graph `G` on `ℵ_ (ω + 1)` vertices has every `ℵ_ ω`-vertex subgraph of chromatic cardinal
equal to `ℵ₀`. -/
theorem not_exists_all_subgraphs_eq_aleph0_parts_ii (ω : Ordinal.{u}) :
    ¬ ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal = ℵ₀ := by
  rintro ⟨V, G, hV, _, hall⟩
  have hle : ℵ_ ω ≤ #V := by
    rw [hV, ← Cardinal.succ_aleph]
    exact Order.le_succ (ℵ_ ω)
  exact not_all_subgraphs_equal_aleph0 G (ℵ_ ω) hle hall

end Erdos918PigeonholeWalk
end
