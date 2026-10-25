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
open scoped BigOperators Cardinal Ordinal
open SimpleGraph Cardinal
universe u v w
open Cardinal SimpleGraph
namespace SimpleGraph

noncomputable def chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}
end SimpleGraph

/-! ## Cardinal Coloring Foundations -/

namespace Erdos918.CardinalCover
variable {V W C : Type u}

theorem exists_minimal_palette (G : SimpleGraph V) :
    ∃ C : Type u, Cardinal.mk C = G.chromaticCardinal ∧ Nonempty (G.Coloring C) := by
  obtain ⟨C, hC, hc⟩ := csInf_mem
    (s := {κ : Cardinal.{u} | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)})
    ⟨Cardinal.mk V, V, rfl, ⟨G.selfColoring⟩⟩
  exact ⟨C, hC, hc⟩

theorem chromatic_le_of_coloring {G : SimpleGraph V} (color : G.Coloring C) :
    G.chromaticCardinal ≤ Cardinal.mk C :=
  csInf_le' ⟨C, rfl, ⟨color⟩⟩

theorem chromatic_mono_hom {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) :
    G.chromaticCardinal ≤ H.chromaticCardinal := by
  obtain ⟨C, hC, ⟨color⟩⟩ := exists_minimal_palette H
  rw [← hC]
  exact chromatic_le_of_coloring (color.comap f)

theorem chromatic_complete (V : Type u) :
    (completeGraph V).chromaticCardinal = Cardinal.mk V := by
  apply le_antisymm (chromatic_le_of_coloring (completeGraph V).selfColoring)
  obtain ⟨C, hC, ⟨color⟩⟩ := exists_minimal_palette (completeGraph V)
  rw [← hC]
  apply Cardinal.mk_le_of_injective
  intro a b heq
  by_contra hne
  exact color.valid hne heq
end Erdos918.CardinalCover
open Cardinal SimpleGraph
open Erdos918.CardinalCover
open scoped Cardinal

/-! ## Complete-Graph Witness at Ordinal Zero -/

namespace Erdos918Transfer

/-- The zero-ordinal instance of the captured induced-equality negation has an
explicit complete-graph counterexample. The host is the type of cardinal aleph1. -/
theorem zero_ordinal_induced_equality_witness :
    ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ ((0 : Ordinal.{u}) + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ W : Set V, #W = ℵ_ (0 : Ordinal.{u}) →
        (G.induce W).chromaticCardinal = ℵ₀ := by
  refine ⟨(ℵ₁ : Cardinal.{u}).out, completeGraph _, ?_, ?_, ?_⟩
  · simp
  · rw [chromatic_complete, Cardinal.mk_out]
  · intro W hW
    rw [SimpleGraph.induce_top, chromatic_complete]
    simpa using hW
end Erdos918Transfer
noncomputable section
open Cardinal SimpleGraph
open Erdos918.CardinalCover Erdos918Transfer
open scoped Cardinal

/-! ## Higher-Order Shift Graphs and the Erdős–Hajnal Iterated Powerset Threshold -/

namespace Erdos918HigherShift

/-- Vertices of the order-`(r + 1)` shift graph `ShiftGraph r α`: strictly increasing `(r + 1)`-tuples
`Fin (r + 1) → α` over a preorder `α`. -/
abbrev ShiftTuple (r : ℕ) (α : Type u) [Preorder α] : Type u :=
  {x : Fin (r + 1) → α // StrictMono x}

/-- Underlying map of the initial `(r + 1)`-window of an `(r + 2)`-tuple `u : ShiftTuple (r + 1) α`. -/
def shiftTupleInit {r : ℕ} {α : Type u} [Preorder α]
    (u : ShiftTuple (r + 1) α) : Fin (r + 1) → α :=
  fun i => u.1 i.castSucc

/-- The initial `(r + 1)`-window of any strictly increasing `(r + 2)`-tuple is strictly monotone. -/
theorem shiftTupleInit_strictMono {r : ℕ} {α : Type u} [Preorder α]
    (u : ShiftTuple (r + 1) α) : StrictMono (shiftTupleInit u) := by
  intro i j hij
  exact u.2 (Fin.castSucc_lt_castSucc_iff.mpr hij)

/-- Initial `(r + 1)`-tuple `shiftInit u : ShiftTuple r α` obtained by dropping the last coordinate. -/
def shiftInit {r : ℕ} {α : Type u} [Preorder α]
    (u : ShiftTuple (r + 1) α) : ShiftTuple r α :=
  ⟨shiftTupleInit u, shiftTupleInit_strictMono u⟩

/-- Underlying map of the terminal `(r + 1)`-window of an `(r + 2)`-tuple `u : ShiftTuple (r + 1) α`. -/
def shiftTupleTail {r : ℕ} {α : Type u} [Preorder α]
    (u : ShiftTuple (r + 1) α) : Fin (r + 1) → α :=
  fun i => u.1 i.succ

/-- The terminal `(r + 1)`-window of any strictly increasing `(r + 2)`-tuple is strictly monotone. -/
theorem shiftTupleTail_strictMono {r : ℕ} {α : Type u} [Preorder α]
    (u : ShiftTuple (r + 1) α) : StrictMono (shiftTupleTail u) := by
  intro i j hij
  exact u.2 (Fin.succ_lt_succ_iff.mpr hij)

/-- Terminal `(r + 1)`-tuple `shiftTail u : ShiftTuple r α` obtained by dropping the first coordinate. -/
def shiftTail {r : ℕ} {α : Type u} [Preorder α]
    (u : ShiftTuple (r + 1) α) : ShiftTuple r α :=
  ⟨shiftTupleTail u, shiftTupleTail_strictMono u⟩

/-- Directed shift step on `(r + 1)`-tuples: `u 0 < v 0` and `u (i + 1) = v i` for all `i : Fin r`. -/
def ShiftStep (r : ℕ) {α : Type u} [Preorder α]
    (u v : ShiftTuple r α) : Prop :=
  u.1 0 < v.1 0 ∧ ∀ i : Fin r, u.1 i.succ = v.1 i.castSucc

/-- Every `(r + 2)`-tuple `u : ShiftTuple (r + 1) α` witnesses a forward shift step from
`shiftInit u` to `shiftTail u`. -/
theorem shiftInit_step_shiftTail {r : ℕ} {α : Type u} [Preorder α]
    (u : ShiftTuple (r + 1) α) :
    ShiftStep r (shiftInit u) (shiftTail u) := by
  refine ⟨u.2 (Fin.zero_lt_one), fun i => ?_⟩
  change u.1 i.succ.castSucc = u.1 i.castSucc.succ
  rw [Fin.succ_castSucc]

/-- The universal `(r + 1)`-tuple shift graph `ShiftGraph r α` on `ShiftTuple r α`. -/
def ShiftGraph (r : ℕ) (α : Type u) [Preorder α] : SimpleGraph (ShiftTuple r α) where
  Adj u v := ShiftStep r u v ∨ ShiftStep r v u
  symm := by
    constructor
    intro u v h
    exact h.symm
  loopless := by
    constructor
    intro u h
    rcases h with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> exact lt_irrefl _ hlt

/-- Forward shift steps produce edges in `ShiftGraph r α`. -/
theorem shiftGraph_adj_step {r : ℕ} {α : Type u} [Preorder α]
    {u v : ShiftTuple r α} (h : ShiftStep r u v) :
    (ShiftGraph r α).Adj u v :=
  Or.inl h

/-- At order `r + 1`, a forward shift step `ShiftStep (r + 1) u v` is equivalent to the window
matching condition `shiftTail u = shiftInit v`. -/
theorem shiftStep_succ_iff_tail_eq_init {r : ℕ} {α : Type u} [Preorder α]
    (u v : ShiftTuple (r + 1) α) :
    ShiftStep (r + 1) u v ↔ shiftTail u = shiftInit v := by
  constructor
  · intro h
    ext i
    exact h.2 i
  · intro h
    have hcoord : ∀ i : Fin (r + 1), u.1 i.succ = v.1 i.castSucc :=
      fun i => congrFun (congrArg Subtype.val h) i
    refine ⟨?_, hcoord⟩
    have h01 : u.1 0 < u.1 1 := u.2 (Fin.zero_lt_one)
    have heq0 : u.1 (0 : Fin (r + 1)).succ = v.1 (0 : Fin (r + 1)).castSucc := hcoord 0
    simpa using h01.trans_eq heq0

/-- Prepending `a < w.1 0` to `w : ShiftTuple r α` via `Fin.cons` preserves strict monotonicity. -/
theorem shiftTupleCons_strictMono {r : ℕ} {α : Type u} [Preorder α]
    (a : α) (w : ShiftTuple r α) (ha : a < w.1 0) :
    StrictMono (Fin.cons a w.1) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · intro j
    refine Fin.cases (fun h => (lt_irrefl _ h).elim) (fun j0 _ => ?_) j
    simp only [Fin.cons_zero, Fin.cons_succ]
    rcases eq_or_lt_of_le (Fin.zero_le j0) with rfl | hpos
    · exact ha
    · exact ha.trans (w.2 hpos)
  · intro i0 j
    refine Fin.cases (fun h => (not_lt_of_ge (Fin.zero_le _) h).elim) (fun j0 hij => ?_) j
    simp only [Fin.cons_succ]
    exact w.2 (Fin.succ_lt_succ_iff.mp hij)

/-- Prepending constructor `shiftTupleCons a w ha : ShiftTuple (r + 1) α`. -/
def shiftTupleCons {r : ℕ} {α : Type u} [Preorder α]
    (a : α) (w : ShiftTuple r α) (ha : a < w.1 0) : ShiftTuple (r + 1) α :=
  ⟨Fin.cons a w.1, shiftTupleCons_strictMono a w ha⟩

/-- The terminal window `shiftTail` of `shiftTupleCons a w ha` recovers `w`. -/
theorem shiftTail_cons {r : ℕ} {α : Type u} [Preorder α]
    (a : α) (w : ShiftTuple r α) (ha : a < w.1 0) :
    shiftTail (shiftTupleCons a w ha) = w := by
  ext i
  simp [shiftTail, shiftTupleTail, shiftTupleCons]

/-- Whenever `ShiftStep r v w` holds, prepending `v.1 0` to `w` produces an `(r + 2)`-tuple whose
initial window `shiftInit` equals `v`. -/
theorem shiftInit_cons_of_step {r : ℕ} {α : Type u} [Preorder α]
    {v w : ShiftTuple r α} (hstep : ShiftStep r v w) :
    shiftInit (shiftTupleCons (v.1 0) w hstep.1) = v := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [shiftInit, shiftTupleInit, shiftTupleCons]
  · intro j
    have h1 : (shiftInit (shiftTupleCons (v.1 0) w hstep.1)).1 j.succ = w.1 j.castSucc := by
      change @Fin.cons (r + 1) (fun _ => α) (v.1 0) w.1 j.succ.castSucc = w.1 j.castSucc
      rw [← Fin.succ_castSucc, Fin.cons_succ]
    exact h1.trans (hstep.2 j).symm

/-- Predecessor color-profile map induced on `ShiftTuple r α` by a proper coloring `c` of
`ShiftGraph (r + 1) α`. -/
def higherShiftProfile {r : ℕ} {α : Type u} [Preorder α] {C : Type v}
    (c : (ShiftGraph (r + 1) α).Coloring C) (w : ShiftTuple r α) : Set C :=
  {k : C | ∃ u : ShiftTuple (r + 1) α, shiftTail u = w ∧ c u = k}

/-- Every prepended tuple `shiftTupleCons a w ha` contributes its color to `higherShiftProfile c w`. -/
theorem mem_higherShiftProfile_cons {r : ℕ} {α : Type u} [Preorder α] {C : Type v}
    (c : (ShiftGraph (r + 1) α).Coloring C) (a : α) (w : ShiftTuple r α) (ha : a < w.1 0) :
    c (shiftTupleCons a w ha) ∈ higherShiftProfile c w :=
  ⟨shiftTupleCons a w ha, shiftTail_cons a w ha, rfl⟩

/-- For any step `ShiftStep r v w`, the glued tuple color `c (shiftTupleCons (v.1 0) w hstep.1)`
is forbidden from `higherShiftProfile c v`. -/
theorem not_mem_higherShiftProfile_of_step {r : ℕ} {α : Type u} [Preorder α] {C : Type v}
    (c : (ShiftGraph (r + 1) α).Coloring C) {v w : ShiftTuple r α}
    (hstep : ShiftStep r v w) :
    c (shiftTupleCons (v.1 0) w hstep.1) ∉ higherShiftProfile c v := by
  rintro ⟨u, htail, heq⟩
  have hstep_succ : ShiftStep (r + 1) u (shiftTupleCons (v.1 0) w hstep.1) := by
    rw [shiftStep_succ_iff_tail_eq_init]
    exact htail.trans (shiftInit_cons_of_step hstep).symm
  exact c.valid (shiftGraph_adj_step hstep_succ) heq

/-- Every forward step `ShiftStep r v w` forces `higherShiftProfile c v ≠ higherShiftProfile c w`. -/
theorem higherShiftProfile_ne_of_step {r : ℕ} {α : Type u} [Preorder α] {C : Type v}
    (c : (ShiftGraph (r + 1) α).Coloring C) {v w : ShiftTuple r α}
    (hstep : ShiftStep r v w) :
    higherShiftProfile c v ≠ higherShiftProfile c w := by
  intro heq
  have hmem : c (shiftTupleCons (v.1 0) w hstep.1) ∈ higherShiftProfile c v := by
    rw [heq]
    exact mem_higherShiftProfile_cons c (v.1 0) w hstep.1
  exact not_mem_higherShiftProfile_of_step c hstep hmem

/-- Proper `Set C`-coloring of `ShiftGraph r α` induced by any `C`-coloring of `ShiftGraph (r + 1) α`. -/
def higherShiftProfileColoring {r : ℕ} {α : Type u} [Preorder α] {C : Type v}
    (c : (ShiftGraph (r + 1) α).Coloring C) :
    (ShiftGraph r α).Coloring (Set C) :=
  Coloring.mk (higherShiftProfile c) (by
    intro v w hadj heq
    rcases hadj with hvw | hwv
    · exact higherShiftProfile_ne_of_step c hvw heq
    · exact higherShiftProfile_ne_of_step c hwv heq.symm)

/-- Universal higher-order step-coloring lower-bound reduction: for every `r : ℕ` and preorder `α`,
`(ShiftGraph r α).chromaticCardinal ≤ 2 ^ (ShiftGraph (r + 1) α).chromaticCardinal`. -/
theorem chromatic_shiftGraph_le_two_pow_succ (r : ℕ) (α : Type u) [Preorder α] :
    (ShiftGraph r α).chromaticCardinal ≤
      (2 : Cardinal.{u}) ^ (ShiftGraph (r + 1) α).chromaticCardinal := by
  obtain ⟨C, hC, ⟨c⟩⟩ := exists_minimal_palette (ShiftGraph (r + 1) α)
  have hcol := chromatic_le_of_coloring (higherShiftProfileColoring c)
  simpa only [Cardinal.mk_set, hC] using hcol

/-- Distinguishing coordinate between `e (c (shiftInit u))` and `e (c (shiftTail u))` for an
injective binary encoding `e : K → (C → Bool)`. -/
def higherShiftDiffCoord {r : ℕ} {α : Type u} [Preorder α] {K C : Type v}
    (c : (ShiftGraph r α).Coloring K)
    {e : K → (C → Bool)} (he : Function.Injective e)
    (u : ShiftTuple (r + 1) α) : C :=
  Classical.choose (Function.ne_iff.mp (he.ne (c.valid (shiftGraph_adj_step (shiftInit_step_shiftTail u)))))

/-- The distinguishing coordinate `higherShiftDiffCoord c he u` separates the binary encodings
of `c (shiftInit u)` and `c (shiftTail u)`. -/
theorem higherShiftDiffCoord_spec {r : ℕ} {α : Type u} [Preorder α] {K C : Type v}
    (c : (ShiftGraph r α).Coloring K)
    {e : K → (C → Bool)} (he : Function.Injective e)
    (u : ShiftTuple (r + 1) α) :
    e (c (shiftInit u)) (higherShiftDiffCoord c he u) ≠
      e (c (shiftTail u)) (higherShiftDiffCoord c he u) :=
  Classical.choose_spec (Function.ne_iff.mp (he.ne (c.valid (shiftGraph_adj_step (shiftInit_step_shiftTail u)))))

/-- Universal binary-difference step lifting coloring of `ShiftGraph (r + 1) α` with palette
`C × Bool` from any `K`-coloring of `ShiftGraph r α` and injection `e : K → (C → Bool)`. -/
def higherShiftBinaryDiffColoring {r : ℕ} {α : Type u} [Preorder α] {K C : Type v}
    (c : (ShiftGraph r α).Coloring K)
    {e : K → (C → Bool)} (he : Function.Injective e) :
    (ShiftGraph (r + 1) α).Coloring (C × Bool) :=
  Coloring.mk
    (fun u => (higherShiftDiffCoord c he u, e (c (shiftInit u)) (higherShiftDiffCoord c he u)))
    (by
      intro u v hadj heq
      obtain ⟨hk, hb⟩ := Prod.mk.inj heq
      rcases hadj with huv | hvu
      · have hti : shiftTail u = shiftInit v := (shiftStep_succ_iff_tail_eq_init u v).mp huv
        apply higherShiftDiffCoord_spec c he u
        calc
          e (c (shiftInit u)) (higherShiftDiffCoord c he u) =
              e (c (shiftInit v)) (higherShiftDiffCoord c he v) := hb
          _ = e (c (shiftTail u)) (higherShiftDiffCoord c he u) := by rw [← hti, ← hk]
      · have hti : shiftTail v = shiftInit u := (shiftStep_succ_iff_tail_eq_init v u).mp hvu
        apply higherShiftDiffCoord_spec c he v
        calc
          e (c (shiftInit v)) (higherShiftDiffCoord c he v) =
              e (c (shiftInit u)) (higherShiftDiffCoord c he u) := hb.symm
          _ = e (c (shiftTail v)) (higherShiftDiffCoord c he v) := by rw [← hti, hk])

/-- Universal higher-order step upper bound: for any `r : ℕ`, preorder `α`, and infinite cardinal
`μ` (`ℵ₀ ≤ μ`), if `(ShiftGraph r α).chromaticCardinal ≤ 2 ^ μ`, then
`(ShiftGraph (r + 1) α).chromaticCardinal ≤ μ`. -/
theorem chromatic_shiftGraph_succ_le_of_le_two_pow
    (r : ℕ) (α : Type u) [Preorder α] {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hr : (ShiftGraph r α).chromaticCardinal ≤ (2 : Cardinal.{u}) ^ μ) :
    (ShiftGraph (r + 1) α).chromaticCardinal ≤ μ := by
  let C := μ.out
  have hpow : #(C → Bool) = (2 : Cardinal.{u}) ^ μ := by simp [C]
  obtain ⟨K, hK, ⟨c⟩⟩ := exists_minimal_palette (ShiftGraph r α)
  obtain ⟨e⟩ := (Cardinal.le_def K (C → Bool)).mp ((hK.trans_le hr).trans_eq hpow.symm)
  have hcol := chromatic_le_of_coloring (higherShiftBinaryDiffColoring c e.injective)
  have hpal : #(C × Bool) = μ := by
    calc
      #(C × Bool) = #C * 2 := by simp
      _ = μ * 2 := by simp [C]
      _ = μ + μ := mul_two μ
      _ = μ := Cardinal.add_eq_self hμ
  exact hcol.trans_eq hpal

/-- Exact higher-order step chromatic biconditional: for every `r : ℕ`, preorder `α`, and infinite
cardinal `μ` (`ℵ₀ ≤ μ`), `(ShiftGraph (r + 1) α).chromaticCardinal ≤ μ ↔
(ShiftGraph r α).chromaticCardinal ≤ 2 ^ μ`. -/
theorem chromatic_shiftGraph_succ_le_iff
    (r : ℕ) (α : Type u) [Preorder α] {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    (ShiftGraph (r + 1) α).chromaticCardinal ≤ μ ↔
      (ShiftGraph r α).chromaticCardinal ≤ (2 : Cardinal.{u}) ^ μ := by
  constructor
  · intro hle
    exact (chromatic_shiftGraph_le_two_pow_succ r α).trans
      (Cardinal.power_le_power_left (by norm_num) hle)
  · exact chromatic_shiftGraph_succ_le_of_le_two_pow r α hμ

/-- Homomorphism from `ShiftGraph 0 α` to `completeGraph α` via evaluation at coordinate `0`. -/
def shiftZeroToComplete (α : Type u) [Preorder α] :
    ShiftGraph 0 α →g completeGraph α :=
  ⟨fun u => u.1 0, by
    intro u v hadj
    rcases hadj with ⟨hlt, _⟩ | ⟨hlt, _⟩
    · exact ne_of_lt hlt
    · exact ne_of_gt hlt⟩

/-- Homomorphism from `completeGraph α` to `ShiftGraph 0 α` over any linear order `α`. -/
def completeToShiftZero (α : Type u) [LinearOrder α] :
    completeGraph α →g ShiftGraph 0 α :=
  ⟨fun a => ⟨fun _ => a, fun i j hij => (lt_irrefl _ ((Fin.eq_zero i).trans (Fin.eq_zero j).symm ▸ hij)).elim⟩, by
    intro a b hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact Or.inl ⟨hlt, fun i => Fin.elim0 i⟩
    · exact Or.inr ⟨hgt, fun i => Fin.elim0 i⟩⟩

/-- Over any linear order `α`, the 1-tuple shift graph `ShiftGraph 0 α` has chromatic cardinal `#α`. -/
theorem chromatic_shiftGraph_zero_eq_mk (α : Type u) [LinearOrder α] :
    (ShiftGraph 0 α).chromaticCardinal = #α := by
  apply le_antisymm
  · exact (chromatic_mono_hom (shiftZeroToComplete α)).trans_eq (chromatic_complete α)
  · exact (chromatic_complete α).symm.trans_le (chromatic_mono_hom (completeToShiftZero α))

/-- Iterated powerset (beth-step) tower `iteratedTwoPow r μ = B_r(μ)`, with `B_0(μ) = μ`
and `B_{r+1}(μ) = 2 ^ B_r(μ)`. -/
def iteratedTwoPow : ℕ → Cardinal.{u} → Cardinal.{u}
  | 0, μ => μ
  | r + 1, μ => (2 : Cardinal.{u}) ^ iteratedTwoPow r μ

/-- Shift identity for the iterated powerset tower: `iteratedTwoPow r (2 ^ μ) = iteratedTwoPow (r + 1) μ`. -/
theorem iteratedTwoPow_two_pow (r : ℕ) (μ : Cardinal.{u}) :
    iteratedTwoPow r ((2 : Cardinal.{u}) ^ μ) = iteratedTwoPow (r + 1) μ := by
  induction r with
  | zero => simp [iteratedTwoPow]
  | succ r ih => simp [iteratedTwoPow, ih]

/-- Exact Erdős–Hajnal (1968) Theorem 1 threshold for all finite shift-graph orders `r : ℕ`:
for every linear order `α` and infinite cardinal `μ` (`ℵ₀ ≤ μ`),
`(ShiftGraph r α).chromaticCardinal ≤ μ ↔ #α ≤ iteratedTwoPow r μ`. -/
theorem chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow
    (r : ℕ) (α : Type u) [LinearOrder α] {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    (ShiftGraph r α).chromaticCardinal ≤ μ ↔ #α ≤ iteratedTwoPow r μ := by
  induction r generalizing μ with
  | zero =>
    simp [iteratedTwoPow, chromatic_shiftGraph_zero_eq_mk]
  | succ r ih =>
    have hμ2 : ℵ₀ ≤ (2 : Cardinal.{u}) ^ μ := hμ.trans (Cardinal.cantor μ).le
    rw [chromatic_shiftGraph_succ_le_iff r α hμ, ih hμ2, iteratedTwoPow_two_pow]

/-! ## GCH Specialization and Erdős–Hajnal (1968), Corollary 1 -/

/-- Under GCH (`∀ c ≥ ℵ₀, 2 ^ c = Order.succ c`), `iteratedTwoPow r (ℵ_ m) = ℵ_ (m + r)`. -/
theorem iteratedTwoPow_aleph_nat_of_gch
    (hGCH : ∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c)
    (m : ℕ) :
    ∀ r : ℕ, iteratedTwoPow r (ℵ_ (m : Ordinal.{u})) =
      ℵ_ ((m + r : ℕ) : Ordinal.{u})
  | 0 => by simp [iteratedTwoPow]
  | r + 1 => by
    have ih := iteratedTwoPow_aleph_nat_of_gch hGCH m r
    have hinf : ℵ₀ ≤ ℵ_ ((m + r : ℕ) : Ordinal.{u}) := Cardinal.aleph0_le_aleph _
    calc iteratedTwoPow (r + 1) (ℵ_ (m : Ordinal.{u}))
        = (2 : Cardinal.{u}) ^ iteratedTwoPow r (ℵ_ (m : Ordinal.{u})) := rfl
      _ = (2 : Cardinal.{u}) ^ (ℵ_ ((m + r : ℕ) : Ordinal.{u})) := by rw [ih]
      _ = Order.succ (ℵ_ ((m + r : ℕ) : Ordinal.{u})) := hGCH _ hinf
      _ = ℵ_ (((m + r : ℕ) : Ordinal.{u}) + 1) := Cardinal.succ_aleph _
      _ = ℵ_ ((m + (r + 1) : ℕ) : Ordinal.{u}) := by simp [add_assoc]

/-- Under GCH, `ShiftGraph r α` on a linear order `α` of size `ℵ_ (r + 1)` has chromatic cardinal `ℵ₁`. -/
theorem chromatic_shiftGraph_eq_aleph1_of_gch
    (hGCH : ∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c)
    (r : ℕ) (α : Type u) [LinearOrder α] (hα : #α = ℵ_ ((r + 1 : ℕ) : Ordinal.{u})) :
    (ShiftGraph r α).chromaticCardinal = ℵ₁ := by
  have hle : (ShiftGraph r α).chromaticCardinal ≤ ℵ₁ := by
    rw [chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow r α (Cardinal.aleph0_le_aleph 1)]
    have h1 : (ℵ₁ : Cardinal.{u}) = ℵ_ ((1 : ℕ) : Ordinal.{u}) := by simp
    rw [h1, iteratedTwoPow_aleph_nat_of_gch hGCH 1 r, hα]
    apply Cardinal.aleph_le_aleph.mpr
    exact_mod_cast Nat.le_of_eq (Nat.add_comm r 1)
  have hnot_le0 : ¬ ((ShiftGraph r α).chromaticCardinal ≤ ℵ₀) := by
    rw [chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow r α le_rfl]
    have h0 : (ℵ₀ : Cardinal.{u}) = ℵ_ ((0 : ℕ) : Ordinal.{u}) := by simp
    rw [h0, iteratedTwoPow_aleph_nat_of_gch hGCH 0 r, hα]
    apply not_le_of_gt
    apply Cardinal.aleph_lt_aleph.mpr
    exact_mod_cast (show 0 + r < r + 1 by omega)
  have hgt0 : ℵ₀ < (ShiftGraph r α).chromaticCardinal := not_le.mp hnot_le0
  have hsucc : Order.succ (ℵ₀ : Cardinal.{u}) = ℵ₁ := by
    simpa [Cardinal.aleph_zero] using (Cardinal.succ_aleph (0 : Ordinal.{u}))
  have hge : ℵ₁ ≤ (ShiftGraph r α).chromaticCardinal := by
    rw [← hsucc, Order.succ_le_iff]
    exact hgt0
  exact le_antisymm hle hge

/-- Coordinate support of a tuple subset `W : Set (ShiftTuple r α)`. -/
def tupleCoordSupport {r : ℕ} {α : Type u} [Preorder α]
    (W : Set (ShiftTuple r α)) : Set α :=
  ⋃ i : ULift.{u} (Fin (r + 1)), (fun u : ShiftTuple r α => u.1 i.down) '' W

/-- Every coordinate of `u ∈ W` lies in `tupleCoordSupport W`. -/
theorem mem_tupleCoordSupport {r : ℕ} {α : Type u} [Preorder α]
    {W : Set (ShiftTuple r α)} {u : ShiftTuple r α} (hu : u ∈ W) (i : Fin (r + 1)) :
    u.1 i ∈ tupleCoordSupport W :=
  Set.mem_iUnion.mpr ⟨⟨i⟩, u, hu, rfl⟩

/-- Canonical graph homomorphism `(ShiftGraph r α).induce W →g ShiftGraph r (tupleCoordSupport W)`. -/
def induceShiftGraphToCoordSupport {r : ℕ} {α : Type u} [Preorder α]
    (W : Set (ShiftTuple r α)) :
    (ShiftGraph r α).induce W →g ShiftGraph r (tupleCoordSupport W) :=
  ⟨fun u => ⟨fun i => ⟨u.1.1 i, mem_tupleCoordSupport u.2 i⟩, fun i j hij => u.1.2 hij⟩, by
    intro u v hadj
    rcases hadj with ⟨hlt, hstep⟩ | ⟨hlt, hstep⟩
    · exact Or.inl ⟨hlt, fun i => Subtype.ext (hstep i)⟩
    · exact Or.inr ⟨hlt, fun i => Subtype.ext (hstep i)⟩⟩

/-- Cardinality bound `#(tupleCoordSupport W) ≤ κ` for infinite `κ` when `#W ≤ κ`. -/
theorem card_tupleCoordSupport_le_of_infinite {r : ℕ} {α : Type u} [Preorder α]
    {W : Set (ShiftTuple r α)} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hW : #W ≤ κ) :
    #(tupleCoordSupport W) ≤ κ := by
  let f : ULift.{u} (Fin (r + 1)) → Set α :=
    fun i => (fun u : ShiftTuple r α => u.1 i.down) '' W
  have h1 : #(tupleCoordSupport W) ≤ #(ULift.{u} (Fin (r + 1))) * ⨆ i, #(f i) :=
    Cardinal.mk_iUnion_le f
  have hfin : #(ULift.{u} (Fin (r + 1))) ≤ κ := by
    have hcard : #(ULift.{u} (Fin (r + 1))) = ((r + 1 : ℕ) : Cardinal.{u}) := by
      simp [Cardinal.mk_uLift, Cardinal.mk_fin]
    rw [hcard]
    exact (Cardinal.natCast_lt_aleph0 (n := r + 1)).le.trans hκ
  have hsup : (⨆ i, #(f i)) ≤ κ := by
    refine ciSup_le' (fun i => ?_)
    exact Cardinal.mk_image_le.trans hW
  calc #(tupleCoordSupport W) ≤ #(ULift.{u} (Fin (r + 1))) * ⨆ i, #(f i) := h1
    _ ≤ κ * κ := mul_le_mul' hfin hsup
    _ = κ := Cardinal.mul_eq_self hκ

/-- Upper bound `#(ShiftTuple r α) ≤ κ` for infinite `κ` when `#α ≤ κ`. -/
theorem card_shiftTuple_le_of_infinite (r : ℕ) (α : Type u) [Preorder α]
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hα : #α ≤ κ) :
    #(ShiftTuple r α) ≤ κ := by
  have hinj : Function.Injective (Subtype.val : ShiftTuple r α → (Fin (r + 1) → α)) :=
    Subtype.val_injective
  have hle : #(ShiftTuple r α) ≤ #(Fin (r + 1) → α) :=
    Cardinal.mk_le_of_injective hinj
  have hfun : #(Fin (r + 1) → α) = (#α) ^ ((r + 1 : ℕ) : Cardinal.{u}) := by
    simp [Cardinal.mk_arrow, Cardinal.mk_fin]
  have hpow : (#α) ^ ((r + 1 : ℕ) : Cardinal.{u}) ≤ κ ^ ((r + 1 : ℕ) : Cardinal.{u}) :=
    Cardinal.power_le_power_right hα
  have hκpow : κ ^ ((r + 1 : ℕ) : Cardinal.{u}) = κ :=
    Cardinal.power_nat_eq hκ (Nat.succ_pos r)
  exact hle.trans (hfun.le.trans (hpow.trans_eq hκpow))

/-- Under GCH, every induced subgraph of `ShiftGraph r α` on `< ℵ_ (r + 1)` vertices has chromatic
cardinal `≤ ℵ₀`. -/
theorem chromatic_induce_shiftGraph_le_aleph0_of_card_lt_of_gch
    (hGCH : ∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c)
    (r : ℕ) (α : Type u) [LinearOrder α]
    {W : Set (ShiftTuple r α)} (hW : #W < ℵ_ ((r + 1 : ℕ) : Ordinal.{u})) :
    ((ShiftGraph r α).induce W).chromaticCardinal ≤ ℵ₀ := by
  have hsucc : Order.succ (ℵ_ (r : Ordinal.{u})) = ℵ_ ((r + 1 : ℕ) : Ordinal.{u}) := by
    simpa using (Cardinal.succ_aleph (r : Ordinal.{u}))
  have hWle : #W ≤ ℵ_ (r : Ordinal.{u}) := by
    rw [← hsucc, Order.lt_succ_iff] at hW
    exact hW
  have hcoord : #(tupleCoordSupport W) ≤ iteratedTwoPow r ℵ₀ := by
    have h0 : (ℵ₀ : Cardinal.{u}) = ℵ_ ((0 : ℕ) : Ordinal.{u}) := by simp
    rw [h0, iteratedTwoPow_aleph_nat_of_gch hGCH 0 r]
    simpa using card_tupleCoordSupport_le_of_infinite (Cardinal.aleph0_le_aleph (r : Ordinal.{u})) hWle
  have hsub : (ShiftGraph r (tupleCoordSupport W)).chromaticCardinal ≤ ℵ₀ :=
    (chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow r (tupleCoordSupport W) le_rfl).mpr hcoord
  exact (chromatic_mono_hom (induceShiftGraphToCoordSupport W)).trans hsub

/-- Erdős–Hajnal (1968), Corollary 1: under GCH, for every finite `k > 0` there is a graph on
`ℵ_ k` vertices with chromatic cardinal `ℵ₁` whose induced subgraphs on fewer than `ℵ_ k`
vertices have chromatic cardinal at most `ℵ₀`. -/
theorem erdos_hajnal_of_gch (hGCH : ∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c)
    (k : ℕ) (hk : 0 < k) : ∃ (V : Type u) (G : SimpleGraph V),
    #V = ℵ_ k ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W < ℵ_ k), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let α : Type u := (ℵ_ ((r + 1 : ℕ) : Ordinal.{u})).out
  letI : LinearOrder α := WellOrderingRel.isWellOrder.linearOrder
  have hα : #α = ℵ_ ((r + 1 : ℕ) : Ordinal.{u}) := Cardinal.mk_out _
  have hchi : (ShiftGraph r α).chromaticCardinal = ℵ₁ :=
    chromatic_shiftGraph_eq_aleph1_of_gch hGCH r α hα
  have hlocal : ∀ (W : Set (ShiftTuple r α)),
      #W < ℵ_ ((r + 1 : ℕ) : Ordinal.{u}) → ((ShiftGraph r α).induce W).chromaticCardinal ≤ ℵ₀ :=
    fun W hW => chromatic_induce_shiftGraph_le_aleph0_of_card_lt_of_gch hGCH r α hW
  have hV_le : #(ShiftTuple r α) ≤ ℵ_ ((r + 1 : ℕ) : Ordinal.{u}) :=
    card_shiftTuple_le_of_infinite r α (Cardinal.aleph0_le_aleph _) hα.le
  have hV_ge : ℵ_ ((r + 1 : ℕ) : Ordinal.{u}) ≤ #(ShiftTuple r α) := by
    by_contra hlt
    rw [not_le] at hlt
    have huniv : #(Set.univ : Set (ShiftTuple r α)) < ℵ_ ((r + 1 : ℕ) : Ordinal.{u}) := by
      simpa [Cardinal.mk_univ] using hlt
    have hle0 : ((ShiftGraph r α).induce Set.univ).chromaticCardinal ≤ ℵ₀ := hlocal Set.univ huniv
    have piso : ShiftGraph r α →g (ShiftGraph r α).induce Set.univ :=
      ⟨fun u => ⟨u, trivial⟩, fun {_ _} h => h⟩
    have hchi_le0 : (ShiftGraph r α).chromaticCardinal ≤ ℵ₀ :=
      (chromatic_mono_hom piso).trans hle0
    rw [hchi] at hchi_le0
    exact (Cardinal.aleph0_lt_aleph_one).not_ge hchi_le0
  refine ⟨ShiftTuple r α, ShiftGraph r α, le_antisymm hV_le hV_ge, hchi, hlocal⟩

end Erdos918HigherShift
