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

public import PigeonholeAndEqualityRefutations918

@[expose] public section

universe u

open SimpleGraph
open scoped Cardinal Ordinal

namespace Erdos918

abbrev ShiftTuple (r : ℕ) (α : Type u) [Preorder α] : Type u :=
  {x : Fin (r + 1) → α // StrictMono x}

def ShiftStep (r : ℕ) {α : Type u} [Preorder α]
    (u v : ShiftTuple r α) : Prop :=
  u.1 0 < v.1 0 ∧ ∀ i : Fin r, u.1 i.succ = v.1 i.castSucc

def ShiftGraph (r : ℕ) (α : Type u) [Preorder α] : SimpleGraph (ShiftTuple r α) where
  Adj u v := ShiftStep r u v ∨ ShiftStep r v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> exact lt_irrefl _ hlt⟩

def iteratedTwoPow (r : ℕ) (μ : Cardinal.{u}) : Cardinal.{u} :=
  Nat.rec μ (fun _ c => (2 : Cardinal.{u}) ^ c) r

private theorem iteratedTwoPow_eq (r : ℕ) (μ : Cardinal.{u}) :
    iteratedTwoPow r μ = Erdos918HigherShift.iteratedTwoPow r μ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (2 : Cardinal.{u}) ^ iteratedTwoPow r μ = (2 : Cardinal.{u}) ^ Erdos918HigherShift.iteratedTwoPow r μ
    rw [ih]

namespace variants

theorem erdos_hajnal (hGCH : ∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c)
    (k : ℕ) (hk : 0 < k) : ∃ (V : Type u) (G : SimpleGraph V),
    #V = ℵ_ k ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W < ℵ_ k), (G.induce W).chromaticCardinal ≤ ℵ₀ :=
  Erdos918HigherShift.erdos_hajnal_of_gch hGCH k hk

theorem eq_aleph_0.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal = ℵ₀ :=
  Erdos918PigeonholeWalk.not_exists_induced_eq_aleph0_parts_i

theorem eq_aleph_0_all_subgraphs.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal = ℵ₀ :=
  Erdos918PigeonholeWalk.not_exists_all_subgraphs_eq_aleph0_parts_i

theorem eq_aleph_0.parts.ii :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal = ℵ₀ :=
  Erdos918PigeonholeWalk.not_exists_induced_eq_aleph0_parts_ii_of_one_le
    (le_of_lt Ordinal.one_lt_omega0)

theorem eq_aleph_0_all_subgraphs.parts.ii :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal = ℵ₀ :=
  Erdos918PigeonholeWalk.not_exists_all_subgraphs_eq_aleph0_parts_ii ω

theorem induced_eq_aleph0_parts_ii_negation_iff_one_le (ω₀ : Ordinal.{u}) :
    (¬ ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ (ω₀ + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω₀), (G.induce W).chromaticCardinal = ℵ₀) ↔
      (1 : Ordinal.{u}) ≤ ω₀ :=
  Erdos918PigeonholeWalk.induced_eq_aleph0_parts_ii_negation_iff_one_le ω₀

theorem chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow
    (r : ℕ) (α : Type u) [LinearOrder α] {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    (ShiftGraph r α).chromaticCardinal ≤ μ ↔ #α ≤ iteratedTwoPow r μ := by
  rw [iteratedTwoPow_eq]
  exact Erdos918HigherShift.chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow r α hμ

end variants
end Erdos918
