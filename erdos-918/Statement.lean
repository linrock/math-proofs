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

universe u

open SimpleGraph
open scoped Cardinal Ordinal

namespace Erdos918

noncomputable def chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

def statement_erdos_hajnal : Prop :=
  ∀ (hGCH : ∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c) (k : ℕ), 0 < k →
    ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ k ∧ chromaticCardinal G = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W < ℵ_ k), chromaticCardinal (G.induce W) ≤ ℵ₀

def statement_eq_aleph_0_parts_i : Prop :=
  ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ chromaticCardinal G = ℵ_ 2 ∧
    ∀ (W : Set V) (_ : #W = ℵ₁), chromaticCardinal (G.induce W) = ℵ₀

def statement_eq_aleph_0_all_subgraphs_parts_i : Prop :=
  ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ chromaticCardinal G = ℵ_ 2 ∧
    ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), chromaticCardinal H.coe = ℵ₀

def statement_eq_aleph_0_parts_ii : Prop :=
  ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ chromaticCardinal G = ℵ₁ ∧
    ∀ (W : Set V) (_ : #W = ℵ_ ω), chromaticCardinal (G.induce W) = ℵ₀

def statement_eq_aleph_0_all_subgraphs_parts_ii : Prop :=
  ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ chromaticCardinal G = ℵ₁ ∧
    ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), chromaticCardinal H.coe = ℵ₀

end Erdos918
