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

Adaptation notice: `chromaticCardinal` and the Erdős–Hajnal and `eq_aleph_0` statement
signatures are adapted from google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/918.lean` and
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`).
The higher-order shift-graph characterization, the color-class pigeonhole
independent-set theorem, and the ordinal dichotomy are new for this standalone
Lean 4 benchmark. This file imports only Mathlib.
-/

public import Mathlib

@[expose] public section

universe u

open SimpleGraph
open scoped Cardinal Ordinal

namespace SimpleGraph

/-- Cardinal chromatic number of a simple graph $G$: the least cardinal $\kappa$ of a proper vertex-colouring palette $C$. -/
noncomputable def chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

end SimpleGraph

namespace Erdos918

/-- Strictly increasing $(r+1)$-tuples in a preorder $\alpha$. -/
abbrev ShiftTuple (r : ℕ) (α : Type u) [Preorder α] : Type u :=
  {x : Fin (r + 1) → α // StrictMono x}

/-- Directed shift-step relation on $(r+1)$-tuples. -/
def ShiftStep (r : ℕ) {α : Type u} [Preorder α]
    (u v : ShiftTuple r α) : Prop :=
  u.1 0 < v.1 0 ∧ ∀ i : Fin r, u.1 i.succ = v.1 i.castSucc

/-- The order-$r$ Erdős–Hajnal shift graph on strictly increasing $(r+1)$-tuples in $\alpha$. -/
def ShiftGraph (r : ℕ) (α : Type u) [Preorder α] : SimpleGraph (ShiftTuple r α) where
  Adj u v := ShiftStep r u v ∨ ShiftStep r v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> exact lt_irrefl _ hlt⟩

/-- Iterated base-2 cardinal exponentiation $\exp_2^{(r)}(\mu)$. -/
def iteratedTwoPow (r : ℕ) (μ : Cardinal.{u}) : Cardinal.{u} :=
  Nat.rec μ (fun _ c => (2 : Cardinal.{u}) ^ c) r

namespace variants

/-- Erdős and Hajnal [ErHa68b, Corollary 1]: assuming GCH, for every finite $k > 0$ there is a
graph on $\aleph_k$ vertices with chromatic cardinal $\aleph_1$ whose induced subgraphs on fewer
than $\aleph_k$ vertices have chromatic cardinal at most $\aleph_0$. -/
theorem erdos_hajnal (hGCH : ∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c)
    (k : ℕ) (hk : 0 < k) : ∃ (V : Type u) (G : SimpleGraph V),
    #V = ℵ_ k ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W < ℵ_ k), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- Refutation of `erdos_918.variants.eq_aleph_0.parts.i`: no graph on $\aleph_2$ vertices with chromatic cardinal $\aleph_2$ can have every induced subgraph on $\aleph_1$ vertices of chromatic cardinal $= \aleph_0$. -/
theorem eq_aleph_0.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal = ℵ₀ := by
  sorry

/-- Refutation of `erdos_918.variants.eq_aleph_0_all_subgraphs.parts.i`: no graph on $\aleph_2$ vertices with chromatic cardinal $\aleph_2$ can have every subgraph on $\aleph_1$ vertices of chromatic cardinal $= \aleph_0$. -/
theorem eq_aleph_0_all_subgraphs.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal = ℵ₀ := by
  sorry

/-- Refutation of `erdos_918.variants.eq_aleph_0.parts.ii` at $\omega = \omega_0$. -/
theorem eq_aleph_0.parts.ii :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal = ℵ₀ := by
  sorry

/-- Refutation of `erdos_918.variants.eq_aleph_0_all_subgraphs.parts.ii` at $\omega = \omega_0$. -/
theorem eq_aleph_0_all_subgraphs.parts.ii :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal = ℵ₀ := by
  sorry

/-- Exact ordinal dichotomy for induced $= \aleph_0$ at $(\aleph_{\omega_0 + 1}, \aleph_{\omega_0})$: impossible iff $1 \le \omega_0$. -/
theorem induced_eq_aleph0_parts_ii_negation_iff_one_le (ω₀ : Ordinal.{u}) :
    (¬ ∃ (V : Type u) (G : SimpleGraph V),
      #V = ℵ_ (ω₀ + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω₀), (G.induce W).chromaticCardinal = ℵ₀) ↔
      (1 : Ordinal.{u}) ≤ ω₀ := by
  sorry

/-- Erdős–Hajnal (1968), Theorem 1's partition threshold in the graph-coloring form made explicit by Theorem 2: for any linear order $\alpha$, finite order $r \in \mathbb{N}$, and infinite cardinal $\mu$, $\chi(\mathrm{ShiftGraph}(r, \alpha)) \le \mu \iff |\alpha| \le \exp_2^{(r)}(\mu)$. -/
theorem chromatic_shiftGraph_le_iff_card_le_iteratedTwoPow
    (r : ℕ) (α : Type u) [LinearOrder α] {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    (ShiftGraph r α).chromaticCardinal ≤ μ ↔ #α ≤ iteratedTwoPow r μ := by
  sorry

end variants
end Erdos918
