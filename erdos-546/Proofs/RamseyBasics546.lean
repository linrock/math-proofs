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

The two Ramsey definitions are adapted verbatim from the Apache-2.0 file
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean in the
pinned Formal Conjectures repository. The remaining declarations establish
basic monotonicity, clique-containment, and empty-graph properties of
`graphRamsey` and `diagonalGraphRamsey`.
-/
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic


@[expose] public section

namespace SimpleGraph

noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphRamsey G G

end SimpleGraph

namespace Erdos546

open SimpleGraph

/-- The exact property whose least natural witness is `graphRamsey G H`. -/
def GraphRamseyWitness {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    (n : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ

theorem graphRamsey_le_of_witness {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (hn : GraphRamseyWitness G H n) : SimpleGraph.graphRamsey G H ≤ n :=
  Nat.sInf_le hn

theorem diagonalGraphRamsey_le_of_witness {α : Type*} [Fintype α]
    {G : SimpleGraph α} {n : ℕ} (hn : GraphRamseyWitness G G n) :
    SimpleGraph.diagonalGraphRamsey G ≤ n :=
  graphRamsey_le_of_witness hn

/-- A graph fits into any clique at least as large as its vertex type. -/
noncomputable def copyIntoClique {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (s : Finset W)
    (hs : H.IsClique (s : Set W)) (hcard : Fintype.card V ≤ s.card) : G.Copy H := by
  classical
  let f : V ↪ s :=
    (Function.Embedding.nonempty_of_card_le (by simpa using hcard)).some
  refine ⟨⟨fun v => (f v : W), ?_⟩, ?_⟩
  · intro v w hvw
    apply hs (f v).property (f w).property
    intro h
    exact hvw.ne (f.injective (Subtype.ext h))
  · intro v w h
    exact f.injective (Subtype.ext h)

theorem isContained_of_clique {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (s : Finset W)
    (hs : H.IsClique (s : Set W)) (hcard : Fintype.card V ≤ s.card) : G.IsContained H :=
  ⟨copyIntoClique G H s hs hcard⟩

/-- An injective change of vertices commutes with graph complementation. -/
theorem comap_compl_of_injective {V W : Type*} (f : V → W)
    (hf : Function.Injective f) (H : SimpleGraph W) :
    SimpleGraph.comap f Hᶜ = (SimpleGraph.comap f H)ᶜ := by
  ext v w
  simp only [SimpleGraph.comap_adj, SimpleGraph.compl_adj, hf.ne_iff]

/-- A concrete Ramsey witness remains valid on a larger complete host. -/
theorem GraphRamseyWitness.mono {α β : Type*}
    {G : SimpleGraph α} {H : SimpleGraph β} {m n : ℕ}
    (hm : GraphRamseyWitness G H m) (hmn : m ≤ n) : GraphRamseyWitness G H n := by
  classical
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  intro C
  rcases hm (SimpleGraph.comap f C) with hG | hH
  · exact Or.inl (hG.trans ⟨(SimpleGraph.Embedding.comap f C).toCopy⟩)
  · apply Or.inr
    rw [← comap_compl_of_injective f f.injective C] at hH
    exact hH.trans ⟨(SimpleGraph.Embedding.comap f Cᶜ).toCopy⟩

/-- The least witness has the forcing property whenever a witness exists.
The hypothesis is essential because `sInf ∅ = 0` in `ℕ`. -/
theorem graphRamsey_witness_of_exists {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} (hne : ∃ n, GraphRamseyWitness G H n) :
    GraphRamseyWitness G H (SimpleGraph.graphRamsey G H) :=
  Nat.sInf_mem hne

/-- Monotonicity in the target graphs, with an explicit existence premise. -/
theorem graphRamsey_mono_of_exists {α β α' β' : Type*}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    {G : SimpleGraph α} {H : SimpleGraph β}
    {G' : SimpleGraph α'} {H' : SimpleGraph β'}
    (hG : G.IsContained G') (hH : H.IsContained H')
    (hne : ∃ n, GraphRamseyWitness G' H' n) :
    SimpleGraph.graphRamsey G H ≤ SimpleGraph.graphRamsey G' H' := by
  apply graphRamsey_le_of_witness
  intro C
  rcases graphRamsey_witness_of_exists hne C with hGC | hHC
  · exact Or.inl (hG.trans hGC)
  · exact Or.inr (hH.trans hHC)

theorem graphRamsey_eq_zero_of_isEmpty_left {α β : Type*} [Fintype α] [Fintype β]
    [IsEmpty α] (G : SimpleGraph α) (H : SimpleGraph β) :
    SimpleGraph.graphRamsey G H = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact graphRamsey_le_of_witness (fun C => Or.inl SimpleGraph.IsContained.of_isEmpty)

theorem graphRamsey_eq_zero_of_isEmpty_right {α β : Type*} [Fintype α] [Fintype β]
    [IsEmpty β] (G : SimpleGraph α) (H : SimpleGraph β) :
    SimpleGraph.graphRamsey G H = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact graphRamsey_le_of_witness (fun C => Or.inr SimpleGraph.IsContained.of_isEmpty)

theorem diagonalGraphRamsey_eq_zero_of_isEmpty {α : Type*} [Fintype α] [IsEmpty α]
    (G : SimpleGraph α) : SimpleGraph.diagonalGraphRamsey G = 0 :=
  graphRamsey_eq_zero_of_isEmpty_left G G

/-- Edgeless target graphs require only enough vertices for one target. -/
theorem graphRamsey_bot_bot {α β : Type*} [Fintype α] [Fintype β] :
    SimpleGraph.graphRamsey (⊥ : SimpleGraph α) (⊥ : SimpleGraph β) =
      min (Fintype.card α) (Fintype.card β) := by
  classical
  have hbot : GraphRamseyWitness (⊥ : SimpleGraph α) (⊥ : SimpleGraph β)
      (min (Fintype.card α) (Fintype.card β)) := by
    intro C
    rcases le_total (Fintype.card α) (Fintype.card β) with hab | hba
    · apply Or.inl
      apply SimpleGraph.bot_isContained_iff_card_le.mpr
      simp [min_eq_left hab]
    · apply Or.inr
      apply SimpleGraph.bot_isContained_iff_card_le.mpr
      simp [min_eq_right hba]
  apply le_antisymm (graphRamsey_le_of_witness hbot)
  have hleast := graphRamsey_witness_of_exists ⟨_, hbot⟩
    (⊥ : SimpleGraph (Fin (SimpleGraph.graphRamsey
      (⊥ : SimpleGraph α) (⊥ : SimpleGraph β))))
  rcases hleast with ha | hb
  · have hcard := SimpleGraph.bot_isContained_iff_card_le.mp ha
    simp only [Fintype.card_fin] at hcard
    exact (min_le_left _ _).trans hcard
  · have hcard := SimpleGraph.bot_isContained_iff_card_le.mp hb
    simp only [Fintype.card_fin] at hcard
    exact (min_le_right _ _).trans hcard

theorem diagonalGraphRamsey_bot {α : Type*} [Fintype α] :
    SimpleGraph.diagonalGraphRamsey (⊥ : SimpleGraph α) = Fintype.card α := by
  simp [SimpleGraph.diagonalGraphRamsey, graphRamsey_bot_bot]

end Erdos546
