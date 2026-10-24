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
public import Erdos902Unified435

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped Classical BigOperators

namespace Erdos902

/-- Schütte's property `S_n`: every set `E` of `n` vertices is dominated by a vertex outside it. -/
def HasPropertyS {V : Type*} (G : Digraph V) (n : ℕ) : Prop :=
  ∀ E : Finset V, E.card = n → ∃ x ∉ E, ∀ e ∈ E, G.Adj x e

namespace Core

/-- A tournament is a directed graph with no loops in which every pair of distinct vertices is
joined by exactly one directed edge. -/
def IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u))

end Core

/-- The upstream-shaped minimum vertex count for property `S_n`. -/
def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), Erdos902.Core.IsTournament G ∧ HasPropertyS G n}

/-- In a tournament, domination is exactly domination from outside the set. -/
theorem dominates_iff_notMem_and_forall' {V : Type*} {G : Digraph V} (hG : IsTournament G)
    (v : V) (S : Finset V) : Dominates G v S ↔ v ∉ S ∧ ∀ e ∈ S, G.Adj v e := by
  constructor
  · intro h
    refine ⟨fun hv => hG.1 v (h v hv), fun e he => h e he⟩
  · rintro ⟨-, h⟩
    exact h

theorem isParadoxicalTournament_of_hasPropertyS {V : Type*} [Fintype V] (n : ℕ)
    {G : Digraph V} (hn : n ≤ Fintype.card V) (hG : IsTournament G) (hS : HasPropertyS G n) :
    IsParadoxicalTournament n G :=
  ⟨hG, hn, fun E hE => by
    obtain ⟨x, hx, hedges⟩ := hS E hE
    exact ⟨x, fun e he => hedges e he⟩⟩


theorem hasParadoxicalTournament_iff_upstream {n N : ℕ} :
    HasParadoxicalTournament n N ↔
      (n ≤ N ∧ ∃ G : Digraph (Fin N), IsTournament G ∧ HasPropertyS G n) := by
  constructor
  · rintro ⟨G, hG⟩
    refine ⟨by have := card_gt_of_isParadoxicalTournament hG; omega, G, hG.1, ?_⟩
    exact fun E hE => by
      obtain ⟨v, hv⟩ := hG.2.2 E hE
      obtain ⟨hnot, hedges⟩ := (dominates_iff_notMem_and_forall' hG.1 v E).mp hv
      exact ⟨v, hnot, hedges⟩
  · rintro ⟨hnN, G, hG, hS⟩
    exact ⟨G, isParadoxicalTournament_of_hasPropertyS n (by simpa using hnN) hG hS⟩

theorem legacyF_eq_f (n : ℕ) : legacyF n = f n := by
  have hset : {N : ℕ | HasParadoxicalTournament n N}.Nonempty := by
    by_cases h : ∃ N : ℕ, HasParadoxicalTournament n N
    · obtain ⟨N, hN⟩ := h
      exact ⟨N, hN⟩
    · by_cases hn0 : n = 0
      · subst hn0
        exact ⟨1, hasParadoxicalTournament_zero_one⟩
      · exact ⟨ErdosUpperBoundFormula n,
          hasParadoxicalTournament_erdosUpperBoundFormula n (Nat.pos_of_ne_zero hn0)⟩
  have hmemLegacy : legacyF n ∈ {N : ℕ | HasParadoxicalTournament n N} :=
    Nat.sInf_mem hset
  have hle1 : f n ≤ legacyF n := by
    refine Nat.sInf_le ?_
    show legacyF n ∈ {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), IsTournament G ∧ HasPropertyS G n}
    exact hasParadoxicalTournament_iff_upstream.mp hmemLegacy
  have hle2 : legacyF n ≤ f n := by
    refine Nat.sInf_le ?_
    show f n ∈ {N : ℕ | HasParadoxicalTournament n N}
    have hfle : f n ≤ legacyF n := by
      refine Nat.sInf_le ?_
      show legacyF n ∈ {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), IsTournament G ∧ HasPropertyS G n}
      exact hasParadoxicalTournament_iff_upstream.mp hmemLegacy
    have hmemF : f n ∈ {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), IsTournament G ∧ HasPropertyS G n} := by
      refine Nat.sInf_mem ⟨legacyF n, ?_⟩
      obtain ⟨hcard, G, hG, hS⟩ := hasParadoxicalTournament_iff_upstream.mp hmemLegacy
      exact ⟨hcard, G, hG, hS⟩
    obtain ⟨hcard, G, hG, hS⟩ := hmemF
    exact ⟨G, isParadoxicalTournament_of_hasPropertyS n (by simpa using hcard) hG hS⟩
  exact le_antisymm hle2 hle1
end Erdos902
end
