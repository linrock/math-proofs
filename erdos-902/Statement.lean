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

noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics

namespace Erdos902.Challenge

def IsTournament {V : Type*} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ (∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u))

def Dominates {V : Type*} (G : Digraph V) (v : V) (S : Finset V) : Prop :=
  ∀ u ∈ S, G.Adj v u

def outNeigh {N : ℕ} (G : Digraph (Fin N)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun u => G.Adj v u)

def inNeigh {N : ℕ} (G : Digraph (Fin N)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun u => G.Adj u v)

def commonOutNeigh {N : ℕ} (G : Digraph (Fin N)) (u v : Fin N) : Finset (Fin N) :=
  outNeigh G u ∩ outNeigh G v

def IsParadoxicalTournament {V : Type*} [Fintype V] (n : ℕ) (G : Digraph V) : Prop :=
  IsTournament G ∧ n ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card = n → ∃ v : V, Dominates G v S

def HasParadoxicalTournament (n N : ℕ) : Prop :=
  ∃ G : Digraph (Fin N), IsParadoxicalTournament n G

noncomputable def f (n : ℕ) : ℕ :=
  sInf {N : ℕ | HasParadoxicalTournament n N}

def ErdosProbabilisticCriterion (n N : ℕ) : Prop :=
  N.choose n * (2 ^ n - 1) ^ (N - n) < (2 ^ n) ^ (N - n)

def statement_small_cases_and_paley : Prop :=
  f 0 = 1 ∧ f 1 = 3 ∧ f 2 = 7 ∧ 14 ≤ f 3 ∧ f 3 ≤ 19 ∧ f 3 = 19 ∧ 47 ≤ f 4 ∧ f 4 ≤ 67

def statement_erdos_szekeres_sandwich : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    2 ^ (n + 1) - 1 ≤ f n ∧
      (n + 2) * 2 ^ (n - 1) - 1 ≤ f n ∧
      f n ≤ n * (n + 1) * 2 ^ n ∧
      f n ≤ n + (n ^ 2 + 5) * 2 ^ n ∧
      f n ≤ 5 * n ^ 2 * 2 ^ n

end Erdos902.Challenge

namespace Erdos902

def HasPropertyS {V : Type*} (G : Digraph V) (n : ℕ) : Prop :=
  ∀ E : Finset V, E.card = n → ∃ x ∉ E, ∀ e ∈ E, G.Adj x e

noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), Erdos902.Challenge.IsTournament G ∧ HasPropertyS G n}


end Erdos902
end
