module

/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 OpenAI.
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

Adaptation notice: Linmiao Xu adapted the Erdős 575 definitions and statements
for this standalone Lean 4.35.0-rc2 Challenge in 2026. This file imports only
Mathlib.
-/

public import Mathlib


@[expose] public section

/-!
# Independent statements for Erdős problem 575: bipartite extremal-graph compactness

Given a finite family $\mathcal{F}$ of finite graphs, write $\mathrm{ex}(n;\mathcal{F})$
for the maximum number of edges in an $n$-vertex graph containing no member of
$\mathcal{F}$ as a subgraph. Erdős problem 575 asks whether, whenever
$\mathcal{F}$ contains at least one bipartite graph, there must exist a
**bipartite** $H \in \mathcal{F}$ such that
$$\mathrm{ex}(n;H) = O_{\mathcal{F}}(\mathrm{ex}(n;\mathcal{F})).$$

This standalone Mathlib-only module states nine targets covering:
- the negative answer to the corrected cycle-containing formulation
  (`not_erdos_575_corrected`, `erdos_575`),
- the negative answer to the unrestricted catalog formulation
  (`not_erdos_575`, `erdos_575_unrestricted`),
- the negative answer to the all-bipartite cyclic specialization
  (`not_erdos_575_all_bipartite`),
- the qualitative and quantitative cyclic all-bipartite counterexamples
  (`correctedCounterexample`, `quantitativeCounterexample`), and
- the self-contained bipartite forest counterexample $\mathcal{F}_0 = \{K_{1,2}, 2K_2\}$
  (`forestCounterexample`, `forestFamily_not_isBipartiteCompact`).

The nine intentional challenge holes are matched by proved declarations in
`Solution.lean`; `Solution.lean` does not import this module.
-/

namespace CompactnessConjecture

noncomputable section Foundations

open Filter Finset SimpleGraph
open scoped Topology

/-- A finite simple graph bundled with its vertex order `n`, represented as a
`SimpleGraph (Fin order)`. Allowing `order` to vary lets a single `Finset FiniteGraph`
contain forbidden graphs on different numbers of vertices. -/
structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

/-- A host graph `host` on `Fin n` is `FamilyFree family` if it contains no copy of
any graph in `family`. -/
def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

/-- The Turán extremal number `ex(n; family)`: the maximum number of edges in an
`n`-vertex simple graph that is `FamilyFree family`. -/
noncomputable def familyExtremal (family : Finset FiniteGraph)
    (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (FamilyFree family)).sup
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)

/-- Every forbidden graph in `family` contains a cycle (`¬ H.graph.IsAcyclic`). -/
def IsCyclicFamily (family : Finset FiniteGraph) : Prop :=
  ∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic

/-- Erdős–Simonovits compactness (#180): some member `H ∈ family` controls
`familyExtremal family n` up to a positive constant factor for all sufficiently
large `n`. -/
def IsCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
        C * (familyExtremal family n : ℝ)

/-- The reference polynomial scale `n ^ (4 / 3)` for the symplectic quadrangle
extremal lower bound. -/
def extremalScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((4 : ℝ) / 3)

/-- Every member `H ∈ family` satisfies `ex(n; H) ≥ c * n ^ (4 / 3)` for all
sufficiently large `n`. -/
def UniformMemberLower (family : Finset FiniteGraph) (c : ℝ) : Prop :=
  ∀ forbidden ∈ family,
    ∀ᶠ n : ℕ in atTop,
      c * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ)

end Foundations

end CompactnessConjecture

namespace Erdos575

open CompactnessConjecture Filter
open scoped Classical Topology

/-- The hypothesis of #575: at least one forbidden graph is bipartite. -/
def ContainsBipartiteMember (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, forbidden.graph.IsBipartite

/-- Eventual constant-factor control by one member of a forbidden family. -/
def ControlsFamily (family : Finset FiniteGraph)
    (forbidden : FiniteGraph) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
        C * (familyExtremal family n : ℝ)

/-- Unlike #180, #575 requires the controlling member to be bipartite. -/
def IsBipartiteCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family,
    forbidden.graph.IsBipartite ∧ ControlsFamily family forbidden

/-- The cataloged unrestricted question, retaining its mixed-family domain. -/
def BipartiteCompactnessStatement : Prop :=
  ∀ family : Finset FiniteGraph,
    family.Nonempty → ContainsBipartiteMember family →
      IsBipartiteCompactFamily family

/-- The meaningful corrected question: every forbidden graph contains a cycle. -/
def CyclicBipartiteCompactnessStatement : Prop :=
  ∀ family : Finset FiniteGraph,
    family.Nonempty → IsCyclicFamily family →
      ContainsBipartiteMember family → IsBipartiteCompactFamily family

/-- Even the more restricted all-bipartite cyclic question is false. -/
def AllBipartiteCyclicCompactnessStatement : Prop :=
    ∀ family : Finset FiniteGraph,
      family.Nonempty → IsCyclicFamily family →
        (∀ forbidden ∈ family, forbidden.graph.IsBipartite) →
          IsBipartiteCompactFamily family

/-- Negative answer to the intended cyclic correction of Erdős #575. -/
theorem not_erdos_575_corrected :
    ¬ CyclicBipartiteCompactnessStatement := by
  sorry

/-- Negative answer to the literal unrestricted catalog statement of Erdős #575. -/
theorem not_erdos_575 :
    ¬ BipartiteCompactnessStatement := by
  sorry

/-- Negative answer to the all-bipartite cyclic specialization of Erdős #575. -/
theorem not_erdos_575_all_bipartite :
    ¬ AllBipartiteCyclicCompactnessStatement := by
  sorry

/-- Explicit nonforest counterexample family whose members are all connected,
bipartite, and cyclic. -/
theorem correctedCounterexample :
    ∃ family : Finset FiniteGraph,
      family.Nonempty ∧
      IsCyclicFamily family ∧
      ContainsBipartiteMember family ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      ¬ IsBipartiteCompactFamily family := by
  sorry

/-- Quantitative separation counterexample with exponent gap `1 / 48`. -/
theorem quantitativeCounterexample :
    ∃ (family : Finset FiniteGraph) (c C : ℝ),
      family.Nonempty ∧
      ContainsBipartiteMember family ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      0 < C ∧
      UniformMemberLower family c ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree family host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal family n : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily family ∧
      ¬ IsBipartiteCompactFamily family := by
  sorry

/-- Elaborated Formal Conjectures `False ↔` form of the corrected cyclic statement. -/
theorem erdos_575 :
    False ↔
      ∀ family : Finset FiniteGraph,
        family.Nonempty → IsCyclicFamily family →
          ContainsBipartiteMember family → IsBipartiteCompactFamily family := by
  sorry

/-- Elaborated Formal Conjectures `False ↔` form of the unrestricted statement. -/
theorem erdos_575_unrestricted :
    False ↔
      ∀ family : Finset FiniteGraph,
        family.Nonempty →
          ContainsBipartiteMember family → IsBipartiteCompactFamily family := by
  sorry

end Erdos575

namespace Erdos575.ForestCounterexample

open CompactnessConjecture Erdos575 Filter SimpleGraph
open scoped Classical Topology

/-- The star simple graph on `Fin n` centered at vertex `0` (when `n > 0`). -/
def starSimpleGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u.val = 0 ∨ v.val = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The matching simple graph on `Fin n` pairing `2k` with `2k + 1`. -/
def matchingSimpleGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val / 2 = v.val / 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The cherry graph `K_{1,2}` on `Fin 3` with edges `{0,1}` and `{0,2}`. -/
abbrev cherryGraph : FiniteGraph := ⟨3, starSimpleGraph 3⟩

/-- The two-edge matching `2K_2` on `Fin 4` with edges `{0,1}` and `{2,3}`. -/
abbrev twoMatchingGraph : FiniteGraph := ⟨4, matchingSimpleGraph 4⟩

/-- The two-forest family `F_0 = {K_{1,2}, 2K_2}`. -/
noncomputable def forestFamily : Finset FiniteGraph :=
  {cherryGraph, twoMatchingGraph}

/-- `forestFamily` is not bipartite-compact. -/
theorem forestFamily_not_isBipartiteCompact :
    ¬ IsBipartiteCompactFamily forestFamily := by
  sorry

/-- Complete quantitative package for the bipartite forest counterexample `{K_{1,2}, 2K_2}`. -/
theorem forestCounterexample :
    forestFamily.Nonempty ∧
    ContainsBipartiteMember forestFamily ∧
    (∀ forbidden ∈ forestFamily, forbidden.graph.IsBipartite) ∧
    (∀ n : ℕ, familyExtremal forestFamily n ≤ 1) ∧
    (∀ n : ℕ, n / 2 ≤ SimpleGraph.extremalNumber n cherryGraph.graph) ∧
    (∀ n : ℕ, n - 1 ≤ SimpleGraph.extremalNumber n twoMatchingGraph.graph) ∧
    ¬ IsBipartiteCompactFamily forestFamily := by
  sorry

end Erdos575.ForestCounterexample
