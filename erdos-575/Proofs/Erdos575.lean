module

/-
Erdős problem #575, including its intended restriction to cyclic forbidden
families, follows negatively from the particular all-bipartite counterexample
in OpenAI's Apache-2.0 `CompactnessAndDegeneracy.lean` at commit
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6.

The bare negated #180 statement does not directly provide the bipartite
witness used here: the bridge explicitly uses the nonempty, cyclic,
all-bipartite `proposedFamily` and proves that the controlling member required
by #575 itself must be bipartite.
-/
public import CompactnessAndDegeneracy


@[expose] public section

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

/-- Forgetting the required coloring turns a #575 controller into a #180 one. -/
theorem isCompactFamily_of_isBipartiteCompactFamily
    {family : Finset FiniteGraph}
    (hcompact : IsBipartiteCompactFamily family) :
    IsCompactFamily family :=
  let ⟨forbidden, hmem, _, hcontrol⟩ := hcompact
  ⟨forbidden, hmem, hcontrol⟩

/-- For all-bipartite families, an unrestricted controller is admissible. -/
theorem isBipartiteCompactFamily_of_isCompactFamily
    {family : Finset FiniteGraph}
    (hbipartite : ∀ forbidden ∈ family, forbidden.graph.IsBipartite)
    (hcompact : IsCompactFamily family) :
    IsBipartiteCompactFamily family :=
  let ⟨forbidden, hmem, hcontrol⟩ := hcompact
  ⟨forbidden, hmem, hbipartite forbidden hmem, hcontrol⟩

/-- Exactly on all-bipartite families, the two compactness notions coincide. -/
theorem isBipartiteCompactFamily_iff_isCompactFamily
    {family : Finset FiniteGraph}
    (hbipartite : ∀ forbidden ∈ family, forbidden.graph.IsBipartite) :
    IsBipartiteCompactFamily family ↔ IsCompactFamily family :=
  ⟨isCompactFamily_of_isBipartiteCompactFamily,
    isBipartiteCompactFamily_of_isCompactFamily hbipartite⟩

/-- The upstream witness has no nonbipartite members at all. -/
theorem proposedFamily_allBipartite :
    ∀ forbidden ∈ proposedFamily, forbidden.graph.IsBipartite :=
  fun _ h => proposedFamily_member_isBipartite h

/-- The hypothesis is nonvacuous: its specific four-cycle is bipartite. -/
theorem proposedFamily_containsBipartiteMember :
    ContainsBipartiteMember proposedFamily :=
  ⟨finiteCycle 4, four_cycle_mem_proposedFamily,
    proposedFamily_member_isBipartite four_cycle_mem_proposedFamily⟩

/-- The particular cyclic OpenAI witness does not satisfy #575's conclusion. -/
theorem proposedFamily_not_isBipartiteCompact :
    ¬ IsBipartiteCompactFamily proposedFamily :=
  fun h => proposedFamily_not_compact (isCompactFamily_of_isBipartiteCompactFamily h)

/-- In fact every member is bipartite and every individual control fails. -/
theorem proposedFamily_noMemberControls :
    ∀ forbidden ∈ proposedFamily,
      forbidden.graph.IsBipartite ∧
        ¬ ControlsFamily proposedFamily forbidden :=
  fun forbidden hforbidden =>
    ⟨proposedFamily_member_isBipartite hforbidden,
      fun hcontrol => proposedFamily_not_compact ⟨forbidden, hforbidden, hcontrol⟩⟩

/-- A concrete nonforest counterexample with all the intended graph geometry. -/
theorem correctedCounterexample :
    ∃ family : Finset FiniteGraph,
      family.Nonempty ∧
      IsCyclicFamily family ∧
      ContainsBipartiteMember family ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      ¬ IsBipartiteCompactFamily family :=
  ⟨proposedFamily, proposedFamily_nonempty, proposedFamily_isCyclic,
    proposedFamily_containsBipartiteMember,
    fun forbidden h => ⟨proposedFamily_member_connected h,
      proposedFamily_member_isBipartite h, proposedFamily_isCyclic forbidden h⟩,
    proposedFamily_not_isBipartiteCompact⟩

/-- The all-bipartite cyclic specialization already has a counterexample. -/
theorem not_erdos_575_all_bipartite :
    ¬ AllBipartiteCyclicCompactnessStatement :=
  fun h => proposedFamily_not_isBipartiteCompact
    (h proposedFamily proposedFamily_nonempty
      proposedFamily_isCyclic proposedFamily_allBipartite)

/-- A positive corrected mixed-family statement would imply its specialization. -/
theorem allBipartiteStatement_of_cyclicStatement
    (hstatement : CyclicBipartiteCompactnessStatement) :
    AllBipartiteCyclicCompactnessStatement :=
  fun family ⟨forbidden, hforbidden⟩ hcyclic hbipartite =>
    hstatement family ⟨forbidden, hforbidden⟩ hcyclic
      ⟨forbidden, hforbidden, hbipartite forbidden hforbidden⟩

/-- Negative answer to the intended cyclic correction of Erdős #575. -/
theorem not_erdos_575_corrected :
    ¬ CyclicBipartiteCompactnessStatement :=
  fun h => not_erdos_575_all_bipartite (allBipartiteStatement_of_cyclicStatement h)

/-- The unrestricted catalog statement would imply the corrected statement. -/
theorem cyclicStatement_of_unrestrictedStatement
    (hstatement : BipartiteCompactnessStatement) :
    CyclicBipartiteCompactnessStatement :=
  fun family hnonempty _hcyclic hcontains => hstatement family hnonempty hcontains

/-- The literal catalog statement is false even on the nonforest witness. -/
theorem not_erdos_575 : ¬ BipartiteCompactnessStatement :=
  fun h => not_erdos_575_corrected (cyclicStatement_of_unrestrictedStatement h)

/-- The #575 witness inherits all upstream quantitative separation bounds. -/
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
  refine ⟨proposedFamily, manuscriptLowerConstant, compactnessHostPowerConstant,
    proposedFamily_nonempty, proposedFamily_containsBipartiteMember,
    fun forbidden h => ⟨proposedFamily_member_connected h,
      proposedFamily_member_isBipartite h, proposedFamily_isCyclic forbidden h⟩,
    manuscriptLowerConstant_pos, ?_, proposedFamily_uniformMemberLower,
    proposedFamilyFree_sixteenth_power_host_bound,
    proposedFamily_familyExtremal_sixteenth_power_le,
    by norm_num, by norm_num,
    proposedFamily_not_compact, proposedFamily_not_isBipartiteCompact⟩
  unfold compactnessHostPowerConstant compactnessDegreePowerConstant
  positivity

/-- Elaborated Formal Conjectures `False ↔` form of the corrected cyclic statement. -/
theorem erdos_575 :
    False ↔
      ∀ family : Finset FiniteGraph,
        family.Nonempty → IsCyclicFamily family →
          ContainsBipartiteMember family → IsBipartiteCompactFamily family :=
  ⟨False.elim, fun h => not_erdos_575_corrected h⟩

/-- Elaborated Formal Conjectures `False ↔` form of the unrestricted statement. -/
theorem erdos_575_unrestricted :
    False ↔
      ∀ family : Finset FiniteGraph,
        family.Nonempty →
          ContainsBipartiteMember family → IsBipartiteCompactFamily family :=
  ⟨False.elim, fun h => not_erdos_575 h⟩

end Erdos575
