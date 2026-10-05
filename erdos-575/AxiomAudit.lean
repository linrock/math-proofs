module

public import Solution
public import Statement


@[expose] public section

/-!
Full statement, fidelity, non-vacuity, and transitive-axiom checks for the
submitted Erdős #575 endpoints. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.
-/

namespace Erdos575.Audit

/-- The separately stated Formal Conjectures cyclic target is definitionally the proved proposition. -/
theorem statement_fidelity : _root_.Erdos575.Challenge.statement :=
  _root_.Erdos575.erdos_575

/-- The separately stated Formal Conjectures unrestricted target is definitionally the proved proposition. -/
theorem statement_unrestricted_fidelity : _root_.Erdos575.Challenge.statement_unrestricted :=
  _root_.Erdos575.erdos_575_unrestricted

/-- The cyclic counterexample family is nonempty, cyclic, and contains a bipartite member. -/
theorem nonvacuity_cyclic_domain :
    ∃ family : Finset CompactnessConjecture.FiniteGraph,
      family.Nonempty ∧
      CompactnessConjecture.IsCyclicFamily family ∧
      _root_.Erdos575.ContainsBipartiteMember family := by
  rcases _root_.Erdos575.correctedCounterexample with ⟨family, hne, hcyc, hbip, _, _⟩
  exact ⟨family, hne, hcyc, hbip⟩

/-- The self-contained two-forest family `{K_{1,2}, 2K_2}` is nonempty and contains a
bipartite member. -/
theorem nonvacuity_forest_domain :
    _root_.Erdos575.ForestCounterexample.forestFamily.Nonempty ∧
      _root_.Erdos575.ContainsBipartiteMember
        _root_.Erdos575.ForestCounterexample.forestFamily :=
  ⟨_root_.Erdos575.ForestCounterexample.forestFamily_nonempty,
    _root_.Erdos575.ForestCounterexample.forestFamily_containsBipartiteMember⟩

end Erdos575.Audit

#print Erdos575.not_erdos_575_corrected
#print Erdos575.not_erdos_575
#print Erdos575.not_erdos_575_all_bipartite
#print Erdos575.correctedCounterexample
#print Erdos575.quantitativeCounterexample
#print Erdos575.ForestCounterexample.forestCounterexample
#print Erdos575.ForestCounterexample.forestFamily_not_isBipartiteCompact
#print Erdos575.erdos_575
#print Erdos575.erdos_575_unrestricted
#print axioms Erdos575.not_erdos_575_corrected
#print axioms Erdos575.not_erdos_575
#print axioms Erdos575.not_erdos_575_all_bipartite
#print axioms Erdos575.correctedCounterexample
#print axioms Erdos575.quantitativeCounterexample
#print axioms Erdos575.ForestCounterexample.forestCounterexample
#print axioms Erdos575.ForestCounterexample.forestFamily_not_isBipartiteCompact
#print axioms Erdos575.erdos_575
#print axioms Erdos575.erdos_575_unrestricted
#print axioms Erdos575.Audit.statement_fidelity
#print axioms Erdos575.Audit.statement_unrestricted_fidelity
#print axioms Erdos575.Audit.nonvacuity_cyclic_domain
#print axioms Erdos575.Audit.nonvacuity_forest_domain
