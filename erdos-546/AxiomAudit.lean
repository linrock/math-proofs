module

public import Solution
public import Statement


@[expose] public section

/-!
Full statement, fidelity, non-vacuity, and transitive-axiom checks for the
submitted Erdős #546 endpoints. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.
-/

namespace Erdos546.Audit

/-- The separately stated Formal Conjectures target is definitionally the proved proposition. -/
theorem statement_fidelity : _root_.Erdos546.Challenge.statement :=
  _root_.erdos_546_original_statement

/-- Non-vacuity on the empty vertex type `Empty` at `m = 0`:
the no-isolates hypothesis holds vacuously, the edge count is `0`, and
`diagonalGraphRamsey` is `0`. -/
theorem nonvacuity_empty_graph :
    (∀ v : Empty, 0 < (⊥ : SimpleGraph Empty).degree v) ∧
    (⊥ : SimpleGraph Empty).edgeSet.ncard = 0 ∧
    SimpleGraph.diagonalGraphRamsey (⊥ : SimpleGraph Empty) = 0 :=
  ⟨fun v => v.elim, by simp, Erdos546.diagonalGraphRamsey_eq_zero_of_isEmpty _⟩

/-- Non-vacuity on `K_2` (`⊤ : SimpleGraph (Fin 2)`): every vertex has positive
degree `1 > 0` and the explicit bound holds. -/
theorem nonvacuity_complete_two :
    (∀ v : Fin 2, 0 < (⊤ : SimpleGraph (Fin 2)).degree v) ∧
    (SimpleGraph.diagonalGraphRamsey (⊤ : SimpleGraph (Fin 2)) : ℝ) ≤
      (2 : ℝ) ^ (4000 * Real.sqrt (⊤ : SimpleGraph (Fin 2)).edgeSet.ncard) := by
  refine ⟨by decide, ?_⟩
  exact Erdos546.sudakov_sparse_bound (⊤ : SimpleGraph (Fin 2))
    (⊤ : SimpleGraph (Fin 2)).edgeSet.ncard (by decide) rfl

end Erdos546.Audit

#print erdos_546_original_statement
#print Erdos546.erdos_546
#print Erdos546.sudakov_sparse_bound
#print Erdos546.sparse_graph_ramsey_witness
#print Erdos546.boundedDegree_sparse_cut
#print Erdos546.exists_monoPair_of_low_edgeDensity
#print Erdos546.quantitative_monoPair_amplification
#print axioms erdos_546_original_statement
#print axioms Erdos546.erdos_546
#print axioms Erdos546.sudakov_sparse_bound
#print axioms Erdos546.sparse_graph_ramsey_witness
#print axioms Erdos546.boundedDegree_sparse_cut
#print axioms Erdos546.exists_monoPair_of_low_edgeDensity
#print axioms Erdos546.quantitative_monoPair_amplification
#print axioms Erdos546.Audit.statement_fidelity
#print axioms Erdos546.Audit.nonvacuity_empty_graph
#print axioms Erdos546.Audit.nonvacuity_complete_two
