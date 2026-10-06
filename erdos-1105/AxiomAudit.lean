module

public import Solution
public import Statement

@[expose] public section

/-! Full statement, fidelity, and transitive-axiom checks for the submitted
Erdős #1105 endpoints. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. -/

namespace Erdos1105.Palomar

/-- The separately stated Part (i) target is definitionally the proved proposition. -/
theorem statement_i_fidelity : Erdos1105.Challenge.statement_i :=
  Erdos1105.erdos_1105.parts.i

/-- The separately stated Part (ii) target is definitionally the proved proposition. -/
theorem statement_ii_fidelity : Erdos1105.Challenge.statement_ii :=
  Erdos1105.erdos_1105.parts.ii

end Erdos1105.Palomar

#print Erdos1105.Palomar.erdos_1105_cycles
#print Erdos1105.Palomar.erdos_1105_paths
#print Erdos1105.Palomar.erdos_1105_parts_i
#print Erdos1105.Palomar.erdos_1105_parts_ii
#print Erdos1105.Palomar.antiRamseyNum_triangle
#print Erdos1105.Palomar.cycle_fullBlock_lower
#print Erdos1105.Palomar.cycle_real_lower
#print Erdos1105.Palomar.cycle_linear_upper
#print Erdos1105.erdos_1105.parts.i
#print Erdos1105.erdos_1105.parts.ii
#print axioms Erdos1105.Palomar.erdos_1105_cycles
#print axioms Erdos1105.Palomar.erdos_1105_paths
#print axioms Erdos1105.Palomar.erdos_1105_parts_i
#print axioms Erdos1105.Palomar.erdos_1105_parts_ii
#print axioms Erdos1105.Palomar.antiRamseyNum_triangle
#print axioms Erdos1105.Palomar.cycle_fullBlock_lower
#print axioms Erdos1105.Palomar.cycle_real_lower
#print axioms Erdos1105.Palomar.cycle_linear_upper
#print axioms Erdos1105.erdos_1105.parts.i
#print axioms Erdos1105.erdos_1105.parts.ii
#print axioms Erdos1105.Palomar.statement_i_fidelity
#print axioms Erdos1105.Palomar.statement_ii_fidelity
