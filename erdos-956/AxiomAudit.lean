import Solution
import Statement

/-!
Full statement, fidelity, non-vacuity, and transitive-axiom checks for the
submitted Erdős #956 endpoints. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.
-/

namespace Erdos956.Palomar

/-- The separately stated Formal Conjectures target is definitionally the proved proposition. -/
theorem statement_fidelity : Erdos956.Challenge.statement :=
  Erdos956.erdos_956

/-- Explicit finite non-vacuity witness at `N = 80` (`q = 1` of the four-layer signed grid):
`144 ≤ h 80`. -/
theorem nonvacuity_h_80 : 144 ≤ h 80 :=
  Erdos956.FourLayer.h_80_ge_144

end Erdos956.Palomar

#print Erdos956.Palomar.erdos_956_superlinear
#print Erdos956.Palomar.erdos_956
#print Erdos956.Palomar.erdos_956_omega_four_thirds
#print Erdos956.Palomar.erdos_956_four_layer_polynomial
#print Erdos956.Palomar.erdos_956_eventual_two_fifths
#print Erdos956.erdos_956
#print axioms Erdos956.Palomar.erdos_956_superlinear
#print axioms Erdos956.Palomar.erdos_956
#print axioms Erdos956.Palomar.erdos_956_omega_four_thirds
#print axioms Erdos956.Palomar.erdos_956_four_layer_polynomial
#print axioms Erdos956.Palomar.erdos_956_eventual_two_fifths
#print axioms Erdos956.erdos_956
#print axioms Erdos956.Palomar.statement_fidelity
#print axioms Erdos956.Palomar.nonvacuity_h_80
