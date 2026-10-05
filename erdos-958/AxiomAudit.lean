module

public import Solution
public import Statement


@[expose] public section

/-!
Full statement, fidelity, non-vacuity, and transitive-axiom checks for the
submitted Erdős #958 endpoints. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.
-/

namespace Erdos958.Palomar

open Finset EuclideanGeometry

/-- The separately stated Formal Conjectures target is definitionally the proved proposition. -/
theorem statement_fidelity : Erdos958.Challenge.statement :=
  Erdos958.erdos_958

/-- Explicit finite non-vacuity witness at `n = 5` for the Clemen–Dumitrescu–Liu configuration `cdlSet 5`. -/
theorem nonvacuity_cdlSet_5 :
    #(Erdos958.cdlSet 5) = 5 ∧
      #(distanceSet (Erdos958.cdlSet 5)) = 4 ∧
      (distanceSet (Erdos958.cdlSet 5)).image (distanceMultiplicity (Erdos958.cdlSet 5)) =
        Finset.Icc 1 4 ∧
      ¬ IsEquidistantOnLine (Erdos958.cdlSet 5) ∧
      ¬ IsEquidistantOnCircle (Erdos958.cdlSet 5) :=
  Erdos958.clemen_dumitrescu_liu 5 (by decide)

end Erdos958.Palomar

#print Erdos958.Palomar.erdos_958
#print Erdos958.Palomar.not_erdos_958
#print Erdos958.Palomar.clemen_dumitrescu_liu
#print Erdos958.Palomar.equidistantOnLine_has_profile
#print Erdos958.Palomar.equidistantOnCircle_exists_has_profile
#print Erdos958.erdos_958
#print axioms Erdos958.Palomar.erdos_958
#print axioms Erdos958.Palomar.not_erdos_958
#print axioms Erdos958.Palomar.clemen_dumitrescu_liu
#print axioms Erdos958.Palomar.equidistantOnLine_has_profile
#print axioms Erdos958.Palomar.equidistantOnCircle_exists_has_profile
#print axioms Erdos958.erdos_958
#print axioms Erdos958.Palomar.statement_fidelity
#print axioms Erdos958.Palomar.nonvacuity_cdlSet_5
