module

/-
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

public import Solution
public import Statement

@[expose] public section

/-!
Full statement, fidelity, non-vacuity, and transitive-axiom checks for the
submitted Erdős #261 endpoints. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.
-/

namespace Erdos261.Palomar

/-- The separately stated Formal Conjectures target is definitionally the proved proposition. -/
theorem statement_fidelity : Erdos261.Challenge.statement :=
  Erdos261.erdos_261.parts.i

theorem statement_borwein_loring_fidelity : Erdos261.Challenge.statement_borwein_loring :=
  Erdos261.erdos_261.variants.borwein_loring

theorem statement_borwein_loring_property_fidelity :
    Erdos261.Challenge.statement_borwein_loring_property :=
  Erdos261.erdos_261.variants.borwein_loring_property

theorem statement_le_10000_fidelity : Erdos261.Challenge.statement_le_10000 :=
  Erdos261.erdos_261.variants.le_10000

theorem statement_two_representations_fidelity :
    Erdos261.Challenge.statement_two_representations :=
  Erdos261.erdos_261.variants.two_representations

/-- Explicit finite non-vacuity witness at $n = 10000$. -/
theorem nonvacuity_10000 : Erdos261Prop 10000 :=
  Erdos261.le_10000 (by decide) (by decide)

end Erdos261.Palomar

#print Erdos261.Palomar.borwein_loring
#print Erdos261.Palomar.borwein_loring_property
#print Erdos261.Palomar.erdos_261_parts_i
#print Erdos261.Palomar.le_10000
#print Erdos261.Palomar.two_representations
#print Erdos261.Palomar.infinite_rationals_two_pow_reps
#print Erdos261.Palomar.max_n_bound
#print Erdos261.Palomar.exists_term_le_add_three
#print Erdos261.Palomar.last_term_gap_dvd
#print Erdos261.Palomar.borwein_loring_unique
#print Erdos261.Palomar.punctured_family_erdos261Prop
#print Erdos261.Palomar.arbitrary_length_rep_of_all_erdos261Prop
#print Erdos261.erdos_261.variants.borwein_loring
#print Erdos261.erdos_261.variants.borwein_loring_property
#print Erdos261.erdos_261.parts.i
#print Erdos261.erdos_261.variants.le_10000
#print Erdos261.erdos_261.variants.two_representations
#print axioms Erdos261.Palomar.borwein_loring
#print axioms Erdos261.Palomar.borwein_loring_property
#print axioms Erdos261.Palomar.erdos_261_parts_i
#print axioms Erdos261.Palomar.le_10000
#print axioms Erdos261.Palomar.two_representations
#print axioms Erdos261.Palomar.infinite_rationals_two_pow_reps
#print axioms Erdos261.Palomar.max_n_bound
#print axioms Erdos261.Palomar.exists_term_le_add_three
#print axioms Erdos261.Palomar.last_term_gap_dvd
#print axioms Erdos261.Palomar.borwein_loring_unique
#print axioms Erdos261.Palomar.punctured_family_erdos261Prop
#print axioms Erdos261.Palomar.arbitrary_length_rep_of_all_erdos261Prop
#print axioms Erdos261.erdos_261.variants.borwein_loring
#print axioms Erdos261.erdos_261.variants.borwein_loring_property
#print axioms Erdos261.erdos_261.parts.i
#print axioms Erdos261.erdos_261.variants.le_10000
#print axioms Erdos261.erdos_261.variants.two_representations
#print axioms Erdos261.Palomar.statement_fidelity
#print axioms Erdos261.Palomar.statement_borwein_loring_fidelity
#print axioms Erdos261.Palomar.statement_borwein_loring_property_fidelity
#print axioms Erdos261.Palomar.statement_le_10000_fidelity
#print axioms Erdos261.Palomar.statement_two_representations_fidelity
#print axioms Erdos261.Palomar.nonvacuity_10000
