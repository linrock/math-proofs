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

namespace Erdos70.Palomar

theorem statement_omega_one_refuted_fidelity : Erdos70.Challenge.statement_omega_one_refuted :=
  fun h => erdos_70_omega_one_refuted.mpr h

theorem statement_omega_three_fidelity : Erdos70.Challenge.statement_omega_three :=
  ordinalCardinalRamsey3_continuum_omega_three

end Erdos70.Palomar

#print Erdos70.Palomar.not_ordinalCardinalRamsey3_continuum_aleph1_four
#print Erdos70.Palomar.erdos_70_omega_one_refuted
#print Erdos70.Palomar.ordinalCardinalRamsey3_continuum_omega_three
#print Erdos70.Palomar.erdos_70_omega_three_solved
#print axioms Erdos70.Palomar.not_ordinalCardinalRamsey3_continuum_aleph1_four
#print axioms Erdos70.Palomar.erdos_70_omega_one_refuted
#print axioms Erdos70.Palomar.ordinalCardinalRamsey3_continuum_omega_three
#print axioms Erdos70.Palomar.erdos_70_omega_three_solved
#print axioms Erdos70.Palomar.statement_omega_one_refuted_fidelity
#print axioms Erdos70.Palomar.statement_omega_three_fidelity
