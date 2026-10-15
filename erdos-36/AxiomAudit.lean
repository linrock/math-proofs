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

namespace Erdos36

theorem statement_scherk_1955_fidelity : Erdos36.Challenge.statement_scherk_1955 :=
  minimum_overlap_variants_lower_scherk_1955

theorem statement_swierczkowski_1958_fidelity : Erdos36.Challenge.statement_swierczkowski_1958 :=
  minimum_overlap_variants_lower_swierczkowski_1958

theorem statement_exists_limit_fidelity : Erdos36.Challenge.statement_exists_limit :=
  ⟨_, tendsto_minOverlapQuotient_liminf⟩

theorem nonvacuity_M_fourteen : M 14 = 6 :=
  exact_values_M.2.2.2.2.2.2.2.2.1

end Erdos36

#print Erdos36.liminf_eq_limsup_minOverlapQuotient
#print Erdos36.tendsto_minOverlapQuotient_liminf
#print Erdos36.minimum_overlap_variants_lower_erdos_1955
#print Erdos36.minimum_overlap_variants_lower_scherk_1955
#print Erdos36.minimum_overlap_variants_lower_swierczkowski_1958
#print Erdos36.moser_sqrt_two_div_four_le_liminf
#print Erdos36.minimum_overlap_variants_upper_erdos_1955
#print Erdos36.moser_scherk_combined_le_M
#print Erdos36.exact_values_M
#print axioms Erdos36.liminf_eq_limsup_minOverlapQuotient
#print axioms Erdos36.tendsto_minOverlapQuotient_liminf
#print axioms Erdos36.minimum_overlap_variants_lower_erdos_1955
#print axioms Erdos36.minimum_overlap_variants_lower_scherk_1955
#print axioms Erdos36.minimum_overlap_variants_lower_swierczkowski_1958
#print axioms Erdos36.moser_sqrt_two_div_four_le_liminf
#print axioms Erdos36.minimum_overlap_variants_upper_erdos_1955
#print axioms Erdos36.moser_scherk_combined_le_M
#print axioms Erdos36.exact_values_M
#print axioms Erdos36.statement_scherk_1955_fidelity
#print axioms Erdos36.statement_swierczkowski_1958_fidelity
#print axioms Erdos36.statement_exists_limit_fidelity
#print axioms Erdos36.nonvacuity_M_fourteen
