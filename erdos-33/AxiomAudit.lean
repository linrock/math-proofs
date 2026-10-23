module

/-
Copyright 2025-2026 The Formal Conjectures Authors.
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

namespace Erdos33

theorem statement_one_mem_lowerBounds_fidelity : Erdos33.Challenge.statement_one_mem_lowerBounds :=
  erdos_33_variants_one_mem_lowerBounds

theorem statement_vanDoorn_fidelity : Erdos33.Challenge.statement_vanDoorn :=
  erdos_33_variants_vanDoorn

theorem nonvacuity_fib_complement :
    AdditiveBasisCondition (vanDoornUnion fibBlockWidth) :=
  additiveBasisCondition_vanDoornUnion (fun j => Nat.fib_pos.2 (by omega))

end Erdos33

#print axioms Erdos33.erdos_33_variants_one_mem_lowerBounds
#print axioms Erdos33.erdos_33_variants_vanDoorn
#print axioms Erdos33.sixty_three_fiftieths_le_iInf_limsup
#print axioms Erdos33.exists_ge_sixty_three_fiftieths_normalizedPrefixRatio
#print axioms Erdos33.additiveBasisCondition_vanDoornUnion
#print axioms Erdos33.two_mul_sum_fibBlockWidth_div_sqrt_start_le
#print axioms Erdos33.one_hundred_twenty_seven_over_one_hundred_le_iInf_limsup
#print axioms Erdos33.exists_ge_one_hundred_twenty_seven_over_one_hundred_normalizedPrefixRatio
#print axioms Erdos33.Core.five_fourths_le_iInf_limsup
#print axioms Erdos33.Core.exists_ge_five_fourths_normalizedPrefixRatio
#print axioms Erdos33.statement_one_mem_lowerBounds_fidelity
#print axioms Erdos33.statement_vanDoorn_fidelity
#print axioms Erdos33.nonvacuity_fib_complement
