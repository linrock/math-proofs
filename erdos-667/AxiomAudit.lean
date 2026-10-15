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

namespace Erdos667

theorem statement_endpoint_fidelity : Erdos667.Challenge.statement_endpoint :=
  variants.endpoint

theorem nonvacuity_H_three_two_eq (n : ℕ) : Erdos667.Core.H 3 2 n = (n + 1) / 2 :=
  Erdos667.Core.H_three_two_eq n

end Erdos667

#print Erdos667.variants.monotoneOn
#print Erdos667.variants.endpoint
#print Erdos667.variants.ramsey_lower_bound
#print Erdos667.variants.c_ge_inv_pred
#print axioms Erdos667.variants.monotoneOn
#print axioms Erdos667.variants.endpoint
#print axioms Erdos667.variants.ramsey_lower_bound
#print axioms Erdos667.variants.c_ge_inv_pred
#print axioms Erdos667.statement_endpoint_fidelity
#print axioms Erdos667.nonvacuity_H_three_two_eq
