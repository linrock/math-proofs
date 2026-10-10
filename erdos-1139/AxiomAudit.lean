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
submitted Erdős #1139 endpoints. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.
-/

namespace Erdos1139.Palomar

/-- The separately stated Formal Conjectures target is definitionally the proved proposition
under the published Green–Tao–Ziegler von Mangoldt linear-forms hypothesis. -/
theorem statement_fidelity
    (published : _root_.Erdos1139.HasFixedSignedMixedPublishedVonMangoldtAsymptotics) :
    Erdos1139.Challenge.statement :=
  erdos_1139_of_gtz published

end Erdos1139.Palomar

#print Erdos1139.Palomar.uniform_maximal_gap
#print Erdos1139.Palomar.limsup_strictly_gt_one
#print Erdos1139.Palomar.cover_crt_interval
#print Erdos1139.Palomar.seven_square_crt
#print Erdos1139.Palomar.primorial_log_limit
#print Erdos1139.Palomar.limsup_top_of_sparse
#print Erdos1139.Palomar.erdos_1139_of_gtz
#print Erdos1139.Palomar.prime_ap_of_gtz
#print Erdos1139.Palomar.core_classification
#print axioms Erdos1139.Palomar.uniform_maximal_gap
#print axioms Erdos1139.Palomar.limsup_strictly_gt_one
#print axioms Erdos1139.Palomar.cover_crt_interval
#print axioms Erdos1139.Palomar.seven_square_crt
#print axioms Erdos1139.Palomar.primorial_log_limit
#print axioms Erdos1139.Palomar.limsup_top_of_sparse
#print axioms Erdos1139.Palomar.erdos_1139_of_gtz
#print axioms Erdos1139.Palomar.prime_ap_of_gtz
#print axioms Erdos1139.Palomar.core_classification
#print axioms Erdos1139.Palomar.statement_fidelity
