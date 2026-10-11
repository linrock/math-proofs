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

namespace Erdos1180.Palomar

theorem statement_erdos_1180_fidelity : Erdos1180.Challenge.statement_erdos_1180 :=
  erdos_1180

theorem statement_glibichuk_fidelity : Erdos1180.Challenge.statement_glibichuk :=
  erdos_1180_variants_glibichuk

theorem statement_shparlinski_fidelity : Erdos1180.Challenge.statement_shparlinski :=
  erdos_1180_variants_shparlinski

theorem statement_lower_bound_fidelity : Erdos1180.Challenge.statement_lower_bound :=
  erdos_1180_variants_lower_bound

theorem statement_lower_bound_large_primes_fidelity :
    Erdos1180.Challenge.statement_lower_bound_large_primes :=
  erdos_1180_variants_lower_bound_large_primes

theorem statement_optimal_false_fidelity : Erdos1180.Challenge.statement_optimal_false :=
  not_erdos_1180_variants_optimal

theorem nonvacuity_casymptotic_one_half :
    CAsymptotic (1 / 2 : ℝ) ≤ 128 := by
  have h := CAsymptotic_le_eight_mul_sq_of_one_lt_mul (ε := 1 / 2) (k := 4)
    (by norm_num) (by omega) (by norm_num)
  omega

end Erdos1180.Palomar

#print Erdos1180.Palomar.erdos_1180
#print Erdos1180.Palomar.erdos_1180_variants_glibichuk
#print Erdos1180.Palomar.erdos_1180_variants_shparlinski
#print Erdos1180.Palomar.erdos_1180_variants_lower_bound
#print Erdos1180.Palomar.erdos_1180_variants_lower_bound_large_primes
#print Erdos1180.Palomar.not_erdos_1180_variants_optimal
#print Erdos1180.Palomar.two_rpow_inv_le_four_mul_C
#print Erdos1180.Palomar.inv_le_CAsymptotic
#print Erdos1180.Palomar.natCeil_inv_le_CAsymptotic
#print Erdos1180.Palomar.CAsymptotic_le_thirty_two_mul_inv_sq
#print Erdos1180.Palomar.CAsymptotic_le_eight_mul_sq_of_one_lt_mul
#print Erdos1180.Palomar.CAsymptotic_le_eight_mul_succ_of_two_lt_mul
#print Erdos1180.Palomar.CAsymptotic_le_eight_mul_of_lt_mul
#print Erdos1180.Palomar.CAsymptotic_le_sixteen_of_two_thirds_lt
#print Erdos1180.Palomar.CAsymptotic_le_eight_mul_floor_inv_add_one_sq
#print Erdos1180.Palomar.eventually_CAsymptotic_le_eight_add_mul_inv_sq
#print Erdos1180.Palomar.CAsymptotic_inv_nat_lt_C_inv_nat
#print Erdos1180.erdos_1180
#print Erdos1180.erdos_1180.variants.glibichuk
#print Erdos1180.erdos_1180.variants.shparlinski
#print Erdos1180.erdos_1180.variants.lower_bound
#print Erdos1180.erdos_1180.variants.lower_bound_large_primes
#print Erdos1180.not_erdos_1180_variants_optimal
#print axioms Erdos1180.Palomar.erdos_1180
#print axioms Erdos1180.Palomar.erdos_1180_variants_glibichuk
#print axioms Erdos1180.Palomar.erdos_1180_variants_shparlinski
#print axioms Erdos1180.Palomar.erdos_1180_variants_lower_bound
#print axioms Erdos1180.Palomar.erdos_1180_variants_lower_bound_large_primes
#print axioms Erdos1180.Palomar.not_erdos_1180_variants_optimal
#print axioms Erdos1180.Palomar.two_rpow_inv_le_four_mul_C
#print axioms Erdos1180.Palomar.inv_le_CAsymptotic
#print axioms Erdos1180.Palomar.natCeil_inv_le_CAsymptotic
#print axioms Erdos1180.Palomar.CAsymptotic_le_thirty_two_mul_inv_sq
#print axioms Erdos1180.Palomar.CAsymptotic_le_eight_mul_sq_of_one_lt_mul
#print axioms Erdos1180.Palomar.CAsymptotic_le_eight_mul_succ_of_two_lt_mul
#print axioms Erdos1180.Palomar.CAsymptotic_le_eight_mul_of_lt_mul
#print axioms Erdos1180.Palomar.CAsymptotic_le_sixteen_of_two_thirds_lt
#print axioms Erdos1180.Palomar.CAsymptotic_le_eight_mul_floor_inv_add_one_sq
#print axioms Erdos1180.Palomar.eventually_CAsymptotic_le_eight_add_mul_inv_sq
#print axioms Erdos1180.Palomar.CAsymptotic_inv_nat_lt_C_inv_nat
#print axioms Erdos1180.erdos_1180
#print axioms Erdos1180.erdos_1180.variants.glibichuk
#print axioms Erdos1180.erdos_1180.variants.shparlinski
#print axioms Erdos1180.erdos_1180.variants.lower_bound
#print axioms Erdos1180.erdos_1180.variants.lower_bound_large_primes
#print axioms Erdos1180.not_erdos_1180_variants_optimal
#print axioms Erdos1180.Palomar.statement_erdos_1180_fidelity
#print axioms Erdos1180.Palomar.statement_glibichuk_fidelity
#print axioms Erdos1180.Palomar.statement_shparlinski_fidelity
#print axioms Erdos1180.Palomar.statement_lower_bound_fidelity
#print axioms Erdos1180.Palomar.statement_lower_bound_large_primes_fidelity
#print axioms Erdos1180.Palomar.statement_optimal_false_fidelity
#print axioms Erdos1180.Palomar.nonvacuity_casymptotic_one_half
