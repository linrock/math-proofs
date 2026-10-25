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

namespace Erdos423

theorem statement_erdos_423_variants_nondecreasing_fidelity :
    Erdos423.Challenge.statement_erdos_423_variants_nondecreasing :=
  @erdos_423.variants.nondecreasing

theorem statement_erdos_423_variants_unbounded_fidelity :
    Erdos423.Challenge.statement_erdos_423_variants_unbounded :=
  @erdos_423.variants.unbounded

theorem statement_erdos_423_variants_infinite_complement_fidelity :
    Erdos423.Challenge.statement_erdos_423_variants_infinite_complement :=
  @erdos_423.variants.infinite_complement

theorem statement_existsUnique_isHofstadterSeq_fidelity :
    Erdos423.Challenge.statement_existsUnique_isHofstadterSeq :=
  @existsUnique_isHofstadterSeq

theorem statement_IsHofstadterSeq_card_omitted_Icc_eq_sub_fidelity :
    Erdos423.Challenge.statement_IsHofstadterSeq_card_omitted_Icc_eq_sub :=
  @IsHofstadterSeq_card_omitted_Icc_eq_sub

theorem statement_IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum_fidelity :
    Erdos423.Challenge.statement_IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum :=
  @IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum

theorem statement_two_mul_sub_one_le_of_prefixSum_le_fidelity :
    Erdos423.Challenge.statement_two_mul_sub_one_le_of_prefixSum_le :=
  @two_mul_sub_one_le_of_prefixSum_le

theorem statement_strict_excess_increase_of_blockSum_eq_two_pow_fidelity :
    Erdos423.Challenge.statement_strict_excess_increase_of_blockSum_eq_two_pow :=
  @strict_excess_increase_of_blockSum_eq_two_pow

theorem statement_completed_square_tail_quadratic_identity_fidelity :
    Erdos423.Challenge.statement_completed_square_tail_quadratic_identity :=
  @completed_square_tail_quadratic_identity

theorem statement_exists_completed_square_discriminant_of_two_pow_fidelity :
    Erdos423.Challenge.statement_exists_completed_square_discriminant_of_two_pow :=
  @exists_completed_square_discriminant_of_two_pow

theorem statement_discriminantOffset_emod_eight_fidelity :
    Erdos423.Challenge.statement_discriminantOffset_emod_eight :=
  @discriminantOffset_emod_eight

theorem statement_completed_square_collision_factor_eq_fidelity :
    Erdos423.Challenge.statement_completed_square_collision_factor_eq :=
  @completed_square_collision_factor_eq

theorem statement_two_pow_le_of_completed_square_collision_fidelity :
    Erdos423.Challenge.statement_two_pow_le_of_completed_square_collision :=
  @two_pow_le_of_completed_square_collision

theorem statement_two_mul_le_succ_of_completed_square_collision_fidelity :
    Erdos423.Challenge.statement_two_mul_le_succ_of_completed_square_collision :=
  @two_mul_le_succ_of_completed_square_collision

theorem statement_completedSquareExpFiber_card_le_one_fidelity :
    Erdos423.Challenge.statement_completedSquareExpFiber_card_le_one :=
  @completedSquareExpFiber_card_le_one

theorem statement_not_eventual_linear_of_isHofstadterSeq_fidelity :
    Erdos423.Challenge.statement_not_eventual_linear_of_isHofstadterSeq :=
  @not_eventual_linear_of_isHofstadterSeq

theorem statement_exists_stabilization_breaking_index_le_fidelity :
    Erdos423.Challenge.statement_exists_stabilization_breaking_index_le :=
  @exists_stabilization_breaking_index_le

theorem statement_strict_excess_increase_at_stabilizationIndexHorizon_fidelity :
    Erdos423.Challenge.statement_strict_excess_increase_at_stabilizationIndexHorizon :=
  @strict_excess_increase_at_stabilizationIndexHorizon

theorem statement_le_excess_of_iterExcessHorizon_le_fidelity :
    Erdos423.Challenge.statement_le_excess_of_iterExcessHorizon_le :=
  @le_excess_of_iterExcessHorizon_le

theorem statement_iterExcessHorizon_one_eq_sixteen_fidelity :
    Erdos423.Challenge.statement_iterExcessHorizon_one_eq_sixteen :=
  @iterExcessHorizon_one_eq_sixteen

theorem statement_nextExcessHorizon_le_two_pow_five_mul_sq_add_fidelity :
    Erdos423.Challenge.statement_nextExcessHorizon_le_two_pow_five_mul_sq_add :=
  @nextExcessHorizon_le_two_pow_five_mul_sq_add

theorem statement_erdos_423_variants_lower_bound_of_iterExcessHorizon_log_log_le_fidelity :
    Erdos423.Challenge.statement_erdos_423_variants_lower_bound_of_iterExcessHorizon_log_log_le :=
  @erdos_423_variants_lower_bound_of_iterExcessHorizon_log_log_le

theorem statement_erdos_423_variants_upper_bound_of_iterExcessHorizon_rpow_le_fidelity :
    Erdos423.Challenge.statement_erdos_423_variants_upper_bound_of_iterExcessHorizon_rpow_le :=
  @erdos_423_variants_upper_bound_of_iterExcessHorizon_rpow_le

theorem statement_erdos_423_of_iterExcessHorizon_littleO_bound_fidelity :
    Erdos423.Challenge.statement_erdos_423_of_iterExcessHorizon_littleO_bound :=
  @erdos_423_of_iterExcessHorizon_littleO_bound

end Erdos423

#print axioms Erdos423.erdos_423.variants.nondecreasing
#print axioms Erdos423.erdos_423.variants.unbounded
#print axioms Erdos423.erdos_423.variants.infinite_complement
#print axioms Erdos423.existsUnique_isHofstadterSeq
#print axioms Erdos423.IsHofstadterSeq_card_omitted_Icc_eq_sub
#print axioms Erdos423.IsHofstadterSeq_exists_ge_three_eq_iff_isGlobalConsecutiveBlockSum
#print axioms Erdos423.two_mul_sub_one_le_of_prefixSum_le
#print axioms Erdos423.strict_excess_increase_of_blockSum_eq_two_pow
#print axioms Erdos423.completed_square_tail_quadratic_identity
#print axioms Erdos423.exists_completed_square_discriminant_of_two_pow
#print axioms Erdos423.discriminantOffset_emod_eight
#print axioms Erdos423.completed_square_collision_factor_eq
#print axioms Erdos423.two_pow_le_of_completed_square_collision
#print axioms Erdos423.two_mul_le_succ_of_completed_square_collision
#print axioms Erdos423.completedSquareExpFiber_card_le_one
#print axioms Erdos423.not_eventual_linear_of_isHofstadterSeq
#print axioms Erdos423.exists_stabilization_breaking_index_le
#print axioms Erdos423.strict_excess_increase_at_stabilizationIndexHorizon
#print axioms Erdos423.le_excess_of_iterExcessHorizon_le
#print axioms Erdos423.iterExcessHorizon_one_eq_sixteen
#print axioms Erdos423.nextExcessHorizon_le_two_pow_five_mul_sq_add
#print axioms Erdos423.erdos_423_variants_lower_bound_of_iterExcessHorizon_log_log_le
#print axioms Erdos423.erdos_423_variants_upper_bound_of_iterExcessHorizon_rpow_le
#print axioms Erdos423.erdos_423_of_iterExcessHorizon_littleO_bound
