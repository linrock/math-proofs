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

public import Erdos306Unified435
public import HeadPrimeRowAdmissibilityDefectsAndMultiTailWitnesses306

@[expose] public section


set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

noncomputable section
open scoped BigOperators

namespace Erdos306.PrimeResidueAndRowPotential

/-! ## Part 1: 11-Element `U_37(p)` Local Row-Admissibility Defect Envelope and `|E| ≥ 59` -/

def headRowEnvelope (p q : ℕ) : Finset ℕ :=
  (headPrimes29.erase p) ∪ {31, q}

def headRowEnvelope37 (p : ℕ) : Finset ℕ :=
  headRowEnvelope p 37

def tailEnvelopePrimes47 : Finset ℕ :=
  {37, 41, 43, 47}

def headPrimeEnvelope37Defect (p : ℕ) : ℚ :=
  if p = 3 then 6430 / 3093459
  else if p = 7 then 9974 / 7998403
  else if p = 11 then 9810 / 12568919
  else if p = 13 then 9728 / 14854177
  else if p = 17 then 9564 / 19424693
  else if p = 19 then 9482 / 21709951
  else if p = 23 then 9318 / 26280467
  else if p = 29 then 54 / 640987
  else 0

theorem not_primeRowAdmissible_headPrimes29_erase {p : ℕ} (hp : p ∈ headDefectPrimes29.erase 3) :
    ¬ PrimeRowAdmissible p (headPrimes29.erase p) := by
  decide +revert

theorem not_headPrimes29_erase_subset_of_card_le_nine
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ headDefectPrimes29.erase 3)
    (hcard : S.card ≤ 9) (hadm : PrimeRowAdmissible p S) :
    ¬ (headPrimes29.erase p ⊆ S) := by
  intro hsub
  have hp29 : p ∈ headPrimes29 := by
    rcases Finset.mem_erase.mp hp with ⟨_, hp_def⟩
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp_def)
  have hcard_erase : (headPrimes29.erase p).card = 9 := by
    have h : ∀ x ∈ headPrimes29, (headPrimes29.erase x).card = 9 := by decide
    exact h p hp29
  have heq : headPrimes29.erase p = S :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact not_primeRowAdmissible_headPrimes29_erase hp (heq ▸ hadm)

theorem exists_erase_of_subset_of_card_eq_ten_of_card_eq_eleven
    {U S : Finset ℕ} (hsub : S ⊆ U) (hS : S.card = 10) (hU : U.card = 11) :
    ∃ x ∈ U, S = U.erase x := by
  have hcard_sdiff : (U \ S).card = 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard_sdiff
  have hx_mem : x ∈ U \ S := by
    rw [hx]
    exact Finset.mem_singleton_self x
  rcases Finset.mem_sdiff.mp hx_mem with ⟨hxU, hxS⟩
  refine ⟨x, hxU, ?_⟩
  have hsub_erase : S ⊆ U.erase x := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun hyx => hxS (hyx ▸ hy), hsub hy⟩
  exact Finset.eq_of_subset_of_card_le hsub_erase (by rw [Finset.card_erase_of_mem hxU, hU, hS])

theorem prime_ge_forty_one_of_not_mem_headPrimes29_ne_thirty_one_ne_thirty_seven
    {q : ℕ} (hq : q.Prime) (hnot : q ∉ headPrimes29) (hne31 : q ≠ 31) (hne37 : q ≠ 37) :
    41 ≤ q := by
  have hge37 : 37 ≤ q := prime_ge_thirty_seven_of_not_mem_headPrimes29_ne_thirty_one hq hnot hne31
  by_contra hlt41
  have hmem : q ∈ Finset.Icc 38 40 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcheck : ∀ n ∈ Finset.Icc 38 40, ¬ Nat.Prime n := by decide
  exact hcheck q hmem hq

theorem exists_tail_neighbor_ge_forty_one_of_not_subset_headRowEnvelope37
    {p : ℕ} {S : Finset ℕ} (hpS : p ∉ S) (hprime : ∀ q ∈ S, q.Prime)
    (hnot : ¬ S ⊆ headRowEnvelope37 p) :
    ∃ q ∈ S \ headPrimes29, 41 ≤ q := by
  obtain ⟨q, hqS, hqnot⟩ := Finset.not_subset.mp hnot
  have hqp : q ≠ p := fun h => hpS (h ▸ hqS)
  have hqnotH : q ∉ headPrimes29 := by
    intro hqH
    apply hqnot
    unfold headRowEnvelope37 headRowEnvelope
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hqp, hqH⟩))
  have hne31 : q ≠ 31 := by
    intro h31
    apply hqnot
    unfold headRowEnvelope37 headRowEnvelope
    rw [h31]
    simp
  have hne37 : q ≠ 37 := by
    intro h37
    apply hqnot
    unfold headRowEnvelope37 headRowEnvelope
    rw [h37]
    simp
  exact ⟨q, Finset.mem_sdiff.mpr ⟨hqS, hqnotH⟩,
    prime_ge_forty_one_of_not_mem_headPrimes29_ne_thirty_one_ne_thirty_seven
      (hprime q hqS) hqnotH hne31 hne37⟩

theorem headPrimeEnvelope37Defect_aux_bounds :
    (∀ p ∈ ({2, 3, 5} : Finset ℕ), headPrimeEnvelope37Defect p = headPrimeFullRowDefect p) ∧
    (∀ p ∈ headDefectPrimes29.erase 3, (headRowEnvelope37 p).card = 11) ∧
    (∀ p ∈ headDefectPrimes29.erase 3,
      headPrimeEnvelope37Defect p ≤ headCardLam p + headMinMissingPairSlack p) ∧
    (∀ p ∈ headDefectPrimes29.erase 3,
      headPrimeEnvelope37Defect p ≤ (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ))) ∧
    (∀ p ∈ headDefectPrimes29.erase 3,
      headPrimeEnvelope37Defect p ≤
        (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 41 : ℚ)) + headMinMissingPairSlack p) ∧
    (∀ p ∈ headDefectPrimes29.erase 3, ∀ x ∈ headRowEnvelope37 p,
      PrimeRowAdmissible p ((headRowEnvelope37 p).erase x) →
        headPrimeEnvelope37Defect p ≤ headRowCapacityDefect p ((headRowEnvelope37 p).erase x)) := by
  decide +kernel

theorem headPrimeEnvelope37Defect_le_headRowCapacityDefect
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ headPrimes29) (hpS : p ∉ S)
    (hcard : S.card ≤ 10) (hprime : ∀ q ∈ S, q.Prime)
    (hadm : PrimeRowAdmissible p S) :
    headPrimeEnvelope37Defect p ≤ headRowCapacityDefect p S := by
  by_cases hp235 : p ∈ ({2, 3, 5} : Finset ℕ)
  · rw [headPrimeEnvelope37Defect_aux_bounds.1 p hp235]
    exact headPrimeFullRowDefect_le_headRowCapacityDefect hp hpS hcard hprime hadm
  · have hp_def3 : p ∈ headDefectPrimes29.erase 3 := by
      have h : ∀ x ∈ headPrimes29, x ∉ ({2, 3, 5} : Finset ℕ) → x ∈ headDefectPrimes29.erase 3 := by
        decide
      exact h p hp hp235
    have hp_def : p ∈ headDefectPrimes29 := Finset.mem_of_mem_erase hp_def3
    by_cases hc9 : S.card ≤ 9
    · have hnot_sub := not_headPrimes29_erase_subset_of_card_le_nine hp_def3 hc9 hadm
      have hmiss := headMinMissingPairSlack_le_headRowMissingPairSlack_of_not_subset hp hnot_sub
      have h1 : (1 : ℚ) ≤ (10 : ℚ) - (S.card : ℚ) := by
        have hc9_q : (S.card : ℚ) ≤ 9 := by exact_mod_cast hc9
        linarith
      have hdeg : headCardLam p ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
        nlinarith [headCardLam_nonneg p]
      have haux := headPrimeEnvelope37Defect_aux_bounds.2.2.1 p hp_def3
      unfold headRowCapacityDefect headRowAdmissibilityDefect
      linarith [headRowTailSlack_nonneg (p := p) hprime]
    · have hc10 : S.card = 10 := by omega
      by_cases hsub37 : S ⊆ headRowEnvelope37 p
      · have hU11 := headPrimeEnvelope37Defect_aux_bounds.2.1 p hp_def3
        obtain ⟨x, hx, rfl⟩ :=
          exists_erase_of_subset_of_card_eq_ten_of_card_eq_eleven hsub37 hc10 hU11
        exact headPrimeEnvelope37Defect_aux_bounds.2.2.2.2.2 p hp_def3 x hx hadm
      · by_cases hsubH : headPrimes29.erase p ⊆ S
        · obtain ⟨q, hq, hS_eq⟩ :=
            exists_single_tail_neighbor_of_head_erase_subset_of_card_eq_ten hp hpS hsubH hc10
          rcases Finset.mem_sdiff.mp hq with ⟨hqS, hqnotH⟩
          have hnot43 : q ∉ smallTailPrimes43 := by
            intro hq43
            exact not_primeRowAdmissible_head_union_singleton_of_mem_smallTailPrimes43
              hp_def hq43 (hS_eq ▸ hadm)
          have hge47 : 47 ≤ q :=
            prime_ge_forty_seven_of_not_mem_headPrimes29_not_mem_smallTailPrimes43
              (hprime q hqS) hqnotH hnot43
          have hinv47 : (1 : ℚ) / (q : ℚ) ≤ (1 / 47 : ℚ) :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge47)
          have hp_pos : (0 : ℚ) ≤ (1 : ℚ) / (p : ℚ) := by positivity
          have hterm :
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 47 : ℚ)) ≤
                (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) :=
            mul_le_mul_of_nonneg_left (by linarith) hp_pos
          have hsingle :
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) ≤ headRowTailSlack p S := by
            unfold headRowTailSlack
            apply Finset.single_le_sum (fun r hr => ?_) hq
            rcases Finset.mem_sdiff.mp hr with ⟨hrS, hrnot⟩
            have hge31 : 31 ≤ r := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime r hrS) hrnot
            have hinv31 : (1 : ℚ) / (r : ℚ) ≤ (1 / 31 : ℚ) :=
              one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
            exact mul_nonneg hp_pos (sub_nonneg.mpr hinv31)
          have hdeg0 : (0 : ℚ) ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
            rw [hc10]; norm_num
          have haux := headPrimeEnvelope37Defect_aux_bounds.2.2.2.1 p hp_def3
          unfold headRowCapacityDefect headRowAdmissibilityDefect
          linarith [headRowMissingPairSlack_nonneg p S]
        · obtain ⟨q, hq, hge41⟩ :=
            exists_tail_neighbor_ge_forty_one_of_not_subset_headRowEnvelope37 hpS hprime hsub37
          have hinv41 : (1 : ℚ) / (q : ℚ) ≤ (1 / 41 : ℚ) :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge41)
          have hp_pos : (0 : ℚ) ≤ (1 : ℚ) / (p : ℚ) := by positivity
          have hterm :
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 41 : ℚ)) ≤
                (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) :=
            mul_le_mul_of_nonneg_left (by linarith) hp_pos
          have hsingle :
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) ≤ headRowTailSlack p S := by
            unfold headRowTailSlack
            apply Finset.single_le_sum (fun r hr => ?_) hq
            rcases Finset.mem_sdiff.mp hr with ⟨hrS, hrnot⟩
            have hge31 : 31 ≤ r := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime r hrS) hrnot
            have hinv31 : (1 : ℚ) / (r : ℚ) ≤ (1 / 31 : ℚ) :=
              one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
            exact mul_nonneg hp_pos (sub_nonneg.mpr hinv31)
          have hmiss := headMinMissingPairSlack_le_headRowMissingPairSlack_of_not_subset hp hsubH
          have hdeg0 : (0 : ℚ) ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
            rw [hc10]; norm_num
          have haux := headPrimeEnvelope37Defect_aux_bounds.2.2.2.2.1 p hp_def3
          unfold headRowCapacityDefect headRowAdmissibilityDefect
          linarith

theorem prime_edges_card_ge_fifty_nine_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    59 ≤ E.card := by
  have hE_lt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hsum_div : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = ((1 : ℤ) : ℚ) / ((1 : ℕ) : ℚ) := by
    simpa using hsum
  have hcap := constant_tail_capacity_with_full_row_defect E hE
  have hdef_sum :
      (∑ p ∈ headPrimes29, headPrimeEnvelope37Defect p) ≤
        ∑ p ∈ headPrimes29, headRowCapacityDefect p (graphNeighbors E p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp_prime : p.Prime := by decide +revert
    have hpS : p ∉ graphNeighbors E p := not_mem_graphNeighbors_self E hE_lt p
    have hcard : (graphNeighbors E p).card ≤ 10 := by
      rw [card_graphNeighbors_eq_incidenceDegree E hE_lt p]
      exact hdeg p hp_prime
    have hprime : ∀ q ∈ graphNeighbors E p, q.Prime := by
      intro q hq
      rcases (mem_graphNeighbors_iff E p q).mp hq with he | he
      · exact (hE (p, q) he).2.1
      · exact (hE (q, p) he).1
    have hadm : PrimeRowAdmissible p (graphNeighbors E p) :=
      (prime_graph_row_admissible_of_sum_eq_div E p 1 1 hE hp_prime (by decide) (Nat.coprime_one_right p) hsum_div).1
    exact headPrimeEnvelope37Defect_le_headRowCapacityDefect hp hpS hcard hprime hadm
  have hconst :
      (10 : ℚ) * (∑ p ∈ headPrimes29, headCardLam p) +
        (∑ e ∈ headPairs29, headCardSlack e) -
        (∑ p ∈ headPrimes29, headPrimeEnvelope37Defect p) +
        58 * ((1 / 31 : ℚ) ^ 2) < 1 := by
    decide +kernel
  have hlt : (58 : ℚ) < (E.card : ℚ) := by
    by_contra hle
    have hle' : (E.card : ℚ) ≤ 58 := not_lt.mp hle
    have hmul : ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) ≤ 58 * ((1 / 31 : ℚ) ^ 2) := by linarith
    linarith
  have hlt_nat : 58 < E.card := by exact_mod_cast hlt
  omega

theorem semiprime_set_card_ge_fifty_nine_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    59 ≤ S.card := by
  obtain ⟨E, hE, hprod⟩ := Erdos306.PrimeIncidence.semiprime_set_is_prime_edge_image S hS
  have hcard : S.card = E.card := by
    rw [← hprod, Finset.card_image_of_injOn (Erdos306.Representation.product_injOn_prime_edges E hE)]
  have hdegE : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10 := by
    intro p hp
    have hcount := Erdos306.Representation.degree_eq_divisible_denominators E hE p hp
    change incidenceDegree E p = _ at hcount
    rw [hprod] at hcount
    rw [hcount]
    exact hdeg p hp
  have hsumImage := Erdos306.Representation.reciprocal_sum_image_prime_edges E hE
  rw [hprod] at hsumImage
  have hsumE : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 := by
    have hcast :
        (∑ e ∈ E, (1 : ℚ) / (e.1 * e.2 : ℕ)) =
          ∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro e _
      push_cast
      rfl
    rw [← hcast, ← hsumImage]
    exact hsum
  rw [hcard]
  exact prime_edges_card_ge_fifty_nine_of_sum_eq_one E hE hdegE hsumE

/-! ## Part 2: `primes47` Local Row-Admissibility Defect Envelope and `|E| ≥ 60, 61` -/

def headPrimePrimes47Defect (p : ℕ) : ℚ :=
  if p = 3 then 6430 / 3093459
  else if p = 7 then 1812 / 950429
  else if p = 11 then 9810 / 12568919
  else if p = 13 then 22 / 21359
  else if p = 17 then 22 / 27931
  else if p = 19 then 8714 / 12726523
  else if p = 23 then 565920 / 972377279
  else if p = 29 then 100 / 640987
  else 0

def headPrimes47Target : Finset ℕ :=
  {7, 13, 17, 19, 23, 29}

theorem not_primeRowAdmissible_headRowCandidate31_erase_of_ge_nineteen
    {p : ℕ} (hp : p ∈ ({19, 23, 29} : Finset ℕ)) :
    ∀ x ∈ headRowCandidate31 p, ¬ PrimeRowAdmissible p ((headRowCandidate31 p).erase x) := by
  decide +revert

theorem exists_erase_of_subset_of_card_eq_nine_of_card_eq_ten
    {U S : Finset ℕ} (hsub : S ⊆ U) (hS : S.card = 9) (hU : U.card = 10) :
    ∃ x ∈ U, S = U.erase x := by
  have hcard_sdiff : (U \ S).card = 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard_sdiff
  have hx_mem : x ∈ U \ S := by
    rw [hx]
    exact Finset.mem_singleton_self x
  rcases Finset.mem_sdiff.mp hx_mem with ⟨hxU, hxS⟩
  refine ⟨x, hxU, ?_⟩
  have hsub_erase : S ⊆ U.erase x := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun hyx => hxS (hyx ▸ hy), hsub hy⟩
  exact Finset.eq_of_subset_of_card_le hsub_erase (by rw [Finset.card_erase_of_mem hxU, hU, hS])

theorem exists_tail_neighbor_ne_thirty_one_of_not_subset_headRowCandidate31
    {p : ℕ} {S : Finset ℕ} (hpS : p ∉ S) (hnot : ¬ S ⊆ headRowCandidate31 p) :
    ∃ q ∈ S \ headPrimes29, q ≠ 31 := by
  obtain ⟨q, hqS, hqnot⟩ := Finset.not_subset.mp hnot
  have hqp : q ≠ p := fun h => hpS (h ▸ hqS)
  have hqnotH : q ∉ headPrimes29 := by
    intro hqH
    apply hqnot
    unfold headRowCandidate31
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hqp, hqH⟩))
  have hne31 : q ≠ 31 := by
    intro h31
    apply hqnot
    unfold headRowCandidate31
    rw [h31]; simp
  exact ⟨q, Finset.mem_sdiff.mpr ⟨hqS, hqnotH⟩, hne31⟩

theorem prime_ge_fifty_three_of_not_mem_headPrimes29_ne_thirty_one_not_mem_tailEnvelopePrimes47
    {q : ℕ} (hq : q.Prime) (hnotH : q ∉ headPrimes29) (hne31 : q ≠ 31)
    (hnotT : q ∉ tailEnvelopePrimes47) :
    53 ≤ q := by
  have hge37 : 37 ≤ q := prime_ge_thirty_seven_of_not_mem_headPrimes29_ne_thirty_one hq hnotH hne31
  by_contra hlt53
  have hmem : q ∈ Finset.Icc 37 52 := Finset.mem_Icc.mpr ⟨hge37, by omega⟩
  have hcheck : ∀ n ∈ Finset.Icc 37 52, Nat.Prime n → n ∈ tailEnvelopePrimes47 := by decide
  exact hnotT (hcheck q hmem hq)

theorem prime_gt_thirty_seven_ge_forty_one {q : ℕ} (hq : q.Prime) (hgt : 37 < q) :
    41 ≤ q := by
  by_contra hlt41
  have hmem : q ∈ Finset.Icc 38 40 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcheck : ∀ n ∈ Finset.Icc 38 40, ¬ Nat.Prime n := by decide
  exact hcheck q hmem hq

theorem ordered_pair_of_two_le_card (T : Finset ℕ) (h2 : 2 ≤ T.card) :
    ∃ q₁ ∈ T, ∃ q₂ ∈ T, q₁ < q₂ := by
  have h1 : 1 < T.card := by omega
  obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp h1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨a, ha, b, hb, hlt⟩
  · exact ⟨b, hb, a, ha, hgt⟩

theorem pair_le_headRowTailSlack {p q₁ q₂ : ℕ} {S : Finset ℕ}
    (hprime : ∀ q ∈ S, q.Prime)
    (hq₁ : q₁ ∈ S \ headPrimes29) (hq₂ : q₂ ∈ S \ headPrimes29) (hne : q₁ ≠ q₂) :
    (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q₁ : ℚ)) +
      (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q₂ : ℚ)) ≤ headRowTailSlack p S := by
  have hsub : ({q₁, q₂} : Finset ℕ) ⊆ S \ headPrimes29 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hp_pos : (0 : ℚ) ≤ (1 : ℚ) / (p : ℚ) := by positivity
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun q : ℕ => (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)))
    (fun r hr _ => by
      rcases Finset.mem_sdiff.mp hr with ⟨hrS, hrnot⟩
      have hge31 : 31 ≤ r := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime r hrS) hrnot
      have hinv31 : (1 : ℚ) / (r : ℚ) ≤ (1 / 31 : ℚ) :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
      exact mul_nonneg hp_pos (sub_nonneg.mpr hinv31))
  rw [Finset.sum_pair hne] at hle
  exact hle

theorem not_headPrimes29_erase_subset_of_two_tail_neighbors
    {p q₁ q₂ : ℕ} {S : Finset ℕ} (hp : p ∈ headPrimes29) (hcard : S.card ≤ 10)
    (hq₁ : q₁ ∈ S \ headPrimes29) (hq₂ : q₂ ∈ S \ headPrimes29) (hne : q₁ ≠ q₂) :
    ¬ (headPrimes29.erase p ⊆ S) := by
  intro hsub
  have hpair_sub : ({q₁, q₂} : Finset ℕ) ⊆ S \ headPrimes29 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h2 : 2 ≤ (S \ headPrimes29).card := by
    have h := Finset.card_le_card hpair_sub
    rwa [Finset.card_pair hne] at h
  have hsub_inter : headPrimes29.erase p ⊆ S ∩ headPrimes29 :=
    Finset.subset_inter hsub (Finset.erase_subset p headPrimes29)
  have hcard_erase : (headPrimes29.erase p).card = 9 := by
    have h : ∀ x ∈ headPrimes29, (headPrimes29.erase x).card = 9 := by decide
    exact h p hp
  have h9 : 9 ≤ (S ∩ headPrimes29).card := by
    rw [← hcard_erase]
    exact Finset.card_le_card hsub_inter
  have hsplit := Finset.card_sdiff_add_card_inter S headPrimes29
  omega

theorem exists_headRowEnvelope_of_sdiff_erase_card_le_one
    {p : ℕ} {S : Finset ℕ} (hpS : p ∉ S)
    (hsubT : (S \ headPrimes29).erase 31 ⊆ tailEnvelopePrimes47)
    (hcard1 : ((S \ headPrimes29).erase 31).card ≤ 1) :
    ∃ q ∈ tailEnvelopePrimes47, S ⊆ headRowEnvelope p q := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard1 with h0 | h1
  · refine ⟨37, by decide, ?_⟩
    have hemp : (S \ headPrimes29).erase 31 = ∅ := Finset.card_eq_zero.mp h0
    intro x hx
    unfold headRowEnvelope
    by_cases hxH : x ∈ headPrimes29
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨fun hxp => hpS (hxp ▸ hx), hxH⟩))
    · by_cases hx31 : x = 31
      · subst hx31; simp
      · exfalso
        have hmem : x ∈ (S \ headPrimes29).erase 31 :=
          Finset.mem_erase.mpr ⟨hx31, Finset.mem_sdiff.mpr ⟨hx, hxH⟩⟩
        rw [hemp] at hmem
        exact Finset.notMem_empty x hmem
  · obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp h1
    have hq_mem : q ∈ tailEnvelopePrimes47 :=
      hsubT (by rw [hq_eq]; exact Finset.mem_singleton_self q)
    refine ⟨q, hq_mem, ?_⟩
    intro x hx
    unfold headRowEnvelope
    by_cases hxH : x ∈ headPrimes29
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨fun hxp => hpS (hxp ▸ hx), hxH⟩))
    · by_cases hx31 : x = 31
      · subst hx31; simp
      · have hmem : x ∈ (S \ headPrimes29).erase 31 :=
          Finset.mem_erase.mpr ⟨hx31, Finset.mem_sdiff.mpr ⟨hx, hxH⟩⟩
        rw [hq_eq, Finset.mem_singleton] at hmem
        subst hmem; simp

theorem headPrimePrimes47Defect_aux_bounds :
    (∀ p ∈ ({2, 3, 5, 11} : Finset ℕ),
      headPrimePrimes47Defect p = headPrimeEnvelope37Defect p) ∧
    (∀ p ∈ headPrimes47Target, ∀ q ∈ tailEnvelopePrimes47,
      (headRowEnvelope p q).card = 11) ∧
    (∀ p ∈ headPrimes47Target,
      headPrimePrimes47Defect p ≤ 2 * headCardLam p + headMinMissingPairSlack p) ∧
    (∀ p ∈ ({7, 13, 17} : Finset ℕ),
      headPrimePrimes47Defect p ≤ headCardLam p + headMinMissingPairSlack p) ∧
    (∀ p ∈ ({19, 23, 29} : Finset ℕ),
      headPrimePrimes47Defect p ≤
        headCardLam p + headMinMissingPairSlack p +
          (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ))) ∧
    (∀ p ∈ headPrimes47Target,
      headPrimePrimes47Defect p ≤
        (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 53 : ℚ))) ∧
    (∀ p ∈ headPrimes47Target,
      headPrimePrimes47Defect p ≤
        (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ)) +
          (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 41 : ℚ)) +
          headMinMissingPairSlack p) ∧
    (∀ p ∈ headPrimes47Target, ∀ q ∈ tailEnvelopePrimes47, ∀ x ∈ headRowEnvelope p q,
      PrimeRowAdmissible p ((headRowEnvelope p q).erase x) →
        headPrimePrimes47Defect p ≤ headRowCapacityDefect p ((headRowEnvelope p q).erase x)) := by
  decide +kernel

theorem headPrimePrimes47Defect_le_headRowCapacityDefect
    {p : ℕ} {S : Finset ℕ} (hp : p ∈ headPrimes29) (hpS : p ∉ S)
    (hcard : S.card ≤ 10) (hprime : ∀ q ∈ S, q.Prime)
    (hadm : PrimeRowAdmissible p S) :
    headPrimePrimes47Defect p ≤ headRowCapacityDefect p S := by
  by_cases hp_base : p ∈ ({2, 3, 5, 11} : Finset ℕ)
  · rw [headPrimePrimes47Defect_aux_bounds.1 p hp_base]
    exact headPrimeEnvelope37Defect_le_headRowCapacityDefect hp hpS hcard hprime hadm
  · have hp_tgt : p ∈ headPrimes47Target := by
      have h : ∀ x ∈ headPrimes29, x ∉ ({2, 3, 5, 11} : Finset ℕ) → x ∈ headPrimes47Target := by
        decide
      exact h p hp hp_base
    have hp_def3 : p ∈ headDefectPrimes29.erase 3 := by
      have h : ∀ x ∈ headPrimes47Target, x ∈ headDefectPrimes29.erase 3 := by decide
      exact h p hp_tgt
    by_cases hc8 : S.card ≤ 8
    · have hnot_sub := not_headPrimes29_erase_subset_of_card_le_nine hp_def3 (by omega) hadm
      have hmiss := headMinMissingPairSlack_le_headRowMissingPairSlack_of_not_subset hp hnot_sub
      have h2 : (2 : ℚ) ≤ (10 : ℚ) - (S.card : ℚ) := by
        have hc8_q : (S.card : ℚ) ≤ 8 := by exact_mod_cast hc8
        linarith
      have hdeg : 2 * headCardLam p ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
        nlinarith [headCardLam_nonneg p]
      have haux := headPrimePrimes47Defect_aux_bounds.2.2.1 p hp_tgt
      unfold headRowCapacityDefect headRowAdmissibilityDefect
      linarith [headRowTailSlack_nonneg (p := p) hprime]
    · by_cases hc9 : S.card = 9
      · have hnot_sub := not_headPrimes29_erase_subset_of_card_le_nine hp_def3 (by omega) hadm
        have hmiss := headMinMissingPairSlack_le_headRowMissingPairSlack_of_not_subset hp hnot_sub
        have hdeg : headCardLam p = ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
          rw [hc9]; ring
        by_cases hp_small : p ∈ ({7, 13, 17} : Finset ℕ)
        · have haux := headPrimePrimes47Defect_aux_bounds.2.2.2.1 p hp_small
          unfold headRowCapacityDefect headRowAdmissibilityDefect
          linarith [headRowTailSlack_nonneg (p := p) hprime]
        · have hp_large : p ∈ ({19, 23, 29} : Finset ℕ) := by
            have h : ∀ x ∈ headPrimes47Target,
                x ∉ ({7, 13, 17} : Finset ℕ) → x ∈ ({19, 23, 29} : Finset ℕ) := by decide
            exact h p hp_tgt hp_small
          have hnot_sub31 : ¬ S ⊆ headRowCandidate31 p := by
            intro hsub31
            obtain ⟨x, hx, hS_eq⟩ := exists_erase_of_subset_of_card_eq_nine_of_card_eq_ten
              hsub31 hc9 (card_headRowCandidate31 hp)
            exact not_primeRowAdmissible_headRowCandidate31_erase_of_ge_nineteen hp_large
              x hx (hS_eq ▸ hadm)
          obtain ⟨q, hq, hne31⟩ :=
            exists_tail_neighbor_ne_thirty_one_of_not_subset_headRowCandidate31 hpS hnot_sub31
          rcases Finset.mem_sdiff.mp hq with ⟨hqS, hqnotH⟩
          have hge37 : 37 ≤ q :=
            prime_ge_thirty_seven_of_not_mem_headPrimes29_ne_thirty_one
              (hprime q hqS) hqnotH hne31
          have hinv37 : (1 : ℚ) / (q : ℚ) ≤ (1 / 37 : ℚ) :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge37)
          have hp_pos : (0 : ℚ) ≤ (1 : ℚ) / (p : ℚ) := by positivity
          have hterm :
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ)) ≤
                (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) :=
            mul_le_mul_of_nonneg_left (by linarith) hp_pos
          have hsingle :
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) ≤ headRowTailSlack p S := by
            unfold headRowTailSlack
            apply Finset.single_le_sum (fun r hr => ?_) hq
            rcases Finset.mem_sdiff.mp hr with ⟨hrS, hrnot⟩
            have hge31 : 31 ≤ r := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime r hrS) hrnot
            have hinv31 : (1 : ℚ) / (r : ℚ) ≤ (1 / 31 : ℚ) :=
              one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
            exact mul_nonneg hp_pos (sub_nonneg.mpr hinv31)
          have haux := headPrimePrimes47Defect_aux_bounds.2.2.2.2.1 p hp_large
          unfold headRowCapacityDefect headRowAdmissibilityDefect
          linarith
      · have hc10 : S.card = 10 := by omega
        have hdeg0 : (0 : ℚ) ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam p := by
          rw [hc10]; norm_num
        by_cases hsubT : (S \ headPrimes29).erase 31 ⊆ tailEnvelopePrimes47
        · by_cases hcard1 : ((S \ headPrimes29).erase 31).card ≤ 1
          · obtain ⟨q, hqT, hsub_env⟩ :=
              exists_headRowEnvelope_of_sdiff_erase_card_le_one hpS hsubT hcard1
            have hU11 := headPrimePrimes47Defect_aux_bounds.2.1 p hp_tgt q hqT
            obtain ⟨x, hx, rfl⟩ :=
              exists_erase_of_subset_of_card_eq_ten_of_card_eq_eleven hsub_env hc10 hU11
            exact headPrimePrimes47Defect_aux_bounds.2.2.2.2.2.2.2 p hp_tgt q hqT x hx hadm
          · obtain ⟨q₁, hq₁, q₂, hq₂, hlt12⟩ :=
              ordered_pair_of_two_le_card ((S \ headPrimes29).erase 31) (by omega)
            rcases Finset.mem_erase.mp hq₁ with ⟨hne31_1, hq₁_sd⟩
            rcases Finset.mem_erase.mp hq₂ with ⟨_, hq₂_sd⟩
            rcases Finset.mem_sdiff.mp hq₁_sd with ⟨hq₁S, hq₁notH⟩
            rcases Finset.mem_sdiff.mp hq₂_sd with ⟨hq₂S, _⟩
            have hge37 : 37 ≤ q₁ :=
              prime_ge_thirty_seven_of_not_mem_headPrimes29_ne_thirty_one
                (hprime q₁ hq₁S) hq₁notH hne31_1
            have hge41 : 41 ≤ q₂ :=
              prime_gt_thirty_seven_ge_forty_one (hprime q₂ hq₂S) (by omega)
            have hinv37 : (1 : ℚ) / (q₁ : ℚ) ≤ (1 / 37 : ℚ) :=
              one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge37)
            have hinv41 : (1 : ℚ) / (q₂ : ℚ) ≤ (1 / 41 : ℚ) :=
              one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge41)
            have hp_pos : (0 : ℚ) ≤ (1 : ℚ) / (p : ℚ) := by positivity
            have hterm1 :
                (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 37 : ℚ)) ≤
                  (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q₁ : ℚ)) :=
              mul_le_mul_of_nonneg_left (by linarith) hp_pos
            have hterm2 :
                (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 41 : ℚ)) ≤
                  (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q₂ : ℚ)) :=
              mul_le_mul_of_nonneg_left (by linarith) hp_pos
            have hpair := pair_le_headRowTailSlack (p := p) hprime hq₁_sd hq₂_sd (ne_of_lt hlt12)
            have hnot_sub := not_headPrimes29_erase_subset_of_two_tail_neighbors
              hp hcard hq₁_sd hq₂_sd (ne_of_lt hlt12)
            have hmiss := headMinMissingPairSlack_le_headRowMissingPairSlack_of_not_subset hp hnot_sub
            have haux := headPrimePrimes47Defect_aux_bounds.2.2.2.2.2.2.1 p hp_tgt
            unfold headRowCapacityDefect headRowAdmissibilityDefect
            linarith
        · obtain ⟨q, hq_erase, hqnotT⟩ := Finset.not_subset.mp hsubT
          rcases Finset.mem_erase.mp hq_erase with ⟨hne31, hq_sd⟩
          rcases Finset.mem_sdiff.mp hq_sd with ⟨hqS, hqnotH⟩
          have hge53 : 53 ≤ q :=
            prime_ge_fifty_three_of_not_mem_headPrimes29_ne_thirty_one_not_mem_tailEnvelopePrimes47
              (hprime q hqS) hqnotH hne31 hqnotT
          have hinv53 : (1 : ℚ) / (q : ℚ) ≤ (1 / 53 : ℚ) :=
            one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge53)
          have hp_pos : (0 : ℚ) ≤ (1 : ℚ) / (p : ℚ) := by positivity
          have hterm :
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 / 53 : ℚ)) ≤
                (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) :=
            mul_le_mul_of_nonneg_left (by linarith) hp_pos
          have hsingle :
              (1 : ℚ) / (p : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) ≤ headRowTailSlack p S := by
            unfold headRowTailSlack
            apply Finset.single_le_sum (fun r hr => ?_) hq_sd
            rcases Finset.mem_sdiff.mp hr with ⟨hrS, hrnot⟩
            have hge31 : 31 ≤ r := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime r hrS) hrnot
            have hinv31 : (1 : ℚ) / (r : ℚ) ≤ (1 / 31 : ℚ) :=
              one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
            exact mul_nonneg hp_pos (sub_nonneg.mpr hinv31)
          have haux := headPrimePrimes47Defect_aux_bounds.2.2.2.2.2.1 p hp_tgt
          unfold headRowCapacityDefect headRowAdmissibilityDefect
          linarith [headRowMissingPairSlack_nonneg p S]

theorem prime_edges_card_ge_sixty_one_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    61 ≤ E.card := by
  have hE_lt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hsum_div : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = ((1 : ℤ) : ℚ) / ((1 : ℕ) : ℚ) := by
    simpa using hsum
  have hcap := constant_tail_capacity_with_full_row_defect E hE
  have hdef_sum :
      (∑ p ∈ headPrimes29, headPrimePrimes47Defect p) ≤
        ∑ p ∈ headPrimes29, headRowCapacityDefect p (graphNeighbors E p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp_prime : p.Prime := by decide +revert
    have hpS : p ∉ graphNeighbors E p := not_mem_graphNeighbors_self E hE_lt p
    have hcard : (graphNeighbors E p).card ≤ 10 := by
      rw [card_graphNeighbors_eq_incidenceDegree E hE_lt p]
      exact hdeg p hp_prime
    have hprime : ∀ q ∈ graphNeighbors E p, q.Prime := by
      intro q hq
      rcases (mem_graphNeighbors_iff E p q).mp hq with he | he
      · exact (hE (p, q) he).2.1
      · exact (hE (q, p) he).1
    have hadm : PrimeRowAdmissible p (graphNeighbors E p) :=
      (prime_graph_row_admissible_of_sum_eq_div E p 1 1 hE hp_prime (by decide) (Nat.coprime_one_right p) hsum_div).1
    exact headPrimePrimes47Defect_le_headRowCapacityDefect hp hpS hcard hprime hadm
  have hconst :
      (10 : ℚ) * (∑ p ∈ headPrimes29, headCardLam p) +
        (∑ e ∈ headPairs29, headCardSlack e) -
        (∑ p ∈ headPrimes29, headPrimePrimes47Defect p) +
        60 * ((1 / 31 : ℚ) ^ 2) < 1 := by
    decide +kernel
  have hlt : (60 : ℚ) < (E.card : ℚ) := by
    by_contra hle
    have hle' : (E.card : ℚ) ≤ 60 := not_lt.mp hle
    have hmul : ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) ≤ 60 * ((1 / 31 : ℚ) ^ 2) := by linarith
    linarith
  have hlt_nat : 60 < E.card := by exact_mod_cast hlt
  omega

theorem prime_edges_card_ge_sixty_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    60 ≤ E.card :=
  le_trans (by decide : 60 ≤ 61) (prime_edges_card_ge_sixty_one_of_sum_eq_one E hE hdeg hsum)

theorem semiprime_set_card_ge_sixty_one_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    61 ≤ S.card := by
  obtain ⟨E, hE, hprod⟩ := Erdos306.PrimeIncidence.semiprime_set_is_prime_edge_image S hS
  have hcard : S.card = E.card := by
    rw [← hprod, Finset.card_image_of_injOn (Erdos306.Representation.product_injOn_prime_edges E hE)]
  have hdegE : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10 := by
    intro p hp
    have hcount := Erdos306.Representation.degree_eq_divisible_denominators E hE p hp
    change incidenceDegree E p = _ at hcount
    rw [hprod] at hcount
    rw [hcount]
    exact hdeg p hp
  have hsumImage := Erdos306.Representation.reciprocal_sum_image_prime_edges E hE
  rw [hprod] at hsumImage
  have hsumE : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 := by
    have hcast :
        (∑ e ∈ E, (1 : ℚ) / (e.1 * e.2 : ℕ)) =
          ∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro e _
      push_cast
      rfl
    rw [← hcast, ← hsumImage]
    exact hsum
  rw [hcard]
  exact prime_edges_card_ge_sixty_one_of_sum_eq_one E hE hdegE hsumE

theorem semiprime_set_card_ge_sixty_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) :
    60 ≤ S.card :=
  le_trans (by decide : 60 ≤ 61) (semiprime_set_card_ge_sixty_one_of_sum_eq_one S hS hdeg hsum)

/-! ## Part 3: Universal Mod-4 Parity at Prime `2`, Odd-Cardinality Bounds (`|E| ≥ 63`), and Three-Tail Cell `111` Witnesses (`|E| = 71, 72, 73`) -/

def oddVertices (E : Finset (ℕ × ℕ)) : Finset ℕ :=
  ((E.image Prod.fst) ∪ (E.image Prod.snd)).erase 2

def oddPrimeProd (E : Finset (ℕ × ℕ)) : ℕ :=
  ∏ p ∈ oddVertices E, p

theorem odd_of_mem_oddVertices {E : Finset (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    {p : ℕ} (hp : p ∈ oddVertices E) : p.Prime ∧ p % 2 = 1 := by
  rcases Finset.mem_erase.mp hp with ⟨hne2, hmem⟩
  have hpr : p.Prime := by
    rcases Finset.mem_union.mp hmem with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨e, he, rfl⟩
      exact (hE e he).1
    · rcases Finset.mem_image.mp h2 with ⟨e, he, rfl⟩
      exact (hE e he).2.1
  exact ⟨hpr, hpr.eq_two_or_odd.resolve_left hne2⟩

theorem prod_mod_two_eq_one_of_forall_odd (S : Finset ℕ) (hall : ∀ p ∈ S, p % 2 = 1) :
    (∏ p ∈ S, p) % 2 = 1 := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.mul_mod,
      hall a (Finset.mem_insert_self a s),
      ih (fun _p hp => hall _p (Finset.mem_insert_of_mem hp))]

theorem oddPrimeProd_mod_two {E : Finset (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    oddPrimeProd E % 2 = 1 :=
  prod_mod_two_eq_one_of_forall_odd (oddVertices E)
    (fun p hp => (odd_of_mem_oddVertices hE hp).2)

theorem snd_mem_oddVertices_of_mem {E : Finset (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    {e : ℕ × ℕ} (he : e ∈ E) : e.2 ∈ oddVertices E := by
  have h1 : 2 ≤ e.1 := (hE e he).1.two_le
  have hlt : e.1 < e.2 := (hE e he).2.2
  refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))

theorem fst_mem_oddVertices_of_mem_of_ne_two {E : Finset (ℕ × ℕ)}
    {e : ℕ × ℕ} (he : e ∈ E) (hne : e.1 ≠ 2) : e.1 ∈ oddVertices E := by
  refine Finset.mem_erase.mpr ⟨hne, ?_⟩
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨e, he, rfl⟩))

theorem snd_dvd_oddPrimeProd_of_mem {E : Finset (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    {e : ℕ × ℕ} (he : e ∈ E) : e.2 ∣ oddPrimeProd E :=
  Finset.dvd_prod_of_mem _ (snd_mem_oddVertices_of_mem hE he)

theorem mul_dvd_oddPrimeProd_of_mem_of_ne_two {E : Finset (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    {e : ℕ × ℕ} (he : e ∈ E) (hne : e.1 ≠ 2) : e.1 * e.2 ∣ oddPrimeProd E := by
  have hlt : e.1 < e.2 := (hE e he).2.2
  have hpair : ∏ p ∈ ({e.1, e.2} : Finset ℕ), p = e.1 * e.2 :=
    Finset.prod_pair (ne_of_lt hlt)
  rw [← hpair]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact fst_mem_oddVertices_of_mem_of_ne_two he hne
  · exact snd_mem_oddVertices_of_mem hE he

theorem odd_sq_mod_four {m : ℕ} (hm : m % 2 = 1) : (m * m) % 4 = 1 := by
  have h : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h with h1 | h3
  · rw [Nat.mul_mod, h1]
  · rw [Nat.mul_mod, h3]

theorem mul_div_mod_four_eq_of_dvd_odd {M q : ℕ} (hM : M % 2 = 1) (hdvd : q ∣ M) :
    (M * (M / q)) % 4 = q % 4 := by
  rcases hdvd with ⟨m, rfl⟩
  have hq0 : 0 < q := by
    by_contra h0
    have hq_eq : q = 0 := by omega
    subst hq_eq
    simp at hM
  rw [Nat.mul_div_cancel_left m hq0]
  have hm : m % 2 = 1 := by
    by_contra hm0
    have hm_even : m % 2 = 0 := by omega
    rw [Nat.mul_mod, hm_even, mul_zero, Nat.zero_mod] at hM
    omega
  calc
    (q * m * m) % 4 = (q * (m * m)) % 4 := by rw [mul_assoc]
    _ = ((q % 4) * ((m * m) % 4)) % 4 := by rw [Nat.mul_mod]
    _ = ((q % 4) * 1) % 4 := by rw [odd_sq_mod_four hm]
    _ = q % 4 := by simp [Nat.mod_mod]

theorem two_mul_mul_div_mod_four_eq_two_of_dvd_odd {M d : ℕ} (hM : M % 2 = 1) (hdvd : d ∣ M) :
    (M * (2 * (M / d))) % 4 = 2 := by
  rcases hdvd with ⟨m, rfl⟩
  have hd0 : 0 < d := by
    by_contra h0
    have hd_eq : d = 0 := by omega
    subst hd_eq
    simp at hM
  rw [Nat.mul_div_cancel_left m hd0]
  have hdm : (d * m) % 2 = 1 := hM
  have hm : m % 2 = 1 := by
    by_contra hm0
    have hm_even : m % 2 = 0 := by omega
    rw [Nat.mul_mod, hm_even, mul_zero, Nat.zero_mod] at hM
    omega
  have hprod_odd : (d * m * m) % 2 = 1 := by
    rw [Nat.mul_mod, hdm, hm]
  have hrew : d * m * (2 * m) = 2 * (d * m * m) := by ring
  rw [hrew]
  omega

theorem cleared_nat_sum_eq_of_sum_edges_inv_eq_one
    (E : Finset (ℕ × ℕ)) (M : ℕ) (hM0 : M ≠ 0)
    (hdvd : ∀ e ∈ E, e.1 * e.2 ∣ M)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    (∑ e ∈ E, M / (e.1 * e.2)) = M := by
  have hM_q : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM0
  have hterm : ∀ e ∈ E,
      (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) = ((M / (e.1 * e.2) : ℕ) : ℚ) / (M : ℚ) := by
    intro e he
    have hmul : (e.1 * e.2) * (M / (e.1 * e.2)) = M := Nat.mul_div_cancel' (hdvd e he)
    have hprod0 : e.1 * e.2 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      exact hM0 hmul.symm
    have hprod_q : ((e.1 : ℚ) * (e.2 : ℚ)) ≠ 0 := by exact_mod_cast hprod0
    have hmul_q : ((e.1 : ℚ) * (e.2 : ℚ)) * ((M / (e.1 * e.2) : ℕ) : ℚ) = (M : ℚ) := by
      exact_mod_cast hmul
    rw [div_eq_div_iff hprod_q hM_q, one_mul, mul_comm, hmul_q]
  have hdiv : ((∑ e ∈ E, M / (e.1 * e.2) : ℕ) : ℚ) / (M : ℚ) = 1 := by
    rw [Nat.cast_sum, Finset.sum_div, ← Finset.sum_congr rfl hterm, hsum]
  have hcast : ((∑ e ∈ E, M / (e.1 * e.2) : ℕ) : ℚ) = (M : ℚ) :=
    (div_eq_one_iff_eq hM_q).mp hdiv
  exact Nat.cast_inj.mp hcast

theorem leftNeighbors_two_eq_empty (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    leftNeighbors E 2 = ∅ := by
  ext q
  simp only [leftNeighbors, Finset.mem_image, Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨e, ⟨he, he2⟩, rfl⟩
  have h1 := (hE e he).1.two_le
  have hlt := (hE e he).2.2
  omega

theorem graphNeighbors_two_eq_rightNeighbors (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    graphNeighbors E 2 = rightNeighbors E 2 := by
  rw [graphNeighbors, leftNeighbors_two_eq_empty E hE, Finset.union_empty]

theorem filter_snd_eq_two_eq_empty (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    E.filter (fun e => e.2 = 2) = ∅ := by
  ext e
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro he he2
  have h1 := (hE e he).1.two_le
  have hlt := (hE e he).2.2
  omega

theorem card_filter_fst_eq_two_eq_incidenceDegree_two (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    (E.filter (fun e => e.1 = 2)).card = incidenceDegree E 2 := by
  unfold incidenceDegree
  rw [filter_snd_eq_two_eq_empty E hE, Finset.card_empty, add_zero]

theorem sum_graphNeighbors_two_add_two_mul_card_mod_four_eq_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    ((∑ q ∈ graphNeighbors E 2, q) + 2 * E.card) % 4 = 2 := by
  set M := oddPrimeProd E
  have hM_odd : M % 2 = 1 := oddPrimeProd_mod_two hE
  have h2M_ne : 2 * M ≠ 0 := by omega
  have hdvd_2M : ∀ e ∈ E, e.1 * e.2 ∣ 2 * M := by
    intro e he
    by_cases h2 : e.1 = 2
    · rw [h2]
      exact mul_dvd_mul_left 2 (snd_dvd_oddPrimeProd_of_mem hE he)
    · exact dvd_mul_of_dvd_right (mul_dvd_oddPrimeProd_of_mem_of_ne_two hE he h2) 2
  have hcleared := cleared_nat_sum_eq_of_sum_edges_inv_eq_one E (2 * M) h2M_ne hdvd_2M hsum
  have hsplit := (Finset.sum_filter_add_sum_filter_not E (fun e => e.1 = 2)
    (fun e => (2 * M) / (e.1 * e.2))).symm
  rw [hcleared] at hsplit
  have heven_sum :
      (∑ e ∈ E.filter (fun e => e.1 = 2), (2 * M) / (e.1 * e.2)) =
        ∑ q ∈ graphNeighbors E 2, M / q := by
    rw [graphNeighbors_two_eq_rightNeighbors E hE, rightNeighbors,
      Finset.sum_image (injOn_snd_filter_fst E 2)]
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2, Nat.mul_div_mul_left M e.2 (by decide)]
  have hodd_sum :
      (∑ e ∈ E.filter (fun e => ¬ e.1 = 2), (2 * M) / (e.1 * e.2)) =
        ∑ e ∈ E.filter (fun e => ¬ e.1 = 2), 2 * (M / (e.1 * e.2)) := by
    apply Finset.sum_congr rfl
    intro e he
    rcases Finset.mem_filter.mp he with ⟨heE, hne2⟩
    exact Nat.mul_div_assoc 2 (mul_dvd_oddPrimeProd_of_mem_of_ne_two hE heE hne2)
  rw [heven_sum, hodd_sum] at hsplit
  have hmul_eq :
      (M * (∑ q ∈ graphNeighbors E 2, M / q) +
        M * (∑ e ∈ E.filter (fun e => ¬ e.1 = 2), 2 * (M / (e.1 * e.2)))) % 4 =
        (M * (2 * M)) % 4 := by
    rw [← mul_add, ← hsplit]
  have hrhs : (M * (2 * M)) % 4 = 2 := by
    calc
      (M * (2 * M)) % 4 = (2 * (M * M)) % 4 := by ring_nf
      _ = ((2 % 4) * ((M * M) % 4)) % 4 := by rw [Nat.mul_mod]
      _ = 2 := by rw [odd_sq_mod_four hM_odd]
  have hterm1 :
      (M * (∑ q ∈ graphNeighbors E 2, M / q)) % 4 =
        (∑ q ∈ graphNeighbors E 2, q) % 4 := by
    rw [Finset.mul_sum, Finset.sum_nat_mod, Finset.sum_nat_mod (s := graphNeighbors E 2) (f := fun q => q)]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    rw [graphNeighbors_two_eq_rightNeighbors E hE] at hq
    rcases Finset.mem_image.mp hq with ⟨e, he_filt, rfl⟩
    have hdvd_q := snd_dvd_oddPrimeProd_of_mem hE (Finset.mem_filter.mp he_filt).1
    exact mul_div_mod_four_eq_of_dvd_odd hM_odd hdvd_q
  have hterm2 :
      (M * (∑ e ∈ E.filter (fun e => ¬ e.1 = 2), 2 * (M / (e.1 * e.2)))) % 4 =
        (2 * (E.filter (fun e => ¬ e.1 = 2)).card) % 4 := by
    rw [Finset.mul_sum, Finset.sum_nat_mod]
    have hcongr :
        (∑ e ∈ E.filter (fun e => ¬ e.1 = 2), (M * (2 * (M / (e.1 * e.2)))) % 4) =
          ∑ _e ∈ E.filter (fun e => ¬ e.1 = 2), 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rcases Finset.mem_filter.mp he with ⟨heE, hne2⟩
      exact two_mul_mul_div_mod_four_eq_two_of_dvd_odd hM_odd
        (mul_dvd_oddPrimeProd_of_mem_of_ne_two hE heE hne2)
    rw [hcongr, Finset.sum_const, smul_eq_mul, mul_comm]
  have hdeg2_even : 2 ∣ (E.filter (fun e => e.1 = 2)).card := by
    rw [card_filter_fst_eq_two_eq_incidenceDegree_two E hE]
    exact two_dvd_incidenceDegree_two_of_prime_graph E 1 1 hE (by decide) (by decide)
      (by simpa using hsum)
  have hcard_split := Finset.card_filter_add_card_filter_not (s := E) (p := fun e => e.1 = 2)
  rcases hdeg2_even with ⟨k2, hk2⟩
  have hcard_mod : (2 * (E.filter (fun e => ¬ e.1 = 2)).card) % 4 = (2 * E.card) % 4 := by
    omega
  rw [Nat.add_mod, hterm1, hterm2, hcard_mod, ← Nat.add_mod, hrhs] at hmul_eq
  exact hmul_eq

theorem sum_odd_mod_two_eq_card_mod_two (S : Finset ℕ) (hall : ∀ q ∈ S, q % 2 = 1) :
    (∑ q ∈ S, q) % 2 = S.card % 2 := by
  rw [Finset.sum_nat_mod]
  have hcongr : (∑ q ∈ S, q % 2) = ∑ _q ∈ S, 1 := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hall q hq
  rw [hcongr, Finset.sum_const, smul_eq_mul, mul_one]

theorem even_card_iff_sum_graphNeighbors_two_mod_four_eq_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    2 ∣ E.card ↔ (∑ q ∈ graphNeighbors E 2, q) % 4 = 2 := by
  have hmod4 := sum_graphNeighbors_two_add_two_mul_card_mod_four_eq_two E hE hsum
  have hE_lt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hdeg2_even : 2 ∣ (graphNeighbors E 2).card := by
    rw [card_graphNeighbors_eq_incidenceDegree E hE_lt 2]
    exact two_dvd_incidenceDegree_two_of_prime_graph E 1 1 hE (by decide) (by decide)
      (by simpa using hsum)
  have hall_odd : ∀ q ∈ graphNeighbors E 2, q % 2 = 1 := by
    intro q hq
    rw [graphNeighbors_two_eq_rightNeighbors E hE] at hq
    rcases Finset.mem_image.mp hq with ⟨e, he_filt, rfl⟩
    exact (odd_of_mem_oddVertices hE
      (snd_mem_oddVertices_of_mem hE (Finset.mem_filter.mp he_filt).1)).2
  have hsum_even : (∑ q ∈ graphNeighbors E 2, q) % 2 = 0 := by
    rw [sum_odd_mod_two_eq_card_mod_two (graphNeighbors E 2) hall_odd]
    exact Nat.mod_eq_zero_of_dvd hdeg2_even
  omega

theorem odd_card_iff_four_dvd_sum_graphNeighbors_two
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) :
    ¬ 2 ∣ E.card ↔ 4 ∣ ∑ q ∈ graphNeighbors E 2, q := by
  have hmod4 := sum_graphNeighbors_two_add_two_mul_card_mod_four_eq_two E hE hsum
  have hE_lt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hdeg2_even : 2 ∣ (graphNeighbors E 2).card := by
    rw [card_graphNeighbors_eq_incidenceDegree E hE_lt 2]
    exact two_dvd_incidenceDegree_two_of_prime_graph E 1 1 hE (by decide) (by decide)
      (by simpa using hsum)
  have hall_odd : ∀ q ∈ graphNeighbors E 2, q % 2 = 1 := by
    intro q hq
    rw [graphNeighbors_two_eq_rightNeighbors E hE] at hq
    rcases Finset.mem_image.mp hq with ⟨e, he_filt, rfl⟩
    exact (odd_of_mem_oddVertices hE
      (snd_mem_oddVertices_of_mem hE (Finset.mem_filter.mp he_filt).1)).2
  have hsum_even : (∑ q ∈ graphNeighbors E 2, q) % 2 = 0 := by
    rw [sum_odd_mod_two_eq_card_mod_two (graphNeighbors E 2) hall_odd]
    exact Nat.mod_eq_zero_of_dvd hdeg2_even
  omega

theorem graphNeighbors_two_ne_headRowCandidate31_of_odd_card
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1)
    (hodd : ¬ 2 ∣ E.card) :
    graphNeighbors E 2 ≠ headRowCandidate31 2 := by
  intro heq
  have hdvd4 := (odd_card_iff_four_dvd_sum_graphNeighbors_two E hE hsum).mp hodd
  rw [heq] at hdvd4
  have hnot : ¬ 4 ∣ ∑ q ∈ headRowCandidate31 2, q := by decide
  exact hnot hdvd4

def headPrimeOddCardDefect (p : ℕ) : ℚ :=
  if p = 2 then 3 / 1147 else headPrimePrimes47Defect p

theorem headPrimeOddCardDefect_le_two
    {S : Finset ℕ} (h2S : 2 ∉ S) (hcard : S.card ≤ 10)
    (hprime : ∀ q ∈ S, q.Prime) (hne : S ≠ headRowCandidate31 2) :
    (3 / 1147 : ℚ) ≤ headRowCapacityDefect 2 S := by
  by_cases hc9 : S.card ≤ 9
  · have h1 : (1 : ℚ) ≤ (10 : ℚ) - (S.card : ℚ) := by
      have hc9_q : (S.card : ℚ) ≤ 9 := by exact_mod_cast hc9
      linarith
    have hdeg : headCardLam 2 ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam 2 := by
      nlinarith [headCardLam_nonneg 2]
    have hval : (3 / 1147 : ℚ) ≤ headCardLam 2 := by decide +kernel
    unfold headRowCapacityDefect headRowAdmissibilityDefect
    linarith [headRowTailSlack_nonneg (p := 2) hprime, headRowMissingPairSlack_nonneg 2 S]
  · have hc10 : S.card = 10 := by omega
    obtain ⟨q, hq, hne31⟩ :=
      exists_tail_neighbor_ne_thirty_one_of_card_eq_ten_ne_candidate (by decide) h2S hc10 hne
    rcases Finset.mem_sdiff.mp hq with ⟨hqS, hqnotH⟩
    have hge37 : 37 ≤ q :=
      prime_ge_thirty_seven_of_not_mem_headPrimes29_ne_thirty_one (hprime q hqS) hqnotH hne31
    have hinv37 : (1 : ℚ) / (q : ℚ) ≤ (1 / 37 : ℚ) :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge37)
    have hterm :
        (3 / 1147 : ℚ) ≤ (1 : ℚ) / (2 : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) := by
      linarith
    have hsingle :
        (1 : ℚ) / (2 : ℚ) * ((1 / 31 : ℚ) - (1 : ℚ) / (q : ℚ)) ≤ headRowTailSlack 2 S := by
      unfold headRowTailSlack
      apply Finset.single_le_sum (fun r hr => ?_) hq
      rcases Finset.mem_sdiff.mp hr with ⟨hrS, hrnot⟩
      have hge31 : 31 ≤ r := prime_ge_thirty_one_of_not_mem_headPrimes29 (hprime r hrS) hrnot
      have hinv31 : (1 : ℚ) / (r : ℚ) ≤ (1 / 31 : ℚ) :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge31)
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hinv31)
    have hdeg0 : (0 : ℚ) ≤ ((10 : ℚ) - (S.card : ℚ)) * headCardLam 2 := by
      rw [hc10]; norm_num
    unfold headRowCapacityDefect headRowAdmissibilityDefect
    linarith [headRowMissingPairSlack_nonneg 2 S]

theorem prime_edges_card_ge_sixty_three_of_odd_card_of_sum_eq_one
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1)
    (hodd : ¬ 2 ∣ E.card) :
    63 ≤ E.card := by
  have hE_lt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hsum_div : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = ((1 : ℤ) : ℚ) / ((1 : ℕ) : ℚ) := by
    simpa using hsum
  have hcap := constant_tail_capacity_with_full_row_defect E hE
  have hdef_sum :
      (∑ p ∈ headPrimes29, headPrimeOddCardDefect p) ≤
        ∑ p ∈ headPrimes29, headRowCapacityDefect p (graphNeighbors E p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp_prime : p.Prime := by decide +revert
    have hpS : p ∉ graphNeighbors E p := not_mem_graphNeighbors_self E hE_lt p
    have hcard : (graphNeighbors E p).card ≤ 10 := by
      rw [card_graphNeighbors_eq_incidenceDegree E hE_lt p]
      exact hdeg p hp_prime
    have hprime : ∀ q ∈ graphNeighbors E p, q.Prime := by
      intro q hq
      rcases (mem_graphNeighbors_iff E p q).mp hq with he | he
      · exact (hE (p, q) he).2.1
      · exact (hE (q, p) he).1
    have hadm : PrimeRowAdmissible p (graphNeighbors E p) :=
      (prime_graph_row_admissible_of_sum_eq_div E p 1 1 hE hp_prime (by decide) (Nat.coprime_one_right p) hsum_div).1
    unfold headPrimeOddCardDefect
    split_ifs with h2
    · subst h2
      exact headPrimeOddCardDefect_le_two hpS hcard hprime
        (graphNeighbors_two_ne_headRowCandidate31_of_odd_card E hE hsum hodd)
    · exact headPrimePrimes47Defect_le_headRowCapacityDefect hp hpS hcard hprime hadm
  have hconst :
      (10 : ℚ) * (∑ p ∈ headPrimes29, headCardLam p) +
        (∑ e ∈ headPairs29, headCardSlack e) -
        (∑ p ∈ headPrimes29, headPrimeOddCardDefect p) +
        62 * ((1 / 31 : ℚ) ^ 2) < 1 := by
    decide +kernel
  have hlt : (62 : ℚ) < (E.card : ℚ) := by
    by_contra hle
    have hle' : (E.card : ℚ) ≤ 62 := not_lt.mp hle
    have hmul : ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) ≤ 62 * ((1 / 31 : ℚ) ^ 2) := by linarith
    linarith
  have hlt_nat : 62 < E.card := by exact_mod_cast hlt
  omega

theorem semiprime_set_card_ge_sixty_three_of_odd_card_of_sum_eq_one
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1)
    (hodd : ¬ 2 ∣ S.card) :
    63 ≤ S.card := by
  obtain ⟨E, hE, hprod⟩ := Erdos306.PrimeIncidence.semiprime_set_is_prime_edge_image S hS
  have hcard : S.card = E.card := by
    rw [← hprod, Finset.card_image_of_injOn (Erdos306.Representation.product_injOn_prime_edges E hE)]
  have hdegE : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10 := by
    intro p hp
    have hcount := Erdos306.Representation.degree_eq_divisible_denominators E hE p hp
    change incidenceDegree E p = _ at hcount
    rw [hprod] at hcount
    rw [hcount]
    exact hdeg p hp
  have hsumImage := Erdos306.Representation.reciprocal_sum_image_prime_edges E hE
  rw [hprod] at hsumImage
  have hsumE : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 := by
    have hcast :
        (∑ e ∈ E, (1 : ℚ) / (e.1 * e.2 : ℕ)) =
          ∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro e _
      push_cast
      rfl
    rw [← hcast, ← hsumImage]
    exact hsum
  rw [hcard] at hodd ⊢
  exact prime_edges_card_ge_sixty_three_of_odd_card_of_sum_eq_one E hE hdegE hsumE hodd

def witnessEdges71Cell111 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 37),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 29), (13, 37), (13, 43), (17, 19), (17, 23), (17, 43), (17, 53), (19, 29),
   (19, 41), (19, 43), (23, 29), (23, 31), (23, 41), (23, 43), (29, 31), (29, 41), (29, 43), (29, 61),
   (31, 41), (31, 43), (31, 59), (31, 61), (37, 41), (37, 53), (37, 59), (37, 61), (41, 61), (43, 59),
   (43, 61)}

def witnessEdges72Cell111 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 23), (13, 37), (13, 59), (17, 19), (17, 29), (17, 37), (17, 59), (19, 23),
   (19, 53), (23, 41), (23, 43), (23, 59), (29, 31), (29, 37), (29, 43), (29, 53), (29, 59), (29, 61),
   (31, 61), (37, 53), (37, 59), (37, 61), (41, 43), (41, 47), (41, 59), (41, 61), (43, 59), (43, 61),
   (47, 53), (53, 59)}

def witnessEdges73Cell111 : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 37),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37), (5, 7),
   (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31), (7, 11), (7, 13), (7, 17),
   (7, 19), (7, 23), (7, 29), (7, 53), (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 23), (13, 37), (13, 59), (17, 23), (17, 37), (17, 41), (17, 53), (19, 23),
   (19, 29), (19, 31), (19, 41), (23, 47), (23, 61), (29, 31), (29, 43), (29, 47), (29, 61), (31, 37),
   (31, 41), (31, 47), (31, 53), (31, 59), (37, 41), (37, 43), (37, 59), (41, 43), (41, 47), (41, 53),
   (43, 61), (53, 59), (59, 61)}

theorem witnessEdges71Cell111_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges71Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges71Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges71Cell111.card = 71 ∧
      ¬ 2 ∣ witnessEdges71Cell111.card ∧
      incidenceDegree witnessEdges71Cell111 47 = 0 ∧
      incidenceDegree witnessEdges71Cell111 53 = 3 ∧
      incidenceDegree witnessEdges71Cell111 59 = 3 ∧
      incidenceDegree witnessEdges71Cell111 61 = 5 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges71Cell111 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges71Cell111 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges71Cell111 (primorial47 * 53 * 59 * 61)
    (by decide) (by decide) (by decide)

theorem witnessEdges72Cell111_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges72Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges72Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges72Cell111.card = 72 ∧
      2 ∣ witnessEdges72Cell111.card ∧
      incidenceDegree witnessEdges72Cell111 53 = 6 ∧
      incidenceDegree witnessEdges72Cell111 59 = 8 ∧
      incidenceDegree witnessEdges72Cell111 61 = 5 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges72Cell111 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges72Cell111 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, by decide,
    fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges72Cell111 (primorial47 * 53 * 59 * 61)
    (by decide) (by decide) (by decide)

theorem witnessEdges73Cell111_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdges73Cell111,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdges73Cell111, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdges73Cell111.card = 73 ∧
      ¬ 2 ∣ witnessEdges73Cell111.card ∧
      incidenceDegree witnessEdges73Cell111 53 = 5 ∧
      incidenceDegree witnessEdges73Cell111 59 = 5 ∧
      incidenceDegree witnessEdges73Cell111 61 = 4 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdges73Cell111 p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdges73Cell111 p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, by decide,
    fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdges73Cell111 (primorial47 * 53 * 59 * 61)
    (by decide) (by decide) (by decide)

end Erdos306.PrimeResidueAndRowPotential

/-! ## Part 4: Direct Bridges to `FormalConjectures.ErdosProblems.306` (`erdos_306` and `erdos_306.variants.integer_three_primes`) -/

namespace Erdos306

open ArithmeticFunction Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

theorem omega_Omega_eq_three_of_three_distinct_primes
    {w v u : ℕ} (hw : w.Prime) (hv : v.Prime) (hu : u.Prime)
    (hwv : w ≠ v) (hwu : w ≠ u) (hvu : v ≠ u) :
    ω (w * (v * u)) = 3 ∧ Ω (w * (v * u)) = 3 ∧ 1 < w * (v * u) := by
  have hcop_vu : Nat.Coprime v u := (Nat.coprime_primes hv hu).2 hvu
  have hcop_wv : Nat.Coprime w v := (Nat.coprime_primes hw hv).2 hwv
  have hcop_wu : Nat.Coprime w u := (Nat.coprime_primes hw hu).2 hwu
  have hcop_w_vu : Nat.Coprime w (v * u) := hcop_wv.mul_right hcop_wu
  have hvu_ne : v * u ≠ 0 := mul_ne_zero hv.ne_zero hu.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [cardDistinctFactors_mul hcop_w_vu, cardDistinctFactors_mul hcop_vu,
      cardDistinctFactors_apply_prime hw, cardDistinctFactors_apply_prime hv,
      cardDistinctFactors_apply_prime hu]
  · rw [cardFactors_mul hw.ne_zero hvu_ne, cardFactors_mul hv.ne_zero hu.ne_zero,
      cardFactors_apply_prime hw, cardFactors_apply_prime hv, cardFactors_apply_prime hu]
  · have hvu_gt : 1 < v * u := one_lt_mul_of_lt_of_le hv.one_lt hu.one_lt.le
    exact one_lt_mul_of_lt_of_le hw.one_lt hvu_gt.le

theorem thm_small_avoiding_prime
    (τ : ℚ) (w : ℕ) (h0 : 0 < τ) (hη : τ ≤ 1 / 400) (hsq : Squarefree τ.den)
    (hw : w.Prime) (hw3 : 3 ≤ w) (hndvd : ¬ w ∣ τ.den) :
    ∃ y0 : ℕ, ∀ y ≥ y0, ∃ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧ p.1 ≤ 2 * y ^ 2 ∧ y ^ 8 < p.2 ∧ p.2 ≤ y ^ 9 ∧
        w ≠ p.1 ∧ w ≠ p.2) ∧
      ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2) = τ := by
  obtain ⟨y0, hy0⟩ := eventually_large h0
  refine ⟨max y0 w, fun y hy => ?_⟩
  have hy0' : y0 ≤ y := le_trans (le_max_left y0 w) hy
  have hwy : w ≤ y := le_trans (le_max_right y0 w) hy
  have hL : Large τ y := hy0 y hy0'
  obtain ⟨Y, hT⟩ := lem_tuning h0 hη hL
  obtain ⟨S, hSA, k, hk⟩ := prop_core hsq hL hT
  refine ⟨S, fun p hp => ?_, sigma_eq_of_congr h0 hη hT hSA k hk⟩
  have hpA := mem_Aset.1 (hSA hp)
  have hv := le_of_mem_Vset hL hpA.1
  have hu := bounds_of_mem_Uset hpA.2
  have hy3 : 3 ≤ y := hL.y_ge
  have hy2 : y < y ^ 2 := by nlinarith
  have hy8 : y ≤ y ^ 8 := Nat.le_self_pow (by norm_num) y
  have hwv : w ≠ p.1 := by
    intro heq
    subst heq
    rcases mem_Vset.1 hpA.1 with h2 | hB | hW
    · omega
    · exact hndvd (Nat.dvd_of_mem_primeFactors hB)
    · have hW1 := (mem_Wset.1 hW).1
      omega
  have hwu : w ≠ p.2 := by
    have := hu.1
    omega
  exact ⟨prime_of_mem_Vset hpA.1, prime_of_mem_Uset hpA.2, hv.2, hu.1, hu.2.trans hT.hi, hwv, hwu⟩

theorem integer_three_primes_finset (m : ℕ) (hm : 0 < m) :
    ∃ F : Finset ℕ,
      (∀ n ∈ F, ω n = 3 ∧ Ω n = 3 ∧ 1 < n) ∧
      (m : ℚ) = ∑ n ∈ F, (1 : ℚ) / (n : ℚ) := by
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (1200 * m + 5)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  set τ : ℚ := (3 * m : ℕ) * (p : ℚ)⁻¹ with hτ
  have h3m_pos : 0 < 3 * m := by omega
  have h3m_q : (0 : ℚ) < (3 * m : ℕ) := by exact_mod_cast h3m_pos
  have hτ0 : 0 < τ := by positivity
  have hτη : τ ≤ 1 / 400 := by
    rw [hτ, ← div_eq_mul_inv, div_le_iff₀ hp0]
    have : (1200 * m : ℚ) ≤ p := by exact_mod_cast (by omega : 1200 * m ≤ p)
    push_cast at this ⊢
    linarith
  have hden_dvd : τ.den ∣ p := by
    have h1 := Rat.mul_den_dvd ((3 * m : ℕ) : ℚ) ((p : ℚ)⁻¹)
    rwa [Rat.den_natCast, one_mul, Rat.inv_natCast_den, if_neg hp.ne_zero] at h1
  have hτsq : Squarefree τ.den :=
    Squarefree.squarefree_of_dvd hden_dvd hp.squarefree
  have hndvd3 : ¬ 3 ∣ τ.den := by
    intro hd3
    have h3p : 3 ∣ p := dvd_trans hd3 hden_dvd
    rcases hp.eq_one_or_self_of_dvd 3 h3p with h | h <;> omega
  obtain ⟨y0, hy0⟩ := thm_small_avoiding_prime τ 3 hτ0 hτη hτsq Nat.prime_three (by decide) hndvd3
  have key : ∀ j : ℕ, ∃ F : Finset ℕ,
      (∀ n ∈ F, ω n = 3 ∧ Ω n = 3 ∧ 1 < n) ∧
      ∑ n ∈ F, (1 : ℚ) / (n : ℚ) = (j : ℚ) * (τ / 3) := by
    intro j
    induction j with
    | zero => exact ⟨∅, by simp, by simp⟩
    | succ j ih =>
      obtain ⟨F, hF, hFsum⟩ := ih
      set y := max y0 (max (F.sup id + 1) 2)
      have hy0' : y0 ≤ y := le_max_left _ _
      have hyF : F.sup id + 1 ≤ y := le_trans (le_max_left _ _) (le_max_right _ _)
      have hy2 : 2 ≤ y := le_trans (le_max_right _ _) (le_max_right _ _)
      obtain ⟨S, hS, hSsum⟩ := hy0 y hy0'
      have h2y : 2 * y ^ 2 < y ^ 8 := by
        have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
        have h6 : 2 < y ^ 6 := by
          calc 2 < 2 ^ 6 := by norm_num
            _ ≤ y ^ 6 := Nat.pow_le_pow_left hy2 6
        rw [this]
        have : 0 < y ^ 2 := by positivity
        nlinarith
      have hyy : y ≤ y ^ 8 := Nat.le_self_pow (by norm_num) y
      set G := S.image (fun r : ℕ × ℕ => 3 * (r.1 * r.2)) with hG
      have hinj : Set.InjOn (fun r : ℕ × ℕ => 3 * (r.1 * r.2)) S := by
        rintro ⟨v, u⟩ hr ⟨v', u'⟩ hr' heq
        simp only at heq
        have heq' : v * u = v' * u' := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) heq
        obtain ⟨hv, hu, hv2, hu8, -, -, -⟩ := hS _ hr
        obtain ⟨hv', hu', hv2', hu8', -, -, -⟩ := hS _ hr'
        simp only at hv hu hv2 hu8 hv' hu' hv2' hu8'
        have hdvd : u ∣ v' * u' := ⟨v, by rw [← heq']; ring⟩
        rcases (Nat.Prime.dvd_mul hu).1 hdvd with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hu hv').1 h
          omega
        · have huu := (Nat.prime_dvd_prime_iff_eq hu hu').1 h
          subst huu
          have : v = v' := Nat.eq_of_mul_eq_mul_right hu.pos heq'
          rw [this]
      have hdisj : Disjoint F G := by
        rw [Finset.disjoint_left]
        intro n hnF hnG
        obtain ⟨⟨v, u⟩, hr, rfl⟩ := Finset.mem_image.1 hnG
        obtain ⟨hv, hu, -, hu8, -, -, -⟩ := hS _ hr
        have h1 : 3 * (v * u) ≤ F.sup id := Finset.le_sup (f := id) hnF
        have h2 : u ≤ v * u := Nat.le_mul_of_pos_left u hv.pos
        have h3 : v * u ≤ 3 * (v * u) := Nat.le_mul_of_pos_left (v * u) (by decide)
        simp only at hu8
        omega
      refine ⟨F ∪ G, ?_, ?_⟩
      · intro n hn
        rcases Finset.mem_union.1 hn with h | h
        · exact hF n h
        · obtain ⟨⟨v, u⟩, hr, rfl⟩ := Finset.mem_image.1 h
          obtain ⟨hv, hu, hv2, hu8, -, h3v, h3u⟩ := hS _ hr
          simp only at hv hu hv2 hu8 h3v h3u
          have hvu : v ≠ u := by omega
          exact omega_Omega_eq_three_of_three_distinct_primes Nat.prime_three hv hu h3v h3u hvu
      · rw [Finset.sum_union hdisj, hFsum, hG, Finset.sum_image hinj]
        have hsumG :
            (∑ x ∈ S, (1 : ℚ) / ((3 * (x.1 * x.2) : ℕ) : ℚ)) =
              (1 / 3 : ℚ) * ∑ x ∈ S, (1 : ℚ) / ((x.1 : ℚ) * (x.2 : ℚ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          push_cast
          ring
        rw [hsumG, hSsum]
        push_cast
        ring
  obtain ⟨F, hF, hFsum⟩ := key p
  refine ⟨F, hF, ?_⟩
  rw [hFsum, hτ]
  push_cast
  field_simp

theorem erdos_306_iff_true :
    True ↔ ∀ (q : ℚ), 0 < q → Squarefree q.den →
      ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
      (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
      q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) :=
  ⟨fun _ => erdos_306_formal_conjectures, fun _ => trivial⟩

theorem erdos_306.variants.integer_three_primes (m : ℕ) (h : 0 < m) :
    ∃ k > (0 : ℕ), ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧
    ∀ i, (hik : i < k) → n ⟨i, Nat.lt_succ_of_lt hik⟩ < n ⟨(i + 1), Nat.succ_lt_succ hik⟩ ∧
    (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 3 ∧ Ω (n i) = 3) ∧
    m = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) := by
  obtain ⟨F, hF, hsum⟩ := integer_three_primes_finset m h
  have hm0 : (0 : ℚ) < m := by exact_mod_cast h
  obtain ⟨c, hc⟩ : ∃ c, F.card = c + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [Finset.card_eq_zero.1 h0, Finset.sum_empty] at hsum
    exact hm0.ne' hsum
  set e := F.orderEmbOfFin hc
  have heF : ∀ j, e j ∈ F := fun j => F.orderEmbOfFin_mem hc j
  have he1 : ∀ j, 1 < e j := fun j => (hF _ (heF j)).2.2
  have hIcc : Finset.Icc (1 : Fin (c + 2)) (Fin.last (c + 1)) =
      Finset.univ.map (Fin.succEmb (c + 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_univ, true_and, Fin.coe_succEmb,
      Fin.exists_succ_eq, Fin.le_last, and_true]
    rw [Fin.le_iff_val_le_val, Fin.val_one, Ne, Fin.ext_iff, Fin.val_zero]
    omega
  have hmono : StrictMono (Fin.cons 1 (fun j => e j) : Fin (c + 2) → ℕ) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    induction i using Fin.cases with
    | zero => simp [he1 0]
    | succ j =>
      rw [← Fin.succ_castSucc]
      simp only [Fin.cons_succ]
      exact e.strictMono j.castSucc_lt_succ
  have hfac : ∀ i ∈ Finset.Icc (1 : Fin (c + 2)) (Fin.last (c + 1)),
      ω ((Fin.cons 1 (fun j => e j) : Fin (c + 2) → ℕ) i) = 3 ∧
      Ω ((Fin.cons 1 (fun j => e j) : Fin (c + 2) → ℕ) i) = 3 := by
    rw [hIcc]
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    simp only [Fin.coe_succEmb, Fin.cons_succ]
    exact ⟨(hF _ (heF j)).1, (hF _ (heF j)).2.1⟩
  have hsum_eq : (m : ℚ) = ∑ i ∈ Finset.Icc (1 : Fin (c + 2)) (Fin.last (c + 1)),
      (1 : ℚ) / ((Fin.cons 1 (fun j => e j) : Fin (c + 2) → ℕ) i) := by
    have hmapF : Finset.univ.map e.toEmbedding = F := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and]
      exact Set.ext_iff.1 (F.range_orderEmbOfFin hc) x
    rw [hIcc, Finset.sum_map, hsum, ← hmapF, Finset.sum_map]
    simp
  refine ⟨c + 1, by omega, Fin.cons 1 (fun j => e j), rfl, ?_⟩
  intro i hik
  refine ⟨?_, hfac, hsum_eq⟩
  exact hmono (by simp [Fin.lt_def, hik])

end Erdos306

