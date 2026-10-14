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

public import PowerfulSumsAndNitaj939
public import AbcQualityAndCohnRecurrence939

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Nat

namespace Erdos939

/-- Unconditional resolution of `erdos_939.variants.triples` (`FormalConjectures.ErdosProblems.939`). -/
theorem erdos_939_variants_triples :
    True ↔ {(a, b, c) | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      a + b = c}.Infinite :=
  ⟨fun _ => erdos_939_variants_triples_infinite, fun _ => trivial⟩

/-- Dotted alias matching `FormalConjectures.ErdosProblems.939`. -/
theorem erdos_939.variants.triples :
    True ↔ {(a, b, c) | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      a + b = c}.Infinite :=
  erdos_939_variants_triples

/-- Unconditional resolution of `erdos_939.variants.infinite_of_six_le` (`FormalConjectures.ErdosProblems.939`). -/
theorem erdos_939_variants_infinite_of_six_le : ∀ r ≥ 6, (Erdos939Sums r).Infinite :=
  erdos_939.variants.infinite_of_six_le

/-- Negation form of `erdos_939.variants.finite`. -/
theorem erdos_939_variants_finite_not : ¬ (∀ r ≥ 4, (Erdos939Sums r).Finite) := by
  intro h
  exact erdos_939_variants_infinite_of_six_le 6 le_rfl (h 6 (by omega))

/-- Unconditional resolution of `erdos_939.variants.finite` (`FormalConjectures.ErdosProblems.939`). -/
theorem erdos_939_variants_finite : False ↔ ∀ r ≥ 4, (Erdos939Sums r).Finite :=
  ⟨False.elim, fun h => erdos_939_variants_finite_not h⟩

/-- Dotted alias matching `FormalConjectures.ErdosProblems.939`. -/
theorem erdos_939.variants.finite : False ↔ ∀ r ≥ 4, (Erdos939Sums r).Finite :=
  erdos_939_variants_finite

/-- Unconditional resolution of `erdos_939.variants.examples` (`FormalConjectures.ErdosProblems.939`). -/
theorem erdos_939_variants_examples : ∃ r ≥ 4, (Erdos939Sums r).Nonempty :=
  ⟨5, by omega, erdos939Sums_nonempty_of_five_le 5 le_rfl⟩

/-- Unconditional resolution of `erdos_939.variants.seven` (`FormalConjectures.ErdosProblems.939`). -/
theorem erdos_939_variants_seven : (Erdos939Sums 7).Nonempty :=
  erdos939Sums_nonempty_of_five_le 7 (by omega)

/-- Dotted alias matching `FormalConjectures.ErdosProblems.939`. -/
theorem erdos_939.variants.seven : (Erdos939Sums 7).Nonempty :=
  erdos_939_variants_seven

/-- Unconditional resolution of `erdos_939.variants.eight` (`FormalConjectures.ErdosProblems.939`). -/
theorem erdos_939_variants_eight : (Erdos939Sums 8).Nonempty :=
  erdos939Sums_nonempty_of_five_le 8 (by omega)

/-- Dotted alias matching `FormalConjectures.ErdosProblems.939`. -/
theorem erdos_939.variants.eight : (Erdos939Sums 8).Nonempty :=
  erdos_939_variants_eight

/-- Unconditional resolution of `erdos_939.variants.euler` (`FormalConjectures.ErdosProblems.939`)
via Lander and Parkin's (1967) fifth-power counterexample $27^5 + 84^5 + 110^5 + 133^5 = 144^5$. -/
theorem erdos_939_variants_euler :
    ¬ (∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
      (∀ s ∈ S, 0 < s) → ¬ (∃ q, ∑ s ∈ S, s ^ k = q ^ k)) := by
  push Not
  refine ⟨5, by omega, {27, 84, 110, 133}, by decide, by decide, 144, by decide⟩

/-- Lander–Parkin's 4-element fifth-power set `{27^5, 84^5, 110^5, 133^5}`. -/
def landerParkinFiveSet : Finset ℕ :=
  {27 ^ 5, 84 ^ 5, 110 ^ 5, 133 ^ 5}

/-- `1` is vacuously `r`-powerful for every `r : ℕ`. -/
theorem full_one (r : ℕ) : r.Full 1 := by
  intro p hp
  simp at hp

/-- `landerParkinFiveSet` belongs to `Erdos939GeneralSums 5 4` and has sum `144^5`. -/
theorem landerParkinFiveSet_mem_erdos939GeneralSums_five_four :
    landerParkinFiveSet ∈ Erdos939GeneralSums 5 4 ∧
      ∑ s ∈ landerParkinFiveSet, s = 144 ^ 5 := by
  have hsum : ∑ s ∈ landerParkinFiveSet, s = 144 ^ 5 := by decide
  refine ⟨?_, hsum⟩
  rw [mem_erdos939GeneralSums_iff]
  refine ⟨by decide, ?_, ?_, ?_⟩
  · unfold Finset.Coprime landerParkinFiveSet
    decide
  · rw [hsum]
    simpa using full_pow_mul_of_le 5 5 144 1 le_rfl (full_one 5)
  · intro s hs
    simp only [landerParkinFiveSet, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨by decide, by simpa using full_pow_mul_of_le 5 5 27 1 le_rfl (full_one 5)⟩
    · exact ⟨by decide, by simpa using full_pow_mul_of_le 5 5 84 1 le_rfl (full_one 5)⟩
    · exact ⟨by decide, by simpa using full_pow_mul_of_le 5 5 110 1 le_rfl (full_one 5)⟩
    · exact ⟨by decide, by simpa using full_pow_mul_of_le 5 5 133 1 le_rfl (full_one 5)⟩

/-! ## Section 2: General $k$-Summand Radical Divisibility & ABC Quality Exponent `r / (r - 1)` -/

/-- `r.Full` is closed under arbitrary `Finset` products. -/
theorem full_finset_prod_of_forall_full {α : Type*} (r : ℕ) (S : Finset α) (f : α → ℕ)
    (h : ∀ x ∈ S, r.Full (f x)) :
    r.Full (∏ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [full_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact full_mul_of_full r (f a) (∏ x ∈ s, f x)
      (h a (Finset.mem_insert_self a s))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

/-- In any `Finset ℕ` of cardinality `≥ 2` with positive elements, every element is strictly
less than the sum of all elements. -/
theorem lt_sum_of_mem_of_two_le_card {S : Finset ℕ} (hcard : 2 ≤ S.card)
    (hpos : ∀ x ∈ S, 0 < x) {s : ℕ} (hs : s ∈ S) :
    s < ∑ x ∈ S, x := by
  have her_card : 0 < (S.erase s).card := by
    rw [Finset.card_erase_of_mem hs]
    omega
  rcases Finset.card_pos.mp her_card with ⟨t, ht⟩
  have htS : t ∈ S := Finset.mem_of_mem_erase ht
  have ht_pos : 0 < t := hpos t htS
  have hle : t ≤ ∑ x ∈ S.erase s, x :=
    Finset.single_le_sum (f := fun x : ℕ => x) (fun x _ => Nat.zero_le x) ht
  have hsum := (Finset.add_sum_erase S id hs).symm
  dsimp at hsum
  omega

/-- For any `S : Finset ℕ` of cardinality `≥ 2` with positive elements,
`∏ x ∈ S, x < (∑ x ∈ S, x) ^ S.card`. -/
theorem prod_lt_sum_pow_card_of_two_le_card {S : Finset ℕ} (hcard : 2 ≤ S.card)
    (hpos : ∀ x ∈ S, 0 < x) :
    ∏ x ∈ S, x < (∑ x ∈ S, x) ^ S.card := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  rcases hne with ⟨s₀, hs₀⟩
  set σ := ∑ x ∈ S, x
  have hs₀_lt : s₀ < σ := lt_sum_of_mem_of_two_le_card hcard hpos hs₀
  have her_prod_pos : 0 < ∏ x ∈ S.erase s₀, x :=
    Finset.prod_pos (fun x hx => hpos x (Finset.mem_of_mem_erase hx))
  have her_prod_le : ∏ x ∈ S.erase s₀, x ≤ σ ^ (S.erase s₀).card := by
    calc ∏ x ∈ S.erase s₀, x
        ≤ ∏ _x ∈ S.erase s₀, σ := Finset.prod_le_prod'
          (fun x hx => Finset.single_le_sum (f := fun y : ℕ => y) (fun y _ => Nat.zero_le y)
            (Finset.mem_of_mem_erase hx))
      _ = σ ^ (S.erase s₀).card := by rw [Finset.prod_const]
  have h1 : s₀ * ∏ x ∈ S.erase s₀, x < σ * ∏ x ∈ S.erase s₀, x :=
    Nat.mul_lt_mul_of_pos_right hs₀_lt her_prod_pos
  have h2 : σ * ∏ x ∈ S.erase s₀, x ≤ σ * σ ^ (S.erase s₀).card :=
    Nat.mul_le_mul_left σ her_prod_le
  have hprod := (Finset.mul_prod_erase S id hs₀).symm
  dsimp at hprod
  have hpow : σ * σ ^ (S.erase s₀).card = σ ^ S.card := by
    rw [Finset.card_erase_of_mem hs₀, ← _root_.pow_succ']
    congr 1
    omega
  omega

/-- For any `S : Finset ℕ` of cardinality `≥ 2` with positive elements,
`(∏ x ∈ S, x) * (∑ x ∈ S, x) < (∑ x ∈ S, x) ^ (S.card + 1)`. -/
theorem prod_mul_sum_lt_sum_pow_succ_of_two_le_card {S : Finset ℕ} (hcard : 2 ≤ S.card)
    (hpos : ∀ x ∈ S, 0 < x) :
    (∏ x ∈ S, x) * (∑ x ∈ S, x) < (∑ x ∈ S, x) ^ (S.card + 1) := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  rcases hne with ⟨s₀, hs₀⟩
  have hsum_pos : 0 < ∑ x ∈ S, x :=
    lt_of_lt_of_le (hpos s₀ hs₀)
      (Finset.single_le_sum (f := fun x : ℕ => x) (fun x _ => Nat.zero_le x) hs₀)
  rw [pow_succ]
  exact Nat.mul_lt_mul_of_pos_right (prod_lt_sum_pow_card_of_two_le_card hcard hpos) hsum_pos

/-- Universal $k$-summand radical divisibility and inequality for `S ∈ Erdos939GeneralSums r k` (`1 ≤ k`):
`rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ∣ (∏ s ∈ S, s) * (∑ s ∈ S, s)` and
`rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ≤ (∏ s ∈ S, s) * (∑ s ∈ S, s)`. -/
theorem rad_pow_r_dvd_and_le_prod_mul_sum_of_mem_generalSums {r k : ℕ} (hk : 1 ≤ k)
    {S : Finset ℕ} (hS : S ∈ Erdos939GeneralSums r k) :
    rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ∣ (∏ s ∈ S, s) * (∑ s ∈ S, s) ∧
      rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ≤ (∏ s ∈ S, s) * (∑ s ∈ S, s) := by
  rcases (mem_erdos939GeneralSums_iff r k S).mp hS with ⟨hcard, _, hfull_sum, hall⟩
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  rcases hne with ⟨s₀, hs₀⟩
  have hprod_pos : 0 < ∏ s ∈ S, s := Finset.prod_pos (fun s hs => (hall s hs).1)
  have hsum_pos : 0 < ∑ s ∈ S, s :=
    lt_of_lt_of_le (hall s₀ hs₀).1
      (Finset.single_le_sum (f := fun x : ℕ => x) (fun x _ => Nat.zero_le x) hs₀)
  have hfull_prod : r.Full (∏ s ∈ S, s) :=
    full_finset_prod_of_forall_full r S id (fun s hs => (hall s hs).2)
  have hfull_all : r.Full ((∏ s ∈ S, s) * (∑ s ∈ S, s)) :=
    full_mul_of_full r _ _ hfull_prod hfull_sum
  have hpos_all : 0 < (∏ s ∈ S, s) * (∑ s ∈ S, s) := Nat.mul_pos hprod_pos hsum_pos
  have hdvd := rad_pow_dvd_of_full hpos_all hfull_all
  exact ⟨hdvd, Nat.le_of_dvd hpos_all hdvd⟩

/-- Universal $k$-summand radical upper bound for `S ∈ Erdos939GeneralSums r k` (`2 ≤ k`):
`rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ≤ (∏ s ∈ S, s) * (∑ s ∈ S, s) < (∑ s ∈ S, s) ^ (k + 1)`. -/
theorem rad_pow_r_lt_sum_pow_succ_of_mem_generalSums {r k : ℕ} (hk : 2 ≤ k)
    {S : Finset ℕ} (hS : S ∈ Erdos939GeneralSums r k) :
    rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ≤ (∏ s ∈ S, s) * (∑ s ∈ S, s) ∧
      (∏ s ∈ S, s) * (∑ s ∈ S, s) < (∑ s ∈ S, s) ^ (k + 1) ∧
      rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r < (∑ s ∈ S, s) ^ (k + 1) := by
  rcases (mem_erdos939GeneralSums_iff r k S).mp hS with ⟨hcard, _, _, hall⟩
  have h1 := (rad_pow_r_dvd_and_le_prod_mul_sum_of_mem_generalSums (by omega) hS).2
  have h2 : (∏ s ∈ S, s) * (∑ s ∈ S, s) < (∑ s ∈ S, s) ^ (k + 1) := by
    rw [← hcard]
    exact prod_mul_sum_lt_sum_pow_succ_of_two_le_card (by omega) (fun s hs => (hall s hs).1)
  exact ⟨h1, h2, lt_of_le_of_lt h1 h2⟩

/-- Specialization to `k = r - 2` for `S ∈ Erdos939Sums r` (`4 ≤ r`):
`rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ≤ (∏ s ∈ S, s) * (∑ s ∈ S, s) < (∑ s ∈ S, s) ^ (r - 1)`. -/
theorem rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums {r : ℕ} (hr : 4 ≤ r)
    {S : Finset ℕ} (hS : S ∈ Erdos939Sums r) :
    rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r ≤ (∏ s ∈ S, s) * (∑ s ∈ S, s) ∧
      (∏ s ∈ S, s) * (∑ s ∈ S, s) < (∑ s ∈ S, s) ^ (r - 1) ∧
      rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r < (∑ s ∈ S, s) ^ (r - 1) := by
  have hgen : S ∈ Erdos939GeneralSums r (r - 2) :=
    (mem_erdos939GeneralSums_r_sub_two_iff r S).mpr hS
  have h := rad_pow_r_lt_sum_pow_succ_of_mem_generalSums (by omega) hgen
  rwa [show r - 2 + 1 = r - 1 by omega] at h

/-- Real-logarithmic ABC quality bound for `S ∈ Erdos939Sums r` (`4 ≤ r`):
`(r / (r - 1)) * log rad((∏ s ∈ S, s) * (∑ s ∈ S, s)) < log (∑ s ∈ S, s)`. -/
theorem abc_quality_real_bound_of_mem_erdos939Sums {r : ℕ} (hr : 4 ≤ r)
    {S : Finset ℕ} (hS : S ∈ Erdos939Sums r) :
    ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) *
        Real.log (rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) : ℝ) <
      Real.log ((∑ s ∈ S, s : ℕ) : ℝ) := by
  have h := (rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums hr hS).2.2
  have hlt_real : (rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) : ℝ) ^ r <
      ((∑ s ∈ S, s : ℕ) : ℝ) ^ (r - 1) := by exact_mod_cast h
  have hrad_pos : (0 : ℝ) < (rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) : ℝ) := by
    exact_mod_cast rad_pos _
  have hlog : Real.log ((rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) : ℝ) ^ r) <
      Real.log (((∑ s ∈ S, s : ℕ) : ℝ) ^ (r - 1)) :=
    Real.log_lt_log (pow_pos hrad_pos r) hlt_real
  rw [Real.log_pow, Real.log_pow] at hlog
  have hr1_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by
    have : 1 ≤ r - 1 := by omega
    exact_mod_cast this
  rw [div_mul_eq_mul_div, div_lt_iff₀ hr1_pos]
  linarith

/-- Specialization of the ABC quality bound to `r = 5` (`S ∈ Erdos939Sums 5`):
`rad((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 5 < (∑ s ∈ S, s) ^ 4` and
`(5 / 4) * log rad < log sum`. -/
theorem abc_quality_five_fourths_of_mem_erdos939Sums_five
    {S : Finset ℕ} (hS : S ∈ Erdos939Sums 5) :
    rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 5 < (∑ s ∈ S, s) ^ 4 ∧
      ((5 : ℝ) / 4) * Real.log (rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) : ℝ) <
        Real.log ((∑ s ∈ S, s : ℕ) : ℝ) := by
  have h1 := (rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums (r := 5) (by omega) hS).2.2
  have h2 := abc_quality_real_bound_of_mem_erdos939Sums (r := 5) (by omega) hS
  refine ⟨by simpa using h1, ?_⟩
  simpa using h2

/-- Specialization of the ABC quality bound to `r = 4` (`S ∈ Erdos939Sums 4`):
`rad((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 4 < (∑ s ∈ S, s) ^ 3` and
`(4 / 3) * log rad < log sum`. -/
theorem abc_quality_four_thirds_of_mem_erdos939Sums_four
    {S : Finset ℕ} (hS : S ∈ Erdos939Sums 4) :
    rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 4 < (∑ s ∈ S, s) ^ 3 ∧
      ((4 : ℝ) / 3) * Real.log (rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) : ℝ) <
        Real.log ((∑ s ∈ S, s : ℕ) : ℝ) := by
  have h1 := (rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums (r := 4) (by omega) hS).2.2
  have h2 := abc_quality_real_bound_of_mem_erdos939Sums (r := 4) (by omega) hS
  refine ⟨by simpa using h1, ?_⟩
  simpa using h2

/-! ## Section 3: Walsh's (2024) Quadratic-Twist Criteria & Parametric Scaling -/

/-- Universal prime-support absorption lemma: if every prime dividing `a` also divides `x`,
then `a ^ m * x ^ r` is `r`-powerful for all `r, m : ℕ`. -/
theorem full_mul_pow_of_prime_dvd_imp {r m a x : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ x) :
    r.Full (a ^ m * x ^ r) := by
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hdvd : p ∣ a ^ m * x ^ r := (Nat.mem_primeFactors.mp hp).2.1
  have hpx : p ∣ x := by
    rcases hpp.dvd_mul.mp hdvd with hpa | hpxr
    · exact h p hpp (hpp.dvd_of_dvd_pow hpa)
    · exact hpp.dvd_of_dvd_pow hpxr
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpx r) (a ^ m)

/-- Divisibility specialization: if `a ∣ x`, then `a ^ m * x ^ r` is `r`-powerful for all `r, m : ℕ`. -/
theorem full_mul_pow_of_dvd {r m a x : ℕ} (hax : a ∣ x) :
    r.Full (a ^ m * x ^ r) :=
  full_mul_pow_of_prime_dvd_imp (fun _ _ hpa => dvd_trans hpa hax)

/-- Walsh's radical-divisibility criterion: if `0 < a` and `rad a ∣ x`, then
`a ^ m * x ^ r` is `r`-powerful for all `r, m : ℕ`. -/
theorem full_mul_pow_of_rad_dvd {r m a x : ℕ} (ha : 0 < a) (hrad : rad a ∣ x) :
    r.Full (a ^ m * x ^ r) := by
  refine full_mul_pow_of_prime_dvd_imp (fun p hpp hpa => ?_)
  have hp_mem : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpa, by omega⟩
  have hp_rad : p ∣ rad a := Finset.dvd_prod_of_mem _ hp_mem
  exact dvd_trans hp_rad hrad

/-- Exact decomposition of the coprime twist condition
`Nat.Coprime (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3)` into pairwise coprimality of `(d₁, x₁)` and `(d₂, x₂)`. -/
theorem walsh_coprime_twist_condition_iff
    {d₁ x₁ d₂ x₂ : ℕ} :
    Nat.Coprime (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3) ↔
      Nat.Coprime d₁ d₂ ∧ Nat.Coprime d₁ x₂ ∧ Nat.Coprime x₁ d₂ ∧ Nat.Coprime x₁ x₂ := by
  simp only [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right,
    Nat.coprime_pow_left_iff (by omega : 0 < 2),
    Nat.coprime_pow_left_iff (by omega : 0 < 3),
    Nat.coprime_pow_right_iff (by omega : 0 < 2),
    Nat.coprime_pow_right_iff (by omega : 0 < 3)]
  tauto

/-- Walsh's quadratic-twist criterion for coprime $3$-powerful sets in `Erdos939GeneralSums 3 2`:
if `(d₁, x₁), (d₂, x₂), (d₃, x₃)` are positive integers with `rad dᵢ ∣ xᵢ`,
`Nat.Coprime (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3)`, and
`d₁ ^ 2 * x₁ ^ 3 + d₂ ^ 2 * x₂ ^ 3 = d₃ ^ 2 * x₃ ^ 3`, then
`{d₁ ^ 2 * x₁ ^ 3, d₂ ^ 2 * x₂ ^ 3} ∈ Erdos939GeneralSums 3 2`. -/
theorem walsh_twist_pair_mem_erdos939GeneralSums_three_two
    {d₁ x₁ d₂ x₂ d₃ x₃ : ℕ}
    (hd₁ : 0 < d₁) (hx₁ : 0 < x₁) (hd₂ : 0 < d₂) (hx₂ : 0 < x₂) (hd₃ : 0 < d₃)
    (hr₁ : rad d₁ ∣ x₁) (hr₂ : rad d₂ ∣ x₂) (hr₃ : rad d₃ ∣ x₃)
    (hcop : Nat.Coprime (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3))
    (hsum : d₁ ^ 2 * x₁ ^ 3 + d₂ ^ 2 * x₂ ^ 3 = d₃ ^ 2 * x₃ ^ 3) :
    ({d₁ ^ 2 * x₁ ^ 3, d₂ ^ 2 * x₂ ^ 3} : Finset ℕ) ∈ Erdos939GeneralSums 3 2 := by
  rw [pair_mem_erdos939GeneralSums_two_iff 3 (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3) (by omega)]
  refine ⟨by positivity, by positivity, hcop,
    full_mul_pow_of_rad_dvd hd₁ hr₁, full_mul_pow_of_rad_dvd hd₂ hr₂, ?_⟩
  rw [hsum]
  exact full_mul_pow_of_rad_dvd hd₃ hr₃

/-- Walsh's quadratic-twist criterion for the `erdos_939.variants.triples` set of coprime
$3$-powerful triples `(a, b, c)`. -/
theorem walsh_twist_triple_mem_triples_set
    {d₁ x₁ d₂ x₂ d₃ x₃ : ℕ}
    (hd₁ : 0 < d₁) (hx₁ : 0 < x₁) (hd₂ : 0 < d₂) (hx₂ : 0 < x₂) (hd₃ : 0 < d₃)
    (hr₁ : rad d₁ ∣ x₁) (hr₂ : rad d₂ ∣ x₂) (hr₃ : rad d₃ ∣ x₃)
    (hcop : Nat.Coprime (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3))
    (hsum : d₁ ^ 2 * x₁ ^ 3 + d₂ ^ 2 * x₂ ^ 3 = d₃ ^ 2 * x₃ ^ 3) :
    (d₁ ^ 2 * x₁ ^ 3, d₂ ^ 2 * x₂ ^ 3, d₃ ^ 2 * x₃ ^ 3) ∈
      {(a, b, c) : ℕ × ℕ × ℕ |
        ({a, b, c} : Finset ℕ).Coprime ∧
        0 < a ∧ 0 < b ∧
        (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
        a + b = c} := by
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, by positivity, by positivity,
    full_mul_pow_of_rad_dvd hd₁ hr₁,
    full_mul_pow_of_rad_dvd hd₂ hr₂,
    full_mul_pow_of_rad_dvd hd₃ hr₃,
    hsum⟩
  exact coprime_insert_of_coprime_pair
    {d₁ ^ 2 * x₁ ^ 3, d₂ ^ 2 * x₂ ^ 3, d₃ ^ 2 * x₃ ^ 3}
    (by simp) (by simp) hcop

/-- Any Walsh quadratic-twist triple with `3` dividing one of its three terms forms a valid
`IsNitajTriple` seed for the Euler–Viète cubic tangent recurrence. -/
theorem isNitajTriple_of_walsh_twist
    {d₁ x₁ d₂ x₂ d₃ x₃ : ℕ}
    (hd₁ : 0 < d₁) (hx₁ : 0 < x₁) (hd₂ : 0 < d₂) (hx₂ : 0 < x₂) (hd₃ : 0 < d₃)
    (hr₁ : rad d₁ ∣ x₁) (hr₂ : rad d₂ ∣ x₂) (hr₃ : rad d₃ ∣ x₃)
    (hcop : Nat.Coprime (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3))
    (h3 : 3 ∣ d₁ ^ 2 * x₁ ^ 3 ∨ 3 ∣ d₂ ^ 2 * x₂ ^ 3 ∨ 3 ∣ d₃ ^ 2 * x₃ ^ 3)
    (hsum : d₁ ^ 2 * x₁ ^ 3 + d₂ ^ 2 * x₂ ^ 3 = d₃ ^ 2 * x₃ ^ 3) :
    IsNitajTriple (d₁ ^ 2 * x₁ ^ 3) (d₂ ^ 2 * x₂ ^ 3) (d₃ ^ 2 * x₃ ^ 3) :=
  ⟨by positivity, by positivity, hsum, hcop, h3,
    full_mul_pow_of_rad_dvd hd₁ hr₁,
    full_mul_pow_of_rad_dvd hd₂ hr₂,
    full_mul_pow_of_rad_dvd hd₃ hr₃⟩

/-- Parametric cube scaling `(d^3 * a, d^3 * b, d^3 * c)` preserves positivity, `3`-powerful
status, and the additive relation `a + b = c` for any positive scaling factor `d`. -/
theorem walsh_parametric_cube_scaling_full_and_sum {a b c : ℕ} (d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hfa : (3).Full a) (hfb : (3).Full b) (hfc : (3).Full c)
    (hsum : a + b = c) :
    0 < d ^ 3 * a ∧ 0 < d ^ 3 * b ∧ 0 < d ^ 3 * c ∧
      (3).Full (d ^ 3 * a) ∧ (3).Full (d ^ 3 * b) ∧ (3).Full (d ^ 3 * c) ∧
      d ^ 3 * a + d ^ 3 * b = d ^ 3 * c := by
  have hc : 0 < c := by omega
  refine ⟨by positivity, by positivity, by positivity,
    full_pow_mul_of_le 3 3 d a le_rfl hfa,
    full_pow_mul_of_le 3 3 d b le_rfl hfb,
    full_pow_mul_of_le 3 3 d c le_rfl hfc,
    by linear_combination d ^ 3 * hsum⟩

/-- Diagonal cube scaling `(d^3 * a, d^3 * b)` of a coprime pair `(a, b)` preserves coprimality
if and only if `d = 1` (explaining why Walsh twists individual terms `dᵢ^2 xᵢ^3` with
`gcd(d₁ x₁, d₂ x₂) = 1` rather than scaling uniformly by `d^3`). -/
theorem walsh_parametric_cube_scaling_coprime_iff {a b d : ℕ}
    (hd : 0 < d) (hcop : Nat.Coprime a b) :
    Nat.Coprime (d ^ 3 * a) (d ^ 3 * b) ↔ d = 1 := by
  constructor
  · intro h
    have hd_dvd_left : d ∣ d ^ 3 * a := dvd_mul_of_dvd_left (dvd_pow_self d (by omega)) a
    have hd_dvd_right : d ∣ d ^ 3 * b := dvd_mul_of_dvd_left (dvd_pow_self d (by omega)) b
    have hd1 : d ∣ 1 := h.gcd_eq_one ▸ Nat.dvd_gcd hd_dvd_left hd_dvd_right
    exact Nat.eq_one_of_dvd_one hd1
  · rintro rfl
    simpa using hcop

/-! ## Section 4: Exact Reduction of `erdos_939` to $r = 4$ & Conditional $r = 4, 5$ ABC Reductions -/

/-- **Exact Reduction of `erdos_939` to $r = 4$:** Since $r = 5$ is solved by Cambie's witness
and $r \ge 6$ is solved by `erdos_939_variants_infinite_of_six_le`, the universal statement
`∀ r ≥ 4, (Erdos939Sums r).Nonempty` is equivalent to `(Erdos939Sums 4).Nonempty`. -/
theorem erdos_939_iff_four_nonempty :
    (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔ (Erdos939Sums 4).Nonempty :=
  (erdos939_forall_four_le_iff_four_nonempty ((Erdos939Sums 4).Nonempty) Iff.rfl).symm

/-- Equivalence between `∀ r ≥ 4, (Erdos939Sums r).Nonempty` and the existence of a positive
coprime $4$-powerful pair `(a, b)` with $4$-powerful sum `a + b`. -/
theorem erdos_939_iff_exists_coprime_four_full_pair :
    (∀ r ≥ 4, (Erdos939Sums r).Nonempty) ↔
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
        (4).Full a ∧ (4).Full b ∧ (4).Full (a + b) :=
  erdos939Sums_four_nonempty_iff_exists_pair
    (∀ r ≥ 4, (Erdos939Sums r).Nonempty) erdos_939_iff_four_nonempty

/-- Top-down conditional resolution of `erdos_939` from any positive coprime $4$-powerful pair
`(a, b)` with $4$-powerful sum. -/
theorem erdos_939_of_coprime_four_full_pair {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hfa : (4).Full a) (hfb : (4).Full b) (hfs : (4).Full (a + b)) :
    ∀ r ≥ 4, (Erdos939Sums r).Nonempty :=
  erdos_939_iff_exists_coprime_four_full_pair.mpr ⟨a, b, ha, hb, hcop, hfa, hfb, hfs⟩

/-- Universal finiteness of `Erdos939Sums r` under any uniform upper bound `B` on the sum `∑ s ∈ S, s`. -/
theorem erdos939Sums_finite_of_sum_bound (r B : ℕ)
    (hbound : ∀ S ∈ Erdos939Sums r, ∑ s ∈ S, s ≤ B) :
    (Erdos939Sums r).Finite := by
  apply Set.Finite.subset (s := (Finset.Icc 1 B).powerset)
  · exact Finset.finite_toSet _
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_powerset]
    have hle : ∑ s ∈ S, s ≤ B := hbound S hS
    rcases hS with ⟨_, _, _, hall⟩
    intro x hx
    rw [Finset.mem_Icc]
    have hx_pos : 0 < x := (hall x hx).1
    have hx_le : x ≤ ∑ s ∈ S, s :=
      Finset.single_le_sum (f := fun y : ℕ => y) (fun y _ => Nat.zero_le y) hx
    omega

/-- Universal $k$-summand ABC height bound for `Erdos939Sums r` ($r \ge 4$): if every set
`S ∈ Erdos939Sums r` with `∑ s ∈ S, s > B` satisfies `(∑ s ∈ S, s) ^ (r - 1) ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r`,
then every `S ∈ Erdos939Sums r` satisfies `∑ s ∈ S, s ≤ B`. -/
theorem sum_bound_of_k_summand_abc_threshold_for_erdos939Sums {r B : ℕ} (hr : 4 ≤ r)
    (habc : ∀ S ∈ Erdos939Sums r, B < ∑ s ∈ S, s →
      (∑ s ∈ S, s) ^ (r - 1) ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ r)
    {S : Finset ℕ} (hS : S ∈ Erdos939Sums r) :
    ∑ s ∈ S, s ≤ B := by
  have hlt := (rad_pow_r_lt_sum_pow_pred_of_mem_erdos939Sums hr hS).2.2
  by_contra hnot
  have hgt : B < ∑ s ∈ S, s := by omega
  have hge := habc S hS hgt
  omega

/-- Conditional finiteness of `Erdos939Sums 4` under a $4/3$-exponent radical threshold above `B`. -/
theorem erdos939Sums_four_finite_of_abc_four_thirds_threshold {B : ℕ}
    (habc : ∀ S ∈ Erdos939Sums 4, B < ∑ s ∈ S, s →
      (∑ s ∈ S, s) ^ 3 ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 4) :
    (Erdos939Sums 4).Finite :=
  erdos939Sums_finite_of_sum_bound 4 B fun _ hS =>
    sum_bound_of_k_summand_abc_threshold_for_erdos939Sums (by omega) habc hS

/-- Conditional finiteness of `Erdos939Sums 5` under a $5/4$-exponent $3$-summand radical threshold above `B`. -/
theorem erdos939Sums_five_finite_of_abc_five_fourths_threshold {B : ℕ}
    (habc : ∀ S ∈ Erdos939Sums 5, B < ∑ s ∈ S, s →
      (∑ s ∈ S, s) ^ 4 ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 5) :
    (Erdos939Sums 5).Finite :=
  erdos939Sums_finite_of_sum_bound 5 B fun _ hS =>
    sum_bound_of_k_summand_abc_threshold_for_erdos939Sums (by omega) habc hS

/-- Top-down conditional disproof of `erdos_939` if every `S ∈ Erdos939Sums 4` satisfies the
radical inequality `(∑ s ∈ S, s) ^ 3 ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 4`. -/
theorem not_erdos_939_of_four_full_radical_obstruction
    (habc : ∀ S ∈ Erdos939Sums 4,
      (∑ s ∈ S, s) ^ 3 ≤ rad ((∏ s ∈ S, s) * (∑ s ∈ S, s)) ^ 4) :
    Erdos939Sums 4 = ∅ ∧ ¬ (∀ r ≥ 4, (Erdos939Sums r).Nonempty) := by
  have hempty : Erdos939Sums 4 = ∅ := by
    ext S
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hS
    have hlt := (abc_quality_four_thirds_of_mem_erdos939Sums_four hS).1
    have hge := habc S hS
    omega
  refine ⟨hempty, ?_⟩
  rw [erdos_939_iff_four_nonempty, hempty]
  exact Set.not_nonempty_empty

end Erdos939
