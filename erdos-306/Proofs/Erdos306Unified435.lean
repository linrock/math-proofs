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

public import Mathlib

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators


/-!
## Finite weighted-edge dual for Erdős #306

An auxiliary finite inequality, not a proof of the original existence problem.
Every edge is an ordered pair; incidence counts both endpoint positions.
The application uses the unique orientation p < q of two distinct primes.
-/

namespace Erdos306.GraphDual

def incidenceDegree {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (v : α) : ℕ :=
  (E.filter fun e => e.1 = v).card + (E.filter fun e => e.2 = v).card

theorem endpoint_sum {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (V : Finset α) (lam : α → ℝ)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    (∑ e ∈ E, (lam e.1 + lam e.2)) =
      ∑ v ∈ V, (incidenceDegree E v : ℝ) * lam v := by
  have hfst := Finset.sum_fiberwise_of_maps_to'
    (s := E) (t := V) (g := Prod.fst) (fun e he => (hend e he).1) lam
  have hsnd := Finset.sum_fiberwise_of_maps_to'
    (s := E) (t := V) (g := Prod.snd) (fun e he => (hend e he).2) lam
  rw [Finset.sum_add_distrib, ← hfst, ← hsnd, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  simp [incidenceDegree, Nat.cast_add, add_mul]

theorem capacity_dual {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (V : Finset α) (lam : α → ℝ)
    (w z : α × α → ℝ) (D : ℕ)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hlam : ∀ v ∈ V, 0 ≤ lam v)
    (hdegree : ∀ v ∈ V, incidenceDegree E v ≤ D)
    (hedge : ∀ e ∈ E, w e ≤ lam e.1 + lam e.2 + z e) :
    (∑ e ∈ E, w e) ≤ (D : ℝ) * (∑ v ∈ V, lam v) + ∑ e ∈ E, z e := by
  calc
    (∑ e ∈ E, w e) ≤ ∑ e ∈ E, (lam e.1 + lam e.2 + z e) :=
      Finset.sum_le_sum hedge
    _ = (∑ v ∈ V, (incidenceDegree E v : ℝ) * lam v) + ∑ e ∈ E, z e := by
      rw [Finset.sum_add_distrib, endpoint_sum E V lam hend]
    _ ≤ (∑ v ∈ V, (D : ℝ) * lam v) + ∑ e ∈ E, z e := by
      apply add_le_add _ le_rfl
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree v hv) (hlam v hv)
    _ = _ := by rw [Finset.mul_sum]

theorem capacity_dual_with_slack_bound {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (V : Finset α) (lam : α → ℝ)
    (w z : α × α → ℝ) (D : ℕ) (Z : ℝ)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hlam : ∀ v ∈ V, 0 ≤ lam v)
    (hdegree : ∀ v ∈ V, incidenceDegree E v ≤ D)
    (hedge : ∀ e ∈ E, w e ≤ lam e.1 + lam e.2 + z e)
    (hslack : (∑ e ∈ E, z e) ≤ Z) :
    (∑ e ∈ E, w e) ≤ (D : ℝ) * (∑ v ∈ V, lam v) + Z := by
  exact (capacity_dual E V lam w z D hend hlam hdegree hedge).trans
    (add_le_add le_rfl hslack)

theorem head_weight_nonnegative (x t : ℝ) (ht : 0 ≤ t) (hx : t ≤ x) :
    0 ≤ t * x - t ^ 2 / 2 := by
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hx), sq_nonneg t]

theorem tail_weight_nonnegative (x : ℝ) : 0 ≤ x ^ 2 / 2 := by positivity

theorem head_head_identity (x y t : ℝ) :
    (t * x - t ^ 2 / 2) + (t * y - t ^ 2 / 2) +
      (x - t) * (y - t) = x * y := by ring

theorem head_head_slack_nonnegative (x y t : ℝ) (hx : t ≤ x) (hy : t ≤ y) :
    0 ≤ (x - t) * (y - t) :=
  mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)

theorem head_tail_bound (x y t : ℝ) (hx : t ≤ x) (hy : y ≤ t) :
    x * y ≤ (t * x - t ^ 2 / 2) + y ^ 2 / 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hx), sq_nonneg (t - y)]

theorem tail_tail_bound (x y : ℝ) : x * y ≤ x ^ 2 / 2 + y ^ 2 / 2 := by
  nlinarith [sq_nonneg (x - y)]

end Erdos306.GraphDual


/-! ## Odd reciprocal-square tail bound -/

/-! A finite odd-integer reciprocal-square tail bound. No asymptotic prime
estimate or summability assumption is used. -/

namespace Erdos306.OddTail

theorem odd_square_le_telescope (k : ℕ) (hk : 0 < k) :
    (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 ≤
      ((1 : ℝ) / k - 1 / ((k + 1 : ℕ) : ℝ)) / 4 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  push_cast
  calc
    (1 : ℝ) / (2 * k + 1) ^ 2 ≤ 1 / (4 * (k : ℝ) * (k + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = (1 / (k : ℝ) - 1 / (k + 1)) / 4 := by
      field_simp
      ring

theorem finite_odd_square_tail (S : Finset ℕ) (K : ℕ) (hK : 0 < K)
    (hS : ∀ k ∈ S, K ≤ k) :
    (∑ k ∈ S, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (4 * (K : ℝ)) := by
  let N := max K (S.sup id) + 1
  have hKN : K ≤ N := le_trans (le_max_left _ _) (Nat.le_succ _)
  have hsub : S ⊆ Finset.Ico K N := by
    intro k hk
    refine Finset.mem_Ico.mpr ⟨hS k hk, ?_⟩
    have hsup : k ≤ S.sup id := Finset.le_sup (f := id) hk
    exact Nat.lt_succ_of_le (hsup.trans (le_max_right _ _))
  have htel : (∑ k ∈ Finset.Ico K N,
      ((1 : ℝ) / k - 1 / ((k + 1 : ℕ) : ℝ))) = 1 / (K : ℝ) - 1 / (N : ℝ) := by
    rw [Finset.sum_Ico_eq_sub _ hKN]
    have hN := Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / k) N
    have hK' := Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / k) K
    rw [hN, hK']
    ring
  calc
    (∑ k ∈ S, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) ≤
        ∑ k ∈ Finset.Ico K N, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ ∑ k ∈ Finset.Ico K N,
        ((1 : ℝ) / k - 1 / ((k + 1 : ℕ) : ℝ)) / 4 := by
      apply Finset.sum_le_sum
      intro k hk
      exact odd_square_le_telescope k (lt_of_lt_of_le hK (Finset.mem_Ico.mp hk).1)
    _ = (1 / (K : ℝ) - 1 / (N : ℝ)) / 4 := by rw [← Finset.sum_div, htel]
    _ ≤ 1 / (4 * (K : ℝ)) := by
      have hNnonneg : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      have hident : (1 : ℝ) / (4 * (K : ℝ)) = (1 / (K : ℝ)) / 4 := by ring
      rw [hident]
      linarith

theorem finite_odd_square_tail_129 (S : Finset ℕ)
    (hS : ∀ k ∈ S, 64 ≤ k) :
    (∑ k ∈ S, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / 256 := by
  convert finite_odd_square_tail S 64 (by norm_num) hS using 1
  norm_num

theorem finite_large_prime_square_tail (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 128 < p) :
    (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / 256 := by
  have hform : ∀ p ∈ P, 2 * (p / 2) + 1 = p := by
    intro p hp
    have hprime := (hP p hp).1
    have hlarge := (hP p hp).2
    have hmod : p % 2 = 1 := hprime.eq_two_or_odd.resolve_left (by omega)
    omega
  have hinj : Set.InjOn (fun p : ℕ => p / 2) P := by
    intro p hp q hq heq
    change p / 2 = q / 2 at heq
    have hpform := hform p hp
    have hqform := hform q hq
    omega
  have himage : ∀ k ∈ P.image (fun p => p / 2), 64 ≤ k := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have := (hP p hp).2
    omega
  have htail := finite_odd_square_tail_129 (P.image fun p => p / 2) himage
  rw [Finset.sum_image hinj] at htail
  have heq : (∑ p ∈ P, (1 : ℝ) / ((2 * (p / 2) + 1 : ℕ) : ℝ) ^ 2) =
      ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hform p hp]
  rw [heq] at htail
  exact htail

end Erdos306.OddTail


/-!
## Literal representation and prime-edge interfaces for Erdős #306

The `IndexedRepresentation` proposition copies the witness-side definition
from the Formal Conjectures Authors' Apache-2.0 statement (Copyright 2025),
`FormalConjectures/ErdosProblems/306.lean`. No original conjecture is assumed
or proved. The finite graph interface below is self-contained.
-/

open scoped BigOperators ArithmeticFunction.omega ArithmeticFunction.Omega

namespace Erdos306.Representation

def IndexedRepresentation (q : ℚ) : Prop :=
  ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
    (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
    q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i)

theorem witness_length_positive (k : ℕ) (n : Fin (k + 1) → ℕ)
    (hzero : n 0 = 1)
    (hfactors : ∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) :
    0 < k := by
  by_contra h
  have hk : k = 0 := by omega
  subst k
  have hbad := (hfactors 0 (by decide)).1
  simp [hzero] at hbad

theorem witness_noninitial_gt_one (k : ℕ) (n : Fin (k + 1) → ℕ)
    (hzero : n 0 = 1) (hmono : StrictMono n)
    (i : Fin (k + 1)) (hi : i ≠ 0) : 1 < n i := by
  have hipos : (0 : Fin (k + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
  simpa [hzero] using hmono hipos

theorem factor_counts_of_distinct_primes (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ω (p * q) = 2 ∧ Ω (p * q) = 2 := by
  constructor
  · rw [ArithmeticFunction.cardDistinctFactors_mul ((Nat.coprime_primes hp hq).mpr hpq.ne),
      ArithmeticFunction.cardDistinctFactors_apply_prime hp,
      ArithmeticFunction.cardDistinctFactors_apply_prime hq]
  · rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hq.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hp,
      ArithmeticFunction.cardFactors_apply_prime hq]

theorem prime_pair_product_injective (p q r s : ℕ)
    (hp : p.Prime) (_hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hrs : r < s) (heq : p * q = r * s) :
    p = r ∧ q = s := by
  have hpd : p ∣ r * s := heq ▸ dvd_mul_right p q
  rcases hp.dvd_mul.mp hpd with hpr | hps
  · have hpr' : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
    subst r
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos heq⟩
  · have hps' : p = s := (Nat.prime_dvd_prime_iff_eq hp hs).mp hps
    subst s
    have hqr : q = r := Nat.eq_of_mul_eq_mul_left hp.pos (heq.trans (Nat.mul_comm r p))
    omega

theorem prime_dvd_product_iff_endpoint (p q r : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) :
    p ∣ q * r ↔ p = q ∨ p = r := by
  rw [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp hq,
    Nat.prime_dvd_prime_iff_eq hp hr]

theorem factor_counts_iff_distinct_primes (n : ℕ) :
    (ω n = 2 ∧ Ω n = 2) ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q := by
  constructor
  · rintro ⟨homega, hOmega⟩
    have hn0 : n ≠ 0 := by intro h; subst n; simp at homega
    have hsf : Squarefree n :=
      (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn0).mp
        (homega.trans hOmega.symm)
    have hlen : n.primeFactorsList.length = 2 := hOmega
    obtain ⟨p, q, hlist⟩ := List.length_eq_two.mp hlen
    have hp : p.Prime := Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hlist])
    have hq : q.Prime := Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hlist])
    have hpq : p ≠ q := by
      have hnodup := (Nat.squarefree_iff_nodup_primeFactorsList hn0).mp hsf
      simpa [hlist] using hnodup
    have hprod : n = p * q := by
      simpa [hlist] using (Nat.prod_primeFactorsList hn0).symm
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact ⟨p, q, hp, hq, hlt, hprod⟩
    · exact ⟨q, p, hq, hp, hgt, hprod.trans (Nat.mul_comm p q)⟩
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    exact factor_counts_of_distinct_primes p q hp hq hpq

theorem product_injOn_prime_edges (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    Set.InjOn (fun e : ℕ × ℕ => e.1 * e.2) E := by
  intro e he f hf hprod
  rcases hE e he with ⟨hep, heq, heord⟩
  rcases hE f hf with ⟨hfp, hfq, hford⟩
  rcases prime_pair_product_injective e.1 e.2 f.1 f.2 hep heq hfp hfq heord hford hprod
    with ⟨hfirst, hsecond⟩
  exact Prod.ext hfirst hsecond

theorem reciprocal_sum_image_prime_edges (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    (∑ n ∈ E.image (fun e => e.1 * e.2), (1 : ℚ) / n) =
      ∑ e ∈ E, (1 : ℚ) / (e.1 * e.2 : ℕ) := by
  exact Finset.sum_image (product_injOn_prime_edges E hE)

theorem degree_eq_divisible_denominators (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (p : ℕ) (hp : p.Prime) :
    (E.filter fun e => e.1 = p).card + (E.filter fun e => e.2 = p).card =
      ((E.image fun e => e.1 * e.2).filter fun n => p ∣ n).card := by
  have hdis : Disjoint (E.filter fun e => e.1 = p) (E.filter fun e => e.2 = p) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have ho := (hE e (Finset.mem_filter.mp he).1).2.2
    have hfirst := (Finset.mem_filter.mp he).2
    have hsecond := (Finset.mem_filter.mp hf).2
    omega
  have heq : (E.filter fun e => e.1 = p ∨ e.2 = p) =
      E.filter (fun e => p ∣ e.1 * e.2) := by
    ext e
    simp only [Finset.mem_filter]
    by_cases he : e ∈ E
    · have hprime := hE e he
      simp [he, prime_dvd_product_iff_endpoint p e.1 e.2 hp hprime.1 hprime.2.1, eq_comm]
    · simp [he]
  calc
    _ = (E.filter fun e => e.1 = p ∨ e.2 = p).card := by
      rw [Finset.filter_or, Finset.card_union_of_disjoint hdis]
    _ = (E.filter fun e => p ∣ e.1 * e.2).card := congrArg Finset.card heq
    _ = ((E.filter fun e => p ∣ e.1 * e.2).image fun e => e.1 * e.2).card :=
      (Finset.card_image_of_injOn
        ((product_injOn_prime_edges E hE).mono (Finset.filter_subset _ _))).symm
    _ = _ := by rw [Finset.filter_image]

end Erdos306.Representation


/-! ## Maximum prime incidence nine forces reciprocal mass below one -/

/-! Finite prime graphs with maximum incidence at most nine have reciprocal
edge sum strictly below one. This does not assert any representation exists. -/

namespace Erdos306.PrimeIncidence

set_option maxRecDepth 2048

def smallPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
   59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127}

def headPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

def headPairs : Finset (ℕ × ℕ) :=
  (headPrimes ×ˢ headPrimes).filter (fun e => e.1 < e.2)

noncomputable def charge (p : ℕ) : ℝ :=
  if p ≤ 29 then (1 / 31 : ℝ) * (1 / p) - (1 / 31 : ℝ) ^ 2 / 2
  else (1 / (p : ℝ)) ^ 2 / 2

noncomputable def slack (e : ℕ × ℕ) : ℝ :=
  if e.1 ≤ 29 ∧ e.2 ≤ 29 then
    ((1 : ℝ) / e.1 - 1 / 31) * ((1 : ℝ) / e.2 - 1 / 31)
  else 0

theorem small_prime_table : (Finset.range 129).filter Nat.Prime = smallPrimes := by decide

theorem head_prime_table : (Finset.range 30).filter Nat.Prime = headPrimes := by decide

theorem mem_small_primes_iff (p : ℕ) : p ∈ smallPrimes ↔ p.Prime ∧ p ≤ 128 := by
  rw [← small_prime_table]
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hp⟩
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, hle⟩
    exact ⟨by omega, hp⟩

theorem mem_head_primes_iff (p : ℕ) : p ∈ headPrimes ↔ p.Prime ∧ p ≤ 29 := by
  rw [← head_prime_table]
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, hp⟩
    exact ⟨hp, by omega⟩
  · rintro ⟨hp, hle⟩
    exact ⟨by omega, hp⟩

theorem head_reciprocal_lower (p : ℕ) (hp : p.Prime) (hle : p ≤ 29) :
    (1 / 31 : ℝ) ≤ 1 / (p : ℝ) := by
  exact one_div_le_one_div_of_le (by exact_mod_cast hp.pos) (by exact_mod_cast (show p ≤ 31 by omega))

theorem tail_reciprocal_upper (p : ℕ) (hp : p.Prime) (hlt : 29 < p) :
    (1 : ℝ) / p ≤ 1 / 31 := by
  have h31 : 31 ≤ p := by
    by_contra h
    have heq : p = 30 := by omega
    subst p
    norm_num at hp
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h31)

theorem charge_nonnegative (p : ℕ) (hp : p.Prime) : 0 ≤ charge p := by
  unfold charge
  split_ifs with h
  · exact GraphDual.head_weight_nonnegative _ _ (by norm_num) (head_reciprocal_lower p hp h)
  · exact GraphDual.tail_weight_nonnegative _

theorem slack_nonnegative (e : ℕ × ℕ) (hp : e.1.Prime) (hq : e.2.Prime) :
    0 ≤ slack e := by
  unfold slack
  split_ifs with h
  · exact GraphDual.head_head_slack_nonnegative _ _ _
      (head_reciprocal_lower e.1 hp h.1) (head_reciprocal_lower e.2 hq h.2)
  · rfl

theorem edge_dual (e : ℕ × ℕ) (hp : e.1.Prime) (hq : e.2.Prime) :
    (1 : ℝ) / e.1 * (1 / e.2) ≤ charge e.1 + charge e.2 + slack e := by
  by_cases h1 : e.1 ≤ 29 <;> by_cases h2 : e.2 ≤ 29
  · simpa [charge, slack, h1, h2] using
      (GraphDual.head_head_identity ((1 : ℝ) / e.1) (1 / e.2) (1 / 31)).symm.le
  · simpa [charge, slack, h1, h2] using
      GraphDual.head_tail_bound ((1 : ℝ) / e.1) (1 / e.2) (1 / 31)
        (head_reciprocal_lower e.1 hp h1) (tail_reciprocal_upper e.2 hq (by omega))
  · have h := GraphDual.head_tail_bound ((1 : ℝ) / e.2) (1 / e.1) (1 / 31)
        (head_reciprocal_lower e.2 hq h2) (tail_reciprocal_upper e.1 hp (by omega))
    simpa [charge, slack, h1, h2, add_comm, mul_comm] using h
  · simpa [charge, slack, h1, h2] using
      GraphDual.tail_tail_bound ((1 : ℝ) / e.1) (1 / e.2)

theorem finite_charge_bound (V : Finset ℕ) (hV : ∀ p ∈ V, p.Prime) :
    (∑ p ∈ V, charge p) ≤ (∑ p ∈ smallPrimes, charge p) + 1 / 512 := by
  let T := V.filter (fun p => ¬p ≤ 128)
  have hsub : V.filter (fun p => p ≤ 128) ⊆ smallPrimes := by
    intro p hp
    exact (mem_small_primes_iff p).mpr ⟨hV p (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2⟩
  have hsmall : (∑ p ∈ V.filter (fun p => p ≤ 128), charge p) ≤
      ∑ p ∈ smallPrimes, charge p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => charge_nonnegative p ((mem_small_primes_iff p).mp hp).1)
  have hT : ∀ p ∈ T, p.Prime ∧ 128 < p := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    exact ⟨hV p hmem.1, by omega⟩
  have htail := OddTail.finite_large_prime_square_tail T hT
  have htailEq : (∑ p ∈ T, charge p) = (∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hlarge := (hT p hp).2
    simp [charge, show ¬p ≤ 29 by omega]
  have htailCharge : (∑ p ∈ T, charge p) ≤ 1 / 512 := by rw [htailEq]; linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not V (fun p => p ≤ 128) (f := charge)
  change (∑ p ∈ V.filter (fun p => p ≤ 128), charge p) + ∑ p ∈ T, charge p = _ at hsplit
  rw [← hsplit]
  exact add_le_add hsmall htailCharge

theorem finite_slack_bound (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    (∑ e ∈ E, slack e) ≤ ∑ e ∈ headPairs, slack e := by
  let T := E.filter (fun e => e.1 ≤ 29 ∧ e.2 ≤ 29)
  have hsum : (∑ e ∈ T, slack e) = ∑ e ∈ E, slack e := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases h : e.1 ≤ 29 ∧ e.2 ≤ 29 <;> simp [slack, h]
  have hsub : T ⊆ headPairs := by
    intro e he
    have hmem := Finset.mem_filter.mp he
    have hprime := hE e hmem.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_head_primes_iff e.1).mpr ⟨hprime.1, hmem.2.1⟩,
       (mem_head_primes_iff e.2).mpr ⟨hprime.2.1, hmem.2.2⟩⟩, hprime.2.2⟩
  rw [← hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro e he _
  have hmem := Finset.mem_product.mp (Finset.mem_filter.mp he).1
  exact slack_nonnegative e ((mem_head_primes_iff e.1).mp hmem.1).1
    ((mem_head_primes_iff e.2).mp hmem.2).1

theorem exact_numerical_bound :
    (9 : ℝ) * ((∑ p ∈ smallPrimes, charge p) + 1 / 512) +
      (∑ e ∈ headPairs, slack e) < 499 / 500 := by
  norm_num [smallPrimes, headPairs, headPrimes, charge, slack, Finset.sum_product,
    Finset.sum_filter]

theorem prime_edges_of_degree_le_nine (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdegree : ∀ p : ℕ, p.Prime → GraphDual.incidenceDegree E p ≤ 9) :
    (∑ e ∈ E, (1 : ℝ) / (e.1 * e.2 : ℕ)) < 499 / 500 := by
  let V := E.image Prod.fst ∪ E.image Prod.snd
  have hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V := by
    intro e he
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ he),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)⟩
  have hV : ∀ p ∈ V, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      exact (hE e he).1
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      exact (hE e he).2.1
  have hd := GraphDual.capacity_dual_with_slack_bound E V charge
    (fun e => (1 : ℝ) / e.1 * (1 / e.2)) slack 9
    (∑ e ∈ headPairs, slack e) hend (fun p hp => charge_nonnegative p (hV p hp))
    (fun p hp => hdegree p (hV p hp)) (fun e he => edge_dual e (hE e he).1 (hE e he).2.1)
    (finite_slack_bound E hE)
  have hc := finite_charge_bound V hV
  have hn := exact_numerical_bound
  have hmul : (∑ e ∈ E, (1 : ℝ) / e.1 * (1 / e.2)) < 499 / 500 := by
    norm_num only [Nat.cast_ofNat] at hd
    linarith
  simpa only [one_div_mul_one_div, Nat.cast_mul] using hmul

theorem prime_edges_sum_ge_one_forces_degree_ten (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hsum : 1 ≤ ∑ e ∈ E, (1 : ℝ) / (e.1 * e.2 : ℕ)) :
    ∃ p : ℕ, p.Prime ∧ 10 ≤ GraphDual.incidenceDegree E p := by
  by_contra h
  push Not at h
  have hdegree : ∀ p : ℕ, p.Prime → GraphDual.incidenceDegree E p ≤ 9 := by
    intro p hp
    have := h p hp
    omega
  have hbound := prime_edges_of_degree_le_nine E hE hdegree
  linarith

theorem semiprime_set_is_prime_edge_image (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2) :
    ∃ E : Finset (ℕ × ℕ),
      (∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      E.image (fun e => e.1 * e.2) = S := by
  classical
  have hf : ∀ n : S, ∃ e : ℕ × ℕ,
      e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2 ∧ n.val = e.1 * e.2 := by
    intro n
    obtain ⟨p, q, hp, hq, hpq, hn⟩ :=
      (Representation.factor_counts_iff_distinct_primes n.val).mp (hS n.val n.property)
    exact ⟨(p, q), hp, hq, hpq, hn⟩
  choose edge hedge using hf
  let E := S.attach.image edge
  refine ⟨E, ?_, ?_⟩
  · intro e he
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp he
    exact ⟨(hedge n).1, (hedge n).2.1, (hedge n).2.2.1⟩
  · calc
      E.image (fun e => e.1 * e.2) =
          S.attach.image (fun n => (edge n).1 * (edge n).2) := by
        rw [Finset.image_image]
        rfl
      _ = S.attach.image Subtype.val := by
        apply Finset.image_congr
        intro n hn
        exact (hedge n).2.2.2.symm
      _ = S := Finset.attach_image_val

theorem semiprime_sum_ge_one_forces_degree_ten (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hsum : 1 ≤ ∑ n ∈ S, (1 : ℝ) / n) :
    ∃ p : ℕ, p.Prime ∧ 10 ≤ (S.filter fun n => p ∣ n).card := by
  obtain ⟨E, hE, hprod⟩ := semiprime_set_is_prime_edge_image S hS
  have hsumImage := Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / n)
    (Representation.product_injOn_prime_edges E hE)
  rw [hprod] at hsumImage
  have hsumE : 1 ≤ ∑ e ∈ E, (1 : ℝ) / (e.1 * e.2 : ℕ) := by
    rw [← hsumImage]
    exact hsum
  obtain ⟨p, hp, hlarge⟩ := prime_edges_sum_ge_one_forces_degree_ten E hE hsumE
  have hcount := Representation.degree_eq_divisible_denominators E hE p hp
  change GraphDual.incidenceDegree E p = _ at hcount
  rw [hprod] at hcount
  exact ⟨p, hp, hcount ▸ hlarge⟩

end Erdos306.PrimeIncidence


/-! ## Shisheng Li's elementary proof of Erdős #306 (arXiv:2609.32140) -/

/-!
Erdős Problem #306 — Unit fractions with semiprime denominators:
an elementary proof of Erdős Problem #306.

Adapted to Lean 4.35.0-rc2 from Shisheng Li, arXiv:2609.32140v1 (Sep 2026),
"Unit fractions with semiprime denominators: an elementary proof of Erdős Problem #306"
(and https://github.com/daizisheng/erdos-306), licensed under CC BY 4.0
(http://creativecommons.org/licenses/by/4.0/).

The thirteen modules of the companion Lean development appear below as sections of
namespace `Erdos306`, in dependency order:
  1. `Basic`             — `nint x = ‖x‖` and `ee x = exp(2πix)`
  2. `Primes`            — Lemma 2.1 (`lem_cheb_erdos`, `centralBinom_le_primesIn`,
                           `primesIn_log_lower`, `lem_cheb`) and Corollary 2.2 (`cor_mertens`)
  3. `Construction`      — §4 bipartite graph `V × U`, `Large`, `Tuned`, `lem_tuning`
  4. `Counting`          — §5 finite Fourier inversion (`freq`, `phi`, `Ncount`, `eq_N`)
  5. `Table`             — §6 CRT row/column labels and Case I/II/III frequency split
  6. `Major`             — §7 Proposition 7.1 (`prop_major`)
  7. `Columns`           — §8 Lemmas 8.1–8.4 (`lem_cos`, `lem_count`, `lem_unique`, `lem_admissible`)
  8. `Minor`             — §9 Proposition 9.1 (`prop_minor`)
  9. `Asymptotics`       — `eps_le` and `eventually_large`
 10. `Core`              — Proposition 4.2 (`prop_core`) and Theorem 3.1 (`thm_small`)
 11. `Reduction`         — §3 prime-dilution reduction (`thm_main_of_small`)
 12. `Main`              — Theorem 1.1 (`erdos_306_semiprime_finset`), plus the arXiv v1 Ramanujan pathway
 13. `FormalConjectures` — `erdos_306_fc_core` proving the exact proposition of
                           `FormalConjectures.ErdosProblems.«306».erdos_306`
-/

/-! ### Li (2026): Basic notation -/
/-
Erdős Problem #306 — formalisation of S. Li, "Unit fractions with semiprime denominators:
an elementary proof of Erdős Problem #306" (arXiv:2609.32140v1).

Basic notation shared by all files:
* `nint x`  — the distance `‖x‖` from a real number to the nearest integer (paper §8);
* `ee x`    — the additive character `e(x) = exp(2πix)` (paper §5).
-/

open Real

namespace Erdos306

section

/-- `‖x‖`: the distance from the real number `x` to the nearest integer (paper, §8). -/
noncomputable def nint (x : ℝ) : ℝ := |x - round x|

/-- `e(x) = exp(2πix)` (paper, §5). -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `‖x‖ ≥ 0`. -/
lemma nint_nonneg (x : ℝ) : 0 ≤ nint x := abs_nonneg _

/-- `‖x‖ ≤ 1/2`. -/
lemma nint_le_half (x : ℝ) : nint x ≤ 1 / 2 := abs_sub_round x

/-- `‖x‖ ≤ |x - n|` for every integer `n`. -/
lemma nint_le_abs_sub (x : ℝ) (n : ℤ) : nint x ≤ |x - n| := round_le x n

/-- `‖x‖ ≤ |x|`. -/
lemma nint_le_abs (x : ℝ) : nint x ≤ |x| := by
  simpa using nint_le_abs_sub x 0

/-- `‖x + n‖ = ‖x‖` for integers `n`. -/
lemma nint_add_int (x : ℝ) (n : ℤ) : nint (x + n) = nint x := by
  unfold nint
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

/-- `‖x - n‖ = ‖x‖` for integers `n`. -/
lemma nint_sub_int (x : ℝ) (n : ℤ) : nint (x - n) = nint x := by
  have := nint_add_int x (-n)
  simpa [sub_eq_add_neg] using this

/-- `‖-x‖ = ‖x‖`. -/
lemma nint_neg (x : ℝ) : nint (-x) = nint x := by
  apply le_antisymm
  · calc nint (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := nint_le_abs_sub _ _
      _ = nint x := by unfold nint; push_cast; rw [← abs_neg]; ring_nf
  · calc nint x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := nint_le_abs_sub _ _
      _ = nint (-x) := by unfold nint; push_cast; rw [← abs_neg]; ring_nf

/-- Triangle inequality for `‖·‖`. -/
lemma nint_add_le (x z : ℝ) : nint (x + z) ≤ nint x + nint z := by
  calc nint (x + z) ≤ |x + z - ((round x + round z : ℤ) : ℝ)| := nint_le_abs_sub _ _
    _ = |(x - round x) + (z - round z)| := by push_cast; ring_nf
    _ ≤ nint x + nint z := abs_add_le _ _

/-- `‖x - z‖ ≤ ‖x‖ + ‖z‖`. -/
lemma nint_sub_le (x z : ℝ) : nint (x - z) ≤ nint x + nint z := by
  have := nint_add_le x (-z)
  rw [nint_neg] at this
  simpa [sub_eq_add_neg] using this

/-- If `‖x‖ ≤ d` then some integer `n` has `|x - n| ≤ d`. -/
lemma exists_int_of_nint_le {x d : ℝ} (h : nint x ≤ d) : ∃ n : ℤ, |x - n| ≤ d :=
  ⟨round x, h⟩

/-- `e(x + z) = e(x) e(z)`. -/
lemma ee_add (x z : ℝ) : ee (x + z) = ee x * ee z := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e(0) = 1`. -/
lemma ee_zero : ee 0 = 1 := by simp [ee]

/-- `|e(x)| = 1`. -/
lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

end

/-! ### Li (2026): §2, prime bounds -/
/-
§2 of the paper: two bounds for primes.

* `lem_cheb_erdos`, `lem_cheb` — Lemma 2.1 (Chebyshev-type bounds); the lower bound is proved
  here by Erdős' central-binomial argument (`centralBinom_le_primesIn`) instead of citing
  Ramanujan's inequality;
* `cor_mertens`                — Corollary 2.2 (the large side carries reciprocal mass `≥ 1/50`).
-/

section

open Real Finset

/-- The primes `p` with `a < p ≤ b`. -/
def primesIn (a b : ℕ) : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime

/-- Membership in `primesIn a b`. -/
lemma mem_primesIn {a b p : ℕ} : p ∈ primesIn a b ↔ a < p ∧ p ≤ b ∧ p.Prime := by
  simp [primesIn, and_assoc]

/-- **Lemma 2.1, first part** (Erdős' bound): `∏_{p ≤ x} p ≤ 4^x`.  This is Mathlib's
`primorial_le_four_pow`. -/
theorem lem_cheb_erdos (n : ℕ) : primorial n ≤ 4 ^ n := primorial_le_four_pow n

/-- Erdős' bound on the central binomial coefficient, without the Bertrand hypothesis:
`C(2n, n) ≤ (2n)^{⌊√(2n)⌋} · 4^{⌊2n/3⌋} · (2n)^{#(primes in (n, 2n])}`. -/
theorem centralBinom_le_primesIn (n : ℕ) (n_large : 2 < n) :
    Nat.centralBinom n ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ (primesIn n (2 * n)).card := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  set f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x with hf
  have hsplit : Nat.centralBinom n = (∏ p ∈ Finset.range (2 * n / 3 + 1), f p) *
      ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f p := by
    rw [Finset.prod_range_mul_prod_Ico _ (by omega)]
    exact n.prod_pow_factorization_centralBinom.symm
  rw [hsplit]
  apply mul_le_mul'
  · -- the small primes, exactly as in Mathlib's `centralBinom_le_of_no_bertrand_prime`
    let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
    have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
      refine Finset.prod_filter_of_ne fun p _ h => ?_
      contrapose! h; dsimp only [f]
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
    rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
      · exact Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
      have : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · -- the primes above `2n/3`: those `≤ n` do not divide `C(2n, n)`; the rest lie in `(n, 2n]`
    have hsub : ∏ p ∈ Finset.Ico (2 * n / 3 + 1) (2 * n + 1), f p =
        ∏ p ∈ primesIn n (2 * n), f p := by
      symm
      apply Finset.prod_subset
      · intro p hp
        obtain ⟨h1, h2, -⟩ := mem_primesIn.1 hp
        rw [Finset.mem_Ico]; omega
      · intro p hp hp'
        rw [Finset.mem_Ico] at hp
        dsimp only [f]
        by_cases hpr : p.Prime
        · have hpn : p ≤ n := by
            by_contra h
            exact hp' (mem_primesIn.2 ⟨by omega, by omega, hpr⟩)
          rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large hpn (by omega),
            _root_.pow_zero]
        · rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hpr, _root_.pow_zero]
    rw [hsub, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)

/-- Logarithmic form: `#(primes in (n, 2n]) · log(2n) ≥ (n log 4)/3 − log(2n+1) − √(2n) log(2n)`. -/
theorem primesIn_log_lower (n : ℕ) (n_large : 2 < n) :
    (n : ℝ) * log 4 / 3 - log (2 * n + 1) - √(2 * n : ℝ) * log (2 * n) ≤
      ((primesIn n (2 * n)).card : ℝ) * log (2 * n) := by
  have h4 := Nat.four_pow_le_two_mul_add_one_mul_centralBinom n
  have hc := centralBinom_le_primesIn n n_large
  have key : (4 : ℝ) ^ n ≤ (2 * n + 1) *
      ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ (primesIn n (2 * n)).card) := by
    have := h4.trans (Nat.mul_le_mul_left _ hc)
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ 2 * n := by norm_cast; omega
  have hl2n : 0 ≤ log (2 * n : ℝ) := log_nonneg hn
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  have hsq : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ≤ √(2 * n : ℝ) := by
    have := @Real.nat_sqrt_le_real_sqrt (2 * n); push_cast at this; exact this
  have hdiv : (((2 * n / 3 : ℕ) : ℝ)) ≤ 2 * n / 3 := by
    have := (Nat.cast_div_le (α := ℝ) (m := 2 * n) (n := 3)); push_cast at this; exact this
  have hl4 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hsq hl2n, mul_le_mul_of_nonneg_right hdiv hl4]

/-- **Lemma 2.1, second part**: for all sufficiently large real `x`,
`x / (7 log x) ≤ π(x) - π(x/2)`, i.e. there are at least `x/(7 log x)` primes in `(x/2, x]`.
The paper derives this from Ramanujan's inequality; here it is proved for `x ≥ 10^8` from
`primesIn_log_lower`, which is all the paper uses. -/
theorem lem_cheb : ∃ x0 : ℝ, ∀ x ≥ x0,
    x / (7 * log x) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) := by
  refine ⟨100 ^ 4, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans (by positivity) hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hlog : 0 < log x := Real.log_pos hx1
  set n := ⌊x / 2⌋₊ with hn_def
  have hn1 : x / 2 - 1 < n := Nat.sub_one_lt_floor _
  have hn2 : (n : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hn3 : 2 < n := by
    have : (2 : ℝ) < n := by linarith
    exact_mod_cast this
  -- the primes of `(n, 2n]` lie in `(x/2, x]`
  have hsub : primesIn n (2 * n) ⊆ primesIn ⌊x / 2⌋₊ ⌊x⌋₊ := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIn.1 hp
    refine mem_primesIn.2 ⟨h1, le_trans h2 ?_, h3⟩
    apply Nat.le_floor; push_cast; linarith
  have hcard : ((primesIn n (2 * n)).card : ℝ) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hmain := primesIn_log_lower n hn3
  -- `r = x^{1/4}`, so that `log x ≤ 4r` and `√x = r²`
  set s := √x with hs
  set r := √s with hr
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hss : s * s = x := Real.mul_self_sqrt hx0
  have hrr : r * r = s := Real.mul_self_sqrt hs0
  have hr100 : 100 ≤ r := by
    have h1 : (100 : ℝ) ^ 2 ≤ s := by
      rw [hs, show ((100 : ℝ) ^ 2) = √((100 ^ 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [hr, show (100 : ℝ) = √(100 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h1
  have hrpos : 0 < r := by linarith
  have hlogx : log x ≤ 4 * r := by
    have : log x = 4 * log r := by
      rw [← hss, ← hrr, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]; ring
    rw [this]; nlinarith [Real.log_le_sub_one_of_pos hrpos]
  have h2n_pos : (0 : ℝ) < 2 * n := by positivity
  have h2n_le : (2 * n : ℝ) ≤ x := by linarith
  have hlog2n : log (2 * n : ℝ) ≤ log x := Real.log_le_log h2n_pos h2n_le
  have hlog2n0 : 0 ≤ log (2 * n : ℝ) := log_nonneg (by linarith)
  have hsqrt2n : √(2 * n : ℝ) ≤ s := Real.sqrt_le_sqrt h2n_le
  have hlog2n1 : log (2 * n + 1 : ℝ) ≤ 1 + 4 * r := by
    have h := Real.log_le_log (by positivity) (show (2 * n + 1 : ℝ) ≤ 2 * x by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at h
    have : log (2 : ℝ) < 1 := by
      have := Real.log_two_lt_d9; norm_num at this; linarith
    linarith
  have hl4 : 1.38 < log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hk0 : (0 : ℝ) ≤ (primesIn n (2 * n)).card := by positivity
  -- lower bound on `k log x`
  have hklog : (n : ℝ) * log 4 / 3 - (1 + 4 * r) - s * (4 * r) ≤
      ((primesIn n (2 * n)).card : ℝ) * log x := by
    have e1 : √(2 * n : ℝ) * log (2 * n) ≤ s * (4 * r) :=
      mul_le_mul hsqrt2n (hlog2n.trans hlogx) hlog2n0 hs0
    have e2 : ((primesIn n (2 * n)).card : ℝ) * log (2 * n) ≤
        ((primesIn n (2 * n)).card : ℝ) * log x := mul_le_mul_of_nonneg_left hlog2n hk0
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hxr : x = r * r * (r * r) := by rw [hrr, hss]
  have hnl : (x / 2 - 1) * 1.38 ≤ (n : ℝ) * log 4 := by
    apply mul_le_mul (le_of_lt hn1) (le_of_lt hl4) (by norm_num) (by positivity)
  have hcl := mul_le_mul_of_nonneg_right hcard hlog.le
  rw [← hrr] at hklog
  nlinarith [mul_pos hrpos hrpos, mul_pos (mul_pos hrpos hrpos) hrpos]

/-- Telescoping bound for the harmonic sum used in Corollary 2.2:
`∑_{a ≤ i < a+n} 1/(i+1) ≥ log((a+n+1)/(a+1))` (from `log(1+1/m) ≤ 1/m`). -/
lemma harmonic_ge_log (a n : ℕ) :
    log (((a + n + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.Ico a (a + n), (1 : ℝ) / ((i : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have hpos1 : (0 : ℝ) < ((a + n + 1 : ℕ) : ℝ) := by positivity
    have hpos2 : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
    have hsplit : log (((a + n + 1 + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) =
        log (((a + n + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) +
          log (((a + n + 2 : ℕ) : ℝ) / ((a + n + 1 : ℕ) : ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hstep : log (((a + n + 2 : ℕ) : ℝ) / ((a + n + 1 : ℕ) : ℝ)) ≤
        1 / (((a + n : ℕ) : ℝ) + 1) := by
      refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) (le_of_eq ?_)
      field_simp
      push_cast; ring
    rw [hsplit]
    linarith

/-- One dyadic block in the proof of Corollary 2.2: if `2^{i+1}` is past the threshold of
Lemma 2.1, then `∑_{2^i < p ≤ 2^{i+1}} 1/p ≥ 1/(7 (i+1) log 2)`. -/
lemma dyadic_block {x0 : ℝ} (hx0 : ∀ x ≥ x0, x / (7 * log x) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ))
    (i : ℕ) (hi : x0 ≤ (2 : ℝ) ^ (i + 1)) :
    1 / (7 * ((i : ℝ) + 1) * log 2) ≤ ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
  have h := hx0 _ hi
  have hfl1 : ⌊(2 : ℝ) ^ (i + 1) / 2⌋₊ = 2 ^ i := by
    rw [pow_succ, mul_div_assoc, div_self (by norm_num), mul_one]
    exact_mod_cast Nat.floor_natCast (2 ^ i)
  have hfl2 : ⌊(2 : ℝ) ^ (i + 1)⌋₊ = 2 ^ (i + 1) := by exact_mod_cast Nat.floor_natCast _
  rw [hfl1, hfl2, Real.log_pow] at h
  have hsum : ((primesIn (2 ^ i) (2 ^ (i + 1))).card : ℝ) * (1 / (2 : ℝ) ^ (i + 1)) ≤
      ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIn.1 hp
    apply one_div_le_one_div_of_le (by exact_mod_cast h3.pos)
    exact_mod_cast h2
  refine le_trans ?_ hsum
  have h2pos : (0 : ℝ) < 2 ^ (i + 1) := by positivity
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  calc 1 / (7 * ((i : ℝ) + 1) * log 2)
      = (2 : ℝ) ^ (i + 1) / (7 * (((i + 1 : ℕ) : ℝ) * log 2)) * (1 / (2 : ℝ) ^ (i + 1)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

/-- **Corollary 2.2**: for all sufficiently large `y`, `∑_{y^8 < p ≤ y^9} 1/p ≥ c_U = 1/50`. -/
theorem cor_mertens : ∃ y0 : ℕ, ∀ y ≥ y0,
    (1 : ℝ) / 50 ≤ ∑ p ∈ primesIn (y ^ 8) (y ^ 9), (1 : ℝ) / p := by
  obtain ⟨x0, hx0⟩ := lem_cheb
  set K0 : ℕ := max 75 ⌈x0⌉₊ with hK0
  refine ⟨2 ^ K0, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by have := Nat.one_le_two_pow (n := K0); omega
  set k := Nat.log 2 y with hk
  have hkK : K0 ≤ k := (Nat.le_log_iff_pow_le (by norm_num) hy0).2 hy
  have hk75 : 75 ≤ k := le_trans (le_max_left _ _) hkK
  have hkx : ⌈x0⌉₊ ≤ k := le_trans (le_max_right _ _) hkK
  have hlo : 2 ^ k ≤ y := Nat.pow_log_le_self 2 hy0
  have hhi : y < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) y
  -- the blocks `(2^i, 2^{i+1}]`, `8k+8 ≤ i < 9k`, lie inside `(y^8, y^9]`
  have hsub : (Finset.Ico (8 * k + 8) (9 * k)).biUnion
      (fun i => primesIn (2 ^ i) (2 ^ (i + 1))) ⊆ primesIn (y ^ 8) (y ^ 9) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIn.1 hpi
    rw [Finset.mem_Ico] at hi
    refine mem_primesIn.2 ⟨?_, ?_, h3⟩
    · calc y ^ 8 < (2 ^ (k + 1)) ^ 8 := Nat.pow_lt_pow_left hhi (by norm_num)
        _ = 2 ^ (8 * k + 8) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi.1
        _ < p := h1
    · calc p ≤ 2 ^ (i + 1) := h2
        _ ≤ 2 ^ (9 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ k) ^ 9 := by rw [← pow_mul]; ring_nf
        _ ≤ y ^ 9 := Nat.pow_le_pow_left hlo 9
  have hdisj : (↑(Finset.Ico (8 * k + 8) (9 * k)) : Set ℕ).PairwiseDisjoint
      (fun i => primesIn (2 ^ i) (2 ^ (i + 1))) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    obtain ⟨a1, a2, -⟩ := mem_primesIn.1 hpi
    obtain ⟨b1, b2, -⟩ := mem_primesIn.1 hpj
    rcases lt_or_gt_of_ne hij with h | h
    · have : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
      omega
    · have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      omega
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  -- sum of the block bounds
  have hblocks : (1 / (7 * log 2)) * ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1)
      ≤ ∑ p ∈ primesIn (y ^ 8) (y ^ 9), (1 : ℝ) / p := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), 1 / (7 * log 2) * (1 / ((i : ℝ) + 1))
        ≤ ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k),
            ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Ico] at hi
          have hx : x0 ≤ (2 : ℝ) ^ (i + 1) := by
            calc x0 ≤ (⌈x0⌉₊ : ℝ) := Nat.le_ceil x0
              _ ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
              _ ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_two_pow_self).le
              _ = (2 : ℝ) ^ (i + 1) := by push_cast; ring
          have := dyadic_block hx0 i hx
          calc 1 / (7 * log 2) * (1 / ((i : ℝ) + 1)) = 1 / (7 * ((i : ℝ) + 1) * log 2) := by
                field_simp
            _ ≤ _ := this
      _ = ∑ p ∈ (Finset.Ico (8 * k + 8) (9 * k)).biUnion
            (fun i => primesIn (2 ^ i) (2 ^ (i + 1))), (1 : ℝ) / p := (Finset.sum_biUnion hdisj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  -- the harmonic sum is at least `log((9k+1)/(8k+9)) ≥ log 1.11 ≥ (7/50) log 2`
  have hharm := harmonic_ge_log (8 * k + 8) (k - 8)
  have e1 : 8 * k + 8 + (k - 8) = 9 * k := by omega
  rw [e1] at hharm
  have hratio : (1.11 : ℝ) ≤ ((9 * k + 1 : ℕ) : ℝ) / ((8 * k + 8 + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have : (75 : ℝ) ≤ k := by exact_mod_cast hk75
    push_cast; linarith
  have hlog111 : 7 * log 2 / 50 ≤ log (1.11 : ℝ) := by
    have h1 : log ((2 : ℝ) ^ 7) ≤ log ((1.11 : ℝ) ^ 50) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogr := Real.log_le_log (by norm_num) hratio
  have hH : 7 * log 2 / 50 ≤ ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1) := by
    linarith
  calc (1 : ℝ) / 50 = (1 / (7 * log 2)) * (7 * log 2 / 50) := by field_simp
    _ ≤ (1 / (7 * log 2)) * ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ _ := hblocks

end

/-! ### Li (2026): §4, the bipartite construction -/
/-
§4 of the paper: the construction `V = {2} ∪ B ∪ W`, `U = U(Y)`, the tuning lemma, and the
reduction of Theorem 3.1 to Proposition 4.2 (a congruence mod 1 forces equality).

Conventions.  The target is a rational `τ` (the paper's `a/b`, so `b = τ.den`); `y` is a natural
number (the paper allows real `y`; natural `y` suffices and makes `y^7` an integer).
Edges `vu` of the complete bipartite graph `V × U` are pairs `(v, u) : ℕ × ℕ`.
The endpoint `Y` is a natural number with `y^8 ≤ Y ≤ y^9` (the paper takes `Y` prime; only
the set `U(Y)` matters, and `U(Y) = U(max U(Y))`).
-/

section

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `B`: the primes dividing `b = τ.den`. -/
def Bset : Finset ℕ := τ.den.primeFactors

/-- `W = {w prime : y^2 < w ≤ 2y^2}`: the test primes. -/
def Wset : Finset ℕ := primesIn (y ^ 2) (2 * y ^ 2)

/-- The small side `V = {2} ∪ B ∪ W`. -/
def Vset : Finset ℕ := insert 2 (Bset τ ∪ Wset y)

/-- The large side `U = U(Y) = {u prime : y^8 < u ≤ Y}`. -/
def Uset : Finset ℕ := primesIn (y ^ 8) Y

/-- `H_V = ∑_{v ∈ V} 1/v`. -/
noncomputable def HV : ℝ := ∑ v ∈ Vset τ y, (1 : ℝ) / v

/-- The edge set `A = A(Y) = V × U`. -/
def Aset : Finset (ℕ × ℕ) := Vset τ y ×ˢ Uset y Y

/-- `μ(Y) = ½ ∑_{(v,u) ∈ A} 1/(uv)`: half the total mass of `A`. -/
noncomputable def mu : ℝ := (1 / 2) * ∑ p ∈ Aset τ y Y, (1 : ℝ) / (p.1 * p.2)

/-- `σ(S) = ∑_{(v,u) ∈ S} 1/(vu)` (a rational number). -/
def sigma (S : Finset (ℕ × ℕ)) : ℚ := ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2)

/-- `L = ∏_{p ∈ V ∪ U} p`. -/
def Lnum : ℕ := ∏ p ∈ Vset τ y ∪ Uset y Y, p

/-- `δ = 1/(400 log y)` (paper §8.1). -/
noncomputable def delta : ℝ := 1 / (400 * log y)

/-- `ε = exp(-|W| δ² / 8)` (paper §8.1). -/
noncomputable def eps : ℝ := exp (-((Wset y).card * delta y ^ 2 / 8))

/-- `δ_a = 1/(8y²)` (paper §8.2). -/
noncomputable def deltaA : ℝ := 1 / (8 * (y : ℝ) ^ 2)

/-- All the inequalities that the paper asserts "for `y` sufficiently large (in terms of `b`)".
Each field is used at exactly the place indicated; `eventually_large` (file `Asymptotics`)
shows that they all hold for all large `y`. -/
structure Large : Prop where
  /-- a harmless lower bound on `y` -/
  y_ge : 3 ≤ y
  /-- `y > max B` (§4) -/
  B_lt : ∀ r ∈ Bset τ, r < y
  /-- eq. (1): `|W| ≥ y²/(8 log y)` -/
  card_W : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card
  /-- eq. (1) / Corollary 2.2: `∑_{u ∈ U(y^9)} 1/u ≥ c_U = 1/50` -/
  mertens : (1 : ℝ) / 50 ≤ ∑ u ∈ Uset y (y ^ 9), (1 : ℝ) / u
  /-- Lemma 4.1: `H_V/(2y^8) < τ/2` -/
  tune : HV τ y / (2 * (y : ℝ) ^ 8) < τ / 2
  /-- Proposition 7.1, step 4: `y > 2 H_V` -/
  major : 2 * HV τ y < y
  /-- Lemma 8.2: `y²/(20 log y) + 10 ≤ y²/(16 log y)` -/
  count : (y : ℝ) ^ 2 / (20 * log y) + 10 ≤ (y : ℝ) ^ 2 / (16 * log y)
  /-- Proposition 9.1, case II: `y^{-3} ≤ δ/2` -/
  phase : 1 / (y : ℝ) ^ 3 ≤ delta y / 2
  /-- Proposition 9.1, case III: `e^{-2δ_a²} + Yε ≤ e^{-δ_a²}` (with `Y ≤ y^9`) -/
  colIII : exp (-2 * deltaA y ^ 2) + (y : ℝ) ^ 9 * eps y ≤ exp (-(deltaA y ^ 2))
  /-- Proposition 9.1, case III: `2b·16^{y²}·exp(-τy⁴/(64 H_V)) ≤ 1/4` -/
  caseIII : 2 * (τ.den : ℝ) * 16 ^ (y ^ 2) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)))
    ≤ 1 / 4
  /-- Proposition 9.1, case II: `3y^{25} ε e^{y^{18} ε} ≤ 1/4` -/
  caseII : 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) ≤ 1 / 4

/-- The conclusions of the tuning lemma (Lemma 4.1) for the endpoint `Y`. -/
structure Tuned : Prop where
  lo : y ^ 8 ≤ Y
  hi : Y ≤ y ^ 9
  beta_nonpos : mu τ y Y ≤ τ
  beta_ge : (τ : ℝ) - mu τ y Y ≤ HV τ y / (2 * (y : ℝ) ^ 8)
  mu_ge : (τ : ℝ) / 2 ≤ mu τ y Y
  card_U : (τ : ℝ) * (y : ℝ) ^ 8 / HV τ y ≤ (Uset y Y).card

/-! ### Elementary facts about the construction -/

section facts

variable {τ y Y}

/-- Membership in `W`. -/
lemma mem_Wset {w : ℕ} : w ∈ Wset y ↔ y ^ 2 < w ∧ w ≤ 2 * y ^ 2 ∧ w.Prime := mem_primesIn

/-- Membership in `U(Y)`. -/
lemma mem_Uset {u : ℕ} : u ∈ Uset y Y ↔ y ^ 8 < u ∧ u ≤ Y ∧ u.Prime := mem_primesIn

/-- Membership in `V = {2} ∪ B ∪ W`. -/
lemma mem_Vset {v : ℕ} : v ∈ Vset τ y ↔ v = 2 ∨ v ∈ Bset τ ∨ v ∈ Wset y := by
  simp [Vset]

/-- Membership in `A = V × U`. -/
lemma mem_Aset {p : ℕ × ℕ} : p ∈ Aset τ y Y ↔ p.1 ∈ Vset τ y ∧ p.2 ∈ Uset y Y := by
  simp [Aset]

/-- Every element of `V` is prime. -/
lemma prime_of_mem_Vset {v : ℕ} (hv : v ∈ Vset τ y) : v.Prime := by
  rcases mem_Vset.1 hv with h | h | h
  · subst h; exact Nat.prime_two
  · exact Nat.prime_of_mem_primeFactors h
  · exact (mem_Wset.1 h).2.2

/-- Every element of `U` is prime. -/
lemma prime_of_mem_Uset {u : ℕ} (hu : u ∈ Uset y Y) : u.Prime := (mem_Uset.1 hu).2.2

/-- `2 ∈ V`. -/
lemma two_mem_Vset : 2 ∈ Vset τ y := by simp [Vset]

/-- `W ⊆ V`. -/
lemma Wset_subset_Vset : Wset y ⊆ Vset τ y := by
  intro w hw; simp [Vset, hw]

/-- Every `v ∈ V` satisfies `2 ≤ v ≤ 2y²`. -/
lemma le_of_mem_Vset (hL : Large τ y) {v : ℕ} (hv : v ∈ Vset τ y) : 2 ≤ v ∧ v ≤ 2 * y ^ 2 := by
  refine ⟨(prime_of_mem_Vset hv).two_le, ?_⟩
  have hy := hL.y_ge
  have hyy : y ≤ y ^ 2 := Nat.le_self_pow (by norm_num) y
  rcases mem_Vset.1 hv with h | h | h
  · omega
  · have := hL.B_lt v h; omega
  · exact (mem_Wset.1 h).2.1

/-- Every `u ∈ U(Y)` satisfies `y^8 < u ≤ Y`. -/
lemma bounds_of_mem_Uset {u : ℕ} (hu : u ∈ Uset y Y) : y ^ 8 < u ∧ u ≤ Y :=
  ⟨(mem_Uset.1 hu).1, (mem_Uset.1 hu).2.1⟩

/-- `V` and `U` are disjoint (they live at different scales). -/
lemma two_y_sq_lt (hL : Large τ y) : 2 * y ^ 2 < y ^ 8 := by
  have hy := hL.y_ge
  have h6 : 2 < y ^ 6 := by
    calc 2 < 3 ^ 6 := by norm_num
      _ ≤ y ^ 6 := Nat.pow_le_pow_left hy 6
  have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
  rw [this]
  have : 0 < y ^ 2 := by positivity
  nlinarith

/-- `V` and `U` are disjoint (they live at different scales, `v ≤ 2y² < y^8 < u`). -/
lemma disjoint_V_U (hL : Large τ y) : Disjoint (Vset τ y) (Uset y Y) := by
  rw [Finset.disjoint_left]
  intro v hv hu
  have h1 := (le_of_mem_Vset hL hv).2
  have h2 := (bounds_of_mem_Uset hu).1
  have := two_y_sq_lt hL
  omega

/-- `b ∣ L`: the primes of `b` are among the primes of the graph (`b` squarefree). -/
lemma den_dvd_L (hsq : Squarefree τ.den) : τ.den ∣ Lnum τ y Y := by
  have h : ∏ p ∈ Bset τ, p = τ.den := Nat.prod_primeFactors_of_squarefree hsq
  rw [← h]
  apply Finset.prod_dvd_prod_of_subset
  intro r hr
  exact Finset.mem_union_left _ (by simp [Vset, hr])

/-- every edge `vu` divides `L` -/
lemma edge_dvd_L (hL : Large τ y) {p : ℕ × ℕ} (hp : p ∈ Aset τ y Y) :
    p.1 * p.2 ∣ Lnum τ y Y := by
  obtain ⟨hv, hu⟩ := mem_Aset.1 hp
  have hne : p.1 ≠ p.2 := by
    intro h
    exact Finset.disjoint_left.1 (disjoint_V_U (Y := Y) hL) hv (h ▸ hu)
  have : ∏ x ∈ ({p.1, p.2} : Finset ℕ), x = p.1 * p.2 := Finset.prod_pair hne
  rw [← this]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact Finset.mem_union_left _ hv
  · exact Finset.mem_union_right _ hu

/-- `μ = ½ H_V ∑_{u ∈ U} 1/u`. -/
lemma mu_eq : mu τ y Y = (1 / 2) * HV τ y * ∑ u ∈ Uset y Y, (1 : ℝ) / u := by
  unfold mu HV Aset
  rw [Finset.sum_product, mul_assoc, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
  rw [div_mul_div_comm, one_mul]

/-- eq. (1), second item: `∏_{v ∈ V} v ≤ 2 b 16^{y²}`. -/
lemma prod_V_le :
    ((∏ v ∈ Vset τ y, v : ℕ) : ℝ) ≤ 2 * τ.den * 16 ^ (y ^ 2) := by
  -- `∏_{insert 2 s} ∣ 2 ∏_s`
  have h1 : ∏ v ∈ Vset τ y, v ∣ 2 * ∏ v ∈ Bset τ ∪ Wset y, v := by
    unfold Vset
    by_cases h2 : 2 ∈ Bset τ ∪ Wset y
    · rw [Finset.insert_eq_of_mem h2]; exact Dvd.intro_left _ rfl
    · rw [Finset.prod_insert h2]
  have h2 : ∏ v ∈ Bset τ ∪ Wset y, v ∣ (∏ v ∈ Bset τ, v) * ∏ v ∈ Wset y, v := by
    rw [← Finset.prod_union_inter]; exact Dvd.intro _ rfl
  have hB : ∏ v ∈ Bset τ, v ∣ τ.den := Nat.prod_primeFactors_dvd τ.den
  have hW : ∏ v ∈ Wset y, v ∣ primorial (2 * y ^ 2) := by
    unfold primorial
    apply Finset.prod_dvd_prod_of_subset
    intro w hw
    obtain ⟨-, h2, h3⟩ := mem_Wset.1 hw
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h3⟩
  have hprim := primorial_le_four_pow (2 * y ^ 2)
  have hden := τ.den_pos
  have hpp : 0 < primorial (2 * y ^ 2) := primorial_pos _
  have hN : ∏ v ∈ Vset τ y, v ≤ 2 * τ.den * 16 ^ (y ^ 2) := by
    have h3 : ∏ v ∈ Vset τ y, v ∣ 2 * (τ.den * primorial (2 * y ^ 2)) :=
      h1.trans (mul_dvd_mul_left 2 (h2.trans (mul_dvd_mul hB hW)))
    have h4 := Nat.le_of_dvd (by positivity) h3
    have h5 : (4 : ℕ) ^ (2 * y ^ 2) = 16 ^ (y ^ 2) := by
      rw [pow_mul]; norm_num
    calc ∏ v ∈ Vset τ y, v ≤ 2 * (τ.den * primorial (2 * y ^ 2)) := h4
      _ ≤ 2 * (τ.den * 4 ^ (2 * y ^ 2)) := by gcongr
      _ = 2 * τ.den * 16 ^ (y ^ 2) := by rw [h5]; ring
  exact_mod_cast hN

/-- eq. (1), third item: `½ ≤ H_V ≤ 3/2 + ∑_{r ∈ B} 1/r`. -/
lemma HV_bounds (hL : Large τ y) :
    1 / 2 ≤ HV τ y ∧ HV τ y ≤ 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r := by
  have hnn : ∀ s : Finset ℕ, ∀ i ∈ s, (0 : ℝ) ≤ 1 / (i : ℝ) := fun _ _ _ => by positivity
  constructor
  · have := Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / v) (hnn _)
      (two_mem_Vset (τ := τ) (y := y))
    simpa [HV] using this
  · -- `∑_{w ∈ W} 1/w ≤ |W|/y² ≤ 1`
    have hy : (0 : ℝ) < (y : ℝ) ^ 2 := by have := hL.y_ge; positivity
    have hWsum : ∑ w ∈ Wset y, (1 : ℝ) / w ≤ 1 := by
      have hcard : (Wset y).card ≤ y ^ 2 := by
        unfold Wset primesIn
        refine (Finset.card_filter_le _ _).trans ?_
        simp only [Nat.card_Ioc]
        omega
      calc ∑ w ∈ Wset y, (1 : ℝ) / w ≤ ∑ w ∈ Wset y, (1 : ℝ) / (y : ℝ) ^ 2 := by
            refine Finset.sum_le_sum (fun w hw => ?_)
            have h1 := (mem_Wset.1 hw).1
            have h2 : (y : ℝ) ^ 2 ≤ w := by exact_mod_cast h1.le
            exact one_div_le_one_div_of_le hy h2
        _ = (Wset y).card / (y : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 := by
            rw [div_le_one hy]; exact_mod_cast hcard
    have hunion : ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v ≤
        ∑ r ∈ Bset τ, (1 : ℝ) / r + ∑ w ∈ Wset y, (1 : ℝ) / w := by
      rw [← Finset.sum_union_inter]
      have := Finset.sum_nonneg (hnn (Bset τ ∩ Wset y))
      linarith
    have hins : HV τ y ≤ 1 / 2 + ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v := by
      unfold HV Vset
      by_cases h2 : 2 ∈ Bset τ ∪ Wset y
      · rw [Finset.insert_eq_of_mem h2]; linarith
      · rw [Finset.sum_insert h2]; norm_num
    linarith

/-- `H_V > 0`. -/
lemma HV_pos (hL : Large τ y) : 0 < HV τ y := by
  have := (HV_bounds hL).1; linarith

end facts

/-! ### Lemma 4.1 (Tuning) -/

/-- Auxiliary: `U(y^8) = ∅`. -/
lemma Uset_eq_empty (y : ℕ) : Uset y (y ^ 8) = ∅ := by
  ext u; simp only [mem_Uset, Finset.notMem_empty, iff_false]; omega

/-- Adding the next integer `Y+1` adds at most one prime, of reciprocal `< 1/y^8`. -/
lemma sumU_succ_le {y Y : ℕ} (hy : 0 < y) (hY : y ^ 8 ≤ Y) :
    ∑ u ∈ Uset y (Y + 1), (1 : ℝ) / u ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u + 1 / (y : ℝ) ^ 8 := by
  have hsub : Uset y (Y + 1) ⊆ insert (Y + 1) (Uset y Y) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := mem_Uset.1 hu
    rcases Nat.lt_or_ge u (Y + 1) with h | h
    · exact Finset.mem_insert_of_mem (mem_Uset.2 ⟨h1, by omega, h3⟩)
    · rw [show u = Y + 1 by omega]; exact Finset.mem_insert_self _ _
  have hnotin : Y + 1 ∉ Uset y Y := by intro h; have := (mem_Uset.1 h).2.1; omega
  calc ∑ u ∈ Uset y (Y + 1), (1 : ℝ) / u ≤ ∑ u ∈ insert (Y + 1) (Uset y Y), (1 : ℝ) / u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 / ((Y + 1 : ℕ) : ℝ) + ∑ u ∈ Uset y Y, (1 : ℝ) / u := Finset.sum_insert hnotin
    _ ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u + 1 / (y : ℝ) ^ 8 := by
        have : (y : ℝ) ^ 8 ≤ ((Y + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : y ^ 8 ≤ Y + 1)
        have hpos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
        have := one_div_le_one_div_of_le hpos this; linarith

/-- `∑_{u ∈ U} 1/u ≤ |U|/y^8`. -/
lemma sumU_le_card {y Y : ℕ} (hy : 0 < y) :
    ∑ u ∈ Uset y Y, (1 : ℝ) / u ≤ (Uset y Y).card / (y : ℝ) ^ 8 := by
  have hpos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
  calc ∑ u ∈ Uset y Y, (1 : ℝ) / u ≤ ∑ u ∈ Uset y Y, 1 / (y : ℝ) ^ 8 := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have h1 := (mem_Uset.1 hu).1
        exact one_div_le_one_div_of_le hpos (by exact_mod_cast h1.le)
    _ = (Uset y Y).card / (y : ℝ) ^ 8 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Lemma 4.1 (Tuning).**  For `0 < τ ≤ η = 1/400` and `y` large, there is an endpoint
`Y ∈ [y^8, y^9]` with `0 ≤ τ - μ(Y) ≤ H_V/(2y^8)`, `μ(Y) ≥ τ/2` and `|U| ≥ τ y^8 / H_V`.
(Add the primes of `(y^8, y^9]` one at a time; stop at the last point where `μ ≤ τ`.) -/
theorem lem_tuning {τ : ℚ} {y : ℕ} (h0 : 0 < τ) (hη : τ ≤ 1 / 400) (hL : Large τ y) :
    ∃ Y, Tuned τ y Y := by
  classical
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast h0
  have hτη : (τ : ℝ) ≤ 1 / 400 := by
    have := (Rat.cast_le (K := ℝ)).2 hη; simpa using this
  have hHV := HV_bounds hL
  have hHVpos := HV_pos hL
  have hy : 0 < y := by have := hL.y_ge; omega
  have hy8 : y ^ 8 ≤ y ^ 9 := Nat.pow_le_pow_right hy (by norm_num)
  set T := (Finset.Icc (y ^ 8) (y ^ 9)).filter (fun Z => mu τ y Z ≤ τ) with hT
  have hne : y ^ 8 ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_rfl, hy8⟩, ?_⟩
    rw [mu_eq, Uset_eq_empty]; simp; exact h0.le
  set Y := T.max' ⟨_, hne⟩ with hYdef
  have hYT : Y ∈ T := Finset.max'_mem _ _
  simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hYT
  obtain ⟨⟨hYlo, hYhi⟩, hmuY⟩ := hYT
  -- the full range has `μ(y^9) ≥ c_U/4 = 1/200 > τ`
  have hfull : τ < mu τ y (y ^ 9) := by
    rw [mu_eq]
    have := hL.mertens
    have : (1 : ℝ) / 2 * (1 / 2) * (1 / 50) ≤ 1 / 2 * HV τ y * ∑ u ∈ Uset y (y ^ 9), (1 : ℝ) / u := by
      gcongr
      linarith [hHV.1]
    linarith
  have hYlt : Y < y ^ 9 := by
    rcases lt_or_eq_of_le hYhi with h | h
    · exact h
    · rw [h] at hmuY; linarith
  have hnext : τ < mu τ y (Y + 1) := by
    by_contra hcon
    push Not at hcon
    have hmem : Y + 1 ∈ T := by
      simp only [hT, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hcon⟩
    have := Finset.le_max' T (Y + 1) hmem
    rw [← hYdef] at this
    omega
  have hstep : mu τ y (Y + 1) ≤ mu τ y Y + HV τ y / (2 * (y : ℝ) ^ 8) := by
    rw [mu_eq, mu_eq]
    have := sumU_succ_le (y := y) hy hYlo
    have h2 : 0 ≤ 1 / 2 * HV τ y := by positivity
    have := mul_le_mul_of_nonneg_left this h2
    have e : 1 / 2 * HV τ y * (1 / (y : ℝ) ^ 8) = HV τ y / (2 * (y : ℝ) ^ 8) := by
      field_simp
    nlinarith
  have hbeta : (τ : ℝ) - mu τ y Y ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by linarith
  have hmu : (τ : ℝ) / 2 ≤ mu τ y Y := by linarith [hL.tune]
  refine ⟨Y, hYlo, hYhi, hmuY, hbeta, hmu, ?_⟩
  -- `∑_U 1/u = 2μ/H_V ≥ τ/H_V` and `∑_U 1/u ≤ |U|/y^8`
  have hsum : (τ : ℝ) / HV τ y ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u := by
    rw [div_le_iff₀ hHVpos]
    have := mu_eq (τ := τ) (y := y) (Y := Y)
    nlinarith
  have hcard := sumU_le_card (Y := Y) hy
  have hy8pos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
  have := hsum.trans hcard
  rw [le_div_iff₀ hy8pos] at this
  calc (τ : ℝ) * (y : ℝ) ^ 8 / HV τ y = (τ : ℝ) / HV τ y * (y : ℝ) ^ 8 := by ring
    _ ≤ _ := this

/-! ### A congruence mod 1 forces equality (end of §4) -/

/-- The total mass of the graph is `2μ ≤ 2τ ≤ 1/2`, so every `S ⊆ A` has `0 ≤ σ(S) ≤ 1/2`. -/
lemma sigma_le_half {τ : ℚ} {y Y : ℕ} (hη : τ ≤ 1 / 400) (hT : Tuned τ y Y)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ Aset τ y Y) : 0 ≤ sigma S ∧ sigma S ≤ 1 / 2 := by
  have hnn : ∀ p : ℕ × ℕ, (0 : ℚ) ≤ 1 / ((p.1 : ℚ) * p.2) := fun _ => by positivity
  refine ⟨Finset.sum_nonneg (fun p _ => hnn p), ?_⟩
  have h1 : sigma S ≤ sigma (Aset τ y Y) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun p _ _ => hnn p)
  have h2 : ((sigma (Aset τ y Y) : ℚ) : ℝ) = 2 * mu τ y Y := by
    unfold sigma mu; push_cast; ring
  have h3 : ((sigma (Aset τ y Y) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
    rw [h2]
    have := hT.beta_nonpos
    have : (τ : ℝ) ≤ 1 / 400 := by have := (Rat.cast_le (K := ℝ)).2 hη; simpa using this
    push_cast; linarith
  exact h1.trans (by exact_mod_cast h3)

/-- If `σ(S) ≡ τ (mod 1)` then `σ(S) = τ` (end of §4). -/
lemma sigma_eq_of_congr {τ : ℚ} {y Y : ℕ} (h0 : 0 < τ) (hη : τ ≤ 1 / 400) (hT : Tuned τ y Y)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ Aset τ y Y) (k : ℤ) (hk : sigma S - τ = k) :
    sigma S = τ := by
  obtain ⟨hs0, hs1⟩ := sigma_le_half hη hT hS
  have hk1 : (k : ℚ) < 1 := by rw [← hk]; linarith
  have hk2 : (-1 : ℚ) < k := by rw [← hk]; linarith
  have : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  rw [this] at hk
  simp at hk
  linarith

end

/-! ### Li (2026): §5, counting with a geometric sum -/
/-
§5 of the paper: counting with a geometric sum.

For a finite edge set `A` (pairs `(v,u)`, the edge standing for `1/(vu)`), a target `τ` and a
common denominator `L`, the number `N` of subsets `S ⊆ A` with `σ(S) ≡ τ (mod 1)` satisfies
  `N / 2^{|A|} = (1/L) ∑_h e(-hτ) φ(h)`,       eq. (2)
where `h` runs over the frequencies `-L/2 < h ≤ L/2` and `φ(h) = ∏_{(v,u)∈A} (1 + e(h/(uv)))/2`.
-/

section

open Real Finset

/-- The frequencies: the integers `h` with `-⌊L/2⌋ < h ≤ L - ⌊L/2⌋` (for even `L`, exactly the
paper's `-L/2 < h ≤ L/2`); a complete residue system modulo `L`. -/
noncomputable def freq (L : ℕ) : Finset ℤ := Finset.Ioc (-((L : ℤ) / 2)) ((L : ℤ) - (L : ℤ) / 2)

/-- `φ(h) = ∏_{(v,u) ∈ A} (1 + e(h/(uv)))/2`. -/
noncomputable def phi (A : Finset (ℕ × ℕ)) (h : ℤ) : ℂ :=
  ∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2))) / 2

open Classical in
/-- `N`: the number of `S ⊆ A` with `σ(S) ≡ τ (mod 1)`. -/
noncomputable def Ncount (A : Finset (ℕ × ℕ)) (τ : ℚ) : ℕ :=
  ((A.powerset).filter (fun S => ∃ k : ℤ, sigma S - τ = k)).card

/-- There are exactly `L` frequencies. -/
lemma card_freq (L : ℕ) : (freq L).card = L := by
  simp [freq]

/-- `e(n) = 1` for integers `n` (period 1). -/
lemma ee_int (n : ℤ) : ee (n : ℝ) = 1 := by
  unfold ee
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1; push_cast; ring

/-- `e(kx) = e(x)^k`. -/
lemma ee_nat_mul (k : ℕ) (x : ℝ) : ee ((k : ℝ) * x) = ee x ^ k := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1; push_cast; ring

/-- `e(∑ f) = ∏ e(f)`. -/
lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee
  rw [← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum]

/-- `e(x) = 1` iff `x` is an integer. -/
lemma ee_eq_one_iff (x : ℝ) : ee x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((x : ℂ) - n) * (2 * π * Complex.I) = 0 := by rw [sub_mul]; rw [← hn]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact_mod_cast sub_eq_zero.1 h
    · exact absurd h hpi
  · rintro ⟨n, rfl⟩; exact ⟨n, by push_cast; ring⟩

/-- The geometric-series identity: over any `L` consecutive integers `h`,
`∑_h e(hm/L) = L` if `L ∣ m` and `= 0` otherwise. -/
theorem lem_geom (L : ℕ) (hL : 0 < L) (a m : ℤ) :
    ∑ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * m / L) = if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have : ∀ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * ((L : ℤ) * k : ℤ) / L) = 1 := by
      intro h _
      have : (h : ℝ) * (((L : ℤ) * k : ℤ) : ℝ) / L = ((h * k : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [this, ee_int]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Int.card_Ioc]
    simp
  · -- reindex `h = a + 1 + k`, `0 ≤ k < L`
    have hre : ∑ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * m / L) =
        ∑ k ∈ Finset.range L, ee (((a + 1 : ℤ) : ℝ) * m / L) * ee ((m : ℝ) / L) ^ k := by
      refine Finset.sum_nbij' (fun h => (h - a - 1).toNat) (fun k => a + 1 + k) ?_ ?_ ?_ ?_ ?_
      · intro h hh; simp only [Finset.mem_Ioc] at hh; simp only [Finset.mem_range]; omega
      · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ioc]; omega
      · intro h hh; simp only [Finset.mem_Ioc] at hh
        show a + 1 + ((h - a - 1).toNat : ℤ) = h; omega
      · intro k _
        show (a + 1 + (k : ℤ) - a - 1).toNat = k; omega
      · intro h hh
        simp only [Finset.mem_Ioc] at hh
        rw [← ee_nat_mul, ← ee_add]
        congr 1
        have : (((h - a - 1).toNat : ℕ) : ℝ) = (h : ℝ) - a - 1 := by
          have : (((h - a - 1).toNat : ℕ) : ℤ) = h - a - 1 := Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [this]; push_cast; field_simp; ring
    rw [hre, ← Finset.mul_sum]
    set ζ := ee ((m : ℝ) / L)
    have hζ1 : ζ ≠ 1 := by
      intro h
      obtain ⟨n, hn⟩ := (ee_eq_one_iff _).1 h
      apply hdvd
      refine ⟨n, ?_⟩
      have : (m : ℝ) = L * n := by field_simp at hn; linarith
      exact_mod_cast this
    have hζL : ζ ^ L = 1 := by
      rw [← ee_nat_mul]
      have : (L : ℝ) * ((m : ℝ) / L) = ((m : ℤ) : ℝ) := by field_simp
      rw [this, ee_int]
    rw [geom_sum_eq hζ1, hζL]
    simp

/-- **Formula (2)**: `N / 2^{|A|} = (1/L) ∑_h e(-hτ) φ(h)`, valid whenever `L > 0`, every
edge `vu` divides `L`, and the denominator of `τ` divides `L`. -/
theorem eq_N (A : Finset (ℕ × ℕ)) (τ : ℚ) (L : ℕ) (hL : 0 < L)
    (hA : ∀ p ∈ A, 0 < p.1 * p.2 ∧ p.1 * p.2 ∣ L) (hτ : τ.den ∣ L) :
    (Ncount A τ : ℂ) / 2 ^ A.card =
      (1 / (L : ℂ)) * ∑ h ∈ freq L, ee (-((h : ℝ) * τ)) * phi A h := by
  classical
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  -- every `L (σ(S) - τ)` is an integer
  have hint : ∀ S ⊆ A, ∃ m : ℤ, (L : ℚ) * (sigma S - τ) = m := by
    intro S hS
    have hσ : ∃ m : ℤ, (L : ℚ) * sigma S = m := by
      induction S using Finset.induction_on with
      | empty => exact ⟨0, by simp [sigma]⟩
      | insert p S hpS ih =>
        obtain ⟨m, hm⟩ := ih ((Finset.subset_insert _ _).trans hS)
        obtain ⟨hpos, ⟨c, hc⟩⟩ := hA p (hS (Finset.mem_insert_self _ _))
        refine ⟨c + m, ?_⟩
        unfold sigma at hm ⊢
        rw [Finset.sum_insert hpS, mul_add, hm, hc]
        have : ((p.1 : ℚ) * p.2) ≠ 0 := by exact_mod_cast hpos.ne'
        push_cast
        rw [mul_one_div, mul_div_cancel_left₀ _ this]
    obtain ⟨m, hm⟩ := hσ
    obtain ⟨c, hc⟩ := hτ
    refine ⟨m - c * τ.num, ?_⟩
    rw [mul_sub, hm]
    push_cast
    congr 1
    conv_lhs => rw [← Rat.num_div_den τ, hc]
    have : (τ.den : ℚ) ≠ 0 := by exact_mod_cast τ.den_pos.ne'
    push_cast
    field_simp
  -- the indicator of `σ(S) ≡ τ` as a geometric sum
  have hind : ∀ S ⊆ A, (if ∃ k : ℤ, sigma S - τ = k then (1 : ℂ) else 0) =
      (1 / (L : ℂ)) * ∑ h ∈ freq L, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) := by
    intro S hS
    obtain ⟨m, hm⟩ := hint S hS
    have hσq : sigma S - τ = (m : ℚ) / L := by
      rw [eq_div_iff hLq, mul_comm, hm]
    have hσ : (((sigma S : ℚ) : ℝ) - τ) = (m : ℝ) / L := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hσq
      push_cast at this
      exact this
    have hsum : ∑ h ∈ freq L, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) =
        if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
      rw [← lem_geom L hL (-((L : ℤ) / 2)) m]
      unfold freq
      have : (L : ℤ) - (L : ℤ) / 2 = -((L : ℤ) / 2) + L := by ring
      rw [this]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [hσ]; ring_nf
    rw [hsum]
    have hiff : (∃ k : ℤ, sigma S - τ = k) ↔ (L : ℤ) ∣ m := by
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have : (m : ℚ) = L * k := by rw [← hm, hk]
        exact_mod_cast this
      · rintro ⟨c, hc⟩
        refine ⟨c, ?_⟩
        rw [hσq, hc]; push_cast; field_simp
    by_cases hc : (L : ℤ) ∣ m
    · rw [ite_eq_left hc, ite_eq_left (hiff.2 hc)]
      have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      field_simp
    · rw [ite_eq_right hc, ite_eq_right (mt hiff.1 hc)]; simp
  -- the product formula for `φ`
  have hphi : ∀ h : ℤ, ee (-((h : ℝ) * τ)) * phi A h =
      (1 / 2 ^ A.card) * ∑ S ∈ A.powerset, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) := by
    intro h
    have h1 : phi A h = (∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2)))) / 2 ^ A.card := by
      unfold phi; rw [Finset.prod_div_distrib, Finset.prod_const]
    have h2 : ∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2))) =
        ∑ S ∈ A.powerset, ee ((h : ℝ) * ((sigma S : ℚ) : ℝ)) := by
      have := Finset.prod_add (fun p : ℕ × ℕ => ee ((h : ℝ) / ((p.1 : ℝ) * p.2)))
        (fun _ => (1 : ℂ)) A
      simp only [Finset.prod_const_one, mul_one] at this
      rw [Finset.prod_congr rfl (fun p _ => add_comm _ _), this]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      rw [← ee_sum]
      congr 1
      unfold sigma; push_cast; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_); ring
    rw [h1, h2, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [show (h : ℝ) * (((sigma S : ℚ) : ℝ) - τ) = -((h : ℝ) * τ) + (h : ℝ) * ((sigma S : ℚ) : ℝ)
      by ring, ee_add]
    ring
  rw [Finset.sum_congr rfl (fun h _ => hphi h)]
  unfold Ncount
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_congr rfl (fun S hS => hind S (Finset.mem_powerset.1 hS))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  ring

/-- eq. (3): `1 + e(x) = 2 e(x/2) cos πx`. -/
lemma eq_half (x : ℝ) : 1 + ee x = 2 * ee (x / 2) * (Real.cos (π * x) : ℂ) := by
  rw [mul_assoc, mul_comm (ee _), ← mul_assoc, Complex.ofReal_cos, Complex.two_cos]
  unfold ee
  rw [add_mul, ← Complex.exp_add, ← Complex.exp_add]
  have e1 : (↑(π * x) : ℂ) * Complex.I + 2 * ↑π * Complex.I * ↑(x / 2) = 2 * π * Complex.I * x := by
    push_cast; ring
  have e2 : -(↑(π * x) : ℂ) * Complex.I + 2 * ↑π * Complex.I * ↑(x / 2) = 0 := by
    push_cast; ring
  rw [e1, e2, Complex.exp_zero, add_comm]

/-- `|φ(h)| = ∏_{(v,u) ∈ A} |cos(π h/(uv))|`. -/
lemma norm_phi (A : Finset (ℕ × ℕ)) (h : ℤ) :
    ‖phi A h‖ = ∏ p ∈ A, |Real.cos (π * ((h : ℝ) / ((p.1 : ℝ) * p.2)))| := by
  unfold phi
  rw [norm_prod]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [eq_half, norm_div, norm_mul, norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- Each factor of `φ(h)` has absolute value at most `1`, so `|φ(h)| ≤ 1` (§5). -/
lemma norm_phi_le_one (A : Finset (ℕ × ℕ)) (h : ℤ) : ‖phi A h‖ ≤ 1 := by
  rw [norm_phi]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)

/-- `φ(0) = 1` (§5). -/
lemma phi_zero (A : Finset (ℕ × ℕ)) : phi A 0 = 1 := by
  simp [phi, ee]

end

/-! ### Li (2026): §6, the table and the three cases -/
/-
§6 of the paper: the `V × U` table and the three cases.

By the Chinese remainder theorem a frequency `h` is the same as its row labels
`ξ_v = h mod v` (`v ∈ V`) and its column labels `ζ_u = h mod u` (`u ∈ U`).  We record the row
labels as a single residue `ξ = h mod P_V`, `P_V = ∏_{v∈V} v` (so `ξ_v = ξ mod v`), and the
column labels as residues `ζ_u ∈ [0, u)`.  The `(v,u)` entry of the table is
`|cos π φ_{vu}|`, where the phase `φ_{vu}(ξ, ζ_u) = J/(uv)` for the CRT integer
`J ≡ ξ (mod P_V)`, `J ≡ ζ_u (mod u)`.

For the minor-arc bound we only need that the label map `h ↦ (ξ, ζ)` is *injective* on
frequencies (`label_inj`); surjectivity (the other half of the CRT bijection) is never used,
because all terms are nonnegative.
-/

section

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `P_V = ∏_{v ∈ V} v = |G_V|`. -/
def PV : ℕ := ∏ v ∈ Vset τ y, v

/-- The CRT integer `J ∈ [0, P_V u)` with `J ≡ ξ (mod P_V)` and `J ≡ z (mod u)`. -/
noncomputable def crt (u ξ z : ℕ) : ℕ :=
  if h : Nat.Coprime (PV τ y) u then (Nat.chineseRemainder h ξ z).1 else 0

/-- The phase `φ_{vu}(ξ, ζ_u) = J/(uv)` (defined modulo 1; only `|cos π ·|` and `‖·‖` of it are
used). -/
noncomputable def phase (u v ξ z : ℕ) : ℝ := (crt τ y u ξ z : ℝ) / ((u : ℝ) * v)

/-- `F_u(ξ, ζ_u) = ∏_{v ∈ V} |cos π φ_{vu}(ξ, ζ_u)|`: the weight of column `u`. -/
noncomputable def Fcol (u ξ z : ℕ) : ℝ := ∏ v ∈ Vset τ y, |Real.cos (π * phase τ y u v ξ z)|

/-- `S_u(ξ) = ∑_{ζ_u mod u} F_u(ξ, ζ_u)`. -/
noncomputable def Scol (u ξ : ℕ) : ℝ := ∑ z ∈ range u, Fcol τ y u ξ z

/-- Row labels `ξ` are *coherent* if `ξ ≡ M (mod v)` for all `v ∈ V`, for some `|M| ≤ y^7`. -/
def Coherent (ξ : ℤ) : Prop := ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M

/-- Case I: coherent rows `ξ ≡ M`, all columns matching (`ζ_u ≡ M (mod u)` for all `u`). -/
def CaseI (h : ℤ) : Prop :=
  ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧ ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - M

/-- Case II: coherent rows `ξ ≡ M`, some mismatched column. -/
def CaseII (h : ℤ) : Prop :=
  ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧
    ∃ u ∈ Uset y Y, ¬ (u : ℤ) ∣ h - M

/-- Case III: incoherent rows. -/
def CaseIII (h : ℤ) : Prop := ¬ Coherent τ y h

variable {τ y Y}

/-- A product of distinct primes that all divide an integer `n` divides `n`. -/
lemma prod_primes_dvd_int (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (n : ℤ)
    (h : ∀ p ∈ t, (p : ℤ) ∣ n) : ((∏ p ∈ t, p : ℕ) : ℤ) ∣ n := by
  apply Int.natCast_dvd.2
  exact Finset.prod_primes_dvd _ (fun p hp => (ht p hp).prime)
    (fun p hp => Int.natCast_dvd.1 (h p hp))

/-- `u > 2y² ≥ v` for `u ∈ U`, `v ∈ V`. -/
lemma v_lt_u (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y) : v < u := by
  have h1 := (le_of_mem_Vset hL hv).2
  have h2 := (bounds_of_mem_Uset hu).1
  have hy := hL.y_ge
  have : 2 * y ^ 2 < y ^ 8 := by
    have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
    have h6 : 2 < y ^ 6 := by
      calc 2 < 3 ^ 6 := by norm_num
        _ ≤ y ^ 6 := Nat.pow_le_pow_left hy 6
    rw [this]
    have : 0 < y ^ 2 := by positivity
    nlinarith
  omega

/-- For `v ∈ V` and `u ∈ U`: `P_V` and `u` are coprime. -/
lemma coprime_PV_u (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) : Nat.Coprime (PV τ y) u := by
  apply Nat.Coprime.prod_left
  intro v hv
  exact (Nat.coprime_primes (prime_of_mem_Vset hv) (prime_of_mem_Uset hu)).2
    (v_lt_u hL hu hv).ne

/-- `|W| ≥ 100` (from eq. (1) and the numerical condition of Lemma 8.2). -/
lemma card_W_ge (hL : Large τ y) : 100 ≤ (Wset y).card := by
  have h1 := hL.card_W
  have h2 := hL.count
  have hy : (3 : ℝ) ≤ y := by exact_mod_cast hL.y_ge
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have e1 : (y : ℝ) ^ 2 / (16 * Real.log y) - (y : ℝ) ^ 2 / (20 * Real.log y) =
      ((y : ℝ) ^ 2 / (8 * Real.log y)) / 10 := by field_simp; ring
  have : (100 : ℝ) ≤ (Wset y).card := by linarith
  exact_mod_cast this

/-- `P_V > y^8`. -/
lemma PV_gt_y8 (hL : Large τ y) : y ^ 8 < PV τ y := by
  have hW := card_W_ge hL
  have h1 : ∏ w ∈ Wset y, w ≤ PV τ y := by
    unfold PV
    apply Finset.prod_le_prod_of_subset_of_one_le' Wset_subset_Vset
    intro v hv _
    exact (prime_of_mem_Vset hv).one_lt.le
  have h2 : (y ^ 2 + 1) ^ (Wset y).card ≤ ∏ w ∈ Wset y, w :=
    Finset.pow_card_le_prod _ _ _ (fun w hw => (mem_Wset.1 hw).1)
  have h3 : (y ^ 2 + 1) ^ 4 ≤ (y ^ 2 + 1) ^ (Wset y).card :=
    Nat.pow_le_pow_right (by positivity) (by omega)
  have h4 : y ^ 8 < (y ^ 2 + 1) ^ 4 := by
    calc y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ < (y ^ 2 + 1) ^ 4 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

/-- `P_V > 2 y^7` (so a coherent `ξ` determines `M`). -/
lemma PV_gt (hL : Large τ y) : 2 * (y : ℤ) ^ 7 < PV τ y := by
  have h := PV_gt_y8 hL
  have hy := hL.y_ge
  have : 2 * y ^ 7 < y ^ 8 := by
    have : y ^ 8 = y * y ^ 7 := by ring
    rw [this]
    have : 0 < y ^ 7 := by positivity
    nlinarith
  exact_mod_cast (by omega : 2 * y ^ 7 < PV τ y)

/-- `L > 2 y^7 + 2`. -/
lemma L_gt (hL : Large τ y) : 2 * (y : ℤ) ^ 7 + 2 < Lnum τ y Y := by
  have h := PV_gt_y8 hL
  have hy := hL.y_ge
  have h1 : PV τ y ≤ Lnum τ y Y := by
    unfold PV Lnum
    apply Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
    intro p hp _
    rcases Finset.mem_union.1 hp with h | h
    · exact (prime_of_mem_Vset h).one_lt.le
    · exact (prime_of_mem_Uset h).one_lt.le
  have : 2 * y ^ 7 + 2 < y ^ 8 := by
    have : y ^ 8 = y * y ^ 7 := by ring
    rw [this]
    have : 3 ≤ y ^ 7 := le_trans hy (Nat.le_self_pow (by norm_num) y)
    nlinarith
  exact_mod_cast (by omega : 2 * y ^ 7 + 2 < Lnum τ y Y)

/-- The CRT integer is `≡ ξ (mod P_V)`. -/
lemma crt_modEq_xi (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ) :
    ((crt τ y u ξ z : ℕ) : ℤ) ≡ ξ [ZMOD PV τ y] := by
  have hc := coprime_PV_u hL hu
  have h := (Nat.chineseRemainder hc ξ z).2.1
  unfold crt
  rw [dite_eq_left hc]
  exact Int.modEq_iff_dvd.2 (Nat.modEq_iff_dvd.1 h)

/-- The CRT integer is `≡ ζ_u (mod u)`. -/
lemma crt_modEq_z (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ) :
    ((crt τ y u ξ z : ℕ) : ℤ) ≡ z [ZMOD u] := by
  have hc := coprime_PV_u hL hu
  have h := (Nat.chineseRemainder hc ξ z).2.2
  unfold crt
  rw [dite_eq_left hc]
  exact Int.modEq_iff_dvd.2 (Nat.modEq_iff_dvd.1 h)

/-- The phase depends only on `J` modulo `uv`: if `J ≡ ξ (mod v)` and `J ≡ z (mod u)` then
`|cos π φ_{vu}(ξ,z)| = |cos(π J/(uv))|` and `‖φ_{vu}(ξ,z)‖ = ‖J/(uv)‖`. -/
lemma phase_congr (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y)
    (ξ z : ℕ) (J : ℤ) (hJv : (v : ℤ) ∣ J - ξ) (hJu : (u : ℤ) ∣ J - z) :
    ∃ n : ℤ, phase τ y u v ξ z = (J : ℝ) / ((u : ℝ) * v) + n := by
  set C : ℤ := ((crt τ y u ξ z : ℕ) : ℤ) with hC
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  have h1 : (v : ℤ) ∣ C - J := by
    have := hvP.trans (crt_modEq_xi hL hu ξ z).dvd
    have e : C - J = -(J - ξ) - ((ξ : ℤ) - C) := by ring
    rw [e]; exact dvd_sub (dvd_neg.2 hJv) this
  have h2 : (u : ℤ) ∣ C - J := by
    have := (crt_modEq_z hL hu ξ z).dvd
    have e : C - J = -(J - z) - ((z : ℤ) - C) := by ring
    rw [e]; exact dvd_sub (dvd_neg.2 hJu) this
  have hcop : IsCoprime (u : ℤ) (v : ℤ) := Nat.isCoprime_iff_coprime.2
    ((Nat.coprime_primes (prime_of_mem_Uset hu) (prime_of_mem_Vset hv)).2 (v_lt_u hL hu hv).ne')
  obtain ⟨n, hn⟩ := hcop.mul_dvd h2 h1
  refine ⟨n, ?_⟩
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
  have hCR : ((crt τ y u ξ z : ℕ) : ℝ) = (J : ℝ) + (u : ℝ) * v * n := by
    have := congrArg (fun m : ℤ => (m : ℝ)) hn
    push_cast at this
    rw [hC] at this
    push_cast at this
    linarith
  unfold phase
  rw [hCR]
  field_simp

/-- Uniqueness of `M` for coherent row labels. -/
lemma coherent_unique (hL : Large τ y) {ξ M M' : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7)
    (hM' : |M'| ≤ (y : ℤ) ^ 7) (h1 : ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M)
    (h2 : ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M') : M = M' := by
  have hd : ((PV τ y : ℕ) : ℤ) ∣ M' - M := by
    apply prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv)
    intro v hv
    have := dvd_sub (h1 v hv) (h2 v hv)
    have e : ξ - M - (ξ - M') = M' - M := by ring
    rwa [e] at this
  have hlt : |M' - M| < (PV τ y : ℤ) := by
    have := PV_gt (τ := τ) hL
    have h3 := abs_sub M' M
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  linarith

/-- Injectivity of the label map on frequencies (half of the CRT bijection): two frequencies
with the same residue modulo `P_V` and modulo every `u ∈ U` are equal. -/
lemma label_inj {h h' : ℤ} (hh : h ∈ freq (Lnum τ y Y))
    (hh' : h' ∈ freq (Lnum τ y Y)) (hV : (PV τ y : ℤ) ∣ h - h')
    (hU : ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - h') : h = h' := by
  have hd : ((Lnum τ y Y : ℕ) : ℤ) ∣ h - h' := by
    apply prod_primes_dvd_int
    · intro p hp
      rcases Finset.mem_union.1 hp with h | h
      · exact prime_of_mem_Vset h
      · exact prime_of_mem_Uset h
    · intro p hp
      rcases Finset.mem_union.1 hp with hpV | hpU
      · have hvP : (p : ℤ) ∣ (PV τ y : ℤ) := by
          exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hpV
        exact hvP.trans hV
      · exact hU p hpU
  have hlt : |h - h'| < (Lnum τ y Y : ℤ) := by
    simp only [freq, Finset.mem_Ioc] at hh hh'
    rw [abs_lt]
    constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  linarith

/-- Every frequency falls into exactly one of the three cases. -/
lemma three_cases (hL : Large τ y) (h : ℤ) :
    (CaseI τ y Y h ∨ CaseII τ y Y h ∨ CaseIII τ y h) ∧
    ¬ (CaseI τ y Y h ∧ CaseII τ y Y h) ∧ ¬ (CaseI τ y Y h ∧ CaseIII τ y h) ∧
    ¬ (CaseII τ y Y h ∧ CaseIII τ y h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hc : Coherent τ y h
    · obtain ⟨M, hM, hMv⟩ := hc
      by_cases hU : ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - M
      · exact Or.inl ⟨M, hM, hMv, hU⟩
      · push Not at hU
        exact Or.inr (Or.inl ⟨M, hM, hMv, hU⟩)
    · exact Or.inr (Or.inr hc)
  · rintro ⟨⟨M, hM, hMv, hMu⟩, ⟨M', hM', hM'v, u, hu, hnd⟩⟩
    have := coherent_unique hL hM hM' hMv hM'v
    subst this
    exact hnd (hMu u hu)
  · rintro ⟨⟨M, hM, hMv, -⟩, hIII⟩
    exact hIII ⟨M, hM, hMv⟩
  · rintro ⟨⟨M, hM, hMv, -⟩, hIII⟩
    exact hIII ⟨M, hM, hMv⟩

/-- Every `|M| ≤ y^7` is a frequency. -/
lemma mem_freq_of_small (hL : Large τ y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    M ∈ freq (Lnum τ y Y) := by
  have h := L_gt (Y := Y) hL
  simp only [freq, Finset.mem_Ioc]
  rw [abs_le] at hM
  constructor <;> omega

/-- Case I consists exactly of the frequencies `h` with `|h| ≤ y^7` (the major arcs). -/
lemma caseI_iff (hL : Large τ y) {h : ℤ} (hh : h ∈ freq (Lnum τ y Y)) :
    CaseI τ y Y h ↔ |h| ≤ (y : ℤ) ^ 7 := by
  constructor
  · rintro ⟨M, hM, hMv, hMu⟩
    have hPV : (PV τ y : ℤ) ∣ h - M := by
      apply prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv)
      exact hMv
    have := label_inj hh (mem_freq_of_small hL hM) hPV hMu
    rw [this]; exact hM
  · intro hsmall
    exact ⟨h, hsmall, fun v _ => by simp, fun u _ => by simp⟩

/-- `|φ(h)|` is the product of the column weights: `|φ(h)| = ∏_{u ∈ U} F_u(ξ, ζ_u)` with
`ξ = h mod P_V`, `ζ_u = h mod u`. -/
lemma norm_phi_eq_prod_Fcol (hL : Large τ y) (h : ℤ) :
    ‖phi (Aset τ y Y) h‖ =
      ∏ u ∈ Uset y Y, Fcol τ y u (h % (PV τ y : ℤ)).toNat (h % (u : ℤ)).toNat := by
  rw [norm_phi, Aset, Finset.prod_product_right]
  refine Finset.prod_congr rfl (fun u hu => ?_)
  unfold Fcol
  refine Finset.prod_congr rfl (fun v hv => ?_)
  have hPV0 : (PV τ y : ℤ) ≠ 0 := by
    have := PV_gt (τ := τ) hL
    have : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    omega
  have hu0 : (u : ℤ) ≠ 0 := by exact_mod_cast (prime_of_mem_Uset hu).ne_zero
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  have hJv : (v : ℤ) ∣ h - (((h % (PV τ y : ℤ)).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hPV0)]
    exact hvP.trans (Int.dvd_self_sub_emod)
  have hJu : (u : ℤ) ∣ h - (((h % (u : ℤ)).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hu0)]
    exact Int.dvd_self_sub_emod
  obtain ⟨n, hn⟩ := phase_congr hL hu hv _ _ h hJv hJu
  rw [hn, mul_add, mul_comm π ((n : ℤ) : ℝ), Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow,
    one_mul, mul_comm (u : ℝ)]

/-- eq. (4) Once the row labels `ξ` are fixed, the sum over column labels factorises:
`∑_ζ ∏_u F_u(ξ, ζ_u) = ∏_u S_u(ξ)`. -/
lemma eq_factor (ξ : ℕ) :
    ∑ ζ ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)),
        ∏ u : Uset y Y, Fcol τ y u ξ (ζ u) =
      ∏ u ∈ Uset y Y, Scol τ y u ξ := by
  rw [← Finset.prod_coe_sort (Uset y Y) (fun u => Scol τ y u ξ)]
  unfold Scol
  exact (Finset.prod_univ_sum (fun u : Uset y Y => range (u : ℕ))
    (fun u z => Fcol τ y u ξ z)).symm

/-- Column weights are nonnegative. -/
lemma Fcol_nonneg (u ξ z : ℕ) : 0 ≤ Fcol τ y u ξ z :=
  Finset.prod_nonneg (fun _ _ => abs_nonneg _)

/-- Column weights are at most `1` (§6). -/
lemma Fcol_le_one (u ξ z : ℕ) : Fcol τ y u ξ z ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)

/-- `S_u(ξ) ≥ 0`. -/
lemma Scol_nonneg (u ξ : ℕ) : 0 ≤ Scol τ y u ξ :=
  Finset.sum_nonneg (fun _ _ => Fcol_nonneg _ _ _)

end

/-! ### Li (2026): §7, major arcs -/
/-
§7 of the paper: Case I, the major arcs (Proposition 7.1), by positivity.
-/

section

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `P(M) = ∏_{(v,u) ∈ A} cos(π M/(uv))`. -/
noncomputable def Pmaj (M : ℤ) : ℝ :=
  ∏ p ∈ Aset τ y Y, Real.cos (π * ((M : ℝ) / ((p.1 : ℝ) * p.2)))

/-- `Σ_maj = (1/L) ∑_{|M| ≤ y^7} e(-Mτ) φ(M)`: the part of eq. (2) coming from case I. -/
noncomputable def SigmaMaj : ℂ :=
  (1 / (Lnum τ y Y : ℂ)) *
    ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7), ee (-((M : ℝ) * τ)) * phi (Aset τ y Y) M

variable {τ y Y}

/-- `Re e(x) = cos 2πx`. -/
lemma ee_re (x : ℝ) : (ee x).re = Real.cos (2 * π * x) := by
  unfold ee
  rw [Complex.exp_re]
  have h1 : (2 * (π : ℂ) * Complex.I * x).re = 0 := by simp
  have h2 : (2 * (π : ℂ) * Complex.I * x).im = 2 * π * x := by simp
  rw [h1, h2, Real.exp_zero, one_mul]

/-- `Im e(x) = sin 2πx`. -/
lemma ee_im (x : ℝ) : (ee x).im = Real.sin (2 * π * x) := by
  unfold ee
  rw [Complex.exp_im]
  have h1 : (2 * (π : ℂ) * Complex.I * x).re = 0 := by simp
  have h2 : (2 * (π : ℂ) * Complex.I * x).im = 2 * π * x := by simp
  rw [h1, h2, Real.exp_zero, one_mul]

/-- Proposition 7.1, Step 1: `φ(M) = e(Mμ) P(M)`, hence `e(-Mτ) φ(M) = e(Mβ) P(M)` with
`β = μ - τ`. -/
lemma major_step1 (M : ℤ) :
    ee (-((M : ℝ) * τ)) * phi (Aset τ y Y) M =
      ee ((M : ℝ) * (mu τ y Y - τ)) * (Pmaj τ y Y M : ℂ) := by
  have hphi : phi (Aset τ y Y) M = ee ((M : ℝ) * mu τ y Y) * (Pmaj τ y Y M : ℂ) := by
    unfold phi Pmaj
    have : ∀ p ∈ Aset τ y Y, (1 + ee ((M : ℝ) / ((p.1 : ℝ) * p.2))) / 2 =
        ee ((M : ℝ) / ((p.1 : ℝ) * p.2) / 2) *
          (Real.cos (π * ((M : ℝ) / ((p.1 : ℝ) * p.2))) : ℂ) := by
      intro p _
      rw [eq_half]; ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, ← ee_sum, Complex.ofReal_prod]
    congr 2
    unfold mu
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [hphi, ← mul_assoc, ← ee_add]
  congr 2
  ring

/-- Proposition 7.1, Step 2: `P(M) > 0` for `|M| ≤ y^7`; `P(0) = 1`; `P(-M) = P(M)`. -/
lemma major_step2 (hL : Large τ y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    0 < Pmaj τ y Y M := by
  unfold Pmaj
  refine Finset.prod_pos (fun p hp => ?_)
  obtain ⟨hv, hu⟩ := mem_Aset.1 hp
  have hv2 := (le_of_mem_Vset hL hv).1
  have hu8 := (bounds_of_mem_Uset hu).1
  have hy := hL.y_ge
  -- `2|M| ≤ 2y^7 < 2y^8 < vu`
  have hy78 : y ^ 7 < y ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hMR : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by exact_mod_cast hM
  have hprod : 2 * (y : ℝ) ^ 8 < (p.1 : ℝ) * p.2 := by
    have : 2 * y ^ 8 < p.1 * p.2 := by nlinarith
    exact_mod_cast this
  have hy78R : (y : ℝ) ^ 7 < (y : ℝ) ^ 8 := by exact_mod_cast hy78
  have hpos : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    have : (0 : ℝ) ≤ (y : ℝ) ^ 8 := by positivity
    linarith
  have hx : |(M : ℝ) / ((p.1 : ℝ) * p.2)| < 1 / 2 := by
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    linarith
  apply Real.cos_pos_of_mem_Ioo
  rw [abs_lt] at hx
  constructor <;> nlinarith [Real.pi_pos]

/-- Proposition 7.1, Step 2: `P(0) = 1`. -/
lemma Pmaj_zero : Pmaj τ y Y 0 = 1 := by
  simp [Pmaj]

/-- Proposition 7.1, Step 2: `P(-M) = P(M)` (cosine is even). -/
lemma Pmaj_neg (M : ℤ) : Pmaj τ y Y (-M) = Pmaj τ y Y M := by
  unfold Pmaj
  refine Finset.prod_congr rfl (fun p _ => ?_)
  push_cast
  rw [neg_div, mul_neg, Real.cos_neg]

/-- **Proposition 7.1 (major arcs).**  `Σ_maj` is real and `Σ_maj ≥ 1/L`.
(Pair `M` with `-M`: the contribution is `2 cos(2πMβ) P(M) ≥ 0`, since `|2πMβ| < π/2` by the
tuning lemma; and `M = 0` contributes `1/L`.) -/
theorem prop_major (hL : Large τ y) (hT : Tuned τ y Y) :
    (SigmaMaj τ y Y).im = 0 ∧ 1 / (Lnum τ y Y : ℝ) ≤ (SigmaMaj τ y Y).re := by
  set β : ℝ := mu τ y Y - τ with hβ
  set K : ℤ := (y : ℤ) ^ 7 with hK
  have hS : SigmaMaj τ y Y = ((1 / (Lnum τ y Y : ℝ) : ℝ) : ℂ) *
      ∑ M ∈ Finset.Icc (-K) K, ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ) := by
    unfold SigmaMaj
    rw [Finset.sum_congr rfl (fun M _ => major_step1 M)]
    push_cast; ring
  have hre : ∀ M : ℤ, (ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ)).re =
      Real.cos (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
    intro M; rw [Complex.mul_re, ee_re]; simp
  have him : ∀ M : ℤ, (ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ)).im =
      Real.sin (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
    intro M; rw [Complex.mul_im, ee_im]; simp
  have hLpos : (0 : ℝ) < 1 / (Lnum τ y Y : ℝ) := by
    have h1 := L_gt (Y := Y) hL
    have h2 : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    have : (0 : ℤ) < (Lnum τ y Y : ℤ) := by linarith
    have : (0 : ℝ) < (Lnum τ y Y : ℝ) := by exact_mod_cast this
    positivity
  constructor
  · -- Step 3: pairing `M ↔ -M` makes the sum real
    rw [hS, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [him]
    have : ∑ M ∈ Finset.Icc (-K) K, Real.sin (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M = 0 := by
      refine Finset.sum_involution (fun M _ => -M) ?_ ?_ ?_ ?_
      · intro M _
        rw [Pmaj_neg]; push_cast
        rw [show 2 * π * (-(M : ℝ) * β) = -(2 * π * ((M : ℝ) * β)) by ring, Real.sin_neg]
        ring
      · intro M _ hne heq
        apply hne
        change -M = M at heq
        have : M = 0 := by omega
        subst this; simp
      · intro M hM; simp only [Finset.mem_Icc] at hM ⊢; omega
      · intro M _; simp
    rw [this, mul_zero]
  · -- Step 4: every term is nonnegative, and `M = 0` contributes `1`
    rw [hS, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [hre]
    have hβ1 : |β| ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by
      rw [abs_le]
      constructor
      · linarith [hT.beta_ge]
      · have := hT.beta_nonpos
        have hHV := HV_pos hL
        have : 0 ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by positivity
        linarith
    have hy : (3 : ℝ) ≤ y := by exact_mod_cast hL.y_ge
    have hterm : ∀ M ∈ Finset.Icc (-K) K,
        0 ≤ Real.cos (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
      intro M hM
      have hMabs : |M| ≤ K := abs_le.2 (Finset.mem_Icc.1 hM)
      refine mul_nonneg ?_ (major_step2 hL hMabs).le
      apply Real.cos_nonneg_of_mem_Icc
      -- `|2 M β| ≤ 2 y^7 · H_V/(2y^8) = H_V / y < 1/2`
      have hMR : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by exact_mod_cast hMabs
      have hy0 : (0 : ℝ) < y := by linarith
      have hb : |(M : ℝ) * β| ≤ (y : ℝ) ^ 7 * (HV τ y / (2 * (y : ℝ) ^ 8)) := by
        rw [abs_mul]
        exact mul_le_mul hMR hβ1 (abs_nonneg _) (by positivity)
      have he : (y : ℝ) ^ 7 * (HV τ y / (2 * (y : ℝ) ^ 8)) = HV τ y / (2 * y) := by
        field_simp
      rw [he] at hb
      have hmaj := hL.major
      have : HV τ y / (2 * y) < 1 / 4 := by
        rw [div_lt_iff₀ (by positivity)]; linarith
      rw [abs_le] at hb
      constructor <;> nlinarith [Real.pi_pos]
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-K) K := by
      simp only [Finset.mem_Icc]
      have : (0 : ℤ) ≤ K := by positivity
      omega
    have := Finset.single_le_sum hterm h0mem
    simp only [Int.cast_zero, zero_mul, mul_zero, Real.cos_zero, one_mul, Pmaj_zero] at this
    nlinarith

end

/-! ### Li (2026): §8, single columns -/
/-
§8 of the paper: two lemmas about a single column.

* Lemma 8.1 (`lem_cos`):        `|cos πx| ≤ exp(-2‖x‖²)`;
* eq. (5) (`eq_pf`):              changing only the column label by `s` shifts the phase in row `v`
                                by `s v̄ / u (mod 1)`;
* Lemma 8.2 (`lem_count`):      few test primes are "invisible" (divisor count);
* Lemma 8.3 (`lem_unique`):     separation;
* Lemma 8.4 (`lem_admissible`): no wrap-around.

Inverses modulo `u` are avoided: "`‖s w̄/u‖ ≤ δ`" is expressed as
"`t w ≡ s (mod u)` for some integer `|t| ≤ δ u`" (`Invisible`); the two are equivalent, since
`t` is then the balanced representative of `s w̄` (see the proof of Lemma 8.2 in the paper).
-/

section

open Real Finset

attribute [local instance] Classical.propDecidable

/-- **Lemma 8.1.**  For all real `x`, `|cos πx| ≤ exp(-2‖x‖²)`. -/
theorem lem_cos (x : ℝ) : |Real.cos (π * x)| ≤ exp (-2 * nint x ^ 2) := by
  set t := x - round x with ht
  -- `|cos πx|` has period 1 and is even, so `|cos πx| = cos πa` with `a = ‖x‖ ∈ [0, 1/2]`
  have hper : |Real.cos (π * x)| = |Real.cos (π * t)| := by
    have : π * x = π * t + ((round x : ℤ) : ℝ) * π := by rw [ht]; ring
    rw [this, Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  set a := nint x with ha
  have hat : a = |t| := rfl
  have ha0 : 0 ≤ a := nint_nonneg x
  have ha1 : a ≤ 1 / 2 := nint_le_half x
  have hcos_abs : |Real.cos (π * t)| = Real.cos (π * a) := by
    have h1 : Real.cos (π * t) = Real.cos (π * a) := by
      rw [hat]
      rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
      · rw [h, mul_neg, Real.cos_neg]
    rw [h1]
    apply abs_of_nonneg
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  rw [hper, hcos_abs]
  have hc0 : 0 ≤ Real.cos (π * a) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  -- `sin πa ≥ 2a` (concavity, i.e. Jordan's inequality)
  have hsin : 2 * a ≤ Real.sin (π * a) := by
    have := Real.mul_le_sin (x := π * a) (by positivity) (by nlinarith [Real.pi_pos])
    have e : 2 / π * (π * a) = 2 * a := by field_simp
    linarith
  -- `cos² πa = 1 - sin² πa ≤ 1 - 4a² ≤ e^{-4a²}`
  have hsq : Real.cos (π * a) ^ 2 ≤ exp (-4 * a ^ 2) := by
    have h1 : Real.cos (π * a) ^ 2 = 1 - Real.sin (π * a) ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq (π * a)]; ring
    have h2 : (2 * a) ^ 2 ≤ Real.sin (π * a) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hsin
    have h3 := Real.add_one_le_exp (-4 * a ^ 2)
    nlinarith
  by_contra hcon
  push Not at hcon
  have : exp (-2 * a ^ 2) ^ 2 < Real.cos (π * a) ^ 2 :=
    pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  rw [← Real.exp_nat_mul] at this
  have e : ((2 : ℕ) : ℝ) * (-2 * a ^ 2) = -4 * a ^ 2 := by push_cast; ring
  rw [e] at this
  linarith

variable {τ : ℚ} {y Y : ℕ}

/-- **eq. (5)**: two frequencies with the same row labels `ξ` and column labels `z, z'` at `u`:
their phases in row `v` differ by `k/u` where `v k ≡ z - z' (mod u)`, i.e. by `s v̄/u` with
`s = z - z'`. -/
lemma eq_pf (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y) (ξ z z' : ℕ) :
    ∃ k : ℤ, (u : ℤ) ∣ (v : ℤ) * k - ((z : ℤ) - z') ∧
      phase τ y u v ξ z - phase τ y u v ξ z' = (k : ℝ) / u := by
  have hJ := crt_modEq_xi hL hu ξ z
  have hJ' := crt_modEq_xi hL hu ξ z'
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  -- `J ≡ J' (mod v)`, so `J - J' = v k`
  have hdv : (v : ℤ) ∣ ((crt τ y u ξ z : ℕ) : ℤ) - (crt τ y u ξ z' : ℕ) :=
    hvP.trans ((hJ.trans hJ'.symm).symm.dvd)
  obtain ⟨k, hk⟩ := hdv
  refine ⟨k, ?_, ?_⟩
  · have h1 := (crt_modEq_z hL hu ξ z).symm.dvd
    have h2 := (crt_modEq_z hL hu ξ z').symm.dvd
    rw [← hk]
    have := dvd_sub h1 h2
    have e : ((crt τ y u ξ z : ℕ) : ℤ) - (crt τ y u ξ z' : ℕ) - ((z : ℤ) - z') =
        ((crt τ y u ξ z : ℕ) - (z : ℤ)) - ((crt τ y u ξ z' : ℕ) - (z' : ℤ)) := by ring
    rw [e]; exact this
  · have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
    have hkR : ((crt τ y u ξ z : ℕ) : ℝ) - (crt τ y u ξ z' : ℕ) = (v : ℝ) * k := by
      have := congrArg (fun n : ℤ => (n : ℝ)) hk
      push_cast at this
      exact this
    unfold phase
    rw [div_sub_div_same, hkR]
    field_simp

/-- A test prime `w` is *invisible* for the shift `s` at the column `u` if `‖s w̄/u‖ ≤ δ`,
i.e. if `t w ≡ s (mod u)` for some integer `t` with `|t| ≤ δ u`. -/
def Invisible (d : ℝ) (u : ℕ) (s : ℤ) (w : ℕ) : Prop :=
  ∃ t : ℤ, |(t : ℝ)| ≤ d * u ∧ (u : ℤ) ∣ t * w - s

/-- **Lemma 8.2 (divisor count).**  Let `u ∈ U` and `s ≢ 0 (mod u)`.  If `y` is large, then
`#{w ∈ W : ‖s w̄/u‖ ≤ δ} ≤ 5(4δy² + 2) ≤ |W|/2`.
(Each invisible `w` divides one of the at most `4δy²+2` nonzero integers `s + uℓ`, of absolute
value at most `y^{11}`, and such an integer has at most `5` prime factors exceeding `y²`.) -/
theorem lem_count (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) {s : ℤ}
    (hs : ¬ (u : ℤ) ∣ s) :
    (((Wset y).filter (fun w => Invisible (delta y) u s w)).card : ℝ)
        ≤ 5 * (4 * delta y * (y : ℝ) ^ 2 + 2) ∧
      5 * (4 * delta y * (y : ℝ) ^ 2 + 2) ≤ ((Wset y).card : ℝ) / 2 := by
  have hy3 : 3 ≤ y := hL.y_ge
  have hyR : (3 : ℝ) ≤ y := by exact_mod_cast hy3
  have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log y := by linarith
  set δ := delta y with hδdef
  have hδ0 : 0 < δ := by rw [hδdef, delta]; positivity
  have hδ1 : 2 * δ ≤ 1 := by
    rw [hδdef, delta]
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  obtain ⟨hu8, huY, hup⟩ := mem_Uset.1 hu
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hup.pos
  have hu0' : (0 : ℤ) < u := by exact_mod_cast hup.pos
  have huy9 : (u : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast huY.trans hY
  -- Step 0: take `s` balanced, `|s'| ≤ u/2`, `s' ≡ s (mod u)`.
  set s' : ℤ := s - u * round ((s : ℝ) / u) with hs'def
  have hs' : |(s' : ℝ)| ≤ u / 2 := by
    have h1 := abs_sub_round ((s : ℝ) / u)
    have e : (s' : ℝ) = u * ((s : ℝ) / u - round ((s : ℝ) / u)) := by
      rw [hs'def]; push_cast; field_simp
    rw [e, abs_mul, abs_of_pos hu0]
    nlinarith
  have hss' : (u : ℤ) ∣ s - s' := ⟨round ((s : ℝ) / u), by rw [hs'def]; ring⟩
  have hs'nd : ¬ (u : ℤ) ∣ s' := by
    intro h; exact hs (by have := dvd_add h hss'; simpa using this)
  -- Step 1: for each invisible `w` choose `t` with `|t| ≤ δu`, `t w ≡ s (mod u)`,
  -- and write `t w = s' + u ℓ`.
  set I := (Wset y).filter (fun w => Invisible δ u s w) with hIdef
  let tw : ℕ → ℤ := fun w => if h : Invisible δ u s w then Classical.choose h else 0
  have htw : ∀ w ∈ I, |((tw w : ℤ) : ℝ)| ≤ δ * u ∧ (u : ℤ) ∣ tw w * w - s := by
    intro w hw
    have hinv := (Finset.mem_filter.1 hw).2
    simp only [tw, dite_eq_left hinv]
    exact Classical.choose_spec hinv
  let ℓ : ℕ → ℤ := fun w => (tw w * w - s') / u
  have hℓeq : ∀ w ∈ I, tw w * w = s' + u * ℓ w := by
    intro w hw
    have h1 : (u : ℤ) ∣ tw w * w - s' := by
      have := dvd_add (htw w hw).2 hss'
      have e : tw w * ↑w - s + (s - s') = tw w * w - s' := by ring
      rwa [e] at this
    simp only [ℓ]
    rw [Int.mul_ediv_cancel' h1]; ring
  have hWb : ∀ w ∈ I, y ^ 2 < w ∧ w ≤ 2 * y ^ 2 ∧ w.Prime := fun w hw =>
    mem_Wset.1 (Finset.mem_filter.1 hw).1
  -- `|t w| ≤ δ u · 2y² ≤ u y² ≤ y^{11}`
  have htwb : ∀ w ∈ I, |((tw w * w : ℤ) : ℝ)| ≤ δ * u * (2 * (y : ℝ) ^ 2) := by
    intro w hw
    have h1 := (htw w hw).1
    have h2 : (w : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by exact_mod_cast (hWb w hw).2.1
    push_cast
    rw [abs_mul, Nat.abs_cast]
    apply mul_le_mul h1 h2 (by positivity) (by positivity)
  -- Step 2: `|ℓ| ≤ 2δy² + 1/2`, so `ℓ` takes at most `4δy² + 2` values.
  set m : ℕ := ⌊2 * δ * (y : ℝ) ^ 2 + 1 / 2⌋₊ with hmdef
  have hℓm : ∀ w ∈ I, ℓ w ∈ Finset.Icc (-(m : ℤ)) m := by
    intro w hw
    have e := hℓeq w hw
    have h1 : (u : ℝ) * |((ℓ w : ℤ) : ℝ)| ≤ u * (2 * δ * (y : ℝ) ^ 2 + 1 / 2) := by
      have e' : ((u : ℤ) : ℝ) * ((ℓ w : ℤ) : ℝ) = ((tw w * w : ℤ) : ℝ) - (s' : ℝ) := by
        have := congrArg (fun n : ℤ => (n : ℝ)) e
        push_cast at this ⊢
        linarith
      have h2 : |((u : ℤ) : ℝ) * ((ℓ w : ℤ) : ℝ)| ≤ δ * u * (2 * (y : ℝ) ^ 2) + u / 2 := by
        rw [e']
        exact (abs_sub _ _).trans (add_le_add (htwb w hw) hs')
      rw [abs_mul] at h2
      push_cast at h2
      rw [abs_of_pos hu0] at h2
      nlinarith
    have h2 : |((ℓ w : ℤ) : ℝ)| ≤ 2 * δ * (y : ℝ) ^ 2 + 1 / 2 := le_of_mul_le_mul_left h1 hu0
    have h3 : (ℓ w).natAbs ≤ m := by
      apply Nat.le_floor
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact h2
    rw [Finset.mem_Icc]
    constructor <;> omega
  -- Step 3: each value of `ℓ` accounts for at most 5 primes `w`.
  have hfib : ∀ l : ℤ, (I.filter (fun w => ℓ w = l)).card ≤ 5 := by
    intro l
    by_contra hcon
    push Not at hcon
    set T := I.filter (fun w => ℓ w = l) with hT
    obtain ⟨w0, hw0⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
    have hw0I := (Finset.mem_filter.1 hw0).1
    have hw0l := (Finset.mem_filter.1 hw0).2
    set n : ℤ := s' + u * l with hn
    have hn0 : n ≠ 0 := by
      intro h
      apply hs'nd
      exact ⟨-l, by linarith⟩
    -- every `w ∈ T` divides `n`
    have hdvd : ∀ w ∈ T, w ∣ n.natAbs := by
      intro w hw
      have hwI := (Finset.mem_filter.1 hw).1
      have hwl := (Finset.mem_filter.1 hw).2
      have e := hℓeq w hwI
      rw [hwl] at e
      have : (w : ℤ) ∣ n := ⟨tw w, by rw [hn, ← e]; ring⟩
      exact Int.natCast_dvd.1 this
    -- `|n| ≤ y^{11}`
    have hnb : n.natAbs ≤ y ^ 11 := by
      have e := hℓeq w0 hw0I
      rw [hw0l] at e
      have h1 := htwb w0 hw0I
      rw [e] at h1
      have h2 : |(n : ℝ)| ≤ (y : ℝ) ^ 11 := by
        have : δ * u * (2 * (y : ℝ) ^ 2) ≤ (y : ℝ) ^ 11 := by
          have : δ * u * (2 * (y : ℝ) ^ 2) = (2 * δ) * (u * (y : ℝ) ^ 2) := by ring
          rw [this]
          have h3 : u * (y : ℝ) ^ 2 ≤ (y : ℝ) ^ 11 := by
            have : (y : ℝ) ^ 11 = (y : ℝ) ^ 9 * (y : ℝ) ^ 2 := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right huy9 (by positivity)
          calc 2 * δ * (u * (y : ℝ) ^ 2) ≤ 1 * (u * (y : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right hδ1 (by positivity)
            _ ≤ (y : ℝ) ^ 11 := by linarith
        push_cast [hn] at h1 ⊢
        linarith
      have : ((n.natAbs : ℕ) : ℝ) ≤ ((y ^ 11 : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; exact h2
      exact_mod_cast this
    -- the product of the primes in `T` divides `n`, hence is at most `y^{11}`
    have hprod : ∏ w ∈ T, w ∣ n.natAbs :=
      Finset.prod_primes_dvd _ (fun w hw => (hWb w (Finset.mem_filter.1 hw).1).2.2.prime) hdvd
    have hprodle : ∏ w ∈ T, w ≤ y ^ 11 :=
      (Nat.le_of_dvd (Int.natAbs_pos.2 hn0) hprod).trans hnb
    -- but it exceeds `(y²)^6 = y^{12}`
    have hlow : (y ^ 2 + 1) ^ T.card ≤ ∏ w ∈ T, w :=
      Finset.pow_card_le_prod _ _ _ (fun w hw => (hWb w (Finset.mem_filter.1 hw).1).1)
    have h6 : (y ^ 2 + 1) ^ 6 ≤ (y ^ 2 + 1) ^ T.card :=
      Nat.pow_le_pow_right (by positivity) hcon
    have h12 : y ^ 11 < (y ^ 2 + 1) ^ 6 := by
      calc y ^ 11 < y ^ 12 := Nat.pow_lt_pow_right (by omega) (by norm_num)
        _ = (y ^ 2) ^ 6 := by ring
        _ < (y ^ 2 + 1) ^ 6 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  -- Step 4: combine.
  have hcard : I.card ≤ 5 * (I.image ℓ).card :=
    Finset.card_le_mul_card_image I 5 (fun b _ => hfib b)
  have himg : (I.image ℓ).card ≤ 2 * m + 1 := by
    have h1 : I.image ℓ ⊆ Finset.Icc (-(m : ℤ)) m := by
      intro l hl
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hl
      exact hℓm w hw
    have h2 := Finset.card_le_card h1
    rw [Int.card_Icc] at h2
    omega
  have hmR : (m : ℝ) ≤ 2 * δ * (y : ℝ) ^ 2 + 1 / 2 := Nat.floor_le (by positivity)
  refine ⟨?_, ?_⟩
  · have : (I.card : ℝ) ≤ 5 * (2 * m + 1) := by exact_mod_cast (hcard.trans (by omega))
    linarith
  · have hW := hL.card_W
    have hc := hL.count
    have e : 5 * (4 * δ * (y : ℝ) ^ 2 + 2) = (y : ℝ) ^ 2 / (20 * Real.log y) + 10 := by
      rw [hδdef, delta]; field_simp; ring
    have e2 : (y : ℝ) ^ 2 / (16 * Real.log y) = ((y : ℝ) ^ 2 / (8 * Real.log y)) / 2 := by
      field_simp; ring
    rw [e]
    linarith

/-- The heart of the separation argument: in a *visible* row `w` (i.e. `‖s w̄/u‖ > δ` with
`s = ζ_u - ζ_u'`), the two phases cannot both be close to an integer:
`‖φ_{wu}(ξ,ζ_u)‖ + ‖φ_{wu}(ξ,ζ_u')‖ > δ` (triangle inequality for `‖·‖` and eq. (5)). -/
lemma visible_phase_sum (hL : Large τ y) {u w : ℕ} (hu : u ∈ Uset y Y) (hw : w ∈ Wset y)
    (ξ z z' : ℕ) (hvis : ¬ Invisible (delta y) u ((z : ℤ) - z') w) :
    delta y < nint (phase τ y u w ξ z) + nint (phase τ y u w ξ z') := by
  by_contra hcon
  push Not at hcon
  apply hvis
  obtain ⟨k, hk, hph⟩ := eq_pf hL hu (Wset_subset_Vset hw) ξ z z'
  have h1 : nint ((k : ℝ) / u) ≤ delta y := by
    rw [← hph]; exact (nint_sub_le _ _).trans hcon
  obtain ⟨n, hn⟩ := exists_int_of_nint_le h1
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
  refine ⟨k - n * u, ?_, ?_⟩
  · have e : ((k - n * u : ℤ) : ℝ) = u * ((k : ℝ) / u - n) := by push_cast; field_simp
    rw [e, abs_mul, abs_of_pos hu0, mul_comm]
    exact mul_le_mul_of_nonneg_right hn hu0.le
  · have e : (k - n * u) * (w : ℤ) - ((z : ℤ) - z') = ((w : ℤ) * k - ((z : ℤ) - z')) - u * (n * w) := by
      ring
    rw [e]
    exact dvd_sub hk (dvd_mul_right _ _)

/-- A product of factors in `[0,1]` only grows when factors are dropped. -/
lemma prod_le_prod_subset_of_le_one {s t : Finset ℕ} (hst : s ⊆ t) (f : ℕ → ℝ)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i :=
  Finset.prod_le_prod_of_subset_of_le_one₀ hst h0 (fun i hi _ => h1 i hi)

/-- The visible rows form at least half of `W` (Lemma 8.2). -/
lemma card_visible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) {s : ℤ}
    (hs : ¬ (u : ℤ) ∣ s) :
    ((Wset y).card : ℝ) / 2 ≤
      (((Wset y).filter (fun w => ¬ Invisible (delta y) u s w)).card : ℝ) := by
  have h := lem_count hL hY hu hs
  have e := Finset.card_filter_add_card_filter_not
    (s := Wset y) (fun w => Invisible (delta y) u s w)
  have e' : (((Wset y).filter (fun w => Invisible (delta y) u s w)).card : ℝ) +
      (((Wset y).filter (fun w => ¬ Invisible (delta y) u s w)).card : ℝ) = (Wset y).card := by
    exact_mod_cast e
  linarith [h.1, h.2]

/-- `exp(-δ²/2)^{#visible} ≤ ε²`. -/
lemma pow_visible_le (n : ℕ) (hn : ((Wset y).card : ℝ) / 2 ≤ n) :
    exp (-(delta y ^ 2 / 2)) ^ n ≤ eps y ^ 2 := by
  rw [← Real.exp_nat_mul, eps, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have : 0 ≤ delta y ^ 2 := by positivity
  push_cast
  nlinarith

/-- **Lemma 8.3 (Separation).**  Let `u ∈ U`, `ξ` row labels, and `ζ_u ≢ ζ_u' (mod u)`.
(i) `F_u(ξ,ζ_u) F_u(ξ,ζ_u') ≤ ε²`; in particular at most one label is heavy (`> ε`).
(ii) If `‖φ_{wu}(ξ, ζ_u')‖ ≤ δ/2` for all `w ∈ W`, then `F_u(ξ, ζ_u) ≤ ε`. -/
theorem lem_unique (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z z' : ℕ)
    (hzz : ¬ (u : ℤ) ∣ (z : ℤ) - z') :
    Fcol τ y u ξ z * Fcol τ y u ξ z' ≤ eps y ^ 2 ∧
      ((∀ w ∈ Wset y, nint (phase τ y u w ξ z') ≤ delta y / 2) → Fcol τ y u ξ z ≤ eps y) := by
  set s : ℤ := (z : ℤ) - z' with hsdef
  set Vis := (Wset y).filter (fun w => ¬ Invisible (delta y) u s w) with hVis
  have hVisW : Vis ⊆ Wset y := Finset.filter_subset _ _
  have hVisV : Vis ⊆ Vset τ y := hVisW.trans Wset_subset_Vset
  have hcard := card_visible hL hY hu hzz
  -- one cosine factor is at most `exp(-δ²/2)` when its phase exceeds `δ/2`
  have hfac : ∀ x : ℝ, delta y / 2 < nint x → |Real.cos (π * x)| ≤ exp (-(delta y ^ 2 / 2)) := by
    intro x hx
    refine (lem_cos x).trans (Real.exp_le_exp.2 ?_)
    have : 0 ≤ delta y / 2 := by
      have := hL.y_ge
      rw [delta]
      have : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
      positivity
    nlinarith
  set c := fun (ζ : ℕ) (v : ℕ) => |Real.cos (π * phase τ y u v ξ ζ)| with hc
  have hc0 : ∀ ζ v, 0 ≤ c ζ v := fun _ _ => abs_nonneg _
  have hc1 : ∀ ζ v, c ζ v ≤ 1 := fun _ _ => Real.abs_cos_le_one _
  constructor
  · -- (i)
    have e : Fcol τ y u ξ z * Fcol τ y u ξ z' = ∏ v ∈ Vset τ y, (c z v * c z' v) := by
      rw [Fcol, Fcol, ← Finset.prod_mul_distrib]
    rw [e]
    calc ∏ v ∈ Vset τ y, (c z v * c z' v) ≤ ∏ v ∈ Vis, (c z v * c z' v) :=
          prod_le_prod_subset_of_le_one hVisV _ (fun v _ => mul_nonneg (hc0 _ _) (hc0 _ _))
            (fun v _ => by nlinarith [hc0 z v, hc1 z v, hc0 z' v, hc1 z' v])
      _ ≤ ∏ v ∈ Vis, exp (-(delta y ^ 2 / 2)) := by
          apply Finset.prod_le_prod₀ (fun v _ => mul_nonneg (hc0 _ _) (hc0 _ _))
          intro w hw
          have hw' := Finset.mem_filter.1 hw
          have hsum := visible_phase_sum hL hu hw'.1 ξ z z' hw'.2
          by_cases h1 : delta y / 2 < nint (phase τ y u w ξ z)
          · calc c z w * c z' w ≤ exp (-(delta y ^ 2 / 2)) * 1 :=
                  mul_le_mul (hfac _ h1) (hc1 _ _) (hc0 _ _) (by positivity)
              _ = _ := mul_one _
          · have h2 : delta y / 2 < nint (phase τ y u w ξ z') := by linarith
            calc c z w * c z' w ≤ 1 * exp (-(delta y ^ 2 / 2)) :=
                  mul_le_mul (hc1 _ _) (hfac _ h2) (hc0 _ _) zero_le_one
              _ = _ := one_mul _
      _ = exp (-(delta y ^ 2 / 2)) ^ Vis.card := Finset.prod_const _
      _ ≤ eps y ^ 2 := pow_visible_le _ hcard
  · -- (ii)
    intro hsmall
    have heps1 : eps y ≤ 1 := by
      rw [eps]; apply Real.exp_le_one_iff.2
      have : 0 ≤ ((Wset y).card : ℝ) * delta y ^ 2 / 8 := by positivity
      linarith
    have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
    calc Fcol τ y u ξ z = ∏ v ∈ Vset τ y, c z v := rfl
      _ ≤ ∏ v ∈ Vis, c z v := prod_le_prod_subset_of_le_one hVisV _ (fun v _ => hc0 _ _)
            (fun v _ => hc1 _ _)
      _ ≤ ∏ v ∈ Vis, exp (-(delta y ^ 2 / 2)) := by
          apply Finset.prod_le_prod₀ (fun v _ => hc0 _ _)
          intro w hw
          have hw' := Finset.mem_filter.1 hw
          have hsum := visible_phase_sum hL hu hw'.1 ξ z z' hw'.2
          have h2 := hsmall w hw'.1
          exact hfac _ (by linarith)
      _ = exp (-(delta y ^ 2 / 2)) ^ Vis.card := Finset.prod_const _
      _ ≤ eps y ^ 2 := pow_visible_le _ hcard
      _ ≤ eps y := by nlinarith

/-- Consequence of Lemma 8.3(i): at most one label of a column is heavy. -/
lemma heavy_unique (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z z' : ℕ)
    (hz : eps y < Fcol τ y u ξ z) (hz' : eps y < Fcol τ y u ξ z') : (u : ℤ) ∣ (z : ℤ) - z' := by
  by_contra hcon
  have h := (lem_unique hL hY hu ξ z z' hcon).1
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have : eps y * eps y < Fcol τ y u ξ z * Fcol τ y u ξ z' :=
    mul_lt_mul'' hz hz' heps0 heps0
  nlinarith

/-- **Lemma 8.4 (No wrap-around).**  Let `u ∈ U`, `ξ` row labels and `ζ_u` a column label.
If `‖φ_{vu}(ξ, ζ_u)‖ ≤ δ_a` for all `v ∈ V`, then there is an integer `M` with `|M| ≤ y^7/4`
and `ξ ≡ M (mod v)` for all `v ∈ V`; in particular `ξ` is coherent. -/
theorem lem_admissible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ)
    (h : ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y) :
    ∃ M : ℤ, (|M| : ℝ) ≤ (y : ℝ) ^ 7 / 4 ∧ ∀ v ∈ Vset τ y, (v : ℤ) ∣ (ξ : ℤ) - M := by
  set J : ℤ := ((crt τ y u ξ z : ℕ) : ℤ) with hJdef
  obtain ⟨hu8, huY, hup⟩ := mem_Uset.1 hu
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hup.pos
  have hy0 : (0 : ℝ) < y := by have := hL.y_ge; exact_mod_cast (by omega : 0 < y)
  -- `J_v`: the balanced representative of `J` modulo `uv`
  let Jv : ℕ → ℤ := fun v => J - round ((J : ℝ) / ((u : ℝ) * v)) * (u * v)
  have hJv_bound : ∀ v ∈ Vset τ y, |((Jv v : ℤ) : ℝ)| ≤ deltaA y * u * v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
    have h1 := h v hv
    unfold nint phase at h1
    have e : ((Jv v : ℤ) : ℝ) = ((u : ℝ) * v) *
        ((J : ℝ) / ((u : ℝ) * v) - round ((J : ℝ) / ((u : ℝ) * v))) := by
      simp only [Jv]; push_cast; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hJ : ((crt τ y u ξ z : ℕ) : ℝ) = (J : ℝ) := by rw [hJdef]; push_cast; rfl
    rw [hJ] at h1
    have : (0 : ℝ) < u * v := by positivity
    calc (u : ℝ) * v * |(J : ℝ) / ((u : ℝ) * v) - round ((J : ℝ) / ((u : ℝ) * v))|
        ≤ u * v * deltaA y := mul_le_mul_of_nonneg_left h1 this.le
      _ = deltaA y * u * v := by ring
  have hJv_u : ∀ v ∈ Vset τ y, |((Jv v : ℤ) : ℝ)| ≤ u / 4 := by
    intro v hv
    have hvb := (le_of_mem_Vset hL hv).2
    have hvR : (v : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by exact_mod_cast hvb
    refine (hJv_bound v hv).trans ?_
    rw [deltaA]
    have : 1 / (8 * (y : ℝ) ^ 2) * u * v = u * (v / (8 * (y : ℝ) ^ 2)) := by ring
    rw [this]
    have : v / (8 * (y : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith
  -- all `J_v` are `≡ J (mod u)`, differ by less than `u`, hence are equal
  have hJv_mod : ∀ v, (u : ℤ) ∣ J - Jv v := by
    intro v; exact ⟨round ((J : ℝ) / ((u : ℝ) * v)) * v, by simp only [Jv]; ring⟩
  have h2 : (2 : ℕ) ∈ Vset τ y := two_mem_Vset
  have hall : ∀ v ∈ Vset τ y, Jv v = Jv 2 := by
    intro v hv
    have hd : (u : ℤ) ∣ Jv v - Jv 2 := by
      have := dvd_sub (hJv_mod 2) (hJv_mod v)
      have e : J - Jv 2 - (J - Jv v) = Jv v - Jv 2 := by ring
      rwa [e] at this
    have hlt : |Jv v - Jv 2| < (u : ℤ) := by
      have h1 := hJv_u v hv
      have h2' := hJv_u 2 h2
      have : |((Jv v - Jv 2 : ℤ) : ℝ)| < (u : ℝ) := by
        push_cast
        calc |((Jv v : ℤ) : ℝ) - ((Jv 2 : ℤ) : ℝ)| ≤ |((Jv v : ℤ) : ℝ)| + |((Jv 2 : ℤ) : ℝ)| :=
              abs_sub _ _
          _ ≤ u / 4 + u / 4 := add_le_add h1 h2'
          _ < u := by linarith
      exact_mod_cast this
    have := Int.eq_zero_of_abs_lt_dvd hd hlt
    linarith
  refine ⟨Jv 2, ?_, ?_⟩
  · -- `|M| = |J_2| ≤ 2 δ_a u ≤ Y/(4y²) ≤ y^7/4`
    have h1 := hJv_bound 2 h2
    have huy : (u : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast huY.trans hY
    push_cast at h1 ⊢
    calc |((Jv 2 : ℤ) : ℝ)| ≤ deltaA y * u * 2 := h1
      _ = u / (4 * (y : ℝ) ^ 2) := by rw [deltaA]; field_simp; ring
      _ ≤ (y : ℝ) ^ 9 / (4 * (y : ℝ) ^ 2) := by gcongr
      _ = (y : ℝ) ^ 7 / 4 := by field_simp
  · -- `M = J_v ≡ J ≡ ξ (mod v)`
    intro v hv
    rw [← hall v hv]
    have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
      exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
    have hJξ : (v : ℤ) ∣ (ξ : ℤ) - J := hvP.trans (crt_modEq_xi hL hu ξ z).dvd
    have : (ξ : ℤ) - Jv v = ((ξ : ℤ) - J) + round ((J : ℝ) / ((u : ℝ) * v)) * u * v := by
      simp only [Jv]; ring
    rw [this]
    exact dvd_add hJξ (dvd_mul_left _ _)

/-- Lemma 8.4, last sentence: under its hypothesis the row labels `ξ` are coherent. -/
lemma coherent_of_admissible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y)
    (ξ z : ℕ) (h : ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y) :
    Coherent τ y ξ := by
  obtain ⟨M, hM, hMv⟩ := lem_admissible hL hY hu ξ z h
  refine ⟨M, ?_, hMv⟩
  have : ((|M| : ℤ) : ℝ) ≤ ((y ^ 7 : ℕ) : ℤ) := by
    push_cast
    have : (0 : ℝ) ≤ (y : ℝ) ^ 7 := by positivity
    linarith
  exact_mod_cast this

end

/-! ### Li (2026): §9, minor arcs -/
/-
§9 of the paper: Cases II and III, the minor arcs (Proposition 9.1).
-/

section

open Real Finset

attribute [local instance] Classical.propDecidable

variable {τ : ℚ} {y Y : ℕ}

/-! ### Generic helpers -/

/-- A single factor bounds a product of factors in `[0,1]`. -/
lemma prod_le_single_of_le_one {s : Finset ℕ} {f : ℕ → ℝ} {a : ℕ} (ha : a ∈ s)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ f a := by
  have := Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.singleton_subset_iff.2 ha) h0
    (fun i hi _ => h1 i hi)
  simpa using this

/-- `∏ (a_u + R_u) - ∏ a_u ≤ (1 + r)^n - 1` for `0 ≤ a_u ≤ 1`, `0 ≤ R_u ≤ r` (this is the
expansion over the set `T` of mismatched columns in the proof of Prop. 9.1, case II). -/
lemma prod_add_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a R : ι → ℝ) (r : ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) (hR0 : ∀ i ∈ s, 0 ≤ R i)
    (hR : ∀ i ∈ s, R i ≤ r) :
    ∏ i ∈ s, (a i + R i) - ∏ i ∈ s, a i ≤ (1 + r) ^ s.card - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have ha0' := fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    have ha1' := fun i hi => ha1 i (Finset.mem_insert_of_mem hi)
    have hR0' := fun i hi => hR0 i (Finset.mem_insert_of_mem hi)
    have hR' := fun i hi => hR i (Finset.mem_insert_of_mem hi)
    have ih' := ih ha0' ha1' hR0' hR'
    have hj0 := ha0 j (Finset.mem_insert_self j s)
    have hj1 := ha1 j (Finset.mem_insert_self j s)
    have hRj0 := hR0 j (Finset.mem_insert_self j s)
    have hRj := hR j (Finset.mem_insert_self j s)
    set P := ∏ i ∈ s, (a i + R i)
    set Q := ∏ i ∈ s, a i
    have hQ0 : 0 ≤ Q := Finset.prod_nonneg ha0'
    have hQP : Q ≤ P := Finset.prod_le_prod₀ ha0' (fun i hi => by linarith [hR0' i hi])
    have hr0 : 0 ≤ r := hRj0.trans hRj
    have hP : P ≤ (1 + r) ^ s.card := by
      calc P ≤ ∏ i ∈ s, (1 + r) := Finset.prod_le_prod₀
            (fun i hi => by linarith [ha0' i hi, hR0' i hi])
            (fun i hi => by linarith [ha1' i hi, hR' i hi])
        _ = (1 + r) ^ s.card := Finset.prod_const _
    -- `(a+R)P - aQ = a(P - Q) + R P`
    have e : (a j + R j) * P - a j * Q = a j * (P - Q) + R j * P := by ring
    rw [e, pow_succ]
    have h1 : a j * (P - Q) ≤ (1 + r) ^ s.card - 1 := by
      calc a j * (P - Q) ≤ 1 * (P - Q) := mul_le_mul_of_nonneg_right hj1 (by linarith)
        _ ≤ _ := by linarith
    have h2 : R j * P ≤ r * (1 + r) ^ s.card :=
      mul_le_mul hRj hP (hQ0.trans hQP) hr0
    nlinarith

/-- `(1 + z)^n - 1 ≤ n z e^{n z}` for `z ≥ 0`. -/
lemma one_add_pow_sub_one_le (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (1 + z) ^ n - 1 ≤ n * z * exp (n * z) := by
  have h1 : (1 + z) ^ n ≤ exp (n * z) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by linarith)
    linarith [Real.add_one_le_exp z]
  have h2 : exp (n * z) - 1 ≤ n * z * exp (n * z) := by
    have := Real.add_one_le_exp (-(n * z))
    have hpos := Real.exp_pos (n * z)
    have e : exp (-(n * z)) * exp (n * z) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  linarith

/-- For `u ∈ U`, a column label is an element of `range u`. -/
lemma toNat_emod_lt {h : ℤ} {m : ℕ} (hm : 0 < m) : (h % (m : ℤ)).toNat < m := by
  have h1 : 0 ≤ h % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have h2 : h % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  omega

/-- `m ∣ h - (h mod m)`. -/
lemma dvd_sub_toNat_emod (h : ℤ) {m : ℕ} (hm : 0 < m) : (m : ℤ) ∣ h - ((h % (m : ℤ)).toNat : ℤ) := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))]
  exact Int.dvd_self_sub_emod

/-- Column bound: with at most one heavy label and every label of weight at most `c`,
`S_u(ξ) ≤ c + u ε`. -/
lemma Scol_le_of_heavy (hL : Large τ y) (hT : Tuned τ y Y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ : ℕ)
    {c : ℝ} (hc : ∀ z, Fcol τ y u ξ z ≤ c) : Scol τ y u ξ ≤ c + u * eps y := by
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hc0 : 0 ≤ c := (Fcol_nonneg u ξ 0).trans (hc 0)
  unfold Scol
  by_cases hheavy : ∃ z0 ∈ range u, eps y < Fcol τ y u ξ z0
  · obtain ⟨z0, hz0, hz0h⟩ := hheavy
    rw [← Finset.add_sum_erase _ _ hz0]
    have hrest : ∑ z ∈ (range u).erase z0, Fcol τ y u ξ z ≤ ((range u).erase z0).card * eps y := by
      have : ∀ z ∈ (range u).erase z0, Fcol τ y u ξ z ≤ eps y := by
        intro z hz
        by_contra hcon
        push Not at hcon
        have hdvd := heavy_unique hL hT.hi hu ξ z z0 hcon hz0h
        have hz := Finset.mem_erase.1 hz
        have h1 := Finset.mem_range.1 hz.2
        have h2 := Finset.mem_range.1 hz0
        have : (z : ℤ) - z0 = 0 := by
          apply Int.eq_zero_of_abs_lt_dvd hdvd
          rw [abs_lt]; constructor <;> omega
        omega
      calc _ ≤ ∑ z ∈ (range u).erase z0, eps y := Finset.sum_le_sum this
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((range u).erase z0).card : ℝ) ≤ u := by
      rw [Finset.card_erase_of_mem hz0, Finset.card_range]
      exact_mod_cast Nat.sub_le u 1
    have := mul_le_mul_of_nonneg_right hcard heps0
    linarith [hc z0]
  · push Not at hheavy
    calc ∑ z ∈ range u, Fcol τ y u ξ z ≤ ∑ z ∈ range u, eps y := Finset.sum_le_sum hheavy
      _ = u * eps y := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ c + u * eps y := by linarith

/-- Proposition 9.1, case III, one column: for incoherent `ξ`, `S_u(ξ) ≤ e^{-δ_a²}`.
(By Lemma 8.4 every label has an entry with phase `> δ_a`, so weight `≤ e^{-2δ_a²}`; by
Lemma 8.3(i) at most one label is heavy, the others have weight `≤ ε`.) -/
theorem caseIII_column (hL : Large τ y) (hT : Tuned τ y Y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ : ℕ)
    (hξ : ¬ Coherent τ y ξ) : Scol τ y u ξ ≤ exp (-(deltaA y ^ 2)) := by
  -- every label has an entry with phase `> δ_a` (Lemma 8.4), so weight `≤ e^{-2δ_a²}`
  have hc : ∀ z, Fcol τ y u ξ z ≤ exp (-2 * deltaA y ^ 2) := by
    intro z
    have : ¬ ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y :=
      fun h => hξ (coherent_of_admissible hL hT.hi hu ξ z h)
    push Not at this
    obtain ⟨v, hv, hvd⟩ := this
    have hδa : 0 ≤ deltaA y := by rw [deltaA]; positivity
    calc Fcol τ y u ξ z ≤ |Real.cos (π * phase τ y u v ξ z)| :=
          prod_le_single_of_le_one hv (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
      _ ≤ exp (-2 * nint (phase τ y u v ξ z) ^ 2) := lem_cos _
      _ ≤ exp (-2 * deltaA y ^ 2) := by
          apply Real.exp_le_exp.2
          nlinarith
  have h1 := Scol_le_of_heavy hL hT hu ξ hc
  have hu9 : (u : ℝ) ≤ (y : ℝ) ^ 9 := by
    exact_mod_cast (bounds_of_mem_Uset hu).2.trans hT.hi
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_right hu9 heps0
  linarith [hL.colIII]

/-- Proposition 9.1, case III: `∑_{ξ incoherent} ∏_u S_u(ξ) ≤ 2b·16^{y²} e^{-δ_a²|U|} ≤ 1/4`. -/
theorem caseIII_total (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), ∏ u ∈ Uset y Y, Scol τ y u ξ
      ≤ 1 / 4 := by
  set X := exp (-(deltaA y ^ 2)) ^ (Uset y Y).card with hX
  have h1 : ∀ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
      ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ X := by
    intro ξ hξ
    have hξ' := (Finset.mem_filter.1 hξ).2
    calc ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ ∏ u ∈ Uset y Y, exp (-(deltaA y ^ 2)) :=
          Finset.prod_le_prod₀ (fun u _ => Scol_nonneg u ξ)
            (fun u hu => caseIII_column hL hT hu ξ hξ')
      _ = X := Finset.prod_const _
  have hX0 : 0 ≤ X := by positivity
  have h2 : ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
      ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ (PV τ y : ℝ) * X := by
    calc _ ≤ ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), X :=
          Finset.sum_le_sum h1
      _ = (((range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ))).card : ℝ) * X := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PV τ y : ℝ) * X := by
          apply mul_le_mul_of_nonneg_right _ hX0
          have := Finset.card_filter_le (range (PV τ y)) (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ))
          rw [Finset.card_range] at this
          exact_mod_cast this
  -- `e^{-δ_a² |U|} ≤ exp(-τ y⁴/(64 H_V))` since `|U| ≥ τ y^8/H_V`
  have hHV := HV_pos hL
  have hy0 : (0 : ℝ) < y := by have := hL.y_ge; exact_mod_cast (by omega : 0 < y)
  have h3 : X ≤ exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) := by
    rw [hX, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hU := hT.card_U
    have e1 : deltaA y ^ 2 = 1 / (64 * (y : ℝ) ^ 4) := by rw [deltaA]; field_simp; ring
    rw [e1]
    have e2 : (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) =
        ((τ : ℝ) * (y : ℝ) ^ 8 / HV τ y) * (1 / (64 * (y : ℝ) ^ 4)) := by
      field_simp
    rw [e2]
    have : 0 ≤ 1 / (64 * (y : ℝ) ^ 4) := by positivity
    nlinarith
  have h4 := prod_V_le (τ := τ) (y := y)
  have h5 := hL.caseIII
  have hPV : (PV τ y : ℝ) = ((∏ v ∈ Vset τ y, v : ℕ) : ℝ) := rfl
  calc _ ≤ (PV τ y : ℝ) * X := h2
    _ ≤ (2 * (τ.den : ℝ) * 16 ^ (y ^ 2)) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) := by
        apply mul_le_mul (hPV ▸ h4) h3 hX0 (by positivity)
    _ ≤ 1 / 4 := h5

/-- Proposition 9.1, case II, for one coherent `ξ ≡ M`: the frequencies with some mismatched
column contribute `∏_u S_u(ξ) - ∏_u F_u(ξ, M mod u) ≤ |U| Y ε e^{|U| Y ε}`. -/
theorem caseII_single (hL : Large τ y) (hT : Tuned τ y Y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    ∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat
      ≤ (Uset y Y).card * Y * eps y * exp ((Uset y Y).card * Y * eps y) := by
  set ξ := (M % (PV τ y : ℤ)).toNat with hξ
  set m : ℕ → ℕ := fun u => (M % (u : ℤ)).toNat with hm
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy3 := hL.y_ge
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hPV0 : 0 < PV τ y := by
    have := PV_gt_y8 hL; omega
  -- the matching label `M mod u` has small phases in the test rows, so every mismatched label
  -- has weight `≤ ε` (Lemma 8.3(ii))
  have hmis : ∀ u ∈ Uset y Y, ∀ z ∈ (range u).erase (m u), Fcol τ y u ξ z ≤ eps y := by
    intro u hu z hz
    have hu0 : 0 < u := (prime_of_mem_Uset hu).pos
    have hz' := Finset.mem_erase.1 hz
    apply (lem_unique hL hT.hi hu ξ z (m u) ?_).2 ?_
    · intro hd
      have h1 := Finset.mem_range.1 hz'.2
      have h2 : m u < u := toNat_emod_lt hu0
      have : (z : ℤ) - (m u : ℕ) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd hd
        rw [abs_lt]; constructor <;> omega
      exact hz'.1 (by omega)
    · intro w hw
      have hwV := Wset_subset_Vset (τ := τ) hw
      have hwP : (w : ℤ) ∣ (PV τ y : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hwV
      obtain ⟨n, hn⟩ := phase_congr hL hu hwV ξ (m u) M
        (hwP.trans (dvd_sub_toNat_emod M hPV0)) (dvd_sub_toNat_emod M hu0)
      rw [hn, nint_add_int]
      obtain ⟨hw1, -, -⟩ := mem_Wset.1 hw
      obtain ⟨hu1, -, -⟩ := mem_Uset.1 hu
      have hw1' : (y : ℝ) ^ 2 < w := by exact_mod_cast hw1
      have hu1' : (y : ℝ) ^ 8 < u := by exact_mod_cast hu1
      have hM' : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by
        have : ((|M| : ℤ) : ℝ) ≤ (((y : ℤ) ^ 7 : ℤ) : ℝ) := by exact_mod_cast hM
        push_cast at this; exact this
      have huw : (y : ℝ) ^ 10 < (u : ℝ) * w := by
        have : (y : ℝ) ^ 10 = (y : ℝ) ^ 8 * (y : ℝ) ^ 2 := by ring
        rw [this]
        exact mul_lt_mul'' hu1' hw1' (by positivity) (by positivity)
      calc nint ((M : ℝ) / ((u : ℝ) * w)) ≤ |(M : ℝ) / ((u : ℝ) * w)| := nint_le_abs _
        _ = |(M : ℝ)| / ((u : ℝ) * w) := by
            rw [abs_div, abs_of_pos (a := (u : ℝ) * w) (lt_trans (by positivity) huw)]
        _ ≤ (y : ℝ) ^ 7 / (y : ℝ) ^ 10 := by
            exact div_le_div₀ (by positivity) hM' (by positivity) huw.le
        _ = 1 / (y : ℝ) ^ 3 := by field_simp
        _ ≤ delta y / 2 := hL.phase
  -- `S_u = F_u(ξ, M mod u) + R_u` with `R_u ≤ Y ε`
  set R : ℕ → ℝ := fun u => ∑ z ∈ (range u).erase (m u), Fcol τ y u ξ z with hR
  have hS : ∀ u ∈ Uset y Y, Scol τ y u ξ = Fcol τ y u ξ (m u) + R u := by
    intro u hu
    unfold Scol
    rw [hR, Finset.add_sum_erase _ _ (Finset.mem_range.2 (toNat_emod_lt (prime_of_mem_Uset hu).pos))]
  have hRb : ∀ u ∈ Uset y Y, R u ≤ Y * eps y := by
    intro u hu
    calc R u ≤ ∑ z ∈ (range u).erase (m u), eps y := Finset.sum_le_sum (hmis u hu)
      _ = (((range u).erase (m u)).card : ℝ) * eps y := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Y * eps y := by
          apply mul_le_mul_of_nonneg_right _ heps0
          have h1 := Finset.card_erase_le (s := range u) (a := m u)
          rw [Finset.card_range] at h1
          have h2 := (bounds_of_mem_Uset hu).2
          exact_mod_cast h1.trans h2
  have hR0 : ∀ u ∈ Uset y Y, 0 ≤ R u := fun u _ => Finset.sum_nonneg (fun _ _ => Fcol_nonneg _ _ _)
  rw [Finset.prod_congr rfl hS]
  have := prod_add_sub_prod_le (Uset y Y) (fun u => Fcol τ y u ξ (m u)) R (Y * eps y)
    (fun u _ => Fcol_nonneg _ _ _) (fun u _ => Fcol_le_one _ _ _) hR0 hRb
  refine this.trans ?_
  have h := one_add_pow_sub_one_le (Uset y Y).card (z := Y * eps y) (by positivity)
  calc _ ≤ _ := h
    _ = _ := by ring_nf


/-- Proposition 9.1, case II: summing over the `2y^7+1 ≤ 3y^7` values of `M` gives `≤ 1/4`. -/
theorem caseII_total (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7),
      (∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat) ≤ 1 / 4 := by
  set B := ((Uset y Y).card : ℝ) * Y * eps y * exp ((Uset y Y).card * Y * eps y) with hB
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy3 := hL.y_ge
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast (by omega : 1 ≤ y)
  have hYR : (Y : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast hT.hi
  have hUR : ((Uset y Y).card : ℝ) ≤ (y : ℝ) ^ 9 := by
    have : (Uset y Y).card ≤ Y := by
      calc (Uset y Y).card ≤ (Finset.Ioc (y ^ 8) Y).card := Finset.card_filter_le _ _
        _ = Y - y ^ 8 := Nat.card_Ioc _ _
        _ ≤ Y := Nat.sub_le _ _
    exact le_trans (by exact_mod_cast this) hYR
  have hUY : ((Uset y Y).card : ℝ) * Y * eps y ≤ (y : ℝ) ^ 18 * eps y := by
    have : ((Uset y Y).card : ℝ) * Y ≤ (y : ℝ) ^ 9 * (y : ℝ) ^ 9 :=
      mul_le_mul hUR hYR (by positivity) (by positivity)
    have e : (y : ℝ) ^ 18 = (y : ℝ) ^ 9 * (y : ℝ) ^ 9 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right this heps0
  have hB' : B ≤ (y : ℝ) ^ 18 * eps y * exp ((y : ℝ) ^ 18 * eps y) := by
    rw [hB]
    apply mul_le_mul hUY (Real.exp_le_exp.2 hUY) (by positivity) (by positivity)
  have hcard : ((Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7)).card : ℝ) ≤ 3 * (y : ℝ) ^ 7 := by
    rw [Int.card_Icc]
    have h7 : (1 : ℤ) ≤ (y : ℤ) ^ 7 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ y))
    have : ((y : ℤ) ^ 7 + 1 - -(y : ℤ) ^ 7).toNat ≤ 3 * y ^ 7 := by
      have : ((y : ℤ) ^ 7 + 1 - -(y : ℤ) ^ 7) ≤ 3 * (y : ℤ) ^ 7 := by linarith
      have h' : (((3 * y ^ 7 : ℕ)) : ℤ) = 3 * (y : ℤ) ^ 7 := by push_cast; ring
      omega
    exact_mod_cast this
  calc _ ≤ ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7), B := by
        apply Finset.sum_le_sum
        intro M hM
        have hM' : |M| ≤ (y : ℤ) ^ 7 := abs_le.2 (Finset.mem_Icc.1 hM)
        exact caseII_single hL hT hM'
    _ = ((Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * (y : ℝ) ^ 7) * ((y : ℝ) ^ 18 * eps y * exp ((y : ℝ) ^ 18 * eps y)) :=
        mul_le_mul hcard hB' (by positivity) (by positivity)
    _ = 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) := by ring
    _ ≤ 1 / 4 := hL.caseII


/-- Passing from frequencies to labels (via eq. (4) and the injectivity of the label map):
the case III frequencies contribute at most `∑_{ξ incoherent} ∏_u S_u(ξ)`, and the case II
frequencies at most `∑_M (∏_u S_u(M) - ∏_u F_u(M, M mod u))`. -/
theorem minor_le_labels (hL : Large τ y) :
    ∑ h ∈ (freq (Lnum τ y Y)).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖
      ≤ ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), ∏ u ∈ Uset y Y, Scol τ y u ξ
        + ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7),
          (∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
            - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat) := by
  set L := Lnum τ y Y with hLdef
  set P := PV τ y with hPdef
  have hP0 : 0 < P := by have := PV_gt_y8 hL; omega
  have hP0' : (P : ℤ) ≠ 0 := by exact_mod_cast hP0.ne'
  -- the label map `h ↦ (ξ, ζ)` and the column-product `G(ξ, ζ) = ∏_u F_u(ξ, ζ_u)`
  let col : ℤ → (Uset y Y → ℕ) := fun h u => (h % ((u : ℕ) : ℤ)).toNat
  let lab : ℤ → ℕ × (Uset y Y → ℕ) := fun h => ((h % (P : ℤ)).toNat, col h)
  let G : ℕ × (Uset y Y → ℕ) → ℝ := fun x => ∏ u : Uset y Y, Fcol τ y u x.1 (x.2 u)
  have hG0 : ∀ x, 0 ≤ G x := fun x => Finset.prod_nonneg (fun _ _ => Fcol_nonneg _ _ _)
  have hphi : ∀ h, ‖phi (Aset τ y Y) h‖ = G (lab h) := by
    intro h
    rw [norm_phi_eq_prod_Fcol hL]
    exact (Finset.prod_coe_sort (Uset y Y)
      (fun u => Fcol τ y u (h % (P : ℤ)).toNat (h % (u : ℤ)).toNat)).symm
  have hu0 : ∀ u : Uset y Y, 0 < (u : ℕ) := fun u => (prime_of_mem_Uset u.2).pos
  have hcol_mem : ∀ h, col h ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)) := by
    intro h
    rw [Fintype.mem_piFinset]
    intro u
    exact Finset.mem_range.2 (toNat_emod_lt (hu0 u))
  -- equal column labels give divisibility by each `u`
  have hcol_dvd : ∀ h h', col h = col h' → ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - h' := by
    intro h h' he u hu
    have := congrFun he ⟨u, hu⟩
    simp only [col] at this
    have h1 := Int.toNat_of_nonneg (Int.emod_nonneg h (b := (u : ℤ))
      (by exact_mod_cast (prime_of_mem_Uset hu).ne_zero))
    have h2 := Int.toNat_of_nonneg (Int.emod_nonneg h' (b := (u : ℤ))
      (by exact_mod_cast (prime_of_mem_Uset hu).ne_zero))
    have h3 : h % (u : ℤ) = h' % (u : ℤ) := by rw [← h1, ← h2, this]
    exact Int.ModEq.dvd h3.symm
  -- equal row labels give divisibility by `P_V`
  have hrow_dvd : ∀ h h', (h % (P : ℤ)).toNat = (h' % (P : ℤ)).toNat → (P : ℤ) ∣ h - h' := by
    intro h h' he
    have h1 := Int.toNat_of_nonneg (Int.emod_nonneg h hP0')
    have h2 := Int.toNat_of_nonneg (Int.emod_nonneg h' hP0')
    have h3 : h % (P : ℤ) = h' % (P : ℤ) := by rw [← h1, ← h2, he]
    exact Int.ModEq.dvd h3.symm
  -- Step 0: split cases II and III
  have hsplit : ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖ ≤
      ∑ h ∈ (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ +
      ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h), ‖phi (Aset τ y Y) h‖ := by
    rw [Finset.filter_or]
    have e := Finset.sum_union_inter (s₁ := (freq L).filter (fun h => CaseII τ y Y h))
      (s₂ := (freq L).filter (fun h => CaseIII τ y h)) (f := fun h => ‖phi (Aset τ y Y) h‖)
    have : 0 ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h) ∩
        (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  -- Step 1: case III, via the injective label map and eq. (4)
  have h3 : ∑ h ∈ (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ ≤
      ∑ ξ ∈ (range P).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
        ∏ u ∈ Uset y Y, Scol τ y u ξ := by
    set s := (freq L).filter (fun h => CaseIII τ y h)
    have hinj : Set.InjOn lab s := by
      intro h hh h' hh' he
      have hh := (Finset.mem_filter.1 hh).1
      have hh' := (Finset.mem_filter.1 hh').1
      have e1 := congrArg Prod.fst he
      have e2 := congrArg Prod.snd he
      exact label_inj hh hh' (hrow_dvd h h' e1) (hcol_dvd h h' e2)
    set T := (range P).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)) ×ˢ
      Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))
    have himg : s.image lab ⊆ T := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
      have hIII := (Finset.mem_filter.1 hh).2
      refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 (toNat_emod_lt hP0), ?_⟩,
        hcol_mem h⟩
      -- `h ≡ ξ (mod P_V)`, so coherence of `ξ` would give coherence of `h`
      rintro ⟨M, hM, hMv⟩
      apply hIII
      refine ⟨M, hM, fun v hv => ?_⟩
      have hvP : (v : ℤ) ∣ (P : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
      have := dvd_add (hvP.trans (dvd_sub_toNat_emod h hP0)) (hMv v hv)
      simp only [lab] at this
      have e : h - (((h % (P : ℤ)).toNat : ℕ) : ℤ) + ((((h % (P : ℤ)).toNat : ℕ) : ℤ) - M) =
        h - M := by ring
      rwa [e] at this
    calc ∑ h ∈ s, ‖phi (Aset τ y Y) h‖ = ∑ h ∈ s, G (lab h) := Finset.sum_congr rfl (fun h _ => hphi h)
      _ = ∑ x ∈ s.image lab, G x := (Finset.sum_image hinj).symm
      _ ≤ ∑ x ∈ T, G x := Finset.sum_le_sum_of_subset_of_nonneg himg (fun x _ _ => hG0 x)
      _ = _ := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl (fun ξ _ => ?_)
          exact eq_factor ξ
  -- Step 2: case II.  First a union bound over the (unique) `M`.
  set K := (y : ℤ) ^ 7
  let Q : ℤ → ℤ → Prop := fun M h =>
    (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧ ∃ u ∈ Uset y Y, ¬ (u : ℤ) ∣ h - M
  have h2a : ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h), ‖phi (Aset τ y Y) h‖ ≤
      ∑ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (Q M), ‖phi (Aset τ y Y) h‖ := by
    calc _ ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h),
          ∑ M ∈ Finset.Icc (-K) K, (if Q M h then ‖phi (Aset τ y Y) h‖ else 0) := by
          apply Finset.sum_le_sum
          intro h hh
          obtain ⟨M, hM, hMv, hMu⟩ := (Finset.mem_filter.1 hh).2
          have hMI : M ∈ Finset.Icc (-K) K := Finset.mem_Icc.2 (abs_le.1 hM)
          have := Finset.single_le_sum (f := fun M => if Q M h then ‖phi (Aset τ y Y) h‖ else 0)
            (fun M _ => by positivity) hMI
          rw [ite_eq_left ⟨hMv, hMu⟩] at this
          exact this
      _ = ∑ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h),
          (if Q M h then ‖phi (Aset τ y Y) h‖ else 0) := Finset.sum_comm
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro M _
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro h hh
            simp only [Finset.mem_filter] at hh ⊢
            exact ⟨hh.1.1, hh.2⟩
          · intros; exact norm_nonneg _
  -- For fixed `M`: inject `h ↦ ζ(h)` into the mismatched column labels.
  have h2b : ∀ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (Q M), ‖phi (Aset τ y Y) h‖ ≤
      ∏ u ∈ Uset y Y, Scol τ y u (M % (P : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (P : ℤ)).toNat (M % (u : ℤ)).toNat := by
    intro M _
    set ξM := (M % (P : ℤ)).toNat
    set s := (freq L).filter (Q M)
    let G' : (Uset y Y → ℕ) → ℝ := fun ζ => ∏ u : Uset y Y, Fcol τ y u ξM (ζ u)
    have hPdvd : ∀ h ∈ s, (P : ℤ) ∣ h - M := by
      intro h hh
      exact prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv) _
        (Finset.mem_filter.1 hh).2.1
    have hrow : ∀ h ∈ s, (h % (P : ℤ)).toNat = ξM := by
      intro h hh
      have : h % (P : ℤ) = M % (P : ℤ) := (Int.modEq_iff_dvd.2 (hPdvd h hh)).symm
      simp only [ξM, this]
    have hinj : Set.InjOn col s := by
      intro h hh h' hh' he
      have hd : (P : ℤ) ∣ h - h' := by
        have := dvd_sub (hPdvd h hh) (hPdvd h' hh')
        have e : h - M - (h' - M) = h - h' := by ring
        rwa [e] at this
      exact label_inj (Finset.mem_filter.1 hh).1 (Finset.mem_filter.1 hh').1 hd
        (hcol_dvd h h' he)
    set ζM : Uset y Y → ℕ := col M
    have hζM : ζM ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)) := hcol_mem M
    have himg : s.image col ⊆ (Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))).erase ζM := by
      intro ζ hζ
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hζ
      refine Finset.mem_erase.2 ⟨fun he => ?_, hcol_mem h⟩
      obtain ⟨u, hu, hnd⟩ := (Finset.mem_filter.1 hh).2.2
      exact hnd (hcol_dvd h M he u hu)
    calc ∑ h ∈ s, ‖phi (Aset τ y Y) h‖ = ∑ h ∈ s, G' (col h) := by
          refine Finset.sum_congr rfl (fun h hh => ?_)
          rw [hphi h]
          simp only [G, G', lab, hrow h hh]
      _ = ∑ ζ ∈ s.image col, G' ζ := (Finset.sum_image hinj).symm
      _ ≤ ∑ ζ ∈ (Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))).erase ζM, G' ζ :=
          Finset.sum_le_sum_of_subset_of_nonneg himg
            (fun ζ _ _ => Finset.prod_nonneg (fun _ _ => Fcol_nonneg _ _ _))
      _ = ∑ ζ ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)), G' ζ - G' ζM :=
          Finset.sum_erase_eq_sub hζM
      _ = _ := by
          rw [eq_factor ξM]
          congr 1
          exact Finset.prod_coe_sort (Uset y Y)
            (fun u => Fcol τ y u ξM (M % (u : ℤ)).toNat)
  have h2 := h2a.trans (Finset.sum_le_sum h2b)
  linarith

/-- **Proposition 9.1 (minor arcs).**  For `y` large, `∑_{h in cases II and III} |φ(h)| ≤ 1/2`. -/
theorem prop_minor (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ h ∈ (freq (Lnum τ y Y)).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖ ≤ 1 / 2 := by
  have h1 := minor_le_labels (Y := Y) hL
  have h2 := caseIII_total hL hT
  have h3 := caseII_total hL hT
  linarith

end

/-! ### Li (2026): asymptotic thresholds -/
/-
All "for `y` sufficiently large" statements of the paper, collected: every field of `Large τ y`
holds for all large `y`.
-/

section

open Real Finset

/-- The bound for `ε` stated in §8.1: `ε ≤ exp(-y²/(2·10⁷ log³ y))` (from eq. (1)). -/
lemma eps_le {y : ℕ} (hy : 3 ≤ y) (hW : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card) :
    eps y ≤ exp (-((y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3))) := by
  unfold eps delta
  apply Real.exp_le_exp.2
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hy2 : (0 : ℝ) ≤ (y : ℝ) ^ 2 := by positivity
  have hdelta : (1 / (400 * log (y : ℝ))) ^ 2 / 8 = 1 / (1280000 * log y ^ 2) := by
    field_simp; ring
  have h1 : (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3) ≤
      (y : ℝ) ^ 2 / (8 * log y) * (1 / (1280000 * log y ^ 2)) := by
    rw [div_mul_div_comm, mul_one]
    apply div_le_div_of_nonneg_left hy2 (by positivity)
    nlinarith [pow_pos hlog 3]
  have h2 : (y : ℝ) ^ 2 / (8 * log y) * (1 / (1280000 * log y ^ 2)) ≤
      (Wset y).card * (1 / (1280000 * log y ^ 2)) :=
    mul_le_mul_of_nonneg_right hW (by positivity)
  rw [mul_div_assoc, hdelta]
  linarith

/-- A `y`-uniform version of the bounds eq. (1) for `H_V`:
`½ ≤ H_V ≤ 3/2 + ∑_{r ∈ B} 1/r` for every `y ≥ 1` (using `∑_{w ∈ W} 1/w ≤ |W|/y² ≤ 1`). -/
lemma HV_bounds_uniform (τ : ℚ) {y : ℕ} (hy : 1 ≤ y) :
    1 / 2 ≤ HV τ y ∧ HV τ y ≤ 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r := by
  have hnn : ∀ s : Finset ℕ, 0 ≤ ∑ i ∈ s, (1 : ℝ) / i := fun s => by positivity
  constructor
  · unfold HV
    have := Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / v)
      (fun i _ => by positivity) (two_mem_Vset (τ := τ) (y := y))
    simpa using this
  · -- `∑_{w ∈ W} 1/w ≤ 1`
    have hW : ∑ w ∈ Wset y, (1 : ℝ) / w ≤ 1 := by
      have hy2 : (0 : ℝ) < (y : ℝ) ^ 2 := by positivity
      calc ∑ w ∈ Wset y, (1 : ℝ) / w ≤ ∑ w ∈ Wset y, (1 : ℝ) / (y : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro w hw
            have := (mem_Wset.1 hw).1
            apply one_div_le_one_div_of_le hy2
            exact_mod_cast this.le
        _ = (Wset y).card / (y : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 := by
            rw [div_le_one hy2]
            have : (Wset y).card ≤ y ^ 2 := by
              calc (Wset y).card ≤ (Finset.Ioc (y ^ 2) (2 * y ^ 2)).card :=
                    Finset.card_filter_le _ _
                _ = y ^ 2 := by simp; omega
            exact_mod_cast this
    have hunion : ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v ≤
        ∑ v ∈ Bset τ, (1 : ℝ) / v + ∑ v ∈ Wset y, (1 : ℝ) / v := by
      rw [← Finset.sum_union_inter]
      linarith [hnn (Bset τ ∩ Wset y)]
    have hins : HV τ y ≤ 1 / 2 + ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v := by
      unfold HV Vset
      by_cases h2 : 2 ∈ Bset τ ∪ Wset y
      · rw [Finset.insert_eq_of_mem h2]; linarith
      · rw [Finset.sum_insert h2]; norm_num
    linarith

/-- `y^30 ε ≤ 1` for large `y` (the only place where the super-polynomial decay of `ε`,
`ε ≤ exp(-y²/(2·10⁷ log³ y))`, is used). -/
lemma y30_eps_le {y : ℕ} (hy : 2 * 10 ^ 11 ≤ y)
    (hW : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card) : (y : ℝ) ^ 30 * eps y ≤ 1 := by
  have hy3 : 3 ≤ y := by omega
  have hyR : (2 * 10 ^ 11 : ℝ) ≤ y := by exact_mod_cast hy
  have hypos : (0 : ℝ) < y := by linarith
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  -- `log y ≤ 4 y^{1/4}`, hence `log⁴ y ≤ 256 y`
  have hl4 : log (y : ℝ) ^ 4 ≤ 256 * y := by
    have h1 := Real.log_le_rpow_div hypos.le (by norm_num : (0 : ℝ) < 1 / 4)
    have h2 : ((y : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hypos.le]; norm_num
    calc log (y : ℝ) ^ 4 ≤ ((y : ℝ) ^ (1 / 4 : ℝ) / (1 / 4)) ^ 4 :=
          pow_le_pow_left₀ hlog.le h1 4
      _ = 256 * ((y : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by ring
      _ = 256 * y := by rw [h2]
  -- hence `30 log y ≤ y²/(2·10⁷ log³ y)`
  have hkey : 30 * log (y : ℝ) ≤ (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    have : 30 * log (y : ℝ) * (2 * 10 ^ 7 * log y ^ 3) = 6 * 10 ^ 8 * log y ^ 4 := by ring
    rw [this]
    nlinarith
  have he := eps_le hy3 hW
  have hy30 : (y : ℝ) ^ 30 = exp (30 * log y) := by
    rw [show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hypos]
  rw [hy30]
  calc exp (30 * log y) * eps y
      ≤ exp (30 * log y) * exp (-((y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3))) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = exp (30 * log y - (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3)) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ exp 0 := Real.exp_le_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

/-- `|W| ≥ y²/(8 log y)` for large `y` (eq. (1), from Lemma 2.1 with `x = 2y²`). -/
lemma card_W_eventually : ∃ y0 : ℕ, ∀ y ≥ y0, (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card := by
  obtain ⟨x0, hx0⟩ := lem_cheb
  refine ⟨max 12 ⌈x0⌉₊, fun y hy => ?_⟩
  have hy12 : 12 ≤ y := le_trans (le_max_left _ _) hy
  have hyx : ⌈x0⌉₊ ≤ y := le_trans (le_max_right _ _) hy
  have hyR : (12 : ℝ) ≤ y := by exact_mod_cast hy12
  have hx : x0 ≤ 2 * (y : ℝ) ^ 2 := by
    calc x0 ≤ (⌈x0⌉₊ : ℝ) := Nat.le_ceil x0
      _ ≤ y := by exact_mod_cast hyx
      _ ≤ 2 * (y : ℝ) ^ 2 := by nlinarith
  have h := hx0 _ hx
  have hf1 : ⌊2 * (y : ℝ) ^ 2 / 2⌋₊ = y ^ 2 := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact_mod_cast Nat.floor_natCast (y ^ 2)
  have hf2 : ⌊2 * (y : ℝ) ^ 2⌋₊ = 2 * y ^ 2 := by exact_mod_cast Nat.floor_natCast (2 * y ^ 2)
  rw [hf1, hf2] at h
  refine le_trans ?_ h
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  have hlog2 : log (2 * (y : ℝ) ^ 2) = log 2 + 2 * log y := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  -- `7 log 2 ≤ 2 log y` since `2^7 ≤ y²`
  have h7 : 7 * log (2 : ℝ) ≤ 2 * log y := by
    have : log ((2 : ℝ) ^ 7) ≤ log ((y : ℝ) ^ 2) := Real.log_le_log (by norm_num) (by nlinarith)
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [hlog2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hy2 : (0 : ℝ) ≤ (y : ℝ) ^ 2 := by positivity
  nlinarith

/-- Numerics for Proposition 9.1, case III (one column):
`e^{-2δ_a²} + y^9 ε ≤ e^{-δ_a²}`, since `e^{-x} - e^{-2x} ≥ x/2` and `y^9 ε ≤ 1/(128 y⁴)`. -/
lemma colIII_numeric {y : ℕ} (hy : 128 ≤ y) (heps : (y : ℝ) ^ 30 * eps y ≤ 1) :
    exp (-2 * deltaA y ^ 2) + (y : ℝ) ^ 9 * eps y ≤ exp (-(deltaA y ^ 2)) := by
  have hyR : (128 : ℝ) ≤ y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  set x := deltaA y ^ 2 with hx
  have hxy : x = 1 / (64 * (y : ℝ) ^ 4) := by rw [hx]; unfold deltaA; field_simp; ring
  have hx0 : 0 ≤ x := by rw [hxy]; positivity
  have hx4 : x ≤ 1 / 4 := by
    rw [hxy, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [one_le_pow₀ (n := 4) hy1]
  have hdiff : x / 2 ≤ exp (-x) - exp (-2 * x) := by
    have h1 : exp (-x) - exp (-2 * x) = exp (-2 * x) * (exp x - 1) := by
      rw [mul_sub, ← Real.exp_add]; ring_nf
    have h2 : x ≤ exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h3 : 1 - 2 * x ≤ exp (-2 * x) := by linarith [Real.add_one_le_exp (-2 * x)]
    rw [h1]
    nlinarith
  have hy9 : (y : ℝ) ^ 9 * eps y ≤ x / 2 := by
    rw [hxy]
    have hy17 : (128 : ℝ) ≤ (y : ℝ) ^ 17 := le_trans hyR (le_self_pow₀ hy1 (by norm_num))
    have : (y : ℝ) ^ 9 * eps y * (128 * (y : ℝ) ^ 4) ≤ 1 := by
      calc (y : ℝ) ^ 9 * eps y * (128 * (y : ℝ) ^ 4) = 128 * ((y : ℝ) ^ 13 * eps y) := by ring
        _ ≤ (y : ℝ) ^ 17 * ((y : ℝ) ^ 13 * eps y) :=
            mul_le_mul_of_nonneg_right hy17 (by positivity)
        _ = (y : ℝ) ^ 30 * eps y := by ring
        _ ≤ 1 := heps
    rw [div_div, le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- Numerics for Proposition 9.1, case II: `3y^{25} ε e^{y^{18} ε} ≤ 1/4`. -/
lemma caseII_numeric {y : ℕ} (hy : 36 ≤ y) (heps : (y : ℝ) ^ 30 * eps y ≤ 1) :
    3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) ≤ 1 / 4 := by
  have hyR : (36 : ℝ) ≤ y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy12 : (1 : ℝ) ≤ (y : ℝ) ^ 12 := one_le_pow₀ hy1
  have h18 : (y : ℝ) ^ 18 * eps y ≤ 1 := by
    calc (y : ℝ) ^ 18 * eps y ≤ (y : ℝ) ^ 12 * ((y : ℝ) ^ 18 * eps y) :=
          le_mul_of_one_le_left (by positivity) hy12
      _ = (y : ℝ) ^ 30 * eps y := by ring
      _ ≤ 1 := heps
  have hexp : exp ((y : ℝ) ^ 18 * eps y) ≤ 3 := by
    calc exp ((y : ℝ) ^ 18 * eps y) ≤ exp 1 := Real.exp_le_exp.2 h18
      _ ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h25 : 36 * ((y : ℝ) ^ 25 * eps y) ≤ 1 := by
    have hy5 : (36 : ℝ) ≤ (y : ℝ) ^ 5 := le_trans hyR (le_self_pow₀ hy1 (by norm_num))
    calc 36 * ((y : ℝ) ^ 25 * eps y) ≤ (y : ℝ) ^ 5 * ((y : ℝ) ^ 25 * eps y) :=
          mul_le_mul_of_nonneg_right hy5 (by positivity)
      _ = (y : ℝ) ^ 30 * eps y := by ring
      _ ≤ 1 := heps
  have hpos : 0 ≤ 3 * (y : ℝ) ^ 25 * eps y := by positivity
  calc 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y)
      ≤ 3 * (y : ℝ) ^ 25 * eps y * 3 := mul_le_mul_of_nonneg_left hexp hpos
    _ ≤ 1 / 4 := by linarith

/-- Numerics for Proposition 9.1, case III (total): with `C ≥ H_V` and `y² ≥ Q`,
`2b·16^{y²}·exp(-τy⁴/(64 H_V)) ≤ 1/4`. -/
lemma caseIII_numeric {τ : ℚ} {y : ℕ} (hτ : 0 < τ) {C : ℝ} (hHV0 : 0 < HV τ y)
    (hHVC : HV τ y ≤ C) (hy1 : (1 : ℝ) ≤ y)
    (hyQ : 64 * C * (log (8 * τ.den) + log 16) / τ ≤ (y : ℝ) ^ 2) :
    2 * (τ.den : ℝ) * 16 ^ (y ^ 2) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) ≤ 1 / 4 := by
  have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hden1 : (1 : ℝ) ≤ τ.den := by exact_mod_cast τ.den_pos
  have hlog8b : 0 ≤ log (8 * (τ.den : ℝ)) := Real.log_nonneg (by linarith)
  have hlog16 : 0 < log (16 : ℝ) := Real.log_pos (by norm_num)
  have hC0 : 0 < C := lt_of_lt_of_le hHV0 hHVC
  have h16 : (16 : ℝ) ^ (y ^ 2) = exp ((y : ℝ) ^ 2 * log 16) := by
    rw [show ((y : ℝ) ^ 2) = ((y ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
  have h8b : 2 * (τ.den : ℝ) = exp (log (8 * τ.den)) / 4 := by
    rw [Real.exp_log (by positivity)]; ring
  have hexp : (y : ℝ) ^ 2 * log 16 + log (8 * τ.den) ≤ (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) := by
    have h1 : (τ : ℝ) * (y : ℝ) ^ 4 / (64 * C) ≤ (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    refine le_trans ?_ h1
    have hQ' : 64 * C * (log (8 * τ.den) + log 16) ≤ τ * (y : ℝ) ^ 2 := by
      rwa [div_le_iff₀ hτR, mul_comm ((y : ℝ) ^ 2)] at hyQ
    rw [le_div_iff₀ (by positivity)]
    have hy2 : (1 : ℝ) ≤ (y : ℝ) ^ 2 := one_le_pow₀ hy1
    calc ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den)) * (64 * C)
        ≤ (y : ℝ) ^ 2 * (64 * C * (log (8 * τ.den) + log 16)) := by
          have e : (y : ℝ) ^ 2 * (64 * C * (log (8 * τ.den) + log 16)) -
              ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den)) * (64 * C) =
              ((y : ℝ) ^ 2 - 1) * (64 * C * log (8 * τ.den)) := by ring
          have : 0 ≤ ((y : ℝ) ^ 2 - 1) * (64 * C * log (8 * τ.den)) := by
            apply mul_nonneg (by linarith); positivity
          linarith
      _ ≤ (y : ℝ) ^ 2 * (τ * (y : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hQ' (by positivity)
      _ = τ * (y : ℝ) ^ 4 := by ring
  rw [h16, h8b]
  calc exp (log (8 * τ.den)) / 4 * exp ((y : ℝ) ^ 2 * log 16) *
        exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)))
      = exp ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den) -
          (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)) / 4 := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]; ring
    _ ≤ exp 0 / 4 := by gcongr; linarith
    _ = 1 / 4 := by rw [Real.exp_zero]

/-- Numerics for Lemma 8.2 and Proposition 9.1 (case II): `800 log y ≤ y²` gives
`y²/(20 log y) + 10 ≤ y²/(16 log y)` and `y^{-3} ≤ δ/2`. -/
lemma count_phase_numeric {y : ℕ} (hy : 800 ≤ y) :
    (y : ℝ) ^ 2 / (20 * log y) + 10 ≤ (y : ℝ) ^ 2 / (16 * log y) ∧
      1 / (y : ℝ) ^ 3 ≤ delta y / 2 := by
  have hyR : (800 : ℝ) ≤ y := by exact_mod_cast hy
  have hypos : (0 : ℝ) < y := by linarith
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  have hlogy : log (y : ℝ) ≤ y := le_trans (Real.log_le_sub_one_of_pos hypos) (by linarith)
  have h800 : 800 * log (y : ℝ) ≤ (y : ℝ) ^ 2 := by nlinarith
  constructor
  · have e : (y : ℝ) ^ 2 / (16 * log y) - (y : ℝ) ^ 2 / (20 * log y) =
        (y : ℝ) ^ 2 / (80 * log y) := by
      field_simp; ring
    have : 10 ≤ (y : ℝ) ^ 2 / (80 * log y) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · unfold delta
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- All the "sufficiently large `y`" conditions hold simultaneously for large `y`. -/
theorem eventually_large {τ : ℚ} (h0 : 0 < τ) :
    ∃ y0 : ℕ, ∀ y ≥ y0, Large τ y := by
  obtain ⟨yW, hyW⟩ := card_W_eventually
  obtain ⟨yM, hyM⟩ := cor_mertens
  set C : ℝ := 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r with hC
  have hτR : (0 : ℝ) < τ := by exact_mod_cast h0
  set Q : ℝ := 64 * C * (log (8 * τ.den) + log 16) / τ with hQ
  refine ⟨max (max yW yM) (max (2 * 10 ^ 11) (max (τ.den + 1)
    (⌈C / τ⌉₊ + ⌈2 * C⌉₊ + ⌈Q⌉₊ + 1))), fun y hy => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hy
  obtain ⟨⟨hyW', hyM'⟩, hbig, hden, hy1'⟩ := hy
  have hyR : (2 * 10 ^ 11 : ℝ) ≤ y := by exact_mod_cast hbig
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hsum : (⌈C / τ⌉₊ : ℝ) + ⌈2 * C⌉₊ + ⌈Q⌉₊ + 1 ≤ y := by exact_mod_cast hy1'
  have c1 := Nat.le_ceil (C / τ)
  have c2 := Nat.le_ceil (2 * C)
  have c3 := Nat.le_ceil Q
  have n1 : (0 : ℝ) ≤ ⌈C / τ⌉₊ := Nat.cast_nonneg _
  have n2 : (0 : ℝ) ≤ ⌈2 * C⌉₊ := Nat.cast_nonneg _
  have n3 : (0 : ℝ) ≤ ⌈Q⌉₊ := Nat.cast_nonneg _
  have hyC : C / τ ≤ y := by linarith
  have hy2C : 2 * C < y := by linarith
  have hyQ : Q ≤ (y : ℝ) ^ 2 := le_trans (by linarith) (le_self_pow₀ hy1 (by norm_num))
  have hHV := HV_bounds_uniform τ (y := y) (by omega)
  have hHVpos : 0 < HV τ y := by linarith [hHV.1]
  have hW := hyW y hyW'
  have heps := y30_eps_le hbig hW
  have hcp := count_phase_numeric (y := y) (by omega)
  refine
    { y_ge := by omega
      B_lt := ?_
      card_W := hW
      mertens := hyM y hyM'
      tune := ?_
      major := ?_
      count := hcp.1
      phase := hcp.2
      colIII := colIII_numeric (by omega) heps
      caseIII := caseIII_numeric h0 hHVpos hHV.2 hy1 hyQ
      caseII := caseII_numeric (by omega) heps }
  · intro r hr
    have hr' := Nat.le_of_dvd τ.den_pos (Nat.dvd_of_mem_primeFactors hr)
    omega
  · -- `H_V/(2y^8) < τ/2`: `H_V ≤ C ≤ τ y < τ y^8`
    have hy8 : (y : ℝ) < (y : ℝ) ^ 8 := by
      have : (y : ℝ) ^ 1 < (y : ℝ) ^ 8 := pow_lt_pow_right₀ (by linarith) (by norm_num)
      simpa using this
    have hCy : C ≤ τ * y := by rwa [div_le_iff₀ hτR, mul_comm] at hyC
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hHV.2]
  · -- `2 H_V < y`
    linarith [hHV.2]

end

/-! ### Li (2026): Proposition 4.2 and Theorem 3.1 -/
/-
Assembly of §§4–9: Proposition 4.2 and Theorem 3.1 (small targets).
-/

section

open Real Finset

attribute [local instance] Classical.propDecidable

variable {τ : ℚ} {y Y : ℕ}

/-- **Proposition 4.2.**  There is `S ⊆ A` with `σ(S) ≡ τ (mod 1)`.
(Split formula (2) into the three cases: case I contributes `≥ 1/L` (Prop. 7.1), cases II and III at
most `1/(2L)` in absolute value (Prop. 9.1); so `N > 0`.) -/
theorem prop_core (hsq : Squarefree τ.den) (hL : Large τ y) (hT : Tuned τ y Y) :
    ∃ S ⊆ Aset τ y Y, ∃ k : ℤ, sigma S - τ = k := by
  set L := Lnum τ y Y with hLdef
  set A := Aset τ y Y with hAdef
  set K : ℤ := (y : ℤ) ^ 7 with hK
  have hLpos : 0 < L := by
    have h1 := L_gt (Y := Y) hL
    have h2 : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    have : (0 : ℤ) < (L : ℤ) := by rw [hLdef]; linarith
    exact_mod_cast this
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hA : ∀ p ∈ A, 0 < p.1 * p.2 ∧ p.1 * p.2 ∣ L := by
    intro p hp
    refine ⟨?_, edge_dvd_L hL hp⟩
    have h1 := (prime_of_mem_Vset (mem_Aset.1 hp).1).pos
    have h2 := (prime_of_mem_Uset (mem_Aset.1 hp).2).pos
    positivity
  have hN := eq_N A τ L hLpos hA (den_dvd_L hsq)
  -- split the frequencies into major arcs `|h| ≤ y^7` and the rest
  set f : ℤ → ℂ := fun h => ee (-((h : ℝ) * τ)) * phi A h with hf
  have hsplit := Finset.sum_filter_add_sum_filter_not (freq L) (fun h => |h| ≤ K) f
  have hmaj : (freq L).filter (fun h => |h| ≤ K) = Finset.Icc (-K) K := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨-, hh⟩; exact abs_le.1 hh
    · intro hh
      exact ⟨mem_freq_of_small hL (abs_le.2 hh), abs_le.2 hh⟩
  rw [hmaj] at hsplit
  -- bound on the minor arcs
  have hminor : ‖∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h‖ ≤ 1 / 2 := by
    calc ‖∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h‖
        ≤ ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), ‖f h‖ := norm_sum_le _ _
      _ = ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), ‖phi A h‖ := by
          refine Finset.sum_congr rfl (fun h _ => ?_)
          simp [hf, norm_ee]
      _ ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h), ‖phi A h‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro h hh
            simp only [Finset.mem_filter] at hh ⊢
            refine ⟨hh.1, ?_⟩
            rcases (three_cases (Y := Y) hL h).1 with h1 | h1
            · exact absurd ((caseI_iff hL hh.1).1 h1) hh.2
            · exact h1
          · intros; exact norm_nonneg _
      _ ≤ 1 / 2 := prop_minor hL hT
  have hmajor := prop_major hL hT
  -- real parts
  have hre : ((Ncount A τ : ℂ) / 2 ^ A.card).re ≥ 1 / (2 * L) := by
    rw [hN, ← hsplit, mul_add]
    have e1 : (1 / (L : ℂ)) * ∑ h ∈ Finset.Icc (-K) K, f h = SigmaMaj τ y Y := rfl
    rw [Complex.add_re, e1]
    have e2 : ((1 / (L : ℂ)) * ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h).re
        ≥ -(1 / (2 * L)) := by
      set R := ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h
      have : (1 / (L : ℂ)) * R = ((1 / (L : ℝ) : ℝ) : ℂ) * R := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
      have hRre : -‖R‖ ≤ R.re := by
        have := Complex.abs_re_le_norm R
        linarith [neg_abs_le R.re]
      have hpos : (0 : ℝ) ≤ 1 / L := by positivity
      have : -(1 / (2 * (L : ℝ))) = 1 / L * (-(1 / 2)) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hpos
    have e3 := hmajor.2
    have : 1 / (L : ℝ) - 1 / (2 * L) = 1 / (2 * L) := by field_simp; ring
    linarith
  have hNpos : 0 < Ncount A τ := by
    by_contra hcon
    push Not at hcon
    have : Ncount A τ = 0 := by omega
    rw [this] at hre
    simp at hre
    have : (0 : ℝ) < (L : ℝ)⁻¹ * 2⁻¹ := by positivity
    linarith
  unfold Ncount at hNpos
  obtain ⟨S, hS⟩ := Finset.card_pos.1 hNpos
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  exact ⟨S, hS.1, hS.2⟩

/-- The statement of Theorem 3.1 (small targets). -/
def SmallTargets : Prop :=
  ∀ τ : ℚ, 0 < τ → τ ≤ 1 / 400 → Squarefree τ.den →
    ∃ y0 : ℕ, ∀ y ≥ y0, ∃ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧ p.1 ≤ 2 * y ^ 2 ∧ y ^ 8 < p.2 ∧ p.2 ≤ y ^ 9) ∧
      ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2) = τ

/-- **Theorem 3.1 (Small targets).**  Let `τ = a/b ∈ (0, η]`, `η = 1/400`, with `b` squarefree.
Then for every sufficiently large `y`, `τ` is a finite sum of distinct `1/(vu)` with
`v ≤ 2y² < y^8 < u ≤ y^9` primes. -/
theorem thm_small : SmallTargets := by
  intro τ h0 hη hsq
  obtain ⟨y0, hy0⟩ := eventually_large h0
  refine ⟨y0, fun y hy => ?_⟩
  have hL := hy0 y hy
  obtain ⟨Y, hT⟩ := lem_tuning h0 hη hL
  obtain ⟨S, hSA, k, hk⟩ := prop_core hsq hL hT
  refine ⟨S, fun p hp => ?_, sigma_eq_of_congr h0 hη hT hSA k hk⟩
  have hpA := mem_Aset.1 (hSA hp)
  have hv := le_of_mem_Vset hL hpA.1
  have hu := bounds_of_mem_Uset hpA.2
  exact ⟨prime_of_mem_Vset hpA.1, prime_of_mem_Uset hpA.2, hv.2, hu.1, hu.2.trans hT.hi⟩

end

/-! ### Li (2026): §3, reduction by prime dilution -/
/-
§3 of the paper: reduction of Theorem 1.1 to small targets (Theorem 3.1) by prime dilution.
-/

section

open Finset

/-- `n` is a product of two distinct primes. -/
def IsSemiprime2 (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q

/-- The statement of Theorem 1.1. -/
def MainStatement : Prop :=
  ∀ q : ℚ, 0 < q → Squarefree q.den →
    ∃ F : Finset ℕ, (∀ n ∈ F, IsSemiprime2 n) ∧ ∑ n ∈ F, (1 : ℚ) / n = q

/-- **Proof of Theorem 1.1 from Theorem 3.1** (§3).  Split `a/b` into `q` equal parts
`x = a/(bq) ≤ η` for a large prime `q ∤ ab`, represent `x` with `q` different values of `y`
whose ranges `(y^8, y^9]` are disjoint, and take the union. -/
theorem thm_main_of_small
    (hsmall : ∀ τ : ℚ, 0 < τ → τ ≤ 1 / 400 → Squarefree τ.den →
      ∃ y0 : ℕ, ∀ y ≥ y0, ∃ S : Finset (ℕ × ℕ),
        (∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧ p.1 ≤ 2 * y ^ 2 ∧ y ^ 8 < p.2 ∧ p.2 ≤ y ^ 9) ∧
        ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2) = τ) :
    MainStatement := by
  intro q hq hsq
  -- Step 1: choose a large prime `p ∤ ab` with `x = q/p ≤ η`.
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (400 * q.num.natAbs + q.den + 1)
  have hnum : 0 < q.num := Rat.num_pos.2 hq
  have hq_le : q ≤ (q.num.natAbs : ℚ) := by
    have h1 : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hnum)]
    rw [h1]
    conv_lhs => rw [← Rat.num_div_den q]
    apply div_le_self (by exact_mod_cast hnum.le)
    exact_mod_cast q.den_pos
  have hbp : Nat.Coprime q.den p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have := Nat.le_of_dvd q.den_pos hdvd
    omega
  set x : ℚ := q * (p : ℚ)⁻¹ with hx
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hx0 : 0 < x := by positivity
  have hxη : x ≤ 1 / 400 := by
    rw [hx, ← div_eq_mul_inv, div_le_iff₀ hp0]
    have : (400 * q.num.natAbs : ℚ) ≤ p := by exact_mod_cast (by omega)
    linarith
  have hxsq : Squarefree x.den := by
    have h1 : x.den ∣ q.den * p := by
      have := Rat.mul_den_dvd q ((p : ℚ)⁻¹)
      rwa [Rat.inv_natCast_den, ite_eq_right hp.ne_zero] at this
    exact Squarefree.squarefree_of_dvd h1
      ((Nat.squarefree_mul hbp).2 ⟨hsq, hp.prime.squarefree⟩)
  obtain ⟨y0, hy0⟩ := hsmall x hx0 hxη hxsq
  -- Step 2: `k` disjoint representations of `x`, one for each of `k` increasing values of `y`.
  have key : ∀ k : ℕ, ∃ F : Finset ℕ, (∀ n ∈ F, IsSemiprime2 n) ∧
      ∑ n ∈ F, (1 : ℚ) / n = k * x := by
    intro k
    induction k with
    | zero => exact ⟨∅, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨F, hF, hFsum⟩ := ih
      -- choose `y` so large that the new semiprimes exceed every element of `F`
      set y := max y0 (max (F.sup id + 1) 2) with hy
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
      set G := S.image (fun r : ℕ × ℕ => r.1 * r.2) with hG
      have hinj : Set.InjOn (fun r : ℕ × ℕ => r.1 * r.2) S := by
        rintro ⟨v, u⟩ hr ⟨v', u'⟩ hr' heq
        simp only at heq
        obtain ⟨hv, hu, hv2, hu8, -⟩ := hS _ hr
        obtain ⟨hv', hu', hv2', hu8', -⟩ := hS _ hr'
        simp only at hv hu hv2 hu8 hv' hu' hv2' hu8'
        have hdvd : u ∣ v' * u' := ⟨v, by rw [← heq]; ring⟩
        rcases (Nat.Prime.dvd_mul hu).1 hdvd with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hu hv').1 h
          omega
        · have huu := (Nat.prime_dvd_prime_iff_eq hu hu').1 h
          subst huu
          have : v = v' := Nat.eq_of_mul_eq_mul_right hu.pos heq
          rw [this]
      have hdisj : Disjoint F G := by
        rw [Finset.disjoint_left]
        intro n hnF hnG
        obtain ⟨⟨v, u⟩, hr, rfl⟩ := Finset.mem_image.1 hnG
        obtain ⟨hv, hu, -, hu8, -⟩ := hS _ hr
        have h1 : v * u ≤ F.sup id := Finset.le_sup (f := id) hnF
        have h2 : u ≤ v * u := Nat.le_mul_of_pos_left u hv.pos
        simp only at hu8
        omega
      refine ⟨F ∪ G, ?_, ?_⟩
      · intro n hn
        rcases Finset.mem_union.1 hn with h | h
        · exact hF n h
        · obtain ⟨⟨v, u⟩, hr, rfl⟩ := Finset.mem_image.1 h
          obtain ⟨hv, hu, hv2, hu8, -⟩ := hS _ hr
          exact ⟨v, u, hv, hu, by simp only at hv2 hu8 ⊢; omega, rfl⟩
      · rw [Finset.sum_union hdisj, hFsum, hG, Finset.sum_image hinj]
        push_cast
        rw [hSsum]
        ring
  obtain ⟨F, hF, hFsum⟩ := key p
  refine ⟨F, hF, ?_⟩
  rw [hFsum, hx]
  field_simp

end

/-! ### Li (2026): Theorem 1.1 -/
/-
Main theorem (Theorem 1.1 of the paper): Erdős Problem #306.
-/

section

/-- **Theorem 1.1 (Erdős Problem #306).**  Every positive rational number whose reduced
denominator is squarefree is a finite sum of reciprocals of pairwise distinct natural numbers,
each a product of two distinct primes. -/
theorem erdos_306_semiprime_finset (q : ℚ) (hq : 0 < q) (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q := by
  obtain ⟨F, hF, hsum⟩ := thm_main_of_small thm_small q hq hsq
  refine ⟨F, fun n hn => ?_, hsum⟩
  obtain ⟨p, r, hp, hr, hpr, rfl⟩ := hF n hn
  exact ⟨p, r, hp, hr, hpr.ne, rfl⟩

end


/-! ### Li (2026): the Formal Conjectures statement -/
/-
The statement of Erdős Problem #306 as formalised in Google DeepMind's `formal-conjectures`
repository (`FormalConjectures/ErdosProblems/306.lean`, theorem `Erdos306.erdos_306`), derived
from `Erdos306.erdos_306_semiprime_finset`.  The current upstream statement is the
plain proposition `P`; the theorem below proves that exact proposition.
-/

section

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

/-- **Erdős Problem #306**, in the exact form of `formal-conjectures`: every positive rational
with squarefree denominator is `1/n_1 + ⋯ + 1/n_k` with `1 < n_1 < ⋯ < n_k`, each `n_i` a
product of two distinct primes (`ω(n_i) = Ω(n_i) = 2`). -/
theorem erdos_306_fc_core : ∀ (q : ℚ), 0 < q → Squarefree q.den →
    ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
    (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
    q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) := by
  intro q hq hsq
  obtain ⟨F, hF, hsum⟩ := erdos_306_semiprime_finset q hq hsq
  -- `F` is nonempty since `q > 0`
  obtain ⟨m, hm⟩ : ∃ m, F.card = m + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h => ?_
    rw [Finset.card_eq_zero.1 h, Finset.sum_empty] at hsum
    exact hq.ne' hsum.symm
  set e := F.orderEmbOfFin hm with he
  have heF : ∀ j, e j ∈ F := fun j => F.orderEmbOfFin_mem hm j
  have he2 : ∀ j, 1 < e j := by
    intro j
    obtain ⟨p, r, hp, hr, -, hpr⟩ := hF _ (heF j)
    rw [hpr]; exact one_lt_mul_of_lt_of_le hp.one_lt hr.one_lt.le
  -- the index set `{1, …, k}` is the image of `Fin.succ`
  have hIcc : Finset.Icc (1 : Fin (m + 2)) (Fin.last (m + 1)) =
      Finset.univ.map (Fin.succEmb (m + 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_univ, true_and, Fin.coe_succEmb,
      Fin.exists_succ_eq, Fin.le_last, and_true]
    rw [Fin.le_iff_val_le_val, Fin.val_one, Ne, Fin.ext_iff, Fin.val_zero]
    omega
  refine ⟨m + 1, Fin.cons 1 (fun j => e j), rfl, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    induction i using Fin.cases with
    | zero => simp [he2 0]
    | succ j =>
      rw [← Fin.succ_castSucc]
      simp only [Fin.cons_succ]
      exact e.strictMono j.castSucc_lt_succ
  · rw [hIcc]
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨p, r, hp, hr, hpr, h⟩ := hF _ (heF j)
    simp only [Fin.coe_succEmb, Fin.cons_succ, h]
    refine ⟨?_, ?_⟩
    · rw [cardDistinctFactors_mul ((Nat.coprime_primes hp hr).2 hpr),
        cardDistinctFactors_apply_prime hp, cardDistinctFactors_apply_prime hr]
    · rw [cardFactors_mul hp.ne_zero hr.ne_zero, cardFactors_apply_prime hp,
        cardFactors_apply_prime hr]
  · have hmapF : Finset.univ.map e.toEmbedding = F := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and]
      exact Set.ext_iff.1 (F.range_orderEmbOfFin hm) x
    rw [hIcc, Finset.sum_map, ← hsum, ← hmapF, Finset.sum_map]
    simp

end

/-! ### Additional corollaries and the conditional arXiv v1 pathway -/

section

open Real Finset

/-- The statement of Ramanujan's inequality (1919), as formulated in the arXiv v1 ancillary Lean files
of `arXiv:2609.32140v1`: for every real `x > 300`, `θ(x) - θ(x/2) > x/6 - 3√x`.
In the unconditional proof above, `lem_cheb` is proved directly via `centralBinom_le_primesIn`
without this hypothesis. -/
def RamanujanInequality : Prop :=
  ∀ x : ℝ, 300 < x → x / 6 - 3 * Real.sqrt x < Chebyshev.theta x - Chebyshev.theta (x / 2)

/-- Conditional derivation of Lemma 2.1 (`lem_cheb`) from `RamanujanInequality`,
preserved from the arXiv:2609.32140v1 ancillary Lean files. -/
theorem lem_cheb_of_ramanujan (hR : RamanujanInequality) : ∃ x0 : ℝ, ∀ x ≥ x0,
    x / (7 * Real.log x) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) := by
  refine ⟨126 ^ 2, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans (by positivity) hx
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hθ : Chebyshev.theta x - Chebyshev.theta (x / 2) =
      ∑ p ∈ primesIn ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p := by
    have hmono : ⌊x / 2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
    unfold Chebyshev.theta primesIn
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmono]
    ring
  have hle : ∑ p ∈ primesIn ⌊x / 2⌋₊ ⌊x⌋₊, Real.log p ≤
      ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ) * Real.log x := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    obtain ⟨-, hp2, hpp⟩ := mem_primesIn.1 hp
    apply Real.log_le_log (by exact_mod_cast hpp.pos)
    exact le_trans (by exact_mod_cast hp2) (Nat.floor_le hx0)
  have hram := hR x (by nlinarith)
  have hsq : (126 : ℝ) ≤ Real.sqrt x := by
    rw [show (126 : ℝ) = Real.sqrt (126 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hss := Real.mul_self_sqrt hx0
  have h7 : x / 7 ≤ x / 6 - 3 * Real.sqrt x := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The conditional Theorem 1.1 (`erdos_306_of_ramanujan`) from the ancillary Lean files
of `arXiv:2609.32140v1`. -/
theorem erdos_306_of_ramanujan_core (_hR : RamanujanInequality) (q : ℚ) (hq : 0 < q)
    (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q :=
  erdos_306_semiprime_finset q hq hsq

/-- Finset form of `erdos_306_fc_core` using `ArithmeticFunction.cardDistinctFactors` (`ω`)
and `ArithmeticFunction.cardFactors` (`Ω`). -/
theorem erdos_306_finset_omega_Omega (q : ℚ) (hq : 0 < q) (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ,
      (∀ n ∈ F, ArithmeticFunction.cardDistinctFactors n = 2 ∧
        ArithmeticFunction.cardFactors n = 2) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q := by
  obtain ⟨F, hF, hsum⟩ := erdos_306_semiprime_finset q hq hsq
  refine ⟨F, fun n hn => ?_, hsum⟩
  obtain ⟨p, r, hp, hr, hpr, rfl⟩ := hF n hn
  refine ⟨?_, ?_⟩
  · rw [ArithmeticFunction.cardDistinctFactors_mul ((Nat.coprime_primes hp hr).2 hpr),
      ArithmeticFunction.cardDistinctFactors_apply_prime hp,
      ArithmeticFunction.cardDistinctFactors_apply_prime hr]
  · rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hr.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hp,
      ArithmeticFunction.cardFactors_apply_prime hr]

/-- Special case `q = 1` of Theorem 1.1: the number `1` is representable as a finite sum
of reciprocals of distinct squarefree semiprimes. -/
theorem exists_semiprime_unit_fraction_sum_eq_one :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = 1 :=
  erdos_306_semiprime_finset 1 one_pos (by simp)

end

end Erdos306


/-!
## Prime-Local Residue Admissibility and Opposite-Signed Row-Potential Duality for Erdős #306

This part formalizes the two structural pillars underlying the finite prime-support
row-potential exclusions and squarefree-denominator reductions for Erdős Problem #306:

1. **Universal Prime-Local Denominator Elimination:**
   For any finite set of denominators split at a prime `p` into `p`-multiples `{p * q | q ∈ N}`
   (with `p.Coprime q`) and `p`-coprime denominators `R`, if the rational reciprocal sum
   `∑_{q ∈ N} 1/(p*q) + ∑_{m ∈ R} 1/m = a / b` has `p.Coprime b`, then clearing denominators
   forces `p ∣ ∑_{q ∈ N} ∏_{r ∈ N.erase q} r` (`PrimeRowAdmissible p N`), which in `ZMod p`
   is equivalent to `∑_{q ∈ N} (q : ZMod p)⁻¹ = 0`. In particular, `N.card ≠ 1` (no degree-1
   prime can be eliminated from the reduced denominator), and for any odd prime `p` and
   distinct odd integers `q₁, q₂ < p`, `{q₁, q₂}` is never `p`-admissible.

2. **Opposite-Signed Edge-Potential / Row-Potential Duality:**
   For any finite oriented prime graph `E` (`∀ e ∈ E, e.1 < e.2`) on vertex set `V` and any
   opposite-signed rational edge potential `φ : ℕ → ℕ → ℚ` satisfying `φ p q + φ q p = 0`,
   the total reciprocal sum decomposes exactly across vertex neighborhoods `graphNeighbors E p`:
   `∑_{e ∈ E} 1/(e.1 * e.2) = ∑_{p ∈ V} ∑_{q ∈ graphNeighbors E p} (1/(2*p*q) + φ p q)`.
   Consequently, prime-wise row maxima `R p` over `p`-admissible neighborhoods of size `≤ d`
   bound the total reciprocal sum by `∑_{p ∈ V} R p`.

3. **Explicit Positive and Negative Controls:**
   - Explicit distinct squarefree semiprime representations of unit fractions `1/6`, `1/3`,
     and `1/2`, together with verification of prime-row admissibility at every eliminated prime.
   - Explicit through-61 boundary controls (`p ∈ {53, 59, 61}`).
-/

namespace Erdos306.Core.PrimeResidueAndRowPotential

/-! ### Part 1: Cleared-Denominator Row Sum and `ZMod p` Inverse Characterization -/

/-- The cleared-denominator numerator sum `∑_{q ∈ N} ∏_{r ∈ N \ {q}} r` for a neighbor set `N`. -/
def clearedRowSum (N : Finset ℕ) : ℕ :=
  ∑ q ∈ N, ∏ r ∈ N.erase q, r

/-- A neighbor set `N` is `p`-admissible if `p` divides `clearedRowSum N`. -/
def PrimeRowAdmissible (p : ℕ) (N : Finset ℕ) : Prop :=
  p ∣ clearedRowSum N

instance instDecidablePrimeRowAdmissible (p : ℕ) (N : Finset ℕ) :
    Decidable (PrimeRowAdmissible p N) :=
  inferInstanceAs (Decidable (p ∣ clearedRowSum N))

/-- The modular reciprocal sum `∑_{q ∈ N} (q : ZMod p)⁻¹` in `ZMod p`. -/
noncomputable def zmodInverseRowSum (p : ℕ) (N : Finset ℕ) : ZMod p :=
  ∑ q ∈ N, (q : ZMod p)⁻¹

theorem clearedRowSum_empty : clearedRowSum ∅ = 0 := rfl

theorem primeRowAdmissible_empty (p : ℕ) : PrimeRowAdmissible p ∅ := by
  simp [PrimeRowAdmissible, clearedRowSum]

theorem clearedRowSum_singleton (q : ℕ) : clearedRowSum {q} = 1 := by
  simp [clearedRowSum]

theorem not_primeRowAdmissible_singleton {p : ℕ} (hp : p.Prime) (q : ℕ) :
    ¬ PrimeRowAdmissible p {q} := by
  rw [PrimeRowAdmissible, clearedRowSum_singleton]
  exact hp.not_dvd_one

theorem card_ne_one_of_primeRowAdmissible {p : ℕ} (hp : p.Prime) {N : Finset ℕ}
    (hadm : PrimeRowAdmissible p N) : N.card ≠ 1 := by
  intro hcard
  obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hcard
  exact not_primeRowAdmissible_singleton hp q hadm

theorem clearedRowSum_pair {q₁ q₂ : ℕ} (hne : q₁ ≠ q₂) :
    clearedRowSum {q₁, q₂} = q₂ + q₁ := by
  have h1 : ({q₁, q₂} : Finset ℕ).erase q₁ = {q₂} := by
    ext x
    simp [Finset.mem_erase, hne.symm]
    omega
  have h2 : ({q₁, q₂} : Finset ℕ).erase q₂ = {q₁} := by
    ext x
    simp [Finset.mem_erase, hne]
    omega
  simp [clearedRowSum, Finset.sum_pair hne, h1, h2]

theorem primeRowAdmissible_pair_iff (p : ℕ) {q₁ q₂ : ℕ} (hne : q₁ ≠ q₂) :
    PrimeRowAdmissible p {q₁, q₂} ↔ p ∣ q₁ + q₂ := by
  rw [PrimeRowAdmissible, clearedRowSum_pair hne, add_comm]

/-- Universal odd-prime degree-2 obstruction: for any odd prime `p` and distinct odd positive
integers `q₁, q₂ < p`, the degree-2 neighborhood `{q₁, q₂}` is never `p`-admissible because
`q₁ + q₂` is even and strictly between `0` and `2 * p`. -/
theorem not_primeRowAdmissible_pair_of_odd_lt {p q₁ q₂ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hne : q₁ ≠ q₂)
    (hq₁_odd : q₁ % 2 = 1) (hq₂_odd : q₂ % 2 = 1)
    (hq₁_lt : q₁ < p) (hq₂_lt : q₂ < p) :
    ¬ PrimeRowAdmissible p {q₁, q₂} := by
  rw [primeRowAdmissible_pair_iff p hne]
  rintro ⟨k, hk⟩
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hsum_pos : 0 < q₁ + q₂ := by omega
  have hsum_lt : q₁ + q₂ < 2 * p := by omega
  have hk_eq : k = 1 := by nlinarith
  subst hk_eq
  omega

/-- Clearing denominators on a finite reciprocal sum `∑_{q ∈ N} 1/q` yields `clearedRowSum N`. -/
theorem rat_sum_inv_mul_prod_eq_clearedRowSum (N : Finset ℕ) (hN : ∀ q ∈ N, q ≠ 0) :
    (∑ q ∈ N, (1 : ℚ) / (q : ℚ)) * (∏ r ∈ N, (r : ℚ)) = (clearedRowSum N : ℚ) := by
  rw [Finset.sum_mul, clearedRowSum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod : (∏ r ∈ N, (r : ℚ)) = (q : ℚ) * (∏ r ∈ N.erase q, (r : ℚ)) := by
    rw [← Finset.mul_prod_erase N (fun r : ℕ => (r : ℚ)) hq]
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hN q hq)
  rw [hprod, Nat.cast_prod]
  field_simp [hq0]

/-- In `ZMod p` for prime `p`, `clearedRowSum N` factors as `(∏_{r ∈ N} r) * ∑_{q ∈ N} q⁻¹`
whenever `p` divides no element of `N`. -/
theorem clearedRowSum_cast_zmod_eq_prod_mul_zmodInverseRowSum (p : ℕ) [Fact p.Prime]
    (N : Finset ℕ) (hN : ∀ q ∈ N, ¬ p ∣ q) :
    (clearedRowSum N : ZMod p) = (∏ r ∈ N, (r : ZMod p)) * zmodInverseRowSum p N := by
  rw [clearedRowSum, zmodInverseRowSum, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hN q hq
  have hprod : (∏ r ∈ N, (r : ZMod p)) = (q : ZMod p) * (∏ r ∈ N.erase q, (r : ZMod p)) := by
    rw [← Finset.mul_prod_erase N (fun r : ℕ => (r : ZMod p)) hq]
  rw [Nat.cast_prod, hprod, mul_right_comm, mul_inv_cancel₀ hq0, one_mul]

/-- Equivalence between the integer divisibility condition `PrimeRowAdmissible p N` and
vanishing of the modular inverse sum `zmodInverseRowSum p N = 0` in `ZMod p`. -/
theorem primeRowAdmissible_iff_zmodInverseRowSum_eq_zero (p : ℕ) [Fact p.Prime]
    (N : Finset ℕ) (hN : ∀ q ∈ N, ¬ p ∣ q) :
    PrimeRowAdmissible p N ↔ zmodInverseRowSum p N = 0 := by
  rw [PrimeRowAdmissible, ← ZMod.natCast_eq_zero_iff,
    clearedRowSum_cast_zmod_eq_prod_mul_zmodInverseRowSum p N hN]
  have hprod_ne : (∏ r ∈ N, (r : ZMod p)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro r hr
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hN r hr
  exact mul_eq_zero_iff_left hprod_ne

/-- Universal prime-local denominator elimination theorem:
if a rational sum `∑_{q ∈ N} 1/(p*q) + ∑_{m ∈ R} 1/m = a / b` has `p` coprime to every
`q ∈ N`, every `m ∈ R`, and the target denominator `b` (`b ≠ 0`), then `N` must be
`p`-admissible (`p ∣ clearedRowSum N`) and in particular `N.card ≠ 1`. -/
theorem primeRowAdmissible_of_split_reciprocal_sum
    (p b : ℕ) (a : ℤ) (N R : Finset ℕ)
    (hp : p.Prime) (hb0 : b ≠ 0)
    (hpb : p.Coprime b)
    (hN : ∀ q ∈ N, p.Coprime q)
    (hR : ∀ m ∈ R, p.Coprime m)
    (hsum : (∑ q ∈ N, (1 : ℚ) / ((p : ℚ) * (q : ℚ))) + (∑ m ∈ R, (1 : ℚ) / (m : ℚ)) =
      (a : ℚ) / (b : ℚ)) :
    PrimeRowAdmissible p N ∧ N.card ≠ 1 := by
  have hN0 : ∀ q ∈ N, q ≠ 0 := by
    intro q hq hq0
    subst hq0
    have := (Nat.coprime_zero_right p).mp (hN 0 hq)
    exact hp.ne_one this
  have hR0 : ∀ m ∈ R, m ≠ 0 := by
    intro m hm hm0
    subst hm0
    have := (Nat.coprime_zero_right p).mp (hR 0 hm)
    exact hp.ne_one this
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb0
  have hN_factor :
      (∑ q ∈ N, (1 : ℚ) / ((p : ℚ) * (q : ℚ))) =
        ((1 : ℚ) / (p : ℚ)) * (∑ q ∈ N, (1 : ℚ) / (q : ℚ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hclearN := rat_sum_inv_mul_prod_eq_clearedRowSum N hN0
  have hclearR := rat_sum_inv_mul_prod_eq_clearedRowSum R hR0
  set PN : ℕ := ∏ r ∈ N, r
  set PR : ℕ := ∏ m ∈ R, m
  have hPN_cast : (∏ r ∈ N, (r : ℚ)) = (PN : ℚ) := (Nat.cast_prod _ _).symm
  have hPR_cast : (∏ m ∈ R, (m : ℚ)) = (PR : ℚ) := (Nat.cast_prod _ _).symm
  rw [hPN_cast] at hclearN
  rw [hPR_cast] at hclearR
  have hidentQ :
      ((b : ℚ) * (PR : ℚ) * (clearedRowSum N : ℚ)) +
        (p : ℚ) * ((b : ℚ) * (PN : ℚ) * (clearedRowSum R : ℚ)) =
      (p : ℚ) * ((a : ℚ) * (PN : ℚ) * (PR : ℚ)) := by
    calc
      ((b : ℚ) * (PR : ℚ) * (clearedRowSum N : ℚ)) +
          (p : ℚ) * ((b : ℚ) * (PN : ℚ) * (clearedRowSum R : ℚ))
        = (b : ℚ) * (PR : ℚ) * ((∑ q ∈ N, (1 : ℚ) / (q : ℚ)) * (PN : ℚ)) +
          (p : ℚ) * ((b : ℚ) * (PN : ℚ) * ((∑ m ∈ R, (1 : ℚ) / (m : ℚ)) * (PR : ℚ))) := by
          rw [hclearN, hclearR]
      _ = (p : ℚ) * (b : ℚ) * (PN : ℚ) * (PR : ℚ) *
          (((1 : ℚ) / (p : ℚ)) * (∑ q ∈ N, (1 : ℚ) / (q : ℚ)) +
            (∑ m ∈ R, (1 : ℚ) / (m : ℚ))) := by
          field_simp [hpQ]
      _ = (p : ℚ) * (b : ℚ) * (PN : ℚ) * (PR : ℚ) * ((a : ℚ) / (b : ℚ)) := by
          rw [← hN_factor, hsum]
      _ = (p : ℚ) * ((a : ℚ) * (PN : ℚ) * (PR : ℚ)) := by
          field_simp [hbQ]
  have hidentZ :
      ((b : ℤ) * (PR : ℤ) * (clearedRowSum N : ℤ)) +
        (p : ℤ) * ((b : ℤ) * (PN : ℤ) * (clearedRowSum R : ℤ)) =
      (p : ℤ) * (a * (PN : ℤ) * (PR : ℤ)) := by
    exact_mod_cast hidentQ
  have hdvdZ : (p : ℤ) ∣ ((b : ℕ) * PR * clearedRowSum N : ℕ) := by
    refine ⟨a * (PN : ℤ) * (PR : ℤ) - (b : ℤ) * (PN : ℤ) * (clearedRowSum R : ℤ), ?_⟩
    push_cast
    linarith
  have hdvdN : p ∣ b * PR * clearedRowSum N := Int.ofNat_dvd.mp hdvdZ
  have hpPR : p.Coprime PR := Nat.Coprime.prod_right hR
  have hp_bPR : p.Coprime (b * PR) := hpb.mul_right hpPR
  have hadm : PrimeRowAdmissible p N := hp_bPR.dvd_of_dvd_mul_left hdvdN
  exact ⟨hadm, card_ne_one_of_primeRowAdmissible hp hadm⟩


/-! ### Part 2: Opposite-Signed Edge-Potential / Row-Potential Duality -/

/-- Incidence degree of vertex `v` in an oriented edge set `E`. -/
def incidenceDegree {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (v : α) : ℕ :=
  (E.filter fun e => e.1 = v).card + (E.filter fun e => e.2 = v).card

/-- Neighbors `q` of `p` appearing as right endpoints `(p, q) ∈ E`. -/
def rightNeighbors (E : Finset (ℕ × ℕ)) (p : ℕ) : Finset ℕ :=
  (E.filter fun e => e.1 = p).image Prod.snd

/-- Neighbors `q` of `p` appearing as left endpoints `(q, p) ∈ E`. -/
def leftNeighbors (E : Finset (ℕ × ℕ)) (p : ℕ) : Finset ℕ :=
  (E.filter fun e => e.2 = p).image Prod.fst

/-- Complete undirected neighbor set `N_E(p)` of vertex `p` in an oriented graph `E`. -/
def graphNeighbors (E : Finset (ℕ × ℕ)) (p : ℕ) : Finset ℕ :=
  rightNeighbors E p ∪ leftNeighbors E p

/-- The rational row-potential objective at prime `p` for a neighbor subset `S`
under signed edge potential `φ : ℕ → ℕ → ℚ`. -/
def rowPotential (φ : ℕ → ℕ → ℚ) (p : ℕ) (S : Finset ℕ) : ℚ :=
  ∑ q ∈ S, ((1 : ℚ) / (2 * (p : ℚ) * (q : ℚ)) + φ p q)

theorem disjoint_rightNeighbors_leftNeighbors (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2) (p : ℕ) :
    Disjoint (rightNeighbors E p) (leftNeighbors E p) := by
  rw [Finset.disjoint_left]
  intro q hright hleft
  rcases Finset.mem_image.mp hright with ⟨e₁, he₁, rfl⟩
  rcases Finset.mem_image.mp hleft with ⟨e₂, he₂, hfst⟩
  have h1 := hE e₁ (Finset.mem_filter.mp he₁).1
  have h1p : e₁.1 = p := (Finset.mem_filter.mp he₁).2
  have h2 := hE e₂ (Finset.mem_filter.mp he₂).1
  have h2p : e₂.2 = p := (Finset.mem_filter.mp he₂).2
  omega

theorem injOn_snd_filter_fst (E : Finset (ℕ × ℕ)) (p : ℕ) :
    Set.InjOn (Prod.snd : ℕ × ℕ → ℕ) ((E.filter fun e => e.1 = p) : Set (ℕ × ℕ)) := by
  intro e₁ he₁ e₂ he₂ hsnd
  have h1 : e₁.1 = p := (Finset.mem_filter.mp he₁).2
  have h2 : e₂.1 = p := (Finset.mem_filter.mp he₂).2
  exact Prod.ext (h1.trans h2.symm) hsnd

theorem injOn_fst_filter_snd (E : Finset (ℕ × ℕ)) (p : ℕ) :
    Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) ((E.filter fun e => e.2 = p) : Set (ℕ × ℕ)) := by
  intro e₁ he₁ e₂ he₂ hfst
  have h1 : e₁.2 = p := (Finset.mem_filter.mp he₁).2
  have h2 : e₂.2 = p := (Finset.mem_filter.mp he₂).2
  exact Prod.ext hfst (h1.trans h2.symm)

theorem card_graphNeighbors_eq_incidenceDegree (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2) (p : ℕ) :
    (graphNeighbors E p).card = incidenceDegree E p := by
  rw [graphNeighbors, Finset.card_union_of_disjoint (disjoint_rightNeighbors_leftNeighbors E hE p),
    rightNeighbors, leftNeighbors,
    Finset.card_image_of_injOn (injOn_snd_filter_fst E p),
    Finset.card_image_of_injOn (injOn_fst_filter_snd E p),
    incidenceDegree]

theorem rowPotential_graphNeighbors_eq_fiber_sums (φ : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E, e.1 < e.2) (p : ℕ) :
    rowPotential φ p (graphNeighbors E p) =
      (∑ e ∈ E.filter (fun e => e.1 = p), ((1 : ℚ) / (2 * (e.1 : ℚ) * (e.2 : ℚ)) + φ e.1 e.2)) +
      (∑ e ∈ E.filter (fun e => e.2 = p), ((1 : ℚ) / (2 * (e.2 : ℚ) * (e.1 : ℚ)) + φ e.2 e.1)) := by
  rw [rowPotential, graphNeighbors,
    Finset.sum_union (disjoint_rightNeighbors_leftNeighbors E hE p),
    rightNeighbors, leftNeighbors,
    Finset.sum_image (injOn_snd_filter_fst E p),
    Finset.sum_image (injOn_fst_filter_snd E p)]
  congr 1
  · apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  · apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]

theorem sum_graphNeighbors_inv_eq_filter_incident (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2) (p : ℕ) :
    (∑ q ∈ graphNeighbors E p, (1 : ℚ) / ((p : ℚ) * (q : ℚ))) =
      ∑ e ∈ E.filter (fun e => e.1 = p ∨ e.2 = p), (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
  have hdis : Disjoint (E.filter fun e => e.1 = p) (E.filter fun e => e.2 = p) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    have hlt := hE e (Finset.mem_filter.mp he1).1
    have h1 := (Finset.mem_filter.mp he1).2
    have h2 := (Finset.mem_filter.mp he2).2
    omega
  rw [graphNeighbors,
    Finset.sum_union (disjoint_rightNeighbors_leftNeighbors E hE p),
    rightNeighbors, leftNeighbors,
    Finset.sum_image (injOn_snd_filter_fst E p),
    Finset.sum_image (injOn_fst_filter_snd E p),
    Finset.filter_or, Finset.sum_union hdis]
  congr 1
  · apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  · apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2, mul_comm]

/-- End-to-end prime-graph local divisibility theorem:
for any oriented prime graph `E` (`∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2`), if
`∑_{e ∈ E} 1/(e.1 * e.2) = a / b` with `b ≠ 0` and `p.Coprime b` for a prime `p`, then
`graphNeighbors E p` is `p`-admissible (`p ∣ clearedRowSum (graphNeighbors E p)`) and
`incidenceDegree E p ≠ 1`. -/
theorem prime_graph_row_admissible_of_sum_eq_div
    (E : Finset (ℕ × ℕ)) (p b : ℕ) (a : ℤ)
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hp : p.Prime) (hb0 : b ≠ 0) (hpb : p.Coprime b)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = (a : ℚ) / (b : ℚ)) :
    PrimeRowAdmissible p (graphNeighbors E p) ∧ incidenceDegree E p ≠ 1 := by
  have hlt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  let E_rest := E.filter (fun e => ¬ (e.1 = p ∨ e.2 = p))
  let R := E_rest.image (fun e => e.1 * e.2)
  have hinj : Set.InjOn (fun e : ℕ × ℕ => e.1 * e.2) (E_rest : Set (ℕ × ℕ)) := by
    intro e₁ he₁ e₂ he₂ hprod
    change e₁.1 * e₁.2 = e₂.1 * e₂.2 at hprod
    have he₁E := (Finset.mem_filter.mp he₁).1
    have he₂E := (Finset.mem_filter.mp he₂).1
    have hp1 := (hE e₁ he₁E).1
    have hq1 := (hE e₁ he₁E).2.1
    have ho1 := (hE e₁ he₁E).2.2
    have hp2 := (hE e₂ he₂E).1
    have hq2 := (hE e₂ he₂E).2.1
    have ho2 := (hE e₂ he₂E).2.2
    have hpd : e₁.1 ∣ e₂.1 * e₂.2 := hprod ▸ dvd_mul_right e₁.1 e₁.2
    rcases hp1.dvd_mul.mp hpd with h11 | h12
    · have hfst : e₁.1 = e₂.1 := (Nat.prime_dvd_prime_iff_eq hp1 hp2).mp h11
      rw [hfst] at hprod
      have hsnd : e₁.2 = e₂.2 := Nat.eq_of_mul_eq_mul_left hp2.pos hprod
      exact Prod.ext hfst hsnd
    · have hfst : e₁.1 = e₂.2 := (Nat.prime_dvd_prime_iff_eq hp1 hq2).mp h12
      rw [hfst] at hprod
      have hsnd : e₁.2 = e₂.1 :=
        Nat.eq_of_mul_eq_mul_left hq2.pos (hprod.trans (Nat.mul_comm e₂.1 e₂.2))
      omega
  have hR_sum : (∑ m ∈ R, (1 : ℚ) / (m : ℚ)) =
      ∑ e ∈ E_rest, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro e _
    push_cast
    rfl
  have hsplit :
      (∑ q ∈ graphNeighbors E p, (1 : ℚ) / ((p : ℚ) * (q : ℚ))) +
        (∑ m ∈ R, (1 : ℚ) / (m : ℚ)) = (a : ℚ) / (b : ℚ) := by
    rw [sum_graphNeighbors_inv_eq_filter_incident E hlt p, hR_sum]
    have htot := Finset.sum_filter_add_sum_filter_not E (fun e => e.1 = p ∨ e.2 = p)
      (f := fun e : ℕ × ℕ => (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)))
    exact htot.trans hsum
  have hN_cop : ∀ q ∈ graphNeighbors E p, p.Coprime q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hright | hleft
    · rcases Finset.mem_image.mp hright with ⟨e, he, rfl⟩
      have heE := (Finset.mem_filter.mp he).1
      have hep := (Finset.mem_filter.mp he).2
      have hqe := (hE e heE).2.1
      have hoe := (hE e heE).2.2
      exact (Nat.coprime_primes hp hqe).mpr (by omega)
    · rcases Finset.mem_image.mp hleft with ⟨e, he, rfl⟩
      have heE := (Finset.mem_filter.mp he).1
      have hep := (Finset.mem_filter.mp he).2
      have hpe := (hE e heE).1
      have hoe := (hE e heE).2.2
      exact (Nat.coprime_primes hp hpe).mpr (by omega)
  have hR_cop : ∀ m ∈ R, p.Coprime m := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨e, he, rfl⟩
    have heE := (Finset.mem_filter.mp he).1
    have hnot := (Finset.mem_filter.mp he).2
    have hc1 : p.Coprime e.1 := (Nat.coprime_primes hp (hE e heE).1).mpr (by tauto)
    have hc2 : p.Coprime e.2 := (Nat.coprime_primes hp (hE e heE).2.1).mpr (by tauto)
    exact hc1.mul_right hc2
  rcases primeRowAdmissible_of_split_reciprocal_sum p b a (graphNeighbors E p) R
    hp hb0 hpb hN_cop hR_cop hsplit with ⟨hadm, hcard⟩
  rw [card_graphNeighbors_eq_incidenceDegree E hlt p] at hcard
  exact ⟨hadm, hcard⟩

/-- Exact row-potential decomposition identity: for any opposite-signed edge potential
`φ` (`φ e.1 e.2 + φ e.2 e.1 = 0`), the sum of `rowPotential φ p (graphNeighbors E p)` over
all vertices `p ∈ V` equals the exact rational reciprocal sum `∑_{e ∈ E} 1/(e.1 * e.2)`. -/
theorem reciprocal_sum_eq_sum_rowPotential (φ : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hskew : ∀ e ∈ E, φ e.1 e.2 + φ e.2 e.1 = 0) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) =
      ∑ p ∈ V, rowPotential φ p (graphNeighbors E p) := by
  have hrew :
      (∑ p ∈ V, rowPotential φ p (graphNeighbors E p)) =
        (∑ p ∈ V, ∑ e ∈ E.filter (fun e => e.1 = p),
          ((1 : ℚ) / (2 * (e.1 : ℚ) * (e.2 : ℚ)) + φ e.1 e.2)) +
        (∑ p ∈ V, ∑ e ∈ E.filter (fun e => e.2 = p),
          ((1 : ℚ) / (2 * (e.2 : ℚ) * (e.1 : ℚ)) + φ e.2 e.1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    exact rowPotential_graphNeighbors_eq_fiber_sums φ E hE p
  have hfst := Finset.sum_fiberwise_of_maps_to
    (s := E) (t := V) (g := Prod.fst) (fun e he => (hend e he).1)
    (fun e : ℕ × ℕ => (1 : ℚ) / (2 * (e.1 : ℚ) * (e.2 : ℚ)) + φ e.1 e.2)
  have hsnd := Finset.sum_fiberwise_of_maps_to
    (s := E) (t := V) (g := Prod.snd) (fun e he => (hend e he).2)
    (fun e : ℕ × ℕ => (1 : ℚ) / (2 * (e.2 : ℚ) * (e.1 : ℚ)) + φ e.2 e.1)
  rw [hrew, hfst, hsnd, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hanti := hskew e he
  calc
    (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))
      = ((1 : ℚ) / (2 * (e.1 : ℚ) * (e.2 : ℚ)) + (1 : ℚ) / (2 * (e.2 : ℚ) * (e.1 : ℚ))) +
        (φ e.1 e.2 + φ e.2 e.1) := by
        rw [hanti]
        ring
    _ = ((1 : ℚ) / (2 * (e.1 : ℚ) * (e.2 : ℚ)) + φ e.1 e.2) +
        ((1 : ℚ) / (2 * (e.2 : ℚ) * (e.1 : ℚ)) + φ e.2 e.1) := by
        ring

/-- Row-potential dual upper bound: if every vertex `p ∈ V` has `graphNeighbors E p`
`p`-admissible of degree `≤ d`, and `R p` upper-bounds `rowPotential φ p S` over all
`p`-admissible subsets `S ⊆ V.erase p` of cardinality `≤ d`, then
`∑_{e ∈ E} 1/(e.1 * e.2) ≤ ∑_{p ∈ V} R p`. -/
theorem reciprocal_sum_le_sum_row_maxima (φ : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ) (R : ℕ → ℚ) (d : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hskew : ∀ e ∈ E, φ e.1 e.2 + φ e.2 e.1 = 0)
    (hdeg : ∀ p ∈ V, incidenceDegree E p ≤ d)
    (hadm : ∀ p ∈ V, PrimeRowAdmissible p (graphNeighbors E p))
    (hmax : ∀ p ∈ V, ∀ S : Finset ℕ,
      S ⊆ V.erase p → S.card ≤ d → PrimeRowAdmissible p S → rowPotential φ p S ≤ R p) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) ≤ ∑ p ∈ V, R p := by
  rw [reciprocal_sum_eq_sum_rowPotential φ E V hE hend hskew]
  apply Finset.sum_le_sum
  intro p hp
  apply hmax p hp (graphNeighbors E p)
  · intro q hq
    rcases Finset.mem_union.mp hq with hright | hleft
    · rcases Finset.mem_image.mp hright with ⟨e, he, rfl⟩
      have heE := (Finset.mem_filter.mp he).1
      have hep := (Finset.mem_filter.mp he).2
      have hlt := hE e heE
      exact Finset.mem_erase.mpr ⟨by omega, (hend e heE).2⟩
    · rcases Finset.mem_image.mp hleft with ⟨e, he, rfl⟩
      have heE := (Finset.mem_filter.mp he).1
      have hep := (Finset.mem_filter.mp he).2
      have hlt := hE e heE
      exact Finset.mem_erase.mpr ⟨by omega, (hend e heE).1⟩
  · rw [card_graphNeighbors_eq_incidenceDegree E hE p]
    exact hdeg p hp
  · exact hadm p hp

/-- Row-potential exclusion criterion for representations of `1`: if `∑_{p ∈ V} R p < 1`,
no `p`-admissible graph of maximum degree `≤ d` on `V` can have reciprocal sum `1`. -/
theorem ne_one_of_sum_row_maxima_lt_one (φ : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ) (R : ℕ → ℚ) (d : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hskew : ∀ e ∈ E, φ e.1 e.2 + φ e.2 e.1 = 0)
    (hdeg : ∀ p ∈ V, incidenceDegree E p ≤ d)
    (hadm : ∀ p ∈ V, PrimeRowAdmissible p (graphNeighbors E p))
    (hmax : ∀ p ∈ V, ∀ S : Finset ℕ,
      S ⊆ V.erase p → S.card ≤ d → PrimeRowAdmissible p S → rowPotential φ p S ≤ R p)
    (hlt : (∑ p ∈ V, R p) < 1) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) ≠ 1 := by
  have hle := reciprocal_sum_le_sum_row_maxima φ E V R d hE hend hskew hdeg hadm hmax
  linarith


/-! ### Part 3: Explicit Positive and Negative Controls -/

/-- Positive control 1: `1/6 = 1/10 + 1/15` using distinct squarefree semiprimes `{10, 15}`,
eliminating the prime `5` via the `5`-admissible neighborhood `{2, 3}` (`2 + 3 = 5`). -/
def witnessOneSixth : Finset ℕ := {10, 15}

theorem witnessOneSixth_sum_and_admissibility :
    (∑ n ∈ witnessOneSixth, (1 : ℚ) / (n : ℚ)) = 1 / 6 ∧
    PrimeRowAdmissible 5 {2, 3} ∧
    ¬ PrimeRowAdmissible 2 {5} ∧
    ¬ PrimeRowAdmissible 3 {5} := by
  refine ⟨?_, by decide, by decide, by decide⟩
  norm_num [witnessOneSixth]

/-- Positive control 2: `1/3 = 1/6 + 1/10 + 1/15` using distinct squarefree semiprimes
`{6, 10, 15}`, eliminating primes `2` (`3 + 5 = 8`) and `5` (`2 + 3 = 5`) while keeping `3`
(`2 + 5 = 7` is not divisible by `3`). -/
def witnessOneThird : Finset ℕ := {6, 10, 15}

theorem witnessOneThird_sum_and_admissibility :
    (∑ n ∈ witnessOneThird, (1 : ℚ) / (n : ℚ)) = 1 / 3 ∧
    PrimeRowAdmissible 2 {3, 5} ∧
    PrimeRowAdmissible 5 {2, 3} ∧
    ¬ PrimeRowAdmissible 3 {2, 5} := by
  refine ⟨?_, by decide, by decide, by decide⟩
  norm_num [witnessOneThird]

/-- Positive control 3: `1/2` represented as the reciprocal sum of 9 distinct squarefree
semiprimes `{6, 10, 15, 21, 26, 35, 39, 65, 91}` supported on `{2, 3, 5, 7, 13}`, where
every odd prime `p ∈ {3, 5, 7, 13}` satisfies `PrimeRowAdmissible p (N(p))` and only `p = 2`
remains in the reduced denominator. -/
def witnessOneHalf : Finset ℕ := {6, 10, 15, 21, 26, 35, 39, 65, 91}

theorem witnessOneHalf_sum_and_admissibility :
    (∑ n ∈ witnessOneHalf, (1 : ℚ) / (n : ℚ)) = 1 / 2 ∧
    PrimeRowAdmissible 3 {2, 5, 7, 13} ∧
    PrimeRowAdmissible 5 {2, 3, 7, 13} ∧
    PrimeRowAdmissible 7 {3, 5, 13} ∧
    PrimeRowAdmissible 13 {2, 3, 5, 7} ∧
    ¬ PrimeRowAdmissible 2 {3, 5, 13} := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide⟩
  norm_num [witnessOneHalf]

/-- Through-61 prime universe `P_61`. -/
def primes61 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}

/-- Through-61 boundary controls:
- `p = 53` has the degree-2 admissible neighborhood `{47, 59}` (`47 + 59 = 106 = 2 * 53`);
- `p = 61` has the degree-2 admissible neighborhood `{2, 59}` (`2 + 59 = 61`);
- `p = 59` has NO degree-2 admissible neighborhood `{q₁, q₂}` anywhere in `primes61 \ {59}`. -/
theorem primes61_boundary_degree_two_controls :
    PrimeRowAdmissible 53 {47, 59} ∧
    PrimeRowAdmissible 61 {2, 59} ∧
    (∀ q₁ ∈ primes61.erase 59, ∀ q₂ ∈ primes61.erase 59,
      q₁ < q₂ → ¬ PrimeRowAdmissible 59 {q₁, q₂}) := by
  decide

/-!
## Tail-Activity Cell Pruning, Branch-Cover Row-Potential Duality, and `P_61` Degree Obstructions for Erdős #306

This part extends the prime-row admissibility and row-potential results above with universal
structural theorems supporting the 8-cell (`{0,1}^3` on `{53, 59, 61}`) tail-activity decomposition
and exact rational branch-and-bound row-potential certificates on `P_61`:

1. **Universal Neighbor Symmetry & Inactive-Vertex Domain Pruning:**
   - Characterization of `rightNeighbors`, `leftNeighbors`, and `graphNeighbors` via edge membership;
   - Universal symmetry `q ∈ graphNeighbors E p ↔ p ∈ graphNeighbors E q` and irreflexivity
     `p ∉ graphNeighbors E p` for oriented simple graphs (`∀ e ∈ E, e.1 < e.2`);
   - Inactive-vertex pruning (`graphNeighbors E p = ∅ → p ∉ graphNeighbors E q`) and the cell-domain
     reduction `graphNeighbors E p ⊆ (V \ I).erase p` for any set `I` of inactive vertices.

2. **Activity-Cell & Finite Branch-Cover Row-Potential Exclusion Duality:**
   - Inactive vertices satisfy `rowPotential φ p ∅ = 0` and drop out of the global row-potential sum:
     `∑_{e ∈ E} 1/(e.1 * e.2) = ∑_{p ∈ V \ I} rowPotential φ p (graphNeighbors E p)`;
   - Universal activity-cell bound `reciprocal_sum_le_sum_activity_cell_row_maxima` and exclusion
     criterion `ne_one_of_activity_cell_row_maxima_lt_one`, simultaneously enforcing inactive-vertex
     domain pruning `S ⊆ (V \ I).erase p` and active-vertex non-emptiness `p ∈ A → S ≠ ∅`;
   - Universal finite branch-cover exclusion theorem `ne_one_of_branch_cover_row_maxima_lt_one`.

3. **Universal Minimum Tail-Degree (`≥ 3`) and Coupled Degree (`≥ 5`) Obstructions on `P_61 \ P_47`:**
   - Universal non-empty prime-row lower bound `2 ≤ S.card` and no-pair lower bound `3 ≤ S.card`;
   - Exact characterization of degree-2 admissible rows for `53` (`{47, 59}` only) and `61`
     (`{2, 59}` only) across `primes61`, and absence of degree-2 rows for `53` and `61` in
     `primes61 \ {59}`;
   - Proof that in every `p`-admissible simple graph on `primes61` activating at least one tail
     prime in `{53, 59, 61}`, some tail prime `p ∈ {53, 59, 61}` satisfies
     `3 ≤ (graphNeighbors E p).card`, and if `53` or `61` has degree `2`, then `59` is also active
     with `3 ≤ (graphNeighbors E 59).card`, forcing combined tail degree `≥ 5`.

4. **Explicit Positive and Negative Controls:**
   - Concrete degree-3 admissible neighborhoods inside `primes47` for `53` (`{2, 13, 23}`),
     `59` (`{2, 5, 7}`), and `61` (`{2, 3, 11}`);
   - Exact rational comparison of the zero-potential and root LP-dual bounds across
     the 8 tail-activity cells `(a_53, a_59, a_61) ∈ {0, 1}^3`.
-/
/-! ### Part 1: Universal Neighbor Symmetry and Inactive-Vertex Domain Pruning -/

theorem mem_rightNeighbors_iff (E : Finset (ℕ × ℕ)) (p q : ℕ) :
    q ∈ rightNeighbors E p ↔ (p, q) ∈ E := by
  rw [rightNeighbors, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, he, rfl⟩
    have he1 := (Finset.mem_filter.mp he).1
    have he2 : a = p := (Finset.mem_filter.mp he).2
    subst he2
    exact he1
  · intro h
    exact ⟨(p, q), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

theorem mem_leftNeighbors_iff (E : Finset (ℕ × ℕ)) (p q : ℕ) :
    q ∈ leftNeighbors E p ↔ (q, p) ∈ E := by
  rw [leftNeighbors, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, he, rfl⟩
    have he1 := (Finset.mem_filter.mp he).1
    have he2 : b = p := (Finset.mem_filter.mp he).2
    subst he2
    exact he1
  · intro h
    exact ⟨(q, p), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

theorem mem_graphNeighbors_iff (E : Finset (ℕ × ℕ)) (p q : ℕ) :
    q ∈ graphNeighbors E p ↔ (p, q) ∈ E ∨ (q, p) ∈ E := by
  rw [graphNeighbors, Finset.mem_union, mem_rightNeighbors_iff, mem_leftNeighbors_iff]

theorem mem_graphNeighbors_comm (E : Finset (ℕ × ℕ)) (p q : ℕ) :
    q ∈ graphNeighbors E p ↔ p ∈ graphNeighbors E q := by
  rw [mem_graphNeighbors_iff, mem_graphNeighbors_iff, or_comm]

theorem not_mem_rightNeighbors_self (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2) (p : ℕ) :
    p ∉ rightNeighbors E p := by
  rw [mem_rightNeighbors_iff]
  intro h
  have hlt := hE (p, p) h
  omega

theorem not_mem_leftNeighbors_self (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2) (p : ℕ) :
    p ∉ leftNeighbors E p := by
  rw [mem_leftNeighbors_iff]
  intro h
  have hlt := hE (p, p) h
  omega

theorem not_mem_graphNeighbors_self (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2) (p : ℕ) :
    p ∉ graphNeighbors E p := by
  rw [mem_graphNeighbors_iff]
  rintro (h | h) <;> { have hlt := hE (p, p) h; omega }

/-- Universal inactive-vertex pruning: if `p` has empty neighborhood in `E`, then `p` cannot belong
to the neighborhood of any vertex `q`. -/
theorem not_mem_graphNeighbors_of_eq_empty (E : Finset (ℕ × ℕ)) {p q : ℕ}
    (h : graphNeighbors E p = ∅) :
    p ∉ graphNeighbors E q := by
  rw [mem_graphNeighbors_comm, h]
  exact Finset.notMem_empty q

theorem graphNeighbors_subset_vertexSet_erase (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) (p : ℕ) :
    graphNeighbors E p ⊆ V.erase p := by
  intro q hq
  rw [Finset.mem_erase]
  refine ⟨?_, ?_⟩
  · intro hqp
    subst hqp
    exact not_mem_graphNeighbors_self E hE q hq
  · rcases (mem_graphNeighbors_iff E p q).mp hq with h | h
    · exact (hend (p, q) h).2
    · exact (hend (q, p) h).1

/-- Universal activity-cell domain reduction: if every vertex `r ∈ I` is inactive
(`graphNeighbors E r = ∅`), then every vertex `p` has its neighborhood contained in
`(V \ I).erase p`. -/
theorem graphNeighbors_subset_sdiff_inactive (E : Finset (ℕ × ℕ)) (V I : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hinact : ∀ r ∈ I, graphNeighbors E r = ∅) (p : ℕ) :
    graphNeighbors E p ⊆ (V \ I).erase p := by
  intro q hq
  have hsub := graphNeighbors_subset_vertexSet_erase E V hE hend p hq
  rw [Finset.mem_erase] at hsub ⊢
  rw [Finset.mem_sdiff]
  refine ⟨hsub.1, hsub.2, ?_⟩
  intro hqI
  exact not_mem_graphNeighbors_of_eq_empty E (hinact q hqI) hq

theorem rowPotential_empty (φ : ℕ → ℕ → ℚ) (p : ℕ) :
    rowPotential φ p ∅ = 0 := by
  simp [rowPotential]


/-! ### Part 2: Activity-Cell and Branch-Cover Row-Potential Duality -/

/-- Inactive vertices contribute `0` to the global row-potential sum under any skew-symmetric
edge potential `φ`. -/
theorem reciprocal_sum_eq_sum_sdiff_inactive_rowPotential (φ : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V I : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hskew : ∀ e ∈ E, φ e.1 e.2 + φ e.2 e.1 = 0)
    (hinact : ∀ r ∈ I, graphNeighbors E r = ∅) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) =
      ∑ p ∈ V \ I, rowPotential φ p (graphNeighbors E p) := by
  rw [reciprocal_sum_eq_sum_rowPotential φ E V hE hend hskew]
  symm
  apply Finset.sum_subset Finset.sdiff_subset
  intro p hpV hpNotSdiff
  have hpI : p ∈ I := by
    by_contra hpNotI
    exact hpNotSdiff (Finset.mem_sdiff.mpr ⟨hpV, hpNotI⟩)
  rw [hinact p hpI, rowPotential_empty]

/-- Soundness of the activity-cell row-potential relaxation:
for an active subset `A ⊆ V` (`∀ p ∈ A, graphNeighbors E p ≠ ∅`) and an inactive subset `I ⊆ V`
(`∀ r ∈ I, graphNeighbors E r = ∅`), the reciprocal sum is bounded by `∑_{p ∈ V \ I} R p` whenever
`R p` bounds `rowPotential φ p S` over all `p`-admissible subsets `S ⊆ (V \ I).erase p` of size
`≤ d` satisfying `p ∈ A → S ≠ ∅`. -/
theorem reciprocal_sum_le_sum_activity_cell_row_maxima (φ : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V A I : Finset ℕ) (R : ℕ → ℚ) (d : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hskew : ∀ e ∈ E, φ e.1 e.2 + φ e.2 e.1 = 0)
    (hdeg : ∀ p ∈ V \ I, incidenceDegree E p ≤ d)
    (hadm : ∀ p ∈ V \ I, PrimeRowAdmissible p (graphNeighbors E p))
    (hact : ∀ p ∈ A, graphNeighbors E p ≠ ∅)
    (hinact : ∀ r ∈ I, graphNeighbors E r = ∅)
    (hmax : ∀ p ∈ V \ I, ∀ S : Finset ℕ,
      S ⊆ (V \ I).erase p → S.card ≤ d → (p ∈ A → S ≠ ∅) →
      PrimeRowAdmissible p S → rowPotential φ p S ≤ R p) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) ≤ ∑ p ∈ V \ I, R p := by
  rw [reciprocal_sum_eq_sum_sdiff_inactive_rowPotential φ E V I hE hend hskew hinact]
  apply Finset.sum_le_sum
  intro p hp
  apply hmax p hp (graphNeighbors E p)
  · exact graphNeighbors_subset_sdiff_inactive E V I hE hend hinact p
  · rw [card_graphNeighbors_eq_incidenceDegree E hE p]
    exact hdeg p hp
  · exact fun hpA => hact p hpA
  · exact hadm p hp

/-- Exclusion criterion for an activity cell `(A, I)` when `∑_{p ∈ V \ I} R p < 1`. -/
theorem ne_one_of_activity_cell_row_maxima_lt_one (φ : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V A I : Finset ℕ) (R : ℕ → ℚ) (d : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hskew : ∀ e ∈ E, φ e.1 e.2 + φ e.2 e.1 = 0)
    (hdeg : ∀ p ∈ V \ I, incidenceDegree E p ≤ d)
    (hadm : ∀ p ∈ V \ I, PrimeRowAdmissible p (graphNeighbors E p))
    (hact : ∀ p ∈ A, graphNeighbors E p ≠ ∅)
    (hinact : ∀ r ∈ I, graphNeighbors E r = ∅)
    (hmax : ∀ p ∈ V \ I, ∀ S : Finset ℕ,
      S ⊆ (V \ I).erase p → S.card ≤ d → (p ∈ A → S ≠ ∅) →
      PrimeRowAdmissible p S → rowPotential φ p S ≤ R p)
    (hlt : (∑ p ∈ V \ I, R p) < 1) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) ≠ 1 := by
  have hle :=
    reciprocal_sum_le_sum_activity_cell_row_maxima φ E V A I R d hE hend hskew hdeg hadm hact hinact hmax
  linarith

/-- Universal finite branch-cover exclusion theorem:
if a graph `E` on `V` falls into at least one branch `b ∈ B` of a finite cover, and each branch `b`
has a skew-symmetric potential `φ b` and row-maximum bound `R b` with `∑_{p ∈ V} R b p < 1`, then
`∑_{e ∈ E} 1/(e.1 * e.2) ≠ 1`. -/
theorem ne_one_of_branch_cover_row_maxima_lt_one {ι : Type*}
    (B : Finset ι) (BranchPred : ι → Finset (ℕ × ℕ) → Prop)
    (φ : ι → ℕ → ℕ → ℚ) (R : ι → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hcover : ∃ b ∈ B, BranchPred b E)
    (hskew : ∀ b ∈ B, ∀ e ∈ E, φ b e.1 e.2 + φ b e.2 e.1 = 0)
    (hbranch : ∀ b ∈ B, BranchPred b E →
      ∀ p ∈ V, rowPotential (φ b) p (graphNeighbors E p) ≤ R b p)
    (hlt : ∀ b ∈ B, (∑ p ∈ V, R b p) < 1) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) ≠ 1 := by
  rcases hcover with ⟨b, hbB, hbE⟩
  have hsum_eq := reciprocal_sum_eq_sum_rowPotential (φ b) E V hE hend (hskew b hbB)
  have hsum_le :
      ∑ p ∈ V, rowPotential (φ b) p (graphNeighbors E p) ≤ ∑ p ∈ V, R b p :=
    Finset.sum_le_sum (hbranch b hbB hbE)
  have hlt_b := hlt b hbB
  linarith


/-! ### Part 3: Universal `P_61 \ P_47` Minimum Tail-Degree (`≥ 3`) and Coupled Degree (`≥ 5`) Obstructions -/

/-- Any non-empty `p`-admissible neighborhood `S` of a prime `p` has cardinality at least `2`. -/
theorem card_ge_two_of_primeRowAdmissible_nonempty {p : ℕ} {S : Finset ℕ}
    (hp : p.Prime) (hadm : PrimeRowAdmissible p S) (hne : S ≠ ∅) :
    2 ≤ S.card := by
  have h0 : S.card ≠ 0 := by
    intro h0
    exact hne (Finset.card_eq_zero.mp h0)
  have h1 : S.card ≠ 1 := card_ne_one_of_primeRowAdmissible hp hadm
  omega

/-- Universal degree-3 lower bound: if a candidate neighbor pool `U` contains no `p`-admissible pair
`{q₁, q₂}` (`q₁ < q₂`), then every non-empty `p`-admissible subset `S ⊆ U` satisfies `3 ≤ S.card`. -/
theorem card_ge_three_of_primeRowAdmissible_of_no_pair {p : ℕ} {U S : Finset ℕ}
    (hp : p.Prime) (hSU : S ⊆ U) (hadm : PrimeRowAdmissible p S) (hne : S ≠ ∅)
    (hnopair : ∀ q₁ ∈ U, ∀ q₂ ∈ U, q₁ < q₂ → ¬ PrimeRowAdmissible p {q₁, q₂}) :
    3 ≤ S.card := by
  have h2 : 2 ≤ S.card := card_ge_two_of_primeRowAdmissible_nonempty hp hadm hne
  by_contra hlt
  have hcard2 : S.card = 2 := by omega
  rcases Finset.card_eq_two.mp hcard2 with ⟨a, b, hab, rfl⟩
  have haU : a ∈ U := hSU (Finset.mem_insert_self a {b})
  have hbU : b ∈ U := hSU (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  rcases lt_or_gt_of_ne hab with hlt_ab | hlt_ba
  · exact hnopair a haU b hbU hlt_ab hadm
  · rw [Finset.pair_comm] at hadm
    exact hnopair b hbU a haU hlt_ba hadm

/-- Through-47 and intermediate prime universes `P_47 ⊂ P_53 ⊂ P_59 ⊂ P_61`. -/
def primes47 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47}

def primes53 : Finset ℕ := primes47 ∪ {53}

def primes59 : Finset ℕ := primes53 ∪ {59}

/-- Complete classification of degree-2 admissible pairs for `53`, `59`, and `61` across `primes61`:
- For `p = 53`, `{47, 59}` is the unique degree-2 admissible pair in `primes61 \ {53}`;
- For `p = 61`, `{2, 59}` is the unique degree-2 admissible pair in `primes61 \ {61}`;
- In `(primes61 \ {59}).erase 53` and `(primes61 \ {59}).erase 61`, neither `53` nor `61` has any
  degree-2 admissible pair. -/
theorem primes61_unique_degree_two_53_and_61 :
    (∀ q₁ ∈ primes61.erase 53, ∀ q₂ ∈ primes61.erase 53,
      q₁ < q₂ → (PrimeRowAdmissible 53 {q₁, q₂} ↔ q₁ = 47 ∧ q₂ = 59)) ∧
    (∀ q₁ ∈ primes61.erase 61, ∀ q₂ ∈ primes61.erase 61,
      q₁ < q₂ → (PrimeRowAdmissible 61 {q₁, q₂} ↔ q₁ = 2 ∧ q₂ = 59)) ∧
    (∀ q₁ ∈ (primes61 \ {59}).erase 53, ∀ q₂ ∈ (primes61 \ {59}).erase 53,
      q₁ < q₂ → ¬ PrimeRowAdmissible 53 {q₁, q₂}) ∧
    (∀ q₁ ∈ (primes61 \ {59}).erase 61, ∀ q₂ ∈ (primes61 \ {59}).erase 61,
      q₁ < q₂ → ¬ PrimeRowAdmissible 61 {q₁, q₂}) := by
  decide

/-- In any `p`-admissible simple graph `E` on `primes61`, if `59` is active (`graphNeighbors E 59 ≠ ∅`),
then `3 ≤ (graphNeighbors E 59).card`. -/
theorem card_graphNeighbors_59_ge_three_of_nonempty (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ primes61 ∧ e.2 ∈ primes61)
    (hadm59 : PrimeRowAdmissible 59 (graphNeighbors E 59))
    (hne59 : graphNeighbors E 59 ≠ ∅) :
    3 ≤ (graphNeighbors E 59).card := by
  have hp59 : Nat.Prime 59 := by decide
  exact card_ge_three_of_primeRowAdmissible_of_no_pair hp59
    (graphNeighbors_subset_vertexSet_erase E primes61 hE hend 59)
    hadm59 hne59 primes61_boundary_degree_two_controls.2.2

/-- In any `p`-admissible simple graph `E` on `primes61`, if `59` is inactive
(`graphNeighbors E 59 = ∅`) and `53` is active (`graphNeighbors E 53 ≠ ∅`), then
`3 ≤ (graphNeighbors E 53).card`. -/
theorem card_graphNeighbors_53_ge_three_of_59_empty (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ primes61 ∧ e.2 ∈ primes61)
    (h59 : graphNeighbors E 59 = ∅)
    (hadm53 : PrimeRowAdmissible 53 (graphNeighbors E 53))
    (hne53 : graphNeighbors E 53 ≠ ∅) :
    3 ≤ (graphNeighbors E 53).card := by
  have hp53 : Nat.Prime 53 := by decide
  have hinact : ∀ r ∈ ({59} : Finset ℕ), graphNeighbors E r = ∅ := by
    intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact h59
  exact card_ge_three_of_primeRowAdmissible_of_no_pair hp53
    (graphNeighbors_subset_sdiff_inactive E primes61 {59} hE hend hinact 53)
    hadm53 hne53 primes61_unique_degree_two_53_and_61.2.2.1

/-- In any `p`-admissible simple graph `E` on `primes61`, if `59` is inactive
(`graphNeighbors E 59 = ∅`) and `61` is active (`graphNeighbors E 61 ≠ ∅`), then
`3 ≤ (graphNeighbors E 61).card`. -/
theorem card_graphNeighbors_61_ge_three_of_59_empty (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ primes61 ∧ e.2 ∈ primes61)
    (h59 : graphNeighbors E 59 = ∅)
    (hadm61 : PrimeRowAdmissible 61 (graphNeighbors E 61))
    (hne61 : graphNeighbors E 61 ≠ ∅) :
    3 ≤ (graphNeighbors E 61).card := by
  have hp61 : Nat.Prime 61 := by decide
  have hinact : ∀ r ∈ ({59} : Finset ℕ), graphNeighbors E r = ∅ := by
    intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact h59
  exact card_ge_three_of_primeRowAdmissible_of_no_pair hp61
    (graphNeighbors_subset_sdiff_inactive E primes61 {59} hE hend hinact 61)
    hadm61 hne61 primes61_unique_degree_two_53_and_61.2.2.2

/-- Universal `P_61 \ P_47` minimum tail-degree theorem:
for every `p`-admissible simple graph `E` on `primes61`, if at least one tail prime in
`{53, 59, 61}` is active, then there exists `p ∈ ({53, 59, 61} : Finset ℕ)` with
`3 ≤ (graphNeighbors E p).card`. -/
theorem exists_tail_prime_card_ge_three_of_active_tail (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ primes61 ∧ e.2 ∈ primes61)
    (hadm : ∀ p ∈ primes61, PrimeRowAdmissible p (graphNeighbors E p))
    (hactive : graphNeighbors E 53 ≠ ∅ ∨ graphNeighbors E 59 ≠ ∅ ∨ graphNeighbors E 61 ≠ ∅) :
    ∃ p ∈ ({53, 59, 61} : Finset ℕ), 3 ≤ (graphNeighbors E p).card := by
  by_cases h59 : graphNeighbors E 59 = ∅
  · rcases hactive with h53 | h59_ne | h61
    · refine ⟨53, by decide, card_graphNeighbors_53_ge_three_of_59_empty E hE hend h59 ?_ h53⟩
      exact hadm 53 (by decide)
    · exact False.elim (h59_ne h59)
    · refine ⟨61, by decide, card_graphNeighbors_61_ge_three_of_59_empty E hE hend h59 ?_ h61⟩
      exact hadm 61 (by decide)
  · refine ⟨59, by decide, card_graphNeighbors_59_ge_three_of_nonempty E hE hend ?_ h59⟩
    exact hadm 59 (by decide)

/-- Coupled tail-degree theorem: if `53` or `61` has degree `2` in a `p`-admissible simple graph
`E` on `primes61`, then `59` cannot be inactive (`graphNeighbors E 59 ≠ ∅`), so `59` has degree at
least `3` and the combined tail degree `(graphNeighbors E 53).card + (graphNeighbors E 59).card +
(graphNeighbors E 61).card` is at least `5`. -/
theorem sum_tail_degrees_ge_five_of_degree_two_53_or_61 (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ primes61 ∧ e.2 ∈ primes61)
    (hadm : ∀ p ∈ primes61, PrimeRowAdmissible p (graphNeighbors E p))
    (hdeg2 : (graphNeighbors E 53).card = 2 ∨ (graphNeighbors E 61).card = 2) :
    3 ≤ (graphNeighbors E 59).card ∧
      5 ≤ (graphNeighbors E 53).card + (graphNeighbors E 59).card + (graphNeighbors E 61).card := by
  have h59_ne : graphNeighbors E 59 ≠ ∅ := by
    intro h59
    rcases hdeg2 with h53_2 | h61_2
    · have h53_ne : graphNeighbors E 53 ≠ ∅ := by
        intro h
        simp [h] at h53_2
      have hge3 :=
        card_graphNeighbors_53_ge_three_of_59_empty E hE hend h59 (hadm 53 (by decide)) h53_ne
      omega
    · have h61_ne : graphNeighbors E 61 ≠ ∅ := by
        intro h
        simp [h] at h61_2
      have hge3 :=
        card_graphNeighbors_61_ge_three_of_59_empty E hE hend h59 (hadm 61 (by decide)) h61_ne
      omega
  have h59_ge3 : 3 ≤ (graphNeighbors E 59).card :=
    card_graphNeighbors_59_ge_three_of_nonempty E hE hend (hadm 59 (by decide)) h59_ne
  refine ⟨h59_ge3, ?_⟩
  rcases hdeg2 with h53_2 | h61_2 <;> omega

theorem primes61_sdiff_tail_eq_primes47 :
    primes61 \ ({53, 59, 61} : Finset ℕ) = primes47 := by
  decide

/-- Universal `P_61` vs. `P_47` tail-activity dichotomy:
for every `p`-admissible simple graph `E` on `primes61`, either:
1. Every tail prime `r ∈ {53, 59, 61}` is inactive (`graphNeighbors E r = ∅`) and every neighborhood
   `graphNeighbors E p` is contained in `primes47.erase p` (reducing `E` to the certified `P_47`
   domain); or
2. Some tail prime `p ∈ {53, 59, 61}` has incidence degree at least `3`
   (`3 ≤ (graphNeighbors E p).card`). -/
theorem primes61_tail_dichotomy (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ primes61 ∧ e.2 ∈ primes61)
    (hadm : ∀ p ∈ primes61, PrimeRowAdmissible p (graphNeighbors E p)) :
    ((∀ r ∈ ({53, 59, 61} : Finset ℕ), graphNeighbors E r = ∅) ∧
      (∀ p, graphNeighbors E p ⊆ primes47.erase p)) ∨
    (∃ p ∈ ({53, 59, 61} : Finset ℕ), 3 ≤ (graphNeighbors E p).card) := by
  by_cases h53 : graphNeighbors E 53 = ∅
  · by_cases h59 : graphNeighbors E 59 = ∅
    · by_cases h61 : graphNeighbors E 61 = ∅
      · left
        have hinact : ∀ r ∈ ({53, 59, 61} : Finset ℕ), graphNeighbors E r = ∅ := by
          intro r hr
          rcases Finset.mem_insert.mp hr with rfl | hr59
          · exact h53
          · rcases Finset.mem_insert.mp hr59 with rfl | hr61
            · exact h59
            · rw [Finset.mem_singleton.mp hr61]
              exact h61
        refine ⟨hinact, fun p => ?_⟩
        rw [← primes61_sdiff_tail_eq_primes47]
        exact graphNeighbors_subset_sdiff_inactive E primes61 {53, 59, 61} hE hend hinact p
      · right
        exact exists_tail_prime_card_ge_three_of_active_tail E hE hend hadm (Or.inr (Or.inr h61))
    · right
      exact exists_tail_prime_card_ge_three_of_active_tail E hE hend hadm (Or.inr (Or.inl h59))
  · right
    exact exists_tail_prime_card_ge_three_of_active_tail E hE hend hadm (Or.inl h53)


/-! ### Part 4: Explicit Positive and Negative Controls -/

/-- Positive control: concrete degree-3 admissible neighborhoods inside `primes47` for each of the
three tail primes `53` (`{2, 13, 23}`), `59` (`{2, 5, 7}`), and `61` (`{2, 3, 11}`). -/
theorem tail_primes_degree_three_positive_controls_in_primes47 :
    ({2, 13, 23} : Finset ℕ) ⊆ primes47 ∧
    ({2, 13, 23} : Finset ℕ).card = 3 ∧
    PrimeRowAdmissible 53 {2, 13, 23} ∧
    ({2, 5, 7} : Finset ℕ) ⊆ primes47 ∧
    ({2, 5, 7} : Finset ℕ).card = 3 ∧
    PrimeRowAdmissible 59 {2, 5, 7} ∧
    ({2, 3, 11} : Finset ℕ) ⊆ primes47 ∧
    ({2, 3, 11} : Finset ℕ).card = 3 ∧
    PrimeRowAdmissible 61 {2, 3, 11} := by
  decide

/-- Negative and quantitative control for the tail-activity cells:
- On `P_47` (cell `000`), the unbranched zero-potential sum is
  `34566382168021421 / 32362620136236390` and the worst leaf of the 14-leaf exact dual tree is
  `204954349153254940510464199 / 204963260862830470000000000 < 1`;
- Across all 8 cells `000..111` on `P_61`, the root LP-discovered exact rational row-potential
  bounds strictly improve upon the unbranched zero-potential sums and reduce the `P_61` excess
  from `86689711670600051093063 / 78192254239604647322180 - 1` (`≈ 0.10867390`) down to
  `1358313013723343637241719586423 / 1348142314475942195210000000000 - 1` (`< 8 / 1000`). -/
theorem tail_cells_rational_bounds_control :
    (204954349153254940510464199 : ℚ) / 204963260862830470000000000 < 1 ∧
    (1 : ℚ) < 615810276797833571805398167 / 614889782588491410000000000 ∧
    (615810276797833571805398167 : ℚ) / 614889782588491410000000000 <
      34566382168021421 / 32362620136236390 ∧
    (37634930621612607172881787049 : ℚ) / 37508276737897976010000000000 < 1 + 4 / 1000 ∧
    (3034357537575097332151516037 : ℚ) / 3023208097726749432500000000 < 1 + 4 / 1000 ∧
    (72555861252585454518850799 : ℚ) / 72259774893991230000000000 < 1 + 5 / 1000 ∧
    (1358313013723343637241719586423 : ℚ) / 1348142314475942195210000000000 < 1 + 8 / 1000 ∧
    (1358313013723343637241719586423 : ℚ) / 1348142314475942195210000000000 <
      86689711670600051093063 / 78192254239604647322180 := by
  norm_num

set_option maxRecDepth 16384

/-!
## Bilateral Additive Row-Defect Pruning, Even-Degree Parity at `2`, and Minimax Prime Incidence (`= 10`) for Erdős #306

This part builds on `Erdos306.Core.PrimeResidueAndRowPotential`, `Erdos306.GraphDual`,
`Erdos306.Representation`, and `Erdos306.PrimeIncidence` with 26
universally quantified structural theorems that formalize the bilateral additive row-cost
pruning method and resolve the extremal minimum-incidence (`= 10`) representation question for `1`:

1. **Universal Degree-`2` Parity at Prime `2` and Largest-Prime Degree-`2` Twin-Prime Structure:**
   - Every odd integer has modular inverse `1` in `ZMod 2` (`zmodInverse_two_of_odd`), so any
     finite set `S` of odd integers satisfies `zmodInverseRowSum 2 S = (S.card : ZMod 2)`
     (`zmodInverseRowSum_two_eq_card_cast`) and `PrimeRowAdmissible 2 S ↔ 2 ∣ S.card`
     (`primeRowAdmissible_two_iff_two_dvd_card`);
   - Consequently, in any oriented prime graph `E` whose reciprocal sum equals `a / b` with `b` odd,
     `2 ∣ incidenceDegree E 2` (`two_dvd_incidenceDegree_two_of_prime_graph`);
   - If an odd prime `p` has a `p`-admissible degree-2 prime neighborhood `{q₁, q₂}` with
     `q₁ < q₂ < p`, then `q₁ = 2` and `q₂ = p - 2`
     (`largest_prime_degree_two_forces_two_and_sub_two`), matching the twin-prime replacement
     identity `1/(2p) + 1/(p(p-2)) = 1/(2(p-2))` (`twin_prime_reciprocal_pair_sum_eq`).

2. **Universal Additive Row-Defect Decomposition and Bilateral Pruning Duality:**
   - Double-counting any symmetric edge slack `s p q / 2` across undirected neighborhoods
     `graphNeighbors E p` recovers `∑_{e ∈ E} s e.1 e.2` (`sum_graphNeighbors_symm_eq_sum_edges`);
   - The vertex-local `additiveRowDefect` sums over `p ∈ V` to the exact global degree-and-edge
     defect (`sum_additiveRowDefect_eq_global_defect`, `reciprocal_sum_add_sum_additiveRowDefect_eq`)
     and is pointwise nonnegative (`additiveRowDefect_nonneg`);
   - Single-vertex (`single_vertex_defect_pruning`), residual-minimum
     (`residual_min_defect_pruning`), and bilateral neighbor/non-neighbor row-cost bounds
     (`bilateral_split_sum_erase_eq`, `bilateral_row_cost_pruning`,
     `not_mem_valid_row_of_bilateral_cost_gt`) rigorously prune candidate row domains.

3. **Explicit 68-Edge Single-Tail Witnesses in Cells `100` (`P_53`), `010` (`59`), and `001` (`61`):**
   - Universal denominator-clearing identity (`sum_edges_inv_eq_one_of_cleared_nat_sum`) and
     kernel verification of 68-edge maximum-incidence-10 representations of `1` in `P_53`
     (`witnessEdgesFiftyThree_edges_valid_and_bounded`,
     `witnessEdgesFiftyThree_universal_degree_and_admissible`,
     `witnessEdgesFiftyThree_sum_eq_one_and_deg_le`), `P_47 ∪ {59}`
     (`witnessEdgesFiftyNine_valid_and_sum_eq_one`), and `P_47 ∪ {61}`
     (`witnessEdgesSixtyOne_valid_and_sum_eq_one`).

4. **Exact Minimax Prime Incidence Characterization (`d ≥ 10`) for Representing `1`:**
   - Combines the 68-semiprime `P_53` witness (`witnessSemiprimesFiftyThree_valid_and_sum_eq_one`)
     with the universal degree-9 upper bound `< 499 / 500`
     (`prime_edges_sum_ne_one_of_deg_le_nine`, `semiprime_set_sum_ne_one_of_deg_le_nine`) to prove
     both `exists_prime_edges_sum_eq_one_iff_ten_le` and
     `exists_semiprime_set_sum_eq_one_iff_ten_le`: a representation of `1` as a sum of distinct
     squarefree semiprime reciprocals with maximum prime incidence `≤ d` exists **if and only if**
     `10 ≤ d`.
-/
/-! ### Part 1: Universal Degree-`2` Parity at Prime `2` and Twin-Prime Reduction -/

/-- Every odd natural number `q` casts to `1` in `ZMod 2` and therefore has modular inverse `1`. -/
theorem zmodInverse_two_of_odd (q : ℕ) (hq : q % 2 = 1) :
    ((q : ZMod 2))⁻¹ = 1 := by
  let k := q / 2
  have hq_eq : q = 2 * k + 1 := by omega
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hcast : (q : ZMod 2) = 1 := by
    calc
      (q : ZMod 2) = ((2 * k + 1 : ℕ) : ZMod 2) := congrArg Nat.cast hq_eq
      _ = (2 : ZMod 2) * (k : ZMod 2) + 1 := by push_cast; ring
      _ = 1 := by rw [h2, zero_mul, zero_add]
  rw [hcast, inv_one]

/-- For any finite set `S` of odd natural numbers, `zmodInverseRowSum 2 S = (S.card : ZMod 2)`. -/
theorem zmodInverseRowSum_two_eq_card_cast (S : Finset ℕ)
    (hodd : ∀ q ∈ S, q % 2 = 1) :
    zmodInverseRowSum 2 S = (S.card : ZMod 2) := by
  unfold zmodInverseRowSum
  have hcongr : ∑ q ∈ S, ((q : ZMod 2))⁻¹ = ∑ _q ∈ S, (1 : ZMod 2) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact zmodInverse_two_of_odd q (hodd q hq)
  rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A finite set `S` of odd natural numbers is `2`-admissible if and only if `2 ∣ S.card`. -/
theorem primeRowAdmissible_two_iff_two_dvd_card (S : Finset ℕ)
    (hodd : ∀ q ∈ S, q % 2 = 1) :
    PrimeRowAdmissible 2 S ↔ 2 ∣ S.card := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hndvd : ∀ q ∈ S, ¬ 2 ∣ q := by
    intro q hq hdvd
    have := hodd q hq
    omega
  rw [@primeRowAdmissible_iff_zmodInverseRowSum_eq_zero 2 hfact S hndvd,
    zmodInverseRowSum_two_eq_card_cast S hodd, ZMod.natCast_eq_zero_iff]

/-- Universal parity obstruction at `p = 2`: in any oriented prime graph `E` whose reciprocal sum
equals `a / b` with `b` odd (`Nat.Coprime 2 b`), the incidence degree of `2` is even. -/
theorem two_dvd_incidenceDegree_two_of_prime_graph
    (E : Finset (ℕ × ℕ)) (b : ℕ) (a : ℤ)
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hb0 : b ≠ 0) (h2b : Nat.Coprime 2 b)
    (hsum : (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = (a : ℚ) / (b : ℚ)) :
    2 ∣ incidenceDegree E 2 := by
  have hlt : ∀ e ∈ E, e.1 < e.2 := fun e he => (hE e he).2.2
  have hadm := (prime_graph_row_admissible_of_sum_eq_div E 2 b a hE Nat.prime_two hb0 h2b hsum).1
  have hodd : ∀ q ∈ graphNeighbors E 2, q % 2 = 1 := by
    intro q hq
    rcases Finset.mem_union.mp hq with hright | hleft
    · rcases Finset.mem_image.mp hright with ⟨e, he, rfl⟩
      have heE := (Finset.mem_filter.mp he).1
      have he1 := (Finset.mem_filter.mp he).2
      have hqprime : e.2.Prime := (hE e heE).2.1
      have h2lt : e.1 < e.2 := (hE e heE).2.2
      exact hqprime.eq_two_or_odd.resolve_left (by omega)
    · rcases Finset.mem_image.mp hleft with ⟨e, he, rfl⟩
      have heE := (Finset.mem_filter.mp he).1
      have he2 := (Finset.mem_filter.mp he).2
      have hqprime : e.1.Prime := (hE e heE).1
      have hlt2 : e.1 < e.2 := (hE e heE).2.2
      have h2le : 2 ≤ e.1 := hqprime.two_le
      omega
  rw [← card_graphNeighbors_eq_incidenceDegree E hlt 2]
  exact (primeRowAdmissible_two_iff_two_dvd_card (graphNeighbors E 2) hodd).mp hadm

/-- If an odd prime `p` has a `p`-admissible degree-2 prime neighborhood `{q₁, q₂}` with
`q₁ < q₂ < p`, then `q₁ = 2` and `q₂ = p - 2` (so `(p - 2, p)` must be a twin-prime pair). -/
theorem largest_prime_degree_two_forces_two_and_sub_two
    (p q₁ q₂ : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (h12 : q₁ < q₂) (h2p : q₂ < p)
    (hadm : PrimeRowAdmissible p {q₁, q₂}) :
    q₁ = 2 ∧ q₂ = p - 2 := by
  have hq₂_odd : q₂ % 2 = 1 := by
    have hq₁_ge : 2 ≤ q₁ := hq₁.two_le
    exact hq₂.eq_two_or_odd.resolve_left (by omega)
  have hq₁_two : q₁ = 2 := by
    rcases hq₁.eq_two_or_odd with rfl | hq₁_odd
    · rfl
    · exfalso
      exact not_primeRowAdmissible_pair_of_odd_lt hp hp2 (ne_of_lt h12)
        hq₁_odd hq₂_odd (lt_trans h12 h2p) h2p hadm
  subst hq₁_two
  have hdvd : p ∣ 2 + q₂ := (primeRowAdmissible_pair_iff p (ne_of_lt h12)).mp hadm
  rcases hdvd with ⟨k, hk⟩
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hk1 : k = 1 := by nlinarith
  subst hk1
  omega

/-- Exact rational telescopic identity for a degree-2 twin-prime neighborhood `{2, p - 2}` of `p`:
`1 / (2 * p) + 1 / (p * (p - 2)) = 1 / (2 * (p - 2))`. -/
theorem twin_prime_reciprocal_pair_sum_eq (p : ℕ) (hp : 2 < p) :
    (1 : ℚ) / (2 * (p : ℚ)) + (1 : ℚ) / ((p : ℚ) * ((p : ℚ) - 2)) =
      (1 : ℚ) / (2 * ((p : ℚ) - 2)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hpm2 : (p : ℚ) - 2 ≠ 0 := by
    have : (2 : ℚ) < (p : ℚ) := by exact_mod_cast hp
    linarith
  field_simp [hp0, hpm2]
  ring


/-! ### Part 2: Universal Additive Row-Defect Decomposition and Bilateral Pruning Duality -/

/-- Additive row-defect cost at vertex `p` for a candidate neighborhood `S` under degree cap `d`,
vertex weight `lam p`, and half-split edge slack `s p q / 2`. -/
def additiveRowDefect (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (d : ℕ) (p : ℕ) (S : Finset ℕ) : ℚ :=
  ((d : ℚ) - (S.card : ℚ)) * lam p + ∑ q ∈ S, s p q / 2

/-- Summing a half-weighted symmetric edge function `s p q / 2` over all undirected neighborhoods
`graphNeighbors E p` (`p ∈ V`) recovers the exact edge sum `∑_{e ∈ E} s e.1 e.2`. -/
theorem sum_graphNeighbors_symm_eq_sum_edges (s : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hsym : ∀ e ∈ E, s e.1 e.2 = s e.2 e.1) :
    (∑ p ∈ V, ∑ q ∈ graphNeighbors E p, s p q / 2) = ∑ e ∈ E, s e.1 e.2 := by
  have hfiber : ∀ p ∈ V,
      (∑ q ∈ graphNeighbors E p, s p q / 2) =
        (∑ e ∈ E.filter (fun e => e.1 = p), s e.1 e.2 / 2) +
        (∑ e ∈ E.filter (fun e => e.2 = p), s e.2 e.1 / 2) := by
    intro p _
    rw [graphNeighbors,
      Finset.sum_union (disjoint_rightNeighbors_leftNeighbors E hE p),
      rightNeighbors, leftNeighbors,
      Finset.sum_image (injOn_snd_filter_fst E p),
      Finset.sum_image (injOn_fst_filter_snd E p)]
    congr 1
    · apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    · apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
  have hrew :
      (∑ p ∈ V, ∑ q ∈ graphNeighbors E p, s p q / 2) =
        (∑ p ∈ V, ∑ e ∈ E.filter (fun e => e.1 = p), s e.1 e.2 / 2) +
        (∑ p ∈ V, ∑ e ∈ E.filter (fun e => e.2 = p), s e.2 e.1 / 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hfiber
  have hfst := Finset.sum_fiberwise_of_maps_to
    (s := E) (t := V) (g := Prod.fst) (fun e he => (hend e he).1)
    (fun e : ℕ × ℕ => s e.1 e.2 / 2)
  have hsnd := Finset.sum_fiberwise_of_maps_to
    (s := E) (t := V) (g := Prod.snd) (fun e he => (hend e he).2)
    (fun e : ℕ × ℕ => s e.2 e.1 / 2)
  rw [hrew, hfst, hsnd, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← hsym e he]
  ring

/-- Global identity for `additiveRowDefect`: summing `additiveRowDefect lam s d p (graphNeighbors E p)`
over `p ∈ V` yields `(d : ℚ) * ∑_{p ∈ V} lam p - ∑_{p ∈ V} deg(p) * lam p + ∑_{e ∈ E} s e.1 e.2`. -/
theorem sum_additiveRowDefect_eq_global_defect (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (d : ℕ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hsym : ∀ e ∈ E, s e.1 e.2 = s e.2 e.1) :
    (∑ p ∈ V, additiveRowDefect lam s d p (graphNeighbors E p)) =
      (d : ℚ) * (∑ p ∈ V, lam p) -
        (∑ p ∈ V, (incidenceDegree E p : ℚ) * lam p) +
        ∑ e ∈ E, s e.1 e.2 := by
  unfold additiveRowDefect
  rw [Finset.sum_add_distrib, sum_graphNeighbors_symm_eq_sum_edges s E V hE hend hsym]
  congr 1
  have hdeg :
      (∑ p ∈ V, ((d : ℚ) - ((graphNeighbors E p).card : ℚ)) * lam p) =
        ∑ p ∈ V, ((d : ℚ) * lam p - (incidenceDegree E p : ℚ) * lam p) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [card_graphNeighbors_eq_incidenceDegree E hE p]
    ring
  rw [hdeg, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Exact conservation law between the reciprocal sum `∑_{e ∈ E} 1/(e.1 * e.2)` and the vertex-summed
`additiveRowDefect` whenever `1/(e.1 * e.2) + s e.1 e.2 = lam e.1 + lam e.2` on `E`. -/
theorem reciprocal_sum_add_sum_additiveRowDefect_eq (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (d : ℕ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hsym : ∀ e ∈ E, s e.1 e.2 = s e.2 e.1)
    (hdecomp : ∀ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) + s e.1 e.2 = lam e.1 + lam e.2) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) +
      (∑ p ∈ V, additiveRowDefect lam s d p (graphNeighbors E p)) =
      (d : ℚ) * (∑ p ∈ V, lam p) := by
  have hend_sum :
      (∑ e ∈ E, (lam e.1 + lam e.2)) =
        ∑ p ∈ V, (incidenceDegree E p : ℚ) * lam p := by
    have hfst := Finset.sum_fiberwise_of_maps_to'
      (s := E) (t := V) (g := Prod.fst) (fun e he => (hend e he).1) lam
    have hsnd := Finset.sum_fiberwise_of_maps_to'
      (s := E) (t := V) (g := Prod.snd) (fun e he => (hend e he).2) lam
    rw [Finset.sum_add_distrib, ← hfst, ← hsnd, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    simp [incidenceDegree, Nat.cast_add, add_mul]
  have hedges :
      (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) + (∑ e ∈ E, s e.1 e.2) =
        ∑ p ∈ V, (incidenceDegree E p : ℚ) * lam p := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hdecomp, hend_sum]
  rw [sum_additiveRowDefect_eq_global_defect lam s d E V hE hend hsym]
  linarith

/-- Pointwise nonnegativity of `additiveRowDefect` when `S.card ≤ d`, `0 ≤ lam p`, and `0 ≤ s p q`. -/
theorem additiveRowDefect_nonneg (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (d : ℕ)
    (p : ℕ) (S : Finset ℕ)
    (hcard : S.card ≤ d) (hlam : 0 ≤ lam p) (hs : ∀ q ∈ S, 0 ≤ s p q) :
    0 ≤ additiveRowDefect lam s d p S := by
  unfold additiveRowDefect
  have hd : (0 : ℚ) ≤ (d : ℚ) - (S.card : ℚ) := by
    have : (S.card : ℚ) ≤ (d : ℚ) := by exact_mod_cast hcard
    linarith
  have h1 : 0 ≤ ((d : ℚ) - (S.card : ℚ)) * lam p := mul_nonneg hd hlam
  have h2 : 0 ≤ ∑ q ∈ S, s p q / 2 := by
    apply Finset.sum_nonneg
    intro q hq
    have := hs q hq
    linarith
  linarith

/-- Single-vertex nonnegative defect pruning: if `∑_{q ∈ V} c q ≤ B` and `c ≥ 0` on `V`, then
`c p ≤ B` for every `p ∈ V`. -/
theorem single_vertex_defect_pruning (c : ℕ → ℚ) (V : Finset ℕ) (B : ℚ) (p : ℕ)
    (hp : p ∈ V) (hnonneg : ∀ q ∈ V, 0 ≤ c q) (hsum : (∑ q ∈ V, c q) ≤ B) :
    c p ≤ B := by
  have herase := Finset.add_sum_erase V c hp
  have hrest : 0 ≤ ∑ q ∈ V.erase p, c q := by
    apply Finset.sum_nonneg
    intro q hq
    exact hnonneg q (Finset.mem_of_mem_erase hq)
  linarith

/-- Residual-minimum row-cost pruning: if `cmin q ≤ c q` for all `q ∈ V.erase p` and
`∑_{q ∈ V} c q ≤ B`, then `c p + ∑_{q ∈ V.erase p} cmin q ≤ B`. -/
theorem residual_min_defect_pruning (c cmin : ℕ → ℚ) (V : Finset ℕ) (B : ℚ) (p : ℕ)
    (hp : p ∈ V)
    (hmin : ∀ q ∈ V.erase p, cmin q ≤ c q)
    (hsum : (∑ q ∈ V, c q) ≤ B) :
    c p + (∑ q ∈ V.erase p, cmin q) ≤ B := by
  have herase := Finset.add_sum_erase V c hp
  have hle : (∑ q ∈ V.erase p, cmin q) ≤ ∑ q ∈ V.erase p, c q :=
    Finset.sum_le_sum hmin
  linarith

/-- Exact partition of `∑_{q ∈ V.erase p} f q` across a neighbor subset `S ⊆ V.erase p` and its
complement `(V.erase p) \ S`. -/
theorem bilateral_split_sum_erase_eq (f : ℕ → ℚ) (V S : Finset ℕ) (p : ℕ)
    (hS : S ⊆ V.erase p) :
    (∑ q ∈ S, f q) + (∑ q ∈ (V.erase p) \ S, f q) = ∑ q ∈ V.erase p, f q := by
  have hunion : S ∪ ((V.erase p) \ S) = V.erase p := Finset.union_sdiff_of_subset hS
  have hdisj : Disjoint S ((V.erase p) \ S) := disjoint_sdiff_self_right
  rw [← Finset.sum_union hdisj, hunion]

/-- Universal bilateral row-cost pruning inequality:
by neighbor symmetry (`q ∈ graphNeighbors E p ↔ p ∈ graphNeighbors E q`), every neighbor
`q ∈ graphNeighbors E p` incurs at least `cmin1 q p` (the minimum cost at `q` given `p ∈ N_E(q)`)
and every non-neighbor `q ∈ (V.erase p) \ graphNeighbors E p` incurs at least `cmin0 q p`
(the minimum cost at `q` given `p ∉ N_E(q)`). -/
theorem bilateral_row_cost_pruning
    (c : ℕ → ℚ) (cmin1 cmin0 : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ) (B : ℚ) (p : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hp : p ∈ V)
    (hsum : (∑ q ∈ V, c q) ≤ B)
    (hmin1 : ∀ q ∈ V.erase p, p ∈ graphNeighbors E q → cmin1 q p ≤ c q)
    (hmin0 : ∀ q ∈ V.erase p, p ∉ graphNeighbors E q → cmin0 q p ≤ c q) :
    c p + (∑ q ∈ graphNeighbors E p, cmin1 q p) +
      (∑ q ∈ (V.erase p) \ graphNeighbors E p, cmin0 q p) ≤ B := by
  have hsub : graphNeighbors E p ⊆ V.erase p := by
    intro q hq
    rcases Finset.mem_union.mp hq with hright | hleft
    · rcases Finset.mem_image.mp hright with ⟨e, he, rfl⟩
      have heE := (Finset.mem_filter.mp he).1
      have hep := (Finset.mem_filter.mp he).2
      have hlt := hE e heE
      exact Finset.mem_erase.mpr ⟨by omega, (hend e heE).2⟩
    · rcases Finset.mem_image.mp hleft with ⟨e, he, rfl⟩
      have heE := (Finset.mem_filter.mp he).1
      have hep := (Finset.mem_filter.mp he).2
      have hlt := hE e heE
      exact Finset.mem_erase.mpr ⟨by omega, (hend e heE).1⟩
  have hcomm : ∀ q, q ∈ graphNeighbors E p ↔ p ∈ graphNeighbors E q := by
    intro q
    simp only [graphNeighbors, rightNeighbors, leftNeighbors, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro (⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩ | ⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩)
      · right; exact ⟨(a, b), ⟨hab, rfl⟩, rfl⟩
      · left; exact ⟨(a, b), ⟨hab, rfl⟩, rfl⟩
    · rintro (⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩ | ⟨⟨a, b⟩, ⟨hab, rfl⟩, rfl⟩)
      · right; exact ⟨(a, b), ⟨hab, rfl⟩, rfl⟩
      · left; exact ⟨(a, b), ⟨hab, rfl⟩, rfl⟩
  have hle1 : (∑ q ∈ graphNeighbors E p, cmin1 q p) ≤ ∑ q ∈ graphNeighbors E p, c q := by
    apply Finset.sum_le_sum
    intro q hq
    exact hmin1 q (hsub hq) ((hcomm q).mp hq)
  have hle0 : (∑ q ∈ (V.erase p) \ graphNeighbors E p, cmin0 q p) ≤
      ∑ q ∈ (V.erase p) \ graphNeighbors E p, c q := by
    apply Finset.sum_le_sum
    intro q hq
    have hq_erase := (Finset.mem_sdiff.mp hq).1
    have hq_not := (Finset.mem_sdiff.mp hq).2
    exact hmin0 q hq_erase (fun hpq => hq_not ((hcomm q).mpr hpq))
  have hsplit := bilateral_split_sum_erase_eq c V (graphNeighbors E p) p hsub
  have herase := Finset.add_sum_erase V c hp
  linarith

/-- Contrapositive bilateral pruning rule: if a candidate neighborhood `S` at vertex `p` has
`B < c p + ∑_{q ∈ S} cmin1 q p + ∑_{q ∈ (V.erase p) \ S} cmin0 q p`, then `graphNeighbors E p ≠ S`. -/
theorem not_mem_valid_row_of_bilateral_cost_gt
    (c : ℕ → ℚ) (cmin1 cmin0 : ℕ → ℕ → ℚ)
    (E : Finset (ℕ × ℕ)) (V S : Finset ℕ) (B : ℚ) (p : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hp : p ∈ V)
    (hsum : (∑ q ∈ V, c q) ≤ B)
    (hmin1 : ∀ q ∈ V.erase p, p ∈ graphNeighbors E q → cmin1 q p ≤ c q)
    (hmin0 : ∀ q ∈ V.erase p, p ∉ graphNeighbors E q → cmin0 q p ≤ c q)
    (hgt : B < c p + (∑ q ∈ S, cmin1 q p) + (∑ q ∈ (V.erase p) \ S, cmin0 q p)) :
    graphNeighbors E p ≠ S := by
  intro heq
  have hle := bilateral_row_cost_pruning c cmin1 cmin0 E V B p hE hend hp hsum hmin1 hmin0
  rw [heq] at hle
  linarith


/-! ### Part 3: Explicit 68-Edge Incidence-10 Representations of `1` in Cells `100`, `010`, and `001` -/

/-- Universal denominator-clearing identity for unit-sum edge sets: if `M ≠ 0`, every edge product
`e.1 * e.2` divides `M`, and `∑_{e ∈ E} M / (e.1 * e.2) = M` in `ℕ`, then
`∑_{e ∈ E} 1 / (e.1 * e.2) = 1` in `ℚ`. -/
theorem sum_edges_inv_eq_one_of_cleared_nat_sum
    (E : Finset (ℕ × ℕ)) (M : ℕ) (hM0 : M ≠ 0)
    (hdvd : ∀ e ∈ E, e.1 * e.2 ∣ M)
    (hsum : (∑ e ∈ E, M / (e.1 * e.2)) = M) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 := by
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
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum, hsum, div_self hM_q]

def pool47 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47}

def pool53 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53}

def primorial47 : ℕ :=
  2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41 * 43 * 47

/-- Explicit 68-edge representation of `1` on `P_53` (cell `100`) with maximum prime incidence `10`,
establishing that the `P_47` exclusion bound (`p_max ≥ 53`) is sharp. -/
def witnessEdgesFiftyThree : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37),
   (5, 7), (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31),
   (7, 11), (7, 13), (7, 17), (7, 19), (7, 23), (7, 29), (7, 53),
   (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 19), (13, 23), (13, 29), (13, 31), (13, 53),
   (17, 19), (17, 23), (17, 37), (17, 41), (17, 47),
   (19, 29), (19, 41), (19, 43),
   (23, 43),
   (29, 31), (29, 37), (29, 41), (29, 43), (29, 53),
   (31, 37), (31, 41), (31, 47), (31, 53),
   (37, 47), (37, 53),
   (41, 43), (41, 53),
   (43, 53)}

/-- Explicit 68-edge representation of `1` on `P_47 ∪ {59}` (single-tail cell `010`) with
maximum prime incidence `10`. -/
def witnessEdgesFiftyNine : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37),
   (5, 7), (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31),
   (7, 11), (7, 13), (7, 17), (7, 19), (7, 23), (7, 37), (7, 41),
   (11, 13), (11, 17), (11, 19), (11, 23), (11, 29), (11, 47),
   (13, 17), (13, 19), (13, 29), (13, 37), (13, 43),
   (17, 19), (17, 23), (17, 31),
   (19, 29), (19, 41), (19, 43),
   (23, 37), (23, 41), (23, 47), (23, 59),
   (29, 31), (29, 41), (29, 43), (29, 47), (29, 59),
   (31, 37), (31, 59),
   (37, 43), (37, 47), (37, 59),
   (41, 43),
   (43, 47),
   (47, 59)}

/-- Explicit 68-edge representation of `1` on `P_47 ∪ {61}` (single-tail cell `001`) with
maximum prime incidence `10`. -/
def witnessEdgesSixtyOne : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37),
   (5, 7), (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 41),
   (7, 11), (7, 13), (7, 17), (7, 19), (7, 23), (7, 37), (7, 41),
   (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 29), (13, 37), (13, 43),
   (17, 23), (17, 29), (17, 37), (17, 47),
   (19, 29), (19, 31), (19, 41), (19, 61),
   (23, 29), (23, 31), (23, 41), (23, 43),
   (29, 31), (29, 37), (29, 43),
   (31, 37), (31, 43), (31, 47),
   (37, 41), (37, 47), (37, 61),
   (41, 43),
   (43, 61)}

/-- Every edge in `witnessEdgesFiftyThree` has prime endpoints in `pool53` with `e.1 < e.2`. -/
theorem witnessEdgesFiftyThree_edges_valid_and_bounded :
    ∀ e ∈ witnessEdgesFiftyThree,
      e.1 ∈ pool53 ∧ e.2 ∈ pool53 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2 := by
  decide

/-- Every natural number `p` has `incidenceDegree witnessEdgesFiftyThree p ≤ 10`, and every
`p ∈ pool53` has a `p`-admissible neighborhood in `witnessEdgesFiftyThree`. -/
theorem witnessEdgesFiftyThree_universal_degree_and_admissible (p : ℕ) :
    incidenceDegree witnessEdgesFiftyThree p ≤ 10 ∧
      (p ∈ pool53 → PrimeRowAdmissible p (graphNeighbors witnessEdgesFiftyThree p)) := by
  have hpool : ∀ q ∈ pool53,
      incidenceDegree witnessEdgesFiftyThree q ≤ 10 ∧
        PrimeRowAdmissible q (graphNeighbors witnessEdgesFiftyThree q) := by
    decide
  by_cases hp : p ∈ pool53
  · exact ⟨(hpool p hp).1, fun _ => (hpool p hp).2⟩
  · refine ⟨?_, fun hp_in => False.elim (hp hp_in)⟩
    have h1 : (witnessEdgesFiftyThree.filter fun e => e.1 = p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hfst
      exact hp (hfst ▸ (witnessEdgesFiftyThree_edges_valid_and_bounded e he).1)
    have h2 : (witnessEdgesFiftyThree.filter fun e => e.2 = p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hsnd
      exact hp (hsnd ▸ (witnessEdgesFiftyThree_edges_valid_and_bounded e he).2.1)
    simp [incidenceDegree, h1, h2]

/-- For every degree bound `d ≥ 10`, `witnessEdgesFiftyThree` has exact reciprocal sum `1`,
cardinality `68`, and universal incidence degree `≤ d`. -/
theorem witnessEdgesFiftyThree_sum_eq_one_and_deg_le (d : ℕ) (hd : 10 ≤ d) :
    (∑ e ∈ witnessEdgesFiftyThree, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdgesFiftyThree.card = 68 ∧
      ∀ p, incidenceDegree witnessEdgesFiftyThree p ≤ d := by
  refine ⟨?_, by decide, fun p =>
    le_trans (witnessEdgesFiftyThree_universal_degree_and_admissible p).1 hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdgesFiftyThree (primorial47 * 53)
    (by decide) (by decide) (by decide)

/-- Kernel verification of the 68-edge single-tail witness in cell `010` (`pool47 ∪ {59}`). -/
theorem witnessEdgesFiftyNine_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdgesFiftyNine,
      e.1 ∈ pool47 ∪ {59} ∧ e.2 ∈ pool47 ∪ {59} ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdgesFiftyNine, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdgesFiftyNine.card = 68 ∧
      ∀ p ∈ pool47 ∪ {59}, incidenceDegree witnessEdgesFiftyNine p ≤ d := by
  have hdeg : ∀ p ∈ pool47 ∪ {59}, incidenceDegree witnessEdgesFiftyNine p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdgesFiftyNine (primorial47 * 59)
    (by decide) (by decide) (by decide)

/-- Kernel verification of the 68-edge single-tail witness in cell `001` (`pool47 ∪ {61}`). -/
theorem witnessEdgesSixtyOne_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdgesSixtyOne,
      e.1 ∈ pool47 ∪ {61} ∧ e.2 ∈ pool47 ∪ {61} ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdgesSixtyOne, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdgesSixtyOne.card = 68 ∧
      ∀ p ∈ pool47 ∪ {61}, incidenceDegree witnessEdgesSixtyOne p ≤ d := by
  have hdeg : ∀ p ∈ pool47 ∪ {61}, incidenceDegree witnessEdgesSixtyOne p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdgesSixtyOne (primorial47 * 61)
    (by decide) (by decide) (by decide)


/-! ### Part 4: Exact Minimax Prime Incidence Theorem (`= 10`) for Representations of `1` -/

/-- The 68 distinct squarefree semiprime denominators induced by `witnessEdgesFiftyThree`. -/
def witnessSemiprimesFiftyThree : Finset ℕ :=
  witnessEdgesFiftyThree.image (fun e => e.1 * e.2)

/-- For every `d ≥ 10`, `witnessSemiprimesFiftyThree` is a 68-element set of distinct squarefree
semiprimes (`ω(n) = Ω(n) = 2`) with maximum prime divisibility count `≤ d` and reciprocal sum `1`. -/
theorem witnessSemiprimesFiftyThree_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    witnessSemiprimesFiftyThree.card = 68 ∧
      (∀ n ∈ witnessSemiprimesFiftyThree,
        ArithmeticFunction.cardDistinctFactors n = 2 ∧ ArithmeticFunction.cardFactors n = 2) ∧
      (∀ p : ℕ, p.Prime → (witnessSemiprimesFiftyThree.filter fun n => p ∣ n).card ≤ d) ∧
      (∑ n ∈ witnessSemiprimesFiftyThree, (1 : ℚ) / (n : ℚ)) = 1 := by
  have hE : ∀ e ∈ witnessEdgesFiftyThree, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2 := by
    intro e he
    exact (witnessEdgesFiftyThree_edges_valid_and_bounded e he).2.2
  have hsum_deg := witnessEdgesFiftyThree_sum_eq_one_and_deg_le d hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold witnessSemiprimesFiftyThree
    rw [Finset.card_image_of_injOn
      (Erdos306.Representation.product_injOn_prime_edges witnessEdgesFiftyThree hE)]
    exact hsum_deg.2.1
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨e, he, rfl⟩
    rcases hE e he with ⟨hp, hq, hlt⟩
    exact Erdos306.Representation.factor_counts_of_distinct_primes e.1 e.2 hp hq hlt
  · intro p hp
    unfold witnessSemiprimesFiftyThree
    rw [← Erdos306.Representation.degree_eq_divisible_denominators witnessEdgesFiftyThree hE p hp]
    exact hsum_deg.2.2 p
  · unfold witnessSemiprimesFiftyThree
    rw [Erdos306.Representation.reciprocal_sum_image_prime_edges witnessEdgesFiftyThree hE]
    have hcast :
        (∑ e ∈ witnessEdgesFiftyThree, (1 : ℚ) / (e.1 * e.2 : ℕ)) =
          ∑ e ∈ witnessEdgesFiftyThree, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro e _
      push_cast
      rfl
    rw [hcast]
    exact hsum_deg.1

/-- Rational prime-graph exclusion for `d ≤ 9`: no oriented prime graph `E` with maximum prime
incidence `≤ d` (`d ≤ 9`) can have rational reciprocal sum equal to `1`. -/
theorem prime_edges_sum_ne_one_of_deg_le_nine
    (E : Finset (ℕ × ℕ)) (d : ℕ) (hd : d ≤ 9)
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ d) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) ≠ 1 := by
  intro hsum
  have hdeg9 : ∀ p : ℕ, p.Prime → Erdos306.GraphDual.incidenceDegree E p ≤ 9 := by
    intro p hp
    exact le_trans (hdeg p hp) hd
  have hlt := Erdos306.PrimeIncidence.prime_edges_of_degree_le_nine E hE hdeg9
  have hcast : ((∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) : ℚ) : ℝ) = (1 : ℝ) := by
    exact_mod_cast hsum
  have heq : ((∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) : ℚ) : ℝ) =
      ∑ e ∈ E, (1 : ℝ) / (e.1 * e.2 : ℕ) := by
    push_cast
    rfl
  rw [heq] at hcast
  linarith

/-- **Exact Minimax Prime-Graph Incidence Theorem for `1`:**
An oriented prime graph `E` with rational reciprocal sum `1` and maximum prime incidence `≤ d`
exists if and only if `10 ≤ d`. -/
theorem exists_prime_edges_sum_eq_one_iff_ten_le (d : ℕ) :
    (∃ E : Finset (ℕ × ℕ),
      (∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∀ p : ℕ, p.Prime → incidenceDegree E p ≤ d) ∧
      (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1) ↔ 10 ≤ d := by
  constructor
  · rintro ⟨E, hE, hdeg, hsum⟩
    by_contra hlt
    exact prime_edges_sum_ne_one_of_deg_le_nine E d (by omega) hE hdeg hsum
  · intro hd
    have h := witnessEdgesFiftyThree_sum_eq_one_and_deg_le d hd
    refine ⟨witnessEdgesFiftyThree, ?_, fun p _ => h.2.2 p, h.1⟩
    intro e he
    exact (witnessEdgesFiftyThree_edges_valid_and_bounded e he).2.2

/-- Rational semiprime-set exclusion for `d ≤ 9`: no finite set `S` of distinct squarefree
semiprimes with maximum prime divisibility count `≤ d` (`d ≤ 9`) has reciprocal sum `1`. -/
theorem semiprime_set_sum_ne_one_of_deg_le_nine
    (S : Finset ℕ) (d : ℕ) (hd : d ≤ 9)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ d) :
    (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) ≠ 1 := by
  intro hsum
  have hcast : ((∑ n ∈ S, (1 : ℚ) / (n : ℚ) : ℚ) : ℝ) = (1 : ℝ) := by
    exact_mod_cast hsum
  have hge1 : (1 : ℝ) ≤ ∑ n ∈ S, (1 : ℝ) / (n : ℝ) := by
    have heq : ((∑ n ∈ S, (1 : ℚ) / (n : ℚ) : ℚ) : ℝ) = ∑ n ∈ S, (1 : ℝ) / (n : ℝ) := by
      push_cast
      rfl
    linarith
  rcases Erdos306.PrimeIncidence.semiprime_sum_ge_one_forces_degree_ten S hS hge1 with ⟨p, hp, h10⟩
  have hle := le_trans (hdeg p hp) hd
  omega

/-- **Exact Minimax Semiprime-Denominator Incidence Theorem for `1`:**
A finite set `S` of distinct squarefree semiprime denominators (`ω(n) = Ω(n) = 2`) with rational
reciprocal sum `1` and maximum prime incidence `≤ d` exists if and only if `10 ≤ d`. -/
theorem exists_semiprime_set_sum_eq_one_iff_ten_le (d : ℕ) :
    (∃ S : Finset ℕ,
      (∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
        ArithmeticFunction.cardFactors n = 2) ∧
      (∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ d) ∧
      (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1) ↔ 10 ≤ d := by
  constructor
  · rintro ⟨S, hS, hdeg, hsum⟩
    by_contra hlt
    exact semiprime_set_sum_ne_one_of_deg_le_nine S d (by omega) hS hdeg hsum
  · intro hd
    have h := witnessSemiprimesFiftyThree_valid_and_sum_eq_one d hd
    exact ⟨witnessSemiprimesFiftyThree, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## Handshake identity, constant-tail capacity duals, and `P_47`/`P_61` certificates -/

/-! ### Part 1: Handshake Identity, Degree-Slack Conservation, and Lagrangian Duality -/

theorem sum_incidenceDegree_eq_two_mul_card {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (V : Finset α)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    (∑ v ∈ V, incidenceDegree E v) = 2 * E.card := by
  have hfst := Finset.sum_fiberwise_of_maps_to'
    (s := E) (t := V) (g := Prod.fst) (fun e he => (hend e he).1) (fun _ => (1 : ℕ))
  have hsnd := Finset.sum_fiberwise_of_maps_to'
    (s := E) (t := V) (g := Prod.snd) (fun e he => (hend e he).2) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hfst hsnd
  unfold incidenceDegree
  rw [Finset.sum_add_distrib, hfst, hsnd, two_mul]

theorem sum_card_graphNeighbors_eq_two_mul_card
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    (∑ p ∈ V, (graphNeighbors E p).card) = 2 * E.card := by
  have hcongr :
      (∑ p ∈ V, (graphNeighbors E p).card) = ∑ p ∈ V, incidenceDegree E p := by
    apply Finset.sum_congr rfl
    intro p _
    exact card_graphNeighbors_eq_incidenceDegree E hE p
  rw [hcongr, sum_incidenceDegree_eq_two_mul_card E V hend]

theorem sum_degree_slack_eq_mul_card_sub_two_mul_edges
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ) (d : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    (∑ p ∈ V, ((d : ℚ) - ((graphNeighbors E p).card : ℚ))) =
      (d : ℚ) * (V.card : ℚ) - 2 * (E.card : ℚ) := by
  have hsum_nat := sum_card_graphNeighbors_eq_two_mul_card E V hE hend
  have hsum_q :
      (∑ p ∈ V, ((graphNeighbors E p).card : ℚ)) = 2 * (E.card : ℚ) := by
    exact_mod_cast hsum_nat
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsum_q]
  ring

def lagrangianRowDefect (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (β : ℚ) (d : ℕ) (p : ℕ) (S : Finset ℕ) : ℚ :=
  additiveRowDefect lam s d p S - β * ((d : ℚ) - (S.card : ℚ))

theorem lagrangianRowDefect_eq_shifted_weight
    (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (β : ℚ) (d p : ℕ) (S : Finset ℕ) :
    lagrangianRowDefect lam s β d p S =
      ((d : ℚ) - (S.card : ℚ)) * (lam p - β) + ∑ q ∈ S, s p q / 2 := by
  unfold lagrangianRowDefect additiveRowDefect
  ring

theorem sum_lagrangianRowDefect_eq_sum_additiveRowDefect_sub
    (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (β : ℚ) (d : ℕ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    (∑ p ∈ V, lagrangianRowDefect lam s β d p (graphNeighbors E p)) =
      (∑ p ∈ V, additiveRowDefect lam s d p (graphNeighbors E p)) -
        β * ((d : ℚ) * (V.card : ℚ) - 2 * (E.card : ℚ)) := by
  unfold lagrangianRowDefect
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_degree_slack_eq_mul_card_sub_two_mul_edges E V d hE hend]

theorem reciprocal_sum_add_sum_lagrangianRowDefect_eq
    (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (β : ℚ) (d : ℕ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hsym : ∀ e ∈ E, s e.1 e.2 = s e.2 e.1)
    (hdecomp : ∀ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) + s e.1 e.2 = lam e.1 + lam e.2) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) +
      (∑ p ∈ V, lagrangianRowDefect lam s β d p (graphNeighbors E p)) +
      β * ((d : ℚ) * (V.card : ℚ) - 2 * (E.card : ℚ)) =
      (d : ℚ) * (∑ p ∈ V, lam p) := by
  have hcons := reciprocal_sum_add_sum_additiveRowDefect_eq lam s d E V hE hend hsym hdecomp
  rw [sum_lagrangianRowDefect_eq_sum_additiveRowDefect_sub lam s β d E V hE hend]
  linarith

theorem sum_lagrangianRowDefect_le_of_card_le
    (lam : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (β B : ℚ) (d K : ℕ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hβ : 0 ≤ β)
    (hcard : E.card ≤ K)
    (hsum : (∑ p ∈ V, additiveRowDefect lam s d p (graphNeighbors E p)) ≤ B) :
    (∑ p ∈ V, lagrangianRowDefect lam s β d p (graphNeighbors E p)) ≤
      B - β * ((d : ℚ) * (V.card : ℚ) - 2 * (K : ℚ)) := by
  rw [sum_lagrangianRowDefect_eq_sum_additiveRowDefect_sub lam s β d E V hE hend]
  have hK : (E.card : ℚ) ≤ (K : ℚ) := by exact_mod_cast hcard
  have hmul : 0 ≤ β * (2 * ((K : ℚ) - (E.card : ℚ))) :=
    mul_nonneg hβ (by linarith)
  linarith

theorem lagrangian_bilateral_row_cost_pruning
    (lam : ℕ → ℚ) (s cmin1 cmin0 : ℕ → ℕ → ℚ) (β B : ℚ) (d K : ℕ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ) (p : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hp : p ∈ V) (hβ : 0 ≤ β) (hcard : E.card ≤ K)
    (hsum : (∑ q ∈ V, additiveRowDefect lam s d q (graphNeighbors E q)) ≤ B)
    (hmin1 : ∀ q ∈ V.erase p, p ∈ graphNeighbors E q →
      cmin1 q p ≤ lagrangianRowDefect lam s β d q (graphNeighbors E q))
    (hmin0 : ∀ q ∈ V.erase p, p ∉ graphNeighbors E q →
      cmin0 q p ≤ lagrangianRowDefect lam s β d q (graphNeighbors E q)) :
    lagrangianRowDefect lam s β d p (graphNeighbors E p) +
      (∑ q ∈ graphNeighbors E p, cmin1 q p) +
      (∑ q ∈ (V.erase p) \ graphNeighbors E p, cmin0 q p) ≤
      B - β * ((d : ℚ) * (V.card : ℚ) - 2 * (K : ℚ)) := by
  have hlag := sum_lagrangianRowDefect_le_of_card_le lam s β B d K E V hE hend hβ hcard hsum
  exact bilateral_row_cost_pruning
    (fun q => lagrangianRowDefect lam s β d q (graphNeighbors E q))
    cmin1 cmin0 E V (B - β * ((d : ℚ) * (V.card : ℚ) - 2 * (K : ℚ))) p
    hE hend hp hlag hmin1 hmin0

theorem card_edges_gt_of_sum_lagrangian_min_gt
    (lam cmin : ℕ → ℚ) (s : ℕ → ℕ → ℚ) (β B : ℚ) (d K : ℕ)
    (E : Finset (ℕ × ℕ)) (V : Finset ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hβ : 0 ≤ β)
    (hsum : (∑ q ∈ V, additiveRowDefect lam s d q (graphNeighbors E q)) ≤ B)
    (hmin : ∀ q ∈ V, cmin q ≤ lagrangianRowDefect lam s β d q (graphNeighbors E q))
    (hgt : B - β * ((d : ℚ) * (V.card : ℚ) - 2 * (K : ℚ)) < ∑ q ∈ V, cmin q) :
    K < E.card := by
  by_contra hle
  have hcard : E.card ≤ K := by omega
  have hlag := sum_lagrangianRowDefect_le_of_card_le lam s β B d K E V hE hend hβ hcard hsum
  have hsum_min : (∑ q ∈ V, cmin q) ≤
      ∑ q ∈ V, lagrangianRowDefect lam s β d q (graphNeighbors E q) :=
    Finset.sum_le_sum hmin
  linarith

/-! ### Part 2: Universal Constant-Tail Capacity Dual and All-Support Minimum Cardinality (`|E| ≥ 53`) -/

theorem constant_tail_head_head_identity (x y t : ℚ) :
    (t * x - t ^ 2) + (t * y - t ^ 2) + t ^ 2 + (x - t) * (y - t) = x * y := by
  ring

theorem constant_tail_head_tail_bound (x y t : ℚ) (hx : 0 ≤ x) (hy : y ≤ t) :
    x * y ≤ (t * x - t ^ 2) + t ^ 2 := by
  have h1 : 0 ≤ x * (t - y) := mul_nonneg hx (sub_nonneg.mpr hy)
  linarith

theorem constant_tail_tail_tail_bound (x y t : ℚ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxt : x ≤ t) (hyt : y ≤ t) :
    x * y ≤ t ^ 2 := by
  have h1 : x * y ≤ t * y := mul_le_mul_of_nonneg_right hxt hy0
  have h2 : t * y ≤ t * t := mul_le_mul_of_nonneg_left hyt (le_trans hx0 hxt)
  linarith

theorem capacity_dual_with_edge_offset {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (V : Finset α) (lam : α → ℚ)
    (w z : α × α → ℚ) (μ : ℚ) (D : ℕ)
    (hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V)
    (hlam : ∀ v ∈ V, 0 ≤ lam v)
    (hdeg : ∀ v ∈ V, incidenceDegree E v ≤ D)
    (hedge : ∀ e ∈ E, w e ≤ lam e.1 + lam e.2 + μ + z e) :
    (∑ e ∈ E, w e) ≤ (D : ℚ) * (∑ v ∈ V, lam v) + μ * (E.card : ℚ) + ∑ e ∈ E, z e := by
  have hend_sum :
      (∑ e ∈ E, (lam e.1 + lam e.2)) = ∑ v ∈ V, (incidenceDegree E v : ℚ) * lam v := by
    have hfst := Finset.sum_fiberwise_of_maps_to'
      (s := E) (t := V) (g := Prod.fst) (fun e he => (hend e he).1) lam
    have hsnd := Finset.sum_fiberwise_of_maps_to'
      (s := E) (t := V) (g := Prod.snd) (fun e he => (hend e he).2) lam
    rw [Finset.sum_add_distrib, ← hfst, ← hsnd, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    simp [incidenceDegree, Nat.cast_add, add_mul]
  have hdeg_sum :
      (∑ v ∈ V, (incidenceDegree E v : ℚ) * lam v) ≤ (D : ℚ) * (∑ v ∈ V, lam v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg v hv) (hlam v hv)
  have hstep1 : (∑ e ∈ E, w e) ≤ ∑ e ∈ E, (lam e.1 + lam e.2 + μ + z e) :=
    Finset.sum_le_sum hedge
  have hstep2 :
      (∑ e ∈ E, (lam e.1 + lam e.2 + μ + z e)) =
        (∑ e ∈ E, (lam e.1 + lam e.2)) + μ * (E.card : ℚ) + ∑ e ∈ E, z e := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith

def headPrimes29 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

def headPairs29 : Finset (ℕ × ℕ) :=
  (headPrimes29 ×ˢ headPrimes29).filter (fun e => e.1 < e.2)

def headCardLam (p : ℕ) : ℚ :=
  if p ∈ headPrimes29 then (1 / 31 : ℚ) * (1 / (p : ℚ)) - (1 / 31 : ℚ) ^ 2 else 0

def headCardSlack (e : ℕ × ℕ) : ℚ :=
  if e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29 then
    ((1 : ℚ) / (e.1 : ℚ) - (1 / 31 : ℚ)) * ((1 : ℚ) / (e.2 : ℚ) - (1 / 31 : ℚ))
  else 0

theorem mem_headPrimes29_bounds {p : ℕ} (hp : p ∈ headPrimes29) :
    1 ≤ p ∧ p ≤ 29 := by
  have h : ∀ q ∈ headPrimes29, 1 ≤ q ∧ q ≤ 29 := by decide
  exact h p hp

theorem prime_ge_thirty_one_of_not_mem_headPrimes29 {p : ℕ} (hp : p.Prime)
    (hnot : p ∉ headPrimes29) : 31 ≤ p := by
  by_contra hlt
  have hle30 : p ∈ Finset.Icc 2 30 := Finset.mem_Icc.mpr ⟨hp.two_le, by omega⟩
  have hcheck : ∀ q ∈ Finset.Icc 2 30, Nat.Prime q → q ∈ headPrimes29 := by decide
  exact hnot (hcheck p hle30 hp)

theorem headCardLam_nonneg (p : ℕ) : 0 ≤ headCardLam p := by
  unfold headCardLam
  split_ifs with hp
  · rcases mem_headPrimes29_bounds hp with ⟨h1, h2⟩
    have hinv : (1 / 31 : ℚ) ≤ (1 : ℚ) / (p : ℚ) :=
      one_div_le_one_div_of_le (by exact_mod_cast h1) (by exact_mod_cast (show p ≤ 31 by omega))
    nlinarith
  · rfl

theorem headCardSlack_nonneg (e : ℕ × ℕ) : 0 ≤ headCardSlack e := by
  unfold headCardSlack
  split_ifs with he
  · rcases mem_headPrimes29_bounds he.1 with ⟨h1a, h1b⟩
    rcases mem_headPrimes29_bounds he.2 with ⟨h2a, h2b⟩
    have hp1 : (1 / 31 : ℚ) ≤ (1 : ℚ) / (e.1 : ℚ) :=
      one_div_le_one_div_of_le (by exact_mod_cast h1a) (by exact_mod_cast (show e.1 ≤ 31 by omega))
    have hp2 : (1 / 31 : ℚ) ≤ (1 : ℚ) / (e.2 : ℚ) :=
      one_div_le_one_div_of_le (by exact_mod_cast h2a) (by exact_mod_cast (show e.2 ≤ 31 by omega))
    exact mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hp2)
  · rfl

theorem prime_edge_inv_le_headCard_decomp (e : ℕ × ℕ)
    (he : e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) :
    (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) ≤
      headCardLam e.1 + headCardLam e.2 + (1 / 31 : ℚ) ^ 2 + headCardSlack e := by
  rcases he with ⟨hp1, hp2, hlt⟩
  have hx0 : (0 : ℚ) ≤ (1 : ℚ) / (e.1 : ℚ) := by positivity
  have hy0 : (0 : ℚ) ≤ (1 : ℚ) / (e.2 : ℚ) := by positivity
  have hsplit : (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) =
      ((1 : ℚ) / (e.1 : ℚ)) * ((1 : ℚ) / (e.2 : ℚ)) :=
    (one_div_mul_one_div (e.1 : ℚ) (e.2 : ℚ)).symm
  rw [hsplit]
  by_cases h1 : e.1 ∈ headPrimes29
  · by_cases h2 : e.2 ∈ headPrimes29
    · have hh : e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29 := ⟨h1, h2⟩
      unfold headCardLam headCardSlack
      rw [if_pos h1, if_pos h2, if_pos hh,
        constant_tail_head_head_identity ((1 : ℚ) / (e.1 : ℚ)) ((1 : ℚ) / (e.2 : ℚ)) (1 / 31 : ℚ)]
    · have hh : ¬ (e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29) := fun h => h2 h.2
      have hge2 : 31 ≤ e.2 := prime_ge_thirty_one_of_not_mem_headPrimes29 hp2 h2
      have hy_le : (1 : ℚ) / (e.2 : ℚ) ≤ (1 / 31 : ℚ) :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge2)
      unfold headCardLam headCardSlack
      rw [if_pos h1, if_neg h2, if_neg hh]
      have hbd := constant_tail_head_tail_bound
        ((1 : ℚ) / (e.1 : ℚ)) ((1 : ℚ) / (e.2 : ℚ)) (1 / 31 : ℚ) hx0 hy_le
      linarith
  · have h2 : e.2 ∉ headPrimes29 := by
      intro h2in
      have h2le : e.2 ≤ 29 := (mem_headPrimes29_bounds h2in).2
      have h1ge : 31 ≤ e.1 := prime_ge_thirty_one_of_not_mem_headPrimes29 hp1 h1
      omega
    have hh : ¬ (e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29) := fun h => h1 h.1
    have hge1 : 31 ≤ e.1 := prime_ge_thirty_one_of_not_mem_headPrimes29 hp1 h1
    have hge2 : 31 ≤ e.2 := prime_ge_thirty_one_of_not_mem_headPrimes29 hp2 h2
    have hx_le : (1 : ℚ) / (e.1 : ℚ) ≤ (1 / 31 : ℚ) :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge1)
    have hy_le : (1 : ℚ) / (e.2 : ℚ) ≤ (1 / 31 : ℚ) :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge2)
    unfold headCardLam headCardSlack
    rw [if_neg h1, if_neg h2, if_neg hh]
    have hbd := constant_tail_tail_tail_bound
      ((1 : ℚ) / (e.1 : ℚ)) ((1 : ℚ) / (e.2 : ℚ)) (1 / 31 : ℚ) hx0 hy0 hx_le hy_le
    linarith

theorem prime_edges_card_ge_fifty_three_of_deg_le_ten
    (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2)
    (hdeg : ∀ p : ℕ, p.Prime → incidenceDegree E p ≤ 10)
    (hsum : (1 : ℚ) ≤ ∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) :
    53 ≤ E.card := by
  let V := headPrimes29 ∪ E.image Prod.fst ∪ E.image Prod.snd
  have hend : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V := by
    intro e he
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))
  have hdegV : ∀ v ∈ V, incidenceDegree E v ≤ 10 := by
    intro v _
    by_cases hv : v.Prime
    · exact hdeg v hv
    · have h1 : (E.filter fun e => e.1 = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he hfst
        exact hv (hfst ▸ (hE e he).1)
      have h2 : (E.filter fun e => e.2 = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he hsnd
        exact hv (hsnd ▸ (hE e he).2.1)
      simp [incidenceDegree, h1, h2]
  have hcap := capacity_dual_with_edge_offset E V headCardLam
    (fun e => (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) headCardSlack ((1 / 31 : ℚ) ^ 2) 10
    hend (fun v _ => headCardLam_nonneg v) hdegV
    (fun e he => prime_edge_inv_le_headCard_decomp e (hE e he))
  have hlam_eq : (∑ v ∈ V, headCardLam v) = ∑ v ∈ headPrimes29, headCardLam v := by
    symm
    apply Finset.sum_subset
    · intro v hv
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
    · intro v _ hvnot
      unfold headCardLam
      rw [if_neg hvnot]
  have hslack_le : (∑ e ∈ E, headCardSlack e) ≤ ∑ e ∈ headPairs29, headCardSlack e := by
    have hfilter : (∑ e ∈ E, headCardSlack e) =
        ∑ e ∈ E.filter (fun e => e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29), headCardSlack e := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ E)
      intro e _ henot
      have hnot : ¬ (e.1 ∈ headPrimes29 ∧ e.2 ∈ headPrimes29) := by
        intro hh
        exact henot (Finset.mem_filter.mpr ⟨by aesop, hh⟩)
      unfold headCardSlack
      rw [if_neg hnot]
    rw [hfilter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      rcases Finset.mem_filter.mp he with ⟨heE, h1, h2⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, (hE e heE).2.2⟩
    · intro e _ _
      exact headCardSlack_nonneg e
  have hconst :
      (10 : ℚ) * (∑ v ∈ headPrimes29, headCardLam v) + (∑ e ∈ headPairs29, headCardSlack e) +
        52 * ((1 / 31 : ℚ) ^ 2) < 1 := by
    decide +kernel
  rw [hlam_eq] at hcap
  have hlt : (52 : ℚ) < (E.card : ℚ) := by
    by_contra hle
    have hle' : (E.card : ℚ) ≤ 52 := not_lt.mp hle
    have hmul : ((1 / 31 : ℚ) ^ 2) * (E.card : ℚ) ≤ 52 * ((1 / 31 : ℚ) ^ 2) := by linarith
    linarith
  have hlt_nat : 52 < E.card := by exact_mod_cast hlt
  omega

theorem semiprime_set_card_ge_fifty_three_of_deg_le_ten
    (S : Finset ℕ)
    (hS : ∀ n ∈ S, ArithmeticFunction.cardDistinctFactors n = 2 ∧
      ArithmeticFunction.cardFactors n = 2)
    (hdeg : ∀ p : ℕ, p.Prime → (S.filter fun n => p ∣ n).card ≤ 10)
    (hsum : (1 : ℚ) ≤ ∑ n ∈ S, (1 : ℚ) / (n : ℚ)) :
    53 ≤ S.card := by
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
  have hsumE : (1 : ℚ) ≤ ∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
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
  exact prime_edges_card_ge_fifty_three_of_deg_le_ten E hE hdegE hsumE

/-! ### Part 3: 5-Leaf Weighted Row-Potential Exclusion Certificate for `P_47` (Cell `000`) -/

def p47LeafPred (b : Fin 5) (E : Finset (ℕ × ℕ)) : Prop :=
  if b = 0 then (7, 37) ∉ E ∧ (13, 19) ∉ E
  else if b = 1 then (7, 37) ∉ E ∧ (13, 19) ∈ E
  else if b = 2 then (7, 37) ∈ E ∧ (7, 19) ∉ E
  else if b = 3 then (7, 37) ∈ E ∧ (7, 19) ∈ E ∧ (11, 41) ∉ E
  else (7, 37) ∈ E ∧ (7, 19) ∈ E ∧ (11, 41) ∈ E

theorem exists_p47LeafPred_mem_univ (E : Finset (ℕ × ℕ)) :
    ∃ b ∈ (Finset.univ : Finset (Fin 5)), p47LeafPred b E := by
  by_cases h1 : (7, 37) ∈ E
  · by_cases h3 : (7, 19) ∈ E
    · by_cases h4 : (11, 41) ∈ E
      · refine ⟨4, Finset.mem_univ _, ?_⟩
        dsimp [p47LeafPred]
        exact ⟨h1, h3, h4⟩
      · refine ⟨3, Finset.mem_univ _, ?_⟩
        dsimp [p47LeafPred]
        exact ⟨h1, h3, h4⟩
    · refine ⟨2, Finset.mem_univ _, ?_⟩
      dsimp [p47LeafPred]
      exact ⟨h1, h3⟩
  · by_cases h2 : (13, 19) ∈ E
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      dsimp [p47LeafPred]
      exact ⟨h1, h2⟩
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      dsimp [p47LeafPred]
      exact ⟨h1, h2⟩

theorem p47LeafPred_unique (E : Finset (ℕ × ℕ)) (b₁ b₂ : Fin 5)
    (hb₁ : p47LeafPred b₁ E) (hb₂ : p47LeafPred b₂ E) :
    b₁ = b₂ := by
  fin_cases b₁ <;> fin_cases b₂ <;> dsimp [p47LeafPred] at hb₁ hb₂ <;> tauto

theorem edge_mem_iff_mem_graphNeighbors_of_lt
    (E : Finset (ℕ × ℕ)) (p q : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2) (hpq : p < q) :
    ((p, q) ∈ E ↔ q ∈ graphNeighbors E p) ∧
      ((p, q) ∈ E ↔ p ∈ graphNeighbors E q) := by
  have hnot_qp : (q, p) ∉ E := by
    intro hqp
    have := hE (q, p) hqp
    omega
  rw [mem_graphNeighbors_iff, mem_graphNeighbors_iff]
  simp [hnot_qp]

def p47LeafRowCompatible (b : Fin 5) (p : ℕ) (S : Finset ℕ) : Prop :=
  if b = 0 then (p = 7 → 37 ∉ S) ∧ (p = 37 → 7 ∉ S) ∧ (p = 13 → 19 ∉ S) ∧ (p = 19 → 13 ∉ S)
  else if b = 1 then (p = 7 → 37 ∉ S) ∧ (p = 37 → 7 ∉ S) ∧ (p = 13 → 19 ∈ S) ∧ (p = 19 → 13 ∈ S)
  else if b = 2 then (p = 7 → 37 ∈ S ∧ 19 ∉ S) ∧ (p = 37 → 7 ∈ S) ∧ (p = 19 → 7 ∉ S)
  else if b = 3 then
    (p = 7 → 37 ∈ S ∧ 19 ∈ S) ∧ (p = 37 → 7 ∈ S) ∧ (p = 19 → 7 ∈ S) ∧
    (p = 11 → 41 ∉ S) ∧ (p = 41 → 11 ∉ S)
  else
    (p = 7 → 37 ∈ S ∧ 19 ∈ S) ∧ (p = 37 → 7 ∈ S) ∧ (p = 19 → 7 ∈ S) ∧
    (p = 11 → 41 ∈ S) ∧ (p = 41 → 11 ∈ S)

theorem p47LeafRowCompatible_of_p47LeafPred
    (E : Finset (ℕ × ℕ)) (b : Fin 5) (p : ℕ)
    (hE : ∀ e ∈ E, e.1 < e.2) (hb : p47LeafPred b E) :
    p47LeafRowCompatible b p (graphNeighbors E p) := by
  rcases edge_mem_iff_mem_graphNeighbors_of_lt E 7 37 hE (by decide) with ⟨h7_37, h37_7⟩
  rcases edge_mem_iff_mem_graphNeighbors_of_lt E 13 19 hE (by decide) with ⟨h13_19, h19_13⟩
  rcases edge_mem_iff_mem_graphNeighbors_of_lt E 7 19 hE (by decide) with ⟨h7_19, h19_7⟩
  rcases edge_mem_iff_mem_graphNeighbors_of_lt E 11 41 hE (by decide) with ⟨h11_41, h41_11⟩
  fin_cases b <;> dsimp [p47LeafPred, p47LeafRowCompatible] at hb ⊢
  · refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
    · subst hp; exact h7_37.not.mp hb.1
    · subst hp; exact h37_7.not.mp hb.1
    · subst hp; exact h13_19.not.mp hb.2
    · subst hp; exact h19_13.not.mp hb.2
  · refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
    · subst hp; exact h7_37.not.mp hb.1
    · subst hp; exact h37_7.not.mp hb.1
    · subst hp; exact h13_19.mp hb.2
    · subst hp; exact h19_13.mp hb.2
  · refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
    · subst hp; exact ⟨h7_37.mp hb.1, h7_19.not.mp hb.2⟩
    · subst hp; exact h37_7.mp hb.1
    · subst hp; exact h19_7.not.mp hb.2
  · refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
    · subst hp; exact ⟨h7_37.mp hb.1, h7_19.mp hb.2.1⟩
    · subst hp; exact h37_7.mp hb.1
    · subst hp; exact h19_7.mp hb.2.1
    · subst hp; exact h11_41.not.mp hb.2.2
    · subst hp; exact h41_11.not.mp hb.2.2
  · refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
    · subst hp; exact ⟨h7_37.mp hb.1, h7_19.mp hb.2.1⟩
    · subst hp; exact h37_7.mp hb.1
    · subst hp; exact h19_7.mp hb.2.1
    · subst hp; exact h11_41.mp hb.2.2
    · subst hp; exact h41_11.mp hb.2.2

def p47CommonDenom : ℚ := 614889782588491410000000000

def p47LeafRowMaxNum (b : Fin 5) (p : ℕ) : ℤ :=
  if b = 0 then
    if p = 2 then 173376488947317752208724597
    else if p = 3 then 135516782019928688949334755
    else if p = 5 then 87311895826443663740497126
    else if p = 7 then 65970548320816587721708778
    else if p = 11 then 43002130662617492858926423
    else if p = 13 then 35585746298700937201895006
    else if p = 17 then 25339523955291539814481777
    else if p = 19 then 22445505311386292087312711
    else if p = 23 then 12680137498485181491955705
    else if p = 29 then 4561400678182938961478406
    else if p = 31 then 5324415467001094256011538
    else if p = 37 then 2197260082441769730620081
    else if p = 41 then 442233409918085621005170
    else if p = 43 then 486734854222430209534710
    else if p = 47 then 339323805389578385161038
    else 0
  else if b = 1 then
    if p = 2 then 174788275150273189379894905
    else if p = 3 then 135824132159949946204146645
    else if p = 5 then 87239029105667182961348125
    else if p = 7 then 67055728869432968572916351
    else if p = 11 then 43520815896623797562202361
    else if p = 13 then -9681022436149090
    else if p = 17 then 23461838454588698500178959
    else if p = 19 then 58632758346453513553398803
    else if p = 23 then 11536691597205952674594328
    else if p = 29 then 4886696817425820689080857
    else if p = 31 then 4299851351593595323376162
    else if p = 37 then 1489897150592042506317003
    else if p = 41 then 861627239785259103673671
    else if p = 43 then 472238096938412112452793
    else if p = 47 then 534374690434508747142033
    else 0
  else if b = 2 then
    if p = 2 then 174671876183753078488977604
    else if p = 3 then 135985124359587817786247766
    else if p = 5 then 87923254782475026545476840
    else if p = 7 then 72382898979187139
    else if p = 11 then 43665340021546244395152748
    else if p = 13 then 37137729526888777393821188
    else if p = 17 then 25211371066965242216030908
    else if p = 19 then 17385982217751022321567142
    else if p = 23 then 14221442901923486944997659
    else if p = 29 then 4545535620556807781332428
    else if p = 31 then 5047462028620036552819208
    else if p = 37 then 65975667815327895905839691
    else if p = 41 then 1168007837607228124153647
    else if p = 43 then 504443953313247148051928
    else if p = 47 then 537991500554502138636492
    else 0
  else if b = 3 then
    if p = 2 then 172846439197371690489510757
    else if p = 3 then 136604311883071196001726879
    else if p = 5 then 88472252586940322130050014
    else if p = 7 then 7678758415392407
    else if p = 11 then 43573603096718283707719744
    else if p = 13 then 35792176630039166710238840
    else if p = 17 then 24492595409652512146914844
    else if p = 19 then 87976103495417924190051383
    else if p = 23 then 12903383304650143248790363
    else if p = 29 then 3812313280681696022625120
    else if p = 31 then 4145762476423437936932327
    else if p = 37 then 2269413833151858248010287
    else if p = 41 then 939520534276900727298576
    else if p = 43 then 425789021816468617237917
    else if p = 47 then 594345654984614867802468
    else 0
  else
    if p = 2 then 172994778405950207617414489
    else if p = 3 then 136204361059654857130217046
    else if p = 5 then 88817291751135862706555758
    else if p = 7 then 66540441518606612454127958
    else if p = 11 then 66454459611942391
    else if p = 13 then 34789518004223265665314907
    else if p = 17 then 24098081044480299341760352
    else if p = 19 then 22540614003837189397923521
    else if p = 23 then 13378328026700072982844675
    else if p = 29 then 3401269877949807417026970
    else if p = 31 then 3473531331626591537040200
    else if p = 37 then 2695848023784391843334372
    else if p = 41 then 44263806194726415271869960
    else if p = 43 then 989233854208009710608385
    else if p = 47 then 548190067925986499281521
    else 0

def p47LeafRowMax (b : Fin 5) (p : ℕ) : ℚ :=
  (p47LeafRowMaxNum b p : ℚ) / p47CommonDenom

theorem p47LeafRowMax_sum_lt_one (b : Fin 5) :
    (∑ p ∈ primes47, p47LeafRowMax b p) ≤
      770486228587562623383837 / 770538574672295000000000 ∧
    (∑ p ∈ primes47, p47LeafRowMax b p) < 1 := by
  fin_cases b <;> decide +kernel

theorem p47_five_leaf_exclusion_via_branch_cover
    (φ : Fin 5 → ℕ → ℕ → ℚ) (E : Finset (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ primes47 ∧ e.2 ∈ primes47)
    (hskew : ∀ b ∈ (Finset.univ : Finset (Fin 5)), ∀ e ∈ E, φ b e.1 e.2 + φ b e.2 e.1 = 0)
    (hbranch : ∀ b ∈ (Finset.univ : Finset (Fin 5)), p47LeafPred b E →
      ∀ p ∈ primes47, rowPotential (φ b) p (graphNeighbors E p) ≤ p47LeafRowMax b p) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) ≠ 1 := by
  exact ne_one_of_branch_cover_row_maxima_lt_one
    (Finset.univ : Finset (Fin 5)) p47LeafPred φ p47LeafRowMax E primes47
    hE hend (exists_p47LeafPred_mem_univ E) hskew hbranch
    (fun b _ => (p47LeafRowMax_sum_lt_one b).2)

theorem p47_five_leaf_exclusion_of_local_row_bounds
    (φ : Fin 5 → ℕ → ℕ → ℚ) (E : Finset (ℕ × ℕ)) (d : ℕ) (hd : d ≤ 10)
    (hE : ∀ e ∈ E, e.1 < e.2)
    (hend : ∀ e ∈ E, e.1 ∈ primes47 ∧ e.2 ∈ primes47)
    (hdeg : ∀ p ∈ primes47, incidenceDegree E p ≤ d)
    (hadm : ∀ p ∈ primes47, PrimeRowAdmissible p (graphNeighbors E p))
    (hskew : ∀ b ∈ (Finset.univ : Finset (Fin 5)), ∀ e ∈ E, φ b e.1 e.2 + φ b e.2 e.1 = 0)
    (hlocal : ∀ b : Fin 5, ∀ p ∈ primes47, ∀ S : Finset ℕ,
      S ⊆ primes47.erase p → S.card ≤ 10 → PrimeRowAdmissible p S →
      p47LeafRowCompatible b p S → rowPotential (φ b) p S ≤ p47LeafRowMax b p) :
    (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) ≠ 1 := by
  apply p47_five_leaf_exclusion_via_branch_cover φ E hE hend hskew
  intro b _ hb p hp
  apply hlocal b p hp (graphNeighbors E p)
  · exact graphNeighbors_subset_vertexSet_erase E primes47 hE hend p
  · rw [card_graphNeighbors_eq_incidenceDegree E hE p]
    exact le_trans (hdeg p hp) hd
  · exact hadm p hp
  · exact p47LeafRowCompatible_of_p47LeafPred E b p hE hb

/-! ### Part 4: 68-Edge Multi-Tail Witnesses (`011, 101, 110, 111`) and 7-Cell Sharpness on `P_61` -/

def witnessEdgesFiftyNineSixtyOne : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37),
   (5, 7), (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31),
   (7, 11), (7, 13), (7, 17), (7, 19), (7, 29), (7, 31), (7, 43),
   (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 31), (13, 41), (13, 43),
   (17, 23), (17, 29), (17, 59), (17, 61),
   (19, 23), (19, 29), (19, 31), (19, 41),
   (23, 29), (23, 31), (23, 47), (23, 59),
   (29, 31), (29, 37), (29, 59), (29, 61),
   (31, 37), (37, 43), (37, 47), (41, 43), (41, 59), (41, 61), (43, 47)}

def witnessEdgesFiftyThreeSixtyOne : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37),
   (5, 7), (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31),
   (7, 11), (7, 13), (7, 17), (7, 19), (7, 23), (7, 29), (7, 53),
   (11, 13), (11, 17), (11, 19), (11, 23), (11, 29), (11, 47),
   (13, 17), (13, 19), (13, 31), (13, 41), (13, 43),
   (17, 23), (17, 37), (17, 41), (17, 53),
   (19, 23), (19, 29), (19, 31), (19, 41),
   (23, 31), (23, 47), (23, 53),
   (29, 31), (29, 37), (29, 61),
   (31, 37), (31, 47), (31, 53),
   (37, 47), (37, 53), (41, 43), (43, 61), (47, 53), (53, 61)}

def witnessEdgesFiftyThreeFiftyNine : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37),
   (5, 7), (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31),
   (7, 11), (7, 13), (7, 17), (7, 19), (7, 23), (7, 29), (7, 53),
   (11, 13), (11, 17), (11, 19), (11, 23), (11, 29), (11, 47),
   (13, 17), (13, 19), (13, 23), (13, 37), (13, 59),
   (17, 29), (17, 37), (17, 53), (17, 59),
   (19, 23), (19, 29), (19, 31), (19, 41),
   (23, 31), (23, 37), (23, 41),
   (29, 31), (29, 41), (29, 47),
   (31, 37), (31, 41), (31, 59),
   (37, 53), (41, 47), (41, 59), (47, 53), (47, 59), (53, 59)}

def witnessEdgesAllThreeTailPrimes : Finset (ℕ × ℕ) :=
  {(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (2, 17), (2, 19), (2, 23), (2, 29), (2, 31),
   (3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19), (3, 23), (3, 31), (3, 37),
   (5, 7), (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29), (5, 31),
   (7, 11), (7, 13), (7, 17), (7, 19), (7, 23), (7, 37), (7, 41),
   (11, 13), (11, 17), (11, 19), (11, 23), (11, 31), (11, 41),
   (13, 17), (13, 19), (13, 31), (13, 41), (13, 43),
   (17, 23), (17, 37), (17, 43), (17, 61),
   (19, 23), (19, 29), (19, 31), (19, 41),
   (23, 29), (23, 53),
   (29, 31), (29, 37), (29, 41), (29, 43), (29, 53), (29, 61),
   (31, 41), (31, 53), (31, 59),
   (37, 41), (37, 59), (41, 61), (43, 59)}

theorem witnessEdgesFiftyNineSixtyOne_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdgesFiftyNineSixtyOne,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdgesFiftyNineSixtyOne, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdgesFiftyNineSixtyOne.card = 68 ∧
      incidenceDegree witnessEdgesFiftyNineSixtyOne 53 = 0 ∧
      incidenceDegree witnessEdgesFiftyNineSixtyOne 59 = 4 ∧
      incidenceDegree witnessEdgesFiftyNineSixtyOne 61 = 3 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdgesFiftyNineSixtyOne p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdgesFiftyNineSixtyOne p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdgesFiftyNineSixtyOne (primorial47 * 59 * 61)
    (by decide) (by decide) (by decide)

theorem witnessEdgesFiftyThreeSixtyOne_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdgesFiftyThreeSixtyOne,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdgesFiftyThreeSixtyOne, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdgesFiftyThreeSixtyOne.card = 68 ∧
      incidenceDegree witnessEdgesFiftyThreeSixtyOne 53 = 7 ∧
      incidenceDegree witnessEdgesFiftyThreeSixtyOne 59 = 0 ∧
      incidenceDegree witnessEdgesFiftyThreeSixtyOne 61 = 3 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdgesFiftyThreeSixtyOne p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdgesFiftyThreeSixtyOne p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdgesFiftyThreeSixtyOne (primorial47 * 53 * 61)
    (by decide) (by decide) (by decide)

theorem witnessEdgesFiftyThreeFiftyNine_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdgesFiftyThreeFiftyNine,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdgesFiftyThreeFiftyNine, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdgesFiftyThreeFiftyNine.card = 68 ∧
      incidenceDegree witnessEdgesFiftyThreeFiftyNine 53 = 5 ∧
      incidenceDegree witnessEdgesFiftyThreeFiftyNine 59 = 6 ∧
      incidenceDegree witnessEdgesFiftyThreeFiftyNine 61 = 0 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdgesFiftyThreeFiftyNine p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdgesFiftyThreeFiftyNine p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdgesFiftyThreeFiftyNine (primorial47 * 53 * 59)
    (by decide) (by decide) (by decide)

theorem witnessEdgesAllThreeTailPrimes_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    (∀ e ∈ witnessEdgesAllThreeTailPrimes,
      e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ witnessEdgesAllThreeTailPrimes, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      witnessEdgesAllThreeTailPrimes.card = 68 ∧
      incidenceDegree witnessEdgesAllThreeTailPrimes 53 = 3 ∧
      incidenceDegree witnessEdgesAllThreeTailPrimes 59 = 3 ∧
      incidenceDegree witnessEdgesAllThreeTailPrimes 61 = 3 ∧
      ∀ p ∈ primes61, incidenceDegree witnessEdgesAllThreeTailPrimes p ≤ d := by
  have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdgesAllThreeTailPrimes p ≤ 10 := by decide
  refine ⟨by decide, ?_, by decide, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  exact sum_edges_inv_eq_one_of_cleared_nat_sum witnessEdgesAllThreeTailPrimes (primorial47 * 53 * 59 * 61)
    (by decide) (by decide) (by decide)

def witnessSemiprimesAllThreeTailPrimes : Finset ℕ :=
  witnessEdgesAllThreeTailPrimes.image (fun e => e.1 * e.2)

theorem witnessSemiprimesAllThreeTailPrimes_valid_and_sum_eq_one (d : ℕ) (hd : 10 ≤ d) :
    witnessSemiprimesAllThreeTailPrimes.card = 68 ∧
      (∀ n ∈ witnessSemiprimesAllThreeTailPrimes,
        ArithmeticFunction.cardDistinctFactors n = 2 ∧ ArithmeticFunction.cardFactors n = 2) ∧
      (∀ p : ℕ, p.Prime → (witnessSemiprimesAllThreeTailPrimes.filter fun n => p ∣ n).card ≤ d) ∧
      (∑ n ∈ witnessSemiprimesAllThreeTailPrimes, (1 : ℚ) / (n : ℚ)) = 1 := by
  have hw := witnessEdgesAllThreeTailPrimes_valid_and_sum_eq_one d hd
  have hE : ∀ e ∈ witnessEdgesAllThreeTailPrimes, e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2 :=
    fun e he => (hw.1 e he).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold witnessSemiprimesAllThreeTailPrimes
    rw [Finset.card_image_of_injOn
      (Erdos306.Representation.product_injOn_prime_edges witnessEdgesAllThreeTailPrimes hE)]
    exact hw.2.2.1
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨e, he, rfl⟩
    rcases hE e he with ⟨hp, hq, hlt⟩
    exact Erdos306.Representation.factor_counts_of_distinct_primes e.1 e.2 hp hq hlt
  · intro p hp
    unfold witnessSemiprimesAllThreeTailPrimes
    rw [← Erdos306.Representation.degree_eq_divisible_denominators witnessEdgesAllThreeTailPrimes hE p hp]
    change incidenceDegree witnessEdgesAllThreeTailPrimes p ≤ d
    by_cases hp61 : p ∈ primes61
    · exact hw.2.2.2.2.2.2 p hp61
    · have h1 : (witnessEdgesAllThreeTailPrimes.filter fun e => e.1 = p) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he hfst
        exact hp61 (hfst ▸ (hw.1 e he).1)
      have h2 : (witnessEdgesAllThreeTailPrimes.filter fun e => e.2 = p) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he hsnd
        exact hp61 (hsnd ▸ (hw.1 e he).2.1)
      simp [incidenceDegree, h1, h2]
  · unfold witnessSemiprimesAllThreeTailPrimes
    rw [Erdos306.Representation.reciprocal_sum_image_prime_edges witnessEdgesAllThreeTailPrimes hE]
    have hcast :
        (∑ e ∈ witnessEdgesAllThreeTailPrimes, (1 : ℚ) / (e.1 * e.2 : ℕ)) =
          ∑ e ∈ witnessEdgesAllThreeTailPrimes, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro e _
      push_cast
      rfl
    rw [hcast]
    exact hw.2.1

def cellWitness68 (b53 b59 b61 : Bool) : Finset (ℕ × ℕ) :=
  match b53, b59, b61 with
  | false, false, true  => witnessEdgesSixtyOne
  | false, true,  false => witnessEdgesFiftyNine
  | false, true,  true  => witnessEdgesFiftyNineSixtyOne
  | true,  false, false => witnessEdgesFiftyThree
  | true,  false, true  => witnessEdgesFiftyThreeSixtyOne
  | true,  true,  false => witnessEdgesFiftyThreeFiftyNine
  | _,     _,     _     => witnessEdgesAllThreeTailPrimes

theorem exists_card_sixty_eight_witness_in_every_active_tail_cell
    (b53 b59 b61 : Bool) (d : ℕ)
    (hact : (b53, b59, b61) ≠ (false, false, false)) (hd : 10 ≤ d) :
    let E := cellWitness68 b53 b59 b61
    (∀ e ∈ E, e.1 ∈ primes61 ∧ e.2 ∈ primes61 ∧ e.1.Prime ∧ e.2.Prime ∧ e.1 < e.2) ∧
      (∑ e ∈ E, (1 : ℚ) / ((e.1 : ℚ) * (e.2 : ℚ))) = 1 ∧
      E.card = 68 ∧
      (decide (incidenceDegree E 53 ≠ 0) = b53) ∧
      (decide (incidenceDegree E 59 ≠ 0) = b59) ∧
      (decide (incidenceDegree E 61 ≠ 0) = b61) ∧
      ∀ p ∈ primes61, incidenceDegree E p ≤ d := by
  cases b53 <;> cases b59 <;> cases b61
  · exact False.elim (hact rfl)
  · have h := witnessEdgesSixtyOne_valid_and_sum_eq_one d hd
    have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdgesSixtyOne p ≤ 10 := by decide
    refine ⟨by decide, h.2.1, h.2.2.1, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  · have h := witnessEdgesFiftyNine_valid_and_sum_eq_one d hd
    have hdeg : ∀ p ∈ primes61, incidenceDegree witnessEdgesFiftyNine p ≤ 10 := by decide
    refine ⟨by decide, h.2.1, h.2.2.1, by decide, by decide, by decide, fun p hp => le_trans (hdeg p hp) hd⟩
  · have h := witnessEdgesFiftyNineSixtyOne_valid_and_sum_eq_one d hd
    exact ⟨h.1, h.2.1, h.2.2.1, by decide, by decide, by decide, h.2.2.2.2.2.2⟩
  · have h := witnessEdgesFiftyThree_sum_eq_one_and_deg_le d hd
    refine ⟨by decide, h.1, h.2.1, by decide, by decide, by decide, fun p _ => h.2.2 p⟩
  · have h := witnessEdgesFiftyThreeSixtyOne_valid_and_sum_eq_one d hd
    exact ⟨h.1, h.2.1, h.2.2.1, by decide, by decide, by decide, h.2.2.2.2.2.2⟩
  · have h := witnessEdgesFiftyThreeFiftyNine_valid_and_sum_eq_one d hd
    exact ⟨h.1, h.2.1, h.2.2.1, by decide, by decide, by decide, h.2.2.2.2.2.2⟩
  · have h := witnessEdgesAllThreeTailPrimes_valid_and_sum_eq_one d hd
    exact ⟨h.1, h.2.1, h.2.2.1, by decide, by decide, by decide, h.2.2.2.2.2.2⟩

end Erdos306.Core.PrimeResidueAndRowPotential

