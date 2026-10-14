module

/-
Copyright 2025 The Formal Conjectures Authors.
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

open Filter

namespace Erdos494

/-!
## The Selfridge–Straus sum-multiset problem

For a finite set `A ⊂ ℂ`, `sumMultiset A k` records the sums of all `k`-element subsets as a
multiset. The theorems below show that this multiset determines `A` in the fixed-cardinality
cases established by Selfridge and Straus (1958): `k = 2` when the cardinality is not a power
of two, and `k = 3` when the cardinality exceeds six and is not 27 or 486.
-/

/--
For a finite set $A \subset \mathbb{C}$ and $k \ge 1$, define $A_k$ as the multiset consisting of
all sums of $k$ distinct elements of $A$.
-/
noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

open Finset in
/-- Newton's identities evaluated at the elements of a finset. -/
lemma e494_newton (A : Finset ℂ) (k : ℕ) :
    (k : ℂ) * A.val.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * A.val.esymm a.1 * ∑ x ∈ A, x ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval (fun x : A => (x : ℂ))) (MvPolynomial.mul_esymm_eq_sum A ℂ k)
  have hval : (Finset.univ : Finset A).val.map (fun x : A => (x : ℂ)) = A.val := by
    rw [Finset.univ_eq_attach, Finset.attach_val]; exact Multiset.attach_map_val _
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, hval] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
  exact Finset.sum_coe_sort A (fun x => x ^ a.2)

open Finset in
/-- Equal power sums give equal elementary symmetric functions. -/
lemma e494_esymm_eq (A B : Finset ℂ) (hp : ∀ m, ∑ x ∈ A, x ^ m = ∑ x ∈ B, x ^ m) :
    ∀ k, A.val.esymm k = B.val.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm]
    · have hA := e494_newton A k
      have hB := e494_newton B k
      have hrhs : ∑ a ∈ antidiagonal k with a.1 < k, (-1 : ℂ) ^ a.1 * A.val.esymm a.1 * ∑ x ∈ A, x ^ a.2
          = ∑ a ∈ antidiagonal k with a.1 < k, (-1 : ℂ) ^ a.1 * B.val.esymm a.1 * ∑ x ∈ B, x ^ a.2 := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_filter] at ha
        rw [ih a.1 ha.2, hp a.2]
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [hA, hB, hrhs]

open Finset in
/-- The same cardinality and elementary symmetric functions imply equal finsets. -/
lemma e494_eq_of_esymm (A B : Finset ℂ) (hc : A.card = B.card)
    (he : ∀ k, A.val.esymm k = B.val.esymm k) : A = B := by
  have hpoly : (A.val.map fun t => Polynomial.X - Polynomial.C t).prod =
      (B.val.map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    have : Multiset.card A.val = Multiset.card B.val := hc
    rw [this]
    simp only [he]
  have := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  exact Finset.val_inj.mp this

open Finset in
/-- Split the sum over ordered distinct pairs into two copies of the unordered-pair sum. -/
lemma e494_offDiag (A : Finset ℂ) (m : ℕ) :
    ∑ x ∈ A.offDiag, (x.1 + x.2) ^ m = 2 * ∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m := by
  classical
  have hmaps : ∀ x ∈ A.offDiag, ({x.1, x.2} : Finset ℂ) ∈ A.powersetCard 2 := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hx
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair h3⟩
    intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  obtain ⟨hyA, hy2⟩ := Finset.mem_powersetCard.mp hy
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hy2
  have haA : a ∈ A := hyA (by simp)
  have hbA : b ∈ A := hyA (by simp)
  have hfib : A.offDiag.filter (fun x => ({x.1, x.2} : Finset ℂ) = {a, b}) = {(a, b), (b, a)} := by
    ext ⟨x1, x2⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, _, hne⟩, heq⟩
      have h1 : x1 ∈ ({a, b} : Finset ℂ) := heq ▸ (by simp)
      have h2 : x2 ∈ ({a, b} : Finset ℂ) := heq ▸ (by simp)
      simp at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact absurd rfl hne
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
      · exact absurd rfl hne
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨haA, hbA, hab⟩, rfl⟩
      · exact ⟨⟨hbA, haA, Ne.symm hab⟩, Finset.pair_comm _ _⟩
  rw [hfib, Finset.sum_pair (by simp [hab]), Finset.sum_pair hab]
  simp only
  ring

open Finset in
/-- Relate powers of unordered pair sums to products of power sums. -/
lemma e494_pair_pow (A : Finset ℂ) (m : ℕ) :
    2 * ∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m + 2 ^ m * ∑ x ∈ A, x ^ m =
      ∑ l ∈ range (m + 1), (m.choose l : ℂ) * (∑ x ∈ A, x ^ l) * (∑ x ∈ A, x ^ (m - l)) := by
  classical
  have hfull : ∑ x ∈ A ×ˢ A, (x.1 + x.2) ^ m =
      ∑ l ∈ range (m + 1), (m.choose l : ℂ) * (∑ x ∈ A, x ^ l) * (∑ x ∈ A, x ^ (m - l)) := by
    rw [Finset.sum_product]
    simp_rw [add_pow]
    calc ∑ a ∈ A, ∑ b ∈ A, ∑ l ∈ range (m + 1), a ^ l * b ^ (m - l) * (m.choose l : ℂ)
        = ∑ a ∈ A, ∑ l ∈ range (m + 1), ∑ b ∈ A, a ^ l * b ^ (m - l) * (m.choose l : ℂ) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ l ∈ range (m + 1), ∑ a ∈ A, ∑ b ∈ A, a ^ l * b ^ (m - l) * (m.choose l : ℂ) :=
          Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          ring
  have hdiag : ∑ x ∈ A.diag, (x.1 + x.2) ^ m = 2 ^ m * ∑ x ∈ A, x ^ m := by
    rw [Finset.diag, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [Function.Embedding.coeFn_mk, Function.diag]
    ring
  rw [← hfull, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag A),
    hdiag, e494_offDiag]
  ring

open Finset in
/-- The power sums of pair sums are determined by `sumMultiset A 2`. -/
lemma e494_T (A : Finset ℂ) (m : ℕ) :
    ∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m = ((sumMultiset A 2).map (· ^ m)).sum := by
  unfold sumMultiset
  rw [Multiset.map_map]
  rfl

open Finset in
/-- If `n` is not a power of two, equal pair-sum multisets give equal power sums. -/
lemma e494_psum_eq (A B : Finset ℂ) (n : ℕ) (hA : A.card = n) (hB : B.card = n)
    (hn : ∀ l : ℕ, n ≠ 2 ^ l) (h : sumMultiset A 2 = sumMultiset B 2) :
    ∀ m, ∑ x ∈ A, x ^ m = ∑ x ∈ B, x ^ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hA, hB]
    · have hT : ∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m = ∑ s ∈ B.powersetCard 2, (∑ x ∈ s, x) ^ m := by
        rw [e494_T, e494_T, h]
      have h0A : ∑ x ∈ A, x ^ 0 = (n : ℂ) := by simp [hA]
      have h0B : ∑ x ∈ B, x ^ 0 = (n : ℂ) := by simp [hB]
      set pA := ∑ x ∈ A, x ^ m
      set pB := ∑ x ∈ B, x ^ m
      have hD : ∑ l ∈ range (m + 1), ((m.choose l : ℂ) * (∑ x ∈ A, x ^ l) * (∑ x ∈ A, x ^ (m - l))
          - (m.choose l : ℂ) * (∑ x ∈ B, x ^ l) * (∑ x ∈ B, x ^ (m - l))) = 2 * n * (pA - pB) := by
        rw [Finset.sum_eq_add 0 m (by omega)]
        · simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.choose_self, Nat.sub_self,
            Nat.cast_one, one_mul, pow_zero]
          simp only [pA, pB, Finset.sum_const, nsmul_eq_mul, mul_one, hA, hB]
          ring
        · intro c hc hne
          have hc' := Finset.mem_range.mp hc
          obtain ⟨hne0, hnem⟩ := hne
          rw [ih c (by omega), ih (m - c) (by omega)]
          ring
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      have hPA := e494_pair_pow A m
      have hPB := e494_pair_pow B m
      rw [Finset.sum_sub_distrib] at hD
      have key : ((2 : ℂ) ^ m - 2 * n) * (pA - pB) = 0 := by
        have : 2 * (∑ s ∈ A.powersetCard 2, (∑ x ∈ s, x) ^ m) + 2 ^ m * pA
            - (2 * (∑ s ∈ B.powersetCard 2, (∑ x ∈ s, x) ^ m) + 2 ^ m * pB) = 2 * n * (pA - pB) := by
          rw [hPA, hPB]; exact hD
        rw [hT] at this
        linear_combination this
      have hne : (2 : ℂ) ^ m - 2 * n ≠ 0 := by
        intro h0
        have h1 : ((2 ^ m : ℕ) : ℂ) = ((2 * n : ℕ) : ℂ) := by push_cast; linear_combination h0
        have h2 : 2 ^ m = 2 * n := by exact_mod_cast h1
        apply hn (m - 1)
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        rw [pow_succ] at h2
        simp only [Nat.add_sub_cancel]
        omega
      have := (mul_eq_zero.mp key).resolve_left hne
      exact sub_eq_zero.mp this

/--
Selfridge and Straus [SeSt58] showed that the conjecture is true when $k = 2$ and
$|A| \ne 2^l$ for $l \ge 0$.
They also gave counterexamples when $k = 2$ and $|A| = 2^l$.
-/
theorem erdos_494.variants.k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494Unique 2 card := by
  intro card hcard A B hA hB h
  exact e494_eq_of_esymm A B (hA.trans hB.symm)
    (e494_esymm_eq A B (e494_psum_eq A B card hA hB hcard h))

/-!
## The three-sum case
-/

lemma e494_bound (m : ℕ) (hm : 14 ≤ m) : 3 * m * (2 ^ m + 1) < 3 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [show m + 1 - 1 = (m - 1) + 1 by omega, pow_succ, pow_succ]
    nlinarith [Nat.one_le_two_pow (n := m)]

open Finset in
lemma e494_div_form (n a : ℕ) (h : n ∣ 2 * 3 ^ a) : ∃ e u, e ≤ 1 ∧ u ≤ a ∧ n = 2 ^ e * 3 ^ u := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨u, hu, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hz
  rcases (Nat.dvd_prime Nat.prime_two).mp hy with rfl | rfl
  · exact ⟨0, u, by omega, hu, by simp⟩
  · exact ⟨1, u, le_rfl, hu, by simp⟩

open Finset in
lemma e494_v3 (m : ℕ) (hm : 1 ≤ m) (w : ℕ) (hw : 3 ^ w ∣ 2 ^ m + 1) : 3 ^ w ≤ 3 * m := by
  rcases Nat.even_or_odd m with he | ho
  · have h3 : ¬ 3 ∣ 2 ^ m + 1 := by
      obtain ⟨t, rfl⟩ := he
      rw [← two_mul, pow_mul]; norm_num
      intro h; have := Nat.pow_mod 4 t 3; norm_num at this; omega
    rcases Nat.eq_zero_or_pos w with rfl | hw0
    · simp; omega
    · exact absurd ((pow_dvd_pow 3 hw0).trans hw |> fun h => by simpa using h) h3
  · have hv : padicValNat 3 (2 ^ m + 1) = padicValNat 3 3 + padicValNat 3 m := by
      have := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by norm_num) (by norm_num)
        (by norm_num) ho
      simpa using this
    have hle : w ≤ padicValNat 3 (2 ^ m + 1) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact (padicValNat_dvd_iff_le (by positivity)).mp hw
    rw [hv, padicValNat_self] at hle
    have hm3 : 3 ^ padicValNat 3 m ≤ m := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    calc 3 ^ w ≤ 3 ^ (1 + padicValNat 3 m) := Nat.pow_le_pow_right (by norm_num) hle
      _ = 3 * 3 ^ padicValNat 3 m := by rw [pow_add, pow_one]
      _ ≤ 3 * m := by omega

set_option maxRecDepth 100000 in
open Finset in
lemma e494_small : ∀ m ∈ Finset.range 14, ∀ e ∈ Finset.range 2, ∀ u ∈ Finset.range 14,
    1 ≤ m → 2 ^ e * 3 ^ u ≤ 2 ^ m + 1 →
    2 ^ e * 3 ^ u * (2 ^ m + 1 - 2 ^ e * 3 ^ u) = 2 * 3 ^ (m - 1) →
    2 ^ e * 3 ^ u ≤ 6 ∨ 2 ^ e * 3 ^ u = 27 ∨ 2 ^ e * 3 ^ u = 486 := by decide

open Finset in
lemma e494_nt (n m : ℕ) (hm : 1 ≤ m) (h : 3 * n ^ 2 + 2 * 3 ^ m = 3 * n * (2 ^ m + 1)) :
    n ≤ 6 ∨ n = 27 ∨ n = 486 := by
  have hnle : n ≤ 2 ^ m + 1 := by
    by_contra hc; push Not at hc
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hc
    have h1 : 3 * n * (2 ^ m + 1) < 3 * n * n :=
      Nat.mul_lt_mul_of_pos_left hc (by omega)
    have h2 : 0 < 2 * 3 ^ m := by positivity
    rw [sq] at h
    nlinarith [h1, h2, h]
  set k := 2 ^ m + 1 - n with hk
  have hnk : n + k = 2 ^ m + 1 := by omega
  have hprod : n * k = 2 * 3 ^ (m - 1) := by
    have h1 : 3 * (n * k) = 3 * (2 * 3 ^ (m - 1)) := by
      have : 3 * n * (2 ^ m + 1) = 3 * n ^ 2 + 3 * (n * k) := by rw [← hnk]; ring
      have h3m : 3 ^ m = 3 * 3 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    omega
  obtain ⟨e, u, he, hu, hn⟩ := e494_div_form n (m - 1) ⟨k, hprod.symm⟩
  obtain ⟨e', v, he', hv, hk'⟩ := e494_div_form k (m - 1) ⟨n, by rw [← hprod]; ring⟩
  -- u + v = m - 1
  have huv : u + v = m - 1 := by
    rw [hn, hk'] at hprod
    have : 2 ^ (e + e') * 3 ^ (u + v) = 2 ^ 1 * 3 ^ (m - 1) := by rw [pow_add, pow_add]; linarith
    have h2 := congrArg (padicValNat 3) this
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) (by positivity),
      padicValNat.prime_pow, padicValNat.prime_pow] at h2
    have h0 : ∀ t, padicValNat 3 (2 ^ t) = 0 := fun t =>
      padicValNat.eq_zero_of_not_dvd (fun hd => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.prime_three.dvd_of_dvd_pow hd); omega)
    rw [h0, h0] at h2; omega
  -- bound m
  have hmle : m < 14 := by
    by_contra hc; push Not at hc
    set w := min u v
    have hw : 3 ^ w ∣ 2 ^ m + 1 := by
      rw [← hnk]
      apply dvd_add
      · rw [hn]; exact (pow_dvd_pow 3 (min_le_left u v)).mul_left _
      · rw [hk']; exact (pow_dvd_pow 3 (min_le_right u v)).mul_left _
    have h3w := e494_v3 m hm w hw
    have hmax : 3 ^ (m - 1 - w) ≤ 2 ^ m + 1 := by
      rcases le_total u v with h | h
      · have : m - 1 - w = v := by simp [w, h]; omega
        rw [this, ← hnk]
        have : 3 ^ v ≤ k := by rw [hk']; exact Nat.le_mul_of_pos_left _ (by positivity)
        omega
      · have : m - 1 - w = u := by simp [w, h]; omega
        rw [this, ← hnk]
        have : 3 ^ u ≤ n := by rw [hn]; exact Nat.le_mul_of_pos_left _ (by positivity)
        omega
    have hw' : w ≤ m - 1 := by omega
    have : 3 ^ (m - 1) ≤ 3 * m * (2 ^ m + 1) := by
      calc 3 ^ (m - 1) = 3 ^ w * 3 ^ (m - 1 - w) := by rw [← pow_add]; congr 1; omega
        _ ≤ (3 * m) * (2 ^ m + 1) := Nat.mul_le_mul h3w hmax
    have := e494_bound m hc
    omega
  have hu14 : u < 14 := by omega
  have hnle' : 2 ^ e * 3 ^ u ≤ 2 ^ m + 1 := hn ▸ hnle
  have hprod' : 2 ^ e * 3 ^ u * (2 ^ m + 1 - 2 ^ e * 3 ^ u) = 2 * 3 ^ (m - 1) := by
    rw [← hn]; exact hprod
  have := e494_small m (Finset.mem_range.mpr hmle) e (Finset.mem_range.mpr (by omega)) u
    (Finset.mem_range.mpr hu14) hm hnle' hprod'
  rw [← hn] at this
  exact this


open Finset in
/-- Split the sum of a function of ordered distinct pairs into two unordered-pair copies. -/
lemma e494_offDiag_g (A : Finset ℂ) (g : Finset ℂ → ℂ) :
    ∑ x ∈ A.offDiag, g {x.1, x.2} = 2 * ∑ s ∈ A.powersetCard 2, g s := by
  classical
  have hmaps : ∀ x ∈ A.offDiag, ({x.1, x.2} : Finset ℂ) ∈ A.powersetCard 2 := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hx
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair h3⟩
    intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  obtain ⟨hyA, hy2⟩ := Finset.mem_powersetCard.mp hy
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hy2
  have haA : a ∈ A := hyA (by simp)
  have hbA : b ∈ A := hyA (by simp)
  have hfib : A.offDiag.filter (fun x => ({x.1, x.2} : Finset ℂ) = {a, b}) = {(a, b), (b, a)} := by
    ext ⟨x1, x2⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, _, hne⟩, heq⟩
      have h1 : x1 ∈ ({a, b} : Finset ℂ) := heq ▸ (by simp)
      have h2 : x2 ∈ ({a, b} : Finset ℂ) := heq ▸ (by simp)
      simp at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact absurd rfl hne
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
      · exact absurd rfl hne
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨haA, hbA, hab⟩, rfl⟩
      · exact ⟨⟨hbA, haA, Ne.symm hab⟩, Finset.pair_comm _ _⟩
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const,
    hfib, Finset.card_pair (by simp [hab]), nsmul_eq_mul]
  norm_num

open Finset in
/-- Double-count `(P, z)` with `|P| = 2` and `z ∉ P` against three-element subsets. -/
lemma e494_pair_point (A : Finset ℂ) (h : Finset ℂ → ℂ) :
    ∑ P ∈ A.powersetCard 2, ∑ z ∈ A \ P, h (insert z P) = 3 * ∑ S ∈ A.powersetCard 3, h S := by
  classical
  have h1 : ∑ S ∈ A.powersetCard 3, ∑ z ∈ S, h S = 3 * ∑ S ∈ A.powersetCard 3, h S := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [Finset.sum_const, (Finset.mem_powersetCard.mp hS).2, nsmul_eq_mul]; norm_num
  rw [← h1, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨insert x.2 x.1, x.2⟩) (fun x _ => ⟨x.1.erase x.2, x.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨P, z⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hx ⊢
    obtain ⟨⟨hPA, hP2⟩, hzA, hzP⟩ := hx
    refine ⟨⟨Finset.insert_subset hzA hPA, by rw [Finset.card_insert_of_notMem hzP, hP2]⟩,
      Finset.mem_insert_self _ _⟩
  · rintro ⟨S, z⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hx ⊢
    obtain ⟨⟨hSA, hS3⟩, hzS⟩ := hx
    refine ⟨⟨(Finset.erase_subset _ _).trans hSA, by rw [Finset.card_erase_of_mem hzS, hS3]⟩,
      hSA hzS, Finset.notMem_erase _ _⟩
  · rintro ⟨P, z⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_sdiff] at hx
    simp [Finset.erase_insert hx.2.2]
  · rintro ⟨S, z⟩ hx
    simp only [Finset.mem_sigma] at hx
    simp [Finset.insert_erase hx.2]
  · rintro ⟨P, z⟩ hx
    rfl

open Finset in
/-- Interchange the two coordinates in sums over ordered distinct pairs. -/
lemma e494_swap (A : Finset ℂ) (f : ℂ → ℂ → ℂ) :
    ∑ x ∈ A.offDiag, f x.2 x.1 = ∑ x ∈ A.offDiag, f x.1 x.2 := by
  refine Finset.sum_bij' (fun x _ => x.swap) (fun x _ => x.swap) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_offDiag] at hx ⊢; exact ⟨hx.2.1, hx.1, Ne.symm hx.2.2⟩
  · intro x hx; simp only [Finset.mem_offDiag] at hx ⊢; exact ⟨hx.2.1, hx.1, Ne.symm hx.2.2⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; rfl

open Finset in
/-- Expand the cube-sum decomposition used for the three-sum argument. -/
lemma e494_C1 (A : Finset ℂ) (m : ℕ) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (x + y + z) ^ m =
      6 * ∑ S ∈ A.powersetCard 3, (∑ x ∈ S, x) ^ m +
      3 * ∑ x ∈ A, ∑ y ∈ A, (2 * x + y) ^ m - 2 * 3 ^ m * ∑ x ∈ A, x ^ m := by
  classical
  set G : ℂ × ℂ → ℂ := fun p => ∑ z ∈ A, (p.1 + p.2 + z) ^ m
  have hsplitA : ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (x + y + z) ^ m = ∑ p ∈ A ×ˢ A, G p := by
    rw [Finset.sum_product]
  have hdiagG : ∑ p ∈ A.diag, G p = ∑ x ∈ A, ∑ y ∈ A, (2 * x + y) ^ m := by
    rw [Finset.diag, Finset.sum_map]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [G, Function.Embedding.coeFn_mk, Function.diag]
    refine Finset.sum_congr rfl (fun z _ => by ring_nf)
  have hoff : ∀ p ∈ A.offDiag, G p = ∑ z ∈ A \ {p.1, p.2}, (p.1 + p.2 + z) ^ m +
      ((2 * p.1 + p.2) ^ m + (2 * p.2 + p.1) ^ m) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
    have hsub : ({p.1, p.2} : Finset ℂ) ⊆ A := by
      intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
    simp only [G]
    rw [← Finset.sum_sdiff hsub, Finset.sum_pair h3]
    congr 1; congr 1 <;> ring
  have hpartT : ∑ p ∈ A.offDiag, ∑ z ∈ A \ {p.1, p.2}, (p.1 + p.2 + z) ^ m =
      6 * ∑ S ∈ A.powersetCard 3, (∑ x ∈ S, x) ^ m := by
    have := e494_offDiag_g A (fun P => ∑ z ∈ A \ P, (∑ w ∈ P, w + z) ^ m)
    have hcongr : ∑ p ∈ A.offDiag, ∑ z ∈ A \ {p.1, p.2}, (p.1 + p.2 + z) ^ m =
        ∑ x ∈ A.offDiag, (fun P => ∑ z ∈ A \ P, (∑ w ∈ P, w + z) ^ m) {x.1, x.2} := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      obtain ⟨-, -, h3⟩ := Finset.mem_offDiag.mp hp
      simp only [Finset.sum_pair h3]
    rw [hcongr, this]
    have h2 := e494_pair_point A (fun S => (∑ x ∈ S, x) ^ m)
    have hcongr2 : ∑ s ∈ A.powersetCard 2, (fun P => ∑ z ∈ A \ P, (∑ w ∈ P, w + z) ^ m) s =
        ∑ P ∈ A.powersetCard 2, ∑ z ∈ A \ P, (fun S => (∑ x ∈ S, x) ^ m) (insert z P) := by
      refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun z hz => ?_))
      have hzP : z ∉ P := (Finset.mem_sdiff.mp hz).2
      simp only [Finset.sum_insert hzP]; ring_nf
    rw [hcongr2, h2]; ring
  have hswap : ∑ p ∈ A.offDiag, (2 * p.2 + p.1) ^ m = ∑ p ∈ A.offDiag, (2 * p.1 + p.2) ^ m :=
    e494_swap A (fun a b => (2 * a + b) ^ m)
  have hoff2 : ∑ p ∈ A.offDiag, (2 * p.1 + p.2) ^ m =
      ∑ x ∈ A, ∑ y ∈ A, (2 * x + y) ^ m - 3 ^ m * ∑ x ∈ A, x ^ m := by
    have hfull : ∑ x ∈ A, ∑ y ∈ A, (2 * x + y) ^ m = ∑ p ∈ A ×ˢ A, (2 * p.1 + p.2) ^ m := by
      rw [Finset.sum_product]
    have hd : ∑ p ∈ A.diag, (2 * p.1 + p.2) ^ m = 3 ^ m * ∑ x ∈ A, x ^ m := by
      rw [Finset.diag, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [Function.Embedding.coeFn_mk, Function.diag]; ring
    rw [hfull, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag A), hd]
    ring
  rw [hsplitA, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag A),
    hdiagG, Finset.sum_congr rfl hoff, Finset.sum_add_distrib, hpartT, Finset.sum_add_distrib,
    hswap, hoff2]
  ring

open Finset in
/-- Expand a weighted two-variable power sum. -/
lemma e494_G2 (A : Finset ℂ) (a b : ℂ) (j : ℕ) :
    ∑ x ∈ A, ∑ y ∈ A, (a * x + b * y) ^ j =
      ∑ l ∈ range (j + 1), (j.choose l : ℂ) * a ^ l * b ^ (j - l) *
        (∑ x ∈ A, x ^ l) * (∑ x ∈ A, x ^ (j - l)) := by
  simp_rw [add_pow]
  calc ∑ x ∈ A, ∑ y ∈ A, ∑ l ∈ range (j + 1), (a * x) ^ l * (b * y) ^ (j - l) * (j.choose l : ℂ)
      = ∑ l ∈ range (j + 1), ∑ x ∈ A, ∑ y ∈ A, (a * x) ^ l * (b * y) ^ (j - l) * (j.choose l : ℂ) := by
        exact (Finset.sum_congr rfl (fun x _ => Finset.sum_comm)).trans Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        calc ∑ x ∈ A, ∑ y ∈ A, (a * x) ^ l * (b * y) ^ (j - l) * (j.choose l : ℂ)
            = ∑ x ∈ A, ∑ y ∈ A, ((j.choose l : ℂ) * a ^ l * b ^ (j - l)) * (x ^ l * y ^ (j - l)) :=
              Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
          _ = ((j.choose l : ℂ) * a ^ l * b ^ (j - l)) * ((∑ x ∈ A, x ^ l) * ∑ y ∈ A, y ^ (j - l)) := by
              rw [Finset.sum_mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun x _ => ?_)
              rw [Finset.mul_sum]
          _ = _ := by ring

open Finset in
/-- Equal lower-order power sums determine weighted two-variable power sums. -/
lemma e494_G2_eq (A B : Finset ℂ) (a b : ℂ) (j : ℕ)
    (hp : ∀ i ≤ j, ∑ x ∈ A, x ^ i = ∑ x ∈ B, x ^ i) :
    ∑ x ∈ A, ∑ y ∈ A, (a * x + b * y) ^ j = ∑ x ∈ B, ∑ y ∈ B, (a * x + b * y) ^ j := by
  rw [e494_G2, e494_G2]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hl' := Finset.mem_range.mp hl
  rw [hp l (by omega), hp (j - l) (by omega)]

open Finset in
/-- Isolate the leading power-sum contribution of a weighted two-variable sum. -/
lemma e494_G2_diff (A B : Finset ℂ) (a b : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (hp : ∀ i < m, ∑ x ∈ A, x ^ i = ∑ x ∈ B, x ^ i) :
    ∑ x ∈ A, ∑ y ∈ A, (a * x + b * y) ^ m - ∑ x ∈ B, ∑ y ∈ B, (a * x + b * y) ^ m =
      (a ^ m + b ^ m) * (∑ x ∈ A, x ^ 0) * ((∑ x ∈ A, x ^ m) - ∑ x ∈ B, x ^ m) := by
  rw [e494_G2, e494_G2, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add 0 m (by omega)]
  · have h0 := hp 0 (by omega)
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.choose_self, Nat.sub_self, pow_zero,
      Nat.cast_one, one_mul, mul_one] at h0 ⊢
    rw [← h0]; ring
  · intro c hc hne
    have hc' := Finset.mem_range.mp hc
    rw [hp c (by omega), hp (m - c) (by omega)]; ring
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

open Finset in
/-- Expand a three-variable power sum. -/
lemma e494_G3 (A : Finset ℂ) (m : ℕ) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (x + y + z) ^ m =
      ∑ l ∈ range (m + 1), (m.choose l : ℂ) * (∑ x ∈ A, x ^ l) *
        ∑ y ∈ A, ∑ z ∈ A, (1 * y + 1 * z) ^ (m - l) := by
  have : ∀ x y z : ℂ, (x + y + z) ^ m =
      ∑ l ∈ range (m + 1), x ^ l * (1 * y + 1 * z) ^ (m - l) * (m.choose l : ℂ) := by
    intro x y z; rw [add_assoc, add_pow]; simp
  simp_rw [this]
  rw [show (∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, ∑ l ∈ range (m + 1),
      x ^ l * (1 * y + 1 * z) ^ (m - l) * (m.choose l : ℂ)) =
      ∑ l ∈ range (m + 1), ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A,
      x ^ l * (1 * y + 1 * z) ^ (m - l) * (m.choose l : ℂ) by
    exact (Finset.sum_congr rfl (fun x _ =>
      (Finset.sum_congr rfl (fun y _ => Finset.sum_comm)).trans Finset.sum_comm)).trans
      Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  calc ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, x ^ l * (1 * y + 1 * z) ^ (m - l) * (m.choose l : ℂ)
      = ∑ x ∈ A, ((m.choose l : ℂ) * x ^ l) * ∑ y ∈ A, ∑ z ∈ A, (1 * y + 1 * z) ^ (m - l) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z _ => by ring)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

open Finset in
/-- Isolate the leading power-sum contribution of a three-variable sum. -/
lemma e494_G3_diff (A B : Finset ℂ) (m : ℕ) (hm : 1 ≤ m)
    (hp : ∀ i < m, ∑ x ∈ A, x ^ i = ∑ x ∈ B, x ^ i) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (x + y + z) ^ m - ∑ x ∈ B, ∑ y ∈ B, ∑ z ∈ B, (x + y + z) ^ m =
      3 * (∑ x ∈ A, x ^ 0) ^ 2 * ((∑ x ∈ A, x ^ m) - ∑ x ∈ B, x ^ m) := by
  rw [e494_G3, e494_G3, ← Finset.sum_sub_distrib]
  have h0 := hp 0 (by omega)
  have hQ0 : ∀ C : Finset ℂ, ∑ y ∈ C, ∑ z ∈ C, (1 * y + 1 * z) ^ 0 = (∑ x ∈ C, x ^ 0) ^ 2 := by
    intro C; simp [sq]
  rw [Finset.sum_eq_add 0 m (by omega)]
  · have hd := e494_G2_diff A B 1 1 m hm hp
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.choose_self, Nat.sub_self, Nat.cast_one,
      hQ0]
    have : ∑ y ∈ A, ∑ z ∈ A, (1 * y + 1 * z) ^ m =
        ∑ y ∈ B, ∑ z ∈ B, (1 * y + 1 * z) ^ m + 2 * (∑ x ∈ A, x ^ 0) *
          ((∑ x ∈ A, x ^ m) - ∑ x ∈ B, x ^ m) := by
      rw [← sub_eq_iff_eq_add', hd]; ring
    rw [this, ← h0]; ring
  · intro c hc hne
    have hc' := Finset.mem_range.mp hc
    rw [hp c (by omega), e494_G2_eq A B 1 1 (m - c) (fun i hi => hp i (by omega))]; ring
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

open Finset in
/-- Equal three-sum multisets determine all power sums outside the exceptional cardinalities. -/
lemma e494_psum_eq3 (A B : Finset ℂ) (n : ℕ) (hA : A.card = n) (hB : B.card = n)
    (hn : 6 < n) (h27 : n ≠ 27) (h486 : n ≠ 486) (h : sumMultiset A 3 = sumMultiset B 3) :
    ∀ m, ∑ x ∈ A, x ^ m = ∑ x ∈ B, x ^ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hA, hB]
    · have hT : ∑ s ∈ A.powersetCard 3, (∑ x ∈ s, x) ^ m = ∑ s ∈ B.powersetCard 3, (∑ x ∈ s, x) ^ m := by
        have hTA : ∑ s ∈ A.powersetCard 3, (∑ x ∈ s, x) ^ m = ((sumMultiset A 3).map (· ^ m)).sum := by
          unfold sumMultiset; rw [Multiset.map_map]; rfl
        have hTB : ∑ s ∈ B.powersetCard 3, (∑ x ∈ s, x) ^ m = ((sumMultiset B 3).map (· ^ m)).sum := by
          unfold sumMultiset; rw [Multiset.map_map]; rfl
        rw [hTA, hTB, h]
      have hp : ∀ i < m, ∑ x ∈ A, x ^ i = ∑ x ∈ B, x ^ i := fun i hi => ih i hi
      have hCA := e494_C1 A m
      have hCB := e494_C1 B m
      have hG2 := e494_G2_diff A B 2 1 m hm hp
      have hG3 := e494_G3_diff A B m hm hp
      have hn0 : ∑ x ∈ A, x ^ 0 = (n : ℂ) := by simp [hA]
      have hG2' : ∑ x ∈ A, ∑ y ∈ A, (2 * x + y) ^ m - ∑ x ∈ B, ∑ y ∈ B, (2 * x + y) ^ m =
          (2 ^ m + 1) * n * ((∑ x ∈ A, x ^ m) - ∑ x ∈ B, x ^ m) := by
        have := hG2
        simp only [one_mul, one_pow] at this
        rw [hn0] at this
        exact this
      rw [hn0] at hG3
      have key : ((3 : ℂ) * n ^ 2 + 2 * 3 ^ m - 3 * n * (2 ^ m + 1)) *
          ((∑ x ∈ A, x ^ m) - ∑ x ∈ B, x ^ m) = 0 := by
        have e1 : ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, (x + y + z) ^ m - ∑ x ∈ B, ∑ y ∈ B, ∑ z ∈ B, (x + y + z) ^ m
            = 3 * (∑ x ∈ A, ∑ y ∈ A, (2 * x + y) ^ m - ∑ x ∈ B, ∑ y ∈ B, (2 * x + y) ^ m)
              - 2 * 3 ^ m * ((∑ x ∈ A, x ^ m) - ∑ x ∈ B, x ^ m) := by
          rw [hCA, hCB, hT]; ring
        rw [hG3, hG2'] at e1
        linear_combination e1
      have hc : ((3 : ℂ) * n ^ 2 + 2 * 3 ^ m - 3 * n * (2 ^ m + 1)) ≠ 0 := by
        intro h0
        have h1 : ((3 * n ^ 2 + 2 * 3 ^ m : ℕ) : ℂ) = ((3 * n * (2 ^ m + 1) : ℕ) : ℂ) := by
          push_cast; linear_combination h0
        have h2 : 3 * n ^ 2 + 2 * 3 ^ m = 3 * n * (2 ^ m + 1) := by exact_mod_cast h1
        rcases e494_nt n m hm h2 with h | h | h <;> omega
      exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hc)


/--
Selfridge and Straus [SeSt58] also showed that the conjecture is true when
1) $k = 3$ and $|A| > 6$, except possibly for $|A| = 27$ and $|A| = 486$, or
2) $k = 4$ and $|A| > 12$.
More generally, they proved that $A$ is determined by $A_k$ (and $|A|$) if $|A|$ is divisible by
a prime greater than $k$.

The cases $|A| = 27$ and $|A| = 486$ were left open in [SeSt58]. Fomin and Izhboldin [FoIz94]
later found two distinct sets of each of these sizes with the same multiset of $3$-sums, so
these exceptions are genuine.
-/
theorem erdos_494.variants.k_eq_3_card_gt_6 :
    ∀ card > 6, card ≠ 27 → card ≠ 486 → Erdos494Unique 3 card := by
  intro card hcard h27 h486 A B hA hB h
  exact e494_eq_of_esymm A B (hA.trans hB.symm)
    (e494_esymm_eq A B (e494_psum_eq3 A B card hA hB hcard h27 h486 h))



end Erdos494
