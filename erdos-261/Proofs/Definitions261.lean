module

/-
Copyright 2026 The Formal Conjectures Authors.
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

/-!
# Erdős Problem 261: Core Definitions, Borwein–Loring Identity, Part (i), and Extremal Bound

This module defines `Erdos261Prop` and `Erdos261InfiniteRepresentation` matching
`FormalConjectures/ErdosProblems/261.lean` verbatim, proves the telescoping dyadic
interval sum identity, derives the Borwein–Loring identity (`borwein_loring`) and property
(`borwein_loring_property`), resolves `erdos_261.parts.i` (`infinitely_many_erdos261Prop`),
and proves the Tengely–Ulas–Zygadło sharp extremal upper bound `max_n_bound` showing that
every `t`-term representation ($t \ge 2$) satisfies $n \le 2^{t+1} - t - 2$.
-/

open scoped BigOperators Cardinal

namespace Erdos261

/-- A natural number $n$ is said to have property `Erdos261Prop` if there exist $t \ge 2$
pairwise distinct positive integers $a_1, \ldots, a_t$ such that
$n / 2^n = \sum_{1 \le k \le t} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- A canonical infinite representation of a rational number $x$ by positive integers. The
denominators are strictly increasing so that reorderings are not counted as different
representations. -/
def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

/-- Helper abbreviation for the dyadic weighted term $k / 2^k$ in $\mathbb{Q}$. -/
def dyadicTerm (k : ℕ) : ℚ := (k : ℚ) / (2 ^ k : ℚ)

/-- Single-step telescoping identity: $(k + 1) / 2^{k+1} = (k + 2) / 2^k - (k + 3) / 2^{k+1}$. -/
theorem dyadicTerm_succ_telescope (k : ℕ) :
    ((k + 1 : ℕ) : ℚ) / (2 ^ (k + 1) : ℚ) =
      ((k + 2 : ℕ) : ℚ) / (2 ^ k : ℚ) - ((k + 3 : ℕ) : ℚ) / (2 ^ (k + 1) : ℚ) := by
  rw [pow_succ (2 : ℚ) k]
  have h2 : (2 : ℚ) ^ k ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Closed-form telescoping sum of $k / 2^k$ over `Finset.Ioc a b` for $a \le b$:
$$\sum_{k \in (a, b]} \frac{k}{2^k} = \frac{a + 2}{2^a} - \frac{b + 2}{2^b}.$$ -/
theorem sum_Ioc_dyadic (a : ℕ) : ∀ m : ℕ,
    ∑ k ∈ Finset.Ioc a (a + m), (k : ℚ) / (2 ^ k : ℚ) =
      ((a + 2 : ℕ) : ℚ) / (2 ^ a : ℚ) - ((a + m + 2 : ℕ) : ℚ) / (2 ^ (a + m) : ℚ)
  | 0 => by simp
  | m + 1 => by
    have hab : a ≤ a + m := Nat.le_add_right a m
    rw [← Nat.add_assoc a m 1, Finset.sum_Ioc_succ_top hab, sum_Ioc_dyadic a m]
    have hstep := dyadicTerm_succ_telescope (a + m)
    have h1 : a + m + 1 + 2 = a + m + 3 := by omega
    rw [h1, hstep]
    ring

/-- Strict lower bound $2^{m+1} \ge m + 3$ for $m \ge 1$, ensuring $n = 2^{m+1} - m - 2 \ge 1$. -/
theorem two_pow_succ_ge_add_three : ∀ m : ℕ, 1 ≤ m → m + 3 ≤ 2 ^ (m + 1)
  | 0, hm => by omega
  | 1, _ => by decide
  | m + 2, _ => by
    have ih : (m + 1) + 3 ≤ 2 ^ ((m + 1) + 1) := two_pow_succ_ge_add_three (m + 1) (by omega)
    have hstep : 2 ^ ((m + 2) + 1) = 2 * 2 ^ ((m + 1) + 1) := pow_succ' (2 : ℕ) ((m + 1) + 1)
    omega

/-- For every positive integer $m$, if $n = 2^{m+1} - m - 2$, then
$$\frac{n}{2^n} = \sum_{n < k \le n + m} \frac{k}{2^k}.$$
This is the Borwein–Loring identity [BoLo90]. -/
theorem borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
  intro n
  rw [sum_Ioc_dyadic n m]
  have hpow : m + 3 ≤ 2 ^ (m + 1) := two_pow_succ_ge_add_three m hm
  have hnm2 : n + m + 2 = 2 ^ (m + 1) := by
    dsimp [n]
    omega
  rw [hnm2, pow_add (2 : ℚ) n m]
  have h2n : (2 : ℚ) ^ n ≠ 0 := by positivity
  have h2m : (2 : ℚ) ^ m ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The Borwein–Loring construction satisfies `Erdos261Prop` for all $m \ge 2$. -/
theorem borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  set n := 2 ^ (m + 1) - m - 2
  have hn_pos : 1 ≤ n := by
    have := two_pow_succ_ge_add_three m (by omega)
    dsimp [n]
    omega
  refine ⟨m, hm, fun k : Fin m => n + 1 + k.val, ?_, ?_, ?_⟩
  · intro k1 k2 h
    ext
    dsimp at h
    omega
  · intro k
    dsimp
    omega
  · rw [borwein_loring m (by omega)]
    have hbij : (Finset.univ : Finset (Fin m)).image (fun k : Fin m => n + 1 + k.val) =
        Finset.Ioc n (n + m) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Ioc, Fin.exists_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        omega
      · intro ⟨hx1, hx2⟩
        refine ⟨x - (n + 1), by omega, by omega⟩
    rw [← hbij, Finset.sum_image]
    intro k1 _ k2 _ h
    ext
    dsimp at h
    omega

/-- One-step strict growth of the Borwein–Loring sequence $m \mapsto 2^{m+1} - m - 2$ for $m \ge 1$. -/
theorem borwein_loring_lt_succ (m : ℕ) (hm : 1 ≤ m) :
    2 ^ (m + 1) - m - 2 < 2 ^ (m + 2) - (m + 1) - 2 := by
  have h1 : m + 3 ≤ 2 ^ (m + 1) := two_pow_succ_ge_add_three m hm
  have h2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := pow_succ' (2 : ℕ) (m + 1)
  omega

/-- Strict monotonicity of the shifted Borwein–Loring sequence $k \mapsto 2^{k+3} - (k + 2) - 2$. -/
theorem borwein_loring_shifted_strictMono :
    StrictMono (fun k : ℕ => 2 ^ ((k + 2) + 1) - (k + 2) - 2) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  exact borwein_loring_lt_succ (k + 2) (by omega)

/-- Direct theorem for Erdős #261 Part (i): there are infinitely many positive integers $n$
satisfying `Erdos261Prop n`. -/
theorem infinitely_many_erdos261Prop : {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite := by
  let f : ℕ → ℕ := fun k => 2 ^ ((k + 2) + 1) - (k + 2) - 2
  have hinj : Function.Injective f := borwein_loring_shifted_strictMono.injective
  have hsub : Set.range f ⊆ {n : ℕ | 0 < n ∧ Erdos261Prop n} := by
    rintro _ ⟨k, rfl⟩
    simp only [Set.mem_ofPred_eq, f]
    refine ⟨?_, borwein_loring_property (k + 2) (by omega)⟩
    have hpow : (k + 2) + 3 ≤ 2 ^ ((k + 2) + 1) := two_pow_succ_ge_add_three (k + 2) (by omega)
    omega
  exact (Set.infinite_range_of_injective hinj).mono hsub

/-- Formal Conjectures `True ↔` form of Erdős #261 Part (i). -/
theorem erdos_261_parts_i : True ↔ {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite :=
  ⟨fun _ => infinitely_many_erdos261Prop, fun _ => trivial⟩

/-!
## Tengely–Ulas–Zygadło (2020) Extremal Upper Bound (`max_n_bound`)

We now prove Theorem 2.1(i) of Tengely, Ulas, and Zygadło (*J. Number Theory* 214, 2020):
for any $t \ge 2$ and any $t$ pairwise distinct positive integers $a_1, \dots, a_t$ satisfying
$n / 2^n = \sum_{k=1}^t a_k / 2^{a_k}$, we have
$$n \le 2^{t+1} - t - 2.$$
-/

/-- `dyadicTerm` is strictly positive for $k \ge 1$. -/
theorem dyadicTerm_pos {k : ℕ} (hk : 1 ≤ k) : 0 < dyadicTerm k := by
  unfold dyadicTerm
  positivity

/-- Antotonicity of `dyadicTerm`: if $1 \le a \le b$, then $b / 2^b \le a / 2^a$. -/
theorem dyadicTerm_antitone : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → dyadicTerm b ≤ dyadicTerm a
  | a, b, ha, hab => by
    induction hab with
    | refl => exact le_rfl
    | @step m hle ih =>
      refine le_trans ?_ ih
      rw [Nat.succ_eq_add_one]
      unfold dyadicTerm
      have hm1 : 1 ≤ m := le_trans ha hle
      have hdiff : ((m : ℚ) / (2 : ℚ) ^ m) - (((m + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (m + 1)) =
          ((m : ℚ) - 1) / (2 : ℚ) ^ (m + 1) := by
        rw [pow_succ (2 : ℚ) m]
        have h2m : (2 : ℚ) ^ m ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      have hnonneg : (0 : ℚ) ≤ ((m : ℚ) - 1) / (2 : ℚ) ^ (m + 1) := by
        apply div_nonneg
        · have : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1
          linarith
        · positivity
      linarith

/-- In any representation $n / 2^n = \sum_{k : \text{Fin } t} a_k / 2^{a_k}$ with $t \ge 2$
and $1 \le a$, every term satisfies $n + 1 \le a_k$. -/
theorem term_gt_n_of_rep {n t : ℕ} (ht : 2 ≤ t) (a : Fin t → ℕ)
    (ha_pos : 1 ≤ a)
    (hsum : (n : ℚ) / (2 ^ n : ℚ) = ∑ k, dyadicTerm (a k)) (k : Fin t) :
    n + 1 ≤ a k := by
  by_contra hle
  have hak_le_n : a k ≤ n := by omega
  have hak_pos : 1 ≤ a k := ha_pos k
  have hterm_ge : dyadicTerm n ≤ dyadicTerm (a k) := dyadicTerm_antitone hak_pos hak_le_n
  have h_exists : ∃ k' : Fin t, k' ≠ k := by
    by_cases hk0 : k.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro heq
      have hval : (1 : ℕ) = k.val := congrArg Fin.val heq
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro heq
      have hval : (0 : ℕ) = k.val := congrArg Fin.val heq
      omega
  obtain ⟨k', hk'⟩ := h_exists
  have hk'_pos : 0 < dyadicTerm (a k') := dyadicTerm_pos (ha_pos k')
  have hsub : ({k, k'} : Finset (Fin t)) ⊆ Finset.univ := Finset.subset_univ _
  have hpair_le : ∑ i ∈ ({k, k'} : Finset (Fin t)), dyadicTerm (a i) ≤ ∑ i, dyadicTerm (a i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => le_of_lt (dyadicTerm_pos (ha_pos i)))
  rw [Finset.sum_pair hk'.symm] at hpair_le
  have hsum' : dyadicTerm n = ∑ i, dyadicTerm (a i) := hsum
  linarith

/-- Any finset $S \subseteq [n + 1, \infty)$ of cardinality $t$ has dyadic sum at most the
sum over the initial interval `Finset.Ioc n (n + t)`. -/
theorem sum_le_sum_Ioc_of_subset {n t : ℕ} (S : Finset ℕ) (hcard : S.card = t)
    (hbounds : ∀ a ∈ S, n + 1 ≤ a) :
    ∑ a ∈ S, dyadicTerm a ≤ ∑ b ∈ Finset.Ioc n (n + t), dyadicTerm b := by
  let I := Finset.Ioc n (n + t)
  have hI_card : I.card = t := by simp [I]
  have hS_split : ∑ a ∈ S, dyadicTerm a =
      ∑ a ∈ S \ I, dyadicTerm a + ∑ a ∈ S ∩ I, dyadicTerm a := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S I), Finset.sdiff_union_inter]
  have hI_split : ∑ b ∈ I, dyadicTerm b =
      ∑ b ∈ I \ S, dyadicTerm b + ∑ b ∈ S ∩ I, dyadicTerm b := by
    have hdisj : Disjoint (I \ S) (S ∩ I) := by
      rw [Finset.inter_comm]
      exact Finset.disjoint_sdiff_inter I S
    have hunion : I \ S ∪ S ∩ I = I := by
      rw [Finset.inter_comm, Finset.sdiff_union_inter]
    rw [← Finset.sum_union hdisj, hunion]
  have hcard_sdiff : (S \ I).card = (I \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S I
    have h2 := Finset.card_sdiff_add_card_inter I S
    rw [Finset.inter_comm] at h2
    omega
  have h_upper : ∑ a ∈ S \ I, dyadicTerm a ≤ (S \ I).card • dyadicTerm (n + t + 1) := by
    apply Finset.sum_le_card_nsmul
    intro a ha
    simp only [Finset.mem_sdiff, I, Finset.mem_Ioc, not_and, not_le] at ha
    have ha_ge : n + 1 ≤ a := hbounds a ha.1
    have ha_gt : n + t < a := ha.2 (by omega)
    exact dyadicTerm_antitone (by omega) (by omega)
  have h_lower : (I \ S).card • dyadicTerm (n + t + 1) ≤ ∑ b ∈ I \ S, dyadicTerm b := by
    apply Finset.card_nsmul_le_sum
    intro b hb
    simp only [Finset.mem_sdiff, I, Finset.mem_Ioc] at hb
    exact dyadicTerm_antitone (by omega) (by omega)
  rw [hS_split, hI_split, ← hcard_sdiff] at *
  linarith

/-- **Tengely–Ulas–Zygadło Theorem 2.1(i)**: In any solution to
$n / 2^n = \sum_{k : \text{Fin } t} a_k / 2^{a_k}$ with $t \ge 2$ distinct positive integers,
we have $n \le 2^{t+1} - t - 2$. -/
theorem max_n_bound {n t : ℕ} (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hinj : Function.Injective a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    n ≤ 2 ^ (t + 1) - t - 2 := by
  have hpow : t + 3 ≤ 2 ^ (t + 1) := two_pow_succ_ge_add_three t (by omega)
  by_cases hn2 : n < 2
  · omega
  · have hsum' : (n : ℚ) / (2 ^ n : ℚ) = ∑ k, dyadicTerm (a k) := hsum
    have hgt : ∀ k, n + 1 ≤ a k := term_gt_n_of_rep ht a ha_pos hsum'
    let S := Finset.univ.image a
    have hS_card : S.card = t := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    have hS_bounds : ∀ x ∈ S, n + 1 ≤ x := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
      exact hgt k
    have hS_sum : ∑ x ∈ S, dyadicTerm x = (n : ℚ) / (2 ^ n : ℚ) := by
      rw [Finset.sum_image (fun x _ y _ h => hinj h), ← hsum']
    have hle := sum_le_sum_Ioc_of_subset S hS_card hS_bounds
    rw [hS_sum] at hle
    unfold dyadicTerm at hle
    rw [sum_Ioc_dyadic n t, pow_add (2 : ℚ) n t] at hle
    have h2n : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
    have h2t : (0 : ℚ) < (2 : ℚ) ^ t := by positivity
    have h_ineq : ((n + t + 2 : ℕ) : ℚ) ≤ 2 * (2 : ℚ) ^ t := by
      have h1 : ((n + t + 2 : ℕ) : ℚ) / ((2 : ℚ) ^ n * (2 : ℚ) ^ t) ≤ 2 / (2 : ℚ) ^ n := by
        have : ((n + 2 : ℕ) : ℚ) / (2 : ℚ) ^ n - (n : ℚ) / (2 : ℚ) ^ n = 2 / (2 : ℚ) ^ n := by
          push_cast; ring
        linarith
      have h2 := (div_le_div_iff₀ (by positivity) h2n).mp h1
      nlinarith
    have h_nat : n + t + 2 ≤ 2 ^ (t + 1) := by
      rw [pow_succ' (2 : ℕ) t]
      exact_mod_cast h_ineq
    omega

/-- **Tengely–Ulas–Zygadło Theorem 2.1(ii) (First-term upper bound)**:
In any solution to $n / 2^n = \sum_{k : \text{Fin } t} a_k / 2^{a_k}$ with $n \ge 1$ and $t \ge 2$
distinct positive integers, there is at least one term $a_k$ satisfying
$n + 1 \le a_k \le n + 3$. -/
theorem exists_term_le_add_three {n t : ℕ} (hn : 1 ≤ n) (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hinj : Function.Injective a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    ∃ k : Fin t, n + 1 ≤ a k ∧ a k ≤ n + 3 := by
  have hsum' : (n : ℚ) / (2 ^ n : ℚ) = ∑ k, dyadicTerm (a k) := hsum
  have hgt : ∀ k, n + 1 ≤ a k := term_gt_n_of_rep ht a ha_pos hsum'
  by_contra hnone
  have hall_ge : ∀ k : Fin t, (n + 3) + 1 ≤ a k := by
    intro k
    have hk := hgt k
    have hnot : ¬(n + 1 ≤ a k ∧ a k ≤ n + 3) := fun h => hnone ⟨k, h⟩
    omega
  let S := Finset.univ.image a
  have hS_card : S.card = t := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hS_bounds : ∀ x ∈ S, (n + 3) + 1 ≤ x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
    exact hall_ge k
  have hS_sum : ∑ x ∈ S, dyadicTerm x = (n : ℚ) / (2 ^ n : ℚ) := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h), ← hsum']
  have hle := sum_le_sum_Ioc_of_subset S hS_card hS_bounds
  rw [hS_sum] at hle
  unfold dyadicTerm at hle
  rw [sum_Ioc_dyadic (n + 3) t] at hle
  have htail_pos : (0 : ℚ) < ((n + 3 + t + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (n + 3 + t) := by positivity
  have hlt : (n : ℚ) / (2 : ℚ) ^ n < ((n + 3 + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (n + 3) := by linarith
  rw [pow_add (2 : ℚ) n 3] at hlt
  have h2n : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
  have h1 := (div_lt_div_iff₀ h2n (by positivity)).mp hlt
  have hn_q : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  push_cast at h1
  nlinarith

/-- **Tengely–Ulas–Zygadło Theorem 2.1(ii) (Last-gap divisibility)**:
For any strictly increasing solution $a : \text{Fin } (t + 2) \to \mathbb{N}$ ($1 \le a$) to
$n / 2^n = \sum_{k} a_k / 2^{a_k}$, the power of two of the last gap divides the last term:
$$2^{a_{t+1} - a_t} \mid a_{t+1}.$$ -/
theorem last_term_gap_dvd {n t : ℕ} (a : Fin (t + 2) → ℕ)
    (hmono : StrictMono a) (ha_pos : 1 ≤ a)
    (hsum : n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    2 ^ (a (Fin.last (t + 1)) - a (Fin.castSucc (Fin.last t))) ∣ a (Fin.last (t + 1)) := by
  let last : Fin (t + 2) := Fin.last (t + 1)
  let prev : Fin (t + 2) := Fin.castSucc (Fin.last t)
  have hprev_val : prev.val = t := rfl
  have hgt : ∀ k, n + 1 ≤ a k := term_gt_n_of_rep (by omega) a ha_pos hsum
  have hn_le_prev : n ≤ a prev := by have := hgt prev; omega
  have hprev_lt_last : a prev < a last := hmono (by change t < t + 1; omega)
  have hk_le_prev : ∀ k ∈ (Finset.univ.erase last), a k ≤ a prev := by
    intro k hk
    have hne : k ≠ last := Finset.ne_of_mem_erase hk
    have hlt : k.val < t + 1 := by
      have := k.isLt
      have : k.val ≠ t + 1 := fun h => hne (Fin.ext h)
      omega
    exact hmono.monotone (by change k.val ≤ t; omega)
  set G := 2 ^ (a last - a prev)
  have h_lhs : (n : ℚ) / (2 ^ n : ℚ) * (2 : ℚ) ^ (a last) =
      ((G * (n * 2 ^ (a prev - n)) : ℕ) : ℚ) := by
    have hexp : a last = n + ((a last - a prev) + (a prev - n)) := by omega
    conv_lhs => rw [hexp, pow_add (2 : ℚ) n, pow_add]
    have h2n : (2 : ℚ) ^ n ≠ 0 := by positivity
    push_cast [G]
    field_simp
  have h_rhs_term : ∀ k ∈ Finset.univ.erase last,
      ((a k : ℚ) / (2 ^ (a k) : ℚ)) * (2 : ℚ) ^ (a last) =
        ((G * (a k * 2 ^ (a prev - a k)) : ℕ) : ℚ) := by
    intro k hk
    have hak := hk_le_prev k hk
    have hexp : a last = a k + ((a last - a prev) + (a prev - a k)) := by omega
    conv_lhs => rw [hexp, pow_add (2 : ℚ) (a k), pow_add]
    have h2k : (2 : ℚ) ^ (a k) ≠ 0 := by positivity
    push_cast [G]
    field_simp
  have h_rhs : (∑ k, (a k : ℚ) / (2 ^ (a k) : ℚ)) * (2 : ℚ) ^ (a last) =
      (a last : ℚ) + ((G * ∑ k ∈ Finset.univ.erase last, a k * 2 ^ (a prev - a k) : ℕ) : ℚ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ last), add_mul, Finset.sum_mul]
    have h_last : ((a last : ℚ) / (2 ^ (a last) : ℚ)) * (2 : ℚ) ^ (a last) = (a last : ℚ) :=
      div_mul_cancel₀ _ (by positivity)
    rw [h_last, Finset.sum_congr rfl h_rhs_term]
    push_cast
    rw [Finset.mul_sum]
  have h_eq_q : ((G * (n * 2 ^ (a prev - n)) : ℕ) : ℚ) =
      ((a last + G * ∑ k ∈ Finset.univ.erase last, a k * 2 ^ (a prev - a k) : ℕ) : ℚ) := by
    calc ((G * (n * 2 ^ (a prev - n)) : ℕ) : ℚ)
      _ = (n : ℚ) / (2 ^ n : ℚ) * (2 : ℚ) ^ (a last) := h_lhs.symm
      _ = (∑ k, (a k : ℚ) / (2 ^ (a k) : ℚ)) * (2 : ℚ) ^ (a last) := by rw [hsum]
      _ = ((a last + G * ∑ k ∈ Finset.univ.erase last, a k * 2 ^ (a prev - a k) : ℕ) : ℚ) := by
        rw [h_rhs]; push_cast; rfl
  have h_eq_nat : G * (n * 2 ^ (a prev - n)) =
      a last + G * ∑ k ∈ Finset.univ.erase last, a k * 2 ^ (a prev - a k) := by
    exact_mod_cast h_eq_q
  refine ⟨n * 2 ^ (a prev - n) - ∑ k ∈ Finset.univ.erase last, a k * 2 ^ (a prev - a k), ?_⟩
  rw [Nat.mul_sub]
  change a last = _
  omega

/-!
## Uniqueness of the Extremal Borwein–Loring Representation (`borwein_loring_unique`)
-/

/-- Strict antotonicity of `dyadicTerm` for $2 \le a < b$: $b / 2^b < a / 2^a$. -/
theorem dyadicTerm_strictAnti {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    dyadicTerm b < dyadicTerm a := by
  have hle : dyadicTerm b ≤ dyadicTerm (a + 1) :=
    dyadicTerm_antitone (by omega) (Nat.succ_le_of_lt hab)
  refine lt_of_le_of_lt hle ?_
  unfold dyadicTerm
  have hdiff : ((a : ℚ) / (2 : ℚ) ^ a) - (((a + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (a + 1)) =
      ((a : ℚ) - 1) / (2 : ℚ) ^ (a + 1) := by
    rw [pow_succ (2 : ℚ) a]
    have h2a : (2 : ℚ) ^ a ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hpos : (0 : ℚ) < ((a : ℚ) - 1) / (2 : ℚ) ^ (a + 1) := by
    apply div_pos
    · have : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
      linarith
    · positivity
  linarith

/-- Equality in the majorization bound `sum_le_sum_Ioc_of_subset` forces $S = \text{Finset.Ioc } n \, (n + t)$. -/
theorem eq_Ioc_of_sum_eq_sum_Ioc {n t : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) (S : Finset ℕ)
    (hcard : S.card = t) (hbounds : ∀ a ∈ S, n + 1 ≤ a)
    (hsum : ∑ a ∈ S, dyadicTerm a = ∑ b ∈ Finset.Ioc n (n + t), dyadicTerm b) :
    S = Finset.Ioc n (n + t) := by
  set I := Finset.Ioc n (n + t)
  have hI_card : I.card = t := by simp [I]
  by_contra hne
  have hnot_sub : ¬(S ⊆ I) := fun hsub =>
    hne (Finset.eq_of_subset_of_card_le hsub (by rw [hI_card, hcard]))
  have hsdiff_ne : (S \ I).Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun hemp => hnot_sub (Finset.sdiff_eq_empty_iff_subset.mp hemp))
  have hS_split : ∑ a ∈ S, dyadicTerm a =
      ∑ a ∈ S \ I, dyadicTerm a + ∑ a ∈ S ∩ I, dyadicTerm a := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S I), Finset.sdiff_union_inter]
  have hI_split : ∑ b ∈ I, dyadicTerm b =
      ∑ b ∈ I \ S, dyadicTerm b + ∑ b ∈ S ∩ I, dyadicTerm b := by
    have hdisj : Disjoint (I \ S) (S ∩ I) := by
      rw [Finset.inter_comm]
      exact Finset.disjoint_sdiff_inter I S
    have hunion : I \ S ∪ S ∩ I = I := by
      rw [Finset.inter_comm, Finset.sdiff_union_inter]
    rw [← Finset.sum_union hdisj, hunion]
  have hcard_sdiff : (S \ I).card = (I \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S I
    have h2 := Finset.card_sdiff_add_card_inter I S
    rw [Finset.inter_comm] at h2
    omega
  have h_upper : ∑ a ∈ S \ I, dyadicTerm a ≤ (S \ I).card • dyadicTerm (n + t + 1) := by
    apply Finset.sum_le_card_nsmul
    intro a ha
    simp only [Finset.mem_sdiff, I, Finset.mem_Ioc, not_and, not_le] at ha
    have ha_ge : n + 1 ≤ a := hbounds a ha.1
    have ha_gt : n + t < a := ha.2 (by omega)
    exact dyadicTerm_antitone (by omega) (by omega)
  have h_lower : (I \ S).card • dyadicTerm (n + t) ≤ ∑ b ∈ I \ S, dyadicTerm b := by
    apply Finset.card_nsmul_le_sum
    intro b hb
    simp only [Finset.mem_sdiff, I, Finset.mem_Ioc] at hb
    exact dyadicTerm_antitone (by omega) (by omega)
  have h_strict : dyadicTerm (n + t + 1) < dyadicTerm (n + t) :=
    dyadicTerm_strictAnti (by omega) (by omega)
  have hcard_pos : 0 < (S \ I).card := Finset.Nonempty.card_pos hsdiff_ne
  rw [← hcard_sdiff] at h_lower
  simp only [nsmul_eq_mul] at h_upper h_lower
  have hcard_pos_q : (0 : ℚ) < ((S \ I).card : ℚ) := by exact_mod_cast hcard_pos
  have h_mul_lt : ((S \ I).card : ℚ) * dyadicTerm (n + t + 1) <
      ((S \ I).card : ℚ) * dyadicTerm (n + t) :=
    mul_lt_mul_of_pos_left h_strict hcard_pos_q
  linarith

theorem strictMono_fin_add_le {t : ℕ} {a : Fin t → ℕ} (hmono : StrictMono a) :
    ∀ {i j : Fin t}, i.val ≤ j.val → a i + (j.val - i.val) ≤ a j := by
  intro i j hij
  obtain ⟨d, hd⟩ : ∃ d, j.val = i.val + d := ⟨j.val - i.val, by omega⟩
  induction d generalizing i j with
  | zero =>
    have hij_eq : i = j := Fin.ext (by omega)
    subst hij_eq
    omega
  | succ d ih =>
    let j' : Fin t := ⟨i.val + d, by omega⟩
    have hj' : a i + (j'.val - i.val) ≤ a j' := ih (by change i.val ≤ i.val + d; omega) rfl
    have hlt : a j' < a j := hmono (by change i.val + d < j.val; omega)
    have hdiff : j'.val - i.val = d := by change (i.val + d) - i.val = d; omega
    omega

/-- **Tengely–Ulas–Zygadło Theorem 2.1(i) (Extremal Uniqueness)**:
For $n = 2^{t+1} - t - 2$ ($t \ge 2$), the Borwein–Loring block $a_k = n + 1 + k$ is the
unique strictly increasing $t$-term representation of $n / 2^n$. -/
theorem borwein_loring_unique {t : ℕ} (ht : 2 ≤ t) (a : Fin t → ℕ)
    (hmono : StrictMono a) (ha_pos : 1 ≤ a)
    (hsum : (2 ^ (t + 1) - t - 2 : ℕ) / (2 ^ (2 ^ (t + 1) - t - 2) : ℚ) =
      ∑ k, (a k) / (2 ^ (a k) : ℚ)) :
    ∀ k : Fin t, a k = (2 ^ (t + 1) - t - 2) + 1 + k.val := by
  set n := 2 ^ (t + 1) - t - 2
  have hpow : t + 3 ≤ 2 ^ (t + 1) := two_pow_succ_ge_add_three t (by omega)
  have hn1 : 1 ≤ n := by dsimp [n]; omega
  have hsum' : (n : ℚ) / (2 ^ n : ℚ) = ∑ k, dyadicTerm (a k) := hsum
  have hgt : ∀ k, n + 1 ≤ a k := term_gt_n_of_rep ht a ha_pos hsum'
  let S := Finset.univ.image a
  have hS_card : S.card = t := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_fin]
  have hS_bounds : ∀ x ∈ S, n + 1 ≤ x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
    exact hgt k
  have hS_sum : ∑ x ∈ S, dyadicTerm x = ∑ b ∈ Finset.Ioc n (n + t), dyadicTerm b := by
    rw [Finset.sum_image (fun x _ y _ h => hmono.injective h), ← hsum']
    exact borwein_loring t (by omega)
  have hS_eq : S = Finset.Ioc n (n + t) :=
    eq_Ioc_of_sum_eq_sum_Ioc hn1 (by omega) S hS_card hS_bounds hS_sum
  have hak_mem : ∀ k : Fin t, a k ∈ Finset.Ioc n (n + t) := by
    intro k
    rw [← hS_eq]
    exact Finset.mem_image_of_mem a (Finset.mem_univ k)
  intro k
  let first : Fin t := ⟨0, by omega⟩
  let last : Fin t := ⟨t - 1, by omega⟩
  have h1 : a first + (k.val - first.val) ≤ a k :=
    strictMono_fin_add_le hmono (by change 0 ≤ k.val; omega)
  have h2 : a k + (last.val - k.val) ≤ a last :=
    strictMono_fin_add_le hmono (by change k.val ≤ t - 1; omega)
  have hfirst_ge : n + 1 ≤ a first := (Finset.mem_Ioc.mp (hak_mem first)).1
  have hlast_le : a last ≤ n + t := (Finset.mem_Ioc.mp (hak_mem last)).2
  have hfirst_val : first.val = 0 := rfl
  have hlast_val : last.val = t - 1 := rfl
  omega

/-!
## Punctured-Interval Infinite Family (`punctured_interval_identity`, `punctured_family_erdos261Prop`)

Following Tengely, Ulas, and Zygadło (2020, Theorem 3.1), removing a single element $n + j$
from $(n, n + m]$ yields a representation of $n / 2^n$ whenever
$(2^{m - j} + 1) n + 2^{m - j} j + m + 2 = 2^{m + 1}$. Taking $m = 4k + 1$ and $j = 4k - 1$
gives the infinite non-Borwein–Loring family $n_k = (2^{4k + 2} + 1) / 5 - 4k$.
-/

/-- General punctured-interval identity: if $1 \le j \le m$ and
$(2^{m - j} + 1) n + 2^{m - j} j + m + 2 = 2^{m + 1}$, then removing $n + j$ from
`Finset.Ioc n (n + m)` yields a representation of $n / 2^n$. -/
theorem punctured_interval_identity {n m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (heq : (2 ^ (m - j) + 1) * n + 2 ^ (m - j) * j + m + 2 = 2 ^ (m + 1)) :
    n / (2 ^ n : ℚ) = ∑ k ∈ (Finset.Ioc n (n + m)).erase (n + j), k / (2 ^ k : ℚ) := by
  have hmem : n + j ∈ Finset.Ioc n (n + m) := by
    simp only [Finset.mem_Ioc]; omega
  have hsum_erase := Finset.add_sum_erase (Finset.Ioc n (n + m))
    (fun k => (k : ℚ) / (2 ^ k : ℚ)) hmem
  rw [sum_Ioc_dyadic n m] at hsum_erase
  have hm_split : n + m = (n + j) + (m - j) := by omega
  have hpow_mj : (2 : ℚ) ^ (n + m) = (2 : ℚ) ^ (n + j) * (2 : ℚ) ^ (m - j) := by
    conv_lhs => rw [hm_split, pow_add]
  have hpow_m : (2 : ℚ) ^ (n + m) = (2 : ℚ) ^ n * (2 : ℚ) ^ m := pow_add (2 : ℚ) n m
  have h2n : (2 : ℚ) ^ n ≠ 0 := by positivity
  have h2nj : (2 : ℚ) ^ (n + j) ≠ 0 := by positivity
  have h2mj : (2 : ℚ) ^ (m - j) ≠ 0 := by positivity
  have h2m : (2 : ℚ) ^ m ≠ 0 := by positivity
  have heq_q : (((2 : ℚ) ^ (m - j) + 1) * (n : ℚ) + (2 : ℚ) ^ (m - j) * (j : ℚ) +
      (m : ℚ) + 2) = 2 * (2 : ℚ) ^ m := by
    have heq' : (2 ^ (m - j) + 1) * n + 2 ^ (m - j) * j + m + 2 = 2 * 2 ^ m := by
      rw [← pow_succ' (2 : ℕ) m]; exact heq
    exact_mod_cast heq'
  have h_target : ((n + j : ℕ) : ℚ) / (2 ^ (n + j) : ℚ) +
      ((n + m + 2 : ℕ) : ℚ) / (2 ^ (n + m) : ℚ) = 2 / (2 ^ n : ℚ) := by
    rw [hpow_mj]
    have h_lhs : ((n + j : ℕ) : ℚ) / ((2 : ℚ) ^ (n + j)) +
        ((n + m + 2 : ℕ) : ℚ) / ((2 : ℚ) ^ (n + j) * (2 : ℚ) ^ (m - j)) =
        (((2 : ℚ) ^ (m - j) + 1) * (n : ℚ) + (2 : ℚ) ^ (m - j) * (j : ℚ) + (m : ℚ) + 2) /
          ((2 : ℚ) ^ (n + j) * (2 : ℚ) ^ (m - j)) := by
      push_cast; field_simp; ring
    rw [h_lhs, heq_q, ← hpow_mj, hpow_m]
    field_simp
  have h_main : ∑ k ∈ (Finset.Ioc n (n + m)).erase (n + j), (k : ℚ) / (2 ^ k : ℚ) =
      ((n + 2 : ℕ) : ℚ) / (2 ^ n : ℚ) - 2 / (2 ^ n : ℚ) := by
    linarith
  rw [h_main]
  push_cast
  ring

/-- Any punctured-interval parameter triple $(n, m, j)$ with $m \ge 3$ and $1 \le j \le m$
satisfying $(2^{m - j} + 1) n + 2^{m - j} j + m + 2 = 2^{m + 1}$ yields `Erdos261Prop n`. -/
theorem erdos261Prop_of_punctured_interval {n m j : ℕ} (hm : 3 ≤ m) (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (heq : (2 ^ (m - j) + 1) * n + 2 ^ (m - j) * j + m + 2 = 2 ^ (m + 1)) :
    Erdos261Prop n := by
  let S := (Finset.Ioc n (n + m)).erase (n + j)
  have hmem : n + j ∈ Finset.Ioc n (n + m) := by
    simp only [Finset.mem_Ioc]; omega
  have hcard : S.card = m - 1 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hmem, Nat.card_Ioc, Nat.add_sub_cancel_left]
  have hcard2 : 2 ≤ S.card := by omega
  have hpos : ∀ a ∈ S, 1 ≤ a := by
    intro a ha
    have ha' := Finset.mem_of_mem_erase ha
    simp only [Finset.mem_Ioc] at ha'
    omega
  let e := S.equivFin.symm
  refine ⟨S.card, hcard2, fun k => (e k).val, ?_, ?_, ?_⟩
  · intro k1 k2 h
    exact e.injective (Subtype.ext h)
  · intro k
    exact hpos (e k).val (e k).property
  · rw [punctured_interval_identity hj1 hjm heq]
    have hbij : ∑ k : Fin S.card, ((e k).val : ℚ) / (2 ^ (e k).val : ℚ) =
        ∑ x : S, (x.val : ℚ) / (2 ^ x.val : ℚ) :=
      Equiv.sum_comp e (fun x : S => (x.val : ℚ) / (2 ^ x.val : ℚ))
    have hcoe : ∑ x : S, (x.val : ℚ) / (2 ^ x.val : ℚ) =
        ∑ a ∈ S, (a : ℚ) / (2 ^ a : ℚ) :=
      Finset.sum_coe_sort S (fun a => (a : ℚ) / (2 ^ a : ℚ))
    exact (hbij.trans hcoe).symm

theorem five_dvd_two_pow_four_mul_add_two_add_one : ∀ k : ℕ, 5 ∣ (2 ^ (4 * k + 2) + 1)
  | 0 => ⟨1, rfl⟩
  | k + 1 => by
    obtain ⟨q, hq⟩ := five_dvd_two_pow_four_mul_add_two_add_one k
    refine ⟨16 * q - 3, ?_⟩
    have hexp : 4 * (k + 1) + 2 = (4 * k + 2) + 4 := by omega
    have hpow : 2 ^ (4 * (k + 1) + 2) = 16 * 2 ^ (4 * k + 2) := by
      rw [hexp, pow_add]; ring
    omega

theorem twenty_k_lt_two_pow_four_k_add_two : ∀ k : ℕ, 1 ≤ k → 20 * k + 4 ≤ 2 ^ (4 * k + 2)
  | 0, hk => by omega
  | 1, _ => by decide
  | k + 2, _ => by
    have ih := twenty_k_lt_two_pow_four_k_add_two (k + 1) (by omega)
    have hexp : 4 * (k + 2) + 2 = (4 * (k + 1) + 2) + 4 := by omega
    have hpow : 2 ^ (4 * (k + 2) + 2) = 16 * 2 ^ (4 * (k + 1) + 2) := by
      rw [hexp, pow_add]; ring
    omega

/-- **Tengely–Ulas–Zygadło (2020, Theorem 3.1 specialization)**:
For every $k \ge 1$, the non-Borwein–Loring integer $n_k = (2^{4k + 2} + 1) / 5 - 4k$
(starting at $n_1 = 9$) satisfies `Erdos261Prop n_k` via the punctured interval
$(n_k, n_k + 4k + 1] \setminus \{n_k + 4k - 1\}$. -/
theorem punctured_family_erdos261Prop (k : ℕ) (hk : 1 ≤ k) :
    Erdos261Prop ((2 ^ (4 * k + 2) + 1) / 5 - 4 * k) := by
  obtain ⟨q, hq⟩ := five_dvd_two_pow_four_mul_add_two_add_one k
  have hbound := twenty_k_lt_two_pow_four_k_add_two k hk
  have hdiv : (2 ^ (4 * k + 2) + 1) / 5 = q := by omega
  refine erdos261Prop_of_punctured_interval (m := 4 * k + 1) (j := 4 * k - 1)
    (by omega) (by omega) (by omega) ?_
  have hmj : (4 * k + 1) - (4 * k - 1) = 2 := by omega
  rw [hmj, hdiv]
  change 5 * (q - 4 * k) + 4 * (4 * k - 1) + (4 * k + 1) + 2 = 2 ^ (4 * k + 2)
  omega

/-!
## Splicing Representations (`arbitrary_length_rep_of_all_erdos261Prop`)
-/

/-- Splicing lemma: if $n / 2^n$ is the dyadic sum of a finite set $S$ with $2 \le S.\text{card}$,
and the maximum element $m = S.\text{max'}$ satisfies `Erdos261Prop m`, then $n / 2^n$ is also
the dyadic sum of a finite set $S'$ of strictly larger cardinality $S.\text{card} + 1 \le S'.\text{card}$. -/
theorem splice_finset_rep_at_max {n : ℕ} (S : Finset ℕ) (hcard : 2 ≤ S.card)
    (hpos : ∀ a ∈ S, 1 ≤ a) (hsum : (n : ℚ) / (2 ^ n : ℚ) = ∑ a ∈ S, dyadicTerm a)
    (hmax_prop : Erdos261Prop (S.max' (Finset.card_pos.mp (by omega)))) :
    ∃ S' : Finset ℕ, S.card + 1 ≤ S'.card ∧ (∀ a ∈ S', 1 ≤ a) ∧
      (n : ℚ) / (2 ^ n : ℚ) = ∑ a ∈ S', dyadicTerm a := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set m := S.max' hne
  have hm_mem : m ∈ S := Finset.max'_mem S hne
  have hm_le : ∀ a ∈ S, a ≤ m := fun a ha => Finset.le_max' S a ha
  obtain ⟨t, ht, b, hbinj, hb_pos, hbsum⟩ := hmax_prop
  have hb_gt : ∀ k : Fin t, m + 1 ≤ b k := term_gt_n_of_rep ht b hb_pos hbsum
  let T := Finset.univ.image b
  have hT_card : T.card = t := by
    rw [Finset.card_image_of_injective _ hbinj, Finset.card_fin]
  have hT_gt : ∀ x ∈ T, m + 1 ≤ x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
    exact hb_gt k
  have hT_sum : ∑ x ∈ T, dyadicTerm x = dyadicTerm m := by
    rw [Finset.sum_image (fun x _ y _ h => hbinj h)]
    exact hbsum.symm
  have hdisj : Disjoint (S.erase m) T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hx_le : x ≤ m := hm_le x (Finset.mem_of_mem_erase hxS)
    have hx_gt : m + 1 ≤ x := hT_gt x hxT
    omega
  refine ⟨S.erase m ∪ T, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hm_mem, hT_card]
    omega
  · intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxT
    · exact hpos x (Finset.mem_of_mem_erase hxS)
    · have := hT_gt x hxT; omega
  · rw [Finset.sum_union hdisj, hT_sum, Finset.sum_erase_add S dyadicTerm hm_mem, ← hsum]

/-- If every positive integer satisfies `Erdos261Prop` (Erdős #261 Part (ii)), then every
positive integer $n$ admits representations $n / 2^n = \sum_{k : \text{Fin } t} a_k / 2^{a_k}$
of arbitrarily large length $t \ge L$. -/
theorem arbitrary_length_rep_of_all_erdos261Prop
    (hall : ∀ m : ℕ, 0 < m → Erdos261Prop m) {n : ℕ} (hn : 0 < n) (L : ℕ) :
    ∃ᵉ (t ≥ max 2 L) (a : Fin t → ℕ), a.Injective ∧
      (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ) := by
  have h_finset : ∀ k : ℕ, ∃ S : Finset ℕ, k + 2 ≤ S.card ∧ (∀ a ∈ S, 1 ≤ a) ∧
      (n : ℚ) / (2 ^ n : ℚ) = ∑ a ∈ S, dyadicTerm a := by
    intro k
    induction k with
    | zero =>
      obtain ⟨t, ht, a, hainj, ha_pos, hasum⟩ := hall n hn
      let S := Finset.univ.image a
      refine ⟨S, ?_, ?_, ?_⟩
      · rw [Finset.card_image_of_injective _ hainj, Finset.card_fin]; omega
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact ha_pos i
      · rw [Finset.sum_image (fun x _ y _ h => hainj h)]
        exact hasum
    | succ k ih =>
      obtain ⟨S, hcard, hpos, hsum⟩ := ih
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hm_pos : 0 < S.max' hne := by
        have := hpos (S.max' hne) (Finset.max'_mem S hne)
        omega
      obtain ⟨S', hcard', hpos', hsum'⟩ :=
        splice_finset_rep_at_max S (by omega) hpos hsum (hall (S.max' hne) hm_pos)
      exact ⟨S', by omega, hpos', hsum'⟩
  obtain ⟨S, hcard, hpos, hsum⟩ := h_finset L
  let e := S.equivFin.symm
  refine ⟨S.card, by omega, fun k => (e k).val, ?_, ?_, ?_⟩
  · intro k1 k2 h
    exact e.injective (Subtype.ext h)
  · intro k
    exact hpos (e k).val (e k).property
  · rw [hsum]
    have hbij : ∑ k : Fin S.card, dyadicTerm (e k).val = ∑ x : S, dyadicTerm x.val :=
      Equiv.sum_comp e (fun x : S => dyadicTerm x.val)
    have hcoe : ∑ x : S, dyadicTerm x.val = ∑ a ∈ S, dyadicTerm a :=
      Finset.sum_coe_sort S dyadicTerm
    exact (hbij.trans hcoe).symm

end Erdos261
