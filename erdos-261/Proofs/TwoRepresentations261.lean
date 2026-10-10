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
public import Definitions261

@[expose] public section

/-!
# Erdős Problem 261: Infinitely Many Rationals with $2^m$ Infinite Representations

This module proves `erdos_261.variants.two_representations` and generalizes it to
`infinite_rationals_two_pow_reps`: for **every** $m \in \mathbb{N}$, there are infinitely many
rational numbers $x \in \mathbb{Q}$ having at least $2^m$ distinct infinite representations
$x = \sum_{k=0}^\infty a_k / 2^{a_k}$ by strictly increasing positive integers.

For each $r \ge 2$, let $n_r = 2^{r+1} - r - 2$ be the $r$-th Borwein–Loring number (`blN r`).
Because $n_r + r = 2^{r+1} - 2 < 2^{r+2} - r - 3 = n_{r+1}$, the intervals $[n_r, n_r + r]$
are pairwise disjoint. In each block $j \in \text{Fin } m$ ($r = j + 2$), choosing either
$\{n_r\}$ (`c j = false`) or $(n_r, n_r + r]$ (`c j = true`) yields $2^m$ distinct finite subsets
`prefixFinset m c` $\subseteq [1, n_{m+2}]$, all having the exact same dyadic sum
$\sum_{j : \text{Fin } m} n_{j+2} / 2^{n_{j+2}}$. Appending any contiguous tail $[L + 1, \infty)$
with $L \ge n_{m+2}$ produces $2^m$ distinct strictly increasing sequences (`seqOfFinset L`)
all summing to the same rational `valMulti m L`, and varying $L \ge n_{m+2}$ yields infinitely
many such rationals.
-/

open Filter Topology
open scoped BigOperators Cardinal

namespace Erdos261

/-- Elementary quadratic-vs-exponential bound $n^2 \le 2^{n+2}$ for all $n \in \mathbb{N}$. -/
theorem mul_self_le_two_pow_add_two : ∀ n : ℕ, n * n ≤ 2 ^ (n + 2)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n + 4 => by
    have ih := mul_self_le_two_pow_add_two (n + 3)
    have hid : (n + 4) * (n + 4) + n * n + 4 * n + 2 = 2 * ((n + 3) * (n + 3)) := by ring
    have hpow : 2 ^ (n + 4 + 2) = 2 * 2 ^ (n + 3 + 2) := by
      rw [show n + 4 + 2 = (n + 3 + 2) + 1 by omega, pow_succ']
    omega

/-- Telescoping partial sums over `Finset.range n` in $\mathbb{Q}$:
$$\sum_{k < n} \frac{a + 1 + k}{2^{a + 1 + k}} = \frac{a + 2}{2^a} - \frac{a + n + 2}{2^{a + n}}.$$ -/
theorem sum_range_dyadic_shift (a : ℕ) : ∀ n : ℕ,
    ∑ k ∈ Finset.range n, ((a + 1 + k : ℕ) : ℚ) / (2 ^ (a + 1 + k) : ℚ) =
      ((a + 2 : ℕ) : ℚ) / (2 ^ a : ℚ) - ((a + n + 2 : ℕ) : ℚ) / (2 ^ (a + n) : ℚ)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_dyadic_shift a n]
    have hstep := dyadicTerm_succ_telescope (a + n)
    have h1 : a + 1 + n = a + n + 1 := by omega
    have h2 : a + (n + 1) + 2 = a + n + 3 := by omega
    have h3 : a + (n + 1) = a + n + 1 := by omega
    rw [h1, h2, h3, hstep]
    ring

/-- Order-topological convergence of a non-negative rational series from its `Finset.range` partial sums. -/
theorem hasSum_rat_of_tendsto_nat_of_nonneg {f : ℕ → ℚ} {a : ℚ}
    (hf : ∀ i, 0 ≤ f i)
    (ht : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i) atTop (𝓝 a)) :
    HasSum f a := by
  have hmono_set : Monotone (fun s : Finset ℕ ↦ ∑ i ∈ s, f i) :=
    Finset.sum_mono_set_of_nonneg hf
  have hmono_nat : Monotone (fun n : ℕ ↦ ∑ i ∈ Finset.range n, f i) :=
    fun m n hmn ↦ hmono_set (Finset.range_mono hmn)
  have hlub_nat : IsLUB (Set.range fun n : ℕ ↦ ∑ i ∈ Finset.range n, f i) a :=
    isLUB_of_tendsto_atTop hmono_nat ht
  refine hasSum_of_isLUB_of_nonneg a hf ⟨?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    have hsub : s ⊆ Finset.range (s.sup id + 1) := by
      intro x hx
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Finset.le_sup (f := id) hx
    exact (hmono_set hsub).trans (hlub_nat.1 ⟨s.sup id + 1, rfl⟩)
  · intro b hb
    exact hlub_nat.2 (by rintro _ ⟨n, rfl⟩; exact hb ⟨Finset.range n, rfl⟩)

/-- The telescoping remainder $(a + n + 2) / 2^{a + n}$ tends to $0$ in $\mathbb{Q}$ as $n \to \infty$. -/
theorem tendsto_dyadic_rem_zero (a : ℕ) :
    Tendsto (fun n : ℕ ↦ ((a + n + 2 : ℕ) : ℚ) / (2 ^ (a + n) : ℚ)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (4 * ((a : ℚ) + 3)))
    (Eventually.of_forall fun n ↦ by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hsq : (n : ℚ) * (n : ℚ) ≤ (2 : ℚ) ^ (n + 2) := by
    exact_mod_cast mul_self_le_two_pow_add_two n
  have hpow : (2 : ℚ) ^ (n + 2) ≤ 4 * (2 : ℚ) ^ (a + n) := by
    have : 2 ^ (n + 2) ≤ 4 * 2 ^ (a + n) := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact_mod_cast this
  have hnum : ((a + n + 2 : ℕ) : ℚ) ≤ ((a : ℚ) + 3) * (n : ℚ) := by
    have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    have ha0 : (0 : ℚ) ≤ (a : ℚ) := Nat.cast_nonneg a
    push_cast; nlinarith
  rw [div_le_div_iff₀ (by positivity) hn_pos]
  nlinarith

/-- Closed-form infinite dyadic tail sum in $\mathbb{Q}$:
$$\sum_{k=0}^\infty \frac{a + 1 + k}{2^{a + 1 + k}} = \frac{a + 2}{2^a}.$$ -/
theorem hasSum_dyadic_shift_rat (a : ℕ) :
    HasSum (fun k : ℕ ↦ ((a + 1 + k : ℕ) : ℚ) / (2 ^ (a + 1 + k) : ℚ))
      (((a + 2 : ℕ) : ℚ) / (2 ^ a : ℚ)) := by
  refine hasSum_rat_of_tendsto_nat_of_nonneg (fun _ ↦ by positivity) ?_
  simp_rw [sum_range_dyadic_shift a]
  simpa using tendsto_const_nhds.sub (tendsto_dyadic_rem_zero a)

/-- The Borwein–Loring number $n_r = 2^{r+1} - r - 2$. -/
def blN (r : ℕ) : ℕ := 2 ^ (r + 1) - r - 2

theorem blN_pos {r : ℕ} (hr : 1 ≤ r) : 1 ≤ blN r := by
  unfold blN
  have := two_pow_succ_ge_add_three r hr
  omega

theorem blN_add_lt_succ {r : ℕ} (hr : 1 ≤ r) : blN r + r < blN (r + 1) := by
  unfold blN
  have h1 := two_pow_succ_ge_add_three r hr
  have h2 : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := pow_succ' (2 : ℕ) (r + 1)
  omega

theorem blN_mono {r1 r2 : ℕ} (hr1 : 1 ≤ r1) (h : r1 < r2) : blN r1 + r1 < blN r2 := by
  have hle : r1 + 1 ≤ r2 := h
  induction hle with
  | refl => exact blN_add_lt_succ hr1
  | @step k hle ih =>
    rw [Nat.succ_eq_add_one]
    have hle' : r1 + 1 ≤ k := hle
    have hk := blN_add_lt_succ (r := k) (by omega)
    omega

/-- The $r$-th Borwein–Loring block choice: either `(blN r, blN r + r]` (`b = true`)
or `{blN r}` (`b = false`). -/
def blockFinset (r : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ioc (blN r) (blN r + r) else {blN r}

theorem mem_blockFinset_bounds {r x : ℕ} {b : Bool} (hx : x ∈ blockFinset r b) :
    blN r ≤ x ∧ x ≤ blN r + r := by
  unfold blockFinset at hx
  split_ifs at hx
  · simp only [Finset.mem_Ioc] at hx; omega
  · simp only [Finset.mem_singleton] at hx; omega

theorem blN_mem_blockFinset_iff {r : ℕ} (b : Bool) :
    blN r ∈ blockFinset r b ↔ b = false := by
  unfold blockFinset
  cases b <;> simp

theorem sum_blockFinset {r : ℕ} (hr : 1 ≤ r) (b : Bool) :
    ∑ k ∈ blockFinset r b, (k : ℚ) / (2 ^ k : ℚ) = (blN r : ℚ) / (2 ^ (blN r) : ℚ) := by
  unfold blockFinset
  cases b
  · simp
  · simpa [blN] using (borwein_loring r (by omega)).symm

/-- Disjoint union of `m` Borwein–Loring blocks for `c : Fin m → Bool`. -/
def prefixFinset (m : ℕ) (c : Fin m → Bool) : Finset ℕ :=
  Finset.univ.biUnion (fun j : Fin m => blockFinset (j.val + 2) (c j))

theorem blockFinset_disjoint {j1 j2 : ℕ} (hj1 : 1 ≤ j1) (hj2 : 1 ≤ j2) (hne : j1 ≠ j2) (b1 b2 : Bool) :
    Disjoint (blockFinset j1 b1) (blockFinset j2 b2) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have h1 := mem_blockFinset_bounds hx1
  have h2 := mem_blockFinset_bounds hx2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := blN_mono hj1 hlt; omega
  · have := blN_mono hj2 hgt; omega

theorem sum_prefixFinset (m : ℕ) (c : Fin m → Bool) :
    ∑ k ∈ prefixFinset m c, (k : ℚ) / (2 ^ k : ℚ) =
      ∑ j : Fin m, (blN (j.val + 2) : ℚ) / (2 ^ (blN (j.val + 2)) : ℚ) := by
  unfold prefixFinset
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun j _ => sum_blockFinset (by omega) (c j))
  · intro j1 _ j2 _ hne
    exact blockFinset_disjoint (j1 := j1.val + 2) (j2 := j2.val + 2)
      (by omega) (by omega) (fun h => hne (Fin.ext (by omega))) (c j1) (c j2)

theorem blN_mem_prefixFinset_iff {m : ℕ} (c : Fin m → Bool) (j : Fin m) :
    blN (j.val + 2) ∈ prefixFinset m c ↔ c j = false := by
  unfold prefixFinset
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j', hj'⟩
    by_cases hjeq : j' = j
    · subst hjeq
      exact (blN_mem_blockFinset_iff (c j')).mp hj'
    · exfalso
      have hbounds := mem_blockFinset_bounds hj'
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjeq) with hlt | hgt
      · have := blN_mono (r1 := j'.val + 2) (r2 := j.val + 2) (by omega) (by omega)
        omega
      · have := blN_mono (r1 := j.val + 2) (r2 := j'.val + 2) (by omega) (by omega)
        omega
  · intro hc
    exact ⟨j, (blN_mem_blockFinset_iff (c j)).mpr hc⟩

theorem mem_prefixFinset_bounds {m x : ℕ} {c : Fin m → Bool} (hx : x ∈ prefixFinset m c) :
    1 ≤ x ∧ x ≤ blN (m + 2) := by
  unfold prefixFinset at hx
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
  rcases hx with ⟨j, hj⟩
  have hb := mem_blockFinset_bounds hj
  have hpos := blN_pos (r := j.val + 2) (by omega)
  have htop := blN_mono (r1 := j.val + 2) (r2 := m + 2) (by omega) (by omega)
  omega

/-- Strictly increasing sequence enumerating `P ⊆ [1, L]` followed by `[L + 1, ∞)`. -/
noncomputable def seqOfFinset (L : ℕ) (P : Finset ℕ) (k : ℕ) : ℕ :=
  if h : k < P.card then P.orderEmbOfFin rfl ⟨k, h⟩
  else (L + 1) + (k - P.card)

theorem seqOfFinset_strictMono {L : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, 1 ≤ x ∧ x ≤ L) :
    StrictMono (seqOfFinset L P) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  dsimp only [seqOfFinset]
  split_ifs with h1 h2 h2
  · exact (P.orderEmbOfFin rfl).strictMono (Nat.lt_succ_self k)
  · have hmem : P.orderEmbOfFin rfl ⟨k, h1⟩ ∈ P := Finset.orderEmbOfFin_mem P rfl ⟨k, h1⟩
    have hle := (hP _ hmem).2
    omega
  · omega
  · omega

theorem seqOfFinset_ge_one {L : ℕ} {P : Finset ℕ} (hP : ∀ x ∈ P, 1 ≤ x ∧ x ≤ L) :
    1 ≤ seqOfFinset L P := by
  intro k
  dsimp only [Pi.one_apply, seqOfFinset]
  split_ifs with h
  · exact (hP _ (Finset.orderEmbOfFin_mem P rfl ⟨k, h⟩)).1
  · omega

theorem sum_range_seqOfFinset (L : ℕ) (P : Finset ℕ) :
    ∑ i ∈ Finset.range P.card, (seqOfFinset L P i : ℚ) / (2 ^ (seqOfFinset L P i) : ℚ) =
      ∑ x ∈ P, (x : ℚ) / (2 ^ x : ℚ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  have hcongr : ∑ i : Fin P.card, (seqOfFinset L P i.val : ℚ) / (2 ^ (seqOfFinset L P i.val) : ℚ) =
      ∑ i : Fin P.card, ((P.orderEmbOfFin rfl i : ℕ) : ℚ) / (2 ^ (P.orderEmbOfFin rfl i : ℕ) : ℚ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [seqOfFinset, i.isLt]
  rw [hcongr]
  let e : Fin P.card ≃ P := (P.orderIsoOfFin rfl).toEquiv
  have hbij := Equiv.sum_comp e (fun x : P => (x.val : ℚ) / (2 ^ x.val : ℚ))
  have hcoe := Finset.sum_coe_sort P (fun x : ℕ => (x : ℚ) / (2 ^ x : ℚ))
  exact hbij.trans hcoe

theorem hasSum_seqOfFinset (L : ℕ) (P : Finset ℕ) :
    HasSum (fun k => (seqOfFinset L P k : ℚ) / (2 ^ (seqOfFinset L P k) : ℚ))
      ((∑ x ∈ P, (x : ℚ) / (2 ^ x : ℚ)) + (2 * ((L + 1 : ℕ) : ℚ) + 2) / (2 : ℚ) ^ (L + 1)) := by
  have htail : HasSum (fun n => (seqOfFinset L P (n + P.card) : ℚ) / (2 ^ (seqOfFinset L P (n + P.card)) : ℚ))
      ((2 * ((L + 1 : ℕ) : ℚ) + 2) / (2 : ℚ) ^ (L + 1)) := by
    have e : ∀ n, seqOfFinset L P (n + P.card) = L + 1 + n := fun n => by
      dsimp only [seqOfFinset]
      rw [dite_eq_right_iff.mpr (fun h => by omega)]
      omega
    simp_rw [e]
    convert hasSum_dyadic_shift_rat L using 1
    rw [pow_succ (2 : ℚ) L]
    have h2 : (2 : ℚ) ^ L ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [← sum_range_seqOfFinset L P]
  exact htail.sum_range_add

theorem mem_range_seqOfFinset_iff {L x : ℕ} {P : Finset ℕ} (hx : x ≤ L) :
    x ∈ Set.range (seqOfFinset L P) ↔ x ∈ P := by
  constructor
  · rintro ⟨k, rfl⟩
    dsimp only [seqOfFinset] at hx ⊢
    split_ifs at hx ⊢ with h
    · exact Finset.orderEmbOfFin_mem P rfl ⟨k, h⟩
    · omega
  · intro hxP
    have hrange : x ∈ Set.range (P.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hxP
    rcases hrange with ⟨i, rfl⟩
    refine ⟨i.val, ?_⟩
    simp [seqOfFinset, i.isLt]

/-- The rational value represented by all $2^m$ sequences with tail starting at $L + 1$. -/
def valMulti (m L : ℕ) : ℚ :=
  (∑ j : Fin m, (blN (j.val + 2) : ℚ) / (2 ^ (blN (j.val + 2)) : ℚ)) +
    (2 * ((L + 1 : ℕ) : ℚ) + 2) / (2 : ℚ) ^ (L + 1)

theorem rep_seqOfFinset_prefix (m L : ℕ) (hL : blN (m + 2) ≤ L) (c : Fin m → Bool) :
    Erdos261InfiniteRepresentation (valMulti m L) (seqOfFinset L (prefixFinset m c)) := by
  have hbounds : ∀ x ∈ prefixFinset m c, 1 ≤ x ∧ x ≤ L := by
    intro x hx
    have hb := mem_prefixFinset_bounds hx
    omega
  have hsum : HasSum (fun k => (seqOfFinset L (prefixFinset m c) k : ℚ) / (2 ^ (seqOfFinset L (prefixFinset m c) k) : ℚ))
      (valMulti m L) := by
    unfold valMulti
    rw [← sum_prefixFinset m c]
    exact hasSum_seqOfFinset L (prefixFinset m c)
  exact ⟨seqOfFinset_strictMono hbounds, seqOfFinset_ge_one hbounds, hsum.summable, hsum.tsum_eq.symm⟩

theorem two_pow_le_card_representations_valMulti (m L : ℕ) (hL : blN (m + 2) ≤ L) :
    (2 ^ m : Cardinal) ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation (valMulti m L) a} := by
  let f : (Fin m → Bool) → {a : ℕ → ℕ | Erdos261InfiniteRepresentation (valMulti m L) a} :=
    fun c => ⟨seqOfFinset L (prefixFinset m c), rep_seqOfFinset_prefix m L hL c⟩
  have hinj : Function.Injective f := by
    intro c1 c2 h
    have hseq : seqOfFinset L (prefixFinset m c1) = seqOfFinset L (prefixFinset m c2) :=
      congrArg Subtype.val h
    funext j
    have hj_le : blN (j.val + 2) ≤ L := by
      have := blN_mono (r1 := j.val + 2) (r2 := m + 2) (by omega) (by omega)
      omega
    have hmem1 := (mem_range_seqOfFinset_iff (P := prefixFinset m c1) hj_le).trans
      (blN_mem_prefixFinset_iff c1 j)
    have hmem2 := (mem_range_seqOfFinset_iff (P := prefixFinset m c2) hj_le).trans
      (blN_mem_prefixFinset_iff c2 j)
    rw [hseq] at hmem1
    have hiff := hmem1.symm.trans hmem2
    cases hc1 : c1 j <;> cases hc2 : c2 j <;> simp_all
  have hcard := Cardinal.mk_le_of_injective hinj
  simpa using hcard

theorem valMulti_shifted_strictAnti (m : ℕ) :
    StrictAnti (fun k : ℕ => valMulti m (blN (m + 2) + k)) := by
  refine strictAnti_nat_of_succ_lt fun k => ?_
  unfold valMulti
  set L := blN (m + 2) + k
  have hL_eq : blN (m + 2) + (k + 1) + 1 = L + 1 + 1 := by omega
  rw [hL_eq]
  have hdiff : ((2 * ((L + 1 : ℕ) : ℚ) + 2) / (2 : ℚ) ^ (L + 1)) -
      ((2 * ((L + 1 + 1 : ℕ) : ℚ) + 2) / (2 : ℚ) ^ (L + 1 + 1)) =
      ((2 * (L : ℚ) + 2) / (2 : ℚ) ^ (L + 1 + 1)) := by
    rw [pow_succ (2 : ℚ) (L + 1)]
    have h2 : (2 : ℚ) ^ (L + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hpos : (0 : ℚ) < (2 * (L : ℚ) + 2) / (2 : ℚ) ^ (L + 1 + 1) := by positivity
  linarith

/-- **Arbitrarily many representations ($2^m$ for every $m \in \mathbb{N}$)**:
For every $m \in \mathbb{N}$, there are infinitely many rational numbers $x \in \mathbb{Q}$
with at least $2^m$ distinct infinite representations `Erdos261InfiniteRepresentation x a`. -/
theorem infinite_rationals_two_pow_reps (m : ℕ) :
    {x : ℚ | (2 ^ m : Cardinal) ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}}.Infinite := by
  let f : ℕ → ℚ := fun k => valMulti m (blN (m + 2) + k)
  have hinj : Function.Injective f := (valMulti_shifted_strictAnti m).injective
  have hsub : Set.range f ⊆ {x : ℚ | (2 ^ m : Cardinal) ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}} := by
    rintro _ ⟨k, rfl⟩
    simp only [Set.mem_ofPred_eq, f]
    exact two_pow_le_card_representations_valMulti m (blN (m + 2) + k) (by omega)
  exact (Set.infinite_range_of_injective hinj).mono hsub

/-- Infinitely many rationals have at least two distinct infinite representations ($m = 1$ specialization). -/
theorem infinite_rationals_two_reps :
    {x : ℚ | 2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}}.Infinite := by
  simpa using infinite_rationals_two_pow_reps 1

/-- Direct existential theorem: there exists a rational $x$ with at least two infinite representations. -/
theorem exists_rational_two_representations :
    ∃ x : ℚ, 2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  have h := two_pow_le_card_representations_valMulti 1 (blN 3) le_rfl
  exact ⟨valMulti 1 (blN 3), by simpa using h⟩

/-- Formal Conjectures `True ↔` form of `erdos_261.variants.two_representations`. -/
theorem two_representations :
    True ↔ ∃ x : ℚ, 2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} :=
  ⟨fun _ => exists_rational_two_representations, fun _ => trivial⟩

end Erdos261
