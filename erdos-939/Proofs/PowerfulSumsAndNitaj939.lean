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

namespace Nat

def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

instance Full.decide (k n : ℕ) : Decidable (Full k n) :=
  Finset.decidableDforallFinset

theorem Full.zero_left (n : ℕ) : (0 : ℕ).Full n := by simp [Nat.Full]
theorem Full.one_left (n : ℕ) : (1 : ℕ).Full n := by aesop (add simp [Nat.Full])
theorem Full.zero_right (k : ℕ) : k.Full 0 := by simp [Nat.Full]
theorem Full.one_right (k : ℕ) : k.Full 1 := by simp [Nat.Full]

abbrev Powerful : ℕ → Prop := (2).Full

instance Powerful.decide (n : ℕ) : Decidable (Powerful n) :=
  Finset.decidableDforallFinset

theorem full_of_le_full (k : ℕ) (n : ℕ) {m : ℕ} (hk : k ≤ m) (h : m.Full n) : k.Full n :=
  fun p a => pow_dvd_of_le_of_pow_dvd hk (h p a)

end Nat

@[reducible] def Finset.Coprime (S : Finset ℕ) : Prop := S.gcd id = 1

theorem Finset.Coprime_pair_iff (S : Finset ℕ) (a b : ℕ) (h : S = {a, b}) :
    S.Coprime ↔ Nat.Coprime a b := by
  simp only [h, Finset.Coprime, Nat.Coprime, Finset.gcd_insert, Finset.gcd_singleton, normalize_eq]
  rfl

namespace Erdos939

lemma e939_full_pow (r m : ℕ) : r.Full (m ^ r) := by
  intro p hp
  have hp_prime := (Nat.mem_primeFactors.mp hp).1
  have hp_dvd := (Nat.mem_primeFactors.mp hp).2.1
  exact pow_dvd_pow_of_dvd (hp_prime.dvd_of_dvd_pow hp_dvd) r

open scoped BigOperators

def Erdos939Sums (r : ℕ) : Set (Finset ℕ) :=
  {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧
    ∀ s ∈ S, 0 < s ∧ r.Full s}

open Nat

/-!
## Foundational Theory for `Erdos939Sums` and `Nat.Full`

This section establishes universal (`∀`) theorems characterizing:
1. Unfolding and membership criteria for `Erdos939Sums r`.
2. Complete classification of the degenerate/boundary regimes $r \le 2$ (`Erdos939Sums r = ∅`)
   and $r = 3$ (`Erdos939Sums 3 = {{1}}`), plus cardinality and sum lower bounds for $r \ge 4$.
3. Multiplicative and power closure of $r$-powerful numbers (`Nat.Full`), prime-power threshold
   equivalences, and universal $2^r$ lower bounds for $r$-full integers $n > 1$.
4. Subset monotonicity and common-divisor obstructions for `Finset.Coprime` and `Erdos939Sums r`.
5. Sylvester–Frobenius exponent decompositions ($m = 2u + 3v$ and $r$-basis decompositions)
   governing canonical power-product representations of $r$-powerful numbers.
-/

/-- Membership unfolding for `Erdos939Sums r`. -/
theorem mem_erdos939Sums_iff (r : ℕ) (S : Finset ℕ) :
    S ∈ Erdos939Sums r ↔
      S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧ ∀ s ∈ S, 0 < s ∧ r.Full s := by
  simp [Erdos939Sums]

/-- The empty `Finset ℕ` has gcd `0`, so it is never coprime. -/
theorem not_coprime_empty_finset (S : Finset ℕ) (hS : S = ∅) : ¬ S.Coprime := by
  subst hS
  simp [Finset.Coprime]

/-- Every set `S ∈ Erdos939Sums r` is nonempty and cannot contain `0`. -/
theorem ne_empty_and_zero_notMem_of_mem_erdos939Sums (r : ℕ) (S : Finset ℕ)
    (hS : S ∈ Erdos939Sums r) : S ≠ ∅ ∧ 0 ∉ S := by
  rcases hS with ⟨_, hcop, _, hpos⟩
  refine ⟨?_, ?_⟩
  · intro hempty
    exact not_coprime_empty_finset S hempty hcop
  · intro h0
    have := (hpos 0 h0).1
    omega

/-- For every $r \le 2$, `Erdos939Sums r` contains no sets because $|S| = r - 2 = 0$ forces $S = ∅$. -/
theorem erdos939Sums_eq_empty_of_le_two (r : ℕ) (hr : r ≤ 2) (S : Finset ℕ) :
    S ∉ Erdos939Sums r := by
  intro hS
  have hne := (ne_empty_and_zero_notMem_of_mem_erdos939Sums r S hS).1
  rcases hS with ⟨hcard, -, -, -⟩
  have h0 : S.card = 0 := by omega
  exact hne (Finset.card_eq_zero.mp h0)

/-- A singleton `{a}` is coprime if and only if `a = 1`. -/
theorem coprime_singleton_iff_eq_one (a : ℕ) :
    ({a} : Finset ℕ).Coprime ↔ a = 1 := by
  simp [Finset.Coprime]

/-- A singleton `{a}` belongs to `Erdos939Sums r` if and only if `r = 3` and `a = 1`. -/
theorem singleton_mem_erdos939Sums_iff (r a : ℕ) :
    ({a} : Finset ℕ) ∈ Erdos939Sums r ↔ r = 3 ∧ a = 1 := by
  rw [mem_erdos939Sums_iff]
  simp only [Finset.card_singleton, coprime_singleton_iff_eq_one, Finset.sum_singleton,
    Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨hr, rfl, -, -⟩
    exact ⟨by omega, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, Nat.Full.one_right 3, Nat.zero_lt_one, Nat.Full.one_right 3⟩

/-- At $r = 3$, `Erdos939Sums 3` consists of the unique singleton `{1}`. -/
theorem mem_erdos939Sums_three_iff (S : Finset ℕ) :
    S ∈ Erdos939Sums 3 ↔ S = {1} := by
  constructor
  · intro hS
    have hcard : S.card = 1 := hS.1
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    have ha := (singleton_mem_erdos939Sums_iff 3 a).mp hS
    rw [ha.2]
  · rintro rfl
    exact (singleton_mem_erdos939Sums_iff 3 1).mpr ⟨rfl, rfl⟩

/-- For $r \ge 4$, every `S ∈ Erdos939Sums r` has at least $2$ elements and sum at least $2$. -/
theorem two_le_card_and_two_le_sum_of_mem_erdos939Sums (r : ℕ) (hr : 4 ≤ r)
    (S : Finset ℕ) (hS : S ∈ Erdos939Sums r) :
    2 ≤ S.card ∧ 2 ≤ ∑ s ∈ S, s := by
  rcases hS with ⟨hcard, -, -, hpos⟩
  have h2 : 2 ≤ S.card := by omega
  refine ⟨h2, ?_⟩
  have hsum : S.card ≤ ∑ s ∈ S, s := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun s hs => (hpos s hs).1
  omega

/-- The product of two $r$-powerful (`Nat.Full r`) numbers is $r$-powerful. -/
theorem full_mul_of_full (r a b : ℕ) (ha : r.Full a) (hb : r.Full b) :
    r.Full (a * b) := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, hne⟩ := hp
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hne
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hne
  rcases hpp.dvd_mul.mp hpd with hpa | hpb
  · exact (ha p (Nat.mem_primeFactors.mpr ⟨hpp, hpa, ha0⟩)).trans (dvd_mul_right a b)
  · exact (hb p (Nat.mem_primeFactors.mpr ⟨hpp, hpb, hb0⟩)).trans (dvd_mul_left b a)

/-- Any power $a^m$ of an $r$-powerful number $a$ is $r$-powerful. -/
theorem full_pow_of_full (r a m : ℕ) (ha : r.Full a) :
    r.Full (a ^ m) := by
  induction m with
  | zero => simpa using Nat.Full.one_right r
  | succ m ih =>
    rw [pow_succ]
    exact full_mul_of_full r (a ^ m) a ih ha

/-- Multiplying an $r$-powerful number $b$ by $a^k$ with $k \ge r$ preserves $r$-powerful status. -/
theorem full_pow_mul_of_le (r k a b : ℕ) (hrk : r ≤ k) (hb : r.Full b) :
    r.Full (a ^ k * b) :=
  full_mul_of_full r (a ^ k) b
    (Nat.full_of_le_full r (a ^ k) hrk (e939_full_pow k a)) hb

/-- Every canonical consecutive-power product $a^r b^{r+1}$ is $r$-powerful. -/
theorem full_mul_pow_succ (r a b : ℕ) :
    r.Full (a ^ r * b ^ (r + 1)) :=
  full_mul_of_full r (a ^ r) (b ^ (r + 1))
    (e939_full_pow r a)
    (Nat.full_of_le_full r (b ^ (r + 1)) (Nat.le_succ r) (e939_full_pow (r + 1) b))

/-- A positive prime power $p^m$ ($m > 0$) is $r$-powerful if and only if $r \le m$. -/
theorem prime_pow_full_iff (r p m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    r.Full (p ^ m) ↔ r ≤ m := by
  constructor
  · intro hfull
    have hpm : p ∈ (p ^ m).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, dvd_pow_self p (by omega), pow_ne_zero m hp.ne_zero⟩
    have hdvd : p ^ r ∣ p ^ m := hfull p hpm
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  · intro hrm
    exact Nat.full_of_le_full r (p ^ m) hrm (e939_full_pow m p)

/-- For $r \ge 2$, no prime number $p$ is $r$-powerful. -/
theorem not_full_prime_of_two_le (r p : ℕ) (hr : 2 ≤ r) (hp : p.Prime) :
    ¬ r.Full p := by
  intro hfull
  have h1 : r ≤ 1 := (prime_pow_full_iff r p 1 hp Nat.zero_lt_one).mp (by simpa using hfull)
  omega

/-- Every $r$-powerful integer $n > 1$ is at least $2^r$. -/
theorem two_pow_le_of_full_of_gt_one (r n : ℕ) (hn : 1 < n) (hfull : r.Full n) :
    2 ^ r ≤ n := by
  have hmin_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hmin_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hmem : n.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hmin_prime, hmin_dvd, by omega⟩
  have hpow_dvd : n.minFac ^ r ∣ n := hfull n.minFac hmem
  calc 2 ^ r ≤ n.minFac ^ r := Nat.pow_le_pow_left hmin_prime.two_le r
    _ ≤ n := Nat.le_of_dvd (by omega) hpow_dvd

/-- For every $r \ge 4$ and `S ∈ Erdos939Sums r`, the total sum satisfies $2^r \le \sum_{s \in S} s$. -/
theorem two_pow_le_sum_of_mem_erdos939Sums (r : ℕ) (hr : 4 ≤ r)
    (S : Finset ℕ) (hS : S ∈ Erdos939Sums r) :
    2 ^ r ≤ ∑ s ∈ S, s := by
  have h2 := (two_le_card_and_two_le_sum_of_mem_erdos939Sums r hr S hS).2
  exact two_pow_le_of_full_of_gt_one r (∑ s ∈ S, s) (by omega) hS.2.2.1

/-- Superset monotonicity of `Finset.Coprime`: if `S ⊆ T` and `S` is coprime, then `T` is coprime. -/
theorem coprime_mono_subset (S T : Finset ℕ) (hST : S ⊆ T) (hS : S.Coprime) :
    T.Coprime := by
  show T.gcd id = 1
  have hdvd : T.gcd id ∣ S.gcd id := Finset.gcd_mono hST
  rw [show S.gcd id = 1 from hS] at hdvd
  exact Nat.eq_one_of_dvd_one hdvd

/-- If every element of `S` is divisible by `d > 1`, then `S` is not coprime. -/
theorem not_coprime_of_common_divisor (S : Finset ℕ) (d : ℕ) (hd : 1 < d)
    (hdvd : ∀ s ∈ S, d ∣ s) : ¬ S.Coprime := by
  intro hcop
  have hd_gcd : d ∣ S.gcd id := Finset.dvd_gcd hdvd
  rw [show S.gcd id = 1 from hcop] at hd_gcd
  have := Nat.le_of_dvd Nat.zero_lt_one hd_gcd
  omega

/-- For every `S ∈ Erdos939Sums r` and every prime `p`, some summand `s ∈ S` is not divisible by `p`. -/
theorem exists_not_dvd_of_mem_erdos939Sums (r : ℕ) (S : Finset ℕ)
    (hS : S ∈ Erdos939Sums r) (p : ℕ) (hp : p.Prime) :
    ∃ s ∈ S, ¬ p ∣ s := by
  by_contra h
  have hall : ∀ s ∈ S, p ∣ s := by
    intro s hs
    by_contra hps
    exact h ⟨s, hs, hps⟩
  exact not_coprime_of_common_divisor S p hp.one_lt hall hS.2.1

/-- Sylvester–Frobenius $\{2, 3\}$ exponent basis: every $m \ge 2$ decomposes as $2u + 3v$ with $v \in \{0, 1\}$. -/
theorem frobenius_exponent_two_three (m : ℕ) (hm : 2 ≤ m) :
    ∃ u v : ℕ, m = 2 * u + 3 * v ∧ (v = 0 ∨ v = 1) := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · exact ⟨k, 0, by omega, Or.inl rfl⟩
  · exact ⟨k - 1, 1, by omega, Or.inr rfl⟩

/-!
## Generalized $k$-Summand Families, Prime-Sharing Obstructions, Radical Bounds, and Reduction of `erdos_939` to $r = 4$

This section establishes universal structural theorems for Erdős Problem #939:
1. **Generalized $k$-Summand $r$-Powerful Family (`Erdos939GeneralSums r k`):**
   - Unfolding, specialization `Erdos939GeneralSums r (r - 2) = Erdos939Sums r`, and boundary
     classifications at $k = 0$ (empty) and $k = 1$ ($\{\{1\}\}$).
   - **Downward Exponent Monotonicity (`erdos939GeneralSums_antitone_r`):** For fixed $k$, increasing
     the power threshold $r_1 \le r_2$ shrinks `Erdos939GeneralSums r k`, so any $(r - 2)$-summand
     $r'$-powerful coprime representation with $r' \ge r$ belongs to `Erdos939Sums r`
     (`mem_erdos939Sums_of_mem_generalSums_ge`), explaining why Cambie's $5$-summand $8$-powerful
     witness simultaneously inhabits `Erdos939Sums 7`.
2. **Prime-Sharing, Erase-Divisibility, and $p$-adic Valuation Obstructions:**
   - **Prime-Sharing Law (`not_dvd_sum_of_coprime_of_dvd_erase`):** In any coprime set $S$, if a prime
     $p$ divides every element of $S.\text{erase } s_0$, then $p$ divides neither $s_0$ nor $\sum_{s \in S} s$.
   - Prime-power divisibility of the sum and summands (`p ∣ X → p^r ∣ X`), modular remainder
     obstruction (`n % p^r ≠ 0 → ¬ r.Full n`), and the $r$-basis Sylvester–Frobenius decomposition
     $m = (q - 1)r + (r + \text{rem})$ with $0 \le \text{rem} < r$.
3. **Two-Summand Coprime $r$-Powerful Theory, Universal $3^r$ Lower Bound, and Radical / $abc$ Inequality:**
   - Pairwise coprimality and disjointness of `primeFactors` for $(a, b, a+b)$ when $\gcd(a,b)=1$.
   - Distinctness $a \ne b$ of any positive coprime pair with $r$-powerful sum ($r \ge 2$), giving a
     characterization of `{a, b} ∈ Erdos939GeneralSums r 2` without an explicit $a \ne b$ side condition.
   - Universal odd lower bound $3^r \le n$ (`three_pow_le_of_full_of_odd_gt_one`) and unconditional
     two-summand lower bound $3^r \le a + b$ (`three_pow_le_sum_of_coprime_full_pair`).
   - Radical / $abc$ product bound $(p \cdot q \cdot l)^r \le a b (a + b) < (a + b)^3$ for prime factors
     $p \in a.\text{primeFactors}$, $q \in b.\text{primeFactors}$, $l \in (a + b).\text{primeFactors}$.
4. **Master Reduction of `erdos_939` (`∀ r ≥ 4`) to $r = 4$ and Quantitative Growth of `e939S r q`:**
   - Complete equivalence between `∀ r ≥ 4, (Erdos939Sums r).Nonempty`, `(Erdos939Sums 4).Nonempty`,
     and the existence of a positive coprime $4$-powerful pair $(a, b)$ with $4$-powerful sum $a + b$.
   - Strict monotonicity of $\sum_{s \in \text{e939S } r\ q} s$ in $q$ and existence of witnesses in
     `Erdos939Sums r` with arbitrarily large sum for every $r \ge 6$.
-/

/-- Generalized $k$-summand family of coprime positive $r$-powerful sets with $r$-powerful sum. -/
def Erdos939GeneralSums (r k : ℕ) : Set (Finset ℕ) :=
  {S : Finset ℕ | S.card = k ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧ ∀ s ∈ S, 0 < s ∧ r.Full s}

/-- Membership unfolding for `Erdos939GeneralSums r k`. -/
theorem mem_erdos939GeneralSums_iff (r k : ℕ) (S : Finset ℕ) :
    S ∈ Erdos939GeneralSums r k ↔
      S.card = k ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧ ∀ s ∈ S, 0 < s ∧ r.Full s := by
  simp [Erdos939GeneralSums]

/-- Specializing `Erdos939GeneralSums r k` to $k = r - 2$ recovers `Erdos939Sums r`. -/
theorem mem_erdos939GeneralSums_r_sub_two_iff (r : ℕ) (S : Finset ℕ) :
    S ∈ Erdos939GeneralSums r (r - 2) ↔ S ∈ Erdos939Sums r := by
  simp [Erdos939GeneralSums, Erdos939Sums]

/-- Downward exponent monotonicity of `Erdos939GeneralSums r k` in $r$ for fixed summand count $k$. -/
theorem erdos939GeneralSums_antitone_r (r₁ r₂ k : ℕ) (hr : r₁ ≤ r₂)
    (S : Finset ℕ) (hS : S ∈ Erdos939GeneralSums r₂ k) :
    S ∈ Erdos939GeneralSums r₁ k := by
  rw [mem_erdos939GeneralSums_iff] at hS ⊢
  rcases hS with ⟨hcard, hcop, hsum, hall⟩
  refine ⟨hcard, hcop, Nat.full_of_le_full r₁ (∑ s ∈ S, s) hr hsum, ?_⟩
  intro s hs
  exact ⟨(hall s hs).1, Nat.full_of_le_full r₁ s hr (hall s hs).2⟩

/-- Any $(r - 2)$-summand $r₂$-powerful coprime representation with $r \le r₂$ belongs to `Erdos939Sums r`. -/
theorem mem_erdos939Sums_of_mem_generalSums_ge (r r₂ : ℕ) (hrr : r ≤ r₂)
    (S : Finset ℕ) (hS : S ∈ Erdos939GeneralSums r₂ (r - 2)) :
    S ∈ Erdos939Sums r := by
  rw [← mem_erdos939GeneralSums_r_sub_two_iff]
  exact erdos939GeneralSums_antitone_r r r₂ (r - 2) hrr S hS

/-- For every $r$, `Erdos939GeneralSums r 0` is empty. -/
theorem erdos939GeneralSums_zero_card_empty (r : ℕ) (S : Finset ℕ) :
    S ∉ Erdos939GeneralSums r 0 := by
  intro hS
  rw [mem_erdos939GeneralSums_iff] at hS
  have hempty : S = ∅ := Finset.card_eq_zero.mp hS.1
  exact not_coprime_empty_finset S hempty hS.2.1

/-- For every $r$, `Erdos939GeneralSums r 1` consists exclusively of the singleton `{1}`. -/
theorem erdos939GeneralSums_one_card_iff (r : ℕ) (S : Finset ℕ) :
    S ∈ Erdos939GeneralSums r 1 ↔ S = {1} := by
  rw [mem_erdos939GeneralSums_iff]
  constructor
  · rintro ⟨hcard, hcop, -, -⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    have ha : a = 1 := (coprime_singleton_iff_eq_one a).mp hcop
    rw [ha]
  · rintro rfl
    simp [coprime_singleton_iff_eq_one, Nat.Full.one_right]

/-- If `p` divides the total sum of `S` and every element of `S.erase s₀`, then `p` divides `s₀`. -/
theorem dvd_target_of_dvd_sum_and_dvd_erase (S : Finset ℕ) (s₀ p : ℕ)
    (hs₀ : s₀ ∈ S) (hsum : p ∣ ∑ s ∈ S, s) (herase : ∀ s ∈ S.erase s₀, p ∣ s) :
    p ∣ s₀ := by
  have hsplit : s₀ + ∑ s ∈ S.erase s₀, s = ∑ s ∈ S, s := Finset.add_sum_erase S id hs₀
  rw [← hsplit] at hsum
  have hdvd_erase : p ∣ ∑ s ∈ S.erase s₀, s := Finset.dvd_sum herase
  exact (Nat.dvd_add_left hdvd_erase).mp hsum

/--
**Prime-Sharing Obstruction:** In any coprime set `S`, if a prime `p` divides every summand in
`S.erase s₀`, then `p` divides neither `s₀` nor the total sum `∑ s ∈ S, s`.
-/
theorem not_dvd_sum_of_coprime_of_dvd_erase (S : Finset ℕ) (s₀ p : ℕ)
    (hcop : S.Coprime) (hs₀ : s₀ ∈ S) (hp : p.Prime)
    (herase : ∀ s ∈ S.erase s₀, p ∣ s) :
    ¬ p ∣ ∑ s ∈ S, s ∧ ¬ p ∣ s₀ := by
  have hnot_s₀ : ¬ p ∣ s₀ := by
    intro hps₀
    have hall : ∀ s ∈ S, p ∣ s := by
      intro s hs
      by_cases h : s = s₀
      · subst h; exact hps₀
      · exact herase s (Finset.mem_erase.mpr ⟨h, hs⟩)
    exact not_coprime_of_common_divisor S p hp.one_lt hall hcop
  refine ⟨?_, hnot_s₀⟩
  intro hsum
  exact hnot_s₀ (dvd_target_of_dvd_sum_and_dvd_erase S s₀ p hs₀ hsum herase)

/-- For `S ∈ Erdos939Sums r`, any prime `p` dividing `∑ s ∈ S, s` satisfies `p ^ r ∣ ∑ s ∈ S, s`. -/
theorem pow_dvd_sum_of_mem_erdos939Sums_of_dvd (r : ℕ) (S : Finset ℕ)
    (hS : S ∈ Erdos939Sums r) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ ∑ s ∈ S, s) :
    p ^ r ∣ ∑ s ∈ S, s := by
  by_cases hzero : ∑ s ∈ S, s = 0
  · rw [hzero]; exact dvd_zero (p ^ r)
  · exact hS.2.2.1 p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hzero⟩)

/-- For `S ∈ Erdos939Sums r` and `s ∈ S`, any prime `p ∣ s` satisfies `p ^ r ∣ s`. -/
theorem pow_dvd_summand_of_mem_erdos939Sums_of_dvd (r : ℕ) (S : Finset ℕ)
    (hS : S ∈ Erdos939Sums r) (s p : ℕ) (hs : s ∈ S) (hp : p.Prime) (hdvd : p ∣ s) :
    p ^ r ∣ s := by
  have hpos := (hS.2.2.2 s hs).1
  have hfull := (hS.2.2.2 s hs).2
  exact hfull p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, by omega⟩)

/-- If a prime `p` divides `n` but `n % p ^ r ≠ 0`, then `n` is not $r$-powerful. -/
theorem not_full_of_dvd_of_mod_pow_ne_zero (r p n : ℕ) (hp : p.Prime)
    (hdvd : p ∣ n) (hmod : n % p ^ r ≠ 0) : ¬ r.Full n := by
  intro hfull
  have hn0 : n ≠ 0 := by
    intro h0; subst h0; simp at hmod
  have hpr : p ^ r ∣ n := hfull p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn0⟩)
  exact hmod (Nat.mod_eq_zero_of_dvd hpr)

/-- Every exponent $m \ge r \ge 1$ decomposes as $(q - 1)r + (r + \text{rem})$ with $q \ge 1$ and $\text{rem} < r$. -/
theorem frobenius_exponent_r_basis (r m : ℕ) (hr : 1 ≤ r) (hm : r ≤ m) :
    ∃ q rem : ℕ, 1 ≤ q ∧ rem < r ∧ m = (q - 1) * r + (r + rem) := by
  refine ⟨m / r, m % r, Nat.div_pos hm hr, Nat.mod_lt m hr, ?_⟩
  have hdiv := Nat.div_add_mod m r
  have h1 : 1 ≤ m / r := Nat.div_pos hm hr
  calc m = r * (m / r) + m % r := hdiv.symm
    _ = (m / r - 1 + 1) * r + m % r := by
      rw [Nat.sub_add_cancel h1, mul_comm]
    _ = (m / r - 1) * r + (r + m % r) := by ring

/-- If `Nat.Coprime a b`, then both `a` and `b` are coprime to `a + b`. -/
theorem coprime_add_self_left_and_right (a b : ℕ) (hcop : Nat.Coprime a b) :
    Nat.Coprime a (a + b) ∧ Nat.Coprime b (a + b) := by
  refine ⟨?_, ?_⟩
  · exact Nat.coprime_self_add_right.mpr hcop
  · rw [add_comm]
    exact Nat.coprime_self_add_right.mpr hcop.symm

/-- For coprime `a` and `b`, the prime factor sets of `a`, `b`, and `a + b` are pairwise disjoint. -/
theorem disjoint_primeFactors_of_coprime_sum (a b : ℕ) (hcop : Nat.Coprime a b) :
    Disjoint a.primeFactors b.primeFactors ∧
      Disjoint a.primeFactors (a + b).primeFactors ∧
      Disjoint b.primeFactors (a + b).primeFactors := by
  have hab := coprime_add_self_left_and_right a b hcop
  exact ⟨Nat.Coprime.disjoint_primeFactors hcop,
    Nat.Coprime.disjoint_primeFactors hab.1,
    Nat.Coprime.disjoint_primeFactors hab.2⟩

/-- If `a > 0`, `Nat.Coprime a b`, and `a + b` is $r$-powerful with $r \ge 2$, then `a ≠ b`. -/
theorem ne_of_coprime_of_full_add (r a b : ℕ) (hr : 2 ≤ r) (ha : 0 < a)
    (hcop : Nat.Coprime a b) (hsum : r.Full (a + b)) : a ≠ b := by
  rintro rfl
  have ha1 : a = 1 := by simpa [Nat.Coprime] using hcop
  subst ha1
  exact not_full_prime_of_two_le r 2 hr Nat.prime_two hsum

/-- Characterization of 2-summand membership `{a, b} ∈ Erdos939GeneralSums r 2` for $r \ge 2$. -/
theorem pair_mem_erdos939GeneralSums_two_iff (r a b : ℕ) (hr : 2 ≤ r) :
    ({a, b} : Finset ℕ) ∈ Erdos939GeneralSums r 2 ↔
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ r.Full a ∧ r.Full b ∧ r.Full (a + b) := by
  rw [mem_erdos939GeneralSums_iff]
  constructor
  · rintro ⟨hcard, hcop, hsum, hall⟩
    have hab_ne : a ≠ b := by
      intro h; subst h; simp at hcard
    rw [Finset.Coprime_pair_iff {a, b} a b rfl] at hcop
    rw [Finset.sum_pair hab_ne] at hsum
    have ha := hall a (by simp)
    have hb := hall b (by simp)
    exact ⟨ha.1, hb.1, hcop, ha.2, hb.2, hsum⟩
  · rintro ⟨ha, hb, hcop, hfa, hfb, hsum⟩
    have hab_ne : a ≠ b := ne_of_coprime_of_full_add r a b hr ha hcop hsum
    refine ⟨Finset.card_pair hab_ne, (Finset.Coprime_pair_iff {a, b} a b rfl).mpr hcop, ?_, ?_⟩
    · rwa [Finset.sum_pair hab_ne]
    · intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact ⟨ha, hfa⟩
      · exact ⟨hb, hfb⟩

/-- Every odd $r$-powerful integer $n > 1$ is at least $3^r$. -/
theorem three_pow_le_of_full_of_odd_gt_one (r n : ℕ) (hn : 1 < n)
    (hodd : ¬ 2 ∣ n) (hfull : r.Full n) : 3 ^ r ≤ n := by
  have hmin_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hmin_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hne2 : n.minFac ≠ 2 := by
    intro h2; rw [h2] at hmin_dvd; exact hodd hmin_dvd
  have h3 : 3 ≤ n.minFac := by
    have := hmin_prime.two_le
    omega
  have hmem : n.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hmin_prime, hmin_dvd, by omega⟩
  have hpow_dvd : n.minFac ^ r ∣ n := hfull n.minFac hmem
  calc 3 ^ r ≤ n.minFac ^ r := Nat.pow_le_pow_left h3 r
    _ ≤ n := Nat.le_of_dvd (by omega) hpow_dvd

/-- Every positive coprime $r$-powerful pair $(a, b)$ ($r \ge 2$) with $r$-powerful sum satisfies $3^r \le a + b$. -/
theorem three_pow_le_sum_of_coprime_full_pair (r a b : ℕ) (hr : 2 ≤ r)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hfa : r.Full a) (hfb : r.Full b) (hfs : r.Full (a + b)) :
    3 ^ r ≤ a + b := by
  have hab_ne : a ≠ b := ne_of_coprime_of_full_add r a b hr ha hcop hfs
  by_cases h2 : 2 ∣ a + b
  · have hnot2a : ¬ 2 ∣ a := by
      intro h2a
      have h2b : 2 ∣ b := (Nat.dvd_add_right h2a).mp h2
      have h21 : 2 ∣ 1 := hcop ▸ Nat.dvd_gcd h2a h2b
      omega
    have hnot2b : ¬ 2 ∣ b := by
      intro h2b
      have h2a : 2 ∣ a := (Nat.dvd_add_left h2b).mp h2
      exact hnot2a h2a
    have hgt1 : 1 < a ∨ 1 < b := by omega
    rcases hgt1 with ha1 | hb1
    · have := three_pow_le_of_full_of_odd_gt_one r a ha1 hnot2a hfa
      omega
    · have := three_pow_le_of_full_of_odd_gt_one r b hb1 hnot2b hfb
      omega
  · exact three_pow_le_of_full_of_odd_gt_one r (a + b) (by omega) h2 hfs

/--
**Radical / $abc$ Product Bound:** If $a, b > 0$ and $a, b, a+b$ are $r$-powerful with prime factors
$p \in a.\text{primeFactors}$, $q \in b.\text{primeFactors}$, $l \in (a+b).\text{primeFactors}$,
then $(p \cdot q \cdot l)^r \le a b (a + b) < (a + b)^3$.
-/
theorem pow_mul_le_and_lt_cube_of_full_triple (r a b p q l : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hfa : r.Full a) (hfb : r.Full b) (hfs : r.Full (a + b))
    (hp : p ∈ a.primeFactors) (hq : q ∈ b.primeFactors) (hl : l ∈ (a + b).primeFactors) :
    (p * q * l) ^ r ≤ a * b * (a + b) ∧ (p * q * l) ^ r < (a + b) ^ 3 := by
  have hpa : p ^ r ≤ a := Nat.le_of_dvd ha (hfa p hp)
  have hqb : q ^ r ≤ b := Nat.le_of_dvd hb (hfb q hq)
  have hls : l ^ r ≤ a + b := Nat.le_of_dvd (by omega) (hfs l hl)
  have hprod : (p * q * l) ^ r ≤ a * b * (a + b) := by
    rw [mul_pow, mul_pow]
    exact Nat.mul_le_mul (Nat.mul_le_mul hpa hqb) hls
  have hcube : a * b * (a + b) < (a + b) ^ 3 := by
    have hexp : (a + b) ^ 3 = a * b * (a + b) + (a ^ 3 + b ^ 3 + 2 * a ^ 2 * b + 2 * a * b ^ 2) := by
      ring
    have hpos : 0 < a ^ 3 + b ^ 3 + 2 * a ^ 2 * b + 2 * a * b ^ 2 := by positivity
    omega
  exact ⟨hprod, lt_of_le_of_lt hprod hcube⟩

/-- Exact membership criterion for `{a, b} ∈ Erdos939Sums 4`. -/
theorem pair_mem_erdos939Sums_four_iff (a b : ℕ) :
    ({a, b} : Finset ℕ) ∈ Erdos939Sums 4 ↔
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ (4).Full a ∧ (4).Full b ∧ (4).Full (a + b) := by
  rw [← mem_erdos939GeneralSums_r_sub_two_iff 4]
  exact pair_mem_erdos939GeneralSums_two_iff 4 a b (by omega)

/-- `(Erdos939Sums 4).Nonempty` is equivalent to the existence of a positive coprime $4$-powerful pair with $4$-powerful sum. -/
theorem erdos939Sums_four_nonempty_iff_exists_pair (P : Prop)
    (hP : P ↔ (Erdos939Sums 4).Nonempty) :
    P ↔ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      (4).Full a ∧ (4).Full b ∧ (4).Full (a + b) := by
  rw [hP]
  constructor
  · rintro ⟨S, hS⟩
    have hcard : S.card = 2 := hS.1
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    exact ⟨a, b, (pair_mem_erdos939Sums_four_iff a b).mp hS⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨{a, b}, (pair_mem_erdos939Sums_four_iff a b).mpr hab⟩

/-!
## Squarefree-Core Canonical Decomposition of $r$-Powerful Numbers and Modular Sieve Constraints on `Erdos939Sums 4`

This section establishes canonical core factorizations and modular congruences:
1. **Squarefree-Core Canonical Decomposition of $r$-Powerful Numbers:**
   - Explicit canonical base core `rFullBaseCore r n` and squarefree excess cores
     `rFullExcessCore r j n` ($1 \le j < r$).
   - Unconditional squarefreeness (`rFullExcessCore_squarefree`) and pairwise coprimality
     (`rFullExcessCore_coprime`) of the excess cores.
   - Exact canonical product identity (`rFullBaseCore_mul_excess_prod_eq_self`):
     $$(rFullBaseCore\ r\ n)^r \cdot \prod_{j \in \text{Ico } 1\ r} (rFullExcessCore\ r\ j\ n)^{r + j} = n$$
     for every $r \ge 1$ and positive $r$-powerful integer $n$.
   - Complete bidirectional characterizations of positive $r$-powerful numbers
     (`r_full_iff_exists_squarefree_cores`) and explicit specializations at $r = 2$
     ($n = u^2 v^3$), $r = 3$ ($n = u^3 v_1^4 v_2^5$), and $r = 4$ ($n = u^4 v_1^5 v_2^6 v_3^7$).
2. **Parity Partition, Sharpened Non-Catalan Lower Bounds, and Prime-Power Sieve:**
   - Exact parity partition (`even_xor_of_coprime_sum`) and $2^r$-divisibility of the unique
     even element in any coprime $r$-powerful triple (`two_pow_dvd_unique_even_of_coprime_full_triple`,
     `sixteen_dvd_unique_even_of_mem_erdos939Sums_four`).
   - Sharpened non-Catalan lower bound $2^r + 3^r \le a + b$ for all coprime $r$-powerful
     summands $a, b > 1$ (`two_pow_add_three_pow_le_sum_of_coprime_full_gt_one`).
   - Prime-power sum sieve (`prime_pow_sieve_of_dvd_sum_of_coprime_full`) and summand
     congruence (`summand_modEq_of_prime_dvd_left`).
3. **Squarefree-Core Modular Congruences and Odd-Power Sum Obstructions:**
   - Mod-8, mod-16, mod-3, and mod-5 reductions of the $4$-powerful canonical core
     $u^4 v_1^5 v_2^6 v_3^7$.
   - Universal parity obstructions $\neg r.\text{Full}(x^2 + y^2)$, $\neg r.\text{Full}(x^4 + y^4)$,
     and $\{x^4, y^4\} \notin \text{Erdos939Sums } 4$ for odd $x, y$, paired with the positive
     Catalan control $\{1, 8\} \in \text{Erdos939GeneralSums } 2\ 2$.
-/

/-- Canonical $r$-th power base factor of a natural number `n`. -/
def rFullBaseCore (r n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors,
    p ^ (if n.factorization p % r = 0 then n.factorization p / r else n.factorization p / r - 1)

/-- Canonical $j$-th squarefree excess core ($1 \le j < r$) of a natural number `n`. -/
def rFullExcessCore (r j n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p % r = j), p

/-- Canonical exponent decomposition in the $\{r, r+1, \dots, 2r-1\}$ basis for $1 \le r \le m$. -/
theorem r_full_exponent_canonical_split (r m : ℕ) (hr : 1 ≤ r) (hm : r ≤ m) :
    (if m % r = 0 then m / r else m / r - 1) * r +
      (if m % r = 0 then 0 else r + m % r) = m := by
  have hdiv : (m / r) * r + m % r = m := by
    rw [mul_comm]
    exact Nat.div_add_mod m r
  have hq : 1 ≤ m / r := Nat.div_pos hm hr
  split_ifs with h0
  · omega
  · have hsub : (m / r - 1) * r + r = (m / r) * r := by
      calc (m / r - 1) * r + r = (m / r - 1 + 1) * r := by ring
        _ = (m / r) * r := by rw [Nat.sub_add_cancel hq]
    omega

/-- Evaluation of the excess-exponent product over `j ∈ Finset.Ico 1 r`. -/
theorem prod_ico_excess_pow_eq (r m p : ℕ) (hr : 1 ≤ r) :
    (∏ j ∈ Finset.Ico 1 r, if m % r = j then p ^ (r + j) else 1) =
      p ^ (if m % r = 0 then 0 else r + m % r) := by
  split_ifs with h0
  · rw [pow_zero]
    refine Finset.prod_eq_one fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    have hne : m % r ≠ j := by omega
    simp [hne]
  · have hmem : m % r ∈ Finset.Ico 1 r := by
      rw [Finset.mem_Ico]
      have hlt : m % r < r := Nat.mod_lt m hr
      omega
    rw [Finset.prod_eq_single (m % r)]
    · simp
    · intro j _ hjne
      have : m % r ≠ j := Ne.symm hjne
      simp [this]
    · intro hnot
      exact False.elim (hnot hmem)

/-- Every product of primes over a `Finset ℕ` is squarefree. -/
theorem squarefree_finset_prod_of_prime (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons p T hpT ih =>
    rw [Finset.prod_cons]
    have hp : p.Prime := hprime p (Finset.mem_cons_self p T)
    have hT : ∀ q ∈ T, q.Prime := fun q hq => hprime q (Finset.mem_cons_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ T, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq_prime : q.Prime := hT q hq
      have hne : p ≠ q := fun h => hpT (h ▸ hq)
      exact (Nat.coprime_primes hp hq_prime).mpr hne
    exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ih hT⟩

/-- Products of primes over disjoint `Finset ℕ`s are coprime. -/
theorem coprime_finset_prod_of_disjoint_primes (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ q ∈ T, q.Prime) (hdisj : Disjoint S T) :
    Nat.Coprime (∏ p ∈ S, p) (∏ q ∈ T, q) := by
  refine Nat.Coprime.prod_left fun p hp => ?_
  refine Nat.Coprime.prod_right fun q hq => ?_
  have hne : p ≠ q := Finset.disjoint_left.mp hdisj hp ∘ (fun h => h ▸ hq)
  exact (Nat.coprime_primes (hS p hp) (hT q hq)).mpr hne

/-- Every canonical excess core `rFullExcessCore r j n` is squarefree. -/
theorem rFullExcessCore_squarefree (r j n : ℕ) :
    Squarefree (rFullExcessCore r j n) := by
  unfold rFullExcessCore
  refine squarefree_finset_prod_of_prime _ fun p hp => ?_
  rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
  exact hp.1.1

/-- Distinct canonical excess cores `rFullExcessCore r j₁ n` and `rFullExcessCore r j₂ n` are coprime. -/
theorem rFullExcessCore_coprime (r j₁ j₂ n : ℕ) (hne : j₁ ≠ j₂) :
    Nat.Coprime (rFullExcessCore r j₁ n) (rFullExcessCore r j₂ n) := by
  unfold rFullExcessCore
  refine coprime_finset_prod_of_disjoint_primes _ _
    (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1)
    (fun q hq => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1) ?_
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  rw [Finset.mem_filter] at hp₁ hp₂
  exact hne (hp₁.2.symm.trans hp₂.2)

/--
**Canonical Squarefree-Core Decomposition Identity:** For every $r \ge 1$ and every positive
$r$-powerful integer $n$,
$$(rFullBaseCore\ r\ n)^r \cdot \prod_{j \in \text{Ico } 1\ r} (rFullExcessCore\ r\ j\ n)^{r + j} = n.$$
-/
theorem rFullBaseCore_mul_excess_prod_eq_self (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n)
    (hfull : r.Full n) :
    (rFullBaseCore r n) ^ r * ∏ j ∈ Finset.Ico 1 r, (rFullExcessCore r j n) ^ (r + j) = n := by
  unfold rFullBaseCore rFullExcessCore
  rw [← Finset.prod_pow]
  have hexcess :
      (∏ j ∈ Finset.Ico 1 r, (∏ p ∈ n.primeFactors.filter (fun p => n.factorization p % r = j), p) ^ (r + j)) =
        ∏ p ∈ n.primeFactors, p ^ (if n.factorization p % r = 0 then 0 else r + n.factorization p % r) := by
    calc
      (∏ j ∈ Finset.Ico 1 r, (∏ p ∈ n.primeFactors.filter (fun p => n.factorization p % r = j), p) ^ (r + j))
        = ∏ j ∈ Finset.Ico 1 r, ∏ p ∈ n.primeFactors, (if n.factorization p % r = j then p ^ (r + j) else 1) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← Finset.prod_pow, Finset.prod_filter]
      _ = ∏ p ∈ n.primeFactors, ∏ j ∈ Finset.Ico 1 r, (if n.factorization p % r = j then p ^ (r + j) else 1) :=
          Finset.prod_comm
      _ = ∏ p ∈ n.primeFactors, p ^ (if n.factorization p % r = 0 then 0 else r + n.factorization p % r) := by
          refine Finset.prod_congr rfl fun p _ => ?_
          exact prod_ico_excess_pow_eq r (n.factorization p) p hr
  rw [hexcess, ← Finset.prod_mul_distrib]
  calc
    (∏ x ∈ n.primeFactors,
        (x ^ (if n.factorization x % r = 0 then n.factorization x / r else n.factorization x / r - 1)) ^ r *
          x ^ (if n.factorization x % r = 0 then 0 else r + n.factorization x % r))
      = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        rw [← pow_mul, ← pow_add]
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hdvd : p ^ r ∣ n := hfull p hp
        have hrm : r ≤ n.factorization p :=
          (hpp.pow_dvd_iff_le_factorization (by omega)).mp hdvd
        rw [r_full_exponent_canonical_split r (n.factorization p) hr hrm]
    _ = n := Nat.factorization_prod_pow_eq_self (by omega)

/-- Every shifted power $v^{r + j}$ is $r$-powerful. -/
theorem full_of_pow_r_add_offset (r j v : ℕ) :
    r.Full (v ^ (r + j)) :=
  Nat.full_of_le_full r (v ^ (r + j)) (Nat.le_add_right r j) (e939_full_pow (r + j) v)

/-- Any `Finset` product of $r$-powerful integers is $r$-powerful. -/
theorem full_finset_prod (r : ℕ) (I : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ j ∈ I, r.Full (f j)) :
    r.Full (∏ j ∈ I, f j) := by
  induction I using Finset.cons_induction with
  | empty => simpa using Nat.Full.one_right r
  | cons j J hjJ ih =>
    rw [Finset.prod_cons]
    exact full_mul_of_full r (f j) (∏ i ∈ J, f i)
      (hf j (Finset.mem_cons_self j J))
      (ih fun i hi => hf i (Finset.mem_cons_of_mem hi))

/-- Any product of the form $u^r \prod_{j \in \text{Ico } 1\ r} (v\ j)^{r + j}$ is $r$-powerful. -/
theorem full_canonical_core_product (r u : ℕ) (v : ℕ → ℕ) :
    r.Full (u ^ r * ∏ j ∈ Finset.Ico 1 r, (v j) ^ (r + j)) := by
  refine full_mul_of_full r (u ^ r) _ (e939_full_pow r u) ?_
  refine full_finset_prod r (Finset.Ico 1 r) (fun j => (v j) ^ (r + j)) ?_
  intro j _
  exact full_of_pow_r_add_offset r j (v j)

/--
**Universal Squarefree-Core Characterization of $r$-Powerful Numbers:** For $r \ge 1$ and $n > 0$,
`r.Full n` holds if and only if $n = u^r \prod_{j=1}^{r-1} (v\ j)^{r+j}$ for some $u$ and
pairwise coprime squarefree cores $v(1), \dots, v(r-1)$.
-/
theorem r_full_iff_exists_squarefree_cores (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n) :
    r.Full n ↔
      ∃ (u : ℕ) (v : ℕ → ℕ),
        (∀ j ∈ Finset.Ico 1 r, Squarefree (v j)) ∧
        (∀ j₁ ∈ Finset.Ico 1 r, ∀ j₂ ∈ Finset.Ico 1 r, j₁ ≠ j₂ → Nat.Coprime (v j₁) (v j₂)) ∧
        u ^ r * ∏ j ∈ Finset.Ico 1 r, (v j) ^ (r + j) = n := by
  constructor
  · intro hfull
    refine ⟨rFullBaseCore r n, fun j => rFullExcessCore r j n, ?_, ?_, ?_⟩
    · intro j _
      exact rFullExcessCore_squarefree r j n
    · intro j₁ _ j₂ _ hne
      exact rFullExcessCore_coprime r j₁ j₂ n hne
    · exact rFullBaseCore_mul_excess_prod_eq_self r n hr hn hfull
  · rintro ⟨u, v, -, -, rfl⟩
    exact full_canonical_core_product r u v

/-- Canonical squarefree-core characterization of positive $2$-powerful numbers ($n = u^2 v^3$). -/
theorem two_full_iff_exists_canonical_core (n : ℕ) (hn : 0 < n) :
    (2).Full n ↔ ∃ u v : ℕ, Squarefree v ∧ u ^ 2 * v ^ 3 = n := by
  constructor
  · intro hfull
    refine ⟨rFullBaseCore 2 n, rFullExcessCore 2 1 n, rFullExcessCore_squarefree 2 1 n, ?_⟩
    have h := rFullBaseCore_mul_excess_prod_eq_self 2 n (by omega) hn hfull
    have hico : (Finset.Ico 1 2 : Finset ℕ) = {1} := by decide
    rw [hico, Finset.prod_singleton] at h
    exact h
  · rintro ⟨u, v, -, rfl⟩
    exact full_mul_pow_succ 2 u v

/-- Canonical squarefree-core characterization of positive $3$-powerful numbers ($n = u^3 v_1^4 v_2^5$). -/
theorem three_full_iff_exists_canonical_cores (n : ℕ) (hn : 0 < n) :
    (3).Full n ↔
      ∃ u v₁ v₂ : ℕ, Squarefree v₁ ∧ Squarefree v₂ ∧ Nat.Coprime v₁ v₂ ∧
        u ^ 3 * v₁ ^ 4 * v₂ ^ 5 = n := by
  constructor
  · intro hfull
    refine ⟨rFullBaseCore 3 n, rFullExcessCore 3 1 n, rFullExcessCore 3 2 n,
      rFullExcessCore_squarefree 3 1 n, rFullExcessCore_squarefree 3 2 n,
      rFullExcessCore_coprime 3 1 2 n (by omega), ?_⟩
    have h := rFullBaseCore_mul_excess_prod_eq_self 3 n (by omega) hn hfull
    have hico : (Finset.Ico 1 3 : Finset ℕ) = {1, 2} := by decide
    rw [hico, Finset.prod_pair (by omega), ← mul_assoc] at h
    exact h
  · rintro ⟨u, v₁, v₂, -, -, -, rfl⟩
    refine full_mul_of_full 3 (u ^ 3 * v₁ ^ 4) (v₂ ^ 5) ?_ (full_of_pow_r_add_offset 3 2 v₂)
    exact full_mul_of_full 3 (u ^ 3) (v₁ ^ 4) (e939_full_pow 3 u) (full_of_pow_r_add_offset 3 1 v₁)

/-- Canonical squarefree-core characterization of positive $4$-powerful numbers ($n = u^4 v_1^5 v_2^6 v_3^7$). -/
theorem four_full_iff_exists_canonical_cores (n : ℕ) (hn : 0 < n) :
    (4).Full n ↔
      ∃ u v₁ v₂ v₃ : ℕ, Squarefree v₁ ∧ Squarefree v₂ ∧ Squarefree v₃ ∧
        Nat.Coprime v₁ v₂ ∧ Nat.Coprime v₁ v₃ ∧ Nat.Coprime v₂ v₃ ∧
        u ^ 4 * v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7 = n := by
  constructor
  · intro hfull
    refine ⟨rFullBaseCore 4 n, rFullExcessCore 4 1 n, rFullExcessCore 4 2 n, rFullExcessCore 4 3 n,
      rFullExcessCore_squarefree 4 1 n, rFullExcessCore_squarefree 4 2 n, rFullExcessCore_squarefree 4 3 n,
      rFullExcessCore_coprime 4 1 2 n (by omega),
      rFullExcessCore_coprime 4 1 3 n (by omega),
      rFullExcessCore_coprime 4 2 3 n (by omega), ?_⟩
    have h := rFullBaseCore_mul_excess_prod_eq_self 4 n (by omega) hn hfull
    have hico : (Finset.Ico 1 4 : Finset ℕ) = insert 1 {2, 3} := by decide
    rw [hico, Finset.prod_insert (by decide), Finset.prod_pair (by omega)] at h
    calc (rFullBaseCore 4 n) ^ 4 * (rFullExcessCore 4 1 n) ^ 5 * (rFullExcessCore 4 2 n) ^ 6 *
          (rFullExcessCore 4 3 n) ^ 7
        = (rFullBaseCore 4 n) ^ 4 *
            ((rFullExcessCore 4 1 n) ^ (4 + 1) *
              ((rFullExcessCore 4 2 n) ^ (4 + 2) * (rFullExcessCore 4 3 n) ^ (4 + 3))) := by ring
      _ = n := h
  · rintro ⟨u, v₁, v₂, v₃, -, -, -, -, -, -, rfl⟩
    refine full_mul_of_full 4 (u ^ 4 * v₁ ^ 5 * v₂ ^ 6) (v₃ ^ 7) ?_ (full_of_pow_r_add_offset 4 3 v₃)
    refine full_mul_of_full 4 (u ^ 4 * v₁ ^ 5) (v₂ ^ 6) ?_ (full_of_pow_r_add_offset 4 2 v₂)
    exact full_mul_of_full 4 (u ^ 4) (v₁ ^ 5) (e939_full_pow 4 u) (full_of_pow_r_add_offset 4 1 v₁)

/-- **Exact Parity Partition:** In any coprime pair `(a, b)`, exactly one of `a`, `b`, `a + b` is even. -/
theorem even_xor_of_coprime_sum (a b : ℕ) (hcop : Nat.Coprime a b) :
    (2 ∣ a ∧ ¬ 2 ∣ b ∧ ¬ 2 ∣ (a + b)) ∨
      (2 ∣ b ∧ ¬ 2 ∣ a ∧ ¬ 2 ∣ (a + b)) ∨
      (2 ∣ (a + b) ∧ ¬ 2 ∣ a ∧ ¬ 2 ∣ b) := by
  have hnot_both : ¬ (2 ∣ a ∧ 2 ∣ b) := by
    rintro ⟨ha, hb⟩
    have h21 : 2 ∣ 1 := hcop ▸ Nat.dvd_gcd ha hb
    omega
  by_cases ha : 2 ∣ a
  · left
    have hb : ¬ 2 ∣ b := fun h => hnot_both ⟨ha, h⟩
    refine ⟨ha, hb, ?_⟩
    intro hab
    exact hb ((Nat.dvd_add_right ha).mp hab)
  · by_cases hb : 2 ∣ b
    · right; left
      refine ⟨hb, ha, ?_⟩
      intro hab
      exact ha ((Nat.dvd_add_left hb).mp hab)
    · right; right
      refine ⟨?_, ha, hb⟩
      omega

/-- In any positive coprime $r$-powerful triple `(a, b, a + b)`, the unique even term is divisible by `2 ^ r`. -/
theorem two_pow_dvd_unique_even_of_coprime_full_triple (r a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hfa : r.Full a) (hfb : r.Full b) (hfs : r.Full (a + b)) :
    (2 ^ r ∣ a ∧ ¬ 2 ∣ b ∧ ¬ 2 ∣ (a + b)) ∨
      (2 ^ r ∣ b ∧ ¬ 2 ∣ a ∧ ¬ 2 ∣ (a + b)) ∨
      (2 ^ r ∣ (a + b) ∧ ¬ 2 ∣ a ∧ ¬ 2 ∣ b) := by
  rcases even_xor_of_coprime_sum a b hcop with ⟨h2a, hnb, hns⟩ | ⟨h2b, hna, hns⟩ | ⟨h2s, hna, hnb⟩
  · left
    exact ⟨hfa 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2a, by omega⟩), hnb, hns⟩
  · right; left
    exact ⟨hfb 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2b, by omega⟩), hna, hns⟩
  · right; right
    exact ⟨hfs 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2s, by omega⟩), hna, hnb⟩

/-- For any `{a, b} ∈ Erdos939Sums 4`, one of `a`, `b`, `a + b` is divisible by `16` and the other two are odd. -/
theorem sixteen_dvd_unique_even_of_mem_erdos939Sums_four (a b : ℕ)
    (hmem : ({a, b} : Finset ℕ) ∈ Erdos939Sums 4) :
    (16 ∣ a ∧ ¬ 2 ∣ b ∧ ¬ 2 ∣ (a + b)) ∨
      (16 ∣ b ∧ ¬ 2 ∣ a ∧ ¬ 2 ∣ (a + b)) ∨
      (16 ∣ (a + b) ∧ ¬ 2 ∣ a ∧ ¬ 2 ∣ b) := by
  rcases (pair_mem_erdos939Sums_four_iff a b).mp hmem with ⟨ha, hb, hcop, hfa, hfb, hfs⟩
  simpa using two_pow_dvd_unique_even_of_coprime_full_triple 4 a b ha hb hcop hfa hfb hfs

/-- **Sharpened Non-Catalan Lower Bound:** Any two coprime $r$-powerful integers $a, b > 1$ satisfy $2^r + 3^r \le a + b$. -/
theorem two_pow_add_three_pow_le_sum_of_coprime_full_gt_one (r a b : ℕ)
    (ha : 1 < a) (hb : 1 < b) (hcop : Nat.Coprime a b)
    (hfa : r.Full a) (hfb : r.Full b) :
    2 ^ r + 3 ^ r ≤ a + b := by
  by_cases h2a : 2 ∣ a
  · have hnot2b : ¬ 2 ∣ b := by
      intro h2b
      have h21 : 2 ∣ 1 := hcop ▸ Nat.dvd_gcd h2a h2b
      omega
    have ha_le : 2 ^ r ≤ a := two_pow_le_of_full_of_gt_one r a ha hfa
    have hb_le : 3 ^ r ≤ b := three_pow_le_of_full_of_odd_gt_one r b hb hnot2b hfb
    omega
  · have ha_le : 3 ^ r ≤ a := three_pow_le_of_full_of_odd_gt_one r a ha h2a hfa
    have hb_le : 2 ^ r ≤ b := two_pow_le_of_full_of_gt_one r b hb hfb
    omega

/-- **Prime-Power Sum Sieve:** Any prime `l ∣ a + b` in a coprime triple with $r$-powerful sum satisfies `l ^ r ∣ a + b` and `Coprime a (l ^ r)`, `Coprime b (l ^ r)`. -/
theorem prime_pow_sieve_of_dvd_sum_of_coprime_full (r a b l : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) (hfs : r.Full (a + b))
    (hl : l.Prime) (hdvd : l ∣ a + b) :
    l ^ r ∣ a + b ∧ (a + b) % l ^ r = 0 ∧
      Nat.Coprime a (l ^ r) ∧ Nat.Coprime b (l ^ r) ∧ ¬ l ∣ a ∧ ¬ l ∣ b := by
  have hlr : l ^ r ∣ a + b :=
    hfs l (Nat.mem_primeFactors.mpr ⟨hl, hdvd, by omega⟩)
  have hmod : (a + b) % l ^ r = 0 := Nat.mod_eq_zero_of_dvd hlr
  have hnot_a : ¬ l ∣ a := by
    intro hla
    have hlb : l ∣ b := (Nat.dvd_add_right hla).mp hdvd
    have hl1 : l ∣ 1 := hcop ▸ Nat.dvd_gcd hla hlb
    have hle1 : l ≤ 1 := Nat.le_of_dvd Nat.zero_lt_one hl1
    have := hl.two_le
    omega
  have hnot_b : ¬ l ∣ b := by
    intro hlb
    have hla : l ∣ a := (Nat.dvd_add_left hlb).mp hdvd
    exact hnot_a hla
  have hcop_al : Nat.Coprime a l := (hl.coprime_iff_not_dvd.mpr hnot_a).symm
  have hcop_bl : Nat.Coprime b l := (hl.coprime_iff_not_dvd.mpr hnot_b).symm
  exact ⟨hlr, hmod, hcop_al.pow_right r, hcop_bl.pow_right r, hnot_a, hnot_b⟩

/-- **Prime-Power Summand Congruence:** Any prime `p ∣ a` of a positive $r$-powerful summand forces `p ^ r ∣ a` and `a + b ≡ b [MOD p ^ r]`. -/
theorem summand_modEq_of_prime_dvd_left (r a b p : ℕ)
    (ha : 0 < a) (hfa : r.Full a) (hp : p.Prime) (hdvd : p ∣ a) :
    p ^ r ∣ a ∧ a + b ≡ b [MOD p ^ r] := by
  have hpr : p ^ r ∣ a := hfa p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, by omega⟩)
  refine ⟨hpr, ?_⟩
  have h0 : a ≡ 0 [MOD p ^ r] := Nat.modEq_zero_iff_dvd.mpr hpr
  simpa using h0.add_right b

/-- Universal mod-8 and mod-16 power congruences for odd natural numbers. -/
theorem odd_pow_mod_eight_and_sixteen (x : ℕ) (hx : ¬ 2 ∣ x) :
    x ^ 2 % 8 = 1 ∧ x ^ 4 % 8 = 1 ∧ x ^ 5 % 8 = x % 8 ∧
      x ^ 6 % 8 = 1 ∧ x ^ 7 % 8 = x % 8 ∧ x ^ 4 % 16 = 1 := by
  have hlt8 : x % 8 < 8 := Nat.mod_lt x (by omega)
  have hodd8 : (x % 8) % 2 = 1 := by omega
  have hlt16 : x % 16 < 16 := Nat.mod_lt x (by omega)
  have hodd16 : (x % 16) % 2 = 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.pow_mod]; generalize x % 8 = r at hlt8 hodd8 ⊢; decide +revert
  · rw [Nat.pow_mod]; generalize x % 8 = r at hlt8 hodd8 ⊢; decide +revert
  · rw [Nat.pow_mod]; generalize x % 8 = r at hlt8 hodd8 ⊢; decide +revert
  · rw [Nat.pow_mod]; generalize x % 8 = r at hlt8 hodd8 ⊢; decide +revert
  · rw [Nat.pow_mod]; generalize x % 8 = r at hlt8 hodd8 ⊢; decide +revert
  · rw [Nat.pow_mod]; generalize x % 16 = r at hlt16 hodd16 ⊢; decide +revert

/-- **Mod-8 Squarefree-Core Congruence Law:** Every odd $4$-powerful core product reduces modulo $8$ to `v₁ * v₃`. -/
theorem odd_four_full_core_mod_eight (u v₁ v₂ v₃ : ℕ)
    (hu : ¬ 2 ∣ u) (hv₁ : ¬ 2 ∣ v₁) (hv₂ : ¬ 2 ∣ v₂) (hv₃ : ¬ 2 ∣ v₃) :
    (u ^ 4 * v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7) % 8 = (v₁ * v₃) % 8 := by
  rw [Nat.mul_mod, Nat.mul_mod (u ^ 4 * v₁ ^ 5), Nat.mul_mod (u ^ 4),
    (odd_pow_mod_eight_and_sixteen u hu).2.1,
    (odd_pow_mod_eight_and_sixteen v₁ hv₁).2.2.1,
    (odd_pow_mod_eight_and_sixteen v₂ hv₂).2.2.2.1,
    (odd_pow_mod_eight_and_sixteen v₃ hv₃).2.2.2.2.1]
  simp [Nat.mul_mod]

/-- **Mod-16 Base-Core Elimination Law:** For any odd base `u`, `u ^ 4 * v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7 ≡ v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7 (mod 16)`. -/
theorem odd_four_full_core_mod_sixteen (u v₁ v₂ v₃ : ℕ) (hu : ¬ 2 ∣ u) :
    (u ^ 4 * v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7) % 16 = (v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7) % 16 := by
  have h1 : u ^ 4 * v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7 = u ^ 4 * (v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7) := by ring
  rw [h1, Nat.mul_mod, (odd_pow_mod_eight_and_sixteen u hu).2.2.2.2.2, one_mul, Nat.mod_mod]

/-- **Mod-3 and Mod-5 Squarefree-Core Congruence Laws** for $4$-powerful core products. -/
theorem four_full_core_mod_three_and_five (u v₁ v₂ v₃ : ℕ) :
    (¬ 3 ∣ u → ¬ 3 ∣ v₁ → ¬ 3 ∣ v₂ → ¬ 3 ∣ v₃ →
      (u ^ 4 * v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7) % 3 = (v₁ * v₃) % 3) ∧
    (¬ 5 ∣ u → ¬ 5 ∣ v₁ → ¬ 5 ∣ v₂ → ¬ 5 ∣ v₃ →
      (u ^ 4 * v₁ ^ 5 * v₂ ^ 6 * v₃ ^ 7) % 5 = (v₁ * v₂ ^ 2 * v₃ ^ 3) % 5) := by
  have hmod3 : ∀ x : ℕ, ¬ 3 ∣ x →
      x ^ 4 % 3 = 1 ∧ x ^ 5 % 3 = x % 3 ∧ x ^ 6 % 3 = 1 ∧ x ^ 7 % 3 = x % 3 := by
    intro x hx
    have hlt : x % 3 < 3 := Nat.mod_lt x (by omega)
    have hne : x % 3 ≠ 0 := by omega
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [Nat.pow_mod]; generalize x % 3 = r at hlt hne ⊢; decide +revert)
  have hmod5 : ∀ x : ℕ, ¬ 5 ∣ x →
      x ^ 4 % 5 = 1 ∧ x ^ 5 % 5 = x % 5 ∧ x ^ 6 % 5 = x ^ 2 % 5 ∧ x ^ 7 % 5 = x ^ 3 % 5 := by
    intro x hx
    have hlt : x % 5 < 5 := Nat.mod_lt x (by omega)
    have hne : x % 5 ≠ 0 := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Nat.pow_mod]; generalize x % 5 = r at hlt hne ⊢; decide +revert
    · rw [Nat.pow_mod]; generalize x % 5 = r at hlt hne ⊢; decide +revert
    · rw [Nat.pow_mod, Nat.pow_mod x 2]; generalize x % 5 = r at hlt hne ⊢; decide +revert
    · rw [Nat.pow_mod, Nat.pow_mod x 3]; generalize x % 5 = r at hlt hne ⊢; decide +revert
  refine ⟨?_, ?_⟩
  · intro hu hv₁ hv₂ hv₃
    rw [Nat.mul_mod, Nat.mul_mod (u ^ 4 * v₁ ^ 5), Nat.mul_mod (u ^ 4),
      (hmod3 u hu).1, (hmod3 v₁ hv₁).2.1, (hmod3 v₂ hv₂).2.2.1, (hmod3 v₃ hv₃).2.2.2]
    simp [Nat.mul_mod]
  · intro hu hv₁ hv₂ hv₃
    rw [Nat.mul_mod, Nat.mul_mod (u ^ 4 * v₁ ^ 5), Nat.mul_mod (u ^ 4),
      (hmod5 u hu).1, (hmod5 v₁ hv₁).2.1, (hmod5 v₂ hv₂).2.2.1, (hmod5 v₃ hv₃).2.2.2]
    simp [Nat.mul_mod]

/--
**Universal Odd-Power Obstructions & Controls:** For any odd `x, y` and `r ≥ 2`, neither `x ^ 2 + y ^ 2`
nor `x ^ 4 + y ^ 4` is $r$-powerful, `{x ^ 4, y ^ 4} ∉ Erdos939Sums 4`, whereas Catalan's pair
`{1, 8}` belongs to `Erdos939GeneralSums 2 2`.
-/
theorem not_full_add_odd_squares_and_fourth_powers_and_controls (r x y : ℕ)
    (hr : 2 ≤ r) (hx : ¬ 2 ∣ x) (hy : ¬ 2 ∣ y) :
    ¬ r.Full (x ^ 2 + y ^ 2) ∧ ¬ r.Full (x ^ 4 + y ^ 4) ∧
      ({x ^ 4, y ^ 4} : Finset ℕ) ∉ Erdos939Sums 4 ∧
      ({1, 8} : Finset ℕ) ∈ Erdos939GeneralSums 2 2 := by
  have hsq : ¬ r.Full (x ^ 2 + y ^ 2) := by
    intro hfull
    have h2 : (2).Full (x ^ 2 + y ^ 2) := Nat.full_of_le_full 2 (x ^ 2 + y ^ 2) hr hfull
    have hx8 := (odd_pow_mod_eight_and_sixteen x hx).1
    have hy8 := (odd_pow_mod_eight_and_sixteen y hy).1
    have hmod8 : (x ^ 2 + y ^ 2) % 8 = 2 := by omega
    have hdvd2 : 2 ∣ x ^ 2 + y ^ 2 := by omega
    have hmod4 : (x ^ 2 + y ^ 2) % 2 ^ 2 ≠ 0 := by omega
    have h4 : 2 ^ 2 ∣ x ^ 2 + y ^ 2 :=
      h2 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd2, by omega⟩)
    exact hmod4 (Nat.mod_eq_zero_of_dvd h4)
  have hpow2 : ¬ (2).Full (x ^ 4 + y ^ 4) := by
    intro h2
    have hx16 := (odd_pow_mod_eight_and_sixteen x hx).2.2.2.2.2
    have hy16 := (odd_pow_mod_eight_and_sixteen y hy).2.2.2.2.2
    have hmod16 : (x ^ 4 + y ^ 4) % 16 = 2 := by omega
    have hdvd2 : 2 ∣ x ^ 4 + y ^ 4 := by omega
    have hmod4 : (x ^ 4 + y ^ 4) % 2 ^ 2 ≠ 0 := by omega
    have h4 : 2 ^ 2 ∣ x ^ 4 + y ^ 4 :=
      h2 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd2, by omega⟩)
    exact hmod4 (Nat.mod_eq_zero_of_dvd h4)
  have hpow4_r : ¬ r.Full (x ^ 4 + y ^ 4) := by
    intro hfull
    exact hpow2 (Nat.full_of_le_full 2 (x ^ 4 + y ^ 4) hr hfull)
  refine ⟨hsq, hpow4_r, ?_, ?_⟩
  · intro hmem
    have hfull4 := ((pair_mem_erdos939Sums_four_iff (x ^ 4) (y ^ 4)).mp hmem).2.2.2.2.2
    exact hpow2 (Nat.full_of_le_full 2 (x ^ 4 + y ^ 4) (by omega) hfull4)
  · rw [pair_mem_erdos939GeneralSums_two_iff 2 1 8 (by omega)]
    refine ⟨by omega, by omega, by decide, Nat.Full.one_right 2, ?_, ?_⟩
    · exact (prime_pow_full_iff 2 2 3 Nat.prime_two (by omega)).mpr (by omega)
    · exact (prime_pow_full_iff 2 3 2 Nat.prime_three (by omega)).mpr (by omega)

/-!
## Infinite Coprime $3$-Powerful Triples, Fermat–Catalan Exponent Obstructions, and $5$-Powerful Sums

This section establishes:
1. **Part 1 (Euler–Viète–Nitaj Tangent Recurrence & Unconditional Proof of `erdos_939.variants.triples`):**
   - Formalizes the Euler–Viète cubic tangent identity $u(v+w)^3 + w(v-u)^3 = v(u+w)^3$ for $u + v = w$,
     universal coprimality preservation $\gcd(u(v+w)^3, w(v-u)^3) = 1$ whenever $\gcd(u,v) = 1$ and
     $3 \mid uvw$, Nitaj's base seed $271^3 + 2^3 \cdot 3^5 \cdot 73^3 = 919^3$, and the strictly increasing
     infinite sequence `nitajSeq`, unconditionally proving `erdos_939.variants.triples` and
     `(Erdos939GeneralSums 3 2).Infinite`.
2. **Part 2 (Darmon–Granville / Fermat–Catalan Hyperbolic Exponent Obstruction for $r \ge 4$):**
   - Proves $r(ql + pl + pq) \le 3pql$, $4(ql + pl + pq) \le 3pql < 4pql$, and
     $\frac{1}{p} + \frac{1}{q} + \frac{1}{l} \le \frac{3}{r} \le \frac{3}{4} < 1$ for all $p, q, l \ge r \ge 4$,
     together with the canonical fixed-core $4$-powerful equation
     $v_{a,1}^5 v_{a,2}^6 v_{a,3}^7 u_a^4 + v_{b,1}^5 v_{b,2}^6 v_{b,3}^7 u_b^4 = v_{c,1}^5 v_{c,2}^6 v_{c,3}^7 u_c^4$.
3. **Part 3 ($3$-Term Coprime $5$-Powerful Sum Structure in `Erdos939Sums 5`):**
   - Proves the canonical $5$-powerful squarefree-core factorization $n = u^5 v_1^6 v_2^7 v_3^8 v_4^9$,
     $32$-divisibility of even $5$-powerful summands, parity exclusions, and Cambie's $r = 5$ witness.
-/

/-! ## Part 1: Euler–Viète–Nitaj Tangent Recurrence & Unconditional `erdos_939.variants.triples` -/

structure IsNitajTriple (u v w : ℕ) : Prop where
  u_pos : 0 < u
  v_pos : 0 < v
  sum_eq : u + v = w
  coprime_uv : Nat.Coprime u v
  three_dvd : 3 ∣ u ∨ 3 ∣ v ∨ 3 ∣ w
  full_u : (3).Full u
  full_v : (3).Full v
  full_w : (3).Full w

theorem euler_viete_cubic_tangent_identity {u v w : ℕ} (huv : u ≤ v) (hw : u + v = w) :
    u * (v + w) ^ 3 + w * (v - u) ^ 3 = v * (u + w) ^ 3 := by
  subst hw
  zify [huv]
  ring

theorem coprime_euler_viete_factors {u v w : ℕ} (huv : u ≤ v) (hw : u + v = w)
    (hcop : Nat.Coprime u v) (h3 : 3 ∣ u ∨ 3 ∣ v ∨ 3 ∣ w) :
    Nat.Coprime (v + w) (v - u) := by
  set P := v + w
  set Q := v - u
  set g := Nat.gcd P Q
  have hgP : g ∣ P := Nat.gcd_dvd_left P Q
  have hgQ : g ∣ Q := Nat.gcd_dvd_right P Q
  have hPQ : P + Q = 3 * v := by omega
  have hP2Q : 2 * Q + 3 * u = P := by omega
  have hg3v : g ∣ 3 * v := hPQ ▸ dvd_add hgP hgQ
  have hg3u : g ∣ 3 * u := (Nat.dvd_add_right (dvd_mul_of_dvd_right hgQ 2)).mp (hP2Q ▸ hgP)
  have hg3 : g ∣ 3 := by
    have h1 : g ∣ Nat.gcd (3 * u) (3 * v) := Nat.dvd_gcd hg3u hg3v
    rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one] at h1
    exact h1
  have hnot3Q : ¬ 3 ∣ Q := by
    intro h3Q
    have hnot_both : ¬ (3 ∣ u ∧ 3 ∣ v) := by
      intro ⟨h3u, h3v⟩
      have : 3 ∣ Nat.gcd u v := Nat.dvd_gcd h3u h3v
      rw [hcop.gcd_eq_one] at this
      omega
    rcases h3 with h3u | h3v | h3w
    · exact hnot_both ⟨h3u, by omega⟩
    · exact hnot_both ⟨by omega, h3v⟩
    · have h3_2v : 3 ∣ 2 * v := by
        have : 2 * v = w + Q := by omega
        rw [this]
        exact dvd_add h3w h3Q
      have hcop32 : Nat.Coprime 3 2 := by decide
      have h3v : 3 ∣ v := hcop32.dvd_of_dvd_mul_left h3_2v
      exact hnot_both ⟨by omega, h3v⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hg3 with hg1 | hg3_eq
  · exact hg1
  · exfalso
    exact hnot3Q (hg3_eq ▸ hgQ)

theorem coprime_euler_viete_summands {u v w : ℕ} (huv : u ≤ v) (hw : u + v = w)
    (hcop : Nat.Coprime u v) (h3 : 3 ∣ u ∨ 3 ∣ v ∨ 3 ∣ w) :
    Nat.Coprime (u * (v + w) ^ 3) (w * (v - u) ^ 3) := by
  have h_uw : Nat.Coprime u w := by
    rw [← hw]
    exact Nat.coprime_self_add_right.mpr hcop
  have h_uQ : Nat.Coprime u (v - u) := by
    have h : u + (v - u) = v := by omega
    have h1 : Nat.Coprime u (u + (v - u)) := h.symm ▸ hcop
    exact Nat.coprime_self_add_right.mp h1
  have h_vw : Nat.Coprime v w := by
    rw [← hw, add_comm]
    exact Nat.coprime_self_add_right.mpr hcop.symm
  have h_Pw : Nat.Coprime (v + w) w := by
    rw [add_comm]
    exact (Nat.coprime_self_add_right.mpr h_vw.symm).symm
  have h_PQ : Nat.Coprime (v + w) (v - u) :=
    coprime_euler_viete_factors huv hw hcop h3
  exact (h_uw.mul_right (h_uQ.pow_right 3)).mul_left
    ((h_Pw.pow_left 3).mul_right (h_PQ.pow 3 3))

theorem isNitajTriple_symm {u v w : ℕ} (h : IsNitajTriple u v w) :
    IsNitajTriple v u w :=
  ⟨h.v_pos, h.u_pos, by have := h.sum_eq; omega, h.coprime_uv.symm,
    h.three_dvd.elim (fun h3 => Or.inr (Or.inl h3))
      (fun h3 => h3.elim Or.inl (fun h3w => Or.inr (Or.inr h3w))),
    h.full_v, h.full_u, h.full_w⟩

theorem isNitajTriple_ordered_step {u v w : ℕ} (h : IsNitajTriple u v w) (huv : u ≤ v) :
    IsNitajTriple (u * (v + w) ^ 3) (w * (v - u) ^ 3) (v * (u + w) ^ 3) ∧
      w < v * (u + w) ^ 3 := by
  have hu : 0 < u := h.u_pos
  have hv : 0 < v := h.v_pos
  have hw_eq : u + v = w := h.sum_eq
  have hw_gt : 2 < w := by
    rcases h.three_dvd with h3u | h3v | h3w
    · have : 3 ≤ u := Nat.le_of_dvd hu h3u; omega
    · have : 3 ≤ v := Nat.le_of_dvd hv h3v; omega
    · have : 3 ≤ w := Nat.le_of_dvd (by omega) h3w; omega
  have huv_lt : u < v := by
    rcases eq_or_lt_of_le huv with rfl | hlt
    · have : u = 1 := h.coprime_uv.eq_one_of_dvd dvd_rfl
      omega
    · exact hlt
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Nat.mul_pos hu (pow_pos (by omega) 3)
  · exact Nat.mul_pos (by omega) (pow_pos (by omega) 3)
  · exact euler_viete_cubic_tangent_identity huv hw_eq
  · exact coprime_euler_viete_summands huv hw_eq h.coprime_uv h.three_dvd
  · rcases h.three_dvd with h3u | h3v | h3w
    · exact Or.inl (dvd_mul_of_dvd_left h3u _)
    · exact Or.inr (Or.inr (dvd_mul_of_dvd_left h3v _))
    · exact Or.inr (Or.inl (dvd_mul_of_dvd_left h3w _))
  · exact full_mul_of_full 3 u ((v + w) ^ 3) h.full_u (full_of_pow_r_add_offset 3 0 (v + w))
  · exact full_mul_of_full 3 w ((v - u) ^ 3) h.full_w (full_of_pow_r_add_offset 3 0 (v - u))
  · exact full_mul_of_full 3 v ((u + w) ^ 3) h.full_v (full_of_pow_r_add_offset 3 0 (u + w))
  · have h1 : w < u + w := by omega
    have h2 : u + w ≤ (u + w) ^ 3 := Nat.le_self_pow (by omega) (u + w)
    have h3 : (u + w) ^ 3 ≤ v * (u + w) ^ 3 := Nat.le_mul_of_pos_left _ hv
    omega

def nitajStep (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let u := min t.1 t.2.1
  let v := max t.1 t.2.1
  let w := t.2.2
  (u * (v + w) ^ 3, w * (v - u) ^ 3, v * (u + w) ^ 3)

theorem isNitajTriple_nitajStep {t : ℕ × ℕ × ℕ} (h : IsNitajTriple t.1 t.2.1 t.2.2) :
    IsNitajTriple (nitajStep t).1 (nitajStep t).2.1 (nitajStep t).2.2 ∧
      t.2.2 < (nitajStep t).2.2 := by
  dsimp [nitajStep]
  rcases le_total t.1 t.2.1 with hle | hge
  · rw [min_eq_left hle, max_eq_right hle]
    exact isNitajTriple_ordered_step h hle
  · rw [min_eq_right hge, max_eq_left hge]
    exact isNitajTriple_ordered_step (isNitajTriple_symm h) hge

def nitajSeed : ℕ × ℕ × ℕ :=
  (271 ^ 3, 2 ^ 3 * 3 ^ 5 * 73 ^ 3, 919 ^ 3)

theorem isNitajTriple_nitajSeed :
    IsNitajTriple nitajSeed.1 nitajSeed.2.1 nitajSeed.2.2 := by
  dsimp [nitajSeed]
  refine ⟨by decide, by decide, by decide, by decide, Or.inr (Or.inl (by decide)), ?_, ?_, ?_⟩
  · exact full_of_pow_r_add_offset 3 0 271
  · exact full_mul_of_full 3 (2 ^ 3 * 3 ^ 5) (73 ^ 3)
      (full_mul_of_full 3 (2 ^ 3) (3 ^ 5)
        ((prime_pow_full_iff 3 2 3 Nat.prime_two (by omega)).mpr (by omega))
        ((prime_pow_full_iff 3 3 5 Nat.prime_three (by omega)).mpr (by omega)))
      (full_of_pow_r_add_offset 3 0 73)
  · exact full_of_pow_r_add_offset 3 0 919

def nitajSeq (n : ℕ) : ℕ × ℕ × ℕ :=
  nitajStep^[n] nitajSeed

theorem isNitajTriple_nitajSeq (n : ℕ) :
    IsNitajTriple (nitajSeq n).1 (nitajSeq n).2.1 (nitajSeq n).2.2 := by
  induction n with
  | zero => exact isNitajTriple_nitajSeed
  | succ n ih =>
    unfold nitajSeq
    rw [Function.iterate_succ_apply']
    exact (isNitajTriple_nitajStep ih).1

theorem strictMono_nitajSeq_third :
    StrictMono (fun n : ℕ => (nitajSeq n).2.2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold nitajSeq
  rw [Function.iterate_succ_apply']
  exact (isNitajTriple_nitajStep (isNitajTriple_nitajSeq n)).2

theorem coprime_insert_of_coprime_pair {a b : ℕ} (S : Finset ℕ)
    (ha : a ∈ S) (hb : b ∈ S) (hcop : Nat.Coprime a b) :
    S.Coprime := by
  show S.gcd id = 1
  exact Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (Finset.gcd_dvd ha) (Finset.gcd_dvd hb))

theorem nitajSeq_mem_triples_set (n : ℕ) :
    nitajSeq n ∈ {(a, b, c) : ℕ × ℕ × ℕ |
      ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      a + b = c} := by
  have h := isNitajTriple_nitajSeq n
  simp only [Set.mem_setOf_eq]
  refine ⟨?_, h.u_pos, h.v_pos, h.full_u, h.full_v, h.full_w, h.sum_eq⟩
  exact coprime_insert_of_coprime_pair {(nitajSeq n).1, (nitajSeq n).2.1, (nitajSeq n).2.2}
    (by simp) (by simp) h.coprime_uv

/-- **Unconditional Resolution of `erdos_939.variants.triples`:**
There are infinitely many triples $(a, b, c)$ of coprime $3$-powerful positive integers with $a + b = c$. -/
theorem erdos_939_variants_triples_infinite :
    {(a, b, c) : ℕ × ℕ × ℕ |
      ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      a + b = c}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := nitajSeq)
  · intro m n hmn
    have h3 : (nitajSeq m).2.2 = (nitajSeq n).2.2 := by rw [hmn]
    exact strictMono_nitajSeq_third.injective h3
  · exact nitajSeq_mem_triples_set

theorem nitajSeq_pair_mem_erdos939GeneralSums (n : ℕ) :
    ({(nitajSeq n).1, (nitajSeq n).2.1} : Finset ℕ) ∈ Erdos939GeneralSums 3 2 ∧
      ∑ s ∈ ({(nitajSeq n).1, (nitajSeq n).2.1} : Finset ℕ), s = (nitajSeq n).2.2 := by
  have h := isNitajTriple_nitajSeq n
  have hmem : ({(nitajSeq n).1, (nitajSeq n).2.1} : Finset ℕ) ∈ Erdos939GeneralSums 3 2 := by
    rw [pair_mem_erdos939GeneralSums_two_iff 3 (nitajSeq n).1 (nitajSeq n).2.1 (by omega)]
    exact ⟨h.u_pos, h.v_pos, h.coprime_uv, h.full_u, h.full_v, h.sum_eq.symm ▸ h.full_w⟩
  have hne : (nitajSeq n).1 ≠ (nitajSeq n).2.1 :=
    ne_of_coprime_of_full_add 3 (nitajSeq n).1 (nitajSeq n).2.1 (by omega)
      h.u_pos h.coprime_uv (h.sum_eq.symm ▸ h.full_w)
  refine ⟨hmem, ?_⟩
  rw [Finset.sum_pair hne, h.sum_eq]

/-- **Unconditional Infinitude of `Erdos939GeneralSums 3 2`:**
The family of $2$-element coprime $3$-powerful sets whose sum is $3$-powerful is infinite. -/
theorem erdos_939_generalSums_three_two_infinite :
    (Erdos939GeneralSums 3 2).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ({(nitajSeq n).1, (nitajSeq n).2.1} : Finset ℕ))
  · intro m n hmn
    have hm := (nitajSeq_pair_mem_erdos939GeneralSums m).2
    have hn := (nitajSeq_pair_mem_erdos939GeneralSums n).2
    change ({(nitajSeq m).1, (nitajSeq m).2.1} : Finset ℕ) =
      {(nitajSeq n).1, (nitajSeq n).2.1} at hmn
    have hsum : (nitajSeq m).2.2 = (nitajSeq n).2.2 := by
      rw [← hm, ← hn, hmn]
    exact strictMono_nitajSeq_third.injective hsum
  · intro n
    exact (nitajSeq_pair_mem_erdos939GeneralSums n).1

/-! ## Part 2: Darmon–Granville / Fermat–Catalan Hyperbolic Exponent Obstructions for $r \ge 4$ -/

theorem fermat_catalan_nat_cross_product_bound {r p q l : ℕ}
    (hr : 4 ≤ r) (hp : r ≤ p) (hq : r ≤ q) (hl : r ≤ l) :
    r * (q * l + p * l + p * q) ≤ 3 * (p * q * l) ∧
      4 * (q * l + p * l + p * q) ≤ 3 * (p * q * l) ∧
      q * l + p * l + p * q < p * q * l := by
  have h1 : r * q * l ≤ p * q * l := Nat.mul_le_mul_right l (Nat.mul_le_mul_right q hp)
  have h2 : r * p * l ≤ p * q * l := by
    calc r * p * l = p * (r * l) := by ring
      _ ≤ p * (q * l) := Nat.mul_le_mul_left p (Nat.mul_le_mul_right l hq)
      _ = p * q * l := by ring
  have h3 : r * p * q ≤ p * q * l := by
    calc r * p * q = p * q * r := by ring
      _ ≤ p * q * l := Nat.mul_le_mul_left (p * q) hl
  have hsum : r * (q * l + p * l + p * q) ≤ 3 * (p * q * l) := by
    calc r * (q * l + p * l + p * q)
        = r * q * l + r * p * l + r * p * q := by ring
      _ ≤ p * q * l + p * q * l + p * q * l := by omega
      _ = 3 * (p * q * l) := by ring
  have h4 : 4 * (q * l + p * l + p * q) ≤ r * (q * l + p * l + p * q) :=
    Nat.mul_le_mul_right _ hr
  have hpql_pos : 0 < p * q * l := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  refine ⟨hsum, le_trans h4 hsum, ?_⟩
  omega

theorem fermat_catalan_reciprocal_sum_le_three_div_r_lt_one {r p q l : ℕ}
    (hr : 4 ≤ r) (hp : r ≤ p) (hq : r ≤ q) (hl : r ≤ l) :
    (1 : ℝ) / (p : ℝ) + 1 / (q : ℝ) + 1 / (l : ℝ) ≤ 3 / (r : ℝ) ∧
      3 / (r : ℝ) ≤ 3 / 4 ∧
      (1 : ℝ) / (p : ℝ) + 1 / (q : ℝ) + 1 / (l : ℝ) < 1 := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hp_ge : (r : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hq_ge : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hl_ge : (r : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hr4 : (4 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1p : (1 : ℝ) / (p : ℝ) ≤ 1 / (r : ℝ) := one_div_le_one_div_of_le hr_pos hp_ge
  have h1q : (1 : ℝ) / (q : ℝ) ≤ 1 / (r : ℝ) := one_div_le_one_div_of_le hr_pos hq_ge
  have h1l : (1 : ℝ) / (l : ℝ) ≤ 1 / (r : ℝ) := one_div_le_one_div_of_le hr_pos hl_ge
  have h3_eq : (1 : ℝ) / (r : ℝ) + 1 / (r : ℝ) + 1 / (r : ℝ) = 3 / (r : ℝ) := by ring
  have h3r : 3 / (r : ℝ) ≤ 3 / 4 := by
    rw [div_le_div_iff₀ hr_pos (by norm_num)]
    linarith
  refine ⟨by linarith, h3r, by linarith⟩

theorem fermat_catalan_three_powerful_boundary_sharp :
    (1 : ℝ) / 3 + 1 / 3 + 1 / 3 = 1 ∧
      ({271 ^ 3, 2 ^ 3 * 3 ^ 5 * 73 ^ 3} : Finset ℕ) ∈ Erdos939GeneralSums 3 2 := by
  refine ⟨by norm_num, (nitajSeq_pair_mem_erdos939GeneralSums 0).1⟩

theorem mem_erdos939Sums_four_canonical_fifteen_core_equation {a b : ℕ}
    (hmem : ({a, b} : Finset ℕ) ∈ Erdos939Sums 4) :
    ∃ (u_a v_a1 v_a2 v_a3 u_b v_b1 v_b2 v_b3 u_c v_c1 v_c2 v_c3 : ℕ),
      a = u_a ^ 4 * v_a1 ^ 5 * v_a2 ^ 6 * v_a3 ^ 7 ∧
      b = u_b ^ 4 * v_b1 ^ 5 * v_b2 ^ 6 * v_b3 ^ 7 ∧
      a + b = u_c ^ 4 * v_c1 ^ 5 * v_c2 ^ 6 * v_c3 ^ 7 ∧
      u_a ^ 4 * v_a1 ^ 5 * v_a2 ^ 6 * v_a3 ^ 7 +
        u_b ^ 4 * v_b1 ^ 5 * v_b2 ^ 6 * v_b3 ^ 7 =
          u_c ^ 4 * v_c1 ^ 5 * v_c2 ^ 6 * v_c3 ^ 7 ∧
      Squarefree v_a1 ∧ Squarefree v_a2 ∧ Squarefree v_a3 ∧
      Squarefree v_b1 ∧ Squarefree v_b2 ∧ Squarefree v_b3 ∧
      Squarefree v_c1 ∧ Squarefree v_c2 ∧ Squarefree v_c3 ∧
      Nat.Coprime a b := by
  rcases (pair_mem_erdos939Sums_four_iff a b).mp hmem with
    ⟨ha_pos, hb_pos, hcop, ha4, hb4, hc4⟩
  rcases (four_full_iff_exists_canonical_cores a ha_pos).mp ha4 with
    ⟨u_a, v_a1, v_a2, v_a3, hva1, hva2, hva3, _, _, _, ha_eq⟩
  rcases (four_full_iff_exists_canonical_cores b hb_pos).mp hb4 with
    ⟨u_b, v_b1, v_b2, v_b3, hvb1, hvb2, hvb3, _, _, _, hb_eq⟩
  rcases (four_full_iff_exists_canonical_cores (a + b) (by omega)).mp hc4 with
    ⟨u_c, v_c1, v_c2, v_c3, hvc1, hvc2, hvc3, _, _, _, hc_eq⟩
  refine ⟨u_a, v_a1, v_a2, v_a3, u_b, v_b1, v_b2, v_b3, u_c, v_c1, v_c2, v_c3,
    ha_eq.symm, hb_eq.symm, hc_eq.symm, ?_, hva1, hva2, hva3, hvb1, hvb2, hvb3, hvc1, hvc2, hvc3, hcop⟩
  omega

theorem erdos939Sums_four_finite_of_sum_bound {B : ℕ}
    (hbound : ∀ a b : ℕ, ({a, b} : Finset ℕ) ∈ Erdos939Sums 4 → a + b ≤ B) :
    (Erdos939Sums 4).Finite := by
  apply Set.Finite.subset (s := (Finset.Icc 1 B).powerset)
  · exact Finset.finite_toSet _
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_powerset]
    rcases hS with ⟨hcard, hcop, hfull_sum, hall⟩
    have hcard2 : S.card = 2 := by omega
    rcases Finset.card_eq_two.mp hcard2 with ⟨a, b, hab, rfl⟩
    have hmem4 : ({a, b} : Finset ℕ) ∈ Erdos939Sums 4 := ⟨hcard, hcop, hfull_sum, hall⟩
    have hab_le : a + b ≤ B := hbound a b hmem4
    intro x hx
    rw [Finset.mem_Icc]
    have hx_pos : 0 < x := (hall x hx).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega

/-! ## Part 3: Canonical $5$-Powerful Decomposition & $3$-Term Sums in `Erdos939Sums 5` -/

theorem five_full_iff_exists_canonical_cores (n : ℕ) (hn : 0 < n) :
    (5).Full n ↔
      ∃ u v₁ v₂ v₃ v₄ : ℕ,
        n = u ^ 5 * v₁ ^ 6 * v₂ ^ 7 * v₃ ^ 8 * v₄ ^ 9 ∧
        Squarefree v₁ ∧ Squarefree v₂ ∧ Squarefree v₃ ∧ Squarefree v₄ ∧
        Nat.Coprime v₁ v₂ ∧ Nat.Coprime v₁ v₃ ∧ Nat.Coprime v₁ v₄ ∧
        Nat.Coprime v₂ v₃ ∧ Nat.Coprime v₂ v₄ ∧ Nat.Coprime v₃ v₄ := by
  constructor
  · intro h5
    refine ⟨rFullBaseCore 5 n, rFullExcessCore 5 1 n, rFullExcessCore 5 2 n,
      rFullExcessCore 5 3 n, rFullExcessCore 5 4 n, ?_,
      rFullExcessCore_squarefree 5 1 n, rFullExcessCore_squarefree 5 2 n,
      rFullExcessCore_squarefree 5 3 n, rFullExcessCore_squarefree 5 4 n,
      rFullExcessCore_coprime 5 1 2 n (by decide),
      rFullExcessCore_coprime 5 1 3 n (by decide),
      rFullExcessCore_coprime 5 1 4 n (by decide),
      rFullExcessCore_coprime 5 2 3 n (by decide),
      rFullExcessCore_coprime 5 2 4 n (by decide),
      rFullExcessCore_coprime 5 3 4 n (by decide)⟩
    have hprod := (rFullBaseCore_mul_excess_prod_eq_self 5 n (by omega) hn h5).symm
    have hico : (Finset.Ico 1 5 : Finset ℕ) = insert 1 (insert 2 (insert 3 {4})) := by decide
    rw [hico, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton] at hprod
    calc n = rFullBaseCore 5 n ^ 5 *
          (rFullExcessCore 5 1 n ^ 6 *
            (rFullExcessCore 5 2 n ^ 7 *
              (rFullExcessCore 5 3 n ^ 8 * rFullExcessCore 5 4 n ^ 9))) := hprod
      _ = rFullBaseCore 5 n ^ 5 * rFullExcessCore 5 1 n ^ 6 *
            rFullExcessCore 5 2 n ^ 7 * rFullExcessCore 5 3 n ^ 8 *
            rFullExcessCore 5 4 n ^ 9 := by ring
  · rintro ⟨u, v₁, v₂, v₃, v₄, rfl, _⟩
    have h1 : (5).Full (u ^ 5) := full_of_pow_r_add_offset 5 0 u
    have h2 : (5).Full (v₁ ^ 6) := full_of_pow_r_add_offset 5 1 v₁
    have h3 : (5).Full (v₂ ^ 7) := full_of_pow_r_add_offset 5 2 v₂
    have h4 : (5).Full (v₃ ^ 8) := full_of_pow_r_add_offset 5 3 v₃
    have h5 : (5).Full (v₄ ^ 9) := full_of_pow_r_add_offset 5 4 v₄
    exact full_mul_of_full 5 _ _
      (full_mul_of_full 5 _ _
        (full_mul_of_full 5 _ _ (full_mul_of_full 5 _ _ h1 h2) h3) h4) h5

theorem two_pow_dvd_of_even_and_r_full {r n : ℕ} (hn : 0 < n) (h2 : 2 ∣ n) (hfull : r.Full n) :
    2 ^ r ∣ n :=
  hfull 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, ne_of_gt hn⟩)

theorem thirty_two_dvd_of_even_and_five_full {n : ℕ} (hn : 0 < n) (h2 : 2 ∣ n) (h5 : (5).Full n) :
    32 ∣ n :=
  two_pow_dvd_of_even_and_r_full hn h2 h5

theorem exists_odd_of_mem_erdos939Sums (r : ℕ) {S : Finset ℕ} (hS : S ∈ Erdos939Sums r) :
    ∃ s ∈ S, ¬ 2 ∣ s :=
  exists_not_dvd_of_mem_erdos939Sums r S hS 2 Nat.prime_two

theorem mem_erdos939Sums_five_parity_and_mod_thirty_two {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha5 : (5).Full a) (hb5 : (5).Full b) (hc5 : (5).Full c) (hsum5 : (5).Full (a + b + c)) :
    (2 ∣ a → 32 ∣ a) ∧
      (2 ∣ b → 32 ∣ b) ∧
      (2 ∣ c → 32 ∣ c) ∧
      (2 ∣ (a + b + c) → 32 ∣ (a + b + c)) ∧
      (2 ∣ a → 2 ∣ b → ¬ 2 ∣ c → (a + b + c) % 32 = c % 32) ∧
      (2 ∣ c → ¬ 2 ∣ a → ¬ 2 ∣ b → 32 ∣ (a + b)) := by
  have hda : 2 ∣ a → 32 ∣ a := fun h => thirty_two_dvd_of_even_and_five_full ha h ha5
  have hdb : 2 ∣ b → 32 ∣ b := fun h => thirty_two_dvd_of_even_and_five_full hb h hb5
  have hdc : 2 ∣ c → 32 ∣ c := fun h => thirty_two_dvd_of_even_and_five_full hc h hc5
  have hdsum : 2 ∣ (a + b + c) → 32 ∣ (a + b + c) :=
    fun h => thirty_two_dvd_of_even_and_five_full (by omega) h hsum5
  refine ⟨hda, hdb, hdc, hdsum, ?_, ?_⟩
  · intro h2a h2b _
    have h32a := hda h2a
    have h32b := hdb h2b
    omega
  · intro h2c hna hnb
    have h32c := hdc h2c
    have h2sum : 2 ∣ (a + b + c) := by omega
    have h32sum := hdsum h2sum
    omega

theorem not_three_odd_fourth_or_fifth_powers_in_erdos939Sums_five {x y z : ℕ}
    (hx : ¬ 2 ∣ x) (hy : ¬ 2 ∣ y) (hz : ¬ 2 ∣ z) :
    ¬ (3).Full (x ^ 4 + y ^ 4 + z ^ 4 + 1) ∧
      ¬ (5).Full (x ^ 4 + y ^ 4 + z ^ 4 + 1) := by
  have hx8 := (odd_pow_mod_eight_and_sixteen x hx).2.1
  have hy8 := (odd_pow_mod_eight_and_sixteen y hy).2.1
  have hz8 := (odd_pow_mod_eight_and_sixteen z hz).2.1
  have hnot3 : ¬ (3).Full (x ^ 4 + y ^ 4 + z ^ 4 + 1) := by
    intro h3
    have hdvd2 : 2 ∣ (x ^ 4 + y ^ 4 + z ^ 4 + 1) := by omega
    have h8 : 2 ^ 3 ∣ (x ^ 4 + y ^ 4 + z ^ 4 + 1) :=
      h3 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hdvd2, by omega⟩)
    have hmod8 : (x ^ 4 + y ^ 4 + z ^ 4 + 1) % 8 ≠ 0 := by omega
    exact hmod8 (Nat.mod_eq_zero_of_dvd h8)
  refine ⟨hnot3, fun h5 => hnot3 (Nat.full_of_le_full 3 _ (by omega) h5)⟩

/-! ## Part 4: Cambie's $r = 5$ Witness and Positive/Negative Controls -/

def cambieFiveSet : Finset ℕ :=
  {2 ^ 8 * 3 ^ 10 * 5 ^ 7, 2 ^ 12 * 23 ^ 6, 11 ^ 5 * 13 ^ 5}

theorem cambieFiveSet_mem_erdos939Sums_five_and_controls :
    cambieFiveSet ∈ Erdos939Sums 5 ∧
      ∑ s ∈ cambieFiveSet, s = 3 ^ 7 * 61 ^ 5 ∧
      32 ∣ (2 ^ 8 * 3 ^ 10 * 5 ^ 7) ∧
      32 ∣ (2 ^ 12 * 23 ^ 6) ∧
      ¬ 2 ∣ (11 ^ 5 * 13 ^ 5) ∧
      (Erdos939Sums 5).Nonempty := by
  have hcard : cambieFiveSet.card = 3 := by decide
  have hsum : ∑ s ∈ cambieFiveSet, s = 3 ^ 7 * 61 ^ 5 := by decide
  have hcop : cambieFiveSet.Coprime :=
    coprime_insert_of_coprime_pair cambieFiveSet
      (a := 2 ^ 12 * 23 ^ 6) (b := 11 ^ 5 * 13 ^ 5)
      (by decide) (by decide) (by decide)
  have hfull_sum : (5).Full (∑ s ∈ cambieFiveSet, s) := by
    rw [hsum]
    exact full_mul_of_full 5 (3 ^ 7) (61 ^ 5)
      ((prime_pow_full_iff 5 3 7 Nat.prime_three (by omega)).mpr (by omega))
      (full_of_pow_r_add_offset 5 0 61)
  have hall : ∀ s ∈ cambieFiveSet, 0 < s ∧ (5).Full s := by
    intro s hs
    dsimp [cambieFiveSet] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      exact full_mul_of_full 5 (2 ^ 8 * 3 ^ 10) (5 ^ 7)
        (full_mul_of_full 5 (2 ^ 8) (3 ^ 10)
          ((prime_pow_full_iff 5 2 8 Nat.prime_two (by omega)).mpr (by omega))
          ((prime_pow_full_iff 5 3 10 Nat.prime_three (by omega)).mpr (by omega)))
        ((prime_pow_full_iff 5 5 7 Nat.prime_five (by omega)).mpr (by omega))
    · refine ⟨by decide, ?_⟩
      exact full_mul_of_full 5 (2 ^ 12) (23 ^ 6)
        ((prime_pow_full_iff 5 2 12 Nat.prime_two (by omega)).mpr (by omega))
        (full_of_pow_r_add_offset 5 1 23)
    · refine ⟨by decide, ?_⟩
      exact full_mul_of_full 5 (11 ^ 5) (13 ^ 5)
        (full_of_pow_r_add_offset 5 0 11)
        (full_of_pow_r_add_offset 5 0 13)
  have hmem : cambieFiveSet ∈ Erdos939Sums 5 := ⟨hcard, hcop, hfull_sum, hall⟩
  exact ⟨hmem, hsum, by decide, by decide, by decide, ⟨cambieFiveSet, hmem⟩⟩

/-! ## Part 5: Binomial Odd-Power Splitting Construction for $r \ge 6$ (Price 2026) -/

open Finset in
lemma e939_split (f : ℕ → ℤ) (N : ℕ) :
    ∑ j ∈ range (2 * N), f j = ∑ m ∈ range N, f (2 * m) + ∑ m ∈ range N, f (2 * m + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    ring

open Finset in
lemma e939_binom (X Y : ℤ) (r : ℕ) (hr : 1 ≤ r) :
    (X + Y) ^ r = (X - Y) ^ r +
      ∑ m ∈ range r, 2 * (r.choose (2 * m + 1) : ℤ) * X ^ (r - (2 * m + 1)) * Y ^ (2 * m + 1) := by
  have h1 : (X + Y) ^ r = ∑ j ∈ range (2 * r), Y ^ j * X ^ (r - j) * (r.choose j : ℤ) := by
    rw [add_comm, add_pow]
    apply sum_subset (by intro j; simp only [mem_range]; omega)
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have h2 : (X - Y) ^ r = ∑ j ∈ range (2 * r), (-Y) ^ j * X ^ (r - j) * (r.choose j : ℤ) := by
    rw [sub_eq_neg_add, add_pow]
    apply sum_subset (by intro j; simp only [mem_range]; omega)
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [h1, h2, e939_split, e939_split]
  have he : ∀ m, (-Y) ^ (2 * m) = Y ^ (2 * m) := fun m => by rw [pow_mul, pow_mul, neg_sq]
  have ho : ∀ m, (-Y) ^ (2 * m + 1) = - Y ^ (2 * m + 1) := fun m => by
    rw [pow_succ, he, pow_succ]; ring
  simp only [he, ho]
  rw [← sub_eq_iff_eq_add']
  rw [show ∀ a b c : ℤ, a + b - (a + c) = b - c from fun a b c => by ring]
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro m _; ring

open Finset in
lemma e939_full_mul_pow (r a b : ℕ) (h : ∀ p, p.Prime → p ∣ a → p ∣ b) :
    r.Full (a * b ^ r) := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, -⟩ := hp
  have hpb : p ∣ b := by
    rcases (Nat.Prime.dvd_mul hpp).mp hpd with h1 | h1
    · exact h _ hpp h1
    · exact hpp.dvd_of_dvd_pow h1
  exact (pow_dvd_pow_of_dvd hpb r).trans (dvd_mul_left _ _)

open Finset in
lemma e939_geom (d : ℕ) : ∑ i ∈ range d, 2 ^ i = 2 ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega

open Finset in
lemma e939_powlt (X Y c k : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) (hY : 0 < Y) (h : c * Y < X) :
    c * Y ^ k < X ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simpa using h
    · have ih' := ih h0
      have hYX : Y ≤ X := by nlinarith
      calc c * Y ^ (k + 1) = c * Y ^ k * Y := by ring
        _ < X ^ k * Y := Nat.mul_lt_mul_of_pos_right ih' hY
        _ ≤ X ^ (k + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hYX

open Finset in
lemma e939_dec (X Y c a b k C C' : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) (hC : 1 ≤ C) (hC' : C' ≤ c) (hY : 0 < Y)
    (h : c * Y < X) : 2 * C' * X ^ a * Y ^ (b + k) < 2 * C * X ^ (a + k) * Y ^ b := by
  have hX : 0 < X := by omega
  have hkey : c * Y ^ k < X ^ k := e939_powlt X Y c k hk hc hY h
  calc 2 * C' * X ^ a * Y ^ (b + k) = 2 * C' * (X ^ a * Y ^ b) * Y ^ k := by ring
    _ ≤ 2 * c * (X ^ a * Y ^ b) * Y ^ k := by gcongr
    _ = 2 * (X ^ a * Y ^ b) * (c * Y ^ k) := by ring
    _ < 2 * (X ^ a * Y ^ b) * X ^ k := Nat.mul_lt_mul_of_pos_left hkey (by positivity)
    _ ≤ C * (2 * (X ^ a * Y ^ b) * X ^ k) := Nat.le_mul_of_pos_left _ hC
    _ = 2 * C * X ^ (a + k) * Y ^ b := by ring

open Finset in
def e939d (r : ℕ) : ℕ := r / 2 - 2
open Finset in
def e939g (r : ℕ) : ℕ := 2 ^ e939d r - 1
open Finset in
def e939B1 (r : ℕ) : ℕ := 2 * r.factorial * e939g r
open Finset in
def e939B (r : ℕ) : ℕ := e939g r * e939B1 r
open Finset in
def e939T (r q j : ℕ) : ℕ := 2 * r.choose j * (q ^ r) ^ (r - j) * (e939B r ^ r) ^ j
open Finset in
def e939K (r q : ℕ) : ℕ := 2 * r * q ^ (r * (r - 1)) * e939g r ^ (r - 1) * e939B1 r ^ r
open Finset in
def e939A (r q : ℕ) : ℕ := (q ^ r - e939B r ^ r) ^ r
open Finset in
def e939S (r q : ℕ) : Finset ℕ :=
  insert (e939A r q) ((range (e939d r)).image (fun i => 2 ^ i * e939K r q) ∪
    (range ((r - 1) / 2)).image (fun m => e939T r q (2 * m + 3)))

open Finset in
lemma e939g_pos (r : ℕ) (hr : 6 ≤ r) : 1 ≤ e939g r := by
  unfold e939g e939d
  have : 2 ≤ 2 ^ (r / 2 - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r / 2 - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

open Finset in
lemma e939g_lt (r : ℕ) : e939g r < 2 ^ r := by
  unfold e939g e939d
  have : 2 ^ (r / 2 - 2) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 1 ≤ 2 ^ (r / 2 - 2) := Nat.one_le_two_pow
  omega

open Finset in
lemma e939B_pos (r : ℕ) (hr : 6 ≤ r) : 0 < e939B r := by
  unfold e939B e939B1
  have := e939g_pos r hr
  have := Nat.factorial_pos r
  positivity

open Finset in
lemma e939_dvdB1 (r p : ℕ) (hp : p.Prime) (h : p ∣ 2 ∨ p ∣ r.factorial ∨ p ∣ e939g r) :
    p ∣ e939B1 r := by
  unfold e939B1
  rcases h with h | h | h
  · exact (h.mul_right _).mul_right _
  · exact (h.mul_left _).mul_right _
  · exact h.mul_left _

open Finset in
lemma e939_B1_dvd_B (r : ℕ) : e939B1 r ∣ e939B r := dvd_mul_left _ _

open Finset in
lemma e939_gK (r q : ℕ) (hr : 6 ≤ r) : e939g r * e939K r q = e939T r q 1 := by
  unfold e939K e939T e939B
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.choose_one_right, Nat.add_sub_cancel, pow_one]
  ring

open Finset in
lemma e939_sumT (r q : ℕ) (hr : 6 ≤ r) (hXY : e939B r ^ r ≤ q ^ r) :
    e939A r q + e939T r q 1 + ∑ m ∈ range ((r - 1) / 2), e939T r q (2 * m + 3) =
      (q ^ r + e939B r ^ r) ^ r := by
  zify [hXY]
  have hb := e939_binom ((q : ℤ) ^ r) ((e939B r : ℤ) ^ r) r (by omega)
  have hT : ∀ j, ((e939T r q j : ℕ) : ℤ) =
      2 * (r.choose j : ℤ) * ((q : ℤ) ^ r) ^ (r - j) * ((e939B r : ℤ) ^ r) ^ j := by
    intro j; unfold e939T; push_cast; ring
  unfold e939A
  push_cast
  rw [hb]
  obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hsplit : ∑ m ∈ range r, 2 * (r.choose (2 * m + 1) : ℤ) * ((q : ℤ) ^ r) ^ (r - (2 * m + 1)) *
      ((e939B r : ℤ) ^ r) ^ (2 * m + 1) =
      ((e939T r q 1 : ℕ) : ℤ) + ∑ m ∈ range ((r - 1) / 2), ((e939T r q (2 * m + 3) : ℕ) : ℤ) := by
    have h1 : range r = range (s + 1) := by rw [hs]
    rw [h1, sum_range_succ', add_comm]
    simp only [hT]
    simp_rw [show ∀ k : ℕ, 2 * (k + 1) + 1 = 2 * k + 3 from fun k => by ring]
    congr 1
    symm
    apply sum_subset (by intro m; simp only [mem_range]; omega)
    intro m hm hm'
    simp only [mem_range, not_lt] at hm hm'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hsplit, Nat.cast_sub hXY]
  push_cast
  ring

open Finset in
lemma e939_XY (r q : ℕ) (hr : 6 ≤ r) (hqB : 4 * e939B r < q) :
    4 ^ r * e939B r ^ r < q ^ r := by
  rw [← mul_pow]; exact Nat.pow_lt_pow_left hqB (by omega)

open Finset in
lemma e939_choose_le (r j : ℕ) : r.choose j ≤ 4 ^ r :=
  (Nat.choose_le_two_pow r j).trans (Nat.pow_le_pow_left (by norm_num) r)

open Finset in
lemma e939_Tdec (r q m m' : ℕ) (hr : 6 ≤ r) (hqB : 4 * e939B r < q) (hmm : m < m')
    (hm' : 2 * m' + 3 ≤ r) : e939T r q (2 * m' + 3) < e939T r q (2 * m + 3) := by
  have hY : 0 < e939B r ^ r := pow_pos (e939B_pos r hr) r
  have h := e939_dec (q ^ r) (e939B r ^ r) (4 ^ r) (r - (2 * m' + 3)) (2 * m + 3) (2 * (m' - m))
    (r.choose (2 * m + 3)) (r.choose (2 * m' + 3)) (by omega) (Nat.one_le_pow _ _ (by norm_num))
    (Nat.choose_pos (by omega)) (e939_choose_le _ _) hY (e939_XY r q hr hqB)
  calc e939T r q (2 * m' + 3) = 2 * r.choose (2 * m' + 3) * (q ^ r) ^ (r - (2 * m' + 3)) *
        (e939B r ^ r) ^ (2 * m + 3 + 2 * (m' - m)) := by
          unfold e939T; rw [show 2 * m + 3 + 2 * (m' - m) = 2 * m' + 3 by omega]
    _ < _ := h
    _ = e939T r q (2 * m + 3) := by
          unfold e939T; rw [show r - (2 * m' + 3) + 2 * (m' - m) = r - (2 * m + 3) by omega]

open Finset in
lemma e939_T3K (r q : ℕ) (hr : 6 ≤ r) (hqB : 4 * e939B r < q) : e939T r q 3 < e939K r q := by
  have hY : 0 < e939B r ^ r := pow_pos (e939B_pos r hr) r
  have hg := e939g_pos r hr
  have hcg : r.choose 3 * e939g r ≤ 4 ^ r := by
    calc r.choose 3 * e939g r ≤ 2 ^ r * 2 ^ r :=
          Nat.mul_le_mul (Nat.choose_le_two_pow r 3) (e939g_lt r).le
      _ = 4 ^ r := by rw [← mul_pow]; norm_num
  have h := e939_dec (q ^ r) (e939B r ^ r) (4 ^ r) (r - 3) 1 2 r (r.choose 3 * e939g r)
    (by omega) (Nat.one_le_pow _ _ (by norm_num)) (by omega) hcg hY (e939_XY r q hr hqB)
  have h2 : e939g r * e939T r q 3 < e939g r * e939K r q := by
    rw [e939_gK r q hr]
    calc e939g r * e939T r q 3 = 2 * (r.choose 3 * e939g r) * (q ^ r) ^ (r - 3) *
          (e939B r ^ r) ^ (1 + 2) := by unfold e939T; ring
      _ < _ := h
      _ = e939T r q 1 := by
          unfold e939T; rw [show r - 3 + 2 = r - 1 by omega, Nat.choose_one_right]
  exact Nat.lt_of_mul_lt_mul_left h2

open Finset in
lemma e939_Tle3 (r q m : ℕ) (hr : 6 ≤ r) (hqB : 4 * e939B r < q) (hm : m < (r - 1) / 2) :
    e939T r q (2 * m + 3) ≤ e939T r q 3 := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; rfl
  · exact (e939_Tdec r q 0 m hr hqB h0 (by omega)).le

open Finset in
lemma e939_B_even (r : ℕ) : 2 ∣ e939B r := by
  unfold e939B e939B1; exact ((dvd_mul_right 2 _).mul_right _).mul_left _

open Finset in
lemma e939_K_even (r q : ℕ) : 2 ∣ e939K r q := by
  unfold e939K; exact (((dvd_mul_right 2 r).mul_right _).mul_right _).mul_right _

open Finset in
lemma e939_T_even (r q j : ℕ) : 2 ∣ e939T r q j := by
  unfold e939T; exact ((dvd_mul_right 2 _).mul_right _).mul_right _

open Finset in
lemma e939_A_odd (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hqB : 4 * e939B r < q) :
    ¬ 2 ∣ e939A r q := by
  have hq2 : q ≠ 2 := by have := e939B_pos r hr; omega
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have hXo : Odd (q ^ r) := hqo.pow
  have hYe : Even (e939B r ^ r) := (even_iff_two_dvd.mpr (e939_B_even r)).pow_of_ne_zero (by omega)
  have hle : e939B r ^ r ≤ q ^ r := (Nat.le_of_lt (lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) (e939_XY r q hr hqB)))
  have hd : Odd (q ^ r - e939B r ^ r) := by
    rcases hXo with ⟨a, ha⟩; rcases hYe with ⟨b, hb⟩
    exact ⟨a - b, by omega⟩
  unfold e939A
  rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact hd.pow

open Finset in
lemma e939_full_P (r q i : ℕ) (hr : 6 ≤ r) : r.Full (2 ^ i * e939K r q) := by
  have heq : 2 ^ i * e939K r q =
      (2 ^ (i + 1) * r * e939g r ^ (r - 1)) * (q ^ (r - 1) * e939B1 r) ^ r := by
    unfold e939K; rw [mul_pow, ← pow_mul, show (r - 1) * r = r * (r - 1) by ring]; ring
  rw [heq]
  apply e939_full_mul_pow
  intro p hp h
  apply Dvd.dvd.mul_left
  apply e939_dvdB1 r p hp
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · exact Or.inl (hp.dvd_of_dvd_pow h2)
    · exact Or.inr (Or.inl (h2.trans (Nat.dvd_factorial (by omega) le_rfl)))
  · exact Or.inr (Or.inr (hp.dvd_of_dvd_pow h1))

open Finset in
lemma e939_full_T (r q j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) : r.Full (e939T r q j) := by
  have heq : e939T r q j = (2 * r.choose j) * (q ^ (r - j) * e939B r ^ j) ^ r := by
    unfold e939T; rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]; ring
  rw [heq]
  apply e939_full_mul_pow
  intro p hp h
  apply Dvd.dvd.mul_left
  have hB : p ∣ e939B r := by
    apply (e939_dvdB1 r p hp _).trans (e939_B1_dvd_B r)
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact Or.inl h1
    · refine Or.inr (Or.inl (h1.trans ?_))
      exact ⟨j.factorial * (r - j).factorial, by
        rw [← mul_assoc]; exact (Nat.choose_mul_factorial_mul_factorial hjr).symm⟩
  exact hB.trans (dvd_pow_self _ (by omega))

open Finset in
lemma e939_coprime_AK (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hqB : 4 * e939B r < q) :
    Nat.Coprime (e939A r q) (e939K r q) := by
  have hBpos := e939B_pos r hr
  have hle : e939B r ^ r ≤ q ^ r := (Nat.le_of_lt (lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) (e939_XY r q hr hqB)))
  apply Nat.coprime_of_dvd
  intro p hp hpA hpK
  have hpd : p ∣ q ^ r - e939B r ^ r := hp.dvd_of_dvd_pow hpA
  have hqB' : ¬ q ∣ e939B r := fun h => by have := Nat.le_of_dvd hBpos h; omega
  -- p divides q or B
  have hpqB : p ∣ q ∨ p ∣ e939B r := by
    unfold e939K at hpK
    rcases (Nat.Prime.dvd_mul hp).mp hpK with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
        · right
          apply (e939_dvdB1 r p hp _).trans (e939_B1_dvd_B r)
          rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
          · exact Or.inl h4
          · exact Or.inr (Or.inl (h4.trans (Nat.dvd_factorial (by omega) le_rfl)))
        · left; exact hp.dvd_of_dvd_pow h3
      · right
        exact (e939_dvdB1 r p hp (Or.inr (Or.inr (hp.dvd_of_dvd_pow h2)))).trans (e939_B1_dvd_B r)
    · right; exact (hp.dvd_of_dvd_pow h1).trans (e939_B1_dvd_B r)
  have hsum : q ^ r - e939B r ^ r + e939B r ^ r = q ^ r := Nat.sub_add_cancel hle
  rcases hpqB with h | h
  · have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    have h2 : p ∣ q ^ r := dvd_pow h (by omega)
    rw [← hsum] at h2
    have h3 : p ∣ e939B r ^ r := (Nat.dvd_add_right hpd).mp h2
    exact hqB' (hpq ▸ hp.dvd_of_dvd_pow h3)
  · have h2 : p ∣ q ^ r := by
      rw [← hsum]; exact dvd_add hpd (dvd_pow h (by omega))
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h2)
    exact hqB' (hpq ▸ h)

open Finset in
lemma e939_mem (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hqB : 4 * e939B r < q) :
    e939S r q ∈ Erdos939Sums r ∧ ∑ s ∈ e939S r q, s = (q ^ r + e939B r ^ r) ^ r := by
  have hBpos := e939B_pos r hr
  have hg := e939g_pos r hr
  have hqpos : 0 < q := hq.pos
  have hK : 0 < e939K r q := by
    unfold e939K e939B1
    have := Nat.factorial_pos r
    positivity
  have hle : e939B r ^ r ≤ q ^ r := (Nat.le_of_lt (lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) (e939_XY r q hr hqB)))
  have injP : Set.InjOn (fun i => 2 ^ i * e939K r q) ↑(range (e939d r)) := by
    intro i _ j _ h
    exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hK h)
  have injT : Set.InjOn (fun m => e939T r q (2 * m + 3)) ↑(range ((r - 1) / 2)) := by
    intro m hm m' hm' h
    simp only [coe_range, Set.mem_Iio] at hm hm'
    simp only at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := e939_Tdec r q m m' hr hqB hlt (by omega); omega
    · have := e939_Tdec r q m' m hr hqB hlt (by omega); omega
  have hdisj : Disjoint ((range (e939d r)).image (fun i => 2 ^ i * e939K r q))
      ((range ((r - 1) / 2)).image (fun m => e939T r q (2 * m + 3))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_image, mem_range] at hx hx'
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨m, hm, hm2⟩ := hx'
    have h1 := e939_Tle3 r q m hr hqB hm
    have h2 := e939_T3K r q hr hqB
    have h3 : e939K r q ≤ 2 ^ i * e939K r q := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos i)
    omega
  have hA : e939A r q ∉ (range (e939d r)).image (fun i => 2 ^ i * e939K r q) ∪
      (range ((r - 1) / 2)).image (fun m => e939T r q (2 * m + 3)) := by
    intro h
    apply e939_A_odd r q hr hq hqB
    simp only [mem_union, mem_image, mem_range] at h
    rcases h with ⟨i, -, hi⟩ | ⟨m, -, hm⟩
    · rw [← hi]; exact (e939_K_even r q).mul_left _
    · rw [← hm]; exact e939_T_even r q _
  have hsum : ∑ s ∈ e939S r q, s = (q ^ r + e939B r ^ r) ^ r := by
    unfold e939S
    rw [sum_insert hA, sum_union hdisj, sum_image injP, sum_image injT, ← sum_mul, e939_geom,
      show 2 ^ e939d r - 1 = e939g r from rfl, e939_gK r q hr, ← add_assoc]
    exact e939_sumT r q hr hle
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hsum⟩
  · unfold e939S
    rw [Finset.card_insert_of_notMem hA, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn injP,
      Finset.card_image_of_injOn injT, card_range, card_range]
    unfold e939d; omega
  · show (e939S r q).gcd id = 1
    have hAm : e939A r q ∈ e939S r q := mem_insert_self _ _
    have hKm : e939K r q ∈ e939S r q := by
      unfold e939S
      refine mem_insert_of_mem (mem_union_left _ (mem_image.mpr ⟨0, ?_, by simp⟩))
      simp only [mem_range]; unfold e939d; omega
    exact Nat.eq_one_of_dvd_one ((e939_coprime_AK r q hr hq hqB) ▸
      Nat.dvd_gcd (Finset.gcd_dvd hAm) (Finset.gcd_dvd hKm))
  · rw [hsum]; exact e939_full_pow r _
  · intro s hs
    unfold e939S at hs
    simp only [mem_insert, mem_union, mem_image, mem_range] at hs
    rcases hs with rfl | ⟨i, -, rfl⟩ | ⟨m, hm, rfl⟩
    · refine ⟨?_, e939_full_pow r _⟩
      unfold e939A
      apply pow_pos
      have := e939_XY r q hr hqB
      have : e939B r ^ r < q ^ r := lt_of_le_of_lt
        (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) this
      omega
    · exact ⟨by positivity, e939_full_P r q i hr⟩
    · refine ⟨?_, e939_full_T r q _ (by omega) (by omega)⟩
      unfold e939T
      have := Nat.choose_pos (show 2 * m + 3 ≤ r by omega)
      positivity

/-- For every $r \ge 6$ there are infinitely many sums of $r - 2$ coprime $r$-powerful numbers that
are themselves $r$-powerful. -/
theorem erdos_939.variants.infinite_of_six_le : ∀ r ≥ 6, (Erdos939Sums r).Infinite := by
  intro r hr
  have hs : {q | q.Prime ∧ 4 * e939B r < q}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (a + 4 * e939B r + 1)
    exact ⟨p, ⟨hp2, by omega⟩, by omega⟩
  refine Set.infinite_of_injOn_mapsTo (f := e939S r) ?_ ?_ hs
  · intro q hq q' hq' h
    have h1 := (e939_mem r q hr hq.1 hq.2).2
    have h2 := (e939_mem r q' hr hq'.1 hq'.2).2
    rw [h] at h1
    rw [h1] at h2
    have h3 := Nat.pow_left_injective (by omega : r ≠ 0) h2
    exact Nat.pow_left_injective (by omega : r ≠ 0) (by omega : q ^ r = q' ^ r)
  · intro q hq; exact (e939_mem r q hr hq.1 hq.2).1

/--
Cambie has found several examples of the sum of $r - 2$ coprime $r$-powerful numbers being itself
$r$-powerful. For example when $r=5$ we have
$$3^7\cdot 61^5 = 2^8\cdot3^{10}\cdot 5^7 + 2^{12}\cdot 23^6 + 11^5\cdot 13^5$$.
-/
theorem erdos_939.variants.examples : (∃ r ≥ 4, (Erdos939Sums r).Nonempty) :=
  ⟨5, by omega, cambieFiveSet_mem_erdos939Sums_five_and_controls.2.2.2.2.2⟩

/--
Euler had conjectured that the sum of $k - 1$ many $k$-th powers is never a
$k$-th power, but this is false for $k=5$, as Lander and Parkin [LaPa67] found
$$27^5+84^5+110^5+133^5=144^5$$.

The summands must be positive. Without that condition a set containing `0` would count, so the
negation would be satisfied by a sum of fewer than $k-1$ powers and would claim less than the
refutation of Euler's conjecture that this theorem records.
-/
theorem erdos_939.variants.euler : ¬ (∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
    (∀ s ∈ S, 0 < s) → ¬ (∃ q, ∑ s ∈ S, s ^ k = q ^k)) := by
  push Not
  use 5
  norm_num
  use {27, 84, 110, 133}
  refine ⟨by decide, by decide, 144, by norm_num⟩

/-- Unconditional nonemptiness of `Erdos939Sums r` for every $r \ge 5$. -/
theorem erdos939Sums_nonempty_of_five_le (r : ℕ) (hr : 5 ≤ r) :
    (Erdos939Sums r).Nonempty := by
  by_cases h5 : r = 5
  · subst h5
    exact cambieFiveSet_mem_erdos939Sums_five_and_controls.2.2.2.2.2
  · exact (erdos_939.variants.infinite_of_six_le r (by omega)).nonempty

/--
**Master Reduction of Erdős Problem #939:** The universal statement `∀ r ≥ 4, (Erdos939Sums r).Nonempty`
holds if and only if `(Erdos939Sums 4).Nonempty` holds.
-/
theorem erdos939_forall_four_le_iff_four_nonempty (P : Prop)
    (hP : P ↔ (Erdos939Sums 4).Nonempty) :
    P ↔ ∀ r ≥ 4, (Erdos939Sums r).Nonempty := by
  rw [hP]
  constructor
  · intro h4 r hr
    by_cases hr4 : r = 4
    · subst hr4; exact h4
    · exact erdos939Sums_nonempty_of_five_le r (by omega)
  · intro hall
    exact hall 4 (by omega)

/-- Strict monotonicity of the total sum of the family `e939S r q` in the prime parameter `q`. -/
theorem e939_sum_strictMono_q (r q₁ q₂ : ℕ) (hr : 6 ≤ r)
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hb₁ : 4 * e939B r < q₁) (hlt : q₁ < q₂) :
    ∑ s ∈ e939S r q₁, s < ∑ s ∈ e939S r q₂, s := by
  have hb₂ : 4 * e939B r < q₂ := lt_trans hb₁ hlt
  rw [(e939_mem r q₁ hr hq₁ hb₁).2, (e939_mem r q₂ hr hq₂ hb₂).2]
  apply Nat.pow_lt_pow_left _ (by omega)
  have hpow : q₁ ^ r < q₂ ^ r := Nat.pow_lt_pow_left hlt (by omega)
  omega

/-- For every $r \ge 6$ and every bound $M$, there exists `S ∈ Erdos939Sums r` with `M < ∑ s ∈ S, s`. -/
theorem exists_mem_erdos939Sums_sum_gt (r M : ℕ) (hr : 6 ≤ r) :
    ∃ S ∈ Erdos939Sums r, M < ∑ s ∈ S, s := by
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (M + 4 * e939B r + 1)
  have hqB : 4 * e939B r < q := by omega
  have hmem := e939_mem r q hr hq_prime hqB
  refine ⟨e939S r q, hmem.1, ?_⟩
  rw [hmem.2]
  have hqM : M < q := by omega
  have h1 : q ≤ q ^ r := Nat.le_self_pow (by omega) q
  have h2 : q ^ r ≤ q ^ r + e939B r ^ r := Nat.le_add_right _ _
  have h3 : q ^ r + e939B r ^ r ≤ (q ^ r + e939B r ^ r) ^ r :=
    Nat.le_self_pow (by omega) _
  omega

end Erdos939
