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
open scoped Classical


open Filter Real Set Finset

namespace Erdos962

/--
`Erdos962Prop n k` : there exists $m \le n$ such that each of
$m+1, \ldots, m+k$ has a prime divisor strictly larger than $k$.
-/
def Erdos962Prop (n k : ℕ) : Prop :=
  ∃ m ≤ n, ∀ i ∈ Set.Icc 1 k,
    ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ p ∣ (m + i)

/--
Let $k(n)$ be the maximal $k$ such that there exists $m \le n$ with
$m+1, \ldots, m+k$ each divisible by a prime $> k$.
-/
noncomputable def k (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => Erdos962Prop n k) n

theorem erdos962Prop_zero (n : ℕ) : Erdos962Prop n 0 := by
  refine ⟨0, Nat.zero_le n, ?_⟩
  intro i hi
  rcases hi with ⟨hi1, hi0⟩
  omega

theorem k_le_self (n : ℕ) : k n ≤ n := by
  classical
  exact Nat.findGreatest_le n

theorem erdos962Prop_k (n : ℕ) : Erdos962Prop n (k n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le n) (erdos962Prop_zero n)

theorem erdos962Prop_mono_left {n₁ n₂ k₀ : ℕ} (h : n₁ ≤ n₂) (hp : Erdos962Prop n₁ k₀) :
    Erdos962Prop n₂ k₀ := by
  rcases hp with ⟨m, hmn₁, hrun⟩
  exact ⟨m, le_trans hmn₁ h, hrun⟩

/--
An integer `x` has a prime factor strictly greater than `k` (i.e., `x` is not `k`-smooth).
-/
def HasLargePrimeFactor (k x : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ p ∣ x

/--
`IsLargePrimeRun m k` holds when every integer `m + i` for `i ∈ [1, k]` has a prime divisor `> k`.
-/
def IsLargePrimeRun (m k : ℕ) : Prop :=
  ∀ i ∈ Set.Icc 1 k, HasLargePrimeFactor k (m + i)

theorem erdos962Prop_iff_exists_isLargePrimeRun (n k : ℕ) :
    Erdos962Prop n k ↔ ∃ m ≤ n, IsLargePrimeRun m k := by
  simp [Erdos962Prop, IsLargePrimeRun, HasLargePrimeFactor]

/-! ### Smooth Exclusion and Factorial-Power Duality -/

theorem not_hasLargePrimeFactor_one (k : ℕ) : ¬ HasLargePrimeFactor k 1 := by
  rintro ⟨p, hp, _, hp1⟩
  exact hp.not_dvd_one hp1

theorem hasLargePrimeFactor_iff_exists_primeFactors {k x : ℕ} (hx : x ≠ 0) :
    HasLargePrimeFactor k x ↔ ∃ p ∈ x.primeFactors, k < p := by
  constructor
  · rintro ⟨p, hp, hkp, hpx⟩
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpx, hx⟩, hkp⟩
  · rintro ⟨p, hp, hkp⟩
    rcases Nat.mem_primeFactors.mp hp with ⟨hp_prime, hpx, _⟩
    exact ⟨p, hp_prime, hkp, hpx⟩

theorem not_hasLargePrimeFactor_iff_forall_prime_le (k x : ℕ) :
    ¬ HasLargePrimeFactor k x ↔ ∀ p : ℕ, Nat.Prime p → p ∣ x → p ≤ k := by
  constructor
  · intro h p hp hpx
    by_contra hlt
    exact h ⟨p, hp, by omega, hpx⟩
  · rintro h ⟨p, hp, hkp, hpx⟩
    have := h p hp hpx
    omega

/--
Smooth exclusion criterion: if `x` has a prime factor `p > k`, then `x` cannot divide any power
`(k!)^r` of `k!`.
-/
theorem not_dvd_factorial_pow_of_hasLargePrimeFactor {k x : ℕ}
    (h : HasLargePrimeFactor k x) (r : ℕ) : ¬ (x ∣ (Nat.factorial k) ^ r) := by
  rcases h with ⟨p, hp, hkp, hpx⟩
  intro hxdvd
  have hpdvd_pow : p ∣ (Nat.factorial k) ^ r := dvd_trans hpx hxdvd
  have hpdvd_fact : p ∣ Nat.factorial k := hp.dvd_of_dvd_pow hpdvd_pow
  have hple : p ≤ k := (hp.dvd_factorial).mp hpdvd_fact
  omega

/--
Contrapositive smooth certificate: if `x` divides `(k!)^r` for some `r : ℕ`, then `x` has no prime
divisor `> k`.
-/
theorem not_hasLargePrimeFactor_of_dvd_factorial_pow {k x r : ℕ}
    (h : x ∣ (Nat.factorial k) ^ r) : ¬ HasLargePrimeFactor k x :=
  fun hlarge => not_dvd_factorial_pow_of_hasLargePrimeFactor hlarge r h

/--
Smooth exclusion criterion on runs: in any valid run `m + 1, ..., m + k`, none of the terms
`m + i` (`1 ≤ i ≤ k`) can divide any power `(k!)^r` of `k!`.
-/
theorem not_dvd_factorial_pow_of_isLargePrimeRun {m k i : ℕ}
    (hrun : IsLargePrimeRun m k) (hi : i ∈ Set.Icc 1 k) (r : ℕ) :
    ¬ ((m + i) ∣ (Nat.factorial k) ^ r) :=
  not_dvd_factorial_pow_of_hasLargePrimeFactor (hrun i hi) r

/--
Smooth blocker lemma: if `[m + 1, m + k]` contains an integer `s` that has no prime factor `> k`
(e.g., `s ∣ (k!)^r`), then `m` cannot start a valid run of length `k`.
-/
theorem not_isLargePrimeRun_of_smooth_mem_Icc {m k s : ℕ}
    (hs : s ∈ Set.Icc (m + 1) (m + k)) (hsmooth : ¬ HasLargePrimeFactor k s) :
    ¬ IsLargePrimeRun m k := by
  intro hrun
  rcases hs with ⟨hs1, hsk⟩
  have hi : s - m ∈ Set.Icc 1 k := ⟨by omega, by omega⟩
  have hlarge := hrun (s - m) hi
  have heq : m + (s - m) = s := by omega
  rw [heq] at hlarge
  exact hsmooth hlarge

/--
Left-shift smoothness obstruction: if `m ≥ 1` starts a valid run of length `k` and `m` itself has
a prime factor `p > k`, then `m - 1` also starts a valid run of length `k`. Consequently, any
minimal positive witness `m*(k)` must be `k`-smooth (`¬ HasLargePrimeFactor k m`).
-/
theorem isLargePrimeRun_pred_of_hasLargePrimeFactor {m k : ℕ} (hm : 1 ≤ m)
    (hrun : IsLargePrimeRun m k) (hm_large : HasLargePrimeFactor k m) :
    IsLargePrimeRun (m - 1) k := by
  intro i hi
  rcases hi with ⟨hi1, hik⟩
  rcases eq_or_lt_of_le hi1 with rfl | hi_gt1
  · have h_eq : m - 1 + 1 = m := by omega
    rw [h_eq]
    exact hm_large
  · have h_eq : m - 1 + i = m + (i - 1) := by omega
    rw [h_eq]
    exact hrun (i - 1) ⟨by omega, by omega⟩

/-! ### Downward Closure (Antitonicity) in `k` -/

theorem hasLargePrimeFactor_anti {k₁ k₂ x : ℕ} (hk : k₁ ≤ k₂)
    (h : HasLargePrimeFactor k₂ x) : HasLargePrimeFactor k₁ x := by
  rcases h with ⟨p, hp, hk₂p, hpx⟩
  exact ⟨p, hp, by omega, hpx⟩

theorem isLargePrimeRun_anti {m k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : IsLargePrimeRun m k₂) : IsLargePrimeRun m k₁ := by
  intro i hi
  rcases hi with ⟨hi1, hik₁⟩
  exact hasLargePrimeFactor_anti hk (h i ⟨hi1, le_trans hik₁ hk⟩)

theorem erdos962Prop_anti_right {n k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : Erdos962Prop n k₂) : Erdos962Prop n k₁ := by
  rcases h with ⟨m, hmn, hrun⟩
  exact ⟨m, hmn, isLargePrimeRun_anti hk hrun⟩

/-! ### Pairwise-Distinct Prime Witnesses and Prime-Interval Injection -/

/--
Fundamental spacing obstruction: any prime `p > k` can divide at most one integer in the window
`m + 1, ..., m + k`, because the difference between any two distinct elements is `< k < p`.
-/
theorem eq_of_large_prime_dvd_run {m k i j p : ℕ}
    (hi : i ∈ Set.Icc 1 k) (hj : j ∈ Set.Icc 1 k)
    (hkp : k < p) (hpi : p ∣ m + i) (hpj : p ∣ m + j) : i = j := by
  rcases hi with ⟨hi1, hik⟩
  rcases hj with ⟨hj1, hjk⟩
  rcases le_total i j with hij | hji
  · have hsub : p ∣ (m + j) - (m + i) := Nat.dvd_sub hpj hpi
    have hdiff : (m + j) - (m + i) = j - i := by omega
    rw [hdiff] at hsub
    have hlt : j - i < p := by omega
    have hzero : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hsub hlt
    omega
  · have hsub : p ∣ (m + i) - (m + j) := Nat.dvd_sub hpi hpj
    have hdiff : (m + i) - (m + j) = i - j := by omega
    rw [hdiff] at hsub
    have hlt : i - j < p := by omega
    have hzero : i - j = 0 := Nat.eq_zero_of_dvd_of_lt hsub hlt
    omega

/--
Any assignment `f : ℕ → ℕ` selecting a prime divisor `f i > k` of `m + i` for each `i ∈ [1, k]`
is injective on `Set.Icc 1 k`.
-/
theorem injOn_large_prime_witnesses {m k : ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ Set.Icc 1 k, Nat.Prime (f i) ∧ k < f i ∧ f i ∣ m + i) :
    Set.InjOn f (Set.Icc 1 k) := by
  intro i hi j hj hij
  have hfi := hf i hi
  have hfj := hf j hj
  have hpi : f i ∣ m + i := hfi.2.2
  have hpj : f i ∣ m + j := by simpa [hij] using hfj.2.2
  exact eq_of_large_prime_dvd_run hi hj hfi.2.1 hpi hpj

/--
Product lower bound along any large-prime witness assignment `f`:
`(k + 1)^k ≤ ∏ i ∈ Finset.Icc 1 k, f i ≤ ∏ i ∈ Finset.Icc 1 k, (m + i)`.
-/
theorem pow_succ_le_prod_large_prime_witnesses {m k : ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ Set.Icc 1 k, Nat.Prime (f i) ∧ k < f i ∧ f i ∣ m + i) :
    (k + 1) ^ k ≤ ∏ i ∈ Finset.Icc 1 k, f i ∧
      ∏ i ∈ Finset.Icc 1 k, f i ≤ ∏ i ∈ Finset.Icc 1 k, (m + i) := by
  constructor
  · have hcard : (Finset.Icc 1 k).card = k := by
      rw [Nat.card_Icc]; omega
    calc (k + 1) ^ k = ∏ _i ∈ Finset.Icc 1 k, (k + 1) := by
          rw [Finset.prod_const, hcard]
    _ ≤ ∏ i ∈ Finset.Icc 1 k, f i := by
          apply Finset.prod_le_prod
          intro i hi
          have hi_set : i ∈ Set.Icc 1 k := by simpa [Finset.coe_Icc] using hi
          have hkp := (hf i hi_set).2.1
          omega
  · apply Finset.prod_le_prod
    intro i hi
    have hi_set : i ∈ Set.Icc 1 k := by simpa [Finset.coe_Icc] using hi
    rcases hi_set with ⟨hi1, hik⟩
    exact Nat.le_of_dvd (by omega) (hf i ⟨hi1, hik⟩).2.2

/--
Every large prime divisor `p > k` of `m + i` (`i ∈ [1, k]`) lies in the prime interval
`(Finset.Icc (k + 1) (m + k)).filter Nat.Prime`.
-/
theorem large_prime_witness_mem_filter_Icc {m k i p : ℕ}
    (hi : i ∈ Set.Icc 1 k) (hp : Nat.Prime p) (hkp : k < p) (hpi : p ∣ m + i) :
    p ∈ (Finset.Icc (k + 1) (m + k)).filter Nat.Prime := by
  rcases hi with ⟨hi1, hik⟩
  have hpos : 0 < m + i := by omega
  have hple : p ≤ m + i := Nat.le_of_dvd hpos hpi
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, by omega⟩, hp⟩

/--
In any valid run `m + 1, ..., m + k`, the length `k` is bounded above by the number of primes in
`[k + 1, m + k]`, i.e., `k ≤ π(m + k) - π(k)`.
-/
theorem le_card_primes_Icc_of_isLargePrimeRun {m k : ℕ} (hrun : IsLargePrimeRun m k) :
    k ≤ ((Finset.Icc (k + 1) (m + k)).filter Nat.Prime).card := by
  let f : ℕ → ℕ := fun i =>
    if hi : i ∈ Set.Icc 1 k then Classical.choose (hrun i hi) else 0
  have hf : ∀ i ∈ Set.Icc 1 k, Nat.Prime (f i) ∧ k < f i ∧ f i ∣ m + i := by
    intro i hi
    dsimp [f]
    rw [dif_pos hi]
    exact Classical.choose_spec (hrun i hi)
  have hinj : Set.InjOn f (Finset.Icc 1 k : Set ℕ) := by
    simpa [Finset.coe_Icc] using injOn_large_prime_witnesses hf
  have hmaps : Set.MapsTo f (Finset.Icc 1 k : Set ℕ)
      (((Finset.Icc (k + 1) (m + k)).filter Nat.Prime : Finset ℕ) : Set ℕ) := by
    intro i hi
    have hi_set : i ∈ Set.Icc 1 k := by simpa [Finset.coe_Icc] using hi
    rcases hf i hi_set with ⟨hp, hkp, hpi⟩
    exact Finset.mem_coe.mpr (large_prime_witness_mem_filter_Icc hi_set hp hkp hpi)
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [Nat.card_Icc] using hcard

/--
For any valid run `m + 1, ..., m + k`, the starting offset satisfies `k ≤ m`.
-/
theorem le_witness_of_isLargePrimeRun {m k : ℕ} (hrun : IsLargePrimeRun m k) :
    k ≤ m := by
  have h1 : k ≤ ((Finset.Icc (k + 1) (m + k)).filter Nat.Prime).card :=
    le_card_primes_Icc_of_isLargePrimeRun hrun
  have h2 : ((Finset.Icc (k + 1) (m + k)).filter Nat.Prime).card ≤
      (Finset.Icc (k + 1) (m + k)).card := Finset.card_filter_le _ _
  have h3 : (Finset.Icc (k + 1) (m + k)).card = m := by
    rw [Nat.card_Icc]
    omega
  omega

/--
If `Erdos962Prop n k` holds, then `k ≤ n`.
-/
theorem erdos962Prop_imp_le {n k : ℕ} (h : Erdos962Prop n k) : k ≤ n := by
  rcases h with ⟨m, hmn, hrun⟩
  exact le_trans (le_witness_of_isLargePrimeRun hrun) hmn

/--
The set of valid run lengths `{k | Erdos962Prop n k}` is unconditionally bounded above by `n`.
-/
theorem bddAbove_erdos962Prop (n : ℕ) : BddAbove {k : ℕ | Erdos962Prop n k} :=
  ⟨n, fun _ hk => erdos962Prop_imp_le hk⟩

/-! ### Small-Prime Multiple Obstruction and Unconditional Bertrand Quadratic Bound -/

/--
For every prime `q ≤ k`, among the first `q` consecutive integers `m + 1, ..., m + q` of the run
there is a multiple of `q`, which must also be divisible by a prime `p > k ≥ q`. Coprimality of
`q` and `p` forces `q * (k + 1) ≤ q * p ≤ m + q`, hence `q * k ≤ m`.
-/
theorem prime_mul_le_witness_of_isLargePrimeRun {m k q : ℕ}
    (hq : Nat.Prime q) (hqk : q ≤ k) (hrun : IsLargePrimeRun m k) :
    q * k ≤ m := by
  have hq_pos : 0 < q := hq.pos
  have hmod_lt : m % q < q := Nat.mod_lt m hq_pos
  let i := q - m % q
  have hi1 : 1 ≤ i := by omega
  have hiq : i ≤ q := by omega
  have hik : i ≤ k := le_trans hiq hqk
  have hq_dvd : q ∣ m + i := by
    refine ⟨m / q + 1, ?_⟩
    have hdiv : q * (m / q) + m % q = m := Nat.div_add_mod m q
    calc m + i = (q * (m / q) + m % q) + (q - m % q) := by rw [hdiv]
    _ = q * (m / q) + q := by omega
    _ = q * (m / q + 1) := by ring
  rcases hrun i ⟨hi1, hik⟩ with ⟨p, hp, hkp, hp_dvd⟩
  have hqp_ne : q ≠ p := by omega
  have hcop : Nat.Coprime q p :=
    (Nat.Prime.coprime_iff_not_dvd hq).mpr (by
      intro hqp
      rcases (Nat.dvd_prime hp).mp hqp with h1 | h2
      · have := hq.two_le; omega
      · exact hqp_ne h2)
  have hmul_dvd : q * p ∣ m + i := hcop.mul_dvd_of_dvd_of_dvd hq_dvd hp_dvd
  have hmul_le : q * p ≤ m + i := Nat.le_of_dvd (by omega) hmul_dvd
  have hkp1 : q * (k + 1) ≤ q * p := Nat.mul_le_mul_left q (by omega)
  have h_expand : q * k + q ≤ m + q := by
    calc q * k + q = q * (k + 1) := by ring
    _ ≤ q * p := hkp1
    _ ≤ m + i := hmul_le
    _ ≤ m + q := by omega
  omega

/--
For every prime `q ≤ k`, `Erdos962Prop n k` implies `q * k ≤ n`.
-/
theorem erdos962Prop_imp_prime_mul_le {n k q : ℕ}
    (hq : Nat.Prime q) (hqk : q ≤ k) (h : Erdos962Prop n k) :
    q * k ≤ n := by
  rcases h with ⟨m, hmn, hrun⟩
  exact le_trans (prime_mul_le_witness_of_isLargePrimeRun hq hqk hrun) hmn

/--
Specializing `prime_mul_le_witness_of_isLargePrimeRun` to `q = 2`: for `k ≥ 2`, `2 * k ≤ m`.
-/
theorem two_mul_le_witness_of_isLargePrimeRun {m k : ℕ} (hk : 2 ≤ k)
    (hrun : IsLargePrimeRun m k) : 2 * k ≤ m :=
  prime_mul_le_witness_of_isLargePrimeRun Nat.prime_two hk hrun

/--
Specializing `prime_mul_le_witness_of_isLargePrimeRun` to `q = 3`: for `k ≥ 3`, `3 * k ≤ m`.
-/
theorem three_mul_le_witness_of_isLargePrimeRun {m k : ℕ} (hk : 3 ≤ k)
    (hrun : IsLargePrimeRun m k) : 3 * k ≤ m :=
  prime_mul_le_witness_of_isLargePrimeRun Nat.prime_three hk hrun

/--
By Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`), for any `k ≥ 2` there exists a
prime `q ∈ (k / 2, k]`, which forces `(k / 2 + 1) * k ≤ m` for any valid run starting at `m`.
-/
theorem half_succ_mul_le_witness_of_isLargePrimeRun {m k : ℕ} (hk : 2 ≤ k)
    (hrun : IsLargePrimeRun m k) : (k / 2 + 1) * k ≤ m := by
  have hk2_ne : k / 2 ≠ 0 := by omega
  rcases Nat.exists_prime_lt_and_le_two_mul (k / 2) hk2_ne with ⟨q, hq, hq_gt, hq_le⟩
  have hqk : q ≤ k := by omega
  have hqm : q * k ≤ m := prime_mul_le_witness_of_isLargePrimeRun hq hqk hrun
  have hle : (k / 2 + 1) * k ≤ q * k := Nat.mul_le_mul_right k (by omega)
  exact le_trans hle hqm

/--
Unconditional quadratic lower bound on witnesses: for every `m, k : ℕ`, `IsLargePrimeRun m k`
implies `k * (k + 1) ≤ 2 * m`.
-/
theorem mul_succ_le_two_mul_witness_of_isLargePrimeRun {m k : ℕ}
    (hrun : IsLargePrimeRun m k) : k * (k + 1) ≤ 2 * m := by
  rcases lt_or_ge k 2 with hk_lt | hk_ge
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · omega
    · have hm : 1 ≤ m := le_witness_of_isLargePrimeRun hrun
      omega
  · have hhalf := half_succ_mul_le_witness_of_isLargePrimeRun hk_ge hrun
    have h2 : k + 1 ≤ 2 * (k / 2 + 1) := by omega
    calc k * (k + 1) = (k + 1) * k := Nat.mul_comm _ _
    _ ≤ (2 * (k / 2 + 1)) * k := Nat.mul_le_mul_right k h2
    _ = 2 * ((k / 2 + 1) * k) := by ring
    _ ≤ 2 * m := Nat.mul_le_mul_left 2 hhalf

/-! ### Properties of `k(n)` (`sSup` Characterization, Downward Closure, Monotonicity, Bounds) -/

theorem le_k_of_erdos962Prop {n k₀ : ℕ} (h : Erdos962Prop n k₀) : k₀ ≤ k n := by
  classical
  exact Nat.le_findGreatest (erdos962Prop_imp_le h) h

/--
Exact characterization of `Erdos962Prop` via `k(n)`: `Erdos962Prop n k₀` holds if and only if
`k₀ ≤ k(n)`.
-/
theorem erdos962Prop_iff_le_k (n k₀ : ℕ) :
    Erdos962Prop n k₀ ↔ k₀ ≤ k n := by
  constructor
  · exact le_k_of_erdos962Prop
  · intro hk₀
    exact erdos962Prop_anti_right hk₀ (erdos962Prop_k n)

theorem setOf_erdos962Prop_eq_Iic (n : ℕ) :
    {k₀ : ℕ | Erdos962Prop n k₀} = Set.Iic (k n) := by
  ext k₀
  exact erdos962Prop_iff_le_k n k₀

theorem not_erdos962Prop_of_k_lt {n k₀ : ℕ} (h : k n < k₀) : ¬ Erdos962Prop n k₀ := by
  intro hk₀
  have := le_k_of_erdos962Prop hk₀
  omega

/--
`k(n)` is monotonically non-decreasing in `n`.
-/
theorem k_mono : Monotone k := by
  intro n₁ n₂ h
  exact le_k_of_erdos962Prop (erdos962Prop_mono_left h (erdos962Prop_k n₁))

/--
Because `Erdos962Prop n k₀` implies `k₀ ≤ n`, `k(n)` defined via `Nat.findGreatest` coincides
with the unconstrained supremum `sSup {k₀ : ℕ | Erdos962Prop n k₀}`.
-/
theorem k_eq_sSup (n : ℕ) : k n = sSup {k₀ : ℕ | Erdos962Prop n k₀} := by
  apply le_antisymm
  · exact le_csSup (bddAbove_erdos962Prop n) (erdos962Prop_k n)
  · exact csSup_le ⟨0, erdos962Prop_zero n⟩ (fun _ hk₀ => le_k_of_erdos962Prop hk₀)

/--
When `2 ≤ k(n)`, the parity obstruction forces `2 * k(n) ≤ n` (i.e., `k(n) ≤ n / 2`).
-/
theorem two_mul_k_le_self_of_two_le {n : ℕ} (hk : 2 ≤ k n) : 2 * k n ≤ n :=
  erdos962Prop_imp_prime_mul_le Nat.prime_two hk (erdos962Prop_k n)

theorem k_le_div_two_of_two_le {n : ℕ} (hk : 2 ≤ k n) : k n ≤ n / 2 := by
  have := two_mul_k_le_self_of_two_le hk
  omega

/--
When `3 ≤ k(n)`, the mod-3 obstruction forces `3 * k(n) ≤ n` (i.e., `k(n) ≤ n / 3`).
-/
theorem three_mul_k_le_self_of_three_le {n : ℕ} (hk : 3 ≤ k n) : 3 * k n ≤ n :=
  erdos962Prop_imp_prime_mul_le Nat.prime_three hk (erdos962Prop_k n)

/--
Unconditional quadratic upper bound on `k(n)` for all `n : ℕ`: `k(n) * (k(n) + 1) ≤ 2 * n`.
-/
theorem k_mul_succ_le_two_mul (n : ℕ) : k n * (k n + 1) ≤ 2 * n := by
  rcases erdos962Prop_k n with ⟨m, hmn, hrun⟩
  exact le_trans (mul_succ_le_two_mul_witness_of_isLargePrimeRun hrun) (Nat.mul_le_mul_left 2 hmn)

/--
Unconditional square upper bound on `k(n)` for all `n : ℕ`: `(k n)^2 ≤ 2 * n`.
-/
theorem k_sq_le_two_mul (n : ℕ) : (k n) ^ 2 ≤ 2 * n := by
  have h := k_mul_succ_le_two_mul n
  have hsq : (k n) ^ 2 ≤ k n * (k n + 1) := by
    calc (k n) ^ 2 = k n * k n := sq (k n)
    _ ≤ k n * (k n + 1) := Nat.mul_le_mul_left (k n) (by omega)
  exact le_trans hsq h

/-! ### Exact Small-`n` Evaluations and Jump Horizons -/

@[simp]
theorem k_zero : k 0 = 0 := by
  have := k_le_self 0
  omega

theorem erdos962Prop_one_one : Erdos962Prop 1 1 := by
  refine ⟨1, le_rfl, ?_⟩
  intro i hi
  rcases hi with ⟨hi1, hik⟩
  have hi_eq : i = 1 := by omega
  subst hi_eq
  exact ⟨2, Nat.prime_two, by decide, by decide⟩

theorem one_le_k_of_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ k n :=
  le_k_of_erdos962Prop (erdos962Prop_mono_left hn erdos962Prop_one_one)

/--
For all `n ∈ [1, 3]`, `k(n) = 1`.
-/
theorem k_eq_one_of_Icc {n : ℕ} (hn : n ∈ Set.Icc 1 3) : k n = 1 := by
  rcases hn with ⟨hn1, hn3⟩
  have hge : 1 ≤ k n := one_le_k_of_pos hn1
  by_contra hne
  have h2 : 2 ≤ k n := by omega
  have h2n : 2 * k n ≤ n := two_mul_k_le_self_of_two_le h2
  omega

@[simp] theorem k_one : k 1 = 1 := k_eq_one_of_Icc ⟨by decide, by decide⟩

theorem erdos962Prop_four_two : Erdos962Prop 4 2 := by
  refine ⟨4, le_rfl, ?_⟩
  intro i hi
  rcases hi with ⟨hi1, hi2⟩
  interval_cases i
  · exact ⟨5, by decide, by decide, by decide⟩
  · exact ⟨3, by decide, by decide, by decide⟩

theorem two_le_k_of_four_le {n : ℕ} (hn : 4 ≤ n) : 2 ≤ k n :=
  le_k_of_erdos962Prop (erdos962Prop_mono_left hn erdos962Prop_four_two)

/--
Every `m ≤ 11` fails `IsLargePrimeRun m 3`: for `m < 9` this follows from `3 * 3 ≤ m`, while for
`m ∈ [9, 11]` the window `[m + 1, m + 3]` contains `12`, which divides `(3!)^2 = 36`.
-/
theorem not_erdos962Prop_eleven_three : ¬ Erdos962Prop 11 3 := by
  rintro ⟨m, hm11, hrun⟩
  have hm9 : 9 ≤ m := three_mul_le_witness_of_isLargePrimeRun (by decide) hrun
  have h12_mem : 12 ∈ Set.Icc (m + 1) (m + 3) := ⟨by omega, by omega⟩
  have h12_smooth : ¬ HasLargePrimeFactor 3 12 :=
    not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 2) (by decide)
  exact not_isLargePrimeRun_of_smooth_mem_Icc h12_mem h12_smooth hrun

/--
For all `n ∈ [4, 11]`, `k(n) = 2`.
-/
theorem k_eq_two_of_Icc {n : ℕ} (hn : n ∈ Set.Icc 4 11) : k n = 2 := by
  rcases hn with ⟨hn4, hn11⟩
  have hge : 2 ≤ k n := two_le_k_of_four_le hn4
  have hle11 : k n ≤ k 11 := k_mono hn11
  have hk11_lt : ¬ (3 ≤ k 11) := by
    intro h3
    exact not_erdos962Prop_eleven_three ((erdos962Prop_iff_le_k 11 3).mpr h3)
  omega

@[simp] theorem k_four : k 4 = 2 := k_eq_two_of_Icc ⟨by decide, by decide⟩

theorem erdos962Prop_twelve_three : Erdos962Prop 12 3 := by
  refine ⟨12, le_rfl, ?_⟩
  intro i hi
  rcases hi with ⟨hi1, hi3⟩
  interval_cases i
  · exact ⟨13, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩
  · exact ⟨5, by decide, by decide, by decide⟩

/--
Every `m ≤ 17` fails `IsLargePrimeRun m 4`: for `m < 12` this follows from `3 * 4 ≤ m`, while for
`m ∈ [12, 15]` the window contains `16 ∣ (4!)^2` and for `m ∈ [14, 17]` it contains `18 ∣ (4!)^2`.
-/
theorem not_erdos962Prop_seventeen_four : ¬ Erdos962Prop 17 4 := by
  rintro ⟨m, hm17, hrun⟩
  have hm12 : 12 ≤ m := three_mul_le_witness_of_isLargePrimeRun (by decide) hrun
  rcases le_or_gt m 15 with hm15 | hm16
  · have h16_mem : 16 ∈ Set.Icc (m + 1) (m + 4) := ⟨by omega, by omega⟩
    have h16_smooth : ¬ HasLargePrimeFactor 4 16 :=
      not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 2) (by decide)
    exact not_isLargePrimeRun_of_smooth_mem_Icc h16_mem h16_smooth hrun
  · have h18_mem : 18 ∈ Set.Icc (m + 1) (m + 4) := ⟨by omega, by omega⟩
    have h18_smooth : ¬ HasLargePrimeFactor 4 18 :=
      not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 2) (by decide)
    exact not_isLargePrimeRun_of_smooth_mem_Icc h18_mem h18_smooth hrun

/--
For all `n ∈ [12, 17]`, `k(n) = 3`.
-/
theorem k_eq_three_of_Icc {n : ℕ} (hn : n ∈ Set.Icc 12 17) : k n = 3 := by
  rcases hn with ⟨hn12, hn17⟩
  have hge : 3 ≤ k n :=
    le_k_of_erdos962Prop (erdos962Prop_mono_left hn12 erdos962Prop_twelve_three)
  have hle17 : k n ≤ k 17 := k_mono hn17
  have hk17_lt : ¬ (4 ≤ k 17) := by
    intro h4
    exact not_erdos962Prop_seventeen_four ((erdos962Prop_iff_le_k 17 4).mpr h4)
  omega

@[simp] theorem k_twelve : k 12 = 3 := k_eq_three_of_Icc ⟨by decide, by decide⟩

theorem erdos962Prop_eighteen_four : Erdos962Prop 18 4 := by
  refine ⟨18, le_rfl, ?_⟩
  intro i hi
  rcases hi with ⟨hi1, hi4⟩
  interval_cases i
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨5, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩
  · exact ⟨11, by decide, by decide, by decide⟩

theorem four_le_k_of_eighteen_le {n : ℕ} (hn : 18 ≤ n) : 4 ≤ k n :=
  le_k_of_erdos962Prop (erdos962Prop_mono_left hn erdos962Prop_eighteen_four)

/-!
## Divisor-remainder obstructions and the square-root bound

For any positive integer `d ≤ k` and any prime `p > k`, `p` cannot divide `d`, so primality of `p`
alone gives `Nat.Coprime d p`. Applied to the unique multiple `m + (d - m % d)` of `d` in the
sub-window `[m + 1, m + d] ⊆ [m + 1, m + k]`, this yields the divisor-remainder obstruction
`d * k + m % d ≤ m` for every `1 ≤ d ≤ k`.

Setting `d = k` removes the factor of 2 from the Bertrand argument and gives `k ^ 2 ≤ m` for every
valid run, hence `(k n) ^ 2 ≤ n` and `k n ≤ sqrt n` for all `n`.
-/

/-! ### Coprimality and divisor-multiple remainder obstructions -/

/--
Any positive integer `d ≤ k` is coprime to every prime `p > k`, because `0 < d < p` prevents `p`
from dividing `d`.
-/
theorem coprime_of_prime_gt_of_pos_le {d k p : ℕ}
    (hd : 1 ≤ d) (hdk : d ≤ k) (hp : Nat.Prime p) (hkp : k < p) :
    Nat.Coprime d p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpd
  have hle : p ≤ d := Nat.le_of_dvd (by omega) hpd
  omega

/--
For every positive integer `d`, the shift `i = d - m % d` lies in `[1, d]` and makes `m + i`
a positive multiple of `d`.
-/
theorem dvd_add_sub_mod_of_pos {m d : ℕ} (hd : 1 ≤ d) :
    d - m % d ∈ Set.Icc 1 d ∧ d ∣ m + (d - m % d) := by
  have hmod : m % d < d := Nat.mod_lt m (by omega)
  refine ⟨⟨by omega, by omega⟩, ⟨m / d + 1, ?_⟩⟩
  have hdiv : d * (m / d) + m % d = m := Nat.div_add_mod m d
  calc m + (d - m % d) = (d * (m / d) + m % d) + (d - m % d) := by rw [hdiv]
  _ = d * (m / d) + d := by omega
  _ = d * (m / d + 1) := by ring

/--
In any valid run `IsLargePrimeRun m k`, for every `d` with `1 ≤ d ≤ k`, there exists a prime
`p > k` such that `d * p` divides `m + (d - m % d)`.
-/
theorem exists_prime_gt_mul_dvd_shift_of_isLargePrimeRun {m k d : ℕ}
    (hd : 1 ≤ d) (hdk : d ≤ k) (hrun : IsLargePrimeRun m k) :
    ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ d * p ∣ m + (d - m % d) := by
  rcases dvd_add_sub_mod_of_pos (m := m) hd with ⟨⟨hi1, hid⟩, hd_dvd⟩
  have hi_mem : d - m % d ∈ Set.Icc 1 k := ⟨hi1, le_trans hid hdk⟩
  rcases hrun (d - m % d) hi_mem with ⟨p, hp, hkp, hp_dvd⟩
  have hcop : Nat.Coprime d p := coprime_of_prime_gt_of_pos_le hd hdk hp hkp
  exact ⟨p, hp, hkp, hcop.mul_dvd_of_dvd_of_dvd hd_dvd hp_dvd⟩

/--
Universal divisor-remainder lower bound: for any valid run `IsLargePrimeRun m k` and any `d` with
`1 ≤ d ≤ k`, we have `d * k + m % d ≤ m`.
-/
theorem mul_add_mod_le_witness_of_isLargePrimeRun {m k d : ℕ}
    (hd : 1 ≤ d) (hdk : d ≤ k) (hrun : IsLargePrimeRun m k) :
    d * k + m % d ≤ m := by
  rcases exists_prime_gt_mul_dvd_shift_of_isLargePrimeRun hd hdk hrun with ⟨p, _, hkp, hmul_dvd⟩
  have hmod : m % d < d := Nat.mod_lt m (by omega)
  have hpos : 0 < m + (d - m % d) := by omega
  have hmul_le : d * p ≤ m + (d - m % d) := Nat.le_of_dvd hpos hmul_dvd
  have hkp1 : d * (k + 1) ≤ d * p := Nat.mul_le_mul_left d (by omega)
  have hexpand : d * k + d ≤ m + (d - m % d) := by
    calc d * k + d = d * (k + 1) := by ring
    _ ≤ d * p := hkp1
    _ ≤ m + (d - m % d) := hmul_le
  omega

/--
Universal divisor-multiple lower bound on witnesses: for *every* `d ≤ k` (without any primality
assumption on `d`), `IsLargePrimeRun m k` implies `d * k ≤ m`.
-/
theorem mul_le_witness_of_isLargePrimeRun {m k d : ℕ}
    (hdk : d ≤ k) (hrun : IsLargePrimeRun m k) :
    d * k ≤ m := by
  rcases eq_or_lt_of_le (Nat.zero_le d) with rfl | hd_pos
  · simp
  · have h := mul_add_mod_le_witness_of_isLargePrimeRun hd_pos hdk hrun
    omega

/--
For every `d ≤ k₀`, `Erdos962Prop n k₀` implies `d * k₀ ≤ n`.
-/
theorem erdos962Prop_imp_mul_le {n k₀ d : ℕ}
    (hdk : d ≤ k₀) (h : Erdos962Prop n k₀) :
    d * k₀ ≤ n := by
  rcases h with ⟨m, hmn, hrun⟩
  exact le_trans (mul_le_witness_of_isLargePrimeRun hdk hrun) hmn

/--
For every `d ≤ k(n)`, `d * k(n) ≤ n`.
-/
theorem mul_k_le_self_of_le_k {n d : ℕ} (hd : d ≤ k n) :
    d * k n ≤ n :=
  erdos962Prop_imp_mul_le hd (erdos962Prop_k n)

/--
Quotient upper bound on `k(n)`: for every `d` with `1 ≤ d ≤ k(n)`, `k(n) ≤ n / d`.
-/
theorem k_le_div_of_pos_of_le_k {n d : ℕ} (hd_pos : 1 ≤ d) (hd : d ≤ k n) :
    k n ≤ n / d := by
  have hmul : d * k n ≤ n := mul_k_le_self_of_le_k hd
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)

/-! ### Unconditional Square Bound `k(n)^2 ≤ n` and Integer Square-Root Bridge -/

/--
Specializing the divisor-remainder bound to `d = k`: for every `k ≥ 1`, `IsLargePrimeRun m k`
implies `k ^ 2 + m % k ≤ m`.
-/
theorem sq_add_mod_le_witness_of_isLargePrimeRun {m k : ℕ}
    (hk : 1 ≤ k) (hrun : IsLargePrimeRun m k) :
    k ^ 2 + m % k ≤ m := by
  have h := mul_add_mod_le_witness_of_isLargePrimeRun hk le_rfl hrun
  simpa [sq] using h

/--
Unconditional square lower bound on witnesses: for all `m, k : ℕ`, `IsLargePrimeRun m k` implies
`k ^ 2 ≤ m`. This removes the Bertrand factor of `2` from
`mul_succ_le_two_mul_witness_of_isLargePrimeRun`.
-/
theorem sq_le_witness_of_isLargePrimeRun {m k : ℕ} (hrun : IsLargePrimeRun m k) :
    k ^ 2 ≤ m := by
  have h := mul_le_witness_of_isLargePrimeRun le_rfl hrun
  simpa [sq] using h

/--
Integer square-root upper bound on run length: `IsLargePrimeRun m k` implies `k ≤ Nat.sqrt m`.
-/
theorem le_sqrt_witness_of_isLargePrimeRun {m k : ℕ} (hrun : IsLargePrimeRun m k) :
    k ≤ Nat.sqrt m := by
  rw [Nat.le_sqrt]
  exact mul_le_witness_of_isLargePrimeRun le_rfl hrun

/--
If `Erdos962Prop n k₀` holds, then `k₀ ^ 2 ≤ n`.
-/
theorem erdos962Prop_imp_sq_le {n k₀ : ℕ} (h : Erdos962Prop n k₀) :
    k₀ ^ 2 ≤ n := by
  rcases h with ⟨m, hmn, hrun⟩
  exact le_trans (sq_le_witness_of_isLargePrimeRun hrun) hmn

/--
Contrapositive square obstruction: if `n < k₀ ^ 2`, then `¬ Erdos962Prop n k₀`.
-/
theorem not_erdos962Prop_of_lt_sq {n k₀ : ℕ} (h : n < k₀ ^ 2) :
    ¬ Erdos962Prop n k₀ := by
  intro hk₀
  have hle := erdos962Prop_imp_sq_le hk₀
  omega

/--
Unconditional square upper bound on `k(n)` for all `n : ℕ`: `(k n) ^ 2 ≤ n`.
This sharpens `k_sq_le_two_mul : (k n) ^ 2 ≤ 2 * n` by a factor of `2`.
-/
theorem k_sq_le_self (n : ℕ) : (k n) ^ 2 ≤ n :=
  erdos962Prop_imp_sq_le (erdos962Prop_k n)

/--
Unconditional integer square-root upper bound on `k(n)` for all `n : ℕ`: `k n ≤ Nat.sqrt n`.
-/
theorem k_le_sqrt (n : ℕ) : k n ≤ Nat.sqrt n := by
  rw [Nat.le_sqrt, ← sq]
  exact k_sq_le_self n

/-! ### Real-Valued Square-Root Bound and `erdos_962.variants.tao_upper_bound` -/

/--
Real-cast square upper bound: for all `n : ℕ`, `((k n : ℝ)) ^ 2 ≤ (n : ℝ)`.
-/
theorem cast_k_sq_le_cast (n : ℕ) : ((k n : ℝ)) ^ 2 ≤ (n : ℝ) := by
  exact_mod_cast k_sq_le_self n

/--
Unconditional real square-root upper bound: for all `n : ℕ`, `(k n : ℝ) ≤ Real.sqrt (n : ℝ)`.
-/
theorem cast_k_le_real_sqrt (n : ℕ) : (k n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hcast : ((k n : ℝ)) ^ 2 ≤ (n : ℝ) := cast_k_sq_le_cast n
  have hk_nonneg : 0 ≤ (k n : ℝ) := Nat.cast_nonneg (k n)
  calc (k n : ℝ) = Real.sqrt (((k n : ℝ)) ^ 2) := (Real.sqrt_sq hk_nonneg).symm
  _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hcast

/--
For every `n : ℕ` and every `ε : ℝ` with `0 ≤ ε`, `(k n : ℝ) ≤ (1 + ε) * Real.sqrt (n : ℝ)`.
-/
theorem cast_k_le_one_add_eps_mul_sqrt (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (k n : ℝ) ≤ (1 + ε) * Real.sqrt (n : ℝ) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg (n : ℝ)
  have h1 : (k n : ℝ) ≤ 1 * Real.sqrt (n : ℝ) := by
    simpa using cast_k_le_real_sqrt n
  have h2 : 1 * Real.sqrt (n : ℝ) ≤ (1 + ε) * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hsqrt_nonneg
  exact le_trans h1 h2

/--
Unconditional resolution of `erdos_962.variants.tao_upper_bound`:
there exists `ε : ℕ → ℝ` with `ε(n) → 0` (namely `ε(n) = 0`) such that eventually
`(k n : ℝ) ≤ (1 + ε n) * Real.sqrt (n : ℝ)`.
-/
theorem erdos_962_variants_tao_upper_bound_impl :
    ∃ ε : ℕ → ℝ,
      (∀ δ > 0, ∀ᶠ n in atTop, |ε n| < δ) ∧
      ∀ᶠ n : ℕ in atTop,
        (k n : ℝ) ≤ (1 + ε n) * Real.sqrt (n : ℝ) := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro δ hδ
    exact Filter.Eventually.of_forall (fun _ => by simpa using hδ)
  · exact Filter.Eventually.of_forall (fun n => by simpa using cast_k_le_real_sqrt n)

/--
Logarithmic upper bound on `k(n)`: for every `n ≥ 1`,
`Real.log (k n : ℝ) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ)`.
-/
theorem log_cast_k_le_half_log {n : ℕ} (hn : 1 ≤ n) :
    Real.log (k n : ℝ) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
  have hk_pos : 1 ≤ k n := one_le_k_of_pos hn
  have hk_real_pos : 0 < (k n : ℝ) := by exact_mod_cast (by omega : 0 < k n)
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog : Real.log (k n : ℝ) ≤ Real.log (Real.sqrt (n : ℝ)) :=
    Real.log_le_log hk_real_pos (cast_k_le_real_sqrt n)
  rw [Real.log_sqrt hn_nonneg] at hlog
  linarith

/-! ### Prime-Gap and Composite-Successor Refinements Beyond `k^2 ≤ m` -/

/--
Prime-gap lower bound above `k`: if `1 ≤ d ≤ k`, `1 ≤ B`, and every prime `p > k` satisfies
`B ≤ p`, then any valid run `IsLargePrimeRun m k` satisfies `d * (B - 1) + m % d ≤ m`.
-/
theorem mul_pred_add_mod_le_witness_of_forall_prime_gt_ge {m k d B : ℕ}
    (hd : 1 ≤ d) (hdk : d ≤ k) (hB : 1 ≤ B)
    (hgap : ∀ p : ℕ, Nat.Prime p → k < p → B ≤ p)
    (hrun : IsLargePrimeRun m k) :
    d * (B - 1) + m % d ≤ m := by
  rcases exists_prime_gt_mul_dvd_shift_of_isLargePrimeRun hd hdk hrun with ⟨p, hp, hkp, hmul_dvd⟩
  have hBp : B ≤ p := hgap p hp hkp
  have hmod : m % d < d := Nat.mod_lt m (by omega)
  have hpos : 0 < m + (d - m % d) := by omega
  have hmul_le : d * p ≤ m + (d - m % d) := Nat.le_of_dvd hpos hmul_dvd
  have hB_le : d * B ≤ d * p := Nat.mul_le_mul_left d hBp
  have hexpand : d * (B - 1) + d ≤ m + (d - m % d) := by
    calc d * (B - 1) + d = d * (B - 1 + 1) := by ring
    _ = d * B := by rw [Nat.sub_add_cancel hB]
    _ ≤ d * p := hB_le
    _ ≤ m + (d - m % d) := hmul_le
  omega

/--
Whenever `k + 1` is not prime and `1 ≤ k`, every prime `p > k` satisfies `k + 2 ≤ p`, so any
valid run `IsLargePrimeRun m k` satisfies `k * (k + 1) + m % k ≤ m`.
-/
theorem mul_succ_add_mod_le_witness_of_not_prime_succ {m k : ℕ}
    (hk : 1 ≤ k) (hcomp : ¬ Nat.Prime (k + 1)) (hrun : IsLargePrimeRun m k) :
    k * (k + 1) + m % k ≤ m := by
  have hgap : ∀ p : ℕ, Nat.Prime p → k < p → k + 2 ≤ p := by
    intro p hp hkp
    by_contra hlt
    have heq : p = k + 1 := by omega
    rw [heq] at hp
    exact hcomp hp
  have h := mul_pred_add_mod_le_witness_of_forall_prime_gt_ge
    hk le_rfl (by omega : 1 ≤ k + 2) hgap hrun
  simpa using h

/--
Whenever `k + 1` is not prime, any valid run `IsLargePrimeRun m k` satisfies `k * (k + 1) ≤ m`.
-/
theorem mul_succ_le_witness_of_not_prime_succ {m k : ℕ}
    (hcomp : ¬ Nat.Prime (k + 1)) (hrun : IsLargePrimeRun m k) :
    k * (k + 1) ≤ m := by
  rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
  · simp
  · have h := mul_succ_add_mod_le_witness_of_not_prime_succ hk_pos hcomp hrun
    omega

/--
For every odd `k ≥ 3` (`k % 2 = 1`), `k + 1` is an even integer `≥ 4` and hence not prime;
therefore `IsLargePrimeRun m k` implies `k * (k + 1) ≤ m`.
-/
theorem mul_succ_le_witness_of_odd {m k : ℕ}
    (hk : 3 ≤ k) (hodd : k % 2 = 1) (hrun : IsLargePrimeRun m k) :
    k * (k + 1) ≤ m := by
  have hcomp : ¬ Nat.Prime (k + 1) := by
    intro hp
    have hdvd : 2 ∣ k + 1 := by omega
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2 <;> omega
  exact mul_succ_le_witness_of_not_prime_succ hcomp hrun

/--
Whenever `k(n) + 1` is not prime, `k(n) * (k(n) + 1) ≤ n`.
-/
theorem k_mul_succ_le_self_of_not_prime_succ {n : ℕ}
    (hcomp : ¬ Nat.Prime (k n + 1)) :
    k n * (k n + 1) ≤ n := by
  rcases erdos962Prop_k n with ⟨m, hmn, hrun⟩
  exact le_trans (mul_succ_le_witness_of_not_prime_succ hcomp hrun) hmn

/-!
## Two-Divisor Collision Dichotomy, Second-Prime Lower Bounds, and Exact Plateaus on `[18, 63]`

In `Erdos962Unified435`, the single-divisor remainder obstruction `mul_add_mod_le_witness_of_isLargePrimeRun`
established `d * k + m % d ≤ m` for every `1 ≤ d ≤ k`, yielding `k ^ 2 ≤ m` and `k(n) ≤ √n`.

Here we combine *two* coprime divisors `1 ≤ d₁, d₂ ≤ k` (`Nat.Coprime d₁ d₂`), specializing in
particular to consecutive divisors `k` and `k - 1` (`k ≥ 2`). In any valid run `IsLargePrimeRun m k`,
let `i₁ = d₁ - m % d₁ ∈ [1, d₁]` and `i₂ = d₂ - m % d₂ ∈ [1, d₂]` be the remainder shifts where
`d₁ ∣ m + i₁` and `d₂ ∣ m + i₂`. A sharp structural dichotomy governs the run:

1. **Shift-collision branch (`i₁ = i₂`):** Both `d₁` and `d₂` divide the same term `m + i₂`, which
   also has a prime divisor `p > k`. Since `d₁, d₂, p` are pairwise coprime, `d₁ * d₂ * p ∣ m + i₂`,
   forcing the cubic lower bound `d₁ * d₂ * (k + 1) ≤ m + i₂` (and for `d₁ = k, d₂ = k - 1`,
   `k * (k - 1) * (k + 1) ≤ m + (k - 1) ≤ m + k`).
2. **Distinct-shift branch (`i₁ ≠ i₂`):** By injectivity of large prime divisors across `[1, k]`
   (`eq_of_large_prime_dvd_run`), any large prime divisors `p₁ > k` of `m + i₁` and `p₂ > k` of
   `m + i₂` must be distinct (`p₁ ≠ p₂`). Since every prime `p > k ≥ 2` is odd, two distinct primes
   `> k` satisfy `max p₁ p₂ ≥ k + 3` (and `≥ k + 4` when `k ≥ 3` is odd).

Combining both branches yields the unconditional universal upgrade `(k - 1) * (k + 2) ≤ m`
(and `k ^ 2 + k - 2 ≤ m` for `k ≥ 2`, `(k - 1) * (k + 3) ≤ m` for odd `k ≥ 3`), which is sharp with
equality at `k = 2` (`m = 4`), `k = 3` (`m = 12`), and `k = 4` (`m = 18`). Parameterizing the
dichotomy by lower bounds `(B₁, B₂)` on the first two primes above `k` (`B₁ = 7, B₂ = 11` for
`k ∈ {5, 6}`) proves `40 ≤ m` for `k = 5` and `50 ≤ m` for `k = 6`, reducing the exact plateau
proofs `k(n) = 4` on `[18, 53]` and `k(n) = 5` on `[54, 63]` to three smooth blockers each.
-/

/-! ### Oddness of Large Primes and Prime-Pair Gap Lower Bounds -/

/--
Every prime `p > k` with `2 ≤ k` is strictly greater than `2` and therefore odd (`p % 2 = 1`).
-/
theorem odd_of_prime_gt_of_two_le {k p : ℕ}
    (hk : 2 ≤ k) (hp : Nat.Prime p) (hkp : k < p) :
    p % 2 = 1 := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · omega
  · exact hodd

/--
Any two distinct primes `p ≠ q` strictly greater than `k` (`2 ≤ k`) are distinct odd integers `> k`,
and therefore satisfy `k + 3 ≤ max p q`.
-/
theorem add_three_le_max_of_two_le_of_prime_gt_of_prime_gt {k p q : ℕ}
    (hk : 2 ≤ k) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hkp : k < p) (hkq : k < q) (hne : p ≠ q) :
    k + 3 ≤ max p q := by
  have hp_odd := odd_of_prime_gt_of_two_le hk hp hkp
  have hq_odd := odd_of_prime_gt_of_two_le hk hq hkq
  omega

/--
When `k ≥ 3` is odd (`k % 2 = 1`), `k + 1` and `k + 3` are even, so any two distinct primes `p ≠ q`
strictly greater than `k` satisfy `k + 4 ≤ max p q`.
-/
theorem add_four_le_max_of_three_le_of_odd_of_prime_gt_of_prime_gt {k p q : ℕ}
    (hk : 3 ≤ k) (hodd : k % 2 = 1) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hkp : k < p) (hkq : k < q) (hne : p ≠ q) :
    k + 4 ≤ max p q := by
  have hp_odd := odd_of_prime_gt_of_two_le (by omega) hp hkp
  have hq_odd := odd_of_prime_gt_of_two_le (by omega) hq hkq
  omega

/-! ### General Two-Divisor Collision Dichotomy for Coprime Divisors -/

/--
If `1 ≤ d₁ ≤ k`, `1 ≤ d₂ ≤ k`, and `p > k` is prime, then `d₁ * d₂` is coprime to `p`.
-/
theorem coprime_mul_of_prime_gt_of_pos_le {d₁ d₂ k p : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₁k : d₁ ≤ k) (hd₂ : 1 ≤ d₂) (hd₂k : d₂ ≤ k)
    (hp : Nat.Prime p) (hkp : k < p) :
    Nat.Coprime (d₁ * d₂) p :=
  (coprime_of_prime_gt_of_pos_le hd₁ hd₁k hp hkp).mul_left
    (coprime_of_prime_gt_of_pos_le hd₂ hd₂k hp hkp)

/--
If `1 ≤ d₁, d₂ ≤ k` are coprime and divide `x`, and `p > k` is a prime dividing `x`, then
`d₁ * d₂ * p ∣ x`.
-/
theorem mul_mul_dvd_of_coprime_of_dvd_of_dvd_of_prime_gt {d₁ d₂ k p x : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₁k : d₁ ≤ k) (hd₂ : 1 ≤ d₂) (hd₂k : d₂ ≤ k)
    (hcop : Nat.Coprime d₁ d₂) (hp : Nat.Prime p) (hkp : k < p)
    (hd₁x : d₁ ∣ x) (hd₂x : d₂ ∣ x) (hpx : p ∣ x) :
    d₁ * d₂ * p ∣ x := by
  have hd12 : d₁ * d₂ ∣ x := hcop.mul_dvd_of_dvd_of_dvd hd₁x hd₂x
  exact (coprime_mul_of_prime_gt_of_pos_le hd₁ hd₁k hd₂ hd₂k hp hkp).mul_dvd_of_dvd_of_dvd hd12 hpx

/--
Universal two-divisor collision dichotomy for any coprime divisors `1 ≤ d₁, d₂ ≤ k`:
in any valid run `IsLargePrimeRun m k`, either the remainder shifts `d₁ - m % d₁` and `d₂ - m % d₂`
collide (forcing `d₁ * d₂ * p ∣ m + (d₂ - m % d₂)` and `d₁ * d₂ * (k + 1) ≤ m + (d₂ - m % d₂)`),
or the shifts are distinct and witness two distinct primes `p₁ ≠ p₂ > k`.
-/
theorem coprime_two_divisor_collision_dichotomy {m k d₁ d₂ : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₁k : d₁ ≤ k) (hd₂ : 1 ≤ d₂) (hd₂k : d₂ ≤ k)
    (hcop : Nat.Coprime d₁ d₂) (hrun : IsLargePrimeRun m k) :
    (d₁ - m % d₁ = d₂ - m % d₂ ∧
      ∃ p : ℕ, Nat.Prime p ∧ k < p ∧
        d₁ * d₂ * p ∣ m + (d₂ - m % d₂) ∧
        d₁ * d₂ * (k + 1) ≤ m + (d₂ - m % d₂)) ∨
    (d₁ - m % d₁ ≠ d₂ - m % d₂ ∧
      ∃ p₁ p₂ : ℕ, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ k < p₁ ∧ k < p₂ ∧ p₁ ≠ p₂ ∧
        d₁ * p₁ ∣ m + (d₁ - m % d₁) ∧ d₂ * p₂ ∣ m + (d₂ - m % d₂)) := by
  rcases exists_prime_gt_mul_dvd_shift_of_isLargePrimeRun hd₁ hd₁k hrun with ⟨p₁, hp₁, hkp₁, hmul₁⟩
  rcases exists_prime_gt_mul_dvd_shift_of_isLargePrimeRun hd₂ hd₂k hrun with ⟨p₂, hp₂, hkp₂, hmul₂⟩
  have hmod₁ : m % d₁ < d₁ := Nat.mod_lt m (by omega)
  have hmod₂ : m % d₂ < d₂ := Nat.mod_lt m (by omega)
  by_cases hcol : d₁ - m % d₁ = d₂ - m % d₂
  · left
    have hd₁_shift : d₁ ∣ m + (d₂ - m % d₂) := by
      rw [← hcol]
      exact (dvd_add_sub_mod_of_pos hd₁).2
    have hd₂_shift : d₂ ∣ m + (d₂ - m % d₂) := (dvd_add_sub_mod_of_pos hd₂).2
    have hp₂_shift : p₂ ∣ m + (d₂ - m % d₂) := dvd_of_mul_left_dvd hmul₂
    have h3dvd := mul_mul_dvd_of_coprime_of_dvd_of_dvd_of_prime_gt
      hd₁ hd₁k hd₂ hd₂k hcop hp₂ hkp₂ hd₁_shift hd₂_shift hp₂_shift
    have hpos : 0 < m + (d₂ - m % d₂) := by omega
    have hle : d₁ * d₂ * p₂ ≤ m + (d₂ - m % d₂) := Nat.le_of_dvd hpos h3dvd
    have hkle : d₁ * d₂ * (k + 1) ≤ d₁ * d₂ * p₂ :=
      Nat.mul_le_mul_left (d₁ * d₂) (by omega)
    exact ⟨hcol, p₂, hp₂, hkp₂, h3dvd, le_trans hkle hle⟩
  · right
    refine ⟨hcol, p₁, p₂, hp₁, hp₂, hkp₁, hkp₂, ?_, hmul₁, hmul₂⟩
    intro heq
    have hi₁ : d₁ - m % d₁ ∈ Set.Icc 1 k := ⟨by omega, by omega⟩
    have hi₂ : d₂ - m % d₂ ∈ Set.Icc 1 k := ⟨by omega, by omega⟩
    have hp₁_dvd : p₁ ∣ m + (d₁ - m % d₁) := dvd_of_mul_left_dvd hmul₁
    have hp₂_dvd : p₁ ∣ m + (d₂ - m % d₂) := by
      rw [heq]
      exact dvd_of_mul_left_dvd hmul₂
    exact hcol (eq_of_large_prime_dvd_run hi₁ hi₂ hkp₁ hp₁_dvd hp₂_dvd)

/-! ### Consecutive-Divisor Collision Dichotomy (`d₁ = k, d₂ = k - 1`) -/

/--
Consecutive integers `k` and `k - 1` (`1 ≤ k`) are coprime.
-/
theorem coprime_self_pred {k : ℕ} (hk : 1 ≤ k) : Nat.Coprime k (k - 1) :=
  (Nat.coprime_self_sub_right hk).mpr (Nat.coprime_one_right k)

/--
When `k ≥ 2` is odd (`k % 2 = 1`), `k` and `k - 2` are coprime.
-/
theorem coprime_self_sub_two_of_odd {k : ℕ} (hk : 2 ≤ k) (hodd : k % 2 = 1) :
    Nat.Coprime k (k - 2) := by
  rw [Nat.coprime_self_sub_right hk]
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm

/--
Two-divisor collision dichotomy for consecutive divisors `k` and `k - 1` (`2 ≤ k`):
either the shifts collide and `k * (k - 1) * (k + 1) ≤ m + (k - 1) ≤ m + k`, or the shifts are
distinct and the run contains two distinct primes `p_k ≠ p_{k-1} > k` with `k + 3 ≤ max p_k p_{k-1}`.
-/
theorem consecutive_divisor_collision_dichotomy {m k : ℕ}
    (hk : 2 ≤ k) (hrun : IsLargePrimeRun m k) :
    (k - m % k = (k - 1) - m % (k - 1) ∧
      ∃ p : ℕ, Nat.Prime p ∧ k < p ∧
        k * (k - 1) * p ∣ m + ((k - 1) - m % (k - 1)) ∧
        k * (k - 1) * (k + 1) ≤ m + (k - 1) ∧
        k * (k - 1) * (k + 1) ≤ m + k) ∨
    (k - m % k ≠ (k - 1) - m % (k - 1) ∧
      ∃ p_k p_km1 : ℕ, Nat.Prime p_k ∧ Nat.Prime p_km1 ∧
        k < p_k ∧ k < p_km1 ∧ p_k ≠ p_km1 ∧ k + 3 ≤ max p_k p_km1 ∧
        k * p_k ∣ m + (k - m % k) ∧
        (k - 1) * p_km1 ∣ m + ((k - 1) - m % (k - 1))) := by
  have hd₁ : 1 ≤ k := by omega
  have hd₂ : 1 ≤ k - 1 := by omega
  have hd₂k : k - 1 ≤ k := by omega
  have hcop : Nat.Coprime k (k - 1) := coprime_self_pred hd₁
  rcases coprime_two_divisor_collision_dichotomy hd₁ le_rfl hd₂ hd₂k hcop hrun with
    ⟨hcol, p, hp, hkp, h3dvd, h3le⟩ | ⟨hne, p₁, p₂, hp₁, hp₂, hkp₁, hkp₂, hpne, hmul₁, hmul₂⟩
  · left
    exact ⟨hcol, p, hp, hkp, h3dvd, by omega, by omega⟩
  · right
    have hmax := add_three_le_max_of_two_le_of_prime_gt_of_prime_gt hk hp₁ hp₂ hkp₁ hkp₂ hpne
    exact ⟨hne, p₁, p₂, hp₁, hp₂, hkp₁, hkp₂, hpne, hmax, hmul₁, hmul₂⟩

/--
Remainder-inequality form of the consecutive-divisor collision dichotomy (`2 ≤ k`):
either `k * (k - 1) * (k + 1) ≤ m + (k - 1) ≤ m + k`, or there exist two distinct primes
`p_k ≠ p_{k-1} > k` with `k + 3 ≤ max p_k p_{k-1}` satisfying `k * (p_k - 1) + m % k ≤ m` and
`(k - 1) * (p_{k-1} - 1) + m % (k - 1) ≤ m`.
-/
theorem consecutive_divisor_collision_or_distinct_large_primes {m k : ℕ}
    (hk : 2 ≤ k) (hrun : IsLargePrimeRun m k) :
    (k * (k - 1) * (k + 1) ≤ m + (k - 1) ∧ k * (k - 1) * (k + 1) ≤ m + k) ∨
      ∃ p_k p_km1 : ℕ, Nat.Prime p_k ∧ Nat.Prime p_km1 ∧
        k < p_k ∧ k < p_km1 ∧ p_k ≠ p_km1 ∧ k + 3 ≤ max p_k p_km1 ∧
        k * (p_k - 1) + m % k ≤ m ∧
        (k - 1) * (p_km1 - 1) + m % (k - 1) ≤ m := by
  rcases consecutive_divisor_collision_dichotomy hk hrun with
    ⟨_, _, _, _, _, hle_km1, hle_k⟩ | ⟨_, p₁, p₂, hp₁, hp₂, hkp₁, hkp₂, hpne, hmax, hmul₁, hmul₂⟩
  · exact Or.inl ⟨hle_km1, hle_k⟩
  · right
    have hmod₁ : m % k < k := Nat.mod_lt m (by omega)
    have hmod₂ : m % (k - 1) < k - 1 := Nat.mod_lt m (by omega)
    have hle₁ : k * p₁ ≤ m + (k - m % k) := Nat.le_of_dvd (by omega) hmul₁
    have hle₂ : (k - 1) * p₂ ≤ m + ((k - 1) - m % (k - 1)) := Nat.le_of_dvd (by omega) hmul₂
    have h1 : k * (p₁ - 1) + k ≤ m + (k - m % k) := by
      calc k * (p₁ - 1) + k = k * (p₁ - 1 + 1) := by ring
      _ = k * p₁ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ p₁)]
      _ ≤ m + (k - m % k) := hle₁
    have h2 : (k - 1) * (p₂ - 1) + (k - 1) ≤ m + ((k - 1) - m % (k - 1)) := by
      calc (k - 1) * (p₂ - 1) + (k - 1) = (k - 1) * (p₂ - 1 + 1) := by ring
      _ = (k - 1) * p₂ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ p₂)]
      _ ≤ m + ((k - 1) - m % (k - 1)) := hle₂
    exact ⟨p₁, p₂, hp₁, hp₂, hkp₁, hkp₂, hpne, hmax, by omega, by omega⟩

/-! ### Unconditional Quadratic Upgrade `(k - 1) * (k + 2) ≤ m` -/

/--
Unconditional two-divisor quadratic lower bound: every valid run `IsLargePrimeRun m k` satisfies
`(k - 1) * (k + 2) ≤ m`. This is sharp with equality at `k = 2` (`m = 4`) and `k = 4` (`m = 18`).
-/
theorem pred_mul_add_two_le_witness_of_isLargePrimeRun {m k : ℕ}
    (hrun : IsLargePrimeRun m k) :
    (k - 1) * (k + 2) ≤ m := by
  rcases lt_or_ge k 2 with hk_lt | hk_ge
  · have hk1 : k - 1 = 0 := by omega
    simp [hk1]
  · rcases consecutive_divisor_collision_or_distinct_large_primes hk_ge hrun with
      ⟨hle_km1, _⟩ | ⟨p₁, p₂, _, _, _, _, _, hmax, h₁, h₂⟩
    · nlinarith
    · have hor : k + 2 ≤ p₁ - 1 ∨ k + 2 ≤ p₂ - 1 := by omega
      rcases hor with hp₁_ge | hp₂_ge
      · have hmul₁ : (k - 1) * (k + 2) ≤ k * (p₁ - 1) :=
          Nat.mul_le_mul (by omega) hp₁_ge
        omega
      · have hmul₂ : (k - 1) * (k + 2) ≤ (k - 1) * (p₂ - 1) :=
          Nat.mul_le_mul_left (k - 1) hp₂_ge
        omega

/--
For all `k ≥ 2`, any valid run `IsLargePrimeRun m k` satisfies `k ^ 2 + k - 2 ≤ m`, strictly
strengthening `k ^ 2 ≤ m` (`sq_le_witness_of_isLargePrimeRun`) for all `k ≥ 3`.
-/
theorem sq_add_sub_two_le_witness_of_isLargePrimeRun {m k : ℕ}
    (hk : 2 ≤ k) (hrun : IsLargePrimeRun m k) :
    k ^ 2 + k - 2 ≤ m := by
  have h := pred_mul_add_two_le_witness_of_isLargePrimeRun hrun
  have hident : k ^ 2 + k - 2 = (k - 1) * (k + 2) := by
    rcases Nat.exists_eq_add_of_le hk with ⟨c, rfl⟩
    have h1 : 2 + c - 1 = c + 1 := by omega
    have h2 : (2 + c) ^ 2 + (2 + c) - 2 = (c + 1) * (2 + c + 2) := by
      have hexp : (2 + c) ^ 2 + (2 + c) = (c + 1) * (2 + c + 2) + 2 := by ring
      omega
    rw [h1, h2]
  omega

/--
If `Erdos962Prop n k₀` holds, then `(k₀ - 1) * (k₀ + 2) ≤ n`.
-/
theorem erdos962Prop_imp_pred_mul_add_two_le {n k₀ : ℕ}
    (h : Erdos962Prop n k₀) : (k₀ - 1) * (k₀ + 2) ≤ n := by
  rcases (erdos962Prop_iff_exists_isLargePrimeRun n k₀).mp h with ⟨m, hmn, hrun⟩
  exact le_trans (pred_mul_add_two_le_witness_of_isLargePrimeRun hrun) hmn

/--
Obstruction form: if `n < (k₀ - 1) * (k₀ + 2)`, then `¬ Erdos962Prop n k₀`.
-/
theorem not_erdos962Prop_of_lt_pred_mul_add_two {n k₀ : ℕ}
    (h : n < (k₀ - 1) * (k₀ + 2)) : ¬ Erdos962Prop n k₀ := by
  intro hk₀
  have hle := erdos962Prop_imp_pred_mul_add_two_le hk₀
  omega

/--
Unconditional two-divisor bound on `k(n)`: for every `n : ℕ`, `(k n - 1) * (k n + 2) ≤ n`.
-/
theorem k_pred_mul_add_two_le_self (n : ℕ) : (k n - 1) * (k n + 2) ≤ n :=
  erdos962Prop_imp_pred_mul_add_two_le (erdos962Prop_k n)

/--
Whenever `2 ≤ k(n)` (i.e. `n ≥ 4`), `(k n) ^ 2 + k n - 2 ≤ n`.
-/
theorem k_sq_add_k_sub_two_le_self {n : ℕ} (hk : 2 ≤ k n) :
    (k n) ^ 2 + k n - 2 ≤ n := by
  rcases (erdos962Prop_iff_exists_isLargePrimeRun n (k n)).mp (erdos962Prop_k n) with ⟨m, hmn, hrun⟩
  exact le_trans (sq_add_sub_two_le_witness_of_isLargePrimeRun hk hrun) hmn

/-! ### Second-Prime Lower Bounds and Odd-`k` Refinement `(k - 1) * (k + 3) ≤ m` -/

/--
Universal second-prime lower bound: if `2 ≤ k`, `1 ≤ B₂`, every prime `p > k` satisfies `B₁ ≤ p`,
and every pair of distinct primes `p ≠ q > k` satisfies `B₂ ≤ max p q`, then any valid run
`IsLargePrimeRun m k` satisfies `min ((k - 1) * (B₂ - 1)) (k * (k - 1) * B₁ - (k - 1)) ≤ m`.
-/
theorem pred_mul_second_prime_bound_of_isLargePrimeRun {m k B₁ B₂ : ℕ}
    (hk : 2 ≤ k) (hB₂ : 1 ≤ B₂)
    (hgap₁ : ∀ p : ℕ, Nat.Prime p → k < p → B₁ ≤ p)
    (hgap₂ : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → k < p → k < q → p ≠ q → B₂ ≤ max p q)
    (hrun : IsLargePrimeRun m k) :
    min ((k - 1) * (B₂ - 1)) (k * (k - 1) * B₁ - (k - 1)) ≤ m := by
  have hd₁ : 1 ≤ k := by omega
  have hd₂ : 1 ≤ k - 1 := by omega
  have hd₂k : k - 1 ≤ k := by omega
  have hcop : Nat.Coprime k (k - 1) := coprime_self_pred hd₁
  rcases coprime_two_divisor_collision_dichotomy hd₁ le_rfl hd₂ hd₂k hcop hrun with
    ⟨_, p, hp, hkp, h3dvd, _⟩ | ⟨_, p₁, p₂, hp₁, hp₂, hkp₁, hkp₂, hpne, hmul₁, hmul₂⟩
  · have hBp : B₁ ≤ p := hgap₁ p hp hkp
    have hmod₂ : m % (k - 1) < k - 1 := Nat.mod_lt m (by omega)
    have hle : k * (k - 1) * p ≤ m + ((k - 1) - m % (k - 1)) :=
      Nat.le_of_dvd (by omega) h3dvd
    have hBle : k * (k - 1) * B₁ ≤ k * (k - 1) * p :=
      Nat.mul_le_mul_left (k * (k - 1)) hBp
    have hmin : min ((k - 1) * (B₂ - 1)) (k * (k - 1) * B₁ - (k - 1)) ≤
        k * (k - 1) * B₁ - (k - 1) := Nat.min_le_right _ _
    omega
  · have hmax : B₂ ≤ max p₁ p₂ := hgap₂ p₁ p₂ hp₁ hp₂ hkp₁ hkp₂ hpne
    have hmod₁ : m % k < k := Nat.mod_lt m (by omega)
    have hmod₂ : m % (k - 1) < k - 1 := Nat.mod_lt m (by omega)
    have hle₁ : k * p₁ ≤ m + (k - m % k) := Nat.le_of_dvd (by omega) hmul₁
    have hle₂ : (k - 1) * p₂ ≤ m + ((k - 1) - m % (k - 1)) := Nat.le_of_dvd (by omega) hmul₂
    have h1 : k * (p₁ - 1) + k ≤ m + (k - m % k) := by
      calc k * (p₁ - 1) + k = k * (p₁ - 1 + 1) := by ring
      _ = k * p₁ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ p₁)]
      _ ≤ m + (k - m % k) := hle₁
    have h2 : (k - 1) * (p₂ - 1) + (k - 1) ≤ m + ((k - 1) - m % (k - 1)) := by
      calc (k - 1) * (p₂ - 1) + (k - 1) = (k - 1) * (p₂ - 1 + 1) := by ring
      _ = (k - 1) * p₂ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ p₂)]
      _ ≤ m + ((k - 1) - m % (k - 1)) := hle₂
    have hmin : min ((k - 1) * (B₂ - 1)) (k * (k - 1) * B₁ - (k - 1)) ≤
        (k - 1) * (B₂ - 1) := Nat.min_le_left _ _
    have hor : B₂ - 1 ≤ p₁ - 1 ∨ B₂ - 1 ≤ p₂ - 1 := by omega
    rcases hor with hp₁_ge | hp₂_ge
    · have hmul_ge : (k - 1) * (B₂ - 1) ≤ k * (p₁ - 1) :=
        Nat.mul_le_mul (by omega) hp₁_ge
      omega
    · have hmul_ge : (k - 1) * (B₂ - 1) ≤ (k - 1) * (p₂ - 1) :=
        Nat.mul_le_mul_left (k - 1) hp₂_ge
      omega

/--
For every odd `k ≥ 3` (`k % 2 = 1`), any valid run `IsLargePrimeRun m k` satisfies
`(k - 1) * (k + 3) ≤ m`. This is sharp with equality at `k = 3` (`m = 12`).
-/
theorem pred_mul_add_three_le_witness_of_odd {m k : ℕ}
    (hk : 3 ≤ k) (hodd : k % 2 = 1) (hrun : IsLargePrimeRun m k) :
    (k - 1) * (k + 3) ≤ m := by
  rcases consecutive_divisor_collision_or_distinct_large_primes (by omega) hrun with
    ⟨hle_km1, _⟩ | ⟨p₁, p₂, hp₁, hp₂, hkp₁, hkp₂, hpne, _, h₁, h₂⟩
  · nlinarith
  · have hmax4 := add_four_le_max_of_three_le_of_odd_of_prime_gt_of_prime_gt
      hk hodd hp₁ hp₂ hkp₁ hkp₂ hpne
    have hor : k + 3 ≤ p₁ - 1 ∨ k + 3 ≤ p₂ - 1 := by omega
    rcases hor with hp₁_ge | hp₂_ge
    · have hmul₁ : (k - 1) * (k + 3) ≤ k * (p₁ - 1) :=
        Nat.mul_le_mul (by omega) hp₁_ge
      omega
    · have hmul₂ : (k - 1) * (k + 3) ≤ (k - 1) * (p₂ - 1) :=
        Nat.mul_le_mul_left (k - 1) hp₂_ge
      omega

/--
Whenever `k(n) ≥ 3` is odd, `(k n - 1) * (k n + 3) ≤ n`.
-/
theorem k_pred_mul_add_three_le_self_of_odd {n : ℕ}
    (hk : 3 ≤ k n) (hodd : k n % 2 = 1) :
    (k n - 1) * (k n + 3) ≤ n := by
  rcases (erdos962Prop_iff_exists_isLargePrimeRun n (k n)).mp (erdos962Prop_k n) with ⟨m, hmn, hrun⟩
  exact le_trans (pred_mul_add_three_le_witness_of_odd hk hodd hrun) hmn

/-! ### Exact Evaluations `k(n) = 4` on `[18, 53]` and `k(n) = 5` on `[54, 63]` -/

/--
Since `P₁(5) = 7` and `P₂(5) = 11`, `pred_mul_second_prime_bound_of_isLargePrimeRun` implies that
every valid run `IsLargePrimeRun m 5` satisfies `40 ≤ m`.
-/
theorem forty_le_witness_of_isLargePrimeRun_five {m : ℕ}
    (hrun : IsLargePrimeRun m 5) : 40 ≤ m := by
  have hgap₁ : ∀ p : ℕ, Nat.Prime p → 5 < p → 7 ≤ p := by
    intro p hp h5p
    by_contra hlt
    have heq : p = 6 := by omega
    rw [heq] at hp
    exact (by decide : ¬ Nat.Prime 6) hp
  have hgap₂ : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 5 < p → 5 < q → p ≠ q → 11 ≤ max p q := by
    intro p q hp hq h5p h5q hpne
    by_contra hlt
    have hp10 : p ≤ 10 := by omega
    have hq10 : q ≤ 10 := by omega
    have hp7 : p = 7 := by
      interval_cases p <;> first | rfl | exfalso; revert hp; decide +kernel
    have hq7 : q = 7 := by
      interval_cases q <;> first | rfl | exfalso; revert hq; decide +kernel
    omega
  have h := pred_mul_second_prime_bound_of_isLargePrimeRun
    (by decide : 2 ≤ 5) (by decide : 1 ≤ 11) hgap₁ hgap₂ hrun
  omega

/--
Every `m ≤ 53` fails `IsLargePrimeRun m 5`: for `m < 40` this follows from
`forty_le_witness_of_isLargePrimeRun_five`, while for `m ∈ [40, 53]` the window `[m + 1, m + 5]`
contains one of the three `5`-smooth blockers `45 ∣ (5!)^2`, `50 ∣ (5!)^2`, or `54 ∣ (5!)^3`.
-/
theorem not_erdos962Prop_fifty_three_five : ¬ Erdos962Prop 53 5 := by
  rintro ⟨m, hm53, hrun⟩
  have hm40 : 40 ≤ m := forty_le_witness_of_isLargePrimeRun_five hrun
  rcases le_or_gt m 44 with hm44 | hm45
  · have h45_mem : 45 ∈ Set.Icc (m + 1) (m + 5) := ⟨by omega, by omega⟩
    have h45_smooth : ¬ HasLargePrimeFactor 5 45 :=
      not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 2) (by decide)
    exact not_isLargePrimeRun_of_smooth_mem_Icc h45_mem h45_smooth hrun
  · rcases le_or_gt m 49 with hm49 | hm50
    · have h50_mem : 50 ∈ Set.Icc (m + 1) (m + 5) := ⟨by omega, by omega⟩
      have h50_smooth : ¬ HasLargePrimeFactor 5 50 :=
        not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 2) (by decide)
      exact not_isLargePrimeRun_of_smooth_mem_Icc h50_mem h50_smooth hrun
    · have h54_mem : 54 ∈ Set.Icc (m + 1) (m + 5) := ⟨by omega, by omega⟩
      have h54_smooth : ¬ HasLargePrimeFactor 5 54 :=
        not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 3) (by decide)
      exact not_isLargePrimeRun_of_smooth_mem_Icc h54_mem h54_smooth hrun

/--
For all `n ∈ [18, 53]`, `k(n) = 4`.
-/
theorem k_eq_four_of_Icc {n : ℕ} (hn : n ∈ Set.Icc 18 53) : k n = 4 := by
  rcases hn with ⟨hn18, hn53⟩
  have hge : 4 ≤ k n := four_le_k_of_eighteen_le hn18
  have hle53 : k n ≤ k 53 := k_mono hn53
  have hk53_lt : ¬ (5 ≤ k 53) := by
    intro h5
    exact not_erdos962Prop_fifty_three_five ((erdos962Prop_iff_le_k 53 5).mpr h5)
  omega

@[simp] theorem k_eighteen : k 18 = 4 := k_eq_four_of_Icc ⟨by decide, by decide⟩

/--
At `n = 54`, the run `55 = 5 · 11, 56 = 7 · 8, 57 = 3 · 19, 58 = 2 · 29, 59 = 59` witnesses
`Erdos962Prop 54 5`.
-/
theorem erdos962Prop_fifty_four_five : Erdos962Prop 54 5 := by
  refine ⟨54, le_rfl, ?_⟩
  intro i hi
  rcases hi with ⟨hi1, hi5⟩
  interval_cases i
  · exact ⟨11, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩
  · exact ⟨19, by decide, by decide, by decide⟩
  · exact ⟨29, by decide, by decide, by decide⟩
  · exact ⟨59, by decide, by decide, by decide⟩

theorem five_le_k_of_fifty_four_le {n : ℕ} (hn : 54 ≤ n) : 5 ≤ k n :=
  le_k_of_erdos962Prop (erdos962Prop_mono_left hn erdos962Prop_fifty_four_five)

/--
Since `P₁(6) = 7` and `P₂(6) = 11`, `pred_mul_second_prime_bound_of_isLargePrimeRun` implies that
every valid run `IsLargePrimeRun m 6` satisfies `50 ≤ m`.
-/
theorem fifty_le_witness_of_isLargePrimeRun_six {m : ℕ}
    (hrun : IsLargePrimeRun m 6) : 50 ≤ m := by
  have hgap₁ : ∀ p : ℕ, Nat.Prime p → 6 < p → 7 ≤ p := by
    intro p _ h6p
    omega
  have hgap₂ : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → 6 < p → 6 < q → p ≠ q → 11 ≤ max p q := by
    intro p q hp hq h6p h6q hpne
    by_contra hlt
    have hp10 : p ≤ 10 := by omega
    have hq10 : q ≤ 10 := by omega
    have hp7 : p = 7 := by
      interval_cases p <;> first | rfl | exfalso; revert hp; decide +kernel
    have hq7 : q = 7 := by
      interval_cases q <;> first | rfl | exfalso; revert hq; decide +kernel
    omega
  have h := pred_mul_second_prime_bound_of_isLargePrimeRun
    (by decide : 2 ≤ 6) (by decide : 1 ≤ 11) hgap₁ hgap₂ hrun
  omega

/--
Every `m ≤ 63` fails `IsLargePrimeRun m 6`: for `m < 50` this follows from
`fifty_le_witness_of_isLargePrimeRun_six`, while for `m ∈ [50, 63]` the window `[m + 1, m + 6]`
contains one of the three `6`-smooth blockers `54 ∣ (6!)^3`, `60 ∣ 6!`, or `64 ∣ (6!)^2`.
-/
theorem not_erdos962Prop_sixty_three_six : ¬ Erdos962Prop 63 6 := by
  rintro ⟨m, hm63, hrun⟩
  have hm50 : 50 ≤ m := fifty_le_witness_of_isLargePrimeRun_six hrun
  rcases le_or_gt m 53 with hm53 | hm54
  · have h54_mem : 54 ∈ Set.Icc (m + 1) (m + 6) := ⟨by omega, by omega⟩
    have h54_smooth : ¬ HasLargePrimeFactor 6 54 :=
      not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 3) (by decide)
    exact not_isLargePrimeRun_of_smooth_mem_Icc h54_mem h54_smooth hrun
  · rcases le_or_gt m 59 with hm59 | hm60
    · have h60_mem : 60 ∈ Set.Icc (m + 1) (m + 6) := ⟨by omega, by omega⟩
      have h60_smooth : ¬ HasLargePrimeFactor 6 60 :=
        not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 1) (by decide)
      exact not_isLargePrimeRun_of_smooth_mem_Icc h60_mem h60_smooth hrun
    · have h64_mem : 64 ∈ Set.Icc (m + 1) (m + 6) := ⟨by omega, by omega⟩
      have h64_smooth : ¬ HasLargePrimeFactor 6 64 :=
        not_hasLargePrimeFactor_of_dvd_factorial_pow (r := 2) (by decide)
      exact not_isLargePrimeRun_of_smooth_mem_Icc h64_mem h64_smooth hrun

/--
For all `n ∈ [54, 63]`, `k(n) = 5`.
-/
theorem k_eq_five_of_Icc {n : ℕ} (hn : n ∈ Set.Icc 54 63) : k n = 5 := by
  rcases hn with ⟨hn54, hn63⟩
  have hge : 5 ≤ k n := five_le_k_of_fifty_four_le hn54
  have hle63 : k n ≤ k 63 := k_mono hn63
  have hk63_lt : ¬ (6 ≤ k 63) := by
    intro h6
    exact not_erdos962Prop_sixty_three_six ((erdos962Prop_iff_le_k 63 6).mpr h6)
  omega

@[simp] theorem k_fifty_four : k 54 = 5 := k_eq_five_of_Icc ⟨by decide, by decide⟩

/--
At `n = 64`, the run `65 = 5 · 13, 66 = 6 · 11, 67 = 67, 68 = 4 · 17, 69 = 3 · 23, 70 = 7 · 10`
witnesses `Erdos962Prop 64 6`.
-/
theorem erdos962Prop_sixty_four_six : Erdos962Prop 64 6 := by
  refine ⟨64, le_rfl, ?_⟩
  intro i hi
  rcases hi with ⟨hi1, hi6⟩
  interval_cases i
  · exact ⟨13, by decide, by decide, by decide⟩
  · exact ⟨11, by decide, by decide, by decide⟩
  · exact ⟨67, by decide, by decide, by decide⟩
  · exact ⟨17, by decide, by decide, by decide⟩
  · exact ⟨23, by decide, by decide, by decide⟩
  · exact ⟨7, by decide, by decide, by decide⟩

theorem six_le_k_of_sixty_four_le {n : ℕ} (hn : 64 ≤ n) : 6 ≤ k n :=
  le_k_of_erdos962Prop (erdos962Prop_mono_left hn erdos962Prop_sixty_four_six)

end Erdos962
