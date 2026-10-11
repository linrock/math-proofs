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
noncomputable section
open scoped BigOperators Pointwise
namespace Erdos1180
open Filter

/--
`Represents ε p a s` says that the multiset `s` of denominators `n` with `1 ≤ n ≤ p^ε` and
`n` coprime to `p` has `∑ n⁻¹ = a` in `ZMod p`.
-/
def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a

/--
`AdmissibleDenom ε p n` isolates the per-denominator condition `1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p`
appearing in `Represents ε p a s`.
-/
def AdmissibleDenom (ε : ℝ) (p n : ℕ) : Prop :=
  1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p

/--
Set of uniform multiset-cardinality bounds valid across all primes `p` and all residues `a : ZMod p`.
-/
def UniformBoundSet (ε : ℝ) : Set ℕ :=
  {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

/--
`C ε` is the least `C` such that, for all primes `p`, every residue modulo `p` is the sum of at
most `C` elements of `{n⁻¹ : 1 ≤ n ≤ p^ε}` (or `0` if no such `C` exists).
-/
noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

/--
Proposition corresponding to the open optimality question `erdos_1180.variants.optimal`:
for every `δ > 0`, eventually as `ε → 0⁺`, `(C ε : ℝ) ≤ ε⁻¹ ^ (1 + δ)`.
-/
def Erdos1180OptimalConjecture : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), (C ε : ℝ) ≤ ε⁻¹ ^ (1 + δ)

/--
Zero representation law: the empty multiset `0` represents `0 : ZMod p` for every `ε` and `p`.
-/
theorem represents_zero (ε : ℝ) (p : ℕ) : Represents ε p 0 0 := by
  refine ⟨?_, ?_⟩
  · intro n hn
    simp at hn
  · simp

/--
For any `p ≥ 1` and `ε ≥ 0`, `1` is an admissible denominator since `1 ≤ p^ε` and `Nat.Coprime 1 p`.
-/
theorem admissibleDenom_one {ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hε : 0 ≤ ε) :
    AdmissibleDenom ε p 1 := by
  refine ⟨le_rfl, ?_, Nat.coprime_one_left p⟩
  rw [Nat.cast_one]
  exact Real.one_le_rpow (by exact_mod_cast hp) hε

/--
Any admissible denominator `n` as a singleton multiset `{n}` represents `(n : ZMod p)⁻¹`.
-/
theorem represents_singleton {ε : ℝ} {p n : ℕ} (h : AdmissibleDenom ε p n) :
    Represents ε p (n : ZMod p)⁻¹ {n} := by
  refine ⟨?_, by simp⟩
  intro m hm
  rw [Multiset.mem_singleton] at hm
  subst hm
  exact h

/--
Unit replication representation: for any `k : ℕ`, `Multiset.replicate k 1` has cardinality `k`
and represents `(k : ZMod p)` whenever `1 ≤ p` and `0 ≤ ε`.
-/
theorem represents_replicate_one {ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hε : 0 ≤ ε) (k : ℕ) :
    Represents ε p (k : ZMod p) (Multiset.replicate k 1) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    have hn1 : n = 1 := Multiset.eq_of_mem_replicate hn
    subst hn1
    exact admissibleDenom_one hp hε
  · simp

/--
Every residue `a : ZMod p` for a prime `p` (or any `p ≥ 1` with `[NeZero p]`) is represented by
`Multiset.replicate a.val 1` of cardinality `a.val ≤ p - 1` whenever `0 ≤ ε`.
-/
theorem represents_val_replicate_one {ε : ℝ} {p : ℕ} [NeZero p] (hp : 1 ≤ p) (hε : 0 ≤ ε)
    (a : ZMod p) :
    Represents ε p a (Multiset.replicate a.val 1) ∧
      (Multiset.replicate a.val 1).card ≤ p - 1 := by
  refine ⟨?_, ?_⟩
  · simpa [ZMod.natCast_zmod_val] using represents_replicate_one (p := p) hp hε a.val
  · rw [Multiset.card_replicate]
    have hlt : a.val < p := ZMod.val_lt a
    omega

/--
Additive closure under multiset sum: if `s₁` represents `a` and `s₂` represents `b`, then
`s₁ + s₂` represents `a + b` with `(s₁ + s₂).card = s₁.card + s₂.card`.
-/
theorem represents_add {ε : ℝ} {p : ℕ} {a b : ZMod p} {s₁ s₂ : Multiset ℕ}
    (h₁ : Represents ε p a s₁) (h₂ : Represents ε p b s₂) :
    Represents ε p (a + b) (s₁ + s₂) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [Multiset.mem_add] at hn
    rcases hn with hn₁ | hn₂
    · exact h₁.1 n hn₁
    · exact h₂.1 n hn₂
  · rw [Multiset.map_add, Multiset.sum_add, h₁.2, h₂.2]

/--
Monotonicity of `AdmissibleDenom` in the exponent `ε` for `p ≥ 1`.
-/
theorem admissibleDenom_mono_eps {ε₁ ε₂ : ℝ} {p n : ℕ} (hε : ε₁ ≤ ε₂) (hp : 1 ≤ p)
    (h : AdmissibleDenom ε₁ p n) : AdmissibleDenom ε₂ p n := by
  refine ⟨h.1, ?_, h.2.2⟩
  exact h.2.1.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) hε)

theorem C_mem_uniformBoundSet {ε : ℝ} (hne : (UniformBoundSet ε).Nonempty) :
    C ε ∈ UniformBoundSet ε :=
  Nat.sInf_mem hne

/--
If `(p : ℝ) ^ ε < 2`, then any admissible denominator `n` satisfies `1 ≤ n` and `(n : ℝ) < 2`,
forcing `n = 1`.
-/
theorem admissibleDenom_eq_one_of_rpow_lt_two {ε : ℝ} {p n : ℕ}
    (hpow : (p : ℝ) ^ ε < 2) (hadm : AdmissibleDenom ε p n) : n = 1 := by
  have hlt : (n : ℝ) < (2 : ℕ) := by
    simpa using lt_of_le_of_lt hadm.2.1 hpow
  have hn2 : n < 2 := Nat.cast_lt.mp hlt
  have hn1 : 1 ≤ n := hadm.1
  omega

/--
If `(p : ℝ) ^ ε < 2`, then every denominator `n` in a representing multiset `s` equals `1`.
-/
theorem mem_eq_one_of_represents_of_rpow_lt_two {ε : ℝ} {p : ℕ} {a : ZMod p} {s : Multiset ℕ}
    (hpow : (p : ℝ) ^ ε < 2) (hrep : Represents ε p a s) :
    ∀ n ∈ s, n = 1 := by
  intro n hn
  exact admissibleDenom_eq_one_of_rpow_lt_two hpow (hrep.1 n hn)

/--
If `(p : ℝ) ^ ε < 2` and `Represents ε p a s`, then `s` is `Multiset.replicate s.card 1`.
-/
theorem eq_replicate_card_one_of_represents_of_rpow_lt_two {ε : ℝ} {p : ℕ} {a : ZMod p}
    {s : Multiset ℕ} (hpow : (p : ℝ) ^ ε < 2) (hrep : Represents ε p a s) :
    s = Multiset.replicate s.card 1 :=
  Multiset.eq_replicate_card.mpr (mem_eq_one_of_represents_of_rpow_lt_two hpow hrep)

/--
If `(p : ℝ) ^ ε < 2` and `Represents ε p a s`, then `(s.card : ZMod p) = a`.
-/
theorem natCast_card_eq_of_represents_of_rpow_lt_two {ε : ℝ} {p : ℕ} {a : ZMod p}
    {s : Multiset ℕ} (hpow : (p : ℝ) ^ ε < 2) (hrep : Represents ε p a s) :
    (s.card : ZMod p) = a := by
  have hs := eq_replicate_card_one_of_represents_of_rpow_lt_two hpow hrep
  have hsum := hrep.2
  rw [hs] at hsum
  simpa using hsum

/--
For any nonzero modulus `p` with `(p : ℝ) ^ ε < 2`, representing `a : ZMod p` requires at least
`a.val` summands.
-/
theorem val_le_card_of_represents_of_rpow_lt_two {ε : ℝ} {p : ℕ} [NeZero p] {a : ZMod p}
    {s : Multiset ℕ} (hpow : (p : ℝ) ^ ε < 2) (hrep : Represents ε p a s) :
    a.val ≤ s.card := by
  have hcast := natCast_card_eq_of_represents_of_rpow_lt_two hpow hrep
  rw [← hcast, ZMod.val_natCast]
  exact Nat.mod_le s.card p

/--
For any prime `p` with `(p : ℝ) ^ ε < 2`, representing `((p - 1 : ℕ) : ZMod p)` requires
`p - 1 ≤ s.card`.
-/
theorem pred_prime_le_card_of_represents_of_rpow_lt_two {ε : ℝ} {p : ℕ} (hp : p.Prime)
    {s : Multiset ℕ} (hpow : (p : ℝ) ^ ε < 2)
    (hrep : Represents ε p ((p - 1 : ℕ) : ZMod p) s) :
    p - 1 ≤ s.card := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hval := val_le_card_of_represents_of_rpow_lt_two hpow hrep
  have hlt : p - 1 < p := Nat.sub_lt hp.pos Nat.one_pos
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hval
  exact hval

/--
Every uniform bound `B ∈ UniformBoundSet ε` satisfies `p - 1 ≤ B` for every prime `p` with
`(p : ℝ) ^ ε < 2`.
-/
theorem pred_prime_le_of_mem_uniformBoundSet_of_rpow_lt_two {ε : ℝ} {p B : ℕ}
    (hp : p.Prime) (hpow : (p : ℝ) ^ ε < 2) (hB : B ∈ UniformBoundSet ε) :
    p - 1 ≤ B := by
  obtain ⟨s, hcard, hrep⟩ := hB p hp ((p - 1 : ℕ) : ZMod p)
  exact (pred_prime_le_card_of_represents_of_rpow_lt_two hp hpow hrep).trans hcard

/--
Unconditional lower bound `1 ≤ s.card` for representing `1 : ZMod 2` at any `ε : ℝ`.
-/
theorem one_le_card_of_represents_two_one {ε : ℝ} {s : Multiset ℕ}
    (hrep : Represents ε 2 1 s) : 1 ≤ s.card := by
  have hs0 : s ≠ 0 := by
    intro h0
    have hsum := hrep.2
    rw [h0] at hsum
    simp at hsum
  exact Multiset.card_pos.mpr hs0

/--
Every `B ∈ UniformBoundSet ε` satisfies `1 ≤ B` unconditionally for all `ε : ℝ`.
-/
theorem one_le_of_mem_uniformBoundSet {ε : ℝ} {B : ℕ} (hB : B ∈ UniformBoundSet ε) :
    1 ≤ B := by
  obtain ⟨s, hcard, hrep⟩ := hB 2 Nat.prime_two 1
  exact (one_le_card_of_represents_two_one hrep).trans hcard

/--
Bertrand's postulate dyadic lower bound: for any `m ≠ 0` and `0 ≤ ε` with `((2 * m : ℕ) : ℝ) ^ ε < 2`,
there exists a prime `p` with `m < p ≤ 2 * m`, so `(p : ℝ) ^ ε < 2` and `m ≤ p - 1 ≤ B` for every
`B ∈ UniformBoundSet ε`.
-/
theorem bertrand_le_of_mem_uniformBoundSet {ε : ℝ} {m B : ℕ}
    (hm : m ≠ 0) (hε : 0 ≤ ε) (hpow : ((2 * m : ℕ) : ℝ) ^ ε < 2)
    (hB : B ∈ UniformBoundSet ε) :
    m ≤ B := by
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul m hm
  have hp_pow : (p : ℝ) ^ ε < 2 := by
    refine lt_of_le_of_lt ?_ hpow
    exact Real.rpow_le_rpow (Nat.cast_nonneg p) (by exact_mod_cast hp2m) hε
  have hpred := pred_prime_le_of_mem_uniformBoundSet_of_rpow_lt_two hp hp_pow hB
  omega

/--
Contrapositive of `bertrand_le_of_mem_uniformBoundSet` at `m = B + 1`: for every `0 ≤ ε` and
`B ∈ UniformBoundSet ε`, `(2 : ℝ) ≤ ((2 * (B + 1) : ℕ) : ℝ) ^ ε`.
-/
theorem two_le_two_mul_succ_rpow_of_mem_uniformBoundSet {ε : ℝ} {B : ℕ}
    (hε : 0 ≤ ε) (hB : B ∈ UniformBoundSet ε) :
    (2 : ℝ) ≤ ((2 * (B + 1) : ℕ) : ℝ) ^ ε := by
  by_contra hlt
  have hlt' : ((2 * (B + 1) : ℕ) : ℝ) ^ ε < 2 := lt_of_not_ge hlt
  have hle := bertrand_le_of_mem_uniformBoundSet (Nat.succ_ne_zero B) hε hlt' hB
  omega

/--
Exponential lower bound in `ε⁻¹` for any uniform bound `B ∈ UniformBoundSet ε` (`ε > 0`):
`(2 : ℝ) ^ (ε⁻¹) ≤ 4 * (B : ℝ)`.
-/
theorem two_rpow_inv_le_four_mul_of_mem_uniformBoundSet {ε : ℝ} {B : ℕ}
    (hε : 0 < ε) (hB : B ∈ UniformBoundSet ε) :
    (2 : ℝ) ^ (ε⁻¹) ≤ 4 * (B : ℝ) := by
  have hB1 : 1 ≤ B := one_le_of_mem_uniformBoundSet hB
  have hbase : ((2 * (B + 1) : ℕ) : ℝ) ≤ 4 * (B : ℝ) := by
    have : 2 * (B + 1) ≤ 4 * B := by omega
    exact_mod_cast this
  have h2 : (2 : ℝ) ≤ (4 * (B : ℝ)) ^ ε := by
    refine (two_le_two_mul_succ_rpow_of_mem_uniformBoundSet hε.le hB).trans ?_
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hbase hε.le
  have hinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  calc
    (2 : ℝ) ^ (ε⁻¹) ≤ ((4 * (B : ℝ)) ^ ε) ^ (ε⁻¹) :=
      Real.rpow_le_rpow (by positivity) h2 hinv
    _ = (4 * (B : ℝ)) ^ (ε * ε⁻¹) := by
      rw [← Real.rpow_mul (by positivity)]
    _ = 4 * (B : ℝ) := by
      rw [mul_inv_cancel₀ hε.ne', Real.rpow_one]

/--
Exponential lower bound `(2 : ℝ) ^ (ε⁻¹) ≤ 4 * (C ε : ℝ)` for the all-prime constant `C ε`
whenever `UniformBoundSet ε` is nonempty (`ε > 0`), formalizing the remark in
`FormalConjectures/ErdosProblems/1180.lean` that no bound polynomial in `ε⁻¹` can hold uniformly
across all primes without a large-prime threshold `P ≤ p`.
-/
theorem two_rpow_inv_le_four_mul_C_of_nonempty {ε : ℝ}
    (hε : 0 < ε) (hne : (UniformBoundSet ε).Nonempty) :
    (2 : ℝ) ^ (ε⁻¹) ≤ 4 * (C ε : ℝ) :=
  two_rpow_inv_le_four_mul_of_mem_uniformBoundSet hε (C_mem_uniformBoundSet hne)

/--
Explicit linear-in-`ε⁻¹` lower bound `(Real.log 2 / 4) * ε⁻¹ ≤ (B : ℝ)` for every `ε > 0` and
every `B ∈ UniformBoundSet ε`.
-/
theorem quarter_log_two_mul_inv_le_of_mem_uniformBoundSet {ε : ℝ} {B : ℕ}
    (hε : 0 < ε) (hB : B ∈ UniformBoundSet ε) :
    (Real.log 2 / 4) * ε⁻¹ ≤ (B : ℝ) := by
  have hpow := two_rpow_inv_le_four_mul_of_mem_uniformBoundSet hε hB
  have hexp : Real.log 2 * ε⁻¹ + 1 ≤ (2 : ℝ) ^ (ε⁻¹) := by
    rw [Real.rpow_def_of_pos zero_lt_two]
    exact Real.add_one_le_exp (Real.log 2 * ε⁻¹)
  linarith

/--
Conditional reduction of `erdos_1180.variants.lower_bound`: if `UniformBoundSet ε` is nonempty for
every `ε ∈ (0, 1]` (which is the content of `erdos_1180`), then `K = Real.log 2 / 4 > 0` satisfies
`K * ε⁻¹ ≤ (C ε : ℝ)` for all `0 < ε ≤ 1`.
-/
theorem erdos_1180_lower_bound_of_nonempty
    (hne : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (UniformBoundSet ε).Nonempty) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → K * ε⁻¹ ≤ (C ε : ℝ) := by
  refine ⟨Real.log 2 / 4, ?_, ?_⟩
  · have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  · intro ε hε0 hε1
    exact quarter_log_two_mul_inv_le_of_mem_uniformBoundSet hε0 (C_mem_uniformBoundSet (hne ε hε0 hε1))

/--
Set of large-prime asymptotic multiset-cardinality bounds (matching the quantifier structure of
`erdos_1180.variants.shparlinski` and `erdos_1180.variants.glibichuk`).
-/
def AsymptoticBoundSet (ε : ℝ) : Set ℕ :=
  {C | ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}

/--
Large-prime asymptotic representation constant `CAsymptotic ε = sInf (AsymptoticBoundSet ε)`.
-/
noncomputable def CAsymptotic (ε : ℝ) : ℕ :=
  sInf (AsymptoticBoundSet ε)

/--
Finite set of admissible denominators `n` satisfying `AdmissibleDenom ε p n`.
-/
noncomputable def admissibleFinset (ε : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊(p : ℝ) ^ ε⌋₊).filter (fun n ↦ n.Coprime p)

theorem mem_admissibleFinset_iff {ε : ℝ} {p n : ℕ} :
    n ∈ admissibleFinset ε p ↔ AdmissibleDenom ε p n := by
  unfold admissibleFinset AdmissibleDenom
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨h1, ?_, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨⟨h1, ?_⟩, h3⟩⟩
  · exact (Nat.cast_le.mpr h2).trans (Nat.floor_le (by positivity))
  · exact Nat.le_floor h2

/--
Finite set of modular inverses `(n : ZMod p)⁻¹` of admissible denominators `n ∈ admissibleFinset ε p`.
-/
noncomputable def invSet (ε : ℝ) (p : ℕ) : Finset (ZMod p) :=
  (admissibleFinset ε p).image (fun n : ℕ ↦ (n : ZMod p)⁻¹)

/--
Membership characterization for `invSet ε p`: a residue `a : ZMod p` belongs to `invSet ε p`
if and only if `a = (n : ZMod p)⁻¹` for some admissible denominator `n`.
-/
theorem mem_invSet_iff_exists_admissibleDenom {ε : ℝ} {p : ℕ} {a : ZMod p} :
    a ∈ invSet ε p ↔ ∃ n : ℕ, AdmissibleDenom ε p n ∧ (n : ZMod p)⁻¹ = a := by
  unfold invSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, mem_admissibleFinset_iff.mp hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, mem_admissibleFinset_iff.mpr hn, rfl⟩

/--
Every residue `a` in the `k`-fold sumset `k • invSet ε p` is represented by a multiset `s` of
exact cardinality `s.card = k`.
-/
theorem exists_represents_card_eq_of_mem_nsmul_invSet {ε : ℝ} {p : ℕ} :
    ∀ (k : ℕ) {a : ZMod p}, a ∈ k • invSet ε p →
      ∃ s : Multiset ℕ, s.card = k ∧ Represents ε p a s
  | 0, a, ha => by
      rw [zero_nsmul, Finset.mem_zero] at ha
      subst ha
      exact ⟨0, rfl, represents_zero ε p⟩
  | k + 1, a, ha => by
      rw [succ_nsmul, Finset.mem_add] at ha
      rcases ha with ⟨b, hb, c, hc, rfl⟩
      obtain ⟨s, hscard, hsrep⟩ := exists_represents_card_eq_of_mem_nsmul_invSet k hb
      obtain ⟨n, hnadm, rfl⟩ := mem_invSet_iff_exists_admissibleDenom.mp hc
      refine ⟨s + {n}, ?_, represents_add hsrep (represents_singleton hnadm)⟩
      simp [hscard]

theorem uniformBoundSet_subset_asymptoticBoundSet (ε : ℝ) :
    UniformBoundSet ε ⊆ AsymptoticBoundSet ε := by
  intro B hB
  exact ⟨0, fun p _ hp a ↦ hB p hp a⟩

theorem card_admissibleFinset_le_natFloor (ε : ℝ) (p : ℕ) :
    (admissibleFinset ε p).card ≤ ⌊(p : ℝ) ^ ε⌋₊ := by
  unfold admissibleFinset
  calc
    ((Finset.Icc 1 ⌊(p : ℝ) ^ ε⌋₊).filter (fun n ↦ n.Coprime p)).card
      ≤ (Finset.Icc 1 ⌊(p : ℝ) ^ ε⌋₊).card := Finset.card_filter_le _ _
    _ = ⌊(p : ℝ) ^ ε⌋₊ := by simp

/--
Evaluation of an optional denominator from `D` as its modular inverse in `ZMod p` (or `0` for `none`).
-/
def evalOptionDenom (p : ℕ) (D : Finset ℕ) : Option D → ZMod p
  | none => 0
  | some d => (d.1 : ZMod p)⁻¹

/--
Sum of `C₀` optional denominators in `ZMod p`.
-/
def evalOptionVec (p : ℕ) (D : Finset ℕ) (C₀ : ℕ) (f : Fin C₀ → Option D) : ZMod p :=
  ∑ i : Fin C₀, evalOptionDenom p D (f i)

/--
Every multiset `s` of cardinality at most `C₀` with elements in `D` has its modular-inverse sum
realized by some padded tuple `f : Fin C₀ → Option D`.
-/
theorem exists_evalOptionVec_eq_multiset_sum (p : ℕ) (D : Finset ℕ) :
    ∀ (C₀ : ℕ) (s : Multiset ℕ),
      s.card ≤ C₀ → (∀ n ∈ s, n ∈ D) →
        ∃ f : Fin C₀ → Option D,
          evalOptionVec p D C₀ f = (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum
  | 0, s, hcard, _ => by
      have hs : s = 0 := Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      subst hs
      refine ⟨Fin.elim0, ?_⟩
      simp [evalOptionVec]
  | C₀ + 1, s, hcard, hmem => by
      by_cases hs : s = 0
      · subst hs
        refine ⟨fun _ ↦ none, ?_⟩
        simp [evalOptionVec, evalOptionDenom]
      · obtain ⟨n, hn⟩ := Multiset.exists_mem_of_ne_zero hs
        have hcons : n ::ₘ s.erase n = s := Multiset.cons_erase hn
        have hcard_erase : (s.erase n).card ≤ C₀ := by
          have hc : (n ::ₘ s.erase n).card ≤ C₀ + 1 := by simpa [hcons] using hcard
          rw [Multiset.card_cons] at hc
          omega
        have hmem_erase : ∀ m ∈ s.erase n, m ∈ D := by
          intro m hm
          exact hmem m (Multiset.mem_of_mem_erase hm)
        obtain ⟨f, hf⟩ :=
          exists_evalOptionVec_eq_multiset_sum p D C₀ (s.erase n) hcard_erase hmem_erase
        refine ⟨Fin.cons (some ⟨n, hmem n hn⟩) f, ?_⟩
        unfold evalOptionVec at hf ⊢
        rw [Fin.sum_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ, hf]
        conv_rhs => rw [← hcons]
        simp [evalOptionDenom]

/--
Pigeonhole power bound: if every residue in `ZMod p` is represented by a multiset of size at most
`C₀` drawn from a finite set `D`, then `p ≤ (D.card + 1) ^ C₀`.
-/
theorem prime_le_card_succ_pow_of_subset_denoms (p C₀ : ℕ) [NeZero p] (D : Finset ℕ)
    (hcover : ∀ a : ZMod p, ∃ s : Multiset ℕ,
      s.card ≤ C₀ ∧ (∀ n ∈ s, n ∈ D) ∧ (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a) :
    p ≤ (D.card + 1) ^ C₀ := by
  have hsurj : Function.Surjective (evalOptionVec p D C₀) := by
    intro a
    obtain ⟨s, hcard, hmem, hsum⟩ := hcover a
    obtain ⟨f, hf⟩ := exists_evalOptionVec_eq_multiset_sum p D C₀ s hcard hmem
    exact ⟨f, hf.trans hsum⟩
  have hle := Fintype.card_le_of_surjective (evalOptionVec p D C₀) hsurj
  simpa [ZMod.card, Fintype.card_fun, Fintype.card_option, Fintype.card_coe] using hle

/--
If every residue in `ZMod p` is represented by at most `C₀` admissible denominators for `(ε, p)`,
then `p ≤ ((admissibleFinset ε p).card + 1) ^ C₀` and hence `p ≤ (⌊(p : ℝ) ^ ε⌋₊ + 1) ^ C₀`.
-/
theorem prime_le_natFloor_succ_pow_of_cover {ε : ℝ} {p C₀ : ℕ} [NeZero p]
    (hcover : ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C₀ ∧ Represents ε p a s) :
    p ≤ (⌊(p : ℝ) ^ ε⌋₊ + 1) ^ C₀ := by
  have h1 : p ≤ ((admissibleFinset ε p).card + 1) ^ C₀ := by
    apply prime_le_card_succ_pow_of_subset_denoms p C₀ (admissibleFinset ε p)
    intro a
    obtain ⟨s, hcard, hrep⟩ := hcover a
    refine ⟨s, hcard, ?_, hrep.2⟩
    intro n hn
    exact mem_admissibleFinset_iff.mpr (hrep.1 n hn)
  exact h1.trans (Nat.pow_le_pow_left (Nat.add_le_add_right (card_admissibleFinset_le_natFloor ε p) 1) C₀)

/--
Every asymptotic bound `B ∈ AsymptoticBoundSet ε` satisfies `1 ≤ B` unconditionally for all `ε : ℝ`.
-/
theorem one_le_of_mem_asymptoticBoundSet {ε : ℝ} {B : ℕ}
    (hB : B ∈ AsymptoticBoundSet ε) : 1 ≤ B := by
  rcases hB with ⟨P, hP⟩
  obtain ⟨p, hpP, hp⟩ := Nat.exists_infinite_primes (max P 2)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hcard, hrep⟩ := hP p (le_trans (le_max_left P 2) hpP) hp 1
  have hs0 : s ≠ 0 := by
    intro h0
    have hsum := hrep.2
    rw [h0] at hsum
    simp at hsum
  exact (Nat.succ_le_of_lt (Multiset.card_pos.mpr hs0)).trans hcard

/--
For every `ε ≥ 1`, `1` belongs to `UniformBoundSet ε`: every residue modulo every prime `p` is the
sum of at most `1` admissible modular inverse.
-/
theorem one_mem_uniformBoundSet_of_one_le {ε : ℝ} (hε : 1 ≤ ε) :
    1 ∈ UniformBoundSet ε := by
  intro p hp a
  have : Fact p.Prime := ⟨hp⟩
  by_cases ha0 : a = 0
  · subst ha0
    exact ⟨0, Nat.zero_le 1, represents_zero ε p⟩
  · have hainv0 : a⁻¹ ≠ 0 := inv_ne_zero ha0
    let n : ℕ := a⁻¹.val
    have hn_pos : 0 < n := ZMod.val_pos.mpr hainv0
    have hn_lt : n < p := ZMod.val_lt a⁻¹
    have hcop : n.Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact Nat.not_dvd_of_pos_of_lt hn_pos hn_lt
    have hn_rpow : (n : ℝ) ≤ (p : ℝ) ^ ε := by
      have hnp : (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast hn_lt.le
      have hp_rpow : (p : ℝ) ≤ (p : ℝ) ^ ε := by
        calc
          (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one (p : ℝ)).symm
          _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) hε
      exact hnp.trans hp_rpow
    have hadm : AdmissibleDenom ε p n := ⟨hn_pos, hn_rpow, hcop⟩
    have hrep := represents_singleton hadm
    have hcast : (n : ZMod p)⁻¹ = a := by
      dsimp [n]
      rw [ZMod.natCast_zmod_val, inv_inv]
    rw [hcast] at hrep
    exact ⟨{n}, by simp, hrep⟩

/--
Exact unconditional evaluation `CAsymptotic ε = 1` for every `ε ≥ 1`.
-/
theorem CAsymptotic_eq_one_of_one_le {ε : ℝ} (hε : 1 ≤ ε) :
    CAsymptotic ε = 1 := by
  have hmem : 1 ∈ UniformBoundSet ε := one_mem_uniformBoundSet_of_one_le hε
  have hasymp : 1 ∈ AsymptoticBoundSet ε := uniformBoundSet_subset_asymptoticBoundSet ε hmem
  apply le_antisymm
  · exact Nat.sInf_le hasymp
  · exact one_le_of_mem_asymptoticBoundSet (Nat.sInf_mem ⟨1, hasymp⟩)
end Erdos1180
