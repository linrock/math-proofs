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
open Filter
namespace Erdos338
/-- `A` is an additive basis of order (at most) `h`: every sufficiently large natural number is
the sum of at most `h` elements of `A`, repetitions allowed. -/
def IsAddBasisOfOrderLE (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Multiset ℕ, (∀ a ∈ s, a ∈ A) ∧ Multiset.card s ≤ h ∧ s.sum = n
/-- `h` is *the* order of `A`: `A` is a basis of order `h` and of no smaller order. -/
def HasExactOrder (A : Set ℕ) (h : ℕ) : Prop :=
  IsAddBasisOfOrderLE A h ∧ ∀ k < h, ¬ IsAddBasisOfOrderLE A k

/-- Every sufficiently large natural number is the sum of at most `t` *distinct* elements
of `A`. -/
def IsRestrictedBasisOfOrderLE (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ s.card ≤ t ∧ ∑ a ∈ s, a = n

/-- `t` is the restricted order of `A` (the least `t` with the property above). -/
def HasExactRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  IsRestrictedBasisOfOrderLE A t ∧ ∀ k < t, ¬ IsRestrictedBasisOfOrderLE A k

/-- Enlarging the order keeps an additive basis property. -/
theorem isAddBasisOfOrderLE_mono {A : Set ℕ} {h k : ℕ} (hA : IsAddBasisOfOrderLE A h)
    (hk : h ≤ k) : IsAddBasisOfOrderLE A k :=
  Filter.Eventually.mono hA fun _ ⟨s, hs, hc, hsum⟩ => ⟨s, hs, hc.trans hk, hsum⟩

theorem isRestrictedBasisOfOrderLE_mono {A : Set ℕ} {t k : ℕ}
    (hA : IsRestrictedBasisOfOrderLE A t) (hk : t ≤ k) : IsRestrictedBasisOfOrderLE A k :=
  Filter.Eventually.mono hA fun _ ⟨s, hs, hc, hsum⟩ => ⟨s, hs, hc.trans hk, hsum⟩
/-! ## Modular excess obstruction for restricted order -/

/-- Universal modular excess invariant: if every element of `A` outside `F` has residue `≤ 1`
modulo `M`, then for any finite subset `s ⊆ A`,
`∑ a ∈ s, (a % M) ≤ ∑ a ∈ s ∩ F, (a % M - 1) + s.card`. -/
lemma finset_sum_mod_le_excess_add_card {A : Set ℕ} {F : Finset ℕ} {M : ℕ}
    (hmod : ∀ a ∈ A, a ∉ F → a % M ≤ 1) (s : Finset ℕ) (hs : (↑s : Set ℕ) ⊆ A) :
    ∑ a ∈ s, (a % M) ≤ ∑ a ∈ s ∩ F, (a % M - 1) + s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.coe_insert, Set.insert_subset_iff] at hs
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has]
    have hih := ih hs.2
    by_cases haF : a ∈ F
    · have hins : insert a s ∩ F = insert a (s ∩ F) := Finset.insert_inter_of_mem haF
      have ha_not : a ∉ s ∩ F := fun h => has (Finset.mem_inter.1 h).1
      rw [hins, Finset.sum_insert ha_not]
      omega
    · have hins : insert a s ∩ F = s ∩ F := Finset.insert_inter_of_notMem haF
      have hamod : a % M ≤ 1 := hmod a hs.1 haF
      rw [hins]
      omega

/-- The remainder of a Finset sum modulo `M` never exceeds the sum of the remainders. -/
lemma finset_mod_le_sum_mod (M : ℕ) (s : Finset ℕ) :
    (∑ a ∈ s, a) % M ≤ ∑ a ∈ s, (a % M) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, Nat.add_mod]
    have hle : (a % M + (∑ x ∈ s, x) % M) % M ≤ a % M + (∑ x ∈ s, x) % M := Nat.mod_le _ _
    omega

/-- **Universal Modular Excess Obstruction for Restricted Order**:
if every element of `A \ ↑F` has residue `≤ 1` modulo `M`, and `∑ a ∈ F, (a % M - 1) + t < r`
for some residue `r < M`, then no integer `n ≡ r (mod M)` is a sum of at most `t` distinct
elements of `A`, so `¬ IsRestrictedBasisOfOrderLE A t`. -/
theorem not_isRestrictedBasisOfOrderLE_of_modular_excess {A : Set ℕ} {F : Finset ℕ} {M t r : ℕ}
    (hmod : ∀ a ∈ A, a ∉ F → a % M ≤ 1) (hrM : r < M)
    (hexcess : ∑ a ∈ F, (a % M - 1) + t < r) :
    ¬ IsRestrictedBasisOfOrderLE A t := by
  intro hA
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  have hM1 : 1 ≤ M := by omega
  obtain ⟨s, hs, hcard, hsum⟩ := hN (M * N + r) (by nlinarith)
  have h1 := finset_mod_le_sum_mod M s
  have h2 := finset_sum_mod_le_excess_add_card hmod s hs
  have h3 : ∑ a ∈ s ∩ F, (a % M - 1) ≤ ∑ a ∈ F, (a % M - 1) :=
    Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have hmod_eq : (∑ a ∈ s, a) % M = r := by
    rw [hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt hrM]
  omega
/-! ## Hegyvári–Hennecart–Plagne (2007) construction -/

/-- The modulus `3 * 2 ^ m` of the Hegyvári–Hennecart–Plagne construction at index `m = k - 2`. -/
def hhpMod (m : ℕ) : ℕ := 3 * 2 ^ m

/-- The finite dyadic core `{2^1, 2^2, ..., 2^m}`, which has exactly `m` elements. -/
def hhpCore (m : ℕ) : Finset ℕ := (Finset.range m).image (fun i => 2 ^ (i + 1))

/-- The residue progressions of the construction: all `n ≥ 3 * 2 ^ m` with `n ≡ 0` or `n ≡ 1`
modulo `3 * 2 ^ m`. -/
def hhpProg (m : ℕ) : Set ℕ := {n | hhpMod m ≤ n ∧ (n % hhpMod m = 0 ∨ n % hhpMod m = 1)}

/-- The Hegyvári–Hennecart–Plagne basis at index `m`: the dyadic core together with the residue
progressions. The proofs show that it has exact order `m + 2` (see `hhpSet_hasOrder`) and exact
restricted order `2 ^ m + m + 1` (see `hhpSet_hasRestrictedOrder`). -/
def hhpSet (m : ℕ) : Set ℕ := (↑(hhpCore m) : Set ℕ) ∪ hhpProg m

/-- Predicate that `a` is either `0` or `2 ^ j` for some `j ≤ m`. -/
def IsDyadicOrZero (m a : ℕ) : Prop := a = 0 ∨ ∃ j ≤ m, a = 2 ^ j

lemma two_pow_succ_injOn {m : ℕ} : Set.InjOn (fun i : ℕ => 2 ^ (i + 1)) ↑(Finset.range m) := by
  intro i _ j _ hij
  have h1 : i + 1 = j + 1 := Nat.pow_right_injective le_rfl hij
  omega

lemma hhpCore_card (m : ℕ) : (hhpCore m).card = m := by
  unfold hhpCore
  rw [Finset.card_image_of_injOn two_pow_succ_injOn, Finset.card_range]

lemma sum_range_two_pow_succ (m : ℕ) :
    ∑ i ∈ Finset.range m, 2 ^ (i + 1) = 2 ^ (m + 1) - 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpos : 2 ≤ 2 ^ (m + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    rw [pow_succ, pow_succ]
    omega

lemma hhpCore_sum (m : ℕ) : ∑ a ∈ hhpCore m, a = 2 ^ (m + 1) - 2 := by
  unfold hhpCore
  rw [Finset.sum_image two_pow_succ_injOn, sum_range_two_pow_succ]

lemma hhpCore_lt_hhpMod {m a : ℕ} (ha : a ∈ hhpCore m) : a < hhpMod m := by
  unfold hhpCore hhpMod at *
  rcases Finset.mem_image.1 ha with ⟨i, hi, rfl⟩
  rw [Finset.mem_range] at hi
  have hle : 2 ^ (i + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hpos : 0 < 2 ^ m := by positivity
  omega

lemma hhpCore_mono {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) : hhpCore m₁ ⊆ hhpCore m₂ :=
  Finset.image_subset_image (Finset.range_mono h)

lemma hhpCore_le_two_pow {m a : ℕ} (ha : a ∈ hhpCore m) : a ≤ 2 ^ m := by
  unfold hhpCore at ha
  rcases Finset.mem_image.1 ha with ⟨i, hi, rfl⟩
  rw [Finset.mem_range] at hi
  exact Nat.pow_le_pow_right (by omega) (by omega)

lemma two_pow_succ_notMem_hhpCore (m : ℕ) : 2 ^ (m + 1) ∉ hhpCore m := by
  intro ha
  have hle := hhpCore_le_two_pow ha
  have hpos : 0 < 2 ^ m := by positivity
  rw [pow_succ] at hle
  omega

lemma two_pow_succ_mem_hhpCore_succ (m : ℕ) : 2 ^ (m + 1) ∈ hhpCore (m + 1) := by
  unfold hhpCore
  exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))

lemma hhpMod_three_le (m : ℕ) : 3 ≤ hhpMod m := by
  unfold hhpMod
  have : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by omega)
  omega

lemma hhpMod_mul_add_mem_hhpProg {m q b₀ : ℕ} (hq : 1 ≤ q) (hb₀ : b₀ ≤ 1) :
    hhpMod m * q + b₀ ∈ hhpProg m := by
  have hM := hhpMod_three_le m
  refine ⟨by nlinarith, ?_⟩
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

lemma hhpCore_excess_sum (m : ℕ) :
    ∑ a ∈ hhpCore m, (a % hhpMod m - 1) = 2 ^ (m + 1) - 2 - m := by
  have h1 : ∑ a ∈ hhpCore m, (a % hhpMod m - 1) = ∑ i ∈ Finset.range m, (2 ^ (i + 1) - 1) := by
    unfold hhpCore
    rw [Finset.sum_image two_pow_succ_injOn]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hlt : 2 ^ (i + 1) < hhpMod m := hhpCore_lt_hhpMod (Finset.mem_image_of_mem _ hi)
    rw [Nat.mod_eq_of_lt hlt]
  rw [h1]
  clear h1
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpos1 : 2 + m ≤ 2 ^ (m + 1) := by
      clear ih
      induction m with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ]
        omega
    have hpos2 : 1 ≤ 2 ^ (m + 1 + 1) := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ (2 : ℕ) (m + 1)]
    omega

/-- `hhpSet m` is not a restricted basis of order at most `2 ^ m + m`:
integers `≡ 3 * 2^m - 1 (mod 3 * 2^m)` require at least `2 ^ m + m + 1` distinct summands. -/
theorem hhpSet_not_isRestrictedBasisOfOrderLE (m : ℕ) :
    ¬ IsRestrictedBasisOfOrderLE (hhpSet m) (2 ^ m + m) := by
  have hpos : 2 + m ≤ 2 ^ (m + 1) := by
    induction m with
    | zero => simp
    | succ k ihk => rw [pow_succ]; omega
  refine not_isRestrictedBasisOfOrderLE_of_modular_excess
    (F := hhpCore m) (M := hhpMod m) (r := hhpMod m - 1) ?_ ?_ ?_
  · intro a ha haF
    rcases ha with haCore | ⟨-, h0 | h1⟩
    · exact False.elim (haF haCore)
    · omega
    · omega
  · unfold hhpMod
    have : 0 < 2 ^ m := by positivity
    omega
  · rw [hhpCore_excess_sum]
    unfold hhpMod
    rw [pow_succ]
    omega

lemma hhpSet_mod_isDyadicOrZero {m a : ℕ} (ha : a ∈ hhpSet m) :
    IsDyadicOrZero m (a % hhpMod m) := by
  rcases ha with haCore | ⟨-, h0 | h1⟩
  · have hlt : a < hhpMod m := hhpCore_lt_hhpMod haCore
    rw [Nat.mod_eq_of_lt hlt]
    rcases Finset.mem_image.1 haCore with ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    exact Or.inr ⟨i + 1, by omega, rfl⟩
  · exact Or.inl h0
  · exact Or.inr ⟨0, Nat.zero_le m, by simpa using h1⟩

lemma multiset_dyadic_decompose_step {m : ℕ} (s : Multiset ℕ)
    (hs : ∀ a ∈ s, IsDyadicOrZero (m + 1) a) :
    ∃ (c : ℕ) (u : Multiset ℕ),
      (∀ b ∈ u, IsDyadicOrZero m b) ∧
      c + Multiset.card u = Multiset.card s ∧
      s.sum = c + 2 * u.sum := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, 0, by simp, by simp, by simp⟩
  | cons a s ih =>
    obtain ⟨c, u, hu, hcard, hsum⟩ := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    have ha := hs a (Multiset.mem_cons_self a s)
    rcases ha with rfl | ⟨j, hj, rfl⟩
    · refine ⟨c, 0 ::ₘ u, ?_, ?_, ?_⟩
      · intro b hb
        rcases Multiset.mem_cons.1 hb with rfl | hb
        · exact Or.inl rfl
        · exact hu b hb
      · simp [← hcard]; omega
      · simp [hsum]
    · cases j with
      | zero =>
        refine ⟨c + 1, u, hu, ?_, ?_⟩
        · simp [← hcard]; omega
        · simp [hsum]; omega
      | succ j =>
        refine ⟨c, (2 ^ j) ::ₘ u, ?_, ?_, ?_⟩
        · intro b hb
          rcases Multiset.mem_cons.1 hb with rfl | hb
          · exact Or.inr ⟨j, by omega, rfl⟩
          · exact hu b hb
        · simp [← hcard]; omega
        · rw [Multiset.sum_cons, Multiset.sum_cons, hsum, pow_succ]
          ring

lemma half_mod_eq_pred_of_double_mod_eq_pred {c u M : ℕ} (hM : 0 < M)
    (hbad : (c + 2 * u) % (2 * M) = 2 * M - 1) :
    c % 2 = 1 ∧ (c / 2 + u) % M = M - 1 := by
  have hdiv := Nat.mod_add_div (c + 2 * u) (2 * M)
  rw [hbad] at hdiv
  set q := (c + 2 * u) / (2 * M)
  have hring : 2 * M * q = 2 * (M * q) := by ring
  rw [hring] at hdiv
  have hc_odd : c % 2 = 1 := by omega
  have hhalf : c / 2 + u = M * q + (M - 1) := by omega
  refine ⟨hc_odd, ?_⟩
  rw [hhalf, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

lemma dyadic_multiset_sum_mod_ne_pred (m : ℕ) :
    ∀ s : Multiset ℕ, (∀ a ∈ s, IsDyadicOrZero m a) →
      Multiset.card s ≤ m + 1 → s.sum % hhpMod m ≠ hhpMod m - 1 := by
  induction m with
  | zero =>
    intro s hs hcard
    have hcards : Multiset.card s = 0 ∨ Multiset.card s = 1 := by omega
    rcases hcards with h0 | h1
    · rw [Multiset.card_eq_zero] at h0
      subst h0
      simp [hhpMod]
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h1
      have ha := hs a (by simp)
      rcases ha with rfl | ⟨j, hj, rfl⟩
      · simp [hhpMod]
      · have hj0 : j = 0 := by omega
        subst hj0
        simp [hhpMod]
  | succ m ih =>
    intro s hs hcard hbad
    obtain ⟨c, u, hu, hcu_card, hcu_sum⟩ := multiset_dyadic_decompose_step s hs
    have hmod_even : hhpMod (m + 1) = 2 * hhpMod m := by
      unfold hhpMod
      rw [pow_succ]
      ring
    have hpos : 0 < hhpMod m := by unfold hhpMod; positivity
    rw [hcu_sum, hmod_even] at hbad
    obtain ⟨hc_odd, hhalf_mod⟩ := half_mod_eq_pred_of_double_mod_eq_pred hpos hbad
    set s' : Multiset ℕ := Multiset.replicate (c / 2) 1 + u
    have hs'_mem : ∀ b ∈ s', IsDyadicOrZero m b := by
      intro b hb
      rcases Multiset.mem_add.1 hb with hb1 | hbu
      · rw [Multiset.eq_of_mem_replicate hb1]
        exact Or.inr ⟨0, Nat.zero_le m, rfl⟩
      · exact hu b hbu
    have hs'_card : Multiset.card s' ≤ m + 1 := by
      have hcard_eq : Multiset.card s' = c / 2 + Multiset.card u := by simp [s']
      omega
    have hs'_bad : s'.sum % hhpMod m = hhpMod m - 1 := by
      have hsum_s' : s'.sum = c / 2 + u.sum := by simp [s']
      rw [hsum_s']
      exact hhalf_mod
    exact ih s' hs'_mem hs'_card hs'_bad

lemma multiset_sum_mod_eq_map_mod_sum_mod (M : ℕ) (s : Multiset ℕ) :
    s.sum % M = (s.map (· % M)).sum % M := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Nat.add_mod, ih]
    simp

/-- `hhpSet m` is not an additive basis of order at most `m + 1`:
integers `≡ 3 * 2^m - 1 (mod 3 * 2^m)` cannot be written as a sum of `≤ m + 1` elements of `hhpSet m`. -/
theorem hhpSet_not_isAddBasisOfOrderLE (m : ℕ) :
    ¬ IsAddBasisOfOrderLE (hhpSet m) (m + 1) := by
  intro hA
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  have hpos : 0 < hhpMod m := by unfold hhpMod; positivity
  obtain ⟨s, hs, hcard, hsum⟩ := hN (hhpMod m * N + (hhpMod m - 1)) (by nlinarith)
  set sm := s.map (· % hhpMod m)
  have hsm_mem : ∀ b ∈ sm, IsDyadicOrZero m b := by
    intro b hb
    rcases Multiset.mem_map.1 hb with ⟨a, ha, rfl⟩
    exact hhpSet_mod_isDyadicOrZero (hs a ha)
  have hsm_card : Multiset.card sm ≤ m + 1 := by simpa [sm] using hcard
  have hsm_mod : sm.sum % hhpMod m = hhpMod m - 1 := by
    rw [← multiset_sum_mod_eq_map_mod_sum_mod, hsum, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (by omega)]
  exact dyadic_multiset_sum_mod_ne_pred m sm hsm_mem hsm_card hsm_mod

/-- Every integer `r < 2 ^ (m + 1)` can be written as `(∑ a ∈ u, a) + b₀` for some subset
`u ⊆ hhpCore m` and bit `b₀ ≤ 1`. -/
lemma exists_subset_hhpCore_for_lt_two_pow (m : ℕ) :
    ∀ r < 2 ^ (m + 1), ∃ (u : Finset ℕ) (b₀ : ℕ),
      u ⊆ hhpCore m ∧ b₀ ≤ 1 ∧ r = (∑ a ∈ u, a) + b₀ := by
  induction m with
  | zero =>
    intro r hr
    exact ⟨∅, r, Finset.empty_subset _, by omega, by simp⟩
  | succ m ih =>
    intro r hr
    by_cases hlt : r < 2 ^ (m + 1)
    · obtain ⟨u, b₀, hu, hb₀, hr_eq⟩ := ih r hlt
      exact ⟨u, b₀, Finset.Subset.trans hu (hhpCore_mono (by omega)), hb₀, hr_eq⟩
    · have hr_sub : r - 2 ^ (m + 1) < 2 ^ (m + 1) := by
        rw [pow_succ (2 : ℕ) (m + 1)] at hr
        omega
      obtain ⟨u, b₀, hu, hb₀, hr_eq⟩ := ih (r - 2 ^ (m + 1)) hr_sub
      have hnot : 2 ^ (m + 1) ∉ u := fun h => two_pow_succ_notMem_hhpCore m (hu h)
      refine ⟨insert (2 ^ (m + 1)) u, b₀, ?_, hb₀, ?_⟩
      · rw [Finset.insert_subset_iff]
        exact ⟨two_pow_succ_mem_hhpCore_succ m,
          Finset.Subset.trans hu (hhpCore_mono (by omega))⟩
      · rw [Finset.sum_insert hnot]
        omega

/-- `hhpSet m` is an additive basis of order at most `m + 2`. -/
theorem hhpSet_isAddBasisOfOrderLE (m : ℕ) :
    IsAddBasisOfOrderLE (hhpSet m) (m + 2) := by
  refine Filter.eventually_atTop.2 ⟨3 * hhpMod m, fun n hn => ?_⟩
  have hM3 := hhpMod_three_le m
  set r := n % hhpMod m
  set q := n / hhpMod m
  have hn_eq : n = hhpMod m * q + r := (Nat.div_add_mod n (hhpMod m)).symm
  have hr_lt : r < 3 * 2 ^ m := by
    have : r < hhpMod m := Nat.mod_lt n (by omega)
    simpa [hhpMod] using this
  have hq_ge : 3 ≤ q := by
    have hr_le : r < hhpMod m := Nat.mod_lt n (by omega)
    nlinarith
  by_cases hlt : r < 2 ^ (m + 1)
  · obtain ⟨u, b₀, hu, hb₀, hr_eq⟩ := exists_subset_hhpCore_for_lt_two_pow m r hlt
    refine ⟨(hhpMod m * q + b₀) ::ₘ u.val, ?_, ?_, ?_⟩
    · intro a ha
      rcases Multiset.mem_cons.1 ha with rfl | ha
      · exact Or.inr (hhpMod_mul_add_mem_hhpProg (by omega) hb₀)
      · exact Or.inl (hu ha)
    · rw [Multiset.card_cons, ← Finset.card_def]
      have hucard : u.card ≤ m := (Finset.card_le_card hu).trans (hhpCore_card m).le
      omega
    · rw [Multiset.sum_cons, Finset.sum_val]
      simp only [id_eq]
      omega
  · cases m with
    | zero =>
      have hr2 : r = 2 := by simp at hlt hr_lt; omega
      have hM0 : hhpMod 0 = 3 := rfl
      refine ⟨(hhpMod 0 * 1 + 1) ::ₘ {hhpMod 0 * (q - 1) + 1}, ?_, by simp, ?_⟩
      · intro a ha
        simp only [Multiset.mem_cons, Multiset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact Or.inr (hhpMod_mul_add_mem_hhpProg (by omega) (by omega))
        · exact Or.inr (hhpMod_mul_add_mem_hhpProg (by omega) (by omega))
      · simp [hM0] at hn_eq ⊢
        omega
    | succ m =>
      have hr_sub : r - 2 ^ (m + 1) < 2 ^ (m + 1 + 1) := by
        rw [pow_succ (2 : ℕ) (m + 1)]
        omega
      obtain ⟨u, b₀, hu, hb₀, hr_eq⟩ :=
        exists_subset_hhpCore_for_lt_two_pow (m + 1) (r - 2 ^ (m + 1)) hr_sub
      refine ⟨(hhpMod (m + 1) * q + b₀) ::ₘ (2 ^ (m + 1)) ::ₘ u.val, ?_, ?_, ?_⟩
      · intro a ha
        rcases Multiset.mem_cons.1 ha with rfl | ha
        · exact Or.inr (hhpMod_mul_add_mem_hhpProg (by omega) hb₀)
        · rcases Multiset.mem_cons.1 ha with rfl | ha
          · exact Or.inl (two_pow_succ_mem_hhpCore_succ m)
          · exact Or.inl (hu ha)
      · rw [Multiset.card_cons, Multiset.card_cons, ← Finset.card_def]
        have hucard : u.card ≤ m + 1 :=
          (Finset.card_le_card hu).trans (hhpCore_card (m + 1)).le
        omega
      · rw [Multiset.sum_cons, Multiset.sum_cons, Finset.sum_val]
        simp only [id_eq]
        omega

/-- `hhpSet m` has exact unrestricted order `m + 2`. -/
theorem hhpSet_hasOrder (m : ℕ) : HasExactOrder (hhpSet m) (m + 2) :=
  ⟨hhpSet_isAddBasisOfOrderLE m, fun k hk hA =>
    hhpSet_not_isAddBasisOfOrderLE m (isAddBasisOfOrderLE_mono hA (by omega))⟩

/-- Shifted progression Finset of `j` distinct elements `≡ 1 (mod hhpMod m)`. -/
def hhpProgFinset (m Q j : ℕ) : Finset ℕ :=
  (Finset.range j).image (fun i => hhpMod m * (Q + i + 1) + 1)

lemma hhpProgFinset_injOn (m Q j : ℕ) :
    Set.InjOn (fun i : ℕ => hhpMod m * (Q + i + 1) + 1) ↑(Finset.range j) := by
  intro x _ y _ hxy
  have hM := hhpMod_three_le m
  nlinarith

lemma hhpProgFinset_card (m Q j : ℕ) : (hhpProgFinset m Q j).card = j := by
  unfold hhpProgFinset
  rw [Finset.card_image_of_injOn (hhpProgFinset_injOn m Q j), Finset.card_range]

lemma hhpProgFinset_mem_bounds {m Q j x : ℕ} (hx : x ∈ hhpProgFinset m Q j) :
    x ∈ hhpProg m ∧ hhpMod m * (Q + 1) < x ∧ x ≤ hhpMod m * (Q + j) + 1 := by
  unfold hhpProgFinset at hx
  rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
  rw [Finset.mem_range] at hi
  have hM := hhpMod_three_le m
  refine ⟨hhpMod_mul_add_mem_hhpProg (by omega) (by omega), by nlinarith, by nlinarith⟩

lemma hhpProgFinset_notMem_succ (m Q j : ℕ) :
    hhpMod m * (Q + j + 1) + 1 ∉ hhpProgFinset m Q j := by
  intro hx
  obtain ⟨-, -, hle⟩ := hhpProgFinset_mem_bounds hx
  have hM := hhpMod_three_le m
  nlinarith

lemma hhpProgFinset_sum_decomp (m Q j : ℕ) :
    ∃ K ≤ j * (Q + j + 1), ∑ x ∈ hhpProgFinset m Q j, x = hhpMod m * K + j := by
  induction j with
  | zero => exact ⟨0, by simp, by simp [hhpProgFinset]⟩
  | succ j ih =>
    obtain ⟨K, hK, hsum⟩ := ih
    have hins : hhpProgFinset m Q (j + 1) =
        insert (hhpMod m * (Q + j + 1) + 1) (hhpProgFinset m Q j) := by
      unfold hhpProgFinset
      rw [Finset.range_add_one, Finset.image_insert]
    rw [hins, Finset.sum_insert (hhpProgFinset_notMem_succ m Q j), hsum]
    refine ⟨K + (Q + j + 1), by nlinarith, by ring⟩

/-- `hhpSet m` is a restricted basis of order at most `2 ^ m + m + 1`. -/
theorem hhpSet_isRestrictedBasisOfOrderLE (m : ℕ) :
    IsRestrictedBasisOfOrderLE (hhpSet m) (2 ^ m + m + 1) := by
  set B := (2 ^ m + 2) * (2 ^ m + 2) with hB
  refine Filter.eventually_atTop.2 ⟨hhpMod m * B, fun n hn => ?_⟩
  have hM3 := hhpMod_three_le m
  set r := n % hhpMod m with hr
  set q := n / hhpMod m with hq
  have hn_eq : n = hhpMod m * q + r := (Nat.div_add_mod n (hhpMod m)).symm
  have hr_lt : r < 3 * 2 ^ m := by
    have : r < hhpMod m := Nat.mod_lt n (by omega)
    simpa [hhpMod] using this
  have hq_ge : B ≤ q := by
    have hr_le : r < hhpMod m := Nat.mod_lt n (by omega)
    nlinarith
  have hpos2 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by omega)
  have hB1 : 4 ≤ B := by nlinarith
  by_cases hlt : r < 2 ^ (m + 1)
  · obtain ⟨u, b₀, hu, hb₀, hr_eq⟩ := exists_subset_hhpCore_for_lt_two_pow m r hlt
    set z := hhpMod m * q + b₀ with hz
    have hz_not : z ∉ u := by
      intro hzu
      have hlt_mod : z < hhpMod m := hhpCore_lt_hhpMod (hu hzu)
      nlinarith
    refine ⟨insert z u, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hxu
      · exact Or.inr (hhpMod_mul_add_mem_hhpProg (by omega) hb₀)
      · exact Or.inl (hu hxu)
    · rw [Finset.card_insert_of_notMem hz_not]
      have hucard : u.card ≤ m := (Finset.card_le_card hu).trans (hhpCore_card m).le
      omega
    · rw [Finset.sum_insert hz_not]
      omega
  · set j := r - (2 ^ (m + 1) - 1) with hj
    have hj_le : j ≤ 2 ^ m := by
      have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      omega
    obtain ⟨K, hK, hPsum⟩ := hhpProgFinset_sum_decomp m 0 j
    have hK_lt : K + j + 2 ≤ q := by
      have h1 : j * (0 + j + 1) + j + 2 ≤ (2 ^ m + 2) * (2 ^ m + 2) := by nlinarith
      omega
    set z := hhpMod m * (q - K) + 1 with hz
    set s0 := hhpCore m ∪ hhpProgFinset m 0 j with hs0
    have hdisj : Disjoint (hhpCore m) (hhpProgFinset m 0 j) := by
      rw [Finset.disjoint_left]
      intro x hxCore hxProg
      have h1 := hhpCore_lt_hhpMod hxCore
      obtain ⟨-, h2, -⟩ := hhpProgFinset_mem_bounds hxProg
      omega
    have hz_not : z ∉ s0 := by
      intro hzs
      rcases Finset.mem_union.1 hzs with hzCore | hzProg
      · have h1 := hhpCore_lt_hhpMod hzCore
        have hqK : 1 ≤ q - K := by omega
        nlinarith
      · obtain ⟨-, -, h2⟩ := hhpProgFinset_mem_bounds hzProg
        have hqK : j + 1 ≤ q - K := by omega
        nlinarith
    refine ⟨insert z s0, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hxs0
      · exact Or.inr (hhpMod_mul_add_mem_hhpProg (by omega) (by omega))
      · rcases Finset.mem_union.1 hxs0 with hxCore | hxProg
        · exact Or.inl hxCore
        · exact Or.inr (hhpProgFinset_mem_bounds hxProg).1
    · rw [Finset.card_insert_of_notMem hz_not, Finset.card_union_of_disjoint hdisj,
        hhpCore_card, hhpProgFinset_card]
      omega
    · rw [Finset.sum_insert hz_not, Finset.sum_union hdisj, hhpCore_sum, hPsum]
      have hpos_m1 : 2 ≤ 2 ^ (m + 1) := by rw [pow_succ]; omega
      have hsub : hhpMod m * K + hhpMod m * (q - K) = hhpMod m * q := by
        rw [← Nat.mul_add, Nat.add_sub_of_le (by omega)]
      omega

/-- `hhpSet m` has exact restricted order `2 ^ m + m + 1`. -/
theorem hhpSet_hasRestrictedOrder (m : ℕ) :
    HasExactRestrictedOrder (hhpSet m) (2 ^ m + m + 1) :=
  ⟨hhpSet_isRestrictedBasisOfOrderLE m, fun k hk hA =>
    hhpSet_not_isRestrictedBasisOfOrderLE m (isRestrictedBasisOfOrderLE_mono hA (by omega))⟩
/-! ## Bridges to the Formal Conjectures order definitions -/

/-! The definitions `HasOrder`, `HasRestrictedOrder`, `basisOrder`, and `restrictedOrder` below
match the Formal Conjectures file for Erdős Problem 338 exactly. The lemmas after them convert an
exact-order statement (`HasExactOrder`, `HasExactRestrictedOrder`) into the value of `basisOrder`
or `restrictedOrder`, so the final theorem only needs the two exact-order facts for `hhpSet`. -/

/-- `HasOrder A h` means that `A` is a basis of order at most `h`: every sufficiently large
natural number is a sum of at most `h` elements of `A`, with repetition allowed. -/
def HasOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ h ∧ S.sum = m

/-- `HasRestrictedOrder A t` means that every sufficiently large natural number is a sum of at
most `t` distinct elements of `A`. -/
def HasRestrictedOrder (A : Set ℕ) (t : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ t ∧ ∑ x ∈ S, x = m

/-- The order of `A`: the least `h` with `HasOrder A h`, or `⊤` if `A` is not a basis. -/
noncomputable def basisOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (h : ℕ) (_ : HasOrder A h), (h : ℕ∞)

/-- The restricted order of `A`: the least `t` with `HasRestrictedOrder A t`, or `⊤` if no such `t`
exists. -/
noncomputable def restrictedOrder (A : Set ℕ) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : HasRestrictedOrder A t), (t : ℕ∞)

/-- The at-most formulation of the restricted order is the predicate
`IsRestrictedBasisOfOrderLE`. -/
theorem hasRestrictedOrder_iff_isRestrictedBasisOfOrderLE (A : Set ℕ) (t : ℕ) :
    HasRestrictedOrder A t ↔ IsRestrictedBasisOfOrderLE A t := by
  unfold HasRestrictedOrder IsRestrictedBasisOfOrderLE
  simp [Set.subset_def]

/-- The least `h` with `HasOrder A h` is the exact order of `A`. -/
theorem basisOrder_eq_of_hasExactOrder {A : Set ℕ} {k : ℕ} (hk : HasExactOrder A k) :
    basisOrder A = (k : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · calc basisOrder A ≤ ⨅ (_ : HasOrder A k), (k : ℕ∞) := iInf_le _ k
      _ ≤ (k : ℕ∞) := iInf_le _ hk.1
  · refine le_iInf fun h => le_iInf fun hh => ?_
    have hk_le : k ≤ h := by
      by_contra hlt
      exact hk.2 h (by omega) hh
    exact_mod_cast hk_le

/-- The least `t` with `HasRestrictedOrder A t` is the exact restricted order of `A`. -/
theorem restrictedOrder_eq_of_hasExactRestrictedOrder {A : Set ℕ} {t : ℕ}
    (ht : HasExactRestrictedOrder A t) : restrictedOrder A = (t : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · calc restrictedOrder A ≤ ⨅ (_ : HasRestrictedOrder A t), (t : ℕ∞) := iInf_le _ t
      _ ≤ (t : ℕ∞) := iInf_le _ ht.1
  · refine le_iInf fun s => le_iInf fun hs => ?_
    have ht_le : t ≤ s := by
      by_contra hlt
      exact ht.2 s (by omega)
        ((hasRestrictedOrder_iff_isRestrictedBasisOfOrderLE A s).1 hs)
    exact_mod_cast ht_le

/-- The Hegyvári–Hennecart–Plagne bound, in the form stated by Formal Conjectures: for every
`k ≥ 2` there is a basis of order `k` whose restricted order is `2 ^ (k - 2) + k - 1`. -/
theorem hhpSet_basisOrder_and_restrictedOrder :
    ∀ k : ℕ, 2 ≤ k → ∃ A : Set ℕ,
      basisOrder A = k ∧ restrictedOrder A = (2 ^ (k - 2) + k - 1 : ℕ) := by
  intro k hk
  refine ⟨hhpSet (k - 2), ?_, ?_⟩
  · rw [basisOrder_eq_of_hasExactOrder (hhpSet_hasOrder (k - 2))]
    have hk_eq : k - 2 + 2 = k := by omega
    rw [hk_eq]
  · rw [restrictedOrder_eq_of_hasExactRestrictedOrder (hhpSet_hasRestrictedOrder (k - 2))]
    have h : k - 2 + 1 = k - 1 := by omega
    rw [Nat.add_assoc, h, Nat.add_sub_assoc (by omega : 1 ≤ k)]
end Erdos338
