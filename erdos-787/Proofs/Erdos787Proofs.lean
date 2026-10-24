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
public import Erdos787Base

/-!
# Erdős Problem 787: the logarithmic restricted sum-free bound

The argument peels the largest element from the positive or negative part of a
finite set of reals. Each peeling step either keeps an element or charges it to
a distinct larger element of the ambient set, which gives a halving invariant.
This yields $\lfloor \log_2 |P| \rfloor + 1$ on each same-sign part, and hence
the logarithmic lower bound for the unrestricted function $g$ on $\mathbb{R}$.
-/

open Filter
open scoped Topology

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace Erdos787

/-- `g G n` is the largest `m` such that every `n`-element subset `A` of `G` has a
subset `B` with `|B| ≥ m` and `Disjoint B.restrictedSumset A`. -/
noncomputable def g (G : Type*) [Add G] [DecidableEq G] (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset G, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A}

end Erdos787

namespace Erdos787Proofs

/-! ## Relating the two formulations -/

/-- Disjointness of a restricted sumset from `A` means that no sum of two distinct
elements of `B` lies in `A`. -/
theorem disjoint_restrictedSumset_iff {G : Type*} [Add G] [DecidableEq G] (A B : Finset G) :
    Disjoint B.restrictedSumset A ↔ ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ ∉ A := by
  unfold Finset.restrictedSumset
  rw [Finset.disjoint_left]
  constructor
  · intro h b₁ hb₁ b₂ hb₂ hne hmem
    have hmem' : b₁ + b₂ ∈ Finset.image (fun p : G × G => p.1 + p.2) B.offDiag :=
      Finset.mem_image.2 ⟨(b₁, b₂), Finset.mem_offDiag.2 ⟨hb₁, hb₂, hne⟩, rfl⟩
    exact h hmem' hmem
  · intro h x hx hxA
    obtain ⟨⟨b₁, b₂⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hb₁, hb₂, hne⟩ := Finset.mem_offDiag.1 hp
    exact h b₁ hb₁ b₂ hb₂ hne hxA

/-- If every `n`-element set of reals has a subset of size at least `m` with
restricted sumset disjoint from the ambient set, then `m ≤ g ℝ n`. -/
theorem le_g {n m : ℕ} (h : ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) :
    m ≤ Erdos787.g ℝ n := by
  refine le_csSup (bddAbove_def.2 ⟨n, fun m' hm' => ?_⟩) h
  have hm'' : ∀ A : Finset ℝ, A.card = n →
      ∃ B ⊆ A, m' ≤ B.card ∧ Disjoint B.restrictedSumset A := hm'
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ n
  obtain ⟨B, hBA, hmB, -⟩ := hm'' A hA
  exact hmB.trans ((Finset.card_le_card hBA).trans_eq hA)

/-- The pair `B ⊆ A ∧ Disjoint B.restrictedSumset A` is exactly
`Erdos787.IsSumAvoidingIn A B`. -/
theorem isSumAvoidingIn_iff {A B : Finset ℝ} :
    Erdos787.IsSumAvoidingIn A B ↔ B ⊆ A ∧ Disjoint B.restrictedSumset A := by
  rw [disjoint_restrictedSumset_iff]
  constructor
  · rintro ⟨hBA, h⟩
    exact ⟨hBA, fun b₁ hb₁ b₂ hb₂ hne => h b₁ hb₁ b₂ hb₂ hne⟩
  · rintro ⟨hBA, h⟩
    exact ⟨hBA, fun b₁ hb₁ b₂ hb₂ hne => h b₁ hb₁ b₂ hb₂ hne⟩

/-! ## Conflict peeling on a set of positive reals -/

/-- Peeling lemma. For `S ⊆ P` nonempty with `P` consisting of positive reals, writing
`m = max S`, all but at most `|P| - |S|` elements of `S \ {m}` survive the conflict test
`x + m ∉ P`. Consequently the surviving set `S'` satisfies `2|S| ≤ |P| + |S'| + 1`. -/
theorem two_mul_card_le_card_add_card_survivors (P S : Finset ℝ) (hSP : S ⊆ P)
    (hpos : ∀ p ∈ P, 0 < p) (hne : S.Nonempty) :
    2 * S.card ≤ P.card + ((S.erase (S.max' hne)).filter
      (fun x => x + S.max' hne ∉ P)).card + 1 := by
  set m := S.max' hne with hm_def
  have hmS : m ∈ S := Finset.max'_mem S hne
  have hcard_le : S.card ≤ P.card := Finset.card_le_card hSP
  have hsplit := Finset.card_filter_add_card_filter_not (s := S.erase m)
    (p := fun x => x + m ∈ P)
  have her : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
  have hT : ((S.erase m).filter (fun x => x + m ∈ P)).card ≤ P.card - S.card := by
    have hinj : ((S.erase m).filter (fun x => x + m ∈ P)).card ≤
        (P.filter (fun a => m < a)).card := by
      refine Finset.card_le_card_of_injOn (fun x => x + m) ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_erase] at hx ⊢
        obtain ⟨⟨_, hxS⟩, hxP⟩ := hx
        have hxpos : 0 < x := hpos x (hSP hxS)
        exact ⟨hxP, by linarith⟩
      · intro x _ y _ hxy
        linarith
    have hsub : (P.filter (fun a => m < a)) ⊆ P \ S := by
      intro a ha
      simp only [Finset.mem_filter] at ha
      refine Finset.mem_sdiff.mpr ⟨ha.1, fun haS => ?_⟩
      have hle : a ≤ m := Finset.le_max' S a haS
      linarith [ha.2]
    calc ((S.erase m).filter (fun x => x + m ∈ P)).card
        ≤ (P.filter (fun a => m < a)).card := hinj
      _ ≤ (P \ S).card := Finset.card_le_card hsub
      _ = P.card - S.card := Finset.card_sdiff_of_subset hSP
  omega

/-- Greedy halving invariant: if `S ⊆ P` is large enough relative to `P`, then `S` contains a
sum-avoiding-in-`P` subset of size at least `k + 1`. -/
theorem exists_subset_card_of_pow_two_invariant (P : Finset ℝ) (hpos : ∀ p ∈ P, 0 < p) :
    ∀ (k : ℕ) (S : Finset ℝ), S ⊆ P → 2 ^ k * (P.card + 1) ≤ P.card + 2 ^ k * S.card →
      ∃ B ⊆ S, Erdos787.IsSumAvoidingIn P B ∧ k + 1 ≤ B.card := by
  intro k
  induction k with
  | zero =>
    intro S hSP hinv
    have hSpos : 0 < S.card := by
      simp only [pow_zero, Nat.one_mul] at hinv
      omega
    obtain ⟨x, hxS⟩ := Finset.card_pos.mp hSpos
    refine ⟨{x}, Finset.singleton_subset_iff.mpr hxS, ?_, by simp⟩
    refine ⟨Finset.singleton_subset_iff.mpr (hSP hxS), ?_⟩
    intro b₁ hb₁ b₂ hb₂ hne
    simp only [Finset.mem_singleton] at hb₁ hb₂
    exact absurd (hb₁.trans hb₂.symm) hne
  | succ k ih =>
    intro S hSP hinv
    have hpow_pos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have hpow_succ : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    have hSpos : 0 < S.card := by
      by_contra h0
      have hS0 : S.card = 0 := by omega
      rw [hS0, hpow_succ] at hinv
      nlinarith
    have hne : S.Nonempty := Finset.card_pos.mp hSpos
    set m := S.max' hne with hm_def
    have hmS : m ∈ S := Finset.max'_mem S hne
    set S' := (S.erase m).filter (fun x => x + m ∉ P) with hS'_def
    have hS'sub : S' ⊆ S :=
      Finset.Subset.trans (Finset.filter_subset _ _) (Finset.erase_subset m S)
    have hS'P : S' ⊆ P := Finset.Subset.trans hS'sub hSP
    have hstep : 2 * S.card ≤ P.card + S'.card + 1 :=
      two_mul_card_le_card_add_card_survivors P S hSP hpos hne
    have hinv' : 2 ^ k * (P.card + 1) ≤ P.card + 2 ^ k * S'.card := by
      rw [hpow_succ] at hinv
      nlinarith
    obtain ⟨B, hBS', hBsa, hBcard⟩ := ih S' hS'P hinv'
    have hm_not_B : m ∉ B := by
      intro hmB
      have hmem := hBS' hmB
      simp only [hS'_def, Finset.mem_filter, Finset.mem_erase] at hmem
      exact hmem.1.1 rfl
    refine ⟨insert m B, Finset.insert_subset_iff.mpr ⟨hmS, Finset.Subset.trans hBS' hS'sub⟩,
      ?_, ?_⟩
    · refine ⟨Finset.insert_subset_iff.mpr ⟨hSP hmS, hBsa.1⟩, ?_⟩
      intro b₁ hb₁ b₂ hb₂ hne₂ hsum
      rcases Finset.mem_insert.mp hb₁ with rfl | hb₁B
      · rcases Finset.mem_insert.mp hb₂ with rfl | hb₂B
        · exact hne₂ rfl
        · have hmem := hBS' hb₂B
          simp only [hS'_def, Finset.mem_filter] at hmem
          exact hmem.2 (by rwa [add_comm] at hsum)
      · rcases Finset.mem_insert.mp hb₂ with rfl | hb₂B
        · have hmem := hBS' hb₁B
          simp only [hS'_def, Finset.mem_filter] at hmem
          exact hmem.2 hsum
        · exact hBsa.2 b₁ hb₁B b₂ hb₂B hne₂ hsum
    · rw [Finset.card_insert_of_notMem hm_not_B]
      omega

/-- Klarner's bound on a set of positive reals: `⌊log₂ |P|⌋ + 1 ≤ maxSumAvoidingCard P`. -/
theorem log_two_add_one_le_maxSumAvoidingCard_of_pos (P : Finset ℝ)
    (hpos : ∀ p ∈ P, 0 < p) (hne : P.Nonempty) :
    Nat.log 2 P.card + 1 ≤ Erdos787.maxSumAvoidingCard P := by
  have hcard_ne : P.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hne)
  have hpow : 2 ^ Nat.log 2 P.card ≤ P.card := Nat.pow_log_le_self 2 hcard_ne
  have hinv : 2 ^ Nat.log 2 P.card * (P.card + 1) ≤ P.card + 2 ^ Nat.log 2 P.card * P.card := by
    nlinarith
  obtain ⟨B, _, hBsa, hBcard⟩ :=
    exists_subset_card_of_pow_two_invariant P hpos (Nat.log 2 P.card) P (Finset.Subset.refl P) hinv
  exact le_trans hBcard (Erdos787.card_le_maxSumAvoidingCard hBsa)

/-! ## From same-sign subsets to all finite sets of reals -/

/-- A set of positive reals that is sum-avoiding inside `A.filter (0 < ·)` is sum-avoiding
inside `A`. -/
theorem isSumAvoidingIn_of_posPart {A B : Finset ℝ}
    (h : Erdos787.IsSumAvoidingIn (A.filter (fun x => 0 < x)) B) :
    Erdos787.IsSumAvoidingIn A B := by
  refine ⟨Finset.Subset.trans h.1 (Finset.filter_subset _ _), ?_⟩
  intro b₁ hb₁ b₂ hb₂ hne hsum
  have hb₁' : b₁ ∈ A.filter (fun x => 0 < x) := h.1 hb₁
  have hb₂' : b₂ ∈ A.filter (fun x => 0 < x) := h.1 hb₂
  have h1 : 0 < b₁ := (Finset.mem_filter.mp hb₁').2
  have h2 : 0 < b₂ := (Finset.mem_filter.mp hb₂').2
  exact h.2 b₁ hb₁ b₂ hb₂ hne (Finset.mem_filter.mpr ⟨hsum, by linarith⟩)

/-- Same for the negative part. -/
theorem isSumAvoidingIn_of_negPart {A B : Finset ℝ}
    (h : Erdos787.IsSumAvoidingIn (A.filter (fun x => x < 0)) B) :
    Erdos787.IsSumAvoidingIn A B := by
  refine ⟨Finset.Subset.trans h.1 (Finset.filter_subset _ _), ?_⟩
  intro b₁ hb₁ b₂ hb₂ hne hsum
  have hb₁' : b₁ ∈ A.filter (fun x => x < 0) := h.1 hb₁
  have hb₂' : b₂ ∈ A.filter (fun x => x < 0) := h.1 hb₂
  have h1 : b₁ < 0 := (Finset.mem_filter.mp hb₁').2
  have h2 : b₂ < 0 := (Finset.mem_filter.mp hb₂').2
  exact h.2 b₁ hb₁ b₂ hb₂ hne (Finset.mem_filter.mpr ⟨hsum, by linarith⟩)

/-- The greedy bound for the negative part follows from the positive version by negation. -/
theorem log_two_add_one_le_maxSumAvoidingCard_of_neg (N : Finset ℝ)
    (hneg : ∀ p ∈ N, p < 0) (hne : N.Nonempty) :
    Nat.log 2 N.card + 1 ≤ Erdos787.maxSumAvoidingCard N := by
  have hpos : ∀ p ∈ N.image (fun x => -x), 0 < p := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    linarith [hneg x hx]
  have hne' : (N.image (fun x => -x)).Nonempty := hne.image _
  have hmain := log_two_add_one_le_maxSumAvoidingCard_of_pos (N.image (fun x => -x)) hpos hne'
  have hcard : (N.image (fun x => -x)).card = N.card :=
    Finset.card_image_of_injective _ (fun x y hxy => by simpa using hxy)
  have hmax : Erdos787.maxSumAvoidingCard (N.image (fun x => -x)) =
      Erdos787.maxSumAvoidingCard N :=
    Erdos787.maxSumAvoidingCard_image_eq_of_add_injective (fun x : ℝ => -x)
      (fun x y hxy => by simpa using hxy) (fun x y => by simp [add_comm]) N
  rwa [hcard, hmax] at hmain

/-- Sign splitting: the cardinality of `A` is controlled by its positive and negative parts. -/
theorem card_le_posPart_add_negPart_add_one (A : Finset ℝ) :
    A.card ≤ (A.filter (fun x => 0 < x)).card + (A.filter (fun x => x < 0)).card + 1 := by
  set P := A.filter (fun x => 0 < x) with hP
  set N := A.filter (fun x => x < 0) with hN
  have hcover : A ⊆ (P ∪ N) ∪ ({0} : Finset ℝ) := by
    intro x hx
    rcases lt_trichotomy x 0 with h | h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hx, h⟩))))
    · subst h; exact Finset.mem_union.mpr (Or.inr (by simp))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hx, h⟩))))
  have hd : Disjoint P N :=
    Finset.disjoint_filter.mpr fun x _ h1 h2 => absurd h1 (by linarith)
  have h0P : (0 : ℝ) ∉ P := by simp [hP]
  have h0N : (0 : ℝ) ∉ N := by simp [hN]
  have h1 : (P ∪ N).card = P.card + N.card := Finset.card_union_of_disjoint hd
  have h2 : Disjoint ({0} : Finset ℝ) (P ∪ N) := by
    rw [Finset.disjoint_singleton_left, Finset.mem_union, not_or]
    exact ⟨h0P, h0N⟩
  have h3 : ((P ∪ N) ∪ ({0} : Finset ℝ)).card = P.card + N.card + 1 := by
    rw [Finset.union_comm, Finset.card_union_of_disjoint h2, h1, Finset.card_singleton]
    omega
  calc A.card ≤ ((P ∪ N) ∪ ({0} : Finset ℝ)).card := Finset.card_le_card hcover
    _ = P.card + N.card + 1 := h3

/-- Monotonicity of `Nat.log 2` under a factor-8 bound. -/
theorem log_two_le_log_two_add_three {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : n ≤ 8 * m) :
    Nat.log 2 n ≤ Nat.log 2 m + 3 := by
  have h3 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm
  have h4 : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have h5 : n < 2 ^ (Nat.log 2 m + 4) := by
    have he : 2 ^ (Nat.log 2 m + 4) = 16 * 2 ^ Nat.log 2 m := by ring
    have he1 : 2 ^ (Nat.log 2 m + 1) = 2 * 2 ^ Nat.log 2 m := by ring
    omega
  have := Nat.log_lt_of_lt_pow hn h5
  omega

/-- Every finite `A ⊆ ℝ` of cardinality `n` has a sum-avoiding subset of size at least
`⌊log₂ n⌋ - 4`. The loss of four accounts for the constant additive terms in
the same-sign estimates and for splitting into positive, negative, and zero
elements. -/
theorem exists_isSumAvoidingIn_card_ge (A : Finset ℝ) (n : ℕ) (hA : A.card = n) :
    ∃ B ⊆ A, Erdos787.IsSumAvoidingIn A B ∧ Nat.log 2 n ≤ B.card + 4 := by
  rcases Nat.eq_zero_or_pos n with hzero | hnpos
  · subst hzero
    exact ⟨∅, Finset.empty_subset _, Erdos787.isSumAvoidingIn_empty A, by simp⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  set P := A.filter (fun x => 0 < x) with hP
  set N := A.filter (fun x => x < 0) with hN
  have hsplit : n ≤ P.card + N.card + 1 := by
    rw [← hA]; exact card_le_posPart_add_negPart_add_one A
  by_cases hsmall : n ≤ 1
  · refine ⟨∅, Finset.empty_subset _, Erdos787.isSumAvoidingIn_empty A, ?_⟩
    have hn1 : n = 1 := by omega
    subst hn1
    simp
  rcases le_total P.card N.card with hPN | hNP
  · have hN0 : N.card ≠ 0 := by omega
    have hdom : n ≤ 8 * N.card := by rw [Nat.mul_comm]; omega
    obtain ⟨B, hB, hBcard⟩ :=
      Erdos787.exists_isSumAvoidingIn_card_eq_maxSumAvoidingCard N
    have hbound := log_two_add_one_le_maxSumAvoidingCard_of_neg N
      (fun p hp => (Finset.mem_filter.mp hp).2) (Finset.card_pos.mp (by omega))
    have hb : Nat.log 2 N.card + 1 ≤ B.card := by rw [hBcard]; exact hbound
    refine ⟨B, Finset.Subset.trans hB.1 (Finset.filter_subset _ _),
      isSumAvoidingIn_of_negPart hB, ?_⟩
    rw [hBcard]
    have := log_two_le_log_two_add_three hN0 hn0 hdom
    omega
  · have hP0 : P.card ≠ 0 := by omega
    have hdom : n ≤ 8 * P.card := by rw [Nat.mul_comm]; omega
    obtain ⟨B, hB, hBcard⟩ :=
      Erdos787.exists_isSumAvoidingIn_card_eq_maxSumAvoidingCard P
    have hbound := log_two_add_one_le_maxSumAvoidingCard_of_pos P
      (fun p hp => (Finset.mem_filter.mp hp).2) (Finset.card_pos.mp (by omega))
    have hb : Nat.log 2 P.card + 1 ≤ B.card := by rw [hBcard]; exact hbound
    refine ⟨B, Finset.Subset.trans hB.1 (Finset.filter_subset _ _),
      isSumAvoidingIn_of_posPart hB, ?_⟩
    rw [hBcard]
    have := log_two_le_log_two_add_three hP0 hn0 hdom
    omega

/-- The conversion from binary to natural logarithms:
`log n ≤ (log₂ n + 1) log 2`. -/
theorem real_log_le_nat_log_add_one_mul (n : ℕ) (hn : 1 ≤ n) :
    Real.log n ≤ ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
  have hnat : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hreal : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast hnat
  have h1 : Real.log n < Real.log ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
    Real.log_lt_log (by exact_mod_cast hn) hreal
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- Klarner's logarithmic lower bound for the restricted sum-free subset problem.
The constant `1/16` is explicit and the threshold is `n ≥ 1024`. -/
theorem variants.klarner :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ (Erdos787.g ℝ n : ℝ) := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 1024] with n hn
  have hg8 : Nat.log 2 n - 8 ≤ Erdos787.g ℝ n := by
    refine le_g ?_
    intro A hA
    obtain ⟨B, hBA, hsa, hcard⟩ := exists_isSumAvoidingIn_card_ge A n hA
    have : Nat.log 2 n - 8 ≤ B.card := by omega
    exact ⟨B, hBA, this, (isSumAvoidingIn_iff.mp hsa).2⟩
  have hg : Nat.log 2 n ≤ Erdos787.g ℝ n + 8 := by omega
  have hgn : (Nat.log 2 n : ℝ) ≤ (Erdos787.g ℝ n : ℝ) + 8 := by exact_mod_cast hg
  have hlog := real_log_le_nat_log_add_one_mul n (by omega : 1 ≤ n)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1024 : (10 : ℕ) ≤ Nat.log 2 n := by
    have h1 : Nat.log 2 1024 ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
    have h2 : Nat.log 2 1024 = 10 := by norm_num [Nat.log]
    omega
  have hg10 : (10 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast h1024
  have hexp : 1 / 16 * Real.log n ≤ (Erdos787.g ℝ n : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
    nlinarith
  exact hexp

end Erdos787Proofs
