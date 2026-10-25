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

This module was written for this package, independently of the upstream Lean development
cited in THIRD_PARTY.md.
-/

public import Mathlib

@[expose] public section

/-!
# The Erdős–Hajnal finite independent-set theorem

Theorem 2 of Erdős and Hajnal (*Some remarks on set theory. VIII*, Michigan Math. J. 7 (1960),
187–191): for every `n : ℕ` and every family `A : ℝ → Set ℝ` of bounded sets with Lebesgue outer
measure `< 1`, there is a finite independent set of cardinality at least `n`. This is the
unconditional ZFC part of Erdős Problem 501.

The proof uses forward-cutoff exhaustion of intervals by the slices
`boundedCutoffSet A I L M = {x ∈ I | A x ⊆ (-∞, L + M)}`: boundedness makes the union of the
slices exhaust any candidate interval, and outer-measure continuity from below then produces a
slice whose measure exceeds `n`. On `[L, L + n + 1)` the total measure is `n + 1`, while any
`n`-element union `⋃ y ∈ T, A y` has outer measure at most `n`, so some point of the slice lies
outside every `A y`, and adjoining it preserves pairwise independence.

## Main results

* `Erdos501.erdos501_erdosHajnal_finset_in_Ici_of_le_one`: the induction producing `n` points
  above any lower bound `L`.
* `Erdos501.erdos501_erdosHajnal_finset_card_eq`: the exact-cardinality form.
* `Erdos501.erdos501_erdosHajnal_finite`: the right-hand side for every `n`, in the form
  `n ≤ X.card` with `X : Finset ℝ`.

## References

* P. Erdős, A. Hajnal, *Some remarks on set theory. VIII*, Michigan Math. J. 7 (1960), 187–191.
* [erdosproblems.com/501](https://www.erdosproblems.com/501)
-/

open Set MeasureTheory TopologicalSpace
open scoped BigOperators Cardinal ENNReal

namespace Erdos501

/-- The subset of `I` whose forbidden sets `A x` lie strictly below `L + M`. -/
def boundedCutoffSet (A : ℝ → Set ℝ) (I : Set ℝ) (L : ℝ) (M : ℕ) : Set ℝ :=
  {x ∈ I | A x ⊆ Set.Iio (L + (M : ℝ))}

/-- Every bounded subset of `ℝ` is contained in `(-∞, L + M)` for some natural horizon `M : ℕ`. -/
theorem isBounded_subset_Iio_add_nat {s : Set ℝ} (hs : Bornology.IsBounded s) (L : ℝ) :
    ∃ M : ℕ, s ⊆ Set.Iio (L + (M : ℝ)) := by
  obtain ⟨b, hb⟩ := hs.bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt (b - L)
  refine ⟨M, fun x hx => ?_⟩
  rw [mem_Iio]
  have hxb : x ≤ b := hb hx
  linarith

/-- Every forward-cutoff slice `boundedCutoffSet A I L M` is contained in the base set `I`. -/
theorem boundedCutoffSet_subset (A : ℝ → Set ℝ) (I : Set ℝ) (L : ℝ) (M : ℕ) :
    boundedCutoffSet A I L M ⊆ I := by
  intro x hx
  simp only [boundedCutoffSet, mem_sep_iff] at hx
  exact hx.1

/-- Increasing the natural horizon `M` enlarges `boundedCutoffSet A I L M`. -/
theorem boundedCutoffSet_mono (A : ℝ → Set ℝ) (I : Set ℝ) (L : ℝ) :
    Monotone (boundedCutoffSet A I L) := by
  intro M₁ M₂ hM x hx
  simp only [boundedCutoffSet, mem_sep_iff] at hx ⊢
  refine ⟨hx.1, hx.2.trans ?_⟩
  intro y hy
  rw [mem_Iio] at hy ⊢
  have hM_real : (M₁ : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM
  linarith

/-- When every `A x` is bounded, the countable union of `boundedCutoffSet A I L M` over `M : ℕ`
exhausts `I`. -/
theorem iUnion_boundedCutoffSet_eq {A : ℝ → Set ℝ}
    (hA : ∀ x, Bornology.IsBounded (A x)) (I : Set ℝ) (L : ℝ) :
    (⋃ M : ℕ, boundedCutoffSet A I L M) = I := by
  apply Subset.antisymm
  · exact iUnion_subset (fun M => boundedCutoffSet_subset A I L M)
  · intro x hx
    obtain ⟨M, hM⟩ := isBounded_subset_Iio_add_nat (hA x) L
    exact mem_iUnion.mpr ⟨M, hx, hM⟩

/-- Outer-measure continuity from below along the forward-cutoff slices `boundedCutoffSet A I L M`. -/
theorem iSup_volume_boundedCutoffSet {A : ℝ → Set ℝ}
    (hA : ∀ x, Bornology.IsBounded (A x)) (I : Set ℝ) (L : ℝ) :
    (⨆ M : ℕ, volume (boundedCutoffSet A I L M)) = volume I := by
  rw [← (boundedCutoffSet_mono A I L).measure_iUnion, iUnion_boundedCutoffSet_eq hA I L]

/-- Whenever `c < volume I` and every `A x` is bounded, there exists a finite cutoff `M : ℕ`
whose slice `boundedCutoffSet A I L M` has outer measure strictly exceeding `c`. -/
theorem exists_boundedCutoffSet_volume_gt {A : ℝ → Set ℝ}
    (hA : ∀ x, Bornology.IsBounded (A x)) (I : Set ℝ) (L : ℝ) (c : ℝ≥0∞)
    (hc : c < volume I) :
    ∃ M : ℕ, c < volume (boundedCutoffSet A I L M) := by
  rw [← iSup_volume_boundedCutoffSet hA I L] at hc
  exact lt_iSup_iff.mp hc

/-! ### Outer-measure subadditivity and extraction outside forbidden unions -/

/-- Exact Lebesgue measure of the half-open candidate interval `[L, L + n + 1)`. -/
theorem volume_Ico_add_nat_succ (L : ℝ) (n : ℕ) :
    volume (Set.Ico L (L + (n : ℝ) + 1)) = (n : ℝ≥0∞) + 1 := by
  rw [Real.volume_Ico]
  have hsub : L + (n : ℝ) + 1 - L = (n : ℝ) + 1 := by ring
  rw [hsub, ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one, ENNReal.ofReal_natCast,
    ENNReal.ofReal_one]

/-- The half-open candidate interval `[L, L + n + 1)` has measure strictly larger than `n`. -/
theorem nat_lt_volume_Ico_add_nat_succ (L : ℝ) (n : ℕ) :
    (n : ℝ≥0∞) < volume (Set.Ico L (L + (n : ℝ) + 1)) := by
  rw [volume_Ico_add_nat_succ]
  exact ENNReal.lt_add_right (ENNReal.natCast_ne_top n) one_ne_zero

/-- Finite outer-measure subadditivity over `T : Finset ℝ` when every `A x` has outer measure `≤ C`. -/
theorem volume_biUnion_finset_le_card_mul {A : ℝ → Set ℝ} {C : ℝ≥0∞}
    (hAC : ∀ x, volume (A x) ≤ C) (T : Finset ℝ) :
    volume (⋃ y ∈ T, A y) ≤ (T.card : ℝ≥0∞) * C := by
  calc
    volume (⋃ y ∈ T, A y) ≤ ∑ y ∈ T, volume (A y) := measure_biUnion_finset_le T A
    _ ≤ ∑ _y ∈ T, C := Finset.sum_le_sum (fun y _ => hAC y)
    _ = (T.card : ℝ≥0∞) * C := by rw [Finset.sum_const, nsmul_eq_mul]

/-- When every `A x` has outer measure `≤ 1`, the union of `A y` over `y ∈ T` has outer measure
at most `T.card`. -/
theorem volume_biUnion_finset_le_card {A : ℝ → Set ℝ}
    (hA1 : ∀ x, volume.toOuterMeasure (A x) ≤ 1) (T : Finset ℝ) :
    volume (⋃ y ∈ T, A y) ≤ (T.card : ℝ≥0∞) := by
  have hvol : ∀ x, volume (A x) ≤ 1 := hA1
  simpa using volume_biUnion_finset_le_card_mul hvol T

/-- Whenever `volume B` strictly exceeds `volume (⋃ y ∈ T, A y)`, there exists a point `x ∈ B`
avoiding `A y` for every `y ∈ T`. -/
theorem exists_mem_not_mem_biUnion_of_volume_gt {A : ℝ → Set ℝ} {B : Set ℝ} {T : Finset ℝ}
    (hgt : volume (⋃ y ∈ T, A y) < volume B) :
    ∃ x ∈ B, ∀ y ∈ T, x ∉ A y := by
  by_contra hcon
  have hsub : B ⊆ ⋃ y ∈ T, A y := by
    intro x hx
    by_contra hxnot
    rw [mem_iUnion₂] at hxnot
    exact hcon ⟨x, hx, fun y hyT hxAy => hxnot ⟨y, hyT, hxAy⟩⟩
  exact (not_le_of_gt hgt) (measure_mono hsub)

/-! ### The inductive Erdős–Hajnal construction -/

/-- Forward separation lemma: if `x ∈ boundedCutoffSet A I L M` and `L + M ≤ y`, then `y ∉ A x`. -/
theorem not_mem_of_mem_boundedCutoffSet_of_le {A : ℝ → Set ℝ} {I : Set ℝ} {L : ℝ} {M : ℕ}
    {x y : ℝ} (hx : x ∈ boundedCutoffSet A I L M) (hy : L + (M : ℝ) ≤ y) :
    y ∉ A x := by
  intro hyAx
  have hlt : y < L + (M : ℝ) := hx.2 hyAx
  linarith

/-- Inductive insertion lemma: adjoining `x₀ ∈ boundedCutoffSet A I L M` to a pairwise-independent
`Finset ℝ` `T ⊆ [L + M, ∞)` when `x₀` avoids `⋃ y ∈ T, A y` preserves pairwise independence. -/
theorem pairwise_insert_of_mem_boundedCutoffSet {A : ℝ → Set ℝ} {I : Set ℝ} {L : ℝ} {M : ℕ}
    {T : Finset ℝ} {x₀ : ℝ}
    (hT : (T : Set ℝ).Pairwise (fun x y => x ∉ A y))
    (hx₀ : x₀ ∈ boundedCutoffSet A I L M)
    (hT_ge : ∀ y ∈ T, L + (M : ℝ) ≤ y)
    (hx₀_avoid : ∀ y ∈ T, x₀ ∉ A y) :
    ((insert x₀ T : Finset ℝ) : Set ℝ).Pairwise (fun x y => x ∉ A y) := by
  rw [Finset.coe_insert, Set.pairwise_insert]
  refine ⟨hT, fun y hy _ => ⟨hx₀_avoid y hy, ?_⟩⟩
  exact not_mem_of_mem_boundedCutoffSet_of_le hx₀ (hT_ge y hy)

/-! ### Unconditional finite independent sets -/

/-- Main inductive Erdős–Hajnal theorem on `[L, ∞)`: for every `n : ℕ`, every bounded family `A`
with Lebesgue outer measure `≤ 1`, and every lower bound `L : ℝ`, there exists a pairwise-independent
`Finset ℝ` of cardinality `n` contained in `[L, ∞)`. -/
theorem erdos501_erdosHajnal_finset_in_Ici_of_le_one (n : ℕ) {A : ℝ → Set ℝ}
    (hA : ∀ x, Bornology.IsBounded (A x))
    (hA1 : ∀ x, volume.toOuterMeasure (A x) ≤ 1) (L : ℝ) :
    ∃ X : Finset ℝ, X.card = n ∧ (∀ x ∈ X, L ≤ x) ∧
      (X : Set ℝ).Pairwise (fun x y => x ∉ A y) := by
  induction n generalizing L with
  | zero =>
    refine ⟨∅, Finset.card_empty, ?_, ?_⟩
    · intro x hx
      simp at hx
    · simp
  | succ n ih =>
    set I : Set ℝ := Set.Ico L (L + (n : ℝ) + 1)
    have hI_gt : (n : ℝ≥0∞) < volume I := nat_lt_volume_Ico_add_nat_succ L n
    obtain ⟨M, hM⟩ := exists_boundedCutoffSet_volume_gt hA I L (n : ℝ≥0∞) hI_gt
    set L_next : ℝ := max (L + (n : ℝ) + 1) (L + (M : ℝ))
    obtain ⟨T, hTcard, hTge, hTpair⟩ := ih L_next
    have hU_le : volume (⋃ y ∈ T, A y) ≤ (n : ℝ≥0∞) := by
      rw [← hTcard]
      exact volume_biUnion_finset_le_card hA1 T
    have hU_lt : volume (⋃ y ∈ T, A y) < volume (boundedCutoffSet A I L M) :=
      lt_of_le_of_lt hU_le hM
    obtain ⟨x₀, hx₀B, hx₀_avoid⟩ := exists_mem_not_mem_biUnion_of_volume_gt hU_lt
    have hx₀I : x₀ ∈ I := boundedCutoffSet_subset A I L M hx₀B
    rw [mem_Ico] at hx₀I
    have hx₀_not_mem_T : x₀ ∉ T := by
      intro hx₀T
      have hge : L_next ≤ x₀ := hTge x₀ hx₀T
      have h1 : L + (n : ℝ) + 1 ≤ L_next := le_max_left _ _
      linarith [hx₀I.2]
    refine ⟨insert x₀ T, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hx₀_not_mem_T, hTcard]
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact hx₀I.1
      · have hge : L_next ≤ x := hTge x hxT
        have h1 : L + (n : ℝ) + 1 ≤ L_next := le_max_left _ _
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
    · refine pairwise_insert_of_mem_boundedCutoffSet hTpair hx₀B ?_ hx₀_avoid
      intro y hy
      exact le_trans (le_max_right _ _) (hTge y hy)

/-- **Erdős–Hajnal (1960), Theorem 2 (exact cardinality form):**
For every `n : ℕ` and every family `A : ℝ → Set ℝ` of bounded sets with Lebesgue outer measure
`< 1`, there exists a `Finset ℝ` of cardinality `n` that is pairwise independent for `A`. -/
theorem erdos501_erdosHajnal_finset_card_eq (n : ℕ) (A : ℝ → Set ℝ)
    (hA : ∀ x, Bornology.IsBounded (A x))
    (hA1 : ∀ x, volume.toOuterMeasure (A x) < 1) :
    ∃ X : Finset ℝ, X.card = n ∧ (X : Set ℝ).Pairwise (fun x y => x ∉ A y) := by
  obtain ⟨X, hcard, _, hpair⟩ :=
    erdos501_erdosHajnal_finset_in_Ici_of_le_one n hA (fun x => (hA1 x).le) 0
  exact ⟨X, hcard, hpair⟩

/-- **Erdős–Hajnal (1960), Theorem 2 (`erdos_501.variants.erdosHajnal_finite`):**
The exact right-hand side of `erdos_501.variants.erdosHajnal_finite` in
`FormalConjectures/ErdosProblems/501.lean`. -/
theorem erdos501_erdosHajnal_finite (n : ℕ) (A : ℝ → Set ℝ)
    (hA : ∀ x, Bornology.IsBounded (A x))
    (hA1 : ∀ x, volume.toOuterMeasure (A x) < 1) :
    ∃ X : Finset ℝ, n ≤ X.card ∧ (X : Set ℝ).Pairwise (fun x y => x ∉ A y) := by
  obtain ⟨X, hcard, hpair⟩ := erdos501_erdosHajnal_finset_card_eq n A hA hA1
  exact ⟨X, hcard.symm.le, hpair⟩

end Erdos501
