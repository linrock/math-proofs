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

/-!
# Sum-avoiding subsets of a finite set

This module defines the restricted sumset, the predicate that a finite set is
sum-avoiding in an ambient set, and the maximum size of such a subset. It also
records the invariance of that maximum under injective additive maps, which is
used to transfer the positive-real bound to the negative reals.
-/

public section

open Set Finset

namespace Finset

variable {α : Type*} [Add α] [DecidableEq α]

/--
The restricted sumset of a set $S$, denoted $S \hat{+} S$, is the set
$\lbrace s_1 + s_2 : s_1, s_2 \in S, s_1 \neq s_2 \rbrace$.
-/
@[expose]
def restrictedSumset (S : Finset α) : Finset α :=
  S.offDiag.image (fun p => p.1 + p.2)

end Finset

namespace Erdos787

/-- `B` is contained in `A`, and no sum of two distinct elements of `B` lies in `A`. -/
@[expose]
def IsSumAvoidingIn {α : Type*} [Add α] (A B : Finset α) : Prop :=
  B ⊆ A ∧ ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ ∉ A

/-- The largest cardinality of a sum-avoiding subset of `A`. -/
@[expose]
noncomputable def maxSumAvoidingCard {α : Type*} [Add α] [DecidableEq α]
    (A : Finset α) : ℕ :=
  sSup (Set.image (fun T : Finset α => T.card)
    {T : Finset α | T ⊆ A ∧ IsSumAvoidingIn A T})

theorem isSumAvoidingIn_empty {α : Type*} [Add α] (A : Finset α) :
    IsSumAvoidingIn A ∅ :=
  ⟨Finset.empty_subset _, by simp⟩

theorem card_le_maxSumAvoidingCard {α : Type*} [Add α] [DecidableEq α] {A B : Finset α}
    (hB : IsSumAvoidingIn A B) : B.card ≤ maxSumAvoidingCard A := by
  refine le_csSup (bddAbove_def.2 ⟨A.card, fun m hm => ?_⟩)
    (Set.mem_image_of_mem (fun T : Finset α => T.card)
      (Set.mem_ofPred_eq.mpr ⟨hB.1, hB⟩))
  obtain ⟨B', hB', rfl⟩ := hm
  exact Finset.card_le_card hB'.1

theorem exists_isSumAvoidingIn_card_eq_maxSumAvoidingCard {α : Type*} [Add α] [DecidableEq α]
    (A : Finset α) : ∃ B : Finset α, IsSumAvoidingIn A B ∧ B.card = maxSumAvoidingCard A := by
  have hnonempty : (({T : Finset α | T ⊆ A ∧ IsSumAvoidingIn A T}).image
      (fun T : Finset α => T.card)).Nonempty :=
    ⟨0, ∅, Set.mem_ofPred_eq.mpr ⟨(isSumAvoidingIn_empty A).1, isSumAvoidingIn_empty A⟩, rfl⟩
  have hfinite : (({T : Finset α | T ⊆ A ∧ IsSumAvoidingIn A T}).image
      (fun T : Finset α => T.card)).Finite := by
    refine Set.Finite.image _ (Set.Finite.subset (Set.toFinite ((A.powerset :
      Finset (Finset α)) : Set (Finset α))) ?_)
    intro T hT
    exact Finset.mem_powerset.mpr hT.1
  have hmem : maxSumAvoidingCard A ∈ Set.image (fun T : Finset α => T.card)
      {T : Finset α | T ⊆ A ∧ IsSumAvoidingIn A T} :=
    Set.Nonempty.csSup_mem hnonempty hfinite
  obtain ⟨B, hB, hcard⟩ := hmem
  exact ⟨B, hB.2, hcard⟩

theorem isSumAvoidingIn_image_iff_of_add_injective {α β : Type*} [Add α] [Add β]
    [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (hadd : ∀ x y, f (x + y) = f x + f y) (A B : Finset α) :
    IsSumAvoidingIn (A.image f) (B.image f) ↔ IsSumAvoidingIn A B := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx
      have hfx : f x ∈ A.image f := h.1 (Finset.mem_image_of_mem f hx)
      rcases Finset.mem_image.mp hfx with ⟨y, hy, hfy⟩
      exact hf hfy ▸ hy
    · intro b₁ hb₁ b₂ hb₂ hne hsum
      have hne_f : f b₁ ≠ f b₂ := fun heq => hne (hf heq)
      have hmem_f : f b₁ + f b₂ ∈ A.image f := by
        rw [← hadd]
        exact Finset.mem_image_of_mem f hsum
      exact h.2 (f b₁) (Finset.mem_image_of_mem f hb₁) (f b₂) (Finset.mem_image_of_mem f hb₂)
        hne_f hmem_f
  · intro h
    refine ⟨Finset.image_subset_image h.1, ?_⟩
    intro y₁ hy₁ y₂ hy₂ hne hsum
    rcases Finset.mem_image.mp hy₁ with ⟨b₁, hb₁, rfl⟩
    rcases Finset.mem_image.mp hy₂ with ⟨b₂, hb₂, rfl⟩
    have hne_b : b₁ ≠ b₂ := fun heq => hne (heq ▸ rfl)
    rw [← hadd] at hsum
    rcases Finset.mem_image.mp hsum with ⟨a, ha, hfa⟩
    exact h.2 b₁ hb₁ b₂ hb₂ hne_b (hf hfa ▸ ha)

theorem maxSumAvoidingCard_image_eq_of_add_injective {α β : Type*} [Add α] [Add β]
    [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (hadd : ∀ x y, f (x + y) = f x + f y) (A : Finset α) :
    maxSumAvoidingCard (A.image f) = maxSumAvoidingCard A := by
  apply le_antisymm
  · obtain ⟨B', hB', hB'card⟩ := exists_isSumAvoidingIn_card_eq_maxSumAvoidingCard (A.image f)
    have hsub : B' ⊆ A.image f := hB'.1
    have hB_img : (A.filter (fun x => f x ∈ B')).image f = B' := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hfy⟩, rfl⟩
        exact hfy
      · intro hy
        rcases Finset.mem_image.mp (hsub hy) with ⟨x, hxA, rfl⟩
        exact ⟨x, ⟨hxA, hy⟩, rfl⟩
    have hB_sa : IsSumAvoidingIn A (A.filter (fun x => f x ∈ B')) := by
      apply (isSumAvoidingIn_image_iff_of_add_injective f hf hadd A
        (A.filter (fun x => f x ∈ B'))).mp
      rw [hB_img]
      exact hB'
    have hcard_eq : (A.filter (fun x => f x ∈ B')).card = B'.card := by
      conv_rhs => rw [← hB_img]
      rw [Finset.card_image_of_injective (A.filter (fun x => f x ∈ B')) hf]
    calc maxSumAvoidingCard (A.image f) = B'.card := hB'card.symm
      _ = (A.filter (fun x => f x ∈ B')).card := hcard_eq.symm
      _ ≤ maxSumAvoidingCard A := card_le_maxSumAvoidingCard hB_sa
  · obtain ⟨B, hB, hBcard⟩ := exists_isSumAvoidingIn_card_eq_maxSumAvoidingCard A
    have hB_img : IsSumAvoidingIn (A.image f) (B.image f) :=
      (isSumAvoidingIn_image_iff_of_add_injective f hf hadd A B).mpr hB
    have hle := card_le_maxSumAvoidingCard hB_img
    rwa [Finset.card_image_of_injective B hf, hBcard] at hle

end Erdos787
