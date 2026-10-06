module

public import GallaiColorBound

@[expose] public section

namespace ErdosProblems.AntiRamseyWeakCount

open Finset SimpleGraph
open ErdosProblems.AntiRamseyTriangle

/-- The vertices in one class of a finite block map. -/
def blockFiber {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (b : V → Fin t) (i : Fin t) : Finset V :=
  Finset.univ.filter fun v => b v = i

theorem edgeColors_card_le_choose {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (χ : TopEdgeLabeling V C) (S : Finset V) :
    (edgeColors χ S).card ≤ S.card.choose 2 := by
  let E : Finset (⊤ : SimpleGraph V).edgeSet :=
    (Finset.univ : Finset (⊤ : SimpleGraph V).edgeSet).filter
      (fun e => e.val.toFinset ⊆ S)
  have hEsub : E.image Subtype.val ⊆
      ((⊤ : SimpleGraph V).edgeFinset.filter fun e => e.toFinset ⊆ S) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, he'S⟩ := Finset.mem_filter.mp he'
    exact Finset.mem_filter.mpr ⟨by simpa using e'.property, he'S⟩
  have hEcard : E.card = (E.image Subtype.val).card :=
    (Finset.card_image_of_injective E Subtype.coe_injective).symm
  calc
    (edgeColors χ S).card = (E.image χ).card := rfl
    _ ≤ E.card := Finset.card_image_le
    _ ≤ ((⊤ : SimpleGraph V).edgeFinset.filter fun e => e.toFinset ⊆ S).card := by
      rw [hEcard]
      exact Finset.card_le_card hEsub
    _ = ((⊤ : SimpleGraph V).induce (↑S : Set V)).edgeFinset.card :=
      (⊤ : SimpleGraph V).card_filter_edgeFinset_toFinset_subset S
    _ ≤ S.card.choose 2 := by
      simpa [Fintype.card_subtype] using
        ((⊤ : SimpleGraph V).induce (↑S : Set V)).card_edgeFinset_le_card_choose_two

/-- An edge coloring with monochromatic pairs of blocks and at most two cross colors
on every triple of blocks uses at most the possible internal edges plus `t - 1` colors.
The quotient coloring `ψ` assigns the color of each pair of distinct blocks;
`NoRainbowTriangle ψ` is precisely the triple condition. Empty fibers are allowed. -/
theorem realized_colors_le_block_edges_add {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    {t : ℕ} (χ : TopEdgeLabeling V C) (b : V → Fin t)
    (ψ : TopEdgeLabeling (Fin t) C)
    (hcross : ∀ (a d : V) (had : a ≠ d) (hbd : b a ≠ b d),
      χ.get a d had = ψ.get (b a) (b d) hbd)
    (htriple : NoRainbowTriangle ψ) :
    (Finset.univ.image χ).card ≤
      (∑ i : Fin t, (blockFiber b i).card.choose 2) + (t - 1) := by
  let Q : Finset C := Finset.univ.image ψ
  let I : Fin t → Finset C := fun i => edgeColors χ (blockFiber b i)
  have hcover : edgeColors χ (Finset.univ : Finset V) ⊆
      Q ∪ Finset.univ.biUnion I := by
    intro c hc
    obtain ⟨a, _, d, _, had, hcolor⟩ :=
      (mem_edgeColors_iff χ (Finset.univ : Finset V) c).mp hc
    by_cases hbd : b a = b d
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨b a, Finset.mem_univ _, ?_⟩
      apply (mem_edgeColors_iff χ (blockFiber b (b a)) c).mpr
      exact ⟨a, by simp [blockFiber], d, by simp [blockFiber, hbd], had, hcolor⟩
    · apply Finset.mem_union_left
      let e : (⊤ : SimpleGraph (Fin t)).edgeSet :=
        ⟨s(b a, b d), by simpa using hbd⟩
      have hq : ψ.get (b a) (b d) hbd ∈ Q := by
        exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
      rw [← hcolor, hcross a d had hbd]
      exact hq
  have hinternal : ∀ i : Fin t, (I i).card ≤ (blockFiber b i).card.choose 2 := by
    intro i
    exact edgeColors_card_le_choose χ (blockFiber b i)
  have hQ : Q.card ≤ t - 1 := by
    simpa [Q] using gallai_color_bound ψ htriple
  have hall : edgeColors χ (Finset.univ : Finset V) = Finset.univ.image χ := by
    simp [edgeColors]
  calc
    (Finset.univ.image χ).card = (edgeColors χ (Finset.univ : Finset V)).card := by
      rw [hall]
    _ ≤ (Q ∪ Finset.univ.biUnion I).card := Finset.card_le_card hcover
    _ ≤ Q.card + (Finset.univ.biUnion I).card := Finset.card_union_le _ _
    _ ≤ Q.card + ∑ i : Fin t, (I i).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (t - 1) + ∑ i : Fin t, (blockFiber b i).card.choose 2 :=
      Nat.add_le_add hQ (Finset.sum_le_sum fun i _ => hinternal i)
    _ = (∑ i : Fin t, (blockFiber b i).card.choose 2) + (t - 1) :=
      Nat.add_comm _ _

end ErdosProblems.AntiRamseyWeakCount
