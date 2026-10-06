module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Defs
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Half-size alternation under an actual permutation

This finite-set lemma is an index-set step for an actual
even cycle. It assumes neither a complementary half nor a parity description. It makes no assertion about graph neighbors, cycle chords, or a graph cover.
-/

namespace ErdosProblems.PathUpperReduction.CycleHalfAlternation1105

/-- An independent half-sized set under a permutation fills exactly one half
of the carrier, and the permutation interchanges membership and nonmembership.
The disjointness, exact size, and exhaustive partition are conclusions. -/
theorem half_partition_and_alternation
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (N : Finset α) (d : ℕ)
    (hα : Fintype.card α = 2 * d)
    (hN : d ≤ N.card)
    (havoid : ∀ i ∈ N, σ i ∉ N) :
    Disjoint N (N.image σ) ∧
      (N.image σ).card = N.card ∧
      N.card = d ∧
      N ∪ N.image σ = Finset.univ ∧
      ∀ i : α, σ i ∈ N ↔ i ∉ N := by
  have hdisjoint : Disjoint N (N.image σ) := by
    apply Finset.disjoint_left.mpr
    intro x hxN hxImage
    rcases Finset.mem_image.mp hxImage with ⟨i, hiN, hix⟩
    apply havoid i hiN
    rw [hix]
    exact hxN
  have himage : (N.image σ).card = N.card :=
    Finset.card_image_of_injective N σ.injective
  have hunionCard : (N ∪ N.image σ).card = N.card + N.card := by
    rw [Finset.card_union_of_disjoint hdisjoint, himage]
  have hle : N.card + N.card ≤ 2 * d := by
    have h := Finset.card_le_univ (N ∪ N.image σ)
    rw [hunionCard, hα] at h
    exact h
  have hcard : N.card = d := by
    omega
  have hunion : N ∪ N.image σ = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hunionCard, hcard, hα]
    omega
  refine ⟨hdisjoint, himage, hcard, hunion, ?_⟩
  intro i
  constructor
  · intro hσi hiN
    exact havoid i hiN hσi
  · intro hiN
    have hσiUnion : σ i ∈ N ∪ N.image σ := by
      rw [hunion]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hσiUnion with hσiN | hσiImage
    · exact hσiN
    · rcases Finset.mem_image.mp hσiImage with ⟨j, hjN, hji⟩
      have hji' : j = i := σ.injective hji
      exact False.elim (hiN (hji' ▸ hjN))

end ErdosProblems.PathUpperReduction.CycleHalfAlternation1105
