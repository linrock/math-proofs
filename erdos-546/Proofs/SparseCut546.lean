module

public import BidenseEmbedding546
public import MeanSubsets546


@[expose] public section

/-!
# Rounded bounded-degree sparse-cut lemma

This is a version of Sudakov Lemma 2.4 with an explicit factor of two in
the host-size hypothesis and in the denominator of the retained fraction.
It keeps arbitrary finite target and host graphs, permits isolated target
vertices, uses non-induced copies, and produces exactly equal sparse sides.
It is an auxiliary lemma for the original uniform Ramsey bound.
-/

namespace Erdos546

open Finset
open scoped Classical

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Rounded Sudakov bounded-degree embedding contrapositive. -/
theorem boundedDegree_sparse_cut (G : SimpleGraph V) (H : SimpleGraph W)
    (Δ : ℕ) (ε : ℝ) (hε : 0 < ε) (hhalf : ε ≤ 1 / 2)
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (hlarge : 2 * (Δ + 1 : ℝ) * Fintype.card V ≤ ε ^ Δ * Fintype.card W)
    (hfree : ¬ Nonempty (SimpleGraph.Copy G H)) :
    ∃ X Y : Finset W, Disjoint X Y ∧ X.card = Y.card ∧
      ε ^ Δ * Fintype.card W / (2 * (Δ + 1 : ℝ)) ≤ (X.card : ℝ) ∧
      ε ^ Δ * Fintype.card W / (2 * (Δ + 1 : ℝ)) ≤ (Y.card : ℝ) ∧
      ((H.interedges X Y).card : ℝ) ≤ ε * X.card * Y.card := by
  classical
  obtain ⟨X, Y, hdisjoint, hX, hY, hcross⟩ :=
    sparse_unequal_pair_of_no_copy_large_host G H Δ ε hε hhalf hdegree hlarge hfree
  let k := min X.card Y.card
  obtain ⟨X', Y', hXsub, hYsub, hXcard, hYcard, hcross'⟩ :=
    exists_equal_sparse_subcut H X Y ε k (Nat.min_le_left _ _)
      (Nat.min_le_right _ _) hcross
  have hk : ε ^ Δ * Fintype.card W / (2 * (Δ + 1 : ℝ)) ≤ (k : ℝ) := by
    dsimp [k]
    rw [Nat.cast_min]
    exact le_min hX hY
  refine ⟨X', Y',
    Finset.disjoint_of_subset_left hXsub
      (Finset.disjoint_of_subset_right hYsub hdisjoint),
    hXcard.trans hYcard.symm, ?_, ?_, ?_⟩
  · simpa [hXcard] using hk
  · simpa [hYcard] using hk
  · simpa [hXcard, hYcard, pow_two, mul_assoc] using hcross'

#print axioms boundedDegree_sparse_cut

end Erdos546
