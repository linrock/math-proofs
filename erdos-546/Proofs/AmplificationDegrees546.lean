module

public import ResidualObstruction546
public import DegreeMax546


@[expose] public section

/-!
# Residual maximum-degree bound for amplification

Deletes a vertex set `A` of size `|X|` from `G` and bounds the maximum degree
of the remaining induced subgraph by `2m / (|X| + 1)`.
-/

namespace Erdos546

open SimpleGraph Finset

theorem residual_degree_data_of_monoPair {V W : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (m a : ℕ) (hm : 0 < m) (hedges : G.edgeSet.ncard = m)
    {X Y : Finset W} (hp : MonoPair H X Y) (hfree : ¬ G.IsContained H)
    (hclique : (a : ℝ)^3 * Real.sqrt m ≤ X.card) :
    ∃ (A : Finset V) (D : ℕ), A.card = X.card ∧
      0 < Fintype.card ↥((A : Set V)ᶜ) ∧
      (∀ v : ↥((A : Set V)ᶜ), (G.induce ((A : Set V)ᶜ)).degree v ≤ D) ∧
      (a : ℝ)^3 * D ≤ 2 * Real.sqrt m ∧
      ¬ (G.induce ((A : Set V)ᶜ)).IsContained (H.induce (Y : Set W)) := by
  classical
  obtain ⟨A, hA, hdegree, hresidual_free⟩ :=
    residual_obstruction_of_monoPair G H hp hfree
  have hn : 0 < Fintype.card ↥((A : Set V)ᶜ) := by
    by_contra hn
    have hnzero : Fintype.card ↥((A : Set V)ᶜ) = 0 := by omega
    have hcl : (H.induce (Y : Set W)).IsClique
        ((∅ : Finset ↥(Y : Set W)) : Set ↥(Y : Set W)) := by
      simp [SimpleGraph.IsClique]
    exact hresidual_free (isContained_of_clique (G.induce ((A : Set V)ᶜ))
      (H.induce (Y : Set W)) ∅ hcl (by simp [hnzero]))
  let D : ℕ := univ.sup (fun v : ↥((A : Set V)ᶜ) =>
    (G.induce ((A : Set V)ᶜ)).degree v)
  have hdeg : ∀ v : ↥((A : Set V)ᶜ), (G.induce ((A : Set V)ᶜ)).degree v ≤ D := by
    intro v
    exact Finset.le_sup (f := fun w : ↥((A : Set V)ᶜ) =>
      (G.induce ((A : Set V)ᶜ)).degree w) (mem_univ v)
  have hweighted : (X.card + 1) * D ≤ 2 * G.edgeFinset.card :=
    weighted_sup_bound univ (fun v : ↥((A : Set V)ᶜ) =>
      (G.induce ((A : Set V)ᶜ)).degree v) X.card
      (2 * G.edgeFinset.card) (fun v _ => hdegree v)
  have he : G.edgeFinset.card = m := by
    rw [← hedges, ← G.coe_edgeFinset, Set.ncard_coe_finset]
  rw [he] at hweighted
  have hfactor := sparse_degree_factor_bound X.card D m a hm hclique hweighted
  exact ⟨A, D, hA, hn, hdeg, hfactor, hresidual_free⟩

end Erdos546
