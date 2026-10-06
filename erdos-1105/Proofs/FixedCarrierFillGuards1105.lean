module

public import GenericPathMissingPairClosure1105

@[expose] public section

/-!
Exact ORIGINAL degree guards for the actual two-phase
W-incident filling on the SAME Fin (2*d+2). This source constructs the seed
fill graph; it does not assume a degree trace or discard isolated vertices. The original retained peeled-degree bound is explicit and must be derived
by the actual order/carrier caller.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.FixedCarrierFillGuards1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.GenericPathMissingPairClosure1105

/-- Literal ORIGINAL degree restricted to all vertices of the actual seed. -/
def originalSeedDegree {n : ℕ} (G : SimpleGraph (Fin n))
    (K : Finset (Fin n)) (w : Fin n) : ℕ := by
  classical
  exact (K.filter (fun v => G.Adj w v)).card

/-- Add exactly the finite distinct W-seed pair family on the same carrier. -/
def fillSeedPairs {n : ℕ} (G : SimpleGraph (Fin n))
    (K W : Finset (Fin n)) : SimpleGraph (Fin n) :=
  G ⊔ fromEdgeSet {e | ∃ w ∈ W, ∃ v ∈ K, w ≠ v ∧ e = s(w,v)}

theorem originalSeedDegree_le_degree {n : ℕ}
    (G : SimpleGraph (Fin n)) (K : Finset (Fin n)) (w : Fin n) :
    originalSeedDegree G K w ≤ G.degree w := by
  classical
  have hsub : K.filter (fun v => G.Adj w v) ⊆ G.neighborFinset w := by
    intro v hv
    exact (G.mem_neighborFinset w v).mpr (Finset.mem_filter.mp hv).2
  simpa only [originalSeedDegree, card_neighborFinset_eq_degree] using
    Finset.card_le_card hsub

/-- The first fill's guard is ORIGINAL kernel/high-pool degree, retained in
every intermediate supergraph; no newly filled degree is counted here. -/
theorem seed_pair_guard {d : ℕ}
    (G J : SimpleGraph (Fin (2*d+2))) (K : Finset (Fin (2*d+2)))
    (w v : Fin (2*d+2)) (hGJ : G ≤ J)
    (hhigh : d+1 ≤ originalSeedDegree G K w)
    (hmin : d ≤ originalSeedDegree G K v) :
    2*d+2-1 ≤ J.degree w + J.degree v := by
  have hw : d+1 ≤ J.degree w :=
    hhigh.trans ((originalSeedDegree_le_degree G K w).trans
      (G.degree_le_of_le (v := w) hGJ))
  have hv : d ≤ J.degree v :=
    hmin.trans ((originalSeedDegree_le_degree G K v).trans
      (G.degree_le_of_le (v := v) hGJ))
  omega

/-- Membership in the explicit fill graph derives complete seed adjacency. -/
theorem filled_seed_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (K W : Finset (Fin n)) (w v : Fin n)
    (hw : w ∈ W) (hv : v ∈ K) (hne : w ≠ v) :
    (fillSeedPairs G K W).Adj w v := by
  apply (SimpleGraph.sup_adj _ _ _ _).mpr
  right
  exact (SimpleGraph.fromEdgeSet_adj _).mpr
    ⟨⟨w, hw, v, hv, hne, rfl⟩, hne⟩

/-- After the explicit first family, the SAME original seed supplies the
whole-carrier degree bound |K|-1 for each W vertex. -/
theorem seed_fill_degree_lower {n : ℕ} (G J : SimpleGraph (Fin n))
    (K W : Finset (Fin n)) (w : Fin n) (hw : w ∈ W) (hwK : w ∈ K)
    (hfill : fillSeedPairs G K W ≤ J) : K.card-1 ≤ J.degree w := by
  classical
  have hsub : K.erase w ⊆ J.neighborFinset w := by
    intro v hv
    obtain ⟨hvw, hvK⟩ := Finset.mem_erase.mp hv
    exact (J.mem_neighborFinset w v).mpr
      (hfill (filled_seed_adj G K W w v hw hvK (Ne.symm hvw)))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hwK, card_neighborFinset_eq_degree] at hcard
  exact hcard

/-- Every second-family missing pair meets the exact N-1 threshold, even
when the peeled vertex is maximally deficient. The seed-first order is real. -/
theorem restoration_pair_guard {d h : ℕ}
    (G J : SimpleGraph (Fin (2*d+2)))
    (K W : Finset (Fin (2*d+2))) (w x : Fin (2*d+2))
    (hh : h ≤ d) (horder : K.card = d+h) (hWK : W ⊆ K)
    (hw : w ∈ W) (hfill : fillSeedPairs G K W ≤ J)
    (hpeeled : d-h+2 ≤ G.degree x) :
    2*d+2-1 ≤ J.degree w + J.degree x := by
  have hGJ : G ≤ J := le_trans le_sup_left hfill
  have hwdegree := seed_fill_degree_lower G J K W w hw (hWK hw) hfill
  rw [horder] at hwdegree
  have hxdegree : d-h+2 ≤ J.degree x :=
    hpeeled.trans (G.degree_le_of_le (v := x) hGJ)
  omega

/-- One actual second-family step preserves spanning-path freedom using
the guard derived above, not a supplied sum or a path endpoint oracle. -/
theorem path_free_after_missing_restoration_pair {d h : ℕ}
    (hd : 4 ≤ d) (G J : SimpleGraph (Fin (2*d+2)))
    (K W : Finset (Fin (2*d+2))) (w x : Fin (2*d+2))
    (hh : h ≤ d) (horder : K.card = d+h) (hWK : W ⊆ K)
    (hw : w ∈ W) (hx : x ∉ K)
    (hfill : fillSeedPairs G K W ≤ J)
    (hpeeled : d-h+2 ≤ G.degree x)
    (hfree : (pathGraph (2*d+2)).Free J) (hmissing : ¬ J.Adj w x) :
    (pathGraph (2*d+2)).Free
      (ErdosProblems.PathSpanningNonedgeDeficit.augment J w x) := by
  have hne : w ≠ x := by
    intro heq
    exact hx (heq ▸ hWK hw)
  exact pathGraph_free_after_adding_missing_pair (by omega) J hfree w x hne
    hmissing (restoration_pair_guard G J K W w x hh horder hWK hw hfill hpeeled)

end ErdosProblems.PathUpperReduction.FixedCarrierFillGuards1105

