module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
a supplied finite forbidden-free graph extends to a
forbidden-free graph saturated under every literal missing-pair addition. No coloring, extremal density or classification statement is asserted.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- A supplied graph on a finite carrier has a forbidden-free supergraph
such that every missing distinct pair creates an ordinary forbidden copy. -/
theorem exists_saturated_free_supergraph {V W : Type*} [Fintype V]
    (F : SimpleGraph W) (G : SimpleGraph V) (hG : F.Free G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ F.Free H ∧
      ∀ u v : V, u ≠ v → ¬ H.Adj u v →
        Nonempty (F.Copy (H ⊔
          SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V)))) := by
  classical
  let : (J : SimpleGraph V) → Fintype J.edgeSet :=
    fun J => SimpleGraph.fintypeEdgeSet J
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun J => G ≤ J ∧ F.Free J)
  have hGmem : G ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ G, le_rfl, hG⟩
  obtain ⟨H, hHmem, hmax⟩ :=
    Finset.exists_max_image candidates (fun J => J.edgeFinset.card) ⟨G, hGmem⟩
  obtain ⟨hGH, hFH⟩ := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hGH, hFH, ?_⟩
  intro u v huv hmissing
  let J : SimpleGraph V :=
    H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))
  have hHJ : H ≤ J := le_sup_left
  have hnew : J.Adj u v := by
    exact (SimpleGraph.sup_adj H
      (SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) u v).mpr
      (Or.inr ((SimpleGraph.fromEdgeSet_adj
        ({s(u, v)} : Set (Sym2 V))).mpr ⟨Set.mem_singleton _, huv⟩))
  have hstrict : H < J := by
    refine lt_of_le_of_ne hHJ ?_
    intro heq
    exact hmissing (heq.symm ▸ hnew)
  change Nonempty (F.Copy J)
  by_contra hnoCopy
  have hFJ : F.Free J := hnoCopy
  have hJmem : J ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ J, hGH.trans hHJ, hFJ⟩
  have hcard : H.edgeFinset.card < J.edgeFinset.card :=
    Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hstrict)
  exact (Nat.not_lt_of_ge (hmax J hJmem)) hcard

-- Literal spanning-path application, for every natural k, without positivity.
example (k : ℕ) (G : SimpleGraph (Fin k)) (hG : (pathGraph k).Free G) :
    ∃ H : SimpleGraph (Fin k), G ≤ H ∧ (pathGraph k).Free H ∧
      ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
        Nonempty ((pathGraph k).Copy (H ⊔
          SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin k))))) :=
  exists_saturated_free_supergraph (pathGraph k) G hG

end ErdosProblems.PathUpperReduction
