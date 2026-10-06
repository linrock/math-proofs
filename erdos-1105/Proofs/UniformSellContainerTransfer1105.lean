module

public import UniformSellTransfer1105
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

/-!
Actual Sell edge ledger and full original-palette caller. The core need not be complete, and the selected representative is unrestricted
apart from the actual spanning partition and absence of right-right edges.
-/

namespace ErdosProblems.UniformSellContainerCount1105

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.UniformSellDefects1105
open ErdosProblems.UniformSellApplication1105

/-- Every actual edge belongs either to the actual left core or an actual
crossing pair. The deficit is counted without natural subtraction. -/
theorem edge_count_add_crossing_defects_le {a t : ℕ}
    (G : SimpleGraph (Fin a ⊕ Fin t)) [DecidableRel G.Adj]
    (hYY : ∀ j j' : Fin t, ¬ G.Adj (Sum.inr j) (Sum.inr j')) :
    G.edgeFinset.card +
      (relationHoles (fun i j => G.Adj (Sum.inl i) (Sum.inr j))).card ≤
        a.choose 2 + a * t := by
  classical
  let C : SimpleGraph (Fin a) := G.comap Sum.inl
  let emb : Fin a ↪ (Fin a ⊕ Fin t) :=
    ⟨Sum.inl, by intro i j h; exact Sum.inl.inj h⟩
  let T : Finset (Fin a × Fin t) := Finset.univ.filter
    (fun ij => G.Adj (Sum.inl ij.1) (Sum.inr ij.2))
  let A := C.edgeFinset.map emb.sym2Map
  let B := T.image (fun ij => s(Sum.inl ij.1, Sum.inr ij.2))
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨ij, _hij, hje⟩ := Finset.mem_image.mp heB
    obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp heA
    revert hd hde
    refine Sym2.inductionOn d ?_
    intro x y _hd hde
    have heq : s(Sum.inl x, Sum.inl y) = s(Sum.inl ij.1, Sum.inr ij.2) := by
      change s(Sum.inl x, Sum.inl y) = e at hde
      exact hde.trans hje.symm
    rcases Sym2.eq_iff.mp heq with ⟨_, hy⟩ | ⟨hx, _⟩
    · cases hy
    · cases hx
  have hE : G.edgeFinset = A ∪ B := by
    ext e
    refine Sym2.inductionOn e ?_
    intro x y
    constructor
    · intro he
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
      cases x with
      | inl i =>
        cases y with
        | inl i' =>
          apply Finset.mem_union_left
          apply Finset.mem_map.mpr
          refine ⟨s(i, i'), SimpleGraph.mem_edgeFinset.mpr hxy, ?_⟩
          rfl
        | inr j =>
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩
      | inr j =>
        cases y with
        | inl i =>
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.symm⟩,
              Sym2.eq_swap⟩
        | inr j' => exact (hYY j j' hxy).elim
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp he
        revert hd hde
        refine Sym2.inductionOn d ?_
        intro i j hd hde
        change s(Sum.inl i, Sum.inl j) = s(x, y) at hde
        rw [← hde]
        have hij : C.Adj i j := SimpleGraph.mem_edgeFinset.mp hd
        have hG : G.Adj (Sum.inl i) (Sum.inl j) := hij
        exact SimpleGraph.mem_edgeFinset.mpr hG
      · obtain ⟨ij, hij, hje⟩ := Finset.mem_image.mp he
        rw [← hje]
        exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hij).2
  have hBcard : B.card = T.card := by
    apply Finset.card_image_of_injective
    intro ij kl he
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, _hj⟩
    · exact Prod.ext (Sum.inl.inj hi) (Sum.inr.inj hj)
    · cases hi
  have hcount : G.edgeFinset.card = C.edgeFinset.card + T.card := by
    have h := congrArg Finset.card hE
    rw [Finset.card_union_of_disjoint hAB, Finset.card_map, hBcard] at h
    exact h
  have hpartition : T.card +
      (relationHoles (fun i j => G.Adj (Sum.inl i) (Sum.inr j))).card = a * t := by
    simpa only [T, relationHoles, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin a × Fin t)))
        (fun ij => G.Adj (Sum.inl ij.1) (Sum.inr ij.2)))
  have hcore : C.edgeFinset.card ≤ a.choose 2 := by
    simpa only [Fintype.card_fin] using C.card_edgeFinset_le_card_choose_two
  omega

/-- The strict palette threshold forces the original crossing defect cap. -/
theorem crossing_defects_le_of_edge_count {a t : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (G : SimpleGraph (Fin a ⊕ Fin t)) [DecidableRel G.Adj]
    (hYY : ∀ j j' : Fin t, ¬ G.Adj (Sum.inr j) (Sum.inr j'))
    (he : a.choose 2 + (a - 1) * t + 2 < G.edgeFinset.card) :
    (relationHoles (fun i j => G.Adj (Sum.inl i) (Sum.inr j))).card ≤ t - 3 := by
  classical
  have hcount := edge_count_add_crossing_defects_le G hYY
  have hprod : a * t = (a - 1) * t + t := by
    calc
      a * t = ((a - 1) + 1) * t := by congr 1; omega
      _ = (a - 1) * t + t := by ring
  rw [hprod] at hcount
  omega

/-- Count the entire palette through an actual spanning equivalence. -/
theorem selected_crossing_defects_le_of_spanning_container {a t n q : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (f : (Fin a ⊕ Fin t) ≃ Fin n)
    (hYY : ∀ j j' : Fin t,
      ¬ (selectedGraph chi r).Adj (f (Sum.inr j)) (f (Sum.inr j')))
    (hq : a.choose 2 + (a - 1) * t + 2 < q) :
    (selectedCrossingHoles chi r f.toEmbedding).card ≤ t - 3 := by
  classical
  let G := selectedGraph chi r
  have hcard : (G.comap f).edgeFinset.card = q := by
    rw [(SimpleGraph.Iso.comap f G).card_edgeFinset_eq]
    exact selectedGraph_card_edgeFinset chi r
  have he : a.choose 2 + (a - 1) * t + 2 < (G.comap f).edgeFinset.card := by
    rw [hcard]
    exact hq
  simpa only [selectedCrossingHoles, G, SimpleGraph.comap_adj, Equiv.coe_toEmbedding] using
    crossing_defects_le_of_edge_count ha hat (G.comap f) hYY he

/-- Unconditional original-color Sell container exit. The core may omit
edges; arbitrary original color owners are handled by the verified transfer. -/
theorem rainbow_path_of_spanning_sell_container {a t n q : ℕ}
    (ha : 2 ≤ a) (hat : a + 2 ≤ t)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (f : (Fin a ⊕ Fin t) ≃ Fin n)
    (hYY : ∀ j j' : Fin t,
      ¬ (selectedGraph chi r).Adj (f (Sum.inr j)) (f (Sum.inr j')))
    (hq : a.choose 2 + (a - 1) * t + 2 < q) :
    ∃ p : (pathGraph (2 * a + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom chi := by
  exact rainbow_path_of_missing_selected_cross_edges ha hat chi r f.toEmbedding
    (selected_crossing_defects_le_of_spanning_container ha hat chi r f hYY hq)

end ErdosProblems.UniformSellContainerCount1105

