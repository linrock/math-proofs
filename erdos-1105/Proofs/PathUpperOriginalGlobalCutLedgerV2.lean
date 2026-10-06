module

public import PathUpperOriginalCutFamilyV2
public import PathUpperRainbowBridge
public import PathUpperSubgraphComponentDecompositionV2
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

/-!
Lift the actual simultaneously chosen local cuts into
the SAME original representative graph. Derive disjoint union cardinality,
actual selected-edge membership, and edge/vertex sums for the literal global
deletion graph. Its actual components are not yet identified with PieceIndex;
the original-color splices and numerical upper bound remain separate.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

noncomputable def liftOriginalComponentCut (X : Set (Fin n))
    (B : Finset (Sym2 X)) : Finset (Sym2 (Fin n)) := by
  classical
  exact B.image (Sym2.map (Subtype.val : X → Fin n))

theorem liftOriginalComponentCut_card (X : Set (Fin n)) (B : Finset (Sym2 X)) :
    (liftOriginalComponentCut X B).card = B.card := by
  classical
  exact Finset.card_image_of_injective B (Sym2.map.injective Subtype.val_injective)

theorem liftOriginalComponentCut_mem_map_iff (X : Set (Fin n))
    (B : Finset (Sym2 X)) (e : Sym2 X) :
    Sym2.map (Subtype.val : X → Fin n) e ∈ liftOriginalComponentCut X B ↔ e ∈ B := by
  classical
  constructor
  · intro he
    obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp he
    have h : d = e := Sym2.map.injective Subtype.val_injective hde
    exact h ▸ hd
  · intro he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem liftOriginalComponentCut_vertex_mem (X : Set (Fin n)) (B : Finset (Sym2 X))
    {e : Sym2 (Fin n)} (he : e ∈ liftOriginalComponentCut X B)
    {v : Fin n} (hv : v ∈ e) : v ∈ X := by
  classical
  obtain ⟨d, _hd, hde⟩ := Finset.mem_image.mp he
  rw [← hde] at hv
  obtain ⟨z, _hz, hzv⟩ := Sym2.mem_map.mp hv
  exact hzv ▸ z.property

theorem liftOriginalComponentCut_selected_edges (G : SimpleGraph (Fin n))
    (X : Set (Fin n)) (B : Finset (Sym2 X))
    (hB : (B : Set (Sym2 X)) ⊆ (G.induce X).edgeSet) :
    (liftOriginalComponentCut X B : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
  classical
  intro e he
  obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp he
  have hhost := (SimpleGraph.Embedding.induce (G := G) X).toHom.map_mem_edgeSet (hB hd)
  exact hde ▸ hhost

noncomputable def originalCutFamilyLiftedCuts
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : Finset (Sym2 (Fin n)) := by
  classical
  exact match F with
  | .nil _ _ => ∅
  | .cons stage tail =>
      liftOriginalComponentCut stage.rootSupport stage.B ∪ originalCutFamilyLiftedCuts tail

/-- Every actual cut endpoint lies in its actual residual host W. -/
theorem originalCutFamilyLiftedCuts_vertex_mem
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ {e : Sym2 (Fin n)}, e ∈ originalCutFamilyLiftedCuts F →
      ∀ {v : Fin n}, v ∈ e → v ∈ W := by
  classical
  induction F with
  | nil => simp [originalCutFamilyLiftedCuts]
  | cons stage tail ih =>
    intro e he v hv
    change e ∈ liftOriginalComponentCut stage.rootSupport stage.B ∪
      originalCutFamilyLiftedCuts tail at he
    rcases Finset.mem_union.mp he with he | he
    · exact stage.support_subset (liftOriginalComponentCut_vertex_mem _ _ he hv)
    · exact (ih he hv).1

/-- Actual whole-prefix removal makes head and tail lifted cuts disjoint. -/
theorem originalCutFamilyLiftedCuts_card
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    (originalCutFamilyLiftedCuts F).card = F.cutCount := by
  classical
  induction F with
  | nil => simp [originalCutFamilyLiftedCuts, OriginalResidualCutFamily.cutCount,
      originalCutFamilyCutTotal]
  | cons stage tail ih =>
    have hdis : Disjoint (liftOriginalComponentCut stage.rootSupport stage.B)
        (originalCutFamilyLiftedCuts tail) := by
      apply Finset.disjoint_left.mpr
      intro e he ht
      have hx := liftOriginalComponentCut_vertex_mem _ _ he (Sym2.out_fst_mem e)
      have hy := originalCutFamilyLiftedCuts_vertex_mem tail ht (Sym2.out_fst_mem e)
      exact hy.2 hx
    change (liftOriginalComponentCut stage.rootSupport stage.B ∪
      originalCutFamilyLiftedCuts tail).card = stage.B.card + tail.cutCount
    exact (Finset.card_union_of_disjoint hdis).trans
      (congrArg₂ Nat.add (liftOriginalComponentCut_card _ stage.B) ih)

/-- Each lifted cut is a literal selected edge, not only an abstract bridge. -/
theorem originalCutFamilyLiftedCuts_selected_edges
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    originalCutFamilyLiftedCuts F ⊆ (selectedGraph χ R).edgeFinset := by
  classical
  induction F with
  | nil => simp [originalCutFamilyLiftedCuts]
  | cons stage tail ih =>
    intro e he
    change e ∈ liftOriginalComponentCut stage.rootSupport stage.B ∪
      originalCutFamilyLiftedCuts tail at he
    rcases Finset.mem_union.mp he with he | he
    · apply SimpleGraph.mem_edgeFinset.mpr
      exact liftOriginalComponentCut_selected_edges _ _ _ stage.actual_edges he
    · exact ih he

noncomputable def originalCutFamilyGlobalRetainedGraph
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) : SimpleGraph (Fin n) :=
  (selectedGraph χ R).deleteEdges (originalCutFamilyLiftedCuts F)

/-- The literal global graph restricts to the stored actual first-stage D.
Tail cuts cannot affect a vertex in the whole removed head component. -/
theorem originalCutFamily_global_head_induce
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (stage : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs) :
    (originalCutFamilyGlobalRetainedGraph (.cons stage tail)).induce stage.rootSupport =
      stage.retainedGraph := by
  classical
  ext u v
  dsimp only [OriginalResidualCutStage.rootSupport] at u v ⊢
  have htail : s(u.val, v.val) ∉ originalCutFamilyLiftedCuts tail := by
    intro he
    have hu := originalCutFamilyLiftedCuts_vertex_mem tail he (Sym2.mem_mk_left _ _)
    exact hu.2 u.property
  have hhead : s(u.val, v.val) ∈ liftOriginalComponentCut (componentSupport χ R x) stage.B ↔
      s(u, v) ∈ stage.B := liftOriginalComponentCut_mem_map_iff _ _ s(u, v)
  simp only [originalCutFamilyGlobalRetainedGraph, originalCutFamilyLiftedCuts,
    OriginalResidualCutStage.rootSupport, OriginalResidualCutStage.retainedGraph, OriginalResidualRetainedGraph,
    SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Finset.mem_coe, Finset.mem_union,
    htail, or_false, hhead]

/-- Exact edge deletion for actual cuts; the whole original palette is retained. -/
theorem originalCutFamily_global_edge_card
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    let H := originalCutFamilyGlobalRetainedGraph F
    letI : DecidableRel H.Adj := Classical.decRel _
    q = H.edgeFinset.card + F.cutCount := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  have hcard : H.edgeFinset.card + (originalCutFamilyLiftedCuts F).card =
      (selectedGraph χ R).edgeFinset.card := by
    rw [show H = (selectedGraph χ R).deleteEdges (originalCutFamilyLiftedCuts F) from rfl,
      SimpleGraph.edgeFinset_deleteEdges]
    exact Finset.card_sdiff_add_card_eq_card (originalCutFamilyLiftedCuts_selected_edges F)
  rw [originalCutFamilyLiftedCuts_card F, selectedGraph_card_edgeFinset] at hcard
  exact hcard.symm

/-- Count the edges of the ACTUAL global components after literal deletion. -/
theorem originalCutFamily_global_component_edge_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    let H := originalCutFamilyGlobalRetainedGraph F
    letI : DecidableRel H.Adj := Classical.decRel _
    q = (∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) + F.cutCount := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  have hq := originalCutFamily_global_edge_card F
  have hparts := ErdosProblems.AntiRamseyPathFiveComponents.edge_card_eq_sum_component_edge_card H
  change q = H.edgeFinset.card + F.cutCount at hq
  exact hq.trans (congrArg (fun t => t + F.cutCount) hparts)

/-- Deleting edges keeps every host vertex, including all isolated vertices. -/
theorem originalCutFamily_global_component_vertex_sum
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    let H := originalCutFamilyGlobalRetainedGraph F
    letI : DecidableRel H.Adj := Classical.decRel _
    (∑ C : H.ConnectedComponent, Nat.card C.supp) = n := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  have hparts := ErdosProblems.AntiRamseyPathFiveComponents.vertex_card_eq_sum_component_card H
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hparts.symm

/-- Apply the derived generic refinement to the literal actual deletion graph.
Matching these actual local H-components to every stage D remains a separate seam. -/
noncomputable def originalCutFamilyGlobalComponentRefinement
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    (Σ C : (selectedGraph χ R).ConnectedComponent,
      ((originalCutFamilyGlobalRetainedGraph F).induce C.supp).ConnectedComponent) ≃
      (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent :=
  ErdosProblems.PathUpperSubgraphComponentDecomposition.originalComponentRefinementEquiv
    (G := selectedGraph χ R) (H := originalCutFamilyGlobalRetainedGraph F)
    (show originalCutFamilyGlobalRetainedGraph F ≤ selectedGraph χ R from
      SimpleGraph.deleteEdges_le (G := selectedGraph χ R)
        (originalCutFamilyLiftedCuts F : Set (Sym2 (Fin n))))

/-- Public existence derives the actual family and global graph from χ/full r.
No cuts, counts, partitions or favorable component correspondence are assumed. -/
theorem exists_full_original_global_cut_ledger
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n))
      (F : OriginalResidualCutFamily χ R ∅ Set.univ roots),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      roots.length = Nat.card (selectedGraph χ R).ConnectedComponent ∧
      Nat.card F.PieceIndex =
        Nat.card (selectedGraph χ R).ConnectedComponent + F.cutCount ∧
      originalCutFamilyTotalPieceSize F = n ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) ∧
      (originalCutFamilyLiftedCuts F).card = F.cutCount ∧
      (originalCutFamilyLiftedCuts F ⊆ (selectedGraph χ R).edgeFinset) ∧
      (let H := originalCutFamilyGlobalRetainedGraph F
       letI : DecidableRel H.Adj := Classical.decRel _
       q = (∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) + F.cutCount) ∧
      (let H := originalCutFamilyGlobalRetainedGraph F
       letI : DecidableRel H.Adj := Classical.decRel _
       (∑ C : H.ConnectedComponent, Nat.card C.supp) = n) := by
  obtain ⟨R, roots, F, hgreedy, hpieces, hcount, hT, hS, hcover, hdisjoint⟩ :=
    exists_full_original_cut_family χ r
  exact ⟨R, roots, F, hgreedy, hpieces, hcount, hT, hS, hcover, hdisjoint,
    originalCutFamilyLiftedCuts_card F, originalCutFamilyLiftedCuts_selected_edges F,
    originalCutFamily_global_component_edge_sum F, originalCutFamily_global_component_vertex_sum F⟩

end ErdosProblems.PathUpperReduction
