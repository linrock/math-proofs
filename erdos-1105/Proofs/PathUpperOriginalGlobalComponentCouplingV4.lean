module

public import PathUpperOriginalCutFamilyV2
public import PathUpperOriginalGlobalCutLedgerV2

@[expose] public section

/-!
Couples the globally deleted `H` components to the cut-family `PieceIndex`.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- The actual stage and actual local component underlying a family piece. -/
structure OriginalCutFamilyLocalPieceData
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ) where
  U : Set (Fin q)
  W : Set (Fin n)
  x : Fin n
  stage : OriginalResidualCutStage χ R U W x
  component : stage.retainedGraph.ConnectedComponent

noncomputable def originalCutFamilyLocalPieceData
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    F.PieceIndex → OriginalCutFamilyLocalPieceData χ R :=
  match F with
  | .nil _ _ => fun i => PEmpty.elim i
  | .cons stage tail => Sum.elim (fun C => ⟨_, _, _, stage, C⟩)
      (originalCutFamilyLocalPieceData tail)

theorem originalCutFamily_local_stage_support_subset
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ i, (originalCutFamilyLocalPieceData F i).stage.rootSupport ⊆ W := by
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | cons stage tail ih =>
    intro i
    change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i
    cases i with
    | inl C => exact stage.support_subset
    | inr i => exact fun _ hv => (ih i hv).1

theorem originalCutFamily_local_piece_support
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ i, (Subtype.val '' (originalCutFamilyLocalPieceData F i).component.supp : Set (Fin n)) =
      F.pieceSupport i := by
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | cons stage tail ih =>
    intro i
    change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i
    cases i with
    | inl C => rfl
    | inr i => exact ih i

/-- Ancestor head cuts vanish on the genuine tail residual vertex carrier. -/
theorem originalCutFamily_global_tail_induce
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (stage : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs)
    (Z : Set (Fin n)) (hZ : Z ⊆ W \ componentSupport χ R x) :
    (originalCutFamilyGlobalRetainedGraph (.cons stage tail)).induce Z =
      (originalCutFamilyGlobalRetainedGraph tail).induce Z := by
  classical
  ext u v
  have hhead : s(u.val, v.val) ∉ liftOriginalComponentCut stage.rootSupport stage.B := by
    intro he
    exact (hZ u.property).2
      (liftOriginalComponentCut_vertex_mem _ _ he (Sym2.mem_mk_left _ _))
  simp only [originalCutFamilyGlobalRetainedGraph, originalCutFamilyLiftedCuts,
    SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Finset.mem_coe,
    Finset.mem_union, hhead, false_or]

/-- The restriction equality is DERIVED for every actual family piece's stage. -/
theorem originalCutFamily_global_piece_stage_induce
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ i, (originalCutFamilyGlobalRetainedGraph F).induce
        (originalCutFamilyLocalPieceData F i).stage.rootSupport =
      (originalCutFamilyLocalPieceData F i).stage.retainedGraph := by
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | cons stage tail ih =>
    intro i
    change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i
    cases i with
    | inl C => exact originalCutFamily_global_head_induce stage tail
    | inr i =>
      exact (originalCutFamily_global_tail_induce stage tail
        (originalCutFamilyLocalPieceData tail i).stage.rootSupport
        (originalCutFamily_local_stage_support_subset tail i)).trans (ih i)

theorem connectedComponent_cast_supp
    {V : Type*} {G H : SimpleGraph V} (h : G = H) (C : G.ConnectedComponent) :
    (Equiv.cast (congrArg (fun K : SimpleGraph V => K.ConnectedComponent) h) C).supp = C.supp := by
  cases h
  rfl

/-- Actual local-to-host component map, using only the derived graph equality. -/
noncomputable def originalCutFamilyGlobalPieceMap
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (i : F.PieceIndex) :
    (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent := by
  let P := originalCutFamilyLocalPieceData F i
  have hgraph : (originalCutFamilyGlobalRetainedGraph F).induce
      (componentSupport χ R P.x) = P.stage.retainedGraph := by
    simpa only [OriginalResidualCutStage.rootSupport] using
      originalCutFamily_global_piece_stage_induce F i
  let C := Equiv.cast
    (congrArg (fun K : SimpleGraph (componentSupport χ R P.x) => K.ConnectedComponent)
      hgraph.symm) P.component
  exact ErdosProblems.PathUpperSubgraphComponentDecomposition.originalComponentRefinementMap
    (selectedGraph χ R) (originalCutFamilyGlobalRetainedGraph F)
    ⟨(selectedGraph χ R).connectedComponentMk P.x, C⟩

theorem originalCutFamilyGlobalPieceMap_supp
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (i : F.PieceIndex) :
    (originalCutFamilyGlobalPieceMap F i).supp = F.pieceSupport i := by
  let P := originalCutFamilyLocalPieceData F i
  have hgraph : (originalCutFamilyGlobalRetainedGraph F).induce
      (componentSupport χ R P.x) = P.stage.retainedGraph := by
    simpa only [OriginalResidualCutStage.rootSupport] using
      originalCutFamily_global_piece_stage_induce F i
  let C : ((originalCutFamilyGlobalRetainedGraph F).induce
      (componentSupport χ R P.x)).ConnectedComponent :=
    Equiv.cast
      (congrArg (fun K : SimpleGraph (componentSupport χ R P.x) => K.ConnectedComponent)
        hgraph.symm) P.component
  have hle : originalCutFamilyGlobalRetainedGraph F ≤ selectedGraph χ R := by
    exact (show (selectedGraph χ R).deleteEdges
        (originalCutFamilyLiftedCuts F : Set (Sym2 (Fin n))) ≤ selectedGraph χ R from
      SimpleGraph.deleteEdges_le (G := selectedGraph χ R)
        (originalCutFamilyLiftedCuts F : Set (Sym2 (Fin n))))
  have hmap :=
    ErdosProblems.PathUpperSubgraphComponentDecomposition.original_component_refinement_map_supp
      (G := selectedGraph χ R) (H := originalCutFamilyGlobalRetainedGraph F)
      hle ((selectedGraph χ R).connectedComponentMk P.x) C
  have hcast : C.supp = P.component.supp :=
    connectedComponent_cast_supp hgraph.symm P.component
  have himage := congrArg
    (fun S : Set (componentSupport χ R P.x) => (Subtype.val '' S : Set (Fin n))) hcast
  change
    (ErdosProblems.PathUpperSubgraphComponentDecomposition.originalComponentRefinementMap
      (selectedGraph χ R) (originalCutFamilyGlobalRetainedGraph F)
      ⟨(selectedGraph χ R).connectedComponentMk P.x, C⟩).supp = F.pieceSupport i
  exact hmap.trans (himage.trans (originalCutFamily_local_piece_support F i))

theorem originalCutFamily_piece_support_subset
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (i : F.PieceIndex) :
    F.pieceSupport i ⊆ W := by
  rw [← originalCutFamily_local_piece_support F i]
  rintro v ⟨u, _hu, rfl⟩
  exact originalCutFamily_local_stage_support_subset F i u.property

theorem originalCutFamily_piece_support_nonempty
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (i : F.PieceIndex) :
    (F.pieceSupport i).Nonempty := by
  rw [← originalCutFamily_local_piece_support F i]
  obtain ⟨u, hu⟩ := (originalCutFamilyLocalPieceData F i).component.nonempty_supp
  exact ⟨u.val, u, hu, rfl⟩

theorem original_host_piece_disjoint
    {X : Set (Fin n)} (D : SimpleGraph X) {C E : D.ConnectedComponent} (hCE : C ≠ E) :
    Disjoint (originalResidualHostPiece C) (originalResidualHostPiece E) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨c, hc, hcv⟩ ⟨e, he, hev⟩
  have hce : c = e := Subtype.ext (hcv.trans hev.symm)
  exact (Set.disjoint_left.mp (D.pairwise_disjoint_supp_connectedComponent hCE))
    hc (hce.symm ▸ he)

theorem originalCutFamily_piece_support_disjoint
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ i j, i ≠ j → Disjoint (F.pieceSupport i) (F.pieceSupport j) := by
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | cons stage tail ih =>
    intro i j hij
    change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i j
    cases i with
    | inl C =>
      cases j with
      | inl E =>
        exact original_host_piece_disjoint stage.retainedGraph
          (fun h => hij (congrArg Sum.inl h))
      | inr j =>
        apply Set.disjoint_left.mpr
        rintro v ⟨u, _hu, rfl⟩ hv
        exact (originalCutFamily_piece_support_subset tail j hv).2 u.property
    | inr i =>
      cases j with
      | inl C =>
        apply Set.disjoint_left.mpr
        rintro v hv ⟨u, _hu, rfl⟩
        exact (originalCutFamily_piece_support_subset tail i hv).2 u.property
      | inr j => exact ih i j (fun h => hij (congrArg Sum.inr h))

theorem originalCutFamily_piece_support_cover
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ v, v ∈ W ↔ ∃ i, v ∈ F.pieceSupport i := by
  induction F with
  | nil empty partition =>
    intro v
    constructor
    · intro hv
      rw [empty] at hv
      exact hv.elim
    · rintro ⟨i, _⟩; exact PEmpty.elim i
  | @cons U W x xs stage tail ih =>
    intro v
    constructor
    · intro hv
      by_cases hx : v ∈ componentSupport χ R x
      · let u : componentSupport χ R x := ⟨v, hx⟩
        refine ⟨Sum.inl (stage.retainedGraph.connectedComponentMk u), ?_⟩
        exact ⟨u, ConnectedComponent.connectedComponentMk_mem, rfl⟩
      · obtain ⟨i, hi⟩ := (ih v).mp ⟨hv, hx⟩
        exact ⟨Sum.inr i, hi⟩
    · rintro ⟨i, hi⟩
      exact originalCutFamily_piece_support_subset (.cons stage tail) i hi

/-- Bijection follows from the DERIVED actual supports, not a desired partition. -/
theorem originalCutFamilyGlobalPieceMap_bijective
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)} (F : OriginalResidualCutFamily χ R ∅ Set.univ roots) :
    Function.Bijective (originalCutFamilyGlobalPieceMap F) := by
  constructor
  · intro i j hij
    by_contra hne
    obtain ⟨v, hv⟩ := originalCutFamily_piece_support_nonempty F i
    have hsupport : F.pieceSupport i = F.pieceSupport j := by
      rw [← originalCutFamilyGlobalPieceMap_supp F i,
        ← originalCutFamilyGlobalPieceMap_supp F j, hij]
    exact (Set.disjoint_left.mp (originalCutFamily_piece_support_disjoint F i j hne))
      hv (hsupport ▸ hv)
  · intro C
    obtain ⟨v, hvC⟩ := C.nonempty_supp
    obtain ⟨i, hi⟩ := (originalCutFamily_piece_support_cover F v).mp (Set.mem_univ v)
    refine ⟨i, ConnectedComponent.eq_of_common_vertex ?_ hvC⟩
    rw [originalCutFamilyGlobalPieceMap_supp F i]
    exact hi

noncomputable def originalCutFamilyGlobalComponentCoupling
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)} (F : OriginalResidualCutFamily χ R ∅ Set.univ roots) :
    (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent ≃ F.PieceIndex :=
  (Equiv.ofBijective (originalCutFamilyGlobalPieceMap F)
    (originalCutFamilyGlobalPieceMap_bijective F)).symm

theorem originalCutFamilyGlobalComponentCoupling_supp
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)} (F : OriginalResidualCutFamily χ R ∅ Set.univ roots)
    (i : F.PieceIndex) :
    ((originalCutFamilyGlobalComponentCoupling F).symm i).supp = F.pieceSupport i :=
  originalCutFamilyGlobalPieceMap_supp F i

theorem originalCutFamily_global_component_count
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)} (F : OriginalResidualCutFamily χ R ∅ Set.univ roots) :
    Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent =
      Nat.card (selectedGraph χ R).ConnectedComponent + F.cutCount := by
  calc
    Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent = Nat.card F.PieceIndex :=
      Nat.card_congr (originalCutFamilyGlobalComponentCoupling F)
    _ = roots.length + F.cutCount := originalCutFamily_piece_count F
    _ = Nat.card (selectedGraph χ R).ConnectedComponent + F.cutCount := by
      rw [residualGreedySequence_root_count χ R roots F.toGreedySequence]

theorem exists_full_original_global_component_coupling
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n))
      (F : OriginalResidualCutFamily χ R ∅ Set.univ roots),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      Nonempty ((originalCutFamilyGlobalRetainedGraph F).ConnectedComponent ≃ F.PieceIndex) ∧
      (∀ i : F.PieceIndex,
        ((originalCutFamilyGlobalComponentCoupling F).symm i).supp = F.pieceSupport i) ∧
      Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent =
        Nat.card (selectedGraph χ R).ConnectedComponent + F.cutCount := by
  obtain ⟨R, roots, F, hgreedy, hpieces, _hcount, _hT, _hS, _hcover, _hdisjoint⟩ :=
    exists_full_original_cut_family χ r
  exact ⟨R, roots, F, hgreedy, hpieces, ⟨originalCutFamilyGlobalComponentCoupling F⟩,
    originalCutFamilyGlobalComponentCoupling_supp F, originalCutFamily_global_component_count F⟩

end ErdosProblems.PathUpperReduction
