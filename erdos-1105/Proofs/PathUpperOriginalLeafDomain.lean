module

public import PathUpperOriginalComponentOrder
public import PathUpperOriginalPrefixInduction
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
Actual selected-component leaf extraction and the
last-leaf induction domain. No original NEW-color hypothesis, retained-leaf
edge hypothesis, favorable coloring or numerical anti-Ramsey formula is used. In the actual stage corollary, the full selected tail path forces the earlier
retained graph to be edgeless. Every edge in the whole earlier component is
then an actual cut bridge, so that component is a tree; its selected leaf may
itself have been cut. Two distinct actual components of order at least k-2
give k <= n-1 for k >= 5, including k=5 and the n=k obstruction.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n m q k : ℕ}

/-- A leaf of an actual finite tree component has a unique neighbor in the
WHOLE host graph. Component closure excludes neighbors outside its support. -/
theorem exists_host_leaf_of_actual_component_tree
    (G : SimpleGraph (Fin n)) (C : G.ConnectedComponent)
    (hTree : C.toSimpleGraph.IsTree) (hcard : 2 ≤ C.supp.ncard) :
    ∃ ell h : Fin n, ell ∈ C.supp ∧ h ∈ C.supp ∧ G.Adj ell h ∧
      (∀ v : Fin n, G.Adj ell v → v = h) := by
  classical
  let : Fintype C := Fintype.ofFinite C
  have hcard' : 1 < Fintype.card C := by
    rw [Fintype.card_eq_nat_card]
    change 1 < Nat.card C.supp
    rw [Nat.card_coe_set_eq]
    omega
  let : Nontrivial C := Fintype.one_lt_card_iff_nontrivial.mp hcard'
  obtain ⟨ell, hell⟩ := hTree.exists_vert_degree_one_of_nontrivial
  obtain ⟨h, hadj, hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hell
  refine ⟨ell.val, h.val, ell.property, h.property, hadj, ?_⟩
  intro v hv
  have hvC : v ∈ C.supp := C.mem_supp_of_adj_mem_supp ell.property hv
  have hv' : C.toSimpleGraph.Adj ell ⟨v, hvC⟩ := hv
  exact congrArg Subtype.val (hunique ⟨v, hvC⟩ hv')

/-- Actual edgeless retained stage means that EVERY selected edge in its
whole component is one of the actual bridge cuts; hence the whole induced
selected component is a tree. -/
theorem OriginalResidualCutStage.root_tree_of_retained_edgeless
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) (hD : S.retainedGraph = ⊥) :
    ((selectedGraph χ R).induce (componentSupport χ R x)).IsTree := by
  classical
  have hdata := S.payload
  dsimp [OriginalResidualCutStagePayload] at hdata
  have hbridge := hdata.2.2.2.1
  have hdelete :
      ((selectedGraph χ R).induce (componentSupport χ R x)).deleteEdges
        (S.B : Set (Sym2 (componentSupport χ R x))) = ⊥ := by
    simpa only [OriginalResidualCutStage.retainedGraph,
      OriginalResidualRetainedGraph] using hD
  have hall : ((selectedGraph χ R).induce (componentSupport χ R x)).edgeSet ⊆
      (S.B : Set (Sym2 (componentSupport χ R x))) :=
    deleteEdges_eq_bot.mp hdelete
  have hacyclic : ((selectedGraph χ R).induce (componentSupport χ R x)).IsAcyclic :=
    isAcyclic_iff_forall_isBridge.mpr (fun _ he => hbridge _ (hall he))
  have hconnected : ((selectedGraph χ R).induce (componentSupport χ R x)).Connected := by
    change ((selectedGraph χ R).connectedComponentMk x).toSimpleGraph.Connected
    exact ((selectedGraph χ R).connectedComponentMk x).connected_toSimpleGraph
  exact ⟨hconnected, hacyclic⟩

/-- The actual edgeless stage constructs a literal original selected head
edge and the owner-color confinement required by last-leaf restriction. -/
theorem OriginalResidualCutStage.exists_original_owner_leaf_of_retained_edgeless
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x) (hD : S.retainedGraph = ⊥)
    (hcard : 2 ≤ (componentSupport χ R x).ncard) :
    ∃ (ell h : Fin n) (head : HostEdge n),
      ell ∈ componentSupport χ R x ∧ h ∈ componentSupport χ R x ∧
      head.val = s(ell, h) ∧ head.val ∈ (selectedGraph χ R).edgeSet ∧
      (∀ v : Fin n, (selectedGraph χ R).Adj ell v → v = h) ∧
      (∀ c : Fin q, ell ∈ (R.edge c).val → c = χ head) := by
  classical
  let C := (selectedGraph χ R).connectedComponentMk x
  have hTree : C.toSimpleGraph.IsTree := S.root_tree_of_retained_edgeless hD
  obtain ⟨ell, h, hell, hh, hadj, hunique⟩ :=
    exists_host_leaf_of_actual_component_tree (selectedGraph χ R) C hTree hcard
  let head : HostEdge n := ⟨s(ell, h),
    (top_adj ell h).mpr ((selectedGraph χ R).ne_of_adj hadj)⟩
  have hhead : head.val ∈ (selectedGraph χ R).edgeSet := hadj
  refine ⟨ell, h, head, hell, hh, rfl, hhead, hunique, ?_⟩
  exact original_owner_color_of_unique_selected_neighbor χ R ell h head rfl hunique

/-- Two DISTINCT actual components each large enough for a (k-2)-vertex path
force the leaf-deleted host into the original induction regime k <= n-1. -/
theorem leaf_deleted_host_domain_of_two_actual_components
    (G : SimpleGraph (Fin n)) (C D : G.ConnectedComponent) (hCD : C ≠ D)
    (hk : 5 ≤ k) (hC : k - 2 ≤ C.supp.ncard) (hD : k - 2 ≤ D.supp.ncard) :
    k ≤ n - 1 := by
  have hdisjoint : Disjoint C.supp D.supp :=
    G.pairwise_disjoint_supp_connectedComponent hCD
  have hsum : C.supp.ncard + D.supp.ncard ≤ n := by
    have hbound := Set.ncard_le_card (C.supp ∪ D.supp)
    rw [Set.ncard_union_eq hdisjoint] at hbound
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hbound
  omega

theorem leaf_deleted_host_domain_of_two_selected_components
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (x y : Fin n)
    (hxy : (selectedGraph χ R).connectedComponentMk x ≠
      (selectedGraph χ R).connectedComponentMk y)
    (hk : 5 ≤ k)
    (hx : k - 2 ≤ (componentSupport χ R x).ncard)
    (hy : k - 2 ≤ (componentSupport χ R y).ncard) : k ≤ n - 1 :=
  leaf_deleted_host_domain_of_two_actual_components (selectedGraph χ R)
    ((selectedGraph χ R).connectedComponentMk x)
    ((selectedGraph χ R).connectedComponentMk y) hxy hk hx hy

/-- Full original last-leaf caller: the actual uncut long tail derives the
earlier tree and selected leaf, and the two actual component orders derive
the induction domain. The conclusion uses literal antiRamseyNum on Fin m;
its numerical inductive bound remains a separate application. -/
theorem OriginalResidualCutStage.last_leaf_restriction_with_domain
    {χ : TopEdgeLabeling (Fin (m + 1)) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin (m + 1))} {x : Fin (m + 1)}
    (S : OriginalResidualCutStage χ R U W x) (hk : 5 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬ IsRainbow F.toHom χ)
    (y : Fin (m + 1))
    (hxy : (selectedGraph χ R).connectedComponentMk x ≠
      (selectedGraph χ R).connectedComponentMk y)
    (hx : k - 2 ≤ (componentSupport χ R x).ncard)
    (hy : k - 2 ≤ (componentSupport χ R y).ncard)
    (Q : (pathGraph (k - 2)).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x) :
    k ≤ m ∧ q ≤ antiRamseyNum (pathGraph k) m := by
  classical
  have hk3 : 3 ≤ k := by omega
  have hD : S.retainedGraph = ⊥ :=
    S.retained_edgeless_of_uncut_tail_path_order hk3 hno Q hQ
  have hcard : 2 ≤ (componentSupport χ R x).ncard := by omega
  obtain ⟨ell, h, head, hell, hh, hheadval, hhead, _hunique, howner⟩ :=
    S.exists_original_owner_leaf_of_retained_edgeless hD hcard
  let first : Fin (k - 2) := ⟨0, by omega⟩
  have hne : h ≠ Q first := by
    intro heq
    have ht := hQ ⟨first, rfl⟩
    apply ht.2
    exact Eq.mp (congrArg (fun z => z ∈ componentSupport χ R x) heq) hh
  let join : HostEdge (m + 1) := ⟨s(h, Q first), (top_adj h (Q first)).mpr hne⟩
  have hcount : q ≤ antiRamseyNum (pathGraph k) m :=
    S.last_leaf_color_count_le hk3 hno ell h head hhead hheadval hell hh
      howner Q hQ join rfl
  have hdomain := leaf_deleted_host_domain_of_two_selected_components
    χ R x y hxy hk hx hy
  exact ⟨by simpa only [Nat.add_sub_cancel] using hdomain, hcount⟩

/-- A later ACTUAL retained long path in the SAME-R greedy sequence derives
all domain and leaf premises for the earlier-stage restriction. No component
order, distinctness, acyclicity, leaf or favorable-color premise is supplied. -/
theorem OriginalResidualCutStage.last_leaf_restriction_of_later_retained_long_path
    {χ : TopEdgeLabeling (Fin (m + 1)) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin (m + 1))} {x : Fin (m + 1)}
    {xs : List (Fin (m + 1))}
    (S : OriginalResidualCutStage χ R U W x)
    (hsequence : ResidualGreedySequence χ R U W (x :: xs))
    {y : Fin (m + 1)} (hy : y ∈ xs)
    {V : Set (Fin q)} {Z : Set (Fin (m + 1))}
    (T : OriginalResidualCutStage χ R V Z y) (hk : 5 ≤ k)
    (P : (pathGraph (k - 2)).Copy T.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin (m + 1))),
      ¬ IsRainbow F.toHom χ) :
    k ≤ m ∧ q ≤ antiRamseyNum (pathGraph k) m := by
  classical
  let Q : (pathGraph (k - 2)).Copy (selectedGraph χ R) :=
    { toHom :=
        { toFun := fun u => (P u).val
          map_rel' := by
            intro u v huv
            exact (deleteEdges_adj.mp (P.toHom.map_rel' huv)).1 }
      injective' := by
        intro u v huv
        apply P.injective
        exact Subtype.ext huv }
  have hQY : Set.range (fun v => Q v) ⊆ componentSupport χ R y := by
    rintro z ⟨v, rfl⟩
    exact (P v).property
  have hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x :=
    hQY.trans (S.later_component_support_subset hsequence hy)
  have hY : k - 2 ≤ (componentSupport χ R y).ncard := by
    have hbound := Set.ncard_le_ncard hQY
    rw [Set.ncard_range_of_injective (f := fun v => Q v) Q.injective] at hbound
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hbound
  have hX : k - 2 ≤ (componentSupport χ R x).ncard :=
    hY.trans (S.later_component_size_le hsequence hy)
  have hyY : y ∈ componentSupport χ R y :=
    (mem_componentSupport χ R y y).mpr (SimpleGraph.Reachable.refl y)
  have hyNotX : y ∉ componentSupport χ R x :=
    (S.later_component_support_subset hsequence hy hyY).2
  have hxy : (selectedGraph χ R).connectedComponentMk x ≠
      (selectedGraph χ R).connectedComponentMk y := by
    intro heq
    apply hyNotX
    change y ∈ ((selectedGraph χ R).connectedComponentMk x).supp
    rw [heq]
    exact hyY
  exact S.last_leaf_restriction_with_domain hk hno y hxy hX hY Q hQ

end ErdosProblems.PathUpperReduction

