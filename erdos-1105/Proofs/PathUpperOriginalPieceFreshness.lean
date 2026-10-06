module

public import PathUpperOriginalGlobalComponentCouplingV4
public import PathHighNewHostPathToolsV4

@[expose] public section

/-!
Original-color freshness against TWO actual retained
pieces at their earliest prefix. The public theorem keeps arbitrary original
chi/R/U/W/roots/F and BOTH endpoint pieces. It does not say the joining label
is a global cut color or that every original host edge avoids earlier palettes. The old private
original_owner_of_selected_edge is not publicly callable, so the short exact
owner derivation below is local.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

theorem selected_host_owner
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (e : HostEdge n) (he : e.val ∈ (selectedGraph χ R).edgeSet) :
    e = R.edge (χ e) := by
  rw [selectedGraph_edgeSet] at he
  obtain ⟨c, hc⟩ := he
  have howner : e = R.edge c := Subtype.ext hc.symm
  have hcolor : χ e = c := (congrArg χ howner).trans (R.color_eq c)
  rw [hcolor]
  exact howner

/-- Every A color has its SAME original owner in the actual lifted head cut.
Owner containment is derived from the stage maximum, not supplied. -/
theorem OriginalResidualCutStage.owner_mem_lifted_cut
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    (c : EligibleInteriorColor χ U (componentSupport χ R x)) (hc : c ∈ S.A) :
    (R.edge c.val).val ∈ liftOriginalComponentCut S.rootSupport S.B := by
  classical
  have hinside := selected_edge_inside_of_eligibleInterior_color
    χ R U W S.partition x S.support_subset S.maximum c.val c.property
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective ((R.edge c.val).val)
  change s(a, b) = (R.edge c.val).val at hab
  have ha : a ∈ (R.edge c.val).val := by
    rw [← hab]
    exact Sym2.mem_mk_left _ _
  have hb : b ∈ (R.edge c.val).val := by
    rw [← hab]
    exact Sym2.mem_mk_right _ _
  let z : componentSupport χ R x := ⟨a, hinside a ha⟩
  let w : componentSupport χ R x := ⟨b, hinside b hb⟩
  have hmap : Sym2.map (Subtype.val : componentSupport χ R x → Fin n) s(z, w) =
      (R.edge c.val).val := by
    simpa only [Sym2.map_mk, z, w] using hab
  have hBset : (S.B : Set (Sym2 (componentSupport χ R x))) =
      OriginalResidualColorDeletion χ R U (componentSupport χ R x) (S.A : Set _) :=
    S.payload.2.1
  have hB : s(z, w) ∈ S.B := by
    change s(z, w) ∈ (S.B : Set (Sym2 (componentSupport χ R x)))
    rw [hBset]
    exact ⟨c, hc, hmap⟩
  change (R.edge c.val).val ∈ S.B.image
    (Sym2.map (Subtype.val : componentSupport χ R x → Fin n))
  exact Finset.mem_image.mpr ⟨s(z, w), hB, hmap⟩

theorem global_retained_host_edge_facts
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (e : HostEdge n)
    (he : e.val ∈ (originalCutFamilyGlobalRetainedGraph F).edgeSet) :
    e.val ∈ (selectedGraph χ R).edgeSet ∧ e.val ∉ originalCutFamilyLiftedCuts F := by
  simpa only [originalCutFamilyGlobalRetainedGraph, SimpleGraph.edgeSet_deleteEdges,
    Set.mem_sdiff, Finset.mem_coe] using he

/-- A retained original edge inside the earliest remaining carrier avoids
the frozen prefix U and ALL actual head-A labels. -/
theorem originalCutFamily_head_retained_edge_avoids_prefix_and_cut
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs)
    (f : HostEdge n)
    (hf : f.val ∈ (originalCutFamilyGlobalRetainedGraph (.cons S tail)).edgeSet)
    (hinside : EdgeInside W f.val) :
    χ f ∉ U ∧ χ f ∉ S.A.image (fun c => c.val) := by
  classical
  obtain ⟨hfG, hfcut⟩ := global_retained_host_edge_facts (.cons S tail) f hf
  have howner := selected_host_owner χ R f hfG
  have hz : f.val.out.1 ∈ f.val := Sym2.out_fst_mem _
  have hzowner : f.val.out.1 ∈ (R.edge (χ f)).val := by
    rw [← howner]
    exact hz
  constructor
  · exact selected_slot_color_not_removed_of_endpoint_in_remaining
      χ R U W S.partition (χ f) f.val.out.1 hzowner (hinside _ hz)
  · intro hA
    obtain ⟨c, hc, hcf⟩ := Finset.mem_image.mp hA
    have hmem : f.val ∈ liftOriginalComponentCut S.rootSupport S.B := by
      rw [howner, ← hcf]
      exact S.owner_mem_lifted_cut c hc
    apply hfcut
    change f.val ∈ liftOriginalComponentCut S.rootSupport S.B ∪
      originalCutFamilyLiftedCuts tail
    exact Finset.mem_union.mpr (Or.inl hmem)

theorem originalCutFamily_global_cons_le_tail
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs) :
    originalCutFamilyGlobalRetainedGraph (.cons S tail) ≤
      originalCutFamilyGlobalRetainedGraph tail := by
  classical
  apply SimpleGraph.deleteEdges_anti
  intro e he
  change e ∈ liftOriginalComponentCut S.rootSupport S.B ∪
    originalCutFamilyLiftedCuts tail
  exact Finset.mem_union.mpr (Or.inr he)

theorem originalCutFamily_head_label_fresh_of_cover
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {xs : List (Fin n)}
    (S : OriginalResidualCutStage χ R U W x)
    (tail : OriginalResidualCutFamily χ R
      (U ∪ residualSelectedComponentColors χ R x) (W \ componentSupport χ R x) xs)
    (e f : HostEdge n)
    (hcover : χ e ∈ U ∨ χ e ∈ S.A.image (fun c => c.val))
    (hf : f.val ∈ (originalCutFamilyGlobalRetainedGraph (.cons S tail)).edgeSet)
    (hinside : EdgeInside W f.val) : χ f ≠ χ e := by
  obtain ⟨hU, hA⟩ := originalCutFamily_head_retained_edge_avoids_prefix_and_cut
    S tail f hf hinside
  intro heq
  rcases hcover with hcover | hcover
  · exact hU (heq.symm ▸ hcover)
  · exact hA (heq.symm ▸ hcover)

/-- Every joining host label between TWO distinct actual
pieces is fresh against ANY selected globally retained edge inside either
piece. Later U colors remain an alternative and are excluded at the EARLIEST
of the two chosen original stages. Singleton pieces are allowed. -/
theorem originalCutFamily_cross_piece_color_fresh
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) :
    ∀ (i j : F.PieceIndex), i ≠ j →
      ∀ (e : HostEdge n) (u v : Fin n), e.val = s(u, v) →
        u ∈ F.pieceSupport i → v ∈ F.pieceSupport j →
        ∀ (f : HostEdge n), f.val ∈ (originalCutFamilyGlobalRetainedGraph F).edgeSet →
          (EdgeInside (F.pieceSupport i) f.val ∨ EdgeInside (F.pieceSupport j) f.val) →
            χ f ≠ χ e := by
  classical
  induction F with
  | nil => intro i; exact PEmpty.elim i
  | @cons U W x xs S tail ih =>
    intro i j hij e u v he hu hv f hf hinside
    have hfW : EdgeInside W f.val := by
      intro z hz
      rcases hinside with hi | hj
      · exact originalCutFamily_piece_support_subset (.cons S tail) i (hi z hz)
      · exact originalCutFamily_piece_support_subset (.cons S tail) j (hj z hz)
    change S.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i j
    cases i with
    | inl C =>
      cases j with
      | inl E =>
        change u ∈ originalResidualHostPiece C at hu
        change v ∈ originalResidualHostPiece E at hv
        rcases hu with ⟨z, hz, rfl⟩
        rcases hv with ⟨w, hw, rfl⟩
        have hCE : C ≠ E := fun h => hij (congrArg Sum.inl h)
        have hnotreachable : ¬ S.retainedGraph.Reachable z w := by
          intro hreach
          have hzC : S.retainedGraph.connectedComponentMk z = C := hz
          have hwE : S.retainedGraph.connectedComponentMk w = E := hw
          exact hCE (hzC.symm.trans
            ((SimpleGraph.ConnectedComponent.sound hreach).trans hwE))
        have heX : EdgeInside S.rootSupport e.val := by
          intro a ha
          rw [he] at ha
          rcases Sym2.mem_iff.mp ha with rfl | rfl
          · exact z.property
          · exact w.property
        have hcover : χ e ∈ U ∨ χ e ∈ S.A.image (fun c => c.val) := by
          by_cases hU : χ e ∈ U
          · exact Or.inl hU
          · right
            have h := S.payload
            rcases h with ⟨_, _, _, _, _, hcross, _⟩
            obtain ⟨hc, hA⟩ := hcross e heX hU z w he hnotreachable
            exact Finset.mem_image.mpr ⟨⟨χ e, hc⟩, hA, rfl⟩
        exact originalCutFamily_head_label_fresh_of_cover S tail e f hcover hf hfW
      | inr j =>
        change u ∈ originalResidualHostPiece C at hu
        change v ∈ tail.pieceSupport j at hv
        rcases hu with ⟨z, _hz, rfl⟩
        have hvLater := originalCutFamily_piece_support_subset tail j hv
        have h := S.payload
        rcases h with ⟨_, _, _, _, _, _, hout, _⟩
        have hcover : χ e ∈ U ∨ χ e ∈ S.A.image (fun c => c.val) := by
          rcases hout e z.val v he z.property hvLater.1 hvLater.2 with hU | ⟨hc, hA⟩
          · exact Or.inl hU
          · exact Or.inr (Finset.mem_image.mpr ⟨⟨χ e, hc⟩, hA, rfl⟩)
        exact originalCutFamily_head_label_fresh_of_cover S tail e f hcover hf hfW
    | inr i =>
      cases j with
      | inl E =>
        change u ∈ tail.pieceSupport i at hu
        change v ∈ originalResidualHostPiece E at hv
        rcases hv with ⟨w, _hw, rfl⟩
        have huLater := originalCutFamily_piece_support_subset tail i hu
        have heSwap : e.val = s(w.val, u) := he.trans Sym2.eq_swap
        have h := S.payload
        rcases h with ⟨_, _, _, _, _, _, hout, _⟩
        have hcover : χ e ∈ U ∨ χ e ∈ S.A.image (fun c => c.val) := by
          rcases hout e w.val u heSwap w.property huLater.1 huLater.2 with hU | ⟨hc, hA⟩
          · exact Or.inl hU
          · exact Or.inr (Finset.mem_image.mpr ⟨⟨χ e, hc⟩, hA, rfl⟩)
        exact originalCutFamily_head_label_fresh_of_cover S tail e f hcover hf hfW
      | inr j =>
        have hijTail : i ≠ j := fun h => hij (congrArg Sum.inr h)
        have hfTail : f.val ∈ (originalCutFamilyGlobalRetainedGraph tail).edgeSet :=
          SimpleGraph.edgeSet_mono (originalCutFamily_global_cons_le_tail S tail) hf
        exact ih i j hijTail e u v he hu hv f hfTail hinside

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

theorem original_piece_copy_edge_inside
    {a : ℕ} {H : SimpleGraph (Fin n)} {X : Set (Fin n)}
    (A : (pathGraph a).Copy H) (hA : Set.range (fun u => A u) ⊆ X)
    (e : (pathGraph a).edgeSet) : EdgeInside X (A.mapEdgeSet e).val := by
  intro v hv
  change v ∈ Sym2.map A.toHom e.val at hv
  obtain ⟨u, _hu, huv⟩ := Sym2.mem_map.mp hv
  exact huv ▸ hA ⟨u, rfl⟩

theorem original_piece_edge_has_vertex (e : Sym2 (Fin n)) :
    ∃ v, v ∈ e := by
  induction e using Sym2.inductionOn with
  | _ u v => exact ⟨u, Sym2.mem_mk_left u v⟩

/-- The actual original graph supplies every color and disjointness fact
needed to append two paths in different actual retained pieces. The order of
each path is preserved, with the literal last-A / first-B complete-host edge.
Counts a and b are numbers of vertices; a=b=1 is permitted. -/
theorem originalCutFamily_rainbow_path_of_two_piece_paths
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots)
    (i j : F.PieceIndex) (hij : i ≠ j)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (A : (pathGraph a).Copy (originalCutFamilyGlobalRetainedGraph F))
    (B : (pathGraph b).Copy (originalCutFamilyGlobalRetainedGraph F))
    (hA : Set.range (fun u => A u) ⊆ F.pieceSupport i)
    (hB : Set.range (fun u => B u) ⊆ F.pieceSupport j) :
    ∃ P : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow P.toHom χ ∧
      (∀ u : Fin a, P (Fin.castAdd b u) = A u) ∧
      (∀ v : Fin b, P (Fin.natAdd a v) = B v) := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  have hH : H ≤ selectedGraph χ R :=
    SimpleGraph.deleteEdges_le (G := selectedGraph χ R)
      (originalCutFamilyLiftedCuts F : Set (Sym2 (Fin n)))
  let As : (pathGraph a).Copy (selectedGraph χ R) :=
    (Copy.ofLE H (selectedGraph χ R) hH).comp A
  let Bs : (pathGraph b).Copy (selectedGraph χ R) :=
    (Copy.ofLE H (selectedGraph χ R) hH).comp B
  let Ah : (pathGraph a).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp As
  let Bh : (pathGraph b).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp Bs
  have hAr : IsRainbow Ah.toHom χ := copy_in_selectedGraph_isRainbow χ R As
  have hBr : IsRainbow Bh.toHom χ := copy_in_selectedGraph_isRainbow χ R Bs
  have hs := originalCutFamily_piece_support_disjoint F i j hij
  have hdis : Disjoint (Set.range fun u : Fin a => Ah u)
      (Set.range fun v : Fin b => Bh v) := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact (Set.disjoint_left.mp hs) (hA hzA) (hB hzB)
  have hpal : ∀ e : (pathGraph a).edgeSet, ∀ d : (pathGraph b).edgeSet,
      χ (Ah.toHom.mapEdgeSet e) ≠ χ (Bh.toHom.mapEdgeSet d) := by
    intro e d heq
    have hselected : As.mapEdgeSet e = Bs.mapEdgeSet d := by
      apply selectedColor_injective χ R
      change χ (Ah.toHom.mapEdgeSet e) = χ (Bh.toHom.mapEdgeSet d)
      exact heq
    have hval : (A.mapEdgeSet e).val = (B.mapEdgeSet d).val :=
      congrArg (fun t : (selectedGraph χ R).edgeSet => t.val) hselected
    obtain ⟨v, hv⟩ := original_piece_edge_has_vertex (A.mapEdgeSet e).val
    have hvA := original_piece_copy_edge_inside A hA e v hv
    have hvB := original_piece_copy_edge_inside B hB d v (hval ▸ hv)
    exact (Set.disjoint_left.mp hs) hvA hvB
  let lastA : Fin a := ⟨a - 1, by omega⟩
  let firstB : Fin b := ⟨0, by omega⟩
  have hne : A lastA ≠ B firstB := by
    intro heq
    have hBj : A lastA ∈ F.pieceSupport j := by
      rw [heq]
      exact hB ⟨firstB, rfl⟩
    exact (Set.disjoint_left.mp hs) (hA ⟨lastA, rfl⟩)
      hBj
  let join : HostEdge n :=
    ⟨s(A lastA, B firstB), (SimpleGraph.top_adj _ _).mpr hne⟩
  have hjoin : join.val = s(Ah ⟨a - 1, by omega⟩, Bh ⟨0, by omega⟩) := rfl
  have hfreshA : ∀ e : (pathGraph a).edgeSet,
      χ (Ah.toHom.mapEdgeSet e) ≠ χ join := by
    intro e
    exact originalCutFamily_cross_piece_color_fresh F i j hij join
      (A lastA) (B firstB) rfl (hA ⟨lastA, rfl⟩) (hB ⟨firstB, rfl⟩)
      (Ah.toHom.mapEdgeSet e) (A.mapEdgeSet e).property
      (Or.inl (original_piece_copy_edge_inside A hA e))
  have hfreshB : ∀ d : (pathGraph b).edgeSet,
      χ (Bh.toHom.mapEdgeSet d) ≠ χ join := by
    intro d
    exact originalCutFamily_cross_piece_color_fresh F i j hij join
      (A lastA) (B firstB) rfl (hA ⟨lastA, rfl⟩) (hB ⟨firstB, rfl⟩)
      (Bh.toHom.mapEdgeSet d) (B.mapEdgeSet d).property
      (Or.inr (original_piece_copy_edge_inside B hB d))
  exact ErdosProblems.PathHighNewStageOne.rainbow_path_of_original_disjoint_paths_and_fresh_join
    ha hb χ Ah Bh hAr hBr hdis hpal join hjoin hfreshA hfreshB

/-- An original no-rainbow condition at the SUM length excludes the two
actual positive piece paths. Restricting a longer joined path to length k is
a separate prefix-copy application; no numerical path upper is asserted. -/
theorem originalCutFamily_no_rainbow_sum_excludes_two_piece_paths
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots)
    (i j : F.PieceIndex) (hij : i ≠ j)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hno : ∀ P : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ) :
    ¬ ∃ (A : (pathGraph a).Copy (originalCutFamilyGlobalRetainedGraph F))
      (B : (pathGraph b).Copy (originalCutFamilyGlobalRetainedGraph F)),
      (Set.range (fun u => A u) ⊆ F.pieceSupport i) ∧
      (Set.range (fun v => B v) ⊆ F.pieceSupport j) := by
  rintro ⟨A, B, hA, hB⟩
  obtain ⟨P, hP, _hPA, _hPB⟩ :=
    originalCutFamily_rainbow_path_of_two_piece_paths F i j hij ha hb A B hA hB
  exact hno P hP

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

def original_piece_path_prefix_copy {a b : ℕ} (hab : a ≤ b) :
    (pathGraph a).Copy (pathGraph b) where
  toHom :=
    { toFun := Fin.castLE hab
      map_rel' := by
        intro i j hij
        apply pathGraph_adj.mpr
        simpa only [Fin.val_castLE] using pathGraph_adj.mp hij }
  injective' := Fin.castLE_injective hab

theorem original_piece_rainbow_copy_comp
    {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (f : A.Copy B) (g : B.Copy (⊤ : SimpleGraph (Fin n)))
    (hg : IsRainbow g.toHom χ) :
    IsRainbow (g.comp f).toHom χ := by
  have hmap (e : A.edgeSet) :
      (g.comp f).toHom.mapEdgeSet e =
        g.toHom.mapEdgeSet (f.toHom.mapEdgeSet e) := by
    apply Subtype.ext
    simpa only [Copy.comp, Hom.mapEdgeSet, Hom.coe_comp] using
      (Sym2.map_map (f := f.toHom) (g := g.toHom) e.val).symm
  intro e d heq
  apply Hom.mapEdgeSet.injective f.toHom f.injective
  apply hg
  simpa only [EdgeLabeling.pullback_apply, hmap] using heq

/-- The original no-rainbow predicate forces the
combined VERTEX order of positive paths in any two different actual family
pieces to be strictly below k. The original connector and its two-path
freshness are derived by the prior actual-family theorem. No desired rainbow
copy, disjoint palette, freshness, or path-order conclusion is supplied. The prefix copy is valid for every natural k, including 0 and 1. -/
theorem originalCutFamily_two_piece_path_order_lt
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)} {k : ℕ}
    (F : OriginalResidualCutFamily χ R U W roots)
    (hno : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (i j : F.PieceIndex) (hij : i ≠ j)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (A : (pathGraph a).Copy (originalCutFamilyGlobalRetainedGraph F))
    (B : (pathGraph b).Copy (originalCutFamilyGlobalRetainedGraph F))
    (hA : Set.range (fun u => A u) ⊆ F.pieceSupport i)
    (hB : Set.range (fun u => B u) ⊆ F.pieceSupport j) :
    a + b < k := by
  by_contra hnot
  have hsum : k ≤ a + b := by omega
  obtain ⟨P, hP, _hleft, _hright⟩ :=
    originalCutFamily_rainbow_path_of_two_piece_paths F i j hij ha hb A B hA hB
  let f : (pathGraph k).Copy (pathGraph (a + b)) :=
    original_piece_path_prefix_copy hsum
  exact hno (P.comp f) (original_piece_rainbow_copy_comp χ f P hP)

end ErdosProblems.PathUpperReduction
