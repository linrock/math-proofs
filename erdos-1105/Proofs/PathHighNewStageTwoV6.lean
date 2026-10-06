module

public import CycleOriginalCrossComponentPaletteExclusionV3
public import PathHighNewHostPathToolsV4
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.SuccPred

@[expose] public section

/-! Stage 2 high-NEW cross-component path assembly on the original coloring. -/

namespace ErdosProblems.PathHighNewStageTwo

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion
open ErdosProblems.PathHighNewStageOne

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem component_hamiltonian_cycle_selected_path
    (G : SimpleGraph (Fin n)) (D : G.ConnectedComponent)
    (u : D) (c : D.toSimpleGraph.Walk u u) (hc : c.IsHamiltonianCycle) :
    ∃ f : (pathGraph D.supp.ncard).Copy G, ∀ i, f i ∈ D.supp := by
  classical
  let : Fintype D := Fintype.ofFinite D
  have hcard : Fintype.card D = D.supp.ncard := by
    calc
      Fintype.card D = Nat.card D := Fintype.card_eq_nat_card
      _ = D.supp.ncard := Nat.card_coe_set_eq D.supp
  have horder : c.dropLast.length + 1 = D.supp.ncard := by
    calc
      c.dropLast.length + 1 = c.length :=
        Walk.length_dropLast_add_one hc.isCycle.not_nil
      _ = Fintype.card D := hc.length_eq
      _ = D.supp.ncard := hcard
  let p : (pathGraph D.supp.ncard).Copy D.toSimpleGraph :=
    horder ▸ hc.isCycle.isPath_dropLast.pathGraphCopy
  refine ⟨(Copy.induce G D.supp).comp p, ?_⟩
  intro i
  exact (p i).property

theorem selected_edge_color_mem_new_union
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : (selectedGraph χ r).edgeSet) :
    restrictedColor χ r e ∈ newColorUnion χ := by
  have hm : e.val ∈ Set.range fun c : newColorUnion χ => (r.edge c).val := by
    rw [← selectedGraph_edgeSet χ r]
    exact e.property
  obtain ⟨c, hc⟩ := hm
  have he : (⟨e.val, edgeSet_mono le_top e.property⟩ : HostEdge n) = r.edge c :=
    Subtype.ext hc.symm
  change χ ⟨e.val, edgeSet_mono le_top e.property⟩ ∈ newColorUnion χ
  rw [he, r.color_eq]
  exact c.property

theorem host_color_of_selected_copy
    {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (f : H.Copy (selectedGraph χ r)) (e : H.edgeSet) :
    χ (((Copy.ofLE (selectedGraph χ r)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom.mapEdgeSet e) =
      restrictedColor χ r (f.mapEdgeSet e) := by
  exact congrArg χ (Subtype.ext rfl)

theorem selected_component_path_palettes_disjoint
    {a b : ℕ} (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (D E : (selectedGraph χ r).ConnectedComponent) (hDE : D ≠ E)
    (A : (pathGraph a).Copy (selectedGraph χ r))
    (B : (pathGraph b).Copy (selectedGraph χ r))
    (hA : ∀ i, A i ∈ D.supp) (hB : ∀ j, B j ∈ E.supp) :
    ∀ e : (pathGraph a).edgeSet, ∀ d : (pathGraph b).edgeSet,
      restrictedColor χ r (A.mapEdgeSet e) ≠
        restrictedColor χ r (B.mapEdgeSet d) := by
  intro e d heq
  have hdis := (selectedGraph χ r).pairwise_disjoint_supp_connectedComponent hDE
  have hedges := congrArg
    (fun q : (selectedGraph χ r).edgeSet => q.val)
    (restrictedColor_injective χ r heq)
  obtain ⟨⟨i, j⟩, hij⟩ := Sym2.mk_surjective e.val
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective d.val
  change Sym2.map A e.val = Sym2.map B d.val at hedges
  rw [← hij, ← huv] at hedges
  change s(A i, A j) = s(B u, B v) at hedges
  rcases Sym2.eq_iff.mp hedges with h | h
  · have hboth : A i ∈ E.supp := h.1.symm ▸ hB u
    exact Set.disjoint_left.mp hdis (hA i) hboth
  · have hboth : A i ∈ E.supp := h.1.symm ▸ hB v
    exact Set.disjoint_left.mp hdis (hA i) hboth

def path_prefix_copy {a b : ℕ} (hab : a ≤ b) :
    (pathGraph a).Copy (pathGraph b) where
  toHom :=
    { toFun := Fin.castLE hab
      map_rel' := by
        intro i j hij
        apply pathGraph_adj.mpr
        simpa only [Fin.val_castLE] using pathGraph_adj.mp hij }
  injective' := Fin.castLE_injective hab

omit [DecidableEq C] in
theorem rainbow_copy_comp
    {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}
    (χ : TopEdgeLabeling (Fin n) C)
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

/-- Every-vertex high NEW and the literal odd-cycle exclusion force an
original rainbow even path. All component bounds, paths and palette
conditions used below are derived for the same canonical NEW choice. -/
theorem rainbow_even_path_of_high_new_and_no_odd_cycle
    {ell : ℕ} (χ : TopEdgeLabeling (Fin n) C)
    (hell : 2 ≤ ell) (hn : 2 * ell + 2 ≤ n)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card)
    (hno : ∀ f : (cycleGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    ∃ f : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  classical
  let r : NewChoice χ := canonicalChoice χ
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  have hk : 5 ≤ 2 * ell + 1 := by omega
  have hnew2 : ∀ v : Fin n, 2 ≤ (newColors χ v).card := by
    intro v
    exact hell.trans (hnew v)
  have hpair : ∀ u v : Fin n, u ≠ v →
      (2 * ell + 1) - 1 ≤ (newColors χ u).card + (newColors χ v).card := by
    intro u v _
    have hu := hnew u
    have hv := hnew v
    omega
  let v0 : Fin n := ⟨0, by omega⟩
  let D : G.ConnectedComponent := G.connectedComponentMk v0
  obtain ⟨hD3, hDlow, hDup, _, hDHam⟩ :=
    selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew2 hpair hno D
  have houtside : ∃ w : Fin n, w ∉ D.supp := by
    by_contra! hfull
    have hset : D.supp = Set.univ := Set.eq_univ_of_forall hfull
    have hcard : D.supp.ncard = n := by simp only [hset, Set.ncard_univ, Nat.card_fin]
    omega
  obtain ⟨w, hw⟩ := houtside
  let E : G.ConnectedComponent := G.connectedComponentMk w
  have hwE : w ∈ E.supp := ConnectedComponent.connectedComponentMk_mem
  have hDE : D ≠ E := by
    intro h
    exact hw (h.symm ▸ hwE)
  obtain ⟨hE3, hElow, _, _, hEHam⟩ :=
    selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew2 hpair hno E
  obtain ⟨uD, cD, hcD⟩ := hDHam
  obtain ⟨uE, cE, hcE⟩ := hEHam
  obtain ⟨fD, hfD⟩ := component_hamiltonian_cycle_selected_path G D uD cD hcD
  obtain ⟨fE, hfE⟩ := component_hamiltonian_cycle_selected_path G E uE cE hcE
  let A : (pathGraph D.supp.ncard).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fD
  let B : (pathGraph E.supp.ncard).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fE
  have hArainbow : IsRainbow A.toHom χ := copy_in_selectedGraph_isRainbow χ r fD
  have hBrainbow : IsRainbow B.toHom χ := copy_in_selectedGraph_isRainbow χ r fE
  have hAmem (i : Fin D.supp.ncard) : A i ∈ D.supp := hfD i
  have hBmem (j : Fin E.supp.ncard) : B j ∈ E.supp := hfE j
  have hdis := G.pairwise_disjoint_supp_connectedComponent hDE
  have hArange : Set.range (fun i : Fin D.supp.ncard => A i) ⊆ D.supp := by
    rintro x ⟨i, rfl⟩
    exact hAmem i
  have hBrange : Set.range (fun j : Fin E.supp.ncard => B j) ⊆ E.supp := by
    rintro x ⟨j, rfl⟩
    exact hBmem j
  have hpathsDis := hdis.mono hArange hBrange
  have hpalette : ∀ e : (pathGraph D.supp.ncard).edgeSet,
      ∀ d : (pathGraph E.supp.ncard).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ (B.toHom.mapEdgeSet d) := by
    intro e d
    change χ (((Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fD).toHom.mapEdgeSet e) ≠
      χ (((Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fE).toHom.mapEdgeSet d)
    rw [host_color_of_selected_copy χ r fD e, host_color_of_selected_copy χ r fE d]
    exact selected_component_path_palettes_disjoint χ r D E hDE fD fE hfD hfE e d
  have hDa : 1 ≤ D.supp.ncard := by omega
  have hEb : 1 ≤ E.supp.ncard := by omega
  let u : Fin n := A ⟨D.supp.ncard - 1, by omega⟩
  let v : Fin n := B ⟨0, by omega⟩
  have hu : u ∈ D.supp := hAmem _
  have hv : v ∈ E.supp := hBmem _
  have huv : u ≠ v := by
    intro h
    exact Set.disjoint_left.mp hdis hu (h.symm ▸ hv)
  let join : HostEdge n := ⟨s(u, v), by exact (⊤ : SimpleGraph (Fin n)).mem_edgeSet.mpr ((top_adj u v).mpr huv)⟩
  have hjcolor : χ join ∉ newColorUnion χ :=
    cross_edge_color_not_new_union hk χ r hnew2 hpair hno D E hDE u v hu hv join rfl
  have hfreshA : ∀ e : (pathGraph D.supp.ncard).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ join := by
    intro e heq
    apply hjcolor
    rw [← heq]
    change χ (((Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fD).toHom.mapEdgeSet e) ∈ _
    rw [host_color_of_selected_copy χ r fD e]
    exact selected_edge_color_mem_new_union χ r (fD.mapEdgeSet e)
  have hfreshB : ∀ d : (pathGraph E.supp.ncard).edgeSet,
      χ (B.toHom.mapEdgeSet d) ≠ χ join := by
    intro d heq
    apply hjcolor
    rw [← heq]
    change χ (((Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp fE).toHom.mapEdgeSet d) ∈ _
    rw [host_color_of_selected_copy χ r fE d]
    exact selected_edge_color_mem_new_union χ r (fE.mapEdgeSet d)
  obtain ⟨f, hf, _, _⟩ :=
    rainbow_path_of_original_disjoint_paths_and_fresh_join hDa hEb χ A B
      hArainbow hBrainbow hpathsDis hpalette join rfl hfreshA hfreshB
  have hsum : 2 * ell + 2 ≤ D.supp.ncard + E.supp.ncard := by omega
  exact ⟨f.comp (path_prefix_copy hsum), rainbow_copy_comp χ (path_prefix_copy hsum) f hf⟩

end ErdosProblems.PathHighNewStageTwo
