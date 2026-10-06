module

public import EvenFamilyOwnerCopyV4
public import PathUpperRainbowBridge

@[expose] public section

/-! An exact actual selected-family hypothesis yields an original rainbow path. No classification, numeric upper bound, or universal path conclusion is claimed. -/

namespace ErdosProblems.EvenExceptionExchange
open SimpleGraph
open ErdosProblems.PathUpperReduction

def bbHostEdge {a b n : ℕ} (phi : Vertex a b ≃ Fin n)
    (u v : Fin b) (huv : u ≠ v) : HostEdge n := by
  let U : Vertex a b := Sum.inr (Sum.inr u)
  let V : Vertex a b := Sum.inr (Sum.inr v)
  have hUV : U ≠ V := by
    intro h
    exact huv (Sum.inr.inj (Sum.inr.inj h))
  refine ⟨s(phi U, phi V), ?_⟩
  apply (SimpleGraph.mem_edgeSet _).mpr
  simpa only [SimpleGraph.top_adj] using phi.injective.ne hUV

/-- An ordinary path in the ACTUAL replacement representative, under a literal
pullback equality for the ACTUAL original selected graph. The removed edge is
exactly the selected edge of the color of the inserted B-B host edge. -/
noncomputable def replacement_path_copy_of_selected_comap_eq_family
    {n q : ℕ} (a b : ℕ) (ha : 2 ≤ a) (hab : a + 1 ≤ b)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (phi : Vertex a b ≃ Fin n)
    (hselected : (selectedGraph chi r).comap phi = familyGraph a b)
    (u v : Fin b) (huv : u ≠ v) :
    (pathGraph (2 * a + 4)).Copy
      (selectedGraph chi (r.replace (bbHostEdge phi u v huv))) := by
  classical
  let chordEdge : HostEdge n := bbHostEdge phi u v huv
  let U : Vertex a b := Sum.inr (Sum.inr u)
  let V : Vertex a b := Sum.inr (Sum.inr v)
  let old : HostEdge n := r.edge (chi chordEdge)
  have holdmem : old.val ∈ (selectedGraph chi r).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨chi chordEdge, rfl⟩
  let oldSelected : (selectedGraph chi r).edgeSet := ⟨old.val, holdmem⟩
  let back : (selectedGraph chi r).Copy (familyGraph a b) := by
    refine ⟨⟨phi.symm, ?_⟩, phi.symm.injective⟩
    intro x y hxy
    rw [← hselected]
    change (selectedGraph chi r).Adj (phi (phi.symm x)) (phi (phi.symm y))
    simpa only [Equiv.apply_symm_apply] using hxy
  let owner : (familyGraph a b).edgeSet := back.mapEdgeSet oldSelected
  have howner : owner.val = Sym2.map phi.symm old.val := rfl
  let T : SimpleGraph (Vertex a b) :=
    (familyGraph a b).deleteEdges {owner.val} ⊔
      SimpleGraph.fromEdgeSet {s(U,V)}
  let forward : T.Copy (selectedGraph chi (r.replace chordEdge)) := by
    refine ⟨⟨phi, ?_⟩, phi.injective⟩
    intro x y hxy
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hxy with hretain | hnew
    · have hdelete := SimpleGraph.deleteEdges_adj.mp hretain
      have hfamily : (familyGraph a b).Adj x y := hdelete.1
      have hselectedXY : (selectedGraph chi r).Adj (phi x) (phi y) := by
        change ((selectedGraph chi r).comap phi).Adj x y
        rw [hselected]
        exact hfamily
      have hownerNe : s(x,y) ≠ owner.val := by
        simpa only [Set.mem_singleton_iff] using hdelete.2
      have holdNe : s(phi x,phi y) ≠ old.val := by
        intro heq
        apply hownerNe
        have hpull := congrArg (Sym2.map phi.symm) heq
        rw [howner]
        change s(phi.symm (phi x),phi.symm (phi y)) =
          Sym2.map phi.symm old.val at hpull
        simpa only [Equiv.symm_apply_apply] using hpull
      apply delete_selectedEdge_le_replace chi r chordEdge
      apply SimpleGraph.deleteEdges_adj.mpr
      exact ⟨hselectedXY, by simpa only [Set.mem_singleton_iff] using holdNe⟩
    · have hchord : s(x,y) = s(U,V) := by
        simpa only [Set.mem_singleton_iff] using
          ((SimpleGraph.fromEdgeSet_adj {s(U,V)}).mp hnew).1
      have hmap : s(phi x,phi y) = chordEdge.val := by
        change Sym2.map phi s(x,y) = Sym2.map phi s(U,V)
        exact congrArg (Sym2.map phi) hchord
      have hmem := replacedEdge_mem chi r chordEdge
      apply (SimpleGraph.mem_edgeSet _).mp
      rw [hmap]
      exact hmem
  let familyCopy := path_copy_after_actual_owner_exchange a b ha hab owner u v huv
  exact forward.comp familyCopy

/-- The same exact-family replacement gives a rainbow path for the ORIGINAL
complete-host coloring chi. No favorable owner or replacement coloring is used. -/
theorem exists_original_rainbow_path_of_selected_comap_eq_family
    {n q : ℕ} (a b : ℕ) (ha : 2 ≤ a) (hab : a + 1 ≤ b)
    (chi : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice chi)
    (phi : Vertex a b ≃ Fin n)
    (hselected : (selectedGraph chi r).comap phi = familyGraph a b)
    (u v : Fin b) (huv : u ≠ v) :
    ∃ f : (pathGraph (2 * a + 4)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom chi := by
  classical
  let e : HostEdge n := bbHostEdge phi u v huv
  let f := replacement_path_copy_of_selected_comap_eq_family
    a b ha hab chi r phi hselected u v huv
  exact ⟨(Copy.ofLE (selectedGraph chi (r.replace e))
    (⊤ : SimpleGraph (Fin n)) le_top).comp f,
    copy_in_selectedGraph_isRainbow chi (r.replace e) f⟩

end ErdosProblems.EvenExceptionExchange
