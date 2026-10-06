module

public import PathUpperOriginalPieceFreshness
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
An actual retained head path joins a path in the FULL
original selected graph outside that stage's WHOLE component, before later
cuts. The SAME original chi/full R and arbitrary prefix U are preserved. There is no freshness, disjoint-palette, global retained graph or favorable
endpoint premise. Singletons are included; a and b count vertices.

Those PRIVATE names cannot be called from another module. Their containing
high-NEW capstone is not used: its hypotheses do not fit this full-R target.

Scope: exact stage join, noRainbow(Pk) order exclusion, and FULL uncut tail
edgelessness at retained order k-2. A last nontrivial stage can have empty
tail, so no proper processed-prefix or full connected-representative/upper
bound conclusion is asserted.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

theorem uncut_tail_copy_edge_inside
    {a : ℕ} {G : SimpleGraph (Fin n)} {X : Set (Fin n)}
    (P : (pathGraph a).Copy G) (hP : Set.range (fun u => P u) ⊆ X)
    (e : (pathGraph a).edgeSet) : EdgeInside X (P.mapEdgeSet e).val := by
  intro v hv
  change v ∈ Sym2.map P.toHom e.val at hv
  obtain ⟨u, _hu, huv⟩ := Sym2.mem_map.mp hv
  exact huv ▸ hP ⟨u, rfl⟩

def uncut_tail_path_prefix_copy {a b : ℕ} (hab : a ≤ b) :
    (pathGraph a).Copy (pathGraph b) where
  toHom :=
    { toFun := Fin.castLE hab
      map_rel' := by
        intro i j hij
        apply pathGraph_adj.mpr
        simpa only [Fin.val_castLE] using pathGraph_adj.mp hij }
  injective' := Fin.castLE_injective hab

theorem uncut_tail_rainbow_copy_comp
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

/-- Join a positive retained-head path to a positive FULL-selected-graph tail
path. The actual tail contains all selected edges, including later cut owners.
The original host copy preserves both orders and has a+b vertices. -/
theorem OriginalResidualCutStage.uncut_tail_rainbow_path
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n}
    (S : OriginalResidualCutStage χ R U W x)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (P : (pathGraph a).Copy S.retainedGraph)
    (Q : (pathGraph b).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x) :
    ∃ F : (pathGraph (a + b)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow F.toHom χ ∧
      (∀ u : Fin a, F (Fin.castAdd b u) = (P u).val) ∧
      (∀ v : Fin b, F (Fin.natAdd a v) = Q v) := by
  classical
  let Ps : (pathGraph a).Copy (selectedGraph χ R) :=
    { toHom :=
        { toFun := fun u => (P u).val
          map_rel' := by
            intro u v huv
            exact (SimpleGraph.deleteEdges_adj.mp (P.toHom.map_rel' huv)).1 }
      injective' := by
        intro u v huv
        apply P.injective
        exact Subtype.ext huv }
  let Ph : (pathGraph a).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp Ps
  let Qh : (pathGraph b).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp Q
  have hPr : IsRainbow Ph.toHom χ := copy_in_selectedGraph_isRainbow χ R Ps
  have hQr : IsRainbow Qh.toHom χ := copy_in_selectedGraph_isRainbow χ R Q
  have hPX : Set.range (fun u => Ps u) ⊆ componentSupport χ R x := by
    rintro v ⟨u, rfl⟩
    exact (P u).property
  have hdis : Disjoint (Set.range fun u : Fin a => Ph u)
      (Set.range fun v : Fin b => Qh v) := by
    apply Set.disjoint_left.mpr
    intro v hvP hvQ
    exact (hQ hvQ).2 (hPX hvP)
  have hpal : ∀ e : (pathGraph a).edgeSet, ∀ d : (pathGraph b).edgeSet,
      χ (Ph.toHom.mapEdgeSet e) ≠ χ (Qh.toHom.mapEdgeSet d) := by
    intro e d heq
    have hselected : Ps.mapEdgeSet e = Q.mapEdgeSet d := by
      apply selectedColor_injective χ R
      change χ (Ph.toHom.mapEdgeSet e) = χ (Qh.toHom.mapEdgeSet d)
      exact heq
    have hval : (Ps.mapEdgeSet e).val = (Q.mapEdgeSet d).val :=
      congrArg (fun z : (selectedGraph χ R).edgeSet => z.val) hselected
    let v := (Ps.mapEdgeSet e).val.out.1
    have hv : v ∈ (Ps.mapEdgeSet e).val := Sym2.out_fst_mem _
    have hvX := uncut_tail_copy_edge_inside Ps hPX e v hv
    have hvTail := uncut_tail_copy_edge_inside Q hQ d v (hval ▸ hv)
    exact hvTail.2 hvX
  let lastP : Fin a := ⟨a - 1, by omega⟩
  let firstQ : Fin b := ⟨0, by omega⟩
  have hlast : (P lastP).val ∈ componentSupport χ R x := (P lastP).property
  have hfirst : Q firstQ ∈ W \ componentSupport χ R x := hQ ⟨firstQ, rfl⟩
  have hne : (P lastP).val ≠ Q firstQ := by
    intro heq
    apply hfirst.2
    rw [← heq]
    exact hlast
  let join : HostEdge n :=
    ⟨s((P lastP).val, Q firstQ), (SimpleGraph.top_adj _ _).mpr hne⟩
  have hjoin : join.val = s(Ph ⟨a - 1, by omega⟩, Qh ⟨0, by omega⟩) := rfl
  have hcover : χ join ∈ U ∨ χ join ∈ S.A.image (fun c => c.val) := by
    have h := S.payload
    rcases h with ⟨_, _, _, _, _, _, hout, _⟩
    rcases hout join (P lastP).val (Q firstQ) rfl hlast hfirst.1 hfirst.2 with
      hU | ⟨hc, hcA⟩
    · exact Or.inl hU
    · exact Or.inr (Finset.mem_image.mpr ⟨⟨χ join, hc⟩, hcA, rfl⟩)
  have hfreshP : ∀ e : (pathGraph a).edgeSet,
      χ (Ph.toHom.mapEdgeSet e) ≠ χ join := by
    intro e
    obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.val
    change s(u, v) = e.val at huv
    have hadj : (pathGraph a).Adj u v := by
      have he := e.property
      rwa [← huv] at he
    have hval : (Ph.toHom.mapEdgeSet e).val = s((P u).val, (P v).val) := by
      change Sym2.map (fun z : Fin a => (P z).val) e.val = _
      rw [← huv, Sym2.map_mk]
    have hBset : (S.B : Set (Sym2 (componentSupport χ R x))) =
        OriginalResidualColorDeletion χ R U (componentSupport χ R x) (S.A : Set _) := by
      have h := S.payload
      rcases h with ⟨_, hBset, _⟩
      exact hBset
    have havoid := original_retained_edge_color_outside_removed_and_cut
      χ R U W S.partition (componentSupport χ R x) S.support_subset S.A S.B hBset
      (P u) (P v) (P.toHom.map_rel' hadj) (Ph.toHom.mapEdgeSet e) hval
    intro heq
    rcases hcover with hU | hA
    · apply havoid.1
      rw [heq]
      exact hU
    · apply havoid.2
      rw [heq]
      exact hA
  have hfreshQ : ∀ d : (pathGraph b).edgeSet,
      χ (Qh.toHom.mapEdgeSet d) ≠ χ join := by
    intro d
    have havoid := original_later_selected_edge_color_outside_removed_and_cut
      χ R U W S.partition x S.support_subset S.maximum S.A
      (Qh.toHom.mapEdgeSet d) (Q.mapEdgeSet d).property
      (uncut_tail_copy_edge_inside Q hQ d)
    intro heq
    rcases hcover with hU | hA
    · apply havoid.1
      rw [heq]
      exact hU
    · apply havoid.2
      rw [heq]
      exact hA
  exact ErdosProblems.PathHighNewStageOne.rainbow_path_of_original_disjoint_paths_and_fresh_join
    ha hb χ Ph Qh hPr hQr hdis hpal join hjoin hfreshP hfreshQ

/-- Original noRainbow(Pk) limits a retained head path plus an UNCUT full-G
tail path. No positivity or host-size premise beyond the two supplied paths
is silently added; truncation works for arbitrary natural k. -/
theorem OriginalResidualCutStage.uncut_tail_path_order_lt
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (P : (pathGraph a).Copy S.retainedGraph)
    (Q : (pathGraph b).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x) :
    a + b < k := by
  by_contra hnot
  have hsum : k ≤ a + b := by omega
  obtain ⟨F, hF, _hleft, _hright⟩ := S.uncut_tail_rainbow_path ha hb P Q hQ
  let prefCopy : (pathGraph k).Copy (pathGraph (a + b)) := uncut_tail_path_prefix_copy hsum
  exact hno (F.comp prefCopy) (uncut_tail_rainbow_copy_comp χ prefCopy F hF)

/-- A retained head path on k-2 vertices forces the FULL selected graph on
the remaining W minus WHOLE X to be edgeless, before any later cuts. It does
not imply that the processed prefix is proper or that G is connected. -/
theorem OriginalResidualCutStage.uncut_tail_edgeless_of_retained_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow F.toHom χ) :
    (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥ := by
  classical
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro u v huv
  have hne : u.val ≠ v.val := (selectedGraph χ R).ne_of_adj huv
  let f : Fin 2 → Fin n := fun i => if i = 0 then u.val else v.val
  let Q : (pathGraph 2).Copy (selectedGraph χ R) :=
    { toHom :=
        { toFun := f
          map_rel' := by
            intro i j hij
            fin_cases i <;> fin_cases j
            · have h := pathGraph_adj.mp hij
              omega
            · simpa [f] using huv
            · simpa [f] using huv.symm
            · have h := pathGraph_adj.mp hij
              omega }
      injective' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim (hne (by simpa [f] using hij))
        · exact False.elim (hne (by simpa [f] using hij.symm))
        · rfl }
  have hQ : Set.range (fun i => Q i) ⊆ W \ componentSupport χ R x := by
    rintro z ⟨i, rfl⟩
    change (if i = 0 then u.val else v.val) ∈ W \ componentSupport χ R x
    by_cases hi : i = 0
    · rw [ite_eq_left hi]
      exact u.property
    · rw [ite_eq_right hi]
      exact v.property
  have hlt := S.uncut_tail_path_order_lt hno (a := k - 2) (b := 2)
    (by omega) (by omega) P Q hQ
  omega

end ErdosProblems.PathUpperReduction
