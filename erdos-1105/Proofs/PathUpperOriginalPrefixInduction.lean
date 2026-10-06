module

public import PathUpperOriginalPrefixOwners
public import PathUpperOriginalUncutTailJoin

@[expose] public section

/-!
Restrict the SAME original Fin-q coloring through an
arbitrary complete-host embedding, retaining ALL q original colors from their
actual R owners. Transfer no-rainbow ordinary copies and give the literal
Formal Conjectures antiRamseyNum sSup witness on the smaller/reindexed host. No m < n, k ≤ m, favorable palette, connectedness or numerical formula premise
is introduced. Properness and the induction regime remain separate obligations.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n m q : ℕ}

/-- The original complete-host coloring pulled through a vertex embedding.
The color type remains literally Fin q. -/
def originalPrefixRestrictedColoring
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (i : Fin m ↪ Fin n) :
    TopEdgeLabeling (Fin m) (Fin q) :=
  EdgeLabeling.pullback χ (SimpleGraph.Embedding.completeGraph i).toHom

/-- If all ORIGINAL representative owners lie in the
embedding range, this restricted coloring still uses EVERY original color. -/
theorem originalPrefixRestrictedColoring_surjective
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (i : Fin m ↪ Fin n)
    (howners : ∀ c : Fin q, EdgeInside (Set.range i) (R.edge c).val) :
    Function.Surjective (originalPrefixRestrictedColoring χ i) := by
  intro c
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective (R.edge c).val
  have huOwner : u ∈ (R.edge c).val := by
    rw [← huv]
    exact Sym2.mem_mk_left u v
  have hvOwner : v ∈ (R.edge c).val := by
    rw [← huv]
    exact Sym2.mem_mk_right u v
  obtain ⟨u', hu'⟩ := howners c u huOwner
  obtain ⟨v', hv'⟩ := howners c v hvOwner
  have huvNe : u ≠ v := by
    have htop : (⊤ : SimpleGraph (Fin n)).Adj u v := by
      have he := (R.edge c).property
      rw [← huv] at he
      exact he
    exact (SimpleGraph.top_adj u v).mp htop
  have hpreNe : u' ≠ v' := by
    intro h
    exact huvNe (hu'.symm.trans ((congrArg i h).trans hv'))
  let e : HostEdge m := ⟨s(u', v'), (SimpleGraph.top_adj u' v').mpr hpreNe⟩
  have hmap : (SimpleGraph.Embedding.completeGraph i).toHom.mapEdgeSet e =
      R.edge c := by
    apply Subtype.ext
    change Sym2.map i s(u', v') = (R.edge c).val
    rw [Sym2.map_mk, hu', hv']
    exact huv
  refine ⟨e, ?_⟩
  change χ ((SimpleGraph.Embedding.completeGraph i).toHom.mapEdgeSet e) = c
  rw [hmap]
  exact R.color_eq c

/-- A rainbow ordinary copy for the restricted original
coloring would compose with the complete-host embedding into the SAME original
coloring. No induced-copy or connectedness hypothesis is needed. -/
theorem originalPrefixRestrictedColoring_noRainbowCopy
    {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (i : Fin m ↪ Fin n)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ) :
    ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)),
      ¬ IsRainbow f.toHom (originalPrefixRestrictedColoring χ i) := by
  intro f hr
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    ((SimpleGraph.Embedding.completeGraph i).toCopy).comp f
  apply hno g
  intro e₁ e₂ heq
  apply hr
  have hcolor (e : H.edgeSet) :
      (EdgeLabeling.pullback χ g.toHom) e =
        (EdgeLabeling.pullback (originalPrefixRestrictedColoring χ i) f.toHom) e := by
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (g : α → Fin n) e.val =
      Sym2.map i (Sym2.map (f : α → Fin m) e.val)
    rw [Sym2.map_map]
    congr 1
  rw [hcolor e₁, hcolor e₂] at heq
  exact heq

/-- The direct literal bounded sSup witness. No reduced
image palette or unbounded-supremum shortcut is used. -/
theorem original_surjective_noRainbow_color_count_le_antiRamseyNum
    {α : Type*} [Fintype α] (H : SimpleGraph α)
    (φ : TopEdgeLabeling (Fin m) (Fin q)) (hφ : Function.Surjective φ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬ IsRainbow f.toHom φ) :
    q ≤ antiRamseyNum H m := by
  classical
  let A : Set ℕ :=
    {p | ∃ ψ : TopEdgeLabeling (Fin m) (Fin p), Function.Surjective ψ ∧
      ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬ IsRainbow f.toHom ψ}
  have hbounded : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin m)).edgeSet), ?_⟩
    intro p hp
    obtain ⟨ψ, hψ, _⟩ := hp
    simpa using Fintype.card_le_of_surjective ψ hψ
  have hmem : q ∈ A := ⟨φ, hφ, hno⟩
  change q ≤ sSup A
  exact le_csSup hbounded hmem

/-- Original owner confinement supplies the same full
Fin-q restricted coloring, its no-rainbow predicate, and the numeric witness. -/
theorem originalPrefixRestrictedColoring_full_witness
    {α : Type*} [Fintype α] (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (i : Fin m ↪ Fin n)
    (howners : ∀ c : Fin q, EdgeInside (Set.range i) (R.edge c).val)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ) :
    Function.Surjective (originalPrefixRestrictedColoring χ i) ∧
    (∀ f : H.Copy (⊤ : SimpleGraph (Fin m)),
      ¬ IsRainbow f.toHom (originalPrefixRestrictedColoring χ i)) ∧
    q ≤ antiRamseyNum H m := by
  have hsurj := originalPrefixRestrictedColoring_surjective χ R i howners
  have hrestricted := originalPrefixRestrictedColoring_noRainbowCopy H χ i hno
  exact ⟨hsurj, hrestricted,
    original_surjective_noRainbow_color_count_le_antiRamseyNum
      H (originalPrefixRestrictedColoring χ i) hsurj hrestricted⟩

/-- At an ACTUAL stage with FULL uncut tail edgeless,
restriction to its whole processed prefix retains ALL original colors and
gives q ≤ antiRamseyNum(Pk,m). No properness or k ≤ m is asserted. -/
theorem OriginalResidualCutStage.processed_prefix_color_count_le
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x)
    (htail : (selectedGraph χ R).induce (W \ componentSupport χ R x) = ⊥)
    (i : Fin m ↪ Fin n)
    (hrange : Set.range i = Wᶜ ∪ componentSupport χ R x)
    (hno : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    q ≤ antiRamseyNum (pathGraph k) m := by
  have howners : ∀ c : Fin q, EdgeInside (Set.range i) (R.edge c).val := by
    intro c
    rw [hrange]
    exact S.owner_inside_processed_prefix htail c
  exact (originalPrefixRestrictedColoring_full_witness
    (pathGraph k) χ R i howners hno).2.2

/-- The retained order k-2 endpoint derives FULL-tail
edgelessness internally, then supplies the same original full-palette
anti-Ramsey witness on the processed prefix. Even the last stage is allowed;
this does not prove that the processed prefix is a proper smaller host. -/
theorem OriginalResidualCutStage.processed_prefix_color_count_le_of_retained_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (i : Fin m ↪ Fin n)
    (hrange : Set.range i = Wᶜ ∪ componentSupport χ R x) :
    q ≤ antiRamseyNum (pathGraph k) m :=
  S.processed_prefix_color_count_le
    (S.uncut_tail_edgeless_of_retained_path_order hk P hno) i hrange hno

end ErdosProblems.PathUpperReduction

/-!
Exact new seam: the two-vertex HEAD edge is selected in FULL G and may be a
current cut edge. It is NOT assumed in S.retainedGraph. Q is a full-G path
on k-2 vertices in W minus WHOLE X. S.payload gives connector beta in U OR A;
PiecesV2.original_later_selected_edge_color_outside_removed_and_cut gives
beta freshness on Q. FULL representative selectedColor injection separates
the head color alpha from Q. If beta differs from alpha, checked HostToolsV4
joins P2 and Q into original rainbow Pk. Therefore beta=alpha. No selected
leaf, NEW or induction hypothesis is needed for this equality.

The selected-leaf premise is only used for replacement: every original
R-owner incident to leaf ell has color alpha. Then the SAME R.replace at the
literal connector has every original owner avoiding ell. Restriction through
the literal Fin.succAbove embedding retains the WHOLE original Fin-q palette and the
original noRainbow predicate, via PrefixInduction's exact full_witness API. This proves q<=antiRamseyNum(Pk,m) on Fin(m+1); no IH/formula, connectedness,
stability, proper processed-prefix or uniform full upper is claimed.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

def last_leaf_two_vertex_copy (G : SimpleGraph (Fin n))
    (ell h : Fin n) (hadj : G.Adj ell h) : (pathGraph 2).Copy G := by
  let f : Fin 2 → Fin n := fun i => if i = 0 then ell else h
  refine { toHom := { toFun := f, map_rel' := ?_ }, injective' := ?_ }
  · intro i j hij
    fin_cases i <;> fin_cases j
    · have h := pathGraph_adj.mp hij
      omega
    · simpa [f] using hadj
    · simpa [f] using hadj.symm
    · have h := pathGraph_adj.mp hij
      omega
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (G.ne_of_adj hadj (by simpa [f] using hij))
    · exact False.elim (G.ne_of_adj hadj (by simpa [f] using hij.symm))
    · rfl

theorem last_leaf_two_edge_value (d : (pathGraph 2).edgeSet) :
    d.val = s((0 : Fin 2), (1 : Fin 2)) := by
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective d.val
  change s(u, v) = d.val at huv
  have hadj : (pathGraph 2).Adj u v := by
    have hd := d.property
    rwa [← huv] at hd
  have hu := u.isLt
  have hv := v.isLt
  rcases pathGraph_adj.mp hadj with h | h
  · have hu0 : u = 0 := Fin.ext (by omega)
    have hv1 : v = 1 := Fin.ext (by omega)
    rw [← huv, hu0, hv1]
  · have hu1 : u = 1 := Fin.ext (by omega)
    have hv0 : v = 0 := Fin.ext (by omega)
    rw [← huv, hu1, hv0]
    exact Sym2.eq_swap

theorem last_leaf_path_edge_inside
    {a : ℕ} {G : SimpleGraph (Fin n)} {X : Set (Fin n)}
    (P : (pathGraph a).Copy G) (hP : Set.range (fun u => P u) ⊆ X)
    (e : (pathGraph a).edgeSet) : EdgeInside X (P.mapEdgeSet e).val := by
  intro v hv
  change v ∈ Sym2.map P.toHom e.val at hv
  obtain ⟨u, _hu, huv⟩ := Sym2.mem_map.mp hv
  exact huv ▸ hP ⟨u, rfl⟩

/-- The literal connector from ANY selected inside edge to an uncut tail
path of order k-2 must have that selected edge's original color. Head leaf
uniqueness and NEW are not assumed for this implication. -/
theorem OriginalResidualCutStage.last_leaf_connector_color_eq
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow F.toHom χ)
    (ell h : Fin n) (head : HostEdge n)
    (hhead : head.val ∈ (selectedGraph χ R).edgeSet)
    (hheadval : head.val = s(ell, h))
    (hellX : ell ∈ componentSupport χ R x) (hhX : h ∈ componentSupport χ R x)
    (Q : (pathGraph (k - 2)).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x)
    (join : HostEdge n) (hjoinval : join.val = s(h, Q ⟨0, by omega⟩)) :
    χ join = χ head := by
  classical
  by_contra hneq
  have hadj : (selectedGraph χ R).Adj ell h := by
    rw [hheadval] at hhead
    exact hhead
  let P := last_leaf_two_vertex_copy (selectedGraph χ R) ell h hadj
  let Ph : (pathGraph 2).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp P
  let Qh : (pathGraph (k - 2)).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ R) (⊤ : SimpleGraph (Fin n)) le_top).comp Q
  have hPX : Set.range (fun u => P u) ⊆ componentSupport χ R x := by
    rintro z ⟨u, rfl⟩
    change (if u = 0 then ell else h) ∈ componentSupport χ R x
    by_cases hu : u = 0
    · rw [ite_eq_left hu]
      exact hellX
    · rw [ite_eq_right hu]
      exact hhX
  have hdis : Disjoint (Set.range fun u : Fin 2 => Ph u)
      (Set.range fun v : Fin (k - 2) => Qh v) := by
    apply Set.disjoint_left.mpr
    intro v hvP hvQ
    exact (hQ hvQ).2 (hPX hvP)
  have hpal : ∀ d : (pathGraph 2).edgeSet, ∀ e : (pathGraph (k - 2)).edgeSet,
      χ (Ph.toHom.mapEdgeSet d) ≠ χ (Qh.toHom.mapEdgeSet e) := by
    intro d e heq
    have hselected : P.mapEdgeSet d = Q.mapEdgeSet e := by
      apply selectedColor_injective χ R
      change χ (Ph.toHom.mapEdgeSet d) = χ (Qh.toHom.mapEdgeSet e)
      exact heq
    have hval := congrArg (fun z : (selectedGraph χ R).edgeSet => z.val) hselected
    let v := (P.mapEdgeSet d).val.out.1
    have hv : v ∈ (P.mapEdgeSet d).val := Sym2.out_fst_mem _
    have hvX := last_leaf_path_edge_inside P hPX d v hv
    have hvQ := last_leaf_path_edge_inside Q hQ e v (hval ▸ hv)
    exact hvQ.2 hvX
  have hfreshP : ∀ d : (pathGraph 2).edgeSet,
      χ (Ph.toHom.mapEdgeSet d) ≠ χ join := by
    intro d
    have hhost : Ph.toHom.mapEdgeSet d = head := by
      apply Subtype.ext
      change Sym2.map Ph.toHom d.val = head.val
      rw [last_leaf_two_edge_value d, Sym2.map_mk]
      exact hheadval.symm
    rw [hhost]
    exact Ne.symm hneq
  have hcover : χ join ∈ U ∨ χ join ∈ S.A.image (fun c => c.val) := by
    have hdata := S.payload
    rcases hdata with ⟨_, _, _, _, _, _, hout, _⟩
    have hfirst := hQ ⟨(⟨0, by omega⟩ : Fin (k - 2)), rfl⟩
    rcases hout join h (Q ⟨0, by omega⟩) hjoinval hhX hfirst.1 hfirst.2 with
      hU | ⟨hc, hcA⟩
    · exact Or.inl hU
    · exact Or.inr (Finset.mem_image.mpr ⟨⟨χ join, hc⟩, hcA, rfl⟩)
  have hfreshQ : ∀ e : (pathGraph (k - 2)).edgeSet,
      χ (Qh.toHom.mapEdgeSet e) ≠ χ join := by
    intro e
    have havoid := original_later_selected_edge_color_outside_removed_and_cut
      χ R U W S.partition x S.support_subset S.maximum S.A
      (Qh.toHom.mapEdgeSet e) (Q.mapEdgeSet e).property
      (last_leaf_path_edge_inside Q hQ e)
    intro heq
    rcases hcover with hU | hA
    · apply havoid.1
      rw [heq]
      exact hU
    · apply havoid.2
      rw [heq]
      exact hA
  have hjoin : join.val = s(Ph ⟨2 - 1, by omega⟩, Qh ⟨0, by omega⟩) := by
    change join.val = s(h, Q ⟨0, by omega⟩)
    exact hjoinval
  obtain ⟨F, hF, _hleft, _hright⟩ :=
    ErdosProblems.PathHighNewStageOne.rainbow_path_of_original_disjoint_paths_and_fresh_join
      (by omega) (by omega) χ Ph Qh (copy_in_selectedGraph_isRainbow χ R P)
      (copy_in_selectedGraph_isRainbow χ R Q) hdis hpal join hjoin hfreshP hfreshQ
  have hlen : 2 + (k - 2) = k := by omega
  have hbad : ∃ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow F.toHom χ := by
    exact Eq.mp
      (congrArg (fun t : ℕ => ∃ F : (pathGraph t).Copy (⊤ : SimpleGraph (Fin n)),
        IsRainbow F.toHom χ) hlen) ⟨F, hF⟩
  obtain ⟨F', hF'⟩ := hbad
  exact hno F' hF'

/-- The ordinary selected-neighbor uniqueness premise implies the exact
owner-color leaf premise. It makes no original NEW-color assertion. -/
theorem original_owner_color_of_unique_selected_neighbor
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (ell h : Fin n) (head : HostEdge n) (hheadval : head.val = s(ell, h))
    (hleaf : ∀ v : Fin n, (selectedGraph χ R).Adj ell v → v = h) :
    ∀ c : Fin q, ell ∈ (R.edge c).val → c = χ head := by
  intro c hc
  obtain ⟨v, howner⟩ := Sym2.mem_iff_exists.mp hc
  have heG : (R.edge c).val ∈ (selectedGraph χ R).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, rfl⟩
  have hadj : (selectedGraph χ R).Adj ell v := by
    rw [howner] at heG
    exact heG
  have hv : v = h := hleaf v hadj
  have heq : R.edge c = head := by
    apply Subtype.ext
    rw [howner, hv]
    exact hheadval.symm
  exact (R.color_eq c).symm.trans (congrArg χ heq)

/-- Exact owner-leaf uniqueness is sufficient to remove every selected owner
from ell after replacing alpha with another original alpha edge avoiding ell. -/
theorem original_replace_avoids_selected_leaf
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (ell : Fin n) (head join : HostEdge n)
    (hleaf : ∀ c : Fin q, ell ∈ (R.edge c).val → c = χ head)
    (hcolor : χ join = χ head) (havoid : ell ∉ join.val) :
    ∀ c : Fin q, ell ∉ ((R.replace join).edge c).val := by
  intro c
  by_cases hc : c = χ join
  · subst c
    rw [R.replace_edge_same join]
    exact havoid
  · rw [R.replace_edge_other join hc]
    intro hmem
    exact hc ((hleaf c hmem).trans hcolor.symm)

/-- A selected leaf inside an earlier WHOLE component can be omitted from
the host while retaining ALL q original colors, provided the literal uncut
outside path has k-2 vertices. The bound is antiRamseyNum on the m-vertex
restriction, not an assumed numerical formula or induction hypothesis. -/
theorem OriginalResidualCutStage.last_leaf_color_count_le
    {m : ℕ} {χ : TopEdgeLabeling (Fin (m + 1)) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin (m + 1))} {x : Fin (m + 1)} {k : ℕ}
    (S : OriginalResidualCutStage χ R U W x) (hk : 3 ≤ k)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin (m + 1))), ¬ IsRainbow F.toHom χ)
    (ell h : Fin (m + 1)) (head : HostEdge (m + 1))
    (hhead : head.val ∈ (selectedGraph χ R).edgeSet)
    (hheadval : head.val = s(ell, h))
    (hellX : ell ∈ componentSupport χ R x) (hhX : h ∈ componentSupport χ R x)
    (hleaf : ∀ c : Fin q, ell ∈ (R.edge c).val → c = χ head)
    (Q : (pathGraph (k - 2)).Copy (selectedGraph χ R))
    (hQ : Set.range (fun v => Q v) ⊆ W \ componentSupport χ R x)
    (join : HostEdge (m + 1)) (hjoinval : join.val = s(h, Q ⟨0, by omega⟩)) :
    q ≤ antiRamseyNum (pathGraph k) m := by
  have hcolor := S.last_leaf_connector_color_eq hk hno ell h head hhead hheadval
    hellX hhX Q hQ join hjoinval
  have hadj : (selectedGraph χ R).Adj ell h := by
    rw [hheadval] at hhead
    exact hhead
  have havoid : ell ∉ join.val := by
    intro hmem
    rw [hjoinval] at hmem
    rcases Sym2.mem_iff.mp hmem with heqh | heqQ
    · exact (selectedGraph χ R).ne_of_adj hadj heqh
    · have hfirst := hQ ⟨(⟨0, by omega⟩ : Fin (k - 2)), rfl⟩
      apply hfirst.2
      exact heqQ ▸ hellX
  have hav := original_replace_avoids_selected_leaf χ R ell head join hleaf hcolor havoid
  let i : Fin m ↪ Fin (m + 1) := ⟨ell.succAbove, Fin.succAbove_right_injective⟩
  have hrange : Set.range i = {ell}ᶜ := Fin.range_succAbove ell
  have howners : ∀ c : Fin q, EdgeInside (Set.range i) ((R.replace join).edge c).val := by
    intro c v hv
    rw [hrange]
    have hvne : v ≠ ell := by
      intro hveq
      subst v
      exact hav c hv
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hvne
  exact (originalPrefixRestrictedColoring_full_witness
    (pathGraph k) χ (R.replace join) i howners hno).2.2

end ErdosProblems.PathUpperReduction
