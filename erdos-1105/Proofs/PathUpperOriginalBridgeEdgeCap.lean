module

public import PathUpperOriginalPrefixInduction
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

/-!
Uniform finite bridge edge cap and palette/domain bounds for a proper first
component in the residual decomposition.

These supply the proper-set upper bound while the retained-path endpoint
supplies the independent lower bound.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

theorem choose_two_positive_cap
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    s.choose 2 + t.choose 2 ≤ (s + t - 1).choose 2 := by
  let x := s - 1
  let y := t - 1
  have hsx : s = x + 1 := by dsimp [x]; omega
  have hty : t = y + 1 := by dsimp [y]; omega
  have hshift : s + t - 1 = x + y + 1 := by omega
  have hx : (x + 1) * x = (x + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq x 1
  have hy : (y + 1) * y = (y + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq y 1
  have hxy : (x + y + 1) * (x + y) = (x + y + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq (x + y) 1
  rw [hshift, hsx, hty]
  nlinarith [Nat.zero_le (x * y)]

/-- A finite graph containing an ACTUAL bridge has at
most choose(m-1,2)+1 edges. Connectedness is not assumed; isolates are retained. -/
theorem edge_card_le_choose_pred_of_actual_bridge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Sym2 V) (hf : f ∈ G.edgeSet) (hbridge : G.IsBridge f) :
    G.edgeFinset.card ≤ (Fintype.card V - 1).choose 2 + 1 := by
  classical
  revert hf hbridge
  refine Sym2.inductionOn f ?_
  intro a b hf hbridge
  let D := G.deleteEdges ({s(a, b)} : Set (Sym2 V))
  have hsep : ¬ D.Reachable a b := SimpleGraph.isBridge_iff.mp hbridge
  let S : Finset V := Finset.univ.filter (fun x => D.Reachable a x)
  let T : Finset V := Finset.univ \ S
  have hS (x : V) : x ∈ S ↔ D.Reachable a x := by simp [S]
  have hT (x : V) : x ∈ T ↔ x ∉ S := by simp [T]
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hparts : S ∪ T = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hsum : S.card + T.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hST, hparts, Finset.card_univ]
  have hSpos : 0 < S.card :=
    Finset.card_pos.mpr ⟨a, (hS a).mpr (SimpleGraph.Reachable.refl _)⟩
  have hTpos : 0 < T.card := Finset.card_pos.mpr
    ⟨b, (hT b).mpr (fun hb => hsep ((hS b).mp hb))⟩
  have hSclosed : ∀ {x y : V}, D.Adj x y → x ∈ S → y ∈ S := by
    intro x y hxy hx
    exact (hS y).mpr (((hS x).mp hx).trans hxy.reachable)
  have hTclosed : ∀ {x y : V}, D.Adj x y → x ∈ T → y ∈ T := by
    intro x y hxy hx
    apply (hT y).mpr
    intro hy
    exact ((hT x).mp hx) (hSclosed hxy.symm hy)
  let ES := D.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  let ET := D.edgeFinset.filter (fun e => e.toFinset ⊆ T)
  have hcover : D.edgeFinset ⊆ ES ∪ ET := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y he
    have hxy : D.Adj x y := D.mem_edgeSet.mp (D.mem_edgeFinset.mp he)
    by_cases hxS : x ∈ S
    · have hsub : s(x, y).toFinset ⊆ S := by
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hxS (hSclosed hxy hxS)
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hsub⟩))
    · have hxT : x ∈ T := (hT x).mpr hxS
      have hsub : s(x, y).toFinset ⊆ T := by
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hxT (hTclosed hxy hxT)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))
  have hES : ES.card ≤ S.card.choose 2 := by
    calc
      ES.card = (D.induce (↑S : Set V)).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) S
      _ ≤ (Fintype.card S).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑S : Set V))
      _ = S.card.choose 2 := by rw [Fintype.card_coe]
  have hET : ET.card ≤ T.card.choose 2 := by
    calc
      ET.card = (D.induce (↑T : Set V)).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) T
      _ ≤ (Fintype.card T).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑T : Set V))
      _ = T.card.choose 2 := by rw [Fintype.card_coe]
  have hDcap : D.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 := by
    calc
      D.edgeFinset.card ≤ (ES ∪ ET).card := Finset.card_le_card hcover
      _ ≤ ES.card + ET.card := Finset.card_union_le ES ET
      _ ≤ S.card.choose 2 + T.card.choose 2 := Nat.add_le_add hES hET
  have hchoose : S.card.choose 2 + T.card.choose 2 ≤
      (Fintype.card V - 1).choose 2 := by
    simpa only [hsum] using choose_two_positive_cap S.card T.card hSpos hTpos
  have hdelete : D.edgeFinset = G.edgeFinset.erase s(a, b) := by
    apply Finset.coe_injective
    simp only [SimpleGraph.coe_edgeFinset, Finset.coe_erase, D,
      SimpleGraph.edgeSet_deleteEdges]
  have hedge : D.edgeFinset.card + 1 = G.edgeFinset.card := by
    rw [hdelete]
    exact Finset.card_erase_add_one (G.mem_edgeFinset.mpr hf)
  omega

variable {n q : ℕ}

/-- All original owners inside X and a genuine bridge
of the literal induced selected graph give the ORIGINAL q-color bound. -/
theorem original_palette_le_choose_pred_of_inside_actual_bridge
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (X : Set (Fin n))
    (howners : ∀ c : Fin q, EdgeInside X (R.edge c).val)
    (f : Sym2 X) (hf : f ∈ ((selectedGraph χ R).induce X).edgeSet)
    (hbridge : ((selectedGraph χ R).induce X).IsBridge f) :
    q ≤ (Nat.card X - 1).choose 2 + 1 := by
  classical
  let G := selectedGraph χ R
  have hsupport : G.support ⊆ X := by
    intro v hv
    obtain ⟨w, hvw⟩ := (SimpleGraph.mem_support G).mp hv
    have hmem : s(v, w) ∈ (selectedGraph χ R).edgeSet := hvw
    rw [selectedGraph_edgeSet] at hmem
    obtain ⟨c, hc⟩ := hmem
    change (R.edge c).val = s(v, w) at hc
    apply howners c v
    rw [hc]
    exact Sym2.mem_mk_left v w
  have hcount : (G.induce X).edgeFinset.card = q := by
    have hinduce := G.card_edgeFinset_induce_of_support_subset hsupport
    have horiginal := selectedGraph_card_edgeFinset χ R
    simp only [SimpleGraph.edgeFinset_card, Fintype.card_eq_nat_card, G] at hinduce horiginal ⊢
    exact hinduce.trans horiginal
  have hcap := edge_card_le_choose_pred_of_actual_bridge (G.induce X) f hf hbridge
  rw [hcount] at hcap
  simpa only [Fintype.card_eq_nat_card] using hcap

/-- A high ORIGINAL palette excludes every too-small
whole head once confinement and an ACTUAL inside bridge have been derived. -/
theorem original_head_order_ge_of_high_palette_and_actual_bridge
    {k : ℕ} (hk : 2 ≤ k)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (X : Set (Fin n))
    (howners : ∀ c : Fin q, EdgeInside X (R.edge c).val)
    (f : Sym2 X) (hf : f ∈ ((selectedGraph χ R).induce X).edgeSet)
    (hbridge : ((selectedGraph χ R).induce X).IsBridge f)
    (hq : (k - 2).choose 2 + 1 < q) :
    k ≤ Nat.card X := by
  have hcap := original_palette_le_choose_pred_of_inside_actual_bridge
    χ R X howners f hf hbridge
  by_contra hnot
  have hsize : Nat.card X - 1 ≤ k - 2 := by omega
  have hchoose := Nat.choose_le_choose 2 hsize
  omega

/-- A proper FIRST actual stage has an original eligible
outside connector; its certificate then supplies a genuine inside bridge. Full-tail edgelessness confines ALL q owners to this whole head, so high q
forces its order at least k. No nonempty cut or numerical cap is a premise. -/
theorem OriginalResidualCutStage.first_head_order_ge_of_high_palette
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ)
    (htail : (selectedGraph χ R).induce
      (Set.univ \ componentSupport χ R x) = ⊥)
    (hk : 2 ≤ k) (hq : (k - 2).choose 2 + 1 < q) :
    k ≤ Nat.card (componentSupport χ R x) := by
  classical
  have hx : x ∈ componentSupport χ R x :=
    (mem_componentSupport χ R x x).mpr (SimpleGraph.Reachable.refl _)
  have hyexists : ∃ y : Fin n, y ∉ componentSupport χ R x := by
    by_contra h
    apply hproper
    apply Set.eq_univ_of_forall
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hyexists
  have hxy : x ≠ y := by
    intro h
    exact hy (h ▸ hx)
  let e : HostEdge n := ⟨s(x, y), (SimpleGraph.top_adj x y).mpr hxy⟩
  have hout : EligibleResidualOutgoing χ ∅ Set.univ (componentSupport χ R x) :=
    ⟨e, x, y, rfl, hx, Set.mem_univ y, hy, by simp⟩
  have hdata := S.payload
  rcases hdata with ⟨_, _, hBselected, hBbridges, _, _, _, _, _, houtne, _⟩
  obtain ⟨f, hf⟩ := houtne hout
  have howners : ∀ c : Fin q, EdgeInside (componentSupport χ R x) (R.edge c).val := by
    intro c
    simpa only [Set.compl_univ, Set.empty_union] using
      S.owner_inside_processed_prefix htail c
  exact original_head_order_ge_of_high_palette_and_actual_bridge
    hk χ R (componentSupport χ R x) howners f (hBselected hf) (hBbridges f hf) hq

/-- At a proper first retained order k-2 endpoint,
derive the full-tail condition internally and obtain the FULL induction lower
domain k ≤ m. Properness of the head remains explicit and implies m < n only
through a separate cardinality/embedding application. -/
theorem OriginalResidualCutStage.first_head_order_ge_of_retained_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow F.toHom χ)
    (hq : (k - 2).choose 2 + 1 < q) :
    k ≤ Nat.card (componentSupport χ R x) :=
  S.first_head_order_ge_of_high_palette hproper
    (S.uncut_tail_edgeless_of_retained_path_order hk P hno) (by omega) hq

/-- A proper first retained order k-2 endpoint supplies
both literal FULL smaller-host induction domain bounds. The head carries all
original colors; no reduction of the palette or supplied size bound is used. -/
theorem OriginalResidualCutStage.first_head_full_induction_domain_of_retained_path_order
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {k : ℕ}
    (S : OriginalResidualCutStage χ R ∅ Set.univ x)
    (hproper : componentSupport χ R x ≠ Set.univ) (hk : 3 ≤ k)
    (P : (pathGraph (k - 2)).Copy S.retainedGraph)
    (hno : ∀ F : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow F.toHom χ)
    (hq : (k - 2).choose 2 + 1 < q) :
    k ≤ Nat.card (componentSupport χ R x) ∧
      Nat.card (componentSupport χ R x) < n := by
  refine ⟨S.first_head_order_ge_of_retained_path_order hproper hk P hno hq, ?_⟩
  simpa only [← Nat.card_coe_set_eq, Nat.card_fin] using
    Set.ncard_lt_card hproper

end ErdosProblems.PathUpperReduction
