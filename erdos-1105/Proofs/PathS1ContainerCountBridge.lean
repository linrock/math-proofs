module

public import PathDenseCoreTwoLeavesRainbow
public import Mathlib.Tactic

@[expose] public section

/-!
Supplies the core-degree and two-spoke inputs for the `s1Container` dense-core
rainbow-path extraction in `PathDenseCoreTwoLeavesRainbow`.
-/

namespace ErdosProblems.PathS1ContainerCountBridge

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathDenseCoreTwoLeaves

/-- Literal complete core together with all leaf-to-first-hub spokes. -/
def s1Container {n m l : ℕ} (core : Fin m → Fin n) (leaf : Fin l → Fin n)
    (z : Fin m) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    ((Sym2.map core '' (⊤ : SimpleGraph (Fin m)).edgeSet) ∪
      Set.range (fun j : Fin l => s(core z, leaf j)))

theorem missing_core_degree_bound {m : ℕ} (hm : 1 ≤ m)
    (C : SimpleGraph (Fin m)) [DecidableRel C.Adj] (i : Fin m) :
    m - 1 ≤ C.degree i + (m.choose 2 - C.edgeFinset.card) := by
  classical
  have hcomp : Cᶜ.edgeFinset =
      (⊤ : SimpleGraph (Fin m)).edgeFinset \ C.edgeFinset := by
    ext e
    refine Sym2.inductionOn e ?_
    intro x y
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Finset.mem_sdiff, SimpleGraph.compl_adj, SimpleGraph.top_adj]
  have hcompcard : Cᶜ.edgeFinset.card = m.choose 2 - C.edgeFinset.card := by
    rw [hcomp, Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono le_top)]
    simp only [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  have hdegree := Cᶜ.degree_le_card_edgeFinset (v := i)
  have hdegree_lt := C.degree_lt_card_verts i
  rw [C.degree_compl, Fintype.card_fin, hcompcard] at hdegree
  omega

theorem selected_core_and_spoke_count {n q m l : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (core : Fin m → Fin n) (leaf : Fin l → Fin n) (z : Fin m)
    (hinj : Function.Injective (Sum.elim core leaf))
    (hsub : selectedGraph χ r ≤ s1Container core leaf z) :
    q = Nat.card ((selectedGraph χ r).comap core).edgeSet +
      Nat.card {j : Fin l // (selectedGraph χ r).Adj (core z) (leaf j)} := by
  classical
  let R := selectedGraph χ r
  let C := R.comap core
  let T := Finset.univ.filter (fun j : Fin l => R.Adj (core z) (leaf j))
  have hcore : Function.Injective core := by
    intro i j hij
    exact Sum.inl.inj (hinj hij)
  have hleaf : Function.Injective leaf := by
    intro i j hij
    exact Sum.inr.inj (hinj hij)
  have hcross (i : Fin m) (j : Fin l) : core i ≠ leaf j := by
    intro hij
    have hsum : (Sum.inl i : Fin m ⊕ Fin l) = Sum.inr j :=
      hinj (show Sum.elim core leaf (Sum.inl i) = Sum.elim core leaf (Sum.inr j) from hij)
    cases hsum
  let emb : Fin m ↪ Fin n := ⟨core, hcore⟩
  let A := C.edgeFinset.map emb.sym2Map
  let B := T.image (fun j : Fin l => s(core z, leaf j))
  have hA : A = (C.map emb).edgeFinset := by
    change C.edgeFinset.map emb.sym2Map = (C.map emb).edgeFinset
    rw [← Finset.coe_inj]
    push_cast
    exact (C.edgeSet_map emb).symm
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨j, _hj, hje⟩ := Finset.mem_image.mp heB
    obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp heA
    revert hd hde
    refine Sym2.inductionOn d ?_
    intro x y _hd hde
    have heq : s(core x, core y) = s(core z, leaf j) := by
      change s(core x, core y) = e at hde
      exact hde.trans hje.symm
    rcases Sym2.eq_iff.mp heq with ⟨_, hy⟩ | ⟨hx, _⟩
    · exact hcross y j hy
    · exact hcross x j hx
  have hE : R.edgeFinset = A ∪ B := by
    ext e
    refine Sym2.inductionOn e ?_
    intro x y
    constructor
    · intro he
      have hxy : R.Adj x y := (SimpleGraph.mem_edgeFinset.mp he)
      have hc := ((SimpleGraph.fromEdgeSet_adj _).mp (hsub hxy)).1
      rcases hc with hc | hc
      · obtain ⟨d, _hd, hde⟩ := hc
        have hdR : Sym2.map core d ∈ R.edgeSet := by rw [hde]; exact hxy
        have hdC : d ∈ C.edgeFinset := by
          have hpre : ∀ t : Sym2 (Fin m), Sym2.map core t ∈ R.edgeSet → t ∈ C.edgeFinset := by
            intro t
            refine Sym2.inductionOn t ?_
            intro i j hij
            exact SimpleGraph.mem_edgeFinset.mpr hij
          exact hpre d hdR
        apply Finset.mem_union_left
        exact Finset.mem_map.mpr ⟨d, hdC, hde⟩
      · obtain ⟨j, hje⟩ := hc
        change s(core z, leaf j) = s(x, y) at hje
        have hspoke : R.Adj (core z) (leaf j) := by
          change s(core z, leaf j) ∈ R.edgeSet
          rw [hje]
          exact hxy
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hspoke⟩, hje⟩
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · rw [hA] at he
        exact SimpleGraph.mem_edgeFinset.mpr
          ((SimpleGraph.edgeSet_mono (SimpleGraph.map_comap_le emb R))
            (SimpleGraph.mem_edgeFinset.mp he))
      · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp he
        rw [← hje]
        exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hj).2
  have hBcard : B.card = T.card := by
    apply Finset.card_image_iff.mpr
    intro i _hi j _hj hij
    apply hleaf
    exact (Sym2.mkEmbedding (core z)).injective hij
  have hcount := congrArg Finset.card hE
  rw [Finset.card_union_of_disjoint hAB, Finset.card_map, hBcard] at hcount
  have hCnat : Nat.card C.edgeSet = C.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact C.edgeFinset_card.symm
  have hTnat : Nat.card {j : Fin l // R.Adj (core z) (leaf j)} = T.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype T (by intro j; simp only [T, Finset.mem_filter,
      Finset.mem_univ, true_and])
  change q = Nat.card C.edgeSet + Nat.card {j : Fin l // R.Adj (core z) (leaf j)}
  rw [hCnat, hTnat]
  simpa only [R, C, T, selectedGraph_card_edgeFinset] using hcount

/-- The full ACTUAL S1 container count yields two selected spokes and the
actual reindexed selected-core degree needed by the dense-core caller. -/
theorem dense_core_and_two_spokes_of_s1_container {n q m l : ℕ}
    (hm : 4 ≤ m) (hl : 2 ≤ l) (hwindow : 2 * l ≤ m) (_hn : n = m + l)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (core : Fin m → Fin n) (leaf : Fin l → Fin n)
    (hinj : Function.Injective (Sum.elim core leaf))
    (_hcover : Function.Surjective (Sum.elim core leaf))
    (hsub : selectedGraph χ r ≤ s1Container core leaf ⟨0, by omega⟩)
    (hq : m.choose 2 + 2 ≤ q) :
    (∀ i : Fin m, m + 2 ≤ 2 * ((selectedGraph χ r).comap core).degree i) ∧
      ∃ a b : Fin l, a ≠ b ∧
        (selectedGraph χ r).Adj (core ⟨0, by omega⟩) (leaf a) ∧
        (selectedGraph χ r).Adj (core ⟨0, by omega⟩) (leaf b) := by
  classical
  let C := (selectedGraph χ r).comap core
  let T := Finset.univ.filter
    (fun j : Fin l => (selectedGraph χ r).Adj (core ⟨0, by omega⟩) (leaf j))
  have hcount := selected_core_and_spoke_count χ r core leaf ⟨0, by omega⟩ hinj hsub
  have hCnat : Nat.card C.edgeSet = C.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact C.edgeFinset_card.symm
  have hTnat : Nat.card {j : Fin l // (selectedGraph χ r).Adj
      (core ⟨0, by omega⟩) (leaf j)} = T.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype T (by intro j; simp only [T, Finset.mem_filter,
      Finset.mem_univ, true_and])
  change q = Nat.card C.edgeSet + Nat.card {j : Fin l // (selectedGraph χ r).Adj
    (core ⟨0, by omega⟩) (leaf j)} at hcount
  rw [hCnat, hTnat] at hcount
  have hT : T.card ≤ l := by
    have hh := Finset.card_le_card (Finset.filter_subset
      (fun j : Fin l => (selectedGraph χ r).Adj (core ⟨0, by omega⟩) (leaf j)) Finset.univ)
    simpa only [Finset.card_univ, Fintype.card_fin] using hh
  have hC : C.edgeFinset.card ≤ m.choose 2 := by
    simpa only [Fintype.card_fin] using C.card_edgeFinset_le_card_choose_two
  have hdeficit : (m.choose 2 - C.edgeFinset.card) + (l - T.card) ≤ l - 2 := by omega
  have hmissing : m.choose 2 - C.edgeFinset.card ≤ l - 2 := by omega
  have hspokes : 1 < T.card := by omega
  constructor
  · intro i
    have hd := missing_core_degree_bound (by omega) C i
    change m + 2 ≤ 2 * C.degree i
    omega
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hspokes
    exact ⟨a, b, hab, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩

/-- SAME original-color S1-container exclusion under the exact count/window
hypotheses. No favorable owner, supplied rainbow path or degree premise. -/
theorem rainbow_path_of_representative_s1_container {n q m l : ℕ}
    (hm : 4 ≤ m) (hl : 2 ≤ l) (hwindow : 2 * l ≤ m) (hn : n = m + l)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (core : Fin m → Fin n) (leaf : Fin l → Fin n)
    (hinj : Function.Injective (Sum.elim core leaf))
    (hcover : Function.Surjective (Sum.elim core leaf))
    (hsub : selectedGraph χ r ≤ s1Container core leaf ⟨0, by omega⟩)
    (hq : m.choose 2 + 2 ≤ q) :
    ∃ f : (pathGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  classical
  obtain ⟨hdegree, a, b, hab, ha, hb⟩ :=
    dense_core_and_two_spokes_of_s1_container hm hl hwindow hn χ r core leaf hinj hcover hsub hq
  have hcore : Function.Injective core := by
    intro i j hij
    exact Sum.inl.inj (hinj hij)
  have hleaf : Function.Injective leaf := by
    intro i j hij
    exact Sum.inr.inj (hinj hij)
  have hcross (i : Fin m) (j : Fin l) : leaf j ≠ core i := by
    intro hij
    have hsum : (Sum.inr j : Fin m ⊕ Fin l) = Sum.inl i :=
      hinj (show Sum.elim core leaf (Sum.inr j) = Sum.elim core leaf (Sum.inl i) from hij)
    cases hsum
  have hu : Function.Injective (Fin.cons (leaf a) (Fin.cons (leaf b) core)) := by
    apply Fin.cons_injective_iff.mpr
    constructor
    · have hneq (i : Fin (m + 1)) :
          (Fin.cons (leaf b) core : Fin (m + 1) → Fin n) i ≠ leaf a := by
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (hleaf.ne hab).symm
        · exact (hcross j a).symm
      rintro ⟨i, hi⟩
      exact hneq i hi
    · apply Fin.cons_injective_iff.mpr
      refine ⟨?_, hcore⟩
      rintro ⟨i, hi⟩
      exact hcross i b hi.symm
  exact rainbow_path_of_dense_representative_core_and_two_spokes hm χ r core
    (leaf a) (leaf b) hu hdegree ha.symm hb.symm

end ErdosProblems.PathS1ContainerCountBridge
