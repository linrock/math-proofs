module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

/-!
Bridge-cut cardinality and complete-induced-part lemmas for connected
representative subgraphs on 13 vertices.
-/

namespace ErdosProblems.PathThirteenBridgeEquality

open SimpleGraph
open scoped BigOperators

/-- In the three actual parts obtained from deleting a bridge, density forces
the ten-vertex core, one pendant vertex and the two-vertex outside part.
The outside part may initially contain several components. -/
theorem three_cut_cardinalities
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 2 ≤ c)
    (hcomponent : 9 ≤ a + b) (hsum : a + b + c = 13)
    (hdense : 47 ≤ a.choose 2 + b.choose 2 + c.choose 2 + 1) :
    c = 2 ∧ ((a = 1 ∧ b = 10) ∨ (a = 10 ∧ b = 1)) := by
  let x := a - 1
  let y := b - 1
  have hax : a = x + 1 := by dsimp [x]; omega
  have hby : b = y + 1 := by dsimp [y]; omega
  have hx : (x + 1) * x = (x + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq x 1
  have hy : (y + 1) * y = (y + 1).choose 2 * 2 := by
    simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq y 1
  rw [hax, hby] at hsum hcomponent hdense
  have hcupper : c ≤ 4 := by omega
  have hc2 : c = 2 := by
    by_contra hne
    have hcases : c = 3 ∨ c = 4 := by omega
    rcases hcases with rfl | rfl
    · norm_num at hdense
      nlinarith [Nat.zero_le (x * y)]
    · change 47 ≤ (x + 1).choose 2 + (y + 1).choose 2 + 6 + 1 at hdense
      nlinarith [Nat.zero_le (x * y)]
  subst c
  norm_num at hdense
  have hxy : x * y = 0 := by nlinarith [Nat.zero_le (x * y)]
  refine ⟨rfl, ?_⟩
  rcases Nat.mul_eq_zero.mp hxy with hx0 | hy0
  · left
    omega
  · right
    omega

/-- Equality in the complete-graph edge cap forces the actual graph to be
complete. This is applied to each actual induced part, without relabeling. -/
theorem eq_top_of_card_edgeFinset_eq_choose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : G.edgeFinset.card = (Fintype.card V).choose 2) : G = ⊤ := by
  classical
  apply SimpleGraph.edgeFinset_inj.mp
  apply Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  exact hcard.ge

/-- Forty-seven selected edges force a vertex whose actual component has
at least nine vertices. Global maximality then gives this size to the
chosen largest component. -/
theorem exists_degree_eight_of_edges_forty_seven
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (hdense : 47 ≤ G.edgeFinset.card) : ∃ v, 8 ≤ G.degree v := by
  by_contra h
  push Not at h
  have hsum : (∑ v : Fin 13, G.degree v) ≤ ∑ _v : Fin 13, 7 := by
    apply Finset.sum_le_sum
    intro v _hv
    exact Nat.le_of_lt_succ (h v)
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  norm_num at hsum
  omega

/-- Once the actual bridge cut has sizes one, ten and two, its total edge
cap forces both nontrivial induced parts to be complete. -/
theorem actual_parts_complete_of_bridge_cap
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (S T U : Finset (Fin 13)) (hS : S.card = 1) (hT : T.card = 10)
    (hU : U.card = 2) (hdense : 47 ≤ G.edgeFinset.card)
    (hcap : G.edgeFinset.card ≤
      (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1) :
    G.edgeFinset.card = 47 ∧
      G.induce (↑T : Set (Fin 13)) = ⊤ ∧
      G.induce (↑U : Set (Fin 13)) = ⊤ := by
  classical
  have hScap : (G.induce (↑S : Set (Fin 13))).edgeFinset.card ≤ S.card.choose 2 := by
    calc
      _ ≤ (Fintype.card S).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = S.card.choose 2 := by rw [Fintype.card_coe]
  have hTcap : (G.induce (↑T : Set (Fin 13))).edgeFinset.card ≤ T.card.choose 2 := by
    calc
      _ ≤ (Fintype.card T).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = T.card.choose 2 := by rw [Fintype.card_coe]
  have hUcap : (G.induce (↑U : Set (Fin 13))).edgeFinset.card ≤ U.card.choose 2 := by
    calc
      _ ≤ (Fintype.card U).choose 2 := SimpleGraph.card_edgeFinset_le_card_choose_two
      _ = U.card.choose 2 := by rw [Fintype.card_coe]
  rw [hS] at hScap
  rw [hT] at hTcap
  rw [hU] at hUcap
  change (G.induce (↑S : Set (Fin 13))).edgeFinset.card ≤ 0 at hScap
  change (G.induce (↑T : Set (Fin 13))).edgeFinset.card ≤ 45 at hTcap
  change (G.induce (↑U : Set (Fin 13))).edgeFinset.card ≤ 1 at hUcap
  refine ⟨by omega, ?_, ?_⟩
  · apply eq_top_of_card_edgeFinset_eq_choose
    change (G.induce (↑T : Set (Fin 13))).edgeFinset.card = (Fintype.card T).choose 2
    rw [Fintype.card_coe, hT]
    change (G.induce (↑T : Set (Fin 13))).edgeFinset.card = 45
    omega
  · apply eq_top_of_card_edgeFinset_eq_choose
    change (G.induce (↑U : Set (Fin 13))).edgeFinset.card = (Fintype.card U).choose 2
    rw [Fintype.card_coe, hU]
    change (G.induce (↑U : Set (Fin 13))).edgeFinset.card = 1
    omega

end ErdosProblems.PathThirteenBridgeEquality

/-! The parts are determined by the actual edge, without an assumed cut shape. -/

namespace ErdosProblems.Fin13ActualBridgeCut

open SimpleGraph
open scoped Classical

/-- The deletion cut of an actual bridge, retaining its ORIGINAL component.
Disconnectedness, minimum degree and component size occur only in the two
conditional consequences; they are not substituted by a favorable cut. -/
theorem actual_bridge_cut_certificate
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (a b : Fin 13) (hab : G.Adj a b) (hbridge : G.IsBridge s(a, b)) :
    let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))
    let S := Finset.univ.filter (fun x => D.Reachable a x)
    let T := Finset.univ.filter (fun x => D.Reachable b x)
    let U := Finset.univ \ (S ∪ T)
    Disjoint S T ∧ Disjoint (S ∪ T) U ∧
    (S ∪ T) ∪ U = Finset.univ ∧ a ∈ S ∧ b ∈ T ∧
    S.card + T.card + U.card = 13 ∧
    (∀ x y, G.Adj x y →
      s(x, y) = s(a, b) ∨ (x ∈ S ∧ y ∈ S) ∨
      (x ∈ T ∧ y ∈ T) ∨ (x ∈ U ∧ y ∈ U)) ∧
    S ∪ T = Finset.univ.filter (fun x => G.Reachable a x) ∧
    (¬ G.Connected → (∀ x, 1 ≤ G.degree x) → 2 ≤ U.card) ∧
    (9 ≤ (Finset.univ.filter (fun x => G.Reachable a x)).card →
      9 ≤ S.card + T.card) ∧
    G.edgeFinset.card ≤ (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 ∧
    G.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 + 1 := by
  classical
  let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))
  let S : Finset (Fin 13) := Finset.univ.filter (fun x => D.Reachable a x)
  let T : Finset (Fin 13) := Finset.univ.filter (fun x => D.Reachable b x)
  let U : Finset (Fin 13) := Finset.univ \ (S ∪ T)
  change Disjoint S T ∧ Disjoint (S ∪ T) U ∧
    (S ∪ T) ∪ U = Finset.univ ∧ a ∈ S ∧ b ∈ T ∧
    S.card + T.card + U.card = 13 ∧
    (∀ x y, G.Adj x y →
      s(x, y) = s(a, b) ∨ (x ∈ S ∧ y ∈ S) ∨
      (x ∈ T ∧ y ∈ T) ∨ (x ∈ U ∧ y ∈ U)) ∧
    S ∪ T = Finset.univ.filter (fun x => G.Reachable a x) ∧
    (¬ G.Connected → (∀ x, 1 ≤ G.degree x) → 2 ≤ U.card) ∧
    (9 ≤ (Finset.univ.filter (fun x => G.Reachable a x)).card →
      9 ≤ S.card + T.card) ∧
    G.edgeFinset.card ≤ (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 ∧
    G.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 + 1
  have hle : D ≤ G := G.deleteEdges_le _
  have hsep : ¬ D.Reachable a b := SimpleGraph.isBridge_iff.mp hbridge
  have hS (x : Fin 13) : x ∈ S ↔ D.Reachable a x := by simp [S]
  have hT (x : Fin 13) : x ∈ T ↔ D.Reachable b x := by simp [T]
  have hU (x : Fin 13) : x ∈ U ↔ x ∉ S ∧ x ∉ T := by simp [U]
  have haS : a ∈ S := (hS a).mpr (SimpleGraph.Reachable.refl _)
  have hbT : b ∈ T := (hT b).mpr (SimpleGraph.Reachable.refl _)
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    exact hsep (((hS x).mp hxS).trans ((hT x).mp hxT).symm)
  have hSTU : Disjoint (S ∪ T) U := Finset.disjoint_sdiff
  have hparts : (S ∪ T) ∪ U = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hsum : S.card + T.card + U.card = 13 := by
    calc
      S.card + T.card + U.card = (S ∪ T).card + U.card := by
        rw [Finset.card_union_of_disjoint hST]
      _ = ((S ∪ T) ∪ U).card := (Finset.card_union_of_disjoint hSTU).symm
      _ = 13 := by simp only [hparts, Finset.card_univ, Fintype.card_fin]
  have hSclosed : ∀ {x y : Fin 13}, D.Adj x y → x ∈ S → y ∈ S := by
    intro x y hxy hx
    exact (hS y).mpr (((hS x).mp hx).trans hxy.reachable)
  have hTclosed : ∀ {x y : Fin 13}, D.Adj x y → x ∈ T → y ∈ T := by
    intro x y hxy hx
    exact (hT y).mpr (((hT x).mp hx).trans hxy.reachable)
  have hUclosed : ∀ {x y : Fin 13}, D.Adj x y → x ∈ U → y ∈ U := by
    intro x y hxy hx
    obtain ⟨hxS, hxT⟩ := (hU x).mp hx
    apply (hU y).mpr
    constructor
    · intro hyS
      exact hxS (hSclosed hxy.symm hyS)
    · intro hyT
      exact hxT (hTclosed hxy.symm hyT)
  have hdeleteAdj {x y : Fin 13} (hxy : G.Adj x y)
      (hne : s(x, y) ≠ s(a, b)) : D.Adj x y := by
    change (G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))).Adj x y
    apply SimpleGraph.deleteEdges_adj.mpr
    exact ⟨hxy, by simpa only [Set.mem_singleton_iff] using hne⟩
  have hclosed : ∀ {x y : Fin 13}, G.Adj x y → x ∈ S ∪ T → y ∈ S ∪ T := by
    intro x y hxy hx
    by_cases he : s(x, y) = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Finset.mem_union.mpr (Or.inr hbT)
      · exact Finset.mem_union.mpr (Or.inl haS)
    · have hxyD := hdeleteAdj hxy he
      rcases Finset.mem_union.mp hx with hxS | hxT
      · exact Finset.mem_union.mpr (Or.inl (hSclosed hxyD hxS))
      · exact Finset.mem_union.mpr (Or.inr (hTclosed hxyD hxT))
  have hcomponent (x : Fin 13) : x ∈ S ∪ T ↔ G.Reachable a x := by
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxS | hxT
      · exact SimpleGraph.Reachable.mono hle ((hS x).mp hxS)
      · exact hab.reachable.trans (SimpleGraph.Reachable.mono hle ((hT x).mp hxT))
    · intro hx
      have hrt := (G.reachable_iff_reflTransGen a x).mp hx
      induction hrt with
      | refl => exact Finset.mem_union.mpr (Or.inl haS)
      | tail hprev hxy ih =>
          exact hclosed hxy (ih ((G.reachable_iff_reflTransGen a _).mpr hprev))
  have hcomponentSet : S ∪ T = Finset.univ.filter (fun x => G.Reachable a x) := by
    ext x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcomponent x
  have hUoriginal (x : Fin 13) : x ∈ U ↔ ¬ G.Reachable a x := by
    rw [← hcomponent x]
    simp only [U, Finset.mem_sdiff, Finset.mem_univ, true_and]
  have hUoriginalClosed : ∀ {x y : Fin 13}, G.Adj x y → x ∈ U → y ∈ U := by
    intro x y hxy hx
    apply (hUoriginal y).mpr
    intro hy
    exact (hUoriginal x).mp hx (hy.trans hxy.symm.reachable)
  have hUtwo : ¬ G.Connected → (∀ x, 1 ≤ G.degree x) → 2 ≤ U.card := by
    intro hdis hdegree
    have hzexists : ∃ z : Fin 13, ¬ G.Reachable a z := by
      by_contra hz
      apply hdis
      apply (G.connected_iff_exists_forall_reachable).mpr
      refine ⟨a, ?_⟩
      intro z
      by_contra haz
      exact hz ⟨z, haz⟩
    obtain ⟨z, haz⟩ := hzexists
    have hzU : z ∈ U := (hUoriginal z).mpr haz
    have hzpos : 0 < G.degree z := by have := hdegree z; omega
    obtain ⟨y, hzy⟩ := (G.degree_pos_iff_exists_adj z).mp hzpos
    have hyU : y ∈ U := hUoriginalClosed hzy hzU
    have hpair : ({z, y} : Finset (Fin 13)) ⊆ U := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzU
      · exact hyU
    calc
      2 = ({z, y} : Finset (Fin 13)).card := by simp [hzy.ne]
      _ ≤ U.card := Finset.card_le_card hpair
  have hlarge : 9 ≤ (Finset.univ.filter (fun x => G.Reachable a x)).card →
      9 ≤ S.card + T.card := by
    intro hbig
    rw [← hcomponentSet, Finset.card_union_of_disjoint hST] at hbig
    exact hbig
  have hedgeClass : ∀ x y, G.Adj x y →
      s(x, y) = s(a, b) ∨ (x ∈ S ∧ y ∈ S) ∨
      (x ∈ T ∧ y ∈ T) ∨ (x ∈ U ∧ y ∈ U) := by
    intro x y hxy
    by_cases he : s(x, y) = s(a, b)
    · exact Or.inl he
    · have hxyD := hdeleteAdj hxy he
      apply Or.inr
      by_cases hxS : x ∈ S
      · exact Or.inl ⟨hxS, hSclosed hxyD hxS⟩
      · apply Or.inr
        by_cases hxT : x ∈ T
        · exact Or.inl ⟨hxT, hTclosed hxyD hxT⟩
        · have hxU := (hU x).mpr ⟨hxS, hxT⟩
          exact Or.inr ⟨hxU, hUclosed hxyD hxU⟩
  let ES := D.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  let ET := D.edgeFinset.filter (fun e => e.toFinset ⊆ T)
  let EU := D.edgeFinset.filter (fun e => e.toFinset ⊆ U)
  have hcover : D.edgeFinset ⊆ (ES ∪ ET) ∪ EU := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y he
    have hxy : D.Adj x y := D.mem_edgeSet.mp (D.mem_edgeFinset.mp he)
    by_cases hxS : x ∈ S
    · have hsub : s(x, y).toFinset ⊆ S := by
        simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
          Finset.singleton_subset_iff] using And.intro hxS (hSclosed hxy hxS)
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨he, hsub⟩))))
    · by_cases hxT : x ∈ T
      · have hsub : s(x, y).toFinset ⊆ T := by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hxT (hTclosed hxy hxT)
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))))
      · have hxU := (hU x).mpr ⟨hxS, hxT⟩
        have hsub : s(x, y).toFinset ⊆ U := by
          simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
            Finset.singleton_subset_iff] using And.intro hxU (hUclosed hxy hxU)
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hsub⟩))
  have hES : ES.card ≤ S.card.choose 2 := by
    calc
      ES.card = (D.induce (↑S : Set (Fin 13))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) S
      _ ≤ (Fintype.card S).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑S : Set (Fin 13)))
      _ = S.card.choose 2 := by rw [Fintype.card_coe]
  have hET : ET.card ≤ T.card.choose 2 := by
    calc
      ET.card = (D.induce (↑T : Set (Fin 13))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) T
      _ ≤ (Fintype.card T).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑T : Set (Fin 13)))
      _ = T.card.choose 2 := by rw [Fintype.card_coe]
  have hEU : EU.card ≤ U.card.choose 2 := by
    calc
      EU.card = (D.induce (↑U : Set (Fin 13))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := D) U
      _ ≤ (Fintype.card U).choose 2 :=
        SimpleGraph.card_edgeFinset_le_card_choose_two (G := D.induce (↑U : Set (Fin 13)))
      _ = U.card.choose 2 := by rw [Fintype.card_coe]
  have hDcount : D.edgeFinset.card ≤ ES.card + ET.card + EU.card := by
    calc
      D.edgeFinset.card ≤ ((ES ∪ ET) ∪ EU).card := Finset.card_le_card hcover
      _ ≤ (ES ∪ ET).card + EU.card := Finset.card_union_le (ES ∪ ET) EU
      _ ≤ ES.card + ET.card + EU.card :=
        Nat.add_le_add_right (Finset.card_union_le ES ET) EU.card
  have hDcap : D.edgeFinset.card ≤ S.card.choose 2 + T.card.choose 2 + U.card.choose 2 := by
    omega
  have hpartCount (P : Finset (Fin 13)) :
      (D.edgeFinset.filter (fun e => e.toFinset ⊆ P)).card ≤
      (G.induce (↑P : Set (Fin 13))).edgeFinset.card := by
    calc
      (D.edgeFinset.filter (fun e => e.toFinset ⊆ P)).card ≤
          (G.edgeFinset.filter (fun e => e.toFinset ⊆ P)).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨heD, hsub⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨SimpleGraph.edgeFinset_mono hle heD, hsub⟩
      _ = (G.induce (↑P : Set (Fin 13))).edgeFinset.card :=
        SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := G) P
  have hdelete : D.edgeFinset = G.edgeFinset.erase s(a, b) := by
    apply Finset.coe_injective
    simp only [SimpleGraph.coe_edgeFinset, Finset.coe_erase, D, SimpleGraph.edgeSet_deleteEdges]
  have hedge : D.edgeFinset.card + 1 = G.edgeFinset.card := by
    rw [hdelete]
    exact Finset.card_erase_add_one (G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hab))
  have hGcap : G.edgeFinset.card ≤
      S.card.choose 2 + T.card.choose 2 + U.card.choose 2 + 1 := by omega
  have hSCount : ES.card ≤ (G.induce (↑S : Set (Fin 13))).edgeFinset.card := hpartCount S
  have hTCount : ET.card ≤ (G.induce (↑T : Set (Fin 13))).edgeFinset.card := hpartCount T
  have hUCount : EU.card ≤ (G.induce (↑U : Set (Fin 13))).edgeFinset.card := hpartCount U
  have hGCount : G.edgeFinset.card ≤
      (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
      (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 := by omega
  exact ⟨hST, hSTU, hparts, haS, hbT, hsum, hedgeClass,
    hcomponentSet, hUtwo, hlarge, hGCount, hGcap⟩

end ErdosProblems.Fin13ActualBridgeCut

namespace ErdosProblems.PathThirteenBridgeEquality

open scoped Classical

/-- Exact actual deletion parts in the sole dense disconnected bridge case.
This is the ordinary structural seam in the original Fin13 coloring proof;
the original-color exchange remains to be composed. -/
theorem dense_actual_bridge_exception_shape
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (hdis : ¬ G.Connected) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdense : 47 ≤ G.edgeFinset.card)
    (a b : Fin 13) (hab : G.Adj a b) (hbridge : G.IsBridge s(a, b))
    (hlarge : 9 ≤ (Finset.univ.filter (fun x => G.Reachable a x)).card) :
    let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))
    let S := Finset.univ.filter (fun x => D.Reachable a x)
    let T := Finset.univ.filter (fun x => D.Reachable b x)
    let U := Finset.univ \ (S ∪ T)
    G.edgeFinset.card = 47 ∧ U.card = 2 ∧
      ((S.card = 1 ∧ T.card = 10 ∧ G.induce (↑T : Set (Fin 13)) = ⊤) ∨
       (S.card = 10 ∧ T.card = 1 ∧ G.induce (↑S : Set (Fin 13)) = ⊤)) ∧
      G.induce (↑U : Set (Fin 13)) = ⊤ := by
  classical
  let D := G.deleteEdges ({s(a, b)} : Set (Sym2 (Fin 13)))
  let S : Finset (Fin 13) := Finset.univ.filter (fun x => D.Reachable a x)
  let T : Finset (Fin 13) := Finset.univ.filter (fun x => D.Reachable b x)
  let U : Finset (Fin 13) := Finset.univ \ (S ∪ T)
  obtain ⟨_hST, _hSTU, _hparts, haS, hbT, hsum, _hclass,
      _hcomponent, hUtwo, hbig, hcount, hchoose⟩ :=
    ErdosProblems.Fin13ActualBridgeCut.actual_bridge_cut_certificate G a b hab hbridge
  change G.edgeFinset.card ≤
    (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
    (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
    (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 at hcount
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨a, haS⟩
  have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨b, hbT⟩
  have hUtwo' : 2 ≤ U.card := hUtwo hdis hmin
  obtain ⟨hU, hsize⟩ := three_cut_cardinalities S.card T.card U.card
    hSpos hTpos hUtwo' (hbig hlarge) hsum (hdense.trans hchoose)
  rcases hsize with ⟨hS, hT⟩ | ⟨hS, hT⟩
  · obtain ⟨heq, hcore, hout⟩ :=
      actual_parts_complete_of_bridge_cap G S T U hS hT hU hdense hcount
    exact ⟨heq, hU, Or.inl ⟨hS, hT, hcore⟩, hout⟩
  · have hcount' : G.edgeFinset.card ≤
        (G.induce (↑T : Set (Fin 13))).edgeFinset.card +
        (G.induce (↑S : Set (Fin 13))).edgeFinset.card +
        (G.induce (↑U : Set (Fin 13))).edgeFinset.card + 1 := by omega
    obtain ⟨heq, hcore, hout⟩ :=
      actual_parts_complete_of_bridge_cap G T S U hT hS hU hdense hcount'
    exact ⟨heq, hU, Or.inr ⟨hS, hT, hcore⟩, hout⟩

end ErdosProblems.PathThirteenBridgeEquality
