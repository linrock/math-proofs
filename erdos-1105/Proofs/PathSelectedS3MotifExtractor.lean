module

public import PathSelectedC6FourthLeafRainbow
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic

@[expose] public section

/-!
Graph-only extraction of the selected nine-edge `C6`/fourth-leaf motif from a
seventeen-edge spanning subgraph of `S3`.
-/

namespace ErdosProblems.PathSelectedS3MotifExtractor

open SimpleGraph Finset
open ErdosProblems.PathSelectedC6FourthLeaf

theorem three_hub_card
    (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (U : Finset (Fin 8)) (hU : U.card = 3)
    (hH : ∀ x y, H.Adj x y ↔ x ≠ y ∧ (x ∈ U ∨ y ∈ U)) :
    H.edgeFinset.card = 18 := by
  classical
  have houtside : (univ \ U).card = 5 := by
    rw [card_sdiff_of_subset (subset_univ U)]
    simp [hU]
  have hd : ∀ x : Fin 8, H.degree x = if x ∈ U then 7 else 3 := by
    intro x
    by_cases hx : x ∈ U
    · have hn : H.neighborFinset x = univ.erase x := by
        ext y
        simp only [H.mem_neighborFinset, mem_erase, mem_univ, and_true]
        rw [hH]
        simp [hx, ne_comm]
      rw [ite_eq_left hx, ← H.card_neighborFinset_eq_degree x, hn]
      simp
    · have hn : H.neighborFinset x = U := by
        ext y
        rw [H.mem_neighborFinset, hH]
        constructor
        · rintro ⟨_, hy | hy⟩
          · exact False.elim (hx hy)
          · exact hy
        · intro hy
          refine ⟨?_, Or.inr hy⟩
          intro hxy
          exact hx (hxy.symm ▸ hy)
      rw [ite_eq_right hx, ← H.card_neighborFinset_eq_degree x, hn, hU]
  have hfilter : univ.filter (fun x : Fin 8 => x ∈ U) = U := by
    ext x
    simp
  have hnotfilter : univ.filter (fun x : Fin 8 => x ∉ U) = univ \ U := by
    ext x
    simp
  have hsum : ∑ x : Fin 8, H.degree x = 36 := by
    simp_rw [hd]
    rw [Finset.sum_ite]
    simp [hfilter, hnotfilter, hU, houtside]
  have hhand := H.sum_degrees_eq_twice_card_edges
  omega

theorem four_fully_spoked_leaves
    (R H : SimpleGraph (Fin 8)) [DecidableRel R.Adj] [DecidableRel H.Adj]
    (hRH : R ≤ H) (hcard : 17 ≤ R.edgeFinset.card)
    (U : Finset (Fin 8)) (hU : U.card = 3)
    (hH : ∀ x y, H.Adj x y ↔ x ≠ y ∧ (x ∈ U ∨ y ∈ U)) :
    ∃ A : Finset (Fin 8), A.card = 4 ∧ A ⊆ univ \ U ∧
      ∀ x ∈ A, ∀ a ∈ U, R.Adj x a := by
  classical
  let L : Finset (Fin 8) := univ \ U
  let B : Finset (Fin 8) := L.filter (fun x => ∃ a ∈ U, ¬R.Adj x a)
  let M : Finset (Sym2 (Fin 8)) := H.edgeFinset \ R.edgeFinset
  have hL : L.card = 5 := by
    dsimp [L]
    rw [card_sdiff_of_subset (subset_univ U)]
    simp [hU]
  have hHcard := three_hub_card H U hU hH
  have hM : M.card ≤ 1 := by
    dsimp [M]
    rw [card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hRH)]
    omega
  have hb : ∀ x : B, ∃ a ∈ U, ¬R.Adj x.val a := by
    intro x
    exact (mem_filter.mp x.property).2
  let a : B → Fin 8 := fun x => Classical.choose (hb x)
  have ha (x : B) : a x ∈ U ∧ ¬R.Adj x.val (a x) :=
    Classical.choose_spec (hb x)
  have hxout (x : B) : x.val ∉ U := by
    exact (mem_sdiff.mp ((mem_filter.mp x.property).1)).2
  let f : B → M := fun x => ⟨s(x.val, a x), by
    apply mem_sdiff.mpr
    constructor
    · apply SimpleGraph.mem_edgeFinset.mpr
      apply (H.mem_edgeSet).mpr
      apply (hH x.val (a x)).mpr
      refine ⟨?_, Or.inr (ha x).1⟩
      intro heq
      exact hxout x (heq.symm ▸ (ha x).1)
    · intro he
      exact (ha x).2 ((R.mem_edgeSet).mp (SimpleGraph.mem_edgeFinset.mp he))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have he : s(x.val, a x) = s(y.val, a y) := congrArg Subtype.val hxy
    rcases Sym2.eq_iff.mp he with he | he
    · exact Subtype.ext he.1
    · exact False.elim (hxout x (he.1.symm ▸ (ha y).1))
  have hB : B.card ≤ 1 := by
    have hBM : B.card ≤ M.card := Finset.card_le_card_of_injective hf
    omega
  let G : Finset (Fin 8) := L \ B
  have hBG : B ⊆ L := filter_subset _ _
  have hG : 4 ≤ G.card := by
    dsimp [G]
    rw [card_sdiff_of_subset hBG]
    omega
  obtain ⟨A, hAG, hA⟩ := Finset.exists_subset_card_eq hG
  refine ⟨A, hA, ?_, ?_⟩
  · intro x hx
    exact (mem_sdiff.mp (hAG hx)).1
  · intro x hx b hbU
    have hxG := mem_sdiff.mp (hAG hx)
    by_contra hbad
    exact hxG.2 (mem_filter.mpr ⟨hxG.1, b, hbU, hbad⟩)

def weave (a : Fin 3 → Fin 8) (b : Fin 4 → Fin 8)
    (w : Fin 8) (i : Fin 8) : Fin 8 :=
  if i = 0 then a 0 else if i = 1 then b 0
  else if i = 2 then a 1 else if i = 3 then b 1
  else if i = 4 then a 2 else if i = 5 then b 2
  else if i = 6 then b 3 else w

theorem weave_injective
    (a : Fin 3 → Fin 8) (b : Fin 4 → Fin 8) (w : Fin 8)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (haw : ∀ i, a i ≠ w) (hbw : ∀ i, b i ≠ w) :
    Function.Injective (weave a b w) := by
  have hba : ∀ i j, b i ≠ a j := fun i j => (hab j i).symm
  have hwa : ∀ i, w ≠ a i := fun i => (haw i).symm
  have hwb : ∀ i, w ≠ b i := fun i => (hbw i).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [weave, ha.eq_iff, hb.eq_iff]

/-- Literal graph-only motif extraction. U consists of the three S3 hubs.
The selected subgraph may omit one host edge at any actual location. -/
theorem selected_c6_fourth_leaf_of_seventeen_edges_in_three_hub
    (R H : SimpleGraph (Fin 8)) [DecidableRel R.Adj] [DecidableRel H.Adj]
    (hRH : R ≤ H) (hcard : 17 ≤ R.edgeFinset.card)
    (U : Finset (Fin 8)) (hU : U.card = 3)
    (hH : ∀ x y, H.Adj x y ↔ x ≠ y ∧ (x ∈ U ∨ y ∈ U)) :
    ∃ u : Fin 8 → Fin 8, Function.Injective u ∧ RepresentativeC6FourthLeafOn R u := by
  classical
  obtain ⟨A, hA, hAL, hfull⟩ := four_fully_spoked_leaves R H hRH hcard U hU hH
  have hUA : Disjoint U A := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxA
    exact (mem_sdiff.mp (hAL hxA)).2 hxU
  have hseven : (U ∪ A).card = 7 := by
    rw [card_union_of_disjoint hUA, hU, hA]
  have hremaining : (univ \ (U ∪ A)).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ (U ∪ A))]
    simp [hseven]
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (univ \ (U ∪ A)).card by omega)
  have hwU : w ∉ U := by
    intro hwU
    exact (mem_sdiff.mp hw).2 (mem_union.mpr (Or.inl hwU))
  have hwA : w ∉ A := by
    intro hwA
    exact (mem_sdiff.mp hw).2 (mem_union.mpr (Or.inr hwA))
  let eU : U ≃ Fin 3 := Finset.equivFinOfCardEq hU
  let eA : A ≃ Fin 4 := Finset.equivFinOfCardEq hA
  let a : Fin 3 → Fin 8 := fun i => (eU.symm i).val
  let b : Fin 4 → Fin 8 := fun i => (eA.symm i).val
  have haU (i : Fin 3) : a i ∈ U := (eU.symm i).property
  have hbA (i : Fin 4) : b i ∈ A := (eA.symm i).property
  have hainj : Function.Injective a := by
    intro i j hij
    exact eU.symm.injective (Subtype.ext hij)
  have hbinj : Function.Injective b := by
    intro i j hij
    exact eA.symm.injective (Subtype.ext hij)
  have hab : ∀ i j, a i ≠ b j := by
    intro i j heq
    exact (mem_sdiff.mp (hAL (hbA j))).2 (heq ▸ haU i)
  have haw : ∀ i, a i ≠ w := by
    intro i heq
    exact hwU (heq ▸ haU i)
  have hbw : ∀ i, b i ≠ w := by
    intro i heq
    exact hwA (heq ▸ hbA i)
  have hadj (i : Fin 4) (j : Fin 3) : R.Adj (b i) (a j) :=
    hfull (b i) (hbA i) (a j) (haU j)
  refine ⟨weave a b w, weave_injective a b w hainj hbinj hab haw hbw, ?_⟩
  constructor
  · simpa [weave] using (hadj 0 0).symm
  · simpa [weave] using hadj 0 1
  · simpa [weave] using (hadj 1 1).symm
  · simpa [weave] using hadj 1 2
  · simpa [weave] using (hadj 2 2).symm
  · simpa [weave] using hadj 2 0
  · simpa [weave] using hadj 3 0
  · simpa [weave] using hadj 3 1
  · simpa [weave] using hadj 3 2

end ErdosProblems.PathSelectedS3MotifExtractor
