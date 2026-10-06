module

public import PathSixK23Transfer
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-!
extraction of ACTUAL G spokes from a dense subgraph of the literal
Fin6 two-hub join. The original checked RepresentativeK23On predicate is used.
-/

namespace ErdosProblems.PathUpperFinSixExtractor

open SimpleGraph
open ErdosProblems.AntiRamseyPathSixK23Transfer

/-- An eight-edge subgraph of the actual nine-edge two-hub join contains
three common leaves and the distinct fourth leaf, in the existing motif API. -/
theorem representative_k23_of_dense_fin_six_join
    (G H : SimpleGraph (Fin 6)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (hGedges : 8 ≤ G.edgeFinset.card)
    (U : Finset (Fin 6)) (hUcard : U.card = 2)
    (hshape : ∀ u v, H.Adj u v ↔ u ≠ v ∧ (u ∈ U ∨ v ∈ U))
    (hHedges : H.edgeFinset.card = 9) :
    ∃ u : Fin 6 → Fin 6, Function.Injective u ∧ RepresentativeK23On G u := by
  classical
  let D := H.edgeFinset \ G.edgeFinset
  have hEdgeSubset : G.edgeFinset ⊆ H.edgeFinset := SimpleGraph.edgeFinset_mono hGH
  have hDsum : D.card + G.edgeFinset.card = 9 := by
    simpa only [D, hHedges] using Finset.card_sdiff_add_card_eq_card hEdgeSubset
  have hDle : D.card ≤ 1 := by omega
  let V : Finset (Fin 6) := Uᶜ
  have hVcard : V.card = 4 := by
    change Uᶜ.card = 4
    simpa only [Fintype.card_fin, hUcard] using Finset.card_compl U
  let Bad := V.filter (fun x => ∃ a ∈ U, ¬ G.Adj a x)
  have hBadSubset : Bad ⊆ V := Finset.filter_subset _ _
  have hMissing (a x : Fin 6) (ha : a ∈ U) (hx : x ∈ V)
      (hnot : ¬ G.Adj a x) : s(a, x) ∈ D := by
    have hxNotU : x ∉ U := Finset.mem_compl.mp hx
    have hax : a ≠ x := by
      intro heq
      exact hxNotU (heq ▸ ha)
    have hHadj : H.Adj a x := (hshape a x).mpr ⟨hax, Or.inl ha⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact SimpleGraph.mem_edgeFinset.mpr hHadj
    · intro heG
      exact hnot (SimpleGraph.mem_edgeFinset.mp heG)
  have hBadle : Bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hxV : x ∈ V := (Finset.mem_filter.mp hx).1
    have hyV : y ∈ V := (Finset.mem_filter.mp hy).1
    obtain ⟨a, ha, hax⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨b, hb, hby⟩ := (Finset.mem_filter.mp hy).2
    have heq : s(a, x) = s(b, y) :=
      (Finset.card_le_one.mp hDle) _ (hMissing a x ha hxV hax)
        _ (hMissing b y hb hyV hby)
    rcases Sym2.eq_iff.mp heq with hsame | hswap
    · exact hsame.2
    · exact False.elim ((Finset.mem_compl.mp hyV) (hswap.1 ▸ ha))
  let Good := V \ Bad
  have hGoodV : Good ⊆ V := Finset.sdiff_subset
  have hGoodCard : 3 ≤ Good.card := by
    have hpartition := Finset.card_sdiff_add_card_eq_card hBadSubset
    change Good.card + Bad.card = V.card at hpartition
    omega
  have hSpoke (a x : Fin 6) (ha : a ∈ U) (hx : x ∈ Good) : G.Adj a x := by
    have hxV : x ∈ V := (Finset.mem_sdiff.mp hx).1
    have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
    by_contra hnot
    exact hxNotBad (Finset.mem_filter.mpr ⟨hxV, a, ha, hnot⟩)
  obtain ⟨T, hTGood, hTcard⟩ := Finset.exists_subset_card_eq hGoodCard
  have hTV : T ⊆ V := hTGood.trans hGoodV
  have hRestCard : (V \ T).card = 1 := by
    simpa only [hVcard, hTcard] using Finset.card_sdiff_of_subset hTV
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (V \ T).card)
  have hwV : w ∈ V := (Finset.mem_sdiff.mp hw).1
  have hwNotT : w ∉ T := (Finset.mem_sdiff.mp hw).2
  let hubs : Fin 2 → Fin 6 := fun i => ((Finset.equivFinOfCardEq hUcard).symm i).val
  let leaves : Fin 3 → Fin 6 := fun i => ((Finset.equivFinOfCardEq hTcard).symm i).val
  have hHubsU (i : Fin 2) : hubs i ∈ U :=
    ((Finset.equivFinOfCardEq hUcard).symm i).property
  have hLeavesT (i : Fin 3) : leaves i ∈ T :=
    ((Finset.equivFinOfCardEq hTcard).symm i).property
  have hHubs : Function.Injective hubs := by
    intro i j heq
    apply (Finset.equivFinOfCardEq hUcard).symm.injective
    exact Subtype.ext heq
  have hLeaves : Function.Injective leaves := by
    intro i j heq
    apply (Finset.equivFinOfCardEq hTcard).symm.injective
    exact Subtype.ext heq
  let last : Fin 1 → Fin 6 := fun _ => w
  have hLast : Function.Injective last := fun _i _j _h => Subsingleton.elim _ _
  let tail : Fin 4 → Fin 6 := Fin.append leaves last
  have hTail : Function.Injective tail := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hLeaves, hLast, ?_⟩
    intro i j heq
    have hiw : leaves i = w := heq
    exact hwNotT (hiw ▸ hLeavesT i)
  have hTailV (j : Fin 4) : tail j ∈ V := by
    refine Fin.addCases (m := 3) (n := 1) (fun i => ?_) (fun i => ?_) j
    · simpa only [tail, Fin.append_left] using hTV (hLeavesT i)
    · simpa only [tail, Fin.append_right, last] using hwV
  let u : Fin 6 → Fin 6 := Fin.append hubs tail
  have hu : Function.Injective u := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hHubs, hTail, ?_⟩
    intro i j heq
    exact (Finset.mem_compl.mp (hTailV j)) (heq ▸ hHubsU i)
  have hActualSpoke (i : Fin 2) (j : Fin 3) : G.Adj (hubs i) (leaves j) :=
    hSpoke _ _ (hHubsU i) (hTGood (hLeavesT j))
  refine ⟨u, hu, ?_⟩
  constructor
  · change G.Adj (hubs 0) (leaves 0)
    exact hActualSpoke 0 0
  · change G.Adj (hubs 0) (leaves 1)
    exact hActualSpoke 0 1
  · change G.Adj (hubs 0) (leaves 2)
    exact hActualSpoke 0 2
  · change G.Adj (hubs 1) (leaves 0)
    exact hActualSpoke 1 0
  · change G.Adj (hubs 1) (leaves 1)
    exact hActualSpoke 1 1
  · change G.Adj (hubs 1) (leaves 2)
    exact hActualSpoke 1 2

end ErdosProblems.PathUpperFinSixExtractor

