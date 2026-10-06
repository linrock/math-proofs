module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
Finite vertex and edge partitions by connected components of a simple graph.
-/

namespace ErdosProblems.AntiRamseyPathFiveComponents

open SimpleGraph

/-- The component supports partition a finite vertex carrier. -/
theorem vertex_card_eq_sum_component_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V = ∑ C : G.ConnectedComponent, Fintype.card C.supp := by
  classical
  let supportFinset : G.ConnectedComponent → Finset V := fun C => C.supp.toFinset
  have hpair : Set.PairwiseDisjoint
      ((Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent)
      supportFinset := by
    intro C _ D _ hCD
    exact Set.disjoint_toFinset.mpr
      (G.pairwise_disjoint_supp_connectedComponent hCD)
  have hcover : (Finset.univ : Finset G.ConnectedComponent).biUnion supportFinset =
      (Finset.univ : Finset V) := by
    ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      exact Finset.mem_biUnion.mpr
        ⟨G.connectedComponentMk v, Finset.mem_univ _, by simp [supportFinset]⟩
  calc
    Fintype.card V = (Finset.univ : Finset V).card := by simp
    _ = ((Finset.univ : Finset G.ConnectedComponent).biUnion supportFinset).card :=
      congrArg Finset.card hcover.symm
    _ = ∑ C : G.ConnectedComponent, (supportFinset C).card := by
      simpa using Finset.card_biUnion hpair
    _ = ∑ C : G.ConnectedComponent, Fintype.card C.supp := by
      simp [supportFinset, Set.toFinset_card]

/-- The induced component edges partition a finite simple graph's edges. -/
theorem edge_card_eq_sum_component_edge_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card = ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet := by
  classical
  let componentEdges : G.ConnectedComponent → Finset (Sym2 V) := fun C =>
    G.edgeFinset.filter fun e => e.toFinset ⊆ C.supp.toFinset
  have hpair : Set.PairwiseDisjoint
      ((Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent)
      componentEdges := by
    intro C _ D _ hCD
    apply Finset.disjoint_left.mpr
    intro e heC heD
    have hefirst : e.out.1 ∈ e.toFinset :=
      Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e)
    have hC : e.out.1 ∈ C.supp := by
      have h := (Finset.mem_filter.mp heC).2 hefirst
      simpa using h
    have hD : e.out.1 ∈ D.supp := by
      have h := (Finset.mem_filter.mp heD).2 hefirst
      simpa using h
    have hEq : C = D := by
      have h₁ := (C.mem_supp_iff e.out.1).mp hC
      have h₂ := (D.mem_supp_iff e.out.1).mp hD
      exact h₁.symm.trans h₂
    exact hCD hEq
  have hcover : (Finset.univ : Finset G.ConnectedComponent).biUnion componentEdges =
      G.edgeFinset := by
    ext e
    constructor
    · intro he
      obtain ⟨C, _, heC⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp heC).1
    · intro heG
      induction e using Sym2.inductionOn with
      | hf u w =>
        let C : G.ConnectedComponent := G.connectedComponentMk u
        have hu : u ∈ C.supp := by simp [C]
        have hadj : G.Adj u w := by
          simpa only [G.mem_edgeFinset, G.mem_edgeSet] using heG
        have hw : w ∈ C.supp := (C.mem_supp_congr_adj hadj).mp hu
        refine Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ _, ?_⟩
        refine Finset.mem_filter.mpr ⟨heG, ?_⟩
        intro v hv
        have hvuw : v = u ∨ v = w := by
          simpa [Sym2.toFinset_mk_eq] using hv
        rcases hvuw with rfl | rfl
        · simpa using hu
        · simpa using hw
  calc
    G.edgeFinset.card =
        ((Finset.univ : Finset G.ConnectedComponent).biUnion componentEdges).card :=
      congrArg Finset.card hcover.symm
    _ = ∑ C : G.ConnectedComponent, (componentEdges C).card := by
      simpa using Finset.card_biUnion hpair
    _ = ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet := by
      apply Finset.sum_congr rfl
      intro C _
      have hset : (↑C.supp.toFinset : Set V) = C.supp := by
        ext v
        simp
      have hcard : (G.induce (↑C.supp.toFinset : Set V)).edgeFinset.card =
          Nat.card (G.induce (↑C.supp.toFinset : Set V)).edgeSet := by
        rw [Nat.card_eq_fintype_card]
        exact (G.induce (↑C.supp.toFinset : Set V)).card_edgeSet.symm
      have h := (G.card_filter_edgeFinset_toFinset_subset C.supp.toFinset).trans hcard
      rw [hset] at h
      change (componentEdges C).card = Nat.card (G.induce C.supp).edgeSet
      exact h

end ErdosProblems.AntiRamseyPathFiveComponents
