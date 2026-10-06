module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Lean.Elab.Tactic.Omega

@[expose] public section

open Finset

namespace ErdosProblems.PathUpperReduction

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_degrees_inside_actual_part
    (H : SimpleGraph V) [DecidableRel H.Adj] (L : Finset V) :
    (∑ v ∈ L, (H.between (↑L : Set V) (↑L : Set V)).degree v) =
      2 * (H.induce (↑L : Set V)).edgeFinset.card := by
  classical
  let A : SimpleGraph V := H.between (↑L : Set V) (↑L : Set V)
  have hsupport : A.support ⊆ (↑L : Set V) := by
    intro v hv
    obtain ⟨w, hadj⟩ := hv
    change H.Adj v w ∧ ((v ∈ L ∧ w ∈ L) ∨ (v ∈ L ∧ w ∈ L)) at hadj
    exact hadj.2.elim And.left And.left
  have hcard : (H.induce (↑L : Set V)).edgeFinset.card = A.edgeFinset.card := by
    rw [← H.card_filter_edgeFinset_toFinset_subset L]
    congr 1
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Finset.mem_filter, A, SimpleGraph.between_adj, Finset.mem_coe]
      constructor
      · rintro ⟨hxy, hsub⟩
        have hx : x ∈ L := hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y))
        have hy : y ∈ L := hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y))
        exact ⟨hxy, Or.inl ⟨hx, hy⟩⟩
      · rintro ⟨hxy, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩ <;>
        refine ⟨hxy, ?_⟩ <;>
        intro z hz <;>
        (rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hz) with rfl | rfl <;> assumption)
  have hsum : (∑ v ∈ L, A.degree v) = ∑ v, A.degree v := by
    apply Finset.sum_subset (Finset.subset_univ L)
    intro v _ hv
    apply (A.degree_eq_zero_iff_notMem_support v).mpr
    exact fun hvs => hv (hsupport hvs)
  simpa only [hcard] using hsum.trans A.sum_degrees_eq_twice_card_edges

theorem degree_split_on_actual_part
    (H : SimpleGraph V) [DecidableRel H.Adj] (L : Finset V)
    (v : V) (hv : v ∈ L) :
    H.degree v = (H.between (↑L : Set V) (↑L : Set V)).degree v +
      (H.between (↑L : Set V) (↑(Lᶜ) : Set V)).degree v := by
  let A : SimpleGraph V := H.between (↑L : Set V) (↑L : Set V)
  let B : SimpleGraph V := H.between (↑L : Set V) (↑(Lᶜ) : Set V)
  have hneighbors : H.neighborFinset v = A.neighborFinset v ∪ B.neighborFinset v := by
    ext w
    by_cases hw : w ∈ L <;>
      simp [A, B, SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj, hv, hw]
  have hdisjoint : Disjoint (A.neighborFinset v) (B.neighborFinset v) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hwA hwB
    have hA : H.Adj v w ∧ w ∈ L := by
      simpa [A, SimpleGraph.between_adj, hv] using hwA
    have hB : H.Adj v w ∧ w ∉ L := by
      simpa [B, SimpleGraph.between_adj, hv] using hwB
    exact hB.2 hA.2
  change (H.neighborFinset v).card =
    (A.neighborFinset v).card + (B.neighborFinset v).card
  rw [hneighbors, Finset.card_union_of_disjoint hdisjoint]

theorem degree_sum_on_actual_part
    (H : SimpleGraph V) [DecidableRel H.Adj] (L : Finset V) :
    (∑ v ∈ L, H.degree v) =
      2 * (H.induce (↑L : Set V)).edgeFinset.card +
        (H.between (↑L : Set V) (↑(Lᶜ) : Set V)).edgeFinset.card := by
  let B : SimpleGraph V := H.between (↑L : Set V) (↑(Lᶜ) : Set V)
  have hdisjoint : Disjoint (↑L : Set V) (↑(Lᶜ) : Set V) := by
    refine Set.disjoint_left.mpr ?_
    intro v hvL hvC
    exact (Finset.mem_compl.mp hvC) hvL
  have hbip : B.IsBipartiteWith (↑L : Set V) (↑(Lᶜ) : Set V) :=
    SimpleGraph.between_isBipartiteWith hdisjoint
  have hcross : (∑ v ∈ L, B.degree v) = B.edgeFinset.card :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip
  calc
    (∑ v ∈ L, H.degree v) =
        ∑ v ∈ L, ((H.between (↑L : Set V) (↑L : Set V)).degree v + B.degree v) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact degree_split_on_actual_part H L v hv
    _ = (∑ v ∈ L, (H.between (↑L : Set V) (↑L : Set V)).degree v) +
        ∑ v ∈ L, B.degree v := Finset.sum_add_distrib
    _ = 2 * (H.induce (↑L : Set V)).edgeFinset.card + B.edgeFinset.card := by
      rw [sum_degrees_inside_actual_part H L, hcross]

theorem actual_cut_degree_ledger
    (H : SimpleGraph V) [DecidableRel H.Adj] (L : Finset V) :
    H.edgeFinset.card + (H.induce (↑L : Set V)).edgeFinset.card =
      (H.induce (↑(Lᶜ) : Set V)).edgeFinset.card + ∑ v ∈ L, H.degree v := by
  have hleft := degree_sum_on_actual_part H L
  have hright := degree_sum_on_actual_part H (Lᶜ)
  have hcrossEq :
      (H.between (↑(Lᶜ) : Set V) (↑(Lᶜᶜ) : Set V)).edgeFinset.card =
        (H.between (↑L : Set V) (↑(Lᶜ) : Set V)).edgeFinset.card := by
    congr 1
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.coe_compl, compl_compl]
    rw [SimpleGraph.between_comm]
  rw [hcrossEq] at hright
  have hpartition := Finset.sum_add_sum_compl L (fun v => H.degree v)
  have hhandshake := H.sum_degrees_eq_twice_card_edges
  omega

end ErdosProblems.PathUpperReduction

