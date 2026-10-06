module

public import TightCoreBlockEdgeLedger1105
public import Mathlib.Data.Finset.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Actual unordered restoration ledger on the SAME G. The old join adjacency is the legitimate induction invariant on T; no new
classification, deletion certificate, contact count or edge ledger is supplied. Every old outsider's ORIGINAL restricted neighbor filter is literally C. Finite induction constructs its exact deletion certificate internally, then
the actual restored degree supplies the x-head. Possible new x-L edges remain present and consume one incidence each.
-/

namespace ErdosProblems.PathUpperReduction.EvenRestorationLedger1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105

/-- The old invariant derives exact ORIGINAL degree d in every actual
intermediate support retaining S. No outsider-degree oracle is supplied. -/
theorem old_outsider_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (S C T : Finset V)
    (hST : S ⊆ T) (hCS : C ⊆ S) (hCcard : C.card = d)
    (hOld : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)))
    (A : Finset V) (hSA : S ⊆ A) (hAT : A ⊆ T)
    (y : V) (hyA : y ∈ A) (hyS : y ∉ S) :
    withinDegree G A y = d := by
  classical
  have hfilter : A.filter (fun z => G.Adj y z) = C := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzA, hyz⟩ := Finset.mem_filter.mp hz
      have hrel := (hOld y (hAT hyA) z (hAT hzA)).mp hyz
      rcases hrel.2 with hSS | hSC | hCS'
      · exact False.elim (hyS hSS.1)
      · exact hSC.2
      · exact False.elim (hyS (hCS hCS'.2))
    · intro hzC
      have hzS := hCS hzC
      have hyz : y ≠ z := by
        intro heq
        exact hyS (heq.symm ▸ hzS)
      apply Finset.mem_filter.mpr
      refine ⟨hSA hzS, ?_⟩
      apply (hOld y (hAT hyA) z (hST hzS)).mpr
      exact ⟨hyz, Or.inr (Or.inl ⟨hyS, hzC⟩)⟩
  change (A.filter (fun z => G.Adj y z)).card = d
  rw [hfilter, hCcard]

/-- Construct the COMPLETE old-support certificate internally from the
actual old join invariant. It terminates at the SAME S and G. -/
theorem old_join_exact_deletion {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (S C T L : Finset V)
    (hST : S ⊆ T) (hCS : C ⊆ S) (hCcard : C.card = d)
    (hOld : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)))
    (hLO : letI : DecidableEq V := Classical.decEq V
      L ⊆ T \ S) :
    letI : DecidableEq V := Classical.decEq V
    ExactCoreDeletion G d S (S ∪ L) := by
  classical
  revert hLO
  refine Finset.induction_on L ?_ ?_
  · intro _hLO
    simpa only [Finset.union_empty] using
      (ExactCoreDeletion.stop : ExactCoreDeletion G d S S)
  · intro v R hvR ih hLO
    have hvO := hLO (Finset.mem_insert_self v R)
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hvO).2
    have hRO : R ⊆ T \ S := by
      intro z hzR
      exact hLO (Finset.mem_insert_of_mem hzR)
    have htailOld : ExactCoreDeletion G d S (S ∪ R) := ih hRO
    have hSU : S ⊆ S ∪ insert v R := Finset.subset_union_left
    have hUT : S ∪ insert v R ⊆ T := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzS | hzR
      · exact hST hzS
      · exact (Finset.mem_sdiff.mp (hLO hzR)).1
    have hvU : v ∈ S ∪ insert v R :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self v R))
    have hdegree : withinDegree G (S ∪ insert v R) v = d :=
      old_outsider_degree G d S C T hST hCS hCcard hOld
        (S ∪ insert v R) hSU hUT v hvU hvS
    have herase : (S ∪ insert v R).erase v = S ∪ R := by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hvS,
        Finset.erase_insert hvR]
    have htail : ExactCoreDeletion G d S ((S ∪ insert v R).erase v) := by
      rw [herase]
      exact htailOld
    exact ExactCoreDeletion.delete (S ∪ insert v R) v hvU hvS hdegree htail

/-- The internally selected old outsider support and the actual restored
degree derive BOTH original edge populations. In particular the unordered
cross-plus-outside count is d²; possible new x-L edges are retained.
The actual selected support and its degree come from the separate support
adapter. Neither a certificate nor a count is a public premise here. -/
theorem restoration_edge_ledgers {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (S C T L : Finset V) (x : V)
    (hd : 2 ≤ d) (hST : S ⊆ T) (hScard : S.card = d + 3)
    (hCS : C ⊆ S) (hCcard : C.card = d)
    (hOld : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v ↔ u ≠ v ∧
      ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∈ C) ∨ (v ∉ S ∧ u ∈ C)))
    (hx : x ∉ T)
    (hLO : letI : DecidableEq V := Classical.decEq V
      L ⊆ T \ S)
    (hLcard : L.card = d - 1)
    (hdegree : letI : DecidableEq V := Classical.decEq V
      withinDegree G (insert x (S ∪ L)) x = d) :
    letI : DecidableEq V := Classical.decEq V
    let W := insert x (S ∪ L)
    (withinEdges G W).card = (withinEdges G S).card + d * d ∧
      (coreCrossEdges G S W).card + (withinEdges G (W \ S)).card = d * d := by
  classical
  let W := insert x (S ∪ L)
  have hLT : L ⊆ T := by
    intro z hzL
    exact (Finset.mem_sdiff.mp (hLO hzL)).1
  have hxS : x ∉ S := fun hxS => hx (hST hxS)
  have hxSL : x ∉ S ∪ L := by
    intro hxSL
    rcases Finset.mem_union.mp hxSL with hxS' | hxL
    · exact hxS hxS'
    · exact hx (hLT hxL)
  have hSL : Disjoint S L := by
    apply Finset.disjoint_left.mpr
    intro z hzS hzL
    exact (Finset.mem_sdiff.mp (hLO hzL)).2 hzS
  have hSW : S ⊆ W := by
    intro z hzS
    exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl hzS))
  have hWcard : W.card = 2 * d + 3 := by
    dsimp only [W]
    rw [Finset.card_insert_of_notMem hxSL, Finset.card_union_of_disjoint hSL,
      hScard, hLcard]
    omega
  have hWoutside : (W \ S).card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card hSW
    rw [hScard, hWcard] at hcard
    omega
  have hOldCertificate : ExactCoreDeletion G d S (S ∪ L) :=
    old_join_exact_deletion G d S C T L hST hCS hCcard hOld hLO
  have herase : W.erase x = S ∪ L := Finset.erase_insert hxSL
  have htail : ExactCoreDeletion G d S (W.erase x) := by
    rw [herase]
    exact hOldCertificate
  have hcertificate : ExactCoreDeletion G d S W :=
    ExactCoreDeletion.delete W x (Finset.mem_insert_self x (S ∪ L))
      hxS hdegree htail
  exact ⟨last_block_edge_ledger hcertificate hWoutside,
    last_block_cross_edge_ledger hSW hcertificate hWoutside⟩

end ErdosProblems.PathUpperReduction.EvenRestorationLedger1105
