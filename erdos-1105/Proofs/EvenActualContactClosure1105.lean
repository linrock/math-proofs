module

public import SingleEdgeHamiltonianClosure1105
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic

@[expose] public section

/-!
Finite reversal of the original contact filling.

The public theorem derives every added pair's original degree threshold from
the ORIGINAL clique and an ORIGINAL outsider witness for its contact vertex. It supplies neither a filling order nor a favorable path/cycle. All degrees
are measured on SAME Fin (2*d+3), including every vertex of that carrier.
-/

namespace ErdosProblems.PathUpperReduction.EvenActualContactClosure1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.SingleEdgeHamiltonianClosure1105

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Core vertices with an ACTUAL ORIGINAL outsider neighbor. -/
noncomputable def originalContacts {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact S.filter (fun a => ∃ x, x ∉ S ∧ G.Adj x a)

/-- Precisely the outsider/original-contact pairs, with undirected edges. -/
noncomputable def originalContactEdges {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact ((Finset.univ \ S).product (originalContacts G S)).image
    (fun p => s(p.1, p.2))

/-- Fill only those original contact pairs; no vertex or outsider edge is added. -/
noncomputable def fillOriginalContacts {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : SimpleGraph (Fin n) :=
  G ⊔ fromEdgeSet (originalContactEdges G S : Set (Sym2 (Fin n)))

noncomputable def fillPairs {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) := by
  classical
  exact G ⊔ fromEdgeSet (P.image (fun p => s(p.1, p.2)) : Set (Sym2 (Fin n)))

theorem fillPairs_insert {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    fillPairs G (insert p P) = fillPairs G P ⊔ fromEdgeSet {s(p.1, p.2)} := by
  classical
  have hset :
      ((insert p P).image (fun q => s(q.1, q.2)) : Set (Sym2 (Fin n))) =
        {s(p.1, p.2)} ∪ (P.image (fun q => s(q.1, q.2)) : Set (Sym2 (Fin n))) := by
    ext e
    simp only [Finset.image_insert, Finset.mem_coe, Finset.mem_insert,
      Set.mem_union, Set.mem_singleton_iff]
  simp only [fillPairs, hset, fromEdgeSet_union]
  ac_rfl

/-- Internal finite induction: the caller supplies ORIGINAL pair bounds here;
the public actual-contact theorem derives all of them from original data. -/
theorem finite_pair_closure_iff {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (P : Finset (Fin n × Fin n))
    (hpair : ∀ p, p ∈ P → p.1 ≠ p.2 ∧ n ≤ G.degree p.1 + G.degree p.2) :
    cycleGraph n ⊑ fillPairs G P ↔ cycleGraph n ⊑ G := by
  classical
  revert hpair
  induction P using Finset.induction_on with
  | empty => intro _hpair; simp [fillPairs]
  | @insert p P _hp ih =>
    intro hpair
    have hthis := hpair p (Finset.mem_insert_self p P)
    have hrest : ∀ q, q ∈ P → q.1 ≠ q.2 ∧ n ≤ G.degree q.1 + G.degree q.2 := by
      intro q hq
      exact hpair q (Finset.mem_insert_of_mem hq)
    have hrestIff := ih hrest
    let H : SimpleGraph (Fin n) := fillPairs G P
    have hGH : G ≤ H := le_sup_left
    have hdegree : n ≤ H.degree p.1 + H.degree p.2 := by
      exact hthis.2.trans (Nat.add_le_add
        (G.degree_le_of_le (v := p.1) hGH) (G.degree_le_of_le (v := p.2) hGH))
    have hsingle : cycleGraph n ⊑ (H ⊔ fromEdgeSet {s(p.1, p.2)}) ↔
        cycleGraph n ⊑ H := by
      by_cases hadj : H.Adj p.1 p.2
      · have hsubset : ({s(p.1, p.2)} : Set (Sym2 (Fin n))) ⊆ H.edgeSet := by
          intro e he
          rcases Set.mem_singleton_iff.mp he with rfl
          exact hadj
        have hedge : fromEdgeSet {s(p.1, p.2)} ≤ H := by
          simpa only [fromEdgeSet_edgeSet] using fromEdgeSet_mono hsubset
        rw [sup_eq_left.mpr hedge]
      · exact cycle_contained_add_edge_iff hn H p.1 p.2 hthis.1 hadj hdegree
    rw [fillPairs_insert]
    exact hsingle.trans hrestIff

theorem contacted_core_degree {d : ℕ}
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    {a : Fin (2 * d + 3)} (ha : a ∈ originalContacts G S) :
    d + 3 ≤ G.degree a := by
  classical
  have hacontact : a ∈ S ∧ ∃ w, w ∉ S ∧ G.Adj w a := by
    simpa only [originalContacts, Finset.mem_filter] using ha
  obtain ⟨w, hwS, hwa⟩ := hacontact.2
  have hwErase : w ∉ S.erase a := by
    intro hw
    exact hwS (Finset.mem_of_mem_erase hw)
  let T : Finset (Fin (2 * d + 3)) := insert w (S.erase a)
  have hTcard : T.card = S.card := by
    change (insert w (S.erase a)).card = S.card
    rw [Finset.card_insert_of_notMem hwErase]
    exact Finset.card_erase_add_one hacontact.1
  have hTsub : T ⊆ G.neighborFinset a := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzw | hzErase
    · subst z
      exact (mem_neighborFinset (G := G) (v := a) w).mpr hwa.symm
    · have hzS := (Finset.mem_erase.mp hzErase).2
      have hza := (Finset.mem_erase.mp hzErase).1
      exact (mem_neighborFinset (G := G) (v := a) z).mpr
        (hclique hacontact.1 hzS hza.symm)
  have hbound := Finset.card_le_card hTsub
  rw [hTcard, hScard, card_neighborFinset_eq_degree] at hbound
  exact hbound

/-- Filling exactly the ORIGINAL contacted-core pairs preserves the SAME
spanning-cycle predicate. Original pair thresholds and finite reversal are
derived internally, without a supplied order, path, cycle or degree oracle. -/
theorem cycle_contained_fill_original_contacts_iff {d : ℕ} (_hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x) :
    cycleGraph (2 * d + 3) ⊑ fillOriginalContacts G S ↔
      cycleGraph (2 * d + 3) ⊑ G := by
  classical
  let P : Finset (Fin (2 * d + 3) × Fin (2 * d + 3)) :=
    (Finset.univ \ S).product (originalContacts G S)
  have hpair : ∀ p, p ∈ P → p.1 ≠ p.2 ∧
      2 * d + 3 ≤ G.degree p.1 + G.degree p.2 := by
    intro p hp
    have hprod := Finset.mem_product.mp hp
    have hxS : p.1 ∉ S := (Finset.mem_sdiff.mp hprod.1).2
    have haS : p.2 ∈ S := by
      have hcontact : p.2 ∈ S ∧ ∃ w, w ∉ S ∧ G.Adj w p.2 := by
        simpa only [originalContacts, Finset.mem_filter] using hprod.2
      exact hcontact.1
    have hne : p.1 ≠ p.2 := by
      intro heq
      exact hxS (heq.symm ▸ haS)
    refine ⟨hne, ?_⟩
    have hout := houtsider p.1 hxS
    have hcore := contacted_core_degree G S hScard hclique hprod.2
    omega
  have hclosure := finite_pair_closure_iff (by omega) G P hpair
  simpa only [fillOriginalContacts, originalContactEdges, fillPairs, P] using hclosure

end ErdosProblems.PathUpperReduction.EvenActualContactClosure1105
