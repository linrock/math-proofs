module

public import SingleEdgeHamiltonianClosure1105
public import CoreElimination
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic

@[expose] public section

/-!
Reverses the seed-pair closure on `Fin (2 * d)` by deriving each added pair's
degree threshold from the seed degrees and applying
`SingleEdgeHamiltonianClosure1105`.
-/

namespace ErdosProblems.PathUpperReduction.SeedFillCycleClosure1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.SingleEdgeHamiltonianClosure1105
open ErdosProblems.PathUpperReduction.CoreElimination

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

noncomputable def seedPairs {V : Type*} (K : Finset V) : Finset (V × V) := by
  classical
  exact (K.product K).filter (fun p => p.1 ≠ p.2)

noncomputable def fillSeed {V : Type*} (G : SimpleGraph V)
    (K : Finset V) : SimpleGraph V := by
  classical
  exact G ⊔ fromEdgeSet (seedPairs K |>.image (fun p => s(p.1, p.2)) : Set (Sym2 V))

theorem original_le_fillSeed {V : Type*} (G : SimpleGraph V) (K : Finset V) :
    G ≤ fillSeed G K := le_sup_left

/-- Only actual seed pairs are filled, including when the ambient type has
vertices outside the intended eventual carrier. -/
theorem fillSeed_isClique {V : Type*} (G : SimpleGraph V) (K : Finset V) :
    (fillSeed G K).IsClique (K : Set V) := by
  classical
  intro a ha b hb hab
  apply Or.inr
  apply (fromEdgeSet_adj _).mpr
  refine ⟨?_, hab⟩
  change s(a, b) ∈ (seedPairs K).image (fun p => s(p.1, p.2))
  exact Finset.mem_image.mpr ⟨(a, b),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩

/-- Exact adjacency, used to transport this SAME seed filling to the actual
induced carrier and its finite reindexing. -/
theorem fillSeed_adj_iff {V : Type*} (G : SimpleGraph V) (K : Finset V)
    (x y : V) :
    (fillSeed G K).Adj x y ↔ G.Adj x y ∨ (x ∈ K ∧ y ∈ K ∧ x ≠ y) := by
  classical
  constructor
  · intro h
    rcases h with hG | hfill
    · exact Or.inl hG
    · have he := ((fromEdgeSet_adj _).mp hfill).1
      change s(x, y) ∈ (seedPairs K).image (fun p => s(p.1, p.2)) at he
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp he
      have hpK := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hne := ((fromEdgeSet_adj _).mp hfill).2
      apply Or.inr
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact ⟨heq.1 ▸ hpK.1, heq.2 ▸ hpK.2, hne⟩
      · exact ⟨heq.2 ▸ hpK.2, heq.1 ▸ hpK.1, hne⟩
  · rintro (hG | ⟨hx, hy, hne⟩)
    · exact original_le_fillSeed G K hG
    · exact fillSeed_isClique G K hx hy hne

/-- Filling seed pairs changes no original adjacency at a restored vertex. -/
theorem fillSeed_adj_outside {V : Type*} (G : SimpleGraph V) (K : Finset V)
    {x y : V} (hx : x ∉ K) : (fillSeed G K).Adj x y ↔ G.Adj x y := by
  classical
  constructor
  · intro h
    rcases h with hG | hfill
    · exact hG
    · have he := ((fromEdgeSet_adj _).mp hfill).1
      change s(x, y) ∈ (seedPairs K).image (fun p => s(p.1, p.2)) at he
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp he
      have hpK := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact False.elim (hx (heq.1 ▸ hpK.1))
      · exact False.elim (hx (heq.2 ▸ hpK.2))
  · intro h
    exact original_le_fillSeed G K h

theorem fillSeed_withinDegree_outside {V : Type*} [Fintype V]
    (G : SimpleGraph V) (K U : Finset V) {x : V} (hx : x ∉ K) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    withinDegree (fillSeed G K) U x = withinDegree G U x := by
  classical
  unfold withinDegree
  congr 1
  apply Finset.filter_congr
  intro y _hy
  exact fillSeed_adj_outside G K hx

/-- Every finite cover of the filled seed has at least |K|-1 vertices; the
complement inside K is independent in a clique and therefore has size≤1. -/
theorem fillSeed_cover_bound {V : Type*} (G : SimpleGraph V) (K X : Finset V)
    (hcover : ∀ u ∈ K, ∀ v ∈ K, (fillSeed G K).Adj u v → u ∈ X ∨ v ∈ X) :
    K.card - 1 ≤ X.card := by
  classical
  have hsmall : (K \ X).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := Finset.mem_sdiff.mp ha
    have hb' := Finset.mem_sdiff.mp hb
    by_contra hab
    rcases hcover a ha'.1 b hb'.1
      (fillSeed_isClique G K ha'.1 hb'.1 hab) with haX | hbX
    · exact ha'.2 haX
    · exact hb'.2 hbX
  have hledger := Finset.card_sdiff_add_card_inter K X
  have hinter : (K ∩ X).card ≤ X.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

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

/-- On the ACTUAL2d carrier, original seed degree≥d derives all pair bounds
internally and finite reversal preserves its spanning-cycle predicate. -/
theorem cycle_contained_fill_seed_iff {d : ℕ} (hd : 2 ≤ d)
    (G : SimpleGraph (Fin (2 * d))) (K : Finset (Fin (2 * d)))
    (hseed : ∀ x ∈ K, d ≤ G.degree x) :
    cycleGraph (2 * d) ⊑ fillSeed G K ↔ cycleGraph (2 * d) ⊑ G := by
  classical
  have hpair : ∀ p, p ∈ seedPairs K → p.1 ≠ p.2 ∧
      2 * d ≤ G.degree p.1 + G.degree p.2 := by
    intro p hp
    have hp' : p ∈ K.product K ∧ p.1 ≠ p.2 := by
      simpa only [seedPairs, Finset.mem_filter] using hp
    have hprod := Finset.mem_product.mp hp'.1
    refine ⟨hp'.2, ?_⟩
    have hleft := hseed p.1 hprod.1
    have hright := hseed p.2 hprod.2
    omega
  simpa only [fillSeed, fillPairs, Finset.coe_image] using
    finite_pair_closure_iff (by omega) G (seedPairs K) hpair

end ErdosProblems.PathUpperReduction.SeedFillCycleClosure1105
