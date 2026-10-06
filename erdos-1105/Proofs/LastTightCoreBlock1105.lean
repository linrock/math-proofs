module

public import TightCoreEqualityOrdering1105

@[expose] public section

/-!
Extract the actual last d outsiders from a COMPLETE
exact-core deletion certificate. Same G and S throughout; no supplied order,
minimum-degree oracle, positive d, clique or graph classification premise.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105

namespace ErdosProblems.PathUpperReduction.LastTightCoreBlock1105

variable {V : Type*} [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

omit [Fintype V] in
theorem certificate_core_subset {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (h : ExactCoreDeletion G d S T) : S ⊆ T := by
  classical
  induction h with
  | stop => exact fun _ hx => hx
  | delete T x hx hxS hdegree tail ih =>
      intro z hz
      exact (Finset.mem_erase.mp (ih hz)).2

omit [Fintype V] in
theorem certificate_outsider_degree_ge {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (h : ExactCoreDeletion G d S T) :
    ∀ x ∈ T, x ∉ S → d ≤ withinDegree G T x := by
  classical
  induction h with
  | stop =>
      intro x hx hxS
      exact False.elim (hxS hx)
  | delete T y hy hyS hdegree tail ih =>
      intro x hx hxS
      by_cases hxy : x = y
      · subst x
        exact le_of_eq hdegree.symm
      · have hxTail : x ∈ T.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
        have htailDegree := ih x hxTail hxS
        have hmono : withinDegree G (T.erase y) x ≤ withinDegree G T x := by
          unfold withinDegree
          exact Finset.card_le_card (Finset.filter_subset_filter
            (fun z => G.Adj x z) (Finset.erase_subset y T))
        exact htailDegree.trans hmono

omit [Fintype V] in
/-- A complete exact deletion certificate with at least d actual outsiders
has an actual suffix carrier with exactly d outsiders. The suffix retains the
whole same core and a complete same-G certificate; every outsider has degree
at least d INSIDE this carrier, derived from the recorded forward degrees.
For d=0 the suffix is precisely S, so the degree assertion is vacuous. -/
theorem exists_last_tight_core_block (G : SimpleGraph V) (d : ℕ)
    (S T : Finset V) (hcertificate : ExactCoreDeletion G d S T)
    (houtside : d ≤ (T \ S).card) :
    ∃ U : Finset V, S ⊆ U ∧ U ⊆ T ∧ (U \ S).card = d ∧
      ExactCoreDeletion G d S U ∧
      ∀ x ∈ U, x ∉ S → d ≤ withinDegree G U x := by
  classical
  revert houtside
  induction hcertificate with
  | stop =>
      intro houtside
      have hd0 : d = 0 := by
        have hh : d ≤ 0 := by
          simpa only [Finset.sdiff_self, Finset.card_empty] using houtside
        omega
      refine ⟨S, (fun _ hx => hx), (fun _ hx => hx), ?_,
        ExactCoreDeletion.stop, ?_⟩
      · simp only [Finset.sdiff_self, Finset.card_empty, hd0]
      · exact certificate_outsider_degree_ge ExactCoreDeletion.stop
  | delete T x hx hxS hdegree tail ih =>
      intro houtside
      have hcurrent : ExactCoreDeletion G d S T :=
        ExactCoreDeletion.delete T x hx hxS hdegree tail
      by_cases hlast : (T \ S).card = d
      · exact ⟨T, certificate_core_subset hcurrent, (fun _ hz => hz), hlast,
          hcurrent, certificate_outsider_degree_ge hcurrent⟩
      · have hxOutside : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
        have hcount : ((T.erase x) \ S).card = (T \ S).card - 1 := by
          rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem hxOutside]
        have htailOutside : d ≤ ((T.erase x) \ S).card := by
          rw [hcount]
          omega
        obtain ⟨U, hSU, hUtail, hUcard, hUcertificate, hUdegree⟩ := ih htailOutside
        refine ⟨U, hSU, ?_, hUcard, hUcertificate, hUdegree⟩
        exact hUtail.trans (Finset.erase_subset x T)

/-- Full ambient actual-core caller. Tight original edge count and the actual
nonempty greatest d-core derive the COMPLETE certificate internally; the only
size premise is that the original ambient outside population is at least d.
All ambient vertices, including isolates, remain in Finset.univ. No order,
suffix, minimum degree or d<=|S| input is supplied by the caller. -/
theorem exists_last_tight_core_block_of_tight_nonempty_core
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hcore : degreeCore G d = S) (hS : S.Nonempty)
    (htight : Nat.card G.edgeSet =
      S.card.choose 2 + d * (Nat.card V - S.card))
    (houtside : d ≤ Nat.card V - S.card) :
    ∃ U : Finset V, S ⊆ U ∧ U ⊆ Finset.univ ∧ (U \ S).card = d ∧
      ExactCoreDeletion G d S U ∧
      ∀ x ∈ U, x ∉ S → d ≤ withinDegree G U x := by
  classical
  have hcertificate : ExactCoreDeletion G d S Finset.univ :=
    exact_core_deletion_of_tight_nonempty_core G d S hcore hS htight
  have houtsideFinset : d ≤ ((Finset.univ : Finset V) \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
    simpa only [Nat.card_eq_fintype_card] using houtside
  exact exists_last_tight_core_block G d S Finset.univ hcertificate houtsideFinset

end ErdosProblems.PathUpperReduction.LastTightCoreBlock1105
