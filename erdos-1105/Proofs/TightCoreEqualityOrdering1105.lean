module

public import CoreElimination

@[expose] public section

/-!
Exact deletion certificate for ALL actual outsiders. The certificate terminates only at the supplied ACTUAL greatest d-core. Every deletion has exactly d neighbors in its remaining carrier. No ordering,
degree oracle, clique, cycle classification, coloring or rainbow conclusion
is a premise of the original full-host caller.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination

namespace ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105

variable {V : Type*} [Fintype V]

/-- A complete exact forward-degree deletion order, represented by finite
induction rather than list indices. Its ONLY terminal carrier is S. Each
constructor removes one actual outsider; the head's degree is measured in
the same actual current carrier. The explicit classical erase keeps the
certificate independent of any externally supplied DecidableEq instance. -/
inductive ExactCoreDeletion (G : SimpleGraph V) (d : ℕ) (S : Finset V) :
    Finset V → Prop where
  | stop : ExactCoreDeletion G d S S
  | delete (T : Finset V) (x : V) (hx : x ∈ T) (hxS : x ∉ S)
      (hdegree : withinDegree G T x = d)
      (tail : ExactCoreDeletion G d S (@Finset.erase V (Classical.decEq V) T x)) :
      ExactCoreDeletion G d S T

/-- Every tight actual induced carrier has a complete exact deletion
certificate. The d<=|S| input normalizes the existing maximum in the generic
bound; the full nonempty-core caller below derives it internally. -/
theorem exact_core_deletion_of_tight_induced_count
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hcore : degreeCore G d = S) (hdS : d ≤ S.card)
    (T : Finset V) (hST : S ⊆ T)
    (htight : (withinEdges G T).card =
      S.card.choose 2 + d * (T.card - S.card)) :
    ExactCoreDeletion G d S T := by
  classical
  have hmax : max d (degreeCore G d).card = S.card := by
    rw [hcore]
    exact max_eq_right hdS
  let P : Finset V → Prop := fun U => S ⊆ U →
    (withinEdges G U).card = S.card.choose 2 + d * (U.card - S.card) →
      ExactCoreDeletion G d S U
  have hP : ∀ U, P U := by
    intro U
    refine Finset.strongInductionOn U ?_
    intro U ih
    dsimp only [P]
    intro hSU hU
    by_cases hbase : U = S
    · subst U
      exact ExactCoreDeletion.stop
    · have hcard : S.card < U.card := by
        have hle : S.card ≤ U.card := Finset.card_le_card hSU
        by_contra hnot
        have hUS : U.card ≤ S.card := by omega
        have heq : S = U := Finset.eq_of_subset_of_card_le hSU hUS
        exact hbase heq.symm
      have hCU : degreeCore G d ⊆ U := by
        simpa only [hcore] using hSU
      have hlarge : max d (degreeCore G d).card < U.card := by
        simpa only [hmax] using hcard
      obtain ⟨x, hxU, hxC, hlow⟩ := outside_core_low_degree G d U hCU hlarge
      have hxS : x ∉ S := by simpa only [hcore] using hxC
      have hSerase : S ⊆ U.erase x := by
        intro z hzS
        apply Finset.mem_erase.mpr
        refine ⟨?_, hSU hzS⟩
        intro hzx
        exact hxS (hzx ▸ hzS)
      have hCerase : degreeCore G d ⊆ U.erase x := by
        simpa only [hcore] using hSerase
      have hMerase : max d (degreeCore G d).card ≤ (U.erase x).card := by
        rw [hmax]
        exact Finset.card_le_card hSerase
      have hbound := core_induced_edge_bound G d (U.erase x) hCerase hMerase
      rw [hmax] at hbound
      have hledger := withinEdges_erase_ledger G U x hxU
      have hcardErase : (U.erase x).card = U.card - 1 :=
        Finset.card_erase_of_mem hxU
      have hsteps : U.card - S.card = ((U.erase x).card - S.card) + 1 := by
        omega
      have hbudget : S.card.choose 2 + d * (U.card - S.card) =
          (S.card.choose 2 + d * ((U.erase x).card - S.card)) + d := by
        rw [hsteps, Nat.mul_add, Nat.mul_one]
        exact (Nat.add_assoc _ _ _).symm
      have heq : (withinEdges G (U.erase x)).card + withinDegree G U x =
          (S.card.choose 2 + d * ((U.erase x).card - S.card)) + d := by
        calc
          (withinEdges G (U.erase x)).card + withinDegree G U x =
              (withinEdges G U).card := hledger.symm
          _ = S.card.choose 2 + d * (U.card - S.card) := hU
          _ = (S.card.choose 2 + d * ((U.erase x).card - S.card)) + d := hbudget
      have hdegree : withinDegree G U x = d := by omega
      have htail : (withinEdges G (U.erase x)).card =
          S.card.choose 2 + d * ((U.erase x).card - S.card) := by omega
      have hcertificate : ExactCoreDeletion G d S (U.erase x) :=
        ih (U.erase x) (Finset.erase_ssubset hxU) hSerase htail
      exact ExactCoreDeletion.delete U x hxU hxS hdegree hcertificate
  exact hP T hST htight

/-- The original full-carrier endpoint: actual nonempty greatest core and
tight edge count imply an exact deletion order of ALL outsiders. No public
order or supplied d<=core-size hypothesis appears. The outside set may be
empty, in which case the certificate stops immediately at the actual core. -/
theorem exact_core_deletion_of_tight_nonempty_core
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hcore : degreeCore G d = S) (hS : S.Nonempty)
    (htight : Nat.card G.edgeSet =
      S.card.choose 2 + d * (Nat.card V - S.card)) :
    ExactCoreDeletion G d S Finset.univ := by
  classical
  obtain ⟨x, hxS⟩ := hS
  have hgood : GoodCore G d S := by
    rw [← hcore]
    exact degree_core_good G d
  have hdegree : d < (S.filter (fun z => G.Adj x z)).card := hgood x hxS
  have hfilter : (S.filter (fun z => G.Adj x z)).card ≤ S.card := by
    apply Finset.card_le_card
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hdS : d ≤ S.card := by omega
  have hEdgesUniv : withinEdges G Finset.univ = G.edgeFinset := by
    ext e
    simp [withinEdges]
  have hfull : (withinEdges G Finset.univ).card =
      S.card.choose 2 + d * ((Finset.univ : Finset V).card - S.card) := by
    simpa only [hEdgesUniv, Finset.card_univ, Nat.card_eq_fintype_card,
      G.card_edgeSet] using htight
  exact exact_core_deletion_of_tight_induced_count G d S hcore hdS
    Finset.univ (Finset.subset_univ S) hfull

end ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
