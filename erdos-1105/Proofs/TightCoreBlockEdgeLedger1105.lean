module

public import LastTightCoreBlock1105

@[expose] public section

/-!
Suffix edge ledger for the even rigidity obstruction on `G`, retaining internal
outsider edges.
-/

noncomputable section

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreEqualityOrdering1105
open ErdosProblems.PathUpperReduction.LastTightCoreBlock1105

namespace ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105

variable {V : Type*} [Fintype V]

-- Internal classical instance only: no caller-supplied equality decision or
-- extra mathematical hypothesis is added to the public statements.
local instance : DecidableEq V := Classical.decEq V

/-- Every actual edge of the carrier that is not wholly inside S. This
includes BOTH cross edges and edges internal to the actual outsiders. -/
noncomputable def nonCoreEdges (G : SimpleGraph V) (S U : Finset V) :
    Finset (Sym2 V) := by
  classical
  exact (withinEdges G U).filter (fun e => ¬ e.toFinset ⊆ S)

/-- Actual cross edges: among noncore edges, exclude those whose two
endpoints are both in the actual outsider carrier U\S. -/
noncomputable def coreCrossEdges (G : SimpleGraph V) (S U : Finset V) :
    Finset (Sym2 V) := by
  classical
  exact (nonCoreEdges G S U).filter (fun e => ¬ e.toFinset ⊆ U \ S)

/-- A complete exact deletion certificate telescopes the actual undirected
edge ledger. No supplied intermediate edge equality or clique is required. -/
theorem certificate_edge_ledger {G : SimpleGraph V} {d : ℕ}
    {S T : Finset V} (hcertificate : ExactCoreDeletion G d S T) :
    (withinEdges G T).card =
      (withinEdges G S).card + d * (T \ S).card := by
  classical
  induction hcertificate with
  | stop => simp only [Finset.sdiff_self, Finset.card_empty,
      Nat.mul_zero, Nat.add_zero]
  | delete T x hx hxS hdegree tail ih =>
      have hxOutside : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hx, hxS⟩
      have hcount : (T \ S).card = ((T.erase x) \ S).card + 1 := by
        rw [Finset.erase_sdiff_comm]
        exact (Finset.card_erase_add_one hxOutside).symm
      calc
        (withinEdges G T).card =
            (withinEdges G (T.erase x)).card + withinDegree G T x :=
          withinEdges_erase_ledger G T x hx
        _ = ((withinEdges G S).card + d * ((T.erase x) \ S).card) + d := by
          rw [ih, hdegree]
        _ = (withinEdges G S).card + d * (((T.erase x) \ S).card + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        _ = (withinEdges G S).card + d * (T \ S).card := by rw [← hcount]

/-- For the actual last d outsiders the exact surplus above the actual core
edge count is d*d, even when the outsiders contain edges. -/
theorem last_block_edge_ledger {G : SimpleGraph V} {d : ℕ}
    {S U : Finset V} (hcertificate : ExactCoreDeletion G d S U)
    (houtside : (U \ S).card = d) :
    (withinEdges G U).card = (withinEdges G S).card + d * d := by
  rw [certificate_edge_ledger hcertificate, houtside]

theorem withinEdges_filter_core (G : SimpleGraph V) (S U : Finset V)
    (hSU : S ⊆ U) :
    letI : DecidableEq V := Classical.decEq V
    (withinEdges G U).filter (fun e => e.toFinset ⊆ S) = withinEdges G S := by
  classical
  unfold withinEdges
  ext e
  constructor
  · intro he
    obtain ⟨heU, heS⟩ := Finset.mem_filter.mp he
    obtain ⟨heG, _⟩ := Finset.mem_filter.mp heU
    exact Finset.mem_filter.mpr ⟨heG, heS⟩
  · intro he
    obtain ⟨heG, heS⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨heG, heS.trans hSU⟩, heS⟩

/-- The last block's actual cross plus internal-outside population has d*d
edges. Core containment is exactly the property returned by extraction. -/
theorem nonCoreEdges_card_of_last_block {G : SimpleGraph V} {d : ℕ}
    {S U : Finset V} (hSU : S ⊆ U)
    (hcertificate : ExactCoreDeletion G d S U)
    (houtside : (U \ S).card = d) :
    (nonCoreEdges G S U).card = d * d := by
  classical
  have hpartition := (withinEdges G U).card_filter_add_card_filter_not
    (fun e => e.toFinset ⊆ S)
  rw [withinEdges_filter_core G S U hSU] at hpartition
  have hledger := last_block_edge_ledger hcertificate houtside
  unfold nonCoreEdges
  omega

theorem nonCoreEdges_filter_outside (G : SimpleGraph V)
    (S U : Finset V) :
    letI : DecidableEq V := Classical.decEq V
    (nonCoreEdges G S U).filter (fun e => e.toFinset ⊆ U \ S) =
      withinEdges G (U \ S) := by
  classical
  unfold nonCoreEdges withinEdges
  ext e
  constructor
  · intro he
    obtain ⟨heNonCore, heOutside⟩ := Finset.mem_filter.mp he
    obtain ⟨heU, _⟩ := Finset.mem_filter.mp heNonCore
    obtain ⟨heG, _⟩ := Finset.mem_filter.mp heU
    exact Finset.mem_filter.mpr ⟨heG, heOutside⟩
  · intro he
    obtain ⟨heG, heOutside⟩ := Finset.mem_filter.mp he
    have heU : e.toFinset ⊆ U := heOutside.trans Finset.sdiff_subset
    have heNotCore : ¬ e.toFinset ⊆ S := by
      intro heCore
      obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e)
      exact (Finset.mem_sdiff.mp (heOutside hz)).2 (heCore hz)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨heG, heU⟩, heNotCore⟩, heOutside⟩

/-- Exact even-rigidity input: actual cross edges plus actual edges among
the last d outsiders sum to d*d. An outsider edge consumes one unit of the
cross-edge budget; it is not forbidden by tightness alone. -/
theorem last_block_cross_edge_ledger {G : SimpleGraph V} {d : ℕ}
    {S U : Finset V} (hSU : S ⊆ U)
    (hcertificate : ExactCoreDeletion G d S U)
    (houtside : (U \ S).card = d) :
    (coreCrossEdges G S U).card + (withinEdges G (U \ S)).card = d * d := by
  classical
  have hpartition := (nonCoreEdges G S U).card_filter_add_card_filter_not
    (fun e => e.toFinset ⊆ U \ S)
  rw [nonCoreEdges_filter_outside G S U] at hpartition
  have hcount := nonCoreEdges_card_of_last_block hSU hcertificate houtside
  unfold coreCrossEdges
  omega

/-- A concrete cross-edge lower constraint, retaining the exact possible
internal outsider edge capacity instead of assuming it is zero. -/
theorem last_block_core_cross_edges_lower {G : SimpleGraph V} {d : ℕ}
    {S U : Finset V} (hSU : S ⊆ U)
    (hcertificate : ExactCoreDeletion G d S U)
    (houtside : (U \ S).card = d) :
    d * d ≤ (coreCrossEdges G S U).card + d.choose 2 := by
  have hledger := last_block_cross_edge_ledger hSU hcertificate houtside
  have hbound := withinEdges_card_le_choose G (U \ S)
  rw [houtside] at hbound
  calc
    d * d = (coreCrossEdges G S U).card + (withinEdges G (U \ S)).card :=
      hledger.symm
    _ ≤ (coreCrossEdges G S U).card + d.choose 2 := Nat.add_le_add_left hbound _

/-- Original full-host caller, strengthened by the derived suffix counts.
No suffix, ordering, degree/count oracle, clique, independence or equality
family is supplied. All original ambient vertices remain in univ. -/
theorem exists_last_tight_core_block_with_edge_ledger
    (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hcore : degreeCore G d = S) (hS : S.Nonempty)
    (htight : Nat.card G.edgeSet =
      S.card.choose 2 + d * (Nat.card V - S.card))
    (houtside : d ≤ Nat.card V - S.card) :
    ∃ U : Finset V, S ⊆ U ∧ U ⊆ Finset.univ ∧ (U \ S).card = d ∧
      ExactCoreDeletion G d S U ∧
      (∀ x ∈ U, x ∉ S → d ≤ withinDegree G U x) ∧
      (withinEdges G U).card = (withinEdges G S).card + d * d ∧
      (coreCrossEdges G S U).card + (withinEdges G (U \ S)).card = d * d := by
  obtain ⟨U, hSU, hUuniv, hUoutside, hcertificate, hdegree⟩ :=
    exists_last_tight_core_block_of_tight_nonempty_core G d S
      hcore hS htight houtside
  exact ⟨U, hSU, hUuniv, hUoutside, hcertificate, hdegree,
    last_block_edge_ledger hcertificate hUoutside,
    last_block_cross_edge_ledger hSU hcertificate hUoutside⟩

end ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
