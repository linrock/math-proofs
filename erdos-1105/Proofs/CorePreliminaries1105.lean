module

public import CountCoreBasis
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
The core is the actual union-defined CountCoreBasis core. Its lower bound
requires nonemptiness; no nonemptiness, clique, saturation or cycle-freedom
conclusion is assumed or inferred. The deletion lemmas use only the same
actual graph and the stated lower bound on its actual vertex cardinality.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis

namespace ErdosProblems.PathUpperReduction.CorePreliminaries1105

variable {V : Type*} [Fintype V]

theorem nonempty_degree_core_card_ge_add_two (G : SimpleGraph V) (d : ℕ)
    (hC : (degreeCore G d).Nonempty) :
    d + 2 ≤ (degreeCore G d).card := by
  classical
  obtain ⟨x, hx⟩ := hC
  have hgood : d < ((degreeCore G d).filter (fun z => G.Adj x z)).card :=
    degree_core_good G d x hx
  have hstrict : (degreeCore G d).filter (fun z => G.Adj x z) ⊂ degreeCore G d :=
    Finset.filter_ssubset.mpr ⟨x, hx, G.irrefl⟩
  have hcard : ((degreeCore G d).filter (fun z => G.Adj x z)).card <
      (degreeCore G d).card := Finset.card_lt_card hstrict
  have hstep : d + 1 < (degreeCore G d).card :=
    lt_of_le_of_lt (Nat.succ_le_of_lt hgood) hcard
  exact Nat.succ_le_of_lt hstep

theorem exists_vertex_ne_pair (hN : 3 ≤ Fintype.card V) (x z : V) :
    ∃ w : V, w ≠ x ∧ w ≠ z := by
  classical
  have huniv : 2 < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    exact lt_of_lt_of_le (by decide : 2 < 3) hN
  have hpair : ({x, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hsmall : ({x, z} : Finset V).card < (Finset.univ : Finset V).card :=
    lt_of_le_of_lt hpair huniv
  obtain ⟨w, _hw, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
  exact ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩

theorem exists_adj_avoiding_deleted_vertex (G : SimpleGraph V)
    (hN : 3 ≤ Fintype.card V)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (x z : V) (hxz : x ≠ z) :
    ∃ y : V, G.Adj x y ∧ y ≠ z := by
  classical
  obtain ⟨w, hwx, hwz⟩ := exists_vertex_ne_pair hN x z
  let x' : {v : V | v ≠ z} := ⟨x, hxz⟩
  let w' : {v : V | v ≠ z} := ⟨w, hwz⟩
  have hne : x' ≠ w' := by
    intro h
    exact hwx (congrArg (fun q : {v : V | v ≠ z} => q.val) h).symm
  have hreach : (G.induce {v | v ≠ z}).Reachable x' w' := (hdel z) x' w'
  obtain ⟨y, hy⟩ := SimpleGraph.Reachable.nonempty_neighborSet_left hne hreach
  exact ⟨y.val, SimpleGraph.induce_adj.mp hy, y.property⟩

theorem two_distinct_neighbors_of_deletion_connected (G : SimpleGraph V)
    (hN : 3 ≤ Fintype.card V)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) (x : V) :
    ∃ a b : V, a ≠ b ∧ G.Adj x a ∧ G.Adj x b := by
  obtain ⟨z, hzx, _hzx⟩ := exists_vertex_ne_pair hN x x
  obtain ⟨a, hxa, _haz⟩ := exists_adj_avoiding_deleted_vertex G hN hdel x z hzx.symm
  obtain ⟨b, hxb, hba⟩ := exists_adj_avoiding_deleted_vertex G hN hdel x a hxa.ne
  exact ⟨a, b, hba.symm, hxa, hxb⟩

theorem ambient_neighbor_filter_card_ge_two (G : SimpleGraph V)
    (hN : 3 ≤ Fintype.card V)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) (x : V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    2 ≤ ((Finset.univ : Finset V).filter (fun z => G.Adj x z)).card := by
  classical
  obtain ⟨a, b, hab, hxa, hxb⟩ := two_distinct_neighbors_of_deletion_connected G hN hdel x
  have ha : a ∈ (Finset.univ : Finset V).filter (fun z => G.Adj x z) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ a, hxa⟩
  have hb : b ∈ (Finset.univ : Finset V).filter (fun z => G.Adj x z) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ b, hxb⟩
  have hcard : 1 < ((Finset.univ : Finset V).filter (fun z => G.Adj x z)).card :=
    Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  exact Nat.succ_le_of_lt hcard

end ErdosProblems.PathUpperReduction.CorePreliminaries1105
