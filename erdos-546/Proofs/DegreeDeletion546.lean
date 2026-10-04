module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic


@[expose] public section

/-!
# Degree deletion for Sudakov's sparse graph Ramsey bound

This file proves only the degree deletion ingredient, not the Ramsey bound.
The threshold selection argument is expressed first for natural-valued weights.
All copies used by the eventual Ramsey proof must preserve edges, without an
induced-copy requirement; this ingredient concerns induced vertex deletion.
-/

namespace Erdos546

open Finset

variable {V : Type*} [Fintype V]

/-- Fewer than `r` weights exceed the total weight divided by positive `r`.
The cross-multiplied statement avoids division and rounding conventions. -/
theorem card_weight_threshold_lt (d : V → ℕ) {r : ℕ} (hr : 0 < r) :
    (univ.filter fun v => (∑ w, d w) < r * d v).card < r := by
  classical
  let b := univ.filter fun v => (∑ w, d w) < r * d v
  by_contra h
  have hcard : r ≤ b.card := Nat.le_of_not_gt h
  have hne : b.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hr hcard)
  have hstrict : b.card * (∑ w, d w) < r * ∑ v ∈ b, d v := by
    have hsum := Finset.sum_lt_sum_of_nonempty hne
      (fun v hv => (Finset.mem_filter.mp hv).2)
    simpa [Finset.sum_const, Finset.mul_sum] using hsum
  have hsum : ∑ v ∈ b, d v ≤ ∑ v, d v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ b)
  have hmul := Nat.mul_le_mul_left r hsum
  have hcardmul := Nat.mul_le_mul_right (∑ v, d v) hcard
  omega

/-- Delete exactly `k` vertices so every remaining weight times `k + 1` is
at most the total weight. Unlike division statements this also covers `k = 0`. -/
theorem exists_delete_card_weight_bound (d : V → ℕ) {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    ∃ deleted : Finset V, deleted.card = k ∧
      ∀ v ∉ deleted, (k + 1) * d v ≤ ∑ w, d w := by
  classical
  let b := univ.filter fun v => (∑ w, d w) < (k + 1) * d v
  have hb : b.card ≤ k := Nat.le_of_lt_succ
    (card_weight_threshold_lt d (Nat.succ_pos k))
  obtain ⟨deleted, hsub, hcard⟩ := Finset.exists_superset_card_eq hb hk
  refine ⟨deleted, hcard, fun v hv => ?_⟩
  by_contra hbound
  have hvb : v ∈ b := Finset.mem_filter.mpr ⟨Finset.mem_univ v,
    Nat.lt_of_not_ge hbound⟩
  exact hv (hsub hvb)

/-- A finite graph with no isolated vertices has at most twice as many
vertices as edges. The empty graph is allowed. -/
theorem card_vertices_le_twice_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnoisolated : ∀ v, ¬ G.IsIsolated v) :
    Fintype.card V ≤ 2 * G.edgeFinset.card := by
  classical
  calc
    Fintype.card V = ∑ _v : V, 1 := by simp
    _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ =>
      Nat.succ_le_of_lt ((G.degree_pos v).mpr (hnoisolated v))
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- Deleting `k` vertices leaves every original degree at most `2m/(k+1)`;
this is at least as strong as the usual highest-degree deletion estimate. -/
theorem exists_delete_card_degree_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : k ≤ Fintype.card V) :
    ∃ deleted : Finset V, deleted.card = k ∧
      ∀ v ∉ deleted, (k + 1) * G.degree v ≤ 2 * G.edgeFinset.card := by
  simpa [G.sum_degrees_eq_twice_card_edges] using
    exists_delete_card_weight_bound (fun v => G.degree v) hk

/-- Inducing on a vertex set cannot increase a vertex's degree. -/
theorem degree_induce_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] (v : s) :
    (G.induce s).degree v ≤ G.degree v := by
  classical
  have hmap := congrArg Finset.card (G.map_neighborFinset_induce (s := s) v)
  calc
    (G.induce s).degree v = (G.neighborFinset v ∩ s.toFinset).card := by
      simpa only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] using hmap
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card Finset.inter_subset_left
    _ = G.degree v := G.card_neighborFinset_eq_degree v

/-- The degree deletion ingredient used in Sudakov's Lemma 3.1:
delete exactly `k` vertices, and every vertex in the remaining induced graph
has its degree times `k + 1` bounded by twice the original edge count. -/
theorem exists_delete_card_induced_degree_bound [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    ∃ deleted : Finset V, deleted.card = k ∧
      ∀ v : ↥((deleted : Set V)ᶜ),
        (k + 1) * (G.induce ((deleted : Set V)ᶜ)).degree v ≤
          2 * G.edgeFinset.card := by
  obtain ⟨deleted, hcard, hdegree⟩ := exists_delete_card_degree_bound G hk
  refine ⟨deleted, hcard, fun v => ?_⟩
  calc
    (k + 1) * (G.induce ((deleted : Set V)ᶜ)).degree v ≤
        (k + 1) * G.degree v := Nat.mul_le_mul_left _ (degree_induce_le G _ v)
    _ ≤ 2 * G.edgeFinset.card := hdegree v v.property

end Erdos546

#print axioms Erdos546.card_weight_threshold_lt
#print axioms Erdos546.exists_delete_card_weight_bound
#print axioms Erdos546.card_vertices_le_twice_edges
#print axioms Erdos546.exists_delete_card_degree_bound
#print axioms Erdos546.degree_induce_le
#print axioms Erdos546.exists_delete_card_induced_degree_bound
