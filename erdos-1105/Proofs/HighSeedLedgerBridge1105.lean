module

public import HighSeedDegreePool1105
public import ActualInducedDegree1105
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
Convert the actual remaining edge-deficit balance to
the existing degree-pool premise and select exactly d-1 seed vertices. The ambient support K, its induced graph, its original unordered edges and
its original restricted degrees are literally the SAME throughout. The remaining-deficit bound is explicit: the existing peeling output does
not itself export that stronger bound. No closure or degree oracle is used.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.HighSeedLedgerBridge1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination

/- Statement-time classical decisions supply the actual induced edge set;
   no new public decidability or finite-edge hypothesis is introduced. -/
local instance proposition_decidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The exact balance yields the nontruncated twice-edge hypothesis.
No graph or minimum-degree assumption is needed for this arithmetic step. -/
theorem twice_edges_of_deficit_balance {d h e D : ℕ}
    (hd : 1 ≤ d) (hD : D ≤ h - 3)
    (hbalance : e + D = d.choose 2 + d * h) :
    d * (d - 1) + 2 * d * h ≤ 2 * e + 2 * (h - 3) := by
  have hpred : d - 1 + 1 = d := by omega
  have hdouble : 2 * d.choose 2 = d * (d - 1) := by
    have h := Nat.add_one_mul_choose_eq (d - 1) 1
    rw [hpred, Nat.choose_one_right] at h
    simpa only [Nat.reduceAdd, Nat.mul_comm] using h.symm
  calc
    d * (d - 1) + 2 * d * h = 2 * (d.choose 2 + d * h) := by
      rw [Nat.mul_add, hdouble]
      ring
    _ = 2 * (e + D) := congrArg (fun a : ℕ => 2 * a) hbalance.symm
    _ ≤ 2 * e + 2 * (h - 3) := by
      rw [Nat.mul_add]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hD) _

/-- Extract an exact-sized subset of original high-degree vertices in the
SAME finite graph whose edge balance is supplied. -/
theorem exists_high_subset_of_deficit_balance {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d h D : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h)
    (horder : Fintype.card V = d + h)
    (hD : D ≤ h - 3)
    (hbalance : G.edgeFinset.card + D = d.choose 2 + d * h) :
    ∃ W : Finset V, W.card = d - 1 ∧
      ∀ x ∈ W, d + 1 ≤ G.degree x := by
  classical
  have hedges := twice_edges_of_deficit_balance (by omega : 1 ≤ d) hD hbalance
  have hpool :=
    ErdosProblems.AntiRamseyHighSeedDegreePool1105.high_seed_degree_pool
      G hd hh horder hedges
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hpool
  refine ⟨W, hWcard, ?_⟩
  intro x hx
  have hdegree := (Finset.mem_filter.mp (hWsub hx)).2
  calc
    d + 1 ≤ (Finset.univ.filter (fun w => G.Adj x w)).card := by
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using hdegree
    _ = G.degree x := by
      unfold SimpleGraph.degree
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]

/-- The canonical original restricted edge count equals the edge count of
the actual induced graph on every vertex of K, including any isolates. -/
theorem withinEdges_card_eq_induced {V : Type*} [Fintype V]
    (G : SimpleGraph V) (K : Finset V) :
    (withinEdges G K).card = (G.induce (K : Set V)).edgeFinset.card := by
  classical
  unfold withinEdges
  exact G.card_filter_edgeFinset_toFinset_subset K

/-- Obtain exactly d-1 ACTUAL seed vertices, with ORIGINAL degree inside K.
The ledger has the exact output shape of the actual-deficit kernel provider.
No favorable support, filled edge count or replacement graph is substituted. -/
theorem exists_actual_high_seed_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (K : Finset V) {d h D : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h) (horder : K.card = d + h)
    (hD : D ≤ h - 3)
    (hbalance : (withinEdges G K).card + D =
      d.choose 2 + d * (K.card - d)) :
    ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
      ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  have hkernelOrder : Fintype.card (K : Set V) = d + h := by
    exact (Fintype.card_of_finset' (p := (K : Set V)) K
      (fun _ => Iff.rfl)).trans horder
  have hsub : K.card - d = h := by omega
  have hkernelBalance : (G.induce (K : Set V)).edgeFinset.card + D =
      d.choose 2 + d * h := by
    rw [← withinEdges_card_eq_induced G K, ← hsub]
    exact hbalance
  obtain ⟨W, hWcard, hWdegree⟩ :=
    exists_high_subset_of_deficit_balance (G.induce (K : Set V))
      hd hh hkernelOrder hD hkernelBalance
  let f : (K : Set V) ↪ V := Function.Embedding.subtype (· ∈ (K : Set V))
  refine ⟨W.map f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hx
    exact u.property
  · simpa only [Finset.card_map] using hWcard
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    have hdegree := hWdegree u hu
    rw [ActualInducedDegree1105.degree_induce_eq_withinDegree G K u] at hdegree
    exact hdegree

/-- If D_K is literally the natural edge deficit of the actual K, the
empty-core bound supplies the nontruncation needed for the exact balance.
The same original G is used for the core, deficit and selected degrees. -/
theorem exists_actual_high_seed_subset_of_empty_core_deficit
    {V : Type*} [Fintype V] (G : SimpleGraph V) (K : Finset V)
    {d h : ℕ} (hd : 4 ≤ d) (hh : 3 ≤ h)
    (hcore : ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore G d = ∅)
    (horder : K.card = d + h)
    (hdeficit : (d.choose 2 + d * (K.card - d)) -
      (withinEdges G K).card ≤ h - 3) :
    ∃ W : Finset V, W ⊆ K ∧ W.card = d - 1 ∧
      ∀ x ∈ W, d + 1 ≤ withinDegree G K x := by
  classical
  have hC : ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore G d ⊆ K := by
    rw [hcore]
    exact Finset.empty_subset K
  have hM : max d
      (ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore G d).card ≤
      K.card := by
    rw [hcore, Finset.card_empty, max_eq_left (Nat.zero_le d)]
    omega
  have hcap : (withinEdges G K).card ≤
      d.choose 2 + d * (K.card - d) := by
    simpa only [hcore, Finset.card_empty, max_eq_left (Nat.zero_le d)] using
      (core_induced_edge_bound G d K hC hM)
  have hbalance : (withinEdges G K).card +
      ((d.choose 2 + d * (K.card - d)) - (withinEdges G K).card) =
      d.choose 2 + d * (K.card - d) := Nat.add_sub_of_le hcap
  exact exists_actual_high_seed_subset G K hd hh horder hdeficit hbalance

end ErdosProblems.PathUpperReduction.HighSeedLedgerBridge1105

