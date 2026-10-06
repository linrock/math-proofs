module

public import CoreElimination
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Exact original seed/residual edge counting for
h=3. All counts use SAME original G and CoreElimination.withinEdges/withinDegree. W is arbitrary with W⊆K and the actual specified cardinality: no clique,
universal cross edges, cover, star, forest or supplied degree/count oracle. The general removal bound applies the existing exact unordered-edge erase
ledger; it does not re-prove an edge bijection or double-count removed edges. This is auxiliary counting/minimum-degree progress, not full #1105(ii).
-/

noncomputable section
namespace ErdosProblems.PathUpperReduction.H3ResidualCount1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

omit [Fintype V] in
theorem withinDegree_le_card_sub_one (G : SimpleGraph V)
    (K : Finset V) (x : V) (hx : x ∈ K) :
    withinDegree G K x ≤ K.card - 1 := by
  classical
  have hsub : K.filter (fun z => G.Adj x z) ⊆ K.erase x := by
    intro z hz
    obtain ⟨hzK, hxz⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_erase.mpr ⟨?_, hzK⟩
    exact hxz.ne.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hx] at hcard
  exact hcard

/-- Erasing the ACTUAL arbitrary W counts each removed ORIGINAL edge once.
The residual edges remain untouched; all W-internal and W-to-residual edges
are bounded by the complete capacities without assuming they are present. -/
theorem original_seed_edge_partition_upper (G : SimpleGraph V)
    (K W : Finset V) (hWK : W ⊆ K) :
    (withinEdges G K).card ≤ W.card.choose 2 +
      W.card * (K \ W).card + (withinEdges G (K \ W)).card := by
  classical
  revert K
  induction W using Finset.induction_on with
  | empty =>
      intro K _hWK
      simp
  | @insert x W hx ih =>
      intro K hWK
      have hxK : x ∈ K := hWK (Finset.mem_insert_self x W)
      have hWErase : W ⊆ K.erase x := by
        intro z hzW
        refine Finset.mem_erase.mpr ⟨?_, hWK (Finset.mem_insert_of_mem hzW)⟩
        intro hzx
        exact hx (hzx ▸ hzW)
      have hresidual : K.erase x \ W = K \ insert x W := by
        rw [Finset.erase_sdiff_comm, Finset.sdiff_insert]
      have hprevious := ih (K.erase x) hWErase
      rw [hresidual] at hprevious
      have hnewcard : (insert x W).card = W.card + 1 :=
        Finset.card_insert_of_notMem hx
      have hcardledger := Finset.card_sdiff_add_card_eq_card hWK
      have hdegree := withinDegree_le_card_sub_one G K x hxK
      have hdegreeCapacity : withinDegree G K x ≤
          (K \ insert x W).card + W.card := by
        omega
      have hchoose : (W.card + 1).choose 2 = W.card + W.card.choose 2 := by
        simpa only [Nat.choose_one_right] using (Nat.choose_succ_succ' W.card 1)
      calc
        (withinEdges G K).card =
            (withinEdges G (K.erase x)).card + withinDegree G K x :=
          withinEdges_erase_ledger G K x hxK
        _ ≤ (W.card.choose 2 + W.card * (K \ insert x W).card +
            (withinEdges G (K \ insert x W)).card) +
            ((K \ insert x W).card + W.card) :=
          Nat.add_le_add hprevious hdegreeCapacity
        _ = (W.card + 1).choose 2 + (W.card + 1) * (K \ insert x W).card +
            (withinEdges G (K \ insert x W)).card := by
          rw [hchoose, Nat.add_mul, Nat.one_mul]
          omega
        _ = (insert x W).card.choose 2 +
            (insert x W).card * (K \ insert x W).card +
            (withinEdges G (K \ insert x W)).card := by rw [hnewcard]

/-- In the literal h3 cardinalities, the ACTUAL residual has four vertices
and its original edges are the only unbounded term in the seed partition. -/
theorem h3_original_seed_edge_partition_upper (G : SimpleGraph V)
    (d : ℕ) (K W : Finset V) (hd : 4 ≤ d)
    (hKcard : K.card = d + 3) (hWcard : W.card = d - 1) (hWK : W ⊆ K) :
    (K \ W).card = 4 ∧
      (withinEdges G K).card ≤ (d - 1).choose 2 +
        4 * (d - 1) + (withinEdges G (K \ W)).card := by
  have hcardledger := Finset.card_sdiff_add_card_eq_card hWK
  have hRcard : (K \ W).card = 4 := by omega
  refine ⟨hRcard, ?_⟩
  have hbound := original_seed_edge_partition_upper G K W hWK
  simpa only [hWcard, hRcard, Nat.mul_comm] using hbound

/-- EXACT zero-deficit Q_d(d+3) forces at least three ORIGINAL residual
edges; the two-disjoint-K2 control has at most Q-1 seed edges. -/
theorem h3_residual_edges_ge_three_of_exact_seed_count (G : SimpleGraph V)
    (d : ℕ) (K W : Finset V) (hd : 4 ≤ d)
    (hKcard : K.card = d + 3) (hWcard : W.card = d - 1) (hWK : W ⊆ K)
    (hQ : (withinEdges G K).card = d.choose 2 + 3 * d) :
    (K \ W).card = 4 ∧ 3 ≤ (withinEdges G (K \ W)).card := by
  obtain ⟨hRcard, hbound⟩ :=
    h3_original_seed_edge_partition_upper G d K W hd hKcard hWcard hWK
  have hpred : d - 1 + 1 = d := by omega
  have hchoose : d.choose 2 = (d - 1) + (d - 1).choose 2 := by
    simpa only [hpred, Nat.choose_one_right] using (Nat.choose_succ_succ' (d - 1) 1)
  have hcapacity : d.choose 2 + 3 * d =
      (d - 1).choose 2 + 4 * (d - 1) + 3 := by
    rw [hchoose]
    omega
  rw [hQ, hcapacity] at hbound
  exact ⟨hRcard, by omega⟩

omit [Fintype V] in
/-- Original K-minimum degree≥d and at most d-1 removed vertices give
residual minimum degree≥1. No edge count or residual connectivity is assumed. -/
theorem h3_residual_min_degree_of_original_seed_degree (G : SimpleGraph V)
    (d : ℕ) (K W : Finset V) (hd : 4 ≤ d) (hWcard : W.card = d - 1)
    (hseed : ∀ x ∈ K, d ≤ withinDegree G K x) :
    ∀ x ∈ K \ W, 1 ≤ withinDegree G (K \ W) x := by
  classical
  intro x hxR
  have hxK : x ∈ K := (Finset.mem_sdiff.mp hxR).1
  have hsub : K.filter (fun z => G.Adj x z) ⊆
      ((K \ W).filter (fun z => G.Adj x z)) ∪ W := by
    intro z hz
    obtain ⟨hzK, hxz⟩ := Finset.mem_filter.mp hz
    by_cases hzW : z ∈ W
    · exact Finset.mem_union.mpr (Or.inr hzW)
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hzK, hzW⟩, hxz⟩))
  have hdegreeLoss : withinDegree G K x ≤ withinDegree G (K \ W) x + W.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hdegree := hseed x hxK
  omega

end ErdosProblems.PathUpperReduction.H3ResidualCount1105

