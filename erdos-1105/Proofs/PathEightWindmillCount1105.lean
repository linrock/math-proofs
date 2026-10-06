module

public import PathEightDeletedComponentThree1105
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! The hypotheses describe the SAME actual graph and actual deletion components. No windmill family, clique, degree sequence or edge count is supplied. -/

namespace ErdosProblems.PathUpperReduction.PathEightWindmillCount1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.PathEightDeletedComponentThree1105
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nonroot_degree_three_and_root_adj
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hfree : (pathGraph 8).Free G) (c : V)
    (D0 E0 : (G.induce {v : V | v ≠ c}).ConnectedComponent) (hD0E0 : D0 ≠ E0)
    (v : V) (hv : v ≠ c) : G.degree v = 3 ∧ G.Adj c v := by
  classical
  let x : {w : V // w ≠ c} := ⟨v, hv⟩
  let D := (G.induce {w : V | w ≠ c}).connectedComponentMk x
  obtain ⟨E, hDE⟩ : ∃ E : (G.induce {w : V | w ≠ c}).ConnectedComponent, D ≠ E := by
    by_cases hDD0 : D = D0
    · exact ⟨E0, fun hDE => hD0E0 (hDD0.symm.trans hDE)⟩
    · exact ⟨D0, hDD0⟩
  have hDcard := deleted_component_card_eq_three_of_distinct_component
    G hconn hmin hfree c D E hDE
  let S : Finset V := D.supp.toFinset.image (fun u : {w : V // w ≠ c} => u.val)
  have hScard : S.card = 3 := by
    calc
      S.card = D.supp.toFinset.card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      _ = Nat.card {u : {w : V // w ≠ c} // u ∈ D.supp} :=
        (Nat.card_eq_card_toFinset D.supp).symm
      _ = 3 := hDcard
  have hSmem : ∀ w : V, w ∈ S ↔ w ∈ deletedComponentVertices G c D := by
    intro w
    simp [S, deletedComponentVertices]
  have hvD : v ∈ deletedComponentVertices G c D := by
    refine ⟨x, ?_, rfl⟩
    change (G.induce {w : V | w ≠ c}).connectedComponentMk x = D
    rfl
  have hvS : v ∈ S := (hSmem v).mpr hvD
  have hcS : c ∉ S := by
    intro hc
    exact deletedComponentVertices_ne G c D ((hSmem c).mp hc) rfl
  have hcErase : c ∉ S.erase v := by
    intro hc
    exact hcS (Finset.mem_erase.mp hc).2
  have hEraseCard : (S.erase v).card + 1 = 3 := by
    simpa only [hScard] using Finset.card_erase_add_one hvS
  let T : Finset V := insert c (S.erase v)
  have hTcard : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hcErase]
    exact hEraseCard
  have hNsub : G.neighborFinset v ⊆ T := by
    intro w hw
    have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    by_cases hwc : w = c
    · subst w
      simp [T]
    · have hwD := deletedComponentVertices_adj_closed G c D hvD hvw hwc
      have hwS : w ∈ S := (hSmem w).mpr hwD
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvw.ne.symm, hwS⟩)
  have hNmin : 3 ≤ (G.neighborFinset v).card := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hmin v
  have hNback : T.card ≤ (G.neighborFinset v).card := by
    rw [hTcard]
    exact hNmin
  have hNeq := Finset.eq_of_subset_of_card_le hNsub hNback
  have hdegree : G.degree v = 3 := by
    rw [← G.card_neighborFinset_eq_degree v, hNeq]
    exact hTcard
  have hvc : G.Adj v c := (G.mem_neighborFinset v c).mp (by rw [hNeq]; simp [T])
  exact ⟨hdegree, hvc.symm⟩

/-- The actual edge count in the vertex-cut branch. -/
theorem windmill_edge_count_of_distinct_deleted_components
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hfree : (pathGraph 8).Free G) (c : V)
    (D E : (G.induce {v : V | v ≠ c}).ConnectedComponent) (hDE : D ≠ E) :
    G.edgeFinset.card = 2 * Fintype.card V - 2 := by
  classical
  have hnonroot : ∀ v : V, v ≠ c → G.degree v = 3 ∧ G.Adj c v := by
    intro v hv
    exact nonroot_degree_three_and_root_adj G hconn hmin hfree c D E hDE v hv
  have huniversal : G.IsUniversal c := by
    intro v hcv
    exact (hnonroot v hcv.symm).2
  have hcDegree : G.degree c = Fintype.card V - 1 :=
    (G.degree_eq_card_sub_one c).mpr huniversal
  let rest : Finset V := Finset.univ.erase c
  have hRestCard : rest.card + 1 = Fintype.card V := by
    simpa only [rest, Finset.card_univ] using
      Finset.card_erase_add_one (s := (Finset.univ : Finset V)) (a := c) (by simp)
  have hRestSum : (∑ v ∈ rest, G.degree v) = rest.card * 3 := by
    apply Finset.sum_const_nat
    intro v hv
    exact (hnonroot v (Finset.mem_erase.mp hv).1).1
  have hSplit : G.degree c + (∑ v ∈ rest, G.degree v) = 2 * G.edgeFinset.card := by
    calc
      G.degree c + (∑ v ∈ rest, G.degree v) = ∑ v : V, G.degree v := by
        simpa only [rest] using
          Finset.add_sum_erase (Finset.univ : Finset V) (fun v => G.degree v)
            (by simp : c ∈ (Finset.univ : Finset V))
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  omega

end ErdosProblems.PathUpperReduction.PathEightWindmillCount1105
