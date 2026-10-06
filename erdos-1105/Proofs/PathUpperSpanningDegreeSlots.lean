module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

/-! No saturation, cone, original coloring or numerical anti-Ramsey conclusion. -/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

theorem edge_count_le_complement_clique_and_slots
    {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (L : Finset (Fin k)) (a : ℕ) (hL : ∀ x ∈ L, H.degree x ≤ a) :
    H.edgeFinset.card ≤ (k - L.card).choose 2 + L.card * a := by
  classical
  let C : Finset (Fin k) := Lᶜ
  let inside := H.edgeFinset.filter (fun e => e.toFinset ⊆ C)
  let touching := L.biUnion (fun v => H.incidenceFinset v)
  have hcover : H.edgeFinset ⊆ inside ∪ touching := by
    intro e he
    by_cases hinside : e.toFinset ⊆ C
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hinside⟩))
    · have hex : ∃ x, x ∈ e.toFinset ∧ x ∈ L := by
        by_contra hnone
        apply hinside
        intro x hx
        apply Finset.mem_compl.mpr
        intro hxL
        exact hnone ⟨x, hx, hxL⟩
      obtain ⟨x, hx, hxL⟩ := hex
      apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_biUnion.mpr
      refine ⟨x, hxL, ?_⟩
      rw [H.incidenceFinset_eq_filter x]
      exact Finset.mem_filter.mpr ⟨he, Sym2.mem_toFinset.mp hx⟩
  have hinsideCount : inside.card ≤ C.card.choose 2 := by
    change (H.edgeFinset.filter (fun e => e.toFinset ⊆ C)).card ≤ C.card.choose 2
    rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := H) C]
    have hCfin : Fintype.card {v : Fin k // v ∈ (↑C : Set (Fin k))} = C.card :=
      Fintype.card_of_subtype C (by intro v; rfl)
    simpa only [hCfin] using
      (SimpleGraph.card_edgeFinset_le_card_choose_two
        (G := H.induce (↑C : Set (Fin k))))
  have htouchingCount : touching.card ≤ L.card * a := by
    apply Finset.card_biUnion_le_card_mul L (fun v => H.incidenceFinset v) a
    intro x hx
    simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hL x hx
  have hCcard : C.card = k - L.card := by
    simpa only [Fintype.card_fin] using Finset.card_compl L
  calc
    H.edgeFinset.card ≤ (inside ∪ touching).card := Finset.card_le_card hcover
    _ ≤ inside.card + touching.card := Finset.card_union_le inside touching
    _ ≤ C.card.choose 2 + L.card * a := Nat.add_le_add hinsideCount htouchingCount
    _ = (k - L.card).choose 2 + L.card * a := by rw [hCcard]

/-- A connected noncomplete spanning graph with the missing-pair degree
closure has an actual low-degree set and the corresponding edge-count cap. -/
theorem spanning_degree_slots_and_edge_count
    (k : ℕ) (hk : 3 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected) (hneTop : H ≠ ⊤)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2) :
    ∃ (a : ℕ) (L : Finset (Fin k)),
      1 ≤ a ∧ 2 * a ≤ k - 2 ∧ L.card = a + 1 ∧
      (∀ x ∈ L, H.degree x ≤ a) ∧
      H.edgeFinset.card ≤ (k - 1 - a).choose 2 + a * (a + 1) := by
  classical
  let N : Finset (Fin k) := Finset.univ.filter (fun v => ¬ H.IsUniversal v)
  have hN : N.Nonempty := by
    by_contra hnone
    apply hneTop
    apply SimpleGraph.eq_top_iff_forall_isUniversal.mpr
    intro x
    by_contra hx
    apply hnone
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨v, hvN, hmaxv⟩ := Finset.exists_max_image N (fun v => H.degree v) hN
  have hvNU : ¬ H.IsUniversal v := (Finset.mem_filter.mp hvN).2
  let T := Hᶜ.neighborFinset v
  have hTcard : T.card = k - 1 - H.degree v := by
    change (Hᶜ.neighborFinset v).card = k - 1 - H.degree v
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree_compl,
      Fintype.card_fin]
  have hbLt : H.degree v < k - 1 := by
    simpa only [Fintype.card_fin] using
      (SimpleGraph.degree_lt_card_sub_one (G := H) v).mpr hvNU
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, huT, hmaxu⟩ := Finset.exists_max_image T (fun v => H.degree v) hT
  have hcompl : Hᶜ.Adj v u :=
    (SimpleGraph.mem_neighborFinset (G := Hᶜ) (v := v) u).mp huT
  obtain ⟨hvu, hmissing⟩ := (SimpleGraph.compl_adj H v u).mp hcompl
  have huNU : ¬ H.IsUniversal u := by
    intro hu
    exact hmissing (hu hvu.symm).symm
  have huN : u ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huNU⟩
  let a := H.degree u
  have haLeB : a ≤ H.degree v := hmaxv u huN
  have hsum : a + H.degree v ≤ k - 2 := by
    have := hclosure v u hvu hmissing
    dsimp only [a]
    omega
  have haPos : 1 ≤ a := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hvu.symm (hconn u v)
    exact hpos
  have htwo : 2 * a ≤ k - 2 := by omega
  have hk2 : 2 ≤ k := by omega
  have hsumAmbient : a + H.degree v + 2 ≤ k := by
    have h := Nat.add_le_add_right hsum 2
    rw [Nat.sub_add_cancel hk2] at h
    exact h
  have hsize : a + 1 ≤ T.card := by omega
  obtain ⟨L, hLT, hLcard⟩ := Finset.exists_subset_card_eq hsize
  have hLdegree : ∀ x ∈ L, H.degree x ≤ a := by
    intro x hx
    exact hmaxu x (hLT hx)
  have hcount := edge_count_le_complement_clique_and_slots H L a hLdegree
  have hshift : k - (a + 1) = k - 1 - a := by omega
  have hbound : H.edgeFinset.card ≤ (k - 1 - a).choose 2 + a * (a + 1) := by
    simpa only [hLcard, hshift, Nat.mul_comm] using hcount
  exact ⟨a, L, haPos, htwo, hLcard, hLdegree, hbound⟩

end ErdosProblems.PathUpperReduction
