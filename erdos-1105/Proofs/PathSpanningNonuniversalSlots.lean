module

public import PathUpperSpanningDegreeSlots
public import Batteries.Tactic.OpenPrivate

@[expose] public section

/-! output refinement of the verified slot construction. -/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

theorem spanning_degree_slots_with_nonuniversal_cap
    (k : ℕ) (hk : 3 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected) (hneTop : H ≠ ⊤)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2) :
    ∃ (a : ℕ) (L : Finset (Fin k)),
      1 ≤ a ∧ 2 * a ≤ k - 2 ∧ L.card = a + 1 ∧
      (∀ x ∈ L, H.degree x ≤ a) ∧
      H.edgeFinset.card ≤ (k - 1 - a).choose 2 + a * (a + 1) ∧
      (∀ x : Fin k, ¬ H.IsUniversal x → H.degree x ≤ k - 2 - a) := by
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
  refine ⟨a, L, haPos, htwo, hLcard, hLdegree, hbound, ?_⟩
  intro x hx
  have hxN : x ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
  have hxLe : H.degree x ≤ H.degree v := hmaxv x hxN
  omega

end ErdosProblems.PathUpperReduction
