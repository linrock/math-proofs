module

public import PathUpperConnectedSpanningLowSlot
public import Batteries.Tactic.OpenPrivate

@[expose] public section

/-!
factor of the checked a=1 equality/shape argument. The ACTUAL supplied
two-vertex low slot and original threshold remain explicit. No path, color,
representative or numerical anti-Ramsey theorem is asserted.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- An actual two-vertex slot of degree at most1 at the original edge threshold
forces a complete remainder and two degree1 leaves at one actual hub. -/
theorem a_one_slots_force_s1
    (k : ℕ) (hk : 5 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2)
    (L : Finset (Fin k)) (hLcardTwo : L.card = 2)
    (hLdeg : ∀ x ∈ L, H.degree x ≤ 1)
    (hedges : (k - 2).choose 2 + 2 ≤ H.edgeFinset.card) :
    ∃ w : Fin k,
      w ∉ L ∧ (∀ x ∈ L, H.degree x = 1) ∧
      H.edgeFinset.card = (k - 2).choose 2 + 2 ∧
      H.induce (↑(Lᶜ) : Set (Fin k)) = ⊤ ∧
      (∀ x ∈ L, ∀ y ∈ L, ¬ H.Adj x y) ∧
      (∀ u v, H.Adj u v ↔ u ≠ v ∧
        ((u ∉ L ∧ v ∉ L) ∨ (u ∈ L ∧ v = w) ∨ (v ∈ L ∧ u = w))) := by
  classical
  obtain ⟨x0, y0, hxy, hLpair⟩ := Finset.card_eq_two.mp hLcardTwo
  have hx0 : x0 ∈ L := by rw [hLpair]; simp
  have hy0 : y0 ∈ L := by rw [hLpair]; simp
  have hxDegree : H.degree x0 = 1 := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hxy (hconn x0 y0)
    have hle := hLdeg x0 hx0
    omega
  have hyDegree : H.degree y0 = 1 := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hxy.symm (hconn y0 x0)
    have hle := hLdeg y0 hy0
    omega
  have hLdegree : ∀ x ∈ L, H.degree x = 1 := by
    intro x hx
    have hmem : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    rcases hmem with rfl | rfl
    · exact hxDegree
    · exact hyDegree
  let C : Finset (Fin k) := Lᶜ
  let K := H.induce (↑C : Set (Fin k))
  have hCcard : C.card = k - 2 := by
    simpa only [Fintype.card_fin, hLcardTwo] using Finset.card_compl L
  have hcoreCover : H.edgeFinset.card ≤ K.edgeFinset.card + 2 := by
    simpa only [hLcardTwo, Nat.mul_one] using
      edge_count_le_induced_complement_and_slots H L 1 hLdeg
  have hcoreCount : (k - 2).choose 2 ≤ K.edgeFinset.card := by omega
  have htopCount : (⊤ : SimpleGraph {v : Fin k // v ∈ C}).edgeFinset.card = (k - 2).choose 2 := by
    simpa only [Fintype.card_coe, hCcard] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := {v : Fin k // v ∈ C}))
  have hcoreEdges : K.edgeFinset = (⊤ : SimpleGraph {v : Fin k // v ∈ C}).edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
      (by rw [htopCount]; exact hcoreCount)
  have hcoreTop : H.induce (↑(Lᶜ) : Set (Fin k)) = ⊤ :=
    SimpleGraph.edgeFinset_inj.mp hcoreEdges
  have hKcount : K.edgeFinset.card = (k - 2).choose 2 :=
    (congrArg Finset.card hcoreEdges).trans htopCount
  have hcountExact : H.edgeFinset.card = (k - 2).choose 2 + 2 := by omega
  have hleavesNotAdj : ¬ H.Adj x0 y0 := by
    intro hadj
    obtain ⟨nx, _hnx, hnxUnique⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hxDegree
    obtain ⟨ny, _hny, hnyUnique⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hyDegree
    have hclosed : ∀ u ∈ L, ∀ v, H.Adj u v → v ∈ L := by
      intro u hu v huv
      have hmem : u = x0 ∨ u = y0 := by simpa [hLpair] using hu
      rcases hmem with rfl | rfl
      · have hv : v = y0 := (hnxUnique v huv).trans (hnxUnique y0 hadj).symm
        exact hv.symm ▸ hy0
      · have hv : v = x0 := (hnyUnique v huv).trans (hnyUnique x0 hadj.symm).symm
        exact hv.symm ▸ hx0
    have hstay : ∀ {u v : Fin k}, H.Walk u v → u ∈ L → v ∈ L := by
      intro u v p
      induction p with
      | nil => exact fun hu => hu
      | cons huv _ ih => exact fun hu => ih (hclosed _ hu _ huv)
    have hLuniv : L = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr (fun v => hstay (hconn x0 v).some hx0)
    have hcard : L.card = k := by rw [hLuniv, Finset.card_univ, Fintype.card_fin]
    omega
  have hLindependent : ∀ x ∈ L, ∀ y ∈ L, ¬ H.Adj x y := by
    intro x hx y hy
    have hxm : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    have hym : y = x0 ∨ y = y0 := by simpa [hLpair] using hy
    rcases hxm with rfl | rfl <;> rcases hym with rfl | rfl
    · exact H.loopless.irrefl _
    · exact hleavesNotAdj
    · exact fun hadj => hleavesNotAdj hadj.symm
    · exact H.loopless.irrefl _
  have hcoreAdj : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → H.Adj u v := by
    intro u hu v hv huv
    have hsubNe : (⟨u, hu⟩ : {v : Fin k // v ∈ C}) ≠ ⟨v, hv⟩ := by
      intro heq
      exact huv (congrArg Subtype.val heq)
    have htop : K = ⊤ := hcoreTop
    have hadj : K.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
      rw [htop]
      exact (SimpleGraph.top_adj _ _).mpr hsubNe
    exact hadj
  obtain ⟨p, hxp, hpUnique⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hxDegree
  obtain ⟨q, hyq, hqUnique⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hyDegree
  have hpNotL : p ∉ L := by
    intro hpL
    exact hLindependent x0 hx0 p hpL hxp
  have hqNotL : q ∉ L := by
    intro hqL
    exact hLindependent y0 hy0 q hqL hyq
  have hqC : q ∈ C := Finset.mem_compl.mpr hqNotL
  have hsameHub : p = q := by
    by_contra hpq
    have hxq : x0 ≠ q := by
      intro heq
      exact hqNotL (heq ▸ hx0)
    have hmissing : ¬ H.Adj x0 q := by
      intro hadj
      exact hpq (hpUnique q hadj).symm
    have hyNotErase : y0 ∉ C.erase q := by
      intro hy
      exact (Finset.mem_compl.mp (Finset.mem_erase.mp hy).2) hy0
    let N := insert y0 (C.erase q)
    have hNcard : N.card = k - 2 := by
      change (insert y0 (C.erase q)).card = k - 2
      rw [Finset.card_insert_of_notMem hyNotErase, Finset.card_erase_of_mem hqC,
        hCcard]
      omega
    have hNsubset : N ⊆ H.neighborFinset q := by
      intro v hv
      rw [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hyq.symm
      · exact hcoreAdj q hqC v (Finset.mem_erase.mp hv).2
          (Finset.mem_erase.mp hv).1.symm
    have hqLower : k - 2 ≤ H.degree q := by
      calc
        k - 2 = N.card := hNcard.symm
        _ ≤ (H.neighborFinset q).card := Finset.card_le_card hNsubset
        _ = H.degree q := SimpleGraph.card_neighborFinset_eq_degree H q
    have hclosedPair := hclosure x0 q hxq hmissing
    omega
  have hleafAdj : ∀ x ∈ L, ∀ v, H.Adj x v ↔ v = p := by
    intro x hx v
    have hmem : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    rcases hmem with rfl | rfl
    · constructor
      · exact hpUnique v
      · intro hv
        exact hv.symm ▸ hxp
    · constructor
      · intro hadj
        exact (hqUnique v hadj).trans hsameHub.symm
      · intro hv
        have hyp := hsameHub.symm ▸ hyq
        exact hv.symm ▸ hyp
  have hshape : ∀ u v, H.Adj u v ↔ u ≠ v ∧
      ((u ∉ L ∧ v ∉ L) ∨ (u ∈ L ∧ v = p) ∨ (v ∈ L ∧ u = p)) := by
    intro u v
    constructor
    · intro hadj
      refine ⟨hadj.ne, ?_⟩
      by_cases hu : u ∈ L
      · exact Or.inr (Or.inl ⟨hu, (hleafAdj u hu v).mp hadj⟩)
      · by_cases hv : v ∈ L
        · exact Or.inr (Or.inr ⟨hv, (hleafAdj v hv u).mp hadj.symm⟩)
        · exact Or.inl ⟨hu, hv⟩
    · rintro ⟨huv, hcase⟩
      rcases hcase with ⟨hu, hv⟩ | ⟨hu, hvp⟩ | ⟨hv, hup⟩
      · exact hcoreAdj u (Finset.mem_compl.mpr hu) v (Finset.mem_compl.mpr hv) huv
      · exact (hleafAdj u hu v).mpr hvp
      · exact ((hleafAdj v hv u).mpr hup).symm
  exact ⟨p, hpNotL, hLdegree, hcountExact, hcoreTop, hLindependent, hshape⟩

end ErdosProblems.PathUpperReduction

