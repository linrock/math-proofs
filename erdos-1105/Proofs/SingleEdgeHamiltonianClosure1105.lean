module

public import AllLongSaturation
public import CyclePathOre

@[expose] public section

/-!
Single-edge Hamiltonian closure on the SAME Fin n. This is the first closure adapter needed by the even last-block rigidity
argument. The spanning path is derived internally from the actual added-edge
cycle. No all-pairs degree, connectedness, actual-core or favorable-path
premise is introduced.
-/

namespace ErdosProblems.PathUpperReduction.SingleEdgeHamiltonianClosure1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.AllLongSaturation
open ErdosProblems.AntiRamseyCyclePathOre

-- Match the defining finite-neighbor choice in the actual Ore source.
-- This installs no external degree or equality-decision hypothesis.
noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Adding one actual missing edge preserves existence of an n-vertex cycle
when the two ORIGINAL whole-carrier degrees sum to at least n. -/
theorem cycle_contained_add_edge_iff {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (u v : Fin n)
    (huv : u ≠ v) (hmissing : ¬ G.Adj u v)
    (hdegree : n ≤ G.degree u + G.degree v) :
    (cycleGraph n) ⊑ (G ⊔ fromEdgeSet {s(u, v)}) ↔ (cycleGraph n) ⊑ G := by
  classical
  constructor
  · intro hnew
    by_contra hnone
    have hfree : (cycleGraph n).Free G := hnone
    obtain ⟨f⟩ := hnew
    obtain ⟨P, hP, hPlength⟩ := added_pair_path
      (G := G) (u := u) (v := v) (m := n) (by omega) hfree huv hmissing f
    have hcard : P.length + 1 = n := by omega
    have hlength : 2 ≤ P.length := by omega
    let order : Fin (P.length + 1) → Fin n := fun i => P.getVert i.val
    have horder : Function.Injective order := by
      intro i j hij
      apply Fin.ext
      exact hP.getVert_injOn (Nat.le_of_lt_succ i.isLt)
        (Nat.le_of_lt_succ j.isLt) hij
    have hzero : order 0 = u := P.getVert_zero
    have hlast : order (Fin.last P.length) = v := P.getVert_length
    have hpath : ∀ a b : Fin (P.length + 1),
        a.val + 1 = b.val → G.Adj (order a) (order b) := by
      intro a b hab
      change G.Adj (P.getVert a.val) (P.getVert b.val)
      have hadj := P.adj_getVert_succ (i := a.val) (by omega)
      rw [hab] at hadj
      exact hadj
    have himageCard :
        ((Finset.univ : Finset (Fin (P.length + 1))).image order).card = n := by
      rw [Finset.card_image_of_injective _ horder, Finset.card_univ,
        Fintype.card_fin]
      exact hcard
    have himage :
        (Finset.univ : Finset (Fin (P.length + 1))).image order =
          (Finset.univ : Finset (Fin n)) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa only [himageCard, Finset.card_univ, Fintype.card_fin] using
        (Nat.le_refl n)
    have hfreeOnPath : (cycleGraph (P.length + 1)).Free (G.comap order) := by
      intro hcopy
      obtain ⟨g⟩ := hcopy
      let e : Fin (P.length + 1) ↪ Fin n := ⟨order, horder⟩
      have hactual : (cycleGraph (P.length + 1)) ⊑ G :=
        ⟨(SimpleGraph.Embedding.comap e G).toCopy.comp g⟩
      apply hfree
      exact Eq.mp (congrArg (fun m : ℕ => (cycleGraph m) ⊑ G) hcard) hactual
    have hdeficit := ordered_path_internal_endpoint_degree_sum_lt
      hlength G order horder hpath hfreeOnPath
    simp only [himage, Finset.inter_univ] at hdeficit
    have hdegreePath :
        G.degree (order 0) + G.degree (order (Fin.last P.length)) < n := by
      simpa only [card_neighborFinset_eq_degree, hcard] using hdeficit
    have hsmall : G.degree u + G.degree v < n := by
      rw [hzero, hlast] at hdegreePath
      exact hdegreePath
    omega
  · intro hold
    exact hold.mono_right le_sup_left

end ErdosProblems.PathUpperReduction.SingleEdgeHamiltonianClosure1105
