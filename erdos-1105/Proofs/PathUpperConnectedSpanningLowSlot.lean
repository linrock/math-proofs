module

public import PathUpperConnectedSpanningLargeOrder
public import Batteries.Tactic.OpenPrivate
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Tactic

@[expose] public section

/-!
equality auxiliary for connected spanning degree-closed graphs. The exact existing
private strict arithmetic is reused; no new copy/map or arithmetic infrastructure
is supplied. This derives exact S1: a complete remainder and two degree1 leaves
at one actual common hub. Closure itself rules out distinct leaf neighbors.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- Retain the actual induced-complement count, rather than replacing it with
its clique cap. This is the equality information needed from the edge cover. -/
theorem edge_count_le_induced_complement_and_slots
    {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (L : Finset (Fin k)) (a : ℕ) (hL : ∀ x ∈ L, H.degree x ≤ a) :
    H.edgeFinset.card ≤ (H.induce (↑(Lᶜ) : Set (Fin k))).edgeFinset.card +
      L.card * a := by
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
  have hinsideCount : inside.card = (H.induce (↑C : Set (Fin k))).edgeFinset.card :=
    SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := H) C
  have htouchingCount : touching.card ≤ L.card * a := by
    apply Finset.card_biUnion_le_card_mul L (fun v => H.incidenceFinset v) a
    intro x hx
    simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hL x hx
  calc
    H.edgeFinset.card ≤ (inside ∪ touching).card := Finset.card_le_card hcover
    _ ≤ inside.card + touching.card := Finset.card_union_le inside touching
    _ ≤ inside.card + L.card * a := Nat.add_le_add_left htouchingCount inside.card
    _ = (H.induce (↑(Lᶜ) : Set (Fin k))).edgeFinset.card + L.card * a := by
      rw [hinsideCount]

/-- At order at least11, a connected closed spanning path-free graph at the
threshold is exactly a complete remainder with two degree1 leaves at one hub.
This is an ordinary graph saturation result; it supplies no color-owner claim. -/
theorem connected_spanning_dense_closed_is_s1
    (k : ℕ) (hk : 11 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2)
    (hfree : (pathGraph k).Free H)
    (hedges : (k - 2).choose 2 + 2 ≤ H.edgeFinset.card) :
    ∃ (L : Finset (Fin k)) (w : Fin k),
      L.card = 2 ∧ w ∉ L ∧ (∀ x ∈ L, H.degree x = 1) ∧
      H.edgeFinset.card = (k - 2).choose 2 + 2 ∧
      H.induce (↑(Lᶜ) : Set (Fin k)) = ⊤ ∧
      (∀ x ∈ L, ∀ y ∈ L, ¬ H.Adj x y) ∧
      (∀ u v, H.Adj u v ↔ u ≠ v ∧
        ((u ∉ L ∧ v ∉ L) ∨ (u ∈ L ∧ v = w) ∨ (v ∈ L ∧ u = w))) := by
  classical
  have hneTop : H ≠ ⊤ := by
    intro heq
    apply hfree
    rw [heq]
    exact ⟨Copy.ofLE (pathGraph k) ⊤ le_top⟩
  obtain ⟨a, L, ha, haBound, hLcard, hLdeg, hcount⟩ :=
    spanning_degree_slots_and_edge_count k (by omega) H hconn hneTop hclosure
  have haOne : a = 1 := by
    by_contra hne
    have haStrict : 2 ≤ a := by omega
    have hstrict := degree_slot_cap_lt_spanning_threshold k a hk ha haStrict haBound
    exact (not_lt_of_ge (hedges.trans hcount)) hstrict
  subst a
  have hLcardTwo : L.card = 2 := by omega
  have hshift : k - 1 - 1 = k - 2 := by omega
  have hcountThreshold : H.edgeFinset.card ≤ (k - 2).choose 2 + 2 := by
    simpa [hshift] using hcount
  have hcountExact : H.edgeFinset.card = (k - 2).choose 2 + 2 :=
    Nat.le_antisymm hcountThreshold hedges
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
  exact ⟨L, p, hLcardTwo, hpNotL, hLdegree, hcountExact, hcoreTop, hLindependent, hshape⟩

end ErdosProblems.PathUpperReduction
