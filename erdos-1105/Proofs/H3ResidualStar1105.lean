module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

/-!
The exact h=3 residual obstruction:
four ORIGINAL vertices, minimum ORIGINAL degree one, at least three ORIGINAL
edges, and ordinary non-induced P4 freedom force a spanning three-leaf star. The actual residual wrapper keeps G.induce(K\\W), with no graph replacement,
connectedness, supplied center, favorable order, universal set or cover input. This source does not derive its hypotheses from the full original-color caller
and does not prove a whole-support cover or universal #1105(ii).
-/

namespace ErdosProblems.PathUpperReduction.H3ResidualStar1105

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Apply Mathlib's actual IsPath-to-pathGraph API to three original edges.
Extra edges among the four vertices are permitted: this is an ordinary Copy. -/
theorem false_of_three_edge_chain
    (R : SimpleGraph V) (hfree : (pathGraph 4).Free R)
    (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h01 : R.Adj a b) (h12 : R.Adj b c) (h23 : R.Adj c d) : False := by
  let p : R.Walk a d :=
    .cons h01 (.cons h12 (.cons h23 .nil))
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simp [p, hab, hac, had, hbc, hbd, hcd]
  have hcopy : pathGraph 4 ⊑ R := by
    simpa [p] using hp.isContained_pathGraph
  exact hfree hcopy

/-- A reusable finite ORIGINAL four-vertex lemma, needed precisely to remove
the two-K2 h=3 obstruction. The center and all three leaves are derived. -/
theorem exists_center_of_four_min_degree_edges_three_path_free
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hcard : Fintype.card V = 4)
    (hmin : ∀ x : V, 1 ≤ R.degree x)
    (hedges : 3 ≤ R.edgeFinset.card)
    (hfree : (pathGraph 4).Free R) :
    ∃ c : V, (Finset.univ.erase c).card = 3 ∧
      (∀ x : V, x ≠ c → R.Adj c x) ∧
      (∀ x : V, x ≠ c → ∀ y : V, y ≠ c → ¬ R.Adj x y) := by
  classical
  have htwo : ∃ c : V, 2 ≤ R.degree c := by
    by_contra hnone
    have hbound : ∀ x : V, R.degree x ≤ 1 := by
      intro x
      have hx : ¬ 2 ≤ R.degree x := by
        intro hx
        exact hnone ⟨x, hx⟩
      omega
    have hsum : (∑ x : V, R.degree x) ≤ ∑ x : V, (1 : ℕ) :=
      Finset.sum_le_sum (fun x _hx => hbound x)
    have hconstant : (∑ x : V, (1 : ℕ)) = 4 := by simp [hcard]
    have hhand := R.sum_degrees_eq_twice_card_edges
    omega
  obtain ⟨c, hc2⟩ := htwo
  have hneighbors : 1 < (R.neighborFinset c).card := by
    rw [R.card_neighborFinset_eq_degree c]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hneighbors
  have hcu : R.Adj c u := (R.mem_neighborFinset c u).mp hu
  have hcv : R.Adj c v := (R.mem_neighborFinset c v).mp hv
  let T : Finset V := {c, u, v}
  have hTcard : T.card = 3 := by
    simp [T, hcu.ne, hcv.ne, huv]
  have hrestcard : (Finset.univ \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T),
      Finset.card_univ, hcard, hTcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hrestcard
  have hzmem : z ∈ Finset.univ \ T := by
    rw [hz]
    exact Finset.mem_singleton_self z
  have hzT : z ∉ T := (Finset.mem_sdiff.mp hzmem).2
  have hzc : z ≠ c := by
    intro h
    apply hzT
    simp [T, h]
  have hzu : z ≠ u := by
    intro h
    apply hzT
    simp [T, h]
  have hzv : z ≠ v := by
    intro h
    apply hzT
    simp [T, h]
  have hall : ∀ x : V, x = c ∨ x = u ∨ x = v ∨ x = z := by
    intro x
    by_cases hxT : x ∈ T
    · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with hxc | hxu | hxv
      · exact Or.inl hxc
      · exact Or.inr (Or.inl hxu)
      · exact Or.inr (Or.inr (Or.inl hxv))
    · have hxrest : x ∈ Finset.univ \ T :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩
      have hxz : x = z := by simpa only [hz, Finset.mem_singleton] using hxrest
      exact Or.inr (Or.inr (Or.inr hxz))
  have hcz : R.Adj c z := by
    have hzpos : 0 < R.degree z := by
      have hm := hmin z
      omega
    obtain ⟨y, hzy⟩ := (R.degree_pos_iff_exists_adj z).mp hzpos
    rcases hall y with hyc | hyu | hyv | hyz
    · subst y
      exact hzy.symm
    · subst y
      exact False.elim (false_of_three_edge_chain R hfree z u c v
        hzu hzc hzv hcu.ne.symm huv hcv.ne hzy hcu.symm hcv)
    · subst y
      exact False.elim (false_of_three_edge_chain R hfree z v c u
        hzv hzc hzu hcv.ne.symm huv.symm hcu.ne hzy hcv.symm hcu)
    · exact False.elim (hzy.ne hyz.symm)
  have hnotuv : ¬ R.Adj u v := by
    intro huvAdj
    exact false_of_three_edge_chain R hfree z c u v
      hzc hzu hzv hcu.ne hcv.ne huv hcz.symm hcu huvAdj
  have hnotuz : ¬ R.Adj u z := by
    intro huzAdj
    exact false_of_three_edge_chain R hfree v c u z
      hcv.ne.symm huv.symm hzv.symm hcu.ne hzc.symm hzu.symm
      hcv.symm hcu huzAdj
  have hnotvz : ¬ R.Adj v z := by
    intro hvzAdj
    exact false_of_three_edge_chain R hfree u c v z
      hcu.ne.symm huv hzu.symm hcv.ne hzc.symm hzv.symm
      hcu.symm hcv hvzAdj
  have hleaf : ∀ x : V, x ≠ c → x = u ∨ x = v ∨ x = z := by
    intro x hxc
    rcases hall x with h | h | h | h
    · exact False.elim (hxc h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, hcard]
  · intro x hxc
    rcases hleaf x hxc with rfl | rfl | rfl
    · exact hcu
    · exact hcv
    · exact hcz
  · intro x hxc y hyc hxy
    rcases hleaf x hxc with rfl | rfl | rfl <;>
      rcases hleaf y hyc with rfl | rfl | rfl
    all_goals first
      | exact hxy.ne rfl
      | exact hnotuv hxy
      | exact hnotuv hxy.symm
      | exact hnotuz hxy
      | exact hnotuz hxy.symm
      | exact hnotvz hxy
      | exact hnotvz hxy.symm

omit [Fintype V] in
/-- Project the generic lemma from precisely ORIGINAL G.induce(K\\W).
The actual ambient center, exact three leaves and their original adjacency
are returned. No cover or universal-W assertion is assumed or concluded. -/
theorem original_residual_star
    (G : SimpleGraph V) [DecidableRel G.Adj] (K W : Finset V)
    (hcard : (K \ W).card = 4)
    (hmin : ∀ x : ((K \ W : Finset V) : Set V),
      1 ≤ (G.induce ((K \ W : Finset V) : Set V)).degree x)
    (hedges : 3 ≤ (G.induce ((K \ W : Finset V) : Set V)).edgeFinset.card)
    (hfree : (pathGraph 4).Free (G.induce ((K \ W : Finset V) : Set V))) :
    ∃ c : V, c ∈ K \ W ∧ ((K \ W).erase c).card = 3 ∧
      (∀ x ∈ (K \ W).erase c, G.Adj c x) ∧
      (∀ x ∈ (K \ W).erase c, ∀ y ∈ (K \ W).erase c, ¬ G.Adj x y) := by
  classical
  let R := G.induce ((K \ W : Finset V) : Set V)
  have hRcard : Fintype.card ((K \ W : Finset V) : Set V) = 4 :=
    (Fintype.card_of_finset' (p := ((K \ W : Finset V) : Set V))
      (K \ W) (fun _ => Iff.rfl)).trans hcard
  obtain ⟨c, _hthree, hcenter, hleaves⟩ :=
    exists_center_of_four_min_degree_edges_three_path_free R hRcard hmin hedges hfree
  refine ⟨c.val, c.property, ?_, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem c.property, hcard]
  · intro x hx
    have hx' := Finset.mem_erase.mp hx
    have hxc : (⟨x, hx'.2⟩ : ((K \ W : Finset V) : Set V)) ≠ c := by
      intro heq
      exact hx'.1 (congrArg Subtype.val heq)
    exact hcenter _ hxc
  · intro x hx y hy
    have hx' := Finset.mem_erase.mp hx
    have hy' := Finset.mem_erase.mp hy
    have hxc : (⟨x, hx'.2⟩ : ((K \ W : Finset V) : Set V)) ≠ c := by
      intro heq
      exact hx'.1 (congrArg Subtype.val heq)
    have hyc : (⟨y, hy'.2⟩ : ((K \ W : Finset V) : Set V)) ≠ c := by
      intro heq
      exact hy'.1 (congrArg Subtype.val heq)
    exact hleaves _ hxc _ hyc

end ErdosProblems.PathUpperReduction.H3ResidualStar1105

