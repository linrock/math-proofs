module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.Preorder.Finite

@[expose] public section

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.AllLongSaturation

variable {V : Type*}

/-- A finite graph property admits a same-carrier inclusion-maximal supergraph. -/
theorem exists_saturated_property_supergraph [Finite V]
    (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H, G ≤ H ∧ Q H ∧ ∀ u v, u ≠ v → ¬ H.Adj u v →
      ¬ Q (H ⊔ fromEdgeSet {s(u, v)}) := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ Q H}
  have hfinite : S.Finite := Set.toFinite S
  obtain ⟨H, ⟨hH, hmax⟩⟩ := hfinite.exists_maximal ⟨G, le_refl G, hG⟩
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro u v huv hmissing hnew
  have hJ : H ⊔ fromEdgeSet {s(u, v)} ∈ S :=
    ⟨hH.1.trans le_sup_left, hnew⟩
  have hback : H ⊔ fromEdgeSet {s(u, v)} ≤ H := hmax hJ le_sup_left
  apply hmissing
  apply hback
  exact Or.inr (by simp [fromEdgeSet_adj, huv])

/-- Saturation excludes the entire family of long cycles, not one fixed order. -/
theorem exists_all_long_saturated_supergraph [Finite V]
    (G : SimpleGraph V) (K : ℕ)
    (hG : ∀ m, K ≤ m → (cycleGraph m).Free G) :
    ∃ H, G ≤ H ∧ (∀ m, K ≤ m → (cycleGraph m).Free H) ∧
      ∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)})) := by
  classical
  obtain ⟨H, hGH, hfree, hsat⟩ := exists_saturated_property_supergraph
    (fun H => ∀ m, K ≤ m → (cycleGraph m).Free H) G hG
  refine ⟨H, hGH, hfree, ?_⟩
  intro u v huv hmissing
  have h := hsat u v huv hmissing
  simp only [SimpleGraph.Free, SimpleGraph.IsContained] at h
  push Not at h
  exact h

/-- Deletion connectivity is retained on the same deleted-vertex carrier. -/
theorem deletion_connected_mono (G H : SimpleGraph V) (hGH : G ≤ H)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) :
    ∀ z, (H.induce {w | w ≠ z}).Connected := by
  intro z
  apply SimpleGraph.Connected.mono _ (hdel z)
  intro a b hab
  exact hGH hab

/-- The saturated extension retains the actual deletion-connectivity hypothesis. -/
theorem exists_connected_all_long_saturated_supergraph [Finite V]
    (G : SimpleGraph V) (K : ℕ)
    (hG : ∀ m, K ≤ m → (cycleGraph m).Free G)
    (hdel : ∀ z, (G.induce {w | w ≠ z}).Connected) :
    ∃ H, G ≤ H ∧ (∀ m, K ≤ m → (cycleGraph m).Free H) ∧
      (∀ z, (H.induce {w | w ≠ z}).Connected) ∧
      ∀ u v, u ≠ v → ¬ H.Adj u v →
        ∃ m, K ≤ m ∧ Nonempty ((cycleGraph m).Copy
          (H ⊔ fromEdgeSet {s(u, v)})) := by
  obtain ⟨H, hGH, hfree, hsat⟩ := exists_all_long_saturated_supergraph G K hG
  exact ⟨H, hGH, hfree, deletion_connected_mono G H hGH hdel, hsat⟩

/-- Uniform Copy-freedom implies absence of every actual long cycle walk. -/
theorem no_long_cycle (G : SimpleGraph V) {K : ℕ} (hK : 5 ≤ K)
    (hfree : ∀ m, K ≤ m → (cycleGraph m).Free G) :
    ∀ q (C : G.Walk q q), C.IsCycle → C.length < K := by
  intro q C hC
  by_contra hsmall
  have hlen : K ≤ C.length := by omega
  apply hfree C.length hlen
  exact (cycleGraph_isContained_iff (by omega)).mpr ⟨q, C, hC, rfl⟩

variable {G : SimpleGraph V} {u v : V}

theorem edge_mem_old_of_ne_added_pair {e : Sym2 V}
    (he : e ∈ (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet)
    (hne : e ≠ s(u, v)) : e ∈ G.edgeSet := by
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet] at he
  rcases he with he | he
  · exact he
  · exact (hne (Set.mem_singleton_iff.mp he.1)).elim

theorem cycle_oriented_at_pair {J : SimpleGraph V}
    (huv : u ≠ v) (C : J.Walk u u) (hc : C.IsCycle)
    (he : s(u, v) ∈ C.edges) :
    ∃ D : J.Walk u u, D.IsCycle ∧ D.length = C.length ∧ D.snd = v := by
  have hccons : (SimpleGraph.Walk.cons (C.adj_snd hc.not_nil) C.tail).IsCycle := by
    rw [SimpleGraph.Walk.cons_tail_eq C hc.not_nil]
    exact hc
  have hecons : s(u, v) ∈
      (SimpleGraph.Walk.cons (C.adj_snd hc.not_nil) C.tail).edges := by
    rw [SimpleGraph.Walk.cons_tail_eq C hc.not_nil]
    exact he
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hecons
  rcases hecons with hfirst | htail
  · have hsnd : C.snd = v := by
      rcases Sym2.eq_iff.mp hfirst with hsame | hswap
      · exact hsame.2.symm
      · exact (huv hswap.2.symm).elim
    exact ⟨C, hc, rfl, hsnd⟩
  · have hprev : v = C.tail.penultimate :=
      hc.isPath_tail.eq_penultimate_of_mem_edges htail
    have htailnil : ¬ C.tail.Nil :=
      SimpleGraph.Walk.not_nil_of_isCycle_cons hccons
    have hCprev : C.penultimate = C.tail.penultimate := by
      calc
        C.penultimate =
            (SimpleGraph.Walk.cons (C.adj_snd hc.not_nil) C.tail).penultimate := by
          rw [SimpleGraph.Walk.cons_tail_eq C hc.not_nil]
        _ = C.tail.penultimate :=
          SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ htailnil
    refine ⟨C.reverse, hc.reverse, by simp, ?_⟩
    rw [SimpleGraph.Walk.snd_reverse]
    exact hCprev.trans hprev.symm

theorem added_pair_path {m : ℕ}
    (hm : 2 < m) (hfree : (SimpleGraph.cycleGraph m).Free G)
    (huv : u ≠ v) (_hmissing : ¬ G.Adj u v)
    (f : (SimpleGraph.cycleGraph m).Copy
      (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)})) :
    ∃ P : G.Walk u v, P.IsPath ∧ P.length = m - 1 := by
  classical
  let J : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
  obtain ⟨w, C, hc, hcm⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff hm).mp f.isContained
  have he : s(u, v) ∈ C.edges := by
    by_contra hnot
    have hEdges : ∀ e, e ∈ C.edges → e ∈ G.edgeSet := by
      intro e heC
      apply edge_mem_old_of_ne_added_pair (C.edges_subset_edgeSet heC)
      intro heq
      exact hnot (heq ▸ heC)
    have hcG : (C.transfer G hEdges).IsCycle := hc.transfer hEdges
    have hlenG : (C.transfer G hEdges).length = m := by
      simpa only [SimpleGraph.Walk.length_transfer] using hcm
    exact hfree ((SimpleGraph.cycleGraph_isContained_iff hm).mpr
      ⟨w, C.transfer G hEdges, hcG, hlenG⟩)
  have hu : u ∈ C.support := C.fst_mem_support_of_mem_edges he
  let D : J.Walk u u := C.rotate u hu
  have hcD : D.IsCycle := by
    simpa only [D] using hc.rotate hu
  have hlenD : D.length = m := by
    simpa only [D] using (C.length_rotate u hu).trans hcm
  have heD : s(u, v) ∈ D.edges := by
    exact ((C.rotate_edges u hu).perm.mem_iff).mpr he
  obtain ⟨E, hcE, hlenE, hsnd⟩ := cycle_oriented_at_pair huv D hcD heD
  have hcEcons : (SimpleGraph.Walk.cons (E.adj_snd hcE.not_nil) E.tail).IsCycle := by
    rw [SimpleGraph.Walk.cons_tail_eq E hcE.not_nil]
    exact hcE
  have havoid : s(u, v) ∉ E.tail.edges := by
    have h := (SimpleGraph.Walk.cons_isCycle_iff E.tail
      (E.adj_snd hcE.not_nil)).mp hcEcons
    simpa only [hsnd] using h.2
  let T : J.Walk v u := E.tail.copy hsnd rfl
  have hpT : T.IsPath := by
    exact (SimpleGraph.Walk.isPath_copy E.tail hsnd rfl).mpr hcE.isPath_tail
  have hTold : ∀ e, e ∈ T.edges → e ∈ G.edgeSet := by
    intro e heT
    have heTail : e ∈ E.tail.edges := by simpa only [T, SimpleGraph.Walk.edges_copy] using heT
    apply edge_mem_old_of_ne_added_pair (E.tail.edges_subset_edgeSet heTail)
    intro heq
    exact havoid (heq ▸ heTail)
  refine ⟨(T.transfer G hTold).reverse, (hpT.transfer hTold).reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_transfer,
    T, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_tail]
  rw [hlenE, hlenD]

end ErdosProblems.PathUpperReduction.AllLongSaturation
