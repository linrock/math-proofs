module

public import CycleCutBothEndpoints1105
public import CycleInsertion1105
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
An actual path Copy is converted to a simple walk with exactly its vertex
range. Cutting an actual cycle edge then supplies both prescribed endpoints
internally; two original contacts to a fresh vertex construct an actual cycle
with exactly one more vertex. No favorable path or rotation is supplied.
-/

namespace ErdosProblems.PathUpperReduction.CycleEdgeContact1105

open SimpleGraph

/-- The natural order of an actual path Copy gives an original simple walk,
including every copied vertex and both endpoint equations. -/
theorem walk_of_path_copy {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (q : (pathGraph (n + 3)).Copy G) :
    ∃ P : G.Walk (q 0) (q (Fin.last (n + 2))),
      P.IsPath ∧ P.length = n + 2 ∧
        ∀ w : V, w ∈ P.support ↔ w ∈ Set.range q := by
  classical
  let l : List V := List.ofFn (fun i : Fin (n + 3) => q i)
  have hne : l ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [l, List.length_ofFn, List.length_nil] at hlen
    omega
  have hchain : l.IsChain G.Adj := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have hi' : i + 1 < n + 3 := by
      simpa only [l, List.length_ofFn] using hi
    have ha : G.Adj (q ⟨i, by omega⟩) (q ⟨i + 1, hi'⟩) :=
      q.toHom.map_rel' (pathGraph_adj.mpr (Or.inl rfl))
    simpa only [l, List.getElem_ofFn] using ha
  have hhead : l.head hne = q 0 := by
    exact List.head_ofFn hne
  have hlast : l.getLast hne = q (Fin.last (n + 2)) := by
    exact List.getLast_ofFn_succ (fun i : Fin (n + 3) => q i)
  let W : G.Walk (l.head hne) (l.getLast hne) :=
    SimpleGraph.Walk.ofSupport l hne hchain
  let P : G.Walk (q 0) (q (Fin.last (n + 2))) := W.copy hhead hlast
  refine ⟨P, ?_, ?_, ?_⟩
  · apply (SimpleGraph.Walk.isPath_copy W hhead hlast).mpr
    apply SimpleGraph.Walk.IsPath.mk'
    simpa only [W, SimpleGraph.Walk.support_ofSupport, l] using
      (List.nodup_ofFn_ofInjective (f := fun i : Fin (n + 3) => q i) (by
        intro a b h
        exact q.injective h))
  · simp only [P, W, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.length_ofSupport, l, List.length_ofFn]
    omega
  · intro w
    change w ∈ (W.copy hhead hlast).support ↔ w ∈ Set.range q
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]
    exact List.mem_ofFn

/-- A vertex outside an actual cycle Copy that contacts the endpoints of an
actual cycle edge yields an explicitly constructed longer original cycle. -/
theorem cycle_of_fresh_contacts_to_cycle_edge {V : Type*} (G : SimpleGraph V)
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (u v : Fin (n + 3))
    (huv : (cycleGraph (n + 3)).Adj u v) (z : V)
    (hz : z ∉ Set.range c) (hzu : G.Adj z (c u)) (hvz : G.Adj (c v) z) :
    ∃ D : G.Walk z z, D.IsCycle ∧ D.length = n + 4 := by
  classical
  obtain ⟨p, hp0, hpLast, hpRange⟩ :=
    CycleCutBothEndpoints1105.path_of_cycle_cut_edge_at_both_endpoints G c u v huv
  let q : (pathGraph (n + 3)).Copy G :=
    ⟨⟨(fun i => p i), by
      intro i j hij
      exact (SimpleGraph.deleteEdges_adj.mp (p.toHom.map_rel' hij)).1⟩,
      p.injective⟩
  obtain ⟨P, hP, hPLength, hPSupport⟩ := walk_of_path_copy G q
  have hq0 : q 0 = c u := hp0
  have hqLast : q (Fin.last (n + 2)) = c v := hpLast
  let Q : G.Walk (c u) (c v) := P.copy hq0 hqLast
  have hQ : Q.IsPath := (SimpleGraph.Walk.isPath_copy P hq0 hqLast).mpr hP
  have hQLength : Q.length = n + 2 := by
    simpa only [Q, SimpleGraph.Walk.length_copy] using hPLength
  have hzQ : z ∉ Q.support := by
    intro hm
    have hmP : z ∈ P.support := by
      simpa only [Q, SimpleGraph.Walk.support_copy] using hm
    have hmRange := (hPSupport z).mp hmP
    change z ∈ Set.range p at hmRange
    exact hz (hpRange ▸ hmRange)
  obtain ⟨hD, hDLength⟩ := CycleInsertion1105.cycle_of_fresh_endpoint_contact
    G Q hQ z (by omega) hzQ hzu hvz
  refine ⟨SimpleGraph.Walk.cons hzu (Q.concat hvz), hD, ?_⟩
  omega

end ErdosProblems.PathUpperReduction.CycleEdgeContact1105
