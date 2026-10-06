module

public import BoundaryEndpoint
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
Derive the actual long-cycle consequence (`2 * d ≤ C.length`) from minimum degree `≥ d`
and 2-connectedness (`G.Connected` and `∀ z, (G.induce {w | w ≠ z}).Connected`)
using `BoundaryEndpoint.uniform_endpoint_vertex_threshold`.
-/

open SimpleGraph

namespace ErdosProblems.PathUpperReduction.LongCycleFromMinimumDegree1105

variable {V : Type*} [Fintype V]

/-- A maximum over ALL actual simple paths, seeded by an actual nil path. -/
theorem exists_global_maximum_path (G : SimpleGraph V) (x : V) :
    ∃ u v, ∃ P : G.Walk u v, P.IsPath ∧
      ∀ a b, ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length := by
  classical
  let s : Set ℕ := {l | ∃ a b, ∃ Q : G.Walk a b, Q.IsPath ∧ Q.length = l}
  have hs : s.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V)) (by
    intro l hl
    obtain ⟨a, b, Q, hQ, hlen⟩ := hl
    exact hlen ▸ hQ.length_lt.le)
  have hseed : 0 ∈ s := ⟨x, x, Walk.nil, Walk.IsPath.nil, rfl⟩
  obtain ⟨l, hm⟩ := hs.exists_maximal ⟨0, hseed⟩
  obtain ⟨u, v, P, hp, hlen⟩ := hm.1
  refine ⟨u, v, P, hp, ?_⟩
  intro a b Q hQ
  have hbound := hm.le (show Q.length ∈ s from ⟨a, b, Q, hQ, rfl⟩)
  omega

omit [Fintype V] in
/-- Global maximum, rather than merely maximal, captures BOTH endpoints. -/
theorem global_maximum_captures_endpoints {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (hp : P.IsPath)
    (hmax : ∀ a b, ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length) :
    (∀ z, G.Adj u z → z ∈ P.support) ∧
      (∀ z, G.Adj v z → z ∈ P.support) := by
  constructor
  · intro z huz
    by_contra hz
    let Q := Walk.cons huz.symm P
    have hQ : Q.IsPath := hp.cons hz
    have hbound := hmax z v Q hQ
    simp only [Q, Walk.length_cons] at hbound
    omega
  · intro z hvz
    by_contra hz
    have hzrev : z ∉ P.reverse.support := by simpa only [Walk.support_reverse,
      List.mem_reverse] using hz
    let Q := Walk.cons hvz.symm P.reverse
    have hQ : Q.IsPath := hp.reverse.cons hzrev
    have hbound := hmax z u Q hQ
    simp only [Q, Walk.length_cons, Walk.length_reverse] at hbound
    omega

/-- A nonspanning actual cycle extends to a path of its FULL cycle length. -/
theorem cycle_length_le_global_maximum {G : SimpleGraph V} {u v x : V}
    (hconn : G.Connected) (P : G.Walk u v)
    (hmax : ∀ a b, ∀ Q : G.Walk a b, Q.IsPath → Q.length ≤ P.length)
    (C : G.Walk x x) (hC : C.IsCycle) (hsmall : C.length < Fintype.card V) :
    C.length ≤ P.length := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, z ∉ C.support := by
    by_contra hnone
    have hall : ∀ z, z ∈ C.support := by
      intro z
      by_contra hz
      exact hnone ⟨z, hz⟩
    have heq : C.support.toFinset = Finset.univ := by
      ext z
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      exact hall z
    have hcard := BoundaryEndpoint.cycle_vertex_card C hC
    rw [heq, Finset.card_univ] at hcard
    omega
  obtain ⟨w⟩ := hconn x z
  obtain ⟨dart, _hmem, hin, hout⟩ :=
    w.exists_boundary_dart {y | y ∈ C.support} C.start_mem_support hz
  let rot := C.rotate dart.fst hin
  have hrot : rot.IsCycle := hC.rotate hin
  have houtside : dart.snd ∉ rot.dropLast.support := by
    intro h
    rw [rot.support_dropLast hrot.not_nil] at h
    have hrotmem : dart.snd ∈ rot.support := List.mem_of_mem_dropLast h
    have hCmem : dart.snd ∈ C.support :=
      (C.mem_support_rotate_iff dart.fst hin).mp hrotmem
    exact hout hCmem
  let Q := Walk.cons dart.adj.symm rot.dropLast
  have hQ : Q.IsPath := hrot.isPath_dropLast.cons houtside
  have hlen : Q.length = C.length := by
    change rot.dropLast.length + 1 = C.length
    exact (Walk.length_dropLast_add_one hrot.not_nil).trans
      (Walk.length_rotate C dart.fst hin)
  have hbound := hmax _ _ Q hQ
  rw [hlen] at hbound
  exact hbound

/-- The actual Dirac consequence for d≥4, obtained by TWO fitting applications
of BoundaryEndpoint. Every vertex and edge remains in the original graph. -/
theorem exists_long_cycle_of_minimum_degree (G : SimpleGraph V) (d : ℕ)
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hdelete : ∀ z, (G.induce {w | w ≠ z}).Connected)
    (hdegree : ∀ z, d ≤ Nat.card (G.neighborSet z)) :
    ∃ x, ∃ C : G.Walk x x, C.IsCycle ∧ 2 * d ≤ C.length := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u, v, P, hp, hmax⟩ := exists_global_maximum_path G (Classical.arbitrary V)
  obtain ⟨hleft, hright⟩ := global_maximum_captures_endpoints P hp hmax
  have hcounts (x : V) (hcapture : ∀ z, G.Adj x z → z ∈ P.support) :
      (P.support.toFinset.filter (fun z => G.Adj x z)).card =
        Nat.card (G.neighborSet x) := by
    have heq : P.support.toFinset.filter (fun z => G.Adj x z) = G.neighborFinset x := by
      ext z
      simp only [Finset.mem_filter, List.mem_toFinset, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.2, fun hz => ⟨hcapture z hz, hz⟩⟩
    rw [heq, SimpleGraph.neighborFinset_def, ← Nat.card_eq_card_toFinset]
  have hleftDegree : d ≤ (P.support.toFinset.filter (fun z => G.Adj u z)).card := by
    rw [hcounts u hleft]
    exact hdegree u
  have hrightDegree : d ≤ (P.support.toFinset.filter (fun z => G.Adj v z)).card := by
    rw [hcounts v hright]
    exact hdegree v
  have hleftBound : (P.support.toFinset.filter (fun z => G.Adj u z)).card ≤ P.length := by
    have hsub : P.support.toFinset.filter (fun z => G.Adj u z) ⊆
        P.support.toFinset.erase u := by
      intro z hz
      obtain ⟨hzP, huz⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_erase.mpr ⟨huz.ne', hzP⟩
    have hbound := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr P.start_mem_support),
      List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hbound
    omega
  have hPfive : 5 ≤ P.length + 1 := by omega
  have hsum : 2 * d ≤
      (P.support.toFinset.filter (fun z => G.Adj (P.getVert 0) z)).card +
        (P.support.toFinset.filter (fun z => G.Adj (P.getVert P.length) z)).card := by
    simp only [Walk.getVert_zero, Walk.getVert_length]
    omega
  have hdel : ∀ i : Fin (P.length + 1), 0 < i → i < Fin.last P.length →
      (G.induce {w | w ≠ P.getVert i.val}).Connected := by
    intro i _hi _hlast
    exact hdelete (P.getVert i.val)
  have hlong : 2 * d < P.length + 1 := by
    by_contra hnot
    have hshort : P.length + 1 ≤ 2 * d := by omega
    obtain ⟨C, hC, hlen⟩ := BoundaryEndpoint.uniform_endpoint_vertex_threshold
      P hp hdel (P.length + 1) hPfive le_rfl (by omega)
    have hbound := hmax _ _ C.dropLast hC.isPath_dropLast
    have hdrop := Walk.length_dropLast_add_one hC.not_nil
    have hsmall : C.length < Fintype.card V := by omega
    have hbound' := cycle_length_le_global_maximum hconn P hmax C hC hsmall
    omega
  obtain ⟨C, hC, hlen⟩ := BoundaryEndpoint.uniform_endpoint_vertex_threshold
    P hp hdel (2 * d) (by omega) hlong.le hsum
  exact ⟨P.getVert 0, C, hC, hlen⟩

end ErdosProblems.PathUpperReduction.LongCycleFromMinimumDegree1105
