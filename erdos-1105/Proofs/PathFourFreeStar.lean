module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
A connected graph on at least four vertices with no non-induced four-vertex
path is a star. This is the no-`P₄` branch of the connected `P₅` extremal
bound for Erdős #1105.
-/

namespace ErdosProblems.AntiRamseyPathFourFree

open SimpleGraph

/-- Four distinct consecutive vertices contradict `pathGraph 4`-freeness. -/
theorem no_four_vertex_path {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 4).Free G) (a b c d : V)
    (hne : [a, b, c, d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) : False := by
  let p : G.Walk a d := .cons hab (.cons hbc (.cons hcd .nil))
  have hp : p.IsPath := by
    simpa [p, Walk.isPath_def] using hne
  have hcopy : (pathGraph 4) ⊑ G := by
    simpa [p] using hp.isContained_pathGraph
  exact hfree hcopy

/-- An adjacency-closed nonempty set in a connected graph is all vertices. -/
theorem connected_closed_set_eq_univ {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) {S : Set V} (a : V) (ha : a ∈ S)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) : S = Set.univ := by
  have walk_closed : ∀ {u v : V}, (p : G.Walk u v) → u ∈ S → v ∈ S := by
    intro u v p
    induction p with
    | nil => exact fun hu => hu
    | cons hadj p ih => exact fun hu => ih (hclosed _ hu _ hadj)
  ext v
  constructor
  · intro _
    trivial
  · intro _
    exact (hconn a v).elim fun p => walk_closed p ha

/-- In a connected graph with at least three vertices there is a vertex
with two distinct neighbors. -/
theorem connected_exists_two_neighbors {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (hconn : G.Connected) :
    ∃ b a c : Fin n, a ≠ c ∧ G.Adj b a ∧ G.Adj b c := by
  let x : Fin n := ⟨0, by omega⟩
  let y : Fin n := ⟨1, by omega⟩
  let z : Fin n := ⟨2, by omega⟩
  have hxy : x ≠ y := by simp [x, y]
  have hxz : x ≠ z := by simp [x, z]
  have hyz : y ≠ z := by simp [y, z]
  have pair_of_nonadjacent {u v : Fin n} (huv : u ≠ v)
      (hnot : ¬ G.Adj u v) :
      ∃ b a c : Fin n, a ≠ c ∧ G.Adj b a ∧ G.Adj b c := by
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
    have hdist : 1 < G.dist u v :=
      (hconn u v).one_lt_dist_of_ne_of_not_adj huv hnot
    obtain ⟨w, b, c, hwb, hbc, _, hwc⟩ := p.exists_adj_adj_not_adj_ne hp hdist
    exact ⟨b, w, c, hwc, hwb.symm, hbc⟩
  by_cases hxyadj : G.Adj x y
  · by_cases hxzadj : G.Adj x z
    · exact ⟨x, y, z, hyz, hxyadj, hxzadj⟩
    · exact pair_of_nonadjacent hxz hxzadj
  · exact pair_of_nonadjacent hxy hxyadj

/-- A vertex with two neighbors has a universal closed neighborhood in a
connected `P₄`-free graph. -/
theorem universal_of_two_neighbors {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) (hfree : (pathGraph 4).Free G)
    (b a c : V) (hac : a ≠ c) (hba : G.Adj b a) (hbc : G.Adj b c) :
    ∀ v : V, v ≠ b → G.Adj b v := by
  let S : Set V := {v | v = b ∨ G.Adj b v}
  have hbS : b ∈ S := Or.inl rfl
  have hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S := by
    intro u hu v huv
    by_cases hvb : v = b
    · exact Or.inl hvb
    by_cases hbv : G.Adj b v
    · exact Or.inr hbv
    rcases hu with hub | hbu
    · subst u
      exact False.elim (hbv huv)
    have hub : u ≠ b := hbu.ne'
    by_cases hua : u = a
    · have hnodup : [c, b, u, v].Nodup := by
        have hcb : c ≠ b := hbc.ne'
        have hcu : c ≠ u := by simpa [hua] using hac.symm
        have hcv : c ≠ v := by intro h; subst v; exact hbv hbc
        have huvne : u ≠ v := huv.ne
        simp [List.nodup_cons, List.mem_cons, not_or] at ⊢
        tauto
      exact False.elim (no_four_vertex_path hfree c b u v
        hnodup hbc.symm hbu huv)
    · have hnodup : [a, b, u, v].Nodup := by
        have hab : a ≠ b := hba.ne'
        have hau : a ≠ u := Ne.symm hua
        have hav : a ≠ v := by intro h; subst v; exact hbv hba
        have huvne : u ≠ v := huv.ne
        simp [List.nodup_cons, List.mem_cons, not_or] at ⊢
        tauto
      exact False.elim (no_four_vertex_path hfree a b u v
        hnodup hba.symm hbu huv)
  have hS : S = Set.univ := connected_closed_set_eq_univ hconn b hbS hclosed
  intro v hvb
  have hvS : v ∈ S := by rw [hS]; trivial
  rcases hvS with hv | hv
  · exact False.elim (hvb hv)
  · exact hv

/-- The connected `P₄`-free case is a spanning star and has fewer edges
than vertices. The hypothesis `4 ≤ n` excludes a standalone triangle. -/
theorem connected_path_four_free_edge_count {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hconn : G.Connected)
    (hfree : (pathGraph 4).Free G) :
    G.edgeFinset.card + 1 = n := by
  classical
  obtain ⟨b, a, c, hac, hba, hbc⟩ :=
    connected_exists_two_neighbors (by omega : 3 ≤ n) G hconn
  have huni := universal_of_two_neighbors hconn hfree b a c hac hba hbc
  have hex (u v : Fin n) : ∃ t : Fin n, t ≠ b ∧ t ≠ u ∧ t ≠ v := by
    have hcard : ({b, u, v} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    by_contra h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {b, u, v} := by
      intro t _
      by_contra ht
      exact h ⟨t, by simpa using ht⟩
    have hshort : n ≤ 3 := by
      simpa using (Finset.card_le_card hsub).trans hcard
    omega
  have hle : G ≤ starGraph b := by
    intro u v huv
    by_cases hub : u = b
    · exact starGraph_adj.mpr ⟨huv.ne, Or.inl hub⟩
    by_cases hvb : v = b
    · exact starGraph_adj.mpr ⟨huv.ne, Or.inr hvb⟩
    obtain ⟨t, htb, htu, htv⟩ := hex u v
    have hnodup : [t, b, u, v].Nodup := by
      have hbu : b ≠ u := Ne.symm hub
      have hbv : b ≠ v := Ne.symm hvb
      have huvne : u ≠ v := huv.ne
      simp [List.nodup_cons, List.mem_cons, not_or] at ⊢
      tauto
    exact False.elim (no_four_vertex_path hfree t b u v hnodup
      (huni t htb).symm (huni u hub) huv)
  have hstar : G = starGraph b := by
    apply le_antisymm hle
    intro u v huv
    rcases starGraph_adj.mp huv with ⟨hne, hub | hvb⟩
    · subst u
      exact huni v hne.symm
    · subst v
      exact (huni u hne).symm
  have hcard_eq : G.edgeFinset.card = (starGraph b).edgeFinset.card := by
    exact congrArg Finset.card (edgeFinset_inj.mpr hstar)
  calc
    G.edgeFinset.card + 1 = (starGraph b).edgeFinset.card + 1 := by rw [hcard_eq]
    _ = n := by simpa using (isTree_starGraph b).card_edgeFinset

theorem connected_path_four_free_edge_le {n : ℕ} (hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hconn : G.Connected)
    (hfree : (pathGraph 4).Free G) :
    G.edgeFinset.card ≤ n := by
  have h := connected_path_four_free_edge_count (by omega : 4 ≤ n) G hconn hfree
  omega

end ErdosProblems.AntiRamseyPathFourFree
