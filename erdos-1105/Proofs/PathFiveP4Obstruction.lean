module

public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
Structural consequences of `P₅`-freeness for a four-vertex path.  The
connected extremal bound `e(G) ≤ |V(G)|` is a separate target.
-/

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- A nonempty vertex set closed under adjacency is the entire vertex set of
a connected graph. -/
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

/-- Five distinct vertices joined consecutively form a forbidden `P₅` copy. -/
theorem no_five_vertex_path {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (a b c d e : V)
    (hne : [a, b, c, d, e].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hde : G.Adj d e) : False := by
  let p : G.Walk a e := .cons hab (.cons hbc (.cons hcd (.cons hde .nil)))
  have hp : p.IsPath := by
    simpa [p, Walk.isPath_def] using hne
  have hcopy : (pathGraph 5) ⊑ G := by
    simpa [p] using hp.isContained_pathGraph
  exact hfree hcopy

/-- In a `P₅`-free graph, a fifth vertex cannot join either endpoint of a
four-vertex path, or both of its two interior vertices. -/
theorem p4_external_vertex_restrictions {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (a b c d v : V)
    (hne : [a, b, c, d, v].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    ¬ G.Adj v a ∧ ¬ G.Adj v d ∧ ¬ (G.Adj v b ∧ G.Adj v c) := by
  have hperm₁ : [v, a, b, c, d].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  have hperm₂ : [a, b, c, d, v].Nodup := hne
  have hperm₃ : [a, b, v, c, d].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  refine ⟨?_, ?_, ?_⟩
  · intro hva
    exact no_five_vertex_path hfree v a b c d hperm₁ hva hab hbc hcd
  · intro hvd
    exact no_five_vertex_path hfree a b c d v hperm₂ hab hbc hcd hvd.symm
  · rintro ⟨hvb, hvc⟩
    exact no_five_vertex_path hfree a b v c d hperm₃ hab hvb.symm hvc hcd

/-- An external vertex joined to either interior vertex of a four-vertex path
cannot have an edge to a second external vertex in a `P₅`-free graph. -/
theorem p4_external_neighbor_has_no_external_edge {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (a b c d v w : V)
    (hne : [a, b, c, d, v, w].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hcenter : G.Adj v b ∨ G.Adj v c) : ¬ G.Adj v w := by
  intro hvw
  rcases hcenter with hvb | hvc
  · have hperm : [w, v, b, c, d].Nodup := by
      have hpair := hne
      simp [List.nodup_cons, List.mem_cons, not_or, eq_comm] at hpair ⊢
      tauto
    exact no_five_vertex_path hfree w v b c d hperm hvw.symm hvb hbc hcd
  · have hperm : [w, v, c, b, a].Nodup := by
      have hpair := hne
      simp [List.nodup_cons, List.mem_cons, not_or, eq_comm] at hpair ⊢
      tauto
    exact no_five_vertex_path hfree w v c b a hperm hvw.symm hvc hbc.symm hab.symm

/-- An external vertex adjacent to an interior point rules out the chord
between the path endpoints.  If it joins `b`, it also rules out `a-c`; if it
joins `c`, it rules out `b-d`. -/
theorem p4_external_vertex_forbids_chords {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (a b c d v : V)
    (hne : [a, b, c, d, v].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    (G.Adj v b → ¬ G.Adj a c) ∧
    (G.Adj v c → ¬ G.Adj b d) ∧
    ((G.Adj v b ∨ G.Adj v c) → ¬ G.Adj a d) := by
  have hperm₁ : [v, b, a, c, d].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  have hperm₂ : [v, c, d, b, a].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  have hperm₃ : [v, b, c, d, a].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  have hperm₄ : [v, c, d, a, b].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  refine ⟨?_, ?_, ?_⟩
  · intro hvb hac
    exact no_five_vertex_path hfree v b a c d hperm₁ hvb hab.symm hac hcd
  · intro hvc hbd
    exact no_five_vertex_path hfree v c d b a hperm₂ hvc hcd hbd.symm hab.symm
  · intro hcenter had
    rcases hcenter with hvb | hvc
    · exact no_five_vertex_path hfree v b c d a hperm₃ hvb hbc hcd had.symm
    · exact no_five_vertex_path hfree v c d a b hperm₄ hvc hcd had.symm hab

set_option maxHeartbeats 800000

/-- In a connected `P₅`-free graph, every vertex outside a fixed four-vertex
path is directly adjacent to exactly one of its two interior vertices.
The uniqueness uses `p4_external_vertex_restrictions`. -/
theorem p4_external_vertex_attached_to_center {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (hconn : G.Connected)
    (a b c d v : V) (hpath : [a, b, c, d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d) :
    G.Adj v b ∨ G.Adj v c := by
  let S : Set V := {x | x = a ∨ x = b ∨ x = c ∨ x = d ∨ G.Adj b x ∨ G.Adj c x}
  have hS : S = Set.univ := by
    apply connected_closed_set_eq_univ hconn a (show a ∈ S by simp [S])
    intro u hu w huw
    change u = a ∨ u = b ∨ u = c ∨ u = d ∨ G.Adj b u ∨ G.Adj c u at hu
    change w = a ∨ w = b ∨ w = c ∨ w = d ∨ G.Adj b w ∨ G.Adj c w
    by_cases hwcore : w = a ∨ w = b ∨ w = c ∨ w = d
    · tauto
    have hne_w : [a, b, c, d, w].Nodup := by
      have hpair := hpath
      simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
      tauto
    by_cases hucore : u = a ∨ u = b ∨ u = c ∨ u = d
    · rcases hucore with ha | hb | hc | hd
      · have hwa : G.Adj w a := by simpa [ha] using huw.symm
        exact False.elim ((p4_external_vertex_restrictions hfree a b c d w
          hne_w hab hbc hcd).1 hwa)
      · have hbw : G.Adj b w := by simpa [hb] using huw
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbw))))
      · have hcw : G.Adj c w := by simpa [hc] using huw
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcw))))
      · have hwd : G.Adj w d := by simpa [hd] using huw.symm
        exact False.elim ((p4_external_vertex_restrictions hfree a b c d w
          hne_w hab hbc hcd).2.1 hwd)
    have hcenter : G.Adj u b ∨ G.Adj u c := by
      rcases hu with ha | hb | hc | hd | hub | huc
      · exact False.elim (hucore (Or.inl ha))
      · exact False.elim (hucore (Or.inr (Or.inl hb)))
      · exact False.elim (hucore (Or.inr (Or.inr (Or.inl hc))))
      · exact False.elim (hucore (Or.inr (Or.inr (Or.inr hd))))
      · exact Or.inl hub.symm
      · exact Or.inr huc.symm
    have hne_uw : [a, b, c, d, u, w].Nodup := by
      have hpair := hpath
      have hneq := huw.ne
      simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
      tauto
    exact False.elim ((p4_external_neighbor_has_no_external_edge hfree
      a b c d u w hne_uw hab hbc hcd hcenter) huw)
  have hvS : v ∈ S := by rw [hS]; trivial
  change v = a ∨ v = b ∨ v = c ∨ v = d ∨ G.Adj b v ∨ G.Adj c v at hvS
  rcases hvS with ha | hb | hc | hd | hbv | hcv
  · exact False.elim (hv.1 ha)
  · exact False.elim (hv.2.1 hb)
  · exact False.elim (hv.2.2.1 hc)
  · exact False.elim (hv.2.2.2 hd)
  · exact Or.inl hbv.symm
  · exact Or.inr hcv.symm

/-- Every vertex outside a four-vertex path in a connected `P₅`-free graph
has exactly one neighbor, namely one of the two path interior vertices. -/
theorem p4_external_vertex_is_leaf {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (hconn : G.Connected)
    (a b c d v : V) (hpath : [a, b, c, d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d) :
    ∃ z : V, (z = b ∨ z = c) ∧ G.Adj v z ∧ ∀ w, G.Adj v w → w = z := by
  have hfive : [a, b, c, d, v].Nodup := by
    have hpair := hpath
    simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
    tauto
  have hrestr := p4_external_vertex_restrictions hfree a b c d v hfive hab hbc hcd
  have hcenter := p4_external_vertex_attached_to_center
    hfree hconn a b c d v hpath hab hbc hcd hv
  have honly : ∀ w, G.Adj v w → w = b ∨ w = c := by
    intro w hvw
    by_cases hwcore : w = a ∨ w = b ∨ w = c ∨ w = d
    · rcases hwcore with ha | hb | hc | hd
      · have hva : G.Adj v a := by simpa [ha] using hvw
        exact False.elim (hrestr.1 hva)
      · exact Or.inl hb
      · exact Or.inr hc
      · have hvd : G.Adj v d := by simpa [hd] using hvw
        exact False.elim (hrestr.2.1 hvd)
    have hne_uw : [a, b, c, d, v, w].Nodup := by
      have hpair := hpath
      have hneq := hvw.ne
      simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
      tauto
    exact False.elim ((p4_external_neighbor_has_no_external_edge hfree
      a b c d v w hne_uw hab hbc hcd hcenter) hvw)
  rcases hcenter with hvb | hvc
  · refine ⟨b, Or.inl rfl, hvb, ?_⟩
    intro w hvw
    rcases honly w hvw with hb | hc
    · exact hb
    · have hvc : G.Adj v c := by simpa [hc] using hvw
      exact False.elim (hrestr.2.2 ⟨hvb, hvc⟩)
  · refine ⟨c, Or.inr rfl, hvc, ?_⟩
    intro w hvw
    rcases honly w hvw with hb | hc
    · have hvb : G.Adj v b := by simpa [hb] using hvw
      exact False.elim (hrestr.2.2 ⟨hvb, hvc⟩)
    · exact hc

end ErdosProblems.AntiRamseyPathFiveExtremal
