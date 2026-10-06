module

public import PathFiveP4Obstruction
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
The four-vertex core of a connected `P₅`-free graph with a fifth attached
vertex has at most four edges.  This uses a symbolic six-edge classification.
-/

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- A non-diagonal edge with both endpoints in four named vertices is one of
the six possible unordered pairs. -/
theorem edge_in_four_vertices {V : Type*} [DecidableEq V]
    (a b c d : V) (e : Sym2 V)
    (he : e.toFinset ⊆ ({a, b, c, d} : Finset V))
    (hne : ¬e.IsDiag) :
    e = s(a, b) ∨ e = s(a, c) ∨ e = s(a, d) ∨
    e = s(b, c) ∨ e = s(b, d) ∨ e = s(c, d) := by
  induction e using Sym2.inductionOn with
  | hf u w =>
    have hu : u ∈ ({a, b, c, d} : Finset V) := he (by simp)
    have hw : w ∈ ({a, b, c, d} : Finset V) := he (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
    have huw : u ≠ w := by simpa [Sym2.mk_isDiag_iff] using hne
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hw with rfl | rfl | rfl | rfl <;>
      simp_all [Sym2.eq_swap]

/-- A fifth vertex attached to an interior point of a `P₄` forces the
four-vertex core to have at most four edges. -/
theorem p4_core_edges_le_four {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b c d x : V)
    (hfree : (pathGraph 5).Free G)
    (hpath : [a, b, c, d].Nodup)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hcenter : G.Adj x b ∨ G.Adj x c) :
    (G.edgeFinset.filter fun e => e.toFinset ⊆ ({a, b, c, d} : Finset V)).card ≤ 4 := by
  classical
  have hfive : [a, b, c, d, x].Nodup := by
    have hpair := hpath
    simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
    tauto
  have hchords := p4_external_vertex_forbids_chords
    hfree a b c d x hfive hab hbc hcd
  rcases hcenter with hxb | hxc
  · let allowed : Finset (Sym2 V) := {s(a, b), s(b, c), s(c, d), s(b, d)}
    have hsubset : (G.edgeFinset.filter fun e =>
        e.toFinset ⊆ ({a, b, c, d} : Finset V)) ⊆ allowed := by
      intro e he
      have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
      have hecore := (Finset.mem_filter.mp he).2
      have hcase := edge_in_four_vertices a b c d e hecore
        (G.not_isDiag_of_mem_edgeFinset heG)
      rcases hcase with h₁ | h₂ | h₃ | h₄ | h₅ | h₆
      · simp [allowed, h₁]
      · have hac : G.Adj a c := by
          simpa only [h₂, G.mem_edgeFinset, G.mem_edgeSet] using heG
        exact False.elim ((hchords.1 hxb) hac)
      · have had : G.Adj a d := by
          simpa only [h₃, G.mem_edgeFinset, G.mem_edgeSet] using heG
        exact False.elim ((hchords.2.2 (Or.inl hxb)) had)
      · simp [allowed, h₄]
      · simp [allowed, h₅]
      · simp [allowed, h₆]
    calc
      _ ≤ allowed.card := Finset.card_le_card hsubset
      _ ≤ 4 := Finset.card_le_four
  · let allowed : Finset (Sym2 V) := {s(a, b), s(b, c), s(c, d), s(a, c)}
    have hsubset : (G.edgeFinset.filter fun e =>
        e.toFinset ⊆ ({a, b, c, d} : Finset V)) ⊆ allowed := by
      intro e he
      have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
      have hecore := (Finset.mem_filter.mp he).2
      have hcase := edge_in_four_vertices a b c d e hecore
        (G.not_isDiag_of_mem_edgeFinset heG)
      rcases hcase with h₁ | h₂ | h₃ | h₄ | h₅ | h₆
      · simp [allowed, h₁]
      · simp [allowed, h₂]
      · have had : G.Adj a d := by
          simpa only [h₃, G.mem_edgeFinset, G.mem_edgeSet] using heG
        exact False.elim ((hchords.2.2 (Or.inr hxc)) had)
      · simp [allowed, h₄]
      · have hbd : G.Adj b d := by
          simpa only [h₅, G.mem_edgeFinset, G.mem_edgeSet] using heG
        exact False.elim ((hchords.2.1 hxc) hbd)
      · simp [allowed, h₆]
    calc
      _ ≤ allowed.card := Finset.card_le_card hsubset
      _ ≤ 4 := Finset.card_le_four

end ErdosProblems.AntiRamseyPathFiveExtremal
