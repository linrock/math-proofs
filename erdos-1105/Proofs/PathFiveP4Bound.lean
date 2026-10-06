module

public import PathFiveCoreCount
public import PathFiveEdgeCount

@[expose] public section

/-!
The connected `P₅`-free edge bound in the case of a four-vertex path.
The complementary no-`P₄` case is developed separately.
-/

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- A connected `P₅`-free graph on at least five vertices has at most one
edge per vertex if it contains a four-vertex path. -/
theorem p4_connected_p5_free_edges_le_card {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 5 ≤ Fintype.card V)
    (hfree : (pathGraph 5).Free G) (hconn : G.Connected)
    (a b c d : V) (hpath : [a, b, c, d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  let C : Finset V := {a, b, c, d}
  have hCcard : C.card = 4 := by
    simpa [C, List.toFinset_cons] using
      (List.toFinset_card_of_nodup hpath)
  have hlt : C.card < (Finset.univ : Finset V).card := by
    simpa [hCcard] using
      (Nat.lt_of_lt_of_le (by decide : 4 < 5) hcard)
  obtain ⟨x, _, hxC⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := C) (t := Finset.univ) hlt
  have hx : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
    have hx' : ¬(x = a ∨ x = b ∨ x = c ∨ x = d) := by
      simpa [C] using hxC
    tauto
  have hcenter : G.Adj x b ∨ G.Adj x c :=
    p4_external_vertex_attached_to_center
      hfree hconn a b c d x hpath hab hbc hcd hx
  have hcore :
      (G.edgeFinset.filter fun e => e.toFinset ⊆ C).card ≤ C.card := by
    change (G.edgeFinset.filter fun e =>
      e.toFinset ⊆ ({a, b, c, d} : Finset V)).card ≤ C.card
    rw [hCcard]
    exact p4_core_edges_le_four G a b c d x hfree hpath hx hab hbc hcd hcenter
  have hleaf : ∀ v : V, v ∉ C →
      ∃ z : V, z ∈ C ∧ G.Adj v z ∧ ∀ w : V, G.Adj v w → w = z := by
    intro v hvC
    have hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by
      have hv' : ¬(v = a ∨ v = b ∨ v = c ∨ v = d) := by
        simpa [C] using hvC
      tauto
    obtain ⟨z, hz, hvz, huniq⟩ :=
      p4_external_vertex_is_leaf hfree hconn a b c d v hpath hab hbc hcd hv
    refine ⟨z, ?_, hvz, huniq⟩
    rcases hz with rfl | rfl <;> simp [C]
  exact edge_count_of_core_and_leaves G C hcore hleaf

end ErdosProblems.AntiRamseyPathFiveExtremal
