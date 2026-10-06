module

public import PathFiveP4Obstruction
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
Edge counting for the connected `P₅` extremal problem, bounding the total edge
count of a graph consisting of a core `C` with at most `|C|` internal edges and
pendant leaves outside `C`.
-/

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- If the edges inside a finite core number at most its vertices and every
outside vertex is a leaf attached to the core, then the entire graph has at
most one edge per vertex. -/
theorem edge_count_of_core_and_leaves {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hcore : (G.edgeFinset.filter fun e => e.toFinset ⊆ C).card ≤ C.card)
    (hleaf : ∀ v : V, v ∉ C →
      ∃ z : V, z ∈ C ∧ G.Adj v z ∧ ∀ w : V, G.Adj v w → w = z) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  let Ecore : Finset (Sym2 V) := G.edgeFinset.filter fun e => e.toFinset ⊆ C
  let Eout : Finset (Sym2 V) := G.edgeFinset.filter fun e => ¬e.toFinset ⊆ C
  let O := {v : V // v ∉ C}
  let leafEdge : O → Sym2 V := fun v => s(v.1, Classical.choose (hleaf v.1 v.2))
  have hcover : Eout ⊆ (Finset.univ : Finset O).image leafEdge := by
    intro e he
    have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    have heOutside : ¬e.toFinset ⊆ C := (Finset.mem_filter.mp he).2
    induction e using Sym2.inductionOn with
    | hf u w =>
      have hadj : G.Adj u w := by
        simpa only [G.mem_edgeFinset, G.mem_edgeSet] using heG
      have hout : u ∉ C ∨ w ∉ C := by
        by_contra h
        have hmem : u ∈ C ∧ w ∈ C := by tauto
        apply heOutside
        intro y hy
        have hyuw : y = u ∨ y = w := by simpa [Sym2.toFinset_mk_eq] using hy
        rcases hyuw with rfl | rfl
        · exact hmem.1
        · exact hmem.2
      rcases hout with hu | hw
      · refine Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, ?_⟩
        have huniq := (Classical.choose_spec (hleaf u hu)).2.2
        have hwu := huniq w hadj
        simp [leafEdge, hwu]
      · refine Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, ?_⟩
        have huniq := (Classical.choose_spec (hleaf w hw)).2.2
        have huw := huniq u hadj.symm
        simp [leafEdge, huw, Sym2.eq_swap]
  have hOcard : (Finset.univ : Finset O).card = (Finset.univ \ C).card := by
    simp [O, Fintype.card_subtype, Finset.sdiff_eq_filter]
  have houtCard : Eout.card ≤ (Finset.univ \ C).card := by
    calc
      Eout.card ≤ ((Finset.univ : Finset O).image leafEdge).card :=
        Finset.card_le_card hcover
      _ ≤ (Finset.univ : Finset O).card := Finset.card_image_le
      _ = (Finset.univ \ C).card := hOcard
  have hsplit : Ecore.card + Eout.card = G.edgeFinset.card := by
    simpa [Ecore, Eout] using
      (Finset.card_filter_add_card_filter_not (s := G.edgeFinset)
        (p := fun e : Sym2 V => e.toFinset ⊆ C))
  calc
    G.edgeFinset.card = Ecore.card + Eout.card := hsplit.symm
    _ ≤ C.card + (Finset.univ \ C).card := Nat.add_le_add hcore houtCard
    _ = Fintype.card V := by
      simpa [add_comm] using
        (Finset.card_sdiff_add_card_eq_card (s := C) (t := Finset.univ)
          (Finset.subset_univ C))

end ErdosProblems.AntiRamseyPathFiveExtremal
