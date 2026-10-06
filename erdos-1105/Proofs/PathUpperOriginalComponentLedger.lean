module

public import PathUpperOriginalResidualPieceSequence
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
The actual whole roots of the checked SAME-final-full-R
greedy sequence enumerate the actual selected-graph connected components once. Derive their count and total vertex size; no desired count, coverage or
partition is a public existence premise. This is the first global ledger
step, not a global union-of-cuts or retained-edge ledger.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- Both
no-duplication and completeness are derived from the greedy certificate. -/
theorem residualGreedySequence_component_inventory
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R ∅ Set.univ roots) :
    (roots.map (fun x => (selectedGraph χ R).connectedComponentMk x)).Nodup ∧
    (∀ C : (selectedGraph χ R).ConnectedComponent,
      C ∈ roots.map (fun x => (selectedGraph χ R).connectedComponentMk x)) := by
  have hpair := residualGreedySequence_pairwise_disjoint
    χ R ∅ Set.univ roots hsequence
  have hcover := residualGreedySequence_covers χ R ∅ Set.univ roots hsequence
  constructor
  · change (roots.map (fun x => (selectedGraph χ R).connectedComponentMk x)).Pairwise
      (fun C D => C ≠ D)
    apply List.pairwise_map.mpr
    apply hpair.imp
    intro x y hdisjoint hxy
    have hx : x ∈ componentSupport χ R x := by
      change (selectedGraph χ R).connectedComponentMk x =
        (selectedGraph χ R).connectedComponentMk x
      rfl
    have hy : x ∈ componentSupport χ R y := by
      change (selectedGraph χ R).connectedComponentMk x =
        (selectedGraph χ R).connectedComponentMk y
      exact hxy
    exact (Set.disjoint_left.mp hdisjoint) hx hy
  · intro C
    obtain ⟨v, hv⟩ := C.nonempty_supp
    obtain ⟨x, hx, hvx⟩ := (hcover v).mp (Set.mem_univ v)
    have hvC : (selectedGraph χ R).connectedComponentMk v = C := hv
    have hvX : (selectedGraph χ R).connectedComponentMk v =
        (selectedGraph χ R).connectedComponentMk x := hvx
    exact List.mem_map.mpr ⟨x, hx, hvX.symm.trans hvC⟩

/-- This includes n=0, where both quantities are zero. -/
theorem residualGreedySequence_root_count
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R ∅ Set.univ roots) :
    roots.length = Nat.card (selectedGraph χ R).ConnectedComponent := by
  classical
  let G := selectedGraph χ R
  let L := roots.map (fun x => G.connectedComponentMk x)
  obtain ⟨hnodup, hcomplete⟩ :=
    residualGreedySequence_component_inventory χ R roots hsequence
  have huniv : L.toFinset = (Finset.univ : Finset G.ConnectedComponent) := by
    ext C
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcomplete C
  calc
    roots.length = L.length := by simp only [L, List.length_map]
    _ = L.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ = Fintype.card G.ConnectedComponent := by rw [huniv, Finset.card_univ]
    _ = Nat.card G.ConnectedComponent := Nat.card_eq_fintype_card.symm

/-- Sum the sizes of the ACTUAL whole selected components
at the derived roots. Isolates contribute one; the empty carrier contributes
the empty sum. The generic component vertex theorem is reused unchanged. -/
theorem residualGreedySequence_whole_component_size_sum
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (roots : List (Fin n))
    (hsequence : ResidualGreedySequence χ R ∅ Set.univ roots) :
    (roots.map (fun x => Nat.card (componentSupport χ R x))).sum = n := by
  classical
  let G := selectedGraph χ R
  let L := roots.map (fun x => G.connectedComponentMk x)
  obtain ⟨hnodup, hcomplete⟩ :=
    residualGreedySequence_component_inventory χ R roots hsequence
  have huniv : L.toFinset = (Finset.univ : Finset G.ConnectedComponent) := by
    ext C
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcomplete C
  have hlist : (L.map (fun C : G.ConnectedComponent => Nat.card C.supp)).sum =
      ∑ C : G.ConnectedComponent, Nat.card C.supp := by
    rw [← List.sum_toFinset (fun C : G.ConnectedComponent => Nat.card C.supp) hnodup]
    rw [huniv]
  have hvertex : (∑ C : G.ConnectedComponent, Nat.card C.supp) = n := by
    have h :=
      ErdosProblems.AntiRamseyPathFiveComponents.vertex_card_eq_sum_component_card G
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h.symm
  have htotal := hlist.trans hvertex
  simpa only [L, G, List.map_map, Function.comp_def, componentSupport] using htotal

/-- Public original existence starts only from chi and a
valid full original r. Derive one final full R, enriched actual stage sequence,
actual original component count and whole-component vertex ledger, keeping
the original coverage/disjointness statements unchanged. -/
theorem exists_full_original_component_ledger
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    ∃ (R : RepresentativeChoice χ) (roots : List (Fin n)),
      ResidualGreedySequence χ R ∅ Set.univ roots ∧
      OriginalResidualPieceSequence χ R ∅ Set.univ roots ∧
      roots.length = Nat.card (selectedGraph χ R).ConnectedComponent ∧
      (roots.map (fun x => Nat.card (componentSupport χ R x))).sum = n ∧
      (∀ v, ∃ x ∈ roots, v ∈ componentSupport χ R x) ∧
      roots.Pairwise (fun x y =>
        Disjoint (componentSupport χ R x) (componentSupport χ R y)) := by
  obtain ⟨R, roots, hsequence, hpieces, hcover, hdisjoint⟩ :=
    exists_full_original_residual_piece_sequence χ r
  exact ⟨R, roots, hsequence, hpieces,
    residualGreedySequence_root_count χ R roots hsequence,
    residualGreedySequence_whole_component_size_sum χ R roots hsequence,
    hcover, hdisjoint⟩

end ErdosProblems.PathUpperReduction
