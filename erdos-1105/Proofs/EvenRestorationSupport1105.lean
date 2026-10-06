module

public import CoreElimination
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Derive the actual small restoration carrier from all
original neighbors inside the enlarged current carrier. The retained anchor
consumes one of its d neighbors, leaving at most d-1 outside neighbors. Finset.exists_subsuperset_card_eq supplies the required support internally. No supplied favorable support, restricted degree, classification or ledger.
-/

namespace ErdosProblems.PathUpperReduction.EvenRestorationSupport1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination

/-- Internally select d-1 actual later outsiders containing ALL original
outside neighbors of x. Together with the original core and x they form an
actual carrier of size 2d+3 retaining x's exact original degree d.
No clique, cycle-freedom, old classification or edge ledger is assumed. -/
theorem exists_actual_restoration_support {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) (S T : Finset V) (x a : V)
    (hd : 2 ≤ d) (hST : S ⊆ T) (hScard : S.card = d + 3)
    (houtside : letI : DecidableEq V := Classical.decEq V
      d ≤ (T \ S).card)
    (hx : x ∉ T) (ha : a ∈ S) (hxa : G.Adj x a)
    (hdegree : letI : DecidableEq V := Classical.decEq V
      withinDegree G (insert x T) x = d) :
    letI : DecidableEq V := Classical.decEq V
    ∃ L : Finset V, L ⊆ T \ S ∧ L.card = d - 1 ∧
      (∀ y ∈ T \ S, G.Adj x y → y ∈ L) ∧
      (∀ y ∈ insert x T, G.Adj x y → y ∈ insert x (S ∪ L)) ∧
      (insert x (S ∪ L)).card = 2 * d + 3 ∧
      withinDegree G (insert x (S ∪ L)) x = d := by
  classical
  let O := T \ S
  let R := O.filter (fun y => G.Adj x y)
  let N := (insert x T).filter (fun y => G.Adj x y)
  have hOcard : d ≤ O.card := houtside
  have hRO : R ⊆ O := Finset.filter_subset _ _
  have haR : a ∉ R := by
    intro haR
    have haO : a ∈ O := (Finset.mem_filter.mp haR).1
    exact (Finset.mem_sdiff.mp haO).2 ha
  have hsub : insert a R ⊆ N := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hya | hyR
    · subst y
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (hST ha), hxa⟩
    · obtain ⟨hyO, hxy⟩ := Finset.mem_filter.mp hyR
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mp hyO).1, hxy⟩
  have hNcard : N.card = d := by
    change ((insert x T).filter (fun y => G.Adj x y)).card = d at hdegree
    exact hdegree
  have hRcard : R.card ≤ d - 1 := by
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem haR, hNcard] at hcard
    omega
  obtain ⟨L, hRL, hLO, hLcard⟩ :=
    Finset.exists_subsuperset_card_eq hRO hRcard (by omega : d - 1 ≤ O.card)
  have hLT : L ⊆ T := by
    intro y hyL
    exact (Finset.mem_sdiff.mp (hLO hyL)).1
  have hSL : Disjoint S L := by
    apply Finset.disjoint_left.mpr
    intro y hyS hyL
    exact (Finset.mem_sdiff.mp (hLO hyL)).2 hyS
  have hxSL : x ∉ S ∪ L := by
    intro hxSL
    rcases Finset.mem_union.mp hxSL with hxS | hxL
    · exact hx (hST hxS)
    · exact hx (hLT hxL)
  let W := insert x (S ∪ L)
  have hWsub : W ⊆ insert x T := by
    intro y hyW
    rcases Finset.mem_insert.mp hyW with hyx | hySL
    · exact Finset.mem_insert.mpr (Or.inl hyx)
    · rcases Finset.mem_union.mp hySL with hyS | hyL
      · exact Finset.mem_insert_of_mem (hST hyS)
      · exact Finset.mem_insert_of_mem (hLT hyL)
  have hretain : ∀ y ∈ insert x T, G.Adj x y → y ∈ W := by
    intro y hy hxy
    have hyT : y ∈ T := by
      rcases Finset.mem_insert.mp hy with hyx | hyT
      · exact False.elim (G.ne_of_adj hxy hyx.symm)
      · exact hyT
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union.mpr
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · apply Or.inr
      apply hRL
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hyT, hyS⟩, hxy⟩
  have hWcard : W.card = 2 * d + 3 := by
    dsimp only [W]
    rw [Finset.card_insert_of_notMem hxSL, Finset.card_union_of_disjoint hSL,
      hScard, hLcard]
    omega
  have hfilter : (insert x T).filter (fun y => G.Adj x y) =
      W.filter (fun y => G.Adj x y) := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨hyT, hxy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hretain y hyT hxy, hxy⟩
    · intro y hy
      obtain ⟨hyW, hxy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hWsub hyW, hxy⟩
  have hWdegree : withinDegree G W x = d := by
    change (W.filter (fun y => G.Adj x y)).card = d
    rw [← hfilter]
    exact hNcard
  refine ⟨L, hLO, hLcard, ?_, hretain, hWcard, hWdegree⟩
  intro y hyO hxy
  exact hRL (Finset.mem_filter.mpr ⟨hyO, hxy⟩)

end ErdosProblems.PathUpperReduction.EvenRestorationSupport1105
