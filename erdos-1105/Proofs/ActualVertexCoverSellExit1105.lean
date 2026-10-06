module

public import UniformSellContainerTransfer1105
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Nat.Choose.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
The spanning equivalence is constructed here from the actual cover
and its full complement. No clique, favorable owner, supplied partition,
connectivity, induction or rainbow-freedom assumption is added.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction.ActualVertexCoverSellExit1105

/-- An actual d-vertex cover and a palette above the literal even linear
branch force a rainbow P_(2*d+2) in the original complete-host coloring.
All selected edges and their arbitrary original owners are unchanged. -/
theorem rainbow_path_of_actual_vertex_cover {d n q : ℕ}
    (hd : 2 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (X : Finset (Fin n)) (hX : X.card = d)
    (hcover : ∀ u v : Fin n, (selectedGraph χ r).Adj u v → u ∈ X ∨ v ∈ X)
    (hq : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 < q) :
    ∃ p : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
  classical
  let S : Set (Fin n) := ↑X
  have hS : Fintype.card S = d := by
    exact (Fintype.card_of_finset' (p := S) X (fun _ => Iff.rfl)).trans hX
  have hSc : Fintype.card (Sᶜ : Set (Fin n)) = n - d := by
    rw [Fintype.card_compl_set, Fintype.card_fin, hS]
  let eL : Fin d ≃ S := (Finset.equivFinOfCardEq (s := X) hX).symm
  let eR : Fin (n - d) ≃ (Sᶜ : Set (Fin n)) :=
    (Fintype.equivFinOfCardEq hSc).symm
  let f : (Fin d ⊕ Fin (n - d)) ≃ Fin n :=
    (Equiv.sumCongr eL eR).trans (Equiv.Set.sumCompl S)
  have hright (j : Fin (n - d)) : f (Sum.inr j) ∉ X := by
    change (eR j).val ∉ X
    exact (eR j).property
  have hYY : ∀ j j' : Fin (n - d),
      ¬ (selectedGraph χ r).Adj (f (Sum.inr j)) (f (Sum.inr j')) := by
    intro j j' hjj'
    rcases hcover _ _ hjj' with hx | hx
    · exact hright j hx
    · exact hright j' hx
  have hdt : d + 2 ≤ n - d := by omega
  have hpred : d - 1 + 1 = d := by omega
  have hchoose : d.choose 2 = (d - 1) + (d - 1).choose 2 := by
    simpa only [hpred, Nat.choose_one_right] using
      (Nat.choose_succ_succ' (d - 1) 1)
  have hthreshold : d.choose 2 + (d - 1) * (n - d) + 2 =
      (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 := by
    rw [hchoose]
    ring
  apply ErdosProblems.UniformSellContainerCount1105.rainbow_path_of_spanning_sell_container
    hd hdt χ r f hYY
  rwa [hthreshold]

end ErdosProblems.PathUpperReduction.ActualVertexCoverSellExit1105
