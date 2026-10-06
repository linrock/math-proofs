module

public import CycleHeadNewDominance
public import CyclePathOre

@[expose] public section

/-!
forced terminal NEW witness for Choi Claim 2's inward path tail. Ore's local deficit and the named original-host outside
NEW witness are reused without changing the arbitrary NewChoice.
-/

namespace ErdosProblems.AntiRamseyCycleForcedTailWitness

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Head domination, the component-local Ore deficit and the endpoint NEW
sum force a selected edge leaving the path at its prescribed terminal
endpoint. Its literal original-host color is NEW at that endpoint.
The inward terminal path-edge premise must be supplied by the first path
extension in the eventual component argument. -/
theorem exists_terminal_newColor_edge_outside_inward_path
    {m : ℕ} (hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (m + 2), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (m + 2)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (m + 2), f i ∈ D)
    (hpair : m + 2 ≤ (newColors χ (p 0)).card +
      (newColors χ (p (Fin.last (m + 1)))).card) :
    ∃ w : Fin n, ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
      w ∉ Finset.univ.image p ∧
      (selectedGraph χ r).Adj (p (Fin.last (m + 1))) w ∧
      e.val = s(p (Fin.last (m + 1)), w) ∧
      χ e ∈ newColors χ (p (Fin.last (m + 1))) := by
  classical
  have hordered : ∀ a b : Fin (m + 2), a.val + 1 = b.val →
      (selectedGraph χ r).Adj (p a) (p b) := by
    intro a b hab
    have ha : a.val < m + 1 := by
      have hb := b.isLt
      omega
    let i : Fin (m + 1) := ⟨a.val, ha⟩
    have hcast : Fin.castSucc i = a := Fin.ext rfl
    have hsucc : Fin.succ i = b := Fin.ext hab
    simpa only [hcast, hsucc] using hpath i
  have hhead :=
    ErdosProblems.AntiRamseyCycleHeadNewDominance.no_head_new_deficit_of_inward_tail
      hm χ r p hp hpath hnewLast hno
  have hdeficit :=
    ErdosProblems.AntiRamseyCyclePathOre.ordered_path_endpoint_deficit_of_component
      (s := m + 1) (by omega) (selectedGraph χ r) p hp hordered D hpD hnoD
  have hsmall :
      ((selectedGraph χ r).neighborFinset (p (Fin.last (m + 1))) ∩
        Finset.univ.image p).card <
      (newColors χ (p (Fin.last (m + 1)))).card := by
    omega
  exact
    ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness.exists_selected_newColor_edge_outside
      χ r (p (Fin.last (m + 1))) (Finset.univ.image p) hsmall

end ErdosProblems.AntiRamseyCycleForcedTailWitness
