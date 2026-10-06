module

public import CyclePathOre
public import CycleNewChoiceOutsideWitnessV2

@[expose] public section

/-! first endpoint-extension interface for Choi Claim 2. The checked Ore deficit and arbitrary-choice outside NEW witness are reused. Selected cycle absence is local to D; no ordering or rotation is constructed. -/

namespace ErdosProblems.AntiRamseyCyclePathEndpointExtension

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Some endpoint of a locally shorter-cycle-free selected path has an
outside selected edge whose color is NEW at that exact path endpoint.
The specified finite D preserves the component-local Ore interface.
No selected-cycle exclusion elsewhere or terminal inward NEW is assumed. -/
theorem exists_endpoint_newColor_edge_outside_path
    {t : ℕ} (ht : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ a b : Fin (t + 1), a.val + 1 = b.val →
      (selectedGraph χ r).Adj (p a) (p b))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (t + 1), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (t + 1)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (t + 1), f i ∈ D)
    (hpair : t + 1 ≤
      (newColors χ (p 0)).card + (newColors χ (p (Fin.last t))).card) :
    (∃ w : Fin n, ∃ e : HostEdge n,
      w ∉ Finset.univ.image p ∧ (selectedGraph χ r).Adj (p 0) w ∧
      e.val = s(p 0, w) ∧ χ e ∈ newColors χ (p 0)) ∨
    (∃ w : Fin n, ∃ e : HostEdge n,
      w ∉ Finset.univ.image p ∧
      (selectedGraph χ r).Adj (p (Fin.last t)) w ∧
      e.val = s(p (Fin.last t), w) ∧
      χ e ∈ newColors χ (p (Fin.last t))) := by
  classical
  let P : Finset (Fin n) := Finset.univ.image p
  have hdeficit :=
    ErdosProblems.AntiRamseyCyclePathOre.ordered_path_endpoint_deficit_of_component
      ht (selectedGraph χ r) p hp hpath D hpD hnoD
  change ((selectedGraph χ r).neighborFinset (p 0) ∩ P).card +
    ((selectedGraph χ r).neighborFinset (p (Fin.last t)) ∩ P).card <
      t + 1 at hdeficit
  by_cases hleft :
      ((selectedGraph χ r).neighborFinset (p 0) ∩ P).card <
        (newColors χ (p 0)).card
  · left
    exact
      ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness.exists_selected_newColor_edge_outside
        χ r (p 0) P hleft
  · right
    have hright :
        ((selectedGraph χ r).neighborFinset (p (Fin.last t)) ∩ P).card <
          (newColors χ (p (Fin.last t))).card := by
      omega
    exact
      ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness.exists_selected_newColor_edge_outside
        χ r (p (Fin.last t)) P hright

end ErdosProblems.AntiRamseyCyclePathEndpointExtension

