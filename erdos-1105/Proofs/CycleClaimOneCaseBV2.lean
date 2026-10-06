module

public import CycleClaimOneCommonSpokes
public import CycleClaimOneSecondNewWitness
public import CycleClaimOneJInsertionV2

@[expose] public section

/-! Composition of Choi Claim 1 Case B. -/

namespace ErdosProblems.AntiRamseyCycleClaimOneCaseB

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion
open ErdosProblems.AntiRamseyCycleClaimOneCommonSpokes
open ErdosProblems.AntiRamseyCycleClaimOneSecondNewWitness
open ErdosProblems.AntiRamseyCycleClaimOneJInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Full local Case B positive conclusion. The first literal host spoke is
NEW at its outside endpoint, and at least two colors are NEW there. Neither
selected first attachment nor an initial spoke mismatch is assumed. -/
theorem positive_caseB_outside_new_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnewOutside : χ (outsiderEdge cyc u hu 0) ∈ newColors χ u)
    (hnewu : 2 ≤ (newColors χ u).card) :
    ∃ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  classical
  by_contra hnot
  have hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ := by
    intro f hf
    exact hnot ⟨f, hf⟩
  let α : C := χ (outsiderEdge cyc u hu 0)
  have hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α :=
    no_rainbow_outside_new_spokes_eq hm χ r cyc u hu hnewOutside hnone
  have hcommonHost : ∀ (i : Fin (m + 1)) (e : HostEdge n),
      e.val = s(u, cyc.toHom i) → χ e = α := by
    intro i e hepair
    have he : e = outsiderEdge cyc u hu i := Subtype.ext hepair
    rw [he]
    exact hcommon i
  obtain ⟨δ, hδnew, hδα, w, e, hselected, hwu, hw, hepair, hecolor⟩ :=
    exists_second_new_selected_edge_outside χ r cyc u α hnewu hcommonHost
  have huw : u ≠ w := hwu.symm
  have he : e = betweenEdge u w huw := Subtype.ext hepair
  have hbridge : χ (betweenEdge u w huw) = δ :=
    (congrArg χ he).symm.trans hecolor
  have hbridgeNew : χ (betweenEdge u w huw) ∈ newColors χ u := by
    rw [hbridge]
    exact hδnew
  have hbridgeNe : χ (betweenEdge u w huw) ≠ α := by
    rw [hbridge]
    exact hδα
  have hleft : χ (outsiderEdge cyc w hw 0) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m))) := by
    by_contra hgamma
    exact hnone (jLeftCopy hm cyc u w hu hw huw)
      (positive_jLeft_insertion_copy hm χ r cyc u w hu hw huw α hnewOutside
        hselected hbridgeNew hbridgeNe hcommon hgamma)
  have hright : χ (outsiderEdge cyc w hw 0) =
      restrictedColor χ r (cyc.mapEdgeSet (sourceClosing m hm)) := by
    by_contra hgamma
    exact hnone (jRightCopy hm cyc u w hu hw huw)
      (positive_jRight_insertion_copy hm χ r cyc u w hu hw huw α hnewOutside
        hselected hbridgeNew hbridgeNe hcommon hgamma)
  have hsource : sourceStep (⟨0, by omega⟩ : Fin m) = sourceClosing m hm :=
    cyc.mapEdgeSet.injective
      (restrictedColor_injective χ r (hleft.symm.trans hright))
  exact (sourceStep_ne_closing hm (⟨0, by omega⟩ : Fin m)) hsource

end ErdosProblems.AntiRamseyCycleClaimOneCaseB
