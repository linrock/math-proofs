module

public import CycleClaimOneSecondInsertionV2
public import CycleClaimOneCaseBV2

@[expose] public section

/-!
Claim 1 selected-attachment glue combining the first/second insertion lemmas
with Case B.
-/

namespace ErdosProblems.AntiRamseyCycleClaimOneSelectedAttachment

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion
open ErdosProblems.AntiRamseyCycleClaimOneCaseB

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Local Claim 1 at cycle position zero. Selected attachment alone supplies
a NEW owner at one endpoint; the two positive insertion cases then apply. -/
theorem positive_selected_attachment_copy_zero {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (hnewu : 2 ≤ (newColors χ u).card) :
    ∃ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let e : (selectedGraph χ r).edgeSet := ⟨s(u, cyc.toHom 0), hattach⟩
  have heColor : restrictedColor χ r e = χ (outsiderEdge cyc u hu 0) := by
    rfl
  obtain ⟨v, hve, hnew⟩ := arbitrary_selected_edge_has_new_endpoint χ r e
  have hv : v = u ∨ v = cyc.toHom 0 := by
    change v ∈ s(u, cyc.toHom 0) at hve
    exact Sym2.mem_iff.mp hve
  rcases hv with hv | hv
  · subst v
    have hnewOutside : χ (outsiderEdge cyc u hu 0) ∈ newColors χ u := by
      rw [← heColor]
      exact hnew
    exact positive_caseB_outside_new_copy hm χ r cyc u hu hnewOutside hnewu
  · subst v
    have hnewFirst : χ (outsiderEdge cyc u hu 0) ∈ newColors χ (cyc.toHom 0) := by
      rw [← heColor]
      exact hnew
    exact positive_first_endpoint_attachment_copy hm χ r cyc u hu hattach hnewFirst

/-- The already checked cyclic Copy translation moves an arbitrary selected
attachment endpoint to zero and preserves the outside vertex condition. -/
theorem positive_selected_attachment_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) (a : Fin (m + 1))
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom a))
    (hnewu : 2 ≤ (newColors χ u).card) :
    ∃ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  have hshiftAttach : (selectedGraph χ r).Adj u ((shiftedCycle cyc a).toHom 0) := by
    simpa only [shiftedCycle_apply, zero_add] using hattach
  exact positive_selected_attachment_copy_zero hm χ r (shiftedCycle cyc a) u
    (shifted_outside cyc u hu a) hshiftAttach hnewu

/-- Under literal host no-rainbow exclusion, an outside vertex with at least
two NEW colors has no selected attachment to any vertex of this old cycle. -/
theorem no_rainbow_no_outside_selected_attachment {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnewu : 2 ≤ (newColors χ u).card)
    (hnone : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) (a : Fin (m + 1)) :
    ¬ (selectedGraph χ r).Adj u (cyc.toHom a) := by
  intro hattach
  obtain ⟨f, hf⟩ := positive_selected_attachment_copy hm χ r cyc u hu a hattach hnewu
  exact hnone f hf

end ErdosProblems.AntiRamseyCycleClaimOneSelectedAttachment
