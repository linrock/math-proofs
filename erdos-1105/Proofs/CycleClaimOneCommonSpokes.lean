module

public import CycleClaimOneOutsideInsertionV4

@[expose] public section

/-!
It assumes no selected
first attachment and no outside NEW-color cardinality. It does not construct a J
copy or complete Claim 1 or either universal Formal Conjectures #1105 theorem.
-/

namespace ErdosProblems.AntiRamseyCycleClaimOneCommonSpokes

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion
open ErdosProblems.AntiRamseyCycleClaimOneOutsideInsertion
open scoped Fin.NatCast

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Under literal host rainbow-cycle exclusion, a selected outgoing-color
repeat at any cyclic position propagates to position zero. Natural iteration
uses modular addition on Fin; choosing the value of the additive inverse
reaches zero in at most m successor steps, including the closing-edge wrap. -/
theorem no_rainbow_repeat_forces_zero {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ)
    (a : Fin (m + 1))
    (hfirst : χ (outsiderEdge cyc u hu a) =
      cycleOutgoingColor hm χ r cyc a) :
    χ (outsiderEdge cyc u hu 0) = cycleOutgoingColor hm χ r cyc 0 := by
  have hall : ∀ t : ℕ,
      χ (outsiderEdge cyc u hu (a + (t : Fin (m + 1)))) =
        cycleOutgoingColor hm χ r cyc (a + (t : Fin (m + 1))) := by
    intro t
    induction t with
    | zero =>
        simpa only [Nat.cast_zero, add_zero] using hfirst
    | succ t ih =>
        have hnext := no_rainbow_forces_next_repeat hm χ r cyc u hu
          hnone (a + (t : Fin (m + 1))) ih
        simpa only [Nat.cast_succ, add_assoc] using hnext
  have hzero := hall (-a).val
  simpa only [Fin.cast_val_eq_self, add_neg_cancel] using hzero

/-- Case B common-spoke constancy. If the first outside spoke color is NEW
at u and no literal host rainbow cycle of one greater length exists, every
cycle spoke has that same color. No selected attachment or NEW count is used. -/
theorem no_rainbow_outside_new_spokes_eq {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnewOutside : χ (outsiderEdge cyc u hu 0) ∈ newColors χ u)
    (hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ) :
    ∀ j : Fin (m + 1),
      χ (outsiderEdge cyc u hu j) = χ (outsiderEdge cyc u hu 0) := by
  have hzeroAvoid : χ (outsiderEdge cyc u hu 0) ≠
      cycleOutgoingColor hm χ r cyc 0 := by
    intro heq
    rw [cycleOutgoingColor_zero] at heq
    let d : (cycleGraph (m + 1)).edgeSet :=
      sourceStep (⟨0, by omega⟩ : Fin m)
    let e : HostEdge n :=
      ⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
    have hc : χ e = χ (outsiderEdge cyc u hu 0) := heq.symm
    have hue := newColor_every_edge_incident χ u hnewOutside e hc
    change u ∈ Sym2.map cyc.toHom d.val at hue
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hue
    exact hu ⟨i, hi⟩
  have hadj : ∀ a : Fin (m + 1),
      χ (outsiderEdge cyc u hu a) = χ (outsiderEdge cyc u hu 0) →
      χ (outsiderEdge cyc u hu (a + 1)) =
        χ (outsiderEdge cyc u hu 0) := by
    intro a ha
    by_contra hnext
    have hnew : χ (outsiderEdge cyc u hu a) ∈ newColors χ u := by
      rw [ha]
      exact hnewOutside
    have hspokes : χ (outsiderEdge cyc u hu a) ≠
        χ (outsiderEdge cyc u hu (a + 1)) := by
      intro heq
      exact hnext (heq.symm.trans ha)
    have hrepeat := no_rainbow_outside_mismatch_forces_next_repeat
      hm χ r cyc u hu hnone a hnew hspokes
    have hzero := no_rainbow_repeat_forces_zero hm χ r cyc u hu
      hnone (a + 1) hrepeat
    exact hzeroAvoid hzero
  have hall : ∀ j : ℕ,
      χ (outsiderEdge cyc u hu (j : Fin (m + 1))) =
        χ (outsiderEdge cyc u hu 0) := by
    intro j
    induction j with
    | zero =>
        simp only [Nat.cast_zero]
    | succ j ih =>
        have hnext := hadj (j : Fin (m + 1)) ih
        simpa only [Nat.cast_succ] using hnext
  intro j
  simpa only [Fin.cast_val_eq_self] using hall j.val

end ErdosProblems.AntiRamseyCycleClaimOneCommonSpokes
