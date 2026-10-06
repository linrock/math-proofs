module

public import RestorationTrace1105
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Structural ledgers for the vertex-restoration
trace on the SAME original G. Induction concludes only propositions; it
does not extract data from the Prop-valued trace. No degree, list, count,
positive-restoration, core, connectivity or favorable-order oracle is added.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.RestorationTrace1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

/-- Exact original cardinality, unordered-edge/charge, and excess ledgers.
All natural cardinality subtractions are guarded by the derived K subset U.
The nonnegative excess is constructed by Prop-valued trace induction. -/
theorem restoration_trace_ledgers
    (G : SimpleGraph V) (d : ℕ) (K U : Finset V) (c : ℕ)
    (htrace : RestorationTrace G d K U c) :
    K ⊆ U ∧
      U.card = K.card + (U.card - K.card) ∧
      (withinEdges G U).card + c =
        (withinEdges G K).card + d * (U.card - K.card) ∧
      ∃ w : ℕ, c = (U.card - K.card) + w := by
  classical
  induction htrace with
  | nil =>
      refine ⟨?_, ?_, ?_, 0, ?_⟩
      · intro x hx
        exact hx
      · simp
      · simp
      · simp
  | @snoc U c trace x hfresh hlow ih =>
      obtain ⟨hKU, hcard, hledger, w, hw⟩ := ih
      have hcardLe : K.card ≤ U.card := Finset.card_le_card hKU
      have hcardStep : (insert x U).card = U.card + 1 :=
        Finset.card_insert_of_notMem hfresh
      have hrStep : (insert x U).card - K.card =
          (U.card - K.card) + 1 := by
        omega
      have hrestoredErase : (insert x U).erase x = U :=
        Finset.erase_insert hfresh
      have hdegree := withinDegree_self_erase G (insert x U) x
      rw [hrestoredErase] at hdegree
      have hedgesStep := withinEdges_erase_ledger G (insert x U) x
        (Finset.mem_insert_self x U)
      rw [hrestoredErase, ← hdegree] at hedgesStep
      have hchargeCancel : withinDegree G U x +
          (d - withinDegree G U x) = d := by
        omega
      have hexcessStep : d - withinDegree G U x =
          1 + ((d - 1) - withinDegree G U x) := by
        omega
      have hnewLedger :
          (withinEdges G (insert x U)).card +
              (c + (d - withinDegree G U x)) =
            (withinEdges G K).card + d * ((U.card - K.card) + 1) := by
        calc
          (withinEdges G (insert x U)).card +
              (c + (d - withinDegree G U x)) =
              ((withinEdges G U).card + c) +
                (withinDegree G U x + (d - withinDegree G U x)) := by
                  rw [hedgesStep]
                  omega
          _ = ((withinEdges G K).card + d * (U.card - K.card)) + d := by
                rw [hledger, hchargeCancel]
          _ = (withinEdges G K).card +
                d * ((U.card - K.card) + 1) := by
                rw [Nat.mul_add, Nat.mul_one]
                omega
      have hnewExcess : c + (d - withinDegree G U x) =
          ((U.card - K.card) + 1) +
            (w + ((d - 1) - withinDegree G U x)) := by
        omega
      refine ⟨hKU.trans (Finset.subset_insert x U), ?_, ?_,
        w + ((d - 1) - withinDegree G U x), ?_⟩
      · omega
      · rw [hrStep]
        exact hnewLedger
      · rw [hrStep]
        exact hnewExcess

/-- Each actual snoc increases the excess above one unit per restoration
by exactly its recorded original earlier-prefix defect. No list is supplied. -/
theorem restoration_trace_snoc_excess
    (G : SimpleGraph V) (d : ℕ) (K U : Finset V) (c : ℕ)
    (htrace : RestorationTrace G d K U c)
    (x : V) (hfresh : x ∉ U) (hlow : withinDegree G U x < d) :
    (c + (d - withinDegree G U x)) - ((insert x U).card - K.card) =
      (c - (U.card - K.card)) + ((d - 1) - withinDegree G U x) := by
  classical
  obtain ⟨hKU, _hcard, _hledger, w, hw⟩ :=
    restoration_trace_ledgers G d K U c htrace
  have hcardLe : K.card ≤ U.card := Finset.card_le_card hKU
  have hcardStep : (insert x U).card = U.card + 1 :=
    Finset.card_insert_of_notMem hfresh
  have hexcessStep : d - withinDegree G U x =
      1 + ((d - 1) - withinDegree G U x) := by
    omega
  omega

end ErdosProblems.PathUpperReduction.RestorationTraceLedgers1105
