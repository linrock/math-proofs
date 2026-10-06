module

public import CycleClaimTwoOrientedInsertionV2

@[expose] public section

/-!
semantic bridge for Claim 2's final splice. The checked generic
ordered selected-chain helper supplies the literal host cycle Copy. This
wrapper only derives its closing-color separation from one omitted selected
edge with the same color. No partial-reversal map is implemented here.
-/

namespace ErdosProblems.AntiRamseyCycleOmittedSelectedEdgeClosing

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- An omitted selected edge with the closing color makes every edge of the
literal closed ordered path distinct. The cycle has k=t+1>=3 vertices. -/
theorem omitted_selected_edge_closing_rainbow {t : ℕ} (ht : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (q : Fin (t + 1) → Fin n) (hq : Function.Injective q)
    (hpath : ∀ i : Fin t,
      (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)))
    (e0 : (selectedGraph χ r).edgeSet)
    (homit : ∀ i : Fin t,
      s(q (Fin.castSucc i), q (Fin.succ i)) ≠ e0.val)
    (closing : HostEdge n)
    (hclosing : closing.val = s(q 0, q (Fin.last t)))
    (hcolor : χ closing = restrictedColor χ r e0) :
    ∃ f : (cycleGraph (t + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let chain : Fin t → (selectedGraph χ r).edgeSet :=
    fun i => ⟨s(q (Fin.castSucc i), q (Fin.succ i)), hpath i⟩
  apply ordered_selected_chain_closes_rainbow ht χ r q hq chain
    (fun _ => rfl) closing hclosing
  intro i hsameColor
  exact homit i (congrArg Subtype.val
    (restrictedColor_injective χ r (hsameColor.trans hcolor)))

end ErdosProblems.AntiRamseyCycleOmittedSelectedEdgeClosing
