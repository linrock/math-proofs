module

public import CyclePartialSpliceMapV2
public import CycleOmittedSelectedEdgeClosing

@[expose] public section

/-!
application: two supplied skips and the original first-edge
closing color give the literal rainbow host cycle via the existing constructor. Skip selection and closing-color equality are separate obligations.
-/

namespace ErdosProblems.AntiRamseyCyclePartialSpliceClosing

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCyclePartialSpliceMap
open ErdosProblems.AntiRamseyCycleOmittedSelectedEdgeClosing

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The exact interval reversal omits the first selected edge; its color
therefore closes the reordered path into a rainbow original-host cycle. -/
theorem supplied_skips_and_first_closing_color_rainbow
    {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (R : Fin (m + 3) → Fin n) (hR : Function.Injective R)
    (hpath : ∀ x y : Fin (m + 3), x.val + 1 = y.val →
      (selectedGraph χ r).Adj (R x) (R y))
    (a : Fin (m + 3)) (ha2 : 2 ≤ a.val) (ham : a.val ≤ m)
    (hleft : (selectedGraph χ r).Adj (R 0) (R a))
    (hright : (selectedGraph χ r).Adj
      (R ⟨1, by omega⟩) (R ⟨a.val + 1, by omega⟩))
    (e0 : (selectedGraph χ r).edgeSet)
    (he0 : e0.val = s(R 0, R ⟨1, by omega⟩))
    (closing : HostEdge n)
    (hclosing : closing.val = s(R 0, R (Fin.last (m + 2))))
    (hcolor : χ closing = restrictedColor χ r e0) :
    ∃ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let q : Fin (m + 3) → Fin n := fun i => R (partialReverse a i)
  have hq : Function.Injective q := hR.comp (partialReverse_injective a)
  have hqpath : ∀ i : Fin (m + 2),
      (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)) :=
    partial_splice_ordered_path (selectedGraph χ r) R hpath a ha2 ham hleft hright
  have homit : ∀ i : Fin (m + 2),
      s(q (Fin.castSucc i), q (Fin.succ i)) ≠ e0.val := by
    intro i
    rw [he0]
    exact partial_splice_omits_first_edge R hR a ha2 i
  have hclosingq : closing.val = s(q 0, q (Fin.last (m + 2))) := by
    simpa only [q, partialReverse_zero, partialReverse_last a ham] using hclosing
  exact omitted_selected_edge_closing_rainbow (by omega) χ r q hq hqpath
    e0 homit closing hclosingq hcolor

end ErdosProblems.AntiRamseyCyclePartialSpliceClosing
