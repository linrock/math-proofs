module

public import CycleClaimTwoOrientedInsertionV2

@[expose] public section

/-!
closing-color equality for an inward-terminal selected path. The same arbitrary NewChoice, original host closing edge and inner NEW
owner are preserved. The checked ordered-chain provider constructs the
forbidden host cycle; this module introduces no Copy or graph-map machinery.
-/

namespace ErdosProblems.AntiRamseyCycleClosingColorEquality

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Under literal host no-rainbow, the closing edge of a selected path
whose terminal step is NEW at its inner endpoint has the first step's
color. Interior selected steps are disjoint from closing; the terminal
step is handled by its supplied NEW owner, not by disjointness. -/
theorem no_rainbow_forces_first_closing_color
    {m : ℕ} (hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (q : Fin (m + 2) → Fin n) (hq : Function.Injective q)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)))
    (closing : HostEdge n)
    (hclosing : closing.val = s(q 0, q (Fin.last (m + 1))))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r q hpath (Fin.last m)) ∈
      newColors χ (q (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    χ closing = restrictedColor χ r (selectedPathStep χ r q hpath 0) := by
  by_contra hnot
  let chain : Fin (m + 1) → (selectedGraph χ r).edgeSet :=
    selectedPathStep χ r q hpath
  have houtsideClosing (i : Fin (m + 2))
      (hzero : i ≠ 0) (hlast : i ≠ Fin.last (m + 1)) :
      q i ∉ closing.val := by
    intro hin
    rw [hclosing] at hin
    rcases Sym2.mem_iff.mp hin with h | h
    · exact hzero (hq h)
    · exact hlast (hq h)
  have hcastZeroNe (i : Fin (m + 1)) (hi : i ≠ 0) :
      Fin.castSucc i ≠ (0 : Fin (m + 2)) := by
    intro h
    apply hi
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa only [Fin.val_castSucc, Fin.val_zero] using hv
  have hcastLastNe (i : Fin (m + 1)) :
      Fin.castSucc i ≠ Fin.last (m + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at hv
    have hil := i.isLt
    omega
  have hsuccZeroNe (i : Fin (m + 1)) :
      Fin.succ i ≠ (0 : Fin (m + 2)) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  have hne : ∀ i : Fin (m + 1),
      restrictedColor χ r (chain i) ≠ χ closing := by
    intro i
    by_cases hzero : i = 0
    · subst i
      change restrictedColor χ r (selectedPathStep χ r q hpath 0) ≠ χ closing
      intro heq
      exact hnot heq.symm
    by_cases hlast : i = Fin.last m
    · subst i
      change restrictedColor χ r
        (selectedPathStep χ r q hpath (Fin.last m)) ≠ χ closing
      intro heq
      have hinc := newColor_every_edge_incident χ
        (q (Fin.castSucc (Fin.last m))) hnewLast closing heq.symm
      exact houtsideClosing _ (hcastZeroNe _ hzero) (hcastLastNe _) hinc
    have hsuccLastNe : Fin.succ i ≠ Fin.last (m + 1) := by
      intro h
      apply hlast
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hv ⊢
      omega
    apply arbitrary_selected_edge_ne_disjoint_host_edge χ r (chain i) closing
    intro v hv
    change v ∈ s(q (Fin.castSucc i), q (Fin.succ i)) at hv
    rcases Sym2.mem_iff.mp hv with h | h
    · rw [h]
      exact houtsideClosing _ (hcastZeroNe _ hzero) (hcastLastNe _)
    · rw [h]
      exact houtsideClosing _ (hsuccZeroNe _) hsuccLastNe
  obtain ⟨f, hf⟩ :=
    ordered_selected_chain_closes_rainbow (t := m + 1) (by omega)
      χ r q hq chain (fun _ => rfl) closing hclosing hne
  exact hno f hf

end ErdosProblems.AntiRamseyCycleClosingColorEquality
