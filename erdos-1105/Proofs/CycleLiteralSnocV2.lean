module

public import CycleNewChoiceExchange
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
stronger append interface for the two-tail alignment. The path is the literal snoc, and its named terminal edge/color and old
inner endpoint are exposed. No existential path representation is hidden.
-/

namespace ErdosProblems.AntiRamseyCycleLiteralSnoc

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Append the named outside NEW edge to the literal selected ordered path.
The value of the terminal selected edge, its original host color and its
inner endpoint are retained for a later suffix alignment. -/
theorem literal_snoc_with_new_terminal
    {t : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (hstep : ∀ i : Fin t,
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (t + 1), p i ∈ D)
    (w : Fin n) (hw : w ∉ Set.range p) (hwD : w ∈ D)
    (e : HostEdge n)
    (hadj : (selectedGraph χ r).Adj (p (Fin.last t)) w)
    (he : e.val = s(p (Fin.last t), w))
    (hnew : χ e ∈ newColors χ (p (Fin.last t))) :
    let R : Fin (t + 2) → Fin n := Fin.snoc p w
    ∃ hRpath : ∀ i : Fin (t + 1),
      (selectedGraph χ r).Adj (R (Fin.castSucc i)) (R (Fin.succ i)),
      Function.Injective R ∧
      (∀ i : Fin (t + 2), R i ∈ D) ∧
      (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
        hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet).val = e.val ∧
      restrictedColor χ r
        (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
          hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) = χ e ∧
      R (Fin.castSucc (Fin.last t)) = p (Fin.last t) ∧
      restrictedColor χ r
        (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
          hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) ∈
        newColors χ (R (Fin.castSucc (Fin.last t))) := by
  classical
  dsimp only
  let R : Fin (t + 2) → Fin n := Fin.snoc p w
  have hR : Function.Injective R := Fin.snoc_injective_of_injective hp hw
  have hRD : ∀ i : Fin (t + 2), R i ∈ D := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [R, Fin.snoc_last] using hwD
    | cast j => simpa only [R, Fin.snoc_castSucc] using hpD j
  have hRpath : ∀ i : Fin (t + 1),
      (selectedGraph χ r).Adj (R (Fin.castSucc i)) (R (Fin.succ i)) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simpa only [R, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using hadj
    | cast j =>
      simpa only [R, Fin.succ_castSucc, Fin.snoc_castSucc] using hstep j
  have hval :
      (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
        hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet).val = e.val := by
    simpa only [R, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using he.symm
  have hcolor : restrictedColor χ r
      (⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
        hRpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) = χ e := by
    change χ ⟨s(R (Fin.castSucc (Fin.last t)), R (Fin.succ (Fin.last t))),
      SimpleGraph.edgeSet_mono
        (show selectedGraph χ r ≤ (⊤ : SimpleGraph (Fin n)) from le_top)
        (hRpath (Fin.last t))⟩ = χ e
    apply congrArg χ
    exact Subtype.ext hval
  have hinner : R (Fin.castSucc (Fin.last t)) = p (Fin.last t) := by
    simp only [R, Fin.snoc_castSucc]
  refine ⟨hRpath, hR, hRD, hval, hcolor, hinner, ?_⟩
  rw [hcolor]
  simpa only [Fin.snoc_castSucc] using hnew

end ErdosProblems.AntiRamseyCycleLiteralSnoc
