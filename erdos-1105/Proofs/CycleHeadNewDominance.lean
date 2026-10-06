module

public import CycleNewChoiceOutsideWitnessV2
public import CycleClaimTwoOrientedInsertionV2

@[expose] public section

/-!
head NEW domination for Choi Claim 2's inward-oriented path tail. The checked outside NEW witness and positive host insertion are applied to
the same arbitrary NewChoice and original complete-host coloring.
-/

namespace ErdosProblems.AntiRamseyCycleHeadNewDominance

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A NEW deficit at the head of this selected tail would create an
inward NEW attachment and hence a literal rainbow original-host C_(m+3).
No shorter-cycle exclusion, pair sum or component hypothesis is assumed. -/
theorem no_head_new_deficit_of_inward_tail
    {m : ℕ} (hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    (newColors χ (p 0)).card ≤
      ((selectedGraph χ r).neighborFinset (p 0) ∩ Finset.univ.image p).card := by
  classical
  by_contra hnot
  have hsmall :
      ((selectedGraph χ r).neighborFinset (p 0) ∩ Finset.univ.image p).card <
        (newColors χ (p 0)).card := by
    omega
  obtain ⟨u, e, hu, hselected, he, hnew⟩ :=
    ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness.exists_selected_newColor_edge_outside
      χ r (p 0) (Finset.univ.image p) hsmall
  have huRange : u ∉ Set.range p := by
    rintro ⟨i, hi⟩
    exact hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  have heSelected : e.val ∈ (selectedGraph χ r).edgeSet := by
    rw [he]
    exact hselected
  let attachment : (selectedGraph χ r).edgeSet := ⟨e.val, heSelected⟩
  have hattachment : attachment.val = s(u, p 0) := by
    change e.val = s(u, p 0)
    rw [he]
    exact Sym2.eq_swap
  have hcolor : restrictedColor χ r attachment = χ e := rfl
  have hnewFirst : restrictedColor χ r attachment ∈ newColors χ (p 0) := by
    rw [hcolor]
    exact hnew
  obtain ⟨f, hf⟩ :=
    ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion.inward_oriented_path_insertion_rainbow
      hm χ r p hp hpath u huRange attachment hattachment hnewFirst hnewLast
  exact hno f hf

end ErdosProblems.AntiRamseyCycleHeadNewDominance

