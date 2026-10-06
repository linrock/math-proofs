module

public import CycleLiteralSnocV2
public import CycleForcedTailWitness

@[expose] public section

/-!
Literal forced-tail append and one-vertex suffix. The same selected terminal edge, original host color and inner vertex are
retained.
-/

namespace ErdosProblems.AntiRamseyCycleForcedTailAppendSuffix

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Dropping the first vertex retains the literal selected terminal edge and
its exact inner vertex, hence also its inward NEW color. -/
theorem suffix_inward_new_terminal
    {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (R : Fin (m + 3) → Fin n) (hR : Function.Injective R)
    (hRpath : ∀ i : Fin (m + 2),
      (selectedGraph χ r).Adj (R (Fin.castSucc i)) (R (Fin.succ i)))
    (D : Finset (Fin n)) (hRD : ∀ i : Fin (m + 3), R i ∈ D)
    (hRnew : restrictedColor χ r
      (selectedPathStep χ r R hRpath (Fin.last (m + 1))) ∈
      newColors χ (R (Fin.castSucc (Fin.last (m + 1))))) :
    let Q : Fin (m + 2) → Fin n := fun i => R i.succ
    ∃ hQpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (Q (Fin.castSucc i)) (Q (Fin.succ i)),
      Function.Injective Q ∧
      (∀ i : Fin (m + 2), Q i ∈ D) ∧
      selectedPathStep χ r Q hQpath (Fin.last m) =
        selectedPathStep χ r R hRpath (Fin.last (m + 1)) ∧
      Q (Fin.castSucc (Fin.last m)) =
        R (Fin.castSucc (Fin.last (m + 1))) ∧
      restrictedColor χ r (selectedPathStep χ r Q hQpath (Fin.last m)) ∈
        newColors χ (Q (Fin.castSucc (Fin.last m))) := by
  classical
  dsimp only
  let Q : Fin (m + 2) → Fin n := fun i => R i.succ
  have hQ : Function.Injective Q := hR.comp (Fin.succ_injective (m + 2))
  have hQD : ∀ i : Fin (m + 2), Q i ∈ D := by
    intro i
    exact hRD i.succ
  have hQpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (Q (Fin.castSucc i)) (Q (Fin.succ i)) := by
    intro i
    simpa only [Q, Fin.succ_castSucc] using hRpath i.succ
  have hinner : Q (Fin.castSucc (Fin.last m)) =
      R (Fin.castSucc (Fin.last (m + 1))) := by
    simp only [Q, Fin.succ_castSucc, Fin.succ_last]
  have houter : Q (Fin.succ (Fin.last m)) =
      R (Fin.succ (Fin.last (m + 1))) := by
    simp only [Q, Fin.succ_last]
  have hsame : selectedPathStep χ r Q hQpath (Fin.last m) =
      selectedPathStep χ r R hRpath (Fin.last (m + 1)) := by
    apply Subtype.ext
    change s(Q (Fin.castSucc (Fin.last m)), Q (Fin.succ (Fin.last m))) =
      s(R (Fin.castSucc (Fin.last (m + 1))), R (Fin.succ (Fin.last (m + 1))))
    rw [hinner, houter]
  refine ⟨hQpath, hQ, hQD, hsame, hinner, ?_⟩
  rw [hsame]
  simpa only [Fin.succ_castSucc, Fin.succ_last] using hRnew

/-- The exact forced-tail witness produces a literal snoc R and its literal
suffix Q. Both terminal edges are the same named original-host edge and
are NEW at the old terminal vertex of p. Only containment of the new vertex
uses selected-adjacency closure of D. -/
theorem forced_tail_literal_append_and_suffix
    {m : ℕ} (hm : 1 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (hnewLast : restrictedColor χ r
      (selectedPathStep χ r p hpath (Fin.last m)) ∈
      newColors χ (p (Fin.castSucc (Fin.last m))))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (m + 2), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (m + 2)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (m + 2), f i ∈ D)
    (hpair : m + 2 ≤ (newColors χ (p 0)).card +
      (newColors χ (p (Fin.last (m + 1)))).card)
    (hclosed : ∀ v : Fin n, v ∈ D → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D) :
    ∃ w : Fin n, ∃ e : HostEdge n,
      w ∉ Finset.univ.image p ∧
      (selectedGraph χ r).Adj (p (Fin.last (m + 1))) w ∧
      e.val = s(p (Fin.last (m + 1)), w) ∧
      χ e ∈ newColors χ (p (Fin.last (m + 1))) ∧
      (let R : Fin (m + 3) → Fin n := Fin.snoc p w
       let Q : Fin (m + 2) → Fin n := fun i => R i.succ
       ∃ hRpath : ∀ i : Fin (m + 2),
         (selectedGraph χ r).Adj (R (Fin.castSucc i)) (R (Fin.succ i)),
       ∃ hQpath : ∀ i : Fin (m + 1),
         (selectedGraph χ r).Adj (Q (Fin.castSucc i)) (Q (Fin.succ i)),
         Function.Injective R ∧
         (∀ i : Fin (m + 3), R i ∈ D) ∧
         Function.Injective Q ∧
         (∀ i : Fin (m + 2), Q i ∈ D) ∧
         (selectedPathStep χ r R hRpath (Fin.last (m + 1))).val = e.val ∧
         restrictedColor χ r
           (selectedPathStep χ r R hRpath (Fin.last (m + 1))) = χ e ∧
         R (Fin.castSucc (Fin.last (m + 1))) = p (Fin.last (m + 1)) ∧
         selectedPathStep χ r Q hQpath (Fin.last m) =
           selectedPathStep χ r R hRpath (Fin.last (m + 1)) ∧
         Q (Fin.castSucc (Fin.last m)) = p (Fin.last (m + 1)) ∧
         restrictedColor χ r
           (selectedPathStep χ r R hRpath (Fin.last (m + 1))) ∈
           newColors χ (R (Fin.castSucc (Fin.last (m + 1)))) ∧
         restrictedColor χ r (selectedPathStep χ r Q hQpath (Fin.last m)) ∈
           newColors χ (Q (Fin.castSucc (Fin.last m)))) := by
  classical
  obtain ⟨w, e, hwImage, hadj, he, hnew⟩ :=
    ErdosProblems.AntiRamseyCycleForcedTailWitness.exists_terminal_newColor_edge_outside_inward_path
      hm χ r p hp hpath hnewLast hno D hpD hnoD hpair
  have hwRange : w ∉ Set.range p := by
    rintro ⟨i, hi⟩
    exact hwImage (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  have hwD : w ∈ D := hclosed (p (Fin.last (m + 1))) (hpD (Fin.last (m + 1))) w hadj
  let R : Fin (m + 3) → Fin n := Fin.snoc p w
  let Q : Fin (m + 2) → Fin n := fun i => R i.succ
  obtain ⟨hRpath, hR, hRD, hval, hcolor, hinner, hRnew⟩ :=
    ErdosProblems.AntiRamseyCycleLiteralSnoc.literal_snoc_with_new_terminal
      χ r p hp hpath D hpD w hwRange hwD e hadj he hnew
  have hRnewStep : restrictedColor χ r
      (selectedPathStep χ r R hRpath (Fin.last (m + 1))) ∈
      newColors χ (R (Fin.castSucc (Fin.last (m + 1)))) := hRnew
  obtain ⟨hQpath, hQ, hQD, hsame, hQinner, hQnew⟩ :=
    suffix_inward_new_terminal χ r R hR hRpath D hRD hRnewStep
  have hQold : Q (Fin.castSucc (Fin.last m)) = p (Fin.last (m + 1)) :=
    hQinner.trans hinner
  refine ⟨w, e, hwImage, hadj, he, hnew, ?_⟩
  dsimp only
  exact ⟨hRpath, hQpath, hR, hRD, hQ, hQD, hval, hcolor, hinner,
    hsame, hQold, hRnewStep, hQnew⟩

end ErdosProblems.AntiRamseyCycleForcedTailAppendSuffix
