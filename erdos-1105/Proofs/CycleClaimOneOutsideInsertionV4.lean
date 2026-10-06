module

public import CycleClaimOneSecondInsertionV2
public import Batteries.Tactic.OpenPrivate

@[expose] public section

/-!
Outside-vertex insertion step for Claim 1 of the cycle anti-Ramsey proof.
-/

namespace ErdosProblems.AntiRamseyCycleClaimOneOutsideInsertion

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Insert `u` between the first two cycle vertices. The two literal host
spokes are distinct in color and each avoids every retained selected color.
This palette interface reuses the private map; it assumes no NEW orientation.
-/
theorem positive_two_spoke_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hspokes : χ (outsiderEdge cyc u hu 0) ≠
      χ (outsiderEdge cyc u hu 1))
    (hfirstAvoid : ∀ d : (cycleGraph (m + 1)).edgeSet,
      d ≠ sourceStep (⟨0, by omega⟩ : Fin m) →
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet d))
    (hsecondAvoid : ∀ d : (cycleGraph (m + 1)).edgeSet,
      d ≠ sourceStep (⟨0, by omega⟩ : Fin m) →
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet d)) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  let p := deletedInsertionMap cyc u
  have hp : Function.Injective p := deletedInsertionMap_injective cyc u hu
  let φ : (cycleGraph ((m + 1) + 1)) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨p, by
      intro a b hab
      exact (top_adj _ _).mpr
        (hp.ne ((cycleGraph ((m + 1) + 1)).ne_of_adj hab))⟩
  let f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)) := ⟨φ, hp⟩
  let L := EdgeLabeling.pullback χ f.toHom
  let α : C := χ (outsiderEdge cyc u hu 0)
  let β : C := χ (outsiderEdge cyc u hu 1)
  let lifted : (cycleGraph (m + 1)).edgeSet → HostEdge n := fun d =>
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  have hmapHost (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : HostEdge n) (hval : Sym2.map p e.val = d.val) :
      f.mapEdgeSet e = d := by
    apply Subtype.ext
    exact hval
  have hmapSelected (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map p e.val = Sym2.map cyc.toHom d.val) :
      f.mapEdgeSet e = lifted d := by
    apply Subtype.ext
    exact hval
  have hcolorHost (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : HostEdge n) (hmap : f.mapEdgeSet e = d) : L e = χ d := by
    simpa only [L, EdgeLabeling.pullback_apply, SimpleGraph.Copy.mapEdgeSet, Function.Embedding.coeFn_mk] using congrArg χ hmap
  have hcolorSelected (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hmap : f.mapEdgeSet e = lifted d) :
      L e = restrictedColor χ r (cyc.mapEdgeSet d) := by
    simpa only [L, EdgeLabeling.pullback_apply, lifted, restrictedColor, SimpleGraph.Copy.mapEdgeSet, Function.Embedding.coeFn_mk]
      using congrArg χ hmap
  have hstep0 : L (sourceStep (0 : Fin (m + 1))) = α :=
    hcolorHost _ _ (hmapHost _ _ (deletedInsertionMap_first_spoke cyc u hu))
  have hstep1 : L (sourceStep (1 : Fin (m + 1))) = β :=
    hcolorHost _ _ (hmapHost _ _ (deletedInsertionMap_second_spoke hm cyc u hu))
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hClass (e : (cycleGraph ((m + 1) + 1)).edgeSet) :
      (e = sourceStep (0 : Fin (m + 1)) ∧ L e = α) ∨
      (e = sourceStep (1 : Fin (m + 1)) ∧ L e = β) ∨
      ∃ d : (cycleGraph (m + 1)).edgeSet,
        d ≠ sourceStep (⟨0, by omega⟩ : Fin m) ∧
        L e = restrictedColor χ r (cyc.mapEdgeSet d) ∧
        f.mapEdgeSet e = lifted d := by
    rcases sourceEdge_cases (m := m + 1) (by omega) e with ⟨i, he⟩ | he
    · subst e
      by_cases hi0 : i = 0
      · subst i
        exact Or.inl ⟨rfl, hstep0⟩
      by_cases hi1 : i = 1
      · subst i
        exact Or.inr (Or.inl ⟨rfl, hstep1⟩)
      have hi : 2 ≤ i.val := by
        have hne0 : i.val ≠ 0 := by
          intro h
          exact hi0 (Fin.ext h)
        have hne1 : i.val ≠ 1 := by
          intro h
          apply hi1
          apply Fin.ext
          simpa only [hone] using h
        omega
      obtain ⟨j, _, hj, hval⟩ := deletedInsertionMap_step_ge_two cyc u i hi
      have hd : sourceStep j ≠ sourceStep (⟨0, by omega⟩ : Fin m) := by
        intro heq
        have hidx := sourceStep_injective heq
        have hvalj := congrArg Fin.val hidx
        change j.val = 0 at hvalj
        omega
      have hmap := hmapSelected (sourceStep i) (sourceStep j) hval
      exact Or.inr (Or.inr ⟨sourceStep j, hd,
        hcolorSelected _ _ hmap, hmap⟩)
    · subst e
      have hd : sourceClosing m hm ≠
          sourceStep (⟨0, by omega⟩ : Fin m) :=
        (sourceStep_ne_closing hm (⟨0, by omega⟩ : Fin m)).symm
      have hmap := hmapSelected _ _ (deletedInsertionMap_closing hm cyc u)
      exact Or.inr (Or.inr ⟨sourceClosing m hm, hd,
        hcolorSelected _ _ hmap, hmap⟩)
  have hpalette : Function.Injective (EdgeLabeling.pullback χ f.toHom) := by
    change Function.Injective L
    intro e₁ e₂ heq
    rcases hClass e₁ with hA₁ | hB₁ | hR₁
    · rcases hClass e₂ with hA₂ | hB₂ | hR₂
      · exact hA₁.1.trans hA₂.1.symm
      · exact False.elim (hspokes (hA₁.2.symm.trans (heq.trans hB₂.2)))
      · obtain ⟨d, hd, hc, _⟩ := hR₂
        exact False.elim (hfirstAvoid d hd (hA₁.2.symm.trans (heq.trans hc)))
    · rcases hClass e₂ with hA₂ | hB₂ | hR₂
      · exact False.elim (hspokes (hA₂.2.symm.trans (heq.symm.trans hB₁.2)))
      · exact hB₁.1.trans hB₂.1.symm
      · obtain ⟨d, hd, hc, _⟩ := hR₂
        exact False.elim (hsecondAvoid d hd (hB₁.2.symm.trans (heq.trans hc)))
    · obtain ⟨d₁, hd₁, hc₁, hm₁⟩ := hR₁
      rcases hClass e₂ with hA₂ | hB₂ | hR₂
      · exact False.elim (hfirstAvoid d₁ hd₁ (hA₂.2.symm.trans (heq.symm.trans hc₁)))
      · exact False.elim (hsecondAvoid d₁ hd₁ (hB₂.2.symm.trans (heq.symm.trans hc₁)))
      · obtain ⟨d₂, _, hc₂, hm₂⟩ := hR₂
        have hcolors := hc₁.symm.trans (heq.trans hc₂)
        have hd : d₁ = d₂ :=
          cyc.mapEdgeSet.injective (restrictedColor_injective χ r hcolors)
        apply f.mapEdgeSet.injective
        exact hm₁.trans ((congrArg lifted hd).trans hm₂.symm)
  exact ⟨f, hpalette⟩

/-- Initial Case B mismatch insertion. The first spoke is NEW at the outside
vertex, differs from the second spoke, and the second spoke differs from the
only retained selected color it could repeat. No selected attachment is needed.
-/
theorem positive_outside_new_initial_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnewOutside : χ (outsiderEdge cyc u hu 0) ∈ newColors χ u)
    (hspokes : χ (outsiderEdge cyc u hu 0) ≠
      χ (outsiderEdge cyc u hu 1))
    (hbeta : χ (outsiderEdge cyc u hu 1) ≠
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  have huSelected (d : (cycleGraph (m + 1)).edgeSet) :
      u ∉ (cyc.mapEdgeSet d).val := by
    intro he
    change u ∈ Sym2.map cyc.toHom d.val at he
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp he
    exact hu ⟨i, hi⟩
  have hfirstAvoid (d : (cycleGraph (m + 1)).edgeSet)
      (_hd : d ≠ sourceStep (⟨0, by omega⟩ : Fin m)) :
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    intro heq
    let e : HostEdge n :=
      ⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
    have hcolor : χ e = χ (outsiderEdge cyc u hu 0) := heq.symm
    exact huSelected d (newColor_every_edge_incident χ u hnewOutside e hcolor)
  have hbetaAvoid (d : (cycleGraph (m + 1)).edgeSet)
      (hv : cyc.toHom 1 ∉ (cyc.mapEdgeSet d).val) :
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    intro heq
    have hdisj : ∀ v : Fin n, v ∈ (cyc.mapEdgeSet d).val →
        v ∉ (outsiderEdge cyc u hu 1).val := by
      intro v hve hvspoke
      have hcases : v = u ∨ v = cyc.toHom 1 := by
        simpa only [outsiderEdge, Sym2.mem_iff] using hvspoke
      rcases hcases with h | h
      · subst v
        exact huSelected d hve
      · subst v
        exact hv hve
    exact (arbitrary_selected_edge_ne_disjoint_host_edge χ r
      (cyc.mapEdgeSet d) (outsiderEdge cyc u hu 1) hdisj) heq.symm
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hsecondAvoid (d : (cycleGraph (m + 1)).edgeSet)
      (hd : d ≠ sourceStep (⟨0, by omega⟩ : Fin m)) :
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    rcases sourceEdge_cases hm d with ⟨j, hjEq⟩ | hdClosing
    · subst d
      by_cases hj1 : j.val = 1
      · have hidx : j = (⟨1, by omega⟩ : Fin m) := Fin.ext hj1
        simpa only [hidx] using hbeta
      have hj0 : j.val ≠ 0 := by
        intro heq
        exact hd (congrArg sourceStep (Fin.ext heq))
      have hj2 : 2 ≤ j.val := by omega
      apply hbetaAvoid
      intro hv
      change cyc.toHom 1 ∈ Sym2.map cyc.toHom (sourceStep j).val at hv
      obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
      have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
      subst k
      change (1 : Fin (m + 1)) ∈ s(Fin.castSucc j, Fin.succ j) at hk
      rcases Sym2.mem_iff.mp hk with h | h
      · have hval : (1 : ℕ) = j.val := by
          simpa only [hone, Fin.val_castSucc] using congrArg Fin.val h
        omega
      · have hval : (1 : ℕ) = j.val + 1 := by
          simpa only [hone, Fin.val_succ] using congrArg Fin.val h
        omega
    · subst d
      apply hbetaAvoid
      intro hv
      change cyc.toHom 1 ∈
        Sym2.map cyc.toHom (sourceClosing m hm).val at hv
      obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
      have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
      subst k
      change (1 : Fin (m + 1)) ∈ s((0 : Fin (m + 1)), Fin.last m) at hk
      rcases Sym2.mem_iff.mp hk with h | h
      · have hval : (1 : ℕ) = 0 := by
          simpa only [hone, Fin.val_zero] using congrArg Fin.val h
        exact Nat.one_ne_zero hval
      · have hval : (1 : ℕ) = m := by
          simpa only [hone, Fin.val_last] using congrArg Fin.val h
        omega
  exact positive_two_spoke_insertion_copy hm χ r cyc u hu
    hspokes hfirstAvoid hsecondAvoid

/-- At any cyclic position, a first spoke NEW at the outside vertex and a
different next spoke force that next spoke to equal its selected outgoing
color under literal host rainbow-cycle exclusion. This is the first Case B
transition, before the equality-to-omitted-edge recurrence takes over.
-/
theorem no_rainbow_outside_mismatch_forces_next_repeat {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ)
    (a : Fin (m + 1))
    (hnewOutside : χ (outsiderEdge cyc u hu a) ∈ newColors χ u)
    (hspokes : χ (outsiderEdge cyc u hu a) ≠
      χ (outsiderEdge cyc u hu (a + 1))) :
    χ (outsiderEdge cyc u hu (a + 1)) =
      cycleOutgoingColor hm χ r cyc (a + 1) := by
  by_contra hnext
  have hshift := shifted_outside cyc u hu a
  have hspoke : outsiderEdge (shiftedCycle cyc a) u hshift 1 =
      outsiderEdge cyc u hu (a + 1) := by
    calc
      outsiderEdge (shiftedCycle cyc a) u hshift 1 =
          outsiderEdge cyc u hu (1 + a) :=
        shifted_outsiderEdge cyc u hu a 1
      _ = outsiderEdge cyc u hu (a + 1) :=
        congrArg (outsiderEdge cyc u hu) (add_comm 1 a)
  have hnewShift : χ (outsiderEdge (shiftedCycle cyc a) u hshift 0) ∈
      newColors χ u := by
    rw [shifted_outsiderEdge cyc u hu a 0, zero_add]
    exact hnewOutside
  have hspokesShift : χ (outsiderEdge (shiftedCycle cyc a) u hshift 0) ≠
      χ (outsiderEdge (shiftedCycle cyc a) u hshift 1) := by
    rw [hspoke, shifted_outsiderEdge cyc u hu a 0, zero_add]
    exact hspokes
  have hbeta : χ (outsiderEdge (shiftedCycle cyc a) u hshift 1) ≠
      restrictedColor χ r ((shiftedCycle cyc a).mapEdgeSet
        (sourceStep (⟨1, by omega⟩ : Fin m))) := by
    rw [hspoke, shifted_step_one_eq_next_step_zero hm]
    exact hnext
  obtain ⟨f, hf⟩ := positive_outside_new_initial_insertion_copy hm χ r
    (shiftedCycle cyc a) u hshift hnewShift hspokesShift hbeta
  exact hnone f hf

end ErdosProblems.AntiRamseyCycleClaimOneOutsideInsertion
