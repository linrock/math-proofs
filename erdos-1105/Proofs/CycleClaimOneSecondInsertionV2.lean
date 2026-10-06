module

public import CycleClaimOneFirstInsertion
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-!
Choi Claim 1 Case A (second-insertion branch): extends a selected `(m + 1)`-cycle
with an outside selected attachment whose color is NEW at the cycle endpoint to a
rainbow `(m + 2)`-cycle in the host coloring.
-/

namespace ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
export ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion (outsiderEdge)

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Repeating a selected outgoing edge color on the first spoke forces
that color to be NEW at the first cycle endpoint, for the same arbitrary
choice `r`. This supplies the NEW premise of the deleted-edge insertion. -/
theorem deleted_edge_color_new_at_first {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hfirstEq : χ (outsiderEdge cyc u hu 0) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m)))) :
    χ (outsiderEdge cyc u hu 0) ∈ newColors χ (cyc.toHom 0) := by
  let e := cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m))
  obtain ⟨v, hve, hnew⟩ :=
    arbitrary_selected_edge_has_new_endpoint χ r e
  have hinc := newColor_every_edge_incident χ v hnew
    (outsiderEdge cyc u hu 0) hfirstEq
  have hcases : v = u ∨ v = cyc.toHom 0 := by
    simpa only [outsiderEdge, Sym2.mem_iff] using hinc
  rcases hcases with hvu | hvzero
  · subst v
    change u ∈ Sym2.map cyc.toHom
      (sourceStep (⟨0, by omega⟩ : Fin m)).val at hve
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hve
    exact False.elim (hu ⟨i, hi⟩)
  · subst v
    simpa only [hfirstEq] using hnew

/-- Insert the outside vertex at position one: the order is
`(v₁,u,v₂,…,vₘ₊₁)`. -/
def deletedInsertionMap {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) : Fin ((m + 1) + 1) → Fin n :=
  Fin.insertNth (α := fun _ => Fin n)
    (1 : Fin ((m + 1) + 1)) u cyc.toHom

theorem deletedInsertionMap_zero {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    deletedInsertionMap cyc u 0 = cyc.toHom 0 := by
  have h : Fin.insertNth (α := fun _ => Fin n)
      (1 : Fin ((m + 1) + 1)) u cyc.toHom
      ((1 : Fin ((m + 1) + 1)).succAbove (0 : Fin (m + 1))) =
        cyc.toHom 0 :=
    Fin.insertNth_apply_succAbove (α := fun _ => Fin n)
      (1 : Fin ((m + 1) + 1)) u cyc.toHom 0
  simpa only [deletedInsertionMap, Fin.one_succAbove_zero] using h

theorem deletedInsertionMap_one {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    deletedInsertionMap cyc u 1 = u := by
  simp only [deletedInsertionMap, Fin.insertNth_apply_same]

theorem deletedInsertionMap_succ_of_pos {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (j : Fin (m + 1)) (hj : 1 ≤ j.val) :
    deletedInsertionMap cyc u (Fin.succ j) = cyc.toHom j := by
  have hone : ((1 : Fin ((m + 1) + 1)) : ℕ) = 1 := by
    have hlt : 1 < (m + 1) + 1 := by omega
    rw [Fin.val_one' ((m + 1) + 1), Nat.mod_eq_of_lt hlt]
  have hlt : (1 : Fin ((m + 1) + 1)) < Fin.succ j := by
    simp only [Fin.lt_def, Fin.val_succ]
    rw [hone]
    omega
  unfold deletedInsertionMap
  rw [← Fin.succAbove_of_lt_succ _ _ hlt]
  exact Fin.insertNth_apply_succAbove (α := fun _ => Fin n)
    (1 : Fin ((m + 1) + 1)) u cyc.toHom j

/-- Every host step after the two inserted spokes is exactly a selected
source-cycle step, with the latter index one smaller. -/
theorem deletedInsertionMap_step_ge_two {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (i : Fin (m + 1)) (hi : 2 ≤ i.val) :
    ∃ j : Fin m, j.val + 1 = i.val ∧ 1 ≤ j.val ∧
      Sym2.map (deletedInsertionMap cyc u) (sourceStep i).val =
        Sym2.map cyc.toHom (sourceStep j).val := by
  let j : Fin m := ⟨i.val - 1, by omega⟩
  have hjEq : j.val + 1 = i.val := by dsimp [j]; omega
  have hj : 1 ≤ j.val := by dsimp [j]; omega
  refine ⟨j, hjEq, hj, ?_⟩
  have hloIndex : Fin.castSucc i = Fin.succ (Fin.castSucc j) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ]
    dsimp [j]
    omega
  have hhiIndex : Fin.succ i = Fin.succ (Fin.succ j) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp [j]
    omega
  have hlo : deletedInsertionMap cyc u (Fin.castSucc i) =
      cyc.toHom (Fin.castSucc j) := by
    rw [hloIndex]
    exact deletedInsertionMap_succ_of_pos cyc u (Fin.castSucc j)
      (by simpa only [Fin.val_castSucc] using hj)
  have hhi : deletedInsertionMap cyc u (Fin.succ i) =
      cyc.toHom (Fin.succ j) := by
    rw [hhiIndex]
    exact deletedInsertionMap_succ_of_pos cyc u (Fin.succ j)
      (by simp only [Fin.val_succ]; omega)
  simp only [sourceStep, Sym2.map_mk]
  rw [hlo, hhi]

/-- The closing host edge is precisely the selected source-cycle closing
edge. -/
theorem deletedInsertionMap_closing {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    Sym2.map (deletedInsertionMap cyc u)
      (sourceClosing (m + 1) (by omega)).val =
    Sym2.map cyc.toHom (sourceClosing m hm).val := by
  have hlastIndex : Fin.last (m + 1) = Fin.succ (Fin.last m) := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_succ]
  have hlast : deletedInsertionMap cyc u (Fin.last (m + 1)) =
      cyc.toHom (Fin.last m) := by
    rw [hlastIndex]
    exact deletedInsertionMap_succ_of_pos cyc u (Fin.last m)
      (by simp only [Fin.val_last]; omega)
  simp only [sourceClosing, Sym2.map_mk]
  rw [deletedInsertionMap_zero, hlast]

theorem deletedInsertionMap_first_spoke {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (deletedInsertionMap cyc u)
      (sourceStep (0 : Fin (m + 1))).val =
      (outsiderEdge cyc u hu 0).val := by
  change s(deletedInsertionMap cyc u 0,
      deletedInsertionMap cyc u 1) = s(u, cyc.toHom 0)
  rw [deletedInsertionMap_zero, deletedInsertionMap_one]
  exact Sym2.eq_swap

theorem deletedInsertionMap_second_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (deletedInsertionMap cyc u)
      (sourceStep (1 : Fin (m + 1))).val =
      (outsiderEdge cyc u hu 1).val := by
  simp only [sourceStep, outsiderEdge, Sym2.map_mk]
  have honeSmall : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    have hlt : 1 < m + 1 := by omega
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt hlt]
  have honeLarge : ((1 : Fin ((m + 1) + 1)) : ℕ) = 1 := by
    have hlt : 1 < (m + 1) + 1 := by omega
    rw [Fin.val_one' ((m + 1) + 1), Nat.mod_eq_of_lt hlt]
  have hcast : Fin.castSucc (1 : Fin (m + 1)) =
      (1 : Fin ((m + 1) + 1)) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, honeSmall, honeLarge]
  rw [hcast]
  rw [deletedInsertionMap_one]
  have hpos : 1 ≤ (1 : Fin (m + 1)).val := by
    rw [honeSmall]
  rw [deletedInsertionMap_succ_of_pos cyc u 1 hpos]

theorem deletedInsertionMap_injective {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Function.Injective (deletedInsertionMap cyc u) := by
  intro a b hab
  let t : Fin ((m + 1) + 1) := 1
  by_cases ha : a = t
  · subst a
    by_cases hb : b = t
    · exact hb.symm
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := t) hb
      subst b
      have hbad : u = cyc.toHom j := by
        simpa only [deletedInsertionMap, t, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] using hab
      exact False.elim (hu ⟨j, hbad.symm⟩)
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (y := t) ha
    subst a
    by_cases hb : b = t
    · subst b
      have hbad : cyc.toHom i = u := by
        simpa only [deletedInsertionMap, t, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] using hab
      exact False.elim (hu ⟨i, hbad⟩)
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := t) hb
      subst b
      have hij : cyc.toHom i = cyc.toHom j := by
        simpa only [deletedInsertionMap, t,
          Fin.insertNth_apply_succAbove] using hab
      rw [cyc.injective hij]

/-- Generalized positive insertion when the first spoke repeats exactly the
selected edge deleted by the insertion. Its selected NEW owner is derived
at the first endpoint; the spoke itself is not assumed selected. -/
theorem positive_deleted_edge_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hfirstEq : χ (outsiderEdge cyc u hu 0) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m))))
    (hbeta : χ (outsiderEdge cyc u hu 1) ≠
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  have hnewFirst : χ (outsiderEdge cyc u hu 0) ∈
      newColors χ (cyc.toHom 0) :=
    deleted_edge_color_new_at_first hm χ r cyc u hu hfirstEq
  let p := deletedInsertionMap cyc u
  have hp : Function.Injective p :=
    deletedInsertionMap_injective cyc u hu
  let φ : (cycleGraph ((m + 1) + 1)) →g
      (⊤ : SimpleGraph (Fin n)) :=
    ⟨p, by
      intro a b hab
      exact (top_adj _ _).mpr
        (hp.ne ((cycleGraph ((m + 1) + 1)).ne_of_adj hab))⟩
  let f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)) := ⟨φ, hp⟩

  have honeSmall : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    have hlt : 1 < m + 1 := by omega
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt hlt]

  let closing : (selectedGraph χ r).edgeSet :=
    cyc.mapEdgeSet (sourceClosing m hm)
  have hαβ : χ (outsiderEdge cyc u hu 0) ≠
      χ (outsiderEdge cyc u hu 1) := by
    intro heq
    have hinc := newColor_every_edge_incident χ
      (cyc.toHom 0) hnewFirst (outsiderEdge cyc u hu 1) heq.symm
    have hcases : cyc.toHom 0 = u ∨
        cyc.toHom 0 = cyc.toHom 1 := by
      simpa only [outsiderEdge, Sym2.mem_iff] using hinc
    rcases hcases with h | h
    · exact hu ⟨0, h⟩
    · have h01 : (0 : Fin (m + 1)) = 1 := cyc.injective h
      have hval : (0 : ℕ) = 1 := by
        simpa only [Fin.val_zero, honeSmall] using congrArg Fin.val h01
      exact Nat.zero_ne_one hval
  have huSelected (e : (cycleGraph (m + 1)).edgeSet) :
      u ∉ (cyc.mapEdgeSet e).val := by
    intro he
    change u ∈ Sym2.map cyc.toHom e.val at he
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp he
    exact hu ⟨i, hi⟩
  have hαRetained (e : (cycleGraph (m + 1)).edgeSet)
      (he : sourceStep (⟨0, by omega⟩ : Fin m) ≠ e) :
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet e) := by
    intro heq
    have hcolors := hfirstEq.symm.trans heq
    have hmaps := restrictedColor_injective χ r hcolors
    exact he (cyc.mapEdgeSet.injective hmaps)
  have hαStep (j : Fin m) (hj : 1 ≤ j.val) :
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    apply hαRetained (sourceStep j)
    intro heq
    have hidx := sourceStep_injective heq
    have hval := congrArg Fin.val hidx
    change 0 = j.val at hval
    omega
  have hαclosing : χ (outsiderEdge cyc u hu 0) ≠
      restrictedColor χ r closing :=
    hαRetained (sourceClosing m hm)
      (sourceStep_ne_closing hm (⟨0, by omega⟩ : Fin m))
  have hβAvoid (e : (cycleGraph (m + 1)).edgeSet)
      (hv : cyc.toHom 1 ∉ (cyc.mapEdgeSet e).val) :
      χ (outsiderEdge cyc u hu 1) ≠
        restrictedColor χ r (cyc.mapEdgeSet e) := by
    intro heq
    have hdisj : ∀ v : Fin n, v ∈ (cyc.mapEdgeSet e).val →
        v ∉ (outsiderEdge cyc u hu 1).val := by
      intro v hve hvspoke
      have hcases : v = u ∨ v = cyc.toHom 1 := by
        simpa only [outsiderEdge, Sym2.mem_iff] using hvspoke
      rcases hcases with h | h
      · subst v
        exact huSelected e hve
      · subst v
        exact hv hve
    exact (arbitrary_selected_edge_ne_disjoint_host_edge χ r
      (cyc.mapEdgeSet e) (outsiderEdge cyc u hu 1) hdisj) heq.symm
  have hcycleColors : Function.Injective
      (fun e : (cycleGraph (m + 1)).edgeSet =>
        restrictedColor χ r (cyc.mapEdgeSet e)) :=
    (restrictedColor_injective χ r).comp cyc.mapEdgeSet.injective

  let L := EdgeLabeling.pullback χ f.toHom
  let α : C := χ (outsiderEdge cyc u hu 0)
  let β : C := χ (outsiderEdge cyc u hu 1)
  have hcolor_of_host
      (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : HostEdge n)
      (hval : Sym2.map p e.val = d.val) : L e = χ d := by
    have hedges : f.toHom.mapEdgeSet e = d := by
      apply Subtype.ext
      change Sym2.map p e.val = d.val
      exact hval
    simpa only [L, EdgeLabeling.pullback_apply] using congrArg χ hedges
  have hcolor_of_selected
      (e : (cycleGraph ((m + 1) + 1)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map p e.val = Sym2.map cyc.toHom d.val) :
      L e = restrictedColor χ r (cyc.mapEdgeSet d) := by
    let selectedHostEdge : HostEdge n :=
      ⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
    have hedges : f.toHom.mapEdgeSet e = selectedHostEdge := by
      apply Subtype.ext
      change Sym2.map p e.val = Sym2.map cyc.toHom d.val
      exact hval
    simpa only [L, EdgeLabeling.pullback_apply, restrictedColor,
      selectedHostEdge] using congrArg χ hedges
  have hstep0 : L (sourceStep (0 : Fin (m + 1))) =
      χ (outsiderEdge cyc u hu 0) :=
    hcolor_of_host _ _ (deletedInsertionMap_first_spoke cyc u hu)
  have hstep1 : L (sourceStep (1 : Fin (m + 1))) =
      χ (outsiderEdge cyc u hu 1) :=
    hcolor_of_host _ _ (deletedInsertionMap_second_spoke hm cyc u hu)
  have htail (i : Fin (m + 1)) (hi : 2 ≤ i.val) :
      ∃ j : Fin m, j.val + 1 = i.val ∧ 1 ≤ j.val ∧
        L (sourceStep i) =
          restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    obtain ⟨j, hjEq, hj, hval⟩ :=
      deletedInsertionMap_step_ge_two cyc u i hi
    exact ⟨j, hjEq, hj, hcolor_of_selected _ _ hval⟩
  have hclose : L (sourceClosing (m + 1) (by omega)) =
      restrictedColor χ r closing :=
    hcolor_of_selected _ _ (deletedInsertionMap_closing hm cyc u)

  have hv1NotStep (j : Fin m) (hj : 2 ≤ j.val) :
      cyc.toHom 1 ∉ (cyc.mapEdgeSet (sourceStep j)).val := by
    intro hv
    change cyc.toHom 1 ∈
      Sym2.map cyc.toHom (sourceStep j).val at hv
    obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
    have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
    subst k
    change (1 : Fin (m + 1)) ∈
      s(Fin.castSucc j, Fin.succ j) at hk
    rcases Sym2.mem_iff.mp hk with h | h
    · have hidx : (1 : Fin (m + 1)) = Fin.castSucc j := h
      have hval : (1 : ℕ) = j.val := by
        simpa only [honeSmall, Fin.val_castSucc] using congrArg Fin.val hidx
      omega
    · have hidx : (1 : Fin (m + 1)) = Fin.succ j := h
      have hval : (1 : ℕ) = j.val + 1 := by
        simpa only [honeSmall, Fin.val_succ] using congrArg Fin.val hidx
      omega
  have hv1NotClosing : cyc.toHom 1 ∉ closing.val := by
    intro hv
    change cyc.toHom 1 ∈
      Sym2.map cyc.toHom (sourceClosing m hm).val at hv
    obtain ⟨k, hk, hk1⟩ := Sym2.mem_map.mp hv
    have hkey : k = (1 : Fin (m + 1)) := cyc.injective hk1
    subst k
    change (1 : Fin (m + 1)) ∈
      s((0 : Fin (m + 1)), Fin.last m) at hk
    rcases Sym2.mem_iff.mp hk with h | h
    · have hidx : (1 : Fin (m + 1)) = 0 := h
      have hval : (1 : ℕ) = 0 := by
        simpa only [honeSmall, Fin.val_zero] using congrArg Fin.val hidx
      exact Nat.one_ne_zero hval
    · have hidx : (1 : Fin (m + 1)) = Fin.last m := h
      have hval : (1 : ℕ) = m := by
        simpa only [honeSmall, Fin.val_last] using congrArg Fin.val hidx
      omega

  have hβStep (j : Fin m) (hj : 1 ≤ j.val) :
      β ≠ restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    by_cases hj1 : j.val = 1
    · have hjEq : j = (⟨1, by omega⟩ : Fin m) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hj1
      rw [hjEq]
      exact hbeta
    · have hj2 : 2 ≤ j.val := by omega
      exact hβAvoid (sourceStep j) (hv1NotStep j hj2)

  let hostClosing : (cycleGraph ((m + 1) + 1)).edgeSet :=
    sourceClosing (m + 1) (by omega)
  have hClass (e : (cycleGraph ((m + 1) + 1)).edgeSet) :
      (e = sourceStep (0 : Fin (m + 1)) ∧ L e = α) ∨
      (e = sourceStep (1 : Fin (m + 1)) ∧ L e = β) ∨
      (∃ j : Fin m, 1 ≤ j.val ∧
        e = sourceStep (Fin.succ j) ∧
        L e = restrictedColor χ r (cyc.mapEdgeSet (sourceStep j))) ∨
      (e = hostClosing ∧ L e = restrictedColor χ r closing) := by
    rcases sourceEdge_cases (m := m + 1) (by omega) e with
      ⟨i, he⟩ | he
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
          apply hi0
          apply Fin.ext
          simpa only [Fin.val_zero] using h
        have hne1 : i.val ≠ 1 := by
          intro h
          apply hi1
          apply Fin.ext
          simpa only [honeSmall] using h
        omega
      obtain ⟨j, hjEq, hj, hcol⟩ := htail i hi
      have hij : i = Fin.succ j := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      subst i
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, rfl, hcol⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨he, by rw [he]; exact hclose⟩))

  have hβclosing : β ≠ restrictedColor χ r closing :=
    hβAvoid (sourceClosing m hm) hv1NotClosing

  -- Each of the four source-edge classes has a literal original-host color.
  -- The remaining palette proof uses only the eight unordered collisions.
  have hpalette : Function.Injective
      (EdgeLabeling.pullback χ f.toHom) := by
    change Function.Injective L
    intro e₁ e₂ heq
    rcases hClass e₁ with hA₁ | hB₁ | hT₁ | hC₁
    · obtain ⟨hs₁, hc₁⟩ := hA₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · exact hs₁.trans hA₂.1.symm
      · have hcolors : α = β :=
          hc₁.symm.trans (heq.trans hB₂.2)
        exact False.elim (hαβ hcolors)
      · obtain ⟨j, hj, _, hc₂⟩ := hT₂
        have hcolors : α =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        exact False.elim (hαStep j hj hcolors)
      · have hcolors : α = restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        exact False.elim (hαclosing hcolors)
    · obtain ⟨hs₁, hc₁⟩ := hB₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α = β :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαβ hcolors)
      · exact hs₁.trans hB₂.1.symm
      · obtain ⟨j, hj, _, hc₂⟩ := hT₂
        have hcolors : β =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        exact False.elim (hβStep j hj hcolors)
      · have hcolors : β = restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        exact False.elim (hβclosing hcolors)
    · obtain ⟨i, hi, hs₁, hc₁⟩ := hT₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαStep i hi hcolors)
      · have hcolors : β =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) :=
          hB₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hβStep i hi hcolors)
      · obtain ⟨j, _, hs₂, hc₂⟩ := hT₂
        have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) =
              restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        have hij : i = j :=
          sourceStep_injective (hcycleColors hcolors)
        subst j
        exact hs₁.trans hs₂.symm
      · have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep i)) =
              restrictedColor χ r closing :=
          hc₁.symm.trans (heq.trans hC₂.2)
        have hsource : sourceStep i = sourceClosing m hm :=
          hcycleColors hcolors
        exact False.elim (sourceStep_ne_closing hm i hsource)
    · obtain ⟨hs₁, hc₁⟩ := hC₁
      rcases hClass e₂ with hA₂ | hB₂ | hT₂ | hC₂
      · have hcolors : α = restrictedColor χ r closing :=
          hA₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hαclosing hcolors)
      · have hcolors : β = restrictedColor χ r closing :=
          hB₂.2.symm.trans (heq.symm.trans hc₁)
        exact False.elim (hβclosing hcolors)
      · obtain ⟨j, _, _, hc₂⟩ := hT₂
        have hcolors :
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) =
              restrictedColor χ r closing :=
          hc₂.symm.trans (heq.symm.trans hc₁)
        have hsource : sourceStep j = sourceClosing m hm :=
          hcycleColors hcolors
        exact False.elim (sourceStep_ne_closing hm j hsource)
      · exact hs₁.trans hC₂.1.symm

  exact ⟨f, hpalette⟩

/-- Translate the source cycle by an arbitrary cyclic position. The exact
Mathlib `finCycle` permutation is used, and ordinary graph adjacency is
preserved through subtraction in the cyclic group. -/
noncomputable def shiftedCycle {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (a : Fin (m + 1)) :
    (cycleGraph (m + 1)).Copy (selectedGraph χ r) :=
  cyc.comp
    ⟨⟨finCycle a, by
        intro i j hij
        rw [cycleGraph_adj'] at hij ⊢
        simpa only [finCycle_apply, add_sub_add_right_eq_sub] using hij⟩,
      (finCycle a).injective⟩

theorem shiftedCycle_apply {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (a i : Fin (m + 1)) :
    (shiftedCycle cyc a).toHom i = cyc.toHom (i + a) := rfl

theorem shiftedCycle_zero {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) :
    shiftedCycle cyc 0 = cyc := by
  apply DFunLike.ext
  intro i
  change cyc.toHom (i + 0) = cyc.toHom i
  rw [add_zero]

/-- Translating a selected cycle does not change its vertex range. Only
the forward direction is needed for the outside-vertex condition. -/
theorem shifted_outside {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (a : Fin (m + 1)) :
    u ∉ Set.range (shiftedCycle cyc a).toHom := by
  rintro ⟨i, hi⟩
  exact hu ⟨i + a, hi⟩

theorem shifted_outsiderEdge {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (a i : Fin (m + 1)) :
    outsiderEdge (shiftedCycle cyc a) u (shifted_outside cyc u hu a) i =
      outsiderEdge cyc u hu (i + a) := by
  apply Subtype.ext
  rfl

/-- At a cyclic position `a`, the second retained source step is the
first source step of the cycle shifted once further. This statement also
handles the last source position, where cyclic addition wraps to zero. -/
theorem shifted_step_one_eq_next_step_zero {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (a : Fin (m + 1)) :
    (shiftedCycle cyc a).mapEdgeSet
        (sourceStep (⟨1, by omega⟩ : Fin m)) =
      (shiftedCycle cyc (a + 1)).mapEdgeSet
        (sourceStep (⟨0, by omega⟩ : Fin m)) := by
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hcast0 : Fin.castSucc (⟨0, by omega⟩ : Fin m) =
      (0 : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  have hsucc0 : Fin.succ (⟨0, by omega⟩ : Fin m) =
      (1 : Fin (m + 1)) := by
    apply Fin.ext
    simpa only [Fin.val_succ, Fin.val_mk] using hone.symm
  have hcast1 : Fin.castSucc (⟨1, by omega⟩ : Fin m) =
      (1 : Fin (m + 1)) := by
    apply Fin.ext
    simpa only [Fin.val_castSucc, Fin.val_mk] using hone.symm
  have hsucc1 : Fin.succ (⟨1, by omega⟩ : Fin m) =
      (1 : Fin (m + 1)) + 1 := by
    apply Fin.ext
    rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by omega)]
    rfl
  apply Subtype.ext
  change s(cyc.toHom (Fin.castSucc (⟨1, by omega⟩ : Fin m) + a),
      cyc.toHom (Fin.succ (⟨1, by omega⟩ : Fin m) + a)) =
    s(cyc.toHom (Fin.castSucc (⟨0, by omega⟩ : Fin m) + (a + 1)),
      cyc.toHom (Fin.succ (⟨0, by omega⟩ : Fin m) + (a + 1)))
  rw [hcast1, hsucc1, hcast0, hsucc0]
  simp only [zero_add, add_comm, add_left_comm]

/-- The literal selected outgoing edge color at a cyclic source position.
For the final position this is the selected closing edge color. -/
noncomputable def cycleOutgoingColor {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (a : Fin (m + 1)) : C :=
  restrictedColor χ r ((shiftedCycle cyc a).mapEdgeSet
    (sourceStep (⟨0, by omega⟩ : Fin m)))

theorem cycleOutgoingColor_zero {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) :
    cycleOutgoingColor hm χ r cyc 0 = restrictedColor χ r
      (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m))) := by
  unfold cycleOutgoingColor
  rw [shiftedCycle_zero]

/-- If no literal rainbow host cycle exists, a spoke repeating the selected
outgoing color forces the next spoke to repeat the next outgoing color.
The first spoke is never assumed to be a selected edge. -/
theorem no_rainbow_forces_next_repeat {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ)
    (a : Fin (m + 1))
    (hfirst : χ (outsiderEdge cyc u hu a) =
      cycleOutgoingColor hm χ r cyc a) :
    χ (outsiderEdge cyc u hu (a + 1)) =
      cycleOutgoingColor hm χ r cyc (a + 1) := by
  by_contra hnext
  have hshift := shifted_outside cyc u hu a
  have hfirstEq :
      χ (outsiderEdge (shiftedCycle cyc a) u hshift 0) =
        restrictedColor χ r ((shiftedCycle cyc a).mapEdgeSet
          (sourceStep (⟨0, by omega⟩ : Fin m))) := by
    rw [shifted_outsiderEdge cyc u hu a 0, zero_add]
    exact hfirst
  have hspoke : outsiderEdge (shiftedCycle cyc a) u hshift 1 =
      outsiderEdge cyc u hu (a + 1) := by
    calc
      outsiderEdge (shiftedCycle cyc a) u hshift 1 =
          outsiderEdge cyc u hu (1 + a) :=
        shifted_outsiderEdge cyc u hu a 1
      _ = outsiderEdge cyc u hu (a + 1) :=
        congrArg (outsiderEdge cyc u hu) (add_comm 1 a)
  have hbeta : χ (outsiderEdge (shiftedCycle cyc a) u hshift 1) ≠
      restrictedColor χ r ((shiftedCycle cyc a).mapEdgeSet
        (sourceStep (⟨1, by omega⟩ : Fin m))) := by
    rw [hspoke, shifted_step_one_eq_next_step_zero hm]
    exact hnext
  obtain ⟨f, hf⟩ := positive_deleted_edge_insertion_copy hm χ r
    (shiftedCycle cyc a) u hshift hfirstEq hbeta
  exact hnone f hf

/-- The selected attachment color differs from every selected source-cycle
edge, including the incident first and closing edges. This uses selected
color injection for the same arbitrary `NewChoice`, not only NEW incidence. -/
theorem selected_attachment_color_ne_cycle_color {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (e : (cycleGraph (m + 1)).edgeSet) :
    χ (outsiderEdge cyc u hu 0) ≠
      restrictedColor χ r (cyc.mapEdgeSet e) := by
  let a : (selectedGraph χ r).edgeSet :=
    ⟨s(u, cyc.toHom 0), hattach⟩
  have haColor : χ (outsiderEdge cyc u hu 0) =
      restrictedColor χ r a := by
    simp [outsiderEdge, restrictedColor, a]
  intro heq
  have hae : a = cyc.mapEdgeSet e :=
    restrictedColor_injective χ r (haColor.symm.trans heq)
  have hua : u ∈ a.val := by
    simp [a, Sym2.mem_iff]
  have hue : u ∈ (cyc.mapEdgeSet e).val := hae ▸ hua
  change u ∈ Sym2.map cyc.toHom e.val at hue
  obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hue
  exact hu ⟨i, hi⟩

/-- Choi Claim 1 Case A, the second branch after `beta2=c2`. No inequality
on any later spoke is assumed: each non-rainbow insertion forces the next
repeat, and the final insertion conflicts with the selected attachment.
The inherited NEW-at-first hypothesis is retained although this branch
already derives all later NEW ownership from the repeated selected colors. -/
theorem positive_second_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (_hnewFirst : χ (outsiderEdge cyc u hu 0) ∈
      newColors χ (cyc.toHom 0))
    (hbetaEq : χ (outsiderEdge cyc u hu 1) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  by_contra hnoneExists
  have hnone : ∀ f : (cycleGraph ((m + 1) + 1)).Copy
      (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ := by
    intro f hf
    exact hnoneExists ⟨f, hf⟩
  have hbetaOne : χ (outsiderEdge cyc u hu 1) =
      cycleOutgoingColor hm χ r cyc 1 := by
    have hstep := shifted_step_one_eq_next_step_zero hm cyc
      (0 : Fin (m + 1))
    rw [shiftedCycle_zero, zero_add] at hstep
    simpa only [cycleOutgoingColor, ← hstep] using hbetaEq
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hall : ∀ j : ℕ, ∀ hj : j < m,
      χ (outsiderEdge cyc u hu (⟨j + 1, by omega⟩ : Fin (m + 1))) =
        cycleOutgoingColor hm χ r cyc (⟨j + 1, by omega⟩ : Fin (m + 1)) := by
    intro j
    induction j with
    | zero =>
        intro hj
        have heq : (⟨0 + 1, by omega⟩ : Fin (m + 1)) = 1 := by
          apply Fin.ext
          exact hone.symm
        simpa only [heq] using hbetaOne
    | succ j ih =>
        intro hj
        have hjprev : j < m := by omega
        let a : Fin (m + 1) := ⟨j + 1, by omega⟩
        have hthis : χ (outsiderEdge cyc u hu a) =
            cycleOutgoingColor hm χ r cyc a := ih hjprev
        have hnext := no_rainbow_forces_next_repeat hm χ r cyc u hu
          hnone a hthis
        have ha : a + 1 = (⟨j + 1 + 1, by omega⟩ : Fin (m + 1)) := by
          apply Fin.ext
          rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by dsimp [a]; omega)]
        simpa only [ha, Nat.succ_eq_add_one] using hnext
  have hlast := hall (m - 1) (by omega)
  have hlastIndex : (⟨m - 1 + 1, by omega⟩ : Fin (m + 1)) =
      Fin.last m := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  rw [hlastIndex] at hlast
  have hzero := no_rainbow_forces_next_repeat hm χ r cyc u hu
    hnone (Fin.last m) hlast
  have hwrap : (Fin.last m : Fin (m + 1)) + 1 = 0 := by
    simpa only [finRotate_apply] using (finRotate_last (n := m))
  rw [hwrap, cycleOutgoingColor_zero] at hzero
  exact selected_attachment_color_ne_cycle_color χ r cyc u hu hattach
    (sourceStep (⟨0, by omega⟩ : Fin m)) hzero

/-- Complete local Case A of Choi Claim 1. The first selected attachment
color is NEW at the selected cycle endpoint. The imported first insertion
handles the unequal branch, and the second insertion theorem above handles
the equal branch with no further spoke guard. -/
theorem positive_first_endpoint_attachment_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (hnewFirst : χ (outsiderEdge cyc u hu 0) ∈
      newColors χ (cyc.toHom 0)) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  by_cases hbeta : χ (outsiderEdge cyc u hu 1) =
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))
  · exact positive_second_insertion_copy hm χ r cyc u hu
      hattach hnewFirst hbeta
  · exact positive_first_insertion_copy hm χ r cyc u hu
      hattach hnewFirst hbeta

end ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion
