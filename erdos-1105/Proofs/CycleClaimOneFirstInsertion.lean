module

public import CycleNewChoiceExchange
public import CycleOrderedEdges
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
The arbitrary choice, selected NEW endpoint, and the two
spokes are literal Formal Conjectures objects. The palette proof is factored into source-edge normal forms and explicit
original-host color collision checks for the next bounded diagnostic.
-/

namespace ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A complete-host spoke to a vertex of a selected cycle, with its required
distinctness derived from the outside-vertex condition. -/
def outsiderEdge {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (i : Fin (m + 1)) : HostEdge n :=
  ⟨s(u, cyc.toHom i), (top_adj _ _).mpr (by
    intro h
    exact hu ⟨i, h.symm⟩)⟩

/-- The fixed-choice selected-endpoint theorem does not apply to an arbitrary
`NewChoice`. This is the needed local analogue, proved directly from the
choice's color equality and the checked vertex-deletion semantics. -/
theorem arbitrary_selected_edge_has_new_endpoint
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : (selectedGraph χ r).edgeSet) :
    ∃ v : Fin n, v ∈ e.val ∧
      restrictedColor χ r e ∈ newColors χ v := by
  have he : e.val ∈
      Set.range (fun d : newColorUnion χ => (r.edge d).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e.property
  obtain ⟨d, hd⟩ := he
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp d.property
  have hval : e.val = (r.edge d).val := hd.symm
  have hcolor : restrictedColor χ r e = d.val := by
    simpa [restrictedColor, hval] using r.color_eq d
  have hinc : v ∈ e.val := by
    rw [hval]
    exact newColor_every_edge_incident χ v hv (r.edge d) (r.color_eq d)
  exact ⟨v, hinc, by simpa only [hcolor] using hv⟩

/-- A complete-host edge disjoint from an arbitrary selected edge cannot
repeat the selected edge's label. -/
theorem arbitrary_selected_edge_ne_disjoint_host_edge
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (e : (selectedGraph χ r).edgeSet) (f : HostEdge n)
    (hdisj : ∀ v : Fin n, v ∈ e.val → v ∉ f.val) :
    restrictedColor χ r e ≠ χ f := by
  obtain ⟨v, hve, hnew⟩ :=
    arbitrary_selected_edge_has_new_endpoint χ r e
  intro heq
  have hvf := newColor_every_edge_incident χ v hnew f heq.symm
  exact (hdisj v hve) hvf

/-- Insert the outside vertex at position one: the order is
`(v₁,u,v₂,…,vₘ₊₁)`. -/
def firstInsertionMap {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) : Fin ((m + 1) + 1) → Fin n :=
  Fin.insertNth (α := fun _ => Fin n)
    (1 : Fin ((m + 1) + 1)) u cyc.toHom

theorem firstInsertionMap_zero {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    firstInsertionMap cyc u 0 = cyc.toHom 0 := by
  have h : Fin.insertNth (α := fun _ => Fin n)
      (1 : Fin ((m + 1) + 1)) u cyc.toHom
      ((1 : Fin ((m + 1) + 1)).succAbove (0 : Fin (m + 1))) =
        cyc.toHom 0 :=
    Fin.insertNth_apply_succAbove (α := fun _ => Fin n)
      (1 : Fin ((m + 1) + 1)) u cyc.toHom 0
  simpa only [firstInsertionMap, Fin.one_succAbove_zero] using h

theorem firstInsertionMap_one {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    firstInsertionMap cyc u 1 = u := by
  simp only [firstInsertionMap, Fin.insertNth_apply_same]

theorem firstInsertionMap_succ_of_pos {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (j : Fin (m + 1)) (hj : 1 ≤ j.val) :
    firstInsertionMap cyc u (Fin.succ j) = cyc.toHom j := by
  have hone : ((1 : Fin ((m + 1) + 1)) : ℕ) = 1 := by
    have hlt : 1 < (m + 1) + 1 := by omega
    rw [Fin.val_one' ((m + 1) + 1), Nat.mod_eq_of_lt hlt]
  have hlt : (1 : Fin ((m + 1) + 1)) < Fin.succ j := by
    simp only [Fin.lt_def, Fin.val_succ]
    rw [hone]
    omega
  unfold firstInsertionMap
  rw [← Fin.succAbove_of_lt_succ _ _ hlt]
  exact Fin.insertNth_apply_succAbove (α := fun _ => Fin n)
    (1 : Fin ((m + 1) + 1)) u cyc.toHom j

/-- Every host step after the two inserted spokes is exactly a selected
source-cycle step, with the latter index one smaller. -/
theorem firstInsertionMap_step_ge_two {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (i : Fin (m + 1)) (hi : 2 ≤ i.val) :
    ∃ j : Fin m, j.val + 1 = i.val ∧ 1 ≤ j.val ∧
      Sym2.map (firstInsertionMap cyc u) (sourceStep i).val =
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
  have hlo : firstInsertionMap cyc u (Fin.castSucc i) =
      cyc.toHom (Fin.castSucc j) := by
    rw [hloIndex]
    exact firstInsertionMap_succ_of_pos cyc u (Fin.castSucc j)
      (by simpa only [Fin.val_castSucc] using hj)
  have hhi : firstInsertionMap cyc u (Fin.succ i) =
      cyc.toHom (Fin.succ j) := by
    rw [hhiIndex]
    exact firstInsertionMap_succ_of_pos cyc u (Fin.succ j)
      (by simp only [Fin.val_succ]; omega)
  simp only [sourceStep, Sym2.map_mk]
  rw [hlo, hhi]

/-- The closing host edge is precisely the selected source-cycle closing
edge. -/
theorem firstInsertionMap_closing {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) :
    Sym2.map (firstInsertionMap cyc u)
      (sourceClosing (m + 1) (by omega)).val =
    Sym2.map cyc.toHom (sourceClosing m hm).val := by
  have hlastIndex : Fin.last (m + 1) = Fin.succ (Fin.last m) := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_succ]
  have hlast : firstInsertionMap cyc u (Fin.last (m + 1)) =
      cyc.toHom (Fin.last m) := by
    rw [hlastIndex]
    exact firstInsertionMap_succ_of_pos cyc u (Fin.last m)
      (by simp only [Fin.val_last]; omega)
  simp only [sourceClosing, Sym2.map_mk]
  rw [firstInsertionMap_zero, hlast]

theorem firstInsertionMap_first_spoke {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (firstInsertionMap cyc u)
      (sourceStep (0 : Fin (m + 1))).val =
      (outsiderEdge cyc u hu 0).val := by
  change s(firstInsertionMap cyc u 0,
      firstInsertionMap cyc u 1) = s(u, cyc.toHom 0)
  rw [firstInsertionMap_zero, firstInsertionMap_one]
  exact Sym2.eq_swap

theorem firstInsertionMap_second_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (firstInsertionMap cyc u)
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
  rw [firstInsertionMap_one]
  have hpos : 1 ≤ (1 : Fin (m + 1)).val := by
    rw [honeSmall]
  rw [firstInsertionMap_succ_of_pos cyc u 1 hpos]

theorem firstInsertionMap_injective {m : ℕ}
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom) :
    Function.Injective (firstInsertionMap cyc u) := by
  intro a b hab
  let t : Fin ((m + 1) + 1) := 1
  by_cases ha : a = t
  · subst a
    by_cases hb : b = t
    · exact hb.symm
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := t) hb
      subst b
      have hbad : u = cyc.toHom j := by
        simpa only [firstInsertionMap, t, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] using hab
      exact False.elim (hu ⟨j, hbad.symm⟩)
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (y := t) ha
    subst a
    by_cases hb : b = t
    · subst b
      have hbad : cyc.toHom i = u := by
        simpa only [firstInsertionMap, t, Fin.insertNth_apply_same,
          Fin.insertNth_apply_succAbove] using hab
      exact False.elim (hu ⟨i, hbad⟩)
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := t) hb
      subst b
      have hij : cyc.toHom i = cyc.toHom j := by
        simpa only [firstInsertionMap, t,
          Fin.insertNth_apply_succAbove] using hab
      rw [cyc.injective hij]

/-- First Choi Claim 1 insertion. The selected cycle has `m+1 ≥ 3`
vertices, so the host cycle has `(m+1)+1` vertices. The only possible
unselected-spoke collision is explicitly excluded by `hbeta`. -/
theorem positive_first_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hattach : (selectedGraph χ r).Adj u (cyc.toHom 0))
    (hnewFirst : χ (outsiderEdge cyc u hu 0) ∈
      newColors χ (cyc.toHom 0))
    (hbeta : χ (outsiderEdge cyc u hu 1) ≠
      restrictedColor χ r
        (cyc.mapEdgeSet (sourceStep (⟨1, by omega⟩ : Fin m)))) :
    ∃ f : (cycleGraph ((m + 1) + 1)).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  let p := firstInsertionMap cyc u
  have hp : Function.Injective p :=
    firstInsertionMap_injective cyc u hu
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

  let a : (selectedGraph χ r).edgeSet :=
    ⟨s(u, cyc.toHom 0), hattach⟩
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
  have haColor : χ (outsiderEdge cyc u hu 0) =
      restrictedColor χ r a := by
    simp [outsiderEdge, restrictedColor, a]
  have huSelected (e : (cycleGraph (m + 1)).edgeSet) :
      u ∉ (cyc.mapEdgeSet e).val := by
    intro he
    change u ∈ Sym2.map cyc.toHom e.val at he
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp he
    exact hu ⟨i, hi⟩
  have hαSelected (e : (cycleGraph (m + 1)).edgeSet) :
      χ (outsiderEdge cyc u hu 0) ≠
        restrictedColor χ r (cyc.mapEdgeSet e) := by
    intro heq
    have hae : a = cyc.mapEdgeSet e :=
      restrictedColor_injective χ r (haColor.symm.trans heq)
    have hua : u ∈ a.val := by
      simp [a, Sym2.mem_iff]
    exact huSelected e (hae ▸ hua)
  have hαclosing : χ (outsiderEdge cyc u hu 0) ≠
      restrictedColor χ r closing := hαSelected (sourceClosing m hm)
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
    hcolor_of_host _ _ (firstInsertionMap_first_spoke cyc u hu)
  have hstep1 : L (sourceStep (1 : Fin (m + 1))) =
      χ (outsiderEdge cyc u hu 1) :=
    hcolor_of_host _ _ (firstInsertionMap_second_spoke hm cyc u hu)
  have htail (i : Fin (m + 1)) (hi : 2 ≤ i.val) :
      ∃ j : Fin m, j.val + 1 = i.val ∧ 1 ≤ j.val ∧
        L (sourceStep i) =
          restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
    obtain ⟨j, hjEq, hj, hval⟩ :=
      firstInsertionMap_step_ge_two cyc u i hi
    exact ⟨j, hjEq, hj, hcolor_of_selected _ _ hval⟩
  have hclose : L (sourceClosing (m + 1) (by omega)) =
      restrictedColor χ r closing :=
    hcolor_of_selected _ _ (firstInsertionMap_closing hm cyc u)

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
      · obtain ⟨j, _, _, hc₂⟩ := hT₂
        have hcolors : α =
            restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) :=
          hc₁.symm.trans (heq.trans hc₂)
        exact False.elim (hαSelected (sourceStep j) hcolors)
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
        exact False.elim (hαSelected (sourceStep i) hcolors)
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

end ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
