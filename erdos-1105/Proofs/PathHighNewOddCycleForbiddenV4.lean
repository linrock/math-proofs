module

public import PathHighNewHostPathToolsV4
public import CycleNewChoiceOutsideWitnessV2
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! Exact original χ high-NEW/no-path to no-odd-cycle first stage. All palette, complement owner and path properties are derived below. -/

namespace ErdosProblems.PathHighNewStageOne

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem comp_mapEdgeSet {α β : Type*} {H : SimpleGraph α}
    {J : SimpleGraph β} {G : SimpleGraph (Fin n)}
    (A : H.Copy J) (B : J.Copy G) (e : H.edgeSet) :
    (B.comp A).toHom.mapEdgeSet e = B.toHom.mapEdgeSet (A.toHom.mapEdgeSet e) := by
  apply Subtype.ext
  change Sym2.map (fun x => B (A x)) e.val =
    Sym2.map B (Sym2.map A e.val)
  exact (Sym2.map_map (g := B) (f := A) e.val).symm

omit [DecidableEq C] in
theorem rainbow_comp {α β : Type*} {H : SimpleGraph α}
    {J : SimpleGraph β} (A : H.Copy J)
    (B : J.Copy (⊤ : SimpleGraph (Fin n)))
    (χ : TopEdgeLabeling (Fin n) C) (hB : IsRainbow B.toHom χ) :
    IsRainbow (B.comp A).toHom χ := by
  intro e d heq
  apply A.mapEdgeSet.injective
  apply hB
  change χ (B.toHom.mapEdgeSet (A.toHom.mapEdgeSet e)) =
    χ (B.toHom.mapEdgeSet (A.toHom.mapEdgeSet d))
  simpa only [EdgeLabeling.pullback_apply, comp_mapEdgeSet] using heq

theorem path_one_no_edge (e : (pathGraph 1).edgeSet) : False := by
  obtain ⟨q, hq⟩ := e
  induction q using Sym2.inductionOn with
  | _ i j =>
    have h := pathGraph_adj.mp hq
    have hi := i.isLt
    have hj := j.isLt
    omega

def singletonHostCopy (w : Fin n) :
    (pathGraph 1).Copy (⊤ : SimpleGraph (Fin n)) :=
  (SimpleGraph.Embedding.completeGraph
    (⟨fun _ : Fin 1 => w, fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin n)).toCopy.comp
    (Copy.ofLE (pathGraph 1) (⊤ : SimpleGraph (Fin 1)) le_top)

omit [DecidableEq C] in
theorem singletonHostCopy_rainbow (χ : TopEdgeLabeling (Fin n) C) (w : Fin n) :
    IsRainbow (singletonHostCopy w).toHom χ := by
  intro e d _
  exact False.elim (path_one_no_edge e)

/-- A literal source-cycle spanning path may start at any prescribed source vertex. -/
theorem source_spanning_path_at {m : ℕ} (hm : 3 ≤ m) (j : Fin m) :
    ∃ A : (pathGraph m).Copy (cycleGraph m), A ⟨0, by omega⟩ = j := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, m = d + 3 := ⟨m - 3, by omega⟩
  let p := cycleGraph.cycle d
  have hj : j ∈ p.support := by
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨d + 3 - j.val, ?_, ?_⟩
    · rw [cycleGraph.getVert_cycle (by omega)]
      apply Fin.ext
      have hsub : d + 3 - (d + 3 - j.val) = j.val := by omega
      simp only [hsub, Nat.mod_eq_of_lt j.isLt]
    · simp only [p, cycleGraph.length_cycle]
      omega
  let q := p.rotate j hj
  have hcycle : q.IsCycle := (cycleGraph.isCycle_cycle (n := d)).rotate hj
  have hq : q.length = d + 3 := by simp only [q, SimpleGraph.Walk.length_rotate,
    p, cycleGraph.length_cycle]
  have hp : (q.take (d + 2)).IsPath := hcycle.isPath_take (by omega)
  have hlen : (q.take (d + 2)).length = d + 2 := by
    rw [SimpleGraph.Walk.take_length, hq, Nat.min_eq_left (by omega)]
  have hex : ∃ A : (pathGraph ((q.take (d + 2)).length + 1)).Copy
      (cycleGraph (d + 3)), A ⟨0, by omega⟩ = j := by
    refine ⟨hp.pathGraphCopy, ?_⟩
    change (q.take (d + 2)).support[0] = j
    exact SimpleGraph.Walk.support_getElem_zero _
  have hsize : (q.take (d + 2)).length + 1 = d + 3 := by omega
  let P : ℕ → Prop := fun t => ∀ ht : 0 < t,
    ∃ A : (pathGraph t).Copy (cycleGraph (d + 3)), A ⟨0, ht⟩ = j
  have hP : P ((q.take (d + 2)).length + 1) := fun _ => hex
  have hP' : P (d + 3) := Eq.mp (congrArg P hsize) hP
  exact hP' (by omega)

omit [DecidableEq C] in
/-- No rainbow one-vertex extension forces every original outside-cycle color
into the palette of that same original rainbow cycle. -/
theorem outside_cycle_edge_color_mem_palette {m : ℕ} (hm : 3 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (hc : IsRainbow c.toHom χ)
    (hno : ∀ p : (pathGraph (m + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow p.toHom χ)
    (w : Fin n) (hw : w ∉ Set.range c) (j : Fin m)
    (e : HostEdge n) (he : e.val = s(w, c j)) :
    χ e ∈ Set.range (EdgeLabeling.pullback χ c.toHom) := by
  classical
  by_contra hfresh
  obtain ⟨A, hA0⟩ := source_spanning_path_at hm j
  let B := c.comp A
  let O := singletonHostCopy w
  have hB : IsRainbow B.toHom χ := rainbow_comp A c χ hc
  have hO : IsRainbow O.toHom χ := singletonHostCopy_rainbow χ w
  have hdis : Disjoint (Set.range fun i : Fin 1 => O i)
      (Set.range fun j : Fin m => B j) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨i, hi⟩ ⟨j, hj⟩
    have hwi : O i = w := rfl
    apply hw
    refine ⟨A j, ?_⟩
    exact hj.trans (hi.symm.trans hwi)
  have hjoin : e.val = s(O ⟨1 - 1, by omega⟩, B ⟨0, by omega⟩) := by
    change e.val = s(w, c (A ⟨0, by omega⟩))
    rw [hA0]
    exact he
  have hBfresh : ∀ d : (pathGraph m).edgeSet, χ (B.toHom.mapEdgeSet d) ≠ χ e := by
    intro d h
    apply hfresh
    refine ⟨A.toHom.mapEdgeSet d, ?_⟩
    change χ (c.toHom.mapEdgeSet (A.toHom.mapEdgeSet d)) = χ e
    rw [← comp_mapEdgeSet A c d]
    exact h
  obtain ⟨f, hf, _, _⟩ := rainbow_path_of_original_disjoint_paths_and_fresh_join
    (by omega : 1 ≤ 1) (by omega : 1 ≤ m) χ O B hO hB hdis
    (fun d _ => False.elim (path_one_no_edge d)) e hjoin
    (fun d => False.elim (path_one_no_edge d)) hBfresh
  have hex : ∃ p : (pathGraph (m + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
    exact (Nat.add_comm 1 m) ▸
      (show ∃ p : (pathGraph (1 + m)).Copy (⊤ : SimpleGraph (Fin n)),
        IsRainbow p.toHom χ from ⟨f, hf⟩)
  obtain ⟨p, hp⟩ := hex
  exact hno p hp

/-- A NEW color at an original vertex outside the copy cannot be a copy-edge color. -/
theorem outside_new_color_not_cycle_palette {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (v : Fin n) (hv : v ∉ Set.range c) {a : C} (ha : a ∈ newColors χ v) :
    a ∉ Set.range (EdgeLabeling.pullback χ c.toHom) := by
  rintro ⟨d, hd⟩
  have hmem := newColor_every_edge_incident χ v ha (c.toHom.mapEdgeSet d) hd
  change v ∈ Sym2.map c d.val at hmem
  obtain ⟨z, _, hz⟩ := Sym2.mem_map.mp hmem
  exact hv ⟨z, hz⟩

/-- The checked original NEW-neighbor map remains in the exact cycle complement. -/
theorem outside_new_neighbor {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (hcross : ∀ v : Fin n, v ∉ Set.range c → ∀ j : Fin m,
      ∀ e : HostEdge n, e.val = s(v, c j) →
      χ e ∈ Set.range (EdgeLabeling.pullback χ c.toHom))
    (v : Fin n) (hv : v ∉ Set.range c) (a : newColors χ v) :
    newChoiceColorNeighbor χ r v a ∉ Set.range c := by
  rintro ⟨j, hj⟩
  let e : HostEdge n := ⟨(newChoiceIncidenceEdge χ r v a).val,
    SimpleGraph.edgeSet_mono le_top (newChoiceIncidenceEdge χ r v a).property.1⟩
  have he : e.val = s(v, c j) := by
    rw [newChoiceIncidenceEdge_eq_pair χ r v a, hj]
  have hp := hcross v hv j e he
  have hcolor : χ e = a.val := newChoiceIncidenceEdge_color χ r v a
  exact outside_new_color_not_cycle_palette χ c v hv a.property (hcolor ▸ hp)

/-- Every selected edge wholly outside has original color outside the cycle palette. -/
theorem selected_outside_color {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (e : (selectedGraph χ r).edgeSet)
    (hout : ∀ v : Fin n, v ∈ e.val → v ∉ Set.range c) :
    χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ ∉
      Set.range (EdgeLabeling.pullback χ c.toHom) := by
  have hmem : e.val ∈ Set.range (fun a : newColorUnion χ => (r.edge a).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e.property
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp a.property
  have hhost : (⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ : HostEdge n) =
      r.edge a := Subtype.ext ha.symm
  have hcolor : χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ = a.val := by
    rw [hhost]
    exact r.color_eq a
  have hinc : v ∈ e.val := newColor_every_edge_incident χ v hv
    ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ hcolor
  exact hcolor.symm ▸ outside_new_color_not_cycle_palette χ c v (hout v hinc) hv

/-- A maximum path in the actual selected complement is long enough.
Only original NEW-at-endpoint slots are counted; no full-degree restriction is used. -/
theorem exists_original_rainbow_outside_path {m ell : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (c : (cycleGraph m).Copy (⊤ : SimpleGraph (Fin n)))
    (hout : ∃ v : Fin n, v ∉ Set.range c)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card)
    (hcross : ∀ v : Fin n, v ∉ Set.range c → ∀ j : Fin m,
      ∀ e : HostEdge n, e.val = s(v, c j) →
      χ e ∈ Set.range (EdgeLabeling.pullback χ c.toHom)) :
    ∃ A : (pathGraph (ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow A.toHom χ ∧
      (∀ i, A i ∉ Set.range c) ∧
      (∀ e : (pathGraph (ell + 1)).edgeSet,
        χ (A.toHom.mapEdgeSet e) ∉ Set.range (EdgeLabeling.pullback χ c.toHom)) := by
  classical
  let T : Set (Fin n) := (Set.range c)ᶜ
  let G := selectedGraph χ r
  let D := G.induce T
  obtain ⟨x, hx⟩ := hout
  let : Nonempty T := ⟨⟨x, hx⟩⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length D
  let w : newColors χ v.val → T := fun a =>
    ⟨newChoiceColorNeighbor χ r v.val a,
      outside_new_neighbor χ r c hcross v.val v.property a⟩
  have hadj (a : newColors χ v.val) : D.Adj v (w a) :=
    newChoiceColorNeighbor_adj χ r v.val a
  have hsupp (a : newColors χ v.val) : w a ∈ p.support := by
    by_contra h
    have hlong := hp.concat h (hadj a)
    have hbound := hmax u (w a) (p.concat (hadj a)) hlong
    rw [SimpleGraph.Walk.length_concat] at hbound
    omega
  let P := p.support.toFinset.erase v
  let f : newColors χ v.val → P := fun a =>
    ⟨w a, Finset.mem_erase.mpr
      ⟨(hadj a).ne.symm, List.mem_toFinset.mpr (hsupp a)⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply newChoiceColorNeighbor_injective χ r v.val
    have h := congrArg (fun z : P => z.val.val) hab
    exact h
  have hcard : (newColors χ v.val).card ≤ P.card :=
    Finset.card_le_card_of_injective hf
  have hPcard : P.card = p.length := by
    calc
      P.card = p.support.toFinset.card - 1 :=
        Finset.card_erase_of_mem (List.mem_toFinset.mpr p.end_mem_support)
      _ = p.support.length - 1 := congrArg (fun z : ℕ => z - 1)
        (List.toFinset_card_of_nodup hp.support_nodup)
      _ = p.length := by
        rw [SimpleGraph.Walk.length_support]
        omega
  have hlen : ell ≤ p.length := by
    have hn := hnew v.val
    omega
  have htake : (p.take ell).length = ell := by
    rw [SimpleGraph.Walk.take_length, Nat.min_eq_left hlen]
  have hcopy : ∃ A : (pathGraph (ell + 1)).Copy D, True := by
    have h := (hp.take ell).pathGraphCopy
    have hsize : (p.take ell).length + 1 = ell + 1 := by omega
    exact ⟨hsize ▸ h, trivial⟩
  obtain ⟨A, _⟩ := hcopy
  let B : (pathGraph (ell + 1)).Copy G := (Copy.induce G T).comp A
  let H : (pathGraph (ell + 1)).Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE G (⊤ : SimpleGraph (Fin n)) le_top).comp B
  refine ⟨H, copy_in_selectedGraph_isRainbow χ r B, ?_, ?_⟩
  · intro i
    exact (A i).property
  · intro e
    let d : G.edgeSet := B.toHom.mapEdgeSet e
    have hcol : χ (H.toHom.mapEdgeSet e) =
        χ ⟨d.val, SimpleGraph.edgeSet_mono le_top d.property⟩ := by
      apply congrArg χ
      apply Subtype.ext
      change Sym2.map (fun i => (A i).val) e.val =
        Sym2.map (fun i => (A i).val) e.val
      rfl
    rw [hcol]
    apply selected_outside_color χ r c d
    intro z hz
    change z ∈ Sym2.map (fun i => (A i).val) e.val at hz
    obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hz
    exact hi ▸ (A i).property

/-- Two opposite original half-cycle paths have disjoint palettes, so one avoids
any prescribed literal host color. The original cycle need not be selected. -/
theorem exists_original_half_cycle_path_avoiding {ell : ℕ} (hell : 2 ≤ ell)
    (χ : TopEdgeLabeling (Fin n) C)
    (c : (cycleGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)))
    (hc : IsRainbow c.toHom χ) (join : HostEdge n) :
    ∃ B : (pathGraph (ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow B.toHom χ ∧ B ⟨0, by omega⟩ = c 0 ∧
      (∀ i, B i ∈ Set.range c) ∧
      (∀ e : (pathGraph (ell + 1)).edgeSet,
        χ (B.toHom.mapEdgeSet e) ∈ Set.range (EdgeLabeling.pullback χ c.toHom)) ∧
      (∀ e : (pathGraph (ell + 1)).edgeSet, χ (B.toHom.mapEdgeSet e) ≠ χ join) := by
  classical
  let m := 2 * ell + 1
  let F : Fin (ell + 1) → Fin m := fun i => ⟨i.val, by dsimp [m]; omega⟩
  let R : Fin (ell + 1) → Fin m := fun i =>
    ⟨if i.val = 0 then 0 else m - i.val, by
      have hi := i.isLt
      dsimp [m]
      split_ifs <;> omega⟩
  have hF : Function.Injective F := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin m => z.val) h)
  have hR : Function.Injective R := by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun z : Fin m => z.val) h
    have hi := i.isLt
    have hj := j.isLt
    change (if i.val = 0 then 0 else m - i.val) =
      (if j.val = 0 then 0 else m - j.val) at hv
    dsimp [m] at hv
    split_ifs at hv <;> omega
  have hRF : ∀ i j : Fin (ell + 1), i.val + 1 = j.val →
      (cycleGraph m).Adj (R i) (R j) := by
    intro i j hij
    by_cases hi0 : i.val = 0
    · have hj1 : j.val = 1 := by omega
      have hlt : R i < R j := by
        change (R i).val < (R j).val
        simp only [R, hi0, hj1, ite_eq_left]
        dsimp [m]
        omega
      rw [cycleGraph_adj']
      left
      rw [Fin.coe_sub_iff_lt.mpr hlt]
      simp only [R, hi0, hj1, ite_eq_left]
      dsimp [m]
      omega
    · have hj0 : j.val ≠ 0 := by omega
      apply pathGraph_le_cycleGraph
      apply pathGraph_adj.mpr
      right
      simp only [R, hi0, hj0]
      dsimp [m]
      have hi := i.isLt
      have hj := j.isLt
      omega
  let L : (pathGraph (ell + 1)).Copy (cycleGraph m) :=
    { toHom :=
        { toFun := F
          map_rel' := by
            intro i j h
            apply pathGraph_le_cycleGraph
            apply pathGraph_adj.mpr
            change i.val + 1 = j.val ∨ j.val + 1 = i.val
            exact pathGraph_adj.mp h }
      injective' := hF }
  let Q : (pathGraph (ell + 1)).Copy (cycleGraph m) :=
    { toHom :=
        { toFun := R
          map_rel' := by
            intro i j h
            rcases pathGraph_adj.mp h with h | h
            · exact hRF i j h
            · exact (hRF j i h).symm }
      injective' := hR }
  have hmeet : ∀ i j : Fin (ell + 1), F i = R j →
      i.val = 0 ∧ j.val = 0 := by
    intro i j h
    have hv := congrArg Fin.val h
    have hi := i.isLt
    have hj := j.isLt
    by_cases hj0 : j.val = 0
    · simp only [F, R, hj0, ite_eq_left] at hv
      exact ⟨hv, hj0⟩
    · simp only [F, R, hj0] at hv
      dsimp [m] at hv
      omega
  have hsourceDis : ∀ e d : (pathGraph (ell + 1)).edgeSet,
      L.toHom.mapEdgeSet e ≠ Q.toHom.mapEdgeSet d := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    induction x using Sym2.inductionOn with
    | _ i j =>
      induction y using Sym2.inductionOn with
      | _ u v =>
        have hv := congrArg Subtype.val h
        change s(F i, F j) = s(R u, R v) at hv
        have hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val := pathGraph_adj.mp hx
        rcases Sym2.eq_iff.mp hv with h | h
        · have hi0 : i.val = 0 := (hmeet i u h.1).1
          have hj0 : j.val = 0 := (hmeet j v h.2).1
          rcases hadj with hstep | hstep <;> omega
        · have hi0 : i.val = 0 := (hmeet i v h.1).1
          have hj0 : j.val = 0 := (hmeet j u h.2).1
          rcases hadj with hstep | hstep <;> omega
  let BL := c.comp L
  let BR := c.comp Q
  have hBL : IsRainbow BL.toHom χ := rainbow_comp L c χ hc
  have hBR : IsRainbow BR.toHom χ := rainbow_comp Q c χ hc
  have hpal : ∀ e d : (pathGraph (ell + 1)).edgeSet,
      χ (BL.toHom.mapEdgeSet e) ≠ χ (BR.toHom.mapEdgeSet d) := by
    intro e d h
    apply hsourceDis e d
    apply hc
    change χ (c.toHom.mapEdgeSet (L.toHom.mapEdgeSet e)) =
      χ (c.toHom.mapEdgeSet (Q.toHom.mapEdgeSet d))
    simpa only [BL, BR, comp_mapEdgeSet] using h
  have hBL0 : BL ⟨0, by omega⟩ = c 0 := by
    change c (F ⟨0, by omega⟩) = c 0
    apply congrArg c
    exact Fin.ext rfl
  have hBR0 : BR ⟨0, by omega⟩ = c 0 := by
    change c (R ⟨0, by omega⟩) = c 0
    apply congrArg c
    apply Fin.ext
    simp only [R, Fin.val_zero, ite_eq_left]
  have hBLpal (e : (pathGraph (ell + 1)).edgeSet) :
      χ (BL.toHom.mapEdgeSet e) ∈ Set.range (EdgeLabeling.pullback χ c.toHom) := by
    refine ⟨L.toHom.mapEdgeSet e, ?_⟩
    change χ (c.toHom.mapEdgeSet (L.toHom.mapEdgeSet e)) = χ (BL.toHom.mapEdgeSet e)
    rw [comp_mapEdgeSet]
  have hBRpal (e : (pathGraph (ell + 1)).edgeSet) :
      χ (BR.toHom.mapEdgeSet e) ∈ Set.range (EdgeLabeling.pullback χ c.toHom) := by
    refine ⟨Q.toHom.mapEdgeSet e, ?_⟩
    change χ (c.toHom.mapEdgeSet (Q.toHom.mapEdgeSet e)) = χ (BR.toHom.mapEdgeSet e)
    rw [comp_mapEdgeSet]
  by_cases hleft : ∀ e : (pathGraph (ell + 1)).edgeSet,
      χ (BL.toHom.mapEdgeSet e) ≠ χ join
  · exact ⟨BL, hBL, hBL0, fun i => ⟨L i, rfl⟩, hBLpal, hleft⟩
  · push Not at hleft
    obtain ⟨e, he⟩ := hleft
    refine ⟨BR, hBR, hBR0, fun i => ⟨Q i, rfl⟩, hBRpal, ?_⟩
    intro d hd
    exact hpal e d (he.trans hd.symm)

/-- Exact original first stage: high NEW and no even rainbow path exclude
the preceding odd rainbow cycle. No intermediate palette or path is supplied. -/
theorem no_rainbow_odd_cycle_of_high_new_and_no_even_path {ell : ℕ}
    (hell : 2 ≤ ell) (hn : 2 * ell + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) C)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card)
    (hnoP : ∀ p : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow p.toHom χ) :
    ∀ c : (cycleGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow c.toHom χ := by
  classical
  intro c hc
  have hout : ∃ v : Fin n, v ∉ Set.range c := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective c := fun v => h v
    have hcard := Fintype.card_le_of_surjective c hsurj
    simp only [Fintype.card_fin] at hcard
    omega
  have hcross : ∀ v : Fin n, v ∉ Set.range c → ∀ j : Fin (2 * ell + 1),
      ∀ e : HostEdge n, e.val = s(v, c j) →
      χ e ∈ Set.range (EdgeLabeling.pullback χ c.toHom) := by
    intro v hv j e he
    exact outside_cycle_edge_color_mem_palette (by omega) χ c hc
      hnoP v hv j e he
  let r := canonicalChoice χ
  obtain ⟨A, hA, houtA, hfreshA⟩ :=
    exists_original_rainbow_outside_path χ r c hout hnew hcross
  let w := A ⟨ell, by omega⟩
  have hw : w ∉ Set.range c := houtA _
  have hneq : w ≠ c 0 := by
    intro h
    exact hw ⟨0, h.symm⟩
  let join : HostEdge n := ⟨s(w, c 0), by
    apply (SimpleGraph.mem_edgeSet _).mpr
    exact hneq⟩
  have hjoinpal : χ join ∈ Set.range (EdgeLabeling.pullback χ c.toHom) :=
    hcross w hw 0 join rfl
  obtain ⟨B, hB, hB0, hinB, hBpal, hfreshB⟩ :=
    exists_original_half_cycle_path_avoiding hell χ c hc join
  have hdis : Disjoint (Set.range fun i : Fin (ell + 1) => A i)
      (Set.range fun j : Fin (ell + 1) => B j) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨i, hi⟩ ⟨j, hj⟩
    apply houtA i
    have hab : B j = A i := hj.trans hi.symm
    rw [← hab]
    exact hinB j
  have hpal : ∀ e d : (pathGraph (ell + 1)).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ (B.toHom.mapEdgeSet d) := by
    intro e d h
    exact hfreshA e (h.symm ▸ hBpal d)
  have hj : join.val = s(A ⟨ell + 1 - 1, by omega⟩, B ⟨0, by omega⟩) := by
    have hindex : (⟨ell + 1 - 1, by omega⟩ : Fin (ell + 1)) = ⟨ell, by omega⟩ := by
      apply Fin.ext
      change ell + 1 - 1 = ell
      omega
    change s(A ⟨ell, by omega⟩, c 0) =
      s(A ⟨ell + 1 - 1, by omega⟩, B ⟨0, by omega⟩)
    rw [hindex, hB0]
  have hAfresh : ∀ e : (pathGraph (ell + 1)).edgeSet,
      χ (A.toHom.mapEdgeSet e) ≠ χ join := by
    intro e h
    exact hfreshA e (h.symm ▸ hjoinpal)
  obtain ⟨f, hf, _, _⟩ := rainbow_path_of_original_disjoint_paths_and_fresh_join
    (by omega) (by omega) χ A B hA hB hdis hpal join hj hAfresh hfreshB
  have hex : ∃ p : (pathGraph (2 * ell + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
    have hsize : (ell + 1) + (ell + 1) = 2 * ell + 2 := by omega
    exact hsize ▸
      (show ∃ p : (pathGraph ((ell + 1) + (ell + 1))).Copy
        (⊤ : SimpleGraph (Fin n)), IsRainbow p.toHom χ from ⟨f, hf⟩)
  obtain ⟨p, hp⟩ := hex
  exact hnoP p hp

end ErdosProblems.PathHighNewStageOne
