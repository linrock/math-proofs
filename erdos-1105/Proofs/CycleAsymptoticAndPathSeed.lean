module

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Mathlib.Data.List.ChainOfFn
public import PathRestorationAndCircumference

@[expose] public section

/-!
# CycleAsymptoticAndPathSeed

Ore path-endpoint closure, Hamiltonian selected components, unconditional cycle bounds (`cycle_linear_upper` and `cycle_asymptotic_all`), and connected path-seed reductions for Erdős Problem 1105.
-/

namespace ErdosProblems.AntiRamseyCyclePathOre

open Finset SimpleGraph

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (H : SimpleGraph (Fin n)) (v : Fin n) :
    Fintype (H.neighborSet v) := Fintype.ofFinite _

theorem cycle_adj_cases {s : ℕ} (_hs : 2 ≤ s)
    {a b : Fin (s + 1)} (hab : (cycleGraph (s + 1)).Adj a b) :
    a.val + 1 = b.val ∨ b.val + 1 = a.val ∨
      (a.val = 0 ∧ b.val = s) ∨
      (b.val = 0 ∧ a.val = s) := by
  rw [cycleGraph_adj'] at hab
  rcases hab with h | h
  · by_cases hle : b ≤ a
    · have hsub : (a - b).val = a.val - b.val := Fin.sub_val_of_le hle
      rw [hsub] at h
      right; left
      omega
    · have hlt : a < b := lt_of_not_ge hle
      have hsub : (a - b).val = s + 1 + a.val - b.val :=
        Fin.coe_sub_iff_lt.mpr hlt
      rw [hsub] at h
      have hb := b.isLt
      right; right; left
      omega
  · by_cases hle : a ≤ b
    · have hsub : (b - a).val = b.val - a.val := Fin.sub_val_of_le hle
      rw [hsub] at h
      left
      omega
    · have hlt : b < a := lt_of_not_ge hle
      have hsub : (b - a).val = s + 1 + b.val - a.val :=
        Fin.coe_sub_iff_lt.mpr hlt
      rw [hsub] at h
      have ha := a.isLt
      right; right; right
      omega

/-- Reverse the suffix of a path after `j`, leaving its prefix fixed.
This is the vertex order of Ore's cycle built from two crossing chords. -/
def cycleOrder {s : ℕ} (j : Fin s) (q : Fin (s + 1)) : Fin (s + 1) :=
  if h : q.val ≤ j.val then q else
    ⟨s + 1 + j.val - q.val, by
      have hj := j.isLt
      have hq := q.isLt
      omega⟩

theorem cycleOrder_injective {s : ℕ} (j : Fin s) :
    Function.Injective (cycleOrder j) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  by_cases ha : a.val ≤ j.val
  · by_cases hb : b.val ≤ j.val
    · simpa only [cycleOrder, dite_eq_left ha, dite_eq_left hb] using hab
    · simp only [cycleOrder, dite_eq_left ha, dite_eq_right hb] at hv
      have hj := j.isLt
      have hb' := b.isLt
      omega
  · by_cases hb : b.val ≤ j.val
    · simp only [cycleOrder, dite_eq_right ha, dite_eq_left hb] at hv
      have hj := j.isLt
      have ha' := a.isLt
      omega
    · simp only [cycleOrder, dite_eq_right ha, dite_eq_right hb] at hv
      apply Fin.ext
      have ha' := a.isLt
      have hb' := b.isLt
      omega

theorem cycleOrder_succ_adj {s : ℕ} (j : Fin s)
    (H : SimpleGraph (Fin (s + 1)))
    (hpath : ∀ a b : Fin (s + 1), a.val + 1 = b.val → H.Adj a b)
    (hB : H.Adj (Fin.last s) (Fin.castSucc j))
    {a b : Fin (s + 1)} (hab : a.val + 1 = b.val) :
    H.Adj (cycleOrder j a) (cycleOrder j b) := by
  by_cases ha : a.val ≤ j.val
  · by_cases hb : b.val ≤ j.val
    · simpa only [cycleOrder, dite_eq_left ha, dite_eq_left hb] using hpath a b hab
    · have hleft : cycleOrder j a = Fin.castSucc j := by
        apply Fin.ext
        simp only [cycleOrder, dite_eq_left ha, Fin.val_castSucc]
        omega
      have hright : cycleOrder j b = Fin.last s := by
        apply Fin.ext
        simp only [cycleOrder, dite_eq_right hb, Fin.val_last]
        have hj := j.isLt
        have hb' := b.isLt
        omega
      rw [hleft, hright]
      exact hB.symm
  · have hb : ¬ b.val ≤ j.val := by omega
    have hrev : (cycleOrder j b).val + 1 = (cycleOrder j a).val := by
      simp only [cycleOrder, dite_eq_right ha, dite_eq_right hb]
      have hj := j.isLt
      have ha' := a.isLt
      have hb' := b.isLt
      omega
    exact (hpath (cycleOrder j b) (cycleOrder j a) hrev).symm

theorem cycleOrder_zero {s : ℕ} (j : Fin s) :
    cycleOrder j (0 : Fin (s + 1)) = 0 := by
  simp [cycleOrder]

theorem cycleOrder_last {s : ℕ} (j : Fin s) :
    cycleOrder j (Fin.last s) = Fin.succ j := by
  apply Fin.ext
  have hj := j.isLt
  have hne : ¬ (Fin.last s).val ≤ j.val := by simp [Fin.val_last]
  simp only [cycleOrder, dite_eq_right hne, Fin.val_succ]
  simp only [Fin.val_last]
  omega

/-- Two endpoint chords crossing along a selected `s+1`-vertex path force
an ordinary non-induced `cycleGraph (s+1).Copy` in the graph. -/
theorem crossing_chords_force_cycle {s : ℕ} (hs : 2 ≤ s)
    (H : SimpleGraph (Fin (s + 1)))
    (hpath : ∀ a b : Fin (s + 1), a.val + 1 = b.val → H.Adj a b)
    (j : Fin s)
    (hA : H.Adj 0 (Fin.succ j))
    (hB : H.Adj (Fin.last s) (Fin.castSucc j)) :
    (cycleGraph (s + 1)) ⊑ H := by
  have hmap : ∀ {a b : Fin (s + 1)},
      (cycleGraph (s + 1)).Adj a b →
        H.Adj (cycleOrder j a) (cycleOrder j b) := by
    intro a b hab
    rcases cycle_adj_cases hs hab with hsucc | hsucc | hclose | hclose
    · exact cycleOrder_succ_adj j H hpath hB hsucc
    · exact (cycleOrder_succ_adj j H hpath hB hsucc).symm
    · have ha : a = 0 := Fin.ext (by simpa using hclose.1)
      have hb : b = Fin.last s := Fin.ext (by simpa using hclose.2)
      subst a; subst b
      simpa only [cycleOrder_zero, cycleOrder_last] using hA
    · have hb : b = 0 := Fin.ext (by simpa using hclose.1)
      have ha : a = Fin.last s := Fin.ext (by simpa using hclose.2)
      subst a; subst b
      simpa only [cycleOrder_zero, cycleOrder_last] using hA.symm
  let f : (cycleGraph (s + 1)) →g H := ⟨cycleOrder j, fun hab => hmap hab⟩
  exact ⟨f.toCopy (by simpa [f] using cycleOrder_injective j)⟩

theorem left_neighbor_card {s : ℕ}
    (H : SimpleGraph (Fin (s + 1))) [DecidableRel H.Adj] :
    (H.neighborFinset 0).card =
      ((Finset.univ : Finset (Fin s)).filter
        (fun j => H.Adj 0 (Fin.succ j))).card := by
  classical
  let A : Finset (Fin s) :=
    Finset.univ.filter (fun j => H.Adj 0 (Fin.succ j))
  have hset : H.neighborFinset 0 = A.image Fin.succ := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hx.ne'
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hj).2
  rw [hset, Finset.card_image_of_injective _ (Fin.succ_injective s)]

theorem right_neighbor_card {s : ℕ}
    (H : SimpleGraph (Fin (s + 1))) [DecidableRel H.Adj] :
    (H.neighborFinset (Fin.last s)).card =
      ((Finset.univ : Finset (Fin s)).filter
        (fun j => H.Adj (Fin.last s) (Fin.castSucc j))).card := by
  classical
  let B : Finset (Fin s) :=
    Finset.univ.filter (fun j => H.Adj (Fin.last s) (Fin.castSucc j))
  have hset : H.neighborFinset (Fin.last s) = B.image Fin.castSucc := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hx.ne'
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hj).2
  rw [hset, Finset.card_image_of_injective _ (Fin.castSucc_injective s)]

/-- A `C_(s+1)`-free graph on `Fin (s+1)` containing the consecutive
path cannot have endpoint degrees summing to `s+1` or more. -/
theorem path_endpoint_degree_sum_lt {s : ℕ} (hs : 2 ≤ s)
    (H : SimpleGraph (Fin (s + 1))) [DecidableRel H.Adj]
    (hpath : ∀ a b : Fin (s + 1), a.val + 1 = b.val → H.Adj a b)
    (hfree : (cycleGraph (s + 1)).Free H) :
    H.degree 0 + H.degree (Fin.last s) < s + 1 := by
  classical
  let A : Finset (Fin s) :=
    Finset.univ.filter (fun j => H.Adj 0 (Fin.succ j))
  let B : Finset (Fin s) :=
    Finset.univ.filter (fun j => H.Adj (Fin.last s) (Fin.castSucc j))
  have hA : H.degree 0 = A.card := by
    simpa only [SimpleGraph.degree] using left_neighbor_card H
  have hB : H.degree (Fin.last s) = B.card := by
    simpa only [SimpleGraph.degree] using right_neighbor_card H
  have hunion : (A ∪ B).card ≤ s := by
    have hsub : A ∪ B ⊆ (Finset.univ : Finset (Fin s)) := by simp
    simpa using Finset.card_le_card hsub
  have hcount : A.card + B.card ≤ s + (A ∩ B).card := by
    calc
      A.card + B.card = (A ∪ B).card + (A ∩ B).card :=
        (Finset.card_union_add_card_inter A B).symm
      _ ≤ s + (A ∩ B).card := Nat.add_le_add_right hunion _
  by_contra hnot
  have hlarge : s + 1 ≤ A.card + B.card := by
    rw [hA, hB] at hnot
    omega
  have hpos : 0 < (A ∩ B).card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hjA : H.Adj 0 (Fin.succ j) := (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).2
  have hjB : H.Adj (Fin.last s) (Fin.castSucc j) :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2
  exact hfree (crossing_chords_force_cycle hs H hpath j hjA hjB)

/-- Internal endpoint degrees of an injective ordered path are below its
vertex count when the graph induced on these path vertices has no selected
cycle of exactly that length. This assumes `Free` only for `G.comap p`,
not for all components of `G`. -/
theorem ordered_path_internal_endpoint_degree_sum_lt
    {s n : ℕ} (hs : 2 ≤ s)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin (s + 1) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ a b : Fin (s + 1), a.val + 1 = b.val → G.Adj (p a) (p b))
    (hfreeOnPath : (cycleGraph (s + 1)).Free (G.comap p)) :
    (G.neighborFinset (p 0) ∩ (Finset.univ.image p)).card +
      (G.neighborFinset (p (Fin.last s)) ∩ (Finset.univ.image p)).card <
        s + 1 := by
  classical
  let H : SimpleGraph (Fin (s + 1)) := G.comap p
  have hHpath : ∀ a b : Fin (s + 1), a.val + 1 = b.val → H.Adj a b := by
    intro a b hab
    exact hpath a b hab
  have hHfree : (cycleGraph (s + 1)).Free H := hfreeOnPath
  have hcore := path_endpoint_degree_sum_lt hs H hHpath hHfree
  let P : Finset (Fin n) := Finset.univ.image p
  have hneigh (i : Fin (s + 1)) :
      G.neighborFinset (p i) ∩ P = (H.neighborFinset i).image p := by
    ext x
    constructor
    · intro hx
      obtain ⟨hAdj, hxP⟩ := Finset.mem_inter.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxP
      exact Finset.mem_image.mpr
        ⟨j, by simpa only [SimpleGraph.mem_neighborFinset, H,
          SimpleGraph.comap_adj] using hAdj, rfl⟩
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr
        ⟨by simpa only [SimpleGraph.mem_neighborFinset, H,
          SimpleGraph.comap_adj] using hj,
          Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hcard (i : Fin (s + 1)) :
      (G.neighborFinset (p i) ∩ P).card = H.degree i := by
    rw [hneigh i, Finset.card_image_of_injective _ hp]
    rfl
  simpa only [P, H, ← hcard] using hcore

/-- If no selected `C_(s+1)` Copy is wholly contained in a specified
component vertex set `D`, then no such Copy is contained entirely in the
ordered path vertices. Other components may contain cycles. -/
theorem cycle_free_on_ordered_path_of_component
    {s n : ℕ} (G : SimpleGraph (Fin n))
    (p : Fin (s + 1) → Fin n) (hp : Function.Injective p)
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (s + 1), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (s + 1)).Copy G,
      ¬∀ i : Fin (s + 1), f i ∈ D) :
    (cycleGraph (s + 1)).Free (G.comap p) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  let e : Fin (s + 1) ↪ Fin n := ⟨p, hp⟩
  let g : (cycleGraph (s + 1)).Copy G :=
    (SimpleGraph.Embedding.comap e G).toCopy.comp f
  apply hnoD g
  intro i
  have hg : g i = p (f i) := by
    calc
      g i = (SimpleGraph.Embedding.comap e G) (f i) := rfl
      _ = e (f i) := SimpleGraph.Embedding.comap_apply e G (f i)
      _ = p (f i) := rfl
  rw [hg]
  exact hpD (f i)

/-- Ore's endpoint deficit with the exact component-local selected-cycle
exclusion needed in Choi Claim 2. It does not exclude cycles in any other
component of `G`. -/
theorem ordered_path_endpoint_deficit_of_component
    {s n : ℕ} (hs : 2 ≤ s)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin (s + 1) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ a b : Fin (s + 1), a.val + 1 = b.val → G.Adj (p a) (p b))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (s + 1), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (s + 1)).Copy G,
      ¬∀ i : Fin (s + 1), f i ∈ D) :
    (G.neighborFinset (p 0) ∩ (Finset.univ.image p)).card +
      (G.neighborFinset (p (Fin.last s)) ∩ (Finset.univ.image p)).card <
        s + 1 :=
  ordered_path_internal_endpoint_degree_sum_lt hs G p hp hpath
    (cycle_free_on_ordered_path_of_component G p hp D hpD hnoD)

end ErdosProblems.AntiRamseyCyclePathOre

namespace ErdosProblems.AntiRamseyCyclePathEndpointExtension

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Some endpoint of a locally shorter-cycle-free selected path has an
outside selected edge whose color is NEW at that exact path endpoint.
The specified finite D preserves the component-local Ore interface.
No selected-cycle exclusion elsewhere or terminal inward NEW is assumed. -/
theorem exists_endpoint_newColor_edge_outside_path
    {t : ℕ} (ht : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ a b : Fin (t + 1), a.val + 1 = b.val →
      (selectedGraph χ r).Adj (p a) (p b))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (t + 1), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (t + 1)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (t + 1), f i ∈ D)
    (hpair : t + 1 ≤
      (newColors χ (p 0)).card + (newColors χ (p (Fin.last t))).card) :
    (∃ w : Fin n, ∃ e : HostEdge n,
      w ∉ Finset.univ.image p ∧ (selectedGraph χ r).Adj (p 0) w ∧
      e.val = s(p 0, w) ∧ χ e ∈ newColors χ (p 0)) ∨
    (∃ w : Fin n, ∃ e : HostEdge n,
      w ∉ Finset.univ.image p ∧
      (selectedGraph χ r).Adj (p (Fin.last t)) w ∧
      e.val = s(p (Fin.last t), w) ∧
      χ e ∈ newColors χ (p (Fin.last t))) := by
  classical
  let P : Finset (Fin n) := Finset.univ.image p
  have hdeficit :=
    ErdosProblems.AntiRamseyCyclePathOre.ordered_path_endpoint_deficit_of_component
      ht (selectedGraph χ r) p hp hpath D hpD hnoD
  change ((selectedGraph χ r).neighborFinset (p 0) ∩ P).card +
    ((selectedGraph χ r).neighborFinset (p (Fin.last t)) ∩ P).card <
      t + 1 at hdeficit
  by_cases hleft :
      ((selectedGraph χ r).neighborFinset (p 0) ∩ P).card <
        (newColors χ (p 0)).card
  · left
    exact
      ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness.exists_selected_newColor_edge_outside
        χ r (p 0) P hleft
  · right
    have hright :
        ((selectedGraph χ r).neighborFinset (p (Fin.last t)) ∩ P).card <
          (newColors χ (p (Fin.last t))).card := by
      omega
    exact
      ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness.exists_selected_newColor_edge_outside
        χ r (p (Fin.last t)) P hright

end ErdosProblems.AntiRamseyCyclePathEndpointExtension

namespace ErdosProblems.AntiRamseyCycleFirstPathExtension

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem snoc_with_new_terminal
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
    ∃ q : Fin (t + 2) → Fin n,
      ∃ hqpath : ∀ i : Fin (t + 1),
        (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)),
      Function.Injective q ∧
      (∀ i : Fin (t + 2), q i ∈ D) ∧
      restrictedColor χ r
        (⟨s(q (Fin.castSucc (Fin.last t)), q (Fin.succ (Fin.last t))),
          hqpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) ∈
        newColors χ (q (Fin.castSucc (Fin.last t))) := by
  classical
  let q : Fin (t + 2) → Fin n := Fin.snoc p w
  have hq : Function.Injective q := Fin.snoc_injective_of_injective hp hw
  have hqD : ∀ i : Fin (t + 2), q i ∈ D := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [q, Fin.snoc_last] using hwD
    | cast j => simpa only [q, Fin.snoc_castSucc] using hpD j
  have hqpath : ∀ i : Fin (t + 1),
      (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simpa only [q, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using hadj
    | cast j =>
      simpa only [q, Fin.succ_castSucc, Fin.snoc_castSucc] using hstep j
  have htailColor : restrictedColor χ r
      (⟨s(q (Fin.castSucc (Fin.last t)), q (Fin.succ (Fin.last t))),
        hqpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) = χ e := by
    change χ ⟨s(q (Fin.castSucc (Fin.last t)), q (Fin.succ (Fin.last t))),
      SimpleGraph.edgeSet_mono
        (show selectedGraph χ r ≤ (⊤ : SimpleGraph (Fin n)) from le_top)
        (hqpath (Fin.last t))⟩ = χ e
    apply congrArg χ
    apply Subtype.ext
    simpa only [q, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using he.symm
  refine ⟨q, hqpath, hq, hqD, ?_⟩
  rw [htailColor]
  simpa only [q, Fin.snoc_castSucc] using hnew

/-- Reverse when the first endpoint is chosen, then append its outside NEW
neighbor. The literal witness edge is terminal and NEW at the inner endpoint.
The local cycle exclusion and endpoint pair bound are passed unchanged. -/
theorem exists_inward_new_ordered_path_extension
    {t : ℕ} (ht : 2 ≤ t)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (t + 1) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ a b : Fin (t + 1), a.val + 1 = b.val →
      (selectedGraph χ r).Adj (p a) (p b))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (t + 1), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (t + 1)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (t + 1), f i ∈ D)
    (hpair : t + 1 ≤
      (newColors χ (p 0)).card + (newColors χ (p (Fin.last t))).card)
    (hclosed : ∀ v : Fin n, v ∈ D → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D) :
    ∃ q : Fin (t + 2) → Fin n,
      ∃ hqpath : ∀ i : Fin (t + 1),
        (selectedGraph χ r).Adj (q (Fin.castSucc i)) (q (Fin.succ i)),
      Function.Injective q ∧
      (∀ i : Fin (t + 2), q i ∈ D) ∧
      restrictedColor χ r
        (⟨s(q (Fin.castSucc (Fin.last t)), q (Fin.succ (Fin.last t))),
          hqpath (Fin.last t)⟩ : (selectedGraph χ r).edgeSet) ∈
        newColors χ (q (Fin.castSucc (Fin.last t))) := by
  classical
  have hstep : ∀ i : Fin t,
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)) := by
    intro i
    exact hpath (Fin.castSucc i) (Fin.succ i) rfl
  rcases
    ErdosProblems.AntiRamseyCyclePathEndpointExtension.exists_endpoint_newColor_edge_outside_path
      ht χ r p hp hpath D hpD hnoD hpair with hleft | hright
  · obtain ⟨w, e, hwImage, hadj, he, hnew⟩ := hleft
    let b : Fin (t + 1) → Fin n := fun i => p i.rev
    have hb : Function.Injective b := hp.comp Fin.rev_injective
    have hbD : ∀ i : Fin (t + 1), b i ∈ D := by
      intro i
      exact hpD i.rev
    have hbstep : ∀ i : Fin t,
        (selectedGraph χ r).Adj (b (Fin.castSucc i)) (b (Fin.succ i)) := by
      intro i
      simpa only [b, Fin.rev_castSucc, Fin.rev_succ] using (hstep i.rev).symm
    have hwRange : w ∉ Set.range b := by
      rintro ⟨i, hi⟩
      exact hwImage (Finset.mem_image.mpr ⟨i.rev, Finset.mem_univ _, hi⟩)
    have hwD : w ∈ D := hclosed (p 0) (hpD 0) w hadj
    have hbAdj : (selectedGraph χ r).Adj (b (Fin.last t)) w := by
      simpa only [b, Fin.rev_last] using hadj
    have hbEdge : e.val = s(b (Fin.last t), w) := by
      simpa only [b, Fin.rev_last] using he
    have hbNew : χ e ∈ newColors χ (b (Fin.last t)) := by
      simpa only [b, Fin.rev_last] using hnew
    exact snoc_with_new_terminal χ r b hb hbstep D hbD w hwRange hwD e hbAdj hbEdge hbNew
  · obtain ⟨w, e, hwImage, hadj, he, hnew⟩ := hright
    have hwRange : w ∉ Set.range p := by
      rintro ⟨i, hi⟩
      exact hwImage (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    have hwD : w ∈ D := hclosed (p (Fin.last t)) (hpD (Fin.last t)) w hadj
    exact snoc_with_new_terminal χ r p hp hstep D hpD w hwRange hwD e hadj he hnew

end ErdosProblems.AntiRamseyCycleFirstPathExtension

namespace ErdosProblems.AntiRamseyCycleForcedTailWitness

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Head domination, the component-local Ore deficit and the endpoint NEW
sum force a selected edge leaving the path at its prescribed terminal
endpoint. Its literal original-host color is NEW at that endpoint.
The inward terminal path-edge premise must be supplied by the first path
extension in the eventual component argument. -/
theorem exists_terminal_newColor_edge_outside_inward_path
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
      (newColors χ (p (Fin.last (m + 1)))).card) :
    ∃ w : Fin n, ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
      w ∉ Finset.univ.image p ∧
      (selectedGraph χ r).Adj (p (Fin.last (m + 1))) w ∧
      e.val = s(p (Fin.last (m + 1)), w) ∧
      χ e ∈ newColors χ (p (Fin.last (m + 1))) := by
  classical
  have hordered : ∀ a b : Fin (m + 2), a.val + 1 = b.val →
      (selectedGraph χ r).Adj (p a) (p b) := by
    intro a b hab
    have ha : a.val < m + 1 := by
      have hb := b.isLt
      omega
    let i : Fin (m + 1) := ⟨a.val, ha⟩
    have hcast : Fin.castSucc i = a := Fin.ext rfl
    have hsucc : Fin.succ i = b := Fin.ext hab
    simpa only [hcast, hsucc] using hpath i
  have hhead :=
    ErdosProblems.AntiRamseyCycleHeadNewDominance.no_head_new_deficit_of_inward_tail
      hm χ r p hp hpath hnewLast hno
  have hdeficit :=
    ErdosProblems.AntiRamseyCyclePathOre.ordered_path_endpoint_deficit_of_component
      (s := m + 1) (by omega) (selectedGraph χ r) p hp hordered D hpD hnoD
  have hsmall :
      ((selectedGraph χ r).neighborFinset (p (Fin.last (m + 1))) ∩
        Finset.univ.image p).card <
      (newColors χ (p (Fin.last (m + 1)))).card := by
    omega
  exact
    ErdosProblems.AntiRamseyCycleNewChoiceOutsideWitness.exists_selected_newColor_edge_outside
      χ r (p (Fin.last (m + 1))) (Finset.univ.image p) hsmall

end ErdosProblems.AntiRamseyCycleForcedTailWitness

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

namespace ErdosProblems.AntiRamseyCycleGenericHamiltonian

open SimpleGraph
open ErdosProblems.AntiRamseyCycleMaximumPathLocalFree
open ErdosProblems.AntiRamseyCyclePathOre

/-- A connected finite graph of order at least three whose distinct vertex
degrees sum at least to its order contains a non-induced spanning cycle Copy. -/
theorem contains_spanning_cycle_of_degree_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y →
      Fintype.card V ≤ G.degree x + G.degree y) :
    (cycleGraph (Fintype.card V)) ⊑ G := by
  classical
  have htwoVertices : 1 < (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ] using (show 1 < Fintype.card V by omega)
  obtain ⟨a, _, b, _, hab⟩ := Finset.one_lt_card.mp htwoVertices
  let : Nonempty V := ⟨a⟩
  have hsomeDegree : ∃ x : V, 2 ≤ G.degree x := by
    have hsum := hpair a b hab
    by_cases ha : 2 ≤ G.degree a
    · exact ⟨a, ha⟩
    · exact ⟨b, by omega⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hlen : 2 ≤ p.length := by
    obtain ⟨x, hxdegree⟩ := hsomeDegree
    have hmany : 1 < (G.neighborFinset x).card := by
      change 2 ≤ (G.neighborFinset x).card at hxdegree
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hmany
    have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp ha
    have hxb : G.Adj x b := (G.mem_neighborFinset x b).mp hb
    let one : G.Walk x b := SimpleGraph.Walk.cons hxb SimpleGraph.Walk.nil
    have hone : one.IsPath := by
      apply SimpleGraph.Walk.IsPath.nil.cons
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hxb.ne
    let two : G.Walk a b := SimpleGraph.Walk.cons hxa.symm one
    have htwo : two.IsPath := by
      apply hone.cons
      intro hmem
      change a ∈ x :: [b] at hmem
      rcases List.mem_cons.mp hmem with heq | heq
      · exact hxa.ne heq.symm
      · exact hab (List.mem_singleton.mp heq)
    have hbound := hmax a b two htwo
    change 2 ≤ p.length at hbound
    exact hbound
  have hleft : ∀ x : V, G.Adj u x → x ∈ p.support := by
    intro x hx
    by_contra hout
    let longer : G.Walk x v := SimpleGraph.Walk.cons hx.symm p
    have hlonger : longer.IsPath := hp.cons hout
    have hbound := hmax x v longer hlonger
    change p.length + 1 ≤ p.length at hbound
    omega
  have hright : ∀ x : V, G.Adj v x → x ∈ p.support := by
    intro x hx
    by_contra hout
    have houtReverse : x ∉ p.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hout
    let longer : G.Walk x u := SimpleGraph.Walk.cons hx.symm p.reverse
    have hlonger : longer.IsPath := hp.reverse.cons houtReverse
    have hbound := hmax x u longer hlonger
    change p.reverse.length + 1 ≤ p.length at hbound
    rw [SimpleGraph.Walk.length_reverse] at hbound
    omega
  let order : Fin (p.length + 1) → V := fun i => p.getVert i.val
  have horder : Function.Injective order := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) hij
  have hzero : order 0 = u := p.getVert_zero
  have hlast : order (Fin.last p.length) = v := p.getVert_length
  have huv : u ≠ v := by
    intro heq
    have hi := horder (hzero.trans (heq.trans hlast.symm))
    have hval := congrArg Fin.val hi
    change 0 = p.length at hval
    omega
  have horderCard : p.length + 1 ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective order horder
  let H : SimpleGraph (Fin (p.length + 1)) := G.comap order
  have hHpath : ∀ a b : Fin (p.length + 1),
      a.val + 1 = b.val → H.Adj a b := by
    intro a b hab
    change G.Adj (p.getVert a.val) (p.getVert b.val)
    have hb := b.isLt
    have hadj := p.adj_getVert_succ (i := a.val) (by omega)
    rw [hab] at hadj
    exact hadj
  have hneighbors (i : Fin (p.length + 1))
      (hall : ∀ x : V, G.Adj (order i) x → x ∈ p.support) :
      G.neighborFinset (order i) = (H.neighborFinset i).image order := by
    ext x
    constructor
    · intro hx
      have hadj : G.Adj (order i) x := (G.mem_neighborFinset (order i) x).mp hx
      obtain ⟨a, ha, halength⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hall x hadj)
      let j : Fin (p.length + 1) := ⟨a, by omega⟩
      refine Finset.mem_image.mpr ⟨j, ?_, ha⟩
      apply (H.mem_neighborFinset i j).mpr
      change G.Adj (order i) (p.getVert a)
      rw [ha]
      exact hadj
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      apply (G.mem_neighborFinset (order i) (order j)).mpr
      exact (show G.Adj (order i) (order j) from
        (H.mem_neighborFinset i j).mp hj)
  have hdegree (i : Fin (p.length + 1))
      (hall : ∀ x : V, G.Adj (order i) x → x ∈ p.support) :
      G.degree (order i) = H.degree i := by
    calc
      G.degree (order i) = (G.neighborFinset (order i)).card := rfl
      _ = ((H.neighborFinset i).image order).card :=
        congrArg Finset.card (hneighbors i hall)
      _ = (H.neighborFinset i).card := Finset.card_image_of_injective _ horder
      _ = H.degree i := rfl
  have hdegreeZero := hdegree 0 (by
    intro x hx
    rw [hzero] at hx
    exact hleft x hx)
  rw [hzero] at hdegreeZero
  have hdegreeLast := hdegree (Fin.last p.length) (by
    intro x hx
    rw [hlast] at hx
    exact hright x hx)
  rw [hlast] at hdegreeLast
  have hcycle : (cycleGraph (p.length + 1)) ⊑ H := by
    by_contra hfree
    have hdeficit := path_endpoint_degree_sum_lt hlen H hHpath hfree
    rw [← hdegreeZero, ← hdegreeLast] at hdeficit
    have hsum := hpair u v huv
    omega
  have hspan : p.length + 1 = Fintype.card V := by
    apply Nat.le_antisymm horderCard
    by_contra hshort
    have hlarge : p.length + 1 < Fintype.card V := Nat.lt_of_not_ge hshort
    have hfree := maximum_path_cycle_free_on_image G hconn u v p hp hmax hlen hlarge
    exact hfree hcycle
  let e : Fin (p.length + 1) ↪ V := ⟨order, horder⟩
  obtain ⟨f⟩ := hcycle
  have hwhole : (cycleGraph (p.length + 1)) ⊑ G :=
    ⟨(SimpleGraph.Embedding.comap e G).toCopy.comp f⟩
  exact hspan ▸ hwhole

/-- The same generic degree premise supplies a literal Hamiltonian walk,
through Mathlib's existing cycle-Copy and cycle-length equivalences. -/
theorem exists_hamiltonian_cycle_of_degree_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y →
      Fintype.card V ≤ G.degree x + G.degree y) :
    ∃ (u : V) (c : G.Walk u u), c.IsHamiltonianCycle := by
  obtain ⟨u, c, hc, hlength⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < Fintype.card V)).mp
      (contains_spanning_cycle_of_degree_sum G hconn hcard hpair)
  exact ⟨u, c, SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    ⟨hc, hlength⟩⟩

end ErdosProblems.AntiRamseyCycleGenericHamiltonian

namespace ErdosProblems.AntiRamseyCycleGenericLongPathSeed

open SimpleGraph
open ErdosProblems.AntiRamseyCycleMaximumPathLocalFree
open ErdosProblems.AntiRamseyCyclePathOre

/-- A larger connected finite graph with the supplied minimum and pair degree
bounds contains an injective ordered k-vertex path. The contradiction uses
the cycle order of the actual maximum path, not a fixed shorter cycle order. -/
theorem exists_ordered_path_of_degree_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (hk : 4 ≤ k)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : k ≤ Fintype.card V)
    (hmin : ∀ x : V, 2 ≤ G.degree x)
    (hpair : ∀ x y : V, x ≠ y → k - 1 ≤ G.degree x + G.degree y) :
    ∃ q : Fin k → V, Function.Injective q ∧
      ∀ a b : Fin k, a.val + 1 = b.val → G.Adj (q a) (q b) := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hlen : 2 ≤ p.length := by
    have hmany : 1 < (G.neighborFinset u).card := by
      have hdegree := hmin u
      change 2 ≤ (G.neighborFinset u).card at hdegree
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hmany
    have hua : G.Adj u a := (G.mem_neighborFinset u a).mp ha
    have hub : G.Adj u b := (G.mem_neighborFinset u b).mp hb
    let one : G.Walk u b := SimpleGraph.Walk.cons hub SimpleGraph.Walk.nil
    have hone : one.IsPath := by
      apply SimpleGraph.Walk.IsPath.nil.cons
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hub.ne
    let two : G.Walk a b := SimpleGraph.Walk.cons hua.symm one
    have htwo : two.IsPath := by
      apply hone.cons
      intro hmem
      change a ∈ u :: [b] at hmem
      rcases List.mem_cons.mp hmem with heq | heq
      · exact hua.ne heq.symm
      · exact hab (List.mem_singleton.mp heq)
    have hbound := hmax a b two htwo
    change 2 ≤ p.length at hbound
    exact hbound
  have hleft : ∀ x : V, G.Adj u x → x ∈ p.support := by
    intro x hx
    by_contra hout
    let longer : G.Walk x v := SimpleGraph.Walk.cons hx.symm p
    have hlonger : longer.IsPath := hp.cons hout
    have hbound := hmax x v longer hlonger
    change p.length + 1 ≤ p.length at hbound
    omega
  have hright : ∀ x : V, G.Adj v x → x ∈ p.support := by
    intro x hx
    by_contra hout
    have houtReverse : x ∉ p.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hout
    let longer : G.Walk x u := SimpleGraph.Walk.cons hx.symm p.reverse
    have hlonger : longer.IsPath := hp.reverse.cons houtReverse
    have hbound := hmax x u longer hlonger
    change p.reverse.length + 1 ≤ p.length at hbound
    rw [SimpleGraph.Walk.length_reverse] at hbound
    omega
  let order : Fin (p.length + 1) → V := fun i => p.getVert i.val
  have horder : Function.Injective order := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) hij
  have hzero : order 0 = u := p.getVert_zero
  have hlast : order (Fin.last p.length) = v := p.getVert_length
  have huv : u ≠ v := by
    intro heq
    have hi := horder (hzero.trans (heq.trans hlast.symm))
    have hval := congrArg Fin.val hi
    change 0 = p.length at hval
    omega
  have hlong : k ≤ p.length + 1 := by
    by_contra hshort
    have hshortLength : p.length + 1 < k := Nat.lt_of_not_ge hshort
    have hlarge : p.length + 1 < Fintype.card V :=
      lt_of_lt_of_le hshortLength hcard
    let H : SimpleGraph (Fin (p.length + 1)) := G.comap order
    have hHpath : ∀ a b : Fin (p.length + 1),
        a.val + 1 = b.val → H.Adj a b := by
      intro a b hab
      change G.Adj (p.getVert a.val) (p.getVert b.val)
      have hb := b.isLt
      have hadj := p.adj_getVert_succ (i := a.val) (by omega)
      rw [hab] at hadj
      exact hadj
    have hfree : (cycleGraph (p.length + 1)).Free H :=
      maximum_path_cycle_free_on_image G hconn u v p hp hmax hlen hlarge
    have hneighbors (i : Fin (p.length + 1))
        (hall : ∀ x : V, G.Adj (order i) x → x ∈ p.support) :
        G.neighborFinset (order i) = (H.neighborFinset i).image order := by
      ext x
      constructor
      · intro hx
        have hadj : G.Adj (order i) x := (G.mem_neighborFinset (order i) x).mp hx
        obtain ⟨a, ha, halength⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hall x hadj)
        let j : Fin (p.length + 1) := ⟨a, by omega⟩
        refine Finset.mem_image.mpr ⟨j, ?_, ha⟩
        apply (H.mem_neighborFinset i j).mpr
        change G.Adj (order i) (p.getVert a)
        rw [ha]
        exact hadj
      · intro hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        apply (G.mem_neighborFinset (order i) (order j)).mpr
        exact (show G.Adj (order i) (order j) from
          (H.mem_neighborFinset i j).mp hj)
    have hdegree (i : Fin (p.length + 1))
        (hall : ∀ x : V, G.Adj (order i) x → x ∈ p.support) :
        G.degree (order i) = H.degree i := by
      calc
        G.degree (order i) = (G.neighborFinset (order i)).card := rfl
        _ = ((H.neighborFinset i).image order).card :=
          congrArg Finset.card (hneighbors i hall)
        _ = (H.neighborFinset i).card :=
          Finset.card_image_of_injective _ horder
        _ = H.degree i := rfl
    have hdegreeZero := hdegree 0 (by
      intro x hx
      rw [hzero] at hx
      exact hleft x hx)
    rw [hzero] at hdegreeZero
    have hdegreeLast := hdegree (Fin.last p.length) (by
      intro x hx
      rw [hlast] at hx
      exact hright x hx)
    rw [hlast] at hdegreeLast
    have hdeficit := path_endpoint_degree_sum_lt hlen H hHpath hfree
    rw [← hdegreeZero, ← hdegreeLast] at hdeficit
    have hpairEnds := hpair u v huv
    omega
  let q : Fin k → V := fun i => p.getVert i.val
  refine ⟨q, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn
      (Nat.le_of_lt_succ (lt_of_lt_of_le i.isLt hlong))
      (Nat.le_of_lt_succ (lt_of_lt_of_le j.isLt hlong)) hij
  · intro a b hab
    change G.Adj (p.getVert a.val) (p.getVert b.val)
    have hb := b.isLt
    have hadj := p.adj_getVert_succ (i := a.val) (by omega)
    rw [hab] at hadj
    exact hadj

end ErdosProblems.AntiRamseyCycleGenericLongPathSeed

namespace ErdosProblems.PathUpperReduction.SingleEdgeHamiltonianClosure1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.AllLongSaturation
open ErdosProblems.AntiRamseyCyclePathOre

-- Match the defining finite-neighbor choice in the actual Ore source.
-- This installs no external degree or equality-decision hypothesis.
noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Adding one actual missing edge preserves existence of an n-vertex cycle
when the two ORIGINAL whole-carrier degrees sum to at least n. -/
theorem cycle_contained_add_edge_iff {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (u v : Fin n)
    (huv : u ≠ v) (hmissing : ¬ G.Adj u v)
    (hdegree : n ≤ G.degree u + G.degree v) :
    (cycleGraph n) ⊑ (G ⊔ fromEdgeSet {s(u, v)}) ↔ (cycleGraph n) ⊑ G := by
  classical
  constructor
  · intro hnew
    by_contra hnone
    have hfree : (cycleGraph n).Free G := hnone
    obtain ⟨f⟩ := hnew
    obtain ⟨P, hP, hPlength⟩ := added_pair_path
      (G := G) (u := u) (v := v) (m := n) (by omega) hfree huv hmissing f
    have hcard : P.length + 1 = n := by omega
    have hlength : 2 ≤ P.length := by omega
    let order : Fin (P.length + 1) → Fin n := fun i => P.getVert i.val
    have horder : Function.Injective order := by
      intro i j hij
      apply Fin.ext
      exact hP.getVert_injOn (Nat.le_of_lt_succ i.isLt)
        (Nat.le_of_lt_succ j.isLt) hij
    have hzero : order 0 = u := P.getVert_zero
    have hlast : order (Fin.last P.length) = v := P.getVert_length
    have hpath : ∀ a b : Fin (P.length + 1),
        a.val + 1 = b.val → G.Adj (order a) (order b) := by
      intro a b hab
      change G.Adj (P.getVert a.val) (P.getVert b.val)
      have hadj := P.adj_getVert_succ (i := a.val) (by omega)
      rw [hab] at hadj
      exact hadj
    have himageCard :
        ((Finset.univ : Finset (Fin (P.length + 1))).image order).card = n := by
      rw [Finset.card_image_of_injective _ horder, Finset.card_univ,
        Fintype.card_fin]
      exact hcard
    have himage :
        (Finset.univ : Finset (Fin (P.length + 1))).image order =
          (Finset.univ : Finset (Fin n)) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa only [himageCard, Finset.card_univ, Fintype.card_fin] using
        (Nat.le_refl n)
    have hfreeOnPath : (cycleGraph (P.length + 1)).Free (G.comap order) := by
      intro hcopy
      obtain ⟨g⟩ := hcopy
      let e : Fin (P.length + 1) ↪ Fin n := ⟨order, horder⟩
      have hactual : (cycleGraph (P.length + 1)) ⊑ G :=
        ⟨(SimpleGraph.Embedding.comap e G).toCopy.comp g⟩
      apply hfree
      exact Eq.mp (congrArg (fun m : ℕ => (cycleGraph m) ⊑ G) hcard) hactual
    have hdeficit := ordered_path_internal_endpoint_degree_sum_lt
      hlength G order horder hpath hfreeOnPath
    simp only [himage, Finset.inter_univ] at hdeficit
    have hdegreePath :
        G.degree (order 0) + G.degree (order (Fin.last P.length)) < n := by
      simpa only [card_neighborFinset_eq_degree, hcard] using hdeficit
    have hsmall : G.degree u + G.degree v < n := by
      rw [hzero, hlast] at hdegreePath
      exact hdegreePath
    omega
  · intro hold
    exact hold.mono_right le_sup_left

end ErdosProblems.PathUpperReduction.SingleEdgeHamiltonianClosure1105

namespace ErdosProblems.PathUpperReduction.EvenActualContactClosure1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.SingleEdgeHamiltonianClosure1105

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Core vertices with an ACTUAL ORIGINAL outsider neighbor. -/
noncomputable def originalContacts {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact S.filter (fun a => ∃ x, x ∉ S ∧ G.Adj x a)

/-- Precisely the outsider/original-contact pairs, with undirected edges. -/
noncomputable def originalContactEdges {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact ((Finset.univ \ S).product (originalContacts G S)).image
    (fun p => s(p.1, p.2))

/-- Fill only those original contact pairs; no vertex or outsider edge is added. -/
noncomputable def fillOriginalContacts {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : SimpleGraph (Fin n) :=
  G ⊔ fromEdgeSet (originalContactEdges G S : Set (Sym2 (Fin n)))

noncomputable def fillPairs {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) := by
  classical
  exact G ⊔ fromEdgeSet (P.image (fun p => s(p.1, p.2)) : Set (Sym2 (Fin n)))

theorem fillPairs_insert {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    fillPairs G (insert p P) = fillPairs G P ⊔ fromEdgeSet {s(p.1, p.2)} := by
  classical
  have hset :
      ((insert p P).image (fun q => s(q.1, q.2)) : Set (Sym2 (Fin n))) =
        {s(p.1, p.2)} ∪ (P.image (fun q => s(q.1, q.2)) : Set (Sym2 (Fin n))) := by
    ext e
    simp only [Finset.image_insert, Finset.mem_coe, Finset.mem_insert,
      Set.mem_union, Set.mem_singleton_iff]
  simp only [fillPairs, hset, fromEdgeSet_union]
  ac_rfl

/-- Internal finite induction: the caller supplies ORIGINAL pair bounds here;
the public actual-contact theorem derives all of them from original data. -/
theorem finite_pair_closure_iff {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (P : Finset (Fin n × Fin n))
    (hpair : ∀ p, p ∈ P → p.1 ≠ p.2 ∧ n ≤ G.degree p.1 + G.degree p.2) :
    cycleGraph n ⊑ fillPairs G P ↔ cycleGraph n ⊑ G := by
  classical
  revert hpair
  induction P using Finset.induction_on with
  | empty => intro _hpair; simp [fillPairs]
  | @insert p P _hp ih =>
    intro hpair
    have hthis := hpair p (Finset.mem_insert_self p P)
    have hrest : ∀ q, q ∈ P → q.1 ≠ q.2 ∧ n ≤ G.degree q.1 + G.degree q.2 := by
      intro q hq
      exact hpair q (Finset.mem_insert_of_mem hq)
    have hrestIff := ih hrest
    let H : SimpleGraph (Fin n) := fillPairs G P
    have hGH : G ≤ H := le_sup_left
    have hdegree : n ≤ H.degree p.1 + H.degree p.2 := by
      exact hthis.2.trans (Nat.add_le_add
        (G.degree_le_of_le (v := p.1) hGH) (G.degree_le_of_le (v := p.2) hGH))
    have hsingle : cycleGraph n ⊑ (H ⊔ fromEdgeSet {s(p.1, p.2)}) ↔
        cycleGraph n ⊑ H := by
      by_cases hadj : H.Adj p.1 p.2
      · have hsubset : ({s(p.1, p.2)} : Set (Sym2 (Fin n))) ⊆ H.edgeSet := by
          intro e he
          rcases Set.mem_singleton_iff.mp he with rfl
          exact hadj
        have hedge : fromEdgeSet {s(p.1, p.2)} ≤ H := by
          simpa only [fromEdgeSet_edgeSet] using fromEdgeSet_mono hsubset
        rw [sup_eq_left.mpr hedge]
      · exact cycle_contained_add_edge_iff hn H p.1 p.2 hthis.1 hadj hdegree
    rw [fillPairs_insert]
    exact hsingle.trans hrestIff

theorem contacted_core_degree {d : ℕ}
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    {a : Fin (2 * d + 3)} (ha : a ∈ originalContacts G S) :
    d + 3 ≤ G.degree a := by
  classical
  have hacontact : a ∈ S ∧ ∃ w, w ∉ S ∧ G.Adj w a := by
    simpa only [originalContacts, Finset.mem_filter] using ha
  obtain ⟨w, hwS, hwa⟩ := hacontact.2
  have hwErase : w ∉ S.erase a := by
    intro hw
    exact hwS (Finset.mem_of_mem_erase hw)
  let T : Finset (Fin (2 * d + 3)) := insert w (S.erase a)
  have hTcard : T.card = S.card := by
    change (insert w (S.erase a)).card = S.card
    rw [Finset.card_insert_of_notMem hwErase]
    exact Finset.card_erase_add_one hacontact.1
  have hTsub : T ⊆ G.neighborFinset a := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzw | hzErase
    · subst z
      exact (mem_neighborFinset (G := G) (v := a) w).mpr hwa.symm
    · have hzS := (Finset.mem_erase.mp hzErase).2
      have hza := (Finset.mem_erase.mp hzErase).1
      exact (mem_neighborFinset (G := G) (v := a) z).mpr
        (hclique hacontact.1 hzS hza.symm)
  have hbound := Finset.card_le_card hTsub
  rw [hTcard, hScard, card_neighborFinset_eq_degree] at hbound
  exact hbound

/-- Filling exactly the ORIGINAL contacted-core pairs preserves the SAME
spanning-cycle predicate. Original pair thresholds and finite reversal are
derived internally, without a supplied order, path, cycle or degree oracle. -/
theorem cycle_contained_fill_original_contacts_iff {d : ℕ} (_hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x) :
    cycleGraph (2 * d + 3) ⊑ fillOriginalContacts G S ↔
      cycleGraph (2 * d + 3) ⊑ G := by
  classical
  let P : Finset (Fin (2 * d + 3) × Fin (2 * d + 3)) :=
    (Finset.univ \ S).product (originalContacts G S)
  have hpair : ∀ p, p ∈ P → p.1 ≠ p.2 ∧
      2 * d + 3 ≤ G.degree p.1 + G.degree p.2 := by
    intro p hp
    have hprod := Finset.mem_product.mp hp
    have hxS : p.1 ∉ S := (Finset.mem_sdiff.mp hprod.1).2
    have haS : p.2 ∈ S := by
      have hcontact : p.2 ∈ S ∧ ∃ w, w ∉ S ∧ G.Adj w p.2 := by
        simpa only [originalContacts, Finset.mem_filter] using hprod.2
      exact hcontact.1
    have hne : p.1 ≠ p.2 := by
      intro heq
      exact hxS (heq.symm ▸ haS)
    refine ⟨hne, ?_⟩
    have hout := houtsider p.1 hxS
    have hcore := contacted_core_degree G S hScard hclique hprod.2
    omega
  have hclosure := finite_pair_closure_iff (by omega) G P hpair
  simpa only [fillOriginalContacts, originalContactEdges, fillPairs, P] using hclosure

end ErdosProblems.PathUpperReduction.EvenActualContactClosure1105

namespace ErdosProblems.PathUpperReduction.EvenOriginalContactRigidity1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.EvenActualContactClosure1105
open ErdosProblems.PathUpperReduction.EvenOutsiderEdgeCover1105

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Actual contact filling and its exact reversal rule out an ORIGINAL
outsider edge, without an outsider-independence or filling oracle. -/
theorem original_outsiders_independent {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (hCcard : (originalContacts G S).card = d)
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G) :
    ∀ x, x ∉ S → ∀ y, y ∉ S → ¬ G.Adj x y := by
  classical
  intro x hxS y hyS hxy
  let C := originalContacts G S
  let F := fillOriginalContacts G S
  have hCS : C ⊆ S := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hGF : G ≤ F := le_sup_left
  have hfilled : ∀ z, z ∉ S → ∀ a, a ∈ C → F.Adj z a := by
    intro z hzS a haC
    have haS := hCS haC
    have hza : z ≠ a := by
      intro hza
      exact hzS (hza.symm ▸ haS)
    change G.Adj z a ∨
      (fromEdgeSet (originalContactEdges G S : Set (Sym2 (Fin (2 * d + 3))))).Adj z a
    apply Or.inr
    apply (fromEdgeSet_adj _).mpr
    refine ⟨?_, hza⟩
    change s(z, a) ∈
      ((Finset.univ \ S).product (originalContacts G S)).image
        (fun p => s(p.1, p.2))
    exact Finset.mem_image.mpr ⟨(z, a), Finset.mem_product.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzS⟩, haC⟩, rfl⟩
  have hnew : cycleGraph (2 * d + 3) ⊑ F :=
    cycle_of_actual_outsider_edge hd G F hGF S C hScard hclique hCS
      hCcard hfilled ⟨x, y, hxS, hyS, hxy⟩
  have hclosure := cycle_contained_fill_original_contacts_iff
    hd G S hScard hclique houtsider
  exact hfree (hclosure.mp hnew)

/-- Every ORIGINAL outsider has exactly the actual original contact set as
its neighborhood, and its original whole-carrier degree is exactly d. -/
theorem outsider_neighbors_and_degree {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (hCcard : (originalContacts G S).card = d)
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (x : Fin (2 * d + 3)) (hxS : x ∉ S) :
    G.neighborFinset x = originalContacts G S ∧ G.degree x = d := by
  classical
  have hind := original_outsiders_independent hd G S hScard hclique
    hCcard houtsider hfree
  have hsub : G.neighborFinset x ⊆ originalContacts G S := by
    intro a ha
    have hxa := (mem_neighborFinset (G := G) (v := x) a).mp ha
    have haS : a ∈ S := by
      by_contra haS
      exact hind x hxS a haS hxa
    change a ∈ S.filter (fun a => ∃ z, z ∉ S ∧ G.Adj z a)
    exact Finset.mem_filter.mpr ⟨haS, x, hxS, hxa⟩
  have hcard : (originalContacts G S).card ≤ (G.neighborFinset x).card := by
    rw [hCcard, card_neighborFinset_eq_degree]
    exact houtsider x hxS
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  refine ⟨heq, ?_⟩
  rw [← card_neighborFinset_eq_degree, heq, hCcard]

/-- The actual ORIGINAL partition has d anchors, three other clique vertices,
and d outsiders. Its displayed exact adjacency is K_d join (K_3 disjoint I_d)
on those actual supports, without a supplied partition/order equivalence. -/
theorem original_contact_partition_and_adjacency {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (hCcard : (originalContacts G S).card = d)
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G) :
    originalContacts G S ⊆ S ∧
      (S \ originalContacts G S).card = 3 ∧
      (Finset.univ \ S).card = d ∧
      ∀ u v, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨
          (u ∉ S ∧ v ∈ originalContacts G S) ∨
          (v ∉ S ∧ u ∈ originalContacts G S)) := by
  classical
  have hCS : originalContacts G S ⊆ S := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hthree : (S \ originalContacts G S).card = 3 := by
    have hcard := Finset.card_sdiff_add_card_eq_card hCS
    rw [hCcard, hScard] at hcard
    omega
  have hOcard : (Finset.univ \ S).card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin, hScard] at hcard
    omega
  refine ⟨hCS, hthree, hOcard, ?_⟩
  intro u v
  constructor
  · intro huv
    refine ⟨huv.ne, ?_⟩
    by_cases huS : u ∈ S
    · by_cases hvS : v ∈ S
      · exact Or.inl ⟨huS, hvS⟩
      · apply Or.inr
        apply Or.inr
        refine ⟨hvS, ?_⟩
        have heq := (outsider_neighbors_and_degree hd G S hScard hclique
          hCcard houtsider hfree v hvS).1
        rw [← heq]
        exact (mem_neighborFinset (G := G) (v := v) u).mpr huv.symm
    · apply Or.inr
      apply Or.inl
      refine ⟨huS, ?_⟩
      have heq := (outsider_neighbors_and_degree hd G S hScard hclique
        hCcard houtsider hfree u huS).1
      rw [← heq]
      exact (mem_neighborFinset (G := G) (v := u) v).mpr huv
  · rintro ⟨huv, hSS | hOC | hCO⟩
    · exact hclique hSS.1 hSS.2 huv
    · apply (mem_neighborFinset (G := G) (v := u) v).mp
      rw [(outsider_neighbors_and_degree hd G S hScard hclique
        hCcard houtsider hfree u hOC.1).1]
      exact hOC.2
    · apply Adj.symm
      apply (mem_neighborFinset (G := G) (v := v) u).mp
      rw [(outsider_neighbors_and_degree hd G S hScard hclique
        hCcard houtsider hfree v hCO.1).1]
      exact hCO.2

end ErdosProblems.PathUpperReduction.EvenOriginalContactRigidity1105

section

universe u

namespace ErdosProblems.PathErdosGallai

open SimpleGraph
open scoped BigOperators
open ErdosProblems.AntiRamseyCycleGenericLongPathSeed
open ErdosProblems.AntiRamseyPathFiveComponents

theorem two_mul_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  calc
    2 * n.choose 2 = n.descFactorial 2 := by
      simpa only [Nat.factorial_two] using
        (Nat.descFactorial_eq_factorial_mul_choose n 2).symm
    _ = (n - 1) * n.descFactorial 1 := Nat.descFactorial_succ n 1
    _ = (n - 1) * n :=
      congrArg (fun m => (n - 1) * m) (Nat.descFactorial_one n)
    _ = n * (n - 1) := Nat.mul_comm _ _

theorem degree_le_one_of_path_three_free
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (pathGraph 3).Free G) (x : V) : G.degree x ≤ 1 := by
  classical
  by_contra hdegree
  have hmany : 1 < (G.neighborFinset x).card := by
    change 1 < G.degree x
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hmany
  have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp ha
  have hxb : G.Adj x b := (G.mem_neighborFinset x b).mp hb
  let one : G.Walk x b := Walk.cons hxb Walk.nil
  have hone : one.IsPath := by
    apply Walk.IsPath.nil.cons
    simpa only [Walk.support_nil, List.mem_singleton] using hxb.ne
  let two : G.Walk a b := Walk.cons hxa.symm one
  have htwo : two.IsPath := by
    apply hone.cons
    intro hmem
    change a ∈ x :: [b] at hmem
    rcases List.mem_cons.mp hmem with heq | heq
    · exact hxa.ne heq.symm
    · exact hab (List.mem_singleton.mp heq)
  have hcopy : (pathGraph 3) ⊑ G := by
    have h := htwo.isContained_pathGraph
    change (pathGraph 3) ⊑ G at h
    exact h
  exact hfree hcopy

theorem component_card_le_of_large_degrees
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 3 ≤ d) (hfree : (pathGraph (d + 1)).Free G)
    (hlarge : ∀ x : V, d ≤ 2 * G.degree x)
    (C : G.ConnectedComponent) : Nat.card C ≤ d := by
  classical
  have hdegree (x : C) :
      C.toSimpleGraph.degree x = G.degree x.val := by
    let e : C.toSimpleGraph.neighborSet x ≃ G.neighborSet x.val := {
      toFun := fun y => ⟨y.val.val, y.property⟩
      invFun := fun y =>
        ⟨⟨y.val, C.mem_supp_of_adj_mem_supp x.property y.property⟩, y.property⟩
      left_inv := by intro y; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl
    }
    calc
      C.toSimpleGraph.degree x = Nat.card (C.toSimpleGraph.neighborSet x) := by
        rw [Nat.card_eq_fintype_card, C.toSimpleGraph.card_neighborSet_eq_degree]
      _ = Nat.card (G.neighborSet x.val) := Nat.card_congr e
      _ = G.degree x.val := by
        rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
  by_contra hcard
  have hcardLargeNat : d + 1 ≤ Nat.card C := by omega
  have hcardLarge : d + 1 ≤ Fintype.card C := by
    simpa only [Fintype.card_eq_nat_card] using hcardLargeNat
  have hmin (x : C) : 2 ≤ C.toSimpleGraph.degree x := by
    have hx := hlarge x.val
    rw [← hdegree x] at hx
    omega
  have hpair (x y : C) (_hxy : x ≠ y) :
      d + 1 - 1 ≤ C.toSimpleGraph.degree x + C.toSimpleGraph.degree y := by
    have hx := hlarge x.val
    have hy := hlarge y.val
    rw [← hdegree x] at hx
    rw [← hdegree y] at hy
    omega
  obtain ⟨q, hq, hstep⟩ :=
    exists_ordered_path_of_degree_bounds (by omega : 4 ≤ d + 1)
      C.toSimpleGraph C.connected_toSimpleGraph hcardLarge hmin hpair
  let f : (pathGraph (d + 1)).Copy C.toSimpleGraph := {
    toHom := {
      toFun := q
      map_rel' := by
        intro a b hab
        rcases pathGraph_adj.mp hab with hab | hba
        · exact hstep a b hab
        · exact (hstep b a hba).symm
    }
    injective' := hq
  }
  exact hfree ⟨(Copy.induce G C.supp).comp f⟩

theorem edge_bound_of_large_degrees
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 3 ≤ d) (hfree : (pathGraph (d + 1)).Free G)
    (hlarge : ∀ x : V, d ≤ 2 * G.degree x) :
    2 * G.edgeFinset.card ≤ (d - 1) * Fintype.card V := by
  classical
  have hcomponent (C : G.ConnectedComponent) :
      2 * Nat.card C.toSimpleGraph.edgeSet ≤
        (d - 1) * Fintype.card C := by
    have hcard : Fintype.card C ≤ d := by
      simpa only [Fintype.card_eq_nat_card] using
        component_card_le_of_large_degrees G d hd hfree hlarge C
    have hedge : Nat.card C.toSimpleGraph.edgeSet =
        C.toSimpleGraph.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card]
      exact C.toSimpleGraph.card_edgeSet
    rw [hedge]
    have hsub : Fintype.card C - 1 ≤ d - 1 := by omega
    calc
      2 * C.toSimpleGraph.edgeFinset.card ≤
          2 * (Fintype.card C).choose 2 :=
        Nat.mul_le_mul_left 2 C.toSimpleGraph.card_edgeFinset_le_card_choose_two
      _ = Fintype.card C * (Fintype.card C - 1) :=
        two_mul_choose_two _
      _ ≤ Fintype.card C * (d - 1) :=
        Nat.mul_le_mul_left _ hsub
      _ = (d - 1) * Fintype.card C := Nat.mul_comm _ _
  have hcarrierCard (C : G.ConnectedComponent) :
      Fintype.card C = Fintype.card C.supp := by
    calc
      Fintype.card C = Nat.card C := Fintype.card_eq_nat_card
      _ = Nat.card C.supp := rfl
      _ = Fintype.card C.supp := Fintype.card_eq_nat_card.symm
  calc
    2 * G.edgeFinset.card =
        2 * (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) :=
      congrArg (fun n => 2 * n) (edge_card_eq_sum_component_edge_card G)
    _ = ∑ C : G.ConnectedComponent, 2 * Nat.card C.toSimpleGraph.edgeSet := by
      rw [Finset.mul_sum]
    _ ≤ ∑ C : G.ConnectedComponent, (d - 1) * Fintype.card C :=
      Finset.sum_le_sum (fun C _ => hcomponent C)
    _ = ∑ C : G.ConnectedComponent, (d - 1) * Fintype.card C.supp := by
      simp_rw [hcarrierCard]
    _ = (d - 1) * (∑ C : G.ConnectedComponent, Fintype.card C.supp) := by
      rw [Finset.mul_sum]
    _ = (d - 1) * Fintype.card V :=
      congrArg (fun n => (d - 1) * n) (vertex_card_eq_sum_component_card G).symm

theorem edge_bound_finset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d) (hfree : (pathGraph (d + 1)).Free G) :
    2 * G.edgeFinset.card ≤ (d - 1) * Fintype.card V := by
  classical
  by_cases hd2 : d = 2
  · subst d
    have hdegrees (x : V) : G.degree x ≤ 1 :=
      degree_le_one_of_path_three_free G hfree x
    calc
      2 * G.edgeFinset.card = ∑ x : V, G.degree x :=
        G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _x : V, (1 : ℕ) := Finset.sum_le_sum (fun x _ => hdegrees x)
      _ = (2 - 1) * Fintype.card V := by simp
  · have hd3 : 3 ≤ d := by omega
    let P : ℕ → Prop := fun n =>
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        Fintype.card W = n → (pathGraph (d + 1)).Free H →
        2 * H.edgeFinset.card ≤ (d - 1) * n
    have hP : ∀ n : ℕ, P n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        dsimp [P]
        intro W _instF _instD H _instA hcard hfreeH
        by_cases hlow : ∃ x : W, 2 * H.degree x ≤ d - 1
        · obtain ⟨x, hx⟩ := hlow
          let S : Set W := ({x} : Set W)ᶜ
          let H' : SimpleGraph S := H.induce S
          have hcardS : Fintype.card S = Fintype.card W - 1 := by
            calc
              Fintype.card S = Nat.card S := Fintype.card_eq_nat_card
              _ = Nat.card ↥(({x} : Set W)ᶜ) := rfl
              _ = Fintype.card ↥(({x} : Set W)ᶜ) := Nat.card_eq_fintype_card
              _ = Fintype.card W - Fintype.card ({x} : Set W) :=
                Fintype.card_compl_set ({x} : Set W)
              _ = Fintype.card W - 1 := by rw [Set.card_singleton]
          have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨x⟩
          have hsmall : Fintype.card S < n := by
            rw [hcardS, hcard]
            omega
          have hcardAdd : Fintype.card S + 1 = n := by
            rw [hcardS, hcard]
            omega
          have hfreeS : (pathGraph (d + 1)).Free H' := by
            rintro ⟨f⟩
            exact hfreeH ⟨(Copy.induce H S).comp f⟩
          have hIH := ih (Fintype.card S) hsmall S H' rfl hfreeS
          have hdelete : H'.edgeFinset.card = H.edgeFinset.card - H.degree x :=
            (H.card_edgeFinset_induce_compl_singleton x).trans
              (H.card_edgeFinset_deleteIncidenceSet x)
          have hdegreeEdges : H.degree x ≤ H.edgeFinset.card :=
            H.degree_le_card_edgeFinset (v := x)
          have hedgeAdd : H'.edgeFinset.card + H.degree x = H.edgeFinset.card := by
            omega
          calc
            2 * H.edgeFinset.card = 2 * (H'.edgeFinset.card + H.degree x) :=
              congrArg (fun m => 2 * m) hedgeAdd.symm
            _ = 2 * H'.edgeFinset.card + 2 * H.degree x := by rw [Nat.mul_add]
            _ ≤ (d - 1) * Fintype.card S + (d - 1) := Nat.add_le_add hIH hx
            _ = (d - 1) * (Fintype.card S + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ = (d - 1) * n := congrArg (fun m => (d - 1) * m) hcardAdd
        · have hlarge (x : W) : d ≤ 2 * H.degree x := by
            have hx : ¬ 2 * H.degree x ≤ d - 1 := fun h => hlow ⟨x, h⟩
            omega
          have hbound := edge_bound_of_large_degrees H d hd3 hfreeH hlarge
          simpa only [hcard] using hbound
    exact hP (Fintype.card V) V G rfl hfree

/-- Uniform Erdős–Gallai: a finite simple graph containing no non-induced
(d+1)-vertex path has at most (d-1)|V|/2 edges. No connectedness, supplied
degree, coloring or representative hypothesis is imposed. -/
theorem erdos_gallai_edge_bound {V : Type u} [Finite V]
    (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d)
    (hfree : (pathGraph (d + 1)).Free G) :
    2 * Nat.card G.edgeSet ≤ (d - 1) * Nat.card V := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have hfin := edge_bound_finset G d hd hfree
  have hedge : Nat.card G.edgeSet = G.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact G.card_edgeSet
  rw [hedge, Nat.card_eq_fintype_card]
  exact hfin

end ErdosProblems.PathErdosGallai

end

namespace ErdosProblems.PathUpperReduction.EvenOriginalContactCount1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.TightCoreBlockEdgeLedger1105
open ErdosProblems.PathUpperReduction.EvenActualContactClosure1105
open ErdosProblems.PathUpperReduction.EvenLastBlockRigidity1105
open ErdosProblems.PathUpperReduction.EvenOriginalContactRigidity1105

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

/-- Each canonical unordered crossing edge has one outsider/contact
orientation. A subset of the product's image suffices for its capacity bound;
no injectivity or oriented-cross-count premise is needed. -/
theorem cross_edges_le_contact_capacity {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    (coreCrossEdges G S Finset.univ).card ≤
      (Finset.univ \ S).card * (originalContacts G S).card := by
  classical
  let O : Finset (Fin n) := Finset.univ \ S
  let C := originalContacts G S
  let P := O.product C
  have hsub : coreCrossEdges G S Finset.univ ⊆
      P.image (fun p => s(p.1, p.2)) := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y he
    unfold coreCrossEdges nonCoreEdges withinEdges at he
    simp only [Finset.mem_filter, Finset.subset_iff, Sym2.mem_toFinset,
      Sym2.mem_iff, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_edgeFinset] at he
    rcases he with ⟨⟨⟨hxy, _heUniv⟩, heNotS⟩, heNotO⟩
    have hnotS : ¬ (x ∈ S ∧ y ∈ S) := by
      rintro ⟨hxS, hyS⟩
      apply heNotS
      intro z hz
      rcases hz with rfl | rfl
      · exact hxS
      · exact hyS
    have hnotO : ¬ (x ∉ S ∧ y ∉ S) := by
      rintro ⟨hxS, hyS⟩
      apply heNotO
      intro z hz
      rcases hz with rfl | rfl
      · exact hxS
      · exact hyS
    by_cases hxS : x ∈ S
    · have hyS : y ∉ S := fun hyS => hnotS ⟨hxS, hyS⟩
      have hxC : x ∈ C := by
        change x ∈ S.filter (fun a => ∃ z, z ∉ S ∧ G.Adj z a)
        exact Finset.mem_filter.mpr ⟨hxS, y, hyS, hxy.symm⟩
      have hyO : y ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyS⟩
      exact Finset.mem_image.mpr ⟨(y, x),
        Finset.mem_product.mpr ⟨hyO, hxC⟩, Sym2.eq_swap⟩
    · have hyS : y ∈ S := by
        by_contra hyS
        exact hnotO ⟨hxS, hyS⟩
      have hyC : y ∈ C := by
        change y ∈ S.filter (fun a => ∃ z, z ∉ S ∧ G.Adj z a)
        exact Finset.mem_filter.mpr ⟨hyS, x, hxS, hxy⟩
      have hxO : x ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxS⟩
      exact Finset.mem_image.mpr ⟨(x, y),
        Finset.mem_product.mpr ⟨hxO, hyC⟩, rfl⟩
  calc
    (coreCrossEdges G S Finset.univ).card ≤
        (P.image (fun p => s(p.1, p.2))).card := Finset.card_le_card hsub
    _ ≤ P.card := Finset.card_image_le
    _ = (Finset.univ \ S).card * (originalContacts G S).card :=
      Finset.card_product _ _

/-- Construct an actual path plus all remaining singleton outsiders.
The cardinal identity is additive, avoiding truncated subtraction guards. -/
theorem exists_path_singleton_cover {V : Type*}
    (G : SimpleGraph V) (O : Finset V) (p : List V)
    (hp : p ≠ []) (hchain : p.IsChain G.Adj) (hnodup : p.Nodup)
    (hinside : ∀ z, z ∈ p → z ∈ O) :
    ∃ cover : List (List V),
      (∀ q, q ∈ cover → q ≠ []) ∧
      (∀ q, q ∈ cover → q.IsChain G.Adj) ∧
      cover.flatten.Nodup ∧
      (∀ z, z ∈ cover.flatten ↔ z ∈ O) ∧
      cover.length + p.length = O.card + 1 := by
  classical
  let R := O \ p.toFinset
  let cover := p :: R.toList.map (fun z => [z])
  have hflatten : cover.flatten = p ++ R.toList := by
    change p ++ (R.toList.map (fun z => [z])).flatten = p ++ R.toList
    rw [← List.flatMap_def, List.flatMap_singleton']
  have hnonempty : ∀ q, q ∈ cover → q ≠ [] := by
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hqR
    · subst q
      exact hp
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hqR
      simp
  have hpaths : ∀ q, q ∈ cover → q.IsChain G.Adj := by
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hqR
    · subst q
      exact hchain
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp hqR
      exact List.IsChain.singleton (R := G.Adj) z
  have hsep : p.Disjoint R.toList := by
    rw [List.disjoint_left]
    intro z hzp hzR
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hzR)).2
      (List.mem_toFinset.mpr hzp)
  have hcoverNodup : cover.flatten.Nodup := by
    rw [hflatten]
    exact hnodup.append R.nodup_toList hsep
  have hcovers : ∀ z, z ∈ cover.flatten ↔ z ∈ O := by
    intro z
    rw [hflatten, List.mem_append]
    constructor
    · rintro (hzp | hzR)
      · exact hinside z hzp
      · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hzR)).1
    · intro hzO
      by_cases hzp : z ∈ p
      · exact Or.inl hzp
      · apply Or.inr
        apply Finset.mem_toList.mpr
        exact Finset.mem_sdiff.mpr ⟨hzO, fun hz => hzp (List.mem_toFinset.mp hz)⟩
  have hpSub : p.toFinset ⊆ O := by
    intro z hz
    exact hinside z (List.mem_toFinset.mp hz)
  have hcard := Finset.card_sdiff_add_card_eq_card hpSub
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  have hlength : cover.length + p.length = O.card + 1 := by
    simp only [cover, List.length_cons, List.length_map, Finset.length_toList]
    change R.card + p.length = O.card at hcard
    omega
  exact ⟨cover, hnonempty, hpaths, hcoverNodup, hcovers, hlength⟩

/-- A derived ORIGINAL outsider cover with enough actual contacts contradicts
original cycle-freedom, by filling and reversing only actual contact pairs. -/
theorem no_contact_cover {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (cover : List (List (Fin (2 * d + 3))))
    (hnonempty : ∀ p, p ∈ cover → p ≠ [])
    (hpaths : ∀ p, p ∈ cover → p.IsChain G.Adj)
    (hnodup : cover.flatten.Nodup)
    (hcovers : ∀ z, z ∈ cover.flatten ↔ z ∉ S)
    (hcapacity : cover.length + 1 ≤ (originalContacts G S).card) : False := by
  classical
  let C := originalContacts G S
  let F := fillOriginalContacts G S
  have hCS : C ⊆ S := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hGF : G ≤ F := le_sup_left
  have hfilled : ∀ z, z ∉ S → ∀ a, a ∈ C → F.Adj z a := by
    intro z hzS a haC
    have haS := hCS haC
    have hza : z ≠ a := by
      intro hza
      exact hzS (hza.symm ▸ haS)
    change G.Adj z a ∨
      (fromEdgeSet (originalContactEdges G S : Set (Sym2 (Fin (2 * d + 3))))).Adj z a
    apply Or.inr
    apply (fromEdgeSet_adj _).mpr
    refine ⟨?_, hza⟩
    change s(z, a) ∈
      ((Finset.univ \ S).product (originalContacts G S)).image
        (fun p => s(p.1, p.2))
    exact Finset.mem_image.mpr ⟨(z, a), Finset.mem_product.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzS⟩, haC⟩, rfl⟩
  have hnew : cycleGraph (2 * d + 3) ⊑ F :=
    cycle_of_actual_outsider_path_cover hd G F hGF S C hScard hclique
      hCS cover hnonempty hpaths hnodup hcovers hcapacity hfilled
  exact hfree ((cycle_contained_fill_original_contacts_iff
    hd G S hScard hclique houtsider).mp hnew)

/-- The actual ORIGINAL suffix population, counting every crossing edge and
every internal-outsider edge once, determines the actual contact cardinality.
There is no independence, contact-count, path, cover or classification oracle. -/
theorem original_contacts_card_eq {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (hledger : d * d ≤ (coreCrossEdges G S Finset.univ).card +
      (withinEdges G (Finset.univ \ S)).card) :
    (originalContacts G S).card = d := by
  classical
  let O : Finset (Fin (2 * d + 3)) := Finset.univ \ S
  let C := originalContacts G S
  have hOcard : O.card = d := by
    have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    change O.card + S.card = (Finset.univ : Finset (Fin (2 * d + 3))).card at hcard
    rw [Finset.card_univ, Fintype.card_fin, hScard] at hcard
    omega
  have hcle : C.card ≤ d := by
    by_contra hcle
    obtain ⟨x, hxO⟩ := Finset.card_pos.mp (by omega : 0 < O.card)
    obtain ⟨cover, hnonempty, hpaths, hnodup, hcovers, hlength⟩ :=
      exists_path_singleton_cover G O [x] (by simp)
        (List.IsChain.singleton (R := G.Adj) x) (by simp)
        (by
          intro z hz
          have hzx : z = x := List.mem_singleton.mp hz
          exact hzx.symm ▸ hxO)
    have hcapacity : cover.length + 1 ≤ C.card := by
      simp only [List.length_singleton] at hlength
      omega
    have hcoverOutside : ∀ z, z ∈ cover.flatten ↔ z ∉ S := by
      intro z
      simpa only [O, Finset.mem_sdiff, Finset.mem_univ, true_and] using hcovers z
    exact no_contact_cover hd G S hScard hclique houtsider hfree
      cover hnonempty hpaths hnodup hcoverOutside hcapacity
  have hcge : d ≤ C.card := by
    by_contra hcge
    let t := d - C.card
    have ht : 1 ≤ t := by omega
    have hct : C.card + t = d := by omega
    have hcross := cross_edges_le_contact_capacity G S
    change (coreCrossEdges G S Finset.univ).card ≤ O.card * C.card at hcross
    rw [hOcard] at hcross
    have hEQ : d * t ≤ (withinEdges G O).card := by
      change d * d ≤ (coreCrossEdges G S Finset.univ).card +
        (withinEdges G O).card at hledger
      nlinarith
    let Q := G.induce (O : Set (Fin (2 * d + 3)))
    have hQcard : Nat.card (O : Set (Fin (2 * d + 3))) = d :=
      (Nat.card_eq_finsetCard O).trans hOcard
    have hedgeQ : Nat.card Q.edgeSet = (withinEdges G O).card := by
      have hfilter := G.card_filter_edgeFinset_toFinset_subset O
      have hedge : Nat.card Q.edgeSet = Q.edgeFinset.card := by
        rw [Nat.card_eq_fintype_card]
        exact Q.edgeFinset_card.symm
      refine hedge.trans (hfilter.symm.trans ?_)
      unfold withinEdges
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.subset_iff, Sym2.mem_toFinset]
    have hpath : pathGraph (t + 2) ⊑ Q := by
      by_contra hpath
      have hEG := ErdosProblems.PathErdosGallai.erdos_gallai_edge_bound
        Q (t + 1) (by omega) (by simpa only [Nat.add_assoc] using hpath)
      rw [hedgeQ, hQcard] at hEG
      have hpred : t + 1 - 1 = t := by omega
      rw [hpred] at hEG
      have hpositive : 0 < d * t := Nat.mul_pos (by omega) (by omega)
      nlinarith
    obtain ⟨f⟩ := hpath
    let order : Fin (t + 2) → Fin (2 * d + 3) := fun i => (f i : Fin (2 * d + 3))
    have horder : Function.Injective order := by
      intro i j hij
      apply f.injective
      exact Subtype.ext hij
    let p := List.ofFn order
    have hplen : p.length = t + 2 := List.length_ofFn
    have hp : p ≠ [] := by
      intro hnil
      rw [hnil, List.length_nil] at hplen
      omega
    have hchain : p.IsChain G.Adj := by
      apply List.isChain_ofFn.mpr
      intro i hi
      exact f.toHom.map_adj (pathGraph_adj.mpr (Or.inl rfl))
    have hpnodup : p.Nodup := List.nodup_ofFn_ofInjective horder
    have hpinside : ∀ z, z ∈ p → z ∈ O := by
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact (f i).property
    obtain ⟨cover, hnonempty, hpaths, hnodup, hcovers, hlength⟩ :=
      exists_path_singleton_cover G O p hp hchain hpnodup hpinside
    have hcapacity : cover.length + 1 ≤ C.card := by
      rw [hplen, hOcard] at hlength
      omega
    have hcoverOutside : ∀ z, z ∈ cover.flatten ↔ z ∉ S := by
      intro z
      simpa only [O, Finset.mem_sdiff, Finset.mem_univ, true_and] using hcovers z
    exact no_contact_cover hd G S hScard hclique houtsider hfree
      cover hnonempty hpaths hnodup hcoverOutside hcapacity
  exact Nat.le_antisymm hcle hcge

/-- Exact original support/cardinality/adjacency classification from the
original suffix ledger; the previously supplied contact-cardinality premise
is now derived internally on the SAME G, d and S. -/
theorem original_contact_rigidity_of_suffix_ledger {d : ℕ} (hd : 1 ≤ d)
    (G : SimpleGraph (Fin (2 * d + 3))) (S : Finset (Fin (2 * d + 3)))
    (hScard : S.card = d + 3)
    (hclique : G.IsClique (S : Set (Fin (2 * d + 3))))
    (houtsider : ∀ x, x ∉ S → d ≤ G.degree x)
    (hfree : (cycleGraph (2 * d + 3)).Free G)
    (hledger : d * d ≤ (coreCrossEdges G S Finset.univ).card +
      (withinEdges G (Finset.univ \ S)).card) :
    originalContacts G S ⊆ S ∧
      (S \ originalContacts G S).card = 3 ∧
      (Finset.univ \ S).card = d ∧
      ∀ u v, G.Adj u v ↔ u ≠ v ∧
        ((u ∈ S ∧ v ∈ S) ∨
          (u ∉ S ∧ v ∈ originalContacts G S) ∨
          (v ∉ S ∧ u ∈ originalContacts G S)) := by
  exact original_contact_partition_and_adjacency hd G S hScard hclique
    (original_contacts_card_eq hd G S hScard hclique houtsider hfree hledger)
    houtsider hfree

end ErdosProblems.PathUpperReduction.EvenOriginalContactCount1105

namespace ErdosProblems.PathDenseCoreTwoLeaves

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.AntiRamseyCycleGenericHamiltonian

open ErdosProblems.PathCliqueTwoLeaves

theorem degree_after_one_owner_deletion {n m : ℕ}
    (G : SimpleGraph (Fin n)) (core : Fin m → Fin n)
    (hcore : Function.Injective core) (old : Sym2 (Fin n)) (i : Fin m) :
    (G.comap core).degree i ≤ ((G.deleteEdges {old}).comap core).degree i + 1 := by
  classical
  let C := G.comap core
  let D := (G.deleteEdges {old}).comap core
  let X := C.neighborFinset i
  let Y := D.neighborFinset i
  have hYX : Y ⊆ X := by
    intro x hx
    apply (C.mem_neighborFinset i x).mpr
    have hadj := (D.mem_neighborFinset i x).mp hx
    change (G.deleteEdges {old}).Adj (core i) (core x) at hadj
    exact (SimpleGraph.deleteEdges_adj.mp hadj).1
  have hlost : (X \ Y).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have howner (z : Fin m) (hz : z ∈ X \ Y) : s(core i, core z) = old := by
      have hparts := Finset.mem_sdiff.mp hz
      have hadj : G.Adj (core i) (core z) :=
        (C.mem_neighborFinset i z).mp hparts.1
      by_contra hne
      apply hparts.2
      apply (D.mem_neighborFinset i z).mpr
      exact SimpleGraph.deleteEdges_adj.mpr ⟨hadj, by simpa using hne⟩
    apply hcore
    exact (Sym2.mkEmbedding (core i)).injective
      ((howner x hx).trans (howner y hy).symm)
  have hcard := Finset.card_sdiff_add_card_eq_card hYX
  change (X \ Y).card + Y.card = X.card at hcard
  change X.card ≤ Y.card + 1
  omega

theorem connected_of_distinct_degree_sum {m : ℕ} (hm : 1 ≤ m)
    (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hpair : ∀ x y : Fin m, x ≠ y → m ≤ G.degree x + G.degree y) :
    G.Connected := by
  classical
  apply (SimpleGraph.connected_iff G).mpr
  refine ⟨?_, ⟨⟨0, by omega⟩⟩⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    exact ⟨Walk.nil⟩
  by_cases hadj : G.Adj x y
  · exact hadj.reachable
  let S : Finset (Fin m) := Finset.univ.erase x
  have hxS : G.neighborFinset x ⊆ S := by
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ z⟩
    intro heq
    subst z
    exact G.irrefl ((G.mem_neighborFinset x x).mp hz)
  have hyS : G.neighborFinset y ⊆ S := by
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ z⟩
    intro heq
    subst z
    exact hadj ((G.mem_neighborFinset y x).mp hz).symm
  have hScard : S.card = m - 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_erase_of_mem (Finset.mem_univ x)
  have hsum := hpair x y hxy
  have hcards : S.card < (G.neighborFinset x).card + (G.neighborFinset y).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz⟩ := Finset.inter_nonempty_of_card_lt_card_add_card hxS hyS hcards
  have hxz := (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hz).1
  have hyz := (G.mem_neighborFinset y z).mp (Finset.mem_inter.mp hz).2
  exact hxz.reachable.trans hyz.symm.reachable

/-- A supplied dense ACTUAL selected core and two jointly distinct selected
spokes at its first hub give a rainbow path for the SAME original coloring.
The actual chord-color owner is arbitrary and is deleted before Hamiltonicity. -/
theorem rainbow_path_of_dense_representative_core_and_two_spokes {n q m : ℕ}
    (hm : 4 ≤ m) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (core : Fin m → Fin n) (a b : Fin n)
    (hu : Function.Injective (Fin.cons a (Fin.cons b core)))
    (hdegree : ∀ i : Fin m, m + 2 ≤ 2 * ((selectedGraph χ r).comap core).degree i)
    (ha : (selectedGraph χ r).Adj a (core ⟨0, by omega⟩))
    (hb : (selectedGraph χ r).Adj b (core ⟨0, by omega⟩)) :
    ∃ f : (pathGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  classical
  let z : Fin m := ⟨0, by omega⟩
  have hz : z.val = 0 := rfl
  change (selectedGraph χ r).Adj a (core z) at ha
  change (selectedGraph χ r).Adj b (core z) at hb
  have haRange : a ∉ Set.range (Fin.cons b core) :=
    (Fin.cons_injective_iff.mp hu).1
  have htail : Function.Injective (Fin.cons b core) :=
    (Fin.cons_injective_iff.mp hu).2
  have hbRange : b ∉ Set.range core := (Fin.cons_injective_iff.mp htail).1
  have hcore : Function.Injective core := (Fin.cons_injective_iff.mp htail).2
  have hab : a ≠ b := by
    intro heq
    exact haRange ⟨0, by simpa using heq.symm⟩
  have hacore (i : Fin m) : a ≠ core i := by
    intro heq
    exact haRange ⟨i.succ, by simpa using heq.symm⟩
  have hbcore (i : Fin m) : b ≠ core i := by
    intro heq
    exact hbRange ⟨i, heq.symm⟩
  let e : HostEdge n :=
    ⟨s(a, b), (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin n))).mpr
      ((SimpleGraph.top_adj _ _).mpr hab)⟩
  let old : Sym2 (Fin n) := (r.edge (χ e)).val
  let L := selectedGraph χ r
  let D := (L.deleteEdges {old}).comap core
  have hDpair : ∀ i j : Fin m, i ≠ j → m ≤ D.degree i + D.degree j := by
    intro i j _hij
    have hi := hdegree i
    have hj := hdegree j
    have hdi := degree_after_one_owner_deletion L core hcore old i
    have hdj := degree_after_one_owner_deletion L core hcore old j
    change m + 2 ≤ 2 * (L.comap core).degree i at hi
    change m + 2 ≤ 2 * (L.comap core).degree j at hj
    change (L.comap core).degree i ≤ D.degree i + 1 at hdi
    change (L.comap core).degree j ≤ D.degree j + 1 at hdj
    omega
  have hDconn : D.Connected := connected_of_distinct_degree_sum (by omega) D hDpair
  let oldNeighbors (i : Fin m) : Fintype (D.neighborSet i) := inferInstance
  let : DecidableRel D.Adj := fun i j => Classical.propDecidable (D.Adj i j)
  let (i : Fin m) : Fintype (D.neighborSet i) :=
    Subtype.fintype (Membership.mem (D.neighborSet i))
  have hDpairCanonical : ∀ i j : Fin m, i ≠ j → m ≤ D.degree i + D.degree j := by
    intro i j hij
    have hbound := hDpair i j hij
    have hnormal (x : Fin m) :
        @SimpleGraph.degree _ D x (oldNeighbors x) = D.degree x :=
      congrArg (fun f : Fintype (D.neighborSet x) => @SimpleGraph.degree _ D x f)
        (Subsingleton.elim _ _)
    change m ≤ @SimpleGraph.degree _ D i (oldNeighbors i) +
      @SimpleGraph.degree _ D j (oldNeighbors j) at hbound
    rw [hnormal i, hnormal j] at hbound
    exact hbound
  obtain ⟨u, c, hc⟩ := exists_hamiltonian_cycle_of_degree_sum D hDconn
    (by simpa only [Fintype.card_fin] using (show 3 ≤ m by omega))
    (by simpa only [Fintype.card_fin] using hDpairCanonical)
  let c' := c.rotate z (hc.mem_support z)
  have hc' : c'.IsHamiltonianCycle := hc.rotate (hc.mem_support z)
  let w := c'.tail.reverse
  have hw : w.IsPath := hc'.isHamiltonian_tail.isPath.reverse
  have hlength : w.length + 1 = m := by
    have htailLength := hc'.isHamiltonian_tail.length_eq
    rw [Fintype.card_fin] at htailLength
    simp only [w, Walk.length_reverse, htailLength]
    omega
  let order : Fin m → Fin m := fun i => w.getVert i.val
  have horder : Function.Injective order := by
    intro i j hij
    apply Fin.ext
    have hi : i.val ≤ w.length := by have := i.isLt; omega
    have hj : j.val ≤ w.length := by have := j.isLt; omega
    exact hw.getVert_injOn hi hj hij
  have hzero : order z = z := by
    change w.getVert 0 = z
    exact w.getVert_zero
  have horderSteps (i j : Fin m) (hij : (pathGraph m).Adj i j) :
      D.Adj (order i) (order j) := by
    rcases pathGraph_adj.mp hij with hij | hji
    · have hadj := w.adj_getVert_succ (i := i.val) (by have := j.isLt; omega)
      rw [hij] at hadj
      exact hadj
    · have hadj := w.adj_getVert_succ (i := j.val) (by have := i.isLt; omega)
      rw [hji] at hadj
      exact hadj.symm
  let r' := r.replace e
  let L' := selectedGraph χ r'
  have hle : L.deleteEdges {old} ≤ L' := by
    simpa [L, L', r', old] using delete_selectedEdge_le_replace χ r e
  have hretain {x y : Fin n} (hadj : L.Adj x y) (hne : old ≠ s(x, y)) :
      L'.Adj x y := by
    apply hle
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hadj, by simpa using hne.symm⟩
  have hchord : L'.Adj a b := by
    simpa [L', r', e] using replacedEdge_mem χ r e
  let p : Fin m → Fin n := core ∘ order
  have hp : Function.Injective p := hcore.comp horder
  have hpz : p z = core z := by simp only [p, Function.comp_apply, hzero]
  have hsteps (i j : Fin m) (hij : (pathGraph m).Adj i j) :
      L'.Adj (p i) (p j) := hle (horderSteps i j hij)
  have haP (i : Fin m) : a ≠ p i := hacore (order i)
  have hbP (i : Fin m) : b ≠ p i := hbcore (order i)
  by_cases holdb : old = s(b, core z)
  · have holda : old ≠ s(a, core z) := by
      intro heq
      have hedge : s(b, core z) = s(a, core z) := holdb.symm.trans heq
      rcases Sym2.eq_iff.mp hedge with ⟨hba, _⟩ | ⟨_, hza⟩
      · exact hab hba.symm
      · exact hacore z hza.symm
    have hspoke : L'.Adj a (p z) := by
      rw [hpz]
      exact hretain ha holda
    let f : (pathGraph (m + 2)).Copy L' :=
      prefix_two_copy L' p b a
        (two_prefix_injective p hp b a hab.symm hbP haP)
        z hz hchord.symm hspoke hsteps
    refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
    simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f
  · have hspoke : L'.Adj b (p z) := by
      rw [hpz]
      exact hretain hb holdb
    let f : (pathGraph (m + 2)).Copy L' :=
      prefix_two_copy L' p a b
        (two_prefix_injective p hp a b hab haP hbP)
        z hz hchord hspoke hsteps
    refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
    simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f

end ErdosProblems.PathDenseCoreTwoLeaves

namespace ErdosProblems.PathS1ContainerCountBridge

open SimpleGraph
open ErdosProblems.PathUpperReduction
open ErdosProblems.PathDenseCoreTwoLeaves

/-- Literal complete core together with all leaf-to-first-hub spokes. -/
def s1Container {n m l : ℕ} (core : Fin m → Fin n) (leaf : Fin l → Fin n)
    (z : Fin m) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    ((Sym2.map core '' (⊤ : SimpleGraph (Fin m)).edgeSet) ∪
      Set.range (fun j : Fin l => s(core z, leaf j)))

theorem missing_core_degree_bound {m : ℕ} (hm : 1 ≤ m)
    (C : SimpleGraph (Fin m)) [DecidableRel C.Adj] (i : Fin m) :
    m - 1 ≤ C.degree i + (m.choose 2 - C.edgeFinset.card) := by
  classical
  have hcomp : Cᶜ.edgeFinset =
      (⊤ : SimpleGraph (Fin m)).edgeFinset \ C.edgeFinset := by
    ext e
    refine Sym2.inductionOn e ?_
    intro x y
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Finset.mem_sdiff, SimpleGraph.compl_adj, SimpleGraph.top_adj]
  have hcompcard : Cᶜ.edgeFinset.card = m.choose 2 - C.edgeFinset.card := by
    rw [hcomp, Finset.card_sdiff_of_subset (SimpleGraph.edgeFinset_mono le_top)]
    simp only [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  have hdegree := Cᶜ.degree_le_card_edgeFinset (v := i)
  have hdegree_lt := C.degree_lt_card_verts i
  rw [C.degree_compl, Fintype.card_fin, hcompcard] at hdegree
  omega

theorem selected_core_and_spoke_count {n q m l : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (core : Fin m → Fin n) (leaf : Fin l → Fin n) (z : Fin m)
    (hinj : Function.Injective (Sum.elim core leaf))
    (hsub : selectedGraph χ r ≤ s1Container core leaf z) :
    q = Nat.card ((selectedGraph χ r).comap core).edgeSet +
      Nat.card {j : Fin l // (selectedGraph χ r).Adj (core z) (leaf j)} := by
  classical
  let R := selectedGraph χ r
  let C := R.comap core
  let T := Finset.univ.filter (fun j : Fin l => R.Adj (core z) (leaf j))
  have hcore : Function.Injective core := by
    intro i j hij
    exact Sum.inl.inj (hinj hij)
  have hleaf : Function.Injective leaf := by
    intro i j hij
    exact Sum.inr.inj (hinj hij)
  have hcross (i : Fin m) (j : Fin l) : core i ≠ leaf j := by
    intro hij
    have hsum : (Sum.inl i : Fin m ⊕ Fin l) = Sum.inr j :=
      hinj (show Sum.elim core leaf (Sum.inl i) = Sum.elim core leaf (Sum.inr j) from hij)
    cases hsum
  let emb : Fin m ↪ Fin n := ⟨core, hcore⟩
  let A := C.edgeFinset.map emb.sym2Map
  let B := T.image (fun j : Fin l => s(core z, leaf j))
  have hA : A = (C.map emb).edgeFinset := by
    change C.edgeFinset.map emb.sym2Map = (C.map emb).edgeFinset
    rw [← Finset.coe_inj]
    push_cast
    exact (C.edgeSet_map emb).symm
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨j, _hj, hje⟩ := Finset.mem_image.mp heB
    obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp heA
    revert hd hde
    refine Sym2.inductionOn d ?_
    intro x y _hd hde
    have heq : s(core x, core y) = s(core z, leaf j) := by
      change s(core x, core y) = e at hde
      exact hde.trans hje.symm
    rcases Sym2.eq_iff.mp heq with ⟨_, hy⟩ | ⟨hx, _⟩
    · exact hcross y j hy
    · exact hcross x j hx
  have hE : R.edgeFinset = A ∪ B := by
    ext e
    refine Sym2.inductionOn e ?_
    intro x y
    constructor
    · intro he
      have hxy : R.Adj x y := (SimpleGraph.mem_edgeFinset.mp he)
      have hc := ((SimpleGraph.fromEdgeSet_adj _).mp (hsub hxy)).1
      rcases hc with hc | hc
      · obtain ⟨d, _hd, hde⟩ := hc
        have hdR : Sym2.map core d ∈ R.edgeSet := by rw [hde]; exact hxy
        have hdC : d ∈ C.edgeFinset := by
          have hpre : ∀ t : Sym2 (Fin m), Sym2.map core t ∈ R.edgeSet → t ∈ C.edgeFinset := by
            intro t
            refine Sym2.inductionOn t ?_
            intro i j hij
            exact SimpleGraph.mem_edgeFinset.mpr hij
          exact hpre d hdR
        apply Finset.mem_union_left
        exact Finset.mem_map.mpr ⟨d, hdC, hde⟩
      · obtain ⟨j, hje⟩ := hc
        change s(core z, leaf j) = s(x, y) at hje
        have hspoke : R.Adj (core z) (leaf j) := by
          change s(core z, leaf j) ∈ R.edgeSet
          rw [hje]
          exact hxy
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hspoke⟩, hje⟩
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · rw [hA] at he
        exact SimpleGraph.mem_edgeFinset.mpr
          ((SimpleGraph.edgeSet_mono (SimpleGraph.map_comap_le emb R))
            (SimpleGraph.mem_edgeFinset.mp he))
      · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp he
        rw [← hje]
        exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hj).2
  have hBcard : B.card = T.card := by
    apply Finset.card_image_iff.mpr
    intro i _hi j _hj hij
    apply hleaf
    exact (Sym2.mkEmbedding (core z)).injective hij
  have hcount := congrArg Finset.card hE
  rw [Finset.card_union_of_disjoint hAB, Finset.card_map, hBcard] at hcount
  have hCnat : Nat.card C.edgeSet = C.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact C.edgeFinset_card.symm
  have hTnat : Nat.card {j : Fin l // R.Adj (core z) (leaf j)} = T.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype T (by intro j; simp only [T, Finset.mem_filter,
      Finset.mem_univ, true_and])
  change q = Nat.card C.edgeSet + Nat.card {j : Fin l // R.Adj (core z) (leaf j)}
  rw [hCnat, hTnat]
  simpa only [R, C, T, selectedGraph_card_edgeFinset] using hcount

/-- The full ACTUAL S1 container count yields two selected spokes and the
actual reindexed selected-core degree needed by the dense-core caller. -/
theorem dense_core_and_two_spokes_of_s1_container {n q m l : ℕ}
    (hm : 4 ≤ m) (hl : 2 ≤ l) (hwindow : 2 * l ≤ m) (_hn : n = m + l)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (core : Fin m → Fin n) (leaf : Fin l → Fin n)
    (hinj : Function.Injective (Sum.elim core leaf))
    (_hcover : Function.Surjective (Sum.elim core leaf))
    (hsub : selectedGraph χ r ≤ s1Container core leaf ⟨0, by omega⟩)
    (hq : m.choose 2 + 2 ≤ q) :
    (∀ i : Fin m, m + 2 ≤ 2 * ((selectedGraph χ r).comap core).degree i) ∧
      ∃ a b : Fin l, a ≠ b ∧
        (selectedGraph χ r).Adj (core ⟨0, by omega⟩) (leaf a) ∧
        (selectedGraph χ r).Adj (core ⟨0, by omega⟩) (leaf b) := by
  classical
  let C := (selectedGraph χ r).comap core
  let T := Finset.univ.filter
    (fun j : Fin l => (selectedGraph χ r).Adj (core ⟨0, by omega⟩) (leaf j))
  have hcount := selected_core_and_spoke_count χ r core leaf ⟨0, by omega⟩ hinj hsub
  have hCnat : Nat.card C.edgeSet = C.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact C.edgeFinset_card.symm
  have hTnat : Nat.card {j : Fin l // (selectedGraph χ r).Adj
      (core ⟨0, by omega⟩) (leaf j)} = T.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype T (by intro j; simp only [T, Finset.mem_filter,
      Finset.mem_univ, true_and])
  change q = Nat.card C.edgeSet + Nat.card {j : Fin l // (selectedGraph χ r).Adj
    (core ⟨0, by omega⟩) (leaf j)} at hcount
  rw [hCnat, hTnat] at hcount
  have hT : T.card ≤ l := by
    have hh := Finset.card_le_card (Finset.filter_subset
      (fun j : Fin l => (selectedGraph χ r).Adj (core ⟨0, by omega⟩) (leaf j)) Finset.univ)
    simpa only [Finset.card_univ, Fintype.card_fin] using hh
  have hC : C.edgeFinset.card ≤ m.choose 2 := by
    simpa only [Fintype.card_fin] using C.card_edgeFinset_le_card_choose_two
  have hdeficit : (m.choose 2 - C.edgeFinset.card) + (l - T.card) ≤ l - 2 := by omega
  have hmissing : m.choose 2 - C.edgeFinset.card ≤ l - 2 := by omega
  have hspokes : 1 < T.card := by omega
  constructor
  · intro i
    have hd := missing_core_degree_bound (by omega) C i
    change m + 2 ≤ 2 * C.degree i
    omega
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hspokes
    exact ⟨a, b, hab, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩

/-- SAME original-color S1-container exclusion under the exact count/window
hypotheses. No favorable owner, supplied rainbow path or degree premise. -/
theorem rainbow_path_of_representative_s1_container {n q m l : ℕ}
    (hm : 4 ≤ m) (hl : 2 ≤ l) (hwindow : 2 * l ≤ m) (hn : n = m + l)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (core : Fin m → Fin n) (leaf : Fin l → Fin n)
    (hinj : Function.Injective (Sum.elim core leaf))
    (hcover : Function.Surjective (Sum.elim core leaf))
    (hsub : selectedGraph χ r ≤ s1Container core leaf ⟨0, by omega⟩)
    (hq : m.choose 2 + 2 ≤ q) :
    ∃ f : (pathGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  classical
  obtain ⟨hdegree, a, b, hab, ha, hb⟩ :=
    dense_core_and_two_spokes_of_s1_container hm hl hwindow hn χ r core leaf hinj hcover hsub hq
  have hcore : Function.Injective core := by
    intro i j hij
    exact Sum.inl.inj (hinj hij)
  have hleaf : Function.Injective leaf := by
    intro i j hij
    exact Sum.inr.inj (hinj hij)
  have hcross (i : Fin m) (j : Fin l) : leaf j ≠ core i := by
    intro hij
    have hsum : (Sum.inr j : Fin m ⊕ Fin l) = Sum.inl i :=
      hinj (show Sum.elim core leaf (Sum.inr j) = Sum.elim core leaf (Sum.inl i) from hij)
    cases hsum
  have hu : Function.Injective (Fin.cons (leaf a) (Fin.cons (leaf b) core)) := by
    apply Fin.cons_injective_iff.mpr
    constructor
    · have hneq (i : Fin (m + 1)) :
          (Fin.cons (leaf b) core : Fin (m + 1) → Fin n) i ≠ leaf a := by
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (hleaf.ne hab).symm
        · exact (hcross j a).symm
      rintro ⟨i, hi⟩
      exact hneq i hi
    · apply Fin.cons_injective_iff.mpr
      refine ⟨?_, hcore⟩
      rintro ⟨i, hi⟩
      exact hcross i b hi.symm
  exact rainbow_path_of_dense_representative_core_and_two_spokes hm χ r core
    (leaf a) (leaf b) hu hdegree ha.symm hb.symm

end ErdosProblems.PathS1ContainerCountBridge

section

open SimpleGraph
open ErdosProblems.PathUpperReduction.CountCoreBasis
open ErdosProblems.PathS1ContainerCountBridge

namespace ErdosProblems.PathUpperReduction.OddConnectedOriginalUpper1105

/-- Full original connected-step conclusion for every odd k=2*ell+1, ell>=4.
No supplied core, container, window, selected clique, favorable owner or IH. -/
theorem original_connected_odd_palette_upper {ell n q : ℕ}
    (hell : 4 ≤ ell) (hn : 2 * ell + 1 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (R : RepresentativeChoice χ)
    (hconn : (selectedGraph χ R).Connected)
    (hno : ∀ P : (pathGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ) :
    q ≤ max ((2 * ell - 1).choose 2 + 1)
      ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1) := by
  classical
  by_contra hbound
  have hq : max ((2 * ell - 1).choose 2 + 1)
      ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1) < q :=
    Nat.lt_of_not_ge hbound
  let M := selectedGraph χ R
  obtain ⟨H, _hConeSub, hfree, hdelete, _hsat, _hdensity, hclique, hcard,
      _hapex, _hapexmem, hConeEq, hSelectedSub⟩ :=
    ConnectedOddCore1105.exists_connected_odd_saturated_large_core
      hell hn χ R hconn hno hq
  let J := H.comap (some : Fin n → Option (Fin n))
  let S := degreeCore H ell
  have hSameCone : H = ConeCoreApplication1105.cone J := hConeEq
  have hK : 5 ≤ 2 * ell + 2 := by omega
  have hScard : S.card = (2 * ell + 2) - 2 := by
    dsimp only [S]
    rw [hcard]
    omega
  have hSclique : (ConeCoreApplication1105.cone J).IsClique
      (S : Set (Option (Fin n))) := by
    rw [← hSameCone]
    exact hclique
  have hJfree : ∀ r, 2 * ell + 2 ≤ r →
      (cycleGraph r).Free (ConeCoreApplication1105.cone J) := by
    intro r hr
    rw [← hSameCone]
    exact hfree r hr
  have hJdelete : ∀ z : Option (Fin n),
      ((ConeCoreApplication1105.cone J).induce {w | w ≠ z}).Connected := by
    intro z
    rw [← hSameCone]
    exact hdelete z
  have hcompl : 1 < Sᶜ.card := by
    rw [Finset.card_compl, hScard]
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  have houtside : ∃ u v : Option (Fin n), u ∉ S ∧ v ∉ S ∧ u ≠ v := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcompl
    exact ⟨u, v, Finset.mem_compl.mp hu, Finset.mem_compl.mp hv, huv⟩
  have hContainer := ConeFiniteContainer1105.cone_finite_container
    J S hK hScard hSclique hJfree hJdelete houtside
  dsimp only at hContainer
  let m : ℕ := (2 * ell + 2) - 3
  let l : ℕ := n - m
  obtain ⟨_hm2, hl, hsum, _hTcard, _b, e, _hb, _hezero, _heleft,
    _heright, headj⟩ := hContainer
  have hm : 4 ≤ m := by dsimp only [m]; omega
  have hnSum : n = m + l := hsum.symm
  let core : Fin m → Fin n := fun i => e (Sum.inl i)
  let leaf : Fin l → Fin n := fun j => e (Sum.inr j)
  let z : Fin m := ⟨0, by omega⟩
  have hEnum : Sum.elim core leaf = e := by
    funext x
    cases x <;> rfl
  have hinj : Function.Injective (Sum.elim core leaf) := by
    rw [hEnum]
    exact e.injective
  have hcover : Function.Surjective (Sum.elim core leaf) := by
    rw [hEnum]
    exact e.surjective
  have hsubMJ : M ≤ J := hSelectedSub
  have hsub : M ≤ s1Container core leaf z := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    have hc := (headj a b).mp (hsubMJ hxy)
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            change i ≠ j at hc
            change (s1Container core leaf z).Adj (core i) (core j)
            apply (SimpleGraph.fromEdgeSet_adj _).mpr
            refine ⟨Or.inl ⟨s(i, j), ?_, ?_⟩, hxy.ne⟩
            · exact (SimpleGraph.mem_edgeSet (G := (⊤ : SimpleGraph (Fin m)))).mpr hc
            · simp only [Sym2.map_mk]
        | inr j =>
            change i.val = 0 at hc
            have hi : i = z := by apply Fin.ext; exact hc
            subst i
            change (s1Container core leaf z).Adj (core z) (leaf j)
            exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨Or.inr ⟨j, rfl⟩, hxy.ne⟩
    | inr i =>
        cases b with
        | inl j =>
            change j.val = 0 at hc
            have hj : j = z := by apply Fin.ext; exact hc
            subst j
            change (s1Container core leaf z).Adj (leaf i) (core z)
            exact (SimpleGraph.fromEdgeSet_adj _).mpr
              ⟨Or.inr ⟨i, Sym2.eq_swap⟩, hxy.ne⟩
        | inr j => exact hc.elim
  -- Actual selected-edge capacity; the private equality ledger is unnecessary.
  let A := (⊤ : SimpleGraph (Fin m)).edgeFinset.image (Sym2.map core)
  let B := (Finset.univ : Finset (Fin l)).image (fun j => s(core z, leaf j))
  have hEdgeSubset : M.edgeFinset ⊆ A ∪ B := by
    intro d
    refine Sym2.inductionOn d ?_
    intro x y hd
    have hxy : M.Adj x y := SimpleGraph.mem_edgeFinset.mp hd
    have hs := ((SimpleGraph.fromEdgeSet_adj _).mp (hsub hxy)).1
    rcases hs with ⟨t, ht, hte⟩ | ⟨j, hje⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨t, SimpleGraph.mem_edgeFinset.mpr ht, hte⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, hje⟩)
  have hCount : Nat.card M.edgeSet = q := by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      selectedGraph_card_edgeFinset χ R
  have hCapacity : q ≤ m.choose 2 + l := by
    calc
      q = Nat.card M.edgeSet := hCount.symm
      _ = M.edgeFinset.card := by
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
      _ ≤ (A ∪ B).card := Finset.card_le_card hEdgeSubset
      _ ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ (⊤ : SimpleGraph (Fin m)).edgeFinset.card +
          (Finset.univ : Finset (Fin l)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = m.choose 2 + l := by
        simp only [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
          Fintype.card_fin, Finset.card_univ]
  have hkm : (2 * ell + 1) - 2 = m := by dsimp only [m]; omega
  have hL : n - (2 * ell + 1) + 2 = l := by dsimp only [l, m]; omega
  have hhalf : ((2 * ell + 1) - 1) / 2 = ell := by omega
  have hodd : Odd (2 * ell + 1) := Nat.odd_iff.mpr (by omega)
  have hqLiteral : max (((2 * ell + 1) - 2).choose 2 + 1)
      ((((2 * ell + 1) - 1) / 2 - 1).choose 2 +
        (((2 * ell + 1) - 1) / 2 - 1) *
          (n - ((2 * ell + 1) - 1) / 2 + 1) +
        (if Odd (2 * ell + 1) then 1 else 2)) < q := by
    have hkpred : (2 * ell + 1) - 2 = 2 * ell - 1 := by omega
    simpa only [hkpred, hhalf, ite_eq_left hodd] using hq
  have hCapacityLiteral : q ≤ ((2 * ell + 1) - 2).choose 2 +
      (n - (2 * ell + 1) + 2) := by
    simpa only [hkm, hL] using hCapacity
  obtain ⟨hmargin, hcases⟩ :=
    WindowNumerics1105.original_palette_implies_window_or_full_four
      (2 * ell + 1) n q (by omega) hn hqLiteral hCapacityLiteral
  have hmargin' : m.choose 2 + 2 ≤ q := by
    simpa only [hkm] using hmargin
  have hwindow : 2 * l ≤ m := by
    rcases hcases with hwindow | ⟨hsix, _hfull⟩
    · simpa only [hkm, hL] using hwindow
    · omega
  have hRainbow := rainbow_path_of_representative_s1_container
    hm hl hwindow hnSum χ R core leaf hinj hcover hsub hmargin'
  have hPathOrder : m + 2 = 2 * ell + 1 := by dsimp only [m]; omega
  rw [hPathOrder] at hRainbow
  obtain ⟨P, hP⟩ := hRainbow
  exact hno P hP

end ErdosProblems.PathUpperReduction.OddConnectedOriginalUpper1105

end

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- Every positive finite ordinary P(d+1)-free graph has
the precise multiplied per-component edge-plus-one charge. The elementary
charge arithmetic is reused, rather than reproved here. -/
theorem ordinary_component_charge
    {V : Type*} [Finite V] (G : SimpleGraph V) (d : ℕ)
    (hd : 2 ≤ d) (hv : 1 ≤ Nat.card V)
    (hfree : (pathGraph (d + 1)).Free G) :
    2 * d * (Nat.card G.edgeSet + 1) ≤
      ((d - 1) * d + 2) * Nat.card V := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have hclique : Nat.card G.edgeSet ≤ (Nat.card V).choose 2 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, G.card_edgeSet]
    exact G.card_edgeFinset_le_card_choose_two
  have hEG := ErdosProblems.PathErdosGallai.erdos_gallai_edge_bound G d hd hfree
  have hcharge := ErdosProblems.PathCliqueEGDensity.clique_eg_density
    d (Nat.card V) (Nat.card G.edgeSet) hd hv hclique hEG
  calc
    2 * d * (Nat.card G.edgeSet + 1) ≤
        (d * (d - 1) + 2) * Nat.card V := hcharge
    _ = ((d - 1) * d + 2) * Nat.card V := by
      rw [Nat.mul_comm d (d - 1)]

/-- The same actual graph charge in the exact real
coefficient used by the arbitrary-tail affine envelope and component sum. This only divides the reused multiplied charge by positive2d. -/
theorem ordinary_component_charge_real
    {V : Type*} [Finite V] (G : SimpleGraph V) (d : ℕ)
    (hd : 2 ≤ d) (hv : 1 ≤ Nat.card V)
    (hfree : (pathGraph (d + 1)).Free G) :
    (Nat.card G.edgeSet : ℝ) + 1 ≤
      (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (Nat.card V : ℝ) := by
  have hcharge := ordinary_component_charge G d hd hv hfree
  have hdsub : (d - 1) + 1 = d := by omega
  have hdsubR : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    exact_mod_cast hdsub
  have hsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  have hcast : 2 * (d : ℝ) * ((Nat.card G.edgeSet : ℝ) + 1) ≤
      (((d - 1 : ℕ) : ℝ) * (d : ℝ) + 2) * (Nat.card V : ℝ) := by
    exact_mod_cast hcharge
  rw [hsub] at hcast
  apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * (d : ℝ))).mp
  calc
    2 * (d : ℝ) * ((Nat.card G.edgeSet : ℝ) + 1) ≤
        (((d : ℝ) - 1) * (d : ℝ) + 2) * (Nat.card V : ℝ) := hcast
    _ = 2 * (d : ℝ) *
        ((((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (Nat.card V : ℝ)) := by
      field_simp [ne_of_gt hdpos]

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q : ℕ}

/-- Ordinary P(d+1) freedom at every ACTUAL retained stage, with all literal
U/W/A/B and unchanged R preserved by the structural recursion. -/
def OriginalResidualCutFamily.AllRetainedPathFree
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (d : ℕ) : Prop :=
  match F with
  | .nil _ _ => True
  | .cons stage tail =>
      (pathGraph (d + 1)).Free stage.retainedGraph ∧ tail.AllRetainedPathFree d

/-- Each actual local piece retains its actual stage's all-short exclusion. -/
theorem OriginalResidualCutFamily.local_piece_path_free
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (d : ℕ)
    (hshort : F.AllRetainedPathFree d) (i : F.PieceIndex) :
    (pathGraph (d + 1)).Free (originalCutFamilyLocalPieceData F i).stage.retainedGraph := by
  revert hshort i
  induction F with
  | nil =>
      intro _ i
      exact PEmpty.elim i
  | cons stage tail ih =>
      intro hshort i
      change stage.retainedGraph.ConnectedComponent ⊕ OriginalCutFamilyPieceIndex tail at i
      change (pathGraph (d + 1)).Free stage.retainedGraph ∧
        tail.AllRetainedPathFree d at hshort
      cases i with
      | inl C => exact hshort.1
      | inr i => exact ih hshort.2 i

/-- Derive C0 >= 2,
then T >= 2 and b+2 <= T from the actual T=C0+b ledger, including zero cuts. -/
theorem OriginalResidualCutFamily.proper_first_cut_budget
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ) :
    2 ≤ Nat.card (selectedGraph χ R).ConnectedComponent ∧
      2 ≤ Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent ∧
      F.cutCount + 2 ≤
        Nat.card (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent := by
  have hsequence := F.toGreedySequence
  have hxs : xs ≠ [] := by
    intro hempty
    subst xs
    have hnil : Set.univ \ componentSupport χ R x = ∅ := hsequence.2.2.2.1
    apply hproper
    ext v
    constructor
    · intro _
      exact Set.mem_univ v
    · intro _
      by_contra hv
      have houtside : v ∈ Set.univ \ componentSupport χ R x := ⟨Set.mem_univ v, hv⟩
      rw [hnil] at houtside
      exact houtside
  have hlength : 2 ≤ (x :: xs).length := by
    cases xs with
    | nil => exact (hxs rfl).elim
    | cons y ys => simp
  have hroots := residualGreedySequence_root_count χ R (x :: xs) hsequence
  have hcount := originalCutFamily_global_component_count F
  have hC0 : 2 ≤ Nat.card (selectedGraph χ R).ConnectedComponent := by omega
  exact ⟨hC0, by omega, by omega⟩

/-- Each ACTUAL global retained component inherits freedom by an injective
inclusion into its corresponding ACTUAL stage. Supports and graph restriction
are derived from the checked same-R coupling, rather than supplied. -/
theorem OriginalResidualCutFamily.global_component_path_free
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ roots) (d : ℕ)
    (hshort : F.AllRetainedPathFree d)
    (C : (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent) :
    (pathGraph (d + 1)).Free C.toSimpleGraph := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  let i : F.PieceIndex := originalCutFamilyGlobalComponentCoupling F C
  let L := originalCutFamilyLocalPieceData F i
  have hsupp : C.supp = F.pieceSupport i := by
    have h := originalCutFamilyGlobalComponentCoupling_supp F i
    have hinv : (originalCutFamilyGlobalComponentCoupling F).symm i = C :=
      (originalCutFamilyGlobalComponentCoupling F).symm_apply_apply C
    rw [hinv] at h
    exact h
  have hinside : C.supp ⊆ L.stage.rootSupport := by
    intro v hv
    have hpiece : v ∈ F.pieceSupport i := hsupp ▸ hv
    rw [← originalCutFamily_local_piece_support F i] at hpiece
    obtain ⟨u, _hu, rfl⟩ := hpiece
    exact u.property
  let f : C.toSimpleGraph.Copy L.stage.retainedGraph := {
    toHom := {
      toFun := fun v => ⟨v.val, hinside v.property⟩
      map_rel' := by
        intro a b hab
        have hAdj : (H.induce L.stage.rootSupport).Adj
            ⟨a.val, hinside a.property⟩ ⟨b.val, hinside b.property⟩ := hab
        have hgraph : H.induce L.stage.rootSupport = L.stage.retainedGraph :=
          originalCutFamily_global_piece_stage_induce F i
        rw [hgraph] at hAdj
        exact hAdj
    }
    injective' := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun v : L.stage.rootSupport => (v : Fin n)) hab
  }
  rintro ⟨P⟩
  exact F.local_piece_path_free d hshort i ⟨f.comp P⟩

/-- Sum charges of the actual positive global components. The original q,
all isolated vertices, literal cuts, and actual T=C0+b budget are preserved. -/
theorem OriginalResidualCutFamily.original_all_short_charge
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (d : ℕ) (hd : 2 ≤ d) (hshort : F.AllRetainedPathFree d) :
    (q : ℝ) + 2 ≤ (((d : ℝ) - 1) / 2 + 1 / (d : ℝ)) * (n : ℝ) := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  let c : ℝ := ((d : ℝ) - 1) / 2 + 1 / (d : ℝ)
  have hpositive (C : H.ConnectedComponent) : 1 ≤ Nat.card C.supp := by
    obtain ⟨v, hv⟩ := C.nonempty_supp
    let _ : Nonempty C.supp := ⟨⟨v, hv⟩⟩
    have hpos : 0 < Nat.card C.supp := Nat.card_pos
    omega
  have hcharge (C : H.ConnectedComponent) :
      (Nat.card C.toSimpleGraph.edgeSet : ℝ) + 1 ≤ c * (Nat.card C.supp : ℝ) :=
    ordinary_component_charge_real C.toSimpleGraph d hd (hpositive C)
      (F.global_component_path_free d hshort C)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset H.ConnectedComponent))
    (fun C _ => hcharge C)
  have hsum' : ((∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet : ℕ) : ℝ) +
      (Nat.card H.ConnectedComponent : ℝ) ≤
      c * ((∑ C : H.ConnectedComponent, Nat.card C.supp : ℕ) : ℝ) := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.cast_sum, Nat.card_eq_fintype_card,
      Finset.mul_sum] using hsum
  have hvertices := originalCutFamily_global_component_vertex_sum F
  change (∑ C : H.ConnectedComponent, Nat.card C.supp) = n at hvertices
  rw [hvertices] at hsum'
  have hq := originalCutFamily_global_component_edge_sum F
  change q = (∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) +
    F.cutCount at hq
  have hqR : (q : ℝ) =
      ((∑ C : H.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet : ℕ) : ℝ) +
      (F.cutCount : ℝ) := by exact_mod_cast hq
  have hbudget := (F.proper_first_cut_budget hproper).2.2
  have hbudgetR : (F.cutCount : ℝ) + 2 ≤ (Nat.card H.ConnectedComponent : ℝ) := by
    exact_mod_cast hbudget
  change (q : ℝ) + 2 ≤ c * (n : ℝ)
  linarith

/-- Exact literal-formula bound on the ORIGINAL q in the actual all-short
disconnected case. No desired numeric bound or smaller-host IH is a premise. -/
theorem OriginalResidualCutFamily.original_color_count_le_formula_of_all_short
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)} {k : ℕ}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (hk : 6 ≤ k) (hkn : k ≤ n)
    (hshort : F.AllRetainedPathFree ((k - 2) / 2)) :
    q ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  have hd : 2 ≤ (k - 2) / 2 := by omega
  exact all_short_color_count_le_pathFormula k n q hk hkn
    (F.original_all_short_charge hproper ((k - 2) / 2) hd hshort)

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q k : ℕ}

/-- A positive-order ordinary path copy lies in an actual graph component,
with exactly its original vertex images. No longest-path assumption is used. -/
theorem middle_path_copy_in_actual_component
    {V : Type*} (G : SimpleGraph V) {m : ℕ} (hm : 0 < m)
    (P : (pathGraph m).Copy G) :
    ∃ C : G.ConnectedComponent, Nonempty ((pathGraph m).Copy C.toSimpleGraph) := by
  let j0 : Fin m := ⟨0, hm⟩
  let C : G.ConnectedComponent := G.connectedComponentMk (P j0)
  have hmem (j : Fin m) : P j ∈ C.supp := by
    apply (C.mem_supp_iff (P j)).mpr
    exact ConnectedComponent.sound
      ((pathGraph_preconnected m j j0).map P.toHom)
  let Q : (pathGraph m).Copy C.toSimpleGraph := {
    toHom := {
      toFun := fun j => ⟨P j, hmem j⟩
      map_rel' := by
        intro i j hij
        exact P.toHom.map_rel' hij
    }
    injective' := by
      intro i j hij
      exact P.injective (congrArg (fun v : C.supp => (v : V)) hij)
  }
  exact ⟨C, ⟨Q⟩⟩

/-- The checked recursive P(k-2) exclusion is exactly the all-stage freedom
predicate at d=k-3, with subtraction justified in the original order range. -/
theorem OriginalResidualCutFamily.all_retained_path_free_of_no_long
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots)
    (hk : 3 ≤ k) (hlong : F.NoLongRetainedPath k) :
    F.AllRetainedPathFree (k - 3) := by
  have horder : (k - 3) + 1 = k - 2 := by omega
  revert hlong
  induction F with
  | nil =>
      intro _
      trivial
  | cons stage tail ih =>
      intro hlong
      change (∀ _P : (pathGraph (k - 2)).Copy stage.retainedGraph, False) ∧
        tail.NoLongRetainedPath k at hlong
      change (pathGraph ((k - 3) + 1)).Free stage.retainedGraph ∧
        tail.AllRetainedPathFree (k - 3)
      constructor
      · rintro ⟨P⟩
        rw [horder] at P
        exact hlong.1 P
      · exact ih hlong.2

/-- Failure of the recursive all-short predicate gives a copy in an actual
stored stage, identified by an actual piece index. All U/W updates stay literal. -/
theorem OriginalResidualCutFamily.exists_piece_stage_copy_of_not_all_free
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (d : ℕ)
    (hfail : ¬ F.AllRetainedPathFree d) :
    ∃ i : F.PieceIndex,
      Nonempty ((pathGraph (d + 1)).Copy
        (originalCutFamilyLocalPieceData F i).stage.retainedGraph) := by
  classical
  revert hfail
  induction F with
  | nil =>
      intro hfail
      exact (hfail trivial).elim
  | cons stage tail ih =>
      intro hfail
      change ¬ ((pathGraph (d + 1)).Free stage.retainedGraph ∧
        tail.AllRetainedPathFree d) at hfail
      by_cases hhead : (pathGraph (d + 1)).Free stage.retainedGraph
      · have htail : ¬ tail.AllRetainedPathFree d := fun ht => hfail ⟨hhead, ht⟩
        obtain ⟨i, ⟨P⟩⟩ := ih htail
        exact ⟨Sum.inr i, ⟨P⟩⟩
      · obtain ⟨P⟩ := SimpleGraph.not_free.mp hhead
        let j0 : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
        exact ⟨Sum.inl (stage.retainedGraph.connectedComponentMk (P j0)), ⟨P⟩⟩

/-- Every failing actual stage path survives in the literal global graph and
then lies in one of its actual components. This one-way seed implication also
holds for residual families; it asserts no converse for their global graphs. -/
theorem OriginalResidualCutFamily.exists_global_component_copy_of_not_all_free
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {U : Set (Fin q)} {W : Set (Fin n)} {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R U W roots) (d : ℕ)
    (hfail : ¬ F.AllRetainedPathFree d) :
    ∃ C : (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent,
      Nonempty ((pathGraph (d + 1)).Copy C.toSimpleGraph) := by
  obtain ⟨i, ⟨P⟩⟩ := F.exists_piece_stage_copy_of_not_all_free d hfail
  let L := originalCutFamilyLocalPieceData F i
  let H := originalCutFamilyGlobalRetainedGraph F
  have hgraph : H.induce L.stage.rootSupport = L.stage.retainedGraph :=
    originalCutFamily_global_piece_stage_induce F i
  let inc : L.stage.retainedGraph.Copy H := {
    toHom := {
      toFun := fun v => v.val
      map_rel' := by
        intro u v huv
        have hind : (H.induce L.stage.rootSupport).Adj u v := by
          rw [hgraph]
          exact huv
        exact hind
    }
    injective' := Subtype.val_injective
  }
  exact middle_path_copy_in_actual_component H (Nat.succ_pos d) (inc.comp P)

/-- Actual full-family case extraction: either every stage is all-short, or
an actual global component supplies precisely the middle interval, a real Pa
copy and next-order freedom. The maximum is constructed, never supplied. -/
theorem OriginalResidualCutFamily.all_short_or_middle_component_of_no_long
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {roots : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ roots)
    (hk : 8 ≤ k) (hlong : F.NoLongRetainedPath k) :
    F.AllRetainedPathFree ((k - 2) / 2) ∨
      ∃ (C : (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent) (a : ℕ),
        (k - 2) / 2 + 1 ≤ a ∧ a ≤ k - 3 ∧
        Nonempty ((pathGraph a).Copy C.toSimpleGraph) ∧
        (pathGraph (a + 1)).Free C.toSimpleGraph := by
  classical
  by_cases hshort : F.AllRetainedPathFree ((k - 2) / 2)
  · exact Or.inl hshort
  · obtain ⟨C, hseed⟩ :=
      F.exists_global_component_copy_of_not_all_free ((k - 2) / 2) hshort
    let P : ℕ → Prop := fun t => Nonempty ((pathGraph t).Copy C.toSimpleGraph)
    let a : ℕ := Nat.findGreatest P (k - 3)
    have hseed' : P ((k - 2) / 2 + 1) := hseed
    have hseed_bound : (k - 2) / 2 + 1 ≤ k - 3 := by omega
    have hlower : (k - 2) / 2 + 1 ≤ a := Nat.le_findGreatest hseed_bound hseed'
    have hupper : a ≤ k - 3 := Nat.findGreatest_le (P := P) (k - 3)
    have hcopy : P a := Nat.findGreatest_spec hseed_bound hseed'
    have hboundary : (pathGraph ((k - 3) + 1)).Free C.toSimpleGraph :=
      F.global_component_path_free (k - 3)
        (F.all_retained_path_free_of_no_long (by omega) hlong) C
    have hfree : (pathGraph (a + 1)).Free C.toSimpleGraph := by
      intro hnext
      by_cases hlt : a < k - 3
      · exact Nat.findGreatest_is_greatest (P := P)
          (show Nat.findGreatest P (k - 3) < a + 1 from by change a < a + 1; omega)
          (by omega) hnext
      · have heq : a + 1 = (k - 3) + 1 := by omega
        rw [heq] at hnext
        exact hboundary hnext
    exact Or.inr ⟨C, a, hlower, hupper, hcopy, hfree⟩

end ErdosProblems.PathUpperReduction

noncomputable section

namespace ErdosProblems.PathUpperReduction

open SimpleGraph
open scoped BigOperators

variable {n q k a : ℕ}

/-- Original-color disconnected middle case, on one ACTUAL retained
connected component. Tail exclusions, charges, counts and the original
palette bound are derived internally. No numerical IH is assumed. -/
theorem OriginalResidualCutFamily.original_color_count_le_formula_of_middle_component
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (hk : 8 ≤ k) (hkn : k ≤ n)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (C : (originalCutFamilyGlobalRetainedGraph F).ConnectedComponent)
    (A : (pathGraph a).Copy C.toSimpleGraph)
    (hheadFree : (pathGraph (a + 1)).Free C.toSimpleGraph)
    (hlower : (k - 2) / 2 + 1 ≤ a)
    (hupper : a ≤ k - 3) :
    q + 1 ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  classical
  let H := originalCutFamilyGlobalRetainedGraph F
  let E := originalCutFamilyGlobalComponentCoupling F
  let S : Finset H.ConnectedComponent := Finset.univ.erase C
  let d : ℕ := k - a - 1
  let v : ℕ := Nat.card C.supp
  let u : ℕ := ∑ D ∈ S, Nat.card D.supp
  let eTail : ℕ := ∑ D ∈ S, Nat.card D.toSimpleGraph.edgeSet
  let c : ℝ := ((d : ℝ) - 1) / 2 + 1 / (d : ℝ)

  have ha4 : 4 ≤ a := by omega
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hda : d ≤ a := by dsimp [d]; omega
  have hak : a + d + 1 = k := by dsimp [d]; omega
  have hav : a ≤ v := by
    let f : Fin a → C.supp := fun j => ⟨(A j).val, (A j).property⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply A.injective
      apply Subtype.ext
      exact congrArg (fun z : C.supp => z.val) hij
    simpa only [v, Nat.card_fin] using
      Nat.card_le_card_of_injective f hf

  have hsupp (D : H.ConnectedComponent) :
      D.supp = F.pieceSupport (E D) := by
    have h := originalCutFamilyGlobalComponentCoupling_supp F (E D)
    change (E.symm (E D)).supp = F.pieceSupport (E D) at h
    simpa only [Equiv.symm_apply_apply] using h

  let includeC : C.toSimpleGraph.Copy H :=
    C.toSimpleGraph_hom.toCopy Subtype.val_injective
  let A0 : (pathGraph a).Copy H := includeC.comp A
  have hA0 : Set.range (fun j => A0 j) ⊆ F.pieceSupport (E C) := by
    rintro z ⟨j, rfl⟩
    rw [← hsupp C]
    exact (A j).property

  have hother (D : H.ConnectedComponent) (hDC : D ≠ C) :
      (pathGraph (d + 1)).Free D.toSimpleGraph := by
    rintro ⟨B⟩
    let includeD : D.toSimpleGraph.Copy H :=
      D.toSimpleGraph_hom.toCopy Subtype.val_injective
    let B0 : (pathGraph (d + 1)).Copy H := includeD.comp B
    have hB0 : Set.range (fun j => B0 j) ⊆ F.pieceSupport (E D) := by
      rintro z ⟨j, rfl⟩
      rw [← hsupp D]
      exact (B j).property
    have hij : E C ≠ E D := by
      intro h
      exact hDC (E.injective h).symm
    have hlt := originalCutFamily_two_piece_path_order_lt
      F hno (E C) (E D) hij (by omega) (by omega) A0 B0 hA0 hB0
    omega

  have hpositive (D : H.ConnectedComponent) : 1 ≤ Nat.card D.supp := by
    obtain ⟨z, hz⟩ := D.nonempty_supp
    let : Nonempty D.supp := ⟨⟨z, hz⟩⟩
    have hpos : 0 < Nat.card D.supp := Nat.card_pos
    omega

  have hcharge (D : H.ConnectedComponent) (hD : D ∈ S) :
      (Nat.card D.toSimpleGraph.edgeSet : ℝ) + 1 ≤
        c * (Nat.card D.supp : ℝ) := by
    have hDC : D ≠ C := (Finset.mem_erase.mp hD).1
    exact ordinary_component_charge_real D.toSimpleGraph d hd
      (hpositive D) (hother D hDC)

  have hsum := Finset.sum_le_sum (s := S) (fun D hD => hcharge D hD)
  have htail :
      (eTail : ℝ) + (S.card : ℝ) ≤ c * (u : ℝ) := by
    simpa only [eTail, u, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one, Nat.cast_sum, Finset.mul_sum] using hsum

  have hhead :
      Nat.card C.toSimpleGraph.edgeSet ≤
        ErdosProblems.PathLemmaFourEnvelope.scalarCap a v :=
    ComponentScalarCap1105.connected_component_scalar_cap
      a ha4 C.toSimpleGraph A hheadFree C.connected_toSimpleGraph

  have heparts :
      Nat.card C.toSimpleGraph.edgeSet + eTail =
        ∑ D : H.ConnectedComponent, Nat.card D.toSimpleGraph.edgeSet := by
    dsimp [eTail, S]
    exact Finset.add_sum_erase Finset.univ
      (fun D : H.ConnectedComponent => Nat.card D.toSimpleGraph.edgeSet)
      (Finset.mem_univ C)

  have hvparts :
      v + u = ∑ D : H.ConnectedComponent, Nat.card D.supp := by
    dsimp [v, u, S]
    exact Finset.add_sum_erase Finset.univ
      (fun D : H.ConnectedComponent => Nat.card D.supp)
      (Finset.mem_univ C)

  have hvertices := originalCutFamily_global_component_vertex_sum F
  change (∑ D : H.ConnectedComponent, Nat.card D.supp) = n at hvertices
  have hvu : v + u = n := hvparts.trans hvertices

  have hq0 := originalCutFamily_global_component_edge_sum F
  change q =
    (∑ D : H.ConnectedComponent, Nat.card D.toSimpleGraph.edgeSet) +
      F.cutCount at hq0
  have hq :
      q = Nat.card C.toSimpleGraph.edgeSet + eTail + F.cutCount := by
    rw [← heparts] at hq0
    exact hq0

  have hcard :
      S.card + 1 = Nat.card H.ConnectedComponent := by
    simpa only [S, Finset.card_univ, Nat.card_eq_fintype_card] using
      (Finset.card_erase_add_one
        (s := (Finset.univ : Finset H.ConnectedComponent))
        (Finset.mem_univ C))
  have hbudget := (F.proper_first_cut_budget hproper).2.2
  change F.cutCount + 2 ≤ Nat.card H.ConnectedComponent at hbudget
  have hqNat :
      q + 1 ≤ Nat.card C.toSimpleGraph.edgeSet + eTail + S.card := by
    omega
  have hqReal :
      (q : ℝ) + 1 ≤
        (Nat.card C.toSimpleGraph.edgeSet : ℝ) +
          (eTail : ℝ) + (S.card : ℝ) := by
    exact_mod_cast hqNat
  have hheadReal :
      (Nat.card C.toSimpleGraph.edgeSet : ℝ) ≤
        (ErdosProblems.PathLemmaFourEnvelope.scalarCap a v : ℝ) := by
    exact_mod_cast hhead
  have hmiddle :
      (q : ℝ) + 1 ≤
        (ErdosProblems.PathLemmaFourEnvelope.scalarCap a v : ℝ) +
          c * (u : ℝ) := by
    linarith

  have henvelope :=
    ErdosProblems.PathLemmaFourEnvelope.scalar_affine_envelope
      a d v u hda hd hav (by omega)
  have hformula :
      ErdosProblems.PathLemmaFourEnvelope.pathFormula
          (v + u) (a + d + 1) =
        ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
    rw [hvu, hak]
    rfl
  rw [hformula] at henvelope
  have hfull :
      (q : ℝ) + 1 ≤
        (ErdosProblems.PathLemmaFourScalar.pathFormula n k : ℝ) :=
    hmiddle.trans henvelope
  exact_mod_cast hfull

end ErdosProblems.PathUpperReduction
end

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q k : ℕ}

/-- The original palette bound throughout the proper-first branch, under the
FULL smaller-complete-host IH. Every structural path case is derived on the
actual SAME-R family; no favorable component or numerical cap is supplied. -/
theorem OriginalResidualCutFamily.original_color_count_le_formula_of_proper_first_component
    {χ : TopEdgeLabeling (Fin n) (Fin q)} {R : RepresentativeChoice χ}
    {x : Fin n} {xs : List (Fin n)}
    (F : OriginalResidualCutFamily χ R ∅ Set.univ (x :: xs))
    (hproper : componentSupport χ R x ≠ Set.univ)
    (hk : 8 ≤ k) (hkn : k ≤ n)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n) :
    q ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  classical
  by_contra hbound
  have hhigh : ErdosProblems.PathLemmaFourScalar.pathFormula n k < q := by omega
  have hlong := F.no_long_retained_path_of_proper_first_component
    hproper (by omega) hkn hno hIH hhigh
  rcases F.all_short_or_middle_component_of_no_long hk hlong with
    hshort | ⟨C, a, hlower, hupper, ⟨A⟩, hheadFree⟩
  · have hshortBound := F.original_color_count_le_formula_of_all_short
      hproper (by omega) hkn hshort
    exact (not_lt_of_ge hshortBound) hhigh
  · have hmiddleBound := F.original_color_count_le_formula_of_middle_component
      hproper hk hkn hno C A hheadFree hlower hupper
    omega

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- Remaining connected original-color step at one host size. Its IH concerns
only strictly smaller complete hosts, including every allowed smaller size. -/
def OriginalConnectedPathStep (k n : ℕ) : Prop :=
  ∀ (q : ℕ) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (R : RepresentativeChoice χ), k ≤ n →
    (selectedGraph χ R).Connected →
    (∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ) →
    OriginalFullSmallerHostIH k n →
    q ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k

/-- Construct the actual full family. Both its connected and proper-first exits
receive the SAME genuine current-host FULL smaller-host induction hypothesis. -/
theorem original_color_count_le_formula_of_connected_step_and_full_IH
    {k n q : ℕ} (hk : 8 ≤ k) (hkn : k ≤ n)
    (hstep : OriginalConnectedPathStep k n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow P.toHom χ)
    (hIH : OriginalFullSmallerHostIH k n) :
    q ≤ ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  classical
  obtain ⟨R, roots, F, _hgreedy, _hpieces, _hcount, _hT, _hS, hcover, _hdisjoint⟩ :=
    exists_full_original_cut_family χ (choiceOfSurjective χ hχ)
  cases roots with
  | nil =>
      obtain ⟨x, hx, _⟩ := hcover (⟨0, by omega⟩ : Fin n)
      simp at hx
  | cons x xs =>
      by_cases hwhole : componentSupport χ R x = Set.univ
      · have hconn : (selectedGraph χ R).Connected := by
          apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
          refine ⟨x, fun v => ?_⟩
          apply (mem_componentSupport χ R x v).mp
          rw [hwhole]
          exact Set.mem_univ v
        exact hstep q χ R hkn hconn hno hIH
      · exact F.original_color_count_le_formula_of_proper_first_component
          hwhole hk hkn hno hIH

/-- Strong induction constructs FULL IH from strictly smaller proven hosts,
then applies the pointwise connected step only at the current host. -/
theorem antiRamseyNum_path_le_formula_of_connected_steps
    (k : ℕ) (hk : 8 ≤ k)
    (hsteps : ∀ n : ℕ, OriginalConnectedPathStep k n) :
    ∀ n : ℕ, k ≤ n →
      antiRamseyNum (pathGraph k) n ≤
        ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hkn
      classical
      let admissible : Set ℕ :=
        {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
          ∀ P : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
            ¬ IsRainbow P.toHom χ}
      have hbounded : BddAbove admissible := by
        refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
        intro q hq
        obtain ⟨χ, hχ, _⟩ := hq
        simpa using Fintype.card_le_of_surjective χ hχ
      change sSup admissible ≤ _
      apply (csSup_le_iff' hbounded).2
      intro q hq
      obtain ⟨χ, hχ, hno⟩ := hq
      have hIH : OriginalFullSmallerHostIH k n := by
        intro m hkm hmn
        exact ih m hmn hkm
      exact original_color_count_le_formula_of_connected_step_and_full_IH
        hk hkn (hsteps n) χ hχ hno hIH

/-- All current-host steps are equivalent to the full original upper bound.
No step is manufactured by assuming its own conclusion as an induction IH. -/
theorem original_connected_path_steps_iff_full_upper
    (k : ℕ) (hk : 8 ≤ k) :
    (∀ n : ℕ, OriginalConnectedPathStep k n) ↔
      ∀ n : ℕ, k ≤ n →
        antiRamseyNum (pathGraph k) n ≤
          ErdosProblems.PathLemmaFourScalar.pathFormula n k := by
  constructor
  · exact antiRamseyNum_path_le_formula_of_connected_steps k hk
  · intro hupper n q χ R hkn _hconn hno _hIH
    have hχ : Function.Surjective χ := by
      intro c
      exact ⟨R.edge c, R.color_eq c⟩
    exact (original_surjective_noRainbow_color_count_le_antiRamseyNum
      (pathGraph k) χ hχ hno).trans (hupper n hkn)

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction.OddUniversalUpper1105

open SimpleGraph

/-- Literal original anti-Ramsey upper bound on every complete host, for every
odd path order k>=9. No supplied connectivity, family, degree or IH premise. -/
theorem antiRamseyNum_odd_path_le_formula (k n : ℕ)
    (hk : 9 ≤ k) (hodd : Odd k) (hkn : k ≤ n) :
    antiRamseyNum (pathGraph k) n ≤
      max ((k - 2).choose 2 + 1)
        (((k - 1) / 2 - 1).choose 2 +
          ((k - 1) / 2 - 1) * (n - (k - 1) / 2 + 1) + 1) := by
  let ell : ℕ := (k - 1) / 2
  have hparity := Nat.odd_iff.mp hodd
  have hkEq : k = 2 * ell + 1 := by dsimp only [ell]; omega
  have hell : 4 ≤ ell := by omega
  have hsteps : ∀ u : ℕ, OriginalConnectedPathStep k u := by
    intro u q χ R hku hconn hno _hIH
    have hku' : 2 * ell + 1 ≤ u := by omega
    have hno' : ∀ P : (pathGraph (2 * ell + 1)).Copy
        (⊤ : SimpleGraph (Fin u)), ¬ IsRainbow P.toHom χ := by
      rw [← hkEq]
      exact hno
    have hbound :=
      OddConnectedOriginalUpper1105.original_connected_odd_palette_upper
        hell hku' χ R hconn hno'
    have hhalf : (k - 1) / 2 = ell := rfl
    have hpred : k - 2 = 2 * ell - 1 := by omega
    simpa only [ErdosProblems.PathLemmaFourScalar.pathFormula,
      hhalf, hpred, ite_eq_left hodd] using hbound
  have hupper := antiRamseyNum_path_le_formula_of_connected_steps
    k (by omega) hsteps n hkn
  simpa only [ErdosProblems.PathLemmaFourScalar.pathFormula, ite_eq_left hodd] using hupper

end ErdosProblems.PathUpperReduction.OddUniversalUpper1105

namespace ErdosProblems.PathUpperReduction.SeedFillCycleClosure1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.SingleEdgeHamiltonianClosure1105
open ErdosProblems.PathUpperReduction.CoreElimination

noncomputable instance graph_neighborSet_fintype {n : ℕ}
    (G : SimpleGraph (Fin n)) (x : Fin n) :
    Fintype (G.neighborSet x) := Fintype.ofFinite _

noncomputable def seedPairs {V : Type*} (K : Finset V) : Finset (V × V) := by
  classical
  exact (K.product K).filter (fun p => p.1 ≠ p.2)

noncomputable def fillSeed {V : Type*} (G : SimpleGraph V)
    (K : Finset V) : SimpleGraph V := by
  classical
  exact G ⊔ fromEdgeSet (seedPairs K |>.image (fun p => s(p.1, p.2)) : Set (Sym2 V))

theorem original_le_fillSeed {V : Type*} (G : SimpleGraph V) (K : Finset V) :
    G ≤ fillSeed G K := le_sup_left

/-- Only actual seed pairs are filled, including when the ambient type has
vertices outside the intended eventual carrier. -/
theorem fillSeed_isClique {V : Type*} (G : SimpleGraph V) (K : Finset V) :
    (fillSeed G K).IsClique (K : Set V) := by
  classical
  intro a ha b hb hab
  apply Or.inr
  apply (fromEdgeSet_adj _).mpr
  refine ⟨?_, hab⟩
  change s(a, b) ∈ (seedPairs K).image (fun p => s(p.1, p.2))
  exact Finset.mem_image.mpr ⟨(a, b),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩

/-- Exact adjacency, used to transport this SAME seed filling to the actual
induced carrier and its finite reindexing. -/
theorem fillSeed_adj_iff {V : Type*} (G : SimpleGraph V) (K : Finset V)
    (x y : V) :
    (fillSeed G K).Adj x y ↔ G.Adj x y ∨ (x ∈ K ∧ y ∈ K ∧ x ≠ y) := by
  classical
  constructor
  · intro h
    rcases h with hG | hfill
    · exact Or.inl hG
    · have he := ((fromEdgeSet_adj _).mp hfill).1
      change s(x, y) ∈ (seedPairs K).image (fun p => s(p.1, p.2)) at he
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp he
      have hpK := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hne := ((fromEdgeSet_adj _).mp hfill).2
      apply Or.inr
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact ⟨heq.1 ▸ hpK.1, heq.2 ▸ hpK.2, hne⟩
      · exact ⟨heq.2 ▸ hpK.2, heq.1 ▸ hpK.1, hne⟩
  · rintro (hG | ⟨hx, hy, hne⟩)
    · exact original_le_fillSeed G K hG
    · exact fillSeed_isClique G K hx hy hne

/-- Filling seed pairs changes no original adjacency at a restored vertex. -/
theorem fillSeed_adj_outside {V : Type*} (G : SimpleGraph V) (K : Finset V)
    {x y : V} (hx : x ∉ K) : (fillSeed G K).Adj x y ↔ G.Adj x y := by
  classical
  constructor
  · intro h
    rcases h with hG | hfill
    · exact hG
    · have he := ((fromEdgeSet_adj _).mp hfill).1
      change s(x, y) ∈ (seedPairs K).image (fun p => s(p.1, p.2)) at he
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp he
      have hpK := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact False.elim (hx (heq.1 ▸ hpK.1))
      · exact False.elim (hx (heq.2 ▸ hpK.2))
  · intro h
    exact original_le_fillSeed G K h

theorem fillSeed_withinDegree_outside {V : Type*} [Fintype V]
    (G : SimpleGraph V) (K U : Finset V) {x : V} (hx : x ∉ K) :
    letI := Classical.decEq V
    letI := Classical.propDecidable
    withinDegree (fillSeed G K) U x = withinDegree G U x := by
  classical
  unfold withinDegree
  congr 1
  apply Finset.filter_congr
  intro y _hy
  exact fillSeed_adj_outside G K hx

/-- Every finite cover of the filled seed has at least |K|-1 vertices; the
complement inside K is independent in a clique and therefore has size≤1. -/
theorem fillSeed_cover_bound {V : Type*} (G : SimpleGraph V) (K X : Finset V)
    (hcover : ∀ u ∈ K, ∀ v ∈ K, (fillSeed G K).Adj u v → u ∈ X ∨ v ∈ X) :
    K.card - 1 ≤ X.card := by
  classical
  have hsmall : (K \ X).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := Finset.mem_sdiff.mp ha
    have hb' := Finset.mem_sdiff.mp hb
    by_contra hab
    rcases hcover a ha'.1 b hb'.1
      (fillSeed_isClique G K ha'.1 hb'.1 hab) with haX | hbX
    · exact ha'.2 haX
    · exact hb'.2 hbX
  have hledger := Finset.card_sdiff_add_card_inter K X
  have hinter : (K ∩ X).card ≤ X.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

noncomputable def fillPairs {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) := by
  classical
  exact G ⊔ fromEdgeSet (P.image (fun p => s(p.1, p.2)) : Set (Sym2 (Fin n)))

theorem fillPairs_insert {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    fillPairs G (insert p P) = fillPairs G P ⊔ fromEdgeSet {s(p.1, p.2)} := by
  classical
  have hset :
      ((insert p P).image (fun q => s(q.1, q.2)) : Set (Sym2 (Fin n))) =
        {s(p.1, p.2)} ∪ (P.image (fun q => s(q.1, q.2)) : Set (Sym2 (Fin n))) := by
    ext e
    simp only [Finset.image_insert, Finset.mem_coe, Finset.mem_insert,
      Set.mem_union, Set.mem_singleton_iff]
  simp only [fillPairs, hset, fromEdgeSet_union]
  ac_rfl

theorem finite_pair_closure_iff {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (P : Finset (Fin n × Fin n))
    (hpair : ∀ p, p ∈ P → p.1 ≠ p.2 ∧ n ≤ G.degree p.1 + G.degree p.2) :
    cycleGraph n ⊑ fillPairs G P ↔ cycleGraph n ⊑ G := by
  classical
  revert hpair
  induction P using Finset.induction_on with
  | empty => intro _hpair; simp [fillPairs]
  | @insert p P _hp ih =>
    intro hpair
    have hthis := hpair p (Finset.mem_insert_self p P)
    have hrest : ∀ q, q ∈ P → q.1 ≠ q.2 ∧ n ≤ G.degree q.1 + G.degree q.2 := by
      intro q hq
      exact hpair q (Finset.mem_insert_of_mem hq)
    have hrestIff := ih hrest
    let H : SimpleGraph (Fin n) := fillPairs G P
    have hGH : G ≤ H := le_sup_left
    have hdegree : n ≤ H.degree p.1 + H.degree p.2 := by
      exact hthis.2.trans (Nat.add_le_add
        (G.degree_le_of_le (v := p.1) hGH) (G.degree_le_of_le (v := p.2) hGH))
    have hsingle : cycleGraph n ⊑ (H ⊔ fromEdgeSet {s(p.1, p.2)}) ↔
        cycleGraph n ⊑ H := by
      by_cases hadj : H.Adj p.1 p.2
      · have hsubset : ({s(p.1, p.2)} : Set (Sym2 (Fin n))) ⊆ H.edgeSet := by
          intro e he
          rcases Set.mem_singleton_iff.mp he with rfl
          exact hadj
        have hedge : fromEdgeSet {s(p.1, p.2)} ≤ H := by
          simpa only [fromEdgeSet_edgeSet] using fromEdgeSet_mono hsubset
        rw [sup_eq_left.mpr hedge]
      · exact cycle_contained_add_edge_iff hn H p.1 p.2 hthis.1 hadj hdegree
    rw [fillPairs_insert]
    exact hsingle.trans hrestIff

/-- On the ACTUAL2d carrier, original seed degree≥d derives all pair bounds
internally and finite reversal preserves its spanning-cycle predicate. -/
theorem cycle_contained_fill_seed_iff {d : ℕ} (hd : 2 ≤ d)
    (G : SimpleGraph (Fin (2 * d))) (K : Finset (Fin (2 * d)))
    (hseed : ∀ x ∈ K, d ≤ G.degree x) :
    cycleGraph (2 * d) ⊑ fillSeed G K ↔ cycleGraph (2 * d) ⊑ G := by
  classical
  have hpair : ∀ p, p ∈ seedPairs K → p.1 ≠ p.2 ∧
      2 * d ≤ G.degree p.1 + G.degree p.2 := by
    intro p hp
    have hp' : p ∈ K.product K ∧ p.1 ≠ p.2 := by
      simpa only [seedPairs, Finset.mem_filter] using hp
    have hprod := Finset.mem_product.mp hp'.1
    refine ⟨hp'.2, ?_⟩
    have hleft := hseed p.1 hprod.1
    have hright := hseed p.2 hprod.2
    omega
  simpa only [fillSeed, fillPairs, Finset.coe_image] using
    finite_pair_closure_iff (by omega) G (seedPairs K) hpair

end ErdosProblems.PathUpperReduction.SeedFillCycleClosure1105

namespace ErdosProblems.AntiRamseyCycleTwoSpliceSkipExtraction

open SimpleGraph

noncomputable instance graph_neighborSet_fintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Fintype (G.neighborSet v) := Fintype.ofFinite _

/-- Exact shifted intersection extraction for the final partial reversal.
The two internal degrees are on the literal castSucc/succ tail images. -/
theorem exists_two_splice_skips {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (_hm : 2 ≤ m) (G : SimpleGraph V)
    (R : Fin (m + 3) → V) (hR : Function.Injective R)
    (hleft : ¬ G.Adj (R 0) (R ⟨m + 1, by omega⟩))
    (hright : ¬ G.Adj (R ⟨1, by omega⟩) (R (Fin.last (m + 2))))
    (hsum : m + 2 ≤
      (G.neighborFinset (R 0) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.castSucc i))).card +
      (G.neighborFinset (R ⟨1, by omega⟩) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.succ i))).card) :
    ∃ a : Fin (m + 3), ∃ _ha2 : 2 ≤ a.val, ∃ ham : a.val ≤ m,
      G.Adj (R 0) (R a) ∧
      G.Adj (R ⟨1, by omega⟩) (R ⟨a.val + 1, by omega⟩) := by
  classical
  let p : Fin (m + 2) → V := fun i => R (Fin.castSucc i)
  let q : Fin (m + 2) → V := fun i => R (Fin.succ i)
  let P : Finset V := Finset.univ.image p
  let Q : Finset V := Finset.univ.image q
  let A : Finset (Fin (m + 2)) := Finset.univ.filter (fun i => G.Adj (R 0) (p i))
  let B : Finset (Fin (m + 2)) :=
    Finset.univ.filter (fun i => G.Adj (R ⟨1, by omega⟩) (q i))
  have hp : Function.Injective p := by
    intro i j h
    exact Fin.castSucc_inj.mp (hR h)
  have hq : Function.Injective q := by
    intro i j h
    exact Fin.succ_inj.mp (hR h)
  have hAimage : A.image p = G.neighborFinset (R 0) ∩ P := by
    calc
      A.image p = P.filter (G.Adj (R 0)) := by
        simpa only [A, P] using
          (Finset.filter_image (s := Finset.univ) (f := p) (p := G.Adj (R 0))).symm
      _ = _ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact and_comm
  have hBimage : B.image q = G.neighborFinset (R ⟨1, by omega⟩) ∩ Q := by
    calc
      B.image q = Q.filter (G.Adj (R ⟨1, by omega⟩)) := by
        simpa only [B, Q] using
          (Finset.filter_image (s := Finset.univ) (f := q)
            (p := G.Adj (R ⟨1, by omega⟩))).symm
      _ = _ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact and_comm
  have hAcard : (G.neighborFinset (R 0) ∩ P).card = A.card := by
    rw [← hAimage]
    exact Finset.card_image_of_injective A hp
  have hBcard : (G.neighborFinset (R ⟨1, by omega⟩) ∩ Q).card = B.card := by
    rw [← hBimage]
    exact Finset.card_image_of_injective B hq
  have hABsum : m + 2 ≤ A.card + B.card := by
    change m + 2 ≤ (G.neighborFinset (R 0) ∩ P).card +
      (G.neighborFinset (R ⟨1, by omega⟩) ∩ Q).card at hsum
    rw [hAcard, hBcard] at hsum
    exact hsum
  have hAbounds : ∀ j : Fin (m + 2), j ∈ A → 1 ≤ j.val ∧ j.val ≤ m := by
    intro j hj
    have hadj : G.Adj (R 0) (R (Fin.castSucc j)) :=
      (Finset.mem_filter.mp hj).2
    have hj0 : j.val ≠ 0 := by
      intro heq
      have hidx : Fin.castSucc j = (0 : Fin (m + 3)) := Fin.ext heq
      rw [hidx] at hadj
      exact G.irrefl hadj
    have hjlast : j.val ≠ m + 1 := by
      intro heq
      have hidx : Fin.castSucc j = (⟨m + 1, by omega⟩ : Fin (m + 3)) := Fin.ext heq
      apply hleft
      simpa only [hidx] using hadj
    have hjlt := j.isLt
    omega
  have hBbounds : ∀ j : Fin (m + 2), j ∈ B → 1 ≤ j.val ∧ j.val ≤ m := by
    intro j hj
    have hadj : G.Adj (R ⟨1, by omega⟩) (R (Fin.succ j)) :=
      (Finset.mem_filter.mp hj).2
    have hj0 : j.val ≠ 0 := by
      intro heq
      have hidx : Fin.succ j = (⟨1, by omega⟩ : Fin (m + 3)) := by
        apply Fin.ext
        change j.val + 1 = 1
        omega
      rw [hidx] at hadj
      exact G.irrefl hadj
    have hjlast : j.val ≠ m + 1 := by
      intro heq
      have hidx : Fin.succ j = Fin.last (m + 2) := by
        apply Fin.ext
        change j.val + 1 = m + 2
        omega
      apply hright
      simpa only [hidx] using hadj
    have hjlt := j.isLt
    omega
  let S : Finset (Fin (m + 3)) := A.image Fin.succ
  let T : Finset (Fin (m + 3)) := B.image Fin.succ
  let u : Fin m → Fin (m + 3) := fun i => ⟨i.val + 2, by have hi := i.isLt; omega⟩
  let U : Finset (Fin (m + 3)) := Finset.univ.image u
  have hsucc : Function.Injective (Fin.succ : Fin (m + 2) → Fin (m + 3)) := by
    intro i j h
    exact Fin.succ_inj.mp h
  have hu : Function.Injective u := by
    intro i j h
    have hv : i.val + 2 = j.val + 2 := congrArg Fin.val h
    apply Fin.ext
    omega
  have hScard : S.card = A.card := Finset.card_image_of_injective A hsucc
  have hTcard : T.card = B.card := Finset.card_image_of_injective B hsucc
  have hUcard : U.card = m := by
    change (Finset.univ.image u).card = m
    rw [Finset.card_image_of_injective Finset.univ hu]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hSU : S ⊆ U := by
    intro b hb
    obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hb
    have hbounds := hAbounds j hj
    let i : Fin m := ⟨j.val - 1, by omega⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [← hjb]
    apply Fin.ext
    change (j.val - 1) + 2 = j.val + 1
    omega
  have hTU : T ⊆ U := by
    intro b hb
    obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp hb
    have hbounds := hBbounds j hj
    let i : Fin m := ⟨j.val - 1, by omega⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [← hjb]
    apply Fin.ext
    change (j.val - 1) + 2 = j.val + 1
    omega
  have hUnion : (S ∪ T).card ≤ m := by
    have hbound : (S ∪ T).card ≤ U.card := by
      apply Finset.card_le_card
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact hSU hb
      · exact hTU hb
    exact hbound.trans_eq hUcard
  have hSTsum : m + 2 ≤ S.card + T.card := by
    rw [hScard, hTcard]
    exact hABsum
  have hInter : 1 < (S ∩ T).card := by
    have hidentity := Finset.card_union_add_card_inter S T
    omega
  obtain ⟨b, hb, hbne⟩ := Finset.exists_mem_ne hInter (⟨2, by omega⟩ : Fin (m + 3))
  obtain ⟨j, hjA, hjb⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).1
  obtain ⟨l, hlB, hlb⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).2
  have hjl : j = l := hsucc (hjb.trans hlb.symm)
  have hjB : j ∈ B := hjl.symm ▸ hlB
  have hbounds := hAbounds j hjA
  have hjone : j.val ≠ 1 := by
    intro heq
    apply hbne
    calc
      b = Fin.succ j := hjb.symm
      _ = (⟨2, by omega⟩ : Fin (m + 3)) := by
        apply Fin.ext
        change j.val + 1 = 2
        omega
  let a : Fin (m + 3) := Fin.castSucc j
  have ha2 : 2 ≤ a.val := by
    change 2 ≤ j.val
    omega
  have ham : a.val ≤ m := hbounds.2
  refine ⟨a, ha2, ham, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hjA).2
  · have hadj : G.Adj (R ⟨1, by omega⟩) (R (Fin.succ j)) :=
      (Finset.mem_filter.mp hjB).2
    have hidx : (⟨a.val + 1, by omega⟩ : Fin (m + 3)) = Fin.succ j := Fin.ext rfl
    simpa only [hidx] using hadj

end ErdosProblems.AntiRamseyCycleTwoSpliceSkipExtraction

namespace ErdosProblems.AntiRamseyCycleRotatingClaimTwo

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimTwoOrientedInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem numeric_ordered_of_steps {V : Type*} {t : ℕ}
    (G : SimpleGraph V) (p : Fin (t + 1) → V)
    (hstep : ∀ i : Fin t, G.Adj (p (Fin.castSucc i)) (p (Fin.succ i))) :
    ∀ a b : Fin (t + 1), a.val + 1 = b.val → G.Adj (p a) (p b) := by
  intro a b hab
  have ha : a.val < t := by have hb := b.isLt; omega
  let i : Fin t := ⟨a.val, ha⟩
  have hcast : Fin.castSucc i = a := Fin.ext rfl
  have hsucc : Fin.succ i = b := Fin.ext hab
  simpa only [hcast, hsucc] using hstep i

theorem no_endpoint_chord_of_local_cycle_exclusion
    {s : ℕ} (hs : 2 ≤ s) (G : SimpleGraph (Fin n))
    (p : Fin (s + 1) → Fin n) (hp : Function.Injective p)
    (hstep : ∀ i : Fin s, G.Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (s + 1), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (s + 1)).Copy G,
      ¬∀ i : Fin (s + 1), f i ∈ D) :
    ¬ G.Adj (p 0) (p (Fin.last s)) := by
  intro hchord
  have : NeZero s := ⟨by omega⟩
  let H : SimpleGraph (Fin (s + 1)) := G.comap p
  have hfree :=
    ErdosProblems.AntiRamseyCyclePathOre.cycle_free_on_ordered_path_of_component
      G p hp D hpD hnoD
  have hHpath : ∀ a b : Fin (s + 1), a.val + 1 = b.val → H.Adj a b :=
    numeric_ordered_of_steps G p hstep
  have hA : H.Adj 0 (Fin.succ (0 : Fin s)) := hstep 0
  have hB : H.Adj (Fin.last s) (Fin.castSucc (0 : Fin s)) := hchord.symm
  exact hfree
    (ErdosProblems.AntiRamseyCyclePathOre.crossing_chords_force_cycle
      hs H hHpath 0 hA hB)

/-- An inward selected tail in the original high distinct-pair regime is
impossible under the exact host/local-cycle hypotheses, by rotating splice. -/
theorem inward_tail_contradiction
    {m : ℕ} (hm : 2 ≤ m)
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
    (hpair : ∀ u v : Fin n, u ≠ v →
      m + 2 ≤ (newColors χ u).card + (newColors χ v).card)
    (hclosed : ∀ v : Fin n, v ∈ D → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D) : False := by
  classical
  have hpEnds : p 0 ≠ p (Fin.last (m + 1)) := hp.ne (by
    intro h
    have hv : 0 = m + 1 := congrArg Fin.val h
    omega)
  have hpairP := hpair (p 0) (p (Fin.last (m + 1))) hpEnds
  obtain ⟨w, _e, _hwImage, _hadj, _he, _hnew, hconfig⟩ :=
    ErdosProblems.AntiRamseyCycleForcedTailAppendSuffix.forced_tail_literal_append_and_suffix
      (by omega) χ r p hp hpath hnewLast hno D hpD hnoD hpairP hclosed
  dsimp only at hconfig
  obtain ⟨hRpath, hQpath, hR, _hRD, hQ, hQD, _hval, _hcolor, _hinner,
    _hsame, _hQold, hRnew, hQnew⟩ := hconfig
  let R : Fin (m + 3) → Fin n := Fin.snoc p w
  let Q : Fin (m + 2) → Fin n := fun i => R i.succ
  have hprefix : ∀ i : Fin (m + 2), R (Fin.castSucc i) = p i := by
    intro i
    simp only [R, Fin.snoc_castSucc]
  have hprefixMap : (fun i : Fin (m + 2) => R (Fin.castSucc i)) = p := funext hprefix
  have hRzero : R 0 = p 0 := hprefix 0
  have hQzero : Q 0 = R ⟨1, by omega⟩ := rfl
  have hprefixLast : R ⟨m + 1, by omega⟩ = p (Fin.last (m + 1)) := by
    have hidx : (⟨m + 1, by omega⟩ : Fin (m + 3)) =
        Fin.castSucc (Fin.last (m + 1)) := Fin.ext rfl
    rw [hidx]
    exact hprefix (Fin.last (m + 1))
  have hQLast : Q (Fin.last (m + 1)) = R (Fin.last (m + 2)) := by
    simp only [Q, Fin.succ_last]
  have hforbidLeft : ¬ (selectedGraph χ r).Adj (R 0) (R ⟨m + 1, by omega⟩) := by
    rw [hRzero, hprefixLast]
    exact no_endpoint_chord_of_local_cycle_exclusion (s := m + 1) (by omega)
      (selectedGraph χ r) p hp hpath D hpD hnoD
  have hforbidRight : ¬ (selectedGraph χ r).Adj
      (R ⟨1, by omega⟩) (R (Fin.last (m + 2))) := by
    rw [← hQzero, ← hQLast]
    exact no_endpoint_chord_of_local_cycle_exclusion (s := m + 1) (by omega)
      (selectedGraph χ r) Q hQ hQpath D hQD hnoD
  have hheadP :=
    ErdosProblems.AntiRamseyCycleHeadNewDominance.no_head_new_deficit_of_inward_tail
      (by omega) χ r p hp hpath hnewLast hno
  have hheadQ :=
    ErdosProblems.AntiRamseyCycleHeadNewDominance.no_head_new_deficit_of_inward_tail
      (by omega) χ r Q hQ hQpath hQnew hno
  have h01 : R 0 ≠ R ⟨1, by omega⟩ := hR.ne (by
    intro h
    have hv : 0 = 1 := congrArg Fin.val h
    omega)
  have hpairHeads := hpair (R 0) (R ⟨1, by omega⟩) h01
  have hdegreeP : (newColors χ (R 0)).card ≤
      ((selectedGraph χ r).neighborFinset (R 0) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.castSucc i))).card := by
    rw [hprefixMap, hRzero]
    exact hheadP
  have hdegreeQ : (newColors χ (R ⟨1, by omega⟩)).card ≤
      ((selectedGraph χ r).neighborFinset (R ⟨1, by omega⟩) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.succ i))).card := by
    change (newColors χ (Q 0)).card ≤
      ((selectedGraph χ r).neighborFinset (Q 0) ∩ Finset.univ.image Q).card
    exact hheadQ
  have hdegreeSum : m + 2 ≤
      ((selectedGraph χ r).neighborFinset (R 0) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.castSucc i))).card +
      ((selectedGraph χ r).neighborFinset (R ⟨1, by omega⟩) ∩
        Finset.univ.image (fun i : Fin (m + 2) => R (Fin.succ i))).card := by omega
  obtain ⟨a, ha2, ham, hskipLeft, hskipRight⟩ :=
    ErdosProblems.AntiRamseyCycleTwoSpliceSkipExtraction.exists_two_splice_skips
      hm (selectedGraph χ r) R hR hforbidLeft hforbidRight hdegreeSum
  have hRordered : ∀ x y : Fin (m + 3), x.val + 1 = y.val →
      (selectedGraph χ r).Adj (R x) (R y) :=
    numeric_ordered_of_steps (selectedGraph χ r) R hRpath
  let closing : HostEdge n :=
    ⟨s(R 0, R (Fin.last (m + 2))), (top_adj _ _).mpr (hR.ne
      (show (0 : Fin (m + 3)) ≠ Fin.last (m + 2) from by
        intro h
        have hv : 0 = m + 2 := congrArg Fin.val h
        omega))⟩
  let e0 : (selectedGraph χ r).edgeSet := selectedPathStep χ r R hRpath 0
  have he0 : e0.val = s(R 0, R ⟨1, by omega⟩) := rfl
  have hclosing : closing.val = s(R 0, R (Fin.last (m + 2))) := rfl
  have hcolor : χ closing = restrictedColor χ r e0 :=
    ErdosProblems.AntiRamseyCycleClosingColorEquality.no_rainbow_forces_first_closing_color
      (m := m + 1) (by omega) χ r R hR hRpath closing hclosing hRnew hno
  obtain ⟨f, hf⟩ :=
    ErdosProblems.AntiRamseyCyclePartialSpliceClosing.supplied_skips_and_first_closing_color_rainbow
      χ r R hR hRordered a ha2 ham hskipLeft hskipRight e0 he0 closing hclosing hcolor
  exact hno f hf

/-- No inward orientation is assumed for the old path: first extension and
literal suffix produce it before invoking the rotating contradiction. -/
theorem ordered_path_contradiction
    {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (p : Fin (m + 2) → Fin n) (hp : Function.Injective p)
    (hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)))
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : Finset (Fin n)) (hpD : ∀ i : Fin (m + 2), p i ∈ D)
    (hnoD : ∀ f : (cycleGraph (m + 2)).Copy (selectedGraph χ r),
      ¬∀ i : Fin (m + 2), f i ∈ D)
    (hpair : ∀ u v : Fin n, u ≠ v →
      m + 2 ≤ (newColors χ u).card + (newColors χ v).card)
    (hclosed : ∀ v : Fin n, v ∈ D → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D) : False := by
  classical
  have hpEnds : p 0 ≠ p (Fin.last (m + 1)) := hp.ne (by
    intro h
    have hv : 0 = m + 1 := congrArg Fin.val h
    omega)
  have hpairP := hpair (p 0) (p (Fin.last (m + 1))) hpEnds
  obtain ⟨R, hRpath, hR, hRD, hRnew⟩ :=
    ErdosProblems.AntiRamseyCycleFirstPathExtension.exists_inward_new_ordered_path_extension
      (t := m + 1) (by omega) χ r p hp
      (numeric_ordered_of_steps (selectedGraph χ r) p hpath) D hpD hnoD hpairP hclosed
  let Q : Fin (m + 2) → Fin n := fun i => R i.succ
  obtain ⟨hQpath, hQ, hQD, _hsame, _hinner, hQnew⟩ :=
    ErdosProblems.AntiRamseyCycleForcedTailAppendSuffix.suffix_inward_new_terminal
      χ r R hR hRpath D hRD hRnew
  exact inward_tail_contradiction hm χ r Q hQ hQpath hQnew hno D hQD hnoD hpair hclosed

end ErdosProblems.AntiRamseyCycleRotatingClaimTwo

namespace ErdosProblems.AntiRamseyCycleSelectedComponentOrder

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleClaimOneCycleComponent
open ErdosProblems.AntiRamseyCycleGenericLongPathSeed
open ErdosProblems.AntiRamseyCycleRotatingClaimTwo

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Under the original high-NEW, distinct-pair NEW and host no-rainbow
conditions, every component of the same arbitrary selected graph has at
most the old cycle order. The oversized branch derives its old-cycle
exclusion in that component, then obtains its path inside that component. -/
theorem selected_component_order_le {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      m + 2 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph (m + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) :
    D.supp.ncard ≤ m + 2 := by
  classical
  by_contra hsmall
  have hlarge : m + 2 < D.supp.ncard := Nat.lt_of_not_ge hsmall
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  let H : SimpleGraph D := D.toSimpleGraph
  let : DecidableRel H.Adj := fun x y => Classical.propDecidable (H.Adj x y)
  let (x : D) : Fintype (H.neighborSet x) :=
    Subtype.fintype (Membership.mem (H.neighborSet x))
  have hdegree (x : D) : H.degree x = G.degree x.val := by
    have hsubset : G.neighborSet x.val ⊆ D.supp := by
      intro y hy
      exact D.mem_supp_of_adj_mem_supp x.property hy
    have hcanonical := SimpleGraph.degree_induce_of_neighborSet_subset
      (G := G) (s := D.supp) (v := x) hsubset
    exact (congrArg
      (fun f : Fintype ((G.induce D.supp).neighborSet x) =>
        @SimpleGraph.degree _ (G.induce D.supp) x f)
      (Subsingleton.elim _ _)).trans
      (hcanonical.trans (congrArg
        (fun f : Fintype (G.neighborSet x.val) => @SimpleGraph.degree _ G x.val f)
        (Subsingleton.elim _ _)))
  have hnewdegree (x : D) : (newColors χ x.val).card ≤ H.degree x := by
    rw [hdegree x]
    exact newChoice_degree_ge_newColors χ r x.val
  have hcardEq : Fintype.card D = D.supp.ncard := by
    calc
      Fintype.card D = Nat.card D := Fintype.card_eq_nat_card
      _ = D.supp.ncard := Nat.card_coe_set_eq D.supp
  have hcard : m + 3 ≤ Fintype.card D := by
    rw [hcardEq]
    omega
  have hmin : ∀ x : D, 2 ≤ H.degree x := by
    intro x
    exact le_trans (hnew x.val) (hnewdegree x)
  have hpairD : ∀ x y : D, x ≠ y →
      (m + 3) - 1 ≤ H.degree x + H.degree y := by
    intro x y hxy
    have hval : x.val ≠ y.val := fun heq => hxy (Subtype.ext heq)
    have hsum := hpair x.val y.val hval
    have hx := hnewdegree x
    have hy := hnewdegree y
    omega
  obtain ⟨q, hq, hqpath⟩ := exists_ordered_path_of_degree_bounds
    (k := m + 3) (by omega) H D.connected_toSimpleGraph hcard hmin hpairD
  let p : Fin (m + 2) → Fin n := fun i => (q (Fin.castSucc i)).val
  have hp : Function.Injective p := by
    intro i j hij
    have hsub : q (Fin.castSucc i) = q (Fin.castSucc j) := Subtype.ext hij
    exact Fin.castSucc_injective _ (hq hsub)
  have hpath : ∀ i : Fin (m + 1),
      (selectedGraph χ r).Adj (p (Fin.castSucc i)) (p (Fin.succ i)) := by
    intro i
    exact hqpath (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.succ i)) rfl
  have hpD : ∀ i : Fin (m + 2), p i ∈ D.supp.toFinset := by
    intro i
    exact Set.mem_toFinset.mpr (q (Fin.castSucc i)).property
  have hnoD : ∀ cyc : (cycleGraph (m + 2)).Copy (selectedGraph χ r),
      ¬ (∀ i : Fin (m + 2), cyc i ∈ D.supp.toFinset) := by
    intro cyc hinside
    apply oversized_component_excludes_selected_cycle (m := m + 1)
      (by omega) χ r hnew hno D hlarge cyc
    intro i
    exact Set.mem_toFinset.mp (hinside i)
  have hclosed : ∀ v : Fin n, v ∈ D.supp.toFinset → ∀ w : Fin n,
      (selectedGraph χ r).Adj v w → w ∈ D.supp.toFinset := by
    intro v hv w hvw
    exact Set.mem_toFinset.mpr
      (D.mem_supp_of_adj_mem_supp (Set.mem_toFinset.mp hv) hvw)
  exact ordered_path_contradiction hm χ r p hp hpath hno
    D.supp.toFinset hpD hnoD hpair hclosed

/-- The same bound stated with the original cycle parameter k >= 5. -/
theorem selected_component_order_le_original {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) :
    D.supp.ncard ≤ k - 1 := by
  have hm : 2 ≤ k - 3 := by omega
  have hpairm : ∀ u v : Fin n, u ≠ v →
      (k - 3) + 2 ≤ (newColors χ u).card + (newColors χ v).card := by
    intro u v huv
    have hbound := hpair u v huv
    omega
  have horder : (k - 3) + 3 = k := by omega
  have hnom : ∀ f : (cycleGraph ((k - 3) + 3)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ := by
    exact horder.symm ▸ hno
  have hbound := selected_component_order_le hm χ r hnew hpairm hnom D
  omega

end ErdosProblems.AntiRamseyCycleSelectedComponentOrder

namespace ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleSelectedComponentOrder
open ErdosProblems.AntiRamseyCycleGenericHamiltonian

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The original high-NEW and distinct-pair conditions give both size bounds
and a spanning selected cycle in each component of the same arbitrary choice.
The Hamiltonian walk is on its actual component support subtype. -/
theorem selected_component_size_bounds_and_hamiltonian_cycle {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) :
    3 ≤ D.supp.ncard ∧
    k + 1 ≤ 2 * D.supp.ncard ∧
    D.supp.ncard ≤ k - 1 ∧
    (cycleGraph D.supp.ncard) ⊑ D.toSimpleGraph ∧
    ∃ (u : D) (c : D.toSimpleGraph.Walk u u), c.IsHamiltonianCycle := by
  classical
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  let H : SimpleGraph D := D.toSimpleGraph
  let : DecidableRel H.Adj := fun x y => Classical.propDecidable (H.Adj x y)
  let (x : D) : Fintype (H.neighborSet x) :=
    Subtype.fintype (Membership.mem (H.neighborSet x))
  have hdegree (x : D) : H.degree x = G.degree x.val := by
    have hsubset : G.neighborSet x.val ⊆ D.supp := by
      intro y hy
      exact D.mem_supp_of_adj_mem_supp x.property hy
    have hcanonical := SimpleGraph.degree_induce_of_neighborSet_subset
      (G := G) (s := D.supp) (v := x) hsubset
    exact (congrArg
      (fun f : Fintype ((G.induce D.supp).neighborSet x) =>
        @SimpleGraph.degree _ (G.induce D.supp) x f)
      (Subsingleton.elim _ _)).trans
      (hcanonical.trans (congrArg
        (fun f : Fintype (G.neighborSet x.val) => @SimpleGraph.degree _ G x.val f)
        (Subsingleton.elim _ _)))
  have hnewdegree (x : D) : (newColors χ x.val).card ≤ H.degree x := by
    rw [hdegree x]
    exact newChoice_degree_ge_newColors χ r x.val
  have hcardEq : Fintype.card D = D.supp.ncard := by
    calc
      Fintype.card D = Nat.card D := Fintype.card_eq_nat_card
      _ = D.supp.ncard := Nat.card_coe_set_eq D.supp
  have hcard3 : 3 ≤ Fintype.card D := by
    obtain ⟨x⟩ := D.connected_toSimpleGraph.nonempty
    have hxnew := hnew x.val
    have hxdegree := hnewdegree x
    have hlt := H.degree_lt_card_verts x
    omega
  have hsmall : k + 1 ≤ 2 * Fintype.card D := by
    obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card
      (show 1 < Fintype.card D by omega)
    have hval : x.val ≠ y.val := fun heq => hxy (Subtype.ext heq)
    have hsum := hpair x.val y.val hval
    have hx := hnewdegree x
    have hy := hnewdegree y
    have hxlt := H.degree_lt_card_verts x
    have hylt := H.degree_lt_card_verts y
    omega
  have hupper := selected_component_order_le_original hk χ r hnew hpair hno D
  have hupperCard : Fintype.card D ≤ k - 1 := by
    rw [hcardEq]
    exact hupper
  have hdegreepair : ∀ x y : D, x ≠ y →
      Fintype.card D ≤ H.degree x + H.degree y := by
    intro x y hxy
    have hval : x.val ≠ y.val := fun heq => hxy (Subtype.ext heq)
    have hsum := hpair x.val y.val hval
    have hx := hnewdegree x
    have hy := hnewdegree y
    omega
  have hspanning := contains_spanning_cycle_of_degree_sum
    H D.connected_toSimpleGraph hcard3 hdegreepair
  have hhamiltonian := exists_hamiltonian_cycle_of_degree_sum
    H D.connected_toSimpleGraph hcard3 hdegreepair
  refine ⟨?_, ?_, hupper, ?_, hhamiltonian⟩
  · simpa only [hcardEq] using hcard3
  · simpa only [hcardEq] using hsmall
  · exact hcardEq ▸ hspanning

end ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian

namespace ErdosProblems.AntiRamseyCycleComponentCyclicIndex

open SimpleGraph
open scoped Classical
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree
open ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian

/-- An injective index map onto an actual component preserves the full
original degree at every indexed vertex. Component closure supplies every
original neighbor; degree equality is proved rather than assumed. -/
theorem degree_comap_eq_of_component_range
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : G.ConnectedComponent) {t : ℕ} (A : Fin t → V)
    (hinj : Function.Injective A) (hrange : Set.range A = D.supp)
    (i : Fin t) :
    (G.comap A).degree i = G.degree (A i) := by
  classical
  let f : G.comap A ↪g G := SimpleGraph.Embedding.comap ⟨A, hinj⟩ G
  let e : G.comap A ≃g G.induce (Set.range A) := f.isoInduceRange
  have hsubset : G.neighborSet (e i).val ⊆ Set.range A := by
    intro v hv
    rw [hrange]
    have hi : (e i).val ∈ D.supp := by
      rw [← hrange]
      exact (e i).property
    exact D.mem_supp_of_adj_mem_supp hi hv
  have hcanonical := SimpleGraph.degree_induce_of_neighborSet_subset
    (G := G) (s := Set.range A) (v := e i) hsubset
  have hfull : (G.induce (Set.range A)).degree (e i) =
      G.degree (e i).val := by
    exact (congrArg
      (fun inst : Fintype ((G.induce (Set.range A)).neighborSet (e i)) =>
        @SimpleGraph.degree _ (G.induce (Set.range A)) (e i) inst)
      (Subsingleton.elim _ _)).trans
      (hcanonical.trans (congrArg
        (fun inst : Fintype (G.neighborSet (e i).val) =>
          @SimpleGraph.degree _ G (e i).val inst)
        (Subsingleton.elim _ _)))
  exact (e.degree_eq i).symm.trans hfull

/-- A copy whose order equals the actual finite component order covers the
whole component. Its original host map supplies a cyclic order and the exact
full-degree comap graph, for an arbitrary finite original graph. -/
theorem spanning_component_copy_host_index
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D : G.ConnectedComponent)
    (c : (cycleGraph D.supp.ncard).Copy D.toSimpleGraph) :
    ∃ A : Fin D.supp.ncard → V,
      Function.Injective A ∧
      (∀ x : D, ∃ i : Fin D.supp.ncard, A i = x.val) ∧
      Set.range A = D.supp ∧
      cycleGraph D.supp.ncard ≤ G.comap A ∧
      ∀ i : Fin D.supp.ncard, (G.comap A).degree i = G.degree (A i) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  have hcard : Fintype.card D = D.supp.ncard := by
    calc
      Fintype.card D = Nat.card D := Fintype.card_eq_nat_card
      _ = D.supp.ncard := Nat.card_coe_set_eq D.supp
  have hbij : Function.Bijective (c : Fin D.supp.ncard → D) :=
    (Fintype.bijective_iff_injective_and_card c).mpr
      ⟨c.injective, by simpa only [Fintype.card_fin] using hcard.symm⟩
  let A : Fin D.supp.ncard → V := fun i => (c i).val
  have hinj : Function.Injective A := by
    intro i j hij
    exact c.injective (Subtype.ext hij)
  have honto : ∀ x : D, ∃ i : Fin D.supp.ncard, A i = x.val := by
    intro x
    obtain ⟨i, hi⟩ := hbij.2 x
    exact ⟨i, congrArg Subtype.val hi⟩
  have hrange : Set.range A = D.supp := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact (c i).property
    · intro hv
      obtain ⟨i, hi⟩ := honto ⟨v, hv⟩
      exact ⟨i, hi⟩
  have hcycle : cycleGraph D.supp.ncard ≤ G.comap A := by
    intro i j hij
    exact c.toHom.map_rel hij
  refine ⟨A, hinj, honto, hrange, hcycle, ?_⟩
  intro i
  exact degree_comap_eq_of_component_range G D A hinj hrange i

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The original selected-component hypotheses furnish its literal host
cyclic index and indexed NEW-to-degree lower bound, with all original size
bounds. The choice and coloring are arbitrary. -/
theorem selected_component_cyclic_index
    {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) :
    3 ≤ D.supp.ncard ∧
    k + 1 ≤ 2 * D.supp.ncard ∧
    D.supp.ncard ≤ k - 1 ∧
    ∃ A : Fin D.supp.ncard → Fin n,
      Function.Injective A ∧
      (∀ x : D, ∃ i : Fin D.supp.ncard, A i = x.val) ∧
      Set.range A = D.supp ∧
      cycleGraph D.supp.ncard ≤ (selectedGraph χ r).comap A ∧
      (∀ i : Fin D.supp.ncard,
        ((selectedGraph χ r).comap A).degree i = (selectedGraph χ r).degree (A i)) ∧
      ∀ i : Fin D.supp.ncard,
        (newColors χ (A i)).card ≤ ((selectedGraph χ r).comap A).degree i := by
  obtain ⟨h3, hlower, hupper, ⟨c⟩, _⟩ :=
    selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew hpair hno D
  obtain ⟨A, hinj, honto, hrange, hcycle, hdegree⟩ :=
    spanning_component_copy_host_index (selectedGraph χ r) D c
  refine ⟨h3, hlower, hupper, A, hinj, honto, hrange, hcycle, hdegree, ?_⟩
  intro i
  rw [hdegree i]
  exact newChoice_degree_ge_newColors χ r (A i)

/-- Two distinct actual selected components yield two whole-support cyclic
host maps. Every cross-index vertex pair is distinct, so the original NEW
pair bound gives the full indexed cross-degree bound without an added degree,
surjectivity, component-disjointness or cyclic-order premise. -/
theorem distinct_components_cyclic_indices_cross_degree
    {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D E : (selectedGraph χ r).ConnectedComponent) (hDE : D ≠ E) :
    3 ≤ D.supp.ncard ∧ D.supp.ncard ≤ k - 1 ∧
    k + 1 ≤ 2 * D.supp.ncard ∧
    3 ≤ E.supp.ncard ∧ E.supp.ncard ≤ k - 1 ∧
    k + 1 ≤ 2 * E.supp.ncard ∧
    ∃ (A : Fin D.supp.ncard → Fin n) (B : Fin E.supp.ncard → Fin n),
      Function.Injective A ∧ Function.Injective B ∧
      (∀ x : D, ∃ i : Fin D.supp.ncard, A i = x.val) ∧
      (∀ y : E, ∃ j : Fin E.supp.ncard, B j = y.val) ∧
      Set.range A = D.supp ∧ Set.range B = E.supp ∧
      cycleGraph D.supp.ncard ≤ (selectedGraph χ r).comap A ∧
      cycleGraph E.supp.ncard ≤ (selectedGraph χ r).comap B ∧
      (∀ i : Fin D.supp.ncard,
        ((selectedGraph χ r).comap A).degree i = (selectedGraph χ r).degree (A i)) ∧
      (∀ j : Fin E.supp.ncard,
        ((selectedGraph χ r).comap B).degree j = (selectedGraph χ r).degree (B j)) ∧
      (∀ i : Fin D.supp.ncard, ∀ j : Fin E.supp.ncard, A i ≠ B j) ∧
      ∀ i : Fin D.supp.ncard, ∀ j : Fin E.supp.ncard,
        k - 1 ≤ ((selectedGraph χ r).comap A).degree i +
          ((selectedGraph χ r).comap B).degree j := by
  obtain ⟨h3A, hlowerA, hupperA, A, hinjA, hontoA, hrangeA, hcycleA, hdegreeA,
      hnewdegreeA⟩ := selected_component_cyclic_index hk χ r hnew hpair hno D
  obtain ⟨h3B, hlowerB, hupperB, B, hinjB, hontoB, hrangeB, hcycleB, hdegreeB,
      hnewdegreeB⟩ := selected_component_cyclic_index hk χ r hnew hpair hno E
  have hdistinct : ∀ i : Fin D.supp.ncard, ∀ j : Fin E.supp.ncard, A i ≠ B j := by
    intro i j hij
    have hi : A i ∈ D.supp := by
      rw [← hrangeA]
      exact ⟨i, rfl⟩
    have hj : B j ∈ E.supp := by
      rw [← hrangeB]
      exact ⟨j, rfl⟩
    exact hDE (SimpleGraph.ConnectedComponent.eq_of_common_vertex hi (hij.symm ▸ hj))
  have hcross : ∀ i : Fin D.supp.ncard, ∀ j : Fin E.supp.ncard,
      k - 1 ≤ ((selectedGraph χ r).comap A).degree i +
        ((selectedGraph χ r).comap B).degree j := by
    intro i j
    have hsum := hpair (A i) (B j) (hdistinct i j)
    have hi := hnewdegreeA i
    have hj := hnewdegreeB j
    omega
  exact ⟨h3A, hupperA, hlowerA, h3B, hupperB, hlowerB,
    A, B, hinjA, hinjB, hontoA, hontoB, hrangeA, hrangeB,
    hcycleA, hcycleB, hdegreeA, hdegreeB, hdistinct, hcross⟩

end ErdosProblems.AntiRamseyCycleComponentCyclicIndex

namespace ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleSelectedComponentOrder
open ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian
open ErdosProblems.AntiRamseyCycleComponentHamiltonianNonbridge
open ErdosProblems.AntiRamseyCycleCrossComponentPaletteExclusion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Under the original high-NEW and distinct-pair bounds, every original host
edge between distinct whole selected components has color outside the full
NEW union. The valid choice and the original color type are arbitrary. -/
theorem cross_edge_color_not_new_union {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (A B : (selectedGraph χ r).ConnectedComponent) (hAB : A ≠ B)
    (u v : Fin n) (hu : u ∈ A.supp) (hv : v ∈ B.supp)
    (e : HostEdge n) (he : e.val = s(u, v)) :
    χ e ∉ newColorUnion χ := by
  classical
  have hupper : ∀ r' : NewChoice χ,
      ∀ D : (selectedGraph χ r').ConnectedComponent, D.supp.ncard ≤ k - 1 := by
    intro r' D
    exact selected_component_order_le_original hk χ r' hnew hpair hno D
  have hcycles : ∀ D : (selectedGraph χ r).ConnectedComponent,
      ∃ (x : D) (c : D.toSimpleGraph.Walk x x), c.IsHamiltonianCycle := by
    intro D
    obtain ⟨_, _, _, _, hcycle⟩ :=
      selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew hpair hno D
    exact hcycle
  have hnb : ∀ c : newColorUnion χ,
      ¬ (selectedGraph χ r).IsBridge (r.edge c).val := by
    intro c
    apply not_isBridge_of_component_hamiltonian_cycles (selectedGraph χ r) hcycles
    rw [selectedGraph_edgeSet χ r]
    exact ⟨c, rfl⟩
  have hAlower : k + 1 ≤ 2 * A.supp.ncard :=
    (selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew hpair hno A).2.1
  have hBlower : k + 1 ≤ 2 * B.supp.ncard :=
    (selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew hpair hno B).2.1
  have hlarge : k + 1 ≤ A.supp.ncard + B.supp.ncard := by omega
  have hdisjoint : Disjoint A.supp B.supp :=
    (selectedGraph χ r).pairwise_disjoint_supp_connectedComponent hAB
  exact cross_edge_color_not_new_union_of_nonbridge χ r hnb hupper A B
    hdisjoint hlarge u v hu hv e he

end ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion

namespace ErdosProblems.AntiRamseyCycleOriginalCrossComponentConstancy

open SimpleGraph
open scoped Classical Fin.CommRing
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleCyclicCrossMatrixTranslations
open ErdosProblems.AntiRamseyAdjacentMatrixTranslations
open ErdosProblems.AntiRamseyChordPathWindow
open ErdosProblems.AntiRamseyEvenCheckerboardDegree
open ErdosProblems.AntiRamseyEvenChordRotation
open ErdosProblems.AntiRamseyCycleComponentCyclicIndex
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem cross_matrix_forms
    {k a b : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a ∧ a ≤ k - 1)
    (hb : 3 ≤ b ∧ b ≤ k - 1) (hsum : k + 1 ≤ a + b)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : cycleGraph a ≤ (selectedGraph χ r).comap A)
    (hBcycle : cycleGraph b ≤ (selectedGraph χ r).comap B)
    (hpalette : ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) ∉ newColorUnion χ)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    let M := liftedCrossColor χ A B (by omega) (by omega) hdisjoint
    (∀ i j : ℤ, M i j = M ((i + j) % 2) 0) ∧
      ((¬ Even a ∨ ¬ Even b ∨ ¬ Even k) → ∀ i j : ℤ, M i j = M 0 0) := by
  let : NeZero a := ⟨by omega⟩
  let : NeZero b := ⟨by omega⟩
  have hAsucc (i : Fin a) :
      (selectedGraph χ r).Adj (A i) (A (cyclicSuccessor (by omega) i)) := by
    apply hAcycle
    rw [cycleGraph_adj']
    right
    change ((i + 1) - i).val = 1
    rw [add_sub_cancel_left, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < a)]
  have hBsucc (j : Fin b) :
      (selectedGraph χ r).Adj (B j) (B (cyclicSuccessor (by omega) j)) := by
    apply hBcycle
    rw [cycleGraph_adj']
    right
    change ((j + 1) - j).val = 1
    rw [add_sub_cancel_left, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < b)]
  have hnone : ¬ ∃ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
    rintro ⟨f, hf⟩
    exact hno f hf
  let L : ℕ := max 2 (k - b)
  let d : ℤ := (L : ℤ) - 1
  let e : ℤ := (k : ℤ) - L - 1
  let M := liftedCrossColor χ A B (by omega) (by omega) hdisjoint
  have htrans := cyclic_cross_matrix_has_adjacent_translations hk ha hb hsum
    χ r A B hA hB hdisjoint hAsucc hBsucc hpalette hnone
  change ∀ i j : ℤ,
    M i j = M (i + d) (j + e) ∧
    M i j = M (i + d + 1) (j + e - 1) ∧
    M i j = M (i + d) (j - e) ∧
    M i j = M (i + d + 1) (j - e + 1) at htrans
  have hde (i j : ℤ) : M i j = M (i + d) (j + e) := (htrans i j).1
  have hnext (i j : ℤ) : M i j = M (i + (d + 1)) (j + (e - 1)) := by
    simpa only [add_assoc, add_sub_assoc] using (htrans i j).2.1
  have hreverse (i j : ℤ) : M i j = M (i + d) (j + (-e)) := by
    simpa only [sub_eq_add_neg] using (htrans i j).2.2.1
  have hreverseNext (i j : ℤ) :
      M i j = M (i + (d + 1)) (j + (-e + 1)) := by
    simpa only [sub_eq_add_neg, add_assoc] using (htrans i j).2.2.2
  obtain ⟨hpa, hpb⟩ := liftedCrossColor_periodic χ A B (by omega) (by omega) hdisjoint
  have hsumInt : d + e = (k : ℤ) - 2 := by dsimp only [d, e]; omega
  constructor
  · exact parity_normal_form_of_adjacent_translations M d e
      hde hnext hreverse hreverseNext
  · intro hodd
    exact constant_of_not_all_even_of_adjacent_translations M d e
      hde hnext hreverse hreverseNext a b k
      (fun i j => (hpa i j).symm) (fun i j => (hpb i j).symm) hsumInt hodd

theorem constant_of_first_same_parity_chord
    {k a b : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a ∧ a ≤ k - 1)
    (hb : 3 ≤ b ∧ b ≤ k - 1) (hsum : k + 1 ≤ a + b)
    (hkEven : Even k) (haEven : Even a) (hbEven : Even b)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : cycleGraph a ≤ (selectedGraph χ r).comap A)
    (hBcycle : cycleGraph b ≤ (selectedGraph χ r).comap B)
    (hpalette : ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) ∉ newColorUnion χ)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (x y : Fin a) (hxy : ((selectedGraph χ r).comap A).Adj x y)
    (hparity : x.val % 2 = y.val % 2) :
    ∃ c : C, ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) = c := by
  let : NeZero a := ⟨by omega⟩
  let : NeZero b := ⟨by omega⟩
  obtain ⟨hrotInj, _hrotZero, _hrotLast, hdEven, hd2, hdad, hchord, hrotCycle⟩ :=
    normalized_even_chord_rotation ha.1 haEven ((selectedGraph χ r).comap A)
      x y hxy hparity
  let rot := cyclicRotation x
  let A' : Fin a → Fin n := fun i => A (rot i)
  let d : ℕ := (chordOffset x y).val
  have hA' : Function.Injective A' := hA.comp hrotInj
  have hdisjoint' : Disjoint (Set.range A') (Set.range B) := by
    apply Set.disjoint_range_iff.mpr
    intro i j
    exact Set.disjoint_range_iff.mp hdisjoint (rot i) j
  have hAcycle' : cycleGraph a ≤ (selectedGraph χ r).comap A' := by
    intro i j hij
    exact hAcycle ((hrotCycle i j).mpr hij)
  have hpalette' (i : Fin a) (j : Fin b) :
      χ (cyclicCrossEdge A' B hdisjoint' i j) ∉ newColorUnion χ := by
    change χ (cyclicCrossEdge A B hdisjoint (rot i) j) ∉ newColorUnion χ
    exact hpalette (rot i) j
  let M := liftedCrossColor χ A' B (by omega) (by omega) hdisjoint'
  have hform : ∀ i j : ℤ, M i j = M ((i + j) % 2) 0 :=
    (cross_matrix_forms hk ha hb hsum χ r A' B hA' hB hdisjoint'
      hAcycle' hBcycle hpalette' hno).1
  have hlift (i : Fin a) (j : Fin b) :
      M (i.val : ℤ) (j.val : ℤ) = χ (cyclicCrossEdge A' B hdisjoint' i j) := by
    simp only [M, liftedCrossColor, Int.cast_natCast, Fin.cast_val_eq_self]
  have hkmod := Nat.even_iff.mp hkEven
  have hbmod := Nat.even_iff.mp hbEven
  have hbStrict : b ≤ k - 2 := by omega
  let L : ℕ := k - b + 1
  let T : ℕ := b - 1
  have hL2 : 2 ≤ L := by dsimp only [L]; omega
  have hT2 : 2 ≤ T := by dsimp only [T]; omega
  have hLa : L ≤ a := by dsimp only [L]; omega
  have hTb : T ≤ b := by dsimp only [T]; omega
  have hcount : L + T = k := by dsimp only [L, T]; omega
  have hLmod : (L : ℤ) % 2 = 1 := by dsimp only [L]; omega
  have hTmod : ((T - 1 : ℕ) : ℤ) % 2 = 0 := by dsimp only [T]; omega
  have hconsecutive (i j : Fin a) (hij : i.val + 1 = j.val) :
      ((selectedGraph χ r).comap A').Adj i j := by
    apply hAcycle'
    apply pathGraph_le_cycleGraph
    exact pathGraph_adj.mpr (Or.inl hij)
  have hchord' : ((selectedGraph χ r).comap A').Adj
      (⟨0, by omega⟩ : Fin a) (⟨d, by have hdlt := (chordOffset x y).isLt; omega⟩ : Fin a) := by
    exact hchord
  let P : Fin L → Fin n := fun i => A' (windowOrder d hdad hLa i)
  let J : Fin T → Fin b := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hTb⟩
  let Q : Fin T → Fin n := fun j => B (J j)
  have hP : Function.Injective P := hA'.comp (windowOrder_injective d hdad hLa)
  have hJ : Function.Injective J := by
    intro i j hij
    exact Fin.ext (congrArg (fun j : Fin b => j.val) hij)
  have hQ : Function.Injective Q := hB.comp hJ
  have hPQ : Disjoint (Set.range P) (Set.range Q) := by
    apply Set.disjoint_range_iff.mpr
    intro i j
    exact Set.disjoint_range_iff.mp hdisjoint' (windowOrder d hdad hLa i) (J j)
  have hPpath : ∀ i j : Fin L, i.val + 1 = j.val →
      (selectedGraph χ r).Adj (P i) (P j) :=
    windowOrder_ordered_adj ((selectedGraph χ r).comap A') d hd2 hdad hLa
      hconsecutive hchord'
  have hQpath (i j : Fin T) (hij : i.val + 1 = j.val) :
      (selectedGraph χ r).Adj (Q i) (Q j) := by
    apply hBcycle
    apply pathGraph_le_cycleGraph
    exact pathGraph_adj.mpr (Or.inl hij)
  let p0 : Fin a := windowOrder d hdad hLa ⟨0, by omega⟩
  let p1 : Fin a := windowOrder d hdad hLa ⟨L - 1, by omega⟩
  let q0 : Fin b := J ⟨0, by omega⟩
  let q1 : Fin b := J ⟨T - 1, by omega⟩
  let between := cyclicCrossEdge A' B hdisjoint' p1 q0
  let closing := cyclicCrossEdge A' B hdisjoint' p0 q1
  have hbetween : between.val = s(P ⟨L - 1, by omega⟩, Q ⟨0, by omega⟩) := rfl
  have hclosing : closing.val = s(P ⟨0, by omega⟩, Q ⟨T - 1, by omega⟩) := rfl
  have hcolorsEq : χ between = χ closing := by
    by_contra hdifferent
    have hresult :=
      ErdosProblems.AntiRamseyTwoSelectedPathsRainbow.two_disjoint_selected_paths_close_rainbow
        χ r hL2 hT2 P Q hP hQ hPQ hPpath hQpath between closing
        hbetween hclosing (hpalette' p1 q0) (hpalette' p0 q1) hdifferent
    have hresultk : ∃ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
        IsRainbow f.toHom χ := hcount ▸ hresult
    obtain ⟨f, hf⟩ := hresultk
    exact hno f hf
  have hpSum : ((p1.val : ℤ) + (p0.val : ℤ)) % 2 = 1 :=
    (window_endpoint_sum_emod_two hd2 hdad hL2 hLa hdEven).trans hLmod
  have hq0 : q0.val = 0 := rfl
  have hq1 : q1.val = T - 1 := rfl
  have hparityNe : ((p1.val : ℤ) + (q0.val : ℤ)) % 2 ≠
      ((p0.val : ℤ) + (q1.val : ℤ)) % 2 := by
    rw [hq0, hq1]
    omega
  have hbetweenForm : χ between = M (((p1.val : ℤ) + (q0.val : ℤ)) % 2) 0 :=
    (hlift p1 q0).symm.trans (hform _ _)
  have hclosingForm : χ closing = M (((p0.val : ℤ) + (q1.val : ℤ)) % 2) 0 :=
    (hlift p0 q1).symm.trans (hform _ _)
  have h01 : M 0 0 = M 1 0 := by
    have hp := Int.emod_two_eq_zero_or_one ((p1.val : ℤ) + (q0.val : ℤ))
    have hq := Int.emod_two_eq_zero_or_one ((p0.val : ℤ) + (q1.val : ℤ))
    rw [hbetweenForm, hclosingForm] at hcolorsEq
    rcases hp with hp | hp
    · have hq1 : ((p0.val : ℤ) + (q1.val : ℤ)) % 2 = 1 := by omega
      simpa only [hp, hq1] using hcolorsEq
    · have hq0 : ((p0.val : ℤ) + (q1.val : ℤ)) % 2 = 0 := by omega
      simpa only [hp, hq0] using hcolorsEq.symm
  have hconstant (i j : ℤ) : M i j = M 0 0 := by
    have hf := hform i j
    rcases Int.emod_two_eq_zero_or_one (i + j) with hzero | hone
    · simpa only [hzero] using hf
    · have hf1 : M i j = M 1 0 := by simpa only [hone] using hf
      exact hf1.trans h01.symm
  refine ⟨M 0 0, ?_⟩
  intro i j
  let i' : Fin a := i - x
  have hrot : rot i' = i := add_sub_cancel x i
  have hedge : cyclicCrossEdge A B hdisjoint i j =
      cyclicCrossEdge A' B hdisjoint' i' j := by
    apply Subtype.ext
    change s(A i, B j) = s(A (rot i'), B j)
    rw [hrot]
  rw [hedge]
  exact (hlift i' j).symm.trans (hconstant _ _)

theorem cross_colors_constant_of_indexed_bounds
    {k a b : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a ∧ a ≤ k - 1)
    (hb : 3 ≤ b ∧ b ≤ k - 1) (hsum : k + 1 ≤ a + b)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (A : Fin a → Fin n) (B : Fin b → Fin n)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hdisjoint : Disjoint (Set.range A) (Set.range B))
    (hAcycle : cycleGraph a ≤ (selectedGraph χ r).comap A)
    (hBcycle : cycleGraph b ≤ (selectedGraph χ r).comap B)
    (hpalette : ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) ∉ newColorUnion χ)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (hpair : ∀ i j, k - 1 ≤ ((selectedGraph χ r).comap A).degree i +
      ((selectedGraph χ r).comap B).degree j) :
    ∃ c : C, ∀ i j, χ (cyclicCrossEdge A B hdisjoint i j) = c := by
  let : NeZero a := ⟨by omega⟩
  let : NeZero b := ⟨by omega⟩
  by_cases hodd : ¬ Even a ∨ ¬ Even b ∨ ¬ Even k
  · let M := liftedCrossColor χ A B (by omega) (by omega) hdisjoint
    have hconstant : ∀ i j : ℤ, M i j = M 0 0 :=
      (cross_matrix_forms hk ha hb hsum χ r A B hA hB hdisjoint
        hAcycle hBcycle hpalette hno).2 hodd
    refine ⟨M 0 0, ?_⟩
    intro i j
    have h := hconstant (i.val : ℤ) (j.val : ℤ)
    simpa only [M, liftedCrossColor, Int.cast_natCast, Fin.cast_val_eq_self] using h
  · have haEven : Even a := by
      by_contra h
      exact hodd (Or.inl h)
    have hbEven : Even b := by
      by_contra h
      exact hodd (Or.inr (Or.inl h))
    have hkEven : Even k := by
      by_contra h
      exact hodd (Or.inr (Or.inr h))
    rcases exists_same_parity_edge_of_cross_degree_sum hk hkEven
        ha.1 haEven ha.2 hb.1 hbEven hb.2
        ((selectedGraph χ r).comap A) ((selectedGraph χ r).comap B) (by
          intro i j
          exact Eq.mp
            (congrArg₂ (fun da db : ℕ => k - 1 ≤ da + db)
              (congrArg
                (fun inst : Fintype (((selectedGraph χ r).comap A).neighborSet i) =>
                  @SimpleGraph.degree _ ((selectedGraph χ r).comap A) i inst)
                (Subsingleton.elim _ _))
              (congrArg
                (fun inst : Fintype (((selectedGraph χ r).comap B).neighborSet j) =>
                  @SimpleGraph.degree _ ((selectedGraph χ r).comap B) j inst)
                (Subsingleton.elim _ _)))
            (hpair i j)) with
      ⟨x, y, hxy, hparity⟩ | ⟨x, y, hxy, hparity⟩
    · exact constant_of_first_same_parity_chord hk ha hb hsum hkEven haEven hbEven
        χ r A B hA hB hdisjoint hAcycle hBcycle hpalette hno x y hxy hparity
    · have hdisjointBA := hdisjoint.symm
      have hedge (i : Fin b) (j : Fin a) :
          cyclicCrossEdge B A hdisjointBA i j = cyclicCrossEdge A B hdisjoint j i := by
        apply Subtype.ext
        exact Sym2.eq_swap
      have hpaletteBA (i : Fin b) (j : Fin a) :
          χ (cyclicCrossEdge B A hdisjointBA i j) ∉ newColorUnion χ := by
        rw [hedge]
        exact hpalette j i
      obtain ⟨c, hc⟩ := constant_of_first_same_parity_chord hk hb ha (by omega)
        hkEven hbEven haEven χ r B A hB hA hdisjointBA hBcycle hAcycle
        hpaletteBA hno x y hxy hparity
      refine ⟨c, ?_⟩
      intro i j
      exact (congrArg χ (hedge j i)).symm.trans (hc j i)

/-- Original high-NEW assumptions force one original host color on every
edge between two distinct WHOLE selected components, for every valid choice.
No cyclic order, palette, degree, chord or joined-rainbow premise is added. -/
theorem cross_component_colors_constant
    {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D E : (selectedGraph χ r).ConnectedComponent) (hDE : D ≠ E) :
    ∃ c : C, ∀ u v : Fin n, u ∈ D.supp → v ∈ E.supp →
      ∀ e : HostEdge n, e.val = s(u, v) → χ e = c := by
  obtain ⟨ha, haUpper, haLower, hb, hbUpper, hbLower,
      A, B, hA, hB, hontoA, hontoB, hrangeA, hrangeB,
      hcycleA, hcycleB, _hdegreeA, _hdegreeB, hdistinct, hcross⟩ :=
    distinct_components_cyclic_indices_cross_degree hk χ r hnew hpair hno D E hDE
  have hdisjoint : Disjoint (Set.range A) (Set.range B) :=
    Set.disjoint_range_iff.mpr hdistinct
  have hAmem (i) : A i ∈ D.supp := by
    rw [← hrangeA]
    exact ⟨i, rfl⟩
  have hBmem (j) : B j ∈ E.supp := by
    rw [← hrangeB]
    exact ⟨j, rfl⟩
  have hpalette (i j) : χ (cyclicCrossEdge A B hdisjoint i j) ∉ newColorUnion χ :=
    cross_edge_color_not_new_union hk χ r hnew hpair hno D E hDE
      (A i) (B j) (hAmem i) (hBmem j) (cyclicCrossEdge A B hdisjoint i j) rfl
  obtain ⟨c, hc⟩ := cross_colors_constant_of_indexed_bounds hk
    ⟨ha, haUpper⟩ ⟨hb, hbUpper⟩ (by omega) χ r A B hA hB hdisjoint
    hcycleA hcycleB hpalette hno hcross
  refine ⟨c, ?_⟩
  intro u v hu hv e he
  obtain ⟨i, hi⟩ := hontoA ⟨u, hu⟩
  obtain ⟨j, hj⟩ := hontoB ⟨v, hv⟩
  have hedge : e = cyclicCrossEdge A B hdisjoint i j := by
    apply Subtype.ext
    change e.val = s(A i, B j)
    rw [hi, hj]
    exact he
  rw [hedge]
  exact hc i j

end ErdosProblems.AntiRamseyCycleOriginalCrossComponentConstancy

namespace ErdosProblems.AntiRamseyCycleOriginalThreeComponentTriangle

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleComponentCyclicIndex
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentConstancy
open ErdosProblems.AntiRamseyCycleQuotientTriangleSplice

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The original high-NEW hypotheses exclude three pairwise distinct
original host labels on a triangle in three distinct whole SAME-r selected
components. This is the literal raw triangle input of the component quotient. -/
theorem no_three_component_rainbow_triangle
    {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (u v w : Fin n) (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u)
    (hUV : (selectedGraph χ r).connectedComponentMk u ≠
      (selectedGraph χ r).connectedComponentMk v)
    (hVW : (selectedGraph χ r).connectedComponentMk v ≠
      (selectedGraph χ r).connectedComponentMk w)
    (hWU : (selectedGraph χ r).connectedComponentMk w ≠
      (selectedGraph χ r).connectedComponentMk u) :
    ¬ (χ.get u v huv ≠ χ.get v w hvw ∧
      χ.get v w hvw ≠ χ.get w u hwu ∧
      χ.get w u hwu ≠ χ.get u v huv) := by
  let DA := (selectedGraph χ r).connectedComponentMk u
  let DB := (selectedGraph χ r).connectedComponentMk v
  let DD := (selectedGraph χ r).connectedComponentMk w
  have hu : u ∈ DA.supp := ConnectedComponent.connectedComponentMk_mem
  have hv : v ∈ DB.supp := ConnectedComponent.connectedComponentMk_mem
  have hw : w ∈ DD.supp := ConnectedComponent.connectedComponentMk_mem
  obtain ⟨α, hα⟩ := cross_component_colors_constant hk χ r hnew hpair hno DA DB hUV
  obtain ⟨β, hβ⟩ := cross_component_colors_constant hk χ r hnew hpair hno DB DD hVW
  obtain ⟨γ, hγ⟩ := cross_component_colors_constant hk χ r hnew hpair hno DD DA hWU
  have hgetUV : χ.get u v huv = α := hα u v hu hv ⟨s(u, v), huv⟩ rfl
  have hgetVW : χ.get v w hvw = β := hβ v w hv hw ⟨s(v, w), hvw⟩ rfl
  have hgetWU : χ.get w u hwu = γ := hγ w u hw hu ⟨s(w, u), hwu⟩ rfl
  have hαOutside : α ∉ newColorUnion χ := by
    rw [← hgetUV]
    exact cross_edge_color_not_new_union hk χ r hnew hpair hno DA DB hUV
      u v hu hv ⟨s(u, v), huv⟩ rfl
  have hβOutside : β ∉ newColorUnion χ := by
    rw [← hgetVW]
    exact cross_edge_color_not_new_union hk χ r hnew hpair hno DB DD hVW
      v w hv hw ⟨s(v, w), hvw⟩ rfl
  have hγOutside : γ ∉ newColorUnion χ := by
    rw [← hgetWU]
    exact cross_edge_color_not_new_union hk χ r hnew hpair hno DD DA hWU
      w u hw hu ⟨s(w, u), hwu⟩ rfl
  obtain ⟨ha, haLower, haUpper, A, hA, _hontoA, hAspan, hAcycle, _hdegreeA,
      _hnewDegreeA⟩ := selected_component_cyclic_index hk χ r hnew hpair hno DA
  obtain ⟨hb, hbLower, hbUpper, B, hB, _hontoB, hBspan, hBcycle, _hdegreeB,
      _hnewDegreeB⟩ := selected_component_cyclic_index hk χ r hnew hpair hno DB
  obtain ⟨hc, hcLower, hcUpper, D, hD, _hontoD, hDspan, hDcycle, _hdegreeD,
      _hnewDegreeD⟩ := selected_component_cyclic_index hk χ r hnew hpair hno DD
  have hrepeat := three_components_cross_labels_repeat χ r hk ha hb hc
    haLower hbLower hcLower haUpper hbUpper hcUpper DA DB DD hUV hVW hWU
    A B D hA hB hD hAspan hBspan hDspan
    (fun i j hij => hAcycle hij) (fun i j hij => hBcycle hij)
    (fun i j hij => hDcycle hij) α β γ
    (fun x y e hx hy he => hα x y hx hy e he)
    (fun x y e hx hy he => hβ x y hx hy e he)
    (fun x y e hx hy he => hγ x y hx hy e he)
    hαOutside hβOutside hγOutside hno
  rintro ⟨hUVcolor, hVWcolor, hWUcolor⟩
  rcases hrepeat with hαβ | hβγ | hγα
  · exact hUVcolor (hgetUV.trans (hαβ.trans hgetVW.symm))
  · exact hVWcolor (hgetVW.trans (hβγ.trans hgetWU.symm))
  · exact hWUcolor (hgetWU.trans (hγα.trans hgetUV.symm))

end ErdosProblems.AntiRamseyCycleOriginalThreeComponentTriangle

namespace ErdosProblems.AntiRamseyCycleOriginalHighNewStructure

open SimpleGraph Asymptotics Filter
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleSelectedComponentOrder
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentConstancy
open ErdosProblems.AntiRamseyCycleOriginalThreeComponentTriangle
open ErdosProblems.AntiRamseyCycleComponentQuotient
open ErdosProblems.AntiRamseyConditionalCycleUpper
open ErdosProblems.AntiRamseyConditionalAsymptotic
open ErdosProblems.AntiRamseyCycleFourHighNewStructure
open ErdosProblems.AntiRamseyTriangle

/-- Unconditional proof of `HighNewWeakStructure k` for every `k ≥ 5` by
combining the selected-component order bound (` ≤ k - 1`), cross-component
monochromaticity, and 3-component rainbow-triangle exclusion. -/
theorem highNewWeakStructure_of_five_le {k : ℕ} (hk : 5 ≤ k) :
    HighNewWeakStructure k := by
  intro n q hn χ hno hnew hpair
  let r : NewChoice χ := canonicalChoice χ
  apply weak_structure_of_component_conditions (selectedGraph χ r) (by omega) χ
  · intro D
    exact selected_component_order_le_original hk χ r hnew hpair hno D
  · intro D E hDE a d ha hd had a' d' ha' hd' had'
    obtain ⟨c, hc⟩ := cross_component_colors_constant hk χ r hnew hpair hno D E hDE
    have hfirst : χ.get a d had = c := hc a d ha hd ⟨s(a, d), had⟩ rfl
    have hsecond : χ.get a' d' had' = c := hc a' d' ha' hd' ⟨s(a', d'), had'⟩ rfl
    exact hfirst.trans hsecond.symm
  · intro a d c had hdc hca hAD hDC hCA
    exact no_three_component_rainbow_triangle hk χ r hnew hpair hno
      a d c had hdc hca hAD hDC hCA

/-- Unconditional weak-block decomposition `HighNewWeakStructure k` for every `k ≥ 4`. -/
theorem highNewWeakStructure_of_four_le {k : ℕ} (hk : 4 ≤ k) :
    HighNewWeakStructure k := by
  by_cases hfour : k = 4
  · subst k
    exact highNewWeakStructure_four
  · exact highNewWeakStructure_of_five_le (by omega)

/-- Unconditional linear upper bound for `antiRamseyNum (cycleGraph k) n` across
all cycle orders `k ≥ 3` and host orders `n ≥ k`. -/
theorem cycle_linear_upper (k n : ℕ) (hk : 3 ≤ k) (hn : k ≤ n) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≤
      ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n - 1 := by
  by_cases h3 : k = 3
  · subst k
    rw [antiRamseyNum_cycleGraph_three n hn, Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  · have hk4 : 4 ≤ k := by omega
    simpa only [cycleSlope] using
      antiRamseyNum_le_cycle_linear k n hk4 (by omega : k - 1 ≤ n)
        (highNewWeakStructure_of_four_le hk4)

/-- Complete unconditional proof of Part (i) of Erdős Problem 1105 for all `k ≥ 3`. -/
theorem cycle_asymptotic_all :
    ∀ k, 3 ≤ k →
      ((fun n : ℕ => (antiRamseyNum (cycleGraph k) n : ℝ) -
        ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
        =O[atTop] (fun _ => (1 : ℝ))) :=
  cycle_asymptotic_all_of_highNewWeakStructure (fun _ hk => highNewWeakStructure_of_four_le hk)

end ErdosProblems.AntiRamseyCycleOriginalHighNewStructure
