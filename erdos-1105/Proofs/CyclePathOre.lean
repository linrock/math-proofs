module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Tactic

@[expose] public section

/-!
Ore's elementary path-endpoint closure in the exact non-induced
`cycleGraph (s+1).Copy` semantics. This is graph-only: color incidence
and Choi's later rainbow host cycle are separate.
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
