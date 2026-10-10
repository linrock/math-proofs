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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Sym.Sym2
public import CycleRepresentativeExchange

@[expose] public section

/-!
# CycleBlockAndTriangleBounds

Ordered `(k - 1)`-clique block lower bounds (`cycle_fullBlock_lower`, `cycle_real_lower`), Gallai's triangle theorem (`antiRamseyNum_triangle`), 4-cycle triangle quotients, and conditional weak-block cycle upper bounds for Erdős Problem 1105.
-/

namespace ErdosProblems.AntiRamseyCycleBlockCount

/-- A complete block of `m` vertices contributes `m.choose 2 + 1` colors
per `m` vertices at the cycle coefficient. -/
theorem full_block_coefficient (m : ℕ) (hm : 2 ≤ m) :
    (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (m : ℝ) =
      (((m.choose 2 : ℕ) : ℝ) + 1) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  rw [Nat.cast_choose_two ℝ m]
  field_simp [ne_of_gt hmpos]

/-- The full blocks alone have the required cycle slope with a uniform
constant error for fixed `m`; any partial-block colors can only improve this
lower estimate. -/
theorem full_blocks_real_lower (m n : ℕ) (hm : 2 ≤ m) (_hn : m ≤ n) :
    (((n / m : ℕ) : ℝ) * ((m.choose 2 : ℕ) : ℝ) + ((n / m : ℕ) : ℝ) - 1) ≥
      (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (n : ℝ) -
        (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (m : ℝ) - 1 := by
  let q : ℕ := n / m
  let A : ℝ := ((m : ℝ) - 1) / 2 + 1 / (m : ℝ)
  have hmpos : 0 < m := by omega
  have hA : 0 ≤ A := by
    dsimp [A]
    apply add_nonneg
    · apply div_nonneg
      · have hmreal : (1 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (by omega : 1 ≤ m)
        linarith
      · norm_num
    · exact le_of_lt (one_div_pos.mpr (by exact_mod_cast hmpos))
  have hqbound : n ≤ m * q + m := by
    have hmod := Nat.mod_lt n hmpos
    have hdecomp := Nat.mod_add_div n m
    dsimp [q]
    omega
  have hreal : (n : ℝ) ≤ (m : ℝ) * (q : ℝ) + (m : ℝ) := by
    exact_mod_cast hqbound
  have hprod := mul_le_mul_of_nonneg_left hreal hA
  have hcoeff : A * (m : ℝ) = (((m.choose 2 : ℕ) : ℝ) + 1) := by
    dsimp [A]
    exact full_block_coefficient m hm
  have hformula :
      (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 =
        A * (m : ℝ) * (q : ℝ) - 1 := by
    rw [hcoeff]
    ring
  change (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 ≥
    A * (n : ℝ) - A * (m : ℝ) - 1
  rw [hformula]
  nlinarith [hprod]

/-- Substitute `m = k - 1` into the literal real coefficient of
`erdos_1105.parts.i`. -/
theorem cycle_coefficient_eq_block_coefficient (k : ℕ) (hk : 3 ≤ k) :
    (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) =
      ((((k - 1 : ℕ) : ℝ) - 1) / 2 + 1 / ((k - 1 : ℕ) : ℝ)) := by
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [hcast]
  ring

end ErdosProblems.AntiRamseyCycleBlockCount

namespace ErdosProblems.AntiRamseyCycle

variable {V : Type*}

/-- The edge joins vertices on opposite sides of the Boolean cut. -/
def crossesCut (q : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun u v => decide (q u ≠ q v), by
    intro u v
    simp [ne_comm]⟩

@[simp] theorem crossesCut_mk (q : V → Bool) (u v : V) :
    crossesCut q s(u, v) = decide (q u ≠ q v) := by
  simp [crossesCut]

/-- A walk crosses a Boolean cut an even number of times precisely when its
endpoints have the same Boolean label. -/
theorem even_crossesCut_iff {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : V → Bool) :
    Even (p.edges.countP (crossesCut q)) ↔ q u = q v := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    rw [SimpleGraph.Walk.edges_cons, List.countP_cons]
    simp only [crossesCut_mk]
    cases hu : q u <;> cases hv : q v <;> cases hw : q w <;>
      simp_all [Nat.even_add_one]

/-- A walk that reaches a vertex on the other side of the cut must cross it. -/
theorem exists_crossing_of_mem_support_ne {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : V → Bool) (hw : w ∈ p.support) (hwu : q w ≠ q u) :
    ∃ e ∈ p.edges, crossesCut q e = true := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
    exact (hwu (hw ▸ rfl)).elim
  | @cons u v z huv p ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    by_cases huvq : q u = q v
    · rcases hw with rfl | hw
      · exact (hwu rfl).elim
      · obtain ⟨e, he, hcross⟩ := ih hw (by simpa [huvq] using hwu)
        exact ⟨e, by simp [SimpleGraph.Walk.edges_cons, he], hcross⟩
    · exact ⟨s(u, v), by simp [SimpleGraph.Walk.edges_cons], by simp [huvq]⟩

/-- A nonconstant Boolean label on the support of a closed walk forces at
least two cut-crossing edge occurrences. -/
theorem two_le_crossings_of_closed_walk {G : SimpleGraph V} {u w : V}
    (p : G.Walk u u) (q : V → Bool) (hw : w ∈ p.support) (hwu : q w ≠ q u) :
    2 ≤ p.edges.countP (crossesCut q) := by
  obtain ⟨e, he, hcross⟩ := exists_crossing_of_mem_support_ne p q hw hwu
  have hpos : 0 < p.edges.countP (crossesCut q) :=
    List.countP_pos_iff.mpr ⟨e, he, hcross⟩
  have heven : Even (p.edges.countP (crossesCut q)) :=
    (even_crossesCut_iff p q).2 rfl
  obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp heven
  omega

theorem two_distinct_of_countP_two {α : Type*} {p : α → Bool}
    (l : List α) (hl : l.Nodup) (hcount : 2 ≤ l.countP p) :
    ∃ a ∈ l, ∃ b ∈ l, a ≠ b ∧ p a = true ∧ p b = true := by
  induction l with
  | nil => simp at hcount
  | cons a l ih =>
    have hnd := List.nodup_cons.mp hl
    by_cases ha : p a = true
    · have htail : 0 < l.countP p := by
        simp [ha] at hcount
        exact List.countP_pos_iff.mpr hcount
      obtain ⟨b, hb, hpb⟩ := List.countP_pos_iff.mp htail
      exact ⟨a, by simp, b, by simp [hb],
        fun hab => hnd.1 (hab ▸ hb), ha, hpb⟩
    · have htail : 2 ≤ l.countP p := by
        simp [ha] at hcount
        exact hcount
      obtain ⟨x, hx, y, hy, hxy, hpx, hpy⟩ := ih hnd.2 htail
      exact ⟨x, by simp [hx], y, by simp [hy], hxy, hpx, hpy⟩

/-- A simple closed cycle meets a nontrivial Boolean cut at two distinct edges. -/
theorem exists_two_distinct_crossing_edges_of_cycle {G : SimpleGraph V} {u w : V}
    (p : G.Walk u u) (hp : p.IsCycle) (q : V → Bool)
    (hw : w ∈ p.support) (hwu : q w ≠ q u) :
    ∃ e₁ ∈ p.edges, ∃ e₂ ∈ p.edges,
      e₁ ≠ e₂ ∧ crossesCut q e₁ = true ∧ crossesCut q e₂ = true := by
  exact two_distinct_of_countP_two p.edges hp.1.1.edges_nodup
    (two_le_crossings_of_closed_walk p q hw hwu)

/-- A simple cycle meeting both cut classes cannot have pairwise distinct
edge colors when every cut-crossing edge has one fixed color. -/
theorem not_injOn_cycle_edges_of_constant_cut_color {G : SimpleGraph V}
    {C : Type*} {u w : V} (p : G.Walk u u) (hp : p.IsCycle)
    (q : V → Bool) (hw : w ∈ p.support) (hwu : q w ≠ q u)
    (c : Sym2 V → C) (c₀ : C)
    (hconst : ∀ e ∈ p.edges, crossesCut q e = true → c e = c₀) :
    ¬ Set.InjOn c {e | e ∈ p.edges} := by
  obtain ⟨e₁, he₁, e₂, he₂, hne, hcross₁, hcross₂⟩ :=
    exists_two_distinct_crossing_edges_of_cycle p hp q hw hwu
  intro hinj
  apply hne
  exact hinj he₁ he₂ (by rw [hconst e₁ he₁ hcross₁, hconst e₂ he₂ hcross₂])

/-- An ordered-block edge coloring. Internal edges have their own color;
crossing edges have the color of their earlier block. -/
def orderedBlockColor {B : Type*} [LinearOrder B] [DecidableEq B]
    (π : V → B) : Sym2 V → Sum (Sym2 V) B :=
  Sym2.lift ⟨fun x y =>
    if π x = π y then Sum.inl s(x, y) else Sum.inr (min (π x) (π y)), by
      intro x y
      by_cases hxy : π x = π y
      · simp [hxy, Sym2.eq_swap]
      · simp [hxy, eq_comm, min_comm]⟩

@[simp] theorem orderedBlockColor_mk {B : Type*} [LinearOrder B] [DecidableEq B]
    (π : V → B) (x y : V) :
    orderedBlockColor π s(x, y) =
      if π x = π y then Sum.inl s(x, y) else Sum.inr (min (π x) (π y)) := by
  simp [orderedBlockColor]

/-- A cycle spanning ordered blocks is not rainbow under `orderedBlockColor`:
the two boundary edges of its least block have the same block tag. -/
theorem not_injOn_cycle_edges_orderedBlockColor {G : SimpleGraph V}
    {B : Type*} [LinearOrder B] [DecidableEq B] {u w : V}
    (p : G.Walk u u) (hp : p.IsCycle) (π : V → B)
    (hmin : ∀ x ∈ p.support, π u ≤ π x)
    (hw : w ∈ p.support) (hneq : π w ≠ π u) :
    ¬ Set.InjOn (orderedBlockColor π) {e | e ∈ p.edges} := by
  let q : V → Bool := fun x => decide (π x = π u)
  have hwu : q w ≠ q u := by simp [q, hneq]
  apply not_injOn_cycle_edges_of_constant_cut_color p hp q hw hwu
    (orderedBlockColor π) (Sum.inr (π u))
  intro e he hcross
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hx : π u ≤ π x := hmin x (p.fst_mem_support_of_mem_edges he)
    have hy : π u ≤ π y := hmin y (p.snd_mem_support_of_mem_edges he)
    simp only [crossesCut_mk] at hcross
    by_cases hxu : π x = π u
    · by_cases hyu : π y = π u
      · simp [q, hxu, hyu] at hcross

      · have hxy : π x ≠ π y := by
          rw [hxu]
          exact ne_comm.mp hyu
        rw [orderedBlockColor_mk, ite_eq_right hxy]
        simp [hxu, min_eq_left hy]
    · by_cases hyu : π y = π u
      · have hxy : π x ≠ π y := by
          rw [hyu]
          exact hxu
        rw [orderedBlockColor_mk, ite_eq_right hxy]
        simp [hyu, min_eq_right hx]
      · simp [q, hxu, hyu] at hcross

/-- Every cycle that visits two different ordered blocks has repeated colors
under `orderedBlockColor`, regardless of where the walk starts. -/
theorem not_injOn_cycle_edges_of_spanning_blocks {G : SimpleGraph V}
    {B : Type*} [LinearOrder B] [DecidableEq B] [DecidableEq V]
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) (π : V → B)
    (hspan : ∃ x ∈ p.support, ∃ y ∈ p.support, π x ≠ π y) :
    ¬ Set.InjOn (orderedBlockColor π) {e | e ∈ p.edges} := by
  have hsup : p.support.toFinset.Nonempty := by
    simp [Finset.nonempty_iff_ne_empty]
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image p.support.toFinset π hsup
  have ha' : a ∈ p.support := List.mem_toFinset.mp ha
  have hmin' : ∀ x ∈ p.support, π a ≤ π x := by
    intro x hx
    exact hmin x (List.mem_toFinset.mpr hx)
  obtain ⟨x, hx, y, hy, hxy⟩ := hspan
  have hw : ∃ w ∈ p.support, π w ≠ π a := by
    by_contra h
    push Not at h
    have hxa : π x = π a := h x hx
    have hya : π y = π a := h y hy
    exact hxy (hxa.trans hya.symm)
  obtain ⟨w, hwp, hwa⟩ := hw
  let p' := p.rotate a ha'
  have hp' : p'.IsCycle := hp.rotate ha'
  have hminp' : ∀ x ∈ p'.support, π a ≤ π x := by
    intro x hx
    exact hmin' x ((p.mem_support_rotate_iff a ha').mp hx)
  have hwp' : w ∈ p'.support := (p.mem_support_rotate_iff a ha').mpr hwp
  have hcore := not_injOn_cycle_edges_orderedBlockColor p' hp' π hminp' hwp' hwa
  intro hinj
  apply hcore
  intro e₁ he₁ e₂ he₂ hcolor
  apply hinj
  · exact (p.rotate_edges a ha').mem_iff.mp he₁
  · exact (p.rotate_edges a ha').mem_iff.mp he₂
  · exact hcolor

end ErdosProblems.AntiRamseyCycle

namespace ErdosProblems.AntiRamseyCycle

open SimpleGraph

/-- A simple cycle is not contained in a block smaller than its length. -/
theorem cycle_spans_blocks_of_small_fibers {n t : ℕ} {u : Fin n}
    (p : (⊤ : SimpleGraph (Fin n)).Walk u u) (hp : p.IsCycle)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < p.length) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, π x ≠ π y := by
  classical
  by_contra hspan
  have hconst : ∀ x ∈ p.support, π x = π u := by
    intro x hx
    by_contra hne
    apply hspan
    exact ⟨u, p.start_mem_support, x, hx, Ne.symm hne⟩
  have hsubset : p.support.tail.toFinset ⊆
      Finset.univ.filter (fun x : Fin n => π x = π u) := by
    intro x hx
    have hx' : x ∈ p.support.tail := List.mem_toFinset.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hconst x ((p.mem_support_iff).mpr (Or.inr hx'))⟩
  have hlen : p.support.tail.length = p.length := by
    have h := p.length_support
    rw [← p.cons_tail_support] at h
    simp only [List.length_cons] at h
    omega
  have hcard : p.support.tail.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, hlen]
  have hle := Finset.card_le_card hsubset
  rw [hcard] at hle
  exact (Nat.not_le_of_gt (hsmall (π u))) hle

/-- Injective source-edge pullback forces the raw host coloring to be injective
on all edges of the mapped walk. -/
theorem injOn_mapped_walk_edges_of_injective_pullback
    {V W C : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    {u : V} (f : H →g G) (p : H.Walk u u)
    (c : Sym2 W → C)
    (hinj : Function.Injective
      (fun e : H.edgeSet => c (f.mapEdgeSet e).val)) :
    Set.InjOn c {e | e ∈ (p.map f).edges} := by
  intro e₁ he₁ e₂ he₂ hcolor
  simp only [Walk.edges_map, List.mem_map] at he₁ he₂
  obtain ⟨a, ha, rfl⟩ := he₁
  obtain ⟨b, hb, rfl⟩ := he₂
  let ea : H.edgeSet := ⟨a, p.edges_subset_edgeSet ha⟩
  let eb : H.edgeSet := ⟨b, p.edges_subset_edgeSet hb⟩
  have hpull : c (f.mapEdgeSet ea).val = c (f.mapEdgeSet eb).val := by
    simpa [ea, eb, Hom.mapEdgeSet] using hcolor
  have hab : ea = eb := hinj hpull
  have hab' : a = b := congrArg Subtype.val hab
  simp [hab']

/-- The raw ordered-block coloring pulled back along a copy of `C_k` cannot be
injective when every block contains fewer than `k` vertices. -/
theorem not_injective_raw_orderedBlockColor_pullback
    {k n t : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < k)
    (f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n))) :
    ¬ Function.Injective
      (fun e : (cycleGraph k).edgeSet =>
        orderedBlockColor π (f.toHom.mapEdgeSet e).val) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  let p₀ : (cycleGraph (m + 3)).Walk 0 0 := cycleGraph.cycle m
  let p : (⊤ : SimpleGraph (Fin n)).Walk (f 0) (f 0) := p₀.map f.toHom
  have hp : p.IsCycle :=
    (Walk.isCycle_map_iff_of_injective f.injective).mpr cycleGraph.isCycle_cycle
  have hlen : p.length = m + 3 := by simp [p, p₀]
  have hsmall' : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < p.length := by
    intro b
    simpa [hlen] using hsmall b
  have hspan := cycle_spans_blocks_of_small_fibers p hp π hsmall'
  intro hinj
  have hinjOn : Set.InjOn (orderedBlockColor π) {e | e ∈ p.edges} := by
    simpa [p] using
      (injOn_mapped_walk_edges_of_injective_pullback f.toHom p₀
        (orderedBlockColor π) hinj)
  exact (not_injOn_cycle_edges_of_spanning_blocks p hp π hspan) hinjOn

end ErdosProblems.AntiRamseyCycle

namespace ErdosProblems.AntiRamseyCycle

open SimpleGraph

/-- The raw ordered-block color of a complete-graph edge. -/
def rawOrderedBlockLabeling {n t : ℕ} (π : Fin n → Fin t) :
    TopEdgeLabeling (Fin n) (Sum (Sym2 (Fin n)) (Fin t)) :=
  fun e => orderedBlockColor π e.val

/-- Every copied cycle visits two blocks and repeats a raw color when each
block has fewer vertices than the cycle. -/
theorem rawOrderedBlockLabeling_noRainbow_copy
    {k n t : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < k) :
    ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom (rawOrderedBlockLabeling π) := by
  intro f hf
  apply not_injective_raw_orderedBlockColor_pullback hk hn π hsmall f
  exact hf

end ErdosProblems.AntiRamseyCycle

namespace ErdosProblems.AntiRamseyCycleBlockCount

/-- Consecutive blocks of nominal size `m`, indexed by vertex division. -/
def consecutiveBlockMap (m n : ℕ) : Fin n → Fin (n / m + 1) :=
  fun x => ⟨x.val / m, Nat.lt_succ_of_le
    (Nat.div_le_div_right (Nat.le_of_lt x.isLt))⟩

@[simp] theorem consecutiveBlockMap_val (m n : ℕ) (x : Fin n) :
    (consecutiveBlockMap m n x).val = x.val / m := rfl

/-- Every fiber of the consecutive-block map has at most `m` vertices.
The residue modulo `m` injects each fiber into `Fin m`. -/
theorem consecutiveBlockMap_fiber_card_le (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m + 1)) :
    (Finset.univ.filter (fun x : Fin n => consecutiveBlockMap m n x = b)).card ≤ m := by
  classical
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun x : Fin n => consecutiveBlockMap m n x = b)
  let f : S → Fin m := fun x => ⟨x.val.val % m, Nat.mod_lt _ hm⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Fin.ext
    have hx : consecutiveBlockMap m n x.val = b :=
      (Finset.mem_filter.mp x.property).2
    have hy : consecutiveBlockMap m n y.val = b :=
      (Finset.mem_filter.mp y.property).2
    have hquot : x.val.val / m = y.val.val / m := by
      simpa only [consecutiveBlockMap_val] using
        congrArg Fin.val (hx.trans hy.symm)
    have hmod : x.val.val % m = y.val.val % m := congrArg Fin.val hxy
    have hdecompx := Nat.mod_add_div x.val.val m
    have hdecompy := Nat.mod_add_div y.val.val m
    rw [hmod, hquot] at hdecompx
    omega
  have hcard : Fintype.card S ≤ Fintype.card (Fin m) :=
    Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

/-- With `m = k - 1`, every block is strictly smaller than a `k`-cycle. -/
theorem cycleBlockMap_small_fibers (k n : ℕ) (hk : 3 ≤ k) :
    ∀ b : Fin (n / (k - 1) + 1),
      (Finset.univ.filter
        (fun x : Fin n => consecutiveBlockMap (k - 1) n x = b)).card < k := by
  intro b
  have hm : 0 < k - 1 := by omega
  have hcard := consecutiveBlockMap_fiber_card_le (k - 1) n hm b
  omega

end ErdosProblems.AntiRamseyCycleBlockCount

namespace ErdosProblems.AntiRamseyCycleBlockCount

open SimpleGraph

/-- Vertex `i` of complete block `b`, indexed in the host `Fin n`. -/
def fullBlockVertex (m n : ℕ) (_hm : 0 < m)
    (b : Fin (n / m)) (i : Fin m) : Fin n := by
  have hb : (b.val + 1) * m ≤ (n / m) * m :=
    Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr b.isLt)
  have hb' : m + m * b.val ≤ (n / m) * m := by
    calc
      m + m * b.val = (b.val + 1) * m := by ring
      _ ≤ (n / m) * m := hb
  have hq : (n / m) * m ≤ n := Nat.div_mul_le_self n m
  exact ⟨i.val + m * b.val,
    lt_of_lt_of_le (Nat.add_lt_add_right i.isLt (m * b.val)) (hb'.trans hq)⟩

@[simp] theorem fullBlockVertex_val (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (i : Fin m) :
    (fullBlockVertex m n hm b i).val = i.val + m * b.val := rfl

/-- Every indexed full-block vertex maps back to its block under division. -/
theorem fullBlockVertex_block (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (i : Fin m) :
    consecutiveBlockMap m n (fullBlockVertex m n hm b i) =
      Fin.castLE (Nat.le_succ _) b := by
  apply Fin.ext
  simp only [consecutiveBlockMap_val, Fin.val_castLE, fullBlockVertex_val]
  rw [Nat.add_mul_div_left _ _ hm]
  simp [Nat.div_eq_of_lt i.isLt]

/-- The full-block coordinate pair is recoverable from its host vertex. -/
theorem fullBlockVertex_injective (m n : ℕ) (hm : 0 < m) :
    Function.Injective (fun p : Fin (n / m) × Fin m =>
      fullBlockVertex m n hm p.1 p.2) := by
  intro p q hpq
  have hb : p.1 = q.1 := by
    have hπ := congrArg (consecutiveBlockMap m n) hpq
    rw [fullBlockVertex_block, fullBlockVertex_block] at hπ
    exact Fin.castLE_injective (Nat.le_succ _) hπ
  have hi : p.2 = q.2 := by
    have hval := congrArg Fin.val hpq
    simp only [fullBlockVertex_val] at hval
    rw [hb] at hval
    exact Fin.ext (Nat.add_right_cancel hval)
  exact Prod.ext hb hi

/-- The full block `b` forms a copy of `K_m` in the host `K_n`. -/
def fullBlockCopy (m n : ℕ) (hm : 0 < m) (b : Fin (n / m)) :
    (⊤ : SimpleGraph (Fin m)).Copy (⊤ : SimpleGraph (Fin n)) := by
  let f : Fin m ↪ Fin n :=
    ⟨fullBlockVertex m n hm b, by
      intro i j h
      have hval := congrArg Fin.val h
      simp only [fullBlockVertex_val] at hval
      exact Fin.ext (Nat.add_right_cancel hval)⟩
  exact (SimpleGraph.Embedding.completeGraph f).toCopy

@[simp] theorem fullBlockCopy_apply (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (i : Fin m) :
    fullBlockCopy m n hm b i = fullBlockVertex m n hm b i := rfl

end ErdosProblems.AntiRamseyCycleBlockCount

namespace ErdosProblems.AntiRamseyTriangle

open Finset SimpleGraph

/-- Every triangle in a complete edge labeling has a repeated color. -/
def NoRainbowTriangle {V C : Type*} (χ : SimpleGraph.TopEdgeLabeling V C) : Prop :=
  ∀ (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a),
    χ.get a b hab = χ.get b c hbc ∨
      χ.get b c hbc = χ.get c a hca ∨
      χ.get c a hca = χ.get a b hab

theorem get_comm {V C : Type*} (χ : SimpleGraph.TopEdgeLabeling V C)
    (a b : V) (hab : a ≠ b) : χ.get a b hab = χ.get b a hab.symm := by
  simpa using (SimpleGraph.EdgeLabeling.get_comm (C := χ) b a hab)

theorem cross_color_of_distinct_radials {V C : Type*}
    (χ : SimpleGraph.TopEdgeLabeling V C) (hχ : NoRainbowTriangle χ)
    (x a b : V) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b)
    (hdiff : χ.get x a hxa ≠ χ.get x b hxb) :
    χ.get a b hab = χ.get x a hxa ∨ χ.get a b hab = χ.get x b hxb := by
  obtain h | h | h := hχ x a b hxa hab hxb.symm
  · exact Or.inl h.symm
  · exact Or.inr (h.trans (get_comm χ b x hxb.symm))
  · exact False.elim (hdiff (h.symm.trans (get_comm χ b x hxb.symm)))

/-- Colors occurring on edges whose endpoints lie in `S`. -/
def edgeColors {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (χ : SimpleGraph.TopEdgeLabeling V C) (S : Finset V) : Finset C :=
  ((Finset.univ : Finset (⊤ : SimpleGraph V).edgeSet).filter
    (fun e => e.val.toFinset ⊆ S)).image χ

theorem mem_edgeColors_iff {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (χ : SimpleGraph.TopEdgeLabeling V C) (S : Finset V) (c : C) :
    c ∈ edgeColors χ S ↔
      ∃ a ∈ S, ∃ b ∈ S, ∃ hab : a ≠ b, χ.get a b hab = c := by
  constructor
  · intro hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨_, hsub⟩ := Finset.mem_filter.mp he
    rcases e with ⟨e, hedge⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : a ≠ b := by simpa using hedge
      have ha : a ∈ S := hsub (by simp [Sym2.toFinset_mk_eq])
      have hb : b ∈ S := hsub (by simp [Sym2.toFinset_mk_eq])
      exact ⟨a, ha, b, hb, hab, rfl⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    let e : (⊤ : SimpleGraph V).edgeSet := ⟨s(a, b), by simpa using hab⟩
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    simp only [e, Sym2.toFinset_mk_eq]
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb

def radialColor {V C : Type*} [DecidableEq V]
    (χ : SimpleGraph.TopEdgeLabeling V C) (x : V) (fallback : C) (y : V) : C :=
  if h : x ≠ y then χ.get x y h else fallback

theorem radialColor_eq {V C : Type*} [DecidableEq V]
    (χ : SimpleGraph.TopEdgeLabeling V C) (x : V) (fallback : C)
    (y : V) (h : x ≠ y) : radialColor χ x fallback y = χ.get x y h := by
  simp [radialColor, h]

theorem image_card_add_sum_fiber_sub_one_eq {V C : Type*} [DecidableEq C]
    (T : Finset V) (f : V → C) :
    (T.image f).card +
      ∑ c ∈ T.image f, ((T.filter fun y => f y = c).card - 1) = T.card := by
  let I : Finset C := T.image f
  let F : C → Finset V := fun c => T.filter fun y => f y = c
  have hpos : ∀ c ∈ I, 1 ≤ (F c).card := by
    intro c hc
    have hc' : (F c).card ≠ 0 := by
      simpa [I, F] using (Finset.fiber_card_ne_zero_iff_mem_image T f c).2 hc
    omega
  have hsum : ∑ c ∈ I, ((F c).card - 1) =
      (∑ c ∈ I, (F c).card) - I.card := by
    simpa using (Finset.sum_tsub_distrib I
      (f := fun c => (F c).card) (g := fun _ => 1) hpos)
  have hcard : ∑ c ∈ I, (F c).card = T.card := by
    simpa [I, F] using (Finset.card_eq_sum_card_image f T).symm
  have hle : I.card ≤ T.card := by
    simpa [I] using (Finset.card_image_le (s := T) (f := f))
  change I.card + ∑ c ∈ I, ((F c).card - 1) = T.card
  rw [hsum, hcard]
  omega

theorem gallai_color_bound_on {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (χ : SimpleGraph.TopEdgeLabeling V C) (hχ : NoRainbowTriangle χ)
    (S : Finset V) : (edgeColors χ S).card ≤ S.card - 1 := by
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hS : S = ∅
  · subst S
    have hcolors : edgeColors χ (∅ : Finset V) = ∅ := by
      ext c
      simp [mem_edgeColors_iff]
    simp [hcolors]
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  let T : Finset V := S.erase x
  by_cases hT : T = ∅
  · have hcolors : edgeColors χ S = ∅ := by
      ext c
      constructor
      · intro hc
        obtain ⟨a, ha, b, hb, hab, _⟩ := (mem_edgeColors_iff χ S c).mp hc
        have hax : a = x := by
          by_contra hne
          have : a ∈ T := Finset.mem_erase.mpr ⟨hne, ha⟩
          simp [hT] at this
        have hbx : b = x := by
          by_contra hne
          have : b ∈ T := Finset.mem_erase.mpr ⟨hne, hb⟩
          simp [hT] at this
        exact (hab (hax.trans hbx.symm)).elim
      · simp
    have hScard : S.card = 1 := by
      have hc := Finset.card_erase_of_mem hx
      change T.card = S.card - 1 at hc
      rw [hT] at hc
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
      simp at hc
      omega
    simp [hcolors, hScard]
  obtain ⟨y₀, hy₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  have hxy₀ : x ≠ y₀ := (Finset.ne_of_mem_erase hy₀).symm
  let fallback : C := χ.get x y₀ hxy₀
  let f : V → C := radialColor χ x fallback
  let I : Finset C := T.image f
  let F : C → Finset V := fun c => T.filter (fun y => f y = c)
  have hsub : edgeColors χ S ⊆
      I ∪ I.biUnion (fun c => edgeColors χ (F c)) := by
    intro c hc
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := (mem_edgeColors_iff χ S c).mp hc
    by_cases hax : a = x
    · subst a
      have hbT : b ∈ T := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨b, hbT, by simp [f, radialColor_eq χ x fallback b hab]⟩
    by_cases hbx : b = x
    · subst b
      have haT : a ∈ T := Finset.mem_erase.mpr ⟨hax, ha⟩
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨a, haT, by
        simp [f, radialColor_eq χ x fallback a hab.symm]
        exact (get_comm χ a x hab).symm⟩
    have haT : a ∈ T := Finset.mem_erase.mpr ⟨hax, ha⟩
    have hbT : b ∈ T := Finset.mem_erase.mpr ⟨hbx, hb⟩
    by_cases hsame : f a = f b
    · apply Finset.mem_union_right
      have hk : f a ∈ I := Finset.mem_image.mpr ⟨a, haT, rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨f a, hk, ?_⟩
      apply (mem_edgeColors_iff χ (F (f a)) _).mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨haT, rfl⟩,
        b, Finset.mem_filter.mpr ⟨hbT, hsame.symm⟩, hab, rfl⟩
    · have hxa : x ≠ a := hax ∘ Eq.symm
      have hxb : x ≠ b := hbx ∘ Eq.symm
      have hdiff : χ.get x a hxa ≠ χ.get x b hxb := by
        simpa [f, radialColor_eq χ x fallback a hxa,
          radialColor_eq χ x fallback b hxb] using hsame
      obtain hleft | hright := cross_color_of_distinct_radials χ hχ x a b hxa hxb hab hdiff
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨a, haT, by
          simpa [f, radialColor_eq χ x fallback a hxa] using hleft.symm⟩
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨b, hbT, by
          simpa [f, radialColor_eq χ x fallback b hxb] using hright.symm⟩
  have hcolor_card : (edgeColors χ S).card ≤
      I.card + ∑ c ∈ I, (edgeColors χ (F c)).card := by
    calc
      (edgeColors χ S).card ≤ (I ∪ I.biUnion (fun c => edgeColors χ (F c))).card :=
        Finset.card_le_card hsub
      _ ≤ I.card + (I.biUnion (fun c => edgeColors χ (F c))).card := Finset.card_union_le _ _
      _ ≤ I.card + ∑ c ∈ I, (edgeColors χ (F c)).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
  have hih : ∀ c ∈ I, (edgeColors χ (F c)).card ≤ (F c).card - 1 := by
    intro c _
    have hFsub : F c ⊂ S :=
      lt_of_le_of_lt (Finset.filter_subset _ _) (Finset.erase_ssubset hx)
    exact ih (F c) hFsub
  have hsum : ∑ c ∈ I, (edgeColors χ (F c)).card ≤
      ∑ c ∈ I, ((F c).card - 1) := Finset.sum_le_sum hih
  have hfiber : I.card + ∑ c ∈ I, ((F c).card - 1) = T.card := by
    simpa [I, F] using image_card_add_sum_fiber_sub_one_eq T f
  have hTcard : T.card = S.card - 1 := Finset.card_erase_of_mem hx
  calc
    (edgeColors χ S).card ≤ I.card + ∑ c ∈ I, (edgeColors χ (F c)).card := hcolor_card
    _ ≤ I.card + ∑ c ∈ I, ((F c).card - 1) := Nat.add_le_add_left hsum _
    _ = S.card - 1 := by rw [hfiber, hTcard]

/-- A complete edge coloring without a rainbow triangle uses at most `|V| - 1` colors.
This also covers the empty and singleton vertex types. -/
theorem gallai_color_bound {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
    (χ : SimpleGraph.TopEdgeLabeling V C) (hχ : NoRainbowTriangle χ) :
    (Finset.univ.image χ).card ≤ Fintype.card V - 1 := by
  have hcolors : edgeColors χ (Finset.univ : Finset V) = Finset.univ.image χ := by
    simp [edgeColors]
  simpa [hcolors] using gallai_color_bound_on χ hχ (Finset.univ : Finset V)

end ErdosProblems.AntiRamseyTriangle

namespace ErdosProblems.AntiRamseyWeakCount

open Finset SimpleGraph
open ErdosProblems.AntiRamseyTriangle

/-- The vertices in one class of a finite block map. -/
def blockFiber {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (b : V → Fin t) (i : Fin t) : Finset V :=
  Finset.univ.filter fun v => b v = i

theorem edgeColors_card_le_choose {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (χ : TopEdgeLabeling V C) (S : Finset V) :
    (edgeColors χ S).card ≤ S.card.choose 2 := by
  let E : Finset (⊤ : SimpleGraph V).edgeSet :=
    (Finset.univ : Finset (⊤ : SimpleGraph V).edgeSet).filter
      (fun e => e.val.toFinset ⊆ S)
  have hEsub : E.image Subtype.val ⊆
      ((⊤ : SimpleGraph V).edgeFinset.filter fun e => e.toFinset ⊆ S) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, he'S⟩ := Finset.mem_filter.mp he'
    exact Finset.mem_filter.mpr ⟨by simpa using e'.property, he'S⟩
  have hEcard : E.card = (E.image Subtype.val).card :=
    (Finset.card_image_of_injective E Subtype.coe_injective).symm
  calc
    (edgeColors χ S).card = (E.image χ).card := rfl
    _ ≤ E.card := Finset.card_image_le
    _ ≤ ((⊤ : SimpleGraph V).edgeFinset.filter fun e => e.toFinset ⊆ S).card := by
      rw [hEcard]
      exact Finset.card_le_card hEsub
    _ = ((⊤ : SimpleGraph V).induce (↑S : Set V)).edgeFinset.card :=
      (⊤ : SimpleGraph V).card_filter_edgeFinset_toFinset_subset S
    _ ≤ S.card.choose 2 := by
      simpa [Fintype.card_subtype] using
        ((⊤ : SimpleGraph V).induce (↑S : Set V)).card_edgeFinset_le_card_choose_two

/-- An edge coloring with monochromatic pairs of blocks and at most two cross colors
on every triple of blocks uses at most the possible internal edges plus `t - 1` colors.
The quotient coloring `ψ` assigns the color of each pair of distinct blocks;
`NoRainbowTriangle ψ` is precisely the triple condition. Empty fibers are allowed. -/
theorem realized_colors_le_block_edges_add {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    {t : ℕ} (χ : TopEdgeLabeling V C) (b : V → Fin t)
    (ψ : TopEdgeLabeling (Fin t) C)
    (hcross : ∀ (a d : V) (had : a ≠ d) (hbd : b a ≠ b d),
      χ.get a d had = ψ.get (b a) (b d) hbd)
    (htriple : NoRainbowTriangle ψ) :
    (Finset.univ.image χ).card ≤
      (∑ i : Fin t, (blockFiber b i).card.choose 2) + (t - 1) := by
  let Q : Finset C := Finset.univ.image ψ
  let I : Fin t → Finset C := fun i => edgeColors χ (blockFiber b i)
  have hcover : edgeColors χ (Finset.univ : Finset V) ⊆
      Q ∪ Finset.univ.biUnion I := by
    intro c hc
    obtain ⟨a, _, d, _, had, hcolor⟩ :=
      (mem_edgeColors_iff χ (Finset.univ : Finset V) c).mp hc
    by_cases hbd : b a = b d
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨b a, Finset.mem_univ _, ?_⟩
      apply (mem_edgeColors_iff χ (blockFiber b (b a)) c).mpr
      exact ⟨a, by simp [blockFiber], d, by simp [blockFiber, hbd], had, hcolor⟩
    · apply Finset.mem_union_left
      let e : (⊤ : SimpleGraph (Fin t)).edgeSet :=
        ⟨s(b a, b d), by simpa using hbd⟩
      have hq : ψ.get (b a) (b d) hbd ∈ Q := by
        exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
      rw [← hcolor, hcross a d had hbd]
      exact hq
  have hinternal : ∀ i : Fin t, (I i).card ≤ (blockFiber b i).card.choose 2 := by
    intro i
    exact edgeColors_card_le_choose χ (blockFiber b i)
  have hQ : Q.card ≤ t - 1 := by
    simpa [Q] using gallai_color_bound ψ htriple
  have hall : edgeColors χ (Finset.univ : Finset V) = Finset.univ.image χ := by
    simp [edgeColors]
  calc
    (Finset.univ.image χ).card = (edgeColors χ (Finset.univ : Finset V)).card := by
      rw [hall]
    _ ≤ (Q ∪ Finset.univ.biUnion I).card := Finset.card_le_card hcover
    _ ≤ Q.card + (Finset.univ.biUnion I).card := Finset.card_union_le _ _
    _ ≤ Q.card + ∑ i : Fin t, (I i).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (t - 1) + ∑ i : Fin t, (blockFiber b i).card.choose 2 :=
      Nat.add_le_add hQ (Finset.sum_le_sum fun i _ => hinternal i)
    _ = (∑ i : Fin t, (blockFiber b i).card.choose 2) + (t - 1) :=
      Nat.add_comm _ _

end ErdosProblems.AntiRamseyWeakCount

namespace ErdosProblems.AntiRamseyCycleComponentQuotient

open SimpleGraph Finset
open ErdosProblems.AntiRamseyWeakCount
open ErdosProblems.AntiRamseyTriangle

variable {n k : ℕ} {C : Type*} [DecidableEq C]

/-- Whole components become the exact weak-block witnesses when their sizes
and the original host's cross-component color conditions are supplied.
The graph G is arbitrary and need not be a canonical representative graph. -/
theorem weak_structure_of_component_conditions
    (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (χ : TopEdgeLabeling (Fin n) C)
    (hupper : ∀ D : G.ConnectedComponent, D.supp.ncard ≤ k - 1)
    (hcross : ∀ (D E : G.ConnectedComponent) (_hDE : D ≠ E)
      (a d : Fin n) (_ha : a ∈ D.supp) (_hd : d ∈ E.supp) (had : a ≠ d)
      (a' d' : Fin n) (_ha' : a' ∈ D.supp) (_hd' : d' ∈ E.supp)
      (had' : a' ≠ d'), χ.get a d had = χ.get a' d' had')
    (hrawTriangle : ∀ (a d c : Fin n)
      (had : a ≠ d) (hdc : d ≠ c) (hca : c ≠ a)
      (_hAD : G.connectedComponentMk a ≠ G.connectedComponentMk d)
      (_hDC : G.connectedComponentMk d ≠ G.connectedComponentMk c)
      (_hCA : G.connectedComponentMk c ≠ G.connectedComponentMk a),
      ¬ (χ.get a d had ≠ χ.get d c hdc ∧
        χ.get d c hdc ≠ χ.get c a hca ∧
        χ.get c a hca ≠ χ.get a d had)) :
    ∃ (t : ℕ) (b : Fin n → Fin t) (ψ : TopEdgeLabeling (Fin t) C),
      1 ≤ t ∧
      (∀ (a d : Fin n) (had : a ≠ d) (hbd : b a ≠ b d),
        χ.get a d had = ψ.get (b a) (b d) hbd) ∧
      NoRainbowTriangle ψ ∧
      (∀ i : Fin t, 1 ≤ (blockFiber b i).card) ∧
      (∀ i : Fin t, (blockFiber b i).card ≤ k - 1) ∧
      (∑ i : Fin t, (blockFiber b i).card = n) := by
  classical
  let t : ℕ := Fintype.card G.ConnectedComponent
  let e : G.ConnectedComponent ≃ Fin t := Fintype.equivFin G.ConnectedComponent
  let b : Fin n → Fin t := fun v => e (G.connectedComponentMk v)
  let z : Fin n := ⟨0, hn⟩
  have htpos : 0 < t := by
    dsimp [t]
    exact Finset.card_pos.mpr ⟨G.connectedComponentMk z, Finset.mem_univ _⟩
  have ht : 1 ≤ t := by omega
  have hfiber (i : Fin t) : blockFiber b i = (e.symm i).supp.toFinset := by
    ext v
    simpa [blockFiber, b, ConnectedComponent.mem_supp_iff] using
      (e.eq_symm_apply (x := i) (y := G.connectedComponentMk v)).symm
  have hsupper (i : Fin t) : (blockFiber b i).card ≤ k - 1 := by
    calc
      (blockFiber b i).card = (e.symm i).supp.toFinset.card :=
        congrArg Finset.card (hfiber i)
      _ = (e.symm i).supp.ncard :=
        (Set.ncard_eq_toFinset_card' (e.symm i).supp).symm
      _ ≤ k - 1 := hupper (e.symm i)
  have hnonempty : ∀ i : Fin t, ∃ a : Fin n, b a = i := by
    intro i
    obtain ⟨a, ha⟩ := (e.symm i).nonempty_supp
    have hcomp : G.connectedComponentMk a = e.symm i :=
      (ConnectedComponent.mem_supp_iff (e.symm i) a).mp ha
    refine ⟨a, ?_⟩
    change e (G.connectedComponentMk a) = i
    rw [hcomp]
    exact e.apply_symm_apply i
  have hspos (i : Fin t) : 1 ≤ (blockFiber b i).card := by
    obtain ⟨a, ha⟩ := hnonempty i
    have hm : a ∈ blockFiber b i := by simp [blockFiber, ha]
    have hpos : 0 < (blockFiber b i).card := Finset.card_pos.mpr ⟨a, hm⟩
    omega
  choose rep hrep using hnonempty
  have hinj : Function.Injective rep := by
    intro i j heq
    calc
      i = b (rep i) := (hrep i).symm
      _ = b (rep j) := congrArg b heq
      _ = j := hrep j
  let emb : Fin t ↪ Fin n := ⟨rep, hinj⟩
  let ψ : TopEdgeLabeling (Fin t) C := TopEdgeLabeling.pullback χ emb
  have hpull : ∀ (i j : Fin t) (hij : i ≠ j),
      ψ.get i j hij = χ.get (rep i) (rep j) (hinj.ne hij) := by
    intro i j hij
    simp [ψ, emb, TopEdgeLabeling.pullback, EdgeLabeling.get,
      EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk]
  have hcompne (i j : Fin t) (hij : i ≠ j) :
      G.connectedComponentMk (rep i) ≠ G.connectedComponentMk (rep j) := by
    intro hcomp
    apply hij
    calc
      i = b (rep i) := (hrep i).symm
      _ = b (rep j) := congrArg e hcomp
      _ = j := hrep j
  have hcrosslabel : ∀ (a d : Fin n) (had : a ≠ d)
      (hbd : b a ≠ b d),
      χ.get a d had = ψ.get (b a) (b d) hbd := by
    intro a d had hbd
    have hDE : G.connectedComponentMk a ≠ G.connectedComponentMk d := by
      intro hcomp
      exact hbd (congrArg e hcomp)
    have hrepA : rep (b a) ∈ (G.connectedComponentMk a).supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact e.injective (hrep (b a))
    have hrepD : rep (b d) ∈ (G.connectedComponentMk d).supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact e.injective (hrep (b d))
    have hrepne : rep (b a) ≠ rep (b d) := hinj.ne hbd
    have hconst := hcross (G.connectedComponentMk a) (G.connectedComponentMk d)
      hDE a d ConnectedComponent.connectedComponentMk_mem
      ConnectedComponent.connectedComponentMk_mem had
      (rep (b a)) (rep (b d)) hrepA hrepD hrepne
    calc
      χ.get a d had = χ.get (rep (b a)) (rep (b d)) hrepne := hconst
      _ = ψ.get (b a) (b d) hbd := (hpull (b a) (b d) hbd).symm
  have htriple : NoRainbowTriangle ψ := by
    intro i j l hij hjl hli
    have hraw := hrawTriangle (rep i) (rep j) (rep l)
      (hinj.ne hij) (hinj.ne hjl) (hinj.ne hli)
      (hcompne i j hij) (hcompne j l hjl) (hcompne l i hli)
    by_contra hrepeat
    apply hraw
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      exact hrepeat (Or.inl (by simpa only [hpull] using heq))
    · intro heq
      exact hrepeat (Or.inr (Or.inl (by simpa only [hpull] using heq)))
    · intro heq
      exact hrepeat (Or.inr (Or.inr (by simpa only [hpull] using heq)))
  have hsum : ∑ i : Fin t, (blockFiber b i).card = n := by
    have h : (Finset.univ : Finset (Fin n)).card =
        ∑ i : Fin t, ((Finset.univ : Finset (Fin n)).filter
          (fun v => b v = i)).card :=
      Finset.card_eq_sum_card_fiberwise (by simp)
    simpa [blockFiber] using h.symm
  exact ⟨t, b, ψ, ht, hcrosslabel, htriple, hspos, hsupper, hsum⟩

end ErdosProblems.AntiRamseyCycleComponentQuotient

namespace ErdosProblems.AntiRamseyCycleCounted

open SimpleGraph
open ErdosProblems.AntiRamseyCycle

/-- The finite set of raw colors actually used on complete-graph edges. -/
noncomputable def rawPalette {n t : ℕ} (π : Fin n → Fin t) :
    Finset (Sum (Sym2 (Fin n)) (Fin t)) := by
  classical
  exact Finset.univ.image (rawOrderedBlockLabeling π)

/-- Every complete-graph edge has a color in the realized raw palette. -/
theorem rawPalette_mem {n t : ℕ} (π : Fin n → Fin t)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    rawOrderedBlockLabeling π e ∈ rawPalette π := by
  classical
  unfold rawPalette
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

/-- Relabel each realized raw color bijectively to a consecutive palette. -/
noncomputable def rawImageColor {n t : ℕ} (π : Fin n → Fin t) :
    TopEdgeLabeling (Fin n) (Fin (rawPalette π).card) := by
  classical
  exact fun e => (rawPalette π).equivFin
    ⟨rawOrderedBlockLabeling π e, rawPalette_mem π e⟩

/-- Two equal raw host-edge colors remain equal after image relabeling. -/
theorem rawImageColor_eq_of_raw_eq {n t : ℕ} (π : Fin n → Fin t)
    (e₁ e₂ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (h : rawOrderedBlockLabeling π e₁ = rawOrderedBlockLabeling π e₂) :
    rawImageColor π e₁ = rawImageColor π e₂ := by
  classical
  have hsub :
      (⟨rawOrderedBlockLabeling π e₁, rawPalette_mem π e₁⟩ : rawPalette π) =
      (⟨rawOrderedBlockLabeling π e₂, rawPalette_mem π e₂⟩ : rawPalette π) :=
    Subtype.ext h
  exact congrArg (rawPalette π).equivFin hsub

/-- By construction, every consecutive palette color is used. -/
theorem rawImageColor_surjective {n t : ℕ} (π : Fin n → Fin t) :
    Function.Surjective (rawImageColor π) := by
  classical
  intro j
  let c : rawPalette π := (rawPalette π).equivFin.symm j
  have hc : c.val ∈ rawPalette π := c.property
  change c.val ∈ Finset.univ.image (rawOrderedBlockLabeling π) at hc
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp hc
  have hsub :
      (⟨rawOrderedBlockLabeling π e, rawPalette_mem π e⟩ : rawPalette π) = c :=
    Subtype.ext he
  refine ⟨e, ?_⟩
  simp only [rawImageColor]
  rw [hsub]
  exact (rawPalette π).equivFin.apply_symm_apply j

/-- A small-fiber block coloring remains nonrainbow after its realized image
is relabeled to `Fin M`. -/
theorem rawImageColor_noRainbow_copy
    {k n t : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < k) :
    ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom (rawImageColor π) := by
  intro f hf
  have hraw := rawOrderedBlockLabeling_noRainbow_copy hk hn π hsmall f
  apply hraw
  intro e₁ e₂ hcolor
  apply hf
  exact rawImageColor_eq_of_raw_eq π
    (f.toHom.mapEdgeSet e₁) (f.toHom.mapEdgeSet e₂) hcolor

/-- The number of realized raw colors is a formal lower bound for any
small-fiber ordered block map. -/
theorem rawPalette_card_le_antiRamseyNum
    {k n t : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < k) :
    (rawPalette π).card ≤ antiRamseyNum (cycleGraph k) n := by
  let A : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
      ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ}
  have hbound : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  have hmem : (rawPalette π).card ∈ A :=
    ⟨rawImageColor π, rawImageColor_surjective π,
      rawImageColor_noRainbow_copy hk hn π hsmall⟩
  change (rawPalette π).card ≤ sSup A
  exact le_csSup hbound hmem

end ErdosProblems.AntiRamseyCycleCounted

namespace ErdosProblems.AntiRamseyCycleCounted

open SimpleGraph
open ErdosProblems.AntiRamseyCycle
open ErdosProblems.AntiRamseyCycleBlockCount

abbrev fullSourceEdge (m : ℕ) :=
  (⊤ : SimpleGraph (Fin m)).edgeSet

/-- A source edge of complete full block `b`, mapped to the host. -/
def fullBlockHostEdge (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (e : fullSourceEdge m) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  (fullBlockCopy m n hm b).toHom.mapEdgeSet e

@[simp] theorem fullBlockHostEdge_val (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (e : fullSourceEdge m) :
    (fullBlockHostEdge m n hm b e).val =
      Sym2.map (fullBlockVertex m n hm b) e.val := by
  change Sym2.map (fullBlockCopy m n hm b) e.val =
    Sym2.map (fullBlockVertex m n hm b) e.val
  rfl

/-- All endpoints of a mapped full-block edge have block index `b`. -/
theorem fullBlockHostEdge_blockSym2 (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (e : fullSourceEdge m) :
    Sym2.map (consecutiveBlockMap m n)
      (fullBlockHostEdge m n hm b e).val =
        Sym2.diag (Fin.castLE (Nat.le_succ _) b) := by
  rw [fullBlockHostEdge_val]
  induction e.val using Sym2.inductionOn with
  | hf i j =>
    simp [Sym2.map_mk, Sym2.diag, fullBlockVertex_block]

/-- An internal edge realizes exactly its own host-edge raw tag. -/
theorem fullBlockHostEdge_raw_color (m n : ℕ) (hm : 0 < m)
    (b : Fin (n / m)) (e : fullSourceEdge m) :
    rawOrderedBlockLabeling (consecutiveBlockMap m n)
      (fullBlockHostEdge m n hm b e) =
        Sum.inl (fullBlockHostEdge m n hm b e).val := by
  change orderedBlockColor (consecutiveBlockMap m n)
    (fullBlockHostEdge m n hm b e).val =
      Sum.inl (fullBlockHostEdge m n hm b e).val
  rw [fullBlockHostEdge_val]
  induction e.val using Sym2.inductionOn with
  | hf i j =>
    simp [Sym2.map_mk, orderedBlockColor_mk, fullBlockVertex_block]

/-- Host edges from separate full blocks are distinct; within a block,
the complete-graph Copy map is injective on source edges. -/
theorem fullBlockHostEdge_pair_injective (m n : ℕ) (hm : 0 < m) :
    Function.Injective
      (fun p : Fin (n / m) × fullSourceEdge m =>
        fullBlockHostEdge m n hm p.1 p.2) := by
  intro p r h
  have hblocks :
      Sym2.diag (Fin.castLE (Nat.le_succ _) p.1) =
        Sym2.diag (Fin.castLE (Nat.le_succ _) r.1) := by
    have hh := congrArg
      (fun z : (⊤ : SimpleGraph (Fin n)).edgeSet =>
        Sym2.map (consecutiveBlockMap m n) z.val) h
    simpa only [fullBlockHostEdge_blockSym2] using hh
  have hb : p.1 = r.1 :=
    Fin.castLE_injective (Nat.le_succ _)
      (Sym2.diag_injective hblocks)
  have he : p.2 = r.2 := by
    have h' := h
    change fullBlockHostEdge m n hm p.1 p.2 =
      fullBlockHostEdge m n hm r.1 r.2 at h'
    rw [← hb] at h'
    have hval :
        Sym2.map (fullBlockVertex m n hm p.1) p.2.val =
          Sym2.map (fullBlockVertex m n hm p.1) r.2.val := by
      simpa only [fullBlockHostEdge_val] using congrArg Subtype.val h'
    have hvertex : Function.Injective (fullBlockVertex m n hm p.1) := by
      intro i j hij
      have hv := congrArg Fin.val hij
      simp only [fullBlockVertex_val] at hv
      exact Fin.ext (Nat.add_right_cancel hv)
    exact Subtype.ext ((Sym2.map.injective hvertex) hval)
  exact Prod.ext hb he

def earlyFullBlock (m n : ℕ) (hq : 0 < n / m)
    (b : Fin (n / m - 1)) : Fin (n / m) :=
  ⟨b.val, by omega⟩

def lastFullBlock (m n : ℕ) (hq : 0 < n / m) :
    Fin (n / m) :=
  ⟨n / m - 1, by omega⟩

theorem earlyFullBlock_lt_last (m n : ℕ) (hq : 0 < n / m)
    (b : Fin (n / m - 1)) :
    earlyFullBlock m n hq b < lastFullBlock m n hq := by
  change b.val < n / m - 1
  exact b.isLt

/-- An edge from `b` to the last full block realizes the earlier-block tag. -/
def crossFullHostEdge (m n : ℕ) (hm : 0 < m) (hq : 0 < n / m)
    (b : Fin (n / m - 1)) : (⊤ : SimpleGraph (Fin n)).edgeSet := by
  let z : Fin m := ⟨0, hm⟩
  let x := fullBlockVertex m n hm (earlyFullBlock m n hq b) z
  let y := fullBlockVertex m n hm (lastFullBlock m n hq) z
  have hb : earlyFullBlock m n hq b ≠ lastFullBlock m n hq :=
    ne_of_lt (earlyFullBlock_lt_last m n hq b)
  have hxy : x ≠ y := by
    intro h
    have hp : (earlyFullBlock m n hq b, z) =
        (lastFullBlock m n hq, z) :=
      fullBlockVertex_injective m n hm h
    exact hb (congrArg Prod.fst hp)
  exact ⟨s(x, y), by
    simpa only [SimpleGraph.mem_edgeSet] using ((top_adj x y).mpr hxy)⟩

theorem crossFullHostEdge_raw_color (m n : ℕ) (hm : 0 < m)
    (hq : 0 < n / m) (b : Fin (n / m - 1)) :
    rawOrderedBlockLabeling (consecutiveBlockMap m n)
      (crossFullHostEdge m n hm hq b) =
        Sum.inr (Fin.castLE (Nat.le_succ _) (earlyFullBlock m n hq b)) := by
  let z : Fin m := ⟨0, hm⟩
  let a := earlyFullBlock m n hq b
  let c := lastFullBlock m n hq
  have hlt : (Fin.castLE (Nat.le_succ _) a) <
      (Fin.castLE (Nat.le_succ _) c) := by
    simpa only [Fin.lt_def, Fin.val_castLE] using
      earlyFullBlock_lt_last m n hq b
  change orderedBlockColor (consecutiveBlockMap m n)
    s(fullBlockVertex m n hm a z, fullBlockVertex m n hm c z) =
      Sum.inr (Fin.castLE (Nat.le_succ _) a)
  rw [orderedBlockColor_mk, fullBlockVertex_block, fullBlockVertex_block]
  simp [ne_of_lt hlt, min_eq_left (le_of_lt hlt)]

/-- The complete-block raw colors and the earlier-block crossing tags form
an explicit family of colors that really occur on host edges. -/
noncomputable def fullBlockRawWitness (m n : ℕ) (hm : 0 < m)
    (hq : 0 < n / m) :
    Sum (Fin (n / m) × fullSourceEdge m) (Fin (n / m - 1)) →
      rawPalette (consecutiveBlockMap m n)
  | Sum.inl (b, e) =>
      ⟨Sum.inl (fullBlockHostEdge m n hm b e).val, by
        rw [← fullBlockHostEdge_raw_color m n hm b e]
        exact rawPalette_mem _ _⟩
  | Sum.inr b =>
      ⟨Sum.inr
        (Fin.castLE (Nat.le_succ _) (earlyFullBlock m n hq b)), by
        rw [← crossFullHostEdge_raw_color m n hm hq b]
        exact rawPalette_mem _ _⟩

/-- Exact full-block image injection. -/
theorem fullBlockRawWitness_injective (m n : ℕ) (hm : 0 < m)
    (hq : 0 < n / m) :
    Function.Injective (fullBlockRawWitness m n hm hq) := by
  intro x y h
  have hv := congrArg Subtype.val h
  cases x with
  | inl p =>
    cases y with
    | inl r =>
      have he : fullBlockHostEdge m n hm p.1 p.2 =
          fullBlockHostEdge m n hm r.1 r.2 :=
        Subtype.ext (Sum.inl.inj hv)
      exact congrArg Sum.inl (fullBlockHostEdge_pair_injective m n hm he)
    | inr r => cases hv
  | inr p =>
    cases y with
    | inl r => cases hv
    | inr r =>
      have hc : Fin.castLE (Nat.le_succ _) (earlyFullBlock m n hq p) =
          Fin.castLE (Nat.le_succ _) (earlyFullBlock m n hq r) :=
        Sum.inr.inj hv
      have hearly : earlyFullBlock m n hq p = earlyFullBlock m n hq r :=
        Fin.castLE_injective (Nat.le_succ _) hc
      have hv : p.val = r.val := by
        simpa only [earlyFullBlock] using congrArg Fin.val hearly
      have hp : p = r := Fin.ext hv
      exact congrArg Sum.inr hp

end ErdosProblems.AntiRamseyCycleCounted

namespace ErdosProblems.AntiRamseyCycleCounted

open SimpleGraph
open ErdosProblems.AntiRamseyCycle
open ErdosProblems.AntiRamseyCycleBlockCount

/-- The checked full-block tag injection supplies a numerical lower bound
for the realized raw palette. -/
theorem fullBlock_rawPalette_card_lower (m n : ℕ)
    (hm : 0 < m) (hq : 0 < n / m) :
    n / m * (m.choose 2 + 1) - 1 ≤
      (rawPalette (consecutiveBlockMap m n)).card := by
  classical
  have hedge :
      Fintype.card ((⊤ : SimpleGraph (Fin m)).edgeSet) = m.choose 2 := by
    rw [SimpleGraph.card_edgeSet,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp
  have hdomain :
      Fintype.card
          (Sum (Fin (n / m) × (⊤ : SimpleGraph (Fin m)).edgeSet)
            (Fin (n / m - 1))) =
        n / m * m.choose 2 + (n / m - 1) := by
    simp only [Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, hedge]
  have hle := Fintype.card_le_of_injective
    (fullBlockRawWitness m n hm hq)
    (fullBlockRawWitness_injective m n hm hq)
  have hraw : n / m * m.choose 2 + (n / m - 1) ≤
      (rawPalette (consecutiveBlockMap m n)).card := by
    simpa only [hdomain, Fintype.card_coe] using hle
  have hformula :
      n / m * m.choose 2 + (n / m - 1) =
        n / m * (m.choose 2 + 1) - 1 := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  rw [← hformula]
  exact hraw

/-- For every original `n ≥ k ≥ 3`, full `(k−1)` blocks alone provide
the indicated number of nonrainbow colors on `K_n`. -/
theorem cycle_fullBlock_antiRamseyNum_lower (k n : ℕ)
    (hk : 3 ≤ k) (hn : k ≤ n) :
    n / (k - 1) * ((k - 1).choose 2 + 1) - 1 ≤
      antiRamseyNum (cycleGraph k) n := by
  have hm : 0 < k - 1 := by omega
  have hq : 0 < n / (k - 1) :=
    Nat.div_pos (by omega : k - 1 ≤ n) hm
  have hpalette := fullBlock_rawPalette_card_lower (k - 1) n hm hq
  have himage := rawPalette_card_le_antiRamseyNum hk hn
    (consecutiveBlockMap (k - 1) n)
    (cycleBlockMap_small_fibers k n hk)
  exact hpalette.trans himage

/-- Two full three-vertex blocks on six vertices give seven realized
colors without a rainbow four-cycle. -/
theorem cycle_four_six_antiRamseyNum_ge_seven :
    7 ≤ antiRamseyNum (cycleGraph 4) 6 := by
  simpa using cycle_fullBlock_antiRamseyNum_lower 4 6
    (by decide : 3 ≤ 4) (by decide : 4 ≤ 6)

end ErdosProblems.AntiRamseyCycleCounted

namespace ErdosProblems.AntiRamseyCycleCounted

open SimpleGraph
open ErdosProblems.AntiRamseyCycle
open ErdosProblems.AntiRamseyCycleBlockCount

/-- For every `n ≥ k ≥ 3`, the anti-Ramsey cycle number is at least its linear
coefficient `((k - 2) / 2 + 1 / (k - 1)) * n` minus the fixed remainder offset
`((k - 2) / 2 + 1 / (k - 1)) * (k - 1) + 1`. -/
theorem cycle_fullBlock_real_lower (k n : ℕ)
    (hk : 3 ≤ k) (hn : k ≤ n) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≥
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) *
          ((k - 1 : ℕ) : ℝ) - 1 := by
  let m : ℕ := k - 1
  let q : ℕ := n / m
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmpos : 0 < m := by omega
  have hmle : m ≤ n := by dsimp [m]; omega
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.div_pos hmle hmpos
  have hqone : 1 ≤ q := hq
  have hformula :
      q * m.choose 2 + (q - 1) =
        q * (m.choose 2 + 1) - 1 := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hnat : q * m.choose 2 + (q - 1) ≤
      antiRamseyNum (cycleGraph k) n := by
    rw [hformula]
    simpa only [m, q] using cycle_fullBlock_antiRamseyNum_lower
      k n hk hn
  have hqcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hqone]
    norm_num
  have hnatreal :
      ((q * m.choose 2 + (q - 1) : ℕ) : ℝ) ≤
        (antiRamseyNum (cycleGraph k) n : ℝ) := by
    exact_mod_cast hnat
  have hreal :
      (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 ≤
        (antiRamseyNum (cycleGraph k) n : ℝ) := by
    calc
      (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 =
          ((q * m.choose 2 + (q - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_mul, hqcast]
        ring
      _ ≤ (antiRamseyNum (cycleGraph k) n : ℝ) := hnatreal
  have hcoeff :
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) =
        (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) := by
    exact cycle_coefficient_eq_block_coefficient k hk
  have harith := full_blocks_real_lower m n hm hmle
  calc
    (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) *
          ((k - 1 : ℕ) : ℝ) - 1 =
      (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (n : ℝ) -
        (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (m : ℝ) - 1 := by
      rw [hcoeff]
    _ ≤ (q : ℝ) * ((m.choose 2 : ℕ) : ℝ) + (q : ℝ) - 1 := by
      simpa only [m, q] using harith
    _ ≤ (antiRamseyNum (cycleGraph k) n : ℝ) := hreal

end ErdosProblems.AntiRamseyCycleCounted

namespace ErdosProblems.AntiRamseyCycleBase

open SimpleGraph

/-- A graph with more vertices than the complete host has no injective copy. -/
theorem noCopy_of_card_gt {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) (hn : n < Fintype.card α) :
    ∀ _ : H.Copy (⊤ : SimpleGraph (Fin n)), False := by
  intro f
  have hcard : Fintype.card α ≤ n := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (f : α → Fin n) f.injective
  exact (not_lt_of_ge hcard) hn

/-- With no possible injective `H` copy, every host edge can use its own
color and no admissible coloring can use more colors than host edges. -/
theorem antiRamseyNum_eq_edgeCount_of_card_gt {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) (hn : n < Fintype.card α) :
    antiRamseyNum H n =
      Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet) := by
  classical
  let A : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
      ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f.toHom χ}
  have hbounded : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  have hmem : Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet) ∈ A := by
    let efin := Fintype.equivFin ((⊤ : SimpleGraph (Fin n)).edgeSet)
    let χ : TopEdgeLabeling (Fin n)
        (Fin (Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet))) :=
      fun e => efin e
    refine ⟨χ, ?_, ?_⟩
    · intro c
      obtain ⟨e, he⟩ := efin.surjective c
      exact ⟨e, he⟩
    · intro f
      exact (noCopy_of_card_gt H n hn f).elim
  change sSup A = Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet)
  apply le_antisymm
  · refine (csSup_le_iff' hbounded).2 ?_
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  · exact le_csSup hbounded hmem

/-- Choi's exact `n = k - 1` base for the first `n = k` induction step,
under the current Formal Conjectures injective-copy definition. -/
theorem antiRamseyNum_cycleGraph_induction_base (k : ℕ) (hk : 4 ≤ k) :
    antiRamseyNum (cycleGraph k) (k - 1) = (k - 1).choose 2 := by
  have hsmall : k - 1 < Fintype.card (Fin k) := by
    simp only [Fintype.card_fin]
    omega
  calc
    antiRamseyNum (cycleGraph k) (k - 1) =
        Fintype.card ((⊤ : SimpleGraph (Fin (k - 1))).edgeSet) :=
      antiRamseyNum_eq_edgeCount_of_card_gt (cycleGraph k) (k - 1) hsmall
    _ = (k - 1).choose 2 := by
      rw [SimpleGraph.card_edgeSet,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp

end ErdosProblems.AntiRamseyCycleBase

namespace ErdosProblems.AntiRamseyWeakCount

open Finset

theorem one_block_arithmetic (m s : ℕ) (hm : 2 ≤ m)
    (hs : 1 ≤ s) (hsm : s ≤ m) :
    ((s.choose 2 : ℕ) : ℝ) + 1 ≤
      (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (s : ℝ) := by
  have hmpos_nat : 0 < m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsm' : (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsm
  have htwo : (2 : ℝ) ≤ (m : ℝ) * (s : ℝ) := by
    calc
      (2 : ℝ) ≤ 2 * (s : ℝ) := by nlinarith
      _ ≤ (m : ℝ) * (s : ℝ) :=
        mul_le_mul_of_nonneg_right hm2 (by positivity)
  have hfactor_nonneg :
      0 ≤ ((m : ℝ) - (s : ℝ)) * ((m : ℝ) * (s : ℝ) - 2) :=
    mul_nonneg (sub_nonneg.mpr hsm') (sub_nonneg.mpr htwo)
  have hchoose : ((s.choose 2 : ℕ) : ℝ) =
      (s : ℝ) * ((s : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ s
  let D : ℝ :=
    (((m : ℝ) - 1) / 2 + 1 / (m : ℝ)) * (s : ℝ) -
      (((s.choose 2 : ℕ) : ℝ) + 1)
  have hfactor : (2 * (m : ℝ)) * D =
      ((m : ℝ) - (s : ℝ)) * ((m : ℝ) * (s : ℝ) - 2) := by
    dsimp [D]
    rw [hchoose]
    field_simp [ne_of_gt hmpos]
    ring
  have hscaled : 0 ≤ (2 * (m : ℝ)) * D := by
    rw [hfactor]
    exact hfactor_nonneg
  have hpositive : (0 : ℝ) < 2 * (m : ℝ) := by positivity
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_right hscaled hpositive
  dsimp [D] at hD
  linarith

/-- Conditional arithmetic step for Choi's weak anticyclic block count.
If `t ≥ 1` and every block size is between `1` and `k - 1`, the finite
internal-edge plus quotient-color count is at most the cycle coefficient
times the total number of vertices minus one. It does not assert that a
rainbow-cycle-free coloring has such a block partition. -/
theorem block_arithmetic_linear_bound (k t n : ℕ) (hk : 3 ≤ k) (ht : 1 ≤ t)
    (s : Fin t → ℕ) (hspos : ∀ i, 1 ≤ s i)
    (hsupper : ∀ i, s i ≤ k - 1)
    (hsum : ∑ i : Fin t, s i = n) :
    (((∑ i : Fin t, (s i).choose 2 : ℕ) : ℕ) : ℝ) + ((t - 1 : ℕ) : ℝ) ≤
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) - 1 := by
  let m : ℕ := k - 1
  let A : ℝ := ((m : ℝ) - 1) / 2 + 1 / (m : ℝ)
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hsum_blocks :
      (∑ i : Fin t, ((((s i).choose 2 : ℕ) : ℝ) + 1)) ≤
        ∑ i : Fin t, A * (s i : ℝ) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin t)))
        (f := fun i => (((s i).choose 2 : ℕ) : ℝ) + 1)
        (g := fun i => A * (s i : ℝ))
        (fun i _ => one_block_arithmetic m (s i) hm (hspos i) (hsupper i)))
  have hleft :
      (((∑ i : Fin t, (s i).choose 2 : ℕ) : ℕ) : ℝ) + (t : ℝ) =
        ∑ i : Fin t, ((((s i).choose 2 : ℕ) : ℝ) + 1) := by
    rw [Finset.sum_add_distrib]
    simp
  have hright : (∑ i : Fin t, A * (s i : ℝ)) = A * (n : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, hsum]
  have hfinite :
      (((∑ i : Fin t, (s i).choose 2 : ℕ) : ℕ) : ℝ) + (t : ℝ) ≤
        A * (n : ℝ) := by
    calc
      _ = ∑ i : Fin t, ((((s i).choose 2 : ℕ) : ℝ) + 1) := hleft
      _ ≤ ∑ i : Fin t, A * (s i : ℝ) := hsum_blocks
      _ = A * (n : ℝ) := hright
  have htcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht]
    norm_num
  have hmcast : (m : ℝ) = (k : ℝ) - 1 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hcoeff : A = (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) := by
    dsimp [A]
    rw [hmcast]
    ring
  rw [htcast, ← hcoeff]
  linarith

end ErdosProblems.AntiRamseyWeakCount

namespace ErdosProblems.AntiRamseyWeakCount

open Finset SimpleGraph
open ErdosProblems.AntiRamseyTriangle

/-- A conditional cycle-coefficient bound for the number of colors realized by an
edge coloring. The block map and quotient coloring are supplied explicitly.
Every block is nonempty and has fewer than `k` vertices. This theorem does not
construct the blocks from avoidance of a rainbow `k`-cycle. -/
theorem realized_colors_le_cycle_linear_of_weak_blocks {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (k t n : ℕ) (hk : 3 ≤ k) (ht : 1 ≤ t)
    (χ : TopEdgeLabeling V C) (b : V → Fin t)
    (ψ : TopEdgeLabeling (Fin t) C)
    (hcross : ∀ (a d : V) (had : a ≠ d) (hbd : b a ≠ b d),
      χ.get a d had = ψ.get (b a) (b d) hbd)
    (htriple : NoRainbowTriangle ψ)
    (hspos : ∀ i, 1 ≤ (blockFiber b i).card)
    (hsupper : ∀ i, (blockFiber b i).card ≤ k - 1)
    (hsum : ∑ i : Fin t, (blockFiber b i).card = n) :
    ((Finset.univ.image χ).card : ℝ) ≤
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) - 1 := by
  have hcount := realized_colors_le_block_edges_add χ b ψ hcross htriple
  have hcount_real : ((Finset.univ.image χ).card : ℝ) ≤
      (((∑ i : Fin t, (blockFiber b i).card.choose 2 : ℕ) : ℕ) : ℝ) +
        ((t - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcount
  exact hcount_real.trans
    (block_arithmetic_linear_bound k t n hk ht
      (fun i => (blockFiber b i).card) hspos hsupper hsum)

end ErdosProblems.AntiRamseyWeakCount

namespace ErdosProblems.AntiRamseyConditionalCycleUpper

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleBase
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyWeakCount
open ErdosProblems.AntiRamseyCycleBlockCount
open ErdosProblems.AntiRamseyTriangle

/-- The exact real coefficient in the cycle part of Erdős #1105. -/
noncomputable def cycleSlope (k : ℕ) : ℝ :=
  ((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)

/-- Choi's Lemma 3.2.3 weak-block decomposition property for `C_k`-free host
colorings in which every vertex has at least two private ("NEW") colors and
every pair of distinct vertices has at least `k - 1` private colors in total. -/
def HighNewWeakStructure (k : ℕ) : Prop :=
  ∀ {n q : ℕ} (_hn : k ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (_hfree : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (_hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (_hpair : ∀ x y : Fin n, x ≠ y →
      k - 1 ≤ (newColors χ x).card + (newColors χ y).card),
    ∃ (t : ℕ) (b : Fin n → Fin t)
      (ψ : TopEdgeLabeling (Fin t) (Fin q)),
      1 ≤ t ∧
      (∀ (a d : Fin n) (had : a ≠ d) (hbd : b a ≠ b d),
        χ.get a d had = ψ.get (b a) (b d) hbd) ∧
      NoRainbowTriangle ψ ∧
      (∀ i : Fin t, 1 ≤ (blockFiber b i).card) ∧
      (∀ i : Fin t, (blockFiber b i).card ≤ k - 1) ∧
      (∑ i : Fin t, (blockFiber b i).card = n)

theorem cycleSlope_nonneg (k : ℕ) (hk : 4 ≤ k) :
    0 ≤ cycleSlope k := by
  have hkreal : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - 1 := by linarith
  have hrec : 0 ≤ 1 / ((k : ℝ) - 1) :=
    le_of_lt (one_div_pos.mpr hden)
  unfold cycleSlope
  linarith

theorem new_le_cycleSlope_of_low (k a : ℕ) (hk : 4 ≤ k)
    (ha : a ≤ (k - 2) / 2) : (a : ℝ) ≤ cycleSlope k := by
  have hnat : 2 * a ≤ k - 2 := by
    have hdiv := Nat.div_mul_le_self (k - 2) 2
    omega
  have hreal : (2 : ℝ) * (a : ℝ) ≤ ((k - 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub (by omega : 2 ≤ k)] at hreal
  have hkreal : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - 1 := by linarith
  have hrec : 0 ≤ 1 / ((k : ℝ) - 1) :=
    le_of_lt (one_div_pos.mpr hden)
  have hreal' : (2 : ℝ) * (a : ℝ) ≤ (k : ℝ) - 2 := by
    simpa only [Nat.cast_ofNat] using hreal
  have hhalf : (a : ℝ) ≤ ((k : ℝ) - 2) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    simpa only [mul_comm] using hreal'
  unfold cycleSlope
  exact le_trans hhalf (le_add_of_nonneg_right hrec)

theorem cycleSlope_base_identity (k : ℕ) (hk : 4 ≤ k) :
    cycleSlope k * ((k - 1 : ℕ) : ℝ) =
      (((k - 1).choose 2 : ℕ) : ℝ) + 1 := by
  unfold cycleSlope
  rw [cycle_coefficient_eq_block_coefficient k (by omega)]
  exact full_block_coefficient (k - 1) (by omega)

/-- Under the one explicit high-new-color structure premise, every
surjective palette avoiding a rainbow `C_k` has the claimed upper count.
The first induction state is `n = k - 1`, not `n = k`. -/
theorem admissible_palette_le_cycle_linear (k n : ℕ) (hk : 4 ≤ k)
    (hn : k - 1 ≤ n) (hstructure : HighNewWeakStructure k)
    {q : ℕ} (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ)
    (hfree : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ) :
    (q : ℝ) ≤ cycleSlope k * (n : ℝ) - 1 := by
  have hstrong : ∀ N : ℕ, k - 1 ≤ N →
      ∀ {Q : ℕ} (ψ : TopEdgeLabeling (Fin N) (Fin Q)),
        Function.Surjective ψ →
        (∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin N)),
          ¬IsRainbow f.toHom ψ) →
        (Q : ℝ) ≤ cycleSlope k * (N : ℝ) - 1 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hN Q ψ hψ hno
      by_cases hbase : N = k - 1
      · subst N
        have hused : (usedColors ψ).card = Q := by
          rw [usedColors, Finset.image_univ_of_surjective hψ]
          simp
        have hq : Q ≤ (k - 1).choose 2 := by
          have hbound := usedColors_card_le_antiRamseyNum
            (cycleGraph k) ψ hno
          rw [hused, antiRamseyNum_cycleGraph_induction_base k hk] at hbound
          exact hbound
        have hqreal : (Q : ℝ) ≤ (((k - 1).choose 2 : ℕ) : ℝ) := by
          exact_mod_cast hq
        have hcoeff := cycleSlope_base_identity k hk
        linarith
      · have hkN : k ≤ N := by omega
        cases N with
        | zero => omega
        | succ M =>
          have hM : k - 1 ≤ M := by omega
          by_cases hlow : ∃ v : Fin (M + 1),
              (newColors ψ v).card ≤ (k - 2) / 2
          · obtain ⟨v, hv⟩ := hlow
            obtain ⟨φ, hφ, hφfree⟩ :=
              deletedPalette_witness (cycleGraph k) ψ hno v
            have hp := ih M (by omega) hM φ hφ hφfree
            have hqrec := surjective_color_count_delete_add_new ψ hψ v
            have hqreal : (Q : ℝ) =
                ((colorsAfterDeleting ψ v).card : ℝ) +
                ((newColors ψ v).card : ℝ) := by
              exact_mod_cast hqrec
            have hvreal := new_le_cycleSlope_of_low k
              (newColors ψ v).card hk hv
            have hstep : cycleSlope k * ((M + 1 : ℕ) : ℝ) =
                cycleSlope k * (M : ℝ) + cycleSlope k := by
              push_cast
              ring
            linarith
          · have hlarge : ∀ v : Fin (M + 1),
                (k - 2) / 2 < (newColors ψ v).card := by
              intro v
              have hv : ¬(newColors ψ v).card ≤ (k - 2) / 2 := by
                intro h
                exact hlow ⟨v, h⟩
              omega
            have hnew : ∀ v : Fin (M + 1),
                2 ≤ (newColors ψ v).card := by
              intro v
              have hv := hlarge v
              omega
            have hpair : ∀ x y : Fin (M + 1), x ≠ y →
                k - 1 ≤ (newColors ψ x).card +
                  (newColors ψ y).card := by
              intro x y _
              have hx := hlarge x
              have hy := hlarge y
              omega
            obtain ⟨t, b, φ, ht, hcross, htri, hspos, hsupper, hsum⟩ :=
              hstructure hkN ψ hno hnew hpair
            have hcount := realized_colors_le_cycle_linear_of_weak_blocks
              k t (M + 1) (by omega) ht ψ b φ
              hcross htri hspos hsupper hsum
            have hused : (Finset.univ.image ψ).card = Q := by
              rw [Finset.image_univ_of_surjective hψ]
              simp
            simpa only [hused, cycleSlope] using hcount
  exact hstrong n hn χ hχ hfree

/-- Upper bound on `antiRamseyNum (cycleGraph k) n` for `k ≥ 4` and `n ≥ k - 1`
given `HighNewWeakStructure k`. -/
theorem antiRamseyNum_le_cycle_linear (k n : ℕ) (hk : 4 ≤ k)
    (hn : k - 1 ≤ n) (hstructure : HighNewWeakStructure k) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≤
      cycleSlope k * (n : ℝ) - 1 := by
  classical
  let A : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
      ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
        ¬IsRainbow f.toHom χ}
  have hbounded : BddAbove A := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  change ((sSup A : ℕ) : ℝ) ≤ cycleSlope k * (n : ℝ) - 1
  by_cases hnonempty : A.Nonempty
  · have hmem : sSup A ∈ A := Nat.sSup_mem hnonempty hbounded
    obtain ⟨χ, hχ, hfree⟩ := hmem
    exact admissible_palette_le_cycle_linear k n hk hn hstructure
      χ hχ hfree
  · have hA : A = ∅ := by
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hq
      exact hnonempty ⟨q, hq⟩
    have hsup : sSup A = 0 := by simp [hA]
    rw [hsup]
    have hnreal : ((k - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hmul := mul_le_mul_of_nonneg_left hnreal
      (cycleSlope_nonneg k hk)
    have hcoeff := cycleSlope_base_identity k hk
    have hchoose : (0 : ℝ) ≤ (((k - 1).choose 2 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    norm_num at hmul ⊢
    linarith

end ErdosProblems.AntiRamseyConditionalCycleUpper

namespace ErdosProblems.AntiRamseyTriangle

/-- The edge `s(a,b)` receives its larger endpoint as its color. -/
def maxEndpointColor (n : ℕ) : SimpleGraph.TopEdgeLabeling (Fin n) (Fin n) :=
  fun e => Sym2.lift ⟨fun a b => max a b, fun a b => max_comm a b⟩ e.1

@[simp] theorem maxEndpointColor_get {n : ℕ} (a b : Fin n)
    (hab : (⊤ : SimpleGraph (Fin n)).Adj a b) :
    (maxEndpointColor n).get a b hab = max a b := by
  rfl

/-- Every triangle has a repeated color in the larger-endpoint coloring. -/
theorem maxEndpointColor_noRainbowTriangle {n : ℕ} (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (maxEndpointColor n).get a b ((SimpleGraph.top_adj a b).2 hab) =
        (maxEndpointColor n).get b c ((SimpleGraph.top_adj b c).2 hbc) ∨
      (maxEndpointColor n).get b c ((SimpleGraph.top_adj b c).2 hbc) =
        (maxEndpointColor n).get c a ((SimpleGraph.top_adj c a).2 hca) ∨
      (maxEndpointColor n).get c a ((SimpleGraph.top_adj c a).2 hca) =
        (maxEndpointColor n).get a b ((SimpleGraph.top_adj a b).2 hab) := by
  simp only [maxEndpointColor_get]
  rcases le_total a b with hab' | hba'
  · rcases le_total b c with hbc' | hcb'
    · right; left
      rw [max_eq_right hbc', max_eq_left (le_trans hab' hbc')]
    · left
      rw [max_eq_right hab', max_eq_left hcb']
  · rcases le_total a c with hac' | hca'
    · right; left
      rw [max_eq_right (le_trans hba' hac'), max_eq_left hac']
    · right; right
      rw [max_eq_right hca', max_eq_left hba']

/-- The smallest vertex is not the color of any edge. -/
theorem maxEndpointColor_ne_zero {n : ℕ} [NeZero n]
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) : maxEndpointColor n e ≠ 0 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b :=
      (SimpleGraph.top_adj a b).1 (((⊤ : SimpleGraph (Fin n)).mem_edgeSet).1 he)
    change max a b ≠ 0
    intro hzero
    have ha : a = 0 := le_antisymm (by rw [← hzero]; exact le_max_left a b) (Fin.zero_le a)
    have hb : b = 0 := le_antisymm (by rw [← hzero]; exact le_max_right a b) (Fin.zero_le b)
    exact hab (ha.trans hb.symm)

/-- The colors used by the construction are precisely the vertices other than zero. -/
theorem maxEndpointColor_image_eq_erase_zero {n : ℕ} [NeZero n] :
    Finset.univ.image (maxEndpointColor n) = Finset.univ.erase (0 : Fin n) := by
  apply Finset.ext
  intro c
  constructor
  · intro hc
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_erase.mpr ⟨maxEndpointColor_ne_zero e, Finset.mem_univ _⟩
  · intro hc
    obtain ⟨hc, _⟩ := Finset.mem_erase.mp hc
    apply Finset.mem_image.mpr
    refine ⟨⟨s((0 : Fin n), c), ?_⟩, Finset.mem_univ _, ?_⟩
    · exact ((⊤ : SimpleGraph (Fin n)).mem_edgeSet).2
        ((SimpleGraph.top_adj 0 c).2 (Ne.symm hc))
    · simp [maxEndpointColor]

/-- The lower-bound coloring uses exactly `n-1` colors. -/
theorem maxEndpointColor_image_card {n : ℕ} (hn : 3 ≤ n) :
    (Finset.univ.image (maxEndpointColor n)).card = n - 1 := by
  cases n with
  | zero => omega
  | succ m =>
      rw [maxEndpointColor_image_eq_erase_zero]
      simp [Finset.card_erase_of_mem]

/-- Relabel the used positive endpoints by `Fin m`; this uses every color. -/
def predEndpointColor (m : ℕ) [NeZero m] :
    SimpleGraph.TopEdgeLabeling (Fin (m + 1)) (Fin m) :=
  fun e => (0 : Fin m).predAbove (maxEndpointColor (m + 1) e)

@[simp] theorem predEndpointColor_get {m : ℕ} [NeZero m] (a b : Fin (m + 1))
    (hab : (⊤ : SimpleGraph (Fin (m + 1))).Adj a b) :
    (predEndpointColor m).get a b hab = (0 : Fin m).predAbove (max a b) := by
  rfl

/-- Each color occurs on the edge from vertex zero to its successor. -/
theorem predEndpointColor_surjective (m : ℕ) [NeZero m] :
    Function.Surjective (predEndpointColor m) := by
  intro i
  refine ⟨⟨s((0 : Fin (m + 1)), i.succ), ?_⟩, ?_⟩
  · exact ((⊤ : SimpleGraph (Fin (m + 1))).mem_edgeSet).2
      ((SimpleGraph.top_adj 0 i.succ).2 (Ne.symm (Fin.succ_ne_zero i)))
  · simp [predEndpointColor, maxEndpointColor]

/-- The surjective `Fin m` relabeling also has no rainbow triangle. -/
theorem predEndpointColor_noRainbowTriangle {m : ℕ} [NeZero m]
    (a b c : Fin (m + 1)) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    (predEndpointColor m).get a b ((SimpleGraph.top_adj a b).2 hab) =
        (predEndpointColor m).get b c ((SimpleGraph.top_adj b c).2 hbc) ∨
      (predEndpointColor m).get b c ((SimpleGraph.top_adj b c).2 hbc) =
        (predEndpointColor m).get c a ((SimpleGraph.top_adj c a).2 hca) ∨
      (predEndpointColor m).get c a ((SimpleGraph.top_adj c a).2 hca) =
        (predEndpointColor m).get a b ((SimpleGraph.top_adj a b).2 hab) := by
  simp only [predEndpointColor_get]
  have h := maxEndpointColor_noRainbowTriangle a b c hab hbc hca
  simp only [maxEndpointColor_get] at h
  rcases h with h | h | h
  · exact Or.inl (congrArg (Fin.predAbove (0 : Fin m)) h)
  · exact Or.inr (Or.inl (congrArg (Fin.predAbove (0 : Fin m)) h))
  · exact Or.inr (Or.inr (congrArg (Fin.predAbove (0 : Fin m)) h))

end ErdosProblems.AntiRamseyTriangle

namespace ErdosProblems.AntiRamseyTriangle

open SimpleGraph

/-- A complete edge labeling with no rainbow triangle has no rainbow copy of `C₃`. -/
theorem no_rainbow_cycleGraph_three_copy {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (hχ : NoRainbowTriangle χ) :
    ∀ f : (cycleGraph 3).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ := by
  intro f hf
  let a : Fin n := f 0
  let b : Fin n := f 1
  let c : Fin n := f 2
  have hab : a ≠ b := f.injective.ne (by decide)
  have hbc : b ≠ c := f.injective.ne (by decide)
  have hca : c ≠ a := f.injective.ne (by decide)
  rcases hχ a b c hab hbc hca with h₁ | h₂ | h₃
  · have : (EdgeLabeling.pullback χ f.toHom) ⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩ =
        (EdgeLabeling.pullback χ f.toHom) ⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩ := by
      simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
        EdgeLabeling.get, a, b, c] using h₁
    have he : (⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩ :
        (cycleGraph 3).edgeSet) ≠
        ⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩ := by decide
    exact he (hf this)
  · have : (EdgeLabeling.pullback χ f.toHom) ⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩ =
        (EdgeLabeling.pullback χ f.toHom) ⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩ := by
      simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
        EdgeLabeling.get, a, b, c] using h₂
    have he : (⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩ :
        (cycleGraph 3).edgeSet) ≠
        ⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩ := by decide
    exact he (hf this)
  · have : (EdgeLabeling.pullback χ f.toHom) ⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩ =
        (EdgeLabeling.pullback χ f.toHom) ⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩ := by
      simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
        EdgeLabeling.get, a, b, c] using h₃
    have he : (⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩ :
        (cycleGraph 3).edgeSet) ≠
        ⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩ := by decide
    exact he (hf this)

end ErdosProblems.AntiRamseyTriangle

namespace ErdosProblems.AntiRamseyTriangle

open SimpleGraph

/-- The absence of a rainbow injective copy of `C₃` forces every triangle to repeat a color. -/
theorem noRainbowTriangle_of_no_rainbow_cycleGraph_three_copy {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 3).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) : NoRainbowTriangle χ := by
  intro a b c hab hbc hca
  by_contra hrepeat
  have h₁ : χ.get a b hab ≠ χ.get b c hbc := by
    intro heq
    exact hrepeat (Or.inl heq)
  have h₂ : χ.get b c hbc ≠ χ.get c a hca := by
    intro heq
    exact hrepeat (Or.inr (Or.inl heq))
  have h₃ : χ.get c a hca ≠ χ.get a b hab := by
    intro heq
    exact hrepeat (Or.inr (Or.inr heq))
  let v : Fin 3 → Fin n := fun i => if i = 0 then a else if i = 1 then b else c
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [v, hab, hab.symm, hbc, hbc.symm, hca, hca.symm] at hij ⊢
  let φ : (cycleGraph 3) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨v, by
      intro i j hij
      exact (top_adj _ _).mpr (hv.ne ((cycleGraph 3).ne_of_adj hij))⟩
  let f : (cycleGraph 3).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hv⟩
  let e₁ : (cycleGraph 3).edgeSet :=
    ⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩
  let e₂ : (cycleGraph 3).edgeSet :=
    ⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩
  let e₃ : (cycleGraph 3).edgeSet :=
    ⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩
  have hedges : ∀ e : (cycleGraph 3).edgeSet,
      e = e₁ ∨ e = e₂ ∨ e = e₃ := by
    decide
  have hcol₁ : (EdgeLabeling.pullback χ f.toHom) e₁ = χ.get a b hab := by
    simp [e₁, f, φ, v, EdgeLabeling.get, Hom.mapEdgeSet, Sym2.map_mk]
  have hcol₂ : (EdgeLabeling.pullback χ f.toHom) e₂ = χ.get b c hbc := by
    simp [e₂, f, φ, v, EdgeLabeling.get, Hom.mapEdgeSet, Sym2.map_mk]
  have hcol₃ : (EdgeLabeling.pullback χ f.toHom) e₃ = χ.get c a hca := by
    simp [e₃, f, φ, v, EdgeLabeling.get, Hom.mapEdgeSet, Sym2.map_mk]
  apply hno f
  intro x y hxy
  rcases hedges x with hx | hx | hx <;>
    rcases hedges y with hy | hy | hy <;>
    subst x <;> subst y
  · rfl
  · exact (h₁ (by simpa only [hcol₁, hcol₂] using hxy)).elim
  · exact (h₃ (by simpa only [hcol₃, hcol₁] using hxy.symm)).elim
  · exact (h₁ (by simpa only [hcol₁, hcol₂] using hxy.symm)).elim
  · rfl
  · exact (h₂ (by simpa only [hcol₂, hcol₃] using hxy)).elim
  · exact (h₃ (by simpa only [hcol₃, hcol₁] using hxy)).elim
  · exact (h₂ (by simpa only [hcol₂, hcol₃] using hxy.symm)).elim
  · rfl

end ErdosProblems.AntiRamseyTriangle

namespace ErdosProblems.AntiRamseyTriangle

open SimpleGraph

def admissibleCounts (n : ℕ) : Set ℕ :=
  {k | ∃ χ : TopEdgeLabeling (Fin n) (Fin k), Function.Surjective χ ∧
    ∀ f : (cycleGraph 3).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ}

theorem admissibleCounts_bddAbove (n : ℕ) : BddAbove (admissibleCounts n) := by
  refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
  intro k hk
  obtain ⟨χ, hχ, _⟩ := hk
  simpa using Fintype.card_le_of_surjective χ hχ

/-- For `n ≥ 3`, the anti-Ramsey number of the triangle is exactly `n - 1`. -/
theorem antiRamseyNum_cycleGraph_three (n : ℕ) (hn : 3 ≤ n) :
    antiRamseyNum (cycleGraph 3) n = n - 1 := by
  change sSup (admissibleCounts n) = n - 1
  apply le_antisymm
  · refine (csSup_le_iff' (admissibleCounts_bddAbove n)).2 ?_
    intro k hk
    obtain ⟨χ, hχ, hno⟩ := hk
    have hrepeat := noRainbowTriangle_of_no_rainbow_cycleGraph_three_copy χ hno
    have hbound := gallai_color_bound χ hrepeat
    have himage : Finset.univ.image χ = Finset.univ :=
      Finset.image_univ_of_surjective hχ
    simpa [himage] using hbound
  · cases n with
    | zero => omega
    | succ m =>
      have hm : m ≠ 0 := by omega
      let : NeZero m := ⟨hm⟩
      have hmem : m ∈ admissibleCounts (m + 1) := by
        refine ⟨predEndpointColor m, predEndpointColor_surjective m, ?_⟩
        exact no_rainbow_cycleGraph_three_copy (predEndpointColor m)
          (fun a b c hab hbc hca => predEndpointColor_noRainbowTriangle a b c hab hbc hca)
      have hle := le_csSup (admissibleCounts_bddAbove (m + 1)) hmem
      simpa using hle

end ErdosProblems.AntiRamseyTriangle

namespace ErdosProblems.AntiRamseyTriangle

open SimpleGraph Asymptotics Filter

/-- At `k = 3`, the Formal Conjectures cycle error term is eventually exactly `-1`. -/
theorem triangle_error_eventually_eq_neg_one :
    (fun n : ℕ => (antiRamseyNum (cycleGraph 3) n : ℝ) -
      ((3 - 2 : ℝ) / 2 + 1 / (3 - 1)) * n) =ᶠ[atTop] (fun _ => (-1 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  have hvalue := antiRamseyNum_cycleGraph_three n hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ n))
  have hcoeff : ((3 - 2 : ℝ) / 2 + 1 / (3 - 1)) = 1 := by norm_num
  simp only [hvalue, hcast, hcoeff]
  ring

/-- The `k = 3` instance of the all-cycle `O(1)` claim in `erdos_1105.parts.i`. -/
theorem triangle_asymptotic_formalConjectures :
    ((fun n => (antiRamseyNum (cycleGraph 3) n : ℝ) -
      ((3 - 2 : ℝ) / 2 + 1 / (3 - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) := by
  exact triangle_error_eventually_eq_neg_one.trans_isBigO
    (isBigO_const_one ℝ (-1 : ℝ) atTop)

end ErdosProblems.AntiRamseyTriangle

namespace ErdosProblems.AntiRamseyConditionalAsymptotic

open SimpleGraph Asymptotics Filter
open ErdosProblems.AntiRamseyCycleCounted
open ErdosProblems.AntiRamseyConditionalCycleUpper
open ErdosProblems.AntiRamseyTriangle

/-- For any fixed `k ≥ 4` satisfying `HighNewWeakStructure k`, the full-block
lower bound and linear upper bound yield the `=O[atTop] 1` error term. -/
theorem cycle_asymptotic_of_highNewWeakStructure (k : ℕ)
    (hk : 4 ≤ k) (hstructure : HighNewWeakStructure k) :
    ((fun n : ℕ => (antiRamseyNum (cycleGraph k) n : ℝ) -
      ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
      =O[atTop] (fun _ => (1 : ℝ))) := by
  let α : ℝ := ((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)
  have hkreal : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - 1 := by linarith
  have hα : 0 ≤ α := by
    dsimp [α]
    exact add_nonneg (div_nonneg (by linarith) (by norm_num))
      (le_of_lt (one_div_pos.mpr hden))
  let c : ℝ := α * ((k - 1 : ℕ) : ℝ) + 1
  have hc : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg (mul_nonneg hα (Nat.cast_nonneg _)) (by norm_num)
  refine IsBigO.of_bound c ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  have hlow :
      α * (n : ℝ) - α * ((k - 1 : ℕ) : ℝ) - 1 ≤
        (antiRamseyNum (cycleGraph k) n : ℝ) := by
    simpa only [α] using cycle_fullBlock_real_lower k n (by omega : 3 ≤ k) hn
  have hhigh :
      (antiRamseyNum (cycleGraph k) n : ℝ) ≤ α * (n : ℝ) - 1 := by
    simpa only [α, cycleSlope] using
      antiRamseyNum_le_cycle_linear k n hk (by omega : k - 1 ≤ n) hstructure
  have hleft :
      -c ≤ (antiRamseyNum (cycleGraph k) n : ℝ) - α * (n : ℝ) := by
    dsimp [c]
    linarith
  have hright :
      (antiRamseyNum (cycleGraph k) n : ℝ) - α * (n : ℝ) ≤ c := by
    dsimp [c]
    linarith
  have habs := abs_le.mpr ⟨hleft, hright⟩
  simpa only [Real.norm_eq_abs, norm_one, mul_one, α] using habs

/-- Combines the `k = 3` triangle asymptotic with `cycle_asymptotic_of_highNewWeakStructure`
for all `k ≥ 4`. -/
theorem cycle_asymptotic_all_of_highNewWeakStructure
    (hstructure : ∀ k : ℕ, 4 ≤ k → HighNewWeakStructure k) :
    ∀ k, 3 ≤ k →
      ((fun n : ℕ => (antiRamseyNum (cycleGraph k) n : ℝ) -
        ((k - 2 : ℝ) / 2 + 1 / (k - 1)) * n)
        =O[atTop] (fun _ => (1 : ℝ))) := by
  intro k hk
  by_cases h3 : k = 3
  · subst k
    exact triangle_asymptotic_formalConjectures
  · exact cycle_asymptotic_of_highNewWeakStructure k (by omega)
      (hstructure k (by omega))

end ErdosProblems.AntiRamseyConditionalAsymptotic

namespace ErdosProblems.AntiRamseyCycleFour

open SimpleGraph

def copyOfInjection (v : Fin 4 → Fin 4) (hv : Function.Injective v) :
    (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin 4)) :=
  ⟨⟨v, by
      intro i j hij
      exact (top_adj _ _).mpr (hv.ne ((cycleGraph 4).ne_of_adj hij))⟩, hv⟩

def mapZero : Fin 4 → Fin 4 := id
def mapOne : Fin 4 → Fin 4 := fun i =>
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 3 else 2
def mapTwo : Fin 4 → Fin 4 := fun i =>
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else 3

theorem mapZero_injective : Function.Injective mapZero := by
  intro i j hij
  exact hij

theorem mapOne_injective : Function.Injective mapOne := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [mapOne] at hij ⊢

theorem mapTwo_injective : Function.Injective mapTwo := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [mapTwo] at hij ⊢

/- The image edges are respectively the three complements of perfect matchings. -/
def squareCopyZero : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin 4)) :=
  copyOfInjection mapZero mapZero_injective

def squareCopyOne : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin 4)) :=
  copyOfInjection mapOne mapOne_injective

def squareCopyTwo : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin 4)) :=
  copyOfInjection mapTwo mapTwo_injective

def sourceEdge01 : (cycleGraph 4).edgeSet :=
  ⟨s((0 : Fin 4), 1), by
    change ((0 : Fin 4) - 1 = 1 ∨ (1 : Fin 4) - 0 = 1)
    exact Or.inr rfl⟩

def sourceEdge12 : (cycleGraph 4).edgeSet :=
  ⟨s((1 : Fin 4), 2), by
    change ((1 : Fin 4) - 2 = 1 ∨ (2 : Fin 4) - 1 = 1)
    exact Or.inr rfl⟩

def sourceEdge23 : (cycleGraph 4).edgeSet :=
  ⟨s((2 : Fin 4), 3), by
    change ((2 : Fin 4) - 3 = 1 ∨ (3 : Fin 4) - 2 = 1)
    exact Or.inr rfl⟩

def sourceEdge30 : (cycleGraph 4).edgeSet :=
  ⟨s((3 : Fin 4), 0), by
    change ((3 : Fin 4) - 0 = 1 ∨ (0 : Fin 4) - 3 = 1)
    exact Or.inr rfl⟩

theorem sourceEdge_cases (e : (cycleGraph 4).edgeSet) :
    e = sourceEdge01 ∨ e = sourceEdge12 ∨
      e = sourceEdge23 ∨ e = sourceEdge30 := by
  obtain ⟨q, hq⟩ := e
  induction q using Sym2.inductionOn with
  | _ i j =>
    fin_cases i <;> fin_cases j <;> revert hq <;> decide

def targetEdge01 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((0 : Fin 4), 1), by
    change (0 : Fin 4) ≠ 1
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge02 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((0 : Fin 4), 2), by
    change (0 : Fin 4) ≠ 2
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge03 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((0 : Fin 4), 3), by
    change (0 : Fin 4) ≠ 3
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge12 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((1 : Fin 4), 2), by
    change (1 : Fin 4) ≠ 2
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge13 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((1 : Fin 4), 3), by
    change (1 : Fin 4) ≠ 3
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge23 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((2 : Fin 4), 3), by
    change (2 : Fin 4) ≠ 3
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

theorem completeFourEdge_cases (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    e = targetEdge01 ∨ e = targetEdge02 ∨ e = targetEdge03 ∨
      e = targetEdge12 ∨ e = targetEdge13 ∨ e = targetEdge23 := by
  obtain ⟨q, hq⟩ := e
  induction q using Sym2.inductionOn with
  | _ i j =>
    fin_cases i <;> fin_cases j <;> revert hq <;> decide

theorem copyTwo_omits_edge01 (e : (cycleGraph 4).edgeSet) :
    squareCopyTwo.toHom.mapEdgeSet e ≠ targetEdge01 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyZero_omits_edge02 (e : (cycleGraph 4).edgeSet) :
    squareCopyZero.toHom.mapEdgeSet e ≠ targetEdge02 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyOne_omits_edge03 (e : (cycleGraph 4).edgeSet) :
    squareCopyOne.toHom.mapEdgeSet e ≠ targetEdge03 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyOne_omits_edge12 (e : (cycleGraph 4).edgeSet) :
    squareCopyOne.toHom.mapEdgeSet e ≠ targetEdge12 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyZero_omits_edge13 (e : (cycleGraph 4).edgeSet) :
    squareCopyZero.toHom.mapEdgeSet e ≠ targetEdge13 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyTwo_omits_edge23 (e : (cycleGraph 4).edgeSet) :
    squareCopyTwo.toHom.mapEdgeSet e ≠ targetEdge23 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem every_target_edge_omitted_by_a_square
    (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    (∀ x : (cycleGraph 4).edgeSet, squareCopyZero.toHom.mapEdgeSet x ≠ e) ∨
    (∀ x : (cycleGraph 4).edgeSet, squareCopyOne.toHom.mapEdgeSet x ≠ e) ∨
    (∀ x : (cycleGraph 4).edgeSet, squareCopyTwo.toHom.mapEdgeSet x ≠ e) := by
  rcases completeFourEdge_cases e with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr copyTwo_omits_edge01)
  · exact Or.inl copyZero_omits_edge02
  · exact Or.inr (Or.inl copyOne_omits_edge03)
  · exact Or.inr (Or.inl copyOne_omits_edge12)
  · exact Or.inl copyZero_omits_edge13
  · exact Or.inr (Or.inr copyTwo_omits_edge23)

end ErdosProblems.AntiRamseyCycleFour

namespace ErdosProblems.AntiRamseyCycleSelectedNewEndpoint

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Every edge of the checked NEW representative has a label NEW at
one of its endpoints, even if that label is NEW at both endpoints. -/
theorem selected_edge_color_new_at_endpoint
    (χ : TopEdgeLabeling (Fin n) C)
    (e : (newColorRepresentative χ).edgeSet) :
    ∃ v : Fin n, v ∈ e.val ∧
      χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ ∈
        newColors χ v := by
  have he : e.val ∈
      Set.range (fun d : newColorUnion χ => (chosenNewEdge χ d).val) := by
    rw [← newColorRepresentative_edgeSet χ]
    exact e.property
  obtain ⟨d, hd⟩ := he
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp d.property
  let eTop : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩
  have htop : eTop = chosenNewEdge χ d :=
    Subtype.ext hd.symm
  have hcolor : χ eTop = d.val := by
    rw [htop]
    exact chosenNewEdge_color χ d
  have hinc : v ∈ e.val := by
    have h := newColor_every_edge_incident χ v hv
      (chosenNewEdge χ d) (chosenNewEdge_color χ d)
    simpa only [hd] using h
  refine ⟨v, hinc, ?_⟩
  change χ eTop ∈ newColors χ v
  simpa only [hcolor] using hv

/-- A host edge disjoint from both endpoints of a selected edge has
a different color from the selected edge. -/
theorem selected_edge_color_ne_of_disjoint
    (χ : TopEdgeLabeling (Fin n) C)
    (e : (newColorRepresentative χ).edgeSet)
    (f : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (hdisj : ∀ v : Fin n, v ∈ e.val → v ∉ f.val) :
    χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩ ≠ χ f := by
  obtain ⟨v, hve, hnew⟩ :=
    selected_edge_color_new_at_endpoint χ e
  intro heq
  have hvf := newColor_every_edge_incident χ v hnew f heq.symm
  exact (hdisj v hve) hvf

end ErdosProblems.AntiRamseyCycleSelectedNewEndpoint

namespace ErdosProblems.AntiRamseyCycleNewRepresentativeRainbow

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Restrict a complete-graph edge coloring to the selected NEW graph. -/
def restrictedNewColor (χ : TopEdgeLabeling (Fin n) C) :
    (newColorRepresentative χ).edgeSet → C :=
  fun e => χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩

/-- Every selected NEW-color edge has a distinct host label. -/
theorem restrictedNewColor_injective (χ : TopEdgeLabeling (Fin n) C) :
    Function.Injective (restrictedNewColor χ) := by
  intro e₁ e₂ heq
  have he₁ : e₁.val ∈
      Set.range (fun c : newColorUnion χ => (chosenNewEdge χ c).val) := by
    rw [← newColorRepresentative_edgeSet χ]
    exact e₁.property
  have he₂ : e₂.val ∈
      Set.range (fun c : newColorUnion χ => (chosenNewEdge χ c).val) := by
    rw [← newColorRepresentative_edgeSet χ]
    exact e₂.property
  obtain ⟨c₁, hc₁⟩ := he₁
  obtain ⟨c₂, hc₂⟩ := he₂
  have hcolor₁ : restrictedNewColor χ e₁ = c₁.val := by
    have hval : e₁.val = (chosenNewEdge χ c₁).val := hc₁.symm
    simpa [restrictedNewColor, hval] using chosenNewEdge_color χ c₁
  have hcolor₂ : restrictedNewColor χ e₂ = c₂.val := by
    have hval : e₂.val = (chosenNewEdge χ c₂).val := hc₂.symm
    simpa [restrictedNewColor, hval] using chosenNewEdge_color χ c₂
  have hcolors : c₁.val = c₂.val :=
    hcolor₁.symm.trans (heq.trans hcolor₂)
  have hc : c₁ = c₂ := Subtype.ext hcolors
  apply Subtype.ext
  calc
    e₁.val = (chosenNewEdge χ c₁).val := hc₁.symm
    _ = (chosenNewEdge χ c₂).val := by rw [hc]
    _ = e₂.val := hc₂

/-- A graph Copy in the selected NEW graph becomes a rainbow Copy in the
complete host, via its inclusion into `⊤`. -/
theorem copy_in_newColorRepresentative_isRainbow
    {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) C)
    (f : H.Copy (newColorRepresentative χ)) :
    IsRainbow ((Copy.ofLE (newColorRepresentative χ)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom χ := by
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (newColorRepresentative χ)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f
  change Function.Injective (EdgeLabeling.pullback χ g.toHom)
  have hcolors (e : H.edgeSet) :
      EdgeLabeling.pullback χ g.toHom e =
        restrictedNewColor χ (f.mapEdgeSet e) := by
    have hval : (g.toHom.mapEdgeSet e).val =
        (f.mapEdgeSet e).val := by
      simp [g, Copy.comp, Copy.ofLE, Hom.mapEdgeSet]
      rfl
    exact congrArg χ (Subtype.ext hval)
  intro e₁ e₂ hcolorsEq
  apply f.mapEdgeSet.injective
  exact restrictedNewColor_injective χ
    ((hcolors e₁).symm.trans (hcolorsEq.trans (hcolors e₂)))

/-- A no-rainbow host coloring forces its NEW-color representative to
contain no ordinary Copy of the same forbidden graph. -/
theorem newColorRepresentative_free {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ) :
    H.Free (newColorRepresentative χ) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact hno _ (copy_in_newColorRepresentative_isRainbow χ f)

/-- The literal Formal Conjectures no-rainbow-`cycleGraph k` premise
implies that the selected NEW graph is `cycleGraph k.Free`. -/
theorem newColorRepresentative_cycleGraph_free (k : ℕ)
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ) :
    (cycleGraph k).Free (newColorRepresentative χ) :=
  newColorRepresentative_free (cycleGraph k) χ hno

end ErdosProblems.AntiRamseyCycleNewRepresentativeRainbow

namespace ErdosProblems.AntiRamseyCycleFourNewWedge

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleSelectedNewEndpoint
open ErdosProblems.AntiRamseyCycleNewRepresentativeRainbow
open ErdosProblems.AntiRamseyCycleFour

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A selected edge, represented by its unordered endpoint pair. -/
def selectedPair (χ : TopEdgeLabeling (Fin n) C)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v) :
    (newColorRepresentative χ).edgeSet :=
  ⟨s(u, v), (SimpleGraph.mem_edgeSet _).mpr huv⟩

/-- The original host color of a selected edge. -/
def selectedEdgeColor (χ : TopEdgeLabeling (Fin n) C)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v) : C :=
  restrictedNewColor χ (selectedPair χ huv)

def squareMap (x u v y : Fin n) (i : Fin 4) : Fin n :=
  if i = 0 then x else if i = 1 then u else if i = 2 then v else y

theorem squareMap_injective {x u v y : Fin n}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxy : x ≠ y)
    (huv : u ≠ v) (huy : u ≠ y) (hvy : v ≠ y) :
    Function.Injective (squareMap x u v y) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [squareMap] at hij ⊢ <;> grind

/-- A distinct fourth vertex makes the wedge into a literal rainbow
`cycleGraph 4.Copy` in the original complete-graph coloring. -/
theorem rainbow_square_of_selected_new_wedge
    (χ : TopEdgeLabeling (Fin n) C) {u v x y : Fin n}
    (huv : (newColorRepresentative χ).Adj u v)
    (hux : (newColorRepresentative χ).Adj u x)
    (hvy : (newColorRepresentative χ).Adj v y)
    (hxv : x ≠ v) (hyu : y ≠ u) (hxy : x ≠ y)
    (hnewUX : selectedEdgeColor χ hux ∈ newColors χ u)
    (hnewVY : selectedEdgeColor χ hvy ∈ newColors χ v) :
    ∃ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  have hxu : x ≠ u := (newColorRepresentative χ).ne_of_adj hux.symm
  have huv' : u ≠ v := (newColorRepresentative χ).ne_of_adj huv
  have huy : u ≠ y := hyu.symm
  have hvy' : v ≠ y := (newColorRepresentative χ).ne_of_adj hvy
  have hρ : Function.Injective (squareMap x u v y) :=
    squareMap_injective hxu hxv hxy huv' huy hvy'
  let φ : (cycleGraph 4) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨squareMap x u v y, by
      intro i j hij
      exact (top_adj _ _).mpr (hρ.ne ((cycleGraph 4).ne_of_adj hij))⟩
  let f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hρ⟩
  let closing : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨s(y, x), (top_adj _ _).mpr hxy.symm⟩

  have h01_12 : selectedEdgeColor χ hux ≠ selectedEdgeColor χ huv := by
    intro hcol
    have he : selectedPair χ hux = selectedPair χ huv :=
      restrictedNewColor_injective χ hcol
    have hv := congrArg Subtype.val he
    change s(u, x) = s(u, v) at hv
    rcases (Sym2.eq_iff.mp hv) with hp | hp <;> grind
  have h01_23 : selectedEdgeColor χ hux ≠ selectedEdgeColor χ hvy := by
    intro hcol
    have he : selectedPair χ hux = selectedPair χ hvy :=
      restrictedNewColor_injective χ hcol
    have hv := congrArg Subtype.val he
    change s(u, x) = s(v, y) at hv
    rcases (Sym2.eq_iff.mp hv) with hp | hp <;> grind
  have h12_23 : selectedEdgeColor χ huv ≠ selectedEdgeColor χ hvy := by
    intro hcol
    have he : selectedPair χ huv = selectedPair χ hvy :=
      restrictedNewColor_injective χ hcol
    have hv := congrArg Subtype.val he
    change s(u, v) = s(v, y) at hv
    rcases (Sym2.eq_iff.mp hv) with hp | hp <;> grind

  have h01_30 : selectedEdgeColor χ hux ≠ χ closing := by
    intro hcol
    have huClosing : u ∈ closing.val :=
      newColor_every_edge_incident χ u hnewUX closing hcol.symm
    change u ∈ s(y, x) at huClosing
    rcases (Sym2.mem_iff.mp huClosing) with h | h <;> grind
  have h23_30 : selectedEdgeColor χ hvy ≠ χ closing := by
    intro hcol
    have hvClosing : v ∈ closing.val :=
      newColor_every_edge_incident χ v hnewVY closing hcol.symm
    change v ∈ s(y, x) at hvClosing
    rcases (Sym2.mem_iff.mp hvClosing) with h | h <;> grind
  have hdisj : ∀ z : Fin n, z ∈ (selectedPair χ huv).val →
      z ∉ closing.val := by
    intro z hz hzc
    change z ∈ s(u, v) at hz
    change z ∈ s(y, x) at hzc
    rcases (Sym2.mem_iff.mp hz) with h | h <;>
      rcases (Sym2.mem_iff.mp hzc) with h' | h' <;> grind
  have h12_30 : selectedEdgeColor χ huv ≠ χ closing := by
    exact selected_edge_color_ne_of_disjoint χ
      (selectedPair χ huv) closing hdisj

  have hcol01 : (EdgeLabeling.pullback χ f.toHom) sourceEdge01 =
      selectedEdgeColor χ hux := by
    change χ (f.toHom.mapEdgeSet sourceEdge01) =
      χ ⟨(selectedPair χ hux).val,
        SimpleGraph.edgeSet_mono le_top (selectedPair χ hux).property⟩
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((0 : Fin 4), 1)) = s(u, x)
    rw [Sym2.map_mk]
    simp [squareMap, Sym2.eq_swap]
  have hcol12 : (EdgeLabeling.pullback χ f.toHom) sourceEdge12 =
      selectedEdgeColor χ huv := by
    change χ (f.toHom.mapEdgeSet sourceEdge12) =
      χ ⟨(selectedPair χ huv).val,
        SimpleGraph.edgeSet_mono le_top (selectedPair χ huv).property⟩
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((1 : Fin 4), 2)) = s(u, v)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol23 : (EdgeLabeling.pullback χ f.toHom) sourceEdge23 =
      selectedEdgeColor χ hvy := by
    change χ (f.toHom.mapEdgeSet sourceEdge23) =
      χ ⟨(selectedPair χ hvy).val,
        SimpleGraph.edgeSet_mono le_top (selectedPair χ hvy).property⟩
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((2 : Fin 4), 3)) = s(v, y)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol30 : (EdgeLabeling.pullback χ f.toHom) sourceEdge30 =
      χ closing := by
    change χ (f.toHom.mapEdgeSet sourceEdge30) = χ closing
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((3 : Fin 4), 0)) = s(y, x)
    rw [Sym2.map_mk]
    simp [squareMap]

  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  rcases sourceEdge_cases e₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases sourceEdge_cases e₂ with h₂ | h₂ | h₂ | h₂ <;>
    subst e₁ <;> subst e₂ <;>
    simp_all

/-- Under the original no-rainbow premise, the two NEW-outward selected
edges of a selected edge have the same third endpoint. -/
theorem selected_new_wedge_eq
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    {u v x y : Fin n}
    (huv : (newColorRepresentative χ).Adj u v)
    (hux : (newColorRepresentative χ).Adj u x)
    (hvy : (newColorRepresentative χ).Adj v y)
    (hxv : x ≠ v) (hyu : y ≠ u)
    (hnewUX : selectedEdgeColor χ hux ∈ newColors χ u)
    (hnewVY : selectedEdgeColor χ hvy ∈ newColors χ v) :
    x = y := by
  by_contra hxy
  obtain ⟨f, hf⟩ := rainbow_square_of_selected_new_wedge χ
    huv hux hvy hxv hyu hxy hnewUX hnewVY
  exact hno f hf

end ErdosProblems.AntiRamseyCycleFourNewWedge

namespace ErdosProblems.AntiRamseyCycleNewOutsideWitness

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The other endpoint of the selected edge indexed by a NEW color at `v`. -/
noncomputable def newColorNeighbor (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) : Fin n :=
  ((newColorRepresentative χ).incidenceSetEquivNeighborSet v
    (newColorIncidenceEdge χ v c)).val

theorem newColorNeighbor_adj (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) :
    (newColorRepresentative χ).Adj v (newColorNeighbor χ v c) := by
  have hw : newColorNeighbor χ v c ∈
      (newColorRepresentative χ).neighborSet v :=
    ((newColorRepresentative χ).incidenceSetEquivNeighborSet v
      (newColorIncidenceEdge χ v c)).property
  exact ((newColorRepresentative χ).mem_neighborSet v _).mp hw

theorem newColorNeighbor_injective (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) : Function.Injective (newColorNeighbor χ v) := by
  intro a b hab
  have he :
      (newColorRepresentative χ).incidenceSetEquivNeighborSet v
          (newColorIncidenceEdge χ v a) =
      (newColorRepresentative χ).incidenceSetEquivNeighborSet v
          (newColorIncidenceEdge χ v b) := Subtype.ext hab
  have hinc : newColorIncidenceEdge χ v a =
      newColorIncidenceEdge χ v b :=
    ((newColorRepresentative χ).incidenceSetEquivNeighborSet v).injective he
  exact newColorIncidenceEdge_injective χ v hinc

theorem newColorIncidenceEdge_eq_pair (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) :
    (newColorIncidenceEdge χ v c).val =
      s(v, newColorNeighbor χ v c) := by
  have h :=
    ((newColorRepresentative χ).incidenceSetEquivNeighborSet v).symm_apply_apply
      (newColorIncidenceEdge χ v c)
  have hval := congrArg Subtype.val h
  change s(v, newColorNeighbor χ v c) =
    (newColorIncidenceEdge χ v c).val at hval
  exact hval.symm

theorem newColorIncidenceEdge_color (χ : TopEdgeLabeling (Fin n) C)
    (v : Fin n) (c : newColors χ v) :
    χ ⟨(newColorIncidenceEdge χ v c).val,
      SimpleGraph.edgeSet_mono le_top (newColorIncidenceEdge χ v c).property.1⟩ =
      c.val := by
  let d : newColorUnion χ :=
    ⟨c.val, mem_newColorUnion_of_mem χ v c.property⟩
  have hval : (newColorIncidenceEdge χ v c).val =
      (chosenNewEdge χ d).val := rfl
  have htop :
      (⟨(newColorIncidenceEdge χ v c).val,
        SimpleGraph.edgeSet_mono le_top
          (newColorIncidenceEdge χ v c).property.1⟩ :
        (⊤ : SimpleGraph (Fin n)).edgeSet) = chosenNewEdge χ d :=
    Subtype.ext hval
  rw [htop]
  exact chosenNewEdge_color χ d

/-- Finite pigeonhole: one indexed NEW(v) color selects a neighbor
outside `P` whenever its internal selected degree is too small. -/
theorem exists_newColorNeighbor_outside
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n)
    (P : Finset (Fin n))
    (hsmall : ((newColorRepresentative χ).neighborFinset v ∩ P).card <
      (newColors χ v).card) :
    ∃ c : newColors χ v, newColorNeighbor χ v c ∉ P := by
  classical
  by_contra h
  push Not at h
  let f : newColors χ v →
      ((newColorRepresentative χ).neighborFinset v ∩ P : Finset (Fin n)) := fun c =>
    ⟨newColorNeighbor χ v c, Finset.mem_inter.mpr
      ⟨((newColorRepresentative χ).mem_neighborFinset v _).mpr
          (newColorNeighbor_adj χ v c), h c⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hval : (f a).val = (f b).val := congrArg Subtype.val hab
    change newColorNeighbor χ v a = newColorNeighbor χ v b at hval
    exact newColorNeighbor_injective χ v hval
  have hcard : (newColors χ v).card ≤
      ((newColorRepresentative χ).neighborFinset v ∩ P).card :=
    Finset.card_le_card_of_injective hinj
  omega

/-- The witness is a selected edge `v-w` whose host label is NEW at the
endpoint `v` inside the finite set. This is the inward orientation used
when extending a selected tail path. -/
theorem exists_selected_newColor_edge_outside
    (χ : TopEdgeLabeling (Fin n) C) (v : Fin n)
    (P : Finset (Fin n))
    (hsmall : ((newColorRepresentative χ).neighborFinset v ∩ P).card <
      (newColors χ v).card) :
    ∃ w : Fin n, ∃ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
      w ∉ P ∧ (newColorRepresentative χ).Adj v w ∧
      e.val = s(v, w) ∧ χ e ∈ newColors χ v := by
  obtain ⟨c, hc⟩ := exists_newColorNeighbor_outside χ v P hsmall
  let w : Fin n := newColorNeighbor χ v c
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨(newColorIncidenceEdge χ v c).val,
      SimpleGraph.edgeSet_mono le_top (newColorIncidenceEdge χ v c).property.1⟩
  refine ⟨w, e, hc, newColorNeighbor_adj χ v c,
    newColorIncidenceEdge_eq_pair χ v c, ?_⟩
  have hcolor : χ e = c.val := newColorIncidenceEdge_color χ v c
  simpa only [hcolor] using c.property

end ErdosProblems.AntiRamseyCycleNewOutsideWitness

namespace ErdosProblems.AntiRamseyCycleFourNewTriangle

open SimpleGraph Finset
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewRepresentativeRainbow
open ErdosProblems.AntiRamseyCycleNewOutsideWitness
open ErdosProblems.AntiRamseyCycleFourNewWedge

variable {n : ℕ} {C : Type*} [DecidableEq C]

theorem newColorNeighbor_selectedColor
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin n)
    (c : newColors χ u) :
    selectedEdgeColor χ (newColorNeighbor_adj χ u c) = c.val := by
  have hedge :
      (⟨(selectedPair χ (newColorNeighbor_adj χ u c)).val,
        SimpleGraph.edgeSet_mono le_top
          (selectedPair χ (newColorNeighbor_adj χ u c)).property⟩ :
          (⊤ : SimpleGraph (Fin n)).edgeSet) =
      (⟨(newColorIncidenceEdge χ u c).val,
        SimpleGraph.edgeSet_mono le_top
          (newColorIncidenceEdge χ u c).property.1⟩ :
          (⊤ : SimpleGraph (Fin n)).edgeSet) := by
    apply Subtype.ext
    change s(u, newColorNeighbor χ u c) =
      (newColorIncidenceEdge χ u c).val
    exact (newColorIncidenceEdge_eq_pair χ u c).symm
  exact (congrArg χ hedge).trans (newColorIncidenceEdge_color χ u c)

theorem newColorNeighbor_selectedNEW
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin n)
    (c : newColors χ u) :
    selectedEdgeColor χ (newColorNeighbor_adj χ u c) ∈ newColors χ u := by
  rw [newColorNeighbor_selectedColor χ u c]
  exact c.property

/-- Choose one NEW-color-indexed selected neighbor other than a named
vertex. The chosen edge is oriented NEW at the current endpoint. -/
theorem exists_newColorNeighbor_ne
    (χ : TopEdgeLabeling (Fin n) C) (u v : Fin n)
    (hu : 2 ≤ (newColors χ u).card) :
    ∃ c : newColors χ u, newColorNeighbor χ u c ≠ v := by
  classical
  have hcap :
      ((newColorRepresentative χ).neighborFinset u ∩ ({v} : Finset (Fin n))).card ≤ 1 := by
    calc
      ((newColorRepresentative χ).neighborFinset u ∩ ({v} : Finset (Fin n))).card ≤
          ({v} : Finset (Fin n)).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = 1 := by simp
  have hsmall :
      ((newColorRepresentative χ).neighborFinset u ∩ ({v} : Finset (Fin n))).card <
        (newColors χ u).card := by omega
  obtain ⟨c, hc⟩ := exists_newColorNeighbor_outside χ u {v} hsmall
  exact ⟨c, by simpa only [Finset.mem_singleton] using hc⟩

theorem selectedColor_eq_of_newColorNeighbor_eq
    (χ : TopEdgeLabeling (Fin n) C)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v)
    (c : newColors χ u) (hc : newColorNeighbor χ u c = v) :
    selectedEdgeColor χ huv = c.val := by
  have hedge : selectedPair χ huv =
      selectedPair χ (newColorNeighbor_adj χ u c) := by
    apply Subtype.ext
    change s(u, v) = s(u, newColorNeighbor χ u c)
    rw [hc]
  exact (congrArg (restrictedNewColor χ) hedge).trans
    (newColorNeighbor_selectedColor χ u c)

/-- Every selected color is NEW at its first endpoint. The high-NEW
cardinality rules out an edge selected only from the other endpoint. -/
theorem selectedColor_new_first
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v) :
    selectedEdgeColor χ huv ∈ newColors χ u := by
  classical
  obtain ⟨d, hyu⟩ := exists_newColorNeighbor_ne χ v u (hnew v)
  let y : Fin n := newColorNeighbor χ v d
  have hvy : (newColorRepresentative χ).Adj v y :=
    newColorNeighbor_adj χ v d
  have hnewVY : selectedEdgeColor χ hvy ∈ newColors χ v :=
    newColorNeighbor_selectedNEW χ v d
  have hrange (c : newColors χ u) :
      newColorNeighbor χ u c = v ∨ newColorNeighbor χ u c = y := by
    by_cases hxv : newColorNeighbor χ u c = v
    · exact Or.inl hxv
    · have hux : (newColorRepresentative χ).Adj u (newColorNeighbor χ u c) :=
        newColorNeighbor_adj χ u c
      have hnewUX : selectedEdgeColor χ hux ∈ newColors χ u :=
        newColorNeighbor_selectedNEW χ u c
      exact Or.inr
        (selected_new_wedge_eq χ hno huv hux hvy hxv hyu hnewUX hnewVY)
  by_contra hnot
  have hconstant (c : newColors χ u) : newColorNeighbor χ u c = y := by
    rcases hrange c with hc | hc
    · have hcolor : selectedEdgeColor χ huv = c.val :=
        selectedColor_eq_of_newColorNeighbor_eq χ huv c hc
      have hnewUV : selectedEdgeColor χ huv ∈ newColors χ u := by
        rw [hcolor]
        exact c.property
      exact False.elim (hnot hnewUV)
    · exact hc
  have hinj : Function.Injective
      (fun _ : newColors χ u => (0 : Fin 1)) := by
    intro a b _
    exact newColorNeighbor_injective χ u
      ((hconstant a).trans (hconstant b).symm)
  have hcard : (newColors χ u).card ≤ 1 := by
    have h := Fintype.card_le_of_injective
      (fun _ : newColors χ u => (0 : Fin 1)) hinj
    simpa only [Fintype.card_coe, Fintype.card_fin] using h
  have hu2 := hnew u
  omega

/-- At k=4 with at least two NEW colors at each vertex, every edge
selected by the NEW representative has a host label NEW at *both*
endpoints. This strengthens the unconditional SOME-endpoint result. -/
theorem selected_edge_color_new_both
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v) :
    selectedEdgeColor χ huv ∈ newColors χ u ∧
      selectedEdgeColor χ huv ∈ newColors χ v := by
  refine ⟨selectedColor_new_first χ hno hnew huv, ?_⟩
  have hswap : selectedEdgeColor χ huv.symm = selectedEdgeColor χ huv := by
    apply congrArg (restrictedNewColor χ)
    apply Subtype.ext
    change s(v, u) = s(u, v)
    exact Sym2.eq_swap
  have hsecond := selectedColor_new_first χ hno hnew huv.symm
  rw [hswap] at hsecond
  exact hsecond

/-- Every vertex of the selected NEW representative has exactly two
selected neighbors, which are themselves adjacent. This is the local
`K₃` structure before passing to connected-component supports. -/
theorem selected_vertex_triangle
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    (u : Fin n) :
    ∃ v w : Fin n, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      (newColorRepresentative χ).Adj u v ∧
      (newColorRepresentative χ).Adj u w ∧
      (newColorRepresentative χ).Adj v w ∧
      (∀ z : Fin n, (newColorRepresentative χ).Adj u z ↔ z = v ∨ z = w) := by
  classical
  have hpos : 0 < (newColors χ u).card := by
    have hu2 := hnew u
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  let c₀ : newColors χ u := ⟨c, hc⟩
  let v : Fin n := newColorNeighbor χ u c₀
  have huv : (newColorRepresentative χ).Adj u v :=
    newColorNeighbor_adj χ u c₀
  obtain ⟨d, hwu⟩ := exists_newColorNeighbor_ne χ v u (hnew v)
  let w : Fin n := newColorNeighbor χ v d
  have hvw : (newColorRepresentative χ).Adj v w :=
    newColorNeighbor_adj χ v d
  have hnewVW : selectedEdgeColor χ hvw ∈ newColors χ v :=
    newColorNeighbor_selectedNEW χ v d
  obtain ⟨a, hxv⟩ := exists_newColorNeighbor_ne χ u v (hnew u)
  let x : Fin n := newColorNeighbor χ u a
  have hux : (newColorRepresentative χ).Adj u x :=
    newColorNeighbor_adj χ u a
  have hnewUX : selectedEdgeColor χ hux ∈ newColors χ u :=
    newColorNeighbor_selectedNEW χ u a
  have hxw : x = w :=
    selected_new_wedge_eq χ hno huv hux hvw hxv hwu hnewUX hnewVW
  have huw : (newColorRepresentative χ).Adj u w := by
    simpa only [hxw] using hux
  have hvw' : v ≠ w := by
    intro heq
    exact hxv (hxw.trans heq.symm)
  have hall (z : Fin n) :
      (newColorRepresentative χ).Adj u z ↔ z = v ∨ z = w := by
    constructor
    · intro huz
      by_cases hzv : z = v
      · exact Or.inl hzv
      · have hnewUZ : selectedEdgeColor χ huz ∈ newColors χ u :=
          (selected_edge_color_new_both χ hno hnew huz).1
        exact Or.inr
          (selected_new_wedge_eq χ hno huv huz hvw hzv hwu hnewUZ hnewVW)
    · rintro (rfl | rfl)
      · exact huv
      · exact huw
  exact ⟨v, w, huv.ne, (huw.ne), hvw', huv, huw, hvw, hall⟩

/-- Under the same hypotheses, degree and NEW count are exactly two
at every selected vertex. -/
theorem selected_vertex_degree_new_card_two
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    (u : Fin n) :
    (newColorRepresentative χ).degree u = 2 ∧
      (newColors χ u).card = 2 := by
  classical
  obtain ⟨v, w, huv, huw, hvw, _, _, _, hall⟩ :=
    selected_vertex_triangle χ hno hnew u
  let G : SimpleGraph (Fin n) := newColorRepresentative χ
  have hneighbor : G.neighborFinset u = {v, w} := by
    ext z
    simp only [G.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    exact hall z
  have hdegree : G.degree u = 2 := by
    change (G.neighborFinset u).card = 2
    rw [hneighbor]
    simp [hvw]
  have hlow := hnew u
  have hhigh := newColorRepresentative_degree_ge_newColors χ u
  have hdegree' : (newColorRepresentative χ).degree u = 2 := hdegree
  refine ⟨hdegree, ?_⟩
  omega

/-- The three selected vertices of a triangle have no selected edge
to a fourth vertex. Every such edge would create a second NEW wedge. -/
theorem selected_triangle_no_outer_neighbors
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    {u v w : Fin n}
    (huv : (newColorRepresentative χ).Adj u v)
    (huw : (newColorRepresentative χ).Adj u w)
    (hvw : (newColorRepresentative χ).Adj v w)
    (huw' : u ≠ w) (hvw' : v ≠ w) :
    (∀ z : Fin n, (newColorRepresentative χ).Adj u z → z = v ∨ z = w) ∧
    (∀ z : Fin n, (newColorRepresentative χ).Adj v z → z = u ∨ z = w) ∧
    (∀ z : Fin n, (newColorRepresentative χ).Adj w z → z = u ∨ z = v) := by
  have hnewUV := (selected_edge_color_new_both χ hno hnew huv).1
  have hnewUW := (selected_edge_color_new_both χ hno hnew huw).1
  have hnewVW := (selected_edge_color_new_both χ hno hnew hvw).1
  refine ⟨?_, ?_, ?_⟩
  · intro z huz
    by_cases hzv : z = v
    · exact Or.inl hzv
    · have hnewUZ := (selected_edge_color_new_both χ hno hnew huz).1
      exact Or.inr
        (selected_new_wedge_eq χ hno huv huz hvw hzv huw'.symm
          hnewUZ hnewVW)
  · intro z hvz
    by_cases hzu : z = u
    · exact Or.inl hzu
    · have hnewVZ := (selected_edge_color_new_both χ hno hnew hvz).1
      exact Or.inr
        (selected_new_wedge_eq χ hno huv.symm hvz huw hzu hvw'.symm
          hnewVZ hnewUW)
  · intro z hwz
    by_cases hzu : z = u
    · exact Or.inl hzu
    · have hnewWZ := (selected_edge_color_new_both χ hno hnew hwz).1
      exact Or.inr
        (selected_new_wedge_eq χ hno huw.symm hwz huv hzu hvw'
          hnewWZ hnewUV)

/-- Every connected component of the selected NEW representative has
exactly the support of one selected triangle. -/
theorem selected_component_is_triangle
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    (D : (newColorRepresentative χ).ConnectedComponent) :
    ∃ u v w : Fin n, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      D.supp = ({u, v, w} : Set (Fin n)) ∧
      (newColorRepresentative χ).Adj u v ∧
      (newColorRepresentative χ).Adj u w ∧
      (newColorRepresentative χ).Adj v w := by
  classical
  let G : SimpleGraph (Fin n) := newColorRepresentative χ
  obtain ⟨u, huD⟩ := D.nonempty_supp
  obtain ⟨v, w, huv', huw', hvw', huv, huw, hvw, _⟩ :=
    selected_vertex_triangle χ hno hnew u
  obtain ⟨honlyU, honlyV, honlyW⟩ :=
    selected_triangle_no_outer_neighbors χ hno hnew
      huv huw hvw huw' hvw'
  let S : Set (Fin n) := {u, v, w}
  have hclosed : ∀ a b : Fin n, a ∈ S → G.Adj a b → b ∈ S := by
    intro a b ha hab
    have ha' : a = u ∨ a = v ∨ a = w := by
      simpa [S] using ha
    rcases ha' with rfl | rfl | rfl
    · rcases honlyU b hab with rfl | rfl <;> simp [S]
    · rcases honlyV b hab with rfl | rfl <;> simp [S]
    · rcases honlyW b hab with rfl | rfl <;> simp [S]
  have hgenS : ∀ z : Fin n, Relation.ReflTransGen G.Adj u z → z ∈ S := by
    intro z hz
    induction hz with
    | refl => simp [S]
    | tail _ hab ih => exact hclosed _ _ ih hab
  have hreachS (z : Fin n) (hz : G.Reachable u z) : z ∈ S :=
    hgenS z ((G.reachable_iff_reflTransGen u z).mp hz)
  have hsubset : D.supp ⊆ S := by
    intro z hz
    have hu : G.connectedComponentMk u = D :=
      (D.mem_supp_iff u).mp huD
    have hz' : G.connectedComponentMk z = D :=
      (D.mem_supp_iff z).mp hz
    have hreach : G.Reachable u z :=
      ConnectedComponent.eq.mp (hu.trans hz'.symm)
    exact hreachS z hreach
  have hsupset : S ⊆ D.supp := by
    intro z hz
    have hz' : z = u ∨ z = v ∨ z = w := by
      simpa [S] using hz
    rcases hz' with rfl | rfl | rfl
    · exact huD
    · exact D.mem_supp_of_adj_mem_supp huD huv
    · exact D.mem_supp_of_adj_mem_supp huD huw
  have hsupport : D.supp = S := Set.Subset.antisymm hsubset hsupset
  exact ⟨u, v, w, huv', huw', hvw', hsupport, huv, huw, hvw⟩

/-- The exact selected-component order at k=4 is three. -/
theorem selected_component_card_three
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    (D : (newColorRepresentative χ).ConnectedComponent) :
    D.supp.ncard = 3 := by
  classical
  obtain ⟨u, v, w, huv, huw, hvw, hsupport, _, _, _⟩ :=
    selected_component_is_triangle χ hno hnew D
  rw [hsupport, Set.ncard_eq_toFinset_card]
  simp [huv, huw, hvw]

end ErdosProblems.AntiRamseyCycleFourNewTriangle

namespace ErdosProblems.AntiRamseyCycleFourTriangleQuotient

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyWeakCount
open ErdosProblems.AntiRamseyCycleFour

/-- Explicit conditional interface: each color on an edge internal to a
block is NEW at both endpoints. Its host occurrence is then unique. -/
def TriangleBlockOwnColors {n t : ℕ} {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C) (b : Fin n → Fin t) : Prop :=
  ∀ (a d : Fin n) (had : a ≠ d), b a = b d →
    χ.get a d had ∈ newColors χ a ∧ χ.get a d had ∈ newColors χ d

/-- Bridge from the explicit two-NEW premise to the
globally unique host occurrence of an internal edge color. -/
theorem within_block_color_unique_edge {n t : ℕ} {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C) (b : Fin n → Fin t)
    (hown : TriangleBlockOwnColors χ b)
    (a d : Fin n) (had : a ≠ d) (hbd : b a = b d)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (he : χ e = χ.get a d had) : e.val = s(a, d) := by
  obtain ⟨ha, hd⟩ := hown a d had hbd
  exact shared_newColor_unique_edge χ a d had ha hd e he

/-- Rewriting of the unique-host-color conclusion for
the `get` form of a second edge. -/
theorem within_block_color_collision_pair {n t : ℕ} {C : Type*}
    [DecidableEq C] (χ : TopEdgeLabeling (Fin n) C)
    (b : Fin n → Fin t) (hown : TriangleBlockOwnColors χ b)
    (a d : Fin n) (had : a ≠ d) (hbd : b a = b d)
    (u v : Fin n) (huv : u ≠ v)
    (hcolor : χ.get u v huv = χ.get a d had) :
    s(u, v) = s(a, d) := by
  let e : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨s(u, v), (top_adj _ _).mpr huv⟩
  have he : χ e = χ.get a d had := by
    change χ.get u v huv = χ.get a d had
    exact hcolor
  exact within_block_color_unique_edge χ b hown a d had hbd e he

/-- Opposite cross-grid equalities on a pair of sets
with third points force every entry to be equal. The third-point hypotheses
are later supplied by three-vertex block fibers. -/
theorem opposite_cross_matrix_constant {A B C : Type*} (M : A → B → C)
    (hthirdA : ∀ a a' : A, ∃ a'' : A, a'' ≠ a ∧ a'' ≠ a')
    (hthirdB : ∀ b b' : B, ∃ b'' : B, b'' ≠ b ∧ b'' ≠ b')
    (hopp : ∀ (a a' : A) (b b' : B), a ≠ a' → b ≠ b' →
      M a b = M a' b') :
    ∀ (a a' : A) (b b' : B), M a b = M a' b' := by
  intro a a' b b'
  by_cases haa : a = a'
  · subst a'
    by_cases hbb : b = b'
    · subst b'
      rfl
    · obtain ⟨a'', haother, _⟩ := hthirdA a a
      obtain ⟨b'', hbother, hb'other⟩ := hthirdB b b'
      calc
        M a b = M a'' b'' := hopp a a'' b b'' haother.symm hbother.symm
        _ = M a b' := (hopp a a'' b' b'' haother.symm hb'other.symm).symm
  · by_cases hbb : b = b'
    · subst b'
      obtain ⟨a'', haother, ha'other⟩ := hthirdA a a'
      obtain ⟨b'', hbother, _⟩ := hthirdB b b
      calc
        M a b = M a'' b'' := hopp a a'' b b'' haother.symm hbother.symm
        _ = M a' b := (hopp a' a'' b b'' ha'other.symm hbother.symm).symm
    · exact hopp a a' b b' haa hbb

/-- Finite version of the third-point premise. -/
theorem third_vertex_of_three_le_card {A : Type*} [DecidableEq A]
    (S : Finset A) (hcard : 3 ≤ S.card) (a d : A) :
    ∃ z ∈ S, z ≠ a ∧ z ≠ d := by
  have hlt : 2 < S.card := by omega
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
    Finset.two_lt_card.mp hlt
  by_cases hpa : p ≠ a ∧ p ≠ d
  · exact ⟨p, hp, hpa.1, hpa.2⟩
  by_cases hqa : q ≠ a ∧ q ≠ d
  · exact ⟨q, hq, hqa.1, hqa.2⟩
  push Not at hpa hqa
  exact ⟨r, hr, by grind, by grind⟩

def squareMap {n : ℕ} (x u v y : Fin n) (i : Fin 4) : Fin n :=
  if i = 0 then x else if i = 1 then u else if i = 2 then v else y

theorem squareMap_injective {n : ℕ} {x u v y : Fin n}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxy : x ≠ y)
    (huv : u ≠ v) (huy : u ≠ y) (hvy : v ≠ y) :
    Function.Injective (squareMap x u v y) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [squareMap] at hij ⊢ <;> grind

/-- Generic host-square constructor. Six unequal edge
labels on four distinct host vertices produce a literal rainbow ordinary
`C₄.Copy`. -/
theorem rainbow_square_of_six_color_inequalities {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) {x u v y : Fin n}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxy : x ≠ y)
    (huv : u ≠ v) (huy : u ≠ y) (hvy : v ≠ y)
    (h01_12 : χ.get x u hxu ≠ χ.get u v huv)
    (h01_23 : χ.get x u hxu ≠ χ.get v y hvy)
    (h01_30 : χ.get x u hxu ≠ χ.get y x hxy.symm)
    (h12_23 : χ.get u v huv ≠ χ.get v y hvy)
    (h12_30 : χ.get u v huv ≠ χ.get y x hxy.symm)
    (h23_30 : χ.get v y hvy ≠ χ.get y x hxy.symm) :
    ∃ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  have hρ : Function.Injective (squareMap x u v y) :=
    squareMap_injective hxu hxv hxy huv huy hvy
  let φ : (cycleGraph 4) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨squareMap x u v y, by
      intro i j hij
      exact (top_adj _ _).mpr (hρ.ne ((cycleGraph 4).ne_of_adj hij))⟩
  let f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hρ⟩
  have hcol01 : (EdgeLabeling.pullback χ f.toHom) sourceEdge01 =
      χ.get x u hxu := by
    change χ (f.toHom.mapEdgeSet sourceEdge01) = χ.get x u hxu
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((0 : Fin 4), 1)) = s(x, u)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol12 : (EdgeLabeling.pullback χ f.toHom) sourceEdge12 =
      χ.get u v huv := by
    change χ (f.toHom.mapEdgeSet sourceEdge12) = χ.get u v huv
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((1 : Fin 4), 2)) = s(u, v)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol23 : (EdgeLabeling.pullback χ f.toHom) sourceEdge23 =
      χ.get v y hvy := by
    change χ (f.toHom.mapEdgeSet sourceEdge23) = χ.get v y hvy
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((2 : Fin 4), 3)) = s(v, y)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol30 : (EdgeLabeling.pullback χ f.toHom) sourceEdge30 =
      χ.get y x hxy.symm := by
    change χ (f.toHom.mapEdgeSet sourceEdge30) = χ.get y x hxy.symm
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((3 : Fin 4), 0)) = s(y, x)
    rw [Sym2.map_mk]
    simp [squareMap]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  rcases sourceEdge_cases e₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases sourceEdge_cases e₂ with h₂ | h₂ | h₂ | h₂ <;>
    subst e₁ <;> subst e₂ <;>
    simp_all

/-- Two same-block internal edges with globally unique
colors force the opposite pair of cross edges to have the same color. No selected adjacency is assumed for the two cross edges. -/
theorem opposite_cross_colors_eq {n t : ℕ} {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (b : Fin n → Fin t) (hown : TriangleBlockOwnColors χ b)
    {x u v y : Fin n}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxy : x ≠ y)
    (huv : u ≠ v) (huy : u ≠ y) (hvy : v ≠ y)
    (hblockA : b x = b u) (hblockB : b v = b y) :
    χ.get u v huv = χ.get y x hxy.symm := by
  have h01_12 : χ.get x u hxu ≠ χ.get u v huv := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      x u hxu hblockA u v huv hcolor.symm
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  have h01_23 : χ.get x u hxu ≠ χ.get v y hvy := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      x u hxu hblockA v y hvy hcolor.symm
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  have h01_30 : χ.get x u hxu ≠ χ.get y x hxy.symm := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      x u hxu hblockA y x hxy.symm hcolor.symm
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  have h12_23 : χ.get u v huv ≠ χ.get v y hvy := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      v y hvy hblockB u v huv hcolor
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  have h23_30 : χ.get v y hvy ≠ χ.get y x hxy.symm := by
    intro hcolor
    have hp := within_block_color_collision_pair χ b hown
      v y hvy hblockB y x hxy.symm hcolor.symm
    rcases Sym2.eq_iff.mp hp with h | h <;> grind
  by_contra h12_30
  obtain ⟨f, hf⟩ := rainbow_square_of_six_color_inequalities χ
    hxu hxv hxy huv huy hvy h01_12 h01_23 h01_30
    h12_23 h12_30 h23_30
  exact hno f hf

/-- All cross edges between two three-vertex fibers
have the same color. The opposite-corner equalities are transported to
the two fiber subtype index sets before applying the pure matrix lemma. -/
theorem cross_color_constant_on_triangle_blocks {n t : ℕ}
    {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (b : Fin n → Fin t)
    (hsize : ∀ i : Fin t, (blockFiber b i).card = 3)
    (hown : TriangleBlockOwnColors χ b)
    (i j : Fin t) (hij : i ≠ j)
    (a d : Fin n) (had : a ≠ d) (ha : b a = i) (hd : b d = j)
    (a' d' : Fin n) (had' : a' ≠ d') (ha' : b a' = i)
    (hd' : b d' = j) :
    χ.get a d had = χ.get a' d' had' := by
  let A : Type := {v : Fin n // b v = i}
  let B : Type := {v : Fin n // b v = j}
  have hcross : ∀ (x : A) (y : B), x.val ≠ y.val := by
    intro x y heq
    apply hij
    calc
      i = b x.val := x.property.symm
      _ = b y.val := congrArg b heq
      _ = j := y.property
  let M : A → B → C := fun x y => χ.get x.val y.val (hcross x y)
  have hThirdA : ∀ x x' : A, ∃ z : A, z ≠ x ∧ z ≠ x' := by
    intro x x'
    obtain ⟨z, hz, hzx, hzx'⟩ :=
      third_vertex_of_three_le_card (blockFiber b i)
        (by simp [hsize i]) x.val x'.val
    have hzblock : b z = i := by simpa [blockFiber] using hz
    refine ⟨⟨z, hzblock⟩, ?_, ?_⟩
    · intro heq
      exact hzx (congrArg Subtype.val heq)
    · intro heq
      exact hzx' (congrArg Subtype.val heq)
  have hThirdB : ∀ y y' : B, ∃ z : B, z ≠ y ∧ z ≠ y' := by
    intro y y'
    obtain ⟨z, hz, hzy, hzy'⟩ :=
      third_vertex_of_three_le_card (blockFiber b j)
        (by simp [hsize j]) y.val y'.val
    have hzblock : b z = j := by simpa [blockFiber] using hz
    refine ⟨⟨z, hzblock⟩, ?_, ?_⟩
    · intro heq
      exact hzy (congrArg Subtype.val heq)
    · intro heq
      exact hzy' (congrArg Subtype.val heq)
  have hOpp : ∀ (x x' : A) (y y' : B), x ≠ x' → y ≠ y' →
      M x y = M x' y' := by
    intro x x' y y' hxx' hyy'
    have hxx'val : x.val ≠ x'.val := by
      intro heq
      exact hxx' (Subtype.ext heq)
    have hyy'val : y.val ≠ y'.val := by
      intro heq
      exact hyy' (Subtype.ext heq)
    have hop : χ.get x.val y.val (hcross x y) =
        χ.get y'.val x'.val (hcross x' y').symm :=
      opposite_cross_colors_eq χ hno b hown
        hxx'val.symm (hcross x' y) (hcross x' y')
        (hcross x y) (hcross x y') hyy'val
        (x'.property.trans x.property.symm)
        (y.property.trans y'.property.symm)
    change χ.get x.val y.val (hcross x y) =
      χ.get x'.val y'.val (hcross x' y')
    calc
      χ.get x.val y.val (hcross x y) =
          χ.get y'.val x'.val (hcross x' y').symm := hop
      _ = χ.get x'.val y'.val (hcross x' y') := by
        simpa using (SimpleGraph.EdgeLabeling.get_comm (C := χ)
          x'.val y'.val (hcross x' y').symm)
  have hconstant := opposite_cross_matrix_constant M hThirdA hThirdB hOpp
  let aa : A := ⟨a, ha⟩
  let aa' : A := ⟨a', ha'⟩
  let dd : B := ⟨d, hd⟩
  let dd' : B := ⟨d', hd'⟩
  simpa [M, aa, aa', dd, dd'] using hconstant aa aa' dd dd'

/-- Conditional `k = 4` color quotient from an explicit partition into
three-vertex fibers whose internal edge colors are NEW at both endpoints.
The selected-triangle component-to-fiber construction is separate. -/
theorem triangle_block_quotient {n t : ℕ} {C : Type*} [DecidableEq C]
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (b : Fin n → Fin t) (_ht : 1 ≤ t)
    (hsize : ∀ i : Fin t, (blockFiber b i).card = 3)
    (hown : TriangleBlockOwnColors χ b) :
    ∃ ψ : TopEdgeLabeling (Fin t) C,
      (∀ (a d : Fin n) (had : a ≠ d) (hbd : b a ≠ b d),
        χ.get a d had = ψ.get (b a) (b d) hbd) ∧
      ErdosProblems.AntiRamseyTriangle.NoRainbowTriangle ψ := by
  classical
  have hnonempty : ∀ i : Fin t, ∃ a : Fin n, b a = i := by
    intro i
    have hpos : 0 < (blockFiber b i).card := by simp [hsize i]
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    exact ⟨a, by simpa [blockFiber] using ha⟩
  choose r hr using hnonempty
  have hinj : Function.Injective r := by
    intro i j heq
    calc
      i = b (r i) := (hr i).symm
      _ = b (r j) := congrArg b heq
      _ = j := hr j
  let emb : Fin t ↪ Fin n := ⟨r, hinj⟩
  let ψ : TopEdgeLabeling (Fin t) C := TopEdgeLabeling.pullback χ emb
  have hpull : ∀ (i j : Fin t) (hij : i ≠ j),
      ψ.get i j hij = χ.get (r i) (r j) (hinj.ne hij) := by
    intro i j hij
    simp [ψ, emb, TopEdgeLabeling.pullback, EdgeLabeling.get,
      EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk]
  have hcrosslabel : ∀ (a d : Fin n) (had : a ≠ d)
      (hbd : b a ≠ b d),
      χ.get a d had = ψ.get (b a) (b d) hbd := by
    intro a d had hbd
    have hrepne : r (b a) ≠ r (b d) := hinj.ne hbd
    have hconst := cross_color_constant_on_triangle_blocks χ hno b
      hsize hown (b a) (b d) hbd
      a d had rfl rfl (r (b a)) (r (b d)) hrepne
      (hr (b a)) (hr (b d))
    calc
      χ.get a d had = χ.get (r (b a)) (r (b d)) hrepne := hconst
      _ = ψ.get (b a) (b d) hbd := (hpull (b a) (b d) hbd).symm
  have htriple : ErdosProblems.AntiRamseyTriangle.NoRainbowTriangle ψ := by
    intro i j k hij hjk hki
    by_contra hrepeat
    have hdiff12_23 : ψ.get i j hij ≠ ψ.get j k hjk := by
      intro heq
      exact hrepeat (Or.inl heq)
    have hdiff23_30 : ψ.get j k hjk ≠ ψ.get k i hki := by
      intro heq
      exact hrepeat (Or.inr (Or.inl heq))
    have hdiff30_12 : ψ.get k i hki ≠ ψ.get i j hij := by
      intro heq
      exact hrepeat (Or.inr (Or.inr heq))
    obtain ⟨z, hz, hzr, _⟩ :=
      third_vertex_of_three_le_card (blockFiber b i)
        (by simp [hsize i]) (r i) (r i)
    have hzi : b z = i := by simpa [blockFiber] using hz
    have hzrj : z ≠ r j := by
      intro heq
      apply hij
      calc
        i = b z := hzi.symm
        _ = b (r j) := congrArg b heq
        _ = j := hr j
    have hzrk : z ≠ r k := by
      intro heq
      apply hki
      calc
        k = b (r k) := (hr k).symm
        _ = b z := congrArg b heq.symm
        _ = i := hzi
    have hrij : r i ≠ r j := hinj.ne hij
    have hrik : r i ≠ r k := hinj.ne hki.symm
    have hrjk : r j ≠ r k := hinj.ne hjk
    have hcol12 : χ.get (r i) (r j) hrij = ψ.get i j hij := by
      have hbd : b (r i) ≠ b (r j) := by simpa [hr i, hr j] using hij
      simpa [hr i, hr j] using hcrosslabel (r i) (r j) hrij hbd
    have hcol23 : χ.get (r j) (r k) hrjk = ψ.get j k hjk := by
      have hbd : b (r j) ≠ b (r k) := by simpa [hr j, hr k] using hjk
      simpa [hr j, hr k] using hcrosslabel (r j) (r k) hrjk hbd
    have hcol30 : χ.get (r k) z hzrk.symm = ψ.get k i hki := by
      have hbd : b (r k) ≠ b z := by simpa [hr k, hzi] using hki
      simpa [hr k, hzi] using hcrosslabel (r k) z hzrk.symm hbd
    have hblock : b z = b (r i) := hzi.trans (hr i).symm
    have h01_12 : χ.get z (r i) hzr ≠ χ.get (r i) (r j) hrij := by
      intro heq
      have hp := within_block_color_collision_pair χ b hown
        z (r i) hzr hblock (r i) (r j) hrij heq.symm
      rcases Sym2.eq_iff.mp hp with h | h <;> grind
    have h01_23 : χ.get z (r i) hzr ≠ χ.get (r j) (r k) hrjk := by
      intro heq
      have hp := within_block_color_collision_pair χ b hown
        z (r i) hzr hblock (r j) (r k) hrjk heq.symm
      rcases Sym2.eq_iff.mp hp with h | h <;> grind
    have h01_30 : χ.get z (r i) hzr ≠ χ.get (r k) z hzrk.symm := by
      intro heq
      have hp := within_block_color_collision_pair χ b hown
        z (r i) hzr hblock (r k) z hzrk.symm heq.symm
      rcases Sym2.eq_iff.mp hp with h | h <;> grind
    have h12_23 : χ.get (r i) (r j) hrij ≠
        χ.get (r j) (r k) hrjk := by
      simpa only [hcol12, hcol23] using hdiff12_23
    have h12_30 : χ.get (r i) (r j) hrij ≠
        χ.get (r k) z hzrk.symm := by
      simpa only [hcol12, hcol30] using hdiff30_12.symm
    have h23_30 : χ.get (r j) (r k) hrjk ≠
        χ.get (r k) z hzrk.symm := by
      simpa only [hcol23, hcol30] using hdiff23_30
    obtain ⟨f, hf⟩ := rainbow_square_of_six_color_inequalities χ
      hzr hzrj hzrk hrij hrik hrjk h01_12 h01_23 h01_30
      h12_23 h12_30 h23_30
    exact hno f hf
  exact ⟨ψ, hcrosslabel, htriple⟩

end ErdosProblems.AntiRamseyCycleFourTriangleQuotient

namespace ErdosProblems.AntiRamseyCycleFourTrianglePartition

open SimpleGraph Finset
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleFourNewWedge
open ErdosProblems.AntiRamseyCycleFourNewTriangle
open ErdosProblems.AntiRamseyCycleFourTriangleQuotient
open ErdosProblems.AntiRamseyWeakCount

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Two distinct vertices in one selected connected component are joined
by one of its three selected triangle edges. -/
theorem selected_adj_of_same_component
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card)
    {a d : Fin n} (had : a ≠ d)
    (hcomp : (newColorRepresentative χ).connectedComponentMk a =
      (newColorRepresentative χ).connectedComponentMk d) :
    (newColorRepresentative χ).Adj a d := by
  classical
  let G : SimpleGraph (Fin n) := newColorRepresentative χ
  let D : G.ConnectedComponent := G.connectedComponentMk a
  obtain ⟨u, v, w, _, _, _, hD, huv, huw, hvw⟩ :=
    selected_component_is_triangle χ hno hnew D
  have haD : a ∈ D.supp := ConnectedComponent.connectedComponentMk_mem
  have hdD : d ∈ D.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact hcomp.symm
  have ha : a = u ∨ a = v ∨ a = w := by
    simpa [hD] using haD
  have hd : d = u ∨ d = v ∨ d = w := by
    simpa [hD] using hdD
  rcases ha with rfl | rfl | rfl
  · rcases hd with rfl | rfl | rfl
    · exact False.elim (had rfl)
    · exact huv
    · exact huw
  · rcases hd with rfl | rfl | rfl
    · exact huv.symm
    · exact False.elim (had rfl)
    · exact hvw
  · rcases hd with rfl | rfl | rfl
    · exact huw.symm
    · exact hvw.symm
    · exact False.elim (had rfl)

/-- The checked k=4 wedge component statement yields a total partition
into selected three-vertex blocks. Every internal host color is NEW at both
ends. The `4≤n` premise is inherited from `HighNewWeakStructure 4` and
ensures a positive number of blocks. -/
theorem selected_triangle_component_partition
    (χ : TopEdgeLabeling (Fin n) C)
    (hn : 4 ≤ n)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (hnew : ∀ z : Fin n, 2 ≤ (newColors χ z).card) :
    ∃ (t : ℕ) (b : Fin n → Fin t),
      1 ≤ t ∧
      (∀ i : Fin t, (blockFiber b i).card = 3) ∧
      (∀ (a d : Fin n) (_had : a ≠ d), b a = b d →
        (newColorRepresentative χ).Adj a d) ∧
      TriangleBlockOwnColors χ b ∧
      (∑ i : Fin t, (blockFiber b i).card = n) := by
  classical
  let G : SimpleGraph (Fin n) := newColorRepresentative χ
  let t : ℕ := Fintype.card G.ConnectedComponent
  let e : G.ConnectedComponent ≃ Fin t := Fintype.equivFin G.ConnectedComponent
  let b : Fin n → Fin t := fun v => e (G.connectedComponentMk v)
  have hn0 : 0 < n := by omega
  let z : Fin n := ⟨0, hn0⟩
  have htpos : 0 < t := by
    dsimp [t]
    exact Finset.card_pos.mpr ⟨G.connectedComponentMk z, Finset.mem_univ _⟩
  have ht : 1 ≤ t := by omega
  have hfiber (i : Fin t) : blockFiber b i = (e.symm i).supp.toFinset := by
    ext v
    simpa [blockFiber, b, ConnectedComponent.mem_supp_iff] using
      (e.eq_symm_apply (x := i) (y := G.connectedComponentMk v)).symm
  have hsize (i : Fin t) : (blockFiber b i).card = 3 := by
    calc
      (blockFiber b i).card = (e.symm i).supp.toFinset.card :=
        congrArg Finset.card (hfiber i)
      _ = (e.symm i).supp.ncard :=
        (Set.ncard_eq_toFinset_card' (e.symm i).supp).symm
      _ = 3 := selected_component_card_three χ hno hnew (e.symm i)
  have hselected (a d : Fin n) (had : a ≠ d) (hbd : b a = b d) :
      G.Adj a d := by
    have hcomp : G.connectedComponentMk a = G.connectedComponentMk d :=
      e.injective hbd
    exact selected_adj_of_same_component χ hno hnew had hcomp
  have hown : TriangleBlockOwnColors χ b := by
    intro a d had hbd
    have hadj : G.Adj a d := hselected a d had hbd
    have hcol : selectedEdgeColor χ hadj = χ.get a d had := rfl
    have hboth := selected_edge_color_new_both χ hno hnew hadj
    rw [hcol] at hboth
    exact hboth
  have hsum : ∑ i : Fin t, (blockFiber b i).card = n := by
    have h : (Finset.univ : Finset (Fin n)).card =
        ∑ i : Fin t, ((Finset.univ : Finset (Fin n)).filter
          (fun v => b v = i)).card :=
      Finset.card_eq_sum_card_fiberwise (by simp)
    simpa [blockFiber] using h.symm
  exact ⟨t, b, ht, hsize, hselected, hown, hsum⟩

end ErdosProblems.AntiRamseyCycleFourTrianglePartition

namespace ErdosProblems.AntiRamseyCycleFourHighNewStructure

open SimpleGraph Asymptotics Filter
open ErdosProblems.AntiRamseyWeakCount
open ErdosProblems.AntiRamseyConditionalCycleUpper
open ErdosProblems.AntiRamseyConditionalAsymptotic
open ErdosProblems.AntiRamseyCycleFourTrianglePartition
open ErdosProblems.AntiRamseyCycleFourTriangleQuotient

/-- Weak-block decomposition theorem `HighNewWeakStructure 4` for `C_4`-free
host colorings in which every vertex has at least two private colors. -/
theorem highNewWeakStructure_four : HighNewWeakStructure 4 := by
  intro n q hn χ hno hnew _hpair
  obtain ⟨t, b, ht, hsize, _, hown, hsum⟩ :=
    selected_triangle_component_partition χ hn hno hnew
  obtain ⟨ψ, hcross, htriangle⟩ :=
    triangle_block_quotient χ hno b ht hsize hown
  refine ⟨t, b, ψ, ht, hcross, htriangle, ?_, ?_, hsum⟩
  · intro i
    rw [hsize i]
    omega
  · intro i
    rw [hsize i]

/-- The `k = 4` specialization of the cycle asymptotic formula. -/
theorem cycle_four_asymptotic_formalConjectures :
    ((fun n : ℕ => (antiRamseyNum (cycleGraph 4) n : ℝ) -
      ((4 - 2 : ℝ) / 2 + 1 / (4 - 1)) * n)
      =O[Filter.atTop] (fun _ => (1 : ℝ))) := by
  exact cycle_asymptotic_of_highNewWeakStructure 4 (by omega)
    highNewWeakStructure_four

end ErdosProblems.AntiRamseyCycleFourHighNewStructure

namespace ErdosProblems.AntiRamseyCycleQuotientTriangleLengths

def trianglePathL (k b : ℕ) : ℕ := min b (k - 2)

def trianglePathT (k b : ℕ) : ℕ := k - 1 - trianglePathL k b

/-- The literal split leaves one vertex for the first component. In particular,
T may equal one; no extra orientation or prescribed endpoints are required. -/
theorem triangle_path_lengths_bounds {k b c : ℕ}
    (hk : 5 ≤ k) (hb : 3 ≤ b) (hc : 3 ≤ c) (hbc : k + 1 ≤ b + c) :
    1 ≤ trianglePathL k b ∧ trianglePathL k b ≤ b ∧
      1 ≤ trianglePathT k b ∧ trianglePathT k b ≤ c ∧
      trianglePathL k b + trianglePathT k b + 1 = k := by
  simp only [trianglePathT, trianglePathL]
  by_cases hmin : b ≤ k - 2
  · rw [Nat.min_eq_left hmin]
    omega
  · rw [Nat.min_eq_right (by omega : k - 2 ≤ b)]
    omega

/-- The exact two component lower-order bounds supply the same split.
No upper-order premise is needed for this numeric auxiliary. -/
theorem triangle_path_lengths_of_component_lower_bounds {k b c : ℕ}
    (hk : 5 ≤ k) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (hbLower : k + 1 ≤ 2 * b) (hcLower : k + 1 ≤ 2 * c) :
    1 ≤ trianglePathL k b ∧ trianglePathL k b ≤ b ∧
      1 ≤ trianglePathT k b ∧ trianglePathT k b ≤ c ∧
      trianglePathL k b + trianglePathT k b + 1 = k := by
  exact triangle_path_lengths_bounds hk hb hc (by omega)

end ErdosProblems.AntiRamseyCycleQuotientTriangleLengths

namespace ErdosProblems.AntiRamseyCycleQuotientTriangleSplice

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleQuotientTriangleLengths

variable {n : ℕ} {C : Type*} [DecidableEq C]

def triangleOrder {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c) : Fin (L + T + 1) → Fin n := fun i =>
  if hzero : i.val = 0 then x
  else if hB : i.val ≤ L then B ⟨i.val - 1, by omega⟩
  else D ⟨i.val - (L + 1), by have hi := i.isLt; omega⟩

theorem triangleOrder_zero {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c) (i : Fin (L + T + 1))
    (hzero : i.val = 0) : triangleOrder x B D hLb hTc i = x := by
  simp only [triangleOrder, dite_eq_left hzero]

theorem triangleOrder_B {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c) (i : Fin (L + T + 1))
    (hpos : 0 < i.val) (hB : i.val ≤ L) :
    triangleOrder x B D hLb hTc i = B ⟨i.val - 1, by omega⟩ := by
  simp only [triangleOrder, dite_eq_right (by omega : ¬ i.val = 0), dite_eq_left hB]

theorem triangleOrder_D {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c) (i : Fin (L + T + 1))
    (hD : L < i.val) :
    triangleOrder x B D hLb hTc i =
      D ⟨i.val - (L + 1), by have _hi := i.isLt; omega⟩ := by
  simp only [triangleOrder, dite_eq_right (by omega : ¬ i.val = 0),
    dite_eq_right (by omega : ¬ i.val ≤ L)]

theorem triangleOrder_injective {b c L T : ℕ}
    (x : Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (hLb : L ≤ b) (hTc : T ≤ c)
    (hB : Function.Injective B) (hD : Function.Injective D)
    (hxB : ∀ i : Fin b, x ≠ B i) (hxD : ∀ i : Fin c, x ≠ D i)
    (hBD : ∀ (i : Fin b) (j : Fin c), B i ≠ D j) :
    Function.Injective (triangleOrder x B D hLb hTc) := by
  intro i j hij
  by_cases hi0 : i.val = 0
  · by_cases hj0 : j.val = 0
    · apply Fin.val_injective
      omega
    · by_cases hjB : j.val ≤ L
      · rw [triangleOrder_zero x B D hLb hTc i hi0,
          triangleOrder_B x B D hLb hTc j (by omega) hjB] at hij
        exact False.elim (hxB _ hij)
      · rw [triangleOrder_zero x B D hLb hTc i hi0,
          triangleOrder_D x B D hLb hTc j (by omega)] at hij
        exact False.elim (hxD _ hij)
  · by_cases hj0 : j.val = 0
    · by_cases hiB : i.val ≤ L
      · rw [triangleOrder_B x B D hLb hTc i (by omega) hiB,
          triangleOrder_zero x B D hLb hTc j hj0] at hij
        exact False.elim (hxB _ hij.symm)
      · rw [triangleOrder_D x B D hLb hTc i (by omega),
          triangleOrder_zero x B D hLb hTc j hj0] at hij
        exact False.elim (hxD _ hij.symm)
    · by_cases hiB : i.val ≤ L
      · by_cases hjB : j.val ≤ L
        · rw [triangleOrder_B x B D hLb hTc i (by omega) hiB,
            triangleOrder_B x B D hLb hTc j (by omega) hjB] at hij
          have hidx := congrArg Fin.val (hB hij)
          change i.val - 1 = j.val - 1 at hidx
          apply Fin.val_injective
          omega
        · rw [triangleOrder_B x B D hLb hTc i (by omega) hiB,
            triangleOrder_D x B D hLb hTc j (by omega)] at hij
          exact False.elim (hBD _ _ hij)
      · by_cases hjB : j.val ≤ L
        · rw [triangleOrder_D x B D hLb hTc i (by omega),
            triangleOrder_B x B D hLb hTc j (by omega) hjB] at hij
          exact False.elim (hBD _ _ hij.symm)
        · rw [triangleOrder_D x B D hLb hTc i (by omega),
            triangleOrder_D x B D hLb hTc j (by omega)] at hij
          have hidx := congrArg Fin.val (hD hij)
          change i.val - (L + 1) = j.val - (L + 1) at hidx
          apply Fin.val_injective
          omega

/-- Three whole selected components with the supplied spanning cyclic orders
and original constant cross colors cannot have three pairwise different
quotient labels under the literal original-host no-rainbow-Ck premise. -/
theorem three_components_cross_labels_repeat
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    {k a b c : ℕ} (hk : 5 ≤ k) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (_haLower : k + 1 ≤ 2 * a) (hbLower : k + 1 ≤ 2 * b)
    (hcLower : k + 1 ≤ 2 * c)
    (_haUpper : a ≤ k - 1) (_hbUpper : b ≤ k - 1) (_hcUpper : c ≤ k - 1)
    (DA DB DD : (selectedGraph χ r).ConnectedComponent)
    (hAB : DA ≠ DB) (hBD : DB ≠ DD) (hDA : DD ≠ DA)
    (A : Fin a → Fin n) (B : Fin b → Fin n) (D : Fin c → Fin n)
    (_hA : Function.Injective A) (hB : Function.Injective B)
    (hD : Function.Injective D)
    (hAspan : Set.range A = DA.supp) (hBspan : Set.range B = DB.supp)
    (hDspan : Set.range D = DD.supp)
    (_hAcycle : ∀ i j : Fin a, (cycleGraph a).Adj i j →
      (selectedGraph χ r).Adj (A i) (A j))
    (hBcycle : ∀ i j : Fin b, (cycleGraph b).Adj i j →
      (selectedGraph χ r).Adj (B i) (B j))
    (hDcycle : ∀ i j : Fin c, (cycleGraph c).Adj i j →
      (selectedGraph χ r).Adj (D i) (D j))
    (α β γ : C)
    (hABcolor : ∀ (x y : Fin n) (e : HostEdge n),
      x ∈ DA.supp → y ∈ DB.supp → e.val = s(x, y) → χ e = α)
    (hBDcolor : ∀ (x y : Fin n) (e : HostEdge n),
      x ∈ DB.supp → y ∈ DD.supp → e.val = s(x, y) → χ e = β)
    (hDAcolor : ∀ (x y : Fin n) (e : HostEdge n),
      x ∈ DD.supp → y ∈ DA.supp → e.val = s(x, y) → χ e = γ)
    (hαOutside : α ∉ newColorUnion χ) (hβOutside : β ∉ newColorUnion χ)
    (hγOutside : γ ∉ newColorUnion χ)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) :
    α = β ∨ β = γ ∨ γ = α := by
  by_contra htriangle
  have hαβ : α ≠ β := fun h => htriangle (Or.inl h)
  have hβγ : β ≠ γ := fun h => htriangle (Or.inr (Or.inl h))
  have hγα : γ ≠ α := fun h => htriangle (Or.inr (Or.inr h))
  let L := trianglePathL k b
  let T := trianglePathT k b
  obtain ⟨hL, hLb, hT, hTc, hcount⟩ :=
    triangle_path_lengths_of_component_lower_bounds hk hb hc hbLower hcLower
  change 1 ≤ L at hL
  change L ≤ b at hLb
  change 1 ≤ T at hT
  change T ≤ c at hTc
  change L + T + 1 = k at hcount
  have ht : 2 ≤ L + T := by omega
  have hAmem (i : Fin a) : A i ∈ DA.supp := by
    rw [← hAspan]
    exact ⟨i, rfl⟩
  have hBmem (i : Fin b) : B i ∈ DB.supp := by
    rw [← hBspan]
    exact ⟨i, rfl⟩
  have hDmem (i : Fin c) : D i ∈ DD.supp := by
    rw [← hDspan]
    exact ⟨i, rfl⟩
  let a0 : Fin a := ⟨0, by omega⟩
  let x := A a0
  have hxB (i : Fin b) : x ≠ B i := by
    intro heq
    apply hAB
    exact ConnectedComponent.eq_of_common_vertex (hAmem a0) (by
      change x ∈ DB.supp
      rw [heq]
      exact hBmem i)
  have hxD (i : Fin c) : x ≠ D i := by
    intro heq
    apply hDA
    exact ConnectedComponent.eq_of_common_vertex (hDmem i) (by
      rw [← heq]
      exact hAmem a0)
  have hBDne (i : Fin b) (j : Fin c) : B i ≠ D j := by
    intro heq
    apply hBD
    exact ConnectedComponent.eq_of_common_vertex (hBmem i) (by
      rw [heq]
      exact hDmem j)
  let q := triangleOrder x B D hLb hTc
  have hq : Function.Injective q :=
    triangleOrder_injective x B D hLb hTc hB hD hxB hxD hBDne
  have hqzero (i : Fin (L + T + 1)) (hi : i.val = 0) : q i = x :=
    triangleOrder_zero x B D hLb hTc i hi
  have hqB (i : Fin (L + T + 1)) (hpos : 0 < i.val) (hi : i.val ≤ L) :
      q i = B ⟨i.val - 1, by omega⟩ :=
    triangleOrder_B x B D hLb hTc i hpos hi
  have hqD (i : Fin (L + T + 1)) (hi : L < i.val) :
      q i = D ⟨i.val - (L + 1), by have hi' := i.isLt; omega⟩ :=
    triangleOrder_D x B D hLb hTc i hi
  let chain : Fin (L + T) → HostEdge n := fun i =>
    ⟨s(q (Fin.castSucc i), q (Fin.succ i)), by
      apply (SimpleGraph.mem_edgeSet _).mpr
      apply (top_adj _ _).mpr
      intro heq
      have hval := congrArg Fin.val (hq heq)
      simp only [Fin.val_castSucc, Fin.val_succ] at hval
      omega⟩
  have hchain (i : Fin (L + T)) :
      (chain i).val = s(q (Fin.castSucc i), q (Fin.succ i)) := rfl
  have hchainInj : Function.Injective chain := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    rw [hchain i, hchain j] at hv
    change Sym2.map q (sourceStep i).val = Sym2.map q (sourceStep j).val at hv
    have hsource : sourceStep i = sourceStep j :=
      Subtype.ext (Sym2.map.injective hq hv)
    exact sourceStep_injective hsource
  have hclass (i : Fin (L + T)) :
      (chain i).val ∈ (selectedGraph χ r).edgeSet ∨
        (i.val = 0 ∧ χ (chain i) = α) ∨
        (i.val = L ∧ χ (chain i) = β) := by
    by_cases hi0 : i.val = 0
    · right; left
      refine ⟨hi0, ?_⟩
      have hleft : q (Fin.castSucc i) = x := hqzero _ hi0
      have hright := hqB (Fin.succ i) (by change 0 < i.val + 1; omega)
        (by change i.val + 1 ≤ L; omega)
      apply hABcolor x _ (chain i) (hAmem a0) (hBmem _)
      rw [hchain i, hleft, hright]
    · by_cases hiL : i.val = L
      · right; right
        refine ⟨hiL, ?_⟩
        have hleft := hqB (Fin.castSucc i) (by change 0 < i.val; omega)
          (by change i.val ≤ L; omega)
        have hright := hqD (Fin.succ i) (by change L < i.val + 1; omega)
        apply hBDcolor _ _ (chain i) (hBmem _) (hDmem _)
        rw [hchain i, hleft, hright]
      · left
        by_cases hiB : i.val < L
        · rw [hchain i, hqB (Fin.castSucc i) (by change 0 < i.val; omega)
            (by change i.val ≤ L; omega),
            hqB (Fin.succ i) (by change 0 < i.val + 1; omega)
              (by change i.val + 1 ≤ L; omega)]
          apply (SimpleGraph.mem_edgeSet _).mpr
          apply hBcycle
          apply pathGraph_le_cycleGraph
          rw [pathGraph_adj]
          left
          change i.val - 1 + 1 = i.val + 1 - 1
          omega
        · rw [hchain i, hqD (Fin.castSucc i) (by change L < i.val; omega),
            hqD (Fin.succ i) (by change L < i.val + 1; omega)]
          apply (SimpleGraph.mem_edgeSet _).mpr
          apply hDcycle
          apply pathGraph_le_cycleGraph
          rw [pathGraph_adj]
          left
          change i.val - (L + 1) + 1 = i.val + 1 - (L + 1)
          omega
  have hselectedUnion (e : HostEdge n)
      (he : e.val ∈ (selectedGraph χ r).edgeSet) : χ e ∈ newColorUnion χ := by
    rw [selectedGraph_edgeSet χ r] at he
    obtain ⟨c', hc'⟩ := he
    have heq : e = r.edge c' := Subtype.ext hc'.symm
    rw [heq, r.color_eq]
    exact c'.property
  have hselectedEq (e₁ e₂ : HostEdge n)
      (he₁ : e₁.val ∈ (selectedGraph χ r).edgeSet)
      (he₂ : e₂.val ∈ (selectedGraph χ r).edgeSet)
      (heq : χ e₁ = χ e₂) : e₁ = e₂ := by
    let s₁ : (selectedGraph χ r).edgeSet := ⟨e₁.val, he₁⟩
    let s₂ : (selectedGraph χ r).edgeSet := ⟨e₂.val, he₂⟩
    have hrestricted : restrictedColor χ r s₁ = restrictedColor χ r s₂ := by
      change χ e₁ = χ e₂
      exact heq
    have hs := restrictedColor_injective χ r hrestricted
    exact Subtype.ext (congrArg (fun e : (selectedGraph χ r).edgeSet => e.val) hs)
  have hcolors : Function.Injective (fun i : Fin (L + T) => χ (chain i)) := by
    intro i j heq
    change χ (chain i) = χ (chain j) at heq
    rcases hclass i with hi | ⟨hi0, hiα⟩ | ⟨hiL, hiβ⟩ <;>
      rcases hclass j with hj | ⟨hj0, hjα⟩ | ⟨hjL, hjβ⟩
    · exact hchainInj (hselectedEq (chain i) (chain j) hi hj heq)
    · have hmem := hselectedUnion (chain i) hi
      rw [heq, hjα] at hmem
      exact False.elim (hαOutside hmem)
    · have hmem := hselectedUnion (chain i) hi
      rw [heq, hjβ] at hmem
      exact False.elim (hβOutside hmem)
    · have hmem := hselectedUnion (chain j) hj
      rw [← heq, hiα] at hmem
      exact False.elim (hαOutside hmem)
    · apply Fin.val_injective
      omega
    · rw [hiα, hjβ] at heq
      exact False.elim (hαβ heq)
    · have hmem := hselectedUnion (chain j) hj
      rw [← heq, hiβ] at hmem
      exact False.elim (hβOutside hmem)
    · rw [hiβ, hjα] at heq
      exact False.elim (hαβ heq.symm)
    · apply Fin.val_injective
      omega
  have hqfirst : q 0 = x := hqzero _ rfl
  have hqlast : q (Fin.last (L + T)) = D ⟨T - 1, by omega⟩ := by
    rw [hqD (Fin.last (L + T)) (by change L < L + T; omega)]
    apply congrArg D
    apply Fin.val_injective
    change L + T - (L + 1) = T - 1
    omega
  let closing : HostEdge n :=
    ⟨s(q 0, q (Fin.last (L + T))), by
      apply (SimpleGraph.mem_edgeSet _).mpr
      apply (top_adj _ _).mpr
      intro heq
      have hval := congrArg Fin.val (hq heq)
      simp only [Fin.val_zero, Fin.val_last] at hval
      omega⟩
  have hclosing : closing.val = s(q 0, q (Fin.last (L + T))) := rfl
  have hclosingColor : χ closing = γ := by
    apply hDAcolor _ x closing (hDmem _) (hAmem a0)
    rw [hclosing, hqfirst, hqlast]
    exact Sym2.eq_swap
  have hne (i : Fin (L + T)) : χ (chain i) ≠ χ closing := by
    intro heq
    rcases hclass i with hi | ⟨_hi0, hiα⟩ | ⟨_hiL, hiβ⟩
    · have hmem := hselectedUnion (chain i) hi
      rw [heq, hclosingColor] at hmem
      exact hγOutside hmem
    · rw [hiα, hclosingColor] at heq
      exact hγα heq.symm
    · rw [hiβ, hclosingColor] at heq
      exact hβγ heq
  have hcopy :=
    ErdosProblems.AntiRamseyCycleHostChainClosing.ordered_host_chain_closes_rainbow
      ht χ q hq chain hchain hcolors closing hclosing hne
  have hcopyk : ∃ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by exact hcount ▸ hcopy
  obtain ⟨f, hf⟩ := hcopyk
  exact hno f hf

end ErdosProblems.AntiRamseyCycleQuotientTriangleSplice
