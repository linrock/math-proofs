module

public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
For a two-valued vertex label, a closed walk crosses the two classes an even
number of times. This is the cut-parity core of the ordered-block anti-Ramsey
coloring for cycles.
-/

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
