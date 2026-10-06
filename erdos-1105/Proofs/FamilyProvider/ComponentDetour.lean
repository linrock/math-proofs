module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

namespace ErdosProblems.PathUpperReduction.ComponentDetour
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- Ambient support of an actual component of the graph outside S. -/
def componentSupport (C : (G.induce Sᶜ).ConnectedComponent) : Set V :=
  Subtype.val '' C.supp

def Attaches (C : (G.induce Sᶜ).ConnectedComponent) (x : V) : Prop :=
  ∃ v : ↥(Sᶜ), v ∈ C.supp ∧ G.Adj x v

theorem componentSupport_subset_compl (C : (G.induce Sᶜ).ConnectedComponent) :
    componentSupport C ⊆ Sᶜ := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

theorem componentSupport_disjoint {C D : (G.induce Sᶜ).ConnectedComponent}
    (hCD : C ≠ D) : Disjoint (componentSupport C) (componentSupport D) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, heq⟩
  have hwv : w = v := Subtype.ext heq
  subst w
  exact Set.disjoint_left.mp (pairwise_disjoint_supp_connectedComponent (G.induce Sᶜ) hCD) hv hw

/-- Two actual attachments to one outside component give a simple ambient detour.
The two attachment vertices inside the component may coincide. -/
theorem exists_component_detour (C : (G.induce Sᶜ).ConnectedComponent)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hCx : Attaches C x) (hCy : Attaches C y) :
    ∃ q : G.Walk x y, q.IsPath ∧ 2 ≤ q.length ∧
      (∀ z, z ∈ q.support → z ≠ x → z ≠ y → z ∈ componentSupport C) ∧
      (∀ z, z ∈ q.support → z ∈ S → z = x ∨ z = y) ∧
      (∃ z, z ∈ q.support ∧ z ∈ componentSupport C) := by
  classical
  obtain ⟨v, hvC, hxv⟩ := hCx
  obtain ⟨w, hwC, hyw⟩ := hCy
  obtain ⟨inside, hinside⟩ := C.connected_toSimpleGraph.exists_isPath ⟨v, hvC⟩ ⟨w, hwC⟩
  let middle : G.Walk v.val w.val :=
    (inside.map C.toSimpleGraph_hom).map (Embedding.induce Sᶜ).toHom
  have hmiddle : middle.IsPath :=
    Walk.IsPath.map (f := (Embedding.induce Sᶜ).toHom) Subtype.val_injective
      (Walk.IsPath.map (f := C.toSimpleGraph_hom) Subtype.val_injective hinside)
  have hcomponent : ∀ z, z ∈ middle.support → z ∈ componentSupport C := by
    intro z hz
    change z ∈ ((inside.map C.toSimpleGraph_hom).map (Embedding.induce Sᶜ).toHom).support at hz
    rw [Walk.support_map, Walk.support_map] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hu
    exact ⟨t.val, t.property, rfl⟩
  have havoids : ∀ z, z ∈ middle.support → z ∉ S := by
    intro z hz
    exact componentSupport_subset_compl C (hcomponent z hz)
  have hynot : y ∉ middle.reverse.support := by
    intro hz
    exact havoids y (by simpa only [Walk.support_reverse, List.mem_reverse] using hz) hy
  let right : G.Walk y v.val := Walk.cons hyw middle.reverse
  have hright : right.IsPath := hmiddle.reverse.cons hynot
  have hxnot : x ∉ right.reverse.support := by
    intro hz
    have hz' : x = y ∨ x ∈ middle.support := by
      simpa only [right, Walk.support_reverse, List.mem_reverse, Walk.support_cons,
        List.mem_cons] using hz
    rcases hz' with h | h
    · exact hxy h
    · exact havoids x h hx
  let q : G.Walk x y := Walk.cons hxv right.reverse
  have hq : q.IsPath := hright.reverse.cons hxnot
  have hsupport : ∀ z, z ∈ q.support ↔ z = x ∨ z = y ∨ z ∈ middle.support := by
    intro z
    simp only [q, right, Walk.support_cons, Walk.support_reverse, List.mem_reverse,
      List.mem_cons]
  refine ⟨q, hq, ?_, ?_, ?_, ?_⟩
  · simp only [q, right, Walk.length_cons, Walk.length_reverse]
    omega
  · intro z hz hzx hzy
    rcases (hsupport z).mp hz with h | h | h
    · exact (hzx h).elim
    · exact (hzy h).elim
    · exact hcomponent z h
  · intro z hz hzS
    rcases (hsupport z).mp hz with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (havoids z h hzS).elim
  · exact ⟨v.val, (hsupport v.val).mpr (Or.inr (Or.inr middle.start_mem_support)),
      hcomponent v.val middle.start_mem_support⟩

/-- Following an outside walk until its sole allowed S-contact gives an actual
attachment to the initial outside component. No simple-walk premise is needed. -/
theorem outside_walk_attaches_end {v y : V} (q : G.Walk v y)
    (hv : v ∉ S) (hy : y ∈ S)
    (hcontact : ∀ z, z ∈ q.support → z ∈ S → z = y) :
    Attaches ((G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩) y := by
  induction q with
  | nil => exact (hv hy).elim
  | @cons v w y hvw q ih =>
    by_cases hw : w ∈ S
    · have hwy : w = y := hcontact w
        (Walk.support_subset_support_cons q hvw q.start_mem_support) hw
      subst w
      exact ⟨⟨v, hv⟩, rfl, hvw.symm⟩
    · have htail : ∀ z, z ∈ q.support → z ∈ S → z = y := by
        intro z hz hzS
        exact hcontact z (Walk.support_subset_support_cons q hvw hz) hzS
      have hcomp : (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩ =
          (G.induce Sᶜ).connectedComponentMk ⟨w, hw⟩ :=
        ConnectedComponent.connectedComponentMk_eq_of_adj (G := G.induce Sᶜ) hvw
      rw [hcomp]
      exact ih hw hy htail

/-- An actual simple detour contacting S only at its ends is either a chord,
or has both actual attachments in one actual outside connected component. -/
theorem path_is_chord_or_component {x y : V} (q : G.Walk x y)
    (_hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hq : q.IsPath)
    (hcontact : ∀ z, z ∈ q.support → z ∈ S → z = x ∨ z = y) :
    G.Adj x y ∨ ∃ C : (G.induce Sᶜ).ConnectedComponent,
      Attaches C x ∧ Attaches C y := by
  cases q with
  | nil => exact (hxy rfl).elim
  | @cons x v y hxv q =>
    by_cases hv : v ∈ S
    · have hvin : v ∈ (Walk.cons hxv q).support := by
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr q.start_mem_support
      rcases hcontact v hvin hv with h | h
      · exact (hxv.ne h.symm).elim
      · exact Or.inl (h ▸ hxv)
    · have hxnot : x ∉ q.support := (Walk.cons_isPath_iff hxv q).mp hq |>.2
      have htail : ∀ z, z ∈ q.support → z ∈ S → z = y := by
        intro z hz hzS
        rcases hcontact z (Walk.support_subset_support_cons q hxv hz) hzS with h | h
        · exact (hxnot (h ▸ hz)).elim
        · exact h
      exact Or.inr ⟨(G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩,
        ⟨⟨v, hv⟩, rfl, hxv⟩, outside_walk_attaches_end q hv hy htail⟩

/-- Actual component extremes come from all actual path attachment indices,
and have a simple, nonempty, component-supported ambient detour. -/
theorem exists_extreme_component_detour {s : ℕ}
    (p : Fin (s + 1) → V) (hp : Function.Injective p)
    (C : (G.induce (Set.range p)ᶜ).ConnectedComponent)
    (hwide : ∃ i j : Fin (s + 1), i < j ∧ Attaches C (p i) ∧ Attaches C (p j)) :
    ∃ a b : Fin (s + 1), a < b ∧ Attaches C (p a) ∧ Attaches C (p b) ∧
      (∀ j, Attaches C (p j) → a ≤ j ∧ j ≤ b) ∧
      ∃ q : G.Walk (p a) (p b), q.IsPath ∧ 2 ≤ q.length ∧
        (∀ z, z ∈ q.support → z ≠ p a → z ≠ p b → z ∈ componentSupport C) ∧
        (∀ j, p j ∈ q.support → j = a ∨ j = b) ∧
        (∃ z, z ∈ q.support ∧ z ∈ componentSupport C) := by
  classical
  let I : Finset (Fin (s + 1)) := Finset.univ.filter (fun i => Attaches C (p i))
  have hmem : ∀ i, i ∈ I ↔ Attaches C (p i) := by intro i; simp [I]
  obtain ⟨i, j, hij, hi, hj⟩ := hwide
  have hI : I.Nonempty := ⟨i, (hmem i).mpr hi⟩
  let a := I.min' hI
  let b := I.max' hI
  have hab : a < b := lt_of_le_of_lt (I.min'_le i ((hmem i).mpr hi))
    (lt_of_lt_of_le hij (I.le_max' j ((hmem j).mpr hj)))
  have ha : Attaches C (p a) := (hmem a).mp (I.min'_mem hI)
  have hb : Attaches C (p b) := (hmem b).mp (I.max'_mem hI)
  have hpa : p a ∈ Set.range p := ⟨a, rfl⟩
  have hpb : p b ∈ Set.range p := ⟨b, rfl⟩
  have hpab : p a ≠ p b := fun h => (ne_of_lt hab) (hp h)
  obtain ⟨q, hq, hlength, hinside, hcontacts, hnonempty⟩ :=
    exists_component_detour C hpa hpb hpab ha hb
  refine ⟨a, b, hab, ha, hb, ?_, q, hq, hlength, hinside, ?_, hnonempty⟩
  · intro k hk
    exact ⟨I.min'_le k ((hmem k).mpr hk), I.le_max' k ((hmem k).mpr hk)⟩
  · intro k hk
    rcases hcontacts (p k) hk ⟨k, rfl⟩ with h | h
    · exact Or.inl (hp h)
    · exact Or.inr (hp h)

/-- Distinct actual component labels force disjoint ordinary internal supports
once the constructed component-support conclusions have been applied. -/
theorem internal_supports_disjoint {C D : (G.induce Sᶜ).ConnectedComponent}
    (hCD : C ≠ D) {x y u v : V} (q : G.Walk x y) (r : G.Walk u v)
    (hq : ∀ z, z ∈ q.support → z ≠ x → z ≠ y → z ∈ componentSupport C)
    (hr : ∀ z, z ∈ r.support → z ≠ u → z ≠ v → z ∈ componentSupport D) :
    Disjoint {z | z ∈ q.support ∧ z ≠ x ∧ z ≠ y}
      {z | z ∈ r.support ∧ z ≠ u ∧ z ≠ v} := by
  apply Set.disjoint_left.mpr
  rintro z ⟨hzq, hzx, hzy⟩ ⟨hzr, hzu, hzv⟩
  exact Set.disjoint_left.mp (componentSupport_disjoint hCD)
    (hq z hzq hzx hzy) (hr z hzr hzu hzv)

end ErdosProblems.PathUpperReduction.ComponentDetour
