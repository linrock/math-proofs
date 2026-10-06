module

public import Mathlib

@[expose] public section

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
