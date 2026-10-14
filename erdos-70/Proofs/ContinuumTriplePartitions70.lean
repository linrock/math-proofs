module

/-
Copyright 2026 The Formal Conjectures Authors.
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
public import Mathlib

@[expose] public section

set_option linter.deprecated false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Cardinal Ordinal
open scoped Cardinal

protected def Set.Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

theorem Set.Triplewise.mono {α : Type*} {r : α → α → α → Prop} {s t : Set α} (h : t ⊆ s)
    (hs : s.Triplewise r) : t.Triplewise r :=
  fun _ hx _ hy _ hz hxy hyz hxz ↦ hs (h hx) (h hy) (h hz) hxy hyz hxz

namespace Erdos70

universe u

def OrdinalCardinalRamsey3 (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    (∃ s : Set α.ToType, typeLT s = β ∧ s.Triplewise isRed) ∨
    (∃ s : Set α.ToType, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

namespace erdos_70.variants

theorem ordinalCardinalRamsey3_mono {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}}
    (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c) :
    OrdinalCardinalRamsey3 α β' c' := by
  intro isRed hSym
  obtain (⟨s, hs_type, hs_clique⟩ | ⟨s, hs_card, hs_clique⟩) := h isRed hSym
  · rw [← Ordinal.type_toType β'] at hβ
    obtain ⟨g⟩ := Ordinal.type_le_iff'.mp (hs_type ▸ hβ)
    let t : Set α.ToType := Set.range (Subtype.val ∘ g)
    refine Or.inl ⟨t, ?_, hs_clique.mono (by rintro x ⟨a, rfl⟩; exact (g a).2)⟩
    let emb : (· < · : β'.ToType → β'.ToType → Prop) ↪r (· < · : ↑t → ↑t → Prop) :=
      { toFun := fun a => ⟨(g a).val, a, rfl⟩
        inj' := fun a b heq => g.injective (Subtype.ext (congr_arg (fun x : ↑t => x.val) heq))
        map_rel_iff' := g.map_rel_iff }
    have hsurj : Function.Surjective emb := fun ⟨_, hy⟩ => ⟨hy.choose, Subtype.ext hy.choose_spec⟩
    exact (Ordinal.type_eq.mpr ⟨RelIso.ofSurjective emb hsurj |>.symm⟩).trans
      (Ordinal.type_toType β')
  · obtain ⟨t, ht_sub, ht_card⟩ := (Cardinal.le_mk_iff_exists_subset).mp (hs_card ▸ hc)
    exact Or.inr ⟨t, ht_card, hs_clique.mono ht_sub⟩

end erdos_70.variants


/-! ## Part 1: ZFC Refutation of `erdos_70.variants.omega_one` (Issue #6550) -/

/-- Real-valued Sierpiński peak predicate on triples: the middle element (in the `<` order on `α`)
strictly exceeds both endpoints under `f : α → ℝ`. -/
def PeakBlueReal {α : Type*} [LT α] (f : α → ℝ) (x y z : α) : Prop :=
  (((x < y ∧ y < z) ∨ (z < y ∧ y < x)) ∧ f x < f y ∧ f z < f y) ∨
  (((y < x ∧ x < z) ∨ (z < x ∧ x < y)) ∧ f y < f x ∧ f z < f x) ∨
  (((x < z ∧ z < y) ∨ (y < z ∧ z < x)) ∧ f x < f z ∧ f y < f z)

lemma peakBlueReal_symm {α : Type*} [LT α] (f : α → ℝ) (x y z : α) :
    (PeakBlueReal f x y z ↔ PeakBlueReal f y x z) ∧
    (PeakBlueReal f x y z ↔ PeakBlueReal f x z y) := by
  unfold PeakBlueReal
  tauto

lemma peakBlueReal_sorted {α : Type*} [LinearOrder α] (f : α → ℝ)
    {x y z : α} (hxy : x < y) (hyz : y < z) :
    PeakBlueReal f x y z ↔ f x < f y ∧ f z < f y := by
  have hxz := hxy.trans hyz
  simp [PeakBlueReal, hxy, hyz, hxz, not_lt.mpr hxy.le,
    not_lt.mpr hyz.le, not_lt.mpr hxz.le]

lemma not_blue_four_sorted_real {α : Type*} [LinearOrder α] (f : α → ℝ)
    {w x y z : α} (hwx : w < x) (hxy : x < y) (hyz : y < z) :
    ¬ (PeakBlueReal f w x y ∧ PeakBlueReal f w x z ∧
       PeakBlueReal f w y z ∧ PeakBlueReal f x y z) := by
  rintro ⟨h₁, _, _, h₄⟩
  have h₁' := (peakBlueReal_sorted f hwx hxy).mp h₁
  have h₄' := (peakBlueReal_sorted f hxy hyz).mp h₄
  exact lt_asymm h₁'.2 h₄'.1

lemma no_blue_order_embedding_four_real {α : Type*} [LinearOrder α]
    (f : α → ℝ) {s : Set α} (hs : s.Triplewise (PeakBlueReal f))
    (e : Fin 4 ↪o α) (he : ∀ i, e i ∈ s) : False := by
  have h01 : e 0 < e 1 := e.strictMono (by decide)
  have h12 : e 1 < e 2 := e.strictMono (by decide)
  have h23 : e 2 < e 3 := e.strictMono (by decide)
  exact not_blue_four_sorted_real f h01 h12 h23
    ⟨hs (he 0) (he 1) (he 2) h01.ne h12.ne (h01.trans h12).ne,
     hs (he 0) (he 1) (he 3) h01.ne (h12.trans h23).ne (h01.trans (h12.trans h23)).ne,
     hs (he 0) (he 2) (he 3) (h01.trans h12).ne h23.ne (h01.trans (h12.trans h23)).ne,
     hs (he 1) (he 2) (he 3) h12.ne h23.ne (h12.trans h23).ne⟩

lemma blue_ncard_le_three_real {α : Type*} [LinearOrder α]
    (f : α → ℝ) {s : Set α} (hs : s.Triplewise (PeakBlueReal f)) :
    s.ncard ≤ 3 := by
  classical
  by_contra h
  have h4 : 4 ≤ s.ncard := by omega
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_card_eq h4
  have htfin : t.Finite := Set.finite_of_ncard_pos (by omega)
  have htcard : htfin.toFinset.card = 4 := by
    rw [← Set.ncard_eq_toFinset_card t htfin]
    exact ht
  let e : Fin 4 ↪o α := htfin.toFinset.orderEmbOfFin htcard
  apply no_blue_order_embedding_four_real f hs e
  intro i
  exact hts (htfin.mem_toFinset.mp (htfin.toFinset.orderEmbOfFin_mem htcard i))

lemma blue_finite_real {α : Type*} [LinearOrder α]
    (f : α → ℝ) {s : Set α} (hs : s.Triplewise (PeakBlueReal f)) : s.Finite := by
  by_contra h
  obtain ⟨t, hts, _, ht⟩ := Set.Infinite.exists_subset_ncard_eq h 4
  have hb := blue_ncard_le_three_real f (hs.mono hts)
  omega

lemma blue_card_le_three_real {α : Type*} [LinearOrder α]
    (f : α → ℝ) {s : Set α} (hs : s.Triplewise (PeakBlueReal f)) : #s ≤ 3 := by
  rw [← Set.cast_ncard (blue_finite_real f hs)]
  exact_mod_cast blue_ncard_le_three_real f hs

/-- Every well-founded subset of `ℝ` (under `<`) is countable. -/
lemma countable_of_wellFoundedLT_real_subtype (S : Set ℝ)
    [WellFoundedLT S] : S.Countable := by
  have hCount :
      {x : ℝ | x ∈ S ∧ ∃ z : ℝ, x < z ∧
        ∀ y ∈ S, x < y → z ≤ y}.Countable :=
    countable_image_lt_image_Ioi_within S (id : ℝ → ℝ)
  apply Set.Countable.mono ?_ hCount
  intro x hx
  refine ⟨hx, ?_⟩
  by_cases hAbove : ∃ y ∈ S, x < y
  · let T : Set S := {a | x < (a : ℝ)}
    have hT : T.Nonempty := by
      obtain ⟨y, hy, hxy⟩ := hAbove
      exact ⟨⟨y, hy⟩, hxy⟩
    obtain ⟨q, hq⟩ :=
      WellFoundedLT.exists_minimal (inferInstance : WellFoundedLT S) T hT
    have hxq : x < (q : ℝ) := hq.prop
    obtain ⟨z, hxz, hzq⟩ := exists_between hxq
    refine ⟨z, hxz, ?_⟩
    intro y hy hxy
    have hqy : (q : ℝ) ≤ y := by
      by_contra hn
      have hyq : y < (q : ℝ) := lt_of_not_ge hn
      exact (hq.not_prop_of_lt (show (⟨y, hy⟩ : S) < q from hyq)) hxy
    exact hzq.le.trans hqy
  · refine ⟨x + 1, by linarith, fun y hy hxy => (hAbove ⟨y, hy, hxy⟩).elim⟩

lemma countable_of_strictMonoOn_wellFounded {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {t : Set α} (g : α → ℝ) (hg : ∀ x ∈ t, ∀ y ∈ t, x < y → g x < g y) :
    t.Countable := by
  let emb : ((· < ·) : t → t → Prop) ↪r ((· < ·) : (g '' t) → (g '' t) → Prop) :=
    { toFun := fun x => ⟨g x.1, ⟨x.1, x.2, rfl⟩⟩
      inj' := by
        intro a b hab
        have hval : g a.1 = g b.1 := congr_arg Subtype.val hab
        rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
        · exact (ne_of_lt (hg a.1 a.2 b.1 b.2 hlt) hval).elim
        · exact Subtype.ext heq
        · exact (ne_of_gt (hg b.1 b.2 a.1 a.2 hgt) hval).elim
      map_rel_iff' := by
        intro a b
        constructor
        · intro hlt
          change g a.1 < g b.1 at hlt
          rcases lt_trichotomy a.1 b.1 with h | h | h
          · exact h
          · rw [h] at hlt
            exact (lt_irrefl _ hlt).elim
          · exact (lt_asymm hlt (hg b.1 b.2 a.1 a.2 h)).elim
        · intro hlt
          exact hg a.1 a.2 b.1 b.2 hlt }
  have hsurj : Function.Surjective emb := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let iso := RelIso.ofSurjective emb hsurj
  have hWF_t : WellFounded ((· < ·) : t → t → Prop) := wellFounded_lt
  have hWF_img : WellFounded ((· < ·) : (g '' t) → (g '' t) → Prop) :=
    iso.symm.toRelEmbedding.wellFounded hWF_t
  have : IsWellFounded (g '' t) (· < ·) := ⟨hWF_img⟩
  have hcnt_img : (g '' t).Countable := countable_of_wellFoundedLT_real_subtype (g '' t)
  have hinj : Set.InjOn g t := by
    intro x hx y hy hxy
    rcases lt_trichotomy x y with h | rfl | h
    · exact (ne_of_lt (hg x hx y hy h) hxy).elim
    · rfl
    · exact (ne_of_gt (hg y hy x hx h) hxy).elim
  exact Set.MapsTo.countable_of_injOn (Set.mapsTo_image g t) hinj hcnt_img

/-- Every red-monochromatic subset under `¬ PeakBlueReal f` in a well-ordered type with an
injection `f : α → ℝ` is countable, because it splits into `s₁` (on which `f` is strictly
increasing) and `s₂` (on which `-f` is strictly increasing). -/
lemma red_countable_of_injective_real {α : Type*} [LinearOrder α] [WellFoundedLT α]
    (f : α → ℝ) (hf : Function.Injective f) {s : Set α}
    (hs : s.Triplewise (fun x y z ↦ ¬ PeakBlueReal f x y z)) : s.Countable := by
  let s₁ : Set α := {x ∈ s | ∃ w ∈ s, w < x ∧ f w < f x}
  let s₂ : Set α := {x ∈ s | ∀ w ∈ s, w < x → f x ≤ f w}
  have hsub : s ⊆ s₁ ∪ s₂ := by
    intro x hx
    by_cases h : ∃ w ∈ s, w < x ∧ f w < f x
    · exact Or.inl ⟨hx, h⟩
    · push Not at h
      exact Or.inr ⟨hx, h⟩
  have hs₁ : s₁.Countable := by
    refine countable_of_strictMonoOn_wellFounded f ?_
    rintro x ⟨hx, w, hw, hwx, hfwx⟩ y ⟨hy, _⟩ hxy
    have hno : ¬ PeakBlueReal f w x y :=
      hs hw hx hy hwx.ne hxy.ne (hwx.trans hxy).ne
    have hnot_peak : ¬ (f w < f x ∧ f y < f x) :=
      fun hp => hno ((peakBlueReal_sorted f hwx hxy).mpr hp)
    have hle : f x ≤ f y := not_lt.mp (fun hfyx => hnot_peak ⟨hfwx, hfyx⟩)
    exact lt_of_le_of_ne hle (fun heq => hxy.ne (hf heq))
  have hs₂ : s₂.Countable := by
    refine countable_of_strictMonoOn_wellFounded (fun x => -f x) ?_
    rintro x ⟨hx, _⟩ y ⟨hy, hy_le⟩ hxy
    have hle : f y ≤ f x := hy_le x hx hxy
    have hlt : f y < f x := lt_of_le_of_ne hle (fun heq => hxy.ne.symm (hf heq))
    exact neg_lt_neg hlt
  exact (hs₁.union hs₂).mono hsub

/-- Unconditional ZFC refutation of `OrdinalCardinalRamsey3 (𝔠).ord (Cardinal.aleph 1).ord 4`. -/
theorem not_ordinalCardinalRamsey3_continuum_aleph1_four :
    ¬ OrdinalCardinalRamsey3.{0} (𝔠).ord (Cardinal.aleph 1).ord 4 := by
  intro hRamsey
  have hcard_eq : #((𝔠 : Cardinal.{0}).ord.ToType) = #ℝ := by
    rw [Cardinal.mk_toType, Cardinal.card_ord, Cardinal.mk_real]
  obtain ⟨e⟩ := Cardinal.eq.mp hcard_eq
  let f : (𝔠 : Cardinal.{0}).ord.ToType → ℝ := e
  have hf : Function.Injective f := e.injective
  obtain (⟨s, htype, hs⟩ | ⟨s, hcard, hs⟩) :=
    hRamsey (fun x y z => ¬ PeakBlueReal f x y z)
      (fun x y z _ _ _ => ⟨(peakBlueReal_symm f x y z).1.not, (peakBlueReal_symm f x y z).2.not⟩)
  · have hcnt : s.Countable := red_countable_of_injective_real f hf hs
    have hcard_le : #s ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr hcnt
    have hcard_s : #s = Cardinal.aleph 1 := by
      have h1 : (typeLT s).card = #s := Ordinal.card_type _
      rw [← h1, htype, Cardinal.card_ord]
    rw [hcard_s] at hcard_le
    exact not_lt_of_ge hcard_le Cardinal.aleph0_lt_aleph_one
  · have hs' : s.Triplewise (PeakBlueReal f) := by
      intro x hx y hy z hz hxy hyz hxz
      exact Classical.not_not.mp (hs hx hy hz hxy hyz hxz)
    have hb := blue_card_le_three_real f hs'
    rw [hcard] at hb
    have : (4 : Cardinal.{0}) ≤ 3 := hb
    norm_num at this

/-- Resolution of `erdos_70.variants.omega_one` in the negative (`False`). -/
theorem erdos_70_omega_one_refuted :
    False ↔
    ∀ᵉ (n : ℕ) (_ : 2 ≤ n),
      OrdinalCardinalRamsey3.{0} (𝔠).ord (Cardinal.aleph 1).ord n := by
  simp only [false_iff, not_forall]
  exact ⟨4, by decide, not_ordinalCardinalRamsey3_continuum_aleph1_four⟩

/-! ## Part 2: Positive Resolution of `erdos_70.variants.omega_three` -/

lemma three_set_triplewise {α : Type*}
    (Q : α → α → α → Prop)
    (hSym : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (Q x y z ↔ Q y x z) ∧ (Q x y z ↔ Q x z y))
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hFace : Q a b c) :
    ({a, b, c} : Set α).Triplewise Q := by
  have hbac : Q b a c := ((hSym a b c hab hbc hac).1).mp hFace
  have hacb : Q a c b := ((hSym a b c hab hbc hac).2).mp hFace
  have hbca : Q b c a := ((hSym b a c hab.symm hac hbc).2).mp hbac
  have hcab : Q c a b := ((hSym a c b hac hbc.symm hab).1).mp hacb
  have hcba : Q c b a := ((hSym b c a hbc hac.symm hab.symm).1).mp hbca
  intro x hx y hy z hz hxy hyz hxz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;>
    simp_all

lemma ordinalCardinalRamsey3_self_three (α : Ordinal.{0}) :
    OrdinalCardinalRamsey3.{0} α α 3 := by
  intro isRed hSym
  by_cases hBlue : ∃ x y z : α.ToType, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ ¬ isRed x y z
  · obtain ⟨x, y, z, hxy, hyz, hxz, hnot⟩ := hBlue
    have hNegSym : ∀ a b c : α.ToType, a ≠ b → b ≠ c → a ≠ c →
        ((¬ isRed a b c) ↔ (¬ isRed b a c)) ∧
        ((¬ isRed a b c) ↔ (¬ isRed a c b)) := by
      intro a b c hab hbc hac
      exact ⟨not_congr (hSym a b c hab hbc hac).1,
        not_congr (hSym a b c hab hbc hac).2⟩
    let s : Set α.ToType := {x, y, z}
    have hsE : s.encard = (3 : ℕ∞) :=
      (Set.encard_eq_three).mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
    have hsCard : #s = (3 : Cardinal.{0}) :=
      Cardinal.toENat_eq_ofNat.mp (by simpa only [Set.toENat_cardinalMk] using hsE)
    exact Or.inr ⟨s, hsCard,
      three_set_triplewise (fun a b c => ¬ isRed a b c) hNegSym hxy hyz hxz hnot⟩
  · push Not at hBlue
    refine Or.inl ⟨Set.univ, ?_, ?_⟩
    · let emb : (· < · : α.ToType → α.ToType → Prop) ↪r
          (· < · : ↑(Set.univ : Set α.ToType) → ↑(Set.univ : Set α.ToType) → Prop) :=
        { toFun := fun a => ⟨a, trivial⟩
          inj' := fun a b heq => congr_arg Subtype.val heq
          map_rel_iff' := Iff.rfl }
      have hsurj : Function.Surjective emb := fun ⟨a, _⟩ => ⟨a, rfl⟩
      exact (Ordinal.type_eq.mpr ⟨RelIso.ofSurjective emb hsurj |>.symm⟩).trans
        (Ordinal.type_toType α)
    · intro x _ y _ z _ hxy hyz hxz
      exact hBlue x y z hxy hyz hxz

theorem ordinalCardinalRamsey3_continuum_omega_three :
    OrdinalCardinalRamsey3.{0} (𝔠).ord ω 3 := by
  refine erdos_70.variants.ordinalCardinalRamsey3_mono
    (ordinalCardinalRamsey3_self_three (𝔠).ord) ?_ le_rfl
  have hle : (ℵ₀ : Cardinal.{0}).ord ≤ (𝔠 : Cardinal.{0}).ord :=
    Cardinal.ord_le_ord.mpr Cardinal.aleph0_le_continuum
  simpa using hle

theorem erdos_70_omega_three_solved :
    True ↔ OrdinalCardinalRamsey3.{0} (𝔠).ord ω 3 := by
  simp only [true_iff]
  exact ordinalCardinalRamsey3_continuum_omega_three

end Erdos70

