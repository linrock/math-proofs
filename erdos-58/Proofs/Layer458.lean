module

public import Layer358
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic

/-
Copyright 2025-2026 The Formal Conjectures Authors.
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

public section

/-! ## Cycle arcs

Both actual arcs of an indexed simple cycle, and outside-root cycles.
-/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x r : V}

def cycleComplementArc (c : G.Walk x x) (i j : ℕ) :
    G.Walk (c.getVert j) (c.getVert i) := (c.drop j).append (c.take i)

theorem cycleComplementArc_eq (c : G.Walk x x) (i j : ℕ) :
    cycleComplementArc c i j = (c.drop j).append (c.take i) := by
  simp [cycleComplementArc]

theorem cycleComplementArc_length (c : G.Walk x x) {i j : ℕ}
    (hi : i ≤ c.length) (_hj : j ≤ c.length) :
    (cycleComplementArc c i j).length = c.length - j + i := by
  simp [cycleComplementArc, Walk.length_append, Walk.drop_length,
    Walk.take_length, Nat.min_eq_left hi]

theorem cycleComplementArc_support_subset (c : G.Walk x x) (i j : ℕ) :
    (cycleComplementArc c i j).support ⊆ c.support := by
  intro z hz
  simp only [cycleComplementArc, Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · rw [Walk.drop_support_eq_support_drop_min] at hz
    exact List.mem_of_mem_drop hz
  · rw [Walk.support_take] at hz
    exact List.mem_of_mem_take hz

theorem cycleComplementArc_isPath (c : G.Walk x x) (hc : c.IsCycle)
    {i j : ℕ} (hij : i < j) (hj : j < c.length) :
    (cycleComplementArc c i j).IsPath := by
  have hdrop : (c.drop j).IsPath := hc.isPath_drop (by omega)
  have htake : (c.take i).IsPath := hc.isPath_take (by omega)
  have hdis : (c.drop j).support.Disjoint (c.take i).support.tail := by
    intro z hz₁ hz₂
    obtain ⟨s, hs, hslen⟩ := Walk.mem_support_iff_exists_getVert.mp hz₁
    rw [Walk.drop_length] at hslen
    rw [Walk.drop_getVert] at hs
    have hz₂' : z ∈ (c.take i).support := List.mem_of_mem_tail hz₂
    obtain ⟨t, ht, htlen⟩ := Walk.mem_support_iff_exists_getVert.mp hz₂'
    rw [Walk.take_length, Nat.min_eq_left (show i ≤ c.length by omega)] at htlen
    rw [Walk.take_getVert, Nat.min_eq_right htlen] at ht
    have hzx : z ≠ x := by
      intro hzx
      have hn := htake.support_nodup
      rw [← Walk.cons_tail_support] at hn
      exact (List.nodup_cons.mp hn).1 (hzx ▸ hz₂)
    have htpos : 1 ≤ t := by
      by_contra! ht0
      have hzero : t = 0 := by omega
      exact hzx (by simpa [hzero] using ht.symm)
    have heq := hc.getVert_injOn
      (show 1 ≤ j + s ∧ j + s ≤ c.length by omega)
      (show 1 ≤ t ∧ t ≤ c.length by omega) (hs.trans ht.symm)
    omega
  rw [Walk.isPath_def, cycleComplementArc, Walk.support_append]
  exact hdrop.support_nodup.append htake.support_nodup.tail hdis

/-- The complementary arc also closes through an outside common neighbor. -/
theorem outside_cycle_complement_witness (c : G.Walk x x) (hc : c.IsCycle)
    (hr : r ∉ c.support) {i j : ℕ} (hij : i < j) (hj : j < c.length)
    (hri : G.Adj r (c.getVert i)) (hrj : G.Adj r (c.getVert j)) :
    ∃ q : G.Walk (c.getVert i) (c.getVert i),
      q.IsCycle ∧ q.length = c.length - (j - i) + 2 := by
  let p := cycleComplementArc c i j
  have hp := cycleComplementArc_isPath c hc hij hj
  have hrp : r ∉ p.support := fun h ↦ hr (cycleComplementArc_support_subset c i j h)
  have hpath : (Walk.cons hrj p).IsPath := hp.cons hrp
  have hlen : p.length = c.length - j + i :=
    cycleComplementArc_length c (by omega) hj.le
  refine ⟨Walk.cons hri.symm (Walk.cons hrj p), ?_, ?_⟩
  · apply cycle_of_path_and_edge (Walk.cons hrj p) hpath hri.symm
    simp only [Walk.length_cons, hlen]
    omega
  · simp only [Walk.length_cons, hlen]
    omega

theorem outside_cycle_forward_witness (c : G.Walk x x) (hc : c.IsCycle)
    (hr : r ∉ c.support) {i j : ℕ} (hij : i < j) (hj : j < c.length)
    (hri : G.Adj r (c.getVert i)) (hrj : G.Adj r (c.getVert j)) :
    ∃ q : G.Walk (c.getVert j) (c.getVert j),
      q.IsCycle ∧ q.length = j - i + 2 := by
  let p := pathInterval c i j hij.le
  have hp : p.IsPath := by
    exact pathInterval_isPath_cycle c hc i j hij.le hj
  have hrp : r ∉ p.support := fun h ↦ hr (pathInterval_support_subset c i j hij.le h)
  have hpath : (Walk.cons hri p).IsPath := hp.cons hrp
  have hlen : p.length = j - i := pathInterval_length c i j hij.le hj.le
  refine ⟨Walk.cons hrj.symm (Walk.cons hri p), ?_, ?_⟩
  · apply cycle_of_path_and_edge (Walk.cons hri p) hpath hrj.symm
    simp only [Walk.length_cons, hlen]
    omega
  · simp only [Walk.length_cons, hlen]

/-- Both cyclic arc lengths occur as actual cycles through an exterior
common neighbor, independent of the chosen starting point of the cycle. -/
theorem outside_cycle_cyclic_arc_lengths (c : G.Walk x x) (hc : c.IsCycle)
    [NeZero c.length] (hr : r ∉ c.support) (a b : ZMod c.length) (hba : b ≠ a)
    (hra : G.Adj r (c.getVert a.val)) (hrb : G.Adj r (c.getVert b.val)) :
    (b - a).val + 2 ∈ G.cycleLengths ∧
      c.length - (b - a).val + 2 ∈ G.cycleLengths := by
  have hne : b.val ≠ a.val := fun h ↦ hba (ZMod.val_injective _ h)
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  rcases lt_or_gt_of_ne hne with hab | hab
  · have hd : (b - a).val = c.length - (a.val - b.val) := by
      have hnz : a - b ≠ 0 := fun h ↦ hba (sub_eq_zero.mp h).symm
      have : NeZero (a - b) := ⟨hnz⟩
      have hneg := ZMod.val_neg_of_ne_zero (a - b)
      rw [ZMod.val_sub hab.le] at hneg
      simpa only [neg_sub] using hneg
    obtain ⟨q, hq, hl⟩ := outside_cycle_complement_witness c hc hr hab ha hrb hra
    obtain ⟨p, hp, hpl⟩ := outside_cycle_forward_witness c hc hr hab ha hrb hra
    constructor
    · exact mem_cycleLengths_intro hq (by simpa only [hd] using hl)
    · refine mem_cycleLengths_intro hp ?_
      rw [hd]
      omega
  · have hd : (b - a).val = b.val - a.val := ZMod.val_sub hab.le
    obtain ⟨q, hq, hl⟩ := outside_cycle_forward_witness c hc hr hab hb hra hrb
    obtain ⟨p, hp, hpl⟩ := outside_cycle_complement_witness c hc hr hab hb hra hrb
    exact ⟨mem_cycleLengths_intro hq (by simpa only [hd] using hl),
      mem_cycleLengths_intro hp (by simpa only [hd] using hpl)⟩

theorem outside_cycle_cyclic_odd_lengths (c : G.Walk x x) (hc : c.IsCycle)
    [NeZero c.length] (hodd : Odd c.length) (hr : r ∉ c.support)
    (a b : ZMod c.length) (hba : b ≠ a)
    (hra : G.Adj r (c.getVert a.val)) (hrb : G.Adj r (c.getVert b.val)) :
    (Odd (b - a).val → (b - a).val + 2 ∈ G.oddCycleLengths) ∧
      (Even (b - a).val → c.length - (b - a).val + 2 ∈ G.oddCycleLengths) := by
  obtain ⟨hforward, hbackward⟩ := outside_cycle_cyclic_arc_lengths c hc hr a b hba hra hrb
  constructor
  · intro hd
    obtain ⟨v, q, hq, hl⟩ := mem_cycleLengths hforward
    exact mem_oddCycleLengths_intro hq hl (hd.add_even (by simp))
  · intro hd
    obtain ⟨v, p, hp, hl⟩ := mem_cycleLengths hbackward
    refine mem_oddCycleLengths_intro hp hl ?_
    rw [Nat.odd_iff] at hodd ⊢
    rw [Nat.even_iff] at hd
    have := ZMod.val_lt (b - a)
    omega

/-! ## Local length counting -/

private def lengthSums (A B : Finset ℕ) : Finset ℕ :=
  (A.product B).image (fun ij => ij.1 + ij.2)

private theorem card_lengthSums_ge (A B : Finset ℕ)
    (ha : A.Nonempty) (hb : B.Nonempty) :
    A.card + B.card ≤ (lengthSums A B).card + 1 := by
  classical
  let a := A.max' ha
  let b := B.min' hb
  have ham : a ∈ A := A.max'_mem ha
  have hbm : b ∈ B := B.min'_mem hb
  let U := A.image (fun x => x + b)
  let W := (B.erase b).image (fun y => a + y)
  have hU : U.card = A.card := Finset.card_image_of_injective A (by
    intro x y h
    change x + b = y + b at h
    omega)
  have hW : W.card = (B.erase b).card :=
    Finset.card_image_of_injective _ (by
      intro x y h
      change a + x = a + y at h
      omega)
  have hd : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzW
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hzU
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hzW
    have hxle : x ≤ a := A.le_max' x hx
    have hyge : b ≤ y := B.min'_le y (Finset.mem_erase.mp hy).2
    have hyne : y ≠ b := (Finset.mem_erase.mp hy).1
    omega
  have hsub : U ∪ W ⊆ lengthSums A B := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨(x, b), Finset.mem_product.mpr ⟨hx, hbm⟩, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr
        ⟨(a, y), Finset.mem_product.mpr ⟨ham, (Finset.mem_erase.mp hy).2⟩, rfl⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hU, hW] at hle
  have herase := Finset.card_erase_add_one hbm
  omega

private theorem local_length_counting_parity_part
    (O X R : Finset ℕ) (L a q b : ℕ)
    (hcap : ∀ n ∈ O, n ≤ L)
    (hXcard : X.card = q + 1)
    (hminmem : a + 1 ∈ X)
    (hmin : ∀ x ∈ X, a + 1 ≤ x)
    (hR : R.Nonempty)
    (hRbounds : ∀ y ∈ R, 3 ≤ y ∧ y ≤ L + 1)
    (hRparity : ∀ y ∈ R, y % 2 = b)
    (hlocal : ∀ x ∈ X, x % 2 = a % 2 → x - a + 1 ∈ O)
    (hforward : ∀ x ∈ X, ∀ y ∈ R, Odd (x + y) → x + y ∈ O)
    (hbackward : ∀ x ∈ X, ∀ y ∈ R,
      Even (x + y) → x + (L + 4 - y) ∈ O) :
    q + R.card ≤ O.card := by
  classical
  let E := X.filter (fun x => x % 2 = a % 2)
  let V := X.filter (fun x => x % 2 ≠ a % 2)
  let F := E.image (fun x => x - a + 1)
  let Z := R.image (fun y => if b = a % 2 then y else L + 4 - y)
  let T := lengthSums V Z
  have hparts : E.card + V.card = X.card := by
    simpa only [E, V] using
      (Finset.card_filter_add_card_filter_not (s := X) (fun x => x % 2 = a % 2))
  have hV : V.Nonempty := by
    refine ⟨a + 1, Finset.mem_filter.mpr ⟨hminmem, ?_⟩⟩
    omega
  have hZ : Z.Nonempty := Finset.Nonempty.image hR _
  have hFcard : F.card = E.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy heq
    have hxge := hmin x (Finset.mem_filter.mp hx).1
    have hyge := hmin y (Finset.mem_filter.mp hy).1
    change x - a + 1 = y - a + 1 at heq
    omega
  have hZcard : Z.card = R.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy heq
    have hxle := (hRbounds x hx).2
    have hyle := (hRbounds y hy).2
    by_cases hba : b = a % 2
    · simp only [ite_eq_left hba] at heq
      exact heq
    · simp only [ite_eq_right hba] at heq
      omega
  have hFsub : F ⊆ O := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hx, hxp⟩ := Finset.mem_filter.mp hx
    exact hlocal x hx hxp
  have hTsub : T ⊆ O := by
    intro n hn
    obtain ⟨⟨v, z⟩, hvz, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hv, hz⟩ := Finset.mem_product.mp hvz
    obtain ⟨hv, hvp⟩ := Finset.mem_filter.mp hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have hyp := hRparity y hy
    by_cases hba : b = a % 2
    · simp only [ite_eq_left hba]
      exact hforward v hv y hy (Nat.odd_iff.mpr (by omega))
    · simp only [ite_eq_right hba]
      apply hbackward v hv y hy
      refine ⟨(v + y) / 2, ?_⟩
      omega
  have hseparate : ∀ f ∈ F, ∀ t ∈ T, f < t := by
    intro f hf t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hx, hxp⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨v, z⟩, hvz, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hv, hz⟩ := Finset.mem_product.mp hvz
    obtain ⟨hv, hvp⟩ := Finset.mem_filter.mp hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have hxge := hmin x hx
    have hvge := hmin v hv
    have hyle := (hRbounds y hy).2
    have hyp := hRparity y hy
    by_cases hba : b = a % 2
    · simp only [ite_eq_left hba]
      have hc : x + (L + 4 - y) ∈ O := by
        apply hbackward x hx y hy
        refine ⟨(x + y) / 2, ?_⟩
        omega
      have hcle := hcap _ hc
      omega
    · simp only [ite_eq_right hba]
      have hc : x + y ∈ O := hforward x hx y hy (Nat.odd_iff.mpr (by omega))
      have hcle := hcap _ hc
      omega
  have hd : Disjoint F T := by
    apply Finset.disjoint_left.mpr
    intro n hnF hnT
    have hlt := hseparate n hnF n hnT
    omega
  have hsub : F ∪ T ⊆ O := Finset.union_subset hFsub hTsub
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hFcard] at hcard
  have hsum := card_lengthSums_ge V Z hV hZ
  change V.card + Z.card ≤ T.card + 1 at hsum
  rw [hZcard] at hsum
  omega

public theorem local_length_counting (O X Y : Finset ℕ) (L a q : ℕ)
    (_hL : Odd L)
    (hcap : ∀ n ∈ O, n ≤ L)
    (hXcard : X.card = q + 1)
    (hminmem : a + 1 ∈ X)
    (hmin : ∀ x ∈ X, a + 1 ≤ x)
    (hY : Y.Nonempty)
    (hYbounds : ∀ y ∈ Y, 3 ≤ y ∧ y ≤ L + 1)
    (hlocal : ∀ x ∈ X, x % 2 = a % 2 → x - a + 1 ∈ O)
    (hforward : ∀ x ∈ X, ∀ y ∈ Y, Odd (x + y) → x + y ∈ O)
    (hbackward : ∀ x ∈ X, ∀ y ∈ Y,
      Even (x + y) → x + (L + 4 - y) ∈ O) :
    q + (Y.card + 1) / 2 ≤ O.card := by
  classical
  let E := Y.filter (fun y => y % 2 = 0)
  let D := Y.filter (fun y => y % 2 ≠ 0)
  have hparts : E.card + D.card = Y.card := by
    simpa only [E, D] using
      (Finset.card_filter_add_card_filter_not (s := Y) (fun y => y % 2 = 0))
  have hYpos : 0 < Y.card := Finset.card_pos.mpr hY
  have hclass : ∀ (R : Finset ℕ) (b : ℕ), R ⊆ Y → R.Nonempty →
      (∀ y ∈ R, y % 2 = b) → q + R.card ≤ O.card := by
    intro R b hsub hR hp
    exact local_length_counting_parity_part O X R L a q b hcap hXcard
      hminmem hmin hR (fun y hy => hYbounds y (hsub hy)) hp hlocal
      (fun x hx y hy => hforward x hx y (hsub hy))
      (fun x hx y hy => hbackward x hx y (hsub hy))
  by_cases hED : D.card ≤ E.card
  · have hE : E.Nonempty := Finset.card_pos.mp (by omega)
    have hcount := hclass E 0 (Finset.filter_subset _ _) hE
      (fun y hy => (Finset.mem_filter.mp hy).2)
    omega
  · have hD : D.Nonempty := Finset.card_pos.mp (by omega)
    have hcount := hclass D 1 (Finset.filter_subset _ _) hD (by
      intro y hy
      have hp := (Finset.mem_filter.mp hy).2
      omega)
    omega

/-! ## Joining cycles

Simple-path and cycle splicing with explicit support intersections.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b c : V}

theorem path_start_notMem_tail (p : G.Walk a b) (hp : p.IsPath) :
    a ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← Walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

theorem path_append_of_meet_only (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z, z ∈ p.support → z ∈ q.support → z = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  apply hp.support_nodup.append hq.support_nodup.tail
  intro z hz₁ hz₂
  have hzb := hmeet z hz₁ (List.mem_of_mem_tail hz₂)
  exact path_start_notMem_tail q hq (hzb ▸ hz₂)

theorem cycle_of_two_paths (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hlen : 3 ≤ p.length + q.length) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · intro z hz₁ hz₂
    have hzp := List.mem_of_mem_tail hz₁
    have hzq : z ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hz₂
    rcases hmeet z hzp hzq with hza | hzb
    · exact path_start_notMem_tail p hp (hza ▸ hz₁)
    · exact path_start_notMem_tail q.reverse hq.reverse (hzb ▸ hz₂)
  · rw [Walk.length_reverse]
    omega

theorem two_paths_cycle_length (p q : G.Walk a b) :
    (p.append q.reverse).length = p.length + q.length := by simp

/-! ## Fans

Fan-of-chords counting, with actual simple-cycle witnesses.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b x : V}

/-- Every odd difference of two neighbor positions has its own actual
odd simple-cycle length. -/
theorem fan_odd_differences_card_le (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i ≤ p.length ∧ G.Adj x (p.getVert i))
    (hfin : G.oddCycleLengths.Finite) :
    (oddPositiveDifferences S).card ≤ G.oddCycleLengths.ncard := by
  classical
  have hmap : Set.MapsTo (fun d : ℕ ↦ d + 2)
      (↑(oddPositiveDifferences S) : Set ℕ) G.oddCycleLengths := by
    intro d hd
    obtain ⟨i, j, ⟨hi, hj, hlt, hodd⟩, rfl⟩ := mem_oddPositiveDifferences.mp hd
    apply fan_odd_cycle_length p hp hx hlt (hS j hj).1 (hS i hi).2 (hS j hj).2
    rw [Nat.odd_iff] at hodd
    omega
  have hinj : Set.InjOn (fun d : ℕ ↦ d + 2)
      (↑(oddPositiveDifferences S) : Set ℕ) := by
    intro i hi j hj hij
    dsimp at hij
    omega
  have hcard := Set.ncard_le_ncard_of_injOn _ hmap hinj hfin
  rw [Set.ncard_coe_finset] at hcard
  exact hcard

/-- Opposite-parity neighbors of an outside vertex give at least half as
many distinct odd lengths as the number of its path neighbors. -/
theorem fan_odd_cycle_count (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i ≤ p.length ∧ G.Adj x (p.getVert i))
    (he : (S.filter Even).Nonempty) (ho : (S.filter Odd).Nonempty)
    (k : ℕ) (hsize : 2 * k + 1 ≤ S.card)
    (hfin : G.oddCycleLengths.Finite) : k ≤ G.oddCycleLengths.ncard := by
  exact (card_oddPositiveDifferences_ge S k he ho hsize).trans
    (fan_odd_differences_card_le p hp hx S hS hfin)

/-- A path together with edges from an outside vertex is two-colorable
when every neighbor position has even index. Vertices with no incident
edge may lie outside this fan. -/
theorem path_fan_colorable (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support)
    (hcover : ∀ u, G.Adj x u → u ∈ p.support)
    (hedges : ∀ {u v}, G.Adj u v → u = x ∨ v = x ∨
      ∃ i < p.length,
        (u = p.getVert i ∧ v = p.getVert (i + 1)) ∨
        (v = p.getVert i ∧ u = p.getVert (i + 1)))
    (heven : ∀ i ∈ pathNeighborPositions p x, Even i) : G.Colorable 2 := by
  classical
  have hidx (i : ℕ) (hi : i ≤ p.length) :
      p.support.idxOf (p.getVert i) = i := by
    rw [p.getVert_eq_support_getElem hi]
    exact hp.support_nodup.idxOf_getElem i _
  let c : V → Fin 2 := fun v ↦
    if v = x then 1 else ⟨p.support.idxOf v % 2, Nat.mod_lt _ (by omega)⟩
  have hroot {v : V} (h : G.Adj x v) : c x ≠ c v := by
    have hvx : v ≠ x := h.ne.symm
    have hv := hcover v h
    have hlt : p.support.idxOf v ≤ p.length := by
      have hi := List.idxOf_lt_length_iff.mpr hv
      rw [Walk.length_support] at hi
      omega
    have he : Even (p.support.idxOf v) := heven _ (by
      rw [mem_pathNeighborPositions]
      exact ⟨hlt, by simpa [p.getVert_support_idxOf hv] using h⟩)
    rw [Nat.even_iff] at he
    intro heq
    have := congrArg Fin.val heq
    simp only [c, ite_eq_left rfl, ite_eq_right hvx, Fin.val_one, he] at this
    omega
  refine ⟨Coloring.mk c ?_⟩
  intro u v huv
  rcases hedges huv with rfl | rfl | ⟨i, hi, huv | hvu⟩
  · exact hroot huv
  · exact (hroot huv.symm).symm
  · rcases huv with ⟨rfl, rfl⟩
    have hix : p.getVert i ≠ x := fun h ↦ hx (h ▸ p.getVert_mem_support i)
    have hisx : p.getVert (i + 1) ≠ x :=
      fun h ↦ hx (h ▸ p.getVert_mem_support (i + 1))
    intro heq
    have heq' := congrArg Fin.val heq
    simp only [c, ite_eq_right hix, ite_eq_right hisx, hidx i hi.le,
      hidx (i + 1) (by omega)] at heq'
    omega
  · rcases hvu with ⟨rfl, rfl⟩
    have hix : p.getVert i ≠ x := fun h ↦ hx (h ▸ p.getVert_mem_support i)
    have hisx : p.getVert (i + 1) ≠ x :=
      fun h ↦ hx (h ▸ p.getVert_mem_support (i + 1))
    intro heq
    have heq' := congrArg Fin.val heq
    simp only [c, ite_eq_right hix, ite_eq_right hisx, hidx i hi.le,
      hidx (i + 1) (by omega)] at heq'
    omega

/-- Gyárfás's fan dichotomy in a path-plus-root representation: a fan
with at least 2k+1 root neighbors is bipartite or has at least k distinct
odd simple-cycle lengths. This applies to a cycle with 2k-1 distinct
diagonals incident to its root, by deleting that root from the cycle. -/
theorem path_fan_dichotomy (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) (hfirst : G.Adj x a)
    (hcover : ∀ u, G.Adj x u → u ∈ p.support)
    (hedges : ∀ {u v}, G.Adj u v → u = x ∨ v = x ∨
      ∃ i < p.length,
        (u = p.getVert i ∧ v = p.getVert (i + 1)) ∨
        (v = p.getVert i ∧ u = p.getVert (i + 1)))
    (k : ℕ) (hdegree : 2 * k + 1 ≤ (G.neighborSet x).ncard)
    (hfin : G.oddCycleLengths.Finite) :
    G.Colorable 2 ∨ k ≤ G.oddCycleLengths.ncard := by
  classical
  let S := pathNeighborPositions p x
  have he : (S.filter Even).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨?_, by simp⟩⟩
    rw [mem_pathNeighborPositions]
    simpa using hfirst
  by_cases ho : (S.filter Odd).Nonempty
  · right
    apply fan_odd_cycle_count p hp hx S (fun i hi ↦ (mem_pathNeighborPositions p x i).mp hi)
      he ho k
    · rw [pathNeighborPositions_card p hp hcover]
      exact hdegree
    · exact hfin
  · left
    apply path_fan_colorable p hp hx hcover hedges
    intro i hi
    rcases Nat.even_or_odd i with heven | hodd
    · exact heven
    · exact False.elim (ho ⟨i, Finset.mem_filter.mpr ⟨hi, hodd⟩⟩)

/-- If the outer fan cycle is odd, the fan has at least k+1 odd lengths.
The outer cycle itself is counted through its two end positions. -/
theorem odd_outer_fan_cycle_count (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) (hfirst : G.Adj x a) (hlast : G.Adj x b)
    (hcover : ∀ u, G.Adj x u → u ∈ p.support) (hodd : Odd p.length)
    (k : ℕ) (hdegree : 2 * k + 1 ≤ (G.neighborSet x).ncard)
    (hfin : G.oddCycleLengths.Finite) : k + 1 ≤ G.oddCycleLengths.ncard := by
  classical
  let S := pathNeighborPositions p x
  have h0 : 0 ∈ S := by
    rw [mem_pathNeighborPositions]
    simpa using hfirst
  have hL : p.length ∈ S := by
    rw [mem_pathNeighborPositions]
    simpa using hlast
  have hmax : ∀ i ∈ S, i ≤ p.length :=
    fun i hi ↦ ((mem_pathNeighborPositions p x i).mp hi).1
  have hsize : 2 * k + 1 ≤ S.card := by
    rw [pathNeighborPositions_card p hp hcover]
    exact hdegree
  exact (card_oddPositiveDifferences_ge_of_odd_endpoints S k p.length
    h0 hL hodd hmax hsize).trans
    (fan_odd_differences_card_le p hp hx S
      (fun i hi ↦ (mem_pathNeighborPositions p x i).mp hi) hfin)

/-! ## Fan paths

Actual simple paths and sumset counting for bipartite fans.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b r : V}

def pathLengths (G : SimpleGraph V) (u v : V) : Set ℕ :=
  {n | ∃ p : G.Walk u v, p.IsPath ∧ p.length = n}

theorem pathLengths_finite [Finite V] (u v : V) : (pathLengths G u v).Finite := by
  classical
  let _ := Fintype.ofFinite V
  apply (Set.finite_Iio (Fintype.card V)).subset
  rintro n ⟨p, hp, rfl⟩
  exact hp.length_lt

theorem pathInterval_support_range (p : G.Walk a b) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p.length) {z : V}
    (hz : z ∈ (pathInterval p i j hij).support) :
    ∃ t, i ≤ t ∧ t ≤ j ∧ p.getVert t = z := by
  obtain ⟨t, ht, htl⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  rw [pathInterval_length p i j hij hj] at htl
  refine ⟨i + t, by omega, by omega, ?_⟩
  exact pathInterval_getVert p i j hij t (by omega) ▸ ht

/-- Join two disjoint path segments through one external vertex. -/
theorem path_via_external {u s t v : V} (q₁ : G.Walk u s) (q₂ : G.Walk t v)
    (h₁ : q₁.IsPath) (h₂ : q₂.IsPath)
    (hdis : ∀ z, z ∈ q₁.support → z ∈ q₂.support → False)
    (hr₁ : r ∉ q₁.support) (hr₂ : r ∉ q₂.support)
    (hrs : G.Adj r s) (hrt : G.Adj r t) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.length = q₁.length + q₂.length + 2 := by
  let q := (q₁.concat hrs.symm).append (Walk.cons hrt q₂)
  refine ⟨q, ?_, ?_⟩
  · simp only [q, Walk.isPath_def, Walk.support_append, Walk.support_concat,
      Walk.support_cons, List.tail_cons]
    apply List.Nodup.append
    · simpa only [Walk.support_concat] using (h₁.concat hr₁ hrs.symm).support_nodup
    · exact h₂.support_nodup
    · intro z hz₁ hz₂
      rcases List.mem_append.mp hz₁ with hz₁ | hz₁
      · exact hdis z hz₁ hz₂
      · have hzr : z = r := by simpa using hz₁
        exact hr₂ (hzr ▸ hz₂)
  · simp only [q, Walk.length_append, Walk.length_concat, Walk.length_cons]
    omega

def pathBetween (p : G.Walk a b) (i j : ℕ) : G.Walk (p.getVert i) (p.getVert j) :=
  if h : i ≤ j then pathInterval p i j h else (pathInterval p j i (by omega)).reverse

theorem pathBetween_isPath (p : G.Walk a b) (hp : p.IsPath) (i j : ℕ) :
    (pathBetween p i j).IsPath := by
  unfold pathBetween
  split
  · exact pathInterval_isPath p hp _ _ _
  · exact (pathInterval_isPath p hp _ _ _).reverse

theorem pathBetween_length (p : G.Walk a b) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    (pathBetween p i j).length = ((i : ℤ) - j).natAbs := by
  unfold pathBetween
  split <;> rename_i h
  · rw [pathInterval_length p i j h hj]
    exact (Int.natAbs_natCast_sub_natCast_of_le h).symm
  · rw [Walk.length_reverse, pathInterval_length p j i (by omega) hi]
    exact (Int.natAbs_natCast_sub_natCast_of_ge (by omega)).symm

theorem pathBetween_support_range (p : G.Walk a b) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) {z : V}
    (hz : z ∈ (pathBetween p i j).support) :
    ∃ t, min i j ≤ t ∧ t ≤ max i j ∧ p.getVert t = z := by
  unfold pathBetween at hz
  split at hz <;> rename_i h
  · simpa [Nat.min_eq_left h, Nat.max_eq_right h] using
      pathInterval_support_range p h hj hz
  · simp only [Walk.support_reverse, List.mem_reverse] at hz
    simpa [Nat.min_eq_right (show j ≤ i by omega), Nat.max_eq_left (show j ≤ i by omega)] using
      pathInterval_support_range p (show j ≤ i by omega) hi hz

theorem fan_path_separated (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    {i j s t : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hs : s ≤ p.length) (ht : t ≤ p.length) (hsep : max i s < min t j)
    (hrs : G.Adj r (p.getVert s)) (hrt : G.Adj r (p.getVert t)) :
    ∃ q : G.Walk (p.getVert i) (p.getVert j), q.IsPath ∧
      q.length = ((i : ℤ) - s).natAbs + ((t : ℤ) - j).natAbs + 2 := by
  have hsub : ∀ {u v : ℕ}, u ≤ p.length → v ≤ p.length →
      ∀ y ∈ (pathBetween p u v).support, y ∈ p.support := by
    intro u v hu hv y hy
    obtain ⟨w, _, _, hwy⟩ := pathBetween_support_range p hu hv hy
    exact hwy ▸ p.getVert_mem_support w
  obtain ⟨q, hq, hl⟩ := path_via_external (pathBetween p i s) (pathBetween p t j)
    (pathBetween_isPath p hp _ _) (pathBetween_isPath p hp _ _)
    (by
      intro z hz₁ hz₂
      obtain ⟨u, _, hu, huz⟩ := pathBetween_support_range p hi hs hz₁
      obtain ⟨v, hv, hvL, hvz⟩ := pathBetween_support_range p ht hj hz₂
      have huL : u ≤ p.length := hu.trans (max_le hi hs)
      have hvL : v ≤ p.length := hvL.trans (max_le ht hj)
      have heq := hp.getVert_injOn huL hvL (huz.trans hvz.symm)
      omega)
    (fun hz => hr (hsub hi hs r hz)) (fun hz => hr (hsub ht hj r hz)) hrs hrt
  exact ⟨q, hq, by simpa only [pathBetween_length p hi hs, pathBetween_length p ht hj] using hl⟩

def parityPathLengths (G : SimpleGraph V) (u v : V) (ε : ℕ) : Set ℕ :=
  pathLengths G u v ∩ {n | n % 2 = ε}

theorem parityPathLengths_finite [Finite V] (u v : V) (ε : ℕ) :
    (parityPathLengths G u v ε).Finite :=
  (pathLengths_finite u v).subset Set.inter_subset_left

/-- Lengths of actual simple paths whose entire support lies in `W`. -/
def pathLengthsWithin (G : SimpleGraph V) (W : Set V) (u v : V) : Set ℕ :=
  {n | ∃ q : G.Walk u v, q.IsPath ∧ q.length = n ∧ ∀ z ∈ q.support, z ∈ W}

def parityPathLengthsWithin (G : SimpleGraph V) (W : Set V)
    (u v : V) (ε : ℕ) : Set ℕ :=
  pathLengthsWithin G W u v ∩ {n | n % 2 = ε}

theorem parityPathLengthsWithin_finite [Finite V] (W : Set V) (u v : V) (ε : ℕ) :
    (parityPathLengthsWithin G W u v ε).Finite := by
  apply (parityPathLengths_finite u v ε).subset
  rintro n ⟨⟨q, hq, hl, _⟩, he⟩
  exact ⟨⟨q, hq, hl⟩, he⟩

public theorem mem_pathLengthsWithin_iff {n : ℕ} :
    n ∈ pathLengthsWithin G W u v ↔
      ∃ q : G.Walk u v, q.IsPath ∧ q.length = n ∧ ∀ z ∈ q.support, z ∈ W := Iff.rfl

public theorem mem_pathLengthsWithin {n : ℕ} {q : G.Walk u v}
    (hq : q.IsPath) (hl : q.length = n)
    (hwithin : ∀ z ∈ q.support, z ∈ W) :
    n ∈ pathLengthsWithin G W u v := ⟨q, hq, hl, hwithin⟩

public theorem parityPathLengthsWithin_eq {n : ℕ} {ε : ℕ} :
    n ∈ parityPathLengthsWithin G W u v ε ↔
      n ∈ pathLengthsWithin G W u v ∧ n % 2 = ε := by
  simp [parityPathLengthsWithin]

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping from an induced graph preserves simple paths, their lengths and their support bound. -/
theorem parityPathLengths_induce_subset (W : Set V) (u v : W) (ε : ℕ) :
    parityPathLengths (G.induce W) u v ε ⊆
      parityPathLengthsWithin G W u.val v.val ε := by
  rintro n ⟨⟨q, hq, hl⟩, he⟩
  let f : G.induce W →g G := ⟨Subtype.val, fun h => h⟩
  refine ⟨⟨q.map f, hq.map Subtype.val_injective,
    (Walk.length_map f q).trans hl, ?_⟩, he⟩
  intro z hz
  rw [Walk.support_map] at hz
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
  exact w.property

/-- The elementary sumset bound transferred to any finite set of witnessed
nonnegative integer lengths. Both sum and difference families use this bridge. -/
theorem affine_differences_card_bound (A B : Finset ℤ) (ha : A.Nonempty) (hb : B.Nonempty)
    (P : Set ℕ) (hP : P.Finite) (c : ℤ)
    (hw : ∀ s ∈ A, ∀ t ∈ B, 0 ≤ c + s - t ∧ (c + s - t).toNat ∈ P) :
    A.card + B.card ≤ P.ncard + 1 := by
  classical
  let D := signedDifferences A B
  have hD : ∀ z ∈ D, 0 ≤ c + z ∧ (c + z).toNat ∈ P := by
    intro z hz
    obtain ⟨s, t, hs, ht, rfl⟩ := mem_signedDifferences.mp hz
    simpa only [sub_eq_add_neg, add_assoc] using hw s hs t ht
  have hinj : Set.InjOn (fun z : ℤ => (c + z).toNat) (D : Set ℤ) := by
    intro z hz w hw heq
    have hzpos := (hD z hz).1
    have hwpos := (hD w hw).1
    change (c + z).toNat = (c + w).toNat at heq
    omega
  have hcard := Set.ncard_le_ncard_of_injOn (fun z : ℤ => (c + z).toNat)
    (fun z hz => (hD z hz).2) hinj hP
  have hdiff := card_signedDifferences_ge A B ha hb
  simp only [Set.ncard_coe_finset] at hcard
  change (signedDifferences A B).card ≤ P.ncard at hcard
  omega

theorem pathBetween_support_subset (p : G.Walk a b) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    (pathBetween p i j).support ⊆ p.support := by
  intro z hz
  obtain ⟨t, _, _, htz⟩ := pathBetween_support_range p hi hj hz
  exact htz ▸ p.getVert_mem_support t

theorem root_to_path_witness (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    {s j : ℕ} (hs : s ≤ p.length) (hj : j ≤ p.length)
    (hrs : G.Adj r (p.getVert s)) :
    ∃ q : G.Walk r (p.getVert j), q.IsPath ∧ q.length = ((s : ℤ) - j).natAbs + 1 := by
  refine ⟨.cons hrs (pathBetween p s j), ?_, ?_⟩
  · exact (pathBetween_isPath p hp s j).cons
      (fun hz => hr (pathBetween_support_subset p hs hj hz))
  · simp only [Walk.length_cons, pathBetween_length p hs hj]

theorem root_to_path_parity (s j : ℕ) (hs : Even s) :
    (((s : ℤ) - j).natAbs + 1) % 2 = (j + 1) % 2 := by
  rw [Nat.even_iff] at hs
  rcases le_total s j with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_le h]
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h]
    omega

/-- A fan root has at least half as many distinct path lengths to any path
vertex as it has spokes. All lengths have the same parity. -/
theorem fan_root_many_paths [Finite V] (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (S : Finset ℕ)
    (hS : ∀ s ∈ S, s ≤ p.length ∧ G.Adj r (p.getVert s) ∧ Even s)
    {j k : ℕ} (hj : j ≤ p.length) (hsize : 2 * k + 1 ≤ S.card) :
    k + 1 ≤ (parityPathLengths G r (p.getVert j) ((j + 1) % 2)).ncard := by
  classical
  let X := S.image (fun s : ℕ => (s : ℤ) - j)
  let T := (X.image Int.natAbs).image (fun n => n + 1)
  have hX : X.card = S.card := Finset.card_image_of_injective _ (by
    intro s t heq
    change (s : ℤ) - j = (t : ℤ) - j at heq
    omega)
  have hT : T.card = (X.image Int.natAbs).card :=
    Finset.card_image_of_injective _ (by
      intro n m heq
      change n + 1 = m + 1 at heq
      omega)
  have hsub : (T : Set ℕ) ⊆ parityPathLengths G r (p.getVert j) ((j + 1) % 2) := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hsL, hrs, hseven⟩ := hS s hs
    exact ⟨root_to_path_witness p hp hr hsL hj hrs, root_to_path_parity s j hseven⟩
  have hcard := Set.ncard_le_ncard hsub (parityPathLengths_finite _ _ _)
  simp only [Set.ncard_coe_finset] at hcard
  have hfold := card_le_two_mul_card_natAbs_image X
  omega

theorem fan_gap_parity (i j s t : ℕ) (hs : Even s) (ht : Even t) :
    (((i : ℤ) - s).natAbs + ((t : ℤ) - j).natAbs + 2) % 2 = (i + j) % 2 := by
  rw [Nat.even_iff] at hs ht
  rcases le_total i s with his | hsi <;> rcases le_total t j with htj | hjt
  · rw [Int.natAbs_natCast_sub_natCast_of_le his, Int.natAbs_natCast_sub_natCast_of_le htj]
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_le his, Int.natAbs_natCast_sub_natCast_of_ge hjt]
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge hsi, Int.natAbs_natCast_sub_natCast_of_le htj]
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge hsi, Int.natAbs_natCast_sub_natCast_of_ge hjt]
    omega

theorem fan_separated_mem (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    {i j s t : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hs : s ≤ p.length) (ht : t ≤ p.length) (hsep : max i s < min t j)
    (hrs : G.Adj r (p.getVert s)) (hrt : G.Adj r (p.getVert t))
    (hseven : Even s) (hteven : Even t) :
    ((i : ℤ) - s).natAbs + ((t : ℤ) - j).natAbs + 2 ∈
      parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2) :=
  ⟨fan_path_separated p hp hr hi hj hs ht hsep hrs hrt, fan_gap_parity i j s t hseven hteven⟩

section PairFamilies

variable [Finite V] (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
variable {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i < j)
variable (A B : Finset ℕ) (ha : A.Nonempty) (hb : B.Nonempty)
variable (hA : ∀ s ∈ A, s ≤ p.length ∧ G.Adj r (p.getVert s) ∧ Even s)
variable (hB : ∀ t ∈ B, t ≤ p.length ∧ G.Adj r (p.getVert t) ∧ Even t)

include hp hr hi hj hij ha hb hA hB

omit hij in
theorem fan_left_middle_card (hleft : ∀ s ∈ A, s ≤ i)
    (hmiddle : ∀ t ∈ B, i < t ∧ t < j) :
    A.card + B.card ≤
      (parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2)).ncard + 1 := by
  classical
  let X := A.image (fun s : ℕ => -(s : ℤ))
  let Y := B.image (fun t : ℕ => (t : ℤ))
  have hX : X.card = A.card := Finset.card_image_of_injective _ (by
    intro s t h; change -(s : ℤ) = -(t : ℤ) at h; omega)
  have hY : Y.card = B.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hbound := affine_differences_card_bound X Y (ha.image _) (hb.image _)
    (parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2))
    (parityPathLengths_finite _ _ _) ((i : ℤ) + j + 2) (by
      intro zs hzs zt hzt
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hzt
      have hsi := hleft s hs
      obtain ⟨hit, htj⟩ := hmiddle t ht
      obtain ⟨hsL, hrs, hse⟩ := hA s hs
      obtain ⟨htL, hrt, hte⟩ := hB t ht
      have hmem := fan_separated_mem p hp hr hi hj hsL htL
        (by omega) hrs hrt hse hte
      rw [Int.natAbs_natCast_sub_natCast_of_ge hsi,
        Int.natAbs_natCast_sub_natCast_of_le htj.le] at hmem
      have heq : ((i : ℤ) + j + 2 + -(s : ℤ) - t).toNat = i - s + (j - t) + 2 := by omega
      exact ⟨by omega, heq.symm ▸ hmem⟩)
  omega

omit hij in
theorem fan_middle_right_card (hmiddle : ∀ s ∈ A, i < s ∧ s < j)
    (hright : ∀ t ∈ B, j ≤ t) :
    A.card + B.card ≤
      (parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2)).ncard + 1 := by
  classical
  let X := A.image (fun s : ℕ => (s : ℤ))
  let Y := B.image (fun t : ℕ => -(t : ℤ))
  have hX : X.card = A.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hY : Y.card = B.card := Finset.card_image_of_injective _ (by
    intro s t h; change -(s : ℤ) = -(t : ℤ) at h; omega)
  have hbound := affine_differences_card_bound X Y (ha.image _) (hb.image _)
    (parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2))
    (parityPathLengths_finite _ _ _) (2 - (i : ℤ) - j) (by
      intro zs hzs zt hzt
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hzt
      obtain ⟨his, hsj⟩ := hmiddle s hs
      have hjt := hright t ht
      obtain ⟨hsL, hrs, hse⟩ := hA s hs
      obtain ⟨htL, hrt, hte⟩ := hB t ht
      have hmem := fan_separated_mem p hp hr hi hj hsL htL
        (by omega) hrs hrt hse hte
      rw [Int.natAbs_natCast_sub_natCast_of_le his.le,
        Int.natAbs_natCast_sub_natCast_of_ge hjt] at hmem
      have heq : (2 - (i : ℤ) - j + s - -(t : ℤ)).toNat = s - i + (t - j) + 2 := by omega
      exact ⟨by omega, heq.symm ▸ hmem⟩)
  omega

theorem fan_left_right_card (hleft : ∀ s ∈ A, s ≤ i)
    (hright : ∀ t ∈ B, j ≤ t) :
    A.card + B.card ≤
      (parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2)).ncard + 1 := by
  classical
  let X := B.image (fun t : ℕ => (t : ℤ))
  let Y := A.image (fun s : ℕ => (s : ℤ))
  have hX : X.card = B.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hY : Y.card = A.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hbound := affine_differences_card_bound X Y (hb.image _) (ha.image _)
    (parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2))
    (parityPathLengths_finite _ _ _) (2 + (i : ℤ) - j) (by
      intro zt hzt zs hzs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hzt
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzs
      have hsi := hleft s hs
      have hjt := hright t ht
      obtain ⟨hsL, hrs, hse⟩ := hA s hs
      obtain ⟨htL, hrt, hte⟩ := hB t ht
      have hmem := fan_separated_mem p hp hr hi hj hsL htL
        (by omega) hrs hrt hse hte
      rw [Int.natAbs_natCast_sub_natCast_of_ge hsi,
        Int.natAbs_natCast_sub_natCast_of_ge hjt] at hmem
      have heq : (2 + (i : ℤ) - j + t - s).toNat = i - s + (t - j) + 2 := by omega
      exact ⟨by omega, heq.symm ▸ hmem⟩)
  omega

end PairFamilies

theorem fan_path_vertices_two_lengths [Finite V] (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) {i j m : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (him : i < m) (hmj : m < j)
    (h0 : G.Adj r (p.getVert 0)) (hm : G.Adj r (p.getVert m))
    (hL : G.Adj r (p.getVert p.length)) (hme : Even m) (hLe : Even p.length) :
    2 ≤ (parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2)).ncard := by
  classical
  let P := parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2)
  have hD : j - i ∈ P := ⟨⟨pathInterval p i j (by omega),
      pathInterval_isPath p hp i j (by omega), pathInterval_length p i j (by omega) hj⟩,
      by change (j - i) % 2 = (i + j) % 2; omega⟩
  have hX := fan_separated_mem p hp hr hi hj (Nat.zero_le _) (show m ≤ p.length by omega)
    (by omega) h0 hm (by simp) hme
  have hY := fan_separated_mem p hp hr hi hj (show m ≤ p.length by omega) (le_refl _)
    (by omega) hm hL hme hLe
  have hZ := fan_separated_mem p hp hr hi hj (Nat.zero_le _) (le_refl _)
    (by omega) h0 hL (by simp) hLe
  rw [Int.natAbs_natCast_sub_natCast_of_ge (Nat.zero_le i),
    Int.natAbs_natCast_sub_natCast_of_le hmj.le] at hX
  rw [Int.natAbs_natCast_sub_natCast_of_le him.le,
    Int.natAbs_natCast_sub_natCast_of_ge hj] at hY
  rw [Int.natAbs_natCast_sub_natCast_of_ge (Nat.zero_le i),
    Int.natAbs_natCast_sub_natCast_of_ge hj] at hZ
  by_contra hn
  have hsub : P.Subsingleton := (Set.ncard_le_one (parityPathLengths_finite _ _ _)).mp (by omega)
  have hDX := hsub hD hX
  have hDY := hsub hD hY
  have hDZ := hsub hD hZ
  omega

/-- Any two path vertices in an even-spoked fan are connected by at least
k+1 actual simple paths with distinct lengths of one common parity. -/
theorem fan_path_vertices_many_paths [Finite V] (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (S : Finset ℕ)
    (hS : ∀ s ∈ S, s ≤ p.length ∧ G.Adj r (p.getVert s) ∧ Even s)
    (h0 : 0 ∈ S) (hL : p.length ∈ S)
    {i j k : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i < j)
    (hk : 1 ≤ k) (hsize : 2 * k + 1 ≤ S.card) :
    k + 1 ≤ (parityPathLengths G (p.getVert i) (p.getVert j) ((i + j) % 2)).ncard := by
  classical
  let A := S.filter (fun s => s ≤ i)
  let BC := S.filter (fun s => ¬s ≤ i)
  let B := BC.filter (fun s => s < j)
  let C := BC.filter (fun s => ¬s < j)
  have hpart₁ : A.card + BC.card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun s => s ≤ i)
  have hpart₂ : B.card + C.card = BC.card :=
    Finset.card_filter_add_card_filter_not (s := BC) (fun s => s < j)
  have hA0 : 0 ∈ A := Finset.mem_filter.mpr ⟨h0, Nat.zero_le _⟩
  have hCL : p.length ∈ C := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hL, by omega⟩, by omega⟩
  have ha : A.Nonempty := ⟨0, hA0⟩
  have hc : C.Nonempty := ⟨p.length, hCL⟩
  have hA : ∀ s ∈ A, s ≤ p.length ∧ G.Adj r (p.getVert s) ∧ Even s := by
    intro s hs
    exact hS s (Finset.mem_filter.mp hs).1
  have hB : ∀ s ∈ B, s ≤ p.length ∧ G.Adj r (p.getVert s) ∧ Even s := by
    intro s hs
    exact hS s (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
  have hC : ∀ s ∈ C, s ≤ p.length ∧ G.Adj r (p.getVert s) ∧ Even s := by
    intro s hs
    exact hS s (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
  have hleft : ∀ s ∈ A, s ≤ i := by intro s hs; exact (Finset.mem_filter.mp hs).2
  have hmiddle : ∀ s ∈ B, i < s ∧ s < j := by
    intro s hs
    obtain ⟨hsBC, hsj⟩ := Finset.mem_filter.mp hs
    obtain ⟨_, hsi⟩ := Finset.mem_filter.mp hsBC
    exact ⟨by omega, hsj⟩
  have hright : ∀ s ∈ C, j ≤ s := by
    intro s hs
    exact Nat.le_of_not_gt (Finset.mem_filter.mp hs).2
  have hAC := fan_left_right_card p hp hr hi hj hij A C ha hc hA hC hleft hright
  by_cases hb : B.Nonempty
  · by_cases hk₂ : 2 ≤ k
    · have hAB := fan_left_middle_card p hp hr hi hj A B ha hb hA hB hleft hmiddle
      have hBC := fan_middle_right_card p hp hr hi hj B C hb hc hB hC hmiddle hright
      omega
    · have hk₁ : k = 1 := by omega
      obtain ⟨m, hm⟩ := hb
      have hmid := hmiddle m hm
      have hms := hB m hm
      have hLs := hS p.length hL
      have h0s := hS 0 h0
      simpa only [hk₁] using fan_path_vertices_two_lengths p hp hr hi hj hmid.1 hmid.2
        h0s.2.1 hms.2.1 hLs.2.1 hms.2.2 hLs.2.2
  · have hB0 : B.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hb)
    omega

theorem parityPathLengths_comm (u v : V) (ε : ℕ) :
    parityPathLengths G u v ε = parityPathLengths G v u ε := by
  ext n
  constructor <;> rintro ⟨⟨p, hp, hl⟩, he⟩ <;>
    exact ⟨⟨p.reverse, hp.reverse, by simpa only [Walk.length_reverse] using hl⟩, he⟩

/-- Gyárfás's fan path lemma, with actual simple walks and exact common parity.
The selected spokes may be any even positions including both path endpoints. -/
theorem bipartite_fan_many_paths [Finite V] (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (S : Finset ℕ)
    (hS : ∀ s ∈ S, s ≤ p.length ∧ G.Adj r (p.getVert s) ∧ Even s)
    (h0 : 0 ∈ S) (hL : p.length ∈ S) {k : ℕ} (hk : 1 ≤ k)
    (hsize : 2 * k + 1 ≤ S.card) {u v : V} (hne : u ≠ v)
    (hu : u = r ∨ u ∈ p.support) (hv : v = r ∨ v ∈ p.support) :
    ∃ ε < 2, k + 1 ≤ (parityPathLengths G u v ε).ncard := by
  classical
  rcases hu with hu | hu
  · subst u
    rcases hv with hv | hv
    · exact (hne hv.symm).elim
    · obtain ⟨j, hjv, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      refine ⟨(j + 1) % 2, Nat.mod_lt _ (by omega), ?_⟩
      simpa only [hjv] using fan_root_many_paths p hp hr S hS hj hsize
  · rcases hv with hv | hv
    · subst v
      obtain ⟨i, hiu, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hu
      refine ⟨(i + 1) % 2, Nat.mod_lt _ (by omega), ?_⟩
      rw [parityPathLengths_comm]
      simpa only [hiu] using fan_root_many_paths p hp hr S hS hi hsize
    · obtain ⟨i, hiu, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hu
      obtain ⟨j, hjv, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      have hijne : i ≠ j := by
        intro h
        subst j
        exact hne (hiu.symm.trans hjv)
      refine ⟨(i + j) % 2, Nat.mod_lt _ (by omega), ?_⟩
      rcases lt_or_gt_of_ne hijne with hij | hji
      · simpa only [hiu, hjv] using fan_path_vertices_many_paths p hp hr S hS h0 hL
          hi hj hij hk hsize
      · rw [parityPathLengths_comm]
        simpa only [hiu, hjv, Nat.add_comm] using fan_path_vertices_many_paths p hp hr S hS h0 hL
          hj hi hji hk hsize

/-- The fan lemma specialized to the entire neighborhood along the simple path. -/
theorem bipartite_neighbor_fan_many_paths [Finite V] (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (h0 : G.Adj r a) (hL : G.Adj r b)
    (he : ∀ s ∈ pathNeighborPositions p r, Even s) {k : ℕ} (hk : 1 ≤ k)
    (hsize : 2 * k + 1 ≤ (pathNeighborPositions p r).card)
    {u v : V} (hne : u ≠ v) (hu : u = r ∨ u ∈ p.support) (hv : v = r ∨ v ∈ p.support) :
    ∃ ε < 2, k + 1 ≤ (parityPathLengths G u v ε).ncard := by
  apply bipartite_fan_many_paths p hp hr (pathNeighborPositions p r) _ _ _ hk hsize hne hu hv
  · intro s hs
    exact ⟨(mem_pathNeighborPositions p r s).mp hs |>.1,
      (mem_pathNeighborPositions p r s).mp hs |>.2, he s hs⟩
  · exact (mem_pathNeighborPositions p r 0).mpr ⟨Nat.zero_le _, by simpa using h0⟩
  · exact (mem_pathNeighborPositions p r p.length).mpr ⟨le_refl _, by simpa using hL⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The fan lemma with a support bound retained for later composition with external connectors. -/
theorem bipartite_fan_many_paths_within [Finite V] (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (S : Finset ℕ)
    (hS : ∀ s ∈ S, s ≤ p.length ∧ G.Adj r (p.getVert s) ∧ Even s)
    (h0 : 0 ∈ S) (hL : p.length ∈ S) {k : ℕ} (hk : 1 ≤ k)
    (hsize : 2 * k + 1 ≤ S.card) {u v : V} (hne : u ≠ v)
    (hu : u = r ∨ u ∈ p.support) (hv : v = r ∨ v ∈ p.support) :
    ∃ ε < 2, k + 1 ≤
      (parityPathLengthsWithin G {z | z = r ∨ z ∈ p.support} u v ε).ncard := by
  classical
  let W : Set V := {z | z = r ∨ z ∈ p.support}
  have hw : ∀ z ∈ p.support, z ∈ W := fun z hz => Or.inr hz
  let q := p.induce W hw
  let rr : W := ⟨r, Or.inl rfl⟩
  let uu : W := ⟨u, hu⟩
  let vv : W := ⟨v, hv⟩
  let f : G.induce W →g G := ⟨Subtype.val, fun h => h⟩
  have hm : q.map f = p := Walk.map_induce p hw
  have hq : q.IsPath := Walk.IsPath.of_map (by rw [hm]; exact hp)
  have hl : q.length = p.length := by
    exact (Walk.length_map f q).symm.trans (congrArg Walk.length hm)
  have hg (s : ℕ) : (q.getVert s).val = p.getVert s := by
    exact (Walk.getVert_map f q s).symm.trans
      (congrArg (fun w : G.Walk a b => w.getVert s) hm)
  have hsupp (z : W) : z ∈ q.support ↔ z.val ∈ p.support := by
    simpa only [q, Walk.support_induce] using List.mem_attachWith hw z
  have hrq : rr ∉ q.support := fun h => hr ((hsupp rr).mp h)
  have hSq : ∀ s ∈ S, s ≤ q.length ∧
      (G.induce W).Adj rr (q.getVert s) ∧ Even s := by
    intro s hs
    obtain ⟨hsl, hsr, hse⟩ := hS s hs
    refine ⟨by rwa [hl], induce_adj.mpr ?_, hse⟩
    change G.Adj r (q.getVert s).val
    rwa [hg]
  have huq : uu = rr ∨ uu ∈ q.support := by
    rcases hu with hu | hu
    · exact Or.inl (Subtype.ext hu)
    · exact Or.inr ((hsupp uu).mpr hu)
  have hvq : vv = rr ∨ vv ∈ q.support := by
    rcases hv with hv | hv
    · exact Or.inl (Subtype.ext hv)
    · exact Or.inr ((hsupp vv).mpr hv)
  obtain ⟨ε, hε, hn⟩ := bipartite_fan_many_paths q hq hrq S hSq h0
    (by rwa [hl]) hk hsize (fun h => hne (congrArg Subtype.val h)) huq hvq
  refine ⟨ε, hε, hn.trans ?_⟩
  exact Set.ncard_le_ncard (parityPathLengths_induce_subset W uu vv ε)
    (parityPathLengthsWithin_finite W u v ε)

theorem bipartite_neighbor_fan_many_paths_within [Finite V]
    (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    (h0 : G.Adj r a) (hL : G.Adj r b)
    (he : ∀ s ∈ pathNeighborPositions p r, Even s) {k : ℕ} (hk : 1 ≤ k)
    (hsize : 2 * k + 1 ≤ (pathNeighborPositions p r).card)
    {u v : V} (hne : u ≠ v) (hu : u = r ∨ u ∈ p.support) (hv : v = r ∨ v ∈ p.support) :
    ∃ ε < 2, k + 1 ≤
      (parityPathLengthsWithin G {z | z = r ∨ z ∈ p.support} u v ε).ncard := by
  apply bipartite_fan_many_paths_within p hp hr (pathNeighborPositions p r) _ _ _
    hk hsize hne hu hv
  · intro s hs
    exact ⟨(mem_pathNeighborPositions p r s).mp hs |>.1,
      (mem_pathNeighborPositions p r s).mp hs |>.2, he s hs⟩
  · exact (mem_pathNeighborPositions p r 0).mpr ⟨Nat.zero_le _, by simpa using h0⟩
  · exact (mem_pathNeighborPositions p r p.length).mpr ⟨le_refl _, by simpa using hL⟩

/-! ## Remaining configurations -/

universe u

open SimpleGraph

/-- The finite positive-`k` equality implication, isolated here as the intermediate
proposition used by `statement_iff_finite_positive_equality`. It is later discharged in
`Layer1158` by `finite_gyarfas`. This is a proposition definition, not an axiom. -/
def FinitePositiveEquality : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ),
    0 < k → G.oddCycleLengths.Finite → G.oddCycleLengths.ncard ≤ k →
      G.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) →
        (completeGraph (Fin (2 * k + 2))).IsContained G

/-- The completed bound, clique direction, zero case and compactness reduce
the full original statement to only the finite positive-k equality implication. -/
theorem statement_iff_finite_positive_equality :
    Statement.{u} ↔ FinitePositiveEquality.{u} := by
  constructor
  · intro h V hV G k hpos hG hk heq
    exact (Erdos58.statement_apply h G k hG hk).2.mp heq
  · intro h
    refine statement_of_finite ?_
    apply finiteStatement_intro
    intro W _ H k hG hk
    refine ⟨finite_chromatic_bound H k hG hk, ⟨?_, ?_⟩⟩
    · intro heq
      by_cases hzero : k = 0
      · subst k
        exact (erdos_58_zero H hG hk).2.mp (by simpa using heq)
      · exact h H k (Nat.pos_of_ne_zero hzero) hG hk heq
    · intro hclique
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
          erdos_58_clique_imp_equality H k hG hk hclique

/-- The clique consequence of Gyárfás's finite structural theorem, stated as a
proposition so that the reduction below is explicit about the structural input.
It is proved by `Erdos58.finite_gyarfas`. -/
@[expose] public def FiniteGyarfas : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ),
    0 < k → G.Connected →
    (∀ v : V, (G.induce {w | w ≠ v}).Connected) →
    (∀ v : V, 2 * k + 1 ≤ (G.neighborSet v).ncard) →
    G.oddCycleLengths.Finite → G.oddCycleLengths.ncard = k →
      (completeGraph (Fin (2 * k + 2))).IsContained G

/-- Conditional form: the published finite structural input suffices for the
full original statement. All critical-core, connectivity, degree and
compactness bridges are proved; `hstruct` is the only remaining hypothesis,
and it is discharged in the finite Gyárfás capstone. -/
theorem statement_of_finite_gyarfas (hstruct : FiniteGyarfas.{u}) : Statement.{u} := by
  apply statement_iff_finite_positive_equality.mpr
  intro V hV G k hpos hG hk heq
  have hnot : ¬ G.Colorable (2 * k + 1) := by
    intro hc
    have hle := hc.chromaticNumber_le
    rw [heq] at hle
    norm_cast at hle
    omega
  obtain ⟨s, hs, hconn, hdeleted, hdegree⟩ :=
    exists_induced_connected_degree_core hnot (by omega)
  let f := Copy.induce G s
  have hfin : (G.induce s).oddCycleLengths.Finite := f.oddCycleLengths_finite hG
  have hjk : (G.induce s).oddCycleLengths.ncard ≤ k :=
    (f.oddCycleLengths_ncard_le hG).trans hk
  have hcount : (G.induce s).oddCycleLengths.ncard = k := by
    apply le_antisymm hjk
    by_contra! hlt
    have hbound := finite_chromatic_bound (G.induce s)
      (G.induce s).oddCycleLengths.ncard hfin le_rfl
    have hle : ((2 * (G.induce s).oddCycleLengths.ncard + 2 : ℕ) : ℕ∞) ≤
        ((2 * k + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast (show 2 * (G.induce s).oddCycleLengths.ncard + 2 ≤
        2 * k + 1 by omega)
    exact hs.not_colorable (chromaticNumber_le_iff_colorable.mp (hbound.trans hle))
  exact (hstruct (G.induce s) k hpos hconn hdeleted hdegree hfin hcount).trans ⟨f⟩

end Erdos58
