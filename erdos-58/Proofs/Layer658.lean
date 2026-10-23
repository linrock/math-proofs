module

public import Layer558
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Max

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

@[expose] public section

/-! ## Common contacts of a cycle

The common-contact counting argument for actual graph cycles. The numeric
memberships are obtained from explicit cycle witnesses, and the initial
cycle position is normalized by rotation. This is an auxiliary theorem for
the positive-k equality argument, not the full Erdős 58 statement.
-/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x A B : V}

/-- Common contacts counted from a common initial cycle vertex. -/
theorem exterior_common_contacts_normalized_many_odd_lengths
    (c : G.Walk x x) (hc : c.IsCycle) (hCodd : Odd c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hAx : G.Adj A x) (hBx : G.Adj B x)
    (k : ℕ) (hk : 1 ≤ k)
    (hcontacts : 2 * k ≤ (exteriorCommonVertices c A B).ncard)
    (hfinite : G.oddCycleLengths.Finite) :
    k + 1 ≤ G.oddCycleLengths.ncard := by
  classical
  let X := exteriorCommonPositions c A B
  let D := X.erase 0
  let O := hfinite.toFinset
  have hzero : 0 ∈ X := by
    apply (mem_exteriorCommonPositions c A B 0).mpr
    exact ⟨by have := hc.three_le_length; omega, by simpa using hAx, by simpa using hBx⟩
  have hsize : 2 * k ≤ D.card + 1 := by
    change 2 * k ≤ (X.erase 0).card + 1
    rw [Finset.card_erase_add_one hzero]
    simpa only [X, exteriorCommonPositions_card c hc] using hcontacts
  have hD : ∀ d ∈ D, 0 < d ∧ d < c.length := by
    intro d hd
    obtain ⟨hdne, hdX⟩ := Finset.mem_erase.mp hd
    exact ⟨Nat.pos_of_ne_zero hdne, ((mem_exteriorCommonPositions c A B d).mp hdX).1⟩
  have hAd : ∀ d ∈ D, G.Adj A (c.getVert d) := by
    intro d hd
    exact ((mem_exteriorCommonPositions c A B d).mp (Finset.mem_erase.mp hd).2).2.1
  have hBd : ∀ d ∈ D, G.Adj B (c.getVert d) := by
    intro d hd
    exact ((mem_exteriorCommonPositions c A B d).mp (Finset.mem_erase.mp hd).2).2.2
  have hAout : A ∉ c.support := havoid A S.start_mem_support
  have hzeroLt : 0 < c.length := by have := hc.three_le_length; omega
  have hAx0 : G.Adj A (c.getVert 0) := by simpa using hAx
  have hmemO : ∀ n, n ∈ G.oddCycleLengths → n ∈ O := by
    intro n hn
    exact hfinite.mem_toFinset.mpr hn
  have hcount : k + 1 ≤ O.card := by
    apply common_contacts_lengths_card D O hCodd hs hk hD hsize
    · intro d hd hodd
      obtain ⟨q, hq, hql⟩ := outside_cycle_forward_witness c hc hAout
        (hD d hd).1 (hD d hd).2 hAx0 (hAd d hd)
      apply hmemO
      refine mem_oddCycleLengths_intro hq
        (by simpa only [Nat.sub_zero] using hql) ?_
      exact hodd.add_even (by simp)
    · intro d hd heven
      obtain ⟨q, hq, hql⟩ := outside_cycle_complement_witness c hc hAout
        (hD d hd).1 (hD d hd).2 hAx0 (hAd d hd)
      apply hmemO
      refine mem_oddCycleLengths_intro hq (by simpa only [Nat.sub_zero] using hql) ?_
      have hdL := (hD d hd).2
      simp only [Nat.odd_iff] at hCodd ⊢
      simp only [Nat.even_iff] at heven
      omega
    · intro d hd hodd
      have hm := (exterior_cycle_distance_odd_lengths c hc hCodd S hS hs havoid
        hzeroLt (hD d hd).2 (by have := (hD d hd).1; omega) hAx0 (hBd d hd)).1
        (by simpa only [Nat.dist_zero_left, Nat.add_comm] using hodd)
      exact hmemO _ (by simpa only [Nat.dist_zero_left, Nat.add_comm] using hm)
    · intro d hd heven
      have hm := (exterior_cycle_distance_odd_lengths c hc hCodd S hS hs havoid
        hzeroLt (hD d hd).2 (by have := (hD d hd).1; omega) hAx0 (hBd d hd)).2
        (by simpa only [Nat.dist_zero_left, Nat.add_comm] using heven)
      exact hmemO _ (by simpa only [Nat.dist_zero_left, Nat.add_comm] using hm)
    · intro hodd
      have hxC : x ∈ c.support := c.start_mem_support
      have hxS : x ∉ S.support := fun h => havoid x h hxC
      exact hmemO _ (exterior_shared_contact_odd_length S hS hs x hxS hAx hBx hodd)
  simpa only [O, ← Set.ncard_eq_toFinset_card G.oddCycleLengths hfinite] using hcount

/-- An odd simple cycle, an exterior nonempty simple path, and at least
2k common endpoint contacts force at least k+1 actual odd cycle lengths.
No maximality or longest-cycle assumption is needed. -/
theorem exterior_common_contacts_many_odd_lengths
    (c : G.Walk x x) (hc : c.IsCycle) (hCodd : Odd c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (k : ℕ) (hk : 1 ≤ k)
    (hcontacts : 2 * k ≤ (exteriorCommonVertices c A B).ncard)
    (hfinite : G.oddCycleLengths.Finite) :
    k + 1 ≤ G.oddCycleLengths.ncard := by
  classical
  have hcard : 0 < (exteriorCommonPositions c A B).card := by
    rw [exteriorCommonPositions_card c hc]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
  obtain ⟨_, hAi, hBi⟩ := (mem_exteriorCommonPositions c A B i).mp hi
  have hiC : c.getVert i ∈ c.support := c.getVert_mem_support i
  let c' := c.rotate (c.getVert i) hiC
  have hc' : c'.IsCycle := hc.rotate hiC
  have hCodd' : Odd c'.length := by simpa only [c', Walk.length_rotate] using hCodd
  have havoid' : ∀ z ∈ S.support, z ∉ c'.support := by
    simpa only [c', Walk.mem_support_rotate_iff] using havoid
  have hcontacts' : 2 * k ≤ (exteriorCommonVertices c' A B).ncard := by
    rw [← exteriorCommonPositions_card c' hc']
    change 2 * k ≤ (exteriorCommonPositions (c.rotate (c.getVert i) hiC) A B).card
    rw [exteriorCommonPositions_rotate_card c hc, exteriorCommonPositions_card c hc]
    exact hcontacts
  exact exterior_common_contacts_normalized_many_odd_lengths
    c' hc' hCodd' S hS hs havoid' hAi hBi k hk hcontacts' hfinite

/-! ## Contact and cycle oracle bounds

Cyclic contact-coordinate memberships supplied by actual simple cycles.
The only realization premise supplies supported positive exterior paths;
there is no cycle-membership oracle in these graph theorem boundaries.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x A B : V}

/-- Actual common contacts in cyclic coordinates, with no closing duplicate. -/
noncomputable def exteriorCommonCyclicPositions (c : G.Walk x x) (A B : V) :
    Finset (ZMod c.length) := by
  classical
  exact (exteriorCommonPositions c A B).image (fun i : ℕ => (i : ZMod c.length))

@[simp] theorem mem_exteriorCommonCyclicPositions (c : G.Walk x x)
    [NeZero c.length] (A B : V) (a : ZMod c.length) :
    a ∈ exteriorCommonCyclicPositions c A B ↔
      G.Adj A (c.getVert a.val) ∧ G.Adj B (c.getVert a.val) := by
  classical
  unfold exteriorCommonCyclicPositions
  constructor
  · intro ha
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
    obtain ⟨hiL, hAi, hBi⟩ := (mem_exteriorCommonPositions c A B i).mp hi
    have haval : a.val = i := by
      rw [← hia]
      exact ZMod.val_natCast_of_lt hiL
    simpa only [haval] using And.intro hAi hBi
  · intro ha
    exact Finset.mem_image.mpr ⟨a.val,
      (mem_exteriorCommonPositions c A B a.val).mpr ⟨ZMod.val_lt a, ha⟩,
      ZMod.natCast_zmod_val a⟩

theorem exteriorCommonCyclicPositions_card_positions (c : G.Walk x x) (A B : V) :
    (exteriorCommonCyclicPositions c A B).card = (exteriorCommonPositions c A B).card := by
  classical
  unfold exteriorCommonCyclicPositions
  apply Finset.card_image_of_injOn
  intro i hi j hj heq
  have hiL := ((mem_exteriorCommonPositions c A B i).mp hi).1
  have hjL := ((mem_exteriorCommonPositions c A B j).mp hj).1
  have hv := congrArg (fun a : ZMod c.length => a.val) heq
  simpa only [ZMod.val_natCast_of_lt hiL, ZMod.val_natCast_of_lt hjL] using hv

theorem exteriorCommonCyclicPositions_card (c : G.Walk x x) (hc : c.IsCycle) (A B : V) :
    (exteriorCommonCyclicPositions c A B).card = (exteriorCommonVertices c A B).ncard := by
  rw [exteriorCommonCyclicPositions_card_positions, exteriorCommonPositions_card c hc]

/-- The two directed cyclic arcs close through an actual exterior path. -/
theorem exterior_cycle_cyclic_arc_lengths (c : G.Walk x x) (hc : c.IsCycle)
    [NeZero c.length] (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (a b : ZMod c.length) (hba : b ≠ a)
    (hAa : G.Adj A (c.getVert a.val)) (hBb : G.Adj B (c.getVert b.val)) :
    S.length + (b - a).val + 2 ∈ G.cycleLengths ∧
      S.length + (c.length - (b - a).val) + 2 ∈ G.cycleLengths := by
  have hne : a.val ≠ b.val := fun h => hba (ZMod.val_injective _ h.symm)
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  obtain ⟨hf, hcpl⟩ := exterior_cycle_distance_lengths c hc S hS hs havoid ha hb hne hAa hBb
  rcases lt_or_gt_of_ne hne with hab | hba'
  · have hd : Nat.dist a.val b.val = b.val - a.val := by simp only [Nat.dist]; omega
    have hδ : (b - a).val = b.val - a.val := ZMod.val_sub hab.le
    simpa only [hd, hδ] using And.intro hf hcpl
  · have hd : Nat.dist a.val b.val = a.val - b.val := by simp only [Nat.dist]; omega
    have hδ : (b - a).val = c.length - (a.val - b.val) := by
      have hnz : a - b ≠ 0 := fun h => hba (sub_eq_zero.mp h).symm
      have : NeZero (a - b) := ⟨hnz⟩
      have hneg := ZMod.val_neg_of_ne_zero (a - b)
      rw [ZMod.val_sub hba'.le] at hneg
      simpa only [neg_sub] using hneg
    refine ⟨by simpa only [hd, hδ] using hcpl, ?_⟩
    have hδc : c.length - (b - a).val = a.val - b.val := by rw [hδ]; omega
    simpa only [hd, hδc] using hf

theorem exterior_cycle_cyclic_odd_lengths (c : G.Walk x x) (hc : c.IsCycle)
    [NeZero c.length] (hCodd : Odd c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (a b : ZMod c.length) (hba : b ≠ a)
    (hAa : G.Adj A (c.getVert a.val)) (hBb : G.Adj B (c.getVert b.val)) :
    (Odd (S.length + (b - a).val) →
      S.length + (b - a).val + 2 ∈ G.oddCycleLengths) ∧
    (Even (S.length + (b - a).val) →
      S.length + (c.length - (b - a).val) + 2 ∈ G.oddCycleLengths) := by
  obtain ⟨hf, hb⟩ := exterior_cycle_cyclic_arc_lengths c hc S hS hs havoid a b hba hAa hBb
  refine ⟨fun hodd => ?_, fun heven => ?_⟩
  · obtain ⟨_, q, hq, hlen⟩ := mem_cycleLengths hf
    refine mem_oddCycleLengths_intro hq ?_ ?_
    · rw [← hlen]
    · exact hodd.add_even (by simp)
  · obtain ⟨_, q, hq, hlen⟩ := mem_cycleLengths hb
    refine mem_oddCycleLengths_intro hq ?_ ?_
    · rw [← hlen]
    · have hparity : Odd (S.length + (c.length - (b - a).val) + 2) := by
        have hd := ZMod.val_lt (b - a)
        simp only [Nat.odd_iff] at hCodd ⊢
        simp only [Nat.even_iff] at heven
        omega
      exact hparity

/-- The cyclic contact oracle used in the saturated common-contact case.
Shift 2 is realized through the outside vertex A, and every other shift
h+2 is realized through a supplied actual positive exterior A-to-B path. -/
theorem contact_cycle_oracles (c : G.Walk x x) (hc : c.IsCycle)
    [NeZero c.length] (hCodd : Odd c.length)
    (S : G.Walk A B) (_hS : S.IsPath) (_hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (X : Finset (ZMod c.length))
    (hcontacts : ∀ a ∈ X, G.Adj A (c.getVert a.val) ∧ G.Adj B (c.getVert a.val))
    (R : Finset ℕ)
    (hrealize : ∀ h ∈ R, ∃ p : G.Walk A B,
      p.IsPath ∧ p.length = h ∧ 1 ≤ p.length ∧
        ∀ z ∈ p.support, z ∉ c.support) :
    ∀ a ∈ X, ∀ b ∈ X, a ≠ b →
      ∀ t ∈ insert 2 (R.image (fun h => h + 2)),
        Odd ((b - a).val + t) → (b - a).val + t ∈ G.oddCycleLengths := by
  intro a ha b hb hab t ht hodd
  rcases Finset.mem_insert.mp ht with rfl | ht
  · have hAout : A ∉ c.support := havoid A S.start_mem_support
    have hδodd : Odd (b - a).val := by
      simp only [Nat.odd_iff] at hodd ⊢
      omega
    exact (outside_cycle_cyclic_odd_lengths c hc hCodd hAout a b hab.symm
      (hcontacts a ha).1 (hcontacts b hb).1).1 hδodd
  · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨p, hp, hlen, hpos, hdis⟩ := hrealize h hh
    have hpar : Odd (p.length + (b - a).val) := by
      rw [hlen]
      simp only [Nat.odd_iff] at hodd ⊢
      omega
    have hm := (exterior_cycle_cyclic_odd_lengths c hc hCodd p hp hpos hdis
      a b hab.symm (hcontacts a ha).1 (hcontacts b hb).2).1 hpar
    simpa only [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

/-! ## Distinct contacts

The repaired different-contact counting argument for actual graph cycles.
Only two contacts at B are needed. The 2k selected A-contacts are a subset
of the actual contacts, and every numeric membership is witnessed by an
actual simple cycle. The longest odd-cycle bound is explicit.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x A B r : V}

/-- Both natural-distance arcs through an outside common neighbor give
actual cycles, regardless of the order of the contact positions. -/
theorem outside_cycle_distance_lengths (c : G.Walk x x) (hc : c.IsCycle)
    (hr : r ∉ c.support) {i j : ℕ} (hi : i < c.length) (hj : j < c.length)
    (hne : i ≠ j) (hri : G.Adj r (c.getVert i)) (hrj : G.Adj r (c.getVert j)) :
    Nat.dist i j + 2 ∈ G.cycleLengths ∧
      c.length - Nat.dist i j + 2 ∈ G.cycleLengths := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hd : Nat.dist i j = j - i := by simp only [Nat.dist]; omega
    obtain ⟨q, hq, hql⟩ := outside_cycle_forward_witness c hc hr hij hj hri hrj
    obtain ⟨q', hq', hql'⟩ := outside_cycle_complement_witness c hc hr hij hj hri hrj
    exact ⟨mem_cycleLengths_intro hq (by simpa only [hd] using hql),
      mem_cycleLengths_intro hq' (by simpa only [hd] using hql')⟩
  · have hd : Nat.dist i j = i - j := by simp only [Nat.dist]; omega
    obtain ⟨q, hq, hql⟩ := outside_cycle_forward_witness c hc hr hji hi hrj hri
    obtain ⟨q', hq', hql'⟩ := outside_cycle_complement_witness c hc hr hji hi hrj hri
    exact ⟨mem_cycleLengths_intro hq (by simpa only [hd] using hql),
      mem_cycleLengths_intro hq' (by simpa only [hd] using hql')⟩

theorem outside_cycle_distance_odd_lengths (c : G.Walk x x) (hc : c.IsCycle)
    (hCodd : Odd c.length) (hr : r ∉ c.support) {i j : ℕ}
    (hi : i < c.length) (hj : j < c.length) (hne : i ≠ j)
    (hri : G.Adj r (c.getVert i)) (hrj : G.Adj r (c.getVert j)) :
    (Odd (Nat.dist i j) → Nat.dist i j + 2 ∈ G.oddCycleLengths) ∧
    (Even (Nat.dist i j) → c.length - Nat.dist i j + 2 ∈ G.oddCycleLengths) := by
  obtain ⟨hf, hb⟩ := outside_cycle_distance_lengths c hc hr hi hj hne hri hrj
  refine ⟨fun hodd => ?_, fun heven => ?_⟩
  · obtain ⟨_, q, hq, hlen⟩ := mem_cycleLengths hf
    refine mem_oddCycleLengths_intro hq ?_ ?_
    · rw [← hlen]
    · exact hodd.add_even (by simp)
  · obtain ⟨_, q, hq, hlen⟩ := mem_cycleLengths hb
    refine mem_oddCycleLengths_intro hq ?_ ?_
    · rw [← hlen]
    · have hparity : Odd (c.length - Nat.dist i j + 2) := by
        have hd : Nat.dist i j < c.length := by simp only [Nat.dist]; omega
        simp only [Nat.odd_iff] at hCodd ⊢
        simp only [Nat.even_iff] at heven
        omega
      exact hparity

/-- The normalized different-contact case. Position zero is a B-contact
outside all A-contacts; only 2k of the available A-contacts are selected. -/
theorem exterior_different_contacts_normalized_many_odd_lengths
    (c : G.Walk x x) (hc : c.IsCycle) (hCodd : Odd c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hAx : ¬ G.Adj A x) (hBx : G.Adj B x)
    (k : ℕ) (hk : 1 ≤ k)
    (hAcontacts : 2 * k ≤ (exteriorCommonVertices c A A).ncard)
    (hBcontacts : 2 ≤ (exteriorCommonVertices c B B).ncard)
    (hcap : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (hfinite : G.oddCycleLengths.Finite) :
    k + 1 ≤ G.oddCycleLengths.ncard := by
  classical
  let X := exteriorCommonPositions c A A
  let Z := exteriorCommonPositions c B B
  have hXcard : 2 * k ≤ X.card := by
    simpa only [X, exteriorCommonPositions_card c hc] using hAcontacts
  obtain ⟨D, hDX, hDcard⟩ := Finset.exists_subset_card_eq hXcard
  let O := hfinite.toFinset
  have hD : ∀ d ∈ D, 0 < d ∧ d < c.length := by
    intro d hd
    obtain ⟨hdL, hAd, _⟩ := (mem_exteriorCommonPositions c A A d).mp (hDX hd)
    have hdne : d ≠ 0 := by
      intro hd0
      exact hAx (by simpa only [hd0, Walk.getVert_zero] using hAd)
    exact ⟨Nat.pos_of_ne_zero hdne, hdL⟩
  have hAd : ∀ d ∈ D, G.Adj A (c.getVert d) := by
    intro d hd
    exact ((mem_exteriorCommonPositions c A A d).mp (hDX hd)).2.1
  have hZ : ∀ z ∈ Z, z < c.length := by
    intro z hz
    exact ((mem_exteriorCommonPositions c B B z).mp hz).1
  have hBz : ∀ z ∈ Z, G.Adj B (c.getVert z) := by
    intro z hz
    exact ((mem_exteriorCommonPositions c B B z).mp hz).2.1
  have hzero : 0 ∈ Z := by
    apply (mem_exteriorCommonPositions c B B 0).mpr
    exact ⟨by have := hc.three_le_length; omega, by simpa using hBx, by simpa using hBx⟩
  have hZcard : 2 ≤ Z.card := by
    simpa only [Z, exteriorCommonPositions_card c hc] using hBcontacts
  have hAout : A ∉ c.support := havoid A S.start_mem_support
  have hmemO : ∀ n, n ∈ G.oddCycleLengths → n ∈ O := by
    intro n hn
    exact hfinite.mem_toFinset.mpr hn
  have hcount : k + 1 ≤ O.card := by
    apply different_contacts_lengths_card D Z O hc.three_le_length hCodd hs hk
      hD hDcard hZ hzero hZcard
    · exact hmemO _ (mem_oddCycleLengths_intro hc rfl hCodd)
    · intro n hn
      exact hcap n (hfinite.mem_toFinset.mp hn)
    · intro d hd e he hne hodd
      exact hmemO _ ((outside_cycle_distance_odd_lengths c hc hCodd hAout
        (hD d hd).2 (hD e he).2 hne (hAd d hd) (hAd e he)).1 hodd)
    · intro d hd e he hne heven
      exact hmemO _ ((outside_cycle_distance_odd_lengths c hc hCodd hAout
        (hD d hd).2 (hD e he).2 hne (hAd d hd) (hAd e he)).2 heven)
    · intro d hd z hz hne hodd
      exact hmemO _ ((exterior_cycle_distance_odd_lengths c hc hCodd S hS hs havoid
        (hD d hd).2 (hZ z hz) hne (hAd d hd) (hBz z hz)).1 hodd)
    · intro d hd z hz hne heven
      exact hmemO _ ((exterior_cycle_distance_odd_lengths c hc hCodd S hS hs havoid
        (hD d hd).2 (hZ z hz) hne (hAd d hd) (hBz z hz)).2 heven)
  simpa only [O, ← Set.ncard_eq_toFinset_card G.oddCycleLengths hfinite] using hcount

/-- At least 2k A-contacts, two B-contacts, and one B-contact absent from A
force k+1 actual odd cycle lengths under the explicit longest-cycle bound. -/
theorem exterior_different_contacts_many_odd_lengths
    (c : G.Walk x x) (hc : c.IsCycle) (hCodd : Odd c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (k : ℕ) (hk : 1 ≤ k)
    (hAcontacts : 2 * k ≤ (exteriorCommonVertices c A A).ncard)
    (hBcontacts : 2 ≤ (exteriorCommonVertices c B B).ncard)
    (hdifferent : ∃ r, r ∈ c.support ∧ G.Adj B r ∧ ¬ G.Adj A r)
    (hcap : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (hfinite : G.oddCycleLengths.Finite) :
    k + 1 ≤ G.oddCycleLengths.ncard := by
  classical
  obtain ⟨r, hrC, hBr, hAr⟩ := hdifferent
  let c' := c.rotate r hrC
  have hc' : c'.IsCycle := hc.rotate hrC
  have hCodd' : Odd c'.length := by simpa only [c', Walk.length_rotate] using hCodd
  have havoid' : ∀ z ∈ S.support, z ∉ c'.support := by
    simpa only [c', Walk.mem_support_rotate_iff] using havoid
  have hAcontacts' : 2 * k ≤ (exteriorCommonVertices c' A A).ncard := by
    rw [← exteriorCommonPositions_card c' hc']
    change 2 * k ≤ (exteriorCommonPositions (c.rotate r hrC) A A).card
    rw [exteriorCommonPositions_rotate_card c hc, exteriorCommonPositions_card c hc]
    exact hAcontacts
  have hBcontacts' : 2 ≤ (exteriorCommonVertices c' B B).ncard := by
    rw [← exteriorCommonPositions_card c' hc']
    change 2 ≤ (exteriorCommonPositions (c.rotate r hrC) B B).card
    rw [exteriorCommonPositions_rotate_card c hc, exteriorCommonPositions_card c hc]
    exact hBcontacts
  have hcap' : ∀ n ∈ G.oddCycleLengths, n ≤ c'.length := by
    simpa only [c', Walk.length_rotate] using hcap
  exact exterior_different_contacts_normalized_many_odd_lengths
    c' hc' hCodd' S hS hs havoid' hAr hBr k hk hAcontacts' hBcontacts' hcap' hfinite

/-! ## Local counting in the exterior -/

/-! Distinct exterior endpoint shortcuts and their local odd cycles.
The numerical counting theorem is applied only after constructing these
actual paths and the cycles obtained from their attachment arcs. -/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b r : V}

def fanShortcut (p : G.Walk a b) (r : V) (i : ℕ)
    (hi : i ≤ p.length) (hedge : G.Adj r (p.getVert i)) : G.Walk r b :=
  (Walk.cons hedge (pathInterval p i p.length hi)).copy rfl (p.getVert_length)

theorem fanShortcut_isPath (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (i : ℕ) (hi : i ≤ p.length)
    (hedge : G.Adj r (p.getVert i)) : (fanShortcut p r i hi hedge).IsPath := by
  apply (Walk.isPath_copy _ _ _).mpr
  exact (pathInterval_isPath p hp i p.length hi).cons
    (fun h => hr (pathInterval_support_subset p i p.length hi h))

theorem fanShortcut_length (p : G.Walk a b) (r : V) (i : ℕ)
    (hi : i ≤ p.length) (hedge : G.Adj r (p.getVert i)) :
    (fanShortcut p r i hi hedge).length = p.length - i + 1 := by
  simp only [fanShortcut, Walk.length_copy, Walk.length_cons,
    pathInterval_length p i p.length hi le_rfl]

theorem fanShortcut_support (p : G.Walk a b) (r : V) (i : ℕ)
    (hi : i ≤ p.length) (hedge : G.Adj r (p.getVert i)) :
    ∀ z ∈ (fanShortcut p r i hi hedge).support, z = r ∨ z ∈ p.support := by
  intro z hz
  rw [fanShortcut, Walk.support_copy, Walk.support_cons] at hz
  rcases List.mem_cons.mp hz with hzr | hz
  · exact Or.inl hzr
  · exact Or.inr (pathInterval_support_subset p i p.length hi hz)

/-- The shortcut family has precisely one length for each neighbor position.
Its least member has the opposite parity to the terminal-tail length `a`;
the other parity gives genuine local odd cycles, never the invalid length 2. -/
theorem fan_shortcut_length_family (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (hne : (pathNeighborPositions p r).Nonempty) :
    ∃ a₀ : ℕ, ∃ X : Finset ℕ,
      X.card = (pathNeighborPositions p r).card ∧
      a₀ + 1 ∈ X ∧ (∀ x ∈ X, a₀ + 1 ≤ x) ∧
      (∀ x ∈ X, x % 2 = a₀ % 2 → x - a₀ + 1 ∈ G.oddCycleLengths) ∧
      (∀ x ∈ X, ∃ q : G.Walk r b, q.IsPath ∧ q.length = x ∧
        ∀ z ∈ q.support, z = r ∨ z ∈ p.support) := by
  classical
  let S := pathNeighborPositions p r
  let m := S.max' hne
  have hmmem : m ∈ S := S.max'_mem hne
  have hm := (mem_pathNeighborPositions p r m).mp hmmem
  let a₀ := p.length - m
  let X := S.image (fun i => p.length - i + 1)
  have hxi : Set.InjOn (fun i => p.length - i + 1) S := by
    intro i hi j hj heq
    have hi' := ((mem_pathNeighborPositions p r i).mp hi).1
    have hj' := ((mem_pathNeighborPositions p r j).mp hj).1
    change p.length - i + 1 = p.length - j + 1 at heq
    omega
  refine ⟨a₀, X, Finset.card_image_of_injOn hxi, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨m, hmmem, rfl⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have him := S.le_max' i hi
    dsimp [a₀]
    omega
  · intro x hx hpar
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    have hi' := (mem_pathNeighborPositions p r i).mp hi
    have him := S.le_max' i hi
    have himlt : i < m := by
      dsimp [a₀] at hpar
      omega
    have hdiff : i % 2 ≠ m % 2 := by
      dsimp [a₀] at hpar
      omega
    have hcycle := fan_odd_cycle_length p hp hr himlt hm.1 hi'.2 hm.2 hdiff
    have hlen : x - a₀ + 1 = m - i + 2 := by dsimp [a₀]; omega
    exact hlen.symm ▸ hcycle
  · intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    have hi' := (mem_pathNeighborPositions p r i).mp hi
    refine ⟨fanShortcut p r i hi'.1 hi'.2,
      fanShortcut_isPath p hp hr i hi'.1 hi'.2, ?_,
      fanShortcut_support p r i hi'.1 hi'.2⟩
    exact (fanShortcut_length p r i hi'.1 hi'.2).trans hix

/-- Gyárfás's local endpoint count, with all three cycle families constructed
from actual paths. The chosen B contact at the cycle root is excluded from
the nonempty A-contact index set D. No cycle oracle is an input. -/
theorem exterior_local_length_count {x : V}
    (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    (hrC : r ∉ c.support) (hpC : ∀ z ∈ p.support, z ∉ c.support)
    (hBx : G.Adj b x) (hfin : G.oddCycleLengths.Finite)
    (D : Finset ℕ) (hD : ∀ i ∈ D, 0 < i ∧ i < c.length ∧ G.Adj r (c.getVert i))
    (hDne : D.Nonempty) (q₀ : ℕ)
    (hsize : (pathNeighborPositions p r).card = q₀ + 1) :
    q₀ + (D.card + 1) / 2 ≤ G.oddCycleLengths.ncard := by
  classical
  have hSne : (pathNeighborPositions p r).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a₀, X, hXcard, hminmem, hmin, hlocal, hpaths⟩ :=
    fan_shortcut_length_family p hp hr hSne
  let O := hfin.toFinset
  let Y := D.image (fun i => i + 2)
  have hYcard : Y.card = D.card := Finset.card_image_of_injective D (by
    intro i j h
    change i + 2 = j + 2 at h
    omega)
  have hYne : Y.Nonempty := hDne.image _
  have hYbounds : ∀ y ∈ Y, 3 ≤ y ∧ y ≤ c.length + 1 := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have := hD i hi
    omega
  have hcycles : ∀ n ∈ X, ∀ i ∈ D,
      (Odd (n + i + 2) → n + i + 2 ∈ O) ∧
      (Even (n + i + 2) → n + (c.length - i) + 2 ∈ O) := by
    intro n hn i hi
    obtain ⟨S, hS, hlen, hsub⟩ := hpaths n hn
    have hs : 1 ≤ S.length := by have := hmin n hn; omega
    have havoid : ∀ z ∈ S.support, z ∉ c.support := by
      intro z hz
      rcases hsub z hz with rfl | hzp
      · exact hrC
      · exact hpC z hzp
    have hd := hD i hi
    have hgeom := exterior_cycle_distance_odd_lengths c hc hodd S hS hs havoid (i := i) (j := 0)
      hd.2.1 (by have := hc.three_le_length; omega) (by omega) hd.2.2
      (by simpa only [Walk.getVert_zero] using hBx)
    have hdist : Nat.dist i 0 = i := by simp [Nat.dist]
    simp only [hlen, hdist] at hgeom
    constructor
    · intro hpar
      apply hfin.mem_toFinset.mpr
      exact hgeom.1 (by rw [Nat.odd_iff] at hpar ⊢; omega)
    · intro hpar
      apply hfin.mem_toFinset.mpr
      exact hgeom.2 (by rw [Nat.even_iff] at hpar ⊢; omega)
  have hcount := local_length_counting O X Y c.length a₀ q₀ hodd
    (fun n hn => hmax n (hfin.mem_toFinset.mp hn))
    (hXcard.trans hsize) hminmem hmin hYne hYbounds
    (fun n hn hpar => hfin.mem_toFinset.mpr (hlocal n hn hpar))
    (by
      intro n hn y hy hpar
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (hcycles n hn i hi).1 (by simpa only [Nat.add_assoc] using hpar))
    (by
      intro n hn y hy hpar
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hg := (hcycles n hn i hi).2 (by simpa only [Nat.add_assoc] using hpar)
      have hiL := (hD i hi).2.1
      have heq : n + (c.length + 4 - (i + 2)) = n + (c.length - i) + 2 := by omega
      exact heq.symm ▸ hg)
  simpa only [hYcard, O, ← Set.ncard_eq_toFinset_card G.oddCycleLengths hfin] using hcount

/-! ## Odd-cycle counting in the exterior

The exterior of a longest odd cycle loses that cycle's odd length.
This is a strict cardinality reduction for the actual cycle-length sets in #58.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Every exterior odd cycle maps to an ambient odd cycle, whose length differs
from the longest cycle's length by the proved disjoint-cycle comparison. -/
theorem exterior_oddCycleLengths_subset (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length) :
    (G.induce {z | z ∉ c.support}).oddCycleLengths ⊆
      G.oddCycleLengths \ {c.length} := by
  intro n hn
  let f := Copy.induce G {z | z ∉ c.support}
  have hnG := f.oddCycleLengths_subset hn
  refine ⟨hnG, ?_⟩
  intro hne
  have hnc : n = c.length := Set.mem_singleton_iff.mp hne
  obtain ⟨v, d, hd, hlen, hoddn⟩ := mem_oddCycleLengths_elim hn
  let q := Walk.map f.toHom d
  have hq : q.IsCycle := hd.map f.injective
  have hqlen : q.length = n := (Walk.length_map f.toHom d).trans hlen
  have hqodd : Odd q.length := by simpa only [hqlen] using hoddn
  have hdisj : c.support.Disjoint q.support := by
    intro z hzc hzq
    change z ∈ (Walk.map f.toHom d).support at hzq
    rw [Walk.support_map] at hzq
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp hzq
    change u.val = z at heq
    exact u.property (heq.symm ▸ hzc)
  have hlt := longest_odd_cycle_disjoint_shorter hG hdel c hc hodd hmax q hq hqodd hdisj
  omega

/-- The exterior odd-length set has at least one fewer member than the ambient
set. Finiteness applies to the length set, with no finite-vertex assumption. -/
theorem exterior_oddCycleLengths_ncard_add_one_le (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (hfin : G.oddCycleLengths.Finite) :
    (G.induce {z | z ∉ c.support}).oddCycleLengths.ncard + 1 ≤
      G.oddCycleLengths.ncard := by
  have hsub := exterior_oddCycleLengths_subset hG hdel c hc hodd hmax
  have houtfin : (G.induce {z | z ∉ c.support}).oddCycleLengths.Finite :=
    hfin.subset (fun n hn => (hsub hn).1)
  have hcnot : c.length ∉ (G.induce {z | z ∉ c.support}).oddCycleLengths := by
    intro h
    exact (hsub h).2 (by simp)
  have hcmem : c.length ∈ G.oddCycleLengths :=
    mem_oddCycleLengths_intro hc rfl hodd
  have hins : insert c.length (G.induce {z | z ∉ c.support}).oddCycleLengths ⊆
      G.oddCycleLengths := Set.insert_subset hcmem (fun n hn => (hsub hn).1)
  have hcard := Set.ncard_le_ncard hins hfin
  rwa [Set.ncard_insert_of_notMem hcnot houtfin] at hcard

/-- Any ambient bound `k` strictly exceeds the exterior odd-length count.
In particular the existence of the given odd cycle makes `k ≥ 1` automatic. -/
theorem exterior_oddCycleLengths_ncard_lt (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (hfin : G.oddCycleLengths.Finite) {k : ℕ} (hcard : G.oddCycleLengths.ncard ≤ k) :
    (G.induce {z | z ∉ c.support}).oddCycleLengths.ncard < k := by
  have h := exterior_oddCycleLengths_ncard_add_one_le hG hdel c hc hodd hmax hfin
  omega

/-- With at most one odd length, the exterior contains no odd simple cycle. -/
theorem exterior_oddCycleLengths_empty_of_ncard_le_one (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (hfin : G.oddCycleLengths.Finite) (hcard : G.oddCycleLengths.ncard ≤ 1) :
    (G.induce {z | z ∉ c.support}).oddCycleLengths = ∅ := by
  have houtfin := (Copy.induce G {z | z ∉ c.support}).oddCycleLengths_finite hfin
  have hlt := exterior_oddCycleLengths_ncard_lt hG hdel c hc hodd hmax hfin hcard
  exact (Set.ncard_eq_zero houtfin).mp (by omega)

/-- The exact one-odd-length case makes every longest-cycle exterior
two-colorable, using the already proved odd-cycle obstruction theorem. -/
theorem exterior_colorable_two_of_ncard_le_one (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (hfin : G.oddCycleLengths.Finite) (hcard : G.oddCycleLengths.ncard ≤ 1) :
    (G.induce {z | z ∉ c.support}).Colorable 2 :=
  colorable_two_of_oddCycleLengths_empty _
    (exterior_oddCycleLengths_empty_of_ncard_le_one hG hdel c hc hodd hmax hfin hcard)

/-! ## Fan attachment

Many same-parity paths in an exterior set force many odd cycle lengths.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem exterior_same_parity_paths_force_odd_lengths
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (B : Set V) (hdis : Disjoint {z | z ∈ c.support} B)
    (hBpair : ∃ u ∈ B, ∃ v ∈ B, u ≠ v) (k : ℕ)
    (hmany : ∀ u ∈ B, ∀ v ∈ B, u ≠ v →
      ∃ ε < 2, k + 1 ≤ (parityPathLengthsWithin G B u v ε).ncard)
    (hfin : G.oddCycleLengths.Finite) : k + 1 ≤ G.oddCycleLengths.ncard := by
  classical
  let A : Set V := {z | z ∈ c.support}
  obtain ⟨u₁, hu₁, u₂, hu₂, v₁, hv₁, v₂, hv₂, huu, hvv,
    p₁, p₂, hp₁, hp₂, hpdisj, hA₁, hB₁, hA₂, hB₂⟩ :=
    twoConnectors hG hdel A B hdis (LongestOddCycle.cycle_distinct_pair c hc) hBpair
  obtain ⟨C₁, C₂, hC₁, hC₂, hCsub₁, hCsub₂, hCsum, hCpos₁, hCpos₂⟩ :=
    LongestOddCycle.two_arcs c hc hu₁ hu₂ huu
  obtain ⟨ε, hε, hcount⟩ := hmany v₁ hv₁ v₂ hv₂ hvv
  have huv₁ : u₁ ≠ v₁ := by
    intro h
    exact Set.disjoint_left.mp hdis hu₁ (h.symm ▸ hv₁)
  have huv₂ : u₂ ≠ v₂ := by
    intro h
    exact Set.disjoint_left.mp hdis hu₂ (h.symm ▸ hv₂)
  let t := p₁.length + p₂.length
  have ht : 2 ≤ t := by
    have := LongestOddCycle.walk_length_pos p₁ huv₁
    have := LongestOddCycle.walk_length_pos p₂ huv₂
    omega
  have hchoice : ∃ C : G.Walk u₁ u₂, C.IsPath ∧
      (∀ z, z ∈ C.support → z ∈ A) ∧ 0 < C.length ∧
      (t + C.length + ε) % 2 = 1 := by
    by_cases h₁ : (t + C₁.length + ε) % 2 = 1
    · exact ⟨C₁, hC₁, hCsub₁, hCpos₁, h₁⟩
    · refine ⟨C₂, hC₂, hCsub₂, hCpos₂, ?_⟩
      rw [Nat.odd_iff] at hodd
      omega
  obtain ⟨C, hC, hCsub, hCpos, hCpar⟩ := hchoice
  let P := parityPathLengthsWithin G B v₁ v₂ ε
  have hmap : Set.MapsTo (fun n : ℕ ↦ t + C.length + n) P G.oddCycleLengths := by
    intro n hn
    have hpair := parityPathLengthsWithin_eq.mp hn
    have hpath : n ∈ pathLengthsWithin G B v₁ v₂ := hpair.1
    have hnpar : n % 2 = ε := hpair.2
    obtain ⟨q, hq, hlen, hqsub⟩ := mem_pathLengthsWithin_iff.mp hpath
    have hwn := LongestOddCycle.bridge_cycle_length A B hdis p₁ p₂ hp₁ hp₂ hpdisj
      hA₁ hB₁ hA₂ hB₂ C q hC hq hCsub hqsub (by omega)
    rw [hlen] at hwn
    obtain ⟨v, w, hwC, hwl⟩ := mem_cycleLengths hwn
    refine mem_oddCycleLengths_intro hwC hwl ?_
    rw [Nat.odd_iff]
    show (t + C.length + n) % 2 = 1
    have hkey : (t + C.length + n) % 2 = 1 := by
      omega
    exact hkey
  have hinj : Set.InjOn (fun n : ℕ ↦ t + C.length + n) P := by
    intro n hn m hm hnm
    dsimp at hnm
    omega
  exact hcount.trans (Set.ncard_le_ncard_of_injOn _ hmap hinj hfin)

/-- A bipartite fan outside an odd cycle forces k+1 distinct odd lengths
in a graph with two disjoint connectors. The counted fan paths retain
their support restriction when they are spliced to the cycle. -/
theorem exterior_bipartite_fan_force_odd_lengths [Finite V]
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a b x r : V} (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    (houtside : Disjoint {z | z ∈ c.support} {z | z = r ∨ z ∈ p.support})
    (h0 : G.Adj r a) (hL : G.Adj r b)
    (he : ∀ s ∈ pathNeighborPositions p r, Even s)
    {k : ℕ} (hk : 1 ≤ k) (hsize : 2 * k + 1 ≤ (pathNeighborPositions p r).card)
    (hfin : G.oddCycleLengths.Finite) : k + 1 ≤ G.oddCycleLengths.ncard := by
  apply exterior_same_parity_paths_force_odd_lengths hG hdel c hc hodd
    {z | z = r ∨ z ∈ p.support} houtside _ k _ hfin
  · refine ⟨r, Or.inl rfl, a, Or.inr p.start_mem_support, ?_⟩
    exact h0.ne
  · intro u hu v hv huv
    exact bipartite_neighbor_fan_many_paths_within p hp hr h0 hL he hk hsize huv hu hv

/-! ## Four-contact cyclic orderings -/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x A B u v z : V}

/-- A simple arc closes through two exterior vertices and one vertex absent
from the arc, giving an actual cycle four edges longer than that arc. -/
theorem four_contact_proper_arc_length (c : G.Walk x x) (p : G.Walk u v)
    (hp : p.IsPath) (hpsub : p.support ⊆ c.support) (huv : u ≠ v)
    (hA : A ∉ c.support) (hB : B ∉ c.support) (hAB : A ≠ B)
    (hz : z ∉ p.support) (hAu : G.Adj A u) (hBv : G.Adj B v)
    (hAz : G.Adj A z) (hBz : G.Adj B z) :
    p.length + 4 ∈ G.cycleLengths := by
  have hAv : A ≠ v := by
    intro h
    apply hA
    simpa only [h] using hpsub p.end_mem_support
  have huB : u ≠ B := by
    intro h
    apply hB
    simpa only [← h] using hpsub p.start_mem_support
  have huz : u ≠ z := by
    intro h
    exact hz (h ▸ p.start_mem_support)
  have hzv : z ≠ v := by
    intro h
    exact hz (h.symm ▸ p.end_mem_support)
  let w : G.Walk u v := Walk.cons hAu.symm
    (Walk.cons hAz (Walk.cons hBz.symm (Walk.cons hBv Walk.nil)))
  have hw : w.IsPath := by
    simp [w, Walk.isPath_def, hAu.ne.symm, hAz.ne, hAB, hAv,
      hBz.ne.symm, hzv, hBv.ne, huB, huz, huv]
  have hwlen : w.length = 4 := by simp [w]
  have hmeet : ∀ y, y ∈ p.support → y ∈ w.support → y = u ∨ y = v := by
    intro y hyp hyw
    simp only [w, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hyw
    rcases hyw with hy | hy | hy | hy | hy
    · exact Or.inl hy
    · exact (hA (hy ▸ hpsub hyp)).elim
    · exact (hz (hy ▸ hyp)).elim
    · exact (hB (hy ▸ hpsub hyp)).elim
    · exact Or.inr hy
  refine mem_cycleLengths_intro
    (cycle_of_two_paths p w hp hw hmeet (by omega)) ?_
  rw [two_paths_cycle_length, hwlen]

private theorem cyclic_val_sub {n : ℕ} [NeZero n] (a b : ZMod n) :
    (b - a).val = if a.val ≤ b.val then b.val - a.val
      else n - (a.val - b.val) := by
  split_ifs with h
  · exact ZMod.val_sub h
  · have hba : b.val < a.val := by omega
    have hne : a - b ≠ 0 := by
      intro heq
      have he := congrArg ZMod.val (sub_eq_zero.mp heq)
      omega
    have : NeZero (a - b) := ⟨hne⟩
    have he := ZMod.val_neg_of_ne_zero (a - b)
    rw [ZMod.val_sub hba.le] at he
    simpa only [neg_sub] using he

private theorem four_interval_support_range (c : G.Walk x x) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ c.length) {y : V}
    (hy : y ∈ (pathInterval c i j hij).support) :
    ∃ s, i ≤ s ∧ s ≤ j ∧ c.getVert s = y := by
  obtain ⟨s, hs, hsl⟩ := Walk.mem_support_iff_exists_getVert.mp hy
  rw [pathInterval_length c i j hij hj] at hsl
  refine ⟨i + s, by omega, by omega, ?_⟩
  simpa only [pathInterval_getVert c i j hij s
    (show i + s ≤ j by omega)] using hs

/-- Four contacts at arbitrary cyclic positions give a genuine odd cycle.
The common contact lies later than the chosen forward arc, so its vertex is
absent from that arc even when the arc crosses the indexed cycle root. -/
theorem four_contact_cyclic_odd_length (c : G.Walk x x) (hc : c.IsCycle)
    [NeZero c.length] (hA : A ∉ c.support) (hB : B ∉ c.support) (hAB : A ≠ B)
    (a b t : ZMod c.length) (hodd : Odd (b - a).val)
    (hbt : (b - a).val < (t - a).val)
    (hAa : G.Adj A (c.getVert a.val)) (hBb : G.Adj B (c.getVert b.val))
    (hAt : G.Adj A (c.getVert t.val)) (hBt : G.Adj B (c.getVert t.val)) :
    (b - a).val + 4 ∈ G.oddCycleLengths := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have ht := ZMod.val_lt t
  have hdpos : 0 < (b - a).val := by
    rw [Nat.odd_iff] at hodd
    omega
  have habne : a.val ≠ b.val := by
    intro heq
    have he : a = b := ZMod.val_injective _ heq
    subst b
    simp at hdpos
  have huv : c.getVert a.val ≠ c.getVert b.val := by
    intro heq
    exact habne (hc.getVert_injOn'
      (show a.val ≤ c.length - 1 by omega)
      (show b.val ≤ c.length - 1 by omega) heq)
  have hlength : (b - a).val + 4 ∈ G.cycleLengths := by
    by_cases hab : a.val < b.val
    · let p := pathInterval c a.val b.val hab.le
      have hp : p.IsPath := pathInterval_isPath_cycle c hc a.val b.val hab.le
        (by have := hc.three_le_length; omega)
      have hpsub : p.support ⊆ c.support :=
        pathInterval_support_subset c a.val b.val hab.le
      have hplen : p.length = (b - a).val := by
        rw [ZMod.val_sub hab.le]
        exact pathInterval_length c a.val b.val hab.le hb.le
      have htnot : c.getVert t.val ∉ p.support := by
        intro hmem
        obtain ⟨s, his, hsj, hse⟩ := four_interval_support_range c hab.le hb.le hmem
        have hst := hc.getVert_injOn'
          (show s ≤ c.length - 1 by omega)
          (show t.val ≤ c.length - 1 by omega) hse
        have hval : (t - a).val = t.val - a.val := ZMod.val_sub (by omega)
        rw [ZMod.val_sub hab.le, hval] at hbt
        omega
      simpa only [hplen] using four_contact_proper_arc_length c p hp hpsub huv
        hA hB hAB htnot hAa hBb hAt hBt
    · have hba : b.val < a.val := by omega
      have hd : (b - a).val = c.length - (a.val - b.val) := by
        rw [cyclic_val_sub, ite_eq_right (show ¬a.val ≤ b.val by omega)]
      have hta : t.val < a.val := by
        by_contra! hat
        rw [hd, ZMod.val_sub hat] at hbt
        omega
      have htb : b.val < t.val := by
        rw [hd, cyclic_val_sub a t,
          ite_eq_right (show ¬a.val ≤ t.val by omega)] at hbt
        omega
      let p := cycleComplementArc c b.val a.val
      have hp : p.IsPath := cycleComplementArc_isPath c hc hba ha
      have hpsub : p.support ⊆ c.support :=
        cycleComplementArc_support_subset c b.val a.val
      have hplen : p.length = (b - a).val := by
        rw [hd]
        have he := cycleComplementArc_length c hb.le ha.le
        change (cycleComplementArc c b.val a.val).length = _
        rw [he]
        omega
      have htnot : c.getVert t.val ∉ (cycleComplementArc c b.val a.val).support := by
        intro hmem
        have hmem' :
            c.getVert t.val ∈ ((c.drop a.val).append (c.take b.val)).support := by
          rw [← cycleComplementArc_eq]
          exact hmem
        rw [Walk.mem_support_append_iff] at hmem'
        rcases hmem' with hmem | hmem
        · obtain ⟨s, hs, hsl⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
          rw [Walk.drop_length] at hsl
          rw [Walk.drop_getVert] at hs
          have he := hc.getVert_injOn
            (show 1 ≤ a.val + s ∧ a.val + s ≤ c.length by omega)
            (show 1 ≤ t.val ∧ t.val ≤ c.length by omega) hs
          omega
        · obtain ⟨s, hs, hsl⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
          rw [Walk.take_length, Nat.min_eq_left hb.le] at hsl
          rw [Walk.take_getVert, Nat.min_eq_right hsl] at hs
          have he := hc.getVert_injOn'
            (show s ≤ c.length - 1 by omega)
            (show t.val ≤ c.length - 1 by omega) hs
          omega
      simpa only [hplen] using four_contact_proper_arc_length c p hp hpsub huv
        hA hB hAB htnot hAa hBb hAt hBt
  obtain ⟨v, wc, hcyc, hclen⟩ := mem_cycleLengths hlength
  exact mem_oddCycleLengths_intro hcyc hclen (hodd.add_even ⟨2, rfl⟩)

/-! ## Independent sets outside the cycle -/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x T U : V}

/-- Two distinct exterior vertices each adjacent to an entire simple cycle
produce an actual simple cycle two edges longer. -/
theorem two_outside_full_spokes_long_cycle (c : G.Walk x x) (hc : c.IsCycle)
    (hT : T ∉ c.support) (hU : U ∉ c.support) (hTU : T ≠ U)
    (hTa : ∀ v ∈ c.support, G.Adj T v)
    (hUa : ∀ v ∈ c.support, G.Adj U v) :
    ∃ q : G.Walk c.tail.penultimate c.tail.penultimate,
      q.IsCycle ∧ q.length = c.length + 2 := by
  let p := cycleWithoutRoot c hc
  have hp : p.IsPath := cycleWithoutRoot_isPath c hc
  have hplen : p.length = c.length - 2 := cycleWithoutRoot_length c hc
  have hpsub : ∀ z ∈ p.support, z ∈ c.support := by
    intro z hz
    have hztail : z ∈ c.tail.support := by
      have hz' : z ∈ c.tail.dropLast.support := by
        have hzdef : p = cycleWithoutRoot c hc := rfl
        rw [hzdef, cycleWithoutRoot_eq] at hz
        exact hz
      rw [Walk.support_dropLast (cycleWithoutRoot_tail_notNil c hc)] at hz'
      have hlast := Walk.support_dropLast_concat
        (cycleWithoutRoot_tail_notNil c hc)
      have hz'' : z ∈ c.tail.dropLast.support ++ [x] := by
        rw [Walk.support_dropLast (cycleWithoutRoot_tail_notNil c hc)]
        exact List.mem_append.mpr (Or.inl hz')
      rw [hlast] at hz''
      exact hz''
    rw [← Walk.cons_support_tail hc.not_nil]
    exact List.mem_cons_of_mem _ hztail
  have hTnotp : T ∉ p.support := fun h => hT (hpsub _ h)
  have hUnotp : U ∉ p.support := fun h => hU (hpsub _ h)
  have hTx : T ≠ x := by
    intro h
    apply hT
    simpa only [h] using c.start_mem_support
  have hUx : U ≠ x := by
    intro h
    apply hU
    simpa only [h] using c.start_mem_support
  have hTxedge := hTa x c.start_mem_support
  have hxUedge := (hUa x c.start_mem_support).symm
  have hUsnd := hUa c.snd (hpsub _ p.start_mem_support)
  have hEndT := (hTa c.tail.penultimate (hpsub _ p.end_mem_support)).symm
  have hpU : (Walk.cons hUsnd p).IsPath := hp.cons hUnotp
  have hxnot : x ∉ (Walk.cons hUsnd p).support := by
    simp only [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hUx.symm, cycleWithoutRoot_root_notMem c hc⟩
  have hpxU : (Walk.cons hxUedge (Walk.cons hUsnd p)).IsPath := hpU.cons hxnot
  have hTnot : T ∉ (Walk.cons hxUedge (Walk.cons hUsnd p)).support := by
    simp only [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hTx, hTU, hTnotp⟩
  let q : G.Walk T c.tail.penultimate :=
    Walk.cons hTxedge (Walk.cons hxUedge (Walk.cons hUsnd p))
  have hq : q.IsPath := hpxU.cons hTnot
  have hqlen : q.length = p.length + 3 := by simp [q, Nat.add_assoc]
  have hn3 := hc.three_le_length
  refine ⟨Walk.cons hEndT q, ?_, ?_⟩
  · apply cycle_of_path_and_edge q hq hEndT
    rw [hqlen, hplen]
    omega
  · rw [Walk.length_cons, hqlen, hplen]
    omega

/-- Gyárfás's independent-exterior case: an actual longest odd cycle in a
finite graph of minimum degree at least `2*k+1`, with at most `k` distinct odd
cycle lengths and independent exterior, forces complete-graph containment. -/
theorem clique_of_independent_outside_longest_odd_cycle [Finite V] (k : ℕ)
    (hmin : ∀ v, 2 * k + 1 ≤ (G.neighborSet v).ncard)
    (hfin : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k)
    (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ m ∈ G.oddCycleLengths, m ≤ c.length)
    (hind : ∀ {u v}, u ∉ c.support → v ∉ c.support → ¬G.Adj u v) :
    (completeGraph (Fin (2 * k + 2))).IsContained G := by
  classical
  let := Fintype.ofFinite V
  have houtside : ∃ T : V, T ∉ c.support := by
    by_contra! hall
    have hdegree := odd_cycle_root_degree_le c hc hodd (fun u _ => hall u) hfin
    have hrootmin := hmin x
    omega
  obtain ⟨T, hT⟩ := houtside
  have hcover (v : V) (hv : v ∉ c.support) :
      ∀ u, G.Adj v u → u ∈ c.support := by
    intro u hadj
    by_contra hu
    exact hind hv hu hadj
  obtain ⟨hlen, hTa⟩ := outside_cycle_spoke_rigidity c hc hodd hT
    (hcover T hT) k (hmin T) hfin hk
  have hunique : ∀ U : V, U ∉ c.support → U = T := by
    intro U hU
    by_contra hUT
    obtain ⟨_, hUa⟩ := outside_cycle_spoke_rigidity c hc hodd hU
      (hcover U hU) k (hmin U) hfin hk
    obtain ⟨q, hq, hqlen⟩ := two_outside_full_spokes_long_cycle c hc hT hU
      (Ne.symm hUT) hTa hUa
    have hlong : c.length + 2 ∈ G.oddCycleLengths :=
      mem_oddCycleLengths_intro hq hqlen (hodd.add_even (by simp))
    have h := hmax _ hlong
    omega
  let p := c.dropLast
  have hp : p.IsPath := hc.isPath_dropLast
  have hplen : p.length + 1 = c.length := Walk.length_dropLast_add_one hc.not_nil
  have hpsub : ∀ u ∈ p.support, u ∈ c.support := by
    intro u hu
    rw [← Walk.support_dropLast_concat hc.not_nil]
    exact List.mem_append.mpr (Or.inl hu)
  have hsupport : ∀ u ∈ c.support, u ∈ p.support := by
    intro u hu
    rw [← Walk.support_dropLast_concat hc.not_nil] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hu
    · have hux : u = x := by simpa using hu
      simpa only [hux] using p.start_mem_support
  have hTnotp : T ∉ p.support.toFinset := by
    intro h
    exact hT (hpsub _ (List.mem_toFinset.mp h))
  have hall : (Finset.univ : Finset V) = insert T p.support.toFinset := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, List.mem_toFinset, true_iff]
    by_cases hu : u ∈ c.support
    · exact Or.inr (hsupport u hu)
    · exact Or.inl (hunique u hu)
  have hcyclecard : p.support.toFinset.card = c.length := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
    exact hplen
  have hcardV : Fintype.card V = 2 * k + 2 := by
    rw [← Finset.card_univ, hall, Finset.card_insert_of_notMem hTnotp, hcyclecard, hlen]
  have hdeg (v : V) : G.degree v = Fintype.card V - 1 := by
    have hcount : (G.neighborSet v).ncard = G.degree v :=
      (Set.fintypeCard_eq_ncard _).symm.trans (G.card_neighborSet_eq_degree v)
    have hlow := hmin v
    rw [hcount] at hlow
    have hup := G.degree_lt_card_verts v
    omega
  have htop : G = ⊤ := SimpleGraph.eq_top_iff_forall_isUniversal.mpr
    (fun v => (G.degree_eq_card_sub_one v).mp (hdeg v))
  have hemb : Nonempty (Fin (2 * k + 2) ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simp only [Fintype.card_fin, hcardV, le_refl])
  rw [htop]
  exact SimpleGraph.isContained_top_iff.mpr hemb

/-! ## One-contact attachments

Actual odd-cycle lengths forced by many supported paths through one cycle contact.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem cycle_without_root_pair {x : V} (c : G.Walk x x) (hc : c.IsCycle) :
    ∃ u, (u ∈ c.support ∧ u ≠ x) ∧
      ∃ v, (v ∈ c.support ∧ v ≠ x) ∧ u ≠ v := by
  have hl := hc.three_le_length
  have h₁ : c.getVert 1 ≠ x := by
    intro h
    have := (hc.getVert_endpoint_iff (by omega)).mp h
    omega
  have h₂ : c.getVert 2 ≠ x := by
    intro h
    have := (hc.getVert_endpoint_iff (by omega)).mp h
    omega
  refine ⟨c.getVert 1, ⟨c.getVert_mem_support _, h₁⟩,
    c.getVert 2, ⟨c.getVert_mem_support _, h₂⟩, ?_⟩
  intro h
  have := hc.getVert_injOn (by simp; omega) (by simp; omega) h
  omega

/-- Of two vertex-disjoint connectors, at least one avoids a prescribed vertex. -/
theorem connector_avoiding_vertex (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    (A B : Set V) (hAB : Disjoint A B)
    (hA : ∃ u ∈ A, ∃ v ∈ A, u ≠ v)
    (hB : ∃ u ∈ B, ∃ v ∈ B, u ≠ v) (x : V) :
    ∃ u ∈ A, ∃ v ∈ B, ∃ p : G.Walk u v, p.IsPath ∧ x ∉ p.support ∧
      (∀ z, z ∈ p.support → z ∈ A → z = u) ∧
      (∀ z, z ∈ p.support → z ∈ B → z = v) := by
  classical
  obtain ⟨u₁, hu₁, u₂, hu₂, v₁, hv₁, v₂, hv₂, _, _,
    p₁, p₂, hp₁, hp₂, hdis, hA₁, hB₁, hA₂, hB₂⟩ :=
    twoConnectors hG hdel A B hAB hA hB
  by_cases hx : x ∈ p₁.support
  · exact ⟨u₂, hu₂, v₂, hv₂, p₂, hp₂, fun h => hdis x hx h, hA₂, hB₂⟩
  · exact ⟨u₁, hu₁, v₁, hv₁, p₁, hp₁, hx, hA₁, hB₁⟩

/-- A supported set meeting an odd cycle only at `x` cannot supply k+1
same-parity simple x-to-v path lengths without forcing k+1 odd cycle lengths. -/
theorem one_contact_same_parity_paths_force_odd_lengths
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {x : V} (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (B : Set V) (_hxB : x ∈ B)
    (hmeet : ∀ z, z ∈ c.support → z ∈ B → z = x)
    (hBpair : ∃ u, (u ∈ B ∧ u ≠ x) ∧ ∃ v, (v ∈ B ∧ v ≠ x) ∧ u ≠ v)
    (k : ℕ) (hmany : ∀ v ∈ B, v ≠ x →
      ∃ ε < 2, k + 1 ≤ (parityPathLengthsWithin G B x v ε).ncard)
    (hfin : G.oddCycleLengths.Finite) : k + 1 ≤ G.oddCycleLengths.ncard := by
  classical
  let A : Set V := {z | z ∈ c.support ∧ z ≠ x}
  let D : Set V := {z | z ∈ B ∧ z ≠ x}
  have hAD : Disjoint A D := Set.disjoint_left.mpr (by
    intro z hzA hzD
    exact hzA.2 (hmeet z hzA.1 hzD.1))
  obtain ⟨u, hu, v, hv, p, hp, hxp, hA, hD⟩ :=
    connector_avoiding_vertex hG hdel A D hAD (cycle_without_root_pair c hc) hBpair x
  have hpC : ∀ z, z ∈ p.support → z ∈ c.support → z = u := by
    intro z hzp hzc
    have hzx : z ≠ x := fun h => hxp (h ▸ hzp)
    exact hA z hzp ⟨hzc, hzx⟩
  have hpB : ∀ z, z ∈ p.support → z ∈ B → z = v := by
    intro z hzp hzb
    have hzx : z ≠ x := fun h => hxp (h ▸ hzp)
    exact hD z hzp ⟨hzb, hzx⟩
  have huv : u ≠ v := by
    intro h
    exact hu.2 (hmeet u hu.1 (h.symm ▸ hv.1))
  have hppos := LongestOddCycle.walk_length_pos p huv
  obtain ⟨C₁, C₂, hC₁, hC₂, hCsub₁, hCsub₂, hCsum, hCpos₁, hCpos₂⟩ :=
    LongestOddCycle.two_arcs c hc c.start_mem_support hu.1 hu.2.symm
  obtain ⟨ε, hε, hcount⟩ := hmany v hv.1 hv.2
  have hchoice : ∃ C : G.Walk x u, C.IsPath ∧
      (∀ z, z ∈ C.support → z ∈ c.support) ∧ 0 < C.length ∧
      (C.length + p.length + ε) % 2 = 1 := by
    by_cases h₁ : (C₁.length + p.length + ε) % 2 = 1
    · exact ⟨C₁, hC₁, hCsub₁, hCpos₁, h₁⟩
    · refine ⟨C₂, hC₂, hCsub₂, hCpos₂, ?_⟩
      rw [Nat.odd_iff] at hodd
      omega
  obtain ⟨C, hC, hCsub, hCpos, hCpar⟩ := hchoice
  have hCp : (C.append p).IsPath := path_append_of_meet_only C p hC hp
    (fun z hzC hzp => hpC z hzp (hCsub z hzC))
  let P := parityPathLengthsWithin G B x v ε
  have hmap : Set.MapsTo (fun n : ℕ => C.length + p.length + n) P G.oddCycleLengths := by
    intro n hn
    have hpair := parityPathLengthsWithin_eq.mp hn
    have hpath : n ∈ pathLengthsWithin G B x v := hpair.1
    have hnpar : n % 2 = ε := hpair.2
    obtain ⟨q, hq, hlen, hqsub⟩ := mem_pathLengthsWithin_iff.mp hpath
    have hqpos := LongestOddCycle.walk_length_pos q hv.2.symm
    have hcross : ∀ z, z ∈ (C.append p).support → z ∈ q.support → z = x ∨ z = v := by
      intro z hzCp hzq
      rcases (Walk.mem_support_append_iff _ _).mp hzCp with hzC | hzp
      · exact Or.inl (hmeet z (hCsub z hzC) (hqsub z hzq))
      · exact Or.inr (hpB z hzp (hqsub z hzq))
    have hcycle := cycle_of_two_paths (C.append p) q hCp hq hcross (by
      simp only [Walk.length_append]
      omega)
    refine mem_oddCycleLengths_intro hcycle ?_ ?_
    · simp only [Walk.length_append, Walk.length_reverse]
      have hq : q.length = n := hlen
      omega
    · rw [Nat.odd_iff]
      change (C.length + p.length + n) % 2 = 1
      change n % 2 = ε at hnpar
      omega
  have hinj : Set.InjOn (fun n : ℕ => C.length + p.length + n) P := by
    intro n hn m hm hnm
    dsimp at hnm
    omega
  exact hcount.trans (Set.ncard_le_ncard_of_injOn _ hmap hinj hfin)

/-- The one-contact attachment consequence for an actual supported bipartite fan.
The supplied pair is outside the contact, allowing two disjoint connectors. -/
theorem one_contact_bipartite_fan_force_odd_lengths [Finite V]
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a b x r : V} (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (p : G.Walk a b) (hp : p.IsPath) (hr : r ∉ p.support)
    (hxB : x = r ∨ x ∈ p.support)
    (hmeet : ∀ z, z ∈ c.support → (z = r ∨ z ∈ p.support) → z = x)
    (hBpair : ∃ u, ((u = r ∨ u ∈ p.support) ∧ u ≠ x) ∧
      ∃ v, ((v = r ∨ v ∈ p.support) ∧ v ≠ x) ∧ u ≠ v)
    (h0 : G.Adj r a) (hL : G.Adj r b)
    (he : ∀ s ∈ pathNeighborPositions p r, Even s)
    {k : ℕ} (hk : 1 ≤ k) (hsize : 2 * k + 1 ≤ (pathNeighborPositions p r).card)
    (hfin : G.oddCycleLengths.Finite) : k + 1 ≤ G.oddCycleLengths.ncard := by
  apply one_contact_same_parity_paths_force_odd_lengths hG hdel c hc hodd
    {z | z = r ∨ z ∈ p.support} hxB hmeet hBpair k _ hfin
  intro v hv hvx
  exact bipartite_neighbor_fan_many_paths_within p hp hr h0 hL he hk hsize hvx.symm hxB hv

/-! ## Single-intersection configurations

The longest-odd-cycle comparison also holds when the two cycles share at most
one vertex. This covers an exterior fan closed through a single cycle contact.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace OneIntersection

theorem cycle_pair_avoiding {a x : V} (c : G.Walk a a) (hc : c.IsCycle)
    (hx : x ∈ c.support) :
    ∃ u ∈ ({z | z ∈ c.support ∧ z ≠ x} : Set V),
      ∃ v ∈ ({z | z ∈ c.support ∧ z ≠ x} : Set V), u ≠ v := by
  classical
  let r := c.rotate x hx
  have hr : r.IsCycle := hc.rotate hx
  have hthree := hr.three_le_length
  have h₁ : r.getVert 1 ≠ x := by
    intro h
    have heq := hr.getVert_injOn'
      (show 1 ≤ r.length - 1 by omega) (Nat.zero_le _)
      (by simpa only [Walk.getVert_zero] using h)
    omega
  have h₂ : r.getVert 2 ≠ x := by
    intro h
    have heq := hr.getVert_injOn'
      (show 2 ≤ r.length - 1 by omega) (Nat.zero_le _)
      (by simpa only [Walk.getVert_zero] using h)
    omega
  have hne : r.getVert 1 ≠ r.getVert 2 := by
    intro h
    have heq := hr.getVert_injOn'
      (show 1 ≤ r.length - 1 by omega) (show 2 ≤ r.length - 1 by omega) h
    omega
  exact ⟨r.getVert 1,
    ⟨(Walk.mem_support_rotate_iff c x hx).mp (r.getVert_mem_support 1), h₁⟩,
    r.getVert 2,
    ⟨(Walk.mem_support_rotate_iff c x hx).mp (r.getVert_mem_support 2), h₂⟩, hne⟩

/-- A connector avoiding the unique common vertex joins any one arc from
each cycle into an actual simple cycle. -/
theorem bridge_cycle_length {a b x u v : V} (c : G.Walk a a) (d : G.Walk b b)
    (hinter : ∀ z, z ∈ c.support → z ∈ d.support → z = x)
    (p : G.Walk u v) (hp : p.IsPath)
    (hC : ∀ z, z ∈ p.support → z ∈ c.support → z = u)
    (hD : ∀ z, z ∈ p.support → z ∈ d.support → z = v)
    (qC : G.Walk x u) (qD : G.Walk x v)
    (hqC : qC.IsPath) (hqD : qD.IsPath)
    (hCsub : ∀ z, z ∈ qC.support → z ∈ c.support)
    (hDsub : ∀ z, z ∈ qD.support → z ∈ d.support)
    (hlen : 3 ≤ p.length + qC.length + qD.length) :
    p.length + qC.length + qD.length ∈ G.cycleLengths := by
  let P := qC.append p
  have hP : P.IsPath := path_append_of_meet_only qC p hqC hp (by
    intro z hzC hzp
    exact hC z hzp (hCsub z hzC))
  have hmeet : ∀ z, z ∈ P.support → z ∈ qD.support → z = x ∨ z = v := by
    intro z hzP hzD
    rcases (Walk.mem_support_append_iff _ _).mp hzP with hzC | hzp
    · exact Or.inl (hinter z (hCsub z hzC) (hDsub z hzD))
    · exact Or.inr (hD z hzp (hDsub z hzD))
  have hPlen : P.length = qC.length + p.length := Walk.length_append qC p
  have hcycle := cycle_of_two_paths P qD hP hqD hmeet (by omega)
  refine mem_cycleLengths_intro hcycle ?_
  simp only [Walk.length_append, Walk.length_reverse, hPlen]
  omega

end OneIntersection

/-- An odd cycle sharing exactly a specified single vertex with a longest
odd cycle is strictly shorter. -/
theorem longest_odd_cycle_shared_vertex_shorter (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a b x : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (d : G.Walk b b) (hd : d.IsCycle) (hdodd : Odd d.length)
    (hxC : x ∈ c.support) (hxD : x ∈ d.support)
    (hinter : ∀ z, z ∈ c.support → z ∈ d.support → z = x) :
    d.length < c.length := by
  classical
  let A : Set V := {z | z ∈ c.support ∧ z ≠ x}
  let B : Set V := {z | z ∈ d.support ∧ z ≠ x}
  have hAB : Disjoint A B := Set.disjoint_left.mpr (by
    intro z hzC hzD
    exact hzC.2 (hinter z hzC.1 hzD.1))
  obtain ⟨u₁, hu₁, u₂, hu₂, v₁, hv₁, v₂, hv₂, huu, hvv,
    p₁, p₂, hp₁, hp₂, hpdisj, hA₁, hB₁, hA₂, hB₂⟩ :=
    twoConnectors hG hdel A B hAB
      (OneIntersection.cycle_pair_avoiding c hc hxC)
      (OneIntersection.cycle_pair_avoiding d hd hxD)
  have hchoose : ∃ u ∈ A, ∃ v ∈ B, ∃ p : G.Walk u v,
      p.IsPath ∧ x ∉ p.support ∧
      (∀ z, z ∈ p.support → z ∈ A → z = u) ∧
      (∀ z, z ∈ p.support → z ∈ B → z = v) := by
    by_cases hx₁ : x ∈ p₁.support
    · exact ⟨u₂, hu₂, v₂, hv₂, p₂, hp₂,
        (fun hx₂ => hpdisj x hx₁ hx₂), hA₂, hB₂⟩
    · exact ⟨u₁, hu₁, v₁, hv₁, p₁, hp₁, hx₁, hA₁, hB₁⟩
  obtain ⟨u, hu, v, hv, p, hp, hpx, hpA, hpB⟩ := hchoose
  have hpC : ∀ z, z ∈ p.support → z ∈ c.support → z = u := by
    intro z hzp hzC
    exact hpA z hzp ⟨hzC, fun heq => hpx (heq ▸ hzp)⟩
  have hpD : ∀ z, z ∈ p.support → z ∈ d.support → z = v := by
    intro z hzp hzD
    exact hpB z hzp ⟨hzD, fun heq => hpx (heq ▸ hzp)⟩
  have huv : u ≠ v := by
    intro heq
    exact hu.2 (hinter u hu.1 (heq.symm ▸ hv.1))
  have hppos := LongestOddCycle.walk_length_pos p huv
  obtain ⟨C₁, C₂, hC₁, hC₂, hCsub₁, hCsub₂, hCsum, hCpos₁, hCpos₂⟩ :=
    LongestOddCycle.two_arcs c hc hxC hu.1 hu.2.symm
  obtain ⟨D₁, D₂, hD₁, hD₂, hDsub₁, hDsub₂, hDsum, hDpos₁, hDpos₂⟩ :=
    LongestOddCycle.two_arcs d hd hxD hv.1 hv.2.symm
  have hm₁₁ : p.length + C₁.length + D₁.length ∈ G.cycleLengths :=
    OneIntersection.bridge_cycle_length c d hinter p hp hpC hpD
      C₁ D₁ hC₁ hD₁ hCsub₁ hDsub₁ (by omega)
  have hm₂₂ : p.length + C₂.length + D₂.length ∈ G.cycleLengths :=
    OneIntersection.bridge_cycle_length c d hinter p hp hpC hpD
      C₂ D₂ hC₂ hD₂ hCsub₂ hDsub₂ (by omega)
  have hm₁₂ : p.length + C₁.length + D₂.length ∈ G.cycleLengths :=
    OneIntersection.bridge_cycle_length c d hinter p hp hpC hpD
      C₁ D₂ hC₁ hD₂ hCsub₁ hDsub₂ (by omega)
  have hm₂₁ : p.length + C₂.length + D₁.length ∈ G.cycleLengths :=
    OneIntersection.bridge_cycle_length c d hinter p hp hpC hpD
      C₂ D₁ hC₂ hD₁ hCsub₂ hDsub₁ (by omega)
  by_contra! hge
  by_cases h₁₁ : Odd (p.length + C₁.length + D₁.length)
  · have h₂₂ : Odd (p.length + C₂.length + D₂.length) := by
      rw [Nat.odd_iff] at hodd hdodd h₁₁ ⊢
      omega
    have hcyc₁ := mem_cycleLengths hm₁₁
    have hcyc₂ := mem_cycleLengths hm₂₂
    obtain ⟨_, wc₁, hcyc₁, hlen₁⟩ := mem_cycleLengths hm₁₁
    obtain ⟨_, wc₂, hcyc₂, hlen₂⟩ := mem_cycleLengths hm₂₂
    have hbound₁ := hmax _ (mem_oddCycleLengths_intro hcyc₁ hlen₁ h₁₁)
    have hbound₂ := hmax _ (mem_oddCycleLengths_intro hcyc₂ hlen₂ h₂₂)
    omega
  · have h₁₂ : Odd (p.length + C₁.length + D₂.length) := by
      rw [Nat.odd_iff] at hodd hdodd h₁₁ ⊢
      omega
    have h₂₁ : Odd (p.length + C₂.length + D₁.length) := by
      rw [Nat.odd_iff] at hodd hdodd h₁₁ ⊢
      omega
    have hcyc₁ := mem_cycleLengths hm₁₂
    have hcyc₂ := mem_cycleLengths hm₂₁
    obtain ⟨_, wc₁, hcyc₁, hlen₁⟩ := mem_cycleLengths hm₁₂
    obtain ⟨_, wc₂, hcyc₂, hlen₂⟩ := mem_cycleLengths hm₂₁
    have hbound₁ := hmax _ (mem_oddCycleLengths_intro hcyc₁ hlen₁ h₁₂)
    have hbound₂ := hmax _ (mem_oddCycleLengths_intro hcyc₂ hlen₂ h₂₁)
    omega

/-- Any odd cycle meeting a longest odd cycle in at most one vertex is
strictly shorter. No finite-vertex assumption is needed. -/
theorem longest_odd_cycle_subsingleton_intersection_shorter (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a b : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (d : G.Walk b b) (hd : d.IsCycle) (hdodd : Odd d.length)
    (hinter : Set.Subsingleton {z | z ∈ c.support ∧ z ∈ d.support}) :
    d.length < c.length := by
  classical
  by_cases hex : ∃ x, x ∈ c.support ∧ x ∈ d.support
  · obtain ⟨x, hxC, hxD⟩ := hex
    exact longest_odd_cycle_shared_vertex_shorter hG hdel c hc hodd hmax d hd hdodd
      hxC hxD (fun z hzC hzD => hinter ⟨hzC, hzD⟩ ⟨hxC, hxD⟩)
  · exact longest_odd_cycle_disjoint_shorter hG hdel c hc hodd hmax d hd hdodd (by
      intro z hzC hzD
      exact hex ⟨z, hzC, hzD⟩)

end Erdos58
