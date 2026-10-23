module

public import Layer758

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

/-! ## Saturated contacts -/

/-! The saturated endpoint-contact configuration is excluded using actual
supported exterior paths and actual arc-plus-path simple cycles. -/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x A B : V}

theorem saturated_extra_endpoint_edge (S : G.Walk A B) (hs : 1 ≤ S.length)
    (hcard : (pathNeighborPositions S.tail A).card = 2) :
    ∃ i, 2 ≤ i ∧ i ≤ S.length ∧ G.Adj A (S.getVert i) := by
  have hnil : ¬S.Nil := by rw [Walk.not_nil_iff_lt_length]; omega
  have h0 : 0 ∈ pathNeighborPositions S.tail A := by
    rw [mem_pathNeighborPositions]
    exact ⟨Nat.zero_le _, by simpa only [Walk.getVert_zero] using S.adj_snd hnil⟩
  have herase := Finset.card_erase_add_one h0
  have hne : ((pathNeighborPositions S.tail A).erase 0).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ht0, htmem⟩ := Finset.mem_erase.mp ht
  obtain ⟨htL, hAt⟩ := (mem_pathNeighborPositions S.tail A t).mp htmem
  rw [Walk.length_tail] at htL
  refine ⟨t + 1, by omega, by omega, ?_⟩
  simpa only [Walk.getVert_tail] using hAt

theorem saturated_two_same_parity_offsets {s r : ℕ}
    (hs : 0 < s) (hr : 0 < r) (hsr : s ≠ r) :
    ∃ t ∈ ({2, s + 2, r + 2} : Finset ℕ),
      ∃ u ∈ ({2, s + 2, r + 2} : Finset ℕ), t ≠ u ∧ t % 2 = u % 2 := by
  by_cases hs0 : s % 2 = 0
  · exact ⟨2, by simp, s + 2, by simp, by omega, by omega⟩
  · by_cases hr0 : r % 2 = 0
    · exact ⟨2, by simp, r + 2, by simp, by omega, by omega⟩
    · exact ⟨s + 2, by simp, r + 2, by simp, by omega, by omega⟩

theorem saturated_realize_within (c : G.Walk x x) (S : G.Walk A B)
    (havoid : ∀ z ∈ S.support, z ∉ c.support) (R : Finset ℕ)
    (hpositive : ∀ r ∈ R, 1 ≤ r)
    (hw : (R : Set ℕ) ⊆ pathLengthsWithin G {z | z ∈ S.support} A B) :
    ∀ r ∈ R, ∃ q : G.Walk A B, q.IsPath ∧ q.length = r ∧
      1 ≤ q.length ∧ ∀ z ∈ q.support, z ∉ c.support := by
  intro r hr
  obtain ⟨q, hq, hlen, hsub⟩ := mem_pathLengthsWithin_iff.mp (hw hr)
  exact ⟨q, hq, hlen, by rw [hlen]; exact hpositive r hr,
    fun z hz ↦ havoid z (hsub z hz)⟩

theorem saturated_distance_cycle_memberships (c : G.Walk x x) (hc : c.IsCycle)
    [NeZero c.length] (hodd : Odd c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (X : Finset (ZMod c.length))
    (hcontacts : ∀ a ∈ X, G.Adj A (c.getVert a.val) ∧ G.Adj B (c.getVert a.val))
    (R : Finset ℕ)
    (hrealize : ∀ r ∈ R, ∃ q : G.Walk A B, q.IsPath ∧ q.length = r ∧
      1 ≤ q.length ∧ ∀ z ∈ q.support, z ∉ c.support)
    (hfin : G.oddCycleLengths.Finite) :
    ∀ d ∈ contactAllDistances X, ∀ t ∈ pathLengthOffsets R,
      Odd (d + t) → d + t ∈ hfin.toFinset := by
  have horacle := contact_cycle_oracles c hc hodd S hS hs havoid X hcontacts R hrealize
  intro d hd t ht hdt
  obtain ⟨a, ha, hda⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨b, hb, hdb⟩ := Finset.mem_image.mp hda
  apply hfin.mem_toFinset.mpr
  have hcycle := horacle a ha b (Finset.mem_erase.mp hb).2
    (Finset.mem_erase.mp hb).1.symm t ht (by simpa only [hdb] using hdt)
  simpa only [hdb] using hcycle

/-- The invariant contacts supply a third contact beyond a minimum odd
arc; its four contact edges realize the extra cycle of length d+4. -/
theorem saturated_minimum_four_contact (c : G.Walk x x) (hc : c.IsCycle)
    [NeZero c.length] (hodd : Odd c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (X : Finset (ZMod c.length))
    (hcontacts : ∀ a ∈ X, G.Adj A (c.getVert a.val) ∧ G.Adj B (c.getVert a.val))
    {d : ℕ} (hd : d ∈ contactAllDistances X) (hdodd : Odd d)
    (hminimum : ∀ e ∈ contactAllDistances X, d ≤ e)
    (hinvariant : ∀ a ∈ X, contactAnchorDistances X a = contactAllDistances X) :
    d + 4 ∈ G.oddCycleLengths := by
  have hAout : A ∉ c.support := havoid A S.start_mem_support
  have hBout : B ∉ c.support := havoid B S.end_mem_support
  have hAB : A ≠ B := by
    intro heq
    have hidx := hS.getVert_injOn (Nat.zero_le _)
      (by change S.length ≤ S.length; rfl)
      (S.getVert_zero.trans (heq.trans S.getVert_length.symm))
    omega
  obtain ⟨a, ha, hda⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨t, ht, hta, hdt⟩ := contact_odd_arc_has_outside_contact X hodd hd hdodd
    hminimum hinvariant ha hda hdodd
  obtain ⟨b, hb, hdb⟩ := Finset.mem_image.mp hda
  have hcycle := four_contact_cyclic_odd_length c hc hAout hBout hAB a b t
    (by simpa only [hdb] using hdodd) (by simpa only [hdb] using hdt)
    (hcontacts a ha).1 (hcontacts b (Finset.mem_erase.mp hb).2).2
    (hcontacts t ht).1 (hcontacts t ht).2
  simpa only [hdb] using hcycle

theorem saturated_common_cyclic_positions_card (c : G.Walk x x) (hc : c.IsCycle)
    (heq : cycleContactVertices c A = cycleContactVertices c B)
    {k : ℕ} (hsize : (cycleContactVertices c A).ncard = 2 * k - 1) :
    (exteriorCommonCyclicPositions c A B).card = 2 * k - 1 := by
  have hcommon : exteriorCommonVertices c A B = cycleContactVertices c A := by
    ext z
    constructor
    · rintro ⟨hz, ha, hb⟩
      exact ⟨ha, hz⟩
    · rintro ⟨ha, hz⟩
      have hb : G.Adj B z :=
        (heq ▸ (show z ∈ cycleContactVertices c A from ⟨ha, hz⟩)).1
      exact ⟨hz, ha, hb⟩
  rw [exteriorCommonCyclicPositions_card c hc, hcommon, hsize]

/-- The full saturated endpoint data are impossible. One endpoint's extra
edge already supplies a second actual exterior path length; the remaining
contact and longest-cycle hypotheses force too many odd cycle lengths. -/
theorem saturated_exterior_path_impossible [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (_hcoverA : ∀ u, G.Adj A u → u ∉ c.support → u ∈ S.support)
    (_hcoverB : ∀ u, G.Adj B u → u ∉ c.support → u ∈ S.support)
    (k : ℕ) (hk : 2 ≤ k) (hfin : G.oddCycleLengths.Finite)
    (hcard : G.oddCycleLengths.ncard ≤ k)
    (heq : cycleContactVertices c A = cycleContactVertices c B)
    (hcontactsCard : (cycleContactVertices c A).ncard = 2 * k - 1)
    (hdiagA : endpointExteriorDiagonals S = 1)
    (_hdiagB : endpointExteriorDiagonals S.reverse = 1) : False := by
  classical
  have hcL := hc.three_le_length
  let : NeZero c.length := ⟨by omega⟩
  have htailcard : (pathNeighborPositions S.tail A).card = 2 := by
    rw [show endpointExteriorDiagonals S = (pathNeighborPositions S.tail A).card - 1 from rfl] at hdiagA
    omega
  obtain ⟨i, hi2, hiL, hai⟩ := saturated_extra_endpoint_edge S hs htailcard
  let r := S.length - i + 1
  have hrpos : 0 < r := by omega
  have hrs : r < S.length := by omega
  have hsr : S.length ≠ r := by omega
  let R : Finset ℕ := {S.length, r}
  have hRcard : R.card = 2 := by
    exact Finset.card_pair hsr
  have hRpositive : ∀ h ∈ R, 1 ≤ h := by
    intro h hh
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl <;> omega
  have hRwithin : (R : Set ℕ) ⊆ pathLengthsWithin G {z | z ∈ S.support} A B := by
    intro h hh
    simp only [R, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact mem_pathLengthsWithin hS rfl (fun _ hz ↦ hz)
    · exact endpoint_chord_suffix_mem S hS (by omega) hiL hai
  have hrealize := saturated_realize_within c S havoid R hRpositive hRwithin
  let X := exteriorCommonCyclicPositions c A B
  let D := contactAllDistances X
  let O := hfin.toFinset
  have hOcard : O.card ≤ k := by
    rw [Set.ncard_eq_toFinset_card G.oddCycleLengths hfin] at hcard
    exact hcard
  have hXsize : X.card = 2 * k - 1 :=
    saturated_common_cyclic_positions_card c hc heq hcontactsCard
  have hcontacts : ∀ a ∈ X, G.Adj A (c.getVert a.val) ∧ G.Adj B (c.getVert a.val) := by
    intro a ha
    exact (mem_exteriorCommonCyclicPositions c A B a).mp ha
  have hcycles : ∀ e ∈ D, ∀ t ∈ pathLengthOffsets R,
      Odd (e + t) → e + t ∈ O :=
    saturated_distance_cycle_memberships c hc hodd S hS hs havoid X hcontacts R hrealize hfin
  have hT : pathLengthOffsets R = {2, S.length + 2, r + 2} := by
    ext t
    simp [show pathLengthOffsets R = insert 2 (R.image (fun h => h + 2)) from rfl, R]
  obtain ⟨t, ht, u, hu, htu, hparity⟩ :=
    saturated_two_same_parity_offsets (by omega : 0 < S.length) hrpos hsr
  have htT : t ∈ pathLengthOffsets R := by rw [hT]; exact ht
  have huT : u ∈ pathLengthOffsets R := by rw [hT]; exact hu
  have hinvariance := contact_distance_invariance X O hodd hk hXsize htu hparity hOcard (by
    intro e he q hq heqodd
    rcases Finset.mem_insert.mp hq with hqt | hq
    · rw [hqt] at heqodd ⊢
      exact hcycles e he t htT heqodd
    · have hqu : q = u := Finset.mem_singleton.mp hq
      subst q
      exact hcycles e he u huT heqodd)
  have hOddCard : (D.filter Odd).card = k - 1 := hinvariance.2.1
  have hEvenCard : (D.filter Even).card = k - 1 := hinvariance.2.2
  have hDodd : (D.filter Odd).Nonempty := Finset.card_pos.mp (by rw [hOddCard]; omega)
  obtain ⟨e, he⟩ := hDodd
  have hD : D.Nonempty := ⟨e, (Finset.mem_filter.mp he).1⟩
  obtain ⟨d, hd, hminimum, hdpos, _, hdodd, _, hevenlower⟩ :=
    contact_gap_structure X hodd hD hinvariance.1
  have hfour : d + 4 ∈ O := hfin.mem_toFinset.mpr
    (saturated_minimum_four_contact c hc hodd S hS hs havoid X hcontacts
      hd hdodd hminimum hinvariance.1)
  have hreflect : ∀ e ∈ D, c.length - e ∈ D :=
    fun e he ↦ contact_structure_reflect X he
  have hdiff : ∀ e ∈ D, ∀ f ∈ D, e < f → f - e ∈ D :=
    fun e he f hf hef ↦ contact_structure_diff X hinvariance.1 he hf hef
  have hcap : ∀ o ∈ O, o ≤ c.length :=
    fun o ho ↦ hmax o (hfin.mem_toFinset.mp ho)
  have hmany := contact_two_paths_lengths_card D R O hcL hodd hk hd hdpos hdodd
    hOddCard hEvenCard hevenlower hreflect hdiff hRpositive (by omega : 2 ≤ R.card)
    hfour hcap (fun e he t ht => hcycles e he t ht)
  omega

/-! ## Singleton contacts

A completed singleton-contact branch for a longest odd cycle.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An exterior covered path cannot have one endpoint's only cycle contact
also adjacent to its other endpoint in the minimum-degree obstruction. -/
theorem singleton_contact_path_impossible [Finite V]
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {x A B : V} (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hAx : G.Adj A x) (hBx : G.Adj B x)
    (hcontact : ∀ z ∈ c.support, G.Adj A z → z = x)
    (hcover : ∀ z, G.Adj A z → z ∉ c.support → z ∈ S.support)
    {k : ℕ} (hk : 1 ≤ k) (hdegree : 2 * k + 1 ≤ (G.neighborSet A).ncard)
    (hfin : G.oddCycleLengths.Finite) (hcount : G.oddCycleLengths.ncard ≤ k) : False := by
  exact singleton_contact_path_impossible_of_exterior_count hG hdel c hc hodd
    S hS hs havoid hAx hBx hcontact hcover hk hdegree hfin hcount
    (one_contact_exterior_oddCycleLengths_ncard_lt hG hdel c hc hodd hmax x hfin hcount)

/-- The same branch allows the unique contact to be any vertex of the
longest cycle; rotation changes neither its support nor its length. -/
theorem singleton_contact_path_impossible_at [Finite V]
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {z x A B : V} (c : G.Walk z z) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length) (hxC : x ∈ c.support)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ u ∈ S.support, u ∉ c.support)
    (hAx : G.Adj A x) (hBx : G.Adj B x)
    (hcontact : ∀ u ∈ c.support, G.Adj A u → u = x)
    (hcover : ∀ u, G.Adj A u → u ∉ c.support → u ∈ S.support)
    {k : ℕ} (hk : 1 ≤ k) (hdegree : 2 * k + 1 ≤ (G.neighborSet A).ncard)
    (hfin : G.oddCycleLengths.Finite) (hcount : G.oddCycleLengths.ncard ≤ k) : False := by
  classical
  let d := c.rotate x hxC
  have hd : d.IsCycle := hc.rotate hxC
  have hdodd : Odd d.length := by simpa only [d, Walk.length_rotate] using hodd
  have hdmax : ∀ n ∈ G.oddCycleLengths, n ≤ d.length := by
    simpa only [d, Walk.length_rotate] using hmax
  apply singleton_contact_path_impossible hG hdel d hd hdodd hdmax S hS hs
    _ hAx hBx _ _ hk hdegree hfin hcount
  · intro u hu hud
    exact havoid u hu ((Walk.mem_support_rotate_iff c x hxC).mp hud)
  · intro u hud hau
    exact hcontact u ((Walk.mem_support_rotate_iff c x hxC).mp hud) hau
  · intro u hau hud
    exact hcover u hau (fun huc => hud ((Walk.mem_support_rotate_iff c x hxC).mpr huc))

end Erdos58
