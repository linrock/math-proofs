module

public import Layer858

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

/-! ## Contact configurations in the case analysis -/

/-! The local endpoint argument reduces a positive longest exterior path
to the saturated two-diagonal, common-contact configuration. -/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x a b : V}

theorem cycleContactVertices_rotate [DecidableEq V] (c : G.Walk x x)
    (y : V) (hy : y ∈ c.support) (v : V) :
    cycleContactVertices (c.rotate y hy) v = cycleContactVertices c v := by
  ext z
  simp only [cycleContactVertices, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Walk.mem_support_rotate_iff]

theorem commonContacts_eq_left_of_equal_contacts (c : G.Walk x x)
    (heq : cycleContactVertices c a = cycleContactVertices c b) :
    exteriorCommonVertices c a b = cycleContactVertices c a := by
  ext z
  constructor
  · rintro ⟨hz, ha, hb⟩
    exact ⟨ha, hz⟩
  · rintro ⟨ha, hz⟩
    have hb : G.Adj b z := (heq ▸ (show z ∈ cycleContactVertices c a from ⟨ha, hz⟩)).1
    exact ⟨hz, ha, hb⟩

theorem selfContacts_eq_contacts (c : G.Walk x x) (v : V) :
    exteriorCommonVertices c v v = cycleContactVertices c v := by
  ext z
  simp only [exteriorCommonVertices, cycleContactVertices, Set.mem_inter_iff,
    Set.mem_ofPred_eq, and_self]
  tauto

/-- The endpoint contact sets coincide: orienting by the smaller contact
cardinality leaves a B-only contact whenever they differ, and that case is
excluded by the actual local count and the different-contact graph lemma. -/
theorem exterior_endpoint_contacts_equal [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (S : G.Walk a b) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hcover : ∀ u, G.Adj a u → u ∉ c.support → u ∈ S.support)
    (hA : (cycleContactVertices c a).Nonempty)
    (horder : (cycleContactVertices c a).ncard ≤ (cycleContactVertices c b).ncard)
    (k : ℕ) (hk : 1 ≤ k) (hfin : G.oddCycleLengths.Finite)
    (hcard : G.oddCycleLengths.ncard ≤ k)
    (hdegree : 2 * k + 1 ≤ (G.neighborSet a).ncard) :
    cycleContactVertices c a = cycleContactVertices c b := by
  classical
  by_contra hne
  have hnot : ¬cycleContactVertices c b ⊆ cycleContactVertices c a := by
    intro hsub
    exact hne (Set.eq_of_subset_of_ncard_le hsub horder).symm
  obtain ⟨y, hyB, hyA⟩ := Set.not_subset.mp hnot
  have hyC : y ∈ c.support := hyB.2
  have hby : G.Adj b y := hyB.1
  have hay : ¬G.Adj a y := fun h => hyA ⟨h, hyC⟩
  let d := c.rotate y hyC
  have hd : d.IsCycle := hc.rotate hyC
  have hdodd : Odd d.length := by simpa only [d, Walk.length_rotate] using hodd
  have hdmax : ∀ n ∈ G.oddCycleLengths, n ≤ d.length := by
    simpa only [d, Walk.length_rotate] using hmax
  have hdavoid : ∀ z ∈ S.support, z ∉ d.support := by
    intro z hz hzd
    exact havoid z hz ((Walk.mem_support_rotate_iff c y hyC).mp hzd)
  have hdcover : ∀ u, G.Adj a u → u ∉ d.support → u ∈ S.support := by
    intro u hu huD
    exact hcover u hu (fun huC => huD ((Walk.mem_support_rotate_iff c y hyC).mpr huC))
  have hdA : (cycleContactVertices d a).Nonempty := by
    simpa only [d, cycleContactVertices_rotate] using hA
  have h0 : 0 ∉ cycleContactPositions d a := by
    intro h
    exact hay ((zero_mem_cycleContactPositions d hd a).mp h)
  have hDne : ((cycleContactPositions d a).erase 0).Nonempty := by
    rw [Finset.erase_eq_of_notMem h0]
    apply Finset.card_pos.mp
    rw [cycleContactPositions_card d hd a]
    exact hdA.ncard_pos
  have hcases := exterior_endpoint_rotated_contact_cases d hd hdodd hdmax S hS hs
    hdavoid hdcover hby hfin hDne k hk hcard hdegree
  have hcountA := (hcases.2 hay).2
  have hcountA' : (cycleContactVertices c a).ncard = 2 * k := by
    simpa only [d, cycleContactVertices_rotate] using hcountA
  have hmany := exterior_different_contacts_many_odd_lengths c hc hodd S hS hs havoid
    k hk (by rw [selfContacts_eq_contacts, hcountA'])
    (by rw [selfContacts_eq_contacts]; omega) ⟨y, hyC, hby, hay⟩ hmax hfin
  omega

/-- Every positive covered exterior path is forced into the sole remaining
configuration: exactly 2k−1 common contacts, one extra exterior edge at
each endpoint, and k≥2. The case of one common contact is excluded by an
actual one-contact fan, rather than applying an empty counting family. -/
theorem exterior_path_endpoint_reduction [Finite V]
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (S : G.Walk a b) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hcoverA : ∀ u, G.Adj a u → u ∉ c.support → u ∈ S.support)
    (hcoverB : ∀ u, G.Adj b u → u ∉ c.support → u ∈ S.support)
    (hA : (cycleContactVertices c a).Nonempty)
    (horder : (cycleContactVertices c a).ncard ≤ (cycleContactVertices c b).ncard)
    (k : ℕ) (hk : 1 ≤ k) (hfin : G.oddCycleLengths.Finite)
    (hcard : G.oddCycleLengths.ncard ≤ k)
    (hdegreeA : 2 * k + 1 ≤ (G.neighborSet a).ncard)
    (hdegreeB : 2 * k + 1 ≤ (G.neighborSet b).ncard) :
    cycleContactVertices c a = cycleContactVertices c b ∧
      (cycleContactVertices c a).ncard = 2 * k - 1 ∧
      endpointExteriorDiagonals S = 1 ∧
      endpointExteriorDiagonals S.reverse = 1 ∧ 2 ≤ k := by
  classical
  have heq := exterior_endpoint_contacts_equal c hc hodd hmax S hS hs havoid hcoverA
    hA horder k hk hfin hcard hdegreeA
  obtain ⟨y, hay, hyC⟩ := hA
  have hby : G.Adj b y := (heq ▸ (show y ∈ cycleContactVertices c a from ⟨hay, hyC⟩)).1
  have hpa : 2 ≤ (cycleContactVertices c a).ncard := by
    by_contra! hsmall
    have hsub := (Set.ncard_le_one (s := cycleContactVertices c a)).mp (by omega)
    have hcontact : ∀ z ∈ c.support, G.Adj a z → z = y := by
      intro z hz haz
      exact hsub z ⟨haz, hz⟩ y ⟨hay, hyC⟩
    exact singleton_contact_path_impossible_at hG hdel c hc hodd hmax hyC S hS hs havoid
      hay hby hcontact hcoverA hk hdegreeA hfin hcard
  let d := c.rotate y hyC
  have hd : d.IsCycle := hc.rotate hyC
  have hdodd : Odd d.length := by simpa only [d, Walk.length_rotate] using hodd
  have hdmax : ∀ n ∈ G.oddCycleLengths, n ≤ d.length := by
    simpa only [d, Walk.length_rotate] using hmax
  have hdavoid : ∀ z ∈ S.support, z ∉ d.support := by
    intro z hz hzd
    exact havoid z hz ((Walk.mem_support_rotate_iff c y hyC).mp hzd)
  have hdcoverA : ∀ u, G.Adj a u → u ∉ d.support → u ∈ S.support := by
    intro u hu huD
    exact hcoverA u hu (fun huC => huD ((Walk.mem_support_rotate_iff c y hyC).mpr huC))
  have hdcoverB : ∀ u, G.Adj b u → u ∉ d.support → u ∈ S.reverse.support := by
    intro u hu huD
    simpa only [Walk.support_reverse, List.mem_reverse] using
      hcoverB u hu (fun huC => huD ((Walk.mem_support_rotate_iff c y hyC).mpr huC))
  have hdP : (cycleContactVertices d a).ncard = (cycleContactVertices c a).ncard := by
    simp only [d, cycleContactVertices_rotate]
  have hdPb : (cycleContactVertices d b).ncard = (cycleContactVertices c a).ncard := by
    simp only [d, cycleContactVertices_rotate, ← heq]
  have hDneA : ((cycleContactPositions d a).erase 0).Nonempty := by
    apply Finset.card_pos.mp
    have hcardpos := cycleContactPositions_card d hd a
    have he := Finset.card_erase_add_one ((zero_mem_cycleContactPositions d hd a).mpr hay)
    omega
  have hDneB : ((cycleContactPositions d b).erase 0).Nonempty := by
    apply Finset.card_pos.mp
    have hcardpos := cycleContactPositions_card d hd b
    have he := Finset.card_erase_add_one ((zero_mem_cycleContactPositions d hd b).mpr hby)
    omega
  have hcasesA := exterior_endpoint_rotated_contact_cases d hd hdodd hdmax S hS hs
    hdavoid hdcoverA hby hfin hDneA k hk hcard hdegreeA
  have hAone : endpointExteriorDiagonals S = 1 ∧
      (cycleContactVertices c a).ncard = 2 * k - 1 := by
    rcases hcasesA.1 with hzero | hone
    · have hcommon : 2 * k ≤ (exteriorCommonVertices c a b).ncard := by
        rw [commonContacts_eq_left_of_equal_contacts c heq]
        omega
      have hmany := exterior_common_contacts_many_odd_lengths c hc hodd S hS hs havoid
        k hk hcommon hfin
      omega
    · exact ⟨hone.1, by omega⟩
  have hdavoidB : ∀ z ∈ S.reverse.support, z ∉ d.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hdavoid
  have hcasesB := exterior_endpoint_rotated_contact_cases d hd hdodd hdmax S.reverse hS.reverse
    (by simpa only [Walk.length_reverse] using hs) hdavoidB hdcoverB hay hfin hDneB
    k hk hcard hdegreeB
  have hBone : endpointExteriorDiagonals S.reverse = 1 := by
    rcases hcasesB.1 with hzero | hone
    · omega
    · exact hone.1
  exact ⟨heq, hAone.2, hAone.1, hBone, by omega⟩

end Erdos58
