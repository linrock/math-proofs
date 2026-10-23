module

public import Layer658

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

/-! ## Endpoint contacts -/

/-! A longest exterior path has a contact with the longest odd cycle at
each endpoint. The no-contact alternative gives an exterior bipartite fan,
whose supported paths contradict the ambient odd-length bound. -/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem longest_exterior_path_endpoint_contact [Finite V]
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {x : V} (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (hfin : G.oddCycleLengths.Finite) (k : ℕ)
    (hcard : G.oddCycleLengths.ncard ≤ k)
    (hdegree : ∀ v, 2 * k + 1 ≤ (G.neighborSet v).ncard)
    {a b : {z // z ∉ c.support}}
    (p : (G.induce {z | z ∉ c.support}).Walk a b) (hp : p.IsPath)
    (hcover : ∀ u, (G.induce {z | z ∉ c.support}).Adj a u → u ∈ p.support) :
    ∃ u ∈ c.support, G.Adj a.val u := by
  classical
  let W : Set V := {z | z ∉ c.support}
  let H := G.induce W
  have hlow : H.oddCycleLengths.ncard < k :=
    exterior_oddCycleLengths_ncard_lt hG hdel c hc hodd hmax hfin hcard
  have hk : 1 ≤ k := by omega
  by_contra hnot
  have houtside : ∀ u, G.Adj a.val u → u ∈ W := by
    intro u hu huc
    exact hnot ⟨u, huc, hu⟩
  have hdeg : 2 * k + 1 ≤ (H.neighborSet a).ncard := by
    have heq : (H.neighborSet a).ncard = (G.neighborSet a.val).ncard :=
      induce_neighbor_ncard_eq_of_all_neighbors (G := G) (W := W) a houtside
    rw [heq]
    exact hdegree a.val
  have hnil : ¬p.Nil := by
    intro hnil
    have hz : (H.neighborSet a) = ∅ := by
      ext u
      constructor
      · intro hu
        have hup := hcover u hu
        have hua : u = a := by
          rw [Walk.nil_iff_support_eq.mp hnil] at hup
          simpa using hup
        subst u
        exact (hu.ne rfl).elim
      · simp
    rw [hz, Set.ncard_empty] at hdeg
    omega
  have hpt : p.tail.IsPath := hp.tail
  have hat : a ∉ p.tail.support := by
    rw [p.support_tail_of_not_nil hnil]
    exact path_start_notMem_tail p hp
  have htailcover : ∀ u, H.Adj a u → u ∈ p.tail.support := by
    intro u hu
    have hup := hcover u hu
    rw [← Walk.cons_support_tail hnil] at hup
    exact (List.mem_cons.mp hup).resolve_left hu.ne.symm
  have hHfin : H.oddCycleLengths.Finite :=
    (Copy.induce G W).oddCycleLengths_finite hfin
  obtain ⟨j, hj, hq, haq, hlast, hqcover, he, hsize⟩ :=
    low_odd_count_even_fan p.tail hpt hat (p.adj_snd hnil) htailcover k hdeg hHfin hlow
  let q := (p.tail.take j).map (Copy.induce G W).toHom
  have hqpath : q.IsPath := hq.map Subtype.val_injective
  have haqG : a.val ∉ q.support := by
    intro ha
    rw [Walk.support_map] at ha
    obtain ⟨u, hu, hua⟩ := List.mem_map.mp ha
    exact haq (Subtype.val_injective hua ▸ hu)
  have hdis : Disjoint {z | z ∈ c.support} {z | z = a.val ∨ z ∈ q.support} := by
    refine Set.disjoint_left.mpr ?_
    intro z hzc hz
    rcases hz with rfl | hz
    · exact a.property hzc
    · rw [Walk.support_map] at hz
      obtain ⟨u, hu, huz⟩ := List.mem_map.mp hz
      have huz' : u.val = z := huz
      have hzc' : z ∈ c.support := hzc
      apply u.property
      simpa only [huz'] using hzc'
  have heG : ∀ s ∈ pathNeighborPositions q a.val, Even s := by
    simpa only [q, pathNeighborPositions_induce_map] using he
  have hsizeG : 2 * k + 1 ≤ (pathNeighborPositions q a.val).card := by
    simpa only [q, pathNeighborPositions_induce_map] using hsize
  have hcontra := exterior_bipartite_fan_force_odd_lengths hG hdel c hc hodd
    q hqpath haqG hdis (p.adj_snd hnil) hlast heG hk hsizeG hfin
  omega

/-! ## Local counting at endpoints

Actual exterior neighborhoods and the local endpoint contact count.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x a b r : V}

theorem covered_exterior_neighbor_positions_card (c : G.Walk x x)
    (p : G.Walk a b) (hp : p.IsPath)
    (havoid : ∀ z ∈ p.support, z ∉ c.support)
    (hcover : ∀ u, G.Adj r u → u ∉ c.support → u ∈ p.support) :
    (pathNeighborPositions p r).card =
      (G.neighborSet r \ {z | z ∈ c.support}).ncard := by
  have hBij : Set.BijOn p.getVert (pathNeighborPositions p r : Set ℕ)
      (G.neighborSet r \ {z | z ∈ c.support}) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact ⟨((mem_pathNeighborPositions p r i).mp hi).2,
        havoid _ (p.getVert_mem_support i)⟩
    · intro i hi j hj heq
      exact hp.getVert_injOn ((mem_pathNeighborPositions p r i).mp hi).1
        ((mem_pathNeighborPositions p r j).mp hj).1 heq
    · intro u hu
      obtain ⟨i, hiu, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hcover u hu.1 hu.2)
      refine ⟨i, (mem_pathNeighborPositions p r i).mpr ⟨hi, ?_⟩, hiu⟩
      have hadj : G.Adj r u := hu.1
      simpa only [hiu] using hadj
  simpa using hBij.ncard_eq

noncomputable def endpointExteriorDiagonals (S : G.Walk a b) : ℕ :=
  (pathNeighborPositions S.tail a).card - 1

theorem exterior_endpoint_tail_data (c : G.Walk x x)
    (S : G.Walk a b) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hcover : ∀ u, G.Adj a u → u ∉ c.support → u ∈ S.support) :
    a ∉ S.tail.support ∧
      (∀ z ∈ S.tail.support, z ∉ c.support) ∧
      (∀ u, G.Adj a u → u ∉ c.support → u ∈ S.tail.support) ∧
      (pathNeighborPositions S.tail a).Nonempty ∧
      (G.neighborSet a \ {z | z ∈ c.support}).ncard = endpointExteriorDiagonals S + 1 := by
  have hnil : ¬S.Nil := by rw [Walk.not_nil_iff_lt_length]; omega
  have hat : a ∉ S.tail.support := by
    rw [S.support_tail_of_not_nil hnil]
    exact path_start_notMem_tail S hS
  have htailavoid : ∀ z ∈ S.tail.support, z ∉ c.support := by
    intro z hz
    apply havoid z
    rw [← Walk.cons_support_tail hnil]
    exact List.mem_cons_of_mem _ hz
  have htailcover : ∀ u, G.Adj a u → u ∉ c.support → u ∈ S.tail.support := by
    intro u hu huC
    have hup := hcover u hu huC
    rw [← Walk.cons_support_tail hnil] at hup
    exact (List.mem_cons.mp hup).resolve_left hu.ne.symm
  have hne : (pathNeighborPositions S.tail a).Nonempty := by
    refine ⟨0, (mem_pathNeighborPositions S.tail a 0).mpr ⟨by omega, ?_⟩⟩
    simpa only [Walk.getVert_zero] using S.adj_snd hnil
  have hcard := covered_exterior_neighbor_positions_card c S.tail hS.tail htailavoid htailcover
  refine ⟨hat, htailavoid, htailcover, hne, ?_⟩
  rw [← hcard]
  have hpos := Finset.card_pos.mpr hne
  dsimp [endpointExteriorDiagonals]
  omega

theorem exterior_endpoint_degree_split [Finite V] (c : G.Walk x x)
    (S : G.Walk a b) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hcover : ∀ u, G.Adj a u → u ∉ c.support → u ∈ S.support) :
    (G.neighborSet a).ncard = (cycleContactVertices c a).ncard +
      endpointExteriorDiagonals S + 1 := by
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (G.neighborSet a) {z | z ∈ c.support}
  have htail := exterior_endpoint_tail_data c S hS hs havoid hcover
  have hcvc : cycleContactVertices c a = G.neighborSet a ∩ {z | z ∈ c.support} := by
    exact cycleContactVertices_eq c a
  rw [← hcvc] at hsplit
  rw [htail.2.2.2.2] at hsplit
  omega

/-- Rotating to a B-contact gives the actual local count. The nonempty
deleted index family explicitly excludes the singleton-contact case. -/
theorem exterior_endpoint_rotated_local_count (c : G.Walk x x)
    (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (S : G.Walk a b) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hcover : ∀ u, G.Adj a u → u ∉ c.support → u ∈ S.support)
    (hBx : G.Adj b x) (hfin : G.oddCycleLengths.Finite)
    (hDne : ((cycleContactPositions c a).erase 0).Nonempty) :
    endpointExteriorDiagonals S +
      (((cycleContactPositions c a).erase 0).card + 1) / 2 ≤ G.oddCycleLengths.ncard := by
  have htail := exterior_endpoint_tail_data c S hS hs havoid hcover
  refine exterior_local_length_count c hc hodd hmax S.tail hS.tail htail.1
    (havoid a S.start_mem_support) htail.2.1 hBx hfin
    ((cycleContactPositions c a).erase 0) ?_ hDne (endpointExteriorDiagonals S) ?_
  · intro i hi
    have hie := Finset.mem_erase.mp hi
    have hip := (mem_cycleContactPositions c a i).mp hie.2
    exact ⟨by omega, hip⟩
  · have hpos := Finset.card_pos.mpr htail.2.2.2.1
    dsimp [endpointExteriorDiagonals]
    omega

/-- The graph-theoretic degree and local cycle constructions leave only
zero exterior diagonals, or one with exactly 2k−1 contacts. If the chosen
B-contact is absent at A, the sole possibility is zero and exactly 2k contacts. -/
theorem exterior_endpoint_rotated_contact_cases [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (S : G.Walk a b) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hcover : ∀ u, G.Adj a u → u ∉ c.support → u ∈ S.support)
    (hBx : G.Adj b x) (hfin : G.oddCycleLengths.Finite)
    (hDne : ((cycleContactPositions c a).erase 0).Nonempty)
    (k : ℕ) (hk : 1 ≤ k) (hcard : G.oddCycleLengths.ncard ≤ k)
    (hdegree : 2 * k + 1 ≤ (G.neighborSet a).ncard) :
    ((endpointExteriorDiagonals S = 0 ∧ 2 * k ≤ (cycleContactVertices c a).ncard) ∨
      (endpointExteriorDiagonals S = 1 ∧
        (cycleContactVertices c a).ncard = 2 * k - 1)) ∧
      (¬G.Adj a x → endpointExteriorDiagonals S = 0 ∧
        (cycleContactVertices c a).ncard = 2 * k) := by
  classical
  let P := cycleContactPositions c a
  let D := P.erase 0
  let q := endpointExteriorDiagonals S
  have hlocal := exterior_endpoint_rotated_local_count c hc hodd hmax S hS hs
    havoid hcover hBx hfin hDne
  change q + (D.card + 1) / 2 ≤ G.oddCycleLengths.ncard at hlocal
  have hsplit := exterior_endpoint_degree_split c S hS hs havoid hcover
  change (G.neighborSet a).ncard = (cycleContactVertices c a).ncard + q + 1 at hsplit
  have hPcard := cycleContactPositions_card c hc a
  change P.card = (cycleContactVertices c a).ncard at hPcard
  have hDcard : P.card ≤ D.card + 1 := by
    by_cases h0 : 0 ∈ P
    · have he : D.card + 1 = P.card := Finset.card_erase_add_one h0
      omega
    · change P.card ≤ (P.erase 0).card + 1
      rw [Finset.erase_eq_of_notMem h0]
      omega
  have hdegree' : 2 * k ≤ P.card + q := by omega
  have hfan : q + P.card / 2 ≤ k := by
    change q + (D.card + 1) / 2 ≤ G.oddCycleLengths.ncard at hlocal
    omega
  have hcases := endpoint_degree_contact_cases hk hdegree' hfan
  constructor
  · rcases hcases with hzero | hone
    · exact Or.inl ⟨hzero.1, by omega⟩
    · exact Or.inr ⟨hone.1, by omega⟩
  · intro hnot
    have h0 : 0 ∉ P := by
      intro h
      exact hnot ((zero_mem_cycleContactPositions c hc a).mp h)
    have hDP : D = P := Finset.erase_eq_of_notMem h0
    rw [hDP] at hlocal
    change q + (P.card + 1) / 2 ≤ G.oddCycleLengths.ncard at hlocal
    rcases hcases with hzero | hone
    · exact ⟨hzero.1, by omega⟩
    · exact (hone.2.2 (by omega)).elim

/-! ## One-contact exterior configurations

Keeping a single cycle contact in the exterior still excludes the longest
odd-cycle length. This is the exact count reduction needed for one-contact fans.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An odd cycle using only exterior vertices and one allowed contact meets
the longest cycle in at most that contact, so has a different odd length. -/
theorem one_contact_exterior_oddCycleLengths_subset (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length) (x : V) :
    (G.induce {z | z ∉ c.support ∨ z = x}).oddCycleLengths ⊆
      G.oddCycleLengths \ {c.length} := by
  intro n hn
  let f := Copy.induce G {z | z ∉ c.support ∨ z = x}
  have hnG := f.oddCycleLengths_subset hn
  refine ⟨hnG, ?_⟩
  intro hne
  have hnc : n = c.length := Set.mem_singleton_iff.mp hne
  obtain ⟨b, d, hd, hlen, hnodd⟩ := mem_oddCycleLengths_elim hn
  let q := d.map f.toHom
  have hq : q.IsCycle := hd.map f.injective
  have hqlen : q.length = n := (d.length_map f.toHom).trans hlen
  have hqodd : Odd q.length := by simpa only [hqlen] using hnodd
  have hmeet : ∀ z, z ∈ c.support → z ∈ q.support → z = x := by
    intro z hzc hzq
    change z ∈ (d.map f.toHom).support at hzq
    rw [Walk.support_map] at hzq
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp hzq
    change u.val = z at heq
    rcases u.property with huC | hux
    · exact (huC (heq.symm ▸ hzc)).elim
    · exact heq.symm.trans hux
  have hinter : Set.Subsingleton {z | z ∈ c.support ∧ z ∈ q.support} := by
    intro z hz w hw
    exact (hmeet z hz.1 hz.2).trans (hmeet w hw.1 hw.2).symm
  have hlt := longest_odd_cycle_subsingleton_intersection_shorter
    hG hdel c hc hodd hmax q hq hqodd hinter
  omega

/-- Even after retaining one contact, the odd-length count drops by at
least one. The vertex type may be infinite. -/
theorem one_contact_exterior_oddCycleLengths_ncard_add_one_le (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length) (x : V)
    (hfin : G.oddCycleLengths.Finite) :
    (G.induce {z | z ∉ c.support ∨ z = x}).oddCycleLengths.ncard + 1 ≤
      G.oddCycleLengths.ncard := by
  have hsub := one_contact_exterior_oddCycleLengths_subset hG hdel c hc hodd hmax x
  have houtfin : (G.induce {z | z ∉ c.support ∨ z = x}).oddCycleLengths.Finite :=
    hfin.subset (fun n hn => (hsub hn).1)
  have hcnot : c.length ∉
      (G.induce {z | z ∉ c.support ∨ z = x}).oddCycleLengths := by
    intro h
    exact (hsub h).2 (by simp)
  have hcmem : c.length ∈ G.oddCycleLengths :=
    mem_oddCycleLengths_intro hc rfl hodd
  have hins : insert c.length
      (G.induce {z | z ∉ c.support ∨ z = x}).oddCycleLengths ⊆
      G.oddCycleLengths := Set.insert_subset hcmem (fun n hn => (hsub hn).1)
  have hcard := Set.ncard_le_ncard hins hfin
  rwa [Set.ncard_insert_of_notMem hcnot houtfin] at hcard

/-- Any ambient bound `k` strictly exceeds the odd-length count in the
exterior with one retained contact. -/
theorem one_contact_exterior_oddCycleLengths_ncard_lt (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length) (x : V)
    (hfin : G.oddCycleLengths.Finite) {k : ℕ} (hcard : G.oddCycleLengths.ncard ≤ k) :
    (G.induce {z | z ∉ c.support ∨ z = x}).oddCycleLengths.ncard < k := by
  have h := one_contact_exterior_oddCycleLengths_ncard_add_one_le
    hG hdel c hc hodd hmax x hfin
  omega

/-! ## Singleton-contact fans

The singleton cycle-contact branch for a covered exterior path endpoint.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

set_option backward.isDefEq.respectTransparency.types false in
/-- A covered exterior path endpoint of degree at least 2k+1 cannot have
exactly one contact with a longest odd cycle when its other endpoint also
touches that contact. All fan and cycle witnesses are actual simple walks. -/
theorem singleton_contact_path_impossible_of_exterior_count [Finite V]
    (hG : G.Connected) (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {x A B : V} (c : G.Walk x x) (hc : c.IsCycle) (hodd : Odd c.length)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (hAx : G.Adj A x) (hBx : G.Adj B x)
    (hcontact : ∀ z ∈ c.support, G.Adj A z → z = x)
    (hcover : ∀ z, G.Adj A z → z ∉ c.support → z ∈ S.support)
    {k : ℕ} (hk : 1 ≤ k) (hdegree : 2 * k + 1 ≤ (G.neighborSet A).ncard)
    (hfin : G.oddCycleLengths.Finite) (hcount : G.oddCycleLengths.ncard ≤ k)
    (hcountH : (G.induce {z | z ∉ c.support ∨ z = x}).oddCycleLengths.ncard < k) : False := by
  classical
  cases S with
  | nil => simp only [Walk.length_nil] at hs; omega
  | @cons _ y _ hAy T =>
    have hT : T.IsPath := (Walk.cons_isPath_iff hAy T).mp hS |>.1
    have hAT : A ∉ T.support := (Walk.cons_isPath_iff hAy T).mp hS |>.2
    have hAout : A ∉ c.support := havoid A (by simp)
    have hTout : ∀ z ∈ T.support, z ∉ c.support := by
      intro z hz
      exact havoid z (List.mem_cons_of_mem _ hz)
    have hxT : x ∉ T.support := fun hx => hTout x hx c.start_mem_support
    let p := T.concat hBx
    have hp : p.IsPath := hT.concat hxT hBx
    have hr : A ∉ p.support := by
      simp only [p, Walk.support_concat, List.mem_append, List.mem_singleton]
      rintro (h | h)
      · exact hAT h
      · exact hAout (h.symm ▸ c.start_mem_support)
    let W : Set V := {z | z ∉ c.support ∨ z = x}
    have hpW : ∀ z ∈ p.support, z ∈ W := by
      intro z hz
      rcases (show z ∈ T.support ∨ z = x by simpa only [p, Walk.support_concat,
        List.mem_append, List.mem_singleton] using hz) with hzT | hzx
      · exact Or.inl (hTout z hzT)
      · exact Or.inr hzx
    let r : W := ⟨A, Or.inl hAout⟩
    let q := p.induce W hpW
    let f : G.induce W →g G := ⟨Subtype.val, fun h => h⟩
    have hm : q.map f = p := Walk.map_induce p hpW
    have hq : q.IsPath := Walk.IsPath.of_map (by rw [hm]; exact hp)
    have hqr : r ∉ q.support := by
      intro h
      apply hr
      rw [← hm, Walk.support_map]
      exact List.mem_map.mpr ⟨r, h, rfl⟩
    have hq0 : (G.induce W).Adj r (q.getVert 0) := by
      change G.Adj A (q.getVert 0).val
      simpa only [Walk.getVert_zero, q, p] using hAy
    have hfullW : ∀ z, G.Adj A z → z ∈ W := by
      intro z hz
      by_cases hzc : z ∈ c.support
      · exact Or.inr (hcontact z hzc hz)
      · exact Or.inl hzc
    have hqcover : ∀ z : W, (G.induce W).Adj r z → z ∈ q.support := by
      intro z hz
      have hzG : G.Adj A z.val := hz
      have hzp : z.val ∈ p.support := by
        by_cases hzc : z.val ∈ c.support
        · have hzx := hcontact z.val hzc hz
          simpa only [hzx] using p.end_mem_support
        · have hzS := hcover z.val hz hzc
          have hzA : z.val ≠ A := hzG.ne.symm
          have hzT : z.val ∈ T.support := by
            simpa only [Walk.support_cons, List.mem_cons, or_iff_right hzA] using hzS
          simp only [p, Walk.support_concat, List.mem_append]
          exact Or.inl hzT
      simpa only [q, Walk.support_induce] using (List.mem_attachWith hpW z).mpr hzp
    have hdegH : 2 * k + 1 ≤ ((G.induce W).neighborSet r).ncard := by
      rw [induce_neighbor_ncard_eq_of_all_neighbors r hfullW]
      exact hdegree
    have hfinH : (G.induce W).oddCycleLengths.Finite :=
      hfin.subset (Copy.induce G W).oddCycleLengths_subset
    obtain ⟨j, hj, hQ, hrQ, hlast, hQcover, he, hsize⟩ :=
      low_odd_count_even_fan q hq hqr (by simpa only [Walk.getVert_zero] using hq0)
        hqcover k hdegH hfinH hcountH
    let Q := (q.take j).map f
    have hQG : Q.IsPath := hQ.map Subtype.val_injective
    have hrG : A ∉ Q.support := by
      intro h
      rw [Walk.support_map] at h
      obtain ⟨z, hz, hzA⟩ := List.mem_map.mp h
      have hzr : z = r := Subtype.ext hzA
      exact hrQ (hzr ▸ hz)
    have hQW : ∀ z ∈ Q.support, z ∈ W := by
      intro z hz
      rw [Walk.support_map] at hz
      obtain ⟨w, hw, hwz⟩ := List.mem_map.mp hz
      exact hwz ▸ w.property
    have hmeet : ∀ z, z ∈ c.support → (z = A ∨ z ∈ Q.support) → z = x := by
      intro z hzC hz
      rcases hz with rfl | hz
      · exact (hAout hzC).elim
      · exact (hQW z hz).resolve_left (not_not.mpr hzC)
    have hxQ : x ∈ Q.support := by
      let xx : W := ⟨x, Or.inr rfl⟩
      have hxx : xx ∈ (q.take j).support := hQcover xx hAx
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨xx, hxx, rfl⟩
    have hpair : ∃ u, ((u = A ∨ u ∈ Q.support) ∧ u ≠ x) ∧
        ∃ v, ((v = A ∨ v ∈ Q.support) ∧ v ≠ x) ∧ u ≠ v := by
      refine ⟨A, ⟨Or.inl rfl, ?_⟩, y, ⟨Or.inr Q.start_mem_support, ?_⟩, hAy.ne⟩
      · intro h
        exact hAout (h.symm ▸ c.start_mem_support)
      · intro h
        exact hTout y T.start_mem_support (h.symm ▸ c.start_mem_support)
    have hposEq : pathNeighborPositions Q A = pathNeighborPositions (q.take j) r :=
      pathNeighborPositions_induce_map (q.take j) r
    have heG : ∀ s ∈ pathNeighborPositions Q A, Even s := by
      rwa [hposEq]
    have hsizeG : 2 * k + 1 ≤ (pathNeighborPositions Q A).card := by rwa [hposEq]
    have hbound := one_contact_bipartite_fan_force_odd_lengths hG hdel c hc hodd
      Q hQG hrG (Or.inr hxQ) hmeet hpair hAy hlast heG hk hsizeG hfin
    omega

end Erdos58
