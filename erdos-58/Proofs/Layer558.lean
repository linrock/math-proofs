module

public import Layer458
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Set.Card

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

/-! ## Cycle degrees -/

/-! Degree bound at the root of an actual odd simple cycle containing all
of its neighbors, using the exact path obtained by removing that root. -/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- An odd simple cycle that contains all neighbors of its root forces
the root degree to be at most twice the number of odd cycle lengths. -/
theorem odd_cycle_root_degree_le (c : G.Walk x x) (hc : c.IsCycle)
    (hodd : Odd c.length)
    (hcover : ∀ u, G.Adj x u → u ∈ c.support)
    (hfin : G.oddCycleLengths.Finite) :
    (G.neighborSet x).ncard ≤ 2 * G.oddCycleLengths.ncard := by
  by_contra hdegree
  have hdegree' : 2 * G.oddCycleLengths.ncard + 1 ≤ (G.neighborSet x).ncard := by
    omega
  have hpathodd : Odd (cycleWithoutRoot c hc).length := by
    rw [cycleWithoutRoot_length, Nat.odd_iff]
    rw [Nat.odd_iff] at hodd
    have := hc.three_le_length
    omega
  have hcount := odd_outer_fan_cycle_count (cycleWithoutRoot c hc)
    (cycleWithoutRoot_isPath c hc) (cycleWithoutRoot_root_notMem c hc)
    (cycleWithoutRoot_first_edge c hc) (cycleWithoutRoot_last_edge c hc)
    (cycleWithoutRoot_covers_neighbors c hc hcover) hpathodd
    G.oddCycleLengths.ncard hdegree' hfin
  omega

/-! ## Endpoint chord paths -/

/-! Actual endpoint-to-endpoint paths made from internal endpoint chords
of a simple path. Every witness remains inside the original path support. -/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b : V}

theorem pathBetween_start_notMem (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hi0 : 0 < i) (hj0 : 0 < j) :
    a ∉ (pathBetween p i j).support := by
  intro ha
  obtain ⟨t, htmin, htmax, hta⟩ := pathBetween_support_range p hi hj ha
  have htL : t ≤ p.length := htmax.trans (max_le hi hj)
  have heq : t = 0 := hp.getVert_injOn htL (Nat.zero_le _)
    (hta.trans p.getVert_zero.symm)
  have := lt_min hi0 hj0
  omega

theorem pathBetween_end_notMem (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi : i < p.length) (hj : j < p.length) :
    b ∉ (pathBetween p i j).support := by
  intro hb
  obtain ⟨t, htmin, htmax, htb⟩ := pathBetween_support_range p hi.le hj.le hb
  have htL : t ≤ p.length := htmax.trans (max_le hi.le hj.le)
  have heq : t = p.length := hp.getVert_injOn htL (by change p.length ≤ p.length; rfl)
    (htb.trans p.getVert_length.symm)
  have := max_lt hi hj
  omega

theorem pathBetween_length_dist (p : G.Walk a b) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    (pathBetween p i j).length = Nat.dist i j := by
  rw [pathBetween_length p hi hj]
  rcases le_total i j with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_le h, Nat.dist_eq_sub_of_le h]
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h, Nat.dist_eq_sub_of_le_right h]

/-- Open with the chord from the first endpoint, then follow the suffix. -/
theorem endpoint_chord_suffix_mem (p : G.Walk a b) (hp : p.IsPath)
    {i : ℕ} (hi0 : 0 < i) (hi : i ≤ p.length)
    (hai : G.Adj a (p.getVert i)) :
    p.length - i + 1 ∈ pathLengthsWithin G {z | z ∈ p.support} a b := by
  let q := (Walk.cons hai (pathBetween p i p.length)).copy rfl p.getVert_length
  refine mem_pathLengthsWithin (q := q) ?_ ?_ ?_
  · simpa only [q, Walk.isPath_copy] using
      (pathBetween_isPath p hp i p.length).cons
        (pathBetween_start_notMem p hp hi (le_refl _) hi0 (by omega))
  · simp only [q, Walk.length_copy, Walk.length_cons, pathBetween_length_dist p hi (le_refl _),
      Nat.dist_eq_sub_of_le hi]
  · intro z hz
    change z ∈ p.support
    simp only [q, Walk.support_copy, Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simpa only [Walk.getVert_zero] using p.getVert_mem_support 0
    · exact pathBetween_support_subset p hi (le_refl _) hz

/-- Follow the prefix, then close with the chord to the last endpoint. -/
theorem endpoint_chord_prefix_mem (p : G.Walk a b) (hp : p.IsPath)
    {j : ℕ} (hj : j < p.length) (hbj : G.Adj b (p.getVert j)) :
    j + 1 ∈ pathLengthsWithin G {z | z ∈ p.support} a b := by
  let q₀ := (pathBetween p 0 j).copy p.getVert_zero rfl
  have hq₀ : q₀.IsPath := by
    simpa only [q₀, Walk.isPath_copy] using pathBetween_isPath p hp 0 j
  have hb : b ∉ q₀.support := by
    simpa only [q₀, Walk.support_copy] using
      pathBetween_end_notMem p hp (by omega : 0 < p.length) hj
  refine mem_pathLengthsWithin (hq₀.concat hb hbj.symm) ?_ ?_
  · simp only [q₀, Walk.length_concat, Walk.length_copy,
      pathBetween_length_dist p (Nat.zero_le _) hj.le, Nat.dist_eq_sub_of_le (Nat.zero_le j),
      Nat.sub_zero]
  · intro z hz
    change z ∈ p.support
    simp only [q₀, Walk.support_concat, Walk.support_copy,
      List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact pathBetween_support_subset p (Nat.zero_le _) hj.le hz
    · simpa only [Walk.getVert_length] using p.getVert_mem_support p.length

/-- Use both endpoint chords and the internal segment between their contacts.
This also handles coincident contacts, producing a path of length two. -/
theorem endpoint_chord_double_mem (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi0 : 0 < i) (hj0 : 0 < j)
    (hi : i < p.length) (hj : j < p.length)
    (hai : G.Adj a (p.getVert i)) (hbj : G.Adj b (p.getVert j)) :
    Nat.dist i j + 2 ∈ pathLengthsWithin G {z | z ∈ p.support} a b := by
  have hab : a ≠ b := by
    intro heq
    have hidx := hp.getVert_injOn (Nat.zero_le _)
      (by change p.length ≤ p.length; rfl)
      (p.getVert_zero.trans (heq.trans p.getVert_length.symm))
    omega
  let q₀ := Walk.cons hai (pathBetween p i j)
  have hq₀ : q₀.IsPath :=
    (pathBetween_isPath p hp i j).cons
      (pathBetween_start_notMem p hp hi.le hj.le hi0 hj0)
  have hb : b ∉ q₀.support := by
    intro hb
    simp only [q₀, Walk.support_cons, List.mem_cons] at hb
    rcases hb with hba | hb
    · exact hab hba.symm
    · exact pathBetween_end_notMem p hp hi hj hb
  refine mem_pathLengthsWithin (hq₀.concat hb hbj.symm) ?_ ?_
  · simp only [q₀, Walk.length_concat, Walk.length_cons,
      pathBetween_length_dist p hi.le hj.le]
  · intro z hz
    change z ∈ p.support
    simp only [q₀, Walk.support_concat, Walk.support_cons,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with (rfl | hz) | rfl
    · simpa only [Walk.getVert_zero] using p.getVert_mem_support 0
    · exact pathBetween_support_subset p hi.le hj.le hz
    · simpa only [Walk.getVert_length] using p.getVert_mem_support p.length

def endpointChordPathLengths (s i j : ℕ) : Finset ℕ :=
  {s, s - i + 1, j + 1, Nat.dist i j + 2}

/-- All four numerical candidates are lengths of actual supported simple paths. -/
theorem endpoint_chord_four_paths (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi0 : 0 < i) (hj0 : 0 < j)
    (hi : i < p.length) (hj : j < p.length)
    (hai : G.Adj a (p.getVert i)) (hbj : G.Adj b (p.getVert j)) :
    (↑(endpointChordPathLengths p.length i j) : Set ℕ) ⊆
      pathLengthsWithin G {z | z ∈ p.support} a b := by
  intro n hn
  simp only [endpointChordPathLengths, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact mem_pathLengthsWithin hp rfl fun _ hz ↦ hz
  · exact endpoint_chord_suffix_mem p hp hi0 hi.le hai
  · exact endpoint_chord_prefix_mem p hp hj hbj
  · exact endpoint_chord_double_mem p hp hi0 hj0 hi hj hai hbj
/-- Restricting every path support to one fixed finite walk support also
restricts the possible simple-path lengths to a finite set. -/
theorem pathLengthsWithin_support_finite (p : G.Walk a b) (u v : V) :
    (pathLengthsWithin G {z | z ∈ p.support} u v).Finite := by
  classical
  refine (Set.finite_Iio p.support.toFinset.card).subset ?_
  rintro n hn
  obtain ⟨q, hq, hlen, hwithin⟩ := mem_pathLengthsWithin_iff.mp hn
  have hqsup : q.support.toFinset.card ≤ p.support.toFinset.card :=
    Finset.card_le_card (fun z hz =>
      List.mem_toFinset.mpr (hwithin z (List.mem_toFinset.mp hz)))
  rw [List.toFinset_card_of_nodup hq.support_nodup, Walk.length_support] at hqsup
  exact hlen ▸ Set.mem_Iio.mpr (by omega)
theorem endpoint_chord_crossing_lengths_eq {s i j : ℕ} (hi : i ≤ s) (hji : j ≤ i) :
    endpointChordPathLengths s i j = crossingPathLengths j (i - j) (s - i) := by
  ext n

  simp only [endpointChordPathLengths, crossingPathLengths_ext_iff,
    Finset.mem_insert, Finset.mem_singleton, Nat.dist_eq_sub_of_le_right hji]
  omega
/-- The positive crossing segments give exactly the four supported path
lengths required by the numerical classification. -/
theorem endpoint_chord_crossing_paths (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hj0 : 0 < j) (hji : j < i) (hi : i < p.length)
    (hai : G.Adj a (p.getVert i)) (hbj : G.Adj b (p.getVert j)) :
    (↑(crossingPathLengths j (i - j) (p.length - i)) : Set ℕ) ⊆
      pathLengthsWithin G {z | z ∈ p.support} a b := by
  rw [← endpoint_chord_crossing_lengths_eq hi.le hji.le]
  exact endpoint_chord_four_paths p hp (by omega) hj0 hi (by omega) hai hbj

/-- At most two actual supported path lengths force one of the two
exceptional crossing configurations. -/
theorem endpoint_chord_crossing_classification (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hj0 : 0 < j) (hji : j < i) (hi : i < p.length)
    (hai : G.Adj a (p.getVert i)) (hbj : G.Adj b (p.getVert j))
    (hcard : (pathLengthsWithin G {z | z ∈ p.support} a b).ncard ≤ 2) :
    j = p.length - i ∧ (j = i - j + 1 ∨ j = 1) := by
  have hbound := Set.ncard_le_ncard
    (endpoint_chord_crossing_paths p hp hj0 hji hi hai hbj)
    (pathLengthsWithin_support_finite p a b)
  rw [Set.ncard_coe_finset] at hbound
  exact crossing_path_lengths_classification hj0 (by omega) (by omega)
    (hbound.trans hcard)

theorem endpoint_chord_noncrossing_lengths_eq {s i j : ℕ}
    (hj : j ≤ s) (hij : i ≤ j) :
    endpointChordPathLengths s i j =
      {j - i + 2, j - i + (s - j) + 1, i + (j - i) + 1,
        i + (j - i) + (s - j)} := by
  ext n
  simp only [endpointChordPathLengths, Finset.mem_insert, Finset.mem_singleton,
    Nat.dist_eq_sub_of_le hij]
  omega

/-- Noncrossing genuine endpoint chords supply at least three actual
supported path lengths. The two skipped endpoint segments have length
at least two; the two internal contacts may coincide. -/
theorem endpoint_chord_noncrossing_three_paths (p : G.Walk a b) (hp : p.IsPath)
    {i j : ℕ} (hi : 2 ≤ i) (hj : j + 2 ≤ p.length) (hij : i ≤ j)
    (hai : G.Adj a (p.getVert i)) (hbj : G.Adj b (p.getVert j)) :
    3 ≤ (pathLengthsWithin G {z | z ∈ p.support} a b).ncard := by
  have hnumeric := noncrossing_path_lengths_card
    (a := i) (b := j - i) (c := p.length - j) hi (by omega)
  rw [← endpoint_chord_noncrossing_lengths_eq (by omega : j ≤ p.length) hij] at hnumeric
  have hbound := Set.ncard_le_ncard
    (endpoint_chord_four_paths p hp (by omega) (by omega) (by omega) (by omega) hai hbj)
    (pathLengthsWithin_support_finite p a b)
  rw [Set.ncard_coe_finset] at hbound
  exact hnumeric.trans hbound

/-! ## Endpoint fans -/

/-! Trim a covered endpoint neighborhood to a genuine fan, retaining all
neighbors; too few odd lengths then force every spoke position even. -/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b r : V}

theorem induce_neighbor_ncard_eq_of_all_neighbors {W : Set V} (r : W)
    (hcover : ∀ u, G.Adj r.val u → u ∈ W) :
    ((G.induce W).neighborSet r).ncard = (G.neighborSet r.val).ncard := by
  have himage : Subtype.val '' (G.induce W).neighborSet r = G.neighborSet r.val := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hu
      exact ⟨⟨u, hcover u hu⟩, hu, rfl⟩
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem pathNeighborPositions_induce_map {W : Set V} {a b : W}
    (p : (G.induce W).Walk a b) (r : W) :
    pathNeighborPositions (p.map (Copy.induce G W).toHom) r.val =
      pathNeighborPositions p r := by
  classical
  ext i
  simp only [mem_pathNeighborPositions, Walk.length_map, Walk.getVert_map]
  rfl

theorem trim_path_to_last_neighbor (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (h0 : G.Adj r a)
    (hcover : ∀ u, G.Adj r u → u ∈ p.support) :
    ∃ j ≤ p.length, (p.take j).IsPath ∧ r ∉ (p.take j).support ∧
      G.Adj r (p.getVert j) ∧
      ∀ u, G.Adj r u → u ∈ (p.take j).support := by
  classical
  let S := pathNeighborPositions p r
  have hS : S.Nonempty := by
    refine ⟨0, (mem_pathNeighborPositions p r 0).mpr ⟨by omega, ?_⟩⟩
    simpa using h0
  let j := S.max' hS
  have hjmem : j ∈ S := S.max'_mem hS
  have hj := (mem_pathNeighborPositions p r j).mp hjmem
  refine ⟨j, hj.1, hp.take j, ?_, hj.2, ?_⟩
  · intro h
    rw [Walk.support_take] at h
    exact hr (List.mem_of_mem_take h)
  · intro u hu
    obtain ⟨i, hiu, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hcover u hu)
    have himem : i ∈ S := (mem_pathNeighborPositions p r i).mpr ⟨hi, hiu ▸ hu⟩
    have hij : i ≤ j := S.le_max' i himem
    have hq : (p.take j).getVert i = u := by
      simpa only [Walk.take_getVert, Nat.min_eq_right hij] using hiu
    exact hq ▸ (p.take j).getVert_mem_support i

/-- A covered endpoint neighborhood of degree at least 2k+1 has a bipartite
fan when the ambient graph has fewer than k odd cycle lengths. All neighbors
and both fan endpoint edges are retained after trimming. -/
theorem low_odd_count_even_fan (p : G.Walk a b) (hp : p.IsPath)
    (hr : r ∉ p.support) (h0 : G.Adj r a)
    (hcover : ∀ u, G.Adj r u → u ∈ p.support)
    (k : ℕ) (hdegree : 2 * k + 1 ≤ (G.neighborSet r).ncard)
    (hfin : G.oddCycleLengths.Finite) (hcount : G.oddCycleLengths.ncard < k) :
    ∃ j ≤ p.length, (p.take j).IsPath ∧ r ∉ (p.take j).support ∧
      G.Adj r (p.getVert j) ∧
      (∀ u, G.Adj r u → u ∈ (p.take j).support) ∧
      (∀ s ∈ pathNeighborPositions (p.take j) r, Even s) ∧
      2 * k + 1 ≤ (pathNeighborPositions (p.take j) r).card := by
  classical
  obtain ⟨j, hj, hq, hrq, hlast, hqcover⟩ :=
    trim_path_to_last_neighbor p hp hr h0 hcover
  let q := p.take j
  let S := pathNeighborPositions q r
  have hsize : 2 * k + 1 ≤ S.card := by
    rw [pathNeighborPositions_card q hq hqcover]
    exact hdegree
  have he : (S.filter Even).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨?_, by simp⟩⟩
    rw [mem_pathNeighborPositions]
    simpa [q] using h0
  have heven : ∀ s ∈ S, Even s := by
    intro s hs
    by_contra hnot
    have ho : (S.filter Odd).Nonempty :=
      ⟨s, Finset.mem_filter.mpr ⟨hs, Nat.not_even_iff_odd.mp hnot⟩⟩
    have hbound := fan_odd_cycle_count q hq hrq S
      (fun i hi ↦ (mem_pathNeighborPositions q r i).mp hi) he ho k hsize hfin
    omega
  exact ⟨j, hj, hq, hrq, hlast, hqcover, heven, hsize⟩

/-! ## Exterior contacts

Actual cycles obtained by attaching an exterior simple path to a simple
cycle. All witnesses are built here; no cycle-membership oracle occurs in
the graph-theoretic statement boundaries.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x A B u v : V}

def exteriorContactPath (S : G.Walk A B) (hu : G.Adj A u) (hv : G.Adj B v) :
    G.Walk u v := (Walk.cons hu.symm S).concat hv

theorem exteriorContactPath_length (S : G.Walk A B)
    (hu : G.Adj A u) (hv : G.Adj B v) :
    (exteriorContactPath S hu hv).length = S.length + 2 := by
  simp [exteriorContactPath]

theorem exteriorContactPath_isPath (S : G.Walk A B) (hS : S.IsPath)
    (hu : G.Adj A u) (hv : G.Adj B v)
    (huS : u ∉ S.support) (hvS : v ∉ S.support) (hne : u ≠ v) :
    (exteriorContactPath S hu hv).IsPath := by
  have hp : (Walk.cons hu.symm S).IsPath := hS.cons huS
  apply hp.concat _ hv
  simp only [Walk.support_cons, List.mem_cons]
  rintro (hvu | hvS')
  · exact hne hvu.symm
  · exact hvS hvS'

theorem exteriorContactPath_support (S : G.Walk A B)
    (hu : G.Adj A u) (hv : G.Adj B v) {z : V}
    (hz : z ∈ (exteriorContactPath S hu hv).support) :
    z = u ∨ z ∈ S.support ∨ z = v := by
  simpa only [exteriorContactPath, Walk.support_concat, Walk.support_cons,
    List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false, or_assoc] using hz

/-- Attach an exterior path to any proper simple C-arc. The supports meet
only at its two contacts, so the resulting closed walk is an actual cycle. -/
theorem exterior_arc_cycle_witness (c : G.Walk x x) (S : G.Walk A B)
    (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support)
    (p : G.Walk u v) (hp : p.IsPath) (hpsub : p.support ⊆ c.support)
    (hu : G.Adj A u) (hv : G.Adj B v) (hne : u ≠ v) :
    ∃ q : G.Walk u u, q.IsCycle ∧ q.length = S.length + p.length + 2 := by
  have huS : u ∉ S.support := fun h => havoid u h (hpsub p.start_mem_support)
  have hvS : v ∉ S.support := fun h => havoid v h (hpsub p.end_mem_support)
  let P := exteriorContactPath S hu hv
  have hP : P.IsPath := exteriorContactPath_isPath S hS hu hv huS hvS hne
  have hlen : P.length = S.length + 2 := exteriorContactPath_length S hu hv
  refine ⟨P.append p.reverse, cycle_of_two_paths P p hP hp ?_ ?_, ?_⟩
  · intro z hzP hzp
    rcases exteriorContactPath_support S hu hv hzP with hzu | hzS | hzv
    · exact Or.inl hzu
    · exact (havoid z hzS (hpsub hzp)).elim
    · exact Or.inr hzv
  · omega
  · rw [two_paths_cycle_length, hlen]
    omega

/-- A common contact closes the exterior path with two different attachment
edges, giving the exact shared-contact cycle length. -/
theorem exterior_shared_contact_cycle_witness (S : G.Walk A B)
    (hS : S.IsPath) (hs : 1 ≤ S.length) (r : V) (hr : r ∉ S.support)
    (hAr : G.Adj A r) (hBr : G.Adj B r) :
    ∃ q : G.Walk B B, q.IsCycle ∧ q.length = S.length + 2 := by
  let p := Walk.cons hAr.symm S
  have hp : p.IsPath := hS.cons hr
  refine ⟨Walk.cons hBr p, cycle_of_path_and_edge p hp hBr ?_, ?_⟩
  · simp only [p, Walk.length_cons]
    omega
  · simp only [p, Walk.length_cons]

theorem exterior_shared_contact_odd_length (S : G.Walk A B)
    (hS : S.IsPath) (hs : 1 ≤ S.length) (r : V) (hr : r ∉ S.support)
    (hAr : G.Adj A r) (hBr : G.Adj B r) (hodd : Odd S.length) :
    S.length + 2 ∈ G.oddCycleLengths := by
  obtain ⟨q, hq, hl⟩ := exterior_shared_contact_cycle_witness S hS hs r hr hAr hBr
  exact mem_oddCycleLengths_intro hq hl (hodd.add_even (by simp))

private theorem exterior_arc_endpoints_ne (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 1 ≤ p.length) : u ≠ v := by
  intro huv
  have heq : p.getVert 0 = p.getVert p.length := by simpa using huv
  have hind := hp.getVert_injOn (Nat.zero_le p.length) (le_refl p.length) heq
  omega

/-- Both proper C arcs give genuine cycles with the same exterior bridge. -/
theorem exterior_cycle_arc_lengths (c : G.Walk x x) (hc : c.IsCycle)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support) {i j : ℕ}
    (hij : i < j) (hj : j < c.length)
    (hAi : G.Adj A (c.getVert i)) (hBj : G.Adj B (c.getVert j)) :
    S.length + (j - i) + 2 ∈ G.cycleLengths ∧
      S.length + (c.length - (j - i)) + 2 ∈ G.cycleLengths := by
  let p := pathInterval c i j hij.le
  have hp : p.IsPath := by
    exact pathInterval_isPath_cycle c hc i j hij.le hj
  have hpl : p.length = j - i := pathInterval_length c i j hij.le hj.le
  have hps : p.support ⊆ c.support := pathInterval_support_subset c i j hij.le
  have hne : c.getVert i ≠ c.getVert j := exterior_arc_endpoints_ne p hp (by omega)
  obtain ⟨q, hq, hql⟩ := exterior_arc_cycle_witness c S hS hs havoid p hp hps hAi hBj hne
  let p' := (cycleComplementArc c i j).reverse
  have hp' : p'.IsPath := (cycleComplementArc_isPath c hc hij hj).reverse
  have hpl' : p'.length = c.length - (j - i) := by
    rw [Walk.length_reverse, cycleComplementArc_length c (by omega) hj.le]
    omega
  have hps' : p'.support ⊆ c.support := by
    intro z hz
    apply cycleComplementArc_support_subset c i j
    simpa only [p', Walk.support_reverse, List.mem_reverse] using hz
  obtain ⟨q', hq', hql'⟩ := exterior_arc_cycle_witness c S hS hs havoid p' hp' hps' hAi hBj hne
  exact ⟨mem_cycleLengths_intro hq (by simpa only [hpl] using hql),
    mem_cycleLengths_intro hq' (by simpa only [hpl'] using hql')⟩

/-- The same two genuine cycles, with no ordering required on the contacts. -/
theorem exterior_cycle_distance_lengths (c : G.Walk x x) (hc : c.IsCycle)
    (S : G.Walk A B) (hS : S.IsPath) (hs : 1 ≤ S.length)
    (havoid : ∀ z ∈ S.support, z ∉ c.support) {i j : ℕ}
    (hi : i < c.length) (hj : j < c.length) (hne : i ≠ j)
    (hAi : G.Adj A (c.getVert i)) (hBj : G.Adj B (c.getVert j)) :
    S.length + Nat.dist i j + 2 ∈ G.cycleLengths ∧
      S.length + (c.length - Nat.dist i j) + 2 ∈ G.cycleLengths := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hd : Nat.dist i j = j - i := by simp only [Nat.dist]; omega
    simpa only [hd] using exterior_cycle_arc_lengths c hc S hS hs havoid hij hj hAi hBj
  · have havoid' : ∀ z ∈ S.reverse.support, z ∉ c.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using havoid
    have hd : Nat.dist i j = i - j := by simp only [Nat.dist]; omega
    simpa only [Walk.length_reverse, hd] using
      exterior_cycle_arc_lengths c hc S.reverse hS.reverse
        (by simpa only [Walk.length_reverse] using hs) havoid' hji hi hBj hAi

/-- Parity selects the odd member among the two complementary exterior
cycles. The entire cycle witness is supplied by the preceding construction. -/
theorem exterior_cycle_distance_odd_lengths (c : G.Walk x x) (hc : c.IsCycle)
    (hCodd : Odd c.length) (S : G.Walk A B) (hS : S.IsPath)
    (hs : 1 ≤ S.length) (havoid : ∀ z ∈ S.support, z ∉ c.support) {i j : ℕ}
    (hi : i < c.length) (hj : j < c.length) (hne : i ≠ j)
    (hAi : G.Adj A (c.getVert i)) (hBj : G.Adj B (c.getVert j)) :
    (Odd (S.length + Nat.dist i j) →
      S.length + Nat.dist i j + 2 ∈ G.oddCycleLengths) ∧
    (Even (S.length + Nat.dist i j) →
      S.length + (c.length - Nat.dist i j) + 2 ∈ G.oddCycleLengths) := by
  obtain ⟨hf, hb⟩ := exterior_cycle_distance_lengths c hc S hS hs havoid hi hj hne hAi hBj
  refine ⟨fun hodd => ?_, fun heven => ?_⟩
  · obtain ⟨_, q, hq, hlen⟩ := mem_cycleLengths hf
    refine mem_oddCycleLengths_intro hq (by rw [← hlen]) ?_
    exact hodd.add_even (by simp)
  · obtain ⟨_, q, hq, hlen⟩ := mem_cycleLengths hb
    refine mem_oddCycleLengths_intro hq (by rw [← hlen]) ?_
    have hdist : i.dist j < c.length := by simp only [Nat.dist]; omega
    simp only [Nat.odd_iff, Nat.even_iff] at hCodd heven ⊢
    have hdist_lt : i.dist j < c.length := hdist
    omega

/-- Actual indexed common C-contacts of the exterior endpoints. The closing
duplicate at index C.length is excluded. -/
noncomputable def exteriorCommonPositions (c : G.Walk x x) (A B : V) : Finset ℕ := by
  classical
  exact (Finset.range c.length).filter
    (fun i => G.Adj A (c.getVert i) ∧ G.Adj B (c.getVert i))

@[simp] theorem mem_exteriorCommonPositions (c : G.Walk x x) (A B : V) (i : ℕ) :
    i ∈ exteriorCommonPositions c A B ↔
      i < c.length ∧ G.Adj A (c.getVert i) ∧ G.Adj B (c.getVert i) := by
  classical
  simp [exteriorCommonPositions]

def exteriorCommonVertices (c : G.Walk x x) (A B : V) : Set V :=
  {z | z ∈ c.support ∧ G.Adj A z ∧ G.Adj B z}

theorem cycle_getVert_injective_below_length (c : G.Walk x x) (hc : c.IsCycle)
    {i j : ℕ} (hi : i < c.length) (hj : j < c.length)
    (heq : c.getVert i = c.getVert j) : i = j := by
  let p := c.take (c.length - 1)
  have hthree := hc.three_le_length
  have hp : p.IsPath := hc.isPath_take (by omega)
  have hpl : p.length = c.length - 1 := by
    simp only [p, Walk.take_length, Nat.min_eq_left (Nat.sub_le _ _)]
  have heq' : p.getVert i = p.getVert j := by
    simpa only [p, Walk.take_getVert,
      Nat.min_eq_right (show i ≤ c.length - 1 by omega),
      Nat.min_eq_right (show j ≤ c.length - 1 by omega)] using heq
  exact hp.getVert_injOn
    (show i ≤ p.length by rw [hpl]; omega)
    (show j ≤ p.length by rw [hpl]; omega) heq'

/-- Indexing a simple cycle counts each actual common contact exactly once. -/
theorem exteriorCommonPositions_card (c : G.Walk x x) (hc : c.IsCycle) (A B : V) :
    (exteriorCommonPositions c A B).card = (exteriorCommonVertices c A B).ncard := by
  have hBij : Set.BijOn c.getVert (exteriorCommonPositions c A B : Set ℕ)
      (exteriorCommonVertices c A B) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨_, hAi, hBi⟩ := (mem_exteriorCommonPositions c A B i).mp hi
      exact ⟨c.getVert_mem_support i, hAi, hBi⟩
    · intro i hi j hj heq
      exact cycle_getVert_injective_below_length c hc
        ((mem_exteriorCommonPositions c A B i).mp hi).1
        ((mem_exteriorCommonPositions c A B j).mp hj).1 heq
    · intro z hz
      obtain ⟨hzC, hAz, hBz⟩ := hz
      obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hzC
      by_cases hiLt : i < c.length
      · refine ⟨i, (mem_exteriorCommonPositions c A B i).mpr ⟨hiLt, ?_, ?_⟩, hiz⟩
        · simpa only [hiz] using hAz
        · simpa only [hiz] using hBz
      · have hiEq : i = c.length := by omega
        have hxz : x = z := by simpa only [hiEq, Walk.getVert_length] using hiz
        refine ⟨0, (mem_exteriorCommonPositions c A B 0).mpr
          ⟨by have := hc.three_le_length; omega, ?_, ?_⟩, ?_⟩
        · simpa only [Walk.getVert_zero, hxz] using hAz
        · simpa only [Walk.getVert_zero, hxz] using hBz
        · simpa only [Walk.getVert_zero] using hxz
  simpa using hBij.ncard_eq

/-- Rotating to any actual cycle vertex preserves the exact indexed number
of common contacts. -/
theorem exteriorCommonPositions_rotate_card [DecidableEq V]
    (c : G.Walk x x) (hc : c.IsCycle)
    (y : V) (hy : y ∈ c.support) (A B : V) :
    (exteriorCommonPositions (c.rotate y hy) A B).card =
      (exteriorCommonPositions c A B).card := by
  rw [exteriorCommonPositions_card _ (hc.rotate hy), exteriorCommonPositions_card c hc]
  have heq : exteriorCommonVertices (c.rotate y hy) A B = exteriorCommonVertices c A B := by
    ext z
    simp only [exteriorCommonVertices, Set.mem_ofPred_eq, Walk.mem_support_rotate_iff]
  rw [heq]

/-! ## Four-contact arcs -/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x A B : V}

/-- A vertex later on a simple cycle is absent from an earlier proper arc. -/
theorem cycle_getVert_notMem_take_of_lt (c : G.Walk x x) (hc : c.IsCycle)
    {j t : ℕ} (hjt : j < t) (ht : t < c.length) :
    c.getVert t ∉ (c.take j).support := by
  intro hmem
  obtain ⟨s, hs, hsl⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
  rw [Walk.take_length, Nat.min_eq_left (show j ≤ c.length by omega)] at hsl
  rw [Walk.take_getVert, Nat.min_eq_right hsl] at hs
  have heq := hc.getVert_injOn'
    (show s ≤ c.length - 1 by omega)
    (show t ≤ c.length - 1 by omega) hs
  omega

/-- Four exterior contact edges close the first `j` cycle edges into an
actual simple cycle of length `j+4`, with the other contact beyond that arc. -/
theorem four_contact_arc_cycle_length (c : G.Walk x x) (hc : c.IsCycle)
    (hA : A ∉ c.support) (hB : B ∉ c.support) (hAB : A ≠ B)
    {j t : ℕ} (hj : 0 < j) (hjt : j < t) (ht : t < c.length)
    (hAx : G.Adj A x) (hBj : G.Adj B (c.getVert j))
    (hAt : G.Adj A (c.getVert t)) (hBt : G.Adj B (c.getVert t)) :
    j + 4 ∈ G.cycleLengths := by
  have hjlen : j < c.length := by omega
  have hxt : x ≠ c.getVert t := by
    intro h
    have heq := hc.getVert_injOn'
      (show 0 ≤ c.length - 1 by omega)
      (show t ≤ c.length - 1 by omega)
      (by simpa only [Walk.getVert_zero] using h)
    omega
  have hxj : x ≠ c.getVert j := by
    intro h
    have heq := hc.getVert_injOn'
      (show 0 ≤ c.length - 1 by omega)
      (show j ≤ c.length - 1 by omega)
      (by simpa only [Walk.getVert_zero] using h)
    omega
  have hAj : A ≠ c.getVert j := by
    intro h
    apply hA
    simpa only [h] using c.getVert_mem_support j
  have hxB : x ≠ B := by
    intro h
    apply hB
    simpa only [← h] using c.start_mem_support
  have htnot := cycle_getVert_notMem_take_of_lt c hc hjt ht
  have htj : c.getVert t ≠ c.getVert j := by
    intro h
    apply htnot
    simpa only [h] using (c.take j).end_mem_support
  let w : G.Walk x (c.getVert j) :=
    Walk.cons hAx.symm (Walk.cons hAt
      (Walk.cons hBt.symm (Walk.cons hBj Walk.nil)))
  have hw : w.IsPath := by
    simp [w, Walk.isPath_def, hAx.ne.symm, hAt.ne, hAB, hAj,
      hBt.ne.symm, htj, hBj.ne, hxB, hxt, hxj]
  have hwlen : w.length = 4 := by simp [w]
  have hp : (c.take j).IsPath := hc.isPath_take hjlen
  have hplen : (c.take j).length = j := by
    rw [Walk.take_length, Nat.min_eq_left hjlen.le]
  have hpsub : ∀ z ∈ (c.take j).support, z ∈ c.support := by
    intro z hz
    rw [Walk.support_take] at hz
    exact List.mem_of_mem_take hz
  have hmeet : ∀ z, z ∈ (c.take j).support → z ∈ w.support →
      z = x ∨ z = c.getVert j := by
    intro z hzp hzw
    simp only [w, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hzw
    rcases hzw with hz | hz | hz | hz | hz
    · exact Or.inl hz
    · exact (hA (hz ▸ hpsub z hzp)).elim
    · exact (htnot (hz ▸ hzp)).elim
    · exact (hB (hz ▸ hpsub z hzp)).elim
    · exact Or.inr hz
  refine mem_cycleLengths_intro
    (cycle_of_two_paths (c.take j) w hp hw hmeet (by omega)) ?_
  rw [two_paths_cycle_length, hplen, hwlen]

/-- An odd first-arc length makes the four-contact cycle odd. -/
theorem four_contact_arc_odd_cycle_length (c : G.Walk x x) (hc : c.IsCycle)
    (hA : A ∉ c.support) (hB : B ∉ c.support) (hAB : A ≠ B)
    {j t : ℕ} (hj : 0 < j) (hjt : j < t) (ht : t < c.length)
    (hAx : G.Adj A x) (hBj : G.Adj B (c.getVert j))
    (hAt : G.Adj A (c.getVert t)) (hBt : G.Adj B (c.getVert t))
    (hodd : Odd j) : j + 4 ∈ G.oddCycleLengths := by
  obtain ⟨_, q, hq, hlen⟩ := mem_cycleLengths
    (four_contact_arc_cycle_length c hc hA hB hAB hj hjt ht hAx hBj hAt hBt)
  refine mem_oddCycleLengths_intro hq hlen (hodd.add_even ⟨2, rfl⟩)

/-! ## The longest odd cycle

Gyárfás's first structural lemma for Erdős #58: an odd cycle disjoint from a
longest odd cycle is strictly shorter. All joined cycles are actual simple walks.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace LongestOddCycle

theorem walk_length_pos {a b : V} (p : G.Walk a b) (hab : a ≠ b) : 0 < p.length := by
  by_contra! hlen
  have hz : p.length = 0 := by omega
  exact hab ((Walk.length_eq_zero_iff.mp hz).eq)

theorem cycle_distinct_pair {a : V} (c : G.Walk a a) (hc : c.IsCycle) :
    ∃ u ∈ c.support, ∃ v ∈ c.support, u ≠ v := by
  cases c with
  | nil => exact (hc.not_nil Walk.nil_nil).elim
  | @cons _ y _ h p =>
      exact ⟨a, by simp, y, List.mem_cons_of_mem a p.start_mem_support, h.ne⟩

/-- Rotating and splitting a simple cycle gives its two simple arcs between
any two distinct vertices, with lengths adding to the original cycle length. -/
theorem two_arcs {a u v : V} (c : G.Walk a a) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v) :
    ∃ q₁ q₂ : G.Walk u v, q₁.IsPath ∧ q₂.IsPath ∧
      (∀ z, z ∈ q₁.support → z ∈ c.support) ∧
      (∀ z, z ∈ q₂.support → z ∈ c.support) ∧
      q₁.length + q₂.length = c.length ∧ 0 < q₁.length ∧ 0 < q₂.length := by
  classical
  let r := c.rotate u hu
  have hr : r.IsCycle := hc.rotate hu
  have hvr : v ∈ r.support := (Walk.mem_support_rotate_iff c u hu).mpr hv
  let q₁ := r.takeUntil v hvr
  let q₂ := (r.dropUntil v hvr).reverse
  have hp₁ : q₁.IsPath := hr.isPath_takeUntil hvr
  have hsplit : ((r.takeUntil v hvr).append (r.dropUntil v hvr)).IsCycle := by
    simpa only [Walk.take_spec] using hr
  have hp₂ : q₂.IsPath := (hsplit.isPath_of_append_right (Walk.not_nil_of_ne huv)).reverse
  have hlen : q₁.length + q₂.length = c.length := by
    have h := congrArg Walk.length (Walk.take_spec r hvr)
    simpa only [q₁, q₂, Walk.length_append, Walk.length_reverse, r, Walk.length_rotate] using h
  refine ⟨q₁, q₂, hp₁, hp₂, ?_, ?_, hlen,
    walk_length_pos q₁ huv, walk_length_pos q₂ huv⟩
  · intro z hz
    exact (Walk.mem_support_rotate_iff c u hu).mp (r.support_takeUntil_subset_support hvr hz)
  · intro z hz
    have hzdrop : z ∈ (r.dropUntil v hvr).support := by
      simpa only [q₂, Walk.support_reverse, List.mem_reverse] using hz
    exact (Walk.mem_support_rotate_iff c u hu).mp (r.support_dropUntil_subset_support hvr hzdrop)

/-- Two disjoint connectors and one simple arc on each endpoint set produce an
actual simple cycle, provided the combined length is at least three. -/
theorem bridge_cycle_length {u₁ u₂ v₁ v₂ : V} (A B : Set V) (hAB : Disjoint A B)
    (p₁ : G.Walk u₁ v₁) (p₂ : G.Walk u₂ v₂)
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hdisj : ∀ z, z ∈ p₁.support → z ∈ p₂.support → False)
    (hA₁ : ∀ z, z ∈ p₁.support → z ∈ A → z = u₁)
    (hB₁ : ∀ z, z ∈ p₁.support → z ∈ B → z = v₁)
    (hA₂ : ∀ z, z ∈ p₂.support → z ∈ A → z = u₂)
    (hB₂ : ∀ z, z ∈ p₂.support → z ∈ B → z = v₂)
    (qC : G.Walk u₁ u₂) (qD : G.Walk v₁ v₂)
    (hqC : qC.IsPath) (hqD : qD.IsPath)
    (hC : ∀ z, z ∈ qC.support → z ∈ A)
    (hD : ∀ z, z ∈ qD.support → z ∈ B)
    (hlen : 3 ≤ (p₁.length + p₂.length) + qC.length + qD.length) :
    (p₁.length + p₂.length) + qC.length + qD.length ∈ G.cycleLengths := by
  have hpath : (p₁.append qD).IsPath := path_append_of_meet_only p₁ qD hp₁ hqD
    (fun z hz₁ hzD => hB₁ z hz₁ (hD z hzD))
  let Q := (p₁.append qD).append p₂.reverse
  have hQ : Q.IsPath := path_append_of_meet_only (p₁.append qD) p₂.reverse hpath hp₂.reverse (by
    intro z hzQ hz₂
    have hz₂' : z ∈ p₂.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hz₂
    rcases (Walk.mem_support_append_iff _ _).mp hzQ with hz₁ | hzD
    · exact (hdisj z hz₁ hz₂').elim
    · exact hB₂ z hz₂' (hD z hzD))
  have hmeet : ∀ z, z ∈ qC.support → z ∈ Q.support → z = u₁ ∨ z = u₂ := by
    intro z hzC hzQ
    have hzA := hC z hzC
    rcases (Walk.mem_support_append_iff _ _).mp hzQ with hzQ | hz₂
    · rcases (Walk.mem_support_append_iff _ _).mp hzQ with hz₁ | hzD
      · exact Or.inl (hA₁ z hz₁ hzA)
      · exact (Set.disjoint_left.mp hAB hzA (hD z hzD)).elim
    · have hz₂' : z ∈ p₂.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hz₂
      exact Or.inr (hA₂ z hz₂' hzA)
  have hQlen : Q.length = p₁.length + qD.length + p₂.length := by simp [Q]
  have hcycle := cycle_of_two_paths qC Q hqC hQ hmeet (by omega)
  refine mem_cycleLengths_intro hcycle ?_
  simp only [Walk.length_append, Walk.length_reverse, hQlen]
  omega

end LongestOddCycle

/-- An odd simple cycle disjoint from a longest odd simple cycle is shorter.
This is Gyárfás's first structural lemma, with actual walk and length witnesses. -/
theorem longest_odd_cycle_disjoint_shorter (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    {a b : V} (c : G.Walk a a) (hc : c.IsCycle) (hodd : Odd c.length)
    (hmax : ∀ n ∈ G.oddCycleLengths, n ≤ c.length)
    (d : G.Walk b b) (hd : d.IsCycle) (hdodd : Odd d.length)
    (hdisj : c.support.Disjoint d.support) : d.length < c.length := by
  classical
  let A : Set V := {z | z ∈ c.support}
  let B : Set V := {z | z ∈ d.support}
  have hAB : Disjoint A B := Set.disjoint_left.mpr (fun z hzC hzD => hdisj hzC hzD)
  obtain ⟨u₁, hu₁, u₂, hu₂, v₁, hv₁, v₂, hv₂, huu, hvv,
    p₁, p₂, hp₁, hp₂, hpdisj, hA₁, hB₁, hA₂, hB₂⟩ :=
    twoConnectors hG hdel A B hAB
      (LongestOddCycle.cycle_distinct_pair c hc)
      (LongestOddCycle.cycle_distinct_pair d hd)
  obtain ⟨C₁, C₂, hC₁, hC₂, hCsub₁, hCsub₂, hCsum, hCpos₁, hCpos₂⟩ :=
    LongestOddCycle.two_arcs c hc hu₁ hu₂ huu
  obtain ⟨D₁, D₂, hD₁, hD₂, hDsub₁, hDsub₂, hDsum, hDpos₁, hDpos₂⟩ :=
    LongestOddCycle.two_arcs d hd hv₁ hv₂ hvv
  have huv₁ : u₁ ≠ v₁ := by
    intro h
    exact Set.disjoint_left.mp hAB hu₁ (h.symm ▸ hv₁)
  have huv₂ : u₂ ≠ v₂ := by
    intro h
    exact Set.disjoint_left.mp hAB hu₂ (h.symm ▸ hv₂)
  have hp₁pos := LongestOddCycle.walk_length_pos p₁ huv₁
  have hp₂pos := LongestOddCycle.walk_length_pos p₂ huv₂
  let t := p₁.length + p₂.length
  have ht : 2 ≤ t := by omega
  have hm₁₁ : t + C₁.length + D₁.length ∈ G.cycleLengths :=
    LongestOddCycle.bridge_cycle_length A B hAB p₁ p₂ hp₁ hp₂ hpdisj
      hA₁ hB₁ hA₂ hB₂ C₁ D₁ hC₁ hD₁ hCsub₁ hDsub₁ (by omega)
  have hm₂₂ : t + C₂.length + D₂.length ∈ G.cycleLengths :=
    LongestOddCycle.bridge_cycle_length A B hAB p₁ p₂ hp₁ hp₂ hpdisj
      hA₁ hB₁ hA₂ hB₂ C₂ D₂ hC₂ hD₂ hCsub₂ hDsub₂ (by omega)
  have hm₁₂ : t + C₁.length + D₂.length ∈ G.cycleLengths :=
    LongestOddCycle.bridge_cycle_length A B hAB p₁ p₂ hp₁ hp₂ hpdisj
      hA₁ hB₁ hA₂ hB₂ C₁ D₂ hC₁ hD₂ hCsub₁ hDsub₂ (by omega)
  have hm₂₁ : t + C₂.length + D₁.length ∈ G.cycleLengths :=
    LongestOddCycle.bridge_cycle_length A B hAB p₁ p₂ hp₁ hp₂ hpdisj
      hA₁ hB₁ hA₂ hB₂ C₂ D₁ hC₂ hD₁ hCsub₂ hDsub₁ (by omega)
  by_contra! hge
  by_cases h₁₁ : Odd (t + C₁.length + D₁.length)
  · have h₂₂ : Odd (t + C₂.length + D₂.length) := by
      rw [Nat.odd_iff] at hodd hdodd h₁₁ ⊢
      omega
    obtain ⟨_, q₁₁, hq₁₁, hlen₁₁⟩ := mem_cycleLengths hm₁₁
    obtain ⟨_, q₂₂, hq₂₂, hlen₂₂⟩ := mem_cycleLengths hm₂₂
    have hparity₂₂ : Odd q₂₂.length := by rw [hlen₂₂]; exact h₂₂
    have hparity₁₁ : Odd q₁₁.length := by rw [hlen₁₁]; exact h₁₁
    have hbound₂ := hmax _ (mem_oddCycleLengths_intro hq₁₁ rfl hparity₁₁)
    have hbound₁ := hmax _ (mem_oddCycleLengths_intro hq₂₂ rfl hparity₂₂)
    omega
  · have h₁₂ : Odd (t + C₁.length + D₂.length) := by
      rw [Nat.odd_iff] at hodd hdodd h₁₁ ⊢
      omega
    have h₂₁ : Odd (t + C₂.length + D₁.length) := by
      rw [Nat.odd_iff] at hodd hdodd h₁₁ ⊢
      omega
    obtain ⟨_, q₁₂, hq₁₂, hlen₁₂⟩ := mem_cycleLengths hm₁₂
    obtain ⟨_, q₂₁, hq₂₁, hlen₂₁⟩ := mem_cycleLengths hm₂₁
    have hparity₂₁ : Odd q₂₁.length := by rw [hlen₂₁]; exact h₂₁
    have hparity₁₂ : Odd q₁₂.length := by rw [hlen₁₂]; exact h₁₂
    have hbound₂ := hmax _ (mem_oddCycleLengths_intro hq₁₂ rfl hparity₁₂)
    have hbound₁ := hmax _ (mem_oddCycleLengths_intro hq₂₁ rfl hparity₂₁)
    omega

/-! ## Neighborhood splitting

Exact neighborhood and contact counts for an actual simple cycle.
The exterior degree is measured in the induced graph, including its subtype.
-/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x : V}

/-- Actual neighbors of `v` lying on the cycle. -/
def cycleContactVertices (c : G.Walk x x) (v : V) : Set V :=
  G.neighborSet v ∩ {z | z ∈ c.support}

/-- Positions on the cycle adjacent to `v`, with the repeated terminal root
excluded. -/
noncomputable def cycleContactPositions (c : G.Walk x x) (v : V) : Finset ℕ := by
  classical
  exact (Finset.range c.length).filter (fun i => G.Adj v (c.getVert i))

@[simp] theorem mem_cycleContactPositions (c : G.Walk x x) (v : V) (i : ℕ) :
    i ∈ cycleContactPositions c v ↔ i < c.length ∧ G.Adj v (c.getVert i) := by
  classical
  simp [cycleContactPositions]

/-- The induced exterior neighbors correspond exactly to the ambient
neighbors lying outside the cycle. This needs no finiteness assumption. -/
theorem exterior_neighborSet_ncard_eq_sdiff (c : G.Walk x x)
    {v : V} (hv : v ∉ c.support) :
    ((G.induce {z | z ∉ c.support}).neighborSet ⟨v, hv⟩).ncard =
      (G.neighborSet v \ {z | z ∈ c.support}).ncard := by
  have hBij : Set.BijOn Subtype.val
      ((G.induce {z | z ∉ c.support}).neighborSet ⟨v, hv⟩)
      (G.neighborSet v \ {z | z ∈ c.support}) := by
    refine ⟨?_, Subtype.val_injective.injOn, ?_⟩
    · intro z hz
      exact ⟨hz, z.property⟩
    · intro z hz
      exact ⟨⟨z, hz.2⟩, hz.1, rfl⟩
  exact hBij.ncard_eq

/-- Ambient degree is the sum of the number of contacts on the cycle and
the degree in the exterior induced graph. -/
theorem neighborSet_ncard_cycle_split [Finite V] (c : G.Walk x x)
    {v : V} (hv : v ∉ c.support) :
    (G.neighborSet v).ncard = (cycleContactVertices c v).ncard +
      ((G.induce {z | z ∉ c.support}).neighborSet ⟨v, hv⟩).ncard := by
  rw [exterior_neighborSet_ncard_eq_sdiff c hv]
  exact (Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (G.neighborSet v) {z | z ∈ c.support}).symm

/-- The positions strictly before the repeated terminal root are injective.
This uses the actual simple path obtained by deleting the final cycle edge. -/
theorem cycle_getVert_injOn_below_length (c : G.Walk x x) (hc : c.IsCycle) :
    Set.InjOn c.getVert {i | i < c.length} := by
  intro i hi j hj heq
  change i < c.length at hi
  change j < c.length at hj
  apply hc.isPath_dropLast.getVert_injOn
    (show i ≤ c.dropLast.length by rw [Walk.length_dropLast]; omega)
    (show j ≤ c.dropLast.length by rw [Walk.length_dropLast]; omega)
  simpa only [Walk.getVert_dropLast hi, Walk.getVert_dropLast hj] using heq

/-- Counting the contact positions counts each actual contact once. -/
theorem cycleContactPositions_card (c : G.Walk x x) (hc : c.IsCycle) (v : V) :
    (cycleContactPositions c v).card = (cycleContactVertices c v).ncard := by
  have hBij : Set.BijOn c.getVert (cycleContactPositions c v : Set ℕ)
      (cycleContactVertices c v) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact ⟨((mem_cycleContactPositions c v i).mp hi).2, c.getVert_mem_support i⟩
    · intro i hi j hj heq
      exact cycle_getVert_injOn_below_length c hc
        ((mem_cycleContactPositions c v i).mp hi).1
        ((mem_cycleContactPositions c v j).mp hj).1 heq
    · intro z hz
      obtain ⟨hvz, hzC⟩ := hz
      change G.Adj v z at hvz
      obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hzC
      by_cases hiLt : i < c.length
      · refine ⟨i, (mem_cycleContactPositions c v i).mpr ⟨hiLt, ?_⟩, hiz⟩
        simpa only [hiz] using hvz
      · have hiEq : i = c.length := by omega
        have hxz : x = z := by simpa only [hiEq, Walk.getVert_length] using hiz
        refine ⟨0, (mem_cycleContactPositions c v 0).mpr
          ⟨by have := hc.three_le_length; omega, ?_⟩, ?_⟩
        · simpa only [Walk.getVert_zero, hxz] using hvz
        · simpa only [Walk.getVert_zero] using hxz
  simpa using hBij.ncard_eq

/-- Position zero is precisely the cycle root, so its contact status is the
actual root adjacency. -/
@[simp] theorem zero_mem_cycleContactPositions (c : G.Walk x x) (hc : c.IsCycle)
    (v : V) : 0 ∈ cycleContactPositions c v ↔ G.Adj v x := by
  rw [mem_cycleContactPositions]
  have hpos : 0 < c.length := by have := hc.three_le_length; omega
  simp only [hpos, true_and, Walk.getVert_zero]

/-! ## Spoke rigidity -/

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {x r : V}

/-- A vertex outside an odd cycle, with all its at least `2*k+1` neighbors on
that cycle, is adjacent to every cycle vertex and forces length `2*k+1`, when
the graph has at most `k` distinct odd cycle lengths. All cycle witnesses are
supplied by the two actual arcs, rather than by a numerical assumption. -/
theorem outside_cycle_spoke_rigidity (c : G.Walk x x) (hc : c.IsCycle)
    (hodd : Odd c.length) (hr : r ∉ c.support)
    (hcover : ∀ u, G.Adj r u → u ∈ c.support) (k : ℕ)
    (hdegree : 2 * k + 1 ≤ (G.neighborSet r).ncard)
    (hfin : G.oddCycleLengths.Finite) (hk : G.oddCycleLengths.ncard ≤ k) :
    c.length = 2 * k + 1 ∧ ∀ u ∈ c.support, G.Adj r u := by
  classical
  have : NeZero c.length := ⟨by
    have h := hc.three_le_length
    omega⟩
  let p := c.dropLast
  have hp : p.IsPath := hc.isPath_dropLast
  have hplen : p.length + 1 = c.length := Walk.length_dropLast_add_one hc.not_nil
  have hsupport : ∀ u ∈ c.support, u ∈ p.support := by
    intro u hu
    rw [← Walk.support_dropLast_concat hc.not_nil] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hu
    · have hux : u = x := by simpa using hu
      simpa only [hux] using p.start_mem_support
  have hcoverp : ∀ u, G.Adj r u → u ∈ p.support :=
    fun u hu => hsupport u (hcover u hu)
  let P := pathNeighborPositions p r
  have hPlt : ∀ i ∈ P, i < c.length := by
    intro i hi
    have := (mem_pathNeighborPositions p r i).mp hi |>.1
    omega
  let S := P.image (fun i : ℕ => (i : ZMod c.length))
  have hPi : Set.InjOn (fun i : ℕ => (i : ZMod c.length)) P := by
    intro i hi j hj heq
    have h := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt (hPlt i hi),
      ZMod.val_natCast_of_lt (hPlt j hj)] using h
  have hScard : S.card = (G.neighborSet r).ncard := by
    change (P.image (fun i : ℕ => (i : ZMod c.length))).card = _
    rw [Finset.card_image_of_injOn hPi]
    exact pathNeighborPositions_card p hp hcoverp
  have hSsize : 2 * k + 1 ≤ S.card := by omega
  have hSad (a : ZMod c.length) (ha : a ∈ S) : G.Adj r (c.getVert a.val) := by
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp ha
    have hilt := hPlt i hi
    have hadj := (mem_pathNeighborPositions p r i).mp hi |>.2
    rw [← heq, ZMod.val_natCast_of_lt hilt]
    simpa only [p, Walk.getVert_dropLast hilt] using hadj
  let L := hfin.toFinset
  have hLcard : L.card ≤ k := by
    change hfin.toFinset.card ≤ k
    rwa [← Set.ncard_eq_toFinset_card G.oddCycleLengths hfin]
  have hLm (m : ℕ) (hm : m ∈ G.oddCycleLengths) : m ∈ L :=
    hfin.mem_toFinset.mpr hm
  have hnL : c.length ∈ L := hLm _ (mem_oddCycleLengths_intro hc rfl hodd)
  have hforward : ∀ a ∈ S, ∀ b ∈ S, b ≠ a →
      Odd (b - a).val → (b - a).val + 2 ∈ L := by
    intro a ha b hb hba hod
    exact hLm _ ((outside_cycle_cyclic_odd_lengths c hc hodd hr a b hba
      (hSad a ha) (hSad b hb)).1 hod)
  have hbackward : ∀ a ∈ S, ∀ b ∈ S, b ≠ a →
      Even (b - a).val → c.length - (b - a).val + 2 ∈ L := by
    intro a ha b hb hba hed
    exact hLm _ ((outside_cycle_cyclic_odd_lengths c hc hodd hr a b hba
      (hSad a ha) (hSad b hb)).2 hed)
  obtain ⟨hfull, hlength⟩ :=
    odd_cyclic_fan_rigidity c.length k hodd S L hSsize hnL hLcard hforward hbackward
  refine ⟨hlength, ?_⟩
  intro u hu
  obtain ⟨i, hget, hile⟩ := Walk.mem_support_iff_exists_getVert.mp (hsupport u hu)
  have hilt : i < c.length := by omega
  have hiS : (i : ZMod c.length) ∈ S := by
    rw [hfull]
    exact Finset.mem_univ _
  have hadj := hSad (i : ZMod c.length) hiS
  rw [ZMod.val_natCast_of_lt hilt, ← Walk.getVert_dropLast hilt] at hadj
  change G.Adj r (p.getVert i) at hadj
  simpa only [hget] using hadj

/-! ## Interface equality -/

open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {x v : V}

theorem cycleContactVertices_eq (c : G.Walk x x) (v : V) :
    cycleContactVertices c v = G.neighborSet v ∩ {z | z ∈ c.support} := by
  simp [cycleContactVertices]

end Erdos58
