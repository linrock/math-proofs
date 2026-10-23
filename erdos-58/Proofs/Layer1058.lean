module

public import Layer958

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

/-! ## Structural cliques

Finite structural assembly for Erdős #58. The sole local premise below is
the explicit saturated-path contradiction. It is not a mathematical axiom;
the unconditional capstone instantiates the separately proved theorem.
-/

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A longest odd cycle realizes the maximum member of the finite set. -/
theorem exists_longest_odd_cycle (hfin : G.oddCycleLengths.Finite)
    (hne : G.oddCycleLengths.Nonempty) :
    ∃ x : V, ∃ c : G.Walk x x, c.IsCycle ∧ Odd c.length ∧
      ∀ n ∈ G.oddCycleLengths, n ≤ c.length := by
  classical
  let S := hfin.toFinset
  have hS : S.Nonempty := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n, hfin.mem_toFinset.mpr hn⟩
  let L := S.max' hS
  have hL : L ∈ G.oddCycleLengths := hfin.mem_toFinset.mp (S.max'_mem hS)
  obtain ⟨⟨x, c, hc, hlen⟩, hodd⟩ := hL
  refine ⟨x, c, hc, by simpa only [hlen] using hodd, ?_⟩
  intro n hn
  rw [hlen]
  exact S.le_max' n (hfin.mem_toFinset.mpr hn)

/-- A longest simple path has maximal endpoints covering all their neighbors. -/
theorem exists_longest_path [Finite V] [Nonempty V] :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧
      (∀ {u v : V} (q : G.Walk u v), q.IsPath → q.length ≤ p.length) ∧
      (∀ u, G.Adj a u → u ∈ p.support) ∧
      (∀ u, G.Adj b u → u ∈ p.support) := by
  classical
  let _ := Fintype.ofFinite V
  let S := (Finset.range (Fintype.card V)).filter
    (fun n ↦ ∃ u v : V, ∃ q : G.Walk u v, q.IsPath ∧ q.length = n)
  have hS : S.Nonempty := by
    obtain ⟨u⟩ := ‹Nonempty V›
    refine ⟨0, Finset.mem_filter.mpr ⟨?_, u, u, .nil, by simp, rfl⟩⟩
    exact Finset.mem_range.mpr Fintype.card_pos
  let L := S.max' hS
  obtain ⟨_, a, b, p, hp, hlen⟩ := Finset.mem_filter.mp (S.max'_mem hS)
  have hmax : ∀ {u v : V} (q : G.Walk u v), q.IsPath → q.length ≤ p.length := by
    intro u v q hq
    rw [hlen]
    exact S.le_max' _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hq.length_lt, u, v, q, hq, rfl⟩)
  refine ⟨a, b, p, hp, hmax, ?_, ?_⟩
  · intro u hu
    by_contra hnot
    have hpath : (Walk.cons hu.symm p).IsPath := hp.cons hnot
    have := hmax _ hpath
    simp only [Walk.length_cons] at this
    omega
  · intro u hu
    by_contra hnot
    have hpath := hp.concat hnot hu
    have := hmax _ hpath
    simp only [Walk.length_concat] at this
    omega

/-- The saturated-path configuration of the longest-cycle argument is
impossible. It is stated as a predicate so that the finite clique assembly can
be read on its own; `Erdos58.saturated_exterior_path_impossible` proves it from
actual cycle and path witnesses. -/
@[expose] public def SaturatedExteriorImpossible (G : SimpleGraph V) : Prop :=
  ∀ {x a b : V} (c : G.Walk x x), c.IsCycle → Odd c.length →
    (∀ n ∈ G.oddCycleLengths, n ≤ c.length) →
    ∀ (S : G.Walk a b), S.IsPath → 1 ≤ S.length →
      (∀ z ∈ S.support, z ∉ c.support) →
      (∀ u, G.Adj a u → u ∉ c.support → u ∈ S.support) →
      (∀ u, G.Adj b u → u ∉ c.support → u ∈ S.support) →
      ∀ (k : ℕ), 2 ≤ k → G.oddCycleLengths.Finite →
        G.oddCycleLengths.ncard ≤ k →
        cycleContactVertices c a = cycleContactVertices c b →
        (cycleContactVertices c a).ncard = 2 * k - 1 →
        endpointExteriorDiagonals S = 1 →
        endpointExteriorDiagonals S.reverse = 1 → False

/-- The complete finite clique conclusion follows from the single explicit
saturation premise. All longest-cycle/path and contact reductions are actual
proved graph constructions. Nonempty odd lengths excludes the bipartite case. -/
theorem finite_structural_clique_of_saturated_impossible [Finite V]
    (hsaturated : SaturatedExteriorImpossible G)
    (k : ℕ) (hk : 1 ≤ k) (hG : G.Connected)
    (hdel : ∀ v, (G.induce {w | w ≠ v}).Connected)
    (hmin : ∀ v, 2 * k + 1 ≤ (G.neighborSet v).ncard)
    (hfin : G.oddCycleLengths.Finite) (hcard : G.oddCycleLengths.ncard ≤ k)
    (hne : G.oddCycleLengths.Nonempty) :
    (completeGraph (Fin (2 * k + 2))).IsContained G := by
  classical
  obtain ⟨x, c, hc, hodd, hmax⟩ := exists_longest_odd_cycle hfin hne
  have hcontra {a b : V} (S : G.Walk a b) (hS : S.IsPath) (hs : 1 ≤ S.length)
      (havoid : ∀ z ∈ S.support, z ∉ c.support)
      (hcoverA : ∀ u, G.Adj a u → u ∉ c.support → u ∈ S.support)
      (hcoverB : ∀ u, G.Adj b u → u ∉ c.support → u ∈ S.support)
      (hA : (cycleContactVertices c a).Nonempty)
      (horder : (cycleContactVertices c a).ncard ≤ (cycleContactVertices c b).ncard) :
      False := by
    obtain ⟨heq, hcontacts, hdiagA, hdiagB, hk2⟩ :=
      exterior_path_endpoint_reduction hG hdel c hc hodd hmax S hS hs havoid
        hcoverA hcoverB hA horder k hk hfin hcard (hmin a) (hmin b)
    exact hsaturated c hc hodd hmax S hS hs havoid hcoverA hcoverB
      k hk2 hfin hcard heq hcontacts hdiagA hdiagB
  have hind : ∀ {u v}, u ∉ c.support → v ∉ c.support → ¬G.Adj u v := by
    intro u v hu hv huv
    let W : Set V := {z | z ∉ c.support}
    let H := G.induce W
    let : Nonempty W := ⟨⟨u, hu⟩⟩
    obtain ⟨a, b, p, hp, hpmax, hcoverA, hcoverB⟩ := exists_longest_path (G := H)
    have hedge : H.Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
    have hedgepath : (Walk.cons hedge Walk.nil).IsPath :=
      (Walk.cons_isPath_iff hedge Walk.nil).mpr
        ⟨by simp, by simpa using hedge.ne⟩
    have hpositive : 1 ≤ p.length := by
      have h := hpmax (Walk.cons hedge Walk.nil) hedgepath
      simpa only [Walk.length_cons, Walk.length_nil] using h
    let f := Copy.induce G W
    let S := p.map f.toHom
    have hS : S.IsPath := hp.map f.injective
    have hs : 1 ≤ S.length := by
      simpa only [S, Walk.length_map] using hpositive
    have havoid : ∀ z ∈ S.support, z ∉ c.support := by
      intro z hz hzc
      change z ∈ (p.map f.toHom).support at hz
      rw [Walk.support_map] at hz
      obtain ⟨w, hw, hwz⟩ := List.mem_map.mp hz
      change w.val = z at hwz
      exact w.property (hwz.symm ▸ hzc)
    have hcoverAG : ∀ z, G.Adj a.val z → z ∉ c.support → z ∈ S.support := by
      intro z haz hzC
      let w : W := ⟨z, hzC⟩
      have haz' : H.Adj a w := haz
      have hw : w ∈ p.support := hcoverA w haz'
      change z ∈ (p.map f.toHom).support
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    have hcoverBG : ∀ z, G.Adj b.val z → z ∉ c.support → z ∈ S.support := by
      intro z hbz hzC
      let w : W := ⟨z, hzC⟩
      have hbz' : H.Adj b w := hbz
      have hw : w ∈ p.support := hcoverB w hbz'
      change z ∈ (p.map f.toHom).support
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    obtain ⟨y, hyC, hay⟩ := longest_exterior_path_endpoint_contact
      hG hdel c hc hodd hmax hfin k hcard hmin p hp hcoverA
    have hA : (cycleContactVertices c a.val).Nonempty := ⟨y, hay, hyC⟩
    have hcoverBreverse : ∀ w, H.Adj b w → w ∈ p.reverse.support := by
      intro w hbw
      simpa only [Walk.support_reverse, List.mem_reverse] using hcoverB w hbw
    obtain ⟨z, hzC, hbz⟩ := longest_exterior_path_endpoint_contact
      hG hdel c hc hodd hmax hfin k hcard hmin p.reverse hp.reverse hcoverBreverse
    have hB : (cycleContactVertices c b.val).Nonempty := ⟨z, hbz, hzC⟩
    rcases le_total (cycleContactVertices c a.val).ncard
        (cycleContactVertices c b.val).ncard with horder | horder
    · exact hcontra S hS hs havoid hcoverAG hcoverBG hA horder
    · have havoid' : ∀ z ∈ S.reverse.support, z ∉ c.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using havoid
      have hcoverA' : ∀ z, G.Adj b.val z → z ∉ c.support → z ∈ S.reverse.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hcoverBG
      have hcoverB' : ∀ z, G.Adj a.val z → z ∉ c.support → z ∈ S.reverse.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hcoverAG
      exact hcontra S.reverse hS.reverse
        (by simpa only [Walk.length_reverse] using hs) havoid' hcoverA' hcoverB' hB horder
  exact clique_of_independent_outside_longest_odd_cycle k hmin hfin hcard c hc hodd hmax hind

end Erdos58
