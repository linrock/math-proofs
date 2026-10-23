module

public import Layer158
public import OddCycleExtraction108

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

namespace Erdos58

/-- A finite graph whose edges have unequal natural levels is greedily colorable
when each vertex has at most `k` neighbors at smaller levels. -/
public theorem colorable_of_earlier_neighbors {V : Type*} [Finite V]
    (G : SimpleGraph V) (d : V → ℕ) (k : ℕ)
    (hne : ∀ {u v}, G.Adj u v → d u ≠ d v)
    (hbound : ∀ v, {u | G.Adj u v ∧ d u < d v}.ncard ≤ k) :
    G.Colorable (k + 1) := by
  classical
  have choose_color (c : V → Fin (k + 1)) (v : V) :
      ∃ a : Fin (k + 1), ∀ u, G.Adj u v → d u < d v → c u ≠ a := by
    let s : Set V := {u | G.Adj u v ∧ d u < d v}
    have hcard : (c '' s).ncard ≤ k :=
      (Set.ncard_image_le (s := s) (f := c)).trans (hbound v)
    have hex : ∃ a : Fin (k + 1), a ∉ c '' s := by
      by_contra! hall
      have heq : c '' s = Set.univ := Set.eq_univ_iff_forall.mpr hall
      rw [heq] at hcard
      simp only [Set.ncard_univ, Nat.card_fin] at hcard
      omega
    obtain ⟨a, ha⟩ := hex
    refine ⟨a, fun u huv hlt heq => ha ?_⟩
    exact ⟨u, ⟨huv, hlt⟩, heq⟩
  have partial_color : ∀ n : ℕ, ∃ c : V → Fin (k + 1),
      ∀ {u v}, G.Adj u v → d u < n → d v < n → c u ≠ c v := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun _ => 0, fun _ h => by omega⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      let a : V → Fin (k + 1) := fun v => (choose_color c v).choose
      have ha : ∀ v u, G.Adj u v → d u < d v → c u ≠ a v :=
        fun v => (choose_color c v).choose_spec
      refine ⟨fun v => if d v = n then a v else c v, ?_⟩
      intro u v huv hu hv
      by_cases hun : d u = n
      · have hvn : d v ≠ n := fun hvn => hne huv (hun.trans hvn.symm)
        have hlt : d v < d u := by omega
        simpa only [ite_eq_left hun, ite_eq_right hvn] using (ha u v huv.symm hlt).symm
      · by_cases hvn : d v = n
        · have hlt : d u < d v := by omega
          simpa only [ite_eq_right hun, ite_eq_left hvn] using ha v u huv hlt
        · have hu' : d u < n := by omega
          have hv' : d v < n := by omega
          simpa only [ite_eq_right hun, ite_eq_right hvn] using hc huv hu' hv'
  obtain ⟨N, hN⟩ := Set.finite_range d |>.bddAbove
  obtain ⟨c, hc⟩ := partial_color (N + 1)
  exact ⟨SimpleGraph.Coloring.mk c fun huv =>
    hc huv (Nat.lt_succ_of_le (hN ⟨_, rfl⟩)) (Nat.lt_succ_of_le (hN ⟨_, rfl⟩))⟩

/-- Two palettes separate depth parity, and greedy coloring needs `k + 1`
colors inside each palette. -/
public theorem colorable_of_earlier_same_parity_neighbors {V : Type*} [Finite V]
    (G : SimpleGraph V) (d : V → ℕ) (k : ℕ)
    (hne : ∀ {u v}, G.Adj u v → d u ≠ d v)
    (hbound : ∀ v,
      {u | G.Adj u v ∧ d u < d v ∧ d u % 2 = d v % 2}.ncard ≤ k) :
    G.Colorable (2 * k + 2) := by
  classical
  let H : SimpleGraph V := {
    Adj := fun u v => G.Adj u v ∧ d u % 2 = d v % 2
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hH : ∀ v, {u | H.Adj u v ∧ d u < d v}.ncard ≤ k := by
    intro v
    have heq : {u | H.Adj u v ∧ d u < d v} =
        {u | G.Adj u v ∧ d u < d v ∧ d u % 2 = d v % 2} := by
      ext u
      simp only [Set.mem_ofPred_eq, H]
      tauto
    rw [heq]
    exact hbound v
  obtain ⟨c⟩ := colorable_of_earlier_neighbors H d k (fun h => hne h.1) hH
  let p : V → Fin 2 := fun v => ⟨d v % 2, Nat.mod_lt _ (by omega)⟩
  let C : G.Coloring (Fin 2 × Fin (k + 1)) :=
    SimpleGraph.Coloring.mk (fun v => (p v, c v)) (by
      intro u v huv heq
      have hp : d u % 2 = d v % 2 := congrArg Fin.val (congrArg Prod.fst heq)
      exact c.valid ⟨huv, hp⟩ (congrArg Prod.snd heq))
  have hc := C.colorable
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_add, Nat.mul_one] using hc

/-! ## The zero-count case

The exact zero-odd-cycle-length case of Erdős #58, for arbitrary vertex
types. The odd-cycle extraction is the separately hash-gated and replayed
local #108 auxiliary theorem, not an assumption about high chromatic number.
-/

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- No odd simple cycle implies a two-coloring, also for infinite graphs. -/
theorem colorable_two_of_oddCycleLengths_empty
    (hEmpty : G.oddCycleLengths = ∅) : G.Colorable 2 := by
  classical
  by_contra hColor
  obtain ⟨n, hn, hOdd, hCopy⟩ :=
    Erdos108OddCycle.not_two_colorable_contains_odd_cycle G hColor
  obtain ⟨v, p, hCycle, hLength⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < n)).mp hCopy
  have hMem : n ∈ G.oddCycleLengths :=
    mem_oddCycleLengths_intro hCycle hLength hOdd
  simp [hEmpty] at hMem

/-- The original cycle-length definition detects exactly the obstruction
to two-colorability; no finiteness hypothesis on the vertex type is needed. -/
theorem oddCycleLengths_empty_iff_colorable_two :
    G.oddCycleLengths = ∅ ↔ G.Colorable 2 := by
  refine ⟨colorable_two_of_oddCycleLengths_empty G, ?_⟩
  intro hColor
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro n hMem
  obtain ⟨v, p, hCycle, hLength, hOdd⟩ := mem_oddCycleLengths_elim hMem
  have hEven := (SimpleGraph.two_colorable_iff_forall_loop_even.mp hColor) v p
  rw [hLength] at hEven
  exact (Nat.not_even_iff_odd.mpr hOdd) hEven

/-- An actual ordinary copy of K₂ is precisely a nonempty edge set. -/
theorem completeGraph_two_isContained_iff_ne_bot :
    (completeGraph (Fin 2)).IsContained G ↔ G ≠ ⊥ := by
  rw [← SimpleGraph.not_cliqueFree_iff_top_isContained, SimpleGraph.cliqueFree_two]

/-- The exact k=0 clause of the current Formal Conjectures statement of
Erdős #58, including the equality characterization. -/
theorem erdos_58_zero
    (hFinite : G.oddCycleLengths.Finite)
    (hCard : G.oddCycleLengths.ncard ≤ 0) :
    G.chromaticNumber ≤ (2 * 0 + 2 : ℕ∞) ∧
      (G.chromaticNumber = (2 * 0 + 2 : ℕ∞) ↔
        (completeGraph (Fin (2 * 0 + 2))).IsContained G) := by
  have hEmpty : G.oddCycleLengths = ∅ :=
    (Set.ncard_eq_zero hFinite).mp (Nat.eq_zero_of_le_zero hCard)
  have hColor : G.Colorable 2 := colorable_two_of_oddCycleLengths_empty G hEmpty
  have hBipartite : G.IsBipartite := hColor
  have hEquality : G.chromaticNumber = 2 ↔ (completeGraph (Fin 2)).IsContained G := by
    rw [SimpleGraph.chromaticNumber_eq_two_iff,
      completeGraph_two_isContained_iff_ne_bot]
    simp [hBipartite]
  simpa using And.intro hColor.chromaticNumber_le hEquality

end Erdos58
