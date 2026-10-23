module

/- Copyright 2025-2026 The Formal Conjectures Authors.
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. -/

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Layer158

public section

/-! ## Shortest odd closed walks

A graph that is not 2-colourable contains a shortest odd closed walk, and the sequence
of its vertices induces the shortest odd cycle. -/

namespace Erdos108OddCycle

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

theorem exists_minimal_odd_walk (hG : ¬ G.Colorable 2) :
    ∃ (u : V) (p : G.Walk u u), Odd p.length ∧
      (∀ v (q : G.Walk v v), Odd q.length → p.length ≤ q.length) := by
  classical
  have hloop : ∃ (u : V) (p : G.Walk u u), Odd p.length := by
    have hn : ¬ ∀ u (p : G.Walk u u), Even p.length := by
      exact fun h => hG (SimpleGraph.two_colorable_iff_forall_loop_even.mpr h)
    push Not at hn
    obtain ⟨u, p, hp⟩ := hn
    exact ⟨u, p, Nat.not_even_iff_odd.mp hp⟩
  have hex : ∃ n : ℕ, ∃ (u : V) (p : G.Walk u u), Odd p.length ∧ p.length = n := by
    obtain ⟨u, p, hp⟩ := hloop
    exact ⟨p.length, u, p, hp, rfl⟩
  obtain ⟨u, p, hp, hlen⟩ := Nat.find_spec hex
  refine ⟨u, p, hp, ?_⟩
  intro v q hq
  rw [hlen]
  exact Nat.find_min' hex ⟨v, q, hq, rfl⟩

theorem minimal_odd_walk_distinct {u : V} (p : G.Walk u u)
    (hodd : Odd p.length)
    (hmin : ∀ v (q : G.Walk v v), Odd q.length → p.length ≤ q.length) :
    ∀ i j : ℕ, i < j → j ≤ p.length → (1 ≤ i ∨ j < p.length) →
      p.getVert i ≠ p.getVert j := by
  have heven : ∀ v (q : G.Walk v v), q.length < p.length → Even q.length := by
    intro v q hshort
    by_contra hn
    have h := hmin v q (Nat.not_even_iff_odd.mp hn)
    omega
  intro i j hij hj hscope hsame
  have hcopy : (p.drop i).getVert (j - i) = p.getVert i := by
    simp only [Walk.drop_getVert, Nat.add_sub_of_le hij.le]
    exact hsame.symm
  let q : G.Walk (p.getVert i) (p.getVert i) :=
    ((p.drop i).take (j - i)).copy rfl hcopy
  let r : G.Walk u u := (p.take i).append ((p.drop j).copy hsame.symm rfl)
  have hq : q.length = j - i := by
    simp [q, Walk.take_length, Walk.drop_length,
      Nat.min_eq_left (by omega : j - i ≤ p.length - i)]
  have hr : r.length = i + (p.length - j) := by
    simp [r, Walk.take_length, Walk.drop_length,
      Nat.min_eq_left (by omega : i ≤ p.length)]
  have hqshort : q.length < p.length := by
    rw [hq]
    rcases hscope with hi | hj'
    · omega
    · omega
  have hqe := heven (p.getVert i) q hqshort
  have hre := heven u r (by omega)
  have hall : Even p.length := by
    have hsum := hqe.add hre
    have hlen : q.length + r.length = p.length := by omega
    simpa only [hlen] using hsum
  exact (Nat.not_even_iff_odd.mpr hodd) hall

theorem minimal_odd_walk_injective {u : V} (p : G.Walk u u)
    (hodd : Odd p.length)
    (hmin : ∀ v (q : G.Walk v v), Odd q.length → p.length ≤ q.length) :
    Function.Injective (fun i : Fin p.length => p.getVert i.val) := by
  intro i j heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (minimal_odd_walk_distinct G p hodd hmin i.val j.val hlt j.isLt.le
      (Or.inr j.isLt)) heq
  · exact (minimal_odd_walk_distinct G p hodd hmin j.val i.val hgt i.isLt.le
      (Or.inr i.isLt)) heq.symm

theorem getVert_cyclic_adj {u : V} (p : G.Walk u u) [NeZero p.length]
    (i : Fin p.length) :
    G.Adj (p.getVert i.val) (p.getVert (i + 1 : Fin p.length).val) := by
  have hval : (i + 1 : Fin p.length).val = (i.val + 1) % p.length := by
    simp [Fin.val_add, Nat.add_mod]
  have hstep := p.adj_getVert_succ i.isLt
  rw [hval]
  by_cases hlt : i.val + 1 < p.length
  · simpa only [Nat.mod_eq_of_lt hlt] using hstep
  · have heq : i.val + 1 = p.length := by omega
    simpa [heq] using hstep

theorem not_two_colorable_contains_odd_cycle
    (hG : ¬ G.Colorable 2) :
    ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ (cycleGraph n).IsContained G := by
  classical
  obtain ⟨u, p, hodd, hmin⟩ := exists_minimal_odd_walk G hG
  have hpos : 0 < p.length := hodd.pos
  have hneone : p.length ≠ 1 := by
    intro hlen
    exact G.irrefl (Walk.adj_of_length_eq_one hlen)
  have hnetwo : p.length ≠ 2 := by
    intro hlen
    exact (Nat.not_even_iff_odd.mpr hodd) (by rw [hlen]; decide)
  have hthree : 3 ≤ p.length := by omega
  let : NeZero p.length := ⟨by omega⟩
  let f : (cycleGraph p.length) →g G := {
    toFun := fun i => p.getVert i.val
    map_rel' := by
      intro i j hij
      rcases (SimpleGraph.cycleGraph_adj').mp hij with hsub | hsub
      · have hfin : i - j = (1 : Fin p.length) := by
          apply Fin.ext
          simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < p.length)] using hsub
        have heq : i = j + 1 := (sub_eq_iff_eq_add').mp hfin
        subst i
        exact (getVert_cyclic_adj G p j).symm
      · have hfin : j - i = (1 : Fin p.length) := by
          apply Fin.ext
          simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < p.length)] using hsub
        have heq : j = i + 1 := (sub_eq_iff_eq_add').mp hfin
        subst j
        exact getVert_cyclic_adj G p i
  }
  refine ⟨p.length, hthree, hodd, ⟨f.toCopy (minimal_odd_walk_injective G p hodd hmin)⟩⟩

end Erdos108OddCycle
