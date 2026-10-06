module

public import CycleGenericLongPathSeedV2
public import PathFiveComponentSums
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Uniform Erdős–Gallai edge bound from the generic long-path seed.
-/

universe u

namespace ErdosProblems.PathErdosGallai

open SimpleGraph
open scoped BigOperators
open ErdosProblems.AntiRamseyCycleGenericLongPathSeed
open ErdosProblems.AntiRamseyPathFiveComponents

theorem two_mul_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  calc
    2 * n.choose 2 = n.descFactorial 2 := by
      simpa only [Nat.factorial_two] using
        (Nat.descFactorial_eq_factorial_mul_choose n 2).symm
    _ = (n - 1) * n.descFactorial 1 := Nat.descFactorial_succ n 1
    _ = (n - 1) * n :=
      congrArg (fun m => (n - 1) * m) (Nat.descFactorial_one n)
    _ = n * (n - 1) := Nat.mul_comm _ _

theorem degree_le_one_of_path_three_free
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (pathGraph 3).Free G) (x : V) : G.degree x ≤ 1 := by
  classical
  by_contra hdegree
  have hmany : 1 < (G.neighborFinset x).card := by
    change 1 < G.degree x
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hmany
  have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp ha
  have hxb : G.Adj x b := (G.mem_neighborFinset x b).mp hb
  let one : G.Walk x b := Walk.cons hxb Walk.nil
  have hone : one.IsPath := by
    apply Walk.IsPath.nil.cons
    simpa only [Walk.support_nil, List.mem_singleton] using hxb.ne
  let two : G.Walk a b := Walk.cons hxa.symm one
  have htwo : two.IsPath := by
    apply hone.cons
    intro hmem
    change a ∈ x :: [b] at hmem
    rcases List.mem_cons.mp hmem with heq | heq
    · exact hxa.ne heq.symm
    · exact hab (List.mem_singleton.mp heq)
  have hcopy : (pathGraph 3) ⊑ G := by
    have h := htwo.isContained_pathGraph
    change (pathGraph 3) ⊑ G at h
    exact h
  exact hfree hcopy

theorem component_card_le_of_large_degrees
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 3 ≤ d) (hfree : (pathGraph (d + 1)).Free G)
    (hlarge : ∀ x : V, d ≤ 2 * G.degree x)
    (C : G.ConnectedComponent) : Nat.card C ≤ d := by
  classical
  have hdegree (x : C) :
      C.toSimpleGraph.degree x = G.degree x.val := by
    let e : C.toSimpleGraph.neighborSet x ≃ G.neighborSet x.val := {
      toFun := fun y => ⟨y.val.val, y.property⟩
      invFun := fun y =>
        ⟨⟨y.val, C.mem_supp_of_adj_mem_supp x.property y.property⟩, y.property⟩
      left_inv := by intro y; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl
    }
    calc
      C.toSimpleGraph.degree x = Nat.card (C.toSimpleGraph.neighborSet x) := by
        rw [Nat.card_eq_fintype_card, C.toSimpleGraph.card_neighborSet_eq_degree]
      _ = Nat.card (G.neighborSet x.val) := Nat.card_congr e
      _ = G.degree x.val := by
        rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
  by_contra hcard
  have hcardLargeNat : d + 1 ≤ Nat.card C := by omega
  have hcardLarge : d + 1 ≤ Fintype.card C := by
    simpa only [Fintype.card_eq_nat_card] using hcardLargeNat
  have hmin (x : C) : 2 ≤ C.toSimpleGraph.degree x := by
    have hx := hlarge x.val
    rw [← hdegree x] at hx
    omega
  have hpair (x y : C) (_hxy : x ≠ y) :
      d + 1 - 1 ≤ C.toSimpleGraph.degree x + C.toSimpleGraph.degree y := by
    have hx := hlarge x.val
    have hy := hlarge y.val
    rw [← hdegree x] at hx
    rw [← hdegree y] at hy
    omega
  obtain ⟨q, hq, hstep⟩ :=
    exists_ordered_path_of_degree_bounds (by omega : 4 ≤ d + 1)
      C.toSimpleGraph C.connected_toSimpleGraph hcardLarge hmin hpair
  let f : (pathGraph (d + 1)).Copy C.toSimpleGraph := {
    toHom := {
      toFun := q
      map_rel' := by
        intro a b hab
        rcases pathGraph_adj.mp hab with hab | hba
        · exact hstep a b hab
        · exact (hstep b a hba).symm
    }
    injective' := hq
  }
  exact hfree ⟨(Copy.induce G C.supp).comp f⟩

theorem edge_bound_of_large_degrees
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 3 ≤ d) (hfree : (pathGraph (d + 1)).Free G)
    (hlarge : ∀ x : V, d ≤ 2 * G.degree x) :
    2 * G.edgeFinset.card ≤ (d - 1) * Fintype.card V := by
  classical
  have hcomponent (C : G.ConnectedComponent) :
      2 * Nat.card C.toSimpleGraph.edgeSet ≤
        (d - 1) * Fintype.card C := by
    have hcard : Fintype.card C ≤ d := by
      simpa only [Fintype.card_eq_nat_card] using
        component_card_le_of_large_degrees G d hd hfree hlarge C
    have hedge : Nat.card C.toSimpleGraph.edgeSet =
        C.toSimpleGraph.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card]
      exact C.toSimpleGraph.card_edgeSet
    rw [hedge]
    have hsub : Fintype.card C - 1 ≤ d - 1 := by omega
    calc
      2 * C.toSimpleGraph.edgeFinset.card ≤
          2 * (Fintype.card C).choose 2 :=
        Nat.mul_le_mul_left 2 C.toSimpleGraph.card_edgeFinset_le_card_choose_two
      _ = Fintype.card C * (Fintype.card C - 1) :=
        two_mul_choose_two _
      _ ≤ Fintype.card C * (d - 1) :=
        Nat.mul_le_mul_left _ hsub
      _ = (d - 1) * Fintype.card C := Nat.mul_comm _ _
  have hcarrierCard (C : G.ConnectedComponent) :
      Fintype.card C = Fintype.card C.supp := by
    calc
      Fintype.card C = Nat.card C := Fintype.card_eq_nat_card
      _ = Nat.card C.supp := rfl
      _ = Fintype.card C.supp := Fintype.card_eq_nat_card.symm
  calc
    2 * G.edgeFinset.card =
        2 * (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) :=
      congrArg (fun n => 2 * n) (edge_card_eq_sum_component_edge_card G)
    _ = ∑ C : G.ConnectedComponent, 2 * Nat.card C.toSimpleGraph.edgeSet := by
      rw [Finset.mul_sum]
    _ ≤ ∑ C : G.ConnectedComponent, (d - 1) * Fintype.card C :=
      Finset.sum_le_sum (fun C _ => hcomponent C)
    _ = ∑ C : G.ConnectedComponent, (d - 1) * Fintype.card C.supp := by
      simp_rw [hcarrierCard]
    _ = (d - 1) * (∑ C : G.ConnectedComponent, Fintype.card C.supp) := by
      rw [Finset.mul_sum]
    _ = (d - 1) * Fintype.card V :=
      congrArg (fun n => (d - 1) * n) (vertex_card_eq_sum_component_card G).symm

theorem edge_bound_finset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d) (hfree : (pathGraph (d + 1)).Free G) :
    2 * G.edgeFinset.card ≤ (d - 1) * Fintype.card V := by
  classical
  by_cases hd2 : d = 2
  · subst d
    have hdegrees (x : V) : G.degree x ≤ 1 :=
      degree_le_one_of_path_three_free G hfree x
    calc
      2 * G.edgeFinset.card = ∑ x : V, G.degree x :=
        G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _x : V, (1 : ℕ) := Finset.sum_le_sum (fun x _ => hdegrees x)
      _ = (2 - 1) * Fintype.card V := by simp
  · have hd3 : 3 ≤ d := by omega
    let P : ℕ → Prop := fun n =>
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        Fintype.card W = n → (pathGraph (d + 1)).Free H →
        2 * H.edgeFinset.card ≤ (d - 1) * n
    have hP : ∀ n : ℕ, P n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        dsimp [P]
        intro W _instF _instD H _instA hcard hfreeH
        by_cases hlow : ∃ x : W, 2 * H.degree x ≤ d - 1
        · obtain ⟨x, hx⟩ := hlow
          let S : Set W := ({x} : Set W)ᶜ
          let H' : SimpleGraph S := H.induce S
          have hcardS : Fintype.card S = Fintype.card W - 1 := by
            calc
              Fintype.card S = Nat.card S := Fintype.card_eq_nat_card
              _ = Nat.card ↥(({x} : Set W)ᶜ) := rfl
              _ = Fintype.card ↥(({x} : Set W)ᶜ) := Nat.card_eq_fintype_card
              _ = Fintype.card W - Fintype.card ({x} : Set W) :=
                Fintype.card_compl_set ({x} : Set W)
              _ = Fintype.card W - 1 := by rw [Set.card_singleton]
          have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨x⟩
          have hsmall : Fintype.card S < n := by
            rw [hcardS, hcard]
            omega
          have hcardAdd : Fintype.card S + 1 = n := by
            rw [hcardS, hcard]
            omega
          have hfreeS : (pathGraph (d + 1)).Free H' := by
            rintro ⟨f⟩
            exact hfreeH ⟨(Copy.induce H S).comp f⟩
          have hIH := ih (Fintype.card S) hsmall S H' rfl hfreeS
          have hdelete : H'.edgeFinset.card = H.edgeFinset.card - H.degree x :=
            (H.card_edgeFinset_induce_compl_singleton x).trans
              (H.card_edgeFinset_deleteIncidenceSet x)
          have hdegreeEdges : H.degree x ≤ H.edgeFinset.card :=
            H.degree_le_card_edgeFinset (v := x)
          have hedgeAdd : H'.edgeFinset.card + H.degree x = H.edgeFinset.card := by
            omega
          calc
            2 * H.edgeFinset.card = 2 * (H'.edgeFinset.card + H.degree x) :=
              congrArg (fun m => 2 * m) hedgeAdd.symm
            _ = 2 * H'.edgeFinset.card + 2 * H.degree x := by rw [Nat.mul_add]
            _ ≤ (d - 1) * Fintype.card S + (d - 1) := Nat.add_le_add hIH hx
            _ = (d - 1) * (Fintype.card S + 1) := by rw [Nat.mul_add, Nat.mul_one]
            _ = (d - 1) * n := congrArg (fun m => (d - 1) * m) hcardAdd
        · have hlarge (x : W) : d ≤ 2 * H.degree x := by
            have hx : ¬ 2 * H.degree x ≤ d - 1 := fun h => hlow ⟨x, h⟩
            omega
          have hbound := edge_bound_of_large_degrees H d hd3 hfreeH hlarge
          simpa only [hcard] using hbound
    exact hP (Fintype.card V) V G rfl hfree

/-- Uniform Erdős–Gallai: a finite simple graph containing no non-induced
(d+1)-vertex path has at most (d-1)|V|/2 edges. No connectedness, supplied
degree, coloring or representative hypothesis is imposed. -/
theorem erdos_gallai_edge_bound {V : Type u} [Finite V]
    (G : SimpleGraph V) (d : ℕ) (hd : 2 ≤ d)
    (hfree : (pathGraph (d + 1)).Free G) :
    2 * Nat.card G.edgeSet ≤ (d - 1) * Nat.card V := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  have hfin := edge_bound_finset G d hd hfree
  have hedge : Nat.card G.edgeSet = G.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact G.card_edgeSet
  rw [hedge, Nat.card_eq_fintype_card]
  exact hfin

end ErdosProblems.PathErdosGallai
